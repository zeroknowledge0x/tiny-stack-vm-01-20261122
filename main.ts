import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Dispatch table: byte -> immediate length, pop count, push count, handler id.
// All arithmetic uses Int32 semantics; unsigned variants re-read via >>> 0.
const SRC = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const DST = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

const STEP_CEIL = 1000000;
const BYTE_CEIL = 65536;
const DS_CAP = 256;
const CS_CAP = 64;
const WORDS = 256;

const immLen = new Uint8Array(256);
const popN = new Uint8Array(256);
const pushN = new Uint8Array(256);
const kind = new Uint8Array(256);
const specs: number[][] = [
  [0x00, 0, 0, 0, 1], [0x01, 1, 0, 1, 2], [0x02, 4, 0, 1, 3],
  [0x03, 0, 1, 0, 4], [0x04, 0, 1, 2, 5], [0x05, 0, 2, 2, 6],
  [0x06, 0, 2, 3, 7], [0x07, 0, 3, 3, 8], [0x10, 0, 2, 1, 9],
  [0x11, 0, 2, 1, 9], [0x12, 0, 2, 1, 9], [0x13, 0, 2, 1, 9],
  [0x14, 0, 2, 1, 9], [0x15, 0, 2, 1, 9], [0x16, 0, 2, 1, 9],
  [0x17, 0, 1, 1, 10], [0x18, 0, 2, 1, 9], [0x19, 0, 2, 1, 9],
  [0x1a, 0, 2, 1, 9], [0x1b, 0, 1, 1, 11], [0x1c, 0, 2, 1, 9],
  [0x1d, 0, 2, 1, 9], [0x1e, 0, 2, 1, 9], [0x20, 0, 2, 1, 9],
  [0x21, 0, 2, 1, 9], [0x22, 0, 2, 1, 9], [0x30, 2, 0, 0, 12],
  [0x31, 2, 1, 0, 12], [0x32, 2, 1, 0, 12], [0x33, 2, 0, 0, 13],
  [0x34, 0, 0, 0, 14], [0x40, 0, 1, 1, 15], [0x41, 0, 2, 0, 16],
  [0x50, 0, 1, 0, 17], [0x51, 0, 1, 0, 18], [0x52, 0, 0, 1, 19],
  [0x53, 0, 1, 0, 20],
];
for (const s of specs) {
  immLen[s[0]] = s[1]; popN[s[0]] = s[2]; pushN[s[0]] = s[3]; kind[s[0]] = s[4];
}

const encode = new TextEncoder();

function execute(prog: Uint8Array, input: Uint8Array) {
  const n = prog.length;
  const data = new Int32Array(DS_CAP);
  const calls = new Int32Array(CS_CAP);
  const mem = new Int32Array(WORDS);
  const bytes = new Uint8Array(BYTE_CEIL);
  let sp = 0, csp = 0, used = 0, inAt = 0, pc = 0, steps = 0;
  const end = (code: number) => ({ bytes: bytes.subarray(0, used), exit: code });
  for (;;) {
    if (steps === STEP_CEIL) return end(10);
    if (pc < 0 || pc >= n) return end(9);
    const op = prog[pc];
    if (kind[op] === 0) return end(5);
    const imm = immLen[op];
    if (pc + imm >= n) return end(9);
    steps++;
    const next = pc + 1 + imm;
    if (sp < popN[op]) return end(2);
    if (sp - popN[op] + pushN[op] > DS_CAP) return end(3);
    pc = next;
    switch (kind[op]) {
      case 1: return end(0);
      case 2: data[sp++] = (prog[next - 1] << 24) >> 24; break;
      case 3:
        data[sp++] = prog[next - 4] | (prog[next - 3] << 8) |
          (prog[next - 2] << 16) | (prog[next - 1] << 24);
        break;
      case 4: sp--; break;
      case 5: data[sp] = data[sp - 1]; sp++; break;
      case 6: {
        const t = data[sp - 1]; data[sp - 1] = data[sp - 2]; data[sp - 2] = t; break;
      }
      case 7: data[sp] = data[sp - 2]; sp++; break;
      case 8: {
        const t = data[sp - 3];
        data[sp - 3] = data[sp - 2];
        data[sp - 2] = data[sp - 1];
        data[sp - 1] = t;
        break;
      }
      case 9: {
        const a = data[sp - 2], b = data[sp - 1];
        let r = 0;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) {
          if (b === 0) return end(4);
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
        } else if (op === 0x14) {
          if (b === 0) return end(4);
          r = b === -1 ? 0 : (a % b) | 0;
        } else if (op === 0x15) {
          if (b === 0) return end(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 0x16) {
          if (b === 0) return end(4);
          r = (a >>> 0) % (b >>> 0) | 0;
        } else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else if (op === 0x22) r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        sp -= 2;
        data[sp++] = r;
        break;
      }
      case 10: data[sp - 1] = -data[sp - 1] | 0; break;
      case 11: data[sp - 1] = ~data[sp - 1]; break;
      case 12: {
        let take = true;
        if (op !== 0x30) {
          const v = data[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) {
          const rel = ((prog[next - 2] | (prog[next - 1] << 8)) << 16) >> 16;
          pc = next + rel;
        }
        break;
      }
      case 13:
        if (csp === CS_CAP) return end(7);
        calls[csp++] = next;
        pc = prog[next - 2] | (prog[next - 1] << 8);
        break;
      case 14:
        if (csp === 0) return end(8);
        pc = calls[--csp];
        break;
      case 15: {
        const addr = data[sp - 1];
        if (addr < 0 || addr >= WORDS) return end(6);
        data[sp - 1] = mem[addr];
        break;
      }
      case 16: {
        const addr = data[sp - 1];
        if (addr < 0 || addr >= WORDS) return end(6);
        mem[addr] = data[sp - 2];
        sp -= 2;
        break;
      }
      case 17: {
        const chunk = encode.encode(String(data[sp - 1]));
        if (used + chunk.length > BYTE_CEIL) return end(11);
        bytes.set(chunk, used);
        used += chunk.length;
        sp--;
        break;
      }
      case 18:
        if (used + 1 > BYTE_CEIL) return end(11);
        bytes[used++] = data[--sp] & 255;
        break;
      case 19:
        data[sp++] = inAt < input.length ? input[inAt++] : -1;
        break;
      case 20:
        return end(data[--sp] & 255);
    }
  }
}

for (const id of readdirSync(SRC).sort()) {
  const here = join(SRC, id);
  const prog = readFileSync(join(here, 'program.bin'));
  let input: Uint8Array;
  try {
    input = readFileSync(join(here, 'input.bin'));
  } catch {
    input = new Uint8Array(0);
  }
  const answer = execute(prog, input);
  mkdirSync(join(DST, id), { recursive: true });
  writeFileSync(join(DST, id, 'stdout.bin'), answer.bytes);
  writeFileSync(join(DST, id, 'exit.txt'), `${answer.exit}\n`);
}
