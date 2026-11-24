// A tiny stack virtual machine for make.fun's tiny stack ISA: runs each
// /input/<id>/program.bin on its input.bin, writes /output/<id>/stdout.bin
// and exit.txt. Traps exit with their own code and keep prior output.
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';

const read = (p) => {
  try { return readFileSync(p); } catch { return Buffer.alloc(0); }
};

const run = (P, inp) => {
  const n = P.length;
  const S = new Int32Array(256), C = new Int32Array(64);
  const M = new Int32Array(256), O = new Uint8Array(65536);
  let sp = 0, cp = 0, pc = 0, ol = 0, ip = 0, steps = 0;
  const end = (e) => [Buffer.from(O.subarray(0, ol)), e];
  for (;;) {
    if (steps >= 1e6) return end(10);
    if (pc < 0 || pc >= n) return end(9);
    const op = P[pc];
    const imm = op == 1 ? 1 : op == 2 ? 4 : op >= 48 && op <= 51 ? 2 : 0;
    const known = op < 8 || op >= 16 && op < 35 && op != 31 || op >= 48 && op < 53
      || op == 64 || op == 65 || op >= 80 && op < 84;
    if (!known) return end(5);
    if (pc + imm >= n) return end(9);
    // Stack needs of the instruction, checked before it runs.
    let po = 2, pu = 0;
    if (op == 0 || op == 1 || op == 2 || op == 48 || op == 51 || op == 52 || op == 82) po = 0;
    else if (op == 7) po = 3;
    else if (op == 3 || op == 4 || op == 23 || op == 27 || op == 49 || op == 50 || op == 64 || op >= 80) po = 1;
    if (op == 4 || op == 5) pu = 2;
    else if (op == 6 || op == 7) pu = 3;
    else if (op == 1 || op == 2 || op == 64 || op == 82 || op >= 16 && op <= 34) pu = 1;
    if (sp < po) return end(2);
    if (sp - po + pu > 256) return end(3);
    steps++;
    const nx = pc + 1 + imm;
    pc = nx;
    const rel = imm == 2 ? (P[nx - 2] | P[nx - 1] << 8) << 16 >> 16 : 0;
    switch (op) {
      case 0: return end(0);                     // HALT
      case 1: S[sp++] = P[nx - 1] << 24 >> 24; break;   // PUSH8, sign-extended
      case 2: S[sp++] = P[nx - 4] | P[nx - 3] << 8 | P[nx - 2] << 16 | P[nx - 1] << 24; break; // PUSH32
      case 3: sp--; break;                       // POP
      case 4: S[sp] = S[sp - 1]; sp++; break;    // DUP
      case 5: { const t = S[sp - 1]; S[sp - 1] = S[sp - 2]; S[sp - 2] = t; break; } // SWAP
      case 6: S[sp] = S[sp - 2]; sp++; break;    // OVER
      case 7: { const t = S[sp - 3]; S[sp - 3] = S[sp - 2]; S[sp - 2] = S[sp - 1]; S[sp - 1] = t; break; } // ROT
      case 23: S[sp - 1] = -S[sp - 1]; break;    // NEG (the store wraps)
      case 27: S[sp - 1] = ~S[sp - 1]; break;    // NOT
      case 16: case 17: case 18: case 19: case 20: case 21: case 22:
      case 24: case 25: case 26: case 28: case 29: case 30:
      case 32: case 33: case 34: {               // the binary operators
        const b = S[sp - 1], a = S[sp - 2];
        let r;
        if (op == 16) r = a + b;                                // ADD
        else if (op == 17) r = a - b;                           // SUB
        else if (op == 18) r = Math.imul(a, b);                 // MUL, low 32 bits
        else if (op == 19) { if (b == 0) return end(4); r = (a / b) | 0; }  // DIV
        else if (op == 20) { if (b == 0) return end(4); r = a % b; }        // MOD
        else if (op == 21) { if (b == 0) return end(4); r = Math.floor((a >>> 0) / (b >>> 0)); } // DIVU
        else if (op == 22) { if (b == 0) return end(4); r = (a >>> 0) % (b >>> 0); }             // MODU
        else if (op == 24) r = a & b;                           // AND
        else if (op == 25) r = a | b;                           // OR
        else if (op == 26) r = a ^ b;                           // XOR
        else if (op == 28) r = a << (b & 31);                   // SHL
        else if (op == 29) r = a >> (b & 31);                   // SHR
        else if (op == 30) r = (a >>> (b & 31)) | 0;            // SHRU
        else if (op == 32) r = a == b ? 1 : 0;                  // EQ
        else if (op == 33) r = a < b ? 1 : 0;                   // LT
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;                 // LTU
        sp--; S[sp - 1] = r; break;
      }
      case 48: pc = nx + rel; break;             // JMP
      case 49: if (S[--sp] == 0) pc = nx + rel; break;   // JZ (pops either way)
      case 50: if (S[--sp] != 0) pc = nx + rel; break;   // JNZ
      case 51:                                   // CALL, unsigned target
        if (cp >= 64) return end(7);
        C[cp++] = nx; pc = P[nx - 2] | P[nx - 1] << 8; break;
      case 52:                                   // RET
        if (cp == 0) return end(8);
        pc = C[--cp]; break;
      case 64: {                                 // LOAD
        const a = S[sp - 1];
        if (a < 0 || a > 255) return end(6);
        S[sp - 1] = M[a]; break;
      }
      case 65: {                                 // STORE: ( v addr -- )
        const a = S[sp - 1];
        if (a < 0 || a > 255) return end(6);
        M[a] = S[sp - 2]; sp -= 2; break;
      }
      case 80: {                                 // PRINT, decimal ASCII
        const s = String(S[sp - 1]);
        if (ol + s.length > 65536) return end(11);
        sp--;
        for (let i = 0; i < s.length; i++) O[ol++] = s.charCodeAt(i);
        break;
      }
      case 81:                                   // PUTC
        if (ol >= 65536) return end(11);
        O[ol++] = S[--sp] & 255; break;
      case 82: S[sp++] = ip < inp.length ? inp[ip++] : -1; break;  // IN, -1 at the end
      case 83: return end(S[--sp] & 255);        // EXIT, low byte only
    }
  }
};

for (let i = 1; i <= 40; i++) {
  const id = 'i' + String(i).padStart(3, '0');
  const [out, code] = run(read(`/input/${id}/program.bin`), read(`/input/${id}/input.bin`));
  mkdirSync(`/output/${id}`, { recursive: true });
  writeFileSync(`/output/${id}/stdout.bin`, out);
  writeFileSync(`/output/${id}/exit.txt`, code + '\n');
}
