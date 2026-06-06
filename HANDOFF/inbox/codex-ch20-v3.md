Read QseriesFormalization/Chapter20.lean. Ch20 needs more than tau values to close. Look at what Chan actually proves in Chapter 20 beyond Ono's theorem.

Step 1: Read the Chan PDF (Hai-Chi Chen_An invitation to q-series.pdf) chapter 20 using pdftotext. Identify ALL theorems/propositions in the chapter.

Step 2: For each theorem that is NOT Ono 20.1 (which is blocked on Mathlib), check if it can be proved with existing infrastructure. Candidates:
- Ramanujan tau congruences beyond p=2,3,5,7
- Lehmer's conjecture finite verification (tau(n) != 0 for n <= 50)
- Hecke eigenform property of Delta
- tau multiplicativity as a GENERAL theorem (not just spot checks)

Step 3: Prove whatever you can. The goal is to get Ch20 closer to PASS by proving more of Chan's actual theorems, not just stating them.

Work in QseriesFormalization/Chapter20.lean or new Pending files. Build: lake env lean QseriesFormalization/Chapter20.lean. Reply to HANDOFF/outbox/codex-ch20-v3-reply.md