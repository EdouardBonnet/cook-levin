# The Cook–Levin theorem

Submission [lax-429075](https://laxarchive.org/lax-429075/), proving NP-completeness of binary-encoded CNF
satisfiability under polynomial many-one reductions. It uses the certificate
definition of NP and the polynomial-time machine model from
[lax-434930](https://laxarchive.org/lax-434930/).

The argument separates binary encoding, bounded assignments, verifier
correctness, gate truth tables, the Tseitin circuit encoding, and NP-hardness.
The SAT verifier is implemented as a finite stack program. Its correctness,
termination on every input, work-stack cleanup, and running time of at most
`100(n+1)^4` steps are proved. This completes the proof that SAT belongs to NP.

For NP-hardness, a bounded single-tape computation is unrolled into an
acyclic Boolean circuit. An explicit finite stack program produces its
encoded gate clauses in polynomial time. The proofs cover the initial tape,
each transition, wire addresses, final acceptance, and the exact output
encoding. All eleven statements have closed proof networks within Lax.

Variable indices are unary. This remains a polynomial-size encoding for the
circuits produced by the reduction and permits an assignment certificate
bounded by the encoded formula length. Lists use self-delimiting markers;
malformed words are excluded from the SAT language.

Only the main NP-completeness statement is labeled `theorem`; supporting
statements are `lemma`. Run `lax build . --replay` to validate the submission.

The submission targets Lean and Mathlib 4.33.0 and includes an annotated companion in [paper/main.tex](paper/main.tex). The class definitions, encodings, and result statements are preserved; proof changes address imports and Lean 4.33 elaboration.
