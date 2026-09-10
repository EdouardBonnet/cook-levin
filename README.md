# The Cook–Levin theorem

Lax submission **lax-429075**, stating NP-completeness of binary-encoded CNF
satisfiability under polynomial many-one reductions. It uses the certificate
definition of NP from lax-434930 and the polynomial time machine model from
lax-554803.

The argument separates binary encoding, bounded assignments, verifier
correctness, gate truth tables, the Tseitin circuit encoding, and NP-hardness.
The SAT verifier is implemented as a finite stack program. Its correctness,
termination on every input, work-stack cleanup, and running time of at most
`100(n+1)^4` steps are proved. This completes the proof that SAT belongs to NP.

Eight of eleven statements have closed proofs. The remaining construction,
`CircuitMachine.compile`, must unroll an arbitrary polynomial time verifier
into an acyclic Boolean circuit and produce its encoded gate clauses in
polynomial time. NP-hardness and the main theorem still depend on this
obligation, so the submission is not yet a complete proof of Cook–Levin.

Variable indices are unary. This remains a polynomial-size encoding for the
circuits produced by the reduction and permits an assignment certificate
bounded by the encoded formula length. Lists use self-delimiting markers;
malformed words are excluded from the SAT language.

Only the main NP-completeness statement is labeled `theorem`; supporting
statements are `lemma`. Run `lax build . --replay` to validate the submission.
