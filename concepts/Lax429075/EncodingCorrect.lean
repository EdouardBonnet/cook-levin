import Lax429075.Encoding

/-!
---
title: Decoding an encoded formula
type: lemma
---
The binary decoder recovers every encoded CNF formula.
-/

namespace Lax429075.EncodingCorrect

open CNF Encoding

axiom roundtrip (F : Formula) : decodeCNF (encodeCNF F) = some F

end Lax429075.EncodingCorrect
