module

public import RBM8D

public section

/-!
# Proofs of the statements of `Challenge.lean`

Each theorem below has the same name and the same statement as its counterpart in
`Challenge.lean`, and is proved by the theorem of the library `RBM8D` named in its proof. The
definitions that occur in the statements are those of `RBM8D/MainDefs.lean`.
-/

section
namespace RBM8D

/-- [I, Theorem 1.3]: weak delocalization of the bulk eigenvectors, (1.12) and (1.13); the statement is `Thm13Stmt`. -/
theorem theorem_1_3 : Thm13Stmt :=
  thm13

/-- [I, Theorem 1.4]: the local law (1.19); the statement is `LocalLawStmt`. -/
theorem theorem_1_4 : LocalLawStmt :=
  localLaw

/-- [I, Theorem 1.5] with [I, Corollaries 1.6 and 1.7]: quantum diffusion; the statement is `quantumDiffusionStmt`. -/
theorem theorem_1_5 : quantumDiffusionStmt :=
  quantumDiffusion

end RBM8D
end
