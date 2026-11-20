import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BNzC
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Primmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Charbij

open Finset UpperTheory.V.Bern

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem nz_iff {R S : Type} [Field R] [Algebra ℚ R] [Field S] [Algebra ℚ S] {N : ℕ} [NeZero N]
    (f : R →+* S) (χ : DirichletCharacter R N) (k : ℕ) :
    ((χ.ringHomComp f : DirichletCharacter S N) (-1) = (-1) ^ k ↔ χ (-1) = (-1) ^ k) ∧
    (Bprim k (χ.ringHomComp f : DirichletCharacter S N) ≠ 0 ↔ Bprim k χ ≠ 0) ∧
    (genB k (χ.ringHomComp f : ZMod N → S) ≠ 0 ↔ genB k χ ≠ 0) := by
  have hinj : Function.Injective f := f.injective
  refine ⟨?_, ?_, ?_⟩
  · rw [MulChar.ringHomComp_apply]
    have e : ((-1 : S)) ^ k = f ((-1 : R) ^ k) := by simp
    rw [e]
    exact hinj.eq_iff
  · rw [← b_primmap f hinj k χ]
    exact map_ne_zero_iff f hinj
  · rw [← map_genB_char f k χ]
    exact map_ne_zero_iff f hinj

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Introduce a local definition for the expression. Introduce a local definition for the expression. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Bern.b_nzany :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] {N : ℕ} [NeZero N] (χ : DirichletCharacter Ω N) (k : ℕ), 1 ≤ k → χ (-1) = (-1) ^ k → Bprim k χ ≠ 0 ∧ (2 ≤ k → genB k χ ≠ 0) := by
  intro Ω _ _ N _ χ k hk hχ
  haveI : NeZero (Monoid.exponent (ZMod N)ˣ) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  let i : Ω →+* AlgebraicClosure Ω := algebraMap _ _
  let f : AlgebraicClosure ℚ →+* AlgebraicClosure Ω :=
    (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure Ω).toRingHom
  let g : AlgebraicClosure ℚ →+* ℂ :=
    (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] ℂ).toRingHom
  obtain ⟨ψ, -, hψ⟩ := (UpperTheory.V.Bern.b_charbij (N := N) f Set.univ).surjOn
    (show (χ.ringHomComp i : DirichletCharacter _ N) ∈ charSet (AlgebraicClosure Ω) Set.univ from Set.mem_univ _)
  obtain ⟨a1, a2, a3⟩ := nz_iff i χ k
  obtain ⟨b1, b2, b3⟩ := nz_iff f ψ k
  obtain ⟨c1, c2, c3⟩ := nz_iff g ψ k
  simp only at hψ
  rw [hψ] at b1 b2 b3
  obtain ⟨h1, h2⟩ := UpperTheory.V.Bern.b_nzC (ψ.ringHomComp g) k hk (c1.2 (b1.1 (a1.2 hχ)))
  exact ⟨a2.1 (b2.2 (c2.1 h1)), fun h => a3.1 (b3.2 (c3.1 (h2 h)))⟩
