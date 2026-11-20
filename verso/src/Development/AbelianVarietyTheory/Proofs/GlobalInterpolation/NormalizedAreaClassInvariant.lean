import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.EquidistributedConjugates
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.ExistsMemIdealInvariants
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UniformizationHolds
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPeriodPairIdealCurveLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateCurveDatumLatticeIsCurveLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvdOfEqMulIntegral

noncomputable section

namespace GlobalTheory.ConjEquidistrib

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric
open scoped nonZeroDivisors Pointwise

open GlobalTheory.IndefiniteRowSideFullHecke.EquidistributedConjugates in

/- English proof (translation)
Set `σ : D.host.K →+* ℂ` to `D.host.φ₀.comp D.host.K.val.toRingHom`. Set `σM : D.host.K →+* M` to `σ.codRestrict M hm`. Establish `hsq` using `D.host.sqd_sq`. Set `b : D.host.K` to `⟨D.host.sqd, IntermediateField.mem_adjoin_simple_self ℚ _⟩`. Establish `hb : b ^ 2 = -(D.host.d : D.host.K)`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `using hsq`. Establish `hall : ∀ ψ : D.host.K →+* ℂ, ψ b ^ 2 = -(D.host.d : ℂ)` using `fun ψ => by`. Rewrite using `[← map_pow, hb, map_neg, map_natCast]`. Establish `hcj : ∀ ψ : D.host.K →+* ℂ, (starRingEnd ℂ) (ψ b) = -ψ b` using `fun ψ => by`.

Establish `h1 : (ψ b) ^ 2 = (Complex.I * (Real.sqrt D.host.d : ℂ)) ^ 2`. Rewrite using `[hall, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]`. Simplify using the standard rewrite rules. Apply the tactic sequence `rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h <;> rw [h] <;>`. Apply the tactic sequence `simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal] <;> ring`.

Establish `hne : σ b ≠ 0`. Introduce `h0`. Use `hall σ` as an intermediate fact. Rewrite `this` using `[h0]`. Establish `hd : (0 : ℂ) ≠ -(D.host.d : ℂ)`.

Rewrite using `[ne_eq, eq_comm, neg_eq_zero, Nat.cast_eq_zero]`. Conclude with `D.host.hyp.2.1.ne_zero`. Conclude with `hd (by simpa using this)`. Establish `key : ∀ ρ' : M →ₐ[ℚ] ℂ, ρ' (σM b) = σ b → FixesK D M ρ'` using `fun ρ' h x y hy => by`. Establish `: ((ρ' : M →+* ℂ).comp σM).toRatAlgHom = σ.toRatAlgHom`.

Use `IntermediateField.algHom_ext_of_eq_adjoin ℚ (S := D.host.K) (s := {D.host.sqd}) rfl fun x hx => ?_` and prove the remaining obligations. Take `rfl : x = _` from `hx`. Conclude with `h`. Establish `h2 : ρ' (σM x) = σ x` using `DFunLike.congr_fun this x`. Establish `hyx : y = σM x` using `Subtype.ext hy`.

Rewrite using `[hyx]`. Conclude with `h2`. Establish `back : ∀ ρ' : M →ₐ[ℚ] ℂ, FixesK D M ρ' → ρ' (σM b) = σ b` using `fun ρ' h => h b (σM b) rfl`. Establish `h1 : ρ (σM b) ^ 2 = σ b ^ 2` using `(hall ((ρ : M →+* ℂ).comp σM)).trans (hall σ).symm`. Prove the components needed by the constructor for the conclusion.

Introduce `hc hf`. Establish `e1` using `back _ hc`. Establish `e2` using `back _ hf`. Rewrite `e1` using `[conjEmb_apply, e2, hcj]`. Conclude with `hne (by linear_combination -e1 / 2)`.

Introduce `hf`. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h` into its components or cases. Conclude with `absurd (key ρ h) hf`. Use `key _ ?_` and prove the remaining obligations. Rewrite using `[conjEmb_apply, h, map_neg, hcj, neg_neg]`.
-/
theorem fixesK_conjEmb_iff (D : D7) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ)
    (hm : ∀ a : D.host.K, D.host.φ₀ (a : D.host.E) ∈ M) :
    FixesK D M (conjEmb M ρ) ↔ ¬ FixesK D M ρ := by
  let σ : D.host.K →+* ℂ := D.host.φ₀.comp D.host.K.val.toRingHom
  let σM : D.host.K →+* M := σ.codRestrict M hm
  have hsq := D.host.sqd_sq
  let b : D.host.K :=
    ⟨D.host.sqd, IntermediateField.mem_adjoin_simple_self ℚ _⟩
  have hb : b ^ 2 = -(D.host.d : D.host.K) := by
    apply Subtype.ext
    simpa using hsq
  have hall : ∀ ψ : D.host.K →+* ℂ, ψ b ^ 2 = -(D.host.d : ℂ) := fun ψ => by
    rw [← map_pow, hb, map_neg, map_natCast]
  have hcj : ∀ ψ : D.host.K →+* ℂ, (starRingEnd ℂ) (ψ b) = -ψ b := fun ψ => by
    have h1 : (ψ b) ^ 2 = (Complex.I * (Real.sqrt D.host.d : ℂ)) ^ 2 := by
      rw [hall, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h <;> rw [h] <;>
      simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal] <;> ring
  have hne : σ b ≠ 0 := by
    intro h0
    have := hall σ
    rw [h0] at this
    have hd : (0 : ℂ) ≠ -(D.host.d : ℂ) := by
      rw [ne_eq, eq_comm, neg_eq_zero, Nat.cast_eq_zero]
      exact D.host.hyp.2.1.ne_zero
    exact hd (by simpa using this)
  have key : ∀ ρ' : M →ₐ[ℚ] ℂ, ρ' (σM b) = σ b → FixesK D M ρ' := fun ρ' h x y hy => by
    have : ((ρ' : M →+* ℂ).comp σM).toRatAlgHom = σ.toRatAlgHom := by
      refine IntermediateField.algHom_ext_of_eq_adjoin ℚ (S := D.host.K)
        (s := {D.host.sqd}) rfl fun x hx => ?_
      obtain rfl : x = _ := hx
      exact h
    have h2 : ρ' (σM x) = σ x := DFunLike.congr_fun this x
    have hyx : y = σM x := Subtype.ext hy
    rw [hyx]
    exact h2
  have back : ∀ ρ' : M →ₐ[ℚ] ℂ, FixesK D M ρ' → ρ' (σM b) = σ b := fun ρ' h => h b (σM b) rfl
  have h1 : ρ (σM b) ^ 2 = σ b ^ 2 := (hall ((ρ : M →+* ℂ).comp σM)).trans (hall σ).symm
  constructor
  · intro hc hf
    have e1 := back _ hc
    have e2 := back _ hf
    rw [conjEmb_apply, e2, hcj] at e1
    exact hne (by linear_combination -e1 / 2)
  · intro hf
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
    · exact absurd (key ρ h) hf
    · refine key _ ?_
      rw [conjEmb_apply, h, map_neg, hcj, neg_neg]

/- English proof (translation)
Introduce `a` and use `by refine ⟨hm a, ?_⟩ unfold Formalism.MainNotions.StandardLatticesGL3.cj Formalism.MainNotions.TaylorLogMetric.liftM rw [dif_pos (hm a)] exact h a _ rfl`.
-/
theorem fixK_of_fixesK (D : D7) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ)
    (hm : ∀ a : D.host.K, D.host.φ₀ (a : D.host.E) ∈ M) (h : GlobalTheory.IndefiniteRowSideFullHecke.EquidistributedConjugates.FixesK D M ρ) :
    Formalism.MainNotions.StandardLatticesGL3.FixK D M ρ := fun a => by
  refine ⟨hm a, ?_⟩
  unfold Formalism.MainNotions.StandardLatticesGL3.cj Formalism.MainNotions.TaylorLogMetric.liftM
  rw [dif_pos (hm a)]
  exact h a _ rfl

open GlobalTheory.IndefiniteRowSideFullHecke.EquidistributedConjugates

end GlobalTheory.ConjEquidistrib
