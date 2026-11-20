import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLeAndExistsRatPtsSwap
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ResidueEisenstein.Swap

open GlobalTheory.ResLine.Swap

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J r X Y hσ hJ hW`. Establish `hxx : Formalism.UG.cT (σ : E →+* E) X * J * X = 0` using `hW.xx`. Establish `hyy : Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0` using `hW.yy`. Establish `hxy : Formalism.UG.cT (σ : E →+* E) X * J * Y = 1` using `hW.xy`. Establish `hJ'` using `cT_eq_of_isHermND hJ`.

Establish `hyx : Formalism.UG.cT (σ : E →+* E) Y * J * X = 1`. Establish `h` using `congrArg (Formalism.UG.cT (σ : E →+* E)) hxy`. Rewrite `h` using `[Formalism.UG.cT_mul, Formalism.UG.cT_mul, cT_cT_of_isCMExt hσ, hJ', Formalism.UG.cT_one]`. Simplify `h` using `[Matrix.mul_assoc]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Set `f : ((Fin (r + 1) → E) × (Fin (r + 1) → E)) →ₗ[E] (Fin n → E)` to `Y.mulVecLin.comp (LinearMap.fst E _ _) + X.mulVecLin.comp (LinearMap.snd E _ _)`. Establish `hf : Function.Injective f`. Introduce `p q hpq`. Establish `hp : ∀ p : (Fin (r + 1) → E) × (Fin (r + 1) → E), (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ f p = p.1 ∧ (Formalism.UG.cT (σ : E →+* E) Y * J) *ᵥ f p = p.2`. Introduce `p`.

Simplify using `only [f, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply, Matrix.mulVecLin_apply, Matrix.mulVec_add, Matrix.mulVec_mulVec, hxx, hyy, hxy, hyx, Matrix.one_mulVec, Matrix.zero_mulVec, add_zero, zero_add]`. Conclude with `⟨trivial, trivial⟩`. Establish `h1` using `hp p`. Establish `h2` using `hp q`. Rewrite `h1` using `[hpq]`.

Conclude with `Prod.ext (h1.1.symm.trans h2.1) (h1.2.symm.trans h2.2)`. Establish `h` using `LinearMap.finrank_le_finrank_of_injective hf`. Simplify `h` using `[Module.finrank_prod, two_mul]`. Use `set u := X - Y with hu`. Use `set v := Formalism.UG.cT (σ : E →+* E) u * J with hv`.

Establish `hvy : v * Y = 1`. Rewrite using `[hv, hu, cT_sub', Matrix.sub_mul, Matrix.sub_mul, hxy, hyy, sub_zero]`. Establish `hvx : v * X = -1`. Rewrite using `[hv, hu, cT_sub', Matrix.sub_mul, Matrix.sub_mul, hxx, hyx, zero_sub]`. Use `set w0 : Matrix (Fin n) (Fin n) E := 1 + u * v with hw0`.

Establish `hw0y : w0 * Y = X`. Rewrite using `[hw0, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hvy, Matrix.mul_one, hu]`. Normalize the expressions using the abelian group laws. Establish `hw0x : w0 * X = Y`. Rewrite using `[hw0, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hvx, Matrix.mul_neg, Matrix.mul_one, hu]`.

Normalize the expressions using the abelian group laws. Establish `hw0u : w0 * u = -u`. Rewrite using `[hu, Matrix.mul_sub, hw0y, hw0x]`. Normalize the expressions using the abelian group laws. Establish `hsq : w0 * w0 = 1` using `by conv_lhs => rw [show w0 * w0 = w0 * (1 + u * v) from rfl]`.

Rewrite using `[Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hw0u, hw0, Matrix.neg_mul]`. Normalize the expressions using the abelian group laws. Establish `hcw : Formalism.UG.cT (σ : E →+* E) w0 * J = J * w0`. Rewrite using `[hw0, cT_add', Formalism.UG.cT_one, Formalism.UG.cT_mul, hv, Formalism.UG.cT_mul, cT_cT_of_isCMExt hσ, hJ', Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one]`. Simplify using `only [Matrix.mul_assoc]`.

Establish `hunit : Formalism.UG.cT (σ : E →+* E) w0 * J * w0 = J`. Rewrite using `[hcw, Matrix.mul_assoc, hsq, Matrix.mul_one]`. Set `U : GL (Fin n) E` to `⟨w0, w0, hsq, hsq⟩`. Establish `hU : U ∈ Formalism.UG.UJ (σ : E →+* E) J` using `hunit`. Use `⟨GlobalTheory.AdelicU.ratEmb σ J ⟨U, hU⟩, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← GlobalTheory.AdelicU.range_ratEmb]`. Conclude with `⟨_, rfl⟩`. Express the relevant statement in the definitionally equal form `w0.map (inclR (F := F) (AF F)) * adMat F Y = adMat F X`. Simplify using `only [adMat]`. Rewrite using `[← Matrix.map_mul, hw0y]`.

Express the relevant statement in the definitionally equal form `w0.map (inclR (F := F) (AF F)) * adMat F X = adMat F Y`. Simplify using `only [adMat]`. Rewrite using `[← Matrix.map_mul, hw0x]`.
-/
theorem two_mul_le_and_exists_ratPts_swap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E),
    IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
    2 * (r + 1) ≤ n ∧ ∃ w ∈ ratPts σ J, (matHom _ σ J w).1 * adMat F Y = adMat F X ∧
      (matHom _ σ J w).1 * adMat F X = adMat F Y := by
  intro F E _ _ _ _ _ σ n J r X Y hσ hJ hW
  classical
  have hxx : Formalism.UG.cT (σ : E →+* E) X * J * X = 0 := hW.xx
  have hyy : Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0 := hW.yy
  have hxy : Formalism.UG.cT (σ : E →+* E) X * J * Y = 1 := hW.xy
  have hJ' := cT_eq_of_isHermND hJ
  have hyx : Formalism.UG.cT (σ : E →+* E) Y * J * X = 1 := by
    have h := congrArg (Formalism.UG.cT (σ : E →+* E)) hxy
    rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cT_cT_of_isCMExt hσ, hJ', Formalism.UG.cT_one] at h
    simpa [Matrix.mul_assoc] using h
  refine ⟨?_, ?_⟩
  ·
    let f : ((Fin (r + 1) → E) × (Fin (r + 1) → E)) →ₗ[E] (Fin n → E) :=
      Y.mulVecLin.comp (LinearMap.fst E _ _) + X.mulVecLin.comp (LinearMap.snd E _ _)
    have hf : Function.Injective f := by
      intro p q hpq
      have hp : ∀ p : (Fin (r + 1) → E) × (Fin (r + 1) → E),
          (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ f p = p.1 ∧ (Formalism.UG.cT (σ : E →+* E) Y * J) *ᵥ f p = p.2 := by
        intro p
        simp only [f, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply,
          Matrix.mulVecLin_apply, Matrix.mulVec_add, Matrix.mulVec_mulVec, hxx, hyy, hxy, hyx,
          Matrix.one_mulVec, Matrix.zero_mulVec, add_zero, zero_add]
        exact ⟨trivial, trivial⟩
      have h1 := hp p
      have h2 := hp q
      rw [hpq] at h1
      exact Prod.ext (h1.1.symm.trans h2.1) (h1.2.symm.trans h2.2)
    have h := LinearMap.finrank_le_finrank_of_injective hf
    simpa [Module.finrank_prod, two_mul] using h
  set u := X - Y with hu
  set v := Formalism.UG.cT (σ : E →+* E) u * J with hv
  have hvy : v * Y = 1 := by
    rw [hv, hu, cT_sub', Matrix.sub_mul, Matrix.sub_mul, hxy, hyy, sub_zero]
  have hvx : v * X = -1 := by
    rw [hv, hu, cT_sub', Matrix.sub_mul, Matrix.sub_mul, hxx, hyx, zero_sub]
  set w0 : Matrix (Fin n) (Fin n) E := 1 + u * v with hw0
  have hw0y : w0 * Y = X := by
    rw [hw0, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hvy, Matrix.mul_one, hu]; abel
  have hw0x : w0 * X = Y := by
    rw [hw0, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hvx, Matrix.mul_neg, Matrix.mul_one, hu]; abel
  have hw0u : w0 * u = -u := by
    rw [hu, Matrix.mul_sub, hw0y, hw0x]; abel
  have hsq : w0 * w0 = 1 := by
    conv_lhs => rw [show w0 * w0 = w0 * (1 + u * v) from rfl]
    rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hw0u, hw0, Matrix.neg_mul]; abel
  have hcw : Formalism.UG.cT (σ : E →+* E) w0 * J = J * w0 := by
    rw [hw0, cT_add', Formalism.UG.cT_one, Formalism.UG.cT_mul, hv, Formalism.UG.cT_mul, cT_cT_of_isCMExt hσ, hJ',
      Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  have hunit : Formalism.UG.cT (σ : E →+* E) w0 * J * w0 = J := by
    rw [hcw, Matrix.mul_assoc, hsq, Matrix.mul_one]
  let U : GL (Fin n) E := ⟨w0, w0, hsq, hsq⟩
  have hU : U ∈ Formalism.UG.UJ (σ : E →+* E) J := hunit
  refine ⟨GlobalTheory.AdelicU.ratEmb σ J ⟨U, hU⟩, ?_, ?_, ?_⟩
  · rw [← GlobalTheory.AdelicU.range_ratEmb]; exact ⟨_, rfl⟩
  · change w0.map (inclR (F := F) (AF F)) * adMat F Y = adMat F X
    simp only [adMat]
    rw [← Matrix.map_mul, hw0y]
  · change w0.map (inclR (F := F) (AF F)) * adMat F X = adMat F Y
    simp only [adMat]
    rw [← Matrix.map_mul, hw0x]

end GlobalTheory.ResidueEisenstein.Swap

end
