import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVBadTOfIsoWX

noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
  Topology Filter
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

def LeftInvRes (a : ℕ) : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → ∀ ϖ : Fv F v, IsUnif v ϖ →
  ∀ M : Matrix (Fin n) (Fin a) (Fv F v ⊗[F] E), (∀ k i, M k i ∈ OEv (E := E) v) →
    (∀ c : Fin a → Fv F v ⊗[F] E, (∀ k, Matrix.mulVec M c k ∈ OEv (E := E) v) → ∀ i, c i ∈ OEv (E := E) v) →
    ∃ N0 : Matrix (Fin a) (Fin n) (Fv F v ⊗[F] E), ∃ B : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E),
      (∀ i k, N0 i k ∈ OEv (E := E) v) ∧ (∀ i j, B i j ∈ OEv (E := E) v) ∧
      N0 * M = 1 + sc (E := E) v ϖ • B

/- English proof (translation)
Rewrite using `[Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Both sides reduce to the same expression.
-/
theorem near_mulVec {a : ℕ} (ϖ : Fv F v) (B : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) (x : Fin a → Fv F v ⊗[F] E)
    (i : Fin a) :
    Matrix.mulVec (1 + sc (E := E) v ϖ • B) x i = x i + sc (E := E) v ϖ * ∑ j, B i j * x j := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rfl

/- English proof (translation)
Introduce `hS hUn M hM hsat`. Take `⟨ϖ, hϖ⟩` from `unifEx_holds v`. Take `⟨h0, hπ, -⟩` from `unif_spec v ϖ hϖ`. Take `⟨N0, B, hN0, hB, hNB⟩` from `hR hS hUn ϖ hϖ M hM hsat`. Use `set C : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) := 1 + sc (E := E) v ϖ • B with hCdef`.

Establish `hker : ∀ d : Fin a → Fv F v ⊗[F] E, Matrix.mulVec C d = 0 → d = 0`. Introduce `d hd`. Use function extensionality and compare the values at `i`. Establish `hm : ∀ m : ℕ, sc (E` using `E) v (ϖ ^ m)⁻¹ * d i ∈ OEv (E := E) v := by`. Introduce `m`.

Use `near_int v ϖ hϖ B hB (fun j => sc (E := E) v (ϖ ^ m)⁻¹ * d j) (fun j => ?_) i` and prove the remaining obligations. Use `near_mulVec v ϖ B (sc (E := E) v (ϖ ^ m)⁻¹ • d) j` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_smul, ← hCdef, hd, smul_zero]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this`. Rewrite using `[← this]`.

Conclude with `oEv_zero v`. Assume the negation of the conclusion as `hne`. Establish `hN : {x : Fv F v ⊗[F] E | x ≠ d i} ∈ 𝓝 (0 : Fv F v ⊗[F] E)` using `isOpen_ne.mem_nhds (Ne.symm hne)`. Take `⟨k, hk⟩` from `PI.VolStabSW.eventually_smul_sub (OEv (E := E) v) (isCompact_oEv v) (fun k => ϖ ^ k) hπ _ hN`. Apply `hk _ (hm k)` to reduce the goal to its premises.

Use `show ϖ ^ k • (sc (E := E) v (ϖ ^ k)⁻¹ * d i) = d i`. Rewrite using `[smul_eq_sc, ← mul_assoc, sc_mul, mul_inv_cancel₀ (pow_ne_zero _ h0), sc_one, one_mul]`. Establish `hinj : Function.Injective (Matrix.mulVecLin C)`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Conclude with `fun d hd => hker d hd`.

Establish `: FiniteDimensional F E` using `Module.Finite.of_restrictScalars_finite ℚ F E`. Establish `hsurj : Function.Surjective (Matrix.mulVecLin C)`. Establish `hinj' : Function.Injective ((Matrix.mulVecLin C).restrictScalars (Fv F v))` using `hinj`. Conclude with `(LinearMap.injective_iff_surjective (f := (Matrix.mulVecLin C).restrictScalars (Fv F v))).1 hinj'`. Establish `hCu : IsUnit C` using `Matrix.mulVec_surjective_iff_isUnit.1 hsurj`.

Establish `hCd : IsUnit C.det` using `(Matrix.isUnit_iff_isUnit_det C).1 hCu`. Establish `hCi : ∀ i j, C⁻¹ i j ∈ OEv (E` using `E) v := by`. Introduce `i j`. Establish `hcol : ∀ l, (fun k => C⁻¹ k j) l + sc (E` using `E) v ϖ * ∑ k, B l k * (fun k => C⁻¹ k j) k ∈ OEv (E := E) v := by`. Introduce `l`.

Rewrite using `[← near_mulVec v ϖ B (fun k => C⁻¹ k j) l, ← hCdef]`. Establish `e : Matrix.mulVec C (fun k => C⁻¹ k j) l = (C * C⁻¹) l j`. Simplify using `[Matrix.mulVec, dotProduct, Matrix.mul_apply]`. Rewrite using `[e, Matrix.mul_nonsing_inv C hCd, Matrix.one_apply]`. Use `split_ifs`.

Conclude with `one_mem_O v`. Conclude with `oEv_zero v`. Conclude with `near_int v ϖ hϖ B hB _ hcol i`. Use `⟨C⁻¹ * N0, fun i k => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply]`.

Conclude with `oEv_sum v _ _ fun l _ => oEv_mul v (hCi i l) (hN0 l k)`. Rewrite using `[Matrix.mul_assoc, hNB, Matrix.nonsing_inv_mul C hCd]`.
-/
theorem leftInvO_of (a : ℕ) (hR : LeftInvRes σ J ψ v (n := n) a) : LeftInvO σ J ψ v (n := n) a := by
  intro hS hUn M hM hsat
  obtain ⟨ϖ, hϖ⟩ := unifEx_holds v
  obtain ⟨h0, hπ, -⟩ := unif_spec v ϖ hϖ
  obtain ⟨N0, B, hN0, hB, hNB⟩ := hR hS hUn ϖ hϖ M hM hsat
  set C : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) := 1 + sc (E := E) v ϖ • B with hCdef

  have hker : ∀ d : Fin a → Fv F v ⊗[F] E, Matrix.mulVec C d = 0 → d = 0 := by
    intro d hd
    funext i
    have hm : ∀ m : ℕ, sc (E := E) v (ϖ ^ m)⁻¹ * d i ∈ OEv (E := E) v := by
      intro m
      refine near_int v ϖ hϖ B hB (fun j => sc (E := E) v (ϖ ^ m)⁻¹ * d j) (fun j => ?_) i
      have := near_mulVec v ϖ B (sc (E := E) v (ϖ ^ m)⁻¹ • d) j
      rw [Matrix.mulVec_smul, ← hCdef, hd, smul_zero] at this
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      rw [← this]
      exact oEv_zero v
    by_contra hne
    have hN : {x : Fv F v ⊗[F] E | x ≠ d i} ∈ 𝓝 (0 : Fv F v ⊗[F] E) := isOpen_ne.mem_nhds (Ne.symm hne)
    obtain ⟨k, hk⟩ := PI.VolStabSW.eventually_smul_sub (OEv (E := E) v) (isCompact_oEv v) (fun k => ϖ ^ k) hπ _ hN
    apply hk _ (hm k)
    show ϖ ^ k • (sc (E := E) v (ϖ ^ k)⁻¹ * d i) = d i
    rw [smul_eq_sc, ← mul_assoc, sc_mul, mul_inv_cancel₀ (pow_ne_zero _ h0), sc_one, one_mul]
  have hinj : Function.Injective (Matrix.mulVecLin C) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    exact fun d hd => hker d hd
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hsurj : Function.Surjective (Matrix.mulVecLin C) := by
    have hinj' : Function.Injective ((Matrix.mulVecLin C).restrictScalars (Fv F v)) := hinj
    exact (LinearMap.injective_iff_surjective (f := (Matrix.mulVecLin C).restrictScalars (Fv F v))).1 hinj'
  have hCu : IsUnit C := Matrix.mulVec_surjective_iff_isUnit.1 hsurj
  have hCd : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).1 hCu

  have hCi : ∀ i j, C⁻¹ i j ∈ OEv (E := E) v := by
    intro i j
    have hcol : ∀ l, (fun k => C⁻¹ k j) l + sc (E := E) v ϖ * ∑ k, B l k * (fun k => C⁻¹ k j) k ∈ OEv (E := E) v := by
      intro l
      rw [← near_mulVec v ϖ B (fun k => C⁻¹ k j) l, ← hCdef]
      have e : Matrix.mulVec C (fun k => C⁻¹ k j) l = (C * C⁻¹) l j := by
        simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
      rw [e, Matrix.mul_nonsing_inv C hCd, Matrix.one_apply]
      split_ifs
      · exact one_mem_O v
      · exact oEv_zero v
    exact near_int v ϖ hϖ B hB _ hcol i
  refine ⟨C⁻¹ * N0, fun i k => ?_, ?_⟩
  · rw [Matrix.mul_apply]
    exact oEv_sum v _ _ fun l _ => oEv_mul v (hCi i l) (hN0 l k)
  · rw [Matrix.mul_assoc, hNB, Matrix.nonsing_inv_mul C hCd]

end PI.OmVd
