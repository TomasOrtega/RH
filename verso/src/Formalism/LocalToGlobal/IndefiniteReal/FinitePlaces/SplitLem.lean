import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.AffineProjectionSplitting
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IpTheta

set_option synthInstance.maxHeartbeats 100000

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (S T : HSp D)

/- English proof (translation)
Establish `hinv : HMul.hMul (mt V g⁻¹) (mt V g) = (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))`. Rewrite using `[← Formalism.IndefR.Eqv.mt_mul, inv_mul_cancel, Formalism.IndefR.Eqv.mt_one]`. Establish `hd : (mt V g⁻¹ : Matrix (Fin V.rank) (Fin V.rank) (AE D)) - 1 = -(HMul.hMul (mt V g⁻¹) ((mt V g : Matrix (Fin V.rank) (Fin V.rank) (AE D)) - 1))`. Rewrite using `[Matrix.mul_sub, hinv, Matrix.mul_one, neg_sub]`. Introduce `i j`.

Rewrite using `[hd, Matrix.neg_apply, mul_neg, Matrix.mul_apply, Finset.mul_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mul_left_comm, hg k j]`.
-/
theorem suppAt_inv_fp {e : AE D} {V : HSp D} {g : GA D V} (hg : SuppAt e V g) : SuppAt e V g⁻¹ := by
  have hinv : HMul.hMul (mt V g⁻¹) (mt V g) = (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
    rw [← Formalism.IndefR.Eqv.mt_mul, inv_mul_cancel, Formalism.IndefR.Eqv.mt_one]
  have hd : (mt V g⁻¹ : Matrix (Fin V.rank) (Fin V.rank) (AE D)) - 1 =
      -(HMul.hMul (mt V g⁻¹) ((mt V g : Matrix (Fin V.rank) (Fin V.rank) (AE D)) - 1)) := by
    rw [Matrix.mul_sub, hinv, Matrix.mul_one, neg_sub]
  intro i j
  rw [hd, Matrix.neg_apply, mul_neg, Matrix.mul_apply, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, hg k j]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Rewrite using `[zero_smul, zero_smul]`. Unfold `actO`. Rewrite using `[Matrix.mul_zero, Matrix.zero_mul]`.

Consider the case `succ n ih => rw [succ_nsmul, succ_nsmul, Formalism.IndefR.Eqv.actO_add, ih]`.
-/
theorem actO_nsmul (g : GA D S) (h : GA D T) (k : ℕ) (t : WO S T) : actO S T g h (k • t) = k • actO S T g h t := by
  induction k with
  | zero =>
    rw [zero_smul, zero_smul]
    unfold actO
    rw [Matrix.mul_zero, Matrix.zero_mul]
  | succ n ih => rw [succ_nsmul, succ_nsmul, Formalism.IndefR.Eqv.actO_add, ih]

/- English proof (translation)
Introduce `i j`. Unfold `actO`. Simplify using `only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Use `conv_rhs => rw [← ht l k]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem isHalf_actO_fp {e : AE D} (g : GA D S) (h : GA D T) {t : WO S T} (ht : IsHalf e t) :
    IsHalf e (actO S T g h t) := by
  intro i j
  unfold actO
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  conv_rhs => rw [← ht l k]
  ring

/- English proof (translation)
Introduce `i j` and use `by rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hv i j]`.
-/
theorem isHalf_nsmul_fp {e : AE D} {v : WO S T} (hv : IsHalf e v) (m : ℕ) : IsHalf e (m • v) := fun i j => by
  rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hv i j]

/- English proof (translation)
Use `⟨fun h' => ?_, isHalf_actO_fp S T g h⟩` and prove the remaining obligations. Use `isHalf_actO_fp S T g⁻¹ h⁻¹ h'` as an intermediate fact. Rewrite `this` using `[Formalism.IndefR.Eqv.actO_actO_inv]`. Then use the resulting hypothesis.
-/
theorem isHalf_actO_iff {e : AE D} (g : GA D S) (h : GA D T) (t : WO S T) :
    IsHalf e (actO S T g h t) ↔ IsHalf e t := by
  refine ⟨fun h' => ?_, isHalf_actO_fp S T g h⟩
  have := isHalf_actO_fp S T g⁻¹ h⁻¹ h'
  rwa [Formalism.IndefR.Eqv.actO_actO_inv] at this

open Classical in
/- English proof (translation)
Unfold `halfInd`. Establish `h1 : s + u ∈ Λ ↔ s ∈ Λ` using `⟨fun h => by simpa using Λ.sub_mem h hu, fun h => Λ.add_mem h hu⟩`. Establish `h2 : IsHalf e (s + u) ↔ IsHalf e s`. Prove the components needed by the constructor for the conclusion. Introduce `h i j`.

Use `h i j` as an intermediate fact. Rewrite `this` using `[Matrix.add_apply, mul_add, hue i j]`. Conclude with `add_right_cancel this`. Introduce `h i j`. Rewrite using `[Matrix.add_apply, mul_add, h i j, hue i j]`.

Simplify using `only [h1, h2]`.
-/
theorem halfInd_add {e : AE D} {Λ : AddSubgroup (WO S T)} {u : WO S T} (hu : u ∈ Λ) (hue : IsHalf e u)
    (s : WO S T) : halfInd e Λ (s + u) = halfInd e Λ s := by
  unfold halfInd
  have h1 : s + u ∈ Λ ↔ s ∈ Λ := ⟨fun h => by simpa using Λ.sub_mem h hu, fun h => Λ.add_mem h hu⟩
  have h2 : IsHalf e (s + u) ↔ IsHalf e s := by
    constructor
    · intro h i j
      have := h i j
      rw [Matrix.add_apply, mul_add, hue i j] at this
      exact add_right_cancel this
    · intro h i j
      rw [Matrix.add_apply, mul_add, h i j, hue i j]
  simp only [h1, h2]

/- English proof (translation)
Take `⟨hs, k, hk, hi, hl⟩` from `hΦ`. Use `⟨fun t ht => (isHalf_actO_iff S T g h t).1 (hs _ ht), k * k₁ * k₂, by positivity, fun u hu hue t => ?_, fun t ht => ?_⟩` and prove the remaining obligations. Use `show Φ (actO S T g h (t + (k * k₁ * k₂) • u)) = Φ (actO S T g h t)`. Rewrite using `[Formalism.IndefR.Eqv.actO_add, actO_nsmul, show (k * k₁ * k₂) • actO S T g h u = k • (k₂ • (k₁ • actO S T g h u)) by rw [smul_smul, smul_smul]; ring_nf]`. Conclude with `hi _ (Λ.nsmul_mem (h₁ u hu) k₂) (isHalf_nsmul_fp S T (isHalf_nsmul_fp S T (isHalf_actO_fp S T g h hue) k₁) k₂) _`.

Establish `h1` using `hl _ ht`. Establish `h2` using `h₂ _ h1`. Rewrite `h2` using `[actO_nsmul, Formalism.IndefR.Eqv.actO_actO_inv, smul_smul]`. Rewrite using `[show k * k₁ * k₂ = k₁ * (k₂ * k) by ring, ← smul_smul]`. Conclude with `Λ.nsmul_mem h2 k₁`.
-/
theorem sb_comp {e : AE D} {Λ : AddSubgroup (WO S T)} (g : GA D S) (h : GA D T)
    {k₁ : ℕ} (hk₁ : 0 < k₁) (h₁ : ∀ t ∈ Λ, k₁ • actO S T g h t ∈ Λ)
    {k₂ : ℕ} (hk₂ : 0 < k₂) (h₂ : ∀ t ∈ Λ, k₂ • actO S T g⁻¹ h⁻¹ t ∈ Λ)
    {Φ : WO S T → ℂ} (hΦ : IsSBHalf e Λ Φ) : IsSBHalf e Λ (fun t => Φ (actO S T g h t)) := by
  obtain ⟨hs, k, hk, hi, hl⟩ := hΦ
  refine ⟨fun t ht => (isHalf_actO_iff S T g h t).1 (hs _ ht), k * k₁ * k₂, by positivity,
    fun u hu hue t => ?_, fun t ht => ?_⟩
  · show Φ (actO S T g h (t + (k * k₁ * k₂) • u)) = Φ (actO S T g h t)
    rw [Formalism.IndefR.Eqv.actO_add, actO_nsmul, show (k * k₁ * k₂) • actO S T g h u =
      k • (k₂ • (k₁ • actO S T g h u)) by rw [smul_smul, smul_smul]; ring_nf]
    exact hi _ (Λ.nsmul_mem (h₁ u hu) k₂)
      (isHalf_nsmul_fp S T (isHalf_nsmul_fp S T (isHalf_actO_fp S T g h hue) k₁) k₂) _
  · have h1 := hl _ ht
    have h2 := h₂ _ h1
    rw [actO_nsmul, Formalism.IndefR.Eqv.actO_actO_inv, smul_smul] at h2
    rw [show k * k₁ * k₂ = k₁ * (k₂ * k) by ring, ← smul_smul]
    exact Λ.nsmul_mem h2 k₁

end Formalism.IndefR.Fin

end
