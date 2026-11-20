import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupSecondKindCoordinatesNearOne

open Matrix
open scoped Topology

noncomputable section

namespace GlobalTheory.UnitaryGroupChart

open Filter

/- English proof (translation)
Establish `: CompleteSpace E` using `FiniteDimensional.complete ℝ E`. Set `: NormedAlgebra ℚ E` to `NormedAlgebra.restrictScalars ℚ ℝ E`. Establish `hexp : ∀ a, σ (NormedSpace.exp a) = NormedSpace.exp (σ a)` using `fun a => by`. Establish `hp : ∀ m : ℕ, σ (a ^ m) = σ a ^ m` using `fun m => by`. Proceed by induction on `m with`.

Consider the case `zero => simpa using h1`. Consider the case `succ m ih => rw [pow_succ, hm, ih, pow_succ']`. Establish `h2` using `(NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) a).map σ.toAddMonoidHom σ.continuous_of_finiteDimensional`. Use `h2.unique ?_` and prove the remaining obligations. Use `NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (σ a) using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `m`. Simplify using `[hp]`. Set `cL : (Fin e → ℝ) →ₗ[ℝ] (Fin d → ℝ)` to `Fintype.linearCombination ℝ (fun i => Pi.single (j i) (1 : ℝ))`. Set `cC : (Fin e → ℝ) →L[ℝ] (Fin d → ℝ)` to `LinearMap.toContinuousLinearMap cL`. Establish `hcC : ∀ t, cC t = cL t` using `fun _ => rfl`.

Establish `hsum : ∀ t : Fin e → ℝ, ∑ a, cL t a • Z a = ∑ i, t i • Z (j i)` using `fun t => by`. Simplify using `only [cL, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[ite_smul]`.

Use `set Θ : (Fin e → ℝ) → E := fun t => (List.ofFn fun a => NormedSpace.exp (cL t a • Z a)).prod with hΘ`. Establish `hU : ∀ t, σ (Θ t) * Θ t = 1 ∧ Θ t * σ (Θ t) = 1` using `fun t => GlobalTheory.UnitaryChart.unitary_list_prod σ hm h1 _ (fun u hu => by`. Take `⟨a, rfl⟩` from `List.mem_ofFn.mp hu`. Rewrite using `[hexp, map_smul, hZσ, smul_neg, ← NormedSpace.exp_add_of_commute (Commute.refl _).neg_left, ← NormedSpace.exp_add_of_commute (Commute.refl _).neg_right]`. Use the proof step `simp)`.

Set `T : (Fin e → ℝ) →L[ℝ] E` to `∑ a, (ContinuousLinearMap.toSpanSingleton ℝ (Z a)).comp ((ContinuousLinearMap.proj a).comp cC)`. Establish `hT : ∀ t, T t = ∑ i, t i • Z (j i)` using `fun t => by`. Rewrite using `[← hsum]`. Simplify using `[T, hcC]`. Take `⟨h0, hD⟩ : Θ 0 = 1 ∧ HasStrictFDerivAt Θ T 0` from `GlobalTheory.UnitaryChart.hasStrictFDerivAt_ofFn_prod d (fun a (t : Fin e → ℝ) => NormedSpace.exp (cL t a • Z a)) _ (fun a => by`.

Use `⟨by simp, ?_⟩` and prove the remaining obligations. Establish `hd : HasStrictFDerivAt (fun s : ℝ => NormedSpace.exp (s • Z a)) (ContinuousLinearMap.toSpanSingleton ℝ (Z a)) (((ContinuousLinearMap.proj a).comp cC) 0)`. Rewrite using `[map_zero]`. Simplify using `using (hasStrictDerivAt_exp_smul_const (𝕂 := ℝ) (Z a) (0 : ℝ)).hasStrictFDerivAt`. Conclude with `hd.comp (0 : Fin e → ℝ) ((ContinuousLinearMap.proj a).comp cC).hasStrictFDerivAt)`.

Take `⟨P, hP1, hP2, hP3⟩` from `GlobalTheory.UnitaryChart.exists_skew_coord σ (fun i => Z (j i)) hσ hli (fun i => hZσ (j i)) hsp`. Establish `hΨ : HasStrictFDerivAt (fun t => P (Θ t)) ((ContinuousLinearEquiv.refl ℝ (Fin e → ℝ) : (Fin e → ℝ) →L[ℝ] (Fin e → ℝ))) 0`. Use `(P.hasStrictFDerivAt.comp 0 hD).congr_fderiv ?_` and prove the remaining obligations. Use `ext1 t`. Simplify using `[hT, hP1]`.

Establish `hP0 : P 1 = 0` using `hP2 _ h1`. Establish `hΨ0 : P (Θ 0) = 0` using `by rw [h0, hP0]`. Establish `p1` using `hΨ.localInverse_continuousAt`. Establish `p2` using `hΨ.localInverse_apply_image`. Establish `p3` using `hΨ.eventually_right_inverse`.

Simplify using `only [hΨ0] at p1 p2 p3`. Use `set Ψ := hΨ.localInverse _ _ _`. Establish `hσc : Continuous σ` using `σ.continuous_of_finiteDimensional`. Establish `hnear : ∀ᶠ m in 𝓝 (1 : E), ‖1 - σ m‖ ≤ 1 / 2`. Establish `: ContinuousAt (fun m => ‖1 - σ m‖) 1` using `(continuous_const.sub hσc).norm.continuousAt`.

Conclude with `this.eventually_le_const (by simp [h1])`. Establish `hPt : Tendsto P (𝓝 1) (𝓝 0)` using `hP0 ▸ P.continuous.tendsto 1`. Establish `hcont : ContinuousAt (fun g => Ψ (P g)) 1` using `ContinuousAt.comp_of_eq p1 P.continuous.continuousAt hP0`. Establish `ht : Tendsto (fun g => Θ (Ψ (P g))) (𝓝 1) (𝓝 1)`. Establish `h3 : Tendsto (fun g => Ψ (P g)) (𝓝 1) (𝓝 0)`.

Use `hcont.tendsto` as an intermediate fact. Simplify using `only [hP0, p2] at this`. Conclude with `this`. Use `hD.continuousAt.tendsto.comp h3` as an intermediate fact. Rewrite `this` using `[h0]`. Then use the resulting hypothesis.

Use `⟨fun g => cL (Ψ (P g)), cC.continuous.continuousAt.comp hcont, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hPt.eventually p3, hnear, ht.eventually hnear] with g q1 q2 q3 hg1`. Use `haveI : IsArtinianRing E := IsArtinianRing.of_finite ℝ E`. Conclude with `(GlobalTheory.UnitaryChart.eq_of_skew_eq (hU _).1 (mul_eq_one_comm.1 hg1) (hP3 _ _ q1) q3 q2).symm`.
-/
theorem chart_general {E : Type} [NormedRing E] [NormedAlgebra ℝ E] [FiniteDimensional ℝ E]
    (σ : E →ₗ[ℝ] E) (hσ : ∀ a, σ (σ a) = a) (hm : ∀ a b, σ (a * b) = σ b * σ a) (h1 : σ 1 = 1)
    {d e : ℕ} (Z : Fin d → E) (j : Fin e → Fin d) (hZσ : ∀ a, σ (Z a) = -Z a)
    (hli : LinearIndependent ℝ (fun i => Z (j i)))
    (hsp : ∀ X, σ X = -X → X ∈ Submodule.span ℝ (Set.range fun i => Z (j i))) :
    ∃ s : E → (Fin d → ℝ), ContinuousAt s 1 ∧
      ∀ᶠ g in 𝓝 (1 : E), σ g * g = 1 →
        g = (List.ofFn fun a => NormedSpace.exp (s g a • Z a)).prod := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : NormedAlgebra ℚ E := NormedAlgebra.restrictScalars ℚ ℝ E
  have hexp : ∀ a, σ (NormedSpace.exp a) = NormedSpace.exp (σ a) := fun a => by
    have hp : ∀ m : ℕ, σ (a ^ m) = σ a ^ m := fun m => by
      induction m with
      | zero => simpa using h1
      | succ m ih => rw [pow_succ, hm, ih, pow_succ']
    have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) a).map σ.toAddMonoidHom
      σ.continuous_of_finiteDimensional
    refine h2.unique ?_
    convert NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (σ a) using 1
    funext m
    simp [hp]
  let cL : (Fin e → ℝ) →ₗ[ℝ] (Fin d → ℝ) :=
    Fintype.linearCombination ℝ (fun i => Pi.single (j i) (1 : ℝ))
  let cC : (Fin e → ℝ) →L[ℝ] (Fin d → ℝ) := LinearMap.toContinuousLinearMap cL
  have hcC : ∀ t, cC t = cL t := fun _ => rfl
  have hsum : ∀ t : Fin e → ℝ, ∑ a, cL t a • Z a = ∑ i, t i • Z (j i) := fun t => by
    simp only [cL, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, Pi.single_apply,
      smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [ite_smul]
  set Θ : (Fin e → ℝ) → E :=
    fun t => (List.ofFn fun a => NormedSpace.exp (cL t a • Z a)).prod with hΘ
  have hU : ∀ t, σ (Θ t) * Θ t = 1 ∧ Θ t * σ (Θ t) = 1 := fun t =>
    GlobalTheory.UnitaryChart.unitary_list_prod σ hm h1 _ (fun u hu => by
      obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hu
      rw [hexp, map_smul, hZσ, smul_neg, ← NormedSpace.exp_add_of_commute (Commute.refl _).neg_left,
        ← NormedSpace.exp_add_of_commute (Commute.refl _).neg_right]
      simp)
  let T : (Fin e → ℝ) →L[ℝ] E :=
    ∑ a, (ContinuousLinearMap.toSpanSingleton ℝ (Z a)).comp ((ContinuousLinearMap.proj a).comp cC)
  have hT : ∀ t, T t = ∑ i, t i • Z (j i) := fun t => by
    rw [← hsum]
    simp [T, hcC]
  obtain ⟨h0, hD⟩ : Θ 0 = 1 ∧ HasStrictFDerivAt Θ T 0 :=
    GlobalTheory.UnitaryChart.hasStrictFDerivAt_ofFn_prod d
      (fun a (t : Fin e → ℝ) => NormedSpace.exp (cL t a • Z a)) _ (fun a => by
        refine ⟨by simp, ?_⟩
        have hd : HasStrictFDerivAt (fun s : ℝ => NormedSpace.exp (s • Z a))
            (ContinuousLinearMap.toSpanSingleton ℝ (Z a))
            (((ContinuousLinearMap.proj a).comp cC) 0) := by
          rw [map_zero]
          simpa using (hasStrictDerivAt_exp_smul_const (𝕂 := ℝ) (Z a) (0 : ℝ)).hasStrictFDerivAt
        exact hd.comp (0 : Fin e → ℝ) ((ContinuousLinearMap.proj a).comp cC).hasStrictFDerivAt)
  obtain ⟨P, hP1, hP2, hP3⟩ := GlobalTheory.UnitaryChart.exists_skew_coord σ (fun i => Z (j i)) hσ hli
    (fun i => hZσ (j i)) hsp
  have hΨ : HasStrictFDerivAt (fun t => P (Θ t))
      ((ContinuousLinearEquiv.refl ℝ (Fin e → ℝ) : (Fin e → ℝ) →L[ℝ] (Fin e → ℝ))) 0 := by
    refine (P.hasStrictFDerivAt.comp 0 hD).congr_fderiv ?_
    ext1 t
    simp [hT, hP1]
  have hP0 : P 1 = 0 := hP2 _ h1
  have hΨ0 : P (Θ 0) = 0 := by rw [h0, hP0]
  have p1 := hΨ.localInverse_continuousAt
  have p2 := hΨ.localInverse_apply_image
  have p3 := hΨ.eventually_right_inverse
  simp only [hΨ0] at p1 p2 p3
  set Ψ := hΨ.localInverse _ _ _
  have hσc : Continuous σ := σ.continuous_of_finiteDimensional
  have hnear : ∀ᶠ m in 𝓝 (1 : E), ‖1 - σ m‖ ≤ 1 / 2 := by
    have : ContinuousAt (fun m => ‖1 - σ m‖) 1 := (continuous_const.sub hσc).norm.continuousAt
    exact this.eventually_le_const (by simp [h1])
  have hPt : Tendsto P (𝓝 1) (𝓝 0) := hP0 ▸ P.continuous.tendsto 1
  have hcont : ContinuousAt (fun g => Ψ (P g)) 1 :=
    ContinuousAt.comp_of_eq p1 P.continuous.continuousAt hP0
  have ht : Tendsto (fun g => Θ (Ψ (P g))) (𝓝 1) (𝓝 1) := by
    have h3 : Tendsto (fun g => Ψ (P g)) (𝓝 1) (𝓝 0) := by
      have := hcont.tendsto
      simp only [hP0, p2] at this
      exact this
    have := hD.continuousAt.tendsto.comp h3
    rwa [h0] at this
  refine ⟨fun g => cL (Ψ (P g)), cC.continuous.continuousAt.comp hcont, ?_⟩
  filter_upwards [hPt.eventually p3, hnear, ht.eventually hnear] with g q1 q2 q3 hg1
  haveI : IsArtinianRing E := IsArtinianRing.of_finite ℝ E
  exact (GlobalTheory.UnitaryChart.eq_of_skew_eq (hU _).1 (mul_eq_one_comm.1 hg1) (hP3 _ _ q1) q3 q2).symm

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/- English proof (translation)
Establish `hHi : H⁻¹ * H = 1` using `Matrix.nonsing_inv_mul H hdet`. Establish `hHi' : H * H⁻¹ = 1` using `Matrix.mul_nonsing_inv H hdet`. Establish `hHih : (H⁻¹)ᴴ = H⁻¹` using `by rw [Matrix.conjTranspose_nonsing_inv, hH]`. Set `σ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ` to `{ toFun := fun x => H⁻¹ * xᴴ * H map_add' := fun x y => by rw [conjTranspose_add, Matrix.mul_add, Matrix.add_mul] map_smul' := fun c x => by simp [conjTranspose_smul] }`. Establish `hs : ∀ x, σ x = H⁻¹ * xᴴ * H` using `fun _ => rfl`.

Establish `hσ : ∀ a, σ (σ a) = a` using `fun a => by`. Simplify using `only [hs, conjTranspose_mul, conjTranspose_conjTranspose, hH, hHih, Matrix.mul_assoc]`. Rewrite using `[hHi, Matrix.mul_one, ← Matrix.mul_assoc, hHi, Matrix.one_mul]`. Establish `hm : ∀ a b, σ (a * b) = σ b * σ a` using `fun a b => by`. Simplify using `only [hs, conjTranspose_mul, Matrix.mul_assoc]`.

Rewrite using `[← Matrix.mul_assoc H, hHi', Matrix.one_mul]`. Establish `h1 : σ 1 = 1` using `by simp [hs, hHi]`. Establish `hZσ : ∀ a, σ (Z a) = -Z a` using `fun a => by`. Rewrite using `[hs, Matrix.mul_assoc, eq_neg_of_add_eq_zero_left (hZ a), Matrix.mul_neg, ← Matrix.mul_assoc, hHi, Matrix.one_mul]`. Establish `hsp' : ∀ X, σ X = -X → X ∈ Submodule.span ℝ (Set.range fun i => Z (j i))` using `fun X hX => by`.

Apply `hsp` to reduce the goal to its premises. Establish `h2 : H * σ X = Xᴴ * H`. Rewrite using `[hs, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hHi', Matrix.one_mul]`. Rewrite using `[← h2, hX, Matrix.mul_neg, neg_add_cancel]`. Take `⟨s, hs1, hs2⟩` from `chart_general σ hσ hm h1 Z j hZσ hli hsp'`.

Use `⟨s, hs1, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hs2] with g hg hgu`. Apply `hg` to reduce the goal to its premises. Simplify using `only [Matrix.mul_assoc] at hgu`. Rewrite using `[hs, Matrix.mul_assoc, Matrix.mul_assoc, hgu, hHi]`.
-/
theorem chart_matrix (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hdet : IsUnit H.det)
    (d e : ℕ) (Z : Fin d → Matrix (Fin n) (Fin n) ℂ) (j : Fin e → Fin d)
    (hZ : ∀ a, (Z a)ᴴ * H + H * Z a = 0) (hli : LinearIndependent ℝ (fun i => Z (j i)))
    (hsp : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * H + H * X = 0 →
      X ∈ Submodule.span ℝ (Set.range fun i => Z (j i))) :
    ∃ s : Matrix (Fin n) (Fin n) ℂ → (Fin d → ℝ), ContinuousAt s 1 ∧
      ∀ᶠ g in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), gᴴ * H * g = H →
        g = (List.ofFn fun a => NormedSpace.exp (s g a • Z a)).prod := by
  have hHi : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H hdet
  have hHi' : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H hdet
  have hHih : (H⁻¹)ᴴ = H⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hH]
  let σ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun x => H⁻¹ * xᴴ * H
      map_add' := fun x y => by rw [conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c x => by simp [conjTranspose_smul] }
  have hs : ∀ x, σ x = H⁻¹ * xᴴ * H := fun _ => rfl
  have hσ : ∀ a, σ (σ a) = a := fun a => by
    simp only [hs, conjTranspose_mul, conjTranspose_conjTranspose, hH, hHih, Matrix.mul_assoc]
    rw [hHi, Matrix.mul_one, ← Matrix.mul_assoc, hHi, Matrix.one_mul]
  have hm : ∀ a b, σ (a * b) = σ b * σ a := fun a b => by
    simp only [hs, conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc H, hHi', Matrix.one_mul]
  have h1 : σ 1 = 1 := by simp [hs, hHi]
  have hZσ : ∀ a, σ (Z a) = -Z a := fun a => by
    rw [hs, Matrix.mul_assoc, eq_neg_of_add_eq_zero_left (hZ a), Matrix.mul_neg, ← Matrix.mul_assoc,
      hHi, Matrix.one_mul]
  have hsp' : ∀ X, σ X = -X → X ∈ Submodule.span ℝ (Set.range fun i => Z (j i)) := fun X hX => by
    apply hsp
    have h2 : H * σ X = Xᴴ * H := by
      rw [hs, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hHi', Matrix.one_mul]
    rw [← h2, hX, Matrix.mul_neg, neg_add_cancel]
  obtain ⟨s, hs1, hs2⟩ := chart_general σ hσ hm h1 Z j hZσ hli hsp'
  refine ⟨s, hs1, ?_⟩
  filter_upwards [hs2] with g hg hgu
  apply hg
  simp only [Matrix.mul_assoc] at hgu
  rw [hs, Matrix.mul_assoc, Matrix.mul_assoc, hgu, hHi]

end

/- English proof (translation)
Introduce `n H hH hdet d e Z j _ _ hZ hli hsp`. Take `⟨s, hs1, hs2⟩` from `chart_matrix n H hH hdet d e Z j hZ hli hsp`. Conclude with `⟨_, hs2, s, hs1, fun g hg => hg⟩`.
-/
theorem unitary_chart : ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ), Hᴴ = H → IsUnit H.det →
    ∀ (d e : ℕ) (Z : Fin d → Matrix (Fin n) (Fin n) ℂ) (j : Fin e → Fin d), Function.Injective j →
      (∀ a, a ∉ Set.range j → Z a = 0) → (∀ a, (Z a)ᴴ * H + H * Z a = 0) →
      LinearIndependent ℝ (fun i => Z (j i)) →
      (∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * H + H * X = 0 → X ∈ Submodule.span ℝ (Set.range fun i => Z (j i))) →
      ∃ V ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), ∃ s : Matrix (Fin n) (Fin n) ℂ → (Fin d → ℝ), ContinuousAt s 1 ∧
        ∀ g ∈ V, gᴴ * H * g = H → g = (List.ofFn fun a => NormedSpace.exp (s g a • Z a)).prod := by
  intro n H hH hdet d e Z j _ _ hZ hli hsp
  obtain ⟨s, hs1, hs2⟩ := chart_matrix n H hH hdet d e Z j hZ hli hsp
  exact ⟨_, hs2, s, hs1, fun g hg => hg⟩

end GlobalTheory.UnitaryGroupChart
