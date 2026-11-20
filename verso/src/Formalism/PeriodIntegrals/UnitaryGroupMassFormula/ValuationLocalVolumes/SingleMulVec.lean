import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensFF

noncomputable section

namespace PI.OmVe

open PI.VolStabSW Matrix

section gen

variable {K : Type} [CommRing K] (σ : K →+* K) {M : ℕ} (J : Matrix (Fin M) (Fin M) K)

/- English proof (translation)
Simplify using `[ffH, mul_add, Finset.sum_add_distrib]`.
-/
theorem ffH_add_right (x y z : Fin M → K) : ffH σ J x (y + z) = ffH σ J x y + ffH σ J x z := by
  simp [ffH, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Unfold `ffH`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ffH_smul_right (c : K) (x y : Fin M → K) : ffH σ J x (c • y) = c * ffH σ J x y := by
  unfold ffH
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Simplify using `[ffH]`.
-/
theorem ffH_zero_right (x : Fin M → K) : ffH σ J x 0 = 0 := by
  simp [ffH]

/- English proof (translation)
Simplify using `[ffH]`.
-/
theorem ffH_zero_left (x : Fin M → K) : ffH σ J 0 x = 0 := by
  simp [ffH]

/- English proof (translation)
Use `Finset.induction_on s (by simp [ffH_zero_right]) ?_` and prove the remaining obligations. Introduce `l s hl ih`. Rewrite using `[Finset.sum_insert hl, Finset.sum_insert hl, ffH_add_right, ffH_smul_right, ih]`.
-/
theorem ffH_sum_right {ι : Type} (s : Finset ι) (c : ι → K) (x : Fin M → K) (y : ι → Fin M → K) :
    ffH σ J x (∑ l ∈ s, c l • y l) = ∑ l ∈ s, c l * ffH σ J x (y l) := by
  classical
  refine Finset.induction_on s (by simp [ffH_zero_right]) ?_
  intro l s hl ih
  rw [Finset.sum_insert hl, Finset.sum_insert hl, ffH_add_right, ffH_smul_right, ih]

/- English proof (translation)
Unfold `ffH`. Simplify using `only [map_sum, map_mul, hσ]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hJ]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem ffH_herm (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin M → K) :
    ffH σ J y x = σ (ffH σ J x y) := by
  unfold ffH
  simp only [map_sum, map_mul, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]
  ring

/- English proof (translation)
Use extensionality with `i`. Distinguish the cases in `h : i = i₀`. Substitute `h` using the available equality. Simplify using `[Matrix.mulVec, dotProduct, Matrix.single_apply]`. Simplify using `[Matrix.mulVec, dotProduct, Matrix.single_apply, h, Ne.symm h]`.
-/
theorem single_mulVec' {a : ℕ} (i₀ : Fin a) (v : Fin a → K) :
    (Matrix.single i₀ i₀ (1 : K)) *ᵥ v = Pi.single i₀ (v i₀) := by
  ext i
  by_cases h : i = i₀
  · subst h
    simp [Matrix.mulVec, dotProduct, Matrix.single_apply]
  · simp [Matrix.mulVec, dotProduct, Matrix.single_apply, h, Ne.symm h]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hli c hc0`. Use `Fintype.linearIndependent_iff.1 hli (Pi.single i₀ c) (by simp [Pi.single_apply, hc0])` as an intermediate fact. Simplify using `using this i₀`. Introduce `h`.

Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Establish `hT : T *ᵥ g = 0`. Use function extensionality and compare the values at `j`. Use `congrArg (ffH σ J (X j)) hg` as an intermediate fact.

Rewrite `this` using `[ffH_sum_right σ J Finset.univ g (X j) X, ffH_zero_right]`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.zero_apply]`. Rewrite using `[← hX]`. Simplify `this` using `[ffGram, mul_comm]`. Establish `hTe : T *ᵥ Pi.single i₀ (g i₀) = 0`.

Use function extensionality and compare the values at `j`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply, hc]`. Establish `heq : (T + Matrix.single i₀ i₀ (1 : K)) *ᵥ g = (T + Matrix.single i₀ i₀ (1 : K)) *ᵥ Pi.single i₀ (g i₀)`. Rewrite using `[Matrix.add_mulVec, Matrix.add_mulVec, hT, hTe, single_mulVec', single_mulVec', Pi.single_eq_same]`. Establish `hinv : (T + Matrix.single i₀ i₀ (1 : K))⁻¹ * (T + Matrix.single i₀ i₀ (1 : K)) = 1` using `Matrix.nonsing_inv_mul _ hu`.

Establish `hg' : g = Pi.single i₀ (g i₀)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hinv, Matrix.one_mulVec]`. Use `_ = (T + Matrix.single i₀ i₀ (1 : K))⁻¹ *ᵥ ((T + Matrix.single i₀ i₀ (1 : K)) *ᵥ g) := by`. Rewrite using `[Matrix.mulVec_mulVec]`.

Use `_ = (T + Matrix.single i₀ i₀ (1 : K))⁻¹ *ᵥ ((T + Matrix.single i₀ i₀ (1 : K)) *ᵥ Pi.single i₀ (g i₀)) := by rw [heq]`. Use `_ = Pi.single i₀ (g i₀) := by rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]`. Establish `hsum : ∑ i, g i • X i = g i₀ • X i₀`. Rewrite using `[hg']`. Simplify using `[Pi.single_apply]`.

Establish `h0 : g i₀ = 0` using `h _ (hsum ▸ hg)`. Introduce `i`. Rewrite using `[hg', h0]`. Simplify using the standard rewrite rules.
-/
theorem indep_iff {a : ℕ} {T : Matrix (Fin a) (Fin a) K} (i₀ : Fin a) (hc : ∀ j, T j i₀ = 0)
    (hu : IsUnit (T + Matrix.single i₀ i₀ 1).det) (X : Fin a → Fin M → K) (hX : ffGram σ J X = T) :
    LinearIndependent K X ↔ ∀ c : K, c • X i₀ = 0 → c = 0 := by
  classical
  constructor
  · intro hli c hc0
    have := Fintype.linearIndependent_iff.1 hli (Pi.single i₀ c) (by simp [Pi.single_apply, hc0])
    simpa using this i₀
  · intro h
    rw [Fintype.linearIndependent_iff]
    intro g hg

    have hT : T *ᵥ g = 0 := by
      funext j
      have := congrArg (ffH σ J (X j)) hg
      rw [ffH_sum_right σ J Finset.univ g (X j) X, ffH_zero_right] at this
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [← hX]
      simpa [ffGram, mul_comm] using this
    have hTe : T *ᵥ Pi.single i₀ (g i₀) = 0 := by
      funext j
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, hc]
    have heq : (T + Matrix.single i₀ i₀ (1 : K)) *ᵥ g =
        (T + Matrix.single i₀ i₀ (1 : K)) *ᵥ Pi.single i₀ (g i₀) := by
      rw [Matrix.add_mulVec, Matrix.add_mulVec, hT, hTe, single_mulVec', single_mulVec', Pi.single_eq_same]

    have hinv : (T + Matrix.single i₀ i₀ (1 : K))⁻¹ * (T + Matrix.single i₀ i₀ (1 : K)) = 1 :=
      Matrix.nonsing_inv_mul _ hu
    have hg' : g = Pi.single i₀ (g i₀) := by
      calc g = ((T + Matrix.single i₀ i₀ (1 : K))⁻¹ * (T + Matrix.single i₀ i₀ (1 : K))) *ᵥ g := by
            rw [hinv, Matrix.one_mulVec]
        _ = (T + Matrix.single i₀ i₀ (1 : K))⁻¹ *ᵥ ((T + Matrix.single i₀ i₀ (1 : K)) *ᵥ g) := by
            rw [Matrix.mulVec_mulVec]
        _ = (T + Matrix.single i₀ i₀ (1 : K))⁻¹ *ᵥ ((T + Matrix.single i₀ i₀ (1 : K)) *ᵥ
              Pi.single i₀ (g i₀)) := by rw [heq]
        _ = Pi.single i₀ (g i₀) := by rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    have hsum : ∑ i, g i • X i = g i₀ • X i₀ := by
      rw [hg']
      simp [Pi.single_apply]
    have h0 : g i₀ = 0 := h _ (hsum ▸ hg)
    intro i
    rw [hg', h0]
    simp

/- English proof (translation)
Rewrite using `[Matrix.det_succ_row _ i₀, Finset.sum_eq_single i₀ (fun j _ hj => by simp [hr, Matrix.single_apply, Ne.symm hj]) (by simp)]`. Establish `hsub : (T + Matrix.single i₀ i₀ t).submatrix i₀.succAbove i₀.succAbove = T.submatrix i₀.succAbove i₀.succAbove`. Use extensionality with `a b`. Simplify using `[Matrix.single_apply, (Fin.succAbove_ne i₀ a).symm]`. Rewrite using `[hsub]`.

Simplify using `[hr, Matrix.single_apply, ← two_mul, pow_mul]`.
-/
theorem det_corOne {a : ℕ} (T : Matrix (Fin (a + 1)) (Fin (a + 1)) K) (i₀ : Fin (a + 1))
    (hr : ∀ j, T i₀ j = 0) (t : K) :
    (T + Matrix.single i₀ i₀ t).det = t * (T.submatrix i₀.succAbove i₀.succAbove).det := by

  rw [Matrix.det_succ_row _ i₀, Finset.sum_eq_single i₀
    (fun j _ hj => by simp [hr, Matrix.single_apply, Ne.symm hj]) (by simp)]
  have hsub : (T + Matrix.single i₀ i₀ t).submatrix i₀.succAbove i₀.succAbove =
      T.submatrix i₀.succAbove i₀.succAbove := by
    ext a b
    simp [Matrix.single_apply, (Fin.succAbove_ne i₀ a).symm]
  rw [hsub]
  simp [hr, Matrix.single_apply, ← two_mul, pow_mul]

end gen

end PI.OmVe
