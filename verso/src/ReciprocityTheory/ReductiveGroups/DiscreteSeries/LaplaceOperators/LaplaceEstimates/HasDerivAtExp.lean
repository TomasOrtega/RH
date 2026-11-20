import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.StepDownStatement

open Matrix Filter Topology

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open Formalism.QuantumDeterminants

namespace ExponentialSlopeDerivatives

section Linfty
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
  Matrix.linftyOpNormedSpace

/- English proof (translation)
Establish `h` using `(hasDerivAt_exp_smul_const (𝕂 := ℂ) X ((0 : ℝ) : ℂ))`. Establish `h2` using `h.scomp (x := (0:ℝ)) Complex.ofRealCLM.hasDerivAt`. Conclude with `h2.congr_deriv (by simp)`.
-/
theorem hasDerivAt_exp {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) X 0 := by
  have h := (hasDerivAt_exp_smul_const (𝕂 := ℂ) X ((0 : ℝ) : ℂ))
  have h2 := h.scomp (x := (0:ℝ)) Complex.ofRealCLM.hasDerivAt
  exact h2.congr_deriv (by simp)

end Linfty

/- English proof (translation)
Set `_` to `Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)`. Set `_` to `Matrix.linftyOpNormedAlgebra (R := ℂ) (n := Fin n) (α := ℂ)`. Set `_` to `Matrix.linftyOpNormedSpace (R := ℝ) (m := Fin n) (n := Fin n) (α := ℂ)`. Conclude with `(hasDerivAt_exp X).tendsto_slope`.
-/
theorem slope_exp {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Tendsto (slope (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) 0) (𝓝[≠] 0) (𝓝 X) := by
  let _ := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
  let _ := Matrix.linftyOpNormedAlgebra (R := ℂ) (n := Fin n) (α := ℂ)
  let _ := Matrix.linftyOpNormedSpace (R := ℝ) (m := Fin n) (n := Fin n) (α := ℂ)
  exact (hasDerivAt_exp X).tendsto_slope

/- English proof (translation)
Establish `hc : Continuous Lf` using `LinearMap.continuous_of_finiteDimensional Lf`. Establish `hT` using `(hc.tendsto Y).comp (slope_exp Y)`. Establish `hD : HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (Lf Y) 0`. Rewrite using `[hasDerivAt_iff_tendsto_slope]`. Use `hT.congr (fun t => ?_)` and prove the remaining obligations.

Simplify using `only [Function.comp_apply, slope_def_module, hf]`. Rewrite using `[LinearMap.map_smul_of_tower, map_sub]`. Conclude with `hD.deriv`.
-/
theorem rdv_of_linear {n : ℕ} (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (g X Y : Matrix (Fin n) (Fin n) ℂ)
    (Lf : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ)
    (hf : ∀ t : ℝ, f (g * NormedSpace.exp ((t : ℂ) • X)) = Lf (NormedSpace.exp ((t : ℂ) • Y))) :
    S7.RdV X f g = Lf Y := by
  have hc : Continuous Lf := LinearMap.continuous_of_finiteDimensional Lf
  have hT := (hc.tendsto Y).comp (slope_exp Y)
  have hD : HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (Lf Y) 0 := by
    rw [hasDerivAt_iff_tendsto_slope]
    refine hT.congr (fun t => ?_)
    simp only [Function.comp_apply, slope_def_module, hf]
    rw [LinearMap.map_smul_of_tower, map_sub]
  exact hD.deriv

end ExponentialSlopeDerivatives

end ReciprocityTheory.ChartRestriction.DS.Lap

namespace ReciprocityTheory.ChartRestriction.DS.Lap
namespace ExponentialSlopeDerivatives
open Formalism.QuantumDeterminants

def sg (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if r ≤ i.val ∧ i.val ≤ r + k then i else ⟨2 * r + k - i.val, by omega⟩

/- English proof (translation)
Apply the tactic sequence `unfold sg; split_ifs <;> rfl`.
-/
theorem sg_val (k r : ℕ) (i : Fin (2 * r + k + 1)) :
    (sg k r i).val = if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val := by
  unfold sg; split_ifs <;> rfl

/- English proof (translation)
Apply the tactic sequence `apply Fin.ext; rw [sg_val, sg_val]; split_ifs <;> omega`.
-/
theorem sg_sg (k r : ℕ) (i : Fin (2 * r + k + 1)) : sg k r (sg k r i) = i := by
  apply Fin.ext; rw [sg_val, sg_val]; split_ifs <;> omega

/- English proof (translation)
Apply the tactic sequence `rw [sg_val]; split_ifs <;> omega`.
-/
theorem sg_mid (k r : ℕ) (i : Fin (2 * r + k + 1)) : (sg k r i).val = r + k ↔ i.val = r + k := by
  rw [sg_val]; split_ifs <;> omega

/- English proof (translation)
Establish `key : j = sg k r i ↔ j.val = (if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val)`. Rewrite using `[← sg_val, Fin.ext_iff]`. Unfold `Hpk`. Simplify using `only [key, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
theorem hpk_apply (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = sg k r i then (if i.val = r + k then -1 else 1) else 0 := by
  have key : j = sg k r i ↔ j.val = (if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val) := by
    rw [← sg_val, Fin.ext_iff]
  unfold Hpk
  simp only [key, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply]`. Simplify using `only [hpk_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, sg_sg, sg_mid]`. Distinguish the cases in `hij : i = j`. Apply the tactic sequence `subst hij; split_ifs <;> simp_all`.

Establish `: ¬ j = i` using `fun h => hij h.symm`. Simplify using `[hij, this]`.
-/
theorem hpk_mul_self (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [hpk_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, sg_sg, sg_mid]
  by_cases hij : i = j
  · subst hij; split_ifs <;> simp_all
  · have : ¬ j = i := fun h => hij h.symm
    simp [hij, this]

/- English proof (translation)
Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg, hH]`.
-/
theorem inv_of_UH {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hH : H * H = 1) (hg : gᴴ * H * g = H) :
    g⁻¹ = H * gᴴ * H := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg, hH]

/- English proof (translation)
Rewrite using `[inv_of_UH hH hg, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg, hH]`.
-/
theorem inv_mul_of_UH {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hH : H * H = 1) (hg : gᴴ * H * g = H) :
    g⁻¹ * g = 1 := by
  rw [inv_of_UH hH hg, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg, hH]

/- English proof (translation)
Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hs]`.
-/
theorem herm_UH {n : ℕ} {H s : Matrix (Fin n) (Fin n) ℂ} (hs : sᴴ * H * s = H) (a b : Fin n → ℂ) :
    star (s *ᵥ a) ⬝ᵥ (H *ᵥ (s *ᵥ b)) = star a ⬝ᵥ (H *ᵥ b) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hs]

end ExponentialSlopeDerivatives
end ReciprocityTheory.ChartRestriction.DS.Lap

namespace ReciprocityTheory.ChartRestriction.DS.Lap
namespace ExponentialSlopeDerivatives
open Formalism.QuantumDeterminants

/- English proof (translation)
Introduce and unpack `s ⟨h, ⟨hU, hfix, hz⟩, m, ⟨mU, mcol, mmid⟩, rfl⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show (h * m)ᴴ * Hpk k r * (h * m) = Hpk k r`. Establish `hU' : hᴴ * Hpk k r * h = Hpk k r` using `hU`. Establish `mU' : mᴴ * Hpk k r * m = Hpk k r` using `mU`.

Rewrite using `[Matrix.conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Hpk k r := by rw [hU', mU']`. Rewrite using `[← Matrix.mulVec_mulVec]`.

Unfold `xOne`. Use `split_ifs with hr`. Establish `hm : m = 1`. Use extensionality with `i j`. Rewrite using `[mmid i j (by omega) (by omega) (by omega), Matrix.one_apply]`.

Rewrite using `[hm, Matrix.one_mulVec, hz]`. Establish `hm : m *ᵥ Pi.single (⟨0, by omega⟩ : Fin (2 * r + k + 1)) (1 : ℂ) = Pi.single (⟨0, by omega⟩ : Fin (2 * r + k + 1)) (1 : ℂ)`. Use function extensionality and compare the values at `i`. Rewrite using `[Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply]`. Conclude with `mcol ⟨0, by omega⟩ i (Nat.zero_le _)`.

Rewrite using `[hm]`. Conclude with `(hfix ⟨0, by omega⟩).1`.
-/
theorem s_fix (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) :
    ∀ s ∈ Sset k r z, s ∈ UH (Hpk k r) ∧ s *ᵥ xOne k r z = xOne k r z := by
  rintro s ⟨h, ⟨hU, hfix, hz⟩, m, ⟨mU, mcol, mmid⟩, rfl⟩
  refine ⟨?_, ?_⟩
  · show (h * m)ᴴ * Hpk k r * (h * m) = Hpk k r
    have hU' : hᴴ * Hpk k r * h = Hpk k r := hU
    have mU' : mᴴ * Hpk k r * m = Hpk k r := mU
    rw [Matrix.conjTranspose_mul]
    calc mᴴ * hᴴ * Hpk k r * (h * m) = mᴴ * (hᴴ * Hpk k r * h) * m := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [hU', mU']
  · rw [← Matrix.mulVec_mulVec]
    unfold xOne
    split_ifs with hr
    · have hm : m = 1 := by
        ext i j
        rw [mmid i j (by omega) (by omega) (by omega), Matrix.one_apply]
      rw [hm, Matrix.one_mulVec, hz]
    · have hm : m *ᵥ Pi.single (⟨0, by omega⟩ : Fin (2 * r + k + 1)) (1 : ℂ) =
          Pi.single (⟨0, by omega⟩ : Fin (2 * r + k + 1)) (1 : ℂ) := by
        funext i
        rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply]
        exact mcol ⟨0, by omega⟩ i (Nat.zero_le _)
      rw [hm]
      exact (hfix ⟨0, by omega⟩).1

/- English proof (translation)
Establish `h1 : a ⬝ᵥ (M *ᵥ b) = ∑ i, ∑ j, a i * M i j * b j`. Simplify using `[dotProduct, mulVec, Finset.mul_sum, mul_assoc]`. Rewrite using `[h1, Finset.mul_sum]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`.

Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, norm_mul]`. Establish `ha : ‖a i‖ ≤ ∑ i, ‖a i‖` using `Finset.single_le_sum (f := fun i => ‖a i‖) (fun i _ => norm_nonneg (a i)) (Finset.mem_univ i)`. Establish `hb : ‖b j‖ ≤ ∑ j, ‖b j‖` using `Finset.single_le_sum (f := fun j => ‖b j‖) (fun j _ => norm_nonneg (b j)) (Finset.mem_univ j)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem dot_bound {n : ℕ} (a b : Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
    ‖a ⬝ᵥ (M *ᵥ b)‖ ≤ ((∑ i, ‖a i‖) * (∑ j, ‖b j‖)) * ∑ i, ∑ j, ‖M i j‖ := by
  have h1 : a ⬝ᵥ (M *ᵥ b) = ∑ i, ∑ j, a i * M i j * b j := by
    simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  rw [h1, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, norm_mul]
  have ha : ‖a i‖ ≤ ∑ i, ‖a i‖ :=
    Finset.single_le_sum (f := fun i => ‖a i‖) (fun i _ => norm_nonneg (a i)) (Finset.mem_univ i)
  have hb : ‖b j‖ ≤ ∑ j, ‖b j‖ :=
    Finset.single_le_sum (f := fun j => ‖b j‖) (fun j _ => norm_nonneg (b j)) (Finset.mem_univ j)
  calc ‖a i‖ * ‖M i j‖ * ‖b j‖ ≤ (∑ i, ‖a i‖) * ‖M i j‖ * (∑ j, ‖b j‖) := by gcongr
    _ = _ := by ring

end ExponentialSlopeDerivatives

open ExponentialSlopeDerivatives Formalism.QuantumDeterminants

/- English proof (translation)
Introduce `k r z _`. Establish `hH` using `hpk_mul_self k r`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `y β s hs g hg`. Take `⟨hsU, hsx⟩` from `s_fix k r z s hs`.

Establish `hsU' : sᴴ * Hpk k r * s = Hpk k r` using `hsU`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show star (xOne k r z) ⬝ᵥ (Hpk k r *ᵥ ((s * g) *ᵥ y)) = star (xOne k r z) ⬝ᵥ (Hpk k r *ᵥ (g *ᵥ y))`. Rewrite using `[← Matrix.mulVec_mulVec]`. Use `herm_UH hsU' (xOne k r z) (g *ᵥ y)` as an intermediate fact.

Rewrite `this` using `[hsx]`. Then use the resulting hypothesis. Use `show β ⬝ᵥ ((s * g)⁻¹ *ᵥ xOne k r z) = β ⬝ᵥ (g⁻¹ *ᵥ xOne k r z)`. Establish `hinv : s⁻¹ *ᵥ xOne k r z = xOne k r z` using `by conv_lhs => rw [← hsx]`. Rewrite using `[Matrix.mulVec_mulVec, inv_mul_of_UH hH hsU', Matrix.one_mulVec]`. Rewrite using `[Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, hinv]`.

Introduce `y β X g _`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Set `Lf : Mat k r →ₗ[ℂ] ℂ` to `{ toFun := fun M => star (xOne k r z) ⬝ᵥ (Hpk k r *ᵥ ((g * M) *ᵥ y)) map_add' := by`. Introduce `A B`. Simplify using `[Matrix.mul_add, Matrix.add_mulVec, Matrix.mulVec_add, dotProduct_add]`.

Use the proof step `map_smul' := by`. Introduce `c A`. Simplify using `[Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul] }`. Rewrite using `[rdv_of_linear (cMul k r z y) g X X Lf (fun t => rfl)]`. Use `show star (xOne k r z) ⬝ᵥ (Hpk k r *ᵥ ((g * X) *ᵥ y)) = star (xOne k r z) ⬝ᵥ (Hpk k r *ᵥ (g *ᵥ (X *ᵥ y)))`.

Rewrite using `[Matrix.mulVec_mulVec y g X]`. Set `Lf : Mat k r →ₗ[ℂ] ℂ` to `{ toFun := fun M => β ⬝ᵥ (M *ᵥ (g⁻¹ *ᵥ xOne k r z)) map_add' := by`. Introduce `A B`. Simplify using `only [Matrix.add_mulVec, dotProduct_add]`. Use the proof step `map_smul' := by`.

Introduce `c A`. Simplify using `[Matrix.smul_mulVec, dotProduct_smul] }`. Establish `hf : ∀ t : ℝ, cMulD k r z β (g * NormedSpace.exp ((t : ℂ) • X)) = Lf (NormedSpace.exp ((t : ℂ) • -X))`. Introduce `t`. Use `show β ⬝ᵥ ((g * NormedSpace.exp ((t : ℂ) • X))⁻¹ *ᵥ xOne k r z) = β ⬝ᵥ (NormedSpace.exp ((t : ℂ) • -X) *ᵥ (g⁻¹ *ᵥ xOne k r z))`.

Rewrite using `[Matrix.mul_inv_rev, smul_neg, Matrix.exp_neg, ← Matrix.mulVec_mulVec]`. Rewrite using `[rdv_of_linear (cMulD k r z β) g X (-X) Lf hf]`. Use `show β ⬝ᵥ ((-X) *ᵥ (g⁻¹ *ᵥ xOne k r z)) = -((β ᵥ* X) ⬝ᵥ (g⁻¹ *ᵥ xOne k r z))`. Rewrite using `[Matrix.neg_mulVec, dotProduct_neg, Matrix.dotProduct_mulVec]`. Introduce `y β set x1 := xOne k r z set C1 : ℝ := (∑ i, ‖(star x1 ᵥ* Hpk k r) i‖) * (∑ j, ‖y j‖) set C2 : ℝ := (∑ i, ‖(β ᵥ* Hpk k r) i‖) * (∑ j, ‖(Hpk k r *ᵥ x1) j‖)`.

Use `⟨max C1 C2, fun g hg => ?_⟩` and prove the remaining obligations. Establish `hg' : gᴴ * Hpk k r * g = Hpk k r` using `hg`. Establish `hS : 0 ≤ ∑ i, ∑ j, ‖g i j‖` using `Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `e : cMul k r z y g = (star x1 ᵥ* Hpk k r) ⬝ᵥ (g *ᵥ y)` using `by show star x1 ⬝ᵥ (Hpk k r *ᵥ (g *ᵥ y)) = _`.

Rewrite using `[Matrix.dotProduct_mulVec]`. Rewrite using `[e]`. Conclude with `(dot_bound _ _ _).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hS)`. Establish `e : cMulD k r z β g = (β ᵥ* Hpk k r) ⬝ᵥ (gᴴ *ᵥ (Hpk k r *ᵥ x1))` using `by show β ⬝ᵥ (g⁻¹ *ᵥ x1) = _`. Rewrite using `[inv_of_UH hH hg', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]`.

Establish `hT : ∑ i, ∑ j, ‖gᴴ i j‖ = ∑ i, ∑ j, ‖g i j‖`. Simplify using `only [Matrix.conjTranspose_apply, norm_star]`. Conclude with `Finset.sum_comm`. Rewrite using `[e]`. Use `(dot_bound _ _ _).trans ?_` and prove the remaining obligations.

Rewrite using `[hT]`. Conclude with `mul_le_mul_of_nonneg_right (le_max_right _ _) hS`.
-/
theorem mult : MultStatement := by
  intro k r z _
  have hH := hpk_mul_self k r
  refine ⟨?_, ?_, ?_⟩
  · intro y β s hs g hg
    obtain ⟨hsU, hsx⟩ := s_fix k r z s hs
    have hsU' : sᴴ * Hpk k r * s = Hpk k r := hsU
    refine ⟨?_, ?_⟩
    · show star (xOne k r z) ⬝ᵥ (Hpk k r *ᵥ ((s * g) *ᵥ y)) =
        star (xOne k r z) ⬝ᵥ (Hpk k r *ᵥ (g *ᵥ y))
      rw [← Matrix.mulVec_mulVec]
      have := herm_UH hsU' (xOne k r z) (g *ᵥ y)
      rwa [hsx] at this
    · show β ⬝ᵥ ((s * g)⁻¹ *ᵥ xOne k r z) = β ⬝ᵥ (g⁻¹ *ᵥ xOne k r z)
      have hinv : s⁻¹ *ᵥ xOne k r z = xOne k r z := by
        conv_lhs => rw [← hsx]
        rw [Matrix.mulVec_mulVec, inv_mul_of_UH hH hsU', Matrix.one_mulVec]
      rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, hinv]
  · intro y β X g _
    refine ⟨?_, ?_⟩
    · let Lf : Mat k r →ₗ[ℂ] ℂ :=
        { toFun := fun M => star (xOne k r z) ⬝ᵥ (Hpk k r *ᵥ ((g * M) *ᵥ y))
          map_add' := by
            intro A B
            simp [Matrix.mul_add, Matrix.add_mulVec, Matrix.mulVec_add, dotProduct_add]
          map_smul' := by
            intro c A
            simp [Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul] }
      rw [rdv_of_linear (cMul k r z y) g X X Lf (fun t => rfl)]
      show star (xOne k r z) ⬝ᵥ (Hpk k r *ᵥ ((g * X) *ᵥ y)) =
        star (xOne k r z) ⬝ᵥ (Hpk k r *ᵥ (g *ᵥ (X *ᵥ y)))
      rw [Matrix.mulVec_mulVec y g X]
    · let Lf : Mat k r →ₗ[ℂ] ℂ :=
        { toFun := fun M => β ⬝ᵥ (M *ᵥ (g⁻¹ *ᵥ xOne k r z))
          map_add' := by
            intro A B
            simp only [Matrix.add_mulVec, dotProduct_add]
          map_smul' := by
            intro c A
            simp [Matrix.smul_mulVec, dotProduct_smul] }
      have hf : ∀ t : ℝ, cMulD k r z β (g * NormedSpace.exp ((t : ℂ) • X)) =
          Lf (NormedSpace.exp ((t : ℂ) • -X)) := by
        intro t
        show β ⬝ᵥ ((g * NormedSpace.exp ((t : ℂ) • X))⁻¹ *ᵥ xOne k r z) =
          β ⬝ᵥ (NormedSpace.exp ((t : ℂ) • -X) *ᵥ (g⁻¹ *ᵥ xOne k r z))
        rw [Matrix.mul_inv_rev, smul_neg, Matrix.exp_neg, ← Matrix.mulVec_mulVec]
      rw [rdv_of_linear (cMulD k r z β) g X (-X) Lf hf]
      show β ⬝ᵥ ((-X) *ᵥ (g⁻¹ *ᵥ xOne k r z)) = -((β ᵥ* X) ⬝ᵥ (g⁻¹ *ᵥ xOne k r z))
      rw [Matrix.neg_mulVec, dotProduct_neg, Matrix.dotProduct_mulVec]
  · intro y β
    set x1 := xOne k r z
    set C1 : ℝ := (∑ i, ‖(star x1 ᵥ* Hpk k r) i‖) * (∑ j, ‖y j‖)
    set C2 : ℝ := (∑ i, ‖(β ᵥ* Hpk k r) i‖) * (∑ j, ‖(Hpk k r *ᵥ x1) j‖)
    refine ⟨max C1 C2, fun g hg => ?_⟩
    have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
    have hS : 0 ≤ ∑ i, ∑ j, ‖g i j‖ :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
    refine ⟨?_, ?_⟩
    · have e : cMul k r z y g = (star x1 ᵥ* Hpk k r) ⬝ᵥ (g *ᵥ y) := by
        show star x1 ⬝ᵥ (Hpk k r *ᵥ (g *ᵥ y)) = _
        rw [Matrix.dotProduct_mulVec]
      rw [e]
      exact (dot_bound _ _ _).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hS)
    · have e : cMulD k r z β g = (β ᵥ* Hpk k r) ⬝ᵥ (gᴴ *ᵥ (Hpk k r *ᵥ x1)) := by
        show β ⬝ᵥ (g⁻¹ *ᵥ x1) = _
        rw [inv_of_UH hH hg', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
          Matrix.dotProduct_mulVec]
      have hT : ∑ i, ∑ j, ‖gᴴ i j‖ = ∑ i, ∑ j, ‖g i j‖ := by
        simp only [Matrix.conjTranspose_apply, norm_star]
        exact Finset.sum_comm
      rw [e]
      refine (dot_bound _ _ _).trans ?_
      rw [hT]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) hS

end ReciprocityTheory.ChartRestriction.DS.Lap
