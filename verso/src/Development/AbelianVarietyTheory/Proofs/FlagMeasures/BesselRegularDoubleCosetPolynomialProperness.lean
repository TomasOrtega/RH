import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelRegionNormBoundStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometryOpNormBoundedByTwoFramesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselZhatInvAndRegularIffStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelUnitaryGroupOpNormPropertiesStatement

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.PolyProper

variable {k r : ℕ}

/- English proof (translation)
The claim follows from `Matrix.isUnit_det_of_right_inverse (hermitian_pos_facts_hold k r).2.1`.
-/
theorem gram_det_unit : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_right_inverse (hermitian_pos_facts_hold k r).2.1

/- English proof (translation)
The claim follows from `(unitary_group_holds _ _ gram_det_unit).2.1 g hg h hh`.
-/
theorem mul_mem {g h : Mat k r} (hg : g ∈ GG k r) (hh : h ∈ GG k r) : g * h ∈ GG k r :=
  (unitary_group_holds _ _ gram_det_unit).2.1 g hg h hh

/- English proof (translation)
The claim follows from `((unitary_group_holds _ _ gram_det_unit).2.2 g hg).2`.
-/
theorem inv_mem {g : Mat k r} (hg : g ∈ GG k r) : g⁻¹ ∈ GG k r :=
  ((unitary_group_holds _ _ gram_det_unit).2.2 g hg).2

/- English proof (translation)
The claim follows from `((unitary_group_holds _ _ gram_det_unit).2.2 g hg).1`.
-/
theorem det_unit {g : Mat k r} (hg : g ∈ GG k r) : IsUnit g.det :=
  ((unitary_group_holds _ _ gram_det_unit).2.2 g hg).1

/- English proof (translation)
Take `⟨h, hh, m, hm, rfl⟩` from `hs`. Conclude with `mul_mem hh.1 hm.1`.
-/
theorem mem_of_S {z : Fin (2 * r + k + 1) → ℂ} {s : Mat k r} (hs : s ∈ Sset k r z) : s ∈ GG k r := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  exact mul_mem hh.1 hm.1

/- English proof (translation)
Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Establish `h : gᴴ * Hpk k r * g = Hpk k r` using `hg`. Rewrite using `[Matrix.mul_assoc (Hpk k r), Matrix.mul_assoc (Hpk k r), h]`. Conclude with `(hermitian_pos_facts_hold k r).2.1`.
-/
theorem inv_eq {g : Mat k r} (hg : g ∈ GG k r) : g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  apply Matrix.inv_eq_left_inv
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  rw [Matrix.mul_assoc (Hpk k r), Matrix.mul_assoc (Hpk k r), h]
  exact (hermitian_pos_facts_hold k r).2.1

/- English proof (translation)
Take `⟨C1, h1⟩` from `GlobalTheory.T.siegel_region_norm_bound k r z z' C hz hz' hT hT' hC hCr`. Take `⟨C2, h2⟩` from `GlobalTheory.T.isometry_opNorm_bounded_by_two_frames k r z z' C hz hz' hT hT' hC (fun γ hγ => ⟨(hCr hγ).1, (hCr hγ).2.2⟩)`. Take `⟨hN1, -, -, -, hN5, -⟩` from `GlobalTheory.T.besselModelUnitaryGroup_opNorm_properties k r`. Use `⟨C2 * (max 1 C1) ^ 2, fun γ hγ s hs s' hs' => ?_⟩` and prove the remaining obligations. Establish `hsG` using `mem_of_S hs`.

Establish `hs'G` using `mem_of_S hs'`. Establish `hγG : γ ∈ GG k r` using `(hCr hγ).1`. Establish `hxG : s * γ * s'⁻¹ ∈ GG k r` using `mul_mem (mul_mem hsG hγG) (inv_mem hs'G)`. Establish `hx1 : 1 ≤ opn (s * γ * s'⁻¹)` using `(hN1 _ hxG).2`. Establish `hxs : (s * γ * s'⁻¹) * s' = s * γ`.

Rewrite using `[Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (det_unit hs'G), Matrix.mul_one]`. Establish `h1'` using `h1 γ hγ s hs s' hs'`. Establish `h5` using `hN5 (s * γ * s'⁻¹)`. Use `set X := opn (s * γ * s'⁻¹) with hX`. Establish `hp1 : 1 ≤ X ^ (r * (r + 1))` using `one_le_pow₀ hx1`.

Establish `hm1 : (1 : ℝ) ≤ max 1 C1` using `le_max_left _ _`. Establish `hle : C1 * X ^ (r * (r + 1)) ≤ max 1 C1 * X ^ (r * (r + 1))` using `mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)`. Establish `hQ1 : 1 ≤ max 1 C1 * X ^ (r * (r + 1))` using `one_le_mul_of_one_le_of_one_le hm1 hp1`. Establish `hB : 1 ≤ X * (max 1 C1 * X ^ (r * (r + 1)))` using `one_le_mul_of_one_le_of_one_le hx1 hQ1`. Establish `key` using `h2 γ hγ s hsG (X * (max 1 C1 * X ^ (r * (r + 1)))) hB (by`.

Introduce and unpack `(a | b)`. Use `show eucl (s *ᵥ fvec k r z a) ≤ _`. Use `((h1' a).1.trans hle).trans ?_` and prove the remaining obligations. Conclude with `le_mul_of_one_le_left (by linarith) hx1`. Use `show eucl (s *ᵥ (γ *ᵥ fvec k r z' b)) ≤ _`.

Rewrite using `[Matrix.mulVec_mulVec, ← hxs, ← Matrix.mulVec_mulVec]`. Use `(h5 _).trans ?_` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_left ((h1' b).2.trans hle) (by linarith))`. Use `key.trans (le_of_eq ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem left_bound (z z' : Fin (2 * r + k + 1) → ℂ) (C : Set (Mat k r)) (hz : inWb k r z)
    (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') (hC : IsCompact C)
    (hCr : C ⊆ Greg k r z z') :
    ∃ C0 : ℝ, ∀ γ ∈ C, ∀ s ∈ Sset k r z, ∀ s' ∈ Sset k r z',
      opn s ≤ C0 * opn (s * γ * s'⁻¹) ^ (2 * (r ^ 2 + r + 1)) := by
  obtain ⟨C1, h1⟩ := GlobalTheory.T.siegel_region_norm_bound k r z z' C hz hz' hT hT' hC hCr
  obtain ⟨C2, h2⟩ := GlobalTheory.T.isometry_opNorm_bounded_by_two_frames k r z z' C hz hz' hT hT' hC
    (fun γ hγ => ⟨(hCr hγ).1, (hCr hγ).2.2⟩)
  obtain ⟨hN1, -, -, -, hN5, -⟩ := GlobalTheory.T.besselModelUnitaryGroup_opNorm_properties k r
  refine ⟨C2 * (max 1 C1) ^ 2, fun γ hγ s hs s' hs' => ?_⟩
  have hsG := mem_of_S hs
  have hs'G := mem_of_S hs'
  have hγG : γ ∈ GG k r := (hCr hγ).1
  have hxG : s * γ * s'⁻¹ ∈ GG k r := mul_mem (mul_mem hsG hγG) (inv_mem hs'G)
  have hx1 : 1 ≤ opn (s * γ * s'⁻¹) := (hN1 _ hxG).2
  have hxs : (s * γ * s'⁻¹) * s' = s * γ := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (det_unit hs'G), Matrix.mul_one]
  have h1' := h1 γ hγ s hs s' hs'
  have h5 := hN5 (s * γ * s'⁻¹)
  set X := opn (s * γ * s'⁻¹) with hX
  have hp1 : 1 ≤ X ^ (r * (r + 1)) := one_le_pow₀ hx1
  have hm1 : (1 : ℝ) ≤ max 1 C1 := le_max_left _ _
  have hle : C1 * X ^ (r * (r + 1)) ≤ max 1 C1 * X ^ (r * (r + 1)) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  have hQ1 : 1 ≤ max 1 C1 * X ^ (r * (r + 1)) := one_le_mul_of_one_le_of_one_le hm1 hp1
  have hB : 1 ≤ X * (max 1 C1 * X ^ (r * (r + 1))) := one_le_mul_of_one_le_of_one_le hx1 hQ1
  have key := h2 γ hγ s hsG (X * (max 1 C1 * X ^ (r * (r + 1)))) hB (by
    rintro (a | b)
    · show eucl (s *ᵥ fvec k r z a) ≤ _
      refine ((h1' a).1.trans hle).trans ?_
      exact le_mul_of_one_le_left (by linarith) hx1
    · show eucl (s *ᵥ (γ *ᵥ fvec k r z' b)) ≤ _
      rw [Matrix.mulVec_mulVec, ← hxs, ← Matrix.mulVec_mulVec]
      refine (h5 _).trans ?_
      exact mul_le_mul_of_nonneg_left ((h1' b).2.trans hle) (by linarith))
  refine key.trans (le_of_eq ?_)
  ring

/- English proof (translation)
Introduce `k r z z' C hz hz' hT hT' hC hCr`. Take `⟨C1, h1⟩` from `left_bound z z' C hz hz' hT hT' hC hCr`. Establish `hcont : Continuous fun g : Mat k r => Hpk k r * gᴴ * Hpk k r` using `(continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const`. Establish `hCr' : (fun g : Mat k r => Hpk k r * gᴴ * Hpk k r) '' C ⊆ Greg k r z' z`. Introduce and unpack `_ ⟨γ, hγ, rfl⟩`.

Establish `hγG : γ ∈ GG k r` using `(hCr hγ).1`. Use `show Hpk k r * γᴴ * Hpk k r ∈ _`. Rewrite using `[← inv_eq hγG]`. Conclude with `(GlobalTheory.T.besselZhat_inv_and_regular_iff k r z z' γ hγG).2.1 (hCr hγ)`. Take `⟨C2, h2⟩` from `left_bound z' z _ hz' hz hT' hT (hC.image hcont) hCr'`.

Take `⟨hN1, -⟩` from `GlobalTheory.T.besselModelUnitaryGroup_opNorm_properties k r`. Use `⟨max 1 (max C1 C2), le_max_left _ _, fun γ hγ s hs s' hs' => ?_⟩` and prove the remaining obligations. Establish `hsG` using `mem_of_S hs`. Establish `hs'G` using `mem_of_S hs'`. Establish `hγG : γ ∈ GG k r` using `(hCr hγ).1`.

Establish `hxG : s * γ * s'⁻¹ ∈ GG k r` using `mul_mem (mul_mem hsG hγG) (inv_mem hs'G)`. Establish `hinv : s' * γ⁻¹ * s⁻¹ = (s * γ * s'⁻¹)⁻¹`. Rewrite using `[Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (det_unit hs'G), Matrix.mul_assoc]`. Establish `ha` using `h1 γ hγ s hs s' hs'`. Establish `hb` using `h2 γ⁻¹ ⟨γ, hγ, (inv_eq hγG).symm⟩ s' hs' s hs`.

Rewrite `hb` using `[hinv, (hN1 _ hxG).1]`. Establish `hp : 0 ≤ opn (s * γ * s'⁻¹) ^ (2 * (r ^ 2 + r + 1))` using `pow_nonneg (opn_nonneg _) _`. Use `max_le (ha.trans ?_) (hb.trans ?_)` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hp`. Conclude with `mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) hp`.
-/
theorem poly_proper : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (C : Set (Mat k r)), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsCompact C → C ⊆ Greg k r z z' → ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ γ ∈ C, ∀ s ∈ Sset k r z, ∀ s' ∈ Sset k r z', max (opn s) (opn s') ≤ C0 * opn (s * γ * s'⁻¹) ^ (2 * (r ^ 2 + r + 1)) := by
  intro k r z z' C hz hz' hT hT' hC hCr
  obtain ⟨C1, h1⟩ := left_bound z z' C hz hz' hT hT' hC hCr
  have hcont : Continuous fun g : Mat k r => Hpk k r * gᴴ * Hpk k r :=
    (continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const
  have hCr' : (fun g : Mat k r => Hpk k r * gᴴ * Hpk k r) '' C ⊆ Greg k r z' z := by
    rintro _ ⟨γ, hγ, rfl⟩
    have hγG : γ ∈ GG k r := (hCr hγ).1
    show Hpk k r * γᴴ * Hpk k r ∈ _
    rw [← inv_eq hγG]
    exact (GlobalTheory.T.besselZhat_inv_and_regular_iff k r z z' γ hγG).2.1 (hCr hγ)
  obtain ⟨C2, h2⟩ := left_bound z' z _ hz' hz hT' hT (hC.image hcont) hCr'
  obtain ⟨hN1, -⟩ := GlobalTheory.T.besselModelUnitaryGroup_opNorm_properties k r
  refine ⟨max 1 (max C1 C2), le_max_left _ _, fun γ hγ s hs s' hs' => ?_⟩
  have hsG := mem_of_S hs
  have hs'G := mem_of_S hs'
  have hγG : γ ∈ GG k r := (hCr hγ).1
  have hxG : s * γ * s'⁻¹ ∈ GG k r := mul_mem (mul_mem hsG hγG) (inv_mem hs'G)
  have hinv : s' * γ⁻¹ * s⁻¹ = (s * γ * s'⁻¹)⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (det_unit hs'G),
      Matrix.mul_assoc]
  have ha := h1 γ hγ s hs s' hs'
  have hb := h2 γ⁻¹ ⟨γ, hγ, (inv_eq hγG).symm⟩ s' hs' s hs
  rw [hinv, (hN1 _ hxG).1] at hb
  have hp : 0 ≤ opn (s * γ * s'⁻¹) ^ (2 * (r ^ 2 + r + 1)) := pow_nonneg (opn_nonneg _) _
  refine max_le (ha.trans ?_) (hb.trans ?_)
  · exact mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hp
  · exact mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) hp

end GlobalTheory.SgInf.PolyProper
