import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspIntegralBasisCovolumeConstantStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsReducedBasisBoundedTypeOfInstanceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralVectorBasesBoundedFiniteUnitaryClassesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactIntegralUnitaryFinitePartStatement
open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

namespace GlobalTheory.HtMinPf

/- English proof (translation)
Establish `hg : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε` using `g.2`. Establish `h1 : uMat g * uMat g⁻¹ = 1` using `by show ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * (((g⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1`. Rewrite using `[Subgroup.coe_inv, Units.mul_inv]`. Establish `hJ` using `Formalism.REAL.Jm_mul_self ε`. Establish `hmi : uMat g⁻¹ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hg, hJ, Matrix.one_mul]`. Use `_ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε * (uMat g * uMat g⁻¹) := by`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by rw [h1, Matrix.mul_one]`.

Rewrite using `[hmi]`. Unfold `Formalism.REAL.Jm`. Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]`. Apply the tactic sequence `by_cases ha : ε j <;> by_cases hb : ε i <;> simp [ha, hb]`.
-/
lemma uj_entry {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) (i j : Fin n) :
    ‖uMat g i j‖ = ‖uMat g⁻¹ j i‖ := by
  have hg : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
  have h1 : uMat g * uMat g⁻¹ = 1 := by
    show ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * (((g⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1
    rw [Subgroup.coe_inv, Units.mul_inv]
  have hJ := Formalism.REAL.Jm_mul_self ε
  have hmi : uMat g⁻¹ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε := by
    calc uMat g⁻¹ = Formalism.REAL.Jm ε * ((uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g) * uMat g⁻¹ := by
            rw [hg, hJ, Matrix.one_mul]
      _ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε * (uMat g * uMat g⁻¹) := by
            simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one]
  rw [hmi]
  unfold Formalism.REAL.Jm
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]
  by_cases ha : ε j <;> by_cases hb : ε i <;> simp [ha, hb]

variable (I : AutInst)

/- English proof (translation)
Use function extensionality and compare the values at `v`. Establish `h : (fun k => I.φ v (∑ i, z i • e i k)) = ∑ i, ((z i : ℝ)) • fun k => I.φ v (e i k)`. Use function extensionality and compare the values at `k`. Simplify using `[Finset.sum_apply, map_sum, Complex.real_smul]`. Simplify using `only [CuspGeo.vec, Finset.sum_apply, Pi.smul_apply]`.

Rewrite using `[h, Matrix.mulVec_sum, Matrix.mulVec_sum]`. Simplify using `[Matrix.mulVec_smul]`.
-/
lemma vec_sum (y : I.Ginf) {N : ℕ} (z : Fin N → ℤ) (e : Fin N → Fin I.n → I.E) :
    vec I y (∑ i, z i • e i) = ∑ i, ((z i : ℝ)) • vec I y (e i) := by
  funext v
  have h : (fun k => I.φ v (∑ i, z i • e i k)) = ∑ i, ((z i : ℝ)) • fun k => I.φ v (e i k) := by
    funext k
    simp [Finset.sum_apply, map_sum, Complex.real_smul]
  simp only [CuspGeo.vec, Finset.sum_apply, Pi.smul_apply]
  rw [h, Matrix.mulVec_sum, Matrix.mulVec_sum]
  simp [Matrix.mulVec_smul]

/- English proof (translation)
Establish `h1 : uMat ((1 : I.Ginf) v)⁻¹ = 1` using `by simp [uMat]`. Simplify using `only [CuspGeo.vec]`. Rewrite using `[h1, Matrix.one_mulVec]`.
-/
lemma vec_one (y : I.Ginf) (u : Fin I.n → I.E) (v : InfinitePlace I.F) :
    vec I y u v = uMat (y v)⁻¹ *ᵥ vec I 1 u v := by
  have h1 : uMat ((1 : I.Ginf) v)⁻¹ = 1 := by simp [uMat]
  simp only [CuspGeo.vec]
  rw [h1, Matrix.one_mulVec]

/- English proof (translation)
Use function extensionality and compare the values at `v`. Establish `hP : I.P v * (I.P v)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v))`. Establish `hinv : uMat (x₁ v)⁻¹ * uMat (x₁ v) = 1` using `by show (((x₁ v)⁻¹ : Formalism.REAL.UJ (I.ε v)) : (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ).val * ((x₁ v : Formalism.REAL.UJ (I.ε v)) : (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ).val = 1`. Rewrite using `[Subgroup.coe_inv, Units.inv_mul]`. Establish `hφ : (fun i => I.φ v (((γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ u) i)) = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) *ᵥ fun i => I.φ v (u i)`.

Use function extensionality and compare the values at `i`. Conclude with `RingHom.map_mulVec _ _ _ _`. Establish `hmul : uMat ((x₁ * y) v)⁻¹ = uMat (y v)⁻¹ * uMat (x₁ v)⁻¹`. Simplify using `[uMat, Pi.mul_apply, _root_.mul_inv_rev]`. Simplify using `only [CuspGeo.vec]`.

Rewrite using `[hmul, hφ, ← Matrix.mulVec_mulVec]`. Use `congr 1`. Establish `: (I.P v)⁻¹ *ᵥ ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) *ᵥ fun i => I.φ v (u i)) = uMat (x₁ v) *ᵥ ((I.P v)⁻¹ *ᵥ fun i => I.φ v (u i))`. Rewrite using `[hx v, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc _ (I.P v), hP, Matrix.mul_one]`. Rewrite using `[this, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]`.
-/
lemma vec_trans (x₁ y : I.Ginf) (γ : GL (Fin I.n) I.E)
    (hx : ∀ v, uMat (x₁ v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v)
    (u : Fin I.n → I.E) : vec I (x₁ * y) ((γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ u) = vec I y u := by
  funext v
  have hP : I.P v * (I.P v)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v))
  have hinv : uMat (x₁ v)⁻¹ * uMat (x₁ v) = 1 := by
    show (((x₁ v)⁻¹ : Formalism.REAL.UJ (I.ε v)) : (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ).val * ((x₁ v : Formalism.REAL.UJ (I.ε v)) : (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ).val = 1
    rw [Subgroup.coe_inv, Units.inv_mul]
  have hφ : (fun i => I.φ v (((γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ u) i)) =
      (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) *ᵥ fun i => I.φ v (u i) := by
    funext i
    exact RingHom.map_mulVec _ _ _ _
  have hmul : uMat ((x₁ * y) v)⁻¹ = uMat (y v)⁻¹ * uMat (x₁ v)⁻¹ := by
    simp [uMat, Pi.mul_apply, _root_.mul_inv_rev]
  simp only [CuspGeo.vec]
  rw [hmul, hφ, ← Matrix.mulVec_mulVec]
  congr 1
  have : (I.P v)⁻¹ *ᵥ ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) *ᵥ fun i => I.φ v (u i)) =
      uMat (x₁ v) *ᵥ ((I.P v)⁻¹ *ᵥ fun i => I.φ v (u i)) := by
    rw [hx v, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc _ (I.P v), hP, Matrix.mul_one]
  rw [this, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]

/- English proof (translation)
Take `⟨N', e', ρ, d, hd, he', -, hdet⟩` from `GlobalTheory.T.cusp_integralBasis_covolume_constant I`. Use `set G := gm I ρ 1 e' with hGdef`. Establish `hG : G.det ≠ 0`. Introduce `h`. Use `hdet 1` as an intermediate fact.

Rewrite `this` using `[← hGdef, h]`. Simplify using `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set a := G⁻¹ *ᵥ ρ w with ha`. Establish `hGa : G *ᵥ a = ρ w`.

Rewrite using `[ha, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hG), Matrix.one_mulVec]`. Establish `hw : w = ∑ j, a j • vec I 1 (e' j)`. Apply `ρ.injective` to reduce the goal to its premises. Rewrite using `[← hGa, map_sum]`. Use function extensionality and compare the values at `i`.

Simplify using `[hGdef, gm, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]`. Establish `hz : ∀ j, ∃ z : Fin N → ℤ, e' j = ∑ i, z i • e₀ i` using `fun j => (he₀.2 (e' j)).mp ((he'.2 (e' j)).mpr ⟨Pi.single j 1, by simp [Pi.single_apply]⟩)`. Use `choose z hz using hz`. Use `⟨fun i => ∑ j, a j * (z j i : ℝ), ?_⟩` and prove the remaining obligations. Rewrite using `[hw]`.

Repeatedly rewrite using `[hz, vec_sum, Finset.smul_sum, smul_smul, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`.
-/
lemma span_of_zbasis {N : ℕ} (e₀ : Fin N → Fin I.n → I.E) (he₀ : IsZBasis I e₀)
    (w : InfinitePlace I.F → Fin I.n → ℂ) : ∃ c : Fin N → ℝ, w = ∑ l, c l • vec I 1 (e₀ l) := by
  obtain ⟨N', e', ρ, d, hd, he', -, hdet⟩ := GlobalTheory.T.cusp_integralBasis_covolume_constant I
  set G := gm I ρ 1 e' with hGdef
  have hG : G.det ≠ 0 := by
    intro h
    have := hdet 1
    rw [← hGdef, h] at this
    simp at this
    linarith
  set a := G⁻¹ *ᵥ ρ w with ha
  have hGa : G *ᵥ a = ρ w := by
    rw [ha, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hG), Matrix.one_mulVec]
  have hw : w = ∑ j, a j • vec I 1 (e' j) := by
    apply ρ.injective
    rw [← hGa, map_sum]
    funext i
    simp [hGdef, gm, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hz : ∀ j, ∃ z : Fin N → ℤ, e' j = ∑ i, z i • e₀ i := fun j =>
    (he₀.2 (e' j)).mp ((he'.2 (e' j)).mpr ⟨Pi.single j 1, by simp [Pi.single_apply]⟩)
  choose z hz using hz
  refine ⟨fun i => ∑ j, a j * (z j i : ℝ), ?_⟩
  rw [hw]
  simp_rw [hz, vec_sum, Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]

open Classical in
/- English proof (translation)
Establish `h : uMat (z v)⁻¹ j i = (∑ l, c l • vec I z (e₀ l)) v j`. Combine the equalities or inequalities in the displayed calculation. Simplify using `[Matrix.mulVec_single_one]`. Use `_ = (uMat (z v)⁻¹ *ᵥ (∑ l, c l • vec I 1 (e₀ l)) v) j := by rw [hc]`. Use `_ = (∑ l, c l • vec I z (e₀ l)) v j := by`.

Simplify using `only [Finset.sum_apply, Pi.smul_apply, Matrix.mulVec_sum, Matrix.mulVec_smul, vec_one I z]`. Rewrite using `[h, Finset.sum_apply, Finset.sum_apply]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, Pi.smul_apply, norm_smul, Real.norm_eq_abs]`. Conclude with `mul_le_mul_of_nonneg_left ((norm_le_pi_norm (vec I z (e₀ l) v) j).trans (norm_le_pi_norm (vec I z (e₀ l)) v)) (abs_nonneg _)`.
-/
lemma entry_bound (z : I.Ginf) {N : ℕ} (e₀ : Fin N → Fin I.n → I.E) (c : Fin N → ℝ)
    (v : InfinitePlace I.F) (i : Fin I.n)
    (hc : (Pi.single v (Pi.single i (1 : ℂ)) : InfinitePlace I.F → Fin I.n → ℂ) = ∑ l, c l • vec I 1 (e₀ l))
    (j : Fin I.n) : ‖uMat (z v)⁻¹ j i‖ ≤ ∑ l, |c l| * ‖vec I z (e₀ l)‖ := by
  have h : uMat (z v)⁻¹ j i = (∑ l, c l • vec I z (e₀ l)) v j := by
    calc uMat (z v)⁻¹ j i
        = (uMat (z v)⁻¹ *ᵥ (Pi.single v (Pi.single i (1 : ℂ)) : InfinitePlace I.F → Fin I.n → ℂ) v) j := by
          simp [Matrix.mulVec_single_one]
      _ = (uMat (z v)⁻¹ *ᵥ (∑ l, c l • vec I 1 (e₀ l)) v) j := by rw [hc]
      _ = (∑ l, c l • vec I z (e₀ l)) v j := by
          simp only [Finset.sum_apply, Pi.smul_apply, Matrix.mulVec_sum, Matrix.mulVec_smul, vec_one I z]
  rw [h, Finset.sum_apply, Finset.sum_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [Pi.smul_apply, Pi.smul_apply, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left ((norm_le_pi_norm (vec I z (e₀ l) v) j).trans
    (norm_le_pi_norm (vec I z (e₀ l)) v)) (abs_nonneg _)

end GlobalTheory.HtMinPf

open GlobalTheory.HtMinPf in

/- English proof (translation)
Introduce `I`. Take `⟨N, R, C, hred⟩` from `GlobalTheory.T.existsReducedBasisBoundedType_of_instance I`. Take `⟨S, hSfin, hS0, hS⟩` from `GlobalTheory.T.integralVectorBases_bounded_finite_unitaryClasses I N R`. Take `⟨K, hK, hK'⟩` from `GlobalTheory.T.exists_compact_integral_unitary_finitePart I`. Establish `hbd : ∀ e₀ : Fin N → Fin I.n → I.E, ∃ M : ℝ, e₀ ∈ S → ∀ v i, ∃ c : Fin N → ℝ, (Pi.single v (Pi.single i (1 : ℂ)) : InfinitePlace I.F → Fin I.n → ℂ) = ∑ l, c l • vec I 1 (e₀ l) ∧ ∑ l, |c l| ≤ M`.

Introduce `e₀`. Distinguish the cases in `h : e₀ ∈ S`. Use `fun v i => span_of_zbasis I e₀ (hS0 e₀ h) (Pi.single v (Pi.single i (1 : ℂ))) choose c hc using this` as an intermediate fact. Use `⟨∑ v, ∑ i, ∑ l, |c v i l|, fun _ v i => ⟨c v i, hc v i, ?_⟩⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Conclude with `⟨0, fun h' => absurd h' h⟩`. Use `choose M hM using hbd`. Take `⟨Mt, hMt⟩` from `(hSfin.image M).bddAbove`. Use `⟨N, Mt * max C 0, K, hK, ?_⟩` and prove the remaining obligations. Introduce `y t ht0 ht1 hns`.

Take `⟨e, heZ, heB, hesz⟩` from `hred y`. Take `⟨e₀, he₀S, γ, hγU, hγi, hγi', hγe⟩` from `hS e heZ heB`. Take `⟨x, hxG, hxK, hx⟩` from `hK' γ hγU hγi hγi'`. Use `⟨x, hxG, hxK, fun v i j => ?_⟩` and prove the remaining obligations. Establish `hMle : M e₀ ≤ Mt` using `hMt (Set.mem_image_of_mem M he₀S)`.

Take `⟨c, hc, hcM⟩` from `hM e₀ he₀S v i`. Establish `hvec : ∀ l, vec I (x.1 * y) (e₀ l) = vec I y (e l)` using `fun l => by`. Rewrite using `[← hγe l]`. Conclude with `vec_trans I x.1 y γ hx (e l)`. Establish `hb` using `entry_bound I (x.1 * y) e₀ c v i hc j`.

Rewrite `hb` using `[hvec]`. Establish `ht : 0 ≤ t ^ N` using `pow_nonneg ht0.le _`. Rewrite using `[uj_entry]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_mul]`.

Repeatedly rewrite using `[mul_assoc]`. Use `_ ≤ ∑ l, |c l| * max C 0 := Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left ((hesz t ht0 ht1 hns l).trans (le_max_left _ _)) (abs_nonneg _)`. Use `_ = (∑ l, |c l|) * max C 0 := by rw [Finset.sum_mul]`. Use `_ ≤ Mt * max C 0 := mul_le_mul_of_nonneg_right (hcM.trans hMle) (le_max_right _ _)`.
-/
theorem GlobalTheory.htMin_of_reduced : ∀ I : AutInst, HtMin I := by
  intro I
  classical
  obtain ⟨N, R, C, hred⟩ := GlobalTheory.T.existsReducedBasisBoundedType_of_instance I
  obtain ⟨S, hSfin, hS0, hS⟩ := GlobalTheory.T.integralVectorBases_bounded_finite_unitaryClasses I N R
  obtain ⟨K, hK, hK'⟩ := GlobalTheory.T.exists_compact_integral_unitary_finitePart I
  have hbd : ∀ e₀ : Fin N → Fin I.n → I.E, ∃ M : ℝ, e₀ ∈ S → ∀ v i, ∃ c : Fin N → ℝ,
      (Pi.single v (Pi.single i (1 : ℂ)) : InfinitePlace I.F → Fin I.n → ℂ) = ∑ l, c l • vec I 1 (e₀ l) ∧
        ∑ l, |c l| ≤ M := by
    intro e₀
    by_cases h : e₀ ∈ S
    · have := fun v i => span_of_zbasis I e₀ (hS0 e₀ h) (Pi.single v (Pi.single i (1 : ℂ)))
      choose c hc using this
      refine ⟨∑ v, ∑ i, ∑ l, |c v i l|, fun _ v i => ⟨c v i, hc v i, ?_⟩⟩
      calc ∑ l, |c v i l| ≤ ∑ i', ∑ l, |c v i' l| :=
            Finset.single_le_sum (f := fun i' => ∑ l, |c v i' l|)
              (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
        _ ≤ ∑ v', ∑ i', ∑ l, |c v' i' l| :=
            Finset.single_le_sum (f := fun v' => ∑ i', ∑ l, |c v' i' l|)
              (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
              (Finset.mem_univ v)
    · exact ⟨0, fun h' => absurd h' h⟩
  choose M hM using hbd
  obtain ⟨Mt, hMt⟩ := (hSfin.image M).bddAbove
  refine ⟨N, Mt * max C 0, K, hK, ?_⟩
  intro y t ht0 ht1 hns
  obtain ⟨e, heZ, heB, hesz⟩ := hred y
  obtain ⟨e₀, he₀S, γ, hγU, hγi, hγi', hγe⟩ := hS e heZ heB
  obtain ⟨x, hxG, hxK, hx⟩ := hK' γ hγU hγi hγi'
  refine ⟨x, hxG, hxK, fun v i j => ?_⟩
  have hMle : M e₀ ≤ Mt := hMt (Set.mem_image_of_mem M he₀S)
  obtain ⟨c, hc, hcM⟩ := hM e₀ he₀S v i
  have hvec : ∀ l, vec I (x.1 * y) (e₀ l) = vec I y (e l) := fun l => by
    rw [← hγe l]
    exact vec_trans I x.1 y γ hx (e l)
  have hb := entry_bound I (x.1 * y) e₀ c v i hc j
  simp_rw [hvec] at hb
  have ht : 0 ≤ t ^ N := pow_nonneg ht0.le _
  rw [uj_entry]
  calc ‖uMat ((x.1 * y) v)⁻¹ j i‖ * t ^ N ≤ (∑ l, |c l| * ‖vec I y (e l)‖) * t ^ N :=
        mul_le_mul_of_nonneg_right hb ht
    _ = ∑ l, |c l| * (‖vec I y (e l)‖ * t ^ N) := by
        rw [Finset.sum_mul]
        simp_rw [mul_assoc]
    _ ≤ ∑ l, |c l| * max C 0 := Finset.sum_le_sum fun l _ =>
        mul_le_mul_of_nonneg_left ((hesz t ht0 ht1 hns l).trans (le_max_left _ _)) (abs_nonneg _)
    _ = (∑ l, |c l|) * max C 0 := by rw [Finset.sum_mul]
    _ ≤ Mt * max C 0 := mul_le_mul_of_nonneg_right (hcM.trans hMle) (le_max_right _ _)
