import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.ProdFormula
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.TestLat

open Classical in

/- English proof (translation)
Simplify using `only [dotProduct, Matrix.mulVec, Matrix.of_apply]`. Rewrite using `[← e.symm.sum_comp, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `congr 1`. Rewrite using `[← e.symm.sum_comp, Fintype.sum_prod_type]`.

Simplify using `only [Equiv.apply_symm_apply, ite_mul, zero_mul]`. Rewrite using `[Finset.sum_eq_single c]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Ne.symm hb]`.

Simplify using the standard rewrite rules.
-/
theorem blockForm_apply {F C I : Type} [CommRing F] [Fintype C] [Fintype I] {N : ℕ} (e : Fin N ≃ C × I)
    (M : Matrix I I F) (x y : Fin N → F) :
    x ⬝ᵥ (Matrix.of fun a b => if (e a).1 = (e b).1 then M (e a).2 (e b).2 else 0) *ᵥ y =
      ∑ c, (fun i => x (e.symm (c, i))) ⬝ᵥ M *ᵥ (fun i => y (e.symm (c, i))) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply]
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.apply_symm_apply, ite_mul, zero_mul]
  rw [Finset.sum_eq_single c]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

open Classical in

/- English proof (translation)
Use `Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_` and prove the remaining obligations. Use extensionality with `a b`. Simplify using `only [Matrix.conjTranspose_apply, Matrix.of_apply]`. Distinguish the cases in `h : (e a).1 = (e b).1`. Rewrite using `[if_pos h, if_pos h.symm]`.

Conclude with `hM.isHermitian.apply _ _`. Rewrite using `[if_neg h, if_neg (fun h' => h h'.symm), star_zero]`. Introduce `x hx`. Rewrite using `[blockForm_apply]`. Take `⟨a, ha⟩` from `Function.ne_iff.mp hx`.

Use `Finset.sum_pos' (fun c _ => ?_) ⟨(e a).1, Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Conclude with `hM.posSemidef.dotProduct_mulVec_nonneg (fun i => x (e.symm (c, i)))`. Use `hM.dotProduct_mulVec_pos (x := fun i => x (e.symm ((e a).1, i))) ?_` and prove the remaining obligations. Introduce `h0`. Apply `ha` to reduce the goal to its premises.

Simplify using `using congrFun h0 (e a).2`.
-/
theorem blockForm_posDef {C I : Type} [Fintype C] [Fintype I] {N : ℕ} (e : Fin N ≃ C × I)
    (M : Matrix I I ℂ) (hM : M.PosDef) :
    (Matrix.of fun a b => if (e a).1 = (e b).1 then M (e a).2 (e b).2 else 0).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext a b
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
    by_cases h : (e a).1 = (e b).1
    · rw [if_pos h, if_pos h.symm]
      exact hM.isHermitian.apply _ _
    · rw [if_neg h, if_neg (fun h' => h h'.symm), star_zero]
  · intro x hx
    rw [blockForm_apply]
    obtain ⟨a, ha⟩ := Function.ne_iff.mp hx
    refine Finset.sum_pos' (fun c _ => ?_) ⟨(e a).1, Finset.mem_univ _, ?_⟩
    · exact hM.posSemidef.dotProduct_mulVec_nonneg (fun i => x (e.symm (c, i)))
    · refine hM.dotProduct_mulVec_pos (x := fun i => x (e.symm ((e a).1, i))) ?_
      intro h0
      apply ha
      simpa using congrFun h0 (e a).2

variable {K : Type} [Field K] [NumberField K] [StarRing K]

/- English proof (translation)
Take `⟨φ⟩ : Nonempty (K →+* ℂ)` from `inferInstance`. Establish `h1` using `(h.2.2 φ).det_pos`. Establish `h2 : (G.map φ).det = φ G.det` using `(RingHom.map_det φ G).symm`. Rewrite `h1` using `[h2]`. Use `isUnit_iff_ne_zero.mpr fun h0 => ?_` and prove the remaining obligations.

Rewrite `h1` using `[h0, map_zero]`. Conclude with `lt_irrefl _ h1`.
-/
theorem IsDefGram.isUnit_det {n : ℕ} {G : Matrix (Fin n) (Fin n) K} (h : IsDefGram G) : IsUnit G.det := by
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have h1 := (h.2.2 φ).det_pos
  have h2 : (G.map φ).det = φ G.det := (RingHom.map_det φ G).symm
  rw [h2] at h1
  refine isUnit_iff_ne_zero.mpr fun h0 => ?_
  rw [h0, map_zero] at h1
  exact lt_irrefl _ h1

/- English proof (translation)
Use `symm`. Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Rewrite using `[← Matrix.map_mul, Matrix.nonsing_inv_mul _ h, Matrix.map_one _ (map_zero φ) (map_one φ)]`.
-/
theorem map_inv_of_isUnit {F F' : Type} [Field F] [Field F'] {n : ℕ} (φ : F →+* F') (G : Matrix (Fin n) (Fin n) F)
    (h : IsUnit G.det) : (G⁻¹).map φ = (G.map φ)⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ h, Matrix.map_one _ (map_zero φ) (map_one φ)]

/- English proof (translation)
Establish `hu` using `h.isUnit_det`. Use `⟨?_, ?_, fun φ => ?_⟩` and prove the remaining obligations. Establish `h1 : (G⁻¹)ᴴ = G⁻¹` using `by rw [Matrix.conjTranspose_nonsing_inv, h.1]`. Use extensionality with `a b`. Use `congrFun (congrFun h1 b) a` as an intermediate fact.

Simplify `this` using `[Matrix.conjTranspose_apply]`. Introduce `a b set G0 : Matrix (Fin n) (Fin n) (cmMax K) := Matrix.of fun a b => ⟨G a b, h.2.1 a b⟩ with hG0`. Establish `e0 : G = G0.map (cmMax K).subtype` using `by ext a b; rfl`. Establish `hu0 : IsUnit G0.det`. Use `isUnit_iff_ne_zero.mpr fun h0 => hu.ne_zero ?_` and prove the remaining obligations.

Establish `h2 : (G0.map (cmMax K).subtype).det = (cmMax K).subtype G0.det` using `(RingHom.map_det _ G0).symm`. Rewrite using `[e0, h2, h0, map_zero]`. Rewrite using `[Matrix.transpose_apply, e0, ← map_inv_of_isUnit _ _ hu0, Matrix.map_apply]`. Conclude with `(G0⁻¹ b a).2`. Rewrite using `[Matrix.transpose_map, map_inv_of_isUnit _ _ hu]`.

Conclude with `(h.2.2 φ).inv.transpose`.
-/
theorem IsDefGram.inv_transpose {n : ℕ} {G : Matrix (Fin n) (Fin n) K} (h : IsDefGram G) : IsDefGram (G⁻¹)ᵀ := by
  have hu := h.isUnit_det
  refine ⟨?_, ?_, fun φ => ?_⟩
  · have h1 : (G⁻¹)ᴴ = G⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, h.1]
    ext a b
    have := congrFun (congrFun h1 b) a
    simpa [Matrix.conjTranspose_apply] using this
  · intro a b
    set G0 : Matrix (Fin n) (Fin n) (cmMax K) := Matrix.of fun a b => ⟨G a b, h.2.1 a b⟩ with hG0
    have e0 : G = G0.map (cmMax K).subtype := by ext a b; rfl
    have hu0 : IsUnit G0.det := by
      refine isUnit_iff_ne_zero.mpr fun h0 => hu.ne_zero ?_
      have h2 : (G0.map (cmMax K).subtype).det = (cmMax K).subtype G0.det := (RingHom.map_det _ G0).symm
      rw [e0, h2, h0, map_zero]
    rw [Matrix.transpose_apply, e0, ← map_inv_of_isUnit _ _ hu0, Matrix.map_apply]
    exact (G0⁻¹ b a).2
  · rw [Matrix.transpose_map, map_inv_of_isUnit _ _ hu]
    exact (h.2.2 φ).inv.transpose

omit [NumberField K] in

/- English proof (translation)
Simplify using `only [Module.Basis.equivFun_symm_apply, dotProduct, Matrix.mulVec, Matrix.of_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, Pi.star_apply, starRingEnd_apply, RingHom.id_apply]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pairK_equivFun_symm {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) K)
    (u v : VVIdx lam → K) :
    pairK lam G ((bVV K lam).equivFun.symm u) ((bVV K lam).equivFun.symm v) =
      star u ⬝ᵥ (Matrix.of fun i j => pairK lam G (bVV K lam i) (bVV K lam j)) *ᵥ v := by
  simp only [Module.Basis.equivFun_symm_apply, dotProduct, Matrix.mulVec, Matrix.of_apply, map_sum,
    LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum,
    Pi.star_apply, starRingEnd_apply, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Introduce `K _ _ _ ι _ n lam G hG C _ N e`. Establish `hdef : IsDefGram (sumGram lam e G)`. Use `⟨?_, ?_, fun φ => ?_⟩` and prove the remaining obligations. Use extensionality with `a b`. Simplify using `only [sumGram, Matrix.conjTranspose_apply, Matrix.of_apply]`.

Distinguish the cases in `h : (e a).1 = (e b).1`. Rewrite using `[if_pos h, if_pos h.symm]`. Conclude with `(pairSymm K ι n lam G fun τ => (hG τ).1).eq _ _`. Rewrite using `[if_neg h, if_neg (fun h' => h h'.symm), star_zero]`. Introduce `a b`.

Simplify using `only [sumGram, Matrix.of_apply]`. Use `split_ifs`. Conclude with `pairingRational_holds K ι n lam _ G (fun τ => (hG τ).2.1) _ _`. Conclude with `zero_mem _`. Establish `h1` using `blockForm_posDef e _ (pairingPositive_holds K ι n lam G φ fun τ => (hG τ).2.2 φ)`.

Use `h1 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `a b`. Simplify using `only [sumGram, Matrix.of_apply, Matrix.map_apply]`. Use `split_ifs`. Both sides reduce to the same expression.

Conclude with `map_zero φ`. Use `⟨fun x y => ?_, hdef, hdef.inv_transpose, fun τ => (hG τ).isUnit_det⟩` and prove the remaining obligations. Establish `h1` using `blockForm_apply e (Matrix.of fun i j => pairK lam G (bVV K lam i) (bVV K lam j)) (star x) y`. Use `Eq.trans h1 (Finset.sum_congr rfl fun c _ => ?_)` and prove the remaining obligations. Conclude with `(pairK_equivFun_symm lam G (fun i => x (e.symm (c, i))) (fun i => y (e.symm (c, i)))).symm`.
-/
theorem sumGram_spec : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) K), (∀ τ, IsDefGram (G τ)) → ∀ (C : Type) [Fintype C] (N : ℕ) (e : Fin N ≃ C × VVIdx lam), (∀ x y : Fin N → K, star x ⬝ᵥ sumGram lam e G *ᵥ y = ∑ c, pairK lam G (valAt lam e c x) (valAt lam e c y)) ∧ IsDefGram (sumGram lam e G) ∧ IsDefGram ((sumGram lam e G)⁻¹)ᵀ ∧ (∀ τ, IsUnit (G τ).det) := by
  intro K _ _ _ ι _ n lam G hG C _ N e
  have hdef : IsDefGram (sumGram lam e G) := by
    refine ⟨?_, ?_, fun φ => ?_⟩
    · ext a b
      simp only [sumGram, Matrix.conjTranspose_apply, Matrix.of_apply]
      by_cases h : (e a).1 = (e b).1
      · rw [if_pos h, if_pos h.symm]
        exact (pairSymm K ι n lam G fun τ => (hG τ).1).eq _ _
      · rw [if_neg h, if_neg (fun h' => h h'.symm), star_zero]
    · intro a b
      simp only [sumGram, Matrix.of_apply]
      split_ifs
      · exact pairingRational_holds K ι n lam _ G (fun τ => (hG τ).2.1) _ _
      · exact zero_mem _
    · have h1 := blockForm_posDef e _ (pairingPositive_holds K ι n lam G φ fun τ => (hG τ).2.2 φ)
      convert h1 using 1
      ext a b
      simp only [sumGram, Matrix.of_apply, Matrix.map_apply]
      split_ifs
      · rfl
      · exact map_zero φ
  refine ⟨fun x y => ?_, hdef, hdef.inv_transpose, fun τ => (hG τ).isUnit_det⟩
  have h1 := blockForm_apply e (Matrix.of fun i j => pairK lam G (bVV K lam i) (bVV K lam j)) (star x) y
  refine Eq.trans h1 (Finset.sum_congr rfl fun c _ => ?_)
  exact (pairK_equivFun_symm lam G (fun i => x (e.symm (c, i))) (fun i => y (e.symm (c, i)))).symm

end GlobalTheory.TestLat
