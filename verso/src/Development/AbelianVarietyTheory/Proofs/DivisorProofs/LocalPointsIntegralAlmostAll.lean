import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormRootOfUnitary
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocRatPt

open scoped ComplexOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Unfold `UL`. Use `split_ifs with hs`. Conclude with `Subgroup.mem_top _`. Establish `hc` using `((GlobalTheory.ConjAtPlace.main E hU w).2.2.2.1 hs).1`. Establish `hγ : cT (IsCMField.complexConj E).toRingEquiv.toRingHom (γ.1 : Matrix (Fin n) (Fin n) E) * 1 * (γ.1 : Matrix (Fin n) (Fin n) E) = 1` using `γ.2`.

Express the relevant statement in the definitionally equal form `cT (cj w) ((γ.1 : Matrix (Fin n) (Fin n) E).map (algebraMap E (w.adicCompletion E))) * 1 * (γ.1 : Matrix (Fin n) (Fin n) E).map (algebraMap E (w.adicCompletion E)) = 1`. Establish `key : cT (cj w) ((γ.1 : Matrix (Fin n) (Fin n) E).map (algebraMap E (w.adicCompletion E))) = (cT (IsCMField.complexConj E).toRingEquiv.toRingHom (γ.1 : Matrix (Fin n) (Fin n) E)).map (algebraMap E (w.adicCompletion E))`. Conclude with `Matrix.ext fun i j => hc _`. Rewrite using `[key, Matrix.mul_one, ← Matrix.map_mul]`. Rewrite `hγ` using `[Matrix.mul_one]`.

Rewrite using `[hγ, Matrix.map_one _ (map_zero _) (map_one _)]`.
-/
theorem map_mem_UL (hU : Unr E) (w : Pl E) (γ : UE E n) :
    GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 ∈ UL n w := by
  unfold UL
  split_ifs with hs
  · exact Subgroup.mem_top _
  · have hc := ((GlobalTheory.ConjAtPlace.main E hU w).2.2.2.1 hs).1
    have hγ : cT (IsCMField.complexConj E).toRingEquiv.toRingHom (γ.1 : Matrix (Fin n) (Fin n) E) * 1 *
        (γ.1 : Matrix (Fin n) (Fin n) E) = 1 := γ.2
    change cT (cj w) ((γ.1 : Matrix (Fin n) (Fin n) E).map (algebraMap E (w.adicCompletion E))) * 1 *
      (γ.1 : Matrix (Fin n) (Fin n) E).map (algebraMap E (w.adicCompletion E)) = 1
    have key : cT (cj w) ((γ.1 : Matrix (Fin n) (Fin n) E).map (algebraMap E (w.adicCompletion E))) =
        (cT (IsCMField.complexConj E).toRingEquiv.toRingHom (γ.1 : Matrix (Fin n) (Fin n) E)).map
          (algebraMap E (w.adicCompletion E)) := by
      exact Matrix.ext fun i j => hc _
    rw [key, Matrix.mul_one, ← Matrix.map_mul]
    rw [Matrix.mul_one] at hγ
    rw [hγ, Matrix.map_one _ (map_zero _) (map_one _)]

/- English proof (translation)
Rewrite using `[locPt, toSub, dif_pos (map_mem_UL hU w γ)]`.
-/
theorem locPt_val (hU : Unr E) (w : Pl E) (γ : UE E n) :
    (locPt w γ).1 = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 := by
  rw [locPt, toSub, dif_pos (map_mem_UL hU w γ)]

/- English proof (translation)
Rewrite using `[Filter.eventually_cofinite]`. Use `(HeightOneSpectrum.Support.finite (𝓞 E) x).subset fun w hw => ?_` and prove the remaining obligations. Conclude with `lt_of_not_ge hw`.
-/
theorem eventually_valuation_le_one (x : E) :
    ∀ᶠ w in (cofinite : Filter (Pl E)), w.valuation E x ≤ 1 := by
  rw [Filter.eventually_cofinite]
  refine (HeightOneSpectrum.Support.finite (𝓞 E) x).subset fun w hw => ?_
  exact lt_of_not_ge hw

/- English proof (translation)
Rewrite using `[ValuationSubring.mem_toSubring, HeightOneSpectrum.mem_adicCompletionIntegers]`. Rewrite using `[show Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x from HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x]`. Conclude with `h`.
-/
theorem algebraMap_mem_Ov {w : Pl E} {x : E} (h : w.valuation E x ≤ 1) :
    algebraMap E (w.adicCompletion E) x ∈ Ov E w := by
  rw [ValuationSubring.mem_toSubring, HeightOneSpectrum.mem_adicCompletionIntegers]
  rw [show Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x from
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x]
  exact h

/- English proof (translation)
Use `⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, ?_, ?_⟩, rfl⟩` and prove the remaining obligations. Use `Matrix.map_injective O.subtype_injective ?_` and prove the remaining obligations. Simplify using `only`. Rewrite using `[Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `x.mul_inv`.

Use `Matrix.map_injective O.subtype_injective ?_` and prove the remaining obligations. Simplify using `only`. Rewrite using `[Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `x.inv_mul`.
-/
theorem mem_GLint_of_entries {K : Type} [Field K] {O : Subring K} {x : GL (Fin n) K} (h1 : ∀ i j, x.1 i j ∈ O)
    (h2 : ∀ i j, (x⁻¹).1 i j ∈ O) : x ∈ GLint (Fin n) O := by
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, ?_, ?_⟩, rfl⟩
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

/- English proof (translation)
Establish `h1 : ∀ᶠ w in (cofinite : Filter (Pl E)), ∀ i j, w.valuation E ((γ.1 : GL (Fin n) E).1 i j) ≤ 1 ∧ w.valuation E (((γ.1 : GL (Fin n) E)⁻¹).1 i j) ≤ 1`. Simplify using `only [Filter.eventually_all]`. Introduce `i j`. Conclude with `(eventually_valuation_le_one _).and (eventually_valuation_le_one _)`. Use `filter_upwards [h1] with w hw`.

Rewrite using `[KL, Subgroup.mem_subgroupOf, locPt_val hU]`. Use `mem_GLint_of_entries (fun i j => algebraMap_mem_Ov (hw i j).1) (fun i j => ?_)` and prove the remaining obligations. Rewrite using `[← map_inv]`. Conclude with `algebraMap_mem_Ov (hw i j).2`.
-/
theorem eventually_mem_KL (hU : Unr E) (γ : UE E n) :
    ∀ᶠ w in (cofinite : Filter (Pl E)), locPt w γ ∈ KL n w := by
  have h1 : ∀ᶠ w in (cofinite : Filter (Pl E)), ∀ i j, w.valuation E ((γ.1 : GL (Fin n) E).1 i j) ≤ 1 ∧
      w.valuation E (((γ.1 : GL (Fin n) E)⁻¹).1 i j) ≤ 1 := by
    simp only [Filter.eventually_all]
    intro i j
    exact (eventually_valuation_le_one _).and (eventually_valuation_le_one _)
  filter_upwards [h1] with w hw
  rw [KL, Subgroup.mem_subgroupOf, locPt_val hU]
  refine mem_GLint_of_entries (fun i j => algebraMap_mem_Ov (hw i j).1) (fun i j => ?_)
  rw [← map_inv]
  exact algebraMap_mem_Ov (hw i j).2

/- English proof (translation)
Use `first`. Consider the case `(rename_i h_1 h_2 h_3; revert E h_1 h_2 h_3 n γ τ z hz; exact @_root_.GlobalTheory.UnitaryCharpolyRootNorm.norm_root_charpoly)`. Consider the case `exact @_root_.GlobalTheory.UnitaryCharpolyRootNorm.norm_root_charpoly`. Consider the case `exact _root_.GlobalTheory.UnitaryCharpolyRootNorm.norm_root_charpoly`. Consider the case `(apply _root_.GlobalTheory.UnitaryCharpolyRootNorm.norm_root_charpoly <;> assumption)`.

Consider the case `(intros; apply _root_.GlobalTheory.UnitaryCharpolyRootNorm.norm_root_charpoly <;> assumption)`. Consider the case `(intros; apply @_root_.GlobalTheory.UnitaryCharpolyRootNorm.norm_root_charpoly <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.UnitaryCharpolyRootNorm.norm_root_charpoly ..)`.
-/
theorem norm_eq_one_of_root (γ : UE E n) (τ : E →+* ℂ) (z : ℂ)
    (hz : z ∈ ((γ.1 : GL (Fin n) E).val.charpoly.map τ).roots) : ‖z‖ = 1 := by
  first
  | (rename_i h_1 h_2 h_3; revert E h_1 h_2 h_3 n γ τ z hz; exact @_root_.GlobalTheory.UnitaryCharpolyRootNorm.norm_root_charpoly)
  | exact @_root_.GlobalTheory.UnitaryCharpolyRootNorm.norm_root_charpoly
  | exact _root_.GlobalTheory.UnitaryCharpolyRootNorm.norm_root_charpoly
  | (apply _root_.GlobalTheory.UnitaryCharpolyRootNorm.norm_root_charpoly <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnitaryCharpolyRootNorm.norm_root_charpoly <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnitaryCharpolyRootNorm.norm_root_charpoly <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnitaryCharpolyRootNorm.norm_root_charpoly ..)

/- English proof (translation)
Assemble the required witnesses or components as `⟨Matrix.charpoly_monic _, by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin], hs, fun τ z hz => norm_eq_one_of_root γ τ z hz⟩`.
-/
theorem charpoly_mem_Ell (γ : UE E n) (hs : (γ.1 : GL (Fin n) E).val.charpoly.Separable) :
    (γ.1 : GL (Fin n) E).val.charpoly ∈ Ell E n :=
  ⟨Matrix.charpoly_monic _, by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin], hs,
    fun τ z hz => norm_eq_one_of_root γ τ z hz⟩

/- English proof (translation)
Introduce `E _ _ _ hU n γ`. Conclude with `⟨fun w => locPt_val hU w γ, eventually_mem_KL hU γ, charpoly_mem_Ell γ⟩`.
-/
theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ : UE E n), (∀ w : Pl E, (locPt w γ).1 = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1) ∧ (∀ᶠ w in (cofinite : Filter (Pl E)), locPt w γ ∈ KL n w) ∧ (γ.1.val.charpoly.Separable → γ.1.val.charpoly ∈ Ell E n) := by
  intro E _ _ _ hU n γ
  exact ⟨fun w => locPt_val hU w γ, eventually_mem_KL hU γ, charpoly_mem_Ell γ⟩

end GlobalTheory.LocRatPt
