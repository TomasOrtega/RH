import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEqZpowMulUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthonormalBasisAndOneOrbit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEquivOfRetractions
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeUnipotentTranslateStandard
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGluingHomomorphismDefectGroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitEntries
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralOfMulVec
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HmUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalExtend
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralOfQuad
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.SelfDual

open Matrix GlobalTheory.HL.Eichler GlobalTheory.UnramOrder

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ L n m Hm hH b hint₀ hunim`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[F]`. Take `⟨htr, -, -, hpir, -, -, -, hnorm⟩` from `order_facts L ϖ hϖ`. Take `⟨P₀, hP₀, hGP₀⟩` from `hunim`. Establish `hmem : ∀ i, b i ∈ Submodule.span L.O (Set.range b)` using `fun i => Submodule.subset_span ⟨i, rfl⟩`.

Establish `hsm : ∀ (a : L.O) (v : Fin n → E), a • v = (a : E) • v` using `fun _ _ => rfl`. Set `c : L.O →+* L.O` to `(L.cj : E →+* E).restrict L.O L.O fun x hx => cj_mem L hx`. Establish `hcv : ∀ x : L.O, ((c x : L.O) : E) = L.cj x` using `fun _ => rfl`. Establish `hc : ∀ x, c (c x) = x` using `fun x => Subtype.ext (L.cj_cj x)`. Set `G : Matrix (Fin m) (Fin m) L.O` to `fun i j => ⟨hf L Hm (b i) (b j), hint₀ i j⟩`.

Establish `hGv : ∀ i j, (G i j : E) = hf L Hm (b i) (b j)` using `fun _ _ => rfl`. Establish `hG : ∀ i j, c (G i j) = G j i` using `fun i j => Subtype.ext (hf_cj L hH.1 _ _)`. Set `Q : Matrix (Fin m) (Fin m) L.O` to `fun i j => ⟨P₀ i j, hP₀ i j⟩`. Establish `hGQ : G * Q = 1`. Use extensionality with `i j`.

Establish `h` using `congrFun (congrFun hGP₀ i) j`. Rewrite using `[Matrix.one_apply, apply_ite Subtype.val, OneMemClass.coe_one, ZeroMemClass.coe_zero, Matrix.mul_apply, AddSubmonoidClass.coe_finset_sum]`. Rewrite `h` using `[Matrix.mul_apply, Matrix.one_apply]`. Conclude with `h`. Establish `hint : ∀ a : 𝒪[F], algebraMap F E a ∈ L.O` using `fun a => (algebraMap_mem_iff L a).2 a.2`.

Set `i : 𝒪[F] →+* L.O` to `(algebraMap 𝒪[F] E).codRestrict L.O hint`. Set `: Algebra 𝒪[F] L.O` to `i.toAlgebra`. Establish `hfix : ∀ x, c x = x → x ∈ (algebraMap 𝒪[F] L.O).range` using `fun x hx => by`. Take `⟨a, ha⟩` from `exists_int_of_fixed L x.2 (congrArg Subtype.val hx)`. Conclude with `⟨a, Subtype.ext ha.symm⟩`.

Establish `hinj : Function.Injective (algebraMap 𝒪[F] L.O)` using `fun a b h => Subtype.ext (algebraMap_inj L (congrArg Subtype.val h))`. Take `⟨P, hP, hGP⟩` from `GlobalTheory.UnramifiedHermitian.exists_eq_transpose_mul_map (R₀ := 𝒪[F]) c hc hfix (by`. Take `⟨w, hw, h⟩` from `htr 1`. Conclude with `⟨⟨w, hw⟩, Subtype.ext (by simpa [hcv] using h)⟩)`. Use the proof step `(fun u hu hu' => by`.

Take `⟨v, hv⟩` from `hu'.exists_right_inv`. Establish `hv'` using `congrArg c hv`. Rewrite `hv'` using `[map_mul, hu, map_one]`. Take `⟨s, rfl⟩` from `hfix v (by linear_combination v * hv' - c v * hv)`. Take `⟨r, rfl⟩` from `hfix u hu`.

Establish `hr : IsUnit r` using `IsUnit.of_mul_eq_one s (hinj (by rw [map_mul, hv, map_one]))`. Take `⟨x, hx, h⟩` from `hnorm hr.unit`. Conclude with `⟨⟨x, hx⟩, Subtype.ext h⟩)`. Use `hG (Matrix.isUnit_det_of_right_inverse hGQ)`. Establish `hQ : (P⁻¹)ᵀ * G * (P⁻¹).map c = 1`.

Rewrite using `[hGP, ← Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hP, Matrix.transpose_one, Matrix.one_mul, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hP, Matrix.map_one _ (map_zero c) (map_one c)]`. Use `⟨fun i => ∑ k, P⁻¹ k i • b k, fun i j => ?_, le_antisymm ?_ ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg Subtype.val (congrFun (congrFun hQ i) j)`. Rewrite `h` using `[Matrix.one_apply, apply_ite Subtype.val, OneMemClass.coe_one, ZeroMemClass.coe_zero]`. Rewrite using `[← h]`.

Simplify using `only [hsm, hf_sum_l, hf_sum_r, Matrix.mul_apply, AddSubmonoidClass.coe_finset_sum, Subring.coe_mul, Matrix.transpose_apply, Matrix.map_apply, hcv, hGv]`. Conclude with `Finset.sum_congr rfl fun k _ => mul_comm _ _`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hmem l)`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Use `(Submodule.mem_span_range_iff_exists_fun L.O).2 ⟨fun i => P i k, ?_⟩` and prove the remaining obligations. Simplify using `only [Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`.

Establish `h : ∀ l, ∑ i, P i k * P⁻¹ l i = if l = k then 1 else 0` using `fun l => by`. Rewrite using `[← Matrix.one_apply, ← Matrix.nonsing_inv_mul _ hP, Matrix.mul_apply]`. Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`. Simplify using `[← Finset.sum_smul, h]`.
-/
theorem exists_orthonormal_same_span : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ b : Fin m → Fin n → E, (∀ i j, hf L Hm (b i) (b j) ∈ L.O) → (∃ P : Matrix (Fin m) (Fin m) E, IsIntM L P ∧ (Matrix.of fun i j => hf L Hm (b i) (b j)) * P = 1) → ∃ b' : Fin m → Fin n → E, (∀ i j, hf L Hm (b' i) (b' j) = if i = j then 1 else 0) ∧ Submodule.span L.O (Set.range b') = Submodule.span L.O (Set.range b) := by
  intro F _ _ _ _ _ E _ _ _ L n m Hm hH b hint₀ hunim
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨htr, -, -, hpir, -, -, -, hnorm⟩ := order_facts L ϖ hϖ
  obtain ⟨P₀, hP₀, hGP₀⟩ := hunim
  have hmem : ∀ i, b i ∈ Submodule.span L.O (Set.range b) := fun i =>
    Submodule.subset_span ⟨i, rfl⟩
  have hsm : ∀ (a : L.O) (v : Fin n → E), a • v = (a : E) • v := fun _ _ => rfl
  let c : L.O →+* L.O := (L.cj : E →+* E).restrict L.O L.O fun x hx => cj_mem L hx
  have hcv : ∀ x : L.O, ((c x : L.O) : E) = L.cj x := fun _ => rfl
  have hc : ∀ x, c (c x) = x := fun x => Subtype.ext (L.cj_cj x)
  let G : Matrix (Fin m) (Fin m) L.O := fun i j => ⟨hf L Hm (b i) (b j), hint₀ i j⟩
  have hGv : ∀ i j, (G i j : E) = hf L Hm (b i) (b j) := fun _ _ => rfl
  have hG : ∀ i j, c (G i j) = G j i := fun i j => Subtype.ext (hf_cj L hH.1 _ _)
  let Q : Matrix (Fin m) (Fin m) L.O := fun i j => ⟨P₀ i j, hP₀ i j⟩
  have hGQ : G * Q = 1 := by
    ext i j
    have h := congrFun (congrFun hGP₀ i) j
    rw [Matrix.one_apply, apply_ite Subtype.val, OneMemClass.coe_one, ZeroMemClass.coe_zero,
      Matrix.mul_apply, AddSubmonoidClass.coe_finset_sum]
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    exact h
  have hint : ∀ a : 𝒪[F], algebraMap F E a ∈ L.O := fun a => (algebraMap_mem_iff L a).2 a.2
  let i : 𝒪[F] →+* L.O := (algebraMap 𝒪[F] E).codRestrict L.O hint
  let : Algebra 𝒪[F] L.O := i.toAlgebra
  have hfix : ∀ x, c x = x → x ∈ (algebraMap 𝒪[F] L.O).range := fun x hx => by
    obtain ⟨a, ha⟩ := exists_int_of_fixed L x.2 (congrArg Subtype.val hx)
    exact ⟨a, Subtype.ext ha.symm⟩
  have hinj : Function.Injective (algebraMap 𝒪[F] L.O) := fun a b h =>
    Subtype.ext (algebraMap_inj L (congrArg Subtype.val h))
  obtain ⟨P, hP, hGP⟩ := GlobalTheory.UnramifiedHermitian.exists_eq_transpose_mul_map (R₀ := 𝒪[F]) c hc hfix
    (by
      obtain ⟨w, hw, h⟩ := htr 1
      exact ⟨⟨w, hw⟩, Subtype.ext (by simpa [hcv] using h)⟩)
    (fun u hu hu' => by
      obtain ⟨v, hv⟩ := hu'.exists_right_inv
      have hv' := congrArg c hv
      rw [map_mul, hu, map_one] at hv'
      obtain ⟨s, rfl⟩ := hfix v (by linear_combination v * hv' - c v * hv)
      obtain ⟨r, rfl⟩ := hfix u hu
      have hr : IsUnit r := IsUnit.of_mul_eq_one s (hinj (by rw [map_mul, hv, map_one]))
      obtain ⟨x, hx, h⟩ := hnorm hr.unit
      exact ⟨⟨x, hx⟩, Subtype.ext h⟩)
    hG (Matrix.isUnit_det_of_right_inverse hGQ)
  have hQ : (P⁻¹)ᵀ * G * (P⁻¹).map c = 1 := by
    rw [hGP, ← Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hP,
      Matrix.transpose_one, Matrix.one_mul, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hP,
      Matrix.map_one _ (map_zero c) (map_one c)]
  refine ⟨fun i => ∑ k, P⁻¹ k i • b k, fun i j => ?_, le_antisymm ?_ ?_⟩
  · have h := congrArg Subtype.val (congrFun (congrFun hQ i) j)
    rw [Matrix.one_apply, apply_ite Subtype.val, OneMemClass.coe_one, ZeroMemClass.coe_zero] at h
    rw [← h]
    simp only [hsm, hf_sum_l, hf_sum_r, Matrix.mul_apply, AddSubmonoidClass.coe_finset_sum,
      Subring.coe_mul, Matrix.transpose_apply, Matrix.map_apply, hcv, hGv]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hmem l)
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    refine (Submodule.mem_span_range_iff_exists_fun L.O).2 ⟨fun i => P i k, ?_⟩
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have h : ∀ l, ∑ i, P i k * P⁻¹ l i = if l = k then 1 else 0 := fun l => by
      rw [← Matrix.one_apply, ← Matrix.nonsing_inv_mul _ hP, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    simp [← Finset.sum_smul, h]

end GlobalTheory.HL.SelfDual
