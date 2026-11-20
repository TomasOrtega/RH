import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerFurther
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsJoinPointIdeal
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsJoinDivCycle
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsJoinVariety
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsJoinIntNum
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsVerticalComponentFibre
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsFieldIntersectionExample
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBridgeFull
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord)

namespace JoinPointNumbers

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Conclude with `Classical.epsilon_spec (p := fun I : ReciprocityTheory.ChartRestriction.G.AI.I1.IFamily F κ => ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection I) ⟨_, IntNumIsFieldIntersection.full F K' κ⟩`.
-/
theorem fieldNum_spec (F : Type) [Field F] {K' : Type} [Fintype K'] (κ : K' → Type) [∀ k, Fintype (κ k)] :
    ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum F κ) := by
  classical
  exact Classical.epsilon_spec (p := fun I : ReciprocityTheory.ChartRestriction.G.AI.I1.IFamily F κ =>
    ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection I) ⟨_, IntNumIsFieldIntersection.full F K' κ⟩

/- English proof (translation)
Unfold `IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal`. Express the relevant statement in the definitionally equal form `Ideal.map (MvPolynomial.map (IsLocalRing.residue O)) (Ideal.map (rename (R := O) (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx)).toRingHom W) = Ideal.map (rename (R := IsLocalRing.ResidueField O) (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := …`. Rewrite using `[Ideal.map_map, Ideal.map_map]`. Use `congr 1`. Use `RingHom.ext fun p => ?_` and prove the remaining obligations.

Simplify using `[MvPolynomial.map_rename]`.
-/
theorem redIdeal_map_liftVar {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (W : Ideal (MRing ι O)) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O (W.map (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx))) =
      (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W).map
        (rename (R := IsLocalRing.ResidueField O) (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx)) := by
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal
  change Ideal.map (MvPolynomial.map (IsLocalRing.residue O))
      (Ideal.map (rename (R := O) (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx)).toRingHom W) =
    Ideal.map (rename (R := IsLocalRing.ResidueField O)
      (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx)).toRingHom
      (Ideal.map (MvPolynomial.map (IsLocalRing.residue O)) W)
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  refine RingHom.ext fun p => ?_
  simp [MvPolynomial.map_rename]

/- English proof (translation)
Simplify using `[IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList, List.map_flatMap, List.map_replicate]`.
-/
theorem monoList_pullDeg {r : ℕ} (deg : Fin r → K → ℤ) (μ : Fin r →₀ ℕ) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList (fun j => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (deg j)) μ =
      (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList deg μ).map (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit)) := by
  simp [IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList, List.map_flatMap, List.map_replicate]

/- English proof (translation)
Establish `hV'` using `hV F K ι V d hVd`. Unfold `IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum`. Use `Finset.sum_congr rfl fun μ _ => ?_` and prove the remaining obligations. Use `congr 1`. Establish `hl` using `monoList_pullDeg deg μ`.

Distinguish the cases in `h : (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList deg μ).length = d`. Establish `h' : (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList (fun j => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K'` using `Unit) (deg j)) μ).length = d := by`. Rewrite using `[hl, List.length_map, h]`. Rewrite using `[dif_pos h', dif_pos h, Numbers.agree_of FieldNumbers.IntNumBase.full FieldNumbers.CutRational.full FieldNumbers.ExistsForm.full FieldNumbers.DivCycleSupport.full _ (fieldNum_spec F _) _ d _ hV']`. Use `beta_reduce`.

Rewrite using `[← hN F K ι V d]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Simplify using `only [hl, List.get_eq_getElem, List.getElem_map, Fin.val_cast]`. Establish `h' : ¬ (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList (fun j => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K'` using `Unit) (deg j)) μ).length = d := by`.

Rewrite using `[hl, List.length_map]` and apply the resulting hypothesis. Rewrite using `[dif_neg h', dif_neg h]`.
-/
theorem polyNum_join (hV : JoinVariety.Statement) (hN : JoinIntNum.Statement) (F : Type) [Field F]
    (V : Ideal (MRing ι F)) (d : ℕ) (hVd : ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF V d) {r : ℕ}
    (deg : Fin r → K → ℤ) (H : MvPolynomial (Fin r) ℤ) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum F (Sum.elim ι ptIdx))
                              (V.map (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx))) d
                              (fun j => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (deg j)) H =
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum (fun V _ bs => intNum F V bs) V d deg H := by
  have hV' := hV F K ι V d hVd
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
  refine Finset.sum_congr rfl fun μ _ => ?_
  congr 1
  have hl := monoList_pullDeg deg μ
  by_cases h : (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList deg μ).length = d
  · have h' : (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList
        (fun j => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (deg j)) μ).length = d := by
      rw [hl, List.length_map, h]
    rw [dif_pos h', dif_pos h, Numbers.agree_of FieldNumbers.IntNumBase.full FieldNumbers.CutRational.full
      FieldNumbers.ExistsForm.full FieldNumbers.DivCycleSupport.full _ (fieldNum_spec F _) _ d _ hV']
    beta_reduce
    rw [← hN F K ι V d]
    congr 1
    funext j
    simp only [hl, List.get_eq_getElem, List.getElem_map, Fin.val_cast]
  · have h' : ¬ (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList
        (fun j => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (deg j)) μ).length = d := by
      rwa [hl, List.length_map]
    rw [dif_neg h', dif_neg h]

/- English proof (translation)
Unfold `IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval`. Rewrite using `[Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]`. Use `Finsupp.sum_congr fun W hW => ?_` and prove the remaining obligations. Rewrite using `[redIdeal_map_liftVar]`. Use `beta_reduce`.

Rewrite using `[polyNum_join hV hN _ (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W) d (hZ W (Finsupp.mem_support_iff.mp hW)) deg H]`.
-/
theorem vEval_join (hV : JoinVariety.Statement) (hN : JoinIntNum.Statement) {O : Type} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] (d : ℕ) {r : ℕ} (deg : Fin r → K → ℤ)
    (H : MvPolynomial (Fin r) ℤ) (Z : Ideal (MRing ι O) →₀ ℤ)
    (hZ : ∀ W, Z W ≠ 0 → ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF (specialIdeal W) d) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun V => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
                              (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum (IsLocalRing.ResidueField O) (Sum.elim ι ptIdx)) V d
                              (fun j => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (deg j)) H)
      (Finsupp.mapDomain (Ideal.map (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx))) Z) =
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun V => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
                              (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs) V d deg H) Z := by
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval
  rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  refine Finsupp.sum_congr fun W hW => ?_
  rw [redIdeal_map_liftVar]
  beta_reduce
  rw [polyNum_join hV hN _ (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W) d (hZ W (Finsupp.mem_support_iff.mp hW))
    deg H]

/- English proof (translation)
Assume the negation of the conclusion as `hW`. Apply `h` to reduce the goal to its premises. Simplify using `only [ReciprocityTheory.ChartRestriction.G.Geo.divCycle, Finsupp.ofSupportFinite_coe]`. Rewrite using `[if_neg hW]`.
-/
theorem mem_divSupp_of_ne {R : Type} [CommRing R] [IsNoetherianRing R] (P : Ideal (MRing ι R))
    (s : MRing ι R) (W : Ideal (MRing ι R)) (h : ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s W ≠ 0) :
    W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s := by
  classical
  by_contra hW
  apply h
  simp only [ReciprocityTheory.ChartRestriction.G.Geo.divCycle, Finsupp.ofSupportFinite_coe]
  rw [if_neg hW]

/- English proof (translation)
Rewrite using `[hD R K ι P s, Finsupp.mapDomain_mapRange _ _ _ _ fun x y => Nat.cast_add x y]`.
-/
theorem intCycle_join (hD : JoinDivCycle.Statement) {R : Type} [CommRing R] [IsNoetherianRing R]
    (P : Ideal (MRing ι R)) (s : MRing ι R) :
    Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero (ReciprocityTheory.ChartRestriction.G.Geo.divCycle
        (P.map (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx)))
        (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx) s)) =
      Finsupp.mapDomain (Ideal.map (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx)))
        (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s)) := by
  rw [hD R K ι P s, Finsupp.mapDomain_mapRange _ _ _ _ fun x y => Nat.cast_add x y]

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hM r deg H`. Rewrite using `[hI O Ω K ι y]`. Use `⟨fun b f g hdiv => ?_, fun a ha => ?_⟩` and prove the remaining obligations. Establish `hc : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O ((pointIdeal O y).map (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι` using `ι) ptIdx))) (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) f) (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) g) = Finsupp.mapDomain (Ideal.map (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx))) (Indefinit …`. Unfold `IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc`.

Rewrite using `[intCycle_join hD, intCycle_join hD, Finsupp.mapDomain_sub]`. Rewrite using `[hc]`. Use `vEval_join hV hN d deg H _ fun W hW => ?_` and prove the remaining obligations. Establish `hvert : (C ϖ : MRing ι O) ∈ W` using `hdiv.vertical W (by rwa [← BundleExamples.ratCyc_eq])`. Take `⟨bf, bg, hf, hg, -⟩` from `hdiv.degrees`.

Establish `hor : ReciprocityTheory.ChartRestriction.G.Geo.divCycle (pointIdeal O y) f W ≠ 0 ∨ ReciprocityTheory.ChartRestriction.G.Geo.divCycle (pointIdeal O y) g W ≠ 0`. Assume the negation of the conclusion as `hc`. Simplify using `only [not_or, ne_eq, not_not] at hc`. Apply `hW` to reduce the goal to its premises. Simplify using `[IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc, hc.1, hc.2]`.

Break down `hor with h | h` into its components or cases. Establish `hs` using `mem_divSupp_of_ne _ _ _ h`. Take `⟨h1, h2⟩` from `hF O ϖ hϖ K ι (pointIdeal O y) d hM f bf hf hdiv.num_not_mem W hs.1 hs.2 hvert`. Conclude with `⟨(Objects.isMultiProjPrime_iff _).mp h1, h2⟩`. Establish `hs` using `mem_divSupp_of_ne _ _ _ h`.

Take `⟨h1, h2⟩` from `hF O ϖ hϖ K ι (pointIdeal O y) d hM g bg hg hdiv.den_not_mem W hs.1 hs.2 hvert`. Conclude with `⟨(Objects.isMultiProjPrime_iff _).mp h1, h2⟩`. Establish `hC : (C a : MRing (Sum.elim ι ptIdx) O) = rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι` using `ι) ptIdx) (C a) := (rename_C _ _).symm`. Rewrite using `[hC, intCycle_join hD]`. Use `vEval_join hV hN d deg H _ fun W hW => ?_` and prove the remaining obligations.

Establish `h : ReciprocityTheory.ChartRestriction.G.Geo.divCycle (pointIdeal O y) (C a) W ≠ 0`. Introduce `h0`. Apply `hW` to reduce the goal to its premises. Simplify using `[h0]`. Establish `hs` using `mem_divSupp_of_ne _ _ _ h`.

Establish `hWp : W.IsPrime` using `hs.1.1.1`. Establish `hCa : (C a : MRing ι O) ∈ W` using `hs.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))`. Establish `hnP : (C a : MRing ι O) ∉ pointIdeal O y`. Introduce `hmem`. Establish `hmem' : a ∈ (pointIdeal O y).comap (C : O →+* MRing ι O)` using `hmem`.

Rewrite `hmem'` using `[hM.noTorsion, Ideal.mem_bot]`. Conclude with `ha hmem'`. Establish `hvert : (C ϖ : MRing ι O) ∈ W`. Take `⟨n, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ`. Rewrite `hCa` using `[hu, C_mul, C_pow]`.

Break down `hWp.mem_or_mem hCa with h1 | h1` into its components or cases. Conclude with `absurd (Ideal.eq_top_of_isUnit_mem _ h1 ((Units.isUnit u).map C)) hWp.ne_top`. Conclude with `hWp.mem_of_pow_mem n h1`. Take `⟨h1, h2⟩` from `hF O ϖ hϖ K ι (pointIdeal O y) d hM (C a) 0 (isWeightedHomogeneous_C _ _) hnP W hs.1 hs.2 hvert`. Conclude with `⟨(Objects.isMultiProjPrime_iff _).mp h1, h2⟩`.
-/
theorem proof (hI : JoinPointIdeal.Statement) (hD : JoinDivCycle.Statement)
    (hV : JoinVariety.Statement) (hN : JoinIntNum.Statement)
    (hF : VerticalComponentFibre.Statement) : JoinPointNumbers.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hM r deg H
  rw [hI O Ω K ι y]
  refine ⟨fun b f g hdiv => ?_, fun a ha => ?_⟩
  · have hc : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O
        ((pointIdeal O y).map (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx)))
        (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) f)
        (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) g) =
        Finsupp.mapDomain (Ideal.map (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx)))
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O (pointIdeal O y) f g) := by
      unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc
      rw [intCycle_join hD, intCycle_join hD, Finsupp.mapDomain_sub]
    rw [hc]
    refine vEval_join hV hN d deg H _ fun W hW => ?_
    have hvert : (C ϖ : MRing ι O) ∈ W :=
      hdiv.vertical W (by rwa [← BundleExamples.ratCyc_eq])
    obtain ⟨bf, bg, hf, hg, -⟩ := hdiv.degrees
    have hor : ReciprocityTheory.ChartRestriction.G.Geo.divCycle (pointIdeal O y) f W ≠ 0 ∨
        ReciprocityTheory.ChartRestriction.G.Geo.divCycle (pointIdeal O y) g W ≠ 0 := by
      by_contra hc
      simp only [not_or, ne_eq, not_not] at hc
      apply hW
      simp [IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc, hc.1, hc.2]
    rcases hor with h | h
    · have hs := mem_divSupp_of_ne _ _ _ h
      obtain ⟨h1, h2⟩ := hF O ϖ hϖ K ι (pointIdeal O y) d hM f bf hf hdiv.num_not_mem W hs.1 hs.2 hvert
      exact ⟨(Objects.isMultiProjPrime_iff _).mp h1, h2⟩
    · have hs := mem_divSupp_of_ne _ _ _ h
      obtain ⟨h1, h2⟩ := hF O ϖ hϖ K ι (pointIdeal O y) d hM g bg hg hdiv.den_not_mem W hs.1 hs.2 hvert
      exact ⟨(Objects.isMultiProjPrime_iff _).mp h1, h2⟩
  · have hC : (C a : MRing (Sum.elim ι ptIdx) O) =
        rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx) (C a) := (rename_C _ _).symm
    rw [hC, intCycle_join hD]
    refine vEval_join hV hN d deg H _ fun W hW => ?_
    have h : ReciprocityTheory.ChartRestriction.G.Geo.divCycle (pointIdeal O y) (C a) W ≠ 0 := by
      intro h0
      apply hW
      simp [h0]
    have hs := mem_divSupp_of_ne _ _ _ h
    have hWp : W.IsPrime := hs.1.1.1
    have hCa : (C a : MRing ι O) ∈ W := hs.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hnP : (C a : MRing ι O) ∉ pointIdeal O y := by
      intro hmem
      have hmem' : a ∈ (pointIdeal O y).comap (C : O →+* MRing ι O) := hmem
      rw [hM.noTorsion, Ideal.mem_bot] at hmem'
      exact ha hmem'
    have hvert : (C ϖ : MRing ι O) ∈ W := by
      obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
      rw [hu, C_mul, C_pow] at hCa
      rcases hWp.mem_or_mem hCa with h1 | h1
      · exact absurd (Ideal.eq_top_of_isUnit_mem _ h1 ((Units.isUnit u).map C)) hWp.ne_top
      · exact hWp.mem_of_pow_mem n h1
    obtain ⟨h1, h2⟩ := hF O ϖ hϖ K ι (pointIdeal O y) d hM (C a) 0 (isWeightedHomogeneous_C _ _) hnP W
      hs.1 hs.2 hvert
    exact ⟨(Objects.isMultiProjPrime_iff _).mp h1, h2⟩

end JoinPointNumbers

end GroundTheory.Heights₂.Heights.NumbersDVR
