import Mathlib
import Formalism.LocalRingCardinality.HostCls
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AsIdealSpMapClosedPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkMapInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportedRuleOfFlagComponentSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceComponentSmoothProjectiveConnected
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFlagNonempty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivLeSubMulDiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WtBigRun
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanBdLeSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsExtendVanishCompactifiedFlagSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalIntegralWeightSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongerPublishedHypothesesImplyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroSectionWeightBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentredPointPhiPositiveWeightsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentredPointPhiPositiveStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelObjectDescendsFgSubfield
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ValMultRun

section Algebra

open IsLocalRing IsDedekindDomain
open scoped NNReal

/- English proof (translation)
Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x h => exact hF x h`. Consider the case `zero => rw [map_zero, zero_pow hn]`. Conclude with `zero_lt_iff.2 hc`.

Consider the case `add x y _ _ hx hy`. Break down `le_max_iff.1 (μ.map_add x y) with h | h` into its components or cases. Use `exacts [(pow_le_pow_left₀ zero_le' h n).trans_lt hx, (pow_le_pow_left₀ zero_le' h n).trans_lt hy]`. Consider the case `smul a x _ hx`. Use `(pow_le_pow_left₀ zero_le' ?_ n).trans_lt hx` and prove the remaining obligations.

Rewrite using `[smul_eq_mul, map_mul]`. Conclude with `mul_le_of_le_one_left' (h1 a)`.
-/
theorem pow_lt_of_mem_span {R Γ : Type} [CommRing R] [LinearOrderedCommGroupWithZero Γ] (μ : Valuation R Γ)
    (h1 : ∀ x, μ x ≤ 1) {n : ℕ} (hn : n ≠ 0) {c : Γ} (hc : c ≠ 0) {F : Set R} (hF : ∀ x ∈ F, μ x ^ n < c) :
    ∀ x ∈ Ideal.span F, μ x ^ n < c := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x h => exact hF x h
  | zero => rw [map_zero, zero_pow hn]; exact zero_lt_iff.2 hc
  | add x y _ _ hx hy =>
    rcases le_max_iff.1 (μ.map_add x y) with h | h
    exacts [(pow_le_pow_left₀ zero_le' h n).trans_lt hx, (pow_le_pow_left₀ zero_le' h n).trans_lt hy]
  | smul a x _ hx =>
    refine (pow_le_pow_left₀ zero_le' ?_ n).trans_lt hx
    rw [smul_eq_mul, map_mul]
    exact mul_le_of_le_one_left' (h1 a)

/- English proof (translation)
Take `⟨μ₀, hμ₀⟩` from `GlobalTheory.HSApp.ValCrit.exists_valuation R`. Take `⟨i₀, hi₀⟩` from `h μ₀ hμ₀`. Distinguish the cases in `hu : t ^ a = 0`. Conclude with `⟨i₀, by rw [← map_pow, ← map_pow, hu, map_zero, map_zero]; exact zero_le'⟩`. Distinguish the cases in `hf : IsField R`.

Use `⟨i₀, (pow_le_one₀ zero_le' (h1 t)).trans (one_le_pow₀ ?_)⟩` and prove the remaining obligations. Establish `hs : s i₀ ≠ 0` using `fun e => by`. Rewrite `hi₀` using `[e, map_zero, zero_pow hb, ← map_pow]`. Conclude with `hu (hμ₀.2.2 _ (le_antisymm hi₀ zero_le'))`. Take `⟨v, hv⟩` from `hf.mul_inv_cancel hs`.

Combine the equalities or inequalities in the displayed calculation. Assume the negation of the conclusion as `hn`. Use `push Not at hn`. Set `K` to `FractionRing R`. Set `G : K →+* Ω` to `IsFractionRing.lift hg`.

Establish `hG : ∀ x : R, G (algebraMap R K x) = g x` using `fun x => IsFractionRing.lift_algebraMap hg x`. Set `W` to `(ν.comap G).valuationSubring`. Establish `hW : ∀ x : K, ν (G x) < 1 → x ∈ W.nonunits` using `fun x hx => by`. Rewrite using `[ValuationSubring.mem_nonunits_iff, ← (Valuation.isEquiv_valuation_valuationSubring (ν.comap G)).lt_one_iff_lt_one]`. Conclude with `hx`.

Take `⟨M, hM⟩` from `(IsNoetherian.noetherian (maximalIdeal R))`. Take `⟨F, hF, hFs⟩` from `(Submodule.fg_span_iff_fg_span_finset_subset (R := R) (Set.range s)).1 (IsNoetherian.noetherian _)`. Establish `hu' : algebraMap R K (t ^ a) ≠ 0` using `fun e => hu (IsFractionRing.injective R K (e.trans (map_zero _).symm))`. Take `⟨V, hV, hRV, -, hnu⟩` from `GlobalTheory.exists_discreteValuationSubring_of_valuationSubring (R := R) W (fun r => show ν (G (algebraMap R K r)) ≤ 1 by rw [hG]; exact h1 r) Set.finite_empty ((M.finite_toSet.image (algebraMap R K)).union (F.finite_toSet.image fun x => algebraMap R K (x ^ b) / algebraMap R K ( …`. Introduce and unpack `_ (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)`.

Conclude with `hW _ (by rw [hG]; exact h2 x (hM ▸ Submodule.subset_span hx))`. Take `⟨i, rfl⟩` from `hF hx`. Use `hW _ ?_` and prove the remaining obligations. Rewrite using `[map_div₀, hG, hG, map_div₀, map_pow, map_pow, map_pow, map_pow]`. Conclude with `(div_lt_one₀ (zero_le'.trans_lt (hn i))).2 (hn i))`.

Use the proof step `(by`. Assume the negation of the conclusion as `hz`. Use `push Not at hz`. Use `hf (isField_iff_maximalIdeal_eq.2 ?_)` and prove the remaining obligations. Rewrite using `[← hM, Submodule.span_eq_bot]`.

Conclude with `fun x hx => IsFractionRing.injective R K ((hz _ (Or.inl ⟨x, hx, rfl⟩)).trans (map_zero _).symm))`. Set `v : HeightOneSpectrum V` to `⟨maximalIdeal V, inferInstance, IsDiscreteValuationRing.not_a_field V⟩`. Establish `hle : ∀ x ∈ V, v.valuation K x ≤ 1` using `fun x hx => v.valuation_le_one (K := K) ⟨x, hx⟩`. Establish `hlt : ∀ x ∈ V.nonunits, v.valuation K x < 1` using `fun x hx => (v.valuation_lt_one_iff_mem (K := K) ⟨x, V.nonunits_subset hx⟩).2 ((ValuationSubring.coe_mem_nonunits_iff (a := ⟨x, V.nonunits_subset hx⟩)).1 hx)`. Set `μ` to `(v.valuation K).comap (algebraMap R K)`.

Establish `m1 : ∀ x, μ x ≤ 1` using `fun x => hle _ (hRV x)`. Establish `m0 : ∀ x, μ x = 0 → x = 0` using `fun x hx => IsFractionRing.injective R K (((v.valuation K).zero_iff.1 hx).trans (map_zero _).symm)`. Establish `mm : ∀ x ∈ maximalIdeal R, μ x < 1` using `fun x hx => by`. Rewrite `hx` using `[← hM]`. Simplify using `using pow_lt_of_mem_span μ m1 one_ne_zero one_ne_zero (fun x hx => by rw [pow_one]; exact hlt _ (hnu _ (Or.inl ⟨x, hx, rfl⟩))) x hx`.

Take `⟨i, hi⟩` from `h μ ⟨m1, mm, m0⟩`. Establish `hc : μ (t ^ a) ≠ 0` using `fun e => hu (m0 _ e)`. Use `pow_lt_of_mem_span μ m1 hb hc (F := F) (fun x hx => by` as an intermediate fact. Establish `e` using `hlt _ (hnu _ (Or.inr ⟨x, hx, rfl⟩))`. Rewrite `e` using `[map_div₀]`.

Rewrite using `[← map_pow]`. Conclude with `(div_lt_one₀ (zero_lt_iff.2 hc)).1 e) (s i) (hFs.le (Submodule.subset_span ⟨i, rfl⟩))`. Rewrite `this` using `[map_pow]`. Conclude with `absurd hi (not_le.2 this)`.
-/
theorem exists_le_of_discrete {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] {ι : Type}
    (s : ι → R) (t : R) (a : ℕ) {b : ℕ} (hb : b ≠ 0)
    (h : ∀ μ : Valuation R (WithZero (Multiplicative ℤ)),
      ((∀ x, μ x ≤ 1) ∧ (∀ x ∈ maximalIdeal R, μ x < 1) ∧ ∀ x, μ x = 0 → x = 0) → ∃ i, μ t ^ a ≤ μ (s i) ^ b)
    {Ω : Type} [Field Ω] (g : R →+* Ω) (hg : Function.Injective g) (ν : Valuation Ω ℝ≥0) (h1 : ∀ x, ν (g x) ≤ 1)
    (h2 : ∀ x ∈ maximalIdeal R, ν (g x) < 1) : ∃ i, ν (g t) ^ a ≤ ν (g (s i)) ^ b := by
  classical
  obtain ⟨μ₀, hμ₀⟩ := GlobalTheory.HSApp.ValCrit.exists_valuation R
  obtain ⟨i₀, hi₀⟩ := h μ₀ hμ₀
  by_cases hu : t ^ a = 0
  · exact ⟨i₀, by rw [← map_pow, ← map_pow, hu, map_zero, map_zero]; exact zero_le'⟩
  by_cases hf : IsField R
  · refine ⟨i₀, (pow_le_one₀ zero_le' (h1 t)).trans (one_le_pow₀ ?_)⟩
    have hs : s i₀ ≠ 0 := fun e => by
      rw [e, map_zero, zero_pow hb, ← map_pow] at hi₀
      exact hu (hμ₀.2.2 _ (le_antisymm hi₀ zero_le'))
    obtain ⟨v, hv⟩ := hf.mul_inv_cancel hs
    calc (1 : ℝ≥0) = ν (g (s i₀)) * ν (g v) := by rw [← map_mul, ← map_mul, hv, map_one, map_one]
      _ ≤ _ := mul_le_of_le_one_right' (h1 v)
  by_contra hn
  push Not at hn
  let K := FractionRing R
  let G : K →+* Ω := IsFractionRing.lift hg
  have hG : ∀ x : R, G (algebraMap R K x) = g x := fun x => IsFractionRing.lift_algebraMap hg x
  let W := (ν.comap G).valuationSubring
  have hW : ∀ x : K, ν (G x) < 1 → x ∈ W.nonunits := fun x hx => by
    rw [ValuationSubring.mem_nonunits_iff, ← (Valuation.isEquiv_valuation_valuationSubring (ν.comap G)).lt_one_iff_lt_one]
    exact hx
  obtain ⟨M, hM⟩ := (IsNoetherian.noetherian (maximalIdeal R))
  obtain ⟨F, hF, hFs⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (R := R) (Set.range s)).1
    (IsNoetherian.noetherian _)
  have hu' : algebraMap R K (t ^ a) ≠ 0 := fun e => hu (IsFractionRing.injective R K (e.trans (map_zero _).symm))
  obtain ⟨V, hV, hRV, -, hnu⟩ := GlobalTheory.exists_discreteValuationSubring_of_valuationSubring (R := R) W
    (fun r => show ν (G (algebraMap R K r)) ≤ 1 by rw [hG]; exact h1 r) Set.finite_empty
    ((M.finite_toSet.image (algebraMap R K)).union
      (F.finite_toSet.image fun x => algebraMap R K (x ^ b) / algebraMap R K (t ^ a))) (by simp)
    (by
      rintro _ (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
      · exact hW _ (by rw [hG]; exact h2 x (hM ▸ Submodule.subset_span hx))
      · obtain ⟨i, rfl⟩ := hF hx
        refine hW _ ?_
        rw [map_div₀, hG, hG, map_div₀, map_pow, map_pow, map_pow, map_pow]
        exact (div_lt_one₀ (zero_le'.trans_lt (hn i))).2 (hn i))
    (by
      by_contra hz
      push Not at hz
      refine hf (isField_iff_maximalIdeal_eq.2 ?_)
      rw [← hM, Submodule.span_eq_bot]
      exact fun x hx => IsFractionRing.injective R K ((hz _ (Or.inl ⟨x, hx, rfl⟩)).trans (map_zero _).symm))
  let v : HeightOneSpectrum V := ⟨maximalIdeal V, inferInstance, IsDiscreteValuationRing.not_a_field V⟩
  have hle : ∀ x ∈ V, v.valuation K x ≤ 1 := fun x hx => v.valuation_le_one (K := K) ⟨x, hx⟩
  have hlt : ∀ x ∈ V.nonunits, v.valuation K x < 1 := fun x hx =>
    (v.valuation_lt_one_iff_mem (K := K) ⟨x, V.nonunits_subset hx⟩).2
      ((ValuationSubring.coe_mem_nonunits_iff (a := ⟨x, V.nonunits_subset hx⟩)).1 hx)
  let μ := (v.valuation K).comap (algebraMap R K)
  have m1 : ∀ x, μ x ≤ 1 := fun x => hle _ (hRV x)
  have m0 : ∀ x, μ x = 0 → x = 0 := fun x hx =>
    IsFractionRing.injective R K (((v.valuation K).zero_iff.1 hx).trans (map_zero _).symm)
  have mm : ∀ x ∈ maximalIdeal R, μ x < 1 := fun x hx => by
    rw [← hM] at hx
    simpa using pow_lt_of_mem_span μ m1 one_ne_zero one_ne_zero
      (fun x hx => by rw [pow_one]; exact hlt _ (hnu _ (Or.inl ⟨x, hx, rfl⟩))) x hx
  obtain ⟨i, hi⟩ := h μ ⟨m1, mm, m0⟩
  have hc : μ (t ^ a) ≠ 0 := fun e => hu (m0 _ e)
  have := pow_lt_of_mem_span μ m1 hb hc (F := F) (fun x hx => by
    have e := hlt _ (hnu _ (Or.inr ⟨x, hx, rfl⟩))
    rw [map_div₀] at e
    rw [← map_pow]
    exact (div_lt_one₀ (zero_lt_iff.2 hc)).1 e) (s i) (hFs.le (Submodule.subset_span ⟨i, rfl⟩))
  rw [map_pow] at this
  exact absurd hi (not_le.2 this)

end Algebra

section Centre

open TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.TangentOrigin
open GlobalTheory.Adelic (ptOf le_iff_ptOf_mem ptOf_comp)
open scoped NNReal

/- English proof (translation)
Establish `key` using `Scheme.germ_stalkClosedPointTo (R := CommRingCat.of V) x W hy`. Use `congrArg (fun φ => φ.hom g) key` as an intermediate fact. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply] at this`. Use `this.trans ?_` and prove the remaining obligations. Simplify using `only [evalPt, Scheme.Hom.appLE, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, CommRingCat.hom_comp, RingHom.comp_apply, Category.assoc]`.

Use `congr!`.
-/
theorem stalkClosedPointTo_ger' {V : Type} [CommRing V] [IsLocalRing V] {Y : Scheme.{0}} (x : Sp V ⟶ Y) (W : Y.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ W) (g : Γ(Y, W)) (hy : x (IsLocalRing.closedPoint V) ∈ W) :
    (Scheme.stalkClosedPointTo (R := CommRingCat.of V) x).hom (ger _ hy g) = evalPt x W h g := by
  have key := Scheme.germ_stalkClosedPointTo (R := CommRingCat.of V) x W hy
  have := congrArg (fun φ => φ.hom g) key
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  refine this.trans ?_
  simp only [evalPt, Scheme.Hom.appLE, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom,
    CommRingCat.hom_comp, RingHom.comp_apply, Category.assoc]
  congr!

/- English proof (translation)
Establish `hη : ptOf z ∈ W` using `(le_iff_ptOf_mem _ _).1 h`. Use `haveI : IsLocalHom (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) z).hom := Scheme.isLocalHom_stalkClosedPointTo' (R := Ω) z`. Establish `hu : ¬ IsUnit (ger (ptOf z) hη s)` using `fun hu => by`. Use `hu.map (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) z).hom` as an intermediate fact. Conclude with `not_isUnit_zero (((stalkClosedPointTo_ger' z W h s hη).trans hs) ▸ this)`.

Establish `key : ∀ η : Y, IsGenericPoint η Set.univ → ∀ x : Y.presheaf.stalk η, ¬ IsUnit x → x = 0`. Introduce `η hgen x hx`. Take `rfl : η = genericPoint Y` from `hgen.eq (genericPoint_spec _)`. Assume the negation of the conclusion as `hne`. Conclude with `hx ((isUnit_iff_ne_zero (G₀ := Y.functionField)).2 hne)`.

Conclude with `germ_injective_of_isIntegral Y _ hη ((key _ hz _ hu).trans (map_zero _).symm)`.
-/
theorem eq_zero_of_evalPt {Ω : Type} [Field Ω] {Y : Scheme.{0}} [IsIntegral Y] (z : Sp Ω ⟶ Y)
    (hz : IsGenericPoint (ptOf z) Set.univ) (W : Y.Opens) (h : ⊤ ≤ z ⁻¹ᵁ W) (s : Γ(Y, W)) (hs : evalPt z W h s = 0) :
    s = 0 := by
  have hη : ptOf z ∈ W := (le_iff_ptOf_mem _ _).1 h
  haveI : IsLocalHom (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) z).hom :=
    Scheme.isLocalHom_stalkClosedPointTo' (R := Ω) z
  have hu : ¬ IsUnit (ger (ptOf z) hη s) := fun hu => by
    have := hu.map (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) z).hom
    exact not_isUnit_zero (((stalkClosedPointTo_ger' z W h s hη).trans hs) ▸ this)
  have key : ∀ η : Y, IsGenericPoint η Set.univ → ∀ x : Y.presheaf.stalk η, ¬ IsUnit x → x = 0 := by
    intro η hgen x hx
    obtain rfl : η = genericPoint Y := hgen.eq (genericPoint_spec _)
    by_contra hne
    exact hx ((isUnit_iff_ne_zero (G₀ := Y.functionField)).2 hne)
  exact germ_injective_of_isIntegral Y _ hη ((key _ hz _ hu).trans (map_zero _).symm)

/- English proof (translation)
Set `V` to `ν.valuationSubring`. Set `β : k →+* V` to `(algebraMap k Ω).codRestrict V fun a => show ν (algebraMap k Ω a) ≤ 1 by`. Distinguish the cases in `ha : a = 0`. Simplify using `[ha]`. Conclude with `(hν a ha).le`.

Establish `hE : ValuativeCriterion.Existence p` using `(UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed p) : (ValuativeCriterion.Existence ⊓ @QuasiCompact) p).1`. Establish `hw : z ≫ p = Spec.map (CommRingCat.ofHom (algebraMap V Ω)) ≫ spMap β`. Rewrite using `[hp, ← Spec.map_comp]`. Both sides reduce to the same expression. Take `⟨⟨w, hw', -⟩⟩` from `(hE { R := V, K := Ω, i₁ := z, i₂ := spMap β, commSq := ⟨hw⟩ }).exists_lift`.

Establish `hw'' : spMap (algebraMap V Ω) ≫ w = z` using `hw'`. Use `haveI : IsLocalHom (Scheme.stalkClosedPointTo (R := CommRingCat.of V) w).hom := Scheme.isLocalHom_stalkClosedPointTo' (R := V) w`. Set `g : Y.presheaf.stalk (w (IsLocalRing.closedPoint V)) →+* Ω` to `(algebraMap V Ω).comp (Scheme.stalkClosedPointTo (R := CommRingCat.of V) w).hom`. Establish `hg : ∀ (W : Y.Opens) (hy : w (IsLocalRing.closedPoint V) ∈ W) (h : ⊤ ≤ z ⁻¹ᵁ W) (s : Γ(Y, W)), g (ger _ hy s) = evalPt z W h s` using `fun W hy h s => by`. Establish `hW : ⊤ ≤ w ⁻¹ᵁ W` using `fun x _ => ((IsLocalRing.specializes_closedPoint x).map w.continuous).mem_open W.isOpen hy`.

Establish `e : ∀ (z' : Sp Ω ⟶ Y) (_ : spMap (algebraMap V Ω) ≫ w = z') (h' : ⊤ ≤ z' ⁻¹ᵁ W), evalPt z' W h' s = algebraMap V Ω (evalPt w W hW s)`. Introduce and unpack `_ rfl h'`. Conclude with `evalPt_spMap_comp _ w W hW h' s`. Rewrite using `[e z hw'' h]`. Conclude with `congrArg (algebraMap V Ω) (stalkClosedPointTo_ger' (V := V) w W hW s hy)`.

Use `⟨_, g, (injective_iff_map_eq_zero g).2 fun x hx => ?_, fun x => ((Scheme.stalkClosedPointTo (R := CommRingCat.of V) w).hom x).2, fun x hx => ?_, hg⟩` and prove the remaining obligations. Take `⟨W, hy, s, rfl⟩` from `Y.presheaf.exists_germ_eq x`. Establish `h : ⊤ ≤ z ⁻¹ᵁ W` using `(le_iff_ptOf_mem _ _).2 ((hz.mem_open_set_iff W.isOpen).2 ⟨_, trivial, hy⟩)`. Rewrite using `[eq_zero_of_evalPt z hz W h s ((hg W hy h s).symm.trans hx), map_zero]`. Establish `hm : (Scheme.stalkClosedPointTo (R` using `CommRingCat.of V) w).hom x ∈ IsLocalRing.maximalIdeal V := (IsLocalRing.mem_maximalIdeal _).2 fun hu => (IsLocalRing.mem_maximalIdeal _).1 hx (isUnit_of_map_unit _ x hu)`.

Use `(ValuationSubring.valuation_lt_one_iff V _).1 hm` as an intermediate fact. Conclude with `(Valuation.isEquiv_valuation_valuationSubring ν).lt_one_iff_lt_one.2 this`.
-/
theorem exists_centre {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {Y : Scheme.{0}} [IsIntegral Y] (p : Y ⟶ Sp k)
    [IsProper p] (z : Sp Ω ⟶ Y) (hp : z ≫ p = spMap (algebraMap k Ω)) (hz : IsGenericPoint (ptOf z) Set.univ)
    (ν : Valuation Ω ℝ≥0) (hν : ∀ a : k, a ≠ 0 → ν (algebraMap k Ω a) = 1) :
    ∃ (y : Y) (g : Y.presheaf.stalk y →+* Ω), Function.Injective g ∧ (∀ x, ν (g x) ≤ 1) ∧
      (∀ x ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y), ν (g x) < 1) ∧
      ∀ (W : Y.Opens) (hy : y ∈ W) (h : ⊤ ≤ z ⁻¹ᵁ W) (s : Γ(Y, W)), g (ger y hy s) = evalPt z W h s := by
  let V := ν.valuationSubring
  let β : k →+* V := (algebraMap k Ω).codRestrict V fun a => show ν (algebraMap k Ω a) ≤ 1 by
    by_cases ha : a = 0
    · simp [ha]
    · exact (hν a ha).le
  have hE : ValuativeCriterion.Existence p :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed p) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) p).1
  have hw : z ≫ p = Spec.map (CommRingCat.ofHom (algebraMap V Ω)) ≫ spMap β := by
    rw [hp, ← Spec.map_comp]; rfl
  obtain ⟨⟨w, hw', -⟩⟩ := (hE { R := V, K := Ω, i₁ := z, i₂ := spMap β, commSq := ⟨hw⟩ }).exists_lift
  have hw'' : spMap (algebraMap V Ω) ≫ w = z := hw'
  haveI : IsLocalHom (Scheme.stalkClosedPointTo (R := CommRingCat.of V) w).hom :=
    Scheme.isLocalHom_stalkClosedPointTo' (R := V) w
  let g : Y.presheaf.stalk (w (IsLocalRing.closedPoint V)) →+* Ω :=
    (algebraMap V Ω).comp (Scheme.stalkClosedPointTo (R := CommRingCat.of V) w).hom
  have hg : ∀ (W : Y.Opens) (hy : w (IsLocalRing.closedPoint V) ∈ W) (h : ⊤ ≤ z ⁻¹ᵁ W) (s : Γ(Y, W)),
      g (ger _ hy s) = evalPt z W h s := fun W hy h s => by
    have hW : ⊤ ≤ w ⁻¹ᵁ W := fun x _ =>
      ((IsLocalRing.specializes_closedPoint x).map w.continuous).mem_open W.isOpen hy
    have e : ∀ (z' : Sp Ω ⟶ Y) (_ : spMap (algebraMap V Ω) ≫ w = z') (h' : ⊤ ≤ z' ⁻¹ᵁ W),
        evalPt z' W h' s = algebraMap V Ω (evalPt w W hW s) := by
      rintro _ rfl h'
      exact evalPt_spMap_comp _ w W hW h' s
    rw [e z hw'' h]
    exact congrArg (algebraMap V Ω) (stalkClosedPointTo_ger' (V := V) w W hW s hy)
  refine ⟨_, g, (injective_iff_map_eq_zero g).2 fun x hx => ?_,
    fun x => ((Scheme.stalkClosedPointTo (R := CommRingCat.of V) w).hom x).2, fun x hx => ?_, hg⟩
  · obtain ⟨W, hy, s, rfl⟩ := Y.presheaf.exists_germ_eq x
    have h : ⊤ ≤ z ⁻¹ᵁ W := (le_iff_ptOf_mem _ _).2 ((hz.mem_open_set_iff W.isOpen).2 ⟨_, trivial, hy⟩)
    rw [eq_zero_of_evalPt z hz W h s ((hg W hy h s).symm.trans hx), map_zero]
  · have hm : (Scheme.stalkClosedPointTo (R := CommRingCat.of V) w).hom x ∈ IsLocalRing.maximalIdeal V :=
      (IsLocalRing.mem_maximalIdeal _).2 fun hu => (IsLocalRing.mem_maximalIdeal _).1 hx (isUnit_of_map_unit _ x hu)
    have := (ValuationSubring.valuation_lt_one_iff V _).1 hm
    exact (Valuation.isEquiv_valuation_valuationSubring ν).lt_one_iff_lt_one.2 this

end Centre

section Component

open TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.TangentOrigin GlobalTheory.Vanishing.H0
open GlobalTheory.Adelic (ptOf le_iff_ptOf_mem ptOf_comp)
open GlobalTheory.AllWt (secZ exOf suppOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (genVal genPoint)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open scoped NNReal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c)

/- English proof (translation)
Establish `h : GenFrEx Xo c` using `(Reg.genFrEx_and_genFromTest E H Dw l Xo c).1`. Use `haveI : IsProper (str₀ X Z) := by`. Take `⟨N, i, hi, e⟩` from `hV.2.1`. Rewrite using `[← e]`. Use `isProper_str c.F N` as an intermediate fact.

Use `infer_instance`. Set `M` to `Modif.refl hV.1 hV.2.1 (dense_U₀ X Z)`. Take `⟨z, hz, hO⟩` from `exists_lift_genFr M h`. Establish `hgen` using `isGenericPoint_of_lift M h hz hO`. Express the relevant statement in the definitionally equal form `Sp (Om Z) ⟶ Y₀ X Z at z`.

Establish `hz' : z ≫ inc₀ X Z = X.ptY (genFr h Z)` using `(congrArg (z ≫ ·) (Category.id_comp _)).symm.trans hz`. Establish `hU : ⊤ ≤ z ⁻¹ᵁ U₀ X Z`. Introduce `s _`. Use `hO (Set.mem_univ s)` as an intermediate fact. Rewrite `this` using `[M.off_eq]`.

Conclude with `this`. Establish `hstr : z ≫ str₀ X Z = spMap (algebraMap c.F (Om Z))`. Rewrite using `[← Category.assoc, hz', ptY_str]`. Take `⟨y, g, hg, h1, h2, h3⟩` from `exists_centre (str₀ X Z) z hstr hgen ν hν`. Take `⟨k, hk⟩` from `(common₀ X Z).cover y`.

Establish `hj : ∀ la, y ∈ (L₀ X Z la).U ((common₀ X Z).idx la k)` using `fun la => ((common₀ X Z).mem la k y).2 hk`. Establish `hopen : ∀ W : (Y₀ X Z).Opens, y ∈ W → ⊤ ≤ z ⁻¹ᵁ W` using `fun W hy => (le_iff_ptOf_mem _ _).2 ((hgen.mem_open_set_iff W.isOpen).2 ⟨_, trivial, hy⟩)`. Establish `e₁ : z ≫ inc₀ X Z = X.pt (genFr h Z) ≫ X.inc` using `by rw [X.pt_inc]; exact hz'`. Establish `hk₂ : ⊤ ≤ (z ≫ inc₀ X Z) ⁻¹ᵁ X.F.U k` using `hopen _ hk`. Establish `hk₁ : ⊤ ≤ (X.pt (genFr h Z) ≫ X.inc) ⁻¹ᵁ X.F.U k` using `e₁ ▸ hk₂`.

Take `⟨Q, t, hQ, ht⟩` from `X.exists_chartFr_frBor (genFr h Z) k hk₁`. Establish `hQ₂ : X.F.ChartFr k (z ≫ inc₀ X Z) hk₂ Q` using `chartFr_congr e₁.symm hQ`. Establish `hO₂ : ⊤ ≤ (z ≫ inc₀ X Z) ⁻¹ᵁ flagOpen X` using `hU`. Use `⟨y, g, fun la => (common₀ X Z).idx la k, hj, fun la => ∏ ix, t ix ^ exOf Dw la 0 ix, hg, h1, h2, fun a b => ?_, fun la f s hs => ?_⟩` and prove the remaining obligations. Simplify using `only [exOf_add_zero, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]`.

Establish `hTop : ⊤ ≤ z ⁻¹ᵁ (⊤ : (Y₀ X Z).Opens)` using `fun _ _ => trivial`. Establish `hi'` using `hopen _ (hj la)`. Establish `v₈` using `evR_eq_val_secOf f hO₂ hQ₂ ht`. Establish `v₅ : H0.val z ((common₀ X Z).idx la k) hU hi' (sec₀ X Z _ f) = H0.val (B` using `X.LL (exOf Dw la 0)) (z ≫ inc₀ X Z) k hO₂ hk₂ (secOf X _ f) := H0.val_pull (inc₀ X Z) le_rfl z _ hU hi' hO₂ hk₂ _`. Establish `v₄` using `val_restr' (p := str₀ X Z) (le_top : U₀ X Z ≤ ⊤) z _ hTop hU hi' s`.

Establish `v₆ : genVal Z f.1 = evR Xo c f.1 (genFr h Z)` using `rfl`. Establish `v₇ : g (germ ((common₀ X Z).idx la k) y (memTop y) (hj la) s) = H0.val z _ hTop hi' s`. Rewrite using `[H0.val_apply, H0.germ_apply]`. Conclude with `h3 _ _ _ _`. Rewrite using `[v₆, v₈, ← v₅, ← hs, v₄, v₇]`.
-/
theorem exists_centre_genVal (hV : IsVariety₀ X Z) [IsIntegral (Y₀ X Z)] (ν : Valuation (Om Z) ℝ≥0)
    (hν : ∀ a : c.F, a ≠ 0 → ν (algebraMap c.F (Om Z) a) = 1) :
    ∃ (y : Y₀ X Z) (g : (Y₀ X Z).presheaf.stalk y →+* Om Z) (j : ∀ la, (L₀ X Z la).ι) (hj : ∀ la, y ∈ (L₀ X Z la).U (j la))
      (T : AllWt.Weight Dw → (Om Z)ˣ), Function.Injective g ∧ (∀ x, ν (g x) ≤ 1) ∧
      (∀ x ∈ IsLocalRing.maximalIdeal ((Y₀ X Z).presheaf.stalk y), ν (g x) < 1) ∧ (∀ a b, T (a + b) = T a * T b) ∧
      ∀ (la : AllWt.Weight Dw) (f : secZ Xo c (exOf Dw la 0)) (s : H0 (str₀ X Z) (L₀ X Z la) ⊤),
        restr le_top s = sec₀ X Z _ f → genVal Z f.1 = T la * g (germ (j la) y (memTop y) (hj la) s) := by
  classical
  have h : GenFrEx Xo c := (Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  haveI : IsProper (str₀ X Z) := by
    obtain ⟨N, i, hi, e⟩ := hV.2.1
    rw [← e]
    have := isProper_str c.F N
    infer_instance
  let M := Modif.refl hV.1 hV.2.1 (dense_U₀ X Z)
  obtain ⟨z, hz, hO⟩ := exists_lift_genFr M h
  have hgen := isGenericPoint_of_lift M h hz hO
  change Sp (Om Z) ⟶ Y₀ X Z at z
  have hz' : z ≫ inc₀ X Z = X.ptY (genFr h Z) := (congrArg (z ≫ ·) (Category.id_comp _)).symm.trans hz
  have hU : ⊤ ≤ z ⁻¹ᵁ U₀ X Z := by
    intro s _
    have := hO (Set.mem_univ s)
    rw [M.off_eq] at this
    exact this
  have hstr : z ≫ str₀ X Z = spMap (algebraMap c.F (Om Z)) := by
    rw [← Category.assoc, hz', ptY_str]
  obtain ⟨y, g, hg, h1, h2, h3⟩ := exists_centre (str₀ X Z) z hstr hgen ν hν
  obtain ⟨k, hk⟩ := (common₀ X Z).cover y
  have hj : ∀ la, y ∈ (L₀ X Z la).U ((common₀ X Z).idx la k) := fun la => ((common₀ X Z).mem la k y).2 hk
  have hopen : ∀ W : (Y₀ X Z).Opens, y ∈ W → ⊤ ≤ z ⁻¹ᵁ W := fun W hy =>
    (le_iff_ptOf_mem _ _).2 ((hgen.mem_open_set_iff W.isOpen).2 ⟨_, trivial, hy⟩)
  have e₁ : z ≫ inc₀ X Z = X.pt (genFr h Z) ≫ X.inc := by rw [X.pt_inc]; exact hz'
  have hk₂ : ⊤ ≤ (z ≫ inc₀ X Z) ⁻¹ᵁ X.F.U k := hopen _ hk
  have hk₁ : ⊤ ≤ (X.pt (genFr h Z) ≫ X.inc) ⁻¹ᵁ X.F.U k := e₁ ▸ hk₂
  obtain ⟨Q, t, hQ, ht⟩ := X.exists_chartFr_frBor (genFr h Z) k hk₁
  have hQ₂ : X.F.ChartFr k (z ≫ inc₀ X Z) hk₂ Q := chartFr_congr e₁.symm hQ
  have hO₂ : ⊤ ≤ (z ≫ inc₀ X Z) ⁻¹ᵁ flagOpen X := hU
  refine ⟨y, g, fun la => (common₀ X Z).idx la k, hj, fun la => ∏ ix, t ix ^ exOf Dw la 0 ix, hg, h1, h2,
    fun a b => ?_, fun la f s hs => ?_⟩
  · simp only [exOf_add_zero, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
  · have hTop : ⊤ ≤ z ⁻¹ᵁ (⊤ : (Y₀ X Z).Opens) := fun _ _ => trivial
    have hi' := hopen _ (hj la)
    have v₈ := evR_eq_val_secOf f hO₂ hQ₂ ht
    have v₅ : H0.val z ((common₀ X Z).idx la k) hU hi' (sec₀ X Z _ f) =
        H0.val (B := X.LL (exOf Dw la 0)) (z ≫ inc₀ X Z) k hO₂ hk₂ (secOf X _ f) :=
      H0.val_pull (inc₀ X Z) le_rfl z _ hU hi' hO₂ hk₂ _
    have v₄ := val_restr' (p := str₀ X Z) (le_top : U₀ X Z ≤ ⊤) z _ hTop hU hi' s
    have v₆ : genVal Z f.1 = evR Xo c f.1 (genFr h Z) := rfl
    have v₇ : g (germ ((common₀ X Z).idx la k) y (memTop y) (hj la) s) = H0.val z _ hTop hi' s := by
      rw [H0.val_apply, H0.germ_apply]
      exact h3 _ _ _ _
    rw [v₆, v₈, ← v₅, ← hs, v₄, v₇]

variable {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

/- English proof (translation)
Take `⟨s', hs', e'⟩` from `(hC b).1 ⟨f, hf⟩`. Establish `h` using `(exOf_add_zero (Dw := Dw) a b).symm`. Set `C` to `((commonLL X).addChart h).pull (inc₀ X Z)`. Establish `hm : C.mul s s' ∈ vanBd X Z (a + b)`. Use `(mem_vanBd X Z).2 fun y hy hu => ?_` and prove the remaining obligations.

Take `⟨t, ha, hb, hc⟩` from `C.cover y`. Establish `h1` using `(isUnit_ger_iff _ hc).2 hu`. Rewrite `h1` using `[ger_toSec]`. Establish `h2` using `C.germ_mul s s' t y (memTop y) ha hb hc`. Conclude with `hs' y hy _ hb (isUnit_of_mul_isUnit_right (h2 ▸ h1))`.

Take `⟨m, hm'⟩` from `(hC (a + b)).2 hm`. Set `P : secZ Xo c (exOf Dw (a + b) 0)` to `⟨θ.1 * f, h ▸ AllWt.mul_mem_secZ θ.2 (cusp_le_secZ Z U b hf)⟩`. Establish `e₁ : sec₀ X Z _ P = restr le_top (C.mul s s')` using `(sec₀_mul X Z h θ ⟨f, cusp_le_secZ Z U b hf⟩ P rfl).trans ((congrArg₂ (fun u v => C.mul u v) hs.symm e'.symm).trans (C.restr_mul le_top s s').symm)`. Establish `e₂ : P - ⟨m.1, cusp_le_secZ Z U _ m.2⟩ = 0` using `eq_zero_of_sec₀ X Z (sub_mem (AllWt.mul_mem_suppOn _ hf.2) m.2.2) (by`. Rewrite using `[map_sub, e₁]`.

Conclude with `sub_eq_zero.2 hm'.symm)`. Establish `e₃ : θ.1 * f = m.1` using `congrArg Subtype.val (sub_eq_zero.1 e₂)`. Rewrite using `[e₃]`. Conclude with `m.2`.
-/
theorem mul_mem_cusp (hC : ∀ la, CuspIso X Z U la) {a : AllWt.Weight Dw} (θ : secZ Xo c (exOf Dw a 0))
    (s : H0 (str₀ X Z) (L₀ X Z a) ⊤) (hs : restr le_top s = sec₀ X Z _ θ) (b : AllWt.Weight Dw) {f : Rul Xo c}
    (hf : f ∈ Cusp Z U b) : θ.1 * f ∈ Cusp Z U (a + b) := by
  obtain ⟨s', hs', e'⟩ := (hC b).1 ⟨f, hf⟩
  have h := (exOf_add_zero (Dw := Dw) a b).symm
  let C := ((commonLL X).addChart h).pull (inc₀ X Z)
  have hm : C.mul s s' ∈ vanBd X Z (a + b) := by
    refine (mem_vanBd X Z).2 fun y hy hu => ?_
    obtain ⟨t, ha, hb, hc⟩ := C.cover y
    have h1 := (isUnit_ger_iff _ hc).2 hu
    rw [ger_toSec] at h1
    have h2 := C.germ_mul s s' t y (memTop y) ha hb hc
    exact hs' y hy _ hb (isUnit_of_mul_isUnit_right (h2 ▸ h1))
  obtain ⟨m, hm'⟩ := (hC (a + b)).2 hm
  let P : secZ Xo c (exOf Dw (a + b) 0) := ⟨θ.1 * f, h ▸ AllWt.mul_mem_secZ θ.2 (cusp_le_secZ Z U b hf)⟩
  have e₁ : sec₀ X Z _ P = restr le_top (C.mul s s') :=
    (sec₀_mul X Z h θ ⟨f, cusp_le_secZ Z U b hf⟩ P rfl).trans
      ((congrArg₂ (fun u v => C.mul u v) hs.symm e'.symm).trans (C.restr_mul le_top s s').symm)
  have e₂ : P - ⟨m.1, cusp_le_secZ Z U _ m.2⟩ = 0 :=
    eq_zero_of_sec₀ X Z (sub_mem (AllWt.mul_mem_suppOn _ hf.2) m.2.2) (by
      rw [map_sub, e₁]; exact sub_eq_zero.2 hm'.symm)
  have e₃ : θ.1 * f = m.1 := congrArg Subtype.val (sub_eq_zero.1 e₂)
  rw [e₃]
  exact m.2

/- English proof (translation)
Use `haveI : Smooth (str₀ X Z) := haveI := hV.1`. Use the proof step `SmoothOfRelativeDimension.smooth (FlagTan.dimFlag Dw) (str₀ X Z)`. Use `haveI := hV.2.2`. Use `haveI : IsIntegral (Y₀ X Z) := GlobalTheory.isIntegral_of_smooth_of_geometricallyConnected (str₀ X Z)`. Use `haveI : IsLocallyNoetherian (Y₀ X Z) := LocallyOfFiniteType.isLocallyNoetherian (str₀ X Z)`.

Take `⟨θ, -, hθ⟩` from `exists_suppOn_sec₀_eq _ _ _ _ _ _ _ X Z (exOf Dw a 0) (restr le_top s)`. Establish `hpow : ∀ (n : ℕ) (b : AllWt.Weight Dw), ∀ f ∈ Cusp Z U b, θ.1 ^ n * f ∈ Cusp Z U (n • a + b)`. Introduce `n b f hf`. Proceed by induction on `n with`. Consider the case `zero => simpa using hf`.

Consider the case `succ n ih`. Rewrite using `[pow_succ', mul_assoc, succ_nsmul', add_assoc]`. Conclude with `mul_mem_cusp X Z U hC θ s hθ.symm _ ih`. Establish `hwk : ∀ k : ℕ, (3 * k) • a + (8 * k) • u' = (8 * k) • u` using `fun k => by`. Rewrite using `[mul_comm 3 k, mul_comm 8 k, mul_smul, mul_smul, mul_smul, ← smul_add, hw]`.

Use `⟨8, θ.1 ^ 3, by norm_num, ?_, fun k _ f hf => ?_⟩` and prove the remaining obligations. Take `⟨y, g, j, hj, T, hg, -, -, -, hT⟩` from `exists_centre_genVal X Z hV 1 fun a ha => Valuation.one_apply_of_ne_zero ((map_ne_zero _).2 ha)`. Rewrite using `[map_pow, hT a θ s hθ.symm]`. Use `pow_ne_zero _ (mul_ne_zero (Units.ne_zero _) fun h0 => hs ?_)` and prove the remaining obligations. Establish `h1` using `hg (h0.trans (map_zero g).symm)`.

Rewrite `h1` using `[germ_apply]`. Establish `h2 : s.loc (j a) = 0` using `germ_injective_of_isIntegral _ y _ (h1.trans (map_zero _).symm)`. Use `ext_germ fun y' hy' => ?_` and prove the remaining obligations. Take `⟨i, hi⟩` from `exists_chart (isLB_L₀ X Z a) y'`. Use `⟨i, hi, ?_⟩` and prove the remaining obligations.

Take `⟨η, h₁, h₂⟩` from `nonempty_preirreducible_inter ((L₀ X Z a).U i).isOpen ((L₀ X Z a).U (j a)).isOpen ⟨y', hi⟩ ⟨y, hj a⟩`. Establish `e : germ i η (memTop η) h₁ s = 0`. Rewrite using `[germ_change i (j a) η _ h₁ h₂, germ_apply (j a), h2, map_zero, mul_zero]`. Establish `hl : s.loc i = 0` using `germ_injective_of_isIntegral _ η (memInf (memTop η) h₁) (e.trans (map_zero _).symm)`. Rewrite using `[germ_apply, hl, map_zero, map_zero]`.

Rewrite `hf`, the goal using `[CompHt.nsmul_wtOf, smul_zero]`. Rewrite using `[← pow_mul]`. Use `⟨hwk k ▸ hpow (3 * k) _ f hf, fun ν hν => ?_⟩` and prove the remaining obligations. Take `⟨y, g, j, hj, T, hg, h1, h2, hadd, hT⟩` from `exists_centre_genVal X Z hV ν hν`. Establish `hTn : ∀ (n : ℕ) (b : AllWt.Weight Dw), T (n • b) = T b ^ n` using `fun n b => by`.

Proceed by induction on `n with`. Consider the case `zero`. Use `hadd 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Rewrite using `[zero_smul, pow_zero]`.

Conclude with `left_eq_mul.1 this`. Consider the case `succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]`. Choose the witnesses or unpack the hypotheses as in `⟨w, hw'⟩ : ∃ w : space X Z U u, ν (g (germ (j a) y (memTop y) (hj a) s)) ^ 3 ≤ ν (g (germ (j u) y (memTop y) (hj u) w.1)) ^ 8 := by`. Distinguish the cases in `hy : y ∈ U₀ X Z`. Use `mt (mem_support_baseIdeal _ _ y).2 (hfree y hy) push Not at this` as an intermediate fact.

Take `⟨w, hw, hu⟩` from `this`. Establish `hu'` using `(isUnit_ger_iff _ (hj u)).2 hu`. Rewrite `hu'` using `[ger_toSec]`. Take `⟨v, hv⟩` from `hu'.exists_right_inv`. Use `⟨⟨w, hw⟩, (pow_le_one₀ zero_le' (h1 _)).trans (one_le_pow₀ ?_)⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← map_mul, ← map_mul, hv, map_one, map_one]`. Use `_ ≤ _ := mul_le_of_le_one_right' (h1 v)`. Use `exists_le_of_discrete (fun w : space X Z U u => germ (j u) y (memTop y) (hj u) w.1) _ 3 (by norm_num) (fun μ hμ => ?_) g hg ν h1 h2` and prove the remaining obligations. Take `⟨w, hw, hle⟩` from `hbd y hy μ hμ`.

Conclude with `⟨⟨w, hw⟩, hle _ _ _ _⟩`. Take `⟨s', -, e'⟩` from `(hC ((8 * k) • u')).1 ⟨f, hf⟩`. Use `⟨ofSpace X Z U u w, ?_⟩` and prove the remaining obligations. Establish `e₁ : genPoint Z (cuspOn U Z (wtOf Dw u 0)) (ofSpace X Z U u w) = T u * g (germ (j u) y (memTop y) (hj u) w.1)` using `hT u ⟨_, cusp_le_secZ Z U u (ofSpace X Z U u w).2⟩ w.1 (cuspSec_ofSpace X Z U u w).symm`. Establish `e₂ : genVal Z f = T ((8 * k) • u') * g (germ (j _) y (memTop y) (hj _) s')` using `hT _ ⟨f, cusp_le_secZ Z U _ hf⟩ s' e'`.

Establish `e₃ : (T a : Om Z) ^ (3 * k) * T ((8 * k) • u') = (T u : Om Z) ^ (8 * k)`. Rewrite using `[← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← hTn, ← hTn, ← Units.val_mul, ← hadd, hwk]`. Rewrite using `[e₁, map_mul (genVal Z), map_pow (genVal Z), hT a θ s hθ.symm, e₂, mul_pow, mul_mul_mul_comm, e₃, map_mul, map_mul, map_mul, map_pow, map_pow, mul_pow]`. Use `mul_le_mul_of_nonneg_left ((mul_le_of_le_one_right' (h1 _)).trans ?_) zero_le'` and prove the remaining obligations. Rewrite using `[pow_mul, pow_mul]`.

Conclude with `pow_le_pow_left₀ zero_le' hw' k`.
-/
theorem valMult_of_section (hV : IsVariety₀ X Z) (hC : ∀ la, CuspIso X Z U la) {a u u' : AllWt.Weight Dw}
    (hw : 3 • a + 8 • u' = 8 • u) (hfree : FreeOnOpen X Z U u) (s : H0 (str₀ X Z) (L₀ X Z a) ⊤) (hs : s ≠ 0)
    (hbd : ∀ y ∈ (U₀ X Z : Set (Y₀ X Z))ᶜ, ∀ ν, Centred y ν → ∃ w ∈ space X Z U u,
      ∀ (j : (L₀ X Z a).ι) (hj : y ∈ (L₀ X Z a).U j) (j' : (L₀ X Z u).ι) (hj' : y ∈ (L₀ X Z u).U j'),
        ν (germ j y (memTop y) hj s) ^ 3 ≤ ν (germ j' y (memTop y) hj' w) ^ 8) :
    ValMult U Z (wtOf Dw u 0) (wtOf Dw u' 0) := by
  classical
  haveI : Smooth (str₀ X Z) := haveI := hV.1; SmoothOfRelativeDimension.smooth (FlagTan.dimFlag Dw) (str₀ X Z)
  haveI := hV.2.2
  haveI : IsIntegral (Y₀ X Z) := GlobalTheory.isIntegral_of_smooth_of_geometricallyConnected (str₀ X Z)
  haveI : IsLocallyNoetherian (Y₀ X Z) := LocallyOfFiniteType.isLocallyNoetherian (str₀ X Z)
  obtain ⟨θ, -, hθ⟩ := exists_suppOn_sec₀_eq _ _ _ _ _ _ _ X Z (exOf Dw a 0) (restr le_top s)
  have hpow : ∀ (n : ℕ) (b : AllWt.Weight Dw), ∀ f ∈ Cusp Z U b, θ.1 ^ n * f ∈ Cusp Z U (n • a + b) := by
    intro n b f hf
    induction n with
    | zero => simpa using hf
    | succ n ih =>
      rw [pow_succ', mul_assoc, succ_nsmul', add_assoc]
      exact mul_mem_cusp X Z U hC θ s hθ.symm _ ih
  have hwk : ∀ k : ℕ, (3 * k) • a + (8 * k) • u' = (8 * k) • u := fun k => by
    rw [mul_comm 3 k, mul_comm 8 k, mul_smul, mul_smul, mul_smul, ← smul_add, hw]
  refine ⟨8, θ.1 ^ 3, by norm_num, ?_, fun k _ f hf => ?_⟩
  · obtain ⟨y, g, j, hj, T, hg, -, -, -, hT⟩ := exists_centre_genVal X Z hV 1 fun a ha =>
      Valuation.one_apply_of_ne_zero ((map_ne_zero _).2 ha)
    rw [map_pow, hT a θ s hθ.symm]
    refine pow_ne_zero _ (mul_ne_zero (Units.ne_zero _) fun h0 => hs ?_)
    have h1 := hg (h0.trans (map_zero g).symm)
    rw [germ_apply] at h1
    have h2 : s.loc (j a) = 0 := germ_injective_of_isIntegral _ y _ (h1.trans (map_zero _).symm)
    refine ext_germ fun y' hy' => ?_
    obtain ⟨i, hi⟩ := exists_chart (isLB_L₀ X Z a) y'
    refine ⟨i, hi, ?_⟩
    obtain ⟨η, h₁, h₂⟩ := nonempty_preirreducible_inter ((L₀ X Z a).U i).isOpen ((L₀ X Z a).U (j a)).isOpen ⟨y', hi⟩
      ⟨y, hj a⟩
    have e : germ i η (memTop η) h₁ s = 0 := by
      rw [germ_change i (j a) η _ h₁ h₂, germ_apply (j a), h2, map_zero, mul_zero]
    have hl : s.loc i = 0 := germ_injective_of_isIntegral _ η (memInf (memTop η) h₁) (e.trans (map_zero _).symm)
    rw [germ_apply, hl, map_zero, map_zero]
  · rw [CompHt.nsmul_wtOf, smul_zero] at hf ⊢
    rw [← pow_mul]
    refine ⟨hwk k ▸ hpow (3 * k) _ f hf, fun ν hν => ?_⟩
    obtain ⟨y, g, j, hj, T, hg, h1, h2, hadd, hT⟩ := exists_centre_genVal X Z hV ν hν
    have hTn : ∀ (n : ℕ) (b : AllWt.Weight Dw), T (n • b) = T b ^ n := fun n b => by
      induction n with
      | zero =>
        have := hadd 0 0
        rw [add_zero] at this
        rw [zero_smul, pow_zero]
        exact left_eq_mul.1 this
      | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
    obtain ⟨w, hw'⟩ : ∃ w : space X Z U u, ν (g (germ (j a) y (memTop y) (hj a) s)) ^ 3 ≤
        ν (g (germ (j u) y (memTop y) (hj u) w.1)) ^ 8 := by
      by_cases hy : y ∈ U₀ X Z
      · have := mt (mem_support_baseIdeal _ _ y).2 (hfree y hy)
        push Not at this
        obtain ⟨w, hw, hu⟩ := this
        have hu' := (isUnit_ger_iff _ (hj u)).2 hu
        rw [ger_toSec] at hu'
        obtain ⟨v, hv⟩ := hu'.exists_right_inv
        refine ⟨⟨w, hw⟩, (pow_le_one₀ zero_le' (h1 _)).trans (one_le_pow₀ ?_)⟩
        calc (1 : ℝ≥0) = ν (g (germ (j u) y (memTop y) (hj u) w)) * ν (g v) := by
              rw [← map_mul, ← map_mul, hv, map_one, map_one]
          _ ≤ _ := mul_le_of_le_one_right' (h1 v)
      · refine exists_le_of_discrete (fun w : space X Z U u => germ (j u) y (memTop y) (hj u) w.1) _ 3 (by norm_num)
          (fun μ hμ => ?_) g hg ν h1 h2
        obtain ⟨w, hw, hle⟩ := hbd y hy μ hμ
        exact ⟨⟨w, hw⟩, hle _ _ _ _⟩
    obtain ⟨s', -, e'⟩ := (hC ((8 * k) • u')).1 ⟨f, hf⟩
    refine ⟨ofSpace X Z U u w, ?_⟩
    have e₁ : genPoint Z (cuspOn U Z (wtOf Dw u 0)) (ofSpace X Z U u w) = T u * g (germ (j u) y (memTop y) (hj u) w.1) :=
      hT u ⟨_, cusp_le_secZ Z U u (ofSpace X Z U u w).2⟩ w.1 (cuspSec_ofSpace X Z U u w).symm
    have e₂ : genVal Z f = T ((8 * k) • u') * g (germ (j _) y (memTop y) (hj _) s') :=
      hT _ ⟨f, cusp_le_secZ Z U _ hf⟩ s' e'
    have e₃ : (T a : Om Z) ^ (3 * k) * T ((8 * k) • u') = (T u : Om Z) ^ (8 * k) := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← hTn, ← hTn, ← Units.val_mul, ← hadd, hwk]
    rw [e₁, map_mul (genVal Z), map_pow (genVal Z), hT a θ s hθ.symm, e₂, mul_pow, mul_mul_mul_comm, e₃, map_mul, map_mul,
      map_mul, map_pow, map_pow, mul_pow]
    refine mul_le_mul_of_nonneg_left ((mul_le_of_le_one_right' (h1 _)).trans ?_) zero_le'
    rw [pow_mul, pow_mul]
    exact pow_le_pow_left₀ zero_le' hw' k

end Component

open TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechPic GlobalTheory.Vanishing in
set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `hP hGD hQ hS hT hL h2 h3 h4`. Use `((((GlobalTheory.T.exists_nonzero_section_weight_bound hP h2 h3 h4).and (GlobalTheory.T.centred_point_phi_positive_weights hP h2 h3 h4)).and (GlobalTheory.T.centred_point_phi_positive hP h2 h3 h4)).and wtBig_run).imp fun Fm CH _ h => ?_` and prove the remaining obligations. Take `⟨⟨⟨⟨C, hC, x0, hx⟩, ⟨C', hC', x1, hx1⟩⟩, ⟨C'', hC'', x2, hx2⟩⟩, ⟨C₃, hC₃, x3, hx3⟩⟩` from `h`. Use `⟨C, hC, max (max x0 x1) (max x2 x3), fun x hx' hle ι p hp i hi Y hY Z => ?_⟩` and prove the remaining obligations. Simplify using `only [max_le_iff] at hle`.

Establish `hB` using `hx3 x hx' hle.2.2 ι p hp i hi`. Establish `hP'` using `GlobalTheory.T.stronger_published_hypotheses_imply hP`. Take `⟨TF⟩` from `@GlobalTheory.CompHS.TorFlagEx.nonempty_torFlag hP' _ _ _ _ _ _ _ Y.d.Xo₂ Y.d.c₂ hB.one_le`. Take `⟨θ, hθ, -, hst⟩` from `hx x hx' hle.1.1 ι p hp i hi Y hY Z TF`. Establish `hJ` using `hx1 x hx' hle.1.2 ι p hp i hi Y hY Z TF _ (Or.inl rfl)`.

Establish `hD` using `hx2 x hx' hle.2.1 ι p hp i hi Y hY Z TF`. Establish `hf : 2 < Module.finrank ℚ (Fm.D x ι).host.E / 2`. Establish `h3 : Module.finrank ℚ (Fm.D x ι).host.E = 4 * (Fm.D x ι).R.ord` using `(Fm.D x ι).host.finrank_cmField`. Establish `h : 4 ≤ (Fm.D x ι).R.ord` using `(Fm.D x ι).host.four_le_n'`. Use linear arithmetic over natural numbers and integers.

Establish `hCI : ∀ la, CuspIso TF.X Z Y.U la` using `fun la => ⟨GlobalTheory.T.cuspForms_extend_vanish_compactifiedFlagSpace _ _ _ Y _ _ hY.1 hf Z TF _, vanBd_le_space _ _ _ Y _ _ hY.1 hf Z TF _⟩`. Establish `hfree` using `GlobalTheory.T.toroidal_integral_weight_section hP' hGD hQ hP.q15 hP.q16 hS hT.toroidalChartsForFan hL _ _ _ _ _ _ TF Z _ Y.U hY.1.geo hB.one_le _ (gaps_of_wtBig _ _ _ _ hB _ List.mem_cons_self).2 (hCI _)`. Use `valMult_of_section TF.X Z Y.U (GlobalTheory.VarFlag.isVariety₀_flag _ _ _ _ _ _ TF Z hY.1.geo) hCI ?_ hfree θ hθ fun y hy ν hν => ?_` and prove the remaining obligations. Rewrite using `[CompHt.uPrime] module`. Take `⟨φ, hφ, hPh⟩` from `hD y hy ν hν`.

Take `⟨w, hw, hwb⟩` from `hJ y hy ν hν φ hPh`. Use `⟨w, hw, fun j hj j' hj' => ?_⟩` and prove the remaining obligations. Take `⟨hw0, hwm⟩` from `hwb j' hj'`. Take `⟨zw, hzw⟩` from `WithZero.ne_zero_iff_exists.1 hw0`. Establish `ew : ν (H0.germ j' y (memTop y) hj' w) = ((Multiplicative.ofAdd (-(-Multiplicative.toAdd zw)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))`.

Rewrite using `[neg_neg, ofAdd_toAdd]`. Conclude with `hzw.symm`. Establish `bw` using `hwm _ ew`. Distinguish the cases in `h0 : ν (H0.germ j y (memTop y) hj θ) = 0`. Rewrite using `[h0, zero_pow three_ne_zero]`.

Conclude with `zero_le'`. Take `⟨zt, hzt⟩` from `WithZero.ne_zero_iff_exists.1 h0`. Establish `et : ν (H0.germ j y (memTop y) hj θ) = ((Multiplicative.ofAdd (-(-Multiplicative.toAdd zt)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))`. Rewrite using `[neg_neg, ofAdd_toAdd]`. Conclude with `hzt.symm`.

Establish `bt` using `hst y hy ν hν φ hPh j hj _ et`. Establish `hle' : (3 * Multiplicative.toAdd zt : ℝ) ≤ (8 * Multiplicative.toAdd zw : ℝ)`. Move the coercions through the operations in `at bw bt ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hle'' : 3 * Multiplicative.toAdd zt ≤ 8 * Multiplicative.toAdd zw` using `by exact_mod_cast hle'`.

Rewrite using `[← hzt, ← hzw, ← WithZero.coe_pow, ← WithZero.coe_pow, WithZero.coe_le_coe, ← Multiplicative.toAdd_le, toAdd_pow, toAdd_pow]`. Simplify using `using hle''`.
-/
theorem valMult_run : Hypotheses2 → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ Z, ValMult Y.U Z (wtOf (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ 0) (wtOf (dat p i) (CompHt.uPrime (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁) 0) := by
  intro hP hGD hQ hS hT hL h2 h3 h4
  refine ((((GlobalTheory.T.exists_nonzero_section_weight_bound hP h2 h3 h4).and (GlobalTheory.T.centred_point_phi_positive_weights hP h2 h3 h4)).and (GlobalTheory.T.centred_point_phi_positive hP h2 h3 h4)).and wtBig_run).imp
    fun Fm CH _ h => ?_
  obtain ⟨⟨⟨⟨C, hC, x0, hx⟩, ⟨C', hC', x1, hx1⟩⟩, ⟨C'', hC'', x2, hx2⟩⟩, ⟨C₃, hC₃, x3, hx3⟩⟩ := h
  refine ⟨C, hC, max (max x0 x1) (max x2 x3), fun x hx' hle ι p hp i hi Y hY Z => ?_⟩
  simp only [max_le_iff] at hle
  have hB := hx3 x hx' hle.2.2 ι p hp i hi
  have hP' := GlobalTheory.T.stronger_published_hypotheses_imply hP
  obtain ⟨TF⟩ := @GlobalTheory.CompHS.TorFlagEx.nonempty_torFlag hP' _ _ _ _ _ _ _ Y.d.Xo₂ Y.d.c₂ hB.one_le
  obtain ⟨θ, hθ, -, hst⟩ := hx x hx' hle.1.1 ι p hp i hi Y hY Z TF
  have hJ := hx1 x hx' hle.1.2 ι p hp i hi Y hY Z TF _ (Or.inl rfl)
  have hD := hx2 x hx' hle.2.1 ι p hp i hi Y hY Z TF
  have hf : 2 < Module.finrank ℚ (Fm.D x ι).host.E / 2 := by
    have h3 : Module.finrank ℚ (Fm.D x ι).host.E = 4 * (Fm.D x ι).R.ord :=
      (Fm.D x ι).host.finrank_cmField
    have h : 4 ≤ (Fm.D x ι).R.ord := (Fm.D x ι).host.four_le_n'
    omega
  have hCI : ∀ la, CuspIso TF.X Z Y.U la := fun la =>
    ⟨GlobalTheory.T.cuspForms_extend_vanish_compactifiedFlagSpace _ _ _ Y _ _ hY.1 hf Z TF _, vanBd_le_space _ _ _ Y _ _ hY.1 hf Z TF _⟩
  have hfree := GlobalTheory.T.toroidal_integral_weight_section hP' hGD hQ hP.q15 hP.q16 hS hT.toroidalChartsForFan hL _ _ _ _ _ _ TF Z _ Y.U hY.1.geo
    hB.one_le _ (gaps_of_wtBig _ _ _ _ hB _ List.mem_cons_self).2 (hCI _)
  refine valMult_of_section TF.X Z Y.U (GlobalTheory.VarFlag.isVariety₀_flag _ _ _ _ _ _ TF Z hY.1.geo) hCI ?_ hfree θ hθ
    fun y hy ν hν => ?_
  · rw [CompHt.uPrime]
    module
  obtain ⟨φ, hφ, hPh⟩ := hD y hy ν hν
  obtain ⟨w, hw, hwb⟩ := hJ y hy ν hν φ hPh
  refine ⟨w, hw, fun j hj j' hj' => ?_⟩
  obtain ⟨hw0, hwm⟩ := hwb j' hj'
  obtain ⟨zw, hzw⟩ := WithZero.ne_zero_iff_exists.1 hw0
  have ew : ν (H0.germ j' y (memTop y) hj' w) =
      ((Multiplicative.ofAdd (-(-Multiplicative.toAdd zw)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [neg_neg, ofAdd_toAdd]; exact hzw.symm
  have bw := hwm _ ew
  by_cases h0 : ν (H0.germ j y (memTop y) hj θ) = 0
  · rw [h0, zero_pow three_ne_zero]
    exact zero_le'
  · obtain ⟨zt, hzt⟩ := WithZero.ne_zero_iff_exists.1 h0
    have et : ν (H0.germ j y (memTop y) hj θ) =
        ((Multiplicative.ofAdd (-(-Multiplicative.toAdd zt)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
      rw [neg_neg, ofAdd_toAdd]; exact hzt.symm
    have bt := hst y hy ν hν φ hPh j hj _ et
    have hle' : (3 * Multiplicative.toAdd zt : ℝ) ≤ (8 * Multiplicative.toAdd zw : ℝ) := by
      push_cast at bw bt ⊢
      linarith
    have hle'' : 3 * Multiplicative.toAdd zt ≤ 8 * Multiplicative.toAdd zw := by exact_mod_cast hle'
    rw [← hzt, ← hzw, ← WithZero.coe_pow, ← WithZero.coe_pow, WithZero.coe_le_coe, ← Multiplicative.toAdd_le,
      toAdd_pow, toAdd_pow]
    simpa using hle''

end GlobalTheory.ValMultRun
