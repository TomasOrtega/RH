import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrdegResidueFieldOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfIsEtaleCompletion
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularSmooth
import ReciprocityTheory.AnalyticForms.RegularLocalRings.WChartsC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncAtOfStalkIdEqSpanProdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictNormalCrossingsDescentEtaleCompletionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryBranchesDistinctPrimesToricChartStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UChartSmooth

/- English proof (translation)
Use `letI : Algebra F (X.residueField x) := (Spec.preimage (X.fromSpecResidueField x ≫ f)).hom.toAlgebra`. Use `isClosed_singleton_iff_isClosedImmersion.mp hx` as an intermediate fact. Establish `h : LocallyOfFiniteType (X.fromSpecResidueField x ≫ f)` using `inferInstance`. Rewrite `h` using `[← Spec.map_preimage (X.fromSpecResidueField x ≫ f), HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]`. Establish `: Algebra.FiniteType F (X.residueField x)` using `RingHom.finiteType_algebraMap.mp h`.

Establish `: Module.Finite F (X.residueField x)` using `finite_of_finite_type_of_isJacobsonRing F _`. Establish `: Algebra.IsAlgebraic F (X.residueField x)` using `Algebra.IsAlgebraic.of_finite F _`. Conclude with `trdeg_eq_zero`.
-/
theorem trdeg_residueField_eq_zero {F : Type} [Field F] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of F))
    [LocallyOfFiniteType f] (x : X) (hx : IsClosed ({x} : Set X)) :
    letI : Algebra F (X.residueField x) := (Spec.preimage (X.fromSpecResidueField x ≫ f)).hom.toAlgebra
    Algebra.trdeg F (X.residueField x) = 0 := by
  letI : Algebra F (X.residueField x) := (Spec.preimage (X.fromSpecResidueField x ≫ f)).hom.toAlgebra
  have := isClosed_singleton_iff_isClosedImmersion.mp hx
  have h : LocallyOfFiniteType (X.fromSpecResidueField x ≫ f) := inferInstance
  rw [← Spec.map_preimage (X.fromSpecResidueField x ≫ f), HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h
  have : Algebra.FiniteType F (X.residueField x) := RingHom.finiteType_algebraMap.mp h
  have : Module.Finite F (X.residueField x) := finite_of_finite_type_of_isJacobsonRing F _
  have : Algebra.IsAlgebraic F (X.residueField x) := Algebra.IsAlgebraic.of_finite F _
  exact trdeg_eq_zero

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {φ : InvFun (𝓞 E)} {Z : Scheme.{0}} {zs : Z ⟶ Sp c.F} {i : Xo.XF c ⟶ Z} {OZ : LB Z}
  {N d : ℕ} {J : Z.IdealSheafData} {S : Scheme.{0}} {π : S ⟶ Z} {j : Xo.XF c ⟶ S} {BD : EffCartierData S}

/- English proof (translation)
Take `⟨-, -, -, -, ⟨-, hproj, -⟩, -⟩` from `h`. Take `⟨M, i', hi', hcomp⟩` from `hproj`. Use `haveI := hi'`. Use `haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str c.F M`. Rewrite using `[← hcomp]`.

Use `infer_instance`.
-/
theorem locallyOfFiniteType (h : GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD) : LocallyOfFiniteType (π ≫ zs) := by
  obtain ⟨-, -, -, -, ⟨-, hproj, -⟩, -⟩ := h
  obtain ⟨M, i', hi', hcomp⟩ := hproj
  haveI := hi'
  haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str c.F M
  rw [← hcomp]
  infer_instance

/- English proof (translation)
Take `⟨⟨-, -, -, -, hizs, -⟩, -, -, -, ⟨-, -, -, -, hji, -⟩, -⟩` from `h`. Rewrite using `[← Category.assoc, hji, hizs]`. Conclude with `Formalism.L2.Pj.smoothOfRelativeDimension_strK Xo c`.
-/
theorem smooth_j (h : GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD) :
    SmoothOfRelativeDimension Dw.dim (j ≫ π ≫ zs) := by
  obtain ⟨⟨-, -, -, -, hizs, -⟩, -, -, -, ⟨-, -, -, -, hji, -⟩, -⟩ := h
  rw [← Category.assoc, hji, hizs]
  exact Formalism.L2.Pj.smoothOfRelativeDimension_strK Xo c

/- English proof (translation)
Use `haveI := locallyOfFiniteType h`. Use `haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ zs)`. Distinguish the cases in `hx : x ∈ Set.range j`. Take `⟨z, rfl⟩` from `hx haveI := smooth_j h haveI : Smooth (j ≫ π ≫ zs) := SmoothOfRelativeDimension.smooth Dw.dim _ haveI := GroundTheory.Arith.SchemeCoh.isRegularLocalRing_stalk_of_smooth_field (j ≫ π ≫ zs) z`. Conclude with `IsRegularLocalRing.of_ringEquiv (asIso (j.stalkMap z)).commRingCatIsoToRingEquiv.symm`.

Take `⟨k, _, m, e, C, ξ, a, -, -, rfl, hE, -⟩` from `hU x hx haveI : IsRegularLocalRing (ChartRing k m e) := GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries k (Fin m ⊕ Fin e)`. Conclude with `(GlobalTheory.RegSmooth.isRegularLocalRing_of_isEtaleCompletion _ hE).1`.
-/
theorem isRegularLocalRing_stalk [IsOpenImmersion j] (h : GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD)
    (hU : ∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) (x : S) : IsRegularLocalRing (S.presheaf.stalk x) := by
  haveI := locallyOfFiniteType h
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ zs)
  by_cases hx : x ∈ Set.range j
  · obtain ⟨z, rfl⟩ := hx
    haveI := smooth_j h
    haveI : Smooth (j ≫ π ≫ zs) := SmoothOfRelativeDimension.smooth Dw.dim _
    haveI := GroundTheory.Arith.SchemeCoh.isRegularLocalRing_stalk_of_smooth_field (j ≫ π ≫ zs) z
    exact IsRegularLocalRing.of_ringEquiv (asIso (j.stalkMap z)).commRingCatIsoToRingEquiv.symm
  · obtain ⟨k, _, m, e, C, ξ, a, -, -, rfl, hE, -⟩ := hU x hx
    haveI : IsRegularLocalRing (ChartRing k m e) := GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries k (Fin m ⊕ Fin e)
    exact (GlobalTheory.RegSmooth.isRegularLocalRing_of_isEtaleCompletion _ hE).1

/- English proof (translation)
Use `haveI := locallyOfFiniteType h`. Use `GlobalTheory.RegSmooth.smoothOfRelativeDimension_of_isRegularLocalRing (π ≫ zs) Dw.dim fun x hx => ⟨isRegularLocalRing_stalk h hU x, ?_⟩` and prove the remaining obligations. Take `⟨a, b, ha, hb, hab⟩` from `stalk_dim_add_trdeg_of_uPoinOnX h x`. Establish `h0` using `trdeg_residueField_eq_zero (π ≫ zs) x hx`. Establish `hb0 : b = 0`.

Use `hb.symm.trans h0` as an intermediate fact. Conclude with `this` after adjusting the coercions. Rewrite using `[ha, ← hab, hb0, add_zero]`.
-/
theorem smooth [IsOpenImmersion j] (h : GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD)
    (hU : ∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) : SmoothOfRelativeDimension Dw.dim (π ≫ zs) := by
  haveI := locallyOfFiniteType h
  refine GlobalTheory.RegSmooth.smoothOfRelativeDimension_of_isRegularLocalRing (π ≫ zs) Dw.dim fun x hx => ⟨isRegularLocalRing_stalk h hU x, ?_⟩
  obtain ⟨a, b, ha, hb, hab⟩ := stalk_dim_add_trdeg_of_uPoinOnX h x
  have h0 := trdeg_residueField_eq_zero (π ≫ zs) x hx
  have hb0 : b = 0 := by
    have := hb.symm.trans h0
    exact_mod_cast this
  rw [ha, ← hab, hb0, add_zero]

end GlobalTheory.UChartSmooth

namespace GlobalTheory.UChartSmooth

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c φ hpq hfan hno Z zs i OZ N d J S π j _ BD h hsep hU`. Use `⟨smooth h hU, ?_⟩` and prove the remaining obligations. Use `haveI := locallyOfFiniteType h`. Use `haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ zs)`. Introduce `x`.

Distinguish the cases in `hx : x ∈ Set.range j`. Use `sncAt_of_not_mem _ x ?_ (isRegularLocalRing_stalk h hU x)` and prove the remaining obligations. Introduce `hc`. Conclude with `hc hx`. Take `⟨k, _, m, e, C, ξ, a, hT, hy, rfl, hE, hid, hrange, -⟩` from `hU x hx`.

Establish `hs'` using `GlobalTheory.T.boundaryBranches_distinct_primes_toricChart Xo c φ hpq hfan hno zs i OZ N d J π j BD h hsep hU k m e C ξ hT hy hx hE hid hrange`. Take `⟨hm, hs, -⟩` from `hT`. Establish `hprod : ∏ i, C.s i = ∏ i : Fin m, bdParam k m e i` using `Fintype.prod_equiv (finCongr hm) (fun i => C.s i) (fun i => bdParam k m e i) (fun i => by rw [hs i]; rfl)`. Rewrite `hid` using `[hprod]`. Take `⟨n, r, T, hr, hD⟩` from `GlobalTheory.T.strictNormalCrossings_descent_etale_completion _ k m e _ _ hE hid hs'`.

Conclude with `GlobalTheory.T.sncAt_of_stalkId_eq_span_prod_of_isRegularLocalRing S _ _ (isRegularLocalRing_stalk h hU _) n r T hr hD`.
-/
theorem smooth_and_snc : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → SmoothOfRelativeDimension Dw.dim (π ≫ zs) ∧ FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal j.opensRange.compl) := by
  intro E _ _ _ H Dw l Xo c φ hpq hfan hno Z zs i OZ N d J S π j _ BD h hsep hU
  refine ⟨smooth h hU, ?_⟩
  haveI := locallyOfFiniteType h
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ zs)
  intro x
  by_cases hx : x ∈ Set.range j
  · refine sncAt_of_not_mem _ x ?_ (isRegularLocalRing_stalk h hU x)
    intro hc
    exact hc hx
  · obtain ⟨k, _, m, e, C, ξ, a, hT, hy, rfl, hE, hid, hrange, -⟩ := hU x hx
    have hs' := GlobalTheory.T.boundaryBranches_distinct_primes_toricChart Xo c φ hpq hfan hno zs i OZ N d J π j BD h hsep hU k m e C ξ hT hy hx hE hid hrange
    obtain ⟨hm, hs, -⟩ := hT
    have hprod : ∏ i, C.s i = ∏ i : Fin m, bdParam k m e i :=
      Fintype.prod_equiv (finCongr hm) (fun i => C.s i) (fun i => bdParam k m e i) (fun i => by rw [hs i]; rfl)
    rw [hprod] at hid
    obtain ⟨n, r, T, hr, hD⟩ := GlobalTheory.T.strictNormalCrossings_descent_etale_completion _ k m e _ _ hE hid hs'
    exact GlobalTheory.T.sncAt_of_stalkId_eq_span_prod_of_isRegularLocalRing S _ _ (isRegularLocalRing_stalk h hU _) n r T hr hD
end GlobalTheory.UChartSmooth
