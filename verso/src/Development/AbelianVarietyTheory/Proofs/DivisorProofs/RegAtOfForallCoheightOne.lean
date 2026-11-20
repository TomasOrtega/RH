import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CodimOneGenerizationStalk
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.MemRangeOfForallHeightOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WeilCartier

open GlobalTheory.Cartier

section Normal

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]

/- English proof (translation)
Use `haveI := GlobalTheory.IsNormalScheme.isDiscreteValuationRing_stalk hz`. Establish `: Ring.KrullDimLE 1 (X.presheaf.stalk z)` using `krullDimLE_of_coheight_le hz.le`. Establish `e` using `(Scheme.ord_eq_iff hz hf).1 h`. Establish `hm : f ∈ MonoidHom.mker (Ring.ordFrac (X.presheaf.stalk z) (K` using `X.functionField)) := by`. Express the relevant statement in the definitionally equal form `Ring.ordFrac (X.presheaf.stalk z) f = 1`.

Conclude with `e`. Rewrite `hm` using `[Ring.mker_ordFrac_eq_isUnitSubmonoid]`. Take `⟨a, ha, rfl⟩` from `hm`. Conclude with `⟨a, ha, rfl⟩`.
-/
theorem unitAt_of_ord_eq_zero {z : X} (hz : Order.coheight z = 1) {f : X.functionField}
    (hf : f ≠ 0) (h : Scheme.ord f z = 0) : UnitAt z f := by
  haveI := GlobalTheory.IsNormalScheme.isDiscreteValuationRing_stalk hz
  have : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  have e := (Scheme.ord_eq_iff hz hf).1 h
  have hm : f ∈ MonoidHom.mker (Ring.ordFrac (X.presheaf.stalk z) (K := X.functionField)) := by
    change Ring.ordFrac (X.presheaf.stalk z) f = 1
    exact e
  rw [Ring.mker_ordFrac_eq_isUnitSubmonoid] at hm
  obtain ⟨a, ha, rfl⟩ := hm
  exact ⟨a, ha, rfl⟩

/- English proof (translation)
Take `⟨a, ha⟩` from `ReciprocityTheory.ChartRestriction.G.Out.KrullAlg.mem_range_of_forall_height_one (A := X.presheaf.stalk x) (K := X.functionField) f (fun P hP h1 => by`. Take `⟨e, he⟩` from `GlobalTheory.LocalRingGeneralisation.stalk_fromSpecStalk_equiv X x P`. Establish `hs : X.fromSpecStalk x (⟨P, inferInstance⟩ : PrimeSpectrum (X.presheaf.stalk x)) ⤳ x`. Establish `: X.fromSpecStalk x (⟨P, inferInstance⟩ : PrimeSpectrum (X.presheaf.stalk x)) ∈ Set.range (X.fromSpecStalk x)` using `⟨_, rfl⟩`. Rewrite `this` using `[Scheme.range_fromSpecStalk]`. Then use the resulting hypothesis.

Generalize the expression as in `X.fromSpecStalk x (⟨P, inferInstance⟩ : PrimeSpectrum (X.presheaf.stalk x)) = z at e he hs`. Establish `hz1 : Order.coheight z = 1`. Establish `h2` using `ringKrullDim_eq_of_ringEquiv e`. Rewrite `h2` using `[IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P), h1, ringKrullDim_stalk_eq_coheight]`. Conclude with `h2` after adjusting the coercions.

Take `⟨b, hb⟩` from `h z hs hz1`. Establish `key : ∀ c : X.presheaf.stalk x, algebraMap (X.presheaf.stalk z) X.functionField (e.symm (algebraMap _ (Localization.AtPrime P) c)) = algebraMap _ X.functionField c`. Introduce `c`. Take `⟨U, hxU, s, rfl⟩` from `X.presheaf.exists_germ_eq c`. Establish `hzU : z ∈ U` using `hs.mem_open U.isOpen hxU`.

Establish `h3` using `he U hzU hxU s`. Rewrite using `[← h3, e.symm_apply_apply]`. Conclude with `(algebraMap_germ hzU s).trans (algebraMap_germ hxU s).symm`. Take `⟨⟨c, t⟩, hct⟩` from `IsLocalization.mk'_surjective P.primeCompl (e b)`. Express the relevant statement in the definitionally equal form `IsLocalization.mk' (Localization.AtPrime P) c t = e b at hct`.

Use `⟨t, t.2, c, ?_⟩` and prove the remaining obligations. Establish `hspec` using `IsLocalization.mk'_spec (Localization.AtPrime P) c t`. Rewrite `hspec` using `[hct]`. Use `congrArg (fun w => algebraMap (X.presheaf.stalk z) X.functionField (e.symm w)) hspec` as an intermediate fact. Simplify using `only [map_mul, e.symm_apply_apply] at this`.

Rewrite `this` using `[key, key, hb]`. Rewrite using `[← this, mul_comm])`. Conclude with `⟨a, ha⟩`.
-/
theorem regAt_of_forall_coheight_one (x : X) (f : X.functionField)
    (h : ∀ z : X, z ⤳ x → Order.coheight z = 1 → RegAt z f) : RegAt x f := by
  obtain ⟨a, ha⟩ := ReciprocityTheory.ChartRestriction.G.Out.KrullAlg.mem_range_of_forall_height_one
    (A := X.presheaf.stalk x) (K := X.functionField) f (fun P hP h1 => by
      obtain ⟨e, he⟩ := GlobalTheory.LocalRingGeneralisation.stalk_fromSpecStalk_equiv X x P
      have hs : X.fromSpecStalk x (⟨P, inferInstance⟩ : PrimeSpectrum (X.presheaf.stalk x)) ⤳ x := by
        have : X.fromSpecStalk x (⟨P, inferInstance⟩ : PrimeSpectrum (X.presheaf.stalk x)) ∈
            Set.range (X.fromSpecStalk x) := ⟨_, rfl⟩
        rwa [Scheme.range_fromSpecStalk] at this
      generalize X.fromSpecStalk x (⟨P, inferInstance⟩ : PrimeSpectrum (X.presheaf.stalk x)) = z
        at e he hs
      have hz1 : Order.coheight z = 1 := by
        have h2 := ringKrullDim_eq_of_ringEquiv e
        rw [IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P), h1, ringKrullDim_stalk_eq_coheight] at h2
        exact_mod_cast h2
      obtain ⟨b, hb⟩ := h z hs hz1
      have key : ∀ c : X.presheaf.stalk x, algebraMap (X.presheaf.stalk z) X.functionField
          (e.symm (algebraMap _ (Localization.AtPrime P) c)) = algebraMap _ X.functionField c := by
        intro c
        obtain ⟨U, hxU, s, rfl⟩ := X.presheaf.exists_germ_eq c
        have hzU : z ∈ U := hs.mem_open U.isOpen hxU
        have h3 := he U hzU hxU s
        rw [← h3, e.symm_apply_apply]
        exact (algebraMap_germ hzU s).trans (algebraMap_germ hxU s).symm
      obtain ⟨⟨c, t⟩, hct⟩ := IsLocalization.mk'_surjective P.primeCompl (e b)
      change IsLocalization.mk' (Localization.AtPrime P) c t = e b at hct
      refine ⟨t, t.2, c, ?_⟩
      have hspec := IsLocalization.mk'_spec (Localization.AtPrime P) c t
      rw [hct] at hspec
      have := congrArg (fun w => algebraMap (X.presheaf.stalk z) X.functionField (e.symm w)) hspec
      simp only [map_mul, e.symm_apply_apply] at this
      rw [key, key, hb] at this
      rw [← this, mul_comm])
  exact ⟨a, ha⟩

end Normal

/- English proof (translation)
Introduce `X _ _ hN D g hD`. Use `haveI := GlobalTheory.IsNormalScheme.of_pred hN`. Use `CartierDiv.ext_of_isEqn fun x => ⟨g, ?_, CartierDiv.isEqn_principal g x⟩` and prove the remaining obligations. Take `⟨h, hh⟩` from `D.exists_isEqn x`. Take `⟨V, hxV, hV⟩` from `hh.exists_nhds`.

Establish `hne : (g : X.functionField) / h ≠ 0` using `div_ne_zero g.ne_zero h.ne_zero`. Establish `hu : ∀ z : X, z ⤳ x → Order.coheight z = 1 → UnitAt z ((g : X.functionField) / h)`. Introduce `z hs hz`. Establish `hzV : z ∈ V` using `hs.mem_open V.isOpen hxV`. Establish `e1` using `(hV z hzV).mult_eq`.

Rewrite `e1` using `[hD z]`. Use `unitAt_of_ord_eq_zero hz hne ?_` and prove the remaining obligations. Establish `e2` using `Scheme.ord_mul (x := z) hne h.ne_zero`. Rewrite `e2` using `[div_mul_cancel₀ _ h.ne_zero]`. Use linear arithmetic over natural numbers and integers.

Use `hh.iff_unitAt.2 ((unitAt_iff hne).2 ⟨?_, ?_⟩)` and prove the remaining obligations. Conclude with `regAt_of_forall_coheight_one x _ fun z hs hz => (hu z hs hz).regAt`. Conclude with `regAt_of_forall_coheight_one x _ fun z hs hz => (hu z hs hz).inv.regAt`.
-/
theorem eq_principal_of_mult_eq : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X →
    ∀ (D : GlobalTheory.Cartier.CartierDiv X) (g : X.functionFieldˣ), (∀ z, D.mult z = Scheme.ord (g : X.functionField) z) →
      D = GlobalTheory.Cartier.CartierDiv.principal g := by
  intro X _ _ hN D g hD
  haveI := GlobalTheory.IsNormalScheme.of_pred hN
  refine CartierDiv.ext_of_isEqn fun x => ⟨g, ?_, CartierDiv.isEqn_principal g x⟩
  obtain ⟨h, hh⟩ := D.exists_isEqn x
  obtain ⟨V, hxV, hV⟩ := hh.exists_nhds
  have hne : (g : X.functionField) / h ≠ 0 := div_ne_zero g.ne_zero h.ne_zero
  have hu : ∀ z : X, z ⤳ x → Order.coheight z = 1 → UnitAt z ((g : X.functionField) / h) := by
    intro z hs hz
    have hzV : z ∈ V := hs.mem_open V.isOpen hxV
    have e1 := (hV z hzV).mult_eq
    rw [hD z] at e1
    refine unitAt_of_ord_eq_zero hz hne ?_
    have e2 := Scheme.ord_mul (x := z) hne h.ne_zero
    rw [div_mul_cancel₀ _ h.ne_zero] at e2
    omega
  refine hh.iff_unitAt.2 ((unitAt_iff hne).2 ⟨?_, ?_⟩)
  · exact regAt_of_forall_coheight_one x _ fun z hs hz => (hu z hs hz).regAt
  · exact regAt_of_forall_coheight_one x _ fun z hs hz => (hu z hs hz).inv.regAt

end GlobalTheory.WeilCartier
