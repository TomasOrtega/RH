import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegralIndicatorCharOfTrivial
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CharEqOneOfNear
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SelfDualMap
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsLocalApproximateIdentity
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsFiniteAdeleHaarNormalized

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.ProdM

section FoundMeas
open GroundTheory.Global
attribute [local instance 100000] GroundTheory.Global.measurableSpace_adeleRing GroundTheory.Global.measurableSpace_infiniteAdeleRing

variable (F : Type) [Field F] [NumberField F]

abbrev ratA : AddSubgroup (AF F) := (algebraMap F (AF F)).toAddMonoidHom.range

/- English proof (translation)
Use `IsAddFundamentalDomain.mk' (measurableSet_fundamentalSet F).nullMeasurableSet fun x ↦ ?_` and prove the remaining obligations. Take `⟨k, hk, huniq⟩` from `existsUnique_sub_mem_fundamentalSet F x`. Use `⟨⟨algebraMap F (AF F) (-k), -k, rfl⟩, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `algebraMap F (AF F) (-k) + x ∈ fundamentalSet F`. Rewrite using `[map_neg, neg_add_eq_sub]` and apply the resulting hypothesis.

Introduce and unpack `⟨_, k', rfl⟩ h`. Express the relevant statement in the definitionally equal form `algebraMap F (AF F) k' + x ∈ fundamentalSet F at h`. Establish `hk' : -k' = k` using `huniq (-k') (by`. Express the relevant statement in the definitionally equal form `x - algebraMap F (AF F) (-k') ∈ fundamentalSet F`. Rewrite using `[map_neg, sub_neg_eq_add, add_comm])` and apply the resulting hypothesis.

Use `Subtype.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `algebraMap F (AF F) k' = algebraMap F (AF F) (-k)`. Rewrite using `[← hk', neg_neg]`.
-/
theorem isFD_fundamentalSet (ν : Measure (AdeleRing (𝓞 F) F)) :
    IsAddFundamentalDomain (ratA F) (fundamentalSet F) ν := by
  refine IsAddFundamentalDomain.mk' (measurableSet_fundamentalSet F).nullMeasurableSet fun x ↦ ?_
  obtain ⟨k, hk, huniq⟩ := existsUnique_sub_mem_fundamentalSet F x
  refine ⟨⟨algebraMap F (AF F) (-k), -k, rfl⟩, ?_, ?_⟩
  · change algebraMap F (AF F) (-k) + x ∈ fundamentalSet F
    rwa [map_neg, neg_add_eq_sub]
  · rintro ⟨_, k', rfl⟩ h
    change algebraMap F (AF F) k' + x ∈ fundamentalSet F at h
    have hk' : -k' = k := huniq (-k') (by
      change x - algebraMap F (AF F) (-k') ∈ fundamentalSet F
      rwa [map_neg, sub_neg_eq_add, add_comm])
    refine Subtype.ext ?_
    change algebraMap F (AF F) k' = algebraMap F (AF F) (-k)
    rw [← hk', neg_neg]

variable {F}

/- English proof (translation)
Take `⟨⟨hlc, hsc, ht2⟩, -⟩` from `GlobalTheory.CompanionTheory.AdeleTop.adele_top F`. Use `haveI := countable_numberField F`. Use `haveI : Countable (ratA F) := (AddMonoidHom.rangeRestrict_surjective _).countable`. Establish `hl : db = Measure.addHaarScalarFactor db (adeleMeasure F) • adeleMeasure F` using `Measure.isAddLeftInvariant_eq_smul db (adeleMeasure F)`. Establish `h2 : db (fundamentalSet F) = 1` using `((isFD_fundamentalSet F db).measure_eq hD).trans hD1`.

Rewrite `h2` using `[hl, Measure.smul_apply, adeleMeasure_fundamentalSet]`. Establish `hc : Measure.addHaarScalarFactor db (adeleMeasure F) = 1`. Simplify `h2` using `[ENNReal.smul_def]`. Rewrite using `[hl, hc, one_smul]`.
-/
theorem eq_adeleMeasure (db : Measure (AdeleRing (𝓞 F) F)) (hH : db.IsAddHaarMeasure) (D : Set (AF F))
    (hD : IsAddFundamentalDomain (ratA F) D db) (hD1 : db D = 1) : db = adeleMeasure F := by
  obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := countable_numberField F
  haveI : Countable (ratA F) := (AddMonoidHom.rangeRestrict_surjective _).countable
  have hl : db = Measure.addHaarScalarFactor db (adeleMeasure F) • adeleMeasure F :=
    Measure.isAddLeftInvariant_eq_smul db (adeleMeasure F)
  have h2 : db (fundamentalSet F) = 1 := ((isFD_fundamentalSet F db).measure_eq hD).trans hD1
  rw [hl, Measure.smul_apply, adeleMeasure_fundamentalSet] at h2
  have hc : Measure.addHaarScalarFactor db (adeleMeasure F) = 1 := by
    simpa [ENNReal.smul_def] using h2
  rw [hl, hc, one_smul]

/- English proof (translation)
Substitute `hm` using the available equality. Take `⟨h1, D, h2, h3⟩` from `hdb`. Conclude with `⟨db, fun _ => rfl, h1, D, h2, h3⟩`.
-/
theorem covol_transfer (db : @Measure (AF F) measAF) (hdb : IsCovolOne db)
    [m : MeasurableSpace (AF F)] (hm : m = measAF) :
    ∃ μ : Measure (AF F), (∀ s, μ s = db s) ∧ μ.IsAddHaarMeasure ∧
      ∃ D : Set (AF F), IsAddFundamentalDomain (ratA F) D μ ∧ μ D = 1 := by
  subst hm
  obtain ⟨h1, D, h2, h3⟩ := hdb
  exact ⟨db, fun _ => rfl, h1, D, h2, h3⟩

end FoundMeas

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.ProdM

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.ProdM

/- English proof (translation)
Substitute `h` using the available equality. Take `rfl : l₁ = l₂` from `Measure.ext fun s _ => hl s`. Both sides reduce to the same expression.
-/
theorem prod_congr_inf {F : Type} [Field F] [NumberField F] {m₁ m₂ : MeasurableSpace (Ainf F)} (h : m₁ = m₂)
    (l₁ : @Measure (Ainf F) m₁) (l₂ : @Measure (Ainf F) m₂) (hl : ∀ s, l₁ s = l₂ s) (lf : Measure (Af F))
    (s : Set (Ainf F × Af F)) :
    @Measure.prod (Ainf F) (Af F) m₁ _ l₁ lf s = @Measure.prod (Ainf F) (Af F) m₂ _ l₂ lf s := by
  subst h
  obtain rfl : l₁ = l₂ := Measure.ext fun s _ => hl s
  rfl

/- English proof (translation)
Use `haveI : BorelSpace (Ainf F) := ⟨rfl⟩`. Use `haveI : BorelSpace (Af F) := ⟨rfl⟩`. Conclude with `(Prod.borelSpace (α := Ainf F) (β := Af F)).measurable_eq`.
-/
theorem prod_meas_eq (F : Type) [Field F] [NumberField F] :
    (inferInstance : MeasurableSpace (Ainf F × Af F)) = (measAF : MeasurableSpace (AF F)) := by
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  exact (Prod.borelSpace (α := Ainf F) (β := Af F)).measurable_eq

def pairE (F : Type) [Field F] [NumberField F] : (Ainf F × Af F) ≃ᵐ AF F where
  toEquiv := Equiv.refl _
  measurable_toFun := by
    intro s hs
    rw [← prod_meas_eq F] at hs
    exact hs
  measurable_invFun := by
    intro s hs
    have hs' : @MeasurableSet (AF F) measAF s := by
      rw [← prod_meas_eq F]
      exact hs
    exact hs'

/- English proof (translation)
Introduce `F _ _ db hdb laminf hinf`. Take `⟨lf, hlf, h1⟩` from `GlobalTheory.CompanionTheory.AdeleHaar.exists_haar_integral_one F`. Use `⟨lf, hlf, h1, pairE F, fun p => rfl, (pairE F).measurable, ?_⟩` and prove the remaining obligations. Establish `hA : GroundTheory.Global.measurableSpace_adeleRing F = (measAF : MeasurableSpace (AF F))` using `(GroundTheory.Global.borelSpace_adeleRing F).measurable_eq`. Establish `hI : GroundTheory.Global.measurableSpace_infiniteAdeleRing F = (measAinf : MeasurableSpace (Ainf F))` using `(GroundTheory.Global.borelSpace_infiniteAdeleRing F).measurable_eq`.

Take `⟨μ, hμ, hH, D, hD, hD1⟩` from `@covol_transfer F _ _ db hdb (GroundTheory.Global.measurableSpace_adeleRing F) hA`. Take `⟨l, hl, hlH, E, hE, hE1⟩` from `@GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler.std_transfer F _ _ laminf hinf (GroundTheory.Global.measurableSpace_infiniteAdeleRing F) hI`. Establish `h2` using `eq_adeleMeasure μ hH D hD hD1`. Establish `h3` using `GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler.adele_eq l hlH E hE hE1 lf hlf h1`. Use `Measure.ext fun s hs => ?_` and prove the remaining obligations.

Rewrite using `[Measure.map_apply (pairE F).measurable hs]`. Establish `e1 : (pairE F) ⁻¹' s = s` using `rfl`. Rewrite using `[e1, ← prod_congr_inf hI l laminf hl lf s, ← hμ s]`. Establish `e2` using `congrArg (fun ν => ν s) h3`. Establish `e3` using `congrArg (fun ν => ν s) h2`.

Conclude with `e2.trans e3.symm`.
-/
theorem prodM : ∀ (F : Type) [Field F] [NumberField F] (db : Measure (AF F)), IsCovolOne db → ∀ laminf : Measure (Ainf F), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → ∃ lf : Measure (Af F), lf.IsAddHaarMeasure ∧ lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 ∧ ∃ e : (Ainf F × Af F) ≃ᵐ AF F, (∀ p, e p = pairA F p.1 p.2) ∧ MeasurePreserving e (laminf.prod lf) db := by
  intro F _ _ db hdb laminf hinf
  obtain ⟨lf, hlf, h1⟩ := GlobalTheory.CompanionTheory.AdeleHaar.exists_haar_integral_one F
  refine ⟨lf, hlf, h1, pairE F, fun p => rfl, (pairE F).measurable, ?_⟩
  have hA : GroundTheory.Global.measurableSpace_adeleRing F = (measAF : MeasurableSpace (AF F)) :=
    (GroundTheory.Global.borelSpace_adeleRing F).measurable_eq
  have hI : GroundTheory.Global.measurableSpace_infiniteAdeleRing F = (measAinf : MeasurableSpace (Ainf F)) :=
    (GroundTheory.Global.borelSpace_infiniteAdeleRing F).measurable_eq
  obtain ⟨μ, hμ, hH, D, hD, hD1⟩ :=
    @covol_transfer F _ _ db hdb (GroundTheory.Global.measurableSpace_adeleRing F) hA
  obtain ⟨l, hl, hlH, E, hE, hE1⟩ :=
    @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler.std_transfer F _ _ laminf hinf (GroundTheory.Global.measurableSpace_infiniteAdeleRing F) hI
  have h2 := eq_adeleMeasure μ hH D hD hD1
  have h3 := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler.adele_eq l hlH E hE hE1 lf hlf h1
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply (pairE F).measurable hs]
  have e1 : (pairE F) ⁻¹' s = s := rfl
  rw [e1, ← prod_congr_inf hI l laminf hl lf s, ← hμ s]
  have e2 := congrArg (fun ν => ν s) h3
  have e3 := congrArg (fun ν => ν s) h2
  exact e2.trans e3.symm

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.ProdM
