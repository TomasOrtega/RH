import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.ExistsRec
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocFixed

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Establish `: (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible` using `Valuation.Compatible.ofValuation _`. Rewrite using `[(isEquiv (valuation (w.adicCompletion F)) (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ)))).lt_one_iff_lt_one]`. Establish `h : Valued.v (((algebraMap (𝓞 F) F (M : 𝓞 F) : F)) : w.adicCompletion F) = w.valuation F (algebraMap (𝓞 F) F (M : 𝓞 F))` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _`. Establish `h2 : w.valuation F (algebraMap (𝓞 F) F (M : 𝓞 F)) < 1` using `(HeightOneSpectrum.valuation_lt_one_iff_mem w _).mpr hw`. Rewrite `h2` using `[← h]`.

Establish `e : (((algebraMap (𝓞 F) F (M : 𝓞 F) : F)) : w.adicCompletion F) = ((M : ℕ) : w.adicCompletion F)`. Rewrite using `[map_natCast]`. Conclude with `map_natCast (algebraMap F (w.adicCompletion F)) M`. Rewrite `h2` using `[e]`. Then use the resulting hypothesis.
-/
private theorem UpperTheory.V.Z.Win.T2.val_lt_one {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) {M : ℕ}
    (hw : (M : 𝓞 F) ∈ w.asIdeal) : valuation (w.adicCompletion F) (M : w.adicCompletion F) < 1 := by
  have : (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [(isEquiv (valuation (w.adicCompletion F))
    (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ)))).lt_one_iff_lt_one]
  have h : Valued.v (((algebraMap (𝓞 F) F (M : 𝓞 F) : F)) : w.adicCompletion F) =
      w.valuation F (algebraMap (𝓞 F) F (M : 𝓞 F)) := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
  have h2 : w.valuation F (algebraMap (𝓞 F) F (M : 𝓞 F)) < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem w _).mpr hw
  rw [← h] at h2
  have e : (((algebraMap (𝓞 F) F (M : 𝓞 F) : F)) : w.adicCompletion F) = ((M : ℕ) : w.adicCompletion F) := by
    rw [map_natCast]
    exact map_natCast (algebraMap F (w.adicCompletion F)) M
  rwa [e] at h2

/- English proof (translation)
Assemble the required witnesses or components as `⟨{IrrGL.ofChar χ hχ}, hasSupport_self (IrrGL.isCusp_ofChar χ hχ), fun y hy => Or.inl (by rw [Multiset.mem_singleton.1 hy] rfl)⟩`.
-/
private theorem UpperTheory.V.Z.Win.T2.good_ofChar {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (χ : kˣ →* ℂˣ) (hχ : GlobalTheory.SmGL.IsSmoothChar χ) :
    UpperTheory.Zero.LLC.Good (IrrGL.ofChar χ hχ) :=
  ⟨{IrrGL.ofChar χ hχ}, hasSupport_self (IrrGL.isCusp_ofChar χ hχ), fun y hy => Or.inl (by
    rw [Multiset.mem_singleton.1 hy]
    rfl)⟩
