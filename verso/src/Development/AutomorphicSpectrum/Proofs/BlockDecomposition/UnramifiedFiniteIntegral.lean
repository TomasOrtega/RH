import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.BasisSet

namespace GlobalTheory.CompanionTheory.Gunr

open NumberField IsDedekindDomain Filter

/- English proof (translation)
Introduce `F _ _ X`. Establish `hone : ∀ x : F, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, algebraMap F (v.adicCompletion F) x ∈ v.adicCompletionIntegers F`. Introduce `x`. Establish `hfin : {v : HeightOneSpectrum (𝓞 F) | 1 < v.valuation F x}.Finite` using `HeightOneSpectrum.Support.finite (𝓞 F) x`. Establish `hev : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ¬ 1 < v.valuation F x`.

Rewrite using `[eventually_cofinite]`. Simplify using `using hfin`. Use `hev.mono fun v hv => ?_` and prove the remaining obligations. Establish `e : Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, e]`.

Conclude with `not_lt.mp hv`. Establish `hall : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ x ∈ X, algebraMap F (v.adicCompletion F) x ∈ v.adicCompletionIntegers F` using `(Filter.eventually_all_finset X).2 fun x _ => hone x`. Conclude with `hall`.
-/
theorem finInt : PositivityTheory.SiegelWeilFormula.Gunr.FinInt := by
  intro F _ _ X
  have hone : ∀ x : F, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      algebraMap F (v.adicCompletion F) x ∈ v.adicCompletionIntegers F := by
    intro x
    have hfin : {v : HeightOneSpectrum (𝓞 F) | 1 < v.valuation F x}.Finite :=
      HeightOneSpectrum.Support.finite (𝓞 F) x
    have hev : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ¬ 1 < v.valuation F x := by
      rw [eventually_cofinite]
      simpa using hfin
    refine hev.mono fun v hv => ?_
    have e : Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, e]
    exact not_lt.mp hv
  have hall : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      ∀ x ∈ X, algebraMap F (v.adicCompletion F) x ∈ v.adicCompletionIntegers F :=
    (Filter.eventually_all_finset X).2 fun x _ => hone x
  exact hall

end GlobalTheory.CompanionTheory.Gunr
