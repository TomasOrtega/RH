import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchemeTheoreticallyDominantOfGermInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreDenseAffineChartPrimesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnnihilatorAvoidsFibreMinimalPrimesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAlgebraLocalizationEqZeroOfAvoidFibreMinimStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonZeroDivisorLocalizationGeneralOfNoetherianStatement
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.FibreDense

/- English proof (translation)
Assume the negation of the conclusion as `hb`. Set `I : Ideal B` to `LinearMap.ker (LinearMap.toSpanSingleton B B b)`. Establish `hI : I ≠ ⊤`. Introduce `h1`. Establish `: (1 : B) ∈ I` using `h1 ▸ Submodule.mem_top`.

Simplify using `[I] at this`. Conclude with `hb this`. Take `⟨m, hm, hle⟩` from `Ideal.exists_le_maximal I hI`. Set `u : PrimeSpectrum B` to `⟨m, hm.isPrime⟩`. Take `⟨g, hg, hgQ⟩` from `GlobalTheory.T.exists_annihilator_not_mem_minimalPrimes_le A B b h u`.

Establish `h0` using `GlobalTheory.T.nonZeroDivisor_localization_general_of_noetherian GlobalTheory.T.smooth_algebra_localization_eq_zero_of_avoid_fibre_minimal A B b g u hg hgQ`. Take `⟨s, hs⟩` from `(IsLocalization.map_eq_zero_iff u.asIdeal.primeCompl _ b).1 h0`. Conclude with `s.2 (hle (by simpa [I] using hs))`.
-/
theorem alg (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B] (b : B)
    (h : ∀ q : PrimeSpectrum B, q ∈ closure ({P : PrimeSpectrum B | ∃ s ∉ P.asIdeal, s * b = 0} ∩
      PrimeSpectrum.comap (algebraMap A B) ⁻¹' {PrimeSpectrum.comap (algebraMap A B) q})) : b = 0 := by
  by_contra hb
  let I : Ideal B := LinearMap.ker (LinearMap.toSpanSingleton B B b)
  have hI : I ≠ ⊤ := by
    intro h1
    have : (1 : B) ∈ I := h1 ▸ Submodule.mem_top
    simp [I] at this
    exact hb this
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I hI
  let u : PrimeSpectrum B := ⟨m, hm.isPrime⟩
  obtain ⟨g, hg, hgQ⟩ := GlobalTheory.T.exists_annihilator_not_mem_minimalPrimes_le A B b h u
  have h0 := GlobalTheory.T.nonZeroDivisor_localization_general_of_noetherian GlobalTheory.T.smooth_algebra_localization_eq_zero_of_avoid_fibre_minimal A B b g u hg hgQ
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff u.asIdeal.primeCompl _ b).1 h0
  exact s.2 (hle (by simpa [I] using hs))

/- English proof (translation)
Use `GlobalTheory.T.schemeTheoreticallyDominant_of_germ_injective X T p W fun U V hU hV e b hb => ?_` and prove the remaining obligations. Use `letI := (p.appLE V U e).hom.toAlgebra`. Use `haveI : Algebra.Smooth Γ(T, V) Γ(X, U) := HasRingHomProperty.appLE @Smooth p ‹_› ⟨V, hV⟩ ⟨U, hU⟩ e`. Conclude with `alg Γ(T, V) Γ(X, U) b (GlobalTheory.T.mem_closure_annihilator_primes_inter_fibre X T p W U V hU hV e hW b hb)`.
-/
theorem dense (X T : Scheme.{0}) (p : X ⟶ T) [Smooth p] (W : X.Opens)
    (hW : ∀ x : X, x ∈ closure ((W : Set X) ∩ p ⁻¹' {p x})) : IsSchemeTheoreticallyDominant W.ι := by
  refine GlobalTheory.T.schemeTheoreticallyDominant_of_germ_injective X T p W fun U V hU hV e b hb => ?_
  letI := (p.appLE V U e).hom.toAlgebra
  haveI : Algebra.Smooth Γ(T, V) Γ(X, U) := HasRingHomProperty.appLE @Smooth p ‹_› ⟨V, hV⟩ ⟨U, hU⟩ e
  exact alg Γ(T, V) Γ(X, U) b (GlobalTheory.T.mem_closure_annihilator_primes_inter_fibre X T p W U V hU hV e hW b hb)

/- English proof (translation)
Set `X' : Over Z` to `Over.mk (f ≫ s)`. Set `Y' : Over Z` to `Over.mk s`. Set `f' : X' ⟶ Y'` to `Over.homMk f`. Set `g' : X' ⟶ Y'` to `Over.homMk g h.symm`. Use `haveI : IsSeparated Y'.hom := ‹IsSeparated s›`.

Set `U' : Over Z` to `Over.mk (d ≫ f ≫ s)`. Set `d' : U' ⟶ X'` to `Over.homMk d`. Establish `e : d' ≫ f' = d' ≫ g'` using `by ext1`. Conclude with `hU`. Set `l` to `equalizer.lift d' e`.

Establish `hd : d = l.left ≫ (equalizer.ι f' g').left`. Rewrite using `[← Over.comp_left, equalizer.lift_ι]`. Both sides reduce to the same expression. Establish `hker : (equalizer.ι f' g').left.ker = ⊥`. Apply `le_bot_iff.1` to reduce the goal to its premises.

Combine the equalities or inequalities in the displayed calculation. Use `haveI : IsIso (equalizer.ι f' g').left := IsClosedImmersion.isIso_iff_ker_eq_bot.2 hker`. Establish `h0 : IsIso ((Over.forget Z).map (equalizer.ι f' g'))` using `(inferInstance : IsIso (equalizer.ι f' g').left)`. Establish `: IsIso (equalizer.ι f' g')` using `isIso_of_reflects_iso _ (Over.forget Z)`. Establish `hfg : f' = g'` using `(cancel_epi (equalizer.ι f' g')).1 (equalizer.condition f' g')`.

Conclude with `congrArg CommaMorphism.left hfg`.
-/
theorem ext_of_dominant {W X Y Z : Scheme.{0}} {f g : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (d : W ⟶ X) [IsSchemeTheoreticallyDominant d] (hU : d ≫ f = d ≫ g) : f = g := by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g h.symm
  haveI : IsSeparated Y'.hom := ‹IsSeparated s›
  let U' : Over Z := Over.mk (d ≫ f ≫ s)
  let d' : U' ⟶ X' := Over.homMk d
  have e : d' ≫ f' = d' ≫ g' := by
    ext1
    exact hU
  let l := equalizer.lift d' e
  have hd : d = l.left ≫ (equalizer.ι f' g').left := by
    rw [← Over.comp_left, equalizer.lift_ι]; rfl
  have hker : (equalizer.ι f' g').left.ker = ⊥ := by
    apply le_bot_iff.1
    calc _ ≤ (l.left ≫ (equalizer.ι f' g').left).ker := Scheme.Hom.le_ker_comp _ _
      _ = ⊥ := by rw [← hd]; exact d.ker_eq_bot
  haveI : IsIso (equalizer.ι f' g').left := IsClosedImmersion.isIso_iff_ker_eq_bot.2 hker
  have h0 : IsIso ((Over.forget Z).map (equalizer.ι f' g')) := (inferInstance : IsIso (equalizer.ι f' g').left)
  have : IsIso (equalizer.ι f' g') := isIso_of_reflects_iso _ (Over.forget Z)
  have hfg : f' = g' := (cancel_epi (equalizer.ι f' g')).1 (equalizer.condition f' g')
  exact congrArg CommaMorphism.left hfg

/- English proof (translation)
Introduce `X T Y p _ q _ W hW f g hfg hfgW`. Use `haveI := dense X T p W hW`. Conclude with `ext_of_dominant q hfg W.ι hfgW`.
-/
theorem main : ∀ (X T Y : Scheme.{0}) (p : X ⟶ T) [Smooth p] (q : Y ⟶ T) [IsSeparated q] (W : X.Opens),
    (∀ x : X, x ∈ closure ((W : Set X) ∩ p ⁻¹' {p x})) →
    ∀ f g : X ⟶ Y, f ≫ q = g ≫ q → W.ι ≫ f = W.ι ≫ g → f = g := by
  intro X T Y p _ q _ W hW f g hfg hfgW
  haveI := dense X T p W hW
  exact ext_of_dominant q hfg W.ι hfgW

end GlobalTheory.FibreDense
