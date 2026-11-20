import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricCharacterIsCMHostValueDatumStatement

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

/- English proof (translation)
Introduce `D N X Z hZ h`. Use `⟨fun i hi => ?_, fun i hi lam => ?_⟩` and prove the remaining obligations. Take `⟨hS, ι, hι, hl⟩` from `h i hi`. Use `⟨ι, hι, fun lam s hs => ?_⟩` and prove the remaining obligations. Take `⟨j, a, s', ⟨-, hs', hv⟩, u, hu, hQ⟩` from `hl lam`.

Choose the witnesses or unpack the hypotheses as in `rfl : s = s' := by`. Establish `h1` using `hs.1`. Establish `h2` using `hs'.1`. Use linear arithmetic over natural numbers and integers. Establish `h1 : 1 ≤ s` using `by exact_mod_cast hs.2.1`.

Conclude with `⟨_, inferInstance, phi D.host, Z.kap j a s, cond0 D.host Z.w0, Z.lam0 (X.l i) j a, u, GlobalTheory.T.isHostDatum_kap_lam0_of_ok D Z hZ (X.l i) j a s h1 hs.2.2, hS, hv, hu, hQ⟩`. Take `⟨-, ι, -, hl⟩` from `h i hi`. Take `⟨j, a, s, ⟨-, hs, -⟩, -⟩` from `hl lam`. Conclude with `⟨s, hs⟩`.
-/
theorem isToricElt_of_isLamTie : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (Z : LamDat D), Z.Ok →
    IsLamTie X Z → IsToricElt X ∧ ∀ i, X.NonzeroIndexPlace i → ∀ lam : X.abelian₂ i, ∃ s : ℤ, BlochKatoReduction.Gen.SOk X i lam s := by
  intro D N X Z hZ h
  refine ⟨fun i hi => ?_, fun i hi lam => ?_⟩
  · obtain ⟨hS, ι, hι, hl⟩ := h i hi
    refine ⟨ι, hι, fun lam s hs => ?_⟩
    obtain ⟨j, a, s', ⟨-, hs', hv⟩, u, hu, hQ⟩ := hl lam
    obtain rfl : s = s' := by
      have h1 := hs.1
      have h2 := hs'.1
      omega
    have h1 : 1 ≤ s := by exact_mod_cast hs.2.1
    exact ⟨_, inferInstance, phi D.host, Z.kap j a s, cond0 D.host Z.w0, Z.lam0 (X.l i) j a, u,
      GlobalTheory.T.isHostDatum_kap_lam0_of_ok D Z hZ (X.l i) j a s h1 hs.2.2, hS, hv, hu, hQ⟩
  · obtain ⟨-, ι, -, hl⟩ := h i hi
    obtain ⟨j, a, s, ⟨-, hs, -⟩, -⟩ := hl lam
    exact ⟨s, hs⟩

end GlobalTheory.LamTie
