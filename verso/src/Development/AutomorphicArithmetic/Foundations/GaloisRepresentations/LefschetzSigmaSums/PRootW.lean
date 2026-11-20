import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi
open UpperTheory.Gal.LocalSmoothExtension

/- English proof (translation)
Introduce `hW hOff hL hS F _ _ n t₀ ε lam h hconj hexp`. Break down `hexp with ⟨m, hm, hh⟩ | ⟨m, hm, hh⟩` into its components or cases. Take `⟨k₀, hk⟩` from `hW F n t₀ ε lam m hconj hm`. Use `⟨k₀, fun k hk' => ?_⟩` and prove the remaining obligations. Take `⟨c, hc, hsum⟩` from `hk k hk'`.

Use `⟨c, hc, ?_⟩` and prove the remaining obligations. Introduce `χ hdeg hsep _ _ y`. Take `⟨g, hg⟩` from `hL F n χ hdeg`. Rewrite using `[hsum χ g hsep hg y, hS F n lam χ g hg]`. Simplify using `only [hh, pow_add, Finset.mul_sum]`.

Take `⟨k₀, hk⟩` from `hOff F n t₀ ε lam m hconj hm`. Use `⟨k₀, fun k hk' => ?_⟩` and prove the remaining obligations. Take `⟨c, hc, hsum⟩` from `hk k hk'`. Use `⟨c, hc, ?_⟩` and prove the remaining obligations. Introduce `χ hdeg hsep h0 hq y`.

Take `⟨g, hg⟩` from `hL F n χ hdeg`. Rewrite using `[hsum χ g hsep hg h0 hq y, hS F n lam χ g hg]`. Simplify using `only [hh, pow_add, Finset.mul_sum]`.
-/
theorem UpperTheory.Gal.LocalSmoothExtension.rootW_of :
    UpperTheory.Gal.W2.RootSumW → UpperTheory.Gal.W2.RootSumWOff → ListsEx → SchWEq → RootW := by
  intro hW hOff hL hS F _ _ n t₀ ε lam h hconj hexp
  rcases hexp with ⟨m, hm, hh⟩ | ⟨m, hm, hh⟩
  · obtain ⟨k₀, hk⟩ := hW F n t₀ ε lam m hconj hm
    refine ⟨k₀, fun k hk' => ?_⟩
    obtain ⟨c, hc, hsum⟩ := hk k hk'
    refine ⟨c, hc, ?_⟩
    intro χ hdeg hsep _ _ y
    obtain ⟨g, hg⟩ := hL F n χ hdeg
    rw [hsum χ g hsep hg y, hS F n lam χ g hg]
    simp only [hh, pow_add, Finset.mul_sum]
  · obtain ⟨k₀, hk⟩ := hOff F n t₀ ε lam m hconj hm
    refine ⟨k₀, fun k hk' => ?_⟩
    obtain ⟨c, hc, hsum⟩ := hk k hk'
    refine ⟨c, hc, ?_⟩
    intro χ hdeg hsep h0 hq y
    obtain ⟨g, hg⟩ := hL F n χ hdeg
    rw [hsum χ g hsep hg h0 hq y, hS F n lam χ g hg]
    simp only [hh, pow_add, Finset.mul_sum]
