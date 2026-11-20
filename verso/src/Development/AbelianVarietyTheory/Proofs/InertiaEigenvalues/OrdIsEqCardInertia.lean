import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedValuationOfPrimeOfGaloisExtensionStatement
import GroundTheory.LocalFields.KroneckerWeber
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

/- English proof (translation)
Unfold `OrdIs`. Rewrite using `[IsDiscreteValuationRing.addVal_uniformizer (GroundTheory.LocalField.Padic.irreducible_natCast_integer l)]`. Both sides reduce to the same expression.
-/
theorem ordIs_padic_self (l : ℕ) [Fact l.Prime] : OrdIs ℚ_[l] l 1 := by
  unfold OrdIs
  rw [IsDiscreteValuationRing.addVal_uniformizer (GroundTheory.LocalField.Padic.irreducible_natCast_integer l)]
  rfl

/- English proof (translation)
Introduce `l _ L _ _ _ _ _ _ _ _ _ _`. Establish `hlL : (l : L) ≠ 0`. Rewrite using `[← map_natCast (algebraMap ℚ_[l] L)]`. Conclude with `(map_ne_zero _).2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)`. Establish `hne : ((l : 𝒪[L])) ≠ 0`.

Introduce `h`. Apply `hlL` to reduce the goal to its premises. Establish `h2 : ((l : 𝒪[L]) : L) = 0` using `by rw [h]; rfl`. Simplify using `using h2`. Establish `htop : IsDiscreteValuationRing.addVal 𝒪[L] (l : 𝒪[L]) ≠ ⊤`.

Rewrite using `[Ne, IsDiscreteValuationRing.addVal_eq_top_iff]` and apply the resulting hypothesis. Take `⟨E, hE⟩` from `WithTop.ne_top_iff_exists.1 htop`. Establish `hL : OrdIs L l E` using `by unfold OrdIs; rw [← hE]; rfl`. Take `⟨e, he, hEe, hram⟩` from `GlobalTheory.T.normalizedValuationOfPrime_of_galoisExtension ℚ_[l] L l E hL`. Establish `h1` using `ordIs_padic_self l`.

Unfold `OrdIs at he h1`. Establish `he1 : e = 1`. Use `he.symm.trans h1` as an intermediate fact. Conclude with `this` after adjusting the coercions. Substitute `he1` using the available equality.

Rewrite `hEe` using `[mul_one]`. Unfold `OrdIs`. Rewrite using `[← hram, ← hEe, ← hE]`. Both sides reduce to the same expression.
-/
theorem ordIs_eq_card_inertia : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra ℚ_[l] L] [ValuativeExtension ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    [IsGalois ℚ_[l] L] [Algebra L (Om l)] [IsScalarTower ℚ_[l] L (Om l)],
    OrdIs L l (Nat.card ↥(lowerRamificationGroup ℚ_[l] L 0)) := by
  intro l _ L _ _ _ _ _ _ _ _ _ _
  have hlL : (l : L) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[l] L)]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hne : ((l : 𝒪[L])) ≠ 0 := by
    intro h
    apply hlL
    have h2 : ((l : 𝒪[L]) : L) = 0 := by rw [h]; rfl
    simpa using h2
  have htop : IsDiscreteValuationRing.addVal 𝒪[L] (l : 𝒪[L]) ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  obtain ⟨E, hE⟩ := WithTop.ne_top_iff_exists.1 htop
  have hL : OrdIs L l E := by unfold OrdIs; rw [← hE]; rfl
  obtain ⟨e, he, hEe, hram⟩ := GlobalTheory.T.normalizedValuationOfPrime_of_galoisExtension ℚ_[l] L l E hL
  have h1 := ordIs_padic_self l
  unfold OrdIs at he h1
  have he1 : e = 1 := by
    have := he.symm.trans h1
    exact_mod_cast this
  subst he1
  rw [mul_one] at hEe
  unfold OrdIs
  rw [← hram, ← hEe, ← hE]
  rfl

end GlobalTheory.PMon.Ram
