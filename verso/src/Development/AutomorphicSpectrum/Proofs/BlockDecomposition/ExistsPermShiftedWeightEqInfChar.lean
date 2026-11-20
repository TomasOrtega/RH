import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LowerIff

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS.ReversedBlocks

variable {n : ℕ}

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Re1.lower_iff P hP b`.
-/
theorem lower_iff (P : Fin n → Prop) [DecidablePred P] (hP : ∀ a b, a ≤ b → P b → P a) (b : Fin n) :
    P b ↔ (b : ℕ) < (univ.filter P).card :=
  _root_.UpperTheory.Reformulated.B.Re1.lower_iff P hP b

def lowC (lev : Fin n → ℕ) (a : Fin n) : ℕ := (univ.filter fun b => lev b < lev a).card

def topC (lev : Fin n → ℕ) (a : Fin n) : ℕ := (univ.filter fun b => lev b ≤ lev a).card

/- English proof (translation)
The claim follows from `lower_iff (fun b => lev b < lev a) (fun _ _ h hb => lt_of_le_of_lt (hm h) hb) b`.
-/
theorem lt_iff {lev : Fin n → ℕ} (hm : Monotone lev) (a b : Fin n) : lev b < lev a ↔ (b : ℕ) < lowC lev a :=
  lower_iff (fun b => lev b < lev a) (fun _ _ h hb => lt_of_le_of_lt (hm h) hb) b

/- English proof (translation)
The claim follows from `lower_iff (fun b => lev b ≤ lev a) (fun _ _ h hb => le_trans (hm h) hb) b`.
-/
theorem le_iff {lev : Fin n → ℕ} (hm : Monotone lev) (a b : Fin n) : lev b ≤ lev a ↔ (b : ℕ) < topC lev a :=
  lower_iff (fun b => lev b ≤ lev a) (fun _ _ h hb => le_trans (hm h) hb) b

/- English proof (translation)
Establish `h` using `Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun b => lev a < lev b)`. Simplify using `only [not_lt, Finset.card_univ, Fintype.card_fin] at h`. Unfold `topC`. Conclude with `h`.
-/
theorem high_add_topC (lev : Fin n → ℕ) (a : Fin n) :
    (univ.filter fun b => lev a < lev b).card + topC lev a = n := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun b => lev a < lev b)
  simp only [not_lt, Finset.card_univ, Fintype.card_fin] at h
  unfold topC
  exact h

def rv (lev : Fin n → ℕ) (a : Fin n) : ℕ := lowC lev a + (topC lev a - 1) - a

/- English proof (translation)
Establish `h1 : ¬ (a : ℕ) < lowC lev a` using `fun h => lt_irrefl _ ((lt_iff hm a a).2 h)`. Establish `h2 : (a : ℕ) < topC lev a` using `(le_iff hm a a).1 le_rfl`. Unfold `rv`. Use linear arithmetic over natural numbers and integers.
-/
theorem rv_bounds {lev : Fin n → ℕ} (hm : Monotone lev) (a : Fin n) :
    lowC lev a ≤ a ∧ (a : ℕ) < topC lev a ∧ rv lev a + a + 1 = lowC lev a + topC lev a := by
  have h1 : ¬ (a : ℕ) < lowC lev a := fun h => lt_irrefl _ ((lt_iff hm a a).2 h)
  have h2 : (a : ℕ) < topC lev a := (le_iff hm a a).1 le_rfl
  unfold rv
  omega

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `rv_bounds hm a`. Use `high_add_topC lev a` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem rv_lt {lev : Fin n → ℕ} (hm : Monotone lev) (a : Fin n) : rv lev a < n := by
  obtain ⟨h1, h2, h3⟩ := rv_bounds hm a
  have := high_add_topC lev a
  omega

def rf {lev : Fin n → ℕ} (hm : Monotone lev) (a : Fin n) : Fin n := ⟨rv lev a, rv_lt hm a⟩

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `rv_bounds hm a`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `(le_iff hm a _).2 (by simp only [rf]; omega)`. Conclude with `not_lt.1 fun h => by`. Use `(lt_iff hm a _).1 h` as an intermediate fact.

Simplify using `only [rf] at this`. Use linear arithmetic over natural numbers and integers.
-/
theorem lev_rf {lev : Fin n → ℕ} (hm : Monotone lev) (a : Fin n) : lev (rf hm a) = lev a := by
  obtain ⟨h1, h2, h3⟩ := rv_bounds hm a
  apply le_antisymm
  · exact (le_iff hm a _).2 (by simp only [rf]; omega)
  · exact not_lt.1 fun h => by
      have := (lt_iff hm a _).1 h
      simp only [rf] at this
      omega

/- English proof (translation)
Establish `hl` using `lev_rf hm a`. Take `⟨h1, h2, h3⟩` from `rv_bounds hm a`. Take `⟨k1, k2, k3⟩` from `rv_bounds hm (rf hm a)`. Establish `e1 : lowC lev (rf hm a) = lowC lev a` using `by simp only [lowC, hl]`. Establish `e2 : topC lev (rf hm a) = topC lev a` using `by simp only [topC, hl]`.

Apply `Fin.ext` to reduce the goal to its premises. Establish `e3 : ((rf hm a : Fin n) : ℕ) = rv lev a` using `rfl`. Establish `e4 : ((rf hm (rf hm a) : Fin n) : ℕ) = rv lev (rf hm a)` using `rfl`. Use linear arithmetic over natural numbers and integers.
-/
theorem rf_rf {lev : Fin n → ℕ} (hm : Monotone lev) (a : Fin n) : rf hm (rf hm a) = a := by
  have hl := lev_rf hm a
  obtain ⟨h1, h2, h3⟩ := rv_bounds hm a
  obtain ⟨k1, k2, k3⟩ := rv_bounds hm (rf hm a)
  have e1 : lowC lev (rf hm a) = lowC lev a := by simp only [lowC, hl]
  have e2 : topC lev (rf hm a) = topC lev a := by simp only [topC, hl]
  apply Fin.ext
  have e3 : ((rf hm a : Fin n) : ℕ) = rv lev a := rfl
  have e4 : ((rf hm (rf hm a) : Fin n) : ℕ) = rv lev (rf hm a) := rfl
  omega

/- English proof (translation)
Introduce `n lam lev h`. Take `⟨hm, hc⟩` from `h`. Use `⟨Function.Involutive.toPerm (rf hm) (rf_rf hm), fun a => ?_⟩` and prove the remaining obligations. Establish `hv : (Function.Involutive.toPerm (rf hm) (rf_rf hm)) a = rf hm a` using `rfl`. Rewrite using `[hv]`.

Establish `hl : lam (rf hm a) = lam a` using `hc _ _ (lev_rf hm a)`. Take `⟨h1, h2, h3⟩` from `rv_bounds hm a`. Establish `h4` using `high_add_topC lev a`. Establish `c3 : ((rv lev a : ℕ) : ℂ) + ((a : ℕ) : ℂ) + 1 = (lowC lev a : ℂ) + (topC lev a : ℂ)` using `by exact_mod_cast h3`. Establish `c4 : (((univ.filter fun b => lev a < lev b).card : ℕ) : ℂ) + (topC lev a : ℂ) = (n : ℂ)` using `by exact_mod_cast h4`.

Establish `e3 : (((rf hm a : Fin n) : ℕ) : ℂ) = (rv lev a : ℂ)` using `rfl`. Establish `hlow : (((univ.filter fun b => lev b < lev a).card : ℕ) : ℂ) = (lowC lev a : ℂ)` using `rfl`. Simplify using `only [GlobalTheory.CompanionTheory.ModelS.yZ, GlobalTheory.CompanionTheory.ModelS.muZ, infOf, hl, e3]`. Use `push_cast`. Rewrite using `[hlow]`.

Take the linear combination `(-1 : ℂ) * c3 - c4`.
-/
theorem exists_perm_yZ : ∀ (n : ℕ) (lam : Fin n → ℤ) (lev : Fin n → ℕ), IsLev lam lev →
    ∃ σ : Equiv.Perm (Fin n), ∀ a : Fin n,
      (GlobalTheory.CompanionTheory.ModelS.yZ lam lev a : ℂ) + ((n : ℂ) - 1) / 2 - ((a : ℕ) : ℂ) = infOf lam false (σ a) := by
  intro n lam lev h
  obtain ⟨hm, hc⟩ := h
  refine ⟨Function.Involutive.toPerm (rf hm) (rf_rf hm), fun a => ?_⟩
  have hv : (Function.Involutive.toPerm (rf hm) (rf_rf hm)) a = rf hm a := rfl
  rw [hv]
  have hl : lam (rf hm a) = lam a := hc _ _ (lev_rf hm a)
  obtain ⟨h1, h2, h3⟩ := rv_bounds hm a
  have h4 := high_add_topC lev a
  have c3 : ((rv lev a : ℕ) : ℂ) + ((a : ℕ) : ℂ) + 1 = (lowC lev a : ℂ) + (topC lev a : ℂ) := by exact_mod_cast h3
  have c4 : (((univ.filter fun b => lev a < lev b).card : ℕ) : ℂ) + (topC lev a : ℂ) = (n : ℂ) := by exact_mod_cast h4
  have e3 : (((rf hm a : Fin n) : ℕ) : ℂ) = (rv lev a : ℂ) := rfl
  have hlow : (((univ.filter fun b => lev b < lev a).card : ℕ) : ℂ) = (lowC lev a : ℂ) := rfl
  simp only [GlobalTheory.CompanionTheory.ModelS.yZ, GlobalTheory.CompanionTheory.ModelS.muZ, infOf, hl, e3]
  push_cast
  rw [hlow]
  linear_combination (-1 : ℂ) * c3 - c4

end GlobalTheory.CompanionTheory.ModelS.ReversedBlocks
