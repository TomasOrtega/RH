import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

/- English proof (translation)
Introduce `B T hC v w _`. Take `⟨z, hz⟩` from `hC.roots v`. Use `haveI : NeZero (B.places.resChar v ^ T.k v) := ⟨pow_ne_zero _ (B.places.resChar_prime v).ne_zero⟩`. Establish `hpow : ∀ (χ : Formalism.L2.Host.HChar B.host.E) (m : ℕ), (χ ^ m).val w = χ.val w ^ m`. Introduce `χ m`.

Proceed by induction on `m with`. Consider the case `zero => rw [pow_zero, pow_zero]`. Both sides reduce to the same expression. Consider the case `succ m ih => rw [pow_succ, Formalism.L2.Host.HChar.val_mul, ih, pow_succ]`. Establish `h1 : (((T.psi v).val w : ℂˣ) : ℂ) ^ (B.places.resChar v ^ T.k v) = 1`.

Establish `hord : T.psi v ^ (B.places.resChar v ^ T.k v) = 1` using `T.psi_ord v`. Establish `h0 : (T.psi v ^ (B.places.resChar v ^ T.k v)).val w = (1 : Formalism.L2.Host.HChar B.host.E).val w` using `by rw [hord]`. Rewrite `h0` using `[hpow]`. Rewrite using `[← Units.val_pow_eq_pow_val, h0]`. Both sides reduce to the same expression.

Establish `hz'` using `hz.map_of_injective B.embLL.injective`. Take `⟨i, -, hi⟩` from `hz'.eq_pow_of_pow_eq_one h1`. Use `⟨z ^ i, ?_⟩` and prove the remaining obligations. Simplify using `only [Formalism.L2.Host.HChar.valTw, Complex.ofReal_zero, neg_zero, Complex.cpow_zero, mul_one]`. Rewrite using `[map_pow, hi]`.
-/
theorem twDat_psi_valuesIn_LL : ∀ (B : Base) (T : TwDat B), Coh B T → ∀ v, (T.psi v).ValuesIn 0 B.embLL := by
  intro B T hC v w _
  obtain ⟨z, hz⟩ := hC.roots v
  haveI : NeZero (B.places.resChar v ^ T.k v) := ⟨pow_ne_zero _ (B.places.resChar_prime v).ne_zero⟩
  have hpow : ∀ (χ : Formalism.L2.Host.HChar B.host.E) (m : ℕ), (χ ^ m).val w = χ.val w ^ m := by
    intro χ m
    induction m with
    | zero => rw [pow_zero, pow_zero]; rfl
    | succ m ih => rw [pow_succ, Formalism.L2.Host.HChar.val_mul, ih, pow_succ]
  have h1 : (((T.psi v).val w : ℂˣ) : ℂ) ^ (B.places.resChar v ^ T.k v) = 1 := by
    have hord : T.psi v ^ (B.places.resChar v ^ T.k v) = 1 := T.psi_ord v
    have h0 : (T.psi v ^ (B.places.resChar v ^ T.k v)).val w = (1 : Formalism.L2.Host.HChar B.host.E).val w := by rw [hord]
    rw [hpow] at h0
    rw [← Units.val_pow_eq_pow_val, h0]
    rfl
  have hz' := hz.map_of_injective B.embLL.injective
  obtain ⟨i, -, hi⟩ := hz'.eq_pow_of_pow_eq_one h1
  refine ⟨z ^ i, ?_⟩
  simp only [Formalism.L2.Host.HChar.valTw, Complex.ofReal_zero, neg_zero, Complex.cpow_zero, mul_one]
  rw [map_pow, hi]

end GlobalTheory
