import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MemPowIffCoeffMem

namespace GlobalTheory.ChF

open MvPowerSeries

section

variable {R : Type*} [CommRing R] (I : Ideal R) {κ : Type*} [Finite κ]

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.IdealPowerCoefficients.mem_pow_iff_coeff_mem`. Consider the case `exact _root_.GlobalTheory.IdealPowerCoefficients.mem_pow_iff_coeff_mem`. Consider the case `(apply _root_.GlobalTheory.IdealPowerCoefficients.mem_pow_iff_coeff_mem <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.IdealPowerCoefficients.mem_pow_iff_coeff_mem <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.IdealPowerCoefficients.mem_pow_iff_coeff_mem <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.IdealPowerCoefficients.mem_pow_iff_coeff_mem ..)`.
-/
private theorem mem_sup_pow_iff (n : ℕ) (f : MvPowerSeries κ R) :
    f ∈ (I.map (C : R →+* MvPowerSeries κ R) ⊔
      Ideal.span (Set.range (X : κ → MvPowerSeries κ R))) ^ n ↔
      ∀ e : κ →₀ ℕ, coeff e f ∈ I ^ (n - e.degree) := by
  first
  | exact @_root_.GlobalTheory.IdealPowerCoefficients.mem_pow_iff_coeff_mem
  | exact _root_.GlobalTheory.IdealPowerCoefficients.mem_pow_iff_coeff_mem
  | (apply _root_.GlobalTheory.IdealPowerCoefficients.mem_pow_iff_coeff_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IdealPowerCoefficients.mem_pow_iff_coeff_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IdealPowerCoefficients.mem_pow_iff_coeff_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IdealPowerCoefficients.mem_pow_iff_coeff_mem ..)

/- English proof (translation)
Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]`.
-/
private theorem smodEq_pow_iff {S : Type*} [CommRing S] (J : Ideal S) (n : ℕ) (x y : S) :
    x ≡ y [SMOD (J ^ n • ⊤ : Submodule S S)] ↔ x - y ∈ J ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

/- English proof (translation)
Establish `hH : IsHausdorff (I.map (C : R →+* MvPowerSeries κ R) ⊔ Ideal.span (Set.range (X : κ → MvPowerSeries κ R))) (MvPowerSeries κ R)`. Use `⟨fun x hx => ?_⟩` and prove the remaining obligations. Use extensionality with `e`. Use `hI.toIsHausdorff.haus _ fun n => ?_` and prove the remaining obligations. Use `(mem_sup_pow_iff I _ _).1 ((smodEq_pow_iff _ _ _ _).1 (hx (n + e.degree))) e` as an intermediate fact.

Rewrite using `[smodEq_pow_iff]`. Simplify using `using this`. Establish `hP : IsPrecomplete (I.map (C : R →+* MvPowerSeries κ R) ⊔ Ideal.span (Set.range (X : κ → MvPowerSeries κ R))) (MvPowerSeries κ R)`. Use `⟨fun f hf => ?_⟩` and prove the remaining obligations. Establish `hf' : ∀ {m n : ℕ}, m ≤ n → ∀ e : κ →₀ ℕ, coeff e (f m) - coeff e (f n) ∈ I ^ (m - e.degree)` using `fun h e => by`.

Use `(mem_sup_pow_iff I _ _).1 ((smodEq_pow_iff _ _ _ _).1 (hf h)) e` as an intermediate fact. Rewrite `this` using `[map_sub]`. Then use the resulting hypothesis. Establish `hL : ∀ e : κ →₀ ℕ, ∃ L : R, ∀ n, coeff e (f (n + e.degree)) ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)]` using `fun e => hI.toIsPrecomplete.prec (f := fun n => coeff e (f (n + e.degree))) fun {m n} h => by`. Rewrite using `[smodEq_pow_iff]`. Simplify using `using hf' (Nat.add_le_add_right h e.degree) e`.

Use `choose L hL using hL`. Use `⟨L, fun n => ?_⟩` and prove the remaining obligations. Use `(smodEq_pow_iff _ _ _ _).2 ((mem_sup_pow_iff I _ _).2 fun e => ?_)` and prove the remaining obligations. Establish `h1` using `(smodEq_pow_iff _ _ _ _).1 (hL e (n - e.degree))`. Establish `h2` using `hf' (show n ≤ n - e.degree + e.degree by omega) e`.

Establish `h3` using `add_mem h2 h1`. Rewrite `h3` using `[sub_add_sub_cancel]`. Conclude with `h3`. Conclude with `IsAdicComplete.mk`.
-/
private theorem isAdicComplete_sup (hI : IsAdicComplete I R) :
    IsAdicComplete (I.map (C : R →+* MvPowerSeries κ R) ⊔
      Ideal.span (Set.range (X : κ → MvPowerSeries κ R))) (MvPowerSeries κ R) := by
  have hH : IsHausdorff (I.map (C : R →+* MvPowerSeries κ R) ⊔
      Ideal.span (Set.range (X : κ → MvPowerSeries κ R))) (MvPowerSeries κ R) := by
    refine ⟨fun x hx => ?_⟩
    ext e
    refine hI.toIsHausdorff.haus _ fun n => ?_
    have := (mem_sup_pow_iff I _ _).1 ((smodEq_pow_iff _ _ _ _).1 (hx (n + e.degree))) e
    rw [smodEq_pow_iff]
    simpa using this
  have hP : IsPrecomplete (I.map (C : R →+* MvPowerSeries κ R) ⊔
      Ideal.span (Set.range (X : κ → MvPowerSeries κ R))) (MvPowerSeries κ R) := by
    refine ⟨fun f hf => ?_⟩
    have hf' : ∀ {m n : ℕ}, m ≤ n → ∀ e : κ →₀ ℕ,
        coeff e (f m) - coeff e (f n) ∈ I ^ (m - e.degree) := fun h e => by
      have := (mem_sup_pow_iff I _ _).1 ((smodEq_pow_iff _ _ _ _).1 (hf h)) e
      rwa [map_sub] at this
    have hL : ∀ e : κ →₀ ℕ, ∃ L : R, ∀ n,
        coeff e (f (n + e.degree)) ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := fun e =>
      hI.toIsPrecomplete.prec (f := fun n => coeff e (f (n + e.degree))) fun {m n} h => by
        rw [smodEq_pow_iff]
        simpa using hf' (Nat.add_le_add_right h e.degree) e
    choose L hL using hL
    refine ⟨L, fun n => ?_⟩
    refine (smodEq_pow_iff _ _ _ _).2 ((mem_sup_pow_iff I _ _).2 fun e => ?_)
    have h1 := (smodEq_pow_iff _ _ _ _).1 (hL e (n - e.degree))
    have h2 := hf' (show n ≤ n - e.degree + e.degree by omega) e
    have h3 := add_mem h2 h1
    rw [sub_add_sub_cancel] at h3
    exact h3
  exact IsAdicComplete.mk

end

/- English proof (translation)
Introduce `_ _ I _ _` and use `⟨mem_sup_pow_iff I, isAdicComplete_sup I⟩`.
-/
theorem mem_sup_span_X_pow_iff_and_isAdicComplete : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : Type) [Finite κ], (∀ (n : ℕ) (f : MvPowerSeries κ R), f ∈ (I.map (MvPowerSeries.C : R →+* MvPowerSeries κ R) ⊔ Ideal.span (Set.range (MvPowerSeries.X : κ → MvPowerSeries κ R))) ^ n ↔ ∀ e : κ →₀ ℕ, MvPowerSeries.coeff e f ∈ I ^ (n - e.degree)) ∧ (IsAdicComplete I R → IsAdicComplete (I.map (MvPowerSeries.C : R →+* MvPowerSeries κ R) ⊔ Ideal.span (Set.range (MvPowerSeries.X : κ → MvPowerSeries κ R))) (MvPowerSeries κ R)) :=
  fun _ _ I _ _ => ⟨mem_sup_pow_iff I, isAdicComplete_sup I⟩

end GlobalTheory.ChF
