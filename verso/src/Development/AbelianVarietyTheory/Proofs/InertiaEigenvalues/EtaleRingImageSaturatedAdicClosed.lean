import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodOfComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleComparisonPiAdicFiltrationModEllStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.Decompl.Sat

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => exact fun e _ _ => ⟨e, by simp⟩`. Consider the case `succ k ih`. Introduce `e r h`. Take `⟨e₁, rfl⟩` from `hd e ((p : R) ^ k * r) (by rw [h]; ring)`.

Establish `h1 : f e₁ = (p : R) ^ k * r`. Rewrite using `[← sub_eq_zero]`. Apply `htf` to reduce the goal to its premises. Rewrite `h` using `[map_mul, map_natCast]`. Take the linear combination `h`.

Take `⟨e₂, rfl⟩` from `ih e₁ r h1`. Conclude with `⟨e₂, by ring⟩`.
-/
theorem pow_dvd_of_map {A R : Type} [CommRing A] [CommRing R] (f : A →+* R) (p : ℕ)
    (htf : ∀ x : R, (p : R) * x = 0 → x = 0)
    (hd : ∀ (e : A) (r : R), f e = (p : R) * r → ∃ e' : A, e = (p : A) * e') (k : ℕ) :
    ∀ (e : A) (r : R), f e = (p : R) ^ k * r → ∃ e' : A, e = (p : A) ^ k * e' := by
  induction k with
  | zero => exact fun e _ _ => ⟨e, by simp⟩
  | succ k ih =>
    intro e r h
    obtain ⟨e₁, rfl⟩ := hd e ((p : R) ^ k * r) (by rw [h]; ring)
    have h1 : f e₁ = (p : R) ^ k * r := by
      rw [← sub_eq_zero]
      apply htf
      rw [map_mul, map_natCast] at h
      linear_combination h
    obtain ⟨e₂, rfl⟩ := ih e₁ r h1
    exact ⟨e₂, by ring⟩

/- English proof (translation)
Use `⟨fun x e h => ?_, fun x h => ?_⟩` and prove the remaining obligations. Take `⟨e', rfl⟩` from `hd e x h.symm`. Use `⟨e', ?_⟩` and prove the remaining obligations. Rewrite using `[← sub_eq_zero]`. Apply `htf` to reduce the goal to its premises.

Rewrite `h` using `[map_mul, map_natCast]`. Take the linear combination `h`. Use `choose e r her using h`. Establish `key : ∀ (n : ℕ) (a b : A), a ≡ b [SMOD (Ideal.span {(p : A)}) ^ n • (⊤ : Submodule A A)] ↔ (p : A) ^ n ∣ a - b`. Introduce `n a b`.

Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Take `⟨L, hL⟩` from `hA.prec (f := e) (by`. Introduce `m n hmn`. Rewrite using `[key]`. Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hmn`.

Use `pow_dvd_of_map f p htf hd m _ ((p : R) ^ k * r (m + k) - r m) ?_` and prove the remaining obligations. Rewrite using `[map_sub]`. Take the linear combination `her (m + k) - her m)`. Use `⟨L, ?_⟩` and prove the remaining obligations. Rewrite using `[← sub_eq_zero]`.

Use `hsep _ fun k => ?_` and prove the remaining obligations. Take `⟨c, hc⟩` from `(key _ _ _).1 (hL k)`. Establish `h1` using `congrArg f hc`. Rewrite `h1` using `[map_sub, map_mul, map_pow, map_natCast]`. Conclude with `⟨r k + f c, by linear_combination her k + h1⟩`.
-/
theorem sat_closed {A R : Type} [CommRing A] [CommRing R] (f : A →+* R) (p : ℕ)
    (hA : IsPrecomplete (Ideal.span {(p : A)}) A)
    (htf : ∀ x : R, (p : R) * x = 0 → x = 0)
    (hsep : ∀ x : R, (∀ k : ℕ, ∃ r, x = (p : R) ^ k * r) → x = 0)
    (hd : ∀ (e : A) (r : R), f e = (p : R) * r → ∃ e' : A, e = (p : A) * e') :
    (∀ (x : R) (e : A), (p : R) * x = f e → ∃ e', x = f e') ∧
      ∀ x : R, (∀ k : ℕ, ∃ e r, x - f e = (p : R) ^ k * r) → ∃ e, x = f e := by
  refine ⟨fun x e h => ?_, fun x h => ?_⟩
  · obtain ⟨e', rfl⟩ := hd e x h.symm
    refine ⟨e', ?_⟩
    rw [← sub_eq_zero]
    apply htf
    rw [map_mul, map_natCast] at h
    linear_combination h
  · choose e r her using h
    have key : ∀ (n : ℕ) (a b : A),
        a ≡ b [SMOD (Ideal.span {(p : A)}) ^ n • (⊤ : Submodule A A)] ↔ (p : A) ^ n ∣ a - b := by
      intro n a b
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton]
    obtain ⟨L, hL⟩ := hA.prec (f := e) (by
      intro m n hmn
      rw [key]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      refine pow_dvd_of_map f p htf hd m _ ((p : R) ^ k * r (m + k) - r m) ?_
      rw [map_sub]
      linear_combination her (m + k) - her m)
    refine ⟨L, ?_⟩
    rw [← sub_eq_zero]
    refine hsep _ fun k => ?_
    obtain ⟨c, hc⟩ := (key _ _ _).1 (hL k)
    have h1 := congrArg f hc
    rw [map_sub, map_mul, map_pow, map_natCast] at h1
    exact ⟨r k + f c, by linear_combination her k + h1⟩

/- English proof (translation)
Introduce `l _ P AI K s LL h W E`. Establish `hc : IsAdicComplete (Ideal.span {(l : W.EE)}) W.EE`. Use `W.EE_complete` as an intermediate fact. Rewrite `this` using `[P.PD_p K]`. Then use the resulting hypothesis. Conclude with `sat_closed (E.tie.ioE : W.EE →+* RW LL) l hc.toIsPrecomplete (LAdic.ladic_RW l LL).1 (LAdic.ladic_RW l LL).2.1 (GlobalTheory.T.etaleComparison_piAdic_filtration_mod_ell l P AI K s LL h W E).2`.
-/
theorem ioE_saturated_closed : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W), (∀ (x : RW LL) (e : W.EE), (l : RW LL) * x = E.tie.ioE e → ∃ e', x = E.tie.ioE e') ∧ ∀ x : RW LL, (∀ k : ℕ, ∃ e r, x - E.tie.ioE e = (l : RW LL) ^ k * r) → ∃ e, x = E.tie.ioE e := by
  intro l _ P AI K s LL h W E
  have hc : IsAdicComplete (Ideal.span {(l : W.EE)}) W.EE := by
    have := W.EE_complete
    rwa [P.PD_p K] at this
  exact sat_closed (E.tie.ioE : W.EE →+* RW LL) l hc.toIsPrecomplete
    (LAdic.ladic_RW l LL).1 (LAdic.ladic_RW l LL).2.1 (GlobalTheory.T.etaleComparison_piAdic_filtration_mod_ell l P AI K s LL h W E).2

end GlobalTheory.Decompl.Sat
