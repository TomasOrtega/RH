import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.MapNMul

/- English proof (translation)
Establish `hs : HasSubst a` using `hasSubst_of_constantCoeff_zero ha`. Establish `h1 : f = (f - C (constantCoeff f)) + C (constantCoeff f)` using `by ring`. Use `conv_lhs => rw [h1]`. Rewrite using `[subst_add hs, map_add, constantCoeff_subst_eq_zero hs ha (by simp), subst_C, zero_add]`. Simplify using the standard rewrite rules.
-/
theorem cc_subst {R : Type} [CommRing R] {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries σ R) :
    constantCoeff (subst a f) = constantCoeff f := by
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have h1 : f = (f - C (constantCoeff f)) + C (constantCoeff f) := by ring
  conv_lhs => rw [h1]
  rw [subst_add hs, map_add, constantCoeff_subst_eq_zero hs ha (by simp), subst_C, zero_add]
  simp

/- English proof (translation)
Unfold `nmul`. Rewrite using `[Function.iterate_succ_apply']`.
-/
theorem nmul_succ {R : Type} [CommRing R] {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (k : ℕ) :
    nmul μ (k + 1) = op μ (nmul μ k) (fun i => X i) := by
  unfold nmul
  rw [Function.iterate_succ_apply']

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro i`. Simplify using `[nmul]`. Consider the case `succ k ih`.

Introduce `i`. Rewrite using `[nmul_succ]`. Simplify using `only [op, at2]`. Apply the tactic sequence `rw [cc_subst (fun s => by cases s <;> simp [ih]), hμ]`.
-/
theorem cc_nmul {R : Type} [CommRing R] {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) : ∀ (k : ℕ) (i : Fin d), constantCoeff (nmul μ k i) = 0 := by
  intro k
  induction k with
  | zero => intro i; simp [nmul]
  | succ k ih =>
    intro i
    rw [nmul_succ]
    simp only [op, at2]
    rw [cc_subst (fun s => by cases s <;> simp [ih]), hμ]

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro i`. Simplify using `[nmul]`. Consider the case `succ k ih`.

Introduce `i`. Rewrite using `[nmul_succ, nmul_succ]`. Simplify using `only [op, at2]`. Apply the tactic sequence `have hs : HasSubst (Sum.elim (nmul μ k) (fun i => (X i : MvPowerSeries (Fin d) R))) := hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp [cc_nmul μ hμ]`. Rewrite using `[map_subst hs]`.

Use `congr 1`. Use function extensionality and compare the values at `s`. Apply the tactic sequence `cases s <;> simp [ih]`.
-/
theorem map_nmul (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0) :
    ∀ (k : ℕ) (i : Fin d), map φ (nmul μ k i) = nmul (fun j => map φ (μ j)) k i := by
  intro k
  induction k with
  | zero => intro i; simp [nmul]
  | succ k ih =>
    intro i
    rw [nmul_succ, nmul_succ]
    simp only [op, at2]
    have hs : HasSubst (Sum.elim (nmul μ k) (fun i => (X i : MvPowerSeries (Fin d) R))) :=
      hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp [cc_nmul μ hμ]
    rw [map_subst hs]
    congr 1
    funext s
    cases s <;> simp [ih]

end GlobalTheory.MapNMul
