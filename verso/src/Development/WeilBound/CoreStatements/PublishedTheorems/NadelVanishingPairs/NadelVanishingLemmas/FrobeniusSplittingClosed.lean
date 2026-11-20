import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.AlternatingProductCocycle

open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI.PhiClosed

variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[pow_succ' _ (n + 1), hd.mul, ih, AlgHom.commutes]`. Establish `hc : d (algebraMap K (ExteriorAlgebra K V) c) * algebraMap K (ExteriorAlgebra K V) c ^ (n + 1) = algebraMap K (ExteriorAlgebra K V) c ^ (n + 1) * d (algebraMap K (ExteriorAlgebra K V) c)`.

Rewrite using `[← map_pow]`. Conclude with `(Algebra.commutes _ _).symm`. Rewrite using `[hc, mul_smul_comm, ← mul_assoc, ← pow_succ', succ_nsmul' _ (n + 1)]`.
-/
theorem d_alg_pow (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (hd : IsOddDer d) (c : K) (n : ℕ) :
    d (algebraMap K (ExteriorAlgebra K V) c ^ (n + 1)) =
      (n + 1) • (algebraMap K (ExteriorAlgebra K V) c ^ n * d (algebraMap K (ExteriorAlgebra K V) c)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ' _ (n + 1), hd.mul, ih, AlgHom.commutes]
    have hc : d (algebraMap K (ExteriorAlgebra K V) c) * algebraMap K (ExteriorAlgebra K V) c ^ (n + 1) =
        algebraMap K (ExteriorAlgebra K V) c ^ (n + 1) * d (algebraMap K (ExteriorAlgebra K V) c) := by
      rw [← map_pow]
      exact (Algebra.commutes _ _).symm
    rw [hc, mul_smul_comm, ← mul_assoc, ← pow_succ', succ_nsmul' _ (n + 1)]

/- English proof (translation)
Take `⟨k, hk⟩ : ∃ k, p = k + 1` from `⟨p - 1, by have := (Fact.out : p.Prime).one_lt; omega⟩`. Rewrite using `[map_pow, hk, d_alg_pow d hd c k, ← hk, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul]`.
-/
theorem d_alg_pow_char (p : ℕ) [Fact p.Prime] [CharP K p] (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V)
    (hd : IsOddDer d) (c : K) : d (algebraMap K (ExteriorAlgebra K V) (c ^ p)) = 0 := by
  obtain ⟨k, hk⟩ : ∃ k, p = k + 1 := ⟨p - 1, by have := (Fact.out : p.Prime).one_lt; omega⟩
  rw [map_pow, hk, d_alg_pow d hd c k, ← hk, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul]

/- English proof (translation)
Rewrite using `[Algebra.smul_def, hd.mul, AlgHom.commutes, d_alg_pow_char p d hd c, zero_mul, zero_add, ← Algebra.smul_def]`.
-/
theorem d_smul_pow (p : ℕ) [Fact p.Prime] [CharP K p] (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V)
    (hd : IsOddDer d) (c : K) (y : ExteriorAlgebra K V) : d (c ^ p • y) = c ^ p • d y := by
  rw [Algebra.smul_def, hd.mul, AlgHom.commutes, d_alg_pow_char p d hd c, zero_mul, zero_add,
    ← Algebra.smul_def]

/- English proof (translation)
Use function extensionality and compare the values at `t`. Simplify using `only [Dtot, delta, Pi.add_apply, smul_add, Finset.sum_add_distrib, map_add]`. Normalize the expressions using the abelian group laws.
-/
theorem Dtot_add (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (a b : Finset ι → ExteriorAlgebra K V) :
    Dtot d (a + b) = Dtot d a + Dtot d b := by
  funext t
  simp only [Dtot, delta, Pi.add_apply, smul_add, Finset.sum_add_distrib, map_add]
  abel

/- English proof (translation)
Use function extensionality and compare the values at `t`. Simplify using `only [Dtot, delta, Pi.smul_apply, d_smul_pow p d hd, Finset.smul_sum, smul_add]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun i _ => smul_comm _ _ _`. Conclude with `smul_comm _ _ _`.
-/
theorem Dtot_smul_pow (p : ℕ) [Fact p.Prime] [CharP K p] (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V)
    (hd : IsOddDer d) (c : K) (a : Finset ι → ExteriorAlgebra K V) :
    Dtot d (c ^ p • a) = c ^ p • Dtot d a := by
  funext t
  simp only [Dtot, delta, Pi.smul_apply, d_smul_pow p d hd, Finset.smul_sum, smul_add]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  · exact smul_comm _ _ _

end GlobalTheory.DI.PhiClosed

open GlobalTheory.DI.PhiClosed in
/- English proof (translation)
Introduce `K _ V _ _ ι _ p _ _ d f h Φ hd hD hΦ`. Establish `hA` using `(prodL_alt_closed p d f h hd hD).2`. Establish `hz0 : Dtot d (0 : Finset ι → ExteriorAlgebra K V) = 0`. Use function extensionality and compare the values at `t`. Simplify using `[Dtot, delta]`.

Establish `key : ∀ x : ExteriorAlgebra K V, ∀ c : K, Φ (c • x) ∅ = 0 ∧ Dtot d (Φ (c • x)) = 0`. Introduce `x`. Establish `hx : x ∈ Submodule.span K (Set.range fun x : (n : ℕ) × (Fin n → V) => ExteriorAlgebra.ιMulti K x.1 x.2)`. Rewrite using `[ExteriorAlgebra.ιMulti_span]`. Conclude with `Submodule.mem_top`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨⟨a, v⟩, rfl⟩` from `hy`. Introduce `c`. Rewrite using `[hΦ c a v]`.

Conclude with `⟨by rw [Pi.smul_apply, (hA a v).2, smul_zero], by rw [PhiClosed.Dtot_smul_pow p d hd, (hA a v).1, smul_zero]⟩`. Consider the case `zero`. Introduce `c`. Simplify using `[hz0]`. Consider the case `add y z _ _ hy hz`.

Introduce `c`. Rewrite using `[smul_add, map_add]`. Conclude with `⟨by rw [Pi.add_apply, (hy c).1, (hz c).1, add_zero], by rw [PhiClosed.Dtot_add, (hy c).2, (hz c).2, add_zero]⟩`. Consider the case `smul a y _ hy`. Introduce `c`.

Rewrite using `[smul_smul]`. Conclude with `hy (c * a)`. Conclude with `⟨fun x => by simpa using (key x 1).1, fun x => by simpa using (key x 1).2⟩`.
-/
theorem GlobalTheory.DI.phi_closed : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) [Fact p.Prime] [CharP K p] (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V) (h : ι → ι → V →+ K) (Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V)), IsOddDer d → IsDatum p d f h → IsPhi p f h Φ → (∀ x, Φ x ∅ = 0) ∧ ∀ x, Dtot d (Φ x) = 0 := by
  intro K _ V _ _ ι _ p _ _ d f h Φ hd hD hΦ
  have hA := (prodL_alt_closed p d f h hd hD).2
  have hz0 : Dtot d (0 : Finset ι → ExteriorAlgebra K V) = 0 := by
    funext t
    simp [Dtot, delta]
  have key : ∀ x : ExteriorAlgebra K V, ∀ c : K, Φ (c • x) ∅ = 0 ∧ Dtot d (Φ (c • x)) = 0 := by
    intro x
    have hx : x ∈ Submodule.span K
        (Set.range fun x : (n : ℕ) × (Fin n → V) => ExteriorAlgebra.ιMulti K x.1 x.2) := by
      rw [ExteriorAlgebra.ιMulti_span]
      exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨⟨a, v⟩, rfl⟩ := hy
      intro c
      rw [hΦ c a v]
      exact ⟨by rw [Pi.smul_apply, (hA a v).2, smul_zero],
        by rw [PhiClosed.Dtot_smul_pow p d hd, (hA a v).1, smul_zero]⟩
    | zero =>
      intro c
      simp [hz0]
    | add y z _ _ hy hz =>
      intro c
      rw [smul_add, map_add]
      exact ⟨by rw [Pi.add_apply, (hy c).1, (hz c).1, add_zero],
        by rw [PhiClosed.Dtot_add, (hy c).2, (hz c).2, add_zero]⟩
    | smul a y _ hy =>
      intro c
      rw [smul_smul]
      exact hy (c * a)
  exact ⟨fun x => by simpa using (key x 1).1, fun x => by simpa using (key x 1).2⟩
