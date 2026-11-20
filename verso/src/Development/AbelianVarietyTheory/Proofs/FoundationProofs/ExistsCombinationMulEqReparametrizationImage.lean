import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraMapZpInjective
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix

namespace GlobalTheory.GeoFix

/- English proof (translation)
Establish `hmem : algebraMap (O0 p) Ω c ∈ ψ.range`. Rewrite using `[h.rng]`. Conclude with `Subalgebra.algebraMap_mem _ c`. Conclude with `hmem`.
-/
theorem inR_algebraMap {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]
    {T : Tower p Ω} {n : ℕ} {ψ : O0 p →+* Ω} (h : IsReb T n ψ) (c : O0 p) :
    ∃ c' : O0 p, ψ c' = algebraMap (O0 p) Ω c := by
  have hmem : algebraMap (O0 p) Ω c ∈ ψ.range := by
    rw [h.rng]
    exact Subalgebra.algebraMap_mem _ c
  exact hmem

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using inR_psi ψ 1`. Consider the case `succ k ih => rw [pow_succ]`. Conclude with `inR_mul ih hx`.
-/
theorem inR_pow {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]
    {ψ : O0 p →+* Ω} {x : Ω} (hx : InR ψ x) (k : ℕ) : InR ψ (x ^ k) := by
  induction k with
  | zero => simpa using inR_psi ψ 1
  | succ k ih => rw [pow_succ]; exact inR_mul ih hx

/- English proof (translation)
Introduce `p _ Ω _ _ hc T n ψ h N hN hN0`. Take `⟨f, hfm, hf⟩ : IsIntegral (O0 p) N` from `hN.isInt h`. Establish `key : ∀ k : ℕ, ∀ f : Polynomial (O0 p), f.natDegree = k → f.Monic → Polynomial.eval₂ (algebraMap (O0 p) Ω) N f = 0 → ∃ (N' : Ω) (D : O0 p), InR ψ N' ∧ D ≠ 0 ∧ N * N' = ψ D`. Introduce `k`. Proceed by induction on `k using Nat.strong_induction_on with`.

Consider the case `_ k ih`. Introduce `f hk hfm hf`. Distinguish the cases in `h0 : f.coeff 0 = 0`. Take `⟨g, rfl⟩` from `Polynomial.X_dvd_iff.2 h0`. Establish `hgm : g.Monic` using `Polynomial.Monic.of_mul_monic_left Polynomial.monic_X hfm`.

Establish `hgdeg : g.natDegree < k`. Rewrite using `[← hk, Polynomial.natDegree_X_mul hgm.ne_zero]`. Use linear arithmetic over natural numbers and integers. Use `ih _ hgdeg g rfl hgm ?_` and prove the remaining obligations. Rewrite `hf` using `[Polynomial.eval₂_mul, Polynomial.eval₂_X]`.

Conclude with `(mul_eq_zero.1 hf).resolve_left hN0`. Take `⟨g, hg⟩` from `Polynomial.X_dvd_iff.2 (show (f - Polynomial.C (f.coeff 0)).coeff 0 = 0 by simp)`. Take `⟨D, hD⟩` from `inR_algebraMap h (-f.coeff 0)`. Use `⟨Polynomial.eval₂ (algebraMap (O0 p) Ω) N g, D, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_eq_sum_range]`.

Use `inR_sum _ _ fun i _ => ?_` and prove the remaining obligations. Take `⟨c', hc'⟩` from `inR_algebraMap h (g.coeff i)`. Rewrite using `[← hc']`. Conclude with `inR_mul (inR_psi ψ c') (inR_pow hN i)`. Introduce and unpack `rfl`.

Rewrite `hD` using `[map_zero, map_neg]`. Conclude with `h0 (hc.inj (by rw [map_zero]; exact neg_eq_zero.1 hD.symm))`. Establish `hf' : f = Polynomial.X * g + Polynomial.C (f.coeff 0)`. Rewrite using `[← hg]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `hf` using `[hf', Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C]`. Rewrite using `[hD, map_neg]`. Take the linear combination `hf`. Conclude with `key _ f rfl hfm hf`.
-/
theorem exists_inR_mul_eq_psi : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (n : ℕ) (ψ : O0 p →+* Ω), IsReb T n ψ → ∀ N : Ω, GlobalTheory.GeoFix.InR ψ N → N ≠ 0 →
    ∃ (N' : Ω) (D : O0 p), GlobalTheory.GeoFix.InR ψ N' ∧ D ≠ 0 ∧ N * N' = ψ D := by
  intro p _ Ω _ _ hc T n ψ h N hN hN0
  obtain ⟨f, hfm, hf⟩ : IsIntegral (O0 p) N := hN.isInt h
  have key : ∀ k : ℕ, ∀ f : Polynomial (O0 p), f.natDegree = k → f.Monic → Polynomial.eval₂ (algebraMap (O0 p) Ω) N f = 0 →
      ∃ (N' : Ω) (D : O0 p), InR ψ N' ∧ D ≠ 0 ∧ N * N' = ψ D := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro f hk hfm hf
      by_cases h0 : f.coeff 0 = 0
      · obtain ⟨g, rfl⟩ := Polynomial.X_dvd_iff.2 h0
        have hgm : g.Monic := Polynomial.Monic.of_mul_monic_left Polynomial.monic_X hfm
        have hgdeg : g.natDegree < k := by
          rw [← hk, Polynomial.natDegree_X_mul hgm.ne_zero]; omega
        refine ih _ hgdeg g rfl hgm ?_
        rw [Polynomial.eval₂_mul, Polynomial.eval₂_X] at hf
        exact (mul_eq_zero.1 hf).resolve_left hN0
      · obtain ⟨g, hg⟩ := Polynomial.X_dvd_iff.2 (show (f - Polynomial.C (f.coeff 0)).coeff 0 = 0 by simp)
        obtain ⟨D, hD⟩ := inR_algebraMap h (-f.coeff 0)
        refine ⟨Polynomial.eval₂ (algebraMap (O0 p) Ω) N g, D, ?_, ?_, ?_⟩
        · rw [Polynomial.eval₂_eq_sum_range]
          refine inR_sum _ _ fun i _ => ?_
          obtain ⟨c', hc'⟩ := inR_algebraMap h (g.coeff i)
          rw [← hc']
          exact inR_mul (inR_psi ψ c') (inR_pow hN i)
        · rintro rfl
          rw [map_zero, map_neg] at hD
          exact h0 (hc.inj (by rw [map_zero]; exact neg_eq_zero.1 hD.symm))
        · have hf' : f = Polynomial.X * g + Polynomial.C (f.coeff 0) := by
            rw [← hg]; ring
          rw [hf', Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C] at hf
          rw [hD, map_neg]
          linear_combination hf
  exact key _ f rfl hfm hf

end GlobalTheory.GeoFix
