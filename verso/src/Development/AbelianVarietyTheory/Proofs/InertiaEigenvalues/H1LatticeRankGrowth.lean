import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientRingIntegersCompactAdicProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteFinrankOfLocalizes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardQuotSpanPowEqCardPowDomainStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardQuotPowSmulBoundsDvrFgModuleStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

set_option autoImplicit false

namespace GlobalTheory.H1Rank

/- English proof (translation)
Introduce `l _ K LL _ _ _ O _ _ hG A LA hfin`. Establish `hG'` using `hG`. Take `⟨⟨hD, hDVR, hFr⟩, -, -, -, -⟩` from `hG'`. Use `haveI := hD`. Use `haveI := hDVR`.

Use `haveI := hFr`. Establish `hl0 : ((l : ℕ) : O) ≠ 0`. Introduce `h`. Establish `h1 : algebraMap O LL ((l : ℕ) : O) = 0` using `by rw [h, map_zero]`. Rewrite `h1` using `[map_natCast]`.

Establish `h2 : ((l : ℕ) : LL) = algebraMap ℚ_[l] LL (l : ℚ_[l])` using `by rw [map_natCast]`. Rewrite `h1` using `[h2]`. Conclude with `(Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) ((map_eq_zero_iff _ (algebraMap ℚ_[l] LL).injective).1 h1)`. Establish `hfq : ∀ r : ℕ, Finite (O ⧸ Ideal.span {((l : ℕ) : O) ^ r})` using `(GlobalTheory.GoodCoeff.good_coeff_integers l LL O hG).2.2.1`. Establish `hfq1 : Finite (O ⧸ Ideal.span {((l : ℕ) : O)})` using `by simpa using hfq 1`.

Establish `hsurj : ∀ y : H1V A.ρ, ∃ n : ℕ, ∃ x : LatticeCohomology LA, toH1V LA x = ((l : ℕ) : O) ^ n • y`. Introduce `y`. Take `⟨c, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Take `⟨n, hn⟩` from `pow_smul_mem_Z1T l K LL O hG A LA c.1 c.2`. Use `⟨n, Submodule.Quotient.mk ⟨_, hn⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[toH1V_mk]`. Both sides reduce to the same expression. Establish `hker : ∀ x : LatticeCohomology LA, toH1V LA x = 0 → ∃ n : ℕ, ((l : ℕ) : O) ^ n • x = 0`. Introduce `x hx`. Take `⟨c, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`.

Rewrite `hx` using `[toH1V_mk, Submodule.Quotient.mk_eq_zero]`. Take `⟨n, hn⟩` from `pow_smul_mem_B1T l K LL O hG A LA c.1 c.2 hx`. Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Conclude with `hn`.

Take `⟨hF, hr⟩` from `finite_finrank_of_localizes O LL (LatticeCohomology LA) (H1V A.ρ) (toH1V LA) _ hl0 hsurj hker`. Use `⟨hF, ?_⟩` and prove the remaining obligations. Rewrite using `[hr]`. Take `⟨C, hC, hb⟩` from `GlobalTheory.T.card_quot_pow_smul_bounds_dvr_fg_module O (LatticeCohomology LA) _ hl0 (not_isUnit_l l LL O hG) hfq`. Establish `e2 : ∀ r : ℕ, Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank O (LatticeCohomology LA)) = Nat.card (O ⧸ Ideal.span {((l : ℕ) : O) ^ r}) ^ finrank O (LatticeCohomology LA)`.

Introduce `r`. Rewrite using `[GlobalTheory.T.card_quot_span_pow_eq_card_pow_domain O _ hl0 hfq1 r, pow_mul]`. Use `⟨C, hC, fun r => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `(e2 r).trans_le (hb r).1`. Conclude with `(hb r).2.trans_eq (congrArg (C * ·) (e2 r).symm)`.
-/
theorem growth_H1T_dim_H1V : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), Module.Finite O (LatticeCohomology LA) → Module.Finite LL (H1V A.ρ) ∧ ∃ C : ℕ, 0 < C ∧ ∀ r : ℕ, Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL (H1V A.ρ)) ≤ Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) ∧ Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) ≤ C * Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL (H1V A.ρ)) := by
  intro l _ K LL _ _ _ O _ _ hG A LA hfin
  have hG' := hG
  obtain ⟨⟨hD, hDVR, hFr⟩, -, -, -, -⟩ := hG'
  haveI := hD
  haveI := hDVR
  haveI := hFr
  have hl0 : ((l : ℕ) : O) ≠ 0 := by
    intro h
    have h1 : algebraMap O LL ((l : ℕ) : O) = 0 := by rw [h, map_zero]
    rw [map_natCast] at h1
    have h2 : ((l : ℕ) : LL) = algebraMap ℚ_[l] LL (l : ℚ_[l]) := by rw [map_natCast]
    rw [h2] at h1
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) ((map_eq_zero_iff _ (algebraMap ℚ_[l] LL).injective).1 h1)
  have hfq : ∀ r : ℕ, Finite (O ⧸ Ideal.span {((l : ℕ) : O) ^ r}) :=
    (GlobalTheory.GoodCoeff.good_coeff_integers l LL O hG).2.2.1
  have hfq1 : Finite (O ⧸ Ideal.span {((l : ℕ) : O)}) := by simpa using hfq 1
  have hsurj : ∀ y : H1V A.ρ, ∃ n : ℕ, ∃ x : LatticeCohomology LA, toH1V LA x = ((l : ℕ) : O) ^ n • y := by
    intro y
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨n, hn⟩ := pow_smul_mem_Z1T l K LL O hG A LA c.1 c.2
    refine ⟨n, Submodule.Quotient.mk ⟨_, hn⟩, ?_⟩
    rw [toH1V_mk]
    rfl
  have hker : ∀ x : LatticeCohomology LA, toH1V LA x = 0 → ∃ n : ℕ, ((l : ℕ) : O) ^ n • x = 0 := by
    intro x hx
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [toH1V_mk, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨n, hn⟩ := pow_smul_mem_B1T l K LL O hG A LA c.1 c.2 hx
    refine ⟨n, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hn
  obtain ⟨hF, hr⟩ := finite_finrank_of_localizes O LL (LatticeCohomology LA) (H1V A.ρ) (toH1V LA) _ hl0 hsurj hker
  refine ⟨hF, ?_⟩
  rw [hr]
  obtain ⟨C, hC, hb⟩ := GlobalTheory.T.card_quot_pow_smul_bounds_dvr_fg_module O (LatticeCohomology LA) _ hl0 (not_isUnit_l l LL O hG) hfq
  have e2 : ∀ r : ℕ, Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank O (LatticeCohomology LA)) = Nat.card (O ⧸ Ideal.span {((l : ℕ) : O) ^ r}) ^ finrank O (LatticeCohomology LA) := by
    intro r
    rw [GlobalTheory.T.card_quot_span_pow_eq_card_pow_domain O _ hl0 hfq1 r, pow_mul]
  refine ⟨C, hC, fun r => ⟨?_, ?_⟩⟩
  · exact (e2 r).trans_le (hb r).1
  · exact (hb r).2.trans_eq (congrArg (C * ·) (e2 r).symm)

end GlobalTheory.H1Rank
