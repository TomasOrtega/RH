import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvFilD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSumsTwistsCharactersExpectedJumps
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory.FilInv

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using PD.one_mem`. Consider the case `succ n ih`. Rewrite using `[pow_succ, Nat.cast_succ, add_mul, one_mul]`. Conclude with `PD.Fil_mul _ _ _ _ ih hx`.
-/
theorem pow_mem_Fil {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {b : ℤ} {x : BdR} (hx : x ∈ PD.Fil b) (n : ℕ) :
    x ^ n ∈ PD.Fil (n * b) := by
  induction n with
  | zero => simpa using PD.one_mem
  | succ n ih =>
    rw [pow_succ, Nat.cast_succ, add_mul, one_mul]
    exact PD.Fil_mul _ _ _ _ ih hx

/- English proof (translation)
Introduce `l _ P AI T K a u v huv hu hu1`. Take `⟨s, hs, hts⟩` from `GlobalTheory.TopSteps.CrysRules.exists_inverse_fontaineElement_mem_fil_neg_one T K`. Establish `ht` using `(P.PD K).mem_filtration_one`. Choose the witnesses or unpack the hypotheses as in `⟨w, w', hw, hw', hww⟩ : ∃ w w' : P.R.BdR, w ∈ (P.PD K).Fil (-a) ∧ w' ∈ (P.PD K).Fil a ∧ w * w' = 1 := by`. Take `⟨n, rfl | rfl⟩` from `Int.eq_nat_or_neg a`.

Use `⟨s ^ n, ((P.PD K).ι (P.PD K).t) ^ n, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `using pow_mem_Fil (P.PD K) hs n`. Simplify using `using pow_mem_Fil (P.PD K) ht n`. Rewrite using `[← mul_pow, mul_comm, hts, one_pow]`. Use `⟨((P.PD K).ι (P.PD K).t) ^ n, s ^ n, ?_, ?_, ?_⟩` and prove the remaining obligations.

Simplify using `using pow_mem_Fil (P.PD K) ht n`. Simplify using `using pow_mem_Fil (P.PD K) hs n`. Rewrite using `[← mul_pow, hts, one_pow]`. Establish `hx0 : u * w ∈ (P.PD K).Fil 0`. Simplify using `using (P.PD K).Fil_mul _ _ _ _ hu hw`.

Establish `hx1 : u * w ∉ (P.PD K).Fil 1`. Introduce `h`. Apply `hu1` to reduce the goal to its premises. Use `(P.PD K).Fil_mul _ _ _ _ h hw'` as an intermediate fact. Rewrite `this` using `[mul_assoc, hww, mul_one, add_comm]`. Then use the resulting hypothesis.

Take `⟨y, hy, hxy⟩` from `((GlobalTheory.Per.TiedField.tied_field l P AI T).2.2.2.2) K _ hx0 hx1`. Establish `hv : v = w * y`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hv]`. Simplify using `using (P.PD K).Fil_mul _ _ _ _ hw hy`.
-/
theorem inv_mem_Fil_neg : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (a : ℤ) (u v : P.R.BdR), u * v = 1 → u ∈ (P.PD K).Fil a → u ∉ (P.PD K).Fil (a + 1) → v ∈ (P.PD K).Fil (-a) := by
  intro l _ P AI T K a u v huv hu hu1
  obtain ⟨s, hs, hts⟩ := GlobalTheory.TopSteps.CrysRules.exists_inverse_fontaineElement_mem_fil_neg_one T K
  have ht := (P.PD K).mem_filtration_one

  obtain ⟨w, w', hw, hw', hww⟩ : ∃ w w' : P.R.BdR, w ∈ (P.PD K).Fil (-a) ∧ w' ∈ (P.PD K).Fil a ∧
      w * w' = 1 := by
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg a
    · refine ⟨s ^ n, ((P.PD K).ι (P.PD K).t) ^ n, ?_, ?_, ?_⟩
      · simpa using pow_mem_Fil (P.PD K) hs n
      · simpa using pow_mem_Fil (P.PD K) ht n
      · rw [← mul_pow, mul_comm, hts, one_pow]
    · refine ⟨((P.PD K).ι (P.PD K).t) ^ n, s ^ n, ?_, ?_, ?_⟩
      · simpa using pow_mem_Fil (P.PD K) ht n
      · simpa using pow_mem_Fil (P.PD K) hs n
      · rw [← mul_pow, hts, one_pow]
  have hx0 : u * w ∈ (P.PD K).Fil 0 := by
    simpa using (P.PD K).Fil_mul _ _ _ _ hu hw
  have hx1 : u * w ∉ (P.PD K).Fil 1 := by
    intro h
    apply hu1
    have := (P.PD K).Fil_mul _ _ _ _ h hw'
    rwa [mul_assoc, hww, mul_one, add_comm] at this
  obtain ⟨y, hy, hxy⟩ := ((GlobalTheory.Per.TiedField.tied_field l P AI T).2.2.2.2) K _ hx0 hx1
  have hv : v = w * y := by
    calc v = v * ((u * w) * y) := by rw [hxy, mul_one]
      _ = (u * v) * (w * y) := by ring
      _ = w * y := by rw [huv, one_mul]
  rw [hv]
  simpa using (P.PD K).Fil_mul _ _ _ _ hw hy

end GlobalTheory.FilInv
