import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicNormZpowSubOnePadicValInt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormUnitPowSubOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicFrobeniusTwistedValueEqPowMulStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualExpTeichmullerPowerSumFormulaStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerFrobeniusFormulaPosWeightStatement
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

noncomputable section

namespace GlobalTheory.ExpImage

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Rewrite using `[norm_mul, PadicAlgCl.norm_extends]`.
-/
theorem norm_algebraMap_mul (κ : ℚ_[l]) (α : Om l) :
    ‖algebraMap ℚ_[l] (Om l) κ * α‖ = ‖κ‖ * ‖α‖ := by
  rw [norm_mul, PadicAlgCl.norm_extends]

/- English proof (translation)
Establish `hn : ‖((1 + l ^ s : ℕ) : ℚ_[l]) - 1‖ = (l : ℝ) ^ (-(s : ℤ))`. Use `push_cast`. Rewrite using `[add_sub_cancel_left, Padic.norm_p_pow]`. Establish `hu : ‖((1 + l ^ s : ℕ) : ℚ_[l])‖ = 1`. Rewrite using `[Padic.norm_natCast_eq_one_iff]`.

Take `⟨k, hk⟩` from `Nat.exists_eq_add_of_le' hs.1`. Rewrite using `[hk, pow_succ]`. Simplify using the standard rewrite rules. Take `⟨g, hg, hχ⟩` from `(GlobalTheory.Cyc.finrank_Ks_and_chi_surjective l K).2 P.χQ P.χQ_cyc _ hu`. Conclude with `⟨g, (((GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc).2.2 K g hg).1 s).2 (by rw [hχ, hn]), hχ⟩`.
-/
theorem exists_gen (P : LocPrime l) (K : FinExt l) {s : ℕ} (hs : Lev l s) :
    ∃ g ∈ Gj K s, (P.χQ g : ℚ_[l]) = ((1 + l ^ s : ℕ) : ℚ_[l]) := by
  have hn : ‖((1 + l ^ s : ℕ) : ℚ_[l]) - 1‖ = (l : ℝ) ^ (-(s : ℤ)) := by
    push_cast
    rw [add_sub_cancel_left, Padic.norm_p_pow]
  have hu : ‖((1 + l ^ s : ℕ) : ℚ_[l])‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff]
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' hs.1
    rw [hk, pow_succ]
    simp
  obtain ⟨g, hg, hχ⟩ := (GlobalTheory.Cyc.finrank_Ks_and_chi_surjective l K).2 P.χQ P.χQ_cyc _ hu
  exact ⟨g, (((GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc).2.2 K g hg).1 s).2 (by rw [hχ, hn]), hχ⟩

/- English proof (translation)
Introduce `D l _ K s hs e α hα hα1`. Take `⟨g, hg, hχ⟩` from `exists_gen (D.loc l) K hs`. Use `set u : ℚ_[l] := ((1 + l ^ s : ℕ) : ℚ_[l]) with hu`. Establish `hl0 : (l : ℚ_[l]) ≠ 0` using `by exact_mod_cast (Fact.out : l.Prime).ne_zero`. Establish `hlr : (0 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).pos`.

Establish `hn : ‖u - 1‖ = (l : ℝ) ^ (-(s : ℤ))`. Rewrite using `[hu]`. Use `push_cast`. Rewrite using `[add_sub_cancel_left, Padic.norm_p_pow]`. Establish `hlog : ‖logZl l u‖ = (l : ℝ) ^ (-(s : ℤ))`.

Rewrite using `[(GlobalTheory.PadicLogUnits.logZl_hom l).2.2.2 s hs.1 hs.2 u hn.le, hn]`. Establish `key : ∀ ρ : ℚ_[l], ‖ρ‖ = (l : ℝ) ^ (((e + 1) * (s - 1) : ℕ) - betaE l s e) → (∀ (lam : ℕ → ↥(K0 K)) (d : ↥(K0 K)), (∀ a, ‖(lam a : Om l)‖ ≤ 1) → ‖(d : Om l)‖ ≤ 1 → d - (l : ↥(K0 K)) ^ e * frK (D.loc l) K d = (frK (D.loc l) K ^ s) (∑ a ∈ primeTo l s, lam a) → ∃ z : GQ l → ℚ_[l], ( …`. Introduce `ρ hρ H`. Establish `hρ0 : ρ ≠ 0`. Rewrite using `[← norm_ne_zero_iff, hρ]`.

Conclude with `(zpow_pos hlr _).ne'`. Use `set κ : ℚ_[l] := (l : ℚ_[l]) ^ (betaE l s e) / (ρ * (l : ℚ_[l]) ^ ((e + 1) * (s - 1))) with hκ`. Establish `hκ1 : ‖κ‖ = 1`. Rewrite using `[hκ, norm_div, norm_mul, hρ, Padic.norm_p_zpow, Padic.norm_p_pow, ← zpow_add₀ hlr.ne', div_eq_one_iff_eq (zpow_pos hlr _).ne']`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨lam, d, h1, h2, h3, h4⟩` from `GlobalTheory.T.exists_cyclotomicFrobeniusTwistedValue_eq_pow_mul l (D.loc l) K s e hs.1 (algebraMap ℚ_[l] (Om l) κ * α) (mul_mem (IntermediateField.algebraMap_mem _ _) hα) (by rw [norm_algebraMap_mul, hκ1, one_mul]; exact hα1)`. Take `⟨z, hz, hE⟩` from `H lam d h1 h2 h3`. Use `⟨z, hz, ?_⟩` and prove the remaining obligations. Use `hE using 1` and compare the differences between its conclusion and the goal.

Establish `: ρ * (l : ℚ_[l]) ^ ((e + 1) * (s - 1)) * κ = (l : ℚ_[l]) ^ (betaE l s e)`. Rewrite using `[hκ]`. Clear the denominators using the available nonvanishing facts. Establish `h5` using `congrArg (algebraMap ℚ_[l] (Om l)) this`. Rewrite `h5` using `[map_mul, map_mul, map_pow, map_zpow₀, map_natCast]`.

Rewrite using `[h4, ← h5]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨s', rfl⟩` from `Nat.exists_eq_add_of_le' hs.1`. Break down `Nat.eq_zero_or_pos e with rfl | he` into its components or cases. Use `key (logZl l u * (((0 : ℕ).factorial : ℚ_[l]) * (l : ℚ_[l]) ^ ((s' + 1) * 0)))⁻¹ ?_ ?_` and prove the remaining obligations.

Simplify using `only [Nat.factorial_zero, Nat.cast_one, mul_zero, pow_zero, mul_one, norm_inv, hlog, betaE]`. Rewrite using `[← zpow_neg]`. Use `congr 1`. Simplify using the standard rewrite rules. Introduce `lam d h1 h2 h3`.

Use `GlobalTheory.T.dualExp_teichmuller_power_sum_formula D.loc l (D.locA l) (D.locT l) K (s' + 1) hs 0 g hg hχ ℕ (primeTo l (s' + 1)) lam id (fun _ => d) (fun i hi => ⟨h1 i, (Finset.mem_filter.1 hi).2⟩) (fun j hj => by` as an intermediate fact. Take `rfl : j = 0` from `Nat.le_zero.1 hj`. Conclude with `⟨h2, by simpa using h3⟩)`. Use `this using 5` and compare the differences between its conclusion and the goal. Simplify using `[cycVal, levSum]`.

Use `key _ ?_ (GlobalTheory.T.cyclotomicTower_frobenius_formula_pos_weight D.loc l (D.locA l) (D.locT l) K (s' + 1) hs e he g hg hχ)` and prove the remaining obligations. Take `⟨e', rfl⟩` from `Nat.exists_eq_add_of_le' he`. Establish `h6` using `GlobalTheory.Cyc.LiftExp.norm_zpow_sub_one l (s' + 1) hs u hn ((e' + 1 : ℕ) : ℤ) (by omega)`. Rewrite `h6` using `[zpow_natCast, padicValInt.of_nat]`. Establish `h7 : ‖(((e' + 1).factorial : ℕ) : ℚ_[l])‖ = (l : ℝ) ^ (-((padicValNat l (e' + 1) : ℤ) + (padicValNat l e'.factorial : ℤ)))`.

Rewrite using `[Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast (e' + 1).factorial_ne_zero), Padic.valuation_natCast, Nat.factorial_succ, padicValNat.mul (Nat.succ_ne_zero _) e'.factorial_ne_zero]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[← hu, norm_div, norm_mul, norm_mul, h6, hlog, h7, Padic.norm_p_pow, ← zpow_add₀ hlr.ne', ← zpow_add₀ hlr.ne', ← zpow_sub₀ hlr.ne']`. Use `congr 1`.

Simplify using `only [betaE, Nat.add_sub_cancel, Nat.succ_ne_zero, if_false]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem expStar_image : ∀ (D : Formalism.BasicNotions.D7) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ), Lev l s → ∀ e : ℕ, ∀ α : Om l, α ∈ Ks K s → ‖α‖ ≤ 1 → ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar D.loc (Gj K s) e z ((l : Om l) ^ (betaE l s e) * α) := by
  intro D l _ K s hs e α hα hα1
  obtain ⟨g, hg, hχ⟩ := exists_gen (D.loc l) K hs
  set u : ℚ_[l] := ((1 + l ^ s : ℕ) : ℚ_[l]) with hu
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hlr : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hn : ‖u - 1‖ = (l : ℝ) ^ (-(s : ℤ)) := by
    rw [hu]
    push_cast
    rw [add_sub_cancel_left, Padic.norm_p_pow]
  have hlog : ‖logZl l u‖ = (l : ℝ) ^ (-(s : ℤ)) := by
    rw [(GlobalTheory.PadicLogUnits.logZl_hom l).2.2.2 s hs.1 hs.2 u hn.le, hn]
  have key : ∀ ρ : ℚ_[l], ‖ρ‖ = (l : ℝ) ^ (((e + 1) * (s - 1) : ℕ) - betaE l s e) →
      (∀ (lam : ℕ → ↥(K0 K)) (d : ↥(K0 K)), (∀ a, ‖(lam a : Om l)‖ ≤ 1) → ‖(d : Om l)‖ ≤ 1 →
        d - (l : ↥(K0 K)) ^ e * frK (D.loc l) K d = (frK (D.loc l) K ^ s) (∑ a ∈ primeTo l s, lam a) →
        ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar D.loc (Gj K s) e z
          (algebraMap ℚ_[l] (Om l) ρ * cycVal (D.loc l) K s e lam d)) →
      ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧
        ExpStar D.loc (Gj K s) e z ((l : Om l) ^ (betaE l s e) * α) := by
    intro ρ hρ H
    have hρ0 : ρ ≠ 0 := by
      rw [← norm_ne_zero_iff, hρ]
      exact (zpow_pos hlr _).ne'
    set κ : ℚ_[l] := (l : ℚ_[l]) ^ (betaE l s e) / (ρ * (l : ℚ_[l]) ^ ((e + 1) * (s - 1))) with hκ
    have hκ1 : ‖κ‖ = 1 := by
      rw [hκ, norm_div, norm_mul, hρ, Padic.norm_p_zpow, Padic.norm_p_pow, ← zpow_add₀ hlr.ne',
        div_eq_one_iff_eq (zpow_pos hlr _).ne']
      congr 1
      ring
    obtain ⟨lam, d, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_cyclotomicFrobeniusTwistedValue_eq_pow_mul l (D.loc l) K s e hs.1 (algebraMap ℚ_[l] (Om l) κ * α)
      (mul_mem (IntermediateField.algebraMap_mem _ _) hα) (by rw [norm_algebraMap_mul, hκ1, one_mul]; exact hα1)
    obtain ⟨z, hz, hE⟩ := H lam d h1 h2 h3
    refine ⟨z, hz, ?_⟩
    convert hE using 1
    have : ρ * (l : ℚ_[l]) ^ ((e + 1) * (s - 1)) * κ = (l : ℚ_[l]) ^ (betaE l s e) := by
      rw [hκ]
      field_simp
    have h5 := congrArg (algebraMap ℚ_[l] (Om l)) this
    rw [map_mul, map_mul, map_pow, map_zpow₀, map_natCast] at h5
    rw [h4, ← h5]
    ring
  obtain ⟨s', rfl⟩ := Nat.exists_eq_add_of_le' hs.1
  rcases Nat.eq_zero_or_pos e with rfl | he
  · refine key (logZl l u * (((0 : ℕ).factorial : ℚ_[l]) * (l : ℚ_[l]) ^ ((s' + 1) * 0)))⁻¹ ?_ ?_
    · simp only [Nat.factorial_zero, Nat.cast_one, mul_zero, pow_zero, mul_one, norm_inv, hlog, betaE]
      rw [← zpow_neg]
      congr 1
      simp
    · intro lam d h1 h2 h3
      have := GlobalTheory.T.dualExp_teichmuller_power_sum_formula D.loc l (D.locA l) (D.locT l) K (s' + 1) hs 0 g hg hχ ℕ (primeTo l (s' + 1)) lam id
        (fun _ => d) (fun i hi => ⟨h1 i, (Finset.mem_filter.1 hi).2⟩)
        (fun j hj => by
          obtain rfl : j = 0 := Nat.le_zero.1 hj
          exact ⟨h2, by simpa using h3⟩)
      convert this using 5
      simp [cycVal, levSum]
  · refine key _ ?_ (GlobalTheory.T.cyclotomicTower_frobenius_formula_pos_weight D.loc l (D.locA l) (D.locT l) K (s' + 1) hs e he g hg hχ)
    obtain ⟨e', rfl⟩ := Nat.exists_eq_add_of_le' he
    have h6 := GlobalTheory.Cyc.LiftExp.norm_zpow_sub_one l (s' + 1) hs u hn ((e' + 1 : ℕ) : ℤ) (by omega)
    rw [zpow_natCast, padicValInt.of_nat] at h6
    have h7 : ‖(((e' + 1).factorial : ℕ) : ℚ_[l])‖ =
        (l : ℝ) ^ (-((padicValNat l (e' + 1) : ℤ) + (padicValNat l e'.factorial : ℤ))) := by
      rw [Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast (e' + 1).factorial_ne_zero),
        Padic.valuation_natCast, Nat.factorial_succ,
        padicValNat.mul (Nat.succ_ne_zero _) e'.factorial_ne_zero]
      push_cast
      rfl
    rw [← hu, norm_div, norm_mul, norm_mul, h6, hlog, h7, Padic.norm_p_pow, ← zpow_add₀ hlr.ne',
      ← zpow_add₀ hlr.ne', ← zpow_sub₀ hlr.ne']
    congr 1
    simp only [betaE, Nat.add_sub_cancel, Nat.succ_ne_zero, if_false]
    push_cast
    ring

end GlobalTheory.ExpImage
