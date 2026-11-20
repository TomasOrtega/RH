import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KatzQuasiIntegralCriterionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesReductionModPrimeRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionCommutesFormalGroupLawCoboundariesStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz

/- English proof (translation)
Distinguish the cases in `h0 : a = 0`. Conclude with `⟨0, by simp [h0]⟩`. Take `⟨m, b, hb, rfl⟩` from `WittVector.exists_eq_pow_p_mul a h0`. Consider the cases of `m with`. Consider the case `zero => exfalso`.

Apply `hb` to reduce the goal to its premises. Simplify using `using ha`. Consider the case `succ m => exact ⟨(p : WittVector p k) ^ m * b, by ring⟩`.
-/
theorem exists_p_mul_of_constantCoeff_eq_zero (p : ℕ) [Fact p.Prime] {k : Type} [Field k]
    [CharP k p] [PerfectRing k p] (a : WittVector p k) (ha : WittVector.constantCoeff a = 0) :
    ∃ c : WittVector p k, a = (p : WittVector p k) * c := by
  by_cases h0 : a = 0
  · exact ⟨0, by simp [h0]⟩
  obtain ⟨m, b, hb, rfl⟩ := WittVector.exists_eq_pow_p_mul a h0
  cases m with
  | zero =>
    exfalso; apply hb
    simpa using ha
  | succ m => exact ⟨(p : WittVector p k) ^ m * b, by ring⟩

/- English proof (translation)
Use `formalCoboundary_add h (f - g) g` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Rewrite using `[this]`. Normalize the expressions using the abelian group laws.
-/
theorem formalGroupLawCoboundaryOne_sub_eq {R : Type} [CommRing R] {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (h : ∀ i, constantCoeff (μ i) = 0) (f g : MvPowerSeries (Fin d) R) :
    cob1 μ (f - g) = cob1 μ f - cob1 μ g := by
  have := formalCoboundary_add h (f - g) g
  rw [sub_add_cancel] at this
  rw [this]; abel

/- English proof (translation)
Introduce `p _ k _ _ _ d μ h f hf b hcf hlf`. Take `⟨R1, -, R3, R4, -, R6, ZariskiNoetherianInduction⟩` from `GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d)`. Take `⟨-, R1', -, -⟩` from `GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d ⊕ Fin d)`. Establish `hL : ∀ i, constantCoeff (Katz.lift p (μ i)) = 0` using `fun i => constantCoeff_lift p (h.const i)`. Take `⟨-, C2, -, -⟩` from `GlobalTheory.T.reduction_commutes_formalGroupLawCoboundaries p k d μ h.const`.

Take `⟨hcb, hlb⟩` from `C2 (Katz.lift p b) b (R3 b)`. Use `set f' := f - Katz.lift p b with hf'`. Establish `hc' : cob1 (fun i => Katz.lift p (μ i)) f' ∈ intBy p k (Fin d ⊕ Fin d) (p : WittVector p k)`. Take `⟨-, -, -, S4, -, S6, -⟩` from `GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d ⊕ Fin d)`. Rewrite using `[S6, hf', formalGroupLawCoboundaryOne_sub_eq hL]`.

Use `(S4 _ _ _ _ hcf hcb).2` as an intermediate fact. Rewrite `this` using `[sub_self]`. Then use the resulting hypothesis. Take `⟨-, -, -, -, -, -, S7⟩` from `GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d ⊕ Fin d)`. Take `⟨c0, hc0, hc0e⟩` from `(S7 _ _).1 hc'`. Establish `hpW : (p : WittVector p k) ≠ 0` using `WittVector.p_nonzero p k`.

Establish `hpF : (p : Fr p k) ≠ 0`. Establish `: (p : Fr p k) = algebraMap (WittVector p k) (Fr p k) (p : WittVector p k)` using `by simp`. Rewrite using `[this]`. Conclude with `fun h0 => hpW (IsFractionRing.injective (WittVector p k) (Fr p k) (by simpa using h0))`. Establish `hsm : ∀ {σ : Type} (x : MvPowerSeries σ (Fr p k)), (p : WittVector p k) • x = (p : Fr p k) • x`.

Introduce `σ x`. Rewrite using `[← algebraMap_smul (Fr p k) (p : WittVector p k) x]`. Simplify using the standard rewrite rules. Establish `hcg : cob1 (fun i => Katz.lift p (μ i)) ((p : Fr p k)⁻¹ • f') ∈ intBy p k _ 1`. Rewrite using `[formalCoboundary_smul hL, hc0e, hsm, smul_smul, inv_mul_cancel₀ hpF, one_smul]`.

Conclude with `hc0`. Use `⟨(p : Fr p k)⁻¹ • f', ⟨?_, hcg⟩, ?_⟩` and prove the remaining obligations. Apply `GlobalTheory.T.katz_quasi_integral_criterion p k d μ h _ _ hcg` to reduce the goal to its premises. Introduce `i`. Take `⟨a, ha, ha0⟩` from `hlf i`.

Take `⟨a', ha', ha0'⟩` from `hlb i`. Take `⟨c, hc⟩` from `exists_p_mul_of_constantCoeff_eq_zero p (a - a') (by`. Rewrite using `[map_sub, ha0, ha0', sub_self])`. Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `e1 : lin f' i = algebraMap (WittVector p k) (Fr p k) (a - a')`.

Simplify using `only [lin, hf', map_sub] at ha ha' ⊢`. Rewrite using `[ha, ha']`. Establish `e2 : lin ((p : Fr p k)⁻¹ • f') i = (p : Fr p k)⁻¹ * lin f' i`. Simplify using `[lin]`. Rewrite using `[e2, e1, hc, map_mul]`.

Simplify using `[hpF]`. Rewrite using `[hsm, smul_smul, mul_inv_cancel₀ hpF, one_smul, hf', sub_sub_cancel]`. Conclude with `(R1 _).2 ⟨b, R3 b⟩`.
-/
theorem quasiLog_eq_p_smul_add_int : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : IsLaw μ),
    ∀ f ∈ quasiLog p h, ∀ b, Red p (cob1 (fun i => Katz.lift p (μ i)) f) (cob1 μ b) →
      RedV p (lin f) (lin b) →
      ∃ g ∈ quasiLog p h, f - (p : WittVector p k) • g ∈ intBy p k (Fin d) 1 := by
  intro p _ k _ _ _ d μ h f hf b hcf hlf
  obtain ⟨R1, -, R3, R4, -, R6, ZariskiNoetherianInduction⟩ := GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d)
  obtain ⟨-, R1', -, -⟩ := GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d ⊕ Fin d)
  have hL : ∀ i, constantCoeff (Katz.lift p (μ i)) = 0 := fun i => constantCoeff_lift p (h.const i)
  obtain ⟨-, C2, -, -⟩ := GlobalTheory.T.reduction_commutes_formalGroupLawCoboundaries p k d μ h.const
  obtain ⟨hcb, hlb⟩ := C2 (Katz.lift p b) b (R3 b)
  set f' := f - Katz.lift p b with hf'

  have hc' : cob1 (fun i => Katz.lift p (μ i)) f' ∈ intBy p k (Fin d ⊕ Fin d) (p : WittVector p k) := by
    obtain ⟨-, -, -, S4, -, S6, -⟩ := GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d ⊕ Fin d)
    rw [S6, hf', formalGroupLawCoboundaryOne_sub_eq hL]
    have := (S4 _ _ _ _ hcf hcb).2
    rwa [sub_self] at this
  obtain ⟨-, -, -, -, -, -, S7⟩ := GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d ⊕ Fin d)
  obtain ⟨c0, hc0, hc0e⟩ := (S7 _ _).1 hc'
  have hpW : (p : WittVector p k) ≠ 0 := WittVector.p_nonzero p k
  have hpF : (p : Fr p k) ≠ 0 := by
    have : (p : Fr p k) = algebraMap (WittVector p k) (Fr p k) (p : WittVector p k) := by simp
    rw [this]
    exact fun h0 => hpW (IsFractionRing.injective (WittVector p k) (Fr p k) (by simpa using h0))
  have hsm : ∀ {σ : Type} (x : MvPowerSeries σ (Fr p k)),
      (p : WittVector p k) • x = (p : Fr p k) • x := by
    intro σ x
    rw [← algebraMap_smul (Fr p k) (p : WittVector p k) x]
    simp
  have hcg : cob1 (fun i => Katz.lift p (μ i)) ((p : Fr p k)⁻¹ • f') ∈ intBy p k _ 1 := by
    rw [formalCoboundary_smul hL, hc0e, hsm, smul_smul, inv_mul_cancel₀ hpF, one_smul]
    exact hc0
  refine ⟨(p : Fr p k)⁻¹ • f', ⟨?_, hcg⟩, ?_⟩
  · apply GlobalTheory.T.katz_quasi_integral_criterion p k d μ h _ _ hcg
    intro i
    obtain ⟨a, ha, ha0⟩ := hlf i
    obtain ⟨a', ha', ha0'⟩ := hlb i
    obtain ⟨c, hc⟩ := exists_p_mul_of_constantCoeff_eq_zero p (a - a') (by
      rw [map_sub, ha0, ha0', sub_self])
    refine ⟨c, ?_⟩
    have e1 : lin f' i = algebraMap (WittVector p k) (Fr p k) (a - a') := by
      simp only [lin, hf', map_sub] at ha ha' ⊢
      rw [ha, ha']
    have e2 : lin ((p : Fr p k)⁻¹ • f') i = (p : Fr p k)⁻¹ * lin f' i := by
      simp [lin]
    rw [e2, e1, hc, map_mul]
    simp [hpF]
  · rw [hsm, smul_smul, mul_inv_cancel₀ hpF, one_smul, hf', sub_sub_cancel]
    exact (R1 _).2 ⟨b, R3 b⟩

end GlobalTheory.Katz
