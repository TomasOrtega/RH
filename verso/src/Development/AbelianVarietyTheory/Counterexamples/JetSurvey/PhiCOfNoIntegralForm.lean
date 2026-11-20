import Mathlib
import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.TraceFormDualSystem
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FunctionalValuesNonempty

noncomputable section
open NumberField Formalism.MainNotions.ModuliIntegralCharts
open GlobalTheory.LeastExponentCompare
open scoped Pointwise

namespace GlobalTheory.LeastExponentProbe

variable {E : Type} [Field E] [NumberField E] {cj : E → E}
variable {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]

def vals (b : SymB cj Y) : Set ℝ := {x | ∃ l : SymB cj Y →ₗ[ℝ] ℝ,
    (∀ β : SymB cj Y, (∀ a c, ∃ z : ℤ, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z) → ∃ z : ℤ, l β = z) ∧
    (∀ β : SymB cj Y, (∀ a, 0 ≤ (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a) → β ≠ 0 → 0 < l β) ∧ x = l b}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem phiC_def (b : SymB cj Y) : phiC cj b = sInf (vals b) := rfl

/- English proof (translation)
Rewrite using `[phiC_def]`. Establish `hb : b = 0` using `Subtype.ext (LinearMap.ext fun a => LinearMap.ext fun c => by`. Rewrite using `[Subsingleton.elim a 0]`. Use the proof step `simp)`. Establish `hsub : vals b ⊆ {0}`.

Introduce and unpack `x ⟨l, -, -, rfl⟩`. Rewrite using `[hb, map_zero]`. Conclude with `Set.mem_singleton _`. Apply the tactic sequence `rcases Set.subset_singleton_iff_eq.1 hsub with he | he <;> simp [he]`.
-/
theorem phiC_of_subsingleton [Subsingleton Y] (b : SymB cj Y) : phiC cj b = 0 := by
  rw [phiC_def]
  have hb : b = 0 := Subtype.ext (LinearMap.ext fun a => LinearMap.ext fun c => by
    rw [Subsingleton.elim a 0]; simp)
  have hsub : vals b ⊆ {0} := by
    rintro x ⟨l, -, -, rfl⟩
    rw [hb, map_zero]
    exact Set.mem_singleton _
  rcases Set.subset_singleton_iff_eq.1 hsub with he | he <;> simp [he]

/- English proof (translation)
Take `⟨l, h1, h2, rfl⟩` from `hx`. Use `⟨(n : ℝ) • l, fun β hβ => ?_, fun β hβ hne => ?_, by simp⟩` and prove the remaining obligations. Take `⟨z, hz⟩` from `h1 β hβ`. Conclude with `⟨n * z, by simp [hz]⟩`. Establish `hl` using `h2 β hβ hne`.

Establish `hn' : (0 : ℝ) < n` using `by exact_mod_cast hn`. Simplify using `using mul_pos hn' hl`.
-/
private lemma nat_mul_mem_vals {b : SymB cj Y} {x : ℝ} (hx : x ∈ vals b) (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * x ∈ vals b := by
  obtain ⟨l, h1, h2, rfl⟩ := hx
  refine ⟨(n : ℝ) • l, fun β hβ => ?_, fun β hβ hne => ?_, by simp⟩
  · obtain ⟨z, hz⟩ := h1 β hβ
    exact ⟨n * z, by simp [hz]⟩
  · have hl := h2 β hβ hne
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    simpa using mul_pos hn' hl

/- English proof (translation)
Rewrite using `[phiC_def]`. Apply `Real.sInf_of_not_bddBelow` to reduce the goal to its premises. Introduce and unpack `⟨m, hm⟩`. Take `⟨n, hn⟩` from `exists_nat_gt (m / x)`. Establish `hmem` using `nat_mul_mem_vals hx (n + 1) n.succ_pos`.

Establish `h1 : m ≤ ((n + 1 : ℕ) : ℝ) * x` using `hm hmem`. Establish `h2 : ((n + 1 : ℕ) : ℝ) * x < m`. Rewrite using `[← div_lt_iff_of_neg hneg]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem phiC_eq_zero_of_neg (b : SymB cj Y) {x : ℝ} (hx : x ∈ vals b) (hneg : x < 0) : phiC cj b = 0 := by
  rw [phiC_def]
  apply Real.sInf_of_not_bddBelow
  rintro ⟨m, hm⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (m / x)
  have hmem := nat_mul_mem_vals hx (n + 1) n.succ_pos
  have h1 : m ≤ ((n + 1 : ℕ) : ℝ) * x := hm hmem
  have h2 : ((n + 1 : ℕ) : ℝ) * x < m := by
    rw [← div_lt_iff_of_neg hneg]
    push_cast
    linarith
  linarith

/- English proof (translation)
Use `eq_bot_iff.2 fun β hβ => (Submodule.mem_bot ℝ).2 ?_` and prove the remaining obligations. Establish `hb` using `hβ.2 1 0 (by simp [h])`. Use extensionality with `a c`. Simplify using `using hb a c`.
-/
theorem symB_eq_bot_of_apply_one (h : cj 1 = 0) : SymB cj Y = ⊥ := by
  refine eq_bot_iff.2 fun β hβ => (Submodule.mem_bot ℝ).2 ?_
  have hb := hβ.2 1 0 (by simp [h])
  ext a c
  simpa using hb a c

/- English proof (translation)
Take `⟨l, h1, h2, rfl⟩` from `hx`. Use `⟨c • l, fun β hβ => ⟨0, ?_⟩, fun β hβ hne => ?_, by simp⟩` and prove the remaining obligations. Rewrite using `[h β hβ]`. Simplify using the standard rewrite rules. Simplify using `using mul_pos hc (h2 β hβ hne)`.
-/
private lemma pos_mul_mem_vals_of_integral_eq_zero (h : ∀ β : SymB cj Y, (∀ a c, ∃ z : ℤ, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z) → β = 0)
    {b : SymB cj Y} {x : ℝ} (hx : x ∈ vals b) {c : ℝ} (hc : 0 < c) : c * x ∈ vals b := by
  obtain ⟨l, h1, h2, rfl⟩ := hx
  refine ⟨c • l, fun β hβ => ⟨0, ?_⟩, fun β hβ hne => ?_, by simp⟩
  · rw [h β hβ]
    simp
  · simpa using mul_pos hc (h2 β hβ hne)

/- English proof (translation)
Distinguish the cases in `hneg : ∃ x ∈ vals b, x < 0`. Take `⟨x, hx, hx0⟩` from `hneg`. Conclude with `phiC_eq_zero_of_neg b hx hx0`. Use `push_neg at hneg`. Establish `hbdd : BddBelow (vals b)` using `⟨0, fun y hy => hneg y hy⟩`.

Rewrite using `[phiC_def]`. Break down `(vals b).eq_empty_or_nonempty with he | hne` into its components or cases. Rewrite using `[he, Real.sInf_empty]`. Use `le_antisymm ?_ (le_csInf hne fun y hy => hneg y hy)` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`.

Use `push_neg at hlt`. Take `⟨x, hx⟩` from `hne`. Establish `hxs : sInf (vals b) ≤ x` using `csInf_le hbdd hx`. Establish `hxpos : 0 < x` using `lt_of_lt_of_le hlt hxs`. Establish `hc : 0 < sInf (vals b) / (2 * x)` using `by positivity`.

Establish `hmem` using `pos_mul_mem_vals_of_integral_eq_zero h hx hc`. Establish `hle` using `csInf_le hbdd hmem`. Establish `hx0 : x ≠ 0` using `hxpos.ne'`. Establish `heq : sInf (vals b) / (2 * x) * x = sInf (vals b) / 2`. Clear the denominators using the available nonvanishing facts.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem phiC_of_no_integral_form
    (h : ∀ β : SymB cj Y, (∀ a c, ∃ z : ℤ, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z) → β = 0) (b : SymB cj Y) :
    phiC cj b = 0 := by
  by_cases hneg : ∃ x ∈ vals b, x < 0
  · obtain ⟨x, hx, hx0⟩ := hneg
    exact phiC_eq_zero_of_neg b hx hx0
  push_neg at hneg
  have hbdd : BddBelow (vals b) := ⟨0, fun y hy => hneg y hy⟩
  rw [phiC_def]
  rcases (vals b).eq_empty_or_nonempty with he | hne
  · rw [he, Real.sInf_empty]
  refine le_antisymm ?_ (le_csInf hne fun y hy => hneg y hy)
  by_contra hlt
  push_neg at hlt
  obtain ⟨x, hx⟩ := hne
  have hxs : sInf (vals b) ≤ x := csInf_le hbdd hx
  have hxpos : 0 < x := lt_of_lt_of_le hlt hxs
  have hc : 0 < sInf (vals b) / (2 * x) := by positivity
  have hmem := pos_mul_mem_vals_of_integral_eq_zero h hx hc
  have hle := csInf_le hbdd hmem
  have hx0 : x ≠ 0 := hxpos.ne'
  have heq : sInf (vals b) / (2 * x) * x = sInf (vals b) / 2 := by
    field_simp
  linarith

/- English proof (translation)
Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨l, h1, h2, hx⟩`. Conclude with `⟨l, ⟨h1, h2⟩, hx⟩`. Introduce and unpack `⟨l, ⟨h1, h2⟩, hx⟩`.

Conclude with `⟨l, h1, h2, hx⟩`.
-/
private lemma vals_eq_functionalValues [IsCMField E] (b : SymB cj Y) : vals b = functionalValues b := by
  ext x
  constructor
  · rintro ⟨l, h1, h2, hx⟩
    exact ⟨l, ⟨h1, h2⟩, hx⟩
  · rintro ⟨l, ⟨h1, h2⟩, hx⟩
    exact ⟨l, h1, h2, hx⟩

section CM

variable [IsCMField E] [Module.Finite (𝓞 E) Y] [Module.Projective (𝓞 E) Y]

/- English proof (translation)
Rewrite using `[phiC_def]`. Use `le_csInf (by rw [vals_eq_functionalValues]; exact functionalValues_nonempty h b) ?_` and prove the remaining obligations. Introduce and unpack `x ⟨l, h1, h2, rfl⟩`. Take `⟨z, hz⟩` from `h1 b hint`. Establish `hp` using `h2 b hpos h0`.

Rewrite `hp`, the goal using `[hz]`. Establish `hz0 : (0 : ℤ) < z` using `by exact_mod_cast hp`. Conclude with `(show (1 : ℤ) ≤ z by omega)` after adjusting the coercions.
-/
theorem one_le_phiC (h : IsConj cj) (b : SymB cj Y)
    (hint : ∀ a c, ∃ z : ℤ, (b : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z)
    (hpos : ∀ a, 0 ≤ (b : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a) (h0 : b ≠ 0) : 1 ≤ phiC cj b := by
  rw [phiC_def]
  refine le_csInf (by rw [vals_eq_functionalValues]; exact functionalValues_nonempty h b) ?_
  rintro x ⟨l, h1, h2, rfl⟩
  obtain ⟨z, hz⟩ := h1 b hint
  have hp := h2 b hpos h0
  rw [hz] at hp ⊢
  have hz0 : (0 : ℤ) < z := by exact_mod_cast hp
  exact_mod_cast (show (1 : ℤ) ≤ z by omega)

def trForm (h : IsConj cj) : SymB cj (𝓞 E) := (formsEquiv (𝓞 E) h).symm (GlobalTheory.IndefiniteRowSideFullHecke.TraceFormDualSystem.traceForm E)

end CM

end GlobalTheory.LeastExponentProbe

end
