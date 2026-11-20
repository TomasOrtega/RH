import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Use `⟨1, 1, by simp, by simp, ?_⟩` and prove the remaining obligations. Introduce `t ht _ i`. Establish `hi : i = Fin.last 0` using `Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)`.

Substitute `hi` using the available equality. Rewrite using `[ht]`. Simplify using the standard rewrite rules. Consider the case `succ m ih`. Take `⟨R1', R2', h1', h2', hR⟩` from `ih (fun j => r1 j.succ) (fun j => r2 j.succ)`.

Use `set a : kˣ := if valuation k (r1 0 : k) ≤ 1 then 1 else r1 0 with ha_def`. Use `set b : kˣ := if 1 ≤ valuation k (r2 0 : k) then 1 else r2 0 with hb_def`. Establish `ha1 : 1 ≤ valuation k (a : k)`. Rewrite using `[ha_def]`. Use `split_ifs with h`.

Simplify using the standard rewrite rules. Conclude with `le_of_lt (not_le.mp h)`. Establish `har : valuation k (r1 0 : k) ≤ valuation k (a : k)`. Rewrite using `[ha_def]`. Use `split_ifs with h`.

Simplify using `using h`. Conclude with `le_rfl`. Establish `hb1 : valuation k (b : k) ≤ 1`. Rewrite using `[hb_def]`. Use `split_ifs with h`.

Simplify using the standard rewrite rules. Conclude with `le_of_lt (not_le.mp h)`. Establish `hbr : valuation k (b : k) ≤ valuation k (r2 0 : k)`. Rewrite using `[hb_def]`. Use `split_ifs with h`.

Simplify using `using h`. Conclude with `le_rfl`. Use `⟨R1' * a, R2' * b, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Units.val_mul, map_mul]`. Conclude with `one_le_mul h1' ha1`.

Simplify using `only [Units.val_mul, map_mul]`. Conclude with `mul_le_one' h2' hb1`. Introduce `t ht hrat`. Establish `hT` using `hR (fun j => t j.succ) (by simp only [Fin.succ_last]; exact ht) (fun i => by`. Use `hrat i.succ` as an intermediate fact.

Rewrite `this` using `[← Fin.succ_castSucc]`. Conclude with `this)`. Establish `hR1le : valuation k (R1' : k) ≤ valuation k ((R1' * a : kˣ) : k)`. Simplify using `only [Units.val_mul, map_mul]`. Conclude with `le_mul_of_one_le_right' ha1`.

Establish `hR2le : valuation k ((R2' * b : kˣ) : k) ≤ valuation k (R2' : k)`. Simplify using `only [Units.val_mul, map_mul]`. Conclude with `mul_le_of_le_one_right' hb1`. Introduce `i`. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations.

Establish `h0` using `hrat 0`. Establish `ht1` using `hT 0`. Simplify using `only [Fin.castSucc_zero, Fin.succ_zero_eq_one] at h0 ht1`. Establish `hne : ((t 1 : kˣ) : k) ≠ 0` using `(t 1).ne_zero`. Establish `hsplit : ((t 0 : kˣ) : k) = ((t 0 : k) / t 1) * t 1` using `by field_simp`.

Rewrite using `[hsplit, map_mul]`. Prove the components needed by the constructor for the conclusion. Simplify using `only [Units.val_mul, map_mul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Units.val_mul, map_mul]`.

Combine the equalities or inequalities in the displayed calculation. Use `hT j` as an intermediate fact. Conclude with `⟨hR2le.trans this.1, this.2.trans hR1le⟩`.
-/
theorem valuation_chain_ratio_bounds (k : Type) [Field k] [ValuativeRel k] (m : ℕ) (r1 r2 : Fin m → kˣ) :
    ∃ R1 R2 : kˣ, 1 ≤ valuation k (R1 : k) ∧ valuation k (R2 : k) ≤ 1 ∧
      ∀ t : Fin (m + 1) → kˣ, t (Fin.last m) = 1 →
        (∀ i : Fin m, valuation k (r2 i : k) ≤ valuation k ((t i.castSucc : k) / t i.succ) ∧
          valuation k ((t i.castSucc : k) / t i.succ) ≤ valuation k (r1 i : k)) →
        ∀ i, valuation k (R2 : k) ≤ valuation k (t i : k) ∧ valuation k (t i : k) ≤ valuation k (R1 : k) := by
  induction m with
  | zero =>
    refine ⟨1, 1, by simp, by simp, ?_⟩
    intro t ht _ i
    have hi : i = Fin.last 0 := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
    subst hi
    rw [ht]; simp
  | succ m ih =>
    obtain ⟨R1', R2', h1', h2', hR⟩ := ih (fun j => r1 j.succ) (fun j => r2 j.succ)
    set a : kˣ := if valuation k (r1 0 : k) ≤ 1 then 1 else r1 0 with ha_def
    set b : kˣ := if 1 ≤ valuation k (r2 0 : k) then 1 else r2 0 with hb_def
    have ha1 : 1 ≤ valuation k (a : k) := by
      rw [ha_def]; split_ifs with h
      · simp
      · exact le_of_lt (not_le.mp h)
    have har : valuation k (r1 0 : k) ≤ valuation k (a : k) := by
      rw [ha_def]; split_ifs with h
      · simpa using h
      · exact le_rfl
    have hb1 : valuation k (b : k) ≤ 1 := by
      rw [hb_def]; split_ifs with h
      · simp
      · exact le_of_lt (not_le.mp h)
    have hbr : valuation k (b : k) ≤ valuation k (r2 0 : k) := by
      rw [hb_def]; split_ifs with h
      · simpa using h
      · exact le_rfl
    refine ⟨R1' * a, R2' * b, ?_, ?_, ?_⟩
    · simp only [Units.val_mul, map_mul]
      exact one_le_mul h1' ha1
    · simp only [Units.val_mul, map_mul]
      exact mul_le_one' h2' hb1
    intro t ht hrat
    have hT := hR (fun j => t j.succ) (by simp only [Fin.succ_last]; exact ht) (fun i => by
      have := hrat i.succ
      rw [← Fin.succ_castSucc] at this; exact this)
    have hR1le : valuation k (R1' : k) ≤ valuation k ((R1' * a : kˣ) : k) := by
      simp only [Units.val_mul, map_mul]; exact le_mul_of_one_le_right' ha1
    have hR2le : valuation k ((R2' * b : kˣ) : k) ≤ valuation k (R2' : k) := by
      simp only [Units.val_mul, map_mul]; exact mul_le_of_le_one_right' hb1
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · have h0 := hrat 0
      have ht1 := hT 0
      simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one] at h0 ht1
      have hne : ((t 1 : kˣ) : k) ≠ 0 := (t 1).ne_zero
      have hsplit : ((t 0 : kˣ) : k) = ((t 0 : k) / t 1) * t 1 := by field_simp
      rw [hsplit, map_mul]
      constructor
      · simp only [Units.val_mul, map_mul]
        calc valuation k (R2' : k) * valuation k (b : k)
            = valuation k (b : k) * valuation k (R2' : k) := mul_comm _ _
          _ ≤ valuation k (r2 0 : k) * valuation k (t 1 : k) := mul_le_mul' hbr ht1.1
          _ ≤ _ := mul_le_mul' h0.1 le_rfl
      · simp only [Units.val_mul, map_mul]
        calc valuation k ((t 0 : k) / t 1) * valuation k (t 1 : k)
            ≤ valuation k (r1 0 : k) * valuation k (R1' : k) := mul_le_mul' h0.2 ht1.2
          _ ≤ valuation k (a : k) * valuation k (R1' : k) := mul_le_mul' har le_rfl
          _ = _ := mul_comm _ _
    · have := hT j
      exact ⟨hR2le.trans this.1, this.2.trans hR1le⟩

/- English proof (translation)
Introduce `k _ _ _ _ m r1 r2`. Take `⟨R1, R2, -, -, h⟩` from `valuation_chain_ratio_bounds k m r1 r2`. Conclude with `⟨R1, R2, h⟩`.
-/
theorem chain_bound : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) (r1 r2 : Fin m → kˣ), ∃ R1 R2 : kˣ, ∀ t : Fin (m + 1) → kˣ, t (Fin.last m) = 1 → (∀ i : Fin m, valuation k (r2 i : k) ≤ valuation k ((t i.castSucc : k) / t i.succ) ∧ valuation k ((t i.castSucc : k) / t i.succ) ≤ valuation k (r1 i : k)) → ∀ i, valuation k (R2 : k) ≤ valuation k (t i : k) ∧ valuation k (t i : k) ≤ valuation k (R1 : k) := by
  intro k _ _ _ _ m r1 r2
  obtain ⟨R1, R2, -, -, h⟩ := valuation_chain_ratio_bounds k m r1 r2
  exact ⟨R1, R2, h⟩

end GlobalTheory
