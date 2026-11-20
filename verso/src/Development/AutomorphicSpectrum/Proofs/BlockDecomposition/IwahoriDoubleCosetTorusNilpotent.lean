import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagPairs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureCballZpow
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GindikinKarpelevich

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix ValuativeRel GlobalTheory.CompanionTheory.IwJac
open scoped Classical

namespace GlobalTheory.CompanionTheory.IwJac.DCoset

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

/- English proof (translation)
Unfold `tor`. Rewrite using `[← map_inv]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `[_root_.zpow_neg]`.
-/
theorem tor_inv (ϖ : kˣ) (x : Fin n → ℤ) : (tor ϖ x)⁻¹ = tor ϖ (fun i => - x i) := by
  unfold tor
  rw [← map_inv]
  congr 1
  funext i
  simp [_root_.zpow_neg]

/- English proof (translation)
Rewrite using `[tor_inv, Units.val_mul, Units.val_mul]`. Unfold `tor`. Rewrite using `[val_diagT, val_diagT, Matrix.mul_diagonal, Matrix.diagonal_mul, sub_eq_add_neg, add_comm (x j), _root_.zpow_add, Units.val_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem conj_apply (ϖ : kˣ) (x : Fin n → ℤ) (l : GL (Fin n) k) (i j : Fin n) :
    (((tor ϖ x)⁻¹ * l * tor ϖ x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      ((ϖ ^ (x j - x i) : kˣ) : k) * (l : Matrix (Fin n) (Fin n) k) i j := by
  rw [tor_inv, Units.val_mul, Units.val_mul]
  unfold tor
  rw [val_diagT, val_diagT, Matrix.mul_diagonal, Matrix.diagonal_mul, sub_eq_add_neg, add_comm (x j),
    _root_.zpow_add, Units.val_mul]
  ring

/- English proof (translation)
Establish `h` using `GlobalTheory.OrdShellInt.val_le_iff_ord (k := k) 1 (ϖ ^ m)`. Rewrite `h` using `[GlobalTheory.OrdShellInt.ord_zpow, hϖ, ord_eq_zero (by simp)]`. Rewrite `h` using `[Units.val_one, map_one]`. Conclude with `not_le.1 fun h' => absurd (h.1 h') (by omega)`.
-/
theorem val_zpow_lt_one {ϖ : kˣ} (hϖ : ord k ϖ = 1) {m : ℤ} (hm : 0 < m) :
    valuation k ((ϖ ^ m : kˣ) : k) < 1 := by
  have h := GlobalTheory.OrdShellInt.val_le_iff_ord (k := k) 1 (ϖ ^ m)
  rw [GlobalTheory.OrdShellInt.ord_zpow, hϖ, ord_eq_zero (by simp)] at h
  rw [Units.val_one, map_one] at h
  exact not_le.1 fun h' => absurd (h.1 h') (by omega)

/- English proof (translation)
Take `⟨h0, h1⟩` from `GlobalTheory.IwahoriTraceProof.mem_unipBLower.1 hl.2`. Establish `hint : valuation k ((l : Matrix (Fin n) (Fin n) k) i j) ≤ 1` using `(Valuation.mem_integer_iff _ _).1 (((GlobalTheory.SplitFlip.mem_KO_iff l).1 (iwahori_le_KO k (Fin n) hl.1)).1 i j)`. Rewrite using `[conj_apply]`. Break down `lt_trichotomy i j with h | rfl | h` into its components or cases. Rewrite using `[h0 i j h, mul_zero, map_zero]`.

Conclude with `⟨zero_le', fun h' => absurd h' h.not_gt⟩`. Rewrite using `[h1, sub_self]`. Simplify using the standard rewrite rules. Establish `hlt : valuation k (((ϖ ^ (x j - x i) : kˣ) : k) * (l : Matrix (Fin n) (Fin n) k) i j) < 1`. Rewrite using `[map_mul]`.

Use `lt_of_le_of_lt (mul_le_mul' le_rfl hint) ?_` and prove the remaining obligations. Rewrite using `[mul_one]`. Conclude with `val_zpow_lt_one hϖ (sub_pos.2 (hx h))`. Conclude with `⟨hlt.le, fun _ => hlt⟩`.
-/
theorem conj_entries {ϖ : kˣ} (hϖ : ord k ϖ = 1) {x : Fin n → ℤ} (hx : StrictAnti x) {l : GL (Fin n) k}
    (hl : l ∈ iwahori k (Fin n) ⊓ unipBLower k (Fin n)) (i j : Fin n) :
    valuation k ((((tor ϖ x)⁻¹ * l * tor ϖ x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) ≤ 1 ∧
      (j < i → valuation k ((((tor ϖ x)⁻¹ * l * tor ϖ x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) < 1) := by
  obtain ⟨h0, h1⟩ := GlobalTheory.IwahoriTraceProof.mem_unipBLower.1 hl.2
  have hint : valuation k ((l : Matrix (Fin n) (Fin n) k) i j) ≤ 1 :=
    (Valuation.mem_integer_iff _ _).1 (((GlobalTheory.SplitFlip.mem_KO_iff l).1 (iwahori_le_KO k (Fin n) hl.1)).1 i j)
  rw [conj_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · rw [h0 i j h, mul_zero, map_zero]
    exact ⟨zero_le', fun h' => absurd h' h.not_gt⟩
  · rw [h1, sub_self]
    simp
  · have hlt : valuation k (((ϖ ^ (x j - x i) : kˣ) : k) * (l : Matrix (Fin n) (Fin n) k) i j) < 1 := by
      rw [map_mul]
      refine lt_of_le_of_lt (mul_le_mul' le_rfl hint) ?_
      rw [mul_one]
      exact val_zpow_lt_one hϖ (sub_pos.2 (hx h))
    exact ⟨hlt.le, fun _ => hlt⟩

/- English proof (translation)
Use `mem_iwahori.2 ⟨(GlobalTheory.SplitFlip.mem_KO_iff _).2 ⟨fun i j => ?_, fun i j => ?_⟩, fun i j hij => (conj_entries hϖ hx hl i j).2 hij⟩` and prove the remaining obligations. Conclude with `(Valuation.mem_integer_iff _ _).2 (conj_entries hϖ hx hl i j).1`. Establish `e : ((tor ϖ x)⁻¹ * l * tor ϖ x)⁻¹ = (tor ϖ x)⁻¹ * l⁻¹ * tor ϖ x` using `by group`. Rewrite using `[e]`. Conclude with `(Valuation.mem_integer_iff _ _).2 (conj_entries hϖ hx (inv_mem hl) i j).1`.
-/
theorem conj_mem_iwahori {ϖ : kˣ} (hϖ : ord k ϖ = 1) {x : Fin n → ℤ} (hx : StrictAnti x) {l : GL (Fin n) k}
    (hl : l ∈ iwahori k (Fin n) ⊓ unipBLower k (Fin n)) :
    (tor ϖ x)⁻¹ * l * tor ϖ x ∈ iwahori k (Fin n) := by
  refine mem_iwahori.2 ⟨(GlobalTheory.SplitFlip.mem_KO_iff _).2 ⟨fun i j => ?_, fun i j => ?_⟩,
    fun i j hij => (conj_entries hϖ hx hl i j).2 hij⟩
  · exact (Valuation.mem_integer_iff _ _).2 (conj_entries hϖ hx hl i j).1
  · have e : ((tor ϖ x)⁻¹ * l * tor ϖ x)⁻¹ = (tor ϖ x)⁻¹ * l⁻¹ * tor ϖ x := by group
    rw [e]
    exact (Valuation.mem_integer_iff _ _).2 (conj_entries hϖ hx (inv_mem hl) i j).1

/- English proof (translation)
Establish `e : tor ϖ x * diagT k (Fin n) s = diagT k (Fin n) s * tor ϖ x`. Unfold `tor`. Rewrite using `[← map_mul, ← map_mul, mul_comm]`. Rewrite using `[e]`. Use `group`.
-/
theorem diagT_conj_tor (ϖ : kˣ) (x : Fin n → ℤ) (s : Fin n → kˣ) :
    tor ϖ x * diagT k (Fin n) s * (tor ϖ x)⁻¹ = diagT k (Fin n) s := by
  have e : tor ϖ x * diagT k (Fin n) s = diagT k (Fin n) s * tor ϖ x := by
    unfold tor
    rw [← map_mul, ← map_mul, mul_comm]
  rw [e]
  group

end GlobalTheory.CompanionTheory.IwJac.DCoset

namespace GlobalTheory.CompanionTheory.IwJac

/- English proof (translation)
Introduce `k _ _ _ _ n ϖ hϖ x hx a ha b hb`. Take `⟨c, hc, τ, hτ, l, hl, rfl⟩` from `GlobalTheory.CompanionTheory.IwahoriDatumGL.fact_up' k n ha`. Use `⟨c, hc, τ * ((tor ϖ x)⁻¹ * l * tor ϖ x) * b, mul_mem (mul_mem hτ.1 (DCoset.conj_mem_iwahori hϖ hx hl)) hb, ?_⟩` and prove the remaining obligations. Take `⟨s, rfl⟩` from `hτ.2`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[DCoset.diagT_conj_tor]`. Use `_ = c * tor ϖ x * (diagT k (Fin n) s * ((tor ϖ x)⁻¹ * l * tor ϖ x) * b) := by group`.
-/
theorem iwahori_mul_tor_mul_iwahori : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (ϖ : kˣ), ord k ϖ = 1 → ∀ x : Fin n → ℤ, StrictAnti x →
    ∀ a ∈ iwahori k (Fin n), ∀ b ∈ iwahori k (Fin n), ∃ m ∈ nO k n, ∃ c ∈ iwahori k (Fin n),
      a * tor ϖ x * b = m * tor ϖ x * c := by
  intro k _ _ _ _ n ϖ hϖ x hx a ha b hb
  obtain ⟨c, hc, τ, hτ, l, hl, rfl⟩ := GlobalTheory.CompanionTheory.IwahoriDatumGL.fact_up' k n ha
  refine ⟨c, hc, τ * ((tor ϖ x)⁻¹ * l * tor ϖ x) * b,
    mul_mem (mul_mem hτ.1 (DCoset.conj_mem_iwahori hϖ hx hl)) hb, ?_⟩
  obtain ⟨s, rfl⟩ := hτ.2
  calc c * diagT k (Fin n) s * l * tor ϖ x * b
      = c * (tor ϖ x * diagT k (Fin n) s * (tor ϖ x)⁻¹) * l * tor ϖ x * b := by
        rw [DCoset.diagT_conj_tor]
    _ = c * tor ϖ x * (diagT k (Fin n) s * ((tor ϖ x)⁻¹ * l * tor ϖ x) * b) := by group

end GlobalTheory.CompanionTheory.IwJac

end
