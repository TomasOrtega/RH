import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumOpTransversal

open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

/- English proof (translation)
Introduce `R X M _ _ _ _ _ σ w γ W h A B C hA hB hC hAB hBC hle`. Establish `hdec : ∀ b ∈ B, ∃ c, c ∈ B ∧ c ∈ C ∧ b - c ∈ A`. Introduce `b hb`. Take `⟨a, ha, c, hc, rfl⟩` from `Submodule.mem_sup.1 (hle hb)`. Conclude with `⟨c, hc.1, hc.2, by simpa using ha.2⟩`.

Establish `hAC : ∀ x, x ∈ A → x ∈ C → x ∈ B`. Introduce `x hxA hxC`. Use `(hB x).2 fun b hb => ?_` and prove the remaining obligations. Take `⟨c, -, hcC, hcA⟩` from `hdec b hb`. Establish `e : b = (b - c) + c` using `by abel`.

Rewrite using `[e, h.add_right, h.iso hA hxA hcA, h.iso hC hxC hcC, one_mul]`. Take `⟨tAB, tAB2, -⟩` from `GlobalTheory.FinWeil.sumOp_transversal h A B hB`. Take `⟨tBC, tBC2, -⟩` from `GlobalTheory.FinWeil.sumOp_transversal h B C hC`. Take `⟨tAC, -, -⟩` from `GlobalTheory.FinWeil.sumOp_transversal h A C hC`. Take `⟨⟨n, f0, hf0B, hf0⟩, hfix, -⟩` from `tAB2 hAB`.

Take `⟨⟨m, g, hgC, hg⟩, -, -⟩` from `tBC2 hBC`. Use `choose f hfB hfC hfA using fun i => hdec (f0 i) (hf0B i)`. Establish `hf : ∀ b ∈ B, ∃! i, b - f i ∈ A`. Introduce `b hb`. Establish `key : ∀ i, b - f i ∈ A ↔ b - f0 i ∈ A`.

Introduce `i`. Establish `e : b - f i = (b - f0 i) + (f0 i - f i)` using `by abel`. Rewrite using `[e]`. Conclude with `A.add_mem_iff_left (hfA i)`. Simplify using `only [key]`.

Conclude with `hf0 b hb`. Establish `hkC : ∀ p : Fin m × Fin n, g p.1 + f p.2 ∈ C` using `fun p => C.add_mem (hgC _) (hfC _)`. Establish `hk : ∀ x ∈ C, ∃! p : Fin m × Fin n, x - (g p.1 + f p.2) ∈ A`. Introduce `x hx`. Take `⟨j, hj, hju⟩` from `hg x hx`.

Take `⟨i, hi, hiu⟩` from `hf _ hj`. Use `⟨(j, i), by simpa [sub_add_eq_sub_sub] using hi, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨j', i'⟩ hp`. Establish `hp' : x - (g j' + f i') ∈ A` using `hp`. Establish `h1 : x - (g j' + f i') ∈ B` using `hAC _ hp' (C.sub_mem hx (hkC (j', i')))`.

Establish `h2 : x - g j' ∈ B`. Establish `e : x - g j' = (x - (g j' + f i')) + f i'` using `by abel`. Rewrite using `[e]`. Conclude with `B.add_mem h1 (hfB i')`. Take `rfl : j' = j` from `hju j' h2`.

Take `rfl : i' = i` from `hiu i' (by simpa [sub_add_eq_sub_sub] using hp')`. Both sides reduce to the same expression. Establish `z : ∀ D : Submodule R X, Fixes W D 0` using `fun D a _ => map_zero _`. Use `⟨?_, fun v hv => ?_⟩` and prove the remaining obligations. Rewrite using `[(tAC 0 (z A) _ (fun p : Fin m × Fin n => g p.1 + f p.2) hkC hk).2, (tAB 0 (z A) _ f hfB hf).2, (tBC 0 (z B) _ g hgC hg).2, Fintype.card_prod, mul_comm]`.

Rewrite using `[(tBC _ (hfix v hv) _ g hgC hg).1, (tAB v hv _ f hfB hf).1, (tAC v hv _ (fun p : Fin m × Fin n => g p.1 + f p.2) hkC hk).1, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => h.comp_of_mem hC (hgC j) (hfC i) v`.
-/
theorem sumOp_comp_of_between : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ (A B C : Submodule R X), SelfDual γ A → SelfDual γ B → SelfDual γ C → idx A B ≠ 0 → idx B C ≠ 0 → B ≤ (B ⊓ A) ⊔ (B ⊓ C) → idx A C = idx A B * idx B C ∧ ∀ v, Fixes W A v → sumOp W B C (sumOp W A B v) = sumOp W A C v := by
  intro R X M _ _ _ _ _ σ w γ W h A B C hA hB hC hAB hBC hle
  have hdec : ∀ b ∈ B, ∃ c, c ∈ B ∧ c ∈ C ∧ b - c ∈ A := by
    intro b hb
    obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.1 (hle hb)
    exact ⟨c, hc.1, hc.2, by simpa using ha.2⟩
  have hAC : ∀ x, x ∈ A → x ∈ C → x ∈ B := by
    intro x hxA hxC
    refine (hB x).2 fun b hb => ?_
    obtain ⟨c, -, hcC, hcA⟩ := hdec b hb
    have e : b = (b - c) + c := by abel
    rw [e, h.add_right, h.iso hA hxA hcA, h.iso hC hxC hcC, one_mul]
  obtain ⟨tAB, tAB2, -⟩ := GlobalTheory.FinWeil.sumOp_transversal h A B hB
  obtain ⟨tBC, tBC2, -⟩ := GlobalTheory.FinWeil.sumOp_transversal h B C hC
  obtain ⟨tAC, -, -⟩ := GlobalTheory.FinWeil.sumOp_transversal h A C hC
  obtain ⟨⟨n, f0, hf0B, hf0⟩, hfix, -⟩ := tAB2 hAB
  obtain ⟨⟨m, g, hgC, hg⟩, -, -⟩ := tBC2 hBC
  choose f hfB hfC hfA using fun i => hdec (f0 i) (hf0B i)
  have hf : ∀ b ∈ B, ∃! i, b - f i ∈ A := by
    intro b hb
    have key : ∀ i, b - f i ∈ A ↔ b - f0 i ∈ A := by
      intro i
      have e : b - f i = (b - f0 i) + (f0 i - f i) := by abel
      rw [e]
      exact A.add_mem_iff_left (hfA i)
    simp only [key]
    exact hf0 b hb
  have hkC : ∀ p : Fin m × Fin n, g p.1 + f p.2 ∈ C := fun p => C.add_mem (hgC _) (hfC _)
  have hk : ∀ x ∈ C, ∃! p : Fin m × Fin n, x - (g p.1 + f p.2) ∈ A := by
    intro x hx
    obtain ⟨j, hj, hju⟩ := hg x hx
    obtain ⟨i, hi, hiu⟩ := hf _ hj
    refine ⟨(j, i), by simpa [sub_add_eq_sub_sub] using hi, ?_⟩
    rintro ⟨j', i'⟩ hp
    have hp' : x - (g j' + f i') ∈ A := hp
    have h1 : x - (g j' + f i') ∈ B := hAC _ hp' (C.sub_mem hx (hkC (j', i')))
    have h2 : x - g j' ∈ B := by
      have e : x - g j' = (x - (g j' + f i')) + f i' := by abel
      rw [e]
      exact B.add_mem h1 (hfB i')
    obtain rfl : j' = j := hju j' h2
    obtain rfl : i' = i := hiu i' (by simpa [sub_add_eq_sub_sub] using hp')
    rfl
  have z : ∀ D : Submodule R X, Fixes W D 0 := fun D a _ => map_zero _
  refine ⟨?_, fun v hv => ?_⟩
  · rw [(tAC 0 (z A) _ (fun p : Fin m × Fin n => g p.1 + f p.2) hkC hk).2, (tAB 0 (z A) _ f hfB hf).2,
      (tBC 0 (z B) _ g hgC hg).2, Fintype.card_prod, mul_comm]
  · rw [(tBC _ (hfix v hv) _ g hgC hg).1, (tAB v hv _ f hfB hf).1,
      (tAC v hv _ (fun p : Fin m × Fin n => g p.1 + f p.2) hkC hk).1, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => h.comp_of_mem hC (hgC j) (hfC i) v

end GlobalTheory.FinWeil
