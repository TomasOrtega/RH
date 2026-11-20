import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementKT
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumMinorRowExpansionEigenFunctionalStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.RowChain

/- English proof (translation)
Proceed by induction on `d with`. Consider the case `zero`. Introduce `i t a b hi ht ha hb`. Take `rfl : t = r + k` from `by omega`. Establish `hai : Function.Injective a` using `fun x y hxy => by`.

Establish `h1` using `ha x; have h2 := ha y; rw [hxy] at h1; exact Fin.ext (by omega)`. Establish `hbi : Function.Injective b` using `fun x y hxy => by`. Establish `h1` using `hb x; have h2 := hb y; rw [hxy] at h1; exact Fin.ext (by omega)`. Apply the tactic sequence `obtain ⟨e, he, hl⟩ := GlobalTheory.T.quantumMinor_rowExpansion_eigenFunctional M Wp _ _ E l a b (fun j : Fin (r + k) => (⟨r + j.val, by omega⟩ : Fin (2 * r + k + 1))) (fun j : Fin (r + k) => (⟨if j.val < k then r + j.val else r + j.val + 1, by split_ifs <;> omega⟩ : Fin (2 * r + …`. Simplify using `only [Fin.mk.injEq] at hxy; exact Fin.ext (by omega))`.

Use the proof step `(fun x y hxy => by`. Apply the tactic sequence `simp only [Fin.mk.injEq] at hxy; exact Fin.ext (by split_ifs at hxy <;> omega))`. Use the proof step `(by`. Use extensionality with `x`. Simplify using `only [Set.mem_range, Set.mem_insert_iff, Fin.ext_iff, ha]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨j, hj⟩`. Distinguish the cases in `h0 : j.val = 0`. Use `left`. Use linear arithmetic over natural numbers and integers.

Use the proof step `right; exact ⟨⟨j.val - 1, by omega⟩, by simp only; omega⟩`. Introduce and unpack `(hx | ⟨j, hj⟩)`. Conclude with `⟨⟨0, by omega⟩, by simp only; omega⟩`. Conclude with `⟨⟨j.val + 1, by omega⟩, by simp only; omega⟩)`. Use the proof step `(by`.

Simplify using `only [Set.mem_range, Fin.ext_iff]`. Introduce and unpack `⟨j, hj⟩`. Use the proof step `omega)`. Use the proof step `(by`. Use extensionality with `x`.

Simplify using `only [Set.mem_range, Set.mem_insert_iff, Fin.ext_iff, hb]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨j, hj⟩`. Break down `lt_trichotomy j.val k with h0 | h0 | h0` into its components or cases. Apply the tactic sequence `right; exact ⟨⟨j.val, by omega⟩, by simp only; split_ifs <;> omega⟩`.

Use `left`. Use linear arithmetic over natural numbers and integers. Apply the tactic sequence `right; exact ⟨⟨j.val - 1, by omega⟩, by simp only; split_ifs <;> omega⟩`. Introduce and unpack `(hx | ⟨j, hj⟩)`. Conclude with `⟨⟨k, by omega⟩, by simp only; omega⟩`.

Use `split_ifs at hj`. Conclude with `⟨⟨j.val, by omega⟩, by simp only; omega⟩`. Conclude with `⟨⟨j.val + 1, by omega⟩, by simp only; omega⟩)`. Use the proof step `(by`. Simplify using `only [Set.mem_range, Fin.ext_iff]`.

Apply the tactic sequence `rintro ⟨j, hj⟩; split_ifs at hj <;> omega)`. Use the proof step `(by`. Simplify using `only [Set.mem_range, Fin.ext_iff, hb]`. Introduce and unpack `⟨j, hj⟩`. Use the proof step `omega)`.

Use the proof step `(by`. Introduce `j v`. Establish `hj` using `hb j`. Take `⟨h1, h2⟩` from `h ⟨i, by omega⟩ (b j) (by rw [Fin.lt_def]; simp only; omega) (by simp only; omega)`. Rewrite using `[h1]`.

Distinguish the cases in `hc : b j = ⟨r + k, by omega⟩`. Rewrite using `[if_pos hc, hc]`. Rewrite using `[if_neg hc]`. Establish `hc' : (b j).val ≠ r + k` using `fun h' => hc (Fin.ext h')`. Rewrite `h2` using `[if_neg (by simp only; omega), if_neg (by simp only; omega)]`.

Rewrite using `[norm_eq_zero.mp h2])`. Use `⟨_, ?_, hl⟩` and prove the remaining obligations. Take `⟨-, h2⟩` from `h ⟨i, by omega⟩ ⟨r + k, by omega⟩ (by rw [Fin.lt_def]; simp only; omega) (by simp only; omega)`. Rewrite `h2` using `[if_neg (by simp only; omega), if_pos (Or.inl ⟨by simp only; omega, rfl⟩)]`. Rewrite using `[norm_mul, he, h2, one_mul]`.

Consider the case `succ d ih`. Introduce `i t a b hi ht ha hb`. Take `⟨t, rfl⟩ : ∃ s, t = s + 1` from `⟨t - 1, by omega⟩`. Establish `hai : Function.Injective a` using `fun x y hxy => by`. Establish `h1` using `ha x; have h2 := ha y; rw [hxy] at h1; exact Fin.ext (by omega)`.

Establish `hbi : Function.Injective b` using `fun x y hxy => by`. Establish `h1` using `hb x; have h2 := hb y; rw [hxy] at h1; exact Fin.ext (by omega)`. Take `⟨c, hc, hcl⟩` from `ih (i + 1) t (fun j : Fin (t + 1) => (⟨i + 1 + j.val, by omega⟩ : Fin (2 * r + k + 1))) (fun j : Fin (t + 1) => (⟨i + 1 + 1 + j.val, by omega⟩ : Fin (2 * r + k + 1))) (by omega) (by omega) (fun _ => rfl) (fun _ => rfl)`. Take `⟨e, he, hl⟩` from `GlobalTheory.T.quantumMinor_rowExpansion_eigenFunctional M Wp _ _ E l a b (fun j : Fin (t + 1) => (⟨i + 1 + j.val, by omega⟩ : Fin (2 * r + k + 1))) (fun j : Fin (t + 1) => (⟨i + 1 + 1 + j.val, by omega⟩ : Fin (2 * r + k + 1))) ⟨i, by omega⟩ ⟨i + 1, by omega⟩ (p ⟨i, by omega⟩ ⟨i …`. Simplify using `only [Fin.mk.injEq] at hxy; exact Fin.ext (by omega))`.

Use the proof step `(fun x y hxy => by`. Simplify using `only [Fin.mk.injEq] at hxy; exact Fin.ext (by omega))`. Use the proof step `(by`. Use extensionality with `x`. Simplify using `only [Set.mem_range, Set.mem_insert_iff, Fin.ext_iff, ha]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨j, hj⟩`. Distinguish the cases in `h0 : j.val = 0`. Use `left`. Use linear arithmetic over natural numbers and integers.

Use the proof step `right; exact ⟨⟨j.val - 1, by omega⟩, by simp only; omega⟩`. Introduce and unpack `(hx | ⟨j, hj⟩)`. Conclude with `⟨⟨0, by omega⟩, by simp only; omega⟩`. Conclude with `⟨⟨j.val + 1, by omega⟩, by simp only; omega⟩)`. Use the proof step `(by`.

Simplify using `only [Set.mem_range, Fin.ext_iff]`. Introduce and unpack `⟨j, hj⟩`. Use the proof step `omega)`. Use the proof step `(by`. Use extensionality with `x`.

Simplify using `only [Set.mem_range, Set.mem_insert_iff, Fin.ext_iff, hb]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨j, hj⟩`. Distinguish the cases in `h0 : j.val = 0`. Use `left`.

Use linear arithmetic over natural numbers and integers. Use the proof step `right; exact ⟨⟨j.val - 1, by omega⟩, by simp only; omega⟩`. Introduce and unpack `(hx | ⟨j, hj⟩)`. Conclude with `⟨⟨0, by omega⟩, by simp only; omega⟩`. Conclude with `⟨⟨j.val + 1, by omega⟩, by simp only; omega⟩)`.

Use the proof step `(by`. Simplify using `only [Set.mem_range, Fin.ext_iff]`. Introduce and unpack `⟨j, hj⟩`. Use the proof step `omega)`. Use the proof step `(by`.

Simplify using `only [Set.mem_range, Fin.ext_iff, hb]`. Introduce and unpack `⟨j, hj⟩`. Use the proof step `omega)`. Use the proof step `(by`. Introduce `j v`.

Establish `hj` using `hb j`. Take `⟨h1, h2⟩` from `h ⟨i, by omega⟩ (b j) (by rw [Fin.lt_def]; simp only; omega) (by simp only; omega)`. Rewrite using `[h1]`. Distinguish the cases in `hc : b j = ⟨i + 1, by omega⟩`. Rewrite using `[if_pos hc, hc]`.

Rewrite using `[if_neg hc]`. Establish `hc' : (b j).val ≠ i + 1` using `fun h' => hc (Fin.ext h')`. Rewrite `h2` using `[if_neg (by simp only; omega), if_neg (by simp only; omega)]`. Rewrite using `[norm_eq_zero.mp h2])`. Take `⟨-, h2⟩` from `h ⟨i, by omega⟩ ⟨i + 1, by omega⟩ (by rw [Fin.lt_def]; simp only; omega) (by simp only; omega)`.

Rewrite `h2` using `[if_pos (by simp only; exact ⟨trivial, by omega⟩)]`. Use `⟨e * p ⟨i, by omega⟩ ⟨i + 1, by omega⟩ * c, ?_, fun u v => ?_⟩` and prove the remaining obligations. Rewrite using `[norm_mul, norm_mul, he, h2, hc, one_mul, one_mul]`. Rewrite using `[hl, hcl, smul_smul]`.
-/
theorem quantumMinor_row_removal_chain (M Wp : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup Wp] [Module ℂ Wp]
    (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ M) (l : M →ₗ[ℂ] Wp)
    (p : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ) (τ : ℝ) (hE : Formalism.REAL.GlRel E)
    (h : ∀ a b : Fin (2 * r + k + 1), a < b → ¬ (r ≤ a.val ∧ b.val ≤ r + k) →
      (∀ v, l (E a b v) = p a b • l v) ∧
      ‖p a b‖ = (if b.val = a.val + 1 ∧ (b.val < r ∨ r + k < a.val) then (1 : ℝ)
        else if (a.val + 1 = r ∧ b.val = r + k) ∨ (a.val = r + k ∧ b.val = r + k + 1) then τ
        else 0)) (d : ℕ) :
    ∀ (i t : ℕ) (a b : Fin (t + 1) → Fin (2 * r + k + 1)), i + d + 1 = r → t + 1 + i = 2 * r + k →
      (∀ j, (a j).val = i + j.val) → (∀ j, (b j).val = i + 1 + j.val) →
      ∃ c : ℂ, ‖c‖ = τ ∧ ∀ u v, l (Formalism.REAL.qminor E a b u v) =
        c • l (Formalism.REAL.qminor E
          (fun j : Fin (r + k) => (⟨r + j.val, by omega⟩ : Fin (2 * r + k + 1)))
          (fun j : Fin (r + k) => (⟨if j.val < k then r + j.val else r + j.val + 1,
            by split_ifs <;> omega⟩ : Fin (2 * r + k + 1))) u v) := by
  induction d with
  | zero =>
    intro i t a b hi ht ha hb
    obtain rfl : t = r + k := by omega
    have hai : Function.Injective a := fun x y hxy => by
      have h1 := ha x; have h2 := ha y; rw [hxy] at h1; exact Fin.ext (by omega)
    have hbi : Function.Injective b := fun x y hxy => by
      have h1 := hb x; have h2 := hb y; rw [hxy] at h1; exact Fin.ext (by omega)
    obtain ⟨e, he, hl⟩ := GlobalTheory.T.quantumMinor_rowExpansion_eigenFunctional M Wp _ _ E l a b
      (fun j : Fin (r + k) => (⟨r + j.val, by omega⟩ : Fin (2 * r + k + 1)))
      (fun j : Fin (r + k) => (⟨if j.val < k then r + j.val else r + j.val + 1,
            by split_ifs <;> omega⟩ : Fin (2 * r + k + 1)))
      ⟨i, by omega⟩ ⟨r + k, by omega⟩ (p ⟨i, by omega⟩ ⟨r + k, by omega⟩) hE hai hbi
      (fun x y hxy => by
        simp only [Fin.mk.injEq] at hxy; exact Fin.ext (by omega))
      (fun x y hxy => by
        simp only [Fin.mk.injEq] at hxy; exact Fin.ext (by split_ifs at hxy <;> omega))
      (by
        ext x
        simp only [Set.mem_range, Set.mem_insert_iff, Fin.ext_iff, ha]
        constructor
        · rintro ⟨j, hj⟩
          by_cases h0 : j.val = 0
          · left; omega
          · right; exact ⟨⟨j.val - 1, by omega⟩, by simp only; omega⟩
        · rintro (hx | ⟨j, hj⟩)
          · exact ⟨⟨0, by omega⟩, by simp only; omega⟩
          · exact ⟨⟨j.val + 1, by omega⟩, by simp only; omega⟩)
      (by
        simp only [Set.mem_range, Fin.ext_iff]
        rintro ⟨j, hj⟩; omega)
      (by
        ext x
        simp only [Set.mem_range, Set.mem_insert_iff, Fin.ext_iff, hb]
        constructor
        · rintro ⟨j, hj⟩
          rcases lt_trichotomy j.val k with h0 | h0 | h0
          · right; exact ⟨⟨j.val, by omega⟩, by simp only; split_ifs <;> omega⟩
          · left; omega
          · right; exact ⟨⟨j.val - 1, by omega⟩, by simp only; split_ifs <;> omega⟩
        · rintro (hx | ⟨j, hj⟩)
          · exact ⟨⟨k, by omega⟩, by simp only; omega⟩
          · split_ifs at hj
            · exact ⟨⟨j.val, by omega⟩, by simp only; omega⟩
            · exact ⟨⟨j.val + 1, by omega⟩, by simp only; omega⟩)
      (by
        simp only [Set.mem_range, Fin.ext_iff]
        rintro ⟨j, hj⟩; split_ifs at hj <;> omega)
      (by
        simp only [Set.mem_range, Fin.ext_iff, hb]
        rintro ⟨j, hj⟩; omega)
      (by
        intro j v
        have hj := hb j
        obtain ⟨h1, h2⟩ := h ⟨i, by omega⟩ (b j) (by rw [Fin.lt_def]; simp only; omega)
          (by simp only; omega)
        rw [h1]
        by_cases hc : b j = ⟨r + k, by omega⟩
        · rw [if_pos hc, hc]
        · rw [if_neg hc]
          have hc' : (b j).val ≠ r + k := fun h' => hc (Fin.ext h')
          rw [if_neg (by simp only; omega), if_neg (by simp only; omega)] at h2
          rw [norm_eq_zero.mp h2])
    refine ⟨_, ?_, hl⟩
    obtain ⟨-, h2⟩ := h ⟨i, by omega⟩ ⟨r + k, by omega⟩ (by rw [Fin.lt_def]; simp only; omega)
          (by simp only; omega)
    rw [if_neg (by simp only; omega), if_pos (Or.inl ⟨by simp only; omega, rfl⟩)] at h2
    rw [norm_mul, he, h2, one_mul]
  | succ d ih =>
    intro i t a b hi ht ha hb
    obtain ⟨t, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    have hai : Function.Injective a := fun x y hxy => by
      have h1 := ha x; have h2 := ha y; rw [hxy] at h1; exact Fin.ext (by omega)
    have hbi : Function.Injective b := fun x y hxy => by
      have h1 := hb x; have h2 := hb y; rw [hxy] at h1; exact Fin.ext (by omega)
    obtain ⟨c, hc, hcl⟩ := ih (i + 1) t
      (fun j : Fin (t + 1) => (⟨i + 1 + j.val, by omega⟩ : Fin (2 * r + k + 1)))
      (fun j : Fin (t + 1) => (⟨i + 1 + 1 + j.val, by omega⟩ : Fin (2 * r + k + 1)))
      (by omega) (by omega) (fun _ => rfl) (fun _ => rfl)
    obtain ⟨e, he, hl⟩ := GlobalTheory.T.quantumMinor_rowExpansion_eigenFunctional M Wp _ _ E l a b
      (fun j : Fin (t + 1) => (⟨i + 1 + j.val, by omega⟩ : Fin (2 * r + k + 1)))
      (fun j : Fin (t + 1) => (⟨i + 1 + 1 + j.val, by omega⟩ : Fin (2 * r + k + 1)))
      ⟨i, by omega⟩ ⟨i + 1, by omega⟩ (p ⟨i, by omega⟩ ⟨i + 1, by omega⟩) hE hai hbi
      (fun x y hxy => by
        simp only [Fin.mk.injEq] at hxy; exact Fin.ext (by omega))
      (fun x y hxy => by
        simp only [Fin.mk.injEq] at hxy; exact Fin.ext (by omega))
      (by
        ext x
        simp only [Set.mem_range, Set.mem_insert_iff, Fin.ext_iff, ha]
        constructor
        · rintro ⟨j, hj⟩
          by_cases h0 : j.val = 0
          · left; omega
          · right; exact ⟨⟨j.val - 1, by omega⟩, by simp only; omega⟩
        · rintro (hx | ⟨j, hj⟩)
          · exact ⟨⟨0, by omega⟩, by simp only; omega⟩
          · exact ⟨⟨j.val + 1, by omega⟩, by simp only; omega⟩)
      (by
        simp only [Set.mem_range, Fin.ext_iff]
        rintro ⟨j, hj⟩; omega)
      (by
        ext x
        simp only [Set.mem_range, Set.mem_insert_iff, Fin.ext_iff, hb]
        constructor
        · rintro ⟨j, hj⟩
          by_cases h0 : j.val = 0
          · left; omega
          · right; exact ⟨⟨j.val - 1, by omega⟩, by simp only; omega⟩
        · rintro (hx | ⟨j, hj⟩)
          · exact ⟨⟨0, by omega⟩, by simp only; omega⟩
          · exact ⟨⟨j.val + 1, by omega⟩, by simp only; omega⟩)
      (by
        simp only [Set.mem_range, Fin.ext_iff]
        rintro ⟨j, hj⟩; omega)
      (by
        simp only [Set.mem_range, Fin.ext_iff, hb]
        rintro ⟨j, hj⟩; omega)
      (by
        intro j v
        have hj := hb j
        obtain ⟨h1, h2⟩ := h ⟨i, by omega⟩ (b j) (by rw [Fin.lt_def]; simp only; omega)
          (by simp only; omega)
        rw [h1]
        by_cases hc : b j = ⟨i + 1, by omega⟩
        · rw [if_pos hc, hc]
        · rw [if_neg hc]
          have hc' : (b j).val ≠ i + 1 := fun h' => hc (Fin.ext h')
          rw [if_neg (by simp only; omega), if_neg (by simp only; omega)] at h2
          rw [norm_eq_zero.mp h2])
    obtain ⟨-, h2⟩ := h ⟨i, by omega⟩ ⟨i + 1, by omega⟩ (by rw [Fin.lt_def]; simp only; omega)
          (by simp only; omega)
    rw [if_pos (by simp only; exact ⟨trivial, by omega⟩)] at h2
    refine ⟨e * p ⟨i, by omega⟩ ⟨i + 1, by omega⟩ * c, ?_, fun u v => ?_⟩
    · rw [norm_mul, norm_mul, he, h2, hc, one_mul, one_mul]
    · rw [hl, hcl, smul_smul]

/- English proof (translation)
Introduce `M Wp _ _ _ _ k r E l p τ _ hE h hr`. Apply the tactic sequence `have gen : ∀ (n : ℕ) (a b : Fin n → Fin (2 * r + k + 1)), n = 2 * r + k → (∀ j, (a j).val = 0 + j.val) → (∀ j, (b j).val = 0 + 1 + j.val) → ∃ c : ℂ, ‖c‖ = τ ∧ ∀ u v, l (Formalism.REAL.qminor E a b u v) = c • l (Formalism.REAL.qminor E (fun j : Fin (r + k) => (⟨r + j.val, by omega …`. Introduce `n a b hn ha hb`. Consider the cases of `n with`. Consider the case `zero => omega`.

Consider the case `succ t`. Conclude with `quantumMinor_row_removal_chain M Wp k r E l p τ hE h (r - 1) 0 t a b (by omega) (by omega) ha hb`. Conclude with `gen _ _ _ rfl (fun j => by simp) (fun j => by simp; omega)`.
-/
theorem chain_rows : ∀ (M Wp : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup Wp] [Module ℂ Wp] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ M) (l : M →ₗ[ℂ] Wp) (p : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ) (τ : ℝ), 1 ≤ k → Formalism.REAL.GlRel E → (∀ a b : Fin (2 * r + k + 1), a < b → ¬ (r ≤ a.val ∧ b.val ≤ r + k) → (∀ v, l (E a b v) = p a b • l v) ∧ ‖p a b‖ = (if b.val = a.val + 1 ∧ (b.val < r ∨ r + k < a.val) then (1 : ℝ) else if (a.val + 1 = r ∧ b.val = r + k) ∨ (a.val = r + k ∧ b.val = r + k + 1) then τ else 0)) → 1 ≤ r → ∃ c : ℂ, ‖c‖ = τ ∧ ∀ u v, l (Formalism.REAL.qminor E (Fin.succAbove (Fin.last (2 * r + k))) (Fin.succAbove 0) u v) = c • l (Formalism.REAL.qminor E (fun j : Fin (r + k) => (⟨r + j.val, by omega⟩ : Fin (2 * r + k + 1))) (fun j : Fin (r + k) => (⟨if j.val < k then r + j.val else r + j.val + 1, by split_ifs <;> omega⟩ : Fin (2 * r + k + 1))) u v) := by
  intro M Wp _ _ _ _ k r E l p τ _ hE h hr
  have gen : ∀ (n : ℕ) (a b : Fin n → Fin (2 * r + k + 1)), n = 2 * r + k →
      (∀ j, (a j).val = 0 + j.val) → (∀ j, (b j).val = 0 + 1 + j.val) →
      ∃ c : ℂ, ‖c‖ = τ ∧ ∀ u v, l (Formalism.REAL.qminor E a b u v) =
        c • l (Formalism.REAL.qminor E
          (fun j : Fin (r + k) => (⟨r + j.val, by omega⟩ : Fin (2 * r + k + 1)))
          (fun j : Fin (r + k) => (⟨if j.val < k then r + j.val else r + j.val + 1,
            by split_ifs <;> omega⟩ : Fin (2 * r + k + 1))) u v) := by
    intro n a b hn ha hb
    cases n with
    | zero => omega
    | succ t =>
      exact quantumMinor_row_removal_chain M Wp k r E l p τ hE h (r - 1) 0 t a b (by omega) (by omega) ha hb
  exact gen _ _ _ rfl (fun j => by simp) (fun j => by simp; omega)

end GlobalTheory.RowChain
