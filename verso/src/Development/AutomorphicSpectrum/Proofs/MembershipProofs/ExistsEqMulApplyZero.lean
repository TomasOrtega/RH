import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar

open Matrix ValuativeRel GlobalTheory.WeilM MeasureTheory
open scoped ComplexConjugate NNReal

namespace GlobalTheory.CompanionTheory.WeilCoinv

/- English proof (translation)
Take `⟨t, ht⟩` from `AddChar.ne_one_iff.mp hψ`. Take `⟨i, hi⟩` from `Function.ne_iff.mp hx`. Establish `hi' : x i ≠ 0` using `hi`. Use `⟨Pi.single i (t / x i), ?_⟩` and prove the remaining obligations. Establish `hxt : x i * (t / x i) = t` using `by field_simp`.

Rewrite using `[dotProduct_single, hxt]`. Conclude with `ht`.
-/
theorem exists_dotProduct_ne_one {k : Type} [Field k] {κ : Type} [Fintype κ] {ψ : AddChar k ℂ} (hψ : ψ ≠ 1)
    {x : κ → k} (hx : x ≠ 0) : ∃ y : κ → k, ψ (x ⬝ᵥ y) ≠ 1 := by
  classical
  obtain ⟨t, ht⟩ := AddChar.ne_one_iff.mp hψ
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  have hi' : x i ≠ 0 := hi
  refine ⟨Pi.single i (t / x i), ?_⟩
  have hxt : x i * (t / x i) = t := by field_simp
  rw [dotProduct_single, hxt]
  exact ht

/- English proof (translation)
Introduce `k _ _ _ _ _ κ _ ψ hψc hψ l hl`. Use `haveI : NonarchimedeanAddGroup k := GlobalTheory.WeilM.nonarch_field k`. Use `haveI : NonarchimedeanAddGroup (κ → k) := GlobalTheory.WeilM.nonarch_pi k κ`. Establish `hψlc : IsLocallyConstant ψ` using `GlobalTheory.WeilM.isLocallyConstant_addChar ψ hψc`. Establish `hχ : ∀ y : κ → k, IsLocallyConstant (fun x : κ → k => ψ (x ⬝ᵥ y))` using `fun y => hψlc.comp_continuous (continuous_id.dotProduct continuous_const)`.

Establish `key : ∀ t : Finset (κ → k), ∀ φ ∈ SB (κ → k), (∀ x, φ x ≠ 0 → ∃ y ∈ t, ψ (x ⬝ᵥ y) ≠ 1) → l φ = 0`. Introduce `t`. Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty`. Introduce `φ _ h`.

Establish `hz : φ = 0` using `funext fun x => by`. Assume the negation of the conclusion as `hx`. Take `⟨y, hy, -⟩` from `h x hx`. Simplify using `at hy`. Rewrite using `[hz, map_zero]`.

Consider the case `@insert y t hyt ih`. Introduce `φ hφ h`. Take `⟨hφl, hφc⟩` from `hφ`. Take `⟨φ₁, hφ₁⟩ : ∃ f : (κ → k) → ℂ, f = fun x => if ψ (x ⬝ᵥ y) = 1 then φ x else 0` from `⟨_, rfl⟩`. Take `⟨g, hg⟩ : ∃ f : (κ → k) → ℂ, f = fun x => if ψ (x ⬝ᵥ y) = 1 then 0 else φ x / (ψ (x ⬝ᵥ y) - 1)` from `⟨_, rfl⟩`.

Establish `hφ₁SB : φ₁ ∈ SB (κ → k)`. Use `⟨?_, hφc.mono ?_⟩` and prove the remaining obligations. Rewrite using `[hφ₁]`. Conclude with `(hχ y).comp₂ hφl (fun a b => if a = 1 then b else 0)`. Introduce `x hx`.

Rewrite `hx`, the goal using `[Function.mem_support]`. Introduce `h0`. Apply `hx` to reduce the goal to its premises. Simplify using `[hφ₁, h0]`. Establish `hgSB : g ∈ SB (κ → k)`.

Use `⟨?_, hφc.mono ?_⟩` and prove the remaining obligations. Rewrite using `[hg]`. Conclude with `(hχ y).comp₂ hφl (fun a b => if a = 1 then 0 else b / (a - 1))`. Introduce `x hx`. Rewrite `hx`, the goal using `[Function.mem_support]`.

Introduce `h0`. Apply `hx` to reduce the goal to its premises. Simplify using `[hg, h0]`. Establish `hsch : schr ψ ((0 : κ → k), y) g = fun x => ψ (x ⬝ᵥ y) * g x`. Use function extensionality and compare the values at `x`.

Simplify using `[GlobalTheory.WeilM.schr]`. Establish `hdiff : φ = φ₁ + (schr ψ ((0 : κ → k), y) g - g)`. Rewrite using `[hsch]`. Use function extensionality and compare the values at `x`. Simplify using `only [Pi.add_apply, Pi.sub_apply, hφ₁, hg]`.

Use `split_ifs with h1`. Simplify using the standard rewrite rules. Establish `hne : ψ (x ⬝ᵥ y) - 1 ≠ 0` using `sub_ne_zero.mpr h1`. Rewrite using `[zero_add, ← sub_one_mul]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[hdiff, map_add, map_sub, hl y g hgSB, sub_self, add_zero]`. Use `ih φ₁ hφ₁SB ?_` and prove the remaining obligations. Introduce `x hx`. Establish `hx1 : ψ (x ⬝ᵥ y) = 1`. Assume the negation of the conclusion as `hne`.

Apply `hx` to reduce the goal to its premises. Simplify using `[hφ₁, hne]`. Establish `hx2 : φ x ≠ 0`. Introduce `h0`. Apply `hx` to reduce the goal to its premises.

Simplify using `[hφ₁, h0]`. Take `⟨y', hy', hy'ne⟩` from `h x hx2`. Break down `Finset.mem_insert.mp hy' with rfl | hy't` into its components or cases. Conclude with `absurd hx1 hy'ne`. Conclude with `⟨y', hy't, hy'ne⟩`.

Establish `vanish : ∀ φ ∈ SB (κ → k), φ 0 = 0 → l φ = 0`. Introduce `φ hφ h0`. Take `⟨hφl, hφc⟩` from `hφ`. Establish `hsupp : IsClosed (Function.support φ)` using `(hφl.isOpen_fiber 0).isClosed_compl`. Establish `hK : IsCompact (Function.support φ)`.

Establish `hc` using `hφc.isCompact`. Rewrite `hc` using `[tsupport, hsupp.closure_eq]`. Then use the resulting hypothesis. Establish `hcov : Function.support φ ⊆ ⋃ y : κ → k, {x | ψ (x ⬝ᵥ y) ≠ 1}`. Introduce `x hx`. Establish `hx0 : x ≠ 0`.

Introduce and unpack `rfl`. Conclude with `hx h0`. Take `⟨y, hy⟩` from `exists_dotProduct_ne_one hψ hx0`. Conclude with `Set.mem_iUnion.mpr ⟨y, hy⟩`. Take `⟨t, ht⟩` from `hK.elim_finite_subcover (fun y : κ → k => {x | ψ (x ⬝ᵥ y) ≠ 1}) (fun y => ((hχ y).isClosed_fiber 1).isOpen_compl) hcov`.

Use `key t φ ⟨hφl, hφc⟩ ?_` and prove the remaining obligations. Introduce `x hx`. Establish `hxt` using `ht hx`. Simplify using `only [Set.mem_iUnion] at hxt`. Take `⟨y, hy, hxy⟩` from `hxt`.

Conclude with `⟨y, hy, hxy⟩`. Take `⟨C, hC, hC0⟩` from `exists_compact_mem_nhds (0 : κ → k)`. Take `⟨O, hO⟩` from `NonarchimedeanAddGroup.is_nonarchimedean C hC0`. Establish `hOc : IsCompact (O : Set (κ → k))` using `hC.of_isClosed_subset O.isClosed hO`. Establish `hO0 : (0 : κ → k) ∈ O` using `O.zero_mem`.

Take `⟨φ₀, hφ₀d⟩ : ∃ f : (κ → k) → ℂ, f = fun x => if x ∈ O then 1 else 0` from `⟨_, rfl⟩`. Establish `hφ₀ : φ₀ ∈ SB (κ → k)`. Use `⟨?_, HasCompactSupport.intro' hOc O.isClosed fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[IsLocallyConstant.iff_exists_open]`. Introduce `x`.

Distinguish the cases in `hx : x ∈ O`. Use `⟨O, O.isOpen, hx, fun x' hx' => ?_⟩` and prove the remaining obligations. Establish `hx'' : x' ∈ O` using `hx'`. Simplify using `[hφ₀d, hx, hx'']`. Use `⟨(O : Set (κ → k))ᶜ, O.isClosed.isOpen_compl, hx, fun x' hx' => ?_⟩` and prove the remaining obligations.

Establish `hx'' : x' ∉ O` using `hx'`. Simplify using `[hφ₀d, hx, hx'']`. Establish `hx' : x ∉ O` using `hx`. Simplify using `[hφ₀d, hx']`. Use `⟨l φ₀, fun φ hφ => ?_⟩` and prove the remaining obligations.

Establish `h1 : φ - φ 0 • φ₀ ∈ SB (κ → k)` using `Submodule.sub_mem _ hφ (Submodule.smul_mem _ _ hφ₀)`. Establish `h2 : (φ - φ 0 • φ₀) 0 = 0` using `by simp [hφ₀d, hO0]`. Establish `h3` using `vanish _ h1 h2`. Rewrite `h3` using `[map_sub, map_smul, smul_eq_mul, sub_eq_zero]`. Rewrite using `[h3, mul_comm]`.
-/
theorem exists_eq_mul_apply_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Invertible (2 : k)] (κ : Type) [Fintype κ] (ψ : AddChar k ℂ),
    Continuous ψ → ψ ≠ 1 → ∀ l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ,
    (∀ y, ∀ φ ∈ SB (κ → k), l (schr ψ (0, y) φ) = l φ) → ∃ a : ℂ, ∀ φ ∈ SB (κ → k), l φ = a * φ 0 := by
  intro k _ _ _ _ _ κ _ ψ hψc hψ l hl
  classical
  haveI : NonarchimedeanAddGroup k := GlobalTheory.WeilM.nonarch_field k
  haveI : NonarchimedeanAddGroup (κ → k) := GlobalTheory.WeilM.nonarch_pi k κ
  have hψlc : IsLocallyConstant ψ := GlobalTheory.WeilM.isLocallyConstant_addChar ψ hψc
  have hχ : ∀ y : κ → k, IsLocallyConstant (fun x : κ → k => ψ (x ⬝ᵥ y)) := fun y =>
    hψlc.comp_continuous (continuous_id.dotProduct continuous_const)
  have key : ∀ t : Finset (κ → k), ∀ φ ∈ SB (κ → k),
      (∀ x, φ x ≠ 0 → ∃ y ∈ t, ψ (x ⬝ᵥ y) ≠ 1) → l φ = 0 := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro φ _ h
      have hz : φ = 0 := funext fun x => by
        by_contra hx
        obtain ⟨y, hy, -⟩ := h x hx
        simp at hy
      rw [hz, map_zero]
    | @insert y t hyt ih =>
      intro φ hφ h
      obtain ⟨hφl, hφc⟩ := hφ
      obtain ⟨φ₁, hφ₁⟩ : ∃ f : (κ → k) → ℂ, f = fun x => if ψ (x ⬝ᵥ y) = 1 then φ x else 0 := ⟨_, rfl⟩
      obtain ⟨g, hg⟩ : ∃ f : (κ → k) → ℂ,
          f = fun x => if ψ (x ⬝ᵥ y) = 1 then 0 else φ x / (ψ (x ⬝ᵥ y) - 1) := ⟨_, rfl⟩
      have hφ₁SB : φ₁ ∈ SB (κ → k) := by
        refine ⟨?_, hφc.mono ?_⟩
        · rw [hφ₁]
          exact (hχ y).comp₂ hφl (fun a b => if a = 1 then b else 0)
        · intro x hx
          rw [Function.mem_support] at hx ⊢
          intro h0
          apply hx
          simp [hφ₁, h0]
      have hgSB : g ∈ SB (κ → k) := by
        refine ⟨?_, hφc.mono ?_⟩
        · rw [hg]
          exact (hχ y).comp₂ hφl (fun a b => if a = 1 then 0 else b / (a - 1))
        · intro x hx
          rw [Function.mem_support] at hx ⊢
          intro h0
          apply hx
          simp [hg, h0]
      have hsch : schr ψ ((0 : κ → k), y) g = fun x => ψ (x ⬝ᵥ y) * g x := by
        funext x
        simp [GlobalTheory.WeilM.schr]
      have hdiff : φ = φ₁ + (schr ψ ((0 : κ → k), y) g - g) := by
        rw [hsch]
        funext x
        simp only [Pi.add_apply, Pi.sub_apply, hφ₁, hg]
        split_ifs with h1
        · simp
        · have hne : ψ (x ⬝ᵥ y) - 1 ≠ 0 := sub_ne_zero.mpr h1
          rw [zero_add, ← sub_one_mul]
          field_simp
      rw [hdiff, map_add, map_sub, hl y g hgSB, sub_self, add_zero]
      refine ih φ₁ hφ₁SB ?_
      intro x hx
      have hx1 : ψ (x ⬝ᵥ y) = 1 := by
        by_contra hne
        apply hx
        simp [hφ₁, hne]
      have hx2 : φ x ≠ 0 := by
        intro h0
        apply hx
        simp [hφ₁, h0]
      obtain ⟨y', hy', hy'ne⟩ := h x hx2
      rcases Finset.mem_insert.mp hy' with rfl | hy't
      · exact absurd hx1 hy'ne
      · exact ⟨y', hy't, hy'ne⟩
  have vanish : ∀ φ ∈ SB (κ → k), φ 0 = 0 → l φ = 0 := by
    intro φ hφ h0
    obtain ⟨hφl, hφc⟩ := hφ
    have hsupp : IsClosed (Function.support φ) := (hφl.isOpen_fiber 0).isClosed_compl
    have hK : IsCompact (Function.support φ) := by
      have hc := hφc.isCompact
      rwa [tsupport, hsupp.closure_eq] at hc
    have hcov : Function.support φ ⊆ ⋃ y : κ → k, {x | ψ (x ⬝ᵥ y) ≠ 1} := by
      intro x hx
      have hx0 : x ≠ 0 := by
        rintro rfl
        exact hx h0
      obtain ⟨y, hy⟩ := exists_dotProduct_ne_one hψ hx0
      exact Set.mem_iUnion.mpr ⟨y, hy⟩
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun y : κ → k => {x | ψ (x ⬝ᵥ y) ≠ 1})
      (fun y => ((hχ y).isClosed_fiber 1).isOpen_compl) hcov
    refine key t φ ⟨hφl, hφc⟩ ?_
    intro x hx
    have hxt := ht hx
    simp only [Set.mem_iUnion] at hxt
    obtain ⟨y, hy, hxy⟩ := hxt
    exact ⟨y, hy, hxy⟩
  obtain ⟨C, hC, hC0⟩ := exists_compact_mem_nhds (0 : κ → k)
  obtain ⟨O, hO⟩ := NonarchimedeanAddGroup.is_nonarchimedean C hC0
  have hOc : IsCompact (O : Set (κ → k)) := hC.of_isClosed_subset O.isClosed hO
  have hO0 : (0 : κ → k) ∈ O := O.zero_mem
  obtain ⟨φ₀, hφ₀d⟩ : ∃ f : (κ → k) → ℂ, f = fun x => if x ∈ O then 1 else 0 := ⟨_, rfl⟩
  have hφ₀ : φ₀ ∈ SB (κ → k) := by
    refine ⟨?_, HasCompactSupport.intro' hOc O.isClosed fun x hx => ?_⟩
    · rw [IsLocallyConstant.iff_exists_open]
      intro x
      by_cases hx : x ∈ O
      · refine ⟨O, O.isOpen, hx, fun x' hx' => ?_⟩
        have hx'' : x' ∈ O := hx'
        simp [hφ₀d, hx, hx'']
      · refine ⟨(O : Set (κ → k))ᶜ, O.isClosed.isOpen_compl, hx, fun x' hx' => ?_⟩
        have hx'' : x' ∉ O := hx'
        simp [hφ₀d, hx, hx'']
    · have hx' : x ∉ O := hx
      simp [hφ₀d, hx']
  refine ⟨l φ₀, fun φ hφ => ?_⟩
  have h1 : φ - φ 0 • φ₀ ∈ SB (κ → k) := Submodule.sub_mem _ hφ (Submodule.smul_mem _ _ hφ₀)
  have h2 : (φ - φ 0 • φ₀) 0 = 0 := by simp [hφ₀d, hO0]
  have h3 := vanish _ h1 h2
  rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h3
  rw [h3, mul_comm]

end GlobalTheory.CompanionTheory.WeilCoinv
