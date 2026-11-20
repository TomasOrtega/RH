import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntIndMemSB

open MeasureTheory Matrix ValuativeRel

namespace GlobalTheory.HeisUnit

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open Classical in

/- English proof (translation)
Simplify using `only [intInd, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]`.
-/
theorem intInd_apply {n d : ℕ} (M : Matrix (Fin n) (Fin d) k) :
    intInd k n d M = if ∀ i j, M i j ∈ 𝒪[k] then 1 else 0 := by
  classical
  simp only [intInd, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]

/- English proof (translation)
Establish `ht : t = Ideal.Quotient.mk _ (Quotient.out t)` using `(Quotient.out_eq t).symm`. Use `set a := Quotient.out t`. Establish `hϖ0 : (ϖ : k) ≠ 0` using `ϖ.ne_zero`. Prove the components needed by the constructor for the conclusion. Introduce `hc`.

Establish `hy : (ϖ : k) * y = ϖ * (y - (ϖ : k)⁻¹ * a) + a` using `by field_simp; ring`. Establish `hmem : (ϖ : k) * y ∈ 𝒪[k]` using `hy ▸ add_mem (mul_mem hϖ.mem hc) a.2`. Use `⟨hmem, ?_⟩` and prove the remaining obligations. Rewrite using `[ht, Ideal.Quotient.eq, pow_one, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton']`. Use `⟨-⟨_, hc⟩, Subtype.ext ?_⟩` and prove the remaining obligations.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `⟨h, e⟩`. Establish `e'` using `ht.symm.trans e`.

Rewrite `e'` using `[Ideal.Quotient.eq, pow_one, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton']`. Take `⟨c, hc⟩` from `e'`. Establish `hc' : (c : k) * ϖ = a - ϖ * y` using `by simpa using congrArg Subtype.val hc`. Establish `hinv : (ϖ : k)⁻¹ * ϖ = 1` using `inv_mul_cancel₀ hϖ0`. Establish `: y - (ϖ : k)⁻¹ * a = -(c : k)`.

Take the linear combination `(ϖ : k)⁻¹ * hc' - (y + c) * hinv`. Rewrite using `[this]`. Conclude with `neg_mem c.2`.
-/
theorem sub_inv_mul_out_mem_iff {ϖ : kˣ} (hϖ : SplitFlip.IsUnif ϖ) (y : k) (t : SplitFlip.Res k 1) :
    y - (ϖ : k)⁻¹ * ((Quotient.out t : 𝒪[k]) : k) ∈ 𝒪[k] ↔
      ∃ h : (ϖ : k) * y ∈ 𝒪[k], t = Ideal.Quotient.mk _ ⟨(ϖ : k) * y, h⟩ := by
  have ht : t = Ideal.Quotient.mk _ (Quotient.out t) := (Quotient.out_eq t).symm
  set a := Quotient.out t
  have hϖ0 : (ϖ : k) ≠ 0 := ϖ.ne_zero
  constructor
  · intro hc
    have hy : (ϖ : k) * y = ϖ * (y - (ϖ : k)⁻¹ * a) + a := by field_simp; ring
    have hmem : (ϖ : k) * y ∈ 𝒪[k] := hy ▸ add_mem (mul_mem hϖ.mem hc) a.2
    refine ⟨hmem, ?_⟩
    rw [ht, Ideal.Quotient.eq, pow_one, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton']
    refine ⟨-⟨_, hc⟩, Subtype.ext ?_⟩
    push_cast
    field_simp
    ring
  · rintro ⟨h, e⟩
    have e' := ht.symm.trans e
    rw [Ideal.Quotient.eq, pow_one, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at e'
    obtain ⟨c, hc⟩ := e'
    have hc' : (c : k) * ϖ = a - ϖ * y := by simpa using congrArg Subtype.val hc
    have hinv : (ϖ : k)⁻¹ * ϖ = 1 := inv_mul_cancel₀ hϖ0
    have : y - (ϖ : k)⁻¹ * a = -(c : k) := by
      linear_combination (ϖ : k)⁻¹ * hc' - (y + c) * hinv
    rw [this]
    exact neg_mem c.2

/- English proof (translation)
Introduce `k _ _ _ _ n d ϖ hϖ i0 Y`. Establish `hL : ∀ i j, ((diagAt ϖ i0).valᵀ * Y) i j = (if i = i0 then (ϖ : k) else 1) * Y i j`. Introduce `i j`. Rewrite using `[diagAt_val, diagonal_transpose, diagonal_mul]`. Establish `hR : ∀ (T : Fin d → SplitFlip.Res k 1) i j, (Y + cosetRep ϖ i0 T) i j = if i = i0 then Y i j - (ϖ : k)⁻¹ * ((Quotient.out (T j) : 𝒪[k]) : k) else Y i j`.

Introduce `T i j`. Simplify using `only [cosetRep, Matrix.add_apply, Matrix.of_apply]`. Apply the tactic sequence `split_ifs <;> ring`. Distinguish the cases in `hQR : (∀ i j, i ≠ i0 → Y i j ∈ 𝒪[k]) ∧ ∀ j, (ϖ : k) * Y i0 j ∈ 𝒪[k]`. Take `⟨hQ, hRR⟩` from `hQR`.

Set `T0 : Fin d → SplitFlip.Res k 1` to `fun j => Ideal.Quotient.mk _ ⟨_, hRR j⟩`. Establish `hl : intInd k n d ((diagAt ϖ i0).valᵀ * Y) = 1`. Rewrite using `[intInd_apply, if_pos]`. Introduce `i j`. Rewrite using `[hL]`.

Use `split_ifs with h`. Substitute `h` using the available equality. Conclude with `hRR j`. Rewrite using `[one_mul]`. Conclude with `hQ i j h`.

Establish `hs : ∀ T, intInd k n d (Y + cosetRep ϖ i0 T) = if T = T0 then 1 else 0`. Introduce `T`. Rewrite using `[intInd_apply]`. Distinguish the cases in `hT : T = T0`. Rewrite using `[if_pos hT, if_pos]`.

Introduce `i j`. Rewrite using `[hR]`. Use `split_ifs with h`. Substitute `h; exact (sub_inv_mul_out_mem_iff hϖ _ _).2 ⟨hRR j, by rw [hT]⟩` using the available equality. Conclude with `hQ i j h`.

Rewrite using `[if_neg hT, if_neg]`. Introduce `hm`. Apply `hT` to reduce the goal to its premises. Use function extensionality and compare the values at `j`. Use `hm i0 j` as an intermediate fact.

Rewrite `this` using `[hR, if_pos rfl]`. Take `⟨_, e⟩` from `(sub_inv_mul_out_mem_iff hϖ _ _).1 this`. Conclude with `e`. Rewrite using `[hl, Finset.sum_congr rfl (fun T _ => hs T), Finset.sum_ite_eq']`. Simplify using the standard rewrite rules.

Establish `hl : intInd k n d ((diagAt ϖ i0).valᵀ * Y) = 0`. Rewrite using `[intInd_apply, if_neg]`. Introduce `hm`. Use `hQR ⟨fun i j h => ?_, fun j => ?_⟩` and prove the remaining obligations. Use `hm i j` as an intermediate fact.

Rewrite `this` using `[hL, if_neg h, one_mul]`. Then use the resulting hypothesis. Use `hm i0 j` as an intermediate fact. Rewrite `this` using `[hL, if_pos rfl]`. Then use the resulting hypothesis. Rewrite using `[hl]`. Use `symm`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `T _`. Rewrite using `[intInd_apply, if_neg]`. Introduce `hm`. Use `hQR ⟨fun i j h => ?_, fun j => ?_⟩` and prove the remaining obligations.

Use `hm i j` as an intermediate fact. Rewrite `this` using `[hR, if_neg h]`. Then use the resulting hypothesis. Use `hm i0 j` as an intermediate fact. Rewrite `this` using `[hR, if_pos rfl]`. Conclude with `((sub_inv_mul_out_mem_iff hϖ _ _).1 this).1`.
-/
theorem intInd_diagAt_eq_sum : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ} (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (i0 : Fin n) (Y : Matrix (Fin n) (Fin d) k),
    GlobalTheory.HeisUnit.intInd k n d ((GlobalTheory.HeisUnit.diagAt ϖ i0).valᵀ * Y) =
      ∑ T : Fin d → GlobalTheory.SplitFlip.Res k 1, GlobalTheory.HeisUnit.intInd k n d (Y + GlobalTheory.HeisUnit.cosetRep ϖ i0 T) := by
  intro k _ _ _ _ n d ϖ hϖ i0 Y
  classical
  have hL : ∀ i j, ((diagAt ϖ i0).valᵀ * Y) i j = (if i = i0 then (ϖ : k) else 1) * Y i j := by
    intro i j
    rw [diagAt_val, diagonal_transpose, diagonal_mul]
  have hR : ∀ (T : Fin d → SplitFlip.Res k 1) i j, (Y + cosetRep ϖ i0 T) i j =
      if i = i0 then Y i j - (ϖ : k)⁻¹ * ((Quotient.out (T j) : 𝒪[k]) : k) else Y i j := by
    intro T i j
    simp only [cosetRep, Matrix.add_apply, Matrix.of_apply]
    split_ifs <;> ring
  by_cases hQR : (∀ i j, i ≠ i0 → Y i j ∈ 𝒪[k]) ∧ ∀ j, (ϖ : k) * Y i0 j ∈ 𝒪[k]
  · obtain ⟨hQ, hRR⟩ := hQR
    let T0 : Fin d → SplitFlip.Res k 1 := fun j => Ideal.Quotient.mk _ ⟨_, hRR j⟩
    have hl : intInd k n d ((diagAt ϖ i0).valᵀ * Y) = 1 := by
      rw [intInd_apply, if_pos]
      intro i j
      rw [hL]
      split_ifs with h
      · subst h; exact hRR j
      · rw [one_mul]; exact hQ i j h
    have hs : ∀ T, intInd k n d (Y + cosetRep ϖ i0 T) = if T = T0 then 1 else 0 := by
      intro T
      rw [intInd_apply]
      by_cases hT : T = T0
      · rw [if_pos hT, if_pos]
        intro i j
        rw [hR]
        split_ifs with h
        · subst h; exact (sub_inv_mul_out_mem_iff hϖ _ _).2 ⟨hRR j, by rw [hT]⟩
        · exact hQ i j h
      · rw [if_neg hT, if_neg]
        intro hm
        apply hT
        funext j
        have := hm i0 j
        rw [hR, if_pos rfl] at this
        obtain ⟨_, e⟩ := (sub_inv_mul_out_mem_iff hϖ _ _).1 this
        exact e
    rw [hl, Finset.sum_congr rfl (fun T _ => hs T), Finset.sum_ite_eq']
    simp
  · have hl : intInd k n d ((diagAt ϖ i0).valᵀ * Y) = 0 := by
      rw [intInd_apply, if_neg]
      intro hm
      refine hQR ⟨fun i j h => ?_, fun j => ?_⟩
      · have := hm i j; rwa [hL, if_neg h, one_mul] at this
      · have := hm i0 j; rwa [hL, if_pos rfl] at this
    rw [hl]
    symm
    apply Finset.sum_eq_zero
    intro T _
    rw [intInd_apply, if_neg]
    intro hm
    refine hQR ⟨fun i j h => ?_, fun j => ?_⟩
    · have := hm i j; rwa [hR, if_neg h] at this
    · have := hm i0 j
      rw [hR, if_pos rfl] at this
      exact ((sub_inv_mul_out_mem_iff hϖ _ _).1 this).1

end GlobalTheory.HeisUnit
