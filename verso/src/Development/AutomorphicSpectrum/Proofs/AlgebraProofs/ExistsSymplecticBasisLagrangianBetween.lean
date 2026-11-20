import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient

open Matrix

namespace GlobalTheory.CompanionTheory.Ar.Flat

/- English proof (translation)
Use `⟨{ carrier := {x | ∃ k : ℤ, k ≠ 0 ∧ k • x ∈ W} add_mem' := ?_, zero_mem' := ⟨1, one_ne_zero, by simp⟩, smul_mem' := ?_ }, fun x => Iff.rfl, ?_⟩` and prove the remaining obligations. Introduce and unpack `a b ⟨k, hk, ha⟩ ⟨l, hl, hb⟩`. Use `⟨k * l, mul_ne_zero hk hl, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `W.add_mem ?_ ?_` and prove the remaining obligations.

Rewrite using `[mul_comm, mul_smul]`. Conclude with `W.smul_mem _ ha`. Rewrite using `[mul_smul]`. Conclude with `W.smul_mem _ hb`. Introduce and unpack `c a ⟨k, hk, ha⟩`.

Conclude with `⟨k, hk, by rw [smul_comm]; exact W.smul_mem _ ha⟩`. Rewrite using `[GlobalTheory.isTorsionFree_quotient_iff]`. Introduce and unpack `r x hr ⟨k, hk, hx⟩`. Conclude with `⟨k * r, mul_ne_zero hk hr, by rw [mul_smul]; exact hx⟩`.
-/
theorem exists_saturation_torsionFree {Λ : Type*} [AddCommGroup Λ] (W : Submodule ℤ Λ) :
    ∃ S : Submodule ℤ Λ, (∀ x, x ∈ S ↔ ∃ k : ℤ, k ≠ 0 ∧ k • x ∈ W) ∧
      Module.IsTorsionFree ℤ (Λ ⧸ S) := by
  refine ⟨{ carrier := {x | ∃ k : ℤ, k ≠ 0 ∧ k • x ∈ W}
            add_mem' := ?_, zero_mem' := ⟨1, one_ne_zero, by simp⟩, smul_mem' := ?_ },
    fun x => Iff.rfl, ?_⟩
  · rintro a b ⟨k, hk, ha⟩ ⟨l, hl, hb⟩
    refine ⟨k * l, mul_ne_zero hk hl, ?_⟩
    rw [smul_add]
    refine W.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact W.smul_mem _ ha
    · rw [mul_smul]; exact W.smul_mem _ hb
  · rintro c a ⟨k, hk, ha⟩
    exact ⟨k, hk, by rw [smul_comm]; exact W.smul_mem _ ha⟩
  · rw [GlobalTheory.isTorsionFree_quotient_iff]
    rintro r x hr ⟨k, hk, hx⟩
    exact ⟨k * r, mul_ne_zero hk hr, by rw [mul_smul]; exact hx⟩

/- English proof (translation)
Introduce `g Λ _ _ _ B hB hp hg W hW`. Establish `hA : B.IsAlt` using `hB`. Take `⟨S, hS, hSt⟩` from `exists_saturation_torsionFree W`. Establish `hmem : ∀ x, x ∈ B.orthogonal S ↔ ∀ y ∈ W, B x y = 0`. Introduce `x`.

Rewrite using `[LinearMap.BilinForm.mem_orthogonal_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h y hy`. Conclude with `hA.isRefl _ _ (h y ((hS y).2 ⟨1, one_ne_zero, by simpa using hy⟩))`. Introduce `h y hy`.

Take `⟨k, hk, hy⟩` from `(hS y).1 hy`. Use `h _ hy` as an intermediate fact. Rewrite `this` using `[map_smul, smul_eq_mul]`. Conclude with `hA.isRefl _ _ ((mul_eq_zero.1 this).resolve_left hk)`. Establish `hoo : B.orthogonal (B.orthogonal S) = S` using `GlobalTheory.orthogonal_orthogonal_of_isTorsionFree_quotient hA hp.2 hSt`.

Establish `hiso : B.orthogonal S ≤ B.orthogonal (B.orthogonal S)`. Rewrite using `[hoo]`. Introduce `x hx`. Conclude with `(hS x).2 (hW x ((hmem x).1 hx))`. Set `v` to `Module.finBasis ℤ (B.orthogonal S)`.

Take `⟨m, b, hb, hv⟩` from `GlobalTheory.exists_isSymplecticBasis_extend hA hp (GlobalTheory.isTorsionFree_quotient_orthogonal B S) hiso v`. Establish `hc` using `GlobalTheory.IsSymplecticBasisOfType.finrank_eq b`. Establish `hc' : Fintype.card (Fin (Module.finrank ℤ (B.orthogonal S)) ⊕ Fin m) = g` using `by omega`. Set `σ` to `Fintype.equivFinOfCardEq hc'`. Establish `hb'` using `hb.reindex σ`.

Establish `hl : ∀ i, (b.reindex (σ.sumCongr σ)) (.inl i) = b (.inl (σ.symm i))`. Introduce `i`. Simplify using the standard rewrite rules. Use `⟨b.reindex (σ.sumCongr σ), fun i j => ⟨hb'.left_left i j, hb'.right_right i j, hb'.left_right i j⟩, fun i => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Use `(hS _).1 (hoo.le ((hb.orthogonal_eq_span hv).ge ?_))` and prove the remaining obligations.

Rewrite using `[hl]`. Conclude with `Submodule.subset_span (Or.inl ⟨_, rfl⟩)`. Establish `hx'` using `(hmem x).2 hx`. Establish `h1 : x = ∑ i, v.repr ⟨x, hx'⟩ i • (v i : Λ)`. Use `congrArg Subtype.val (v.sum_repr ⟨x, hx'⟩)` as an intermediate fact.

Rewrite `this` using `[Submodule.coe_sum]`. Conclude with `this.symm`. Rewrite using `[h1]`. Use `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ (.inl i), ?_⟩)` and prove the remaining obligations. Simplify using `only [hl, Equiv.symm_apply_apply, hv]`.
-/
theorem exists_symplecticBasis_lagrangian_between : ∀ (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (B : LinearMap.BilinForm ℤ Λ), (∀ x, B x x = 0) → Function.Bijective B → Module.finrank ℤ Λ = 2 * g → ∀ W : Submodule ℤ Λ, (∀ x, (∀ y ∈ W, B x y = 0) → ∃ k : ℤ, k ≠ 0 ∧ k • x ∈ W) → ∃ bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ, (∀ i j, B (bas (.inl i)) (bas (.inl j)) = 0 ∧ B (bas (.inr i)) (bas (.inr j)) = 0 ∧ B (bas (.inl i)) (bas (.inr j)) = if i = j then 1 else 0) ∧ (∀ i, ∃ k : ℤ, k ≠ 0 ∧ k • bas (.inl i) ∈ W) ∧ ∀ x, (∀ y ∈ W, B x y = 0) → x ∈ Submodule.span ℤ (Set.range fun i => bas (.inl i)) := by
  intro g Λ _ _ _ B hB hp hg W hW
  have hA : B.IsAlt := hB
  obtain ⟨S, hS, hSt⟩ := exists_saturation_torsionFree W
  have hmem : ∀ x, x ∈ B.orthogonal S ↔ ∀ y ∈ W, B x y = 0 := by
    intro x
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h y hy
      exact hA.isRefl _ _ (h y ((hS y).2 ⟨1, one_ne_zero, by simpa using hy⟩))
    · intro h y hy
      obtain ⟨k, hk, hy⟩ := (hS y).1 hy
      have := h _ hy
      rw [map_smul, smul_eq_mul] at this
      exact hA.isRefl _ _ ((mul_eq_zero.1 this).resolve_left hk)
  have hoo : B.orthogonal (B.orthogonal S) = S :=
    GlobalTheory.orthogonal_orthogonal_of_isTorsionFree_quotient hA hp.2 hSt
  have hiso : B.orthogonal S ≤ B.orthogonal (B.orthogonal S) := by
    rw [hoo]
    intro x hx
    exact (hS x).2 (hW x ((hmem x).1 hx))
  let v := Module.finBasis ℤ (B.orthogonal S)
  obtain ⟨m, b, hb, hv⟩ := GlobalTheory.exists_isSymplecticBasis_extend hA hp
    (GlobalTheory.isTorsionFree_quotient_orthogonal B S) hiso v
  have hc := GlobalTheory.IsSymplecticBasisOfType.finrank_eq b
  have hc' : Fintype.card (Fin (Module.finrank ℤ (B.orthogonal S)) ⊕ Fin m) = g := by omega
  let σ := Fintype.equivFinOfCardEq hc'
  have hb' := hb.reindex σ
  have hl : ∀ i, (b.reindex (σ.sumCongr σ)) (.inl i) = b (.inl (σ.symm i)) := by
    intro i; simp
  refine ⟨b.reindex (σ.sumCongr σ), fun i j => ⟨hb'.left_left i j, hb'.right_right i j,
    hb'.left_right i j⟩, fun i => ?_, fun x hx => ?_⟩
  · refine (hS _).1 (hoo.le ((hb.orthogonal_eq_span hv).ge ?_))
    rw [hl]
    exact Submodule.subset_span (Or.inl ⟨_, rfl⟩)
  · have hx' := (hmem x).2 hx
    have h1 : x = ∑ i, v.repr ⟨x, hx'⟩ i • (v i : Λ) := by
      have := congrArg Subtype.val (v.sum_repr ⟨x, hx'⟩)
      rw [Submodule.coe_sum] at this
      exact this.symm
    rw [h1]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨σ (.inl i), ?_⟩)
    simp only [hl, Equiv.symm_apply_apply, hv]

end GlobalTheory.CompanionTheory.Ar.Flat
