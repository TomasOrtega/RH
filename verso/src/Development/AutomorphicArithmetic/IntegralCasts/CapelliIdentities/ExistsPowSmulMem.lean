import Mathlib

/- English proof (translation)
Introduce `O K X _ _ _ _ _ _ _ _ _ _ ϖ hϖ A B hA hB`. Establish `h1 : ∀ x ∈ Submodule.span K (↑B : Set X), ∃ d : O, d ≠ 0 ∧ d • x ∈ B`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_ne_zero, B.smul_mem _ hx⟩`.

Consider the case `zero => exact ⟨1, one_ne_zero, B.smul_mem _ B.zero_mem⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨d, hd, hdx⟩` from `hx`. Take `⟨e, he, hey⟩` from `hy`. Use `⟨d * e, mul_ne_zero hd he, ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_add]`. Use `B.add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`. Conclude with `B.smul_mem _ hdx`. Rewrite using `[mul_smul]`.

Conclude with `B.smul_mem _ hey`. Consider the case `smul r x _ hx`. Take `⟨d, hd, hdx⟩` from `hx`. Take `⟨⟨n, e⟩, hne⟩` from `IsLocalization.surj (nonZeroDivisors O) r`. Use `⟨d * e, mul_ne_zero hd (nonZeroDivisors.ne_zero e.2), ?_⟩` and prove the remaining obligations.

Establish `h : (e : O) • r • x = n • x`. Rewrite using `[← algebraMap_smul K (e : O), smul_smul, mul_comm, hne, algebraMap_smul]`. Rewrite using `[mul_smul, h, smul_smul, mul_comm, mul_smul]`. Conclude with `B.smul_mem _ hdx`. Establish `h2 : ∀ x : X, ∃ k : ℕ, ϖ ^ k • x ∈ B`.

Introduce `x`. Take `⟨d, hd, hdx⟩` from `h1 x (hB ▸ Submodule.mem_top)`. Take `⟨k, u, hu⟩` from `IsDiscreteValuationRing.associated_pow_irreducible hd hϖ`. Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite using `[← hu, mul_comm, mul_smul]`.

Conclude with `B.smul_mem _ hdx`. Use `choose f hf using h2`. Take `⟨s, rfl⟩` from `hA`. Use `⟨s.sup f, fun a ha => ?_⟩` and prove the remaining obligations. Proceed by induction on `ha using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨m, hm⟩` from `Nat.exists_eq_add_of_le (Finset.le_sup (f := f) (Finset.mem_coe.1 hx))`. Rewrite using `[hm, add_comm, pow_add, mul_smul]`. Conclude with `B.smul_mem _ (hf x)`. Consider the case `zero => exact B.smul_mem _ B.zero_mem`.

Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `B.add_mem hx hy`. Consider the case `smul r x _ hx => rw [smul_comm]`. Conclude with `B.smul_mem _ hx`.
-/
theorem UpperTheory.Reformulated.B.ExistsPowSmulMem.exists_pow_smul_mem :
    ∀ {O K X : Type} [inst : CommRing O] [inst_1 : IsDomain O]
    [IsDiscreteValuationRing O] [inst_3 : Field K] [inst_4 : Algebra O K] [IsFractionRing O K] [inst_6 : AddCommGroup X]
    [inst_7 : _root_.Module K X] [inst_8 : _root_.Module O X] [IsScalarTower O K X] (ϖ : O),
    Irreducible ϖ →
      ∀ (A B : Submodule O X), A.FG → Submodule.span K (↑B : Set X) = ⊤ → ∃ (k : ℕ), ∀ a ∈ A, ϖ ^ k • a ∈ B := by
  intro O K X _ _ _ _ _ _ _ _ _ _ ϖ hϖ A B hA hB
  have h1 : ∀ x ∈ Submodule.span K (↑B : Set X), ∃ d : O, d ≠ 0 ∧ d • x ∈ B := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact ⟨1, one_ne_zero, B.smul_mem _ hx⟩
    | zero => exact ⟨1, one_ne_zero, B.smul_mem _ B.zero_mem⟩
    | add x y _ _ hx hy =>
      obtain ⟨d, hd, hdx⟩ := hx
      obtain ⟨e, he, hey⟩ := hy
      refine ⟨d * e, mul_ne_zero hd he, ?_⟩
      rw [smul_add]
      refine B.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact B.smul_mem _ hdx
      · rw [mul_smul]; exact B.smul_mem _ hey
    | smul r x _ hx =>
      obtain ⟨d, hd, hdx⟩ := hx
      obtain ⟨⟨n, e⟩, hne⟩ := IsLocalization.surj (nonZeroDivisors O) r
      refine ⟨d * e, mul_ne_zero hd (nonZeroDivisors.ne_zero e.2), ?_⟩
      have h : (e : O) • r • x = n • x := by
        rw [← algebraMap_smul K (e : O), smul_smul, mul_comm, hne, algebraMap_smul]
      rw [mul_smul, h, smul_smul, mul_comm, mul_smul]
      exact B.smul_mem _ hdx
  have h2 : ∀ x : X, ∃ k : ℕ, ϖ ^ k • x ∈ B := by
    intro x
    obtain ⟨d, hd, hdx⟩ := h1 x (hB ▸ Submodule.mem_top)
    obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hd hϖ
    refine ⟨k, ?_⟩
    rw [← hu, mul_comm, mul_smul]
    exact B.smul_mem _ hdx
  choose f hf using h2
  obtain ⟨s, rfl⟩ := hA
  refine ⟨s.sup f, fun a ha => ?_⟩
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := f) (Finset.mem_coe.1 hx))
    rw [hm, add_comm, pow_add, mul_smul]
    exact B.smul_mem _ (hf x)
  | zero => exact B.smul_mem _ B.zero_mem
  | add x y _ _ hx hy => rw [smul_add]; exact B.add_mem hx hy
  | smul r x _ hx => rw [smul_comm]; exact B.smul_mem _ hx
