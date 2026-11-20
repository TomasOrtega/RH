import Mathlib
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `k A _ _ _ _ ε hnil`. Use `set I : Ideal A := RingHom.ker ε with hI`. Set `W : Submodule k A` to `(I ^ 2).restrictScalars k`. Set `U : Submodule k (A ⧸ W)` to `(I.restrictScalars k).map W.mkQ`. Set `b : Module.Basis (Fin (Module.finrank k U)) k U` to `Module.finBasis k U`.

Establish `hx : ∀ j, ∃ y, y ∈ I ∧ W.mkQ y = (b j : A ⧸ W)` using `fun j => by`. Take `⟨y, hy, hy'⟩` from `Submodule.mem_map.mp (b j).2`. Conclude with `⟨y, hy, hy'⟩`. Use `choose x hxI hxq using hx`. Set `P : A →ₗ[k] A` to `LinearMap.id - (Algebra.linearMap k A) ∘ₗ ε.toLinearMap`.

Establish `hPa : ∀ a, P a = a - algebraMap k A (ε a)` using `fun a => rfl`. Establish `hP : ∀ a, P a ∈ I` using `fun a => by`. Rewrite using `[hI, RingHom.mem_ker, hPa, map_sub, AlgHom.commutes]`. Simplify using the standard rewrite rules. Set `T : A →ₗ[k] U` to `LinearMap.codRestrict U (W.mkQ ∘ₗ P) (fun a => Submodule.mem_map_of_mem (show P a ∈ I.restrictScalars k from hP a))`.

Establish `hT : ∀ a, ((T a : U) : A ⧸ W) = W.mkQ (P a)` using `fun a => rfl`. Set `l : Fin (Module.finrank k U) → A →ₗ[k] k` to `fun i => b.coord i ∘ₗ T`. Establish `hspan : ∀ y ∈ I, ∃ s ∈ Submodule.span k (Set.range x), y - s ∈ I ^ 2`. Introduce `y hy`. Set `u : U` to `⟨W.mkQ y, Submodule.mem_map_of_mem (show y ∈ I.restrictScalars k from hy)⟩`.

Use `⟨∑ j, b.repr u j • x j, Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)), ?_⟩` and prove the remaining obligations. Establish `h1 : W.mkQ (∑ j, b.repr u j • x j) = ∑ j, b.repr u j • (b j : A ⧸ W)`. Simplify using `[map_sum, hxq]`. Establish `h2` using `congrArg Subtype.val (b.sum_repr u)`. Move the coercions through the operations in `at h2`.

Establish `hq : W.mkQ (∑ j, b.repr u j • x j) = W.mkQ y` using `by rw [h1, h2]`. Establish `h0 : W.mkQ (y - ∑ j, b.repr u j • x j) = 0` using `by rw [map_sub, hq, sub_self]`. Establish `h3` using `LinearMap.mem_ker.mpr h0`. Rewrite `h3` using `[Submodule.ker_mkQ]`. Conclude with `h3`.

Set `S` to `Algebra.adjoin k (Set.range x)`. Establish `spanS : Submodule.span k (Set.range x) ≤ Subalgebra.toSubmodule S` using `Submodule.span_le.mpr (fun z hz => Algebra.subset_adjoin hz)`. Establish `spanI : Submodule.span k (Set.range x) ≤ I.restrictScalars k` using `Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hxI j)`. Establish `hstep : ∀ n : ℕ, ∀ z ∈ I ^ n, z ∈ Subalgebra.toSubmodule S ⊔ (I ^ (n + 1)).restrictScalars k`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero`. Introduce `z _`. Use `Submodule.mem_sup.mpr ⟨_, S.algebraMap_mem (ε z), P z, ?_, ?_⟩` and prove the remaining obligations. Use `show P z ∈ I ^ (0 + 1)`.

Rewrite using `[zero_add, pow_one]`. Conclude with `hP z`. Rewrite using `[hPa]`. Normalize the expressions using the abelian group laws. Consider the case `succ n ih`.

Introduce `z hz`. Rewrite `hz` using `[pow_succ']`. Use `Submodule.mul_induction_on hz ?_ (fun a c ha hc => add_mem ha hc)` and prove the remaining obligations. Introduce `y hy w hw`. Take `⟨s, hs, hys⟩` from `hspan y hy`.

Take `⟨t, ht, v, hv, htv⟩` from `Submodule.mem_sup.mp (ih w hw)`. Establish `h1 : s * v ∈ I ^ (n + 1 + 1)`. Rewrite using `[pow_succ']`. Conclude with `Ideal.mul_mem_mul (spanI hs) hv`. Establish `h2 : (y - s) * w ∈ I ^ (n + 1 + 1)`.

Rewrite using `[show n + 1 + 1 = 2 + n by omega, pow_add]; exact Ideal.mul_mem_mul hys hw`. Use `Submodule.mem_sup.mpr ⟨s * t, S.mul_mem (spanS hs) ht, s * v + (y - s) * w, add_mem h1 h2, ?_⟩` and prove the remaining obligations. Rewrite using `[← htv]`. Expand and normalize the polynomial expressions, which then agree. Establish `hall : ∀ n : ℕ, ∀ a : A, a ∈ Subalgebra.toSubmodule S ⊔ (I ^ n).restrictScalars k`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `a`. Use `Submodule.mem_sup.mpr ⟨0, zero_mem _, a, ?_, zero_add a⟩` and prove the remaining obligations.

Use `show a ∈ I ^ 0`. Rewrite using `[pow_zero, Ideal.one_eq_top]`. Conclude with `Submodule.mem_top`. Consider the case `succ n ih`. Introduce `a`.

Take `⟨s, hs, w, hw, hsw⟩` from `Submodule.mem_sup.mp (ih a)`. Take `⟨t, ht, v, hv, htv⟩` from `Submodule.mem_sup.mp (hstep n w hw)`. Use `Submodule.mem_sup.mpr ⟨s + t, add_mem hs ht, v, hv, ?_⟩` and prove the remaining obligations. Rewrite using `[← hsw, ← htv]`. Normalize the expressions using the abelian group laws.

Use `⟨Module.finrank k U, x, l, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i a c`. Establish `key : P (a * c) - (ε a • P c + ε c • P a) = P a * P c`. Simplify using `only [hPa, Algebra.smul_def, map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hmem : P (a * c) - (ε a • P c + ε c • P a) ∈ W`. Rewrite using `[key]`. Use `show P a * P c ∈ I ^ 2`. Rewrite using `[pow_two]`. Conclude with `Ideal.mul_mem_mul (hP a) (hP c)`.

Establish `hTac : T (a * c) = ε a • T c + ε c • T a`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, hT, hT, hT]`. Establish `h0 : W.mkQ (P (a * c) - (ε a • P c + ε c • P a)) = 0`. Rewrite using `[← LinearMap.mem_ker, Submodule.ker_mkQ]`.

Conclude with `hmem`. Rewrite `h0` using `[map_sub, map_add, map_smul, map_smul, sub_eq_zero]`. Conclude with `h0`. Use `show b.coord i (T (a * c)) = ε a * b.coord i (T c) + ε c * b.coord i (T a)`. Rewrite using `[hTac, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]`.

Introduce `i j`. Establish `hTx : T (x j) = b j`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hT, hPa]`. Establish `: ε (x j) = 0` using `(RingHom.mem_ker).mp (hxI j)`.

Rewrite using `[this, map_zero, sub_zero, hxq]`. Use `show b.coord i (T (x j)) = _`. Rewrite using `[hTx, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[h, Ne.symm h]`. Take `⟨N, hN⟩` from `hnil`. Establish `hv : (I ^ N).restrictScalars k = ⊥`. Rewrite using `[hI, hN, Submodule.zero_eq_bot, Submodule.restrictScalars_bot]`.

Use `eq_top_iff.mpr (fun a _ => ?_)` and prove the remaining obligations. Use `hall N a` as an intermediate fact. Rewrite `this` using `[hv, sup_bot_eq]`. Conclude with `this`.
-/
theorem exists_generators_dual_point_derivations :
    ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] [Module.Finite k A] (ε : A →ₐ[k] k),
      IsNilpotent (RingHom.ker ε) → ∃ (d : ℕ) (x : Fin d → A) (l : Fin d → A →ₗ[k] k),
        (∀ i a b, l i (a * b) = ε a * l i b + ε b * l i a) ∧
        (∀ i j, l i (x j) = if i = j then 1 else 0) ∧ Algebra.adjoin k (Set.range x) = ⊤ := by
  intro k A _ _ _ _ ε hnil
  set I : Ideal A := RingHom.ker ε with hI
  let W : Submodule k A := (I ^ 2).restrictScalars k
  let U : Submodule k (A ⧸ W) := (I.restrictScalars k).map W.mkQ
  let b : Module.Basis (Fin (Module.finrank k U)) k U := Module.finBasis k U
  have hx : ∀ j, ∃ y, y ∈ I ∧ W.mkQ y = (b j : A ⧸ W) := fun j => by
    obtain ⟨y, hy, hy'⟩ := Submodule.mem_map.mp (b j).2
    exact ⟨y, hy, hy'⟩
  choose x hxI hxq using hx
  let P : A →ₗ[k] A := LinearMap.id - (Algebra.linearMap k A) ∘ₗ ε.toLinearMap
  have hPa : ∀ a, P a = a - algebraMap k A (ε a) := fun a => rfl
  have hP : ∀ a, P a ∈ I := fun a => by
    rw [hI, RingHom.mem_ker, hPa, map_sub, AlgHom.commutes]
    simp
  let T : A →ₗ[k] U := LinearMap.codRestrict U (W.mkQ ∘ₗ P)
    (fun a => Submodule.mem_map_of_mem (show P a ∈ I.restrictScalars k from hP a))
  have hT : ∀ a, ((T a : U) : A ⧸ W) = W.mkQ (P a) := fun a => rfl
  let l : Fin (Module.finrank k U) → A →ₗ[k] k := fun i => b.coord i ∘ₗ T
  have hspan : ∀ y ∈ I, ∃ s ∈ Submodule.span k (Set.range x), y - s ∈ I ^ 2 := by
    intro y hy
    let u : U := ⟨W.mkQ y, Submodule.mem_map_of_mem (show y ∈ I.restrictScalars k from hy)⟩
    refine ⟨∑ j, b.repr u j • x j,
      Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)), ?_⟩
    have h1 : W.mkQ (∑ j, b.repr u j • x j) = ∑ j, b.repr u j • (b j : A ⧸ W) := by
      simp [map_sum, hxq]
    have h2 := congrArg Subtype.val (b.sum_repr u)
    push_cast at h2
    have hq : W.mkQ (∑ j, b.repr u j • x j) = W.mkQ y := by rw [h1, h2]
    have h0 : W.mkQ (y - ∑ j, b.repr u j • x j) = 0 := by rw [map_sub, hq, sub_self]
    have h3 := LinearMap.mem_ker.mpr h0
    rw [Submodule.ker_mkQ] at h3
    exact h3
  let S := Algebra.adjoin k (Set.range x)
  have spanS : Submodule.span k (Set.range x) ≤ Subalgebra.toSubmodule S :=
    Submodule.span_le.mpr (fun z hz => Algebra.subset_adjoin hz)
  have spanI : Submodule.span k (Set.range x) ≤ I.restrictScalars k :=
    Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hxI j)
  have hstep : ∀ n : ℕ, ∀ z ∈ I ^ n,
      z ∈ Subalgebra.toSubmodule S ⊔ (I ^ (n + 1)).restrictScalars k := by
    intro n
    induction n with
    | zero =>
      intro z _
      refine Submodule.mem_sup.mpr ⟨_, S.algebraMap_mem (ε z), P z, ?_, ?_⟩
      · show P z ∈ I ^ (0 + 1)
        rw [zero_add, pow_one]; exact hP z
      · rw [hPa]; abel
    | succ n ih =>
      intro z hz
      rw [pow_succ'] at hz
      refine Submodule.mul_induction_on hz ?_ (fun a c ha hc => add_mem ha hc)
      intro y hy w hw
      obtain ⟨s, hs, hys⟩ := hspan y hy
      obtain ⟨t, ht, v, hv, htv⟩ := Submodule.mem_sup.mp (ih w hw)
      have h1 : s * v ∈ I ^ (n + 1 + 1) := by
        rw [pow_succ']; exact Ideal.mul_mem_mul (spanI hs) hv
      have h2 : (y - s) * w ∈ I ^ (n + 1 + 1) := by
        rw [show n + 1 + 1 = 2 + n by omega, pow_add]; exact Ideal.mul_mem_mul hys hw
      refine Submodule.mem_sup.mpr ⟨s * t, S.mul_mem (spanS hs) ht, s * v + (y - s) * w,
        add_mem h1 h2, ?_⟩
      rw [← htv]; ring
  have hall : ∀ n : ℕ, ∀ a : A, a ∈ Subalgebra.toSubmodule S ⊔ (I ^ n).restrictScalars k := by
    intro n
    induction n with
    | zero =>
      intro a
      refine Submodule.mem_sup.mpr ⟨0, zero_mem _, a, ?_, zero_add a⟩
      show a ∈ I ^ 0
      rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
    | succ n ih =>
      intro a
      obtain ⟨s, hs, w, hw, hsw⟩ := Submodule.mem_sup.mp (ih a)
      obtain ⟨t, ht, v, hv, htv⟩ := Submodule.mem_sup.mp (hstep n w hw)
      refine Submodule.mem_sup.mpr ⟨s + t, add_mem hs ht, v, hv, ?_⟩
      rw [← hsw, ← htv]; abel
  refine ⟨Module.finrank k U, x, l, ?_, ?_, ?_⟩
  · intro i a c
    have key : P (a * c) - (ε a • P c + ε c • P a) = P a * P c := by
      simp only [hPa, Algebra.smul_def, map_mul]; ring
    have hmem : P (a * c) - (ε a • P c + ε c • P a) ∈ W := by
      rw [key]
      show P a * P c ∈ I ^ 2
      rw [pow_two]; exact Ideal.mul_mem_mul (hP a) (hP c)
    have hTac : T (a * c) = ε a • T c + ε c • T a := by
      apply Subtype.ext
      rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, hT, hT, hT]
      have h0 : W.mkQ (P (a * c) - (ε a • P c + ε c • P a)) = 0 := by
        rw [← LinearMap.mem_ker, Submodule.ker_mkQ]; exact hmem
      rw [map_sub, map_add, map_smul, map_smul, sub_eq_zero] at h0
      exact h0
    show b.coord i (T (a * c)) = ε a * b.coord i (T c) + ε c * b.coord i (T a)
    rw [hTac, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  · intro i j
    have hTx : T (x j) = b j := by
      apply Subtype.ext
      rw [hT, hPa]
      have : ε (x j) = 0 := (RingHom.mem_ker).mp (hxI j)
      rw [this, map_zero, sub_zero, hxq]
    show b.coord i (T (x j)) = _
    rw [hTx, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  · obtain ⟨N, hN⟩ := hnil
    have hv : (I ^ N).restrictScalars k = ⊥ := by
      rw [hI, hN, Submodule.zero_eq_bot, Submodule.restrictScalars_bot]
    refine eq_top_iff.mpr (fun a _ => ?_)
    have := hall N a
    rw [hv, sup_bot_eq] at this
    exact this

end GlobalTheory
