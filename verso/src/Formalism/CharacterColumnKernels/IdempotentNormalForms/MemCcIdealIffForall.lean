import Formalism.CharacterColumnKernels.StatementBC

open Finset

noncomputable section

namespace Formalism.NG

/- English proof (translation)
Unfold `ccIdeal`. Rewrite using `[RingHom.mem_ker]`. Prove the components needed by the constructor for the conclusion. Introduce `h x hx`. Use `congrFun h ⟨x, hx⟩` as an intermediate fact.

Simplify `this` using `[resOff]`. Introduce `h`. Use function extensionality and compare the values at `x`. Simplify using `[resOff, h x.1 x.2]`.
-/
theorem mem_ccIdeal_iff_forall {O : Type*} [CommRing O] {X : Type*} (T : Subalgebra O (X → O))
    (Z : Set X) (c : T) : c ∈ ccIdeal T Z ↔ ∀ x ∉ Z, (c : X → O) x = 0 := by
  unfold ccIdeal
  rw [RingHom.mem_ker]
  constructor
  · intro h x hx
    have := congrFun h ⟨x, hx⟩
    simpa [resOff] using this
  · intro h
    funext x
    simp [resOff, h x.1 x.2]

/- English proof (translation)
Introduce `O O' _ _ _ _ _ _ _ _ _ e he X T T' hT' Z x`. Use `set b := Module.Free.chooseBasis O O' with hb`. Use `set φ : (X → O) → (X → O') := fun f => algebraMap O O' ∘ f with hφ`. Establish `hdec : ∀ f ∈ Submodule.span O' (φ '' (T : Set (X → O))), ∃ g : Module.Free.ChooseBasisIndex O O' → (X → O), (∀ j, g j ∈ T) ∧ f = ∑ j, b j • φ (g j)`. Introduce `f hf`.

Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem f hf`. Take `⟨t, ht, rfl⟩` from `hf`. Use `⟨fun j => b.repr 1 j • t, fun j => T.smul_mem ht _, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x'`.

Simplify using `only [hφ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[b.sum_repr, mul_one]`. Use `_ = ∑ j, b j * algebraMap O O' (b.repr 1 j * t x') := by`. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `zero`. Use `⟨0, fun j => T.zero_mem, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `x'`. Simplify using `[hφ]`. Consider the case `add f f' _ _ hf hf'`. Take `⟨g, hg, rfl⟩` from `hf`. Take `⟨g', hg', rfl⟩` from `hf'`.

Use `⟨g + g', fun j => T.add_mem (hg j) (hg' j), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x'`. Simplify using `only [hφ, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply, map_add, mul_add, Finset.sum_add_distrib]`. Consider the case `smul o f _ hf`. Take `⟨g, hg, rfl⟩` from `hf`.

Use `⟨fun k => ∑ j, b.repr (o * b j) k • g j, fun k => T.sum_mem fun j _ => T.smul_mem (hg j) _, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x'`. Simplify using `only [hφ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply, map_sum, map_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun j _ => by ring`. Use `_ = ∑ j, (∑ k, b.repr (o * b j) k • b k) * algebraMap O O' (g j x') := by`. Repeatedly rewrite using `[b.sum_repr]`. Use `_ = ∑ k, b k * ∑ j, algebraMap O O' (b.repr (o * b j) k) * algebraMap O O' (g j x') := by`. Simplify using `only [Finset.sum_mul, Finset.mul_sum, Algebra.smul_def]`.

Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring`. Establish `hvan : ∀ (g : Module.Free.ChooseBasisIndex O O' → X → O) (x' : X), ∑ j, b j * algebraMap O O' (g j x') = 0 → ∀ j, g j x' = 0`. Introduce `g x' h`. Establish `h2 : ∑ j, g j x' • b j = 0`.

Rewrite using `[← h]`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [Algebra.smul_def, mul_comm]`. Conclude with `Fintype.linearIndependent_iff.mp b.linearIndependent _ h2`. Apply `le_antisymm` to reduce the goal to its premises. Establish `hne : ((fun c : T => IsDiscreteValuationRing.addVal O ((c : X → O) x)) '' (ccIdeal T Z : Set T)).Nonempty` using `⟨_, 0, (ccIdeal T Z).zero_mem, rfl⟩`.

Take `⟨c0, hc0, hc0eq⟩` from `csInf_mem hne`. Establish `hvcc : vcc T Z x = IsDiscreteValuationRing.addVal O ((c0 : X → O) x)`. Rewrite using `[show IsDiscreteValuationRing.addVal O ((c0 : X → O) x) = _ from hc0eq, sInf_image]`. Both sides reduce to the same expression. Rewrite using `[hvcc, ← he]`.

Establish `hmem : φ (c0 : X → O) ∈ T'`. Establish `h1 : φ (c0 : X → O) ∈ (T' : Set (X → O'))`. Rewrite using `[hT']`. Conclude with `Submodule.subset_span ⟨c0, c0.2, rfl⟩`. Conclude with `h1`.

Establish `hc0' : (⟨φ (c0 : X → O), hmem⟩ : T') ∈ ccIdeal T' Z`. Rewrite using `[mem_ccIdeal_iff_forall]`. Introduce `x' hx'`. Establish `h0` using `(mem_ccIdeal_iff_forall T Z c0).mp hc0 x' hx'`. Simplify using `[hφ, h0]`.

Conclude with `iInf₂_le _ hc0'`. Unfold `vcc`. Use `le_iInf₂ fun c' hc' => ?_` and prove the remaining obligations. Establish `hc'span : (c' : X → O') ∈ Submodule.span O' (φ '' (T : Set (X → O)))`. Establish `h1 : (c' : X → O') ∈ (T' : Set (X → O'))` using `c'.2`.

Rewrite `h1` using `[hT']`. Conclude with `h1`. Take `⟨g, hg, hgeq⟩` from `hdec _ hc'span`. Establish `hgZ : ∀ j, (⟨g j, hg j⟩ : T) ∈ ccIdeal T Z`. Introduce `j`.

Rewrite using `[mem_ccIdeal_iff_forall]`. Introduce `x' hx'`. Establish `h0` using `(mem_ccIdeal_iff_forall T' Z c').mp hc' x' hx'`. Rewrite `h0` using `[hgeq]`. Simplify using `only [hφ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply] at h0`.

Conclude with `hvan g x' h0 j`. Rewrite using `[hgeq]`. Simplify using `only [hφ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply]`. Use `AddValuation.map_le_sum _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[AddValuation.map_mul, he]`.

Use `le_trans ?_ le_add_self` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_left (iInf₂_le (⟨g j, hg j⟩ : T) (hgZ j)) (zero_le)`.
-/
theorem vccBaseChange : StatVccBaseChange := by
  intro O O' _ _ _ _ _ _ _ _ _ e he X T T' hT' Z x
  classical
  set b := Module.Free.chooseBasis O O' with hb
  set φ : (X → O) → (X → O') := fun f => algebraMap O O' ∘ f with hφ
  have hdec : ∀ f ∈ Submodule.span O' (φ '' (T : Set (X → O))),
      ∃ g : Module.Free.ChooseBasisIndex O O' → (X → O), (∀ j, g j ∈ T) ∧ f = ∑ j, b j • φ (g j) := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨t, ht, rfl⟩ := hf
      refine ⟨fun j => b.repr 1 j • t, fun j => T.smul_mem ht _, ?_⟩
      funext x'
      simp only [hφ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply]
      calc algebraMap O O' (t x') = algebraMap O O' (t x') * ∑ j, b.repr 1 j • b j := by
            rw [b.sum_repr, mul_one]
        _ = ∑ j, b j * algebraMap O O' (b.repr 1 j * t x') := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Algebra.smul_def, map_mul]
            ring
    | zero =>
      refine ⟨0, fun j => T.zero_mem, ?_⟩
      funext x'
      simp [hφ]
    | add f f' _ _ hf hf' =>
      obtain ⟨g, hg, rfl⟩ := hf
      obtain ⟨g', hg', rfl⟩ := hf'
      refine ⟨g + g', fun j => T.add_mem (hg j) (hg' j), ?_⟩
      funext x'
      simp only [hφ, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply,
        map_add, mul_add, Finset.sum_add_distrib]
    | smul o f _ hf =>
      obtain ⟨g, hg, rfl⟩ := hf
      refine ⟨fun k => ∑ j, b.repr (o * b j) k • g j, fun k => T.sum_mem fun j _ => T.smul_mem (hg j) _, ?_⟩
      funext x'
      simp only [hφ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply, map_sum, map_mul]
      calc o * ∑ j, b j * algebraMap O O' (g j x') = ∑ j, (o * b j) * algebraMap O O' (g j x') := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by ring
        _ = ∑ j, (∑ k, b.repr (o * b j) k • b k) * algebraMap O O' (g j x') := by
            simp_rw [b.sum_repr]
        _ = ∑ k, b k * ∑ j, algebraMap O O' (b.repr (o * b j) k) * algebraMap O O' (g j x') := by
            simp only [Finset.sum_mul, Finset.mul_sum, Algebra.smul_def]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  have hvan : ∀ (g : Module.Free.ChooseBasisIndex O O' → X → O) (x' : X),
      ∑ j, b j * algebraMap O O' (g j x') = 0 → ∀ j, g j x' = 0 := by
    intro g x' h
    have h2 : ∑ j, g j x' • b j = 0 := by
      rw [← h]
      exact Finset.sum_congr rfl fun j _ => by rw [Algebra.smul_def, mul_comm]
    exact Fintype.linearIndependent_iff.mp b.linearIndependent _ h2
  apply le_antisymm
  · have hne : ((fun c : T => IsDiscreteValuationRing.addVal O ((c : X → O) x)) ''
        (ccIdeal T Z : Set T)).Nonempty := ⟨_, 0, (ccIdeal T Z).zero_mem, rfl⟩
    obtain ⟨c0, hc0, hc0eq⟩ := csInf_mem hne
    have hvcc : vcc T Z x = IsDiscreteValuationRing.addVal O ((c0 : X → O) x) := by
      rw [show IsDiscreteValuationRing.addVal O ((c0 : X → O) x) = _ from hc0eq, sInf_image]
      rfl
    rw [hvcc, ← he]
    have hmem : φ (c0 : X → O) ∈ T' := by
      have h1 : φ (c0 : X → O) ∈ (T' : Set (X → O')) := by
        rw [hT']
        exact Submodule.subset_span ⟨c0, c0.2, rfl⟩
      exact h1
    have hc0' : (⟨φ (c0 : X → O), hmem⟩ : T') ∈ ccIdeal T' Z := by
      rw [mem_ccIdeal_iff_forall]
      intro x' hx'
      have h0 := (mem_ccIdeal_iff_forall T Z c0).mp hc0 x' hx'
      simp [hφ, h0]
    exact iInf₂_le _ hc0'
  · unfold vcc
    refine le_iInf₂ fun c' hc' => ?_
    have hc'span : (c' : X → O') ∈ Submodule.span O' (φ '' (T : Set (X → O))) := by
      have h1 : (c' : X → O') ∈ (T' : Set (X → O')) := c'.2
      rw [hT'] at h1
      exact h1
    obtain ⟨g, hg, hgeq⟩ := hdec _ hc'span
    have hgZ : ∀ j, (⟨g j, hg j⟩ : T) ∈ ccIdeal T Z := by
      intro j
      rw [mem_ccIdeal_iff_forall]
      intro x' hx'
      have h0 := (mem_ccIdeal_iff_forall T' Z c').mp hc' x' hx'
      rw [hgeq] at h0
      simp only [hφ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply] at h0
      exact hvan g x' h0 j
    rw [hgeq]
    simp only [hφ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply]
    refine AddValuation.map_le_sum _ fun j _ => ?_
    rw [AddValuation.map_mul, he]
    refine le_trans ?_ le_add_self
    exact mul_le_mul_of_nonneg_left (iInf₂_le (⟨g j, hg j⟩ : T) (hgZ j)) (zero_le)

end Formalism.NG
