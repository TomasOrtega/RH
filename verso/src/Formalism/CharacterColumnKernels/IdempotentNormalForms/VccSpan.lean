import Formalism.CharacterColumnKernels.StatementN

open Finset

namespace Formalism.NG

/- English proof (translation)
Introduce `O _ X X' T T' Z p q b hexp hind f' hf' hvan π'`. Take `⟨a, haT, rfl⟩` from `hexp f' hf'`. Establish `hker : ∀ k, (⟨a k, haT k⟩ : T) ∈ ccIdeal T Z`. Introduce `k`. Rewrite using `[ccIdeal, RingHom.mem_ker]`.

Use function extensionality and compare the values at `x`. Establish `hx : x.1 ∉ Z` using `x.2`. Establish `h0` using `hind x.1 hx (fun k => a k x.1) (fun x' hx' => by`. Establish `e` using `hvan x' (by rw [hx']; exact hx)`. Simplify `e)` using `[hx', Finset.sum_apply, Pi.mul_apply, Function.comp]`.

Establish `e2` using `congrFun h0 k`. Simplify `e2` using `[resOff]`. Rewrite using `[Finset.sum_apply]`. Use `Ideal.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.mul_apply, Function.comp_apply]`.

Conclude with `Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨_, hker k, rfl⟩)`.
-/
theorem descent : StatDescent := by
  intro O _ X X' T T' Z p q b hexp hind f' hf' hvan π'
  obtain ⟨a, haT, rfl⟩ := hexp f' hf'
  have hker : ∀ k, (⟨a k, haT k⟩ : T) ∈ ccIdeal T Z := by
    intro k
    rw [ccIdeal, RingHom.mem_ker]
    funext x
    have hx : x.1 ∉ Z := x.2
    have h0 := hind x.1 hx (fun k => a k x.1) (fun x' hx' => by
      have e := hvan x' (by rw [hx']; exact hx)
      simpa [hx', Finset.sum_apply, Pi.mul_apply, Function.comp] using e)
    have e2 := congrFun h0 k
    simpa [resOff] using e2
  rw [Finset.sum_apply]
  refine Ideal.sum_mem _ fun k _ => ?_
  simp only [Pi.mul_apply, Function.comp_apply]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨_, hker k, rfl⟩)

/- English proof (translation)
Introduce `O _ _ _ X T Z x y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem s hs`. Take `⟨c, hc, rfl⟩` from `hs`. Conclude with `iInf₂_le c hc`.

Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb`. Conclude with `le_trans (le_min ha hb) IsDiscreteValuationRing.addVal_add`. Consider the case `smul r a _ ha`. Rewrite using `[smul_eq_mul, IsDiscreteValuationRing.addVal_mul]`.

Conclude with `le_trans ha le_add_self`.
-/
theorem vccSpan : StatVccSpan := by
  intro O _ _ _ X T Z x y hy
  induction hy using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨c, hc, rfl⟩ := hs
    exact iInf₂_le c hc
  | zero => simp
  | add a b _ _ ha hb =>
    exact le_trans (le_min ha hb) IsDiscreteValuationRing.addVal_add
  | smul r a _ ha =>
    rw [smul_eq_mul, IsDiscreteValuationRing.addVal_mul]
    exact le_trans ha le_add_self

end Formalism.NG
