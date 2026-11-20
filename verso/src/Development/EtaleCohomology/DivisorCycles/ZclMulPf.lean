import Development.EtaleCohomology.DivisorCycles.OpenCoset

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div

namespace LateralTheory.DivDb.ZclMulPf
open LateralTheory.DivDb

/- English proof (translation)
Introduce `f hf`. Take `⟨f', hf', -⟩` from `hC C N N (LinearMap.mulLeft C s) f`. Establish `hv : f' ∈ Van (S : Set (Mat C N))`. Introduce `t ht`. Rewrite using `[hf']`.

Conclude with `hf _ (S.mul_mem hs ht)`. Use `hy f' hv` as an intermediate fact. Rewrite `this` using `[hf']`. Simplify using `using this`.
-/
theorem left_mem (hC : Chain) {C : Type} [Field C] {N : ℕ} (S : Submonoid (Mat C N))
    (s : Mat C N) (hs : s ∈ S) (y : Mat C N) (hy : y ∈ Zcl (S : Set (Mat C N))) :
    s * y ∈ Zcl (S : Set (Mat C N)) := by
  intro f hf
  obtain ⟨f', hf', -⟩ := hC C N N (LinearMap.mulLeft C s) f
  have hv : f' ∈ Van (S : Set (Mat C N)) := by
    intro t ht
    rw [hf']
    exact hf _ (S.mul_mem hs ht)
  have := hy f' hv
  rw [hf'] at this
  simpa using this

/- English proof (translation)
Introduce `f hf`. Take `⟨f', hf', -⟩` from `hC C N N (LinearMap.mulRight C y) f`. Establish `hv : f' ∈ Van (S : Set (Mat C N))`. Introduce `t ht`. Rewrite using `[hf']`.

Conclude with `left_mem hC S t ht y hy f hf`. Use `hx f' hv` as an intermediate fact. Rewrite `this` using `[hf']`. Simplify using `using this`.
-/
theorem mul_mem (hC : Chain) {C : Type} [Field C] {N : ℕ} (S : Submonoid (Mat C N))
    (x : Mat C N) (hx : x ∈ Zcl (S : Set (Mat C N))) (y : Mat C N) (hy : y ∈ Zcl (S : Set (Mat C N))) :
    x * y ∈ Zcl (S : Set (Mat C N)) := by
  intro f hf
  obtain ⟨f', hf', -⟩ := hC C N N (LinearMap.mulRight C y) f
  have hv : f' ∈ Van (S : Set (Mat C N)) := by
    intro t ht
    rw [hf']
    exact left_mem hC S t ht y hy f hf
  have := hx f' hv
  rw [hf'] at this
  simpa using this

end LateralTheory.DivDb.ZclMulPf

namespace LateralTheory.DivDb

/- English proof (translation)
Introduce `_C _ _N S x hx y hy` and use `LateralTheory.DivDb.ZclMulPf.mul_mem hC S x hx y hy`.
-/
theorem ZclMul_of (hC : Chain) : ZclMul := fun _C _ _N S x hx y hy =>
  LateralTheory.DivDb.ZclMulPf.mul_mem hC S x hx y hy

end LateralTheory.DivDb
