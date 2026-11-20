import Mathlib

open Polynomial Matrix

/- English proof (translation)
Introduce `n`. Proceed by induction on `n generalizing W with`. Consider the case `zero`. Introduce `f _ v hv`. Simplify using `using hv`.

Consider the case `succ n ih`. Introduce `f hf v hv`. Rewrite using `[List.ofFn_succ, List.prod_cons, Module.End.mul_apply]`. Establish `h0` using `hf 0`. Simplify using `only [Fin.val_zero, zero_add] at h0`.

Apply `h0` to reduce the goal to its premises. Establish `ht` using `ih (fun k => W (k + 1)) (fun i => f i.succ) (fun j w hw => by`. Establish `hj` using `hf j.succ w (by simpa [Fin.val_succ] using hw)`. Simplify `hj) v hv` using `[Fin.val_succ]`. Simplify using `using ht`.
-/
private theorem UpperTheory.V.AlgebraTools.Det.flag_product_maps_into {R V : Type} [CommRing R] [AddCommGroup V] [Module R V]
    (W : ℕ → Submodule R V) :
    ∀ (n : ℕ) (f : Fin n → Module.End R V),
    (∀ j : Fin n, ∀ v ∈ W (j + 1), f j v ∈ W j) → ∀ v ∈ W n, (List.ofFn f).prod v ∈ W 0 := by
  intro n
  induction n generalizing W with
  | zero =>
    intro f _ v hv
    simpa using hv
  | succ n ih =>
    intro f hf v hv
    rw [List.ofFn_succ, List.prod_cons, Module.End.mul_apply]
    have h0 := hf 0
    simp only [Fin.val_zero, zero_add] at h0
    apply h0
    have ht := ih (fun k => W (k + 1)) (fun i => f i.succ) (fun j w hw => by
      have hj := hf j.succ w (by simpa [Fin.val_succ] using hw)
      simpa [Fin.val_succ] using hj) v hv
    simpa using ht

/- English proof (translation)
Introduce `R V _ _ _ n W f h0 hn hf`. Use extensionality with `v`. Establish `h` using `UpperTheory.V.AlgebraTools.Det.flag_product_maps_into W n f hf v (by rw [hn]; exact Submodule.mem_top)`. Rewrite `h` using `[h0, Submodule.mem_bot]`. Simplify using `using h`.
-/
theorem UpperTheory.V.AlgebraTools.Det.flagKill :
    ∀ {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (n : ℕ) (W : ℕ → Submodule R V) (f : Fin n → Module.End R V),
    W 0 = ⊥ → W n = ⊤ → (∀ j : Fin n, ∀ v ∈ W (j + 1), f j v ∈ W j) → (List.ofFn f).prod = 0 := by
  intro R V _ _ _ n W f h0 hn hf
  ext v
  have h := UpperTheory.V.AlgebraTools.Det.flag_product_maps_into W n f hf v (by rw [hn]; exact Submodule.mem_top)
  rw [h0, Submodule.mem_bot] at h
  simpa using h
