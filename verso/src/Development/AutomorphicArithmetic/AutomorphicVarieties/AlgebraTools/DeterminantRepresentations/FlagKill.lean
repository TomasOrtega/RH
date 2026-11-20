import Mathlib

open Polynomial Matrix

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Simplify to obtain the desired conclusion from the available facts.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts.
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
Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
theorem UpperTheory.V.AlgebraTools.Det.flagKill :
    ∀ {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (n : ℕ) (W : ℕ → Submodule R V) (f : Fin n → Module.End R V),
    W 0 = ⊥ → W n = ⊤ → (∀ j : Fin n, ∀ v ∈ W (j + 1), f j v ∈ W j) → (List.ofFn f).prod = 0 := by
  intro R V _ _ _ n W f h0 hn hf
  ext v
  have h := UpperTheory.V.AlgebraTools.Det.flag_product_maps_into W n f hf v (by rw [hn]; exact Submodule.mem_top)
  rw [h0, Submodule.mem_bot] at h
  simpa using h
