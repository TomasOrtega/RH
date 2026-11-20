import Mathlib
open Polynomial

/- English proof (translation)
Introduce `L C D W _ _ _ _ _ _ _ _ s j S T hj hspan hT q b hb hq`. Assume the negation of the conclusion as `hcon`. Establish `hinj : Function.Injective (aeval S q)`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`.

Assume the negation of the conclusion as `h0`. Conclude with `hcon ⟨x, h0, hx⟩`. Establish `hsurj : Function.Surjective (aeval S q)` using `LinearMap.injective_iff_surjective.mp hinj`. Establish `hpow : ∀ (n : ℕ) (x : D), (T ^ n) (j x) = j ((S ^ n) x)`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => intro x`. Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `x`.

Rewrite using `[pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, hT, ih]`. Establish `hcomm : ∀ (p : L[X]) (x : D), aeval T (p.map s) (j x) = j (aeval S p x)`. Introduce `p`. Proceed by induction on `p using Polynomial.induction_on' with`. Consider the case `add p r hp hr`.

Introduce `x`. Simplify using `only [Polynomial.map_add, map_add, LinearMap.add_apply, hp, hr]`. Consider the case `monomial n a`. Introduce `x`. Rewrite using `[Polynomial.map_monomial, aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply, hj, hpow]`.

Establish `hsurj' : Function.Surjective (aeval T (q.map s))`. Rewrite using `[← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]`. Introduce and unpack `_ ⟨y, rfl⟩`. Take `⟨x, rfl⟩` from `hsurj y`. Conclude with `⟨j x, hcomm q x⟩`.

Establish `hinj' : Function.Injective (aeval T (q.map s))` using `LinearMap.injective_iff_surjective.mpr hsurj'`. Establish `hroot : T.charpoly.IsRoot b` using `(mem_roots'.mp hb).2`. Establish `hev : T.HasEigenvalue b` using `(Module.End.hasEigenvalue_iff_isRoot_charpoly T b).mpr hroot`. Take `⟨v, hv⟩` from `hev.exists_hasEigenvector`. Establish `h1` using `Module.End.aeval_apply_of_hasEigenvector (p := q.map s) hv`.

Rewrite `h1` using `[eval_map, hq, zero_smul]`. Conclude with `hv.2 (hinj' (by rw [h1, map_zero]))`.
-/
theorem UpperTheory.exists_eigenvector_of_root :
    ∀ {L C D W : Type} [Field L] [Field C] [AddCommGroup D] [Module L D] [FiniteDimensional L D] [AddCommGroup W] [Module C W] [FiniteDimensional C W] (s : L →+* C) (j : D →+ W) (S : Module.End L D) (T : Module.End C W), (∀ (a : L) (x : D), j (a • x) = s a • j x) → Submodule.span C (Set.range j) = ⊤ → (∀ x, T (j x) = j (S x)) → ∀ (q : L[X]) (b : C), b ∈ T.charpoly.roots → q.eval₂ s b = 0 → ∃ x : D, x ≠ 0 ∧ aeval S q x = 0 := by
  intro L C D W _ _ _ _ _ _ _ _ s j S T hj hspan hT q b hb hq
  by_contra hcon
  have hinj : Function.Injective (aeval S q) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    exact hcon ⟨x, h0, hx⟩
  have hsurj : Function.Surjective (aeval S q) := LinearMap.injective_iff_surjective.mp hinj
  have hpow : ∀ (n : ℕ) (x : D), (T ^ n) (j x) = j ((S ^ n) x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, hT, ih]
  have hcomm : ∀ (p : L[X]) (x : D), aeval T (p.map s) (j x) = j (aeval S p x) := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p r hp hr =>
      intro x
      simp only [Polynomial.map_add, map_add, LinearMap.add_apply, hp, hr]
    | monomial n a =>
      intro x
      rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial, Module.End.mul_apply,
        Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply, hj, hpow]
  have hsurj' : Function.Surjective (aeval T (q.map s)) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨j x, hcomm q x⟩
  have hinj' : Function.Injective (aeval T (q.map s)) :=
    LinearMap.injective_iff_surjective.mpr hsurj'
  have hroot : T.charpoly.IsRoot b := (mem_roots'.mp hb).2
  have hev : T.HasEigenvalue b := (Module.End.hasEigenvalue_iff_isRoot_charpoly T b).mpr hroot
  obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
  have h1 := Module.End.aeval_apply_of_hasEigenvector (p := q.map s) hv
  rw [eval_map, hq, zero_smul] at h1
  exact hv.2 (hinj' (by rw [h1, map_zero]))
