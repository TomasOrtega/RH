import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.WeylComplementInDetCoeffSpan

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

/- English proof (translation)
Introduce `K τ W _ _ _ _ S w h m hm`. Assume the negation of the conclusion as `hne`. Choose the witnesses or unpack the hypotheses as in `⟨φ, hφ⟩ : ∃ φ : Module.Dual K W, φ (w m) ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Conclude with `hne ((Module.forall_dual_apply_eq_zero_iff K (w m)).1 hcon)`. Set `P : MvPolynomial τ K` to `∑ m' ∈ S, monomial m' (φ (w m'))`. Establish `hP : P = 0`. Apply `MvPolynomial.funext` to reduce the goal to its premises. Introduce `x`.

Use `congrArg φ (h x)` as an intermediate fact. Rewrite `this` using `[map_sum, map_zero]`. Rewrite using `[map_zero, map_sum, ← this]`. Use `Finset.sum_congr rfl fun m' _ => ?_` and prove the remaining obligations. Rewrite using `[eval_monomial, map_smul, smul_eq_mul, mul_comm]`.

Establish `hc : coeff m P = φ (w m)` using `by classical`. Simplify using `only [P, coeff_sum, coeff_monomial]`. Rewrite using `[Finset.sum_ite_eq' S m]`. Rewrite using `[if_pos hm]`. Rewrite `hc` using `[hP, coeff_zero]`.

Conclude with `hφ hc.symm`.
-/
theorem interpolation_holds : Interp := by
  intro K τ W _ _ _ _ S w h m hm
  by_contra hne
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual K W, φ (w m) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hne ((Module.forall_dual_apply_eq_zero_iff K (w m)).1 hcon)
  let P : MvPolynomial τ K := ∑ m' ∈ S, monomial m' (φ (w m'))
  have hP : P = 0 := by
    apply MvPolynomial.funext
    intro x
    have := congrArg φ (h x)
    rw [map_sum, map_zero] at this
    rw [map_zero, map_sum, ← this]
    refine Finset.sum_congr rfl fun m' _ => ?_
    rw [eval_monomial, map_smul, smul_eq_mul, mul_comm]
  have hc : coeff m P = φ (w m) := by
    classical
    simp only [P, coeff_sum, coeff_monomial]
    rw [Finset.sum_ite_eq' S m]
    rw [if_pos hm]
  rw [hP, coeff_zero] at hc
  exact hφ hc.symm

/- English proof (translation)
Establish `key : ∀ (s : Finset ι) (f : ι → A), (∀ i ∈ s, f i ∈ Submodule.span R (S i)) → (∀ i ∉ s, f i ∈ S i) → ∏ i, f i ∈ T`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro f _ h2`. Conclude with `h f fun i => h2 i (Finset.notMem_empty i)`.

Consider the case `insert a s ha ih`. Introduce `f h1 h2`. Establish `hfa` using `h1 a (Finset.mem_insert_self a s)`. Establish `hup : ∀ z : A, ∏ i, Function.update f a z i = z * ∏ i ∈ Finset.univ.erase a, f i`. Introduce `z`.

Rewrite using `[← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a), Function.update_self]`. Use `congr 1`. Use `Finset.prod_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[Function.update_of_ne (Finset.ne_of_mem_erase hi)]`. Establish `hgen : ∀ z ∈ Submodule.span R (S a), z * ∏ i ∈ Finset.univ.erase a, f i ∈ T`.

Introduce `z hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`. Rewrite using `[← hup]`. Apply `ih` to reduce the goal to its premises.

Introduce `i hi`. Establish `: i ≠ a` using `fun e => ha (e ▸ hi)`. Rewrite using `[Function.update_of_ne this]`. Conclude with `h1 i (Finset.mem_insert_of_mem hi)`. Introduce `i hi`.

Distinguish the cases in `e : i = a`. Substitute `e` using the available equality. Rewrite using `[Function.update_self]`. Conclude with `hz`. Rewrite using `[Function.update_of_ne e]`.

Conclude with `h2 i fun hh => (Finset.mem_insert.1 hh).elim e hi`. Consider the case `zero => rw [zero_mul]`. Conclude with `T.zero_mem`. Consider the case `add x y _ _ hx hy => rw [add_mul]`. Conclude with `T.add_mem hx hy`.

Consider the case `smul c x _ hx => rw [smul_mul_assoc]`. Conclude with `T.smul_mem c hx`. Use `hgen (f a) hfa` as an intermediate fact. Rewrite `this` using `[Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a)]`. Then use the resulting hypothesis. Introduce `f hf`.

Conclude with `key Finset.univ f (fun i _ => hf i) fun i hi => absurd (Finset.mem_univ i) hi`.
-/
theorem prod_span {ι R A : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing A] [Algebra R A] (S : ι → Set A)
    (T : Submodule R A) (h : ∀ f : ι → A, (∀ i, f i ∈ S i) → ∏ i, f i ∈ T) :
    ∀ f : ι → A, (∀ i, f i ∈ Submodule.span R (S i)) → ∏ i, f i ∈ T := by
  have key : ∀ (s : Finset ι) (f : ι → A), (∀ i ∈ s, f i ∈ Submodule.span R (S i)) → (∀ i ∉ s, f i ∈ S i) → ∏ i, f i ∈ T := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro f _ h2; exact h f fun i => h2 i (Finset.notMem_empty i)
    | insert a s ha ih =>
      intro f h1 h2
      have hfa := h1 a (Finset.mem_insert_self a s)
      have hup : ∀ z : A, ∏ i, Function.update f a z i = z * ∏ i ∈ Finset.univ.erase a, f i := by
        intro z
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a), Function.update_self]
        congr 1
        refine Finset.prod_congr rfl fun i hi => ?_
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      have hgen : ∀ z ∈ Submodule.span R (S a), z * ∏ i ∈ Finset.univ.erase a, f i ∈ T := by
        intro z hz
        induction hz using Submodule.span_induction with
        | mem z hz =>
          rw [← hup]
          apply ih
          · intro i hi
            have : i ≠ a := fun e => ha (e ▸ hi)
            rw [Function.update_of_ne this]
            exact h1 i (Finset.mem_insert_of_mem hi)
          · intro i hi
            by_cases e : i = a
            · subst e; rw [Function.update_self]; exact hz
            · rw [Function.update_of_ne e]
              exact h2 i fun hh => (Finset.mem_insert.1 hh).elim e hi
        | zero => rw [zero_mul]; exact T.zero_mem
        | add x y _ _ hx hy => rw [add_mul]; exact T.add_mem hx hy
        | smul c x _ hx => rw [smul_mul_assoc]; exact T.smul_mem c hx
      have := hgen (f a) hfa
      rwa [Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a)] at this
  intro f hf
  exact key Finset.univ f (fun i _ => hf i) fun i hi => absurd (Finset.mem_univ i) hi

end Formalism.L2.PairingIndexBounds.Ent
