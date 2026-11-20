import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

/- English proof (translation)
Introduce `R O _ _ _ _ _ _ t`. Set `b` to `Module.Free.chooseBasis R O`. Set `f : O →+ (Module.Free.ChooseBasisIndex R O → R ⧸ Ideal.span {t})` to `{ toFun := fun x i => Ideal.Quotient.mk _ (b.repr x i) map_zero' := by ext i; simp map_add' := by intro x y; ext i; simp }`. Establish `hsurj : Function.Surjective f`. Introduce `y`.

Use `choose z hz using fun i => Ideal.Quotient.mk_surjective (y i)`. Use `⟨b.equivFun.symm z, ?_⟩` and prove the remaining obligations. Use extensionality with `i`. Use `show Ideal.Quotient.mk _ (b.equivFun (b.equivFun.symm z) i) = y i`. Rewrite using `[LinearEquiv.apply_symm_apply, hz]`.

Establish `hker : f.ker = (Ideal.span {algebraMap R O t}).toAddSubgroup`. Use extensionality with `x`. Simplify using `only [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton']`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Establish `h' : ∀ i, ∃ a, a * t = b.repr x i` using `fun i => by`. Use `congrFun h i` as an intermediate fact. Conclude with `Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 this)`. Use `choose a ha using h'`. Use `⟨b.equivFun.symm a, ?_⟩` and prove the remaining obligations.

Rewrite using `[mul_comm, ← Algebra.smul_def, ← map_smul]`. Apply `b.equivFun.injective` to reduce the goal to its premises. Rewrite using `[LinearEquiv.apply_symm_apply]`. Use extensionality with `i`. Simplify using `[← ha i, mul_comm]`.

Introduce and unpack `⟨a, rfl⟩`. Use extensionality with `i`. Use `show Ideal.Quotient.mk _ (b.repr _ i) = 0`. Rewrite using `[mul_comm, ← Algebra.smul_def, map_smul, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.mem_span_singleton'.2 ⟨b.repr a i, by simp [mul_comm]⟩`.

Establish `e` using `Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hsurj).toEquiv`. Rewrite `e` using `[hker]`. Establish `h1 : Nat.card (O ⧸ Ideal.span {algebraMap R O t}) = Nat.card (Module.Free.ChooseBasisIndex R O → R ⧸ Ideal.span {t})` using `e`. Rewrite using `[h1, Nat.card_fun, Module.finrank_eq_card_chooseBasisIndex, Nat.card_eq_fintype_card (α := Module.Free.ChooseBasisIndex R O)]`.
-/
theorem card_quot_span_algebraMap : ∀ (R O : Type) [CommRing R] [Nontrivial R] [CommRing O] [Algebra R O] [Module.Free R O] [Module.Finite R O] (t : R), Nat.card (O ⧸ Ideal.span {algebraMap R O t}) = Nat.card (R ⧸ Ideal.span {t}) ^ Module.finrank R O := by
  intro R O _ _ _ _ _ _ t
  classical
  let b := Module.Free.chooseBasis R O
  let f : O →+ (Module.Free.ChooseBasisIndex R O → R ⧸ Ideal.span {t}) :=
    { toFun := fun x i => Ideal.Quotient.mk _ (b.repr x i)
      map_zero' := by ext i; simp
      map_add' := by intro x y; ext i; simp }
  have hsurj : Function.Surjective f := by
    intro y
    choose z hz using fun i => Ideal.Quotient.mk_surjective (y i)
    refine ⟨b.equivFun.symm z, ?_⟩
    ext i
    show Ideal.Quotient.mk _ (b.equivFun (b.equivFun.symm z) i) = y i
    rw [LinearEquiv.apply_symm_apply, hz]
  have hker : f.ker = (Ideal.span {algebraMap R O t}).toAddSubgroup := by
    ext x
    simp only [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton']
    constructor
    · intro h
      have h' : ∀ i, ∃ a, a * t = b.repr x i := fun i => by
        have := congrFun h i
        exact Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 this)
      choose a ha using h'
      refine ⟨b.equivFun.symm a, ?_⟩
      rw [mul_comm, ← Algebra.smul_def, ← map_smul]
      apply b.equivFun.injective
      rw [LinearEquiv.apply_symm_apply]
      ext i
      simp [← ha i, mul_comm]
    · rintro ⟨a, rfl⟩
      ext i
      show Ideal.Quotient.mk _ (b.repr _ i) = 0
      rw [mul_comm, ← Algebra.smul_def, map_smul, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton'.2 ⟨b.repr a i, by simp [mul_comm]⟩
  have e := Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hsurj).toEquiv
  rw [hker] at e
  have h1 : Nat.card (O ⧸ Ideal.span {algebraMap R O t}) =
      Nat.card (Module.Free.ChooseBasisIndex R O → R ⧸ Ideal.span {t}) := e
  rw [h1, Nat.card_fun, Module.finrank_eq_card_chooseBasisIndex, Nat.card_eq_fintype_card (α := Module.Free.ChooseBasisIndex R O)]

end GlobalTheory.CNorm
