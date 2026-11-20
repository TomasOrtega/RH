import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch

open GlobalTheory.UnitLemma Matrix MeasureTheory

namespace GlobalTheory.UnitLemma.OrthoSelfDual

noncomputable def hermLeft {K : UQ} (B : InvAlg K) (x z : B.A) : B.A →ₗ[K.E] K.E where
  toFun y := B.herm x y z
  map_add' a b := by
    unfold InvAlg.herm
    rw [mul_add, add_mul, map_add]
  map_smul' e y := by
    unfold InvAlg.herm
    rw [mul_smul_comm, smul_mul_assoc, map_smul, RingHom.id_apply]

/- English proof (translation)
Establish `hlin : hermLeft B x (e j) = e.coord j`. Use `e.ext fun i => ?_` and prove the remaining obligations. Rewrite using `[Module.Basis.coord_apply, e.repr_self, Finsupp.single_apply]`. Conclude with `h i j`. Use `LinearMap.congr_fun hlin y` as an intermediate fact.

Rewrite `this` using `[Module.Basis.coord_apply]`. Conclude with `this`.
-/
theorem herm_basis {K : UQ} (B : InvAlg K) (x : B.A) (n : ℕ) (e : Module.Basis (Fin n) K.E B.A)
    (h : ∀ i j, B.herm x (e i) (e j) = if i = j then 1 else 0) (y : B.A) (j : Fin n) :
    B.herm x y (e j) = e.repr y j := by

  have hlin : hermLeft B x (e j) = e.coord j := by
    refine e.ext fun i => ?_
    rw [Module.Basis.coord_apply, e.repr_self, Finsupp.single_apply]
    exact h i j
  have := LinearMap.congr_fun hlin y
  rw [Module.Basis.coord_apply] at this
  exact this

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem w hw`. Take `⟨i, rfl⟩` from `hw`.

Introduce `j`. Rewrite using `[e.repr_self, Finsupp.single_apply]`. Use `split_ifs`. Conclude with `⟨1, map_one _⟩`. Conclude with `⟨0, map_zero _⟩`.

Consider the case `zero`. Introduce `j`. Rewrite using `[map_zero, Finsupp.zero_apply]`. Conclude with `zero_mem _`. Consider the case `add a b _ _ ha hb`.

Introduce `j`. Rewrite using `[map_add, Finsupp.add_apply]`. Conclude with `add_mem (ha j) (hb j)`. Consider the case `smul o a _ ha`. Introduce `j`.

Rewrite using `[← algebraMap_smul K.E o a, map_smul, Finsupp.smul_apply, smul_eq_mul]`. Conclude with `mul_mem ⟨o, rfl⟩ (ha j)`. Introduce `h`. Rewrite using `[← e.sum_repr y]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations.

Take `⟨o, ho⟩` from `h j`. Rewrite using `[← ho, algebraMap_smul]`. Conclude with `Submodule.smul_mem _ o (Submodule.subset_span ⟨j, rfl⟩)`.
-/
private lemma coord_lemma {K : UQ} (B : InvAlg K) (n : ℕ) (e : Module.Basis (Fin n) K.E B.A) (y : B.A) :
    y ∈ Submodule.span K.O (Set.range e) ↔ ∀ j, e.repr y j ∈ (algebraMap K.O K.E).range := by
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨i, rfl⟩ := hw
      intro j
      rw [e.repr_self, Finsupp.single_apply]
      split_ifs
      · exact ⟨1, map_one _⟩
      · exact ⟨0, map_zero _⟩
    | zero =>
      intro j
      rw [map_zero, Finsupp.zero_apply]
      exact zero_mem _
    | add a b _ _ ha hb =>
      intro j
      rw [map_add, Finsupp.add_apply]
      exact add_mem (ha j) (hb j)
    | smul o a _ ha =>
      intro j
      rw [← algebraMap_smul K.E o a, map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact mul_mem ⟨o, rfl⟩ (ha j)
  · intro h
    rw [← e.sum_repr y]
    refine Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨o, ho⟩ := h j
    rw [← ho, algebraMap_smul]
    exact Submodule.smul_mem _ o (Submodule.subset_span ⟨j, rfl⟩)

/- English proof (translation)
Rewrite using `[coord_lemma B n e y]`. Prove the components needed by the constructor for the conclusion. Introduce `hy z hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem w hw`.

Take `⟨j, rfl⟩` from `hw`. Rewrite using `[herm_basis B x n e h y j]`. Conclude with `hy j`. Consider the case `zero => simp [InvAlg.herm]`. Consider the case `add a b _ _ ha hb`.

Establish `hadd : B.herm x y (a + b) = B.herm x y a + B.herm x y b`. Unfold `InvAlg.herm`. Rewrite using `[map_add, mul_add, map_add]`. Rewrite using `[hadd]`. Conclude with `add_mem ha hb`.

Consider the case `smul o a _ ha`. Take `⟨o', ho'⟩` from `K.c_int o`. Establish `hsmul : B.herm x y (o • a) = algebraMap K.O K.E o' * B.herm x y a`. Unfold `InvAlg.herm`. Rewrite using `[← algebraMap_smul K.E o a, Algebra.smul_def, map_mul B.σ, B.σ_alg, ho', mul_left_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]`.

Rewrite using `[hsmul]`. Conclude with `mul_mem ⟨o', rfl⟩ ha`. Introduce `hy j`. Rewrite using `[← herm_basis B x n e h y j]`. Conclude with `hy (e j) (Submodule.subset_span ⟨j, rfl⟩)`.
-/
theorem span_selfDual (K : UQ) (B : InvAlg K) (x : B.A) (n : ℕ) (e : Module.Basis (Fin n) K.E B.A)
    (h : ∀ i j, B.herm x (e i) (e j) = if i = j then 1 else 0) (y : B.A) :
    y ∈ Submodule.span K.O (Set.range e) ↔
      ∀ z ∈ Submodule.span K.O (Set.range e), B.herm x y z ∈ (algebraMap K.O K.E).range := by
  rw [coord_lemma B n e y]
  constructor
  · intro hy z hz

    induction hz using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨j, rfl⟩ := hw
      rw [herm_basis B x n e h y j]
      exact hy j
    | zero => simp [InvAlg.herm]
    | add a b _ _ ha hb =>
      have hadd : B.herm x y (a + b) = B.herm x y a + B.herm x y b := by
        unfold InvAlg.herm
        rw [map_add, mul_add, map_add]
      rw [hadd]
      exact add_mem ha hb
    | smul o a _ ha =>
      obtain ⟨o', ho'⟩ := K.c_int o
      have hsmul : B.herm x y (o • a) = algebraMap K.O K.E o' * B.herm x y a := by
        unfold InvAlg.herm
        rw [← algebraMap_smul K.E o a, Algebra.smul_def, map_mul B.σ, B.σ_alg, ho', mul_left_comm,
          ← Algebra.smul_def, map_smul, smul_eq_mul]
      rw [hsmul]
      exact mul_mem ⟨o', rfl⟩ ha
  · intro hy j
    rw [← herm_basis B x n e h y j]
    exact hy (e j) (Submodule.subset_span ⟨j, rfl⟩)

end GlobalTheory.UnitLemma.OrthoSelfDual
