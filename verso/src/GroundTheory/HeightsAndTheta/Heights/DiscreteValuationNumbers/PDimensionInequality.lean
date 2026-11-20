import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsDimensionInequality
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsDimensionInequalitySteps
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u v

open Cardinal

/- English proof (translation)
Establish `: FaithfulSMul A C` using `(faithfulSMul_iff_algebraMap_injective A C).mpr hAC`. Establish `: FaithfulSMul C B` using `(faithfulSMul_iff_algebraMap_injective C B).mpr hCB`. Establish `: IsScalarTower (A ⧸ p) (C ⧸ Q) (B ⧸ P)` using `IsScalarTower.of_algebraMap_eq fun x ↦ by`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Simplify using `[Ideal.Quotient.algebraMap_mk_of_liesOver, ← IsScalarTower.algebraMap_apply]`.

Establish `t₁` using `trdeg_add_eq A C (A := B)`. Establish `t₂` using `trdeg_add_eq (A ⧸ p) (C ⧸ Q) (A := B ⧸ P)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← t₂]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ ≤ (ofENat Q.height + Algebra.trdeg C B) + Algebra.trdeg (A ⧸ p) (C ⧸ Q) := by gcongr`. Use `_ = (ofENat Q.height + Algebra.trdeg (A ⧸ p) (C ⧸ Q)) + Algebra.trdeg C B := by ring`. Use `_ ≤ (ofENat p.height + Algebra.trdeg A C) + Algebra.trdeg C B := by gcongr`. Use `_ = ofENat p.height + Algebra.trdeg A B := by rw [add_assoc, t₁]`.
-/
theorem DimensionInequality.tower_step {A : Type u} {C B : Type v} [CommRing A] [CommRing C]
    [CommRing B] [IsDomain A] [IsDomain C] [IsDomain B] [Algebra A C] [Algebra C B] [Algebra A B]
    [IsScalarTower A C B] (hAC : Function.Injective (algebraMap A C))
    (hCB : Function.Injective (algebraMap C B)) (P : Ideal B) [P.IsPrime] (Q : Ideal C) [Q.IsPrime]
    (p : Ideal A) [p.IsPrime] [P.LiesOver Q] [Q.LiesOver p] [P.LiesOver p]
    (e₁ : ofENat Q.height + Algebra.trdeg (A ⧸ p) (C ⧸ Q) ≤ ofENat p.height + Algebra.trdeg A C)
    (e₂ : ofENat P.height + Algebra.trdeg (C ⧸ Q) (B ⧸ P) ≤ ofENat Q.height + Algebra.trdeg C B) :
    ofENat P.height + Algebra.trdeg (A ⧸ p) (B ⧸ P) ≤ ofENat p.height + Algebra.trdeg A B := by
  have : FaithfulSMul A C := (faithfulSMul_iff_algebraMap_injective A C).mpr hAC
  have : FaithfulSMul C B := (faithfulSMul_iff_algebraMap_injective C B).mpr hCB
  have : IsScalarTower (A ⧸ p) (C ⧸ Q) (B ⧸ P) := IsScalarTower.of_algebraMap_eq fun x ↦ by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [Ideal.Quotient.algebraMap_mk_of_liesOver, ← IsScalarTower.algebraMap_apply]
  have t₁ := trdeg_add_eq A C (A := B)
  have t₂ := trdeg_add_eq (A ⧸ p) (C ⧸ Q) (A := B ⧸ P)
  calc ofENat P.height + Algebra.trdeg (A ⧸ p) (B ⧸ P)
      = (ofENat P.height + Algebra.trdeg (C ⧸ Q) (B ⧸ P)) + Algebra.trdeg (A ⧸ p) (C ⧸ Q) := by
        rw [← t₂]; ring
    _ ≤ (ofENat Q.height + Algebra.trdeg C B) + Algebra.trdeg (A ⧸ p) (C ⧸ Q) := by gcongr
    _ = (ofENat Q.height + Algebra.trdeg (A ⧸ p) (C ⧸ Q)) + Algebra.trdeg C B := by ring
    _ ≤ (ofENat p.height + Algebra.trdeg A C) + Algebra.trdeg C B := by gcongr
    _ = ofENat p.height + Algebra.trdeg A B := by rw [add_assoc, t₁]

/- English proof (translation)
Introduce `A B _ _ _ _ _ _ _ hinj P _`. It suffices to establish `key : ∀ (n : ℕ) (B : Type v) [CommRing B] [IsDomain B] [Algebra A B] (x : Fin n → B), Algebra.adjoin A (Set.range x) = ⊤ → Function.Injective (algebraMap A B) → ∀ (P : Ideal B) [P.IsPrime] (p : Ideal A) [p.IsPrime] [P.LiesOver p], ofENat P.height + Algebra.trdeg (A ⧸ p) (B ⧸ P) ≤ …`. Take `⟨s, hs⟩` from `Algebra.FiniteType.out (R := A) (A := B)`. Use `key s.card B (fun i ↦ (s.equivFin.symm i : B)) ?_ hinj P (P.under A)` and prove the remaining obligations. Rewrite using `[← hs]`.

Use `congr 1`. Use extensionality with `b`. Use `⟨?_, fun hb ↦ ⟨s.equivFin ⟨b, hb⟩, by simp⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨i, rfl⟩`. Conclude with `(s.equivFin.symm i).2`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `B _ _ _ x hx hinj P _ p _ _`. Take `rfl : p = P.under A` from `Ideal.LiesOver.over`.

Use `h₁ A B 0 ?_ hinj P` and prove the remaining obligations. Rewrite using `[eq_top_iff, ← hx]`. Conclude with `Algebra.adjoin_mono (by simp [Set.range_eq_empty])`. Consider the case `succ n ih`. Introduce `B _ _ _ x hx hinj P _ p _ _`.

Use `set C : Subalgebra A B := Algebra.adjoin A (Set.range (x ∘ Fin.succ)) with hC`. Set `y : Fin n → C` to `fun i ↦ ⟨x i.succ, Algebra.subset_adjoin ⟨i, rfl⟩⟩`. Establish `hy : Algebra.adjoin A (Set.range y) = ⊤`. Apply `Subalgebra.map_injective (f := C.val) Subtype.val_injective` to reduce the goal to its premises. Rewrite using `[AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val, ← Set.range_comp]`.

Both sides reduce to the same expression. Establish `hAC : Function.Injective (algebraMap A C)` using `fun a b hab ↦ hinj (congrArg Subtype.val hab :)`. Establish `hCB : Function.Injective (algebraMap C B)` using `Subtype.val_injective`. Establish `: Algebra.FiniteType A C` using `⟨⟨Finset.univ.image y, by simpa [Finset.coe_image] using hy⟩⟩`. Establish `: IsNoetherianRing C` using `Algebra.FiniteType.isNoetherianRing A C`.

Establish `hB : Algebra.adjoin C {x 0} = ⊤`. Apply `Subalgebra.restrictScalars_injective A` to reduce the goal to its premises. Rewrite using `[Subalgebra.restrictScalars_top, ← Algebra.adjoin_union_eq_adjoin_adjoin, eq_top_iff, ← hx]`. Apply `Algebra.adjoin_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨i, rfl⟩`.

Consider the cases of `i using Fin.cases with`. Consider the case `zero => exact Or.inr rfl`. Consider the case `succ j => exact Or.inl ⟨j, rfl⟩`. Establish `: (P.under C).LiesOver p` using `Ideal.LiesOver.tower_bot P (P.under C) p`. Conclude with `DimensionInequality.tower_step hAC hCB P (P.under C) p (ih C y hy hAC (P.under C) p) (h₂ C B (x 0) hB hCB P)`.
-/
theorem DimensionInequality.proof (h₁ : DimensionInequalityOneGenerator.Statement.{u, v})
    (h₂ : DimensionInequalityOneGenerator.Statement.{v, v}) :
    DimensionInequality.Statement.{u, v} := by
  classical
  intro A B _ _ _ _ _ _ _ hinj P _

  suffices key : ∀ (n : ℕ) (B : Type v) [CommRing B] [IsDomain B] [Algebra A B] (x : Fin n → B),
      Algebra.adjoin A (Set.range x) = ⊤ → Function.Injective (algebraMap A B) →
      ∀ (P : Ideal B) [P.IsPrime] (p : Ideal A) [p.IsPrime] [P.LiesOver p],
        ofENat P.height + Algebra.trdeg (A ⧸ p) (B ⧸ P) ≤ ofENat p.height + Algebra.trdeg A B by
    obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := A) (A := B)
    refine key s.card B (fun i ↦ (s.equivFin.symm i : B)) ?_ hinj P (P.under A)
    rw [← hs]
    congr 1
    ext b
    refine ⟨?_, fun hb ↦ ⟨s.equivFin ⟨b, hb⟩, by simp⟩⟩
    rintro ⟨i, rfl⟩
    exact (s.equivFin.symm i).2
  intro n
  induction n with
  | zero =>
    intro B _ _ _ x hx hinj P _ p _ _
    obtain rfl : p = P.under A := Ideal.LiesOver.over
    refine h₁ A B 0 ?_ hinj P
    rw [eq_top_iff, ← hx]
    exact Algebra.adjoin_mono (by simp [Set.range_eq_empty])
  | succ n ih =>
    intro B _ _ _ x hx hinj P _ p _ _
    set C : Subalgebra A B := Algebra.adjoin A (Set.range (x ∘ Fin.succ)) with hC
    let y : Fin n → C := fun i ↦ ⟨x i.succ, Algebra.subset_adjoin ⟨i, rfl⟩⟩
    have hy : Algebra.adjoin A (Set.range y) = ⊤ := by
      apply Subalgebra.map_injective (f := C.val) Subtype.val_injective
      rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val, ← Set.range_comp]
      rfl
    have hAC : Function.Injective (algebraMap A C) := fun a b hab ↦
      hinj (congrArg Subtype.val hab :)
    have hCB : Function.Injective (algebraMap C B) := Subtype.val_injective
    have : Algebra.FiniteType A C :=
      ⟨⟨Finset.univ.image y, by simpa [Finset.coe_image] using hy⟩⟩
    have : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing A C
    have hB : Algebra.adjoin C {x 0} = ⊤ := by
      apply Subalgebra.restrictScalars_injective A
      rw [Subalgebra.restrictScalars_top, ← Algebra.adjoin_union_eq_adjoin_adjoin, eq_top_iff, ← hx]
      apply Algebra.adjoin_mono
      rintro _ ⟨i, rfl⟩
      cases i using Fin.cases with
      | zero => exact Or.inr rfl
      | succ j => exact Or.inl ⟨j, rfl⟩
    have : (P.under C).LiesOver p := Ideal.LiesOver.tower_bot P (P.under C) p
    exact DimensionInequality.tower_step hAC hCB P (P.under C) p
      (ih C y hy hAC (P.under C) p) (h₂ C B (x 0) hB hCB P)

end GroundTheory.Heights₂.Heights.NumbersDVR
