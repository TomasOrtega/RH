import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SubClosed
open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.SeqCx.BdBd

/- English proof (translation)
Simplify using `[bd, Finsupp.linearCombination_single]`.
-/
theorem bd_single (V : Type) (l : List V) (r : ℤ) :
    bd V (Finsupp.single l r) =
      r • ∑ i ∈ Finset.range l.length, (-1 : ℤ) ^ i • Finsupp.single (l.eraseIdx i) (1 : ℤ) := by
  simp [bd, Finsupp.linearCombination_single]

noncomputable def consMap (V : Type) (x : V) : (List V →₀ ℤ) →ₗ[ℤ] (List V →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (fun l : List V => x :: l)

/- English proof (translation)
Rewrite using `[bd_single, bd_single, one_smul, one_smul, List.length_cons, Finset.sum_range_succ']`. Simplify using `only [consMap, map_sum, map_zsmul, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, pow_zero, one_smul, pow_succ, mul_neg_one, neg_smul, Finset.sum_neg_distrib]`. Normalize the expressions using the abelian group laws.
-/
theorem bd_single_cons (V : Type) (x : V) (l : List V) :
    bd V (Finsupp.single (x :: l) 1) =
      Finsupp.single l 1 - consMap V x (bd V (Finsupp.single l 1)) := by
  rw [bd_single, bd_single, one_smul, one_smul, List.length_cons, Finset.sum_range_succ']
  simp only [consMap, map_sum, map_zsmul, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, pow_zero, one_smul, pow_succ, mul_neg_one,
    neg_smul, Finset.sum_neg_distrib]
  abel

/- English proof (translation)
Apply `Finsupp.lhom_ext` to reduce the goal to its premises. Introduce `l r`. Establish `h : Finsupp.single l r = r • Finsupp.single l (1 : ℤ)`. Rewrite using `[Finsupp.smul_single, smul_eq_mul, mul_one]`. Simplify using `only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply]`.

Rewrite using `[h]`. Simplify using `only [map_zsmul]`. Rewrite using `[show consMap V x (Finsupp.single l 1) = Finsupp.single (x :: l) 1 by`. Simplify using `[consMap, Finsupp.mapDomain_single], bd_single_cons, smul_sub]`.
-/
theorem bd_consMap (V : Type) (x : V) :
    bd V ∘ₗ consMap V x = LinearMap.id - consMap V x ∘ₗ bd V := by
  apply Finsupp.lhom_ext
  intro l r
  have h : Finsupp.single l r = r • Finsupp.single l (1 : ℤ) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply]
  rw [h]
  simp only [map_zsmul]
  rw [show consMap V x (Finsupp.single l 1) = Finsupp.single (x :: l) 1 by
    simp [consMap, Finsupp.mapDomain_single], bd_single_cons, smul_sub]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp [bd_single]`. Consider the case `cons x l ih`. Rewrite using `[bd_single_cons, map_sub]`. Use `congrArg (fun f => f (bd V (Finsupp.single l 1))) (bd_consMap V x)` as an intermediate fact.

Simplify using `only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply] at this`. Rewrite using `[this, ih, map_zero]`. Normalize the expressions using the abelian group laws.
-/
theorem bd_bd_single (V : Type) (l : List V) : bd V (bd V (Finsupp.single l 1)) = 0 := by
  induction l with
  | nil => simp [bd_single]
  | cons x l ih =>
    rw [bd_single_cons, map_sub]
    have := congrArg (fun f => f (bd V (Finsupp.single l 1))) (bd_consMap V x)
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply] at this
    rw [this, ih, map_zero]
    abel

end GlobalTheory.SeqCx.BdBd

namespace GlobalTheory.SeqCx

/- English proof (translation)
Introduce `V c`. Establish `h : bd V ∘ₗ bd V = 0`. Apply `Finsupp.lhom_ext` to reduce the goal to its premises. Introduce `l r`. Establish `e : Finsupp.single l r = r • Finsupp.single l (1 : ℤ)`.

Rewrite using `[Finsupp.smul_single, smul_eq_mul, mul_one]`. Simplify using `only [LinearMap.comp_apply, LinearMap.zero_apply]`. Rewrite using `[e, map_zsmul, map_zsmul, GlobalTheory.SeqCx.BdBd.bd_bd_single, smul_zero]`. Conclude with `congrArg (fun f => f c) h`.
-/
theorem bd_bd : ∀ (V : Type) (c : List V →₀ ℤ), bd V (bd V c) = 0 := by
  intro V c
  have h : bd V ∘ₗ bd V = 0 := by
    apply Finsupp.lhom_ext
    intro l r
    have e : Finsupp.single l r = r • Finsupp.single l (1 : ℤ) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    rw [e, map_zsmul, map_zsmul, GlobalTheory.SeqCx.BdBd.bd_bd_single, smul_zero]
  exact congrArg (fun f => f c) h

end GlobalTheory.SeqCx

section
open GlobalTheory.SeqCx Matrix
/- English proof (translation)
Use `first`. Consider the case `exact @GlobalTheory.SeqCx.bd_bd`. Consider the case `exact @GlobalTheory.SeqCx.BdBd.bd_bd_single`. Consider the case `exact @GlobalTheory.SeqCx.BdBd.bd_consMap`. Consider the case `exact @GlobalTheory.SeqCx.BdBd.bd_single_cons`.

Consider the case `exact @GlobalTheory.SeqCx.BdBd.bd_single`.
-/
theorem _root_.GlobalTheory.T.seqChain_boundary_comp_boundary_apply : ∀ (V : Type) (c : List V →₀ ℤ), bd V (bd V c) = 0 := by
  first
  | exact @GlobalTheory.SeqCx.bd_bd
  | exact @GlobalTheory.SeqCx.BdBd.bd_bd_single
  | exact @GlobalTheory.SeqCx.BdBd.bd_consMap
  | exact @GlobalTheory.SeqCx.BdBd.bd_single_cons
  | exact @GlobalTheory.SeqCx.BdBd.bd_single
end
