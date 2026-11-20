import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.TensorIrr
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Algebraic.LinearIndependent
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Cardinality
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SpectrumNonemptyOfCountableRank

noncomputable section

namespace PositivityTheory.KReal

/- English proof (translation)
Set `S : Subalgebra ℂ D` to `Subalgebra.centralizer ℂ (Subalgebra.centralizer ℂ {x} : Set D)`. Establish `hS : ∀ a : D, a ∈ S ↔ ∀ g : D, x * g = g * x → g * a = a * g`. Introduce `a`. Simplify using `only [S, Subalgebra.mem_centralizer_iff, SetLike.mem_coe, Set.mem_singleton_iff, forall_eq]`. Establish `hx : x ∈ S` using `(hS x).2 fun g hg => hg.symm`.

Establish `hF : IsField S` using `{ exists_pair_ne := ⟨0, 1, zero_ne_one⟩ mul_comm := fun a b => Subtype.ext ((hS b).1 b.2 a ((hS a).1 a.2 x rfl)) mul_inv_cancel := fun {a} ha => by`. Establish `ha' : (a : D) ≠ 0` using `fun h0 => ha (Subtype.ext h0)`. Use `⟨⟨(a : D)⁻¹, (hS _).2 fun g hg => ?_⟩, Subtype.ext (mul_inv_cancel₀ ha')⟩` and prove the remaining obligations. Conclude with `(Commute.inv_right₀ ((hS a).1 a.2 g hg : Commute g a)).eq }`. Use `letI : Field S := hF.toField`.

Establish `hx' : IsAlgebraic ℂ (⟨x, hx⟩ : S)`. Assume the negation of the conclusion as `ht`. Establish `h1` using `(Transcendental.linearIndependent_sub_inv (F := ℂ) (E := S) ht).cardinal_le_rank`. Establish `h2 : Module.rank ℂ S ≤ Module.rank ℂ D` using `LinearMap.rank_le_of_injective S.val.toLinearMap Subtype.val_injective`. Rewrite `h1` using `[Cardinal.mk_complex]`.

Conclude with `absurd (h1.trans (h2.trans h)) (not_le.2 Cardinal.aleph0_lt_continuum)`. Conclude with `hx'.algHom S.val`.
-/
theorem isAlgebraic_of_rank_le {D : Type} [DivisionRing D] [Algebra ℂ D]
    (h : Module.rank ℂ D ≤ Cardinal.aleph0) (x : D) : IsAlgebraic ℂ x := by
  let S : Subalgebra ℂ D := Subalgebra.centralizer ℂ (Subalgebra.centralizer ℂ {x} : Set D)
  have hS : ∀ a : D, a ∈ S ↔ ∀ g : D, x * g = g * x → g * a = a * g := by
    intro a
    simp only [S, Subalgebra.mem_centralizer_iff, SetLike.mem_coe, Set.mem_singleton_iff, forall_eq]
  have hx : x ∈ S := (hS x).2 fun g hg => hg.symm
  have hF : IsField S :=
    { exists_pair_ne := ⟨0, 1, zero_ne_one⟩
      mul_comm := fun a b => Subtype.ext ((hS b).1 b.2 a ((hS a).1 a.2 x rfl))
      mul_inv_cancel := fun {a} ha => by
        have ha' : (a : D) ≠ 0 := fun h0 => ha (Subtype.ext h0)
        refine ⟨⟨(a : D)⁻¹, (hS _).2 fun g hg => ?_⟩, Subtype.ext (mul_inv_cancel₀ ha')⟩
        exact (Commute.inv_right₀ ((hS a).1 a.2 g hg : Commute g a)).eq }
  letI : Field S := hF.toField
  have hx' : IsAlgebraic ℂ (⟨x, hx⟩ : S) := by
    by_contra ht
    have h1 := (Transcendental.linearIndependent_sub_inv (F := ℂ) (E := S) ht).cardinal_le_rank
    have h2 : Module.rank ℂ S ≤ Module.rank ℂ D :=
      LinearMap.rank_le_of_injective S.val.toLinearMap Subtype.val_injective
    rw [Cardinal.mk_complex] at h1
    exact absurd (h1.trans (h2.trans h)) (not_le.2 Cardinal.aleph0_lt_continuum)
  exact hx'.algHom S.val

/- English proof (translation)
Establish `: Nontrivial V` using `IsSimpleModule.nontrivial B V`. Take `⟨v, hv⟩` from `exists_ne (0 : V)`. Set `ev : Module.End B V →ₗ[ℂ] V` to `{ toFun := fun T => T v map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Establish `hev : Function.Injective ev`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `T hT`. Assume the negation of the conclusion as `h0`. Conclude with `hv ((LinearMap.injective_of_ne_zero h0) (by rw [map_zero]; exact hT))`. Establish `hr : Module.rank ℂ (Module.End B V) ≤ Cardinal.aleph0` using `(LinearMap.rank_le_of_injective ev hev).trans h`. Establish `: Algebra.IsAlgebraic ℂ (Module.End B V)` using `⟨isAlgebraic_of_rank_le hr⟩`.

Establish `: Algebra.IsIntegral ℂ (Module.End B V)` using `Algebra.IsAlgebraic.isIntegral`. Conclude with `(IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ)).2`.
-/
theorem schur_countable {B V : Type} [Ring B] [Algebra ℂ B] [AddCommGroup V] [Module ℂ V] [Module B V]
    [IsScalarTower ℂ B V] [IsSimpleModule B V] (h : Module.rank ℂ V ≤ Cardinal.aleph0) :
    Function.Surjective (algebraMap ℂ (Module.End B V)) := by
  classical
  have : Nontrivial V := IsSimpleModule.nontrivial B V
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let ev : Module.End B V →ₗ[ℂ] V :=
    { toFun := fun T => T v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : Function.Injective ev := by
    rw [injective_iff_map_eq_zero]
    intro T hT
    by_contra h0
    exact hv ((LinearMap.injective_of_ne_zero h0) (by rw [map_zero]; exact hT))
  have hr : Module.rank ℂ (Module.End B V) ≤ Cardinal.aleph0 :=
    (LinearMap.rank_le_of_injective ev hev).trans h
  have : Algebra.IsAlgebraic ℂ (Module.End B V) := ⟨isAlgebraic_of_rank_le hr⟩
  have : Algebra.IsIntegral ℂ (Module.End B V) := Algebra.IsAlgebraic.isIntegral
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ)).2

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.DYhd6.main h B hB f s`.
-/
theorem dense_countable {V : Type} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (h : Module.rank ℂ V ≤ Cardinal.aleph0) (B : Subalgebra ℂ (Module.End ℂ V))
    (hB : ∀ N : Submodule ℂ V, (∀ b ∈ B, ∀ x ∈ N, b x ∈ N) → N = ⊥ ∨ N = ⊤)
    (f : Module.End ℂ V) (s : Finset V) : ∃ b ∈ B, ∀ m ∈ s, f m = b m :=
  _root_.UpperTheory.Reformulated.B.DYhd6.main h B hB f s

section

variable {ι : Type} [DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]

def one_op (i : ι) (f : Module.End ℂ (M i)) : Module.End ℂ (PiTensorProduct ℂ M) :=
  PiTensorProduct.map (Function.update (fun j => (LinearMap.id : M j →ₗ[ℂ] M j)) i f)

/- English proof (translation)
Rewrite using `[one_op, PiTensorProduct.map_tprod]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Function.update_of_ne hj]`.
-/
theorem one_op_tprod (i : ι) (f : Module.End ℂ (M i)) (x : ∀ j, M j) :
    one_op i f (PiTensorProduct.tprod ℂ x) = PiTensorProduct.tprod ℂ (Function.update x i (f (x i))) := by
  rw [one_op, PiTensorProduct.map_tprod]
  congr 1
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj]

/- English proof (translation)
Use extensionality with `x`. Simplify using `[one_op_tprod]`.
-/
theorem one_op_mul (i : ι) (f g : Module.End ℂ (M i)) : one_op i (f * g) = one_op i f * one_op i g := by
  ext x
  simp [one_op_tprod]

/- English proof (translation)
Use extensionality with `x`. Simplify using `[one_op_tprod]`.
-/
theorem one_op_add (i : ι) (f g : Module.End ℂ (M i)) : one_op i (f + g) = one_op i f + one_op i g := by
  ext x
  simp [one_op_tprod]

/- English proof (translation)
Use extensionality with `x`. Simplify using `[one_op_tprod]`.
-/
theorem one_op_alg (i : ι) (c : ℂ) : one_op i (algebraMap ℂ (Module.End ℂ (M i)) c) = algebraMap ℂ _ c := by
  ext x
  simp [one_op_tprod]

/- English proof (translation)
Proceed by induction on `x using PiTensorProduct.induction_on with`. Consider the case `smul_tprod r y`. Use `⟨{y i}, fun f g h => ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, map_smul, one_op_tprod, one_op_tprod, h _ (Finset.mem_singleton_self _)]`. Consider the case `add y z hy hz`.

Take `⟨s, hs⟩` from `hy`. Take `⟨t, ht⟩` from `hz`. Use `⟨s ∪ t, fun f g h => ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_add, hs f g fun m hm => h m (Finset.mem_union_left _ hm), ht f g fun m hm => h m (Finset.mem_union_right _ hm)]`.
-/
theorem one_op_fin (i : ι) (x : PiTensorProduct ℂ M) :
    ∃ s : Finset (M i), ∀ f g : Module.End ℂ (M i), (∀ m ∈ s, f m = g m) → one_op i f x = one_op i g x := by
  classical
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r y =>
    refine ⟨{y i}, fun f g h => ?_⟩
    rw [map_smul, map_smul, one_op_tprod, one_op_tprod, h _ (Finset.mem_singleton_self _)]
  | add y z hy hz =>
    obtain ⟨s, hs⟩ := hy
    obtain ⟨t, ht⟩ := hz
    refine ⟨s ∪ t, fun f g h => ?_⟩
    rw [map_add, map_add, hs f g fun m hm => h m (Finset.mem_union_left _ hm),
      ht f g fun m hm => h m (Finset.mem_union_right _ hm)]

/- English proof (translation)
Establish `key : ∀ s : Finset ι, PiTensorProduct.map (fun j => if j ∈ s then f j else (LinearMap.id : M j →ₗ[ℂ] M j)) x ∈ N`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using hx`. Consider the case `insert i s hi ih`.

Establish `e : PiTensorProduct.map (fun j => if j ∈ insert i s then f j else (LinearMap.id : M j →ₗ[ℂ] M j)) = one_op i (f i) ∘ₗ PiTensorProduct.map (fun j => if j ∈ s then f j else (LinearMap.id : M j →ₗ[ℂ] M j))`. Rewrite using `[one_op, ← PiTensorProduct.map_comp]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = i`.

Substitute `hj` using the available equality. Simplify using `[hi]`. Simplify using `[hj, Function.update_of_ne hj]`. Rewrite using `[e]`. Conclude with `hN i (f i) _ ih`.

Simplify using `using key Finset.univ`.
-/
theorem map_mem_of_one_op [Fintype ι] (N : Submodule ℂ (PiTensorProduct ℂ M))
    (hN : ∀ i (f : Module.End ℂ (M i)), ∀ x ∈ N, one_op i f x ∈ N)
    (f : ∀ i, Module.End ℂ (M i)) (x : PiTensorProduct ℂ M) (hx : x ∈ N) : PiTensorProduct.map f x ∈ N := by
  have key : ∀ s : Finset ι,
      PiTensorProduct.map (fun j => if j ∈ s then f j else (LinearMap.id : M j →ₗ[ℂ] M j)) x ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hx
    | insert i s hi ih =>
      have e : PiTensorProduct.map (fun j => if j ∈ insert i s then f j else (LinearMap.id : M j →ₗ[ℂ] M j)) =
          one_op i (f i) ∘ₗ
            PiTensorProduct.map (fun j => if j ∈ s then f j else (LinearMap.id : M j →ₗ[ℂ] M j)) := by
        rw [one_op, ← PiTensorProduct.map_comp]
        congr 1
        funext j
        by_cases hj : j = i
        · subst hj; simp [hi]
        · simp [hj, Function.update_of_ne hj]
      rw [e]
      exact hN i (f i) _ ih
  simpa using key Finset.univ

end

/- English proof (translation)
Introduce `ι _ _ A M _ _ act hr hnt hirr N hN`. Establish `hall : ∀ i (f : Module.End ℂ (M i)), ∀ x ∈ N, one_op i f x ∈ N`. Introduce `i f x hx`. Set `B : Subalgebra ℂ (Module.End ℂ (M i))` to `{ carrier := {b | ∀ y ∈ N, one_op i b y ∈ N} mul_mem' := fun {a b} ha hb y hy => by`. Rewrite using `[one_op_mul]`.

Conclude with `ha _ (hb y hy)`. Use the proof step `add_mem' := fun {a b} ha hb y hy => by`. Rewrite using `[one_op_add]`. Conclude with `N.add_mem (ha y hy) (hb y hy)`. Use the proof step `algebraMap_mem' := fun c y hy => by`.

Rewrite using `[one_op_alg]`. Conclude with `N.smul_mem c hy }`. Take `⟨s, hs⟩` from `one_op_fin i x`. Use `hnt i` as an intermediate fact. Take `⟨b, hb, hfb⟩` from `dense_countable (hr i) B (fun P hP => hirr i P fun a y hy => hP (act i a) (hN i a) y hy) f s`.

Rewrite using `[hs f b hfb]`. Conclude with `hb x hx`. Rewrite using `[or_iff_not_imp_left]`. Introduce `h0`. Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot h0`.

Set `b` to `fun i => Module.Basis.ofVectorSpace ℂ (M i)`. Choose the witnesses or unpack the hypotheses as in `⟨p, hp⟩ : ∃ p, (Basis.piTensorProduct b).repr x p ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `hx0 ((Basis.piTensorProduct b).repr.map_eq_zero_iff.1 (Finsupp.ext hc))`.

Rewrite using `[eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]`. Introduce and unpack `_ ⟨v, rfl⟩`. Establish `e : PiTensorProduct.map (fun i => ((b i).coord (p i)).smulRight (v i)) = ((Basis.piTensorProduct b).coord p).smulRight (PiTensorProduct.tprod ℂ v)`. Use extensionality with `y`. Simplify using `[Basis.piTensorProduct_repr_tprod_apply, MultilinearMap.map_smul_univ]`.

Establish `h1` using `map_mem_of_one_op N hall (fun i => ((b i).coord (p i)).smulRight (v i)) x hx`. Rewrite `h1` using `[e, LinearMap.smulRight_apply]`. Conclude with `(N.smul_mem_iff hp).1 h1`.
-/
theorem tensorIrr : TensorIrr := by
  intro ι _ _ A M _ _ act hr hnt hirr N hN
  have hall : ∀ i (f : Module.End ℂ (M i)), ∀ x ∈ N, one_op i f x ∈ N := by
    intro i f x hx
    let B : Subalgebra ℂ (Module.End ℂ (M i)) :=
      { carrier := {b | ∀ y ∈ N, one_op i b y ∈ N}
        mul_mem' := fun {a b} ha hb y hy => by
          rw [one_op_mul]; exact ha _ (hb y hy)
        add_mem' := fun {a b} ha hb y hy => by
          rw [one_op_add]; exact N.add_mem (ha y hy) (hb y hy)
        algebraMap_mem' := fun c y hy => by
          rw [one_op_alg]; exact N.smul_mem c hy }
    obtain ⟨s, hs⟩ := one_op_fin i x
    have := hnt i
    obtain ⟨b, hb, hfb⟩ := dense_countable (hr i) B
      (fun P hP => hirr i P fun a y hy => hP (act i a) (hN i a) y hy) f s
    rw [hs f b hfb]
    exact hb x hx
  rw [or_iff_not_imp_left]
  intro h0
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  let b := fun i => Module.Basis.ofVectorSpace ℂ (M i)
  obtain ⟨p, hp⟩ : ∃ p, (Basis.piTensorProduct b).repr x p ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hx0 ((Basis.piTensorProduct b).repr.map_eq_zero_iff.1 (Finsupp.ext hc))
  rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  have e : PiTensorProduct.map (fun i => ((b i).coord (p i)).smulRight (v i)) =
      ((Basis.piTensorProduct b).coord p).smulRight (PiTensorProduct.tprod ℂ v) := by
    ext y
    simp [Basis.piTensorProduct_repr_tprod_apply, MultilinearMap.map_smul_univ]
  have h1 := map_mem_of_one_op N hall (fun i => ((b i).coord (p i)).smulRight (v i)) x hx
  rw [e, LinearMap.smulRight_apply] at h1
  exact (N.smul_mem_iff hp).1 h1

end PositivityTheory.KReal

end
