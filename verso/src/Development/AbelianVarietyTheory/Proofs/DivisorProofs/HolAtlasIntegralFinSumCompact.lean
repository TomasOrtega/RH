import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSubOfIsFormStatement

set_option autoImplicit false

noncomputable section

open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder

namespace GlobalTheory.CxForm.IntegralSum

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

/- English proof (translation)
Unfold `HolAtlas.loc`. Use `split_ifs`. Conclude with `Finset.sum_apply _ _ _`. Conclude with `Finset.sum_const_zero.symm`.
-/
theorem loc_finset_sum {κ : Type} (s : Finset κ) (α : κ → A.Fld) (i : A.ι) (v : ReciprocityTheory.L2DbarEstimates.V n) :
    A.loc (∑ j ∈ s, α j) i v = ∑ j ∈ s, A.loc (α j) i v := by
  unfold HolAtlas.loc
  split_ifs
  · exact Finset.sum_apply _ _ _
  · exact Finset.sum_const_zero.symm

/- English proof (translation)
Use `⟨fun i S => ?_, fun x x' e => ?_⟩` and prove the remaining obligations. Simplify using `only [loc_finset_sum, map_sum, Finsupp.finsetSum_apply]`. Conclude with `ContDiffOn.sum fun j hj => (h j hj).smooth i S`. Rewrite using `[Finset.sum_apply, Finset.sum_apply, map_sum]`. Conclude with `Finset.sum_congr rfl fun j hj => (h j hj).compat x x' e`.
-/
theorem isForm_finset_sum {κ : Type} (s : Finset κ) (α : κ → A.Fld) (h : ∀ j ∈ s, A.IsForm (α j)) :
    A.IsForm (∑ j ∈ s, α j) := by
  refine ⟨fun i S => ?_, fun x x' e => ?_⟩
  · simp only [loc_finset_sum, map_sum, Finsupp.finsetSum_apply]
    exact ContDiffOn.sum fun j hj => (h j hj).smooth i S
  · rw [Finset.sum_apply, Finset.sum_apply, map_sum]
    exact Finset.sum_congr rfl fun j hj => (h j hj).compat x x' e

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Establish `h0` using `isForm_finset_sum A ∅ α h`. Use `GlobalTheory.T.integral_sub_of_isForm' A _ _ h0 h0` as an intermediate fact. Rewrite `this` using `[sub_self, sub_self]`.

Simplify using `using this`. Consider the case `insert a s ha ih`. Use `GlobalTheory.T.integral_sub_of_isForm' A _ _ (isForm_finset_sum A _ α h) (h a (Finset.mem_insert_self a s))` as an intermediate fact. Rewrite `this` using `[Finset.sum_insert ha, add_sub_cancel_left, ih fun j hj => h j (Finset.mem_insert_of_mem hj)]`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem integral_finset_sum [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
    {κ : Type} (s : Finset κ) (α : κ → A.Fld) (h : ∀ j ∈ s, A.IsForm (α j)) :
    A.integral (∑ j ∈ s, α j) = ∑ j ∈ s, A.integral (α j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 := isForm_finset_sum A ∅ α h
    have := GlobalTheory.T.integral_sub_of_isForm' A _ _ h0 h0
    rw [sub_self, sub_self] at this
    simpa using this
  | insert a s ha ih =>
    have := GlobalTheory.T.integral_sub_of_isForm' A _ _ (isForm_finset_sum A _ α h) (h a (Finset.mem_insert_self a s))
    rw [Finset.sum_insert ha, add_sub_cancel_left, ih fun j hj => h j (Finset.mem_insert_of_mem hj)] at this
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    linarith

set_option autoImplicit false in
open Set Matrix MeasureTheory in
open scoped ComplexOrder in
variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : _root_.GlobalTheory.CxForm.HolAtlas M n) in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `i S`. Unfold `_root_.GlobalTheory.CxForm.HolAtlas.loc`. Use `(contDiffOn_const (c := (0 : ℂ))).congr ?_` and prove the remaining obligations. Introduce `v _`.

Use `split_ifs`. Use `erw [Pi.zero_apply, map_zero, Finsupp.zero_apply]`. Introduce `x x' _`. Conclude with `(map_zero _).symm`.
-/
private theorem isForm_zero' : A.IsForm 0 := by
  constructor
  · intro i S
    unfold _root_.GlobalTheory.CxForm.HolAtlas.loc
    refine (contDiffOn_const (c := (0 : ℂ))).congr ?_
    intro v _
    split_ifs
    erw [Pi.zero_apply, map_zero, Finsupp.zero_apply]
  · intro x x' _
    exact (map_zero _).symm

set_option autoImplicit false in
open Set Matrix MeasureTheory in
open scoped ComplexOrder in
variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : _root_.GlobalTheory.CxForm.HolAtlas M n) in
variable [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] in
/- English proof (translation)
Establish `h` using `A.integral_sub_of_isForm 0 0 (isForm_zero' A) (isForm_zero' A)`. Simplify using `using h`.
-/
private theorem integral_zero_fld : A.integral 0 = 0 := by
  have h := A.integral_sub_of_isForm 0 0 (isForm_zero' A) (isForm_zero' A)
  simpa using h

set_option autoImplicit false in
open Set Matrix MeasureTheory in
open scoped ComplexOrder in
variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : _root_.GlobalTheory.CxForm.HolAtlas M n) in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `i S`. Establish `h1` using `ha.smooth i S`. Establish `h2` using `hb.smooth i S`. Unfold `_root_.GlobalTheory.CxForm.HolAtlas.loc`.

Unfold `_root_.GlobalTheory.CxForm.HolAtlas.loc at h1 h2`. Use `(h1.add h2).congr ?_` and prove the remaining obligations. Introduce `v hv`. Simplify using `only [dif_pos hv]`. Use `erw [Pi.add_apply, map_add, Finsupp.add_apply]`.

Introduce `x x' hx`. Simplify using `[ha.compat x x' hx, hb.compat x x' hx]`.
-/
private theorem isForm_add' {α β : A.Fld}
    (ha : A.IsForm α) (hb : A.IsForm β) :
    A.IsForm (α + β) := by
  constructor
  · intro i S
    have h1 := ha.smooth i S
    have h2 := hb.smooth i S
    unfold _root_.GlobalTheory.CxForm.HolAtlas.loc
    unfold _root_.GlobalTheory.CxForm.HolAtlas.loc at h1 h2
    refine (h1.add h2).congr ?_
    intro v hv
    simp only [dif_pos hv]
    erw [Pi.add_apply, map_add, Finsupp.add_apply]
  · intro x x' hx
    simp [ha.compat x x' hx, hb.compat x x' hx]

set_option autoImplicit false in
open Set Matrix MeasureTheory in
open scoped ComplexOrder in
variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : _root_.GlobalTheory.CxForm.HolAtlas M n) in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `i S`. Establish `h1` using `ha.smooth i S`. Establish `h2` using `hb.smooth i S`. Unfold `_root_.GlobalTheory.CxForm.HolAtlas.loc`.

Unfold `_root_.GlobalTheory.CxForm.HolAtlas.loc at h1 h2`. Use `(h1.sub h2).congr ?_` and prove the remaining obligations. Introduce `v hv`. Simplify using `only [dif_pos hv]`. Use `erw [Pi.sub_apply, map_sub, Finsupp.sub_apply]`.

Introduce `x x' hx`. Simplify using `[ha.compat x x' hx, hb.compat x x' hx]`.
-/
private theorem isForm_sub' {α β : A.Fld}
    (ha : A.IsForm α) (hb : A.IsForm β) :
    A.IsForm (α - β) := by
  constructor
  · intro i S
    have h1 := ha.smooth i S
    have h2 := hb.smooth i S
    unfold _root_.GlobalTheory.CxForm.HolAtlas.loc
    unfold _root_.GlobalTheory.CxForm.HolAtlas.loc at h1 h2
    refine (h1.sub h2).congr ?_
    intro v hv
    simp only [dif_pos hv]
    erw [Pi.sub_apply, map_sub, Finsupp.sub_apply]
  · intro x x' hx
    simp [ha.compat x x' hx, hb.compat x x' hx]

set_option autoImplicit false in
open Set Matrix MeasureTheory in
open scoped ComplexOrder in
variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : _root_.GlobalTheory.CxForm.HolAtlas M n) in
variable [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] in
/- English proof (translation)
Establish `hnb : A.IsForm (0 - β)` using `isForm_sub' A (isForm_zero' A) hb`. Establish `h` using `A.integral_sub_of_isForm α (0 - β) ha hnb`. Establish `h0` using `A.integral_sub_of_isForm 0 β (isForm_zero' A) hb`. Rewrite `h0` using `[integral_zero_fld A]`. Rewrite `h` using `[show α - (0 - β) = α + β by abel]`.

Rewrite using `[h, h0]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem integral_add_of_isForm {α β : A.Fld}
    (ha : A.IsForm α) (hb : A.IsForm β) :
    A.integral (α + β) =
      A.integral α + A.integral β := by
  have hnb : A.IsForm (0 - β) :=
    isForm_sub' A (isForm_zero' A) hb
  have h := A.integral_sub_of_isForm α (0 - β) ha hnb
  have h0 := A.integral_sub_of_isForm 0 β (isForm_zero' A) hb
  rw [integral_zero_fld A] at h0
  rw [show α - (0 - β) = α + β by abel] at h
  rw [h, h0]
  ring

set_option autoImplicit false in
open Set Matrix MeasureTheory in
open scoped ComplexOrder in
variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : _root_.GlobalTheory.CxForm.HolAtlas M n) in
variable [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] in
/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using ⟨isForm_zero' A, integral_zero_fld A⟩`. Consider the case `insert a s ha ih`. Establish `hs` using `ih (fun j hj => hα j (Finset.mem_insert_of_mem hj))`. Establish `hA` using `hα a (Finset.mem_insert_self a s)`.

Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha]`. Use `⟨isForm_add' A hA hs.1, ?_⟩` and prove the remaining obligations. Rewrite using `[integral_add_of_isForm A hA hs.1, hs.2]`.
-/
private theorem isForm_and_integral_finset_sum {ι : Type} (s : Finset ι)
    (α : ι → A.Fld) (hα : ∀ j ∈ s, A.IsForm (α j)) :
    A.IsForm (∑ j ∈ s, α j) ∧
      A.integral (∑ j ∈ s, α j) = ∑ j ∈ s, A.integral (α j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ⟨isForm_zero' A, integral_zero_fld A⟩
  | insert a s ha ih =>
    have hs := ih (fun j hj => hα j (Finset.mem_insert_of_mem hj))
    have hA := hα a (Finset.mem_insert_self a s)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨isForm_add' A hA hs.1, ?_⟩
    rw [integral_add_of_isForm A hA hs.1, hs.2]

set_option autoImplicit false in

/- English proof (translation)
Introduce `M _ _ _ _ _ _ n A N α hα`. Conclude with `(isForm_and_integral_finset_sum A Finset.univ α (fun j _ => hα j)).2`.
-/
theorem _root_.GlobalTheory.CxForm.IntegralSum.integral_sum : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M]
    [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ}
    (A : _root_.GlobalTheory.CxForm.HolAtlas M n) {N : ℕ} (α : Fin N → A.Fld),
    (∀ j, A.IsForm (α j)) →
      A.integral (∑ j, α j) = ∑ j, A.integral (α j) := by
  intro M _ _ _ _ _ _ n A N α hα
  exact (isForm_and_integral_finset_sum A Finset.univ α (fun j _ => hα j)).2

end GlobalTheory.CxForm.IntegralSum
