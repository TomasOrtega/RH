import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

/- English proof (translation)
Introduce `A _ _ ι κ a b S haa hab hbb haS hbS`. Establish `hcomm : ∀ x ∈ Set.range a ∪ Set.range b, ∀ y ∈ Set.range a ∪ Set.range b, x * y = y * x`. Introduce and unpack `x (⟨i, rfl⟩ | ⟨k, rfl⟩) y (⟨j, rfl⟩ | ⟨l, rfl⟩)`. Conclude with `(haa i j).eq`. Conclude with `(hab i l).eq`.

Conclude with `(hab j k).symm.eq`. Conclude with `(hbb k l).eq`. Establish `hle : Algebra.adjoin ℂ (Set.range a ∪ Set.range b) ≤ S`. Apply `Algebra.adjoin_le` to reduce the goal to its premises. Introduce and unpack `x (⟨i, rfl⟩ | ⟨k, rfl⟩)`.

Conclude with `haS i`. Conclude with `hbS k`. Establish `hmc : ∀ x y : Algebra.adjoin ℂ (Set.range a ∪ Set.range b), x * y = y * x`. Introduce `x y`. Apply `Subtype.ext` to reduce the goal to its premises.

Establish `h1 : ∀ z ∈ Set.range a ∪ Set.range b, Commute z (y : A)` using `fun z hz => Algebra.commute_of_mem_adjoin_of_forall_mem_commute y.2 (fun w hw => hcomm z hz w hw)`. Conclude with `(Algebra.commute_of_mem_adjoin_of_forall_mem_commute x.2 (fun w hw => (h1 w hw).symm)).symm.eq`. Use `letI : CommRing (Algebra.adjoin ℂ (Set.range a ∪ Set.range b)) := { (inferInstance : Ring (Algebra.adjoin ℂ (Set.range a ∪ Set.range b))) with mul_comm := hmc }`. Set `a' : ι → Algebra.adjoin ℂ (Set.range a ∪ Set.range b)` to `fun i => ⟨a i, Algebra.subset_adjoin (Or.inl ⟨i, rfl⟩)⟩`. Set `b' : κ → Algebra.adjoin ℂ (Set.range a ∪ Set.range b)` to `fun k => ⟨b k, Algebra.subset_adjoin (Or.inr ⟨k, rfl⟩)⟩`.

Set `e : MvPolynomial κ (MvPolynomial ι ℂ) →+* Algebra.adjoin ℂ (Set.range a ∪ Set.range b)` to `eval₂Hom (eval₂Hom (algebraMap ℂ _) a') b'`. Use `⟨(Algebra.adjoin ℂ (Set.range a ∪ Set.range b)).val.toRingHom.comp e, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `c show ((e (C (C c)) : Algebra.adjoin ℂ (Set.range a ∪ Set.range b)) : A) = _`. Simplify using `only [e, eval₂Hom_C]`. Rewrite using `[Algebra.algebraMap_eq_smul_one]`.

Both sides reduce to the same expression. Introduce `i show ((e (C (X i)) : Algebra.adjoin ℂ (Set.range a ∪ Set.range b)) : A) = _`. Simplify using `only [e, eval₂Hom_C, eval₂Hom_X']`. Both sides reduce to the same expression. Introduce `k show ((e (X k) : Algebra.adjoin ℂ (Set.range a ∪ Set.range b)) : A) = _`.

Simplify using `only [e, eval₂Hom_X']`. Both sides reduce to the same expression. Introduce `P`. Conclude with `hle (e P).2`.
-/
theorem UpperTheory.ConvolutionTheory.Tf.evOf :
    ∀ (A : Type) [Ring A] [Algebra ℂ A] (ι κ : Type) (a : ι → A) (b : κ → A) (S : Subalgebra ℂ A),
      (∀ i j, Commute (a i) (a j)) → (∀ i k, Commute (a i) (b k)) → (∀ k l, Commute (b k) (b l)) → (∀ i, a i ∈ S) → (∀ k, b k ∈ S) →
      ∃ ev : MvPolynomial κ (MvPolynomial ι ℂ) →+* A, (∀ c : ℂ, ev (C (C c)) = c • 1) ∧ (∀ i, ev (C (X i)) = a i) ∧
        (∀ k, ev (X k) = b k) ∧ ∀ P, ev P ∈ S := by
  intro A _ _ ι κ a b S haa hab hbb haS hbS
  have hcomm : ∀ x ∈ Set.range a ∪ Set.range b, ∀ y ∈ Set.range a ∪ Set.range b,
      x * y = y * x := by
    rintro x (⟨i, rfl⟩ | ⟨k, rfl⟩) y (⟨j, rfl⟩ | ⟨l, rfl⟩)
    · exact (haa i j).eq
    · exact (hab i l).eq
    · exact (hab j k).symm.eq
    · exact (hbb k l).eq
  have hle : Algebra.adjoin ℂ (Set.range a ∪ Set.range b) ≤ S := by
    apply Algebra.adjoin_le
    rintro x (⟨i, rfl⟩ | ⟨k, rfl⟩)
    · exact haS i
    · exact hbS k
  have hmc : ∀ x y : Algebra.adjoin ℂ (Set.range a ∪ Set.range b), x * y = y * x := by
    intro x y
    apply Subtype.ext
    have h1 : ∀ z ∈ Set.range a ∪ Set.range b, Commute z (y : A) := fun z hz =>
      Algebra.commute_of_mem_adjoin_of_forall_mem_commute y.2 (fun w hw => hcomm z hz w hw)
    exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute x.2
      (fun w hw => (h1 w hw).symm)).symm.eq
  letI : CommRing (Algebra.adjoin ℂ (Set.range a ∪ Set.range b)) :=
    { (inferInstance : Ring (Algebra.adjoin ℂ (Set.range a ∪ Set.range b))) with
      mul_comm := hmc }
  let a' : ι → Algebra.adjoin ℂ (Set.range a ∪ Set.range b) :=
    fun i => ⟨a i, Algebra.subset_adjoin (Or.inl ⟨i, rfl⟩)⟩
  let b' : κ → Algebra.adjoin ℂ (Set.range a ∪ Set.range b) :=
    fun k => ⟨b k, Algebra.subset_adjoin (Or.inr ⟨k, rfl⟩)⟩
  let e : MvPolynomial κ (MvPolynomial ι ℂ) →+* Algebra.adjoin ℂ (Set.range a ∪ Set.range b) :=
    eval₂Hom (eval₂Hom (algebraMap ℂ _) a') b'
  refine ⟨(Algebra.adjoin ℂ (Set.range a ∪ Set.range b)).val.toRingHom.comp e, ?_, ?_, ?_, ?_⟩
  · intro c
    show ((e (C (C c)) : Algebra.adjoin ℂ (Set.range a ∪ Set.range b)) : A) = _
    simp only [e, eval₂Hom_C]
    rw [Algebra.algebraMap_eq_smul_one]
    rfl
  · intro i
    show ((e (C (X i)) : Algebra.adjoin ℂ (Set.range a ∪ Set.range b)) : A) = _
    simp only [e, eval₂Hom_C, eval₂Hom_X']
    rfl
  · intro k
    show ((e (X k) : Algebra.adjoin ℂ (Set.range a ∪ Set.range b)) : A) = _
    simp only [e, eval₂Hom_X']
    rfl
  · intro P
    exact hle (e P).2
