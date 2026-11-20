import Mathlib

namespace GlobalTheory

/- English proof (translation)
Take `⟨s, hs⟩` from `(Algebra.FiniteType.out : (⊤ : Subalgebra R A).FG)`. Use `⟨s.image (fun x => x - e x), ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.coe_image]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Ideal.span_le]`.

Introduce and unpack `_ ⟨x, _, rfl⟩`. Express the relevant statement in the definitionally equal form `e.rangeRestrict (x - e x) = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[he]`. Introduce `b hb`.

Establish `hb' : e b = 0`. Use `congrArg Subtype.val (show e.rangeRestrict b = 0 from hb)` as an intermediate fact. Simplify using `using this`. Establish `key : ∀ y : A, y - e y ∈ Ideal.span ((fun x => x - e x) '' (s : Set A))`. Introduce `y`.

Establish `hy : y ∈ Algebra.adjoin R (s : Set A)` using `by rw [hs]; exact Algebra.mem_top`. Proceed by induction on `hy using Algebra.adjoin_induction with`. Consider the case `mem x hx => exact Ideal.subset_span ⟨x, hx, rfl⟩`. Consider the case `algebraMap r => simp`. Consider the case `add x y _ _ hx hy`.

Establish `h : x + y - e (x + y) = (x - e x) + (y - e y)` using `by rw [map_add]; ring`. Rewrite using `[h]`. Conclude with `Ideal.add_mem _ hx hy`. Consider the case `mul x y _ _ hx hy`. Establish `h : x * y - e (x * y) = x * (y - e y) + e y * (x - e x)` using `by rw [map_mul]; ring`.

Rewrite using `[h]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ hy) (Ideal.mul_mem_left _ _ hx)`. Simplify `key b` using `[hb']`.
-/
theorem idempotent_algHom_ker_fg {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (e : A →ₐ[R] A) (he : ∀ x, e (e x) = e x) :
    (RingHom.ker e.rangeRestrict.toRingHom).FG := by
  classical
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R A).FG)
  refine ⟨s.image (fun x => x - e x), ?_⟩
  rw [Finset.coe_image]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨x, _, rfl⟩
    change e.rangeRestrict (x - e x) = 0
    apply Subtype.ext
    simp [he]
  · intro b hb
    have hb' : e b = 0 := by
      have := congrArg Subtype.val (show e.rangeRestrict b = 0 from hb)
      simpa using this
    have key : ∀ y : A, y - e y ∈ Ideal.span ((fun x => x - e x) '' (s : Set A)) := by
      intro y
      have hy : y ∈ Algebra.adjoin R (s : Set A) := by rw [hs]; exact Algebra.mem_top
      induction hy using Algebra.adjoin_induction with
      | mem x hx => exact Ideal.subset_span ⟨x, hx, rfl⟩
      | algebraMap r => simp
      | add x y _ _ hx hy =>
        have h : x + y - e (x + y) = (x - e x) + (y - e y) := by rw [map_add]; ring
        rw [h]; exact Ideal.add_mem _ hx hy
      | mul x y _ _ hx hy =>
        have h : x * y - e (x * y) = x * (y - e y) + e y * (x - e x) := by rw [map_mul]; ring
        rw [h]; exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hy) (Ideal.mul_mem_left _ _ hx)
    simpa [hb'] using key b

/- English proof (translation)
Introduce `R A _ _ _ _ e he`. Establish `hq : ∀ b : e.range, e.rangeRestrict (b : A) = b`. Introduce and unpack `⟨_, a, rfl⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[he]`.

Establish `hsurj : Function.Surjective e.rangeRestrict` using `fun b => ⟨b, hq b⟩`. Use `{ formallySmooth := ?_, finitePresentation := ?_ }` and prove the remaining obligations. Use `Algebra.FormallySmooth.of_split e.rangeRestrict ((Ideal.Quotient.mkₐ R _).comp e.range.val) ?_` and prove the remaining obligations. Use extensionality with `b`. Simplify using `only [AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgHom.coe_id, id_eq, Subalgebra.coe_val]`.

Rewrite using `[AlgHom.kerSquareLift_mk, hq]`. Conclude with `Algebra.FinitePresentation.of_surjective hsurj (idempotent_algHom_ker_fg e he)`.
-/
theorem smooth_range_of_idempotent : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.Smooth R A] (e : A →ₐ[R] A), (∀ x, e (e x) = e x) → Algebra.Smooth R e.range := by
  intro R A _ _ _ _ e he
  have hq : ∀ b : e.range, e.rangeRestrict (b : A) = b := by
    rintro ⟨_, a, rfl⟩
    apply Subtype.ext
    simp [he]
  have hsurj : Function.Surjective e.rangeRestrict := fun b => ⟨b, hq b⟩
  refine { formallySmooth := ?_, finitePresentation := ?_ }
  · refine Algebra.FormallySmooth.of_split e.rangeRestrict
      ((Ideal.Quotient.mkₐ R _).comp e.range.val) ?_
    ext b
    simp only [AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgHom.coe_id, id_eq,
      Subalgebra.coe_val]
    rw [AlgHom.kerSquareLift_mk, hq]
  · exact Algebra.FinitePresentation.of_surjective hsurj (idempotent_algHom_ker_fg e he)

end GlobalTheory
