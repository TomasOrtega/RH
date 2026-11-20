import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PGradedFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

namespace HilbExactDivide

variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

open Classical in

/- English proof (translation)
Establish `hs' : s ∈ weightedHomogeneousSubmodule F (blockWeight ι) c` using `(mem_weightedHomogeneousSubmodule _ _ _ _).mpr hs`. Use `DirectSum.coe_decompose_mul_of_right_mem (𝒜 := weightedHomogeneousSubmodule F (blockWeight ι)) n (a := t) hs'` as an intermediate fact. Rewrite using `[← weightedDecomposition.decompose'_apply, ← weightedDecomposition.decompose'_apply]`. Conclude with `this`.
-/
theorem component_mul_form {c : K → ℕ} {s : MRing ι F} (hs : IsMultiHomog s c)
    (t : MRing ι F) (n : K → ℕ) :
    weightedHomogeneousComponent (blockWeight ι) n (t * s) =
      if c ≤ n then weightedHomogeneousComponent (blockWeight ι) (n - c) t * s else 0 := by
  have hs' : s ∈ weightedHomogeneousSubmodule F (blockWeight ι) c :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hs
  have := DirectSum.coe_decompose_mul_of_right_mem
    (𝒜 := weightedHomogeneousSubmodule F (blockWeight ι)) n (a := t) hs'
  rw [← weightedDecomposition.decompose'_apply, ← weightedDecomposition.decompose'_apply]
  exact this

/- English proof (translation)
Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.mp hfL`. Take `⟨t, rfl⟩` from `Ideal.mem_span_singleton'.mp hb`. Use `⟨t, ?_⟩` and prove the remaining obligations. Establish `h1 : weightedHomogeneousComponent (blockWeight ι) n (a + t * s) = a + t * s` using `IsWeightedHomogeneous.weightedHomogeneousComponent_same hf`. Establish `e : a + t * s - weightedHomogeneousComponent (blockWeight ι) n (t * s) = weightedHomogeneousComponent (blockWeight ι) n a`.

Rewrite using `[sub_eq_iff_eq_add, ← map_add, h1]`. Rewrite using `[e]`. Conclude with `hI a ha n`.
-/
theorem exists_sub_component_mem {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I)
    {s f : MRing ι F} {n : K → ℕ} (hf : IsMultiHomog f n) (hfL : f ∈ I ⊔ Ideal.span {s}) :
    ∃ t : MRing ι F, f - weightedHomogeneousComponent (blockWeight ι) n (t * s) ∈ I := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hfL
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hb
  refine ⟨t, ?_⟩
  have h1 : weightedHomogeneousComponent (blockWeight ι) n (a + t * s) = a + t * s :=
    IsWeightedHomogeneous.weightedHomogeneousComponent_same hf
  have e : a + t * s - weightedHomogeneousComponent (blockWeight ι) n (t * s) =
      weightedHomogeneousComponent (blockWeight ι) n a := by
    rw [sub_eq_iff_eq_add, ← map_add, h1]
  rw [e]
  exact hI a ha n

omit [DecidableEq K] in

/- English proof (translation)
Rewrite using `[Submodule.mem_colon]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Simplify `h s (Ideal.subset_span rfl)` using `[smul_eq_mul]`. Introduce `h x hx`.

Take `⟨t, rfl⟩` from `Ideal.mem_span_singleton'.mp hx`. Rewrite using `[smul_eq_mul, show g * (t * s) = t * (g * s) by ring]`. Conclude with `I.mul_mem_left t h`.
-/
theorem mem_colon_span_iff {I : Ideal (MRing ι F)} {s g : MRing ι F} :
    g ∈ I.colon (Ideal.span {s}) ↔ g * s ∈ I := by
  rw [Submodule.mem_colon]
  constructor
  · intro h
    simpa [smul_eq_mul] using h s (Ideal.subset_span rfl)
  · intro h x hx
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [smul_eq_mul, show g * (t * s) = t * (g * s) by ring]
    exact I.mul_mem_left t h

open Classical in

/- English proof (translation)
Establish `hIL : I ≤ I ⊔ Ideal.span {s}` using `le_sup_left`. Set `π : (MRing ι F ⧸ I) →ₗ[F] (MRing ι F ⧸ (I ⊔ Ideal.span {s}))` to `(Ideal.Quotient.liftₐ I (Ideal.Quotient.mkₐ F (I ⊔ Ideal.span {s})) (fun a ha => by`. Rewrite using `[Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hIL ha)).toLinearMap`. Establish `hπ : ∀ x, π (Ideal.Quotient.mk I x) = Ideal.Quotient.mk (I ⊔ Ideal.span {s}) x` using `fun x => rfl`.

Establish `: FiniteDimensional F (gradedPiece I n)` using `(h1 F K ι I n).1`. Establish `hrn` using `(π.domRestrict (gradedPiece I n)).finrank_range_add_finrank_ker`. Establish `hrange : LinearMap.range (π.domRestrict (gradedPiece I n)) = gradedPiece (I ⊔ Ideal.span {s}) n`. Rewrite using `[LinearMap.range_domRestrict, gradedPiece, gradedPiece, ← Submodule.map_comp]`. Use `congr 1`.

Establish `hkerdesc : ∀ y ∈ LinearMap.ker (π.domRestrict (gradedPiece I n)), ∃ f : MRing ι F, IsMultiHomog f n ∧ f ∈ I ⊔ Ideal.span {s} ∧ ((y : gradedPiece I n) : MRing ι F ⧸ I) = Ideal.Quotient.mk I f`. Introduce and unpack `⟨y, hy⟩ hker`. Take `⟨f, hf, rfl⟩` from `Submodule.mem_map.mp hy`. Use `⟨f, (mem_weightedHomogeneousSubmodule _ _ _ _).mp hf, ?_, rfl⟩` and prove the remaining obligations. Rewrite `hker` using `[LinearMap.mem_ker, LinearMap.domRestrict_apply]`.

Establish `: π (Ideal.Quotient.mk I f) = 0` using `hker`. Rewrite `this` using `[hπ, Ideal.Quotient.eq_zero_iff_mem]`. Then use the resulting hypothesis. Rewrite using `[← hrange, ← hrn]`. Use `congr 1`. Distinguish the cases in `hc : c ≤ n`.

Rewrite using `[if_pos hc]`. Set `W` to `weightedHomogeneousSubmodule F (blockWeight ι) (n - c)`. Set `α : W →ₗ[F] (MRing ι F ⧸ I.colon (Ideal.span {s}))` to `(Ideal.Quotient.mkₐ F (I.colon (Ideal.span {s}))).toLinearMap ∘ₗ W.subtype`. Set `β : W →ₗ[F] (MRing ι F ⧸ I)` to `(Ideal.Quotient.mkₐ F I).toLinearMap ∘ₗ (LinearMap.mulRight F s) ∘ₗ W.subtype`. Establish `hker : LinearMap.ker α = LinearMap.ker β`.

Use extensionality with `g`. Simplify using `[α, β, Ideal.Quotient.eq_zero_iff_mem]`. Rewrite using `[← map_mul, Ideal.Quotient.eq_zero_iff_mem]`. Establish `e1 : LinearMap.range α = gradedPiece (I.colon (Ideal.span {s})) (n - c)`. Rewrite using `[LinearMap.range_comp, Submodule.range_subtype]`.

Both sides reduce to the same expression. Establish `e2 : LinearMap.range β = (LinearMap.ker (π.domRestrict (gradedPiece I n))).map (gradedPiece I n).subtype`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨g, hg⟩, rfl⟩`.

Establish `hgs : g * s ∈ weightedHomogeneousSubmodule F (blockWeight ι) n`. Use `IsWeightedHomogeneous.mul ((mem_weightedHomogeneousSubmodule _ _ _ _).mp hg) hs` as an intermediate fact. Rewrite `this` using `[tsub_add_cancel_of_le hc]`. Conclude with `(mem_weightedHomogeneousSubmodule _ _ _ _).mpr this`. Use `⟨⟨(Ideal.Quotient.mkₐ F I).toLinearMap (g * s), Submodule.mem_map_of_mem hgs⟩, ?_, rfl⟩` and prove the remaining obligations.

Rewrite using `[SetLike.mem_coe, LinearMap.mem_ker, LinearMap.domRestrict_apply]`. Express the relevant statement in the definitionally equal form `π ((Ideal.Quotient.mkₐ F I) (g * s)) = 0`. Rewrite using `[Ideal.Quotient.mkₐ_eq_mk, hπ, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨g, rfl⟩)`. Introduce and unpack `⟨y, hy, rfl⟩`.

Take `⟨f, hf, hfL, hyf⟩` from `hkerdesc y hy`. Take `⟨t, ht⟩` from `exists_sub_component_mem hI hf hfL`. Rewrite `ht` using `[component_mul_form hs, if_pos hc]`. Use `⟨⟨weightedHomogeneousComponent (blockWeight ι) (n - c) t, weightedHomogeneousComponent_mem _ _ _⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk I (weightedHomogeneousComponent (blockWeight ι) (n - c) t * s) = ((y : gradedPiece I n) : MRing ι F ⧸ I)`.

Rewrite using `[hyf, Ideal.Quotient.eq]`. Simplify using `using I.neg_mem ht`. Establish `eα : LinearMap.range α ≃ₗ[F] LinearMap.range β` using `α.quotKerEquivRange.symm ≪≫ₗ Submodule.quotEquivOfEq _ _ hker ≪≫ₗ β.quotKerEquivRange`. Rewrite using `[← e1, eα.finrank_eq, e2]`. Conclude with `(Submodule.equivMapOfInjective (gradedPiece I n).subtype Subtype.val_injective (LinearMap.ker (π.domRestrict (gradedPiece I n)))).finrank_eq`.

Rewrite using `[if_neg hc]`. Establish `hbot : LinearMap.ker (π.domRestrict (gradedPiece I n)) = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `y hy`. Take `⟨f, hf, hfL, hyf⟩` from `hkerdesc y hy`.

Take `⟨t, ht⟩` from `exists_sub_component_mem hI hf hfL`. Rewrite `ht` using `[component_mul_form hs, if_neg hc, sub_zero]`. Rewrite using `[Submodule.mem_bot]`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hyf, ZeroMemClass.coe_zero, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `ht`. Rewrite using `[hbot, finrank_bot]`.
-/
theorem finrank_eq (h1 : GradedFinite.Statement.{u}) [Fintype K] [∀ k, Fintype (ι k)]
    {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I) {c : K → ℕ} {s : MRing ι F}
    (hs : IsMultiHomog s c) (n : K → ℕ) :
    Module.finrank F (gradedPiece I n) =
      Module.finrank F (gradedPiece (I ⊔ Ideal.span {s}) n) +
        (if c ≤ n then Module.finrank F (gradedPiece (I.colon (Ideal.span {s})) (n - c))
          else 0) := by
  have hIL : I ≤ I ⊔ Ideal.span {s} := le_sup_left
  let π : (MRing ι F ⧸ I) →ₗ[F] (MRing ι F ⧸ (I ⊔ Ideal.span {s})) :=
    (Ideal.Quotient.liftₐ I (Ideal.Quotient.mkₐ F (I ⊔ Ideal.span {s}))
      (fun a ha => by
        rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
        exact hIL ha)).toLinearMap
  have hπ : ∀ x, π (Ideal.Quotient.mk I x) = Ideal.Quotient.mk (I ⊔ Ideal.span {s}) x :=
    fun x => rfl
  have : FiniteDimensional F (gradedPiece I n) := (h1 F K ι I n).1
  have hrn := (π.domRestrict (gradedPiece I n)).finrank_range_add_finrank_ker
  have hrange : LinearMap.range (π.domRestrict (gradedPiece I n)) =
      gradedPiece (I ⊔ Ideal.span {s}) n := by
    rw [LinearMap.range_domRestrict, gradedPiece, gradedPiece, ← Submodule.map_comp]
    congr 1

  have hkerdesc : ∀ y ∈ LinearMap.ker (π.domRestrict (gradedPiece I n)),
      ∃ f : MRing ι F, IsMultiHomog f n ∧ f ∈ I ⊔ Ideal.span {s} ∧
        ((y : gradedPiece I n) : MRing ι F ⧸ I) = Ideal.Quotient.mk I f := by
    rintro ⟨y, hy⟩ hker
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hy
    refine ⟨f, (mem_weightedHomogeneousSubmodule _ _ _ _).mp hf, ?_, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hker
    have : π (Ideal.Quotient.mk I f) = 0 := hker
    rwa [hπ, Ideal.Quotient.eq_zero_iff_mem] at this
  rw [← hrange, ← hrn]
  congr 1
  by_cases hc : c ≤ n
  · rw [if_pos hc]
    let W := weightedHomogeneousSubmodule F (blockWeight ι) (n - c)
    let α : W →ₗ[F] (MRing ι F ⧸ I.colon (Ideal.span {s})) :=
      (Ideal.Quotient.mkₐ F (I.colon (Ideal.span {s}))).toLinearMap ∘ₗ W.subtype
    let β : W →ₗ[F] (MRing ι F ⧸ I) :=
      (Ideal.Quotient.mkₐ F I).toLinearMap ∘ₗ (LinearMap.mulRight F s) ∘ₗ W.subtype
    have hker : LinearMap.ker α = LinearMap.ker β := by
      ext g
      simp [α, β, Ideal.Quotient.eq_zero_iff_mem]
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    have e1 : LinearMap.range α = gradedPiece (I.colon (Ideal.span {s})) (n - c) := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
      rfl
    have e2 : LinearMap.range β =
        (LinearMap.ker (π.domRestrict (gradedPiece I n))).map (gradedPiece I n).subtype := by
      ext x
      constructor
      · rintro ⟨⟨g, hg⟩, rfl⟩
        have hgs : g * s ∈ weightedHomogeneousSubmodule F (blockWeight ι) n := by
          have := IsWeightedHomogeneous.mul ((mem_weightedHomogeneousSubmodule _ _ _ _).mp hg) hs
          rw [tsub_add_cancel_of_le hc] at this
          exact (mem_weightedHomogeneousSubmodule _ _ _ _).mpr this
        refine ⟨⟨(Ideal.Quotient.mkₐ F I).toLinearMap (g * s), Submodule.mem_map_of_mem hgs⟩,
          ?_, rfl⟩
        rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.domRestrict_apply]
        change π ((Ideal.Quotient.mkₐ F I) (g * s)) = 0
        rw [Ideal.Quotient.mkₐ_eq_mk, hπ, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨g, rfl⟩)
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨f, hf, hfL, hyf⟩ := hkerdesc y hy
        obtain ⟨t, ht⟩ := exists_sub_component_mem hI hf hfL
        rw [component_mul_form hs, if_pos hc] at ht
        refine ⟨⟨weightedHomogeneousComponent (blockWeight ι) (n - c) t,
          weightedHomogeneousComponent_mem _ _ _⟩, ?_⟩
        change Ideal.Quotient.mk I (weightedHomogeneousComponent (blockWeight ι) (n - c) t * s) =
          ((y : gradedPiece I n) : MRing ι F ⧸ I)
        rw [hyf, Ideal.Quotient.eq]
        simpa using I.neg_mem ht
    have eα : LinearMap.range α ≃ₗ[F] LinearMap.range β :=
      α.quotKerEquivRange.symm ≪≫ₗ Submodule.quotEquivOfEq _ _ hker ≪≫ₗ β.quotKerEquivRange
    rw [← e1, eα.finrank_eq, e2]
    exact (Submodule.equivMapOfInjective (gradedPiece I n).subtype Subtype.val_injective
      (LinearMap.ker (π.domRestrict (gradedPiece I n)))).finrank_eq
  · rw [if_neg hc]
    have hbot : LinearMap.ker (π.domRestrict (gradedPiece I n)) = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨f, hf, hfL, hyf⟩ := hkerdesc y hy
      obtain ⟨t, ht⟩ := exists_sub_component_mem hI hf hfL
      rw [component_mul_form hs, if_neg hc, sub_zero] at ht
      rw [Submodule.mem_bot]
      apply Subtype.ext
      rw [hyf, ZeroMemClass.coe_zero, Ideal.Quotient.eq_zero_iff_mem]
      exact ht
    rw [hbot, finrank_bot]

/- English proof (translation)
Introduce `F _ K _ _ ι _ I hI c s hs m`. Distinguish the cases in `hm : ∀ k, 0 ≤ m k`. Take `⟨n, rfl⟩ : ∃ n : K → ℕ, m = fun k => (n k : ℤ)` from `⟨fun k => (m k).toNat, funext fun k => (Int.toNat_of_nonneg (hm k)).symm⟩`. Establish `key` using `finrank_eq h1 hI hs n`. Rewrite using `[(h1 F K ι I n).2, (h1 F K ι (I ⊔ Ideal.span {s}) n).2, key]`.

Distinguish the cases in `hc : c ≤ n`. Rewrite using `[if_pos hc]`. Establish `hnc : ((fun k => (n k : ℤ)) - fun k => (c k : ℤ)) = fun k => ((n - c) k : ℤ)`. Use function extensionality and compare the values at `fun k => by`. Establish `: c k ≤ n k` using `hc k`.

Simplify using `only [Pi.sub_apply]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hnc, (h1 F K ι _ (n - c)).2]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[if_neg hc]`. Establish `hneg : hilbFn (I.colon (Ideal.span {s})) ((fun k => (n k : ℤ)) - fun k => (c k : ℤ)) = 0`. Rewrite using `[hilbFn, if_neg]`. Introduce `hall`. Apply `hc` to reduce the goal to its premises.

Introduce `k`. Use `show c k ≤ n k`. Use `hall k` as an intermediate fact. Simplify using `only [Pi.sub_apply] at this`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[hneg]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hm' : ¬ ∀ k, 0 ≤ (m - fun k => (c k : ℤ)) k`. Introduce `hall`.

Apply `hm` to reduce the goal to its premises. Introduce `k`. Use `hall k` as an intermediate fact. Simplify using `only [Pi.sub_apply] at this`. Use linear arithmetic over natural numbers and integers.

Simplify using `only [hilbFn, if_neg hm, if_neg hm', sub_zero]`.
-/
theorem proof (h1 : GradedFinite.Statement.{u}) : HilbExactDivide.Statement.{u} := by
  intro F _ K _ _ ι _ I hI c s hs m
  by_cases hm : ∀ k, 0 ≤ m k
  · obtain ⟨n, rfl⟩ : ∃ n : K → ℕ, m = fun k => (n k : ℤ) :=
      ⟨fun k => (m k).toNat, funext fun k => (Int.toNat_of_nonneg (hm k)).symm⟩
    have key := finrank_eq h1 hI hs n
    rw [(h1 F K ι I n).2, (h1 F K ι (I ⊔ Ideal.span {s}) n).2, key]
    by_cases hc : c ≤ n
    · rw [if_pos hc]
      have hnc : ((fun k => (n k : ℤ)) - fun k => (c k : ℤ)) = fun k => ((n - c) k : ℤ) :=
        funext fun k => by
          have : c k ≤ n k := hc k
          simp only [Pi.sub_apply]
          omega
      rw [hnc, (h1 F K ι _ (n - c)).2]
      push_cast
      ring
    · rw [if_neg hc]
      have hneg : hilbFn (I.colon (Ideal.span {s}))
          ((fun k => (n k : ℤ)) - fun k => (c k : ℤ)) = 0 := by
        rw [hilbFn, if_neg]
        intro hall
        apply hc
        intro k
        show c k ≤ n k
        have := hall k
        simp only [Pi.sub_apply] at this
        omega
      rw [hneg]
      push_cast
      ring
  · have hm' : ¬ ∀ k, 0 ≤ (m - fun k => (c k : ℤ)) k := by
      intro hall
      apply hm
      intro k
      have := hall k
      simp only [Pi.sub_apply] at this
      omega
    simp only [hilbFn, if_neg hm, if_neg hm', sub_zero]

/- English proof (translation)
The claim follows from `proof GradedFinite.proof`.
-/
theorem closed : HilbExactDivide.Statement.{u} :=
  proof GradedFinite.proof

end HilbExactDivide

end

end GroundTheory.Heights₂.Heights.FieldNumbers
