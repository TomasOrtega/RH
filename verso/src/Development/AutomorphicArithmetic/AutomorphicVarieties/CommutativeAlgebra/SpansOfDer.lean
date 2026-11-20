import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

/- English proof (translation)
Establish `hne : (Submodule.torsion O (L ⧸ S)).mkQ (S.mkQ p) ≠ 0`. Introduce `h`. Rewrite `h` using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Take `⟨⟨c, hc⟩, hcp⟩` from `h`. Use `hp c (nonZeroDivisors.ne_zero hc) ?_` and prove the remaining obligations.

Rewrite using `[← Submodule.Quotient.mk_eq_zero]`. Conclude with `hcp`. Take `⟨ψ, hψ⟩` from `Module.Projective.exists_dual_ne_zero O hne`. Use `⟨ψ ∘ₗ (Submodule.torsion O (L ⧸ S)).mkQ ∘ₗ S.mkQ, fun s hs => ?_, hψ⟩` and prove the remaining obligations. Establish `: S.mkQ s = 0` using `(Submodule.Quotient.mk_eq_zero S).2 hs`.

Simplify using `only [LinearMap.comp_apply, this, map_zero]`.
-/
private theorem UpperTheory.V.Alg.exists_form_of_not_torsion {O L : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [AddCommGroup L] [Module O L] [Module.Finite O L] (S : Submodule O L) (p : L)
    (hp : ∀ c : O, c ≠ 0 → c • p ∉ S) : ∃ φ : L →ₗ[O] O, (∀ s ∈ S, φ s = 0) ∧ φ p ≠ 0 := by
  have hne : (Submodule.torsion O (L ⧸ S)).mkQ (S.mkQ p) ≠ 0 := by
    intro h
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
    obtain ⟨⟨c, hc⟩, hcp⟩ := h
    refine hp c (nonZeroDivisors.ne_zero hc) ?_
    rw [← Submodule.Quotient.mk_eq_zero]
    exact hcp
  obtain ⟨ψ, hψ⟩ := Module.Projective.exists_dual_ne_zero O hne
  refine ⟨ψ ∘ₗ (Submodule.torsion O (L ⧸ S)).mkQ ∘ₗ S.mkQ, fun s hs => ?_, hψ⟩
  have : S.mkQ s = 0 := (Submodule.Quotient.mk_eq_zero S).2 hs
  simp only [LinearMap.comp_apply, this, map_zero]

/- English proof (translation)
Establish `h0 : ∀ f : A, x (DirectSum.decompose 𝒜 f 0 : A) = x f`. Introduce `f`. Proceed by induction on `f using DirectSum.Decomposition.inductionOn 𝒜 with`. Consider the case `zero => simp`. Consider the case `@homogeneous i m`.

Distinguish the cases in `hi : i = 0`. Substitute `hi` using the available equality. Rewrite using `[DirectSum.decompose_of_mem_same 𝒜 m.2]`. Rewrite using `[DirectSum.decompose_of_mem_ne 𝒜 m.2 hi, map_zero, hx i hi m m.2]`. Consider the case `add a b ha hb => simp [ha, hb]`.

Introduce `i f hf`. Rewrite `hf`, the goal using `[RingHom.mem_ker]`. Distinguish the cases in `hi : i = 0`. Substitute `hi` using the available equality. Rewrite using `[h0, hf]`.

Conclude with `hx i hi _ (DirectSum.decompose 𝒜 f i).2`.
-/
private theorem UpperTheory.V.Alg.ker_isHomogeneous {O A X : Type} [CommRing O] [CommRing A] [Algebra O A]
    [AddCommGroup X] [DecidableEq X] (𝒜 : X → Submodule O A) [GradedAlgebra 𝒜] (x : A →ₐ[O] O)
    (hx : ∀ i, i ≠ 0 → ∀ f ∈ 𝒜 i, x f = 0) : (RingHom.ker x).IsHomogeneous 𝒜 := by
  have h0 : ∀ f : A, x (DirectSum.decompose 𝒜 f 0 : A) = x f := by
    intro f
    induction f using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | @homogeneous i m =>
      by_cases hi : i = 0
      · subst hi
        rw [DirectSum.decompose_of_mem_same 𝒜 m.2]
      · rw [DirectSum.decompose_of_mem_ne 𝒜 m.2 hi, map_zero, hx i hi m m.2]
    | add a b ha hb => simp [ha, hb]
  intro i f hf
  rw [RingHom.mem_ker] at hf ⊢
  by_cases hi : i = 0
  · subst hi
    rw [h0, hf]
  · exact hx i hi _ (DirectSum.decompose 𝒜 f i).2

/- English proof (translation)
Introduce `O A X _ _ _ _ _ _ _ 𝒜 _ x hx j hfg ι F hF hD p hp`. Assume the negation of the conclusion as `hcon`. Use `haveI : Module.Finite O (cotLat x 𝒜 j) := Module.Finite.iff_fg.2 hfg`. Take `⟨φ, hφS, hφp⟩` from `exists_form_of_not_torsion ((cotSpan x F).comap (cotLat x 𝒜 j).subtype) ⟨p, hp⟩ (fun c hc h => hcon ⟨c, hc, h⟩)`. Establish `hq` using `ker_isHomogeneous 𝒜 x hx`.

Establish `hq2 : (RingHom.ker x ^ 2).IsHomogeneous 𝒜` using `by rw [pow_two]; exact hq.mul hq`. Set `r : A →ₗ[O] A` to `LinearMap.id - Algebra.linearMap O A ∘ₗ x.toLinearMap`. Establish `hr : ∀ f, r f = f - algebraMap O A (x f)` using `fun f => rfl`. Establish `hrq : ∀ f, r f ∈ RingHom.ker x` using `fun f => by`. Rewrite using `[RingHom.mem_ker, hr, map_sub, AlgHom.commutes]`.

Simplify using the standard rewrite rules. Set `T : A →ₗ[O] A ⧸ satSq x` to `(satSq x).mkQ ∘ₗ GradedAlgebra.proj 𝒜 j ∘ₗ r`. Establish `hT : ∀ f, T f = (satSq x).mkQ (DirectSum.decompose 𝒜 (r f) j : A)` using `fun f => rfl`. Establish `hTL : ∀ f, T f ∈ cotLat x 𝒜 j` using `fun f => ⟨_, ⟨(DirectSum.decompose 𝒜 (r f) j).2, hq j (hrq f)⟩, (hT f).symm⟩`. Establish `hTj : ∀ f ∈ 𝒜 j, x f = 0 → T f = (satSq x).mkQ f` using `fun f hf h0 => by`.

Rewrite using `[hT, hr, h0, map_zero, sub_zero, DirectSum.decompose_of_mem_same 𝒜 hf]`. Establish `hTi : ∀ i, i ≠ j → ∀ f ∈ 𝒜 i, T f = 0` using `fun i hi f hf => by`. Establish `: r f ∈ 𝒜 i`. Distinguish the cases in `h0 : i = 0`. Substitute `h0` using the available equality.

Rewrite using `[hr]`. Conclude with `sub_mem hf (SetLike.algebraMap_mem_graded 𝒜 _)`. Rewrite using `[hr, hx i h0 f hf, map_zero, sub_zero]`. Conclude with `hf`. Rewrite using `[hT, DirectSum.decompose_of_mem_ne 𝒜 this hi, map_zero]`.

Establish `hTm : ∀ f g, T (f * g) = x f • T g + x g • T f` using `fun f g => by`. Establish `e : r (f * g) = r f * r g + (x f • r g + x g • r f)`. Simplify using `only [hr, Algebra.smul_def, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hz : (satSq x).mkQ (GradedAlgebra.proj 𝒜 j (r f * r g)) = 0`.

Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Use `⟨1, one_ne_zero, ?_⟩` and prove the remaining obligations. Rewrite using `[one_smul]`. Use `hq2 j ?_` and prove the remaining obligations. Rewrite using `[pow_two]`.

Conclude with `Ideal.mul_mem_mul (hrq f) (hrq g)`. Use `show (satSq x).mkQ (GradedAlgebra.proj 𝒜 j (r (f * g))) = x f • (satSq x).mkQ (GradedAlgebra.proj 𝒜 j (r g)) + x g • (satSq x).mkQ (GradedAlgebra.proj 𝒜 j (r f))`. Rewrite using `[e]`. Simplify using `only [map_add, map_smul, hz, zero_add]`. Set `T' : A →ₗ[O] cotLat x 𝒜 j` to `T.codRestrict _ hTL`.

Establish `hD0 : φ ∘ₗ T' = 0`. Use `hD _ (fun f g => ?_) (fun i hi f hf => ?_) (fun i => ?_)` and prove the remaining obligations. Establish `: T' (f * g) = x f • T' g + x g • T' f` using `Subtype.ext (hTm f g)`. Simplify using `only [LinearMap.comp_apply, this, map_add, map_smul]`. Establish `: T' f = 0` using `Subtype.ext (hTi i hi f hf)`.

Simplify using `only [LinearMap.comp_apply, this, map_zero]`. Use `hφS _ ?_ show T (F i) ∈ cotSpan x F` and prove the remaining obligations. Rewrite using `[hTj _ (hF i).1 (hF i).2]`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`. Take `⟨a, ⟨ha1, ha2⟩, rfl⟩` from `hp`.

Apply `hφp` to reduce the goal to its premises. Establish `h1 : φ (T' a) = 0` using `LinearMap.congr_fun hD0 a`. Rewrite using `[← h1]`. Use `congr 1`. Conclude with `Subtype.ext (hTj a ha1 ha2).symm`.
-/
theorem UpperTheory.V.Alg.spans_of_der :
    ∀ (O A X : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [Algebra O A] [AddCommGroup X] [DecidableEq X] (𝒜 : X → Submodule O A) [GradedAlgebra 𝒜] (x : A →ₐ[O] O),
      (∀ i, i ≠ 0 → ∀ f ∈ 𝒜 i, x f = 0) → ∀ (j : X), (cotLat x 𝒜 j).FG → ∀ (ι : Type) (F : ι → A), (∀ i, F i ∈ 𝒜 j ∧ x (F i) = 0) →
      (∀ D ∈ PtDer x O, HasWt 𝒜 j D → (∀ i, D (F i) = 0) → D = 0) → SpansCot x 𝒜 j F := by
  intro O A X _ _ _ _ _ _ _ 𝒜 _ x hx j hfg ι F hF hD p hp
  by_contra hcon
  haveI : Module.Finite O (cotLat x 𝒜 j) := Module.Finite.iff_fg.2 hfg
  obtain ⟨φ, hφS, hφp⟩ := exists_form_of_not_torsion ((cotSpan x F).comap (cotLat x 𝒜 j).subtype) ⟨p, hp⟩
    (fun c hc h => hcon ⟨c, hc, h⟩)
  have hq := ker_isHomogeneous 𝒜 x hx
  have hq2 : (RingHom.ker x ^ 2).IsHomogeneous 𝒜 := by rw [pow_two]; exact hq.mul hq
  let r : A →ₗ[O] A := LinearMap.id - Algebra.linearMap O A ∘ₗ x.toLinearMap
  have hr : ∀ f, r f = f - algebraMap O A (x f) := fun f => rfl
  have hrq : ∀ f, r f ∈ RingHom.ker x := fun f => by
    rw [RingHom.mem_ker, hr, map_sub, AlgHom.commutes]; simp
  let T : A →ₗ[O] A ⧸ satSq x := (satSq x).mkQ ∘ₗ GradedAlgebra.proj 𝒜 j ∘ₗ r
  have hT : ∀ f, T f = (satSq x).mkQ (DirectSum.decompose 𝒜 (r f) j : A) := fun f => rfl
  have hTL : ∀ f, T f ∈ cotLat x 𝒜 j := fun f =>
    ⟨_, ⟨(DirectSum.decompose 𝒜 (r f) j).2, hq j (hrq f)⟩, (hT f).symm⟩
  have hTj : ∀ f ∈ 𝒜 j, x f = 0 → T f = (satSq x).mkQ f := fun f hf h0 => by
    rw [hT, hr, h0, map_zero, sub_zero, DirectSum.decompose_of_mem_same 𝒜 hf]
  have hTi : ∀ i, i ≠ j → ∀ f ∈ 𝒜 i, T f = 0 := fun i hi f hf => by
    have : r f ∈ 𝒜 i := by
      by_cases h0 : i = 0
      · subst h0
        rw [hr]
        exact sub_mem hf (SetLike.algebraMap_mem_graded 𝒜 _)
      · rw [hr, hx i h0 f hf, map_zero, sub_zero]; exact hf
    rw [hT, DirectSum.decompose_of_mem_ne 𝒜 this hi, map_zero]
  have hTm : ∀ f g, T (f * g) = x f • T g + x g • T f := fun f g => by
    have e : r (f * g) = r f * r g + (x f • r g + x g • r f) := by
      simp only [hr, Algebra.smul_def, map_mul]; ring
    have hz : (satSq x).mkQ (GradedAlgebra.proj 𝒜 j (r f * r g)) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      refine ⟨1, one_ne_zero, ?_⟩
      rw [one_smul]
      refine hq2 j ?_
      rw [pow_two]
      exact Ideal.mul_mem_mul (hrq f) (hrq g)
    show (satSq x).mkQ (GradedAlgebra.proj 𝒜 j (r (f * g))) =
      x f • (satSq x).mkQ (GradedAlgebra.proj 𝒜 j (r g)) + x g • (satSq x).mkQ (GradedAlgebra.proj 𝒜 j (r f))
    rw [e]
    simp only [map_add, map_smul, hz, zero_add]
  let T' : A →ₗ[O] cotLat x 𝒜 j := T.codRestrict _ hTL
  have hD0 : φ ∘ₗ T' = 0 := by
    refine hD _ (fun f g => ?_) (fun i hi f hf => ?_) (fun i => ?_)
    · have : T' (f * g) = x f • T' g + x g • T' f := Subtype.ext (hTm f g)
      simp only [LinearMap.comp_apply, this, map_add, map_smul]
    · have : T' f = 0 := Subtype.ext (hTi i hi f hf)
      simp only [LinearMap.comp_apply, this, map_zero]
    · refine hφS _ ?_
      show T (F i) ∈ cotSpan x F
      rw [hTj _ (hF i).1 (hF i).2]
      exact Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨a, ⟨ha1, ha2⟩, rfl⟩ := hp
  apply hφp
  have h1 : φ (T' a) = 0 := LinearMap.congr_fun hD0 a
  rw [← h1]
  congr 1
  exact Subtype.ext (hTj a ha1 ha2).symm
