import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.SchemeModels

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct MvPolynomial

namespace GlobalTheory.CompanionTheory.SmoothSpread

section Witness

variable {T S ι σ : Type} [CommRing T] [CommRing S] [Algebra T S]

/- English proof (translation)
Set `f : Q.Ring →ₐ[T] S` to `IsScalarTower.toAlgHom _ _ _`. Establish `hkerf : RingHom.ker f = Ideal.span (.range Q.relation)` using `Q.span_range_relation_eq_ker.symm`. Take `⟨(τ : S →ₐ[T] MvPolynomial _ T ⧸ RingHom.ker f ^ 2), hsig⟩` from `(Algebra.FormallySmooth.iff_split_surjection f Q.algebraMap_surjective).mp inferInstance`. Establish `hex (i : _)` using `Ideal.Quotient.mk_surjective (τ <| Q.val i)`. Use `choose h hh using hex`.

Establish `hdiag : (Ideal.Quotient.mkₐ _ _).comp (aeval h) = τ.comp (aeval Q.val)` using `algHom_ext (by simp [hh])`. Use `⟨h, fun i ↦ ?_, fun j ↦ ?_⟩` and prove the remaining obligations. Establish `hs : f (h i) = Q.val i`. Rewrite using `[← AlgHom.kerSquareLift_mk]`. Conclude with `hh i ▸ congr($hsig (Q.val i))`.

Rewrite using `[← hkerf, RingHom.mem_ker, map_sub, sub_eq_zero, hs]`. Simplify using `[f]`. Establish `ho : Ideal.Quotient.mk (RingHom.ker f ^ 2) (aeval h (Q.relation j)) = 0`. It suffices to establish `ho : τ (aeval Q.val (Q.relation j)) = 0 by convert! ho`. Conclude with `congr($hdiag _)`.

Simplify using the standard rewrite rules. Rewrite `ho` using `[Ideal.Quotient.eq_zero_iff_mem, hkerf]`. Then use the resulting hypothesis.
-/
theorem exists_witness [Algebra.FormallySmooth T S] (Q : Algebra.Presentation T S ι σ) :
    ∃ h : ι → Q.Ring, (∀ i, h i - X i ∈ Ideal.span (Set.range Q.relation)) ∧
      ∀ j, aeval h (Q.relation j) ∈ Ideal.span (Set.range Q.relation) ^ 2 := by
  let f : Q.Ring →ₐ[T] S := IsScalarTower.toAlgHom _ _ _
  have hkerf : RingHom.ker f = Ideal.span (.range Q.relation) :=
    Q.span_range_relation_eq_ker.symm
  obtain ⟨(τ : S →ₐ[T] MvPolynomial _ T ⧸ RingHom.ker f ^ 2), hsig⟩ :=
    (Algebra.FormallySmooth.iff_split_surjection f Q.algebraMap_surjective).mp inferInstance
  have hex (i : _) := Ideal.Quotient.mk_surjective (τ <| Q.val i)
  choose h hh using hex
  have hdiag : (Ideal.Quotient.mkₐ _ _).comp (aeval h) = τ.comp (aeval Q.val) :=
    algHom_ext (by simp [hh])
  refine ⟨h, fun i ↦ ?_, fun j ↦ ?_⟩
  · have hs : f (h i) = Q.val i := by
      rw [← AlgHom.kerSquareLift_mk]
      exact hh i ▸ congr($hsig (Q.val i))
    rw [← hkerf, RingHom.mem_ker, map_sub, sub_eq_zero, hs]
    simp [f]
  · have ho : Ideal.Quotient.mk (RingHom.ker f ^ 2) (aeval h (Q.relation j)) = 0 := by
      suffices ho : τ (aeval Q.val (Q.relation j)) = 0 by
        convert! ho
        exact congr($hdiag _)
      simp
    rwa [Ideal.Quotient.eq_zero_iff_mem, hkerf] at ho

/- English proof (translation)
Set `f : Q.Ring →ₐ[T] S` to `IsScalarTower.toAlgHom _ _ _`. Establish `hf : Function.Surjective f` using `Q.algebraMap_surjective`. Establish `hkerf : RingHom.ker f = Ideal.span (.range Q.relation)` using `Q.span_range_relation_eq_ker.symm`. Set `g₀ : Q.Ring →ₐ[T] Q.Ring ⧸ RingHom.ker f.toRingHom ^ 2` to `(Ideal.Quotient.mkₐ T _).comp (aeval h)`. Establish `hg₀ : ∀ a ∈ RingHom.ker f.toRingHom, g₀ a = 0`.

Introduce `a ha`. Establish `ha' : a ∈ Ideal.span (Set.range Q.relation)` using `hkerf ▸ ha`. Establish `: Ideal.span (Set.range Q.relation) ≤ RingHom.ker g₀`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`.

Simplify using `only [SetLike.mem_coe, RingHom.mem_ker]`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk _ _ = 0`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem]`. Use `h2 j` as an intermediate fact. Rewrite `this` using `[← hkerf]`.

Conclude with `this`. Conclude with `this ha'`. Set `g : S →ₐ[T] Q.Ring ⧸ RingHom.ker f.toRingHom ^ 2` to `(Ideal.Quotient.liftₐ (RingHom.ker f.toRingHom) g₀ hg₀).comp (Ideal.quotientKerAlgEquivOfSurjective hf).symm.toAlgHom`. Use `Algebra.FormallySmooth.of_split f g ?_` and prove the remaining obligations. Rewrite using `[← AlgHom.cancel_right hf]`.

Use `MvPolynomial.algHom_ext fun i ↦ ?_` and prove the remaining obligations. Establish `hgf : g (f (X i)) = Ideal.Quotient.mk _ (h i)`. Establish `: (Ideal.quotientKerAlgEquivOfSurjective hf).symm (f (X i)) = Ideal.Quotient.mk _ (X i)`. Rewrite using `[AlgEquiv.symm_apply_eq]`. Both sides reduce to the same expression.

Express the relevant statement in the definitionally equal form `(Ideal.Quotient.liftₐ _ g₀ hg₀) ((Ideal.quotientKerAlgEquivOfSurjective hf).symm (f (X i))) = _`. Rewrite using `[this]`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk _ (aeval h (X i)) = _`. Rewrite using `[aeval_X]`. Establish `hfx : f (h i) = f (X i)`.

Use `h1 i` as an intermediate fact. Rewrite `this` using `[← hkerf, RingHom.mem_ker, map_sub, sub_eq_zero]`. Conclude with `this`. Simplify using `only [AlgHom.comp_apply, hgf, AlgHom.id_apply]`. Rewrite using `[AlgHom.kerSquareLift_mk, hfx]`.
-/
theorem formallySmooth_of_witness (Q : Algebra.Presentation T S ι σ) (h : ι → Q.Ring)
    (h1 : ∀ i, h i - X i ∈ Ideal.span (Set.range Q.relation))
    (h2 : ∀ j, aeval h (Q.relation j) ∈ Ideal.span (Set.range Q.relation) ^ 2) :
    Algebra.FormallySmooth T S := by
  let f : Q.Ring →ₐ[T] S := IsScalarTower.toAlgHom _ _ _
  have hf : Function.Surjective f := Q.algebraMap_surjective
  have hkerf : RingHom.ker f = Ideal.span (.range Q.relation) :=
    Q.span_range_relation_eq_ker.symm
  let g₀ : Q.Ring →ₐ[T] Q.Ring ⧸ RingHom.ker f.toRingHom ^ 2 :=
    (Ideal.Quotient.mkₐ T _).comp (aeval h)
  have hg₀ : ∀ a ∈ RingHom.ker f.toRingHom, g₀ a = 0 := by
    intro a ha
    have ha' : a ∈ Ideal.span (Set.range Q.relation) := hkerf ▸ ha
    have : Ideal.span (Set.range Q.relation) ≤ RingHom.ker g₀ := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      simp only [SetLike.mem_coe, RingHom.mem_ker]
      change Ideal.Quotient.mk _ _ = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      have := h2 j
      rw [← hkerf] at this
      exact this
    exact this ha'
  let g : S →ₐ[T] Q.Ring ⧸ RingHom.ker f.toRingHom ^ 2 :=
    (Ideal.Quotient.liftₐ (RingHom.ker f.toRingHom) g₀ hg₀).comp
      (Ideal.quotientKerAlgEquivOfSurjective hf).symm.toAlgHom
  refine Algebra.FormallySmooth.of_split f g ?_
  rw [← AlgHom.cancel_right hf]
  refine MvPolynomial.algHom_ext fun i ↦ ?_
  have hgf : g (f (X i)) = Ideal.Quotient.mk _ (h i) := by
    have : (Ideal.quotientKerAlgEquivOfSurjective hf).symm (f (X i)) = Ideal.Quotient.mk _ (X i) := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    change (Ideal.Quotient.liftₐ _ g₀ hg₀)
      ((Ideal.quotientKerAlgEquivOfSurjective hf).symm (f (X i))) = _
    rw [this]
    change Ideal.Quotient.mk _ (aeval h (X i)) = _
    rw [aeval_X]
  have hfx : f (h i) = f (X i) := by
    have := h1 i
    rw [← hkerf, RingHom.mem_ker, map_sub, sub_eq_zero] at this
    exact this
  simp only [AlgHom.comp_apply, hgf, AlgHom.id_apply]
  rw [AlgHom.kerSquareLift_mk, hfx]

end Witness

section Spread

variable {R₀ R B : Type} [CommRing R₀] [CommRing R] [CommRing B] [Algebra R₀ R] [Algebra R₀ B]

/- English proof (translation)
Rewrite using `[pow_two, Ideal.span_mul_span']`. Use `congr 1`. Use extensionality with `x`. Simplify using `only [Set.mem_mul, Set.mem_range, Prod.exists]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩`. Conclude with `⟨a, b, rfl⟩`. Introduce and unpack `⟨a, b, rfl⟩`. Conclude with `⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩`.
-/
theorem span_range_sq {P : Type} [CommRing P] {σ : Type} (g : σ → P) :
    Ideal.span (Set.range g) ^ 2 = Ideal.span (Set.range fun p : σ × σ ↦ g p.1 * g p.2) := by
  rw [pow_two, Ideal.span_mul_span']
  congr 1
  ext x
  simp only [Set.mem_mul, Set.mem_range, Prod.exists]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩
    exact ⟨a, b, rfl⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩

/- English proof (translation)
Set `P` to `Algebra.Presentation.ofFinitePresentation R₀ B`. Set `Q` to `P.baseChange R`. Take `⟨h, h1, h2⟩` from `exists_witness Q`. Rewrite `h2` using `[span_range_sq]`. Rewrite `h1`, `h2` using `[Ideal.mem_span_range_iff_exists_fun]`.

Use `choose c hc using h1`. Use `choose d hd using h2`. Use `⟨(⋃ i, ((h i).coeffs : Set R)) ∪ (⋃ i, ⋃ j, ((c i j).coeffs : Set R)) ∪ (⋃ i, ⋃ j, ((d i j).coeffs : Set R)), ?_, fun A hA ↦ ?_⟩` and prove the remaining obligations. Use `.union (.union ?_ ?_) ?_` and prove the remaining obligations. Conclude with `Set.finite_iUnion fun i ↦ Finset.finite_toSet _`.

Conclude with `Set.finite_iUnion fun i ↦ Set.finite_iUnion fun j ↦ Finset.finite_toSet _`. Conclude with `Set.finite_iUnion fun i ↦ Set.finite_iUnion fun j ↦ Finset.finite_toSet _`. Set `M {ι : Type} : MvPolynomial ι A →+* MvPolynomial ι R` to `MvPolynomial.map (algebraMap A R)`. Establish `hM {ι : Type} : Function.Injective (M (ι` using `ι)) := MvPolynomial.map_injective _ Subtype.val_injective`. Establish `hMX {ι : Type} (i : ι) : M (X i) = (X i : MvPolynomial ι R)` using `MvPolynomial.map_X _ _`.

Establish `lift {ι : Type} (p : MvPolynomial ι R) (hp : (p.coeffs : Set R) ⊆ A) : ∃ q, M q = p`. Use `MvPolynomial.mem_range_map_iff_coeffs_subset.mpr fun x hx ↦ ?_` and prove the remaining obligations. Conclude with `⟨⟨x, hp hx⟩, rfl⟩`. Establish `hh' (i) : ∃ q, M q = h i` using `lift _ fun x hx ↦ hA (.inl (.inl (Set.mem_iUnion.mpr ⟨i, hx⟩)))`. Establish `hc' (i j) : ∃ q, M q = c i j` using `lift _ fun x hx ↦ hA (.inl (.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, hx⟩⟩)))`.

Establish `hd' (i j) : ∃ q, M q = d i j` using `lift _ fun x hx ↦ hA (.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, hx⟩⟩))`. Use `choose h' hh' using hh'`. Use `choose c' hc' using hc'`. Use `choose d' hd' using hd'`. Set `Q'` to `P.baseChange A`.

Establish `hrel (j) : M (Q'.relation j) = Q.relation j`. Simplify using `[Q, Q', M, Algebra.Presentation.baseChange_relation, MvPolynomial.map_map, ← IsScalarTower.algebraMap_eq]`. Establish `: Algebra.FormallySmooth A (A ⊗[R₀] B)`. Use `formallySmooth_of_witness Q' h' (fun i ↦ ?_) (fun j ↦ ?_)` and prove the remaining obligations. Rewrite using `[Ideal.mem_span_range_iff_exists_fun]`.

Use `⟨c' i, hM ?_⟩` and prove the remaining obligations. Simplify using `only [map_sum, map_mul, map_sub, hc', hrel, hh', hMX]`. Conclude with `hc i`. Rewrite using `[span_range_sq, Ideal.mem_span_range_iff_exists_fun]`. Use `⟨d' j, hM ?_⟩` and prove the remaining obligations.

Establish `hMa (q : MvPolynomial _ A) : M (aeval h' q) = aeval h (M q)`. Proceed by induction on `q using MvPolynomial.induction_on with`. Consider the case `C a => simp [M, MvPolynomial.algebraMap_apply]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p i hp`.

Simplify using `only [map_mul, aeval_X, hp, hh', hMX]`. Simplify using `only [map_sum, map_mul, hd', hrel, hMa, hd j]`. Conclude with `⟨inferInstance, inferInstance⟩`.
-/
theorem exists_finite_smooth [Algebra.FinitePresentation R₀ B] [Algebra.Smooth R (R ⊗[R₀] B)] :
    ∃ s : Set R, s.Finite ∧ ∀ A : Subalgebra R₀ R, s ⊆ A → Algebra.Smooth A (A ⊗[R₀] B) := by
  classical
  let P := Algebra.Presentation.ofFinitePresentation R₀ B
  let Q := P.baseChange R
  obtain ⟨h, h1, h2⟩ := exists_witness Q
  simp_rw [span_range_sq] at h2
  simp_rw [Ideal.mem_span_range_iff_exists_fun] at h1 h2
  choose c hc using h1
  choose d hd using h2
  refine ⟨(⋃ i, ((h i).coeffs : Set R)) ∪ (⋃ i, ⋃ j, ((c i j).coeffs : Set R)) ∪
    (⋃ i, ⋃ j, ((d i j).coeffs : Set R)), ?_, fun A hA ↦ ?_⟩
  · refine .union (.union ?_ ?_) ?_
    · exact Set.finite_iUnion fun i ↦ Finset.finite_toSet _
    · exact Set.finite_iUnion fun i ↦ Set.finite_iUnion fun j ↦ Finset.finite_toSet _
    · exact Set.finite_iUnion fun i ↦ Set.finite_iUnion fun j ↦ Finset.finite_toSet _
  let M {ι : Type} : MvPolynomial ι A →+* MvPolynomial ι R := MvPolynomial.map (algebraMap A R)
  have hM {ι : Type} : Function.Injective (M (ι := ι)) :=
    MvPolynomial.map_injective _ Subtype.val_injective
  have hMX {ι : Type} (i : ι) : M (X i) = (X i : MvPolynomial ι R) := MvPolynomial.map_X _ _
  have lift {ι : Type} (p : MvPolynomial ι R) (hp : (p.coeffs : Set R) ⊆ A) : ∃ q, M q = p := by
    refine MvPolynomial.mem_range_map_iff_coeffs_subset.mpr fun x hx ↦ ?_
    exact ⟨⟨x, hp hx⟩, rfl⟩
  have hh' (i) : ∃ q, M q = h i := lift _ fun x hx ↦
    hA (.inl (.inl (Set.mem_iUnion.mpr ⟨i, hx⟩)))
  have hc' (i j) : ∃ q, M q = c i j := lift _ fun x hx ↦
    hA (.inl (.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, hx⟩⟩)))
  have hd' (i j) : ∃ q, M q = d i j := lift _ fun x hx ↦
    hA (.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, hx⟩⟩))
  choose h' hh' using hh'
  choose c' hc' using hc'
  choose d' hd' using hd'
  let Q' := P.baseChange A
  have hrel (j) : M (Q'.relation j) = Q.relation j := by
    simp [Q, Q', M, Algebra.Presentation.baseChange_relation, MvPolynomial.map_map,
      ← IsScalarTower.algebraMap_eq]
  have : Algebra.FormallySmooth A (A ⊗[R₀] B) := by
    refine formallySmooth_of_witness Q' h' (fun i ↦ ?_) (fun j ↦ ?_)
    · rw [Ideal.mem_span_range_iff_exists_fun]
      refine ⟨c' i, hM ?_⟩
      simp only [map_sum, map_mul, map_sub, hc', hrel, hh', hMX]
      exact hc i
    · rw [span_range_sq, Ideal.mem_span_range_iff_exists_fun]
      refine ⟨d' j, hM ?_⟩
      have hMa (q : MvPolynomial _ A) : M (aeval h' q) = aeval h (M q) := by
        induction q using MvPolynomial.induction_on with
        | C a => simp [M, MvPolynomial.algebraMap_apply]
        | add p q hp hq => simp only [map_add, hp, hq]
        | mul_X p i hp =>
          simp only [map_mul, aeval_X, hp, hh', hMX]
      simp only [map_sum, map_mul, hd', hrel, hMa, hd j]
  exact ⟨inferInstance, inferInstance⟩

end Spread

section Schemes

/- English proof (translation)
Establish `sq` using `(isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R₀ T B)).flip`. Establish `H' : IsPullback (p ≫ e.hom) q (Spec.map (CommRingCat.ofHom (algebraMap R₀ B))) (Spec.map (CommRingCat.ofHom (algebraMap R₀ T)))` using `H.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp [he]) (by simp)`. Establish `hq : (H'.isoIsPullback _ _ sq).hom ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : T →+* T ⊗[R₀] B)) = q` using `IsPullback.isoIsPullback_hom_snd ..`. Establish `: MorphismProperty.RespectsIso @Smooth.{0}` using `by first`. Consider the case `exact inferInstance`.

Consider the case `exact HasRingHomProperty.respectsIso`. Consider the case `exact MorphismProperty.IsStableUnderBaseChange.respectsIso`. Consider the case `exact (HasRingHomProperty.isLocal_ringHomProperty (P := @Smooth.{0})).respectsIso.arrow`. Rewrite using `[← hq, MorphismProperty.cancel_left_of_respectsIso (P := @Smooth.{0}), HasRingHomProperty.Spec_iff (P := @Smooth.{0})]`. Conclude with `RingHom.smooth_algebraMap (R := T) (S := T ⊗[R₀] B)`.
-/
theorem smooth_iff_of_isPullback {R₀ T B : Type} [CommRing R₀] [CommRing T] [CommRing B] [Algebra R₀ T]
    [Algebra R₀ B] {U W : Scheme.{0}} (g : U ⟶ Spec (CommRingCat.of R₀)) (e : U ≅ Spec (CommRingCat.of B))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R₀ B)) = g)
    {p : W ⟶ U} {q : W ⟶ Spec (CommRingCat.of T)}
    (H : IsPullback p q g (Spec.map (CommRingCat.ofHom (algebraMap R₀ T)))) :
    Smooth q ↔ Algebra.Smooth T (T ⊗[R₀] B) := by
  have sq := (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R₀ T B)).flip
  have H' : IsPullback (p ≫ e.hom) q (Spec.map (CommRingCat.ofHom (algebraMap R₀ B)))
      (Spec.map (CommRingCat.ofHom (algebraMap R₀ T))) :=
    H.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp [he]) (by simp)
  have hq : (H'.isoIsPullback _ _ sq).hom ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom : T →+* T ⊗[R₀] B)) = q :=
    IsPullback.isoIsPullback_hom_snd ..
  have : MorphismProperty.RespectsIso @Smooth.{0} := by
    first
      | exact inferInstance
      | exact HasRingHomProperty.respectsIso
      | exact MorphismProperty.IsStableUnderBaseChange.respectsIso
      | exact (HasRingHomProperty.isLocal_ringHomProperty (P := @Smooth.{0})).respectsIso.arrow
  rw [← hq, MorphismProperty.cancel_left_of_respectsIso (P := @Smooth.{0}), HasRingHomProperty.Spec_iff (P := @Smooth.{0})]
  exact RingHom.smooth_algebraMap (R := T) (S := T ⊗[R₀] B)

/- English proof (translation)
Set `B : Type` to `Γ(U, ⊤)`. Set `e : U ≅ Spec (CommRingCat.of B)` to `U.isoSpec`. Set `α : CommRingCat.of R₀ ⟶ CommRingCat.of B` to `Spec.preimage (e.inv ≫ j ≫ f₀)`. Establish `hα : Spec.map α = e.inv ≫ j ≫ f₀` using `Spec.map_preimage _`. Use `letI : Algebra R₀ B := α.hom.toAlgebra`.

Establish `hmap : Spec.map (CommRingCat.ofHom (algebraMap R₀ B)) = e.inv ≫ j ≫ f₀` using `hα`. Establish `he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R₀ B)) = j ≫ f₀`. Rewrite using `[hmap, Iso.hom_inv_id_assoc]`. Establish `hfp : Algebra.FinitePresentation R₀ B`. Establish `: LocallyOfFinitePresentation (Spec.map α)`.

Rewrite using `[hα]`. Use `infer_instance`. Rewrite `this` using `[HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation.{0})]`. Conclude with `this`. Establish `hsm : Algebra.Smooth R (R ⊗[R₀] B)`.

Use `(smooth_iff_of_isPullback (j ≫ f₀) e he ((IsPullback.of_hasPullback j π).paste_vert hpb)).mp ?_` and prove the remaining obligations. Use `infer_instance`. Take `⟨s, hs, H⟩` from `exists_finite_smooth (R₀ := R₀) (R := R) (B := B)`. Use `⟨s, hs, fun A hA W p q hW ↦ ?_⟩` and prove the remaining obligations. Use `H A hA` as an intermediate fact.

Conclude with `(smooth_iff_of_isPullback (j ≫ f₀) e he hW).mpr this`.
-/
theorem exists_finite_chart {R R₀ : Type} [CommRing R] [CommRing R₀] [Algebra R₀ R] {Y Y₀ U : Scheme.{0}}
    {f : Y ⟶ Spec (CommRingCat.of R)} {f₀ : Y₀ ⟶ Spec (CommRingCat.of R₀)} {π : Y ⟶ Y₀}
    (hlfp : LocallyOfFinitePresentation f₀)
    (hpb : IsPullback π f f₀ (Spec.map (CommRingCat.ofHom (algebraMap R₀ R))))
    (hf : Smooth f) [IsAffine U] (j : U ⟶ Y₀) [IsOpenImmersion j] :
    ∃ s : Set R, s.Finite ∧ ∀ (A : Subalgebra R₀ R), s ⊆ A → ∀ {W : Scheme.{0}} {p : W ⟶ U}
      {q : W ⟶ Spec (CommRingCat.of A)},
      IsPullback p q (j ≫ f₀) (Spec.map (CommRingCat.ofHom (algebraMap R₀ A))) → Smooth q := by
  let B : Type := Γ(U, ⊤)
  let e : U ≅ Spec (CommRingCat.of B) := U.isoSpec
  let α : CommRingCat.of R₀ ⟶ CommRingCat.of B := Spec.preimage (e.inv ≫ j ≫ f₀)
  have hα : Spec.map α = e.inv ≫ j ≫ f₀ := Spec.map_preimage _
  letI : Algebra R₀ B := α.hom.toAlgebra
  have hmap : Spec.map (CommRingCat.ofHom (algebraMap R₀ B)) = e.inv ≫ j ≫ f₀ := hα
  have he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R₀ B)) = j ≫ f₀ := by
    rw [hmap, Iso.hom_inv_id_assoc]
  have hfp : Algebra.FinitePresentation R₀ B := by
    have : LocallyOfFinitePresentation (Spec.map α) := by
      rw [hα]
      infer_instance
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation.{0})] at this
    exact this
  have hsm : Algebra.Smooth R (R ⊗[R₀] B) := by
    refine (smooth_iff_of_isPullback (j ≫ f₀) e he
      ((IsPullback.of_hasPullback j π).paste_vert hpb)).mp ?_
    infer_instance
  obtain ⟨s, hs, H⟩ := exists_finite_smooth (R₀ := R₀) (R := R) (B := B)
  refine ⟨s, hs, fun A hA W p q hW ↦ ?_⟩
  have := H A hA
  exact (smooth_iff_of_isPullback (j ≫ f₀) e he hW).mpr this

end Schemes

/- English proof (translation)
Introduce `R R₀ _ _ φ Y Y₀ f f₀ π ⟨hfg, hlfp, hqc, hqs, hpb⟩ hsm`. Use `letI : Algebra R₀ R := φ.toAlgebra`. Establish `: CompactSpace Y₀` using `QuasiCompact.compactSpace_of_compactSpace f₀`. Set `𝒰` to `Y₀.affineCover.finiteSubcover`. Establish `hch (i : 𝒰.I₀)` using `exists_finite_chart (R := R) (R₀ := R₀) hlfp hpb hsm (𝒰.f i)`.

Use `choose s hs H using hch`. Establish `: Finite 𝒰.I₀`. Express the relevant statement in the definitionally equal form `Finite Y₀.affineCover.finiteSubcover.I₀`. Use `infer_instance`. Set `A : Subalgebra R₀ R` to `Algebra.adjoin R₀ (⋃ i, s i)`.

Establish `hAfg : A.FG` using `⟨(Set.finite_iUnion hs).toFinset, by simp [A]⟩`. Establish `hft : Algebra.FiniteType R₀ A` using `(Subalgebra.fg_iff_finiteType A).mp hAfg`. Use `⟨A, inferInstance, algebraMap R₀ A, algebraMap A R, rfl, Algebra.FiniteType.trans hfg hft, ?_⟩` and prove the remaining obligations. Establish `hloc : IsZariskiLocalAtSource @Smooth.{0}` using `HasRingHomProperty.instIsZariskiLocalAtSource`. Use `IsZariskiLocalAtSource.of_openCover (P := @Smooth.{0}) (𝒰.pullback₁ (pullback.fst f₀ (Spec.map (CommRingCat.ofHom (algebraMap R₀ A))))) fun i ↦ ?_` and prove the remaining obligations.

Conclude with `H i A (fun x hx ↦ Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨i, hx⟩)) ((IsPullback.of_hasPullback _ (𝒰.f i)).flip.paste_vert (IsPullback.of_hasPullback _ _))`.
-/
theorem smooth_spreads : GlobalTheory.SpreadingModels.Spreads (fun _ _ f ↦ Smooth f) := by
  intro R R₀ _ _ φ Y Y₀ f f₀ π ⟨hfg, hlfp, hqc, hqs, hpb⟩ hsm
  letI : Algebra R₀ R := φ.toAlgebra
  have : CompactSpace Y₀ := QuasiCompact.compactSpace_of_compactSpace f₀
  let 𝒰 := Y₀.affineCover.finiteSubcover
  have hch (i : 𝒰.I₀) := exists_finite_chart (R := R) (R₀ := R₀) hlfp hpb hsm (𝒰.f i)
  choose s hs H using hch
  have : Finite 𝒰.I₀ := by
    change Finite Y₀.affineCover.finiteSubcover.I₀
    infer_instance
  let A : Subalgebra R₀ R := Algebra.adjoin R₀ (⋃ i, s i)
  have hAfg : A.FG := ⟨(Set.finite_iUnion hs).toFinset, by simp [A]⟩
  have hft : Algebra.FiniteType R₀ A := (Subalgebra.fg_iff_finiteType A).mp hAfg
  refine ⟨A, inferInstance, algebraMap R₀ A, algebraMap A R, rfl, Algebra.FiniteType.trans hfg hft, ?_⟩
  have hloc : IsZariskiLocalAtSource @Smooth.{0} := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_openCover (P := @Smooth.{0})
    (𝒰.pullback₁ (pullback.fst f₀ (Spec.map (CommRingCat.ofHom (algebraMap R₀ A))))) fun i ↦ ?_
  exact H i A (fun x hx ↦ Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨i, hx⟩))
    ((IsPullback.of_hasPullback _ (𝒰.f i)).flip.paste_vert (IsPullback.of_hasPullback _ _))

end GlobalTheory.CompanionTheory.SmoothSpread
