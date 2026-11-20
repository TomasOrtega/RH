import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGoodModelOfIsogeny
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrdegEqOfLocallyIsStandardSmoothOfRelativeDimens
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocallyQuasiFiniteOfIsPullbackSurjective

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory

namespace SurjIsogeny

/- English proof (translation)
Use `algebraize [φ]`. Establish `: IsScalarTower K R S` using `IsScalarTower.of_algebraMap_eq' hφ.symm`. Establish `: FaithfulSMul R S`. Rewrite using `[faithfulSMul_iff_algebraMap_injective, RingHom.injective_iff_ker_eq_bot, eq_bot_iff, ← hp]`. Conclude with `Ideal.comap_mono bot_le`.

Establish `h` using `trdeg_add_eq K R (A := S)`. Rewrite `h` using `[hR, hS]`. Establish `h0 : Algebra.trdeg R S = 0`. Establish `h1 : Algebra.trdeg R S + g = 0 + g` using `by rw [add_comm, h, zero_add]`. Conclude with `(Cardinal.add_right_inj_of_lt_aleph0 Cardinal.natCast_lt_aleph0).1 h1`.

Establish `halg` using `trdeg_eq_zero_iff.1 h0`. Assume the negation of the conclusion as `hne`. Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hne`. Conclude with `Ideal.comap_ne_bot_of_algebraic_mem hx0 hx (halg.1 x) hp`.
-/
theorem eq_bot_of_comap_eq_bot {K R S : Type} [Field K] [CommRing R] [CommRing S] [IsDomain R]
    [IsDomain S] [Algebra K R] [Algebra K S] (φ : R →+* S)
    (hφ : φ.comp (algebraMap K R) = algebraMap K S) {g : ℕ}
    (hR : Algebra.trdeg K R = g) (hS : Algebra.trdeg K S = g) {p : Ideal S}
    (hp : p.comap φ = ⊥) : p = ⊥ := by
  algebraize [φ]
  have : IsScalarTower K R S := IsScalarTower.of_algebraMap_eq' hφ.symm
  have : FaithfulSMul R S := by
    rw [faithfulSMul_iff_algebraMap_injective, RingHom.injective_iff_ker_eq_bot, eq_bot_iff, ← hp]
    exact Ideal.comap_mono bot_le
  have h := trdeg_add_eq K R (A := S)
  rw [hR, hS] at h
  have h0 : Algebra.trdeg R S = 0 := by
    have h1 : Algebra.trdeg R S + g = 0 + g := by rw [add_comm, h, zero_add]
    exact (Cardinal.add_right_inj_of_lt_aleph0 Cardinal.natCast_lt_aleph0).1 h1
  have halg := trdeg_eq_zero_iff.1 h0
  by_contra hne
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact Ideal.comap_ne_bot_of_algebraic_mem hx0 hx (halg.1 x) hp

/- English proof (translation)
Rewrite using `[← genericPoint_eq_of_isOpenImmersion j, j.isOpenEmbedding.injective.eq_iff, genericPoint_eq_bot_of_affine]`. Conclude with `⟨fun h => h ▸ rfl, fun h => PrimeSpectrum.ext h⟩`.
-/
theorem eq_genericPoint_iff {X : Scheme.{0}} [IsIntegral X] {R : CommRingCat.{0}} [IsDomain R]
    (j : Spec R ⟶ X) [IsOpenImmersion j] (p : Spec R) :
    j p = genericPoint X ↔ p.asIdeal = ⊥ := by
  rw [← genericPoint_eq_of_isOpenImmersion j, j.isOpenEmbedding.injective.eq_iff,
    genericPoint_eq_bot_of_affine]
  exact ⟨fun h => h ▸ rfl, fun h => PrimeSpectrum.ext h⟩

/- English proof (translation)
Take `⟨R, j, hj, y, hy⟩` from `Scheme.exists_Spec_apply_eq (f x)`. Take `⟨S, k, hk, ⟨p, rfl⟩, hsub⟩` from `Scheme.exists_affine_mem_range_and_range_subset (x := x) (U := f ⁻¹ᵁ j.opensRange) ⟨y, hy⟩`. Establish `hr : Set.range (k ≫ f) ⊆ Set.range j`. Introduce and unpack `_ ⟨z, rfl⟩`. Conclude with `hsub ⟨z, rfl⟩`.

Take `⟨φ, hφ⟩` from `Spec.map_surjective (IsOpenImmersion.lift j (k ≫ f) hr)`. Establish `hw : Spec.map φ ≫ j = k ≫ f` using `by rw [hφ, IsOpenImmersion.lift_fac]`. Take `⟨α, hα⟩` from `Spec.map_surjective (j ≫ s)`. Establish `: Nonempty (Spec R)` using `⟨y⟩`. Establish `: Nonempty (Spec S)` using `⟨p⟩`.

Establish `: IsIntegral (Spec R)` using `isIntegral_of_isOpenImmersion j`. Establish `: IsIntegral (Spec S)` using `isIntegral_of_isOpenImmersion k`. Establish `: IsDomain R` using `(affine_isIntegral_iff R).1 inferInstance`. Establish `: IsDomain S` using `(affine_isIntegral_iff S).1 inferInstance`. Use `letI : Algebra K R := α.hom.toAlgebra`.

Use `letI : Algebra K S := (α ≫ φ).hom.toAlgebra`. Establish `hR` using `trdeg_eq_of_smoothOfRelativeDimension K Y s g hY R j hj hα.symm`. Establish `hS` using `trdeg_eq_of_smoothOfRelativeDimension K X (f ≫ s) g hX S k hk (by`. Rewrite using `[← reassoc_of% hw, ← hα, ← Spec.map_comp]`. Use the proof step `rfl)`.

Rewrite using `[eq_genericPoint_iff]`. Use `eq_bot_of_comap_eq_bot φ.hom rfl hR hS ?_` and prove the remaining obligations. Use `(eq_genericPoint_iff j (Spec.map φ p)).1 ?_` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply, hx]`.
-/
theorem eq_genericPoint_of_apply_eq {K : Type} [Field K] {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) (s : Y ⟶ Spec (CommRingCat.of K)) {g : ℕ}
    (hY : SmoothOfRelativeDimension g s) (hX : SmoothOfRelativeDimension g (f ≫ s)) {x : X}
    (hx : f x = genericPoint Y) : x = genericPoint X := by
  obtain ⟨R, j, hj, y, hy⟩ := Scheme.exists_Spec_apply_eq (f x)
  obtain ⟨S, k, hk, ⟨p, rfl⟩, hsub⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := x) (U := f ⁻¹ᵁ j.opensRange) ⟨y, hy⟩
  have hr : Set.range (k ≫ f) ⊆ Set.range j := by
    rintro _ ⟨z, rfl⟩
    exact hsub ⟨z, rfl⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift j (k ≫ f) hr)
  have hw : Spec.map φ ≫ j = k ≫ f := by rw [hφ, IsOpenImmersion.lift_fac]
  obtain ⟨α, hα⟩ := Spec.map_surjective (j ≫ s)
  have : Nonempty (Spec R) := ⟨y⟩
  have : Nonempty (Spec S) := ⟨p⟩
  have : IsIntegral (Spec R) := isIntegral_of_isOpenImmersion j
  have : IsIntegral (Spec S) := isIntegral_of_isOpenImmersion k
  have : IsDomain R := (affine_isIntegral_iff R).1 inferInstance
  have : IsDomain S := (affine_isIntegral_iff S).1 inferInstance
  letI : Algebra K R := α.hom.toAlgebra
  letI : Algebra K S := (α ≫ φ).hom.toAlgebra
  have hR := trdeg_eq_of_smoothOfRelativeDimension K Y s g hY R j hj hα.symm
  have hS := trdeg_eq_of_smoothOfRelativeDimension K X (f ≫ s) g hX S k hk (by
    rw [← reassoc_of% hw, ← hα, ← Spec.map_comp]; rfl)
  rw [eq_genericPoint_iff]
  refine eq_bot_of_comap_eq_bot φ.hom rfl hR hS ?_
  refine (eq_genericPoint_iff j (Spec.map φ p)).1 ?_
  rw [← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply, hx]

/- English proof (translation)
Establish `hi : i ≫ ψ = 1` using `hp.w`. Use `⟨⟨?_⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => lift (hp.lift (s.fst * s.snd⁻¹) (toUnit _) ?_) s.snd) (fun s => ?_) (fun s => ?_) (fun s m h1 h2 => ?_)⟩⟩` and prove the remaining obligations. Rewrite using `[MonObj.mul_comp, Category.assoc, hi, MonObj.comp_one, _root_.one_mul]`. Rewrite using `[MonObj.mul_comp, GrpObj.inv_comp, s.condition, mul_inv_cancel, Hom.one_def]`. Rewrite using `[MonObj.comp_mul, lift_fst_assoc, hp.lift_fst, lift_snd, inv_mul_cancel_right]`.

Conclude with `lift_snd _ _`. Use `CartesianMonoidalCategory.hom_ext _ _ ?_ (by rw [lift_snd, h2])` and prove the remaining obligations. Use `hp.hom_ext ?_ (toUnit_unique _ _)` and prove the remaining obligations. Rewrite using `[lift_fst, hp.lift_fst, ← h1, ← h2, MonObj.comp_mul, mul_inv_cancel_right, Category.assoc]`.
-/
theorem isPullback_kernel_mul {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {Z A B : C} [GrpObj A] [GrpObj B] {i : Z ⟶ A} {ψ : A ⟶ B} [IsMonHom ψ]
    (hp : IsPullback i (toUnit Z) ψ η[B]) :
    IsPullback ((fst Z A ≫ i) * snd Z A) (snd Z A) ψ ψ := by
  have hi : i ≫ ψ = 1 := hp.w
  refine ⟨⟨?_⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => lift (hp.lift (s.fst * s.snd⁻¹) (toUnit _) ?_) s.snd) (fun s => ?_) (fun s => ?_)
    (fun s m h1 h2 => ?_)⟩⟩
  · rw [MonObj.mul_comp, Category.assoc, hi, MonObj.comp_one, _root_.one_mul]
  · rw [MonObj.mul_comp, GrpObj.inv_comp, s.condition, mul_inv_cancel, Hom.one_def]
  · rw [MonObj.comp_mul, lift_fst_assoc, hp.lift_fst, lift_snd, inv_mul_cancel_right]
  · exact lift_snd _ _
  · refine CartesianMonoidalCategory.hom_ext _ _ ?_ (by rw [lift_snd, h2])
    refine hp.hom_ext ?_ (toUnit_unique _ _)
    rw [lift_fst, hp.lift_fst, ← h1, ← h2, MonObj.comp_mul, mul_inv_cancel_right, Category.assoc]

/- English proof (translation)
Establish `hp : IsPullback (pullback.fst ψ η[B]) (toUnit _) ψ η[B]`. Use `IsPullback.of_hasPullback ψ η[B]` as an intermediate fact. Rewrite `this` using `[toUnit_unique (pullback.snd ψ η[B]) (toUnit _)]`. Then use the resulting hypothesis. Generalize the expression as in `pullback.fst ψ η[B] = i at hp`. Generalize the expression as in `pullback ψ η[B] = Z at i hp`.

Establish `hl` using `hp.map (Over.forget S)`. Establish `hZ1 : LocallyOfFiniteType Z.hom`. Simplify using `using MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hl ‹_›`. Establish `hZ2 : QuasiCompact Z.hom`. Simplify using `using MorphismProperty.of_isPullback (P := @QuasiCompact) hl ‹_›`.

Establish `h1 : IsPullback ((fst Z A ≫ i) * snd Z A).left (pullback.snd Z.hom A.hom) ψ.left ψ.left` using `(isPullback_kernel_mul hp).map (Over.forget S)`. Set `j` to `A.left.fromSpecResidueField a`. Establish `h2` using `IsPullback.of_hasPullback (pullback.snd Z.hom A.hom) j`. Establish `h3` using `h2.paste_horiz h1`. Establish `h4` using `h2.paste_horiz (IsPullback.of_hasPullback Z.hom A.hom)`.

Establish `hF : LocallyQuasiFinite (ψ.left.fiberToSpecResidueField (ψ.left a))`. Establish `: Finite (ψ.left.fiber (ψ.left a))` using `(ψ.left.fiberHomeo (ψ.left a)).toEquiv.finite_iff.2 h.to_subtype`. Establish `: LocallyOfFiniteType (ψ.left.fiberToSpecResidueField (ψ.left a))` using `inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))`. Conclude with `LocallyQuasiFinite.of_finite_preimage_singleton _ fun _ => Set.toFinite _`. Rewrite `h3` using `[← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]`.

Establish `h5` using `h3.of_right' (IsPullback.of_hasPullback ψ.left (B.left.fromSpecResidueField (ψ.left a)))`. Establish `h6 : LocallyQuasiFinite (pullback.snd (pullback.snd Z.hom A.hom) j)` using `MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) h5 hF`. Establish `h7 : LocallyQuasiFinite Z.hom` using `Unif.locallyQuasiFinite_of_isPullback_surjective _ _ _ _ _ _ _ _ h4 ⟨fun _ => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩ hZ1 hZ2 h6`. Conclude with `Unif.locallyQuasiFinite_of_isPullback_surjective _ _ _ _ _ _ _ _ h1 ‹_› ‹_› ‹_› inferInstance`.
-/
theorem locallyQuasiFinite_of_finite_fibre {S : Scheme.{0}} [Subsingleton S] {A B : Over S}
    [GrpObj A] [GrpObj B] (ψ : A ⟶ B) [IsMonHom ψ] [Surjective ψ.left]
    [LocallyOfFiniteType ψ.left] [QuasiCompact ψ.left] (a : A.left)
    (h : (ψ.left ⁻¹' {ψ.left a}).Finite) : LocallyQuasiFinite ψ.left := by
  have hp : IsPullback (pullback.fst ψ η[B]) (toUnit _) ψ η[B] := by
    have := IsPullback.of_hasPullback ψ η[B]
    rwa [toUnit_unique (pullback.snd ψ η[B]) (toUnit _)] at this
  generalize pullback.fst ψ η[B] = i at hp
  generalize pullback ψ η[B] = Z at i hp
  have hl := hp.map (Over.forget S)
  have hZ1 : LocallyOfFiniteType Z.hom := by
    simpa using MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hl ‹_›
  have hZ2 : QuasiCompact Z.hom := by
    simpa using MorphismProperty.of_isPullback (P := @QuasiCompact) hl ‹_›
  have h1 : IsPullback ((fst Z A ≫ i) * snd Z A).left (pullback.snd Z.hom A.hom) ψ.left ψ.left :=
    (isPullback_kernel_mul hp).map (Over.forget S)
  let j := A.left.fromSpecResidueField a
  have h2 := IsPullback.of_hasPullback (pullback.snd Z.hom A.hom) j
  have h3 := h2.paste_horiz h1
  have h4 := h2.paste_horiz (IsPullback.of_hasPullback Z.hom A.hom)
  have hF : LocallyQuasiFinite (ψ.left.fiberToSpecResidueField (ψ.left a)) := by
    have : Finite (ψ.left.fiber (ψ.left a)) :=
      (ψ.left.fiberHomeo (ψ.left a)).toEquiv.finite_iff.2 h.to_subtype
    have : LocallyOfFiniteType (ψ.left.fiberToSpecResidueField (ψ.left a)) :=
      inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
    exact LocallyQuasiFinite.of_finite_preimage_singleton _ fun _ => Set.toFinite _
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField] at h3
  have h5 := h3.of_right' (IsPullback.of_hasPullback ψ.left
    (B.left.fromSpecResidueField (ψ.left a)))
  have h6 : LocallyQuasiFinite (pullback.snd (pullback.snd Z.hom A.hom) j) :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) h5 hF
  have h7 : LocallyQuasiFinite Z.hom :=
    Unif.locallyQuasiFinite_of_isPullback_surjective _ _ _ _ _ _ _ _ h4
      ⟨fun _ => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩ hZ1 hZ2 h6
  exact Unif.locallyQuasiFinite_of_isPullback_surjective _ _ _ _ _ _ _ _ h1 ‹_› ‹_› ‹_›
    inferInstance

end SurjIsogeny

open SurjIsogeny IsogenyModel in

/- English proof (translation)
Introduce `hL K _ P B _ ψ hB hg _ _`. Use `hB.proper` as an intermediate fact. Use `P.isAb.proper` as an intermediate fact. Use `P.isAb.comm` as an intermediate fact. Use `forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ B.hom hB.smooth hB.geomConnected` as an intermediate fact.

Establish `: IsIntegral B.left` using `GeometricallyIntegral.isIntegral_of_subsingleton B.hom`. Use `forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ P.A.hom P.isAb.smooth P.isAb.geomConnected` as an intermediate fact. Establish `: IsIntegral P.A.left` using `GeometricallyIntegral.isIntegral_of_subsingleton P.A.hom`. Establish `: IsProper (ψ.left ≫ B.hom)` using `by rw [Over.w]; infer_instance`. Establish `: IsProper ψ.left` using `IsProper.of_comp ψ.left B.hom`.

Establish `hA : SmoothOfRelativeDimension P.g (ψ.left ≫ B.hom)` using `by rw [Over.w]; exact P.smoothDim`. Take `⟨a, ha⟩` from `ψ.left.surjective (genericPoint B.left)`. Establish `: LocallyQuasiFinite ψ.left`. Use `locallyQuasiFinite_of_finite_fibre ψ a ((Set.finite_singleton (genericPoint _)).subset ?_)` and prove the remaining obligations. Introduce `x hx`.

Conclude with `eq_genericPoint_of_apply_eq ψ.left B.hom hg hA (ha ▸ hx)`. Establish `hf : IsFinite ψ.left` using `.of_isProper_of_locallyQuasiFinite _`. Take `⟨Z, _, i, _, hi, hZ, hk⟩` from `exists_kernel ψ`. Establish `hm : Mono i` using `(Over.forget _).mono_of_mono_map (inferInstanceAs (Mono i.left))`. Use `isCommMonObj_of_mono i` as an intermediate fact.

Take `⟨N, hN, hZN⟩` from `FiniteFlatKilled.main K Z hZ inferInstance`. Take `⟨A, _, hA', q, _, _, _, _, hq⟩` from `hL.quotient K P Z i ‹_› hm hZ inferInstance`. Use `hA'.proper` as an intermediate fact. Take `⟨e, -, he⟩` from `exists_iso_of_same_kernel q ψ i hq hk`. Use `⟨hf, ?_, N, hN, fun T x hx => ?_⟩` and prove the remaining obligations.

Establish `: IsIso e.hom.left` using `inferInstanceAs (IsIso ((Over.forget _).map e.hom))`. Rewrite using `[← he, Over.comp_left]`. Use `infer_instance`. Establish `h1 : i ^ N = 1`. Rewrite using `[← Category.id_comp i, ← MonObj.pow_comp, hZN, MonObj.one_comp]`.

Rewrite using `[← hk.lift_fst x (toUnit _) hx, ← MonObj.comp_pow, h1, MonObj.comp_one]`.
-/
theorem isogeny_of_surjective_of_dim_eq : Out.Laws → ∀ (K : Type) [Field K] (P : Out.PolAV (Sp K)) (B : Over (Sp K)) [GrpObj B] (ψ : P.A ⟶ B), IsAbelianScheme B → SmoothOfRelativeDimension P.g B.hom → IsMonHom ψ → Surjective ψ.left → IsFinite ψ.left ∧ Flat ψ.left ∧ ∃ n : ℕ, 1 ≤ n ∧ ∀ (T : Over (Sp K)) (x : T ⟶ P.A), x ≫ ψ = 1 → x ^ n = 1 := by
  intro hL K _ P B _ ψ hB hg _ _
  have := hB.proper
  have := P.isAb.proper
  have := P.isAb.comm
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ B.hom hB.smooth
    hB.geomConnected
  have : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_subsingleton B.hom
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ P.A.hom
    P.isAb.smooth P.isAb.geomConnected
  have : IsIntegral P.A.left := GeometricallyIntegral.isIntegral_of_subsingleton P.A.hom
  have : IsProper (ψ.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : IsProper ψ.left := IsProper.of_comp ψ.left B.hom
  have hA : SmoothOfRelativeDimension P.g (ψ.left ≫ B.hom) := by rw [Over.w]; exact P.smoothDim
  obtain ⟨a, ha⟩ := ψ.left.surjective (genericPoint B.left)
  have : LocallyQuasiFinite ψ.left := by
    refine locallyQuasiFinite_of_finite_fibre ψ a ((Set.finite_singleton (genericPoint _)).subset ?_)
    intro x hx
    exact eq_genericPoint_of_apply_eq ψ.left B.hom hg hA (ha ▸ hx)
  have hf : IsFinite ψ.left := .of_isProper_of_locallyQuasiFinite _
  obtain ⟨Z, _, i, _, hi, hZ, hk⟩ := exists_kernel ψ
  have hm : Mono i := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono i.left))
  have := isCommMonObj_of_mono i
  obtain ⟨N, hN, hZN⟩ := FiniteFlatKilled.main K Z hZ inferInstance
  obtain ⟨A, _, hA', q, _, _, _, _, hq⟩ := hL.quotient K P Z i ‹_› hm hZ inferInstance
  have := hA'.proper
  obtain ⟨e, -, he⟩ := exists_iso_of_same_kernel q ψ i hq hk
  refine ⟨hf, ?_, N, hN, fun T x hx => ?_⟩
  · have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
    rw [← he, Over.comp_left]
    infer_instance
  · have h1 : i ^ N = 1 := by
      rw [← Category.id_comp i, ← MonObj.pow_comp, hZN, MonObj.one_comp]
    rw [← hk.lift_fst x (toUnit _) hx, ← MonObj.comp_pow, h1, MonObj.comp_one]

/- English proof (translation)
Introduce `_ hL K _ _ P P' ψ hg` and use `isogeny_of_surjective_of_dim_eq hL K P P'.A ψ P'.isAb (hg ▸ P'.smoothDim)`.
-/
theorem isogeny_of_surjective_polAV : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] (σ : K →+* ℂ) (P P' : Out.PolAV (Sp K)) (ψ : P.A ⟶ P'.A), P.g = P'.g → IsMonHom ψ → Surjective ψ.left → IsFinite ψ.left ∧ Flat ψ.left ∧ ∃ n : ℕ, 1 ≤ n ∧ ∀ (T : Over (Sp K)) (x : T ⟶ P.A), x ≫ ψ = 1 → x ^ n = 1 :=
  fun _ hL K _ _ P P' ψ hg => isogeny_of_surjective_of_dim_eq hL K P P'.A ψ P'.isAb
    (hg ▸ P'.smoothDim)

end GlobalTheory
