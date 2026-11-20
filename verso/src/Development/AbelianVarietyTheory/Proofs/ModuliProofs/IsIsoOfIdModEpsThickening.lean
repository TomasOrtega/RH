import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KerAppEqMapAppLEOfIsPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.EpsIso

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[RingHom.mem_ker, Ideal.mem_span_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `h0 : x.fst = 0` using `hx`.

Use `⟨TrivSqZeroExt.inl x.snd, ?_⟩` and prove the remaining obligations. Use `ext`. Simplify using `[h0]`. Simplify using the standard rewrite rules. Introduce and unpack `⟨y, rfl⟩ show (DualNumber.eps * y).fst = 0`.

Simplify using the standard rewrite rules.
-/
theorem ker_fst_eq_span (K : Type) [Field K] :
    RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom =
      Ideal.span {(DualNumber.eps : DualNumber K)} := by
  ext x
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  constructor
  · intro hx
    have h0 : x.fst = 0 := hx
    refine ⟨TrivSqZeroExt.inl x.snd, ?_⟩
    ext
    · simp [h0]
    · simp
  · rintro ⟨y, rfl⟩
    show (DualNumber.eps * y).fst = 0
    simp

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Set `_ : Algebra (DualNumber K) C` to `a.toAlgebra`. Establish `_ : Module.Flat (DualNumber K) C` using `ha`. Establish `hsum : ∑ _i : Unit, (DualNumber.eps : DualNumber K) • c = 0`. Rewrite using `[Fintype.sum_unique, Algebra.smul_def, RingHom.algebraMap_toAlgebra]`. Conclude with `hc`.

Take `⟨k, b, y, hy, hb⟩` from `Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := DualNumber K) (M := C) (f := fun _ : Unit => (DualNumber.eps : DualNumber K)) (x := fun _ => c) hsum`. Establish `hkill : ∀ i, b () i = DualNumber.eps * TrivSqZeroExt.inl (b () i).snd`. Introduce `i`. Establish `h1 : DualNumber.eps * b () i = 0`. Establish `h0` using `hb i`.

Rewrite `h0` using `[Fintype.sum_unique]`. Then use the resulting hypothesis. Establish `h2 : (b () i).fst = 0`. Establish `h3` using `congrArg TrivSqZeroExt.snd h1`. Rewrite `h3` using `[DualNumber.snd_mul, DualNumber.fst_eps, DualNumber.snd_eps, zero_mul, _root_.one_mul, zero_add, TrivSqZeroExt.snd_zero]`. Conclude with `h3`.

Use `TrivSqZeroExt.ext ?_ ?_` and prove the remaining obligations. Rewrite using `[TrivSqZeroExt.fst_mul, DualNumber.fst_eps, zero_mul, h2]`. Rewrite using `[DualNumber.snd_mul, DualNumber.fst_eps, DualNumber.snd_eps, zero_mul, zero_add, _root_.one_mul, TrivSqZeroExt.fst_inl]`. Use `⟨∑ i, a (TrivSqZeroExt.inl (b () i).snd) * y i, ?_⟩` and prove the remaining obligations. Rewrite using `[show c = ∑ j, b () j • y j from hy (), Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `hki` using `hkill i`. Rewrite using `[Algebra.smul_def, RingHom.algebraMap_toAlgebra]`. Use `conv_lhs => rw [hki]`. Rewrite using `[map_mul, _root_.mul_assoc]`.
-/
private theorem exists_eq_eps_mul_of_flat_of_eps_mul_eq_zero {K : Type} [Field K] {C : Type} [CommRing C] (a : DualNumber K →+* C)
    (ha : a.Flat) (c : C) (hc : a DualNumber.eps * c = 0) :
    ∃ d : C, c = a DualNumber.eps * d := by
  let _ : Algebra (DualNumber K) C := a.toAlgebra
  have _ : Module.Flat (DualNumber K) C := ha
  have hsum : ∑ _i : Unit, (DualNumber.eps : DualNumber K) • c = 0 := by
    rw [Fintype.sum_unique, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    exact hc
  obtain ⟨k, b, y, hy, hb⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := DualNumber K) (M := C)
    (f := fun _ : Unit => (DualNumber.eps : DualNumber K)) (x := fun _ => c) hsum
  have hkill : ∀ i, b () i = DualNumber.eps * TrivSqZeroExt.inl (b () i).snd := by
    intro i
    have h1 : DualNumber.eps * b () i = 0 := by
      have h0 := hb i
      rwa [Fintype.sum_unique] at h0
    have h2 : (b () i).fst = 0 := by
      have h3 := congrArg TrivSqZeroExt.snd h1
      rw [DualNumber.snd_mul, DualNumber.fst_eps, DualNumber.snd_eps, zero_mul, _root_.one_mul, zero_add,
        TrivSqZeroExt.snd_zero] at h3
      exact h3
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [TrivSqZeroExt.fst_mul, DualNumber.fst_eps, zero_mul, h2]
    · rw [DualNumber.snd_mul, DualNumber.fst_eps, DualNumber.snd_eps, zero_mul, zero_add, _root_.one_mul,
        TrivSqZeroExt.fst_inl]
  refine ⟨∑ i, a (TrivSqZeroExt.inl (b () i).snd) * y i, ?_⟩
  rw [show c = ∑ j, b () j • y j from hy (), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hki := hkill i
  rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  conv_lhs => rw [hki]
  rw [map_mul, _root_.mul_assoc]

/- English proof (translation)
Rewrite using `[Ideal.mem_span_singleton]`. Conclude with `exists_eq_eps_mul_of_flat_of_eps_mul_eq_zero a ha c hc`.
-/
theorem mem_span_of_flat {K : Type} [Field K] {C : Type} [CommRing C] (a : DualNumber K →+* C)
    (ha : a.Flat) (c : C) (hc : a DualNumber.eps * c = 0) :
    c ∈ Ideal.span {a DualNumber.eps} := by
  rw [Ideal.mem_span_singleton]
  exact exists_eq_eps_mul_of_flat_of_eps_mul_eq_zero a ha c hc

/- English proof (translation)
Establish `hee : a DualNumber.eps * a DualNumber.eps = 0`. Rewrite using `[← map_mul, DualNumber.eps_mul_eps, map_zero]`. Establish `hk : jC (φ (a DualNumber.eps)) = 0`. Rewrite using `[← RingHom.mem_ker, hC]`. Conclude with `Ideal.mem_span_singleton_self _`.

Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `b hb`. Establish `h1 : b ∈ RingHom.ker jB` using `by rw [RingHom.mem_ker, ← hφ, hb, map_zero]`. Rewrite `h1` using `[hB, Ideal.mem_span_singleton]`.

Take `⟨b1, rfl⟩` from `h1`. Establish `h2 : (φ.comp a) DualNumber.eps * φ b1 = 0`. Rewrite using `[RingHom.comp_apply, ← map_mul]`. Conclude with `hb`. Establish `h3` using `mem_span_of_flat (φ.comp a) hfl (φ b1) h2`.

Rewrite `h3` using `[Ideal.mem_span_singleton]`. Take `⟨c', hc'⟩` from `h3`. Establish `h4 : b1 ∈ RingHom.ker jB`. Rewrite using `[RingHom.mem_ker, ← hφ, hc', map_mul, RingHom.comp_apply, hk, zero_mul]`. Rewrite `h4` using `[hB, Ideal.mem_span_singleton]`.

Take `⟨b2, rfl⟩` from `h4`. Rewrite using `[← _root_.mul_assoc, hee, zero_mul]`. Introduce `c`. Take `⟨b, hb⟩` from `hs (jC c)`. Establish `h1 : c - φ b ∈ RingHom.ker jC` using `by rw [RingHom.mem_ker, map_sub, hφ, hb, sub_self]`.

Rewrite `h1` using `[hC, Ideal.mem_span_singleton]`. Take `⟨c1, hc1⟩` from `h1`. Take `⟨b1, hb1⟩` from `hs (jC c1)`. Establish `h2 : c1 - φ b1 ∈ RingHom.ker jC` using `by rw [RingHom.mem_ker, map_sub, hφ, hb1, sub_self]`. Rewrite `h2` using `[hC, Ideal.mem_span_singleton]`.

Take `⟨c2, hc2⟩` from `h2`. Establish `hφe : φ (a DualNumber.eps) * φ (a DualNumber.eps) = 0`. Rewrite using `[← map_mul, hee, map_zero]`. Use `⟨b + a DualNumber.eps * b1, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_mul]`.

Take the linear combination `(-1 : C) * hc1 - φ (a DualNumber.eps) * hc2 - c2 * hφe`.
-/
theorem bijective_of_mod_eps {K : Type} [Field K] {B C D : Type} [CommRing B] [CommRing C]
    [CommRing D] (a : DualNumber K →+* B) (φ : B →+* C) (jB : B →+* D) (jC : C →+* D)
    (hφ : ∀ b, jC (φ b) = jB b) (hs : Function.Surjective jB) (hfl : (φ.comp a).Flat)
    (hB : RingHom.ker jB = Ideal.span {a DualNumber.eps})
    (hC : RingHom.ker jC = Ideal.span {φ (a DualNumber.eps)}) : Function.Bijective φ := by
  have hee : a DualNumber.eps * a DualNumber.eps = 0 := by
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  have hk : jC (φ (a DualNumber.eps)) = 0 := by
    rw [← RingHom.mem_ker, hC]
    exact Ideal.mem_span_singleton_self _
  constructor
  · rw [injective_iff_map_eq_zero]
    intro b hb
    have h1 : b ∈ RingHom.ker jB := by rw [RingHom.mem_ker, ← hφ, hb, map_zero]
    rw [hB, Ideal.mem_span_singleton] at h1
    obtain ⟨b1, rfl⟩ := h1
    have h2 : (φ.comp a) DualNumber.eps * φ b1 = 0 := by
      rw [RingHom.comp_apply, ← map_mul]
      exact hb
    have h3 := mem_span_of_flat (φ.comp a) hfl (φ b1) h2
    rw [Ideal.mem_span_singleton] at h3
    obtain ⟨c', hc'⟩ := h3
    have h4 : b1 ∈ RingHom.ker jB := by
      rw [RingHom.mem_ker, ← hφ, hc', map_mul, RingHom.comp_apply, hk, zero_mul]
    rw [hB, Ideal.mem_span_singleton] at h4
    obtain ⟨b2, rfl⟩ := h4
    rw [← _root_.mul_assoc, hee, zero_mul]
  · intro c
    obtain ⟨b, hb⟩ := hs (jC c)
    have h1 : c - φ b ∈ RingHom.ker jC := by rw [RingHom.mem_ker, map_sub, hφ, hb, sub_self]
    rw [hC, Ideal.mem_span_singleton] at h1
    obtain ⟨c1, hc1⟩ := h1
    obtain ⟨b1, hb1⟩ := hs (jC c1)
    have h2 : c1 - φ b1 ∈ RingHom.ker jC := by rw [RingHom.mem_ker, map_sub, hφ, hb1, sub_self]
    rw [hC, Ideal.mem_span_singleton] at h2
    obtain ⟨c2, hc2⟩ := h2
    have hφe : φ (a DualNumber.eps) * φ (a DualNumber.eps) = 0 := by
      rw [← map_mul, hee, map_zero]
    refine ⟨b + a DualNumber.eps * b1, ?_⟩
    rw [map_add, map_mul]
    linear_combination (-1 : C) * hc1 - φ (a DualNumber.eps) * hc2 - c2 * hφe

/- English proof (translation)
Introduce `x`. Conclude with `⟨algebraMap K (DualNumber K) x, by simp⟩`.
-/
theorem fst_surjective (K : Type) [Field K] :
    Function.Surjective (TrivSqZeroExt.fstHom K K K).toRingHom := by
  intro x
  exact ⟨algebraMap K (DualNumber K) x, by simp⟩

/- English proof (translation)
Establish `hsp : spMap (TrivSqZeroExt.fstHom K K K).toRingHom = Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom)` using `rfl`. Establish `hsurj` using `fst_surjective K`. Establish `hci : IsClosedImmersion (spMap (TrivSqZeroExt.fstHom K K K).toRingHom)`. Rewrite using `[hsp]`. Conclude with `IsClosedImmersion.spec_of_surjective _ hsurj`.

Establish `hsu : Surjective (spMap (TrivSqZeroExt.fstHom K K K).toRingHom)`. Establish `hr : Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom K K K).toRingHom) = Set.univ`. Rewrite using `[range_comap_of_surjective (f := (TrivSqZeroExt.fstHom K K K).toRingHom) (hf := hsurj), PrimeSpectrum.zeroLocus_eq_univ_iff]`. Introduce `x hx`. Rewrite `hx` using `[SetLike.mem_coe, ker_fst_eq_span, Ideal.mem_span_singleton]`.

Take `⟨y, rfl⟩` from `hx`. Use `show _ ∈ nilradical _`. Rewrite using `[mem_nilradical]`. Conclude with `⟨2, by rw [pow_two, _root_.mul_mul_mul_comm, DualNumber.eps_mul_eps, zero_mul]⟩`. Rewrite using `[hsp]`.

Conclude with `⟨fun p => Set.range_eq_univ.1 hr p⟩`. Establish `hcj : IsClosedImmersion j` using `MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip hci`. Establish `hsj : Surjective j` using `MorphismProperty.of_isPullback (P := @Surjective) h.flip hsu`. Use `⟨hcj, ?_⟩` and prove the remaining obligations. Rewrite using `[isHomeomorph_iff_isEmbedding_surjective]`.

Conclude with `⟨j.isClosedEmbedding.isEmbedding, hsj.surj⟩`.
-/
theorem isHomeomorph_of_isPullback {K : Type} [Field K] {Y Y' : Scheme.{0}} {q : Y ⟶ Sp K}
    {π : Y' ⟶ Sp (DualNumber K)} {j : Y ⟶ Y'}
    (h : IsPullback j q π (spMap (TrivSqZeroExt.fstHom K K K).toRingHom)) :
    IsClosedImmersion j ∧ IsHomeomorph j := by
  have hsp : spMap (TrivSqZeroExt.fstHom K K K).toRingHom =
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) := rfl
  have hsurj := fst_surjective K
  have hci : IsClosedImmersion (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) := by
    rw [hsp]
    exact IsClosedImmersion.spec_of_surjective _ hsurj
  have hsu : Surjective (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) := by
    have hr : Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom K K K).toRingHom) = Set.univ := by
      rw [range_comap_of_surjective (f := (TrivSqZeroExt.fstHom K K K).toRingHom)
        (hf := hsurj), PrimeSpectrum.zeroLocus_eq_univ_iff]
      intro x hx
      rw [SetLike.mem_coe, ker_fst_eq_span, Ideal.mem_span_singleton] at hx
      obtain ⟨y, rfl⟩ := hx
      show _ ∈ nilradical _
      rw [mem_nilradical]
      exact ⟨2, by rw [pow_two, _root_.mul_mul_mul_comm, DualNumber.eps_mul_eps, zero_mul]⟩
    rw [hsp]
    exact ⟨fun p => Set.range_eq_univ.1 hr p⟩
  have hcj : IsClosedImmersion j := MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip hci
  have hsj : Surjective j := MorphismProperty.of_isPullback (P := @Surjective) h.flip hsu
  refine ⟨hcj, ?_⟩
  rw [isHomeomorph_iff_isEmbedding_surjective]
  exact ⟨j.isClosedEmbedding.isEmbedding, hsj.surj⟩

/- English proof (translation)
Apply `isAffineHom_of_forall_exists_isAffineOpen` to reduce the goal to its premises. Introduce `y`. Take `⟨x, rfl⟩` from `he.surjective y`. Establish `hmem : e x ∈ (⊤ : Y.Opens)` using `trivial`. Take `⟨V, hV, hxV, -⟩` from `(TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens) hmem`.

Take `⟨W, hW, hxW, hWV⟩` from `(TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (show x ∈ e ⁻¹ᵁ V from hxV)`. Set `O : Y.Opens` to `⟨(⇑e) '' (W : Set X), he.isOpenMap _ W.isOpen⟩`. Take `⟨g, hgO, hgy⟩` from `(show IsAffineOpen V from hV).exists_basicOpen_le (V := O) ⟨e x, ⟨x, hxW, rfl⟩⟩ hxV`. Establish `hsub : e ⁻¹ᵁ Y.basicOpen g ≤ W`. Introduce `z hz`.

Take `⟨w, hw, hwz⟩` from `hgO hz`. Rewrite using `[← he.injective hwz]` and apply the resulting hypothesis. Use `⟨Y.basicOpen g, hgy, (show IsAffineOpen V from hV).basicOpen g, ?_⟩` and prove the remaining obligations. Establish `heq : e ⁻¹ᵁ Y.basicOpen g = X.basicOpen (X.presheaf.map (homOfLE hWV).op (e.app V g))`. Rewrite using `[Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]`.

Conclude with `(inf_eq_right.2 hsub).symm`. Rewrite using `[heq]`. Conclude with `(show IsAffineOpen W from hW).basicOpen _`.
-/
theorem isAffineHom_of_isHomeomorph {X Y : Scheme.{0}} (e : X ⟶ Y) (he : IsHomeomorph e) :
    IsAffineHom e := by
  apply isAffineHom_of_forall_exists_isAffineOpen
  intro y
  obtain ⟨x, rfl⟩ := he.surjective y
  have hmem : e x ∈ (⊤ : Y.Opens) := trivial
  obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens) hmem
  obtain ⟨W, hW, hxW, hWV⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show x ∈ e ⁻¹ᵁ V from hxV)
  let O : Y.Opens := ⟨(⇑e) '' (W : Set X), he.isOpenMap _ W.isOpen⟩
  obtain ⟨g, hgO, hgy⟩ := (show IsAffineOpen V from hV).exists_basicOpen_le (V := O)
    ⟨e x, ⟨x, hxW, rfl⟩⟩ hxV
  have hsub : e ⁻¹ᵁ Y.basicOpen g ≤ W := by
    intro z hz
    obtain ⟨w, hw, hwz⟩ := hgO hz
    rwa [← he.injective hwz]
  refine ⟨Y.basicOpen g, hgy, (show IsAffineOpen V from hV).basicOpen g, ?_⟩
  have heq : e ⁻¹ᵁ Y.basicOpen g =
      X.basicOpen (X.presheaf.map (homOfLE hWV).op (e.app V g)) := by
    rw [Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]
    exact (inf_eq_right.2 hsub).symm
  rw [heq]
  exact (show IsAffineOpen W from hW).basicOpen _

end GlobalTheory.EpsIso

namespace GlobalTheory

/- English proof (translation)
Introduce `K _ Y Y' Z' q π π' j j' e h h' hfl hπ hj`. Substitute `hπ hj` using the available equality. Take `⟨hcj, hhj⟩` from `GlobalTheory.EpsIso.isHomeomorph_of_isPullback h`. Take `⟨hcj', hhj'⟩` from `GlobalTheory.EpsIso.isHomeomorph_of_isPullback h'`. Establish `hcf : (⇑(j ≫ e) : Y → Z') = ⇑e ∘ ⇑j` using `rfl`.

Establish `hhe : IsHomeomorph e`. Rewrite using `[isHomeomorph_iff_continuous_isClosedMap_bijective]`. Use `⟨e.continuous, ?_, ?_⟩` and prove the remaining obligations. Introduce `F hF`. Establish `hF' : (⇑e) '' F = (⇑(j ≫ e)) '' ((⇑j) ⁻¹' F)`.

Rewrite using `[hcf, Set.image_comp, Set.image_preimage_eq _ hhj.surjective]`. Rewrite using `[hF']`. Conclude with `hhj'.isClosedMap _ (hF.preimage j.continuous)`. Establish `hb` using `hhj'.bijective`. Rewrite `hb` using `[hcf]`.

Conclude with `(Function.Bijective.of_comp_iff _ hhj.bijective).1 hb`. Establish `hA : IsAffineHom e` using `GlobalTheory.EpsIso.isAffineHom_of_isHomeomorph e hhe`. Establish `hβ : Function.Surjective (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom)` using `GlobalTheory.EpsIso.fst_surjective K`. Establish `hker : RingHom.ker (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom).hom = Ideal.span {(DualNumber.eps : DualNumber K)}` using `GlobalTheory.EpsIso.ker_fst_eq_span K`. Establish `hiso : ∀ W : Z'.Opens, IsAffineOpen W → IsIso (e.app W)`.

Introduce `W hW`. Establish `hW' : IsAffineOpen (e ⁻¹ᵁ W)` using `IsAffineHom.isAffine_preimage W hW`. Establish `hcomp : (e ≫ π').appLE ⊤ (e ⁻¹ᵁ W) le_top = π'.appLE ⊤ W le_top ≫ e.app W`. Rewrite using `[Scheme.Hom.app_eq_appLE]`. Conclude with `(Scheme.Hom.appLE_comp_appLE ..).symm`.

Establish `hB` using `GlobalTheory.ker_app_eq_map_appLE_of_isPullback hβ h' hW`. Establish `hC` using `GlobalTheory.ker_app_eq_map_appLE_of_isPullback hβ h hW'`. Rewrite `hB`, `hC` using `[hker, Ideal.map_span, Set.image_singleton]`. Establish `hC'` using `hC.trans (congrArg (fun g => Ideal.span {((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv ≫ g).hom DualNumber.eps}) hcomp)`. Establish `hfl'` using `HasRingHomProperty.appLE @Flat (e ≫ π') hfl ⟨⊤, isAffineOpen_top _⟩ ⟨e ⁻¹ᵁ W, hW'⟩ le_top`.

Establish `hfl2` using `(congrArg (fun g => g.hom.Flat) hcomp).mp hfl'`. Establish `hg : (Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv.hom.Flat` using `RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)`. Establish `hflat : ((e.app W).hom.comp ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv ≫ π'.appLE ⊤ W le_top).hom).Flat`. Establish `heq : (e.app W).hom.comp ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv ≫ π'.appLE ⊤ W le_top).hom = (π'.appLE ⊤ W le_top ≫ e.app W).hom.comp (Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv.hom`. Conclude with `RingHom.ext fun x => rfl`.

Rewrite using `[heq]`. Conclude with `RingHom.Flat.comp hg hfl2`. Use `hcj'` as an intermediate fact. Establish `hbij` using `GlobalTheory.EpsIso.bijective_of_mod_eps ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv ≫ π'.appLE ⊤ W le_top).hom (e.app W).hom ((j ≫ e).app W).hom (j.app (e ⁻¹ᵁ W)).hom (fun b => rfl) (Scheme.Hom.app_surjective (j ≫ e) W hW) hflat hB hC'`. Conclude with `(ConcreteCategory.isIso_iff_bijective _).2 hbij`.

Rewrite using `[← MorphismProperty.isomorphisms.iff]`. Use `IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme.{0}) (fun V : Z'.affineOpens => V.1) (iSup_affineOpens_eq_top Z') fun V => ?_` and prove the remaining obligations. Establish `hsrc : IsAffine (e ⁻¹ᵁ V.1)` using `IsAffineHom.isAffine_preimage _ V.2`. Establish `htgt : IsAffine V.1` using `V.2`. Use `((MorphismProperty.isomorphisms _).arrow_mk_iso_iff (arrowIsoSpecΓOfIsAffine (e ∣_ V.1))).mpr ?_` and prove the remaining obligations.

Rewrite using `[MorphismProperty.isomorphisms.iff, morphismRestrict_appTop]`. Establish `hV : IsAffineOpen (V.1.ι ''ᵁ ⊤)`. Rewrite using `[Scheme.Opens.ι_image_top]`. Conclude with `V.2`. Establish `hb1 : Function.Bijective (e.app (V.1.ι ''ᵁ ⊤)).hom` using `(ConcreteCategory.isIso_iff_bijective _).1 (hiso _ hV)`.

Establish `hb2 : Function.Bijective (Y'.presheaf.map (eqToHom (image_morphismRestrict_preimage e V.1 ⊤)).op).hom` using `(ConcreteCategory.isIso_iff_bijective _).1 inferInstance`. Conclude with `isIso_SpecMap_iff.2 (hb2.comp hb1)`.
-/
theorem isIso_of_id_mod_eps : ∀ (K : Type) [Field K] (Y Y' Z' : Scheme.{0}) (q : Y ⟶ Sp K) (π : Y' ⟶ Sp (DualNumber K)) (π' : Z' ⟶ Sp (DualNumber K)) (j : Y ⟶ Y') (j' : Y ⟶ Z') (e : Y' ⟶ Z'), IsPullback j q π (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) → IsPullback j' q π' (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) → Flat π → e ≫ π' = π → j ≫ e = j' → IsIso e := by
  intro K _ Y Y' Z' q π π' j j' e h h' hfl hπ hj
  subst hπ hj
  obtain ⟨hcj, hhj⟩ := GlobalTheory.EpsIso.isHomeomorph_of_isPullback h
  obtain ⟨hcj', hhj'⟩ := GlobalTheory.EpsIso.isHomeomorph_of_isPullback h'
  have hcf : (⇑(j ≫ e) : Y → Z') = ⇑e ∘ ⇑j := rfl
  have hhe : IsHomeomorph e := by
    rw [isHomeomorph_iff_continuous_isClosedMap_bijective]
    refine ⟨e.continuous, ?_, ?_⟩
    · intro F hF
      have hF' : (⇑e) '' F = (⇑(j ≫ e)) '' ((⇑j) ⁻¹' F) := by
        rw [hcf, Set.image_comp, Set.image_preimage_eq _ hhj.surjective]
      rw [hF']
      exact hhj'.isClosedMap _ (hF.preimage j.continuous)
    · have hb := hhj'.bijective
      rw [hcf] at hb
      exact (Function.Bijective.of_comp_iff _ hhj.bijective).1 hb
  have hA : IsAffineHom e := GlobalTheory.EpsIso.isAffineHom_of_isHomeomorph e hhe
  have hβ : Function.Surjective (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) :=
    GlobalTheory.EpsIso.fst_surjective K
  have hker : RingHom.ker (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom).hom =
      Ideal.span {(DualNumber.eps : DualNumber K)} := GlobalTheory.EpsIso.ker_fst_eq_span K
  have hiso : ∀ W : Z'.Opens, IsAffineOpen W → IsIso (e.app W) := by
    intro W hW
    have hW' : IsAffineOpen (e ⁻¹ᵁ W) := IsAffineHom.isAffine_preimage W hW
    have hcomp : (e ≫ π').appLE ⊤ (e ⁻¹ᵁ W) le_top = π'.appLE ⊤ W le_top ≫ e.app W := by
      rw [Scheme.Hom.app_eq_appLE]
      exact (Scheme.Hom.appLE_comp_appLE ..).symm
    have hB := GlobalTheory.ker_app_eq_map_appLE_of_isPullback hβ h' hW
    have hC := GlobalTheory.ker_app_eq_map_appLE_of_isPullback hβ h hW'
    rw [hker, Ideal.map_span, Set.image_singleton] at hB hC
    have hC' := hC.trans (congrArg
      (fun g => Ideal.span {((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv ≫ g).hom DualNumber.eps}) hcomp)
    have hfl' := HasRingHomProperty.appLE @Flat (e ≫ π') hfl ⟨⊤, isAffineOpen_top _⟩ ⟨e ⁻¹ᵁ W, hW'⟩ le_top
    have hfl2 := (congrArg (fun g => g.hom.Flat) hcomp).mp hfl'
    have hg : (Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv.hom.Flat :=
      RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)
    have hflat : ((e.app W).hom.comp ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv ≫
        π'.appLE ⊤ W le_top).hom).Flat := by
      have heq : (e.app W).hom.comp ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv ≫
          π'.appLE ⊤ W le_top).hom = (π'.appLE ⊤ W le_top ≫ e.app W).hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv.hom := by
        exact RingHom.ext fun x => rfl
      rw [heq]
      exact RingHom.Flat.comp hg hfl2
    have := hcj'
    have hbij := GlobalTheory.EpsIso.bijective_of_mod_eps
      ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv ≫ π'.appLE ⊤ W le_top).hom
      (e.app W).hom ((j ≫ e).app W).hom (j.app (e ⁻¹ᵁ W)).hom (fun b => rfl)
      (Scheme.Hom.app_surjective (j ≫ e) W hW) hflat hB hC'
    exact (ConcreteCategory.isIso_iff_bijective _).2 hbij
  rw [← MorphismProperty.isomorphisms.iff]
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme.{0})
    (fun V : Z'.affineOpens => V.1) (iSup_affineOpens_eq_top Z') fun V => ?_
  have hsrc : IsAffine (e ⁻¹ᵁ V.1) := IsAffineHom.isAffine_preimage _ V.2
  have htgt : IsAffine V.1 := V.2
  refine ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (arrowIsoSpecΓOfIsAffine (e ∣_ V.1))).mpr ?_
  rw [MorphismProperty.isomorphisms.iff, morphismRestrict_appTop]
  have hV : IsAffineOpen (V.1.ι ''ᵁ ⊤) := by
    rw [Scheme.Opens.ι_image_top]
    exact V.2
  have hb1 : Function.Bijective (e.app (V.1.ι ''ᵁ ⊤)).hom :=
    (ConcreteCategory.isIso_iff_bijective _).1 (hiso _ hV)
  have hb2 : Function.Bijective
      (Y'.presheaf.map (eqToHom (image_morphismRestrict_preimage e V.1 ⊤)).op).hom :=
    (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  exact isIso_SpecMap_iff.2 (hb2.comp hb1)

end GlobalTheory
