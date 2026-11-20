import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsIntClosedLocalizationAndQuotient
open IsLocalRing Polynomial

namespace GlobalTheory.LocAcyc

/- English proof (translation)
Introduce `D _ _ hfin hproj hff act hbij`. Use `letI : Algebra B' B := e.symm.toRingHom.toAlgebra`. Use `letI : Algebra B' D := ((algebraMap B D).comp e.symm.toRingHom).toAlgebra`. Use `haveI : IsScalarTower B' B D := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Establish `hmap : ∀ b : B, algebraMap B D b = algebraMap B' D (e b)`.

Introduce `b`. Express the relevant statement in the definitionally equal form `algebraMap B D b = algebraMap B D (e.symm (e b))`. Rewrite using `[RingEquiv.symm_apply_apply]`. Establish `hsmul : ∀ (b : B) (d : D), b • d = (e b) • d`. Introduce `b d`.

Rewrite using `[Algebra.smul_def, Algebra.smul_def, hmap]`. Set `eL : B ≃ₗ[B'] B'` to `{ e.toAddEquiv with map_smul' := fun b' b => by`. Express the relevant statement in the definitionally equal form `e (e.symm b' * b) = b' * e b`. Rewrite using `[map_mul, RingEquiv.apply_symm_apply] }`. Use `haveI : Module.FaithfullyFlat B' B := Module.FaithfullyFlat.of_linearEquiv B' B' eL`.

Use `haveI : Module.Finite B' B := Module.Finite.equiv eL.symm`. Use `haveI : Module.FaithfullyFlat B D := hff`. Use `haveI : Module.Finite B D := hfin`. Establish `hfin' : Module.Finite B' D` using `Module.Finite.trans B D`. Establish `hff' : Module.FaithfullyFlat B' D` using `Module.FaithfullyFlat.trans B' B D`.

Use `haveI i1 : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e`. Use `haveI i2 : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.symm _ _`. Set `sl : D ≃ₛₗ[e.toRingHom] D` to `{ AddEquiv.refl D with map_smul' := fun b d => hsmul b d }`. Use `haveI := hproj`. Establish `hproj' : Module.Projective B' D` using `Module.Projective.of_equiv sl`.

Set `act' : Multiplicative (ZMod q) →* (D ≃ₐ[B'] D)` to `{ toFun := fun g => (act g).restrictScalars B' map_one' := by ext x; simp map_mul' := fun g g' => by ext x; simp }`. Use `haveI : TensorProduct.CompatibleSMul B' B D D := ⟨fun b m n => by`. Rewrite using `[hsmul b m, hsmul b n, TensorProduct.smul_tmul]⟩`. Set `s : TensorProduct B' D D ≃ₗ[B'] TensorProduct B D D` to `TensorProduct.equivOfCompatibleSMul B B' B' D D`. Establish `hcomp : ∀ x : TensorProduct B' D D, Algebra.TensorProduct.productMap (Pi.algHom B' (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id B' D)) (Pi.algHom B' (fun _ : Multiplicative (ZMod q) => D) (fun g => (act' g).toAlgHom)) x = Algebra.TensorProduct.productMap (Pi.algHom …`.

Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b`. Both sides reduce to the same expression.

Consider the case `add x y hx hy => rw [map_add, map_add, map_add, hx, hy]`. Take `⟨σ⟩` from `h D hfin' hproj' hff' act' (by`. Use `hbij.comp s.bijective using 1` and compare the differences between its conclusion and the goal. Conclude with `funext hcomp)`. Use `⟨{ toRingHom := (e.symm : B' →+* B).comp σ.toRingHom, commutes' := fun b => ?_ }⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `e.symm (σ (algebraMap B D b)) = b`. Rewrite using `[hmap, σ.commutes]`. Conclude with `e.symm_apply_apply b`.
-/
theorem torsorsTrivial_of_ringEquiv {B B' : Type} [CommRing B] [CommRing B'] (e : B ≃+* B')
    (q : ℕ) (h : TorsorsTrivial B' q) : TorsorsTrivial B q := by
  intro D _ _ hfin hproj hff act hbij
  letI : Algebra B' B := e.symm.toRingHom.toAlgebra
  letI : Algebra B' D := ((algebraMap B D).comp e.symm.toRingHom).toAlgebra
  haveI : IsScalarTower B' B D := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hmap : ∀ b : B, algebraMap B D b = algebraMap B' D (e b) := by
    intro b
    change algebraMap B D b = algebraMap B D (e.symm (e b))
    rw [RingEquiv.symm_apply_apply]
  have hsmul : ∀ (b : B) (d : D), b • d = (e b) • d := by
    intro b d
    rw [Algebra.smul_def, Algebra.smul_def, hmap]
  let eL : B ≃ₗ[B'] B' :=
    { e.toAddEquiv with
      map_smul' := fun b' b => by
        change e (e.symm b' * b) = b' * e b
        rw [map_mul, RingEquiv.apply_symm_apply] }
  haveI : Module.FaithfullyFlat B' B := Module.FaithfullyFlat.of_linearEquiv B' B' eL
  haveI : Module.Finite B' B := Module.Finite.equiv eL.symm
  haveI : Module.FaithfullyFlat B D := hff
  haveI : Module.Finite B D := hfin
  have hfin' : Module.Finite B' D := Module.Finite.trans B D
  have hff' : Module.FaithfullyFlat B' D := Module.FaithfullyFlat.trans B' B D
  haveI i1 : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  haveI i2 : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.symm _ _
  let sl : D ≃ₛₗ[e.toRingHom] D :=
    { AddEquiv.refl D with
      map_smul' := fun b d => hsmul b d }
  haveI := hproj
  have hproj' : Module.Projective B' D := Module.Projective.of_equiv sl
  let act' : Multiplicative (ZMod q) →* (D ≃ₐ[B'] D) :=
    { toFun := fun g => (act g).restrictScalars B'
      map_one' := by ext x; simp
      map_mul' := fun g g' => by ext x; simp }
  haveI : TensorProduct.CompatibleSMul B' B D D := ⟨fun b m n => by
    rw [hsmul b m, hsmul b n, TensorProduct.smul_tmul]⟩
  let s : TensorProduct B' D D ≃ₗ[B'] TensorProduct B D D :=
    TensorProduct.equivOfCompatibleSMul B B' B' D D
  have hcomp : ∀ x : TensorProduct B' D D,
      Algebra.TensorProduct.productMap
        (Pi.algHom B' (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id B' D))
        (Pi.algHom B' (fun _ : Multiplicative (ZMod q) => D) (fun g => (act' g).toAlgHom)) x =
      Algebra.TensorProduct.productMap
        (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id B D))
        (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun g => (act g).toAlgHom)) (s x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rfl
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  obtain ⟨σ⟩ := h D hfin' hproj' hff' act' (by
    convert hbij.comp s.bijective using 1
    exact funext hcomp)
  refine ⟨{ toRingHom := (e.symm : B' →+* B).comp σ.toRingHom, commutes' := fun b => ?_ }⟩
  change e.symm (σ (algebraMap B D b)) = b
  rw [hmap, σ.commutes]
  exact e.symm_apply_apply b

end GlobalTheory.LocAcyc

namespace GlobalTheory.LocAcyc

/- English proof (translation)
Use `haveI : IsDomain T' := IsLocalization.isDomain_of_le_nonZeroDivisors _ hM`. Establish `hinj : Function.Injective (algebraMap T T')` using `IsLocalization.injective T' hM`. Use `set M1 := Algebra.algebraMapSubmonoid O (nonZeroDivisors T)`. Use `set M2 := Algebra.algebraMapSubmonoid O (nonZeroDivisors T')`. Establish `h1 : M1 ≤ M2`.

Introduce and unpack `x ⟨s, hs, rfl⟩`. Use `⟨algebraMap T T' s, ?_, (IsScalarTower.algebraMap_apply T T' O s).symm⟩` and prove the remaining obligations. Establish `hs' : s ≠ 0` using `mem_nonZeroDivisors_iff_ne_zero.mp hs`. Conclude with `mem_nonZeroDivisors_iff_ne_zero.mpr fun h => hs' (hinj (by rw [h, map_zero]))`. Establish `h2 : ∀ x : M2, ∃ m : O, m * x ∈ M1`.

Introduce and unpack `⟨x, y, hy, rfl⟩`. Take `⟨⟨a, s⟩, rfl⟩` from `IsLocalization.mk'_surjective M y`. Use `⟨algebraMap T O s, a, ?_, ?_⟩` and prove the remaining obligations. Establish `hy' : IsLocalization.mk' T' a s ≠ 0` using `mem_nonZeroDivisors_iff_ne_zero.mp hy`. Use `mem_nonZeroDivisors_iff_ne_zero.mpr ?_` and prove the remaining obligations.

Introduce and unpack `rfl`. Conclude with `hy' (IsLocalization.mk'_zero s)`. Express the relevant statement in the definitionally equal form `algebraMap T O a = algebraMap T O s * algebraMap T' O (IsLocalization.mk' T' a s)`. Rewrite using `[IsScalarTower.algebraMap_apply T T' O s, ← map_mul, IsLocalization.mk'_spec', ← IsScalarTower.algebraMap_apply]`. Use `haveI : IsLocalization M2 (GenFib T O) := IsLocalization.isLocalization_of_is_exists_mul_mem (S := GenFib T O) (M := M1) (N := M2) h1 h2`.

Conclude with `⟨(IsLocalization.algEquiv M2 (GenFib T O) (GenFib T' O)).toRingEquiv⟩`.
-/
theorem nonempty_genFib_equiv {T T' O : Type} [CommRing T] [IsDomain T] [CommRing T'] [CommRing O]
    [Algebra T T'] [Algebra T O] [Algebra T' O] [IsScalarTower T T' O] (M : Submonoid T)
    (hM : M ≤ nonZeroDivisors T) [IsLocalization M T'] :
    Nonempty (GenFib T O ≃+* GenFib T' O) := by
  haveI : IsDomain T' := IsLocalization.isDomain_of_le_nonZeroDivisors _ hM
  have hinj : Function.Injective (algebraMap T T') := IsLocalization.injective T' hM
  set M1 := Algebra.algebraMapSubmonoid O (nonZeroDivisors T)
  set M2 := Algebra.algebraMapSubmonoid O (nonZeroDivisors T')
  have h1 : M1 ≤ M2 := by
    rintro x ⟨s, hs, rfl⟩
    refine ⟨algebraMap T T' s, ?_, (IsScalarTower.algebraMap_apply T T' O s).symm⟩
    have hs' : s ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hs
    exact mem_nonZeroDivisors_iff_ne_zero.mpr fun h => hs' (hinj (by rw [h, map_zero]))
  have h2 : ∀ x : M2, ∃ m : O, m * x ∈ M1 := by
    rintro ⟨x, y, hy, rfl⟩
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective M y
    refine ⟨algebraMap T O s, a, ?_, ?_⟩
    · have hy' : IsLocalization.mk' T' a s ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hy
      refine mem_nonZeroDivisors_iff_ne_zero.mpr ?_
      rintro rfl
      exact hy' (IsLocalization.mk'_zero s)
    · change algebraMap T O a = algebraMap T O s * algebraMap T' O (IsLocalization.mk' T' a s)
      rw [IsScalarTower.algebraMap_apply T T' O s, ← map_mul, IsLocalization.mk'_spec',
        ← IsScalarTower.algebraMap_apply]
  haveI : IsLocalization M2 (GenFib T O) :=
    IsLocalization.isLocalization_of_is_exists_mul_mem (S := GenFib T O) (M := M1) (N := M2) h1 h2
  exact ⟨(IsLocalization.algEquiv M2 (GenFib T O) (GenFib T' O)).toRingEquiv⟩

end GlobalTheory.LocAcyc

namespace GlobalTheory.LocAcyc

open CategoryTheory in

/- English proof (translation)
Introduce `hL T O _ _ _ _ _ _ _ hAIC P _ φ hφ hSH q hq hqu`. Use `set p : Ideal T := P.comap (C : T →+* T[X]) with hp`. Use `haveI : p.IsPrime := Ideal.comap_isPrime _ _`. Set `T'` to `Localization.AtPrime p`. Establish `hle : p.primeCompl ≤ nonZeroDivisors T` using `p.primeCompl_le_nonZeroDivisors`.

Establish `hAIC' : AbsIntClosed T'` using `((absIntClosed_localization_and_quotient T ⟨inferInstance, hAIC⟩).1 p.primeCompl (fun h => h (zero_mem p))).2`. Establish `hTO : ∀ a : T, algebraMap T O a = algebraMap T[X] O (C a)` using `fun a => by`. Rewrite using `[IsScalarTower.algebraMap_apply T T[X] O, Polynomial.algebraMap_eq]`. Establish `hunit : ∀ s : p.primeCompl, IsUnit (algebraMap T O s)`. Introduce `s`.

Establish `hs : C (s : T) ∈ P.primeCompl` using `s.2`. Establish `hu` using `(IsLocalization.map_units (Localization.AtPrime P) (⟨C (s : T), hs⟩ : P.primeCompl)).map φ`. Rewrite `hu` using `[← RingHom.comp_apply, hφ]`. Rewrite using `[hTO]` and apply the resulting hypothesis. Use `letI : Algebra T' O := (IsLocalization.lift (M := p.primeCompl) (S := T') hunit).toAlgebra`.

Use `haveI : IsScalarTower T T' O := IsScalarTower.of_algebraMap_eq (fun x => (IsLocalization.lift_eq hunit x).symm)`. Use `letI : Algebra T'[X] O := (eval₂RingHom (algebraMap T' O) (algebraMap T[X] O X)).toAlgebra`. Use `haveI : IsScalarTower T' T'[X] O := IsScalarTower.of_algebraMap_eq (fun x => by`. Express the relevant statement in the definitionally equal form `_ = eval₂ (algebraMap T' O) (algebraMap T[X] O X) (algebraMap T' T'[X] x)`. Rewrite using `[Polynomial.algebraMap_eq, eval₂_C])`.

Use `letI : Algebra T[X] T'[X] := Polynomial.algebra T T'`. Use `haveI : IsLocalization (Submonoid.map C p.primeCompl) T'[X] := Polynomial.isLocalization p.primeCompl T'`. Establish `hdisj : Disjoint (Submonoid.map C p.primeCompl : Set T[X]) (P : Set T[X])`. Rewrite using `[Set.disjoint_left]`. Introduce and unpack `_ ⟨s, hs, rfl⟩ hsP`.

Conclude with `hs hsP`. Use `set P' : Ideal T'[X] := P.map (algebraMap T[X] T'[X]) with hP'`. Use `haveI hP'prime : P'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ T'[X] P inferInstance hdisj`. Establish `hcomapP' : P'.comap (algebraMap T[X] T'[X]) = P` using `IsLocalization.comap_map_of_isPrime_disjoint _ T'[X] inferInstance hdisj`. Establish `hCcomm : ∀ a : T, C (algebraMap T T' a) = algebraMap T[X] T'[X] (C a)` using `fun a => by`.

Express the relevant statement in the definitionally equal form `_ = (C a).map (algebraMap T T')`. Rewrite using `[Polynomial.map_C]`. Establish `hmax : P'.comap (C : T' →+* T'[X]) = maximalIdeal T'`. Rewrite using `[← IsLocalization.map_comap p.primeCompl T' (P'.comap C), ← IsLocalization.map_comap p.primeCompl T' (maximalIdeal T'), IsLocalization.AtPrime.comap_maximalIdeal T' p]`. Use `congr 1`.

Use extensionality with `a`. Express the relevant statement in the definitionally equal form `C (algebraMap T T' a) ∈ P' ↔ C a ∈ P`. Rewrite using `[hCcomm, ← Ideal.mem_comap, hcomapP']`. Use `haveI : IsLocalization.AtPrime (Localization.AtPrime P') P := by`. Use `IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (Submonoid.map C p.primeCompl) (Localization.AtPrime P') P'` as an intermediate fact.

Establish `hc : (P'.comap (algebraMap T[X] T'[X])).primeCompl = P.primeCompl`. Use extensionality with `x`. Simplify using `only [Ideal.mem_primeCompl_iff, hcomapP']`. Unfold `IsLocalization.AtPrime at this ⊢`. Rewrite `this` using `[hc]`.

Conclude with `this`. Set `e : Localization.AtPrime P ≃ₐ[T[X]] Localization.AtPrime P'` to `IsLocalization.algEquiv P.primeCompl _ _`. Set `φ' : Localization.AtPrime P' →+* O` to `φ.comp e.symm.toRingEquiv.toRingHom`. Establish `hOO : (algebraMap T'[X] O).comp (algebraMap T[X] T'[X]) = algebraMap T[X] O`. Use `Polynomial.ringHom_ext (fun a => ?_) ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `eval₂ (algebraMap T' O) (algebraMap T[X] O X) ((C a).map (algebraMap T T')) = _`. Rewrite using `[Polynomial.map_C, eval₂_C, ← IsScalarTower.algebraMap_apply, hTO]`. Express the relevant statement in the definitionally equal form `eval₂ (algebraMap T' O) (algebraMap T[X] O X) ((X : T[X]).map (algebraMap T T')) = _`. Rewrite using `[Polynomial.map_X, eval₂_X]`. Establish `hφ' : φ'.comp (algebraMap T'[X] (Localization.AtPrime P')) = algebraMap T'[X] O`.

Use `IsLocalization.ringHom_ext (Submonoid.map C p.primeCompl) ?_` and prove the remaining obligations. Rewrite using `[RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, hOO]`. Use `RingHom.ext fun f => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `φ (e.symm (algebraMap T[X] _ f)) = _`. Rewrite using `[AlgEquiv.commutes, ← RingHom.comp_apply, hφ]`.

Establish `hSH' : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ'`. Take `⟨h1, h2, h3, h4⟩` from `hSH`. Use `⟨h1, h2, ?_, ?_⟩` and prove the remaining obligations. Use `⟨fun a ha => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `IsUnit (φ (e.symm a)) at ha`.

Establish `h5 : IsUnit (e.symm a)` using `h3.map_nonunit _ ha`. Simplify using `using h5.map e`. Use `haveI : (RingHom.toMorphismProperty @RingHom.Etale).RespectsIso := RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.Etale.respectsIso`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale at h4 ⊢`. Rewrite using `[CommRingCat.ofHom_comp]`.

Use `haveI : IsIso (CommRingCat.ofHom e.symm.toRingEquiv.toRingHom) := inferInstanceAs (IsIso (e.symm.toRingEquiv.toCommRingCatIso).hom)`. Conclude with `(MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr h4`. Establish `hqu' : IsUnit (q : T')`. Simplify using `using hqu.map (algebraMap T T')`. Establish `key` using `hL T' O hAIC' P' φ' hφ' hSH' hmax trivial q hq hqu'`.

Take `⟨eG⟩` from `nonempty_genFib_equiv (T := T) (T' := T') (O := O) p.primeCompl hle`. Conclude with `torsorsTrivial_of_ringEquiv eG q key`.
-/
theorem keyAll_of_keyLocal : KeyLocal → KeyAll := by
  intro hL T O _ _ _ _ _ _ _ hAIC P _ φ hφ hSH q hq hqu
  set p : Ideal T := P.comap (C : T →+* T[X]) with hp
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  let T' := Localization.AtPrime p
  have hle : p.primeCompl ≤ nonZeroDivisors T := p.primeCompl_le_nonZeroDivisors
  have hAIC' : AbsIntClosed T' :=
    ((absIntClosed_localization_and_quotient T ⟨inferInstance, hAIC⟩).1 p.primeCompl
      (fun h => h (zero_mem p))).2

  have hTO : ∀ a : T, algebraMap T O a = algebraMap T[X] O (C a) := fun a => by
    rw [IsScalarTower.algebraMap_apply T T[X] O, Polynomial.algebraMap_eq]
  have hunit : ∀ s : p.primeCompl, IsUnit (algebraMap T O s) := by
    intro s
    have hs : C (s : T) ∈ P.primeCompl := s.2
    have hu := (IsLocalization.map_units (Localization.AtPrime P)
      (⟨C (s : T), hs⟩ : P.primeCompl)).map φ
    rw [← RingHom.comp_apply, hφ] at hu
    rwa [hTO]
  letI : Algebra T' O := (IsLocalization.lift (M := p.primeCompl) (S := T') hunit).toAlgebra
  haveI : IsScalarTower T T' O :=
    IsScalarTower.of_algebraMap_eq (fun x => (IsLocalization.lift_eq hunit x).symm)
  letI : Algebra T'[X] O := (eval₂RingHom (algebraMap T' O) (algebraMap T[X] O X)).toAlgebra
  haveI : IsScalarTower T' T'[X] O :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      change _ = eval₂ (algebraMap T' O) (algebraMap T[X] O X) (algebraMap T' T'[X] x)
      rw [Polynomial.algebraMap_eq, eval₂_C])

  letI : Algebra T[X] T'[X] := Polynomial.algebra T T'
  haveI : IsLocalization (Submonoid.map C p.primeCompl) T'[X] :=
    Polynomial.isLocalization p.primeCompl T'
  have hdisj : Disjoint (Submonoid.map C p.primeCompl : Set T[X]) (P : Set T[X]) := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hsP
    exact hs hsP
  set P' : Ideal T'[X] := P.map (algebraMap T[X] T'[X]) with hP'
  haveI hP'prime : P'.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ T'[X] P inferInstance hdisj
  have hcomapP' : P'.comap (algebraMap T[X] T'[X]) = P :=
    IsLocalization.comap_map_of_isPrime_disjoint _ T'[X] inferInstance hdisj
  have hCcomm : ∀ a : T, C (algebraMap T T' a) = algebraMap T[X] T'[X] (C a) := fun a => by
    change _ = (C a).map (algebraMap T T')
    rw [Polynomial.map_C]
  have hmax : P'.comap (C : T' →+* T'[X]) = maximalIdeal T' := by
    rw [← IsLocalization.map_comap p.primeCompl T' (P'.comap C),
      ← IsLocalization.map_comap p.primeCompl T' (maximalIdeal T'),
      IsLocalization.AtPrime.comap_maximalIdeal T' p]
    congr 1
    ext a
    change C (algebraMap T T' a) ∈ P' ↔ C a ∈ P
    rw [hCcomm, ← Ideal.mem_comap, hcomapP']

  haveI : IsLocalization.AtPrime (Localization.AtPrime P') P := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.map C p.primeCompl) (Localization.AtPrime P') P'
    have hc : (P'.comap (algebraMap T[X] T'[X])).primeCompl = P.primeCompl := by
      ext x; simp only [Ideal.mem_primeCompl_iff, hcomapP']
    unfold IsLocalization.AtPrime at this ⊢
    rw [hc] at this
    exact this
  let e : Localization.AtPrime P ≃ₐ[T[X]] Localization.AtPrime P' :=
    IsLocalization.algEquiv P.primeCompl _ _
  let φ' : Localization.AtPrime P' →+* O := φ.comp e.symm.toRingEquiv.toRingHom
  have hOO : (algebraMap T'[X] O).comp (algebraMap T[X] T'[X]) = algebraMap T[X] O := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · change eval₂ (algebraMap T' O) (algebraMap T[X] O X) ((C a).map (algebraMap T T')) = _
      rw [Polynomial.map_C, eval₂_C, ← IsScalarTower.algebraMap_apply, hTO]
    · change eval₂ (algebraMap T' O) (algebraMap T[X] O X) ((X : T[X]).map (algebraMap T T')) = _
      rw [Polynomial.map_X, eval₂_X]
  have hφ' : φ'.comp (algebraMap T'[X] (Localization.AtPrime P')) = algebraMap T'[X] O := by
    refine IsLocalization.ringHom_ext (Submonoid.map C p.primeCompl) ?_
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, hOO]
    refine RingHom.ext fun f => ?_
    change φ (e.symm (algebraMap T[X] _ f)) = _
    rw [AlgEquiv.commutes, ← RingHom.comp_apply, hφ]
  have hSH' : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ' := by
    obtain ⟨h1, h2, h3, h4⟩ := hSH
    refine ⟨h1, h2, ?_, ?_⟩
    · refine ⟨fun a ha => ?_⟩
      change IsUnit (φ (e.symm a)) at ha
      have h5 : IsUnit (e.symm a) := h3.map_nonunit _ ha
      simpa using h5.map e
    · haveI : (RingHom.toMorphismProperty @RingHom.Etale).RespectsIso :=
        RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.Etale.respectsIso
      unfold GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale at h4 ⊢
      rw [CommRingCat.ofHom_comp]
      haveI : IsIso (CommRingCat.ofHom e.symm.toRingEquiv.toRingHom) :=
        inferInstanceAs (IsIso (e.symm.toRingEquiv.toCommRingCatIso).hom)
      exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr h4
  have hqu' : IsUnit (q : T') := by
    simpa using hqu.map (algebraMap T T')
  have key := hL T' O hAIC' P' φ' hφ' hSH' hmax trivial q hq hqu'
  obtain ⟨eG⟩ := nonempty_genFib_equiv (T := T) (T' := T') (O := O) p.primeCompl hle
  exact torsorsTrivial_of_ringEquiv eG q key

end GlobalTheory.LocAcyc
