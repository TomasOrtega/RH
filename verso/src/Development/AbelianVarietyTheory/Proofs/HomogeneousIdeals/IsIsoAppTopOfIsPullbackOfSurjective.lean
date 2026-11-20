import Mathlib

open CategoryTheory Limits AlgebraicGeometry TensorProduct Opposite

universe u

namespace GlobalTheory

namespace ProperFunctions

section Algebra

/- English proof (translation)
Set `φ : R →ₗ[R] M` to `LinearMap.toSpanSingleton R M m`. Establish `hex` using `Module.Flat.lTensor_exact A (LinearMap.exact_subtype_ker_map φ)`. Establish `h0 : φ.lTensor A (x ⊗ₜ[R] (1 : R)) = 0` using `by simp [φ, h]`. Take `⟨y, hy⟩` from `(hex _).mp h0`. Establish `key : ∀ y : A ⊗[R] LinearMap.ker φ, TensorProduct.rid R A ((LinearMap.ker φ).subtype.lTensor A y) ∈ J.map (algebraMap R A)`.

Introduce `y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a r`. Simplify using `only [LinearMap.lTensor_tmul, Submodule.subtype_apply, TensorProduct.rid_tmul, Algebra.smul_def]`.

Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hJ _ (LinearMap.mem_ker.mp r.2)))`. Consider the case `add a b ha hb => simpa only [map_add] using Ideal.add_mem _ ha hb`. Simplify `key y` using `[hy]`.
-/
theorem mem_map_of_tmul_eq_zero {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [AddCommGroup M] [Module R M] (x : A) (m : M) (J : Ideal R)
    (hJ : ∀ r : R, r • m = 0 → r ∈ J) (h : x ⊗ₜ[R] m = 0) :
    x ∈ J.map (algebraMap R A) := by
  let φ : R →ₗ[R] M := LinearMap.toSpanSingleton R M m
  have hex := Module.Flat.lTensor_exact A (LinearMap.exact_subtype_ker_map φ)
  have h0 : φ.lTensor A (x ⊗ₜ[R] (1 : R)) = 0 := by simp [φ, h]
  obtain ⟨y, hy⟩ := (hex _).mp h0
  have key : ∀ y : A ⊗[R] LinearMap.ker φ,
      TensorProduct.rid R A ((LinearMap.ker φ).subtype.lTensor A y) ∈ J.map (algebraMap R A) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a r =>
      simp only [LinearMap.lTensor_tmul, Submodule.subtype_apply, TensorProduct.rid_tmul,
        Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hJ _ (LinearMap.mem_ker.mp r.2)))
    | add a b ha hb => simpa only [map_add] using Ideal.add_mem _ ha hb
  simpa [hy] using key y

/- English proof (translation)
Use `algebraize [φ]`. Use `mem_map_of_tmul_eq_zero x (Ideal.Quotient.mk I a) J (fun r hr ↦ hJ r ?_) ?_` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_mul]`. Conclude with `hr`. Establish `h1 : ∀ y ∈ I.map φ, ∀ z : A, (z * y) ⊗ₜ[R] (1 : R ⧸ I) = 0`.

Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨r, hr, rfl⟩` from `hy`. Introduce `z`.

Establish `: z * φ r = r • z` using `by rw [mul_comm]; rfl`. Rewrite using `[this, TensorProduct.smul_tmul]`. Establish `: r • (1 : R ⧸ I) = 0`. Rewrite using `[← Algebra.algebraMap_eq_smul_one]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mpr hr`.

Simplify using `[this]`. Consider the case `zero => simp`. Consider the case `add y y' _ _ hy hy' => intro z`. Rewrite using `[mul_add, TensorProduct.add_tmul, hy, hy', add_zero]`. Consider the case `smul c y _ hy => intro z`.

Rewrite using `[smul_eq_mul, ← mul_assoc, hy]`. Establish `h2` using `h1 _ h 1`. Establish `h3 : (1 : A) * (φ a * x) = a • x` using `by rw [one_mul]; rfl`. Rewrite `h2` using `[h3, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]`. Conclude with `h2`.
-/
theorem mem_map_of_mul_mem_map {R A : Type*} [CommRing R] [CommRing A] (φ : R →+* A)
    (hφ : φ.Flat) (I J : Ideal R) (a : R) (hJ : ∀ r : R, r * a ∈ I → r ∈ J) (x : A)
    (h : φ a * x ∈ I.map φ) : x ∈ J.map φ := by
  algebraize [φ]
  refine mem_map_of_tmul_eq_zero x (Ideal.Quotient.mk I a) J (fun r hr ↦ hJ r ?_) ?_
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
    exact hr
  · have h1 : ∀ y ∈ I.map φ, ∀ z : A, (z * y) ⊗ₜ[R] (1 : R ⧸ I) = 0 := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨r, hr, rfl⟩ := hy
        intro z
        have : z * φ r = r • z := by rw [mul_comm]; rfl
        rw [this, TensorProduct.smul_tmul]
        have : r • (1 : R ⧸ I) = 0 := by
          rw [← Algebra.algebraMap_eq_smul_one]
          exact Ideal.Quotient.eq_zero_iff_mem.mpr hr
        simp [this]
      | zero => simp
      | add y y' _ _ hy hy' => intro z; rw [mul_add, TensorProduct.add_tmul, hy, hy', add_zero]
      | smul c y _ hy => intro z; rw [smul_eq_mul, ← mul_assoc, hy]
    have h2 := h1 _ h 1
    have h3 : (1 : A) * (φ a * x) = a • x := by rw [one_mul]; rfl
    rw [h3, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one] at h2
    exact h2

/- English proof (translation)
Use `algebraize [φ.hom, ψ.hom]`. Set `e` to `(CommRingCat.isPushout_tensorProduct R A K).isoIsPushout _ _ H`. Use `mem_map_of_tmul_eq_zero x (1 : K) _ (fun r hr ↦ ?_) ?_` and prove the remaining obligations. Rewrite `hr` using `[← Algebra.algebraMap_eq_smul_one]`. Then use the resulting hypothesis. Use `congr($((CommRingCat.isPushout_tensorProduct R A K).inl_isoIsPushout_inv _ _ H).hom x)` as an intermediate fact.

Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply] at this`. Rewrite `this` using `[show inl.hom x = 0 from hx, map_zero]`. Conclude with `this.symm`.
-/
theorem mem_map_ker_of_isPushout {R A K P : CommRingCat.{u}} {φ : R ⟶ A} {ψ : R ⟶ K}
    {inl : A ⟶ P} {inr : K ⟶ P} (H : IsPushout φ ψ inl inr) (hφ : φ.hom.Flat) (x : A)
    (hx : inl x = 0) : x ∈ (RingHom.ker ψ.hom).map φ.hom := by
  algebraize [φ.hom, ψ.hom]
  let e := (CommRingCat.isPushout_tensorProduct R A K).isoIsPushout _ _ H
  refine mem_map_of_tmul_eq_zero x (1 : K) _ (fun r hr ↦ ?_) ?_
  · rwa [← Algebra.algebraMap_eq_smul_one] at hr
  · have := congr($((CommRingCat.isPushout_tensorProduct R A K).inl_isoIsPushout_inv _ _ H).hom x)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [show inl.hom x = 0 from hx, map_zero] at this
    exact this.symm

/- English proof (translation)
Establish `hb : Function.Bijective inr.hom` using `ConcreteCategory.bijective_of_isIso inr`. Use `algebraize [φ.hom, ψ.hom, inl.hom, inr.hom, (φ ≫ inl).hom]`. Establish `: IsScalarTower R A P` using `.of_algebraMap_eq' rfl`. Establish `: IsScalarTower R K P` using `.of_algebraMap_eq' congr($(H.w).hom)`. Establish `: Algebra.IsPushout R A K P` using `CommRingCat.isPushout_iff_isPushout.mp H`.

Use `RingHom.FaithfullyFlat.codescendsAlong_bijective (R := R) (S := A) (R' := K) (S' := P) hψ hb` as an intermediate fact. Conclude with `(ConcreteCategory.isIso_iff_bijective φ).mpr this`.
-/
theorem isIso_of_isPushout_of_faithfullyFlat {R A K P : CommRingCat.{u}} {φ : R ⟶ A} {ψ : R ⟶ K}
    {inl : A ⟶ P} {inr : K ⟶ P} (H : IsPushout φ ψ inl inr) (hψ : ψ.hom.FaithfullyFlat)
    [IsIso inr] : IsIso φ := by
  have hb : Function.Bijective inr.hom := ConcreteCategory.bijective_of_isIso inr
  algebraize [φ.hom, ψ.hom, inl.hom, inr.hom, (φ ≫ inl).hom]
  have : IsScalarTower R A P := .of_algebraMap_eq' rfl
  have : IsScalarTower R K P := .of_algebraMap_eq' congr($(H.w).hom)
  have : Algebra.IsPushout R A K P := CommRingCat.isPushout_iff_isPushout.mp H
  have := RingHom.FaithfullyFlat.codescendsAlong_bijective (R := R) (S := A) (R' := K) (S' := P)
    hψ hb
  exact (ConcreteCategory.isIso_iff_bijective φ).mpr this

end Algebra

section BaseChange

variable {X Y S T : Scheme.{u}} {f : T ⟶ S} {g : Y ⟶ X} {p : X ⟶ S} {q : Y ⟶ T}

/- English proof (translation)
The claim follows from `le_top`.
-/
theorem le_preimage_top (p : X ⟶ S) (U : X.Opens) : U ≤ p ⁻¹ᵁ ⊤ := le_top

/- English proof (translation)
The claim follows from `(Scheme.Hom.app_eq_appLE p (U := ⊤)).symm`.
-/
theorem appLE_top_top (p : X ⟶ S) (h : (⊤ : X.Opens) ≤ p ⁻¹ᵁ ⊤) : p.appLE ⊤ ⊤ h = p.appTop :=
  (Scheme.Hom.app_eq_appLE p (U := ⊤)).symm

/- English proof (translation)
Establish `: CompactSpace X` using `QuasiCompact.compactSpace_of_compactSpace p`. Establish `: QuasiSeparatedSpace X` using `(quasiSeparated_iff_quasiSeparatedSpace p).mp inferInstance`. Use `isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤) (le_preimage_top f ⊤) (le_preimage_top p ⊤) (by simp) (isAffineOpen_top S) (isAffineOpen_top T) (by simpa using isCompact_univ) (by simpa using isQuasiSeparated_univ)` as an intermediate fact. Simplify `(isIso_pushoutSection_iff ..).mp this` using `only [appLE_top_top]`.
-/
theorem isPushout_appTop (H : IsPullback g q p f) [IsAffine S] [IsAffine T] [Flat f]
    [QuasiCompact p] [QuasiSeparated p] :
    IsPushout p.appTop f.appTop g.appTop q.appTop := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace X := (quasiSeparated_iff_quasiSeparatedSpace p).mp inferInstance
  have := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H (US := ⊤) (UT := ⊤) (UX := ⊤)
    (UY := ⊤) (le_preimage_top f ⊤) (le_preimage_top p ⊤) (by simp)
    (isAffineOpen_top S) (isAffineOpen_top T)
    (by simpa using isCompact_univ) (by simpa using isQuasiSeparated_univ)
  simpa only [appLE_top_top] using (isIso_pushoutSection_iff ..).mp this

/- English proof (translation)
The claim follows from `(isPushout_appTop H).isIso_inr_of_isIso`.
-/
theorem isIso_appTop_of_isPullback (H : IsPullback g q p f) [IsAffine S] [IsAffine T] [Flat f]
    [QuasiCompact p] [QuasiSeparated p] [IsIso p.appTop] : IsIso q.appTop :=
  (isPushout_appTop H).isIso_inr_of_isIso

/- English proof (translation)
Establish `: CompactSpace X` using `QuasiCompact.compactSpace_of_compactSpace p`. Establish `hUY : (⊤ : Y.Opens) = g ⁻¹ᵁ ⊤ ⊓ q ⁻¹ᵁ ⊤` using `by simp`. Set `σ` to `pushoutSection H (le_preimage_top f ⊤) (le_preimage_top p ⊤) hUY`. Establish `: Mono σ` using `mono_pushoutSection_of_isCompact_of_flat_right H _ _ hUY (isAffineOpen_top S) (isAffineOpen_top T) (by simpa using isCompact_univ)`. Establish `hq : IsIso (q.appLE ⊤ ⊤ (le_preimage_top q ⊤))` using `by rw [appLE_top_top]; infer_instance`.

Establish `h1 : pushout.inr _ _ ≫ σ = q.appLE ⊤ ⊤ (le_preimage_top q ⊤)` using `pushout.inr_desc _ _ _`. Establish `: IsSplitEpi σ` using `⟨⟨inv (q.appLE ⊤ ⊤ (le_preimage_top q ⊤)) ≫ pushout.inr _ _, by rw [Category.assoc, h1, IsIso.inv_hom_id]⟩⟩`. Establish `: IsIso σ` using `isIso_of_mono_of_isSplitEpi σ`. Establish `h2 : IsPushout p.appTop f.appTop g.appTop q.appTop`. Simplify `(isIso_pushoutSection_iff ..).mp this` using `only [appLE_top_top]`.

Conclude with `isIso_of_isPushout_of_faithfullyFlat h2 ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mp ⟨‹_›, ‹_›⟩)`.
-/
theorem isIso_appTop_of_isPullback_of_surjective (H : IsPullback g q p f) [IsAffine S]
    [IsAffine T] [Flat f] [Surjective f] [QuasiCompact p] [IsIso q.appTop] : IsIso p.appTop := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have hUY : (⊤ : Y.Opens) = g ⁻¹ᵁ ⊤ ⊓ q ⁻¹ᵁ ⊤ := by simp
  let σ := pushoutSection H (le_preimage_top f ⊤) (le_preimage_top p ⊤) hUY
  have : Mono σ := mono_pushoutSection_of_isCompact_of_flat_right H _ _ hUY
    (isAffineOpen_top S) (isAffineOpen_top T) (by simpa using isCompact_univ)
  have hq : IsIso (q.appLE ⊤ ⊤ (le_preimage_top q ⊤)) := by rw [appLE_top_top]; infer_instance
  have h1 : pushout.inr _ _ ≫ σ = q.appLE ⊤ ⊤ (le_preimage_top q ⊤) := pushout.inr_desc _ _ _
  have : IsSplitEpi σ :=
    ⟨⟨inv (q.appLE ⊤ ⊤ (le_preimage_top q ⊤)) ≫ pushout.inr _ _,
      by rw [Category.assoc, h1, IsIso.inv_hom_id]⟩⟩
  have : IsIso σ := isIso_of_mono_of_isSplitEpi σ
  have h2 : IsPushout p.appTop f.appTop g.appTop q.appTop := by
    simpa only [appLE_top_top] using (isIso_pushoutSection_iff ..).mp this
  exact isIso_of_isPushout_of_faithfullyFlat h2
    ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mp ⟨‹_›, ‹_›⟩)

/- English proof (translation)
Use `isIso_pushoutSection_of_isAffineOpen H (US := ⊤) (UT := ⊤) (UX := U) (UY := g ⁻¹ᵁ U) (le_preimage_top f ⊤) (le_preimage_top p U) (by simp) (isAffineOpen_top S) (isAffineOpen_top T) hU` as an intermediate fact. Establish `h` using `(isIso_pushoutSection_iff ..).mp this`. Rewrite `h` using `[appLE_top_top, Scheme.Hom.appLE_eq_app]`. Conclude with `mem_map_ker_of_isPushout h (p.flat_appLE (isAffineOpen_top S) hU _) x hx`.
-/
theorem mem_map_ker_of_app_eq_zero (H : IsPullback g q p f) [IsAffine S] [IsAffine T] [Flat p]
    {U : X.Opens} (hU : IsAffineOpen U) (x : Γ(X, U)) (hx : g.app U x = 0) :
    x ∈ (RingHom.ker f.appTop.hom).map (p.appLE ⊤ U (le_preimage_top p U)).hom := by
  have := isIso_pushoutSection_of_isAffineOpen H (US := ⊤) (UT := ⊤) (UX := U)
    (UY := g ⁻¹ᵁ U) (le_preimage_top f ⊤) (le_preimage_top p U) (by simp)
    (isAffineOpen_top S) (isAffineOpen_top T) hU
  have h := (isIso_pushoutSection_iff ..).mp this
  rw [appLE_top_top, Scheme.Hom.appLE_eq_app] at h
  exact mem_map_ker_of_isPushout h (p.flat_appLE (isAffineOpen_top S) hU _) x hx

/- English proof (translation)
The claim follows from `X.sheaf.eq_of_locally_eq' (fun U : X.affineOpens ↦ U.1) ⊤ (fun _ ↦ homOfLE le_top) (iSup_affineOpens_eq_top X).ge x 0 fun U ↦ (h U).trans (map_zero _).symm`.
-/
theorem eq_zero_of_forall_affineOpens (x : Γ(X, ⊤))
    (h : ∀ U : X.affineOpens, X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op x = 0) : x = 0 :=
  X.sheaf.eq_of_locally_eq' (fun U : X.affineOpens ↦ U.1) ⊤ (fun _ ↦ homOfLE le_top)
    (iSup_affineOpens_eq_top X).ge x 0 fun U ↦ (h U).trans (map_zero _).symm

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Use `eq_zero_of_forall_affineOpens x fun U ↦ ?_` and prove the remaining obligations. Use `mem_map_ker_of_app_eq_zero H U.2 (X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op x) (by` as an intermediate fact. Rewrite using `[← CommRingCat.comp_apply, g.naturality, CommRingCat.comp_apply]`.

Use `erw [hx]`. Conclude with `map_zero _)`. Rewrite `this` using `[(RingHom.injective_iff_ker_eq_bot _).mp hf, Ideal.map_bot, Ideal.mem_bot]`. Then use the resulting hypothesis.
-/
theorem injective_appTop_of_isPullback (H : IsPullback g q p f) [IsAffine S] [IsAffine T] [Flat p]
    (hf : Function.Injective f.appTop) : Function.Injective g.appTop := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  refine eq_zero_of_forall_affineOpens x fun U ↦ ?_
  have := mem_map_ker_of_app_eq_zero H U.2 (X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op x) (by
    rw [← CommRingCat.comp_apply, g.naturality, CommRingCat.comp_apply]
    erw [hx]
    exact map_zero _)
  rwa [(RingHom.injective_iff_ker_eq_bot _).mp hf, Ideal.map_bot, Ideal.mem_bot] at this

end BaseChange

section Field

variable {X S : Scheme.{u}}

/- English proof (translation)
Set `F` to `(Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop`. Establish `hF : F.hom.IsIntegral`. Apply `RingHom.isIntegral_respectsIso.2 (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)` to reduce the goal to its premises. Conclude with `isIntegral_appTop_of_universallyClosed p`. Establish `: IsIso F` using `by algebraize [F.hom]`.

Conclude with `(ConcreteCategory.isIso_iff_bijective F).mpr (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := Γ(X, ⊤)))`. Conclude with `IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of k)).inv p.appTop`.
-/
theorem isIso_appTop_of_isAlgClosed {k : Type u} [Field k] [IsAlgClosed k]
    (p : X ⟶ Spec (.of k)) [IsIntegral X] [UniversallyClosed p] : IsIso p.appTop := by
  let F := (Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop
  have hF : F.hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2 (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed p
  have : IsIso F := by
    algebraize [F.hom]
    exact (ConcreteCategory.isIso_iff_bijective F).mpr
      (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := Γ(X, ⊤)))
  exact IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of k)).inv p.appTop

/- English proof (translation)
Set `f : Spec (.of (AlgebraicClosure k)) ⟶ Spec (.of k)` to `Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))`. Establish `: IsIntegral (pullback p f)` using `GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback p f)`. Use `isIso_appTop_of_isAlgClosed (pullback.snd p f)` as an intermediate fact. Establish `: Surjective f` using `⟨fun x ↦ ⟨default, Subsingleton.elim _ _⟩⟩`. Conclude with `isIso_appTop_of_isPullback_of_surjective (.of_hasPullback p f)`.
-/
theorem isIso_appTop_of_field {k : Type u} [Field k]
    (p : X ⟶ Spec (.of k)) [GeometricallyIntegral p] [UniversallyClosed p] : IsIso p.appTop := by
  let f : Spec (.of (AlgebraicClosure k)) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  have : IsIntegral (pullback p f) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback p f)
  have := isIso_appTop_of_isAlgClosed (pullback.snd p f)
  have : Surjective f := ⟨fun x ↦ ⟨default, Subsingleton.elim _ _⟩⟩
  exact isIso_appTop_of_isPullback_of_surjective (.of_hasPullback p f)

end Field

section Section

variable {X S : Scheme.{u}}

/- English proof (translation)
Rewrite using `[← h, CommRingCat.hom_comp, ← Ideal.map_map]`. Conclude with `Ideal.mem_map_of_mem _ hx`.
-/
theorem map_mem_map_of_comp_eq {R A B : CommRingCat.{u}} {φ : R ⟶ A} {ψ : A ⟶ B} {χ : R ⟶ B}
    (h : φ ≫ ψ = χ) {I : Ideal R} {x : A} (hx : x ∈ I.map φ.hom) : ψ x ∈ I.map χ.hom := by
  rw [← h, CommRingCat.hom_comp, ← Ideal.map_map]
  exact Ideal.mem_map_of_mem _ hx

/- English proof (translation)
Rewrite using `[Scheme.Hom.appLE_comp_appLE]`. Use `congr 1`.
-/
theorem appLE_comp_appLE_of_section {p : X ⟶ S} {e : S ⟶ X} (he : e ≫ p = 𝟙 S) (U : X.Opens)
    (W : S.Opens) (hW : W ≤ e ⁻¹ᵁ U) :
    p.appLE ⊤ U (le_preimage_top p U) ≫ e.appLE U W hW =
      Scheme.Hom.appLE (𝟙 S) ⊤ W (le_preimage_top _ W) := by
  rw [Scheme.Hom.appLE_comp_appLE]
  congr 1

/- English proof (translation)
Establish `hker : ∀ {B : CommRingCat.{u}} (χ : Γ(T, ⊤) ⟶ B), (RingHom.ker f.appTop.hom).map (f.appTop ≫ χ).hom = ⊥`. Introduce `B χ`. Rewrite using `[CommRingCat.hom_comp, ← Ideal.map_map, (Ideal.map_eq_bot_iff_le_ker _).mpr le_rfl, Ideal.map_bot]`. Establish `hres : ∀ (U V : X.affineOpens) (hVU : V.1 ≤ U.1), g.appLE U.1 (g ⁻¹ᵁ V.1) (g.preimage_mono hVU) (h U) = g.app V.1 (h V)`. Introduce `U V hVU`.

Establish `e1 : p.appLE ⊤ V.1 (le_preimage_top p _) ≫ g.app V.1 = f.appTop ≫ q.appLE ⊤ (g ⁻¹ᵁ V.1) (le_preimage_top q _)`. Rewrite using `[← appLE_top_top f (le_preimage_top f _), Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]`. Use `congr 1`. Conclude with `H.w`. Use `map_mem_map_of_comp_eq e1 (hc U V hVU)` as an intermediate fact.

Rewrite `this` using `[hker, Ideal.mem_bot, map_sub, sub_eq_zero, ← CommRingCat.comp_apply]`. Rewrite using `[← this, Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE]`. Take `⟨s, hs, -⟩` from `Y.sheaf.existsUnique_gluing' (fun U : X.affineOpens ↦ g ⁻¹ᵁ U.1) ⊤ (fun _ ↦ homOfLE le_top) (g.iSup_preimage_eq_top (iSup_affineOpens_eq_top X)).ge (fun U ↦ g.app U.1 (h U)) (by`. Introduce `U U'`. Use `Y.sheaf.eq_of_locally_eq' (fun V : {V : X.affineOpens // V.1 ≤ U.1 ⊓ U'.1} ↦ g ⁻¹ᵁ V.1.1) _ (fun V ↦ homOfLE (g.preimage_mono V.2)) ?_ _ _ fun V ↦ ?_` and prove the remaining obligations.

Introduce `y hy`. Take `⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open (a := g y) (u := (U.1 ⊓ U'.1 : X.Opens)) hy (U.1 ⊓ U'.1).2`. Conclude with `TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVU⟩, hyV⟩`. Establish `h1` using `hres U V.1 (V.2.trans inf_le_left)`. Establish `h2` using `hres U' V.1 (V.2.trans inf_le_right)`.

Establish `h3` using `h1.trans h2.symm`. Simplify using `only [Scheme.Hom.appLE, CommRingCat.comp_apply] at h3`. Express the relevant statement in the definitionally equal form `(Y.presheaf.map _ ≫ Y.presheaf.map _) _ = (Y.presheaf.map _ ≫ Y.presheaf.map _) _`. Use `erw [← Functor.map_comp, ← Functor.map_comp]`. Conclude with `h3)`.

Take `⟨c, rfl⟩` from `hq s`. Set `e' : T ⟶ Y` to `H.lift (f ≫ e) (𝟙 T) (by simp [he])`. Establish `hc0 : c = 0`. Take `⟨_, ⟨U, hU, rfl⟩, hxU, -⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (e (f t))) isOpen_univ`. Take `⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩` from `S.isBasis_affineOpens.exists_subset_of_mem_open (a := f t) (u := (e ⁻¹ᵁ U : S.Opens)) hxU (e ⁻¹ᵁ U).2`.

Establish `hT : (⊤ : T.Opens) ≤ f ⁻¹ᵁ W` using `fun t' _ ↦ by rwa [Subsingleton.elim t' t]`. Establish `e1 : Scheme.Hom.appLE (𝟙 S) ⊤ W (le_preimage_top _ _) ≫ f.appLE W ⊤ hT = f.appTop ≫ 𝟙 _`. Rewrite using `[Scheme.Hom.appLE_comp_appLE, Category.comp_id, ← appLE_top_top f (le_preimage_top f _)]`. Use `congr 1`. Establish `h1` using `map_mem_map_of_comp_eq e1 (hv ⟨U, hU⟩ ⟨W, hW⟩ hWU)`.

Rewrite `h1` using `[hker, Ideal.mem_bot, ← CommRingCat.comp_apply]`. Use `replace h1 := congr($(Scheme.Hom.appLE_comp_appLE f e U W ⊤ hWU hT) (h ⟨U, hU⟩)).symm.trans h1`. Establish `hT' : (⊤ : T.Opens) ≤ e' ⁻¹ᵁ g ⁻¹ᵁ U`. Rewrite using `[← Scheme.Hom.comp_preimage, H.lift_fst]`. Conclude with `hT.trans (f.preimage_mono hWU)`.

Establish `h2` using `congr(e'.appLE (g ⁻¹ᵁ U) ⊤ hT' $(hs ⟨U, hU⟩))`. Establish `e2 : g.app U ≫ e'.appLE (g ⁻¹ᵁ U) ⊤ hT' = (f ≫ e).appLE U ⊤ (hT.trans (f.preimage_mono hWU))`. Rewrite using `[Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]`. Use `congr 1`. Conclude with `H.lift_fst ..`.

Establish `e3 : q.appTop ≫ Y.presheaf.map (homOfLE (le_top : g ⁻¹ᵁ U ≤ ⊤)).op ≫ e'.appLE (g ⁻¹ᵁ U) ⊤ hT' = 𝟙 _`. Rewrite using `[Scheme.Hom.map_appLE, appLE_top_top, ← Scheme.Hom.comp_appTop, H.lift_snd, Scheme.Hom.id_appTop]`. Establish `h3` using `congr($e3 c)`. Establish `h4` using `congr($e2 (h ⟨U, hU⟩))`. Simplify using `only [CommRingCat.comp_apply, CommRingCat.id_apply] at h3 h4`.

Conclude with `h3.symm.trans (h2.trans (h4.trans h1))`. Use `mem_map_ker_of_app_eq_zero H U.2 _ ((hs U).symm.trans ?_)` and prove the remaining obligations. Rewrite using `[hc0, map_zero]`. Conclude with `map_zero _`.
-/
theorem mem_map_ker_of_compatible {Y T : Scheme.{u}} {f : T ⟶ S} {g : Y ⟶ X} {p : X ⟶ S}
    {q : Y ⟶ T} (H : IsPullback g q p f) [IsAffine S] [IsAffine T] [Flat p] (t : T)
    [Subsingleton T]
    (hq : Function.Surjective q.appTop) {e : S ⟶ X} (he : e ≫ p = 𝟙 S)
    (h : ∀ U : X.affineOpens, Γ(X, U.1))
    (hc : ∀ (U V : X.affineOpens) (hVU : V.1 ≤ U.1),
      X.presheaf.map (homOfLE hVU).op (h U) - h V ∈
        (RingHom.ker f.appTop.hom).map (p.appLE ⊤ V.1 (le_preimage_top p _)).hom)
    (hv : ∀ (U : X.affineOpens) (W : S.affineOpens) (hW : W.1 ≤ e ⁻¹ᵁ U.1),
      e.appLE U.1 W.1 hW (h U) ∈ (RingHom.ker f.appTop.hom).map
        (Scheme.Hom.appLE (𝟙 S) ⊤ W.1 (le_preimage_top _ _)).hom)
    (U : X.affineOpens) :
    h U ∈ (RingHom.ker f.appTop.hom).map (p.appLE ⊤ U.1 (le_preimage_top p _)).hom := by
  have hker : ∀ {B : CommRingCat.{u}} (χ : Γ(T, ⊤) ⟶ B),
      (RingHom.ker f.appTop.hom).map (f.appTop ≫ χ).hom = ⊥ := by
    intro B χ
    rw [CommRingCat.hom_comp, ← Ideal.map_map, (Ideal.map_eq_bot_iff_le_ker _).mpr le_rfl,
      Ideal.map_bot]

  have hres : ∀ (U V : X.affineOpens) (hVU : V.1 ≤ U.1),
      g.appLE U.1 (g ⁻¹ᵁ V.1) (g.preimage_mono hVU) (h U) = g.app V.1 (h V) := by
    intro U V hVU
    have e1 : p.appLE ⊤ V.1 (le_preimage_top p _) ≫ g.app V.1 =
        f.appTop ≫ q.appLE ⊤ (g ⁻¹ᵁ V.1) (le_preimage_top q _) := by
      rw [← appLE_top_top f (le_preimage_top f _), Scheme.Hom.app_eq_appLE,
        Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
      congr 1
      exact H.w
    have := map_mem_map_of_comp_eq e1 (hc U V hVU)
    rw [hker, Ideal.mem_bot, map_sub, sub_eq_zero, ← CommRingCat.comp_apply] at this
    rw [← this, Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE]

  obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' (fun U : X.affineOpens ↦ g ⁻¹ᵁ U.1) ⊤
    (fun _ ↦ homOfLE le_top) (g.iSup_preimage_eq_top (iSup_affineOpens_eq_top X)).ge
    (fun U ↦ g.app U.1 (h U)) (by
      intro U U'
      refine Y.sheaf.eq_of_locally_eq'
        (fun V : {V : X.affineOpens // V.1 ≤ U.1 ⊓ U'.1} ↦ g ⁻¹ᵁ V.1.1) _
        (fun V ↦ homOfLE (g.preimage_mono V.2)) ?_ _ _ fun V ↦ ?_
      · intro y hy
        obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
          X.isBasis_affineOpens.exists_subset_of_mem_open (a := g y) (u := (U.1 ⊓ U'.1 : X.Opens))
            hy (U.1 ⊓ U'.1).2
        exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVU⟩, hyV⟩
      · have h1 := hres U V.1 (V.2.trans inf_le_left)
        have h2 := hres U' V.1 (V.2.trans inf_le_right)
        have h3 := h1.trans h2.symm
        simp only [Scheme.Hom.appLE, CommRingCat.comp_apply] at h3
        change (Y.presheaf.map _ ≫ Y.presheaf.map _) _ = (Y.presheaf.map _ ≫ Y.presheaf.map _) _
        erw [← Functor.map_comp, ← Functor.map_comp]
        exact h3)
  obtain ⟨c, rfl⟩ := hq s

  let e' : T ⟶ Y := H.lift (f ≫ e) (𝟙 T) (by simp [he])
  have hc0 : c = 0 := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (e (f t))) isOpen_univ
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (a := f t) (u := (e ⁻¹ᵁ U : S.Opens))
        hxU (e ⁻¹ᵁ U).2
    have hT : (⊤ : T.Opens) ≤ f ⁻¹ᵁ W := fun t' _ ↦ by rwa [Subsingleton.elim t' t]
    have e1 : Scheme.Hom.appLE (𝟙 S) ⊤ W (le_preimage_top _ _) ≫ f.appLE W ⊤ hT =
        f.appTop ≫ 𝟙 _ := by
      rw [Scheme.Hom.appLE_comp_appLE, Category.comp_id, ← appLE_top_top f (le_preimage_top f _)]
      congr 1
    have h1 := map_mem_map_of_comp_eq e1 (hv ⟨U, hU⟩ ⟨W, hW⟩ hWU)
    rw [hker, Ideal.mem_bot, ← CommRingCat.comp_apply] at h1
    replace h1 := congr($(Scheme.Hom.appLE_comp_appLE f e U W ⊤ hWU hT) (h ⟨U, hU⟩)).symm.trans h1
    have hT' : (⊤ : T.Opens) ≤ e' ⁻¹ᵁ g ⁻¹ᵁ U := by
      rw [← Scheme.Hom.comp_preimage, H.lift_fst]
      exact hT.trans (f.preimage_mono hWU)
    have h2 := congr(e'.appLE (g ⁻¹ᵁ U) ⊤ hT' $(hs ⟨U, hU⟩))
    have e2 : g.app U ≫ e'.appLE (g ⁻¹ᵁ U) ⊤ hT' =
        (f ≫ e).appLE U ⊤ (hT.trans (f.preimage_mono hWU)) := by
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
      congr 1
      exact H.lift_fst ..
    have e3 : q.appTop ≫ Y.presheaf.map (homOfLE (le_top : g ⁻¹ᵁ U ≤ ⊤)).op ≫
        e'.appLE (g ⁻¹ᵁ U) ⊤ hT' = 𝟙 _ := by
      rw [Scheme.Hom.map_appLE, appLE_top_top, ← Scheme.Hom.comp_appTop, H.lift_snd,
        Scheme.Hom.id_appTop]
    have h3 := congr($e3 c)
    have h4 := congr($e2 (h ⟨U, hU⟩))
    simp only [CommRingCat.comp_apply, CommRingCat.id_apply] at h3 h4
    exact h3.symm.trans (h2.trans (h4.trans h1))
  refine mem_map_ker_of_app_eq_zero H U.2 _ ((hs U).symm.trans ?_)
  rw [hc0, map_zero]
  exact map_zero _

/- English proof (translation)
Take `⟨s, hs⟩` from `S.isoSpec.hom.surjective ⟨𝔭, h𝔭⟩`. Use `⟨s, Ideal.ext fun r ↦ ?_⟩` and prove the remaining obligations. Establish `h1 : s ∈ S.basicOpen r ↔ r ∉ 𝔭`. Rewrite using `[← Scheme.toSpecΓ_preimage_basicOpen]`. Express the relevant statement in the definitionally equal form `S.isoSpec.hom s ∈ PrimeSpectrum.basicOpen r ↔ _`.

Rewrite using `[hs]`. Both sides reduce to the same expression. Rewrite using `[RingHom.mem_ker, ← not_iff_not, ← h1]`. Express the relevant statement in the definitionally equal form `¬ (S.fromSpecResidueField s).app ⊤ r = 0 ↔ _`. Rewrite using `[← basicOpen_eq_bot_iff, ← Scheme.preimage_basicOpen]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `hs`. Use `h (eq_bot_iff.mpr fun x hx ↦ hs ?_)` and prove the remaining obligations. Establish `hx' : S.fromSpecResidueField s x ∈ S.basicOpen r` using `hx`.

Rewrite `hx'` using `[Scheme.fromSpecResidueField_apply]`. Then use the resulting hypothesis. Introduce `h h'`. Establish `: (default : Spec (S.residueField s)) ∈ S.fromSpecResidueField s ⁻¹ᵁ S.basicOpen r`. Express the relevant statement in the definitionally equal form `S.fromSpecResidueField s default ∈ S.basicOpen r`. Rewrite using `[Scheme.fromSpecResidueField_apply]` and apply the resulting hypothesis.

Rewrite `this` using `[h']`. Conclude with `this`.
-/
theorem exists_ker_fromSpecResidueField [IsAffine S] (𝔭 : Ideal Γ(S, ⊤)) (h𝔭 : 𝔭.IsPrime) :
    ∃ s : S, RingHom.ker (S.fromSpecResidueField s).appTop.hom = 𝔭 := by
  obtain ⟨s, hs⟩ := S.isoSpec.hom.surjective ⟨𝔭, h𝔭⟩
  refine ⟨s, Ideal.ext fun r ↦ ?_⟩
  have h1 : s ∈ S.basicOpen r ↔ r ∉ 𝔭 := by
    rw [← Scheme.toSpecΓ_preimage_basicOpen]
    change S.isoSpec.hom s ∈ PrimeSpectrum.basicOpen r ↔ _
    rw [hs]
    rfl
  rw [RingHom.mem_ker, ← not_iff_not, ← h1]
  change ¬ (S.fromSpecResidueField s).app ⊤ r = 0 ↔ _
  rw [← basicOpen_eq_bot_iff, ← Scheme.preimage_basicOpen]
  constructor
  · intro h
    by_contra hs
    refine h (eq_bot_iff.mpr fun x hx ↦ hs ?_)
    have hx' : S.fromSpecResidueField s x ∈ S.basicOpen r := hx
    rwa [Scheme.fromSpecResidueField_apply] at hx'
  · intro h h'
    have : (default : Spec (S.residueField s)) ∈ S.fromSpecResidueField s ⁻¹ᵁ S.basicOpen r := by
      change S.fromSpecResidueField s default ∈ S.basicOpen r
      rwa [Scheme.fromSpecResidueField_apply]
    rw [h'] at this
    exact this

/- English proof (translation)
Establish `: IsNoetherianRing Γ(S, ⊤)` using `IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S⟩`. Proceed by induction on `I using IsNoetherian.induction generalizing h U with`. Consider the case `hgt I IH`. Distinguish the cases in `hI : I = ⊤`. Simplify using `[hI, Ideal.map_top]`.

Establish `: Nontrivial (Γ(S, ⊤) ⧸ I)` using `Ideal.Quotient.nontrivial_iff.mpr hI`. Take `⟨𝔭, h𝔭⟩` from `associatedPrimes.nonempty Γ(S, ⊤) (Γ(S, ⊤) ⧸ I)`. Take `⟨h𝔭, a, ha⟩` from `isAssociatedPrime_iff.mp h𝔭`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Establish `ha' : ∀ r, r ∈ 𝔭 ↔ r * a ∈ I`.

Introduce `r`. Rewrite using `[ha, Submodule.mem_colon_singleton, Submodule.mem_bot, ← Ideal.Quotient.eq_zero_iff_mem, map_mul]`. Both sides reduce to the same expression. Establish `haI : a ∉ I` using `fun h ↦ h𝔭.ne_top ((Ideal.eq_top_iff_one _).mpr ((ha' 1).mpr (by simpa)))`. Establish `hlt : I < I ⊔ Ideal.span {a}`.

Use `lt_of_le_of_ne le_sup_left fun h ↦ haI ?_` and prove the remaining obligations. Rewrite using `[h]`. Conclude with `Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)`. Establish `h1` using `IH _ hlt h (fun U V hVU ↦ Ideal.map_mono le_sup_left (hc U V hVU)) (fun U W hW ↦ Ideal.map_mono le_sup_left (hv U W hW))`. Establish `h2 : ∀ U : X.affineOpens, ∃ k : Γ(X, U.1), h U - p.appLE ⊤ U.1 (le_preimage_top p _) a * k ∈ Ideal.map (p.appLE ⊤ U.1 (le_preimage_top p _)).hom I`.

Introduce `U`. Use `h1 U` as an intermediate fact. Rewrite `this` using `[Ideal.map_sup, Ideal.map_span, Set.image_singleton, Submodule.mem_sup]`. Take `⟨y, hy, z, hz, hyz⟩` from `this`. Take `⟨k, rfl⟩` from `Ideal.mem_span_singleton'.mp hz`.

Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite using `[← hyz, mul_comm k]`. Simplify using `using hy`. Use `choose k hk using h2`. Take `⟨s, hs⟩` from `exists_ker_fromSpecResidueField 𝔭 h𝔭`.

Establish `h3` using `mem_map_ker_of_compatible (f := S.fromSpecResidueField s) (g := p.fiberι s) (q := p.fiberToSpecResidueField s) (.of_hasPullback _ _) default (hq s) he k ?_ ?_ U`. Rewrite `h3` using `[hs]`. Establish `h4 : p.appLE ⊤ U.1 (le_preimage_top p _) a * k U ∈ Ideal.map (p.appLE ⊤ U.1 (le_preimage_top p _)).hom I`. Establish `: Ideal.span {a} * 𝔭 ≤ I` using `Ideal.span_singleton_mul_le_iff.mpr fun r hr ↦ by`. Rewrite using `[mul_comm]`.

Conclude with `(ha' r).mp hr`. Use `Ideal.map_mono this ?_` and prove the remaining obligations. Rewrite using `[Ideal.map_mul]`. Conclude with `Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self a)) h3`. Simplify using `using Ideal.add_mem _ (hk U) h4`.

Introduce `U V hVU`. Rewrite using `[hs]`. Use `mem_map_of_mul_mem_map _ (p.flat_appLE (isAffineOpen_top S) V.2 _) I 𝔭 a (fun r ↦ (ha' r).mpr) _ ?_` and prove the remaining obligations. Establish `e1 : p.appLE ⊤ U.1 (le_preimage_top p _) ≫ X.presheaf.map (homOfLE hVU).op = p.appLE ⊤ V.1 (le_preimage_top p _)` using `Scheme.Hom.appLE_map _ _ _`. Establish `h4` using `map_mem_map_of_comp_eq e1 (hk U)`.

Rewrite `h4` using `[map_sub, map_mul, ← CommRingCat.comp_apply _ _ a, e1]`. Use `Ideal.add_mem _ (Ideal.sub_mem _ (hc U V hVU) h4) (hk V) using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Introduce `U W hW`. Rewrite using `[hs]`.

Use `mem_map_of_mul_mem_map _ (Scheme.Hom.flat_appLE (𝟙 S) (isAffineOpen_top S) W.2 _) I 𝔭 a (fun r ↦ (ha' r).mpr) _ ?_` and prove the remaining obligations. Establish `e1` using `appLE_comp_appLE_of_section he U.1 W.1 hW`. Establish `h4` using `map_mem_map_of_comp_eq e1 (hk U)`. Rewrite `h4` using `[map_sub, map_mul, ← CommRingCat.comp_apply _ _ a, e1]`. Use `Ideal.sub_mem _ (hv U W hW) h4 using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem mem_map_of_compatible {p : X ⟶ S} [IsAffine S] [IsLocallyNoetherian S] [Flat p]
    (hq : ∀ s : S, Function.Surjective (p.fiberToSpecResidueField s).appTop)
    {e : S ⟶ X} (he : e ≫ p = 𝟙 S) (I : Ideal Γ(S, ⊤))
    (h : ∀ U : X.affineOpens, Γ(X, U.1))
    (hc : ∀ (U V : X.affineOpens) (hVU : V.1 ≤ U.1),
      X.presheaf.map (homOfLE hVU).op (h U) - h V ∈
        I.map (p.appLE ⊤ V.1 (le_preimage_top p _)).hom)
    (hv : ∀ (U : X.affineOpens) (W : S.affineOpens) (hW : W.1 ≤ e ⁻¹ᵁ U.1),
      e.appLE U.1 W.1 hW (h U) ∈ I.map
        (Scheme.Hom.appLE (𝟙 S) ⊤ W.1 (le_preimage_top _ _)).hom)
    (U : X.affineOpens) :
    h U ∈ I.map (p.appLE ⊤ U.1 (le_preimage_top p _)).hom := by
  have : IsNoetherianRing Γ(S, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S⟩
  induction I using IsNoetherian.induction generalizing h U with
  | hgt I IH =>
  by_cases hI : I = ⊤
  · simp [hI, Ideal.map_top]
  have : Nontrivial (Γ(S, ⊤) ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  obtain ⟨𝔭, h𝔭⟩ := associatedPrimes.nonempty Γ(S, ⊤) (Γ(S, ⊤) ⧸ I)
  obtain ⟨h𝔭, a, ha⟩ := isAssociatedPrime_iff.mp h𝔭
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  have ha' : ∀ r, r ∈ 𝔭 ↔ r * a ∈ I := by
    intro r
    rw [ha, Submodule.mem_colon_singleton, Submodule.mem_bot, ← Ideal.Quotient.eq_zero_iff_mem,
      map_mul]
    rfl
  have haI : a ∉ I := fun h ↦ h𝔭.ne_top ((Ideal.eq_top_iff_one _).mpr ((ha' 1).mpr (by simpa)))
  have hlt : I < I ⊔ Ideal.span {a} := by
    refine lt_of_le_of_ne le_sup_left fun h ↦ haI ?_
    rw [h]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
  have h1 := IH _ hlt h (fun U V hVU ↦ Ideal.map_mono le_sup_left (hc U V hVU))
    (fun U W hW ↦ Ideal.map_mono le_sup_left (hv U W hW))
  have h2 : ∀ U : X.affineOpens, ∃ k : Γ(X, U.1),
      h U - p.appLE ⊤ U.1 (le_preimage_top p _) a * k ∈
        Ideal.map (p.appLE ⊤ U.1 (le_preimage_top p _)).hom I := by
    intro U
    have := h1 U
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, Submodule.mem_sup] at this
    obtain ⟨y, hy, z, hz, hyz⟩ := this
    obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    refine ⟨k, ?_⟩
    rw [← hyz, mul_comm k]
    simpa using hy
  choose k hk using h2
  obtain ⟨s, hs⟩ := exists_ker_fromSpecResidueField 𝔭 h𝔭
  have h3 := mem_map_ker_of_compatible (f := S.fromSpecResidueField s) (g := p.fiberι s)
    (q := p.fiberToSpecResidueField s) (.of_hasPullback _ _) default (hq s) he k ?_ ?_ U
  · rw [hs] at h3
    have h4 : p.appLE ⊤ U.1 (le_preimage_top p _) a * k U ∈
        Ideal.map (p.appLE ⊤ U.1 (le_preimage_top p _)).hom I := by
      have : Ideal.span {a} * 𝔭 ≤ I := Ideal.span_singleton_mul_le_iff.mpr fun r hr ↦ by
        rw [mul_comm]; exact (ha' r).mp hr
      refine Ideal.map_mono this ?_
      rw [Ideal.map_mul]
      exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self a)) h3
    simpa using Ideal.add_mem _ (hk U) h4
  · intro U V hVU
    rw [hs]
    refine mem_map_of_mul_mem_map _ (p.flat_appLE (isAffineOpen_top S) V.2 _) I 𝔭 a
      (fun r ↦ (ha' r).mpr) _ ?_
    have e1 : p.appLE ⊤ U.1 (le_preimage_top p _) ≫ X.presheaf.map (homOfLE hVU).op =
        p.appLE ⊤ V.1 (le_preimage_top p _) := Scheme.Hom.appLE_map _ _ _
    have h4 := map_mem_map_of_comp_eq e1 (hk U)
    rw [map_sub, map_mul, ← CommRingCat.comp_apply _ _ a, e1] at h4
    convert Ideal.add_mem _ (Ideal.sub_mem _ (hc U V hVU) h4) (hk V) using 1
    ring
  · intro U W hW
    rw [hs]
    refine mem_map_of_mul_mem_map _ (Scheme.Hom.flat_appLE (𝟙 S) (isAffineOpen_top S) W.2 _) I 𝔭 a
      (fun r ↦ (ha' r).mpr) _ ?_
    have e1 := appLE_comp_appLE_of_section he U.1 W.1 hW
    have h4 := map_mem_map_of_comp_eq e1 (hk U)
    rw [map_sub, map_mul, ← CommRingCat.comp_apply _ _ a, e1] at h4
    convert Ideal.sub_mem _ (hv U W hW) h4 using 1
    ring

/- English proof (translation)
Establish `h1 : p.appTop ≫ e.appTop = 𝟙 _`. Rewrite using `[← Scheme.Hom.comp_appTop, he, Scheme.Hom.id_appTop]`. Establish `h2 : Function.Injective e.appTop`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`.

Use `eq_zero_of_forall_affineOpens x fun U ↦ ?_` and prove the remaining obligations. Use `mem_map_of_compatible hq he ⊥ (fun U ↦ X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op x) ?_ ?_ U` as an intermediate fact. Simplify using `using this`. Introduce `U V hVU`. Rewrite using `[← CommRingCat.comp_apply, ← Functor.map_comp, Ideal.map_bot, Ideal.mem_bot, sub_eq_zero]`.

Both sides reduce to the same expression. Introduce `U W hW`. Rewrite using `[Ideal.map_bot, Ideal.mem_bot, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE, CommRingCat.comp_apply]`. Use `erw [hx]`. Conclude with `map_zero _`.

Establish `: Mono e.appTop` using `ConcreteCategory.mono_of_injective _ h2`. Conclude with `⟨e.appTop, h1, by rw [← cancel_mono e.appTop, Category.assoc, h1]; simp⟩`.
-/
theorem isIso_appTop_of_section_of_fiber (p : X ⟶ S) [IsAffine S] [IsLocallyNoetherian S] [Flat p]
    (hq : ∀ s : S, Function.Surjective (p.fiberToSpecResidueField s).appTop)
    {e : S ⟶ X} (he : e ≫ p = 𝟙 S) : IsIso p.appTop := by
  have h1 : p.appTop ≫ e.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, he, Scheme.Hom.id_appTop]
  have h2 : Function.Injective e.appTop := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    refine eq_zero_of_forall_affineOpens x fun U ↦ ?_
    have := mem_map_of_compatible hq he ⊥
      (fun U ↦ X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op x) ?_ ?_ U
    · simpa using this
    · intro U V hVU
      rw [← CommRingCat.comp_apply, ← Functor.map_comp, Ideal.map_bot, Ideal.mem_bot, sub_eq_zero]
      rfl
    · intro U W hW
      rw [Ideal.map_bot, Ideal.mem_bot, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE,
        Scheme.Hom.appLE, CommRingCat.comp_apply]
      erw [hx]
      exact map_zero _
  have : Mono e.appTop := ConcreteCategory.mono_of_injective _ h2
  exact ⟨e.appTop, h1, by rw [← cancel_mono e.appTop, Category.assoc, h1]; simp⟩

end Section

section Main

variable {X Y S T : Scheme.{u}}

/- English proof (translation)
Establish `h1 : ∀ i, IsIso (p.app (B i))`. Introduce `i`. Use `h i` as an intermediate fact. Rewrite `this` using `[morphismRestrict_appTop]`. Use `(@isIso_comp_right_iff _ _ _ _ _ (p.app ((B i).ι ''ᵁ ⊤)) _ (by rw [eqToHom_op]; exact Functor.map_isIso _ _)).mp this` as an intermediate fact.

Rewrite `this` using `[(B i).ι_image_top]`. Then use the resulting hypothesis. Set `φ : S.sheaf ⟶ (TopCat.Sheaf.pushforward _ p.base).obj X.sheaf` to `⟨p.c⟩`. Establish `: IsIso φ` using `TopCat.Sheaf.isIso_iff_isIso_basis hB h1`. Establish `: IsIso p.c` using `(TopCat.Sheaf.forget _ _).map_isIso φ`. Conclude with `inferInstanceAs (IsIso (p.c.app (op U)))`.
-/
theorem isIso_app_of_isBasis (p : X ⟶ S) {ι : Type*} (B : ι → S.Opens)
    (hB : TopologicalSpace.Opens.IsBasis (Set.range B))
    (h : ∀ i, IsIso (p ∣_ B i).appTop) (U : S.Opens) : IsIso (p.app U) := by
  have h1 : ∀ i, IsIso (p.app (B i)) := by
    intro i
    have := h i
    rw [morphismRestrict_appTop] at this
    have := (@isIso_comp_right_iff _ _ _ _ _ (p.app ((B i).ι ''ᵁ ⊤)) _
      (by rw [eqToHom_op]; exact Functor.map_isIso _ _)).mp this
    rwa [(B i).ι_image_top] at this
  let φ : S.sheaf ⟶ (TopCat.Sheaf.pushforward _ p.base).obj X.sheaf := ⟨p.c⟩
  have : IsIso φ := TopCat.Sheaf.isIso_iff_isIso_basis hB h1
  have : IsIso p.c := (TopCat.Sheaf.forget _ _).map_isIso φ
  exact inferInstanceAs (IsIso (p.c.app (op U)))

/- English proof (translation)
The claim follows from `isIso_app_of_isBasis p (fun U : S.affineOpens ↦ U.1) (by simpa using S.isBasis_affineOpens) h U`.
-/
theorem isIso_app_of_forall_affineOpens (p : X ⟶ S)
    (h : ∀ U : S.affineOpens, IsIso (p ∣_ U.1).appTop) (U : S.Opens) : IsIso (p.app U) :=
  isIso_app_of_isBasis p (fun U : S.affineOpens ↦ U.1) (by simpa using S.isBasis_affineOpens) h U

/- English proof (translation)
The claim follows from `have := isIso_appTop_of_field p isIso_appTop_of_isPullback H`.
-/
theorem isIso_appTop_baseChange_of_field {k : Type u} [Field k] {p : X ⟶ Spec (.of k)}
    {f : T ⟶ Spec (.of k)} {g : Y ⟶ X} {q : Y ⟶ T} (H : IsPullback g q p f) [IsAffine T]
    [GeometricallyIntegral p] [UniversallyClosed p] [QuasiSeparated p] : IsIso q.appTop :=
  have := isIso_appTop_of_field p
  isIso_appTop_of_isPullback H

/- English proof (translation)
The claim follows from `isIso_app_of_forall_affineOpens q (fun V ↦ have : IsAffine V.1 := V.2 isIso_appTop_baseChange_of_field ((isPullback_morphismRestrict q V.1).flip.paste_horiz H)) U`.
-/
theorem isIso_app_baseChange_of_field {k : Type u} [Field k] {p : X ⟶ Spec (.of k)}
    {f : T ⟶ Spec (.of k)} {g : Y ⟶ X} {q : Y ⟶ T} (H : IsPullback g q p f)
    [GeometricallyIntegral p] [UniversallyClosed p] [QuasiSeparated p] (U : T.Opens) :
    IsIso (q.app U) :=
  isIso_app_of_forall_affineOpens q (fun V ↦
    have : IsAffine V.1 := V.2
    isIso_appTop_baseChange_of_field ((isPullback_morphismRestrict q V.1).flip.paste_horiz H)) U

/- English proof (translation)
Establish `: UniversallyClosed q` using `MorphismProperty.of_isPullback H ‹_›`. Use `isIso_appTop_of_field q` as an intermediate fact. Set `F` to `(Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop`. Set `G` to `g.appTop ≫ inv q.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom`. Establish `hF : F.hom.IsIntegral`.

Apply `RingHom.isIntegral_respectsIso.2 (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)` to reduce the goal to its premises. Conclude with `isIntegral_appTop_of_universallyClosed p`. Establish `hFG : F ≫ G = CommRingCat.ofHom (algebraMap R K)`. Simplify using `only [F, G, Category.assoc]`. Rewrite using `[← Category.assoc p.appTop, ← Scheme.Hom.comp_appTop, H.w, Scheme.Hom.comp_appTop, Category.assoc, IsIso.hom_inv_id_assoc, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]`.

Establish `hg : Function.Injective g.appTop`. Use `injective_appTop_of_isPullback H ?_` and prove the remaining obligations. Establish `: Mono (CommRingCat.ofHom (algebraMap R K))` using `ConcreteCategory.mono_of_injective _ (IsFractionRing.injective R K)`. Establish `: Mono ((Spec.map (CommRingCat.ofHom (algebraMap R K))).appTop ≫ (Scheme.ΓSpecIso (.of K)).hom)`. Rewrite using `[Scheme.ΓSpecIso_naturality]`.

Use `infer_instance`. Use `mono_of_mono (Spec.map (CommRingCat.ofHom (algebraMap R K))).appTop (Scheme.ΓSpecIso (.of K)).hom` as an intermediate fact. Conclude with `ConcreteCategory.injective_of_mono_of_preservesPullback _`. Establish `hG : Function.Injective G`. Establish `: Mono g.appTop` using `ConcreteCategory.mono_of_injective _ hg`.

Establish `: Mono G` using `by unfold G; infer_instance`. Conclude with `ConcreteCategory.injective_of_mono_of_preservesPullback _`. Establish `hFG' : ∀ r : R, G (F r) = algebraMap R K r` using `fun r ↦ congr($hFG r)`. Establish `: IsIso F`. Use `(ConcreteCategory.isIso_iff_bijective F).mpr ⟨fun a b hab ↦ ?_, fun x ↦ ?_⟩` and prove the remaining obligations.

Conclude with `IsFractionRing.injective R K (by rw [← hFG', ← hFG', hab])`. Establish `hx : IsIntegral R (G x : K)`. Take `⟨P, hP, hPx⟩` from `hF x`. Use `⟨P, hP, ?_⟩` and prove the remaining obligations. Use `congr(G.hom $hPx)` as an intermediate fact.

Rewrite `this` using `[Polynomial.hom_eval₂, map_zero, ← CommRingCat.hom_comp, hFG]`. Conclude with `this`. Take `⟨r, hr⟩` from `IsIntegrallyClosed.algebraMap_eq_of_integral hx`. Conclude with `⟨r, hG ((hFG' r).trans hr)⟩`. Conclude with `IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of R)).inv p.appTop`.
-/
theorem isIso_appTop_of_isIntegrallyClosed {R K : Type u} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K] {p : X ⟶ Spec (.of R)}
    {g : Y ⟶ X} {q : Y ⟶ Spec (.of K)}
    (H : IsPullback g q p (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    [Flat p] [UniversallyClosed p] [GeometricallyIntegral q] : IsIso p.appTop := by
  have : UniversallyClosed q := MorphismProperty.of_isPullback H ‹_›
  have := isIso_appTop_of_field q
  let F := (Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop
  let G := g.appTop ≫ inv q.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom
  have hF : F.hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2 (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed p
  have hFG : F ≫ G = CommRingCat.ofHom (algebraMap R K) := by
    simp only [F, G, Category.assoc]
    rw [← Category.assoc p.appTop, ← Scheme.Hom.comp_appTop, H.w, Scheme.Hom.comp_appTop,
      Category.assoc, IsIso.hom_inv_id_assoc, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  have hg : Function.Injective g.appTop := by
    refine injective_appTop_of_isPullback H ?_
    have : Mono (CommRingCat.ofHom (algebraMap R K)) :=
      ConcreteCategory.mono_of_injective _ (IsFractionRing.injective R K)
    have : Mono ((Spec.map (CommRingCat.ofHom (algebraMap R K))).appTop ≫
        (Scheme.ΓSpecIso (.of K)).hom) := by
      rw [Scheme.ΓSpecIso_naturality]; infer_instance
    have := mono_of_mono (Spec.map (CommRingCat.ofHom (algebraMap R K))).appTop
      (Scheme.ΓSpecIso (.of K)).hom
    exact ConcreteCategory.injective_of_mono_of_preservesPullback _
  have hG : Function.Injective G := by
    have : Mono g.appTop := ConcreteCategory.mono_of_injective _ hg
    have : Mono G := by unfold G; infer_instance
    exact ConcreteCategory.injective_of_mono_of_preservesPullback _
  have hFG' : ∀ r : R, G (F r) = algebraMap R K r := fun r ↦ congr($hFG r)
  have : IsIso F := by
    refine (ConcreteCategory.isIso_iff_bijective F).mpr ⟨fun a b hab ↦ ?_, fun x ↦ ?_⟩
    · exact IsFractionRing.injective R K (by rw [← hFG', ← hFG', hab])
    · have hx : IsIntegral R (G x : K) := by
        obtain ⟨P, hP, hPx⟩ := hF x
        refine ⟨P, hP, ?_⟩
        have := congr(G.hom $hPx)
        rw [Polynomial.hom_eval₂, map_zero, ← CommRingCat.hom_comp, hFG] at this
        exact this
      obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hx
      exact ⟨r, hG ((hFG' r).trans hr)⟩
  exact IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of R)).inv p.appTop

/- English proof (translation)
Use `isIso_appTop_of_section_of_fiber p (fun s ↦ ?_) he` and prove the remaining obligations. Establish `: UniversallyClosed (p.fiberToSpecResidueField s)` using `inferInstanceAs (UniversallyClosed (pullback.snd p (S.fromSpecResidueField s)))`. Use `isIso_appTop_of_field (k := S.residueField s) (p.fiberToSpecResidueField s)` as an intermediate fact. Conclude with `(ConcreteCategory.bijective_of_isIso _).2`.
-/
theorem isIso_appTop_of_section (p : X ⟶ S) [IsAffine S] [IsLocallyNoetherian S] [Flat p]
    [UniversallyClosed p] [GeometricallyIntegral p] {e : S ⟶ X} (he : e ≫ p = 𝟙 S) :
    IsIso p.appTop := by
  refine isIso_appTop_of_section_of_fiber p (fun s ↦ ?_) he
  have : UniversallyClosed (p.fiberToSpecResidueField s) :=
    inferInstanceAs (UniversallyClosed (pullback.snd p (S.fromSpecResidueField s)))
  have := isIso_appTop_of_field (k := S.residueField s) (p.fiberToSpecResidueField s)
  exact (ConcreteCategory.bijective_of_isIso _).2

/- English proof (translation)
Establish `: CompactSpace X` using `QuasiCompact.compactSpace_of_compactSpace p`. Use `HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale)` as an intermediate fact. Establish `: MorphismProperty.ContainsIdentities @Etale.{u}` using `⟨fun _ ↦ inferInstance⟩`. Take `⟨T, i, _, hi, _⟩` from `X.exists_hom_isAffine_of_isZariskiLocalAtSource @Etale`. Establish `: IsLocallyNoetherian T` using `LocallyOfFiniteType.isLocallyNoetherian (i ≫ p)`.

Use `isIso_appTop_of_section (pullback.snd p (i ≫ p)) (e := pullback.lift i (𝟙 T) (by simp)) (pullback.lift_snd _ _ _)` as an intermediate fact. Conclude with `isIso_appTop_of_isPullback_of_surjective (.of_hasPullback p (i ≫ p))`.
-/
theorem isIso_appTop_of_isAffine (p : X ⟶ S) [IsAffine S] [IsLocallyNoetherian S] [Flat p]
    [UniversallyClosed p] [LocallyOfFiniteType p] [GeometricallyIntegral p] :
    IsIso p.appTop := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale)
  have : MorphismProperty.ContainsIdentities @Etale.{u} := ⟨fun _ ↦ inferInstance⟩
  obtain ⟨T, i, _, hi, _⟩ := X.exists_hom_isAffine_of_isZariskiLocalAtSource @Etale
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (i ≫ p)
  have := isIso_appTop_of_section (pullback.snd p (i ≫ p)) (e := pullback.lift i (𝟙 T) (by simp))
    (pullback.lift_snd _ _ _)
  exact isIso_appTop_of_isPullback_of_surjective (.of_hasPullback p (i ≫ p))

/- English proof (translation)
The claim follows from `isIso_app_of_forall_affineOpens p (fun V ↦ have : IsAffine V.1 := V.2 isIso_appTop_of_isAffine (p ∣_ V.1)) U`.
-/
theorem isIso_app (p : X ⟶ S) [IsLocallyNoetherian S] [Flat p]
    [UniversallyClosed p] [LocallyOfFiniteType p] [GeometricallyIntegral p] (U : S.Opens) :
    IsIso (p.app U) :=
  isIso_app_of_forall_affineOpens p (fun V ↦
    have : IsAffine V.1 := V.2
    isIso_appTop_of_isAffine (p ∣_ V.1)) U

end Main

section Limit

variable {X Y S T : Scheme.{u}}

/- English proof (translation)
Set `F : Finset A ⥤ CommRingCat.{u}` to `{ obj s := .of (Algebra.adjoin R (s : Set A)) map {s t} h := CommRingCat.ofHom (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.mpr h.le))).toRingHom }`. Set `cF : Cocone F` to `{ pt := .of A ι := { app s := CommRingCat.ofHom (Algebra.adjoin R (s : Set A)).val.toRingHom } }`. Establish `: ReflectsFilteredColimits (forget CommRingCat.{u})` using `⟨fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms⟩`. Establish `hcF : IsColimit cF` using `isColimitOfReflects (forget _) (Types.FilteredColimit.isColimitOf' _ _ (fun x ↦ by`. Set `x' : A` to `x`.

Conclude with `⟨({x'} : Finset A), (⟨x', Algebra.subset_adjoin (by simp)⟩ : Algebra.adjoin R (({x'} : Finset A) : Set A)), rfl⟩)`. Use the proof step `(fun i x y hxy ↦ ⟨i, 𝟙 i, congrArg _ (Subtype.ext hxy)⟩))`. Set `G : (Finset A)ᵒᵖ ⥤ Scheme.{u}` to `F.op ⋙ Scheme.Spec`. Set `cG : Cone G` to `Scheme.Spec.mapCone cF.op`. Establish `hcG : IsLimit cG` using `isLimitOfPreserves Scheme.Spec hcF.op`.

Set `ι (s : (Finset A)ᵒᵖ) : G.obj s ⟶ Spec (.of R)` to `Spec.map (CommRingCat.ofHom (algebraMap R (Algebra.adjoin R (s.unop : Set A))))`. Establish `hι {s t : (Finset A)ᵒᵖ} (f : s ⟶ t) : G.map f ≫ ι t = ι s`. Express the relevant statement in the definitionally equal form `Spec.map _ ≫ Spec.map _ = Spec.map _`. Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.

Establish `hι' (s : (Finset A)ᵒᵖ) : cG.π.app s ≫ ι s = Spec.map (CommRingCat.ofHom (algebraMap R A))`. Express the relevant statement in the definitionally equal form `Spec.map _ ≫ Spec.map _ = Spec.map _`. Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression. Apply the tactic sequence `let D : (Finset A)ᵒᵖ ⥤ Scheme.{u} := { obj s := pullback p (ι s) map {s t} f := pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ G.map f) (by rw [Category.assoc, hι, pullback.condition]) map_id s := by apply pullback.hom_ext <;> simp map_comp f f' := by`.

Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[pullback.lift_fst, Category.assoc, pullback.lift_fst, pullback.lift_fst]`. Rewrite using `[pullback.lift_snd, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, G.map_comp, Category.assoc] }`. Set `α : D ⟶ G` to `{ app s := pullback.snd p (ι s) naturality s t f := pullback.lift_snd _ _ _ }`. Set `π (s : (Finset A)ᵒᵖ) : Y ⟶ pullback p (ι s)` to `pullback.lift g (q ≫ cG.π.app s) (by rw [Category.assoc, hι', H.w])`.

Set `cD : Cone D` to `{ pt := Y π := { app := π naturality s t f := by`. Express the relevant statement in the definitionally equal form `𝟙 Y ≫ π t = π s ≫ pullback.lift _ _ _`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.id_comp, Category.assoc, pullback.lift_fst, pullback.lift_fst, pullback.lift_fst]`. Rewrite using `[Category.id_comp, Category.assoc, pullback.lift_snd, pullback.lift_snd, pullback.lift_snd_assoc, Category.assoc, cG.w f] } }`.

Establish `hπ (s : (Finset A)ᵒᵖ) : IsPullback (π s) q (pullback.snd p (ι s)) (cG.π.app s)`. Use `IsPullback.of_right (h₁₂ := pullback.fst p (ι s)) (v₁₃ := p) (h₂₂ := ι s) ?_ (pullback.lift_snd _ _ _) (.of_hasPullback _ _)` and prove the remaining obligations. Rewrite using `[hι', pullback.lift_fst]`. Conclude with `H`. Establish `hcD : IsLimit cD` using `isLimitOfIsPullbackOfIsConnected α cD cG { hom := q, w s := (pullback.lift_snd _ _ _).symm } hπ hcG`.

Establish `hG (s : (Finset A)ᵒᵖ) : IsAffine (G.obj s)` using `inferInstanceAs (IsAffine (Spec _))`. Establish `{s t : (Finset A)ᵒᵖ} (f : s ⟶ t) : IsAffineHom (D.map f)`. Establish `: IsPullback (D.map f) (pullback.snd p (ι s)) (pullback.snd p (ι t)) (G.map f)`. Use `IsPullback.of_right (h₁₂ := pullback.fst p (ι t)) (v₁₃ := p) (h₂₂ := ι t) ?_ (pullback.lift_snd _ _ _) (.of_hasPullback _ _)` and prove the remaining obligations. Rewrite using `[hι, pullback.lift_fst]`.

Conclude with `.of_hasPullback _ _`. Conclude with `MorphismProperty.of_isPullback this.flip inferInstance`. Establish `(s : (Finset A)ᵒᵖ) : CompactSpace (D.obj s)` using `QuasiCompact.compactSpace_of_compactSpace (pullback.snd p (ι s))`. Establish `(s : (Finset A)ᵒᵖ) : QuasiSeparatedSpace (D.obj s)` using `(quasiSeparated_iff_quasiSeparatedSpace (pullback.snd p (ι s))).mp inferInstance`. Introduce `x`.

Take `⟨s, y, rfl⟩` from `exists_appTop_π_eq_of_isLimit D cD hcD x`. Establish `: Algebra.FiniteType R (Algebra.adjoin R (s.unop : Set A))` using `Algebra.FiniteType.adjoin_of_finite s.unop.finite_toSet`. Take `⟨b, rfl⟩` from `h (Algebra.adjoin R (s.unop : Set A)) y`. Use `⟨(cG.π.app s).appTop b, ?_⟩` and prove the remaining obligations. Use `congr(($((hπ s).w)).appTop b)` as an intermediate fact.

Simplify using `only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at this`. Conclude with `this.symm`.
-/
theorem surjective_appTop_of_forall_finiteType {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] {p : X ⟶ Spec (.of R)} [QuasiCompact p] [QuasiSeparated p]
    (h : ∀ (B : Type u) [CommRing B] [Algebra R B] [Algebra.FiniteType R B], Function.Surjective
      (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap R B)))).appTop)
    {g : Y ⟶ X} {q : Y ⟶ Spec (.of A)}
    (H : IsPullback g q p (Spec.map (CommRingCat.ofHom (algebraMap R A)))) :
    Function.Surjective q.appTop := by
  classical
  let F : Finset A ⥤ CommRingCat.{u} :=
    { obj s := .of (Algebra.adjoin R (s : Set A))
      map {s t} h := CommRingCat.ofHom
        (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.mpr h.le))).toRingHom }
  let cF : Cocone F :=
    { pt := .of A
      ι := { app s := CommRingCat.ofHom (Algebra.adjoin R (s : Set A)).val.toRingHom } }
  have : ReflectsFilteredColimits (forget CommRingCat.{u}) :=
    ⟨fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms⟩
  have hcF : IsColimit cF := isColimitOfReflects (forget _)
    (Types.FilteredColimit.isColimitOf' _ _
      (fun x ↦ by
        let x' : A := x
        exact ⟨({x'} : Finset A), (⟨x', Algebra.subset_adjoin (by simp)⟩ :
          Algebra.adjoin R (({x'} : Finset A) : Set A)), rfl⟩)
      (fun i x y hxy ↦ ⟨i, 𝟙 i, congrArg _ (Subtype.ext hxy)⟩))
  let G : (Finset A)ᵒᵖ ⥤ Scheme.{u} := F.op ⋙ Scheme.Spec
  let cG : Cone G := Scheme.Spec.mapCone cF.op
  have hcG : IsLimit cG := isLimitOfPreserves Scheme.Spec hcF.op
  let ι (s : (Finset A)ᵒᵖ) : G.obj s ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R (Algebra.adjoin R (s.unop : Set A))))
  have hι {s t : (Finset A)ᵒᵖ} (f : s ⟶ t) : G.map f ≫ ι t = ι s := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  have hι' (s : (Finset A)ᵒᵖ) :
      cG.π.app s ≫ ι s = Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  let D : (Finset A)ᵒᵖ ⥤ Scheme.{u} :=
    { obj s := pullback p (ι s)
      map {s t} f := pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ G.map f)
        (by rw [Category.assoc, hι, pullback.condition])
      map_id s := by apply pullback.hom_ext <;> simp
      map_comp f f' := by
        apply pullback.hom_ext
        · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, pullback.lift_fst]
        · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
            G.map_comp, Category.assoc] }
  let α : D ⟶ G :=
    { app s := pullback.snd p (ι s)
      naturality s t f := pullback.lift_snd _ _ _ }
  let π (s : (Finset A)ᵒᵖ) : Y ⟶ pullback p (ι s) :=
    pullback.lift g (q ≫ cG.π.app s) (by rw [Category.assoc, hι', H.w])
  let cD : Cone D :=
    { pt := Y
      π :=
        { app := π
          naturality s t f := by
            change 𝟙 Y ≫ π t = π s ≫ pullback.lift _ _ _
            apply pullback.hom_ext
            · rw [Category.id_comp, Category.assoc, pullback.lift_fst, pullback.lift_fst,
                pullback.lift_fst]
            · rw [Category.id_comp, Category.assoc, pullback.lift_snd, pullback.lift_snd,
                pullback.lift_snd_assoc, Category.assoc, cG.w f] } }
  have hπ (s : (Finset A)ᵒᵖ) : IsPullback (π s) q (pullback.snd p (ι s)) (cG.π.app s) := by
    refine IsPullback.of_right (h₁₂ := pullback.fst p (ι s)) (v₁₃ := p) (h₂₂ := ι s) ?_
      (pullback.lift_snd _ _ _) (.of_hasPullback _ _)
    rw [hι', pullback.lift_fst]
    exact H
  have hcD : IsLimit cD := isLimitOfIsPullbackOfIsConnected α cD cG
    { hom := q, w s := (pullback.lift_snd _ _ _).symm } hπ hcG
  have hG (s : (Finset A)ᵒᵖ) : IsAffine (G.obj s) := inferInstanceAs (IsAffine (Spec _))
  have {s t : (Finset A)ᵒᵖ} (f : s ⟶ t) : IsAffineHom (D.map f) := by
    have : IsPullback (D.map f) (pullback.snd p (ι s)) (pullback.snd p (ι t)) (G.map f) := by
      refine IsPullback.of_right (h₁₂ := pullback.fst p (ι t)) (v₁₃ := p) (h₂₂ := ι t) ?_
        (pullback.lift_snd _ _ _) (.of_hasPullback _ _)
      rw [hι, pullback.lift_fst]
      exact .of_hasPullback _ _
    exact MorphismProperty.of_isPullback this.flip inferInstance
  have (s : (Finset A)ᵒᵖ) : CompactSpace (D.obj s) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd p (ι s))
  have (s : (Finset A)ᵒᵖ) : QuasiSeparatedSpace (D.obj s) :=
    (quasiSeparated_iff_quasiSeparatedSpace (pullback.snd p (ι s))).mp inferInstance
  intro x
  obtain ⟨s, y, rfl⟩ := exists_appTop_π_eq_of_isLimit D cD hcD x
  have : Algebra.FiniteType R (Algebra.adjoin R (s.unop : Set A)) :=
    Algebra.FiniteType.adjoin_of_finite s.unop.finite_toSet
  obtain ⟨b, rfl⟩ := h (Algebra.adjoin R (s.unop : Set A)) y
  refine ⟨(cG.π.app s).appTop b, ?_⟩
  have := congr(($((hπ s).w)).appTop b)
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at this
  exact this.symm

/- English proof (translation)
Establish `: CompactSpace X` using `QuasiCompact.compactSpace_of_compactSpace p`. Use `HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat)` as an intermediate fact. Establish `: MorphismProperty.ContainsIdentities @Flat.{u}` using `⟨fun _ ↦ inferInstance⟩`. Take `⟨T, i, _, hi, _⟩` from `X.exists_hom_isAffine_of_isZariskiLocalAtSource @Flat`. Use `((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine (i ≫ p)).mp ⟨inferInstance, inferInstance⟩).injective` as an intermediate fact.

Rewrite `this` using `[Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]`. Conclude with `this.of_comp`.
-/
theorem injective_appTop_of_flat_of_surjective (p : X ⟶ S) [IsAffine S] [Flat p] [Surjective p]
    [QuasiCompact p] : Function.Injective p.appTop := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat)
  have : MorphismProperty.ContainsIdentities @Flat.{u} := ⟨fun _ ↦ inferInstance⟩
  obtain ⟨T, i, _, hi, _⟩ := X.exists_hom_isAffine_of_isZariskiLocalAtSource @Flat
  have := ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine (i ≫ p)).mp
    ⟨inferInstance, inferInstance⟩).injective
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp] at this
  exact this.of_comp

/- English proof (translation)
Establish `: Flat q` using `MorphismProperty.of_isPullback H ‹_›`. Establish `: Surjective q` using `MorphismProperty.of_isPullback H inferInstance`. Establish `: QuasiCompact q` using `MorphismProperty.of_isPullback H inferInstance`. Use `(ConcreteCategory.isIso_iff_bijective _).mpr ⟨injective_appTop_of_flat_of_surjective q, ?_⟩` and prove the remaining obligations. Establish `: IsNoetherianRing Γ(S, ⊤)` using `IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S⟩`.

Use `algebraize [f.appTop.hom]`. Establish `H' : IsPullback g (q ≫ T.isoSpec.hom) (p ≫ S.isoSpec.hom) (Spec.map f.appTop)` using `H.of_iso (.refl _) (.refl _) T.isoSpec S.isoSpec (by simp) (by simp) (by simp) (Scheme.isoSpec_hom_naturality f).symm`. Establish `: GeometricallyIntegral (p ≫ S.isoSpec.hom)` using `MorphismProperty.of_isPullback (P := @GeometricallyIntegral) (IsPullback.of_horiz_isIso (fst := 𝟙 X) (f := p) (g := S.isoSpec.inv) ⟨by simp⟩) ‹_›`. Use `surjective_appTop_of_forall_finiteType (R := Γ(S, ⊤)) (A := Γ(T, ⊤)) (p := p ≫ S.isoSpec.hom) (fun B _ _ _ ↦ by` as an intermediate fact. Establish `: IsNoetherianRing B` using `Algebra.FiniteType.isNoetherianRing Γ(S, ⊤) B`.

Use `isIso_appTop_of_isAffine (pullback.snd (p ≫ S.isoSpec.hom) (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) B))))` as an intermediate fact. Conclude with `(ConcreteCategory.bijective_of_isIso _).2) H'`. Rewrite `this` using `[Scheme.Hom.comp_appTop]`. Introduce `x`. Take `⟨y, rfl⟩` from `this x`.

Conclude with `⟨_, rfl⟩`.
-/
theorem isIso_appTop_baseChange {p : X ⟶ S} {f : T ⟶ S} {g : Y ⟶ X} {q : Y ⟶ T}
    (H : IsPullback g q p f) [IsAffine S] [IsAffine T] [IsLocallyNoetherian S] [Flat p]
    [IsProper p] [GeometricallyIntegral p] : IsIso q.appTop := by
  have : Flat q := MorphismProperty.of_isPullback H ‹_›
  have : Surjective q := MorphismProperty.of_isPullback H inferInstance
  have : QuasiCompact q := MorphismProperty.of_isPullback H inferInstance
  refine (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨injective_appTop_of_flat_of_surjective q, ?_⟩
  have : IsNoetherianRing Γ(S, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S⟩
  algebraize [f.appTop.hom]
  have H' : IsPullback g (q ≫ T.isoSpec.hom) (p ≫ S.isoSpec.hom) (Spec.map f.appTop) :=
    H.of_iso (.refl _) (.refl _) T.isoSpec S.isoSpec (by simp) (by simp) (by simp)
      (Scheme.isoSpec_hom_naturality f).symm
  have : GeometricallyIntegral (p ≫ S.isoSpec.hom) :=
    MorphismProperty.of_isPullback (P := @GeometricallyIntegral)
      (IsPullback.of_horiz_isIso (fst := 𝟙 X) (f := p) (g := S.isoSpec.inv) ⟨by simp⟩) ‹_›
  have := surjective_appTop_of_forall_finiteType (R := Γ(S, ⊤)) (A := Γ(T, ⊤))
    (p := p ≫ S.isoSpec.hom) (fun B _ _ _ ↦ by
      have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing Γ(S, ⊤) B
      have := isIso_appTop_of_isAffine (pullback.snd (p ≫ S.isoSpec.hom)
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) B))))
      exact (ConcreteCategory.bijective_of_isIso _).2) H'
  rw [Scheme.Hom.comp_appTop] at this
  intro x
  obtain ⟨y, rfl⟩ := this x
  exact ⟨_, rfl⟩

/- English proof (translation)
The claim follows from `ConcreteCategory.bijective_of_isIso _`.
-/
theorem bijective_of_isIso_appTop {R : CommRingCat.{u}} (p : X ⟶ Spec R) [IsIso p.appTop] :
    Function.Bijective ((Scheme.ΓSpecIso R).inv ≫ p.appTop) :=
  ConcreteCategory.bijective_of_isIso _

end Limit

section Summary

/- English proof (translation)
Use `⟨fun k _ X p _ _ ↦ ⟨?_, fun A _ _ ↦ ?_⟩, fun R _ _ _ X p _ _ _ ↦ ?_, fun R _ _ X p _ _ _ ↦ ⟨?_, fun A _ _ ↦ ?_⟩⟩` and prove the remaining obligations. Use `isIso_appTop_of_field p` as an intermediate fact. Conclude with `bijective_of_isIso_appTop p`. Use `isIso_appTop_baseChange_of_field (IsPullback.of_hasPullback p (Spec.map (CommRingCat.ofHom (algebraMap k A))))` as an intermediate fact. Conclude with `bijective_of_isIso_appTop _`.

Use `isIso_appTop_of_isIntegrallyClosed (IsPullback.of_hasPullback p (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))` as an intermediate fact. Conclude with `bijective_of_isIso_appTop p`. Use `isIso_appTop_of_isAffine p` as an intermediate fact. Conclude with `bijective_of_isIso_appTop p`. Use `isIso_appTop_baseChange (IsPullback.of_hasPullback p (Spec.map (CommRingCat.ofHom (algebraMap R A))))` as an intermediate fact.

Conclude with `bijective_of_isIso_appTop _`.
-/
theorem functions_of_isProper :
    (∀ (k : Type u) [Field k] (X : Scheme.{u}) (p : X ⟶ Spec (.of k)) [IsProper p]
      [GeometricallyIntegral p],
        Function.Bijective ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop) ∧
        ∀ (A : Type u) [CommRing A] [Algebra k A],
          Function.Bijective ((Scheme.ΓSpecIso (.of A)).inv ≫
            (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop)) ∧
    (∀ (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (X : Scheme.{u})
      (p : X ⟶ Spec (.of R)) [IsProper p] [Flat p] [GeometricallyIntegral
        (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))],
        Function.Bijective ((Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop)) ∧
    (∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (X : Scheme.{u}) (p : X ⟶ Spec (.of R))
      [IsProper p] [Flat p] [GeometricallyIntegral p],
        Function.Bijective ((Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop) ∧
        ∀ (A : Type u) [CommRing A] [Algebra R A],
          Function.Bijective ((Scheme.ΓSpecIso (.of A)).inv ≫
            (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap R A)))).appTop)) := by
  refine ⟨fun k _ X p _ _ ↦ ⟨?_, fun A _ _ ↦ ?_⟩, fun R _ _ _ X p _ _ _ ↦ ?_,
    fun R _ _ X p _ _ _ ↦ ⟨?_, fun A _ _ ↦ ?_⟩⟩
  · have := isIso_appTop_of_field p
    exact bijective_of_isIso_appTop p
  · have := isIso_appTop_baseChange_of_field
      (IsPullback.of_hasPullback p (Spec.map (CommRingCat.ofHom (algebraMap k A))))
    exact bijective_of_isIso_appTop _
  · have := isIso_appTop_of_isIntegrallyClosed (IsPullback.of_hasPullback p
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))
    exact bijective_of_isIso_appTop p
  · have := isIso_appTop_of_isAffine p
    exact bijective_of_isIso_appTop p
  · have := isIso_appTop_baseChange
      (IsPullback.of_hasPullback p (Spec.map (CommRingCat.ofHom (algebraMap R A))))
    exact bijective_of_isIso_appTop _

end Summary

end ProperFunctions

end GlobalTheory
