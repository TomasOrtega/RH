import Mathlib
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open IsLocalRing TensorProduct

namespace GlobalTheory.GeomRegFibTransport
open ReciprocityTheory.AnForm.R.FinalTheorems

/- English proof (translation)
Use `⟨Algebra.EssFiniteType.subalgebra ℤ A, inferInstance, inferInstance, (maximalIdeal A).comap (algebraMap (Algebra.EssFiniteType.subalgebra ℤ A) A), inferInstance, ?_⟩` and prove the remaining obligations. Establish `hsub : Algebra.EssFiniteType.submonoid ℤ A = ((maximalIdeal A).comap (algebraMap (Algebra.EssFiniteType.subalgebra ℤ A) A)).primeCompl`. Use extensionality with `x`. Simplify using `[Algebra.EssFiniteType.submonoid, Ideal.primeCompl, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, IsUnit.mem_submonoid_iff]`. Establish `hloc` using `Algebra.EssFiniteType.isLocalization ℤ A`.

Rewrite `hloc` using `[hsub]`. Use `haveI : IsLocalization.AtPrime A ((maximalIdeal A).comap (algebraMap (Algebra.EssFiniteType.subalgebra ℤ A) A)) := hloc`. Conclude with `⟨(IsLocalization.algEquiv ((maximalIdeal A).comap (algebraMap (Algebra.EssFiniteType.subalgebra ℤ A) A)).primeCompl (Localization.AtPrime _) A).toRingEquiv⟩`.
-/
theorem exists_loc (A : Type) [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A] :
    ∃ (A₀ : Type) (_ : CommRing A₀) (_ : Algebra.FiniteType ℤ A₀) (p : Ideal A₀) (_ : p.IsPrime),
      Nonempty (Localization.AtPrime p ≃+* A) := by
  refine ⟨Algebra.EssFiniteType.subalgebra ℤ A, inferInstance, inferInstance,
    (maximalIdeal A).comap (algebraMap (Algebra.EssFiniteType.subalgebra ℤ A) A), inferInstance, ?_⟩
  have hsub : Algebra.EssFiniteType.submonoid ℤ A =
      ((maximalIdeal A).comap (algebraMap (Algebra.EssFiniteType.subalgebra ℤ A) A)).primeCompl := by
    ext x
    simp [Algebra.EssFiniteType.submonoid, Ideal.primeCompl, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, IsUnit.mem_submonoid_iff]
  have hloc := Algebra.EssFiniteType.isLocalization ℤ A
  rw [hsub] at hloc
  haveI : IsLocalization.AtPrime A ((maximalIdeal A).comap (algebraMap (Algebra.EssFiniteType.subalgebra ℤ A) A)) := hloc
  exact ⟨(IsLocalization.algEquiv ((maximalIdeal A).comap (algebraMap (Algebra.EssFiniteType.subalgebra ℤ A) A)).primeCompl
    (Localization.AtPrime _) A).toRingEquiv⟩

/- English proof (translation)
Proceed by induction on `x using AdicCompletion.induction_on with`. Consider the case `h a`. Simplify using `only [AdicCompletion.evalₐ_mk]`. Rewrite using `[Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, AdicCompletion.Ideal.mk_eq_mk I hle]`.
-/
theorem evalₐ_factorPow {R : Type} [CommRing R] (I : Ideal R) {m n : ℕ} (hle : m ≤ n)
    (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I m x := by
  induction x using AdicCompletion.induction_on with
  | h a =>
    simp only [AdicCompletion.evalₐ_mk]
    rw [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, AdicCompletion.Ideal.mk_eq_mk I hle]

/- English proof (translation)
Introduce `m n hle`. Use extensionality with `x`. Take `⟨y, hy⟩` from `Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)`. Establish `h1` using `evalₐ_factorPow I hle x`. Simplify using `only [RingHom.comp_apply, RingHom.coe_coe] at h1 ⊢`.

Rewrite using `[← h1, ← hy, Ideal.quotientMap_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, Ideal.quotientMap_mk]`.
-/
theorem complMap_compat {R S : Type} [CommRing R] [CommRing S] (e : R →+* S) (I : Ideal R)
    (J : Ideal S) (h : I.map e ≤ J) : ∀ {m n : ℕ} (hle : m ≤ n),
    (Ideal.Quotient.factorPow J hle).comp ((fun n => (Ideal.quotientMap (J ^ n) e (by
        rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]; exact Ideal.pow_right_mono h n)).comp
      (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n)) n) =
      (fun n => (Ideal.quotientMap (J ^ n) e (by
        rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]; exact Ideal.pow_right_mono h n)).comp
      (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n)) m := by
      intro m n hle
      ext x
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
      have h1 := evalₐ_factorPow I hle x
      simp only [RingHom.comp_apply, RingHom.coe_coe] at h1 ⊢
      rw [← h1, ← hy, Ideal.quotientMap_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factorPow,
        Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, Ideal.quotientMap_mk]

noncomputable def complMap {R S : Type} [CommRing R] [CommRing S] (e : R →+* S) (I : Ideal R)
    (J : Ideal S) (h : I.map e ≤ J) : AdicCompletion I R →+* AdicCompletion J S :=
  AdicCompletion.liftRingHom J
    (fun n => (Ideal.quotientMap (J ^ n) e (by
        rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]; exact Ideal.pow_right_mono h n)).comp
      (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n))
    (complMap_compat e I J h)

/- English proof (translation)
Unfold `complMap`. Conclude with `AdicCompletion.evalₐ_liftRingHom J _ (complMap_compat e I J h) n x`.
-/
theorem evalₐ_complMap {R S : Type} [CommRing R] [CommRing S] (e : R →+* S) (I : Ideal R)
    (J : Ideal S) (h : I.map e ≤ J) (n : ℕ) (x : AdicCompletion I R) :
    AdicCompletion.evalₐ J n (complMap e I J h x) =
      Ideal.quotientMap (J ^ n) e (by
        rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]; exact Ideal.pow_right_mono h n)
        (AdicCompletion.evalₐ I n x) := by
  unfold complMap
  exact AdicCompletion.evalₐ_liftRingHom J _ (complMap_compat e I J h) n x

/- English proof (translation)
Apply `AdicCompletion.ext_evalₐ` to reduce the goal to its premises. Introduce `n`. Rewrite using `[evalₐ_complMap]`. Simplify using `[AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]`.
-/
theorem complMap_algebraMap {R S : Type} [CommRing R] [CommRing S] (e : R →+* S) (I : Ideal R)
    (J : Ideal S) (h : I.map e ≤ J) (r : R) :
    complMap e I J h (algebraMap R _ r) = algebraMap S _ (e r) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [evalₐ_complMap]
  simp [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]

/- English proof (translation)
Apply `AdicCompletion.ext_evalₐ` to reduce the goal to its premises. Introduce `n`. Rewrite using `[evalₐ_complMap, evalₐ_complMap, evalₐ_complMap]`. Take `⟨y, hy⟩` from `Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)`. Rewrite using `[← hy]`.

Simplify using `[Ideal.quotientMap_mk]`.
-/
theorem complMap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (e : R →+* S)
    (e' : S →+* T) (I : Ideal R) (J : Ideal S) (K : Ideal T) (h : I.map e ≤ J) (h' : J.map e' ≤ K)
    (x : AdicCompletion I R) :
    complMap e' J K h' (complMap e I J h x) = complMap (e'.comp e) I K
      (by rw [← Ideal.map_map]; exact (Ideal.map_mono h).trans h') x := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [evalₐ_complMap, evalₐ_complMap, evalₐ_complMap]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [← hy]
  simp [Ideal.quotientMap_mk]

/- English proof (translation)
Apply `AdicCompletion.ext_evalₐ` to reduce the goal to its premises. Introduce `n`. Rewrite using `[evalₐ_complMap]`. Take `⟨y, hy⟩` from `Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)`. Rewrite using `[← hy]`.

Simplify using `[Ideal.quotientMap_mk]`.
-/
theorem complMap_id {R : Type} [CommRing R] (I : Ideal R) (h : I.map (RingHom.id R) ≤ I)
    (x : AdicCompletion I R) : complMap (RingHom.id R) I I h x = x := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [evalₐ_complMap]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [← hy]
  simp [Ideal.quotientMap_mk]

/- English proof (translation)
Establish `h1 : I.map (e : R →+* S) ≤ J` using `h.le`. Establish `h2 : J.map (e.symm : S →+* R) ≤ I`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `y hy`. Rewrite `hy` using `[← h, Ideal.mem_map_of_equiv]`.

Take `⟨x, hx, rfl⟩` from `hy`. Simplify using `using hx`. Use `⟨RingEquiv.ofRingHom (complMap (e : R →+* S) I J h1) (complMap (e.symm : S →+* R) J I h2) ?_ ?_, complMap_algebraMap _ I J h1⟩` and prove the remaining obligations. Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, complMap_comp]`.

Simplify using `only [RingEquiv.toRingHom_eq_coe, RingEquiv.comp_symm, RingHom.id_apply]`. Conclude with `complMap_id J _ x`. Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, complMap_comp]`. Simplify using `only [RingEquiv.toRingHom_eq_coe, RingEquiv.symm_comp, RingHom.id_apply]`.

Conclude with `complMap_id I _ x`.
-/
theorem compl_equiv (R S : Type) [CommRing R] [CommRing S] (e : R ≃+* S) (I : Ideal R)
    (J : Ideal S) (h : I.map e = J) : ∃ f : AdicCompletion I R ≃+* AdicCompletion J S,
      ∀ r : R, f (algebraMap R _ r) = algebraMap S _ (e r) := by
  have h1 : I.map (e : R →+* S) ≤ J := h.le
  have h2 : J.map (e.symm : S →+* R) ≤ I := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [← h, Ideal.mem_map_of_equiv] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    simpa using hx
  refine ⟨RingEquiv.ofRingHom (complMap (e : R →+* S) I J h1) (complMap (e.symm : S →+* R) J I h2)
    ?_ ?_, complMap_algebraMap _ I J h1⟩
  · refine RingHom.ext fun x => ?_
    rw [RingHom.comp_apply, complMap_comp]
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.comp_symm, RingHom.id_apply]
    exact complMap_id J _ x
  · refine RingHom.ext fun x => ?_
    rw [RingHom.comp_apply, complMap_comp]
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.symm_comp, RingHom.id_apply]
    exact complMap_id I _ x

/- English proof (translation)
Take `⟨S, hS⟩` from `h`. Use `⟨S, ?_⟩` and prove the remaining obligations. Apply `IntermediateField.toSubfield_injective` to reduce the goal to its premises. Establish `hr : Set.range (algebraMap F K) = Set.range (algebraMap F' K)`. Use extensionality with `y`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, rfl⟩`. Conclude with `⟨φ x, (hφ x).symm⟩`. Introduce and unpack `⟨x, rfl⟩; exact ⟨φ.symm x, by rw [hφ, RingEquiv.apply_symm_apply]⟩`. Establish `h2` using `congrArg IntermediateField.toSubfield hS`.

Rewrite `h2`, the goal using `[IntermediateField.adjoin_toSubfield, IntermediateField.top_toSubfield]`. Rewrite using `[hr]`. Conclude with `h2`.
-/
theorem fg_top_transfer {F F' K : Type} [Field F] [Field F'] [Field K] [Algebra F K] [Algebra F' K]
    (φ : F ≃+* F') (hφ : ∀ x, algebraMap F K x = algebraMap F' K (φ x))
    (h : (⊤ : IntermediateField F' K).FG) : (⊤ : IntermediateField F K).FG := by
  obtain ⟨S, hS⟩ := h
  refine ⟨S, ?_⟩
  apply IntermediateField.toSubfield_injective
  have hr : Set.range (algebraMap F K) = Set.range (algebraMap F' K) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨φ x, (hφ x).symm⟩
    · rintro ⟨x, rfl⟩; exact ⟨φ.symm x, by rw [hφ, RingEquiv.apply_symm_apply]⟩
  have h2 := congrArg IntermediateField.toSubfield hS
  rw [IntermediateField.adjoin_toSubfield, IntermediateField.top_toSubfield] at h2 ⊢
  rw [hr]
  exact h2

noncomputable def tensorHom {A A' B B' K : Type} [CommRing A] [CommRing A'] [CommRing B]
    [CommRing B'] [CommRing K] [Algebra A B] [Algebra A' B'] [Algebra A K] [Algebra A' K]
    (e : A →+* A') (f : B →+* B') (hf : ∀ a, f (algebraMap A B a) = algebraMap A' B' (e a))
    (hK : ∀ a, algebraMap A K a = algebraMap A' K (e a)) : B ⊗[A] K →+* B' ⊗[A'] K :=
  letI : Algebra A (B' ⊗[A'] K) := ((algebraMap A' (B' ⊗[A'] K)).comp e).toAlgebra
  (Algebra.TensorProduct.lift (S := A)
    { toRingHom := (Algebra.TensorProduct.includeLeftRingHom : B' →+* B' ⊗[A'] K).comp f
      commutes' := fun a => by
        change Algebra.TensorProduct.includeLeftRingHom (f (algebraMap A B a)) =
          algebraMap A' (B' ⊗[A'] K) (e a)
        rw [hf]
        exact (Algebra.TensorProduct.includeLeft (S := A')).commutes (e a) }
    { toRingHom := (Algebra.TensorProduct.includeRight : K →ₐ[A'] B' ⊗[A'] K).toRingHom
      commutes' := fun a => by
        change (Algebra.TensorProduct.includeRight : K →ₐ[A'] B' ⊗[A'] K) (algebraMap A K a) =
          algebraMap A' (B' ⊗[A'] K) (e a)
        rw [hK]
        exact Algebra.TensorProduct.includeRight.commutes (e a) }
    (fun _ _ => Commute.all _ _)).toRingHom

/- English proof (translation)
Simplify using `[tensorHom, Algebra.TensorProduct.lift_tmul]`.
-/
theorem tensorHom_tmul {A A' B B' K : Type} [CommRing A] [CommRing A'] [CommRing B]
    [CommRing B'] [CommRing K] [Algebra A B] [Algebra A' B'] [Algebra A K] [Algebra A' K]
    (e : A →+* A') (f : B →+* B') (hf : ∀ a, f (algebraMap A B a) = algebraMap A' B' (e a))
    (hK : ∀ a, algebraMap A K a = algebraMap A' K (e a)) (b : B) (k : K) :
    tensorHom e f hf hK (b ⊗ₜ k) = f b ⊗ₜ k := by
  simp [tensorHom, Algebra.TensorProduct.lift_tmul]

/- English proof (translation)
Establish `hf' : ∀ a, f.symm (algebraMap A' B' a) = algebraMap A B (e.symm a)` using `fun a => by`. Apply `f.injective` to reduce the goal to its premises. Rewrite using `[RingEquiv.apply_symm_apply, hf, RingEquiv.apply_symm_apply]`. Establish `hK' : ∀ a, algebraMap A' K a = algebraMap A K (e.symm a)` using `fun a => by`. Rewrite using `[hK, RingEquiv.apply_symm_apply]`.

Use `⟨RingEquiv.ofRingHom (tensorHom (e : A →+* A') (f : B →+* B') hf hK) (tensorHom (e.symm : A' →+* A) (f.symm : B' →+* B) hf' hK') ?_ ?_⟩` and prove the remaining obligations. Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul b k`.

Rewrite using `[RingHom.comp_apply]`. Use `erw [tensorHom_tmul, tensorHom_tmul]`. Simplify using the standard rewrite rules. Consider the case `add x y hx hy => simp only [RingHom.comp_apply, map_add] at hx hy ⊢`. Rewrite using `[hx, hy]`.

Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul b k`. Rewrite using `[RingHom.comp_apply]`.

Use `erw [tensorHom_tmul, tensorHom_tmul]`. Simplify using the standard rewrite rules. Consider the case `add x y hx hy => simp only [RingHom.comp_apply, map_add] at hx hy ⊢`. Rewrite using `[hx, hy]`.
-/
theorem tensor_equiv {A A' B B' K : Type} [CommRing A] [CommRing A'] [CommRing B]
    [CommRing B'] [CommRing K] [Algebra A B] [Algebra A' B'] [Algebra A K] [Algebra A' K]
    (e : A ≃+* A') (f : B ≃+* B') (hf : ∀ a, f (algebraMap A B a) = algebraMap A' B' (e a))
    (hK : ∀ a, algebraMap A K a = algebraMap A' K (e a)) : Nonempty (B ⊗[A] K ≃+* B' ⊗[A'] K) := by
  have hf' : ∀ a, f.symm (algebraMap A' B' a) = algebraMap A B (e.symm a) := fun a => by
    apply f.injective
    rw [RingEquiv.apply_symm_apply, hf, RingEquiv.apply_symm_apply]
  have hK' : ∀ a, algebraMap A' K a = algebraMap A K (e.symm a) := fun a => by
    rw [hK, RingEquiv.apply_symm_apply]
  refine ⟨RingEquiv.ofRingHom (tensorHom (e : A →+* A') (f : B →+* B') hf hK)
    (tensorHom (e.symm : A' →+* A) (f.symm : B' →+* B) hf' hK') ?_ ?_⟩
  · refine RingHom.ext fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b k =>
      rw [RingHom.comp_apply]
      erw [tensorHom_tmul, tensorHom_tmul]
      simp
    | add x y hx hy => simp only [RingHom.comp_apply, map_add] at hx hy ⊢; rw [hx, hy]
  · refine RingHom.ext fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b k =>
      rw [RingHom.comp_apply]
      erw [tensorHom_tmul, tensorHom_tmul]
      simp
    | add x y hx hy => simp only [RingHom.comp_apply, map_add] at hx hy ⊢; rw [hx, hy]

/- English proof (translation)
Use `⟨isNoetherianRing_of_ringEquiv T F, fun Q' _ => ?_⟩` and prove the remaining obligations. Use `haveI := hR (Q'.comap F)`. Conclude with `IsRegularLocalRing.of_ringEquiv (IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime (Q'.comap F)) (Localization.AtPrime Q') F (F.map_primeCompl_comap_eq Q'))`.
-/
theorem regular_transfer {T T' : Type} [CommRing T] [CommRing T'] (F : T ≃+* T')
    (hN : IsNoetherianRing T)
    (hR : ∀ (Q : Ideal T) [Q.IsPrime], IsRegularLocalRing (Localization.AtPrime Q)) :
    IsNoetherianRing T' ∧
      ∀ (Q' : Ideal T') [Q'.IsPrime], IsRegularLocalRing (Localization.AtPrime Q') := by
  refine ⟨isNoetherianRing_of_ringEquiv T F, fun Q' _ => ?_⟩
  haveI := hR (Q'.comap F)
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.ringEquivOfRingEquiv
    (Localization.AtPrime (Q'.comap F)) (Localization.AtPrime Q') F (F.map_primeCompl_comap_eq Q'))

/- English proof (translation)
The claim follows from `Ideal.ResidueField.map_algebraMap _ P' (e : A →+* A') rfl a`.
-/
theorem residueFieldRingEquiv_algebraMap {A A' : Type} [CommRing A] [CommRing A'] (e : A ≃+* A')
    (P' : Ideal A') [P'.IsPrime] (a : A) :
    Ideal.residueFieldRingEquiv (P'.comap (e : A →+* A')) P' e rfl
      (algebraMap A (P'.comap (e : A →+* A')).ResidueField a) =
      algebraMap A' P'.ResidueField (e a) :=
  Ideal.ResidueField.map_algebraMap _ P' (e : A →+* A') rfl a

/- English proof (translation)
Introduce `h P' _ K _ _ _ _ hfg`. Set `P : Ideal A` to `P'.comap (e : A →+* A')`. Use `haveI : P.IsPrime := Ideal.comap_isPrime _ _`. Set `φ : P.ResidueField ≃+* P'.ResidueField` to `Ideal.residueFieldRingEquiv P P' e rfl`. Use `letI : Algebra A K := ((algebraMap A' K).comp (e : A →+* A')).toAlgebra`.

Use `letI : Algebra P.ResidueField K := ((algebraMap P'.ResidueField K).comp (φ : _ →+* _)).toAlgebra`. Use `haveI : IsScalarTower A P.ResidueField K := IsScalarTower.of_algebraMap_eq fun a => by`. Express the relevant statement in the definitionally equal form `algebraMap A' K (e a) = algebraMap P'.ResidueField K (φ (algebraMap A P.ResidueField a))`. Rewrite using `[residueFieldRingEquiv_algebraMap e P' a, ← IsScalarTower.algebraMap_apply]`. Establish `hfg' : (⊤ : IntermediateField P.ResidueField K).FG` using `fg_top_transfer φ (fun _ => rfl) hfg`.

Take `⟨hN, hR⟩` from `h P K hfg'`. Take `⟨F⟩` from `tensor_equiv (K := K) e f hf (fun _ => rfl)`. Conclude with `regular_transfer F hN hR`.
-/
theorem transport (A A' B B' : Type) [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A B] [Algebra A' B'] (e : A ≃+* A') (f : B ≃+* B')
    (hf : ∀ a : A, f (algebraMap A B a) = algebraMap A' B' (e a)) :
    GeomRegFib A B → GeomRegFib A' B' := by
  intro h P' _ K _ _ _ _ hfg
  let P : Ideal A := P'.comap (e : A →+* A')
  haveI : P.IsPrime := Ideal.comap_isPrime _ _
  let φ : P.ResidueField ≃+* P'.ResidueField := Ideal.residueFieldRingEquiv P P' e rfl
  letI : Algebra A K := ((algebraMap A' K).comp (e : A →+* A')).toAlgebra
  letI : Algebra P.ResidueField K := ((algebraMap P'.ResidueField K).comp (φ : _ →+* _)).toAlgebra
  haveI : IsScalarTower A P.ResidueField K := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap A' K (e a) = algebraMap P'.ResidueField K (φ (algebraMap A P.ResidueField a))
    rw [residueFieldRingEquiv_algebraMap e P' a, ← IsScalarTower.algebraMap_apply]
  have hfg' : (⊤ : IntermediateField P.ResidueField K).FG := fg_top_transfer φ (fun _ => rfl) hfg
  obtain ⟨hN, hR⟩ := h P K hfg'
  obtain ⟨F⟩ := tensor_equiv (K := K) e f hf (fun _ => rfl)
  exact regular_transfer F hN hR

/- English proof (translation)
Introduce `hQE A _ _ _`. Take `⟨A₀, _, _, p, _, ⟨e⟩⟩` from `exists_loc A`. Establish `h2` using `((hQE A₀).2.1 p).2`. Take `⟨f, hf⟩` from `compl_equiv _ _ e (maximalIdeal (Localization.AtPrime p)) (maximalIdeal A) (map_ringEquiv_maximalIdeal e)`. Conclude with `transport _ _ _ _ e f hf h2`.
-/
theorem geomRegFib_adicCompletion_of_essFiniteType_int :
    (∀ (A : Type) [CommRing A] [Algebra.FiniteType ℤ A], ReciprocityTheory.AnForm.R.FinalTheorems.QERing A) →
      ∀ (A : Type) [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A],
        ReciprocityTheory.AnForm.R.FinalTheorems.GeomRegFib A (AdicCompletion (IsLocalRing.maximalIdeal A) A) := by
  intro hQE A _ _ _
  obtain ⟨A₀, _, _, p, _, ⟨e⟩⟩ := exists_loc A
  have h2 := ((hQE A₀).2.1 p).2
  obtain ⟨f, hf⟩ := compl_equiv _ _ e (maximalIdeal (Localization.AtPrime p)) (maximalIdeal A)
    (map_ringEquiv_maximalIdeal e)
  exact transport _ _ _ _ e f hf h2

end GlobalTheory.GeomRegFibTransport
