import Mathlib

open scoped TensorProduct

namespace FunctorialResolution.EmbeddedResolution

private noncomputable def residueFieldExtension (k A : Type*) [CommRing k] [CommRing A] [Algebra k A]
    [IsLocalRing A] [Algebra k (IsLocalRing.ResidueField A)]
    [IsScalarTower k A (IsLocalRing.ResidueField A)] :
    Algebra.Extension k (IsLocalRing.ResidueField A) :=
  { Ring := A
    σ := Function.surjInv (Ideal.Quotient.mk_surjective :
      Function.Surjective (algebraMap A (IsLocalRing.ResidueField A)))
    algebraMap_σ := Function.surjInv_eq _ }

/- English proof (translation)
Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `tmul a x`. Take `⟨a₀, rfl⟩` from `IsLocalRing.residue_surjective a`.

Use `⟨a₀ • x, ?_⟩` and prove the remaining obligations. Establish `h1 : (a₀ • (1 : IsLocalRing.ResidueField A)) = IsLocalRing.residue A a₀`. Rewrite using `[Algebra.smul_def, mul_one]`. Both sides reduce to the same expression. Use `show (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (a₀ • x) = _`.

Rewrite using `[← TensorProduct.smul_tmul, h1]`. Consider the case `add x y hx hy`. Take `⟨u, hu⟩` from `hx`. Take `⟨v, hv⟩` from `hy`. Use `⟨u + v, ?_⟩` and prove the remaining obligations.

Use `show (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (u + v) = _`. Rewrite using `[TensorProduct.tmul_add]`. Rewrite using `[show (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] u = x from hu, show (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] v = y from hv]`.
-/
private theorem one_tmul_residueField_surjective (A : Type*) [CommRing A] [IsLocalRing A]
    (M : Type*) [AddCommGroup M] [Module A M] :
    Function.Surjective (fun x : M => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] x) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a x =>
      obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective a
      refine ⟨a₀ • x, ?_⟩
      have h1 : (a₀ • (1 : IsLocalRing.ResidueField A)) = IsLocalRing.residue A a₀ := by
        rw [Algebra.smul_def, mul_one]; rfl
      show (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (a₀ • x) = _
      rw [← TensorProduct.smul_tmul, h1]
  | add x y hx hy =>
      obtain ⟨u, hu⟩ := hx
      obtain ⟨v, hv⟩ := hy
      refine ⟨u + v, ?_⟩
      show (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (u + v) = _
      rw [TensorProduct.tmul_add]
      rw [show (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] u = x from hu,
        show (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] v = y from hv]

/- English proof (translation)
Rewrite `hx` using `[Ideal.toCotangent_eq_zero]`. Establish `key : ∀ t : A, t ∈ I ^ 2 → t ∈ I ∧ ∀ ht : t ∈ I, (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (⟨t, ht⟩ : ↥I) = 0`. Introduce `t ht`. Rewrite `ht` using `[sq]`. Use `Submodule.mul_induction_on ht ?_ ?_` and prove the remaining obligations.

Introduce `a ha b hb`. Use `⟨Ideal.mul_mem_right _ _ ha, ?_⟩` and prove the remaining obligations. Introduce `hab`. Establish `h2 : (⟨a * b, hab⟩ : ↥I) = a • (⟨b, hb⟩ : ↥I)`. Use `ext`.

Simplify using `[smul_eq_mul]`. Establish `h3 : a • (1 : IsLocalRing.ResidueField A) = 0`. Rewrite using `[Algebra.smul_def, mul_one]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (hI ha)`. Rewrite using `[h2, ← TensorProduct.smul_tmul, h3, TensorProduct.zero_tmul]`.

Introduce and unpack `u v ⟨hu, hu2⟩ ⟨hv, hv2⟩`. Use `⟨Ideal.add_mem _ hu hv, ?_⟩` and prove the remaining obligations. Introduce `huv`. Establish `h4 : (⟨u + v, huv⟩ : ↥I) = (⟨u, hu⟩ : ↥I) + ⟨v, hv⟩` using `rfl`. Rewrite using `[h4, TensorProduct.tmul_add, hu2, hv2, add_zero]`.

Conclude with `(key x hx).2 x.2`.
-/
private theorem tmul_eq_zero_of_toCotangent_eq_zero (A : Type*) [CommRing A] [IsLocalRing A]
    (I : Ideal A) (hI : I ≤ IsLocalRing.maximalIdeal A) (x : ↥I)
    (hx : I.toCotangent x = 0) :
    (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] x
      = (0 : IsLocalRing.ResidueField A ⊗[A] ↥I) := by
  rw [Ideal.toCotangent_eq_zero] at hx
  have key : ∀ t : A, t ∈ I ^ 2 →
      t ∈ I ∧ ∀ ht : t ∈ I, (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (⟨t, ht⟩ : ↥I) = 0 := by
    intro t ht
    rw [sq] at ht
    refine Submodule.mul_induction_on ht ?_ ?_
    · intro a ha b hb
      refine ⟨Ideal.mul_mem_right _ _ ha, ?_⟩
      intro hab
      have h2 : (⟨a * b, hab⟩ : ↥I) = a • (⟨b, hb⟩ : ↥I) := by
        ext
        simp [smul_eq_mul]
      have h3 : a • (1 : IsLocalRing.ResidueField A) = 0 := by
        rw [Algebra.smul_def, mul_one]
        exact Ideal.Quotient.eq_zero_iff_mem.2 (hI ha)
      rw [h2, ← TensorProduct.smul_tmul, h3, TensorProduct.zero_tmul]
    · rintro u v ⟨hu, hu2⟩ ⟨hv, hv2⟩
      refine ⟨Ideal.add_mem _ hu hv, ?_⟩
      intro huv
      have h4 : (⟨u + v, huv⟩ : ↥I) = (⟨u, hu⟩ : ↥I) + ⟨v, hv⟩ := rfl
      rw [h4, TensorProduct.tmul_add, hu2, hv2, add_zero]
  exact (key x hx).2 x.2

private noncomputable def kerToTensorResidueField (k A : Type*) [CommRing k] [CommRing A] [Algebra k A]
    [IsLocalRing A] :
    ↥(RingHom.ker (algebraMap A (IsLocalRing.ResidueField A))) →ₗ[A]
      IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A :=
  KaehlerDifferential.kerToTensor k A (IsLocalRing.ResidueField A)

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem dTensor_apply (k A : Type*) [CommRing k] [CommRing A] [Algebra k A]
    [IsLocalRing A] (x : ↥(RingHom.ker (algebraMap A (IsLocalRing.ResidueField A)))) :
    kerToTensorResidueField k A x
      = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (KaehlerDifferential.D k A (x : A)) := rfl

/- English proof (translation)
Establish `: Algebra.FormallySmooth k (residueFieldExtension k A).Ring` using `inferInstanceAs (Algebra.FormallySmooth k A)`. Establish `hs0 : Subsingleton (Algebra.H1Cotangent k (IsLocalRing.ResidueField A))` using `Algebra.FormallySmooth.subsingleton_h1Cotangent`. Establish `hsub : Subsingleton (residueFieldExtension k A).H1Cotangent` using `(Algebra.Extension.equivH1CotangentOfFormallySmooth (residueFieldExtension k A)).toEquiv.subsingleton`. Establish `hsub2 : Subsingleton ↥(LinearMap.ker (residueFieldExtension k A).cotangentComplex)` using `hsub`. Establish `hbot : LinearMap.ker (residueFieldExtension k A).cotangentComplex = ⊥` using `Submodule.eq_bot_of_subsingleton`.

Establish `hx2 : (x : A) ∈ (residueFieldExtension k A).ker` using `x.2`. Establish `h0 : (residueFieldExtension k A).cotangentComplex (Algebra.Extension.Cotangent.mk ⟨(x : A), hx2⟩) = 0`. Rewrite using `[Algebra.Extension.cotangentComplex_mk]`. Conclude with `hx`. Establish `hinj` using `LinearMap.ker_eq_bot.mp hbot`.

Establish `h1 : Algebra.Extension.Cotangent.mk (⟨(x : A), hx2⟩ : (residueFieldExtension k A).ker) = 0` using `hinj (by rw [h0, map_zero])`. Rewrite `h1` using `[Algebra.Extension.Cotangent.mk_eq_zero_iff]`. Conclude with `h1`.
-/
private theorem mem_ker_sq_of_tmul_D_eq_zero (k A : Type*) [CommRing k] [CommRing A] [Algebra k A]
    [IsLocalRing A]
    [Algebra k (IsLocalRing.ResidueField A)] [IsScalarTower k A (IsLocalRing.ResidueField A)]
    [Algebra.FormallySmooth k A]
    [Algebra.FormallySmooth k (IsLocalRing.ResidueField A)]
    (x : ↥(RingHom.ker (algebraMap A (IsLocalRing.ResidueField A))))
    (hx : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (KaehlerDifferential.D k A (x : A))
      = (0 : IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A)) :
    (x : A) ∈ (RingHom.ker (algebraMap A (IsLocalRing.ResidueField A))) ^ 2 := by
  have : Algebra.FormallySmooth k (residueFieldExtension k A).Ring :=
    inferInstanceAs (Algebra.FormallySmooth k A)
  have hs0 : Subsingleton (Algebra.H1Cotangent k (IsLocalRing.ResidueField A)) :=
    Algebra.FormallySmooth.subsingleton_h1Cotangent
  have hsub : Subsingleton (residueFieldExtension k A).H1Cotangent :=
    (Algebra.Extension.equivH1CotangentOfFormallySmooth (residueFieldExtension k A)).toEquiv.subsingleton
  have hsub2 : Subsingleton ↥(LinearMap.ker (residueFieldExtension k A).cotangentComplex) := hsub
  have hbot : LinearMap.ker (residueFieldExtension k A).cotangentComplex = ⊥ :=
    Submodule.eq_bot_of_subsingleton
  have hx2 : (x : A) ∈ (residueFieldExtension k A).ker := x.2
  have h0 : (residueFieldExtension k A).cotangentComplex
      (Algebra.Extension.Cotangent.mk ⟨(x : A), hx2⟩) = 0 := by
    rw [Algebra.Extension.cotangentComplex_mk]
    exact hx
  have hinj := LinearMap.ker_eq_bot.mp hbot
  have h1 : Algebra.Extension.Cotangent.mk (⟨(x : A), hx2⟩ : (residueFieldExtension k A).ker) = 0 :=
    hinj (by rw [h0, map_zero])
  rw [Algebra.Extension.Cotangent.mk_eq_zero_iff] at h1
  exact h1

/- English proof (translation)
Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `z hz`. Take `⟨x, rfl⟩` from `one_tmul_residueField_surjective A (↥(RingHom.ker (algebraMap A (IsLocalRing.ResidueField A)))) z`. Establish `h1 : LinearMap.liftBaseChange (IsLocalRing.ResidueField A) (kerToTensorResidueField k A) ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] x) = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (KaehlerDifferential.D k A (x : A))`. Rewrite using `[LinearMap.liftBaseChange_tmul, one_smul, dTensor_apply]`.

Establish `h2 : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (KaehlerDifferential.D k A (x : A)) = (0 : IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A)`. Rewrite using `[← h1]`. Conclude with `hz`. Establish `h3 : (x : A) ∈ (RingHom.ker (algebraMap A (IsLocalRing.ResidueField A))) ^ 2` using `mem_ker_sq_of_tmul_D_eq_zero k A x h2`. Establish `hle : RingHom.ker (algebraMap A (IsLocalRing.ResidueField A)) ≤ IsLocalRing.maximalIdeal A`.

Introduce `a ha`. Establish `ha' : algebraMap A (IsLocalRing.ResidueField A) a = 0` using `ha`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp ha'`. Use `tmul_eq_zero_of_toCotangent_eq_zero A (RingHom.ker (algebraMap A (IsLocalRing.ResidueField A))) hle x ?_` and prove the remaining obligations. Rewrite using `[Ideal.toCotangent_eq_zero]`.

Conclude with `h3`.
-/
private theorem injective_liftBaseChange_dTensor (k A : Type*) [CommRing k] [CommRing A]
    [Algebra k A] [IsLocalRing A] [Algebra k (IsLocalRing.ResidueField A)]
    [IsScalarTower k A (IsLocalRing.ResidueField A)]
    [Algebra.FormallySmooth k A]
    [Algebra.FormallySmooth k (IsLocalRing.ResidueField A)] :
    Function.Injective (LinearMap.liftBaseChange (IsLocalRing.ResidueField A)
      (kerToTensorResidueField k A)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  obtain ⟨x, rfl⟩ := one_tmul_residueField_surjective A
    (↥(RingHom.ker (algebraMap A (IsLocalRing.ResidueField A)))) z
  have h1 : LinearMap.liftBaseChange (IsLocalRing.ResidueField A) (kerToTensorResidueField k A)
      ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] x)
      = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (KaehlerDifferential.D k A (x : A)) := by
    rw [LinearMap.liftBaseChange_tmul, one_smul, dTensor_apply]
  have h2 : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (KaehlerDifferential.D k A (x : A))
      = (0 : IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A) := by
    rw [← h1]; exact hz
  have h3 : (x : A) ∈ (RingHom.ker (algebraMap A (IsLocalRing.ResidueField A))) ^ 2 :=
    mem_ker_sq_of_tmul_D_eq_zero k A x h2
  have hle : RingHom.ker (algebraMap A (IsLocalRing.ResidueField A))
      ≤ IsLocalRing.maximalIdeal A := by
    intro a ha
    have ha' : algebraMap A (IsLocalRing.ResidueField A) a = 0 := ha
    exact Ideal.Quotient.eq_zero_iff_mem.mp ha'
  refine tmul_eq_zero_of_toCotangent_eq_zero A
    (RingHom.ker (algebraMap A (IsLocalRing.ResidueField A))) hle x ?_
  rw [Ideal.toCotangent_eq_zero]
  exact h3

section

variable (k A : Type*) [CommRing k] [CommRing A] [Algebra k A] [IsLocalRing A]
  [IsNoetherianRing A] [Algebra.FormallySmooth k A]
  [Module.Free A (KaehlerDifferential k A)] [Module.Finite A (KaehlerDifferential k A)]
  [Algebra k (IsLocalRing.ResidueField A)]
  [IsScalarTower k A (IsLocalRing.ResidueField A)]
  [Algebra.FormallySmooth k (IsLocalRing.ResidueField A)]

omit [IsNoetherianRing A] [Module.Free A (KaehlerDifferential k A)]
  [Module.Finite A (KaehlerDifferential k A)] in
/- English proof (translation)
Establish `hT0 : LinearMap.ker (LinearMap.liftBaseChange (IsLocalRing.ResidueField A) (kerToTensorResidueField k A)) = ⊥` using `LinearMap.ker_eq_bot.mpr (injective_liftBaseChange_dTensor k A)`. Establish `hmain` using `hm.map' (LinearMap.liftBaseChange (IsLocalRing.ResidueField A) (kerToTensorResidueField k A)) hT0`. Establish `heq : (⇑(LinearMap.liftBaseChange (IsLocalRing.ResidueField A) (kerToTensorResidueField k A)) ∘ fun i : ι => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (m i)) = fun i : ι => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (KaehlerDifferential.D k A ((m i : A)))`. Use function extensionality and compare the values at `i`. Simplify using `only [Function.comp_apply, LinearMap.liftBaseChange_tmul, one_smul, dTensor_apply]`.

Rewrite `hmain` using `[heq]`. Conclude with `hmain`.
-/
theorem linearIndependent_tensor_D_of_ker {ι : Type*}
    (m : ι → (RingHom.ker (algebraMap A (IsLocalRing.ResidueField A)) : Ideal A))
    (hm : LinearIndependent (IsLocalRing.ResidueField A)
      (fun i : ι => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (m i))) :
    LinearIndependent (IsLocalRing.ResidueField A)
      (fun i : ι =>
        (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (KaehlerDifferential.D k A ((m i : A)))) := by
  classical
  have hT0 : LinearMap.ker (LinearMap.liftBaseChange (IsLocalRing.ResidueField A)
      (kerToTensorResidueField k A)) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (injective_liftBaseChange_dTensor k A)
  have hmain := hm.map' (LinearMap.liftBaseChange (IsLocalRing.ResidueField A)
      (kerToTensorResidueField k A)) hT0
  have heq : (⇑(LinearMap.liftBaseChange (IsLocalRing.ResidueField A) (kerToTensorResidueField k A)) ∘
      fun i : ι => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (m i))
      = fun i : ι =>
        (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (KaehlerDifferential.D k A ((m i : A))) := by
    funext i
    simp only [Function.comp_apply, LinearMap.liftBaseChange_tmul, one_smul, dTensor_apply]
  rw [heq] at hmain
  exact hmain

omit [IsNoetherianRing A] [Module.Free A (KaehlerDifferential k A)]
  [Module.Finite A (KaehlerDifferential k A)] in
/- English proof (translation)
Substitute `hI` using the available equality. Conclude with `linearIndependent_tensor_D_of_ker k A m hm`.
-/
private theorem linearIndependent_tensor_D_of_ideal_eq_ker {ι : Type*} (I : Ideal A)
    (hI : I = RingHom.ker (algebraMap A (IsLocalRing.ResidueField A)))
    (m : ι → ↥I)
    (hm : LinearIndependent (IsLocalRing.ResidueField A)
      (fun i : ι => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (m i))) :
    LinearIndependent (IsLocalRing.ResidueField A)
      (fun i : ι =>
        (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (KaehlerDifferential.D k A ((m i : A)))) := by
  subst hI
  exact linearIndependent_tensor_D_of_ker k A m hm

omit [IsNoetherianRing A] [Module.Free A (KaehlerDifferential k A)]
  [Module.Finite A (KaehlerDifferential k A)] in
/- English proof (translation)
The claim follows from `linearIndependent_tensor_D_of_ideal_eq_ker k A (IsLocalRing.maximalIdeal A) (Ideal.mk_ker).symm m hm`.
-/
theorem linearIndependent_tensor_D_of_maximalIdeal {ι : Type*}
    (m : ι → (IsLocalRing.maximalIdeal A : Ideal A))
    (hm : LinearIndependent (IsLocalRing.ResidueField A)
      (fun i : ι => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (m i))) :
    LinearIndependent (IsLocalRing.ResidueField A)
      (fun i : ι =>
        (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (KaehlerDifferential.D k A ((m i : A)))) :=
  linearIndependent_tensor_D_of_ideal_eq_ker k A (IsLocalRing.maximalIdeal A)
    (Ideal.mk_ker).symm m hm

omit [Module.Free A (KaehlerDifferential k A)] [Module.Finite A (KaehlerDifferential k A)] in
/- English proof (translation)
Establish `hfin : Module.Finite A ↥(IsLocalRing.maximalIdeal A)` using `Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)`. Establish `hfin2 : Module.Finite (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A ⊗[A] ↥(IsLocalRing.maximalIdeal A))` using `inferInstance`. Take `⟨y, hy⟩ : ∃ y : Fin (Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A ⊗[A] ↥(IsLocalRing.maximalIdeal A))) → ↥(IsLocalRing.maximalIdeal A), ∀ i, (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (y i) = Module.finBasis (IsLocalRing.ResidueField A) (IsLocalRing.Residue …` from `by choose y hy using fun i => one_tmul_residueField_surjective A (↥(IsLocalRing.maximalIdeal A)) (Module.finBasis (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A ⊗[A] ↥(IsLocalRing.maximalIdeal A)) i)`. Conclude with `⟨y, hy⟩`. Establish `hspan : Submodule.span A (Set.range y) = ⊤` using `IsLocalRing.span_eq_top_of_tmul_eq_basis y (Module.finBasis (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A ⊗[A] ↥(IsLocalRing.maximalIdeal A))) (fun i => hy i)`.

Use `⟨_, fun i => ((y i : A)), ?_, ?_⟩` and prove the remaining obligations. Establish `h3` using `congrArg (Submodule.map (IsLocalRing.maximalIdeal A).subtype) hspan`. Rewrite `h3` using `[Submodule.map_span, Submodule.map_subtype_top]`. Establish `himg : ((IsLocalRing.maximalIdeal A).subtype '' Set.range y) = Set.range (fun i => ((y i : A)))`. Use extensionality with `t`.

Simplify using the standard rewrite rules. Rewrite `h3` using `[himg]`. Conclude with `h3`. Establish `hfun : (fun i => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (y i)) = ⇑(Module.finBasis (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A ⊗[A] ↥(IsLocalRing.maximalIdeal A)))` using `funext hy`. Use `linearIndependent_tensor_D_of_maximalIdeal k A y ?_` and prove the remaining obligations.

Rewrite using `[hfun]`. Conclude with `Module.Basis.linearIndependent _`.
-/
theorem exists_local_parameters :
    ∃ (h : ℕ) (y : Fin h → A),
      Ideal.span (Set.range y) = IsLocalRing.maximalIdeal A ∧
      LinearIndependent (IsLocalRing.ResidueField A)
        (fun i : Fin h =>
          (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (KaehlerDifferential.D k A (y i))) := by
  classical
  have hfin : Module.Finite A ↥(IsLocalRing.maximalIdeal A) :=
    Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
  have hfin2 : Module.Finite (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[A] ↥(IsLocalRing.maximalIdeal A)) := inferInstance
  obtain ⟨y, hy⟩ : ∃ y : Fin (Module.finrank (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[A] ↥(IsLocalRing.maximalIdeal A))) →
      ↥(IsLocalRing.maximalIdeal A),
      ∀ i, (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (y i)
        = Module.finBasis (IsLocalRing.ResidueField A)
            (IsLocalRing.ResidueField A ⊗[A] ↥(IsLocalRing.maximalIdeal A)) i := by
    choose y hy using fun i => one_tmul_residueField_surjective A (↥(IsLocalRing.maximalIdeal A))
      (Module.finBasis (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField A ⊗[A] ↥(IsLocalRing.maximalIdeal A)) i)
    exact ⟨y, hy⟩
  have hspan : Submodule.span A (Set.range y) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis y
      (Module.finBasis (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField A ⊗[A] ↥(IsLocalRing.maximalIdeal A)))
      (fun i => hy i)
  refine ⟨_, fun i => ((y i : A)), ?_, ?_⟩
  · have h3 := congrArg (Submodule.map (IsLocalRing.maximalIdeal A).subtype) hspan
    rw [Submodule.map_span, Submodule.map_subtype_top] at h3
    have himg : ((IsLocalRing.maximalIdeal A).subtype '' Set.range y)
        = Set.range (fun i => ((y i : A))) := by
      ext t
      simp
    rw [himg] at h3
    exact h3
  · have hfun : (fun i => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (y i))
        = ⇑(Module.finBasis (IsLocalRing.ResidueField A)
            (IsLocalRing.ResidueField A ⊗[A] ↥(IsLocalRing.maximalIdeal A))) := funext hy
    refine linearIndependent_tensor_D_of_maximalIdeal k A y ?_
    rw [hfun]
    exact Module.Basis.linearIndependent _

/- English proof (translation)
Take `⟨h, y, hspan, hind⟩` from `exists_local_parameters k A`. Take `⟨v, hv⟩ : ∃ v : Fin h → (IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A), v = fun i => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (KaehlerDifferential.D k A (y i))` from `⟨_, rfl⟩`. Rewrite `hind` using `[← hv]`. Establish `hψ : ∀ i : Fin h, ∃ ψ : (IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A) →ₗ[IsLocalRing.ResidueField A] IsLocalRing.ResidueField A, ∀ j, ψ (v j) = if i = j then 1 else 0`. Introduce `i`.

Take `⟨g, hg⟩` from `LinearMap.exists_extend ((Finsupp.lapply i).comp (hind.repr : _ →ₗ[IsLocalRing.ResidueField A] _))`. Use `⟨g, fun j => ?_⟩` and prove the remaining obligations. Establish `hmem : v j ∈ Submodule.span (IsLocalRing.ResidueField A) (Set.range v)` using `Submodule.subset_span (Set.mem_range_self j)`. Establish `h1 : hind.repr ⟨v j, hmem⟩ = Finsupp.single j 1` using `hind.repr_eq_single j _ rfl`. Establish `h2` using `LinearMap.congr_fun hg ⟨v j, hmem⟩`.

Simplify using `only [LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply, h1, Finsupp.lapply_apply, Finsupp.single_apply] at h2`. Rewrite using `[h2]`. Distinguish the cases in `hij : i = j`. Simplify using `[hij]`. Simplify using `[hij, Ne.symm hij]`.

Use `choose ψ hψ' using hψ`. Simplify using `only [hv] at hψ'`. Establish `hsurj : Function.Surjective (algebraMap A (IsLocalRing.ResidueField A))` using `Ideal.Quotient.mk_surjective`. Establish `hσ : ∀ c, algebraMap A (IsLocalRing.ResidueField A) (Function.surjInv hsurj c) = c` using `Function.surjInv_eq hsurj`. Take `⟨φ, hφ⟩ : ∃ φ : Fin h → (KaehlerDifferential k A →ₗ[A] A), ∀ i j, φ i (Module.Free.chooseBasis A (KaehlerDifferential k A) j) = Function.surjInv hsurj (ψ i ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (Module.Free.chooseBasis A (KaehlerDifferential k A) j)))` from `⟨fun i => (Module.Free.chooseBasis A (KaehlerDifferential k A)).constr A (fun j => Function.surjInv hsurj (ψ i ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (Module.Free.chooseBasis A (KaehlerDifferential k A) j)))), fun i j => by simp⟩`.

Establish `hres : ∀ (i : Fin h) (ω : KaehlerDifferential k A), algebraMap A (IsLocalRing.ResidueField A) (φ i ω) = ψ i ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] ω)`. Introduce `i`. Establish `hmaps : (Algebra.linearMap A (IsLocalRing.ResidueField A)).comp (φ i) = ((ψ i).restrictScalars A).comp (TensorProduct.mk A (IsLocalRing.ResidueField A) (KaehlerDifferential k A) 1)`. Use `(Module.Free.chooseBasis A (KaehlerDifferential k A)).ext (fun j => ?_)` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, Algebra.linearMap_apply, hφ, hσ, LinearMap.coe_restrictScalars, TensorProduct.mk_apply]`.

Introduce `ω`. Establish `hh` using `LinearMap.congr_fun hmaps ω`. Simplify using `using hh`. Take `⟨M, hMdef⟩ : ∃ M : Matrix (Fin h) (Fin h) A, M = Matrix.of fun i j => φ i (KaehlerDifferential.D k A (y j))` from `⟨_, rfl⟩`. Establish `hMapp : ∀ a b, M a b = φ a (KaehlerDifferential.D k A (y b))`.

Introduce `a b`. Rewrite using `[hMdef]`. Both sides reduce to the same expression. Establish `hMres : ∀ a b, algebraMap A (IsLocalRing.ResidueField A) (M a b) = if a = b then 1 else 0`. Introduce `a b`.

Rewrite using `[hMapp, hres a, hψ' a b]`. Establish `hmapM : M.map (algebraMap A (IsLocalRing.ResidueField A)) = 1`. Use extensionality with `a b`. Rewrite using `[Matrix.map_apply, hMres, Matrix.one_apply]`. Establish `hdet1 : algebraMap A (IsLocalRing.ResidueField A) M.det = 1`.

Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, hmapM, Matrix.det_one]`. Establish `hdet : IsUnit M.det`. Assume the negation of the conclusion as `hcon`. Establish `h1 : Ideal.span ({M.det} : Set A) ≠ ⊤` using `fun hq => hcon (Ideal.span_singleton_eq_top.mp hq)`. Establish `hmem : M.det ∈ IsLocalRing.maximalIdeal A` using `IsLocalRing.le_maximalIdeal h1 (Ideal.mem_span_singleton_self _)`.

Establish `hzero : algebraMap A (IsLocalRing.ResidueField A) M.det = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr hmem`. Rewrite `hzero` using `[hdet1]`. Conclude with `one_ne_zero hzero`. Establish `hinvMul : M⁻¹ * M = 1` using `Matrix.nonsing_inv_mul M hdet`. Use `⟨h, y, fun i => (∑ l : Fin h, (M⁻¹ i l) • φ l).compDer (KaehlerDifferential.D k A), hspan, ?_⟩` and prove the remaining obligations.

Introduce `i j`. Establish `hsum : (∑ l : Fin h, M⁻¹ i l * M l j) = if i = j then 1 else 0`. Rewrite using `[← Matrix.mul_apply, hinvMul, Matrix.one_apply]`. Use `show (∑ l : Fin h, (M⁻¹ i l) • φ l) (KaehlerDifferential.D k A (y j)) = if i = j then 1 else 0`. Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]`.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl ?_` and prove the remaining obligations. Introduce `l _`. Rewrite using `[hMapp]`. Use `_ = if i = j then 1 else 0 := hsum`.
-/
theorem exists_local_parameters_and_dual_derivations :
    ∃ (h : ℕ) (y : Fin h → A) (δ : Fin h → Derivation k A A),
      Ideal.span (Set.range y) = IsLocalRing.maximalIdeal A ∧
      ∀ i j : Fin h, δ i (y j) = if i = j then 1 else 0 := by
  classical
  obtain ⟨h, y, hspan, hind⟩ := exists_local_parameters k A
  obtain ⟨v, hv⟩ : ∃ v : Fin h → (IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A),
      v = fun i => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (KaehlerDifferential.D k A (y i)) :=
    ⟨_, rfl⟩
  rw [← hv] at hind
  have hψ : ∀ i : Fin h, ∃ ψ : (IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A)
      →ₗ[IsLocalRing.ResidueField A] IsLocalRing.ResidueField A,
      ∀ j, ψ (v j) = if i = j then 1 else 0 := by
    intro i
    obtain ⟨g, hg⟩ := LinearMap.exists_extend
      ((Finsupp.lapply i).comp (hind.repr : _ →ₗ[IsLocalRing.ResidueField A] _))
    refine ⟨g, fun j => ?_⟩
    have hmem : v j ∈ Submodule.span (IsLocalRing.ResidueField A) (Set.range v) :=
      Submodule.subset_span (Set.mem_range_self j)
    have h1 : hind.repr ⟨v j, hmem⟩ = Finsupp.single j 1 := hind.repr_eq_single j _ rfl
    have h2 := LinearMap.congr_fun hg ⟨v j, hmem⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply,
      h1, Finsupp.lapply_apply, Finsupp.single_apply] at h2
    rw [h2]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  choose ψ hψ' using hψ
  simp only [hv] at hψ'
  have hsurj : Function.Surjective (algebraMap A (IsLocalRing.ResidueField A)) :=
    Ideal.Quotient.mk_surjective
  have hσ : ∀ c, algebraMap A (IsLocalRing.ResidueField A) (Function.surjInv hsurj c) = c :=
    Function.surjInv_eq hsurj
  obtain ⟨φ, hφ⟩ : ∃ φ : Fin h → (KaehlerDifferential k A →ₗ[A] A),
      ∀ i j, φ i (Module.Free.chooseBasis A (KaehlerDifferential k A) j)
        = Function.surjInv hsurj (ψ i ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
            (Module.Free.chooseBasis A (KaehlerDifferential k A) j))) :=
    ⟨fun i => (Module.Free.chooseBasis A (KaehlerDifferential k A)).constr A
        (fun j => Function.surjInv hsurj (ψ i ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
          (Module.Free.chooseBasis A (KaehlerDifferential k A) j)))),
      fun i j => by simp⟩
  have hres : ∀ (i : Fin h) (ω : KaehlerDifferential k A),
      algebraMap A (IsLocalRing.ResidueField A) (φ i ω)
        = ψ i ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] ω) := by
    intro i
    have hmaps : (Algebra.linearMap A (IsLocalRing.ResidueField A)).comp (φ i)
        = ((ψ i).restrictScalars A).comp
            (TensorProduct.mk A (IsLocalRing.ResidueField A) (KaehlerDifferential k A) 1) := by
      refine (Module.Free.chooseBasis A (KaehlerDifferential k A)).ext (fun j => ?_)
      simp only [LinearMap.comp_apply, Algebra.linearMap_apply, hφ, hσ,
        LinearMap.coe_restrictScalars, TensorProduct.mk_apply]
    intro ω
    have hh := LinearMap.congr_fun hmaps ω
    simpa using hh
  obtain ⟨M, hMdef⟩ : ∃ M : Matrix (Fin h) (Fin h) A,
      M = Matrix.of fun i j => φ i (KaehlerDifferential.D k A (y j)) := ⟨_, rfl⟩
  have hMapp : ∀ a b, M a b = φ a (KaehlerDifferential.D k A (y b)) := by
    intro a b; rw [hMdef]; rfl
  have hMres : ∀ a b, algebraMap A (IsLocalRing.ResidueField A) (M a b)
      = if a = b then 1 else 0 := by
    intro a b
    rw [hMapp, hres a, hψ' a b]
  have hmapM : M.map (algebraMap A (IsLocalRing.ResidueField A)) = 1 := by
    ext a b
    rw [Matrix.map_apply, hMres, Matrix.one_apply]
  have hdet1 : algebraMap A (IsLocalRing.ResidueField A) M.det = 1 := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hmapM, Matrix.det_one]
  have hdet : IsUnit M.det := by
    by_contra hcon
    have h1 : Ideal.span ({M.det} : Set A) ≠ ⊤ := fun hq =>
      hcon (Ideal.span_singleton_eq_top.mp hq)
    have hmem : M.det ∈ IsLocalRing.maximalIdeal A :=
      IsLocalRing.le_maximalIdeal h1 (Ideal.mem_span_singleton_self _)
    have hzero : algebraMap A (IsLocalRing.ResidueField A) M.det = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [hdet1] at hzero
    exact one_ne_zero hzero
  have hinvMul : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hdet
  refine ⟨h, y, fun i => (∑ l : Fin h, (M⁻¹ i l) • φ l).compDer (KaehlerDifferential.D k A),
    hspan, ?_⟩
  intro i j
  have hsum : (∑ l : Fin h, M⁻¹ i l * M l j) = if i = j then 1 else 0 := by
    rw [← Matrix.mul_apply, hinvMul, Matrix.one_apply]
  show (∑ l : Fin h, (M⁻¹ i l) • φ l) (KaehlerDifferential.D k A (y j)) = if i = j then 1 else 0
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  calc (∑ l : Fin h, M⁻¹ i l * φ l (KaehlerDifferential.D k A (y j)))
      = ∑ l : Fin h, M⁻¹ i l * M l j := by
        refine Finset.sum_congr rfl ?_
        intro l _
        rw [hMapp]
    _ = if i = j then 1 else 0 := hsum

end

end FunctorialResolution.EmbeddedResolution
