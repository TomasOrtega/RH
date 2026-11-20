import Mathlib

open scoped TensorProduct Pointwise

namespace GlobalTheory

section Ring

variable (A G : Type*) [CommRing A] [Group G] [MulSemiringAction G A]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_fixedSubring_iff {a : A} : a ∈ FixedPoints.subring A G ↔ ∀ g : G, g • a = a :=
  Iff.rfl

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_fixedSubalgebra_iff (R : Type*) [CommRing R] [Algebra R A] [SMulCommClass G R A]
    {a : A} : a ∈ FixedPoints.subalgebra R A G ↔ ∀ g : G, g • a = a :=
  Iff.rfl

instance isInvariant_fixedSubring : Algebra.IsInvariant (FixedPoints.subring A G) A G :=
  ⟨fun b hb ↦ ⟨⟨b, hb⟩, rfl⟩⟩

instance isInvariant_fixedSubalgebra (R : Type*) [CommRing R] [Algebra R A] [SMulCommClass G R A] :
    Algebra.IsInvariant (FixedPoints.subalgebra R A G) A G :=
  ⟨fun b hb ↦ ⟨⟨b, hb⟩, rfl⟩⟩

/- English proof (translation)
The claim follows from `Algebra.IsInvariant.isIntegral _ A G`.
-/
theorem isIntegral_fixedSubring [Finite G] : Algebra.IsIntegral (FixedPoints.subring A G) A :=
  Algebra.IsInvariant.isIntegral _ A G

/- English proof (translation)
The claim follows from `Algebra.IsInvariant.isIntegral _ A G`.
-/
theorem isIntegral_fixedSubalgebra [Finite G] (R : Type*) [CommRing R] [Algebra R A]
    [SMulCommClass G R A] : Algebra.IsIntegral (FixedPoints.subalgebra R A G) A :=
  Algebra.IsInvariant.isIntegral _ A G

/- English proof (translation)
Establish `hinj : Function.Injective (algebraMap B A)` using `FaithfulSMul.algebraMap_injective B A`. Use `haveI : IsDomain B := hinj.isDomain _`. Use `⟨inferInstance, ?_⟩` and prove the remaining obligations. Rewrite using `[isIntegrallyClosed_iff (FractionRing B)]`. Introduce `x hx`.

Establish `hinj' : Function.Injective ((algebraMap A (FractionRing A)).comp (algebraMap B A))` using `(IsFractionRing.injective A (FractionRing A)).comp hinj`. Set `φ : FractionRing B →+* FractionRing A` to `IsFractionRing.lift hinj'`. Establish `hφ : ∀ b : B, φ (algebraMap B _ b) = algebraMap A _ (algebraMap B A b)` using `fun b ↦ IsFractionRing.lift_algebraMap hinj' b`. Establish `hint : IsIntegral A (φ x)` using `hx.map_of_comp_eq (algebraMap B A) φ (RingHom.ext fun b ↦ (hφ b).symm)`. Take `⟨c, hc⟩` from `(isIntegrallyClosed_iff (FractionRing A)).mp ‹_› hint`.

Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective B x`. Establish `hb0 : algebraMap B A b ≠ 0`. Simplify using `using nonZeroDivisors.ne_zero hb`. Establish `hb1 : algebraMap B (FractionRing B) b ≠ 0`. Simplify using `using nonZeroDivisors.ne_zero hb`.

Establish `hb2 : algebraMap A (FractionRing A) (algebraMap B A b) ≠ 0` using `by simpa using hb0`. Establish `hcb : c * algebraMap B A b = algebraMap B A a`. Apply `IsFractionRing.injective A (FractionRing A)` to reduce the goal to its premises. Rewrite using `[map_mul, hc, map_div₀, hφ, hφ, div_mul_cancel₀ _ hb2]`. Establish `hfix : ∀ g : G, g • c = c` using `fun g ↦ by`.

Apply `mul_right_cancel₀ hb0` to reduce the goal to its premises. Use `congrArg (g • ·) hcb` as an intermediate fact. Simplify using `only [smul_mul', smul_algebraMap] at this`. Rewrite using `[this, hcb]`. Take `⟨d, rfl⟩` from `Algebra.IsInvariant.isInvariant (A := B) c hfix`.

Use `⟨d, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_div_iff hb1, ← map_mul]`. Use `congr 1`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_mul, hcb]`.
-/
theorem isIntegrallyClosed_of_isInvariant (B : Type*) [CommRing B] [Algebra B A]
    [FaithfulSMul B A] [SMulCommClass G B A] [Algebra.IsInvariant B A G]
    [IsDomain A] [IsIntegrallyClosed A] : IsDomain B ∧ IsIntegrallyClosed B := by
  have hinj : Function.Injective (algebraMap B A) := FaithfulSMul.algebraMap_injective B A
  haveI : IsDomain B := hinj.isDomain _
  refine ⟨inferInstance, ?_⟩
  rw [isIntegrallyClosed_iff (FractionRing B)]
  intro x hx
  have hinj' : Function.Injective ((algebraMap A (FractionRing A)).comp (algebraMap B A)) :=
    (IsFractionRing.injective A (FractionRing A)).comp hinj
  let φ : FractionRing B →+* FractionRing A := IsFractionRing.lift hinj'
  have hφ : ∀ b : B, φ (algebraMap B _ b) = algebraMap A _ (algebraMap B A b) :=
    fun b ↦ IsFractionRing.lift_algebraMap hinj' b
  have hint : IsIntegral A (φ x) :=
    hx.map_of_comp_eq (algebraMap B A) φ (RingHom.ext fun b ↦ (hφ b).symm)
  obtain ⟨c, hc⟩ := (isIntegrallyClosed_iff (FractionRing A)).mp ‹_› hint
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective B x
  have hb0 : algebraMap B A b ≠ 0 := by
    simpa using nonZeroDivisors.ne_zero hb
  have hb1 : algebraMap B (FractionRing B) b ≠ 0 := by
    simpa using nonZeroDivisors.ne_zero hb
  have hb2 : algebraMap A (FractionRing A) (algebraMap B A b) ≠ 0 := by simpa using hb0
  have hcb : c * algebraMap B A b = algebraMap B A a := by
    apply IsFractionRing.injective A (FractionRing A)
    rw [map_mul, hc, map_div₀, hφ, hφ, div_mul_cancel₀ _ hb2]
  have hfix : ∀ g : G, g • c = c := fun g ↦ by
    apply mul_right_cancel₀ hb0
    have := congrArg (g • ·) hcb
    simp only [smul_mul', smul_algebraMap] at this
    rw [this, hcb]
  obtain ⟨d, rfl⟩ := Algebra.IsInvariant.isInvariant (A := B) c hfix
  refine ⟨d, ?_⟩
  rw [eq_div_iff hb1, ← map_mul]
  congr 1
  apply hinj
  rw [map_mul, hcb]

/- English proof (translation)
The claim follows from `(isIntegrallyClosed_of_isInvariant A G _).2`.
-/
theorem isIntegrallyClosed_fixedSubring [IsDomain A] [IsIntegrallyClosed A] :
    IsIntegrallyClosed (FixedPoints.subring A G) :=
  (isIntegrallyClosed_of_isInvariant A G _).2

/- English proof (translation)
The claim follows from `(isIntegrallyClosed_of_isInvariant A G _).2`.
-/
theorem isIntegrallyClosed_fixedSubalgebra (R : Type*) [CommRing R] [Algebra R A]
    [SMulCommClass G R A] [IsDomain A] [IsIntegrallyClosed A] :
    IsIntegrallyClosed (FixedPoints.subalgebra R A G) :=
  (isIntegrallyClosed_of_isInvariant A G _).2

/- English proof (translation)
Use `haveI := Algebra.IsInvariant.isIntegral B A G`. Use `haveI : Algebra.FiniteType B A := Algebra.FiniteType.of_restrictScalars_finiteType R B A`. Conclude with `Algebra.IsIntegral.finite`.
-/
theorem finite_of_isInvariant [Finite G] (R B : Type*) [CommRing R] [CommRing B] [Algebra R A]
    [Algebra R B] [Algebra B A] [IsScalarTower R B A] [Algebra.IsInvariant B A G]
    [Algebra.FiniteType R A] : Module.Finite B A := by
  haveI := Algebra.IsInvariant.isIntegral B A G
  haveI : Algebra.FiniteType B A := Algebra.FiniteType.of_restrictScalars_finiteType R B A
  exact Algebra.IsIntegral.finite

/- English proof (translation)
The claim follows from `haveI := finite_of_isInvariant A G R B ⟨fg_of_fg_of_fg R B A Algebra.FiniteType.out Module.Finite.fg_top (FaithfulSMul.algebraMap_injective B A)⟩`.
-/
theorem finiteType_of_isInvariant [Finite G] (R B : Type*) [CommRing R] [CommRing B] [Algebra R A]
    [Algebra R B] [Algebra B A] [IsScalarTower R B A] [FaithfulSMul B A]
    [Algebra.IsInvariant B A G] [IsNoetherianRing R] [Algebra.FiniteType R A] :
    Algebra.FiniteType R B :=
  haveI := finite_of_isInvariant A G R B
  ⟨fg_of_fg_of_fg R B A Algebra.FiniteType.out Module.Finite.fg_top
    (FaithfulSMul.algebraMap_injective B A)⟩

/- English proof (translation)
The claim follows from `finite_of_isInvariant A G R _`.
-/
theorem finite_fixedSubalgebra [Finite G] (R : Type*) [CommRing R] [Algebra R A]
    [SMulCommClass G R A] [Algebra.FiniteType R A] :
    Module.Finite (FixedPoints.subalgebra R A G) A :=
  finite_of_isInvariant A G R _

/- English proof (translation)
The claim follows from `finiteType_of_isInvariant A G R _`.
-/
theorem finiteType_fixedSubalgebra [Finite G] (R : Type*) [CommRing R] [Algebra R A]
    [SMulCommClass G R A] [IsNoetherianRing R] [Algebra.FiniteType R A] :
    Algebra.FiniteType R (FixedPoints.subalgebra R A G) :=
  finiteType_of_isInvariant A G R _

/- English proof (translation)
The claim follows from `haveI := finiteType_fixedSubalgebra A G R Algebra.FiniteType.isNoetherianRing R _`.
-/
theorem isNoetherianRing_fixedSubalgebra [Finite G] (R : Type*) [CommRing R] [Algebra R A]
    [SMulCommClass G R A] [IsNoetherianRing R] [Algebra.FiniteType R A] :
    IsNoetherianRing (FixedPoints.subalgebra R A G) :=
  haveI := finiteType_fixedSubalgebra A G R
  Algebra.FiniteType.isNoetherianRing R _

/- English proof (translation)
Use `haveI := Algebra.IsInvariant.isIntegral B A G`. Take `⟨⟨Q, hQ, hQP⟩⟩` from `Ideal.nonempty_primesOver (S := A) P`. Conclude with `⟨Q, hQ, hQP, Algebra.IsInvariant.orbit_eq_primesOver B A G P Q⟩`.
-/
theorem exists_orbit_eq_primesOver_of_isInvariant [Finite G] (B : Type*) [CommRing B]
    [Algebra B A] [FaithfulSMul B A] [SMulCommClass G B A] [Algebra.IsInvariant B A G]
    (P : Ideal B) [P.IsPrime] :
    ∃ Q : Ideal A, Q.IsPrime ∧ Q.LiesOver P ∧ MulAction.orbit G Q = P.primesOver A := by
  haveI := Algebra.IsInvariant.isIntegral B A G
  obtain ⟨⟨Q, hQ, hQP⟩⟩ := Ideal.nonempty_primesOver (S := A) P
  exact ⟨Q, hQ, hQP, Algebra.IsInvariant.orbit_eq_primesOver B A G P Q⟩

/- English proof (translation)
The claim follows from `exists_orbit_eq_primesOver_of_isInvariant A G _ P`.
-/
theorem exists_orbit_eq_primesOver [Finite G] (P : Ideal (FixedPoints.subring A G)) [P.IsPrime] :
    ∃ Q : Ideal A, Q.IsPrime ∧ Q.LiesOver P ∧ MulAction.orbit G Q = P.primesOver A :=
  exists_orbit_eq_primesOver_of_isInvariant A G _ P

/- English proof (translation)
Assemble the required witnesses or components as `⟨Algebra.IsInvariant.exists_smul_of_under_eq B A G Q Q', by rintro ⟨g, rfl⟩; exact (Ideal.under_smul B Q g).symm⟩`.
-/
theorem under_eq_iff_exists_smul [Finite G] (B : Type*) [CommRing B]
    [Algebra B A] [SMulCommClass G B A] [Algebra.IsInvariant B A G]
    (Q Q' : Ideal A) [Q.IsPrime] [Q'.IsPrime] :
    Q.under B = Q'.under B ↔ ∃ g : G, Q' = g • Q :=
  ⟨Algebra.IsInvariant.exists_smul_of_under_eq B A G Q Q',
    by rintro ⟨g, rfl⟩; exact (Ideal.under_smul B Q g).symm⟩

end Ring

section FlatModule

variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
  {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] [Module S M']
  [IsScalarTower R S M']

/- English proof (translation)
Use `IsBaseChange.of_left_exact S k f (.pi fun i ↦ h i ∘ₗ .proj i) (f := j) (f' := j') (g := .pi fun i ↦ φ i - ψ i) (g' := .pi fun i ↦ φ' i - ψ' i) ?_ ?_ hf (IsBaseChange.pi h hh) ?_ hj ?_ hj₁` and prove the remaining obligations. Use extensionality with `x`. Simplify using `[hk]`. Use extensionality with `x i`. Simplify using `[hφ, hψ]`.

Introduce `x`. Rewrite using `[hj']`. Simplify using `[funext_iff, sub_eq_zero]`. Introduce `x`. Rewrite using `[hj₁']`.

Simplify using `[funext_iff, sub_eq_zero]`.
-/
theorem isBaseChange_of_forall_eq [Module.Flat R S] {ι : Type*} [Finite ι]
    {P P' : ι → Type*} [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)]
    [∀ i, AddCommGroup (P' i)] [∀ i, Module R (P' i)] [∀ i, Module S (P' i)]
    [∀ i, IsScalarTower R S (P' i)]
    {N N' : Type*} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N'] [Module S N']
    [IsScalarTower R S N']
    (φ ψ : ∀ i, M →ₗ[R] P i) (φ' ψ' : ∀ i, M' →ₗ[S] P' i)
    (f : M →ₗ[R] M') (hf : IsBaseChange S f) (h : ∀ i, P i →ₗ[R] P' i)
    (hh : ∀ i, IsBaseChange S (h i))
    (hφ : ∀ i x, h i (φ i x) = φ' i (f x)) (hψ : ∀ i x, h i (ψ i x) = ψ' i (f x))
    (j : N →ₗ[R] M) (hj : Function.Injective j)
    (hj' : ∀ x, x ∈ Set.range j ↔ ∀ i, φ i x = ψ i x)
    (j' : N' →ₗ[S] M') (hj₁ : Function.Injective j')
    (hj₁' : ∀ x, x ∈ Set.range j' ↔ ∀ i, φ' i x = ψ' i x)
    (k : N →ₗ[R] N') (hk : ∀ x, j' (k x) = f (j x)) : IsBaseChange S k := by
  refine IsBaseChange.of_left_exact S k f (.pi fun i ↦ h i ∘ₗ .proj i) (f := j) (f' := j')
    (g := .pi fun i ↦ φ i - ψ i) (g' := .pi fun i ↦ φ' i - ψ' i) ?_ ?_ hf
    (IsBaseChange.pi h hh) ?_ hj ?_ hj₁
  · ext x; simp [hk]
  · ext x i; simp [hφ, hψ]
  · intro x; rw [hj']; simp [funext_iff, sub_eq_zero]
  · intro x; rw [hj₁']; simp [funext_iff, sub_eq_zero]

variable {G : Type*} [Group G]

variable {S} in

def invariantsMap (ρ : Representation R G M) (ρ' : Representation S G M') (f : M →ₗ[R] M')
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) : ρ.invariants →ₗ[R] ρ'.invariants where
  toFun x := ⟨f x, fun g ↦ by rw [← hf, x.2 g]⟩
  map_add' x y := Subtype.ext (map_add f _ _)
  map_smul' r x := Subtype.ext (map_smul f _ _)

variable {S} in
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_invariantsMap (ρ : Representation R G M) (ρ' : Representation S G M')
    (f : M →ₗ[R] M') (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) (x : ρ.invariants) :
    (invariantsMap ρ ρ' f hf x : M') = f x := rfl

/- English proof (translation)
The claim follows from `isBaseChange_of_forall_eq S (ι := G) (fun g ↦ ρ g) (fun _ ↦ .id) (fun g ↦ ρ' g) (fun _ ↦ .id) f hb (fun _ ↦ f) (fun _ ↦ hb) hf (fun _ _ ↦ rfl) ρ.invariants.subtype Subtype.val_injective (fun x ↦ by simp [Representation.mem_invariants]) ρ'.invariants.subtype Subtype.val_injective …`.
-/
theorem isBaseChange_invariantsMap [Finite G] [Module.Flat R S] (ρ : Representation R G M)
    (ρ' : Representation S G M') (f : M →ₗ[R] M') (hb : IsBaseChange S f)
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) : IsBaseChange S (invariantsMap ρ ρ' f hf) :=
  isBaseChange_of_forall_eq S (ι := G) (fun g ↦ ρ g) (fun _ ↦ .id) (fun g ↦ ρ' g) (fun _ ↦ .id)
    f hb (fun _ ↦ f) (fun _ ↦ hb) hf (fun _ _ ↦ rfl) ρ.invariants.subtype
    Subtype.val_injective (fun x ↦ by simp [Representation.mem_invariants])
    ρ'.invariants.subtype Subtype.val_injective
    (fun x ↦ by simp [Representation.mem_invariants]) _ (fun _ ↦ rfl)

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `(invariantsMap ρ ρ' f hf ⟨x, hx⟩).2`. Introduce `y hy`.

Establish `key : ∀ z : ρ'.invariants, (z : M') ∈ Submodule.span S (f '' ρ.invariants)`. Introduce `z`. Proceed by induction on `z using (isBaseChange_invariantsMap S ρ ρ' f hb hf).inductionOn with`. Consider the case `zero => exact zero_mem _`. Consider the case `tmul m => exact Submodule.subset_span ⟨m, m.2, rfl⟩`.

Consider the case `smul s n hn => exact Submodule.smul_mem _ s hn`. Consider the case `add a b ha hb => exact add_mem ha hb`. Conclude with `key ⟨y, hy⟩`.
-/
theorem span_image_invariants [Finite G] [Module.Flat R S] (ρ : Representation R G M)
    (ρ' : Representation S G M') (f : M →ₗ[R] M') (hb : IsBaseChange S f)
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) :
    Submodule.span S (f '' ρ.invariants) = ρ'.invariants := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact (invariantsMap ρ ρ' f hf ⟨x, hx⟩).2
  · intro y hy
    have key : ∀ z : ρ'.invariants, (z : M') ∈ Submodule.span S (f '' ρ.invariants) := by
      intro z
      induction z using (isBaseChange_invariantsMap S ρ ρ' f hb hf).inductionOn with
      | zero => exact zero_mem _
      | tmul m => exact Submodule.subset_span ⟨m, m.2, rfl⟩
      | smul s n hn => exact Submodule.smul_mem _ s hn
      | add a b ha hb => exact add_mem ha hb
    exact key ⟨y, hy⟩

/- English proof (translation)
Set `ρ' : Representation S G (S ⊗[R] M)` to `(Module.End.baseChangeHom R S M).toMonoidHom.comp ρ`. Use `span_image_invariants S ρ ρ' (TensorProduct.mk R S M 1) (TensorProduct.isBaseChange R M S) (fun g x ↦ rfl)` as an intermediate fact. Rewrite using `[Submodule.baseChange_eq_span]`. Conclude with `(SetLike.ext_iff.mp this x)`.
-/
theorem mem_baseChange_invariants_iff [Finite G] [Module.Flat R S] (ρ : Representation R G M)
    (x : S ⊗[R] M) :
    x ∈ ρ.invariants.baseChange S ↔ ∀ g, (ρ g).baseChange S x = x := by
  let ρ' : Representation S G (S ⊗[R] M) := (Module.End.baseChangeHom R S M).toMonoidHom.comp ρ
  have := span_image_invariants S ρ ρ' (TensorProduct.mk R S M 1)
    (TensorProduct.isBaseChange R M S) (fun g x ↦ rfl)
  rw [Submodule.baseChange_eq_span]
  exact (SetLike.ext_iff.mp this x)

/- English proof (translation)
The claim follows from `Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective`.
-/
theorem injective_baseChange_invariants_subtype [Module.Flat R S] (ρ : Representation R G M) :
    Function.Injective (ρ.invariants.subtype.baseChange S) :=
  Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective

/- English proof (translation)
The claim follows from `haveI := IsLocalization.flat S T (isLocalizedModule_iff_isBaseChange T S _).mpr <| isBaseChange_invariantsMap S ρ ρ' f ((isLocalizedModule_iff_isBaseChange T S f).mp ‹_›) hf`.
-/
theorem isLocalizedModule_invariantsMap [Finite G] (T : Submonoid R) [IsLocalization T S]
    (ρ : Representation R G M) (ρ' : Representation S G M') (f : M →ₗ[R] M')
    [IsLocalizedModule T f] (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) :
    IsLocalizedModule T (invariantsMap ρ ρ' f hf) :=
  haveI := IsLocalization.flat S T
  (isLocalizedModule_iff_isBaseChange T S _).mpr <| isBaseChange_invariantsMap S ρ ρ' f
    ((isLocalizedModule_iff_isBaseChange T S f).mp ‹_›) hf

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `le_inf (Submodule.span_mono fun x hx ↦ hx.1) ?_` and prove the remaining obligations. Rewrite using `[Submodule.span_le]`. Conclude with `fun x hx ↦ hx.2`. Introduce and unpack `x ⟨hx, hW⟩`.

Establish `key : ∀ y ∈ Submodule.span S (L : Set M'), ∃ t : T, (t : R) • y ∈ L`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy => exact ⟨1, by simpa using hy⟩`. Consider the case `zero => exact ⟨1, by simp⟩`.

Consider the case `add y z _ _ hy hz`. Take `⟨t, ht⟩` from `hy`. Take `⟨u, hu⟩` from `hz`. Use `⟨t * u, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add, Submonoid.coe_mul]`.

Use `add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`. Conclude with `L.smul_mem _ ht`. Rewrite using `[mul_smul]`. Conclude with `L.smul_mem _ hu`.

Consider the case `smul s y _ hy`. Take `⟨t, ht⟩` from `hy`. Take `⟨⟨a, u⟩, hu⟩` from `IsLocalization.surj T s`. Use `⟨u * t, ?_⟩` and prove the remaining obligations. Establish `: ((u * t : T) : R) • s • y = a • (t : R) • y`.

Rewrite using `[← algebraMap_smul S a, ← hu, ← algebraMap_smul S (t : R), ← algebraMap_smul S ((u * t : T) : R), smul_smul, smul_smul, Submonoid.coe_mul, map_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `L.smul_mem _ ht`.

Take `⟨t, ht⟩` from `key x hx`. Take `⟨v, hv⟩` from `IsLocalization.map_units S t`. Establish `: x = (↑v⁻¹ : S) • ((t : R) • x)`. Rewrite using `[← algebraMap_smul S (t : R), ← hv, smul_smul, Units.inv_mul, one_smul]`. Rewrite using `[this]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨ht, (W.restrictScalars R).smul_mem _ hW⟩)`.
-/
theorem span_inf_restrictScalars_of_isLocalization (T : Submonoid R) [IsLocalization T S]
    (L : Submodule R M') (W : Submodule S M') :
    Submodule.span S ((L ⊓ W.restrictScalars R : Submodule R M') : Set M')
      = Submodule.span S (L : Set M') ⊓ W := by
  apply le_antisymm
  · refine le_inf (Submodule.span_mono fun x hx ↦ hx.1) ?_
    rw [Submodule.span_le]; exact fun x hx ↦ hx.2
  · rintro x ⟨hx, hW⟩
    have key : ∀ y ∈ Submodule.span S (L : Set M'), ∃ t : T, (t : R) • y ∈ L := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact ⟨1, by simpa using hy⟩
      | zero => exact ⟨1, by simp⟩
      | add y z _ _ hy hz =>
        obtain ⟨t, ht⟩ := hy
        obtain ⟨u, hu⟩ := hz
        refine ⟨t * u, ?_⟩
        rw [smul_add, Submonoid.coe_mul]
        refine add_mem ?_ ?_
        · rw [mul_comm, mul_smul]; exact L.smul_mem _ ht
        · rw [mul_smul]; exact L.smul_mem _ hu
      | smul s y _ hy =>
        obtain ⟨t, ht⟩ := hy
        obtain ⟨⟨a, u⟩, hu⟩ := IsLocalization.surj T s
        refine ⟨u * t, ?_⟩
        have : ((u * t : T) : R) • s • y = a • (t : R) • y := by
          rw [← algebraMap_smul S a, ← hu, ← algebraMap_smul S (t : R),
            ← algebraMap_smul S ((u * t : T) : R), smul_smul, smul_smul, Submonoid.coe_mul, map_mul]
          congr 1; ring
        rw [this]; exact L.smul_mem _ ht
    obtain ⟨t, ht⟩ := key x hx
    obtain ⟨v, hv⟩ := IsLocalization.map_units S t
    have : x = (↑v⁻¹ : S) • ((t : R) • x) := by
      rw [← algebraMap_smul S (t : R), ← hv, smul_smul, Units.inv_mul, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨ht, (W.restrictScalars R).smul_mem _ hW⟩)

end FlatModule

section FlatRing

variable (G : Type*) [Group G]

section
variable {R S A A' : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing A']
  [Algebra R S] [Algebra R A] [Algebra R A'] [Algebra S A'] [IsScalarTower R S A']
  [MulSemiringAction G A] [SMulCommClass G R A] [MulSemiringAction G A'] [SMulCommClass G S A']

variable (S) in

def fixedSubalgebraMap (f : A →ₐ[R] A') (hf : ∀ (g : G) a, f (g • a) = g • f a) :
    FixedPoints.subalgebra R A G →ₐ[R] FixedPoints.subalgebra S A' G where
  toFun x := ⟨f x, fun g ↦ by rw [← hf, x.2 g]⟩
  map_one' := Subtype.ext (map_one f)
  map_mul' x y := Subtype.ext (map_mul f _ _)
  map_zero' := Subtype.ext (map_zero f)
  map_add' x y := Subtype.ext (map_add f _ _)
  commutes' r := Subtype.ext (f.commutes r)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_fixedSubalgebraMap (f : A →ₐ[R] A') (hf : ∀ (g : G) a, f (g • a) = g • f a)
    (x : FixedPoints.subalgebra R A G) : (fixedSubalgebraMap G S f hf x : A') = f x := rfl

/- English proof (translation)
The claim follows from `isBaseChange_of_forall_eq S (ι := G) (fun g ↦ (MulSemiringAction.toAlgHom R A g).toLinearMap) (fun _ ↦ .id) (fun g ↦ (MulSemiringAction.toAlgHom S A' g).toLinearMap) (fun _ ↦ .id) f.toLinearMap hb (fun _ ↦ f.toLinearMap) (fun _ ↦ hb) hf (fun _ _ ↦ rfl) (FixedPoints.subalgebra R A …`.
-/
theorem isBaseChange_fixedSubalgebraMap [Finite G] [Module.Flat R S] (f : A →ₐ[R] A')
    (hb : IsBaseChange S f.toLinearMap) (hf : ∀ (g : G) a, f (g • a) = g • f a) :
    IsBaseChange S (fixedSubalgebraMap G S f hf).toLinearMap :=
  isBaseChange_of_forall_eq S (ι := G) (fun g ↦ (MulSemiringAction.toAlgHom R A g).toLinearMap)
    (fun _ ↦ .id) (fun g ↦ (MulSemiringAction.toAlgHom S A' g).toLinearMap) (fun _ ↦ .id)
    f.toLinearMap hb (fun _ ↦ f.toLinearMap) (fun _ ↦ hb) hf (fun _ _ ↦ rfl)
    (FixedPoints.subalgebra R A G).val.toLinearMap Subtype.val_injective
    (fun x ↦ ⟨by rintro ⟨y, rfl⟩; exact y.2, fun h ↦ ⟨⟨x, h⟩, rfl⟩⟩)
    (FixedPoints.subalgebra S A' G).val.toLinearMap Subtype.val_injective
    (fun x ↦ ⟨by rintro ⟨y, rfl⟩; exact y.2, fun h ↦ ⟨⟨x, h⟩, rfl⟩⟩) _ (fun _ ↦ rfl)

/- English proof (translation)
Use `⟨fun y hy ↦ ?_⟩` and prove the remaining obligations. Establish `key : ∀ z : FixedPoints.subalgebra S A' G, ∃ s, algebraMap S A' s = z`. Introduce `z`. Proceed by induction on `z using (isBaseChange_fixedSubalgebraMap G f hb hf).inductionOn with`. Consider the case `zero => exact ⟨0, map_zero _⟩`.

Consider the case `tmul m`. Take `⟨r, hr⟩` from `Algebra.IsInvariant.isInvariant (A := R) (G := G) (m : A) m.2`. Use `⟨algebraMap R S r, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = f m`. Rewrite using `[← hr, f.commutes, ← IsScalarTower.algebraMap_apply]`.

Consider the case `smul s n hn`. Take `⟨t, ht⟩` from `hn`. Conclude with `⟨s * t, by rw [map_mul, ht, ← Algebra.smul_def]; rfl⟩`. Consider the case `add a b ha hb`. Take `⟨t, ht⟩` from `ha`.

Take `⟨u, hu⟩` from `hb`. Conclude with `⟨t + u, by rw [map_add, ht, hu]; rfl⟩`. Conclude with `key ⟨y, hy⟩`.
-/
theorem isInvariant_of_isBaseChange [Finite G] [Module.Flat R S] [Algebra.IsInvariant R A G]
    (f : A →ₐ[R] A') (hb : IsBaseChange S f.toLinearMap)
    (hf : ∀ (g : G) a, f (g • a) = g • f a) : Algebra.IsInvariant S A' G := by
  refine ⟨fun y hy ↦ ?_⟩
  have key : ∀ z : FixedPoints.subalgebra S A' G, ∃ s, algebraMap S A' s = z := by
    intro z
    induction z using (isBaseChange_fixedSubalgebraMap G f hb hf).inductionOn with
    | zero => exact ⟨0, map_zero _⟩
    | tmul m =>
      obtain ⟨r, hr⟩ := Algebra.IsInvariant.isInvariant (A := R) (G := G) (m : A) m.2
      refine ⟨algebraMap R S r, ?_⟩
      change _ = f m
      rw [← hr, f.commutes, ← IsScalarTower.algebraMap_apply]
    | smul s n hn =>
      obtain ⟨t, ht⟩ := hn
      exact ⟨s * t, by rw [map_mul, ht, ← Algebra.smul_def]; rfl⟩
    | add a b ha hb =>
      obtain ⟨t, ht⟩ := ha
      obtain ⟨u, hu⟩ := hb
      exact ⟨t + u, by rw [map_add, ht, hu]; rfl⟩
  exact key ⟨y, hy⟩

omit [MulSemiringAction G A] [SMulCommClass G R A] [MulSemiringAction G A']
  [SMulCommClass G S A'] in

/- English proof (translation)
Rewrite using `[faithfulSMul_iff_algebraMap_injective]`. Establish `h` using `Module.Flat.lTensor_preserves_injective_linearMap (M := S) (Algebra.linearMap R A) (FaithfulSMul.algebraMap_injective R A)`. Establish `: ⇑(algebraMap S A') = hb.equiv ∘ (Algebra.linearMap R A).lTensor S ∘ (TensorProduct.rid R S).symm`. Use extensionality with `s`. Simplify using `[IsBaseChange.equiv_tmul, Algebra.algebraMap_eq_smul_one]`.

Rewrite using `[this]`. Conclude with `hb.equiv.injective.comp (h.comp (TensorProduct.rid R S).symm.injective)`.
-/
theorem faithfulSMul_of_isBaseChange [Module.Flat R S] [FaithfulSMul R A]
    (f : A →ₐ[R] A') (hb : IsBaseChange S f.toLinearMap) : FaithfulSMul S A' := by
  rw [faithfulSMul_iff_algebraMap_injective]
  have h := Module.Flat.lTensor_preserves_injective_linearMap (M := S) (Algebra.linearMap R A)
    (FaithfulSMul.algebraMap_injective R A)
  have : ⇑(algebraMap S A') =
      hb.equiv ∘ (Algebra.linearMap R A).lTensor S ∘ (TensorProduct.rid R S).symm := by
    ext s
    simp [IsBaseChange.equiv_tmul, Algebra.algebraMap_eq_smul_one]
  rw [this]
  exact hb.equiv.injective.comp (h.comp (TensorProduct.rid R S).symm.injective)

end

section
variable (R S A : Type*) [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]
  [MulSemiringAction G A] [SMulCommClass G R A]

@[instance_reducible]
noncomputable def tensorMulSemiringAction : MulSemiringAction G (S ⊗[R] A) where
  smul g x := Algebra.TensorProduct.map (AlgHom.id S S) (MulSemiringAction.toAlgHom R A g) x
  one_smul x := by
    change Algebra.TensorProduct.map _ _ x = x
    induction x with
    | zero => simp
    | tmul s a => simp
    | add x y hx hy => rw [map_add, hx, hy]
  mul_smul g h x := by
    change Algebra.TensorProduct.map _ _ x =
      Algebra.TensorProduct.map _ _ (Algebra.TensorProduct.map _ _ x)
    induction x with
    | zero => simp
    | tmul s a => simp [mul_smul]
    | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]
  smul_zero g := map_zero (Algebra.TensorProduct.map _ _)
  smul_add g := map_add (Algebra.TensorProduct.map _ _)
  smul_one g := map_one (Algebra.TensorProduct.map _ _)
  smul_mul g := map_mul (Algebra.TensorProduct.map _ _)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tensorMulSemiringAction_smul_tmul (g : G) (s : S) (a : A) :
    letI := tensorMulSemiringAction G R S A
    g • (s ⊗ₜ[R] a) = s ⊗ₜ[R] (g • a) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tensorMulSemiringAction_includeRight (g : G) (a : A) :
    letI := tensorMulSemiringAction G R S A
    (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A) (g • a) =
      g • (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A) a := rfl

/- English proof (translation)
The claim follows from `letI := tensorMulSemiringAction G R S A ⟨fun g s x ↦ map_smul (Algebra.TensorProduct.map (AlgHom.id S S) (MulSemiringAction.toAlgHom R A g)) s x⟩`.
-/
theorem tensorMulSemiringAction_smulCommClass :
    letI := tensorMulSemiringAction G R S A
    SMulCommClass G S (S ⊗[R] A) :=
  letI := tensorMulSemiringAction G R S A
  ⟨fun g s x ↦ map_smul
    (Algebra.TensorProduct.map (AlgHom.id S S) (MulSemiringAction.toAlgHom R A g)) s x⟩

/- English proof (translation)
The claim follows from `tensorMulSemiringAction_smulCommClass G R S A IsBaseChange S (fixedSubalgebraMap G S (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A) (tensorMulSemiringAction_includeRight G R S A)).toLinearMap := by letI := tensorMulSemiringAction G R S A haveI := tensorMulSemiringAction_ …`.
-/
theorem isBaseChange_fixedSubalgebra_tensor [Finite G] [Module.Flat R S] :
    letI := tensorMulSemiringAction G R S A
    haveI := tensorMulSemiringAction_smulCommClass G R S A
    IsBaseChange S (fixedSubalgebraMap G S
      (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A) (tensorMulSemiringAction_includeRight G R S A)).toLinearMap := by
  letI := tensorMulSemiringAction G R S A
  haveI := tensorMulSemiringAction_smulCommClass G R S A
  have hb : IsBaseChange S
      (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toLinearMap :=
    TensorProduct.isBaseChange R A S
  exact isBaseChange_fixedSubalgebraMap G
    (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A) hb
    (tensorMulSemiringAction_includeRight G R S A)

/- English proof (translation)
The claim follows from `letI := tensorMulSemiringAction G R S A haveI := tensorMulSemiringAction_smulCommClass G R S A isInvariant_of_isBaseChange G (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A) (TensorProduct.isBaseChange R A S) (tensorMulSemiringAction_includeRight G R S A)`.
-/
theorem isInvariant_tensor [Finite G] [Module.Flat R S] [Algebra.IsInvariant R A G] :
    letI := tensorMulSemiringAction G R S A
    Algebra.IsInvariant S (S ⊗[R] A) G :=
  letI := tensorMulSemiringAction G R S A
  haveI := tensorMulSemiringAction_smulCommClass G R S A
  isInvariant_of_isBaseChange G (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A)
    (TensorProduct.isBaseChange R A S) (tensorMulSemiringAction_includeRight G R S A)

end

section
variable {A : Type*} [CommRing A] [MulSemiringAction G A]

@[instance_reducible]
noncomputable def localizationMulSemiringAction (U : Submonoid A)
    (hU : ∀ (g : G), ∀ u ∈ U, g • u ∈ U) (A' : Type*) [CommRing A'] [Algebra A A']
    [IsLocalization U A'] : MulSemiringAction G A' where
  smul g x := IsLocalization.map A' (MulSemiringAction.toRingHom G A g)
    (show U ≤ U.comap _ from hU g) x
  one_smul x := by
    change IsLocalization.map _ _ _ x = RingHom.id A' x
    congr 1
    exact IsLocalization.ringHom_ext U (by ext a; simp)
  mul_smul g h x := by
    change IsLocalization.map _ _ _ x =
      ((IsLocalization.map A' (MulSemiringAction.toRingHom G A g)
        (show U ≤ U.comap _ from hU g)).comp (IsLocalization.map A'
          (MulSemiringAction.toRingHom G A h) (show U ≤ U.comap _ from hU h))) x
    congr 1
    exact IsLocalization.ringHom_ext U (by ext a; simp [mul_smul])
  smul_zero g := map_zero (IsLocalization.map A' _ _)
  smul_add g := map_add (IsLocalization.map A' _ _)
  smul_one g := map_one (IsLocalization.map A' _ _)
  smul_mul g := map_mul (IsLocalization.map A' _ _)

/- English proof (translation)
The claim follows from `IsLocalization.map_eq _ a`.
-/
theorem localizationMulSemiringAction_smul_algebraMap (U : Submonoid A)
    (hU : ∀ (g : G), ∀ u ∈ U, g • u ∈ U) (A' : Type*) [CommRing A'] [Algebra A A']
    [IsLocalization U A'] (g : G) (a : A) :
    letI := localizationMulSemiringAction G U hU A'
    g • algebraMap A A' a = algebraMap A A' (g • a) :=
  IsLocalization.map_eq _ a

/- English proof (translation)
The claim follows from `letI := localizationMulSemiringAction G U hU A' ⟨fun g a x ↦ by rw [Algebra.smul_def, Algebra.smul_def, smul_mul', localizationMulSemiringAction_smul_algebraMap]⟩`.
-/
theorem localizationMulSemiringAction_smulDistribClass (U : Submonoid A)
    (hU : ∀ (g : G), ∀ u ∈ U, g • u ∈ U) (A' : Type*) [CommRing A'] [Algebra A A']
    [IsLocalization U A'] :
    letI := localizationMulSemiringAction G U hU A'
    SMulDistribClass G A A' :=
  letI := localizationMulSemiringAction G U hU A'
  ⟨fun g a x ↦ by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul',
      localizationMulSemiringAction_smul_algebraMap]⟩

variable {B : Type*} [CommRing B] [Algebra B A] [SMulCommClass G B A]

/- English proof (translation)
Introduce and unpack `_ ⟨t, ht, rfl⟩`. Rewrite using `[smul_algebraMap]`. Conclude with `⟨t, ht, rfl⟩`.
-/
theorem smul_mem_algebraMapSubmonoid (T : Submonoid B) (g : G) :
    ∀ u ∈ Algebra.algebraMapSubmonoid A T, g • u ∈ Algebra.algebraMapSubmonoid A T := by
  rintro _ ⟨t, ht, rfl⟩
  rw [smul_algebraMap]
  exact ⟨t, ht, rfl⟩

/- English proof (translation)
Use `haveI := IsLocalization.flat B' T`. Establish `hf : ∀ (g : G) a, algebraMap A A' (g • a) = g • algebraMap A A' a` using `fun g a ↦ by`. Rewrite using `[Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_distrib_smul, smul_one]`. Establish `hfix : ∀ (g : G) (b : B'), g • algebraMap B' A' b = algebraMap B' A' b` using `fun g b ↦ by`. Express the relevant statement in the definitionally equal form `((MulSemiringAction.toRingHom G A' g).comp (algebraMap B' A')) b = _`.

Use `congr 1`. Use `IsLocalization.ringHom_ext T ?_` and prove the remaining obligations. Use extensionality with `b`. Simplify using `only [RingHom.comp_apply, MulSemiringAction.toRingHom_apply]`. Rewrite using `[← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply B A A', ← hf, smul_algebraMap]`.

Use `haveI : SMulCommClass G B' A' := ⟨fun g b x ↦ by rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hfix]⟩`. Establish `hb : IsBaseChange B' (IsScalarTower.toAlgHom B A A').toLinearMap` using `(isLocalizedModule_iff_isBaseChange T B' _).mp (isLocalizedModule_iff_isLocalization.mpr inferInstance)`. Conclude with `⟨this, isInvariant_of_isBaseChange G _ hb hf, fun _ ↦ faithfulSMul_of_isBaseChange _ hb⟩`.
-/
theorem isInvariant_of_isLocalization [Finite G] [Algebra.IsInvariant B A G]
    (T : Submonoid B) (B' A' : Type*) [CommRing B'] [CommRing A'] [Algebra B B'] [Algebra A A']
    [Algebra B' A'] [Algebra B A'] [IsScalarTower B B' A'] [IsScalarTower B A A']
    [IsLocalization T B'] [IsLocalization (Algebra.algebraMapSubmonoid A T) A']
    [MulSemiringAction G A'] [SMulDistribClass G A A'] :
    SMulCommClass G B' A' ∧ Algebra.IsInvariant B' A' G ∧
      (FaithfulSMul B A → FaithfulSMul B' A') := by
  haveI := IsLocalization.flat B' T
  have hf : ∀ (g : G) a, algebraMap A A' (g • a) = g • algebraMap A A' a := fun g a ↦ by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_distrib_smul, smul_one]
  have hfix : ∀ (g : G) (b : B'), g • algebraMap B' A' b = algebraMap B' A' b := fun g b ↦ by
    change ((MulSemiringAction.toRingHom G A' g).comp (algebraMap B' A')) b = _
    congr 1
    refine IsLocalization.ringHom_ext T ?_
    ext b
    simp only [RingHom.comp_apply, MulSemiringAction.toRingHom_apply]
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply B A A', ← hf,
      smul_algebraMap]
  haveI : SMulCommClass G B' A' :=
    ⟨fun g b x ↦ by rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hfix]⟩
  have hb : IsBaseChange B' (IsScalarTower.toAlgHom B A A').toLinearMap :=
    (isLocalizedModule_iff_isBaseChange T B' _).mp
      (isLocalizedModule_iff_isLocalization.mpr inferInstance)
  exact ⟨this, isInvariant_of_isBaseChange G _ hb hf, fun _ ↦ faithfulSMul_of_isBaseChange _ hb⟩

end

end FlatRing

section Generator

variable {A : Type*} [CommRing A]

/- English proof (translation)
The claim follows from `.congr (LinearEquiv.ofBijective _ he)`.
-/
theorem invertible_of_bijective_toSpanSingleton {M : Type*} [AddCommGroup M] [Module A M] {e : M}
    (he : Function.Bijective (LinearMap.toSpanSingleton A M e)) : Module.Invertible A M :=
  .congr (LinearEquiv.ofBijective _ he)

/- English proof (translation)
Take `⟨a, ha⟩` from `he.2 e'`. Take `⟨b, hb⟩` from `he'.2 e`. Simplify using `only [LinearMap.toSpanSingleton_apply] at ha hb`. Establish `: b * a = 1` using `he.1 (by simp [mul_smul, ha, hb])`. Conclude with `⟨Units.mkOfMulEqOne a b (by rw [mul_comm, this]), ha.symm⟩`.
-/
theorem exists_unit_smul_eq_of_bijective_toSpanSingleton {M : Type*} [AddCommGroup M] [Module A M]
    {e e' : M} (he : Function.Bijective (LinearMap.toSpanSingleton A M e))
    (he' : Function.Bijective (LinearMap.toSpanSingleton A M e')) :
    ∃ u : Aˣ, e' = (u : A) • e := by
  obtain ⟨a, ha⟩ := he.2 e'
  obtain ⟨b, hb⟩ := he'.2 e
  simp only [LinearMap.toSpanSingleton_apply] at ha hb
  have : b * a = 1 := he.1 (by simp [mul_smul, ha, hb])
  exact ⟨Units.mkOfMulEqOne a b (by rw [mul_comm, this]), ha.symm⟩

/- English proof (translation)
Consider the cases of `nonempty_fintype ι`. Set `φ : ∀ i, M i ≃ₗ[A] A` to `fun i ↦ (LinearEquiv.ofBijective _ (he i)).symm`. Establish `hφ : ∀ i x, φ i x • e i = x` using `fun i x ↦ (LinearEquiv.ofBijective _ (he i)).apply_symm_apply x`. Establish `hφe : ∀ i, φ i (e i) = 1` using `fun i ↦ by`. Rewrite using `[LinearEquiv.symm_apply_eq]`.

Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Set `l : (⨂[A] i, M i) →ₗ[A] A` to `PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra A ι A).compLinearMap fun i ↦ (φ i).toLinearMap)`. Establish `hl : l (PiTensorProduct.tprod A e) = 1` using `by simp [l, hφe]`. Introduce `a b hab`.

Simplify `congrArg l hab` using `[hl]`. Introduce `y`. Proceed by induction on `y using PiTensorProduct.induction_on with`. Consider the case `smul_tprod r x`. Use `⟨r * ∏ i, φ i (x i), ?_⟩` and prove the remaining obligations.

Rewrite using `[LinearMap.toSpanSingleton_apply, mul_smul, ← MultilinearMap.map_smul_univ]`. Simplify using `only [hφ]`. Consider the case `add x y hx hy`. Take `⟨a, rfl⟩` from `hx`. Take `⟨b, rfl⟩` from `hy`.

Conclude with `⟨a + b, map_add _ _ _⟩`.
-/
theorem bijective_toSpanSingleton_tprod {ι : Type*} [Finite ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)] (e : ∀ i, M i)
    (he : ∀ i, Function.Bijective (LinearMap.toSpanSingleton A (M i) (e i))) :
    Function.Bijective
      (LinearMap.toSpanSingleton A (⨂[A] i, M i) (PiTensorProduct.tprod A e)) := by
  classical
  cases nonempty_fintype ι
  let φ : ∀ i, M i ≃ₗ[A] A := fun i ↦ (LinearEquiv.ofBijective _ (he i)).symm
  have hφ : ∀ i x, φ i x • e i = x := fun i x ↦
    (LinearEquiv.ofBijective _ (he i)).apply_symm_apply x
  have hφe : ∀ i, φ i (e i) = 1 := fun i ↦ by
    rw [LinearEquiv.symm_apply_eq]; simp
  constructor
  · let l : (⨂[A] i, M i) →ₗ[A] A := PiTensorProduct.lift
      ((MultilinearMap.mkPiAlgebra A ι A).compLinearMap fun i ↦ (φ i).toLinearMap)
    have hl : l (PiTensorProduct.tprod A e) = 1 := by simp [l, hφe]
    intro a b hab
    simpa [hl] using congrArg l hab
  · intro y
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r x =>
      refine ⟨r * ∏ i, φ i (x i), ?_⟩
      rw [LinearMap.toSpanSingleton_apply, mul_smul, ← MultilinearMap.map_smul_univ]
      simp only [hφ]
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add _ _ _⟩

variable {M : Type*} [AddCommGroup M] [Module A M]

/- English proof (translation)
Use `congrArg (fun z ↦ TensorProduct.lid A M (f.rTensor M z)) (Module.Invertible.tmul_comm (R := A) (m₁ := x) (m₂ := y))` as an intermediate fact. Simplify using `using this`.
-/
theorem dual_apply_smul_comm [Module.Invertible A M] (f : Module.Dual A M) (x y : M) :
    f x • y = f y • x := by
  have := congrArg (fun z ↦ TensorProduct.lid A M (f.rTensor M z))
    (Module.Invertible.tmul_comm (R := A) (m₁ := x) (m₂ := y))
  simpa using this

/- English proof (translation)
Take `⟨s, hs⟩` from `((Module.Invertible.linearEquiv A M).symm 1).exists_finset`. Use `⟨s, Eq.symm ?_⟩` and prove the remaining obligations. Simplify `hs` using `[LinearEquiv.symm_apply_eq, Module.Invertible.linearEquiv]`.
-/
theorem exists_sum_dual_apply_eq_one (A M : Type*) [CommRing A] [AddCommGroup M] [Module A M]
    [Module.Invertible A M] : ∃ s : Finset (Module.Dual A M × M), ∑ p ∈ s, p.1 p.2 = 1 := by
  obtain ⟨s, hs⟩ := ((Module.Invertible.linearEquiv A M).symm 1).exists_finset
  refine ⟨s, Eq.symm ?_⟩
  simpa [LinearEquiv.symm_apply_eq, Module.Invertible.linearEquiv] using hs

/- English proof (translation)
Consider the cases of `nonempty_fintype ι`. Establish `key : ∀ (f : Module.Dual A M) (m : M) (x : ι → M), f m ^ Fintype.card ι • PiTensorProduct.tprod A (s` using `fun _ ↦ M) x = (∏ i, f (x i)) • PiTensorProduct.tprod A (s := fun _ ↦ M) (fun _ ↦ m) := by`. Introduce `f m x`. Rewrite using `[← MultilinearMap.map_smul_univ, ← Finset.card_univ, ← Finset.prod_const, ← MultilinearMap.map_smul_univ]`. Simplify using `only [dual_apply_smul_comm f m]`.

Rewrite using `[← sub_eq_zero]`. Use `set d := PiTensorProduct.tprod A (s := fun _ ↦ M) (fun i ↦ x (σ i)) - PiTensorProduct.tprod A (s := fun _ ↦ M) x with hd`. Set `I : Ideal A` to `LinearMap.ker (LinearMap.toSpanSingleton A _ d)`. Establish `hI : I.radical = ⊤`. Take `⟨s, hs⟩` from `exists_sum_dual_apply_eq_one A M`.

Rewrite using `[Ideal.eq_top_iff_one, ← hs]`. Use `sum_mem fun p _ ↦ ⟨Fintype.card ι, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `p.1 p.2 ^ Fintype.card ι • d = 0`. Rewrite using `[hd, smul_sub, key, key, Equiv.prod_comp σ (fun i ↦ p.1 (x i)), sub_self]`. Rewrite `hI` using `[Ideal.radical_eq_top, Ideal.eq_top_iff_one]`.

Simplify `hI` using `[I]`.
-/
theorem tprod_comp_perm [Module.Invertible A M] {ι : Type*} [Finite ι] (x : ι → M)
    (σ : Equiv.Perm ι) :
    PiTensorProduct.tprod A (s := fun _ ↦ M) (fun i ↦ x (σ i))
      = PiTensorProduct.tprod A (s := fun _ ↦ M) x := by
  classical
  cases nonempty_fintype ι
  have key : ∀ (f : Module.Dual A M) (m : M) (x : ι → M),
      f m ^ Fintype.card ι • PiTensorProduct.tprod A (s := fun _ ↦ M) x =
        (∏ i, f (x i)) • PiTensorProduct.tprod A (s := fun _ ↦ M) (fun _ ↦ m) := by
    intro f m x
    rw [← MultilinearMap.map_smul_univ, ← Finset.card_univ, ← Finset.prod_const,
      ← MultilinearMap.map_smul_univ]
    simp only [dual_apply_smul_comm f m]
  rw [← sub_eq_zero]
  set d := PiTensorProduct.tprod A (s := fun _ ↦ M) (fun i ↦ x (σ i))
      - PiTensorProduct.tprod A (s := fun _ ↦ M) x with hd
  let I : Ideal A := LinearMap.ker (LinearMap.toSpanSingleton A _ d)
  have hI : I.radical = ⊤ := by
    obtain ⟨s, hs⟩ := exists_sum_dual_apply_eq_one A M
    rw [Ideal.eq_top_iff_one, ← hs]
    refine sum_mem fun p _ ↦ ⟨Fintype.card ι, ?_⟩
    change p.1 p.2 ^ Fintype.card ι • d = 0
    rw [hd, smul_sub, key, key, Equiv.prod_comp σ (fun i ↦ p.1 (x i)), sub_self]
  rw [Ideal.radical_eq_top, Ideal.eq_top_iff_one] at hI
  simpa [I] using hI

/- English proof (translation)
The claim follows from `Module.free_of_flat_of_finrank_eq _ _ 1 fun _ ↦ let _ := @Ideal.Quotient.field A _; Module.Invertible.finrank_eq_one ..`.
-/
theorem free_of_invertible_of_finite_maximalSpectrum (A M : Type*) [CommRing A] [AddCommGroup M]
    [Module A M] [Finite (MaximalSpectrum A)] [Module.Invertible A M] : Module.Free A M :=
  Module.free_of_flat_of_finrank_eq _ _ 1
    fun _ ↦ let _ := @Ideal.Quotient.field A _; Module.Invertible.finrank_eq_one ..

/- English proof (translation)
Take `⟨φ⟩` from `Module.Invertible.free_iff_linearEquiv.mp (free_of_invertible_of_finite_maximalSpectrum A M)`. Use `⟨φ.symm 1, ?_⟩` and prove the remaining obligations. Establish `: LinearMap.toSpanSingleton A M (φ.symm 1) = φ.symm.toLinearMap` using `by ext; simp`. Rewrite using `[this]`. Conclude with `φ.symm.bijective`.
-/
theorem exists_bijective_toSpanSingleton_of_finite_maximalSpectrum (A M : Type*) [CommRing A]
    [AddCommGroup M] [Module A M] [Finite (MaximalSpectrum A)] [Module.Invertible A M] :
    ∃ e : M, Function.Bijective (LinearMap.toSpanSingleton A M e) := by
  obtain ⟨φ⟩ := Module.Invertible.free_iff_linearEquiv.mp
    (free_of_invertible_of_finite_maximalSpectrum A M)
  refine ⟨φ.symm 1, ?_⟩
  have : LinearMap.toSpanSingleton A M (φ.symm 1) = φ.symm.toLinearMap := by ext; simp
  rw [this]
  exact φ.symm.bijective

/- English proof (translation)
Establish `h1 : ∀ P ∈ s, ∃ p : Module.Dual A M × M, p.1 p.2 ∉ P`. Introduce `P hP`. Use `by_contra! h`. Take `⟨t, ht⟩` from `exists_sum_dual_apply_eq_one A M`. Conclude with `(hp P hP).ne_top ((Ideal.eq_top_iff_one _).mpr (ht ▸ sum_mem fun p _ ↦ h p))`.

Use `choose! p hp1 using h1`. Set `t : Finset (Ideal A)` to `hs.toFinset.filter fun P ↦ Maximal (· ∈ s) P`. Establish `ht : ∀ P, P ∈ t ↔ Maximal (· ∈ s) P` using `fun P ↦ by`. Simplify using `only [t, Finset.mem_filter, Set.Finite.mem_toFinset]`. Conclude with `⟨fun h ↦ h.2, fun h ↦ ⟨h.prop, h⟩⟩`.

Establish `h2 : ∀ P ∈ t, ∃ a, a ∉ P ∧ ∀ Q ∈ t, Q ≠ P → a ∈ Q`. Introduce `P hP`. Establish `hP'` using `(ht P).mp hP`. Establish `: ¬ (t.erase P).inf id ≤ P`. Rewrite using `[Ideal.IsPrime.inf_le' (hp P hP'.prop)]`.

Introduce and unpack `⟨Q, hQ, hle⟩`. Rewrite `hQ` using `[Finset.mem_erase]`. Conclude with `hQ.1 (le_antisymm hle (((ht Q).mp hQ.2).le_of_ge hP'.prop hle))`. Take `⟨a, ha, haP⟩` from `SetLike.not_le_iff_exists.mp this`. Conclude with `⟨a, haP, fun Q hQ hne ↦ (Finset.inf_le (f := id) (Finset.mem_erase.mpr ⟨hne, hQ⟩) : _ ≤ Q) ha⟩`.

Use `choose! a ha ha' using h2`. Set `e : M` to `∑ P ∈ t, a P • (p P).2`. Establish `h3 : ∀ P ∈ t, (p P).1 e ∉ P`. Introduce `P hP hmem`. Establish `hP'` using `(ht P).mp hP`.

Simplify using `only [e, map_sum, map_smul, smul_eq_mul] at hmem`. Rewrite `hmem` using `[← Finset.add_sum_erase _ _ hP]`. Establish `h4 : ∑ Q ∈ t.erase P, a Q * (p P).1 (p Q).2 ∈ P` using `sum_mem fun Q hQ ↦ Ideal.mul_mem_right _ _ (ha' Q (Finset.mem_erase.mp hQ).2 P hP (Finset.mem_erase.mp hQ).1.symm)`. Establish `h5` using `(Ideal.add_mem_iff_left _ h4).mp hmem`. Break down `(hp P hP'.prop).mem_or_mem h5 with h | h` into its components or cases.

Conclude with `ha P hP h`. Conclude with `hp1 P hP'.prop h`. Set `I : Ideal A` to `LinearMap.range (Module.Dual.eval A M e)`. Use `by_contra! h`. Establish `hsub : (I : Set A) ⊆ ⋃ P ∈ s, ((id P : Ideal A) : Set A)`.

Introduce and unpack `_ ⟨f, rfl⟩`. Take `⟨P, hP, hf⟩` from `h e f`. Conclude with `Set.mem_biUnion hP hf`. Take `⟨P, hP, hle⟩` from `(Ideal.subset_union_prime_finite hs (f := id) ⊥ ⊥ (fun i hi _ _ ↦ hp i hi)).mp hsub`. Take `⟨Q, hPQ, hQ⟩` from `hs.exists_le_maximal hP`.

Conclude with `h3 Q ((ht Q).mpr hQ) (hPQ (hle ⟨(p Q).1, rfl⟩))`.
-/
theorem exists_dual_apply_notMem_of_finite (M : Type*) [AddCommGroup M] [Module A M]
    [Module.Invertible A M] (s : Set (Ideal A)) (hs : s.Finite) (hp : ∀ P ∈ s, P.IsPrime) :
    ∃ (e : M) (f : Module.Dual A M), ∀ P ∈ s, f e ∉ P := by
  classical
  have h1 : ∀ P ∈ s, ∃ p : Module.Dual A M × M, p.1 p.2 ∉ P := by
    intro P hP
    by_contra! h
    obtain ⟨t, ht⟩ := exists_sum_dual_apply_eq_one A M
    exact (hp P hP).ne_top ((Ideal.eq_top_iff_one _).mpr (ht ▸ sum_mem fun p _ ↦ h p))
  choose! p hp1 using h1
  let t : Finset (Ideal A) := hs.toFinset.filter fun P ↦ Maximal (· ∈ s) P
  have ht : ∀ P, P ∈ t ↔ Maximal (· ∈ s) P := fun P ↦ by
    simp only [t, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨h.prop, h⟩⟩
  have h2 : ∀ P ∈ t, ∃ a, a ∉ P ∧ ∀ Q ∈ t, Q ≠ P → a ∈ Q := by
    intro P hP
    have hP' := (ht P).mp hP
    have : ¬ (t.erase P).inf id ≤ P := by
      rw [Ideal.IsPrime.inf_le' (hp P hP'.prop)]
      rintro ⟨Q, hQ, hle⟩
      rw [Finset.mem_erase] at hQ
      exact hQ.1 (le_antisymm hle (((ht Q).mp hQ.2).le_of_ge hP'.prop hle))
    obtain ⟨a, ha, haP⟩ := SetLike.not_le_iff_exists.mp this
    exact ⟨a, haP, fun Q hQ hne ↦
      (Finset.inf_le (f := id) (Finset.mem_erase.mpr ⟨hne, hQ⟩) : _ ≤ Q) ha⟩
  choose! a ha ha' using h2
  let e : M := ∑ P ∈ t, a P • (p P).2
  have h3 : ∀ P ∈ t, (p P).1 e ∉ P := by
    intro P hP hmem
    have hP' := (ht P).mp hP
    simp only [e, map_sum, map_smul, smul_eq_mul] at hmem
    rw [← Finset.add_sum_erase _ _ hP] at hmem
    have h4 : ∑ Q ∈ t.erase P, a Q * (p P).1 (p Q).2 ∈ P :=
      sum_mem fun Q hQ ↦ Ideal.mul_mem_right _ _
        (ha' Q (Finset.mem_erase.mp hQ).2 P hP (Finset.mem_erase.mp hQ).1.symm)
    have h5 := (Ideal.add_mem_iff_left _ h4).mp hmem
    rcases (hp P hP'.prop).mem_or_mem h5 with h | h
    · exact ha P hP h
    · exact hp1 P hP'.prop h
  let I : Ideal A := LinearMap.range (Module.Dual.eval A M e)
  by_contra! h
  have hsub : (I : Set A) ⊆ ⋃ P ∈ s, ((id P : Ideal A) : Set A) := by
    rintro _ ⟨f, rfl⟩
    obtain ⟨P, hP, hf⟩ := h e f
    exact Set.mem_biUnion hP hf
  obtain ⟨P, hP, hle⟩ := (Ideal.subset_union_prime_finite hs (f := id) ⊥ ⊥
    (fun i hi _ _ ↦ hp i hi)).mp hsub
  obtain ⟨Q, hPQ, hQ⟩ := hs.exists_le_maximal hP
  exact h3 Q ((ht Q).mpr hQ) (hPQ (hle ⟨(p Q).1, rfl⟩))

/- English proof (translation)
Use `haveI : Module.Invertible A' M' := .congr hl.equiv`. Use `Module.Invertible.bijective_of_surjective fun y ↦ ?_` and prove the remaining obligations. Proceed by induction on `y using hl.inductionOn with`. Consider the case `zero => exact ⟨0, map_zero _⟩`. Consider the case `tmul m`.

Take `⟨u, hu⟩` from `hu`. Use `⟨↑u⁻¹ * algebraMap A A' (f m), ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.toSpanSingleton_apply, mul_smul, algebraMap_smul, ← map_smul, dual_apply_smul_comm, map_smul, ← algebraMap_smul A' (f e), ← hu, smul_smul, Units.inv_mul, one_smul]`. Consider the case `smul s n hn`. Take `⟨a, rfl⟩` from `hn`.

Conclude with `⟨s • a, map_smul _ _ _⟩`. Consider the case `add x y hx hy`. Take `⟨a, rfl⟩` from `hx`. Take `⟨b, rfl⟩` from `hy`. Conclude with `⟨a + b, map_add _ _ _⟩`.
-/
theorem bijective_toSpanSingleton_of_isBaseChange [Module.Invertible A M] (f : Module.Dual A M)
    (e : M) {A' M' : Type*} [CommRing A'] [Algebra A A'] [AddCommGroup M'] [Module A M']
    [Module A' M'] [IsScalarTower A A' M'] (l : M →ₗ[A] M') (hl : IsBaseChange A' l)
    (hu : IsUnit (algebraMap A A' (f e))) :
    Function.Bijective (LinearMap.toSpanSingleton A' M' (l e)) := by
  haveI : Module.Invertible A' M' := .congr hl.equiv
  refine Module.Invertible.bijective_of_surjective fun y ↦ ?_
  induction y using hl.inductionOn with
  | zero => exact ⟨0, map_zero _⟩
  | tmul m =>
    obtain ⟨u, hu⟩ := hu
    refine ⟨↑u⁻¹ * algebraMap A A' (f m), ?_⟩
    rw [LinearMap.toSpanSingleton_apply, mul_smul, algebraMap_smul, ← map_smul,
      dual_apply_smul_comm, map_smul, ← algebraMap_smul A' (f e), ← hu, smul_smul, Units.inv_mul,
      one_smul]
  | smul s n hn =>
    obtain ⟨a, rfl⟩ := hn
    exact ⟨s • a, map_smul _ _ _⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩

/- English proof (translation)
Consider the cases of `nonempty_fintype G`. Take `⟨e, f, hf⟩` from `exists_dual_apply_notMem_of_finite M (MulAction.orbit G Q) (Set.finite_range _) (by rintro _ ⟨g, rfl⟩; exact Ideal.IsPrime.smul g)`. Establish `hinv : ∀ g : G, g • ∏ h : G, h • f e = ∏ h : G, h • f e` using `Finset.smul_prod_perm (f e)`. Use `⟨∏ h : G, h • f e, e, hinv, fun g hg ↦ ?_, (∏ h ∈ Finset.univ.erase (1 : G), h • f e) • f, ?_⟩` and prove the remaining obligations. Use `haveI : (g • Q).IsPrime := Ideal.IsPrime.smul g`.

Take `⟨h, -, hh⟩` from `Ideal.IsPrime.prod_mem_iff.mp hg`. Conclude with `hf (h⁻¹ • g • Q) ⟨h⁻¹ * g, mul_smul _ _ _⟩ (Ideal.mem_inv_pointwise_smul_iff.mpr hh)`. Rewrite using `[← Finset.prod_erase_mul _ _ (Finset.mem_univ (1 : G)), one_smul]`. Both sides reduce to the same expression.
-/
theorem exists_invariant_notMem_orbit_generator (G : Type*) [Group G] [Finite G]
    [MulSemiringAction G A] (M : Type*) [AddCommGroup M] [Module A M] [Module.Invertible A M]
    (Q : Ideal A) [Q.IsPrime] :
    ∃ (s : A) (e : M), (∀ g : G, g • s = s) ∧ (∀ g : G, s ∉ g • Q) ∧
      ∃ f : Module.Dual A M, f e = s := by
  classical
  cases nonempty_fintype G
  obtain ⟨e, f, hf⟩ := exists_dual_apply_notMem_of_finite M (MulAction.orbit G Q)
    (Set.finite_range _) (by rintro _ ⟨g, rfl⟩; exact Ideal.IsPrime.smul g)
  have hinv : ∀ g : G, g • ∏ h : G, h • f e = ∏ h : G, h • f e := Finset.smul_prod_perm (f e)
  refine ⟨∏ h : G, h • f e, e, hinv, fun g hg ↦ ?_,
    (∏ h ∈ Finset.univ.erase (1 : G), h • f e) • f, ?_⟩
  · haveI : (g • Q).IsPrime := Ideal.IsPrime.smul g
    obtain ⟨h, -, hh⟩ := Ideal.IsPrime.prod_mem_iff.mp hg
    exact hf (h⁻¹ • g • Q) ⟨h⁻¹ * g, mul_smul _ _ _⟩ (Ideal.mem_inv_pointwise_smul_iff.mpr hh)
  · rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (1 : G)), one_smul]
    rfl

end Generator

section Semilinear

noncomputable def piTensorMapₛₗ {A A' : Type*} [CommRing A] [CommRing A'] (σ : A →+* A')
    {ι : Type*} {M N : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, AddCommGroup (N i)] [∀ i, Module A' (N i)] (f : ∀ i, M i →ₛₗ[σ] N i) :
    (⨂[A] i, M i) →ₛₗ[σ] ⨂[A'] i, N i where
  __ := PiTensorProduct.liftAddHom
    (fun p : A × ∀ i, M i ↦ σ p.1 • PiTensorProduct.tprod A' fun i ↦ f i (p.2 i))
    (fun r x i hx ↦ by
      rw [MultilinearMap.map_coord_zero _ i (by simp [hx]), smul_zero])
    (fun x ↦ by simp)
    (fun r x i m₁ m₂ ↦ by
      simp only [Function.apply_update (fun i ↦ (f i : M i → N i)), map_add,
        MultilinearMap.map_update_add, smul_add])
    (fun r r' x ↦ by simp [add_smul])
    (fun r x i r' ↦ by
      simp only [Function.apply_update (fun i ↦ (f i : M i → N i)), map_smulₛₗ,
        MultilinearMap.map_update_smul, Function.update_eq_self, map_mul, smul_smul, mul_comm])
  map_smul' r y := by
    induction y using PiTensorProduct.induction_on' with
    | tprodCoeff z x =>
      rw [PiTensorProduct.smul_tprodCoeff']
      change σ (r * z) • (PiTensorProduct.tprod A' fun i ↦ f i (x i)) =
        σ r • σ z • PiTensorProduct.tprod A' fun i ↦ f i (x i)
      rw [map_mul, mul_smul]
    | add x y hx hy =>
      simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe] at hx hy ⊢
      rw [smul_add, map_add, map_add, hx, hy, smul_add]

/- English proof (translation)
Rewrite using `[PiTensorProduct.tprod_eq_tprodCoeff_one]`. Express the relevant statement in the definitionally equal form `σ 1 • (PiTensorProduct.tprod A' fun i ↦ f i (x i)) = _`. Rewrite using `[map_one, one_smul]`.
-/
@[simp] theorem piTensorMapₛₗ_tprod {A A' : Type*} [CommRing A] [CommRing A'] (σ : A →+* A')
    {ι : Type*} {M N : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, AddCommGroup (N i)] [∀ i, Module A' (N i)] (f : ∀ i, M i →ₛₗ[σ] N i) (x : ∀ i, M i) :
    piTensorMapₛₗ σ f (PiTensorProduct.tprod A x) =
      PiTensorProduct.tprod A' fun i ↦ f i (x i) := by
  rw [PiTensorProduct.tprod_eq_tprodCoeff_one]
  change σ 1 • (PiTensorProduct.tprod A' fun i ↦ f i (x i)) = _
  rw [map_one, one_smul]

variable {G : Type*} [Group G] (A : Type*) [CommRing A] [MulSemiringAction G A]

section
variable (M : Type*) [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]

def smulSemilinearMap (g : G) : M →ₛₗ[MulSemiringAction.toRingHom G A g] M where
  toFun x := g • x
  map_add' := smul_add g
  map_smul' a x := smul_distrib_smul g a x

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem smulSemilinearMap_apply (g : G) (x : M) : smulSemilinearMap A M g x = g • x := rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun g b x ↦ by rw [← algebraMap_smul A b, smul_distrib_smul, smul_algebraMap, algebraMap_smul]⟩`.
-/
theorem smulCommClass_of_smulDistribClass (B : Type*) [CommRing B] [Algebra B A]
    [SMulCommClass G B A] [Module B M] [IsScalarTower B A M] : SMulCommClass G B M :=
  ⟨fun g b x ↦ by
    rw [← algebraMap_smul A b, smul_distrib_smul, smul_algebraMap, algebraMap_smul]⟩

instance smulCommClass_fixedSubring : SMulCommClass G (FixedPoints.subring A G) M :=
  smulCommClass_of_smulDistribClass A M _

variable {A M}

/- English proof (translation)
Establish `: ⇑(LinearMap.toSpanSingleton A M (g • e)) = (g • ·) ∘ LinearMap.toSpanSingleton A M e ∘ (g⁻¹ • ·)`. Use extensionality with `a`. Simplify using `[smul_distrib_smul]`. Rewrite using `[this]`. Conclude with `(MulAction.bijective g).comp (he.comp (MulAction.bijective g⁻¹))`.
-/
theorem bijective_toSpanSingleton_smul {e : M}
    (he : Function.Bijective (LinearMap.toSpanSingleton A M e)) (g : G) :
    Function.Bijective (LinearMap.toSpanSingleton A M (g • e)) := by
  have : ⇑(LinearMap.toSpanSingleton A M (g • e)) =
      (g • ·) ∘ LinearMap.toSpanSingleton A M e ∘ (g⁻¹ • ·) := by
    ext a
    simp [smul_distrib_smul]
  rw [this]
  exact (MulAction.bijective g).comp (he.comp (MulAction.bijective g⁻¹))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hy`. Take `⟨a, rfl⟩` from `hn.2 y`. Use `⟨a, fun g ↦ hn.1 ?_, rfl⟩` and prove the remaining obligations. Simplify `hy g` using `[smul_distrib_smul, hn']`.

Introduce and unpack `⟨a, ha, rfl⟩ g`. Rewrite using `[smul_distrib_smul, ha g, hn']`.
-/
theorem forall_smul_eq_iff_of_invariant_generator {n : M}
    (hn : Function.Bijective (LinearMap.toSpanSingleton A M n)) (hn' : ∀ g : G, g • n = n)
    (y : M) : (∀ g : G, g • y = y) ↔ ∃ a ∈ FixedPoints.subring A G, y = a • n := by
  constructor
  · intro hy
    obtain ⟨a, rfl⟩ := hn.2 y
    refine ⟨a, fun g ↦ hn.1 ?_, rfl⟩
    simpa [smul_distrib_smul, hn'] using hy g
  · rintro ⟨a, ha, rfl⟩ g
    rw [smul_distrib_smul, ha g, hn']

variable (B : Type*) [CommRing B] [Algebra B A] [FaithfulSMul B A] [SMulCommClass G B A]
  [Algebra.IsInvariant B A G] [Module B M] [IsScalarTower B A M] [SMulCommClass G B M]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `a b hab`. Apply `FaithfulSMul.algebraMap_injective B A` to reduce the goal to its premises. Apply `hn.1` to reduce the goal to its premises. Simplify using `using congrArg Subtype.val hab`.

Introduce and unpack `⟨y, hy⟩`. Take `⟨a, ha, rfl⟩` from `(forall_smul_eq_iff_of_invariant_generator hn hn' y).mp hy`. Take `⟨b, rfl⟩` from `Algebra.IsInvariant.isInvariant (A := B) (G := G) a ha`. Conclude with `⟨b, Subtype.ext (by simp)⟩`.
-/
theorem bijective_toSpanSingleton_invariants {n : M}
    (hn : Function.Bijective (LinearMap.toSpanSingleton A M n)) (hn' : ∀ g : G, g • n = n) :
    Function.Bijective (LinearMap.toSpanSingleton B
      (Representation.ofDistribMulAction B G M).invariants ⟨n, hn'⟩) := by
  constructor
  · intro a b hab
    apply FaithfulSMul.algebraMap_injective B A
    apply hn.1
    simpa using congrArg Subtype.val hab
  · rintro ⟨y, hy⟩
    obtain ⟨a, ha, rfl⟩ := (forall_smul_eq_iff_of_invariant_generator hn hn' y).mp hy
    obtain ⟨b, rfl⟩ := Algebra.IsInvariant.isInvariant (A := B) (G := G) a ha
    exact ⟨b, Subtype.ext (by simp)⟩

/- English proof (translation)
Use `(IsBaseChange.iff_of_equiv_comm (f := Algebra.linearMap B A) (LinearEquiv.ofBijective _ (bijective_toSpanSingleton_invariants B hn hn')) (LinearEquiv.ofBijective _ hn) ?_).mp (IsBaseChange.linearMap B A)` and prove the remaining obligations. Use `ext`. Simplify using the standard rewrite rules.
-/
theorem isBaseChange_invariants_subtype {n : M}
    (hn : Function.Bijective (LinearMap.toSpanSingleton A M n)) (hn' : ∀ g : G, g • n = n) :
    IsBaseChange A (Representation.ofDistribMulAction B G M).invariants.subtype := by
  refine (IsBaseChange.iff_of_equiv_comm (f := Algebra.linearMap B A)
    (LinearEquiv.ofBijective _ (bijective_toSpanSingleton_invariants B hn hn'))
    (LinearEquiv.ofBijective _ hn) ?_).mp (IsBaseChange.linearMap B A)
  ext
  simp

end

section
variable (G) {ι : Type*} (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
  [∀ i, DistribMulAction G (M i)] [∀ i, SMulDistribClass G A (M i)]

@[instance_reducible]
noncomputable def piTensorDistribMulAction : DistribMulAction G (⨂[A] i, M i) where
  smul g y := piTensorMapₛₗ _ (fun i ↦ smulSemilinearMap A (M i) g) y
  one_smul y := by
    change piTensorMapₛₗ _ _ y = y
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r x => simp [map_smulₛₗ]
    | add x y hx hy => rw [map_add, hx, hy]
  mul_smul g h y := by
    change piTensorMapₛₗ _ _ y = piTensorMapₛₗ _ _ (piTensorMapₛₗ _ _ y)
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r x => simp [map_smulₛₗ, mul_smul]
    | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]
  smul_zero g := map_zero (piTensorMapₛₗ _ _)
  smul_add g := map_add (piTensorMapₛₗ _ _)

/- English proof (translation)
The claim follows from `piTensorMapₛₗ_tprod _ _ x`.
-/
theorem piTensorDistribMulAction_smul_tprod (g : G) (x : ∀ i, M i) :
    letI := piTensorDistribMulAction G A M
    g • PiTensorProduct.tprod A x = PiTensorProduct.tprod A fun i ↦ g • x i :=
  piTensorMapₛₗ_tprod _ _ x

/- English proof (translation)
The claim follows from `letI := piTensorDistribMulAction G A M ⟨fun g a y ↦ map_smulₛₗ (piTensorMapₛₗ _ (fun i ↦ smulSemilinearMap A (M i) g)) a y⟩`.
-/
theorem piTensorDistribMulAction_smulDistribClass :
    letI := piTensorDistribMulAction G A M
    SMulDistribClass G A (⨂[A] i, M i) :=
  letI := piTensorDistribMulAction G A M
  ⟨fun g a y ↦ map_smulₛₗ (piTensorMapₛₗ _ (fun i ↦ smulSemilinearMap A (M i) g)) a y⟩

end

section
variable {M : Type*} [AddCommGroup M] [Module A M] [DistribMulAction G M] {ι : Type*}

omit [MulSemiringAction G A] in

noncomputable def tensorNorm (κ : ι ≃ G) (x : M) : ⨂[A] _ : ι, M :=
  PiTensorProduct.tprod A fun i ↦ κ i • x

omit [MulSemiringAction G A] in

/- English proof (translation)
Use `haveI : Finite ι := .of_equiv _ κ.symm`. Rewrite using `[tensorNorm, tensorNorm, ← tprod_comp_perm (fun i ↦ κ' i • x) (κ.trans κ'.symm)]`. Simplify using the standard rewrite rules.
-/
theorem tensorNorm_eq_of_equiv [Finite G] [Module.Invertible A M] (κ κ' : ι ≃ G) (x : M) :
    tensorNorm A κ x = tensorNorm A κ' x := by
  haveI : Finite ι := .of_equiv _ κ.symm
  rw [tensorNorm, tensorNorm, ← tprod_comp_perm (fun i ↦ κ' i • x) (κ.trans κ'.symm)]
  simp

omit [MulSemiringAction G A] in

/- English proof (translation)
Rewrite using `[← tensorNorm_eq_of_equiv A (κ.trans (Equiv.mulRight g)) κ x]`. Simplify using `[tensorNorm, mul_smul]`.
-/
theorem tensorNorm_smul_group [Finite G] [Module.Invertible A M] (κ : ι ≃ G) (g : G) (x : M) :
    tensorNorm A κ (g • x) = tensorNorm A κ x := by
  rw [← tensorNorm_eq_of_equiv A (κ.trans (Equiv.mulRight g)) κ x]
  simp [tensorNorm, mul_smul]

variable [SMulDistribClass G A M]

/- English proof (translation)
Use `letI : Fintype ι := .ofEquiv _ κ.symm`. Simplify using `only [tensorNorm, smul_distrib_smul]`. Rewrite using `[MultilinearMap.map_smul_univ, Equiv.prod_comp κ (fun g ↦ g • a)]`.
-/
theorem tensorNorm_smul [Fintype G] (κ : ι ≃ G) (a : A) (x : M) :
    tensorNorm A κ (a • x) = (∏ g : G, g • a) • tensorNorm A κ x := by
  letI : Fintype ι := .ofEquiv _ κ.symm
  simp only [tensorNorm, smul_distrib_smul]
  rw [MultilinearMap.map_smul_univ, Equiv.prod_comp κ (fun g ↦ g • a)]

/- English proof (translation)
Use `conv_rhs => rw [← tensorNorm_eq_of_equiv A (κ.trans (Equiv.mulLeft g)) κ x]`. Rewrite using `[tensorNorm, piTensorDistribMulAction_smul_tprod]`. Simplify using `[tensorNorm, mul_smul]`.
-/
theorem smul_tensorNorm [Finite G] [Module.Invertible A M] (κ : ι ≃ G) (x : M) (g : G) :
    letI := piTensorDistribMulAction G A (fun _ : ι ↦ M)
    g • tensorNorm A κ x = tensorNorm A κ x := by
  conv_rhs => rw [← tensorNorm_eq_of_equiv A (κ.trans (Equiv.mulLeft g)) κ x]
  rw [tensorNorm, piTensorDistribMulAction_smul_tprod]
  simp [tensorNorm, mul_smul]

variable {A}

/- English proof (translation)
The claim follows from `haveI : Finite ι := .of_equiv _ κ.symm bijective_toSpanSingleton_tprod _ fun i ↦ bijective_toSpanSingleton_smul he (κ i)`.
-/
theorem bijective_toSpanSingleton_tensorNorm [Finite G] (κ : ι ≃ G) {e : M}
    (he : Function.Bijective (LinearMap.toSpanSingleton A M e)) :
    Function.Bijective (LinearMap.toSpanSingleton A _ (tensorNorm A κ e)) :=
  haveI : Finite ι := .of_equiv _ κ.symm
  bijective_toSpanSingleton_tprod _ fun i ↦ bijective_toSpanSingleton_smul he (κ i)

/- English proof (translation)
Consider the cases of `nonempty_fintype G`. Take `⟨h, rfl⟩` from `exists_unit_smul_eq_of_bijective_toSpanSingleton he he'`. Use `⟨Units.mkOfMulEqOne ⟨∏ g : G, g • (h : A), Finset.smul_prod_perm _⟩ ⟨∏ g : G, g • (↑h⁻¹ : A), Finset.smul_prod_perm _⟩ (Subtype.ext ?_), tensorNorm_smul A κ _ _⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(∏ g : G, g • (h : A)) * ∏ g : G, g • (↑h⁻¹ : A) = 1`. Simplify using `[← Finset.prod_mul_distrib, ← smul_mul']`.
-/
theorem exists_unit_tensorNorm_eq [Finite G] (κ : ι ≃ G) {e e' : M}
    (he : Function.Bijective (LinearMap.toSpanSingleton A M e))
    (he' : Function.Bijective (LinearMap.toSpanSingleton A M e')) :
    ∃ u : (FixedPoints.subring A G)ˣ,
      tensorNorm A κ e' = ((u : FixedPoints.subring A G) : A) • tensorNorm A κ e := by
  cases nonempty_fintype G
  obtain ⟨h, rfl⟩ := exists_unit_smul_eq_of_bijective_toSpanSingleton he he'
  refine ⟨Units.mkOfMulEqOne ⟨∏ g : G, g • (h : A), Finset.smul_prod_perm _⟩
    ⟨∏ g : G, g • (↑h⁻¹ : A), Finset.smul_prod_perm _⟩ (Subtype.ext ?_), tensorNorm_smul A κ _ _⟩
  change (∏ g : G, g • (h : A)) * ∏ g : G, g • (↑h⁻¹ : A) = 1
  simp [← Finset.prod_mul_distrib, ← smul_mul']

/- English proof (translation)
The claim follows from `letI := piTensorDistribMulAction G A (fun _ : ι ↦ M) haveI := piTensorDistribMulAction_smulDistribClass G A (fun _ : ι ↦ M) haveI := invertible_of_bijective_toSpanSingleton he forall_smul_eq_iff_of_invariant_generator (bijective_toSpanSingleton_tensorNorm κ he) (smul_tensorNorm A …`.
-/
theorem forall_smul_eq_iff_tensorNorm [Finite G] (κ : ι ≃ G) {e : M}
    (he : Function.Bijective (LinearMap.toSpanSingleton A M e)) (y : ⨂[A] _ : ι, M) :
    letI := piTensorDistribMulAction G A (fun _ : ι ↦ M)
    (∀ g : G, g • y = y) ↔ ∃ a ∈ FixedPoints.subring A G, y = a • tensorNorm A κ e :=
  letI := piTensorDistribMulAction G A (fun _ : ι ↦ M)
  haveI := piTensorDistribMulAction_smulDistribClass G A (fun _ : ι ↦ M)
  haveI := invertible_of_bijective_toSpanSingleton he
  forall_smul_eq_iff_of_invariant_generator (bijective_toSpanSingleton_tensorNorm κ he)
    (smul_tensorNorm A κ e) y

end

end Semilinear

/- English proof (translation)
Take `⟨s, e, h1, h2, f, hf⟩` from `exists_invariant_notMem_orbit_generator G M Q`. Conclude with `⟨s, e, h1, h2, bijective_toSpanSingleton_of_isBaseChange f e _ (IsLocalizedModule.isBaseChange (.powers s) _ _) (by rw [hf]; exact IsLocalization.Away.algebraMap_isUnit s)⟩`.
-/
theorem exists_invariant_notMem_orbit_bijective (G : Type*) [Group G] [Finite G] {A : Type*}
    [CommRing A] [MulSemiringAction G A] (M : Type*) [AddCommGroup M] [Module A M]
    [Module.Invertible A M] (Q : Ideal A) [Q.IsPrime] :
    ∃ (s : A) (e : M), (∀ g : G, g • s = s) ∧ (∀ g : G, s ∉ g • Q) ∧
      Function.Bijective (LinearMap.toSpanSingleton (Localization.Away s)
        (LocalizedModule (.powers s) M) (LocalizedModule.mkLinearMap (.powers s) M e)) := by
  obtain ⟨s, e, h1, h2, f, hf⟩ := exists_invariant_notMem_orbit_generator G M Q
  exact ⟨s, e, h1, h2, bijective_toSpanSingleton_of_isBaseChange f e _
    (IsLocalizedModule.isBaseChange (.powers s) _ _)
    (by rw [hf]; exact IsLocalization.Away.algebraMap_isUnit s)⟩

universe u v

/- English proof (translation)
Use `⟨isIntegral_fixedSubring A G, fun _ _ ↦ isIntegrallyClosed_of_isInvariant A G _, fun R _ _ _ _ _ ↦ ⟨finiteType_fixedSubalgebra A G R, finite_fixedSubalgebra A G R⟩, fun P _ ↦ exists_orbit_eq_primesOver A G P, fun R S M _ _ _ _ _ _ ρ ↦ ⟨injective_baseChange_invariants_subtype S ρ, …` and prove the remaining obligations. Use `letI := localizationMulSemiringAction G (Algebra.algebraMapSubmonoid A T) (smul_mem_algebraMapSubmonoid G T) (Localization (Algebra.algebraMapSubmonoid A T)) haveI := localizationMulSemiringAction_smulDistribClass G (Algebra.algebraMapSubmonoid A T) (smul_mem_algebraMapSubmonoid …`. Take `⟨h1, h2, h3⟩` from `isInvariant_of_isLocalization G (A := A) T (Localization T) (Localization (Algebra.algebraMapSubmonoid A T))`. Use `haveI := h3 inferInstance`. Use `⟨FaithfulSMul.algebraMap_injective _ _, fun x ↦ ⟨h2.isInvariant x, ?_⟩⟩` and prove the remaining obligations.

Introduce and unpack `⟨y, rfl⟩ g`. Conclude with `smul_algebraMap g y`. Use `haveI := invertible_of_bijective_toSpanSingleton he`. Conclude with `smul_tensorNorm A κ e`.
-/
theorem finite_group_invariants_and_norms (G : Type v) [Group G] [Finite G]
    (A : Type u) [CommRing A] [MulSemiringAction G A] :
    Algebra.IsIntegral (FixedPoints.subring A G) A ∧
    (IsDomain A → IsIntegrallyClosed A →
      IsDomain (FixedPoints.subring A G) ∧ IsIntegrallyClosed (FixedPoints.subring A G)) ∧
    (∀ (R : Type u) [CommRing R] [Algebra R A] [SMulCommClass G R A] [IsNoetherianRing R]
      [Algebra.FiniteType R A],
      Algebra.FiniteType R (FixedPoints.subalgebra R A G) ∧
        Module.Finite (FixedPoints.subalgebra R A G) A) ∧
    (∀ (P : Ideal (FixedPoints.subring A G)) [P.IsPrime],
      ∃ Q : Ideal A, Q.IsPrime ∧ Q.LiesOver P ∧ MulAction.orbit G Q = P.primesOver A) ∧
    (∀ (R S M : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
      [AddCommGroup M] [Module R M] (ρ : Representation R G M),
      Function.Injective (ρ.invariants.subtype.baseChange S) ∧
        ∀ x : S ⊗[R] M, x ∈ ρ.invariants.baseChange S ↔ ∀ g, (ρ g).baseChange S x = x) ∧
    (∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S] [Algebra R A]
      [SMulCommClass G R A],
      letI := tensorMulSemiringAction G R S A
      haveI := tensorMulSemiringAction_smulCommClass G R S A
      IsBaseChange S (fixedSubalgebraMap G S
        (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A)
        (tensorMulSemiringAction_includeRight G R S A)).toLinearMap) ∧
    (∀ T : Submonoid (FixedPoints.subring A G),
      letI := localizationMulSemiringAction G (Algebra.algebraMapSubmonoid A T)
        (smul_mem_algebraMapSubmonoid G T) (Localization (Algebra.algebraMapSubmonoid A T))
      Function.Injective
        (algebraMap (Localization T) (Localization (Algebra.algebraMapSubmonoid A T))) ∧
      ∀ x : Localization (Algebra.algebraMapSubmonoid A T),
        (∀ g : G, g • x = x) ↔ ∃ y : Localization T, algebraMap _ _ y = x) ∧
    (∀ (M : Type u) [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]
      (κ : Fin (Nat.card G) ≃ G) (e : M),
      Function.Bijective (LinearMap.toSpanSingleton A M e) →
      letI := piTensorDistribMulAction G A (fun _ : Fin (Nat.card G) ↦ M)
      Function.Bijective
        (LinearMap.toSpanSingleton A (⨂[A]^(Nat.card G) M) (tensorNorm A κ e)) ∧
      (∀ g : G, g • tensorNorm A κ e = tensorNorm A κ e) ∧
      (∀ e' : M, Function.Bijective (LinearMap.toSpanSingleton A M e') →
        ∃ u : (FixedPoints.subring A G)ˣ,
          tensorNorm A κ e' = ((u : FixedPoints.subring A G) : A) • tensorNorm A κ e) ∧
      ∀ y : ⨂[A]^(Nat.card G) M,
        (∀ g : G, g • y = y) ↔ ∃ a ∈ FixedPoints.subring A G, y = a • tensorNorm A κ e) ∧
    (∀ (M : Type u) [AddCommGroup M] [Module A M] [Module.Invertible A M],
      Finite (MaximalSpectrum A) →
        Module.Free A M ∧ ∃ e : M, Function.Bijective (LinearMap.toSpanSingleton A M e)) := by
  refine ⟨isIntegral_fixedSubring A G, fun _ _ ↦ isIntegrallyClosed_of_isInvariant A G _,
    fun R _ _ _ _ _ ↦ ⟨finiteType_fixedSubalgebra A G R, finite_fixedSubalgebra A G R⟩,
    fun P _ ↦ exists_orbit_eq_primesOver A G P,
    fun R S M _ _ _ _ _ _ ρ ↦
      ⟨injective_baseChange_invariants_subtype S ρ, mem_baseChange_invariants_iff S ρ⟩,
    fun R S _ _ _ _ _ _ ↦ isBaseChange_fixedSubalgebra_tensor G R S A, fun T ↦ ?_,
    fun M _ _ _ _ κ e he ↦ ⟨bijective_toSpanSingleton_tensorNorm κ he, ?_,
      fun e' he' ↦ exists_unit_tensorNorm_eq κ he he', forall_smul_eq_iff_tensorNorm κ he⟩,
    fun M _ _ _ _ ↦ ⟨free_of_invertible_of_finite_maximalSpectrum A M,
      exists_bijective_toSpanSingleton_of_finite_maximalSpectrum A M⟩⟩
  · letI := localizationMulSemiringAction G (Algebra.algebraMapSubmonoid A T)
      (smul_mem_algebraMapSubmonoid G T) (Localization (Algebra.algebraMapSubmonoid A T))
    haveI := localizationMulSemiringAction_smulDistribClass G (Algebra.algebraMapSubmonoid A T)
      (smul_mem_algebraMapSubmonoid G T) (Localization (Algebra.algebraMapSubmonoid A T))
    obtain ⟨h1, h2, h3⟩ := isInvariant_of_isLocalization G (A := A) T (Localization T)
      (Localization (Algebra.algebraMapSubmonoid A T))
    haveI := h3 inferInstance
    refine ⟨FaithfulSMul.algebraMap_injective _ _, fun x ↦ ⟨h2.isInvariant x, ?_⟩⟩
    rintro ⟨y, rfl⟩ g
    exact smul_algebraMap g y
  · haveI := invertible_of_bijective_toSpanSingleton he
    exact smul_tensorNorm A κ e

end GlobalTheory
