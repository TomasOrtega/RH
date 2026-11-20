import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.RecNZFullFacts

noncomputable section

namespace Formalism.MainNotions.Gaps.RN

open TensorProduct IsLocalRing IsDiscreteValuationRing

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Rewrite using `[pow_zero, Nat.cast_zero, Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff, Ideal.span_singleton_one]`. Consider the case `succ n ih`. Set `f : (O ⧸ Ideal.span {ϖ}) →ₗ[O] (O ⧸ Ideal.span {ϖ ^ (n + 1)})` to `(Ideal.span {ϖ}).mapQ (Ideal.span {ϖ ^ (n + 1)}) (LinearMap.mulLeft O (ϖ ^ n)) (by`.

Introduce `x hx`. Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.mp hx`. Use `Submodule.mem_comap.mpr (Ideal.mem_span_singleton'.mpr ⟨a, ?_⟩)` and prove the remaining obligations. Rewrite using `[LinearMap.mulLeft_apply]`. Use the proof step `ring)`.

Set `g : (O ⧸ Ideal.span {ϖ ^ (n + 1)}) →ₗ[O] (O ⧸ Ideal.span {ϖ ^ n})` to `(Ideal.span {ϖ ^ (n + 1)}).mapQ (Ideal.span {ϖ ^ n}) LinearMap.id (by`. Introduce `x hx`. Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.mp hx`. Use `Submodule.mem_comap.mpr (Ideal.mem_span_singleton'.mpr ⟨a * ϖ, ?_⟩)` and prove the remaining obligations. Rewrite using `[LinearMap.id_apply]`.

Use the proof step `ring)`. Establish `hf : Function.Injective f`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`.

Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk (ϖ ^ n * x) = (0 : O ⧸ Ideal.span {ϖ ^ (n + 1)}) at hx`. Rewrite `hx` using `[Submodule.Quotient.mk_eq_zero]`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Take `⟨a, ha⟩` from `Ideal.mem_span_singleton'.mp hx`. Use `Ideal.mem_span_singleton'.mpr ⟨a, ?_⟩` and prove the remaining obligations.

Establish `hne : ϖ ^ n ≠ 0` using `pow_ne_zero _ hϖ.ne_zero`. Apply `mul_left_cancel₀ hne` to reduce the goal to its premises. Rewrite using `[← ha]`. Expand and normalize the polynomial expressions, which then agree. Establish `hg : Function.Surjective g`.

Introduce `y`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Conclude with `⟨Submodule.Quotient.mk y, rfl⟩`. Establish `hex : Function.Exact f g`. Introduce `y`.

Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk y = (0 : O ⧸ Ideal.span {ϖ ^ n}) ↔ _`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Prove the components needed by the constructor for the conclusion. Introduce `hy`.

Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.mp hy`. Use `⟨Submodule.Quotient.mk a, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk (ϖ ^ n * a) = (Submodule.Quotient.mk (a * ϖ ^ n) : O ⧸ Ideal.span {ϖ ^ (n + 1)})`. Rewrite using `[mul_comm]`. Introduce and unpack `⟨x, hx⟩`.

Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk (ϖ ^ n * x) = (Submodule.Quotient.mk y : O ⧸ Ideal.span {ϖ ^ (n + 1)}) at hx`. Rewrite `hx` using `[Submodule.Quotient.eq]`. Take `⟨b, hb⟩` from `Ideal.mem_span_singleton'.mp hx`. Use `Ideal.mem_span_singleton'.mpr ⟨x - b * ϖ, ?_⟩` and prove the remaining obligations.

Take the linear combination `-hb`. Establish `hs : Module.length O (O ⧸ Ideal.span {ϖ}) = 1`. Establish `hm : IsLocalRing.maximalIdeal O = Ideal.span {ϖ}` using `by first`. Consider the case `exact (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ`. Consider the case `exact hϖ.maximalIdeal_eq`.

Rewrite using `[Module.length_eq_one_iff, ← hm]`. Use `first`. Consider the case `exact isSimpleModule_iff_isCoatom.mpr (IsLocalRing.maximalIdeal.isMaximal O).out`. Consider the case `exact isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal O))`. Consider the case `infer_instance`.

Rewrite using `[Module.length_eq_add_of_exact f g hf hg hex, hs, ih]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem length_quot_span_singleton_dvr_lemma {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ) (n : ℕ) :
    Module.length O (O ⧸ Ideal.span {ϖ ^ n}) = n := by
  induction n with
  | zero =>
    rw [pow_zero, Nat.cast_zero, Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff,
      Ideal.span_singleton_one]
  | succ n ih =>
    let f : (O ⧸ Ideal.span {ϖ}) →ₗ[O] (O ⧸ Ideal.span {ϖ ^ (n + 1)}) :=
      (Ideal.span {ϖ}).mapQ (Ideal.span {ϖ ^ (n + 1)}) (LinearMap.mulLeft O (ϖ ^ n)) (by
        intro x hx
        obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx
        refine Submodule.mem_comap.mpr (Ideal.mem_span_singleton'.mpr ⟨a, ?_⟩)
        rw [LinearMap.mulLeft_apply]
        ring)
    let g : (O ⧸ Ideal.span {ϖ ^ (n + 1)}) →ₗ[O] (O ⧸ Ideal.span {ϖ ^ n}) :=
      (Ideal.span {ϖ ^ (n + 1)}).mapQ (Ideal.span {ϖ ^ n}) LinearMap.id (by
        intro x hx
        obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx
        refine Submodule.mem_comap.mpr (Ideal.mem_span_singleton'.mpr ⟨a * ϖ, ?_⟩)
        rw [LinearMap.id_apply]
        ring)
    have hf : Function.Injective f := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      change Submodule.Quotient.mk (ϖ ^ n * x) = (0 : O ⧸ Ideal.span {ϖ ^ (n + 1)}) at hx
      rw [Submodule.Quotient.mk_eq_zero] at hx
      rw [Submodule.Quotient.mk_eq_zero]
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hx
      refine Ideal.mem_span_singleton'.mpr ⟨a, ?_⟩
      have hne : ϖ ^ n ≠ 0 := pow_ne_zero _ hϖ.ne_zero
      apply mul_left_cancel₀ hne
      rw [← ha]
      ring
    have hg : Function.Surjective g := by
      intro y
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact ⟨Submodule.Quotient.mk y, rfl⟩
    have hex : Function.Exact f g := by
      intro y
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      change Submodule.Quotient.mk y = (0 : O ⧸ Ideal.span {ϖ ^ n}) ↔ _
      rw [Submodule.Quotient.mk_eq_zero]
      constructor
      · intro hy
        obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hy
        refine ⟨Submodule.Quotient.mk a, ?_⟩
        change Submodule.Quotient.mk (ϖ ^ n * a) = (Submodule.Quotient.mk (a * ϖ ^ n) : O ⧸ Ideal.span {ϖ ^ (n + 1)})
        rw [mul_comm]
      · rintro ⟨x, hx⟩
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        change Submodule.Quotient.mk (ϖ ^ n * x) = (Submodule.Quotient.mk y : O ⧸ Ideal.span {ϖ ^ (n + 1)}) at hx
        rw [Submodule.Quotient.eq] at hx
        obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hx
        refine Ideal.mem_span_singleton'.mpr ⟨x - b * ϖ, ?_⟩
        linear_combination -hb
    have hs : Module.length O (O ⧸ Ideal.span {ϖ}) = 1 := by
      have hm : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} := by
        first
          | exact (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
          | exact hϖ.maximalIdeal_eq
      rw [Module.length_eq_one_iff, ← hm]
      first
        | exact isSimpleModule_iff_isCoatom.mpr (IsLocalRing.maximalIdeal.isMaximal O).out
        | exact isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal O))
        | infer_instance
    rw [Module.length_eq_add_of_exact f g hf hg hex, hs, ih]
    push_cast
    ring

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Take `⟨n, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ht hϖ`. Rewrite using `[IsDiscreteValuationRing.addVal_def _ u hϖ n rfl, Ideal.span_singleton_mul_left_unit u.isUnit]`. Conclude with `length_quot_span_singleton_dvr_lemma ϖ hϖ n`.
-/
theorem length_quot_span_singleton_dvr {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (t : O)
    (ht : t ≠ 0) : Module.length O (O ⧸ Ideal.span {t}) = addVal O t := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ht hϖ
  rw [IsDiscreteValuationRing.addVal_def _ u hϖ n rfl, Ideal.span_singleton_mul_left_unit u.isUnit]
  exact length_quot_span_singleton_dvr_lemma ϖ hϖ n

open Classical in

/- English proof (translation)
Use `set S := Submodule.span O ((fun x : ι → A => algebraMap A O ∘ x) '' (N : Set (ι → A))) with hS`. Set `Φ : (ι → O) →ₗ[O] O ⊗[A] ((ι → A) ⧸ N)` to `{ toFun := fun v => ∑ i, v i ⊗ₜ[A] (Submodule.Quotient.mk (Pi.single i 1) : (ι → A) ⧸ N) map_add' := fun v w => by`. Simplify using `only [Pi.add_apply, TensorProduct.add_tmul, Finset.sum_add_distrib]`. Use the proof step `map_smul' := fun c v => by`. Simplify using `only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, TensorProduct.smul_tmul'] }`.

Establish `hmk : ∀ x : ι → A, (Submodule.Quotient.mk x : (ι → A) ⧸ N) = ∑ i, x i • (Submodule.Quotient.mk (Pi.single i 1) : (ι → A) ⧸ N)`. Introduce `x`. Establish `hx : x = ∑ i, x i • Pi.single i (1 : A)`. Use extensionality with `k`. Simplify using `[Finset.sum_apply, Pi.single_apply]`.

Use `conv_lhs => rw [hx]`. Simplify using `only [← Submodule.mkQ_apply, map_sum, map_smul]`. Establish `hΦg : ∀ x : ι → A, Φ (algebraMap A O ∘ x) = (1 : O) ⊗ₜ[A] (Submodule.Quotient.mk x : (ι → A) ⧸ N)`. Introduce `x`. Express the relevant statement in the definitionally equal form `∑ i, algebraMap A O (x i) ⊗ₜ[A] (Submodule.Quotient.mk (Pi.single i 1) : (ι → A) ⧸ N) = _`.

Rewrite using `[hmk x, TensorProduct.tmul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]`. Establish `hker : S ≤ LinearMap.ker Φ`. Rewrite using `[hS, Submodule.span_le]`.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Rewrite using `[SetLike.mem_coe, LinearMap.mem_ker]`. Establish `hx0 : (Submodule.Quotient.mk x : (ι → A) ⧸ N) = 0` using `(Submodule.Quotient.mk_eq_zero N).mpr hx`. Use `show Φ (algebraMap A O ∘ x) = 0`. Rewrite using `[hΦg x, hx0, TensorProduct.tmul_zero]`.

Set `Φbar : ((ι → O) ⧸ S) →ₗ[O] O ⊗[A] ((ι → A) ⧸ N)` to `S.liftQ Φ hker`. Set `ψ1 : (ι → A) →ₗ[A] (ι → O) ⧸ S` to `(S.mkQ.restrictScalars A) ∘ₗ (LinearMap.compLeft (Algebra.linearMap A O) ι)`. Establish `hN : N ≤ LinearMap.ker ψ1`. Introduce `x hx`. Rewrite using `[LinearMap.mem_ker]`.

Use `show (Submodule.Quotient.mk (algebraMap A O ∘ x) : (ι → O) ⧸ S) = 0`. Rewrite using `[Submodule.Quotient.mk_eq_zero, hS]`. Conclude with `Submodule.subset_span ⟨x, hx, rfl⟩`. Set `ψ0 : ((ι → A) ⧸ N) →ₗ[A] (ι → O) ⧸ S` to `N.liftQ ψ1 hN`. Set `Ψ : O ⊗[A] ((ι → A) ⧸ N) →ₗ[O] (ι → O) ⧸ S` to `TensorProduct.AlgebraTensorModule.lift (LinearMap.toSpanSingleton O (((ι → A) ⧸ N) →ₗ[A] (ι → O) ⧸ S) ψ0)`.

Establish `h1 : Φbar ∘ₗ Ψ = LinearMap.id`. Apply `TensorProduct.AlgebraTensorModule.ext` to reduce the goal to its premises. Introduce `c q`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective N q`. Rewrite using `[LinearMap.comp_apply, LinearMap.id_apply, TensorProduct.AlgebraTensorModule.lift_tmul, LinearMap.toSpanSingleton_apply, LinearMap.smul_apply, Submodule.liftQ_apply, map_smul]`.

Express the relevant statement in the definitionally equal form `c • Φ (algebraMap A O ∘ x) = _`. Rewrite using `[hΦg x, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Establish `hs : ∀ i : ι, algebraMap A O ∘ (Pi.single i (1 : A) : ι → A) = Pi.single i (1 : O)`. Introduce `i`. Use extensionality with `k`.

Apply the tactic sequence `by_cases h : k = i <;> simp [Pi.single_apply, h]`. Establish `h2 : Ψ ∘ₗ Φbar = LinearMap.id`. Apply `Submodule.linearMap_qext` to reduce the goal to its premises. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, LinearMap.id_apply, Submodule.mkQ_apply, Submodule.liftQ_apply]`.

Express the relevant statement in the definitionally equal form `Ψ (∑ i, v i ⊗ₜ[A] (Submodule.Quotient.mk (Pi.single i 1) : (ι → A) ⧸ N)) = _`. Rewrite using `[map_sum]`. Simplify using `only [Ψ, TensorProduct.AlgebraTensorModule.lift_tmul, LinearMap.toSpanSingleton_apply, LinearMap.smul_apply, Submodule.liftQ_apply]`. Express the relevant statement in the definitionally equal form `∑ i, v i • (Submodule.Quotient.mk (algebraMap A O ∘ Pi.single i 1) : (ι → O) ⧸ S) = _`. Establish `hv : v = ∑ i, v i • Pi.single i (1 : O)`.

Use extensionality with `k`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Use `conv_rhs => rw [hv]`. Rewrite using `[← Submodule.mkQ_apply, map_sum]`. Simplify using `only [map_smul, Submodule.mkQ_apply, hs]`.

Conclude with `LinearEquiv.length_eq (LinearEquiv.ofLinear Φbar Ψ h1 h2)`.
-/
theorem length_pi_span_quot (A O : Type*) [CommRing A] [CommRing O] [Algebra A O] (ι : Type*) [Fintype ι]
    (N : Submodule A (ι → A)) :
    Module.length O ((ι → O) ⧸ Submodule.span O ((fun x : ι → A => algebraMap A O ∘ x) '' (N : Set (ι → A)))) =
      Module.length O (O ⊗[A] ((ι → A) ⧸ N)) := by
  set S := Submodule.span O ((fun x : ι → A => algebraMap A O ∘ x) '' (N : Set (ι → A))) with hS

  let Φ : (ι → O) →ₗ[O] O ⊗[A] ((ι → A) ⧸ N) :=
    { toFun := fun v => ∑ i, v i ⊗ₜ[A] (Submodule.Quotient.mk (Pi.single i 1) : (ι → A) ⧸ N)
      map_add' := fun v w => by
        simp only [Pi.add_apply, TensorProduct.add_tmul, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, TensorProduct.smul_tmul'] }
  have hmk : ∀ x : ι → A, (Submodule.Quotient.mk x : (ι → A) ⧸ N) =
      ∑ i, x i • (Submodule.Quotient.mk (Pi.single i 1) : (ι → A) ⧸ N) := by
    intro x
    have hx : x = ∑ i, x i • Pi.single i (1 : A) := by
      ext k
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hx]
    simp only [← Submodule.mkQ_apply, map_sum, map_smul]
  have hΦg : ∀ x : ι → A, Φ (algebraMap A O ∘ x) = (1 : O) ⊗ₜ[A] (Submodule.Quotient.mk x : (ι → A) ⧸ N) := by
    intro x
    change ∑ i, algebraMap A O (x i) ⊗ₜ[A] (Submodule.Quotient.mk (Pi.single i 1) : (ι → A) ⧸ N) = _
    rw [hmk x, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hker : S ≤ LinearMap.ker Φ := by
    rw [hS, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    have hx0 : (Submodule.Quotient.mk x : (ι → A) ⧸ N) = 0 := (Submodule.Quotient.mk_eq_zero N).mpr hx
    show Φ (algebraMap A O ∘ x) = 0
    rw [hΦg x, hx0, TensorProduct.tmul_zero]
  let Φbar : ((ι → O) ⧸ S) →ₗ[O] O ⊗[A] ((ι → A) ⧸ N) := S.liftQ Φ hker
  let ψ1 : (ι → A) →ₗ[A] (ι → O) ⧸ S :=
    (S.mkQ.restrictScalars A) ∘ₗ (LinearMap.compLeft (Algebra.linearMap A O) ι)
  have hN : N ≤ LinearMap.ker ψ1 := by
    intro x hx
    rw [LinearMap.mem_ker]
    show (Submodule.Quotient.mk (algebraMap A O ∘ x) : (ι → O) ⧸ S) = 0
    rw [Submodule.Quotient.mk_eq_zero, hS]
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  let ψ0 : ((ι → A) ⧸ N) →ₗ[A] (ι → O) ⧸ S := N.liftQ ψ1 hN
  let Ψ : O ⊗[A] ((ι → A) ⧸ N) →ₗ[O] (ι → O) ⧸ S :=
    TensorProduct.AlgebraTensorModule.lift (LinearMap.toSpanSingleton O (((ι → A) ⧸ N) →ₗ[A] (ι → O) ⧸ S) ψ0)
  have h1 : Φbar ∘ₗ Ψ = LinearMap.id := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro c q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N q
    rw [LinearMap.comp_apply, LinearMap.id_apply, TensorProduct.AlgebraTensorModule.lift_tmul,
      LinearMap.toSpanSingleton_apply, LinearMap.smul_apply, Submodule.liftQ_apply, map_smul]
    change c • Φ (algebraMap A O ∘ x) = _
    rw [hΦg x, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hs : ∀ i : ι, algebraMap A O ∘ (Pi.single i (1 : A) : ι → A) = Pi.single i (1 : O) := by
    intro i
    ext k
    by_cases h : k = i <;> simp [Pi.single_apply, h]
  have h2 : Ψ ∘ₗ Φbar = LinearMap.id := by
    apply Submodule.linearMap_qext
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, LinearMap.id_apply, Submodule.mkQ_apply, Submodule.liftQ_apply]
    change Ψ (∑ i, v i ⊗ₜ[A] (Submodule.Quotient.mk (Pi.single i 1) : (ι → A) ⧸ N)) = _
    rw [map_sum]
    simp only [Ψ, TensorProduct.AlgebraTensorModule.lift_tmul, LinearMap.toSpanSingleton_apply,
      LinearMap.smul_apply, Submodule.liftQ_apply]
    change ∑ i, v i • (Submodule.Quotient.mk (algebraMap A O ∘ Pi.single i 1) : (ι → O) ⧸ S) = _
    have hv : v = ∑ i, v i • Pi.single i (1 : O) := by
      ext k
      simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hv]
    rw [← Submodule.mkQ_apply, map_sum]
    simp only [map_smul, Submodule.mkQ_apply, hs]
  exact LinearEquiv.length_eq (LinearEquiv.ofLinear Φbar Ψ h1 h2)

/- English proof (translation)
Introduce `A O _ _ _ _ _ _ f hloc hinj ϖ hϖ ι _ N`. Use `letI : Algebra A O := f.toAlgebra`. Use `haveI : IsLocalHom (algebraMap A O) := hloc`. Use `haveI : Module.IsTorsionFree A O := Module.IsTorsionFree.of_smul_eq_zero (fun a c h => by`. Rewrite `h` using `[Algebra.smul_def, mul_eq_zero]`.

Conclude with `h.imp_left (fun h0 => hinj (h0.trans (map_zero f).symm)))`. Use `haveI : Module.Flat A O := inferInstance`. Establish `h0 : f ϖ ≠ 0` using `fun h => hϖ.ne_zero (hinj (h.trans (map_zero f).symm))`. Establish `h1` using `length_pi_span_quot A O ι N`. Establish `h2 : (IsLocalRing.maximalIdeal A).map (algebraMap A O) = Ideal.span {f ϖ}`.

Rewrite using `[hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]`. Both sides reduce to the same expression. Establish `h3 : ((addVal O (f ϖ)).toNat : ℕ∞) = addVal O (f ϖ)` using `ENat.coe_toNat (fun h => h0 (addVal_eq_top_iff.1 h))`. Rewrite `h1` using `[IsLocalRing.length_baseChange, h2, length_quot_span_singleton_dvr _ h0]`. Rewrite using `[h3, mul_comm]`.

Conclude with `h1`.
-/
theorem lenBaseChangeDVR : LenBaseChangeDVR := by
  intro A O _ _ _ _ _ _ f hloc hinj ϖ hϖ ι _ N
  letI : Algebra A O := f.toAlgebra
  haveI : IsLocalHom (algebraMap A O) := hloc
  haveI : Module.IsTorsionFree A O := Module.IsTorsionFree.of_smul_eq_zero (fun a c h => by
    rw [Algebra.smul_def, mul_eq_zero] at h
    exact h.imp_left (fun h0 => hinj (h0.trans (map_zero f).symm)))
  haveI : Module.Flat A O := inferInstance
  have h0 : f ϖ ≠ 0 := fun h => hϖ.ne_zero (hinj (h.trans (map_zero f).symm))
  have h1 := length_pi_span_quot A O ι N
  have h2 : (IsLocalRing.maximalIdeal A).map (algebraMap A O) = Ideal.span {f ϖ} := by
    rw [hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
    rfl
  have h3 : ((addVal O (f ϖ)).toNat : ℕ∞) = addVal O (f ϖ) :=
    ENat.coe_toNat (fun h => h0 (addVal_eq_top_iff.1 h))
  rw [IsLocalRing.length_baseChange, h2, length_quot_span_singleton_dvr _ h0] at h1
  rw [h3, mul_comm]
  exact h1

end Formalism.MainNotions.Gaps.RN

end
