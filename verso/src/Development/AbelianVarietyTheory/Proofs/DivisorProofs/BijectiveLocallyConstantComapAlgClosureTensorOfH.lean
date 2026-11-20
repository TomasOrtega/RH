import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEquivalenceFiniteEtaleBaseChangeResidueField
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory

open IsLocalRing

/- English proof (translation)
The claim follows from `h.mem_open (φ.isLocallyConstant.isOpen_fiber (φ y')) rfl`.
-/
theorem locallyConstant_eq_of_specializes {Y Λ : Type*} [TopologicalSpace Y]
    (φ : LocallyConstant Y Λ) {y y' : Y} (h : y ⤳ y') : φ y = φ y' :=
  h.mem_open (φ.isLocallyConstant.isOpen_fiber (φ y')) rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun hy ↦ h.mem_closed hV.1 hy, fun hy ↦ h.mem_open hV.2 hy⟩`.
-/
theorem mem_iff_of_specializes_of_isClopen {Y : Type*} [TopologicalSpace Y] {V : Set Y}
    (hV : IsClopen V) {y y' : Y} (h : y ⤳ y') : y ∈ V ↔ y' ∈ V :=
  ⟨fun hy ↦ h.mem_closed hV.1 hy, fun hy ↦ h.mem_open hV.2 hy⟩

/- English proof (translation)
Use `choose g hg using h1`. Use `⟨fun φ ψ hφψ ↦ ?_, fun ψ ↦ ?_⟩` and prove the remaining obligations. Use extensionality with `y`. Establish `h : (φ.comap f) (g y) = (ψ.comap f) (g y)`. Rewrite using `[show φ.comap f = ψ.comap f from hφψ]`.

Rewrite using `[locallyConstant_eq_of_specializes φ (hg y), locallyConstant_eq_of_specializes ψ (hg y)]`. Simplify using `using h`. Establish `key : ∀ l : Λ, ∃ V : Set Y, IsClopen V ∧ f ⁻¹' V = {x | ψ x = l} ∧ (fun y ↦ ψ (g y)) ⁻¹' {l} = V`. Introduce `l`. Take `⟨V, hV, hVU⟩` from `h2 _ (ψ.isLocallyConstant.isClopen_fiber l)`.

Use `⟨V, hV, hVU, ?_⟩` and prove the remaining obligations. Use extensionality with `y`. Use `show ψ (g y) = l ↔ y ∈ V`. Rewrite using `[mem_iff_of_specializes_of_isClopen hV (hg y)]`. Express the relevant statement in the definitionally equal form `ψ (g y) = l ↔ g y ∈ f ⁻¹' V`.

Rewrite using `[hVU]`. Both sides reduce to the same expression. Use `⟨⟨fun y ↦ ψ (g y), IsLocallyConstant.iff_isOpen_fiber.2 fun l ↦ ?_⟩, ?_⟩` and prove the remaining obligations. Take `⟨V, hV, -, hV'⟩` from `key l`. Rewrite using `[hV']`.

Conclude with `hV.2`. Use extensionality with `x`. Take `⟨V, -, hVU, hV'⟩` from `key (ψ x)`. Establish `hx : x ∈ f ⁻¹' V` using `by rw [hVU]; rfl`. Rewrite `hx` using `[← hV']`.

Conclude with `hx`.
-/
theorem bijective_locallyConstant_comap_of_specializes_of_isClopen {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (Λ : Type*) (f : C(X, Y))
    (h1 : ∀ y : Y, ∃ x : X, y ⤳ f x)
    (h2 : ∀ U : Set X, IsClopen U → ∃ V : Set Y, IsClopen V ∧ f ⁻¹' V = U) :
    Function.Bijective (fun φ : LocallyConstant Y Λ ↦ φ.comap f) := by
  choose g hg using h1
  refine ⟨fun φ ψ hφψ ↦ ?_, fun ψ ↦ ?_⟩
  · ext y
    have h : (φ.comap f) (g y) = (ψ.comap f) (g y) := by
      rw [show φ.comap f = ψ.comap f from hφψ]
    rw [locallyConstant_eq_of_specializes φ (hg y), locallyConstant_eq_of_specializes ψ (hg y)]
    simpa using h
  · have key : ∀ l : Λ, ∃ V : Set Y, IsClopen V ∧ f ⁻¹' V = {x | ψ x = l} ∧
        (fun y ↦ ψ (g y)) ⁻¹' {l} = V := by
      intro l
      obtain ⟨V, hV, hVU⟩ := h2 _ (ψ.isLocallyConstant.isClopen_fiber l)
      refine ⟨V, hV, hVU, ?_⟩
      ext y
      show ψ (g y) = l ↔ y ∈ V
      rw [mem_iff_of_specializes_of_isClopen hV (hg y)]
      change ψ (g y) = l ↔ g y ∈ f ⁻¹' V
      rw [hVU]
      rfl
    refine ⟨⟨fun y ↦ ψ (g y), IsLocallyConstant.iff_isOpen_fiber.2 fun l ↦ ?_⟩, ?_⟩
    · obtain ⟨V, hV, -, hV'⟩ := key l
      rw [hV']
      exact hV.2
    · ext x
      obtain ⟨V, -, hVU, hV'⟩ := key (ψ x)
      have hx : x ∈ f ⁻¹' V := by rw [hVU]; rfl
      rw [← hV'] at hx
      exact hx

/- English proof (translation)
Rewrite using `[Ideal.map_le_iff_le_comap]`. Establish `: (M.comap (algebraMap A B)).IsMaximal` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M`. Conclude with `(IsLocalRing.eq_maximalIdeal this).ge`.
-/
theorem map_maximalIdeal_le_of_isIntegral (A B : Type*) [CommRing A] [IsLocalRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] (M : Ideal B) [M.IsMaximal] :
    (maximalIdeal A).map (algebraMap A B) ≤ M := by
  rw [Ideal.map_le_iff_le_comap]
  have : (M.comap (algebraMap A B)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
  exact (IsLocalRing.eq_maximalIdeal this).ge

/- English proof (translation)
Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective c`. Establish `hb : b * b - b ∈ (maximalIdeal A).map (algebraMap A B)`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hc.eq, sub_self]`. Establish `hb' : b * b - b ∈ Submodule.span B (algebraMap A B '' (maximalIdeal A : Set A))` using `hb`. Take `⟨n, r, s, hs⟩` from `Submodule.mem_span_set'.1 hb'`.

Use `choose a ha hsa using fun i ↦ (s i).2`. Use `set B₀ := Algebra.adjoin A (insert b (Set.range r)) with hB₀`. Use `haveI : Module.Finite A B₀ := Algebra.finite_adjoin_of_finite_of_isIntegral ((Set.finite_range r).insert b) fun x _ ↦ Algebra.IsIntegral.isIntegral x`. Set `b₀ : B₀` to `⟨b, Algebra.subset_adjoin (Set.mem_insert _ _)⟩`. Set `r₀ : Fin n → B₀` to `fun i ↦ ⟨r i, Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨i, rfl⟩)⟩`.

Establish `hsum : b₀ * b₀ - b₀ = ∑ i, r₀ i * algebraMap A B₀ (a i)`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show b * b - b = B₀.val (∑ i, r₀ i * algebraMap A B₀ (a i))`. Rewrite using `[map_sum, ← hs]`. Use `Finset.sum_congr rfl fun i _ ↦ ?_` and prove the remaining obligations.

Rewrite using `[map_mul, AlgHom.commutes, hsa i, smul_eq_mul]`. Both sides reduce to the same expression. Establish `hb₀ : b₀ * b₀ - b₀ ∈ (maximalIdeal A).map (algebraMap A B₀)`. Rewrite using `[hsum]`. Conclude with `Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (ha i))`.

Take `⟨e₀, ⟨he₀, he₀b⟩, -⟩` from `existsUnique_idempotent_lift_quotient A (S := B₀) (c := Ideal.Quotient.mk _ b₀) (by show Ideal.Quotient.mk _ b₀ * Ideal.Quotient.mk _ b₀ = Ideal.Quotient.mk _ b₀`. Rewrite using `[← map_mul, Ideal.Quotient.eq]`. Conclude with `hb₀)`. Use `⟨(e₀ : B), he₀.map B₀.val, ?_⟩` and prove the remaining obligations. Establish `h` using `Ideal.mem_map_of_mem (B₀.val : B₀ →+* B) (Ideal.Quotient.eq.1 he₀b)`.

Rewrite `h` using `[Ideal.map_map, AlgHom.comp_algebraMap]`. Rewrite using `[Ideal.Quotient.eq]`. Simplify using `using h`.
-/
theorem exists_isIdempotentElem_lift_quotient_of_isIntegral (A B : Type) [CommRing A]
    [HenselianLocalRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B]
    {c : B ⧸ (maximalIdeal A).map (algebraMap A B)} (hc : IsIdempotentElem c) :
    ∃ e : B, IsIdempotentElem e ∧ Ideal.Quotient.mk _ e = c := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
  have hb : b * b - b ∈ (maximalIdeal A).map (algebraMap A B) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hc.eq, sub_self]
  have hb' : b * b - b ∈ Submodule.span B (algebraMap A B '' (maximalIdeal A : Set A)) := hb
  obtain ⟨n, r, s, hs⟩ := Submodule.mem_span_set'.1 hb'
  choose a ha hsa using fun i ↦ (s i).2
  set B₀ := Algebra.adjoin A (insert b (Set.range r)) with hB₀
  haveI : Module.Finite A B₀ := Algebra.finite_adjoin_of_finite_of_isIntegral
    ((Set.finite_range r).insert b) fun x _ ↦ Algebra.IsIntegral.isIntegral x
  let b₀ : B₀ := ⟨b, Algebra.subset_adjoin (Set.mem_insert _ _)⟩
  let r₀ : Fin n → B₀ := fun i ↦ ⟨r i, Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨i, rfl⟩)⟩
  have hsum : b₀ * b₀ - b₀ = ∑ i, r₀ i * algebraMap A B₀ (a i) := by
    apply Subtype.ext
    show b * b - b = B₀.val (∑ i, r₀ i * algebraMap A B₀ (a i))
    rw [map_sum, ← hs]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, AlgHom.commutes, hsa i, smul_eq_mul]
    rfl
  have hb₀ : b₀ * b₀ - b₀ ∈ (maximalIdeal A).map (algebraMap A B₀) := by
    rw [hsum]
    exact Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (ha i))
  obtain ⟨e₀, ⟨he₀, he₀b⟩, -⟩ := existsUnique_idempotent_lift_quotient A (S := B₀)
    (c := Ideal.Quotient.mk _ b₀) (by
      show Ideal.Quotient.mk _ b₀ * Ideal.Quotient.mk _ b₀ = Ideal.Quotient.mk _ b₀
      rw [← map_mul, Ideal.Quotient.eq]
      exact hb₀)
  refine ⟨(e₀ : B), he₀.map B₀.val, ?_⟩
  have h := Ideal.mem_map_of_mem (B₀.val : B₀ →+* B) (Ideal.Quotient.eq.1 he₀b)
  rw [Ideal.map_map, AlgHom.comp_algebraMap] at h
  rw [Ideal.Quotient.eq]
  simpa using h

/- English proof (translation)
Introduce `Λ A _ _ _ _ B _ _ _`. Set `k` to `ResidueField A`. Set `Ω` to `AlgebraicClosure k`. Set `I : Ideal B` to `(maximalIdeal A).map (algebraMap A B)`. Set `ιk : B →ₐ[A] k ⊗[A] B` to `Algebra.TensorProduct.includeRight`.

Set `μ : k ⊗[A] B →+* Ω ⊗[A] B` to `(Algebra.TensorProduct.map (Algebra.ofId k Ω) (AlgHom.id A B)).toRingHom`. Establish `hμ : IsHomeomorph (PrimeSpectrum.comap μ)` using `PrimeSpectrum.isHomeomorph_comap_tensorProductMap_of_isPurelyInseparable (R := A) (K := k) (S := B) Ω`. Establish `hIk : ∀ x ∈ I, ιk x = 0`. Introduce `x hx`. Establish `hle : I ≤ RingHom.ker ιk`.

Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `a ha`. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker]`. Use `show ιk (algebraMap A B a) = 0`. Rewrite using `[AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply, show algebraMap A k a = 0 from (IsLocalRing.residue_eq_zero_iff a).2 ha, zero_tmul]`.

Conclude with `hle hx`. Set `e' : B ⧸ I →+* k ⊗[A] B` to `Ideal.Quotient.lift I ιk.toRingHom hIk`. Establish `he'mk : ∀ b : B, e' (Ideal.Quotient.mk I b) = ιk b` using `fun b ↦ rfl`. Set `σ : k →ₐ[A] B ⧸ I` to `Ideal.Quotient.liftₐ (maximalIdeal A) (Algebra.ofId A (B ⧸ I)) fun a ha ↦ by`. Rewrite using `[Algebra.ofId_apply]`.

Use `show Ideal.Quotient.mk I (algebraMap A B a) = 0`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha)`. Set `τ : k ⊗[A] B →ₐ[A] B ⧸ I` to `Algebra.TensorProduct.lift σ (Ideal.Quotient.mkₐ A I) fun _ _ ↦ Commute.all _ _`. Establish `hτ : ∀ q, τ (e' q) = q`. Introduce `q`.

Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective q`. Rewrite using `[he'mk]`. Use `show τ ((1 : k) ⊗ₜ[A] b) = _`. Simplify using `[τ]`. Establish `he' : Function.Bijective e'`.

Use `⟨Function.LeftInverse.injective hτ, fun y ↦ ?_⟩` and prove the remaining obligations. Take `⟨b, rfl⟩` from `includeRight_residueField_surjective A B y`. Conclude with `⟨Ideal.Quotient.mk I b, rfl⟩`. Set `ρ : B ⧸ I →+* Ω ⊗[A] B` to `μ.comp e'`. Establish `hρ : IsHomeomorph (PrimeSpectrum.comap ρ)`.

Rewrite using `[PrimeSpectrum.comap_comp]`. Conclude with `(PrimeSpectrum.isHomeomorph_comap_of_bijective he').comp hμ`. Establish `hfac : ∀ x : PrimeSpectrum (Ω ⊗[A] B), PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] Ω ⊗[A] B).toRingHom x = PrimeSpectrum.comap (Ideal.Quotient.mk I) (PrimeSpectrum.comap ρ x)`. Introduce `x`. Establish `: (Algebra.TensorProduct.includeRight : B →ₐ[A] Ω ⊗[A] B).toRingHom = ρ.comp (Ideal.Quotient.mk I)`.

Use extensionality with `b`. Use `show (1 : Ω) ⊗ₜ[A] b = μ ((1 : k) ⊗ₜ[A] b)`. Simplify using `[μ]`. Rewrite using `[this]`. Both sides reduce to the same expression.

Apply `bijective_locallyConstant_comap_of_specializes_of_isClopen` to reduce the goal to its premises. Introduce `y`. Take `⟨M, hM, hyM⟩` from `Ideal.exists_le_maximal y.asIdeal y.isPrime.ne_top`. Establish `hIM : I ≤ M` using `map_maximalIdeal_le_of_isIntegral A B M`. Use `haveI := hM.isPrime`.

Set `P : PrimeSpectrum (B ⧸ I)` to `⟨M.map (Ideal.Quotient.mk I), Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])⟩`. Establish `hPM : (PrimeSpectrum.comap (Ideal.Quotient.mk I) P).asIdeal = M` using `by show (M.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = M`. Rewrite using `[Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.2 hIM]`. Take `⟨x, hx⟩` from `hρ.surjective P`. Use `⟨x, ?_⟩` and prove the remaining obligations.

Rewrite using `[← PrimeSpectrum.le_iff_specializes, ← PrimeSpectrum.asIdeal_le_asIdeal]`. Use `show y.asIdeal ≤ (PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] Ω ⊗[A] B).toRingHom x).asIdeal`. Rewrite using `[hfac, hx, hPM]`. Conclude with `hyM`. Introduce `U hU`.

Establish `hU' : IsClopen (PrimeSpectrum.comap ρ '' U)` using `⟨hρ.isClosedMap U hU.1, hρ.isOpenMap U hU.2⟩`. Use `set c := PrimeSpectrum.isIdempotentElemEquivClopens.symm ⟨_, hU'⟩ with hc`. Take `⟨e, he, hec⟩` from `exists_isIdempotentElem_lift_quotient_of_isIntegral A B c.2`. Establish `hU'c : (PrimeSpectrum.basicOpen (Ideal.Quotient.mk I e) : Set (PrimeSpectrum (B ⧸ I))) = PrimeSpectrum.comap ρ '' U`. Rewrite using `[hec]`.

Conclude with `congrArg SetLike.coe (PrimeSpectrum.basicOpen_isIdempotentElemEquivClopens_symm _)`. Use `⟨PrimeSpectrum.basicOpen e, ?_, ?_⟩` and prove the remaining obligations. Use `(PrimeSpectrum.isIdempotentElemEquivClopens ⟨e, he⟩).isClopen` as an intermediate fact. Rewrite `this` using `[PrimeSpectrum.coe_isIdempotentElemEquivClopens_apply]`. Then use the resulting hypothesis. Use extensionality with `x`.

Express the relevant statement in the definitionally equal form `PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] Ω ⊗[A] B).toRingHom x ∈ PrimeSpectrum.basicOpen e ↔ x ∈ U`. Rewrite using `[hfac, PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, ← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, hU'c, hρ.injective.mem_set_image]`.
-/
theorem bijective_locallyConstant_comap_algebraicClosure_tensor : ∀ (Λ : Type) (A : Type) [CommRing A] [IsLocalRing A] [HenselianLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)] (B : Type) [CommRing B] [Algebra A B] [Algebra.IsIntegral A B], Function.Bijective (fun φ : LocallyConstant (PrimeSpectrum B) Λ => φ.comap ⟨PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] AlgebraicClosure (IsLocalRing.ResidueField A) ⊗[A] B).toRingHom, PrimeSpectrum.continuous_comap _⟩) := by
  intro Λ A _ _ _ _ B _ _ _
  let k := ResidueField A
  let Ω := AlgebraicClosure k
  let I : Ideal B := (maximalIdeal A).map (algebraMap A B)
  let ιk : B →ₐ[A] k ⊗[A] B := Algebra.TensorProduct.includeRight
  let μ : k ⊗[A] B →+* Ω ⊗[A] B :=
    (Algebra.TensorProduct.map (Algebra.ofId k Ω) (AlgHom.id A B)).toRingHom
  have hμ : IsHomeomorph (PrimeSpectrum.comap μ) :=
    PrimeSpectrum.isHomeomorph_comap_tensorProductMap_of_isPurelyInseparable (R := A) (K := k)
      (S := B) Ω
  have hIk : ∀ x ∈ I, ιk x = 0 := by
    intro x hx
    have hle : I ≤ RingHom.ker ιk := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, RingHom.mem_ker]
      show ιk (algebraMap A B a) = 0
      rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply,
        show algebraMap A k a = 0 from (IsLocalRing.residue_eq_zero_iff a).2 ha, zero_tmul]
    exact hle hx
  let e' : B ⧸ I →+* k ⊗[A] B := Ideal.Quotient.lift I ιk.toRingHom hIk
  have he'mk : ∀ b : B, e' (Ideal.Quotient.mk I b) = ιk b := fun b ↦ rfl
  let σ : k →ₐ[A] B ⧸ I := Ideal.Quotient.liftₐ (maximalIdeal A) (Algebra.ofId A (B ⧸ I))
    fun a ha ↦ by
      rw [Algebra.ofId_apply]
      show Ideal.Quotient.mk I (algebraMap A B a) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha)
  let τ : k ⊗[A] B →ₐ[A] B ⧸ I :=
    Algebra.TensorProduct.lift σ (Ideal.Quotient.mkₐ A I) fun _ _ ↦ Commute.all _ _
  have hτ : ∀ q, τ (e' q) = q := by
    intro q
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [he'mk]
    show τ ((1 : k) ⊗ₜ[A] b) = _
    simp [τ]
  have he' : Function.Bijective e' := by
    refine ⟨Function.LeftInverse.injective hτ, fun y ↦ ?_⟩
    obtain ⟨b, rfl⟩ := includeRight_residueField_surjective A B y
    exact ⟨Ideal.Quotient.mk I b, rfl⟩
  let ρ : B ⧸ I →+* Ω ⊗[A] B := μ.comp e'
  have hρ : IsHomeomorph (PrimeSpectrum.comap ρ) := by
    rw [PrimeSpectrum.comap_comp]
    exact (PrimeSpectrum.isHomeomorph_comap_of_bijective he').comp hμ
  have hfac : ∀ x : PrimeSpectrum (Ω ⊗[A] B),
      PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] Ω ⊗[A] B).toRingHom x =
        PrimeSpectrum.comap (Ideal.Quotient.mk I) (PrimeSpectrum.comap ρ x) := by
    intro x
    have : (Algebra.TensorProduct.includeRight : B →ₐ[A] Ω ⊗[A] B).toRingHom =
        ρ.comp (Ideal.Quotient.mk I) := by
      ext b
      show (1 : Ω) ⊗ₜ[A] b = μ ((1 : k) ⊗ₜ[A] b)
      simp [μ]
    rw [this]
    rfl
  apply bijective_locallyConstant_comap_of_specializes_of_isClopen
  · intro y
    obtain ⟨M, hM, hyM⟩ := Ideal.exists_le_maximal y.asIdeal y.isPrime.ne_top
    have hIM : I ≤ M := map_maximalIdeal_le_of_isIntegral A B M
    haveI := hM.isPrime
    let P : PrimeSpectrum (B ⧸ I) := ⟨M.map (Ideal.Quotient.mk I),
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])⟩
    have hPM : (PrimeSpectrum.comap (Ideal.Quotient.mk I) P).asIdeal = M := by
      show (M.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = M
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
        Ideal.mk_ker, sup_eq_left.2 hIM]
    obtain ⟨x, hx⟩ := hρ.surjective P
    refine ⟨x, ?_⟩
    rw [← PrimeSpectrum.le_iff_specializes, ← PrimeSpectrum.asIdeal_le_asIdeal]
    show y.asIdeal ≤ (PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight : B →ₐ[A] Ω ⊗[A] B).toRingHom x).asIdeal
    rw [hfac, hx, hPM]
    exact hyM
  · intro U hU
    have hU' : IsClopen (PrimeSpectrum.comap ρ '' U) :=
      ⟨hρ.isClosedMap U hU.1, hρ.isOpenMap U hU.2⟩
    set c := PrimeSpectrum.isIdempotentElemEquivClopens.symm ⟨_, hU'⟩ with hc
    obtain ⟨e, he, hec⟩ := exists_isIdempotentElem_lift_quotient_of_isIntegral A B c.2
    have hU'c : (PrimeSpectrum.basicOpen (Ideal.Quotient.mk I e) : Set (PrimeSpectrum (B ⧸ I))) =
        PrimeSpectrum.comap ρ '' U := by
      rw [hec]
      exact congrArg SetLike.coe (PrimeSpectrum.basicOpen_isIdempotentElemEquivClopens_symm _)
    refine ⟨PrimeSpectrum.basicOpen e, ?_, ?_⟩
    · have := (PrimeSpectrum.isIdempotentElemEquivClopens ⟨e, he⟩).isClopen
      rwa [PrimeSpectrum.coe_isIdempotentElemEquivClopens_apply] at this
    · ext x
      change PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] Ω ⊗[A] B).toRingHom x ∈
        PrimeSpectrum.basicOpen e ↔ x ∈ U
      rw [hfac, PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
        ← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, hU'c, hρ.injective.mem_set_image]

end GlobalTheory
