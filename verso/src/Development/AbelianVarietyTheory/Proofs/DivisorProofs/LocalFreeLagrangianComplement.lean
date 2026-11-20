import Mathlib

open TensorProduct

namespace GlobalTheory.AdaptedBasis

/- English proof (translation)
Establish `: Module.FinitePresentation R P` using `Module.finitePresentation_of_projective _ _`. Use `haveI : Module.Free (Localization.AtPrime q.asIdeal) (LocalizedModule q.asIdeal.primeCompl P) := Module.mem_freeLocus.1 (by rw [Module.freeLocus_eq_univ]; trivial)`. Establish `hr : Module.finrank (Localization.AtPrime q.asIdeal) (LocalizedModule q.asIdeal.primeCompl P) = g` using `hq`. Take `⟨r, hr', b', -⟩` from `Module.FinitePresentation.exists_basis_localizedModule_powers q.asIdeal.primeCompl (LocalizedModule.mkLinearMap q.asIdeal.primeCompl P) (Localization.AtPrime q.asIdeal) (Module.finBasisOfFinrankEq _ _ hr)`. Use `⟨r, hr', fun R' _ _ hu => ?_⟩` and prove the remaining obligations.

Use `letI : Algebra (Localization.Away r) R' := (IsLocalization.Away.lift r hu).toAlgebra`. Use `haveI : IsScalarTower R (Localization.Away r) R' := IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.Away.lift_eq r hu x).symm`. Set `b₁` to `b'.map (LocalizedModule.equivTensorProduct (Submonoid.powers r) P)`. Conclude with `⟨(b₁.baseChange R').map (AlgebraTensorModule.cancelBaseChange R (Localization.Away r) R' R' P)⟩`.
-/
theorem exists_basis_baseChange_of_isUnit (R : Type) [CommRing R] (P : Type*) [AddCommGroup P]
    [Module R P] [Module.Finite R P] [Module.Projective R P] (g : ℕ) (q : PrimeSpectrum R)
    (hq : Module.rankAtStalk P q = g) :
    ∃ r : R, r ∈ q.asIdeal.primeCompl ∧ ∀ (R' : Type) [CommRing R'] [Algebra R R'],
      IsUnit (algebraMap R R' r) → Nonempty (Module.Basis (Fin g) R' (R' ⊗[R] P)) := by
  have : Module.FinitePresentation R P := Module.finitePresentation_of_projective _ _
  haveI : Module.Free (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl P) :=
    Module.mem_freeLocus.1 (by rw [Module.freeLocus_eq_univ]; trivial)
  have hr : Module.finrank (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl P) = g := hq
  obtain ⟨r, hr', b', -⟩ := Module.FinitePresentation.exists_basis_localizedModule_powers
    q.asIdeal.primeCompl (LocalizedModule.mkLinearMap q.asIdeal.primeCompl P)
    (Localization.AtPrime q.asIdeal) (Module.finBasisOfFinrankEq _ _ hr)
  refine ⟨r, hr', fun R' _ _ hu => ?_⟩
  letI : Algebra (Localization.Away r) R' := (IsLocalization.Away.lift r hu).toAlgebra
  haveI : IsScalarTower R (Localization.Away r) R' :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.Away.lift_eq r hu x).symm
  let b₁ := b'.map (LocalizedModule.equivTensorProduct (Submonoid.powers r) P)
  exact ⟨(b₁.baseChange R').map
    (AlgebraTensorModule.cancelBaseChange R (Localization.Away r) R' R' P)⟩

/- English proof (translation)
Introduce `R _ M _ _ g P ⟨N, hN⟩ hM hMp hMr hP hPp hPr q`. Set `e` to `Submodule.prodEquivOfIsCompl P N hN`. Set `π : M →ₗ[R] N` to `LinearMap.snd R P N ∘ₗ e.symm.toLinearMap`. Establish `hπ : π ∘ₗ N.subtype = LinearMap.id`. Use extensionality with `x`.

Simplify using `[π, e]`. Use `haveI : Module.Projective R N := Module.Projective.of_split N.subtype π hπ`. Use `haveI : Module.Finite R N := Module.Finite.of_surjective π fun x => ⟨x, LinearMap.congr_fun hπ x⟩`. Establish `hNr : Module.rankAtStalk N q = g`. Establish `h1` using `congrFun (Module.rankAtStalk_eq_of_equiv e) q`.

Rewrite `h1` using `[Module.rankAtStalk_prod, Pi.add_apply, hMr, hPr]`. Use linear arithmetic over natural numbers and integers. Take `⟨r₁, hr₁, H₁⟩` from `exists_basis_baseChange_of_isUnit R P g q (hPr q)`. Take `⟨r₂, hr₂, H₂⟩` from `exists_basis_baseChange_of_isUnit R N g q hNr`. Use `⟨r₁ * r₂, mul_mem hr₁ hr₂, fun R' _ _ _ M' _ _ _ _ f hf => ?_⟩` and prove the remaining obligations.

Establish `hu : IsUnit (algebraMap R R' r₁ * algebraMap R R' r₂)`. Rewrite using `[← map_mul]`. Conclude with `IsLocalization.Away.algebraMap_isUnit (r₁ * r₂)`. Take `⟨b₁⟩` from `H₁ R' (isUnit_of_mul_isUnit_left hu)`. Take `⟨b₂⟩` from `H₂ R' (isUnit_of_mul_isUnit_right hu)`.

Establish `hbc : IsBaseChange R' f` using `(isLocalizedModule_iff_isBaseChange (Submonoid.powers (r₁ * r₂)) R' f).1 hf`. Set `E : ((R' ⊗[R] P) × (R' ⊗[R] N)) ≃ₗ[R'] M'` to `(TensorProduct.prodRight R R' R' P N).symm ≪≫ₗ (e.baseChange R R' _ _) ≪≫ₗ hbc.equiv`. Set `ι : R' ⊗[R] P →ₗ[R'] M'` to `E.toLinearMap ∘ₗ LinearMap.inl R' _ _`. Establish `hι (x : P) : ι (1 ⊗ₜ x) = f x`. Establish `: (TensorProduct.prodRight R R' R' P N).symm ((1 : R') ⊗ₜ[R] x, 0) = (1 : R') ⊗ₜ[R] (x, (0 : N))`.

Rewrite using `[LinearEquiv.symm_apply_eq]`. Simplify using the standard rewrite rules. Simplify using `[ι, E, this, e]`. Set `σ : Fin g ⊕ Fin g ≃ Fin (2 * g)` to `finSumFinEquiv.trans (finCongr (two_mul g).symm)`. Use `⟨((b₁.prod b₂).map E).reindex σ, ?_⟩` and prove the remaining obligations.

Establish `h1 : Submodule.span R' (f '' P) = LinearMap.range ι`. Rewrite using `[LinearMap.range_eq_map, ← Submodule.baseChange_top (A := R'), Submodule.baseChange_eq_span, Submodule.map_span]`. Use `congr 1`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨1 ⊗ₜ ⟨x, hx⟩, ⟨⟨x, hx⟩, trivial, rfl⟩, hι _⟩`. Introduce and unpack `⟨_, ⟨x, -, rfl⟩, rfl⟩`. Conclude with `⟨x, x.2, (hι x).symm⟩`. Rewrite using `[h1, LinearMap.range_eq_map, ← b₁.span_eq, Submodule.map_span]`.

Use `congr 1`. Establish `h2 (i : Fin g) : (((b₁.prod b₂).map E).reindex σ) (σ (Sum.inl i)) = ι (b₁ i)`. Simplify using `[ι]`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨_, ⟨i, rfl⟩, rfl⟩`. Conclude with `⟨σ (Sum.inl i), by simp [σ], h2 i⟩`. Introduce and unpack `⟨j, hj, rfl⟩`. Establish `: j = σ (Sum.inl ⟨j, hj⟩)`. Use `ext`.

Simplify using `[σ]`. Conclude with `⟨_, ⟨⟨j, hj⟩, rfl⟩, by rw [← h2, ← this]⟩`.
-/
theorem exists_adapted_basis_away :
    ∀ (R : Type) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M] (g : ℕ) (P : Submodule R M),
    (∃ N : Submodule R M, IsCompl P N) → Module.Finite R M → Module.Projective R M →
    (∀ q : PrimeSpectrum R, Module.rankAtStalk M q = 2 * g) →
    Module.Finite R P → Module.Projective R P → (∀ q : PrimeSpectrum R, Module.rankAtStalk P q = g) →
    ∀ q : PrimeSpectrum R, ∃ r : R, r ∈ q.asIdeal.primeCompl ∧
      ∀ (R' : Type) [CommRing R'] [Algebra R R'] [IsLocalization.Away r R']
        (M' : Type*) [AddCommGroup M'] [Module R' M'] [Module R M'] [IsScalarTower R R' M']
        (f : M →ₗ[R] M'), IsLocalizedModule (Submonoid.powers r) f →
        ∃ c : Module.Basis (Fin (2 * g)) R' M',
          Submodule.span R' (f '' P) = Submodule.span R' (c '' {j | (j : ℕ) < g}) := by
  intro R _ M _ _ g P ⟨N, hN⟩ hM hMp hMr hP hPp hPr q
  let e := Submodule.prodEquivOfIsCompl P N hN
  let π : M →ₗ[R] N := LinearMap.snd R P N ∘ₗ e.symm.toLinearMap
  have hπ : π ∘ₗ N.subtype = LinearMap.id := by
    ext x
    simp [π, e]
  haveI : Module.Projective R N := Module.Projective.of_split N.subtype π hπ
  haveI : Module.Finite R N :=
    Module.Finite.of_surjective π fun x => ⟨x, LinearMap.congr_fun hπ x⟩
  have hNr : Module.rankAtStalk N q = g := by
    have h1 := congrFun (Module.rankAtStalk_eq_of_equiv e) q
    rw [Module.rankAtStalk_prod, Pi.add_apply, hMr, hPr] at h1
    omega
  obtain ⟨r₁, hr₁, H₁⟩ := exists_basis_baseChange_of_isUnit R P g q (hPr q)
  obtain ⟨r₂, hr₂, H₂⟩ := exists_basis_baseChange_of_isUnit R N g q hNr
  refine ⟨r₁ * r₂, mul_mem hr₁ hr₂, fun R' _ _ _ M' _ _ _ _ f hf => ?_⟩
  have hu : IsUnit (algebraMap R R' r₁ * algebraMap R R' r₂) := by
    rw [← map_mul]; exact IsLocalization.Away.algebraMap_isUnit (r₁ * r₂)
  obtain ⟨b₁⟩ := H₁ R' (isUnit_of_mul_isUnit_left hu)
  obtain ⟨b₂⟩ := H₂ R' (isUnit_of_mul_isUnit_right hu)
  have hbc : IsBaseChange R' f :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers (r₁ * r₂)) R' f).1 hf
  let E : ((R' ⊗[R] P) × (R' ⊗[R] N)) ≃ₗ[R'] M' :=
    (TensorProduct.prodRight R R' R' P N).symm ≪≫ₗ
      (e.baseChange R R' _ _) ≪≫ₗ hbc.equiv
  let ι : R' ⊗[R] P →ₗ[R'] M' := E.toLinearMap ∘ₗ LinearMap.inl R' _ _
  have hι (x : P) : ι (1 ⊗ₜ x) = f x := by
    have : (TensorProduct.prodRight R R' R' P N).symm ((1 : R') ⊗ₜ[R] x, 0) =
        (1 : R') ⊗ₜ[R] (x, (0 : N)) := by
      rw [LinearEquiv.symm_apply_eq]
      simp
    simp [ι, E, this, e]
  let σ : Fin g ⊕ Fin g ≃ Fin (2 * g) := finSumFinEquiv.trans (finCongr (two_mul g).symm)
  refine ⟨((b₁.prod b₂).map E).reindex σ, ?_⟩
  have h1 : Submodule.span R' (f '' P) = LinearMap.range ι := by
    rw [LinearMap.range_eq_map, ← Submodule.baseChange_top (A := R'), Submodule.baseChange_eq_span,
      Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨1 ⊗ₜ ⟨x, hx⟩, ⟨⟨x, hx⟩, trivial, rfl⟩, hι _⟩
    · rintro ⟨_, ⟨x, -, rfl⟩, rfl⟩
      exact ⟨x, x.2, (hι x).symm⟩
  rw [h1, LinearMap.range_eq_map, ← b₁.span_eq, Submodule.map_span]
  congr 1
  have h2 (i : Fin g) : (((b₁.prod b₂).map E).reindex σ) (σ (Sum.inl i)) = ι (b₁ i) := by
    simp [ι]
  ext y
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨σ (Sum.inl i), by simp [σ], h2 i⟩
  · rintro ⟨j, hj, rfl⟩
    have : j = σ (Sum.inl ⟨j, hj⟩) := by
      ext
      simp [σ]
    exact ⟨_, ⟨⟨j, hj⟩, rfl⟩, by rw [← h2, ← this]⟩

end GlobalTheory.AdaptedBasis
