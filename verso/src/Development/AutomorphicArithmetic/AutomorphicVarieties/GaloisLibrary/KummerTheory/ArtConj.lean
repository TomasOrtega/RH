import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ClPullApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ArtKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ArtFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ArtIne
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ArtSurj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ClMapBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ClSubUniv

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Simplify using `[hx]`. Establish `h0 : B.valuation x ≠ 0` using `by simpa using hx`. Rewrite using `[← B.valuation_le_one_iff, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.mpr h0)]`. Simplify using `[hx]`.
-/
private theorem valuation_lt_one_iff_eq_zero_or_inv_notMem {L : Type} [Field L] (B : ValuationSubring L) (x : L) :
    B.valuation x < 1 ↔ x = 0 ∨ x⁻¹ ∉ B := by
  by_cases hx : x = 0
  · simp [hx]
  · have h0 : B.valuation x ≠ 0 := by simpa using hx
    rw [← B.valuation_le_one_iff, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.mpr h0)]
    simp [hx]

/- English proof (translation)
Use `open scoped Pointwise in`. Rewrite `hg`, the goal using `[ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff]`. Use `open scoped Pointwise in`. Use extensionality with `x`. Use `open scoped Pointwise in`.

Rewrite using `[ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_comap, ValuationSubring.mem_comap, ← map_inv, AlgEquiv.smul_def, conjGal_apply]`. Simplify using `only [RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]`. Use `open scoped Pointwise in`. Rewrite using `[← AlgEquiv.smul_def, ← ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hg]`.
-/
private theorem conjGal_mem_decompositionSubgroup_comap {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {τ : K ≃+* K}
    {σ : Ω ≃+* Ω} (h : IsLift τ σ) (A : ValuationSubring Ω) (g : G K Ω)
    (hg : g ∈ ValuationSubring.decompositionSubgroup K A) :
    conjGal h g ∈ ValuationSubring.decompositionSubgroup K (A.comap (σ : Ω →+* Ω)) := by
  open scoped Pointwise in
  rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff] at hg ⊢
  open scoped Pointwise in
  ext x
  open scoped Pointwise in
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_comap,
    ValuationSubring.mem_comap, ← map_inv, AlgEquiv.smul_def, conjGal_apply]
  simp only [RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
  open scoped Pointwise in
  rw [← AlgEquiv.smul_def, ← ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hg]

/- English proof (translation)
Rewrite using `[ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff, ValuationSubring.mem_comap]`. Both sides reduce to the same expression.
-/
private theorem valuation_comap_le_one_iff {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (σ : Ω ≃+* Ω) (x : Ω) :
    (A.comap (σ : Ω →+* Ω)).valuation x ≤ 1 ↔ A.valuation (σ x) ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff,
    ValuationSubring.mem_comap]
  rfl

/- English proof (translation)
Rewrite using `[valuation_lt_one_iff_eq_zero_or_inv_notMem, valuation_lt_one_iff_eq_zero_or_inv_notMem, ValuationSubring.mem_comap]`. Simplify using `[map_inv₀]`.
-/
private theorem valuation_comap_lt_one_iff {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (σ : Ω ≃+* Ω) (x : Ω) :
    (A.comap (σ : Ω →+* Ω)).valuation x < 1 ↔ A.valuation (σ x) < 1 := by
  rw [valuation_lt_one_iff_eq_zero_or_inv_notMem, valuation_lt_one_iff_eq_zero_or_inv_notMem, ValuationSubring.mem_comap]
  simp [map_inv₀]

/- English proof (translation)
Use `⟨conjGal_mem_decompositionSubgroup_comap h A g hg.1, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite `hx` using `[valuation_comap_le_one_iff]`. Rewrite using `[valuation_comap_lt_one_iff, map_sub, map_pow, conjGal_apply, RingEquiv.apply_symm_apply]`. Conclude with `hg.2 (σ x) hx`.
-/
private theorem isFrob_comap_conjGal {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {τ : K ≃+* K}
    {σ : Ω ≃+* Ω} (h : IsLift τ σ) (A : ValuationSubring Ω) (q : ℕ) (g : G K Ω)
    (hg : IsFrob A q g) : IsFrob (A.comap (σ : Ω →+* Ω)) q (conjGal h g) := by
  refine ⟨conjGal_mem_decompositionSubgroup_comap h A g hg.1, fun x hx => ?_⟩
  rw [valuation_comap_le_one_iff] at hx
  rw [valuation_comap_lt_one_iff, map_sub, map_pow, conjGal_apply, RingEquiv.apply_symm_apply]
  exact hg.2 (σ x) hx

/- English proof (translation)
Establish `hg' : g ∈ Inertia A` using `hg`. Use `show conjGal h g ∈ Inertia (A.comap (σ : Ω →+* Ω))`. Use `⟨conjGal_mem_decompositionSubgroup_comap h A g hg'.1, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite `hx` using `[valuation_comap_le_one_iff]`. Rewrite using `[valuation_comap_lt_one_iff, map_sub, conjGal_apply, RingEquiv.apply_symm_apply]`.

Conclude with `hg'.2 (σ x) hx`.
-/
private theorem conjGal_mem_ine_comap {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    {τ : K ≃+* K} {σ : Ω ≃+* Ω} (h : IsLift τ σ) (A : ValuationSubring Ω) (g : G K Ω)
    (hg : g ∈ Ine A) : conjGal h g ∈ Ine (A.comap (σ : Ω →+* Ω)) := by
  have hg' : g ∈ Inertia A := hg
  show conjGal h g ∈ Inertia (A.comap (σ : Ω →+* Ω))
  refine ⟨conjGal_mem_decompositionSubgroup_comap h A g hg'.1, fun x hx => ?_⟩
  rw [valuation_comap_le_one_iff] at hx
  rw [valuation_comap_lt_one_iff, map_sub, conjGal_apply, RingEquiv.apply_symm_apply]
  exact hg'.2 (σ x) hx

/- English proof (translation)
Introduce `K Ω _ _ _ _ _ τ σ h g`. Use `set ψ : G K Ω →* ClassGroup (𝓞 K) := (clMap τ).comp ((artCl K Ω).comp (conjGal h)) with hψ`. Establish `hker : (artCl K Ω).ker ≤ ψ.ker`. Use `artKer K Ω _ ψ ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[MonoidHom.coe_ker]`.

Establish `hlc : IsLocallyConstant ψ` using `((artSurj K Ω).2.comp_continuous (continuous_conjGal h)).comp (clMap τ)`. Conclude with `hlc.isOpen_fiber 1`. Introduce `A x hx`. Rewrite using `[MonoidHom.mem_ker]`. Use `show clMap τ (artCl K Ω (conjGal h x)) = 1`.

Rewrite using `[(artIne K Ω).1 (A.comap (σ : Ω →+* Ω)) _ (conjGal_mem_ine_comap h A x hx), map_one]`. Introduce `c hc show clMap τ (artCl K Ω (conjGal h c)) = 1`. Take `⟨j, hj⟩` from `hc`. Establish `hc' : IsConjOm (conjGal h c).toRingEquiv`. Use `⟨j.comp (σ : Ω →+* Ω), fun x => ?_⟩` and prove the remaining obligations.

Simplify using `only [RingHom.comp_apply, RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv, conjGal_apply, RingEquiv.apply_symm_apply]`. Conclude with `hj (σ x)`. Rewrite using `[(artIne K Ω).2 _ hc', map_one]`. Establish `hsame : ∀ g₁ g₂, artCl K Ω g₁ = artCl K Ω g₂ → ψ g₁ = ψ g₂`. Introduce `g₁ g₂ he`.

Establish `hm : g₁ * g₂⁻¹ ∈ (artCl K Ω).ker`. Rewrite using `[MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]`. Establish `hm'` using `hker hm`. Rewrite `hm'` using `[MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]`. Conclude with `hm'`.

Establish `hall : ∀ c : ClassGroup (𝓞 K), ∃ x, artCl K Ω x = c ∧ ψ x = c`. Introduce `c`. Establish `hc : c ∈ Subgroup.closure (primeCl '' (Set.univ : Set (HeightOneSpectrum (𝓞 K))))`. Establish `hu` using `clSubUniv K`. Rewrite `hu` using `[clSub]`.

Rewrite using `[hu]`. Conclude with `Subgroup.mem_top c`. Use `Subgroup.closure_induction (p := fun c _ => ∃ x, artCl K Ω x = c ∧ ψ x = c) ?_ ?_ ?_ ?_ hc` and prove the remaining obligations. Introduce and unpack `_ ⟨v, -, rfl⟩`. Take `⟨A, hA⟩` from `exists_isPlaceOver Ω v`.

Take `⟨f, hf⟩` from `exists_isFrob hA`. Use `⟨f, artFrob K Ω A v f hA hf, ?_⟩` and prove the remaining obligations. Set `τO` to `RingOfIntegers.mapRingEquiv τ`. Set `v' : HeightOneSpectrum (𝓞 K)` to `v.comap (τO : 𝓞 K →+* 𝓞 K) τO.surjective`. Establish `hA' : IsPlaceOver (A.comap (σ : Ω →+* Ω)) v'`.

Introduce `x`. Rewrite using `[valuation_comap_lt_one_iff, h]`. Conclude with `hA (τO x)`. Establish `hn : normV v' = normV v` using `Nat.card_congr (Ideal.quotientEquiv v'.asIdeal v.asIdeal τO (Ideal.map_comap_of_surjective _ τO.surjective _).symm).toEquiv`. Establish `hF' : IsFrob (A.comap (σ : Ω →+* Ω)) (normV v') (conjGal h f)`.

Rewrite using `[hn]`. Conclude with `isFrob_comap_conjGal h A _ f hf`. Use `show clMap τ (artCl K Ω (conjGal h f)) = primeCl v`. Rewrite using `[artFrob K Ω _ v' _ hA' hF', primeCl, primeCl, class_map_mk0]`. Use `congr 1`.

Conclude with `Subtype.ext (Ideal.map_comap_of_surjective _ τO.surjective _)`. Conclude with `⟨1, map_one _, map_one _⟩`. Introduce and unpack `a b - - ⟨ga, ha1, ha2⟩ ⟨gb, hb1, hb2⟩`. Conclude with `⟨ga * gb, by rw [map_mul, ha1, hb1], by rw [map_mul, ha2, hb2]⟩`. Introduce and unpack `a - ⟨ga, h1, h2⟩`.

Conclude with `⟨ga⁻¹, by rw [map_inv, h1], by rw [map_inv, h2]⟩`. Take `⟨g₀, h1, h2⟩` from `hall (artCl K Ω g)`. Use `show artCl K Ω g = ψ g`. Rewrite using `[hsame g g₀ h1.symm, h2]`.
-/
theorem UpperTheory.V.Kum.artConj :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (τ : K ≃+* K) (σ : Ω ≃+* Ω) (h : IsLift τ σ) (g : G K Ω), artCl K Ω g = clMap τ (artCl K Ω (conjGal h g)) := by
  intro K Ω _ _ _ _ _ τ σ h g
  set ψ : G K Ω →* ClassGroup (𝓞 K) := (clMap τ).comp ((artCl K Ω).comp (conjGal h)) with hψ
  have hker : (artCl K Ω).ker ≤ ψ.ker := by
    refine artKer K Ω _ ψ ?_ ?_ ?_
    · rw [MonoidHom.coe_ker]
      have hlc : IsLocallyConstant ψ :=
        ((artSurj K Ω).2.comp_continuous (continuous_conjGal h)).comp (clMap τ)
      exact hlc.isOpen_fiber 1
    · intro A x hx
      rw [MonoidHom.mem_ker]
      show clMap τ (artCl K Ω (conjGal h x)) = 1
      rw [(artIne K Ω).1 (A.comap (σ : Ω →+* Ω)) _ (conjGal_mem_ine_comap h A x hx), map_one]
    · intro c hc
      show clMap τ (artCl K Ω (conjGal h c)) = 1
      obtain ⟨j, hj⟩ := hc
      have hc' : IsConjOm (conjGal h c).toRingEquiv := by
        refine ⟨j.comp (σ : Ω →+* Ω), fun x => ?_⟩
        simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv,
          conjGal_apply, RingEquiv.apply_symm_apply]
        exact hj (σ x)
      rw [(artIne K Ω).2 _ hc', map_one]
  have hsame : ∀ g₁ g₂, artCl K Ω g₁ = artCl K Ω g₂ → ψ g₁ = ψ g₂ := by
    intro g₁ g₂ he
    have hm : g₁ * g₂⁻¹ ∈ (artCl K Ω).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
    have hm' := hker hm
    rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hm'
    exact hm'
  have hall : ∀ c : ClassGroup (𝓞 K), ∃ x, artCl K Ω x = c ∧ ψ x = c := by
    intro c
    have hc : c ∈ Subgroup.closure (primeCl '' (Set.univ : Set (HeightOneSpectrum (𝓞 K)))) := by
      have hu := clSubUniv K
      rw [clSub] at hu
      rw [hu]
      exact Subgroup.mem_top c
    refine Subgroup.closure_induction (p := fun c _ => ∃ x, artCl K Ω x = c ∧ ψ x = c)
      ?_ ?_ ?_ ?_ hc
    · rintro _ ⟨v, -, rfl⟩
      obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
      obtain ⟨f, hf⟩ := exists_isFrob hA
      refine ⟨f, artFrob K Ω A v f hA hf, ?_⟩
      let τO := RingOfIntegers.mapRingEquiv τ
      let v' : HeightOneSpectrum (𝓞 K) := v.comap (τO : 𝓞 K →+* 𝓞 K) τO.surjective
      have hA' : IsPlaceOver (A.comap (σ : Ω →+* Ω)) v' := by
        intro x
        rw [valuation_comap_lt_one_iff, h]
        exact hA (τO x)
      have hn : normV v' = normV v :=
        Nat.card_congr (Ideal.quotientEquiv v'.asIdeal v.asIdeal τO
          (Ideal.map_comap_of_surjective _ τO.surjective _).symm).toEquiv
      have hF' : IsFrob (A.comap (σ : Ω →+* Ω)) (normV v') (conjGal h f) := by
        rw [hn]
        exact isFrob_comap_conjGal h A _ f hf
      show clMap τ (artCl K Ω (conjGal h f)) = primeCl v
      rw [artFrob K Ω _ v' _ hA' hF', primeCl, primeCl, class_map_mk0]
      congr 1
      exact Subtype.ext (Ideal.map_comap_of_surjective _ τO.surjective _)
    · exact ⟨1, map_one _, map_one _⟩
    · rintro a b - - ⟨ga, ha1, ha2⟩ ⟨gb, hb1, hb2⟩
      exact ⟨ga * gb, by rw [map_mul, ha1, hb1], by rw [map_mul, ha2, hb2]⟩
    · rintro a - ⟨ga, h1, h2⟩
      exact ⟨ga⁻¹, by rw [map_inv, h1], by rw [map_inv, h2]⟩
  obtain ⟨g₀, h1, h2⟩ := hall (artCl K Ω g)
  show artCl K Ω g = ψ g
  rw [hsame g g₀ h1.symm, h2]
