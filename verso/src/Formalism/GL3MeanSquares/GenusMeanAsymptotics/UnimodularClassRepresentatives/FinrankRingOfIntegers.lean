import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsUnimodularAtIffVd
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemSmulOfMemSmulLocF

open NumberField Module IsDedekindDomain Function

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BrA

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

def maxEquiv (F : Type) [Field F] [NumberField F] :
    {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} ≃ HeightOneSpectrum (𝓞 F) where
  toFun 𝔭 := ⟨𝔭.1, 𝔭.2.isPrime, idealPowerSpanBounds.ne_bot 𝔭.2⟩
  invFun v := ⟨v.asIdeal, v.isMaximal⟩
  left_inv _ := rfl
  right_inv _ := rfl

/- English proof (translation)
Establish `hfin : FiniteMultiplicity v.asIdeal I` using `FiniteMultiplicity.of_not_isUnit v.prime.not_isUnit hI`. Establish `: {e : ℕ | I ≤ v.asIdeal ^ e} = Set.Iic (multiplicity v.asIdeal I)`. Use extensionality with `e`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_Iic]`. Rewrite using `[← Ideal.dvd_iff_le, hfin.pow_dvd_iff_le_multiplicity]`.

Rewrite using `[this, csSup_Iic]`.
-/
theorem sSup_le_pow (v : HeightOneSpectrum (𝓞 F)) {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    sSup {e : ℕ | I ≤ v.asIdeal ^ e} = multiplicity v.asIdeal I := by
  have hfin : FiniteMultiplicity v.asIdeal I :=
    FiniteMultiplicity.of_not_isUnit v.prime.not_isUnit hI
  have : {e : ℕ | I ≤ v.asIdeal ^ e} = Set.Iic (multiplicity v.asIdeal I) := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.mem_Iic]
    rw [← Ideal.dvd_iff_le, hfin.pow_dvd_iff_le_multiplicity]
  rw [this, csSup_Iic]

/- English proof (translation)
Set `φ : Ideal (𝓞 F) →* ℝ` to `((Nat.castRingHom ℝ : ℕ →+* ℝ) : ℕ →* ℝ).comp (Ideal.absNorm : Ideal (𝓞 F) →*₀ ℕ).toMonoidHom`. Establish `hφ : ∀ J, φ J = (Ideal.absNorm J : ℝ)` using `fun _ => rfl`. Establish `h0 : HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => v.maxPowDividing I` using `Ideal.hasFiniteMulSupport hI`. Establish `h1 : φ I = ∏ᶠ v : HeightOneSpectrum (𝓞 F), φ (v.maxPowDividing I)` using `by conv_lhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hI]`. Conclude with `map_finprod φ h0`.

Establish `h2 : HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => φ (v.maxPowDividing I)` using `h0.fun_comp (map_one φ)`. Establish `h3 : ∏' v : HeightOneSpectrum (𝓞 F), φ (v.maxPowDividing I) = ∏ᶠ v : HeightOneSpectrum (𝓞 F), φ (v.maxPowDividing I)` using `tprod_eq_finprod h2`. Rewrite using `[← hφ, h1, ← h3, ← (maxEquiv F).tprod_eq]`. Use `tprod_congr fun 𝔭 => ?_` and prove the remaining obligations. Rewrite using `[HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity hI, map_pow, hφ, ← sSup_le_pow _ hI]`.

Both sides reduce to the same expression.
-/
theorem absNorm_eq_tprod {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    (Ideal.absNorm I : ℝ) = ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal},
      (Ideal.absNorm 𝔭.1 : ℝ) ^ sSup {e : ℕ | I ≤ 𝔭.1 ^ e} := by
  let φ : Ideal (𝓞 F) →* ℝ :=
    ((Nat.castRingHom ℝ : ℕ →+* ℝ) : ℕ →* ℝ).comp (Ideal.absNorm : Ideal (𝓞 F) →*₀ ℕ).toMonoidHom
  have hφ : ∀ J, φ J = (Ideal.absNorm J : ℝ) := fun _ => rfl
  have h0 : HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => v.maxPowDividing I :=
    Ideal.hasFiniteMulSupport hI
  have h1 : φ I = ∏ᶠ v : HeightOneSpectrum (𝓞 F), φ (v.maxPowDividing I) := by
    conv_lhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hI]
    exact map_finprod φ h0
  have h2 : HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => φ (v.maxPowDividing I) :=
    h0.fun_comp (map_one φ)
  have h3 : ∏' v : HeightOneSpectrum (𝓞 F), φ (v.maxPowDividing I) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), φ (v.maxPowDividing I) := tprod_eq_finprod h2
  rw [← hφ, h1, ← h3, ← (maxEquiv F).tprod_eq]
  refine tprod_congr fun 𝔭 => ?_
  rw [HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity hI, map_pow, hφ,
    ← sSup_le_pow _ hI]
  rfl

/- English proof (translation)
Rewrite using `[← MeanB.finrank_eq_two hK hF]`. Conclude with `(IsFractionRing.finrank_eq (𝓞 F) F (𝓞 K) K).symm`.
-/
theorem finrank_ringOfIntegers (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) :
    finrank (𝓞 F) (𝓞 K) = 2 := by
  rw [← MeanB.finrank_eq_two hK hF]
  exact (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 K) K).symm

/- English proof (translation)
Rewrite using `[Ideal.absNorm_algebraMap, finrank_ringOfIntegers hK hF]`.
-/
theorem absNorm_map (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (I : Ideal (𝓞 F)) :
    Ideal.absNorm (I.map (algebraMap (𝓞 F) (𝓞 K))) = Ideal.absNorm I ^ 2 := by
  rw [Ideal.absNorm_algebraMap, finrank_ringOfIntegers hK hF]

/- English proof (translation)
Rewrite using `[Ideal.map_le_iff_le_comap, MeanB.comap_extP_pow]`.
-/
theorem map_le_extP_pow (I 𝔭 : Ideal (𝓞 F)) (e : ℕ) :
    I.map (algebraMap (𝓞 F) (𝓞 K)) ≤ extP K 𝔭 ^ e ↔ I ≤ 𝔭 ^ e := by
  rw [Ideal.map_le_iff_le_comap, MeanB.comap_extP_pow]

variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def discrF (F : Type) [Field F] [NumberField F] [Algebra F K] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (L : Submodule (𝓞 K) V) : Ideal (𝓞 F) :=
  (discrIdeal h L).comap (algebraMap (𝓞 F) (𝓞 K))

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `conv_lhs => unfold discrIdeal`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `z ⟨x, hx, hz⟩`. Establish `hzfix : conjO K z = z`.

Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[conjO_coe]`. Express the relevant statement in the definitionally equal form `star (algebraMap (𝓞 K) K z) = algebraMap (𝓞 K) K z`. Rewrite using `[hz, LocF.star_gram_det h hs]`. Take `⟨t, ht⟩` from `(conjO_eq_iff_mem_range hF z).mp hzfix`.

Rewrite using `[← ht]`. Apply `Ideal.mem_map_of_mem` to reduce the goal to its premises. Rewrite using `[discrF, Ideal.mem_comap, ht]`. Conclude with `Ideal.subset_span ⟨x, hx, hz⟩`. Conclude with `Ideal.map_comap_le`.
-/
theorem discrIdeal_eq_map (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (L : Submodule (𝓞 K) V) :
    discrIdeal h L = (discrF F h L).map (algebraMap (𝓞 F) (𝓞 K)) := by
  apply le_antisymm
  · conv_lhs => unfold discrIdeal
    rw [Ideal.span_le]
    rintro z ⟨x, hx, hz⟩
    have hzfix : conjO K z = z := by
      apply RingOfIntegers.ext
      rw [conjO_coe]
      change star (algebraMap (𝓞 K) K z) = algebraMap (𝓞 K) K z
      rw [hz, LocF.star_gram_det h hs]
    obtain ⟨t, ht⟩ := (conjO_eq_iff_mem_range hF z).mp hzfix
    rw [← ht]
    apply Ideal.mem_map_of_mem
    rw [discrF, Ideal.mem_comap, ht]
    exact Ideal.subset_span ⟨x, hx, hz⟩
  · exact Ideal.map_comap_le

/- English proof (translation)
Unfold `vd`. Use `congr 1`. Use extensionality with `e`. Simplify using `only [Set.mem_ofPred_eq]`. Rewrite using `[discrIdeal_eq_map hF hs, map_le_extP_pow]`.
-/
theorem vd_eq (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) :
    vd h L 𝔭 = sSup {e : ℕ | discrF F h L ≤ 𝔭 ^ e} := by
  unfold vd
  congr 1
  ext e
  simp only [Set.mem_ofPred_eq]
  rw [discrIdeal_eq_map hF hs, map_le_extP_pow]

/- English proof (translation)
Unfold `normD`. Rewrite using `[discrIdeal_eq_map hF hs, absNorm_map hK hF, Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg _)]`.
-/
theorem normD_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) (L : Submodule (𝓞 K) V) : normD h L = (Ideal.absNorm (discrF F h L) : ℝ) := by
  unfold normD
  rw [discrIdeal_eq_map hF hs, absNorm_map hK hF, Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg _)]

/- English proof (translation)
Unfold `discrIdeal`. Use `congr 1`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, e⟩`.

Use `⟨fun i => g.symm (x i), fun i => ?_, ?_⟩` and prove the remaining obligations. Take `⟨y, hy, hyx⟩` from `Submodule.mem_map.mp (hx i)`. Establish `: g y = x i` using `hyx`. Express the relevant statement in the definitionally equal form `g.symm (x i) ∈ A`. Rewrite using `[← this, LinearEquiv.symm_apply_apply]`.

Conclude with `hy`. Rewrite using `[e]`. Use `congr 1`. Use extensionality with `i j`. Use `hg (g.symm (x i)) (g.symm (x j))` as an intermediate fact.

Rewrite `this` using `[LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]`. Conclude with `this`. Introduce and unpack `⟨x, hx, e⟩`. Use `⟨fun i => g (x i), fun i => Submodule.mem_map.mpr ⟨x i, hx i, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[e]`.

Use `congr 1`. Use extensionality with `i j`. Conclude with `(hg (x i) (x j)).symm`.
-/
theorem discrIdeal_gmap {h : V →ₗ⋆[K] V →ₗ[K] K} {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    (A : Submodule (𝓞 K) V) : discrIdeal h (Formalism.HermitianLatticesTheory.gmap g A) = discrIdeal h A := by
  unfold discrIdeal
  congr 1
  ext z
  constructor
  · rintro ⟨x, hx, e⟩
    refine ⟨fun i => g.symm (x i), fun i => ?_, ?_⟩
    · obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp (hx i)
      have : g y = x i := hyx
      change g.symm (x i) ∈ A
      rw [← this, LinearEquiv.symm_apply_apply]
      exact hy
    · rw [e]
      congr 1
      ext i j
      have := hg (g.symm (x i)) (g.symm (x j))
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at this
      exact this
  · rintro ⟨x, hx, e⟩
    refine ⟨fun i => g (x i), fun i => Submodule.mem_map.mpr ⟨x i, hx i, rfl⟩, ?_⟩
    rw [e]
    congr 1
    ext i j
    exact (hg (x i) (x j)).symm

/- English proof (translation)
Take `⟨x', hx', ex⟩` from `Submodule.mem_map.mp hx`. Take `⟨y', hy', ey⟩` from `Submodule.mem_map.mp hy`. Establish `ex' : g x' = x` using `ex`. Establish `ey' : g y' = y` using `ey`. Take `⟨s, hs, hsx⟩` from `(LocF.mem_locF_iff hp L x').mp hx'`.

Take `⟨t, ht, hty⟩` from `(LocF.mem_locF_iff hp L y').mp hy'`. Rewrite using `[← ex', ← ey', hg x' y', LocF.mem_locF_iff hp]`. Use `⟨s * t, fun hm => (hp.mem_or_mem hm).elim hs ht, ?_⟩` and prove the remaining obligations. Use `hLi _ hsx _ hty` as an intermediate fact. Rewrite `this` using `[localizedQuotients.form_smul hF]`.

Rewrite using `[Algebra.smul_def]` and apply the resulting hypothesis.
-/
theorem form_mem_locF (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) {g : V ≃ₗ[K] V}
    (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) {x y : V} (hx : x ∈ Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L))
    (hy : y ∈ Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)) : h x y ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
  obtain ⟨x', hx', ex⟩ := Submodule.mem_map.mp hx
  obtain ⟨y', hy', ey⟩ := Submodule.mem_map.mp hy
  have ex' : g x' = x := ex
  have ey' : g y' = y := ey
  obtain ⟨s, hs, hsx⟩ := (LocF.mem_locF_iff hp L x').mp hx'
  obtain ⟨t, ht, hty⟩ := (LocF.mem_locF_iff hp L y').mp hy'
  rw [← ex', ← ey', hg x' y', LocF.mem_locF_iff hp]
  refine ⟨s * t, fun hm => (hp.mem_or_mem hm).elim hs ht, ?_⟩
  have := hLi _ hsx _ hty
  rw [localizedQuotients.form_smul hF] at this
  rwa [Algebra.smul_def]

end Formalism.HermitianLattices.Ext.L3.BrA
