import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionaryStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogLieNormSqEqMeanLogEta
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsNumberFieldDefiningCmCurveHoms
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmCurvesOfWeierstrassCurves
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsEllipticCurvePolarisedLatticeFamilyStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVarietyStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditionalStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SemiAbelianHomExtensionDvrStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QCoreGlobPf

namespace GlobalTheory.PeriodMean

section Curves

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CommonField
open scoped UpperHalfPlane nonZeroDivisors

/- English proof (translation)
Establish `hU` using `GlobalTheory.T.thetaUniformisation_complexAbelianVariety`. Establish `hB` using `GlobalTheory.T.abelianScheme_laws_unconditional.1.polBaseChange`. Take `⟨_, b, hb, h⟩` from `h`. Take `rfl : b = a` from `Subtype.ext hb`. Use `⟨?_, fun s => (EllipticHom.multiplier_iff_exists_hom hU hB _ P Q v t _ _ _ _ hP.1 hQ.1 hP.isTangent hQ.isTangent (hP.2.2.2 _) (hQ.2.2.2 _)).2 (h.up hB s)⟩` and prove the remaining obligations.

Set `i : k →+* N` to `(IntermediateField.inclusion hk).toRingHom`. Set `f : 𝓞 k →+* 𝓞 N` to `RingOfIntegers.mapRingHom i`. Establish `ef : i.comp (algebraMap (𝓞 k) k) = (algebraMap (𝓞 N) N).comp f` using `RingHom.ext fun _ => rfl`. Take `⟨P', φ, hφ⟩` from `exists_isPolFibre hB f P`. Take `⟨Q', ψ, hψ⟩` from `exists_isPolFibre hB f Q`.

Take `⟨v', hv, -⟩` from `existsUnique_isVecOver hφ.2.1.1 v`. Take `⟨t', ht, -⟩` from `existsUnique_isVecOver hψ.2.1.1 t`. Conclude with `GlobalTheory.T.isIntegral_derivative_curve_hom_good_reduction GlobalTheory.T.semiAbelian_hom_extension_dvr hB N P' Q' v' t' b (hv.isTangent hφ.2.1 hP.isTangent) (curve_lattice_baseChange _ Q t L' _ f Q' ψ t' hQ hψ ht).2.2.1 (HomOf.fibre (ef ▸ h) hφ hψ hv ht)`.
-/
theorem integral_and_conj {k N : IntermediateField ℚ ℂ} [NumberField k] [NumberField N]
    {P Q : Out.PolAV (Sp (𝓞 k))} {v : epsR (𝓞 k) ⟶ P.A} {t : epsR (𝓞 k) ⟶ Q.A}
    {L L' : (𝓞 k →+* ℂ) → PeriodPair} (hP : Curve P v L) (hQ : Curve Q t L') (hk : k ≤ N) {a : N}
    (h : DefinedOver (algebraMap (𝓞 k) k) P v Q t N a) :
    IsIntegral ℤ a ∧ ∀ s : N →+* ℂ,
      ∀ z ∈ (L (s.comp ((IntermediateField.inclusion hk).toRingHom.comp (algebraMap (𝓞 k) k)))).lattice,
        s a * z ∈ (L' (s.comp ((IntermediateField.inclusion hk).toRingHom.comp (algebraMap (𝓞 k) k)))).lattice := by
  have hU := GlobalTheory.T.thetaUniformisation_complexAbelianVariety
  have hB := GlobalTheory.T.abelianScheme_laws_unconditional.1.polBaseChange
  obtain ⟨_, b, hb, h⟩ := h
  obtain rfl : b = a := Subtype.ext hb
  refine ⟨?_, fun s => (EllipticHom.multiplier_iff_exists_hom hU hB _ P Q v t _ _ _ _ hP.1 hQ.1 hP.isTangent
    hQ.isTangent (hP.2.2.2 _) (hQ.2.2.2 _)).2 (h.up hB s)⟩
  let i : k →+* N := (IntermediateField.inclusion hk).toRingHom
  let f : 𝓞 k →+* 𝓞 N := RingOfIntegers.mapRingHom i
  have ef : i.comp (algebraMap (𝓞 k) k) = (algebraMap (𝓞 N) N).comp f := RingHom.ext fun _ => rfl
  obtain ⟨P', φ, hφ⟩ := exists_isPolFibre hB f P
  obtain ⟨Q', ψ, hψ⟩ := exists_isPolFibre hB f Q
  obtain ⟨v', hv, -⟩ := existsUnique_isVecOver hφ.2.1.1 v
  obtain ⟨t', ht, -⟩ := existsUnique_isVecOver hψ.2.1.1 t
  exact GlobalTheory.T.isIntegral_derivative_curve_hom_good_reduction GlobalTheory.T.semiAbelian_hom_extension_dvr hB N P' Q' v' t' b (hv.isTangent hφ.2.1 hP.isTangent)
    (curve_lattice_baseChange _ Q t L' _ f Q' ψ t' hQ hψ ht).2.2.1 (HomOf.fibre (ef ▸ h) hφ hψ hv ht)

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Establish `hU` using `GlobalTheory.T.thetaUniformisation_complexAbelianVariety`. Establish `hB` using `GlobalTheory.T.abelianScheme_laws_unconditional.1.polBaseChange`. Take `⟨k, hk, hσk, HI⟩` from `CMData.exists_field h2 σ hσ`. Establish `hNF : NumberField k` using `⟨⟩`. Use `choose W hW hc using HI`.

Use `choose P v Lf h₁ h₂ using fun I ↦ GlobalTheory.T.exists_ellipticCurve_polarised_lattice_family hU hB (𝓞 k) (W I) (hW I)`. Use `choose c hc0 hc using fun I ↦ hc I (Lf I _) (h₂ I _).1 (h₂ I _).2.2`. Set `J : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ` to `fun C ↦ (FractionalIdeal.mk0 K (𝔟 C))⁻¹ * I`. Take `⟨N₀, hN₀, hk₀, e₀⟩` from `exists_field hU hB (algebraMap (𝓞 k) k) (h₁ I) (h₁ I)`. Use `choose N₁ hN₁ hk₁ e₁ using fun C => exists_field hU hB (algebraMap (𝓞 k) k) (h₁ I) (h₁ (J C))`.

Use `choose N₂ hN₂ hk₂ e₂ using fun C => exists_field hU hB (algebraMap (𝓞 k) k) (h₁ (J C)) (h₁ I)`. Take `⟨N, hN, lM, l₀, l₁, l₂⟩ : ∃ N : IntermediateField ℚ ℂ, FiniteDimensional ℚ N ∧ M ≤ N ∧ N₀ ≤ N ∧ (∀ C, N₁ C ≤ N) ∧ ∀ C, N₂ C ≤ N` from `⟨M ⊔ (N₀ ⊔ ((⨆ C, N₁ C) ⊔ ⨆ C, N₂ C)), inferInstance, le_sup_left, le_sup_left.trans le_sup_right, fun C => (((le_iSup N₁ C).trans le_sup_left).trans le_sup_right).trans le_sup_right, fun C => (((le_iSup N₂ C).trans le_sup_right).trans le_sup_right).trans le_sup_right⟩`. Establish `hkN : k ≤ N` using `hk₀.trans l₀`. Establish `hNF' : NumberField N` using `⟨⟩`. Set `i : k →+* N` to `(IntermediateField.inclusion hkN).toRingHom`.

Set `ρ : 𝓞 k →+* N` to `i.comp (algebraMap (𝓞 k) k)`. Set `f : 𝓞 k →+* 𝓞 N` to `RingOfIntegers.mapRingHom i`. Set `_ : Algebra K N` to `(σ.codRestrict N fun a => hkN (hσk a)).toAlgebra`. Establish `ha : ∀ x : K, ((algebraMap K N x : N) : ℂ) = σ x` using `fun _ => rfl`. Establish `m₁ : ∀ C (x : K), (∀ b ∈ (𝔟 C : Ideal (𝓞 K)), IsIntegral ℤ (x * (b : K))) → DefinedOver (algebraMap (𝓞 k) k) (P I) (v I) (P (J C)) (v (J C)) N (c (J C) / c I * σ x)` using `fun C x hx => (e₁ C _ fun z hz => by`.

Take `⟨y, hy, rfl⟩` from `(hc I z).1 hz`. Use `(hc _ _).2 ⟨x * y, FractionalIdeal.mul_mem_mul ((CMData.mem_inv_iff _ x).2 hx) hy, ?_⟩` and prove the remaining obligations. Use `hc0 I` as an intermediate fact. Rewrite using `[map_mul]`. Use the proof step `field_simp).mono hB (l₁ C)`.

Establish `m₂ : ∀ C, ∀ y ∈ (𝔟 C : Ideal (𝓞 K)), DefinedOver (algebraMap (𝓞 k) k) (P (J C)) (v (J C)) (P I) (v I) N ((c (J C) / c I)⁻¹ * σ (y : K))` using `fun C y hy => (e₂ C _ fun z hz => by`. Take `⟨x, hx, rfl⟩` from `(hc _ z).1 hz`. Establish `h3 : (y : K) * x ∈ (FractionalIdeal.mk0 K (𝔟 C) * J C).1` using `FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hy) hx`. Rewrite `h3` using `[mul_inv_cancel_left]`. Use `(hc _ _).2 ⟨_, h3, ?_⟩` and prove the remaining obligations.

Use `hc0 (J C)` as an intermediate fact. Rewrite using `[map_mul]`. Use the proof step `field_simp).mono hB (l₂ C)`. Establish `hβN : ∀ C, c (J C) / c I ∈ N` using `fun C => by`. Take `⟨_, a, ha, -⟩` from `m₁ C 1 (fun b _ => by simpa using b.isIntegral_coe)`.

Rewrite `ha` using `[map_one, mul_one]`. Conclude with `ha ▸ a.2`. Establish `key` using `mean_log_covolume_eq_mean_classGroup K N h2 σ hσ 𝔟 Lc h𝔟 hLc (fun s => Lf I (s.comp ρ)) (fun C s => Lf (J C) (s.comp ρ)) (fun C => Units.map f.toMonoidHom (hW (J C)).unit) (fun C => ⟨_, hβN C⟩) (fun s a => (integral_and_conj (h₁ I) (h₁ I) hkN (a := algebraMap K N a) ((e₀ (σ a) fu …`. Take `⟨y, hy, rfl⟩` from `(hc I z).1 hz`. Use `(hc _ _).2 ⟨a • y, I.1.coeToSubmodule.smul_mem a hy, ?_⟩` and prove the remaining obligations.

Rewrite using `[show a • y = (a : K) * y from rfl, map_mul]`. Use the proof step `ring).mono hB l₀)).2 s)`. Use the proof step `(fun C s => (h₂ (J C) (s.comp ρ)).2.2.symm)`. Use the proof step `(fun C h => div_ne_zero (hc0 _) (hc0 _) (congrArg Subtype.val h))`. Use the proof step `(fun C x hx => integral_and_conj (h₁ I) (h₁ (J C)) hkN (m₁ C x hx))`.

Use the proof step `(fun C y hy => integral_and_conj (h₁ (J C)) (h₁ I) hkN (m₂ C y hy))`. Simplify using `only [← latticeNormDisc_eq] at key`. Simplify using `only [← latticeArea_eq_abs_im_mul_conj] at key`. Conclude with `⟨N, hNF', ρ (W I).c₄, Units.map f.toMonoidHom (hW I).unit, fun s => Lf I (s.comp ρ), c I, lM, fun s => ⟨(h₂ I (s.comp ρ)).1, (h₂ I (s.comp ρ)).2.2⟩, hc0 I, hc I, key⟩`.
-/
theorem exists_family (h2 : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ¬ ComplexEmbedding.IsReal σ)
    (𝔟 : ClassGroup (𝓞 K) → (Ideal (𝓞 K))⁰) (Lc : ClassGroup (𝓞 K) → PeriodPair) (h𝔟 : ∀ C, ClassGroup.mk0 (𝔟 C) = C)
    (hLc : ∀ C z, z ∈ (Lc C).lattice ↔ ∃ a ∈ (𝔟 C : Ideal (𝓞 K)), z = σ (a : K))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] :
    ∃ (N : IntermediateField ℚ ℂ) (_ : NumberField N) (c₄ : N) (Δ : (𝓞 N)ˣ) (L : (N →+* ℂ) → PeriodPair) (c : ℂ),
      M ≤ N ∧ (∀ s : N →+* ℂ, s c₄ = 12 * (L s).g₂ ∧ s (Δ : 𝓞 N) = (L s).g₂ ^ 3 - 27 * (L s).g₃ ^ 2) ∧ c ≠ 0 ∧
      (∀ z, z ∈ (L (algebraMap N ℂ)).lattice ↔ ∃ x ∈ I.1, z = c * σ x) ∧
      (∑ s, Real.log (latticeArea (L s))) / Module.finrank ℚ N =
        (∑ C, Real.log (latticeNormDisc (Lc C))) / (6 * Fintype.card (ClassGroup (𝓞 K))) := by
  have hU := GlobalTheory.T.thetaUniformisation_complexAbelianVariety
  have hB := GlobalTheory.T.abelianScheme_laws_unconditional.1.polBaseChange
  obtain ⟨k, hk, hσk, HI⟩ := CMData.exists_field h2 σ hσ
  have hNF : NumberField k := ⟨⟩
  choose W hW hc using HI
  choose P v Lf h₁ h₂ using fun I ↦ GlobalTheory.T.exists_ellipticCurve_polarised_lattice_family hU hB (𝓞 k) (W I) (hW I)
  choose c hc0 hc using fun I ↦ hc I (Lf I _) (h₂ I _).1 (h₂ I _).2.2
  let J : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ := fun C ↦ (FractionalIdeal.mk0 K (𝔟 C))⁻¹ * I
  obtain ⟨N₀, hN₀, hk₀, e₀⟩ := exists_field hU hB (algebraMap (𝓞 k) k) (h₁ I) (h₁ I)
  choose N₁ hN₁ hk₁ e₁ using fun C => exists_field hU hB (algebraMap (𝓞 k) k) (h₁ I) (h₁ (J C))
  choose N₂ hN₂ hk₂ e₂ using fun C => exists_field hU hB (algebraMap (𝓞 k) k) (h₁ (J C)) (h₁ I)
  obtain ⟨N, hN, lM, l₀, l₁, l₂⟩ : ∃ N : IntermediateField ℚ ℂ, FiniteDimensional ℚ N ∧ M ≤ N ∧ N₀ ≤ N ∧
      (∀ C, N₁ C ≤ N) ∧ ∀ C, N₂ C ≤ N :=
    ⟨M ⊔ (N₀ ⊔ ((⨆ C, N₁ C) ⊔ ⨆ C, N₂ C)), inferInstance, le_sup_left, le_sup_left.trans le_sup_right,
      fun C => (((le_iSup N₁ C).trans le_sup_left).trans le_sup_right).trans le_sup_right,
      fun C => (((le_iSup N₂ C).trans le_sup_right).trans le_sup_right).trans le_sup_right⟩
  have hkN : k ≤ N := hk₀.trans l₀
  have hNF' : NumberField N := ⟨⟩
  let i : k →+* N := (IntermediateField.inclusion hkN).toRingHom
  let ρ : 𝓞 k →+* N := i.comp (algebraMap (𝓞 k) k)
  let f : 𝓞 k →+* 𝓞 N := RingOfIntegers.mapRingHom i
  let _ : Algebra K N := (σ.codRestrict N fun a => hkN (hσk a)).toAlgebra
  have ha : ∀ x : K, ((algebraMap K N x : N) : ℂ) = σ x := fun _ => rfl
  have m₁ : ∀ C (x : K), (∀ b ∈ (𝔟 C : Ideal (𝓞 K)), IsIntegral ℤ (x * (b : K))) →
      DefinedOver (algebraMap (𝓞 k) k) (P I) (v I) (P (J C)) (v (J C)) N (c (J C) / c I * σ x) := fun C x hx =>
    (e₁ C _ fun z hz => by
      obtain ⟨y, hy, rfl⟩ := (hc I z).1 hz
      refine (hc _ _).2 ⟨x * y, FractionalIdeal.mul_mem_mul ((CMData.mem_inv_iff _ x).2 hx) hy, ?_⟩
      have := hc0 I
      rw [map_mul]
      field_simp).mono hB (l₁ C)
  have m₂ : ∀ C, ∀ y ∈ (𝔟 C : Ideal (𝓞 K)),
      DefinedOver (algebraMap (𝓞 k) k) (P (J C)) (v (J C)) (P I) (v I) N ((c (J C) / c I)⁻¹ * σ (y : K)) := fun C y hy =>
    (e₂ C _ fun z hz => by
      obtain ⟨x, hx, rfl⟩ := (hc _ z).1 hz
      have h3 : (y : K) * x ∈ (FractionalIdeal.mk0 K (𝔟 C) * J C).1 :=
        FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hy) hx
      rw [mul_inv_cancel_left] at h3
      refine (hc _ _).2 ⟨_, h3, ?_⟩
      have := hc0 (J C)
      rw [map_mul]
      field_simp).mono hB (l₂ C)
  have hβN : ∀ C, c (J C) / c I ∈ N := fun C => by
    obtain ⟨_, a, ha, -⟩ := m₁ C 1 (fun b _ => by simpa using b.isIntegral_coe)
    rw [map_one, mul_one] at ha
    exact ha ▸ a.2
  have key := mean_log_covolume_eq_mean_classGroup K N h2 σ hσ 𝔟 Lc h𝔟 hLc (fun s => Lf I (s.comp ρ))
    (fun C s => Lf (J C) (s.comp ρ)) (fun C => Units.map f.toMonoidHom (hW (J C)).unit) (fun C => ⟨_, hβN C⟩)
    (fun s a => (integral_and_conj (h₁ I) (h₁ I) hkN (a := algebraMap K N a) ((e₀ (σ a) fun z hz => by
      obtain ⟨y, hy, rfl⟩ := (hc I z).1 hz
      refine (hc _ _).2 ⟨a • y, I.1.coeToSubmodule.smul_mem a hy, ?_⟩
      rw [show a • y = (a : K) * y from rfl, map_mul]
      ring).mono hB l₀)).2 s)
    (fun C s => (h₂ (J C) (s.comp ρ)).2.2.symm)
    (fun C h => div_ne_zero (hc0 _) (hc0 _) (congrArg Subtype.val h))
    (fun C x hx => integral_and_conj (h₁ I) (h₁ (J C)) hkN (m₁ C x hx))
    (fun C y hy => integral_and_conj (h₁ (J C)) (h₁ I) hkN (m₂ C y hy))
  simp only [← latticeNormDisc_eq] at key
  simp only [← latticeArea_eq_abs_im_mul_conj] at key
  exact ⟨N, hNF', ρ (W I).c₄, Units.map f.toMonoidHom (hW I).unit, fun s => Lf I (s.comp ρ), c I, lM,
    fun s => ⟨(h₂ I (s.comp ρ)).1, (h₂ I (s.comp ρ)).2.2⟩, hc0 I, hc I, key⟩

end Curves

section Mean

open NumberField
open scoped UpperHalfPlane nonZeroDivisors

/- English proof (translation)
Use `sum_log_norm_embedding_eq_finrank_mul_log_absNorm N N ⊤ ((u : 𝓞 N) : N) top_ne_bot (by exact_mod_cast u.ne_zero) (fun x hx => (RingOfIntegers.isIntegral_coe _).mul (by simpa using hx 1 trivial)) (fun y _ => by` as an intermediate fact. Establish `: (((u : 𝓞 N) : N))⁻¹ = ((u⁻¹ : (𝓞 N)ˣ) : 𝓞 N)`. Apply `inv_eq_of_mul_eq_one_right` to reduce the goal to its premises. Rewrite using `[← map_mul]`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Conclude with `(RingOfIntegers.isIntegral_coe _).mul (RingOfIntegers.isIntegral_coe _))`. Simplify using `using this`.
-/
theorem sum_log_norm_unit {N : Type} [Field N] [NumberField N] (u : (𝓞 N)ˣ) :
    ∑ s : N →+* ℂ, Real.log ‖s ((u : 𝓞 N) : N)‖ = 0 := by
  have := sum_log_norm_embedding_eq_finrank_mul_log_absNorm N N ⊤ ((u : 𝓞 N) : N) top_ne_bot
    (by exact_mod_cast u.ne_zero)
    (fun x hx => (RingOfIntegers.isIntegral_coe _).mul (by simpa using hx 1 trivial))
    (fun y _ => by
      have : (((u : 𝓞 N) : N))⁻¹ = ((u⁻¹ : (𝓞 N)ˣ) : 𝓞 N) := by
        apply inv_eq_of_mul_eq_one_right
        rw [← map_mul]; simp
      rw [this]
      exact (RingOfIntegers.isIntegral_coe _).mul (RingOfIntegers.isIntegral_coe _))
  simpa using this

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Use `choose 𝔟 h𝔟 using ClassGroup.mk0_surjective (R := 𝓞 K)`. Use `choose Lc hLc using fun C => exists_periodPair_image_ideal h2 hσ (nonZeroDivisors.coe_ne_zero (𝔟 C))`. Use `choose τ hτ using exists_isIdealClassPoint h2 hD σ`. Take `⟨N, _, c₄, Δ, L', c, hMN, hL', hc, hI, key⟩` from `exists_family h2 σ hσ 𝔟 Lc h𝔟 hLc I M`. Set `_ : Algebra M N` to `(IntermediateField.inclusion hMN).toRingHom.toAlgebra`.

Establish `hH : IsHomothetic (c / δ) L₀ (L' (algebraMap N ℂ))` using `fun z => by`. Rewrite using `[hI, hL₀]`. Use `exists_congr fun x => and_congr_right fun _ => ?_` and prove the remaining obligations. Rewrite using `[div_mul_eq_mul_div, div_eq_iff hδ, mul_assoc, mul_right_inj' hc, mul_comm]`. Establish `e1 : a ^ 3 - 27 * b ^ 2 = 1` using `(algebraMap M ℂ).injective (by`.

Rewrite using `[map_sub, map_mul, map_pow, map_pow, map_ofNat, map_one, ← h1, ← ha, ← hb]`. Use the proof step `rfl)`. Establish `e2 : c₄ ^ 3 = 1728 * algebraMap M N a ^ 3 * (Δ : 𝓞 N)` using `(algebraMap N ℂ).injective (by`. Establish `hj` using `CMCurves.latticeJ_eq_of_isHomothetic hH`. Rewrite `hj` using `[CMCurves.latticeJ, CMCurves.latticeJ, h1, div_one, div_eq_iff (g₂_cube_sub_g₃_sq_ne_zero _), ← ha]`.

Rewrite using `[map_mul, map_mul, map_pow, map_pow, map_ofNat, (hL' _).1, (hL' _).2, show algebraMap N ℂ (algebraMap M N a) = a from rfl, ← hj]`. Use the proof step `ring)`. Establish `e3 : ∀ s : N →+* ℂ, 6 * Real.log (latticeArea (L (s.comp (algebraMap M N)))) = 6 * Real.log (latticeArea (L' s)) + Real.log ‖s ((Δ : 𝓞 N) : N)‖` using `fun s => by`. Establish `e4 : (L (s.comp (algebraMap M N))).g₂ ^ 3 - 27 * (L (s.comp (algebraMap M N))).g₃ ^ 2 = 1`. Use `congrArg (s.comp (algebraMap M N)) e1` as an intermediate fact.

Rewrite `this` using `[map_sub, map_mul, map_pow, map_pow, map_ofNat, map_one, ← (hL _).1, ← (hL _).2]`. Then use the resulting hypothesis. Take `⟨κ, H⟩` from `exists_isHomothetic_of_j_eq (L := L (s.comp (algebraMap M N))) (L' := L' s) (by`. Use `congrArg s e2` as an intermediate fact. Rewrite `this` using `[map_mul, map_mul, map_pow, map_pow, map_ofNat, (hL' _).1, (hL' _).2]`. Rewrite using `[e4, (hL _).1, RingHom.comp_apply]`.

Take the linear combination `-this / 1728)`. Use `congrArg Real.log H.latticeNormDisc_eq` as an intermediate fact. Rewrite `this` using `[latticeNormDisc, latticeNormDisc, e4, norm_one, mul_one, Real.log_mul (pow_pos (latticeArea_pos _) _).ne' (norm_ne_zero_iff.2 (g₂_cube_sub_g₃_sq_ne_zero _)), Real.log_pow, Real.log_pow, ← (hL' _).2]`. Conclude with `this.symm` after adjusting the coercions. Establish `e5` using `Finset.sum_congr (rfl : Finset.univ = Finset.univ) fun s _ => e3 s`.

Rewrite `e5` using `[Finset.sum_add_distrib, sum_log_norm_unit, ← Finset.mul_sum, ← Finset.mul_sum, add_zero, ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.sum_embeddings_restrict fun s => Real.log (latticeArea (L s))]`. Establish `e6` using `log_pi_sub_mean_log_latticeNormDisc K h2 σ hσ 𝔟 Lc h𝔟 hLc σ τ hτ`. Simplify using `only [← latticeNormDisc_eq] at e6`. Establish `e7` using `congrArg Complex.re (chowla_selberg_eta h2 hD hd hχ σ hτ)`. Rewrite `e7` using `[Complex.ofReal_re, Complex.sub_re, Complex.ofReal_re]`.

Rewrite `e6` using `[← key, Finset.sum_neg_distrib, neg_div, e7, ← Module.finrank_mul_finrank ℚ M N]`. Establish `hM : (Module.finrank ℚ M : ℝ) ≠ 0` using `by exact_mod_cast Module.finrank_pos.ne'`. Establish `: Module.Finite M N` using `Module.Finite.of_restrictScalars_finite ℚ M N`. Establish `hN : (Module.finrank M N : ℝ) ≠ 0` using `by exact_mod_cast Module.finrank_pos.ne'`. Rewrite `e6` using `[← mul_left_cancel₀ (by norm_num) e5, Nat.cast_mul, mul_comm (Module.finrank ℚ M : ℝ), mul_div_mul_left _ _ hN]`.

Simplify using `only [Real.log_div (latticeArea_pos _).ne' Real.pi_ne_zero, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Embeddings.card, nsmul_eq_mul]`. Rewrite using `[sub_div, mul_div_cancel_left₀ _ hM]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem mean_log_area {d : ℕ} [NeZero d] (h2 : Module.finrank ℚ K = 2) (hD : discr K = -d) (hd : 4 < d)
    {χ : DirichletCharacter ℂ d} (hχ : IsKroneckerChar χ) (σ : K →+* ℂ) (hσ : ¬ ComplexEmbedding.IsReal σ)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {δ : ℂ} (hδ : δ ≠ 0) {L₀ : PeriodPair}
    (hL₀ : ∀ z, z ∈ L₀.lattice ↔ ∃ x ∈ I.1, z = δ * σ x) (h1 : L₀.g₂ ^ 3 - 27 * L₀.g₃ ^ 2 = 1)
    (M : IntermediateField ℚ ℂ) [NumberField M] (a b : M) (ha : (a : ℂ) = L₀.g₂) (hb : (b : ℂ) = L₀.g₃)
    (L : (M →+* ℂ) → PeriodPair) (hL : ∀ s, (L s).g₂ = s a ∧ (L s).g₃ = s b) :
    (∑ s, Real.log (latticeArea (L s) / Real.pi)) / Module.finrank ℚ M =
      Real.eulerMascheroniConstant + Real.log (2 * Real.pi / √d) - (deriv χ.LFunction 1 / χ.LFunction 1).re := by
  choose 𝔟 h𝔟 using ClassGroup.mk0_surjective (R := 𝓞 K)
  choose Lc hLc using fun C => exists_periodPair_image_ideal h2 hσ (nonZeroDivisors.coe_ne_zero (𝔟 C))
  choose τ hτ using exists_isIdealClassPoint h2 hD σ
  obtain ⟨N, _, c₄, Δ, L', c, hMN, hL', hc, hI, key⟩ := exists_family h2 σ hσ 𝔟 Lc h𝔟 hLc I M
  let _ : Algebra M N := (IntermediateField.inclusion hMN).toRingHom.toAlgebra
  have hH : IsHomothetic (c / δ) L₀ (L' (algebraMap N ℂ)) := fun z => by
    rw [hI, hL₀]
    refine exists_congr fun x => and_congr_right fun _ => ?_
    rw [div_mul_eq_mul_div, div_eq_iff hδ, mul_assoc, mul_right_inj' hc, mul_comm]
  have e1 : a ^ 3 - 27 * b ^ 2 = 1 := (algebraMap M ℂ).injective (by
    rw [map_sub, map_mul, map_pow, map_pow, map_ofNat, map_one, ← h1, ← ha, ← hb]; rfl)
  have e2 : c₄ ^ 3 = 1728 * algebraMap M N a ^ 3 * (Δ : 𝓞 N) := (algebraMap N ℂ).injective (by
    have hj := CMCurves.latticeJ_eq_of_isHomothetic hH
    rw [CMCurves.latticeJ, CMCurves.latticeJ, h1, div_one, div_eq_iff (g₂_cube_sub_g₃_sq_ne_zero _), ← ha] at hj
    rw [map_mul, map_mul, map_pow, map_pow, map_ofNat, (hL' _).1, (hL' _).2, show algebraMap N ℂ (algebraMap M N a) = a from rfl, ← hj]
    ring)
  have e3 : ∀ s : N →+* ℂ, 6 * Real.log (latticeArea (L (s.comp (algebraMap M N)))) =
      6 * Real.log (latticeArea (L' s)) + Real.log ‖s ((Δ : 𝓞 N) : N)‖ := fun s => by
    have e4 : (L (s.comp (algebraMap M N))).g₂ ^ 3 - 27 * (L (s.comp (algebraMap M N))).g₃ ^ 2 = 1 := by
      have := congrArg (s.comp (algebraMap M N)) e1
      rwa [map_sub, map_mul, map_pow, map_pow, map_ofNat, map_one, ← (hL _).1, ← (hL _).2] at this
    obtain ⟨κ, H⟩ := exists_isHomothetic_of_j_eq (L := L (s.comp (algebraMap M N))) (L' := L' s) (by
      have := congrArg s e2
      rw [map_mul, map_mul, map_pow, map_pow, map_ofNat, (hL' _).1, (hL' _).2] at this
      rw [e4, (hL _).1, RingHom.comp_apply]
      linear_combination -this / 1728)
    have := congrArg Real.log H.latticeNormDisc_eq
    rw [latticeNormDisc, latticeNormDisc, e4, norm_one, mul_one, Real.log_mul (pow_pos (latticeArea_pos _) _).ne'
      (norm_ne_zero_iff.2 (g₂_cube_sub_g₃_sq_ne_zero _)), Real.log_pow, Real.log_pow, ← (hL' _).2] at this
    exact_mod_cast this.symm
  have e5 := Finset.sum_congr (rfl : Finset.univ = Finset.univ) fun s _ => e3 s
  rw [Finset.sum_add_distrib, sum_log_norm_unit, ← Finset.mul_sum, ← Finset.mul_sum, add_zero,
    ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.sum_embeddings_restrict fun s => Real.log (latticeArea (L s))] at e5
  have e6 := log_pi_sub_mean_log_latticeNormDisc K h2 σ hσ 𝔟 Lc h𝔟 hLc σ τ hτ
  simp only [← latticeNormDisc_eq] at e6
  have e7 := congrArg Complex.re (chowla_selberg_eta h2 hD hd hχ σ hτ)
  rw [Complex.ofReal_re, Complex.sub_re, Complex.ofReal_re] at e7
  rw [← key, Finset.sum_neg_distrib, neg_div, e7, ← Module.finrank_mul_finrank ℚ M N] at e6
  have hM : (Module.finrank ℚ M : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have : Module.Finite M N := Module.Finite.of_restrictScalars_finite ℚ M N
  have hN : (Module.finrank M N : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  rw [← mul_left_cancel₀ (by norm_num) e5, Nat.cast_mul, mul_comm (Module.finrank ℚ M : ℝ),
    mul_div_mul_left _ _ hN] at e6
  simp only [Real.log_div (latticeArea_pos _).ne' Real.pi_ne_zero, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Embeddings.card, nsmul_eq_mul]
  rw [sub_div, mul_div_cancel_left₀ _ hM]
  linarith

end Mean

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

/- English proof (translation)
Introduce `D hD cc δ hc M _ h2 h3`. Establish `: NumberField M` using `⟨⟩`. Establish `: Fact D.host.d.Prime` using `⟨D.host.hyp.2.1⟩`. Establish `: NeZero D.host.d` using `⟨D.host.hyp.2.1.ne_zero⟩`. Establish `h16` using `D.host.hyp.2.2.2.1`.

Take `⟨⟨w₁, w₂, hw, hΛ⟩, hδ, h1, -⟩` from `CurveLattice.lattice_of_curve D hD cc δ hc`. Set `L₀ : PeriodPair` to `⟨w₁, w₂, hw⟩`. Establish `hL₀ : ∀ z, z ∈ lamOf D cc δ ↔ z ∈ L₀.lattice` using `fun z => by`. Rewrite using `[hΛ, AddSubgroup.mem_closure_pair, PeriodPair.mem_lattice]`. Simplify using `only [zsmul_eq_mul, L₀]`.

Take `⟨e2, e3, -, -, -, -, hex⟩` from `GlobalTheory.T.latticeInvariants_periodPair_dictionary L₀ _ hL₀`. Set `σ : D.host.K →+* ℂ` to `D.host.φ₀.comp D.host.K.val.toRingHom`. Establish `hσ : ¬ ComplexEmbedding.IsReal σ` using `fun h => by`. Take `⟨r, hr⟩ : ∃ r : D.host.K, r ^ 2 = -(D.host.d : D.host.K)` from `⟨_, Formalism.FrobeniusOrbits.SplitK.bK_sq (D.host.sqd_sq)⟩`. Establish `e` using `congrArg h.embedding hr`.

Rewrite `e` using `[map_pow, map_neg, map_natCast]`. Establish `: (0 : ℝ) < D.host.d` using `by exact_mod_cast D.host.hyp.2.1.pos`. Use polynomial arithmetic with `[sq_nonneg (h.embedding r)]`. Establish `e1 : TaylorLogMetric.liftM M (g2 (lamOf D cc δ)) ^ 3 - 27 * TaylorLogMetric.liftM M (g3 (lamOf D cc δ)) ^ 2 = 1` using `(algebraMap M ℂ).injective (by`. Rewrite using `[map_sub, map_mul, map_pow, map_pow, map_ofNat, map_one, ← h1, TaylorLogMetric.liftM, TaylorLogMetric.liftM, dif_pos h2, dif_pos h3]`.

Use the proof step `rfl)`. Use `choose L hL using fun s : M →+* ℂ => hex (s (TaylorLogMetric.liftM M (g2 (lamOf D cc δ)))) (s (TaylorLogMetric.liftM M (g3 (lamOf D cc δ)))) (by`. Use `congrArg s e1` as an intermediate fact. Rewrite `this` using `[map_sub, map_mul, map_pow, map_pow, map_ofNat, map_one]`. Rewrite using `[this]`.

Conclude with `one_ne_zero)`. Establish `key` using `mean_log_area (CurveLattice.finrank_hostK D) (CurveLattice.discr_hostK D) (by omega) (isKroneckerChar_quadraticChar (by omega)) σ hσ (FractionalIdeal.mk0 D.host.K ⟨cc, mem_nonZeroDivisors_of_ne_zero hc.1.1⟩) hδ (L₀ := L₀) (fun z => by`. Rewrite using `[← hL₀, CurveLattice.mem_lamOf]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc, rfl⟩`.

Conclude with `⟨c, FractionalIdeal.mem_coeIdeal_of_mem _ hc, rfl⟩`. Introduce and unpack `⟨y, hy, rfl⟩`. Take `⟨c, hc, rfl⟩` from `(FractionalIdeal.mem_coeIdeal _).1 hy`. Conclude with `⟨c, hc, rfl⟩)`. Use the proof step `(by rw [← e2, ← e3]; exact h1) M _ _ (by rw [← e2, TaylorLogMetric.liftM, dif_pos h2]) (by rw [← e3, TaylorLogMetric.liftM, dif_pos h3]) L hL`.

Use `Eq.trans ?_ key` and prove the remaining obligations. Use `congr 1`. Use `(Fintype.sum_equiv (RingHom.equivRatAlgHom M ℂ) _ _ fun s => ?_).symm` and prove the remaining obligations. Take `⟨f2, f3, -, fa, -, fu, -⟩` from `GlobalTheory.T.latticeInvariants_periodPair_dictionary (L s) (L s).lattice.toAddSubgroup fun _ => Iff.rfl`. Establish `hs : g2 (lamConj M (RingHom.equivRatAlgHom M ℂ s) (lamOf D cc δ)) = s (TaylorLogMetric.liftM M (g2 (lamOf D cc δ))) ∧ g3 (lamConj M (RingHom.equivRatAlgHom M ℂ s) (lamOf D cc δ)) = s (TaylorLogMetric.liftM M (g3 (lamOf D cc δ)))` using `Classical.epsilon_spec (p := fun Λ' : AddSubgroup ℂ => g2 Λ' = s (TaylorLogMetric.liftM M (g2 (lamOf D cc δ))) ∧ g3 Λ' = s (TaylorLogMetric.liftM M (g3 (lamOf D cc δ)))) ⟨_, f2.trans (hL s).1, f3.trans (hL s).2⟩`.

Rewrite using `[fu _ (hs.1.trans (f2.trans (hL s).1).symm) (hs.2.trans (f3.trans (hL s).2).symm), fa, latticeArea_eq_abs_im_mul_conj]`.
-/
theorem mean_log_period : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M], g2 (lamOf D cc δ) ∈ M → g3 (lamOf D cc δ) ∈ M → (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ (lamOf D cc δ)) / Real.pi)) / (Module.finrank ℚ M : ℝ) = Real.eulerMascheroniConstant + Real.log (2 * Real.pi / Real.sqrt D.host.d) - logDerivativeAtOne D := by
  intro D hD cc δ hc M _ h2 h3
  have : NumberField M := ⟨⟩
  have : Fact D.host.d.Prime := ⟨D.host.hyp.2.1⟩
  have : NeZero D.host.d := ⟨D.host.hyp.2.1.ne_zero⟩
  have h16 := D.host.hyp.2.2.2.1
  obtain ⟨⟨w₁, w₂, hw, hΛ⟩, hδ, h1, -⟩ := CurveLattice.lattice_of_curve D hD cc δ hc
  let L₀ : PeriodPair := ⟨w₁, w₂, hw⟩
  have hL₀ : ∀ z, z ∈ lamOf D cc δ ↔ z ∈ L₀.lattice := fun z => by
    rw [hΛ, AddSubgroup.mem_closure_pair, PeriodPair.mem_lattice]
    simp only [zsmul_eq_mul, L₀]
  obtain ⟨e2, e3, -, -, -, -, hex⟩ := GlobalTheory.T.latticeInvariants_periodPair_dictionary L₀ _ hL₀
  let σ : D.host.K →+* ℂ := D.host.φ₀.comp D.host.K.val.toRingHom
  have hσ : ¬ ComplexEmbedding.IsReal σ := fun h => by
    obtain ⟨r, hr⟩ : ∃ r : D.host.K, r ^ 2 = -(D.host.d : D.host.K) :=
      ⟨_, Formalism.FrobeniusOrbits.SplitK.bK_sq (D.host.sqd_sq)⟩
    have e := congrArg h.embedding hr
    rw [map_pow, map_neg, map_natCast] at e
    have : (0 : ℝ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos
    nlinarith [sq_nonneg (h.embedding r)]
  have e1 : TaylorLogMetric.liftM M (g2 (lamOf D cc δ)) ^ 3 - 27 * TaylorLogMetric.liftM M (g3 (lamOf D cc δ)) ^ 2 = 1 :=
    (algebraMap M ℂ).injective (by
      rw [map_sub, map_mul, map_pow, map_pow, map_ofNat, map_one, ← h1, TaylorLogMetric.liftM, TaylorLogMetric.liftM, dif_pos h2, dif_pos h3]; rfl)
  choose L hL using fun s : M →+* ℂ => hex (s (TaylorLogMetric.liftM M (g2 (lamOf D cc δ)))) (s (TaylorLogMetric.liftM M (g3 (lamOf D cc δ)))) (by
    have := congrArg s e1
    rw [map_sub, map_mul, map_pow, map_pow, map_ofNat, map_one] at this
    rw [this]; exact one_ne_zero)
  have key := mean_log_area (CurveLattice.finrank_hostK D) (CurveLattice.discr_hostK D) (by omega)
    (isKroneckerChar_quadraticChar (by omega)) σ hσ
    (FractionalIdeal.mk0 D.host.K ⟨cc, mem_nonZeroDivisors_of_ne_zero hc.1.1⟩) hδ (L₀ := L₀) (fun z => by
      rw [← hL₀, CurveLattice.mem_lamOf]
      constructor
      · rintro ⟨c, hc, rfl⟩
        exact ⟨c, FractionalIdeal.mem_coeIdeal_of_mem _ hc, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨c, hc, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
        exact ⟨c, hc, rfl⟩)
    (by rw [← e2, ← e3]; exact h1) M _ _ (by rw [← e2, TaylorLogMetric.liftM, dif_pos h2]) (by rw [← e3, TaylorLogMetric.liftM, dif_pos h3]) L hL
  refine Eq.trans ?_ key
  congr 1
  refine (Fintype.sum_equiv (RingHom.equivRatAlgHom M ℂ) _ _ fun s => ?_).symm
  obtain ⟨f2, f3, -, fa, -, fu, -⟩ := GlobalTheory.T.latticeInvariants_periodPair_dictionary (L s) (L s).lattice.toAddSubgroup fun _ => Iff.rfl
  have hs : g2 (lamConj M (RingHom.equivRatAlgHom M ℂ s) (lamOf D cc δ)) = s (TaylorLogMetric.liftM M (g2 (lamOf D cc δ))) ∧
      g3 (lamConj M (RingHom.equivRatAlgHom M ℂ s) (lamOf D cc δ)) = s (TaylorLogMetric.liftM M (g3 (lamOf D cc δ))) :=
    Classical.epsilon_spec (p := fun Λ' : AddSubgroup ℂ => g2 Λ' = s (TaylorLogMetric.liftM M (g2 (lamOf D cc δ))) ∧
      g3 Λ' = s (TaylorLogMetric.liftM M (g3 (lamOf D cc δ)))) ⟨_, f2.trans (hL s).1, f3.trans (hL s).2⟩
  rw [fu _ (hs.1.trans (f2.trans (hL s).1).symm) (hs.2.trans (f3.trans (hL s).2).symm), fa,
    latticeArea_eq_abs_im_mul_conj]

end GlobalTheory.PeriodMean
