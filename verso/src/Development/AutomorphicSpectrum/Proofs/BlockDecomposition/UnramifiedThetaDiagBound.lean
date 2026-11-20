import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.CasselmanShalikaStandardVector
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BndIUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentIdealRat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedRankinSelbergLocalFactor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsStdInvAndTrivialAndNontrivial
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitOrInertOfUnramified
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnramifiedCharCompUnitsMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableMulIntInd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalSplitOfPointwise
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrdEqZeroOfModulusEqOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedWhittakerSphericalSpan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactWhittakerMemSphericalSpanStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticResidueCardStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa

noncomputable section

namespace GlobalTheory.CompanionTheory.StdThetaBound

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/- English proof (translation)
Take `⟨u, hu⟩` from `GlobalTheory.CompanionTheory.LocalUnramified.exists_unit_eq_uniformizer_zpow_ord_mul F a`. Take `⟨u', hu'⟩` from `GlobalTheory.CompanionTheory.LocalUnramified.exists_unit_eq_uniformizer_zpow_ord_mul F b`. Use `⟨GLnLocal.integralGLHom F 2 (d2 u u'), ⟨_, rfl⟩, ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`.

Rewrite using `[Units.val_mul, coe_torusPow]`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Simplify using `[d2, GLnLocal.integralGLHom, Matrix.diagonal_mul, ← hu, ← hu']`.
-/
theorem partialYAtZero_eq (a b : Fˣ) : ∃ k ∈ integralGL F 2,
    (d2 a b : GL (Fin 2) F) = torusPow F 2 ![ord (a : F), ord (b : F)] * k := by
  obtain ⟨u, hu⟩ := GlobalTheory.CompanionTheory.LocalUnramified.exists_unit_eq_uniformizer_zpow_ord_mul F a
  obtain ⟨u', hu'⟩ := GlobalTheory.CompanionTheory.LocalUnramified.exists_unit_eq_uniformizer_zpow_ord_mul F b
  refine ⟨GLnLocal.integralGLHom F 2 (d2 u u'), ⟨_, rfl⟩, ?_⟩
  apply Units.ext
  ext i j
  rw [Units.val_mul, coe_torusPow]
  fin_cases i <;> fin_cases j <;>
    simp [d2, GLnLocal.integralGLHom, Matrix.diagonal_mul, ← hu, ← hu']

/- English proof (translation)
Establish `h1 : (1 : ℝ) ≤ (qF F : ℝ)` using `by exact_mod_cast (qF_pos (F := F))`. Establish `h2 : ‖sqrtQ F‖ = Real.sqrt (qF F : ℝ)`. Simplify using `[sqrtQ, Real.coe_sqrt]`. Rewrite using `[h2]`. Conclude with `Real.one_le_sqrt.2 h1`.
-/
theorem one_le_norm_sqrtQ : 1 ≤ ‖sqrtQ F‖ := by
  have h1 : (1 : ℝ) ≤ (qF F : ℝ) := by exact_mod_cast (qF_pos (F := F))
  have h2 : ‖sqrtQ F‖ = Real.sqrt (qF F : ℝ) := by
    simp [sqrtQ, Real.coe_sqrt]
  rw [h2]
  exact Real.one_le_sqrt.2 h1

/- English proof (translation)
Simplify using `[monomialChar, Fin.prod_univ_two, hz, Units.val_zpow_eq_zpow_val]`.
-/
theorem norm_monomialChar_const (z : Fin 2 → ℂˣ) (hz : ∀ j, ‖((z j : ℂˣ) : ℂ)‖ = 1) (n : ℤ) :
    ‖monomialChar (fun _ : Fin 2 => n) z‖ = 1 := by
  simp [monomialChar, Fin.prod_univ_two, hz, Units.val_zpow_eq_zpow_val]

/- English proof (translation)
Take `⟨k, hk, hd⟩` from `partialYAtZero_eq (unifUnit F ^ ((m : ℤ) + n)) (unifUnit F ^ n)`. Rewrite using `[hd, sphericalWhittaker_mul_right hψ₀ _ _ hk, ord_unifUnit_zpow, ord_unifUnit_zpow, sphericalWhittaker_torusPow hψ₀]`. Establish `hanti : Antitone (![(m : ℤ) + n, n] : Fin 2 → ℤ)`. Introduce `i j hij`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp_all`.

Establish `hr : rhoPair (![(m : ℤ) + n, n] : Fin 2 → ℤ) = m`. Simplify using `[rhoPair, Fin.sum_univ_two]`. Establish `hl : (![(m : ℤ) + n, n] : Fin 2 → ℤ) = ![(m : ℤ), 0] + fun _ => n`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp`.

Rewrite using `[if_pos hanti, halfModulus_eq, hr, hl, schur_add_const, map_mul, GlobalTheory.CompanionTheory.RSUnram.evalAt_schur_row, monomial, evalAt_single, one_mul, norm_mul, norm_mul, norm_monomialChar_const z hz, one_mul]`. Establish `h1 : ‖sqrtQ F ^ (-(m : ℤ))‖ ≤ 1`. Rewrite using `[norm_zpow, _root_.zpow_neg, zpow_natCast]`. Conclude with `inv_le_one_of_one_le₀ (one_le_pow₀ one_le_norm_sqrtQ)`. Establish `h2` using `GlobalTheory.CompanionTheory.RSUnram.norm_hs_le (hz 0) (hz 1) m`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_spherical_whittaker_diag_le {ψ₀ : AddChar F ℂ} (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1) (z : Fin 2 → ℂˣ)
    (hz : ∀ j, ‖((z j : ℂˣ) : ℂ)‖ = 1) (m : ℕ) (n : ℤ) :
    ‖sphericalWhittaker ψ₀ z (d2 (unifUnit F ^ ((m : ℤ) + n)) (unifUnit F ^ n))‖ ≤ (m : ℝ) + 1 := by
  obtain ⟨k, hk, hd⟩ := partialYAtZero_eq (unifUnit F ^ ((m : ℤ) + n)) (unifUnit F ^ n)
  rw [hd, sphericalWhittaker_mul_right hψ₀ _ _ hk, ord_unifUnit_zpow, ord_unifUnit_zpow,
    sphericalWhittaker_torusPow hψ₀]
  have hanti : Antitone (![(m : ℤ) + n, n] : Fin 2 → ℤ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hr : rhoPair (![(m : ℤ) + n, n] : Fin 2 → ℤ) = m := by
    simp [rhoPair, Fin.sum_univ_two]
  have hl : (![(m : ℤ) + n, n] : Fin 2 → ℤ) = ![(m : ℤ), 0] + fun _ => n := by
    funext i
    fin_cases i <;> simp
  rw [if_pos hanti, halfModulus_eq, hr, hl, schur_add_const, map_mul,
    GlobalTheory.CompanionTheory.RSUnram.evalAt_schur_row, monomial, evalAt_single, one_mul, norm_mul, norm_mul,
    norm_monomialChar_const z hz, one_mul]
  have h1 : ‖sqrtQ F ^ (-(m : ℤ))‖ ≤ 1 := by
    rw [norm_zpow, _root_.zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ one_le_norm_sqrtQ)
  have h2 := GlobalTheory.CompanionTheory.RSUnram.norm_hs_le (hz 0) (hz 1) m
  calc _ ≤ 1 * ((m : ℝ) + 1) := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

end Local

/- English proof (translation)
Take `⟨z, hz⟩` from `IsAlgClosed.exists_pow_nat_eq (a : ℂ) (n := 2) (by norm_num)`. Establish `hz0 : z ≠ 0`. Introduce and unpack `rfl`. Conclude with `a.ne_zero (by simpa using hz.symm)`. Use `⟨Units.mk0 z hz0, Units.ext (by simpa using hz), ?_⟩` and prove the remaining obligations.

Establish `h2 : ‖z‖ ^ 2 = 1` using `by rw [← norm_pow, hz, ha]`. Establish `h0 : 0 ≤ ‖z‖` using `norm_nonneg z`. Simplify using `using (pow_eq_one_iff_of_nonneg h0 (by norm_num)).1 h2`.
-/
theorem exists_sqrt_unit (a : ℂˣ) (ha : ‖(a : ℂ)‖ = 1) : ∃ b : ℂˣ, b ^ 2 = a ∧ ‖(b : ℂ)‖ = 1 := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (a : ℂ) (n := 2) (by norm_num)
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact a.ne_zero (by simpa using hz.symm)
  refine ⟨Units.mk0 z hz0, Units.ext (by simpa using hz), ?_⟩
  have h2 : ‖z‖ ^ 2 = 1 := by rw [← norm_pow, hz, ha]
  have h0 : 0 ≤ ‖z‖ := norm_nonneg z
  simpa using (pow_eq_one_iff_of_nonneg h0 (by norm_num)).1 h2

/- English proof (translation)
Use `⟨GroundTheory.Automorphic.GodementSection.continuous_localChar c w, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[GroundTheory.Automorphic.GodementSection.coe_localChar]`. Conclude with `Circle.norm_coe _`.
-/
theorem isUnit1_localChar {K : Type} [Field K] [NumberField K] (c : HeckeCharacter K) (w : PlK K) :
    IsUnit1 (localChar c w) := by
  refine ⟨GroundTheory.Automorphic.GodementSection.continuous_localChar c w, fun x => ?_⟩
  rw [GroundTheory.Automorphic.GodementSection.coe_localChar]
  exact Circle.norm_coe _

/- English proof (translation)
Establish `hU` using `isUnit1_localChar c w`. Use `⟨hU.1.comp (Continuous.units_map _ (continuous_adicCompletionMap v w)), fun x => hU.2 _⟩` and prove the remaining obligations.
-/
theorem isUnit1_cAt {K : Type} [Field K] [NumberField K] (c : HeckeCharacter K) (v : Pl) (w : PlK K)
    [w.asIdeal.LiesOver v.asIdeal] : IsUnit1 (cAt c v w) := by
  have hU := isUnit1_localChar c w
  refine ⟨hU.1.comp (Continuous.units_map _ (continuous_adicCompletionMap v w)), fun x => hU.2 _⟩

/- English proof (translation)
Use function extensionality and compare the values at `x`. Distinguish the cases in `h1 : x.1 ∈ 𝒪[F]`. Distinguish the cases in `h2 : x.2 ∈ 𝒪[F]`. Rewrite using `[Set.indicator_of_mem (show x ∈ {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} from ⟨h1, h2⟩)]`. Simplify using `[GlobalTheory.CompanionTheory.SphTheta.phiS, GlobalTheory.CompanionTheory.SphTheta.intInd_of_mem h1, GlobalTheory.CompanionTheory.SphTheta.intInd_of_mem h2]`.

Rewrite using `[Set.indicator_of_notMem (fun h => h2 h.2)]`. Simplify using `[GlobalTheory.CompanionTheory.SphTheta.phiS, GlobalTheory.CompanionTheory.SphTheta.intInd_of_notMem h2]`. Rewrite using `[Set.indicator_of_notMem (fun h => h1 h.1)]`. Simplify using `[GlobalTheory.CompanionTheory.SphTheta.phiS, GlobalTheory.CompanionTheory.SphTheta.intInd_of_notMem h1]`.
-/
theorem indicator_eq_phiS {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] :
    Set.indicator {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} (1 : F × F → ℂ) =
      GlobalTheory.CompanionTheory.SphTheta.phiS := by
  funext x
  by_cases h1 : x.1 ∈ 𝒪[F]
  · by_cases h2 : x.2 ∈ 𝒪[F]
    · rw [Set.indicator_of_mem (show x ∈ {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} from ⟨h1, h2⟩)]
      simp [GlobalTheory.CompanionTheory.SphTheta.phiS, GlobalTheory.CompanionTheory.SphTheta.intInd_of_mem h1,
        GlobalTheory.CompanionTheory.SphTheta.intInd_of_mem h2]
    · rw [Set.indicator_of_notMem (fun h => h2 h.2)]
      simp [GlobalTheory.CompanionTheory.SphTheta.phiS, GlobalTheory.CompanionTheory.SphTheta.intInd_of_notMem h2]
  · rw [Set.indicator_of_notMem (fun h => h1 h.1)]
    simp [GlobalTheory.CompanionTheory.SphTheta.phiS, GlobalTheory.CompanionTheory.SphTheta.intInd_of_notMem h1]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Distinguish the cases in `h : x ∈ 𝒪[E]`. Rewrite using `[Set.indicator_of_mem (show x ∈ {x : E | x ∈ 𝒪[E]} from h)]`. Simplify using `[GlobalTheory.CompanionTheory.SphTheta.intInd, h]`. Rewrite using `[Set.indicator_of_notMem (show x ∉ {x : E | x ∈ 𝒪[E]} from h)]`.

Simplify using `[GlobalTheory.CompanionTheory.SphTheta.intInd, h]`.
-/
theorem indicator_eq_intInd {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] :
    Set.indicator {x : E | x ∈ 𝒪[E]} (1 : E → ℂ) = GlobalTheory.CompanionTheory.SphTheta.intInd := by
  funext x
  by_cases h : x ∈ 𝒪[E]
  · rw [Set.indicator_of_mem (show x ∈ {x : E | x ∈ 𝒪[E]} from h)]
    simp [GlobalTheory.CompanionTheory.SphTheta.intInd, h]
  · rw [Set.indicator_of_notMem (show x ∉ {x : E | x ∈ 𝒪[E]} from h)]
    simp [GlobalTheory.CompanionTheory.SphTheta.intInd, h]

/- English proof (translation)
Establish `hψ : IsStd (GP.psiF v)` using `GlobalTheory.CompanionTheory.StdCharQ.stdChar v`. Establish `hχ : IsStd (GP.psiF v)⁻¹` using `(GlobalTheory.CompanionTheory.StdAddChar.isStd_inv_and_trivial_and_nontrivial (Qv v) _ hψ).1`. Take `⟨-, h1, h2⟩` from `GlobalTheory.CompanionTheory.StdAddChar.isStd_inv_and_trivial_and_nontrivial (Qv v) _ hχ`. Use `GlobalTheory.CompanionTheory.SphericalSpan.eq_mul_sphericalWhittaker (Qv v) 2 _ h1 h2 y W' hm (fun g k hk => hs.1 k hk g) g` as an intermediate fact. Rewrite `this` using `[hs.2, one_mul]`. Then use the resulting hypothesis.
-/
theorem eq_sph_of_mem {v : Pl} (W' : GL (Fin 2) (Qv v) → ℂ) (hs : SphN W') (y : Fin 2 → ℂˣ)
    (hm : W' ∈ Submodule.span ℂ {f : GL (Fin 2) (Qv v) → ℂ | ∃ h : GL (Fin 2) (Qv v),
      f = fun g => Spherical.sphericalWhittaker (Circle.coeHom.compAddChar (GP.psiF v)⁻¹) y (g * h)})
    (g : GL (Fin 2) (Qv v)) :
    W' g = Spherical.sphericalWhittaker (Circle.coeHom.compAddChar (GP.psiF v)⁻¹) y g := by
  have hψ : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.StdCharQ.stdChar v
  have hχ : IsStd (GP.psiF v)⁻¹ :=
    (GlobalTheory.CompanionTheory.StdAddChar.isStd_inv_and_trivial_and_nontrivial (Qv v) _ hψ).1
  obtain ⟨-, h1, h2⟩ := GlobalTheory.CompanionTheory.StdAddChar.isStd_inv_and_trivial_and_nontrivial (Qv v) _ hχ
  have := GlobalTheory.CompanionTheory.SphericalSpan.eq_mul_sphericalWhittaker (Qv v) 2 _ h1 h2 y W' hm
    (fun g k hk => hs.1 k hk g) g
  rwa [hs.2, one_mul] at this

/- English proof (translation)
Establish `hψ : IsStd (GP.psiF v)` using `GlobalTheory.CompanionTheory.StdCharQ.stdChar v`. Establish `hχ : IsStd (GP.psiF v)⁻¹` using `(GlobalTheory.CompanionTheory.StdAddChar.isStd_inv_and_trivial_and_nontrivial (Qv v) _ hψ).1`. Break down `hth with ⟨w₁, w₂, i₁, i₂, hne, rfl⟩ | ⟨w, i, hu, σ, η, hσ, hη, rfl⟩` into its components or cases. Use `haveI := i₁ haveI := i₂`. Establish `u₁` using `isUnit1_cAt c v w₁`.

Establish `u₂` using `isUnit1_cAt c v w₂`. Establish `r₁ : IsUnramifiedChar (cAt c v w₁)` using `GlobalTheory.CompanionTheory.SphTheta.isUnramifiedChar_comp_unitsMap (Qv v) (Kv K w₁) (localChar c w₁) (hw w₁).1`. Establish `r₂ : IsUnramifiedChar (cAt c v w₂)` using `GlobalTheory.CompanionTheory.SphTheta.isUnramifiedChar_comp_unitsMap (Qv v) (Kv K w₂) (localChar c w₂) (hw w₂).1`. Use `⟨![cAt c v w₁ (unifUnit (Qv v)), cAt c v w₂ (unifUnit (Qv v))], fun j => ?_, ?_⟩` and prove the remaining obligations. Use `fin_cases j`.

Conclude with `u₁.2 _`. Conclude with `u₂.2 _`. Rewrite using `[indicator_eq_phiS]`. Conclude with `GlobalTheory.T.compact_whittaker_mem_spherical_span (Qv v) _ hχ _ _ u₁ u₂ r₁ r₂ _ GlobalTheory.CompanionTheory.SphTheta.isLocallyConstant_phiS GlobalTheory.CompanionTheory.SphTheta.hasCompactSupport_phiS`. Use `haveI := i`.

Break down `GlobalTheory.CompanionTheory.QuadPlace.split_or_inert_of_unramified K hd v (fun w _ => (hw w).2) with ⟨a, b, ha, hb, hab⟩ | ⟨w', hw', -, hf, hord⟩` into its components or cases. Conclude with `absurd ((hu a ha).trans (hu b hb).symm) hab`. Take `rfl : w' = w` from `hu w' hw' haveI : FiniteDimensional (Qv v) (Kv K w') := Module.finite_of_finrank_pos (by omega) haveI : Fact (Module.finrank (Qv v) (Kv K w') = 2) := ⟨hf⟩`. Establish `hres : residueCard (Kv K w') = residueCard (Qv v) ^ 2` using `GlobalTheory.CompanionTheory.NormGauss.card_E hf hord`. Establish `hU` using `isUnit1_localChar c w'`.

Take `⟨b, hb2, hbn⟩` from `exists_sqrt_unit (localChar c w' (Units.map (algebraMap (Qv v) (Kv K w')).toMonoidHom (unifUnit (Qv v)))) (hU.2 _)`. Use `⟨![b, -b], fun j => ?_, ?_⟩` and prove the remaining obligations. Use `fin_cases j`. Conclude with `hbn`. Simplify using `using hbn`.

Rewrite using `[indicator_eq_intInd]`. Conclude with `GlobalTheory.T.unramified_quadratic_residue_card (Qv v) (Kv K w') hf (continuous_adicCompletionMap v w') hres _ hχ σ hσ η hη _ hU (hw w').1 b hb2 _ (GlobalTheory.CompanionTheory.SphTheta.InertAsm.intInd_mem_SBc _ (hw w').1)`.
-/
theorem exists_params {K : Type} [Field K] [NumberField K] (hd : Module.finrank ℚ K = 2)
    (c : HeckeCharacter K) (v : Pl) (hw : Ad3.K.QuadraticBaseChangeGL3.Th.Unr c v)
    (W' : GL (Fin 2) (Qv v) → ℂ) (hth : Ad3.K.QuadraticBaseChangeGL3.Th.StdTh c v W') :
    ∃ y : Fin 2 → ℂˣ, (∀ j, ‖((y j : ℂˣ) : ℂ)‖ = 1) ∧
      W' ∈ Submodule.span ℂ {f : GL (Fin 2) (Qv v) → ℂ | ∃ h : GL (Fin 2) (Qv v),
        f = fun g => Spherical.sphericalWhittaker (Circle.coeHom.compAddChar (GP.psiF v)⁻¹) y (g * h)} := by
  have hψ : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.StdCharQ.stdChar v
  have hχ : IsStd (GP.psiF v)⁻¹ :=
    (GlobalTheory.CompanionTheory.StdAddChar.isStd_inv_and_trivial_and_nontrivial (Qv v) _ hψ).1
  rcases hth with ⟨w₁, w₂, i₁, i₂, hne, rfl⟩ | ⟨w, i, hu, σ, η, hσ, hη, rfl⟩
  · haveI := i₁
    haveI := i₂
    have u₁ := isUnit1_cAt c v w₁
    have u₂ := isUnit1_cAt c v w₂
    have r₁ : IsUnramifiedChar (cAt c v w₁) :=
      GlobalTheory.CompanionTheory.SphTheta.isUnramifiedChar_comp_unitsMap (Qv v) (Kv K w₁) (localChar c w₁) (hw w₁).1
    have r₂ : IsUnramifiedChar (cAt c v w₂) :=
      GlobalTheory.CompanionTheory.SphTheta.isUnramifiedChar_comp_unitsMap (Qv v) (Kv K w₂) (localChar c w₂) (hw w₂).1
    refine ⟨![cAt c v w₁ (unifUnit (Qv v)), cAt c v w₂ (unifUnit (Qv v))], fun j => ?_, ?_⟩
    · fin_cases j
      · exact u₁.2 _
      · exact u₂.2 _
    · rw [indicator_eq_phiS]
      exact GlobalTheory.T.compact_whittaker_mem_spherical_span (Qv v) _ hχ _ _ u₁ u₂ r₁ r₂ _ GlobalTheory.CompanionTheory.SphTheta.isLocallyConstant_phiS
        GlobalTheory.CompanionTheory.SphTheta.hasCompactSupport_phiS
  · haveI := i
    rcases GlobalTheory.CompanionTheory.QuadPlace.split_or_inert_of_unramified K hd v (fun w _ => (hw w).2) with
      ⟨a, b, ha, hb, hab⟩ | ⟨w', hw', -, hf, hord⟩
    · exact absurd ((hu a ha).trans (hu b hb).symm) hab
    · obtain rfl : w' = w := hu w' hw'
      haveI : FiniteDimensional (Qv v) (Kv K w') := Module.finite_of_finrank_pos (by omega)
      haveI : Fact (Module.finrank (Qv v) (Kv K w') = 2) := ⟨hf⟩
      have hres : residueCard (Kv K w') = residueCard (Qv v) ^ 2 := GlobalTheory.CompanionTheory.NormGauss.card_E hf hord
      have hU := isUnit1_localChar c w'
      obtain ⟨b, hb2, hbn⟩ := exists_sqrt_unit
        (localChar c w' (Units.map (algebraMap (Qv v) (Kv K w')).toMonoidHom (unifUnit (Qv v)))) (hU.2 _)
      refine ⟨![b, -b], fun j => ?_, ?_⟩
      · fin_cases j
        · exact hbn
        · simpa using hbn
      · rw [indicator_eq_intInd]
        exact GlobalTheory.T.unramified_quadratic_residue_card (Qv v) (Kv K w') hf (continuous_adicCompletionMap v w') hres _ hχ σ hσ
          η hη _ hU (hw w').1 b hb2 _ (GlobalTheory.CompanionTheory.SphTheta.InertAsm.intInd_mem_SBc _ (hw w').1)

/- English proof (translation)
Introduce `K _ _ hd c v hw W' hth hsph m n`. Take `⟨y, hy, hm⟩` from `exists_params hd c v hw W' hth`. Establish `hψ : IsStd (GP.psiF v)` using `GlobalTheory.CompanionTheory.StdCharQ.stdChar v`. Establish `hχ : IsStd (GP.psiF v)⁻¹` using `(GlobalTheory.CompanionTheory.StdAddChar.isStd_inv_and_trivial_and_nontrivial (Qv v) _ hψ).1`. Take `⟨-, h1, -⟩` from `GlobalTheory.CompanionTheory.StdAddChar.isStd_inv_and_trivial_and_nontrivial (Qv v) _ hχ`.

Rewrite using `[eq_sph_of_mem W' hsph y hm]`. Conclude with `norm_spherical_whittaker_diag_le h1 y hy m n`.
-/
theorem main : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
    ∀ (c : HeckeCharacter K) (v : Pl), Ad3.K.QuadraticBaseChangeGL3.Th.Unr c v →
    ∀ W' : GL (Fin 2) (Qv v) → ℂ, Ad3.K.QuadraticBaseChangeGL3.Th.StdTh c v W' → SphN W' → ∀ (m : ℕ) (n : ℤ),
      ‖W' (d2 (unifUnit (Qv v) ^ ((m : ℤ) + n)) (unifUnit (Qv v) ^ n))‖ ≤ (m : ℝ) + 1 := by
  intro K _ _ hd c v hw W' hth hsph m n
  obtain ⟨y, hy, hm⟩ := exists_params hd c v hw W' hth
  have hψ : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.StdCharQ.stdChar v
  have hχ : IsStd (GP.psiF v)⁻¹ :=
    (GlobalTheory.CompanionTheory.StdAddChar.isStd_inv_and_trivial_and_nontrivial (Qv v) _ hψ).1
  obtain ⟨-, h1, -⟩ := GlobalTheory.CompanionTheory.StdAddChar.isStd_inv_and_trivial_and_nontrivial (Qv v) _ hχ
  rw [eq_sph_of_mem W' hsph y hm]
  exact norm_spherical_whittaker_diag_le h1 y hy m n

end GlobalTheory.CompanionTheory.StdThetaBound
