import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BndIUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentIdealRat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedRankinSelbergLocalFactor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsStdInvAndTrivialAndNontrivial
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitOrInertOfUnramified
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnramifiedCharCompUnitsMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableMulIntInd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EnlHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedWhittakerSphericalSpanStatement
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

namespace GlobalTheory.CompanionTheory.ThetaBound

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components.

Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.
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
Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem one_le_norm_sqrtQ : 1 ≤ ‖sqrtQ F‖ := by
  have h1 : (1 : ℝ) ≤ (qF F : ℝ) := by exact_mod_cast (qF_pos (F := F))
  have h2 : ‖sqrtQ F‖ = Real.sqrt (qF F : ℝ) := by
    simp [sqrtQ, Real.coe_sqrt]
  rw [h2]
  exact Real.one_le_sqrt.2 h1

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem norm_monomialChar_const (z : Fin 2 → ℂˣ) (hz : ∀ j, ‖((z j : ℂˣ) : ℂ)‖ = 1) (n : ℤ) :
    ‖monomialChar (fun _ : Fin 2 => n) z‖ = 1 := by
  simp [monomialChar, Fin.prod_univ_two, hz, Units.val_zpow_eq_zpow_val]

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Apply the first step, then apply the next step to every resulting obligation.

Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Apply the first step, then apply the next step to every resulting obligation.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Chain the equalities or inequalities of the calculation.

A detailed English derivation is pending.
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
Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Treat this case separately. Treat this case separately.

Treat this case separately. A detailed English derivation is pending.
-/
theorem translate_mem {G : Type} [Group G] (f W : G → ℂ)
    (hW : W ∈ Submodule.span ℂ {u : G → ℂ | ∃ h : G, u = fun g => f (g * h)}) (h₀ : G) :
    (fun g => W (g * h₀)) ∈ Submodule.span ℂ {u : G → ℂ | ∃ h : G, u = fun g => f (g * h)} := by
  induction hW using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    exact Submodule.subset_span ⟨h₀ * h, by funext g; simp only [mul_assoc]⟩
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx => exact Submodule.smul_mem _ a hx

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
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
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isUnit1_localChar {K : Type} [Field K] [NumberField K] (c : HeckeCharacter K) (w : PlK K) :
    IsUnit1 (localChar c w) := by
  refine ⟨GroundTheory.Automorphic.GodementSection.continuous_localChar c w, fun x => ?_⟩
  rw [GroundTheory.Automorphic.GodementSection.coe_localChar]
  exact Circle.norm_coe _

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.
-/
theorem isUnit1_cAt {K : Type} [Field K] [NumberField K] (c : HeckeCharacter K) (v : Pl) (w : PlK K)
    [w.asIdeal.LiesOver v.asIdeal] : IsUnit1 (cAt c v w) := by
  have hU := isUnit1_localChar c w
  refine ⟨hU.1.comp (Continuous.units_map _ (continuous_adicCompletionMap v w)), fun x => hU.2 _⟩

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem exists_bad (K : Type) [Field K] [NumberField K] (hd : Module.finrank ℚ K = 2)
    (c : HeckeCharacter K) : ∃ Bd : Finset Pl, ∀ v ∉ Bd, Ad3.K.QuadraticBaseChangeGL3.Th.Unr c v := by
  classical
  have hB : ({w : PlK K | w.asIdeal ∣ c.conductor}).Finite := Ideal.finite_factors c.conductor_ne_bot
  exact GlobalTheory.CompanionTheory.BaseChangeData.enl_holds K hd c hB.toFinset
    (fun w hw => (c.isUnramifiedChar_localChar_iff w).2 (by simpa using hw))

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem eq_sph_of_mem {v : Pl} (W' : GL (Fin 2) (Qv v) → ℂ) (hs : SphN W') (y : Fin 2 → ℂˣ)
    (hm : W' ∈ Submodule.span ℂ {f : GL (Fin 2) (Qv v) → ℂ | ∃ h : GL (Fin 2) (Qv v),
      f = fun g => Spherical.sphericalWhittaker (Circle.coeHom.compAddChar (GP.psiF v)⁻¹) y (g * h)})
    (g : GL (Fin 2) (Qv v)) :
    W' g = Spherical.sphericalWhittaker (Circle.coeHom.compAddChar (GP.psiF v)⁻¹) y g := by
  have hψ : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.StdCharQ.stdChar v
  have hχ : IsStd (GP.psiF v)⁻¹ := (GlobalTheory.CompanionTheory.StdAddChar.isStd_inv_and_trivial_and_nontrivial (Qv v) _ hψ).1
  obtain ⟨-, h1, h2⟩ := GlobalTheory.CompanionTheory.StdAddChar.isStd_inv_and_trivial_and_nontrivial (Qv v) _ hχ
  have := GlobalTheory.T.unramified_whittaker_spherical_span (Qv v) 2 _ h1 h2 y W' hm (fun g k hk => hs.1 k hk g) g
  rwa [hs.2, one_mul] at this

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

Separate the alternatives or extract the components of the hypothesis. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem exists_params {K : Type} [Field K] [NumberField K] (hd : Module.finrank ℚ K = 2)
    (c : HeckeCharacter K) (v : Pl) (hw : Ad3.K.QuadraticBaseChangeGL3.Th.Unr c v)
    (W' : GL (Fin 2) (Qv v) → ℂ) (e : ℂ) (hth : InThE c v W' e) :
    ∃ y : Fin 2 → ℂˣ, (∀ j, ‖((y j : ℂˣ) : ℂ)‖ = 1) ∧
      W' ∈ Submodule.span ℂ {f : GL (Fin 2) (Qv v) → ℂ | ∃ h : GL (Fin 2) (Qv v),
        f = fun g => Spherical.sphericalWhittaker (Circle.coeHom.compAddChar (GP.psiF v)⁻¹) y (g * h)} := by
  have hψ : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.StdCharQ.stdChar v
  have hχ : IsStd (GP.psiF v)⁻¹ := (GlobalTheory.CompanionTheory.StdAddChar.isStd_inv_and_trivial_and_nontrivial (Qv v) _ hψ).1
  rcases hth with ⟨w₁, w₂, i₁, i₂, hne, hW, -⟩ | ⟨w, i, hu, σ, η, hσ, hη, hW, -⟩
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
    · refine (Submodule.span_le.2 ?_) hW
      rintro _ ⟨Φ, hlc, hcs, h₀, rfl⟩
      exact translate_mem (fun g => _) _ (GlobalTheory.T.compact_whittaker_mem_spherical_span (Qv v) _ hχ _ _ u₁ u₂ r₁ r₂ Φ hlc hcs) h₀
  · haveI := i
    rcases GlobalTheory.CompanionTheory.QuadPlace.split_or_inert_of_unramified K hd v (fun w _ => (hw w).2) with
      ⟨a, b, ha, hb, hab⟩ | ⟨w', hw', -, hf, hord⟩
    · exact absurd ((hu a ha).trans (hu b hb).symm) hab
    · obtain rfl : w' = w := hu w' hw'
      haveI : FiniteDimensional (Qv v) (Kv K w') := Module.finite_of_finrank_pos (by omega)
      have hres : residueCard (Kv K w') = residueCard (Qv v) ^ 2 := GlobalTheory.CompanionTheory.NormGauss.card_E hf hord
      have hU := isUnit1_localChar c w'
      obtain ⟨b, hb2, hbn⟩ := exists_sqrt_unit
        (localChar c w' (Units.map (algebraMap (Qv v) (Kv K w')).toMonoidHom (unifUnit (Qv v)))) (hU.2 _)
      refine ⟨![b, -b], fun j => ?_, ?_⟩
      · fin_cases j
        · exact hbn
        · simpa using hbn
      · refine (Submodule.span_le.2 ?_) hW
        rintro _ ⟨Φ, hΦ, h₀, rfl⟩
        exact translate_mem (fun g => _) _ (GlobalTheory.T.unramified_quadratic_residue_card (Qv v) (Kv K w') hf
          (continuous_adicCompletionMap v w') hres _ hχ σ hσ η hη _ hU (hw w').1 b hb2 Φ hΦ) h₀

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem main : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
    ∀ c : HeckeCharacter K, ∃ Bd : Finset Pl, ∀ v ∉ Bd,
    ∀ (W' : GL (Fin 2) (Qv v) → ℂ) (e : ℂ), InThE c v W' e → SphN W' → ∀ (m : ℕ) (n : ℤ),
      ‖W' (d2 (unifUnit (Qv v) ^ ((m : ℤ) + n)) (unifUnit (Qv v) ^ n))‖ ≤ (m : ℝ) + 1 := by
  intro K _ _ hd c
  obtain ⟨Bd, hBd⟩ := exists_bad K hd c
  refine ⟨Bd, fun v hv W' e hth hsph m n => ?_⟩
  obtain ⟨y, hy, hm⟩ := exists_params hd c v (hBd v hv) W' e hth
  have hψ : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.StdCharQ.stdChar v
  have hχ : IsStd (GP.psiF v)⁻¹ := (GlobalTheory.CompanionTheory.StdAddChar.isStd_inv_and_trivial_and_nontrivial (Qv v) _ hψ).1
  obtain ⟨-, h1, -⟩ := GlobalTheory.CompanionTheory.StdAddChar.isStd_inv_and_trivial_and_nontrivial (Qv v) _ hχ
  rw [eq_sph_of_mem W' hsph y hm]
  exact norm_spherical_whittaker_diag_le h1 y hy m n

end GlobalTheory.CompanionTheory.ThetaBound
