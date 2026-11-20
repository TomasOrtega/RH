import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.CasselmanShalikaStandardVector
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BndIUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntInd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusEntryLeMRow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableIntIndMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalSplitOfPointwise
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsQuadCharUnramified
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsStdChEOfOrdUnif
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLFactorHalfNeZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticUniformizerOrder
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralSubst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrdEqZeroOfModulusEqOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitOrInertOfUnramified
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnramifiedCharCompUnitsMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AddCharConductorInv
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
open GlobalTheory.CompanionTheory.SphTheta

noncomputable section

namespace GlobalTheory.CompanionTheory.StdSph

section Ind

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Distinguish the cases in `h : x ∈ 𝒪[F]`. Rewrite using `[Set.indicator_of_mem (show x ∈ {x : F | x ∈ 𝒪[F]} from h), intInd_of_mem h]`. Simplify using the standard rewrite rules. Rewrite using `[Set.indicator_of_notMem (show x ∉ {x : F | x ∈ 𝒪[F]} from h), intInd_of_notMem h]`.
-/
theorem indicator_eq_intInd : Set.indicator {x : F | x ∈ 𝒪[F]} 1 = (intInd : F → ℂ) := by
  funext x
  by_cases h : x ∈ 𝒪[F]
  · rw [Set.indicator_of_mem (show x ∈ {x : F | x ∈ 𝒪[F]} from h), intInd_of_mem h]
    simp
  · rw [Set.indicator_of_notMem (show x ∉ {x : F | x ∈ 𝒪[F]} from h), intInd_of_notMem h]

/- English proof (translation)
Use function extensionality and compare the values at `z`. Distinguish the cases in `h1 : z.1 ∈ 𝒪[F]`. Distinguish the cases in `h2 : z.2 ∈ 𝒪[F]`. Rewrite using `[Set.indicator_of_mem (show z ∈ {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} from ⟨h1, h2⟩), phiS, intInd_of_mem h1, intInd_of_mem h2]`. Simplify using the standard rewrite rules.

Rewrite using `[Set.indicator_of_notMem (show z ∉ {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} from fun h => h2 h.2), phiS, intInd_of_notMem h2]`. Simplify using the standard rewrite rules. Rewrite using `[Set.indicator_of_notMem (show z ∉ {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} from fun h => h1 h.1), phiS, intInd_of_notMem h1]`. Simplify using the standard rewrite rules.
-/
theorem indicator_eq_phiS :
    Set.indicator {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} 1 = (phiS : F × F → ℂ) := by
  funext z
  by_cases h1 : z.1 ∈ 𝒪[F]
  · by_cases h2 : z.2 ∈ 𝒪[F]
    · rw [Set.indicator_of_mem (show z ∈ {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} from ⟨h1, h2⟩),
        phiS, intInd_of_mem h1, intInd_of_mem h2]
      simp
    · rw [Set.indicator_of_notMem (show z ∉ {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} from fun h => h2 h.2),
        phiS, intInd_of_notMem h2]
      simp
  · rw [Set.indicator_of_notMem (show z ∉ {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} from fun h => h1 h.1),
      phiS, intInd_of_notMem h1]
    simp

end Ind

/- English proof (translation)
Establish `H1` using `GlobalTheory.CompanionTheory.SphTheta.SplitRW.rW_phiS F χ hχ`. Establish `H2` using `GlobalTheory.CompanionTheory.SphTheta.RowIwasawa.iwasawa_lower_row F`. Establish `key : ∀ g : GL (Fin 2) F, GL2LocalData.WcS χ c₁ c₂ phiS g = ((c₁ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * mp (Matrix.GeneralLinearGroup.det g) (1 / 2) * ((((modulus (mRow g) : ℝ)⁻¹ : ℝ) : ℂ) * (χ (xRow g) : ℂ) * ∫ u, sphJ c₁ c₂ (g.val).det (mRow g) u ∂multHaar F)`. Introduce `g`. Unfold `GL2LocalData.WcS`.

Use `congr 1`. Rewrite using `[← integral_const_mul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Simplify using `only [H1 g u, sphJ]`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `k hk g`. Take `⟨hm, hD, hM, hx⟩` from `H2 g k hk`. Establish `hk1 : modulus (k.val).det = 1`. Use `(H2 1 k hk).2.1` as an intermediate fact.

Simplify using `using this`. Establish `hdet : Matrix.GeneralLinearGroup.det (g * k) = Matrix.GeneralLinearGroup.det g * Matrix.GeneralLinearGroup.det k` using `map_mul _ _ _`. Establish `hc : ((c₁ (Matrix.GeneralLinearGroup.det (g * k)) : ℂˣ) : ℂ) = ((c₁ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)`. Rewrite using `[hdet, map_mul, Units.val_mul, char_eq_one hc₁ (u := Matrix.GeneralLinearGroup.det k) hk1, mul_one]`. Establish `hmp : mp (Matrix.GeneralLinearGroup.det (g * k)) (1 / 2) = mp (Matrix.GeneralLinearGroup.det g) (1 / 2)`.

Unfold `mp`. Establish `: modulus ((Matrix.GeneralLinearGroup.det (g * k) : Fˣ) : F) = modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F)` using `hD`. Rewrite using `[this]`. Rewrite using `[key, key, hc, hmp, hM, sphJ_congr c₁ c₂ hD hM]`. Distinguish the cases in `hle : modulus (g.val).det ≤ modulus (mRow g) ^ 2`.

Establish `ht` using `hx hle`. Establish `h1 : χ (xRow (g * k) - xRow g) = 1`. Establish `h` using `isTrivialOn_addCharConductor hχ.1 hχ.2.1`. Rewrite `h` using `[hχ.2.2]`. Conclude with `h _ (mem_valBall_zero_iff.2 ht)`.

Establish `h2 : χ (xRow (g * k)) = χ (xRow g)`. Establish `e : xRow (g * k) = (xRow (g * k) - xRow g) + xRow g` using `by ring`. Rewrite using `[e, AddChar.map_add_eq_mul, h1, one_mul]`. Rewrite using `[h2]`. Establish `h0 : (fun u => sphJ c₁ c₂ (g.val).det (mRow g) u) = fun _ => 0`.

Use function extensionality and compare the values at `(sphJ_eq_zero c₁ c₂ hm hle)`. Simplify using `only [h0, integral_zero, mul_zero]`. Rewrite using `[key]`. Establish `hm1 : mRow (1 : GL (Fin 2) F) = 1`. Simplify using `[mRow]`.

Establish `hx1 : xRow (1 : GL (Fin 2) F) = 0`. Simplify using `[xRow]`. Establish `hJ : (fun u => sphJ c₁ c₂ ((1 : GL (Fin 2) F).val).det 1 u) = (unitFiltrationUnits F 0 : Set Fˣ).indicator (fun _ => (1 : ℂ))`. Use function extensionality and compare the values at `u`. Distinguish the cases in `hu : u ∈ (unitFiltrationUnits F 0 : Set Fˣ)`.

Establish `hu1 : modulus (u : F) = 1` using `mem_units_iff_modulus.1 hu`. Rewrite using `[Set.indicator_of_mem hu]`. Establish `e1 : ((c₂ u)⁻¹ : ℂˣ) = 1`. Establish `: c₂ u = 1` using `hc₂ (mem_units_iff_modulus.2 hu1)`. Rewrite using `[this, inv_one]`.

Unfold `sphJ`. Rewrite using `[e1, char_eq_one hc₁ hu1, intInd_of_mem, intInd_of_mem]`. Simplify using the standard rewrite rules. Rewrite using `[← modulus_le_one_iff]`. Simplify using `[modulus_mul, hu1]`.

Rewrite using `[← modulus_le_one_iff]`. Simplify using `[modulus_mul, modulus_inv, hu1]`. Rewrite using `[Set.indicator_of_notMem hu]`. Establish `hu1 : modulus (u : F) ≠ 1` using `fun h => hu (mem_units_iff_modulus.2 h)`. Unfold `sphJ`.

Break down `lt_or_gt_of_ne hu1 with h | h` into its components or cases. Rewrite using `[intInd_of_notMem (x := (1 * (u : F))⁻¹)]`. Simplify using the standard rewrite rules. Rewrite using `[← modulus_le_one_iff, one_mul, modulus_inv, not_le]`. Conclude with `(one_lt_inv₀ (modulus_pos u.ne_zero)).2 h`.

Rewrite using `[intInd_of_notMem (x := ((1 : GL (Fin 2) F).val).det * u / 1)]`. Simplify using the standard rewrite rules. Rewrite using `[← modulus_le_one_iff, not_le]`. Simplify using `using h`. Establish `hmeas : MeasurableSet (unitFiltrationUnits F 0 : Set Fˣ)`.

Conclude with `(isOpen_unitFiltrationUnits 0).measurableSet`. Establish `hint : ∫ u, sphJ c₁ c₂ ((1 : GL (Fin 2) F).val).det 1 u ∂multHaar F = 1`. Rewrite using `[hJ, integral_indicator_const _ hmeas]`. Simplify using `[Measure.real, multHaar_unitFiltrationUnits_zero]`. Rewrite using `[hm1, hx1, hint]`.

Simplify using `[mp]`.
-/
theorem split_sph (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle)
    (c₁ c₂ : Fˣ →* ℂˣ) (hχ : Ad3.IsStd χ) (hc₁ : IsUnramifiedChar c₁) (hc₂ : IsUnramifiedChar c₂) :
    SphN (GL2LocalData.WcS χ c₁ c₂ phiS) := by
  have H1 := GlobalTheory.CompanionTheory.SphTheta.SplitRW.rW_phiS F χ hχ
  have H2 := GlobalTheory.CompanionTheory.SphTheta.RowIwasawa.iwasawa_lower_row F
  have key : ∀ g : GL (Fin 2) F, GL2LocalData.WcS χ c₁ c₂ phiS g =
      ((c₁ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * mp (Matrix.GeneralLinearGroup.det g) (1 / 2) *
        ((((modulus (mRow g) : ℝ)⁻¹ : ℝ) : ℂ) * (χ (xRow g) : ℂ) *
          ∫ u, sphJ c₁ c₂ (g.val).det (mRow g) u ∂multHaar F) := by
    intro g
    unfold GL2LocalData.WcS
    congr 1
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [H1 g u, sphJ]
    ring
  refine ⟨?_, ?_⟩
  · intro k hk g
    obtain ⟨hm, hD, hM, hx⟩ := H2 g k hk
    have hk1 : modulus (k.val).det = 1 := by
      have := (H2 1 k hk).2.1
      simpa using this
    have hdet : Matrix.GeneralLinearGroup.det (g * k) =
        Matrix.GeneralLinearGroup.det g * Matrix.GeneralLinearGroup.det k := map_mul _ _ _
    have hc : ((c₁ (Matrix.GeneralLinearGroup.det (g * k)) : ℂˣ) : ℂ) =
        ((c₁ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) := by
      rw [hdet, map_mul, Units.val_mul, char_eq_one hc₁ (u := Matrix.GeneralLinearGroup.det k) hk1, mul_one]
    have hmp : mp (Matrix.GeneralLinearGroup.det (g * k)) (1 / 2) =
        mp (Matrix.GeneralLinearGroup.det g) (1 / 2) := by
      unfold mp
      have : modulus ((Matrix.GeneralLinearGroup.det (g * k) : Fˣ) : F) =
          modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) := hD
      rw [this]
    rw [key, key, hc, hmp, hM, sphJ_congr c₁ c₂ hD hM]
    by_cases hle : modulus (g.val).det ≤ modulus (mRow g) ^ 2
    · have ht := hx hle
      have h1 : χ (xRow (g * k) - xRow g) = 1 := by
        have h := isTrivialOn_addCharConductor hχ.1 hχ.2.1
        rw [hχ.2.2] at h
        exact h _ (mem_valBall_zero_iff.2 ht)
      have h2 : χ (xRow (g * k)) = χ (xRow g) := by
        have e : xRow (g * k) = (xRow (g * k) - xRow g) + xRow g := by ring
        rw [e, AddChar.map_add_eq_mul, h1, one_mul]
      rw [h2]
    · have h0 : (fun u => sphJ c₁ c₂ (g.val).det (mRow g) u) = fun _ => 0 :=
        funext (sphJ_eq_zero c₁ c₂ hm hle)
      simp only [h0, integral_zero, mul_zero]
  · rw [key]
    have hm1 : mRow (1 : GL (Fin 2) F) = 1 := by
      simp [mRow]
    have hx1 : xRow (1 : GL (Fin 2) F) = 0 := by
      simp [xRow]
    have hJ : (fun u => sphJ c₁ c₂ ((1 : GL (Fin 2) F).val).det 1 u) =
        (unitFiltrationUnits F 0 : Set Fˣ).indicator (fun _ => (1 : ℂ)) := by
      funext u
      by_cases hu : u ∈ (unitFiltrationUnits F 0 : Set Fˣ)
      · have hu1 : modulus (u : F) = 1 := mem_units_iff_modulus.1 hu
        rw [Set.indicator_of_mem hu]
        have e1 : ((c₂ u)⁻¹ : ℂˣ) = 1 := by
          have : c₂ u = 1 := hc₂ (mem_units_iff_modulus.2 hu1)
          rw [this, inv_one]
        unfold sphJ
        rw [e1, char_eq_one hc₁ hu1, intInd_of_mem, intInd_of_mem]
        · simp
        · rw [← modulus_le_one_iff]; simp [modulus_mul, hu1]
        · rw [← modulus_le_one_iff]; simp [modulus_mul, modulus_inv, hu1]
      · rw [Set.indicator_of_notMem hu]
        have hu1 : modulus (u : F) ≠ 1 := fun h => hu (mem_units_iff_modulus.2 h)
        unfold sphJ
        rcases lt_or_gt_of_ne hu1 with h | h
        · rw [intInd_of_notMem (x := (1 * (u : F))⁻¹)]
          · simp
          · rw [← modulus_le_one_iff, one_mul, modulus_inv, not_le]
            exact (one_lt_inv₀ (modulus_pos u.ne_zero)).2 h
        · rw [intInd_of_notMem (x := ((1 : GL (Fin 2) F).val).det * u / 1)]
          · simp
          · rw [← modulus_le_one_iff, not_le]
            simpa using h
    have hmeas : MeasurableSet (unitFiltrationUnits F 0 : Set Fˣ) := by
      exact (isOpen_unitFiltrationUnits 0).measurableSet
    have hint : ∫ u, sphJ c₁ c₂ ((1 : GL (Fin 2) F).val).det 1 u ∂multHaar F = 1 := by
      rw [hJ, integral_indicator_const _ hmeas]
      simp [Measure.real, multHaar_unitFiltrationUnits_zero]
    rw [hm1, hx1, hint]
    simp [mp]

open GlobalTheory.CompanionTheory.SphTheta.InertAsm in

/- English proof (translation)
Establish `hstd` using `GlobalTheory.CompanionTheory.SphTheta.isStd_chE_of_ord_unif F E h2 hcont hord χ hχ`. Establish `hform` using `GlobalTheory.CompanionTheory.SphTheta.inert_rw F E h2 hcont hord χ η σ hσ hχ hstd hη (GlobalTheory.CompanionTheory.NormGauss.gauss_main F E h2 hcont hord χ η hχ hstd hη)`. Establish `hrow` using `GlobalTheory.CompanionTheory.SphTheta.RowIwasawa.iwasawa_lower_row F`. Take `⟨hη1, hηu, -, -⟩` from `hη`. Use `haveI : Fact (Module.finrank F E = 2) := ⟨h2⟩`.

Use `haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)`. Use `haveI : Algebra.IsSeparable F E := inferInstance`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `k hk g`. Establish `hdk : modulus (k.val).det = 1`.

Establish `h1` using `(hrow 1 k hk).2.1`. Simplify using `using h1`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs⟩ : ∃ s : Eˣ, Algebra.norm F (s : E) = (k.val).det := by`. Establish `hk0 : (k.val).det ≠ 0` using `(Matrix.GeneralLinearGroup.det k).ne_zero`. Establish `h1` using `hη1 (Units.mk0 _ hk0)`.

Rewrite `h1` using `[char_congr η hηu (u := Units.mk0 _ hk0) (v := 1) (by simpa using hdk), map_one, Units.val_one, Units.val_mk0, GL2LocalData.nsg]`. Assume the negation of the conclusion as `hn`. Rewrite `h1` using `[if_neg hn]`. Evaluate the numerical expressions using `at h1`. Distinguish the cases in `hg : ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det`.

Take `⟨t, ht⟩` from `hg`. Establish `ht' : Algebra.norm F ((t * s : Eˣ) : E) = ((g * k).val).det`. Rewrite using `[Units.val_mul, map_mul, ht, hs, Units.val_mul, Matrix.det_mul]`. Rewrite using `[Wc_eq hc hform _ _ ht', Wc_eq hc hform _ _ ht]`. Take `⟨hm0, hdet, hmm, hx⟩` from `hrow g k hk`.

Conclude with `val_eq hχ hη1 hηu hc ht ht' hm0 (hrow (g * k) 1 (one_mem _)).1 hdet hmm hx`. Establish `hg' : ¬ ∃ t : Eˣ, Algebra.norm F (t : E) = ((g * k).val).det`. Introduce and unpack `⟨t', ht'⟩`. Use `hg ⟨t' * s⁻¹, ?_⟩` and prove the remaining obligations. Establish `hs0 : Algebra.norm F (s : E) ≠ 0` using `Algebra.norm_ne_zero_iff.2 s.ne_zero`.

Establish `hmul : Algebra.norm F ((t' * s⁻¹ : Eˣ) : E) * Algebra.norm F (s : E) = Algebra.norm F (t' : E)`. Rewrite using `[← map_mul, ← Units.val_mul, inv_mul_cancel_right]`. Establish `hd : ((g * k).val).det = (g.val).det * (k.val).det`. Rewrite using `[Units.val_mul, Matrix.det_mul]`. Rewrite `hmul` using `[ht', hs, hd]`.

Conclude with `mul_right_cancel₀ (hs ▸ hs0) hmul`. Rewrite using `[GL2LocalData.Wc, GL2LocalData.Wc, dif_neg hg, dif_neg hg']`. Rewrite using `[Wc_eq hc hform 1 1 (by simp)]`. Establish `hn : GL2LocalData.nsg E (1 : F) = 1`. Rewrite using `[GL2LocalData.nsg, if_pos ⟨1, by simp⟩]`.

Establish `hO : (1 : E) ∈ 𝒪[E]` using `one_mem _`. Simplify using `[val, mRow_one, xRow_one, hn, intInd, hO]`.
-/
theorem inert_sph (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] [CharZero F]
    (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E]
    (h2 : Module.finrank F E = 2) (hcont : Continuous (algebraMap F E))
    (hord : GroundTheory.LocalField.ord (algebraMap F E (unifUnit F : F)) = 1)
    (χ : AddChar F Circle) (η : Fˣ →* ℂˣ) (σ : E ≃ₐ[F] E) (c : Eˣ →* ℂˣ)
    (hσ : σ ≠ AlgEquiv.refl) (hχ : Ad3.IsStd χ) (hc : IsUnramifiedChar c)
    (hη : (∀ a, ((η a : ℂˣ) : ℂ) = GL2LocalData.nsg E (a : F)) ∧ IsUnramifiedChar η ∧ η * η = 1 ∧
      GL2LocalData.nsg E (-1 : F) = 1) :
    SphN (GL2LocalData.Wc χ σ (selfDualMeasure (GL2LocalData.chE E χ)) 1 c intInd) := by
  have hstd := GlobalTheory.CompanionTheory.SphTheta.isStd_chE_of_ord_unif F E h2 hcont hord χ hχ
  have hform := GlobalTheory.CompanionTheory.SphTheta.inert_rw F E h2 hcont hord χ η σ hσ hχ hstd hη
    (GlobalTheory.CompanionTheory.NormGauss.gauss_main F E h2 hcont hord χ η hχ hstd hη)
  have hrow := GlobalTheory.CompanionTheory.SphTheta.RowIwasawa.iwasawa_lower_row F
  obtain ⟨hη1, hηu, -, -⟩ := hη
  classical
  haveI : Fact (Module.finrank F E = 2) := ⟨h2⟩
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  haveI : Algebra.IsSeparable F E := inferInstance
  refine ⟨?_, ?_⟩
  · intro k hk g
    have hdk : modulus (k.val).det = 1 := by
      have h1 := (hrow 1 k hk).2.1
      simpa using h1
    obtain ⟨s, hs⟩ : ∃ s : Eˣ, Algebra.norm F (s : E) = (k.val).det := by
      have hk0 : (k.val).det ≠ 0 := (Matrix.GeneralLinearGroup.det k).ne_zero
      have h1 := hη1 (Units.mk0 _ hk0)
      rw [char_congr η hηu (u := Units.mk0 _ hk0) (v := 1) (by simpa using hdk), map_one,
        Units.val_one, Units.val_mk0, GL2LocalData.nsg] at h1
      by_contra hn
      rw [if_neg hn] at h1
      norm_num at h1
    by_cases hg : ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det
    · obtain ⟨t, ht⟩ := hg
      have ht' : Algebra.norm F ((t * s : Eˣ) : E) = ((g * k).val).det := by
        rw [Units.val_mul, map_mul, ht, hs, Units.val_mul, Matrix.det_mul]
      rw [Wc_eq hc hform _ _ ht', Wc_eq hc hform _ _ ht]
      obtain ⟨hm0, hdet, hmm, hx⟩ := hrow g k hk
      exact val_eq hχ hη1 hηu hc ht ht' hm0 (hrow (g * k) 1 (one_mem _)).1 hdet hmm hx
    · have hg' : ¬ ∃ t : Eˣ, Algebra.norm F (t : E) = ((g * k).val).det := by
        rintro ⟨t', ht'⟩
        refine hg ⟨t' * s⁻¹, ?_⟩
        have hs0 : Algebra.norm F (s : E) ≠ 0 := Algebra.norm_ne_zero_iff.2 s.ne_zero
        have hmul : Algebra.norm F ((t' * s⁻¹ : Eˣ) : E) * Algebra.norm F (s : E) =
            Algebra.norm F (t' : E) := by
          rw [← map_mul, ← Units.val_mul, inv_mul_cancel_right]
        have hd : ((g * k).val).det = (g.val).det * (k.val).det := by
          rw [Units.val_mul, Matrix.det_mul]
        rw [ht', hs, hd] at hmul
        exact mul_right_cancel₀ (hs ▸ hs0) hmul
      rw [GL2LocalData.Wc, GL2LocalData.Wc, dif_neg hg, dif_neg hg']
  · rw [Wc_eq hc hform 1 1 (by simp)]
    have hn : GL2LocalData.nsg E (1 : F) = 1 := by
      rw [GL2LocalData.nsg, if_pos ⟨1, by simp⟩]
    have hO : (1 : E) ∈ 𝒪[E] := one_mem _
    simp [val, mRow_one, xRow_one, hn, intInd, hO]

/- English proof (translation)
Introduce `K _ _ h2 c v hv W' hth`. Break down `hth with ⟨w₁, w₂, h₁, h₂, hne, rfl⟩ | ⟨w, hw, huniq, σ, η, hσ, hη, rfl⟩` into its components or cases. Use `haveI := h₁ haveI := h₂`. Rewrite using `[indicator_eq_phiS]`. Conclude with `split_sph (Qv v) (GP.psiF v)⁻¹ (cAt c v w₁) (cAt c v w₂) (GlobalTheory.CompanionTheory.SphStd.isStd_psiF_inv v) (GlobalTheory.CompanionTheory.SphTheta.isUnramifiedChar_comp_unitsMap (Qv v) (Kv K w₁) (localChar c w₁) (hv w₁).1) (GlobalTheory.CompanionTheory.SphTheta.isUnramifiedCh …`.

Use `haveI := hw`. Break down `GlobalTheory.CompanionTheory.QuadPlace.split_or_inert_of_unramified K h2 v (fun w _ => (hv w).2) with ⟨w₁, w₂, h₁, h₂, hne⟩ | ⟨w₀, hw₀, -, hf, hord⟩` into its components or cases. Conclude with `absurd ((huniq w₁ h₁).trans (huniq w₂ h₂).symm) hne`. Take `rfl` from `huniq w₀ hw₀`. Establish `hcont` using `GroundTheory.Global.continuous_adicCompletionMap v w₀`.

Take `⟨η', hη'⟩` from `GlobalTheory.CompanionTheory.SphTheta.UnramQuad.exists_quadChar_unramified (Qv v) (Kv K w₀) hf hcont hord`. Establish `hηη : η = η'`. Use extensionality with `a`. Rewrite using `[hη a, hη'.1 a]`. Substitute `hηη` using the available equality.

Establish `hχ` using `GlobalTheory.CompanionTheory.SphStd.isStd_psiF_inv v`. Establish `hstd` using `GlobalTheory.CompanionTheory.SphTheta.isStd_chE_of_ord_unif (Qv v) (Kv K w₀) hf hcont hord _ hχ`. Establish `hlam : GL2LocalData.lamE (Kv K w₀) (GP.psiF v)⁻¹ η = 1` using `GlobalTheory.CompanionTheory.LamUnr.lamE_eq_one (Qv v) (Kv K w₀) _ η hχ hstd hη'.2.1 hη'.2.2.1`. Rewrite using `[hlam, indicator_eq_intInd]`. Conclude with `inert_sph (Qv v) (Kv K w₀) hf hcont hord _ η σ (localChar c w₀) hσ hχ (hv w₀).1 hη'`.
-/
theorem stdTh_sphN : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
    ∀ (c : HeckeCharacter K) (v : Pl), Ad3.K.QuadraticBaseChangeGL3.Th.Unr c v →
      ∀ W' : GL (Fin 2) (Qv v) → ℂ, Ad3.K.QuadraticBaseChangeGL3.Th.StdTh c v W' → SphN W' := by
  intro K _ _ h2 c v hv W' hth
  rcases hth with ⟨w₁, w₂, h₁, h₂, hne, rfl⟩ | ⟨w, hw, huniq, σ, η, hσ, hη, rfl⟩
  · haveI := h₁
    haveI := h₂
    rw [indicator_eq_phiS]
    exact split_sph (Qv v) (GP.psiF v)⁻¹ (cAt c v w₁) (cAt c v w₂) (GlobalTheory.CompanionTheory.SphStd.isStd_psiF_inv v)
      (GlobalTheory.CompanionTheory.SphTheta.isUnramifiedChar_comp_unitsMap (Qv v) (Kv K w₁) (localChar c w₁) (hv w₁).1)
      (GlobalTheory.CompanionTheory.SphTheta.isUnramifiedChar_comp_unitsMap (Qv v) (Kv K w₂) (localChar c w₂) (hv w₂).1)
  · haveI := hw
    rcases GlobalTheory.CompanionTheory.QuadPlace.split_or_inert_of_unramified K h2 v (fun w _ => (hv w).2) with
      ⟨w₁, w₂, h₁, h₂, hne⟩ | ⟨w₀, hw₀, -, hf, hord⟩
    · exact absurd ((huniq w₁ h₁).trans (huniq w₂ h₂).symm) hne
    · obtain rfl := huniq w₀ hw₀
      have hcont := GroundTheory.Global.continuous_adicCompletionMap v w₀
      obtain ⟨η', hη'⟩ := GlobalTheory.CompanionTheory.SphTheta.UnramQuad.exists_quadChar_unramified (Qv v) (Kv K w₀) hf hcont hord
      have hηη : η = η' := by
        ext a
        rw [hη a, hη'.1 a]
      subst hηη
      have hχ := GlobalTheory.CompanionTheory.SphStd.isStd_psiF_inv v
      have hstd := GlobalTheory.CompanionTheory.SphTheta.isStd_chE_of_ord_unif (Qv v) (Kv K w₀) hf hcont hord _ hχ
      have hlam : GL2LocalData.lamE (Kv K w₀) (GP.psiF v)⁻¹ η = 1 :=
        GlobalTheory.CompanionTheory.LamUnr.lamE_eq_one (Qv v) (Kv K w₀) _ η hχ hstd hη'.2.1 hη'.2.2.1
      rw [hlam, indicator_eq_intInd]
      exact inert_sph (Qv v) (Kv K w₀) hf hcont hord _ η σ (localChar c w₀) hσ hχ (hv w₀).1 hη'

end GlobalTheory.CompanionTheory.StdSph
