import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperDiagEqSdM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUnipotentMemUpperUnipotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAutomorphicFormIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentTranslationMeasurePreservingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactGLOfCompactInvertibleMatricesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerBumpArchimedeanFactorContDiffOnInvertibStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWhittakerBumpArchimedeanFactorOneNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharFiniteSuperDiagonalSumIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerBumpFiniteFactorPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicGenericUnipotentCharacterEqArchMulFiniteStatement

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory
open scoped ContDiff

namespace GlobalTheory.WhitBump

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

/- English proof (translation)
The claim follows from `GlobalTheory.T.unipotent_translation_measure_preserving E n u hu`.
-/
theorem shear (u : GL (Fin n) (Cinf E)) (hu : u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n)) :
    ∃ τ : Vp E n ≃ᵐ Vp E n, MeasurePreserving τ volume volume ∧
      ∀ t, nu (τ t) = nu t * (u : Matrix (Fin n) (Fin n) (Cinf E)) := GlobalTheory.T.unipotent_translation_measure_preserving E n u hu

/- English proof (translation)
The claim follows from `GlobalTheory.T.isCompact_GL_of_compact_invertibleMatrices E n T hT hs`.
-/
theorem isCompact_setOf_toL (T : Set (Lie E n)) (hT : IsCompact T) (hs : T ⊆ invSet E n) :
    IsCompact {y : GL (Fin n) (Cinf E) | toL (y : Matrix (Fin n) (Fin n) (Cinf E)) ∈ T} := GlobalTheory.T.isCompact_GL_of_compact_invertibleMatrices E n T hT hs

variable [IsTotallyComplex E]

/- English proof (translation)
The claim follows from `GlobalTheory.T.whittakerBumpArchimedeanFactor_contDiffOn_invertible E n f hf hc hs`.
-/
theorem contDiffOn_bumpInf (f : Lie E n → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ invSet E n) : ContDiffOn ℝ ∞ (bumpInf f) (invSet E n) := GlobalTheory.T.whittakerBumpArchimedeanFactor_contDiffOn_invertible E n f hf hc hs

/- English proof (translation)
The claim follows from `GlobalTheory.T.exists_whittakerBumpArchimedeanFactor_one_ne_zero E n`.
-/
theorem exists_bumpInf_ne : ∃ f : Lie E n → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ invSet E n ∧
    bumpInf f (oneL E n) ≠ 0 := GlobalTheory.T.exists_whittakerBumpArchimedeanFactor_one_ne_zero E n

/- English proof (translation)
The claim follows from `GlobalTheory.T.standardAdelicCharFinite_superDiagonalSum_integral_eq_one E n u hu hk`.
-/
theorem psiFin_integral (u : GL (Fin n) (Af E)) (hu : u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n))
    (hk : u ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n) : psiFin (GlobalTheory.Whittaker.superDiag u) = 1 :=
  GlobalTheory.T.standardAdelicCharFinite_superDiagonalSum_integral_eq_one E n u hu hk

/- English proof (translation)
The claim follows from `GlobalTheory.T.whittakerBumpFiniteFactor_properties E n htriv`.
-/
theorem bumpFin_spec
    (htriv : ∀ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), u ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n →
      psiFin (GlobalTheory.Whittaker.superDiag u) = 1) :
    bumpFin (E := E) (n := n) 1 = 1 ∧
    (∀ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), ∀ g, bumpFin (u * g) = psiFin (GlobalTheory.Whittaker.superDiag u) * bumpFin g) ∧
    (∀ k ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n, ∀ g, bumpFin (g * k) = bumpFin g) ∧
    ∀ g, bumpFin g ≠ 0 → ∃ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n),
      u⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n := GlobalTheory.T.whittakerBumpFiniteFactor_properties E n htriv

/- English proof (translation)
The claim follows from `GlobalTheory.T.adelicGenericUnipotentCharacter_eq_arch_mul_finite E n u`.
-/
theorem psiN_eq (u : GA E n) :
    GlobalTheory.JSW.psiN u = psiInf (sdM ((GeneralLinearGroup.map (pInf E) u : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E))) *
      psiFin (GlobalTheory.Whittaker.superDiag (GeneralLinearGroup.map (pFin E) u)) := GlobalTheory.T.adelicGenericUnipotentCharacter_eq_arch_mul_finite E n u

end GlobalTheory.WhitBump

namespace GlobalTheory.WhitBump

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

/- English proof (translation)
Use `Continuous.units_map _ ?_` and prove the remaining obligations. Establish `hs : Continuous (sFin E : Af E → Ad E)` using `(continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))`. Conclude with `continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)`.
-/
theorem continuous_finGL_bump : Continuous (finGL E n) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sFin E : Af E → Ad E) :=
    (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))
  exact continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)

variable [IsTotallyComplex E]

/- English proof (translation)
Simplify using `[psiInf, map_add, AddChar.map_add_eq_mul]`.
-/
theorem psiInf_add (a b : Cinf E) : psiInf (a + b) = psiInf a * psiInf b := by
  simp [psiInf, map_add, AddChar.map_add_eq_mul]

/- English proof (translation)
Take `⟨τ, hτ, hτu⟩` from `shear u hu`. Establish `hsd : ∀ t, sdM (nu (τ t)) = sdM (nu t) + sdM (u : Matrix (Fin n) (Fin n) (Cinf E))` using `fun t => by`. Rewrite using `[hτu, ← nuGL_val, ← superDiag_eq_sdM, ← superDiag_eq_sdM, ← Units.val_mul, ← superDiag_eq_sdM]`. Conclude with `GlobalTheory.GamMul.UnipPlaced.superDiag_mul_unip (nuGL_mem t) hu`. Establish `key : ∀ t, (f (toL (nu t * Matrix.of (toL ((u : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of x)))) : ℂ) * psiInf (-sdM (nu t)) = psiInf (sdM (u : Matrix (Fin n) (Fin n) (Cinf E))) * ((f (toL (nu (τ t) * Matrix.of x)) : ℂ) * psiInf (-sdM (nu (τ t))))` using `fun t => by`.

Establish `e1 : Matrix.of (toL ((u : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of x)) = (u : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of x` using `rfl`. Establish `e2 : -sdM (nu t) = sdM (u : Matrix (Fin n) (Fin n) (Cinf E)) + -sdM (nu (τ t))`. Rewrite using `[hsd]`. Normalize the expressions using the abelian group laws. Rewrite using `[e1, ← Matrix.mul_assoc, ← hτu, e2, psiInf_add]`.

Expand and normalize the polynomial expressions, which then agree. Unfold `bumpInf`. Repeatedly rewrite using `[key]`. Rewrite using `[integral_const_mul]`. Use `congr 1`.

Conclude with `hτ.integral_comp' (g := fun s => (f (toL (nu s * Matrix.of x)) : ℂ) * psiInf (-sdM (nu s)))`.
-/
theorem bumpInf_mul (f : Lie E n → ℝ) (u : GL (Fin n) (Cinf E)) (hu : u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n))
    (x : Lie E n) :
    bumpInf f (toL ((u : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of x)) =
      psiInf (sdM (u : Matrix (Fin n) (Fin n) (Cinf E))) * bumpInf f x := by
  obtain ⟨τ, hτ, hτu⟩ := shear u hu
  have hsd : ∀ t, sdM (nu (τ t)) = sdM (nu t) + sdM (u : Matrix (Fin n) (Fin n) (Cinf E)) := fun t => by
    rw [hτu, ← nuGL_val, ← superDiag_eq_sdM, ← superDiag_eq_sdM, ← Units.val_mul, ← superDiag_eq_sdM]
    exact GlobalTheory.GamMul.UnipPlaced.superDiag_mul_unip (nuGL_mem t) hu
  have key : ∀ t, (f (toL (nu t * Matrix.of (toL ((u : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of x)))) : ℂ) *
      psiInf (-sdM (nu t)) = psiInf (sdM (u : Matrix (Fin n) (Fin n) (Cinf E))) *
        ((f (toL (nu (τ t) * Matrix.of x)) : ℂ) * psiInf (-sdM (nu (τ t)))) := fun t => by
    have e1 : Matrix.of (toL ((u : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of x)) =
        (u : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of x := rfl
    have e2 : -sdM (nu t) = sdM (u : Matrix (Fin n) (Fin n) (Cinf E)) + -sdM (nu (τ t)) := by
      rw [hsd]; abel
    rw [e1, ← Matrix.mul_assoc, ← hτu, e2, psiInf_add]
    ring
  unfold bumpInf
  simp_rw [key]
  rw [integral_const_mul]
  congr 1
  exact hτ.integral_comp' (g := fun s => (f (toL (nu s * Matrix.of x)) : ℂ) * psiInf (-sdM (nu s)))

end GlobalTheory.WhitBump

namespace GlobalTheory.WhitBump

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem map_apply_bump {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (g : GL (Fin n) R) (i j : Fin n) :
    (GeneralLinearGroup.map p g : Matrix (Fin n) (Fin n) S) i j = p ((g : Matrix (Fin n) (Fin n) R) i j) := rfl

/- English proof (translation)
The claim follows from `(GlobalTheory.SmGL.mem_unipB (Cinf E)).2 ⟨fun i j h => by rw [map_apply_bump, hu.1 i j h, map_zero], fun i => by rw [map_apply_bump, hu.2 i, map_one]⟩`.
-/
theorem pInf_mem_unipB {u : GA E n} (hu : u ∈ GlobalTheory.JSW.NA E n) :
    GeneralLinearGroup.map (pInf E) u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n) :=
  (GlobalTheory.SmGL.mem_unipB (Cinf E)).2 ⟨fun i j h => by rw [map_apply_bump, hu.1 i j h, map_zero],
    fun i => by rw [map_apply_bump, hu.2 i, map_one]⟩

omit [IsTotallyComplex E] in
/- English proof (translation)
The claim follows from `(GlobalTheory.SmGL.mem_unipB (Af E)).2 ⟨fun i j h => by rw [map_apply_bump, hu.1 i j h, map_zero], fun i => by rw [map_apply_bump, hu.2 i, map_one]⟩`.
-/
theorem pFin_mem_unipB {u : GA E n} (hu : u ∈ GlobalTheory.JSW.NA E n) :
    GeneralLinearGroup.map (pFin E) u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n) :=
  (GlobalTheory.SmGL.mem_unipB (Af E)).2 ⟨fun i j h => by rw [map_apply_bump, hu.1 i j h, map_zero],
    fun i => by rw [map_apply_bump, hu.2 i, map_one]⟩

/- English proof (translation)
Establish `hI : GeneralLinearGroup.map (pInf E) (infGL E n y * finGL E n k) = y` using `by simp`. Establish `hF : GeneralLinearGroup.map (pFin E) (infGL E n y * finGL E n k) = k` using `by simp`. Take `⟨hy1, hy2⟩` from `(GlobalTheory.SmGL.mem_unipB (Cinf E)).1 hy`. Take `⟨hk1, hk2⟩` from `(GlobalTheory.SmGL.mem_unipB (Af E)).1 hk`. Use `⟨fun i j h => ad_ext ?_ ?_, fun i => ad_ext ?_ ?_⟩` and prove the remaining obligations.

Rewrite using `[← map_apply_bump, hI, hy1 i j h, map_zero]`. Rewrite using `[← map_apply_bump, hF, hk1 i j h, map_zero]`. Rewrite using `[← map_apply_bump, hI, hy2 i, map_one]`. Rewrite using `[← map_apply_bump, hF, hk2 i, map_one]`.
-/
theorem mem_NA_of {y : GL (Fin n) (Cinf E)} {k : GL (Fin n) (Af E)} (hy : y ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n))
    (hk : k ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n)) : infGL E n y * finGL E n k ∈ GlobalTheory.JSW.NA E n := by
  have hI : GeneralLinearGroup.map (pInf E) (infGL E n y * finGL E n k) = y := by simp
  have hF : GeneralLinearGroup.map (pFin E) (infGL E n y * finGL E n k) = k := by simp
  obtain ⟨hy1, hy2⟩ := (GlobalTheory.SmGL.mem_unipB (Cinf E)).1 hy
  obtain ⟨hk1, hk2⟩ := (GlobalTheory.SmGL.mem_unipB (Af E)).1 hk
  refine ⟨fun i j h => ad_ext ?_ ?_, fun i => ad_ext ?_ ?_⟩
  · rw [← map_apply_bump, hI, hy1 i j h, map_zero]
  · rw [← map_apply_bump, hF, hk1 i j h, map_zero]
  · rw [← map_apply_bump, hI, hy2 i, map_one]
  · rw [← map_apply_bump, hF, hk2 i, map_one]

end GlobalTheory.WhitBump

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump in

/- English proof (translation)
Introduce `E _ _ _ m S`. Take `⟨f, hf, hfc, hfs, hf1⟩` from `exists_bumpInf_ne (E := E) (n := m + 1)`. Take `⟨h1, hN, hK, hsupp⟩` from `bumpFin_spec (E := E) (n := m + 1) fun u hu hk => psiFin_integral u hu hk`. Use `set c := bumpInf f (oneL E (m + 1)) with hc`. Set `pI : GA E (m + 1) → GL (Fin (m + 1)) (Cinf E)` to `fun g => GeneralLinearGroup.map (pInf E) g`.

Set `pF : GA E (m + 1) → GL (Fin (m + 1)) (Af E)` to `fun g => GeneralLinearGroup.map (pFin E) g`. Use `⟨fun g => bumpInf f (toL (pI g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E))) / c * bumpFin (pF g), ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [pI, pF, map_one, Units.val_one, h1, mul_one]`. Conclude with `div_self hf1`. Introduce `u hu g`.

Simplify using `only [pI, pF, map_mul, Units.val_mul]`. Establish `e` using `bumpInf_mul f _ (pInf_mem_unipB hu) (toL ((GeneralLinearGroup.map (pInf E) g : GL (Fin (m + 1)) (Cinf E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)))`. Use `erw [e]`. Rewrite using `[hN _ (pFin_mem_unipB hu), psiN_eq]`. Expand and normalize the polynomial expressions, which then agree.

Set `T` to `tsupport f`. Set `C : Set (GA E (m + 1))` to `(fun q : GL (Fin (m + 1)) (Cinf E) × GL (Fin (m + 1)) (Af E) => infGL E (m + 1) q.1 * finGL E (m + 1) q.2) '' ({y : GL (Fin (m + 1)) (Cinf E) | toL (y : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) ∈ T} ×ˢ (GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E (m + 1) : Set (GL ( …`. Use `⟨C, ?_, ?_⟩` and prove the remaining obligations. Use `((isCompact_setOf_toL T hfc hfs).prod (GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL E (m + 1))).image ?_` and prove the remaining obligations. Conclude with `((GlobalTheory.ConstTermSmooth.continuous_infGL).comp continuous_fst).mul (continuous_finGL_bump.comp continuous_snd)`.

Introduce `p _ hp`. Establish `hI : bumpInf f (toL (pI p : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E))) ≠ 0`. Introduce `h`. Apply `hp` to reduce the goal to its premises. Simplify using `only [h, zero_div, zero_mul]`.

Establish `hF : bumpFin (pF p) ≠ 0`. Introduce `h`. Apply `hp` to reduce the goal to its premises. Simplify using `only [h, mul_zero]`. Choose the witnesses or unpack the hypotheses as in `⟨t, ht⟩ : ∃ t, f (toL (nu t * Matrix.of (toL (pI p : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E))))) ≠ 0 := by`.

Assume the negation of the conclusion as `hall`. Use `push_neg at hall`. Establish `hall' : ∀ t, f (toL (nu t * (pI p : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)))) = 0` using `hall`. Apply `hI` to reduce the goal to its premises. Unfold `bumpInf`.

Simplify using `[hall']`. Take `⟨uf, huf, hk⟩` from `hsupp _ hF`. Use `⟨infGL E (m + 1) (nuGL t)⁻¹ * finGL E (m + 1) uf, mem_NA_of (inv_mem (nuGL_mem t)) huf, ⟨(nuGL t * pI p, uf⁻¹ * pF p), ⟨?_, hk⟩, ?_⟩⟩` and prove the remaining obligations. Conclude with `subset_tsupport f ht`. Apply the tactic sequence `refine ga_ext ?_ ?_ <;> simp [pI, pF]`.

Use `⟨GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E (m + 1), GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E (m + 1), fun k hk g => ?_⟩` and prove the remaining obligations. Simplify using `only [pI, pF, map_mul, pInf_finGL, pFin_finGL, mul_one]`. Rewrite using `[hK k hk]`. Introduce `g`. Establish `hsm` using `contDiffOn_bumpInf f hf hfc hfs`.

Use `set L := lmul (toL (pI g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E))) with hL`. Establish `hmaps : Set.MapsTo L (invSet E (m + 1)) (invSet E (m + 1))` using `fun x hx => by`. Establish `hx' : IsUnit (Matrix.of x)` using `hx`. Express the relevant statement in the definitionally equal form `IsUnit ((pI g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) * Matrix.of x)`. Conclude with `(pI g).isUnit.mul hx'`.

Establish `h2 : ContDiffOn ℝ ∞ (fun x : Lie E (m + 1) => bumpInf f (L x)) (invSet E (m + 1))` using `hsm.comp (L.contDiff.contDiffOn) hmaps`. Establish `hl : ContDiffOn ℝ ∞ (fun x : Lie E (m + 1) => bumpInf f (L x) / c * bumpFin (pF g)) (invSet E (m + 1))` using `(h2.div_const c).mul contDiffOn_const`. Use `hl.congr fun x hx => ?_` and prove the remaining obligations. Establish `hx' : IsUnit (Matrix.of x)` using `hx`. Rewrite using `[chart, dif_pos hx']`.

Simplify using `only [pI, pF, map_mul, pInf_infGL, pFin_infGL, mul_one, Units.val_mul, IsUnit.unit_spec]`. Both sides reduce to the same expression.
-/
theorem GlobalTheory.WhitBump.exists_bump : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), ∃ b : GA E (m + 1) → ℂ, b 1 = 1 ∧ (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) ∧ (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ GlobalTheory.JSW.mirS E S m, b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * p ∈ C) ∧ (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (m + 1) u) = b g) ∧ ∀ g, ContDiffOn ℝ ∞ (chart b g) (invSet E (m + 1)) := by
  intro E _ _ _ m S
  obtain ⟨f, hf, hfc, hfs, hf1⟩ := exists_bumpInf_ne (E := E) (n := m + 1)
  obtain ⟨h1, hN, hK, hsupp⟩ := bumpFin_spec (E := E) (n := m + 1) fun u hu hk => psiFin_integral u hu hk
  set c := bumpInf f (oneL E (m + 1)) with hc
  let pI : GA E (m + 1) → GL (Fin (m + 1)) (Cinf E) := fun g => GeneralLinearGroup.map (pInf E) g
  let pF : GA E (m + 1) → GL (Fin (m + 1)) (Af E) := fun g => GeneralLinearGroup.map (pFin E) g
  refine ⟨fun g => bumpInf f (toL (pI g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E))) / c * bumpFin (pF g),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp only [pI, pF, map_one, Units.val_one, h1, mul_one]
    exact div_self hf1
  · intro u hu g
    simp only [pI, pF, map_mul, Units.val_mul]
    have e := bumpInf_mul f _ (pInf_mem_unipB hu) (toL ((GeneralLinearGroup.map (pInf E) g : GL (Fin (m + 1)) (Cinf E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)))
    erw [e]
    rw [hN _ (pFin_mem_unipB hu), psiN_eq]
    ring
  · let T := tsupport f
    let C : Set (GA E (m + 1)) := (fun q : GL (Fin (m + 1)) (Cinf E) × GL (Fin (m + 1)) (Af E) =>
      infGL E (m + 1) q.1 * finGL E (m + 1) q.2) ''
        ({y : GL (Fin (m + 1)) (Cinf E) | toL (y : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) ∈ T} ×ˢ
          (GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E (m + 1) : Set (GL (Fin (m + 1)) (Af E))))
    refine ⟨C, ?_, ?_⟩
    · refine ((isCompact_setOf_toL T hfc hfs).prod
        (GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL E (m + 1))).image ?_
      exact ((GlobalTheory.ConstTermSmooth.continuous_infGL).comp continuous_fst).mul
        (continuous_finGL_bump.comp continuous_snd)
    · intro p _ hp
      have hI : bumpInf f (toL (pI p : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E))) ≠ 0 := by
        intro h; apply hp; simp only [h, zero_div, zero_mul]
      have hF : bumpFin (pF p) ≠ 0 := by
        intro h; apply hp; simp only [h, mul_zero]
      obtain ⟨t, ht⟩ : ∃ t, f (toL (nu t * Matrix.of (toL (pI p : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E))))) ≠ 0 := by
        by_contra hall
        push_neg at hall
        have hall' : ∀ t, f (toL (nu t * (pI p : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)))) = 0 := hall
        apply hI
        unfold bumpInf
        simp [hall']
      obtain ⟨uf, huf, hk⟩ := hsupp _ hF
      refine ⟨infGL E (m + 1) (nuGL t)⁻¹ * finGL E (m + 1) uf,
        mem_NA_of (inv_mem (nuGL_mem t)) huf, ⟨(nuGL t * pI p, uf⁻¹ * pF p), ⟨?_, hk⟩, ?_⟩⟩
      · exact subset_tsupport f ht
      · refine ga_ext ?_ ?_ <;> simp [pI, pF]
  · refine ⟨GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E (m + 1),
      GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E (m + 1), fun k hk g => ?_⟩
    simp only [pI, pF, map_mul, pInf_finGL, pFin_finGL, mul_one]
    rw [hK k hk]
  · intro g
    have hsm := contDiffOn_bumpInf f hf hfc hfs
    set L := lmul (toL (pI g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E))) with hL
    have hmaps : Set.MapsTo L (invSet E (m + 1)) (invSet E (m + 1)) := fun x hx => by
      have hx' : IsUnit (Matrix.of x) := hx
      change IsUnit ((pI g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) * Matrix.of x)
      exact (pI g).isUnit.mul hx'
    have h2 : ContDiffOn ℝ ∞ (fun x : Lie E (m + 1) => bumpInf f (L x)) (invSet E (m + 1)) :=
      hsm.comp (L.contDiff.contDiffOn) hmaps
    have hl : ContDiffOn ℝ ∞ (fun x : Lie E (m + 1) => bumpInf f (L x) / c * bumpFin (pF g))
        (invSet E (m + 1)) := (h2.div_const c).mul contDiffOn_const
    refine hl.congr fun x hx => ?_
    have hx' : IsUnit (Matrix.of x) := hx
    rw [chart, dif_pos hx']
    simp only [pI, pF, map_mul, pInf_infGL, pFin_infGL, mul_one, Units.val_mul, IsUnit.unit_spec]
    rfl
