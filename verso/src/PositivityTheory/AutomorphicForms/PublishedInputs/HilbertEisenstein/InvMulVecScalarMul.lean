import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.ContinuousPInfApply
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.ContinuousPInfCoord
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.IdeleModuleSectionMul

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix SchwartzMap nonZeroDivisors Classical Pointwise
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published NumberField.mixedEmbedding

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinIntegrability

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/- English proof (translation)
Rewrite using `[Units.val_mul, ← Matrix.vecMul_vecMul, Matrix.GeneralLinearGroup.coe_scalar]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `only [Matrix.scalar_apply, Matrix.vecMul_diagonal, Units.smul_def, rowA]`. Conclude with `mul_comm _ _`.
-/
theorem vecMul_scalar_mul (z : IdeleGroup F) (g : GA F 2) (ξ : Fin 2 → F) :
    rowA ξ ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) z * g : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) =
      (fun i => z • algebraMap F (Ad F) (ξ i)) ᵥ* (g : Matrix (Fin 2) (Fin 2) (Ad F)) := by
  rw [Units.val_mul, ← Matrix.vecMul_vecMul, Matrix.GeneralLinearGroup.coe_scalar]
  congr 1
  funext i
  simp only [Matrix.scalar_apply, Matrix.vecMul_diagonal, Units.smul_def, rowA]
  exact mul_comm _ _

/- English proof (translation)
Rewrite using `[mul_inv_rev, ← map_inv, Units.val_mul, ← Matrix.mulVec_mulVec, Matrix.GeneralLinearGroup.coe_scalar]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `only [Matrix.scalar_apply, Matrix.mulVec_diagonal, Units.smul_def, rowA]`. Both sides reduce to the same expression.
-/
theorem inv_mulVec_scalar_mul (z : IdeleGroup F) (g : GA F 2) (ξ : Fin 2 → F) :
    (((Matrix.GeneralLinearGroup.scalar (Fin 2) z * g)⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ =
      ((g⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ (fun i => z⁻¹ • algebraMap F (Ad F) (ξ i)) := by
  rw [mul_inv_rev, ← map_inv, Units.val_mul, ← Matrix.mulVec_mulVec, Matrix.GeneralLinearGroup.coe_scalar]
  congr 1
  funext i
  simp only [Matrix.scalar_apply, Matrix.mulVec_diagonal, Units.smul_def, rowA]
  rfl

/- English proof (translation)
Use `set Kc : Set (Matrix (Fin 2) (Fin 2) (Ad F)) := (fun g : GA F 2 => ((g⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) '' K with hKcdef`. Establish `hKc : IsCompact Kc` using `hK.image Units.continuous_coe_inv`. Use `set L : Set (Af F) := (idealFiniteAdeles (Jc c) : Set (Af F)) ∪ ((1 : Af F) +ᵥ (idealFiniteAdeles (Jc c) : Set (Af F))) with hLdef`. Establish `hL : IsCompact L` using `(isCompact_idealFiniteAdeles _).union ((isCompact_idealFiniteAdeles _).vadd (1 : Af F))`. Take `⟨J, N, hdom⟩` from `dom_gen hKc hL`.

Use `set C : Set (IdeleGroup F) := (fun u : normOneSubgroup F => invN F N * (u : IdeleGroup F)) '' closure (normOneFundamentalDomain F) with hCdef`. Establish `hC : IsCompact C` using `(isCompact_closure_normOneFundamentalDomain F).image (continuous_const.mul continuous_subtype_val)`. Take `⟨M1, hM1, hdec⟩` from `decay1D (gJ_mem J) hC (w0 F)`. Use `⟨2 * (‖gJ J 0‖ + M1) * M1, mul_nonneg (mul_nonneg (by norm_num) (add_nonneg (norm_nonneg _) hM1)) hM1, fun g hg t ht u hu => ?_⟩` and prove the remaining obligations. Take `⟨hsum, hS', hS⟩` from `hdec _ ⟨u, hu, rfl⟩ t ht`.

Use `set b : IdeleGroup F := moduleSection (w0 F) t * (invN F N * (u : IdeleGroup F)) with hbdef`. Use `set f : F → ℝ := fun x => ‖gJ J (b • algebraMap F (Ad F) x)‖ with hfdef`. Establish `hf0 : ∀ x, 0 ≤ f x` using `fun x => norm_nonneg _`. Take `⟨hps, hpb⟩` from `pair_sum hf0 hsum`. Use `set h : GA F 2 := Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F)) * g with hhdef`.

Establish `hterm : ∀ ξ : {ξ : Fin 2 → F // ξ ≠ 0}, ‖Phi c (rowA ξ.1 ᵥ* (h : Matrix (Fin 2) (Fin 2) (Ad F)))‖ ≤ f (ξ.1 0) * f (ξ.1 1)`. Introduce `ξ`. Rewrite using `[hhdef, vecMul_scalar_mul]`. Use `set v : Fin 2 → Ad F := fun i => (moduleSection (w0 F) t * (u : IdeleGroup F)) • algebraMap F (Ad F) (ξ.1 i) with hvdef`. Use `set y : Fin 2 → Ad F := v ᵥ* (g : Matrix (Fin 2) (Fin 2) (Ad F)) with hydef`.

Establish `hy : y ᵥ* ((g⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) = v`. Rewrite using `[hydef, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]`. Establish `h1` using `hdom _ ⟨g, hg, rfl⟩ y`. Rewrite `h1` using `[hy]`. Establish `hv : ∀ i, invN F N • v i = b • algebraMap F (Ad F) (ξ.1 i)`.

Introduce `i`. Rewrite using `[hvdef, hbdef, smul_smul, mul_left_comm]`. Rewrite `h1` using `[hv 0, hv 1]`. Use `le_trans ?_ h1` and prove the remaining obligations. Rewrite using `[phi_eq H y, norm_mul]`.

Use `mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)` and prove the remaining obligations. Distinguish the cases in `h2 : pFin F (y 0) ∈ idealFiniteAdeles (Jc c) ∧ pFin F (y 1) - 1 ∈ idealFiniteAdeles (Jc c)`. Establish `h3 : pFin F (y 0) ∈ L ∧ pFin F (y 1) ∈ L` using `⟨Or.inl h2.1, Or.inr (mem_vadd_idealFiniteAdeles.2 h2.2)⟩`. Rewrite using `[if_pos h2, if_pos h3, norm_one]`. Apply the tactic sequence `rw [if_neg h2, norm_zero] split_ifs <;> norm_num`.

Establish `hsumPhi : Summable fun ξ : {ξ : Fin 2 → F // ξ ≠ 0} => ‖Phi c (rowA ξ.1 ᵥ* (h : Matrix (Fin 2) (Fin 2) (Ad F)))‖` using `hps.of_nonneg_of_le (fun _ => norm_nonneg _) hterm`. Apply the tactic sequence `have hS'0 : 0 ≤ ∑' x : F, (if x = 0 then 0 else f x) := tsum_nonneg fun x => by split_ifs <;> simp [hf0]`. Rewrite using `[thetaS]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem thetaS_bound {ω : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (H : Hyp ω c) {K : Set (GA F 2)}
    (hK : IsCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ g ∈ K, ∀ t : {r : ℝ // 0 < r}, 1 ≤ (t : ℝ) → ∀ u ∈ closure (normOneFundamentalDomain F),
      ‖thetaS (Phi c) (Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F)) * g)‖ ≤
        ((t : ℝ) ^ 3)⁻¹ * M := by
  set Kc : Set (Matrix (Fin 2) (Fin 2) (Ad F)) :=
    (fun g : GA F 2 => ((g⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) '' K with hKcdef
  have hKc : IsCompact Kc := hK.image Units.continuous_coe_inv
  set L : Set (Af F) := (idealFiniteAdeles (Jc c) : Set (Af F)) ∪
    ((1 : Af F) +ᵥ (idealFiniteAdeles (Jc c) : Set (Af F))) with hLdef
  have hL : IsCompact L := (isCompact_idealFiniteAdeles _).union ((isCompact_idealFiniteAdeles _).vadd (1 : Af F))
  obtain ⟨J, N, hdom⟩ := dom_gen hKc hL
  set C : Set (IdeleGroup F) := (fun u : normOneSubgroup F => invN F N * (u : IdeleGroup F)) ''
    closure (normOneFundamentalDomain F) with hCdef
  have hC : IsCompact C := (isCompact_closure_normOneFundamentalDomain F).image
    (continuous_const.mul continuous_subtype_val)
  obtain ⟨M1, hM1, hdec⟩ := decay1D (gJ_mem J) hC (w0 F)
  refine ⟨2 * (‖gJ J 0‖ + M1) * M1, mul_nonneg (mul_nonneg (by norm_num) (add_nonneg (norm_nonneg _) hM1)) hM1,
    fun g hg t ht u hu => ?_⟩
  obtain ⟨hsum, hS', hS⟩ := hdec _ ⟨u, hu, rfl⟩ t ht
  set b : IdeleGroup F := moduleSection (w0 F) t * (invN F N * (u : IdeleGroup F)) with hbdef
  set f : F → ℝ := fun x => ‖gJ J (b • algebraMap F (Ad F) x)‖ with hfdef
  have hf0 : ∀ x, 0 ≤ f x := fun x => norm_nonneg _
  obtain ⟨hps, hpb⟩ := pair_sum hf0 hsum
  set h : GA F 2 := Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F)) * g with hhdef
  have hterm : ∀ ξ : {ξ : Fin 2 → F // ξ ≠ 0},
      ‖Phi c (rowA ξ.1 ᵥ* (h : Matrix (Fin 2) (Fin 2) (Ad F)))‖ ≤ f (ξ.1 0) * f (ξ.1 1) := by
    intro ξ
    rw [hhdef, vecMul_scalar_mul]
    set v : Fin 2 → Ad F := fun i => (moduleSection (w0 F) t * (u : IdeleGroup F)) • algebraMap F (Ad F) (ξ.1 i)
      with hvdef
    set y : Fin 2 → Ad F := v ᵥ* (g : Matrix (Fin 2) (Fin 2) (Ad F)) with hydef
    have hy : y ᵥ* ((g⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) = v := by
      rw [hydef, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
    have h1 := hdom _ ⟨g, hg, rfl⟩ y
    rw [hy] at h1
    have hv : ∀ i, invN F N • v i = b • algebraMap F (Ad F) (ξ.1 i) := by
      intro i
      rw [hvdef, hbdef, smul_smul, mul_left_comm]
    rw [hv 0, hv 1] at h1
    refine le_trans ?_ h1
    rw [phi_eq H y, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    by_cases h2 : pFin F (y 0) ∈ idealFiniteAdeles (Jc c) ∧ pFin F (y 1) - 1 ∈ idealFiniteAdeles (Jc c)
    · have h3 : pFin F (y 0) ∈ L ∧ pFin F (y 1) ∈ L :=
        ⟨Or.inl h2.1, Or.inr (mem_vadd_idealFiniteAdeles.2 h2.2)⟩
      rw [if_pos h2, if_pos h3, norm_one]
    · rw [if_neg h2, norm_zero]
      split_ifs <;> norm_num
  have hsumPhi : Summable fun ξ : {ξ : Fin 2 → F // ξ ≠ 0} =>
      ‖Phi c (rowA ξ.1 ᵥ* (h : Matrix (Fin 2) (Fin 2) (Ad F)))‖ :=
    hps.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
  have hS'0 : 0 ≤ ∑' x : F, (if x = 0 then 0 else f x) :=
    tsum_nonneg fun x => by split_ifs <;> simp [hf0]
  rw [thetaS]
  calc ‖∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, Phi c (rowA ξ.1 ᵥ* (h : Matrix (Fin 2) (Fin 2) (Ad F)))‖
      ≤ ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, ‖Phi c (rowA ξ.1 ᵥ* (h : Matrix (Fin 2) (Fin 2) (Ad F)))‖ :=
        norm_tsum_le_tsum_norm hsumPhi
    _ ≤ ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, f (ξ.1 0) * f (ξ.1 1) := hsumPhi.tsum_le_tsum hterm hps
    _ ≤ 2 * (∑' x, f x) * ∑' x, (if x = 0 then 0 else f x) := hpb
    _ ≤ 2 * (‖gJ J 0‖ + M1) * (((t : ℝ) ^ 3)⁻¹ * M1) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hS (by norm_num)) hS' hS'0
          (mul_nonneg (by norm_num) (add_nonneg (norm_nonneg _) hM1))
    _ = ((t : ℝ) ^ 3)⁻¹ * (2 * (‖gJ J 0‖ + M1) * M1) := by ring

/- English proof (translation)
Use `set Kc : Set (Matrix (Fin 2) (Fin 2) (Ad F)) := (fun g : GA F 2 => ((g : Matrix (Fin 2) (Fin 2) (Ad F)))ᵀ) '' K with hKcdef`. Establish `hKc : IsCompact Kc` using `hK.image Units.continuous_val.matrix_transpose`. Take `⟨J, N, hdom⟩` from `dom_gen hKc (isCompact_idealFiniteAdeles (Jh c))`. Use `set C : Set (IdeleGroup F) := (fun u : normOneSubgroup F => invN F N * (u : IdeleGroup F)⁻¹) '' closure (normOneFundamentalDomain F) with hCdef`. Establish `hC : IsCompact C` using `(isCompact_closure_normOneFundamentalDomain F).image (continuous_const.mul continuous_subtype_val.inv)`.

Take `⟨M1, hM1, hdec⟩` from `decay1D (gJ_mem J) hC (w0 F)`. Use `⟨2 * (‖gJ J 0‖ + M1) * M1, mul_nonneg (mul_nonneg (by norm_num) (add_nonneg (norm_nonneg _) hM1)) hM1, fun g hg t ht u hu => ?_⟩` and prove the remaining obligations. Establish `htinv : ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ) = (t : ℝ)⁻¹` using `rfl`. Establish `hT : 1 ≤ ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ)`. Rewrite using `[htinv]`.

Conclude with `one_le_inv₀ t.2 |>.2 ht`. Take `⟨hsum, hS', hS⟩` from `hdec _ ⟨u, hu, rfl⟩ t⁻¹ hT`. Use `set b : IdeleGroup F := moduleSection (w0 F) t⁻¹ * (invN F N * (u : IdeleGroup F)⁻¹) with hbdef`. Use `set f : F → ℝ := fun x => ‖gJ J (b • algebraMap F (Ad F) x)‖ with hfdef`. Establish `hf0 : ∀ x, 0 ≤ f x` using `fun x => norm_nonneg _`.

Take `⟨hps, hpb⟩` from `pair_sum hf0 hsum`. Use `set h : GA F 2 := Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F)) * g with hhdef`. Establish `hterm : ∀ ξ : {ξ : Fin 2 → F // ξ ≠ 0}, ‖PhiH c (((h⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ.1)‖ ≤ f (ξ.1 0) * f (ξ.1 1)`. Introduce `ξ`. Rewrite using `[hhdef, inv_mulVec_scalar_mul]`.

Use `set v : Fin 2 → Ad F := fun i => (moduleSection (w0 F) t * (u : IdeleGroup F))⁻¹ • algebraMap F (Ad F) (ξ.1 i) with hvdef`. Use `set y : Fin 2 → Ad F := ((g⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ v with hydef`. Establish `hy : y ᵥ* ((g : Matrix (Fin 2) (Fin 2) (Ad F)))ᵀ = v`. Rewrite using `[Matrix.vecMul_transpose, hydef, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`. Establish `h1` using `hdom _ ⟨g, hg, rfl⟩ y`.

Rewrite `h1` using `[hy]`. Establish `hv : ∀ i, invN F N • v i = b • algebraMap F (Ad F) (ξ.1 i)`. Introduce `i`. Rewrite using `[hvdef, hbdef, smul_smul]`. Use `congr 1`.

Rewrite using `[map_inv, mul_inv_rev]`. Conclude with `(mul_assoc _ _ _).symm.trans (mul_comm _ _)`. Rewrite `h1` using `[hv 0, hv 1]`. Conclude with `le_trans (norm_phiH_le H y) h1`. Establish `hsumPhi : Summable fun ξ : {ξ : Fin 2 → F // ξ ≠ 0} => ‖PhiH c (((h⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ.1)‖` using `hps.of_nonneg_of_le (fun _ => norm_nonneg _) hterm`.

Apply the tactic sequence `have hS'0 : 0 ≤ ∑' x : F, (if x = 0 then 0 else f x) := tsum_nonneg fun x => by split_ifs <;> simp [hf0]`. Rewrite using `[thetaT]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem thetaT_bound {ω : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (H : Hyp ω c) {K : Set (GA F 2)}
    (hK : IsCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ g ∈ K, ∀ t : {r : ℝ // 0 < r}, (t : ℝ) ≤ 1 → ∀ u ∈ closure (normOneFundamentalDomain F),
      ‖thetaT (PhiH c) (Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F)) * g)‖ ≤
        (t : ℝ) ^ 3 * M := by
  set Kc : Set (Matrix (Fin 2) (Fin 2) (Ad F)) :=
    (fun g : GA F 2 => ((g : Matrix (Fin 2) (Fin 2) (Ad F)))ᵀ) '' K with hKcdef
  have hKc : IsCompact Kc := hK.image Units.continuous_val.matrix_transpose
  obtain ⟨J, N, hdom⟩ := dom_gen hKc (isCompact_idealFiniteAdeles (Jh c))
  set C : Set (IdeleGroup F) := (fun u : normOneSubgroup F => invN F N * (u : IdeleGroup F)⁻¹) ''
    closure (normOneFundamentalDomain F) with hCdef
  have hC : IsCompact C := (isCompact_closure_normOneFundamentalDomain F).image
    (continuous_const.mul continuous_subtype_val.inv)
  obtain ⟨M1, hM1, hdec⟩ := decay1D (gJ_mem J) hC (w0 F)
  refine ⟨2 * (‖gJ J 0‖ + M1) * M1, mul_nonneg (mul_nonneg (by norm_num) (add_nonneg (norm_nonneg _) hM1)) hM1,
    fun g hg t ht u hu => ?_⟩
  have htinv : ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ) = (t : ℝ)⁻¹ := rfl
  have hT : 1 ≤ ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ) := by
    rw [htinv]
    exact one_le_inv₀ t.2 |>.2 ht
  obtain ⟨hsum, hS', hS⟩ := hdec _ ⟨u, hu, rfl⟩ t⁻¹ hT
  set b : IdeleGroup F := moduleSection (w0 F) t⁻¹ * (invN F N * (u : IdeleGroup F)⁻¹) with hbdef
  set f : F → ℝ := fun x => ‖gJ J (b • algebraMap F (Ad F) x)‖ with hfdef
  have hf0 : ∀ x, 0 ≤ f x := fun x => norm_nonneg _
  obtain ⟨hps, hpb⟩ := pair_sum hf0 hsum
  set h : GA F 2 := Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F)) * g with hhdef
  have hterm : ∀ ξ : {ξ : Fin 2 → F // ξ ≠ 0},
      ‖PhiH c (((h⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ.1)‖ ≤ f (ξ.1 0) * f (ξ.1 1) := by
    intro ξ
    rw [hhdef, inv_mulVec_scalar_mul]
    set v : Fin 2 → Ad F := fun i => (moduleSection (w0 F) t * (u : IdeleGroup F))⁻¹ • algebraMap F (Ad F) (ξ.1 i)
      with hvdef
    set y : Fin 2 → Ad F := ((g⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ v with hydef
    have hy : y ᵥ* ((g : Matrix (Fin 2) (Fin 2) (Ad F)))ᵀ = v := by
      rw [Matrix.vecMul_transpose, hydef, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
    have h1 := hdom _ ⟨g, hg, rfl⟩ y
    rw [hy] at h1
    have hv : ∀ i, invN F N • v i = b • algebraMap F (Ad F) (ξ.1 i) := by
      intro i
      rw [hvdef, hbdef, smul_smul]
      congr 1
      rw [map_inv, mul_inv_rev]
      exact (mul_assoc _ _ _).symm.trans (mul_comm _ _)
    rw [hv 0, hv 1] at h1
    exact le_trans (norm_phiH_le H y) h1
  have hsumPhi : Summable fun ξ : {ξ : Fin 2 → F // ξ ≠ 0} =>
      ‖PhiH c (((h⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ.1)‖ :=
    hps.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
  have hS'0 : 0 ≤ ∑' x : F, (if x = 0 then 0 else f x) :=
    tsum_nonneg fun x => by split_ifs <;> simp [hf0]
  rw [thetaT]
  calc ‖∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, PhiH c (((h⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ.1)‖
      ≤ ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, ‖PhiH c (((h⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ.1)‖ :=
        norm_tsum_le_tsum_norm hsumPhi
    _ ≤ ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, f (ξ.1 0) * f (ξ.1 1) := hsumPhi.tsum_le_tsum hterm hps
    _ ≤ 2 * (∑' x, f x) * ∑' x, (if x = 0 then 0 else f x) := hpb
    _ ≤ 2 * (‖gJ J 0‖ + M1) * ((((t⁻¹ : {r : ℝ // 0 < r}) : ℝ) ^ 3)⁻¹ * M1) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hS (by norm_num)) hS' hS'0
          (mul_nonneg (by norm_num) (add_nonneg (norm_nonneg _) hM1))
    _ = (t : ℝ) ^ 3 * (2 * (‖gJ J 0‖ + M1) * M1) := by rw [htinv, inv_pow, inv_inv]; ring

/- English proof (translation)
Establish `ht0 : 0 < t` using `lt_of_lt_of_le one_pos ht`. Establish `hy : 0 ≤ Real.log t` using `Real.log_nonneg ht`. Establish `h1 : Real.log t + 1 ≤ t`. Use `Real.add_one_le_exp (Real.log t)` as an intermediate fact. Rewrite `this` using `[Real.exp_log ht0]`. Then use the resulting hypothesis.

Establish `h2 : 1 + Real.log t ^ 2 ≤ t ^ 2` using `by nlinarith`. Conclude with `inv_anti₀ (by positivity) h2`.
-/
theorem inv_sq_le_of_one_le {t : ℝ} (ht : 1 ≤ t) : (t ^ 2)⁻¹ ≤ (1 + Real.log t ^ 2)⁻¹ := by
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  have hy : 0 ≤ Real.log t := Real.log_nonneg ht
  have h1 : Real.log t + 1 ≤ t := by
    have := Real.add_one_le_exp (Real.log t)
    rwa [Real.exp_log ht0] at this
  have h2 : 1 + Real.log t ^ 2 ≤ t ^ 2 := by nlinarith
  exact inv_anti₀ (by positivity) h2

/- English proof (translation)
Use `set y := Real.log t with hy`. Establish `hy0 : y ≤ 0` using `Real.log_nonpos ht0.le ht`. Establish `h1 : 1 - y ≤ t⁻¹`. Use `Real.add_one_le_exp (-y)` as an intermediate fact. Rewrite `this` using `[Real.exp_neg, hy, Real.exp_log ht0]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : t * (1 - y) ≤ 1`. Use `mul_le_mul_of_nonneg_left h1 ht0.le` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel₀ ht0.ne']`. Then use the resulting hypothesis. Establish `h0 : 0 ≤ t * (1 - y)` using `mul_nonneg ht0.le (by linarith)`.

Establish `h4 : (t * (1 - y)) ^ 2 ≤ 1` using `by nlinarith`. Establish `h5 : t ^ 2 * (1 + y ^ 2) ≤ (t * (1 - y)) ^ 2`. Use polynomial arithmetic with `[mul_nonneg (sq_nonneg t) (neg_nonneg.2 hy0)]`. Rewrite using `[← one_div, le_div_iff₀ (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sq_le_of_le_one {t : ℝ} (ht0 : 0 < t) (ht : t ≤ 1) : t ^ 2 ≤ (1 + Real.log t ^ 2)⁻¹ := by
  set y := Real.log t with hy
  have hy0 : y ≤ 0 := Real.log_nonpos ht0.le ht
  have h1 : 1 - y ≤ t⁻¹ := by
    have := Real.add_one_le_exp (-y)
    rw [Real.exp_neg, hy, Real.exp_log ht0] at this
    linarith
  have h3 : t * (1 - y) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left h1 ht0.le
    rwa [mul_inv_cancel₀ ht0.ne'] at this
  have h0 : 0 ≤ t * (1 - y) := mul_nonneg ht0.le (by linarith)
  have h4 : (t * (1 - y)) ^ 2 ≤ 1 := by nlinarith
  have h5 : t ^ 2 * (1 + y ^ 2) ≤ (t * (1 - y)) ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg t) (neg_nonneg.2 hy0)]
  rw [← one_div, le_div_iff₀ (by positivity)]
  linarith

/- English proof (translation)
Take `⟨n, hn, hpow⟩` from `hω.exists_pow_eq_one`. Establish `h1 : (ω.1 x) ^ n = 1` using `congrArg (fun ξ : HChar F => ξ.1 x) hpow`. Establish `h2 : ‖((ω.1 x : ℂˣ) : ℂ)‖ ^ n = 1`. Rewrite using `[← norm_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2`.
-/
theorem norm_omega_eq_one {ω : HChar F} (hω : IsOfFinOrder ω) (x : Ideles F) : ‖((ω.1 x : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨n, hn, hpow⟩ := hω.exists_pow_eq_one
  have h1 : (ω.1 x) ^ n = 1 := congrArg (fun ξ : HChar F => ξ.1 x) hpow
  have h2 : ‖((ω.1 x : ℂˣ) : ℂ)‖ ^ n = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2

/- English proof (translation)
Establish `hdet : Continuous fun g : GA F 2 => (Matrix.GeneralLinearGroup.det g : IdeleGroup F)`. Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Continuous fun g : GA F 2 => (g : Matrix (Fin 2) (Fin 2) (Ad F)).det`. Conclude with `Units.continuous_val.matrix_det`. Establish `e : ∀ g : GA F 2, ((g⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).det = (((Matrix.GeneralLinearGroup.det g)⁻¹ : (Ad F)ˣ) : Ad F)` using `fun g => by`.

Rewrite using `[← map_inv]`. Both sides reduce to the same expression. Conclude with `(Units.continuous_coe_inv.matrix_det).congr e`. Conclude with `continuous_subtype_val.comp (IdeleGroup.continuous_ideleModule.comp hdet)`.
-/
theorem continuous_absD : Continuous (absD (F := F)) := by
  have hdet : Continuous fun g : GA F 2 => (Matrix.GeneralLinearGroup.det g : IdeleGroup F) := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · change Continuous fun g : GA F 2 => (g : Matrix (Fin 2) (Fin 2) (Ad F)).det
      exact Units.continuous_val.matrix_det
    · have e : ∀ g : GA F 2, ((g⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).det =
          (((Matrix.GeneralLinearGroup.det g)⁻¹ : (Ad F)ˣ) : Ad F) := fun g => by
        rw [← map_inv]
        rfl
      exact (Units.continuous_coe_inv.matrix_det).congr e
  exact continuous_subtype_val.comp (IdeleGroup.continuous_ideleModule.comp hdet)

/- English proof (translation)
The claim follows from `(IdeleGroup.ideleModule F (Matrix.GeneralLinearGroup.det g)).2`.
-/
theorem absD_pos (g : GA F 2) : 0 < absD g := (IdeleGroup.ideleModule F (Matrix.GeneralLinearGroup.det g)).2

/- English proof (translation)
Take `⟨C0, hC0⟩` from `hP F ω c H`. Take `⟨M1, hM1, hθS⟩` from `thetaS_bound H hK`. Take `⟨M2, hM2, hθT⟩` from `thetaT_bound H hK`. Establish `hs_cont : Continuous fun g : GA F 2 => absD g ^ ((1 : ℝ) / 2)` using `continuous_absD.rpow_const fun _ => Or.inr (by norm_num)`. Establish `hs_pos : ∀ g : GA F 2, 0 < absD g ^ ((1 : ℝ) / 2)` using `fun g => Real.rpow_pos_of_pos (absD_pos g) _`.

Take `⟨B1, hB1⟩` from `hK.exists_bound_of_continuousOn hs_cont.continuousOn`. Take `⟨B2, hB2⟩` from `hK.exists_bound_of_continuousOn (hs_cont.inv₀ fun g => (hs_pos g).ne').continuousOn`. Use `⟨M1 * max B1 0 + ‖C0‖ * M2 * max B2 0, fun g hg t u hu => ?_⟩` and prove the remaining obligations. Use `set a := absD g with hadef`. Use `set s := absD g ^ ((1 : ℝ) / 2) with hsdef`.

Establish `ha : 0 < a` using `absD_pos g`. Establish `hs0 : 0 < s` using `hs_pos g`. Establish `hsa : s ^ 2 = a`. Rewrite using `[hsdef, ← Real.sqrt_eq_rpow, Real.sq_sqrt ha.le]`. Establish `hsB1 : s ≤ max B1 0`.

Use `hB1 g hg` as an intermediate fact. Rewrite `this` using `[Real.norm_of_nonneg hs0.le]`. Conclude with `this.trans (le_max_left _ _)`. Establish `hsB2 : s⁻¹ ≤ max B2 0`. Use `hB2 g hg` as an intermediate fact.

Simplify using `only [Pi.inv_apply] at this`. Rewrite `this` using `[Real.norm_of_nonneg (inv_nonneg.2 (hs_pos g).le)]`. Conclude with `this.trans (le_max_left _ _)`. Establish `ht0 : (0 : ℝ) < t` using `t.2`. Establish `hL0 : 0 < (1 + Real.log t ^ 2)⁻¹` using `by positivity`.

Use `set z : IdeleGroup F := moduleSection (w0 F) t * (u : Ideles F) with hzdef`. Establish `hnorm : ‖eisInt ω (Phi c) g t u‖ = ‖thetaS (Phi c) (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g)‖ * t * s`. Simplify using `only [eisInt, norm_mul, norm_inv, norm_omega_eq_one H.fin, inv_one, mul_one, Complex.norm_real, Real.norm_of_nonneg ht0.le]`. Rewrite using `[Real.norm_of_nonneg (hs_pos g).le]`. Rewrite using `[hnorm]`.

Establish `hB10 : 0 ≤ M1 * max B1 0` using `mul_nonneg hM1 (le_max_right _ _)`. Establish `hB20 : 0 ≤ ‖C0‖ * M2 * max B2 0` using `mul_nonneg (mul_nonneg (norm_nonneg _) hM2) (le_max_right _ _)`. Break down `le_total (1 : ℝ) t with h1 | h1` into its components or cases. Establish `hX` using `hθS g hg t h1 u hu`. Combine the equalities or inequalities in the displayed calculation.

Establish `hX` using `hθT g hg t h1 u hu`. Establish `hθ` using `(hC0 (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g)).2.2`. Establish `hdet : absD (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = (t : ℝ) ^ 2 * a`. Rewrite using `[absD_scalar_mul, hzdef, ideleModule_section_mul]`. Establish `hY : ‖thetaS (Phi c) (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g)‖ ≤ ‖C0‖ * ((t : ℝ) ^ 2 * a)⁻¹ * ((t : ℝ) ^ 3 * M2)`.

Rewrite using `[hθ, norm_mul, norm_mul, hdet, Complex.norm_real, Real.norm_of_nonneg (by positivity)]`. Conclude with `mul_le_mul_of_nonneg_left hX (by positivity)`. Establish `hs' : s ≠ 0` using `hs0.ne'`. Establish `ht' : (t : ℝ) ≠ 0` using `ht0.ne'`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem eisInt_bound (hP : SPois) {ω : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (H : Hyp ω c)
    {K : Set (GA F 2)} (hK : IsCompact K) :
    ∃ M : ℝ, ∀ g ∈ K, ∀ t : {r : ℝ // 0 < r}, ∀ u ∈ closure (normOneFundamentalDomain F),
      ‖eisInt ω (Phi c) g t u‖ ≤ M * (1 + Real.log t ^ 2)⁻¹ := by
  obtain ⟨C0, hC0⟩ := hP F ω c H
  obtain ⟨M1, hM1, hθS⟩ := thetaS_bound H hK
  obtain ⟨M2, hM2, hθT⟩ := thetaT_bound H hK
  have hs_cont : Continuous fun g : GA F 2 => absD g ^ ((1 : ℝ) / 2) :=
    continuous_absD.rpow_const fun _ => Or.inr (by norm_num)
  have hs_pos : ∀ g : GA F 2, 0 < absD g ^ ((1 : ℝ) / 2) := fun g => Real.rpow_pos_of_pos (absD_pos g) _
  obtain ⟨B1, hB1⟩ := hK.exists_bound_of_continuousOn hs_cont.continuousOn
  obtain ⟨B2, hB2⟩ := hK.exists_bound_of_continuousOn
    (hs_cont.inv₀ fun g => (hs_pos g).ne').continuousOn
  refine ⟨M1 * max B1 0 + ‖C0‖ * M2 * max B2 0, fun g hg t u hu => ?_⟩
  set a := absD g with hadef
  set s := absD g ^ ((1 : ℝ) / 2) with hsdef
  have ha : 0 < a := absD_pos g
  have hs0 : 0 < s := hs_pos g
  have hsa : s ^ 2 = a := by
    rw [hsdef, ← Real.sqrt_eq_rpow, Real.sq_sqrt ha.le]
  have hsB1 : s ≤ max B1 0 := by
    have := hB1 g hg
    rw [Real.norm_of_nonneg hs0.le] at this
    exact this.trans (le_max_left _ _)
  have hsB2 : s⁻¹ ≤ max B2 0 := by
    have := hB2 g hg
    simp only [Pi.inv_apply] at this
    rw [Real.norm_of_nonneg (inv_nonneg.2 (hs_pos g).le)] at this
    exact this.trans (le_max_left _ _)
  have ht0 : (0 : ℝ) < t := t.2
  have hL0 : 0 < (1 + Real.log t ^ 2)⁻¹ := by positivity
  set z : IdeleGroup F := moduleSection (w0 F) t * (u : Ideles F) with hzdef
  have hnorm : ‖eisInt ω (Phi c) g t u‖ =
      ‖thetaS (Phi c) (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g)‖ * t * s := by
    simp only [eisInt, norm_mul, norm_inv, norm_omega_eq_one H.fin, inv_one, mul_one, Complex.norm_real,
      Real.norm_of_nonneg ht0.le]
    rw [Real.norm_of_nonneg (hs_pos g).le]
  rw [hnorm]
  have hB10 : 0 ≤ M1 * max B1 0 := mul_nonneg hM1 (le_max_right _ _)
  have hB20 : 0 ≤ ‖C0‖ * M2 * max B2 0 := mul_nonneg (mul_nonneg (norm_nonneg _) hM2) (le_max_right _ _)
  rcases le_total (1 : ℝ) t with h1 | h1
  · have hX := hθS g hg t h1 u hu
    calc ‖thetaS (Phi c) (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g)‖ * t * s
        ≤ ((t : ℝ) ^ 3)⁻¹ * M1 * t * max B1 0 :=
          mul_le_mul (mul_le_mul_of_nonneg_right hX ht0.le) hsB1 hs0.le
            (mul_nonneg (mul_nonneg (by positivity) hM1) ht0.le)
      _ = M1 * max B1 0 * ((t : ℝ) ^ 2)⁻¹ := by field_simp; try ring
      _ ≤ M1 * max B1 0 * (1 + Real.log t ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_left (inv_sq_le_of_one_le h1) hB10
      _ ≤ (M1 * max B1 0 + ‖C0‖ * M2 * max B2 0) * (1 + Real.log t ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB20) hL0.le
  · have hX := hθT g hg t h1 u hu
    have hθ := (hC0 (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g)).2.2
    have hdet : absD (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = (t : ℝ) ^ 2 * a := by
      rw [absD_scalar_mul, hzdef, ideleModule_section_mul]
    have hY : ‖thetaS (Phi c) (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g)‖ ≤
        ‖C0‖ * ((t : ℝ) ^ 2 * a)⁻¹ * ((t : ℝ) ^ 3 * M2) := by
      rw [hθ, norm_mul, norm_mul, hdet, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left hX (by positivity)
    have hs' : s ≠ 0 := hs0.ne'
    have ht' : (t : ℝ) ≠ 0 := ht0.ne'
    calc ‖thetaS (Phi c) (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g)‖ * t * s
        ≤ ‖C0‖ * ((t : ℝ) ^ 2 * a)⁻¹ * ((t : ℝ) ^ 3 * M2) * t * s :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hY ht0.le) hs0.le
      _ = ‖C0‖ * M2 * ((t : ℝ) ^ 2 * s⁻¹) := by rw [← hsa]; field_simp; try ring
      _ ≤ ‖C0‖ * M2 * ((1 + Real.log t ^ 2)⁻¹ * max B2 0) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (sq_le_of_le_one ht0 h1) hsB2 (inv_nonneg.2 hs0.le) hL0.le)
            (mul_nonneg (norm_nonneg _) hM2)
      _ = ‖C0‖ * M2 * max B2 0 * (1 + Real.log t ^ 2)⁻¹ := by ring
      _ ≤ (M1 * max B1 0 + ‖C0‖ * M2 * max B2 0) * (1 + Real.log t ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hB10) hL0.le

end UpperTheory.HilbertEisensteinWeightOne.EisensteinIntegrability

namespace UpperTheory.HilbertEisensteinWeightOne

open EisensteinIntegrability in
/- English proof (translation)
Introduce `hP F _ _ _ ω c H g`. Take `⟨M, hM⟩` from `eisInt_bound hP H (isCompact_singleton (x := g))`. Establish `: IsFiniteMeasure ((normOneMeasure F).restrict (normOneFundamentalDomain F))` using `⟨by rw [Measure.restrict_apply_univ]; exact normOneMeasure_normOneFundamentalDomain_lt_top F⟩`. Establish `hE : ∀ᵐ p ∂(posRealMeasure.prod ((normOneMeasure F).restrict (normOneFundamentalDomain F))), p.2 ∈ normOneFundamentalDomain F` using `Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem (measurableSet_normOneFundamentalDomain F))`. Use `Integrable.mono' ((integrable_bound.const_mul M).comp_fst _) (measurable_eisInt H g).aestronglyMeasurable ?_` and prove the remaining obligations.

Use `filter_upwards [hE] with p hp`. Conclude with `hM g rfl p.1 p.2 (subset_closure hp)`.
-/
theorem s_integrality : SPois → SInt := by
  intro hP F _ _ _ ω c H g
  obtain ⟨M, hM⟩ := eisInt_bound hP H (isCompact_singleton (x := g))
  have : IsFiniteMeasure ((normOneMeasure F).restrict (normOneFundamentalDomain F)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact normOneMeasure_normOneFundamentalDomain_lt_top F⟩
  have hE : ∀ᵐ p ∂(posRealMeasure.prod ((normOneMeasure F).restrict (normOneFundamentalDomain F))),
      p.2 ∈ normOneFundamentalDomain F :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem (measurableSet_normOneFundamentalDomain F))
  refine Integrable.mono' ((integrable_bound.const_mul M).comp_fst _)
    (measurable_eisInt H g).aestronglyMeasurable ?_
  filter_upwards [hE] with p hp
  exact hM g rfl p.1 p.2 (subset_closure hp)

end UpperTheory.HilbertEisensteinWeightOne
