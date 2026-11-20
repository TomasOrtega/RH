import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.IdeleModuleInfIdDetLe

noncomputable section

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.eisensteinGrowth

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def mn (M : Matrix (Fin 2) (Fin 2) (Ad F)) : ℝ := ∑ i, ∑ j, ‖UpperTheory.V.TR.pInf F (M i j)‖

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pLoc_pFin_algebraMap (w : HeightOneSpectrum (𝓞 F)) (x : F) :
    pLoc F w (pFin F (algebraMap F (Ad F) x)) = algebraMap F (w.adicCompletion F) x := rfl

/- English proof (translation)
Rewrite using `[Units.val_mul, map_mul]`. Establish `h1 : pFin F ((moduleSection (w0 F) t : Ideles F) : Ad F) = 1`. Rewrite using `[coe_moduleSection]`. Both sides reduce to the same expression. Rewrite using `[h1, one_mul]`.
-/
theorem pFin_moduleSection_mul (t : {r : ℝ // 0 < r}) (a : Ideles F) :
    pFin F ((moduleSection (w0 F) t * a : Ideles F) : Ad F) = pFin F (a : Ad F) := by
  rw [Units.val_mul, map_mul]
  have h1 : pFin F ((moduleSection (w0 F) t : Ideles F) : Ad F) = 1 := by
    rw [coe_moduleSection]; rfl
  rw [h1, one_mul]

/- English proof (translation)
Rewrite using `[mul_inv, ← map_inv, pFin_moduleSection_mul]`.
-/
theorem pFin_inv_moduleSection_mul (t : {r : ℝ // 0 < r}) (a : Ideles F) :
    pFin F (((moduleSection (w0 F) t * a)⁻¹ : Ideles F) : Ad F) = pFin F ((a⁻¹ : Ideles F) : Ad F) := by
  rw [mul_inv, ← map_inv, pFin_moduleSection_mul]

/- English proof (translation)
Rewrite using `[Matrix.vecMul_vecMul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Units.mul_inv, one_smul, hM, Matrix.vecMul_one]`.
-/
theorem rowA_eq (ξ : Fin 2 → F) (z : Ideles F) (M M' : Matrix (Fin 2) (Fin 2) (Ad F)) (hM : M * M' = 1) :
    rowA ξ = (rowA ξ ᵥ* ((z : Ad F) • M)) ᵥ* (((z⁻¹ : Ideles F) : Ad F) • M') := by
  rw [Matrix.vecMul_vecMul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Units.mul_inv, one_smul, hM,
    Matrix.vecMul_one]

/- English proof (translation)
Use `set S : Set (Af F) := ⋃ i : Fin 2, ⋃ j : Fin 2, (fun a : Ideles F => pFin F ((a⁻¹ : Ideles F) : Ad F) * Mf' i j) '' K with hSdef`. Establish `hS : IsCompact S`. Use `isCompact_iUnion fun i => isCompact_iUnion fun j => hK.image ?_` and prove the remaining obligations. Establish `hc : Continuous fun a : Ideles F => pFin F ((a⁻¹ : Ideles F) : Ad F)` using `(continuous_snd : Continuous (Prod.snd : InfiniteAdeleRing F × Af F → Af F)).comp (Units.continuous_coe_inv (M := Ad F))`. Conclude with `hc.mul continuous_const`.

Take `⟨D1, hD10, hD1⟩` from `exists_mul_mem_integralFiniteAdeles_of_isCompact hS`. Use `⟨D * D1, mul_ne_zero hD0 hD10, fun a ha t ξ M M' hM hMf hbox j => ?_⟩` and prove the remaining obligations. Use `set z : Ideles F := moduleSection (w0 F) t * a`. Use `set v := rowA ξ ᵥ* ((z : Ad F) • M)`. Establish `hrow` using `congrFun (rowA_eq ξ z M M' hM) j`.

Establish `hval : ∀ w : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (w.adicCompletion F) (((D * D1 : 𝓞 F) : F) * ξ j)) ≤ 1`. Introduce `w`. Establish `h1 : algebraMap F (w.adicCompletion F) (ξ j) = ∑ i, pLoc F w (pFin F (v i)) * (pLoc F w (pFin F ((a⁻¹ : Ideles F) : Ad F)) * pLoc F w (Mf' i j))`. Rewrite using `[← pLoc_pFin_algebraMap]`. Express the relevant statement in the definitionally equal form `pLoc F w (pFin F (rowA ξ j)) = _`.

Rewrite using `[hrow]`. Simplify using `only [Matrix.vecMul, dotProduct, Matrix.smul_apply, smul_eq_mul, map_sum, map_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[pFin_inv_moduleSection_mul]`. Use `congr 2`.

Rewrite using `[← hMf]`. Both sides reduce to the same expression. Rewrite using `[map_mul, h1, Finset.mul_sum]`. Use `Valuation.map_sum_le _ fun i _ => ?_` and prove the remaining obligations. Establish `hA : Valued.v (algebraMap F (w.adicCompletion F) (D : F) * pLoc F w (pFin F (v i))) ≤ 1` using `hD w _ (hbox w i)`.

Establish `hs : pFin F ((a⁻¹ : Ideles F) : Ad F) * Mf' i j ∈ S`. Rewrite using `[hSdef]`. Conclude with `Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, ⟨a, ha, rfl⟩⟩⟩`. Establish `hB : Valued.v (algebraMap F (w.adicCompletion F) (D1 : F) * (pLoc F w (pFin F ((a⁻¹ : Ideles F) : Ad F)) * pLoc F w (Mf' i j))) ≤ 1`. Use `hD1 _ hs w` as an intermediate fact.

Rewrite `this` using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Conclude with `this`. Establish `hc : ((D * D1 : 𝓞 F) : F) = (D : F) * (D1 : F)` using `by simp`. Establish `key : algebraMap F (w.adicCompletion F) ((D * D1 : 𝓞 F) : F) * (pLoc F w (pFin F (v i)) * (pLoc F w (pFin F ((a⁻¹ : Ideles F) : Ad F)) * pLoc F w (Mf' i j))) = (algebraMap F (w.adicCompletion F) (D : F) * pLoc F w (pFin F (v i))) * (algebraMap F (w.adicCompletion F) (D1 : F) * (p …`. Rewrite using `[hc, map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key, map_mul]`. Conclude with `(mul_le_mul' hA hB).trans_eq (one_mul 1)`. Take `⟨r, hr⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F (((D * D1 : 𝓞 F) : F) * ξ j) fun w => (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).symm.trans_le (hval w)`. Conclude with `⟨r, hr.symm⟩`.
-/
theorem fin_part {e : HeightOneSpectrum (𝓞 F) → ℤ} (D : 𝓞 F)
    (hD : ∀ w, ∀ x : w.adicCompletion F, Valued.v x ≤ WithZero.exp (e w) →
      Valued.v (algebraMap F (w.adicCompletion F) (D : F) * x) ≤ 1)
    {K : Set (Ideles F)} (hK : IsCompact K) (Mf' : Matrix (Fin 2) (Fin 2) (Af F)) (hD0 : D ≠ 0) :
    ∃ D' : 𝓞 F, D' ≠ 0 ∧ ∀ a ∈ K, ∀ t : {r : ℝ // 0 < r}, ∀ (ξ : Fin 2 → F) (M M' : Matrix (Fin 2) (Fin 2) (Ad F)),
      M * M' = 1 → M'.map (pFin F) = Mf' →
      boxP e (rowA ξ ᵥ* (((moduleSection (w0 F) t * a : Ideles F) : Ad F) • M)) →
      ∀ j, ∃ r : 𝓞 F, (D' : F) * ξ j = r := by
  classical
  set S : Set (Af F) := ⋃ i : Fin 2, ⋃ j : Fin 2,
    (fun a : Ideles F => pFin F ((a⁻¹ : Ideles F) : Ad F) * Mf' i j) '' K with hSdef
  have hS : IsCompact S := by
    refine isCompact_iUnion fun i => isCompact_iUnion fun j => hK.image ?_
    have hc : Continuous fun a : Ideles F => pFin F ((a⁻¹ : Ideles F) : Ad F) :=
      (continuous_snd : Continuous (Prod.snd : InfiniteAdeleRing F × Af F → Af F)).comp
        (Units.continuous_coe_inv (M := Ad F))
    exact hc.mul continuous_const
  obtain ⟨D1, hD10, hD1⟩ := exists_mul_mem_integralFiniteAdeles_of_isCompact hS
  refine ⟨D * D1, mul_ne_zero hD0 hD10, fun a ha t ξ M M' hM hMf hbox j => ?_⟩
  set z : Ideles F := moduleSection (w0 F) t * a
  set v := rowA ξ ᵥ* ((z : Ad F) • M)
  have hrow := congrFun (rowA_eq ξ z M M' hM) j
  have hval : ∀ w : HeightOneSpectrum (𝓞 F),
      Valued.v (algebraMap F (w.adicCompletion F) (((D * D1 : 𝓞 F) : F) * ξ j)) ≤ 1 := by
    intro w
    have h1 : algebraMap F (w.adicCompletion F) (ξ j) =
        ∑ i, pLoc F w (pFin F (v i)) * (pLoc F w (pFin F ((a⁻¹ : Ideles F) : Ad F)) * pLoc F w (Mf' i j)) := by
      rw [← pLoc_pFin_algebraMap]
      change pLoc F w (pFin F (rowA ξ j)) = _
      rw [hrow]
      simp only [Matrix.vecMul, dotProduct, Matrix.smul_apply, smul_eq_mul, map_sum, map_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pFin_inv_moduleSection_mul]
      congr 2
      rw [← hMf]
      rfl
    rw [map_mul, h1, Finset.mul_sum]
    refine Valuation.map_sum_le _ fun i _ => ?_
    have hA : Valued.v (algebraMap F (w.adicCompletion F) (D : F) * pLoc F w (pFin F (v i))) ≤ 1 :=
      hD w _ (hbox w i)
    have hs : pFin F ((a⁻¹ : Ideles F) : Ad F) * Mf' i j ∈ S := by
      rw [hSdef]
      exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, ⟨a, ha, rfl⟩⟩⟩
    have hB : Valued.v (algebraMap F (w.adicCompletion F) (D1 : F) *
        (pLoc F w (pFin F ((a⁻¹ : Ideles F) : Ad F)) * pLoc F w (Mf' i j))) ≤ 1 := by
      have := hD1 _ hs w
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at this
      exact this
    have hc : ((D * D1 : 𝓞 F) : F) = (D : F) * (D1 : F) := by simp
    have key : algebraMap F (w.adicCompletion F) ((D * D1 : 𝓞 F) : F) *
        (pLoc F w (pFin F (v i)) * (pLoc F w (pFin F ((a⁻¹ : Ideles F) : Ad F)) * pLoc F w (Mf' i j))) =
        (algebraMap F (w.adicCompletion F) (D : F) * pLoc F w (pFin F (v i))) *
          (algebraMap F (w.adicCompletion F) (D1 : F) *
            (pLoc F w (pFin F ((a⁻¹ : Ideles F) : Ad F)) * pLoc F w (Mf' i j))) := by
      rw [hc, map_mul]
      ring
    rw [key, map_mul]
    exact (mul_le_mul' hA hB).trans_eq (one_mul 1)
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F
    (((D * D1 : 𝓞 F) : F) * ξ j) fun w =>
      (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).symm.trans_le (hval w)
  exact ⟨r, hr.symm⟩

/- English proof (translation)
Unfold `mn`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem entry_le_mn (B : Matrix (Fin 2) (Fin 2) (Ad F)) (i j : Fin 2) :
    ‖UpperTheory.V.TR.pInf F (B i j)‖ ≤ mn B := by
  unfold mn
  calc ‖UpperTheory.V.TR.pInf F (B i j)‖ ≤ ∑ j', ‖UpperTheory.V.TR.pInf F (B i j')‖ :=
        Finset.single_le_sum (f := fun j' => ‖UpperTheory.V.TR.pInf F (B i j')‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖UpperTheory.V.TR.pInf F (B i' j')‖ :=
        Finset.single_le_sum (f := fun i' => ∑ j', ‖UpperTheory.V.TR.pInf F (B i' j')‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)

/- English proof (translation)
The claim follows from `Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _`.
-/
theorem mn_nonneg (B : Matrix (Fin 2) (Fin 2) (Ad F)) : 0 ≤ mn B :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

/- English proof (translation)
Unfold `mn`. Rewrite using `[Finset.sum_comm]`. Both sides reduce to the same expression.
-/
theorem mn_transpose (B : Matrix (Fin 2) (Fin 2) (Ad F)) : mn B.transpose = mn B := by
  unfold mn
  rw [Finset.sum_comm]
  rfl

/- English proof (translation)
Establish `hH : 0 ≤ H` using `(norm_nonneg _).trans (hA 0 0)`. Establish `h : ∀ i j, ‖UpperTheory.V.TR.pInf F ((A * B) i j)‖ ≤ 2 * H * mn B`. Introduce `i j`. Rewrite using `[Matrix.mul_apply, map_sum]`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_mul]`. Conclude with `(norm_mul_le _ _).trans (mul_le_mul (hA i k) (entry_le_mn B k j) (norm_nonneg _) hH)`. Apply the tactic sequence `_ = 2 * H * mn B := by simp [Finset.sum_const]; try ring`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem mn_mul_le_left (A B : Matrix (Fin 2) (Fin 2) (Ad F)) (H : ℝ)
    (hA : ∀ i k, ‖UpperTheory.V.TR.pInf F (A i k)‖ ≤ H) : mn (A * B) ≤ 8 * H * mn B := by
  have hH : 0 ≤ H := (norm_nonneg _).trans (hA 0 0)
  have h : ∀ i j, ‖UpperTheory.V.TR.pInf F ((A * B) i j)‖ ≤ 2 * H * mn B := by
    intro i j
    rw [Matrix.mul_apply, map_sum]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k, ‖UpperTheory.V.TR.pInf F (A i k * B k j)‖ ≤ ∑ _k : Fin 2, H * mn B :=
          Finset.sum_le_sum fun k _ => by
            rw [map_mul]
            exact (norm_mul_le _ _).trans (mul_le_mul (hA i k) (entry_le_mn B k j) (norm_nonneg _) hH)
      _ = 2 * H * mn B := by simp [Finset.sum_const]; try ring
  calc mn (A * B) ≤ ∑ _i : Fin 2, ∑ _j : Fin 2, 2 * H * mn B :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j
    _ = 8 * H * mn B := by simp [Finset.sum_const]; try ring

/- English proof (translation)
Establish `hH : 0 ≤ H` using `(norm_nonneg _).trans (hB 0 0)`. Establish `h : ∀ i j, ‖UpperTheory.V.TR.pInf F ((A * B) i j)‖ ≤ 2 * H * mn A`. Introduce `i j`. Rewrite using `[Matrix.mul_apply, map_sum]`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_mul, mul_comm H]`. Conclude with `(norm_mul_le _ _).trans (mul_le_mul (entry_le_mn A i k) (hB k j) (norm_nonneg _) (mn_nonneg A))`. Apply the tactic sequence `_ = 2 * H * mn A := by simp [Finset.sum_const]; try ring`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem mn_mul_le_right (A B : Matrix (Fin 2) (Fin 2) (Ad F)) (H : ℝ)
    (hB : ∀ k j, ‖UpperTheory.V.TR.pInf F (B k j)‖ ≤ H) : mn (A * B) ≤ 8 * H * mn A := by
  have hH : 0 ≤ H := (norm_nonneg _).trans (hB 0 0)
  have h : ∀ i j, ‖UpperTheory.V.TR.pInf F ((A * B) i j)‖ ≤ 2 * H * mn A := by
    intro i j
    rw [Matrix.mul_apply, map_sum]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k, ‖UpperTheory.V.TR.pInf F (A i k * B k j)‖ ≤ ∑ _k : Fin 2, H * mn A :=
          Finset.sum_le_sum fun k _ => by
            rw [map_mul, mul_comm H]
            exact (norm_mul_le _ _).trans (mul_le_mul (entry_le_mn A i k) (hB k j) (norm_nonneg _) (mn_nonneg A))
      _ = 2 * H * mn A := by simp [Finset.sum_const]; try ring
  calc mn (A * B) ≤ ∑ _i : Fin 2, ∑ _j : Fin 2, 2 * H * mn A :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j
    _ = 8 * H * mn A := by simp [Finset.sum_const]; try ring

/- English proof (translation)
Use `Matrix.GeneralLinearGroup.map_apply (UpperTheory.V.TR.pInf F) i k (UpperTheory.V.TR.infGL F 2 y)` as an intermediate fact. Rewrite `this` using `[UpperTheory.V.TR.pInf_infGL]`. Rewrite using `[← this]`. Establish `h1 : ‖(y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) i k‖ ≤ ‖UpperTheory.V.TR.toL (y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F))‖` using `(norm_le_pi_norm _ k).trans (norm_le_pi_norm _ i)`. Establish `h2` using `norm_nonneg (UpperTheory.V.TR.toL ((y⁻¹ : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)))`.

Unfold `UpperTheory.V.TR.height`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_pInf_infGL_le (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) (i k : Fin 2) :
    ‖UpperTheory.V.TR.pInf F (((UpperTheory.V.TR.infGL F 2 y : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) i k)‖ ≤
      UpperTheory.V.TR.height y := by
  have := Matrix.GeneralLinearGroup.map_apply (UpperTheory.V.TR.pInf F) i k (UpperTheory.V.TR.infGL F 2 y)
  rw [UpperTheory.V.TR.pInf_infGL] at this
  rw [← this]
  have h1 : ‖(y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) i k‖ ≤
      ‖UpperTheory.V.TR.toL (y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F))‖ :=
    (norm_le_pi_norm _ k).trans (norm_le_pi_norm _ i)
  have h2 := norm_nonneg (UpperTheory.V.TR.toL ((y⁻¹ : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)))
  unfold UpperTheory.V.TR.height
  linarith

/- English proof (translation)
Unfold `UpperTheory.V.TR.height`. Rewrite using `[inv_inv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem height_inv (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) : UpperTheory.V.TR.height y⁻¹ = UpperTheory.V.TR.height y := by
  unfold UpperTheory.V.TR.height
  rw [inv_inv]
  ring

/- English proof (translation)
Use `⟨8 * (mn (g⁻¹ : GA F 2).val + mn (g : GA F 2).val), mul_nonneg (by norm_num) (add_nonneg (mn_nonneg _) (mn_nonneg _)), fun y => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Establish `hH` using `one_le_height y`. Rewrite using `[mul_inv_rev, ← map_inv, Units.val_mul]`. Use `(mn_mul_le_left _ _ _ fun i k => (norm_pInf_infGL_le y⁻¹ i k).trans (height_inv y).le).trans ?_` and prove the remaining obligations. Use polynomial arithmetic with `[mn_nonneg (g⁻¹ : GA F 2).val, mn_nonneg (g : GA F 2).val]`.

Establish `hH` using `one_le_height y`. Rewrite using `[mn_transpose, Units.val_mul]`. Use `(mn_mul_le_right _ _ _ fun k j => norm_pInf_infGL_le y k j).trans ?_` and prove the remaining obligations. Use polynomial arithmetic with `[mn_nonneg (g⁻¹ : GA F 2).val, mn_nonneg (g : GA F 2).val]`.
-/
theorem mn_bound (g : GA F 2) : ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ y : GL (Fin 2) (UpperTheory.V.TR.Rinf F),
    mn ((g * UpperTheory.V.TR.infGL F 2 y)⁻¹ : GA F 2).val ≤ Cm * UpperTheory.V.TR.height y ∧
    mn (g * UpperTheory.V.TR.infGL F 2 y : GA F 2).val.transpose ≤ Cm * UpperTheory.V.TR.height y := by
  refine ⟨8 * (mn (g⁻¹ : GA F 2).val + mn (g : GA F 2).val),
    mul_nonneg (by norm_num) (add_nonneg (mn_nonneg _) (mn_nonneg _)), fun y => ⟨?_, ?_⟩⟩
  · have hH := one_le_height y
    rw [mul_inv_rev, ← map_inv, Units.val_mul]
    refine (mn_mul_le_left _ _ _ fun i k => (norm_pInf_infGL_le y⁻¹ i k).trans (height_inv y).le).trans ?_
    nlinarith [mn_nonneg (g⁻¹ : GA F 2).val, mn_nonneg (g : GA F 2).val]
  · have hH := one_le_height y
    rw [mn_transpose, Units.val_mul]
    refine (mn_mul_le_right _ _ _ fun k j => norm_pInf_infGL_le y k j).trans ?_
    nlinarith [mn_nonneg (g⁻¹ : GA F 2).val, mn_nonneg (g : GA F 2).val]

end UpperTheory.HilbertEisensteinWeightOne.eisensteinGrowth
