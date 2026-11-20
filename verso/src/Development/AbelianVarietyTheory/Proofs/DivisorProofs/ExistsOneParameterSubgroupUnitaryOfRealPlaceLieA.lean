import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FramedDConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieElementsGenerateOneParamLines
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

noncomputable section

namespace GlobalTheory.HoweD
open GlobalTheory.RealLift.OneParam

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ β _ _ R S τ J b C hCM hC Y hY`. Use `hCM.1` as an intermediate fact. Take `⟨ξ, hξ⟩` from `exists_moved hCM`. Establish `hξ' : ∀ w, ((τ w).1 ξ).im ≠ 0` using `fun w => im_ne_zero hCM hξ (τ w).1`. Use `choose C' hC' using fun w => (hC w).2`.

Establish `hL : ∀ w, C' w * C w = 1` using `fun w => frame_inv (hC w).1 (hC' w)`. Use `set G : InfinitePlace F → ℝ → Matrix β β ℂ := fun w t => C w * NormedSpace.exp (t • Y w) * C' w with hG`. Use `set f : ℝ → Matrix β β (AE F E) := fun t => 1 + liftM τ ξ (fun w => G w t - 1) with hf`. Establish `hfπ : ∀ t w, (f t).map (piInf (τ w)) = G w t` using `fun t w => by`. Rewrite using `[hf, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), OneParam.liftM_map τ hξ', add_sub_cancel]`.

Establish `hfat : ∀ t, At (evI F) (f t - 1)` using `fun t => by`. Rewrite using `[hf, add_sub_cancel_left]`. Conclude with `at_liftM τ ξ _`. Establish `hfadd : ∀ s t, f (s + t) = f s * f t` using `fun s t => by`. Use `(eq_of_at hCM τ ?_ fun w => ?_).symm` and prove the remaining obligations.

Establish `e : f s * f t - f (s + t) = (f s - 1) * f t + (f t - 1) - (f (s + t) - 1)` using `by noncomm_ring`. Rewrite using `[e]`. Conclude with `at_sub (at_add (at_mul_right (hfat s) _) (hfat t)) (hfat _)`. Rewrite using `[Matrix.map_mul, hfπ, hfπ, hfπ]`. Conclude with `(conj_add (hL w) (Y w) s t).symm`.

Establish `hf0 : f 0 = 1`. Use `eq_of_at hCM τ (hfat 0) fun w => ?_` and prove the remaining obligations. Rewrite using `[hfπ, Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `conj_zero (hC' w) (Y w)`. Establish `hfU : ∀ t, (f t)ᵀ * J * (f t).map (cA σ) = J` using `fun t => by`.

Use `eq_of_at hCM τ ?_ fun w => ?_` and prove the remaining obligations. Establish `e : (f t)ᵀ * J * (f t).map (cA σ) - J = (f t - 1)ᵀ * J * (f t).map (cA σ) + J * (f t - 1).map (cA σ)`. Establish `e1 : (f t - 1).map (cA σ) = (f t).map (cA σ) - 1`. Rewrite using `[Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]`. Rewrite using `[e1, Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `at_add (at_mul_right (at_mul_right (at_transpose (hfat t)) _) _) (at_mul_left (at_map_cA σ (hfat t)) _)`. Establish `hc : ((f t).map (cA σ)).map (piInf (τ w)) = (G w t).map star`. Rewrite using `[← hfπ t w, Matrix.map_map, Matrix.map_map]`.

Use `congr 1`. Use function extensionality and compare the values at `z`. Conclude with `piInf_cA hCM (τ w) z`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, hc, Matrix.transpose_map, hfπ]`. Distinguish the cases in `hb : b = 0`.

Use `haveI := isEmpty_of_zero (hb ▸ (hC w).1) (hC' w)`. Use extensionality with `i`. Conclude with `isEmptyElim i`. Establish `h1` using `conj_unitary (hC w).1 (hC' w) (hY w) t`. Rewrite `h1` using `[Matrix.mul_smul, Matrix.smul_mul]`.

Conclude with `smul_right_injective _ hb h1`. Use `haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)`. Establish `hfc : Continuous f` using `continuous_const.add ((continuous_liftM τ ξ).comp (continuous_pi fun w => (((continuous_const.matrix_mul (continuous_exp_smul (Y w))).matrix_mul continuous_const).sub continuous_const)))`. Set `g : ℝ → UG (cA σ) J` to `fun t => ⟨⟨f t, f (-t), by rw [← hfadd, add_neg_cancel, hf0], by rw [← hfadd, neg_add_cancel, hf0]⟩, hfU t⟩`. Set `γ : Multiplicative ℝ →* UG (cA σ) J` to `{ toFun := fun t => g (Multiplicative.toAdd t) map_one' := Subtype.ext (Units.ext hf0) map_mul' := fun x y => Subtype.ext (Units.ext (hfadd _ _)) }`.

Use `⟨γ, ⟨?_, fun t => hfat _⟩, fun t w => ?_⟩` and prove the remaining obligations. Establish `hu : Continuous fun t : Multiplicative ℝ => ((g (Multiplicative.toAdd t)).1 : GL β (AE F E))` using `Units.continuous_iff.2 ⟨hfc.comp continuous_toAdd, (hfc.comp continuous_neg).comp continuous_toAdd⟩`. Conclude with `hu.subtype_mk _`. Express the relevant statement in the definitionally equal form `(f t).map (piInf (τ w)) * C w = C w * NormedSpace.exp (t • Y w)`. Rewrite using `[hfπ, hG]`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[hL, Matrix.mul_one]`.
-/
theorem exists_line_of_upqD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type) [Fintype β]
    [DecidableEq β] (R S : InfinitePlace F → ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (AE F E)) (b : ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ), IsCMExt F E σ → (∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) →
    ∀ Y : ∀ w : InfinitePlace F, Mat (R w) (S w), (∀ w, Y w ∈ upq (R w) (S w)) → ∃ γ ∈ RLines σ J, IsGenD τ C γ Y := by
  intro F E _ _ _ _ _ σ β _ _ R S τ J b C hCM hC Y hY
  have := hCM.1
  obtain ⟨ξ, hξ⟩ := exists_moved hCM
  have hξ' : ∀ w, ((τ w).1 ξ).im ≠ 0 := fun w => im_ne_zero hCM hξ (τ w).1
  choose C' hC' using fun w => (hC w).2
  have hL : ∀ w, C' w * C w = 1 := fun w => frame_inv (hC w).1 (hC' w)
  set G : InfinitePlace F → ℝ → Matrix β β ℂ := fun w t => C w * NormedSpace.exp (t • Y w) * C' w with hG
  set f : ℝ → Matrix β β (AE F E) := fun t => 1 + liftM τ ξ (fun w => G w t - 1) with hf
  have hfπ : ∀ t w, (f t).map (piInf (τ w)) = G w t := fun t w => by
    rw [hf, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), OneParam.liftM_map τ hξ', add_sub_cancel]
  have hfat : ∀ t, At (evI F) (f t - 1) := fun t => by
    rw [hf, add_sub_cancel_left]
    exact at_liftM τ ξ _
  have hfadd : ∀ s t, f (s + t) = f s * f t := fun s t => by
    refine (eq_of_at hCM τ ?_ fun w => ?_).symm
    · have e : f s * f t - f (s + t) = (f s - 1) * f t + (f t - 1) - (f (s + t) - 1) := by noncomm_ring
      rw [e]
      exact at_sub (at_add (at_mul_right (hfat s) _) (hfat t)) (hfat _)
    · rw [Matrix.map_mul, hfπ, hfπ, hfπ]
      exact (conj_add (hL w) (Y w) s t).symm
  have hf0 : f 0 = 1 := by
    refine eq_of_at hCM τ (hfat 0) fun w => ?_
    rw [hfπ, Matrix.map_one _ (map_zero _) (map_one _)]
    exact conj_zero (hC' w) (Y w)
  have hfU : ∀ t, (f t)ᵀ * J * (f t).map (cA σ) = J := fun t => by
    refine eq_of_at hCM τ ?_ fun w => ?_
    · have e : (f t)ᵀ * J * (f t).map (cA σ) - J =
          (f t - 1)ᵀ * J * (f t).map (cA σ) + J * (f t - 1).map (cA σ) := by
        have e1 : (f t - 1).map (cA σ) = (f t).map (cA σ) - 1 := by
          rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
        rw [e1, Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul,
          Matrix.mul_sub, Matrix.mul_one]
        abel
      rw [e]
      exact at_add (at_mul_right (at_mul_right (at_transpose (hfat t)) _) _)
        (at_mul_left (at_map_cA σ (hfat t)) _)
    · have hc : ((f t).map (cA σ)).map (piInf (τ w)) = (G w t).map star := by
        rw [← hfπ t w, Matrix.map_map, Matrix.map_map]
        congr 1
        funext z
        exact piInf_cA hCM (τ w) z
      rw [Matrix.map_mul, Matrix.map_mul, hc, Matrix.transpose_map, hfπ]
      by_cases hb : b = 0
      · haveI := isEmpty_of_zero (hb ▸ (hC w).1) (hC' w)
        ext i
        exact isEmptyElim i
      · have h1 := conj_unitary (hC w).1 (hC' w) (hY w) t
        rw [Matrix.mul_smul, Matrix.smul_mul] at h1
        exact smul_right_injective _ hb h1
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  have hfc : Continuous f :=
    continuous_const.add ((continuous_liftM τ ξ).comp (continuous_pi fun w =>
      (((continuous_const.matrix_mul (continuous_exp_smul (Y w))).matrix_mul continuous_const).sub continuous_const)))
  let g : ℝ → UG (cA σ) J := fun t => ⟨⟨f t, f (-t), by rw [← hfadd, add_neg_cancel, hf0],
    by rw [← hfadd, neg_add_cancel, hf0]⟩, hfU t⟩
  let γ : Multiplicative ℝ →* UG (cA σ) J :=
    { toFun := fun t => g (Multiplicative.toAdd t)
      map_one' := Subtype.ext (Units.ext hf0)
      map_mul' := fun x y => Subtype.ext (Units.ext (hfadd _ _)) }
  refine ⟨γ, ⟨?_, fun t => hfat _⟩, fun t w => ?_⟩
  · have hu : Continuous fun t : Multiplicative ℝ => ((g (Multiplicative.toAdd t)).1 : GL β (AE F E)) :=
      Units.continuous_iff.2 ⟨hfc.comp continuous_toAdd, (hfc.comp continuous_neg).comp continuous_toAdd⟩
    exact hu.subtype_mk _
  · change (f t).map (piInf (τ w)) * C w = C w * NormedSpace.exp (t • Y w)
    rw [hfπ, hG]
    simp only [Matrix.mul_assoc]
    rw [hL, Matrix.mul_one]

end GlobalTheory.HoweD
