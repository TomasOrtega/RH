import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HermExpand

noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace BL

section cont
variable {p m : ℕ}

/- English proof (translation)
Distinguish the cases in `h : c`. Simplify using `only [h, if_true]`. Conclude with `hf`. Simplify using `only [h, if_false]`. Conclude with `continuous_const`.
-/
theorem cont_ite {β : Type} [TopologicalSpace β] [Zero β] (c : Prop) [Decidable c] {f : Xp p m → β}
    (hf : Continuous f) : Continuous (fun x => if c then f x else 0) := by
  by_cases h : c
  · simp only [h, if_true]; exact hf
  · simp only [h, if_false]; exact continuous_const

/- English proof (translation)
Unfold `Lsq`. Conclude with `continuous_const.add (continuous_finsetSum _ fun j _ => cont_ite _ (((continuous_apply j).comp continuous_fst).norm.pow 2))`.
-/
theorem cont_Lsq (l : Fin (p + 1)) : Continuous (fun x : Xp p m => Lsq x l) := by
  unfold Lsq
  exact continuous_const.add (continuous_finsetSum _ fun j _ =>
    cont_ite _ (((continuous_apply j).comp continuous_fst).norm.pow 2))

/- English proof (translation)
Unfold `rhoSq`. Use `((cont_Lsq _).add (continuous_finsetSum _ fun i _ => ?_)).add (continuous_finsetSum _ fun j _ => ?_)` and prove the remaining obligations. Conclude with `((continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))).norm.pow 2`. Conclude with `cont_ite _ (((continuous_apply j).comp (continuous_fst.comp continuous_snd)).norm.pow 2)`.
-/
theorem cont_rhoSq (l : Fin (p + 1)) : Continuous (fun x : Xp p m => rhoSq x l) := by
  unfold rhoSq
  refine ((cont_Lsq _).add (continuous_finsetSum _ fun i _ => ?_)).add (continuous_finsetSum _ fun j _ => ?_)
  · exact ((continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))).norm.pow 2
  · exact cont_ite _ (((continuous_apply j).comp (continuous_fst.comp continuous_snd)).norm.pow 2)

/- English proof (translation)
Unfold `bco`. Use `((Complex.continuous_ofReal.comp ((continuous_finsetSum _ fun i _ => ?_).neg.div_const 2)).add ((Complex.continuous_ofReal.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))).mul continuous_const)).sub (continuous_finsetSum _ fun j _ => ?_)` and prove the remaining obligations. Conclude with `((continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))).norm.pow 2`. Conclude with `cont_ite _ (((continuous_apply j).comp (continuous_fst.comp continuous_snd)).mul ((continuous_apply j).comp continuous_fst).star)`.
-/
theorem cont_bco (l : Fin (p + 1)) : Continuous (fun x : Xp p m => bco x l) := by
  unfold bco
  refine ((Complex.continuous_ofReal.comp ((continuous_finsetSum _ fun i _ => ?_).neg.div_const 2)).add
    ((Complex.continuous_ofReal.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))).mul
      continuous_const)).sub (continuous_finsetSum _ fun j _ => ?_)
  · exact ((continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))).norm.pow 2
  · exact cont_ite _ (((continuous_apply j).comp (continuous_fst.comp continuous_snd)).mul
      ((continuous_apply j).comp continuous_fst).star)

/- English proof (translation)
Unfold `de`. Conclude with `Real.continuous_sqrt.comp (((cont_Lsq l).mul (cont_rhoSq l)).add ((cont_bco l).norm.pow 2))`.
-/
theorem cont_de (l : Fin (p + 1)) : Continuous (fun x : Xp p m => de x l) := by
  unfold de
  exact Real.continuous_sqrt.comp (((cont_Lsq l).mul (cont_rhoSq l)).add ((cont_bco l).norm.pow 2))

/- English proof (translation)
Unfold `linF`. Use `(continuous_finsetSum _ fun j _ => ?_).add (continuous_finsetSum _ fun i _ => ?_)` and prove the remaining obligations. Conclude with `(((continuous_apply j).comp continuous_fst).mul continuous_const).add (((continuous_apply j).comp (continuous_fst.comp continuous_snd)).mul continuous_const)`. Conclude with `((continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))).mul continuous_const`.
-/
theorem cont_linF (η η' : Fin p → ℂ) (ζ : Fin m → ℂ) : Continuous (fun x : Xp p m => linF η η' ζ x) := by
  unfold linF
  refine (continuous_finsetSum _ fun j _ => ?_).add (continuous_finsetSum _ fun i _ => ?_)
  · exact (((continuous_apply j).comp continuous_fst).mul continuous_const).add
      (((continuous_apply j).comp (continuous_fst.comp continuous_snd)).mul continuous_const)
  · exact ((continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))).mul continuous_const

def GI (s : Fin (p + 1) → ℝ) (δ : ℝ) (η η' : Fin p → ℂ) (ζ : Fin m → ℂ) (c₀ : ℝ) (x : Xp p m) : ℝ≥0∞ :=
  (∏ l, ENNReal.ofReal (de x l ^ (-s l))) * ENNReal.ofReal ((1 + |2 * (linF η η' ζ x).im + c₀|) ^ (-δ))

/- English proof (translation)
Unfold `GI`. Use `(Finset.measurable_prod _ fun l _ => ?_).mul ?_` and prove the remaining obligations. Conclude with `ENNReal.measurable_ofReal.comp ((cont_de l).measurable.pow_const _)`. Conclude with `ENNReal.measurable_ofReal.comp ((continuous_const.add ((continuous_const.mul (Complex.continuous_im.comp (cont_linF η η' ζ))).add continuous_const).abs).measurable.pow_const _)`.
-/
theorem meas_GI (s : Fin (p + 1) → ℝ) (δ : ℝ) (η η' : Fin p → ℂ) (ζ : Fin m → ℂ) (c₀ : ℝ) :
    Measurable (GI s δ η η' ζ c₀) := by
  unfold GI
  refine (Finset.measurable_prod _ fun l _ => ?_).mul ?_
  · exact ENNReal.measurable_ofReal.comp ((cont_de l).measurable.pow_const _)
  · exact ENNReal.measurable_ofReal.comp ((continuous_const.add ((continuous_const.mul
      (Complex.continuous_im.comp (cont_linF η η' ζ))).add continuous_const).abs).measurable.pow_const _)

end cont

/- English proof (translation)
Use `set f : (Fin N → ℂ) →ₗ[ℝ] (Fin N → ℂ) := (Matrix.toLin' U).restrictScalars ℝ with hf`. Establish `hfU : (fun y : Fin N → ℂ => U *ᵥ y) = ⇑f` using `by funext y; simp [hf, Matrix.toLin'_apply]`. Establish `hn : ((Complex.normSq U.det : ℝ) : ℂ) = 1`. Establish `h` using `congrArg Matrix.det hU`. Rewrite `h` using `[Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one]`.

Rewrite using `[Complex.normSq_eq_conj_mul_self]`. Conclude with `h`. Establish `hdet : LinearMap.det f = 1`. Rewrite using `[hf, LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply]`. Conclude with `hn` after adjusting the coercions.

Rewrite using `[hfU]`. Use `⟨f.continuous_of_finiteDimensional.measurable, ?_⟩` and prove the remaining obligations. Rewrite using `[Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hdet]; norm_num), hdet]`. Simplify using the standard rewrite rules.
-/
theorem mp_unitary {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) (hU : Uᴴ * U = 1) :
    MeasurePreserving (fun y : Fin N → ℂ => U *ᵥ y) volume volume := by
  set f : (Fin N → ℂ) →ₗ[ℝ] (Fin N → ℂ) := (Matrix.toLin' U).restrictScalars ℝ with hf
  have hfU : (fun y : Fin N → ℂ => U *ᵥ y) = ⇑f := by funext y; simp [hf, Matrix.toLin'_apply]
  have hn : ((Complex.normSq U.det : ℝ) : ℂ) = 1 := by
    have h := congrArg Matrix.det hU
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h
    rw [Complex.normSq_eq_conj_mul_self]; exact h
  have hdet : LinearMap.det f = 1 := by
    rw [hf, LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply]; exact_mod_cast hn
  rw [hfU]
  refine ⟨f.continuous_of_finiteDimensional.measurable, ?_⟩
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hdet]; norm_num), hdet]
  simp

/- English proof (translation)
The claim follows from `(mp_unitary U hU).prod (MeasurePreserving.id volume)`.
-/
theorem mp_hpar {k n : ℕ} (U : Mat k n) (hU : Uᴴ * U = 1) :
    MeasurePreserving (fun X : HPar k n => (U *ᵥ X.1, X.2)) volume volume :=
  (mp_unitary U hU).prod (MeasurePreserving.id volume)

/- English proof (translation)
Substitute `hq` using the available equality. Take `⟨C, hC⟩` from `hOS p m δ γ e hδ hδ2 hγ hγ8 he hsum`. Use `⟨C, fun η η' ζ c₀ h0 => ?_⟩` and prove the remaining obligations. Establish `e0 : (⟨0, by omega⟩ : Fin (p + 1)) = 0` using `Fin.ext (by simp)`. Rewrite `h0`, the goal using `[e0]`.

Conclude with `hC η η' ζ c₀ h0`.
-/
theorem os_q (hOS : OS) (q p m : ℕ) (hq : q = p + 1) (δ γ : ℝ) (e : Fin (q + 1) → ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hγ : 0 < γ) (hγ8 : γ ≤ δ / 8) (he : ∀ l, 0 < e l) (hsum : e 0 + 2 * ∑ i : Fin q, e i.succ < γ / 2) :
    ∃ C : ℝ, ∀ (η η' : Fin q → ℂ) (ζ : Fin m → ℂ) (c₀ : ℝ), η' ⟨0, by omega⟩ ≠ 0 →
      ∫⁻ x, GI (fun l => s0N q m l - e l) δ η η' ζ c₀ x ≤
        ENNReal.ofReal (C * ‖η' ⟨0, by omega⟩‖ ^ (-γ) * (1 + |c₀|) ^ (-δ / 4)) := by
  subst hq
  obtain ⟨C, hC⟩ := hOS p m δ γ e hδ hδ2 hγ hγ8 he hsum
  refine ⟨C, fun η η' ζ c₀ h0 => ?_⟩
  have e0 : (⟨0, by omega⟩ : Fin (p + 1)) = 0 := Fin.ext (by simp)
  rw [e0] at h0 ⊢
  exact hC η η' ζ c₀ h0

end BL

end ReciprocityTheory.ChartRestriction.DS.Xi
