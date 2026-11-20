import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.TriDens
import Formalism.LocalRingCardinality.DataCD
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.OmegaA

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

def uToLieMat (x : UCo N) : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ :=
  Matrix.reindex (Equiv.sumEmpty (Fin N) (Fin 0)).symm (Equiv.sumEmpty (Fin N) (Fin 0)).symm (skMat x)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem uToLieMat_apply (x : UCo N) (i j : Fin N ⊕ Fin 0) :
    uToLieMat x i j = skMat x (Equiv.sumEmpty (Fin N) (Fin 0) i) (Equiv.sumEmpty (Fin N) (Fin 0) j) := by
  rfl

/- English proof (translation)
Rewrite using `[mem_lieU_zero_iff_om]`. Use extensionality with `i j`. Establish `h` using `congrFun (congrFun (skMat_conjTranspose_om x) (Equiv.sumEmpty (Fin N) (Fin 0) i)) (Equiv.sumEmpty (Fin N) (Fin 0) j)`. Simplify using `only [Matrix.conjTranspose_apply, Matrix.neg_apply] at h ⊢`. Rewrite using `[uToLieMat_apply, uToLieMat_apply]`.

Conclude with `h`.
-/
theorem uToLieMat_mem (x : UCo N) : uToLieMat x ∈ Formalism.BasicNotions.lieU N 0 := by
  rw [mem_lieU_zero_iff_om]
  ext i j
  have h := congrFun (congrFun (skMat_conjTranspose_om x) (Equiv.sumEmpty (Fin N) (Fin 0) i))
    (Equiv.sumEmpty (Fin N) (Fin 0) j)
  simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at h ⊢
  rw [uToLieMat_apply, uToLieMat_apply]
  exact h

def uToLie (x : UCo N) : Formalism.BasicNotions.lieU N 0 := ⟨uToLieMat x, uToLieMat_mem x⟩

def uToLieLin : UCo N →ₗ[ℝ] Formalism.BasicNotions.lieU N 0 where
  toFun := uToLie
  map_add' x y := by
    apply Subtype.ext
    show uToLieMat (x + y) = uToLieMat x + uToLieMat y
    ext i j
    simp [uToLieMat_apply, skMat_add_om]
  map_smul' c x := by
    apply Subtype.ext
    show uToLieMat (c • x) = c • uToLieMat x
    ext i j
    simp [uToLieMat_apply, skMat_smul_om, Complex.real_smul]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `x y hxy`. Establish `hm : ∀ a b : Fin N, skMat x a b = skMat y a b` using `fun a b => by`. Use `congrArg (fun z : Formalism.BasicNotions.lieU N 0 => (z : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ) (Sum.inl a) (Sum.inl b)) hxy` as an intermediate fact. Simplify `this` using `[uToLieLin, uToLie, uToLieMat_apply]`.

Use `Prod.ext (funext fun a => ?_) (funext fun l => ?_)` and prove the remaining obligations. Establish `h` using `hm a a`. Rewrite `h` using `[skMat_diag_om, skMat_diag_om]`. Establish `h'` using `mul_left_cancel₀ Complex.I_ne_zero h`. Conclude with `h'` after adjusting the coercions.

Establish `h` using `hm l.1.1 l.1.2`. Rewrite `h` using `[skMat_low_om, skMat_low_om]`. Then use the resulting hypothesis. Introduce and unpack `⟨X, hX⟩`. Establish `hX'` using `(mem_lieU_zero_iff_om X).1 hX`. Establish `hent : ∀ i j, star (X j i) = -X i j` using `fun i j => by`.

Use `congrFun (congrFun hX' i) j` as an intermediate fact. Simplify `this` using `[Matrix.conjTranspose_apply]`. Use `⟨((fun a => (X (Sum.inl a) (Sum.inl a)).im), fun l => X (Sum.inl l.1.1) (Sum.inl l.1.2)), ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Use `show uToLieMat _ = X`.

Use extensionality with `i j`. Break down `i with a | i` into its components or cases. Break down `j with b | j` into its components or cases. Rewrite using `[uToLieMat_apply]`. Simplify using `only [Equiv.sumEmpty_apply_inl]`.

Unfold `skMat`. Use `split_ifs with h1 h2 h3`. Substitute `h1` using the available equality. Establish `hre : (X (Sum.inl a) (Sum.inl a)).re = 0`. Use `congrArg Complex.re (hent (Sum.inl a) (Sum.inl a))` as an intermediate fact.

Simplify using `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Apply the tactic sequence `apply Complex.ext <;> simp [hre]`. Both sides reduce to the same expression. Use `show -star (X (Sum.inl b) (Sum.inl a)) = X (Sum.inl a) (Sum.inl b)`.

Rewrite using `[hent (Sum.inl a) (Sum.inl b), neg_neg]`. Conclude with `absurd (lt_trichotomy a b) (by tauto)`. Conclude with `j.elim0`. Conclude with `i.elim0`.
-/
theorem uToLieLin_bij : Function.Bijective (uToLieLin (N := N)) := by
  constructor
  · intro x y hxy
    have hm : ∀ a b : Fin N, skMat x a b = skMat y a b := fun a b => by
      have := congrArg (fun z : Formalism.BasicNotions.lieU N 0 =>
        (z : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ) (Sum.inl a) (Sum.inl b)) hxy
      simpa [uToLieLin, uToLie, uToLieMat_apply] using this
    refine Prod.ext (funext fun a => ?_) (funext fun l => ?_)
    · have h := hm a a
      rw [skMat_diag_om, skMat_diag_om] at h
      have h' := mul_left_cancel₀ Complex.I_ne_zero h
      exact_mod_cast h'
    · have h := hm l.1.1 l.1.2
      rwa [skMat_low_om, skMat_low_om] at h
  · rintro ⟨X, hX⟩
    have hX' := (mem_lieU_zero_iff_om X).1 hX
    have hent : ∀ i j, star (X j i) = -X i j := fun i j => by
      have := congrFun (congrFun hX' i) j
      simpa [Matrix.conjTranspose_apply] using this
    refine ⟨((fun a => (X (Sum.inl a) (Sum.inl a)).im), fun l => X (Sum.inl l.1.1) (Sum.inl l.1.2)), ?_⟩
    apply Subtype.ext
    show uToLieMat _ = X
    ext i j
    rcases i with a | i
    · rcases j with b | j
      · rw [uToLieMat_apply]
        simp only [Equiv.sumEmpty_apply_inl]
        unfold skMat
        split_ifs with h1 h2 h3
        · subst h1
          have hre : (X (Sum.inl a) (Sum.inl a)).re = 0 := by
            have := congrArg Complex.re (hent (Sum.inl a) (Sum.inl a))
            simp at this
            linarith
          apply Complex.ext <;> simp [hre]
        · rfl
        · show -star (X (Sum.inl b) (Sum.inl a)) = X (Sum.inl a) (Sum.inl b)
          rw [hent (Sum.inl a) (Sum.inl b), neg_neg]
        · exact absurd (lt_trichotomy a b) (by tauto)
      · exact j.elim0
    · exact i.elim0

def uToLieE : UCo N ≃L[ℝ] Formalism.BasicNotions.lieU N 0 :=
  (LinearEquiv.ofBijective uToLieLin uToLieLin_bij).toContinuousLinearEquiv

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem uToLieE_coe : ⇑(uToLieE (N := N)) = uToLie := rfl

def phiOmE : (UCo N × UCo N) ≃L[ℝ] ((Fin N ⊕ Fin 0) × (Fin N ⊕ Fin 0) → ℂ) :=
  (uToLieE.prodCongr uToLieE).trans complexifyLieEquiv

/- English proof (translation)
Use `show complexifyLieEquiv (uToLieE x, uToLieE y) p = _`. Rewrite using `[complexifyLieEquiv_coe, uToLieE_coe]`. Simplify using `[Formalism.BasicNotions.entries, uToLie, uToLieMat_apply]`.
-/
theorem phiOmE_apply (x y : UCo N) (p : (Fin N ⊕ Fin 0) × (Fin N ⊕ Fin 0)) :
    phiOmE (x, y) p = skMat x (Equiv.sumEmpty (Fin N) (Fin 0) p.1) (Equiv.sumEmpty (Fin N) (Fin 0) p.2) +
      Complex.I * skMat y (Equiv.sumEmpty (Fin N) (Fin 0) p.1) (Equiv.sumEmpty (Fin N) (Fin 0) p.2) := by
  show complexifyLieEquiv (uToLieE x, uToLieE y) p = _
  rw [complexifyLieEquiv_coe, uToLieE_coe]
  simp [Formalism.BasicNotions.entries, uToLie, uToLieMat_apply]

/- English proof (translation)
Conclude with `phiOmE.isAddHaarMeasure_map volume`.
-/
theorem phiOmE_haar : ((volume : Measure (UCo N × UCo N)).map (phiOmE (N := N))).IsAddHaarMeasure := by
  exact phiOmE.isAddHaarMeasure_map volume
/- English proof (translation)
Establish `hsum : ∑ p : (Fin N ⊕ Fin 0) × (Fin N ⊕ Fin 0), Complex.normSq (phiOmE (x, y) p) = ∑ a, (x.1 a ^ 2 + y.1 a ^ 2) + ∑ l : LoOm N, 2 * (Complex.normSq (x.2 l) + Complex.normSq (y.2 l))`. Rewrite using `[← normSq_skMat_sum]`. Conclude with `Fintype.sum_equiv ((Equiv.sumEmpty (Fin N) (Fin 0)).prodCongr (Equiv.sumEmpty (Fin N) (Fin 0))) _ _ (fun p => by rw [phiOmE_apply]; rfl)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[gaussEOm, ← Real.exp_sum]`.

Use `congr 1`. Simplify using `[Finset.sum_neg_distrib]`. Use `_ = gaussUOm x * gaussUOm y := by`. Rewrite using `[hsum]`. Simplify using `only [gaussUOm, ← Real.exp_sum, ← Real.exp_add]`.

Use `congr 1`. Simplify using `only [Finset.sum_add_distrib, ← Finset.mul_sum, mul_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gaussEOm_phiOmE (x y : UCo N) : gaussEOm (phiOmE (x, y)) = gaussUOm x * gaussUOm y := by
  have hsum : ∑ p : (Fin N ⊕ Fin 0) × (Fin N ⊕ Fin 0), Complex.normSq (phiOmE (x, y) p) =
      ∑ a, (x.1 a ^ 2 + y.1 a ^ 2) + ∑ l : LoOm N, 2 * (Complex.normSq (x.2 l) + Complex.normSq (y.2 l)) := by
    rw [← normSq_skMat_sum]
    exact Fintype.sum_equiv ((Equiv.sumEmpty (Fin N) (Fin 0)).prodCongr (Equiv.sumEmpty (Fin N) (Fin 0))) _ _
      (fun p => by rw [phiOmE_apply]; rfl)
  calc gaussEOm (phiOmE (x, y)) = Real.exp (-(∑ p, Complex.normSq (phiOmE (x, y) p))) := by
        rw [gaussEOm, ← Real.exp_sum]
        congr 1
        simp [Finset.sum_neg_distrib]
    _ = gaussUOm x * gaussUOm y := by
        rw [hsum]
        simp only [gaussUOm, ← Real.exp_sum, ← Real.exp_add]
        congr 1
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, mul_add]
        ring

/- English proof (translation)
Rewrite using `[MeasureTheory.integral_map phiOmE.continuous.measurable.aemeasurable continuous_gaussEOm.aestronglyMeasurable]`. Use `show ∫ z : UCo N × UCo N, gaussEOm (phiOmE (z.1, z.2)) = _`. Repeatedly rewrite using `[gaussEOm_phiOmE]`. Rewrite using `[MeasureTheory.Measure.volume_eq_prod, MeasureTheory.integral_prod_mul (f := gaussUOm) (g := gaussUOm), integral_gaussUOm, sq]`.
-/
theorem integral_gaussEOm_phiOmE : ∫ Z, gaussEOm Z ∂((volume : Measure (UCo N × UCo N)).map (phiOmE (N := N))) =
    (Real.sqrt Real.pi ^ N * (Real.pi / 2) ^ Fintype.card (LoOm N)) ^ 2 := by
  rw [MeasureTheory.integral_map phiOmE.continuous.measurable.aemeasurable
    continuous_gaussEOm.aestronglyMeasurable]
  show ∫ z : UCo N × UCo N, gaussEOm (phiOmE (z.1, z.2)) = _
  simp_rw [gaussEOm_phiOmE]
  rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.integral_prod_mul (f := gaussUOm) (g := gaussUOm), integral_gaussUOm, sq]

/- English proof (translation)
Rewrite using `[← uToLieE_coe]`. Conclude with `uToLieE.isAddHaarMeasure_map volume`.
-/
theorem map_uToLie_haar : (Measure.map (uToLie (N := N)) volume).IsAddHaarMeasure := by
  rw [← uToLieE_coe]
  exact uToLieE.isAddHaarMeasure_map volume

/- English proof (translation)
Establish `hm : Measurable (uToLie (N` using `N)) := by`. Rewrite using `[← uToLieE_coe]`. Conclude with `uToLieE.continuous.measurable`. Establish `hp : Measurable (fun ab : Formalism.BasicNotions.lieU N 0 × Formalism.BasicNotions.lieU N 0 => Formalism.BasicNotions.entries ((ab.1 : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ) + Complex.I • (ab.2 : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ)))`. Rewrite using `[← complexifyLieEquiv_coe]`.

Conclude with `complexifyLieEquiv.continuous.measurable`. Rewrite using `[Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.map_smul, Measure.map_prod_map _ _ hm hm, Measure.map_map hp (hm.prodMap hm)]`. Use `congr 2`.
-/
private lemma prod_map_lemma (c : ENNReal) :
    ((c • Measure.map (uToLie (N := N)) volume).prod (c • Measure.map (uToLie (N := N)) volume)).map
      (fun ab : Formalism.BasicNotions.lieU N 0 × Formalism.BasicNotions.lieU N 0 =>
        Formalism.BasicNotions.entries ((ab.1 : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ) +
          Complex.I • (ab.2 : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ))) =
      (c * c) • (volume : Measure (UCo N × UCo N)).map (phiOmE (N := N)) := by
  have hm : Measurable (uToLie (N := N)) := by
    rw [← uToLieE_coe]
    exact uToLieE.continuous.measurable
  have hp : Measurable (fun ab : Formalism.BasicNotions.lieU N 0 × Formalism.BasicNotions.lieU N 0 =>
      Formalism.BasicNotions.entries ((ab.1 : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ) +
        Complex.I • (ab.2 : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ))) := by
    rw [← complexifyLieEquiv_coe]
    exact complexifyLieEquiv.continuous.measurable
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.map_smul,
    Measure.map_prod_map _ _ hm hm, Measure.map_map hp (hm.prodMap hm)]
  congr 2

/- English proof (translation)
Use `haveI := phiOmE_haar (N := N)`. Establish `h1` using `Measure.isAddLeftInvariant_eq_smul (volume : Measure ((Fin N ⊕ Fin 0) × (Fin N ⊕ Fin 0) → ℂ)) ((volume : Measure (UCo N × UCo N)).map (phiOmE (N := N)))`. Rewrite `h1` using `[ENNReal.smul_def]`. Establish `hI` using `integral_gaussEOm (N := N)`. Rewrite `hI` using `[h1, integral_smul_measure, integral_gaussEOm_phiOmE, smul_eq_mul, ENNReal.coe_toReal]`.

Establish `hk` using `omega_key_real (N := N)`. Establish `hI2 : (0 : ℝ) < (Real.sqrt Real.pi ^ N * (Real.pi / 2) ^ Fintype.card (LoOm N)) ^ 2` using `by positivity`. Establish `hs` using `mul_right_cancel₀ hI2.ne' (hI.trans hk.symm)`. Rewrite using `[h1, ← ENNReal.ofReal_coe_nnreal, hs]`.
-/
private lemma vol_eq_lemma_2 :
    (volume : Measure ((Fin N ⊕ Fin 0) × (Fin N ⊕ Fin 0) → ℂ)) =
      ENNReal.ofReal (2 ^ (N * (N - 1) / 2) * 2 ^ (N * (N - 1) / 2)) •
        (volume : Measure (UCo N × UCo N)).map (phiOmE (N := N)) := by
  haveI := phiOmE_haar (N := N)
  have h1 := Measure.isAddLeftInvariant_eq_smul (volume : Measure ((Fin N ⊕ Fin 0) × (Fin N ⊕ Fin 0) → ℂ))
    ((volume : Measure (UCo N × UCo N)).map (phiOmE (N := N)))
  rw [ENNReal.smul_def] at h1
  have hI := integral_gaussEOm (N := N)
  rw [h1, integral_smul_measure, integral_gaussEOm_phiOmE, smul_eq_mul, ENNReal.coe_toReal] at hI
  have hk := omega_key_real (N := N)
  have hI2 : (0 : ℝ) < (Real.sqrt Real.pi ^ N * (Real.pi / 2) ^ Fintype.card (LoOm N)) ^ 2 := by positivity
  have hs := mul_right_cancel₀ hI2.ne' (hI.trans hk.symm)
  rw [h1, ← ENNReal.ofReal_coe_nnreal, hs]

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `haveI := map_uToLie_haar (N := N)`. Conclude with `Measure.IsAddHaarMeasure.smul _ (ENNReal.ofReal_pos.2 (by positivity)).ne' ENNReal.ofReal_ne_top`. Rewrite using `[prod_map_lemma, ← ENNReal.ofReal_mul (by positivity), vol_eq_lemma_2]`.
-/
theorem isOmegaLeb_uToLie :
    Formalism.BasicNotions.IsOmegaLeb (ENNReal.ofReal (2 ^ (N * (N - 1) / 2)) • Measure.map (uToLie (N := N)) volume) := by
  refine ⟨?_, ?_⟩
  · haveI := map_uToLie_haar (N := N)
    exact Measure.IsAddHaarMeasure.smul _ (ENNReal.ofReal_pos.2 (by positivity)).ne' ENNReal.ofReal_ne_top
  · rw [prod_map_lemma, ← ENNReal.ofReal_mul (by positivity), vol_eq_lemma_2]

end ReciprocityTheory.ChartRestriction.DS
