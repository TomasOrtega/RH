import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParP
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralEqClosedSubgroupConjAverageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralParabolicUnfoldLeviStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockUpperParabolicMulIntegralGLStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerBlockLeParabolicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentConjLeviEqBlockUpperTwistedSylvesterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedMatrixIntegralCompLinearEquivDetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetTwistedSylvesterSqMulDetPowEqResultantSqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjAverageUnipotentLocallyConstantCompactSupporStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResultantNeZeroOfSeparableMulStatement

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LeviDesc

/- English proof (translation)
Introduce `E _ _ w x y hx hy`. Establish `hq : (0 : ℝ) < (qV E w : ℝ)` using `by exact_mod_cast Nat.pos_of_ne_zero (GlobalTheory.LFun.qV_ne_zero w)`. Establish `ho : Formalism.UG.ordL (x * y) = Formalism.UG.ordL x + Formalism.UG.ordL y`. Unfold `Formalism.UG.ordL`. Establish `h1 : Valued.v x ≠ 0` using `(Valuation.ne_zero_iff _).2 hx`.

Establish `h2 : Valued.v y ≠ 0` using `(Valuation.ne_zero_iff _).2 hy`. Establish `h3 : Valued.v (x * y) ≠ 0` using `(Valuation.ne_zero_iff _).2 (mul_ne_zero hx hy)`. Rewrite using `[dif_neg h1, dif_neg h2, dif_neg h3]`. Establish `: WithZero.unzero h3 = WithZero.unzero h1 * WithZero.unzero h2`. Apply `WithZero.coe_injective` to reduce the goal to its premises.

Simplify using `[map_mul]`. Rewrite using `[this, toAdd_mul]`. Expand and normalize the polynomial expressions, which then agree. Unfold `absHalf`. Rewrite using `[ho, neg_add, zpow_add₀ hq.ne', Real.sqrt_mul (zpow_pos hq _).le]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem absHalf_mul : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (x y : w.adicCompletion E), x ≠ 0 → y ≠ 0 → absHalf w (x * y) = absHalf w x * absHalf w y := by
  intro E _ _ w x y hx hy
  have hq : (0 : ℝ) < (qV E w : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (GlobalTheory.LFun.qV_ne_zero w)
  have ho : Formalism.UG.ordL (x * y) = Formalism.UG.ordL x + Formalism.UG.ordL y := by
    unfold Formalism.UG.ordL
    have h1 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
    have h2 : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
    have h3 : Valued.v (x * y) ≠ 0 := (Valuation.ne_zero_iff _).2 (mul_ne_zero hx hy)
    rw [dif_neg h1, dif_neg h2, dif_neg h3]
    have : WithZero.unzero h3 = WithZero.unzero h1 * WithZero.unzero h2 := by
      apply WithZero.coe_injective
      simp [map_mul]
    rw [this, toAdd_mul]
    ring
  unfold absHalf
  rw [ho, neg_add, zpow_add₀ hq.ne', Real.sqrt_mul (zpow_pos hq _).le]
  push_cast
  ring

/- English proof (translation)
Introduce `E _ _ a n w`. Establish `: (parP a n w : Set (GLw n w)) = ⋂ i : Fin n, ⋂ j : Fin n, {g : GLw n w | decide (a ≤ (j : ℕ)) < decide (a ≤ (i : ℕ)) → (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j = 0}`. Use extensionality with `g`. Simplify using `only [Set.mem_iInter]`. Both sides reduce to the same expression.

Rewrite using `[this]`. Use `isClosed_iInter fun i => isClosed_iInter fun j => ?_` and prove the remaining obligations. Distinguish the cases in `hij : decide (a ≤ (j : ℕ)) < decide (a ≤ (i : ℕ))`. Simplify using `only [hij, true_implies]`. Conclude with `isClosed_eq (Continuous.matrix_elem (Units.continuous_val (M := Matrix (Fin n) (Fin n) (w.adicCompletion E))) i j) continuous_const`.

Simplify using `only [hij, false_implies, Set.ofPred_true]`. Conclude with `isClosed_univ`.
-/
theorem isClosed_parP : ∀ (E : Type) [Field E] [NumberField E] (a n : ℕ) (w : Pl E), IsClosed (GlobalTheory.LeviDesc.parP a n w : Set (GLw n w)) := by
  intro E _ _ a n w
  have : (parP a n w : Set (GLw n w)) = ⋂ i : Fin n, ⋂ j : Fin n,
      {g : GLw n w | decide (a ≤ (j : ℕ)) < decide (a ≤ (i : ℕ)) → (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j = 0} := by
    ext g
    simp only [Set.mem_iInter]
    rfl
  rw [this]
  refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
  by_cases hij : decide (a ≤ (j : ℕ)) < decide (a ≤ (i : ℕ))
  · simp only [hij, true_implies]
    exact isClosed_eq (Continuous.matrix_elem (Units.continuous_val (M := Matrix (Fin n) (Fin n) (w.adicCompletion E))) i j) continuous_const
  · simp only [hij, false_implies, Set.ofPred_true]
    exact isClosed_univ

/- English proof (translation)
Introduce `E _ _ n a b h w m X`. Unfold `blk`. Simplify using `only []`. Use `split_ifs with hM`. Express the relevant statement in the definitionally equal form `(hM.unit : Matrix (Fin n) (Fin n) (w.adicCompletion E)).BlockTriangular _`.

Rewrite using `[IsUnit.unit_spec]`. Introduce `i j hij`. Establish `hj : (j : ℕ) < a`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Simplify using `only [hc, decide_true] at hij`. Conclude with `(by decide : ∀ c : Bool, ¬ (true < c)) _ hij`. Establish `hi : a ≤ (i : ℕ)`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Simplify using `only [not_le.2 hc, decide_false] at hij`. Conclude with `(by decide : ∀ c : Bool, ¬ (c < false)) _ hij`. Simplify using `only [Matrix.reindex_apply, Matrix.submatrix_apply]`. Break down `hi' : (finSumFinEquiv.trans (finCongr h)).symm i with i' | i'` into its components or cases. It suffices to derive a contradiction.

Use `congrArg (finSumFinEquiv.trans (finCongr h)) hi'` as an intermediate fact. Rewrite `this` using `[Equiv.apply_symm_apply]`. Establish `hv` using `congrArg Fin.val this`. Simplify using `at hv`. Use linear arithmetic over natural numbers and integers.

Break down `hj' : (finSumFinEquiv.trans (finCongr h)).symm j with j' | j'` into its components or cases. Simplify using the standard rewrite rules. It suffices to derive a contradiction. Use `congrArg (finSumFinEquiv.trans (finCongr h)) hj'` as an intermediate fact. Rewrite `this` using `[Equiv.apply_symm_apply]`.

Establish `hv` using `congrArg Fin.val this`. Simplify using `at hv`. Use linear arithmetic over natural numbers and integers. Conclude with `(parP a n w).one_mem`.
-/
theorem blk_mem_parP : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)), blk h w m X ∈ GlobalTheory.LeviDesc.parP a n w := by
  intro E _ _ n a b h w m X
  unfold blk
  simp only []
  split_ifs with hM
  · change (hM.unit : Matrix (Fin n) (Fin n) (w.adicCompletion E)).BlockTriangular _
    rw [IsUnit.unit_spec]
    intro i j hij
    have hj : (j : ℕ) < a := by
      by_contra hc
      push_neg at hc
      simp only [hc, decide_true] at hij
      exact (by decide : ∀ c : Bool, ¬ (true < c)) _ hij
    have hi : a ≤ (i : ℕ) := by
      by_contra hc
      push_neg at hc
      simp only [not_le.2 hc, decide_false] at hij
      exact (by decide : ∀ c : Bool, ¬ (c < false)) _ hij
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
    rcases hi' : (finSumFinEquiv.trans (finCongr h)).symm i with i' | i'
    · exfalso
      have := congrArg (finSumFinEquiv.trans (finCongr h)) hi'
      rw [Equiv.apply_symm_apply] at this
      have hv := congrArg Fin.val this
      simp at hv
      omega
    · rcases hj' : (finSumFinEquiv.trans (finCongr h)).symm j with j' | j'
      · simp
      · exfalso
        have := congrArg (finSumFinEquiv.trans (finCongr h)) hj'
        rw [Equiv.apply_symm_apply] at this
        have hv := congrArg Fin.val this
        simp at hv
        omega
  · exact (parP a n w).one_mem

/- English proof (translation)
Establish `hs : rStab (fun x => c * u x) = rStab u`. Use extensionality with `k`. Express the relevant statement in the definitionally equal form `(∀ x, c * u (x * k) = c * u x) ↔ (∀ x, u (x * k) = u x)`. Conclude with `⟨fun h x => mul_left_cancel₀ hc (h x), fun h x => by rw [h x]⟩`. Unfold `avg`.

Rewrite using `[hs, ← mul_finsum]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem avg_const_mul {H : Type} [Group H] (u : H → ℂ) {c : ℂ} (hc : c ≠ 0) :
    avg (fun x => c * u x) = c * avg u := by
  have hs : rStab (fun x => c * u x) = rStab u := by
    ext k
    change (∀ x, c * u (x * k) = c * u x) ↔ (∀ x, u (x * k) = u x)
    exact ⟨fun h x => mul_left_cancel₀ hc (h x), fun h x => by rw [h x]⟩
  unfold avg
  rw [hs, ← mul_finsum]
  ring

/- English proof (translation)
Unfold `absHalf`. Establish `hq : (0 : ℝ) < (qV E w : ℝ)` using `by exact_mod_cast Nat.pos_of_ne_zero (GlobalTheory.LFun.qV_ne_zero w)`. Conclude with `(Real.sqrt_pos.2 (zpow_pos hq _)).ne'` after adjusting the coercions.
-/
theorem absHalf_ne_zero' {E : Type} [Field E] [NumberField E] (w : Pl E) (x : w.adicCompletion E) : absHalf w x ≠ 0 := by
  unfold absHalf
  have hq : (0 : ℝ) < (qV E w : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (GlobalTheory.LFun.qV_ne_zero w)
  exact_mod_cast (Real.sqrt_pos.2 (zpow_pos hq _)).ne'

/- English proof (translation)
Introduce `E _ _ _ n a ha w f hf m hsep`. Take `⟨hU, hcs⟩` from `GlobalTheory.T.conjAverage_unipotent_locallyConstant_compactSupport E n a (n - a) (Nat.add_sub_cancel' ha) w f hf m`. Establish `hR` using `GlobalTheory.T.resultant_ne_zero_of_monic_of_separable_mul (w.adicCompletion E) _ _ (Matrix.charpoly_monic _) (Matrix.charpoly_monic _) hsep`. Establish `hD` using `GlobalTheory.T.det_twistedSylvester_sq_mul_det_pow_eq_resultant_sq (w.adicCompletion E) a (n - a) m.1 m.2.val`. Establish `hd1 : m.1.val.det ≠ 0` using `((Matrix.isUnit_iff_isUnit_det _).mp m.1.isUnit).ne_zero`.

Establish `hd2 : m.2.val.det ≠ 0` using `((Matrix.isUnit_iff_isUnit_det _).mp m.2.isUnit).ne_zero`. Establish `hL : LinearMap.det (adL m.1 m.2.val) ≠ 0`. Introduce `h0`. Rewrite `hD` using `[h0]`. Apply `hR` to reduce the goal to its premises.

Establish `: resultant m.1.val.charpoly m.2.val.charpoly ^ 2 = 0` using `by rw [← hD]; ring`. Conclude with `pow_eq_zero_iff (by norm_num) |>.mp this`. Establish `hJ` using `GlobalTheory.T.normalisedMatrixIntegral_comp_linearEquiv_det E w a (n - a) (adL m.1 m.2.val) (fun X => cavg (GlobalTheory.LFun.KGL w n) f (blk (Nat.add_sub_cancel' ha) w m X)) hL hU hcs`. Establish `hI : orbN (Nat.add_sub_cancel' ha) w f m = hint (intMat a (n - a) w) (fun X => cavg (GlobalTheory.LFun.KGL w n) f (blk (Nat.add_sub_cancel' ha) w m (adL m.1 m.2.val (Multiplicative.toAdd X))))`. Unfold `orbN`.

Simplify using `only [GlobalTheory.T.unipotent_conj_levi_eq_blockUpperTwistedSylvester]`. Rewrite using `[hI, hJ]`. Express the relevant statement in the definitionally equal form `absHalf w (m.1.val.det ^ (n - a) / m.2.val.det ^ a) * hint (intMat a (n - a) w) (fun X => cavg (GlobalTheory.LFun.KGL w n) f (blk (Nat.add_sub_cancel' ha) w m (Multiplicative.toAdd X))) = _`. Establish `hq : resultant m.1.val.charpoly m.2.val.charpoly ^ 2 / (m.1.val.det ^ (n - a) * m.2.val.det ^ a) = LinearMap.det (adL m.1 m.2.val) * (LinearMap.det (adL m.1 m.2.val) * (m.1.val.det ^ (n - a) / m.2.val.det ^ a))`. Rewrite using `[← hD]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hq0 : m.1.val.det ^ (n - a) / m.2.val.det ^ a ≠ 0` using `div_ne_zero (pow_ne_zero _ hd1) (pow_ne_zero _ hd2)`. Rewrite using `[hq, absHalf_mul E w _ _ hL (mul_ne_zero hL hq0), absHalf_mul E w _ _ hL hq0]`. Establish `h0` using `absHalf_ne_zero' w (LinearMap.det (adL m.1 m.2.val))`.

Clear the denominators using the available nonvanishing facts.
-/
theorem ct_eq_mul_orbN : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n a : ℕ) (ha : a ≤ n) (w : Pl E) (f : GLw n w → ℂ), (∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f) → ∀ m : GLw a w × GLw (n - a) w, (m.1.val.charpoly * m.2.val.charpoly).Separable → ct (Nat.add_sub_cancel' ha) w f m = absHalf w (resultant m.1.val.charpoly m.2.val.charpoly ^ 2 / (m.1.val.det ^ (n - a) * m.2.val.det ^ a)) * GlobalTheory.LeviDesc.orbN (Nat.add_sub_cancel' ha) w f m := by
  intro E _ _ _ n a ha w f hf m hsep
  obtain ⟨hU, hcs⟩ := GlobalTheory.T.conjAverage_unipotent_locallyConstant_compactSupport E n a (n - a) (Nat.add_sub_cancel' ha) w f hf m
  have hR := GlobalTheory.T.resultant_ne_zero_of_monic_of_separable_mul (w.adicCompletion E) _ _ (Matrix.charpoly_monic _) (Matrix.charpoly_monic _) hsep
  have hD := GlobalTheory.T.det_twistedSylvester_sq_mul_det_pow_eq_resultant_sq (w.adicCompletion E) a (n - a) m.1 m.2.val
  have hd1 : m.1.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp m.1.isUnit).ne_zero
  have hd2 : m.2.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp m.2.isUnit).ne_zero
  have hL : LinearMap.det (adL m.1 m.2.val) ≠ 0 := by
    intro h0
    rw [h0] at hD
    apply hR
    have : resultant m.1.val.charpoly m.2.val.charpoly ^ 2 = 0 := by rw [← hD]; ring
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  have hJ := GlobalTheory.T.normalisedMatrixIntegral_comp_linearEquiv_det E w a (n - a) (adL m.1 m.2.val)
    (fun X => cavg (GlobalTheory.LFun.KGL w n) f (blk (Nat.add_sub_cancel' ha) w m X)) hL hU hcs
  have hI : orbN (Nat.add_sub_cancel' ha) w f m = hint (intMat a (n - a) w)
      (fun X => cavg (GlobalTheory.LFun.KGL w n) f (blk (Nat.add_sub_cancel' ha) w m (adL m.1 m.2.val (Multiplicative.toAdd X)))) := by
    unfold orbN
    simp only [GlobalTheory.T.unipotent_conj_levi_eq_blockUpperTwistedSylvester]
  rw [hI, hJ]
  change absHalf w (m.1.val.det ^ (n - a) / m.2.val.det ^ a) * hint (intMat a (n - a) w)
      (fun X => cavg (GlobalTheory.LFun.KGL w n) f (blk (Nat.add_sub_cancel' ha) w m (Multiplicative.toAdd X))) = _
  have hq : resultant m.1.val.charpoly m.2.val.charpoly ^ 2 / (m.1.val.det ^ (n - a) * m.2.val.det ^ a) =
      LinearMap.det (adL m.1 m.2.val) * (LinearMap.det (adL m.1 m.2.val) * (m.1.val.det ^ (n - a) / m.2.val.det ^ a)) := by
    rw [← hD]
    field_simp
    ring
  have hq0 : m.1.val.det ^ (n - a) / m.2.val.det ^ a ≠ 0 := div_ne_zero (pow_ne_zero _ hd1) (pow_ne_zero _ hd2)
  rw [hq, absHalf_mul E w _ _ hL (mul_ne_zero hL hq0), absHalf_mul E w _ _ hL hq0]
  have h0 := absHalf_ne_zero' w (LinearMap.det (adL m.1 m.2.val))
  field_simp

/- English proof (translation)
Rewrite using `[Units.val_mul, Units.val_mul, Matrix.coe_units_inv]`. Conclude with `Matrix.charpoly_units_conj' g m.val`.
-/
theorem conjP_charpoly {k : Type} [Field k] {a : ℕ} (g m : GL (Fin a) k) : (g⁻¹ * m * g).val.charpoly = m.val.charpoly := by
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
  exact Matrix.charpoly_units_conj' g m.val

/- English proof (translation)
Rewrite using `[Units.val_mul, Units.val_mul]`. Conclude with `Matrix.det_units_conj' g m.val`.
-/
theorem conjP_det {k : Type} [Field k] {a : ℕ} (g m : GL (Fin a) k) : (g⁻¹ * m * g).val.det = m.val.det := by
  rw [Units.val_mul, Units.val_mul]
  exact Matrix.det_units_conj' g m.val

/- English proof (translation)
Introduce `E _ _ _ n a ha w f hf m hsep`. Establish `hf' : ∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f`. Break down `hf with h | h` into its components or cases. Conclude with `⟨_, (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1, h⟩`. Conclude with `h`.

Establish `hc0` using `absHalf_ne_zero' w (resultant m.1.val.charpoly m.2.val.charpoly ^ 2 / (m.1.val.det ^ (n - a) * m.2.val.det ^ a))`. Establish `h1 : twOrb (MonoidHom.id _) ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w (n - a))) m (ct (Nat.add_sub_cancel' ha) w f) = twOrb (MonoidHom.id _) ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w (n - a))) m (fun m' => absHalf w (resultant m.1.val.charpoly m. …`. Unfold `twOrb`. Use `finsum_congr fun q => ?_` and prove the remaining obligations. Use `congr 2`.

Use function extensionality and compare the values at `k`. Establish `e1 : ∀ g : GLw a w × GLw (n - a) w, ((g⁻¹ * m * (MonoidHom.id _) g).1).val.charpoly = m.1.val.charpoly` using `fun g => conjP_charpoly g.1 m.1`. Establish `e2 : ∀ g : GLw a w × GLw (n - a) w, ((g⁻¹ * m * (MonoidHom.id _) g).2).val.charpoly = m.2.val.charpoly` using `fun g => conjP_charpoly g.2 m.2`. Establish `d1 : ∀ g : GLw a w × GLw (n - a) w, ((g⁻¹ * m * (MonoidHom.id _) g).1).val.det = m.1.val.det` using `fun g => conjP_det g.1 m.1`. Establish `d2 : ∀ g : GLw a w × GLw (n - a) w, ((g⁻¹ * m * (MonoidHom.id _) g).2).val.det = m.2.val.det` using `fun g => conjP_det g.2 m.2`.

Use `set g := Quotient.out q * (k : GLw a w × GLw (n - a) w)`. Rewrite using `[ct_eq_mul_orbN E n a ha w f hf' _ (by rw [e1, e2]; exact hsep), e1, e2, d1, d2]`. Establish `h2 : twOrb (MonoidHom.id _) ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w (n - a))) m (fun m' => absHalf w (resultant m.1.val.charpoly m.2.val.charpoly ^ 2 / (m.1.val.det ^ (n - a) * m.2.val.det ^ a)) * orbN (Nat.add_sub_cancel' ha) w f m') = absHalf w (resultant m.1 …`. Unfold `twOrb`. Rewrite using `[mul_finsum]`.

Use `finsum_congr fun q => ?_` and prove the remaining obligations. Rewrite using `[avg_const_mul _ hc0]`. Expand and normalize the polynomial expressions, which then agree. Establish `hγ` using `blk_mem_parP E n a (n - a) (Nat.add_sub_cancel' ha) w m 0`. Establish `hKG` using `GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n`.

Rewrite using `[h1, h2, ← GlobalTheory.T.twistedOrbitalIntegral_parabolic_unfold_levi E n a ha w f hf' m hsep hγ, ← GlobalTheory.T.orbitalIntegral_eq_closedSubgroup_conjAverage (GLw n w) (GlobalTheory.LFun.KGL w n) (parP a n w) hKG.1 hKG.2 (isClosed_parP E a n w) (GlobalTheory.T.exists_blockUpp …`.
-/
theorem orbInt_descent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n a : ℕ) (ha : a ≤ n) (w : Pl E) (f : GLw n w → ℂ), IsHecke (GlobalTheory.LFun.KGL w n) f ∨ (∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f) → ∀ m : GLw a w × GLw (n - a) w, (m.1.val.charpoly * m.2.val.charpoly).Separable → twOrb (MonoidHom.id _) ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w (n - a))) m (ct (Nat.add_sub_cancel' ha) w f) = absHalf w (resultant m.1.val.charpoly m.2.val.charpoly ^ 2 / (m.1.val.det ^ (n - a) * m.2.val.det ^ a)) * twOrb (MonoidHom.id _) (GlobalTheory.LFun.KGL w n) (blk (Nat.add_sub_cancel' ha) w m 0) f := by
  intro E _ _ _ n a ha w f hf m hsep
  have hf' : ∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f := by
    rcases hf with h | h
    · exact ⟨_, (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1, h⟩
    · exact h
  have hc0 := absHalf_ne_zero' w (resultant m.1.val.charpoly m.2.val.charpoly ^ 2 / (m.1.val.det ^ (n - a) * m.2.val.det ^ a))
  have h1 : twOrb (MonoidHom.id _) ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w (n - a))) m (ct (Nat.add_sub_cancel' ha) w f) =
      twOrb (MonoidHom.id _) ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w (n - a))) m
        (fun m' => absHalf w (resultant m.1.val.charpoly m.2.val.charpoly ^ 2 / (m.1.val.det ^ (n - a) * m.2.val.det ^ a)) *
          orbN (Nat.add_sub_cancel' ha) w f m') := by
    unfold twOrb
    refine finsum_congr fun q => ?_
    congr 2
    funext k
    have e1 : ∀ g : GLw a w × GLw (n - a) w, ((g⁻¹ * m * (MonoidHom.id _) g).1).val.charpoly = m.1.val.charpoly :=
      fun g => conjP_charpoly g.1 m.1
    have e2 : ∀ g : GLw a w × GLw (n - a) w, ((g⁻¹ * m * (MonoidHom.id _) g).2).val.charpoly = m.2.val.charpoly :=
      fun g => conjP_charpoly g.2 m.2
    have d1 : ∀ g : GLw a w × GLw (n - a) w, ((g⁻¹ * m * (MonoidHom.id _) g).1).val.det = m.1.val.det :=
      fun g => conjP_det g.1 m.1
    have d2 : ∀ g : GLw a w × GLw (n - a) w, ((g⁻¹ * m * (MonoidHom.id _) g).2).val.det = m.2.val.det :=
      fun g => conjP_det g.2 m.2
    set g := Quotient.out q * (k : GLw a w × GLw (n - a) w)
    rw [ct_eq_mul_orbN E n a ha w f hf' _ (by rw [e1, e2]; exact hsep), e1, e2, d1, d2]
  have h2 : twOrb (MonoidHom.id _) ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w (n - a))) m
        (fun m' => absHalf w (resultant m.1.val.charpoly m.2.val.charpoly ^ 2 / (m.1.val.det ^ (n - a) * m.2.val.det ^ a)) *
          orbN (Nat.add_sub_cancel' ha) w f m') =
      absHalf w (resultant m.1.val.charpoly m.2.val.charpoly ^ 2 / (m.1.val.det ^ (n - a) * m.2.val.det ^ a)) *
        twOrb (MonoidHom.id _) ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w (n - a))) m (orbN (Nat.add_sub_cancel' ha) w f) := by
    unfold twOrb
    rw [mul_finsum]
    refine finsum_congr fun q => ?_
    rw [avg_const_mul _ hc0]
    ring
  have hγ := blk_mem_parP E n a (n - a) (Nat.add_sub_cancel' ha) w m 0
  have hKG := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n
  rw [h1, h2, ← GlobalTheory.T.twistedOrbitalIntegral_parabolic_unfold_levi E n a ha w f hf' m hsep hγ,
    ← GlobalTheory.T.orbitalIntegral_eq_closedSubgroup_conjAverage (GLw n w) (GlobalTheory.LFun.KGL w n) (parP a n w) hKG.1 hKG.2 (isClosed_parP E a n w) (GlobalTheory.T.exists_blockUpperParabolic_mul_integralGL E a n w) _ hγ
      (GlobalTheory.T.twisted_centralizer_block_le_parabolic E n a (n - a) _ w m hsep) f hf']

end GlobalTheory.LeviDesc
