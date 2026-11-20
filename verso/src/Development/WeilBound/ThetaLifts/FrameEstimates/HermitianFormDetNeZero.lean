import Mathlib
import Development.WeilBound.ThetaLifts.FrameEstimates.ContinuousMixedSymm
import Development.WeilBound.ThetaLifts.FrameEstimates.RankIffRight

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.EmbChart (atPlace atPlace_mul_right evFin_atPlace)
open scoped TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace PositivityTheory.ThKEst

namespace W

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

/- English proof (translation)
Rewrite using `[AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hn a)]`.
-/
theorem conj_psi {ψ : AddChar (AF F) ℂ} (hn : ∀ x, ‖ψ x‖ = 1) (a : AF F) : (starRingEnd ℂ) (ψ a) = ψ (-a) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hn a)]

/- English proof (translation)
Use `haveI : BorelSpace (κ → AF F) := ⟨rfl⟩`. Establish `key : ∀ y, Φ (y + u.1) = ψ (a - (y ⬝ᵥ u.2 + ⅟(2 : AF F) * (u.1 ⬝ᵥ u.2))) * Φ y` using `fun y => by`. Use `congrFun h y` as an intermediate fact. Simplify using `only [schr, Pi.smul_apply, smul_eq_mul] at this`. Rewrite using `[sub_eq_neg_add, AddChar.map_add_eq_mul, mul_assoc, ← this, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]`.

Establish `key' : ∀ x, Φ (-(x + u.1)) = ψ (-(a - ((-(x + u.1)) ⬝ᵥ u.2 + ⅟(2 : AF F) * (u.1 ⬝ᵥ u.2)))) * Φ (-x)` using `fun x => by`. Use `key (-(x + u.1))` as an intermediate fact. Rewrite `this` using `[show -(x + u.1) + u.1 = -x by abel]`. Rewrite using `[this, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]`. Unfold `coef`.

Rewrite using `[← integral_const_mul, ← integral_add_right_eq_self _ u.1]`. Use `integral_congr_ae (.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only [schr]`. Rewrite using `[add_right_comm x u.1 w.1, key, key', map_mul, conj_psi hn]`. Establish `e : ∀ p q s t t' : AF F, ∀ A B : ℂ, p + q + s = t + t' → ψ p * (ψ q * A) * (ψ s * B) = ψ t * (ψ t' * A * B)`.

Introduce `p q s t t' A B e`. Use `congrArg ψ e` as an intermediate fact. Simplify using `only [AddChar.map_add_eq_mul] at this`. Take the linear combination `A * B * this`. Use `e _ _ _ _ _ _ _ ?_` and prove the remaining obligations.

Establish `h2 : ⅟(2 : AF F) + ⅟(2 : AF F) = 1` using `invOf_two_add_invOf_two`. Simplify using `only [add_dotProduct, neg_dotProduct]`. Take the linear combination `(-(u.1 ⬝ᵥ u.2)) * h2`.
-/
theorem coef_eigen {ψ : AddChar (AF F) ℂ} (hn : ∀ x, ‖ψ x‖ = 1) (μ : Measure (κ → AF F)) [μ.IsAddHaarMeasure]
    (Φ : (κ → AF F) → ℂ) (u w : (κ → AF F) × (κ → AF F)) (a : AF F) (h : schr ψ u Φ = ψ a • Φ) :
    coef F ψ μ Φ (fun x => Φ (-x)) w = ψ (u.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ u.2 + (a + a)) * coef F ψ μ Φ (fun x => Φ (-x)) w := by
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  have key : ∀ y, Φ (y + u.1) = ψ (a - (y ⬝ᵥ u.2 + ⅟(2 : AF F) * (u.1 ⬝ᵥ u.2))) * Φ y := fun y => by
    have := congrFun h y
    simp only [schr, Pi.smul_apply, smul_eq_mul] at this
    rw [sub_eq_neg_add, AddChar.map_add_eq_mul, mul_assoc, ← this, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel,
      AddChar.map_zero_eq_one, one_mul]
  have key' : ∀ x, Φ (-(x + u.1)) = ψ (-(a - ((-(x + u.1)) ⬝ᵥ u.2 + ⅟(2 : AF F) * (u.1 ⬝ᵥ u.2)))) * Φ (-x) := fun x => by
    have := key (-(x + u.1))
    rw [show -(x + u.1) + u.1 = -x by abel] at this
    rw [this, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
  unfold coef
  rw [← integral_const_mul, ← integral_add_right_eq_self _ u.1]
  refine integral_congr_ae (.of_forall fun x => ?_)
  simp only [schr]
  rw [add_right_comm x u.1 w.1, key, key', map_mul, conj_psi hn]
  have e : ∀ p q s t t' : AF F, ∀ A B : ℂ, p + q + s = t + t' → ψ p * (ψ q * A) * (ψ s * B) = ψ t * (ψ t' * A * B) := by
    intro p q s t t' A B e
    have := congrArg ψ e
    simp only [AddChar.map_add_eq_mul] at this
    linear_combination A * B * this
  refine e _ _ _ _ _ _ _ ?_
  have h2 : ⅟(2 : AF F) + ⅟(2 : AF F) = 1 := invOf_two_add_invOf_two
  simp only [add_dotProduct, neg_dotProduct]
  linear_combination (-(u.1 ⬝ᵥ u.2)) * h2

variable {v : Pl F}

/- English proof (translation)
Introduce `x t` and use `h.1 x _ ((at_iff _).2 (funext fun i => (ep_mul _).trans (by rw [evFin_atPlace])))`.
-/
theorem indep_of_rest {φ : (κ → Fv F v) → ℂ} {r : (κ → AF F) → ℂ} (h : Rest (evFin F v) φ r) : Indep v r :=
  fun x t => h.1 x _ ((at_iff _).2 (funext fun i => (ep_mul _).trans (by rw [evFin_atPlace])))

/- English proof (translation)
Introduce `r hr` and use `by rw [schr_tens ψ w _ (indep_of_rest hr), offP_eq, sub_smul, hw, one_smul, sub_self, schr_zero]`.
-/
theorem acts_schr (ψ : AddChar (AF F) ℂ) {w : (κ → AF F) × (κ → AF F)} (hw : ep v • w = w) (φ : (κ → Fv F v) → ℂ) :
    Acts (evFin F v) (schr ψ w) φ (schr (psv v ψ) (evP v w) φ) := fun r hr => by
  rw [schr_tens ψ w _ (indep_of_rest hr), offP_eq, sub_smul, hw, one_smul, sub_self, schr_zero]

end W

open W

/- English proof (translation)
Introduce `h0` and use `by obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance exact hasSig_det (h.sig w) (by rw [show (X.J.map (B.emb w).1).det = (B.emb w).1 X.J.det from (RingHom.map_det _ _).symm, h0, map_zero])`.
-/
theorem det_X {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {n r s : ℕ} {X : Spc F E n} (h : X.IsHerm σ B r s) : X.J.det ≠ 0 := fun h0 => by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact hasSig_det (h.sig w) (by
    rw [show (X.J.map (B.emb w).1).det = (B.emb w).1 X.J.det from (RingHom.map_det _ _).symm, h0, map_zero])

/- English proof (translation)
Introduce `h0` and use `by obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance exact hasSig_det (h.sig w) (by rw [det_smul, show (X.J.map (B.emb w).1).det = (B.emb w).1 X.J.det from (RingHom.map_det _ _).symm, h0, map_zero, mul_zero])`.
-/
theorem hermitian_form_det_ne_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {n r s : ℕ} {X : Spc F E n} (h : X.IsSkew σ B r s) : X.J.det ≠ 0 := fun h0 => by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact hasSig_det (h.sig w) (by
    rw [det_smul, show (X.J.map (B.emb w).1).det = (B.emb w).1 X.J.det from (RingHom.map_det _ _).symm, h0, map_zero,
      mul_zero])

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP φ hφ`. Take `⟨hφ, ι, hι, hz⟩` from `hφ`. Establish `h` using `hP.base.cm`. Use `haveI := h.1`. Establish `hψ` using `isCharAF hP.base.std`.

Generalize the expression as in `B.τ₁ = t at *`. Generalize the expression as in `B.v₁ = v at *`. Generalize the expression as in `B.ψ = ψ at *`. Establish `hc : Continuous (psv v ψ)` using `hψ.1.comp cont_at`. Take `⟨b, hb⟩` from `(GlobalTheory.GaugeEx.CharLoc.char_local F ψ hψ).1 v`.

Use `haveI := nonarch_field (Fv F v)`. Use `haveI : CharZero (Fv F v) := algebraRat.charZero _`. Take `⟨m, g, hsum, hg⟩` from `exists_cut (v.adicCompletionIntegers F) (isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)) (fun U hU => by`. Take `⟨a, ha⟩` from `GlobalTheory.SplitWeil.exists_cball_subset hU`. Conclude with `⟨a, a.ne_zero, ha (by simp [GlobalTheory.SplitWeil.cball])⟩)`.

Use the proof step `(psv v ψ) (isLocallyConstant_addChar _ hc) (b := b) hb (hι.bij.mapsTo hφ) hz`. Use `choose χ hχ hχg using fun i => hι.bij.surjOn (hg i).1`. Establish `hu : ∀ {m : ℕ} (J : Matrix (Fin m) (Fin m) E), J.det ≠ 0 → ∃ P : GL (Fin m) (Fv F v), P.1 = J.map t` using `fun J hJ => ⟨GeneralLinearGroup.mkOfDetNeZero (J.map t) (by`. Rewrite using `[show (J.map t).det = t J.det from ((t : E →+* Fv F v).map_det J).symm]`. Conclude with `(map_ne_zero t).2 hJ), rfl⟩`.

Take `⟨P, hP'⟩` from `hu _ (det_X hP.herm)`. Take `⟨Q, hQ⟩` from `hu _ (hermitian_form_det_ne_zero hP.skew)`. Establish `hco : ∀ u, coB σ X W t u = -(P.1 * u.map (piW (t.comp σ)) * Q.1ᵀ)` using `fun u => by rw [coB, hP', hQ]`. Establish `QQ : (Q⁻¹).1ᵀ * Q.1ᵀ = 1` using `by rw [← transpose_mul, Units.mul_inv, transpose_one]`. Establish `coU : ∀ A Y, coB σ X W t (spM h t A (-((P⁻¹).1 * Y * (Q⁻¹).1ᵀ))) = Y` using `fun A Y => by`.

Rewrite using `[hco, spM_snd, Matrix.mul_neg, Matrix.neg_mul, neg_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, QQ, Matrix.mul_one]`. Establish `epU : ∀ A A' : Matrix (Fin n) (Fin d) (Fv F v), ep v • spM h t A A' = spM h t A A'` using `fun A A' => by`. Use `spM_off h t A A'` as an intermediate fact. Rewrite `this` using `[sub_smul, one_smul, sub_eq_zero]`. Conclude with `this.symm`.

Establish `e1 : ∀ u : Matrix (Fin n) (Fin d) (AE F E), -((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * u.map (piW (t.comp σ)) * (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1) = coB σ X W t u` using `fun u => by simp [coB]`. Establish `sy : ∀ (U : Matrix (Fin n) (Fin d) (Fv F v)) z, symp (R` using `AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) z (spM h t (-U) 0) = atPlace v (trace (coB σ X W t z * Uᵀ)) := fun U z => by`. Use `ev_symp h t hP.herm.herm hP.skew.skew z (spM h t (-U) 0)` as an intermediate fact. Rewrite `this` using `[spM_fst, neg_neg, hco (spM h t (-U) 0), spM_snd]`. Simplify using `only [Matrix.mul_zero, Matrix.zero_mul, neg_zero, trace_zero, sub_zero] at this`.

Rewrite using `[← this, ← ep_mul, M.co.form]`. Use `conv_lhs => rw [← epU, map_smul]`. Simplify using `only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul, mul_sub]`. Use `⟨m, χ, hι.bij.injOn hφ (Submodule.sum_mem _ fun i _ => hχ i) ?_, fun i => ⟨⟨hχ i, ι, hι, fun Y hY => ?_⟩, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[map_sum, hsum]`.

Conclude with `Finset.sum_congr rfl fun i _ => (hχg i).symm`. Rewrite using `[hχg]`. Conclude with `(hg i).2.1 Y (hz Y hY)`. Introduce `r hr μ hμ z hzr`. Take `⟨Y₀, hY₀⟩` from `(hg i).2.2`.

Take `⟨U, hU, hU'⟩` from `hY₀ (coB σ X W t z) fun h' => hzr (rank_of_mul _ _ _ (rank_neg_full h'))`. Establish `hw : ep v • M.co.e (spM h t (-U) 0) = M.co.e (spM h t (-U) 0)` using `by rw [← map_smul, epU]`. Establish `ha` using `acts_schr ψ hw (χ i)`. Establish `hs` using `schr_mem_SB hc (evP v (M.co.e (spM h t (-U) 0))) (hχ i)`. Establish `eig : schr (psv v ψ) (evP v (M.co.e (spM h t (-U) 0))) (χ i) = psv v ψ (trace (Y₀ * Uᵀ)) • χ i`.

Use `hι.bij.injOn hs (Submodule.smul_mem _ _ (hχ i)) (funext fun Y => ?_)` and prove the remaining obligations. Use `hι.mult _ ((at_iff _).2 (epU _ _)) (spM_snd h t _ _) _ (hχ i) _ hs ha (spM h t 0 (-((P⁻¹).1 * Y * (Q⁻¹).1ᵀ))) ((at_iff _).2 (epU _ _)) (spM_fst h t _ _)` as an intermediate fact. Simplify using `only [e1] at this`. Rewrite `this` using `[sy, coU, ← psv_apply]`. Rewrite using `[this, map_smul, Pi.smul_apply, smul_eq_mul, hχg]`.

Distinguish the cases in `h0 : g i Y = 0`. Simplify using `[h0]`. Rewrite using `[hU Y h0]`. Establish `hΦ` using `ha r hr`. Rewrite `hΦ` using `[eig]`.

Use `coef_eigen hψ.2.1 μ (tens (evFin F v) (χ i) r) _ (M.co.e z) (atPlace v (trace (Y₀ * Uᵀ))) (hΦ.trans (funext fun x => mul_assoc _ _ _))` as an intermediate fact. Rewrite `this` using `[← neg_sub, ← M.co.form, sy, ← map_add, ← map_neg, ← map_add, ← psv_apply]`. Assume the negation of the conclusion as `h0`. Apply `hU'` to reduce the goal to its premises. Establish `h1` using `(mul_eq_right₀ h0).1 this.symm`.

Rewrite using `[← inv_eq_one, ← AddChar.map_neg_eq_inv, ← h1]`. Use `congr 1`. Rewrite using `[Matrix.sub_mul, Matrix.add_mul, trace_sub, trace_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem soCut_of : SoCut := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP φ hφ
  classical
  obtain ⟨hφ, ι, hι, hz⟩ := hφ
  have h := hP.base.cm
  haveI := h.1
  have hψ := isCharAF hP.base.std
  generalize B.τ₁ = t at *
  generalize B.v₁ = v at *
  generalize B.ψ = ψ at *
  have hc : Continuous (psv v ψ) := hψ.1.comp cont_at
  obtain ⟨b, hb⟩ := (GlobalTheory.GaugeEx.CharLoc.char_local F ψ hψ).1 v
  haveI := nonarch_field (Fv F v)
  haveI : CharZero (Fv F v) := algebraRat.charZero _
  obtain ⟨m, g, hsum, hg⟩ := exists_cut (v.adicCompletionIntegers F)
    (isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v))
    (fun U hU => by
      obtain ⟨a, ha⟩ := GlobalTheory.SplitWeil.exists_cball_subset hU
      exact ⟨a, a.ne_zero, ha (by simp [GlobalTheory.SplitWeil.cball])⟩)
    (psv v ψ) (isLocallyConstant_addChar _ hc) (b := b) hb (hι.bij.mapsTo hφ) hz
  choose χ hχ hχg using fun i => hι.bij.surjOn (hg i).1
  have hu : ∀ {m : ℕ} (J : Matrix (Fin m) (Fin m) E), J.det ≠ 0 → ∃ P : GL (Fin m) (Fv F v), P.1 = J.map t := fun J hJ =>
    ⟨GeneralLinearGroup.mkOfDetNeZero (J.map t) (by
      rw [show (J.map t).det = t J.det from ((t : E →+* Fv F v).map_det J).symm]
      exact (map_ne_zero t).2 hJ), rfl⟩
  obtain ⟨P, hP'⟩ := hu _ (det_X hP.herm)
  obtain ⟨Q, hQ⟩ := hu _ (hermitian_form_det_ne_zero hP.skew)
  have hco : ∀ u, coB σ X W t u = -(P.1 * u.map (piW (t.comp σ)) * Q.1ᵀ) := fun u => by rw [coB, hP', hQ]
  have QQ : (Q⁻¹).1ᵀ * Q.1ᵀ = 1 := by rw [← transpose_mul, Units.mul_inv, transpose_one]
  have coU : ∀ A Y, coB σ X W t (spM h t A (-((P⁻¹).1 * Y * (Q⁻¹).1ᵀ))) = Y := fun A Y => by
    rw [hco, spM_snd, Matrix.mul_neg, Matrix.neg_mul, neg_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv,
      Matrix.one_mul, Matrix.mul_assoc, QQ, Matrix.mul_one]
  have epU : ∀ A A' : Matrix (Fin n) (Fin d) (Fv F v), ep v • spM h t A A' = spM h t A A' := fun A A' => by
    have := spM_off h t A A'
    rw [sub_smul, one_smul, sub_eq_zero] at this
    exact this.symm
  have e1 : ∀ u : Matrix (Fin n) (Fin d) (AE F E), -((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * u.map (piW (t.comp σ)) *
      (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1) = coB σ X W t u := fun u => by simp [coB]
  have sy : ∀ (U : Matrix (Fin n) (Fin d) (Fv F v)) z, symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) z
      (spM h t (-U) 0) = atPlace v (trace (coB σ X W t z * Uᵀ)) := fun U z => by
    have := ev_symp h t hP.herm.herm hP.skew.skew z (spM h t (-U) 0)
    rw [spM_fst, neg_neg, hco (spM h t (-U) 0), spM_snd] at this
    simp only [Matrix.mul_zero, Matrix.zero_mul, neg_zero, trace_zero, sub_zero] at this
    rw [← this, ← ep_mul, M.co.form]
    conv_lhs => rw [← epU, map_smul]
    simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul, mul_sub]
  refine ⟨m, χ, hι.bij.injOn hφ (Submodule.sum_mem _ fun i _ => hχ i) ?_, fun i => ⟨⟨hχ i, ι, hι, fun Y hY => ?_⟩, ?_⟩⟩
  · rw [map_sum, hsum]
    exact Finset.sum_congr rfl fun i _ => (hχg i).symm
  · rw [hχg]
    exact (hg i).2.1 Y (hz Y hY)
  intro r hr μ hμ z hzr
  obtain ⟨Y₀, hY₀⟩ := (hg i).2.2
  obtain ⟨U, hU, hU'⟩ := hY₀ (coB σ X W t z) fun h' => hzr (rank_of_mul _ _ _ (rank_neg_full h'))
  have hw : ep v • M.co.e (spM h t (-U) 0) = M.co.e (spM h t (-U) 0) := by rw [← map_smul, epU]
  have ha := acts_schr ψ hw (χ i)
  have hs := schr_mem_SB hc (evP v (M.co.e (spM h t (-U) 0))) (hχ i)
  have eig : schr (psv v ψ) (evP v (M.co.e (spM h t (-U) 0))) (χ i) = psv v ψ (trace (Y₀ * Uᵀ)) • χ i := by
    refine hι.bij.injOn hs (Submodule.smul_mem _ _ (hχ i)) (funext fun Y => ?_)
    have := hι.mult _ ((at_iff _).2 (epU _ _)) (spM_snd h t _ _) _ (hχ i) _ hs ha
      (spM h t 0 (-((P⁻¹).1 * Y * (Q⁻¹).1ᵀ))) ((at_iff _).2 (epU _ _)) (spM_fst h t _ _)
    simp only [e1] at this
    rw [sy, coU, ← psv_apply] at this
    rw [this, map_smul, Pi.smul_apply, smul_eq_mul, hχg]
    by_cases h0 : g i Y = 0
    · simp [h0]
    · rw [hU Y h0]
  have hΦ := ha r hr
  rw [eig] at hΦ
  have := coef_eigen hψ.2.1 μ (tens (evFin F v) (χ i) r) _ (M.co.e z) (atPlace v (trace (Y₀ * Uᵀ)))
    (hΦ.trans (funext fun x => mul_assoc _ _ _))
  rw [← neg_sub, ← M.co.form, sy, ← map_add, ← map_neg, ← map_add, ← psv_apply] at this
  by_contra h0
  apply hU'
  have h1 := (mul_eq_right₀ h0).1 this.symm
  rw [← inv_eq_one, ← AddChar.map_neg_eq_inv, ← h1]
  congr 1
  rw [Matrix.sub_mul, Matrix.add_mul, trace_sub, trace_add]
  ring

end PositivityTheory.ThKEst
end
