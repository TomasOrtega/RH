import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerRepK
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.HalfSumRootsStandard
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdPartialZpow
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PhiPositiveDefiniteCholeskyFormula
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompComplexifiedMaxCompact
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaInt

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder

noncomputable section
namespace GlobalTheory.Dec.Equivar
variable {n : ℕ}

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal]`. Conclude with `IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun a _ => hd a)`. Unfold `Jm`. Rewrite using `[Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]`.

Use `congr 1`. Use function extensionality and compare the values at `a`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma diag_KC (ε : Fin n → Bool) {d : Fin n → ℂ} (hd : ∀ a, d a ≠ 0) : Matrix.diagonal d ∈ KC ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal]
    exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun a _ => hd a)
  · unfold Jm
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1; funext a; ring

/- English proof (translation)
Use `⟨ha.1.mul hb.1, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_assoc, hb.2, ← Matrix.mul_assoc, ha.2, Matrix.mul_assoc]`.
-/
lemma KC_mul {ε : Fin n → Bool} {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ KC ε) (hb : b ∈ KC ε) :
    a * b ∈ KC ε := by
  refine ⟨ha.1.mul hb.1, ?_⟩
  rw [Matrix.mul_assoc, hb.2, ← Matrix.mul_assoc, ha.2, Matrix.mul_assoc]

/- English proof (translation)
Establish `hd` using `(Matrix.isUnit_iff_isUnit_det a).1 ha.1`. Use `⟨Matrix.isUnit_nonsing_inv_iff.2 ha.1, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hd]`. Use `_ = Jm ε * a⁻¹ := by rw [← ha.2, Matrix.nonsing_inv_mul_cancel_left _ _ hd]`.
-/
lemma KC_inv {ε : Fin n → Bool} {a : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ KC ε) : a⁻¹ ∈ KC ε := by
  have hd := (Matrix.isUnit_iff_isUnit_det a).1 ha.1
  refine ⟨Matrix.isUnit_nonsing_inv_iff.2 ha.1, ?_⟩
  calc a⁻¹ * Jm ε = a⁻¹ * (Jm ε * a) * a⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hd]
    _ = Jm ε * a⁻¹ := by rw [← ha.2, Matrix.nonsing_inv_mul_cancel_left _ _ hd]

/- English proof (translation)
Use `⟨by simpa [Matrix.star_eq_conjTranspose] using ha.1.star, ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg Matrix.conjTranspose ha.2`. Simplify using `only [Matrix.conjTranspose_mul, Jm_conjTranspose] at h`. Conclude with `h.symm`.
-/
lemma KC_conjT {ε : Fin n → Bool} {a : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ KC ε) : aᴴ ∈ KC ε := by
  refine ⟨by simpa [Matrix.star_eq_conjTranspose] using ha.1.star, ?_⟩
  have h := congrArg Matrix.conjTranspose ha.2
  simp only [Matrix.conjTranspose_mul, Jm_conjTranspose] at h
  exact h.symm

variable {ε : Fin n → Bool} {abelian₂ : Fin n → ℝ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {w : W}

/- English proof (translation)
Use `ext_inner_left ℂ fun u => ?_` and prove the remaining obligations. Use `set c : ℂ := -((∑ a, abelian₂ a * r a : ℝ) : ℂ) with hc`. Set `f : ℂ → ℂ` to `fun s => ⟪u, τ (Matrix.diagonal fun a => Complex.exp (r a * s)) w⟫_ℂ`. Set `g : ℂ → ℂ` to `fun s => Complex.exp (c * s) * ⟪u, w⟫_ℂ`. Establish `hf : Differentiable ℂ f`.

Establish `h1 : Differentiable ℂ (fun s : ℂ => fun i j : Fin n => (Matrix.diagonal fun a => Complex.exp (r a * s)) i j)`. Use `differentiable_pi.2 fun i => differentiable_pi.2 fun j => ?_` and prove the remaining obligations. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `only [Matrix.diagonal_apply_eq]`.

Use `fun_prop`. Simplify using `only [Matrix.diagonal_apply_ne _ h]`. Use `fun_prop`. Use `(hτ.2.2.1 u w).comp (s := Set.univ) h1.differentiableOn (fun s _ => diag_KC ε fun a => Complex.exp_ne_zero _)` as an intermediate fact. Conclude with `differentiableOn_univ.1 this`.

Establish `hg : Differentiable ℂ g` using `by fun_prop`. Establish `hfg : ∀ t : ℝ, f (t * Complex.I) = g (t * Complex.I)`. Introduce `t`. Establish `hmem : Matrix.diagonal (fun a => Complex.exp (((r a * t : ℝ) : ℂ) * Complex.I)) ∈ Kset ε`. Use `⟨?_, (diag_KC ε fun a => Complex.exp_ne_zero _).2⟩` and prove the remaining obligations.

Rewrite using `[Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Rewrite using `[Pi.star_apply, Complex.star_def, Complex.mul_conj', Complex.norm_exp_ofReal_mul_I]`. Simplify using the standard rewrite rules.

Establish `h` using `hτ.2.2.2.2.2.2.1 (fun a => r a * t) hmem`. Simplify using `only [f, g]`. Establish `e : (fun a => Complex.exp (r a * (t * Complex.I))) = (fun a => Complex.exp (((r a * t : ℝ) : ℂ) * Complex.I))`. Use function extensionality and compare the values at `a`. Use `push_cast`.

Rewrite using `[mul_assoc]`. Rewrite using `[e, h, inner_smul_right, hc]`. Use `congr 2`. Simplify using `only [Pi.neg_apply, ← mul_assoc, ← Finset.sum_mul, neg_mul, Finset.sum_neg_distrib]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hfreq : ∃ᶠ z in nhdsWithin (0 : ℂ) {0}ᶜ, f z = g z`. Establish `ht : Filter.Tendsto (fun t : ℝ => (t : ℂ) * Complex.I) (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 {0}ᶜ)`. Use `tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Establish `: Continuous fun t : ℝ => (t : ℂ) * Complex.I` using `by fun_prop`.

Simplify using `using (this.tendsto 0).mono_left nhdsWithin_le_nhds`. Use `filter_upwards [self_mem_nhdsWithin] with t ht`. Simplify using `using ht`. Conclude with `ht.frequently (Filter.Frequently.of_forall hfg)`. Use `AnalyticOnNhd.eq_of_frequently_eq (hf.differentiableOn.analyticOnNhd isOpen_univ) (hg.differentiableOn.analyticOnNhd isOpen_univ) hfreq` as an intermediate fact.

Use `congrFun this 1` as an intermediate fact. Simplify `this` using `[f, g, inner_smul_right]`.
-/
lemma tau_diag (hτ : IsTau ε abelian₂ τ w) (r : Fin n → ℝ) :
    τ (Matrix.diagonal fun a => Complex.exp (r a)) w = Complex.exp (-((∑ a, abelian₂ a * r a : ℝ) : ℂ)) • w := by
  refine ext_inner_left ℂ fun u => ?_
  set c : ℂ := -((∑ a, abelian₂ a * r a : ℝ) : ℂ) with hc
  let f : ℂ → ℂ := fun s => ⟪u, τ (Matrix.diagonal fun a => Complex.exp (r a * s)) w⟫_ℂ
  let g : ℂ → ℂ := fun s => Complex.exp (c * s) * ⟪u, w⟫_ℂ
  have hf : Differentiable ℂ f := by
    have h1 : Differentiable ℂ (fun s : ℂ => fun i j : Fin n =>
        (Matrix.diagonal fun a => Complex.exp (r a * s)) i j) := by
      refine differentiable_pi.2 fun i => differentiable_pi.2 fun j => ?_
      by_cases h : i = j
      · subst h; simp only [Matrix.diagonal_apply_eq]; fun_prop
      · simp only [Matrix.diagonal_apply_ne _ h]; fun_prop
    have := (hτ.2.2.1 u w).comp (s := Set.univ) h1.differentiableOn
      (fun s _ => diag_KC ε fun a => Complex.exp_ne_zero _)
    exact differentiableOn_univ.1 this
  have hg : Differentiable ℂ g := by fun_prop
  have hfg : ∀ t : ℝ, f (t * Complex.I) = g (t * Complex.I) := by
    intro t
    have hmem : Matrix.diagonal (fun a => Complex.exp (((r a * t : ℝ) : ℂ) * Complex.I)) ∈ Kset ε := by
      refine ⟨?_, (diag_KC ε fun a => Complex.exp_ne_zero _).2⟩
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext a
      rw [Pi.star_apply, Complex.star_def, Complex.mul_conj', Complex.norm_exp_ofReal_mul_I]
      simp
    have h := hτ.2.2.2.2.2.2.1 (fun a => r a * t) hmem
    simp only [f, g]
    have e : (fun a => Complex.exp (r a * (t * Complex.I))) =
        (fun a => Complex.exp (((r a * t : ℝ) : ℂ) * Complex.I)) := by
      funext a; push_cast; rw [mul_assoc]
    rw [e, h, inner_smul_right, hc]
    congr 2
    simp only [Pi.neg_apply, ← mul_assoc, ← Finset.sum_mul, neg_mul, Finset.sum_neg_distrib]
    push_cast; ring
  have hfreq : ∃ᶠ z in nhdsWithin (0 : ℂ) {0}ᶜ, f z = g z := by
    have ht : Filter.Tendsto (fun t : ℝ => (t : ℂ) * Complex.I) (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 {0}ᶜ) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Continuous fun t : ℝ => (t : ℂ) * Complex.I := by fun_prop
        simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        simpa using ht
    exact ht.frequently (Filter.Frequently.of_forall hfg)
  have := AnalyticOnNhd.eq_of_frequently_eq (hf.differentiableOn.analyticOnNhd isOpen_univ)
    (hg.differentiableOn.analyticOnNhd isOpen_univ) hfreq
  have := congrFun this 1
  simpa [f, g, inner_smul_right] using this

/- English proof (translation)
Establish `hne : ∀ l, b l l ≠ 0` using `fun l => (hpos l).ne'`. Establish `hn : ∀ l, 0 < ‖b l l‖` using `fun l => norm_pos_iff.2 (hne l)`. Establish `hexp : ∀ l, Complex.exp (Real.log ‖b l l‖ : ℝ) = b l l` using `fun l => by`. Rewrite using `[← Complex.ofReal_exp, Real.exp_log (hn l)]`. Conclude with `Complex.norm_of_nonneg' (hpos l).le`.

Establish `hu : Matrix.diagonal (fun a => (b a a)⁻¹) * b ∈ KC ε` using `KC_mul (diag_KC ε fun a => inv_ne_zero (hne a)) hb`. Establish `hu1 : IsLoUni (Matrix.diagonal (fun a => (b a a)⁻¹) * b)`. Introduce `i j`. Use `⟨fun h => by simp [Matrix.diagonal_mul, hlo i j h], fun h => ?_⟩` and prove the remaining obligations. Substitute `h` using the available equality.

Simplify using `[Matrix.diagonal_mul, hne]`. Establish `e : b = (Matrix.diagonal fun a => Complex.exp (Real.log ‖b a a‖ : ℝ)) * (Matrix.diagonal (fun a => (b a a)⁻¹) * b)`. Simplify using `only [hexp]`. Use extensionality with `i j`. Simplify using `[Matrix.diagonal_mul, hne]`.

Establish `h1` using `hτ.2.1.2 _ (diag_KC ε (d := fun a => Complex.exp (Real.log ‖b a a‖ : ℝ)) fun a => Complex.exp_ne_zero _) _ hu`. Rewrite `h1` using `[← e]`. Rewrite using `[h1, ContinuousLinearMap.comp_apply, hτ.2.2.2.2.2.2.2 _ hu hu1, tau_diag hτ]`. Use `congr 1`. Rewrite using `[← Complex.ofReal_neg, ← Complex.ofReal_exp, ← Finset.sum_neg_distrib, Real.exp_sum]`.

Use `congr 1`. Use `Finset.prod_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Real.rpow_def_of_pos (hn l)]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma tau_lo (hτ : IsTau ε abelian₂ τ w) {b : Matrix (Fin n) (Fin n) ℂ} (hb : b ∈ KC ε) (hlo : IsLo b)
    (hpos : ∀ l, 0 < b l l) : τ b w = ((∏ l, ‖b l l‖ ^ (-(abelian₂ l)) : ℝ) : ℂ) • w := by
  have hne : ∀ l, b l l ≠ 0 := fun l => (hpos l).ne'
  have hn : ∀ l, 0 < ‖b l l‖ := fun l => norm_pos_iff.2 (hne l)
  have hexp : ∀ l, Complex.exp (Real.log ‖b l l‖ : ℝ) = b l l := fun l => by
    rw [← Complex.ofReal_exp, Real.exp_log (hn l)]
    exact Complex.norm_of_nonneg' (hpos l).le
  have hu : Matrix.diagonal (fun a => (b a a)⁻¹) * b ∈ KC ε :=
    KC_mul (diag_KC ε fun a => inv_ne_zero (hne a)) hb
  have hu1 : IsLoUni (Matrix.diagonal (fun a => (b a a)⁻¹) * b) := by
    intro i j
    refine ⟨fun h => by simp [Matrix.diagonal_mul, hlo i j h], fun h => ?_⟩
    subst h
    simp [Matrix.diagonal_mul, hne]
  have e : b = (Matrix.diagonal fun a => Complex.exp (Real.log ‖b a a‖ : ℝ)) *
      (Matrix.diagonal (fun a => (b a a)⁻¹) * b) := by
    simp only [hexp]
    ext i j
    simp [Matrix.diagonal_mul, hne]
  have h1 := hτ.2.1.2 _ (diag_KC ε (d := fun a => Complex.exp (Real.log ‖b a a‖ : ℝ))
    fun a => Complex.exp_ne_zero _) _ hu
  rw [← e] at h1
  rw [h1, ContinuousLinearMap.comp_apply, hτ.2.2.2.2.2.2.2 _ hu hu1, tau_diag hτ]
  congr 1
  rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, ← Finset.sum_neg_distrib, Real.exp_sum]
  congr 1
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [Real.rpow_def_of_pos (hn l)]
  congr 1; ring

/- English proof (translation)
Use `hτ.1` as an intermediate fact. Establish `e : (fun k => τ k v) = fun k => ∑ i, ⟪stdOrthonormalBasis ℂ W i, τ k v⟫_ℂ • stdOrthonormalBasis ℂ W i`. Use function extensionality and compare the values at `k`. Rewrite using `[(stdOrthonormalBasis ℂ W).sum_repr']`. Rewrite using `[e]`.

Use `continuousOn_finsetSum _ fun i _ => ContinuousOn.smul ?_ continuousOn_const` and prove the remaining obligations. Conclude with `(hτ.2.2.1 _ v).continuousOn.mono fun k hk => FormF.K_KC hk`.
-/
lemma tau_cont (hτ : IsTau ε abelian₂ τ w) (v : W) : ContinuousOn (fun k => τ k v) (Kset ε) := by
  have := hτ.1
  have e : (fun k => τ k v) = fun k => ∑ i, ⟪stdOrthonormalBasis ℂ W i, τ k v⟫_ℂ • stdOrthonormalBasis ℂ W i := by
    funext k
    rw [(stdOrthonormalBasis ℂ W).sum_repr']
  rw [e]
  refine continuousOn_finsetSum _ fun i _ => ContinuousOn.smul ?_ continuousOn_const
  exact (hτ.2.2.1 _ v).continuousOn.mono fun k hk => FormF.K_KC hk

/- English proof (translation)
Take `⟨m, hm⟩` from `hlam.2 l`. Establish `h1` using `half_sum_roots_standard n ε l`. Establish `h2 : lam l + Formalism.QuantumDeterminants.rhoStd n l = ((m + n - 1 - (l : ℕ) : ℤ) : ℝ)`. Simplify using `only [Formalism.QuantumDeterminants.rhoStd]`. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : (muInt lam l : ℝ) = lam l + Formalism.QuantumDeterminants.rhoStd n l`. Rewrite using `[muInt, h2, Int.floor_intCast]`. Rewrite using `[h3]`. Simplify using `only [lowK, Formalism.QuantumDeterminants.rhoStd, Pi.add_apply, Pi.sub_apply]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma muInt_cast {lam : Fin n → ℝ} (hlam : IsHCParam lam) (ε : Fin n → Bool) (l : Fin n) :
    (muInt lam l : ℝ) = lowK ε lam l + 2 * rhoC ε l := by
  obtain ⟨m, hm⟩ := hlam.2 l
  have h1 := half_sum_roots_standard n ε l
  have h2 : lam l + Formalism.QuantumDeterminants.rhoStd n l = ((m + n - 1 - (l : ℕ) : ℤ) : ℝ) := by
    simp only [Formalism.QuantumDeterminants.rhoStd]; push_cast; linarith
  have h3 : (muInt lam l : ℝ) = lam l + Formalism.QuantumDeterminants.rhoStd n l := by
    rw [muInt, h2, Int.floor_intCast]
  rw [h3]
  simp only [lowK, Formalism.QuantumDeterminants.rhoStd, Pi.add_apply, Pi.sub_apply]
  linarith

/- English proof (translation)
Simplify using `only [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_zpow, ← Complex.ofReal_prod, ← Complex.ofReal_mul, ← Finset.prod_mul_distrib]`. Use `congr 1`. Use `Finset.prod_congr rfl fun l _ => ?_` and prove the remaining obligations. Establish `hn : 0 < ‖d l‖` using `norm_pos_iff.2 (hd l)`. Rewrite using `[← Real.rpow_intCast, ← Real.rpow_natCast, ← Real.rpow_mul hn.le, ← Real.rpow_add hn, ← Real.rpow_add hn]`.

Use `congr 1`. Use `push_cast`. Rewrite using `[muInt_cast hlam ε]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma scalar_eq {lam : Fin n → ℝ} (hlam : IsHCParam lam) (ε : Fin n → Bool) {d : Fin n → ℂ} (hd : ∀ l, d l ≠ 0) :
    (∏ l, (d l * star (d l)) ^ (-(muInt lam l))) * ((∏ l, ‖d l‖ ^ (4 * rhoC ε l) : ℝ) : ℂ) =
      ((∏ l, ‖d l‖ ^ (-(lowK ε lam l)) : ℝ) : ℂ) * ((∏ l, ‖d l‖ ^ (-(lowK ε lam l)) : ℝ) : ℂ) := by
  simp only [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_zpow,
    ← Complex.ofReal_prod, ← Complex.ofReal_mul, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun l _ => ?_
  have hn : 0 < ‖d l‖ := norm_pos_iff.2 (hd l)
  rw [← Real.rpow_intCast, ← Real.rpow_natCast, ← Real.rpow_mul hn.le, ← Real.rpow_add hn, ← Real.rpow_add hn]
  congr 1
  push_cast
  rw [muInt_cast hlam ε]
  ring

/- English proof (translation)
Introduce `n ε lam W _ _ τ w hlam hτ x y hx hy`. Establish `hyd` using `(Matrix.isUnit_iff_isUnit_det y).1 hy.1`. Establish `hx' : (y * x * yᴴ).PosDef` using `hx.mul_mul_conjTranspose_same (Matrix.vecMul_injective_of_isUnit hy.1)`. Take `⟨κ, β, hκ, -⟩` from `hI n ε`. Establish `hmem : ∀ k : KG ε, y⁻¹ * toMK k ∈ KC ε` using `fun k => KC_mul (KC_inv hy) (FormF.K_KC k.2)`.

Use extensionality with `u`. Use `ext_inner_left ℂ fun v => ?_` and prove the remaining obligations. Establish `hadj : ∀ a : W, ⟪v, τ y a⟫_ℂ = ⟪τ yᴴ v, a⟫_ℂ` using `fun a => by`. Rewrite using `[hτ.2.2.2.1 _ (KC_conjT hy), Matrix.conjTranspose_conjTranspose]`. Apply the tactic sequence `rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hadj, FormF.psEntry hP n ε lam W τ w hτ.1 (tau_cont hτ) _ hx', FormF.psEntry hP n ε lam W τ w hτ.1 (tau_cont hτ) _ hx]`.

Use `congr 1`. Establish `hF : ContinuousOn (fun k : Matrix (Fin n) (Fin n) ℂ => Phi lam (k⁻¹ * x * k) * (⟪τ yᴴ v, τ k w⟫_ℂ * ⟪τ k w, τ yᴴ u⟫_ℂ)) (Kset ε)`. Use `ContinuousOn.mul ?_ ((ContinuousOn.inner (𝕜 := ℂ) continuousOn_const (tau_cont hτ w)).mul (ContinuousOn.inner (𝕜 := ℂ) (tau_cont hτ w) continuousOn_const))` and prove the remaining obligations. Use `ContinuousOn.congr (f := fun k => Phi lam (kᴴ * x * k)) ?_ fun k hk => by simp only [FormF.K_inv hk]` and prove the remaining obligations. Unfold `Phi`.

Use `continuousOn_finsetProd _ fun i _ => ContinuousOn.zpow₀ ?_ _ fun k hk => Or.inl ?_` and prove the remaining obligations. Unfold `leadMinor`. Conclude with `(((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id).matrix_submatrix _ _).matrix_det.continuousOn`. Conclude with `(hP n lam _ (hx.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit (FormF.K_KC hk).1))).1 i`. Rewrite using `[← hH n ε y⁻¹ (fun k => κ (y⁻¹ * toMK k)) (fun k => β (y⁻¹ * toMK k)) (KC_inv hy) (fun k => hκ _ (hmem k)) _ hF]`.

Use `congr 1`. Use function extensionality and compare the values at `k`. Take `⟨h1, h2, h3, h4, h5⟩` from `hκ _ (hmem k)`. Establish `hk : toMK k ∈ Kset ε` using `k.2`. Generalize the expression as in `κ (y⁻¹ * toMK k) = c at *`.

Generalize the expression as in `β (y⁻¹ * toMK k) = b at *`. Generalize the expression as in `toMK k = g at *`. Establish `hg : g = y * (c * b)` using `by rw [← h5, Matrix.mul_nonsing_inv_cancel_left _ _ hyd]`. Establish `hgg : gᴴ * g = 1` using `Unitary.star_mul_self_of_mem hk.1`. Establish `hc : cᴴ = b * gᴴ * y`.

Rewrite using `[← FormF.K_inv h1]`. Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Establish `: gᴴ * y * c * b = 1`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, ← hg, hgg]`. Use `mul_eq_one_comm.1 this` as an intermediate fact.

Simplify `this` using `only [Matrix.mul_assoc]`. Establish `hz : c⁻¹ * x * c = b * (g⁻¹ * (y * x * yᴴ) * g) * bᴴ`. Establish `: c = yᴴ * g * bᴴ`. Rewrite using `[← Matrix.conjTranspose_conjTranspose c, hc]`. Simplify using `[Matrix.mul_assoc]`.

Rewrite using `[FormF.K_inv h1, FormF.K_inv hk, hc]`. Use `conv_lhs => rw [this]`. Simplify using `only [Matrix.mul_assoc]`. Establish `hne : ∀ l, b l l ≠ 0` using `fun l => (h4 l).ne'`. Establish `hΩ : g⁻¹ * (y * x * yᴴ) * g ∈ Omega n`.

Rewrite using `[FormF.K_inv hk]`. Conclude with `(hP n lam _ (hx'.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit (FormF.K_KC hk).1))).1`. Establish `hΦ` using `(hT n lam b _ bᴴ h3 (fun i j h => by simp [h3 j i h]) (fun l => ⟨hne l, by simp [hne l]⟩) hΩ).2`. Establish `hw : τ g w = ((∏ l, ‖b l l‖ ^ (-(lowK ε lam l)) : ℝ) : ℂ) • τ y (τ c w)` using `by conv_lhs => rw [hg]`. Rewrite using `[hτ.2.1.2 _ hy _ (KC_mul (FormF.K_KC h1) h2), hτ.2.1.2 _ (FormF.K_KC h1) _ h2]`.

Simplify using `only [ContinuousLinearMap.comp_apply]`. Rewrite using `[tau_lo hτ h2 h3 h4, map_smul, map_smul]`. Establish `hs` using `scalar_eq hlam ε (d := fun l => b l l) hne`. Rewrite using `[hz, hΦ, hw, inner_smul_right, inner_smul_left, Complex.conj_ofReal, hadj, hτ.2.2.2.1 _ hy]`. Simplify using `only [Matrix.conjTranspose_apply]`.

Take the linear combination `(-(Phi lam (g⁻¹ * (y * x * yᴴ) * g) * (⟪τ yᴴ v, τ c w⟫_ℂ * ⟪τ c w, τ yᴴ u⟫_ℂ))) * hs`.
-/
theorem psEquiv_of (hT : PhiTri) (hP : PhiPos) (hI : IwasawaKC) (hH : IwasawaInt) : PsEquiv := by
  intro n ε lam W _ _ τ w hlam hτ x y hx hy
  have hyd := (Matrix.isUnit_iff_isUnit_det y).1 hy.1
  have hx' : (y * x * yᴴ).PosDef := hx.mul_mul_conjTranspose_same (Matrix.vecMul_injective_of_isUnit hy.1)
  obtain ⟨κ, β, hκ, -⟩ := hI n ε
  have hmem : ∀ k : KG ε, y⁻¹ * toMK k ∈ KC ε := fun k => KC_mul (KC_inv hy) (FormF.K_KC k.2)
  ext u
  refine ext_inner_left ℂ fun v => ?_
  have hadj : ∀ a : W, ⟪v, τ y a⟫_ℂ = ⟪τ yᴴ v, a⟫_ℂ := fun a => by
    rw [hτ.2.2.2.1 _ (KC_conjT hy), Matrix.conjTranspose_conjTranspose]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hadj,
    FormF.psEntry hP n ε lam W τ w hτ.1 (tau_cont hτ) _ hx', FormF.psEntry hP n ε lam W τ w hτ.1 (tau_cont hτ) _ hx]
  congr 1
  have hF : ContinuousOn (fun k : Matrix (Fin n) (Fin n) ℂ =>
      Phi lam (k⁻¹ * x * k) * (⟪τ yᴴ v, τ k w⟫_ℂ * ⟪τ k w, τ yᴴ u⟫_ℂ)) (Kset ε) := by
    refine ContinuousOn.mul ?_ ((ContinuousOn.inner (𝕜 := ℂ) continuousOn_const (tau_cont hτ w)).mul
      (ContinuousOn.inner (𝕜 := ℂ) (tau_cont hτ w) continuousOn_const))
    refine ContinuousOn.congr (f := fun k => Phi lam (kᴴ * x * k)) ?_ fun k hk => by simp only [FormF.K_inv hk]
    unfold Phi
    refine continuousOn_finsetProd _ fun i _ => ContinuousOn.zpow₀ ?_ _ fun k hk => Or.inl ?_
    · unfold leadMinor
      exact (((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
        continuous_id).matrix_submatrix _ _).matrix_det.continuousOn
    · exact (hP n lam _ (hx.conjTranspose_mul_mul_same
        (Matrix.mulVec_injective_of_isUnit (FormF.K_KC hk).1))).1 i
  rw [← hH n ε y⁻¹ (fun k => κ (y⁻¹ * toMK k)) (fun k => β (y⁻¹ * toMK k)) (KC_inv hy)
    (fun k => hκ _ (hmem k)) _ hF]
  congr 1
  funext k
  obtain ⟨h1, h2, h3, h4, h5⟩ := hκ _ (hmem k)
  have hk : toMK k ∈ Kset ε := k.2
  generalize κ (y⁻¹ * toMK k) = c at *
  generalize β (y⁻¹ * toMK k) = b at *
  generalize toMK k = g at *
  have hg : g = y * (c * b) := by rw [← h5, Matrix.mul_nonsing_inv_cancel_left _ _ hyd]
  have hgg : gᴴ * g = 1 := Unitary.star_mul_self_of_mem hk.1
  have hc : cᴴ = b * gᴴ * y := by
    rw [← FormF.K_inv h1]
    apply Matrix.inv_eq_left_inv
    have : gᴴ * y * c * b = 1 := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← hg, hgg]
    have := mul_eq_one_comm.1 this
    simpa only [Matrix.mul_assoc] using this
  have hz : c⁻¹ * x * c = b * (g⁻¹ * (y * x * yᴴ) * g) * bᴴ := by
    have : c = yᴴ * g * bᴴ := by
      rw [← Matrix.conjTranspose_conjTranspose c, hc]
      simp [Matrix.mul_assoc]
    rw [FormF.K_inv h1, FormF.K_inv hk, hc]
    conv_lhs => rw [this]
    simp only [Matrix.mul_assoc]
  have hne : ∀ l, b l l ≠ 0 := fun l => (h4 l).ne'
  have hΩ : g⁻¹ * (y * x * yᴴ) * g ∈ Omega n := by
    rw [FormF.K_inv hk]
    exact (hP n lam _ (hx'.conjTranspose_mul_mul_same
        (Matrix.mulVec_injective_of_isUnit (FormF.K_KC hk).1))).1
  have hΦ := (hT n lam b _ bᴴ h3 (fun i j h => by simp [h3 j i h]) (fun l => ⟨hne l, by simp [hne l]⟩) hΩ).2
  have hw : τ g w = ((∏ l, ‖b l l‖ ^ (-(lowK ε lam l)) : ℝ) : ℂ) • τ y (τ c w) := by
    conv_lhs => rw [hg]
    rw [hτ.2.1.2 _ hy _ (KC_mul (FormF.K_KC h1) h2), hτ.2.1.2 _ (FormF.K_KC h1) _ h2]
    simp only [ContinuousLinearMap.comp_apply]
    rw [tau_lo hτ h2 h3 h4, map_smul, map_smul]
  have hs := scalar_eq hlam ε (d := fun l => b l l) hne
  rw [hz, hΦ, hw, inner_smul_right, inner_smul_left, Complex.conj_ofReal, hadj, hτ.2.2.2.1 _ hy]
  simp only [Matrix.conjTranspose_apply]
  linear_combination (-(Phi lam (g⁻¹ * (y * x * yᴴ) * g) * (⟪τ yᴴ v, τ c w⟫_ℂ * ⟪τ c w, τ yᴴ u⟫_ℂ))) * hs

/- English proof (translation)
The claim follows from `psEquiv_of GlobalTheory.PhiTriangular.phiTri GlobalTheory.Dec.phiPos GlobalTheory.Dec.iwasawaKC GlobalTheory.IwaInt.iwasawaInt`.
-/
theorem psEquiv : PsEquiv := psEquiv_of GlobalTheory.PhiTriangular.phiTri GlobalTheory.Dec.phiPos GlobalTheory.Dec.iwasawaKC GlobalTheory.IwaInt.iwasawaInt

end GlobalTheory.Dec.Equivar
