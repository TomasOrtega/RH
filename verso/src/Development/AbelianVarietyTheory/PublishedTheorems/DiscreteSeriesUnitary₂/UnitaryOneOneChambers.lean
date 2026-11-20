import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.SubmatrixMemUJsetIff
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered

open Formalism.MainNotions.S MeasureTheory Matrix
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.FormalDegree.Model

def detPow (n : ℕ) (m : ℤ) (g : Matrix (Fin n) (Fin n) ℂ) : ℂ →L[ℂ] ℂ :=
  (g.det ^ m) • ContinuousLinearMap.id ℂ ℂ

/- English proof (translation)
Simplify using `[detPow]`.
-/
theorem detPow_apply (n : ℕ) (m : ℤ) (g : Matrix (Fin n) (Fin n) ℂ) (v : ℂ) :
    detPow n m g v = g.det ^ m * v := by simp [detPow]

/- English proof (translation)
Establish `h : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε` using `hg`. Establish `h1` using `congrArg Matrix.det h`. Establish `h2 : (Formalism.REAL.Jm ε).det * (Formalism.REAL.Jm ε).det = 1`. Rewrite using `[← Matrix.det_mul, Formalism.REAL.Jm_mul_self, Matrix.det_one]`. Establish `h3 : (Formalism.REAL.Jm ε).det ≠ 0` using `left_ne_zero_of_mul_eq_one h2`.

Rewrite `h1` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]`. Establish `h4 : star g.det * g.det = 1`. Apply `mul_left_cancel₀ h3` to reduce the goal to its premises. Take the linear combination `h1`. Establish `h5` using `congrArg norm h4`.

Rewrite `h5` using `[norm_mul, norm_star, norm_one]`. Use polynomial arithmetic with `[norm_nonneg g.det]`.
-/
theorem norm_det {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    ‖g.det‖ = 1 := by
  have h : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  have h1 := congrArg Matrix.det h
  have h2 : (Formalism.REAL.Jm ε).det * (Formalism.REAL.Jm ε).det = 1 := by
    rw [← Matrix.det_mul, Formalism.REAL.Jm_mul_self, Matrix.det_one]
  have h3 : (Formalism.REAL.Jm ε).det ≠ 0 := left_ne_zero_of_mul_eq_one h2
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h1
  have h4 : star g.det * g.det = 1 := by
    apply mul_left_cancel₀ h3
    linear_combination h1
  have h5 := congrArg norm h4
  rw [norm_mul, norm_star, norm_one] at h5
  nlinarith [norm_nonneg g.det]

/- English proof (translation)
Establish `hemb` using `Formalism.REAL.isClosedEmbeddingMatrix n (fun _ => s)`. Rewrite using `[← isCompact_univ_iff, hemb.1.isEmbedding.isCompact_iff, Set.image_univ, hemb.2]`. Use `(Formalism.REAL.maximal_compact_facts n (fun _ => s)).2.1` as an intermediate fact. Rewrite `this` using `[GlobalTheory.DefiniteCheck.kset_const]`. Then use the resulting hypothesis.
-/
theorem compact_const (n : ℕ) (s : Bool) : CompactSpace (Formalism.REAL.UJ (fun _ : Fin n => s)) := by
  have hemb := Formalism.REAL.isClosedEmbeddingMatrix n (fun _ => s)
  rw [← isCompact_univ_iff, hemb.1.isEmbedding.isCompact_iff, Set.image_univ, hemb.2]
  have := (Formalism.REAL.maximal_compact_facts n (fun _ => s)).2.1
  rwa [GlobalTheory.DefiniteCheck.kset_const] at this

def cst (n : ℕ) (s : Bool) : ℝ := ((Formalism.REAL.muG (fun _ : Fin n => s)).real Set.univ)⁻¹

/- English proof (translation)
Use `compact_const n s` as an intermediate fact. Use `inv_pos.2 (ENNReal.toReal_pos ?_ (measure_ne_top _ _))` and prove the remaining obligations. Conclude with `(isOpen_univ.measure_pos _ Set.univ_nonempty).ne'`.
-/
theorem cst_pos (n : ℕ) (s : Bool) : 0 < cst n s := by
  have := compact_const n s
  refine inv_pos.2 (ENNReal.toReal_pos ?_ (measure_ne_top _ _))
  exact (isOpen_univ.measure_pos _ Set.univ_nonempty).ne'

/- English proof (translation)
Use `compact_const n s` as an intermediate fact. Use `⟨cst_pos n s, fun v w v' w' => ?_⟩` and prove the remaining obligations. Establish `key : (fun g : Formalism.REAL.UJ (fun _ : Fin n => s) => coefOn σ v w g * star (coefOn σ v' w' g)) = fun _ => ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ`. Use function extensionality and compare the values at `g`. Take `⟨z, hz, hg⟩` from `hσ (umat g) g.2`.

Take `⟨a, rfl⟩` from `he v`. Take `⟨b, rfl⟩` from `he w`. Take `⟨a', rfl⟩` from `he v'`. Take `⟨b', rfl⟩` from `he w'`. Establish `h1 : z * (starRingEnd ℂ) z = 1` using `by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; simp`.

Establish `h2 : (starRingEnd ℂ) ⟪e, e⟫_ℂ = ⟪e, e⟫_ℂ` using `inner_conj_symm e e`. Simplify using `only [coefOn, map_smul, hg, inner_smul_left, inner_smul_right, RCLike.star_def, map_mul, h2, RingHomCompTriple.comp_apply, RingHom.id_apply, Complex.conj_conj]`. Take the linear combination `(a * (starRingEnd ℂ) b * (starRingEnd ℂ) a' * b' * ⟪e, e⟫_ℂ * ⟪e, e⟫_ℂ) * h1`. Rewrite using `[key]`. Use `⟨integrable_const _, ?_⟩` and prove the remaining obligations.

Rewrite using `[integral_const, cst]`. Simplify using `[div_eq_mul_inv, mul_comm]`.
-/
theorem isFdeg_of_scalar {n : ℕ} {s : Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (e : H) (he : ∀ x : H, ∃ a : ℂ, x = a • e)
    (hσ : ∀ g ∈ UJset (fun _ : Fin n => s), ∃ z : ℂ, ‖z‖ = 1 ∧ σ g e = z • e) :
    IsFdeg (Formalism.REAL.muG (fun _ : Fin n => s)) σ (cst n s) := by
  have := compact_const n s
  refine ⟨cst_pos n s, fun v w v' w' => ?_⟩
  have key : (fun g : Formalism.REAL.UJ (fun _ : Fin n => s) => coefOn σ v w g * star (coefOn σ v' w' g)) =
      fun _ => ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ := by
    funext g
    obtain ⟨z, hz, hg⟩ := hσ (umat g) g.2
    obtain ⟨a, rfl⟩ := he v
    obtain ⟨b, rfl⟩ := he w
    obtain ⟨a', rfl⟩ := he v'
    obtain ⟨b', rfl⟩ := he w'
    have h1 : z * (starRingEnd ℂ) z = 1 := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; simp
    have h2 : (starRingEnd ℂ) ⟪e, e⟫_ℂ = ⟪e, e⟫_ℂ := inner_conj_symm e e
    simp only [coefOn, map_smul, hg, inner_smul_left, inner_smul_right, RCLike.star_def, map_mul, h2,
      RingHomCompTriple.comp_apply, RingHom.id_apply, Complex.conj_conj]
    linear_combination (a * (starRingEnd ℂ) b * (starRingEnd ℂ) a' * b' * ⟪e, e⟫_ℂ * ⟪e, e⟫_ℂ) * h1
  rw [key]
  refine ⟨integrable_const _, ?_⟩
  rw [integral_const, cst]
  simp [div_eq_mul_inv, mul_comm]

def lamDet (n : ℕ) (m : ℤ) : Fin n → ℝ := fun a => (m : ℝ) + Formalism.QuantumDeterminants.rhoStd n a

/- English proof (translation)
Use `⟨fun a b h => ?_, fun a => ⟨m - (a : ℕ), ?_⟩⟩` and prove the remaining obligations. Establish `: ((a : ℕ) : ℝ) < (b : ℕ)` using `by exact_mod_cast h`. Simplify using `only [lamDet, Formalism.QuantumDeterminants.rhoStd]`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [lamDet, Formalism.QuantumDeterminants.rhoStd]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lamDet_hc (n : ℕ) (m : ℤ) : Formalism.QuantumDeterminants.IsHCParam (lamDet n m) := by
  refine ⟨fun a b h => ?_, fun a => ⟨m - (a : ℕ), ?_⟩⟩
  · have : ((a : ℕ) : ℝ) < (b : ℕ) := by exact_mod_cast h
    simp only [lamDet, Formalism.QuantumDeterminants.rhoStd]; linarith
  · simp only [lamDet, Formalism.QuantumDeterminants.rhoStd]; push_cast; ring

/- English proof (translation)
Unfold `Formalism.QuantumDeterminants.fdegHC`. Rewrite using `[div_eq_one_iff_eq]`. Use `Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b hb => ?_` and prove the remaining obligations. Establish `: ((a : ℕ) : ℝ) < (b : ℕ)` using `by exact_mod_cast (Finset.mem_filter.1 hb).2`. Simplify using `only [lamDet, Formalism.QuantumDeterminants.rhoStd]`.

Rewrite using `[abs_of_pos (by linarith)]; ring`. Use `Finset.prod_ne_zero_iff.2 fun a _ => Finset.prod_ne_zero_iff.2 fun b hb => ?_` and prove the remaining obligations. Establish `: ((a : ℕ) : ℝ) < (b : ℕ)` using `by exact_mod_cast (Finset.mem_filter.1 hb).2`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem fdeg_lamDet (n : ℕ) (m : ℤ) : Formalism.QuantumDeterminants.fdegHC (lamDet n m) = 1 := by
  unfold Formalism.QuantumDeterminants.fdegHC
  rw [div_eq_one_iff_eq]
  · refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b hb => ?_
    have : ((a : ℕ) : ℝ) < (b : ℕ) := by exact_mod_cast (Finset.mem_filter.1 hb).2
    simp only [lamDet, Formalism.QuantumDeterminants.rhoStd]
    rw [abs_of_pos (by linarith)]; ring
  · refine Finset.prod_ne_zero_iff.2 fun a _ => Finset.prod_ne_zero_iff.2 fun b hb => ?_
    have : ((a : ℕ) : ℝ) < (b : ℕ) := by exact_mod_cast (Finset.mem_filter.1 hb).2
    linarith

/- English proof (translation)
Use function extensionality and compare the values at `a`. Rewrite using `[GlobalTheory.DefiniteCheck.lowK_const]`. Simplify using `only [lamDet, Formalism.QuantumDeterminants.rhoStd]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lowK_lamDet (n : ℕ) (s : Bool) (m : ℤ) :
    Formalism.QuantumDeterminants.lowK (fun _ : Fin n => s) (lamDet n m) = fun _ => (m : ℝ) := by
  funext a
  rw [GlobalTheory.DefiniteCheck.lowK_const]
  simp only [lamDet, Formalism.QuantumDeterminants.rhoStd]; ring

/- English proof (translation)
Rewrite using `[detPow_apply, Matrix.det_diagonal, ← Complex.exp_sum, ← Complex.exp_int_mul, smul_eq_mul]`. Use `congr 2`. Use `push_cast`. Rewrite using `[Finset.mul_sum, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun a _ => by ring`.
-/
theorem detPow_diag (n : ℕ) (m : ℤ) (θ : Fin n → ℝ) (v : ℂ) :
    detPow n m (Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) v =
      Complex.exp (((∑ a, (m : ℝ) * θ a : ℝ) : ℂ) * Complex.I) • v := by
  rw [detPow_apply, Matrix.det_diagonal, ← Complex.exp_sum, ← Complex.exp_int_mul, smul_eq_mul]
  congr 2
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => by ring

/- English proof (translation)
Rewrite using `[GlobalTheory.RealPar.isDS_const_iff]`. Use `⟨inferInstance, inferInstance, ⟨⟨?_, fun a _ b _ => ?_⟩, fun g hg v => ?_, fun v => ?_⟩, inferInstance, fun _ _ _ _ => trivial, fun S _ _ => eq_bot_or_eq_top S, ?_, ?_⟩` and prove the remaining obligations. Use `ext`. Simplify using `[detPow_apply]`. Use `ext`.

Simplify using `[detPow_apply, mul_zpow]`. Rewrite using `[detPow_apply, norm_mul, norm_zpow, norm_det hg]`. Simplify using the standard rewrite rules. Simplify using `only [detPow_apply]`. Use `ContinuousOn.mul (ContinuousOn.zpow₀ (continuous_id.matrix_det.continuousOn) m fun g hg => Or.inl ?_) continuousOn_const` and prove the remaining obligations.

Introduce `h0`. Use `norm_det hg` as an intermediate fact. Simplify using `only [id] at h0`. Rewrite `this` using `[h0]`. Simplify using `at this`.

Use `⟨1, trivial, one_ne_zero, fun θ _ => ?_⟩` and prove the remaining obligations. Unfold `allPos`. Rewrite using `[lowK_lamDet]`. Conclude with `detPow_diag n m θ 1`. Introduce `μ v _ hv hw`.

Use `⟨0, fun a b h => absurd rfl h, ?_⟩` and prove the remaining obligations. Unfold `allPos at *`. Rewrite using `[lowK_lamDet]`. Establish `hK : ∀ θ : Fin n → ℝ, Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Formalism.REAL.Kset (fun _ : Fin n => true)`. Introduce `θ`.

Use `⟨?_, by simp [GlobalTheory.DefiniteCheck.jm_const]⟩` and prove the remaining obligations. Rewrite using `[Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Rewrite using `[Pi.star_apply, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]`.

Simplify using the standard rewrite rules. Use function extensionality and compare the values at `a`. Simplify using `only [Pi.zero_apply, Nat.cast_zero, zero_smul, Finset.sum_const_zero, Pi.sub_apply]`. Assume the negation of the conclusion as `hne`. Establish `h` using `hw (Pi.single a (Real.pi / ((m : ℝ) - μ a))) (hK _)`.

Rewrite `h` using `[detPow_diag]`. Establish `h2` using `smul_left_injective ℂ hv h`. Simplify using `only [Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2`. Establish `h3 : Complex.exp (Real.pi * Complex.I) = 1`. Establish `e : (Real.pi : ℂ) * Complex.I = (((m : ℝ) * (Real.pi / ((m : ℝ) - μ a)) : ℝ) : ℂ) * Complex.I - ((μ a * (Real.pi / ((m : ℝ) - μ a)) : ℝ) : ℂ) * Complex.I`.

Rewrite using `[← sub_mul, ← Complex.ofReal_sub, ← sub_mul, mul_div_cancel₀ _ hne]`. Rewrite using `[e, Complex.exp_sub, h2, div_self (Complex.exp_ne_zero _)]`. Rewrite `h3` using `[Complex.exp_pi_mul_I]`. Evaluate the numerical expressions using `at h3`.
-/
theorem isDS_detPow (n : ℕ) (s : Bool) (m : ℤ) : IsDS (fun _ : Fin n => s) (lamDet n m) (detPow n m) := by
  rw [GlobalTheory.RealPar.isDS_const_iff]
  refine ⟨inferInstance, inferInstance, ⟨⟨?_, fun a _ b _ => ?_⟩, fun g hg v => ?_, fun v => ?_⟩,
    inferInstance, fun _ _ _ _ => trivial, fun S _ _ => eq_bot_or_eq_top S, ?_, ?_⟩
  · ext; simp [detPow_apply]
  · ext; simp [detPow_apply, mul_zpow]
  · rw [detPow_apply, norm_mul, norm_zpow, norm_det hg]; simp
  · simp only [detPow_apply]
    refine ContinuousOn.mul (ContinuousOn.zpow₀ (continuous_id.matrix_det.continuousOn) m fun g hg => Or.inl ?_)
      continuousOn_const
    intro h0
    have := norm_det hg
    simp only [id] at h0
    rw [h0] at this
    simp at this
  · refine ⟨1, trivial, one_ne_zero, fun θ _ => ?_⟩
    unfold allPos
    rw [lowK_lamDet]
    exact detPow_diag n m θ 1
  · intro μ v _ hv hw
    refine ⟨0, fun a b h => absurd rfl h, ?_⟩
    unfold allPos at *
    rw [lowK_lamDet]
    have hK : ∀ θ : Fin n → ℝ, Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈
        Formalism.REAL.Kset (fun _ : Fin n => true) := by
      intro θ
      refine ⟨?_, by simp [GlobalTheory.DefiniteCheck.jm_const]⟩
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext a
      rw [Pi.star_apply, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
        Complex.norm_exp_ofReal_mul_I]
      simp
    funext a
    simp only [Pi.zero_apply, Nat.cast_zero, zero_smul, Finset.sum_const_zero, Pi.sub_apply]
    by_contra hne
    have h := hw (Pi.single a (Real.pi / ((m : ℝ) - μ a))) (hK _)
    rw [detPow_diag] at h
    have h2 := smul_left_injective ℂ hv h
    simp only [Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
    have h3 : Complex.exp (Real.pi * Complex.I) = 1 := by
      have e : (Real.pi : ℂ) * Complex.I = (((m : ℝ) * (Real.pi / ((m : ℝ) - μ a)) : ℝ) : ℂ) * Complex.I -
          ((μ a * (Real.pi / ((m : ℝ) - μ a)) : ℝ) : ℂ) * Complex.I := by
        rw [← sub_mul, ← Complex.ofReal_sub, ← sub_mul, mul_div_cancel₀ _ hne]
      rw [e, Complex.exp_sub, h2, div_self (Complex.exp_ne_zero _)]
    rw [Complex.exp_pi_mul_I] at h3
    norm_num at h3

/- English proof (translation)
Rewrite using `[fdeg_lamDet, mul_one]`. Use `isFdeg_of_scalar _ (1 : ℂ) (fun x => ⟨x, by simp⟩) fun g hg => ⟨g.det ^ m, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[norm_zpow, norm_det hg, _root_.one_zpow]`. Rewrite using `[detPow_apply, smul_eq_mul]`.
-/
theorem isFdeg_detPow (n : ℕ) (s : Bool) (m : ℤ) :
    IsFdeg (Formalism.REAL.muG (fun _ : Fin n => s)) (detPow n m) (cst n s * Formalism.QuantumDeterminants.fdegHC (lamDet n m)) := by
  rw [fdeg_lamDet, mul_one]
  refine isFdeg_of_scalar _ (1 : ℂ) (fun x => ⟨x, by simp⟩) fun g hg => ⟨g.det ^ m, ?_, ?_⟩
  · rw [norm_zpow, norm_det hg, _root_.one_zpow]
  · rw [detPow_apply, smul_eq_mul]

/- English proof (translation)
Take `⟨s, rfl⟩ : ∃ s, ε = fun _ => s` from `⟨ε 0, funext fun a => by rw [Subsingleton.elim a 0]⟩`. Use `⟨cst 1 s, cst_pos 1 s, fun lam _ H _ _ σ h => ?_⟩` and prove the remaining obligations. Establish `hf : Formalism.QuantumDeterminants.fdegHC lam = 1`. Simplify using `[Formalism.QuantumDeterminants.fdegHC, Finset.filter_singleton]`. Rewrite using `[hf, mul_one]`.

Establish `ht` using `GlobalTheory.DefiniteCheck.isDS_const_top h`. Take `⟨e, -, he0, hw⟩` from `ht.2.2.2.1`. Establish `hs : ∀ g ∈ UJset (fun _ : Fin 1 => s), ∃ z : ℂ, ‖z‖ = 1 ∧ σ g e = z • e`. Introduce `g hg`. Establish `h1` using `norm_det hg`.

Rewrite `h1` using `[Matrix.det_fin_one]`. Establish `h2 : g = Matrix.diagonal (fun a => Complex.exp ((((fun _ => (g 0 0).arg : Fin 1 → ℝ) a : ℝ) : ℂ) * Complex.I))`. Use extensionality with `i j`. Rewrite using `[Subsingleton.elim i 0, Subsingleton.elim j 0, Matrix.diagonal_apply_eq]`. Use `Complex.norm_mul_exp_arg_mul_I (g 0 0)` as an intermediate fact.

Rewrite `this` using `[h1]`. Simplify using `using this.symm`. Establish `h3` using `hw (fun _ => (g 0 0).arg) (by rw [← h2, GlobalTheory.DefiniteCheck.kset_const]; exact hg)`. Rewrite `h3` using `[← h2]`. Conclude with `⟨_, Complex.norm_exp_ofReal_mul_I _, h3⟩`.

Use `isFdeg_of_scalar σ e (fun x => ?_) hs` and prove the remaining obligations. Establish `hst : IsKStableOn (fun _ : Fin 1 => s) σ (ℂ ∙ e)`. Introduce `g hg v hv`. Take `⟨a, rfl⟩` from `Submodule.mem_span_singleton.1 hv`. Take `⟨z, -, hz⟩` from `hs g (by rwa [← GlobalTheory.DefiniteCheck.kset_const])`.

Rewrite using `[map_smul, hz]`. Conclude with `Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e))`. Break down `ht.2.2.1 _ le_top hst with h0 | h1` into its components or cases. Conclude with `absurd (Submodule.span_singleton_eq_bot.1 h0) he0`. Take `⟨a, ha⟩` from `Submodule.mem_span_singleton.1 (h1 ▸ Submodule.mem_top : x ∈ (ℂ ∙ e))`.

Conclude with `⟨a, ha.symm⟩`.
-/
theorem rank_one (ε : Fin 1 → Bool) : ∃ c : ℝ, 0 < c ∧
    ∀ (lam : Fin 1 → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        (σ : Matrix (Fin 1) (Fin 1) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
        IsFdeg (Formalism.REAL.muG ε) σ (c * Formalism.QuantumDeterminants.fdegHC lam) := by
  obtain ⟨s, rfl⟩ : ∃ s, ε = fun _ => s := ⟨ε 0, funext fun a => by rw [Subsingleton.elim a 0]⟩
  refine ⟨cst 1 s, cst_pos 1 s, fun lam _ H _ _ σ h => ?_⟩
  have hf : Formalism.QuantumDeterminants.fdegHC lam = 1 := by
    simp [Formalism.QuantumDeterminants.fdegHC, Finset.filter_singleton]
  rw [hf, mul_one]
  have ht := GlobalTheory.DefiniteCheck.isDS_const_top h
  obtain ⟨e, -, he0, hw⟩ := ht.2.2.2.1
  have hs : ∀ g ∈ UJset (fun _ : Fin 1 => s), ∃ z : ℂ, ‖z‖ = 1 ∧ σ g e = z • e := by
    intro g hg
    have h1 := norm_det hg
    rw [Matrix.det_fin_one] at h1
    have h2 : g = Matrix.diagonal (fun a => Complex.exp ((((fun _ => (g 0 0).arg : Fin 1 → ℝ) a : ℝ) : ℂ) * Complex.I)) := by
      ext i j
      rw [Subsingleton.elim i 0, Subsingleton.elim j 0, Matrix.diagonal_apply_eq]
      have := Complex.norm_mul_exp_arg_mul_I (g 0 0)
      rw [h1] at this
      simpa using this.symm
    have h3 := hw (fun _ => (g 0 0).arg) (by rw [← h2, GlobalTheory.DefiniteCheck.kset_const]; exact hg)
    rw [← h2] at h3
    exact ⟨_, Complex.norm_exp_ofReal_mul_I _, h3⟩
  refine isFdeg_of_scalar σ e (fun x => ?_) hs
  have hst : IsKStableOn (fun _ : Fin 1 => s) σ (ℂ ∙ e) := by
    intro g hg v hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hv
    obtain ⟨z, -, hz⟩ := hs g (by rwa [← GlobalTheory.DefiniteCheck.kset_const])
    rw [map_smul, hz]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e))
  rcases ht.2.2.1 _ le_top hst with h0 | h1
  · exact absurd (Submodule.span_singleton_eq_bot.1 h0) he0
  · obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (h1 ▸ Submodule.mem_top : x ∈ (ℂ ∙ e))
    exact ⟨a, ha.symm⟩

/- English proof (translation)
Take `⟨e, he⟩` from `exists_ne (0 : H)`. Establish `h1` using `(h.2 e e e e).2.symm.trans (h'.2 e e e e).2`. Establish `h2 : ⟪e, e⟫_ℂ ≠ 0` using `inner_self_ne_zero.2 he`. Establish `hd : (d : ℂ) ≠ 0` using `by exact_mod_cast h.1.ne'`. Establish `hd' : (d' : ℂ) ≠ 0` using `by exact_mod_cast h'.1.ne'`.

Rewrite `h1` using `[div_eq_div_iff hd hd']`. Conclude with `(mul_left_cancel₀ (mul_ne_zero h2 h2) h1).symm` after adjusting the coercions.
-/
theorem isFdeg_unique {n : ℕ} {ε : Fin n → Bool} {μ : Measure (Formalism.REAL.UJ ε)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [Nontrivial H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {d d' : ℝ}
    (h : IsFdeg μ σ d) (h' : IsFdeg μ σ d') : d = d' := by
  obtain ⟨e, he⟩ := exists_ne (0 : H)
  have h1 := (h.2 e e e e).2.symm.trans (h'.2 e e e e).2
  have h2 : ⟪e, e⟫_ℂ ≠ 0 := inner_self_ne_zero.2 he
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast h.1.ne'
  have hd' : (d' : ℂ) ≠ 0 := by exact_mod_cast h'.1.ne'
  rw [div_eq_div_iff hd hd'] at h1
  exact_mod_cast (mul_left_cancel₀ (mul_ne_zero h2 h2) h1).symm

/- English proof (translation)
Take `⟨c, -, hc⟩` from `hHC.chamber n ε`. Use `h.2.1` as an intermediate fact. Use `h'.2.1` as an intermediate fact. Rewrite using `[isFdeg_unique hd (hc lam hl H σ h), isFdeg_unique hd' (hc lam' hl' H' σ' h')]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ratio (hHC : HarishChandra) {n : ℕ} {ε : Fin n → Bool} {lam lam' : Fin n → ℝ}
    (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hl' : Formalism.QuantumDeterminants.IsHCParam lam')
    {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}
    (h : IsDS ε lam σ) (h' : IsDS ε lam' σ') {d d' : ℝ}
    (hd : IsFdeg (Formalism.REAL.muG ε) σ d) (hd' : IsFdeg (Formalism.REAL.muG ε) σ' d') :
    d * Formalism.QuantumDeterminants.fdegHC lam' = d' * Formalism.QuantumDeterminants.fdegHC lam := by
  obtain ⟨c, -, hc⟩ := hHC.chamber n ε
  have := h.2.1
  have := h'.2.1
  rw [isFdeg_unique hd (hc lam hl H σ h), isFdeg_unique hd' (hc lam' hl' H' σ' h')]
  ring

/- English proof (translation)
Take `⟨c, -, hc⟩` from `hHC n ε`. Use `h.2.1` as an intermediate fact. Use `h'.2.1` as an intermediate fact. Rewrite using `[isFdeg_unique hd (hc π lam hl H σ h), isFdeg_unique hd' (hc π' lam' hl' H' σ' h')]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ratio_chambers (hHC : HarishChandra) {n : ℕ} {ε : Fin n → Bool} {π π' : Equiv.Perm (Fin n)}
    {lam lam' : Fin n → ℝ}
    (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hl' : Formalism.QuantumDeterminants.IsHCParam lam')
    {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}
    (h : IsDS (ε ∘ π) lam (fun g => σ (g.submatrix π.symm π.symm)))
    (h' : IsDS (ε ∘ π') lam' (fun g => σ' (g.submatrix π'.symm π'.symm))) {d d' : ℝ}
    (hd : IsFdeg (Formalism.REAL.muG ε) σ d) (hd' : IsFdeg (Formalism.REAL.muG ε) σ' d') :
    d * Formalism.QuantumDeterminants.fdegHC lam' = d' * Formalism.QuantumDeterminants.fdegHC lam := by
  obtain ⟨c, -, hc⟩ := hHC n ε
  have := h.2.1
  have := h'.2.1
  rw [isFdeg_unique hd (hc π lam hl H σ h), isFdeg_unique hd' (hc π' lam' hl' H' σ' h')]
  ring

/- English proof (translation)
Establish `e : (fun g : Matrix (Fin n) (Fin n) ℂ => detPow n m (g.submatrix π.symm π.symm)) = detPow n m`. Use function extensionality and compare the values at `g`. Simplify using `only [detPow, Matrix.det_submatrix_equiv_self]`. Rewrite using `[e]`. Conclude with `isDS_detPow n s m`.
-/
theorem isDS_detPow_perm (n : ℕ) (s : Bool) (m : ℤ) (π : Equiv.Perm (Fin n)) :
    IsDS ((fun _ : Fin n => s) ∘ π) (lamDet n m) (fun g => detPow n m (g.submatrix π.symm π.symm)) := by
  have e : (fun g : Matrix (Fin n) (Fin n) ℂ => detPow n m (g.submatrix π.symm π.symm)) = detPow n m := by
    funext g
    simp only [detPow, Matrix.det_submatrix_equiv_self]
  rw [e]
  exact isDS_detPow n s m

/- English proof (translation)
Establish `h` using `isFdeg_unique (hc 1 _ (lamDet_hc n 0) ℂ _ (isDS_detPow_perm n s 0 1)) (isFdeg_detPow n s 0)`. Simplify `h` using `[fdeg_lamDet]`.
-/
theorem const_eq_cst {n : ℕ} {s : Bool} {c : ℝ}
    (hc : ∀ (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
        IsDS ((fun _ : Fin n => s) ∘ π) lam (fun g => σ (g.submatrix π.symm π.symm)) →
        IsFdeg (Formalism.REAL.muG (fun _ : Fin n => s)) σ (c * Formalism.QuantumDeterminants.fdegHC lam)) : c = cst n s := by
  have h := isFdeg_unique (hc 1 _ (lamDet_hc n 0) ℂ _ (isDS_detPow_perm n s 0 1)) (isFdeg_detPow n s 0)
  simpa [fdeg_lamDet] using h

/- English proof (translation)
Take `⟨c, hc, h1⟩` from `rank_one ε`. Use `⟨c, hc, fun π lam hl H _ _ σ hσ => h1 lam hl H σ ?_⟩` and prove the remaining obligations. Take `rfl : π = 1` from `Subsingleton.elim _ _`. Simplify `hσ` using `[Equiv.Perm.one_def]`.
-/
theorem rank_one_perm (ε : Fin 1 → Bool) : ∃ c : ℝ, 0 < c ∧
    ∀ (π : Equiv.Perm (Fin 1)) (lam : Fin 1 → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        (σ : Matrix (Fin 1) (Fin 1) ℂ → (H →L[ℂ] H)),
        IsDS (ε ∘ π) lam (fun g => σ (g.submatrix π.symm π.symm)) →
        IsFdeg (Formalism.REAL.muG ε) σ (c * Formalism.QuantumDeterminants.fdegHC lam) := by
  obtain ⟨c, hc, h1⟩ := rank_one ε
  refine ⟨c, hc, fun π lam hl H _ _ σ hσ => h1 lam hl H σ ?_⟩
  obtain rfl : π = 1 := Subsingleton.elim _ _
  simpa [Equiv.Perm.one_def] using hσ

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem diag_submatrix {n : ℕ} (π : Equiv.Perm (Fin n)) (d : Fin n → ℂ) (a : Fin n) :
    (Matrix.diagonal d).submatrix π.symm π.symm (π a) (π a) = d a := by simp

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `funext a fin_cases a <;>`. Apply the tactic sequence `simp only [Formalism.QuantumDeterminants.lowK, Pi.add_apply, Pi.sub_apply, Formalism.REAL.rhoN, Formalism.REAL.rhoC, Finset.card_filter, Fin.sum_univ_two] <;> simp <;> norm_num`. Apply the tactic sequence `funext a fin_cases a <;>`. Apply the tactic sequence `simp only [Formalism.QuantumDeterminants.lowK, Pi.add_apply, Pi.sub_apply, Formalism.REAL.rhoN, Formalism.REAL.rhoC, Finset.card_filter, Fin.sum_univ_two] <;> simp <;> norm_num`.

Simplify using `[Formalism.QuantumDeterminants.fdegHC, Finset.prod_filter, Fin.prod_univ_two]`. Rewrite using `[abs_of_nonneg (by linarith)]; ring`.
-/
theorem unitary_one_one_chambers (k : ℝ) (hk : 1 ≤ k) :
    Formalism.QuantumDeterminants.lowK (![true, false] ∘ (1 : Equiv.Perm (Fin 2))) ![k - 1 / 2, 1 / 2] = ![k, 0] ∧
    Formalism.QuantumDeterminants.lowK (![true, false] ∘ (Equiv.swap (0 : Fin 2) 1)) ![k - 1 / 2, 1 / 2] = ![k, 0] ∧
    Formalism.QuantumDeterminants.fdegHC ![k - 1 / 2, 1 / 2] = k - 1 := by
  refine ⟨?_, ?_, ?_⟩
  · funext a
    fin_cases a <;>
      simp only [Formalism.QuantumDeterminants.lowK, Pi.add_apply, Pi.sub_apply, Formalism.REAL.rhoN, Formalism.REAL.rhoC, Finset.card_filter,
        Fin.sum_univ_two] <;> simp <;> norm_num
  · funext a
    fin_cases a <;>
      simp only [Formalism.QuantumDeterminants.lowK, Pi.add_apply, Pi.sub_apply, Formalism.REAL.rhoN, Formalism.REAL.rhoC, Finset.card_filter,
        Fin.sum_univ_two] <;> simp <;> norm_num
  · simp [Formalism.QuantumDeterminants.fdegHC, Finset.prod_filter, Fin.prod_univ_two]
    rw [abs_of_nonneg (by linarith)]; ring

/- English proof (translation)
Establish `h1` using `Finset.card_filter_add_card_filter_not (s := Finset.univ.filter fun b : Fin n => a < b) (fun b => ε b = ε a)`. Establish `h2` using `Finset.card_filter_add_card_filter_not (s := Finset.univ.filter fun b : Fin n => b < a) (fun b => ε b = ε a)`. Rewrite `h1`, `h2` using `[Finset.filter_filter, Finset.filter_filter]`. Rewrite using `[← h1, ← h2]`. Simplify using `only [Formalism.QuantumDeterminants.lowK, Formalism.REAL.rhoN, Formalism.REAL.rhoC, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ne_eq]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lowK_add_two_rhoC {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) (a : Fin n) :
    (Formalism.QuantumDeterminants.lowK ε lam + (2 : ℝ) • Formalism.REAL.rhoC ε) a =
      lam a + (((Finset.univ.filter fun b => a < b).card : ℝ) - (Finset.univ.filter fun b => b < a).card) / 2 := by
  have h1 := Finset.card_filter_add_card_filter_not (s := Finset.univ.filter fun b : Fin n => a < b)
    (fun b => ε b = ε a)
  have h2 := Finset.card_filter_add_card_filter_not (s := Finset.univ.filter fun b : Fin n => b < a)
    (fun b => ε b = ε a)
  rw [Finset.filter_filter, Finset.filter_filter] at h1 h2
  rw [← h1, ← h2]
  simp only [Formalism.QuantumDeterminants.lowK, Formalism.REAL.rhoN, Formalism.REAL.rhoC, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, ne_eq]
  push_cast
  ring

end GlobalTheory.FormalDegree.Model
