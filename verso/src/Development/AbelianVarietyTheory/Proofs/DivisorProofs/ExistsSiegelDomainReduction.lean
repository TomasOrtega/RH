import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorusUOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusElementUnitaryMatrixIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusElementArchimedeanMatrixFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSetArchimedeanNormBoundStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay

noncomputable section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

namespace GlobalTheory.SiegelHt

/- English proof (translation)
Take `⟨hpos, hstep, hlast⟩` from `ht`. Establish `hm0 : 0 < min 1 c` using `lt_min one_pos hc`. Establish `hm1 : min 1 c ≤ 1` using `min_le_left _ _`. Establish `key : ∀ k : ℕ, ∀ i : Fin r, i.val + k + 1 = r → min 1 c ^ (k + 1) ≤ t i`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero`. Introduce `i hi`. Simplify using `only [zero_add, pow_one]`. Conclude with `(min_le_right _ _).trans (hlast i (by omega))`.

Consider the case `succ k ih`. Introduce `i hi`. Establish `hj : i.val + 1 < r` using `by omega`. Establish `h1` using `ih ⟨i.val + 1, hj⟩ (by simp; omega)`. Establish `h2` using `hstep i ⟨i.val + 1, hj⟩ rfl`.

Establish `h3 : 0 < t ⟨i.val + 1, hj⟩` using `hpos _`. Combine the equalities or inequalities in the displayed calculation. Use `key (r - i.val - 1) i (by omega)` as an intermediate fact. Use `le_trans ?_ this` and prove the remaining obligations. Conclude with `pow_le_pow_of_le_one hm0.le hm1 (by omega)`.
-/
theorem cone_low {r : ℕ} {c : ℝ} (hc : 0 < c) {t : Fin r → ℝ}
    (ht : t ∈ GlobalTheory.SiegelSet.cone r c) (i : Fin r) : min 1 c ^ r ≤ t i := by
  obtain ⟨hpos, hstep, hlast⟩ := ht
  have hm0 : 0 < min 1 c := lt_min one_pos hc
  have hm1 : min 1 c ≤ 1 := min_le_left _ _
  have key : ∀ k : ℕ, ∀ i : Fin r, i.val + k + 1 = r → min 1 c ^ (k + 1) ≤ t i := by
    intro k
    induction k with
    | zero =>
      intro i hi
      simp only [zero_add, pow_one]
      exact (min_le_right _ _).trans (hlast i (by omega))
    | succ k ih =>
      intro i hi
      have hj : i.val + 1 < r := by omega
      have h1 := ih ⟨i.val + 1, hj⟩ (by simp; omega)
      have h2 := hstep i ⟨i.val + 1, hj⟩ rfl
      have h3 : 0 < t ⟨i.val + 1, hj⟩ := hpos _
      calc min 1 c ^ (k + 1 + 1) = min 1 c * min 1 c ^ (k + 1) := by ring
        _ ≤ min 1 c * t ⟨i.val + 1, hj⟩ := mul_le_mul_of_nonneg_left h1 hm0.le
        _ ≤ c * t ⟨i.val + 1, hj⟩ := mul_le_mul_of_nonneg_right (min_le_right _ _) h3.le
        _ ≤ t i := h2
  have := key (r - i.val - 1) i (by omega)
  refine le_trans ?_ this
  exact pow_le_pow_of_le_one hm0.le hm1 (by omega)

/- English proof (translation)
Take `⟨rfl, A, hA⟩` from `h`. Set `A' : Matrix (Fin (r + s)) (Fin (r + s)) ℂ` to `A.submatrix id finSumFinEquiv.symm`. Establish `e : A'ᵀ * M * A'.map star = (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) _ ℂ).submatrix finSumFinEquiv.symm finSumFinEquiv.symm`. Rewrite using `[← hA]`. Both sides reduce to the same expression.

Introduce `h0`. Establish `e2` using `congrArg Matrix.det e`. Rewrite `e2` using `[Matrix.det_mul, Matrix.det_mul, h0, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]`. Simplify using `at e2`. Conclude with `absurd e2.symm (by simp)`.
-/
theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨rfl, A, hA⟩ := h
  let A' : Matrix (Fin (r + s)) (Fin (r + s)) ℂ := A.submatrix id finSumFinEquiv.symm
  have e : A'ᵀ * M * A'.map star =
      (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) _ ℂ).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← hA]; rfl
  intro h0
  have e2 := congrArg Matrix.det e
  rw [Matrix.det_mul, Matrix.det_mul, h0, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_neg] at e2
  simp at e2
  exact absurd e2.symm (by simp)

/- English proof (translation)
Simplify using `only [form, one_smul, Matrix.mul_apply, dotProduct, Matrix.mulVec, map_sum, map_mul, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, RingHom.coe_coe, hσ, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem form_cols {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n q : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (U V : Matrix (Fin n) (Fin q) E) (i j : Fin q) :
    form σ J (fun k => U k i) (fun k => V k j) =
      σ ((Formalism.UG.cT (σ : E →+* E) U * ((1 : E) • J.map σ) * V) i j) := by
  simp only [form, one_smul, Matrix.mul_apply, dotProduct, Matrix.mulVec, map_sum, map_mul, Formalism.UG.cT,
    Matrix.transpose_apply, Matrix.map_apply, RingHom.coe_coe, hσ, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.SiegelHt

open GlobalTheory.SiegelHt in
/- English proof (translation)
Introduce `hP F E _ _ _ _ _ σ B n X r s hB hX`. Establish `hcm` using `hB.cm`. Establish `hσ` using `GlobalTheory.SiegelSet.sigma_sigma hcm`. Take `⟨w₀⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Establish `hd : X.J.det ≠ 0` using `fun h0 => det_ne_zero_of_hasSig (hX.sig w₀) (by`.

Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero])`. Establish `hJ' : IsHermND σ ((1 : E) • X.J.map σ)`. Rewrite using `[one_smul]`. Use `⟨fun i j => congrArg σ (hX.herm i j), ?_⟩` and prove the remaining obligations. Establish `e : (X.J.map σ).det = σ X.J.det` using `((σ : E →+* E).map_det _).symm`.

Rewrite using `[e]`. Conclude with `(map_ne_zero σ).2 hd`. Set `e : UA σ X.J ≃* GAd σ ((1 : E) • X.J.map σ)` to `MulEquiv.subgroupCongr (GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := X.J) hσ (one_ne_zero : (1 : E) ≠ 0))`. Establish `he' : Continuous e.symm` using `continuous_subtype_val.subtype_mk _`. Take `⟨q, Xf, Yf, hW⟩` from `GlobalTheory.SiegelSet.exists_isWittFrame hcm hJ'`.

Take `⟨K, Ω, c, hK, hΩ, -, hc, -, -, hcov, ⟨C₀, hC₀, hconj⟩, -⟩` from `hP F E σ hcm n _ hJ' q Xf Yf hW`. Establish `hc'0 : 0 < min 1 c ^ q` using `pow_pos (lt_min one_pos hc) _`. Take `⟨Ch, Ah, hh0⟩` from `GlobalTheory.T.siegel_set_archimedean_norm_bound F E σ hcm n _ q Xf Yf _ hc'0`. Establish `hh : ∀ t : Fin q → ℝ, (∀ i, min 1 c ^ q ≤ t i) → ∀ a, GlobalTheory.SiegelSet.IsTorusElt σ _ Xf Yf t a → (height σ _ a : ℝ) ≤ Ch * (1 + ∏ i, t i) ^ Ah` using `fun t ht a ha => hh0 t ht a ha.1 (GlobalTheory.T.torus_element_archimedean_matrix_form F E σ hcm n _ hJ' q Xf Yf hW t (fun i => hc'0.trans_le (ht i)) a ha)`. Set `mul2 : GAd σ ((1 : E) • X.J.map σ) × GAd σ ((1 : E) • X.J.map σ) → GAd σ ((1 : E) • X.J.map σ)` to `fun p => p.1 * p.2`.

Establish `hCK : IsCompact (mul2 '' (C₀ ×ˢ (K : Set (GAd σ ((1 : E) • X.J.map σ)))))` using `(hC₀.prod hK).image continuous_mul`. Establish `hhc : Continuous fun g : GAd σ ((1 : E) • X.J.map σ) => (height σ ((1 : E) • X.J.map σ) g : ℝ)` using `NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL F).comp continuous_subtype_val)`. Take `⟨Bd, hBd⟩` from `(hCK.image hhc).bddAbove`. Establish `hfr : IsFrameU σ X.J (fun i k => Xf k i) (fun i k => Yf k i)`. Use `⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations.

Rewrite using `[form_cols hσ, hW.xx]`. Simplify using the standard rewrite rules. Rewrite using `[form_cols hσ, hW.yy]`. Simplify using the standard rewrite rules. Apply the tactic sequence `rw [form_cols hσ, hW.xy, Matrix.one_apply]; split_ifs <;> simp`.

Use `⟨q, fun i k => Xf k i, fun i k => Yf k i, hfr, e.symm '' (mul2 '' (C₀ ×ˢ (K : Set _))), min 1 c ^ q, Ch * max Bd 0, Ah, hCK.image he', hc'0, fun g => ?_⟩` and prove the remaining obligations. Take `⟨γ, hγ, s', ⟨p, hp, t, htc, a, ha, k, hk, rfl⟩, hgs⟩` from `hcov (e g)`. Take `⟨u, -, hu⟩` from `Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)`. Establish `hr : e.symm γ ∈ ratU σ X.J` using `Subgroup.mem_subgroupOf.2 ⟨u, hu⟩`. Establish `hmem : a⁻¹ * p * a * k ∈ mul2 '' (C₀ ×ˢ (K : Set _))` using `⟨(a⁻¹ * p * a, k), ⟨hconj p hp t htc a ha, hk⟩, rfl⟩`.

Use `⟨(e.symm γ)⁻¹, inv_mem hr, t, e.symm a, e.symm (a⁻¹ * p * a * k), cone_low hc htc, GlobalTheory.T.torus_element_unitary_matrix_identity F E σ hcm n X.J hX.herm q Xf Yf t a ha _ rfl, ⟨_, hmem, rfl⟩, ?_, ?_⟩` and prove the remaining obligations. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, hgs]`. Use `group`. Establish `h1 : (ht (e.symm a * e.symm (a⁻¹ * p * a * k)) : ℝ) ≤ (height σ _ a : ℝ) * (height σ _ (a⁻¹ * p * a * k) : ℝ)`.

Conclude with `heightGL_mul_le F (e.symm a).1 (e.symm (a⁻¹ * p * a * k)).1` after adjusting the coercions. Establish `h2` using `hh t (cone_low hc htc) a ha`. Establish `h3 : (height σ _ (a⁻¹ * p * a * k) : ℝ) ≤ max Bd 0` using `(hBd ⟨_, hmem, rfl⟩).trans (le_max_left _ _)`. Establish `h4 : (0 : ℝ) ≤ height σ _ a` using `NNReal.coe_nonneg _`. Establish `h5 : (0 : ℝ) ≤ height σ _ (a⁻¹ * p * a * k)` using `NNReal.coe_nonneg _`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem GlobalTheory.SiegelHt.siegel_reduction : GlobalTheory.Published.SiegelSetUnitary → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    ∃ (q : ℕ) (x y : Fin q → Fin n → E), IsFrameU σ X.J x y ∧ ∃ (Cc : Set (UA σ X.J)) (c C : ℝ) (A : ℕ),
      IsCompact Cc ∧ 0 < c ∧ ∀ g : UA σ X.J, ∃ γ ∈ ratU σ X.J, ∃ (t : Fin q → ℝ) (a κ : UA σ X.J),
        (∀ i, c ≤ t i) ∧ IsTorusU x y t a ∧ κ ∈ Cc ∧ γ * g = a * κ ∧ (ht (a * κ) : ℝ) ≤ C * (1 + ∏ i, t i) ^ A := by
  intro hP F E _ _ _ _ _ σ B n X r s hB hX
  have hcm := hB.cm
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hcm
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hd : X.J.det ≠ 0 := fun h0 => det_ne_zero_of_hasSig (hX.sig w₀) (by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero])
  have hJ' : IsHermND σ ((1 : E) • X.J.map σ) := by
    rw [one_smul]
    refine ⟨fun i j => congrArg σ (hX.herm i j), ?_⟩
    have e : (X.J.map σ).det = σ X.J.det := ((σ : E →+* E).map_det _).symm
    rw [e]
    exact (map_ne_zero σ).2 hd
  let e : UA σ X.J ≃* GAd σ ((1 : E) • X.J.map σ) :=
    MulEquiv.subgroupCongr (GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := X.J) hσ (one_ne_zero : (1 : E) ≠ 0))
  have he' : Continuous e.symm := continuous_subtype_val.subtype_mk _
  obtain ⟨q, Xf, Yf, hW⟩ := GlobalTheory.SiegelSet.exists_isWittFrame hcm hJ'
  obtain ⟨K, Ω, c, hK, hΩ, -, hc, -, -, hcov, ⟨C₀, hC₀, hconj⟩, -⟩ := hP F E σ hcm n _ hJ' q Xf Yf hW
  have hc'0 : 0 < min 1 c ^ q := pow_pos (lt_min one_pos hc) _
  obtain ⟨Ch, Ah, hh0⟩ := GlobalTheory.T.siegel_set_archimedean_norm_bound F E σ hcm n _ q Xf Yf _ hc'0
  have hh : ∀ t : Fin q → ℝ, (∀ i, min 1 c ^ q ≤ t i) → ∀ a, GlobalTheory.SiegelSet.IsTorusElt σ _ Xf Yf t a →
      (height σ _ a : ℝ) ≤ Ch * (1 + ∏ i, t i) ^ Ah := fun t ht a ha =>
    hh0 t ht a ha.1 (GlobalTheory.T.torus_element_archimedean_matrix_form F E σ hcm n _ hJ' q Xf Yf hW t (fun i => hc'0.trans_le (ht i)) a ha)
  let mul2 : GAd σ ((1 : E) • X.J.map σ) × GAd σ ((1 : E) • X.J.map σ) → GAd σ ((1 : E) • X.J.map σ) :=
    fun p => p.1 * p.2
  have hCK : IsCompact (mul2 '' (C₀ ×ˢ (K : Set (GAd σ ((1 : E) • X.J.map σ))))) :=
    (hC₀.prod hK).image continuous_mul
  have hhc : Continuous fun g : GAd σ ((1 : E) • X.J.map σ) => (height σ ((1 : E) • X.J.map σ) g : ℝ) :=
    NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL F).comp continuous_subtype_val)
  obtain ⟨Bd, hBd⟩ := (hCK.image hhc).bddAbove
  have hfr : IsFrameU σ X.J (fun i k => Xf k i) (fun i k => Yf k i) := by
    refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
    · rw [form_cols hσ, hW.xx]; simp
    · rw [form_cols hσ, hW.yy]; simp
    · rw [form_cols hσ, hW.xy, Matrix.one_apply]; split_ifs <;> simp
  refine ⟨q, fun i k => Xf k i, fun i k => Yf k i, hfr, e.symm '' (mul2 '' (C₀ ×ˢ (K : Set _))), min 1 c ^ q,
    Ch * max Bd 0, Ah, hCK.image he', hc'0, fun g => ?_⟩
  obtain ⟨γ, hγ, s', ⟨p, hp, t, htc, a, ha, k, hk, rfl⟩, hgs⟩ := hcov (e g)
  obtain ⟨u, -, hu⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)
  have hr : e.symm γ ∈ ratU σ X.J := Subgroup.mem_subgroupOf.2 ⟨u, hu⟩
  have hmem : a⁻¹ * p * a * k ∈ mul2 '' (C₀ ×ˢ (K : Set _)) := ⟨(a⁻¹ * p * a, k), ⟨hconj p hp t htc a ha, hk⟩, rfl⟩
  refine ⟨(e.symm γ)⁻¹, inv_mem hr, t, e.symm a, e.symm (a⁻¹ * p * a * k), cone_low hc htc,
    GlobalTheory.T.torus_element_unitary_matrix_identity F E σ hcm n X.J hX.herm q Xf Yf t a ha _ rfl, ⟨_, hmem, rfl⟩, ?_, ?_⟩
  · apply e.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, hgs]
    group
  · have h1 : (ht (e.symm a * e.symm (a⁻¹ * p * a * k)) : ℝ) ≤
        (height σ _ a : ℝ) * (height σ _ (a⁻¹ * p * a * k) : ℝ) := by
      exact_mod_cast heightGL_mul_le F (e.symm a).1 (e.symm (a⁻¹ * p * a * k)).1
    have h2 := hh t (cone_low hc htc) a ha
    have h3 : (height σ _ (a⁻¹ * p * a * k) : ℝ) ≤ max Bd 0 :=
      (hBd ⟨_, hmem, rfl⟩).trans (le_max_left _ _)
    have h4 : (0 : ℝ) ≤ height σ _ a := NNReal.coe_nonneg _
    have h5 : (0 : ℝ) ≤ height σ _ (a⁻¹ * p * a * k) := NNReal.coe_nonneg _
    calc (ht (e.symm a * e.symm (a⁻¹ * p * a * k)) : ℝ) ≤ _ := h1
      _ ≤ (Ch * (1 + ∏ i, t i) ^ Ah) * max Bd 0 := mul_le_mul h2 h3 h5 (h4.trans h2)
      _ = Ch * max Bd 0 * (1 + ∏ i, t i) ^ Ah := by ring

end
