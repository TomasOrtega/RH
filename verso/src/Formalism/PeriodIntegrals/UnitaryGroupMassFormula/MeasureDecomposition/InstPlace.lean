import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstDefs

noncomputable section

open Matrix

namespace PI.ScMuExists.UnitaryGroupMassFormula

/- English proof (translation)
Use `⟨Unitary.star_mem hg.1, ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg star hg.2`. Simplify using `only [star_mul, Matrix.star_eq_conjTranspose, Formalism.REAL.Jm_conjTranspose] at h`. Simplify `h.symm` using `[Matrix.star_eq_conjTranspose]`.
-/
theorem inst_Kset_star {n : ℕ} (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) :
    star g ∈ Formalism.REAL.Kset ε := by
  refine ⟨Unitary.star_mem hg.1, ?_⟩
  have h := congrArg star hg.2
  simp only [star_mul, Matrix.star_eq_conjTranspose, Formalism.REAL.Jm_conjTranspose] at h
  simpa [Matrix.star_eq_conjTranspose] using h.symm

/- English proof (translation)
Use function extensionality and compare the values at `r`. Simplify using `only [Formalism.REAL.Jm, Matrix.mulVec_diagonal, Pi.smul_apply, Pi.single_apply, smul_eq_mul]`. Distinguish the cases in `h : r = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[h]`.
-/
theorem inst_Jm_single {n : ℕ} (ε : Fin n → Bool) (i : Fin n) :
    Formalism.REAL.Jm ε *ᵥ Pi.single i 1 = (if ε i then (1 : ℂ) else -1) • Pi.single i 1 := by
  funext r
  simp only [Formalism.REAL.Jm, Matrix.mulVec_diagonal, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  by_cases h : r = i
  · subst h; simp
  · simp [h]

/- English proof (translation)
Establish `hc' : c = ∑ i ∈ T, c i • Pi.single i (1 : ℂ)`. Use function extensionality and compare the values at `r`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]`. Rewrite using `[Finset.sum_ite_eq]`. Use `split_ifs with h`.

Both sides reduce to the same expression. Conclude with `hc r h`. Rewrite using `[hc', Matrix.mulVec_sum]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_smul, hm i hi]`.
-/
theorem inst_fix_sum {n : ℕ} (m : Matrix (Fin n) (Fin n) ℂ) (T : Finset (Fin n))
    (hm : ∀ i ∈ T, m *ᵥ Pi.single i 1 = Pi.single i 1) (c : Fin n → ℂ) (hc : ∀ i ∉ T, c i = 0) :
    m *ᵥ c = c := by
  have hc' : c = ∑ i ∈ T, c i • Pi.single i (1 : ℂ) := by
    funext r
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · exact hc r h
  rw [hc', Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Matrix.mulVec_smul, hm i hi]

/- English proof (translation)
Use `congrFun hm r` as an intermediate fact. Simplify `this` using `[Matrix.mulVec_single_one, Pi.single_apply]`.
-/
theorem inst_col_entry {n : ℕ} (m : Matrix (Fin n) (Fin n) ℂ) (i : Fin n)
    (hm : m *ᵥ Pi.single i 1 = Pi.single i 1) (r : Fin n) : m r i = if r = i then 1 else 0 := by
  have := congrFun hm r
  simpa [Matrix.mulVec_single_one, Pi.single_apply] using this

/- English proof (translation)
Introduce `n ε ι _ _ B hBG g hg hgB`. Take `⟨A, ε', T, hA, hT1, hT2⟩` from `hAB n ε ι B hBG`. Establish `hJ'J' : Formalism.REAL.Jm ε' * Formalism.REAL.Jm ε' = 1` using `Formalism.REAL.Jm_mul_self ε'`. Establish `hAdet : IsUnit A.det`. Establish `h1 : IsUnit (Aᴴ * Formalism.REAL.Jm ε * A).det`.

Rewrite using `[hA]`. Conclude with `(Matrix.isUnit_iff_isUnit_det _).mp ⟨⟨_, _, hJ'J', hJ'J'⟩, rfl⟩`. Rewrite `h1` using `[Matrix.det_mul]`. Conclude with `isUnit_of_mul_isUnit_right h1`. Take `⟨Ai, hAi⟩ : ∃ Ai, Ai = A⁻¹` from `⟨_, rfl⟩`.

Establish `hAAi : A * Ai = 1` using `by rw [hAi]; exact Matrix.mul_nonsing_inv A hAdet`. Establish `hAiA : Ai * A = 1` using `by rw [hAi]; exact Matrix.nonsing_inv_mul A hAdet`. Establish `hAiJ : Aiᴴ * Formalism.REAL.Jm ε' * Ai = Formalism.REAL.Jm ε`. Rewrite using `[← hA]`. Establish `h2 : Aiᴴ * Aᴴ = 1` using `by rw [← Matrix.conjTranspose_mul, hAAi, Matrix.conjTranspose_one]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Formalism.REAL.Jm ε := by rw [h2, hAAi, Matrix.one_mul, Matrix.mul_one]`. Establish `tr1 : ∀ m, Formalism.REAL.inUJ ε m → Formalism.REAL.inUJ ε' (Ai * m * A)`. Introduce `m hm`.

Unfold `Formalism.REAL.inUJ at *`. Establish `: (Ai * m * A)ᴴ * Formalism.REAL.Jm ε' * (Ai * m * A) = Aᴴ * (mᴴ * (Aiᴴ * Formalism.REAL.Jm ε' * Ai) * m) * A`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Rewrite using `[this, hAiJ, hm, hA]`. Establish `tr2 : ∀ m, Formalism.REAL.inUJ ε' m → Formalism.REAL.inUJ ε (A * m * Ai)`.

Introduce `m hm`. Unfold `Formalism.REAL.inUJ at *`. Establish `: (A * m * Ai)ᴴ * Formalism.REAL.Jm ε * (A * m * Ai) = Aiᴴ * (mᴴ * (Aᴴ * Formalism.REAL.Jm ε * A) * m) * Ai`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Rewrite using `[this, hA, hm, hAiJ]`.

Establish `back : ∀ m, (∀ i ∈ T, m *ᵥ Pi.single i 1 = Pi.single i 1) → A * m * Ai * B = B`. Introduce `m hm`. Use `Matrix.ext_of_mulVec_single fun j => ?_` and prove the remaining obligations. Take `⟨c, hc0, hc⟩` from `hT2 j`. Simplify using `only [← Matrix.mulVec_mulVec]`.

Rewrite using `[hc, Matrix.mulVec_mulVec c Ai A, hAiA, Matrix.one_mulVec, inst_fix_sum m T hm c hc0]`. Take `⟨g', hg'def⟩ : ∃ g', g' = Ai * g * A` from `⟨_, rfl⟩`. Establish `hg' : Formalism.REAL.inUJ ε' g'` using `hg'def ▸ tr1 g hg`. Establish `hg'fix : ∀ i ∈ T, g' *ᵥ Pi.single i 1 = Pi.single i 1`. Introduce `i hi`.

Take `⟨c, hc⟩` from `hT1 i hi`. Rewrite using `[hg'def, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_mulVec c g B, hgB, ← hc, Matrix.mulVec_mulVec, hAiA, Matrix.one_mulVec]`. Take `⟨k', X', hk', hX', hgkX⟩` from `(Formalism.REAL.polar n ε').1 g' hg'`. Establish `hXc` using `((Formalism.REAL.pChar n ε' X').1.mp hX')`. Establish `hXh : X'.IsHermitian` using `hXc.1`.

Take `⟨p', hp'def⟩ : ∃ p', p' = NormedSpace.exp X'` from `⟨_, rfl⟩`. Rewrite `hgkX` using `[← hp'def]`. Establish `hk'u : star k' * k' = 1` using `Matrix.mem_unitaryGroup_iff'.mp hk'.1`. Establish `hk'u2 : k' * star k' = 1` using `Matrix.mem_unitaryGroup_iff.mp hk'.1`. Establish `hp'H : p'ᴴ = p'` using `by rw [hp'def]; exact hXh.exp`.

Establish `hgg : g'ᴴ * g' = NormedSpace.exp (X' + X')`. Rewrite using `[Matrix.exp_add_of_commute X' X' (Commute.refl X'), ← hp'def, hgkX, Matrix.conjTranspose_mul, hp'H, ← Matrix.star_eq_conjTranspose]`. Combine the equalities or inequalities in the displayed calculation. Establish `hgHfix : ∀ i ∈ T, g'ᴴ *ᵥ Pi.single i 1 = Pi.single i 1`. Introduce `i hi`.

Establish `h1` using `congrArg (fun M => M *ᵥ Pi.single i (1 : ℂ)) hg'`. Simplify using `only [← Matrix.mulVec_mulVec, hg'fix i hi, inst_Jm_single, Matrix.mulVec_smul] at h1`. Apply the tactic sequence `have hs : (if ε' i then (1 : ℂ) else -1) ≠ 0 := by split_ifs <;> norm_num`. Conclude with `smul_right_injective _ hs h1`. Establish `hXfix : ∀ i ∈ T, X' *ᵥ Pi.single i 1 = 0`.

Introduce `i hi`. Establish `h2 : NormedSpace.exp (X' + X') *ᵥ Pi.single i 1 = Pi.single i 1`. Rewrite using `[← hgg, ← Matrix.mulVec_mulVec, hg'fix i hi, hgHfix i hi]`. Establish `h3` using `(hE n (X' + X') (hXh.add hXh) _).mp h2`. Establish `h4 : (2 : ℂ) • (X' *ᵥ Pi.single i 1) = 0` using `by rw [two_smul, ← Matrix.add_mulVec]; exact h3`.

Conclude with `(smul_eq_zero.mp h4).resolve_left two_ne_zero`. Establish `hpfix : ∀ i ∈ T, p' *ᵥ Pi.single i 1 = Pi.single i 1` using `fun i hi => by`. Rewrite using `[hp'def]`. Conclude with `(hE n X' hXh _).mpr (hXfix i hi)`. Establish `hkfix : ∀ i ∈ T, k' *ᵥ Pi.single i 1 = Pi.single i 1`.

Introduce `i hi`. Establish `h1` using `hg'fix i hi`. Rewrite `h1` using `[hgkX, ← Matrix.mulVec_mulVec, hpfix i hi]`. Conclude with `h1`. Take `⟨σ', hσdef⟩ : ∃ σ' : Matrix (Fin n) (Fin n) ℂ, σ' = Matrix.diagonal fun i => if i ∈ T then (1 : ℂ) else (if ε' i then 1 else -1)` from `⟨_, rfl⟩`.

Establish `hσσ' : σ' * σ' = 1`. Rewrite using `[hσdef, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Apply the tactic sequence `congr 1; funext i; split_ifs <;> norm_num`. Establish `hσ'UJ : Formalism.REAL.inUJ ε' σ'`. Unfold `Formalism.REAL.inUJ Formalism.REAL.Jm`.

Rewrite using `[hσdef, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]`. Apply the tactic sequence `congr 1; funext i; simp only [Pi.star_apply]; split_ifs <;> simp`. Establish `hσfix : ∀ i ∈ T, σ' *ᵥ Pi.single i 1 = Pi.single i 1`. Introduce `i hi`. Use function extensionality and compare the values at `r`.

Rewrite using `[hσdef, Matrix.mulVec_diagonal]`. Distinguish the cases in `hr : r = i`. Substitute `hr` using the available equality. Simplify using `[hi]`. Simplify using `[Pi.single_apply, hr]`.

Apply the tactic sequence `have hcol : ∀ i ∈ T, ∀ r, p' r i = if r = i then 1 else 0 := fun i hi r => inst_col_entry p' i (hpfix i hi) r`. Establish `hrow : ∀ i ∈ T, ∀ r, p' i r = if r = i then 1 else 0`. Introduce `i hi r`. Establish `h1 : p' i r = star (p' r i)` using `by conv_lhs => rw [← hp'H]`. Both sides reduce to the same expression.

Rewrite using `[h1, hcol i hi r]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hkey : σ' * p' * σ' = Formalism.REAL.Jm ε' * p' * Formalism.REAL.Jm ε'`. Use extensionality with `r c`. Simplify using `only [hσdef, Formalism.REAL.Jm, Matrix.diagonal_mul, Matrix.mul_diagonal]`.

Distinguish the cases in `hr : r ∈ T`. Rewrite using `[hrow r hr c]`. Distinguish the cases in `hrc : c = r`. Apply the tactic sequence `subst hrc; simp only [hr, if_true]; split_ifs <;> norm_num`. Simplify using `[hrc]`.

Distinguish the cases in `hc : c ∈ T`. Rewrite using `[hcol c hc r]`. Distinguish the cases in `hrc : r = c`. Substitute `hrc` using the available equality. Conclude with `absurd hc hr`.

Simplify using `[hrc]`. Simplify using `[hr, hc]`. Establish `hJinv : (Formalism.REAL.Jm ε')⁻¹ = Formalism.REAL.Jm ε'` using `Matrix.inv_eq_left_inv hJ'J'`. Establish `hJX : Formalism.REAL.Jm ε' * X' * Formalism.REAL.Jm ε' = -X'` using `((Formalism.REAL.pChar n ε' X').2 hX')`. Establish `hJp : Formalism.REAL.Jm ε' * p' * Formalism.REAL.Jm ε' = NormedSpace.exp (-X')`.

Use `Matrix.exp_conj (Formalism.REAL.Jm ε') X' ⟨⟨_, _, hJ'J', hJ'J'⟩, rfl⟩` as an intermediate fact. Rewrite `this` using `[hJinv, hJX]`. Rewrite using `[hp'def, this]`. Establish `hσp' : σ' * p' * σ' * p' = 1`. Rewrite using `[hkey, hJp, hp'def, ← Matrix.exp_add_of_commute _ _ (Commute.refl X').neg_left, neg_add_cancel, NormedSpace.exp_zero]`.

Establish `hk'UJ : Formalism.REAL.inUJ ε' k'` using `(Formalism.REAL.kFacts n ε').1 k' hk'`. Establish `hp'UJ : Formalism.REAL.inUJ ε' p'`. Use `Formalism.REAL.expUJ n ε' X' hX'.1 1` as an intermediate fact. Simplify `this` using `[hp'def]`. Use `⟨A * k' * Ai, A * p' * Ai, A * σ' * Ai, tr2 _ hk'UJ, tr2 _ hp'UJ, tr2 _ hσ'UJ, back _ hkfix, back _ hpfix, back _ hσfix, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `: g = A * g' * Ai`. Rewrite using `[hg'def]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[this, hgkX]`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[← Matrix.mul_assoc Ai A, hAiA, Matrix.one_mul]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc Ai A, hAiA, Matrix.one_mul, ← Matrix.mul_assoc σ' σ', hσσ', Matrix.one_mul, hAAi]`. Establish `: A * σ' * Ai * (A * p' * Ai) * (A * σ' * Ai) * (A * p' * Ai) = A * (σ' * p' * σ' * p') * Ai`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[← Matrix.mul_assoc Ai A, hAiA, Matrix.one_mul, ← Matrix.mul_assoc Ai A, hAiA, Matrix.one_mul, ← Matrix.mul_assoc Ai A, hAiA, Matrix.one_mul]`. Rewrite using `[this, hσp', Matrix.mul_one, hAAi]`. Use `set R : ℝ := (n : ℝ) + 1 with hR`. Establish `hemb` using `(Formalism.REAL.uJEmb n ε).1`. Use `⟨{x : Formalism.REAL.UJ ε | Formalism.REAL.hs (Ai * Formalism.MainNotions.S.uMat x * A) ≤ R}, ?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `hcomp : IsCompact ((fun m => A * m * Ai) '' {m | Formalism.REAL.inUJ ε' m ∧ Formalism.REAL.hs m ≤ R})` using `((Formalism.REAL.hSBall n ε').1 R).image ((continuous_const.mul continuous_id).mul continuous_const)`. Establish `hset : {x : Formalism.REAL.UJ ε | Formalism.REAL.hs (Ai * Formalism.MainNotions.S.uMat x * A) ≤ R} = (fun g : Formalism.REAL.UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) ⁻¹' ((fun m => A * m * Ai) '' {m | Formalism.REAL.inUJ ε' m ∧ Formalism.REAL.hs m ≤ …`. Use extensionality with `x`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_image]`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Use `⟨Ai * Formalism.MainNotions.S.uMat x * A, ⟨tr1 _ x.2, hx⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[hAAi, Matrix.mul_one, ← Matrix.mul_assoc, hAAi, Matrix.one_mul]`. Introduce and unpack `⟨m, ⟨_, hm2⟩, hm⟩`.

Establish `: Ai * Formalism.MainNotions.S.uMat x * A = m`. Establish `hx : Formalism.MainNotions.S.uMat x = A * m * Ai` using `hm.symm`. Rewrite using `[hx]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[hAiA, Matrix.mul_one, ← Matrix.mul_assoc, hAiA, Matrix.one_mul]`.

Rewrite using `[this]`. Conclude with `hm2`. Rewrite using `[hset]`. Conclude with `hemb.isCompact_preimage hcomp`. Take `⟨U, hUo, h1U, hU⟩` from `Formalism.REAL.ballOpen n R (by rw [hR]; linarith)`.

Use `mem_interior.mpr ⟨(fun x : Formalism.REAL.UJ ε => Ai * Formalism.MainNotions.S.uMat x * A) ⁻¹' U, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Conclude with `(hU _ hx).le`. Conclude with `hUo.preimage ((continuous_const.mul hemb.continuous).mul continuous_const)`. Use `show Ai * Formalism.MainNotions.S.uMat (1 : Formalism.REAL.UJ ε) * A ∈ U`.

Establish `h1 : Formalism.MainNotions.S.uMat (1 : Formalism.REAL.UJ ε) = 1` using `rfl`. Rewrite using `[h1, Matrix.mul_one, hAiA]`. Conclude with `h1U`. Introduce `x y hxy`. Establish `h1 : Ai * Formalism.MainNotions.S.uMat y * A * k' = k' * (Ai * Formalism.MainNotions.S.uMat x * A)`.

Use `congrArg (fun M => Ai * M * A) hxy` as an intermediate fact. Simplify using `only [Matrix.mul_assoc] at this ⊢`. Rewrite `this` using `[hAiA, Matrix.mul_one, ← Matrix.mul_assoc Ai A, hAiA, Matrix.one_mul]`. Conclude with `this`. Establish `h2 : Ai * Formalism.MainNotions.S.uMat y * A = k' * (Ai * Formalism.MainNotions.S.uMat x * A) * star k'`.

Rewrite using `[← h1, Matrix.mul_assoc _ k', hk'u2, Matrix.mul_one]`. Establish `h3 : Formalism.REAL.hs (Ai * Formalism.MainNotions.S.uMat y * A) = Formalism.REAL.hs (Ai * Formalism.MainNotions.S.uMat x * A)`. Rewrite using `[h2, ((Formalism.REAL.hSBall n ε').2 _ _ (inst_Kset_star ε' hk')).1, ((Formalism.REAL.hSBall n ε').2 _ _ hk').2]`. Simplify using `only [Set.mem_ofPred_eq, h3]`.
-/
theorem placeDecomp_of (hE : InstExpFix) (hAB : InstAdaptBasis) : InstPlaceDecomp := by
  intro n ε ι _ _ B hBG g hg hgB
  obtain ⟨A, ε', T, hA, hT1, hT2⟩ := hAB n ε ι B hBG
  have hJ'J' : Formalism.REAL.Jm ε' * Formalism.REAL.Jm ε' = 1 := Formalism.REAL.Jm_mul_self ε'

  have hAdet : IsUnit A.det := by
    have h1 : IsUnit (Aᴴ * Formalism.REAL.Jm ε * A).det := by
      rw [hA]; exact (Matrix.isUnit_iff_isUnit_det _).mp ⟨⟨_, _, hJ'J', hJ'J'⟩, rfl⟩
    rw [Matrix.det_mul] at h1
    exact isUnit_of_mul_isUnit_right h1
  obtain ⟨Ai, hAi⟩ : ∃ Ai, Ai = A⁻¹ := ⟨_, rfl⟩
  have hAAi : A * Ai = 1 := by rw [hAi]; exact Matrix.mul_nonsing_inv A hAdet
  have hAiA : Ai * A = 1 := by rw [hAi]; exact Matrix.nonsing_inv_mul A hAdet
  have hAiJ : Aiᴴ * Formalism.REAL.Jm ε' * Ai = Formalism.REAL.Jm ε := by
    rw [← hA]
    have h2 : Aiᴴ * Aᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hAAi, Matrix.conjTranspose_one]
    calc Aiᴴ * (Aᴴ * Formalism.REAL.Jm ε * A) * Ai = (Aiᴴ * Aᴴ) * Formalism.REAL.Jm ε * (A * Ai) := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [h2, hAAi, Matrix.one_mul, Matrix.mul_one]
  have tr1 : ∀ m, Formalism.REAL.inUJ ε m → Formalism.REAL.inUJ ε' (Ai * m * A) := by
    intro m hm
    unfold Formalism.REAL.inUJ at *
    have : (Ai * m * A)ᴴ * Formalism.REAL.Jm ε' * (Ai * m * A) =
        Aᴴ * (mᴴ * (Aiᴴ * Formalism.REAL.Jm ε' * Ai) * m) * A := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [this, hAiJ, hm, hA]
  have tr2 : ∀ m, Formalism.REAL.inUJ ε' m → Formalism.REAL.inUJ ε (A * m * Ai) := by
    intro m hm
    unfold Formalism.REAL.inUJ at *
    have : (A * m * Ai)ᴴ * Formalism.REAL.Jm ε * (A * m * Ai) =
        Aiᴴ * (mᴴ * (Aᴴ * Formalism.REAL.Jm ε * A) * m) * Ai := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [this, hA, hm, hAiJ]
  have back : ∀ m, (∀ i ∈ T, m *ᵥ Pi.single i 1 = Pi.single i 1) → A * m * Ai * B = B := by
    intro m hm
    refine Matrix.ext_of_mulVec_single fun j => ?_
    obtain ⟨c, hc0, hc⟩ := hT2 j
    simp only [← Matrix.mulVec_mulVec]
    rw [hc, Matrix.mulVec_mulVec c Ai A, hAiA, Matrix.one_mulVec, inst_fix_sum m T hm c hc0]

  obtain ⟨g', hg'def⟩ : ∃ g', g' = Ai * g * A := ⟨_, rfl⟩
  have hg' : Formalism.REAL.inUJ ε' g' := hg'def ▸ tr1 g hg
  have hg'fix : ∀ i ∈ T, g' *ᵥ Pi.single i 1 = Pi.single i 1 := by
    intro i hi
    obtain ⟨c, hc⟩ := hT1 i hi
    rw [hg'def, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_mulVec c g B, hgB, ← hc,
      Matrix.mulVec_mulVec, hAiA, Matrix.one_mulVec]

  obtain ⟨k', X', hk', hX', hgkX⟩ := (Formalism.REAL.polar n ε').1 g' hg'
  have hXc := ((Formalism.REAL.pChar n ε' X').1.mp hX')
  have hXh : X'.IsHermitian := hXc.1
  obtain ⟨p', hp'def⟩ : ∃ p', p' = NormedSpace.exp X' := ⟨_, rfl⟩
  rw [← hp'def] at hgkX
  have hk'u : star k' * k' = 1 := Matrix.mem_unitaryGroup_iff'.mp hk'.1
  have hk'u2 : k' * star k' = 1 := Matrix.mem_unitaryGroup_iff.mp hk'.1
  have hp'H : p'ᴴ = p' := by rw [hp'def]; exact hXh.exp
  have hgg : g'ᴴ * g' = NormedSpace.exp (X' + X') := by
    rw [Matrix.exp_add_of_commute X' X' (Commute.refl X'), ← hp'def, hgkX, Matrix.conjTranspose_mul, hp'H,
      ← Matrix.star_eq_conjTranspose]
    calc p' * star k' * (k' * p') = p' * (star k' * k') * p' := by simp only [Matrix.mul_assoc]
      _ = p' * p' := by rw [hk'u, Matrix.mul_one]
  have hgHfix : ∀ i ∈ T, g'ᴴ *ᵥ Pi.single i 1 = Pi.single i 1 := by
    intro i hi
    have h1 := congrArg (fun M => M *ᵥ Pi.single i (1 : ℂ)) hg'
    simp only [← Matrix.mulVec_mulVec, hg'fix i hi, inst_Jm_single, Matrix.mulVec_smul] at h1
    have hs : (if ε' i then (1 : ℂ) else -1) ≠ 0 := by split_ifs <;> norm_num
    exact smul_right_injective _ hs h1
  have hXfix : ∀ i ∈ T, X' *ᵥ Pi.single i 1 = 0 := by
    intro i hi
    have h2 : NormedSpace.exp (X' + X') *ᵥ Pi.single i 1 = Pi.single i 1 := by
      rw [← hgg, ← Matrix.mulVec_mulVec, hg'fix i hi, hgHfix i hi]
    have h3 := (hE n (X' + X') (hXh.add hXh) _).mp h2
    have h4 : (2 : ℂ) • (X' *ᵥ Pi.single i 1) = 0 := by rw [two_smul, ← Matrix.add_mulVec]; exact h3
    exact (smul_eq_zero.mp h4).resolve_left two_ne_zero
  have hpfix : ∀ i ∈ T, p' *ᵥ Pi.single i 1 = Pi.single i 1 := fun i hi => by
    rw [hp'def]; exact (hE n X' hXh _).mpr (hXfix i hi)
  have hkfix : ∀ i ∈ T, k' *ᵥ Pi.single i 1 = Pi.single i 1 := by
    intro i hi
    have h1 := hg'fix i hi
    rw [hgkX, ← Matrix.mulVec_mulVec, hpfix i hi] at h1
    exact h1

  obtain ⟨σ', hσdef⟩ : ∃ σ' : Matrix (Fin n) (Fin n) ℂ,
      σ' = Matrix.diagonal fun i => if i ∈ T then (1 : ℂ) else (if ε' i then 1 else -1) := ⟨_, rfl⟩
  have hσσ' : σ' * σ' = 1 := by
    rw [hσdef, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; split_ifs <;> norm_num
  have hσ'UJ : Formalism.REAL.inUJ ε' σ' := by
    unfold Formalism.REAL.inUJ Formalism.REAL.Jm
    rw [hσdef, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1; funext i; simp only [Pi.star_apply]; split_ifs <;> simp
  have hσfix : ∀ i ∈ T, σ' *ᵥ Pi.single i 1 = Pi.single i 1 := by
    intro i hi
    funext r
    rw [hσdef, Matrix.mulVec_diagonal]
    by_cases hr : r = i
    · subst hr; simp [hi]
    · simp [Pi.single_apply, hr]
  have hcol : ∀ i ∈ T, ∀ r, p' r i = if r = i then 1 else 0 := fun i hi r =>
    inst_col_entry p' i (hpfix i hi) r
  have hrow : ∀ i ∈ T, ∀ r, p' i r = if r = i then 1 else 0 := by
    intro i hi r
    have h1 : p' i r = star (p' r i) := by
      conv_lhs => rw [← hp'H]
      rfl
    rw [h1, hcol i hi r]
    split_ifs <;> simp
  have hkey : σ' * p' * σ' = Formalism.REAL.Jm ε' * p' * Formalism.REAL.Jm ε' := by
    ext r c
    simp only [hσdef, Formalism.REAL.Jm, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hr : r ∈ T
    · rw [hrow r hr c]
      by_cases hrc : c = r
      · subst hrc; simp only [hr, if_true]; split_ifs <;> norm_num
      · simp [hrc]
    · by_cases hc : c ∈ T
      · rw [hcol c hc r]
        by_cases hrc : r = c
        · subst hrc; exact absurd hc hr
        · simp [hrc]
      · simp [hr, hc]
  have hJinv : (Formalism.REAL.Jm ε')⁻¹ = Formalism.REAL.Jm ε' := Matrix.inv_eq_left_inv hJ'J'
  have hJX : Formalism.REAL.Jm ε' * X' * Formalism.REAL.Jm ε' = -X' := ((Formalism.REAL.pChar n ε' X').2 hX')
  have hJp : Formalism.REAL.Jm ε' * p' * Formalism.REAL.Jm ε' = NormedSpace.exp (-X') := by
    have := Matrix.exp_conj (Formalism.REAL.Jm ε') X' ⟨⟨_, _, hJ'J', hJ'J'⟩, rfl⟩
    rw [hJinv, hJX] at this
    rw [hp'def, this]
  have hσp' : σ' * p' * σ' * p' = 1 := by
    rw [hkey, hJp, hp'def, ← Matrix.exp_add_of_commute _ _ (Commute.refl X').neg_left, neg_add_cancel,
      NormedSpace.exp_zero]
  have hk'UJ : Formalism.REAL.inUJ ε' k' := (Formalism.REAL.kFacts n ε').1 k' hk'
  have hp'UJ : Formalism.REAL.inUJ ε' p' := by
    have := Formalism.REAL.expUJ n ε' X' hX'.1 1
    simpa [hp'def] using this

  refine ⟨A * k' * Ai, A * p' * Ai, A * σ' * Ai, tr2 _ hk'UJ, tr2 _ hp'UJ, tr2 _ hσ'UJ, back _ hkfix,
    back _ hpfix, back _ hσfix, ?_, ?_, ?_, ?_⟩
  · have : g = A * g' * Ai := by
      rw [hg'def]
      calc g = (A * Ai) * g * (A * Ai) := by rw [hAAi, Matrix.one_mul, Matrix.mul_one]
        _ = A * (Ai * g * A) * Ai := by simp only [Matrix.mul_assoc]
    rw [this, hgkX]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Ai A, hAiA, Matrix.one_mul]
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Ai A, hAiA, Matrix.one_mul, ← Matrix.mul_assoc σ' σ', hσσ', Matrix.one_mul, hAAi]
  · have : A * σ' * Ai * (A * p' * Ai) * (A * σ' * Ai) * (A * p' * Ai) = A * (σ' * p' * σ' * p') * Ai := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Ai A, hAiA, Matrix.one_mul, ← Matrix.mul_assoc Ai A, hAiA, Matrix.one_mul,
        ← Matrix.mul_assoc Ai A, hAiA, Matrix.one_mul]
    rw [this, hσp', Matrix.mul_one, hAAi]
  ·
    set R : ℝ := (n : ℝ) + 1 with hR
    have hemb := (Formalism.REAL.uJEmb n ε).1
    refine ⟨{x : Formalism.REAL.UJ ε | Formalism.REAL.hs (Ai * Formalism.MainNotions.S.uMat x * A) ≤ R}, ?_, ?_, ?_⟩
    · have hcomp : IsCompact ((fun m => A * m * Ai) '' {m | Formalism.REAL.inUJ ε' m ∧ Formalism.REAL.hs m ≤ R}) :=
        ((Formalism.REAL.hSBall n ε').1 R).image ((continuous_const.mul continuous_id).mul continuous_const)
      have hset : {x : Formalism.REAL.UJ ε | Formalism.REAL.hs (Ai * Formalism.MainNotions.S.uMat x * A) ≤ R} =
          (fun g : Formalism.REAL.UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) ⁻¹'
            ((fun m => A * m * Ai) '' {m | Formalism.REAL.inUJ ε' m ∧ Formalism.REAL.hs m ≤ R}) := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_image]
        constructor
        · intro hx
          refine ⟨Ai * Formalism.MainNotions.S.uMat x * A, ⟨tr1 _ x.2, hx⟩, ?_⟩
          simp only [Matrix.mul_assoc]
          rw [hAAi, Matrix.mul_one, ← Matrix.mul_assoc, hAAi, Matrix.one_mul]
        · rintro ⟨m, ⟨_, hm2⟩, hm⟩
          have : Ai * Formalism.MainNotions.S.uMat x * A = m := by
            have hx : Formalism.MainNotions.S.uMat x = A * m * Ai := hm.symm
            rw [hx]
            simp only [Matrix.mul_assoc]
            rw [hAiA, Matrix.mul_one, ← Matrix.mul_assoc, hAiA, Matrix.one_mul]
          rw [this]; exact hm2
      rw [hset]
      exact hemb.isCompact_preimage hcomp
    · obtain ⟨U, hUo, h1U, hU⟩ := Formalism.REAL.ballOpen n R (by rw [hR]; linarith)
      refine mem_interior.mpr ⟨(fun x : Formalism.REAL.UJ ε => Ai * Formalism.MainNotions.S.uMat x * A) ⁻¹' U, ?_, ?_, ?_⟩
      · intro x hx
        exact (hU _ hx).le
      · exact hUo.preimage ((continuous_const.mul hemb.continuous).mul continuous_const)
      · show Ai * Formalism.MainNotions.S.uMat (1 : Formalism.REAL.UJ ε) * A ∈ U
        have h1 : Formalism.MainNotions.S.uMat (1 : Formalism.REAL.UJ ε) = 1 := rfl
        rw [h1, Matrix.mul_one, hAiA]
        exact h1U
    · intro x y hxy
      have h1 : Ai * Formalism.MainNotions.S.uMat y * A * k' = k' * (Ai * Formalism.MainNotions.S.uMat x * A) := by
        have := congrArg (fun M => Ai * M * A) hxy
        simp only [Matrix.mul_assoc] at this ⊢
        rw [hAiA, Matrix.mul_one, ← Matrix.mul_assoc Ai A, hAiA, Matrix.one_mul] at this
        exact this
      have h2 : Ai * Formalism.MainNotions.S.uMat y * A = k' * (Ai * Formalism.MainNotions.S.uMat x * A) * star k' := by
        rw [← h1, Matrix.mul_assoc _ k', hk'u2, Matrix.mul_one]
      have h3 : Formalism.REAL.hs (Ai * Formalism.MainNotions.S.uMat y * A) = Formalism.REAL.hs (Ai * Formalism.MainNotions.S.uMat x * A) := by
        rw [h2, ((Formalism.REAL.hSBall n ε').2 _ _ (inst_Kset_star ε' hk')).1,
          ((Formalism.REAL.hSBall n ε').2 _ _ hk').2]
      simp only [Set.mem_ofPred_eq, h3]

end PI.ScMuExists.UnitaryGroupMassFormula
