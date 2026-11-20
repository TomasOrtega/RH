import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PsiSmoothHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GoodChartExOfStd

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Metric Formalism.MainNotions.S Formalism.MainNotions.S.Gauge Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

def LieSkewU : Prop := ∀ (n : ℕ) (ε : Fin n → Bool) (x : EuclideanSpace ℝ (Fin n × Fin n × Bool)), x ∈ gLie ε →
    (unrealify x)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * unrealify x = 0

def SkewLieU : Prop := ∀ (n : ℕ) (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ),
    Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 → (WithLp.equiv 2 _).symm (realifyFun X) ∈ gLie ε

def CaySkewU : Prop := ∀ (n : ℕ) (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.inUJ ε M → IsUnit (M + 1) →
    ((2 : ℂ) • ((M - 1) * (M + 1)⁻¹))ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * ((2 : ℂ) • ((M - 1) * (M + 1)⁻¹)) = 0

def CayIdU : Prop := ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ), IsUnit (M + 1) →
    (2 + (2 : ℂ) • ((M - 1) * (M + 1)⁻¹)) * (2 - (2 : ℂ) • ((M - 1) * (M + 1)⁻¹))⁻¹ = M

/- English proof (translation)
Conclude with `Formalism.MainNotions.S.Gauge.unrealify_realify X`.
-/
theorem unr_re {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : unrealify ((WithLp.equiv 2 _).symm (realifyFun X)) = X := by
  exact Formalism.MainNotions.S.Gauge.unrealify_realify X

/- English proof (translation)
Unfold `Formalism.REAL.inUJ at *`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Formalism.REAL.Jm ε := by rw [hA, hB]`.
-/
theorem inUJ_mul {n : ℕ} (ε : Fin n → Bool) {A B : Matrix (Fin n) (Fin n) ℂ} (hA : Formalism.REAL.inUJ ε A)
    (hB : Formalism.REAL.inUJ ε B) : Formalism.REAL.inUJ ε (A * B) := by
  unfold Formalism.REAL.inUJ at *
  calc (A * B)ᴴ * Formalism.REAL.Jm ε * (A * B) = Bᴴ * (Aᴴ * Formalism.REAL.Jm ε * A) * B := by
        rw [conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [hA, hB]

/- English proof (translation)
Unfold `expR`. Rewrite using `[dif_pos (inUJ_exp ε _ hx)]`. Both sides reduce to the same expression.
-/
theorem expR_val {n : ℕ} (ε : Fin n → Bool) (x : EuclideanSpace ℝ (Fin n × Fin n × Bool))
    (hx : (unrealify x)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * unrealify x = 0) :
    (((expR ε x : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
      NormedSpace.exp (unrealify x) := by
  unfold expR
  rw [dif_pos (inUJ_exp ε _ hx)]
  rfl

/- English proof (translation)
Introduce `n ε m h hmh horth ι η _ _ L₀ L₁`. Use `set Mf : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → Matrix (Fin n) (Fin n) ℂ := fun p => NormedSpace.exp (unrealify (L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool))) * NormedSpace.exp (unrealify (L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool))) with hMf`. Establish `hcu : Continuous (unrealify : EuclideanSpace ℝ (Fin n × Fin n × Bool) → Matrix (Fin n) (Fin n) ℂ)` using `(unrLin n).continuous_of_finiteDimensional`. Establish `hMc : Continuous Mf`. Use `Continuous.mul ?_ ?_` and prove the remaining obligations.

Conclude with `NormedSpace.exp_continuous.comp (hcu.comp (continuous_subtype_val.comp (L₀.continuous.comp continuous_fst)))`. Conclude with `NormedSpace.exp_continuous.comp (hcu.comp (continuous_subtype_val.comp (L₁.continuous.comp continuous_snd)))`. Establish `hdet : ∀ᶠ p in 𝓝 (0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η), (Mf p + 1).det ≠ 0`. Establish `hc : Continuous fun p => (Mf p + 1).det` using `(hMc.add continuous_const).matrix_det`. Establish `h0 : (Mf 0 + 1).det ≠ 0`.

Establish `: Mf 0 = 1` using `by simp [hMf, unrealify_zero']`. Rewrite using `[this]`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).1 (unit2 n).isUnit).ne_zero`. Conclude with `hc.continuousAt.eventually_ne h0`. Use `filter_upwards [hdet] with p hp`.

Establish `hu : IsUnit (Mf p + 1)` using `(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hp)`. Use `set a := unrealify (L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) with ha_def`. Use `set b := unrealify (L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) with hb_def`. Establish `hma : (L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) ∈ gLie ε`. Rewrite using `[← hmh]`.

Conclude with `Submodule.mem_sup_left (L₀ p.1).2`. Establish `hmb : (L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) ∈ gLie ε`. Rewrite using `[← hmh]`. Conclude with `Submodule.mem_sup_right (L₁ p.2).2`. Establish `ha` using `hL n ε _ hma`.

Establish `hb` using `hL n ε _ hmb`. Establish `hMU : Formalism.REAL.inUJ ε (Mf p)` using `inUJ_mul ε (inUJ_exp ε a ha) (inUJ_exp ε b hb)`. Use `set X := (2 : ℂ) • ((Mf p - 1) * (Mf p + 1)⁻¹) with hX`. Establish `hXs` using `hC n ε (Mf p) hMU hu`. Establish `hv : (WithLp.equiv 2 _).symm (realifyFun X) ∈ m ⊔ h` using `by rw [hmh]; exact hS n ε X hXs`.

Establish `hrec : (L₀ (psiE ε m h L₀ L₁ p).1 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) + (L₁ (psiE ε m h L₀ L₁ p).2 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) = (WithLp.equiv 2 _).symm (realifyFun X)`. Take `⟨u, hu', w, hw, huw⟩` from `Submodule.mem_sup.1 hv`. Establish `h1 : w ∈ mᗮ` using `by rw [Submodule.mem_orthogonal]; intro z hz; exact horth z hz w hw`. Establish `h2 : u ∈ hᗮ` using `by rw [Submodule.mem_orthogonal]; intro z hz; rw [real_inner_comm]; exact horth u hu' z hz`. Use `show ((L₀ (L₀.symm (m.orthogonalProjectionOnto ((WithLp.equiv 2 _).symm (realifyFun X)))) : m) : EuclideanSpace ℝ (Fin n × Fin n × Bool)) + ((L₁ (L₁.symm (h.orthogonalProjectionOnto ((WithLp.equiv 2 _).symm (realifyFun X)))) : h) : EuclideanSpace ℝ (Fin n × Fin n × Bool)) = _`.

Rewrite using `[LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply, ← huw, map_add, map_add, Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal h1, Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal h2, add_zero, zero_add]`. Rewrite using `[show u = ((⟨u, hu'⟩ : m) : EuclideanSpace ℝ _) from rfl, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self, show w = ((⟨w, hw⟩ : h) : EuclideanSpace ℝ _) from rfl, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]`. Rewrite using `[hrec]`. Establish `hid : (2 + unrealify ((WithLp.equiv 2 _).symm (realifyFun X))) * (2 - unrealify ((WithLp.equiv 2 _).symm (realifyFun X)))⁻¹ = Mf p`. Rewrite using `[unr_re]`.

Conclude with `hI n (Mf p) hu`. Establish `hMunit : IsUnit (Mf p)` using `(Matrix.isUnit_exp a).mul (Matrix.isUnit_exp b)`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Unfold `cayR`.

Rewrite using `[dif_pos ⟨by rw [hid]; exact hMunit, by rw [hid]; exact hMU⟩]`. Use `show (2 + unrealify ((WithLp.equiv 2 _).symm (realifyFun X))) * (2 - unrealify ((WithLp.equiv 2 _).symm (realifyFun X)))⁻¹ = _`. Rewrite using `[hid]`. Use `show Mf p = (((expR ε (L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * (((expR ε (L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix …`. Rewrite using `[expR_val ε _ ha, expR_val ε _ hb]`.
-/
theorem psiInv_of (hL : LieSkewU) (hS : SkewLieU) (hC : CaySkewU) (hI : CayIdU) : PsiInvU := by
  intro n ε m h hmh horth ι η _ _ L₀ L₁
  set Mf : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → Matrix (Fin n) (Fin n) ℂ := fun p =>
    NormedSpace.exp (unrealify (L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool))) *
      NormedSpace.exp (unrealify (L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool))) with hMf
  have hcu : Continuous (unrealify : EuclideanSpace ℝ (Fin n × Fin n × Bool) → Matrix (Fin n) (Fin n) ℂ) :=
    (unrLin n).continuous_of_finiteDimensional
  have hMc : Continuous Mf := by
    refine Continuous.mul ?_ ?_
    · exact NormedSpace.exp_continuous.comp (hcu.comp (continuous_subtype_val.comp (L₀.continuous.comp continuous_fst)))
    · exact NormedSpace.exp_continuous.comp (hcu.comp (continuous_subtype_val.comp (L₁.continuous.comp continuous_snd)))
  have hdet : ∀ᶠ p in 𝓝 (0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η), (Mf p + 1).det ≠ 0 := by
    have hc : Continuous fun p => (Mf p + 1).det := (hMc.add continuous_const).matrix_det
    have h0 : (Mf 0 + 1).det ≠ 0 := by
      have : Mf 0 = 1 := by simp [hMf, unrealify_zero']
      rw [this]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 (unit2 n).isUnit).ne_zero
    exact hc.continuousAt.eventually_ne h0
  filter_upwards [hdet] with p hp
  have hu : IsUnit (Mf p + 1) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hp)
  set a := unrealify (L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) with ha_def
  set b := unrealify (L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) with hb_def
  have hma : (L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) ∈ gLie ε := by
    rw [← hmh]; exact Submodule.mem_sup_left (L₀ p.1).2
  have hmb : (L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) ∈ gLie ε := by
    rw [← hmh]; exact Submodule.mem_sup_right (L₁ p.2).2
  have ha := hL n ε _ hma
  have hb := hL n ε _ hmb
  have hMU : Formalism.REAL.inUJ ε (Mf p) := inUJ_mul ε (inUJ_exp ε a ha) (inUJ_exp ε b hb)
  set X := (2 : ℂ) • ((Mf p - 1) * (Mf p + 1)⁻¹) with hX
  have hXs := hC n ε (Mf p) hMU hu
  have hv : (WithLp.equiv 2 _).symm (realifyFun X) ∈ m ⊔ h := by rw [hmh]; exact hS n ε X hXs

  have hrec : (L₀ (psiE ε m h L₀ L₁ p).1 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) +
      (L₁ (psiE ε m h L₀ L₁ p).2 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) = (WithLp.equiv 2 _).symm (realifyFun X) := by
    obtain ⟨u, hu', w, hw, huw⟩ := Submodule.mem_sup.1 hv
    have h1 : w ∈ mᗮ := by rw [Submodule.mem_orthogonal]; intro z hz; exact horth z hz w hw
    have h2 : u ∈ hᗮ := by rw [Submodule.mem_orthogonal]; intro z hz; rw [real_inner_comm]; exact horth u hu' z hz
    show ((L₀ (L₀.symm (m.orthogonalProjectionOnto ((WithLp.equiv 2 _).symm (realifyFun X)))) : m) :
        EuclideanSpace ℝ (Fin n × Fin n × Bool)) +
      ((L₁ (L₁.symm (h.orthogonalProjectionOnto ((WithLp.equiv 2 _).symm (realifyFun X)))) : h) :
        EuclideanSpace ℝ (Fin n × Fin n × Bool)) = _
    rw [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply, ← huw, map_add, map_add,
      Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal h1,
      Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal h2, add_zero, zero_add]
    rw [show u = ((⟨u, hu'⟩ : m) : EuclideanSpace ℝ _) from rfl, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
      show w = ((⟨w, hw⟩ : h) : EuclideanSpace ℝ _) from rfl, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  rw [hrec]
  have hid : (2 + unrealify ((WithLp.equiv 2 _).symm (realifyFun X))) *
      (2 - unrealify ((WithLp.equiv 2 _).symm (realifyFun X)))⁻¹ = Mf p := by
    rw [unr_re]; exact hI n (Mf p) hu
  have hMunit : IsUnit (Mf p) := (Matrix.isUnit_exp a).mul (Matrix.isUnit_exp b)
  apply Subtype.ext
  apply Units.ext
  unfold cayR
  rw [dif_pos ⟨by rw [hid]; exact hMunit, by rw [hid]; exact hMU⟩]
  show (2 + unrealify ((WithLp.equiv 2 _).symm (realifyFun X))) *
      (2 - unrealify ((WithLp.equiv 2 _).symm (realifyFun X)))⁻¹ = _
  rw [hid]
  show Mf p = (((expR ε (L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) : Formalism.REAL.UJ ε) :
      (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
    (((expR ε (L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) : Formalism.REAL.UJ ε) :
      (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
  rw [expR_val ε _ ha, expR_val ε _ hb]

/- English proof (translation)
Introduce `n ε X hX`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨X, ?_, rfl⟩` and prove the remaining obligations. Introduce `t`. Apply `inUJ_exp` to reduce the goal to its premises.

Rewrite using `[conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]`.
-/
theorem skewLie_holds : SkewLieU := by
  intro n ε X hX
  apply Submodule.subset_span
  refine ⟨X, ?_, rfl⟩
  intro t
  apply inUJ_exp
  rw [conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX,
    smul_zero]

/- English proof (translation)
Introduce `n M hM`. Establish `hdet : IsUnit (M + 1).det` using `(Matrix.isUnit_iff_isUnit_det _).1 hM`. Establish `h1 : (M + 1) * (M + 1)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hdet`. Establish `h2 : (M + 1)⁻¹ * (M + 1) = 1` using `Matrix.nonsing_inv_mul _ hdet`. Use `set A := (M + 1)⁻¹ with hA`.

Establish `two : (2 : Matrix (Fin n) (Fin n) ℂ) = (M + 1) * A + (M + 1) * A`. Rewrite using `[h1]`. Evaluate the numerical expressions. Establish `e1 : (2 : Matrix (Fin n) (Fin n) ℂ) - (2 : ℂ) • ((M - 1) * A) = (4 : ℂ) • A`. Rewrite using `[two, two_smul, show (4 : ℂ) = 2 + 2 by norm_num, add_smul, two_smul]`.

Use `noncomm_ring`. Establish `e2 : (2 : Matrix (Fin n) (Fin n) ℂ) + (2 : ℂ) • ((M - 1) * A) = (4 : ℂ) • (M * A)`. Rewrite using `[two, two_smul, show (4 : ℂ) = 2 + 2 by norm_num, add_smul, two_smul]`. Use `noncomm_ring`. Establish `hinv : ((4 : ℂ) • A)⁻¹ = (4 : ℂ)⁻¹ • (M + 1)`.

Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Rewrite using `[smul_mul_smul_comm, h2, mul_inv_cancel₀ (by norm_num : (4 : ℂ) ≠ 0), one_smul]`. Rewrite using `[e1, e2, hinv, smul_mul_smul_comm, mul_inv_cancel₀ (by norm_num : (4 : ℂ) ≠ 0), one_smul, mul_assoc, h2, mul_one]`.
-/
theorem cayId_holds : CayIdU := by
  intro n M hM
  have hdet : IsUnit (M + 1).det := (Matrix.isUnit_iff_isUnit_det _).1 hM
  have h1 : (M + 1) * (M + 1)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have h2 : (M + 1)⁻¹ * (M + 1) = 1 := Matrix.nonsing_inv_mul _ hdet
  set A := (M + 1)⁻¹ with hA
  have two : (2 : Matrix (Fin n) (Fin n) ℂ) = (M + 1) * A + (M + 1) * A := by
    rw [h1]
    norm_num
  have e1 : (2 : Matrix (Fin n) (Fin n) ℂ) - (2 : ℂ) • ((M - 1) * A) = (4 : ℂ) • A := by
    rw [two, two_smul, show (4 : ℂ) = 2 + 2 by norm_num, add_smul, two_smul]
    noncomm_ring
  have e2 : (2 : Matrix (Fin n) (Fin n) ℂ) + (2 : ℂ) • ((M - 1) * A) = (4 : ℂ) • (M * A) := by
    rw [two, two_smul, show (4 : ℂ) = 2 + 2 by norm_num, add_smul, two_smul]
    noncomm_ring
  have hinv : ((4 : ℂ) • A)⁻¹ = (4 : ℂ)⁻¹ • (M + 1) := by
    apply Matrix.inv_eq_right_inv
    rw [smul_mul_smul_comm, h2, mul_inv_cancel₀ (by norm_num : (4 : ℂ) ≠ 0), one_smul]
  rw [e1, e2, hinv, smul_mul_smul_comm, mul_inv_cancel₀ (by norm_num : (4 : ℂ) ≠ 0), one_smul, mul_assoc, h2,
    mul_one]

/- English proof (translation)
Introduce `n ε M hM hu`. Establish `hdet : IsUnit (M + 1).det` using `(Matrix.isUnit_iff_isUnit_det _).1 hu`. Establish `h1 : (M + 1) * (M + 1)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hdet`. Establish `h2 : (M + 1)⁻¹ * (M + 1) = 1` using `Matrix.nonsing_inv_mul _ hdet`. Use `set A := (M + 1)⁻¹ with hA`.

Use `set J := Formalism.REAL.Jm ε with hJdef`. Establish `hJ : Mᴴ * J * M = J` using `hM`. Establish `h2' : Aᴴ * (Mᴴ + 1) = 1`. Establish `e` using `congrArg Matrix.conjTranspose h1`. Simplify using `only [conjTranspose_mul, conjTranspose_add, conjTranspose_one] at e`.

Conclude with `e`. Establish `hY : (Mᴴ - 1) * J * (M + 1) + (Mᴴ + 1) * J * (M - 1) = 0`. Establish `e : (Mᴴ - 1) * J * (M + 1) + (Mᴴ + 1) * J * (M - 1) = (Mᴴ * J * M + Mᴴ * J * M) - (J + J)` using `by noncomm_ring`. Rewrite using `[e, hJ, sub_self]`. Establish `hL : ((2 : ℂ) • ((M - 1) * A))ᴴ = (2 : ℂ) • (Aᴴ * (Mᴴ - 1))`.

Rewrite using `[conjTranspose_smul, conjTranspose_mul, conjTranspose_sub, conjTranspose_one]`. Use `congr 1`. Simplify using the standard rewrite rules. Rewrite using `[hL]`. Establish `e : (2 : ℂ) • (Aᴴ * (Mᴴ - 1)) * J + J * ((2 : ℂ) • ((M - 1) * A)) = (2 : ℂ) • ((Aᴴ * (Mᴴ - 1) * J * ((M + 1) * A)) + ((Aᴴ * (Mᴴ + 1)) * J * (M - 1) * A))`.

Rewrite using `[h1, h2']`. Simplify using `only [mul_one, one_mul, smul_mul_assoc, mul_smul_comm, smul_add, mul_assoc]`. Rewrite using `[e]`. Establish `e3 : (Aᴴ * (Mᴴ - 1) * J * ((M + 1) * A)) + ((Aᴴ * (Mᴴ + 1)) * J * (M - 1) * A) = Aᴴ * ((Mᴴ - 1) * J * (M + 1) + (Mᴴ + 1) * J * (M - 1)) * A` using `by noncomm_ring`. Rewrite using `[e3, hY, mul_zero, zero_mul, smul_zero]`.
-/
theorem caySkew_holds : CaySkewU := by
  intro n ε M hM hu
  have hdet : IsUnit (M + 1).det := (Matrix.isUnit_iff_isUnit_det _).1 hu
  have h1 : (M + 1) * (M + 1)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have h2 : (M + 1)⁻¹ * (M + 1) = 1 := Matrix.nonsing_inv_mul _ hdet
  set A := (M + 1)⁻¹ with hA
  set J := Formalism.REAL.Jm ε with hJdef
  have hJ : Mᴴ * J * M = J := hM
  have h2' : Aᴴ * (Mᴴ + 1) = 1 := by
    have e := congrArg Matrix.conjTranspose h1
    simp only [conjTranspose_mul, conjTranspose_add, conjTranspose_one] at e
    exact e
  have hY : (Mᴴ - 1) * J * (M + 1) + (Mᴴ + 1) * J * (M - 1) = 0 := by
    have e : (Mᴴ - 1) * J * (M + 1) + (Mᴴ + 1) * J * (M - 1) = (Mᴴ * J * M + Mᴴ * J * M) - (J + J) := by
      noncomm_ring
    rw [e, hJ, sub_self]
  have hL : ((2 : ℂ) • ((M - 1) * A))ᴴ = (2 : ℂ) • (Aᴴ * (Mᴴ - 1)) := by
    rw [conjTranspose_smul, conjTranspose_mul, conjTranspose_sub, conjTranspose_one]
    congr 1
    simp
  rw [hL]
  have e : (2 : ℂ) • (Aᴴ * (Mᴴ - 1)) * J + J * ((2 : ℂ) • ((M - 1) * A)) =
      (2 : ℂ) • ((Aᴴ * (Mᴴ - 1) * J * ((M + 1) * A)) + ((Aᴴ * (Mᴴ + 1)) * J * (M - 1) * A)) := by
    rw [h1, h2']
    simp only [mul_one, one_mul, smul_mul_assoc, mul_smul_comm, smul_add, mul_assoc]
  rw [e]
  have e3 : (Aᴴ * (Mᴴ - 1) * J * ((M + 1) * A)) + ((Aᴴ * (Mᴴ + 1)) * J * (M - 1) * A) =
      Aᴴ * ((Mᴴ - 1) * J * (M + 1) + (Mᴴ + 1) * J * (M - 1)) * A := by
    noncomm_ring
  rw [e3, hY, mul_zero, zero_mul, smul_zero]

/- English proof (translation)
Introduce `n ε m h ι η _ _ L₀ L₁`. Use `set Mf : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → Matrix (Fin n) (Fin n) ℂ := fun p => NormedSpace.exp (unrealify (L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool))) * NormedSpace.exp (unrealify (L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool))) with hMf`. Establish `hcu : Continuous (unrealify : EuclideanSpace ℝ (Fin n × Fin n × Bool) → Matrix (Fin n) (Fin n) ℂ)` using `(unrLin n).continuous_of_finiteDimensional`. Establish `hMc : Continuous Mf`. Use `Continuous.mul ?_ ?_` and prove the remaining obligations.

Conclude with `NormedSpace.exp_continuous.comp (hcu.comp (continuous_subtype_val.comp (L₀.continuous.comp continuous_fst)))`. Conclude with `NormedSpace.exp_continuous.comp (hcu.comp (continuous_subtype_val.comp (L₁.continuous.comp continuous_snd)))`. Establish `hN : ∀ k j, Measurable fun p => ((Mf p + 1)⁻¹) k j`. Introduce `k j`. Establish `e : (fun p => ((Mf p + 1)⁻¹) k j) = fun p => Ring.inverse (Mf p + 1).det * (Mf p + 1).adjugate k j`.

Use function extensionality and compare the values at `p`. Rewrite using `[Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]`. Rewrite using `[e]`. Use `Measurable.mul ?_ ?_` and prove the remaining obligations. Rewrite using `[Ring.inverse_eq_inv']`.

Conclude with `measurable_inv.comp (hMc.add continuous_const).matrix_det.measurable`. Conclude with `((continuous_apply j).comp ((continuous_apply k).comp (hMc.add continuous_const).matrix_adjugate)).measurable`. Establish `hX : ∀ i j, Measurable fun p => ((2 : ℂ) • ((Mf p - 1) * (Mf p + 1)⁻¹)) i j`. Introduce `i j`. Simplify using `only [Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]`.

Use `Measurable.const_mul (Finset.measurable_sum _ fun k _ => Measurable.mul ?_ (hN k j)) _` and prove the remaining obligations. Conclude with `((continuous_apply k).comp ((continuous_apply i).comp (hMc.sub continuous_const))).measurable`. Establish `hv : Measurable fun p => ((WithLp.equiv 2 _).symm (realifyFun ((2 : ℂ) • ((Mf p - 1) * (Mf p + 1)⁻¹))) : EuclideanSpace ℝ (Fin n × Fin n × Bool))`. Use `(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n × Fin n × Bool => ℝ)).symm.continuous.measurable.comp ?_` and prove the remaining obligations. Use `measurable_pi_lambda _ fun q => ?_` and prove the remaining obligations.

Break down `q with ⟨i, j, b⟩` into its components or cases. Consider the cases of `b`. Conclude with `Complex.measurable_re.comp (hX i j)`. Conclude with `Complex.measurable_im.comp (hX i j)`. Conclude with `Measurable.prodMk ((L₀.symm.continuous.comp (m.orthogonalProjectionOnto).continuous).measurable.comp hv) ((L₁.symm.continuous.comp (h.orthogonalProjectionOnto).continuous).measurable.comp hv)`.
-/
theorem psiMeas_holds : PsiMeasU := by
  intro n ε m h ι η _ _ L₀ L₁
  set Mf : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → Matrix (Fin n) (Fin n) ℂ := fun p =>
    NormedSpace.exp (unrealify (L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool))) *
      NormedSpace.exp (unrealify (L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool))) with hMf
  have hcu : Continuous (unrealify : EuclideanSpace ℝ (Fin n × Fin n × Bool) → Matrix (Fin n) (Fin n) ℂ) :=
    (unrLin n).continuous_of_finiteDimensional
  have hMc : Continuous Mf := by
    refine Continuous.mul ?_ ?_
    · exact NormedSpace.exp_continuous.comp (hcu.comp (continuous_subtype_val.comp (L₀.continuous.comp continuous_fst)))
    · exact NormedSpace.exp_continuous.comp (hcu.comp (continuous_subtype_val.comp (L₁.continuous.comp continuous_snd)))
  have hN : ∀ k j, Measurable fun p => ((Mf p + 1)⁻¹) k j := by
    intro k j
    have e : (fun p => ((Mf p + 1)⁻¹) k j) = fun p => Ring.inverse (Mf p + 1).det * (Mf p + 1).adjugate k j := by
      funext p; rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
    rw [e]
    refine Measurable.mul ?_ ?_
    · rw [Ring.inverse_eq_inv']; exact measurable_inv.comp (hMc.add continuous_const).matrix_det.measurable
    · exact ((continuous_apply j).comp ((continuous_apply k).comp
        (hMc.add continuous_const).matrix_adjugate)).measurable
  have hX : ∀ i j, Measurable fun p => ((2 : ℂ) • ((Mf p - 1) * (Mf p + 1)⁻¹)) i j := by
    intro i j
    simp only [Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
    refine Measurable.const_mul (Finset.measurable_sum _ fun k _ => Measurable.mul ?_ (hN k j)) _
    exact ((continuous_apply k).comp ((continuous_apply i).comp (hMc.sub continuous_const))).measurable
  have hv : Measurable fun p => ((WithLp.equiv 2 _).symm (realifyFun ((2 : ℂ) • ((Mf p - 1) * (Mf p + 1)⁻¹))) :
      EuclideanSpace ℝ (Fin n × Fin n × Bool)) := by
    refine (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n × Fin n × Bool => ℝ)).symm.continuous.measurable.comp ?_
    refine measurable_pi_lambda _ fun q => ?_
    rcases q with ⟨i, j, b⟩
    cases b
    · exact Complex.measurable_re.comp (hX i j)
    · exact Complex.measurable_im.comp (hX i j)
  exact Measurable.prodMk
    ((L₀.symm.continuous.comp (m.orthogonalProjectionOnto).continuous).measurable.comp hv)
    ((L₁.symm.continuous.comp (h.orthogonalProjectionOnto).continuous).measurable.comp hv)

/- English proof (translation)
The claim follows from `expProdU_of_two hC psiMeas_holds (psiInv_of hL skewLie_holds caySkew_holds cayId_holds)`.
-/
theorem expProdU_of_cay (hC : CayProdU) (hL : LieSkewU) : ExpProdU :=
  expProdU_of_two hC psiMeas_holds (psiInv_of hL skewLie_holds caySkew_holds cayId_holds)

def cTLin (n : ℕ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun A := Aᴴ
  map_add' A B := conjTranspose_add A B
  map_smul' c A := by
    simp only [RingHom.id_apply]
    rw [← Complex.coe_smul, conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Complex.coe_smul]

/- English proof (translation)
Use `set J := Formalism.REAL.Jm ε`. Establish `hc : ∀ t : ℝ, (NormedSpace.exp (t • X))ᴴ * J * NormedSpace.exp (t • X) = J`. Introduce `t`. Establish `h1` using `hX t`. Simplify using `only [Set.mem_setOf_eq, Formalism.REAL.inUJ] at h1`.

Rewrite using `[← Complex.coe_smul]`. Conclude with `h1`. Establish `he : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X)) X 0`. Use `hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)` as an intermediate fact. Conclude with `this.congr_deriv (by simp)`.

Establish `hs : HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • X))ᴴ) Xᴴ 0` using `(cTLin n).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0 : ℝ) he`. Establish `hG` using `(hs.mul (hasDerivAt_const (0 : ℝ) J)).mul he`. Establish `hG' : HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • X))ᴴ * J * NormedSpace.exp (t • X)) 0 0`. Establish `: (fun t : ℝ => (NormedSpace.exp (t • X))ᴴ * J * NormedSpace.exp (t • X)) = fun _ => J` using `funext hc`. Rewrite using `[this]`.

Conclude with `hasDerivAt_const _ _`. Establish `hu` using `hG.unique hG'`. Simplify using `only [zero_smul, NormedSpace.exp_zero, conjTranspose_one, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, add_zero, Pi.mul_apply] at hu`. Conclude with `hu`.
-/
theorem skew_of_lieOf {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ)
    (hX : X ∈ Formalism.MainNotions.S.lieOf {g : Matrix (Fin n) (Fin n) ℂ | Formalism.REAL.inUJ ε g}) :
    Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := by
  set J := Formalism.REAL.Jm ε
  have hc : ∀ t : ℝ, (NormedSpace.exp (t • X))ᴴ * J * NormedSpace.exp (t • X) = J := by
    intro t
    have h1 := hX t
    simp only [Set.mem_setOf_eq, Formalism.REAL.inUJ] at h1
    rw [← Complex.coe_smul]
    exact h1
  have he : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X)) X 0 := by
    have := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
    exact this.congr_deriv (by simp)
  have hs : HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • X))ᴴ) Xᴴ 0 :=
    (cTLin n).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0 : ℝ) he
  have hG := (hs.mul (hasDerivAt_const (0 : ℝ) J)).mul he
  have hG' : HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • X))ᴴ * J * NormedSpace.exp (t • X)) 0 0 := by
    have : (fun t : ℝ => (NormedSpace.exp (t • X))ᴴ * J * NormedSpace.exp (t • X)) = fun _ => J := funext hc
    rw [this]; exact hasDerivAt_const _ _
  have hu := hG.unique hG'
  simp only [zero_smul, NormedSpace.exp_zero, conjTranspose_one, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero,
    add_zero, Pi.mul_apply] at hu
  exact hu

/- English proof (translation)
Introduce `n ε x hx`. Use `Submodule.span_induction (p := fun v _ => (unrealify v)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * unrealify v = 0) ?_ ?_ ?_ ?_ hx` and prove the remaining obligations. Introduce and unpack `v ⟨X, hX, rfl⟩`. Rewrite using `[unr_re]`. Conclude with `skew_of_lieOf ε X hX`.

Simplify using `[unrealify_zero']`. Introduce `a b _ _ ha hb`. Establish `e : unrealify (a + b) = unrealify a + unrealify b` using `(unrLin n).map_add a b`. Rewrite using `[e, conjTranspose_add, Matrix.add_mul, Matrix.mul_add]`. Rewrite using `[show (unrealify a)ᴴ * Formalism.REAL.Jm ε + (unrealify b)ᴴ * Formalism.REAL.Jm ε + (Formalism.REAL.Jm ε * unrealify a + Formalism.REAL.Jm ε * unrealify b) = ((unrealify a)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * unrealify a) + ((unrealify b)ᴴ * Formalism.REAL.Jm ε + Forma …`.

Introduce `c a _ ha`. Establish `e : unrealify (c • a) = c • unrealify a` using `(unrLin n).map_smul c a`. Rewrite using `[e, conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, ha, smul_zero]`.
-/
theorem lieSkew_holds : LieSkewU := by
  intro n ε x hx
  refine Submodule.span_induction (p := fun v _ => (unrealify v)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * unrealify v = 0)
    ?_ ?_ ?_ ?_ hx
  · rintro v ⟨X, hX, rfl⟩
    rw [unr_re]; exact skew_of_lieOf ε X hX
  · simp [unrealify_zero']
  · intro a b _ _ ha hb
    have e : unrealify (a + b) = unrealify a + unrealify b := (unrLin n).map_add a b
    rw [e, conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
    rw [show (unrealify a)ᴴ * Formalism.REAL.Jm ε + (unrealify b)ᴴ * Formalism.REAL.Jm ε +
        (Formalism.REAL.Jm ε * unrealify a + Formalism.REAL.Jm ε * unrealify b) =
        ((unrealify a)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * unrealify a) +
        ((unrealify b)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * unrealify b) by abel, ha, hb, add_zero]
  · intro c a _ ha
    have e : unrealify (c • a) = c • unrealify a := (unrLin n).map_smul c a
    rw [e, conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, ha, smul_zero]

/- English proof (translation)
Conclude with `expProdU_of_cay hC lieSkew_holds`.
-/
theorem expProdU_of_cayProdU (hC : CayProdU) : ExpProdU := by
  exact expProdU_of_cay hC lieSkew_holds

end PI.AprimeInfW
