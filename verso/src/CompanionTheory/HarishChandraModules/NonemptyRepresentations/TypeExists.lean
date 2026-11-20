import CompanionTheory.HarishChandraModules.NonemptyRepresentations.HWRepD
import CompanionTheory.HarishChandraModules.NonemptyRepresentations.TypeHW
import CompanionTheory.HarishChandraModules.NonemptyRepresentations.ExpEntry

open Matrix

noncomputable section

namespace CompanionTheory.D.Inhab.TypeExists

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P CompanionTheory.D.Inhab

variable {k r : ℕ}

def fm (B : Fin k → Fin (2 * r + k + 1) → ℂ) (g : Mx k r) : Matrix (Fin k) (Fin k) ℂ :=
  Matrix.of fun a b => herm (Hpk k r) (g *ᵥ B b) (B a)

/- English proof (translation)
Simplify using `only [fm, herm, Matrix.of_apply]`. Rewrite using `[Matrix.dotProduct_mulVec]`. Simplify using `only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]`.
-/
theorem fm_eq (B : Fin k → Fin (2 * r + k + 1) → ℂ) (g : Mx k r) (a b : Fin k) :
    fm B g a b = ∑ p, ∑ q, (star (B a) ᵥ* Hpk k r) p * g p q * B b q := by
  simp only [fm, herm, Matrix.of_apply]
  rw [Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [fm, Matrix.of_apply, Matrix.add_apply, Matrix.add_mulVec, Qx8.herm_add_left']`.
-/
theorem fm_add (B : Fin k → Fin (2 * r + k + 1) → ℂ) (g h : Mx k r) : fm B (g + h) = fm B g + fm B h := by
  ext a b
  simp only [fm, Matrix.of_apply, Matrix.add_apply, Matrix.add_mulVec, Qx8.herm_add_left']

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [fm, Matrix.of_apply, Matrix.smul_apply, Matrix.smul_mulVec, Qx8.herm_smul_left', smul_eq_mul]`.
-/
theorem fm_smul (B : Fin k → Fin (2 * r + k + 1) → ℂ) (c : ℂ) (g : Mx k r) : fm B (c • g) = c • fm B g := by
  ext a b
  simp only [fm, Matrix.of_apply, Matrix.smul_apply, Matrix.smul_mulVec, Qx8.herm_smul_left', smul_eq_mul]

/- English proof (translation)
Use `continuous_pi fun a => continuous_pi fun b => ?_` and prove the remaining obligations. Simplify using `only [fm_eq]`. Use `fun_prop`.
-/
theorem continuous_fm (B : Fin k → Fin (2 * r + k + 1) → ℂ) : Continuous (fm B) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [fm_eq]
  fun_prop

variable {z : Fin (2 * r + k + 1) → ℂ} {B : Fin k → Fin (2 * r + k + 1) → ℂ}

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [fm, Matrix.of_apply, Matrix.one_mulVec, hB.2.1, Matrix.one_apply, eq_comm]`.
-/
theorem fm_one (hB : IsFrameOf k r [z] B) : fm B 1 = 1 := by
  ext a b
  simp only [fm, Matrix.of_apply, Matrix.one_mulVec, hB.2.1, Matrix.one_apply, eq_comm]

/- English proof (translation)
Use extensionality with `c d`. Simplify using `only [fm, Matrix.of_apply, Qx8.unitB_mulVec, Qx8.herm_smul_left', hB.2.1, Matrix.single_apply]`. Apply the tactic sequence `by_cases h1 : a = c <;> by_cases h2 : b = d <;> simp [h1, h2, eq_comm]`.
-/
theorem fm_unitB (hB : IsFrameOf k r [z] B) (a b : Fin k) : fm B (unitB (Hpk k r) B a b) = Matrix.single a b 1 := by
  ext c d
  simp only [fm, Matrix.of_apply, Qx8.unitB_mulVec, Qx8.herm_smul_left', hB.2.1, Matrix.single_apply]
  by_cases h1 : a = c <;> by_cases h2 : b = d <;> simp [h1, h2, eq_comm]

/- English proof (translation)
Use `HermitianFormSums.complete0 hz (HermitianFormSums.hzz hT) hB (Qx8.inWb_mulVec (Qx8.uw_glev _ hh) (hB.1 b)) ?_` and prove the remaining obligations. Use `conv_lhs => rw [← hh.2.2]`. Rewrite using `[Qx8.herm_UH hh.1, hB.2.2 b z (by simp)]`.
-/
theorem mulVec_frame (hz : inWb k r z) (hT : 0 < Tz k r z) (hB : IsFrameOf k r [z] B) {h : Mx k r}
    (hh : h ∈ UWset k r z) (b : Fin k) : h *ᵥ B b = ∑ c, fm B h c b • B c := by
  refine HermitianFormSums.complete0 hz (HermitianFormSums.hzz hT) hB (Qx8.inWb_mulVec (Qx8.uw_glev _ hh) (hB.1 b)) ?_
  conv_lhs => rw [← hh.2.2]
  rw [Qx8.herm_UH hh.1, hB.2.2 b z (by simp)]

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[Matrix.mul_apply]`. Use `show herm (Hpk k r) ((g * h) *ᵥ B b) (B a) = _`. Rewrite using `[← Matrix.mulVec_mulVec, mulVec_frame hz hT hB hh, Matrix.mulVec_sum]`. Simplify using `only [Matrix.mulVec_smul]`.

Rewrite using `[HermitianFormSums.herm_lsum]`. Conclude with `Finset.sum_congr rfl fun c _ => mul_comm _ _`.
-/
theorem fm_mul (hz : inWb k r z) (hT : 0 < Tz k r z) (hB : IsFrameOf k r [z] B) (g : Mx k r) {h : Mx k r}
    (hh : h ∈ UWset k r z) : fm B (g * h) = fm B g * fm B h := by
  ext a b
  rw [Matrix.mul_apply]
  show herm (Hpk k r) ((g * h) *ᵥ B b) (B a) = _
  rw [← Matrix.mulVec_mulVec, mulVec_frame hz hT hB hh, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul]
  rw [HermitianFormSums.herm_lsum]
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _

/- English proof (translation)
Use extensionality with `a b`. Establish `e` using `Qx8.herm_UH hh.1 (B b) (B a)`. Rewrite `e` using `[hB.2.1, mulVec_frame hz hT hB hh a, HermitianFormSums.herm_rsum]`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply]`. Simplify using `only [eq_comm (a := a), ← e]`.

Both sides reduce to the same expression.
-/
theorem fm_unitary (hz : inWb k r z) (hT : 0 < Tz k r z) (hB : IsFrameOf k r [z] B) {h : Mx k r}
    (hh : h ∈ UWset k r z) : (fm B h)ᴴ * fm B h = 1 := by
  ext a b
  have e := Qx8.herm_UH hh.1 (B b) (B a)
  rw [hB.2.1, mulVec_frame hz hT hB hh a, HermitianFormSums.herm_rsum] at e
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [eq_comm (a := a), ← e]
  rfl

variable {ν : Fin k → ℤ} (R : HWRep k ν)

def πR (B : Fin k → Fin (2 * r + k + 1) → ℂ) (g : Mx k r) : EuclideanSpace ℂ R.I →L[ℂ] EuclideanSpace ℂ R.I :=
  Matrix.toEuclideanCLM (n := R.I) (𝕜 := ℂ) (R.ρ (fm B g))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem πR_apply (g : Mx k r) (v : EuclideanSpace ℂ R.I) :
    πR R B g v = WithLp.toLp 2 (R.ρ (fm B g) *ᵥ v.ofLp) := rfl

/- English proof (translation)
Use `⟨⟨?_, fun a _ b hb => ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[πR, fm_one hB, R.map_one, map_one]`. Rewrite using `[πR, fm_mul hz hT hB a hb, R.map_mul, map_mul]`. Both sides reduce to the same expression. Establish `h1 : ContinuousOn (fun g : Mx k r => R.ρ (fm B g)) (UWset k r z)`.

Use `continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => fun g hg => ?_` and prove the remaining obligations. Establish `hd : (Matrix.of (fm B g : Fin k → Fin k → ℂ)).det ≠ 0`. Introduce `h0`. Use `congrArg Matrix.det (fm_unitary hz hT hB hg)` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul]`.

Establish `h0' : (fm B g).det = 0` using `h0`. Simplify using `[h0'] at this`. Conclude with `((R.diff _ hd i j).continuousAt.comp (f := fm B) (continuous_fm B).continuousAt).continuousWithinAt`. Establish `h2 : Continuous (fun M : Matrix R.I R.I ℂ => Matrix.toEuclideanCLM (n` using `R.I) (𝕜 := ℂ) M) := LinearMap.continuous_of_finiteDimensional (Matrix.toEuclideanCLM (n := R.I) (𝕜 := ℂ)).toAlgEquiv.toLinearMap`. Conclude with `h2.comp_continuousOn h1`.
-/
theorem πR_isRepW (hz : inWb k r z) (hT : 0 < Tz k r z) (hB : IsFrameOf k r [z] B) : IsRepW k r z (πR R B) := by
  refine ⟨⟨?_, fun a _ b hb => ?_⟩, ?_⟩
  · rw [πR, fm_one hB, R.map_one, map_one]
  · rw [πR, fm_mul hz hT hB a hb, R.map_mul, map_mul]; rfl
  · have h1 : ContinuousOn (fun g : Mx k r => R.ρ (fm B g)) (UWset k r z) := by
      refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => fun g hg => ?_
      have hd : (Matrix.of (fm B g : Fin k → Fin k → ℂ)).det ≠ 0 := by
        intro h0
        have := congrArg Matrix.det (fm_unitary hz hT hB hg)
        rw [Matrix.det_mul] at this
        have h0' : (fm B g).det = 0 := h0
        simp [h0'] at this
      exact ((R.diff _ hd i j).continuousAt.comp (f := fm B) (continuous_fm B).continuousAt).continuousWithinAt
    have h2 : Continuous (fun M : Matrix R.I R.I ℂ => Matrix.toEuclideanCLM (n := R.I) (𝕜 := ℂ) M) :=
      LinearMap.continuous_of_finiteDimensional
        (Matrix.toEuclideanCLM (n := R.I) (𝕜 := ℂ)).toAlgEquiv.toLinearMap
    exact h2.comp_continuousOn h1

/- English proof (translation)
Introduce `h hh v`. Establish `e : star (πR R B h) * πR R B h = 1`. Rewrite using `[πR, ← map_star, ← map_mul, Matrix.star_eq_conjTranspose, ← R.map_star, ← R.map_mul, fm_unitary hz hT hB hh, R.map_one, map_one]`. Conclude with `(ContinuousLinearMap.norm_map_iff_adjoint_comp_self (πR R B h)).2 e v`.
-/
theorem πR_unitary (hz : inWb k r z) (hT : 0 < Tz k r z) (hB : IsFrameOf k r [z] B) :
    ∀ h ∈ UWset k r z, ∀ v, ‖πR R B h v‖ = ‖v‖ := by
  intro h hh v
  have e : star (πR R B h) * πR R B h = 1 := by
    rw [πR, ← map_star, ← map_mul, Matrix.star_eq_conjTranspose, ← R.map_star, ← R.map_mul, fm_unitary hz hT hB hh,
      R.map_one, map_one]
  exact (ContinuousLinearMap.norm_map_iff_adjoint_comp_self (πR R B h)).2 e v

/- English proof (translation)
Establish `h` using `R.hasDerivAt_curve (fun t : ℝ => fm B (NormedSpace.exp ((t : ℂ) • X))) (fm B X) (by simp [NormedSpace.exp_zero, fm_one hB]) (fun a b => by`. Simplify using `only [fm_eq]`. Apply the tactic sequence `exact HasDerivAt.fun_sum fun p _ => HasDerivAt.fun_sum fun q _ => ((exp_entry _ X p q).const_mul _).mul_const _) v.ofLp`. Conclude with `(((EuclideanSpace.equiv R.I ℂ).symm.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h).deriv`.
-/
theorem dRep_πR (hB : IsFrameOf k r [z] B) (X : Mx k r) (v : EuclideanSpace ℂ R.I) :
    dRep (πR R B) X v = WithLp.toLp 2 (R.D (fm B X) *ᵥ v.ofLp) := by
  have h := R.hasDerivAt_curve (fun t : ℝ => fm B (NormedSpace.exp ((t : ℂ) • X))) (fm B X)
    (by simp [NormedSpace.exp_zero, fm_one hB]) (fun a b => by
      simp only [fm_eq]
      exact HasDerivAt.fun_sum fun p _ => HasDerivAt.fun_sum fun q _ =>
        ((exp_entry _ X p q).const_mul _).mul_const _) v.ofLp
  exact (((EuclideanSpace.equiv R.I ℂ).symm.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) h).deriv

/- English proof (translation)
Unfold `hpart1 hpart2`. Establish `hI : Complex.I * (1 / (2 * Complex.I)) = 1 / 2` using `by field_simp`. Rewrite using `[smul_smul, hI]`. Use `module`.
-/
theorem hpart_sum {n : ℕ} (H Z : Matrix (Fin n) (Fin n) ℂ) : hpart1 H Z + Complex.I • hpart2 H Z = Z := by
  unfold hpart1 hpart2
  have hI : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by field_simp
  rw [smul_smul, hI]
  module

/- English proof (translation)
Use `conv_rhs => rw [← hpart_sum (Hpk k r) Z, fm_add, fm_smul, R.D_add, R.D_smul, Matrix.add_mulVec, Matrix.smul_mulVec]`. Rewrite using `[EcRep, dRep_πR R hB, dRep_πR R hB]`. Both sides reduce to the same expression.
-/
theorem ecRep_πR (hB : IsFrameOf k r [z] B) (Z : Mx k r) (v : EuclideanSpace ℂ R.I) :
    EcRep (Hpk k r) (πR R B) Z v = WithLp.toLp 2 (R.D (fm B Z) *ᵥ v.ofLp) := by
  conv_rhs => rw [← hpart_sum (Hpk k r) Z, fm_add, fm_smul, R.D_add, R.D_smul, Matrix.add_mulVec, Matrix.smul_mulVec]
  rw [EcRep, dRep_πR R hB, dRep_πR R hB]
  rfl

/- English proof (translation)
Establish `hπ` using `πR_isRepW R hz hT hB`. Establish `e : ∀ a b, EB (πR R B) B a b (WithLp.toLp 2 R.v0) = WithLp.toLp 2 (R.D (Matrix.single a b 1) *ᵥ R.v0)`. Introduce `a b`. Rewrite using `[← fm_unitB hB, ← ecRep_πR R hB _ (WithLp.toLp 2 R.v0), QrD.ecRep_eq hπ.1 hπ.2 (QrD.frame_lie hB a b).1 (QrD.frame_lie hB a b).2]`. Both sides reduce to the same expression.

Conclude with `⟨fun a => by rw [e, R.D_diag]; rfl, fun a b hab => by rw [e, R.D_upper hab]; rfl⟩`.
-/
theorem isHW_πR (hz : inWb k r z) (hT : 0 < Tz k r z) (hB : IsFrameOf k r [z] B) :
    IsHW (EB (πR R B) B) (fun a => (ν a : ℂ)) (WithLp.toLp 2 R.v0) := by
  have hπ := πR_isRepW R hz hT hB
  have e : ∀ a b, EB (πR R B) B a b (WithLp.toLp 2 R.v0) = WithLp.toLp 2 (R.D (Matrix.single a b 1) *ᵥ R.v0) := by
    intro a b
    rw [← fm_unitB hB, ← ecRep_πR R hB _ (WithLp.toLp 2 R.v0),
      QrD.ecRep_eq hπ.1 hπ.2 (QrD.frame_lie hB a b).1 (QrD.frame_lie hB a b).2]
    rfl
  exact ⟨fun a => by rw [e, R.D_diag]; rfl, fun a b hab => by rw [e, R.D_upper hab]; rfl⟩

end CompanionTheory.D.Inhab.TypeExists
