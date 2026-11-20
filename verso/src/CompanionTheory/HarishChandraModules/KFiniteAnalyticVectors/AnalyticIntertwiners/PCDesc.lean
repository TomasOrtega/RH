import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.Clause1
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.DjCurveA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExpFromBlocks

open Matrix

noncomputable section

namespace CompanionTheory.D.gk.HC

open Formalism.BasicNotions.TH (GrpData URep GKMod)

section Reindex

variable {p q : ℕ}

def ixC (g : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) : Formalism.BasicNotions.TH.Mat p q :=
  Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm g

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[rx, ixC]`.
-/
theorem rx_ixC (g : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) : rx (ixC g) = g := by
  ext i j; simp [rx, ixC]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[rx, ixC]`.
-/
theorem ixC_rx (X : Formalism.BasicNotions.TH.Mat p q) : ixC (rx X) = X := by
  ext i j; simp [rx, ixC]

/- English proof (translation)
Simplify using `only [rx, ← reindexAlgEquiv_apply ℂ ℂ, map_mul]`.
-/
theorem rx_mulC (A B : Formalism.BasicNotions.TH.Mat p q) : rx (A * B) = rx A * rx B := by
  simp only [rx, ← reindexAlgEquiv_apply ℂ ℂ, map_mul]

/- English proof (translation)
Simplify using `only [ixC, ← reindexAlgEquiv_apply ℂ ℂ, map_mul]`.
-/
theorem ixC_mul (A B : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) : ixC (A * B) = ixC A * ixC B := by
  simp only [ixC, ← reindexAlgEquiv_apply ℂ ℂ, map_mul]

/- English proof (translation)
Simplify using `only [rx, ← reindexAlgEquiv_apply ℂ ℂ, map_one]`.
-/
theorem rx_oneC : rx (1 : Formalism.BasicNotions.TH.Mat p q) = 1 := by
  simp only [rx, ← reindexAlgEquiv_apply ℂ ℂ, map_one]

/- English proof (translation)
Simplify using `only [rx, conjTranspose_reindex]`.
-/
theorem rx_ctC (A : Formalism.BasicNotions.TH.Mat p q) : rx Aᴴ = (rx A)ᴴ := by
  simp only [rx, conjTranspose_reindex]

/- English proof (translation)
Simplify using `only [ixC, conjTranspose_reindex]`.
-/
theorem ixC_ct (A : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) : ixC Aᴴ = (ixC A)ᴴ := by
  simp only [ixC, conjTranspose_reindex]

/- English proof (translation)
Rewrite using `[← ixC_rx A, h, ixC_rx]`.
-/
theorem rx_injC {A B : Formalism.BasicNotions.TH.Mat p q} (h : rx A = rx B) : A = B := by
  rw [← ixC_rx A, h, ixC_rx]

/- English proof (translation)
Use extensionality with `i j`. Take `⟨a, rfl⟩` from `finSumFinEquiv.surjective i`. Take `⟨b, rfl⟩` from `finSumFinEquiv.surjective j`. Simplify using `only [rx, reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Formalism.REAL.Jm, diagonal_apply, EmbeddingLike.apply_eq_iff_eq, epq]`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;>`.

Apply the tactic sequence `simp [Formalism.UG.Jpq, fromBlocks, one_apply] <;> split_ifs <;> simp_all`.
-/
theorem rx_JC : rx (Formalism.UG.Jpq p q) = Formalism.REAL.Jm (epq p q) := by
  ext i j
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective j
  simp only [rx, reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Formalism.REAL.Jm, diagonal_apply,
    EmbeddingLike.apply_eq_iff_eq, epq]
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Formalism.UG.Jpq, fromBlocks, one_apply] <;> split_ifs <;> simp_all

/- English proof (translation)
Rewrite using `[← rx_JC, ixC_rx]`.
-/
theorem ixC_J : ixC (Formalism.REAL.Jm (epq p q)) = Formalism.UG.Jpq p q := by
  rw [← rx_JC, ixC_rx]

/- English proof (translation)
The claim follows from `det_reindex_self _ _`.
-/
theorem det_rxC (A : Formalism.BasicNotions.TH.Mat p q) : (rx A).det = A.det := det_reindex_self _ _

/- English proof (translation)
Simplify using `only [rx, Matrix.trace, reindex_apply, diag, submatrix_apply]`. Conclude with `Fintype.sum_equiv finSumFinEquiv.symm _ _ fun _ => rfl`.
-/
theorem trace_rxC (A : Formalism.BasicNotions.TH.Mat p q) : (rx A).trace = A.trace := by
  simp only [rx, Matrix.trace, reindex_apply, diag, submatrix_apply]
  exact Fintype.sum_equiv finSumFinEquiv.symm _ _ fun _ => rfl

/- English proof (translation)
The claim follows from `(Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential.exp_reindex finSumFinEquiv X).symm`.
-/
theorem rx_expC (X : Formalism.BasicNotions.TH.Mat p q) : rx (NormedSpace.exp X) = NormedSpace.exp (rx X) :=
  (Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential.exp_reindex finSumFinEquiv X).symm

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Formalism.REAL.Jm, diagonal_mul_diagonal, diagonal_apply, one_apply]`. Apply the tactic sequence `split_ifs <;> simp_all`.
-/
theorem Jm_sqC : Formalism.REAL.Jm (epq p q) * Formalism.REAL.Jm (epq p q) = 1 := by
  ext i j; simp only [Formalism.REAL.Jm, diagonal_mul_diagonal, diagonal_apply, one_apply]
  split_ifs <;> simp_all

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Formalism.REAL.Jm, diagonal_conjTranspose, diagonal_apply]`. Apply the tactic sequence `split_ifs <;> simp_all`.
-/
theorem Jm_ctC : (Formalism.REAL.Jm (epq p q))ᴴ = Formalism.REAL.Jm (epq p q) := by
  ext i j; simp only [Formalism.REAL.Jm, diagonal_conjTranspose, diagonal_apply]
  split_ifs <;> simp_all

end Reindex

section Cover

variable {p q : ℕ} (T : GrpData p q)

abbrev covC (x : T.G) : Formalism.BasicNotions.TH.Mat p q := ((T.cov x : GL _ ℂ) : Formalism.BasicNotions.TH.Mat p q)

/- English proof (translation)
The claim follows from `T.sq_sq x`.
-/
theorem sq_sqC (x : T.G) : ((T.sq x : ℂˣ) : ℂ) ^ 2 = (covC T x).det := T.sq_sq x

/- English proof (translation)
The claim follows from `(T.bij (T.cov x) (T.cov_mem x) (T.sq x) (T.sq_sq x)).unique ⟨rfl, rfl⟩ ⟨h1.symm, h2.symm⟩`.
-/
theorem eq_of_covC {x y : T.G} (h1 : T.cov x = T.cov y) (h2 : T.sq x = T.sq y) : x = y :=
  (T.bij (T.cov x) (T.cov_mem x) (T.sq x) (T.sq_sq x)).unique ⟨rfl, rfl⟩ ⟨h1.symm, h2.symm⟩

/- English proof (translation)
Establish `h : (covC T x)ᴴ * Formalism.UG.Jpq p q * covC T x = Formalism.UG.Jpq p q` using `T.cov_mem x`. Use `show (rx (covC T x))ᴴ * Formalism.REAL.Jm (epq p q) * rx (covC T x) = Formalism.REAL.Jm (epq p q)`. Rewrite using `[← rx_JC, ← rx_ctC, ← rx_mulC, ← rx_mulC, h]`.
-/
theorem mem_UJC (x : T.G) : rx (covC T x) ∈ Formalism.MainNotions.S.UJset (epq p q) := by
  have h : (covC T x)ᴴ * Formalism.UG.Jpq p q * covC T x = Formalism.UG.Jpq p q := T.cov_mem x
  show (rx (covC T x))ᴴ * Formalism.REAL.Jm (epq p q) * rx (covC T x) = Formalism.REAL.Jm (epq p q)
  rw [← rx_JC, ← rx_ctC, ← rx_mulC, ← rx_mulC, h]

/- English proof (translation)
Establish `hg' : gᴴ * Formalism.REAL.Jm (epq p q) * g = Formalism.REAL.Jm (epq p q)` using `hg`. Establish `h1 : (ixC g)ᴴ * Formalism.UG.Jpq p q * ixC g = Formalism.UG.Jpq p q`. Rewrite using `[← ixC_J, ← ixC_ct, ← ixC_mul, ← ixC_mul, hg']`. Establish `hinv : (Formalism.UG.Jpq p q * (ixC g)ᴴ * Formalism.UG.Jpq p q) * ixC g = 1`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (ixC g)ᴴ, h1, ← ixC_J, ← ixC_mul, Jm_sqC]`.

Use extensionality with `i j`. Simplify using `[ixC, one_apply]`. Set `u : GL (Formalism.BasicNotions.TH.Ix p q) ℂ` to `⟨ixC g, Formalism.UG.Jpq p q * (ixC g)ᴴ * Formalism.UG.Jpq p q, mul_eq_one_comm.1 hinv, hinv⟩`. Establish `hu : u ∈ Formalism.UG.Upq p q` using `by show (((u : GL _ ℂ) : Formalism.BasicNotions.TH.Mat p q).map (starRingEnd ℂ))ᵀ * Formalism.UG.Jpq p q * (u : Formalism.BasicNotions.TH.Mat p q) = _`. Conclude with `h1`.

Establish `hd : ((w : ℂ)) ^ 2 = ((u : GL _ ℂ) : Formalism.BasicNotions.TH.Mat p q).det`. Rewrite using `[hw, ← det_rxC]`. Use `show g.det = (rx (ixC g)).det`. Rewrite using `[rx_ixC]`. Take `⟨x, ⟨hx1, hx2⟩, -⟩` from `T.bij u hu w hd`.

Use `⟨x, ?_, hx2⟩` and prove the remaining obligations. Use `show rx ((T.cov x : GL _ ℂ) : Formalism.BasicNotions.TH.Mat p q) = g`. Rewrite using `[hx1]`. Conclude with `rx_ixC g`.
-/
theorem exists_liftC {g : Matrix (Fin (p + q)) (Fin (p + q)) ℂ} (hg : g ∈ Formalism.MainNotions.S.UJset (epq p q))
    (w : ℂˣ) (hw : (w : ℂ) ^ 2 = g.det) : ∃ x : T.G, rx (covC T x) = g ∧ T.sq x = w := by
  have hg' : gᴴ * Formalism.REAL.Jm (epq p q) * g = Formalism.REAL.Jm (epq p q) := hg
  have h1 : (ixC g)ᴴ * Formalism.UG.Jpq p q * ixC g = Formalism.UG.Jpq p q := by
    rw [← ixC_J, ← ixC_ct, ← ixC_mul, ← ixC_mul, hg']
  have hinv : (Formalism.UG.Jpq p q * (ixC g)ᴴ * Formalism.UG.Jpq p q) * ixC g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (ixC g)ᴴ, h1, ← ixC_J, ← ixC_mul, Jm_sqC]
    ext i j; simp [ixC, one_apply]
  let u : GL (Formalism.BasicNotions.TH.Ix p q) ℂ :=
    ⟨ixC g, Formalism.UG.Jpq p q * (ixC g)ᴴ * Formalism.UG.Jpq p q, mul_eq_one_comm.1 hinv, hinv⟩
  have hu : u ∈ Formalism.UG.Upq p q := by
    show (((u : GL _ ℂ) : Formalism.BasicNotions.TH.Mat p q).map (starRingEnd ℂ))ᵀ * Formalism.UG.Jpq p q * (u : Formalism.BasicNotions.TH.Mat p q) = _
    exact h1
  have hd : ((w : ℂ)) ^ 2 = ((u : GL _ ℂ) : Formalism.BasicNotions.TH.Mat p q).det := by
    rw [hw, ← det_rxC]; show g.det = (rx (ixC g)).det; rw [rx_ixC]
  obtain ⟨x, ⟨hx1, hx2⟩, -⟩ := T.bij u hu w hd
  refine ⟨x, ?_, hx2⟩
  show rx ((T.cov x : GL _ ℂ) : Formalism.BasicNotions.TH.Mat p q) = g
  rw [hx1]; exact rx_ixC g

/- English proof (translation)
Establish `hg' : gᴴ * Formalism.REAL.Jm (epq p q) * g = Formalism.REAL.Jm (epq p q)` using `hg`. Establish `hdet : g.det ≠ 0`. Introduce `h0`. Use `congrArg Matrix.det hg'` as an intermediate fact. Rewrite `this` using `[det_mul, det_mul, h0, mul_zero]`.

Establish `h2` using `congrArg Matrix.det (Jm_sqC (p := p) (q := q))`. Rewrite `h2` using `[det_mul, ← this, mul_zero, det_one]`. Conclude with `zero_ne_one h2`. Take `⟨w, hw⟩` from `IsAlgClosed.exists_pow_nat_eq g.det two_pos`. Establish `hw0 : w ≠ 0` using `by rintro rfl; simp at hw; exact hdet hw.symm`.

Take `⟨x, hx, -⟩` from `exists_liftC T hg (Units.mk0 w hw0) hw`. Conclude with `⟨x, hx⟩`.
-/
theorem exists_lift'C {g : Matrix (Fin (p + q)) (Fin (p + q)) ℂ} (hg : g ∈ Formalism.MainNotions.S.UJset (epq p q)) :
    ∃ x : T.G, rx (covC T x) = g := by
  have hg' : gᴴ * Formalism.REAL.Jm (epq p q) * g = Formalism.REAL.Jm (epq p q) := hg
  have hdet : g.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hg'
    rw [det_mul, det_mul, h0, mul_zero] at this
    have h2 := congrArg Matrix.det (Jm_sqC (p := p) (q := q))
    rw [det_mul, ← this, mul_zero, det_one] at h2
    exact zero_ne_one h2
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq g.det two_pos
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw; exact hdet hw.symm
  obtain ⟨x, hx, -⟩ := exists_liftC T hg (Units.mk0 w hw0) hw
  exact ⟨x, hx⟩

/- English proof (translation)
Take `⟨z, ⟨h1, h2⟩, -⟩` from `T.bij 1 (one_mem _) (-1) (by simp)`. Conclude with `⟨z, h1, h2⟩`.
-/
theorem exists_zC : ∃ z : T.G, T.cov z = 1 ∧ T.sq z = -1 := by
  obtain ⟨z, ⟨h1, h2⟩, -⟩ := T.bij 1 (one_mem _) (-1) (by simp)
  exact ⟨z, h1, h2⟩

/- English proof (translation)
Establish `h1 : ((T.sq x : ℂˣ) : ℂ) ^ 2 = ((T.sq y : ℂˣ) : ℂ) ^ 2`. Rewrite using `[sq_sqC, sq_sqC]`. Simplify using `only [covC, h]`. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h2 | h2` into its components or cases. Conclude with `Or.inl (Units.ext h2)`.

Conclude with `Or.inr (Units.ext (by simpa using h2))`.
-/
theorem sq_or_negC {x y : T.G} (h : T.cov x = T.cov y) : T.sq x = T.sq y ∨ T.sq x = -T.sq y := by
  have h1 : ((T.sq x : ℂˣ) : ℂ) ^ 2 = ((T.sq y : ℂˣ) : ℂ) ^ 2 := by
    rw [sq_sqC, sq_sqC]; simp only [covC, h]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h2 | h2
  · exact Or.inl (Units.ext h2)
  · exact Or.inr (Units.ext (by simpa using h2))

/- English proof (translation)
Establish `h : (covC T x)ᴴ * Formalism.UG.Jpq p q * covC T x = Formalism.UG.Jpq p q` using `T.cov_mem x`. Establish `hJ : ‖(Formalism.UG.Jpq p q).det‖ = 1`. Simplify using `[Formalism.UG.Jpq, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]`. Establish `hd` using `congrArg (fun A => ‖Matrix.det A‖) h`. Simplify using `only [det_mul, det_conjTranspose, norm_mul, norm_star, hJ, mul_one] at hd`.

Establish `h2 : ‖((T.sq x : ℂˣ) : ℂ)‖ ^ 4 = 1`. Rewrite using `[show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ← norm_pow, sq_sqC, _root_.sq, ← hd]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h2`.
-/
theorem norm_sqC (x : T.G) : ‖((T.sq x : ℂˣ) : ℂ)‖ = 1 := by
  have h : (covC T x)ᴴ * Formalism.UG.Jpq p q * covC T x = Formalism.UG.Jpq p q := T.cov_mem x
  have hJ : ‖(Formalism.UG.Jpq p q).det‖ = 1 := by
    simp [Formalism.UG.Jpq, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]
  have hd := congrArg (fun A => ‖Matrix.det A‖) h
  simp only [det_mul, det_conjTranspose, norm_mul, norm_star, hJ, mul_one] at hd
  have h2 : ‖((T.sq x : ℂˣ) : ℂ)‖ ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ← norm_pow, sq_sqC, _root_.sq, ← hd]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h2

/- English proof (translation)
The claim follows from `Units.continuous_val.comp (continuous_snd.comp T.emb.continuous)`.
-/
theorem sq_contC : Continuous fun x : T.G => ((T.sq x : ℂˣ) : ℂ) :=
  Units.continuous_val.comp (continuous_snd.comp T.emb.continuous)

end Cover

section Twist

variable {p q : ℕ} {T : GrpData p q} (πU : URep T)

def liftC (g : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) : T.G :=
  open Classical in if h : ∃ x : T.G, rx (covC T x) = g then h.choose else 1

def sigC (j : ℕ) (g : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) : πU.H →L[ℂ] πU.H :=
  open Classical in
  if ∃ x : T.G, rx (covC T x) = g then ((((T.sq (liftC g) : ℂˣ) : ℂ))⁻¹ ^ j) • πU.π (liftC g) else 0

/- English proof (translation)
Establish `hex : ∃ y : T.G, rx (covC T y) = rx (covC T x)` using `⟨x, rfl⟩`. Establish `hl : rx (covC T (liftC (T` using `T) (rx (covC T x)))) = rx (covC T x) := by`. Unfold `liftC`. Rewrite using `[dif_pos hex]`. Conclude with `hex.choose_spec`.

Establish `hc : T.cov (liftC (T` using `T) (rx (covC T x))) = T.cov x := Units.ext (rx_injC hl)`. Unfold `sigC`. Rewrite using `[if_pos hex]`. Use `set y := liftC (T := T) (rx (covC T x))`. Break down `sq_or_negC T hc with h | h` into its components or cases.

Rewrite using `[eq_of_covC T hc h]`. Establish `hy : y = z * x` using `eq_of_covC T (by rw [map_mul, hz.1, one_mul, hc]) (by rw [map_mul, hz.2, h]; simp)`. Rewrite using `[h]`. Rewrite using `[hy, map_mul πU.π, hP]`. Use extensionality with `v`.

Simplify using `only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply, smul_smul, Units.val_neg]`. Use `congr 1`. Rewrite using `[inv_neg, neg_pow, mul_comm ((-1 : ℂ) ^ j), mul_assoc, ← mul_pow, show (-1 : ℂ) * -1 = 1 by norm_num, one_pow, mul_one]`.
-/
theorem sigC_eq {j : ℕ} {z : T.G} (hz : T.cov z = 1 ∧ T.sq z = -1) (hP : πU.π z = ((-1 : ℂ) ^ j) • 1)
    (x : T.G) : sigC πU j (rx (covC T x)) = ((((T.sq x : ℂˣ) : ℂ))⁻¹ ^ j) • πU.π x := by
  have hex : ∃ y : T.G, rx (covC T y) = rx (covC T x) := ⟨x, rfl⟩
  have hl : rx (covC T (liftC (T := T) (rx (covC T x)))) = rx (covC T x) := by
    unfold liftC; rw [dif_pos hex]; exact hex.choose_spec
  have hc : T.cov (liftC (T := T) (rx (covC T x))) = T.cov x := Units.ext (rx_injC hl)
  unfold sigC
  rw [if_pos hex]
  set y := liftC (T := T) (rx (covC T x))
  rcases sq_or_negC T hc with h | h
  · rw [eq_of_covC T hc h]
  · have hy : y = z * x := eq_of_covC T (by rw [map_mul, hz.1, one_mul, hc]) (by rw [map_mul, hz.2, h]; simp)
    rw [h]
    rw [hy, map_mul πU.π, hP]
    ext v
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply,
      smul_smul, Units.val_neg]
    congr 1
    rw [inv_neg, neg_pow, mul_comm ((-1 : ℂ) ^ j), mul_assoc, ← mul_pow, show (-1 : ℂ) * -1 = 1 by norm_num, one_pow, mul_one]

end Twist

section Blocks

variable {p q : ℕ}

def sgnC : Formalism.BasicNotions.TH.Ix p q → ℂ := Sum.elim (fun _ => 1) (fun _ => -1)

/- English proof (translation)
Use extensionality with `a b`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;> simp [Formalism.UG.Jpq, sgnC, fromBlocks, diagonal_apply, one_apply] <;> split_ifs <;> simp_all`.
-/
theorem Jpq_diagC : Formalism.UG.Jpq p q = diagonal (sgnC (p := p) (q := q)) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> simp [Formalism.UG.Jpq, sgnC, fromBlocks, diagonal_apply, one_apply]
    <;> split_ifs <;> simp_all

/- English proof (translation)
Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;> simp_all [Formalism.BasicNotions.TH.sameBlock, sgnC] <;> norm_num`.
-/
theorem sgn_neC {a b : Formalism.BasicNotions.TH.Ix p q} (h : ¬ Formalism.BasicNotions.TH.sameBlock a b) : sgnC b - sgnC a ≠ 0 := by
  rcases a with a | a <;> rcases b with b | b <;> simp_all [Formalism.BasicNotions.TH.sameBlock, sgnC] <;> norm_num

/- English proof (translation)
Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;> simp_all [Formalism.BasicNotions.TH.sameBlock, sgnC]`.
-/
theorem sgn_eqC {a b : Formalism.BasicNotions.TH.Ix p q} (h : Formalism.BasicNotions.TH.sameBlock a b) : sgnC b = sgnC a := by
  rcases a with a | a <;> rcases b with b | b <;> simp_all [Formalism.BasicNotions.TH.sameBlock, sgnC]

/- English proof (translation)
Rewrite using `[Jpq_diagC]`. Prove the components needed by the constructor for the conclusion. Introduce `h a b hab`. Use `congrFun (congrFun h a) b` as an intermediate fact. Rewrite `this` using `[mul_diagonal, diagonal_mul]`.

Establish `h2 : M a b * (sgnC b - sgnC a) = 0` using `by rw [mul_sub, this]; ring`. Conclude with `(mul_eq_zero.1 h2).resolve_right (sgn_neC hab)`. Introduce `h`. Use extensionality with `a b`. Rewrite using `[mul_diagonal, diagonal_mul]`.

Distinguish the cases in `hab : Formalism.BasicNotions.TH.sameBlock a b`. Rewrite using `[sgn_eqC hab, mul_comm]`. Rewrite using `[h a b hab]`. Simplify using the standard rewrite rules.
-/
theorem comm_iff_KC (M : Formalism.BasicNotions.TH.Mat p q) :
    M * Formalism.UG.Jpq p q = Formalism.UG.Jpq p q * M ↔ Formalism.BasicNotions.TH.IsKC M := by
  rw [Jpq_diagC]
  constructor
  · intro h a b hab
    have := congrFun (congrFun h a) b
    rw [mul_diagonal, diagonal_mul] at this
    have h2 : M a b * (sgnC b - sgnC a) = 0 := by rw [mul_sub, this]; ring
    exact (mul_eq_zero.1 h2).resolve_right (sgn_neC hab)
  · intro h
    ext a b
    rw [mul_diagonal, diagonal_mul]
    by_cases hab : Formalism.BasicNotions.TH.sameBlock a b
    · rw [sgn_eqC hab, mul_comm]
    · rw [h a b hab]; simp

/- English proof (translation)
Rewrite `*` using `[← comm_iff_KC]`. Rewrite using `[Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hA, Matrix.mul_assoc]`.
-/
theorem isKC_mulC {A B : Formalism.BasicNotions.TH.Mat p q} (hA : Formalism.BasicNotions.TH.IsKC A) (hB : Formalism.BasicNotions.TH.IsKC B) :
    Formalism.BasicNotions.TH.IsKC (A * B) := by
  rw [← comm_iff_KC] at *
  rw [Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hA, Matrix.mul_assoc]

/- English proof (translation)
Rewrite using `[← comm_iff_KC, Matrix.one_mul, Matrix.mul_one]`.
-/
theorem isKC_oneC : Formalism.BasicNotions.TH.IsKC (1 : Formalism.BasicNotions.TH.Mat p q) := by
  rw [← comm_iff_KC, Matrix.one_mul, Matrix.mul_one]

end Blocks

/- English proof (translation)
Establish `hlift : ∀ g : A, ∃ x : T.G, rx (covC T x) = g.1 ∧ T.sq x = W g` using `fun g => exists_liftC T (hA g.2) _ (hW2 g)`. Use `choose xs hxs using hlift`. Use `⟨xs, ?_, fun g => (hxs g).1⟩` and prove the remaining obligations. Establish `h1 : ∀ g, ((T.cov (xs g) : GL _ ℂ) : Formalism.BasicNotions.TH.Mat p q) = ixC g.1` using `fun g => by`. Rewrite using `[← (hxs g).1, ixC_rx]`.

Establish `h2 : ∀ g, (((T.cov (xs g))⁻¹ : GL _ ℂ) : Formalism.BasicNotions.TH.Mat p q) = ixC (Formalism.REAL.Jm (epq p q) * g.1ᴴ * Formalism.REAL.Jm (epq p q))` using `fun g => by`. Establish `hg : g.1ᴴ * Formalism.REAL.Jm (epq p q) * g.1 = Formalism.REAL.Jm (epq p q)` using `hA g.2`. Establish `key : ixC (Formalism.REAL.Jm (epq p q) * g.1ᴴ * Formalism.REAL.Jm (epq p q)) * ((T.cov (xs g) : GL _ ℂ) : Formalism.BasicNotions.TH.Mat p q) = 1`. Rewrite using `[h1, ← ixC_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc g.1ᴴ, hg, Jm_sqC]`. Use extensionality with `i j`.

Simplify using `[ixC, one_apply]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[key, Matrix.one_mul]`. Use `_ = _ := by rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]`. Establish `hc1 : Continuous fun g : A => T.cov (xs g)`.

Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Establish `e : (fun g : A => ((T.cov (xs g) : GL _ ℂ) : Formalism.BasicNotions.TH.Mat p q)) = fun g => ixC g.1` using `funext h1 show Continuous fun g : A => ((T.cov (xs g) : GL _ ℂ) : Formalism.BasicNotions.TH.Mat p q)`. Rewrite using `[e]`. Conclude with `(continuous_id.matrix_reindex _ _).comp continuous_subtype_val`. Establish `e : (fun g : A => (((T.cov (xs g))⁻¹ : GL _ ℂ) : Formalism.BasicNotions.TH.Mat p q)) = fun g => ixC (Formalism.REAL.Jm (epq p q) * g.1ᴴ * Formalism.REAL.Jm (epq p q))` using `funext h2 show Continuous fun g : A => (((T.cov (xs g))⁻¹ : GL _ ℂ) : Formalism.BasicNotions.TH.Mat p q)`.

Rewrite using `[e]`. Conclude with `((continuous_const.mul continuous_subtype_val.matrix_conjTranspose).mul continuous_const).matrix_reindex _ _`. Establish `hc2 : Continuous fun g : A => T.sq (xs g)`. Establish `e : (fun g : A => T.sq (xs g)) = W` using `funext fun g => (hxs g).2`. Rewrite using `[e]`.

Use `Units.continuous_iff.2 ⟨hWc, ?_⟩` and prove the remaining obligations. Use `show Continuous fun g => (((W g)⁻¹ : ℂˣ) : ℂ)`. Simplify using `only [Units.val_inv_eq_inv_val]`. Conclude with `hWc.inv₀ fun g => Units.ne_zero _`. Establish `hc : Continuous ((fun x : T.G => (T.cov x, T.sq x)) ∘ xs)` using `hc1.prodMk hc2`.

Conclude with `T.emb.continuous_iff.2 hc`.
-/
theorem exists_contLiftC {p q : ℕ} (T : GrpData p q) (A : Set (Matrix (Fin (p + q)) (Fin (p + q)) ℂ))
    (hA : A ⊆ Formalism.MainNotions.S.UJset (epq p q)) (W : A → ℂˣ) (hWc : Continuous fun g => ((W g : ℂˣ) : ℂ))
    (hW2 : ∀ g, ((W g : ℂˣ) : ℂ) ^ 2 = (g : Matrix (Fin (p + q)) (Fin (p + q)) ℂ).det) :
    ∃ xs : A → T.G, Continuous xs ∧ ∀ g, rx (covC T (xs g)) = g.1 := by
  have hlift : ∀ g : A, ∃ x : T.G, rx (covC T x) = g.1 ∧ T.sq x = W g := fun g => exists_liftC T (hA g.2) _ (hW2 g)
  choose xs hxs using hlift
  refine ⟨xs, ?_, fun g => (hxs g).1⟩
  have h1 : ∀ g, ((T.cov (xs g) : GL _ ℂ) : Formalism.BasicNotions.TH.Mat p q) = ixC g.1 := fun g => by
    rw [← (hxs g).1, ixC_rx]
  have h2 : ∀ g, (((T.cov (xs g))⁻¹ : GL _ ℂ) : Formalism.BasicNotions.TH.Mat p q) =
      ixC (Formalism.REAL.Jm (epq p q) * g.1ᴴ * Formalism.REAL.Jm (epq p q)) := fun g => by
    have hg : g.1ᴴ * Formalism.REAL.Jm (epq p q) * g.1 = Formalism.REAL.Jm (epq p q) := hA g.2
    have key : ixC (Formalism.REAL.Jm (epq p q) * g.1ᴴ * Formalism.REAL.Jm (epq p q)) *
        ((T.cov (xs g) : GL _ ℂ) : Formalism.BasicNotions.TH.Mat p q) = 1 := by
      rw [h1, ← ixC_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc g.1ᴴ, hg, Jm_sqC]
      ext i j; simp [ixC, one_apply]
    calc (((T.cov (xs g))⁻¹ : GL _ ℂ) : Formalism.BasicNotions.TH.Mat p q)
        = (ixC (Formalism.REAL.Jm (epq p q) * g.1ᴴ * Formalism.REAL.Jm (epq p q)) *
          ((T.cov (xs g) : GL _ ℂ) : Formalism.BasicNotions.TH.Mat p q)) * (((T.cov (xs g))⁻¹ : GL _ ℂ) : Formalism.BasicNotions.TH.Mat p q) := by
          rw [key, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  have hc1 : Continuous fun g : A => T.cov (xs g) := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · have e : (fun g : A => ((T.cov (xs g) : GL _ ℂ) : Formalism.BasicNotions.TH.Mat p q)) = fun g => ixC g.1 := funext h1
      show Continuous fun g : A => ((T.cov (xs g) : GL _ ℂ) : Formalism.BasicNotions.TH.Mat p q)
      rw [e]; exact (continuous_id.matrix_reindex _ _).comp continuous_subtype_val
    · have e : (fun g : A => (((T.cov (xs g))⁻¹ : GL _ ℂ) : Formalism.BasicNotions.TH.Mat p q)) =
          fun g => ixC (Formalism.REAL.Jm (epq p q) * g.1ᴴ * Formalism.REAL.Jm (epq p q)) := funext h2
      show Continuous fun g : A => (((T.cov (xs g))⁻¹ : GL _ ℂ) : Formalism.BasicNotions.TH.Mat p q)
      rw [e]
      exact ((continuous_const.mul continuous_subtype_val.matrix_conjTranspose).mul continuous_const).matrix_reindex _ _
  have hc2 : Continuous fun g : A => T.sq (xs g) := by
    have e : (fun g : A => T.sq (xs g)) = W := funext fun g => (hxs g).2
    rw [e]
    refine Units.continuous_iff.2 ⟨hWc, ?_⟩
    show Continuous fun g => (((W g)⁻¹ : ℂˣ) : ℂ)
    simp only [Units.val_inv_eq_inv_val]
    exact hWc.inv₀ fun g => Units.ne_zero _
  have hc : Continuous ((fun x : T.G => (T.cov x, T.sq x)) ∘ xs) := hc1.prodMk hc2
  exact T.emb.continuous_iff.2 hc

/- English proof (translation)
Establish `hsq0 : ∀ x : T.G, ((T.sq x : ℂˣ) : ℂ) ≠ 0` using `fun x => Units.ne_zero _`. Introduce `g₀ hg₀`. Take `⟨x₀, rfl⟩` from `exists_lift'C T hg₀`. Take `⟨d₀, hd₀def⟩ : ∃ d : ℂ, d = (rx (covC T x₀)).det` from `⟨_, rfl⟩`. Establish `hd₀ : d₀ ≠ 0`.

Rewrite using `[hd₀def, det_rxC, ← sq_sqC]`. Conclude with `pow_ne_zero 2 (hsq0 x₀)`. Take `⟨N, hNdef⟩ : ∃ N : Set (Matrix (Fin (p + q)) (Fin (p + q)) ℂ), N = {g | g.det / d₀ ∈ Complex.slitPlane}` from `⟨_, rfl⟩`. Establish `hNo : IsOpen N` using `hNdef ▸ Complex.isOpen_slitPlane.preimage ((continuous_id.matrix_det).div_const _)`. Establish `hN₀ : rx (covC T x₀) ∈ N`.

Rewrite using `[hNdef]`. Use `show (rx (covC T x₀)).det / d₀ ∈ Complex.slitPlane`. Rewrite using `[← hd₀def, div_self hd₀]`. Conclude with `Complex.one_mem_slitPlane`. Set `A : Set (Matrix (Fin (p + q)) (Fin (p + q)) ℂ)` to `Formalism.MainNotions.S.UJset (epq p q) ∩ N`.

Establish `hmem : ∀ g : A, (g.1.det / d₀) ∈ Complex.slitPlane` using `fun g => by`. Use `g.2.2` as an intermediate fact. Rewrite `this` using `[hNdef]`. Conclude with `this`. Set `Wf : A → ℂ` to `fun g => (T.sq x₀ : ℂ) * (g.1.det / d₀) ^ (2⁻¹ : ℂ)`.

Establish `hW0 : ∀ g, Wf g ≠ 0` using `fun g => mul_ne_zero (hsq0 x₀) (by`. Rewrite using `[Ne, Complex.cpow_eq_zero_iff]`. Conclude with `fun h => Complex.slitPlane_ne_zero (hmem g) h.1)`. Establish `hWc : Continuous Wf` using `continuous_const.mul (continuous_iff_continuousAt.2 fun g => ((continuousAt_cpow_const (hmem g)).comp (f := fun g : A => g.1.det / d₀) ((((continuous_id.matrix_det).div_const _).comp continuous_subtype_val).continuousAt)))`. Establish `hW2 : ∀ g : A, ((Units.mk0 (Wf g) (hW0 g) : ℂˣ) : ℂ) ^ 2 = g.1.det` using `fun g => by`.

Simplify using `only [Units.val_mk0, Wf]`. Rewrite using `[mul_pow, Complex.cpow_ofNat_inv_pow, sq_sqC, ← det_rxC, ← hd₀def]`. Conclude with `mul_div_cancel₀ _ hd₀`. Take `⟨xs, hxc, hxs⟩` from `exists_contLiftC T A (fun g h => h.1) (fun g => Units.mk0 (Wf g) (hW0 g)) (by simpa using hWc) hW2`. Establish `hon : ContinuousOn (fun g => σ g v) A`.

Rewrite using `[continuousOn_iff_continuous_restrict]`. Establish `e1 : A.restrict (fun g => σ g v) = fun g : A => ((((T.sq (xs g) : ℂˣ) : ℂ))⁻¹ ^ j) • πU.π (xs g) v`. Use function extensionality and compare the values at `g`. Use `show σ g.1 v = _`. Rewrite using `[← hxs g, hσ]`.

Both sides reduce to the same expression. Use `show Continuous (A.restrict fun g => σ g v)`. Rewrite using `[e1]`. Conclude with `((((sq_contC T).comp hxc).inv₀ fun g => hsq0 _).pow j).smul ((πU.cont v).comp hxc)`. Conclude with `(hon.continuousWithinAt ⟨hg₀, hN₀⟩).mono_of_mem_nhdsWithin (inter_mem_nhdsWithin _ (hNo.mem_nhds hN₀))`.
-/
theorem sigC_contC {p q : ℕ} {T : GrpData p q} (πU : URep T) {j : ℕ} {σ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ → (πU.H →L[ℂ] πU.H)}
    (hσ : ∀ x, σ (rx (covC T x)) = ((((T.sq x : ℂˣ) : ℂ))⁻¹ ^ j) • πU.π x) (v : πU.H) :
    ContinuousOn (fun g => σ g v) (Formalism.MainNotions.S.UJset (epq p q)) := by
  have hsq0 : ∀ x : T.G, ((T.sq x : ℂˣ) : ℂ) ≠ 0 := fun x => Units.ne_zero _
  intro g₀ hg₀
  obtain ⟨x₀, rfl⟩ := exists_lift'C T hg₀
  obtain ⟨d₀, hd₀def⟩ : ∃ d : ℂ, d = (rx (covC T x₀)).det := ⟨_, rfl⟩
  have hd₀ : d₀ ≠ 0 := by
    rw [hd₀def, det_rxC, ← sq_sqC]; exact pow_ne_zero 2 (hsq0 x₀)
  obtain ⟨N, hNdef⟩ : ∃ N : Set (Matrix (Fin (p + q)) (Fin (p + q)) ℂ), N = {g | g.det / d₀ ∈ Complex.slitPlane} :=
    ⟨_, rfl⟩
  have hNo : IsOpen N := hNdef ▸ Complex.isOpen_slitPlane.preimage ((continuous_id.matrix_det).div_const _)
  have hN₀ : rx (covC T x₀) ∈ N := by
    rw [hNdef]; show (rx (covC T x₀)).det / d₀ ∈ Complex.slitPlane
    rw [← hd₀def, div_self hd₀]; exact Complex.one_mem_slitPlane
  let A : Set (Matrix (Fin (p + q)) (Fin (p + q)) ℂ) := Formalism.MainNotions.S.UJset (epq p q) ∩ N
  have hmem : ∀ g : A, (g.1.det / d₀) ∈ Complex.slitPlane := fun g => by
    have := g.2.2; rw [hNdef] at this; exact this
  let Wf : A → ℂ := fun g => (T.sq x₀ : ℂ) * (g.1.det / d₀) ^ (2⁻¹ : ℂ)
  have hW0 : ∀ g, Wf g ≠ 0 := fun g => mul_ne_zero (hsq0 x₀) (by
    rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => Complex.slitPlane_ne_zero (hmem g) h.1)
  have hWc : Continuous Wf := continuous_const.mul (continuous_iff_continuousAt.2 fun g =>
    ((continuousAt_cpow_const (hmem g)).comp (f := fun g : A => g.1.det / d₀)
      ((((continuous_id.matrix_det).div_const _).comp continuous_subtype_val).continuousAt)))
  have hW2 : ∀ g : A, ((Units.mk0 (Wf g) (hW0 g) : ℂˣ) : ℂ) ^ 2 = g.1.det := fun g => by
    simp only [Units.val_mk0, Wf]
    rw [mul_pow, Complex.cpow_ofNat_inv_pow, sq_sqC, ← det_rxC, ← hd₀def]
    exact mul_div_cancel₀ _ hd₀
  obtain ⟨xs, hxc, hxs⟩ := exists_contLiftC T A (fun g h => h.1) (fun g => Units.mk0 (Wf g) (hW0 g))
    (by simpa using hWc) hW2
  have hon : ContinuousOn (fun g => σ g v) A := by
    rw [continuousOn_iff_continuous_restrict]
    have e1 : A.restrict (fun g => σ g v) = fun g : A => ((((T.sq (xs g) : ℂˣ) : ℂ))⁻¹ ^ j) • πU.π (xs g) v := by
      funext g
      show σ g.1 v = _
      rw [← hxs g, hσ]; rfl
    show Continuous (A.restrict fun g => σ g v)
    rw [e1]
    exact ((((sq_contC T).comp hxc).inv₀ fun g => hsq0 _).pow j).smul ((πU.cont v).comp hxc)
  exact (hon.continuousWithinAt ⟨hg₀, hN₀⟩).mono_of_mem_nhdsWithin
    (inter_mem_nhdsWithin _ (hNo.mem_nhds hN₀))

/- English proof (translation)
Introduce `p q T πU hirr`. Take `⟨z, hz⟩` from `exists_zC T`. Establish `hzz : z * z = 1` using `eq_of_covC T (by rw [map_mul, hz.1, one_mul, map_one]) (by rw [map_mul, hz.2, map_one]; simp)`. Establish `hzc : ∀ x, z * x = x * z` using `fun x => eq_of_covC T (by rw [map_mul, map_mul, hz.1, one_mul, mul_one]) (by rw [map_mul, map_mul, mul_comm])`. Choose the witnesses or unpack the hypotheses as in `⟨j, hP⟩ : ∃ j : ℕ, πU.π z = ((-1 : ℂ) ^ j) • 1 := by`.

Set `S : Submodule ℂ πU.H` to `LinearMap.ker ((πU.π z - 1 : πU.H →L[ℂ] πU.H) : πU.H →ₗ[ℂ] πU.H)`. Establish `hS : IsClosed (S : Set πU.H)` using `(πU.π z - 1).isClosed_ker`. Establish `hinv : ∀ g, ∀ x ∈ S, πU.π g x ∈ S` using `fun g x hx => by`. Establish `hx' : πU.π z x = x` using `sub_eq_zero.1 hx`. Use `show πU.π z (πU.π g x) - πU.π g x = 0`.

Rewrite using `[← ContinuousLinearMap.mul_apply, ← map_mul, hzc, map_mul, ContinuousLinearMap.mul_apply, hx', sub_self]`. Break down `hirr.2 S hS hinv with h | h` into its components or cases. Use `⟨1, ContinuousLinearMap.ext fun v => ?_⟩` and prove the remaining obligations. Establish `h1 : v + πU.π z v ∈ S` using `by show πU.π z (v + πU.π z v) - (v + πU.π z v) = 0`. Rewrite using `[map_add, ← ContinuousLinearMap.mul_apply, ← map_mul, hzz, map_one]`.

Simplify using `[add_comm]`. Rewrite `h1` using `[h, Submodule.mem_bot]`. Simplify using `[eq_neg_of_add_eq_zero_right h1]`. Use `⟨0, ContinuousLinearMap.ext fun v => ?_⟩` and prove the remaining obligations. Establish `h1 : v ∈ S` using `h ▸ Submodule.mem_top`.

Establish `h2 : (πU.π z - 1) v = 0` using `h1`. Simplify `h2` using `[sub_eq_zero]`. Use `set σ := sigC πU j`. Establish `hσ : ∀ x, σ (rx (covC T x)) = ((((T.sq x : ℂˣ) : ℂ))⁻¹ ^ j) • πU.π x` using `sigC_eq πU hz hP`. Establish `hsq0 : ∀ x : T.G, ((T.sq x : ℂˣ) : ℂ) ≠ 0` using `fun x => Units.ne_zero _`.

Establish `hπ : ∀ x, πU.π x = ((((T.sq x : ℂˣ) : ℂ)) ^ j) • σ (rx (covC T x))` using `fun x => by`. Rewrite using `[hσ, smul_smul, ← mul_pow, mul_inv_cancel₀ (hsq0 x), one_pow, one_smul]`. Establish `hrep : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset (epq p q)) σ`. Use `⟨⟨?_, fun a ha b hb => ?_⟩, fun g hg v => ?_, fun v => ?_⟩` and prove the remaining obligations. Use `hσ 1` as an intermediate fact.

Simplify `this` using `[covC, rx_oneC]`. Take `⟨x, rfl⟩` from `exists_lift'C T ha`. Take `⟨y, rfl⟩` from `exists_lift'C T hb`. Rewrite using `[← rx_mulC, show covC T x * covC T y = covC T (x * y) by simp [covC], hσ, hσ, hσ, map_mul, map_mul, Units.val_mul, mul_inv, mul_pow, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul]`. Both sides reduce to the same expression.

Take `⟨x, rfl⟩` from `exists_lift'C T hg`. Rewrite using `[hσ, ContinuousLinearMap.smul_apply, norm_smul, norm_pow, norm_inv, norm_sqC, inv_one, one_pow, one_mul, πU.isom]`. Conclude with `sigC_contC πU hσ v`. Use `⟨j, σ, ⟨hrep, hπ⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `S hS hinv`.

Use `hirr.2 S hS fun x v hv => ?_` and prove the remaining obligations. Rewrite using `[hπ]`. Conclude with `S.smul_mem _ (hinv _ (mem_UJC T x) v hv)`. Introduce `x`. Establish `hK : ∀ k : T.G, k ∈ T.Kset → rx (covC T k) ∈ Formalism.REAL.Kset (epq p q)`.

Introduce `k hk`. Establish `hU` using `mem_UJC T k`. Establish `hU' : (rx (covC T k))ᴴ * Formalism.REAL.Jm (epq p q) * rx (covC T k) = Formalism.REAL.Jm (epq p q)` using `hU`. Establish `hc : rx (covC T k) * Formalism.REAL.Jm (epq p q) = Formalism.REAL.Jm (epq p q) * rx (covC T k)`. Rewrite using `[← rx_JC, ← rx_mulC, ← rx_mulC, (comm_iff_KC _).2 hk]`.

Use `⟨?_, hc⟩` and prove the remaining obligations. Rewrite using `[Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Jm_sqC, Matrix.mul_one]`. Use `_ = (rx (covC T k))ᴴ * Formalism.REAL.Jm (epq p q) * (rx (covC T k) * Formalism.REAL.Jm (epq p q)) := by`.

Rewrite using `[hc]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [← Matrix.mul_assoc, hU', Jm_sqC]`. Establish `hK' : ∀ g ∈ Formalism.REAL.Kset (epq p q), ∃ k : T.G, k ∈ T.Kset ∧ rx (covC T k) = g`. Introduce `g hg`.

Establish `hgU : g ∈ Formalism.MainNotions.S.UJset (epq p q)` using `by show gᴴ * Formalism.REAL.Jm (epq p q) * g = Formalism.REAL.Jm (epq p q)`. Rewrite using `[Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose, (Matrix.mem_unitaryGroup_iff').1 hg.1, Matrix.one_mul]`. Take `⟨k, hk⟩` from `exists_lift'C T hgU`. Use `⟨k, (comm_iff_KC _).1 ?_, hk⟩` and prove the remaining obligations. Apply `rx_injC` to reduce the goal to its premises.

Rewrite using `[rx_mulC, rx_mulC, hk, rx_JC]`. Conclude with `hg.2`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `⟨_, hx, Submodule.subset_span ⟨⟨1, ?_⟩, by simp⟩, fun g hg v hv => ?_⟩` and prove the remaining obligations.

Use `show Formalism.BasicNotions.TH.IsKC (covC T 1)`. Simplify using `only [covC, map_one, Units.val_one]`. Conclude with `isKC_oneC`. Take `⟨k, hk, rfl⟩` from `hK' g hg`. Rewrite using `[hσ]`.

Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Use `Submodule.span_induction (fun y hy => ?_) (by simp) (fun a b _ _ ha hb => by rw [map_add]; exact add_mem ha hb) (fun c a _ ha => by rw [map_smul]; exact Submodule.smul_mem _ _ ha) hv` and prove the remaining obligations. Take `⟨⟨k', hk'⟩, rfl⟩` from `hy`. Use `Submodule.subset_span ⟨⟨k * k', ?_⟩, by simp⟩` and prove the remaining obligations. Use `show Formalism.BasicNotions.TH.IsKC (covC T (k * k'))`.

Simplify using `only [covC, map_mul, Units.val_mul]`. Conclude with `isKC_mulC hk hk'`. Introduce and unpack `⟨S, hSf, hxS, hSK⟩`. Use `Submodule.finiteDimensional_of_le (S₂ := S) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨k, hk⟩, rfl⟩`.

Use `show πU.π k x ∈ S`. Rewrite using `[hπ]`. Conclude with `S.smul_mem _ (hSK _ (hK k hk) x hxS)`. Introduce `X hX`. Establish `hXg : ReciprocityTheory.ChartRestriction.DS.inG (epq p q) (rx X)`.

Establish `h : Xᴴ * Formalism.UG.Jpq p q + Formalism.UG.Jpq p q * X = 0` using `hX`. Use `show (rx X)ᴴ * Formalism.REAL.Jm (epq p q) + Formalism.REAL.Jm (epq p q) * rx X = 0`. Rewrite using `[← rx_JC, ← rx_ctC, ← rx_mulC, ← rx_mulC]`. Establish `: rx (Xᴴ * Formalism.UG.Jpq p q) + rx (Formalism.UG.Jpq p q * X) = rx (Xᴴ * Formalism.UG.Jpq p q + Formalism.UG.Jpq p q * X)`. Use extensionality with `a b`.

Simplify using `[rx]`. Rewrite using `[this, h]`. Simplify using `[rx]`. Use `⟨hXg, fun t => ?_⟩` and prove the remaining obligations. Establish `hmem : ∀ s : ℝ, s • X ∈ Formalism.BasicNotions.TH.upq p q` using `fun s => by`.

Establish `h : Xᴴ * Formalism.UG.Jpq p q + Formalism.UG.Jpq p q * X = 0` using `hX`. Use `show (s • X)ᴴ * Formalism.UG.Jpq p q + Formalism.UG.Jpq p q * (s • X) = 0`. Rewrite using `[conjTranspose_smul, star_trivial, smul_mul_assoc, mul_smul_comm, ← smul_add, h, smul_zero]`. Set `φ : ℝ → ℂ` to `fun s => ((T.sq (T.expt (s • X)) : ℂˣ) : ℂ)`. Establish `hφc : Continuous φ` using `(sq_contC T).comp ((T.expt_cont.comp_continuous (continuous_id.smul continuous_const) hmem))`.

Establish `hφ2 : ∀ s, φ s ^ 2 = Complex.exp (s * X.trace)` using `fun s => by show ((T.sq (T.expt (s • X)) : ℂˣ) : ℂ) ^ 2 = _`. Rewrite using `[sq_sqC]`. Use `show ((T.cov (T.expt (s • X)) : GL _ ℂ) : Formalism.BasicNotions.TH.Mat p q).det = _`. Rewrite using `[T.expt_cov _ (hmem s)]`. Use `PI.UnitaryCorollaryDerivatives.DjC.mul_hom_exp (fun s => (NormedSpace.exp (s • X)).det) X.trace (fun a b => ?_) ?_ ?_ s` and prove the remaining obligations.

Rewrite using `[add_smul, Matrix.exp_add_of_commute _ _ ((Commute.refl X).smul_left _ |>.smul_right _), det_mul]`. Simplify using the standard rewrite rules. Apply the tactic sequence `exact PI.UnitaryCorollaryDerivatives.DjC.hasDerivAt_det_of_one _ _ (by simp) fun a b => PI.UnitaryCorollaryDerivatives.DjC.hasDerivAt_exp_entry X a b`. Establish `hφe : ∀ s, φ s = Complex.exp (s * X.trace / 2)`. Set `ψ : ℝ → ℂ` to `fun s => φ s * Complex.exp (-(s * X.trace / 2))`.

Establish `hψ2 : ∀ s, ψ s ^ 2 = 1` using `fun s => by`. Simplify using `only [ψ, mul_pow, hφ2, ← Complex.exp_nat_mul, ← Complex.exp_add]`. Use `push_cast`. Put the polynomial expressions in normal form. Simplify using the standard rewrite rules.

Establish `hψc : Continuous ψ` using `hφc.mul (Complex.continuous_exp.comp (by fun_prop))`. Establish `hψ0 : ψ 0 = 1`. Simplify using `only [ψ, φ, zero_smul, T.expt_zero, map_one, Units.val_one, Complex.ofReal_zero, zero_mul, zero_div, neg_zero, Complex.exp_zero, mul_one]`. Establish `hcl : IsClopen {s | ψ s = 1}`. Use `⟨isClosed_eq hψc continuous_const, ?_⟩` and prove the remaining obligations.

Establish `: {s | ψ s = 1} = {s | ‖ψ s - 1‖ < 1}`. Use extensionality with `s`. Simplify using `only [Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Rewrite using `[h]`. Simplify using the standard rewrite rules. Introduce `h`. Establish `h2 : ψ s * ψ s = 1` using `by rw [← _root_.sq]; exact hψ2 s`. Break down `mul_self_eq_one_iff.1 h2 with h3 | h3` into its components or cases.

Conclude with `h3`. Rewrite `h` using `[h3]`. Evaluate the numerical expressions using `at h`. Rewrite using `[this]`. Conclude with `isOpen_lt (hψc.sub continuous_const).norm continuous_const`.

Introduce `s`. Use `(hcl.eq_univ ⟨0, hψ0⟩).ge (Set.mem_univ s)` as an intermediate fact. Establish `h1 : φ s * Complex.exp (-(s * X.trace / 2)) = 1` using `this`. Rewrite using `[← mul_one (Complex.exp _), ← h1, mul_comm (φ s), ← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]`. Rewrite using `[hπ, show covC T (T.expt (t • X)) = NormedSpace.exp (t • X) from T.expt_cov _ (hmem t), rx_expC]`.

Use `show (φ t ^ j) • _ = _`. Rewrite using `[hφe, ← Complex.exp_nat_mul]`. Use `congr 2`.
-/
theorem harish_chandra_descent : Descend := by
  intro p q T πU hirr
  obtain ⟨z, hz⟩ := exists_zC T
  have hzz : z * z = 1 := eq_of_covC T (by rw [map_mul, hz.1, one_mul, map_one]) (by rw [map_mul, hz.2, map_one]; simp)
  have hzc : ∀ x, z * x = x * z := fun x =>
    eq_of_covC T (by rw [map_mul, map_mul, hz.1, one_mul, mul_one]) (by rw [map_mul, map_mul, mul_comm])

  obtain ⟨j, hP⟩ : ∃ j : ℕ, πU.π z = ((-1 : ℂ) ^ j) • 1 := by
    let S : Submodule ℂ πU.H := LinearMap.ker ((πU.π z - 1 : πU.H →L[ℂ] πU.H) : πU.H →ₗ[ℂ] πU.H)
    have hS : IsClosed (S : Set πU.H) := (πU.π z - 1).isClosed_ker
    have hinv : ∀ g, ∀ x ∈ S, πU.π g x ∈ S := fun g x hx => by
      have hx' : πU.π z x = x := sub_eq_zero.1 hx
      show πU.π z (πU.π g x) - πU.π g x = 0
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, hzc, map_mul, ContinuousLinearMap.mul_apply, hx', sub_self]
    rcases hirr.2 S hS hinv with h | h
    · refine ⟨1, ContinuousLinearMap.ext fun v => ?_⟩
      have h1 : v + πU.π z v ∈ S := by
        show πU.π z (v + πU.π z v) - (v + πU.π z v) = 0
        rw [map_add, ← ContinuousLinearMap.mul_apply, ← map_mul, hzz, map_one]
        simp [add_comm]
      rw [h, Submodule.mem_bot] at h1
      simp [eq_neg_of_add_eq_zero_right h1]
    · refine ⟨0, ContinuousLinearMap.ext fun v => ?_⟩
      have h1 : v ∈ S := h ▸ Submodule.mem_top
      have h2 : (πU.π z - 1) v = 0 := h1
      simpa [sub_eq_zero] using h2
  set σ := sigC πU j
  have hσ : ∀ x, σ (rx (covC T x)) = ((((T.sq x : ℂˣ) : ℂ))⁻¹ ^ j) • πU.π x := sigC_eq πU hz hP
  have hsq0 : ∀ x : T.G, ((T.sq x : ℂˣ) : ℂ) ≠ 0 := fun x => Units.ne_zero _
  have hπ : ∀ x, πU.π x = ((((T.sq x : ℂˣ) : ℂ)) ^ j) • σ (rx (covC T x)) := fun x => by
    rw [hσ, smul_smul, ← mul_pow, mul_inv_cancel₀ (hsq0 x), one_pow, one_smul]

  have hrep : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset (epq p q)) σ := by
    refine ⟨⟨?_, fun a ha b hb => ?_⟩, fun g hg v => ?_, fun v => ?_⟩
    · have := hσ 1
      simpa [covC, rx_oneC] using this
    · obtain ⟨x, rfl⟩ := exists_lift'C T ha
      obtain ⟨y, rfl⟩ := exists_lift'C T hb
      rw [← rx_mulC, show covC T x * covC T y = covC T (x * y) by simp [covC], hσ, hσ, hσ, map_mul, map_mul,
        Units.val_mul, mul_inv, mul_pow, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul]
      rfl
    · obtain ⟨x, rfl⟩ := exists_lift'C T hg
      rw [hσ, ContinuousLinearMap.smul_apply, norm_smul, norm_pow, norm_inv, norm_sqC, inv_one, one_pow, one_mul,
        πU.isom]
    · exact sigC_contC πU hσ v
  refine ⟨j, σ, ⟨hrep, hπ⟩, ?_, ?_, ?_⟩
  ·
    intro S hS hinv
    refine hirr.2 S hS fun x v hv => ?_
    rw [hπ]
    exact S.smul_mem _ (hinv _ (mem_UJC T x) v hv)
  ·
    intro x
    have hK : ∀ k : T.G, k ∈ T.Kset → rx (covC T k) ∈ Formalism.REAL.Kset (epq p q) := by
      intro k hk
      have hU := mem_UJC T k
      have hU' : (rx (covC T k))ᴴ * Formalism.REAL.Jm (epq p q) * rx (covC T k) = Formalism.REAL.Jm (epq p q) := hU
      have hc : rx (covC T k) * Formalism.REAL.Jm (epq p q) = Formalism.REAL.Jm (epq p q) * rx (covC T k) := by
        rw [← rx_JC, ← rx_mulC, ← rx_mulC, (comm_iff_KC _).2 hk]
      refine ⟨?_, hc⟩
      rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
      calc (rx (covC T k))ᴴ * rx (covC T k)
          = (rx (covC T k))ᴴ * (Formalism.REAL.Jm (epq p q) * Formalism.REAL.Jm (epq p q)) * rx (covC T k) := by
            rw [Jm_sqC, Matrix.mul_one]
        _ = (rx (covC T k))ᴴ * Formalism.REAL.Jm (epq p q) * (rx (covC T k) * Formalism.REAL.Jm (epq p q)) := by
            rw [hc]; simp only [Matrix.mul_assoc]
        _ = 1 := by rw [← Matrix.mul_assoc, hU', Jm_sqC]
    have hK' : ∀ g ∈ Formalism.REAL.Kset (epq p q), ∃ k : T.G, k ∈ T.Kset ∧ rx (covC T k) = g := by
      intro g hg
      have hgU : g ∈ Formalism.MainNotions.S.UJset (epq p q) := by
        show gᴴ * Formalism.REAL.Jm (epq p q) * g = Formalism.REAL.Jm (epq p q)
        rw [Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
          (Matrix.mem_unitaryGroup_iff').1 hg.1, Matrix.one_mul]
      obtain ⟨k, hk⟩ := exists_lift'C T hgU
      refine ⟨k, (comm_iff_KC _).1 ?_, hk⟩
      apply rx_injC; rw [rx_mulC, rx_mulC, hk, rx_JC]; exact hg.2
    constructor
    · intro hx
      refine ⟨_, hx, Submodule.subset_span ⟨⟨1, ?_⟩, by simp⟩, fun g hg v hv => ?_⟩
      · show Formalism.BasicNotions.TH.IsKC (covC T 1); simp only [covC, map_one, Units.val_one]; exact isKC_oneC
      obtain ⟨k, hk, rfl⟩ := hK' g hg
      rw [hσ]
      refine Submodule.smul_mem _ _ ?_
      refine Submodule.span_induction (fun y hy => ?_) (by simp) (fun a b _ _ ha hb => by rw [map_add]; exact add_mem ha hb)
        (fun c a _ ha => by rw [map_smul]; exact Submodule.smul_mem _ _ ha) hv
      obtain ⟨⟨k', hk'⟩, rfl⟩ := hy
      refine Submodule.subset_span ⟨⟨k * k', ?_⟩, by simp⟩
      show Formalism.BasicNotions.TH.IsKC (covC T (k * k'))
      simp only [covC, map_mul, Units.val_mul]
      exact isKC_mulC hk hk'
    · rintro ⟨S, hSf, hxS, hSK⟩
      refine Submodule.finiteDimensional_of_le (S₂ := S) (Submodule.span_le.2 ?_)
      rintro _ ⟨⟨k, hk⟩, rfl⟩
      show πU.π k x ∈ S
      rw [hπ]
      exact S.smul_mem _ (hSK _ (hK k hk) x hxS)
  ·
    intro X hX
    have hXg : ReciprocityTheory.ChartRestriction.DS.inG (epq p q) (rx X) := by
      have h : Xᴴ * Formalism.UG.Jpq p q + Formalism.UG.Jpq p q * X = 0 := hX
      show (rx X)ᴴ * Formalism.REAL.Jm (epq p q) + Formalism.REAL.Jm (epq p q) * rx X = 0
      rw [← rx_JC, ← rx_ctC, ← rx_mulC, ← rx_mulC]
      have : rx (Xᴴ * Formalism.UG.Jpq p q) + rx (Formalism.UG.Jpq p q * X) = rx (Xᴴ * Formalism.UG.Jpq p q + Formalism.UG.Jpq p q * X) := by
        ext a b; simp [rx]
      rw [this, h]; simp [rx]
    refine ⟨hXg, fun t => ?_⟩
    have hmem : ∀ s : ℝ, s • X ∈ Formalism.BasicNotions.TH.upq p q := fun s => by
      have h : Xᴴ * Formalism.UG.Jpq p q + Formalism.UG.Jpq p q * X = 0 := hX
      show (s • X)ᴴ * Formalism.UG.Jpq p q + Formalism.UG.Jpq p q * (s • X) = 0
      rw [conjTranspose_smul, star_trivial, smul_mul_assoc, mul_smul_comm, ← smul_add, h, smul_zero]
    let φ : ℝ → ℂ := fun s => ((T.sq (T.expt (s • X)) : ℂˣ) : ℂ)
    have hφc : Continuous φ := (sq_contC T).comp ((T.expt_cont.comp_continuous (continuous_id.smul continuous_const) hmem))
    have hφ2 : ∀ s, φ s ^ 2 = Complex.exp (s * X.trace) := fun s => by
      show ((T.sq (T.expt (s • X)) : ℂˣ) : ℂ) ^ 2 = _
      rw [sq_sqC]
      show ((T.cov (T.expt (s • X)) : GL _ ℂ) : Formalism.BasicNotions.TH.Mat p q).det = _
      rw [T.expt_cov _ (hmem s)]
      refine PI.UnitaryCorollaryDerivatives.DjC.mul_hom_exp (fun s => (NormedSpace.exp (s • X)).det) X.trace (fun a b => ?_) ?_ ?_ s
      · rw [add_smul, Matrix.exp_add_of_commute _ _ ((Commute.refl X).smul_left _ |>.smul_right _), det_mul]
      · simp
      · exact PI.UnitaryCorollaryDerivatives.DjC.hasDerivAt_det_of_one _ _ (by simp) fun a b =>
          PI.UnitaryCorollaryDerivatives.DjC.hasDerivAt_exp_entry X a b
    have hφe : ∀ s, φ s = Complex.exp (s * X.trace / 2) := by
      let ψ : ℝ → ℂ := fun s => φ s * Complex.exp (-(s * X.trace / 2))
      have hψ2 : ∀ s, ψ s ^ 2 = 1 := fun s => by
        simp only [ψ, mul_pow, hφ2, ← Complex.exp_nat_mul, ← Complex.exp_add]
        push_cast; ring_nf; simp
      have hψc : Continuous ψ := hφc.mul (Complex.continuous_exp.comp (by fun_prop))
      have hψ0 : ψ 0 = 1 := by
        simp only [ψ, φ, zero_smul, T.expt_zero, map_one, Units.val_one, Complex.ofReal_zero, zero_mul, zero_div,
          neg_zero, Complex.exp_zero, mul_one]
      have hcl : IsClopen {s | ψ s = 1} := by
        refine ⟨isClosed_eq hψc continuous_const, ?_⟩
        have : {s | ψ s = 1} = {s | ‖ψ s - 1‖ < 1} := by
          ext s; simp only [Set.mem_setOf_eq]; constructor
          · intro h; rw [h]; simp
          · intro h
            have h2 : ψ s * ψ s = 1 := by rw [← _root_.sq]; exact hψ2 s
            rcases mul_self_eq_one_iff.1 h2 with h3 | h3
            · exact h3
            · rw [h3] at h; norm_num at h
        rw [this]; exact isOpen_lt (hψc.sub continuous_const).norm continuous_const
      intro s
      have := (hcl.eq_univ ⟨0, hψ0⟩).ge (Set.mem_univ s)
      have h1 : φ s * Complex.exp (-(s * X.trace / 2)) = 1 := this
      rw [← mul_one (Complex.exp _), ← h1, mul_comm (φ s), ← mul_assoc, ← Complex.exp_add, add_neg_cancel,
        Complex.exp_zero, one_mul]
    rw [hπ, show covC T (T.expt (t • X)) = NormedSpace.exp (t • X) from T.expt_cov _ (hmem t), rx_expC]
    show (φ t ^ j) • _ = _
    rw [hφe, ← Complex.exp_nat_mul]
    congr 2

end CompanionTheory.D.gk.HC
