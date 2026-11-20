import Development.WeilBound.ThetaLifts.LatticeBasics.LocUnr
import Development.WeilBound.ThetaLifts.LatticeBasics.LocUnrInertA
import Development.WeilBound.ThetaLifts.LatticeBasics.LocUnrInertN
import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedCohomology.ExistsSelfDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne

noncomputable section

namespace GlobalTheory.ThK.Dbl.Inert

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.LFun.InertChart PositivityTheory.ThK PositivityTheory.ThKH.Iwas PositivityTheory.ThKH.Locpair PositivityTheory.ThKH.Locrep
open GlobalTheory.EmbChart (atPlace evFin_atPlace atPlace_mul_right tensAt)
open GlobalTheory.Doubling (absE)
open GlobalTheory.Doubling (leviOf blkMat dblGram leviMat KeepsDiag)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables

section Alg

variable {L : Type} [CommRing L] {n : ℕ} (a : GL (Fin n) L)

abbrev dg (n : ℕ) (R : Type) [CommRing R] : Matrix (Fin n ⊕ Fin n) (Fin n) R := diagCols (Fin n)

def dA : Matrix (Fin n ⊕ Fin n) (Fin (n + n)) L := (Matrix.fromBlocks a.1 0 0 a.1).submatrix id finSumFinEquiv.symm

def dB : Matrix (Fin (n + n)) (Fin n ⊕ Fin n) L := (Matrix.fromBlocks (a⁻¹).1 0 0 (a⁻¹).1).submatrix finSumFinEquiv.symm id

/- English proof (translation)
Rewrite using `[dA, dB, Matrix.submatrix_mul_equiv]`. Simplify using `[Matrix.fromBlocks_multiply]`.
-/
theorem dA_dB : dA a * dB a = 1 := by
  rw [dA, dB, Matrix.submatrix_mul_equiv]; simp [Matrix.fromBlocks_multiply]

/- English proof (translation)
The claim follows from `(Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv).1 (dA_dB a)`.
-/
theorem dB_dA : dB a * dA a = 1 := (Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv).1 (dA_dB a)

/- English proof (translation)
Establish `: cT c (Matrix.fromBlocks a.1 0 0 a.1) * (dbl J)ᵀ * Matrix.fromBlocks a.1 0 0 a.1 = Matrix.fromBlocks (cT c a.1 * Jᵀ * a.1) 0 0 (-(cT c a.1 * Jᵀ * a.1))`. Simplify using `[cT, dbl, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]`. Rewrite using `[dblGram, blkMat, ← this]`. Both sides reduce to the same expression.
-/
theorem dA_gram (c : L →+* L) (J : Matrix (Fin n) (Fin n) L) :
    cT c (dA a) * (dbl J)ᵀ * dA a = dblGram finSumFinEquiv (cT c a.1 * Jᵀ * a.1) := by
  have : cT c (Matrix.fromBlocks a.1 0 0 a.1) * (dbl J)ᵀ * Matrix.fromBlocks a.1 0 0 a.1 =
      Matrix.fromBlocks (cT c a.1 * Jᵀ * a.1) 0 0 (-(cT c a.1 * Jᵀ * a.1)) := by
    simp [cT, dbl, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  rw [dblGram, blkMat, ← this]; rfl

/- English proof (translation)
Use `conv_lhs => rw [show X = (X.submatrix finSumFinEquiv finSumFinEquiv).submatrix finSumFinEquiv.symm finSumFinEquiv.symm by simp]`. Rewrite using `[dA, dB, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]`. Both sides reduce to the same expression.
-/
theorem dA_conj (X : Matrix (Fin (n + n)) (Fin (n + n)) L) : dA a * X * dB a =
    Matrix.fromBlocks a.1 0 0 a.1 * X.submatrix finSumFinEquiv finSumFinEquiv * Matrix.fromBlocks (a⁻¹).1 0 0 (a⁻¹).1 := by
  conv_lhs => rw [show X = (X.submatrix finSumFinEquiv finSumFinEquiv).submatrix finSumFinEquiv.symm finSumFinEquiv.symm by simp]
  rw [dA, dB, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]; rfl

/- English proof (translation)
Rewrite using `[dA_conj, GlobalTheory.Doubling.submatrix_blkMat]`. Simplify using `[Matrix.fromBlocks_multiply]`.
-/
theorem dA_blk (x : Matrix (Fin n) (Fin n) L) :
    dA a * blkMat finSumFinEquiv x (1 : Matrix (Fin n) (Fin n) L) * dB a = Matrix.fromBlocks (a.1 * x * (a⁻¹).1) 0 0 1 := by
  rw [dA_conj, GlobalTheory.Doubling.submatrix_blkMat]; simp [Matrix.fromBlocks_multiply]

/- English proof (translation)
Rewrite using `[dA_conj, ← Matrix.fromBlocks_toBlocks (X.submatrix _ _)]`. Simplify using `only [dg, diagCols, Matrix.mul_assoc, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul, Matrix.mul_one, Matrix.one_mul, Matrix.zero_mul, add_zero, zero_add, ← Matrix.add_mul]`. Rewrite using `[h]`. Both sides reduce to the same expression.
-/
theorem dA_par {X : Matrix (Fin (n + n)) (Fin (n + n)) L} (h : KeepsDiag finSumFinEquiv X) :
    dA a * X * dB a * dg n L = dg n L * (a.1 * leviMat finSumFinEquiv X * (a⁻¹).1) := by
  rw [dA_conj, ← Matrix.fromBlocks_toBlocks (X.submatrix _ _)]
  simp only [dg, diagCols, Matrix.mul_assoc, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.zero_mul, add_zero, zero_add, ← Matrix.add_mul]
  rw [h]; rfl

/- English proof (translation)
Establish `e : ∀ N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L, (a⁻¹).1 * N.submatrix i j * a.1 = (Matrix.fromBlocks (a⁻¹).1 0 0 (a⁻¹).1 * N * Matrix.fromBlocks a.1 0 0 a.1).submatrix i j` using `fun N => by conv_rhs => rw [← Matrix.fromBlocks_toBlocks N]`. Apply the tactic sequence `rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>`. Apply the tactic sequence `simp only [Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add] <;> rfl`. Establish `d : Matrix.fromBlocks (a⁻¹).1 0 0 (a⁻¹).1 * Matrix.fromBlocks a.1 0 0 a.1 = 1` using `by simp [Matrix.fromBlocks_multiply]`. Rewrite using `[e, dA_conj, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, d, ← Matrix.mul_assoc, ← Matrix.mul_assoc, d, Matrix.one_mul, Matrix.mul_assoc, d, Matrix.mul_one]`.
-/
theorem dA_sub (X : Matrix (Fin (n + n)) (Fin (n + n)) L) {i j : Fin n → Fin n ⊕ Fin n} (hi : i ∈ ({.inl, .inr} : Set _))
    (hj : j ∈ ({.inl, .inr} : Set _)) : (a⁻¹).1 * (dA a * X * dB a - 1).submatrix i j * a.1 =
      (X.submatrix finSumFinEquiv finSumFinEquiv - 1).submatrix i j := by
  have e : ∀ N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L, (a⁻¹).1 * N.submatrix i j * a.1 =
      (Matrix.fromBlocks (a⁻¹).1 0 0 (a⁻¹).1 * N * Matrix.fromBlocks a.1 0 0 a.1).submatrix i j := fun N => by
    conv_rhs => rw [← Matrix.fromBlocks_toBlocks N]
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
      simp only [Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add] <;> rfl
  have d : Matrix.fromBlocks (a⁻¹).1 0 0 (a⁻¹).1 * Matrix.fromBlocks a.1 0 0 a.1 = 1 := by simp [Matrix.fromBlocks_multiply]
  rw [e, dA_conj, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, d, ← Matrix.mul_assoc, ← Matrix.mul_assoc, d, Matrix.one_mul,
    Matrix.mul_assoc, d, Matrix.mul_one]

end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} {Y : Spc F E n}

/- English proof (translation)
The claim follows from `GlobalTheory.InertChars.locIdele_eq_of_inert hw χ 1 (hr.triv_of_even (by simp)) hu (fun _ _ => map_one Circle.toUnits) y`.
-/
theorem chi_at (hw : IsInertAt F E v w) {χ : Chr F E} (hr : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ 0)
    (hu : UnrAt χ w) (y : (w.adicCompletion E)ˣ) : χ (locIdele F w y) = 1 :=
  GlobalTheory.InertChars.locIdele_eq_of_inert hw χ 1 (hr.triv_of_even (by simp)) hu (fun _ _ => map_one Circle.toUnits) y

/- English proof (translation)
Use `set u := GlobalTheory.Doubling.unitFin F E v x`. Establish `e' : toCompl h u.1 = y` using `e`. Establish `h0 : Valued.v y.1 ≠ 0` using `(map_ne_zero _).2 y.ne_zero`. Establish `h1 : Valued.v y.1 = WithZero.exp (-ordL y.1)`. Rewrite using `[ordL, dif_neg h0, neg_neg]`.

Conclude with `(WithZero.coe_unzero h0).symm`. Establish `n0 : Algebra.norm (Fv F v) u.1 ≠ 0` using `(u.isUnit.map _).ne_zero`. Establish `h2 : Valued.v (Algebra.norm (Fv F v) u.1) = WithZero.exp (-(2 * ordL y.1))`. Establish `h3` using `congrArg (toCompl h) (GlobalTheory.Doubling.algebraMap_norm_eq hσ u.1)`. Rewrite `h3` using `[map_mul, ← hc, e', show toCompl h (algebraMap _ _ (Algebra.norm (Fv F v) u.1)) = complMap h (Algebra.norm (Fv F v) u.1) from (toCompl_tmul h _ 1).trans (by rw [map_one, mul_one]; rfl)]`.

Establish `h4` using `congrArg Valued.v h3`. Rewrite `h4` using `[valued_complMap h n0, isUnram_iff.1 (isUnram_of_isInertAt hw) w h, pow_one, map_mul, hv, h1, ← WithZero.exp_add]`. Rewrite using `[h4]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `h5 : (absE F E x : ℝ) = (qV F v : ℝ) ^ ((-(2 * ordL y.1) : ℤ) : ℝ)`. Rewrite using `[GlobalTheory.InertChars.eq_ideleAt_of_at x hx, GlobalTheory.Doubling.absE_ideleAt, GlobalTheory.Doubling.absEv_apply, coe_nnnorm, FinitePlace.norm_def, h2, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, Real.rpow_intCast]`. Conclude with `NNReal.coe_zpow _ _`. Rewrite using `[h5, ← Complex.cpow_mul_ofReal_nonneg (Nat.cast_nonneg _), secVal, MonoidHom.one_apply, Units.val_one, one_mul]`. Use `push_cast`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem abs_at (hσ : IsCMExt F E σ) (hw : IsInertAt F E v w) {h : w.under (𝓞 F) = v} {c : w.adicCompletion E →+* w.adicCompletion E}
    (hc : IsConjAt σ h c) (hv : ∀ x, Valued.v (c x) = Valued.v x) {x : (AE F E)ˣ} (hx : At (evFin F v) (x.1 - 1))
    {y : (w.adicCompletion E)ˣ} (e : piE h x.1 = y) (z : ℂ) : ((absE F E x : ℝ) : ℂ) ^ z = secVal (qV F v) 1 z y := by
  set u := GlobalTheory.Doubling.unitFin F E v x
  have e' : toCompl h u.1 = y := e
  have h0 : Valued.v y.1 ≠ 0 := (map_ne_zero _).2 y.ne_zero
  have h1 : Valued.v y.1 = WithZero.exp (-ordL y.1) := by
    rw [ordL, dif_neg h0, neg_neg]; exact (WithZero.coe_unzero h0).symm
  have n0 : Algebra.norm (Fv F v) u.1 ≠ 0 := (u.isUnit.map _).ne_zero
  have h2 : Valued.v (Algebra.norm (Fv F v) u.1) = WithZero.exp (-(2 * ordL y.1)) := by
    have h3 := congrArg (toCompl h) (GlobalTheory.Doubling.algebraMap_norm_eq hσ u.1)
    rw [map_mul, ← hc, e', show toCompl h (algebraMap _ _ (Algebra.norm (Fv F v) u.1)) = complMap h (Algebra.norm (Fv F v) u.1) from
      (toCompl_tmul h _ 1).trans (by rw [map_one, mul_one]; rfl)] at h3
    have h4 := congrArg Valued.v h3
    rw [valued_complMap h n0, isUnram_iff.1 (isUnram_of_isInertAt hw) w h, pow_one, map_mul, hv, h1, ← WithZero.exp_add] at h4
    rw [h4]; congr 1; ring
  have h5 : (absE F E x : ℝ) = (qV F v : ℝ) ^ ((-(2 * ordL y.1) : ℤ) : ℝ) := by
    rw [GlobalTheory.InertChars.eq_ideleAt_of_at x hx, GlobalTheory.Doubling.absE_ideleAt, GlobalTheory.Doubling.absEv_apply, coe_nnnorm,
      FinitePlace.norm_def, h2, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, Real.rpow_intCast]
    exact NNReal.coe_zpow _ _
  rw [h5, ← Complex.cpow_mul_ofReal_nonneg (Nat.cast_nonneg _), secVal, MonoidHom.one_apply, Units.val_one, one_mul]
  push_cast
  congr 1; ring

/- English proof (translation)
Establish `hd : ((1 : E) • Y.Jᵀ).det ≠ 0` using `by rw [one_smul, Matrix.det_transpose]; exact (Vac.herm_det hY).ne_zero`. Take `⟨a, h1, h2⟩` from `exists_frame_antiJ hσ (J := (1 : E) • Y.Jᵀ) ⟨fun i j => by simp [hY.herm], hd⟩ hY.lat.fg hY.lat.span_eq_top hw hc (PositivityTheory.ThKG.Loc.Iwa.selfDual_of hd hY.lat (fun y hy x hx => SelfDual.inclR_mem_intLoc v (by`. Rewrite using `[PositivityTheory.ThKG.Loc.Iwa.hE_smul, one_mul]`. Conclude with `⟨⟨_, (hY.dual y).1 hy x hx⟩, rfl⟩)) (s := 1)`. Use the proof step `((Ideal.ne_top_iff_one _).1 v.isPrime.ne_top) fun y hy => by`.

Simplify using `only [OneMemClass.coe_one, map_one, one_smul]`. Use `(hY.dual y).2 fun x hx => ?_` and prove the remaining obligations. Take `⟨o, ho⟩` from `hy x hx`. Rewrite `ho` using `[PositivityTheory.ThKG.Loc.Iwa.hE_smul, one_mul]`. Rewrite using `[← ho]`.

Conclude with `o.isIntegral_coe)`. Use `⟨a, h1, Eq.trans ?_ h2⟩` and prove the remaining obligations. Use `congr 2`. Conclude with `Matrix.ext fun i j => (piE_incl h _).trans (by simp)`.
-/
theorem frame {B : Base F E} {r s : ℕ} (hσ : IsCMExt F E σ) (hY : Y.IsHerm σ B r s) (hw : IsInertAt F E v w) {h : w.under (𝓞 F) = v}
    {c : w.adicCompletion E →+* w.adicCompletion E} (hc : IsConjAt σ h c) :
    ∃ a, IsFrameAt w Y.L a ∧ cT c a.1 * ((incM F Y.J).map (piE h))ᵀ * a.1 = antiJ _ n := by
  have hd : ((1 : E) • Y.Jᵀ).det ≠ 0 := by rw [one_smul, Matrix.det_transpose]; exact (Vac.herm_det hY).ne_zero
  obtain ⟨a, h1, h2⟩ := exists_frame_antiJ hσ (J := (1 : E) • Y.Jᵀ) ⟨fun i j => by simp [hY.herm], hd⟩ hY.lat.fg hY.lat.span_eq_top hw hc
    (PositivityTheory.ThKG.Loc.Iwa.selfDual_of hd hY.lat (fun y hy x hx => SelfDual.inclR_mem_intLoc v (by
      rw [PositivityTheory.ThKG.Loc.Iwa.hE_smul, one_mul]; exact ⟨⟨_, (hY.dual y).1 hy x hx⟩, rfl⟩)) (s := 1)
      ((Ideal.ne_top_iff_one _).1 v.isPrime.ne_top) fun y hy => by
        simp only [OneMemClass.coe_one, map_one, one_smul]
        refine (hY.dual y).2 fun x hx => ?_
        obtain ⟨o, ho⟩ := hy x hx
        rw [PositivityTheory.ThKG.Loc.Iwa.hE_smul, one_mul] at ho
        rw [← ho]; exact o.isIntegral_coe)
  refine ⟨a, h1, Eq.trans ?_ h2⟩
  congr 2
  exact Matrix.ext fun i j => (piE_incl h _).trans (by simp)

/- English proof (translation)
The claim follows from `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
theorem one_map {ι R : Type} [DecidableEq ι] [CommRing R] (φ : AE F E →+* R) : (1 : Matrix ι ι (AE F E)).map φ = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

/- English proof (translation)
The claim follows from `Matrix.map_zero _ (map_zero _)`.
-/
theorem zero_map {R : Type} [CommRing R] (φ : AE F E →+* R) : (0 : Matrix (Fin n) (Fin n) (AE F E)).map φ = 0 :=
  Matrix.map_zero _ (map_zero _)

/- English proof (translation)
Rewrite using `[dg, diagCols, Matrix.fromRows_map, one_map]`. Both sides reduce to the same expression.
-/
theorem diag_map {R : Type} [CommRing R] (φ : AE F E →+* R) :
    (dg n (AE F E)).map φ = dg n R := by
  rw [dg, diagCols, Matrix.fromRows_map, one_map]; rfl

variable (hw : IsInertAt F E v w) {h : w.under (𝓞 F) = v} {c : w.adicCompletion E →+* w.adicCompletion E} (hc : IsConjAt σ h c)
  {a : GL (Fin n) (w.adicCompletion E)} (hH : cT c a.1 * ((incM F Y.J).map (piE h))ᵀ * a.1 = antiJ _ n)

def lift1 : GU c n →* UA σ Y.J := liftW hw hc a.mul_inv a.inv_mul hH

def lift2 : GD c n →* G2 σ Y := liftW hw hc (dA_dB a) (dB_dA a) (by
  rw [← hH, ← dA_gram, dbl, dbl, Matrix.fromBlocks_map, zero_map, Matrix.map_neg _ (map_neg _)])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_lift1 (x : GU c n) : mat (lift1 hw hc hH x) = up hw h _ (a.1 * x.1.1 * (a⁻¹).1) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_lift2 (x : GD c n) : mat2 (lift2 hw hc hH x) = up hw h _ (dA a * x.1.1 * dB a) := rfl

/- English proof (translation)
Rewrite using `[IsEmb, mat_lift1, mat_lift2, show mat (1 : UA σ Y.J) = 1 from rfl]`. Use `extW hw h ?_ ?_` and prove the remaining obligations. Rewrite using `[up_pi, Matrix.fromBlocks_map, zero_map, one_map, up_pi]`. Conclude with `dA_blk a _`. Rewrite using `[up_aw, Matrix.fromBlocks_map, zero_map, one_map, up_aw, Matrix.fromBlocks_one]`.
-/
theorem lift_emb (x : GU c n) : IsEmb (lift1 hw hc hH x) 1 (lift2 hw hc hH (io1 c n x)) := by
  rw [IsEmb, mat_lift1, mat_lift2, show mat (1 : UA σ Y.J) = 1 from rfl]
  refine extW hw h ?_ ?_
  · rw [up_pi, Matrix.fromBlocks_map, zero_map, one_map, up_pi]
    exact dA_blk a _
  · rw [up_aw, Matrix.fromBlocks_map, zero_map, one_map, up_aw, Matrix.fromBlocks_one]

/- English proof (translation)
Establish `key : ∀ x ∈ KD c n, At (evFin F v) (mat2 (lift2 hw hc hH x) - 1) ∧ ∀ i j : Fin n → Fin n ⊕ Fin n, i ∈ ({.inl, .inr} : Set _) → j ∈ ({.inl, .inr} : Set _) → ∀ z ∈ latW Y v, (mat2 (lift2 hw hc hH x) - 1).submatrix i j *ᵥ z ∈ latW Y v` using `fun x hx => by`. Rewrite using `[mat_lift2]`. Use `⟨up_at hw h _, fun i j hi hj => (stab_iff hw h ha _).2 fun l m => ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.submatrix_map, Matrix.map_sub _ (map_sub _), one_map, up_pi, dA_sub a _ hi hj]`. Conclude with `sub_mem ((mem_GLint_iff.1 (show x.1 ∈ GLint _ (intL _) from hx.2)).1 _ _) (one_int _ _)`.

Use `mem_K (v := v) hK ?_` and prove the remaining obligations. Introduce and unpack `x (rfl | rfl)`. Conclude with `key k hk`. Rewrite using `[← map_inv]`. Conclude with `key _ (inv_mem hk)`.
-/
theorem lift_mem (ha : IsFrameAt w Y.L a) {B : Base F E} {K : Subgroup (G2 σ Y)} (hK : IsStab2 B K) {k : GD c n}
    (hk : k ∈ KD c n) : lift2 hw hc hH k ∈ K := by
  have key : ∀ x ∈ KD c n, At (evFin F v) (mat2 (lift2 hw hc hH x) - 1) ∧ ∀ i j : Fin n → Fin n ⊕ Fin n,
      i ∈ ({.inl, .inr} : Set _) → j ∈ ({.inl, .inr} : Set _) → ∀ z ∈ latW Y v,
        (mat2 (lift2 hw hc hH x) - 1).submatrix i j *ᵥ z ∈ latW Y v := fun x hx => by
    rw [mat_lift2]
    refine ⟨up_at hw h _, fun i j hi hj => (stab_iff hw h ha _).2 fun l m => ?_⟩
    rw [← Matrix.submatrix_map, Matrix.map_sub _ (map_sub _), one_map, up_pi, dA_sub a _ hi hj]
    exact sub_mem ((mem_GLint_iff.1 (show x.1 ∈ GLint _ (intL _) from hx.2)).1 _ _) (one_int _ _)
  refine mem_K (v := v) hK ?_
  rintro x (rfl | rfl)
  · exact key k hk
  · rw [← map_inv]; exact key _ (inv_mem hk)

/- English proof (translation)
Take `⟨t, ht⟩ : ∃ t : GL (Fin n) (AE F E), t.1 = up hw h _ (a.1 * leviMat finSumFinEquiv p.1.1.1 * (a⁻¹).1)` from `⟨Units.map ((up hw h _).comp (conjM a.mul_inv a.inv_mul)) (leviOf finSumFinEquiv _ p), rfl⟩`. Use `⟨t, ?_, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `mat2 (lift2 hw hc hH p) * dg n (AE F E) = dg n (AE F E) * t.1`. Rewrite using `[mat_lift2, ht]`. Use `extW hw h ?_ ?_` and prove the remaining obligations.

Rewrite using `[Matrix.map_mul, Matrix.map_mul, diag_map, up_pi, up_pi]`. Conclude with `dA_par a (GlobalTheory.Doubling.mem_siegelOf.1 p.2)`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, up_aw, up_aw, Matrix.one_mul, Matrix.mul_one]`. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, ht, up, MonoidHom.comp_apply, det_liftM]`. Rewrite using `[show ∀ y, liftE E v y - 1 = tensAt E v (y - 1) from fun y => add_sub_cancel_left _ _]`.

Conclude with `at_tensAt v _`. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det, RingHom.mapMatrix_apply, ht, up_pi, Matrix.det_units_conj]`. Both sides reduce to the same expression.
-/
theorem lift_par (p : PD c n) : ∃ t, IsPar (lift2 hw hc hH p) t ∧ At (evFin F v) ((Matrix.GeneralLinearGroup.det t).1 - 1) ∧
    piE h (Matrix.GeneralLinearGroup.det t).1 = aD c n p := by
  obtain ⟨t, ht⟩ : ∃ t : GL (Fin n) (AE F E), t.1 = up hw h _ (a.1 * leviMat finSumFinEquiv p.1.1.1 * (a⁻¹).1) :=
    ⟨Units.map ((up hw h _).comp (conjM a.mul_inv a.inv_mul)) (leviOf finSumFinEquiv _ p), rfl⟩
  refine ⟨t, ?_, ?_, ?_⟩
  · change mat2 (lift2 hw hc hH p) * dg n (AE F E) = dg n (AE F E) * t.1
    rw [mat_lift2, ht]
    refine extW hw h ?_ ?_
    · rw [Matrix.map_mul, Matrix.map_mul, diag_map, up_pi, up_pi]
      exact dA_par a (GlobalTheory.Doubling.mem_siegelOf.1 p.2)
    · rw [Matrix.map_mul, Matrix.map_mul, up_aw, up_aw, Matrix.one_mul, Matrix.mul_one]
  · rw [Matrix.GeneralLinearGroup.val_det_apply, ht, up, MonoidHom.comp_apply, det_liftM]
    rw [show ∀ y, liftE E v y - 1 = tensAt E v (y - 1) from fun y => add_sub_cancel_left _ _]
    exact at_tensAt v _
  · rw [Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det, RingHom.mapMatrix_apply, ht, up_pi, Matrix.det_units_conj]
    rfl

/- English proof (translation)
The claim follows from `(Subgroup.closure_le (USub σ Y v)).2 (fun _ h => h) hg`.
-/
theorem mem_locGrp {g : UA σ Y.J} (hg : g ∈ locGrp σ Y v) : At (evFin F v) (g.1.1 - 1) :=
  (Subgroup.closure_le (USub σ Y v)).2 (fun _ h => h) hg

/- English proof (translation)
The claim follows from `Subgroup.subset_closure (by change At (evFin F v) (mat (lift1 hw hc hH x) - 1) rw [mat_lift1] exact up_at hw h _)`.
-/
theorem inert_lift_mem_local_group (x : GU c n) : lift1 hw hc hH x ∈ locGrp σ Y v := Subgroup.subset_closure (by
  change At (evFin F v) (mat (lift1 hw hc hH x) - 1)
  rw [mat_lift1]
  exact up_at hw h _)

def chartW [IsTopologicalRing (AE F E)] : locGrp σ Y v ≃ₜ* GU c n where
  toFun g := downW hc a.mul_inv a.inv_mul hH g.1
  invFun x := ⟨lift1 hw hc hH x, inert_lift_mem_local_group hw hc hH x⟩
  left_inv g := Subtype.ext (lift_down hw hc a.mul_inv a.inv_mul hH (g := g.1) (mem_locGrp g.2))
  right_inv := down_lift hw hc a.mul_inv a.inv_mul hH
  map_mul' g g' := map_mul (downW hc a.mul_inv a.inv_mul hH) g.1 g'.1
  continuous_toFun := (continuous_downW hw hc a.mul_inv a.inv_mul hH).comp continuous_subtype_val
  continuous_invFun := (continuous_liftW hw hc a.mul_inv a.inv_mul hH).subtype_mk (inert_lift_mem_local_group hw hc hH)

include hw in
/- English proof (translation)
Establish `hat : ∀ z ∈ latW Y v, At (evFin F v) z` using `fun z hz => ((mem_latW_iff hw h Y z).1 hz).1`. Establish `e : ∀ x : GU c n, x ∈ KU c n ↔ (∀ i j, x.1.1 i j ∈ Ov E w) ∧ ∀ i j, (x⁻¹).1.1 i j ∈ Ov E w` using `fun x => ⟨fun h => mem_GLint_iff.1 (show x.1 ∈ GLint _ (intL _) from h.2), fun h => ⟨x.2, (mem_GLint_iff (O := intL _)).2 h⟩⟩`. Rewrite using `[e, ← map_inv]`. Use `Iff.trans (and_congr ((stab_latW hat).trans (stab_iff hw h ha (mat g))) ((stab_latW hat).trans (stab_iff hw h ha (mat g⁻¹)))).symm ?_` and prove the remaining obligations. Simplify using `only [IntAt, imp_and, forall_and]`.
-/
theorem down_mem (ha : IsFrameAt w Y.L a) (g : UA σ Y.J) : downW hc a.mul_inv a.inv_mul hH g ∈ KU c n ↔ IntAt v g := by
  have hat : ∀ z ∈ latW Y v, At (evFin F v) z := fun z hz => ((mem_latW_iff hw h Y z).1 hz).1
  have e : ∀ x : GU c n, x ∈ KU c n ↔ (∀ i j, x.1.1 i j ∈ Ov E w) ∧ ∀ i j, (x⁻¹).1.1 i j ∈ Ov E w := fun x =>
    ⟨fun h => mem_GLint_iff.1 (show x.1 ∈ GLint _ (intL _) from h.2), fun h => ⟨x.2, (mem_GLint_iff (O := intL _)).2 h⟩⟩
  rw [e, ← map_inv]
  refine Iff.trans (and_congr ((stab_latW hat).trans (stab_iff hw h ha (mat g))) ((stab_latW hat).trans
    (stab_iff hw h ha (mat g⁻¹)))).symm ?_
  simp only [IntAt, imp_and, forall_and]

/- English proof (translation)
Introduce and unpack `F E _ _ _ _ _ σ B n Y r s hB hY χ - hr K e hK he v ⟨w, hw⟩ hu μ hμ hμ1 z f hz hf`. Establish `h` using `(under_eq_iff hw w).2 rfl`. Take `⟨c, hc, -⟩` from `existsUnique_isConjAt σ hw h`. Take `⟨ϖ, hU⟩` from `exists_isUnramInv hB.cm hw hc`. Establish `hϖ : ϖ ≠ 0` using `fun h0 => WithZero.zero_ne_coe (by simpa only [h0, map_zero] using hU.2.2.2.1)`.

Take `⟨a, ha, hH⟩` from `frame hB.cm hY hw hc`. Establish `sph : IsSphSec c (qV F v) n 1 z fun x => f (lift2 hw hc hH x)` using `fun p k hk => by`. Take `⟨t, h1, h2, h3⟩` from `lift_par hw hc hH p`. Use `beta_reduce`. Rewrite using `[map_mul, hf _ t h1 (up_at hw h _) _ (lift_mem hw hc hH ha hK hk) (up_at hw h _), abs_at hB.cm hw hc hU.2.1 h2 h3, GlobalTheory.InertChars.eq_ideleAt_of_at _ h2, ideleAt_eq_locIdele_of_isInertAt h hw, chi_at hw hr (hu w h), Circle.coe_one, one_mul]`.

Use `GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)` as an intermediate fact. Establish `: BorelSpace (UA σ Y.J)` using `⟨rfl⟩`. Set `_ : MeasurableSpace (GU c n)` to `borel _`. Establish `: BorelSpace (GU c n)` using `⟨rfl⟩`. Set `φ` to `chartW hw hc hH`.

Set `m` to `φ.toHomeomorph.toMeasurableEquiv`. Establish `: (μ.map m).IsHaarMeasure` using `φ.isHaarMeasure_map μ`. Take `⟨i1, i2⟩` from `triv (ϖ := Units.mk0 ϖ hϖ) hU (μ.map m) (by`. Rewrite using `[m.map_apply, ← hμ1]`. Conclude with `congrArg μ (Set.ext fun g => down_mem hw hc hH ha g.1)) hz sph`.

Establish `e2 : ∀ u : locGrp σ Y v, lift2 hw hc hH (io1 c n (m u)) = e (u.1, 1)` using `fun u => by`. Use `Subtype.ext (Units.ext ((lift_emb hw hc hH _).trans (Eq.trans ?_ (he _ _).symm)))` and prove the remaining obligations. Rewrite using `[show lift1 hw hc hH (m u) = u.1 from congrArg Subtype.val (φ.left_inv u)]`. Rewrite `i1` using `[integrable_map_equiv, Function.comp_def]`. Rewrite `i2` using `[integral_map_equiv]`.

Simplify using `only [e2] at i1 i2`. Use `⟨i1, ?_⟩` and prove the remaining obligations. Rewrite using `[locD, if_neg fun ⟨τ⟩ => not_isSplit_of_isInertAt hw (SplitChart.isSplit_of_algHom hB.cm τ)]`. Use `i2.trans (Finset.prod_congr rfl fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[Lv, show Formalism.L2.Host.aboveF (L := E) F v = {w} by ext u; simp [mem_aboveF, under_eq_iff hw], Finset.prod_singleton, locL, charFam_of_unrAt (hu w h), eulerFac_singleton, val, locChar, MonoidHom.comp_apply, MonoidHom.comp_apply, chi_at hw hr (hu w h), map_one, Units.val_one, …`.

Both sides reduce to the same expression.
-/
theorem main : LocUnrInert := by
  rintro F E _ _ _ _ _ σ B n Y r s hB hY χ - hr K e hK he v ⟨w, hw⟩ hu μ hμ hμ1 z f hz hf
  have h := (under_eq_iff hw w).2 rfl
  obtain ⟨c, hc, -⟩ := existsUnique_isConjAt σ hw h
  obtain ⟨ϖ, hU⟩ := exists_isUnramInv hB.cm hw hc
  have hϖ : ϖ ≠ 0 := fun h0 => WithZero.zero_ne_coe (by simpa only [h0, map_zero] using hU.2.2.2.1)
  obtain ⟨a, ha, hH⟩ := frame hB.cm hY hw hc
  have sph : IsSphSec c (qV F v) n 1 z fun x => f (lift2 hw hc hH x) := fun p k hk => by
    obtain ⟨t, h1, h2, h3⟩ := lift_par hw hc hH p
    beta_reduce
    rw [map_mul, hf _ t h1 (up_at hw h _) _ (lift_mem hw hc hH ha hK hk) (up_at hw h _), abs_at hB.cm hw hc hU.2.1 h2 h3,
      GlobalTheory.InertChars.eq_ideleAt_of_at _ h2, ideleAt_eq_locIdele_of_isInertAt h hw, chi_at hw hr (hu w h), Circle.coe_one, one_mul]
  have := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  have : BorelSpace (UA σ Y.J) := ⟨rfl⟩
  let _ : MeasurableSpace (GU c n) := borel _
  have : BorelSpace (GU c n) := ⟨rfl⟩
  let φ := chartW hw hc hH
  let m := φ.toHomeomorph.toMeasurableEquiv
  have : (μ.map m).IsHaarMeasure := φ.isHaarMeasure_map μ
  obtain ⟨i1, i2⟩ := triv (ϖ := Units.mk0 ϖ hϖ) hU (μ.map m) (by
    rw [m.map_apply, ← hμ1]
    exact congrArg μ (Set.ext fun g => down_mem hw hc hH ha g.1)) hz sph
  have e2 : ∀ u : locGrp σ Y v, lift2 hw hc hH (io1 c n (m u)) = e (u.1, 1) := fun u => by
    refine Subtype.ext (Units.ext ((lift_emb hw hc hH _).trans (Eq.trans ?_ (he _ _).symm)))
    rw [show lift1 hw hc hH (m u) = u.1 from congrArg Subtype.val (φ.left_inv u)]
  rw [integrable_map_equiv, Function.comp_def] at i1
  rw [integral_map_equiv] at i2
  simp only [e2] at i1 i2
  refine ⟨i1, ?_⟩
  rw [locD, if_neg fun ⟨τ⟩ => not_isSplit_of_isInertAt hw (SplitChart.isSplit_of_algHom hB.cm τ)]
  refine i2.trans (Finset.prod_congr rfl fun i _ => ?_)
  rw [Lv, show Formalism.L2.Host.aboveF (L := E) F v = {w} by ext u; simp [mem_aboveF, under_eq_iff hw], Finset.prod_singleton, locL,
    charFam_of_unrAt (hu w h), eulerFac_singleton, val, locChar, MonoidHom.comp_apply, MonoidHom.comp_apply, chi_at hw hr (hu w h),
    map_one, Units.val_one, one_mul, npow, absNorm_eq hB.cm.2.2.1 hw]
  rfl

end GlobalTheory.ThK.Dbl.Inert

/- English proof (translation)
The claim follows from `GlobalTheory.ThK.Dbl.Inert.main`.
-/
theorem GlobalTheory.ThK.Dbl.locUnrInert : GlobalTheory.ThK.Dbl.LocUnrInert := GlobalTheory.ThK.Dbl.Inert.main

end
