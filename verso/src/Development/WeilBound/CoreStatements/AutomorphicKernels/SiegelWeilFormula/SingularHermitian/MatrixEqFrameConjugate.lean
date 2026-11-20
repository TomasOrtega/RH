import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.DZTranspose

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KSing

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

set_option linter.unusedSectionVars false

namespace UnitaryGroupBasics

/- English proof (translation)
Unfold `incM`. Conclude with `Matrix.map_mul`.
-/
theorem incM_mul {p q r : Type} [Fintype q] (X : Matrix p q E) (Y : Matrix q r E) :
    incM F (X * Y) = incM F X * incM F Y := by
  unfold incM; exact Matrix.map_mul

/- English proof (translation)
Unfold `incM`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
theorem incM_one {p : Type} [Fintype p] [DecidableEq p] : incM F (1 : Matrix p p E) = 1 := by
  unfold incM; exact Matrix.map_one _ (map_zero _) (map_one _)

/- English proof (translation)
Rewrite using `[← incM_mul, Units.mul_inv, incM_one]`.
-/
theorem incM_b (d : SD σ) : incM F d.b.1 * incM F (d.b⁻¹).1 = 1 := by
  rw [← incM_mul, Units.mul_inv, incM_one]

/- English proof (translation)
Rewrite using `[← incM_mul, Units.inv_mul, incM_one]`.
-/
theorem incM_b' (d : SD σ) : incM F (d.b⁻¹).1 * incM F d.b.1 = 1 := by
  rw [← incM_mul, Units.inv_mul, incM_one]

/- English proof (translation)
Unfold `inFrame`. Establish `e : mat2 (x * y) = mat2 x * mat2 y` using `rfl`. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[incM_b, Matrix.mul_one]`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by simp only [Matrix.mul_assoc]`.
-/
theorem inFrame_mul (d : SD σ) (x y : d.G) : inFrame d.b (x * y) = inFrame d.b x * inFrame d.b y := by
  unfold inFrame
  have e : mat2 (x * y) = mat2 x * mat2 y := rfl
  rw [e]
  calc incM F (d.b⁻¹).1 * (mat2 x * mat2 y) * incM F d.b.1
      = incM F (d.b⁻¹).1 * mat2 x * (incM F d.b.1 * incM F (d.b⁻¹).1) * mat2 y * incM F d.b.1 := by
        rw [incM_b, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

/- English proof (translation)
Unfold `inFrame`. Establish `e : mat2 (1 : d.G) = 1` using `rfl`. Rewrite using `[e, Matrix.mul_one, incM_b']`.
-/
theorem inFrame_one (d : SD σ) : inFrame d.b (1 : d.G) = 1 := by
  unfold inFrame
  have e : mat2 (1 : d.G) = 1 := rfl
  rw [e, Matrix.mul_one, incM_b']

/- English proof (translation)
Unfold `inFrame`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[incM_b, Matrix.one_mul, Matrix.mul_one]`. Use `_ = _ := by simp only [Matrix.mul_assoc]`.
-/
theorem matrix_eq_frame_conjugate (d : SD σ) (x : d.G) : mat2 x = incM F d.b.1 * inFrame d.b x * incM F (d.b⁻¹).1 := by
  unfold inFrame
  calc mat2 x = (incM F d.b.1 * incM F (d.b⁻¹).1) * mat2 x * (incM F d.b.1 * incM F (d.b⁻¹).1) := by
        rw [incM_b, Matrix.one_mul, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

/- English proof (translation)
Establish `e : mat2 x = mat2 y` using `by rw [matrix_eq_frame_conjugate d x, matrix_eq_frame_conjugate d y, h]`. Conclude with `Subtype.ext (Units.ext e)`.
-/
theorem inFrame_inj (d : SD σ) {x y : d.G} (h : inFrame d.b x = inFrame d.b y) : x = y := by
  have e : mat2 x = mat2 y := by rw [matrix_eq_frame_conjugate d x, matrix_eq_frame_conjugate d y, h]
  exact Subtype.ext (Units.ext e)

/- English proof (translation)
Unfold `SD.cw`. Conclude with `Matrix.map_mul`.
-/
theorem cw_mul (d : SD σ) (w : InfinitePlace F) {p q r : Type} [Fintype q] (X : Matrix p q (AE F E))
    (Y : Matrix q r (AE F E)) : d.cw w (X * Y) = d.cw w X * d.cw w Y := by
  unfold SD.cw; exact Matrix.map_mul

/- English proof (translation)
Unfold `SD.cw`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
theorem cw_one (d : SD σ) (w : InfinitePlace F) {p : Type} [Fintype p] [DecidableEq p] :
    d.cw w (1 : Matrix p p (AE F E)) = 1 := by
  unfold SD.cw; exact Matrix.map_one _ (map_zero _) (map_one _)

/- English proof (translation)
The claim follows from `Prod.ext (show (0 : Ainf F) * 0 = 0 from mul_zero _) (show (1 : Af F) * 1 = 1 from mul_one _)`.
-/
theorem finOne_idem : finOne F * finOne F = finOne F :=
  Prod.ext (show (0 : Ainf F) * 0 = 0 from mul_zero _) (show (1 : Af F) * 1 = 1 from mul_one _)

/- English proof (translation)
Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, smul_smul, finOne_idem]`.
-/
theorem fin_mul {p q r : Type} [Fintype q] (X : Matrix p q (AE F E)) (Y : Matrix q r (AE F E)) :
    finOne F • (X * Y) = (finOne F • X) * (finOne F • Y) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, finOne_idem]

/- English proof (translation)
Apply `inFrame_inj d` to reduce the goal to its premises. Rewrite using `[inFrame_mul, inFrame_mul]`. Apply `Place.cw_ext d` to reduce the goal to its premises. Introduce `w'`. Rewrite using `[cw_mul, cw_mul]`.

Distinguish the cases in `h : w' = w`. Substitute `h` using the available equality. Rewrite using `[hx, Matrix.one_mul, Matrix.mul_one]`. Rewrite using `[hu w' h, Matrix.one_mul, Matrix.mul_one]`. Rewrite using `[fin_mul, fin_mul, hf, ← fin_mul, ← fin_mul, Matrix.mul_one, Matrix.one_mul]`.
-/
theorem comm_of (d : SD σ) (w : InfinitePlace F) (x u : d.G) (hx : d.cw w (inFrame d.b x) = 1)
    (hu : ∀ w', w' ≠ w → d.cw w' (inFrame d.b u) = 1) (hf : finOne F • inFrame d.b u = finOne F • 1) :
    x * u = u * x := by
  apply inFrame_inj d
  rw [inFrame_mul, inFrame_mul]
  apply Place.cw_ext d
  · intro w'
    rw [cw_mul, cw_mul]
    by_cases h : w' = w
    · subst h; rw [hx, Matrix.one_mul, Matrix.mul_one]
    · rw [hu w' h, Matrix.one_mul, Matrix.mul_one]
  · rw [fin_mul, fin_mul, hf, ← fin_mul, ← fin_mul, Matrix.mul_one, Matrix.one_mul]

/- English proof (translation)
Simplify using `[cA, inclR, Algebra.TensorProduct.map_tmul]`.
-/
theorem cA_inclR (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR, Algebra.TensorProduct.map_tmul]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, map_sum, map_mul]`.
-/
theorem mapc_mul {p q r : Type} [Fintype q] (X : Matrix p q (AE F E)) (Y : Matrix q r (AE F E)) :
    (X * Y).map (cA σ) = X.map (cA σ) * Y.map (cA σ) := by
  ext i j; simp [Matrix.mul_apply, map_sum, map_mul]

end UnitaryGroupBasics

namespace UnitaryGroupBasics

variable {n : ℕ}

/- English proof (translation)
Introduce `h0`. Establish `e` using `congrArg Matrix.det hg`. Rewrite `e` using `[Matrix.det_mul, Matrix.det_mul, h0, mul_zero]`. Establish `hJ : JJ n * JJ n = -1`. Simplify using `[JJ, Matrix.fromBlocks_multiply]`.

Rewrite using `[← Matrix.fromBlocks_one, Matrix.fromBlocks_neg, neg_zero]`. Establish `h2` using `congrArg Matrix.det hJ`. Rewrite `h2` using `[Matrix.det_mul, ← e, zero_mul, Matrix.det_neg]`. Simplify using `at h2`.
-/
theorem det_ne_of_inG {g : M2 n} (hg : InG g) : g.det ≠ 0 := by
  intro h0
  have e := congrArg Matrix.det hg
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at e
  have hJ : JJ n * JJ n = -1 := by
    simp [JJ, Matrix.fromBlocks_multiply]
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg, neg_zero]
  have h2 := congrArg Matrix.det hJ
  rw [Matrix.det_mul, ← e, zero_mul, Matrix.det_neg] at h2
  simp at h2

def mkGR (g : M2 n) (hg : InG g) : GR n := ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero g (det_ne_of_inG hg), hg⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mR_mkGR (g : M2 n) (hg : InG g) : mR (mkGR g hg) = g := rfl

/- English proof (translation)
Unfold `herm`. Use `fun_prop`.
-/
theorem continuous_herm' : Continuous (herm : (Fin n → Fin n → ℝ) → Matrix (Fin n) (Fin n) ℂ) := by
  unfold herm
  fun_prop

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.conjTranspose_apply]`. Apply the tactic sequence `apply Complex.ext <;> simp [herm] <;> ring`.
-/
theorem herm_conjTranspose' (x : Fin n → Fin n → ℝ) : (herm x)ᴴ = herm x := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  apply Complex.ext <;> simp [herm] <;> ring

/- English proof (translation)
Simplify using `[nU, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]`.
-/
theorem nU_mul_neg (H : Matrix (Fin n) (Fin n) ℂ) : nU H * nU (-H) = 1 := by
  simp [nU, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

/- English proof (translation)
Establish `hH : Continuous fun x : Fin n → Fin n → ℝ => nU (herm x)` using `Continuous.matrix_fromBlocks continuous_const continuous_herm' continuous_const continuous_const`. Establish `hHn : Continuous fun x : Fin n → Fin n → ℝ => nU (-herm x)` using `Continuous.matrix_fromBlocks continuous_const continuous_herm'.neg continuous_const continuous_const`. Use `continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)` and prove the remaining obligations. Conclude with `(hH.congr fun x => (hnr x).symm : Continuous fun x => mR (nr x))`. Use `hHn.congr fun x => ?_` and prove the remaining obligations.

Use `(Units.inv_eq_of_mul_eq_one_right ?_).symm` and prove the remaining obligations. Establish `e : ((nr x : GL (Fin n ⊕ Fin n) ℂ) : M2 n) = nU (herm x)` using `hnr x`. Use `show ((nr x : GL (Fin n ⊕ Fin n) ℂ) : M2 n) * nU (-herm x) = 1`. Rewrite using `[e]`. Conclude with `nU_mul_neg _`.
-/
theorem continuous_nr (nr : (Fin n → Fin n → ℝ) → GR n) (hnr : ∀ x, mR (nr x) = nU (herm x)) : Continuous nr := by
  have hH : Continuous fun x : Fin n → Fin n → ℝ => nU (herm x) :=
    Continuous.matrix_fromBlocks continuous_const continuous_herm' continuous_const continuous_const
  have hHn : Continuous fun x : Fin n → Fin n → ℝ => nU (-herm x) :=
    Continuous.matrix_fromBlocks continuous_const continuous_herm'.neg continuous_const continuous_const
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · exact (hH.congr fun x => (hnr x).symm : Continuous fun x => mR (nr x))
  · refine hHn.congr fun x => ?_
    refine (Units.inv_eq_of_mul_eq_one_right ?_).symm
    have e : ((nr x : GL (Fin n ⊕ Fin n) ℂ) : M2 n) = nU (herm x) := hnr x
    show ((nr x : GL (Fin n ⊕ Fin n) ℂ) : M2 n) * nU (-herm x) = 1
    rw [e]; exact nU_mul_neg _

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Unfold `SD.cw`. Conclude with `Matrix.transpose_map.symm`.
-/
theorem cw_transpose (d : SD σ) (w : InfinitePlace F) {p q : Type} (X : Matrix p q (AE F E)) :
    d.cw w Xᵀ = (d.cw w X)ᵀ := by
  unfold SD.cw; exact Matrix.transpose_map.symm

/- English proof (translation)
Rewrite using `[← R.hε, incM_mul, incM_mul]`. Establish `e1 : incM F d.b.1ᵀ = (incM F d.b.1)ᵀ` using `by unfold incM; exact Matrix.transpose_map`. Establish `e2 : incM F (dbl d.Y.J) = dbl (incM F d.Y.J)`. Apply the tactic sequence `ext i j; rcases i with i | i <;> rcases j with j | j <;> simp [incM, dbl]`. Establish `e3 : incM F (d.b.1.map σ) = (incM F d.b.1).map (cA σ)`.

Use extensionality with `i j`. Simplify using `only [incM, Matrix.map_apply, cA_inclR]`. Rewrite using `[e1, e2, e3]`.
-/
theorem frame_adelic (d : SD σ) (R : RD d) :
    (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ) =
      incM F (Matrix.fromBlocks 0 1 (((R.ε : ℤ) : E) • 1) 0 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) := by
  rw [← R.hε, incM_mul, incM_mul]
  have e1 : incM F d.b.1ᵀ = (incM F d.b.1)ᵀ := by unfold incM; exact Matrix.transpose_map
  have e2 : incM F (dbl d.Y.J) = dbl (incM F d.Y.J) := by
    ext i j; rcases i with i | i <;> rcases j with j | j <;> simp [incM, dbl]
  have e3 : incM F (d.b.1.map σ) = (incM F d.b.1).map (cA σ) := by
    ext i j; simp only [incM, Matrix.map_apply, cA_inclR]
  rw [e1, e2, e3]

/- English proof (translation)
Establish `hG : (mat2 x)ᵀ * dbl (incM F d.Y.J) * (mat2 x).map (cA σ) = dbl (incM F d.Y.J)` using `x.2`. Establish `h1 : (incM F (d.b⁻¹).1)ᵀ * (incM F d.b.1)ᵀ = 1`. Rewrite using `[← Matrix.transpose_mul, incM_b, Matrix.transpose_one]`. Establish `h2 : (incM F d.b.1).map (cA σ) * (incM F (d.b⁻¹).1).map (cA σ) = 1`. Rewrite using `[← mapc_mul, incM_b, Matrix.map_one _ (map_zero _) (map_one _)]`.

Unfold `inFrame`. Rewrite using `[Matrix.transpose_mul, Matrix.transpose_mul, mapc_mul, mapc_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h1, h2, Matrix.mul_one, Matrix.mul_one]`. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = _ := by rw [hG]`.
-/
theorem form_adelic (d : SD σ) (x : d.G) :
    (inFrame d.b x)ᵀ * ((incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ)) *
        (inFrame d.b x).map (cA σ) = (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ) := by
  have hG : (mat2 x)ᵀ * dbl (incM F d.Y.J) * (mat2 x).map (cA σ) = dbl (incM F d.Y.J) := x.2
  have h1 : (incM F (d.b⁻¹).1)ᵀ * (incM F d.b.1)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, incM_b, Matrix.transpose_one]
  have h2 : (incM F d.b.1).map (cA σ) * (incM F (d.b⁻¹).1).map (cA σ) = 1 := by
    rw [← mapc_mul, incM_b, Matrix.map_one _ (map_zero _) (map_one _)]
  unfold inFrame
  rw [Matrix.transpose_mul, Matrix.transpose_mul, mapc_mul, mapc_mul]
  calc _ = (incM F d.b.1)ᵀ * (mat2 x)ᵀ * ((incM F (d.b⁻¹).1)ᵀ * (incM F d.b.1)ᵀ) * dbl (incM F d.Y.J) *
          ((incM F d.b.1).map (cA σ) * (incM F (d.b⁻¹).1).map (cA σ)) * (mat2 x).map (cA σ) *
          (incM F d.b.1).map (cA σ) := by simp only [Matrix.mul_assoc]
    _ = (incM F d.b.1)ᵀ * ((mat2 x)ᵀ * dbl (incM F d.Y.J) * (mat2 x).map (cA σ)) * (incM F d.b.1).map (cA σ) := by
          rw [h1, h2, Matrix.mul_one, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [hG]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;>`. Apply the tactic sequence `simp [SD.cw, incM, Krd.Qc, Matrix.one_apply, apply_ite, Matrix.smul_apply] <;> (intro h1 h2; exact absurd h1 h2)`.
-/
theorem cw_Q (d : SD σ) (R : RD d) (w : InfinitePlace F) :
    d.cw w (incM F (Matrix.fromBlocks 0 1 (((R.ε : ℤ) : E) • 1) 0 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E)) =
      Krd.Qc d.n R.ε := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [SD.cw, incM, Krd.Qc, Matrix.one_apply, apply_ite, Matrix.smul_apply] <;> (intro h1 h2; exact absurd h1 h2)

/- English proof (translation)
Establish `h` using `congrArg (d.cw w) (form_adelic d x)`. Rewrite `h` using `[frame_adelic d R, cw_mul, cw_mul, cw_Q, cw_transpose, Place.cw_cA]`. Conclude with `h`.
-/
theorem form_w (d : SD σ) (R : RD d) (w : InfinitePlace F) (x : d.G) :
    (d.cw w (inFrame d.b x))ᵀ * Krd.Qc d.n R.ε * (d.cw w (inFrame d.b x)).map star = Krd.Qc d.n R.ε := by
  have h := congrArg (d.cw w) (form_adelic d x)
  rw [frame_adelic d R, cw_mul, cw_mul, cw_Q, cw_transpose, Place.cw_cA] at h
  exact h

end UnitaryGroupBasics

open UnitaryGroupBasics in

/- English proof (translation)
Establish `hζ0` using `Krd.zeta_ne R.hζ`. Take `⟨M, hM⟩ : ∃ M, M = d.cw w (inFrame d.b g)` from `⟨_, rfl⟩`. Establish `hY` using `Krd.inG_conj R.hζ M (hM ▸ form_w d R w g)`. Take `⟨y, hy⟩ : ∃ y : GR d.n, mR y = dZ d.n R.ζ * M * dZ d.n R.ζ⁻¹` from `⟨mkGR _ hY, rfl⟩`. Use `⟨y, (R.ι w y)⁻¹ * g, (mul_inv_cancel_left _ _).symm, fun y' => ?_⟩` and prove the remaining obligations.

Establish `hyw : d.cw w (inFrame d.b (R.ι w y)) = M`. Establish `h` using `R.at_w w y`. Rewrite `h` using `[hy]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Matrix.mul_assoc, Krd.dZ_inv_mul hζ0, Matrix.one_mul]`.

Use `_ = dZ d.n R.ζ⁻¹ * (dZ d.n R.ζ * M * dZ d.n R.ζ⁻¹ * dZ d.n R.ζ) := by rw [h]`. Use `_ = M := by`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[Krd.dZ_inv_mul hζ0, Matrix.mul_one, ← Matrix.mul_assoc, Krd.dZ_inv_mul hζ0, Matrix.one_mul]`. Use `comm_of d w _ _ ?_ (fun w' h => R.off_w w w' y' h) (R.off_f w y')` and prove the remaining obligations.

Establish `e1 : inFrame d.b (R.ι w y)⁻¹ * inFrame d.b (R.ι w y) = 1`. Rewrite using `[← inFrame_mul, inv_mul_cancel, inFrame_one]`. Rewrite using `[inFrame_mul, cw_mul, ← hM, ← hyw, ← cw_mul, e1, cw_one]`.
-/
theorem split (d : SD σ) (R : RD d) (w : InfinitePlace F) (g : d.G) :
    ∃ (y : GR d.n) (x : d.G), g = R.ι w y * x ∧ ∀ y' : GR d.n, x * R.ι w y' = R.ι w y' * x := by
  have hζ0 := Krd.zeta_ne R.hζ
  obtain ⟨M, hM⟩ : ∃ M, M = d.cw w (inFrame d.b g) := ⟨_, rfl⟩
  have hY := Krd.inG_conj R.hζ M (hM ▸ form_w d R w g)
  obtain ⟨y, hy⟩ : ∃ y : GR d.n, mR y = dZ d.n R.ζ * M * dZ d.n R.ζ⁻¹ := ⟨mkGR _ hY, rfl⟩
  refine ⟨y, (R.ι w y)⁻¹ * g, (mul_inv_cancel_left _ _).symm, fun y' => ?_⟩
  have hyw : d.cw w (inFrame d.b (R.ι w y)) = M := by
    have h := R.at_w w y
    rw [hy] at h
    calc d.cw w (inFrame d.b (R.ι w y))
        = dZ d.n R.ζ⁻¹ * (dZ d.n R.ζ * d.cw w (inFrame d.b (R.ι w y))) := by
          rw [← Matrix.mul_assoc, Krd.dZ_inv_mul hζ0, Matrix.one_mul]
      _ = dZ d.n R.ζ⁻¹ * (dZ d.n R.ζ * M * dZ d.n R.ζ⁻¹ * dZ d.n R.ζ) := by rw [h]
      _ = M := by
          simp only [Matrix.mul_assoc]
          rw [Krd.dZ_inv_mul hζ0, Matrix.mul_one, ← Matrix.mul_assoc, Krd.dZ_inv_mul hζ0, Matrix.one_mul]
  refine comm_of d w _ _ ?_ (fun w' h => R.off_w w w' y' h) (R.off_f w y')
  have e1 : inFrame d.b (R.ι w y)⁻¹ * inFrame d.b (R.ι w y) = 1 := by
    rw [← inFrame_mul, inv_mul_cancel, inFrame_one]
  rw [inFrame_mul, cw_mul, ← hM, ← hyw, ← cw_mul, e1, cw_one]

namespace UnitaryGroupBasics

/- English proof (translation)
Unfold `SD.cw`. Rewrite using `[Matrix.fromBlocks_map, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _)]`.
-/
theorem cw_fromBlocks (d : SD σ) (w : InfinitePlace F) (B : Matrix (Fin d.n) (Fin d.n) (AE F E)) :
    d.cw w (Matrix.fromBlocks (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) B (0 : Matrix (Fin d.n) (Fin d.n) (AE F E)) 1) =
      Matrix.fromBlocks (1 : Matrix (Fin d.n) (Fin d.n) ℂ) (d.cw w B) (0 : Matrix (Fin d.n) (Fin d.n) ℂ) 1 := by
  unfold SD.cw
  rw [Matrix.fromBlocks_map, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _)]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cw_toBlocks₁₂ (d : SD σ) (w : InfinitePlace F) (X : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    d.cw w X.toBlocks₁₂ = (d.cw w X).toBlocks₁₂ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fin_toBlocks₁₂ {n : ℕ} (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) :
    finOne F • X.toBlocks₁₂ = (finOne F • X).toBlocks₁₂ := rfl

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.toBlocks₁₂, Matrix.one_apply]`.
-/
theorem toBlocks₁₂_one {n : ℕ} {α : Type} [Zero α] [One α] :
    (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) α).toBlocks₁₂ = 0 := by
  ext i j; simp [Matrix.toBlocks₁₂, Matrix.one_apply]

/- English proof (translation)
Simplify using `[SD.cw, Matrix.trace, map_sum]`.
-/
theorem piInf_trace (d : SD σ) (w : InfinitePlace F) (M : Matrix (Fin d.n) (Fin d.n) (AE F E)) :
    piInf (d.B.emb w) M.trace = (d.cw w M).trace := by
  simp [SD.cw, Matrix.trace, map_sum]

/- English proof (translation)
Establish `hζ0` using `Krd.zeta_ne R.hζ`. Establish `h` using `R.at_w w u`. Rewrite `h` using `[hu]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Matrix.mul_assoc, Krd.dZ_inv_mul hζ0, Matrix.one_mul]`.

Use `_ = dZ d.n R.ζ⁻¹ * (nU H * dZ d.n R.ζ) := by rw [h]`. Use `_ = _ := by simp [dZ, nU, Matrix.fromBlocks_multiply, smul_smul, inv_mul_cancel₀ hζ0, mul_inv_cancel₀ hζ0, Matrix.mul_smul]`.
-/
theorem cw_unip (d : SD σ) (R : RD d) (w : InfinitePlace F) (u : GR d.n) (H : Matrix (Fin d.n) (Fin d.n) ℂ)
    (hu : mR u = nU H) : d.cw w (inFrame d.b (R.ι w u)) = Matrix.fromBlocks 1 (R.ζ • H) 0 1 := by
  have hζ0 := Krd.zeta_ne R.hζ
  have h := R.at_w w u
  rw [hu] at h
  calc d.cw w (inFrame d.b (R.ι w u)) = dZ d.n R.ζ⁻¹ * (dZ d.n R.ζ * d.cw w (inFrame d.b (R.ι w u))) := by
        rw [← Matrix.mul_assoc, Krd.dZ_inv_mul hζ0, Matrix.one_mul]
    _ = dZ d.n R.ζ⁻¹ * (nU H * dZ d.n R.ζ) := by rw [h]
    _ = _ := by simp [dZ, nU, Matrix.fromBlocks_multiply, smul_smul, inv_mul_cancel₀ hζ0, mul_inv_cancel₀ hζ0, Matrix.mul_smul]

end UnitaryGroupBasics

open UnitaryGroupBasics in

/- English proof (translation)
Establish `hP : ∀ x, inFrame d.b (R.ι w (nr x)) = Matrix.fromBlocks 1 (inFrame d.b (R.ι w (nr x))).toBlocks₁₂ 0 1`. Introduce `x`. Apply `Place.cw_ext d` to reduce the goal to its premises. Introduce `u`. Rewrite using `[cw_fromBlocks, cw_toBlocks₁₂]`.

Distinguish the cases in `hu : u = w`. Substitute `hu` using the available equality. Rewrite using `[cw_unip d R u (nr x) _ (hnr x), Matrix.toBlocks_fromBlocks₁₂]`. Rewrite using `[R.off_w w u (nr x) hu, toBlocks₁₂_one, Matrix.fromBlocks_one]`. Rewrite using `[Matrix.fromBlocks_smul, fin_toBlocks₁₂, R.off_f w (nr x), ← fin_toBlocks₁₂, toBlocks₁₂_one, smul_zero]`.

Rewrite using `[← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, smul_zero]`. Use `⟨fun x => ⟨(inFrame d.b (R.ι w (nr x))).toBlocks₁₂, AddSubgroup.subset_closure ⟨R.ι w (nr x), hP x⟩⟩, ?_, fun x => inFrame_inj d ?_⟩` and prove the remaining obligations. Use `haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _`. Establish `hm : Continuous fun g : d.G => mat2 g` using `Units.continuous_val.comp continuous_subtype_val`. Establish `hi : Continuous fun g : d.G => inFrame d.b g` using `(continuous_const.matrix_mul hm).matrix_mul continuous_const`.

Establish `hc : Continuous fun x => inFrame d.b (R.ι w (nr x))` using `hi.comp ((R.cont w).comp (continuous_nr nr hnr))`. Use `Continuous.subtype_mk ?_ _` and prove the remaining obligations. Conclude with `continuous_pi fun i => continuous_pi fun j => hc.matrix_elem (Sum.inl i) (Sum.inr j)`. Rewrite using `[h]`. Conclude with `hP x`.
-/
theorem nbw (d : SD σ) (R : RD d) (w : InfinitePlace F) {nb : nA σ d.Y d.b → d.G} (h : IsNMap d.b nb)
    (nr : (Fin d.n → Fin d.n → ℝ) → GR d.n) (hnr : ∀ x, mR (nr x) = nU (herm x)) :
    ∃ β : (Fin d.n → Fin d.n → ℝ) → nA σ d.Y d.b, Continuous β ∧ ∀ x, R.ι w (nr x) = nb (β x) := by
  have hP : ∀ x, inFrame d.b (R.ι w (nr x)) = Matrix.fromBlocks 1 (inFrame d.b (R.ι w (nr x))).toBlocks₁₂ 0 1 := by
    intro x
    apply Place.cw_ext d
    · intro u
      rw [cw_fromBlocks, cw_toBlocks₁₂]
      by_cases hu : u = w
      · subst hu
        rw [cw_unip d R u (nr x) _ (hnr x), Matrix.toBlocks_fromBlocks₁₂]
      · rw [R.off_w w u (nr x) hu, toBlocks₁₂_one, Matrix.fromBlocks_one]
    · rw [Matrix.fromBlocks_smul, fin_toBlocks₁₂, R.off_f w (nr x), ← fin_toBlocks₁₂, toBlocks₁₂_one, smul_zero]
      rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, smul_zero]
  refine ⟨fun x => ⟨(inFrame d.b (R.ι w (nr x))).toBlocks₁₂, AddSubgroup.subset_closure ⟨R.ι w (nr x), hP x⟩⟩, ?_,
    fun x => inFrame_inj d ?_⟩
  · haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
    have hm : Continuous fun g : d.G => mat2 g := Units.continuous_val.comp continuous_subtype_val
    have hi : Continuous fun g : d.G => inFrame d.b g := (continuous_const.matrix_mul hm).matrix_mul continuous_const
    have hc : Continuous fun x => inFrame d.b (R.ι w (nr x)) := hi.comp ((R.cont w).comp (continuous_nr nr hnr))
    refine Continuous.subtype_mk ?_ _
    exact continuous_pi fun i => continuous_pi fun j => hc.matrix_elem (Sum.inl i) (Sum.inr j)
  · rw [h]; exact hP x

open UnitaryGroupBasics in

/- English proof (translation)
Establish `hB : ∀ x, inFrame d.b (R.ι w (nr x)) = Matrix.fromBlocks 1 (β x).1 0 1` using `fun x => by rw [hβ x, h]`. Establish `hBw : ∀ x, d.cw w (β x).1 = R.ζ • herm x` using `fun x => by`. Establish `e` using `cw_unip d R w (nr x) _ (hnr x)`. Rewrite `e` using `[hB x, cw_fromBlocks]`. Conclude with `(Matrix.fromBlocks_inj.1 e).2.1`.

Establish `hBu : ∀ x u, u ≠ w → d.cw u (β x).1 = 0` using `fun x u hu => by`. Establish `e` using `R.off_w w u (nr x) hu`. Rewrite `e` using `[hB x, cw_fromBlocks, ← Matrix.fromBlocks_one]`. Conclude with `(Matrix.fromBlocks_inj.1 e).2.1`. Establish `hBf : ∀ x, finOne F • (β x).1 = 0` using `fun x => by`.

Establish `e` using `R.off_f w (nr x)`. Rewrite `e` using `[hB x, Matrix.fromBlocks_smul, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul]`. Conclude with `(Matrix.fromBlocks_inj.1 e).2.1.trans (smul_zero _)`. Establish `hT : (d.cw w T.1.1)ᵀ + ((R.ε : ℤ) : ℂ) • (d.cw w T.1.1).map star = 0`. Use `AddSubgroup.closure_induction (p := fun β _ => (d.cw w β)ᵀ + ((R.ε : ℤ) : ℂ) • (d.cw w β).map star = 0) ?_ ?_ ?_ ?_ T.1.2` and prove the remaining obligations.

Introduce and unpack `β ⟨x, hx⟩`. Establish `e` using `form_w d R w x`. Rewrite `e` using `[hx, cw_fromBlocks]`. Simplify using `[Krd.Qc, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply] at e`. Rewrite using `[add_comm]`.

Conclude with `e`. Use extensionality with `i j`. Simplify using `[SD.cw]`. Introduce `a b _ _ ha hb`. Use extensionality with `i j`.

Establish `ea` using `congrFun (congrFun ha i) j`. Establish `eb` using `congrFun (congrFun hb i) j`. Simplify using `[SD.cw] at ea eb ⊢`. Take the linear combination `ea + eb`. Introduce `a _ ha`.

Use extensionality with `i j`. Establish `ea` using `congrFun (congrFun ha i) j`. Simplify using `[SD.cw] at ea ⊢`. Take the linear combination `-ea`. Take `⟨Tw, hTw⟩ : ∃ Tw, Tw = d.cw w T.1.1` from `⟨_, rfl⟩`.

Rewrite `hT` using `[← hTw]`. Establish `hAh : (R.ζ • Tw)ᴴ = R.ζ • Tw`. Use extensionality with `i j`. Establish `e` using `congrFun (congrFun hT j) i`. Simplify using `only [Matrix.add_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.zero_apply, smul_eq_mul] at e`.

Rewrite using `[Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, star_mul']`. Break down `R.hζ with ⟨hε, hζ⟩ | ⟨hε, hζ⟩` into its components or cases. Rewrite using `[hζ]`. Rewrite `e` using `[hε]`. Simplify using `at e ⊢`.

Take the linear combination `-e`. Rewrite using `[hζ]`. Rewrite `e` using `[hε]`. Simplify using `at e ⊢`. Take the linear combination `(-Complex.I) * e`.

Use `⟨-(2 : ℂ) • (R.ζ • Tw), ?_, fun h0 => ?_, fun x => ?_⟩` and prove the remaining obligations. Use `show (-(2 : ℂ) • (R.ζ • Tw))ᴴ = -(2 : ℂ) • (R.ζ • Tw)`. Rewrite using `[Matrix.conjTranspose_smul, hAh]`. Use `congr 1`. Simplify using the standard rewrite rules.

Establish `hd : Tw.det = 0`. Rewrite using `[hTw, show (d.cw w T.1.1).det = ((piInf (d.B.emb w)).mapMatrix T.1.1).det from rfl, ← RingHom.map_det, h0, map_zero]`. Rewrite using `[Matrix.det_smul, Matrix.det_smul, hd]`. Simplify using the standard rewrite rules. Establish `hf : finOne F • (T.1.1 * (β x).1).trace = 0`.

Rewrite using `[← Matrix.trace_smul, ← Matrix.mul_smul, hBf x, Matrix.mul_zero, Matrix.trace_zero]`. Establish `hw : ∀ u, u ≠ w → piInf (d.B.emb u) (T.1.1 * (β x).1).trace = 0` using `fun u hu => by`. Rewrite using `[piInf_trace, cw_mul, hBu x u hu, Matrix.mul_zero, Matrix.trace_zero]`. Establish `hz` using `Place.psi_trace_at d.std d.cm d.B.emb w (T.1.1 * (β x).1).trace hf hw`. Establish `hw' : piInf (d.B.emb w) (T.1.1 * (β x).1).trace = ((R.ζ • Tw) * herm x).trace`.

Rewrite using `[piInf_trace, cw_mul, hBw x, ← hTw, Matrix.mul_smul, Matrix.smul_mul]`. Establish `hreal : ((((R.ζ • Tw) * herm x).trace).re : ℂ) = ((R.ζ • Tw) * herm x).trace`. Establish `hs : star (((R.ζ • Tw) * herm x).trace) = ((R.ζ • Tw) * herm x).trace`. Rewrite using `[← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hAh, herm_conjTranspose', Matrix.trace_mul_comm]`. Conclude with `Complex.conj_eq_iff_re.1 hs`.

Establish `eR : (-(2 : ℂ) • (R.ζ • Tw) * herm x).trace = -2 * (R.ζ • Tw * herm x).trace`. Rewrite using `[Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]`. Unfold `SD.tt eTr`. Rewrite using `[hz, hw', eR]`. Generalize the expression as in `(R.ζ • Tw * herm x).trace = c at hreal ⊢`.

Use `congr 1`. Use `push_cast`. Rewrite using `[hreal]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem charW (d : SD σ) (R : RD d) (w : InfinitePlace F) {nb : nA σ d.Y d.b → d.G} (h : IsNMap d.b nb)
    (nr : (Fin d.n → Fin d.n → ℝ) → GR d.n) (hnr : ∀ x, mR (nr x) = nU (herm x))
    (β : (Fin d.n → Fin d.n → ℝ) → nA σ d.Y d.b) (hβ : ∀ x, R.ι w (nr x) = nb (β x)) (T : nF σ d.Y d.b) :
    ∃ β' : Matrix (Fin d.n) (Fin d.n) ℂ, β'.IsHermitian ∧ (T.1.1.det = 0 → β'.det = 0) ∧
      ∀ x, d.B.ψ (d.tt (T.1.1 * (β x).1)) = eTr β' x := by
  have hB : ∀ x, inFrame d.b (R.ι w (nr x)) = Matrix.fromBlocks 1 (β x).1 0 1 := fun x => by rw [hβ x, h]
  have hBw : ∀ x, d.cw w (β x).1 = R.ζ • herm x := fun x => by
    have e := cw_unip d R w (nr x) _ (hnr x)
    rw [hB x, cw_fromBlocks] at e
    exact (Matrix.fromBlocks_inj.1 e).2.1
  have hBu : ∀ x u, u ≠ w → d.cw u (β x).1 = 0 := fun x u hu => by
    have e := R.off_w w u (nr x) hu
    rw [hB x, cw_fromBlocks, ← Matrix.fromBlocks_one] at e
    exact (Matrix.fromBlocks_inj.1 e).2.1
  have hBf : ∀ x, finOne F • (β x).1 = 0 := fun x => by
    have e := R.off_f w (nr x)
    rw [hB x, Matrix.fromBlocks_smul, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul] at e
    exact (Matrix.fromBlocks_inj.1 e).2.1.trans (smul_zero _)
  have hT : (d.cw w T.1.1)ᵀ + ((R.ε : ℤ) : ℂ) • (d.cw w T.1.1).map star = 0 := by
    refine AddSubgroup.closure_induction
      (p := fun β _ => (d.cw w β)ᵀ + ((R.ε : ℤ) : ℂ) • (d.cw w β).map star = 0) ?_ ?_ ?_ ?_ T.1.2
    · rintro β ⟨x, hx⟩
      have e := form_w d R w x
      rw [hx, cw_fromBlocks] at e
      simp [Krd.Qc, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply] at e
      rw [add_comm]
      exact e
    · ext i j; simp [SD.cw]
    · intro a b _ _ ha hb
      ext i j
      have ea := congrFun (congrFun ha i) j
      have eb := congrFun (congrFun hb i) j
      simp [SD.cw] at ea eb ⊢
      linear_combination ea + eb
    · intro a _ ha
      ext i j
      have ea := congrFun (congrFun ha i) j
      simp [SD.cw] at ea ⊢
      linear_combination -ea
  obtain ⟨Tw, hTw⟩ : ∃ Tw, Tw = d.cw w T.1.1 := ⟨_, rfl⟩
  rw [← hTw] at hT
  have hAh : (R.ζ • Tw)ᴴ = R.ζ • Tw := by
    ext i j
    have e := congrFun (congrFun hT j) i
    simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.zero_apply,
      smul_eq_mul] at e
    rw [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, star_mul']
    rcases R.hζ with ⟨hε, hζ⟩ | ⟨hε, hζ⟩
    · rw [hζ]; rw [hε] at e; simp at e ⊢; linear_combination -e
    · rw [hζ]; rw [hε] at e; simp at e ⊢; linear_combination (-Complex.I) * e
  refine ⟨-(2 : ℂ) • (R.ζ • Tw), ?_, fun h0 => ?_, fun x => ?_⟩
  · show (-(2 : ℂ) • (R.ζ • Tw))ᴴ = -(2 : ℂ) • (R.ζ • Tw)
    rw [Matrix.conjTranspose_smul, hAh]
    congr 1
    simp
  · have hd : Tw.det = 0 := by
      rw [hTw, show (d.cw w T.1.1).det = ((piInf (d.B.emb w)).mapMatrix T.1.1).det from rfl, ← RingHom.map_det, h0,
        map_zero]
    rw [Matrix.det_smul, Matrix.det_smul, hd]
    simp
  · have hf : finOne F • (T.1.1 * (β x).1).trace = 0 := by
      rw [← Matrix.trace_smul, ← Matrix.mul_smul, hBf x, Matrix.mul_zero, Matrix.trace_zero]
    have hw : ∀ u, u ≠ w → piInf (d.B.emb u) (T.1.1 * (β x).1).trace = 0 := fun u hu => by
      rw [piInf_trace, cw_mul, hBu x u hu, Matrix.mul_zero, Matrix.trace_zero]
    have hz := Place.psi_trace_at d.std d.cm d.B.emb w (T.1.1 * (β x).1).trace hf hw
    have hw' : piInf (d.B.emb w) (T.1.1 * (β x).1).trace = ((R.ζ • Tw) * herm x).trace := by
      rw [piInf_trace, cw_mul, hBw x, ← hTw, Matrix.mul_smul, Matrix.smul_mul]
    have hreal : ((((R.ζ • Tw) * herm x).trace).re : ℂ) = ((R.ζ • Tw) * herm x).trace := by
      have hs : star (((R.ζ • Tw) * herm x).trace) = ((R.ζ • Tw) * herm x).trace := by
        rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hAh, herm_conjTranspose', Matrix.trace_mul_comm]
      exact Complex.conj_eq_iff_re.1 hs
    have eR : (-(2 : ℂ) • (R.ζ • Tw) * herm x).trace = -2 * (R.ζ • Tw * herm x).trace := by
      rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    unfold SD.tt eTr
    rw [hz, hw', eR]
    generalize (R.ζ • Tw * herm x).trace = c at hreal ⊢
    congr 1
    push_cast
    rw [hreal]
    ring

end PositivityTheory.SiegelWeilFormula.KSing

end
