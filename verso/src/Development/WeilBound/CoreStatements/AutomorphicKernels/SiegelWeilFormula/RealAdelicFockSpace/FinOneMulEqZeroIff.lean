import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.JnArcFin
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.SplitW
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealScalarArchimedeanAdeleSmulMatrixRealPlace

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def yrotM (n : ℕ) (s : ℤˣ) (t : ℝ) : M2 n :=
  Matrix.fromBlocks ((Real.cos t : ℂ) • 1) ((((s : ℤ) : ℂ) * Real.sin t) • 1) ((-(((s : ℤ) : ℂ) * Real.sin t)) • 1)
    ((Real.cos t : ℂ) • 1)

/- English proof (translation)
Apply the tactic sequence `rcases Int.units_eq_one_or s with rfl | rfl <;>`. Simplify using `only [yrotM, Matrix.fromBlocks_multiply, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, ← add_smul]`. Apply the tactic sequence `refine Matrix.fromBlocks_inj.2 ⟨?_, ?_, ?_, ?_⟩ <;>`. Use `congr 1`. Move the coercions through the operations in `[Real.cos_add, Real.sin_add]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem yrotM_mul (n : ℕ) (s : ℤˣ) (t t' : ℝ) : yrotM n s t * yrotM n s t' = yrotM n s (t + t') := by
  rcases Int.units_eq_one_or s with rfl | rfl <;>
  · simp only [yrotM, Matrix.fromBlocks_multiply, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
      ← add_smul]
    refine Matrix.fromBlocks_inj.2 ⟨?_, ?_, ?_, ?_⟩ <;>
    · congr 1
      push_cast [Real.cos_add, Real.sin_add]
      ring

/- English proof (translation)
Simplify using `[yrotM, Matrix.fromBlocks_one]`.
-/
theorem yrotM_zero (n : ℕ) (s : ℤˣ) : yrotM n s 0 = 1 := by
  simp [yrotM, Matrix.fromBlocks_one]

/- English proof (translation)
Simplify using `only [yrotM, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Real.cos_neg, Real.sin_neg]`. Apply the tactic sequence `refine Matrix.fromBlocks_inj.2 ⟨?_, ?_, ?_, ?_⟩ <;>`. Use `congr 1`. Simplify using `[← Complex.cos_conj, ← Complex.sin_conj, Complex.conj_ofReal]`.
-/
theorem yrotM_ct (n : ℕ) (s : ℤˣ) (t : ℝ) : (yrotM n s t)ᴴ = yrotM n s (-t) := by
  simp only [yrotM, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    Real.cos_neg, Real.sin_neg]
  refine Matrix.fromBlocks_inj.2 ⟨?_, ?_, ?_, ?_⟩ <;>
  · congr 1
    simp [← Complex.cos_conj, ← Complex.sin_conj, Complex.conj_ofReal]

/- English proof (translation)
Simplify using `[JJ, yrotM, Matrix.fromBlocks_multiply]`.
-/
theorem JJ_comm_yrotM (n : ℕ) (s : ℤˣ) (t : ℝ) : JJ n * yrotM n s t = yrotM n s t * JJ n := by
  simp [JJ, yrotM, Matrix.fromBlocks_multiply]

/- English proof (translation)
Establish `h1 : (yrotM n s t)ᴴ * yrotM n s t = 1`. Rewrite using `[yrotM_ct, yrotM_mul, neg_add_cancel, yrotM_zero]`. Use `⟨?_, h1⟩` and prove the remaining obligations. Use `show (yrotM n s t)ᴴ * JJ n * yrotM n s t = JJ n`. Rewrite using `[Matrix.mul_assoc, JJ_comm_yrotM, ← Matrix.mul_assoc, h1, Matrix.one_mul]`.
-/
theorem inK_yrotM (n : ℕ) (s : ℤˣ) (t : ℝ) : InK (yrotM n s t) := by
  have h1 : (yrotM n s t)ᴴ * yrotM n s t = 1 := by
    rw [yrotM_ct, yrotM_mul, neg_add_cancel, yrotM_zero]
  refine ⟨?_, h1⟩
  show (yrotM n s t)ᴴ * JJ n * yrotM n s t = JJ n
  rw [Matrix.mul_assoc, JJ_comm_yrotM, ← Matrix.mul_assoc, h1, Matrix.one_mul]

def yrot (n : ℕ) (s : ℤˣ) (t : ℝ) : GR n :=
  ⟨⟨yrotM n s t, yrotM n s (-t), by rw [yrotM_mul, add_neg_cancel, yrotM_zero],
    by rw [yrotM_mul, neg_add_cancel, yrotM_zero]⟩, (inK_yrotM n s t).1⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mR_yrot (n : ℕ) (s : ℤˣ) (t : ℝ) : mR (yrot n s t) = yrotM n s t := rfl

variable {d : SD σ}

def rot (R : RD d) (t : ℝ) : d.G :=
  (((Finset.univ : Finset (InfinitePlace F)).toList).map fun w => R.ι w (yrot d.n (R.sg w) t)).prod

/- English proof (translation)
Unfold `rot`. Use `d.K.list_prod_mem fun x hx => ?_` and prove the remaining obligations. Take `⟨w, -, rfl⟩` from `List.mem_map.1 hx`. Conclude with `KSplitW.iota_mem_K d R w _ (by rw [mR_yrot]; exact inK_yrotM _ _ _)`.
-/
theorem rot_mem (R : RD d) (t : ℝ) : rot R t ∈ d.K := by
  unfold rot
  refine d.K.list_prod_mem fun x hx => ?_
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
  exact KSplitW.iota_mem_K d R w _ (by rw [mR_yrot]; exact inK_yrotM _ _ _)

/- English proof (translation)
Take `⟨s, -, hs1, hs2, -, -⟩` from `Place.exists_sec d.cm d.B.emb`. Use `⟨s (fun w => -(((R.sg w : ℤ) : ℂ) * R.ζ)) • W, ?_, fun w => ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Simplify using `only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]`. Rewrite using `[← smul_mul_assoc, hs2, zero_mul]`.

Use extensionality with `i j`. Simplify using `only [SD.cw, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hs1]`.
-/
theorem exists_tw (R : RD d) (W : Mx F E d.m d.n) :
    ∃ W' : Mx F E d.m d.n, finOne F • W' = 0 ∧ ∀ w, d.cw w W' = (-(((R.sg w : ℤ) : ℂ) * R.ζ)) • d.cw w W := by
  obtain ⟨s, -, hs1, hs2, -, -⟩ := Place.exists_sec d.cm d.B.emb
  refine ⟨s (fun w => -(((R.sg w : ℤ) : ℂ) * R.ζ)) • W, ?_, fun w => ?_⟩
  · ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    rw [← smul_mul_assoc, hs2, zero_mul]
  · ext i j
    simp only [SD.cw, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hs1]

def tw (R : RD d) (W : Mx F E d.m d.n) : Mx F E d.m d.n := (exists_tw R W).choose

def vline (R : RD d) (W : Mx F E d.m d.n) (z : ℂ) : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  (realAd F z.re • W) * (incM F d.b.1.toCols₂)ᵀ + (realAd F z.im • tw R W) * (incM F d.b.1.toCols₁)ᵀ

/- English proof (translation)
Use `show (0 : InfiniteAdeleRing F) * a.1 = 0`. Conclude with `zero_mul _`.
-/
theorem finOne_mul_fst (a : AF F) : (finOne F * a).1 = 0 := by
  show (0 : InfiniteAdeleRing F) * a.1 = 0
  exact zero_mul _

/- English proof (translation)
Use `show (1 : Af F) * a.2 = a.2`. Conclude with `one_mul _`.
-/
theorem finOne_mul_snd (a : AF F) : (finOne F * a).2 = a.2 := by
  show (1 : Af F) * a.2 = a.2
  exact one_mul _

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `congrArg Prod.snd h` as an intermediate fact. Rewrite `this` using `[finOne_mul_snd]`. Conclude with `this`.

Introduce `h`. Conclude with `Prod.ext (finOne_mul_fst a) ((finOne_mul_snd a).trans h)`.
-/
theorem finOne_mul_eq_zero_iff (a : AF F) : finOne F * a = 0 ↔ a.2 = 0 := by
  constructor
  · intro h
    have := congrArg Prod.snd h
    rw [finOne_mul_snd] at this
    exact this
  · intro h
    exact Prod.ext (finOne_mul_fst a) ((finOne_mul_snd a).trans h)

/- English proof (translation)
Use `set bas := Algebra.TensorProduct.basis (AF F) d.bs`. Establish `key : ∀ z : AE F E, finOne F • z = 0 ↔ ∀ l, (bas.repr z l).2 = 0`. Introduce `z`. Rewrite using `[← bas.repr.injective.eq_iff, LinearEquiv.map_smul, LinearEquiv.map_zero]`. Simplify using `only [Finsupp.ext_iff, Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply, finOne_mul_eq_zero_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use extensionality with `i j`. Simplify using `only [Matrix.smul_apply, Matrix.zero_apply]`. Use `(key _).2 fun l => ?_` and prove the remaining obligations.

Conclude with `congrFun h (i, j, l)`. Introduce `h`. Use function extensionality and compare the values at `⟨i, j, l⟩`. Conclude with `(key (X i j)).1 (by simpa using congrFun (congrFun h i) j) l`.
-/
theorem fin_eq_zero_iff (X : Mx F E d.m d.n) : fin d X = 0 ↔ finOne F • X = 0 := by
  set bas := Algebra.TensorProduct.basis (AF F) d.bs
  have key : ∀ z : AE F E, finOne F • z = 0 ↔ ∀ l, (bas.repr z l).2 = 0 := by
    intro z
    rw [← bas.repr.injective.eq_iff, LinearEquiv.map_smul, LinearEquiv.map_zero]
    simp only [Finsupp.ext_iff, Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply,
      finOne_mul_eq_zero_iff]
  constructor
  · intro h
    ext i j
    simp only [Matrix.smul_apply, Matrix.zero_apply]
    refine (key _).2 fun l => ?_
    exact congrFun h (i, j, l)
  · intro h
    funext ⟨i, j, l⟩
    exact (key (X i j)).1 (by simpa using congrFun (congrFun h i) j) l

end PositivityTheory.SiegelWeilFormula.KFP

end
