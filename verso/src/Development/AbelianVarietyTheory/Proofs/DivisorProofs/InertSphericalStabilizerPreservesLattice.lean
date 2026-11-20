import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianLatticeOpenCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
open scoped GlobalTheory.VacAny

noncomputable section
namespace GlobalTheory.InertSphStab

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[incM, Matrix.vecMulVec_apply, map_mul]`.
-/
lemma incM_vecMulVec {n d : ℕ} (x : Fin n → E) (y : Fin d → E) :
    incM F (Matrix.vecMulVec x y) =
      Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) (fun j => inclR (F := F) (AF F) (y j)) := by
  ext i j
  simp [incM, Matrix.vecMulVec_apply, map_mul]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.vecMulVec_apply, mul_smul_comm]`.
-/
lemma smul_vecMulVec {n d : ℕ} (a : AF F) (p : Fin n → AE F E) (q : Fin d → AE F E) :
    a • Matrix.vecMulVec p q = Matrix.vecMulVec p (a • q) := by
  ext i j
  simp [Matrix.vecMulVec_apply, mul_smul_comm]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
lemma vecMulVec_mul_transpose {n d : ℕ} (p : Fin n → AE F E) (q : Fin d → AE F E)
    (M : Matrix (Fin d) (Fin d) (AE F E)) :
    Matrix.vecMulVec p q * Mᵀ = Matrix.vecMulVec p (M *ᵥ q) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/- English proof (translation)
Proceed by induction on `hq using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, hai, y, hy, rfl⟩` from `hz`. Use `AddSubgroup.subset_closure ⟨a, ha, hai, x, hx, y, hy, ?_⟩` and prove the remaining obligations. Rewrite using `[incM_vecMulVec, smul_vecMulVec]`.

Consider the case `zero`. Establish `h0 : Matrix.vecMulVec (fun i => inclR (F` using `F) (AF F) (x i)) (0 : Fin d → AE F E) = 0 := by`. Use extensionality with `i j`. Simplify using `[Matrix.vecMulVec_apply]`. Rewrite using `[h0]`.

Conclude with `(latAtV X W v).zero_mem`. Consider the case `add z z' _ _ h h'`. Rewrite using `[Matrix.vecMulVec_add]`. Conclude with `(latAtV X W v).add_mem h h'`. Consider the case `neg z _ h`.

Rewrite using `[Matrix.vecMulVec_neg]`. Conclude with `(latAtV X W v).neg_mem h`.
-/
lemma vecMulVec_mem {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl F) {x : Fin n → E} (hx : x ∈ X.L)
    {q : Fin d → AE F E} (hq : q ∈ GlobalTheory.InertSph.latAt W v) :
    Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) q ∈ latAtV X W v := by
  induction hq using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hai, y, hy, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, ha, hai, x, hx, y, hy, ?_⟩
    rw [incM_vecMulVec, smul_vecMulVec]
  | zero =>
    have h0 : Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) (0 : Fin d → AE F E) = 0 := by
      ext i j; simp [Matrix.vecMulVec_apply]
    rw [h0]; exact (latAtV X W v).zero_mem
  | add z z' _ _ h h' =>
    rw [Matrix.vecMulVec_add]
    exact (latAtV X W v).add_mem h h'
  | neg z _ h =>
    rw [Matrix.vecMulVec_neg]
    exact (latAtV X W v).neg_mem h

end GlobalTheory.InertSphStab
