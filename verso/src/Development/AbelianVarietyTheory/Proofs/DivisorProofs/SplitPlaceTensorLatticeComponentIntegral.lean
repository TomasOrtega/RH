import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LatInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}

/- English proof (translation)
Simplify using `[piW, inclR, compFin, TensorProduct.smul_tmul', splitProj_tmul]`.
-/
theorem piW_smul_incl (v : Pl F) (t : E →ₐ[F] Fv F v) (a : AF F) (e : E) :
    piW t (a • inclR (F := F) (AF F) e) = evFin F v a * t e := by
  simp [piW, inclR, compFin, TensorProduct.smul_tmul', splitProj_tmul]

/- English proof (translation)
Use `⟨_, tmul_mem_latLoc (one_mem _) hx, funext fun i => ?_⟩` and prove the remaining obligations. Simplify using `[splitVec, splitProj_tmul]`.
-/
theorem comp_mem_splitLat (v : Pl F) (t : E →ₐ[F] Fv F v) {L : Submodule (𝓞 E) (Fin n → E)} {x : Fin n → E}
    (hx : x ∈ L) : (fun i => t (x i)) ∈ splitLat t L := by
  refine ⟨_, tmul_mem_latLoc (one_mem _) hx, funext fun i => ?_⟩
  simp [splitVec, splitProj_tmul]

end GlobalTheory.LatInt

namespace GlobalTheory.LatInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}

/- English proof (translation)
Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.map_apply, Matrix.smul_apply, incM, Matrix.vecMulVec_apply, smul_eq_mul]`. Rewrite using `[piW_smul_incl, map_mul]`.
-/
theorem map_piW_gen (v : Pl F) (t : E →ₐ[F] Fv F v) (a : AF F) (x : Fin n → E) (y : Fin d → E) :
    (a • incM F (Matrix.vecMulVec x y)).map (piW t) =
      evFin F v a • Matrix.vecMulVec (fun i => t (x i)) (fun j => t (y j)) := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.map_apply, Matrix.smul_apply, incM, Matrix.vecMulVec_apply, smul_eq_mul]
  rw [piW_smul_incl, map_mul]

/- English proof (translation)
Introduce `γ hγ`. Proceed by induction on `hγ using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, -, ha, x, hx, y, hy, rfl⟩` from `hz`. Establish `hx'` using `(hb.mem_iff).1 (comp_mem_splitLat v t hx)`.

Establish `hy'` using `(hc.mem_iff).1 (comp_mem_splitLat v t hy)`. Introduce `i j`. Rewrite using `[map_piW_gen, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]`. Conclude with `mul_mem ha (mul_mem (hx' i) (hy' j))`. Consider the case `zero => intro i j`.

Simplify using the standard rewrite rules. Consider the case `add γ δ _ _ hγ hδ`. Introduce `i j`. Rewrite using `[Matrix.map_add (piW t) (map_add _), Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]`. Conclude with `add_mem (hγ i j) (hδ i j)`.

Consider the case `neg γ _ hγ`. Introduce `i j`. Rewrite using `[Matrix.map_neg (piW t) (map_neg _), Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply]`. Conclude with `neg_mem (hγ i j)`.
-/
theorem latAtV_comp_integral {n d : ℕ}
    (X : Spc F E n) (W : Spc F E d) (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v))
    (c : GL (Fin d) (Fv F v)) (hb : IsSplitBasis t X.L b) (hc : IsSplitBasis t W.L c) :
    ∀ γ ∈ latAtV X W v, ∀ i j,
      ((b⁻¹).1 * γ.map (piW t) * (c⁻¹).1ᵀ) i j ∈ v.adicCompletionIntegers F := by
  intro γ hγ
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, -, ha, x, hx, y, hy, rfl⟩ := hz
    have hx' := (hb.mem_iff).1 (comp_mem_splitLat v t hx)
    have hy' := (hc.mem_iff).1 (comp_mem_splitLat v t hy)
    intro i j
    rw [map_piW_gen, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
      Matrix.vecMul_transpose, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    exact mul_mem ha (mul_mem (hx' i) (hy' j))
  | zero => intro i j; simp
  | add γ δ _ _ hγ hδ =>
    intro i j
    rw [Matrix.map_add (piW t) (map_add _), Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
    exact add_mem (hγ i j) (hδ i j)
  | neg γ _ hγ =>
    intro i j
    rw [Matrix.map_neg (piW t) (map_neg _), Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply]
    exact neg_mem (hγ i j)

end GlobalTheory.LatInt
