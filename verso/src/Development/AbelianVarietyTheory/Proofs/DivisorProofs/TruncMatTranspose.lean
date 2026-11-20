import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.TruncFix

open scoped Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def idem (T : Finset (Pl F)) : AF F := ∑ v ∈ T, GlobalTheory.LatVac.liftV v 1

/- English proof (translation)
Distinguish the cases in `h : w = v`. Substitute `h` using the available equality. Rewrite using `[if_pos rfl, GlobalTheory.LatVac.evFin_liftV]`. Rewrite using `[if_neg h]`. Conclude with `GlobalTheory.ThK.LocalOps.evFin_of_at h (GlobalTheory.LatVac.at_liftV v 1)`.
-/
theorem evFin_liftV_one (v w : Pl F) : evFin F w (GlobalTheory.LatVac.liftV v 1) = if w = v then 1 else 0 := by
  by_cases h : w = v
  · subst h; rw [if_pos rfl, GlobalTheory.LatVac.evFin_liftV]
  · rw [if_neg h]; exact GlobalTheory.ThK.LocalOps.evFin_of_at h (GlobalTheory.LatVac.at_liftV v 1)

/- English proof (translation)
Simplify using `only [idem, map_sum, evFin_liftV_one]`. Rewrite using `[Finset.sum_ite_eq]`.
-/
theorem evFin_idem (T : Finset (Pl F)) (w : Pl F) : evFin F w (idem T) = if w ∈ T then 1 else 0 := by
  classical
  simp only [idem, map_sum, evFin_liftV_one]
  rw [Finset.sum_ite_eq]

/- English proof (translation)
Use `conv_lhs => rw [idem, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun v hv => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.ThK.LocalOps.liftV_one_mul, ← idem, evFin_idem, if_pos hv]`.
-/
theorem idem_mul_idem (T : Finset (Pl F)) : idem T * idem T = idem T := by
  classical
  conv_lhs => rw [idem, Finset.sum_mul]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [GlobalTheory.ThK.LocalOps.liftV_one_mul, ← idem, evFin_idem, if_pos hv]

/- English proof (translation)
Rewrite using `[idem, Finset.sum_insert hv]`. Both sides reduce to the same expression.
-/
theorem idem_insert {T : Finset (Pl F)} {v : Pl F} (hv : v ∉ T) :
    idem (insert v T) = GlobalTheory.LatVac.liftV v 1 + idem T := by
  classical
  rw [idem, Finset.sum_insert hv]; rfl

/- English proof (translation)
Rewrite using `[GlobalTheory.ThK.LocalOps.liftV_one_mul, evFin_idem, if_neg hv, map_zero]`.
-/
theorem liftV_mul_idem {T : Finset (Pl F)} {v : Pl F} (hv : v ∉ T) : GlobalTheory.LatVac.liftV v 1 * idem T = 0 := by
  classical
  rw [GlobalTheory.ThK.LocalOps.liftV_one_mul, evFin_idem, if_neg hv, map_zero]

/- English proof (translation)
Simplify using `[idem]`.
-/
theorem idem_singleton (v : Pl F) : idem ({v} : Finset (Pl F)) = GlobalTheory.LatVac.liftV v 1 := by
  simp [idem]

def truncMat {n : ℕ} (e : AF F) (A : Matrix (Fin n) (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E) := 1 + e • (A - 1)

/- English proof (translation)
Simplify using `only [truncMat, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, he, Matrix.sub_mul, Matrix.mul_sub, h]`. Establish `he2 : e ^ 2 = e` using `by rw [sq, he]`. Apply the tactic sequence `match_scalars <;> ring_nf <;> simp only [he2] <;> ring`.
-/
theorem truncMat_mul {n : ℕ} {e : AF F} (he : e * e = e) {A B : Matrix (Fin n) (Fin n) (AE F E)} (h : A * B = 1) :
    truncMat e A * truncMat e B = 1 := by
  simp only [truncMat, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, he, Matrix.sub_mul, Matrix.mul_sub, h]
  have he2 : e ^ 2 = e := by rw [sq, he]
  match_scalars <;> ring_nf <;> simp only [he2] <;> ring

/- English proof (translation)
Simplify using `[truncMat, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_sub]`.
-/
theorem truncMat_transpose {n : ℕ} (e : AF F) (A : Matrix (Fin n) (Fin n) (AE F E)) :
    (truncMat e A)ᵀ = truncMat e Aᵀ := by
  simp [truncMat, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_sub]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `by_cases h : i = j <;> simp [truncMat, Matrix.one_apply, h]`.
-/
theorem truncMat_map (σ : E →ₐ[F] E) {n : ℕ} (e : AF F) (A : Matrix (Fin n) (Fin n) (AE F E)) :
    (truncMat e A).map (cA σ) = truncMat e (A.map (cA σ)) := by
  ext i j
  by_cases h : i = j <;> simp [truncMat, Matrix.one_apply, h]

/- English proof (translation)
Establish `h' : Aᵀ * (J * Ab) = J` using `by rw [← Matrix.mul_assoc, h]`. Rewrite using `[truncMat_transpose]`. Simplify using `only [truncMat, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, h']`. Establish `he2 : e ^ 2 = e` using `by rw [sq, he]`. Apply the tactic sequence `match_scalars <;> ring_nf <;> simp only [he2] <;> ring`.
-/
theorem truncMat_unitary {n : ℕ} {e : AF F} (he : e * e = e) {A Ab J : Matrix (Fin n) (Fin n) (AE F E)}
    (h : Aᵀ * J * Ab = J) : (truncMat e A)ᵀ * J * truncMat e Ab = J := by
  have h' : Aᵀ * (J * Ab) = J := by rw [← Matrix.mul_assoc, h]
  rw [truncMat_transpose]
  simp only [truncMat, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, h']
  have he2 : e ^ 2 = e := by rw [sq, he]
  match_scalars <;> ring_nf <;> simp only [he2] <;> ring

variable {σ : E →ₐ[F] E}

def truncU (T : Finset (Pl F)) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (k : UA σ J) : UA σ J :=
  ⟨⟨truncMat (idem T) k.1.1, truncMat (idem T) k.1.inv, truncMat_mul (idem_mul_idem T) k.1.val_inv,
    truncMat_mul (idem_mul_idem T) k.1.inv_val⟩, by
    show (truncMat (idem T) k.1.1)ᵀ * incM F J * (truncMat (idem T) k.1.1).map (cA σ) = incM F J
    rw [truncMat_map]
    exact truncMat_unitary (idem_mul_idem T) k.2⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_truncU (T : Finset (Pl F)) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (k : UA σ J) :
    mat (truncU T k) = truncMat (idem T) (mat k) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_truncU_inv (T : Finset (Pl F)) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (k : UA σ J) :
    mat (truncU T k)⁻¹ = truncMat (idem T) (mat k⁻¹) := rfl

/- English proof (translation)
Use `Subtype.ext (Units.ext ?_)` and prove the remaining obligations. Use `show truncMat (idem (insert v T)) (mat k) = truncMat (idem {v}) (mat k) * truncMat (idem T) (mat k)`. Establish `h0 : GlobalTheory.LatVac.liftV v 1 * idem T = 0` using `liftV_mul_idem hv`. Rewrite using `[idem_insert hv, idem_singleton]`. Unfold `truncMat`.

Rewrite using `[Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h0, zero_smul, add_zero, add_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem truncU_insert {T : Finset (Pl F)} {v : Pl F} (hv : v ∉ T) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (k : UA σ J) :
    truncU (insert v T) k = truncU {v} k * truncU T k := by
  refine Subtype.ext (Units.ext ?_)
  show truncMat (idem (insert v T)) (mat k) = truncMat (idem {v}) (mat k) * truncMat (idem T) (mat k)
  have h0 : GlobalTheory.LatVac.liftV v 1 * idem T = 0 := liftV_mul_idem hv
  rw [idem_insert hv, idem_singleton]
  unfold truncMat
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h0,
    zero_smul, add_zero, add_smul]
  abel

/- English proof (translation)
Introduce `u hu`. Rewrite using `[mat_truncU, idem_singleton]`. Simplify using `only [truncMat, add_sub_cancel_left, smul_smul]`. Rewrite using `[mul_comm, GlobalTheory.ThK.LocalOps.liftV_one_mul, hu, map_zero, zero_smul]`.
-/
theorem truncU_mem_UAt (v : Pl F) {n : ℕ} {X : Spc F E n} (k : UA σ X.J) :
    truncU {v} k ∈ UAt σ X (evFin F v) := by
  intro u hu
  rw [mat_truncU, idem_singleton]
  simp only [truncMat, add_sub_cancel_left, smul_smul]
  rw [mul_comm, GlobalTheory.ThK.LocalOps.liftV_one_mul, hu, map_zero, zero_smul]

end GlobalTheory.TruncFix
