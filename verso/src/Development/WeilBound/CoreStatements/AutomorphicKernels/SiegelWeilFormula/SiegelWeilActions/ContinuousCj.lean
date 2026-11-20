import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.FirstChernUniqueness

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act.C1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ} {L : LD d} {uM : (Fin L.n → AE F E) → d.G} {ν : Measure (Fin L.n → AE F E)}
  {𝓤 : Set (Fin L.n → AE F E)} {nb : nA σ d.Y d.b → d.G}

def Ap (hU : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) := (hU.1 u).choose

/- English proof (translation)
The claim follows from `(hU.1 u).choose_spec`.
-/
theorem inFrame_uM (hU : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) :
    inFrame d.b (uM u) = Matrix.fromBlocks (Au L u) 0 0 (Ap hU u) := (hU.1 u).choose_spec

/- English proof (translation)
Use `blk_unique d (A₂ := Ap hU u * Ap hU v) (inFrame_uM hU (u + v)) ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, inFrame_uM hU, inFrame_uM hU, Matrix.fromBlocks_multiply]`. Simplify using `only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Au_mul]`.
-/
theorem uM_add (hU : L.UData uM ν 𝓤) (u v : Fin L.n → AE F E) : uM (u + v) = uM u * uM v := by
  refine blk_unique d (A₂ := Ap hU u * Ap hU v) (inFrame_uM hU (u + v)) ?_
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, inFrame_uM hU, inFrame_uM hU, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Au_mul]

/- English proof (translation)
Use `blk_unique d (A₂ := 1) (inFrame_uM hU 0) ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.EisBL.DoubledParabolic.inFrame_one, Au_zero, Matrix.fromBlocks_one]`.
-/
theorem uM_zero (hU : L.UData uM ν 𝓤) : uM 0 = 1 := by
  refine blk_unique d (A₂ := 1) (inFrame_uM hU 0) ?_
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_one, Au_zero, Matrix.fromBlocks_one]

/- English proof (translation)
The claim follows from `eq_inv_of_mul_eq_one_left (by rw [← uM_add hU, neg_add_cancel, uM_zero hU])`.
-/
theorem uM_neg (hU : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) : uM (-u) = (uM u)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← uM_add hU, neg_add_cancel, uM_zero hU])

/- English proof (translation)
Establish `h` using `congrArg (inFrame d.b) (show uM (-u) * uM u = 1 by rw [← uM_add hU, neg_add_cancel, uM_zero hU])`. Rewrite `h` using `[GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, inFrame_uM hU, inFrame_uM hU, Matrix.fromBlocks_multiply, GlobalTheory.EisBL.DoubledParabolic.inFrame_one, ← Matrix.fromBlocks_one]`. Simplify using `only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at h`. Conclude with `(Matrix.fromBlocks_inj.1 h).2.2.2`.
-/
theorem Ap_neg_mul (hU : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) : Ap hU (-u) * Ap hU u = 1 := by
  have h := congrArg (inFrame d.b) (show uM (-u) * uM u = 1 by rw [← uM_add hU, neg_add_cancel, uM_zero hU])
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, inFrame_uM hU, inFrame_uM hU, Matrix.fromBlocks_multiply,
    GlobalTheory.EisBL.DoubledParabolic.inFrame_one, ← Matrix.fromBlocks_one] at h
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at h
  exact (Matrix.fromBlocks_inj.1 h).2.2.2

/- English proof (translation)
Rewrite using `[GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, ← uM_neg hU, inFrame_uM hU, inFrame_uM hU, hN β, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]`. Simplify using `only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Au_mul, neg_add_cancel, Au_zero, Ap_neg_mul hU]`.
-/
theorem frame_conj (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    inFrame d.b ((uM u)⁻¹ * nb β * uM u) = Matrix.fromBlocks 1 (Au L (-u) * β.1 * Ap hU u) 0 1 := by
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, ← uM_neg hU, inFrame_uM hU, inFrame_uM hU, hN β,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Au_mul, neg_add_cancel, Au_zero,
    Ap_neg_mul hU]

/- English proof (translation)
The claim follows from `AddSubgroup.subset_closure ⟨_, frame_conj hU hN u β⟩`.
-/
theorem cj_mem (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    Au L (-u) * β.1 * Ap hU u ∈ nA σ d.Y d.b :=
  AddSubgroup.subset_closure ⟨_, frame_conj hU hN u β⟩

def cj (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) : nA σ d.Y d.b →+ nA σ d.Y d.b where
  toFun β := ⟨_, cj_mem hU hN u β⟩
  map_zero' := Subtype.ext (by simp)
  map_add' β β' := Subtype.ext (by simp [Matrix.mul_add, Matrix.add_mul])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cj_val (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    (cj hU hN u β).1 = Au L (-u) * β.1 * Ap hU u := rfl

/- English proof (translation)
Apply `kunf.inFrame_injective d.b` to reduce the goal to its premises. Rewrite using `[frame_conj hU hN, hN]`. Both sides reduce to the same expression.
-/
theorem nb_cj (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    nb (cj hU hN u β) = (uM u)⁻¹ * nb β * uM u := by
  apply kunf.inFrame_injective d.b
  rw [frame_conj hU hN, hN]
  rfl

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Establish `h1 : Au L u * Au L (-u) = 1` using `by rw [Au_mul, add_neg_cancel, Au_zero]`. Establish `h2 : Ap hU u * Ap hU (-u) = 1` using `by simpa using Ap_neg_mul hU (-u)`. Rewrite using `[cj_val, cj_val, neg_neg]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem cj_inv (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    cj hU hN (-u) (cj hU hN u β) = β := by
  apply Subtype.ext
  have h1 : Au L u * Au L (-u) = 1 := by rw [Au_mul, add_neg_cancel, Au_zero]
  have h2 : Ap hU u * Ap hU (-u) = 1 := by simpa using Ap_neg_mul hU (-u)
  rw [cj_val, cj_val, neg_neg]
  calc Au L u * (Au L (-u) * β.1 * Ap hU u) * Ap hU (-u)
      = (Au L u * Au L (-u)) * β.1 * (Ap hU u * Ap hU (-u)) := by simp only [Matrix.mul_assoc]
    _ = β.1 := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

/- English proof (translation)
The claim follows from `((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const).subtype_mk _`.
-/
theorem continuous_cj (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) :
    Continuous (cj hU hN u) :=
  ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const).subtype_mk _

def cjE (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) : nA σ d.Y d.b ≃ₜ+ nA σ d.Y d.b where
  toFun := cj hU hN u
  invFun := cj hU hN (-u)
  left_inv β := cj_inv hU hN u β
  right_inv β := by simpa using cj_inv hU hN (-u) β
  map_add' := map_add _
  continuous_toFun := continuous_cj hU hN u
  continuous_invFun := continuous_cj hU hN (-u)

end PositivityTheory.SiegelWeilFormula.Act.C1

end
