import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockCentre
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
open scoped TensorProduct

namespace GlobalTheory.LeviBlockExponent

/- English proof (translation)
Unfold `modExp`. Simplify using `only [Fintype.card_fin]`. Establish `h1 : (∑ b ∈ Finset.univ.filter (fun b : Fin (i + 2) => (⟨i, by omega⟩ : Fin (i + 2)) < b), (blockSizes₂ n i b : ℤ)) = (n : ℤ) - i - 1`. Establish `: Finset.univ.filter (fun b : Fin (i + 2) => (⟨i, by omega⟩ : Fin (i + 2)) < b) = {Fin.last (i + 1)}`. Use extensionality with `b`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.lt_def, Fin.ext_iff, Fin.val_last]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[this, Finset.sum_singleton]`. Simplify using `only [blockSizes₂, Fin.val_last]`. Rewrite using `[if_neg (by omega)]`.

Move the coercions through the operations in `[show i + 1 ≤ n from h]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : (∑ b ∈ Finset.univ.filter (fun b : Fin (i + 2) => b < (⟨i, by omega⟩ : Fin (i + 2))), (blockSizes₂ n i b : ℤ)) = i`. Rewrite using `[Finset.sum_congr rfl (g := fun _ => (1 : ℤ)) (fun b hb => by`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at hb`.

Simplify using `only [blockSizes₂]; rw [if_pos (by omega)]; simp)]`. Simplify using `only [Finset.sum_const, smul_eq_mul, mul_one]`. Establish `: Finset.univ.filter (fun b : Fin (i + 2) => b < (⟨i, by omega⟩ : Fin (i + 2))) = (Finset.univ.filter (fun b : Fin (i + 2) => (b : ℕ) < i))`. Use extensionality with `b`. Simplify using `[Fin.lt_def]`.

Rewrite using `[this]`. Establish `hc : (Finset.univ.filter (fun b : Fin (i + 2) => (b : ℕ) < i)).card = i`. Rewrite using `[Fin.card_filter_val_lt]`. Use linear arithmetic over natural numbers and integers. Simplify using `[hc]`.

Rewrite using `[h1, h2]`.
-/
theorem modExp_position (n i : ℕ) (h : i + 1 ≤ n) :
    modExp (fun j : Fin (i + 2) => Fin (blockSizes₂ n i j)) (⟨i, by omega⟩ : Fin (i + 2)) =
      ((n : ℤ) - i - 1) - i := by
  unfold modExp
  simp only [Fintype.card_fin]
  have h1 : (∑ b ∈ Finset.univ.filter (fun b : Fin (i + 2) => (⟨i, by omega⟩ : Fin (i + 2)) < b),
      (blockSizes₂ n i b : ℤ)) = (n : ℤ) - i - 1 := by
    have : Finset.univ.filter (fun b : Fin (i + 2) => (⟨i, by omega⟩ : Fin (i + 2)) < b) = {Fin.last (i + 1)} := by
      ext b; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.lt_def,
        Fin.ext_iff, Fin.val_last]
      omega
    rw [this, Finset.sum_singleton]
    simp only [blockSizes₂, Fin.val_last]
    rw [if_neg (by omega)]
    push_cast [show i + 1 ≤ n from h]
    ring
  have h2 : (∑ b ∈ Finset.univ.filter (fun b : Fin (i + 2) => b < (⟨i, by omega⟩ : Fin (i + 2))),
      (blockSizes₂ n i b : ℤ)) = i := by
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℤ)) (fun b hb => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at hb
      simp only [blockSizes₂]; rw [if_pos (by omega)]; simp)]
    simp only [Finset.sum_const, smul_eq_mul, mul_one]
    have : Finset.univ.filter (fun b : Fin (i + 2) => b < (⟨i, by omega⟩ : Fin (i + 2))) =
        (Finset.univ.filter (fun b : Fin (i + 2) => (b : ℕ) < i)) := by
      ext b; simp [Fin.lt_def]
    rw [this]
    have hc : (Finset.univ.filter (fun b : Fin (i + 2) => (b : ℕ) < i)).card = i := by
      rw [Fin.card_filter_val_lt]; omega
    simp [hc]
  rw [h1, h2]

/- English proof (translation)
Rewrite using `[deltaHalf_apply, Finset.prod_eq_single (⟨i, by omega⟩ : Fin (i + 2))]`. Establish `hd : Matrix.GeneralLinearGroup.det (blockScalar₂ k n i ϖ ⟨i, by omega⟩) = ϖ`. Rewrite using `[blockScalar₂, Pi.mulSingle_eq_same, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]`. Establish `: blockSizes₂ n i (⟨i, by omega⟩ : Fin (i + 2)) = 1` using `by simp [blockSizes₂]`. Rewrite using `[this, pow_one]`.

Rewrite using `[hd, modExp_position n i h]`. Establish `: ((((n : ℤ) - i - 1 - i : ℤ) : ℂ) / 2) = (((((n : ℝ) - 1) / 2 - (i : ℝ)) : ℝ) : ℂ)` using `by push_cast; ring`. Rewrite using `[this, val_absPow_ofReal]`. Introduce `b _ hb`. Establish `: blockScalar₂ k n i ϖ b = 1` using `by simp [blockScalar₂, Pi.mulSingle_eq_of_ne hb]`.

Rewrite using `[this, map_one, map_one]`. Introduce `h'`. Conclude with `absurd (Finset.mem_univ _) h'`.
-/
theorem deltaHalf_positionElt (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n i : ℕ) (h : i + 1 ≤ n) (ϖ : kˣ) :
    ((deltaHalf k (fun j : Fin (i + 2) => Fin (blockSizes₂ n i j)) (blockScalar₂ k n i ϖ) : ℂˣ) : ℂ) =
      ((nabs k ϖ ^ (((n : ℝ) - 1) / 2 - (i : ℝ)) : ℝ) : ℂ) := by
  rw [deltaHalf_apply, Finset.prod_eq_single (⟨i, by omega⟩ : Fin (i + 2))]
  · have hd : Matrix.GeneralLinearGroup.det (blockScalar₂ k n i ϖ ⟨i, by omega⟩) = ϖ := by
      rw [blockScalar₂, Pi.mulSingle_eq_same, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]
      have : blockSizes₂ n i (⟨i, by omega⟩ : Fin (i + 2)) = 1 := by simp [blockSizes₂]
      rw [this, pow_one]
    rw [hd, modExp_position n i h]
    have : ((((n : ℤ) - i - 1 - i : ℤ) : ℂ) / 2) = (((((n : ℝ) - 1) / 2 - (i : ℝ)) : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, val_absPow_ofReal]
  · intro b _ hb
    have : blockScalar₂ k n i ϖ b = 1 := by simp [blockScalar₂, Pi.mulSingle_eq_of_ne hb]
    rw [this, map_one, map_one]
  · intro h'; exact absurd (Finset.mem_univ _) h'

end GlobalTheory.LeviBlockExponent
