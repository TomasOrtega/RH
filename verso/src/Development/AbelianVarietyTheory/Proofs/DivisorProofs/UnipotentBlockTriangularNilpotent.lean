import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

namespace GlobalTheory.LeviHC.UnipFrame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Unfold `incM`. Conclude with `Matrix.map_mul (f := (inclR (F := F) (E := E) (AF F) : E →+* AE F E))`.
-/
theorem incM_mul' {l m k : ℕ} (A : Matrix (Fin l) (Fin m) E) (B : Matrix (Fin m) (Fin k) E) :
    incM F (A * B) = incM F A * incM F B := by
  unfold incM
  exact Matrix.map_mul (f := (inclR (F := F) (E := E) (AF F) : E →+* AE F E))

/- English proof (translation)
Unfold `incM`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
theorem incM_one' {m : ℕ} : incM F (1 : Matrix (Fin m) (Fin m) E) = 1 := by
  unfold incM
  exact Matrix.map_one _ (map_zero _) (map_one _)

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n n₁ Y H R hQR hRQ u hW`. Use `set Wm : Matrix (Fin (1 + n₁ + 1)) (Fin (1 + n₁ + 1)) (AE F E) := incM F R * (mat u - 1 : Matrix (Fin n) (Fin n) (AE F E)) * incM F (frame H) with hWm`. Establish `hQ : incM F (frame H) * incM F R = 1` using `by rw [← incM_mul', hQR, incM_one']`. Establish `key : (mat u - 1 : Matrix (Fin n) (Fin n) (AE F E)) * incM F (frame H) = incM F (frame H) * Wm`. Rewrite using `[hWm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQ, Matrix.one_mul]`.

Establish `hmv : ∀ v, mat u *ᵥ (incM F (frame H) *ᵥ v) = incM F (frame H) *ᵥ v + incM F (frame H) *ᵥ (Wm *ᵥ v)`. Introduce `v`. Establish `e : mat u = 1 + (mat u - 1 : Matrix (Fin n) (Fin n) (AE F E))` using `by abel`. Rewrite using `[e, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, key, ← Matrix.mulVec_mulVec]`. Use `set x0 : Fin (1 + n₁ + 1) := Fin.castAdd 1 (Fin.castAdd n₁ 0) with hx0`.

Establish `hx : incV F H.x = incM F (frame H) *ᵥ Pi.single x0 1`. Use extensionality with `r`. Rewrite using `[Matrix.mulVec_single]`. Simplify using `[incV, incM, hx0, frame_alt]`. Establish `hWx : Wm *ᵥ Pi.single x0 1 = 0`.

Use extensionality with `i`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.zero_apply]`. Apply `hW` to reduce the goal to its premises. Rewrite using `[hx0, block_matrix_mulVec_basis]`. Use linear arithmetic over natural numbers and integers.

Apply `Subgroup.subset_closure` to reduce the goal to its premises. Use `⟨?_, fun z => ⟨∑ k, Wm x0 (mid k) * z k, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hx, hmv, hWx, Matrix.mulVec_zero, add_zero]`. Set `vz : Fin (1 + n₁ + 1) → AE F E` to `Fin.addCases (Fin.addCases (fun _ => 0) fun k => z k) fun _ => 0`. Establish `hι : incM F H.ι *ᵥ z = incM F (frame H) *ᵥ vz`.

Use extensionality with `r`. Simplify using `only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, vz, Fin.addCases_left, Fin.addCases_right, mul_zero, Finset.sum_const_zero, zero_add, add_zero]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `[incM, frame]`. Establish `hWz : Wm *ᵥ vz = (∑ k, Wm x0 (mid k) * z k) • Pi.single x0 1`.

Establish `hs : ∀ i, (Wm *ᵥ vz) i = ∑ k, Wm i (mid k) * z k`. Introduce `i`. Simplify using `only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, vz, Fin.addCases_left, Fin.addCases_right, mul_zero, Finset.sum_const_zero, zero_add, add_zero]`. Both sides reduce to the same expression. Use extensionality with `i`.

Rewrite using `[hs]`. Proceed by induction on `i using Fin.addCases with`. Consider the case `left i`. Proceed by induction on `i using Fin.addCases with`. Consider the case `left a`.

Establish `ha : a = 0` using `Subsingleton.elim _ _`. Substitute `ha` using the available equality. Simplify using `[hx0]`. Consider the case `right k'`. Establish `hne : (Fin.castAdd 1 (Fin.natAdd 1 k') : Fin (1 + n₁ + 1)) ≠ x0`.

Rewrite using `[hx0]`. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `at this`. Rewrite using `[Pi.smul_apply, Pi.single_eq_of_ne hne, smul_zero]`.

Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hW, zero_mul]`. Use `show blk n₁ (mid k) < blk n₁ (mid k') + 1`. Rewrite using `[blk_mid, blk_mid]`. Use linear arithmetic over natural numbers and integers.

Consider the case `right a`. Establish `hne : (Fin.natAdd (1 + n₁) a : Fin (1 + n₁ + 1)) ≠ x0`. Apply the tactic sequence `rw [hx0]; intro h; have := congrArg Fin.val h; (simp at this) <;> omega`. Rewrite using `[Pi.smul_apply, Pi.single_eq_of_ne hne, smul_zero]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[hW, zero_mul]`. Rewrite using `[blk_mid, blk_y]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hι, hmv, hWz, Matrix.mulVec_smul, ← hx]`.
-/
theorem mem_unip_of_strictBlockTri : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n n₁ : ℕ) (Y : Spc F E n) (H : Plane E n n₁) (R : Matrix (Fin (1 + n₁ + 1)) (Fin n) E), frame H * R = 1 → R * frame H = 1 →
    ∀ u : UA σ Y.J, (∀ i j, blk n₁ j < blk n₁ i + 1 → (incM F R * (mat u - 1 : Matrix (Fin n) (Fin n) (AE F E)) * incM F (frame H) :
        Matrix (Fin (1 + n₁ + 1)) (Fin (1 + n₁ + 1)) (AE F E)) i j = 0) →
      u ∈ unip σ Y H := by
  intro F E _ _ _ _ _ σ n n₁ Y H R hQR hRQ u hW
  set Wm : Matrix (Fin (1 + n₁ + 1)) (Fin (1 + n₁ + 1)) (AE F E) :=
    incM F R * (mat u - 1 : Matrix (Fin n) (Fin n) (AE F E)) * incM F (frame H) with hWm
  have hQ : incM F (frame H) * incM F R = 1 := by rw [← incM_mul', hQR, incM_one']
  have key : (mat u - 1 : Matrix (Fin n) (Fin n) (AE F E)) * incM F (frame H) = incM F (frame H) * Wm := by
    rw [hWm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQ, Matrix.one_mul]
  have hmv : ∀ v, mat u *ᵥ (incM F (frame H) *ᵥ v) = incM F (frame H) *ᵥ v + incM F (frame H) *ᵥ (Wm *ᵥ v) := by
    intro v
    have e : mat u = 1 + (mat u - 1 : Matrix (Fin n) (Fin n) (AE F E)) := by abel
    rw [e, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, key, ← Matrix.mulVec_mulVec]
  set x0 : Fin (1 + n₁ + 1) := Fin.castAdd 1 (Fin.castAdd n₁ 0) with hx0
  have hx : incV F H.x = incM F (frame H) *ᵥ Pi.single x0 1 := by
    ext r
    rw [Matrix.mulVec_single]
    simp [incV, incM, hx0, frame_alt]
  have hWx : Wm *ᵥ Pi.single x0 1 = 0 := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Pi.zero_apply]
    apply hW
    rw [hx0, block_matrix_mulVec_basis]
    omega
  apply Subgroup.subset_closure
  refine ⟨?_, fun z => ⟨∑ k, Wm x0 (mid k) * z k, ?_⟩⟩
  · rw [hx, hmv, hWx, Matrix.mulVec_zero, add_zero]
  · let vz : Fin (1 + n₁ + 1) → AE F E := Fin.addCases (Fin.addCases (fun _ => 0) fun k => z k) fun _ => 0
    have hι : incM F H.ι *ᵥ z = incM F (frame H) *ᵥ vz := by
      ext r
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, vz, Fin.addCases_left, Fin.addCases_right, mul_zero,
        Finset.sum_const_zero, zero_add, add_zero]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [incM, frame]
    have hWz : Wm *ᵥ vz = (∑ k, Wm x0 (mid k) * z k) • Pi.single x0 1 := by
      have hs : ∀ i, (Wm *ᵥ vz) i = ∑ k, Wm i (mid k) * z k := by
        intro i
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, vz, Fin.addCases_left, Fin.addCases_right, mul_zero,
          Finset.sum_const_zero, zero_add, add_zero]
        rfl
      ext i
      rw [hs]
      induction i using Fin.addCases with
      | left i =>
        induction i using Fin.addCases with
        | left a =>
          have ha : a = 0 := Subsingleton.elim _ _
          subst ha
          simp [hx0]
        | right k' =>
          have hne : (Fin.castAdd 1 (Fin.natAdd 1 k') : Fin (1 + n₁ + 1)) ≠ x0 := by
            rw [hx0]; intro h; have := congrArg Fin.val h; simp at this
          rw [Pi.smul_apply, Pi.single_eq_of_ne hne, smul_zero]
          refine Finset.sum_eq_zero fun k _ => ?_
          rw [hW, zero_mul]
          show blk n₁ (mid k) < blk n₁ (mid k') + 1
          rw [blk_mid, blk_mid]
          omega
      | right a =>
        have hne : (Fin.natAdd (1 + n₁) a : Fin (1 + n₁ + 1)) ≠ x0 := by
          rw [hx0]; intro h; have := congrArg Fin.val h; (simp at this) <;> omega
        rw [Pi.smul_apply, Pi.single_eq_of_ne hne, smul_zero]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [hW, zero_mul]
        rw [blk_mid, blk_y]
        omega
    rw [hι, hmv, hWz, Matrix.mulVec_smul, ← hx]

end GlobalTheory.LeviHC.UnipFrame
