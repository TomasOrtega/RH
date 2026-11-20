import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemParLevOfQ
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.LiftBrg.LamKV

/- English proof (translation)
Unfold `Formalism.L2.DIV.blkOf`. Use `split_ifs with hi`. Conclude with `Formalism.L2.Col.coarse_of_lt hi`. Rewrite using `[Formalism.L2.Col.coarse_of_le (Nat.not_lt.mp hi)]`. Establish `hi2` using `i.2`.

Establish `h1 : i.val - r < t` using `by omega`. Establish `h2 : (i.val - r) / t = 0` using `Nat.div_eq_of_lt h1`. Rewrite using `[h2]`. Simplify using `[Formalism.L2.Col.blkIdx, h1]`.
-/
theorem coarse_single_eq_blkOf {a r t : ℕ} (hn : a = r + t) (i : Fin a) :
    Formalism.L2.Col.coarse r [t] i.val = Formalism.L2.DIV.blkOf r t i := by
  unfold Formalism.L2.DIV.blkOf
  split_ifs with hi
  · exact Formalism.L2.Col.coarse_of_lt hi
  · rw [Formalism.L2.Col.coarse_of_le (Nat.not_lt.mp hi)]
    have hi2 := i.2
    have h1 : i.val - r < t := by omega
    have h2 : (i.val - r) / t = 0 := Nat.div_eq_of_lt h1
    rw [h2]
    simp [Formalism.L2.Col.blkIdx, h1]

/- English proof (translation)
Introduce `κ K _ _ a n r t h hn hra hrn y hy χ hz`. Substitute `h` using the available equality. Establish `hc : LiftBrg.castGL (rfl : a = a) y = y`. Use extensionality with `i j`. Simplify using `[LiftBrg.castGL]`.

Establish `hf : (fun i : Fin a => Formalism.L2.Col.coarse r [t] i.val) = Formalism.L2.DIV.blkOf r t`. Use function extensionality and compare the values at `(coarse_single_eq_blkOf hn)`. Establish `hy' : y ∈ Formalism.L2.Col.blockUT a κ r [t]`. Introduce `i j hij`. Apply `hy` to reduce the goal to its premises.

Establish `hij' : (fun i : Fin a => Formalism.L2.Col.coarse r [t] i.val) j < (fun i : Fin a => Formalism.L2.Col.coarse r [t] i.val) i` using `hij`. Rewrite `hij'` using `[hf]`. Conclude with `hij'`. Set `Y : Formalism.L2.Col.blockUT a κ r [t]` to `⟨y, hy'⟩`. Set `Dd : Formalism.L2.Col.blockUT a κ r [t]` to `⟨_, Formalism.L2.Col.diagEmb_mem_blockUT hrn [t] (Formalism.L2.DIV.upperLeftBlock hra y)⟩`.

Establish `hzz : (Subgroup.inclusion (Formalism.L2.Col.HK_le_blockUT a κ r [t]) ⟨_, hz⟩ : Formalism.L2.Col.blockUT a κ r [t]) = Y⁻¹ * Dd`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show (LiftBrg.castGL (rfl : a = a) y)⁻¹ * _ = y⁻¹ * _`. Rewrite using `[hc]`. Establish `hD : Formalism.L2.Col.blkDet a κ (Formalism.L2.Col.coarse r [t]) 1 Dd = 1`.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Formalism.L2.Col.blkDet_val, Units.val_one]`. Establish `: (Dd.1 : Matrix (Fin a) (Fin a) κ).toSquareBlock (fun i => Formalism.L2.Col.coarse r [t] i.val) 1 = 1`. Use extensionality with `i j`. Establish `hi : ¬ i.1.val < r` using `fun hi => by`.

Use `i.2` as an intermediate fact. Simplify using `only [Formalism.L2.Col.coarse_of_lt hi] at this`. Conclude with `absurd this (by decide)`. Rewrite using `[Matrix.toSquareBlock_def, Matrix.of_apply]`. Use `show Formalism.L2.Col.diagMat r a _ i.1 j.1 = _`.

Rewrite using `[Formalism.L2.Col.diagMat_of_not_left _ _ hi]`. Simplify using `only [Matrix.one_apply, Subtype.ext_iff]`. Rewrite using `[this, Matrix.det_one]`. Establish `hY : Formalism.L2.Col.blkDet a κ (Formalism.L2.Col.coarse r [t]) 1 Y = Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) 1 y`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[Formalism.L2.Col.blkDet_val, Formalism.L2.DIV.diag_block_det_val 1 hy]`. Establish `key : ∀ b : Fin a → ℕ, b = Formalism.L2.DIV.blkOf r t → ((y : Matrix (Fin a) (Fin a) κ).toSquareBlock b 1).det = ((y : Matrix (Fin a) (Fin a) κ).submatrix (Subtype.val : {x : Fin a // Formalism.L2.DIV.blkOf r t x = 1} → Fin a) Subtype.val).det`. Introduce and unpack `b rfl`. Both sides reduce to the same expression. Conclude with `key _ hf`.

Rewrite using `[Formalism.L2.Col.lamKV, Formalism.L2.Col.lamK, MonoidHom.comp_apply, hzz, Formalism.L2.Col.detChar_apply]`. Simplify using `only [List.length_singleton, Finset.range_one, Finset.prod_singleton, zero_add]`. Rewrite using `[map_mul, map_inv, hD, mul_one, hY, MonoidHom.inv_apply, map_inv, inv_inv]`.
-/
theorem lamKV_inv_mul_diagEmb : ∀ {κ K : Type} [CommRing κ] [Field K] {a n r t : ℕ} (h : a = n) (hn : n = r + t) (hra : r ≤ a)
    (hrn : r ≤ n) (y : GL (Fin a) κ) (hy : y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t)) (χ : κˣ →* Kˣ)
    (hz : (LiftBrg.castGL h y)⁻¹ * Formalism.L2.Col.diagEmb κ hrn (Formalism.L2.DIV.upperLeftBlock hra y) ∈ Formalism.L2.Col.HKV κ n r t),
    Formalism.L2.Col.lamKV χ n r t ⟨_, hz⟩ = χ (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) 1 y) := by
  intro κ K _ _ a n r t h hn hra hrn y hy χ hz
  subst h
  have hc : LiftBrg.castGL (rfl : a = a) y = y := by
    ext i j
    simp [LiftBrg.castGL]
  have hf : (fun i : Fin a => Formalism.L2.Col.coarse r [t] i.val) = Formalism.L2.DIV.blkOf r t :=
    funext (coarse_single_eq_blkOf hn)
  have hy' : y ∈ Formalism.L2.Col.blockUT a κ r [t] := by
    intro i j hij
    apply hy
    have hij' : (fun i : Fin a => Formalism.L2.Col.coarse r [t] i.val) j < (fun i : Fin a => Formalism.L2.Col.coarse r [t] i.val) i := hij
    rw [hf] at hij'
    exact hij'
  let Y : Formalism.L2.Col.blockUT a κ r [t] := ⟨y, hy'⟩
  let Dd : Formalism.L2.Col.blockUT a κ r [t] :=
    ⟨_, Formalism.L2.Col.diagEmb_mem_blockUT hrn [t] (Formalism.L2.DIV.upperLeftBlock hra y)⟩
  have hzz : (Subgroup.inclusion (Formalism.L2.Col.HK_le_blockUT a κ r [t]) ⟨_, hz⟩ : Formalism.L2.Col.blockUT a κ r [t]) = Y⁻¹ * Dd := by
    apply Subtype.ext
    show (LiftBrg.castGL (rfl : a = a) y)⁻¹ * _ = y⁻¹ * _
    rw [hc]
  have hD : Formalism.L2.Col.blkDet a κ (Formalism.L2.Col.coarse r [t]) 1 Dd = 1 := by
    apply Units.ext
    rw [Formalism.L2.Col.blkDet_val, Units.val_one]
    have : (Dd.1 : Matrix (Fin a) (Fin a) κ).toSquareBlock (fun i => Formalism.L2.Col.coarse r [t] i.val) 1 = 1 := by
      ext i j
      have hi : ¬ i.1.val < r := fun hi => by
        have := i.2
        simp only [Formalism.L2.Col.coarse_of_lt hi] at this
        exact absurd this (by decide)
      rw [Matrix.toSquareBlock_def, Matrix.of_apply]
      show Formalism.L2.Col.diagMat r a _ i.1 j.1 = _
      rw [Formalism.L2.Col.diagMat_of_not_left _ _ hi]
      simp only [Matrix.one_apply, Subtype.ext_iff]
    rw [this, Matrix.det_one]
  have hY : Formalism.L2.Col.blkDet a κ (Formalism.L2.Col.coarse r [t]) 1 Y = Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) 1 y := by
    apply Units.ext
    rw [Formalism.L2.Col.blkDet_val, Formalism.L2.DIV.diag_block_det_val 1 hy]
    have key : ∀ b : Fin a → ℕ, b = Formalism.L2.DIV.blkOf r t →
        ((y : Matrix (Fin a) (Fin a) κ).toSquareBlock b 1).det =
          ((y : Matrix (Fin a) (Fin a) κ).submatrix (Subtype.val : {x : Fin a // Formalism.L2.DIV.blkOf r t x = 1} → Fin a)
            Subtype.val).det := by
      rintro b rfl
      rfl
    exact key _ hf
  rw [Formalism.L2.Col.lamKV, Formalism.L2.Col.lamK, MonoidHom.comp_apply, hzz, Formalism.L2.Col.detChar_apply]
  simp only [List.length_singleton, Finset.range_one, Finset.prod_singleton, zero_add]
  rw [map_mul, map_inv, hD, mul_one, hY, MonoidHom.inv_apply, map_inv, inv_inv]

end GlobalTheory.Mem.R3.LiftBrg.LamKV
