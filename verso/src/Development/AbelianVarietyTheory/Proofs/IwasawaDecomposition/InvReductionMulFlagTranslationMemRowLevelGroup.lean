import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsDeco
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryFiniteAdelicPointAsMatrixMemFlagIwahori
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.RowDeco

/- English proof (translation)
Introduce `i _` and use `h i`.
-/
theorem inv_mul_mem_pi {ι : Type} {G : ι → Type} [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i)) (a b : ∀ i, G i)
    (h : ∀ i, (a i)⁻¹ * b i ∈ H i) : a⁻¹ * b ∈ Subgroup.pi Set.univ H := fun i _ => h i

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Both sides reduce to the same expression.
-/
theorem reindex_finCongr_rfl {κ : Type} [CommRing κ] {a : ℕ} (y : GL (Fin a) κ) :
    Units.map (Matrix.reindexAlgEquiv κ κ (finCongr (rfl : a = a))).toMonoidHom y = y := by
  apply Units.ext
  ext i j
  rfl

/- English proof (translation)
Unfold `Formalism.L2.DIV.blkOf`. Use `split_ifs with hi`. Conclude with `Formalism.L2.Col.coarse_of_lt hi`. Rewrite using `[Formalism.L2.Col.coarse_of_le (Nat.not_lt.mp hi)]`. Establish `hi2` using `i.2`.

Establish `ht : 0 < t`. Break down `Nat.eq_zero_or_pos t with h0 | h0` into its components or cases. Substitute `h0` using the available equality. Simplify using `at hn`. Use linear arithmetic over natural numbers and integers.

Conclude with `h0`. Rewrite using `[Formalism.L2.Col.blkIdx_replicate ht m _ (by omega)]`.
-/
theorem coarse_eq_blkOf {a r t m : ℕ} (hn : a = r + m * t) (i : Fin a) :
    Formalism.L2.Col.coarse r (List.replicate m t) i.val = Formalism.L2.DIV.blkOf r t i := by
  unfold Formalism.L2.DIV.blkOf
  split_ifs with hi
  · exact Formalism.L2.Col.coarse_of_lt hi
  · rw [Formalism.L2.Col.coarse_of_le (Nat.not_lt.mp hi)]
    have hi2 := i.2
    have ht : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · subst h0
        simp at hn
        omega
      · exact h0
    rw [Formalism.L2.Col.blkIdx_replicate ht m _ (by omega)]

/- English proof (translation)
Unfold `Formalism.L2.DIV.blk2`. Use `split_ifs with hi`. Conclude with `Formalism.L2.Col.coarse_of_lt hi`. Rewrite using `[Formalism.L2.Col.coarse_of_le (Nat.not_lt.mp hi)]`. Establish `hi2` using `i.2`.

Establish `: i.val - r < b` using `by omega`. Simplify using `[Formalism.L2.Col.blkIdx, this]`.
-/
theorem coarseBlockIndex_eq_twoBlock {a r b : ℕ} (hn : a = r + b) (i : Fin a) :
    Formalism.L2.Col.coarse r [b] i.val = Formalism.L2.DIV.blk2 r i := by
  unfold Formalism.L2.DIV.blk2
  split_ifs with hi
  · exact Formalism.L2.Col.coarse_of_lt hi
  · rw [Formalism.L2.Col.coarse_of_le (Nat.not_lt.mp hi)]
    have hi2 := i.2
    have : i.val - r < b := by omega
    simp [Formalism.L2.Col.blkIdx, this]

/- English proof (translation)
Substitute `h` using the available equality. Rewrite using `[reindex_finCongr_rfl]`. Establish `hy' : y ∈ Formalism.L2.Col.blockUT _ κ r (List.replicate m t)`. Introduce `i j hij`. Apply `hy` to reduce the goal to its premises.

Establish `hij' : Formalism.L2.Col.coarse r (List.replicate m t) j.val < Formalism.L2.Col.coarse r (List.replicate m t) i.val` using `hij`. Rewrite `hij'` using `[coarse_eq_blkOf hn, coarse_eq_blkOf hn]`. Conclude with `hij'`. Establish `hy2 : y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)` using `Formalism.L2.DIV.blockTri_blkOf_le r t hy`. Use `Formalism.L2.Col.mem_HK.2 ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hy') (Formalism.L2.Col.diagEmb_mem_blockUT hrn _ _), fun i j hi hj => ?_⟩` and prove the remaining obligations.

Set `Y : Formalism.L2.Col.blockUT _ κ r (List.replicate m t)` to `⟨y, hy'⟩`. Set `Dd : Formalism.L2.Col.blockUT _ κ r (List.replicate m t)` to `⟨_, Formalism.L2.Col.diagEmb_mem_blockUT hrn (List.replicate m t) (Formalism.L2.DIV.upperLeftBlock hra y)⟩`. Establish `hD : Formalism.L2.Col.blk0 _ κ hrn (List.replicate m t) Dd = Formalism.L2.DIV.upperLeftBlock hra y`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Formalism.L2.Col.blockZero_val]`.

Use extensionality with `i' j'`. Conclude with `Formalism.L2.Col.diagMat_of_lt _ (show (Fin.castLE hrn i').val < r from i'.2) (show (Fin.castLE hrn j').val < r from j'.2)`. Establish `hY : Formalism.L2.Col.blk0 _ κ hrn (List.replicate m t) Y = Formalism.L2.DIV.upperLeftBlock hra y`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Formalism.L2.Col.blockZero_val, Formalism.L2.DIV.upper_block_val_submatrix hra hy2]`.

Both sides reduce to the same expression. Establish `h1 : Formalism.L2.Col.blk0 _ κ hrn (List.replicate m t) (Y⁻¹ * Dd) = 1`. Rewrite using `[map_mul, map_inv, hD, hY, inv_mul_cancel]`. Establish `h2` using `congrArg (fun g : GL (Fin r) κ => (g : Matrix (Fin r) (Fin r) κ) ⟨i.val, hi⟩ ⟨j.val, hj⟩) h1`. Simplify using `only [Formalism.L2.Col.blockZero_val, Units.val_one] at h2`.

Establish `h3 : ((y⁻¹ * Formalism.L2.Col.diagEmb κ hrn (Formalism.L2.DIV.upperLeftBlock hra y) : GL _ κ) : Matrix _ _ κ) i j = (1 : Matrix (Fin r) (Fin r) κ) ⟨i.val, hi⟩ ⟨j.val, hj⟩` using `h2`. Rewrite using `[h3]`. Simplify using `only [Matrix.one_apply, Fin.ext_iff]`.
-/
theorem reindex_inv_mul_diag_mem_HK {κ : Type} [CommRing κ] {a n r t m : ℕ} (h : a = n) (hn : n = r + m * t) (hra : r ≤ a)
    (hrn : r ≤ n) (y : GL (Fin a) κ) (hy : y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t)) :
    (Units.map (Matrix.reindexAlgEquiv κ κ (finCongr h)).toMonoidHom y)⁻¹ *
        Formalism.L2.Col.diagEmb κ hrn (Formalism.L2.DIV.upperLeftBlock hra y) ∈ Formalism.L2.Col.HK n κ r (List.replicate m t) := by
  subst h
  rw [reindex_finCongr_rfl]
  have hy' : y ∈ Formalism.L2.Col.blockUT _ κ r (List.replicate m t) := by
    intro i j hij
    apply hy
    have hij' : Formalism.L2.Col.coarse r (List.replicate m t) j.val < Formalism.L2.Col.coarse r (List.replicate m t) i.val := hij
    rw [coarse_eq_blkOf hn, coarse_eq_blkOf hn] at hij'
    exact hij'
  have hy2 : y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) := Formalism.L2.DIV.blockTri_blkOf_le r t hy
  refine Formalism.L2.Col.mem_HK.2 ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hy')
    (Formalism.L2.Col.diagEmb_mem_blockUT hrn _ _), fun i j hi hj => ?_⟩
  let Y : Formalism.L2.Col.blockUT _ κ r (List.replicate m t) := ⟨y, hy'⟩
  let Dd : Formalism.L2.Col.blockUT _ κ r (List.replicate m t) :=
    ⟨_, Formalism.L2.Col.diagEmb_mem_blockUT hrn (List.replicate m t) (Formalism.L2.DIV.upperLeftBlock hra y)⟩
  have hD : Formalism.L2.Col.blk0 _ κ hrn (List.replicate m t) Dd = Formalism.L2.DIV.upperLeftBlock hra y := by
    apply Units.ext
    rw [Formalism.L2.Col.blockZero_val]
    ext i' j'
    exact Formalism.L2.Col.diagMat_of_lt _ (show (Fin.castLE hrn i').val < r from i'.2) (show (Fin.castLE hrn j').val < r from j'.2)
  have hY : Formalism.L2.Col.blk0 _ κ hrn (List.replicate m t) Y = Formalism.L2.DIV.upperLeftBlock hra y := by
    apply Units.ext
    rw [Formalism.L2.Col.blockZero_val, Formalism.L2.DIV.upper_block_val_submatrix hra hy2]
    rfl
  have h1 : Formalism.L2.Col.blk0 _ κ hrn (List.replicate m t) (Y⁻¹ * Dd) = 1 := by
    rw [map_mul, map_inv, hD, hY, inv_mul_cancel]
  have h2 := congrArg (fun g : GL (Fin r) κ => (g : Matrix (Fin r) (Fin r) κ) ⟨i.val, hi⟩ ⟨j.val, hj⟩) h1
  simp only [Formalism.L2.Col.blockZero_val, Units.val_one] at h2
  have h3 : ((y⁻¹ * Formalism.L2.Col.diagEmb κ hrn (Formalism.L2.DIV.upperLeftBlock hra y) : GL _ κ) : Matrix _ _ κ) i j =
      (1 : Matrix (Fin r) (Fin r) κ) ⟨i.val, hi⟩ ⟨j.val, hj⟩ := h2
  rw [h3]
  simp only [Matrix.one_apply, Fin.ext_iff]

/- English proof (translation)
Substitute `h` using the available equality. Rewrite using `[reindex_finCongr_rfl, mul_one]`. Use `Subgroup.inv_mem _ ?_` and prove the remaining obligations. Introduce `i j hij`. Apply `hy` to reduce the goal to its premises.

Establish `hij' : Formalism.L2.Col.coarse r [b] j.val < Formalism.L2.Col.coarse r [b] i.val` using `hij`. Rewrite `hij'` using `[coarseBlockIndex_eq_twoBlock hn, coarseBlockIndex_eq_twoBlock hn]`. Conclude with `hij'`.
-/
theorem reindex_inv_mem_HQ {κ : Type} [CommRing κ] {a n r b : ℕ} (h : a = n) (hn : n = r + b) (y : GL (Fin a) κ)
    (hy : y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) :
    (Units.map (Matrix.reindexAlgEquiv κ κ (finCongr h)).toMonoidHom y)⁻¹ * 1 ∈ Formalism.L2.Col.blockUT n κ r [b] := by
  subst h
  rw [reindex_finCongr_rfl, mul_one]
  refine Subgroup.inv_mem _ ?_
  intro i j hij
  apply hy
  have hij' : Formalism.L2.Col.coarse r [b] j.val < Formalism.L2.Col.coarse r [b] i.val := hij
  rw [coarseBlockIndex_eq_twoBlock hn, coarseBlockIndex_eq_twoBlock hn] at hij'
  exact hij'

end GlobalTheory.Mem.R3.RowDeco

namespace GlobalTheory.Mem.R3.RowDeco
open GlobalTheory.Mem.R3.RowAd

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `X px I U L eG hI hL hG t q hz`. Apply `inv_mul_mem_pi` to reduce the goal to its premises. Introduce `w`. Use `show _ ∈ (Formalism.L2.Col.rowTyKK I.Ch I.sel t.1 w).H`. Rewrite using `[redG_ptE X I L hL t q hz w]`.

Establish `hQ` using `RowAct.parLev_of_Q X.toD7.sp.X' L.βX (L.datXt t) q`. Distinguish the cases in `hw : w.1 ∈ (X.B.primes px).vGs`. Rewrite using `[Formalism.L2.Col.rowTyKK, Formalism.L2.Col.LevFam.glue_of_mem _ _ w hw]`. Establish `hPg : w.1 ∈ L.Pg` using `by rw [hL.Pg]; exact hw`. Establish `hPg' : w.1 ∈ (L.datXt t).Pg` using `hPg`.

Establish `hy` using `Formalism.L2.DIV.parLev_g hQ hPg'`. Establish `hg0 : ∀ g : Gc X.B px, Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_X' X.B.R) g w = Formalism.L2.Col.diagEmb (𝓞 X.B.fields.E ⧸ w.1.asIdeal) (Formalism.L2.Col.r_le_X' X.B.R) (g ⟨w.1, hw⟩)` using `fun g => by`. Rewrite using `[Formalism.L2.Col.unipotentGroupBlockEmbedding, MonoidHom.comp_apply, Formalism.L2.Col.extGLG_of_mem _ w hw]`. Both sides reduce to the same expression. Rewrite using `[hg0]`.

Establish `hgg : ∀ z, (eG.symm z) ⟨w.1, hw⟩ = z ⟨w.1, hPg⟩` using `fun z => by`. Rewrite using `[← hG (eG.symm z) w.1 hw hPg, MulEquiv.apply_symm_apply]`. Establish `key` using `reindex_inv_mul_diag_mem_HK (rank_X' X) (Formalism.L2.Col.rank_X'_eq X.B.R) (L.datXt t).hr (Formalism.L2.Col.r_le_X' X.B.R) _ hy`. Apply the tactic sequence `convert key using 3 <;> first | rfl | exact heq_of_eq (hgg _) | exact hgg _`. Establish `hwQ : w.1 ∈ Formalism.L2.Col.QE I.sel (t.1 : Formalism.L2.DIV.Chr _ _ _)` using `by classical`.

Conclude with `(Finset.mem_union.1 w.2).resolve_left hw`. Establish `e : I.Q (ixOf I U t) = Formalism.L2.Col.QE I.sel (t.1 : Formalism.L2.DIV.Chr _ _ _)`. Simplify using `only [ColIn.Q, tup_ixOf]`. Establish `hQt : w.1 ∈ L.Q t`. Rewrite using `[hL.Q t, e]`.

Conclude with `hwQ`. Establish `hQt' : w.1 ∈ (L.datXt t).Q` using `hQt`. Establish `hy` using `Formalism.L2.DIV.parLev_q hQ hQt'`. Rewrite using `[Formalism.L2.Col.rowTyKK, Formalism.L2.Col.LevFam.glue_of_not _ _ w hw]`. Establish `hg0 : ∀ g : Gc X.B px, Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_X' X.B.R) g w = 1` using `fun g => by`.

Rewrite using `[Formalism.L2.Col.unipotentGroupBlockEmbedding, MonoidHom.comp_apply, Formalism.L2.Col.extGLG_of_not _ w hw]`. Rewrite using `[hg0]`. Conclude with `reindex_inv_mem_HQ (rank_X' X) (Formalism.L2.Col.rank_X'_eq X.B.R) _ hy`.
-/
theorem inv_redG_mul_g0Hat_mem_grp : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r),
    I.Ok → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG →
    ∀ (t : TupU I U) (q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q)
      (hz : RowAd.ptE X (q : Bridge.Gf X.toD7.sp.X') ∈ Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅),
      (((Formalism.L2.Col.redG X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ⟨_, hz⟩)⁻¹ :
        Formalism.L2.Col.GLG X.B.fields.E (X.B.R.N X.B.R.m - 1) (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)) *
        Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_X' X.B.R)
          (eG.symm (rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _))))) ∈ ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp := by
  intro X px I U L eG hI hL hG t q hz
  apply inv_mul_mem_pi
  intro w
  show _ ∈ (Formalism.L2.Col.rowTyKK I.Ch I.sel t.1 w).H
  rw [redG_ptE X I L hL t q hz w]
  have hQ := RowAct.parLev_of_Q X.toD7.sp.X' L.βX (L.datXt t) q
  by_cases hw : w.1 ∈ (X.B.primes px).vGs
  · rw [Formalism.L2.Col.rowTyKK, Formalism.L2.Col.LevFam.glue_of_mem _ _ w hw]
    have hPg : w.1 ∈ L.Pg := by rw [hL.Pg]; exact hw
    have hPg' : w.1 ∈ (L.datXt t).Pg := hPg
    have hy := Formalism.L2.DIV.parLev_g hQ hPg'
    have hg0 : ∀ g : Gc X.B px, Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_X' X.B.R) g w =
        Formalism.L2.Col.diagEmb (𝓞 X.B.fields.E ⧸ w.1.asIdeal) (Formalism.L2.Col.r_le_X' X.B.R) (g ⟨w.1, hw⟩) := fun g => by
      rw [Formalism.L2.Col.unipotentGroupBlockEmbedding, MonoidHom.comp_apply, Formalism.L2.Col.extGLG_of_mem _ w hw]
      rfl
    rw [hg0]
    have hgg : ∀ z, (eG.symm z) ⟨w.1, hw⟩ = z ⟨w.1, hPg⟩ := fun z => by
      rw [← hG (eG.symm z) w.1 hw hPg, MulEquiv.apply_symm_apply]
    have key := reindex_inv_mul_diag_mem_HK (rank_X' X) (Formalism.L2.Col.rank_X'_eq X.B.R) (L.datXt t).hr
      (Formalism.L2.Col.r_le_X' X.B.R) _ hy
    convert key using 3 <;> first | rfl | exact heq_of_eq (hgg _) | exact hgg _
  · have hwQ : w.1 ∈ Formalism.L2.Col.QE I.sel (t.1 : Formalism.L2.DIV.Chr _ _ _) := by
      classical
      exact (Finset.mem_union.1 w.2).resolve_left hw
    have e : I.Q (ixOf I U t) = Formalism.L2.Col.QE I.sel (t.1 : Formalism.L2.DIV.Chr _ _ _) := by
      simp only [ColIn.Q, tup_ixOf]
    have hQt : w.1 ∈ L.Q t := by
      rw [hL.Q t, e]
      exact hwQ
    have hQt' : w.1 ∈ (L.datXt t).Q := hQt
    have hy := Formalism.L2.DIV.parLev_q hQ hQt'
    rw [Formalism.L2.Col.rowTyKK, Formalism.L2.Col.LevFam.glue_of_not _ _ w hw]
    have hg0 : ∀ g : Gc X.B px, Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_X' X.B.R) g w = 1 := fun g => by
      rw [Formalism.L2.Col.unipotentGroupBlockEmbedding, MonoidHom.comp_apply, Formalism.L2.Col.extGLG_of_not _ w hw]
    rw [hg0]
    exact reindex_inv_mem_HQ (rank_X' X) (Formalism.L2.Col.rank_X'_eq X.B.R) _ hy

end GlobalTheory.Mem.R3.RowDeco
