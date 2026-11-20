import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankWeightComponentEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

noncomputable section
namespace GlobalTheory.LiftDiag

section Mat
variable {k : Type} [CommRing k] {n r t : ℕ}

/- English proof (translation)
Simplify using `[rowIx]`.
-/
theorem rowIx_inl (h : r + t = n) (j : Fin r) : ((rowIx h) (Sum.inl j)).val = j.val := by
  simp [rowIx]

/- English proof (translation)
Break down `hx : (rowIx h).symm a with j | j` into its components or cases. It suffices to derive a contradiction. Establish `: a = rowIx h (Sum.inl j)` using `by rw [← hx, Equiv.apply_symm_apply]`. Establish `h2` using `rowIx_inl h j`. Rewrite `h2` using `[← this]`.

Use linear arithmetic over natural numbers and integers. Conclude with `⟨j, rfl⟩`.
-/
theorem symm_lower (h : r + t = n) {a : Fin n} (ha : r ≤ a.val) : ∃ j, (rowIx h).symm a = Sum.inr j := by
  rcases hx : (rowIx h).symm a with j | j
  · exfalso
    have : a = rowIx h (Sum.inl j) := by rw [← hx, Equiv.apply_symm_apply]
    have h2 := rowIx_inl h j
    rw [← this] at h2
    omega
  · exact ⟨j, rfl⟩

/- English proof (translation)
Rewrite using `[Equiv.symm_apply_eq]`. Use `ext`. Rewrite using `[rowIx_inl]`. Both sides reduce to the same expression.
-/
theorem symm_castLE (h : r + t = n) (hr : r ≤ n) (a : Fin r) : (rowIx h).symm (Fin.castLE hr a) = Sum.inl a := by
  rw [Equiv.symm_apply_eq]
  ext
  rw [rowIx_inl]
  rfl

/- English proof (translation)
Take `⟨j, hj⟩` from `symm_lower h ha`. Rewrite using `[Matrix.submatrix_apply, hj]`. Establish `e1 : (1 : Matrix (Fin n) (Fin n) k) a b = (1 : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k) ((rowIx h).symm a) ((rowIx h).symm b)`. Simplify using `only [Matrix.one_apply, (rowIx h).symm.injective.eq_iff]`. Rewrite using `[e1, hj]`.

Break down `(rowIx h).symm b with j' | j'` into its components or cases. Simplify using `[Matrix.fromBlocks_apply₂₁, Matrix.one_apply]`. Simplify using `[Matrix.fromBlocks_apply₂₂, Matrix.one_apply]`.
-/
theorem lower_row (h : r + t = n) (A : Matrix (Fin r) (Fin r) k) {a : Fin n} (ha : r ≤ a.val) (b : Fin n) :
    ((Matrix.fromBlocks A 0 0 (1 : Matrix (Fin t) (Fin t) k)).submatrix (rowIx h).symm (rowIx h).symm) a b =
      (1 : Matrix (Fin n) (Fin n) k) a b := by
  obtain ⟨j, hj⟩ := symm_lower h ha
  rw [Matrix.submatrix_apply, hj]
  have e1 : (1 : Matrix (Fin n) (Fin n) k) a b =
      (1 : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k) ((rowIx h).symm a) ((rowIx h).symm b) := by
    simp only [Matrix.one_apply, (rowIx h).symm.injective.eq_iff]
  rw [e1, hj]
  rcases (rowIx h).symm b with j' | j'
  · simp [Matrix.fromBlocks_apply₂₁, Matrix.one_apply]
  · simp [Matrix.fromBlocks_apply₂₂, Matrix.one_apply]

/- English proof (translation)
Introduce `i j hij`. Establish `hi : r ≤ i.val`. Assume the negation of the conclusion as `hc`. Rewrite `hij` using `[hb i (by omega)]`. Use linear arithmetic over natural numbers and integers.

Use `show (g : Matrix (Fin n) (Fin n) k) i j = 0`. Rewrite using `[hg, lower_row h A hi, Matrix.one_apply_ne]`. Introduce and unpack `rfl`. Conclude with `lt_irrefl _ hij`.
-/
theorem mem_blockTri_diag (h : r + t = n) (A : Matrix (Fin r) (Fin r) k) {b : Fin n → ℕ}
    (hb : ∀ a : Fin n, a.val < r → b a = 0) (g : GL (Fin n) k)
    (hg : (g : Matrix (Fin n) (Fin n) k) =
      (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin t) (Fin t) k)).submatrix (rowIx h).symm (rowIx h).symm) :
    g ∈ blockTri b := by
  intro i j hij
  have hi : r ≤ i.val := by
    by_contra hc
    rw [hb i (by omega)] at hij
    omega
  show (g : Matrix (Fin n) (Fin n) k) i j = 0
  rw [hg, lower_row h A hi, Matrix.one_apply_ne]
  rintro rfl
  exact lt_irrefl _ hij

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[diag_block_det_val c (mem_blockTri_diag h A hb g hg), Units.val_one]`. Establish `: (g : Matrix (Fin n) (Fin n) k).submatrix (Subtype.val : {a : Fin n // b a = c} → Fin n) (Subtype.val : {a : Fin n // b a = c} → Fin n) = 1`. Use extensionality with `x y`. Establish `hx : r ≤ x.1.val`.

Assume the negation of the conclusion as `hh`. Conclude with `hc (x.2.symm.trans (hb _ (by omega)))`. Rewrite using `[Matrix.submatrix_apply, hg, lower_row h A hx]`. Simplify using `only [Matrix.one_apply, Subtype.ext_iff]`. Rewrite using `[this, Matrix.det_one]`.
-/
theorem blockDiagonalPart_blockDiagOne_reindexed_eq_one (h : r + t = n) (A : Matrix (Fin r) (Fin r) k) {b : Fin n → ℕ}
    (hb : ∀ a : Fin n, a.val < r → b a = 0) (g : GL (Fin n) k)
    (hg : (g : Matrix (Fin n) (Fin n) k) =
      (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin t) (Fin t) k)).submatrix (rowIx h).symm (rowIx h).symm)
    {c : ℕ} (hc : c ≠ 0) : dBlk b c g = 1 := by
  apply Units.ext
  rw [diag_block_det_val c (mem_blockTri_diag h A hb g hg), Units.val_one]
  have : (g : Matrix (Fin n) (Fin n) k).submatrix (Subtype.val : {a : Fin n // b a = c} → Fin n) (Subtype.val : {a : Fin n // b a = c} → Fin n) = 1 := by
    ext x y
    have hx : r ≤ x.1.val := by
      by_contra hh
      exact hc (x.2.symm.trans (hb _ (by omega)))
    rw [Matrix.submatrix_apply, hg, lower_row h A hx]
    simp only [Matrix.one_apply, Subtype.ext_iff]
  rw [this, Matrix.det_one]

/- English proof (translation)
Establish `hb : ∀ a : Fin n, a.val < r → blk2 r a = 0` using `fun a ha => by simp [blk2, ha]`. Rewrite using `[upper_block_val_submatrix hr (mem_blockTri_diag h A hb g hg), hg]`. Use extensionality with `a b`. Simplify using `only [Matrix.submatrix_apply, symm_castLE h hr, Matrix.fromBlocks_apply₁₁]`.
-/
theorem topLeftBlock_blockDiagOne_reindexed_eq (h : r + t = n) (hr : r ≤ n) (A : Matrix (Fin r) (Fin r) k) (g : GL (Fin n) k)
    (hg : (g : Matrix (Fin n) (Fin n) k) =
      (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin t) (Fin t) k)).submatrix (rowIx h).symm (rowIx h).symm) :
    ((upperLeftBlock hr g : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) = A := by
  have hb : ∀ a : Fin n, a.val < r → blk2 r a = 0 := fun a ha => by simp [blk2, ha]
  rw [upper_block_val_submatrix hr (mem_blockTri_diag h A hb g hg), hg]
  ext a b
  simp only [Matrix.submatrix_apply, symm_castLE h hr, Matrix.fromBlocks_apply₁₁]

/- English proof (translation)
Simplify using `[blk2, ha]`.
-/
theorem blockIndexSecond_eq_zero_of_lt (r : ℕ) (a : Fin n) (ha : a.val < r) : blk2 r a = 0 := by simp [blk2, ha]

/- English proof (translation)
Simplify using `[blkOf, ha]`.
-/
theorem blkOf_low (r t : ℕ) (a : Fin n) (ha : a.val < r) : blkOf r t a = 0 := by simp [blkOf, ha]

end Mat

end GlobalTheory.LiftDiag

namespace GlobalTheory.LiftDiag

/- English proof (translation)
Introduce `D G _ _ Pl0 T A Ks _ _ _ R i t PP hPP g hg κ hκ hSt hN hoth`. Establish `memb : ∀ b : Fin (Vc D i).rank → ℕ, (∀ a : Fin (Vc D i).rank, a.val < D.R.r → b a = 0) → ∀ PP', PP' ∈ R.Pg ∨ PP' ∈ R.Q t → redFn (R.βV i) PP' (finE (Vc D i) κ) ∈ blockTri b`. Introduce `b hb PP' hP'`. Distinguish the cases in `he : PP' = PP`. Substitute `he` using the available equality.

Conclude with `mem_blockTri_diag (rank_V i) _ hb _ hN`. Rewrite using `[hoth PP' hP' he]`. Conclude with `Subgroup.one_mem _`. Establish `dB : ∀ b : Fin (Vc D i).rank → ℕ, (∀ a : Fin (Vc D i).rank, a.val < D.R.r → b a = 0) → ∀ c : ℕ, c ≠ 0 → ∀ PP', PP' ∈ R.Pg ∨ PP' ∈ R.Q t → dBlk b c (redFn (R.βV i) PP' (finE (Vc D i) κ)) = 1`. Introduce `b hb c hc PP' hP'`.

Distinguish the cases in `he : PP' = PP`. Substitute `he` using the available equality. Conclude with `blockDiagonalPart_blockDiagOne_reindexed_eq_one (rank_V i) _ hb _ hN hc`. Rewrite using `[hoth PP' hP' he]`. Conclude with `blockDiagonalExtendByOnePrimeField_one _ _`.

Use `⟨⟨hκ, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA _ κ, hSt, fun PP' hP' => memb _ (blkOf_low _ _) PP' (Or.inl hP'), fun PP' hP' => memb _ (blockIndexSecond_eq_zero_of_lt _) PP' (Or.inr hP')⟩`. Use function extensionality and compare the values at `PP'`. Take `⟨PP', hP'⟩` from `PP'`. Use `show upperLeftBlock _ (redFn (R.βV i) PP' (finE (Vc D i) κ)) = R.eG g ⟨PP', hP'⟩`.

Distinguish the cases in `he : PP' = PP`. Substitute `he` using the available equality. Apply `Units.ext` to reduce the goal to its premises. Conclude with `topLeftBlock_blockDiagOne_reindexed_eq (rank_V i) _ _ _ hN`. Rewrite using `[hoth PP' (Or.inl hP') he]`.

Establish `h1 : upperLeftBlock (r_le_V i) (1 : GL (Fin (Vc D i).rank) (kP PP')) = 1` using `blockDiagonalExtendByOnePrimeField_one _ _`. Establish `h2 : R.eG g ⟨PP', hP'⟩ = 1` using `hg ⟨PP', hP'⟩ (fun h => he (congrArg Subtype.val h))`. Rewrite using `[h2]`. Conclude with `h1`. Establish `key : levFn (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) κ) = 1`.

Unfold `levFn`. Rewrite using `[Finset.prod_eq_one, Finset.prod_eq_one, mul_one, mul_one]`. Conclude with `(extendOne_of_mem _ (Subgroup.mem_top _)).trans rfl`. Introduce `PP' hP'`. Conclude with `(congrArg _ (dB _ (blockIndexSecond_eq_zero_of_lt _) 1 one_ne_zero PP' (Or.inr hP'))).trans (map_one _)`.

Introduce `PP' hP'`. Conclude with `Finset.prod_eq_one fun c _ => (congrArg _ (dB _ (blkOf_low _ _) (c + 1) (Nat.succ_ne_zero c) PP' (Or.inl hP'))).trans (map_one _)`. Use `show ((levFn (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) κ) : ℂˣ) : ℂ) = 1`. Rewrite using `[key, Units.val_one]`.
-/
theorem lift_diag : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (i : Fin D.R.m) (t : T) (PP : Pl D.host.E) (hPP : PP ∈ R.Pg) (g : G), (∀ PP' : R.Pg, PP' ≠ ⟨PP, hPP⟩ → R.eG g PP' = 1) → ∀ κ : GA D (Vc D i), κ ∈ GfC (Vc D i) → finE (Vc D i) κ ∈ Formalism.L2.DIV.St (R.βV i) → ((redFn (R.βV i) PP (finE (Vc D i) κ) : GL (Fin (Vc D i).rank) (kP PP)) : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) (kP PP)) = (Matrix.fromBlocks ((R.eG g ⟨PP, hPP⟩ : GL (Fin D.R.r) (kP PP)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP)) 0 0 (1 : Matrix (Fin D.R.t) (Fin D.R.t) (kP PP))).submatrix (rowIx (rank_V i)).symm (rowIx (rank_V i)).symm → (∀ PP', PP' ∈ R.Pg ∨ PP' ∈ R.Q t → PP' ≠ PP → redFn (R.βV i) PP' (finE (Vc D i) κ) = 1) → IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) κ ∧ levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ = 1 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i t PP hPP g hg κ hκ hSt hN hoth
  have memb : ∀ b : Fin (Vc D i).rank → ℕ, (∀ a : Fin (Vc D i).rank, a.val < D.R.r → b a = 0) →
      ∀ PP', PP' ∈ R.Pg ∨ PP' ∈ R.Q t → redFn (R.βV i) PP' (finE (Vc D i) κ) ∈ blockTri b := by
    intro b hb PP' hP'
    by_cases he : PP' = PP
    · subst he; exact mem_blockTri_diag (rank_V i) _ hb _ hN
    · rw [hoth PP' hP' he]; exact Subgroup.one_mem _
  have dB : ∀ b : Fin (Vc D i).rank → ℕ, (∀ a : Fin (Vc D i).rank, a.val < D.R.r → b a = 0) → ∀ c : ℕ, c ≠ 0 →
      ∀ PP', PP' ∈ R.Pg ∨ PP' ∈ R.Q t → dBlk b c (redFn (R.βV i) PP' (finE (Vc D i) κ)) = 1 := by
    intro b hb c hc PP' hP'
    by_cases he : PP' = PP
    · subst he; exact blockDiagonalPart_blockDiagOne_reindexed_eq_one (rank_V i) _ hb _ hN hc
    · rw [hoth PP' hP' he]; exact blockDiagonalExtendByOnePrimeField_one _ _
  refine ⟨⟨hκ, ?_, ?_⟩, ?_⟩
  · exact mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA _ κ, hSt,
      fun PP' hP' => memb _ (blkOf_low _ _) PP' (Or.inl hP'), fun PP' hP' => memb _ (blockIndexSecond_eq_zero_of_lt _) PP' (Or.inr hP')⟩
  · funext PP'
    obtain ⟨PP', hP'⟩ := PP'
    show upperLeftBlock _ (redFn (R.βV i) PP' (finE (Vc D i) κ)) = R.eG g ⟨PP', hP'⟩
    by_cases he : PP' = PP
    · subst he; apply Units.ext; exact topLeftBlock_blockDiagOne_reindexed_eq (rank_V i) _ _ _ hN
    · rw [hoth PP' (Or.inl hP') he]
      have h1 : upperLeftBlock (r_le_V i) (1 : GL (Fin (Vc D i).rank) (kP PP')) = 1 := blockDiagonalExtendByOnePrimeField_one _ _
      have h2 : R.eG g ⟨PP', hP'⟩ = 1 := hg ⟨PP', hP'⟩ (fun h => he (congrArg Subtype.val h))
      rw [h2]
      exact h1
  · have key : levFn (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) κ) = 1 := by
      unfold levFn
      rw [Finset.prod_eq_one, Finset.prod_eq_one, mul_one, mul_one]
      · exact (extendOne_of_mem _ (Subgroup.mem_top _)).trans rfl
      · intro PP' hP'
        exact (congrArg _ (dB _ (blockIndexSecond_eq_zero_of_lt _) 1 one_ne_zero PP' (Or.inr hP'))).trans (map_one _)
      · intro PP' hP'
        exact Finset.prod_eq_one fun c _ =>
          (congrArg _ (dB _ (blkOf_low _ _) (c + 1) (Nat.succ_ne_zero c) PP' (Or.inl hP'))).trans (map_one _)
    show ((levFn (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) κ) : ℂˣ) : ℂ) = 1
    rw [key, Units.val_one]

end GlobalTheory.LiftDiag
