import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UGraph

open GlobalTheory.Doubling Matrix

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

/- English proof (translation)
Use `⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, ?_, ?_⟩, rfl⟩` and prove the remaining obligations. Use `Matrix.map_injective (Formalism.UG.intL L).subtype_injective ?_` and prove the remaining obligations. Simplify using `only`. Rewrite using `[Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `x.mul_inv`.

Use `Matrix.map_injective (Formalism.UG.intL L).subtype_injective ?_` and prove the remaining obligations. Simplify using `only`. Rewrite using `[Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `x.inv_mul`.
-/
theorem mem_GLint_of_entries {ι : Type} [Fintype ι] [DecidableEq ι] {x : GL ι L}
    (h1 : ∀ i j, x.1 i j ∈ Formalism.UG.intL L) (h2 : ∀ i j, (x⁻¹).1 i j ∈ Formalism.UG.intL L) :
    x ∈ Formalism.UG.GLint ι (Formalism.UG.intL L) := by
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, ?_, ?_⟩, rfl⟩
  · refine Matrix.map_injective (Formalism.UG.intL L).subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · refine Matrix.map_injective (Formalism.UG.intL L).subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

/- English proof (translation)
Use `show Valued.v ϖ ≤ 1`. Rewrite using `[hU.2.2.2.1, ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]`. Use linear arithmetic over natural numbers and integers.
-/
theorem unif_mem_int {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) : ϖ ∈ Formalism.UG.intL L := by
  show Valued.v ϖ ≤ 1
  rw [hU.2.2.2.1, ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]
  omega

/- English proof (translation)
Establish `h : Formalism.UG.cT σ t.1.1 * Formalism.UG.antiJ L n * t.1.1 = Formalism.UG.antiJ L n` using `t.2`. Establish `h1` using `congrFun (congrFun h i) (Fin.rev i)`. Establish `hJ : Formalism.UG.antiJ L n i (Fin.rev i) = 1`. Simplify using `only [Formalism.UG.antiJ, Fin.val_rev]`. Rewrite using `[if_pos (by omega)]`.

Rewrite `h1` using `[hJ, ht, Formalism.UG.cT, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose, Matrix.mul_diagonal, Matrix.diagonal_mul, hJ]`. Rewrite `h1` using `[map_zpow₀, hU.2.2.1, mul_one, ← zpow_add₀ ϖ.ne_zero]`. Establish `h2` using `congrArg Formalism.UG.ordL h1`. Rewrite `h2` using `[Formalism.UG.P.fSatake_ord_zpow hU.2.2.2.1, ← zpow_zero (ϖ : L), Formalism.UG.P.fSatake_ord_zpow hU.2.2.2.1]`. Use linear arithmetic over natural numbers and integers.
-/
theorem exp_rev {ϖ : Lˣ} {σ : L →+* L} {q n : ℕ} (hU : IsUnramInv (ϖ : L) σ q) {d : Fin n → ℤ} {t : GU σ n}
    (ht : t.1.1 = Matrix.diagonal (fun i => (ϖ : L) ^ d i)) (i : Fin n) : d (Fin.rev i) = -d i := by
  have h : Formalism.UG.cT σ t.1.1 * Formalism.UG.antiJ L n * t.1.1 = Formalism.UG.antiJ L n := t.2
  have h1 := congrFun (congrFun h i) (Fin.rev i)
  have hJ : Formalism.UG.antiJ L n i (Fin.rev i) = 1 := by
    simp only [Formalism.UG.antiJ, Fin.val_rev]
    rw [if_pos (by omega)]
  rw [hJ, ht, Formalism.UG.cT, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose, Matrix.mul_diagonal,
    Matrix.diagonal_mul, hJ] at h1
  rw [map_zpow₀, hU.2.2.1, mul_one, ← zpow_add₀ ϖ.ne_zero] at h1
  have h2 := congrArg Formalism.UG.ordL h1
  rw [Formalism.UG.P.fSatake_ord_zpow hU.2.2.2.1, ← zpow_zero (ϖ : L), Formalism.UG.P.fSatake_ord_zpow hU.2.2.2.1] at h2
  omega

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul, Formalism.UG.antiJ]`. Use `split_ifs with hij`. Establish `: j = Fin.rev i` using `Fin.ext (by rw [Fin.val_rev]; omega)`. Substitute `this` using the available equality.

Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.
-/
theorem antiJ_mul_diagonal {n : ℕ} (f g : Fin n → L) (h : ∀ i, f (Fin.rev i) = g i) :
    Formalism.UG.antiJ L n * Matrix.diagonal f = Matrix.diagonal g * Formalism.UG.antiJ L n := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Formalism.UG.antiJ]
  split_ifs with hij
  · have : j = Fin.rev i := Fin.ext (by rw [Fin.val_rev]; omega)
    subst this
    rw [h]
    ring
  · simp

/- English proof (translation)
Use `set e := finSumFinEquiv (m := n) (n := n)`. Use `set J := Formalism.UG.antiJ L n`. Use `set u : Fin n → L := fun i => (ϖ : L) ^ (-d i).toNat - 1 with hu`. Use `set w : Fin n → L := fun i => (ϖ : L) ^ (d i).toNat - 1 with hw`. Establish `huw : ∀ i, u i * w i = 0` using `fun i => by`.

Break down `le_total (d i) 0 with h | h` into its components or cases. Simplify using `[hw, Int.toNat_of_nonpos h]`. Simplify using `[hu, Int.toNat_of_nonpos (neg_nonpos.2 h)]`. Use `set B : Matrix (Fin n) (Fin n) L := Matrix.diagonal u with hB`. Use `set C : Matrix (Fin n) (Fin n) L := Matrix.diagonal w with hC`.

Establish `hBC : B * C = 0` using `by rw [hB, hC, diagonal_mul_diagonal]; simp [huw]`. Establish `hCB : C * B = 0` using `by rw [hB, hC, diagonal_mul_diagonal]; simp [mul_comm (w _), huw]`. Establish `hJB : J * B = C * J` using `antiJ_mul_diagonal u w fun i => by simp [hu, hw, hd]`. Establish `hJC : J * C = B * J` using `antiJ_mul_diagonal w u fun i => by simp [hu, hw, hd]`. Establish `hσu : B.map σ = B`.

Rewrite using `[hB, diagonal_map (map_zero σ)]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `[hu, map_sub, map_pow, hU.2.2.1]`. Establish `hσw : C.map σ = C`.

Rewrite using `[hC, diagonal_map (map_zero σ)]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `[hw, map_sub, map_pow, hU.2.2.1]`. Set `κ : GL (Fin (n + n)) L` to `⟨(fromBlocks 1 B C 1).submatrix e.symm e.symm, (fromBlocks 1 (-B) (-C) 1).submatrix e.symm e.symm, by rw [submatrix_mul_equiv, fromBlocks_multiply]; simp [hBC, hCB], by rw [submatrix_mul_equiv, fromBlocks_multiply]; simp [hBC, hCB]⟩`.

Establish `hint : ∀ i j, (fromBlocks (1 : Matrix (Fin n) (Fin n) L) B C 1) i j ∈ Formalism.UG.intL L ∧ (fromBlocks (1 : Matrix (Fin n) (Fin n) L) (-B) (-C) 1) i j ∈ Formalism.UG.intL L`. Establish `h1 : ∀ a b : Fin n, (1 : Matrix (Fin n) (Fin n) L) a b ∈ Formalism.UG.intL L` using `fun a b => by`. Rewrite using `[one_apply]`. Use `split_ifs`. Use `exacts [one_mem _, zero_mem _]`.

Establish `h2 : ∀ (f : Fin n → ℕ) (a b : Fin n), (Matrix.diagonal fun i => (ϖ : L) ^ f i - 1) a b ∈ Formalism.UG.intL L` using `fun f a b => by`. Rewrite using `[diagonal_apply]`. Use `split_ifs`. Conclude with `sub_mem (pow_mem (unif_mem_int hU) _) (one_mem _)`. Conclude with `zero_mem _`.

Introduce `i j`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;>`. Simplify using `only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, neg_apply]`. Apply the tactic sequence `all_goals first`. Consider the case `exact ⟨h1 _ _, h1 _ _⟩`.

Consider the case `exact ⟨h2 _ _ _, neg_mem (h2 _ _ _)⟩`. Establish `hM : (GlobalTheory.Doubling.blkMat e (Matrix.diagonal fun i => (ϖ : L) ^ d i) 1 * κ.1).submatrix e e = fromBlocks (Matrix.diagonal fun i => (ϖ : L) ^ d i) ((Matrix.diagonal fun i => (ϖ : L) ^ d i) * B) C 1` using `by show ((fromBlocks (Matrix.diagonal fun i => (ϖ : L) ^ d i) 0 0 1).submatrix e.symm e.symm * (fromBlocks 1 B C 1).submatrix e.symm e.symm).submatrix e e = _`. Rewrite using `[submatrix_mul_equiv, submatrix_submatrix]`. Simplify using `[fromBlocks_multiply]`. Establish `h1 : (Matrix.diagonal fun i => (ϖ : L) ^ d i) + (Matrix.diagonal fun i => (ϖ : L) ^ d i) * B = Matrix.diagonal fun i => (ϖ : L) ^ (d i).toNat`.

Rewrite using `[hB, diagonal_mul_diagonal, diagonal_add]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `only [hu]`. Rewrite using `[mul_sub, mul_one, add_sub_cancel, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ ϖ.ne_zero]`.

Use `congr 1`. Use linear arithmetic over natural numbers and integers. Establish `h2 : C + 1 = Matrix.diagonal fun i => (ϖ : L) ^ (d i).toNat`. Rewrite using `[hC, ← diagonal_one, diagonal_add]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Simplify using `[hw]`. Use `⟨κ, ?_, mem_GLint_of_entries (fun i j => (hint _ _).1) (fun i j => (hint _ _).2), ?_, ?_⟩` and prove the remaining obligations. Use `show Formalism.UG.cT σ ((fromBlocks 1 B C 1).submatrix e.symm e.symm) * GlobalTheory.Doubling.blkMat e J (-J) * (fromBlocks 1 B C 1).submatrix e.symm e.symm = GlobalTheory.Doubling.blkMat e J (-J)`. Establish `hcT : Formalism.UG.cT σ ((fromBlocks (1 : Matrix (Fin n) (Fin n) L) B C 1).submatrix e.symm e.symm) = (fromBlocks 1 C B 1).submatrix e.symm e.symm`.

Rewrite using `[Formalism.UG.cT, ← submatrix_map, transpose_submatrix, fromBlocks_map, fromBlocks_transpose, hσu, hσw]`. Simplify using `[hB, hC, diagonal_transpose]`. Rewrite using `[hcT, GlobalTheory.Doubling.blkMat, submatrix_mul_equiv, submatrix_mul_equiv, fromBlocks_multiply, fromBlocks_multiply]`. Use `congr 1`. Establish `e1 : C * J * C = 0` using `by rw [Matrix.mul_assoc, hJC, ← Matrix.mul_assoc, hCB, Matrix.zero_mul]`.

Establish `e2 : B * J * B = 0` using `by rw [Matrix.mul_assoc, hJB, ← Matrix.mul_assoc, hBC, Matrix.zero_mul]`. Simplify using `[Matrix.mul_neg, Matrix.neg_mul, hJB, hJC, e1, e2]`. Rewrite using `[GlobalTheory.Doubling.KeepsDiag, GlobalTheory.Doubling.leviMat, hM]`. Simplify using `only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, h1, h2]`. Rewrite using `[GlobalTheory.Doubling.leviMat, hM]`.

Simplify using `only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, h1]`.
-/
theorem exists_kappa {ϖ : Lˣ} {σ : L →+* L} {q n : ℕ} (hU : IsUnramInv (ϖ : L) σ q) (d : Fin n → ℤ)
    (hd : ∀ i, d (Fin.rev i) = -d i) :
    ∃ κ : GL (Fin (n + n)) L, κ ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD σ n ∧ κ ∈ Formalism.UG.GLint (Fin (n + n)) (Formalism.UG.intL L) ∧
      GlobalTheory.Doubling.KeepsDiag finSumFinEquiv (GlobalTheory.Doubling.blkMat finSumFinEquiv (Matrix.diagonal fun i => (ϖ : L) ^ d i) 1 * κ.1) ∧
      GlobalTheory.Doubling.leviMat finSumFinEquiv (GlobalTheory.Doubling.blkMat finSumFinEquiv (Matrix.diagonal fun i => (ϖ : L) ^ d i) 1 * κ.1) =
        Matrix.diagonal fun i => (ϖ : L) ^ (d i).toNat := by
  set e := finSumFinEquiv (m := n) (n := n)
  set J := Formalism.UG.antiJ L n
  set u : Fin n → L := fun i => (ϖ : L) ^ (-d i).toNat - 1 with hu
  set w : Fin n → L := fun i => (ϖ : L) ^ (d i).toNat - 1 with hw
  have huw : ∀ i, u i * w i = 0 := fun i => by
    rcases le_total (d i) 0 with h | h
    · simp [hw, Int.toNat_of_nonpos h]
    · simp [hu, Int.toNat_of_nonpos (neg_nonpos.2 h)]
  set B : Matrix (Fin n) (Fin n) L := Matrix.diagonal u with hB
  set C : Matrix (Fin n) (Fin n) L := Matrix.diagonal w with hC
  have hBC : B * C = 0 := by rw [hB, hC, diagonal_mul_diagonal]; simp [huw]
  have hCB : C * B = 0 := by rw [hB, hC, diagonal_mul_diagonal]; simp [mul_comm (w _), huw]
  have hJB : J * B = C * J := antiJ_mul_diagonal u w fun i => by simp [hu, hw, hd]
  have hJC : J * C = B * J := antiJ_mul_diagonal w u fun i => by simp [hu, hw, hd]
  have hσu : B.map σ = B := by
    rw [hB, diagonal_map (map_zero σ)]
    congr 1; funext i
    simp [hu, map_sub, map_pow, hU.2.2.1]
  have hσw : C.map σ = C := by
    rw [hC, diagonal_map (map_zero σ)]
    congr 1; funext i
    simp [hw, map_sub, map_pow, hU.2.2.1]
  let κ : GL (Fin (n + n)) L := ⟨(fromBlocks 1 B C 1).submatrix e.symm e.symm,
    (fromBlocks 1 (-B) (-C) 1).submatrix e.symm e.symm,
    by rw [submatrix_mul_equiv, fromBlocks_multiply]; simp [hBC, hCB],
    by rw [submatrix_mul_equiv, fromBlocks_multiply]; simp [hBC, hCB]⟩
  have hint : ∀ i j, (fromBlocks (1 : Matrix (Fin n) (Fin n) L) B C 1) i j ∈ Formalism.UG.intL L ∧
      (fromBlocks (1 : Matrix (Fin n) (Fin n) L) (-B) (-C) 1) i j ∈ Formalism.UG.intL L := by
    have h1 : ∀ a b : Fin n, (1 : Matrix (Fin n) (Fin n) L) a b ∈ Formalism.UG.intL L := fun a b => by
      rw [one_apply]; split_ifs
      exacts [one_mem _, zero_mem _]
    have h2 : ∀ (f : Fin n → ℕ) (a b : Fin n),
        (Matrix.diagonal fun i => (ϖ : L) ^ f i - 1) a b ∈ Formalism.UG.intL L := fun f a b => by
      rw [diagonal_apply]; split_ifs
      · exact sub_mem (pow_mem (unif_mem_int hU) _) (one_mem _)
      · exact zero_mem _
    intro i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, neg_apply]
    all_goals first
      | exact ⟨h1 _ _, h1 _ _⟩
      | exact ⟨h2 _ _ _, neg_mem (h2 _ _ _)⟩
  have hM : (GlobalTheory.Doubling.blkMat e (Matrix.diagonal fun i => (ϖ : L) ^ d i) 1 * κ.1).submatrix e e =
      fromBlocks (Matrix.diagonal fun i => (ϖ : L) ^ d i) ((Matrix.diagonal fun i => (ϖ : L) ^ d i) * B) C 1 := by
    show ((fromBlocks (Matrix.diagonal fun i => (ϖ : L) ^ d i) 0 0 1).submatrix e.symm e.symm *
      (fromBlocks 1 B C 1).submatrix e.symm e.symm).submatrix e e = _
    rw [submatrix_mul_equiv, submatrix_submatrix]
    simp [fromBlocks_multiply]
  have h1 : (Matrix.diagonal fun i => (ϖ : L) ^ d i) + (Matrix.diagonal fun i => (ϖ : L) ^ d i) * B =
      Matrix.diagonal fun i => (ϖ : L) ^ (d i).toNat := by
    rw [hB, diagonal_mul_diagonal, diagonal_add]
    congr 1; funext i
    simp only [hu]
    rw [mul_sub, mul_one, add_sub_cancel, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ ϖ.ne_zero]
    congr 1
    omega
  have h2 : C + 1 = Matrix.diagonal fun i => (ϖ : L) ^ (d i).toNat := by
    rw [hC, ← diagonal_one, diagonal_add]
    congr 1; funext i
    simp [hw]
  refine ⟨κ, ?_, mem_GLint_of_entries (fun i j => (hint _ _).1) (fun i j => (hint _ _).2), ?_, ?_⟩
  · show Formalism.UG.cT σ ((fromBlocks 1 B C 1).submatrix e.symm e.symm) * GlobalTheory.Doubling.blkMat e J (-J) *
      (fromBlocks 1 B C 1).submatrix e.symm e.symm = GlobalTheory.Doubling.blkMat e J (-J)
    have hcT : Formalism.UG.cT σ ((fromBlocks (1 : Matrix (Fin n) (Fin n) L) B C 1).submatrix e.symm e.symm) =
        (fromBlocks 1 C B 1).submatrix e.symm e.symm := by
      rw [Formalism.UG.cT, ← submatrix_map, transpose_submatrix, fromBlocks_map, fromBlocks_transpose, hσu, hσw]
      simp [hB, hC, diagonal_transpose]
    rw [hcT, GlobalTheory.Doubling.blkMat, submatrix_mul_equiv, submatrix_mul_equiv, fromBlocks_multiply, fromBlocks_multiply]
    congr 1
    have e1 : C * J * C = 0 := by rw [Matrix.mul_assoc, hJC, ← Matrix.mul_assoc, hCB, Matrix.zero_mul]
    have e2 : B * J * B = 0 := by rw [Matrix.mul_assoc, hJB, ← Matrix.mul_assoc, hBC, Matrix.zero_mul]
    simp [Matrix.mul_neg, Matrix.neg_mul, hJB, hJC, e1, e2]
  · rw [GlobalTheory.Doubling.KeepsDiag, GlobalTheory.Doubling.leviMat, hM]
    simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, h1, h2]
  · rw [GlobalTheory.Doubling.leviMat, hM]
    simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, h1]

/- English proof (translation)
Establish `h` using `Formalism.UG.P.fSatake_ord_zpow hU.2.2.2.1 (k : ℤ)`. Rewrite `h` using `[zpow_natCast]`. Rewrite using `[GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.secVal, Units.val_pow_eq_pow_val, h, map_pow, Units.val_pow_eq_pow_val, GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varX, mul_pow, ← Complex.cpow_nat_mul]`. Use `congr 2`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem secVal_unif_pow {ϖ : Lˣ} {σ : L →+* L} {q n : ℕ} (hU : IsUnramInv (ϖ : L) σ q) (χ : Lˣ →* ℂˣ) (s : ℂ)
    (k : ℕ) : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.secVal q χ (s + (n : ℂ) / 2) (ϖ ^ k) = GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varX q n (χ ϖ) s ^ k := by
  have h := Formalism.UG.P.fSatake_ord_zpow hU.2.2.2.1 (k : ℤ)
  rw [zpow_natCast] at h
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.secVal, Units.val_pow_eq_pow_val, h, map_pow, Units.val_pow_eq_pow_val,
    GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varX, mul_pow, ← Complex.cpow_nat_mul]
  congr 2
  push_cast
  ring

/- English proof (translation)
Establish `hq : q ≠ 0` using `by have := hU.2.2.2.2.2.1; omega`. Take `⟨κ, hκG, hκI, hkeep, hlev⟩` from `exists_kappa hU d (exp_rev hU ht)`. Use `set e := finSumFinEquiv (m := n) (n := n)`. Set `K : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD σ n` to `⟨κ, hκG⟩`. Establish `hK : K ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.KD σ n` using `⟨hκG, hκI⟩`.

Take `⟨x₁, hx₁⟩` from `hk₁.2`. Take `⟨x₂, hx₂⟩` from `hk₂.2`. Take `⟨y₁, hy₁⟩` from `(inv_mem hk₁).2`. Set `p0 : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD σ n` to `GlobalTheory.Doubling.ioU σ e rfl (k₁, k₁)`. Set `r : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD σ n` to `GlobalTheory.Doubling.ioU σ e rfl (k₂, k₁⁻¹)`.

Establish `hp0P : p0 ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.PD σ n` using `GlobalTheory.Doubling.mem_siegelOf.2 ((GlobalTheory.Doubling.keepsDiag_blkMat e).2 rfl)`. Establish `hp0K : p0 ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.KD σ n` using `⟨p0.2, GlobalTheory.Doubling.blkGL e (x₁, x₁), by rw [GlobalTheory.Doubling.bc_blkGL, hx₁]; rfl⟩`. Establish `hrK : r ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.KD σ n` using `⟨r.2, GlobalTheory.Doubling.blkGL e (x₂, y₁), by rw [GlobalTheory.Doubling.bc_blkGL, hx₂, hy₁]; rfl⟩`. Establish `hp1P : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n t * K ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.PD σ n`. Use `GlobalTheory.Doubling.mem_siegelOf.2 ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `GlobalTheory.Doubling.KeepsDiag e (GlobalTheory.Doubling.blkMat e t.1.1 1 * κ.1)`. Rewrite using `[ht]`. Conclude with `hkeep`. Set `P0 : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.PD σ n` to `⟨p0, hp0P⟩`. Set `P1 : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.PD σ n` to `⟨_, hp1P⟩`.

Establish `hdec : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n (k₁ * t * k₂) = ((P0 * P1 : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.PD σ n) : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD σ n) * (K⁻¹ * r)`. Rewrite using `[Subgroup.coe_mul]`. Express the relevant statement in the definitionally equal form `_ = p0 * (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n t * K) * (K⁻¹ * r)`. Rewrite using `[show p0 * (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n t * K) * (K⁻¹ * r) = p0 * GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n t * r by group]`. Express the relevant statement in the definitionally equal form `GlobalTheory.Doubling.ioU σ e rfl (k₁ * t * k₂, 1) = GlobalTheory.Doubling.ioU σ e rfl (k₁, k₁) * GlobalTheory.Doubling.ioU σ e rfl (t, 1) * GlobalTheory.Doubling.ioU σ e rfl (k₂, k₁⁻¹)`.

Rewrite using `[← map_mul, ← map_mul]`. Use `congr 1`. Use `ext1`. Both sides reduce to the same expression. Simplify using the standard rewrite rules.

Establish `ha1 : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.aD σ n P1 = ϖ ^ (∑ i, (d i).toNat)`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[GlobalTheory.Doubling.val_aOf, Units.val_pow_eq_pow_val]`. Express the relevant statement in the definitionally equal form `(GlobalTheory.Doubling.leviMat e (GlobalTheory.Doubling.blkMat e t.1.1 1 * κ.1)).det = _`. Rewrite using `[ht, hlev, Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum]`.

Rewrite using `[hdec, hΦ _ _ (mul_mem (inv_mem hK) hrK), map_mul, GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.secVal_mul hq, GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.secVal_unit q hχ _ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariab …`. Rewrite using `[show ∑ i, max (d i) 0 = ((∑ i, (d i).toNat : ℕ) : ℤ) by push_cast; simp [Int.toNat_eq_max], zpow_natCast]`.
-/
theorem sphericalDoublingSection_graph_diagonal_cartan [CompleteSpace L] {ϖ : Lˣ} {σ : L →+* L} {q n : ℕ} (hU : IsUnramInv (ϖ : L) σ q)
    {χ : Lˣ →* ℂˣ} (hχ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsUnr χ) {s : ℂ} {Φ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD σ n → ℂ}
    (hΦ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsSphSec σ q n χ s Φ) (d : Fin n → ℤ) (t : GU σ n)
    (ht : t.1.1 = Matrix.diagonal (fun i => (ϖ : L) ^ d i)) (k₁ : GU σ n) (hk₁ : k₁ ∈ KU σ n) (k₂ : GU σ n)
    (hk₂ : k₂ ∈ KU σ n) :
    Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n (k₁ * t * k₂)) = GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varX q n (χ ϖ) s ^ (∑ i, max (d i) 0) := by
  have hq : q ≠ 0 := by have := hU.2.2.2.2.2.1; omega
  obtain ⟨κ, hκG, hκI, hkeep, hlev⟩ := exists_kappa hU d (exp_rev hU ht)
  set e := finSumFinEquiv (m := n) (n := n)
  let K : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD σ n := ⟨κ, hκG⟩
  have hK : K ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.KD σ n := ⟨hκG, hκI⟩
  obtain ⟨x₁, hx₁⟩ := hk₁.2
  obtain ⟨x₂, hx₂⟩ := hk₂.2
  obtain ⟨y₁, hy₁⟩ := (inv_mem hk₁).2
  let p0 : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD σ n := GlobalTheory.Doubling.ioU σ e rfl (k₁, k₁)
  let r : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD σ n := GlobalTheory.Doubling.ioU σ e rfl (k₂, k₁⁻¹)
  have hp0P : p0 ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.PD σ n :=
    GlobalTheory.Doubling.mem_siegelOf.2 ((GlobalTheory.Doubling.keepsDiag_blkMat e).2 rfl)
  have hp0K : p0 ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.KD σ n :=
    ⟨p0.2, GlobalTheory.Doubling.blkGL e (x₁, x₁), by rw [GlobalTheory.Doubling.bc_blkGL, hx₁]; rfl⟩
  have hrK : r ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.KD σ n :=
    ⟨r.2, GlobalTheory.Doubling.blkGL e (x₂, y₁), by rw [GlobalTheory.Doubling.bc_blkGL, hx₂, hy₁]; rfl⟩
  have hp1P : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n t * K ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.PD σ n := by
    refine GlobalTheory.Doubling.mem_siegelOf.2 ?_
    change GlobalTheory.Doubling.KeepsDiag e (GlobalTheory.Doubling.blkMat e t.1.1 1 * κ.1)
    rw [ht]
    exact hkeep
  let P0 : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.PD σ n := ⟨p0, hp0P⟩
  let P1 : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.PD σ n := ⟨_, hp1P⟩
  have hdec : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n (k₁ * t * k₂) = ((P0 * P1 : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.PD σ n) :
      GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD σ n) * (K⁻¹ * r) := by
    rw [Subgroup.coe_mul]
    change _ = p0 * (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n t * K) * (K⁻¹ * r)
    rw [show p0 * (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n t * K) * (K⁻¹ * r) = p0 * GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n t * r by group]
    change GlobalTheory.Doubling.ioU σ e rfl (k₁ * t * k₂, 1) = GlobalTheory.Doubling.ioU σ e rfl (k₁, k₁) *
      GlobalTheory.Doubling.ioU σ e rfl (t, 1) * GlobalTheory.Doubling.ioU σ e rfl (k₂, k₁⁻¹)
    rw [← map_mul, ← map_mul]
    congr 1
    ext1
    · rfl
    · simp
  have ha1 : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.aD σ n P1 = ϖ ^ (∑ i, (d i).toNat) := by
    apply Units.ext
    rw [GlobalTheory.Doubling.val_aOf, Units.val_pow_eq_pow_val]
    change (GlobalTheory.Doubling.leviMat e (GlobalTheory.Doubling.blkMat e t.1.1 1 * κ.1)).det = _
    rw [ht, hlev, Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum]
  rw [hdec, hΦ _ _ (mul_mem (inv_mem hK) hrK), map_mul, GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.secVal_mul hq,
    GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.secVal_unit q hχ _ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.v_aD_eq P0 hp0K), one_mul, ha1, secVal_unif_pow hU]
  rw [show ∑ i, max (d i) 0 = ((∑ i, (d i).toNat : ℕ) : ℤ) by push_cast; simp [Int.toNat_eq_max], zpow_natCast]

/- English proof (translation)
Introduce `L _ _ _ ϖ σ q n hU χ hχ s Φ hΦ d t ht k₁ hk₁ k₂ hk₂`. Conclude with `sphericalDoublingSection_graph_diagonal_cartan hU hχ hΦ d t ht k₁ hk₁ k₂ hk₂`.
-/
theorem sphSec_io_diag : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : Lˣ) (σ : L →+* L) (q n : ℕ), IsUnramInv (ϖ : L) σ q → ∀ (χ : Lˣ →* ℂˣ), GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsUnr χ → ∀ (s : ℂ) (Φ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD σ n → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsSphSec σ q n χ s Φ → ∀ (d : Fin n → ℤ) (t : GU σ n), t.1.1 = Matrix.diagonal (fun i => (ϖ : L) ^ d i) → ∀ k₁ ∈ KU σ n, ∀ k₂ ∈ KU σ n, Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n (k₁ * t * k₂)) = GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varX q n (χ ϖ) s ^ (∑ i, max (d i) 0) := by
  intro L _ _ _ ϖ σ q n hU χ hχ s Φ hΦ d t ht k₁ hk₁ k₂ hk₂
  exact sphericalDoublingSection_graph_diagonal_cartan hU hχ hΦ d t ht k₁ hk₁ k₂ hk₂

end GlobalTheory.UGraph

end
