import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BlockRetr
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ToCellSurj
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalOrbitGerms
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsUpUniMul

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.BlockCounting

open Formalism.MainNotions.S Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P.Phase

variable {R : Type} [CommRing R] {n : ℕ} (a : Loc.Pt R n)

abbrev sz : List ℕ := a.blocks.map (fun b => (b.2 : ℕ))

/- English proof (translation)
The claim follows from `a.size`.
-/
theorem sz_sum : (sz a).sum = n := a.size

def bk (i : Fin n) : ℕ := blk (sz a) i

def rv (i : Fin n) : Fin n :=
  ⟨revIn (sz a) i, by have := revIn_lt (sz a) i (by rw [sz_sum]; exact i.2); rwa [sz_sum] at this⟩

def cc (i : Fin n) : R := (((a.blocks.map Prod.fst).getD (bk a i) 1 : Rˣ) : R)

/- English proof (translation)
The claim follows from `Fin.ext (revIn_revIn (sz a) i (by rw [sz_sum]; exact i.2))`.
-/
theorem rv_rv (i : Fin n) : rv a (rv a i) = i :=
  Fin.ext (revIn_revIn (sz a) i (by rw [sz_sum]; exact i.2))

/- English proof (translation)
The claim follows from `blk_revIn (sz a) i (by rw [sz_sum]; exact i.2)`.
-/
theorem bk_rv (i : Fin n) : bk a (rv a i) = bk a i := blk_revIn (sz a) i (by rw [sz_sum]; exact i.2)

/- English proof (translation)
The claim follows from `blk_mono (sz a) i j h`.
-/
theorem bk_mono {i j : Fin n} (h : i ≤ j) : bk a i ≤ bk a j := blk_mono (sz a) i j h

/- English proof (translation)
The claim follows from `revIn_anti (sz a) i j (by rw [sz_sum]; exact j.2) h hb`.
-/
theorem rv_anti {i j : Fin n} (h : i < j) (hb : bk a i = bk a j) : rv a j < rv a i :=
  revIn_anti (sz a) i j (by rw [sz_sum]; exact j.2) h hb

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `bk_mono a (not_lt.1 hc)` as an intermediate fact. Rewrite `this` using `[bk_rv, bk_rv]`. Use linear arithmetic over natural numbers and integers.
-/
theorem rv_lt_of_bk_lt {i j : Fin n} (h : bk a i < bk a j) : rv a i < rv a j := by
  by_contra hc
  have := bk_mono a (not_lt.1 hc)
  rw [bk_rv, bk_rv] at this
  omega

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `bk_mono a (not_lt.1 hc)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem lt_of_bk_lt {i j : Fin n} (h : bk a i < bk a j) : i < j := by
  by_contra hc
  have := bk_mono a (not_lt.1 hc)
  omega

/- English proof (translation)
Unfold `cc`. Rewrite using `[bk_rv]`.
-/
theorem cc_rv (i : Fin n) : cc a (rv a i) = cc a i := by unfold cc; rw [bk_rv]

/- English proof (translation)
The claim follows from `Units.isUnit _`.
-/
theorem cc_unit (i : Fin n) : IsUnit (cc a i) := Units.isUnit _

/- English proof (translation)
Establish `h` using `Formalism.MainNotions.LocalModelPeriodLattices.ptEntryL_eq a.blocks i j (by rw [a.size]; exact i.2)`. Use `show Loc.ptEntryL a.blocks i j = _`. Rewrite using `[h]`. Simplify using `only [Fin.ext_iff, rv, cc, bk]`.
-/
theorem mat_apply (i j : Fin n) : a.mat i j = if j = rv a i then cc a i else 0 := by
  have h := Formalism.MainNotions.LocalModelPeriodLattices.ptEntryL_eq a.blocks i j (by rw [a.size]; exact i.2)
  show Loc.ptEntryL a.blocks i j = _
  rw [h]
  simp only [Fin.ext_iff, rv, cc, bk]

/- English proof (translation)
The claim follows from `Formalism.MainNotions.LocalOrbitGerms.Cls.sameBlock_iff a.blocks i j (by rw [a.size]; exact i.2) (by rw [a.size]; exact j.2)`.
-/
theorem sameBlock_iff (i j : Fin n) : Loc.sameBlock a.blocks i j = true ↔ bk a i = bk a j :=
  Formalism.MainNotions.LocalOrbitGerms.Cls.sameBlock_iff a.blocks i j (by rw [a.size]; exact i.2) (by rw [a.size]; exact j.2)

end Formalism.L2.SG.Pf.BlockCounting

namespace Formalism.L2.SG.Pf.BlockCounting

open Formalism.MainNotions.S Matrix

variable {R : Type} [CommRing R] {n : ℕ} (a : Loc.Pt R n)

def bd (x : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := fun i j => if bk a i = bk a j then x i j else 0

def rvM (M : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := fun i j => M (rv a i) (rv a j)

variable {a}

/- English proof (translation)
Introduce `i j`. Use `⟨fun h => ?_, fun h => ?_⟩` and prove the remaining obligations. Unfold `bd`. Use `split_ifs`. Conclude with `(hx i j).1 h`.

Both sides reduce to the same expression. Substitute `h` using the available equality. Unfold `bd`. Rewrite using `[if_pos rfl]`. Conclude with `(hx i i).2 rfl`.
-/
theorem bd_lo {x : Matrix (Fin n) (Fin n) R} (hx : IsLoUni x) : IsLoUni (bd a x) := by
  intro i j
  refine ⟨fun h => ?_, fun h => ?_⟩
  · unfold bd; split_ifs
    · exact (hx i j).1 h
    · rfl
  · subst h; unfold bd; rw [if_pos rfl]; exact (hx i i).2 rfl

/- English proof (translation)
Use extensionality with `i j`. Unfold `bd`. Use `split_ifs with h`. Both sides reduce to the same expression. Rewrite using `[Matrix.one_apply, if_neg]`.

Introduce and unpack `rfl`. Conclude with `h rfl`.
-/
theorem bd_one : bd a (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  ext i j
  unfold bd
  split_ifs with h
  · rfl
  · rw [Matrix.one_apply, if_neg]
    rintro rfl; exact h rfl

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [bd, Matrix.mul_apply]`. Distinguish the cases in `hij : bk a i = bk a j`. Rewrite using `[if_pos hij]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hk : bk a i = bk a k`. Rewrite using `[if_pos hk, if_pos (hk.symm.trans hij)]`. Rewrite using `[if_neg hk, zero_mul]`. Distinguish the cases in `h1 : i < k`. Rewrite using `[(hx i k).1 h1, zero_mul]`.

Distinguish the cases in `h2 : k < j`. Rewrite using `[(hy k j).1 h2, mul_zero]`. It suffices to derive a contradiction. Establish `e1` using `bk_mono a (not_lt.1 h1)`. Establish `e2` using `bk_mono a (not_lt.1 h2)`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg hij]`. Use `symm`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hk : bk a i = bk a k`.

Rewrite using `[if_pos hk, if_neg (fun e => hij (hk.trans e)), mul_zero]`. Rewrite using `[if_neg hk, zero_mul]`.
-/
theorem bd_mul {x y : Matrix (Fin n) (Fin n) R} (hx : IsLoUni x) (hy : IsLoUni y) :
    bd a (x * y) = bd a x * bd a y := by
  ext i j
  simp only [bd, Matrix.mul_apply]
  by_cases hij : bk a i = bk a j
  · rw [if_pos hij]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : bk a i = bk a k
    · rw [if_pos hk, if_pos (hk.symm.trans hij)]
    · rw [if_neg hk, zero_mul]
      by_cases h1 : i < k
      · rw [(hx i k).1 h1, zero_mul]
      · by_cases h2 : k < j
        · rw [(hy k j).1 h2, mul_zero]
        · exfalso
          have e1 := bk_mono a (not_lt.1 h1)
          have e2 := bk_mono a (not_lt.1 h2)
          omega
  · rw [if_neg hij]
    symm
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : bk a i = bk a k
    · rw [if_pos hk, if_neg (fun e => hij (hk.trans e)), mul_zero]
    · rw [if_neg hk, zero_mul]

/- English proof (translation)
Take `⟨hi, -, h2⟩` from `Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv hx`. Establish `: bd a x * bd a x⁻¹ = 1` using `by rw [← bd_mul hx hi, h2, bd_one]`. Conclude with `(Matrix.inv_eq_right_inv this).symm`.
-/
theorem bd_inv {x : Matrix (Fin n) (Fin n) R} (hx : IsLoUni x) : bd a x⁻¹ = (bd a x)⁻¹ := by
  obtain ⟨hi, -, h2⟩ := Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv hx
  have : bd a x * bd a x⁻¹ = 1 := by rw [← bd_mul hx hi, h2, bd_one]
  exact (Matrix.inv_eq_right_inv this).symm

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h i j hij hb`. Use `congrFun (congrFun h i) j` as an intermediate fact. Simplify using `only [bd, if_pos hb, Matrix.one_apply, if_neg hij] at this`. Conclude with `this`.

Introduce `h`. Use extensionality with `i j`. Unfold `bd`. Rewrite using `[Matrix.one_apply]`. Use `split_ifs with h1 h2 h2`.

Substitute `h2` using the available equality. Conclude with `(hx i i).2 rfl`. Conclude with `h i j h2 h1`. Substitute `h2` using the available equality. Conclude with `absurd rfl h1`.

Both sides reduce to the same expression.
-/
theorem bd_eq_one_iff {x : Matrix (Fin n) (Fin n) R} (hx : IsLoUni x) :
    bd a x = 1 ↔ ∀ i j : Fin n, i ≠ j → bk a i = bk a j → x i j = 0 := by
  constructor
  · intro h i j hij hb
    have := congrFun (congrFun h i) j
    simp only [bd, if_pos hb, Matrix.one_apply, if_neg hij] at this
    exact this
  · intro h
    ext i j
    unfold bd
    rw [Matrix.one_apply]
    split_ifs with h1 h2 h2
    · subst h2; exact (hx i i).2 rfl
    · exact h i j h2 h1
    · subst h2; exact absurd rfl h1
    · rfl

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [rvM, Matrix.mul_apply]`. Conclude with `(Fintype.sum_equiv ⟨rv a, rv a, rv_rv a, rv_rv a⟩ _ _ (fun k => by simp [rv_rv])).symm`.
-/
theorem rvM_mul (M N : Matrix (Fin n) (Fin n) R) : rvM a (M * N) = rvM a M * rvM a N := by
  ext i j
  simp only [rvM, Matrix.mul_apply]
  exact (Fintype.sum_equiv ⟨rv a, rv a, rv_rv a, rv_rv a⟩ _ _ (fun k => by simp [rv_rv])).symm

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [rvM, Matrix.one_apply]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[if_neg (fun e => h (by rw [← rv_rv a i, e, rv_rv])), if_neg h]`.
-/
theorem rvM_one : rvM a (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  ext i j
  simp only [rvM, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg (fun e => h (by rw [← rv_rv a i, e, rv_rv])), if_neg h]

/- English proof (translation)
Introduce `i j`. Use `⟨fun h => ?_, fun h => ?_⟩` and prove the remaining obligations. Unfold `rvM bd split_ifs with hb`. Rewrite `hb` using `[bk_rv, bk_rv]`. Conclude with `(hx _ _).1 (rv_anti a h hb.symm)`.

Both sides reduce to the same expression. Substitute `h` using the available equality. Unfold `rvM bd`. Rewrite using `[if_pos rfl]`. Conclude with `(hx _ _).2 rfl`.
-/
theorem rvM_up {x : Matrix (Fin n) (Fin n) R} (hx : IsLoUni x) : IsUpUni (rvM a (bd a x)) := by
  intro i j
  refine ⟨fun h => ?_, fun h => ?_⟩
  · unfold rvM bd
    split_ifs with hb
    · rw [bk_rv, bk_rv] at hb
      exact (hx _ _).1 (rv_anti a h hb.symm)
    · rfl
  · subst h; unfold rvM bd; rw [if_pos rfl]; exact (hx _ _).2 rfl

/- English proof (translation)
Use extensionality with `i j`. Establish `h1 : (bd a x * a.mat) i j = bd a x i (rv a j) * cc a (rv a j)`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (rv a j)]`. Rewrite using `[mat_apply, if_pos (rv_rv a j).symm]`. Introduce `k _ hk`.

Rewrite using `[mat_apply, if_neg (fun e => hk (by rw [e, rv_rv])), mul_zero]`. Simplify using the standard rewrite rules. Establish `h2 : (a.mat * rvM a (bd a x)) i j = cc a i * bd a x i (rv a j)`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (rv a i)]`. Rewrite using `[mat_apply, if_pos rfl, rvM, rv_rv]`.

Introduce `k _ hk`. Rewrite using `[mat_apply, if_neg hk, zero_mul]`. Simplify using the standard rewrite rules. Rewrite using `[h1, h2, cc_rv]`. Unfold `bd`.

Use `split_ifs with hb`. Establish `: cc a i = cc a j` using `by unfold cc; rw [hb, bk_rv]`. Rewrite using `[this, mul_comm]`. Simplify using the standard rewrite rules.
-/
theorem bd_mat (x : Matrix (Fin n) (Fin n) R) : bd a x * a.mat = a.mat * rvM a (bd a x) := by
  ext i j
  have h1 : (bd a x * a.mat) i j = bd a x i (rv a j) * cc a (rv a j) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (rv a j)]
    · rw [mat_apply, if_pos (rv_rv a j).symm]
    · intro k _ hk
      rw [mat_apply, if_neg (fun e => hk (by rw [e, rv_rv])), mul_zero]
    · simp
  have h2 : (a.mat * rvM a (bd a x)) i j = cc a i * bd a x i (rv a j) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (rv a i)]
    · rw [mat_apply, if_pos rfl, rvM, rv_rv]
    · intro k _ hk
      rw [mat_apply, if_neg hk, zero_mul]
    · simp
  rw [h1, h2, cc_rv]
  unfold bd
  split_ifs with hb
  · have : cc a i = cc a j := by unfold cc; rw [hb, bk_rv]
    rw [this, mul_comm]
  · simp

def ccU (a : Loc.Pt R n) (i : Fin n) : Rˣ := (a.blocks.map Prod.fst).getD (bk a i) 1

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cc_eq (i : Fin n) : cc a i = (ccU a i : R) := rfl

/- English proof (translation)
Unfold `ccU`. Rewrite using `[bk_rv]`.
-/
theorem ccU_rv (i : Fin n) : ccU a (rv a i) = ccU a i := by unfold ccU; rw [bk_rv]

def matI (a : Loc.Pt R n) : Matrix (Fin n) (Fin n) R := fun i j => if j = rv a i then (((ccU a i)⁻¹ : Rˣ) : R) else 0

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (rv a i)]`. Rewrite using `[matI, if_pos rfl, mat_apply, rv_rv, Matrix.one_apply]`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality.

Rewrite using `[if_pos rfl, if_pos rfl, cc_eq, ccU_rv]`. Conclude with `Units.inv_mul _`. Rewrite using `[if_neg h, if_neg (Ne.symm h), mul_zero]`. Introduce `k _ hk`. Rewrite using `[matI, if_neg hk, zero_mul]`.

Simplify using the standard rewrite rules.
-/
theorem matI_mul : matI a * a.mat = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (rv a i)]
  · rw [matI, if_pos rfl, mat_apply, rv_rv, Matrix.one_apply]
    by_cases h : j = i
    · subst h; rw [if_pos rfl, if_pos rfl, cc_eq, ccU_rv]; exact Units.inv_mul _
    · rw [if_neg h, if_neg (Ne.symm h), mul_zero]
  · intro k _ hk
    rw [matI, if_neg hk, zero_mul]
  · simp

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (rv a i)]`. Rewrite using `[mat_apply, if_pos rfl, matI, Matrix.one_apply, ccU_rv]`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality.

Rewrite using `[if_pos (rv_rv a j).symm, if_pos rfl, cc_eq]`. Conclude with `Units.mul_inv _`. Rewrite using `[if_neg (fun e => h (by rw [e, rv_rv])), if_neg (Ne.symm h), mul_zero]`. Introduce `k _ hk`. Rewrite using `[mat_apply, if_neg hk, zero_mul]`.

Simplify using the standard rewrite rules.
-/
theorem mat_mul_matI : a.mat * matI a = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (rv a i)]
  · rw [mat_apply, if_pos rfl, matI, Matrix.one_apply, ccU_rv]
    by_cases h : j = i
    · subst h; rw [if_pos (rv_rv a j).symm, if_pos rfl, cc_eq]; exact Units.mul_inv _
    · rw [if_neg (fun e => h (by rw [e, rv_rv])), if_neg (Ne.symm h), mul_zero]
  · intro k _ hk
    rw [mat_apply, if_neg hk, zero_mul]
  · simp

/- English proof (translation)
Take `⟨hρi, -, hρ2⟩` from `Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_inv hρ`. Establish `e : l * a.mat = a.mat * ρ⁻¹`. Combine the equalities or inequalities in the displayed calculation. Use extensionality with `i j`. Unfold `bd`.

Use `split_ifs with hb`. Both sides reduce to the same expression. Use `symm`. Break down `lt_or_gt_of_ne (show i ≠ j from fun h' => hb (by rw [h'])) with hij | hij` into its components or cases. Conclude with `(hl i j).1 hij`.

Establish `e1` using `congrFun (congrFun e i) (rv a j)`. Establish `lhs : (l * a.mat) i (rv a j) = l i j * cc a j`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single j]`. Rewrite using `[mat_apply, if_pos rfl]`. Introduce `k _ hk`.

Rewrite using `[mat_apply, if_neg (fun e' => hk (by rw [← rv_rv a k, ← e', rv_rv])), mul_zero]`. Simplify using the standard rewrite rules. Establish `rhs : (a.mat * ρ⁻¹) i (rv a j) = cc a i * ρ⁻¹ (rv a i) (rv a j)`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (rv a i)]`. Rewrite using `[mat_apply, if_pos rfl]`.

Introduce `k _ hk`. Rewrite using `[mat_apply, if_neg hk, zero_mul]`. Simplify using the standard rewrite rules. Establish `hlt : bk a j < bk a i` using `lt_of_le_of_ne (bk_mono a hij.le) (fun e' => hb e'.symm)`. Establish `hz : ρ⁻¹ (rv a i) (rv a j) = 0` using `(hρi _ _).1 (rv_lt_of_bk_lt a hlt)`.

Rewrite `e1` using `[lhs, rhs, hz, mul_zero]`. Conclude with `((cc_unit a j).mul_left_eq_zero).1 e1`.
-/
theorem bd_of_stab {l ρ : Matrix (Fin n) (Fin n) R} (hl : IsLoUni l) (hρ : IsUpUni ρ)
    (h : l * a.mat * ρ = a.mat) : bd a l = l := by
  obtain ⟨hρi, -, hρ2⟩ := Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_inv hρ
  have e : l * a.mat = a.mat * ρ⁻¹ := by
    calc l * a.mat = l * a.mat * (ρ * ρ⁻¹) := by rw [hρ2, Matrix.mul_one]
      _ = l * a.mat * ρ * ρ⁻¹ := by rw [Matrix.mul_assoc (l * a.mat)]
      _ = a.mat * ρ⁻¹ := by rw [h]
  ext i j
  unfold bd
  split_ifs with hb
  · rfl
  · symm
    rcases lt_or_gt_of_ne (show i ≠ j from fun h' => hb (by rw [h'])) with hij | hij
    · exact (hl i j).1 hij
    ·
      have e1 := congrFun (congrFun e i) (rv a j)
      have lhs : (l * a.mat) i (rv a j) = l i j * cc a j := by
        rw [Matrix.mul_apply, Finset.sum_eq_single j]
        · rw [mat_apply, if_pos rfl]
        · intro k _ hk
          rw [mat_apply, if_neg (fun e' => hk (by rw [← rv_rv a k, ← e', rv_rv])), mul_zero]
        · simp
      have rhs : (a.mat * ρ⁻¹) i (rv a j) = cc a i * ρ⁻¹ (rv a i) (rv a j) := by
        rw [Matrix.mul_apply, Finset.sum_eq_single (rv a i)]
        · rw [mat_apply, if_pos rfl]
        · intro k _ hk
          rw [mat_apply, if_neg hk, zero_mul]
        · simp
      have hlt : bk a j < bk a i := lt_of_le_of_ne (bk_mono a hij.le) (fun e' => hb e'.symm)
      have hz : ρ⁻¹ (rv a i) (rv a j) = 0 := (hρi _ _).1 (rv_lt_of_bk_lt a hlt)
      rw [lhs, rhs, hz, mul_zero] at e1
      exact ((cc_unit a j).mul_left_eq_zero).1 e1

/- English proof (translation)
Establish `hb` using `bd_of_stab hl hρ h`. Take `⟨hli, h1, -⟩` from `Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv hl`. Establish `e : a.mat * ρ = l⁻¹ * a.mat`. Combine the equalities or inequalities in the displayed calculation. Establish `hbi : bd a l⁻¹ = l⁻¹` using `by rw [bd_inv hl, hb]`.

Establish `e2 : a.mat * ρ = a.mat * rvM a (bd a l⁻¹)` using `by rw [e, ← bd_mat, hbi]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem rho_of_stab {l ρ : Matrix (Fin n) (Fin n) R} (hl : IsLoUni l) (hρ : IsUpUni ρ)
    (h : l * a.mat * ρ = a.mat) : ρ = rvM a (bd a l⁻¹) := by
  have hb := bd_of_stab hl hρ h
  obtain ⟨hli, h1, -⟩ := Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv hl
  have e : a.mat * ρ = l⁻¹ * a.mat := by
    calc a.mat * ρ = (l⁻¹ * l) * a.mat * ρ := by rw [h1, Matrix.one_mul]
      _ = l⁻¹ * (l * a.mat * ρ) := by simp only [Matrix.mul_assoc]
      _ = l⁻¹ * a.mat := by rw [h]
  have hbi : bd a l⁻¹ = l⁻¹ := by rw [bd_inv hl, hb]
  have e2 : a.mat * ρ = a.mat * rvM a (bd a l⁻¹) := by rw [e, ← bd_mat, hbi]
  calc ρ = matI a * (a.mat * ρ) := by rw [← Matrix.mul_assoc, matI_mul, Matrix.one_mul]
    _ = matI a * (a.mat * rvM a (bd a l⁻¹)) := by rw [e2]
    _ = rvM a (bd a l⁻¹) := by rw [← Matrix.mul_assoc, matI_mul, Matrix.one_mul]

end Formalism.L2.SG.Pf.BlockCounting

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut Formalism.L2.SG.Pf.BlockCounting

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D)

section Retr

variable {p}

def loU {l : MP p} (h : IsLoUni l) : GLp p :=
  ⟨l, l⁻¹, (Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv h).2.2, (Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv h).2.1⟩

def upU {l : MP p} (h : IsUpUni l) : GLp p :=
  ⟨l, l⁻¹, (Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_inv h).2.2, (Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_inv h).2.1⟩

variable (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1))

/- English proof (translation)
The claim follows from `x.2.1`.
-/
theorem UP_lo (x : UP p) : IsLoUni (((x : GG p).1 : GLp p) : MP p) := x.2.1

/- English proof (translation)
The claim follows from `x.2.2`.
-/
theorem UP_up (x : UP p) : IsUpUni (((x : GG p).2.unop : GLp p) : MP p) := x.2.2

def retrFun (x : UP p) : UP p :=
  ⟨(loU (bd_lo (a := a) (UP_lo x)),
      MulOpposite.op (upU (rvM_up (a := a) (Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv (UP_lo x)).1))),
    bd_lo (UP_lo x), rvM_up (Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv (UP_lo x)).1⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem retrFun_fst (x : UP p) : ((((retrFun a x : UP p) : GG p).1 : GLp p) : MP p) =
    bd a (((x : GG p).1 : GLp p) : MP p) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem retrFun_snd (x : UP p) : ((((retrFun a x : UP p) : GG p).2.unop : GLp p) : MP p) =
    rvM a (bd a (((x : GG p).1 : GLp p) : MP p)⁻¹) := rfl

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Apply `Prod.ext` to reduce the goal to its premises. Conclude with `Units.ext h1`. Conclude with `MulOpposite.unop_injective (Units.ext h2)`.
-/
theorem UP_ext {x y : UP p} (h1 : (((x : GG p).1 : GLp p) : MP p) = (((y : GG p).1 : GLp p) : MP p))
    (h2 : (((x : GG p).2.unop : GLp p) : MP p) = (((y : GG p).2.unop : GLp p) : MP p)) : x = y := by
  apply Subtype.ext
  apply Prod.ext
  · exact Units.ext h1
  · exact MulOpposite.unop_injective (Units.ext h2)

def retr : UP p →* UP p where
  toFun := retrFun a
  map_one' := by
    apply UP_ext
    · rw [retrFun_fst]; exact bd_one
    · rw [retrFun_snd]
      show rvM a (bd a (1 : MP p)⁻¹) = 1
      rw [inv_one, bd_one, rvM_one]
  map_mul' x y := by
    have hx := UP_lo x
    have hy := UP_lo y
    apply UP_ext
    · show bd a ((((x * y : UP p) : GG p).1 : GLp p) : MP p) = bd a _ * bd a _
      exact bd_mul hx hy
    · show rvM a (bd a ((((x * y : UP p) : GG p).1 : GLp p) : MP p)⁻¹) =
        rvM a (bd a (((y : GG p).1 : GLp p) : MP p)⁻¹) * rvM a (bd a (((x : GG p).1 : GLp p) : MP p)⁻¹)
      have e : ((((x * y : UP p) : GG p).1 : GLp p) : MP p) =
          (((x : GG p).1 : GLp p) : MP p) * (((y : GG p).1 : GLp p) : MP p) := rfl
      rw [e, Matrix.mul_inv_rev, bd_mul (Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv hy).1
        (Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv hx).1, rvM_mul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem smul_UP (x : UP p) (X : MP p) :
    x • X = (((x : GG p).1 : GLp p) : MP p) * X * (((x : GG p).2.unop : GLp p) : MP p) := rfl

/- English proof (translation)
Rewrite using `[smul_UP]`. Use `show bd a _ * a.mat * rvM a (bd a _) = a.mat`. Establish `hx` using `UP_lo x`. Rewrite using `[bd_mat, Matrix.mul_assoc, ← rvM_mul, ← bd_mul hx (Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv hx).1, (Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv hx).2.2, bd_one, rvM_one, Matrix.mul_one]`.
-/
theorem retr_stab (x : UP p) : retr a x • a.mat = a.mat := by
  rw [smul_UP]
  show bd a _ * a.mat * rvM a (bd a _) = a.mat
  have hx := UP_lo x
  rw [bd_mat, Matrix.mul_assoc, ← rvM_mul, ← bd_mul hx (Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv hx).1,
    (Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv hx).2.2, bd_one, rvM_one, Matrix.mul_one]

/- English proof (translation)
Rewrite `hs` using `[smul_UP]`. Apply `UP_ext` to reduce the goal to its premises. Conclude with `bd_of_stab (UP_lo s) (UP_up s) hs`. Conclude with `(rho_of_stab (UP_lo s) (UP_up s) hs).symm`.
-/
theorem retr_id (s : UP p) (hs : s • a.mat = a.mat) : retr a s = s := by
  rw [smul_UP] at hs
  apply UP_ext
  · exact bd_of_stab (UP_lo s) (UP_up s) hs
  · exact (rho_of_stab (UP_lo s) (UP_up s) hs).symm

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Use `⟨fun i => ?_, fun i j hij => ?_, fun i j => ?_⟩` and prove the remaining obligations. Unfold `bd`. Rewrite using `[if_pos rfl]`. Conclude with `h1 i`.

Unfold `bd`. Use `split_ifs`. Conclude with `h2 i j hij`. Both sides reduce to the same expression. Unfold `bd`.

Use `split_ifs`. Conclude with `h3 i j`. Conclude with `(M p).R.zero_mem`.
-/
theorem intLow_bd {l : MP p} (h : Formalism.MainNotions.S.TieN.IntLow (M p) l) : Formalism.MainNotions.S.TieN.IntLow (M p) (bd a l) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun i => ?_, fun i j hij => ?_, fun i j => ?_⟩
  · unfold bd; rw [if_pos rfl]; exact h1 i
  · unfold bd; split_ifs
    · exact h2 i j hij
    · rfl
  · unfold bd; split_ifs
    · exact h3 i j
    · exact (M p).R.zero_mem

/- English proof (translation)
Establish `hl2` using `h.2.1`. Establish `hb` using `intLow_bd M a h`. Take `⟨h1, h2, h3⟩` from `hb`. Use `⟨fun i => h1 _, fun i j hij => ?_, fun i j => h3 _ _⟩` and prove the remaining obligations. Use `show bd a l (rv a i) (rv a j) = 0`.

Unfold `bd`. Use `split_ifs with hb'`. Rewrite `hb'` using `[bk_rv, bk_rv]`. Conclude with `hl2 _ _ (rv_anti a hij hb'.symm)`. Both sides reduce to the same expression.
-/
theorem intUp_rvM {l : MP p} (h : Formalism.MainNotions.S.TieN.IntLow (M p) l) :
    Formalism.MainNotions.S.TieN.IntUp (M p) (rvM a (bd a l)) := by
  have hl2 := h.2.1
  have hb := intLow_bd M a h
  obtain ⟨h1, h2, h3⟩ := hb
  refine ⟨fun i => h1 _, fun i j hij => ?_, fun i j => h3 _ _⟩
  show bd a l (rv a i) (rv a j) = 0
  unfold bd
  split_ifs with hb'
  · rw [bk_rv, bk_rv] at hb'
    exact hl2 _ _ (rv_anti a hij hb'.symm)
  · rfl

/- English proof (translation)
Take `⟨h1, -⟩` from `hk`. Establish `hi` using `(Formalism.L2.SG.Pf.ZsVolGrp.intLow_inv (M p) h1).1`. Conclude with `⟨intLow_bd M a h1, intUp_rvM M a hi⟩`.
-/
theorem retr_K (k : UP p) (hk : k ∈ KU M p) : retr a k ∈ KU M p := by
  obtain ⟨h1, -⟩ := hk
  have hi := (Formalism.L2.SG.Pf.ZsVolGrp.intLow_inv (M p) h1).1
  exact ⟨intLow_bd M a h1, intUp_rvM M a hi⟩

/- English proof (translation)
Use `⟨retr a, ⟨fun x => (MulAction.mem_stabilizer_iff).symm, fun x => retr_stab a x, fun s hs => retr_id a s hs, fun x => MonoidHom.mem_ker, fun k hk => retr_K M a k hk⟩, fun x => ?_⟩` and prove the remaining obligations. Establish `hx` using `UP_lo x`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1 : bd a (((x : GG p).1 : GLp p) : MP p) = 1`.

Rewrite using `[← retrFun_fst a x]`. Use `show ((((retr a x : UP p) : GG p).1 : GLp p) : MP p) = 1`. Rewrite using `[h]`. Both sides reduce to the same expression. Use `⟨hx, fun i j hij hs => ?_⟩` and prove the remaining obligations.

Conclude with `(bd_eq_one_iff hx).1 h1 i j hij ((sameBlock_iff a i j).1 hs)`. Introduce and unpack `⟨-, hV⟩`. Establish `h1 : bd a (((x : GG p).1 : GLp p) : MP p) = 1` using `(bd_eq_one_iff hx).2 fun i j hij hb => hV i j hij ((sameBlock_iff a i j).2 hb)`. Apply `UP_ext` to reduce the goal to its premises. Use `show bd a _ = _`.

Rewrite using `[h1]`. Both sides reduce to the same expression. Use `show rvM a (bd a _) = _`. Rewrite using `[bd_inv hx, h1, inv_one, rvM_one]`. Both sides reduce to the same expression.
-/
theorem blockRetr_holds : BlockRetr M p a := by
  refine ⟨retr a, ⟨fun x => (MulAction.mem_stabilizer_iff).symm, fun x => retr_stab a x,
    fun s hs => retr_id a s hs, fun x => MonoidHom.mem_ker, fun k hk => retr_K M a k hk⟩, fun x => ?_⟩
  have hx := UP_lo x
  constructor
  · intro h
    have h1 : bd a (((x : GG p).1 : GLp p) : MP p) = 1 := by
      rw [← retrFun_fst a x]
      show ((((retr a x : UP p) : GG p).1 : GLp p) : MP p) = 1
      rw [h]; rfl
    refine ⟨hx, fun i j hij hs => ?_⟩
    exact (bd_eq_one_iff hx).1 h1 i j hij ((sameBlock_iff a i j).1 hs)
  · rintro ⟨-, hV⟩
    have h1 : bd a (((x : GG p).1 : GLp p) : MP p) = 1 :=
      (bd_eq_one_iff hx).2 fun i j hij hb => hV i j hij ((sameBlock_iff a i j).2 hb)
    apply UP_ext
    · show bd a _ = _
      rw [h1]; rfl
    · show rvM a (bd a _) = _
      rw [bd_inv hx, h1, inv_one, rvM_one]; rfl

end Retr

end Formalism.L2.SG.Pf.CountAt
