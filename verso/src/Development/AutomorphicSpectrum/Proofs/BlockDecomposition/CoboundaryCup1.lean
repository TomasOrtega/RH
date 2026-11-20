import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BisimplicialActionSecondFactor

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct GlobalTheory.CatCoh MainStatements.Hodge GlobalTheory.CompanionTheory.HodgeCx GlobalTheory.CompanionTheory.HopfLe

namespace GlobalTheory.CompanionTheory.HopfLe.DnCup

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C]

abbrev dl (n : ℕ) (i : Fin (n + 2)) : Fin (n + 1) →o Fin (n + 2) := (Fin.succAboveOrderEmb i).toOrderHom

def incl (n : ℕ) : Fin 3 →o Fin (n + 3) := ⟨Fin.castLE (by omega), fun _ _ h ↦ h⟩

/- English proof (translation)
The claim follows from `Fin.sum_univ_succ f`.
-/
private theorem sum_fin_add_two_eq_zero_add_sum_succ {M : Type*} [AddCommMonoid M] {m : ℕ} (f : Fin (m + 2) → M) :
    ∑ i, f i = f 0 + ∑ k : Fin (m + 1), f k.succ :=
  Fin.sum_univ_succ f

/- English proof (translation)
The claim follows from `((Fin.sum_univ_succ f).trans (congrArg _ (Fin.sum_univ_succ fun i : Fin (m + 1) => f i.succ))).trans (add_assoc _ _ _).symm`.
-/
private theorem sum_fin_add_two_eq_zero_add_one_add_sum {M : Type*} [AddCommMonoid M] {m : ℕ} (f : Fin (m + 2) → M) :
    ∑ i, f i = f 0 + f 1 + ∑ k : Fin m, f k.succ.succ :=
  ((Fin.sum_univ_succ f).trans
    (congrArg _ (Fin.sum_univ_succ fun i : Fin (m + 1) => f i.succ))).trans (add_assoc _ _ _).symm

/- English proof (translation)
Establish `hv : GlobalTheory.CompanionTheory.HopfLe.DnCup.dl n i j = i.succAbove j`. Simplify using `only [OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]`. Rewrite using `[hv]`. Break down `Nat.lt_or_ge (j : ℕ) i with h | h` into its components or cases. Use `left`.

Use `⟨h, ?_⟩` and prove the remaining obligations. Rewrite using `[Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def, Fin.coe_castSucc]; exact h), Fin.coe_castSucc]`. Use `right`. Use `⟨h, ?_⟩` and prove the remaining obligations. Rewrite using `[Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def, Fin.coe_castSucc]; exact h), Fin.val_succ]`.
-/
theorem dl_spec (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 1)) :
    ((j : ℕ) < i ∧ (dl n i j : ℕ) = j) ∨ ((i : ℕ) ≤ j ∧ (dl n i j : ℕ) = j + 1) := by
  have hv : GlobalTheory.CompanionTheory.HopfLe.DnCup.dl n i j = i.succAbove j := by
    simp only [OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rw [hv]
  rcases Nat.lt_or_ge (j : ℕ) i with h | h
  · left
    refine ⟨h, ?_⟩
    rw [Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def, Fin.coe_castSucc]; exact h),
      Fin.coe_castSucc]
  · right
    refine ⟨h, ?_⟩
    rw [Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def, Fin.coe_castSucc]; exact h),
      Fin.val_succ]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem front_val (n : ℕ) (j : Fin 2) : (front n j : ℕ) = j := rfl

/- English proof (translation)
Establish `hv : GlobalTheory.CompanionTheory.HopfLe.back n j = Fin.succAbove 0 j`. Simplify using `only [GlobalTheory.CompanionTheory.HopfLe.back, OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]`. Rewrite using `[hv, Fin.succAbove_of_le_castSucc _ _ (by simp), Fin.val_succ]`.
-/
theorem back_val (n : ℕ) (j : Fin (n + 1)) : (back n j : ℕ) = j + 1 := by
  have hv : GlobalTheory.CompanionTheory.HopfLe.back n j = Fin.succAbove 0 j := by
    simp only [GlobalTheory.CompanionTheory.HopfLe.back, OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rw [hv, Fin.succAbove_of_le_castSucc _ _ (by simp), Fin.val_succ]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem incl_val (n : ℕ) (j : Fin 3) : (incl n j : ℕ) = j := rfl

/- English proof (translation)
Use `DFunLike.ext _ _ fun j => Fin.ext ?_` and prove the remaining obligations. Establish `h1` using `GlobalTheory.CompanionTheory.HopfLe.DnCup.front_val n j`. Establish `h2` using `GlobalTheory.CompanionTheory.HopfLe.DnCup.front_val (n + 1) j`. Establish `h3` using `GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec (n + 1) k.succ.succ (GlobalTheory.CompanionTheory.HopfLe.front n j)`. Establish `hj` using `j.isLt`.

Simplify using `only [OrderHom.comp_coe, Function.comp_apply, Fin.val_succ] at *`. Use linear arithmetic over natural numbers and integers.
-/
theorem dl_front_high (n : ℕ) (k : Fin (n + 1)) : (dl (n + 1) k.succ.succ).comp (front n) = front (n + 1) := by
  refine DFunLike.ext _ _ fun j => Fin.ext ?_
  have h1 := GlobalTheory.CompanionTheory.HopfLe.DnCup.front_val n j
  have h2 := GlobalTheory.CompanionTheory.HopfLe.DnCup.front_val (n + 1) j
  have h3 := GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec (n + 1) k.succ.succ (GlobalTheory.CompanionTheory.HopfLe.front n j)
  have hj := j.isLt
  simp only [OrderHom.comp_coe, Function.comp_apply, Fin.val_succ] at *
  omega

/- English proof (translation)
Use `DFunLike.ext _ _ fun j => Fin.ext ?_` and prove the remaining obligations. Establish `h1` using `GlobalTheory.CompanionTheory.HopfLe.DnCup.back_val n j`. Establish `h2` using `GlobalTheory.CompanionTheory.HopfLe.DnCup.back_val (n + 1) (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl n k.succ j)`. Establish `h3` using `GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec (n + 1) k.succ.succ (GlobalTheory.CompanionTheory.HopfLe.back n j)`. Establish `h4` using `GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec n k.succ j`.

Simplify using `only [OrderHom.comp_coe, Function.comp_apply, Fin.val_succ] at *`. Use linear arithmetic over natural numbers and integers.
-/
theorem dl_back_high (n : ℕ) (k : Fin (n + 1)) :
    (dl (n + 1) k.succ.succ).comp (back n) = (back (n + 1)).comp (dl n k.succ) := by
  refine DFunLike.ext _ _ fun j => Fin.ext ?_
  have h1 := GlobalTheory.CompanionTheory.HopfLe.DnCup.back_val n j
  have h2 := GlobalTheory.CompanionTheory.HopfLe.DnCup.back_val (n + 1) (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl n k.succ j)
  have h3 := GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec (n + 1) k.succ.succ (GlobalTheory.CompanionTheory.HopfLe.back n j)
  have h4 := GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec n k.succ j
  simp only [OrderHom.comp_coe, Function.comp_apply, Fin.val_succ] at *
  omega

/- English proof (translation)
Use `DFunLike.ext _ _ fun j => Fin.ext ?_` and prove the remaining obligations. Establish `h1` using `GlobalTheory.CompanionTheory.HopfLe.DnCup.back_val n j`. Establish `h2` using `GlobalTheory.CompanionTheory.HopfLe.DnCup.back_val (n + 1) (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl n 0 j)`. Establish `h3` using `GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec (n + 1) 0 (GlobalTheory.CompanionTheory.HopfLe.back n j)`. Establish `h4` using `GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec n 0 j`.

Simplify using `only [OrderHom.comp_coe, Function.comp_apply, Fin.val_zero] at *`. Use linear arithmetic over natural numbers and integers.
-/
theorem dl_back_zero (n : ℕ) : (dl (n + 1) 0).comp (back n) = (back (n + 1)).comp (dl n 0) := by
  refine DFunLike.ext _ _ fun j => Fin.ext ?_
  have h1 := GlobalTheory.CompanionTheory.HopfLe.DnCup.back_val n j
  have h2 := GlobalTheory.CompanionTheory.HopfLe.DnCup.back_val (n + 1) (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl n 0 j)
  have h3 := GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec (n + 1) 0 (GlobalTheory.CompanionTheory.HopfLe.back n j)
  have h4 := GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec n 0 j
  simp only [OrderHom.comp_coe, Function.comp_apply, Fin.val_zero] at *
  omega

/- English proof (translation)
Use `DFunLike.ext _ _ fun j => Fin.ext ?_` and prove the remaining obligations. Establish `h1` using `GlobalTheory.CompanionTheory.HopfLe.DnCup.back_val n j`. Establish `h2` using `GlobalTheory.CompanionTheory.HopfLe.DnCup.back_val (n + 1) (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl n 0 j)`. Establish `h3` using `GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec (n + 1) 1 (GlobalTheory.CompanionTheory.HopfLe.back n j)`. Establish `h4` using `GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec n 0 j`.

Simplify using `only [OrderHom.comp_coe, Function.comp_apply, Fin.val_zero, Fin.val_one] at *`. Use linear arithmetic over natural numbers and integers.
-/
theorem dl_back_one (n : ℕ) : (dl (n + 1) 1).comp (back n) = (back (n + 1)).comp (dl n 0) := by
  refine DFunLike.ext _ _ fun j => Fin.ext ?_
  have h1 := GlobalTheory.CompanionTheory.HopfLe.DnCup.back_val n j
  have h2 := GlobalTheory.CompanionTheory.HopfLe.DnCup.back_val (n + 1) (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl n 0 j)
  have h3 := GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec (n + 1) 1 (GlobalTheory.CompanionTheory.HopfLe.back n j)
  have h4 := GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec n 0 j
  simp only [OrderHom.comp_coe, Function.comp_apply, Fin.val_zero, Fin.val_one] at *
  omega

/- English proof (translation)
Use `DFunLike.ext _ _ fun j => Fin.ext ?_` and prove the remaining obligations. Establish `h1` using `GlobalTheory.CompanionTheory.HopfLe.DnCup.front_val n j`. Establish `h2` using `GlobalTheory.CompanionTheory.HopfLe.DnCup.incl_val n (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl 1 0 j)`. Establish `h3` using `GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec (n + 1) 0 (GlobalTheory.CompanionTheory.HopfLe.front n j)`. Establish `h4` using `GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec 1 0 j`.

Simplify using `only [OrderHom.comp_coe, Function.comp_apply, Fin.val_zero] at *`. Use linear arithmetic over natural numbers and integers.
-/
theorem dl_front_zero (n : ℕ) : (dl (n + 1) 0).comp (front n) = (incl n).comp (dl 1 0) := by
  refine DFunLike.ext _ _ fun j => Fin.ext ?_
  have h1 := GlobalTheory.CompanionTheory.HopfLe.DnCup.front_val n j
  have h2 := GlobalTheory.CompanionTheory.HopfLe.DnCup.incl_val n (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl 1 0 j)
  have h3 := GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec (n + 1) 0 (GlobalTheory.CompanionTheory.HopfLe.front n j)
  have h4 := GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec 1 0 j
  simp only [OrderHom.comp_coe, Function.comp_apply, Fin.val_zero] at *
  omega

/- English proof (translation)
Use `DFunLike.ext _ _ fun j => Fin.ext ?_` and prove the remaining obligations. Establish `h1` using `GlobalTheory.CompanionTheory.HopfLe.DnCup.front_val n j`. Establish `h2` using `GlobalTheory.CompanionTheory.HopfLe.DnCup.incl_val n (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl 1 1 j)`. Establish `h3` using `GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec (n + 1) 1 (GlobalTheory.CompanionTheory.HopfLe.front n j)`. Establish `h4` using `GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec 1 1 j`.

Simplify using `only [OrderHom.comp_coe, Function.comp_apply, Fin.val_one] at *`. Use linear arithmetic over natural numbers and integers.
-/
theorem dl_front_one (n : ℕ) : (dl (n + 1) 1).comp (front n) = (incl n).comp (dl 1 1) := by
  refine DFunLike.ext _ _ fun j => Fin.ext ?_
  have h1 := GlobalTheory.CompanionTheory.HopfLe.DnCup.front_val n j
  have h2 := GlobalTheory.CompanionTheory.HopfLe.DnCup.incl_val n (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl 1 1 j)
  have h3 := GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec (n + 1) 1 (GlobalTheory.CompanionTheory.HopfLe.front n j)
  have h4 := GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec 1 1 j
  simp only [OrderHom.comp_coe, Function.comp_apply, Fin.val_one] at *
  omega

/- English proof (translation)
Use `DFunLike.ext _ _ fun j => Fin.ext ?_` and prove the remaining obligations. Establish `h1` using `GlobalTheory.CompanionTheory.HopfLe.DnCup.front_val (n + 1) j`. Establish `h2` using `GlobalTheory.CompanionTheory.HopfLe.DnCup.incl_val n (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl 1 2 j)`. Establish `h3` using `GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec 1 2 j`. Establish `h5 : ((2 : Fin (1 + 2)) : ℕ) = 2` using `rfl`.

Establish `hj` using `j.isLt`. Simplify using `only [OrderHom.comp_coe, Function.comp_apply] at *`. Use linear arithmetic over natural numbers and integers.
-/
theorem front_eq_incl (n : ℕ) : front (n + 1) = (incl n).comp (dl 1 2) := by
  refine DFunLike.ext _ _ fun j => Fin.ext ?_
  have h1 := GlobalTheory.CompanionTheory.HopfLe.DnCup.front_val (n + 1) j
  have h2 := GlobalTheory.CompanionTheory.HopfLe.DnCup.incl_val n (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl 1 2 j)
  have h3 := GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec 1 2 j
  have h5 : ((2 : Fin (1 + 2)) : ℕ) = 2 := rfl
  have hj := j.isLt
  simp only [OrderHom.comp_coe, Function.comp_apply] at *
  omega

/- English proof (translation)
Establish `hface : ∀ (m : ℕ) (j : Fin (m + 2)), MainStatements.Hodge.cof F m j = GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl m j)` using `fun m j => GlobalTheory.CompanionTheory.HodgeCx.cof_eq F m j`. Establish `hd : MainStatements.Hodge.dn F 1 y = GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl 1 0) y - GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl 1 1) y + GlobalTheory.CompanionTheory.HodgeCx.act F (Glo …`. Rewrite using `[MainStatements.Hodge.dn, LinearMap.sum_apply, Fin.sum_univ_three]`. Simplify using `only [LinearMap.smul_apply, hface, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, neg_one_sq, one_smul, neg_smul, sub_eq_add_neg]`. Apply the tactic sequence `first | done | rfl`.

Rewrite using `[GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_front_zero, GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_front_one, GlobalTheory.CompanionTheory.HopfLe.DnCup.front_eq_incl, GlobalTheory.CompanionTheory.HodgeCx.act_comp, GlobalTheory.CompanionTheory.HodgeCx.act_comp, GlobalTheory.Co …`.
-/
theorem bracket (F : C ⥤ CommAlgCat.{0} R) (n : ℕ) (y : Cn F 1) (hy : dn F 1 y = 0) :
    act F ((dl (n + 1) 0).comp (front n)) y - act F ((dl (n + 1) 1).comp (front n)) y
      + act F (front (n + 1)) y = 0 := by
  have hface : ∀ (m : ℕ) (j : Fin (m + 2)),
      MainStatements.Hodge.cof F m j = GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl m j) :=
    fun m j => GlobalTheory.CompanionTheory.HodgeCx.cof_eq F m j
  have hd : MainStatements.Hodge.dn F 1 y =
      GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl 1 0) y - GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl 1 1) y
        + GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl 1 2) y := by
    rw [MainStatements.Hodge.dn, LinearMap.sum_apply, Fin.sum_univ_three]
    simp only [LinearMap.smul_apply, hface, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero,
      pow_one, neg_one_sq, one_smul, neg_smul, sub_eq_add_neg]
    first | done | rfl
  rw [GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_front_zero, GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_front_one, GlobalTheory.CompanionTheory.HopfLe.DnCup.front_eq_incl,
    GlobalTheory.CompanionTheory.HodgeCx.act_comp, GlobalTheory.CompanionTheory.HodgeCx.act_comp, GlobalTheory.CompanionTheory.HodgeCx.act_comp,
    ← map_sub, ← map_add, ← hd, hy, map_zero]

/- English proof (translation)
Establish `hface : ∀ (m : ℕ) (j : Fin (m + 2)), MainStatements.Hodge.cof F m j = GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl m j)` using `fun m j => GlobalTheory.CompanionTheory.HodgeCx.cof_eq F m j`. Establish `hcup : ∀ i : Fin (n + 1 + 2), MainStatements.Hodge.cof F (n + 1) i (GlobalTheory.CompanionTheory.HopfLe.cup1 F y z) = GlobalTheory.CompanionTheory.HodgeCx.act F ((GlobalTheory.CompanionTheory.HopfLe.DnCup.dl (n + 1) i).comp (GlobalTheory.CompanionTheory.HopfLe.front n)) y * Globa …`. Introduce `i`. Rewrite using `[hface, GlobalTheory.CompanionTheory.HopfLe.cup1, GlobalTheory.CompanionTheory.HopfLe.act_mul, GlobalTheory.CompanionTheory.HodgeCx.act_comp F (GlobalTheory.CompanionTheory.HopfLe.front n), GlobalTheory.CompanionTheory.HodgeCx.act_comp F (GlobalTheory.CompanionTheory.HopfLe.back …`. Establish `hback : ∀ {k : ℕ} (θ : Fin (k + 1) →o Fin (n + 1 + 1)) (w : MainStatements.Hodge.Cn F k), GlobalTheory.CompanionTheory.HodgeCx.act F ((GlobalTheory.CompanionTheory.HopfLe.back (n + 1)).comp θ) w = GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.bac …` using `fun θ w => GlobalTheory.CompanionTheory.HodgeCx.act_comp F θ (GlobalTheory.CompanionTheory.HopfLe.back (n + 1)) w`.

Establish `h'` using `eq_neg_iff_add_eq_zero.mpr (GlobalTheory.CompanionTheory.HopfLe.DnCup.bracket F n y hy)`. Establish `key : GlobalTheory.CompanionTheory.HodgeCx.act F ((GlobalTheory.CompanionTheory.HopfLe.DnCup.dl (n + 1) 0).comp (GlobalTheory.CompanionTheory.HopfLe.front n)) y * GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.back (n + 1)) (GlobalTheory.Companion …`. Rewrite using `[← neg_mul, ← add_mul, ← h']`. Use `congr 1`. Normalize the expressions using the abelian group laws.

Establish `h0 : MainStatements.Hodge.cof F (n + 1) 0 (GlobalTheory.CompanionTheory.HopfLe.cup1 F y z) = GlobalTheory.CompanionTheory.HodgeCx.act F ((GlobalTheory.CompanionTheory.HopfLe.DnCup.dl (n + 1) 0).comp (GlobalTheory.CompanionTheory.HopfLe.front n)) y * GlobalTheory.CompanionTheory.H …`. Rewrite using `[hcup, GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_back_zero, hback]`. Establish `h1 : MainStatements.Hodge.cof F (n + 1) 1 (GlobalTheory.CompanionTheory.HopfLe.cup1 F y z) = GlobalTheory.CompanionTheory.HodgeCx.act F ((GlobalTheory.CompanionTheory.HopfLe.DnCup.dl (n + 1) 1).comp (GlobalTheory.CompanionTheory.HopfLe.front n)) y * GlobalTheory.CompanionTheory.H …`. Rewrite using `[hcup, GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_back_one, hback]`. Establish `hk : ∀ k : Fin (n + 1), MainStatements.Hodge.cof F (n + 1) k.succ.succ (GlobalTheory.CompanionTheory.HopfLe.cup1 F y z) = GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.front (n + 1)) y * GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.Co …`.

Introduce `k`. Rewrite using `[hcup, GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_back_high, hback]`. Use `congr 1`. Conclude with `congrArg (fun θ : Fin 2 →o Fin (n + 1 + 2) => GlobalTheory.CompanionTheory.HodgeCx.act F θ y) (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_front_high n k)`. Simplify using `only [MainStatements.Hodge.dn, LinearMap.sum_apply, LinearMap.smul_apply]`.

Rewrite using `[sum_fin_add_two_eq_zero_add_one_add_sum (m := n + 1), sum_fin_add_two_eq_zero_add_sum_succ (m := n), h0, h1]`. Simplify using `only [hk]`. Simplify using `only [hface, GlobalTheory.CompanionTheory.HopfLe.cup1, map_add, map_neg, map_sum, map_smul, map_zsmul, mul_add, Finset.mul_sum, mul_smul_comm, Fin.val_zero, Fin.val_one, Fin.val_succ, pow_zero, pow_one, pow_succ, one_smul, neg_smul, mul_neg, mul_one, neg_neg, Finset.sum_neg_distr …`. Rewrite using `[key]`. Normalize the expressions using the abelian group laws.
-/
theorem coboundary_cup1 (F : C ⥤ CommAlgCat.{0} R) {n : ℕ} (y : Cn F 1) (z : Cn F n) (hy : dn F 1 y = 0) :
    dn F (n + 1) (cup1 F y z) = - cup1 F y (dn F n z) := by
  have hface : ∀ (m : ℕ) (j : Fin (m + 2)),
      MainStatements.Hodge.cof F m j = GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl m j) :=
    fun m j => GlobalTheory.CompanionTheory.HodgeCx.cof_eq F m j
  have hcup : ∀ i : Fin (n + 1 + 2), MainStatements.Hodge.cof F (n + 1) i (GlobalTheory.CompanionTheory.HopfLe.cup1 F y z) =
      GlobalTheory.CompanionTheory.HodgeCx.act F ((GlobalTheory.CompanionTheory.HopfLe.DnCup.dl (n + 1) i).comp (GlobalTheory.CompanionTheory.HopfLe.front n)) y *
        GlobalTheory.CompanionTheory.HodgeCx.act F ((GlobalTheory.CompanionTheory.HopfLe.DnCup.dl (n + 1) i).comp (GlobalTheory.CompanionTheory.HopfLe.back n)) z := by
    intro i
    rw [hface, GlobalTheory.CompanionTheory.HopfLe.cup1, GlobalTheory.CompanionTheory.HopfLe.act_mul,
      GlobalTheory.CompanionTheory.HodgeCx.act_comp F (GlobalTheory.CompanionTheory.HopfLe.front n),
      GlobalTheory.CompanionTheory.HodgeCx.act_comp F (GlobalTheory.CompanionTheory.HopfLe.back n)]
  have hback : ∀ {k : ℕ} (θ : Fin (k + 1) →o Fin (n + 1 + 1)) (w : MainStatements.Hodge.Cn F k),
      GlobalTheory.CompanionTheory.HodgeCx.act F ((GlobalTheory.CompanionTheory.HopfLe.back (n + 1)).comp θ) w =
        GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.back (n + 1)) (GlobalTheory.CompanionTheory.HodgeCx.act F θ w) :=
    fun θ w => GlobalTheory.CompanionTheory.HodgeCx.act_comp F θ (GlobalTheory.CompanionTheory.HopfLe.back (n + 1)) w
  have h' := eq_neg_iff_add_eq_zero.mpr (GlobalTheory.CompanionTheory.HopfLe.DnCup.bracket F n y hy)
  have key : GlobalTheory.CompanionTheory.HodgeCx.act F ((GlobalTheory.CompanionTheory.HopfLe.DnCup.dl (n + 1) 0).comp (GlobalTheory.CompanionTheory.HopfLe.front n)) y *
        GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.back (n + 1)) (GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl n 0) z) =
      GlobalTheory.CompanionTheory.HodgeCx.act F ((GlobalTheory.CompanionTheory.HopfLe.DnCup.dl (n + 1) 1).comp (GlobalTheory.CompanionTheory.HopfLe.front n)) y *
        GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.back (n + 1)) (GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl n 0) z) +
      -(GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.front (n + 1)) y *
        GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.back (n + 1)) (GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl n 0) z)) := by
    rw [← neg_mul, ← add_mul, ← h']
    congr 1
    abel
  have h0 : MainStatements.Hodge.cof F (n + 1) 0 (GlobalTheory.CompanionTheory.HopfLe.cup1 F y z) =
      GlobalTheory.CompanionTheory.HodgeCx.act F ((GlobalTheory.CompanionTheory.HopfLe.DnCup.dl (n + 1) 0).comp (GlobalTheory.CompanionTheory.HopfLe.front n)) y *
        GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.back (n + 1)) (GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl n 0) z) := by
    rw [hcup, GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_back_zero, hback]
  have h1 : MainStatements.Hodge.cof F (n + 1) 1 (GlobalTheory.CompanionTheory.HopfLe.cup1 F y z) =
      GlobalTheory.CompanionTheory.HodgeCx.act F ((GlobalTheory.CompanionTheory.HopfLe.DnCup.dl (n + 1) 1).comp (GlobalTheory.CompanionTheory.HopfLe.front n)) y *
        GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.back (n + 1)) (GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl n 0) z) := by
    rw [hcup, GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_back_one, hback]
  have hk : ∀ k : Fin (n + 1), MainStatements.Hodge.cof F (n + 1) k.succ.succ (GlobalTheory.CompanionTheory.HopfLe.cup1 F y z) =
      GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.front (n + 1)) y *
        GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.back (n + 1))
          (GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl n k.succ) z) := by
    intro k
    rw [hcup, GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_back_high, hback]
    congr 1
    exact congrArg (fun θ : Fin 2 →o Fin (n + 1 + 2) => GlobalTheory.CompanionTheory.HodgeCx.act F θ y)
      (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_front_high n k)
  simp only [MainStatements.Hodge.dn, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [sum_fin_add_two_eq_zero_add_one_add_sum (m := n + 1), sum_fin_add_two_eq_zero_add_sum_succ (m := n), h0, h1]
  simp only [hk]
  simp only [hface, GlobalTheory.CompanionTheory.HopfLe.cup1, map_add, map_neg, map_sum, map_smul, map_zsmul,
    mul_add, Finset.mul_sum, mul_smul_comm, Fin.val_zero, Fin.val_one, Fin.val_succ, pow_zero,
    pow_one, pow_succ, one_smul, neg_smul, mul_neg, mul_one, neg_neg, Finset.sum_neg_distrib]
  rw [key]
  abel

end GlobalTheory.CompanionTheory.HopfLe.DnCup
