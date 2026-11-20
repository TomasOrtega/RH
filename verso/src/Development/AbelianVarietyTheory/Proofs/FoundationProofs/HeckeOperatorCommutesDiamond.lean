import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMulOfDetZero
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

noncomputable section

namespace GlobalTheory.Hk.CommTD

def tri (q : ℕ) : Option (Fin q) → Matrix (Fin 2) (Fin 2) ℤ
  | none => !![(q : ℤ), 0; 0, 1]
  | some u => !![1, ((u : ℕ) : ℤ); 0, (q : ℤ)]

/- English proof (translation)
Apply the tactic sequence `cases x <;> simp [tri, Matrix.det_fin_two_of]`.
-/
theorem tri_det (q : ℕ) (x : Option (Fin q)) : (tri q x).det = q := by
  cases x <;> simp [tri, Matrix.det_fin_two_of]

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.DetZeroFactorization.main`. Consider the case `exact _root_.GlobalTheory.DetZeroFactorization.main`. Consider the case `(apply _root_.GlobalTheory.DetZeroFactorization.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.DetZeroFactorization.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.DetZeroFactorization.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.DetZeroFactorization.main ..)`.
-/
theorem tri_exists {q : ℕ} (hp : q.Prime) (δ : Matrix (Fin 2) (Fin 2) ℤ) (hδ : δ.det = q) :
    ∃ (γ : SL(2, ℤ)) (y : Option (Fin q)), δ = γ.1 * tri q y := by
  first
  | exact @_root_.GlobalTheory.DetZeroFactorization.main
  | exact _root_.GlobalTheory.DetZeroFactorization.main
  | (apply _root_.GlobalTheory.DetZeroFactorization.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.DetZeroFactorization.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DetZeroFactorization.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DetZeroFactorization.main ..)

def rep (q : ℕ) (w : SL(2, ℤ)) : Option (Fin q) → Matrix (Fin 2) (Fin 2) ℤ
  | none => w.1 * tri q none
  | some u => tri q (some u)

/- English proof (translation)
Consider the cases of `x with`. Consider the case `none => simp [rep, Matrix.det_mul, tri_det]`. Consider the case `some u => exact tri_det q (some u)`.
-/
theorem rep_det (q : ℕ) (w : SL(2, ℤ)) (x : Option (Fin q)) : (rep q w x).det = q := by
  cases x with
  | none => simp [rep, Matrix.det_mul, tri_det]
  | some u => exact tri_det q (some u)

/- English proof (translation)
Simplify using `[rep, tri, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]`.
-/
theorem rep_none_entries (q : ℕ) (w : SL(2, ℤ)) :
    rep q w none 0 0 = q * w 0 0 ∧ rep q w none 0 1 = w 0 1 ∧
      rep q w none 1 0 = q * w 1 0 ∧ rep q w none 1 1 = w 1 1 := by
  simp [rep, tri, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

/- English proof (translation)
Establish `hnd : ¬ (q : ℤ) ∣ 1` using `fun h => hp.not_dvd_one (by exact_mod_cast h)`. Establish `h00` using `congrFun (congrFun h 0) 0`. Establish `h01` using `congrFun (congrFun h 0) 1`. Establish `h10` using `congrFun (congrFun h 1) 0`. Establish `h11` using `congrFun (congrFun h 1) 1`.

Establish `dγ` using `γ.det_coe`. Establish `dw` using `w.det_coe`. Rewrite `dγ`, `dw` using `[Matrix.det_fin_two]`. Take `⟨e00, e01, e10, e11⟩` from `rep_none_entries q w`. Apply the tactic sequence `rcases x with _ | u <;> rcases y with _ | v`.

Both sides reduce to the same expression. Simplify using `[rep, tri, Matrix.mul_apply, Fin.sum_univ_two, e00, e10] at h00 h10`. Conclude with `absurd ⟨w 0 0 * γ 1 1 - γ 0 1 * w 1 0, by rw [← h00, ← h10] at dγ; linear_combination -dγ⟩ hnd`. Simplify using `[rep, tri, Matrix.mul_apply, Fin.sum_univ_two, e00, e10] at h00 h10`. Conclude with `absurd ⟨γ 0 0 * w 0 0 + γ 0 1 * w 1 0, by linear_combination h00⟩ hnd`.

Simplify using `[rep, tri, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 ⊢`. Rewrite `h01` using `[← h00]`. Establish `: (u : ℤ) ≡ (v : ℤ) [ZMOD q]` using `(Int.modEq_iff_dvd.2 ⟨γ 0 1, by linear_combination h01⟩).symm`. Establish `h2 : (u : ℕ) ≡ (v : ℕ) [MOD q]` using `Int.natCast_modEq_iff.1 this`. Conclude with `Fin.ext (Nat.ModEq.eq_of_lt_of_lt h2 u.2 v.2)`.
-/
theorem rep_inj {q : ℕ} (hp : q.Prime) (w : SL(2, ℤ)) (γ : SL(2, ℤ)) {x y : Option (Fin q)}
    (h : rep q w x = γ.1 * rep q w y) : x = y := by
  have hnd : ¬ (q : ℤ) ∣ 1 := fun h => hp.not_dvd_one (by exact_mod_cast h)
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  have h11 := congrFun (congrFun h 1) 1
  have dγ := γ.det_coe
  have dw := w.det_coe
  rw [Matrix.det_fin_two] at dγ dw
  obtain ⟨e00, e01, e10, e11⟩ := rep_none_entries q w
  rcases x with _ | u <;> rcases y with _ | v
  · rfl
  · simp [rep, tri, Matrix.mul_apply, Fin.sum_univ_two, e00, e10] at h00 h10
    exact absurd ⟨w 0 0 * γ 1 1 - γ 0 1 * w 1 0, by rw [← h00, ← h10] at dγ; linear_combination -dγ⟩ hnd
  · simp [rep, tri, Matrix.mul_apply, Fin.sum_univ_two, e00, e10] at h00 h10
    exact absurd ⟨γ 0 0 * w 0 0 + γ 0 1 * w 1 0, by linear_combination h00⟩ hnd
  · simp [rep, tri, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 ⊢
    rw [← h00] at h01
    have : (u : ℤ) ≡ (v : ℤ) [ZMOD q] := (Int.modEq_iff_dvd.2 ⟨γ 0 1, by linear_combination h01⟩).symm
    have h2 : (u : ℕ) ≡ (v : ℕ) [MOD q] := Int.natCast_modEq_iff.1 this
    exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt h2 u.2 v.2)

end GlobalTheory.Hk.CommTD

namespace GlobalTheory.Hk.CommTD

/- English proof (translation)
Rewrite `h`, the goal using `[ZMod.intCast_zmod_eq_zero_iff_dvd]`. Rewrite using `[ZMod.intCast_zmod_eq_zero_iff_dvd]`. Move the coercions through the operations in `at h`. Conclude with `⟨dvd_trans (dvd_mul_right _ _) h, dvd_trans (dvd_mul_left _ _) h⟩`.
-/
theorem zmod_of_mul {N l : ℕ} {x : ℤ} (h : ((x : ℤ) : ZMod (N * l)) = 0) :
    ((x : ℤ) : ZMod N) = 0 ∧ ((x : ℤ) : ZMod l) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h ⊢
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast at h
  exact ⟨dvd_trans (dvd_mul_right _ _) h, dvd_trans (dvd_mul_left _ _) h⟩

/- English proof (translation)
Take `⟨hN, hl⟩` from `zmod_of_mul h10`. Use `⟨(Gamma1_mem N γ).2 ⟨h00, ?_, hN⟩, Gamma0_mem.2 hl⟩` and prove the remaining obligations. Establish `dγ` using `congrArg (Int.cast : ℤ → ZMod N) γ.det_coe`. Rewrite `dγ` using `[Matrix.det_fin_two]`. Move the coercions through the operations in `at dγ`.

Rewrite `dγ` using `[h00, hN]`. Take the linear combination `dγ`.
-/
theorem mem_lev {N l : ℕ} (γ : SL(2, ℤ)) (h10 : ((γ 1 0 : ℤ) : ZMod (N * l)) = 0)
    (h00 : ((γ 0 0 : ℤ) : ZMod N) = 1) : γ ∈ lev N l := by
  obtain ⟨hN, hl⟩ := zmod_of_mul h10
  refine ⟨(Gamma1_mem N γ).2 ⟨h00, ?_, hN⟩, Gamma0_mem.2 hl⟩
  have dγ := congrArg (Int.cast : ℤ → ZMod N) γ.det_coe
  rw [Matrix.det_fin_two] at dγ
  push_cast at dγ
  rw [h00, hN] at dγ
  linear_combination dγ

/- English proof (translation)
Establish `hb'` using `(zmod_of_mul hb).1`. Simplify using `only [Matrix.mul_apply, Fin.sum_univ_two]`. Use `push_cast`. Rewrite using `[ha, hb, hb']`. Apply the tactic sequence `constructor <;> ring`.
-/
theorem mul_cong {N l : ℕ} (a b : Matrix (Fin 2) (Fin 2) ℤ) (ha : ((a 1 0 : ℤ) : ZMod (N * l)) = 0)
    (hb : ((b 1 0 : ℤ) : ZMod (N * l)) = 0) :
    (((a * b) 1 0 : ℤ) : ZMod (N * l)) = 0 ∧
      (((a * b) 0 0 : ℤ) : ZMod N) = ((a 0 0 : ℤ) : ZMod N) * ((b 0 0 : ℤ) : ZMod N) := by
  have hb' := (zmod_of_mul hb).1
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  rw [ha, hb, hb']
  constructor <;> ring

/- English proof (translation)
Take `⟨e00, e01, e10, e11⟩` from `rep_none_entries q w`. Break down `x with _ | u` into its components or cases. Rewrite using `[e00, e10]`. Establish `h1` using `hw.2`. Establish `h0` using `(zmod_of_mul hw.1).1`.

Establish `dw` using `congrArg (Int.cast : ℤ → ZMod N) w.det_coe`. Rewrite `dw` using `[Matrix.det_fin_two]`. Move the coercions through the operations in `at dw h1 ⊢`. Use `⟨by rw [hw.1, mul_zero], ?_⟩` and prove the remaining obligations. Rewrite `dw` using `[h0, h1]`.

Take the linear combination `dw`. Simplify using `[rep, tri]`.
-/
theorem rep_cong {N l q : ℕ} {w : SL(2, ℤ)} (hw : IsDia N l q w) (x : Option (Fin q)) :
    ((rep q w x 1 0 : ℤ) : ZMod (N * l)) = 0 ∧ ((rep q w x 0 0 : ℤ) : ZMod N) = 1 := by
  obtain ⟨e00, e01, e10, e11⟩ := rep_none_entries q w
  rcases x with _ | u
  · rw [e00, e10]
    have h1 := hw.2
    have h0 := (zmod_of_mul hw.1).1
    have dw := congrArg (Int.cast : ℤ → ZMod N) w.det_coe
    rw [Matrix.det_fin_two] at dw
    push_cast at dw h1 ⊢
    refine ⟨by rw [hw.1, mul_zero], ?_⟩
    rw [h0, h1] at dw
    linear_combination dw
  · simp [rep, tri]

/- English proof (translation)
Establish `hi : (((ρ⁻¹).1 1 0 : ℤ) : ZMod (N * l)) = 0`. Rewrite using `[Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]`. Simplify using `[hρ]`. Take `⟨a1, a2⟩` from `mul_cong ρ.1 m hρ h10`. Take `⟨b1, b2⟩` from `mul_cong (ρ.1 * m) (ρ⁻¹).1 a1 hi`.

Use `⟨b1, ?_⟩` and prove the remaining obligations. Rewrite using `[b2, a2, h00]`. Establish `e` using `congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) (congrArg Subtype.val (mul_inv_cancel ρ))`. Establish `e'` using `(mul_cong ρ.1 (ρ⁻¹).1 hρ hi).2`. Simplify using `only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at e`.

Rewrite using `[mul_one, ← e', e, Matrix.one_apply_eq, Int.cast_one]`.
-/
theorem conj_cong {N l : ℕ} (ρ : SL(2, ℤ)) (hρ : ((ρ 1 0 : ℤ) : ZMod (N * l)) = 0)
    (m : Matrix (Fin 2) (Fin 2) ℤ) (h10 : ((m 1 0 : ℤ) : ZMod (N * l)) = 0)
    (h00 : ((m 0 0 : ℤ) : ZMod N) = 1) :
    (((ρ.1 * m * (ρ⁻¹).1) 1 0 : ℤ) : ZMod (N * l)) = 0 ∧
      (((ρ.1 * m * (ρ⁻¹).1) 0 0 : ℤ) : ZMod N) = 1 := by
  have hi : (((ρ⁻¹).1 1 0 : ℤ) : ZMod (N * l)) = 0 := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [hρ]
  obtain ⟨a1, a2⟩ := mul_cong ρ.1 m hρ h10
  obtain ⟨b1, b2⟩ := mul_cong (ρ.1 * m) (ρ⁻¹).1 a1 hi
  refine ⟨b1, ?_⟩
  rw [b2, a2, h00]
  have e := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) (congrArg Subtype.val (mul_inv_cancel ρ))
  have e' := (mul_cong ρ.1 (ρ⁻¹).1 hρ hi).2
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at e
  rw [mul_one, ← e', e, Matrix.one_apply_eq, Int.cast_one]

/- English proof (translation)
Take `⟨γ, y, hm⟩` from `tri_exists hq m hdet`. Establish `g00` using `congrFun (congrFun hm 0) 0`. Establish `g10` using `congrFun (congrFun hm 1) 0`. Break down `y with _ | u` into its components or cases. Simplify using `[tri, Matrix.mul_apply, Fin.sum_univ_two] at g00 g10`.

Establish `hcop : Nat.Coprime q (N * l)` using `(Nat.Prime.coprime_iff_not_dvd hq).2 hqN`. Establish `hu : IsUnit ((q : ℕ) : ZMod (N * l))` using `(ZMod.unitOfCoprime q hcop).isUnit`. Establish `c10 : ((γ 1 0 : ℤ) : ZMod (N * l)) = 0`. Rewrite `h10` using `[g10]`. Move the coercions through the operations in `at h10`.

Conclude with `hu.mul_left_eq_zero.1 h10`. Use `⟨γ * w⁻¹, ?_, none, ?_⟩` and prove the remaining obligations. Establish `hwi : (((w⁻¹ : SL(2, ℤ)).1 1 0 : ℤ) : ZMod (N * l)) = 0`. Rewrite using `[Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]`. Simplify using `[hw.1]`.

Take `⟨a1, a2⟩` from `mul_cong γ.1 (w⁻¹).1 c10 hwi`. Use `mem_lev _ (by rw [Matrix.SpecialLinearGroup.coe_mul]; exact a1) ?_` and prove the remaining obligations. Rewrite using `[Matrix.SpecialLinearGroup.coe_mul, a2]`. Rewrite `h00` using `[g00]`. Establish `h1` using `hw.2`.

Establish `h0` using `(zmod_of_mul hw.1).1`. Rewrite using `[Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]`. Simplify using `only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one]`. Move the coercions through the operations in `at h00 h1 ⊢`. Rewrite using `[h1]`.

Take the linear combination `h00`. Rewrite using `[hm, rep, Matrix.SpecialLinearGroup.coe_mul, mul_assoc, ← mul_assoc (w⁻¹).1, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, one_mul]`. Simplify using `[tri, Matrix.mul_apply, Fin.sum_univ_two] at g00 g10`. Use `⟨γ, mem_lev γ (by rw [← g10]; exact h10) (by rw [← g00]; exact h00), some u, hm⟩` and prove the remaining obligations.
-/
theorem exists_rep {N l q : ℕ} (hq : q.Prime) (hqN : ¬ q ∣ N * l) {w : SL(2, ℤ)} (hw : IsDia N l q w)
    (m : Matrix (Fin 2) (Fin 2) ℤ) (hdet : m.det = q) (h10 : ((m 1 0 : ℤ) : ZMod (N * l)) = 0)
    (h00 : ((m 0 0 : ℤ) : ZMod N) = 1) :
    ∃ γ : SL(2, ℤ), γ ∈ lev N l ∧ ∃ y, m = γ.1 * rep q w y := by
  obtain ⟨γ, y, hm⟩ := tri_exists hq m hdet
  have g00 := congrFun (congrFun hm 0) 0
  have g10 := congrFun (congrFun hm 1) 0
  rcases y with _ | u
  · simp [tri, Matrix.mul_apply, Fin.sum_univ_two] at g00 g10
    have hcop : Nat.Coprime q (N * l) := (Nat.Prime.coprime_iff_not_dvd hq).2 hqN
    have hu : IsUnit ((q : ℕ) : ZMod (N * l)) := (ZMod.unitOfCoprime q hcop).isUnit
    have c10 : ((γ 1 0 : ℤ) : ZMod (N * l)) = 0 := by
      rw [g10] at h10; push_cast at h10
      exact hu.mul_left_eq_zero.1 h10
    refine ⟨γ * w⁻¹, ?_, none, ?_⟩
    · have hwi : (((w⁻¹ : SL(2, ℤ)).1 1 0 : ℤ) : ZMod (N * l)) = 0 := by
        rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
        simp [hw.1]
      obtain ⟨a1, a2⟩ := mul_cong γ.1 (w⁻¹).1 c10 hwi
      refine mem_lev _ (by rw [Matrix.SpecialLinearGroup.coe_mul]; exact a1) ?_
      rw [Matrix.SpecialLinearGroup.coe_mul, a2]
      rw [g00] at h00
      have h1 := hw.2
      have h0 := (zmod_of_mul hw.1).1
      rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one]
      push_cast at h00 h1 ⊢
      rw [h1]
      linear_combination h00
    · rw [hm, rep, Matrix.SpecialLinearGroup.coe_mul, mul_assoc, ← mul_assoc (w⁻¹).1,
        ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, one_mul]
  · simp [tri, Matrix.mul_apply, Fin.sum_univ_two] at g00 g10
    refine ⟨γ, mem_lev γ (by rw [← g10]; exact h10) (by rw [← g00]; exact h00), some u, hm⟩

/- English proof (translation)
Establish `ei : (ρ⁻¹ : SL(2, ℤ)).1 * ρ.1 = 1` using `congrArg Subtype.val (inv_mul_cancel ρ)`. Establish `ex : ∀ x, ∃ γ : SL(2, ℤ), γ ∈ lev N l ∧ ∃ y, ρ.1 * rep q w x = γ.1 * rep q w y * ρ.1`. Introduce `x`. Take `⟨c1, c2⟩` from `rep_cong hw x`. Take `⟨d1, d2⟩` from `conj_cong ρ hρ _ c1 c2`.

Take `⟨γ, hγ, y, hy⟩` from `exists_rep hq hqN hw _ (by rw [Matrix.det_mul, Matrix.det_mul, rep_det, ρ.det_coe, (ρ⁻¹).det_coe]; ring) d1 d2`. Use `⟨γ, hγ, y, ?_⟩` and prove the remaining obligations. Rewrite using `[← hy, mul_assoc _ (ρ⁻¹).1, ei, mul_one]`. Use `choose δ hδ s h using ex`. Use `⟨s, δ, Finite.injective_iff_bijective.1 fun x y e => ?_, fun x => ⟨hδ x, h x⟩⟩` and prove the remaining obligations.

Use `rep_inj hq w (ρ⁻¹ * δ x * (δ y)⁻¹ * ρ) ?_` and prove the remaining obligations. Establish `hx` using `h x`. Establish `hy` using `h y`. Rewrite `hx` using `[e]`. Establish `e2 : ((δ y)⁻¹ : SL(2, ℤ)).1 * (δ y).1 = 1` using `congrArg Subtype.val (inv_mul_cancel (δ y))`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hx, e2, mul_one]`. Simplify using `only [mul_assoc]`. Use `_ = (ρ⁻¹ : SL(2, ℤ)).1 * (δ x).1 * ((δ y)⁻¹ : SL(2, ℤ)).1 * ((δ y).1 * rep q w (s y) * ρ.1) := by`. Simplify using `only [mul_assoc]`.

Use `_ = _ := by rw [← hy]; simp only [Matrix.SpecialLinearGroup.coe_mul, mul_assoc]`.
-/
theorem perm {N l q : ℕ} (hq : q.Prime) (hqN : ¬ q ∣ N * l) {w : SL(2, ℤ)} (hw : IsDia N l q w)
    (ρ : SL(2, ℤ)) (hρ : ((ρ 1 0 : ℤ) : ZMod (N * l)) = 0) :
    ∃ (s : Option (Fin q) → Option (Fin q)) (δ : Option (Fin q) → SL(2, ℤ)), Function.Bijective s ∧
      ∀ x, δ x ∈ lev N l ∧ ρ.1 * rep q w x = (δ x).1 * rep q w (s x) * ρ.1 := by
  have ei : (ρ⁻¹ : SL(2, ℤ)).1 * ρ.1 = 1 := congrArg Subtype.val (inv_mul_cancel ρ)
  have ex : ∀ x, ∃ γ : SL(2, ℤ), γ ∈ lev N l ∧ ∃ y, ρ.1 * rep q w x = γ.1 * rep q w y * ρ.1 := by
    intro x
    obtain ⟨c1, c2⟩ := rep_cong hw x
    obtain ⟨d1, d2⟩ := conj_cong ρ hρ _ c1 c2
    obtain ⟨γ, hγ, y, hy⟩ := exists_rep hq hqN hw _
      (by rw [Matrix.det_mul, Matrix.det_mul, rep_det, ρ.det_coe, (ρ⁻¹).det_coe]; ring) d1 d2
    refine ⟨γ, hγ, y, ?_⟩
    rw [← hy, mul_assoc _ (ρ⁻¹).1, ei, mul_one]
  choose δ hδ s h using ex
  refine ⟨s, δ, Finite.injective_iff_bijective.1 fun x y e => ?_, fun x => ⟨hδ x, h x⟩⟩
  refine rep_inj hq w (ρ⁻¹ * δ x * (δ y)⁻¹ * ρ) ?_
  have hx := h x
  have hy := h y
  rw [e] at hx
  have e2 : ((δ y)⁻¹ : SL(2, ℤ)).1 * (δ y).1 = 1 := congrArg Subtype.val (inv_mul_cancel (δ y))
  calc rep q w x = (ρ⁻¹ : SL(2, ℤ)).1 * (ρ.1 * rep q w x) := by rw [← mul_assoc, ei, one_mul]
    _ = (ρ⁻¹ : SL(2, ℤ)).1 * (δ x).1 * (((δ y)⁻¹ : SL(2, ℤ)).1 * (δ y).1) * rep q w (s y) * ρ.1 := by
      rw [hx, e2, mul_one]; simp only [mul_assoc]
    _ = (ρ⁻¹ : SL(2, ℤ)).1 * (δ x).1 * ((δ y)⁻¹ : SL(2, ℤ)).1 * ((δ y).1 * rep q w (s y) * ρ.1) := by
      simp only [mul_assoc]
    _ = _ := by rw [← hy]; simp only [Matrix.SpecialLinearGroup.coe_mul, mul_assoc]

end GlobalTheory.Hk.CommTD

namespace GlobalTheory.Hk.CommTD

def repG {q : ℕ} (hq : 0 < q) (w : SL(2, ℤ)) (x : Option (Fin q)) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((Int.castRingHom ℝ).mapMatrix (rep q w x)) (by
    rw [← RingHom.map_det, rep_det]; simpa using hq.ne')

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem repG_val {q : ℕ} (hq : 0 < q) (w : SL(2, ℤ)) (x : Option (Fin q)) :
    (repG hq w x).1 = (Int.castRingHom ℝ).mapMatrix (rep q w x) := rfl

/- English proof (translation)
Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, repG_val, ← RingHom.map_det, rep_det]`. Simplify using the standard rewrite rules.
-/
theorem repG_det {q : ℕ} (hq : 0 < q) (w : SL(2, ℤ)) (x : Option (Fin q)) :
    (repG hq w x).det.val = q := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, repG_val, ← RingHom.map_det, rep_det]; simp

def diagG {q : ℕ} (hq : 0 < q) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(q : ℝ), 0; 0, 1] (by
    simp [Matrix.det_fin_two_of]; exact hq.ne')

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[repG_val, rep, map_mul]`. Use `congr 1`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [tri, diagG]`.
-/
theorem repG_none {q : ℕ} (hq : 0 < q) (w : SL(2, ℤ)) :
    repG hq w none = Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) w) * diagG hq := by
  apply Units.ext
  rw [repG_val, rep, map_mul]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tri, diagG]

/- English proof (translation)
Establish `hpos : 0 < (diagG hq).det.val`. Simplify using `[diagG, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two_of]`. Conclude with `hq`. Use function extensionality and compare the values at `z`. Rewrite using `[slash_apply, UpperHalfPlane.σ, if_pos hpos, ← ofComplex_apply (diagG hq • z), coe_smul_of_det_pos hpos]`.

Simplify using `[num, denom, diagG, vOp, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two_of]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem slash_diag {q : ℕ} (hq : 0 < q) (k : ℤ) (g : ℍ → ℂ) :
    g ∣[k] diagG hq = ((q : ℂ) ^ (k - 1)) • vOp q g := by
  have hpos : 0 < (diagG hq).det.val := by
    simp [diagG, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two_of]; exact hq
  funext z
  rw [slash_apply, UpperHalfPlane.σ, if_pos hpos, ← ofComplex_apply (diagG hq • z), coe_smul_of_det_pos hpos]
  simp [num, denom, diagG, vOp, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two_of]
  ring

/- English proof (translation)
Establish `hq0 : (q : ℂ) ≠ 0` using `by exact_mod_cast hq.ne'`. Establish `hpos : 0 < (repG hq w (some u)).det.val` using `by rw [repG_det]; exact_mod_cast hq`. Rewrite using `[slash_apply, UpperHalfPlane.σ, if_pos hpos, repG_det, ← ofComplex_apply (repG hq w (some u) • z), coe_smul_of_det_pos hpos]`. Simplify using `[num, denom, repG_val, rep, tri, zpow_sub₀ hq0]`. Clear the denominators using the available nonvanishing facts.
-/
theorem slash_tri {q : ℕ} (hq : 0 < q) (k : ℤ) (w : SL(2, ℤ)) (g : ℍ → ℂ) (u : Fin q) (z : ℍ) :
    (g ∣[k] repG hq w (some u)) z = (q : ℂ)⁻¹ * g (ofComplex (((z : ℂ) + (u : ℕ)) / q)) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hpos : 0 < (repG hq w (some u)).det.val := by rw [repG_det]; exact_mod_cast hq
  rw [slash_apply, UpperHalfPlane.σ, if_pos hpos, repG_det, ← ofComplex_apply (repG hq w (some u) • z),
    coe_smul_of_det_pos hpos]
  simp [num, denom, repG_val, rep, tri, zpow_sub₀ hq0]
  field_simp

/- English proof (translation)
Rewrite using `[Fintype.sum_option, heckeT, repG_none, SlashAction.slash_mul, ← SL_slash, slash_diag, add_comm]`. Use `congr 1`. Use function extensionality and compare the values at `z`. Rewrite using `[Finset.sum_apply]`. Simplify using `only [slash_tri]`.

Rewrite using `[uOp, ← Finset.mul_sum, ← Fin.sum_univ_eq_sum_range (fun b : ℕ => g (ofComplex (((z : ℂ) + b) / q)))]`.
-/
theorem heckeT_eq {q : ℕ} (hq : 0 < q) (k : ℤ) (w : SL(2, ℤ)) (g : ℍ → ℂ) :
    heckeT k q w g = ∑ x : Option (Fin q), g ∣[k] repG hq w x := by
  rw [Fintype.sum_option, heckeT, repG_none, SlashAction.slash_mul, ← SL_slash, slash_diag, add_comm]
  congr 1
  funext z
  rw [Finset.sum_apply]
  simp only [slash_tri]
  rw [uOp, ← Finset.mul_sum, ← Fin.sum_univ_eq_sum_range (fun b : ℕ => g (ofComplex (((z : ℂ) + b) / q)))]

end GlobalTheory.Hk.CommTD

namespace GlobalTheory.Hk.CommTD

/- English proof (translation)
Rewrite using `[SL_slash, SL_slash, SL_slash, ← SlashAction.slash_mul, ← SlashAction.slash_mul, ← SlashAction.slash_mul]`. Use `congr 1`. Apply `Units.ext` to reduce the goal to its premises. Use `congrArg (Int.castRingHom ℝ).mapMatrix h` as an intermediate fact. Rewrite `this` using `[map_mul, map_mul, map_mul, mul_assoc]`.

Simplify using `only [Units.val_mul]`. Conclude with `this`.
-/
theorem slash_conj {q : ℕ} (hq : 0 < q) (k : ℤ) (w ρ δ : SL(2, ℤ)) (g : ℍ → ℂ) {x y : Option (Fin q)}
    (h : ρ.1 * rep q w x = δ.1 * rep q w y * ρ.1) :
    (g ∣[k] ρ) ∣[k] repG hq w x = ((g ∣[k] δ) ∣[k] repG hq w y) ∣[k] ρ := by
  rw [SL_slash, SL_slash, SL_slash, ← SlashAction.slash_mul, ← SlashAction.slash_mul, ← SlashAction.slash_mul]
  congr 1
  apply Units.ext
  have := congrArg (Int.castRingHom ℝ).mapMatrix h
  rw [map_mul, map_mul, map_mul, mul_assoc] at this
  simp only [Units.val_mul]
  exact this

end GlobalTheory.Hk.CommTD

/- English proof (translation)
Introduce `N l q k d σ ρ _ hq hqN hσ hρ f`. Take `⟨s, δ, hs, h⟩` from `GlobalTheory.Hk.CommTD.perm hq hqN hσ ρ hρ.1`. Rewrite using `[GlobalTheory.Hk.CommTD.heckeT_eq hq.pos, GlobalTheory.Hk.CommTD.heckeT_eq hq.pos, GlobalTheory.Hk.dia, GlobalTheory.Hk.dia, SlashAction.sum_slash, ← hs.sum_comp (fun y => (⇑f ∣[k] GlobalTheory.Hk.CommTD.repG hq.pos σ y) ∣[k] ρ)]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Establish `hinv : (⇑f) ∣[k] (δ x) = ⇑f`.

Rewrite using `[SL_slash]`. Conclude with `SlashInvariantFormClass.slash_action_eq f _ ⟨δ x, (h x).1, rfl⟩`. Rewrite using `[GlobalTheory.Hk.CommTD.slash_conj hq.pos k σ ρ (δ x) ⇑f (h x).2, hinv]`.
-/
theorem GlobalTheory.Hk.heckeT_dia_comm : ∀ (N l q : ℕ) (k d : ℤ) (σ ρ : SL(2, ℤ)), 0 < N → q.Prime → ¬ q ∣ N * l →
    GlobalTheory.Hk.IsDia N l q σ → GlobalTheory.Hk.IsDia N l d ρ → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k,
    GlobalTheory.Hk.heckeT k q σ (GlobalTheory.Hk.dia k ρ ⇑f) = GlobalTheory.Hk.dia k ρ (GlobalTheory.Hk.heckeT k q σ ⇑f) := by
  intro N l q k d σ ρ _ hq hqN hσ hρ f
  obtain ⟨s, δ, hs, h⟩ := GlobalTheory.Hk.CommTD.perm hq hqN hσ ρ hρ.1
  rw [GlobalTheory.Hk.CommTD.heckeT_eq hq.pos, GlobalTheory.Hk.CommTD.heckeT_eq hq.pos, GlobalTheory.Hk.dia, GlobalTheory.Hk.dia,
    SlashAction.sum_slash, ← hs.sum_comp (fun y => (⇑f ∣[k] GlobalTheory.Hk.CommTD.repG hq.pos σ y) ∣[k] ρ)]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hinv : (⇑f) ∣[k] (δ x) = ⇑f := by
    rw [SL_slash]
    exact SlashInvariantFormClass.slash_action_eq f _ ⟨δ x, (h x).1, rfl⟩
  rw [GlobalTheory.Hk.CommTD.slash_conj hq.pos k σ ρ (δ x) ⇑f (h x).2, hinv]
