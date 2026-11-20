import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashToGLSmul
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.TrOld

def rep (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) : Option (Fin l) → SL(2, ℤ)
  | none => 1
  | some j => gaOld N l a b h j

def sig (l : ℕ) [NeZero l] (x : SL(2, ℤ)) : Option (Fin l) :=
  if (l : ℤ) ∣ mat x 1 0 then none
  else some ⟨(((mat x 1 1 : ℤ) : ZMod l) * ((mat x 1 0 : ℤ) : ZMod l)⁻¹).val, ZMod.val_lt _⟩

/- English proof (translation)
Simplify using `only [mat, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]`.
-/
lemma mul_11 (x y : SL(2, ℤ)) : mat (x * y) 1 1 = mat x 1 0 * mat y 0 1 + mat x 1 1 * mat y 1 1 := by
  simp only [mat, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

/- English proof (translation)
Simplify using `[mat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma mulInv_10 (x y : SL(2, ℤ)) : mat (x * y⁻¹) 1 0 = mat x 1 0 * mat y 1 1 - mat x 1 1 * mat y 1 0 := by
  simp [mat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  ring

/- English proof (translation)
Simplify using `[mat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]`.
-/
lemma mulInv_11 (x y : SL(2, ℤ)) : mat (x * y⁻¹) 1 1 = -(mat x 1 0 * mat y 0 1) + mat x 1 1 * mat y 0 0 := by
  simp [mat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

/- English proof (translation)
Rewrite using `[Gamma0_mem]`. Conclude with `ZMod.intCast_zmod_eq_zero_iff_dvd _ _`.
-/
lemma mem_iff (M : ℕ) (x : SL(2, ℤ)) : x ∈ Gamma0 M ↔ (M : ℤ) ∣ mat x 1 0 := by
  rw [Gamma0_mem]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd _ _

section
variable {N l : ℕ} {a b : ℤ} {h : (l : ℤ) * b - N * a = 1}

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma rep_none_10 : mat (rep N l a b h none) 1 0 = 0 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma rep_none_11 : mat (rep N l a b h none) 1 1 = 1 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma rep_some_10 (j : Fin l) : mat (rep N l a b h (some j)) 1 0 = N := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma rep_some_11 (j : Fin l) : mat (rep N l a b h (some j)) 1 1 = (N : ℤ) * (j : ℕ) + l * b := rfl

/- English proof (translation)
Apply the tactic sequence `cases o <;> simp [rep, gaOld, mat]`.
-/
lemma rep_00 (o : Option (Fin l)) : mat (rep N l a b h o) 0 0 = 1 := by
  cases o <;> simp [rep, gaOld, mat]

/- English proof (translation)
Consider the cases of `o with`. Consider the case `none => rw [rep_none_10]`. Simplify using the standard rewrite rules. Consider the case `some j => rw [rep_some_10]`. Simplify using the standard rewrite rules.
-/
lemma rep_10 (o : Option (Fin l)) : ((mat (rep N l a b h o) 1 0 : ℤ) : ZMod N) = 0 := by
  cases o with
  | none => rw [rep_none_10]; simp
  | some j => rw [rep_some_10]; simp

/- English proof (translation)
Consider the cases of `o with`. Consider the case `none => rw [rep_none_11]`. Simplify using the standard rewrite rules. Consider the case `some j`. Establish `hc` using `congrArg (Int.cast : ℤ → ZMod N) h`.

Move the coercions through the operations in `at hc`. Rewrite `hc` using `[ZMod.natCast_self, zero_mul, sub_zero]`. Rewrite using `[rep_some_11]`. Use `push_cast`. Rewrite using `[ZMod.natCast_self, zero_mul, zero_add, hc]`.
-/
lemma rep_11 (o : Option (Fin l)) : ((mat (rep N l a b h o) 1 1 : ℤ) : ZMod N) = 1 := by
  cases o with
  | none => rw [rep_none_11]; simp
  | some j =>
    have hc := congrArg (Int.cast : ℤ → ZMod N) h
    push_cast at hc
    rw [ZMod.natCast_self, zero_mul, sub_zero] at hc
    rw [rep_some_11]
    push_cast
    rw [ZMod.natCast_self, zero_mul, zero_add, hc]

include h in
/- English proof (translation)
Assemble the required witnesses or components as `⟨-a, b, by linear_combination h⟩`.
-/
lemma cop : IsCoprime (N : ℤ) (l : ℤ) := ⟨-a, b, by linear_combination h⟩

/- English proof (translation)
Use `Fact.mk hl` as an intermediate fact. Establish `hc : IsCoprime (N : ℤ) l` using `cop (h := h)`. Establish `hδ : ∀ o, (N : ℤ) ∣ mat (rep N l a b h o) 1 0` using `fun o => (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (rep_10 o)`. Rewrite `hx` using `[mem_iff]`. Rewrite using `[mem_iff, mulInv_10]`.

Use `push_cast`. Apply `hc.mul_dvd` to reduce the goal to its premises. Conclude with `dvd_sub (Dvd.dvd.mul_right hx _) (Dvd.dvd.mul_left (hδ _) _)`. Unfold `sig split_ifs with hd`. Rewrite using `[rep_none_10, rep_none_11]`.

Simplify using `using hd`. Rewrite using `[rep_some_10, rep_some_11, ← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Establish `hc0 : ((mat x 1 0 : ℤ) : ZMod l) ≠ 0`. Rewrite using `[Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]` and apply the resulting hypothesis. Establish `hu` using `mul_inv_cancel₀ hc0`.

Establish `hl0 : ((l : ℕ) : ZMod l) = 0` using `ZMod.natCast_self l`. Use `push_cast`. Simplify using `only [ZMod.natCast_zmod_val]`. Take the linear combination `((N : ZMod l) * ((mat x 1 1 : ℤ) : ZMod l)) * hu + (((mat x 1 0 : ℤ) : ZMod l) * (b : ZMod l)) * hl0`.
-/
lemma sig_mem [NeZero l] (hl : l.Prime) (x : SL(2, ℤ)) (hx : x ∈ Gamma0 N) :
    x * (rep N l a b h (sig l x))⁻¹ ∈ Gamma0 (N * l) := by
  have := Fact.mk hl
  have hc : IsCoprime (N : ℤ) l := cop (h := h)
  have hδ : ∀ o, (N : ℤ) ∣ mat (rep N l a b h o) 1 0 := fun o =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (rep_10 o)
  rw [mem_iff] at hx
  rw [mem_iff, mulInv_10]
  push_cast
  apply hc.mul_dvd
  · exact dvd_sub (Dvd.dvd.mul_right hx _) (Dvd.dvd.mul_left (hδ _) _)
  · unfold sig
    split_ifs with hd
    · rw [rep_none_10, rep_none_11]
      simpa using hd
    · rw [rep_some_10, rep_some_11, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      have hc0 : ((mat x 1 0 : ℤ) : ZMod l) ≠ 0 := by
        rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      have hu := mul_inv_cancel₀ hc0
      have hl0 : ((l : ℕ) : ZMod l) = 0 := ZMod.natCast_self l
      push_cast
      simp only [ZMod.natCast_zmod_val]
      linear_combination ((N : ZMod l) * ((mat x 1 1 : ℤ) : ZMod l)) * hu +
        (((mat x 1 0 : ℤ) : ZMod l) * (b : ZMod l)) * hl0

/- English proof (translation)
Introduce `hd`. Establish `h1` using `Int.le_of_dvd (by exact_mod_cast hN) hd`. Establish `h2 : (2 : ℤ) ≤ l` using `by exact_mod_cast hl.two_le`. Establish `h3 : (0 : ℤ) < N` using `by exact_mod_cast hN`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma not_dvd (hN : 0 < N) (hl : l.Prime) : ¬ ((N : ℤ) * l ∣ N) := by
  intro hd
  have h1 := Int.le_of_dvd (by exact_mod_cast hN) hd
  have h2 : (2 : ℤ) ≤ l := by exact_mod_cast hl.two_le
  have h3 : (0 : ℤ) < N := by exact_mod_cast hN
  nlinarith

/- English proof (translation)
Establish `hc : IsCoprime (N : ℤ) l` using `cop (h := h)`. Establish `hN' : (0 : ℤ) < N` using `by exact_mod_cast hN`. Rewrite `hm` using `[mem_iff, mulInv_10]`. Move the coercions through the operations in `at hm`. Apply the tactic sequence `rcases o₁ with _ | i <;> rcases o₂ with _ | j`.

Both sides reduce to the same expression. It suffices to derive a contradiction. Rewrite `hm` using `[rep_none_10, rep_none_11, rep_some_10]`. Conclude with `not_dvd hN hl (by simpa using hm)`. It suffices to derive a contradiction.

Rewrite `hm` using `[rep_some_10, rep_none_11, rep_none_10]`. Conclude with `not_dvd hN hl (by simpa using hm)`. Rewrite `hm` using `[rep_some_10, rep_some_11, rep_some_10, rep_some_11]`. Establish `e : (N : ℤ) * (N * (j : ℕ) + l * b) - (N * (i : ℕ) + l * b) * N = N * (N * (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)))` using `by ring`. Rewrite `hm` using `[e]`.

Establish `h1 : (l : ℤ) ∣ N * (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ))` using `(mul_dvd_mul_iff_left hN'.ne').1 hm`. Establish `h2 : (l : ℤ) ∣ ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)` using `hc.symm.dvd_of_dvd_mul_left h1`. Establish `h3 : ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) = 0`. Apply `Int.eq_zero_of_abs_lt_dvd h2` to reduce the goal to its premises. Use `i.isLt` as an intermediate fact.

Use `j.isLt` as an intermediate fact. Rewrite using `[abs_lt]`. Apply the tactic sequence `constructor <;> omega`. Use `congr 1`. Use `ext`.

Use linear arithmetic over natural numbers and integers.
-/
lemma rep_inj (hN : 0 < N) (hl : l.Prime) (o₁ o₂ : Option (Fin l))
    (hm : rep N l a b h o₁ * (rep N l a b h o₂)⁻¹ ∈ Gamma0 (N * l)) : o₁ = o₂ := by
  have hc : IsCoprime (N : ℤ) l := cop (h := h)
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  rw [mem_iff, mulInv_10] at hm
  push_cast at hm
  rcases o₁ with _ | i <;> rcases o₂ with _ | j
  · rfl
  · exfalso
    rw [rep_none_10, rep_none_11, rep_some_10] at hm
    exact not_dvd hN hl (by simpa using hm)
  · exfalso
    rw [rep_some_10, rep_none_11, rep_none_10] at hm
    exact not_dvd hN hl (by simpa using hm)
  · rw [rep_some_10, rep_some_11, rep_some_10, rep_some_11] at hm
    have e : (N : ℤ) * (N * (j : ℕ) + l * b) - (N * (i : ℕ) + l * b) * N =
        N * (N * (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ))) := by ring
    rw [e] at hm
    have h1 : (l : ℤ) ∣ N * (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) := (mul_dvd_mul_iff_left hN'.ne').1 hm
    have h2 : (l : ℤ) ∣ ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) := hc.symm.dvd_of_dvd_mul_left h1
    have h3 : ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd h2
      have := i.isLt
      have := j.isLt
      rw [abs_lt]
      constructor <;> omega
    congr 1
    ext
    omega

end

end GlobalTheory.HeckeFamilyMatrices.TrOld

open GlobalTheory.HeckeFamilyMatrices.TrOld in

/- English proof (translation)
Introduce `N l k a b h χ G hN hl hG γ hγ`. Establish `: NeZero l` using `⟨hl.ne_zero⟩`. Establish `rep_mem : ∀ o, rep N l a b h o ∈ Gamma0 N` using `fun o => Gamma0_mem.2 (rep_10 o)`. Establish `hsum : trOld k N l a b h G = ∑ o : Option (Fin l), G ∣[k] rep N l a b h o`. Rewrite using `[Fintype.sum_option]`.

Simplify using `only [rep, SlashAction.slash_one]`. Unfold `trOld`. Use `congr 1`. Conclude with `(Fin.sum_univ_eq_sum_range (fun j => G ∣[k] gaOld N l a b h j) l).symm`. Establish `hterm : ∀ o, (G ∣[k] rep N l a b h o) ∣[k] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • (G ∣[k] rep N l a b h (sig l (rep N l a b h o * γ)))`.

Introduce `o`. Establish `hA : rep N l a b h o * γ ∈ Gamma0 N` using `mul_mem (rep_mem o) hγ`. Establish `hη` using `sig_mem (h := h) hl _ hA`. Establish `hA0 : ((mat (rep N l a b h o * γ) 1 0 : ℤ) : ZMod N) = 0` using `Gamma0_mem.1 hA`. Establish `hchar : ((mat (rep N l a b h o * γ * (rep N l a b h (sig l (rep N l a b h o * γ)))⁻¹) 1 1 : ℤ) : ZMod N) = ((mat γ 1 1 : ℤ) : ZMod N)`.

Rewrite using `[mulInv_11, rep_00]`. Use `push_cast`. Rewrite using `[hA0, mul_11]`. Use `push_cast`. Rewrite using `[rep_10, rep_11]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e : G ∣[k] (rep N l a b h o * γ) = (G ∣[k] (rep N l a b h o * γ * (rep N l a b h (sig l (rep N l a b h o * γ)))⁻¹)) ∣[k] rep N l a b h (sig l (rep N l a b h o * γ))`. Rewrite using `[← SlashAction.slash_mul, inv_mul_cancel_right]`. Rewrite using `[← SlashAction.slash_mul, e, hG _ hη, ModularForm.SL_smul_slash, hchar]`. Establish `hinj : Function.Injective (fun o => sig l (rep N l a b h o * γ))`.

Introduce `o₁ o₂ he`. Apply `rep_inj (h := h) hN hl` to reduce the goal to its premises. Establish `h1` using `sig_mem (h := h) hl _ (mul_mem (rep_mem o₁) hγ)`. Establish `h2` using `sig_mem (h := h) hl _ (mul_mem (rep_mem o₂) hγ)`. Simplify using `only at he`.

Rewrite `h1` using `[he]`. Establish `h3` using `mul_mem h1 (inv_mem h2)`. Use `h3 using 1` and compare the differences between its conclusion and the goal. Use `group`. Rewrite using `[hsum, SlashAction.sum_slash, Finset.sum_congr rfl (fun o _ => hterm o), ← Finset.smul_sum]`.

Use `congr 1`. Conclude with `(Finite.injective_iff_bijective.mp hinj).sum_comp (fun o => G ∣[k] rep N l a b h o)`.
-/
theorem GlobalTheory.HeckeFamilyMatrices.chiInv_trOld : ∀ (N l : ℕ) (k : ℤ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1)
    (χ : DirichletCharacter ℂ N) (G : ℍ → ℂ), 0 < N → l.Prime → ChiInv k N (N * l) χ G →
    ChiInv k N N χ (trOld k N l a b h G) := by
  intro N l k a b h χ G hN hl hG γ hγ
  have : NeZero l := ⟨hl.ne_zero⟩
  have rep_mem : ∀ o, rep N l a b h o ∈ Gamma0 N := fun o => Gamma0_mem.2 (rep_10 o)
  have hsum : trOld k N l a b h G = ∑ o : Option (Fin l), G ∣[k] rep N l a b h o := by
    rw [Fintype.sum_option]
    simp only [rep, SlashAction.slash_one]
    unfold trOld
    congr 1
    exact (Fin.sum_univ_eq_sum_range (fun j => G ∣[k] gaOld N l a b h j) l).symm
  have hterm : ∀ o, (G ∣[k] rep N l a b h o) ∣[k] γ =
      χ ((mat γ 1 1 : ℤ) : ZMod N) • (G ∣[k] rep N l a b h (sig l (rep N l a b h o * γ))) := by
    intro o
    have hA : rep N l a b h o * γ ∈ Gamma0 N := mul_mem (rep_mem o) hγ
    have hη := sig_mem (h := h) hl _ hA
    have hA0 : ((mat (rep N l a b h o * γ) 1 0 : ℤ) : ZMod N) = 0 := Gamma0_mem.1 hA
    have hchar : ((mat (rep N l a b h o * γ * (rep N l a b h (sig l (rep N l a b h o * γ)))⁻¹) 1 1 : ℤ)
        : ZMod N) = ((mat γ 1 1 : ℤ) : ZMod N) := by
      rw [mulInv_11, rep_00]
      push_cast
      rw [hA0, mul_11]
      push_cast
      rw [rep_10, rep_11]
      ring
    have e : G ∣[k] (rep N l a b h o * γ) =
        (G ∣[k] (rep N l a b h o * γ * (rep N l a b h (sig l (rep N l a b h o * γ)))⁻¹)) ∣[k]
          rep N l a b h (sig l (rep N l a b h o * γ)) := by
      rw [← SlashAction.slash_mul, inv_mul_cancel_right]
    rw [← SlashAction.slash_mul, e, hG _ hη, ModularForm.SL_smul_slash, hchar]
  have hinj : Function.Injective (fun o => sig l (rep N l a b h o * γ)) := by
    intro o₁ o₂ he
    apply rep_inj (h := h) hN hl
    have h1 := sig_mem (h := h) hl _ (mul_mem (rep_mem o₁) hγ)
    have h2 := sig_mem (h := h) hl _ (mul_mem (rep_mem o₂) hγ)
    simp only at he
    rw [he] at h1
    have h3 := mul_mem h1 (inv_mem h2)
    convert h3 using 1
    group
  rw [hsum, SlashAction.sum_slash, Finset.sum_congr rfl (fun o _ => hterm o), ← Finset.smul_sum]
  congr 1
  exact (Finite.injective_iff_bijective.mp hinj).sum_comp (fun o => G ∣[k] rep N l a b h o)
