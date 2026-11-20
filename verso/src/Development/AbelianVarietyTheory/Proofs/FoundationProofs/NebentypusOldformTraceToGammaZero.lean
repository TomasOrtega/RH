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
Simplify using the standard rewrite rules.
-/
lemma mul_11 (x y : SL(2, ℤ)) : mat (x * y) 1 1 = mat x 1 0 * mat y 0 1 + mat x 1 1 * mat y 1 1 := by
  simp only [mat, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

/- English proof (translation)
Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
lemma mulInv_10 (x y : SL(2, ℤ)) : mat (x * y⁻¹) 1 0 = mat x 1 0 * mat y 1 1 - mat x 1 1 * mat y 1 0 := by
  simp [mat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  ring

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
lemma mulInv_11 (x y : SL(2, ℤ)) : mat (x * y⁻¹) 1 1 = -(mat x 1 0 * mat y 0 1) + mat x 1 1 * mat y 0 0 := by
  simp [mat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Apply the first step, then apply the next step to every resulting obligation.
-/
lemma rep_00 (o : Option (Fin l)) : mat (rep N l a b h o) 0 0 = 1 := by
  cases o <;> simp [rep, gaOld, mat]

/- English proof (translation)
Split into cases according to the possible forms of the given data. Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately. Simplify using the standard rewrite rules.
-/
lemma rep_10 (o : Option (Fin l)) : ((mat (rep N l a b h o) 1 0 : ℤ) : ZMod N) = 0 := by
  cases o with
  | none => rw [rep_none_10]; simp
  | some j => rw [rep_some_10]; simp

/- English proof (translation)
Split into cases according to the possible forms of the given data. Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately. Establish an intermediate fact.

Move the embeddings inside the algebraic operations. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities.
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
Supply the required witnesses or components.
-/
lemma cop : IsCoprime (N : ℤ) (l : ℤ) := ⟨-a, b, by linear_combination h⟩

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Move the embeddings inside the algebraic operations. Reduce the claim to the hypotheses of an applicable result. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Establish an intermediate fact.

Move the embeddings inside the algebraic operations. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma not_dvd (hN : 0 < N) (hl : l.Prime) : ¬ ((N : ℤ) * l ∣ N) := by
  intro hd
  have h1 := Int.le_of_dvd (by exact_mod_cast hN) hd
  have h2 : (2 : ℤ) ≤ l := by exact_mod_cast hl.two_le
  have h3 : (0 : ℤ) < N := by exact_mod_cast hN
  nlinarith

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Move the embeddings inside the algebraic operations. Apply the first step, then apply the next step to every resulting obligation.

Both sides reduce to the same expression. It suffices to derive a contradiction. Rewrite the indicated hypotheses using the stated equalities. It suffices to derive a contradiction. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Apply the first step, then apply the next step to every resulting obligation. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
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
