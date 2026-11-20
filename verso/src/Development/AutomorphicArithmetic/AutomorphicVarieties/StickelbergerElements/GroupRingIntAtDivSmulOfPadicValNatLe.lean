import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.CoefMapSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.SamePrimesMulPow

open Finset UpperTheory.V.Bern UpperTheory.V

/- English proof (translation)
Introduce `l _ M D t hM hD ht Γ _ z g`. Establish `hp : l.Prime` using `Fact.out`. Establish `hcoef : (((M : ℚ) / (D : ℚ)) • Stk.cf ℚ Γ z).coeff g = ((M : ℚ) / (D : ℚ)) * (z.coeff g : ℚ)`. Simplify using `[Stk.cf]`. Rewrite using `[hcoef]`.

Establish `hdvdM : l ^ (padicValNat l D + t) ∣ M` using `(pow_dvd_pow l (by omega)).trans pow_padicValNat_dvd`. Establish `hdvdD : l ^ padicValNat l D ∣ D` using `pow_padicValNat_dvd`. Take `⟨k, hk⟩` from `hdvdM`. Take `⟨E, hE⟩` from `hdvdD`. Establish `hnd : ¬ l ∣ E`.

Introduce `hl`. Apply `pow_succ_padicValNat_not_dvd (p := l) hD.ne'` to reduce the goal to its premises. Use `conv_rhs => rw [hE]`. Rewrite using `[pow_succ]`. Conclude with `Nat.mul_dvd_mul_left _ hl`.

Establish `hE0 : E ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hE`. Use linear arithmetic over natural numbers and integers. Establish `hl0 : (l : ℚ) ≠ 0` using `by exact_mod_cast hp.ne_zero`.

Establish `hEq : (E : ℚ) ≠ 0` using `by exact_mod_cast hE0`. Establish `hMq : (M : ℚ) = (l : ℚ) ^ (padicValNat l D + t) * k` using `by exact_mod_cast hk`. Establish `hDq : (D : ℚ) = (l : ℚ) ^ padicValNat l D * E` using `by exact_mod_cast hE`. Establish `heq : (M : ℚ) / (D : ℚ) * (z.coeff g : ℚ) / (l : ℚ) ^ t = ((k : ℚ) / (E : ℚ)) * (z.coeff g : ℚ)`. Rewrite using `[hMq, hDq, pow_add]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[heq]`. Use `(B4.Zl l).mul_mem ?_ (intCast_mem _ _)` and prove the remaining obligations. Rewrite using `[B4.mem_Zl]`. Introduce `hden`.

Apply `hnd` to reduce the goal to its premises. Establish `h1 : (((k : ℤ) : ℚ) / ((E : ℤ) : ℚ)).den ∣ E`. Rewrite using `[← Rat.divInt_eq_div]`. Conclude with `Rat.den_dvd (k : ℤ) (E : ℤ)` after adjusting the coercions. Move the coercions through the operations in `at h1`.

Conclude with `hden.trans h1`.
-/
theorem UpperTheory.V.Stk.groupRing_intAt_div_smul_of_padicValNat_le :
    ∀ (l : ℕ) [Fact l.Prime] (M D t : ℕ), 0 < M → 0 < D → t + padicValNat l D ≤ padicValNat l M →
      ∀ (Γ : Type) [CommGroup Γ] (z : MonoidAlgebra ℤ Γ), B4.IntAt l t (((M : ℚ) / (D : ℚ)) • Stk.cf ℚ Γ z) := by
  intro l _ M D t hM hD ht Γ _ z g
  have hp : l.Prime := Fact.out
  have hcoef : (((M : ℚ) / (D : ℚ)) • Stk.cf ℚ Γ z).coeff g = ((M : ℚ) / (D : ℚ)) * (z.coeff g : ℚ) := by
    simp [Stk.cf]
  rw [hcoef]
  have hdvdM : l ^ (padicValNat l D + t) ∣ M :=
    (pow_dvd_pow l (by omega)).trans pow_padicValNat_dvd
  have hdvdD : l ^ padicValNat l D ∣ D := pow_padicValNat_dvd
  obtain ⟨k, hk⟩ := hdvdM
  obtain ⟨E, hE⟩ := hdvdD
  have hnd : ¬ l ∣ E := by
    intro hl
    apply pow_succ_padicValNat_not_dvd (p := l) hD.ne'
    conv_rhs => rw [hE]
    rw [pow_succ]
    exact Nat.mul_dvd_mul_left _ hl
  have hE0 : E ≠ 0 := by
    rintro rfl
    simp at hE
    omega
  have hl0 : (l : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hEq : (E : ℚ) ≠ 0 := by exact_mod_cast hE0
  have hMq : (M : ℚ) = (l : ℚ) ^ (padicValNat l D + t) * k := by exact_mod_cast hk
  have hDq : (D : ℚ) = (l : ℚ) ^ padicValNat l D * E := by exact_mod_cast hE
  have heq : (M : ℚ) / (D : ℚ) * (z.coeff g : ℚ) / (l : ℚ) ^ t = ((k : ℚ) / (E : ℚ)) * (z.coeff g : ℚ) := by
    rw [hMq, hDq, pow_add]
    field_simp
  rw [heq]
  refine (B4.Zl l).mul_mem ?_ (intCast_mem _ _)
  rw [B4.mem_Zl]
  intro hden
  apply hnd
  have h1 : (((k : ℤ) : ℚ) / ((E : ℤ) : ℚ)).den ∣ E := by
    rw [← Rat.divInt_eq_div]
    exact_mod_cast Rat.den_dvd (k : ℤ) (E : ℤ)
  push_cast at h1
  exact hden.trans h1
