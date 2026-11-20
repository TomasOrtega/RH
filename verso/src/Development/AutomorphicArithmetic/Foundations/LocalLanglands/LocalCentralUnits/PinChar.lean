import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SumChar

open Finset ComplexConjugate

namespace UpperTheory.Zero.LLC.CharacterSumPairs

variable {G : Type} [CommGroup G] [Fintype G]

/- English proof (translation)
Establish `h : ((χ z : ℂˣ) : ℂ) ^ Fintype.card G = 1`. Rewrite using `[← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one]`. Conclude with `Complex.norm_eq_one_of_pow_eq_one h Fintype.card_ne_zero`.
-/
theorem norm_char (χ : G →* ℂˣ) (z : G) : ‖((χ z : ℂˣ) : ℂ)‖ = 1 := by
  have h : ((χ z : ℂˣ) : ℂ) ^ Fintype.card G = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one h Fintype.card_ne_zero

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qe46.sum_char χ h`.
-/
theorem sum_char (χ : G →* ℂˣ) (h : χ ≠ 1) : ∑ z, ((χ z : ℂˣ) : ℂ) = 0 :=
  _root_.UpperTheory.Reformulated.B.Qe46.sum_char χ h

/- English proof (translation)
Rewrite using `[MonoidHom.inv_apply, Units.val_inv_eq_inv_val, Complex.inv_eq_conj (norm_char χ z)]`.
-/
theorem conj_char (χ : G →* ℂˣ) (z : G) : conj ((χ z : ℂˣ) : ℂ) = (((χ⁻¹) z : ℂˣ) : ℂ) := by
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, Complex.inv_eq_conj (norm_char χ z)]

open Classical in
/- English proof (translation)
Establish `: ∀ z, ((χ z : ℂˣ) : ℂ) * conj ((ψ z : ℂˣ) : ℂ) = (((χ * ψ⁻¹) z : ℂˣ) : ℂ)`. Introduce `z`. Rewrite using `[conj_char, MonoidHom.mul_apply, Units.val_mul]`. Repeatedly rewrite using `[this]`. Use `split_ifs with h`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Conclude with `sum_char _ (fun hh => h (mul_inv_eq_one.mp hh))`.
-/
theorem sum_mul_conj (χ ψ : G →* ℂˣ) :
    ∑ z, ((χ z : ℂˣ) : ℂ) * conj ((ψ z : ℂˣ) : ℂ) = if χ = ψ then (Fintype.card G : ℂ) else 0 := by
  have : ∀ z, ((χ z : ℂˣ) : ℂ) * conj ((ψ z : ℂˣ) : ℂ) = (((χ * ψ⁻¹) z : ℂˣ) : ℂ) := by
    intro z
    rw [conj_char, MonoidHom.mul_apply, Units.val_mul]
  simp_rw [this]
  split_ifs with h
  · subst h
    simp
  · exact sum_char _ (fun hh => h (mul_inv_eq_one.mp hh))

noncomputable def dif (A B : Finset (G →* ℂˣ)) (z : G) : ℂ :=
  ∑ χ ∈ A, ((χ z : ℂˣ) : ℂ) - ∑ χ ∈ B, ((χ z : ℂˣ) : ℂ)

open Classical in
/- English proof (translation)
Establish `key : ∀ C : Finset (G →* ℂˣ), ∑ z, (∑ χ ∈ C, ((χ z : ℂˣ) : ℂ)) * conj ((ψ z : ℂˣ) : ℂ) = (Fintype.card G : ℂ) * (if ψ ∈ C then 1 else 0)`. Introduce `C`. Repeatedly rewrite using `[Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Repeatedly rewrite using `[sum_mul_conj]`.

Rewrite using `[Finset.sum_ite_eq' C ψ]`. Apply the tactic sequence `split_ifs <;> simp`. Simplify using `only [dif, sub_mul, Finset.sum_sub_distrib, key]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem inner_dif (A B : Finset (G →* ℂˣ)) (ψ : G →* ℂˣ) :
    ∑ z, dif A B z * conj ((ψ z : ℂˣ) : ℂ) =
      (Fintype.card G : ℂ) * ((if ψ ∈ A then 1 else 0) - (if ψ ∈ B then 1 else 0)) := by
  have key : ∀ C : Finset (G →* ℂˣ),
      ∑ z, (∑ χ ∈ C, ((χ z : ℂˣ) : ℂ)) * conj ((ψ z : ℂˣ) : ℂ) =
        (Fintype.card G : ℂ) * (if ψ ∈ C then 1 else 0) := by
    intro C
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [sum_mul_conj]
    rw [Finset.sum_ite_eq' C ψ]
    split_ifs <;> simp
  simp only [dif, sub_mul, Finset.sum_sub_distrib, key]
  ring

/- English proof (translation)
Establish `hc : ∀ z, conj (dif A B z) = ∑ χ ∈ A, conj ((χ z : ℂˣ) : ℂ) - ∑ χ ∈ B, conj ((χ z : ℂˣ) : ℂ)`. Introduce `z`. Simplify using `[dif, map_sub, map_sum]`. Repeatedly rewrite using `[hc, mul_sub, Finset.mul_sum]`. Rewrite using `[Finset.sum_sub_distrib, Finset.sum_comm]`.

Rewrite using `[Finset.sum_comm (s := Finset.univ) (t := B)]`. Repeatedly rewrite using `[inner_dif]`. Establish `hA : ∑ ψ ∈ A, (Fintype.card G : ℂ) * ((if ψ ∈ A then 1 else 0) - (if ψ ∈ B then 1 else 0)) = (Fintype.card G : ℂ) * #A`. Rewrite using `[Finset.sum_congr rfl (g := fun _ => (Fintype.card G : ℂ))]`. Simplify using `[mul_comm]`.

Introduce `ψ hψ`. Establish `: ψ ∉ B` using `Finset.disjoint_left.mp hd hψ`. Simplify using `[hψ, this]`. Establish `hB : ∑ ψ ∈ B, (Fintype.card G : ℂ) * ((if ψ ∈ A then 1 else 0) - (if ψ ∈ B then 1 else 0)) = - ((Fintype.card G : ℂ) * #B)`. Rewrite using `[Finset.sum_congr rfl (g := fun _ => - (Fintype.card G : ℂ))]`.

Simplify using `[mul_comm]`. Introduce `ψ hψ`. Establish `: ψ ∉ A` using `Finset.disjoint_right.mp hd hψ`. Simplify using `[hψ, this]`. Rewrite using `[hA, hB]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem parseval (A B : Finset (G →* ℂˣ)) (hd : Disjoint A B) :
    ∑ z, dif A B z * conj (dif A B z) = (Fintype.card G : ℂ) * ((#A : ℂ) + #B) := by
  classical
  have hc : ∀ z, conj (dif A B z) =
      ∑ χ ∈ A, conj ((χ z : ℂˣ) : ℂ) - ∑ χ ∈ B, conj ((χ z : ℂˣ) : ℂ) := by
    intro z
    simp [dif, map_sub, map_sum]
  simp_rw [hc, mul_sub, Finset.mul_sum]
  rw [Finset.sum_sub_distrib, Finset.sum_comm]
  rw [Finset.sum_comm (s := Finset.univ) (t := B)]
  simp_rw [inner_dif]
  have hA : ∑ ψ ∈ A, (Fintype.card G : ℂ) * ((if ψ ∈ A then 1 else 0) - (if ψ ∈ B then 1 else 0))
      = (Fintype.card G : ℂ) * #A := by
    rw [Finset.sum_congr rfl (g := fun _ => (Fintype.card G : ℂ))]
    · simp [mul_comm]
    · intro ψ hψ
      have : ψ ∉ B := Finset.disjoint_left.mp hd hψ
      simp [hψ, this]
  have hB : ∑ ψ ∈ B, (Fintype.card G : ℂ) * ((if ψ ∈ A then 1 else 0) - (if ψ ∈ B then 1 else 0))
      = - ((Fintype.card G : ℂ) * #B) := by
    rw [Finset.sum_congr rfl (g := fun _ => - (Fintype.card G : ℂ))]
    · simp [mul_comm]
    · intro ψ hψ
      have : ψ ∉ A := Finset.disjoint_right.mp hd hψ
      simp [hψ, this]
  rw [hA, hB]
  ring

/- English proof (translation)
Establish `h : ∀ C : Finset (G →* ℂˣ), ‖∑ χ ∈ C, ((χ z : ℂˣ) : ℂ)‖ ≤ #C`. Introduce `C`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations. Simplify using `[norm_char]`. Conclude with `(norm_sub_le _ _).trans (add_le_add (h A) (h B))`.
-/
theorem norm_dif_le (A B : Finset (G →* ℂˣ)) (z : G) : ‖dif A B z‖ ≤ (#A : ℝ) + #B := by
  have h : ∀ C : Finset (G →* ℂˣ), ‖∑ χ ∈ C, ((χ z : ℂˣ) : ℂ)‖ ≤ #C := by
    intro C
    refine (norm_sum_le _ _).trans ?_
    simp [norm_char]
  exact (norm_sub_le _ _).trans (add_le_add (h A) (h B))

/- English proof (translation)
Establish `h1 : ∑ z, ‖dif A B z‖ ^ 2 = (Fintype.card G : ℝ) * ((#A : ℝ) + #B)`. Use `parseval A B hd` as an intermediate fact. Rewrite `this` using `[Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Conclude with `this` after adjusting the coercions. Establish `h2 : ∑ z, ‖dif A B z‖ ^ 2 = ∑ z ∈ D, ‖dif A B z‖ ^ 2`.

Use `symm`. Use `Finset.sum_subset (Finset.subset_univ _) (fun z _ hz => ?_)` and prove the remaining obligations. Simplify using `[hD z hz]`. Establish `h3 : ∑ z ∈ D, ‖dif A B z‖ ^ 2 ≤ (#D : ℝ) * ((#A : ℝ) + #B) ^ 2`. Establish `: ∀ z ∈ D, ‖dif A B z‖ ^ 2 ≤ ((#A : ℝ) + #B) ^ 2` using `fun z _ => pow_le_pow_left₀ (norm_nonneg _) (norm_dif_le A B z) 2`.

Simplify using `using Finset.sum_le_sum this`. Establish `hpos : (0 : ℝ) < (#A : ℝ) + #B` using `by exact_mod_cast hne`. Establish `h4 : (Fintype.card G : ℝ) ≤ (#D : ℝ) * ((#A : ℝ) + #B)`. Establish `: (Fintype.card G : ℝ) * ((#A : ℝ) + #B) ≤ ((#D : ℝ) * ((#A : ℝ) + #B)) * ((#A : ℝ) + #B)`. Rewrite using `[← h1, h2]`.

Use polynomial arithmetic with `[h3]`. Conclude with `le_of_mul_le_mul_right this hpos`. Conclude with `h4` after adjusting the coercions.
-/
theorem card_le (A B : Finset (G →* ℂˣ)) (hd : Disjoint A B) (D : Finset G)
    (hD : ∀ z, z ∉ D → dif A B z = 0) (hne : 0 < #A + #B) :
    Fintype.card G ≤ #D * (#A + #B) := by
  have h1 : ∑ z, ‖dif A B z‖ ^ 2 = (Fintype.card G : ℝ) * ((#A : ℝ) + #B) := by
    have := parseval A B hd
    simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at this
    exact_mod_cast this
  have h2 : ∑ z, ‖dif A B z‖ ^ 2 = ∑ z ∈ D, ‖dif A B z‖ ^ 2 := by
    symm
    refine Finset.sum_subset (Finset.subset_univ _) (fun z _ hz => ?_)
    simp [hD z hz]
  have h3 : ∑ z ∈ D, ‖dif A B z‖ ^ 2 ≤ (#D : ℝ) * ((#A : ℝ) + #B) ^ 2 := by
    have : ∀ z ∈ D, ‖dif A B z‖ ^ 2 ≤ ((#A : ℝ) + #B) ^ 2 := fun z _ =>
      pow_le_pow_left₀ (norm_nonneg _) (norm_dif_le A B z) 2
    simpa using Finset.sum_le_sum this
  have hpos : (0 : ℝ) < (#A : ℝ) + #B := by exact_mod_cast hne
  have h4 : (Fintype.card G : ℝ) ≤ (#D : ℝ) * ((#A : ℝ) + #B) := by
    have : (Fintype.card G : ℝ) * ((#A : ℝ) + #B) ≤ ((#D : ℝ) * ((#A : ℝ) + #B)) * ((#A : ℝ) + #B) := by
      rw [← h1, h2]
      nlinarith [h3]
    exact le_of_mul_le_mul_right this hpos
  exact_mod_cast h4

/- English proof (translation)
Establish `h1 : ∑ z, dif A B z * conj (((ψ * η) z : ℂˣ) : ℂ) = ∑ z, dif A B z * conj ((ψ z : ℂˣ) : ℂ)`. Use `Finset.sum_congr rfl (fun z _ => ?_)` and prove the remaining obligations. Distinguish the cases in `hz : z ∈ D`. Simplify using `[hη z hz]`. Simplify using `[hD z hz]`.

Rewrite `h1` using `[inner_dif, inner_dif]`. Establish `hc : (Fintype.card G : ℂ) ≠ 0` using `by exact_mod_cast Fintype.card_ne_zero`. Establish `h2` using `mul_left_cancel₀ hc h1`. Prove the components needed by the constructor for the conclusion. Introduce `hψ`.

Establish `hB : ψ ∉ B` using `Finset.disjoint_left.mp hd hψ`. Assume the negation of the conclusion as `hn`. Apply the tactic sequence `by_cases hb : ψ * η ∈ B <;> simp [hn, hψ, hB, hb] at h2`. Evaluate the numerical expressions using `at h2`. Introduce `hψ`.

Establish `hA : ψ ∉ A` using `Finset.disjoint_right.mp hd hψ`. Assume the negation of the conclusion as `hn`. Apply the tactic sequence `by_cases ha : ψ * η ∈ A <;> simp [hn, hψ, hA, ha] at h2`. Evaluate the numerical expressions using `at h2`.
-/
theorem mul_mem (A B : Finset (G →* ℂˣ)) (hd : Disjoint A B) (D : Finset G)
    (hD : ∀ z, z ∉ D → dif A B z = 0) (η : G →* ℂˣ) (hη : ∀ z ∈ D, η z = 1) (ψ : G →* ℂˣ) :
    (ψ ∈ A → ψ * η ∈ A) ∧ (ψ ∈ B → ψ * η ∈ B) := by
  classical
  have h1 : ∑ z, dif A B z * conj (((ψ * η) z : ℂˣ) : ℂ) = ∑ z, dif A B z * conj ((ψ z : ℂˣ) : ℂ) := by
    refine Finset.sum_congr rfl (fun z _ => ?_)
    by_cases hz : z ∈ D
    · simp [hη z hz]
    · simp [hD z hz]
  rw [inner_dif, inner_dif] at h1
  have hc : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h2 := mul_left_cancel₀ hc h1
  constructor
  · intro hψ
    have hB : ψ ∉ B := Finset.disjoint_left.mp hd hψ
    by_contra hn
    by_cases hb : ψ * η ∈ B <;> simp [hn, hψ, hB, hb] at h2
    norm_num at h2
  · intro hψ
    have hA : ψ ∉ A := Finset.disjoint_right.mp hd hψ
    by_contra hn
    by_cases ha : ψ * η ∈ A <;> simp [hn, hψ, hA, ha] at h2
    norm_num at h2

end UpperTheory.Zero.LLC.CharacterSumPairs
