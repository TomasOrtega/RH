import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDiagExists

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

def frameMat (k : ℕ) (u : Fin (k + 1) → ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := fun i j =>
  if i = Fin.last k then
    (if j = Fin.last k then u (Fin.last k)
      else u (Fin.last k) * (((‖u (Fin.last k)‖)⁻¹ : ℝ) : ℂ) * star (u j))
  else if j = Fin.last k then u i
  else (if i = j then 1 else 0) + u i * star (u j) * (((1 + ‖u (Fin.last k)‖)⁻¹ : ℝ) : ℂ)

/- English proof (translation)
Distinguish the cases in `h : i = Fin.last k`. Substitute `h` using the available equality. Simplify using `[frameMat]`. Simplify using `[frameMat, h]`.
-/
theorem frameMat_col (k : ℕ) (u : Fin (k + 1) → ℂ) (i : Fin (k + 1)) :
    frameMat k u i (Fin.last k) = u i := by
  by_cases h : i = Fin.last k
  · subst h; simp [frameMat]
  · simp [frameMat, h]

/- English proof (translation)
Rewrite using `[Complex.star_def, Complex.conj_mul']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem frameMat_star_mul_self (t : ℂ) : star t * t = ((‖t‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.conj_mul']
  push_cast
  ring

section
variable (k : ℕ) (u : Fin (k + 1) → ℂ)

/- English proof (translation)
Simplify using `[frameMat, (Fin.castSucc_lt_last x).ne, (Fin.castSucc_lt_last i).ne, Fin.castSucc_inj]`.
-/
theorem frameMat_cc (x i : Fin k) : frameMat k u x.castSucc i.castSucc =
    (if x = i then 1 else 0) + u x.castSucc * star (u i.castSucc) * (((1 + ‖u (Fin.last k)‖)⁻¹ : ℝ) : ℂ) := by
  simp [frameMat, (Fin.castSucc_lt_last x).ne, (Fin.castSucc_lt_last i).ne, Fin.castSucc_inj]

/- English proof (translation)
Simplify using `[frameMat, (Fin.castSucc_lt_last i).ne]`.
-/
theorem frameMat_lc (i : Fin k) : frameMat k u (Fin.last k) i.castSucc =
    u (Fin.last k) * (((‖u (Fin.last k)‖)⁻¹ : ℝ) : ℂ) * star (u i.castSucc) := by
  simp [frameMat, (Fin.castSucc_lt_last i).ne]

/- English proof (translation)
Simplify using `[frameMat, (Fin.castSucc_lt_last x).ne]`.
-/
theorem frameMat_cl (x : Fin k) : frameMat k u x.castSucc (Fin.last k) = u x.castSucc := by
  simp [frameMat, (Fin.castSucc_lt_last x).ne]

/- English proof (translation)
Simplify using `[frameMat]`.
-/
theorem frameMat_ll : frameMat k u (Fin.last k) (Fin.last k) = u (Fin.last k) := by
  simp [frameMat]

end

/- English proof (translation)
Rewrite using `[Complex.star_def, Complex.conj_ofReal]`.
-/
theorem frameMat_star_ofReal (x : ℝ) : star ((x : ℝ) : ℂ) = (x : ℂ) := by
  rw [Complex.star_def, Complex.conj_ofReal]

/- English proof (translation)
Use `set t := u (Fin.last k) with ht`. Use `set n : ℝ := ‖t‖ with hn`. Use `set c : ℝ := (1 + n)⁻¹ with hc`. Use `set m : ℝ := n⁻¹ with hm`. Establish `ht2 : star t * t = (n : ℂ) ^ 2` using `by rw [frameMat_star_mul_self]; push_cast; rfl`.

Establish `hreal : (∑ l : Fin k, ‖u l.castSucc‖ ^ 2 : ℝ) = n ^ 2 - 1`. Establish `h1` using `hu`. Simplify using `only [frameMat_star_mul_self] at h1`. Conclude with `h1` after adjusting the coercions. Establish `hn1 : 1 ≤ n ^ 2`.

Establish `: 0 ≤ (∑ l : Fin k, ‖u l.castSucc‖ ^ 2 : ℝ)` using `Finset.sum_nonneg (fun _ _ => by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hnpos : 0 < n`. Establish `: 0 ≤ n` using `norm_nonneg _`. Break down `this.eq_or_lt with h | h` into its components or cases.

Rewrite `hn1` using `[← h]`. Evaluate the numerical expressions using `at hn1`. Conclude with `h`. Establish `key : (2 : ℂ) * (c : ℂ) + ((n : ℂ) ^ 2 - 1) * (c : ℂ) ^ 2 - (n : ℂ) ^ 2 * (m : ℂ) ^ 2 = 0`. Establish `: (2 * c + (n ^ 2 - 1) * c ^ 2 - n ^ 2 * m ^ 2 : ℝ) = 0`.

Rewrite using `[hc, hm]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Conclude with `this` after adjusting the coercions. Establish `key2 : (1 : ℂ) + ((n : ℂ) ^ 2 - 1) * (c : ℂ) - (n : ℂ) ^ 2 * (m : ℂ) = 0`.

Establish `: (1 + (n ^ 2 - 1) * c - n ^ 2 * m : ℝ) = 0`. Rewrite using `[hc, hm]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Conclude with `this` after adjusting the coercions.

Establish `hne : ∀ x : Fin k, (Fin.last k = x.castSucc) = False` using `fun x => eq_false (fun h => Fin.castSucc_ne_last x h.symm)`. Establish `hne' : ∀ x : Fin k, (x.castSucc = Fin.last k) = False` using `fun x => eq_false (Fin.castSucc_ne_last x)`. Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [Hb, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Fin.sum_univ_castSucc]`.

Consider the cases of `i using Fin.lastCases with`. Consider the case `last`. Consider the cases of `j using Fin.lastCases with`. Consider the case `last`. Simplify using `only [frameMat_ll, frameMat_cl, Matrix.diagonal_apply, hne', if_true, if_false, mul_one]`.

Rewrite using `[hu]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `cast j`. Simplify using `only [frameMat_ll, frameMat_cl, frameMat_lc, frameMat_cc, Matrix.diagonal_apply, hne, hne', if_true, if_false, mul_one, ← ht, ← hn, ← hc, ← hm]`. Establish `hpt : ∀ x : Fin k, star (u x.castSucc) * ((if x = j then (1 : ℂ) else 0) + u x.castSucc * star (u j.castSucc) * (c : ℂ)) = (if x = j then star (u j.castSucc) else 0) + star (u x.castSucc) * u x.castSucc * (star (u j.castSucc) * (c : ℂ))`.

Apply the tactic sequence `intro x; split_ifs with h <;> [subst h; skip] <;> ring`. Rewrite using `[Finset.sum_congr rfl (fun x _ => hpt x)]`. Simplify using `only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, ← Finset.sum_mul, hu, star_mul, frameMat_star_ofReal, star_star]`. Take the linear combination `(star (u j.castSucc)) * key2 + (star (u j.castSucc) * (c : ℂ) - star (u j.castSucc) * (m : ℂ)) * ht2`. Consider the case `cast i`.

Consider the cases of `j using Fin.lastCases with`. Consider the case `last`. Simplify using `only [frameMat_ll, frameMat_cl, frameMat_lc, frameMat_cc, Matrix.diagonal_apply, hne, hne', if_true, if_false, mul_one, ← ht, ← hn, ← hc, ← hm]`. Establish `hpt : ∀ x : Fin k, star ((if x = i then (1 : ℂ) else 0) + u x.castSucc * star (u i.castSucc) * (c : ℂ)) * u x.castSucc = (if x = i then u i.castSucc else 0) + star (u x.castSucc) * u x.castSucc * (u i.castSucc * (c : ℂ))`. Apply the tactic sequence `intro x; split_ifs with h <;> [subst h; skip] <;> simp only [star_add, star_mul, frameMat_star_ofReal, star_star, star_one, star_zero] <;> ring`.

Rewrite using `[Finset.sum_congr rfl (fun x _ => hpt x)]`. Simplify using `only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, ← Finset.sum_mul, hu, star_mul, frameMat_star_ofReal, star_star]`. Take the linear combination `(u i.castSucc) * key2 + (u i.castSucc * (c : ℂ) - u i.castSucc * (m : ℂ)) * ht2`. Consider the case `cast j`. Simplify using `only [frameMat_ll, frameMat_cl, frameMat_lc, frameMat_cc, Matrix.diagonal_apply, hne, hne', if_true, if_false, mul_one, Fin.castSucc_inj, ← ht, ← hn, ← hc, ← hm]`.

Establish `hpt : ∀ x : Fin k, star ((if x = i then (1 : ℂ) else 0) + u x.castSucc * star (u i.castSucc) * (c : ℂ)) * ((if x = j then (1 : ℂ) else 0) + u x.castSucc * star (u j.castSucc) * (c : ℂ)) = (if x = i then (if i = j then 1 else 0) + u i.castSucc * star (u j.castSucc) * (c : ℂ) else …`. Apply the tactic sequence `intro x; split_ifs <;> subst_vars <;> first`. Consider the case `exact (‹¬ _ = _› rfl).elim`. Consider the case `(simp only [star_add, star_mul, frameMat_star_ofReal, star_star, star_one, star_zero]; ring)`. Rewrite using `[Finset.sum_congr rfl (fun x _ => hpt x)]`.

Simplify using `only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, ← Finset.sum_mul, hu, star_mul, frameMat_star_ofReal, star_star]`. Take the linear combination `(u i.castSucc * star (u j.castSucc)) * key + (u i.castSucc * star (u j.castSucc) * (c : ℂ) ^ 2 - u i.castSucc * star (u j.castSucc) * (m : ℂ) ^ 2) * ht2`.
-/
theorem frameMat_unitary (k : ℕ) (u : Fin (k + 1) → ℂ)
    (hu : ∑ l : Fin k, star (u l.castSucc) * u l.castSucc = star (u (Fin.last k)) * u (Fin.last k) - 1) :
    (frameMat k u)ᴴ * Hb k * frameMat k u = Hb k := by
  set t := u (Fin.last k) with ht
  set n : ℝ := ‖t‖ with hn
  set c : ℝ := (1 + n)⁻¹ with hc
  set m : ℝ := n⁻¹ with hm
  have ht2 : star t * t = (n : ℂ) ^ 2 := by rw [frameMat_star_mul_self]; push_cast; rfl
  have hreal : (∑ l : Fin k, ‖u l.castSucc‖ ^ 2 : ℝ) = n ^ 2 - 1 := by
    have h1 := hu
    simp only [frameMat_star_mul_self] at h1
    exact_mod_cast h1
  have hn1 : 1 ≤ n ^ 2 := by
    have : 0 ≤ (∑ l : Fin k, ‖u l.castSucc‖ ^ 2 : ℝ) := Finset.sum_nonneg (fun _ _ => by positivity)
    linarith
  have hnpos : 0 < n := by
    have : 0 ≤ n := norm_nonneg _
    rcases this.eq_or_lt with h | h
    · rw [← h] at hn1; norm_num at hn1
    · exact h
  have key : (2 : ℂ) * (c : ℂ) + ((n : ℂ) ^ 2 - 1) * (c : ℂ) ^ 2 - (n : ℂ) ^ 2 * (m : ℂ) ^ 2 = 0 := by
    have : (2 * c + (n ^ 2 - 1) * c ^ 2 - n ^ 2 * m ^ 2 : ℝ) = 0 := by
      rw [hc, hm]; field_simp; ring
    exact_mod_cast this
  have key2 : (1 : ℂ) + ((n : ℂ) ^ 2 - 1) * (c : ℂ) - (n : ℂ) ^ 2 * (m : ℂ) = 0 := by
    have : (1 + (n ^ 2 - 1) * c - n ^ 2 * m : ℝ) = 0 := by
      rw [hc, hm]; field_simp; ring
    exact_mod_cast this
  have hne : ∀ x : Fin k, (Fin.last k = x.castSucc) = False :=
    fun x => eq_false (fun h => Fin.castSucc_ne_last x h.symm)
  have hne' : ∀ x : Fin k, (x.castSucc = Fin.last k) = False :=
    fun x => eq_false (Fin.castSucc_ne_last x)
  ext i j
  rw [Matrix.mul_apply]
  simp only [Hb, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Fin.sum_univ_castSucc]
  cases i using Fin.lastCases with
  | last =>
    cases j using Fin.lastCases with
    | last =>
      simp only [frameMat_ll, frameMat_cl, Matrix.diagonal_apply, hne', if_true, if_false, mul_one]
      rw [hu]; ring
    | cast j =>
      simp only [frameMat_ll, frameMat_cl, frameMat_lc, frameMat_cc, Matrix.diagonal_apply, hne, hne', if_true, if_false, mul_one,
        ← ht, ← hn, ← hc, ← hm]
      have hpt : ∀ x : Fin k, star (u x.castSucc) * ((if x = j then (1 : ℂ) else 0) +
          u x.castSucc * star (u j.castSucc) * (c : ℂ)) =
          (if x = j then star (u j.castSucc) else 0) + star (u x.castSucc) * u x.castSucc *
            (star (u j.castSucc) * (c : ℂ)) := by
        intro x; split_ifs with h <;> [subst h; skip] <;> ring
      rw [Finset.sum_congr rfl (fun x _ => hpt x)]
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, ← Finset.sum_mul, hu,
        star_mul, frameMat_star_ofReal, star_star]
      linear_combination (star (u j.castSucc)) * key2 +
        (star (u j.castSucc) * (c : ℂ) - star (u j.castSucc) * (m : ℂ)) * ht2
  | cast i =>
    cases j using Fin.lastCases with
    | last =>
      simp only [frameMat_ll, frameMat_cl, frameMat_lc, frameMat_cc, Matrix.diagonal_apply, hne, hne', if_true, if_false, mul_one,
        ← ht, ← hn, ← hc, ← hm]
      have hpt : ∀ x : Fin k, star ((if x = i then (1 : ℂ) else 0) +
          u x.castSucc * star (u i.castSucc) * (c : ℂ)) * u x.castSucc =
          (if x = i then u i.castSucc else 0) + star (u x.castSucc) * u x.castSucc *
            (u i.castSucc * (c : ℂ)) := by
        intro x; split_ifs with h <;> [subst h; skip] <;> simp only [star_add, star_mul, frameMat_star_ofReal, star_star,
          star_one, star_zero] <;> ring
      rw [Finset.sum_congr rfl (fun x _ => hpt x)]
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, ← Finset.sum_mul, hu,
        star_mul, frameMat_star_ofReal, star_star]
      linear_combination (u i.castSucc) * key2 +
        (u i.castSucc * (c : ℂ) - u i.castSucc * (m : ℂ)) * ht2
    | cast j =>
      simp only [frameMat_ll, frameMat_cl, frameMat_lc, frameMat_cc, Matrix.diagonal_apply, hne, hne', if_true, if_false, mul_one,
        Fin.castSucc_inj, ← ht, ← hn, ← hc, ← hm]
      have hpt : ∀ x : Fin k, star ((if x = i then (1 : ℂ) else 0) +
          u x.castSucc * star (u i.castSucc) * (c : ℂ)) * ((if x = j then (1 : ℂ) else 0) +
          u x.castSucc * star (u j.castSucc) * (c : ℂ)) =
          (if x = i then (if i = j then 1 else 0) + u i.castSucc * star (u j.castSucc) * (c : ℂ) else 0) +
          (if x = j then star (u j.castSucc) * u i.castSucc * (c : ℂ) else 0) +
          star (u x.castSucc) * u x.castSucc * (u i.castSucc * star (u j.castSucc) * (c : ℂ) ^ 2) := by
        intro x; split_ifs <;> subst_vars <;> first
          | exact (‹¬ _ = _› rfl).elim
          | (simp only [star_add, star_mul, frameMat_star_ofReal, star_star, star_one, star_zero]; ring)
      rw [Finset.sum_congr rfl (fun x _ => hpt x)]
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, ← Finset.sum_mul, hu,
        star_mul, frameMat_star_ofReal, star_star]
      linear_combination (u i.castSucc * star (u j.castSucc)) * key +
        (u i.castSucc * star (u j.castSucc) * (c : ℂ) ^ 2 - u i.castSucc * star (u j.castSucc) * (m : ℂ) ^ 2) * ht2

def frameCoef (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if r ≤ i.val ∧ i.val ≤ r + k then (if i.val = r + k then -1 else 1) else 0

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem frame_wI_val (k r : ℕ) (j : Fin (k + 1)) : (wI k r j).val = r + j.val := rfl

/- English proof (translation)
Distinguish the cases in `hij : j = i`. Substitute `hij` using the available equality. Rewrite using `[if_pos rfl]`. Distinguish the cases in `hj : j.val < r ∨ r + k < j.val`. Rewrite using `[hz j hj, mul_zero, mul_zero]`.

Use `congr 1`. Unfold `Hpk frameCoef`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega) | simp_all`. Rewrite using `[if_neg hij]`. Distinguish the cases in `hj : j.val < r ∨ r + k < j.val`.

Rewrite using `[hz j hj, mul_zero]`. Establish `hv : j.val ≠ i.val` using `fun h => hij (Fin.ext h)`. Unfold `Hpk`. Apply the tactic sequence `split_ifs <;> first | (exfalso; omega) | simp_all | simp`.
-/
theorem frame_Hpk_mul (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j * z j = if j = i then frameCoef k r i * z i else 0 := by
  by_cases hij : j = i
  · subst hij
    rw [if_pos rfl]
    by_cases hj : j.val < r ∨ r + k < j.val
    · rw [hz j hj, mul_zero, mul_zero]
    · congr 1
      unfold Hpk frameCoef
      split_ifs <;> first | rfl | (exfalso; omega) | simp_all
  · rw [if_neg hij]
    by_cases hj : j.val < r ∨ r + k < j.val
    · rw [hz j hj, mul_zero]
    · have hv : j.val ≠ i.val := fun h => hij (Fin.ext h)
      unfold Hpk
      split_ifs <;> first | (exfalso; omega) | simp_all | simp

/- English proof (translation)
Establish `hrow : ∀ i, (Hpk k r *ᵥ z) i = frameCoef k r i * z i`. Introduce `i`. Use `show ∑ j, Hpk k r i j * z j = _`. Rewrite using `[Finset.sum_congr rfl (fun j _ => frame_Hpk_mul k r z hz i j)]`. Simplify using the standard rewrite rules.

Use `show ∑ i, star (z i) * (Hpk k r *ᵥ z) i = _`. Simplify using `only [hrow]`. Establish `hinj : Function.Injective (wI k r)`. Introduce `a b h`. Establish `h'` using `congrArg Fin.val h`.

Rewrite `h'` using `[frame_wI_val, frame_wI_val]`. Conclude with `Fin.ext (by omega)`. Establish `hsub : ∑ i, star (z i) * (frameCoef k r i * z i) = ∑ i ∈ Finset.univ.image (wI k r), star (z i) * (frameCoef k r i * z i)`. Use `symm`. Apply `Finset.sum_subset (Finset.subset_univ _)` to reduce the goal to its premises.

Introduce `i _ hi`. Establish `hn : ¬ (r ≤ i.val ∧ i.val ≤ r + k)`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `hi (Finset.mem_image.2 ⟨⟨i.val - r, by omega⟩, Finset.mem_univ _, Fin.ext (by rw [frame_wI_val]; simp; omega)⟩)`. Simplify using `[frameCoef, hn]`.

Establish `hc1 : ∀ l : Fin k, frameCoef k r (wI k r l.castSucc) = 1`. Introduce `l`. Establish `hl` using `l.isLt`. Establish `h1 : r ≤ r + (l : ℕ) ∧ r + (l : ℕ) ≤ r + k` using `by omega`. Establish `h3 : (l : ℕ) ≠ k` using `by omega`.

Simplify using `[frameCoef, frame_wI_val, h1, h3]`. Establish `hc2 : frameCoef k r (wI k r (Fin.last k)) = -1`. Simplify using `[frameCoef, frame_wI_val]`. Rewrite using `[hsub, Finset.sum_image (fun a _ b _ h => hinj h), Fin.sum_univ_castSucc]`. Simplify using `only [hc1, hc2, one_mul, neg_one_mul, mul_neg, sub_eq_add_neg]`.
-/
theorem frame_herm (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) :
    herm (Hpk k r) z z = ∑ l : Fin k, star (z (wI k r l.castSucc)) * z (wI k r l.castSucc) -
      star (z (wI k r (Fin.last k))) * z (wI k r (Fin.last k)) := by
  have hrow : ∀ i, (Hpk k r *ᵥ z) i = frameCoef k r i * z i := by
    intro i
    show ∑ j, Hpk k r i j * z j = _
    rw [Finset.sum_congr rfl (fun j _ => frame_Hpk_mul k r z hz i j)]
    simp
  show ∑ i, star (z i) * (Hpk k r *ᵥ z) i = _
  simp only [hrow]
  have hinj : Function.Injective (wI k r) := by
    intro a b h
    have h' := congrArg Fin.val h
    rw [frame_wI_val, frame_wI_val] at h'
    exact Fin.ext (by omega)
  have hsub : ∑ i, star (z i) * (frameCoef k r i * z i) =
      ∑ i ∈ Finset.univ.image (wI k r), star (z i) * (frameCoef k r i * z i) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    have hn : ¬ (r ≤ i.val ∧ i.val ≤ r + k) := by
      rintro ⟨h1, h2⟩
      exact hi (Finset.mem_image.2 ⟨⟨i.val - r, by omega⟩, Finset.mem_univ _,
        Fin.ext (by rw [frame_wI_val]; simp; omega)⟩)
    simp [frameCoef, hn]
  have hc1 : ∀ l : Fin k, frameCoef k r (wI k r l.castSucc) = 1 := by
    intro l
    have hl := l.isLt
    have h1 : r ≤ r + (l : ℕ) ∧ r + (l : ℕ) ≤ r + k := by omega
    have h3 : (l : ℕ) ≠ k := by omega
    simp [frameCoef, frame_wI_val, h1, h3]
  have hc2 : frameCoef k r (wI k r (Fin.last k)) = -1 := by
    simp [frameCoef, frame_wI_val]
  rw [hsub, Finset.sum_image (fun a _ b _ h => hinj h), Fin.sum_univ_castSucc]
  simp only [hc1, hc2, one_mul, neg_one_mul, mul_neg, sub_eq_add_neg]

end ReciprocityTheory.ChartRestriction.DS.Mult1
