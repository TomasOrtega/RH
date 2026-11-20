import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JRepsA

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.RepsA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k : ℕ}

/- English proof (translation)
Introduce `h`. Establish `h2` using `congrArg Fin.val h`. Simplify using `only [Fin.val_zero, Fin.val_last] at h2`. Use linear arithmetic over natural numbers and integers.
-/
theorem zero_ne_last (hk : 1 ≤ k) : (0 : Fin (k + 1)) ≠ Fin.last k := by
  intro h
  have h2 := congrArg Fin.val h
  simp only [Fin.val_zero, Fin.val_last] at h2
  omega

def sgd (d : ℂ) : ℂ := ((Real.sqrt (Complex.normSq d - 1) : ℝ) : ℂ)

/- English proof (translation)
Establish `hx : 0 ≤ Complex.normSq d - 1`. Establish `h1 : 1 < Complex.normSq d`. Rewrite using `[Complex.normSq_eq_norm_sq]`. Use polynomial arithmetic with `[norm_nonneg d]`. Combine the linear equalities and inequalities to obtain the conclusion.

Unfold `sgd`. Rewrite using `[← Complex.ofReal_mul, Real.mul_self_sqrt hx, Complex.mul_conj, Complex.ofReal_sub, Complex.ofReal_one]`.
-/
theorem sgd_sq (d : ℂ) (hd : 1 < ‖d‖) : sgd d * sgd d = d * conj d - 1 := by
  have hx : 0 ≤ Complex.normSq d - 1 := by
    have h1 : 1 < Complex.normSq d := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg d]
    linarith
  unfold sgd
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt hx, Complex.mul_conj, Complex.ofReal_sub, Complex.ofReal_one]

/- English proof (translation)
Unfold `sgd`. Conclude with `Complex.conj_ofReal _`.
-/
theorem star_sgd (d : ℂ) : star (sgd d) = sgd d := by
  unfold sgd
  exact Complex.conj_ofReal _

section entries
variable (hk : 1 ≤ k) (d : ℂ)
include hk

/- English proof (translation)
Unfold `mud`. Simplify using the standard rewrite rules.
-/
theorem character_first_entry : mud k d 0 0 = -conj d := by
  unfold mud
  simp
/- English proof (translation)
Establish `h0` using `zero_ne_last hk`. Unfold `mud sgd`. Rewrite using `[if_neg (fun h => h0 h.1.symm), if_pos ⟨rfl, rfl⟩]`.
-/
theorem character_last_entry : mud k d (Fin.last k) 0 = -sgd d := by
  have h0 := zero_ne_last hk
  unfold mud sgd
  rw [if_neg (fun h => h0 h.1.symm), if_pos ⟨rfl, rfl⟩]
/- English proof (translation)
Establish `h0` using `zero_ne_last hk`. Unfold `mud sgd`. Rewrite using `[if_neg (fun h => h0 h.2.symm), if_neg (fun h => h0 h.1), if_pos ⟨rfl, rfl⟩]`.
-/
theorem mud0L : mud k d 0 (Fin.last k) = sgd d := by
  have h0 := zero_ne_last hk
  unfold mud sgd
  rw [if_neg (fun h => h0 h.2.symm), if_neg (fun h => h0 h.1), if_pos ⟨rfl, rfl⟩]
/- English proof (translation)
Establish `h0` using `zero_ne_last hk`. Unfold `mud`. Rewrite using `[if_neg (fun h => h0 h.1.symm), if_neg (fun h => h0 h.2.symm), if_neg (fun h => h0 h.1.symm), if_pos ⟨rfl, rfl⟩]`.
-/
theorem mudLL : mud k d (Fin.last k) (Fin.last k) = d := by
  have h0 := zero_ne_last hk
  unfold mud
  rw [if_neg (fun h => h0 h.1.symm), if_neg (fun h => h0 h.2.symm), if_neg (fun h => h0 h.1.symm),
    if_pos ⟨rfl, rfl⟩]

/- English proof (translation)
Unfold `mud`. Rewrite using `[if_neg (fun h => hj0 h.2), if_neg (fun h => hj0 h.2), if_neg (fun h => hjL h.2), if_neg (fun h => hjL h.2)]`.
-/
theorem mud_col {l j : Fin (k + 1)} (hj0 : j ≠ 0) (hjL : j ≠ Fin.last k) :
    mud k d l j = if l = j then 1 else 0 := by
  unfold mud
  rw [if_neg (fun h => hj0 h.2), if_neg (fun h => hj0 h.2), if_neg (fun h => hjL h.2),
    if_neg (fun h => hjL h.2)]

/- English proof (translation)
Unfold `mud`. Rewrite using `[if_neg (fun h => hl0 h.1), if_neg (fun h => hlL h.1), if_neg (fun h => hl0 h.1), if_neg (fun h => hlL h.1)]`.
-/
theorem mud_row {l j : Fin (k + 1)} (hl0 : l ≠ 0) (hlL : l ≠ Fin.last k) :
    mud k d l j = if l = j then 1 else 0 := by
  unfold mud
  rw [if_neg (fun h => hl0 h.1), if_neg (fun h => hlL h.1), if_neg (fun h => hl0 h.1),
    if_neg (fun h => hlL h.1)]

/- English proof (translation)
The claim follows from `Finset.sum_eq_add 0 (Fin.last k) (zero_ne_last hk) (fun c _ hc => hf c hc.1 hc.2) (fun h => absurd (Finset.mem_univ _) h) (fun h => absurd (Finset.mem_univ _) h)`.
-/
theorem sum_two {f : Fin (k + 1) → ℂ} (hf : ∀ l, l ≠ 0 → l ≠ Fin.last k → f l = 0) :
    ∑ l, f l = f 0 + f (Fin.last k) := Finset.sum_eq_add 0 (Fin.last k) (zero_ne_last hk) (fun c _ hc => hf c hc.1 hc.2)
    (fun h => absurd (Finset.mem_univ _) h) (fun h => absurd (Finset.mem_univ _) h)

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Simplify using `[mud_col hk d hj0 hjL]`.
-/
theorem mul_mud_col (P : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) {i j : Fin (k + 1)} (hj0 : j ≠ 0)
    (hjL : j ≠ Fin.last k) : (P * mud k d) i j = P i j := by
  rw [Matrix.mul_apply]
  simp [mud_col hk d hj0 hjL]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Apply `sum_two hk` to reduce the goal to its premises. Introduce `l hl0 hlL`. Rewrite using `[mud_row hk d hl0 hlL, if_neg, mul_zero]`. Introduce and unpack `rfl`.

Break down `hj with h | h` into its components or cases. Conclude with `hl0 h`. Conclude with `hlL h`.
-/
theorem mul_mud_blk (P : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i j : Fin (k + 1)) (hj : j = 0 ∨ j = Fin.last k) :
    (P * mud k d) i j = P i 0 * mud k d 0 j + P i (Fin.last k) * mud k d (Fin.last k) j := by
  rw [Matrix.mul_apply]
  apply sum_two hk
  intro l hl0 hlL
  rw [mud_row hk d hl0 hlL, if_neg, mul_zero]
  rintro rfl
  rcases hj with h | h
  · exact hl0 h
  · exact hlL h

end entries

/- English proof (translation)
Unfold `Hb`. Rewrite using `[Matrix.diagonal_apply]`.
-/
theorem Hb_apply (i j : Fin (k + 1)) : Hb k i j = if i = j then (if i = Fin.last k then -1 else 1) else 0 := by
  unfold Hb
  rw [Matrix.diagonal_apply]

/- English proof (translation)
Establish `hs` using `sgd_sq d hd`. Establish `hss` using `star_sgd d`. Establish `h0L` using `zero_ne_last hk`. Use extensionality with `i j`. Establish `hP : ∀ a b : Fin (k + 1), ((mud k d)ᴴ * Hb k) a b = star (mud k d b a) * (if b = Fin.last k then -1 else 1)`.

Introduce `a b`. Unfold `Hb`. Rewrite using `[mul_diagonal, conjTranspose_apply]`. Break down `eq_or_ne j 0 with rfl | hj0` into its components or cases. Rewrite using `[mul_mud_blk hk d _ _ _ (Or.inl rfl), hP, hP, Hb_apply]`.

Break down `eq_or_ne i 0 with rfl | hi0` into its components or cases. Apply the tactic sequence `simp only [character_first_entry hk, character_last_entry hk, if_true, if_neg h0L, if_neg h0L.symm, star_neg, hss, Complex.star_def, Complex.conj_conj]`. Take the linear combination `-hs`. Break down `eq_or_ne i (Fin.last k) with rfl | hiL` into its components or cases. Apply the tactic sequence `simp only [mud0L hk, mudLL hk, character_first_entry hk, character_last_entry hk, if_true, if_neg h0L, if_neg h0L.symm, hss, Complex.star_def]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [mud_col hk d hi0 hiL, if_neg (Ne.symm hi0), if_neg (Ne.symm hiL), if_neg hi0]`. Simplify using the standard rewrite rules. Break down `eq_or_ne j (Fin.last k) with rfl | hjL` into its components or cases. Rewrite using `[mul_mud_blk hk d _ _ _ (Or.inr rfl), hP, hP, Hb_apply]`.

Break down `eq_or_ne i 0 with rfl | hi0` into its components or cases. Apply the tactic sequence `simp only [character_first_entry hk, character_last_entry hk, mud0L hk, mudLL hk, if_true, if_neg h0L, if_neg h0L.symm, star_neg, hss, Complex.star_def, Complex.conj_conj]`. Expand and normalize the polynomial expressions, which then agree. Break down `eq_or_ne i (Fin.last k) with rfl | hiL` into its components or cases. Simplify using `only [mud0L hk, mudLL hk, if_true, if_neg h0L, if_neg h0L.symm, hss, Complex.star_def]`.

Take the linear combination `hs`. Simplify using `only [mud_col hk d hi0 hiL, if_neg (Ne.symm hi0), if_neg (Ne.symm hiL), if_neg hiL]`. Simplify using the standard rewrite rules. Rewrite using `[mul_mud_col hk d _ hj0 hjL, hP, mud_row hk d hj0 hjL, Hb_apply]`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using `[hjL]`. Rewrite using `[if_neg (Ne.symm hij), if_neg hij]`. Simplify using the standard rewrite rules.
-/
theorem mud_unitary (hk : 1 ≤ k) (d : ℂ) (hd : 1 < ‖d‖) : (mud k d)ᴴ * Hb k * mud k d = Hb k := by
  have hs := sgd_sq d hd
  have hss := star_sgd d
  have h0L := zero_ne_last hk
  ext i j
  have hP : ∀ a b : Fin (k + 1), ((mud k d)ᴴ * Hb k) a b = star (mud k d b a) * (if b = Fin.last k then -1 else 1) := by
    intro a b; unfold Hb; rw [mul_diagonal, conjTranspose_apply]
  rcases eq_or_ne j 0 with rfl | hj0
  · rw [mul_mud_blk hk d _ _ _ (Or.inl rfl), hP, hP, Hb_apply]
    rcases eq_or_ne i 0 with rfl | hi0
    · simp only [character_first_entry hk, character_last_entry hk, if_true, if_neg h0L, if_neg h0L.symm, star_neg, hss, Complex.star_def, Complex.conj_conj]
      linear_combination -hs
    rcases eq_or_ne i (Fin.last k) with rfl | hiL
    · simp only [mud0L hk, mudLL hk, character_first_entry hk, character_last_entry hk, if_true, if_neg h0L, if_neg h0L.symm, hss,
        Complex.star_def]
      ring
    · simp only [mud_col hk d hi0 hiL, if_neg (Ne.symm hi0), if_neg (Ne.symm hiL), if_neg hi0]
      simp
  rcases eq_or_ne j (Fin.last k) with rfl | hjL
  · rw [mul_mud_blk hk d _ _ _ (Or.inr rfl), hP, hP, Hb_apply]
    rcases eq_or_ne i 0 with rfl | hi0
    · simp only [character_first_entry hk, character_last_entry hk, mud0L hk, mudLL hk, if_true, if_neg h0L, if_neg h0L.symm, star_neg, hss, Complex.star_def,
        Complex.conj_conj]
      ring
    rcases eq_or_ne i (Fin.last k) with rfl | hiL
    · simp only [mud0L hk, mudLL hk, if_true, if_neg h0L, if_neg h0L.symm, hss, Complex.star_def]
      linear_combination hs
    · simp only [mud_col hk d hi0 hiL, if_neg (Ne.symm hi0), if_neg (Ne.symm hiL), if_neg hiL]
      simp
  · rw [mul_mud_col hk d _ hj0 hjL, hP, mud_row hk d hj0 hjL, Hb_apply]
    by_cases hij : i = j
    · subst hij; simp [hjL]
    · rw [if_neg (Ne.symm hij), if_neg hij]; simp

/- English proof (translation)
Establish `hs` using `sgd_sq d hd`. Establish `hss` using `star_sgd d`. Establish `h0L` using `zero_ne_last hk`. Establish `hc : ∀ a b : Fin (k + 1), ((mud k d).map (starRingEnd ℂ)) a b = conj (mud k d a b)` using `fun a b => rfl`. Establish `hsc : conj (sgd d) = sgd d` using `hss`.

Use extensionality with `i j`. Break down `eq_or_ne j 0 with rfl | hj0` into its components or cases. Rewrite using `[mul_mud_blk hk d _ _ _ (Or.inl rfl), hc, hc, one_apply]`. Break down `eq_or_ne i 0 with rfl | hi0` into its components or cases. Apply the tactic sequence `simp only [character_first_entry hk, mud0L hk, character_last_entry hk, if_true, map_neg, hsc, Complex.conj_conj]`.

Take the linear combination `-hs`. Break down `eq_or_ne i (Fin.last k) with rfl | hiL` into its components or cases. Apply the tactic sequence `simp only [character_last_entry hk, mudLL hk, character_first_entry hk, if_neg h0L.symm, map_neg, hsc]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [mud_row hk d hi0 hiL, if_neg hi0, if_neg hiL]`.

Simplify using the standard rewrite rules. Break down `eq_or_ne j (Fin.last k) with rfl | hjL` into its components or cases. Rewrite using `[mul_mud_blk hk d _ _ _ (Or.inr rfl), hc, hc, one_apply]`. Break down `eq_or_ne i 0 with rfl | hi0` into its components or cases. Apply the tactic sequence `simp only [character_first_entry hk, mud0L hk, mudLL hk, if_neg h0L, if_neg h0L.symm, map_neg, hsc, Complex.conj_conj]`.

Expand and normalize the polynomial expressions, which then agree. Break down `eq_or_ne i (Fin.last k) with rfl | hiL` into its components or cases. Apply the tactic sequence `simp only [character_last_entry hk, mudLL hk, mud0L hk, if_true, map_neg, hsc]`. Take the linear combination `-hs`. Simplify using `only [mud_row hk d hi0 hiL, if_neg hi0, if_neg hiL]`.

Simplify using the standard rewrite rules. Apply the tactic sequence `rw [mul_mud_col hk d _ hj0 hjL, hc, mud_col hk d hj0 hjL, one_apply] split_ifs <;> simp`.
-/
theorem mud_conj_mul (hk : 1 ≤ k) (d : ℂ) (hd : 1 < ‖d‖) : (mud k d).map (starRingEnd ℂ) * mud k d = 1 := by
  have hs := sgd_sq d hd
  have hss := star_sgd d
  have h0L := zero_ne_last hk
  have hc : ∀ a b : Fin (k + 1), ((mud k d).map (starRingEnd ℂ)) a b = conj (mud k d a b) := fun a b => rfl
  have hsc : conj (sgd d) = sgd d := hss
  ext i j
  rcases eq_or_ne j 0 with rfl | hj0
  · rw [mul_mud_blk hk d _ _ _ (Or.inl rfl), hc, hc, one_apply]
    rcases eq_or_ne i 0 with rfl | hi0
    · simp only [character_first_entry hk, mud0L hk, character_last_entry hk, if_true, map_neg, hsc, Complex.conj_conj]
      linear_combination -hs
    rcases eq_or_ne i (Fin.last k) with rfl | hiL
    · simp only [character_last_entry hk, mudLL hk, character_first_entry hk, if_neg h0L.symm, map_neg, hsc]
      ring
    · simp only [mud_row hk d hi0 hiL, if_neg hi0, if_neg hiL]
      simp
  rcases eq_or_ne j (Fin.last k) with rfl | hjL
  · rw [mul_mud_blk hk d _ _ _ (Or.inr rfl), hc, hc, one_apply]
    rcases eq_or_ne i 0 with rfl | hi0
    · simp only [character_first_entry hk, mud0L hk, mudLL hk, if_neg h0L, if_neg h0L.symm, map_neg, hsc, Complex.conj_conj]
      ring
    rcases eq_or_ne i (Fin.last k) with rfl | hiL
    · simp only [character_last_entry hk, mudLL hk, mud0L hk, if_true, map_neg, hsc]
      linear_combination -hs
    · simp only [mud_row hk d hi0 hiL, if_neg hi0, if_neg hiL]
      simp
  · rw [mul_mud_col hk d _ hj0 hjL, hc, mud_col hk d hj0 hjL, one_apply]
    split_ifs <;> simp

/- English proof (translation)
Unfold `herm`. Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`.
-/
theorem herm_mulVec {n : ℕ} (H A : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℂ) :
    herm H (A *ᵥ u) (A *ᵥ v) = herm (Aᴴ * H * A) u v := by
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

/- English proof (translation)
Unfold `herm`. Simplify using `only [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, starRingEnd_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_smul {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (a b : ℂ) (u v : Fin n → ℂ) :
    herm H (a • u) (b • v) = a * conj b * herm H u v := by
  unfold herm
  simp only [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, starRingEnd_apply]
  ring

/- English proof (translation)
Unfold `herm`. Simplify using `only [dotProduct, Matrix.mulVec, Pi.star_apply]`. Rewrite using `[Finset.sum_eq_single (Fin.last k)]`. Simplify using `[Pi.single_apply, Hb_apply, mudLL hk d]`. Introduce `b _ hb`.

Simplify using `[Pi.single_apply, hb]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem herm_mud_last (hk : 1 ≤ k) (d : ℂ) :
    herm (Hb k) (mud k d *ᵥ Pi.single (Fin.last k) 1) (Pi.single (Fin.last k) 1) = -d := by
  unfold herm
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
  rw [Finset.sum_eq_single (Fin.last k)]
  · simp [Pi.single_apply, Hb_apply, mudLL hk d]
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Use function extensionality and compare the values at `i`. Apply the tactic sequence `by_cases h : r ≤ i.val ∧ i.val ≤ r + k <;> simp [wbE, h]`.
-/
theorem wbE_smul {r : ℕ} (a : ℂ) (v : Fin (k + 1) → ℂ) : wbE k r (a • v) = a • wbE k r v := by
  funext i
  by_cases h : r ≤ i.val ∧ i.val ≤ r + k <;> simp [wbE, h]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [bvec, wI, wbE, Pi.single_apply, Fin.ext_iff, Fin.val_mk]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`.
-/
theorem bvec_wI {r : ℕ} (j : Fin (k + 1)) : bvec (wI k r j) = wbE k r (Pi.single j 1) := by
  funext i
  simp only [bvec, wI, wbE, Pi.single_apply, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | omega

end ReciprocityTheory.ChartRestriction.DS.Mult1.RepsA
