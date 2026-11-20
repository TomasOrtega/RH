import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction

open Matrix
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.TheSec

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.SettingConstruction

variable (k : ℕ)

/- English proof (translation)
Establish `hcs : star ((Real.sqrt t : ℝ) : ℂ) = ((Real.sqrt t : ℝ) : ℂ)` using `Complex.conj_ofReal _`. Establish `hs : ((Real.sqrt t : ℝ) : ℂ) * ((Real.sqrt t : ℝ) : ℂ) = (t : ℂ)`. Rewrite using `[← Complex.ofReal_mul, Real.mul_self_sqrt ht.le]`. Unfold `herm Hb`. Rewrite using `[dotProduct, Finset.sum_eq_single (Fin.last k)]`.

Simplify using `only [Matrix.mulVec_diagonal, Matrix.mulVec_smul, Pi.star_apply, Pi.smul_apply, Pi.single_eq_same, if_pos rfl, smul_eq_mul, mul_one, star_mul', star_one]`. Rewrite using `[hcs]`. Simplify using `only [↓reduceIte]`. Take the linear combination `(-1 : ℂ) * hs`. Introduce `i _ hi`.

Simplify using `[Matrix.mulVec_diagonal, Pi.single_apply, hi]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem herm_last_scaled (t : ℝ) (ht : 0 < t) :
    herm (Hb k) (((Real.sqrt t : ℝ) : ℂ) • Pi.single (Fin.last k) 1)
      (((Real.sqrt t : ℝ) : ℂ) • Pi.single (Fin.last k) 1) = -(t : ℂ) := by
  have hcs : star ((Real.sqrt t : ℝ) : ℂ) = ((Real.sqrt t : ℝ) : ℂ) := Complex.conj_ofReal _
  have hs : ((Real.sqrt t : ℝ) : ℂ) * ((Real.sqrt t : ℝ) : ℂ) = (t : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt ht.le]
  unfold herm Hb
  rw [dotProduct, Finset.sum_eq_single (Fin.last k)]
  · simp only [Matrix.mulVec_diagonal, Matrix.mulVec_smul, Pi.star_apply, Pi.smul_apply,
      Pi.single_eq_same, if_pos rfl, smul_eq_mul, mul_one, star_mul', star_one]
    rw [hcs]
    simp only [↓reduceIte]
    linear_combination (-1 : ℂ) * hs
  · intro i _ hi
    simp [Matrix.mulVec_diagonal, Pi.single_apply, hi]
  · intro h
    exact absurd (Finset.mem_univ _) h

def gA (a : Fin (k + 1) → ℂ) (T : ℝ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  if h : 0 < T ∧ herm (Hb k) a a = -(T : ℂ) then
    Classical.choose (transitive (Hb k) (Hb_herm k) _ a T h.1 (herm_last_scaled k T h.1) h.2)
  else 1

def gB (b : Fin (k + 1) → ℂ) (T' : ℝ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  if h : 0 < T' ∧ herm (Hb k) b b = -(T' : ℂ) then
    Classical.choose (transitive (Hb k) (Hb_herm k) b _ T' h.1 h.2 (herm_last_scaled k T' h.1))
  else 1

/- English proof (translation)
Establish `h : 0 < T ∧ herm (Hb k) a a = -(T : ℂ)` using `⟨hT, ha⟩`. Unfold `gA`. Rewrite using `[dif_pos h]`. Conclude with `Classical.choose_spec (transitive (Hb k) (Hb_herm k) _ a T h.1 (herm_last_scaled k T h.1) h.2)`.
-/
theorem gA_spec {a : Fin (k + 1) → ℂ} {T : ℝ} (hT : 0 < T) (ha : herm (Hb k) a a = -(T : ℂ)) :
    (gA k a T)ᴴ * Hb k * gA k a T = Hb k ∧
      gA k a T *ᵥ (((Real.sqrt T : ℝ) : ℂ) • Pi.single (Fin.last k) 1) = a := by
  have h : 0 < T ∧ herm (Hb k) a a = -(T : ℂ) := ⟨hT, ha⟩
  unfold gA
  rw [dif_pos h]
  exact Classical.choose_spec
    (transitive (Hb k) (Hb_herm k) _ a T h.1 (herm_last_scaled k T h.1) h.2)

/- English proof (translation)
Establish `h : 0 < T' ∧ herm (Hb k) b b = -(T' : ℂ)` using `⟨hT', hb⟩`. Unfold `gB`. Rewrite using `[dif_pos h]`. Conclude with `Classical.choose_spec (transitive (Hb k) (Hb_herm k) b _ T' h.1 h.2 (herm_last_scaled k T' h.1))`.
-/
theorem gB_spec {b : Fin (k + 1) → ℂ} {T' : ℝ} (hT' : 0 < T') (hb : herm (Hb k) b b = -(T' : ℂ)) :
    (gB k b T')ᴴ * Hb k * gB k b T' = Hb k ∧
      gB k b T' *ᵥ b = ((Real.sqrt T' : ℝ) : ℂ) • Pi.single (Fin.last k) 1 := by
  have h : 0 < T' ∧ herm (Hb k) b b = -(T' : ℂ) := ⟨hT', hb⟩
  unfold gB
  rw [dif_pos h]
  exact Classical.choose_spec
    (transitive (Hb k) (Hb_herm k) b _ T' h.1 h.2 (herm_last_scaled k T' h.1))

def wZ (T T' : ℝ) (ζ : ℂ) : ℂ := (-((Real.sqrt T * Real.sqrt T' : ℝ) : ℂ)⁻¹) * ζ

def sZ (T T' : ℝ) (ζ : ℂ) : ℂ := ((Real.sqrt (Complex.normSq ζ / (T * T') - 1) : ℝ) : ℂ)

def theSecB (a b : Fin (k + 1) → ℂ) (T T' : ℝ) (ζ : ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  gA k a T * nu k (wZ T T' ζ) (sZ T T' ζ) * gB k b T'

def theSection (r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  theSecB k (wbPart k r z) (wbPart k r z') (Tz k r z) (Tz k r z')

/- English proof (translation)
Unfold `herm`. Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]`.
-/
private theorem herm_mulVec_of_conjTranspose_mul_eq (H g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hg : gᴴ * H * g = H)
    (x y : Fin (k + 1) → ℂ) : herm H (g *ᵥ x) (g *ᵥ y) = herm H x y := by
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]

/- English proof (translation)
Rewrite using `[Matrix.conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem mul_conjTranspose_form_preserving (H A B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hA : Aᴴ * H * A = H)
    (hB : Bᴴ * H * B = H) : (A * B)ᴴ * H * (A * B) = H := by
  rw [Matrix.conjTranspose_mul]
  calc Bᴴ * Aᴴ * H * (A * B) = Bᴴ * (Aᴴ * H * A) * B := by simp only [Matrix.mul_assoc]
    _ = H := by rw [hA, hB]

/- English proof (translation)
Establish `h0L : (0 : Fin (k + 1)) ≠ Fin.last k`. Introduce `h`. Establish `h'` using `congrArg Fin.val h`. Simplify using `only [Fin.val_zero, Fin.val_last] at h'`. Use linear arithmetic over natural numbers and integers.

Unfold `nu`. Simplify using `only [Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]`. Distinguish the cases in `hm0 : m = 0`. Substitute `hm0` using the available equality. Distinguish the cases in `hl0 : l = 0`.

Substitute `hl0` using the available equality. Simplify using `[h0L]`. Distinguish the cases in `hlL : l = Fin.last k`. Substitute `hlL` using the available equality. Simplify using `[h0L, h0L.symm]`.

Simplify using `[hl0, hlL, h0L]`. Distinguish the cases in `hmL : m = Fin.last k`. Substitute `hmL` using the available equality. Distinguish the cases in `hl0 : l = 0`. Substitute `hl0` using the available equality.

Simplify using `[h0L, h0L.symm]`. Distinguish the cases in `hlL : l = Fin.last k`. Substitute `hlL` using the available equality. Simplify using `[h0L.symm]`. Simplify using `[hl0, hlL, h0L.symm]`.

Simplify using `[hm0, hmL]`.
-/
private theorem nu_apply' (hk : 1 ≤ k) (w s : ℂ) (l m : Fin (k + 1)) :
    nu k w s l m =
      if m = 0 then (if l = 0 then star w else if l = Fin.last k then s else 0)
      else if m = Fin.last k then (if l = 0 then s else if l = Fin.last k then w else 0)
      else (if l = m then 1 else 0) := by
  have h0L : (0 : Fin (k + 1)) ≠ Fin.last k := by
    intro h
    have h' := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at h'
    omega
  unfold nu
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply, Pi.add_apply,
    Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  by_cases hm0 : m = 0
  · subst hm0
    by_cases hl0 : l = 0
    · subst hl0
      simp [h0L]
    · by_cases hlL : l = Fin.last k
      · subst hlL
        simp [h0L, h0L.symm]
      · simp [hl0, hlL, h0L]
  · by_cases hmL : m = Fin.last k
    · subst hmL
      by_cases hl0 : l = 0
      · subst hl0
        simp [h0L, h0L.symm]
      · by_cases hlL : l = Fin.last k
        · subst hlL
          simp [h0L.symm]
        · simp [hl0, hlL, h0L.symm]
    · simp [hm0, hmL]

/- English proof (translation)
Establish `h0L : (0 : Fin (k + 1)) ≠ Fin.last k`. Introduce `h`. Establish `h'` using `congrArg Fin.val h`. Simplify using `only [Fin.val_zero, Fin.val_last] at h'`. Use linear arithmetic over natural numbers and integers.

Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [Hb, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply, nu_apply' k hk]`. Distinguish the cases in `hi0 : i = 0`. Substitute `hi0` using the available equality.

Rewrite using `[Fintype.sum_eq_add 0 (Fin.last k) h0L]`. Distinguish the cases in `hj0 : j = 0`. Substitute `hj0` using the available equality. Simplify using `only [h0L, h0L.symm, hs, star_star, eq_self_iff_true, if_true, if_false, ↓reduceIte, mul_one, one_mul, mul_neg, neg_mul]`. Take the linear combination `hws`.

Distinguish the cases in `hjL : j = Fin.last k`. Substitute `hjL` using the available equality. Simplify using `only [h0L, h0L.symm, hs, star_star, eq_self_iff_true, if_true, if_false, ↓reduceIte, mul_one, one_mul, mul_neg, neg_mul]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[h0L, h0L.symm, hj0, hjL, Ne.symm hj0, Ne.symm hjL]`.

Introduce `x hx`. Simplify using `[hx.1, hx.2]`. Distinguish the cases in `hiL : i = Fin.last k`. Substitute `hiL` using the available equality. Rewrite using `[Fintype.sum_eq_add 0 (Fin.last k) h0L]`.

Distinguish the cases in `hj0 : j = 0`. Substitute `hj0` using the available equality. Simplify using `only [h0L, h0L.symm, hs, star_star, eq_self_iff_true, if_true, if_false, ↓reduceIte, mul_one, one_mul, mul_neg, neg_mul]`. Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `hjL : j = Fin.last k`.

Substitute `hjL` using the available equality. Simplify using `only [h0L, h0L.symm, hs, star_star, eq_self_iff_true, if_true, if_false, ↓reduceIte, mul_one, one_mul, mul_neg, neg_mul]`. Take the linear combination `(-1 : ℂ) * hws`. Simplify using `[h0L, h0L.symm, hj0, hjL, Ne.symm hj0, Ne.symm hjL]`. Introduce `x hx`.

Simplify using `[hx.1, hx.2]`. Rewrite using `[Fintype.sum_eq_single i]`. Simplify using `only [hi0, hiL, if_false, if_true, ↓reduceIte, eq_self_iff_true, star_one, one_mul]`. Distinguish the cases in `hj0 : j = 0`. Substitute `hj0` using the available equality.

Simplify using `[hi0, hiL]`. Distinguish the cases in `hjL : j = Fin.last k`. Substitute `hjL` using the available equality. Simplify using `[hi0, hiL]`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using `[hi0, hiL]`. Simplify using `[hj0, hjL, hij, Ne.symm hij]`. Introduce `x hx`. Simplify using `[hi0, hiL, hx]`.
-/
private theorem nu_conjTranspose_mul_Hb_mul_nu (hk : 1 ≤ k) (w s : ℂ) (hs : star s = s)
    (hws : star w * w - s * s = 1) : (nu k w s)ᴴ * Hb k * nu k w s = Hb k := by
  have h0L : (0 : Fin (k + 1)) ≠ Fin.last k := by
    intro h
    have h' := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at h'
    omega
  ext i j
  rw [Matrix.mul_apply]
  simp only [Hb, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
    nu_apply' k hk]
  by_cases hi0 : i = 0
  · subst hi0
    rw [Fintype.sum_eq_add 0 (Fin.last k) h0L]
    · by_cases hj0 : j = 0
      · subst hj0
        simp only [h0L, h0L.symm, hs, star_star, eq_self_iff_true, if_true, if_false,
          ↓reduceIte, mul_one, one_mul, mul_neg, neg_mul]
        linear_combination hws
      · by_cases hjL : j = Fin.last k
        · subst hjL
          simp only [h0L, h0L.symm, hs, star_star, eq_self_iff_true, if_true, if_false,
            ↓reduceIte, mul_one, one_mul, mul_neg, neg_mul]
          ring
        · simp [h0L, h0L.symm, hj0, hjL, Ne.symm hj0, Ne.symm hjL]
    · intro x hx
      simp [hx.1, hx.2]
  · by_cases hiL : i = Fin.last k
    · subst hiL
      rw [Fintype.sum_eq_add 0 (Fin.last k) h0L]
      · by_cases hj0 : j = 0
        · subst hj0
          simp only [h0L, h0L.symm, hs, star_star, eq_self_iff_true, if_true, if_false,
            ↓reduceIte, mul_one, one_mul, mul_neg, neg_mul]
          ring
        · by_cases hjL : j = Fin.last k
          · subst hjL
            simp only [h0L, h0L.symm, hs, star_star, eq_self_iff_true, if_true, if_false,
              ↓reduceIte, mul_one, one_mul, mul_neg, neg_mul]
            linear_combination (-1 : ℂ) * hws
          · simp [h0L, h0L.symm, hj0, hjL, Ne.symm hj0, Ne.symm hjL]
      · intro x hx
        simp [hx.1, hx.2]
    · rw [Fintype.sum_eq_single i]
      · simp only [hi0, hiL, if_false, if_true, ↓reduceIte, eq_self_iff_true, star_one, one_mul]
        by_cases hj0 : j = 0
        · subst hj0
          simp [hi0, hiL]
        · by_cases hjL : j = Fin.last k
          · subst hjL
            simp [hi0, hiL]
          · by_cases hij : i = j
            · subst hij
              simp [hi0, hiL]
            · simp [hj0, hjL, hij, Ne.symm hij]
      · intro x hx
        simp [hi0, hiL, hx]

/- English proof (translation)
Establish `h0L : (0 : Fin (k + 1)) ≠ Fin.last k`. Introduce `h`. Establish `h'` using `congrArg Fin.val h`. Simplify using `only [Fin.val_zero, Fin.val_last] at h'`. Use linear arithmetic over natural numbers and integers.

Use function extensionality and compare the values at `l`. Establish `e : (nu k w s *ᵥ Pi.single (Fin.last k) 1) l = nu k w s l (Fin.last k)`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`. Rewrite using `[e, nu_apply' k hk]`. Distinguish the cases in `hl0 : l = 0`.

Substitute `hl0` using the available equality. Simplify using `[h0L.symm, h0L]`. Distinguish the cases in `hlL : l = Fin.last k`. Substitute `hlL` using the available equality. Simplify using `[h0L.symm]`.

Simplify using `[hl0, hlL, h0L.symm]`.
-/
private theorem nu_mulVec_single_last (hk : 1 ≤ k) (w s : ℂ) :
    nu k w s *ᵥ Pi.single (Fin.last k) 1 = s • Pi.single 0 1 + w • Pi.single (Fin.last k) 1 := by
  have h0L : (0 : Fin (k + 1)) ≠ Fin.last k := by
    intro h
    have h' := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at h'
    omega
  funext l
  have e : (nu k w s *ᵥ Pi.single (Fin.last k) 1) l = nu k w s l (Fin.last k) := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [e, nu_apply' k hk]
  by_cases hl0 : l = 0
  · subst hl0
    simp [h0L.symm, h0L]
  · by_cases hlL : l = Fin.last k
    · subst hlL
      simp [h0L.symm]
    · simp [hl0, hlL, h0L.symm]

/- English proof (translation)
Establish `hTT : 0 < T * T'` using `mul_pos hT hT'`. Set `S : Set ℂ` to `{ζ : ℂ | T * T' < Complex.normSq ζ}`. Establish `hw : ContDiff ℝ ∞ (fun ζ : ℂ => wZ T T' ζ)`. Unfold `wZ`. Conclude with `contDiff_const.mul contDiff_id`.

Establish `hws : ContDiff ℝ ∞ (fun ζ : ℂ => star (wZ T T' ζ))` using `Complex.conjCLE.contDiff.comp hw`. Establish `hsz : ContDiffOn ℝ ∞ (fun ζ : ℂ => sZ T T' ζ) S`. Unfold `sZ`. Establish `hn2 : ContDiff ℝ ∞ (fun ζ : ℂ => Complex.normSq ζ)`. Establish `e : (fun ζ : ℂ => Complex.normSq ζ) = fun ζ => ‖ζ‖ ^ 2`.

Use function extensionality and compare the values at `ζ`. Conclude with `Complex.normSq_eq_norm_sq ζ`. Rewrite using `[e]`. Conclude with `contDiff_norm_sq ℝ`. Establish `hn : ContDiff ℝ ∞ (fun ζ : ℂ => Complex.normSq ζ / (T * T') - 1)` using `(hn2.div_const _).sub contDiff_const`.

Establish `hsq : ContDiffOn ℝ ∞ (fun ζ : ℂ => Real.sqrt (Complex.normSq ζ / (T * T') - 1)) S`. Use `hn.contDiffOn.sqrt ?_` and prove the remaining obligations. Introduce `ζ hζ`. Establish `h1 : 1 < Complex.normSq ζ / (T * T')`. Rewrite using `[lt_div_iff₀ hTT, one_mul]`.

Conclude with `hζ`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `Complex.ofRealCLM.contDiff.comp_contDiffOn hsq`. Establish `hnu : ∀ y x, ContDiffOn ℝ ∞ (fun ζ => nu k (wZ T T' ζ) (sZ T T' ζ) y x) S`. Introduce `y x`.

Simplify using `only [nu_apply' k hk]`. Use `split_ifs`. Apply the tactic sequence `all_goals first`. Consider the case `exact contDiffOn_const`. Consider the case `exact hws.contDiffOn`.

Consider the case `exact hw.contDiffOn`. Consider the case `exact hsz`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `i j`. Simplify using `only [theSecB, Matrix.mul_apply]`.

Apply `ContDiffOn.sum` to reduce the goal to its premises. Introduce `x _`. Apply `ContDiffOn.mul _ contDiffOn_const` to reduce the goal to its premises. Apply `ContDiffOn.sum` to reduce the goal to its premises. Introduce `y _`.

Conclude with `contDiffOn_const.mul (hnu y x)`. Introduce `ζ hζ`. Establish `h0L : (0 : Fin (k + 1)) ≠ Fin.last k`. Introduce `h`. Establish `h'` using `congrArg Fin.val h`.

Simplify using `only [Fin.val_zero, Fin.val_last] at h'`. Use linear arithmetic over natural numbers and integers. Establish `hsr : star (sZ T T' ζ) = sZ T T' ζ`. Unfold `sZ`. Conclude with `Complex.conj_ofReal _`.

Establish `hkey : star (wZ T T' ζ) * wZ T T' ζ - sZ T T' ζ * sZ T T' ζ = 1`. Establish `hx : 0 ≤ Complex.normSq ζ / (T * T') - 1`. Establish `h1 : 1 < Complex.normSq ζ / (T * T')`. Rewrite using `[lt_div_iff₀ hTT, one_mul]`. Conclude with `hζ`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1 : Complex.normSq (wZ T T' ζ) = Complex.normSq ζ / (T * T')`. Unfold `wZ`. Rewrite using `[Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_inv, Complex.normSq_ofReal]`. Rewrite using `[show Real.sqrt T * Real.sqrt T' * (Real.sqrt T * Real.sqrt T') = (Real.sqrt T * Real.sqrt T) * (Real.sqrt T' * Real.sqrt T') by ring, Real.mul_self_sqrt hT.le, Real.mul_self_sqrt hT'.le, div_eq_inv_mul]`.

Establish `h2 : star (wZ T T' ζ) * wZ T T' ζ = (Complex.normSq (wZ T T' ζ) : ℂ)` using `Complex.normSq_eq_conj_mul_self.symm`. Establish `h3 : sZ T T' ζ * sZ T T' ζ = ((Complex.normSq ζ / (T * T') - 1 : ℝ) : ℂ)`. Unfold `sZ`. Rewrite using `[← Complex.ofReal_mul, Real.mul_self_sqrt hx]`. Rewrite using `[h2, h3, h1]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hA` using `gA_spec k hT ha`. Establish `hB` using `gB_spec k hT' hb`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Unfold `theSecB`. Conclude with `mul_conjTranspose_form_preserving k _ _ _ (mul_conjTranspose_form_preserving k _ _ _ hA.1 (nu_conjTranspose_mul_Hb_mul_nu k hk _ _ hsr hkey)) hB.1`. Unfold `theSecB`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hB.2]`. Use `conv_lhs => arg 3`.

Rewrite using `[← hA.2]`. Rewrite using `[herm_mulVec_of_conjTranspose_mul_eq k _ _ hA.1, Matrix.mulVec_smul, nu_mulVec_single_last k hk]`. Establish `hcs : star ((Real.sqrt T : ℝ) : ℂ) = ((Real.sqrt T : ℝ) : ℂ)` using `Complex.conj_ofReal _`. Establish `hT0 : ((Real.sqrt T : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast (Real.sqrt_pos.2 hT).ne'`. Establish `hT0' : ((Real.sqrt T' : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast (Real.sqrt_pos.2 hT').ne'`.

Unfold `herm Hb`. Rewrite using `[dotProduct, Finset.sum_eq_single (Fin.last k)]`. Simplify using `only [Matrix.mulVec_diagonal, Pi.star_apply, Pi.smul_apply, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne h0L.symm, smul_eq_mul, mul_one, mul_zero, zero_add, star_mul', star_one, eq_self_iff_true, if_true, ↓reduceIte]`. Rewrite using `[hcs]`. Unfold `wZ`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Introduce `i _ hi`. Simplify using `[Pi.single_apply, hi]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem theSecB_core (hk : 1 ≤ k) (a b : Fin (k + 1) → ℂ) (T T' : ℝ) (hT : 0 < T) (hT' : 0 < T')
    (ha : herm (Hb k) a a = -(T : ℂ)) (hb : herm (Hb k) b b = -(T' : ℂ)) :
    (∀ i j, ContDiffOn ℝ ∞ (fun ζ => theSecB k a b T T' ζ i j) {ζ : ℂ | T * T' < Complex.normSq ζ}) ∧
      ∀ ζ : ℂ, T * T' < Complex.normSq ζ →
        (theSecB k a b T T' ζ)ᴴ * Hb k * theSecB k a b T T' ζ = Hb k ∧
          herm (Hb k) (theSecB k a b T T' ζ *ᵥ b) a = ζ := by
  have hTT : 0 < T * T' := mul_pos hT hT'
  let S : Set ℂ := {ζ : ℂ | T * T' < Complex.normSq ζ}
  have hw : ContDiff ℝ ∞ (fun ζ : ℂ => wZ T T' ζ) := by
    unfold wZ
    exact contDiff_const.mul contDiff_id
  have hws : ContDiff ℝ ∞ (fun ζ : ℂ => star (wZ T T' ζ)) := Complex.conjCLE.contDiff.comp hw
  have hsz : ContDiffOn ℝ ∞ (fun ζ : ℂ => sZ T T' ζ) S := by
    unfold sZ
    have hn2 : ContDiff ℝ ∞ (fun ζ : ℂ => Complex.normSq ζ) := by
      have e : (fun ζ : ℂ => Complex.normSq ζ) = fun ζ => ‖ζ‖ ^ 2 := by
        funext ζ
        exact Complex.normSq_eq_norm_sq ζ
      rw [e]
      exact contDiff_norm_sq ℝ
    have hn : ContDiff ℝ ∞ (fun ζ : ℂ => Complex.normSq ζ / (T * T') - 1) :=
      (hn2.div_const _).sub contDiff_const
    have hsq : ContDiffOn ℝ ∞ (fun ζ : ℂ => Real.sqrt (Complex.normSq ζ / (T * T') - 1)) S := by
      refine hn.contDiffOn.sqrt ?_
      intro ζ hζ
      have h1 : 1 < Complex.normSq ζ / (T * T') := by
        rw [lt_div_iff₀ hTT, one_mul]
        exact hζ
      linarith
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn hsq
  have hnu : ∀ y x, ContDiffOn ℝ ∞ (fun ζ => nu k (wZ T T' ζ) (sZ T T' ζ) y x) S := by
    intro y x
    simp only [nu_apply' k hk]
    split_ifs
    all_goals first
      | exact contDiffOn_const
      | exact hws.contDiffOn
      | exact hw.contDiffOn
      | exact hsz
  refine ⟨?_, ?_⟩
  · intro i j
    simp only [theSecB, Matrix.mul_apply]
    apply ContDiffOn.sum
    intro x _
    apply ContDiffOn.mul _ contDiffOn_const
    apply ContDiffOn.sum
    intro y _
    exact contDiffOn_const.mul (hnu y x)
  · intro ζ hζ
    have h0L : (0 : Fin (k + 1)) ≠ Fin.last k := by
      intro h
      have h' := congrArg Fin.val h
      simp only [Fin.val_zero, Fin.val_last] at h'
      omega
    have hsr : star (sZ T T' ζ) = sZ T T' ζ := by
      unfold sZ
      exact Complex.conj_ofReal _
    have hkey : star (wZ T T' ζ) * wZ T T' ζ - sZ T T' ζ * sZ T T' ζ = 1 := by
      have hx : 0 ≤ Complex.normSq ζ / (T * T') - 1 := by
        have h1 : 1 < Complex.normSq ζ / (T * T') := by
          rw [lt_div_iff₀ hTT, one_mul]
          exact hζ
        linarith
      have h1 : Complex.normSq (wZ T T' ζ) = Complex.normSq ζ / (T * T') := by
        unfold wZ
        rw [Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_inv, Complex.normSq_ofReal]
        rw [show Real.sqrt T * Real.sqrt T' * (Real.sqrt T * Real.sqrt T') =
            (Real.sqrt T * Real.sqrt T) * (Real.sqrt T' * Real.sqrt T') by ring,
          Real.mul_self_sqrt hT.le, Real.mul_self_sqrt hT'.le, div_eq_inv_mul]
      have h2 : star (wZ T T' ζ) * wZ T T' ζ = (Complex.normSq (wZ T T' ζ) : ℂ) :=
        Complex.normSq_eq_conj_mul_self.symm
      have h3 : sZ T T' ζ * sZ T T' ζ = ((Complex.normSq ζ / (T * T') - 1 : ℝ) : ℂ) := by
        unfold sZ
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt hx]
      rw [h2, h3, h1]
      push_cast
      ring
    have hA := gA_spec k hT ha
    have hB := gB_spec k hT' hb
    refine ⟨?_, ?_⟩
    · unfold theSecB
      exact mul_conjTranspose_form_preserving k _ _ _ (mul_conjTranspose_form_preserving k _ _ _ hA.1 (nu_conjTranspose_mul_Hb_mul_nu k hk _ _ hsr hkey)) hB.1
    · unfold theSecB
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hB.2]
      conv_lhs => arg 3; rw [← hA.2]
      rw [herm_mulVec_of_conjTranspose_mul_eq k _ _ hA.1, Matrix.mulVec_smul, nu_mulVec_single_last k hk]
      have hcs : star ((Real.sqrt T : ℝ) : ℂ) = ((Real.sqrt T : ℝ) : ℂ) := Complex.conj_ofReal _
      have hT0 : ((Real.sqrt T : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hT).ne'
      have hT0' : ((Real.sqrt T' : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hT').ne'
      unfold herm Hb
      rw [dotProduct, Finset.sum_eq_single (Fin.last k)]
      · simp only [Matrix.mulVec_diagonal, Pi.star_apply, Pi.smul_apply, Pi.add_apply,
          Pi.single_eq_same, Pi.single_eq_of_ne h0L.symm, smul_eq_mul, mul_one, mul_zero,
          zero_add, star_mul', star_one, eq_self_iff_true, if_true, ↓reduceIte]
        rw [hcs]
        unfold wZ
        push_cast
        field_simp
      · intro i _ hi
        simp [Pi.single_apply, hi]
      · intro h
        exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Establish `hin : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k → (Hpk k r *ᵥ z) i = (if i.val = r + k then -1 else 1) * z i`. Introduce `i h1 h2`. Simplify using `only [Matrix.mulVec, dotProduct]`. Rewrite using `[Finset.sum_eq_single i]`. Simplify using `only [Hpk]`.

Rewrite using `[if_neg (by omega), if_neg (by omega), if_pos (by simp [h1, h2])]`. Introduce `j _ hji`. Distinguish the cases in `hj : j.val < r ∨ r + k < j.val`. Rewrite using `[hz j hj, mul_zero]`. Simplify using `only [Hpk]`.

Rewrite using `[if_neg (by omega), if_neg (by omega), if_neg (by`. Introduce and unpack `⟨_, _, h⟩`. Conclude with `hji h.symm), zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.

Unfold `herm`. Simplify using `only [dotProduct, Pi.star_apply]`. Use `Fintype.sum_of_injective (wI k r) ?_ _ _ ?_ ?_` and prove the remaining obligations. Introduce `a b h`. Simplify using `only [wI, Fin.mk.injEq] at h`.

Conclude with `Fin.ext (by omega)`. Introduce `i hi`. Establish `hout : i.val < r ∨ r + k < i.val`. Assume the negation of the conclusion as `hc`. Apply `hi` to reduce the goal to its premises.

Use `⟨⟨i.val - r, by omega⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [wI]`. Conclude with `Fin.ext (by simp only; omega)`. Rewrite using `[hz i hout, star_zero, zero_mul]`. Introduce `j`.

Establish `hj` using `j.isLt`. Establish `h1 : r ≤ (wI k r j).val` using `by simp [wI]`. Establish `h2 : (wI k r j).val ≤ r + k` using `by simp [wI]; omega`. Rewrite using `[hin _ h1 h2]`. Unfold `Hb`.

Rewrite using `[Matrix.mulVec_diagonal]`. Establish `hc : (j = Fin.last k) ↔ (wI k r j).val = r + k`. Simplify using `[wI, Fin.ext_iff]`. Simplify using `only [wbPart]`. Distinguish the cases in `hjl : j = Fin.last k`.

Rewrite using `[if_pos hjl, if_pos (hc.1 hjl)]`. Rewrite using `[if_neg hjl, if_neg (fun h => hjl (hc.2 h))]`.
-/
private theorem herm_Hb_wbPart_eq_herm_Hpk_of_inWb (r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) :
    herm (Hb k) (wbPart k r z) (wbPart k r z) = herm (Hpk k r) z z := by
  have hin : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k →
      (Hpk k r *ᵥ z) i = (if i.val = r + k then -1 else 1) * z i := by
    intro i h1 h2
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single i]
    · simp only [Hpk]
      rw [if_neg (by omega), if_neg (by omega), if_pos (by simp [h1, h2])]
    · intro j _ hji
      by_cases hj : j.val < r ∨ r + k < j.val
      · rw [hz j hj, mul_zero]
      · simp only [Hpk]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by
          rintro ⟨_, _, h⟩
          exact hji h.symm), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  unfold herm
  simp only [dotProduct, Pi.star_apply]
  refine Fintype.sum_of_injective (wI k r) ?_ _ _ ?_ ?_
  · intro a b h
    simp only [wI, Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  · intro i hi
    have hout : i.val < r ∨ r + k < i.val := by
      by_contra hc
      apply hi
      refine ⟨⟨i.val - r, by omega⟩, ?_⟩
      simp only [wI]
      exact Fin.ext (by simp only; omega)
    rw [hz i hout, star_zero, zero_mul]
  · intro j
    have hj := j.isLt
    have h1 : r ≤ (wI k r j).val := by simp [wI]
    have h2 : (wI k r j).val ≤ r + k := by simp [wI]; omega
    rw [hin _ h1 h2]
    unfold Hb
    rw [Matrix.mulVec_diagonal]
    have hc : (j = Fin.last k) ↔ (wI k r j).val = r + k := by
      simp [wI, Fin.ext_iff]
    simp only [wbPart]
    by_cases hjl : j = Fin.last k
    · rw [if_pos hjl, if_pos (hc.1 hjl)]
    · rw [if_neg hjl, if_neg (fun h => hjl (hc.2 h))]

/- English proof (translation)
Establish `hreal : ∀ x : Fin (k + 1) → ℂ, (herm (Hb k) x x).im = 0`. Introduce `x`. Unfold `herm Hb`. Rewrite using `[dotProduct, Complex.im_sum]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `j _`. Rewrite using `[Matrix.mulVec_diagonal]`. Apply the tactic sequence `split_ifs <;> simp [Complex.mul_im] <;> (try ring)`. Establish `hrel : ∀ v : Fin (2 * r + k + 1) → ℂ, inWb k r v → herm (Hb k) (wbPart k r v) (wbPart k r v) = -(Tz k r v : ℂ)`. Introduce `v hv`.

Establish `e` using `herm_Hb_wbPart_eq_herm_Hpk_of_inWb k r v hv`. Unfold `Tz`. Rewrite using `[← e]`. Apply the tactic sequence `apply Complex.ext <;> simp [hreal]`. Conclude with `theSecB_core k hk _ _ _ _ hT hT' (hrel z hz) (hrel z' hz')`.
-/
theorem theSection_isSection (r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (hk : 1 ≤ k) (hz : inWb k r z)
    (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') :
    IsSection k r z z' (theSection k r z z') := by
  have hreal : ∀ x : Fin (k + 1) → ℂ, (herm (Hb k) x x).im = 0 := by
    intro x
    unfold herm Hb
    rw [dotProduct, Complex.im_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [Matrix.mulVec_diagonal]
    split_ifs <;> simp [Complex.mul_im] <;> (try ring)
  have hrel : ∀ v : Fin (2 * r + k + 1) → ℂ, inWb k r v →
      herm (Hb k) (wbPart k r v) (wbPart k r v) = -(Tz k r v : ℂ) := by
    intro v hv
    have e := herm_Hb_wbPart_eq_herm_Hpk_of_inWb k r v hv
    unfold Tz
    rw [← e]
    apply Complex.ext <;> simp [hreal]
  exact theSecB_core k hk _ _ _ _ hT hT' (hrel z hz) (hrel z' hz')

end Formalism.FourierDecayAlt.P.TheSec
