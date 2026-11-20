import ReciprocityTheory.SemistableReduction.SemiDegH

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

def hypG {K : Type} [Field K] {r : ℕ} (j p : Fin r) : Matrix (Fin r) (Fin r) K :=
  Matrix.of fun a b => (if a = j ∧ b = p then 1 else 0) + (if a = p ∧ b = j then 1 else 0)

def hypForm {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (j p : Fin r) :
    HermForm K r where
  c := S.c
  c_invol := S.c_invol
  c_emb := S.c_emb
  G := hypG j p
  G_herm a b := by
    simp only [hypG, Matrix.of_apply, map_add, apply_ite S.c, map_one, map_zero]
    rw [add_comm]
    congr 1 <;> simp only [and_comm]

/- English proof (translation)
Rewrite using `[HermForm.h]`. Establish `e : ∀ a, ∑ b, (hypForm S j p).c (x a) * (hypForm S j p).G a b * y b = (if a = j then S.c (x a) * y p else 0) + (if a = p then S.c (x a) * y j else 0)`. Introduce `a`. Simplify using `only [hypForm, hypG, Matrix.of_apply, mul_add, add_mul, Finset.sum_add_distrib]`. Use `congr 1`.

Apply the tactic sequence `by_cases ha : a = j <;> simp [ha]`. Apply the tactic sequence `by_cases ha : a = p <;> simp [ha]`. Rewrite using `[Finset.sum_congr rfl fun a _ => e a]`. Simplify using `[Finset.sum_add_distrib]`.
-/
theorem hypForm_h {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (j p : Fin r)
    (x y : Fin r → K) : (hypForm S j p).h x y = S.c (x j) * y p + S.c (x p) * y j := by
  rw [HermForm.h]
  have e : ∀ a, ∑ b, (hypForm S j p).c (x a) * (hypForm S j p).G a b * y b =
      (if a = j then S.c (x a) * y p else 0) + (if a = p then S.c (x a) * y j else 0) := by
    intro a
    simp only [hypForm, hypG, Matrix.of_apply, mul_add, add_mul, Finset.sum_add_distrib]
    congr 1
    · by_cases ha : a = j <;> simp [ha]
    · by_cases ha : a = p <;> simp [ha]
  rw [Finset.sum_congr rfl fun a _ => e a]
  simp [Finset.sum_add_distrib]

/- English proof (translation)
The claim follows from `|((Algebra.norm ℚ (-z) : ℚ) : ℝ)| = |((Algebra.norm ℚ z : ℚ) : ℝ)| := by rw [neg_eq_neg_one_mul, map_mul, Rat.cast_mul, abs_mul] have h1 : (-1 : K) = algebraMap ℚ K (-1) := by simp rw [h1, Algebra.norm_algebraMap] simp`.
-/
theorem abs_norm_neg {K : Type} [Field K] [NumberField K] (z : K) :
    |((Algebra.norm ℚ (-z) : ℚ) : ℝ)| = |((Algebra.norm ℚ z : ℚ) : ℝ)| := by
  rw [neg_eq_neg_one_mul, map_mul, Rat.cast_mul, abs_mul]
  have h1 : (-1 : K) = algebraMap ℚ K (-1) := by simp
  rw [h1, Algebra.norm_algebraMap]
  simp

/- English proof (translation)
Establish `hjp' : j ≠ p` using `fun h => by rw [h] at hjp; omega`. Establish `hx0p : x0 p = 0` using `hj x0 hx0 p (Ne.symm hjp')`. Establish `hyj : y j = 0` using `hp y hy j hjp'`. Use `set n : ℝ := (Fintype.card (K →+* ℂ) : ℝ)`. Establish `e0` using `h0`.

Rewrite `e0` using `[latDeg_single δ Gj j x0 (hj x0 hx0)]`. Simplify using `only [hδj] at e0`. Rewrite `e0` using `[sum_log_single (x0 j) hx0j d hd]`. Rewrite using `[latDeg_single δ Gp p y (hp y hy)]`. Simplify using `only [hδp]`.

Rewrite using `[sum_log_single (y p) hyp d⁻¹ (inv_pos.2 hd), Real.log_inv]`. Use `set A : ℝ := (spanIdx Gj ![x0] : ℝ)`. Use `set B : ℝ := (spanIdx Gp ![y] : ℝ)`. Use `set X : ℝ := |((Algebra.norm ℚ (x0 j) : ℚ) : ℝ)|`. Use `set Y : ℝ := |((Algebra.norm ℚ (y p) : ℚ) : ℝ)|`.

Establish `hA : 1 ≤ A`. Use `spanIdx_ne_zero Gj ![x0] hGj (kBasisIn_single j Gj hj x0 hx0 hx0j)` as an intermediate fact. Conclude with `Nat.one_le_cast.2 (Nat.one_le_iff_ne_zero.2 this)`. Establish `hB : 1 ≤ B`. Use `spanIdx_ne_zero Gp ![y] hGp (kBasisIn_single p Gp hp y hy hyp)` as an intermediate fact.

Conclude with `Nat.one_le_cast.2 (Nat.one_le_iff_ne_zero.2 this)`. Establish `hX : 0 < X`. Apply `abs_pos.2` to reduce the goal to its premises. Conclude with `(Algebra.norm_ne_zero_iff).2 hx0j` after adjusting the coercions. Establish `hY : 0 < Y`.

Apply `abs_pos.2` to reduce the goal to its premises. Conclude with `(Algebra.norm_ne_zero_iff).2 hyp` after adjusting the coercions. Establish `key : A * B ≤ X * Y` using `by set T := Gj ⊔ Gp`. Establish `hT : T.FG` using `hGj.sup hGp`. Establish `hbT : IsKBasisIn T ![x0, y]`.

Use `⟨fun i => ?_, ?_, ?_⟩` and prove the remaining obligations. Use `fin_cases i`. Conclude with `Submodule.mem_sup_left hx0`. Conclude with `Submodule.mem_sup_right hy`. Rewrite using `[LinearIndependent.pair_iff]`.

Introduce `s t hst`. Establish `h1` using `congr_fun hst j`. Establish `h2` using `congr_fun hst p`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hx0p, hyj, mul_zero, add_zero, zero_add] at h1 h2`. Conclude with `⟨(mul_eq_zero.1 h1).resolve_right hx0j, (mul_eq_zero.1 h2).resolve_right hyp⟩`.

Introduce `z hz`. Take `⟨z1, hz1, z2, hz2, rfl⟩` from `Submodule.mem_sup.1 hz`. Rewrite using `[Matrix.range_cons_cons_empty]`. Establish `e1 : z1 = (z1 j / x0 j) • x0`. Use function extensionality and compare the values at `a`.

Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Distinguish the cases in `ha : a = j`. Substitute `ha` using the available equality. Clear the denominators using the available nonvanishing facts. Rewrite using `[hj z1 hz1 a ha, hj x0 hx0 a ha, mul_zero]`.

Establish `e2 : z2 = (z2 p / y p) • y`. Use function extensionality and compare the values at `a`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Distinguish the cases in `ha : a = p`. Substitute `ha` using the available equality.

Clear the denominators using the available nonvanishing facts. Rewrite using `[hp z2 hz2 a ha, hp y hy a ha, mul_zero]`. Rewrite using `[e1, e2]`. Conclude with `Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))) (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))`. Establish `hint : IsIntegralOn (hypForm S j p) T`.

Introduce `z hz w hw`. Take `⟨z1, hz1, z2, hz2, rfl⟩` from `Submodule.mem_sup.1 hz`. Take `⟨w1, hw1, w2, hw2, rfl⟩` from `Submodule.mem_sup.1 hw`. Rewrite using `[hypForm_h]`. Simplify using `only [Pi.add_apply, hj z1 hz1 p (Ne.symm hjp'), hj w1 hw1 p (Ne.symm hjp'), hp z2 hz2 j hjp', hp w2 hw2 j hjp', add_zero, zero_add]`.

Use `isIntegralElt_add (hpair z1 hz1 w2 hw2) ?_` and prove the remaining obligations. Use `isIntegralElt_c S (hpair w1 hw1 z2 hz2)` as an intermediate fact. Rewrite `this` using `[map_mul, S.c_invol, mul_comm]`. Then use the resulting hypothesis. Establish `hgram : hGram (hypForm S j p) ![x0, y] = !![0, S.c (x0 j) * y p; S.c (y p) * x0 j, 0]`. Use extensionality with `a b`.

Apply the tactic sequence `fin_cases a <;> fin_cases b <;>`. Simplify using `[hGram, hypForm_h, hx0p, hyj]`. Establish `hdet : (hGram (hypForm S j p) ![x0, y]).det = -((S.c (x0 j) * y p) * (S.c (y p) * x0 j))`. Rewrite using `[hgram, Matrix.det_fin_two_of]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hcx : S.c (x0 j) ≠ 0` using `fun h => hx0j (S.c.injective (by rw [h, map_zero]))`. Establish `hcy : S.c (y p) ≠ 0` using `fun h => hyp (S.c.injective (by rw [h, map_zero]))`. Establish `hdet0 : (hGram (hypForm S j p) ![x0, y]).det ≠ 0`. Rewrite using `[hdet, neg_ne_zero]`. Conclude with `mul_ne_zero (mul_ne_zero hcx hyp) (mul_ne_zero hcy hx0j)`.

Establish `hb` using `hN K r 2 (hypForm S j p) T ![x0, y] hT hbT hint hdet0`. Rewrite `hb` using `[hdet, abs_norm_neg, map_mul, map_mul, map_mul, norm_c, norm_c]`. Move the coercions through the operations in `at hb`. Rewrite `hb` using `[spanIdx_pair j p hjp Gj Gp hj hp x0 y hx0 hy]`. Move the coercions through the operations in `at hb`.

Establish `hb' : (A * B) ^ 2 ≤ (X * Y) ^ 2` using `le_of_le_of_eq hb (by simp only [X, Y]; rw [abs_mul, abs_mul, abs_mul]; ring)`. Conclude with `(pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hb'`. Establish `hlog : Real.log A + Real.log B ≤ Real.log X + Real.log Y`. Rewrite using `[← Real.log_mul (by positivity) (by positivity), ← Real.log_mul hX.ne' hY.ne']`. Conclude with `Real.log_le_log (by positivity) key`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem top_le_zero (hN : IntegralIndexStatement) {K : Type} [Field K] [NumberField K] {r : ℕ}
    (S : HermForm K r) (j p : Fin r) (hjp : (j : ℕ) < p) (Gj Gp : Submodule (𝓞 K) (Fin r → K))
    (hGj : Gj.FG) (hGp : Gp.FG) (hj : ∀ x ∈ Gj, IsAt j x) (hp : ∀ x ∈ Gp, IsAt p x)
    (hpair : ∀ x ∈ Gj, ∀ y ∈ Gp, IsIntegralElt (S.c (x j) * y p))
    (x0 y : Fin r → K) (hx0 : x0 ∈ Gj) (hx0j : x0 j ≠ 0) (hy : y ∈ Gp) (hyp : y p ≠ 0)
    (δ : (K →+* ℂ) → Fin r → ℝ) (d : ℝ) (hd : 0 < d) (hδj : ∀ σ, δ σ j = d)
    (hδp : ∀ σ, δ σ p = d⁻¹) (h0 : latDeg (diagMet δ) Gj ![x0] = 0) :
    latDeg (diagMet δ) Gp ![y] ≤ 0 := by
  have hjp' : j ≠ p := fun h => by rw [h] at hjp; omega
  have hx0p : x0 p = 0 := hj x0 hx0 p (Ne.symm hjp')
  have hyj : y j = 0 := hp y hy j hjp'

  set n : ℝ := (Fintype.card (K →+* ℂ) : ℝ)
  have e0 := h0
  rw [latDeg_single δ Gj j x0 (hj x0 hx0)] at e0
  simp only [hδj] at e0
  rw [sum_log_single (x0 j) hx0j d hd] at e0
  rw [latDeg_single δ Gp p y (hp y hy)]
  simp only [hδp]
  rw [sum_log_single (y p) hyp d⁻¹ (inv_pos.2 hd), Real.log_inv]

  set A : ℝ := (spanIdx Gj ![x0] : ℝ)
  set B : ℝ := (spanIdx Gp ![y] : ℝ)
  set X : ℝ := |((Algebra.norm ℚ (x0 j) : ℚ) : ℝ)|
  set Y : ℝ := |((Algebra.norm ℚ (y p) : ℚ) : ℝ)|
  have hA : 1 ≤ A := by
    have := spanIdx_ne_zero Gj ![x0] hGj (kBasisIn_single j Gj hj x0 hx0 hx0j)
    exact Nat.one_le_cast.2 (Nat.one_le_iff_ne_zero.2 this)
  have hB : 1 ≤ B := by
    have := spanIdx_ne_zero Gp ![y] hGp (kBasisIn_single p Gp hp y hy hyp)
    exact Nat.one_le_cast.2 (Nat.one_le_iff_ne_zero.2 this)
  have hX : 0 < X := by
    apply abs_pos.2
    exact_mod_cast (Algebra.norm_ne_zero_iff).2 hx0j
  have hY : 0 < Y := by
    apply abs_pos.2
    exact_mod_cast (Algebra.norm_ne_zero_iff).2 hyp
  have key : A * B ≤ X * Y := by
    set T := Gj ⊔ Gp
    have hT : T.FG := hGj.sup hGp
    have hbT : IsKBasisIn T ![x0, y] := by
      refine ⟨fun i => ?_, ?_, ?_⟩
      · fin_cases i
        · exact Submodule.mem_sup_left hx0
        · exact Submodule.mem_sup_right hy
      · rw [LinearIndependent.pair_iff]
        intro s t hst
        have h1 := congr_fun hst j
        have h2 := congr_fun hst p
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hx0p, hyj,
          mul_zero, add_zero, zero_add] at h1 h2
        exact ⟨(mul_eq_zero.1 h1).resolve_right hx0j, (mul_eq_zero.1 h2).resolve_right hyp⟩
      · intro z hz
        obtain ⟨z1, hz1, z2, hz2, rfl⟩ := Submodule.mem_sup.1 hz
        rw [Matrix.range_cons_cons_empty]
        have e1 : z1 = (z1 j / x0 j) • x0 := by
          funext a
          simp only [Pi.smul_apply, smul_eq_mul]
          by_cases ha : a = j
          · subst ha; field_simp
          · rw [hj z1 hz1 a ha, hj x0 hx0 a ha, mul_zero]
        have e2 : z2 = (z2 p / y p) • y := by
          funext a
          simp only [Pi.smul_apply, smul_eq_mul]
          by_cases ha : a = p
          · subst ha; field_simp
          · rw [hp z2 hz2 a ha, hp y hy a ha, mul_zero]
        rw [e1, e2]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    have hint : IsIntegralOn (hypForm S j p) T := by
      intro z hz w hw
      obtain ⟨z1, hz1, z2, hz2, rfl⟩ := Submodule.mem_sup.1 hz
      obtain ⟨w1, hw1, w2, hw2, rfl⟩ := Submodule.mem_sup.1 hw
      rw [hypForm_h]
      simp only [Pi.add_apply, hj z1 hz1 p (Ne.symm hjp'), hj w1 hw1 p (Ne.symm hjp'),
        hp z2 hz2 j hjp', hp w2 hw2 j hjp', add_zero, zero_add]
      refine isIntegralElt_add (hpair z1 hz1 w2 hw2) ?_
      have := isIntegralElt_c S (hpair w1 hw1 z2 hz2)
      rwa [map_mul, S.c_invol, mul_comm] at this
    have hgram : hGram (hypForm S j p) ![x0, y] =
        !![0, S.c (x0 j) * y p; S.c (y p) * x0 j, 0] := by
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [hGram, hypForm_h, hx0p, hyj]
    have hdet : (hGram (hypForm S j p) ![x0, y]).det = -((S.c (x0 j) * y p) * (S.c (y p) * x0 j)) := by
      rw [hgram, Matrix.det_fin_two_of]
      ring
    have hcx : S.c (x0 j) ≠ 0 := fun h => hx0j (S.c.injective (by rw [h, map_zero]))
    have hcy : S.c (y p) ≠ 0 := fun h => hyp (S.c.injective (by rw [h, map_zero]))
    have hdet0 : (hGram (hypForm S j p) ![x0, y]).det ≠ 0 := by
      rw [hdet, neg_ne_zero]
      exact mul_ne_zero (mul_ne_zero hcx hyp) (mul_ne_zero hcy hx0j)
    have hb := hN K r 2 (hypForm S j p) T ![x0, y] hT hbT hint hdet0
    rw [hdet, abs_norm_neg, map_mul, map_mul, map_mul, norm_c, norm_c] at hb
    push_cast at hb
    rw [spanIdx_pair j p hjp Gj Gp hj hp x0 y hx0 hy] at hb
    push_cast at hb
    have hb' : (A * B) ^ 2 ≤ (X * Y) ^ 2 :=
      le_of_le_of_eq hb (by simp only [X, Y]; rw [abs_mul, abs_mul, abs_mul]; ring)
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hb'
  have hlog : Real.log A + Real.log B ≤ Real.log X + Real.log Y := by
    rw [← Real.log_mul (by positivity) (by positivity), ← Real.log_mul hX.ne' hY.ne']
    exact Real.log_le_log (by positivity) key
  linarith

end ReciprocityTheory.MultiplicativeHeights.SemiPt
