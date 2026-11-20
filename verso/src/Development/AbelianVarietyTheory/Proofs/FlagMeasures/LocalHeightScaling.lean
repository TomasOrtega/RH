import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetGramSumElimSmulSub
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalModelModulusPropertiesOnUnitsStatement
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical

namespace GlobalTheory

/- English proof (translation)
Establish `hD : 0 < ∏ l ∈ s, δ l` using `Finset.prod_pos hδ`. Rewrite using `[Finset.prod_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_inv_distrib]`. Generalize the expression as in `∏ l ∈ s, δ l = D at hD ⊢`. Generalize the expression as in `∑ l ∈ s, m l = N`. Establish `hY : 0 < a ^ ((2 * r + 1 : ℝ) / 2) * b ^ ((r * (r + 1) + N : ℕ) : ℝ) * c ^ (-(1 / 2 : ℝ)) * D⁻¹`.

Check the signs of the components of the expression. Establish `e1 : (a ^ ((2 * r + 1 : ℝ) / 2)) ^ 2 = a ^ (((2 * r + 1 : ℕ)) : ℝ)`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul ha.le]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `e2 : (b ^ ((r * (r + 1) + N : ℕ) : ℝ)) ^ 2 = b ^ (2 * r * (r + 1)) * b ^ (2 * N)`. Rewrite using `[Real.rpow_natCast, ← pow_mul, ← pow_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `e3 : (c ^ (-(1 / 2 : ℝ))) ^ 2 = c⁻¹`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hc.le]`. Evaluate the numerical expressions using `[Real.rpow_neg_one]`. Establish `hX : a * (b⁻¹ ^ (2 * r * (r + 1)) * c / a ^ (2 * (r + 1))) * (b⁻¹ ^ N * D) ^ 2 = ((a ^ ((2 * r + 1 : ℝ) / 2) * b ^ ((r * (r + 1) + N : ℕ) : ℝ) * c ^ (-(1 / 2 : ℝ)) * D⁻¹) ^ 2)⁻¹`. Simplify using `only [mul_pow]`.

Rewrite using `[e1, e2, e3, Real.rpow_natCast]`. Use `ha.ne'` as an intermediate fact. Use `hb.ne'` as an intermediate fact. Use `hc.ne'` as an intermediate fact. Use `hD.ne'` as an intermediate fact.

Simplify using `only [inv_pow]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hX, Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hY.le]`. Evaluate the numerical expressions using `[Real.rpow_neg_one]`.
-/
private theorem rpow_neg_half_height_product_eq (s : Finset ℕ) (r : ℕ) (m : ℕ → ℕ) {a b c : ℝ} {δ : ℕ → ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hδ : ∀ l ∈ s, 0 < δ l) :
    (a * (b⁻¹ ^ (2 * r * (r + 1)) * c / a ^ (2 * (r + 1))) * ∏ l ∈ s, (b⁻¹ ^ m l * δ l) ^ 2) ^ (-(1 / 2 : ℝ)) =
      a ^ ((2 * r + 1 : ℝ) / 2) * b ^ ((r * (r + 1) + ∑ l ∈ s, m l : ℕ) : ℝ) * c ^ (-(1 / 2 : ℝ)) *
        ∏ l ∈ s, (δ l)⁻¹ := by
  have hD : 0 < ∏ l ∈ s, δ l := Finset.prod_pos hδ
  rw [Finset.prod_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_inv_distrib]
  generalize ∏ l ∈ s, δ l = D at hD ⊢
  generalize ∑ l ∈ s, m l = N
  have hY : 0 < a ^ ((2 * r + 1 : ℝ) / 2) * b ^ ((r * (r + 1) + N : ℕ) : ℝ) * c ^ (-(1 / 2 : ℝ)) * D⁻¹ := by
    positivity
  have e1 : (a ^ ((2 * r + 1 : ℝ) / 2)) ^ 2 = a ^ (((2 * r + 1 : ℕ)) : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    congr 1
    push_cast
    ring
  have e2 : (b ^ ((r * (r + 1) + N : ℕ) : ℝ)) ^ 2 = b ^ (2 * r * (r + 1)) * b ^ (2 * N) := by
    rw [Real.rpow_natCast, ← pow_mul, ← pow_add]
    congr 1
    ring
  have e3 : (c ^ (-(1 / 2 : ℝ))) ^ 2 = c⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]
    norm_num [Real.rpow_neg_one]
  have hX : a * (b⁻¹ ^ (2 * r * (r + 1)) * c / a ^ (2 * (r + 1))) * (b⁻¹ ^ N * D) ^ 2 =
      ((a ^ ((2 * r + 1 : ℝ) / 2) * b ^ ((r * (r + 1) + N : ℕ) : ℝ) * c ^ (-(1 / 2 : ℝ)) * D⁻¹) ^ 2)⁻¹ := by
    simp only [mul_pow]
    rw [e1, e2, e3, Real.rpow_natCast]
    have := ha.ne'
    have := hb.ne'
    have := hc.ne'
    have := hD.ne'
    simp only [inv_pow]
    field_simp
    ring
  rw [hX, Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hY.le]
  norm_num [Real.rpow_neg_one]

/- English proof (translation)
Introduce `F _ _ _ E _ _ _ _ M hOK V _ _ H r P hGv0 e he G d hG hD`. Take `⟨hmul, hpc, hone⟩` from `T.localModel_modulus_properties_on_units M hOK`. Establish `hA1 : M.modK 1 = 1` using `hone 1 M.L.O.one_mem ⟨1, M.L.O.one_mem, one_mul 1⟩`. Establish `hpow : ∀ x : E, IsUnit x → ∀ n : ℕ, M.modK (x ^ n) = M.modK x ^ n`. Introduce `x hx n`.

Proceed by induction on `n with`. Consider the case `zero => simp [hA1]`. Consider the case `succ n ih => rw [pow_succ, hmul _ _ (hx.pow n) hx, ih, pow_succ]`. Establish `hneg : ∀ n : ℕ, M.modK ((-1 : E) ^ n) = 1` using `fun n => hone _ (pow_mem (neg_mem M.L.O.one_mem) n) ⟨(-1) ^ n, pow_mem (neg_mem M.L.O.one_mem) n, by rw [← mul_pow]; simp⟩`. Establish `hGvu : IsUnit P.Gv`.

Establish `hfix : M.L.cj P.Gv = P.Gv`. Simplify using `only [LocNG.FPair.Gv, HermSp.Gdet, HermSp.normE, map_sub, map_mul, AlgEquiv.commutes, M.L.cj_cj]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨a, ha⟩` from `(M.L.cj_fix _).1 hfix`. Establish `ha0 : a ≠ 0`.

Introduce and unpack `rfl`. Conclude with `hGv0 (by rw [← ha, map_zero])`. Rewrite using `[← ha]`. Conclude with `(IsUnit.mk0 a ha0).map _`. Establish `hae : IsUnit (algebraMap F E e)` using `(IsUnit.mk0 e he).map _`.

Establish `haei : IsUnit (algebraMap F E e⁻¹)` using `(IsUnit.mk0 _ (inv_ne_zero he)).map _`. Establish `hAei : M.modK (algebraMap F E e⁻¹) = (M.modK (algebraMap F E e))⁻¹`. Establish `h1` using `hmul _ _ haei hae`. Establish `h2 : algebraMap F E e⁻¹ * algebraMap F E e = 1`. Rewrite using `[← map_mul, inv_mul_cancel₀ he, map_one]`.

Rewrite `h1` using `[h2, hA1]`. Conclude with `eq_inv_of_mul_eq_one_left h1.symm`. Establish `hθ0 : LocNG.theta M ≠ 0`. Unfold `LocNG.theta`. Use `split`.

Conclude with `one_ne_zero`. Use `next g _ => simpa using g.q_irr.ne_zero`. Establish `hθu : IsUnit (algebraMap F E (LocNG.theta M))` using `(IsUnit.mk0 _ hθ0).map _`. Establish `hdg` using `det_gram_frame_generators M hOK H r 0 P`. Establish `hdu : IsUnit (H.gram P.MMgen).det`.

Establish `h1 : IsUnit ((H.gram P.MMgen).det * algebraMap F E (LocNG.theta M) ^ (2 * (r + 1)))`. Rewrite using `[hdg]`. Conclude with `(isUnit_one.neg.pow _).mul hGvu`. Conclude with `isUnit_of_mul_isUnit_left h1`. Establish `hAdet : M.modK (H.gram P.MMgen).det * M.modK (algebraMap F E (LocNG.theta M)) ^ (2 * (r + 1)) = M.modK P.Gv`.

Establish `h1` using `congrArg M.modK hdg`. Rewrite `h1` using `[hmul _ _ hdu (hθu.pow _), hpow _ hθu, hmul _ _ (isUnit_one.neg.pow _) hGvu, hneg, one_mul]`. Conclude with `h1`. Establish `hGu : IsUnit G` using `isUnit_of_mul_isUnit_right (by rw [← hG]; exact hGvu)`. Establish `hAGv : M.modK P.Gv = (M.modK (algebraMap F E e))⁻¹ ^ (2 * r * (r + 1)) * M.modK G`.

Rewrite using `[hG, map_pow, hmul _ _ (haei.pow _) hGu, hpow _ haei, hAei]`. Establish `hDu : ∀ l ∈ P.ends, IsUnit (P.Dm l)`. Introduce `l hl`. Simplify using `only [LocNG.FPair.ends, Finset.mem_filter, Finset.mem_range] at hl`. Conclude with `hl.2.2`.

Establish `hdu' : ∀ l ∈ P.ends, IsUnit (d l)` using `fun l hl => isUnit_of_mul_isUnit_right (by rw [← hD l hl]; exact hDu l hl)`. Establish `hAD : ∀ l ∈ P.ends, M.modK (P.Dm l * M.L.cj (P.Dm l)) = ((M.modK (algebraMap F E e))⁻¹ ^ (l * (2 * r + 1 - l)) * M.modK (d l)) ^ 2`. Introduce `l hl`. Rewrite using `[hmul _ _ (hDu l hl) ((hDu l hl).map M.L.cj), (hpc _ (hDu l hl)).2, ← sq, hD l hl, map_pow, hmul _ _ (haei.pow _) (hdu' l hl), hpow _ haei, hAei]`. Establish `ha : 0 < M.modK (algebraMap F E (LocNG.theta M))` using `(hpc _ hθu).1`.

Establish `hb : 0 < M.modK (algebraMap F E e)` using `(hpc _ hae).1`. Establish `hc : 0 < M.modK G` using `(hpc _ hGu).1`. Establish `hδ : ∀ l ∈ P.ends, 0 < M.modK (d l)` using `fun l hl => (hpc _ (hdu' l hl)).1`. Establish `hAdet' : M.modK (H.gram P.MMgen).det = (M.modK (algebraMap F E e))⁻¹ ^ (2 * r * (r + 1)) * M.modK G / M.modK (algebraMap F E (LocNG.theta M)) ^ (2 * (r + 1))`. Rewrite using `[← hAGv, ← hAdet, mul_div_cancel_right₀ _ (pow_ne_zero _ ha.ne')]`.

Use `⟨fun hp => ?_, ?_⟩` and prove the remaining obligations. Take `⟨hs, hGo, hDo⟩` from `hp`. Establish `hθ1 : LocNG.theta M = 1`. Unfold `LocNG.theta`. Rewrite using `[hs]`.

Establish `hAθ : M.modK (algebraMap F E (LocNG.theta M)) = 1` using `by rw [hθ1, map_one, hA1]`. Establish `hG1 : M.modK P.Gv = 1` using `hone _ hGo.1 hGo.2`. Establish `hdet1 : M.modK (H.gram P.MMgen).det = 1`. Establish `h1` using `hAdet`. Rewrite `h1` using `[hAθ, hG1, one_pow, mul_one]`.

Conclude with `h1`. Unfold `LocNG.FPair.Hp`. Rewrite using `[hAθ, hdet1, Finset.prod_eq_one]`. Simplify using the standard rewrite rules. Introduce `l hl`.

Rewrite using `[hmul _ _ (hDu l hl) ((hDu l hl).map M.L.cj), (hpc _ (hDu l hl)).2, hone _ (hDo l hl).1 (hDo l hl).2, one_mul]`. Unfold `LocNG.FPair.Hp`. Rewrite using `[hAdet', Finset.prod_congr rfl hAD]`. Conclude with `rpow_neg_half_height_product_eq P.ends r (fun l => l * (2 * r + 1 - l)) ha hb hc hδ`.
-/
theorem local_height_scaling : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (P : LocNG.FPair H r), P.Gv ≠ 0 → ∀ (e : F), e ≠ 0 → ∀ (G : E) (d : ℕ → E), P.Gv = algebraMap F E (e⁻¹ ^ (2 * r * (r + 1))) * G → (∀ l ∈ P.ends, P.Dm l = algebraMap F E (e⁻¹ ^ (l * (2 * r + 1 - l))) * d l) → (P.PrimeTo → P.Hp = 1) ∧ P.Hp = M.modK (algebraMap F E (LocNG.theta M)) ^ ((2 * r + 1 : ℝ) / 2) * M.modK (algebraMap F E e) ^ ((r * (r + 1) + ∑ l ∈ P.ends, l * (2 * r + 1 - l) : ℕ) : ℝ) * M.modK G ^ (-(1 / 2 : ℝ)) * ∏ l ∈ P.ends, (M.modK (d l))⁻¹ := by
  intro F _ _ _ E _ _ _ _ M hOK V _ _ H r P hGv0 e he G d hG hD
  obtain ⟨hmul, hpc, hone⟩ := T.localModel_modulus_properties_on_units M hOK
  have hA1 : M.modK 1 = 1 := hone 1 M.L.O.one_mem ⟨1, M.L.O.one_mem, one_mul 1⟩
  have hpow : ∀ x : E, IsUnit x → ∀ n : ℕ, M.modK (x ^ n) = M.modK x ^ n := by
    intro x hx n
    induction n with
    | zero => simp [hA1]
    | succ n ih => rw [pow_succ, hmul _ _ (hx.pow n) hx, ih, pow_succ]
  have hneg : ∀ n : ℕ, M.modK ((-1 : E) ^ n) = 1 := fun n =>
    hone _ (pow_mem (neg_mem M.L.O.one_mem) n)
      ⟨(-1) ^ n, pow_mem (neg_mem M.L.O.one_mem) n, by rw [← mul_pow]; simp⟩
  have hGvu : IsUnit P.Gv := by
    have hfix : M.L.cj P.Gv = P.Gv := by
      simp only [LocNG.FPair.Gv, HermSp.Gdet, HermSp.normE, map_sub, map_mul, AlgEquiv.commutes,
        M.L.cj_cj]
      ring
    obtain ⟨a, ha⟩ := (M.L.cj_fix _).1 hfix
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hGv0 (by rw [← ha, map_zero])
    rw [← ha]
    exact (IsUnit.mk0 a ha0).map _
  have hae : IsUnit (algebraMap F E e) := (IsUnit.mk0 e he).map _
  have haei : IsUnit (algebraMap F E e⁻¹) := (IsUnit.mk0 _ (inv_ne_zero he)).map _
  have hAei : M.modK (algebraMap F E e⁻¹) = (M.modK (algebraMap F E e))⁻¹ := by
    have h1 := hmul _ _ haei hae
    have h2 : algebraMap F E e⁻¹ * algebraMap F E e = 1 := by
      rw [← map_mul, inv_mul_cancel₀ he, map_one]
    rw [h2, hA1] at h1
    exact eq_inv_of_mul_eq_one_left h1.symm
  have hθ0 : LocNG.theta M ≠ 0 := by
    unfold LocNG.theta
    split
    · exact one_ne_zero
    · next g _ => simpa using g.q_irr.ne_zero
  have hθu : IsUnit (algebraMap F E (LocNG.theta M)) := (IsUnit.mk0 _ hθ0).map _
  have hdg := det_gram_frame_generators M hOK H r 0 P
  have hdu : IsUnit (H.gram P.MMgen).det := by
    have h1 : IsUnit ((H.gram P.MMgen).det * algebraMap F E (LocNG.theta M) ^ (2 * (r + 1))) := by
      rw [hdg]
      exact (isUnit_one.neg.pow _).mul hGvu
    exact isUnit_of_mul_isUnit_left h1
  have hAdet : M.modK (H.gram P.MMgen).det * M.modK (algebraMap F E (LocNG.theta M)) ^ (2 * (r + 1)) =
      M.modK P.Gv := by
    have h1 := congrArg M.modK hdg
    rw [hmul _ _ hdu (hθu.pow _), hpow _ hθu, hmul _ _ (isUnit_one.neg.pow _) hGvu, hneg, one_mul] at h1
    exact h1
  have hGu : IsUnit G := isUnit_of_mul_isUnit_right (by rw [← hG]; exact hGvu)
  have hAGv : M.modK P.Gv = (M.modK (algebraMap F E e))⁻¹ ^ (2 * r * (r + 1)) * M.modK G := by
    rw [hG, map_pow, hmul _ _ (haei.pow _) hGu, hpow _ haei, hAei]
  have hDu : ∀ l ∈ P.ends, IsUnit (P.Dm l) := by
    intro l hl
    simp only [LocNG.FPair.ends, Finset.mem_filter, Finset.mem_range] at hl
    exact hl.2.2
  have hdu' : ∀ l ∈ P.ends, IsUnit (d l) := fun l hl =>
    isUnit_of_mul_isUnit_right (by rw [← hD l hl]; exact hDu l hl)
  have hAD : ∀ l ∈ P.ends, M.modK (P.Dm l * M.L.cj (P.Dm l)) =
      ((M.modK (algebraMap F E e))⁻¹ ^ (l * (2 * r + 1 - l)) * M.modK (d l)) ^ 2 := by
    intro l hl
    rw [hmul _ _ (hDu l hl) ((hDu l hl).map M.L.cj), (hpc _ (hDu l hl)).2, ← sq, hD l hl, map_pow,
      hmul _ _ (haei.pow _) (hdu' l hl), hpow _ haei, hAei]
  have ha : 0 < M.modK (algebraMap F E (LocNG.theta M)) := (hpc _ hθu).1
  have hb : 0 < M.modK (algebraMap F E e) := (hpc _ hae).1
  have hc : 0 < M.modK G := (hpc _ hGu).1
  have hδ : ∀ l ∈ P.ends, 0 < M.modK (d l) := fun l hl => (hpc _ (hdu' l hl)).1
  have hAdet' : M.modK (H.gram P.MMgen).det = (M.modK (algebraMap F E e))⁻¹ ^ (2 * r * (r + 1)) *
      M.modK G / M.modK (algebraMap F E (LocNG.theta M)) ^ (2 * (r + 1)) := by
    rw [← hAGv, ← hAdet, mul_div_cancel_right₀ _ (pow_ne_zero _ ha.ne')]
  refine ⟨fun hp => ?_, ?_⟩
  · obtain ⟨hs, hGo, hDo⟩ := hp
    have hθ1 : LocNG.theta M = 1 := by
      unfold LocNG.theta
      rw [hs]
    have hAθ : M.modK (algebraMap F E (LocNG.theta M)) = 1 := by rw [hθ1, map_one, hA1]
    have hG1 : M.modK P.Gv = 1 := hone _ hGo.1 hGo.2
    have hdet1 : M.modK (H.gram P.MMgen).det = 1 := by
      have h1 := hAdet
      rw [hAθ, hG1, one_pow, mul_one] at h1
      exact h1
    unfold LocNG.FPair.Hp
    rw [hAθ, hdet1, Finset.prod_eq_one]
    · simp
    · intro l hl
      rw [hmul _ _ (hDu l hl) ((hDu l hl).map M.L.cj), (hpc _ (hDu l hl)).2,
        hone _ (hDo l hl).1 (hDo l hl).2, one_mul]
  · unfold LocNG.FPair.Hp
    rw [hAdet', Finset.prod_congr rfl hAD]
    exact rpow_neg_half_height_product_eq P.ends r (fun l => l * (2 * r + 1 - l)) ha hb hc hδ

end GlobalTheory
