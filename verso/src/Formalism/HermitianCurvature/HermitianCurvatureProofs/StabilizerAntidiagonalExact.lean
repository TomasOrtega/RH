import Formalism.HermitianCurvature.HermitianCurvatureProofs.LowerParabolicCoordinates

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

open C2x2

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp [div_self (hy 0)]`. Consider the case `succ n ih`. Rewrite using `[Finset.prod_range_succ, ih, div_mul_div_comm, mul_comm (y n) (y (n + 1)), mul_div_mul_right _ _ (hy n)]`.
-/
lemma c2x3_tel (y : ℕ → ℝ) (hy : ∀ i, y i ≠ 0) :
    ∀ n, ∏ l ∈ Finset.range n, y (l + 1) / y l = y n / y 0 := by
  intro n
  induction n with
  | zero => simp [div_self (hy 0)]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, div_mul_div_comm, mul_comm (y n) (y (n + 1)),
      mul_div_mul_right _ _ (hy n)]

/- English proof (translation)
Introduce `r`. Proceed by induction on `r with`. Consider the case `zero => simp [h0]`. Consider the case `succ r ih`. Establish `hsplit : ∀ l ∈ Finset.range (r + 1), (y (l + 1) / y l) ^ (4 * (r + 1 - l) + K) = (y (l + 1) / y l) ^ 4 * (y (l + 1) / y l) ^ (4 * (r - l) + K)`.

Introduce `l hl`. Rewrite `hl` using `[Finset.mem_range]`. Rewrite using `[← pow_add]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[Finset.prod_congr rfl hsplit, Finset.prod_mul_distrib, Finset.prod_pow, c2x3_tel y (fun i => (hy i).ne') (r + 1), h0, div_one, Finset.prod_range_succ (fun l => (y (l + 1) / y l) ^ (4 * (r - l) + K)), ih, Nat.sub_self, mul_zero, zero_add, Finset.prod_range_succ (fun l => y (l + 1 …`. Establish `hr0` using `(hy r).ne'`. Establish `hq : y r ^ K * (y (r + 1) / y r) ^ K = y (r + 1) ^ K`. Rewrite using `[div_pow, mul_div_cancel₀ _ (pow_ne_zero K hr0)]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma c2x3_w2core (y : ℕ → ℝ) (hy : ∀ i, 0 < y i) (h0 : y 0 = 1) (K : ℕ) : ∀ r : ℕ,
    ∏ l ∈ Finset.range r, (y (l + 1) / y l) ^ (4 * (r - l) + K) =
      y r ^ K * ∏ l ∈ Finset.range r, y (l + 1) ^ 4 := by
  intro r
  induction r with
  | zero => simp [h0]
  | succ r ih =>
    have hsplit : ∀ l ∈ Finset.range (r + 1), (y (l + 1) / y l) ^ (4 * (r + 1 - l) + K) =
        (y (l + 1) / y l) ^ 4 * (y (l + 1) / y l) ^ (4 * (r - l) + K) := by
      intro l hl
      rw [Finset.mem_range] at hl
      rw [← pow_add]; congr 1; omega
    rw [Finset.prod_congr rfl hsplit, Finset.prod_mul_distrib, Finset.prod_pow,
      c2x3_tel y (fun i => (hy i).ne') (r + 1), h0, div_one,
      Finset.prod_range_succ (fun l => (y (l + 1) / y l) ^ (4 * (r - l) + K)), ih, Nat.sub_self,
      mul_zero, zero_add, Finset.prod_range_succ (fun l => y (l + 1) ^ 4)]
    have hr0 := (hy r).ne'
    have hq : y r ^ K * (y (r + 1) / y r) ^ K = y (r + 1) ^ K := by
      rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero K hr0)]
    calc y (r + 1) ^ 4 * (y r ^ K * (∏ l ∈ Finset.range r, y (l + 1) ^ 4) * (y (r + 1) / y r) ^ K)
        = y (r + 1) ^ 4 * (∏ l ∈ Finset.range r, y (l + 1) ^ 4) * (y r ^ K * (y (r + 1) / y r) ^ K) := by ring
      _ = y (r + 1) ^ K * ((∏ l ∈ Finset.range r, y (l + 1) ^ 4) * y (r + 1) ^ 4) := by rw [hq]; ring

/- English proof (translation)
Introduce `k r x Gv hk hx0 hxpos hG`. Take `⟨y, hyx, hypos⟩ : ∃ y : ℕ → ℝ, (∀ i (h : i < r + 1), y i = x ⟨i, h⟩) ∧ ∀ i, 0 < y i` from `⟨fun i => if h : i < r + 1 then x ⟨i, h⟩ else 1, fun i h => dif_pos h, fun i => by dsimp only; split_ifs; exacts [hxpos _, one_pos]⟩`. Establish `hy0 : y 0 = 1`. Rewrite using `[hyx 0 (Nat.succ_pos r)]`. Establish `: (⟨0, Nat.succ_pos r⟩ : Fin (r + 1)) = 0` using `Fin.ext (by simp)`.

Rewrite using `[this, hx0]`. Establish `hsucc : ∀ l : Fin r, x l.succ = y (l.val + 1)`. Introduce `l; rw [hyx _ (by omega)]; rfl`. Establish `hcast : ∀ l : Fin r, x l.castSucc = y l.val`. Introduce `l; rw [hyx _ (by omega)]; rfl`.

Establish `hlast : x (Fin.last r) = y r` using `by rw [hyx _ (Nat.lt_succ_self r)]; rfl`. Establish `hexp : ∀ l : Fin r, 2 * (C2.Ml k r (l.val + 1) - 2) = 4 * (r - l.val) + 2 * (k - 1)`. Introduce `l`. Unfold `C2.Ml`. Use `l.isLt` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Simplify using `only [hsucc, hcast, hexp, hlast]`. Rewrite using `[Fin.prod_univ_eq_prod_range (fun l => (y (l + 1) / y l) ^ (4 * (r - l) + 2 * (k - 1))) r, Fin.prod_univ_eq_prod_range (fun l => y (l + 1) ^ 4) r, c2x3_w2core y hypos hy0 (2 * (k - 1)) r]`. Use `(hypos r).ne'` as an intermediate fact. Rewrite using `[div_pow, pow_mul]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem gram_product_identity : C2.GramProductIdentity := by
  intro k r x Gv hk hx0 hxpos hG
  obtain ⟨y, hyx, hypos⟩ : ∃ y : ℕ → ℝ, (∀ i (h : i < r + 1), y i = x ⟨i, h⟩) ∧ ∀ i, 0 < y i :=
    ⟨fun i => if h : i < r + 1 then x ⟨i, h⟩ else 1, fun i h => dif_pos h,
     fun i => by dsimp only; split_ifs; exacts [hxpos _, one_pos]⟩
  have hy0 : y 0 = 1 := by
    rw [hyx 0 (Nat.succ_pos r)]
    have : (⟨0, Nat.succ_pos r⟩ : Fin (r + 1)) = 0 := Fin.ext (by simp)
    rw [this, hx0]
  have hsucc : ∀ l : Fin r, x l.succ = y (l.val + 1) := by
    intro l; rw [hyx _ (by omega)]; rfl
  have hcast : ∀ l : Fin r, x l.castSucc = y l.val := by
    intro l; rw [hyx _ (by omega)]; rfl
  have hlast : x (Fin.last r) = y r := by rw [hyx _ (Nat.lt_succ_self r)]; rfl
  have hexp : ∀ l : Fin r, 2 * (C2.Ml k r (l.val + 1) - 2) = 4 * (r - l.val) + 2 * (k - 1) := by
    intro l; unfold C2.Ml; have := l.isLt; omega
  simp only [hsucc, hcast, hexp, hlast]
  rw [Fin.prod_univ_eq_prod_range (fun l => (y (l + 1) / y l) ^ (4 * (r - l) + 2 * (k - 1))) r,
    Fin.prod_univ_eq_prod_range (fun l => y (l + 1) ^ 4) r, c2x3_w2core y hypos hy0 (2 * (k - 1)) r]
  have := (hypos r).ne'
  rw [div_pow, pow_mul]
  field_simp

/- English proof (translation)
Unfold `C2.iSet`. Rewrite using `[Fin.card_filter_val_lt]`. Use linear arithmetic over natural numbers and integers.
-/
lemma c2x3_iSet_card {m a : ℕ} (h : a ≤ m) : (C2.iSet m a).card = a := by
  unfold C2.iSet
  rw [Fin.card_filter_val_lt]; omega

/- English proof (translation)
Unfold `C2.wSet`. Rewrite using `[Finset.card_image_of_injective _ w.injective, c2x3_iSet_card h]`.
-/
lemma c2x3_wSet_card {m a : ℕ} (w : Equiv.Perm (Fin m)) (h : a ≤ m) : (C2.wSet w a).card = a := by
  unfold C2.wSet
  rw [Finset.card_image_of_injective _ w.injective, c2x3_iSet_card h]

/- English proof (translation)
Apply `IsUnit.ne_zero` to reduce the goal to its premises. Apply `Matrix.isUnit_det_of_left_inverse (B := Matrix.of fun j i => if e i = w (f j) then (d (f j))⁻¹ else 0)` to reduce the goal to its premises. Use extensionality with `j j'`. Simplify using `only [Matrix.mul_apply, Matrix.of_apply, Matrix.submatrix_apply, C2.monoP]`. Take `⟨i0, hi0⟩` from `hs j`.

Rewrite using `[Finset.sum_eq_single i0]`. Rewrite using `[if_pos hi0]`. Distinguish the cases in `hjj : j = j'`. Substitute `hjj` using the available equality. Rewrite using `[if_pos hi0, Matrix.one_apply_eq]`.

Clear denominators, using `[hd (f j)]` for the nonvanishing conditions. Rewrite using `[if_neg, mul_zero, Matrix.one_apply_ne hjj]`. Introduce `e'`. Apply `hjj` to reduce the goal to its premises. Rewrite `e'` using `[hi0]`.

Conclude with `hf (w.injective e')`. Introduce `i _ hi`. Rewrite using `[if_neg, zero_mul]`. Introduce `e'`. Apply `hi` to reduce the goal to its premises.

Conclude with `he (e'.trans hi0.symm)`. Simplify using the standard rewrite rules.
-/
lemma c2x3_det_mono_ne {m k : ℕ} (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0)
    (e f : Fin k → Fin m) (he : Function.Injective e) (hf : Function.Injective f)
    (hs : ∀ j, ∃ i, e i = w (f j)) : ((C2.monoP w d).submatrix e f).det ≠ 0 := by
  apply IsUnit.ne_zero
  apply Matrix.isUnit_det_of_left_inverse
    (B := Matrix.of fun j i => if e i = w (f j) then (d (f j))⁻¹ else 0)
  ext j j'
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.submatrix_apply, C2.monoP]
  obtain ⟨i0, hi0⟩ := hs j
  rw [Finset.sum_eq_single i0]
  · rw [if_pos hi0]
    by_cases hjj : j = j'
    · subst hjj; rw [if_pos hi0, Matrix.one_apply_eq]; field_simp [hd (f j)]
    · rw [if_neg, mul_zero, Matrix.one_apply_ne hjj]
      intro e'; apply hjj; rw [hi0] at e'; exact hf (w.injective e')
  · intro i _ hi
    rw [if_neg, zero_mul]
    intro e'; apply hi; exact he (e'.trans hi0.symm)
  · simp

/- English proof (translation)
Introduce `m w d hd a ha`. Establish `hI` using `c2x3_wSet_card w ha`. Establish `hJ` using `c2x3_iSet_card ha`. Unfold `C2.minorS`. Rewrite using `[dif_pos (hI.trans hJ.symm)]`.

Apply `c2x3_det_mono_ne w d hd _ _ (RelEmbedding.injective _) (RelEmbedding.injective _)` to reduce the goal to its premises. Introduce `j`. Establish `hmem : w ((C2.iSet m a).orderEmbOfFin (hI.trans hJ.symm).symm j) ∈ C2.wSet w a` using `Finset.mem_image_of_mem w (Finset.orderEmbOfFin_mem _ _ j)`. Establish `hr` using `Finset.range_orderEmbOfFin (C2.wSet w a) (rfl : (C2.wSet w a).card = (C2.wSet w a).card)`. Rewrite `hmem` using `[← Finset.mem_coe, ← hr]`.

Conclude with `hmem`.
-/
theorem minor_C_nonzero : C2.MinorCNonzero := by
  intro m w d hd a ha
  have hI := c2x3_wSet_card w ha
  have hJ := c2x3_iSet_card ha
  unfold C2.minorS
  rw [dif_pos (hI.trans hJ.symm)]
  apply c2x3_det_mono_ne w d hd _ _ (RelEmbedding.injective _) (RelEmbedding.injective _)
  intro j
  have hmem : w ((C2.iSet m a).orderEmbOfFin (hI.trans hJ.symm).symm j) ∈ C2.wSet w a :=
    Finset.mem_image_of_mem w (Finset.orderEmbOfFin_mem _ _ j)
  have hr := Finset.range_orderEmbOfFin (C2.wSet w a) (rfl : (C2.wSet w a).card = (C2.wSet w a).card)
  rw [← Finset.mem_coe, ← hr] at hmem
  exact hmem

/- English proof (translation)
Introduce `s l u t hu ht`. Establish `hW` using `c2x2_antiW_sq s`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1 : l * C2.antiW s * u = C2.antiW s`.

Establish `: t • (l * C2.antiW s * u) = t • C2.antiW s`. Rewrite using `[← h]`. Simplify using `only [Matrix.mul_smul, Matrix.smul_mul]`. Conclude with `smul_right_injective _ ht this`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Matrix.mul_assoc (l * C2.antiW s) u, Matrix.mul_nonsing_inv _ (ut_unit hu), Matrix.mul_one, Matrix.mul_assoc, hW, Matrix.mul_one]`. Use `_ = C2.antiW s * u⁻¹ * C2.antiW s := by rw [h1]`. Introduce and unpack `rfl`. Conclude with `(stabilizer_antidiagonal s u t hu ht).2.1`.
-/
theorem stabilizer_antidiagonal_exact : C2.StabAntidiagExact := by
  intro s l u t hu ht
  have hW := c2x2_antiW_sq s
  constructor
  · intro h
    have h1 : l * C2.antiW s * u = C2.antiW s := by
      have : t • (l * C2.antiW s * u) = t • C2.antiW s := by
        rw [← h]; simp only [Matrix.mul_smul, Matrix.smul_mul]
      exact smul_right_injective _ ht this
    calc l = l * C2.antiW s * u * u⁻¹ * C2.antiW s := by
          rw [Matrix.mul_assoc (l * C2.antiW s) u, Matrix.mul_nonsing_inv _ (ut_unit hu), Matrix.mul_one,
            Matrix.mul_assoc, hW, Matrix.mul_one]
      _ = C2.antiW s * u⁻¹ * C2.antiW s := by rw [h1]
  · rintro rfl
    exact (stabilizer_antidiagonal s u t hu ht).2.1

/- English proof (translation)
Establish `hnn : ∀ v ∈ U, 0 ≤ (herm H v v).re`. Introduce `v hv`. Distinguish the cases in `h0 : v = 0`. Substitute `h0` using the available equality. Simplify using `[herm]`.

Conclude with `le_of_lt (hpos v hv h0)`. Establish `hreal : ∀ v, (herm H v v).im = 0`. Introduce `v`. Use `ggHerm_swap H hH v v` as an intermediate fact. Establish `h2` using `congrArg Complex.im this`.

Simplify using `only [Complex.star_def, Complex.conj_im] at h2`. Combine the linear equalities and inequalities to obtain the conclusion. Distinguish the cases in `hb0 : b = 0`. Substitute `hb0` using the available equality. Simplify using `[herm]`.

Establish `hbpos` using `hpos b hb hb0`. Use `set β := herm H a b with hβ`. Use `set q : ℝ := (herm H b b).re with hq`. Establish `hbb : herm H b b = (q : ℂ)` using `Complex.ext rfl (by rw [hreal]; simp)`. Establish `hba : herm H b a = conj β` using `by rw [ggHerm_swap H hH b a]; rfl`.

Use `set s : ℂ := β / (q : ℂ) with hs`. Establish `hx : a - s • b ∈ U` using `U.sub_mem ha (U.smul_mem s hb)`. Establish `hexp : herm H (a - s • b) (a - s • b) = herm H a a - conj s * β - s * herm H b a + s * conj s * herm H b b`. Simplify using `only [herm, Matrix.mulVec_sub, Matrix.mulVec_smul, star_sub, star_smul, dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul, hβ]`. Simplify using `only [Complex.star_def]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hqne : (q : ℂ) ≠ 0` using `by exact_mod_cast hbpos.ne'`. Establish `hkey : herm H (a - s • b) (a - s • b) = herm H a a - ((Complex.normSq β / q : ℝ) : ℂ)`. Rewrite using `[hexp, hba, hbb, hs]`. Establish `hn : ((Complex.normSq β : ℝ) : ℂ) = conj β * β` using `Complex.normSq_eq_conj_mul_self`.

Rewrite using `[map_div₀, Complex.conj_ofReal]`. Use `push_cast`. Rewrite using `[hn]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Establish `h1` using `hnn _ hx`. Rewrite `h1` using `[hkey, Complex.sub_re, Complex.ofReal_re]`. Establish `: Complex.normSq β / q ≤ (herm H a a).re` using `by linarith`. Rewrite `this` using `[div_le_iff₀ hbpos]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma c2x3_cs {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (U : Submodule ℂ (Fin n → ℂ))
    (hpos : ∀ v ∈ U, v ≠ 0 → 0 < (herm H v v).re) (a b : Fin n → ℂ) (ha : a ∈ U) (hb : b ∈ U) :
    Complex.normSq (herm H a b) ≤ (herm H a a).re * (herm H b b).re := by
  have hnn : ∀ v ∈ U, 0 ≤ (herm H v v).re := by
    intro v hv
    by_cases h0 : v = 0
    · subst h0; simp [herm]
    · exact le_of_lt (hpos v hv h0)
  have hreal : ∀ v, (herm H v v).im = 0 := by
    intro v
    have := ggHerm_swap H hH v v
    have h2 := congrArg Complex.im this
    simp only [Complex.star_def, Complex.conj_im] at h2
    linarith
  by_cases hb0 : b = 0
  · subst hb0; simp [herm]
  have hbpos := hpos b hb hb0
  set β := herm H a b with hβ
  set q : ℝ := (herm H b b).re with hq
  have hbb : herm H b b = (q : ℂ) := Complex.ext rfl (by rw [hreal]; simp)
  have hba : herm H b a = conj β := by rw [ggHerm_swap H hH b a]; rfl
  set s : ℂ := β / (q : ℂ) with hs
  have hx : a - s • b ∈ U := U.sub_mem ha (U.smul_mem s hb)
  have hexp : herm H (a - s • b) (a - s • b) =
      herm H a a - conj s * β - s * herm H b a + s * conj s * herm H b b := by
    simp only [herm, Matrix.mulVec_sub, Matrix.mulVec_smul, star_sub, star_smul, dotProduct_sub,
      sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul, hβ]
    simp only [Complex.star_def]
    ring
  have hqne : (q : ℂ) ≠ 0 := by exact_mod_cast hbpos.ne'
  have hkey : herm H (a - s • b) (a - s • b) = herm H a a - ((Complex.normSq β / q : ℝ) : ℂ) := by
    rw [hexp, hba, hbb, hs]
    have hn : ((Complex.normSq β : ℝ) : ℂ) = conj β * β := Complex.normSq_eq_conj_mul_self
    rw [map_div₀, Complex.conj_ofReal]
    push_cast
    rw [hn]
    field_simp
    ring
  have h1 := hnn _ hx
  rw [hkey, Complex.sub_re, Complex.ofReal_re] at h1
  have : Complex.normSq β / q ≤ (herm H a a).re := by linarith
  rw [div_le_iff₀ hbpos] at this
  linarith

/- English proof (translation)
Introduce `n H P U c hH hH2 hpos hPU horth hc hPn v hv`. Establish `hE : ∀ x : Fin n → ℂ, star x ⬝ᵥ x = ((∑ i, Complex.normSq (x i) : ℝ) : ℂ)`. Introduce `x`. Simplify using `only [dotProduct, Pi.star_apply, Complex.star_def, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self]`. Establish `hEnn : ∀ x : Fin n → ℂ, 0 ≤ ∑ i, Complex.normSq (x i)` using `fun x => Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)`.

Establish `hHv : ∀ u : Fin n → ℂ, herm H (H *ᵥ v) u = star u ⬝ᵥ v`. Introduce `u`. Simplify using `only [herm, Matrix.mulVec_mulVec, hH2, Matrix.one_mulVec]`. Use `set w := P *ᵥ (H *ᵥ v) with hw`. Establish `hwU : w ∈ U` using `hPU _`.

Establish `hwu : ∀ u ∈ U, herm H w u = star u ⬝ᵥ v`. Introduce `u hu`. Use `horth (H *ᵥ v) u hu` as an intermediate fact. Simplify using `only [herm, Matrix.mulVec_sub, dotProduct_sub, sub_eq_zero] at this`. Rewrite using `[← hHv u]`.

Simplify using `only [herm]`. Conclude with `this.symm`. Establish `hEH : ∑ i, Complex.normSq ((H *ᵥ v) i) = ∑ i, Complex.normSq (v i)`. Establish `h1` using `hE (H *ᵥ v)`. Establish `h2` using `hE v`.

Rewrite `h1` using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hH, hH2, Matrix.one_mulVec, h2]`. Conclude with `h1.symm` after adjusting the coercions. Use `set Ev := ∑ i, Complex.normSq (v i) with hEv`. Use `set Ew := ∑ i, Complex.normSq (w i) with hEw`. Establish `hw2 : Ew ≤ c ^ 2 * Ev` using `by rw [← hEH]; exact hPn _`.

Establish `hcsU` using `c2x3_cs H hH U hpos w v hwU hv`. Rewrite `hcsU` using `[hwu v hv, hE v, Complex.normSq_ofReal]`. Establish `hpos1 : ∀ x ∈ (⊤ : Submodule ℂ (Fin n → ℂ)), x ≠ 0 → 0 < (herm 1 x x).re`. Introduce `x _ hx0`. Simplify using `only [herm, Matrix.one_mulVec, hE, Complex.ofReal_re]`.

Take `⟨i, hi⟩` from `Function.ne_iff.mp hx0`. Conclude with `lt_of_lt_of_le (Complex.normSq_pos.mpr hi) (Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (x j)) (Finset.mem_univ i))`. Establish `hcs1` using `c2x3_cs 1 (by simp) ⊤ hpos1 v w Submodule.mem_top Submodule.mem_top`. Simplify using `only [herm, Matrix.one_mulVec, hE, Complex.ofReal_re] at hcs1`. Use `set ρ := (herm H w w).re with hρ`.

Establish `hρ2 : ρ ^ 2 ≤ (c * Ev) ^ 2`. Establish `h1 : ρ ^ 2 ≤ Complex.normSq (herm H w w)`. Rewrite using `[hρ, Complex.normSq_apply]`. Use polynomial arithmetic with `[sq_nonneg (herm H w w).im]`. Rewrite `h1` using `[hwu w hwU]`.

Establish `h2 : Complex.normSq (star w ⬝ᵥ v) ≤ Ev * Ew` using `hcs1`. Establish `h3 : Ev * Ew ≤ Ev * (c ^ 2 * Ev)` using `mul_le_mul_of_nonneg_left hw2 (hEnn v)`. Use the polynomial consequences of the given equalities and inequalities. Establish `hcE : 0 ≤ c * Ev` using `mul_nonneg hc (hEnn v)`. Establish `hρle : ρ ≤ c * Ev` using `by nlinarith`.

Establish `hvv` using `hcsU`. Establish `hhv : 0 ≤ (herm H v v).re`. Distinguish the cases in `h0 : v = 0`. Substitute `h0` using the available equality. Simplify using `[herm]`.

Conclude with `le_of_lt (hpos v hv h0)`. Distinguish the cases in `hE0 : Ev = 0`. Rewrite using `[hE0]`. Conclude with `mul_nonneg hc hhv`. Establish `hEpos : 0 < Ev` using `lt_of_le_of_ne (hEnn v) (Ne.symm hE0)`.

Establish `: Ev * Ev ≤ c * Ev * (herm H v v).re` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem projection_property : C2.ProjClaim := by
  intro n H P U c hH hH2 hpos hPU horth hc hPn v hv
  have hE : ∀ x : Fin n → ℂ, star x ⬝ᵥ x = ((∑ i, Complex.normSq (x i) : ℝ) : ℂ) := by
    intro x
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self]
  have hEnn : ∀ x : Fin n → ℂ, 0 ≤ ∑ i, Complex.normSq (x i) :=
    fun x => Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)
  have hHv : ∀ u : Fin n → ℂ, herm H (H *ᵥ v) u = star u ⬝ᵥ v := by
    intro u; simp only [herm, Matrix.mulVec_mulVec, hH2, Matrix.one_mulVec]
  set w := P *ᵥ (H *ᵥ v) with hw
  have hwU : w ∈ U := hPU _
  have hwu : ∀ u ∈ U, herm H w u = star u ⬝ᵥ v := by
    intro u hu
    have := horth (H *ᵥ v) u hu
    simp only [herm, Matrix.mulVec_sub, dotProduct_sub, sub_eq_zero] at this
    rw [← hHv u]; simp only [herm]; exact this.symm

  have hEH : ∑ i, Complex.normSq ((H *ᵥ v) i) = ∑ i, Complex.normSq (v i) := by
    have h1 := hE (H *ᵥ v)
    have h2 := hE v
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hH, hH2, Matrix.one_mulVec, h2] at h1
    exact_mod_cast h1.symm
  set Ev := ∑ i, Complex.normSq (v i) with hEv
  set Ew := ∑ i, Complex.normSq (w i) with hEw
  have hw2 : Ew ≤ c ^ 2 * Ev := by rw [← hEH]; exact hPn _

  have hcsU := c2x3_cs H hH U hpos w v hwU hv
  rw [hwu v hv, hE v, Complex.normSq_ofReal] at hcsU

  have hpos1 : ∀ x ∈ (⊤ : Submodule ℂ (Fin n → ℂ)), x ≠ 0 → 0 < (herm 1 x x).re := by
    intro x _ hx0
    simp only [herm, Matrix.one_mulVec, hE, Complex.ofReal_re]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx0
    exact lt_of_lt_of_le (Complex.normSq_pos.mpr hi)
      (Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (x j)) (Finset.mem_univ i))
  have hcs1 := c2x3_cs 1 (by simp) ⊤ hpos1 v w Submodule.mem_top Submodule.mem_top
  simp only [herm, Matrix.one_mulVec, hE, Complex.ofReal_re] at hcs1

  set ρ := (herm H w w).re with hρ
  have hρ2 : ρ ^ 2 ≤ (c * Ev) ^ 2 := by
    have h1 : ρ ^ 2 ≤ Complex.normSq (herm H w w) := by
      rw [hρ, Complex.normSq_apply]; nlinarith [sq_nonneg (herm H w w).im]
    rw [hwu w hwU] at h1
    have h2 : Complex.normSq (star w ⬝ᵥ v) ≤ Ev * Ew := hcs1
    have h3 : Ev * Ew ≤ Ev * (c ^ 2 * Ev) := mul_le_mul_of_nonneg_left hw2 (hEnn v)
    nlinarith
  have hcE : 0 ≤ c * Ev := mul_nonneg hc (hEnn v)
  have hρle : ρ ≤ c * Ev := by nlinarith
  have hvv := hcsU
  have hhv : 0 ≤ (herm H v v).re := by
    by_cases h0 : v = 0
    · subst h0; simp [herm]
    · exact le_of_lt (hpos v hv h0)
  by_cases hE0 : Ev = 0
  · rw [hE0]; exact mul_nonneg hc hhv
  · have hEpos : 0 < Ev := lt_of_le_of_ne (hEnn v) (Ne.symm hE0)
    have : Ev * Ev ≤ c * Ev * (herm H v v).re := by nlinarith
    nlinarith

end Formalism.FourierDecayAlt.P
