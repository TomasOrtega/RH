import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PackingGeometricMeanSeparated

open GlobalTheory.SepPer Finset

namespace GlobalTheory.SepSum

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/- English proof (translation)
Rewrite using `[Matrix.frobenius_norm_def, hsn, Real.sqrt_eq_rpow]`. Use `congr 1`. Simplify using `only [Real.rpow_two]`.
-/
theorem hsn_eq_norm {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : hsn X = ‖X‖ := by
  rw [Matrix.frobenius_norm_def, hsn, Real.sqrt_eq_rpow]
  congr 1
  simp only [Real.rpow_two]

/- English proof (translation)
The claim follows from `Real.sqrt_nonneg _`.
-/
theorem hsn_nonneg {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hsn X := Real.sqrt_nonneg _

/- English proof (translation)
Rewrite using `[Module.finrank_matrix, Complex.finrank_real_complex]`. Simplify using `only [Fintype.card_fin]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem finrank_mat (n : ℕ) : Module.finrank ℝ (Matrix (Fin n) (Fin n) ℂ) = 2 * n ^ 2 := by
  rw [Module.finrank_matrix, Complex.finrank_real_complex]
  simp only [Fintype.card_fin]
  ring

/- English proof (translation)
Establish `h0 : ⌊1 + x⌋₊ ≠ 0` using `(Nat.floor_pos.mpr (by linarith)).ne'`. Prove the components needed by the constructor for the conclusion. Establish `h1` using `Nat.pow_log_le_self 2 h0`. Establish `h2 : ((2 ^ Nat.log 2 ⌊1 + x⌋₊ : ℕ) : ℝ) ≤ (⌊1 + x⌋₊ : ℝ)` using `by exact_mod_cast h1`. Move the coercions through the operations in `at h2`.

Conclude with `h2.trans (Nat.floor_le (by linarith))`. Establish `h1` using `Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌊1 + x⌋₊`. Establish `h2 : ((⌊1 + x⌋₊ + 1 : ℕ) : ℝ) ≤ ((2 ^ (Nat.log 2 ⌊1 + x⌋₊).succ : ℕ) : ℝ)` using `by exact_mod_cast h1`. Move the coercions through the operations in `at h2`. Conclude with `(Nat.lt_floor_add_one _).trans_le h2`.
-/
theorem dyadic (x : ℝ) (hx : 0 ≤ x) :
    (2 : ℝ) ^ Nat.log 2 ⌊1 + x⌋₊ ≤ 1 + x ∧ 1 + x < (2 : ℝ) ^ (Nat.log 2 ⌊1 + x⌋₊ + 1) := by
  have h0 : ⌊1 + x⌋₊ ≠ 0 := (Nat.floor_pos.mpr (by linarith)).ne'
  constructor
  · have h1 := Nat.pow_log_le_self 2 h0
    have h2 : ((2 ^ Nat.log 2 ⌊1 + x⌋₊ : ℕ) : ℝ) ≤ (⌊1 + x⌋₊ : ℝ) := by exact_mod_cast h1
    push_cast at h2
    exact h2.trans (Nat.floor_le (by linarith))
  · have h1 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌊1 + x⌋₊
    have h2 : ((⌊1 + x⌋₊ + 1 : ℕ) : ℝ) ≤ ((2 ^ (Nat.log 2 ⌊1 + x⌋₊).succ : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    exact (Nat.lt_floor_add_one _).trans_le h2

/- English proof (translation)
Use `set M := T.sup fun j => univ.sup j`. Establish `hsub : T ⊆ Fintype.piFinset fun _ : ι => range (M + 1)`. Introduce `j hj`. Rewrite using `[Fintype.mem_piFinset]`. Introduce `v`.

Rewrite using `[mem_range, Nat.lt_succ_iff]`. Conclude with `(le_sup (f := j) (mem_univ v)).trans (le_sup (f := fun j => univ.sup j) hj)`. Use `(sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => by positivity).trans ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_univ_sum (fun _ : ι => range (M + 1)) (fun _ k => ((2 : ℝ) ^ k)⁻¹)]`. Combine the equalities or inequalities in the displayed calculation.

Use `sum_geometric_two_le (M + 1)` as an intermediate fact. Simplify `this` using `[one_div, inv_pow]`. Use `_ = 2 ^ Fintype.card ι := by simp`.
-/
theorem sum_prod_inv_two_le {ι : Type} [Fintype ι] [DecidableEq ι] (T : Finset (ι → ℕ)) :
    ∑ j ∈ T, ∏ v, ((2 : ℝ) ^ j v)⁻¹ ≤ 2 ^ Fintype.card ι := by
  set M := T.sup fun j => univ.sup j
  have hsub : T ⊆ Fintype.piFinset fun _ : ι => range (M + 1) := by
    intro j hj
    rw [Fintype.mem_piFinset]
    intro v
    rw [mem_range, Nat.lt_succ_iff]
    exact (le_sup (f := j) (mem_univ v)).trans (le_sup (f := fun j => univ.sup j) hj)
  refine (sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => by positivity).trans ?_
  rw [← Finset.prod_univ_sum (fun _ : ι => range (M + 1)) (fun _ k => ((2 : ℝ) ^ k)⁻¹)]
  calc ∏ v : ι, ∑ k ∈ range (M + 1), ((2 : ℝ) ^ k)⁻¹ ≤ ∏ _v : ι, (2 : ℝ) :=
        prod_le_prod (fun _ _ => by positivity) fun v _ => by
          have := sum_geometric_two_le (M + 1)
          simpa [one_div, inv_pow] using this
    _ = 2 ^ Fintype.card ι := by simp

/- English proof (translation)
Use `set f := Fintype.card ι with hf`. Use `set N := 2 * n ^ 2 with hN`. Establish `hf0 : f ≠ 0` using `Fintype.card_ne_zero`. Establish `hN1 : 1 ≤ N` using `by have : 1 ≤ n ^ 2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hn); omega`. Establish `hP` using `GlobalTheory.packing_geometric_mean_separated ι (fun _ => Matrix (Fin n) (Fin n) ℂ) N hN1 (fun _ => finrank_mat n) la (T : Set _) (fun v => (2 : ℝ) ^ (j v + 1)) hla (fun v => by positivity) ?sep`.

Use `case sep =>`. Introduce `s hs s' hs' hne`. Establish `h` using `hT s hs s' hs' hne`. Simplify using `only [← hsn_eq_norm]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hset : {s ∈ (T : Set (ι → Matrix (Fin n) (Fin n) ℂ)) | ∀ v, ‖s v‖ ≤ (2 : ℝ) ^ (j v + 1)} = (T : Set _)`. Use extensionality with `s`. Simplify using `only [Set.mem_setOf_eq, Finset.mem_coe, and_iff_left_iff_imp]`. Introduce `hs v`. Rewrite using `[← hsn_eq_norm]`.

Conclude with `hj s hs v`. Establish `hc` using `hP.2`. Rewrite `hc` using `[hset, Set.ncard_coe_finset]`. Use `set Pr : ℝ := ∏ v, (2 : ℝ) ^ (j v + 1) with hPr`. Establish `hPr' : Pr = (∏ v, (2 : ℝ) ^ j v) * 2 ^ f`.

Simplify using `only [hPr, pow_succ, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hf]`. Establish `hPr1 : 1 ≤ Pr`. Rewrite using `[hPr, Finset.prod_pow_eq_pow_sum]`. Conclude with `one_le_pow₀ (by norm_num)`. Establish `hPr0 : 0 ≤ Pr` using `by linarith`.

Use `set G : ℝ := Pr ^ ((1 : ℝ) / f) with hG`. Establish `hGf : G ^ f = Pr` using `by rw [hG, one_div, Real.rpow_inv_natCast_pow hPr0 hf0]`. Establish `hG1 : 1 ≤ G` using `Real.one_le_rpow hPr1 (by positivity)`. Establish `h3 : 1 + 2 * G / la ≤ 3 * G / la`. Establish `: G ≤ G / la` using `le_div_self (by linarith) hla hla1`.

Establish `e : 3 * G / la = G / la + 2 * G / la` using `by ring`. Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[div_eq_mul_inv, mul_pow, mul_pow, ← pow_mul, mul_comm f N]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = 3 ^ (N * f) * la⁻¹ ^ (N * f) * Pr ^ N := by rw [hGf]`. Use `_ = _ := by`. Rewrite using `[hPr', show (6 : ℝ) = 3 * 2 by norm_num, mul_pow, mul_pow, ← pow_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem card_box_le {ι : Type} [Fintype ι] [Nonempty ι] (n : ℕ) (hn : n ≠ 0) (la : ℝ) (hla : 0 < la) (hla1 : la ≤ 1)
    (T : Finset (ι → Matrix (Fin n) (Fin n) ℂ))
    (hT : ∀ s ∈ T, ∀ s' ∈ T, s ≠ s' → la ^ Fintype.card ι ≤ ∏ v, hsn (s v - s' v))
    (j : ι → ℕ) (hj : ∀ s ∈ T, ∀ v, hsn (s v) ≤ (2 : ℝ) ^ (j v + 1)) :
    (T.card : ℝ) ≤ 6 ^ (2 * n ^ 2 * Fintype.card ι) * la⁻¹ ^ (2 * n ^ 2 * Fintype.card ι) *
      (∏ v, (2 : ℝ) ^ j v) ^ (2 * n ^ 2) := by
  set f := Fintype.card ι with hf
  set N := 2 * n ^ 2 with hN
  have hf0 : f ≠ 0 := Fintype.card_ne_zero
  have hN1 : 1 ≤ N := by have : 1 ≤ n ^ 2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hn); omega
  have hP := GlobalTheory.packing_geometric_mean_separated ι (fun _ => Matrix (Fin n) (Fin n) ℂ) N hN1
    (fun _ => finrank_mat n) la (T : Set _) (fun v => (2 : ℝ) ^ (j v + 1)) hla (fun v => by positivity) ?sep
  case sep =>
    intro s hs s' hs' hne
    have h := hT s hs s' hs' hne
    simp only [← hsn_eq_norm]
    calc la = (la ^ f) ^ ((1 : ℝ) / f) := by rw [one_div, Real.pow_rpow_inv_natCast hla.le hf0]
      _ ≤ _ := Real.rpow_le_rpow (by positivity) h (by positivity)
  have hset : {s ∈ (T : Set (ι → Matrix (Fin n) (Fin n) ℂ)) | ∀ v, ‖s v‖ ≤ (2 : ℝ) ^ (j v + 1)} = (T : Set _) := by
    ext s
    simp only [Set.mem_setOf_eq, Finset.mem_coe, and_iff_left_iff_imp]
    intro hs v
    rw [← hsn_eq_norm]
    exact hj s hs v
  have hc := hP.2
  rw [hset, Set.ncard_coe_finset] at hc
  set Pr : ℝ := ∏ v, (2 : ℝ) ^ (j v + 1) with hPr
  have hPr' : Pr = (∏ v, (2 : ℝ) ^ j v) * 2 ^ f := by
    simp only [hPr, pow_succ, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hf]
  have hPr1 : 1 ≤ Pr := by
    rw [hPr, Finset.prod_pow_eq_pow_sum]
    exact one_le_pow₀ (by norm_num)
  have hPr0 : 0 ≤ Pr := by linarith
  set G : ℝ := Pr ^ ((1 : ℝ) / f) with hG
  have hGf : G ^ f = Pr := by rw [hG, one_div, Real.rpow_inv_natCast_pow hPr0 hf0]
  have hG1 : 1 ≤ G := Real.one_le_rpow hPr1 (by positivity)
  have h3 : 1 + 2 * G / la ≤ 3 * G / la := by
    have : G ≤ G / la := le_div_self (by linarith) hla hla1
    have e : 3 * G / la = G / la + 2 * G / la := by ring
    rw [e]; linarith
  calc (T.card : ℝ) ≤ (1 + 2 * G / la) ^ (N * f) := hc
    _ ≤ (3 * G / la) ^ (N * f) := pow_le_pow_left₀ (by positivity) h3 _
    _ = 3 ^ (N * f) * la⁻¹ ^ (N * f) * (G ^ f) ^ N := by
      rw [div_eq_mul_inv, mul_pow, mul_pow, ← pow_mul, mul_comm f N]; ring
    _ = 3 ^ (N * f) * la⁻¹ ^ (N * f) * Pr ^ N := by rw [hGf]
    _ = _ := by
      rw [hPr', show (6 : ℝ) = 3 * 2 by norm_num, mul_pow, mul_pow, ← pow_mul]
      ring

/- English proof (translation)
Introduce `ι _ _ n`. Use `⟨6 ^ (2 * n ^ 2 * Fintype.card ι) * 2 ^ Fintype.card ι, by positivity, ?_⟩` and prove the remaining obligations. Introduce `la hla hla1 S hS`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Establish `hcard : S.card ≤ 1` using `Finset.card_le_one.mpr fun a _ b _ => funext fun v => Matrix.ext fun i _ => i.elim0`.

Establish `hterm : ∀ s ∈ S, ∏ v, ((1 + hsn (s v)) ^ (2 * 0 ^ 2 + 1))⁻¹ ≤ (1 : ℝ)` using `fun s _ => Finset.prod_le_one (fun v _ => by have := hsn_nonneg (s v); positivity) fun v _ => inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [hsn_nonneg (s v)]))`. Combine the equalities or inequalities in the displayed calculation. Establish `: (1 : ℝ) ≤ 2 ^ Fintype.card ι` using `one_le_pow₀ (by norm_num)`. Simplify using `using this`. Use `set N := 2 * n ^ 2 with hN set f := Fintype.card ι with hf`.

Set `jf : (ι → Matrix (Fin n) (Fin n) ℂ) → ι → ℕ` to `fun s v => Nat.log 2 ⌊1 + hsn (s v)⌋₊`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to (g := jf) (t := S.image jf) (fun s hs => Finset.mem_image_of_mem jf hs)]`. Establish `hbox : ∀ j ∈ S.image jf, ∑ s ∈ S.filter (fun s => jf s = j), ∏ v, ((1 + hsn (s v)) ^ (N + 1))⁻¹ ≤ 6 ^ (N * f) * la⁻¹ ^ (N * f) * ∏ v, ((2 : ℝ) ^ j v)⁻¹`. Introduce `j _`. Establish `hb : ∀ s ∈ S.filter (fun s => jf s = j), ∏ v, ((1 + hsn (s v)) ^ (N + 1))⁻¹ ≤ ∏ v, (((2 : ℝ) ^ j v) ^ (N + 1))⁻¹`.

Introduce `s hs`. Rewrite `hs` using `[Finset.mem_filter]`. Use `prod_le_prod (fun v _ => by have := hsn_nonneg (s v); positivity) fun v _ => ?_` and prove the remaining obligations. Establish `hd` using `(dyadic _ (hsn_nonneg (s v))).1`. Rewrite using `[← hs.2]`.

Conclude with `inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hd _)`. Establish `hcard` using `card_box_le n hn.ne' la hla hla1 (S.filter (fun s => jf s = j)) (fun s hs s' hs' hne => hS s (mem_filter.1 hs).1 s' (mem_filter.1 hs').1 hne) j (by`. Introduce `s hs v`. Rewrite `hs` using `[mem_filter]`. Establish `hd` using `(dyadic _ (hsn_nonneg (s v))).2`.

Rewrite using `[← hs.2]`. Use the proof step `linarith)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[sum_const, nsmul_eq_mul]`. Use `_ ≤ (6 ^ (N * f) * la⁻¹ ^ (N * f) * (∏ v, (2 : ℝ) ^ j v) ^ N) * ∏ v, (((2 : ℝ) ^ j v) ^ (N + 1))⁻¹ := mul_le_mul_of_nonneg_right hcard (by positivity)`.

Use `_ = _ := by`. Rewrite using `[mul_assoc, ← Finset.prod_pow, ← Finset.prod_mul_distrib]`. Use `congr 1`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Establish `h2 : ((2 : ℝ) ^ j v) ≠ 0` using `by positivity`.

Rewrite using `[pow_succ, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ h2), one_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem sum_weights_le_of_separated : ∀ (ι : Type) [Fintype ι] [Nonempty ι] (n : ℕ), ∃ C : ℝ, 0 ≤ C ∧
    ∀ la : ℝ, 0 < la → la ≤ 1 → ∀ S : Finset (ι → Matrix (Fin n) (Fin n) ℂ),
      (∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → la ^ Fintype.card ι ≤ ∏ v, hsn (s v - s' v)) →
      ∑ s ∈ S, ∏ v, ((1 + hsn (s v)) ^ (2 * n ^ 2 + 1))⁻¹ ≤ C * la⁻¹ ^ (2 * n ^ 2 * Fintype.card ι) := by
  intro ι _ _ n
  classical
  refine ⟨6 ^ (2 * n ^ 2 * Fintype.card ι) * 2 ^ Fintype.card ι, by positivity, ?_⟩
  intro la hla hla1 S hS
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hcard : S.card ≤ 1 :=
      Finset.card_le_one.mpr fun a _ b _ => funext fun v => Matrix.ext fun i _ => i.elim0
    have hterm : ∀ s ∈ S, ∏ v, ((1 + hsn (s v)) ^ (2 * 0 ^ 2 + 1))⁻¹ ≤ (1 : ℝ) := fun s _ =>
      Finset.prod_le_one (fun v _ => by have := hsn_nonneg (s v); positivity)
        fun v _ => inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [hsn_nonneg (s v)]))
    calc _ ≤ ∑ s ∈ S, (1 : ℝ) := sum_le_sum hterm
      _ = S.card := by simp
      _ ≤ 1 := by exact_mod_cast hcard
      _ ≤ _ := by
        have : (1 : ℝ) ≤ 2 ^ Fintype.card ι := one_le_pow₀ (by norm_num)
        simpa using this
  · set N := 2 * n ^ 2 with hN
    set f := Fintype.card ι with hf
    let jf : (ι → Matrix (Fin n) (Fin n) ℂ) → ι → ℕ := fun s v => Nat.log 2 ⌊1 + hsn (s v)⌋₊
    rw [← Finset.sum_fiberwise_of_maps_to (g := jf) (t := S.image jf) (fun s hs => Finset.mem_image_of_mem jf hs)]
    have hbox : ∀ j ∈ S.image jf, ∑ s ∈ S.filter (fun s => jf s = j), ∏ v, ((1 + hsn (s v)) ^ (N + 1))⁻¹ ≤
        6 ^ (N * f) * la⁻¹ ^ (N * f) * ∏ v, ((2 : ℝ) ^ j v)⁻¹ := by
      intro j _
      have hb : ∀ s ∈ S.filter (fun s => jf s = j),
          ∏ v, ((1 + hsn (s v)) ^ (N + 1))⁻¹ ≤ ∏ v, (((2 : ℝ) ^ j v) ^ (N + 1))⁻¹ := by
        intro s hs
        rw [Finset.mem_filter] at hs
        refine prod_le_prod (fun v _ => by have := hsn_nonneg (s v); positivity) fun v _ => ?_
        have hd := (dyadic _ (hsn_nonneg (s v))).1
        rw [← hs.2]
        exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hd _)
      have hcard := card_box_le n hn.ne' la hla hla1 (S.filter (fun s => jf s = j))
        (fun s hs s' hs' hne => hS s (mem_filter.1 hs).1 s' (mem_filter.1 hs').1 hne) j (by
          intro s hs v
          rw [mem_filter] at hs
          have hd := (dyadic _ (hsn_nonneg (s v))).2
          rw [← hs.2]
          linarith)
      calc _ ≤ ∑ s ∈ S.filter (fun s => jf s = j), ∏ v, (((2 : ℝ) ^ j v) ^ (N + 1))⁻¹ := sum_le_sum hb
        _ = (S.filter (fun s => jf s = j)).card * ∏ v, (((2 : ℝ) ^ j v) ^ (N + 1))⁻¹ := by
          rw [sum_const, nsmul_eq_mul]
        _ ≤ (6 ^ (N * f) * la⁻¹ ^ (N * f) * (∏ v, (2 : ℝ) ^ j v) ^ N) * ∏ v, (((2 : ℝ) ^ j v) ^ (N + 1))⁻¹ :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = _ := by
          rw [mul_assoc, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
          congr 1
          refine Finset.prod_congr rfl fun v _ => ?_
          have h2 : ((2 : ℝ) ^ j v) ≠ 0 := by positivity
          rw [pow_succ, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ h2), one_mul]
    calc _ ≤ ∑ j ∈ S.image jf, 6 ^ (N * f) * la⁻¹ ^ (N * f) * ∏ v, ((2 : ℝ) ^ j v)⁻¹ := sum_le_sum hbox
      _ = 6 ^ (N * f) * la⁻¹ ^ (N * f) * ∑ j ∈ S.image jf, ∏ v, ((2 : ℝ) ^ j v)⁻¹ := by rw [mul_sum]
      _ ≤ 6 ^ (N * f) * la⁻¹ ^ (N * f) * 2 ^ f :=
        mul_le_mul_of_nonneg_left (sum_prod_inv_two_le _) (by positivity)
      _ = _ := by ring

end GlobalTheory.SepSum
