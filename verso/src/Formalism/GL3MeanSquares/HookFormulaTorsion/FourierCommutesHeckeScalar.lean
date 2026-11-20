import Mathlib
import Formalism.GL3MeanSquares.FourierTransformKernelSurjective

namespace Formalism.HermitianLattices.LocalLatticeBases

open Finset

/- English proof (translation)
Introduce `t _ ht ε hε v W C N hv`. Establish `ht' : (0:ℝ) ≤ t` using `by exact_mod_cast ht`. Break down `hε with rfl | rfl` into its components or cases. Use `⟨Or.inr (by push_cast; ring), ?_⟩` and prove the remaining obligations. Use `push_cast`.

Rewrite `hv`, the goal using `[abs_le]`. Apply the tactic sequence `constructor <;> linarith [hv.1, hv.2]`. Use `⟨Or.inl (by push_cast; ring), ?_⟩` and prove the remaining obligations. Use `push_cast`. Rewrite `hv`, the goal using `[abs_le]`.

Apply the tactic sequence `constructor <;> linarith [hv.1, hv.2]`.
-/
theorem odd_half_shift_sign_dichotomy_bound : OddHalfShiftSignDichotomyBound := by
  intro t _ ht ε hε v W C N hv
  have ht' : (0:ℝ) ≤ t := by exact_mod_cast ht
  rcases hε with rfl | rfl
  · refine ⟨Or.inr (by push_cast; ring), ?_⟩
    push_cast
    rw [abs_le] at hv ⊢
    constructor <;> linarith [hv.1, hv.2]
  · refine ⟨Or.inl (by push_cast; ring), ?_⟩
    push_cast
    rw [abs_le] at hv ⊢
    constructor <;> linarith [hv.1, hv.2]

/- English proof (translation)
Introduce `ι Ψ p _ W nu C N t hW ht htN hnu`. Establish `: ∑ τ ∈ Ψ, (2 * W τ + C * N + if p τ then nu τ else 0) ≤ ∑ τ ∈ Ψ, (4 * W τ + (C+1) * N)`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `τ hτ`. Use `split_ifs with h`.

Combine the linear relations using `[hnu τ hτ h, hW τ hτ]`. Combine the linear relations using `[hW τ hτ]`. Use `this.trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exponent_loss_per_embedding : ExponentLossPerEmbedding := by
  intro ι Ψ p _ W nu C N t hW ht htN hnu
  have : ∑ τ ∈ Ψ, (2 * W τ + C * N + if p τ then nu τ else 0) ≤ ∑ τ ∈ Ψ, (4 * W τ + (C+1) * N) := by
    apply Finset.sum_le_sum
    intro τ hτ
    split_ifs with h
    · linarith [hnu τ hτ h, hW τ hτ]
    · linarith [hW τ hτ]
  refine this.trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]; ring

/- English proof (translation)
Introduce `n lam sg h`. Establish `e1 : ∑ i, lam i - ∑ i, sg i = lam 0 + ∑ i : Fin n, (lam i.succ - sg i)`. Rewrite using `[Fin.sum_univ_succ, Finset.sum_sub_distrib]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : ∑ i, lam i - ∑ i, sg i = lam (Fin.last n) + ∑ i : Fin n, (lam i.castSucc - sg i)`.

Rewrite using `[Fin.sum_univ_castSucc, Finset.sum_sub_distrib]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[e1]`. Establish `: ∑ i : Fin n, (lam i.succ - sg i) ≤ 0` using `Finset.sum_nonpos (fun i _ => by linarith [(h i).2])`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[e2]`. Establish `: 0 ≤ ∑ i : Fin n, (lam i.castSucc - sg i)` using `Finset.sum_nonneg (fun i _ => by linarith [(h i).1])`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `hn W h1 h2`.

Rewrite using `[e2]`. Establish `: lam (Fin.castSucc ⟨0,hn⟩) - sg ⟨0,hn⟩ ≤ ∑ i : Fin n, (lam i.castSucc - sg i)` using `Finset.single_le_sum (f := fun i : Fin n => lam i.castSucc - sg i) (fun i _ => by linarith [(h i).1]) (Finset.mem_univ _)`. Establish `h0 : (Fin.castSucc ⟨0,hn⟩ : Fin (n+1)) = 0` using `rfl`. Rewrite `this` using `[h0]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem interlacing_degree_difference : InterlacingDegreeDifference := by
  intro n lam sg h
  have e1 : ∑ i, lam i - ∑ i, sg i = lam 0 + ∑ i : Fin n, (lam i.succ - sg i) := by
    rw [Fin.sum_univ_succ, Finset.sum_sub_distrib]; ring
  have e2 : ∑ i, lam i - ∑ i, sg i = lam (Fin.last n) + ∑ i : Fin n, (lam i.castSucc - sg i) := by
    rw [Fin.sum_univ_castSucc, Finset.sum_sub_distrib]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [e1]
    have : ∑ i : Fin n, (lam i.succ - sg i) ≤ 0 := Finset.sum_nonpos (fun i _ => by linarith [(h i).2])
    linarith
  · rw [e2]
    have : 0 ≤ ∑ i : Fin n, (lam i.castSucc - sg i) := Finset.sum_nonneg (fun i _ => by linarith [(h i).1])
    linarith
  · intro hn W h1 h2
    rw [e2]
    have : lam (Fin.castSucc ⟨0,hn⟩) - sg ⟨0,hn⟩ ≤ ∑ i : Fin n, (lam i.castSucc - sg i) :=
      Finset.single_le_sum (f := fun i : Fin n => lam i.castSucc - sg i) (fun i _ => by linarith [(h i).1]) (Finset.mem_univ _)
    have h0 : (Fin.castSucc ⟨0,hn⟩ : Fin (n+1)) = 0 := rfl
    rw [h0] at this
    linarith

/- English proof (translation)
Introduce `R _ M M' _ _ _ _ U D G U' D' G' K c a a' h1 h2 h3 h4`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem fourier_commutes_hecke_scalar : FourierCommutesHeckeScalar := by
  intro R _ M M' _ _ _ _ U D G U' D' G' K c a a' h1 h2 h3 h4
  calc a' • (K ∘ₗ D ∘ₗ G) = (a' • LinearMap.id) ∘ₗ (K ∘ₗ D ∘ₗ G) := by ext; simp
    _ = D' ∘ₗ (U' ∘ₗ K) ∘ₗ D ∘ₗ G := by rw [← h2]; rfl
    _ = c • (D' ∘ₗ K ∘ₗ (U ∘ₗ D) ∘ₗ G) := by rw [h1]; ext; simp
    _ = (c * a) • (D' ∘ₗ (K ∘ₗ G)) := by rw [h3]; ext; simp [mul_smul]
    _ = _ := by rw [h4]

/- English proof (translation)
Introduce `q _ n n' w ph c fW`. Simplify using `[kerK, Matrix.smul_vecMul]`.
-/
theorem hecke_kernel_scalar_invariance : HeckeKernelScalarInvariance := by
  intro q _ n n' w ph c fW
  simp [kerK, Matrix.smul_vecMul]

/- English proof (translation)
Introduce `R _ M _ _ A N`. Apply `Module.length_le_of_injective (Submodule.mapQ (N.comap A.subtype) N A.subtype le_rfl)` to reduce the goal to its premises. Rewrite using `[← LinearMap.ker_eq_bot, Submodule.ker_mapQ]`. Simplify using the standard rewrite rules.
-/
theorem quotient_length_embedding_bound : QuotientLengthEmbeddingBound := by
  intro R _ M _ _ A N
  apply Module.length_le_of_injective (Submodule.mapQ (N.comap A.subtype) N A.subtype le_rfl)
  rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ]
  simp

/- English proof (translation)
Introduce `a b _ _ _ _ _ _ A B hA hB`. Rewrite using `[Matrix.det_kronecker, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]`. Establish `ha : (Fintype.card a : ℝ) ≠ 0` using `by exact_mod_cast Fintype.card_ne_zero`. Establish `hb : (Fintype.card b : ℝ) ≠ 0` using `by exact_mod_cast Fintype.card_ne_zero`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem slope_kronecker_formula : SlopeTensorProductAdditive := by
  intro a b _ _ _ _ _ _ A B hA hB
  rw [Matrix.det_kronecker, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  have ha : (Fintype.card a : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hb : (Fintype.card b : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  ring

/- English proof (translation)
Introduce `F _ n f g e he`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Use function extensionality and compare the values at `j`. Use `h1 (Pi.single j 1 - f j • e) (by simp [dotProduct_sub, he])` as an intermediate fact.

Simplify using `[dotProduct_sub, h2] at this`. Conclude with `(sub_eq_zero.mp this)`. Introduce and unpack `rfl`. Conclude with `⟨fun _ h => h, he⟩`.
-/
theorem primitive_orbit_functional_unique : PrimitiveOrbitFunctionalUnique := by
  intro F _ n f g e he
  constructor
  · rintro ⟨h1, h2⟩
    funext j
    have := h1 (Pi.single j 1 - f j • e) (by simp [dotProduct_sub, he])
    simp [dotProduct_sub, h2] at this
    exact (sub_eq_zero.mp this)
  · rintro rfl
    exact ⟨fun _ h => h, he⟩

/- English proof (translation)
Introduce `k lam a W b' h0 hW hl`. Establish `hk : (0:ℚ) < (k:ℚ) + 2` using `by positivity`. Establish `hW0 : 0 ≤ W` using `le_trans (abs_nonneg _) (hW (Fin.last (k+1)) (by simp [Fin.ext_iff]))`. Establish `hb : b' ≤ W`. Use `hW (Fin.last (k+1)) (by simp [Fin.ext_iff])` as an intermediate fact.

Rewrite `this` using `[hl, abs_neg]`. Conclude with `le_trans (le_abs_self _) this`. Rewrite using `[div_add' _ _ _ hk.ne', div_le_div_iff_of_pos_right hk, Fin.sum_univ_succ, h0]`. Establish `: ∑ i : Fin (k+1), (lam i.succ + b') ≤ ∑ i : Fin (k+1), (W + W)`. Apply `Finset.sum_le_sum` to reduce the goal to its premises.

Introduce `i _`. Use `hW i.succ (Fin.succ_ne_zero i)` as an intermediate fact. Combine the linear relations using `[le_trans (le_abs_self _) this]`. Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this`. Move the coercions through the operations in `at this`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem length_bound_under_twist : LemmaB'_twist := by
  intro k lam a W b' h0 hW hl
  have hk : (0:ℚ) < (k:ℚ) + 2 := by positivity
  have hW0 : 0 ≤ W := le_trans (abs_nonneg _) (hW (Fin.last (k+1)) (by simp [Fin.ext_iff]))
  have hb : b' ≤ W := by
    have := hW (Fin.last (k+1)) (by simp [Fin.ext_iff])
    rw [hl, abs_neg] at this
    exact le_trans (le_abs_self _) this
  rw [div_add' _ _ _ hk.ne', div_le_div_iff_of_pos_right hk, Fin.sum_univ_succ, h0]
  have : ∑ i : Fin (k+1), (lam i.succ + b') ≤ ∑ i : Fin (k+1), (W + W) := by
    apply Finset.sum_le_sum
    intro i _
    have := hW i.succ (Fin.succ_ne_zero i)
    linarith [le_trans (le_abs_self _) this]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  push_cast at this
  nlinarith

/- English proof (translation)
Introduce `ι TT a W L k m f q e logP muM0 muRam muN EP E0 Eprice hL hk hm hf hq ha hW h1 h2 h3 h4`. Establish `hk0 : 0 < k` using `by linarith`. Establish `key : ∑ τ ∈ TT, m * (a τ / k + 3 * W τ + k) * (1 + 2 * f / q) ≤ m / k * (∑ τ ∈ TT, a τ) + ∑ τ ∈ TT, (m * (3 * W τ + k) * (1 + 2 * f / q) + m * f / (2 * k))`. Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`. Apply `Finset.sum_le_sum` to reduce the goal to its premises.

Introduce `τ hτ`. Take `⟨h0, h4a⟩` from `ha τ hτ`. Establish `: a τ / q ≤ 1 / 4` using `by rw [div_le_iff₀ hq]; linarith`. Establish `e1 : m * (a τ / k + 3 * W τ + k) * (1 + 2 * f / q) = m / k * a τ + m * (3 * W τ + k) * (1 + 2 * f / q) + (2 * m * f / k) * (a τ / q)` using `by field_simp; ring`. Establish `e2 : m * f / (2 * k) = (2 * m * f / k) * (1/4)` using `by field_simp; ring`.

Rewrite using `[e1, e2]`. Establish `: (2 * m * f / k) * (a τ / q) ≤ (2 * m * f / k) * (1/4)` using `mul_le_mul_of_nonneg_left this (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `key2` using `mul_le_mul_of_nonneg_right key hL.le`. Establish `e3 : -(1 - (m + 1) / k) * (∑ τ ∈ TT, a τ) * L = -(∑ τ ∈ TT, a τ) * L + (∑ τ ∈ TT, a τ) / k * L + m / k * (∑ τ ∈ TT, a τ) * L` using `by field_simp; ring`.

Rewrite using `[e3]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem joint_coefficient_formula : Joint_coef := by
  intro ι TT a W L k m f q e logP muM0 muRam muN EP E0 Eprice hL hk hm hf hq ha hW h1 h2 h3 h4
  have hk0 : 0 < k := by linarith
  have key : ∑ τ ∈ TT, m * (a τ / k + 3 * W τ + k) * (1 + 2 * f / q) ≤
      m / k * (∑ τ ∈ TT, a τ) + ∑ τ ∈ TT, (m * (3 * W τ + k) * (1 + 2 * f / q) + m * f / (2 * k)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro τ hτ
    obtain ⟨h0, h4a⟩ := ha τ hτ
    have : a τ / q ≤ 1 / 4 := by rw [div_le_iff₀ hq]; linarith
    have e1 : m * (a τ / k + 3 * W τ + k) * (1 + 2 * f / q) =
      m / k * a τ + m * (3 * W τ + k) * (1 + 2 * f / q) + (2 * m * f / k) * (a τ / q) := by
      field_simp; ring
    have e2 : m * f / (2 * k) = (2 * m * f / k) * (1/4) := by field_simp; ring
    rw [e1, e2]
    have : (2 * m * f / k) * (a τ / q) ≤ (2 * m * f / k) * (1/4) :=
      mul_le_mul_of_nonneg_left this (by positivity)
    linarith
  have key2 := mul_le_mul_of_nonneg_right key hL.le
  have e3 : -(1 - (m + 1) / k) * (∑ τ ∈ TT, a τ) * L = -(∑ τ ∈ TT, a τ) * L + (∑ τ ∈ TT, a τ) / k * L + m / k * (∑ τ ∈ TT, a τ) * L := by
    field_simp; ring
  rw [e3]
  nlinarith

/- English proof (translation)
Introduce `ι Ψ TT VV W bp m t f N C1 C2 e1 hV hm ht htN hf hC1 hC2 hW hb hWb he`. Establish `hN : 1 ≤ N` using `by linarith`. Use `set A := ∑ τ ∈ Ψ, W τ with hA`. Establish `hA0 : 0 ≤ A` using `Finset.sum_nonneg hW`. Use `set Bs := ∑ τ ∈ TT, (bp τ + N) with hB`.

Establish `hB0 : 0 ≤ Bs` using `Finset.sum_nonneg (fun τ h => by linarith [hb τ h])`. Establish `s1 : ∑ τ ∈ VV, (t + 1 + 2 * W τ + C2 * N) ≤ (C2 + 4) * Bs`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `τ h`.

Use `hWb τ h` as an intermediate fact. Use `hb τ (hV h)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Use `_ ≤ ∑ τ ∈ TT, (C2 + 4) * (bp τ + N) := by`. Apply `Finset.sum_le_sum_of_subset_of_nonneg hV` to reduce the goal to its premises.

Introduce `τ h _`. Use `hb τ h` as an intermediate fact. Check the signs of the components of the expression. Use `_ = _ := by rw [Finset.mul_sum]`. Establish `s2 : (∑ τ ∈ VV, (t + 1 + 2 * W τ + C2 * N)) * (m * (m + 1) / 2) ≤ (C2 + 4) * Bs * (m * m)`.

Combine the equalities or inequalities in the displayed calculation. Establish `s3 : m * e1 ≤ m * (4 * A + C1 * f * N)` using `mul_le_mul_of_nonneg_left he (by linarith)`. Establish `s4 : C1 * f * N * m ≤ C1 * f * N * (m * m)` using `mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)`. Establish `p1 : 0 ≤ (C1 + C2 + 5) * m * A` using `by positivity`. Establish `p2 : 0 ≤ (C2 + 9) * m * (f * m * N)` using `by positivity`.

Establish `p3 : 0 ≤ (C1 + 5) * m * (m * Bs)` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem exponent_total_bound : ExponentTotalBound := by
  intro ι Ψ TT VV W bp m t f N C1 C2 e1 hV hm ht htN hf hC1 hC2 hW hb hWb he
  have hN : 1 ≤ N := by linarith
  set A := ∑ τ ∈ Ψ, W τ with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg hW
  set Bs := ∑ τ ∈ TT, (bp τ + N) with hB
  have hB0 : 0 ≤ Bs := Finset.sum_nonneg (fun τ h => by linarith [hb τ h])
  have s1 : ∑ τ ∈ VV, (t + 1 + 2 * W τ + C2 * N) ≤ (C2 + 4) * Bs := by
    calc _ ≤ ∑ τ ∈ VV, (C2 + 4) * (bp τ + N) := by
          apply Finset.sum_le_sum
          intro τ h
          have := hWb τ h
          have := hb τ (hV h)
          nlinarith
      _ ≤ ∑ τ ∈ TT, (C2 + 4) * (bp τ + N) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hV
          intro τ h _
          have := hb τ h
          positivity
      _ = _ := by rw [Finset.mul_sum]
  have s2 : (∑ τ ∈ VV, (t + 1 + 2 * W τ + C2 * N)) * (m * (m + 1) / 2) ≤ (C2 + 4) * Bs * (m * m) := by
    calc _ ≤ (C2 + 4) * Bs * (m * (m + 1) / 2) := mul_le_mul_of_nonneg_right s1 (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  have s3 : m * e1 ≤ m * (4 * A + C1 * f * N) := mul_le_mul_of_nonneg_left he (by linarith)
  have s4 : C1 * f * N * m ≤ C1 * f * N * (m * m) := mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  have p1 : 0 ≤ (C1 + C2 + 5) * m * A := by positivity
  have p2 : 0 ≤ (C2 + 9) * m * (f * m * N) := by positivity
  have p3 : 0 ≤ (C1 + 5) * m * (m * Bs) := by positivity
  nlinarith

/- English proof (translation)
Introduce `K _ _ α hα h0 hle hμ`. Take `⟨n, hn, h⟩` from `NumberField.Embeddings.pow_eq_one_of_norm_le_one K ℂ h0 hα hle`. Conclude with `hμ α ⟨n, hn, h⟩`.
-/
theorem kronecker_root_of_unity' : KroneckerRootOfUnity := by
  intro K _ _ α hα h0 hle hμ
  obtain ⟨n, hn, h⟩ := NumberField.Embeddings.pow_eq_one_of_norm_le_one K ℂ h0 hα hle
  exact hμ α ⟨n, hn, h⟩

/- English proof (translation)
Introduce `q f N hN hf hq`. Establish `h1 : 4 * f + 2 ≤ q` using `by nlinarith`. Establish `hQ : (4:ℝ) * f + 2 ≤ q` using `by exact_mod_cast h1`. Establish `hF : (1:ℝ) ≤ f` using `by exact_mod_cast hf`. Generalize the expression as in `(q:ℝ) = Q at *`.

Establish `hQ2 : 0 < Q - 2` using `by linarith`. Establish `hQ0 : 0 < Q` using `by linarith`. Take `⟨x, hx⟩ : ∃ x, x = 1 / (Q - 2)` from `⟨_, rfl⟩`. Establish `hx0 : 0 < x` using `by rw [hx]; positivity`. Establish `hx1 : x ≤ 1/4` using `by rw [hx, div_le_div_iff₀ hQ2 (by norm_num)]; linarith`.

Establish `e : (Q - 1)/(Q - 2) = 1 + x` using `by rw [hx]; field_simp; ring`. Rewrite using `[e]`. Establish `b1 : 1 + (f:ℝ) * (-x) ≤ (1 + (-x))^f` using `one_add_mul_le_pow (by linarith) f`. Establish `b2 : (1 + x)^f * (1 + (-x))^f ≤ 1`. Apply the tactic sequence `rw [← mul_pow]; apply pow_le_one₀ <;> nlinarith`.

Establish `hfx : (f:ℝ) * x ≤ 1/4` using `by rw [hx, mul_one_div, div_le_div_iff₀ hQ2 (by norm_num)]; linarith`. Establish `pos : 0 < 1 + (f:ℝ) * (-x)` using `by linarith`. Establish `b3 : (1+x)^f * (1 + (f:ℝ) * (-x)) ≤ 1` using `le_trans (mul_le_mul_of_nonneg_left b1 (by positivity)) b2`. Establish `b4 : 1 ≤ (1 + 2*(f:ℝ)/Q) * (1 + (f:ℝ) * (-x))`. Establish `: (1 + 2*(f:ℝ)/Q) * (1 + (f:ℝ) * (-x)) - 1 = (f:ℝ)*(Q-4-2*f)/(Q*(Q-2))`.

Rewrite using `[hx]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : 0 ≤ (f:ℝ)*(Q-4-2*f)/(Q*(Q-2))`. Apply `div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)` to reduce the goal to its premises.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `le_of_mul_le_mul_right (le_trans b3 b4) pos`.
-/
theorem consecutive_ratio_power_bound : ConsecutiveRatioPowerBound := by
  intro q f N hN hf hq
  have h1 : 4 * f + 2 ≤ q := by nlinarith
  have hQ : (4:ℝ) * f + 2 ≤ q := by exact_mod_cast h1
  have hF : (1:ℝ) ≤ f := by exact_mod_cast hf
  generalize (q:ℝ) = Q at *
  have hQ2 : 0 < Q - 2 := by linarith
  have hQ0 : 0 < Q := by linarith
  obtain ⟨x, hx⟩ : ∃ x, x = 1 / (Q - 2) := ⟨_, rfl⟩
  have hx0 : 0 < x := by rw [hx]; positivity
  have hx1 : x ≤ 1/4 := by rw [hx, div_le_div_iff₀ hQ2 (by norm_num)]; linarith
  have e : (Q - 1)/(Q - 2) = 1 + x := by rw [hx]; field_simp; ring
  rw [e]
  have b1 : 1 + (f:ℝ) * (-x) ≤ (1 + (-x))^f := one_add_mul_le_pow (by linarith) f
  have b2 : (1 + x)^f * (1 + (-x))^f ≤ 1 := by
    rw [← mul_pow]; apply pow_le_one₀ <;> nlinarith
  have hfx : (f:ℝ) * x ≤ 1/4 := by rw [hx, mul_one_div, div_le_div_iff₀ hQ2 (by norm_num)]; linarith
  have pos : 0 < 1 + (f:ℝ) * (-x) := by linarith
  have b3 : (1+x)^f * (1 + (f:ℝ) * (-x)) ≤ 1 := le_trans (mul_le_mul_of_nonneg_left b1 (by positivity)) b2
  have b4 : 1 ≤ (1 + 2*(f:ℝ)/Q) * (1 + (f:ℝ) * (-x)) := by
    have : (1 + 2*(f:ℝ)/Q) * (1 + (f:ℝ) * (-x)) - 1 = (f:ℝ)*(Q-4-2*f)/(Q*(Q-2)) := by
      rw [hx]; field_simp; ring
    have h2 : 0 ≤ (f:ℝ)*(Q-4-2*f)/(Q*(Q-2)) := by
      apply div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
    linarith
  exact le_of_mul_le_mul_right (le_trans b3 b4) pos

/- English proof (translation)
Introduce `k n S mult hS hm hn j`. Establish `key : ∀ i : Fin k, ∑ w ∈ S, mult w * w i = ∑ w ∈ S, mult w * w j`. Introduce `i`. Apply `Finset.sum_nbij' (fun w => w ∘ Equiv.swap i j) (fun w => w ∘ Equiv.swap i j)` to reduce the goal to its premises. Introduce `w hw`.

Conclude with `hS _ w hw`. Introduce `w hw`. Conclude with `hS _ w hw`. Introduce `w _`. Use function extensionality and compare the values at `a`.

Simplify using `[Function.comp]`. Introduce `w _`. Use function extensionality and compare the values at `a`. Simplify using `[Function.comp]`. Introduce `w _`.

Simplify using `[hm]`. Establish `: ∑ i : Fin k, ∑ w ∈ S, mult w * w i = k * ∑ w ∈ S, mult w * w j`. Rewrite using `[Finset.sum_congr rfl (fun i _ => key i)]`. Simplify using the standard rewrite rules. Rewrite using `[← this, Finset.sum_comm, Finset.mul_sum]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `w hw`. Rewrite using `[← Finset.mul_sum, hn w hw, mul_comm]`.
-/
theorem length_average_bound : LemmaB'_avg := by
  intro k n S mult hS hm hn j
  have key : ∀ i : Fin k, ∑ w ∈ S, mult w * w i = ∑ w ∈ S, mult w * w j := by
    intro i
    apply Finset.sum_nbij' (fun w => w ∘ Equiv.swap i j) (fun w => w ∘ Equiv.swap i j)
    · intro w hw; exact hS _ w hw
    · intro w hw; exact hS _ w hw
    · intro w _; funext a; simp [Function.comp]
    · intro w _; funext a; simp [Function.comp]
    · intro w _; simp [hm]
  have : ∑ i : Fin k, ∑ w ∈ S, mult w * w i = k * ∑ w ∈ S, mult w * w j := by
    rw [Finset.sum_congr rfl (fun i _ => key i)]; simp
  rw [← this, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [← Finset.mul_sum, hn w hw, mul_comm]

/- English proof (translation)
Introduce `R _ M _ _ U K c h`. Establish `A : ∀ j p, (K j).comp ((U j) ^ p) = (((c j)⁻¹ ^ p : Rˣ) : R) • ((U (j+1)) ^ p).comp (K j)`. Introduce `j p`. Proceed by induction on `p with`. Consider the case `zero => ext`.

Simplify using the standard rewrite rules. Consider the case `succ p ih`. Establish `h' : (K j).comp (U j) = (((c j)⁻¹ : Rˣ) : R) • (U (j+1)).comp (K j)`. Rewrite using `[h j, smul_smul]`. Simplify using the standard rewrite rules.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h', LinearMap.comp_smul, smul_smul, pow_succ, pow_succ]`. Use `push_cast`. Both sides reduce to the same expression. Establish `B : ∀ m p, (chainK R M K m).comp ((U 0) ^ (m + p)) = ((∏ j ∈ range m, (c j)⁻¹ ^ (m - j + p) : Rˣ) : R) • ((U m) ^ p).comp (chainUK R M U K m)`.

Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro p`. Use `ext`. Simplify using `[chainK, chainUK]`.

Consider the case `succ m ih`. Introduce `p`. Establish `e0 : m + 1 + p = m + (p + 1)` using `by ring`. Establish `e1 : ∏ j ∈ range (m+1), (c j)⁻¹ ^ (m + 1 - j + p) = (∏ j ∈ range m, (c j)⁻¹ ^ (m - j + (p+1))) * (c m)⁻¹ ^ (p+1)`. Rewrite using `[Finset.prod_range_succ]`.

Use `congr 1`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `j hj`. Use `Finset.mem_range.mp hj` as an intermediate fact. Use `congr 1`.

Use linear arithmetic over natural numbers and integers. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[ih (p+1), LinearMap.comp_smul]`.

Both sides reduce to the same expression. Use `_ = _ := by`. Rewrite using `[A m (p+1), e1, LinearMap.smul_comp, smul_smul, pow_succ ((U (m+1)))]`. Use `push_cast`. Both sides reduce to the same expression.

Introduce `m`. Use `B m 0` as an intermediate fact. Simplify using `only [add_zero, pow_zero] at this`. Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem commuting_operators : HeckeProductCommutation := by
  intro R _ M _ _ U K c h
  have A : ∀ j p, (K j).comp ((U j) ^ p) = (((c j)⁻¹ ^ p : Rˣ) : R) • ((U (j+1)) ^ p).comp (K j) := by
    intro j p
    induction p with
    | zero => ext; simp
    | succ p ih =>
      have h' : (K j).comp (U j) = (((c j)⁻¹ : Rˣ) : R) • (U (j+1)).comp (K j) := by
        rw [h j, smul_smul]; simp
      calc (K j).comp ((U j) ^ (p+1)) = ((K j).comp ((U j)^p)).comp (U j) := by rw [pow_succ]; rfl
        _ = (((c j)⁻¹ ^ p : Rˣ) : R) • ((U (j+1)) ^ p).comp ((K j).comp (U j)) := by rw [ih]; rfl
        _ = _ := by
          rw [h', LinearMap.comp_smul, smul_smul, pow_succ, pow_succ]; push_cast; rfl
  have B : ∀ m p, (chainK R M K m).comp ((U 0) ^ (m + p)) =
      ((∏ j ∈ range m, (c j)⁻¹ ^ (m - j + p) : Rˣ) : R) • ((U m) ^ p).comp (chainUK R M U K m) := by
    intro m
    induction m with
    | zero => intro p; ext; simp [chainK, chainUK]
    | succ m ih =>
      intro p
      have e0 : m + 1 + p = m + (p + 1) := by ring
      have e1 : ∏ j ∈ range (m+1), (c j)⁻¹ ^ (m + 1 - j + p) =
          (∏ j ∈ range m, (c j)⁻¹ ^ (m - j + (p+1))) * (c m)⁻¹ ^ (p+1) := by
        rw [Finset.prod_range_succ]
        congr 1
        · apply Finset.prod_congr rfl
          intro j hj
          have := Finset.mem_range.mp hj
          congr 1; omega
        · congr 1; omega
      calc (chainK R M K (m+1)).comp ((U 0) ^ (m + 1 + p))
          = (K m).comp ((chainK R M K m).comp ((U 0) ^ (m + (p+1)))) := by rw [e0]; rfl
        _ = ((∏ j ∈ range m, (c j)⁻¹ ^ (m - j + (p+1)) : Rˣ) : R) •
              ((K m).comp ((U m) ^ (p+1))).comp (chainUK R M U K m) := by
            rw [ih (p+1), LinearMap.comp_smul]; rfl
        _ = _ := by
            rw [A m (p+1), e1, LinearMap.smul_comp, smul_smul, pow_succ ((U (m+1)))]; push_cast; rfl
  intro m
  have := B m 0
  simp only [add_zero, pow_zero] at this
  rw [this]; rfl

/- English proof (translation)
Introduce `q _ n n' fW f hfW`. Take `⟨i0, hi0⟩ : ∃ i, fW i ≠ 0` from `by by_contra h; push_neg at h; exact hfW (funext h)`. Establish `add : ∀ x y : Matrix (Fin n') (Fin n) ℤ, compF fW (x - y) = compF fW x - compF fW y`. Introduce `x y`. Use function extensionality and compare the values at `j`.

Simplify using `[compF, mul_sub, Finset.sum_sub_distrib]`. Set `x0 : Matrix (Fin n') (Fin n) ℤ` to `fun i j => if i = i0 then ((f j / fW i0 : ZMod q).val : ℤ) else 0`. Establish `hx0 : compF fW x0 = f`. Use function extensionality and compare the values at `j`. Simplify using `only [compF, x0]`.

Rewrite using `[Finset.sum_eq_single i0]`. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Introduce `i _ hi`. Simplify using `[hi]`.

Simplify using the standard rewrite rules. Use `⟨x0, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x`. Rewrite using `[add, hx0, sub_eq_zero]`. Use function extensionality and compare the values at `j`.

Simplify using `[compF]`. Introduce `x hx l hl`. Establish `: ∑ i, fW i * ((x.mulVec l) i : ZMod q) = ∑ j, compF fW x j * (l j : ZMod q)`. Simplify using `only [compF, Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `j _`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, hx]`. Conclude with `hl`.
-/
theorem coset_decomposition : SupportCosetStructure := by
  intro q _ n n' fW f hfW
  obtain ⟨i0, hi0⟩ : ∃ i, fW i ≠ 0 := by by_contra h; push_neg at h; exact hfW (funext h)
  have add : ∀ x y : Matrix (Fin n') (Fin n) ℤ, compF fW (x - y) = compF fW x - compF fW y := by
    intro x y; funext j; simp [compF, mul_sub, Finset.sum_sub_distrib]
  let x0 : Matrix (Fin n') (Fin n) ℤ := fun i j => if i = i0 then ((f j / fW i0 : ZMod q).val : ℤ) else 0
  have hx0 : compF fW x0 = f := by
    funext j
    simp only [compF, x0]
    rw [Finset.sum_eq_single i0]
    · simp; field_simp
    · intro i _ hi; simp [hi]
    · simp
  refine ⟨x0, ?_, ?_, ?_⟩
  · intro x; rw [add, hx0, sub_eq_zero]
  · funext j; simp [compF]
  · intro x hx l hl
    have : ∑ i, fW i * ((x.mulVec l) i : ZMod q) = ∑ j, compF fW x j * (l j : ZMod q) := by
      simp only [compF, Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro i _; ring
    rw [this, hx]; exact hl

/- English proof (translation)
Introduce `n`. Prove the components needed by the constructor for the conclusion. Introduce `v hv`. Use function extensionality and compare the values at `j`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]`.

Rewrite `hv` using `[Fin.sum_univ_castSucc]`. Use `Fin.lastCases ?_ (fun j => ?_) j` and prove the remaining obligations. Simplify using `[Pi.single_apply, Fin.ext_iff, (Fin.is_lt _).ne']`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `[Pi.single_apply, Fin.ext_iff, (Fin.is_lt _).ne]`.

Simplify using `only [← Fin.ext_iff]`. Simplify using the standard rewrite rules. Establish `: (Matrix.of fun i j : Fin n => ((Pi.single i.castSucc (1 : ℚ) - Pi.single (Fin.last n) 1 : Fin (n + 1) → ℚ) ⬝ᵥ (Pi.single j.castSucc (1 : ℚ) - Pi.single (Fin.last n) 1))) = 1 + Matrix.replicateCol Unit (fun _ => (1:ℚ)) * Matrix.replicateRow Unit (fun _ => (1:ℚ))`. Use extensionality with `i j`. Simplify using `[Matrix.one_apply, Matrix.mul_apply, dotProduct_sub, sub_dotProduct, Pi.single_apply, Fin.ext_iff, (Fin.is_lt _).ne, (Fin.is_lt _).ne']`.

Distinguish the cases in `h : (j:ℕ) = i`. Simplify using `[h]`. Simplify using `[h, Ne.symm h]`. Rewrite using `[this, Matrix.det_one_add_replicateCol_mul_replicateRow]`. Simplify using `[dotProduct]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_zero_lattice_spanning : SumZeroLatticeSpanning := by
  intro n
  constructor
  · intro v hv
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [Fin.sum_univ_castSucc] at hv
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [Pi.single_apply, Fin.ext_iff, (Fin.is_lt _).ne']
      linarith
    · simp [Pi.single_apply, Fin.ext_iff, (Fin.is_lt _).ne]
      simp only [← Fin.ext_iff]; simp
  · have : (Matrix.of fun i j : Fin n =>
        ((Pi.single i.castSucc (1 : ℚ) - Pi.single (Fin.last n) 1 : Fin (n + 1) → ℚ) ⬝ᵥ
          (Pi.single j.castSucc (1 : ℚ) - Pi.single (Fin.last n) 1))) =
        1 + Matrix.replicateCol Unit (fun _ => (1:ℚ)) * Matrix.replicateRow Unit (fun _ => (1:ℚ)) := by
      ext i j
      simp [Matrix.one_apply, Matrix.mul_apply, dotProduct_sub, sub_dotProduct, Pi.single_apply, Fin.ext_iff,
        (Fin.is_lt _).ne, (Fin.is_lt _).ne']
      by_cases h : (j:ℕ) = i
      · simp [h]
      · simp [h, Ne.symm h]
    rw [this, Matrix.det_one_add_replicateCol_mul_replicateRow]
    simp [dotProduct]; ring

/- English proof (translation)
Introduce `R _ M _ _ U hU m`. Proceed by induction on `m with`. Consider the case `zero`. Establish `: LinearMap.range ((U:Module.End R M)^0) = ⊤` using `by rw [pow_zero]; exact LinearMap.range_id`. Rewrite using `[this, zero_smul]`.

Conclude with `Module.length_eq_zero`. Consider the case `succ m ih`. Establish `h1 : LinearMap.range (U^m) ≤ (LinearMap.range (U^(m+1))).comap U`. Introduce and unpack `_ ⟨y, rfl⟩; exact ⟨y, by rw [pow_succ']; rfl⟩`. Establish `h2 : LinearMap.range (U^(m+1)) ≤ (LinearMap.range U).comap LinearMap.id`.

Introduce and unpack `_ ⟨y, rfl⟩; exact ⟨(U^m) y, by rw [pow_succ']; rfl⟩`. Establish `key` using `Module.length_eq_add_of_exact (Submodule.mapQ _ _ U h1) (Submodule.mapQ _ _ LinearMap.id h2) ?_ ?_ ?_`. Rewrite using `[key, ih, succ_nsmul]`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a`.

Proceed by induction on `a using Submodule.Quotient.induction_on with`. Consider the case `H x`. Introduce `hx`. Rewrite `hx` using `[Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]`. Take `⟨y, hy⟩` from `hx`.

Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Use `⟨y, hU ?_⟩` and prove the remaining obligations. Rewrite using `[← hy, pow_succ']`. Both sides reduce to the same expression. Introduce `b`.

Proceed by induction on `b using Submodule.Quotient.induction_on with`. Consider the case `H x => exact ⟨Submodule.Quotient.mk x, by simp⟩`. Introduce `b`. Proceed by induction on `b using Submodule.Quotient.induction_on with`. Consider the case `H x`.

Rewrite using `[Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy⟩`. Conclude with `⟨Submodule.Quotient.mk y, by rw [Submodule.mapQ_apply]; simp at hy; rw [hy]⟩`. Introduce and unpack `⟨a, ha⟩`.

Proceed by induction on `a using Submodule.Quotient.induction_on with`. Consider the case `H y`. Rewrite `ha` using `[Submodule.mapQ_apply, Submodule.Quotient.eq]`. Take `⟨z, hz⟩` from `ha`. Use `⟨y - (U^m) z, ?_⟩` and prove the remaining obligations.

Establish `: (U^(m+1)) z = U ((U^m) z)` using `by rw [pow_succ']; rfl`. Simplify using `only [LinearMap.id_coe, id_eq, map_sub]`. Rewrite using `[← this, hz]`. Normalize the expressions using the abelian group laws.
-/
theorem length_quotient_power_injective : LengthQuotientPowerInjective := by
  intro R _ M _ _ U hU m
  induction m with
  | zero =>
    have : LinearMap.range ((U:Module.End R M)^0) = ⊤ := by rw [pow_zero]; exact LinearMap.range_id
    rw [this, zero_smul]
    exact Module.length_eq_zero
  | succ m ih =>
    have h1 : LinearMap.range (U^m) ≤ (LinearMap.range (U^(m+1))).comap U := by
      rintro _ ⟨y, rfl⟩; exact ⟨y, by rw [pow_succ']; rfl⟩
    have h2 : LinearMap.range (U^(m+1)) ≤ (LinearMap.range U).comap LinearMap.id := by
      rintro _ ⟨y, rfl⟩; exact ⟨(U^m) y, by rw [pow_succ']; rfl⟩
    have key := Module.length_eq_add_of_exact (Submodule.mapQ _ _ U h1) (Submodule.mapQ _ _ LinearMap.id h2) ?_ ?_ ?_
    · rw [key, ih, succ_nsmul]
    · rw [injective_iff_map_eq_zero]
      intro a
      induction a using Submodule.Quotient.induction_on with
      | H x =>
        intro hx
        rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
        obtain ⟨y, hy⟩ := hx
        rw [Submodule.Quotient.mk_eq_zero]
        refine ⟨y, hU ?_⟩
        rw [← hy, pow_succ']; rfl
    · intro b
      induction b using Submodule.Quotient.induction_on with
      | H x => exact ⟨Submodule.Quotient.mk x, by simp⟩
    · intro b
      induction b using Submodule.Quotient.induction_on with
      | H x =>
        rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
        constructor
        · rintro ⟨y, hy⟩
          exact ⟨Submodule.Quotient.mk y, by rw [Submodule.mapQ_apply]; simp at hy; rw [hy]⟩
        · rintro ⟨a, ha⟩
          induction a using Submodule.Quotient.induction_on with
          | H y =>
            rw [Submodule.mapQ_apply, Submodule.Quotient.eq] at ha
            obtain ⟨z, hz⟩ := ha
            refine ⟨y - (U^m) z, ?_⟩
            have : (U^(m+1)) z = U ((U^m) z) := by rw [pow_succ']; rfl
            simp only [LinearMap.id_coe, id_eq, map_sub]
            rw [← this, hz]; abel

/- English proof (translation)
Introduce `R _ M _ _ T hT N c`. Take `⟨V, hV⟩ : ∃ V : Module.End R N, V = T • LinearMap.id` from `⟨_, rfl⟩`. Establish `hVinj : Function.Injective V`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `hT` to reduce the goal to its premises. Use `congrArg Subtype.val hx` as an intermediate fact. Simplify `this` using `[hV]`. Establish `hVc : ∀ x : N, ((V^c) x : M) = T^c • (x:M)`.

Introduce `x`. Proceed by induction on `c with`. Consider the case `zero => simp`. Consider the case `succ c ih`. Establish `hz : ∀ z : N, ((V z : N) : M) = T • (z:M)` using `by intro z; rw [hV]; simp`.

Rewrite using `[pow_succ', Module.End.mul_apply, hz, ih, pow_succ', mul_smul]`. Establish `it` using `length_quotient_power_injective R N V hVinj c`. Rewrite using `[← hV, ← it]`. Establish `h1 : LinearMap.range (V^c) ≤ (N.map ((T ^ c) • (LinearMap.id : M →ₗ[R] M))).comap N.subtype`. Introduce and unpack `_ ⟨y, rfl⟩; exact ⟨y, y.2, by simp [hVc]⟩`.

Establish `h2 : N.map ((T ^ c) • (LinearMap.id : M →ₗ[R] M)) ≤ N.comap LinearMap.id`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `N.smul_mem _ hy`. Establish `key` using `Module.length_eq_add_of_exact (Submodule.mapQ _ _ N.subtype h1) (Submodule.mapQ _ _ LinearMap.id h2) ?_ ?_ ?_`. Rewrite using `[key, add_comm]`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a`. Proceed by induction on `a using Submodule.Quotient.induction_on with`. Consider the case `H x`. Introduce `hx`.

Rewrite `hx` using `[Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]`. Take `⟨y, hy, hyx⟩` from `hx`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Use `⟨⟨y, hy⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[hVc]`.

Simplify using `using hyx`. Introduce `b`. Proceed by induction on `b using Submodule.Quotient.induction_on with`. Consider the case `H x => exact ⟨Submodule.Quotient.mk x, by simp⟩`. Introduce `b`.

Proceed by induction on `b using Submodule.Quotient.induction_on with`. Consider the case `H x`. Rewrite using `[Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Conclude with `⟨Submodule.Quotient.mk ⟨x, hx⟩, by rw [Submodule.mapQ_apply]; rfl⟩`. Introduce and unpack `⟨a, ha⟩`. Proceed by induction on `a using Submodule.Quotient.induction_on with`. Consider the case `H y`. Rewrite `ha` using `[Submodule.mapQ_apply, Submodule.Quotient.eq]`.

Use `h2 ha` as an intermediate fact. Simplify using `only [Submodule.mem_comap, LinearMap.id_coe, id_eq, Submodule.subtype_apply] at this ⊢`. Establish `h3` using `N.sub_mem y.2 this`. Simplify using `using h3`.
-/
theorem length_quotient_twist_formula : LengthQuotientTwistFormula := by
  intro R _ M _ _ T hT N c
  obtain ⟨V, hV⟩ : ∃ V : Module.End R N, V = T • LinearMap.id := ⟨_, rfl⟩
  have hVinj : Function.Injective V := by
    rw [injective_iff_map_eq_zero]; intro x hx
    apply Subtype.ext; apply hT; have := congrArg Subtype.val hx; simpa [hV] using this
  have hVc : ∀ x : N, ((V^c) x : M) = T^c • (x:M) := by
    intro x
    induction c with
    | zero => simp
    | succ c ih =>
      have hz : ∀ z : N, ((V z : N) : M) = T • (z:M) := by intro z; rw [hV]; simp
      rw [pow_succ', Module.End.mul_apply, hz, ih, pow_succ', mul_smul]
  have it := length_quotient_power_injective R N V hVinj c
  rw [← hV, ← it]
  have h1 : LinearMap.range (V^c) ≤ (N.map ((T ^ c) • (LinearMap.id : M →ₗ[R] M))).comap N.subtype := by
    rintro _ ⟨y, rfl⟩; exact ⟨y, y.2, by simp [hVc]⟩
  have h2 : N.map ((T ^ c) • (LinearMap.id : M →ₗ[R] M)) ≤ N.comap LinearMap.id := by
    rintro _ ⟨y, hy, rfl⟩; exact N.smul_mem _ hy
  have key := Module.length_eq_add_of_exact (Submodule.mapQ _ _ N.subtype h1) (Submodule.mapQ _ _ LinearMap.id h2) ?_ ?_ ?_
  · rw [key, add_comm]
  · rw [injective_iff_map_eq_zero]
    intro a
    induction a using Submodule.Quotient.induction_on with
    | H x =>
      intro hx
      rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      rw [Submodule.Quotient.mk_eq_zero]
      refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
      rw [hVc]; simpa using hyx
  · intro b
    induction b using Submodule.Quotient.induction_on with
    | H x => exact ⟨Submodule.Quotient.mk x, by simp⟩
  · intro b
    induction b using Submodule.Quotient.induction_on with
    | H x =>
      rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
      constructor
      · intro hx
        exact ⟨Submodule.Quotient.mk ⟨x, hx⟩, by rw [Submodule.mapQ_apply]; rfl⟩
      · rintro ⟨a, ha⟩
        induction a using Submodule.Quotient.induction_on with
        | H y =>
          rw [Submodule.mapQ_apply, Submodule.Quotient.eq] at ha
          have := h2 ha
          simp only [Submodule.mem_comap, LinearMap.id_coe, id_eq, Submodule.subtype_apply] at this ⊢
          have h3 := N.sub_mem y.2 this
          simpa using h3

/- English proof (translation)
Introduce `q _ n n' fW f`. Establish `swap : ∀ (x : Matrix (Fin n') (Fin n) ℤ) (l : Fin n → ℤ), ∑ i, fW i * ((x.mulVec l) i : ZMod q) = ∑ j, compF fW x j * (l j : ZMod q)`. Introduce `x l`. Simplify using `only [compF, Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `j _`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`. Expand and normalize the polynomial expressions, which then agree.

Prove the components needed by the constructor for the conclusion. Introduce `x hx l hl η hη`. Conclude with `hη (x.mulVec l) (by rw [swap, hx]; exact hl)`. Introduce `hn hfW hf`. Take `⟨i0, hi0⟩ : ∃ i, fW i ≠ 0` from `by by_contra h; push Not at h; exact hfW (funext h)`.

Take `⟨j0, hj0⟩ : ∃ j, f j ≠ 0` from `by by_contra h; push Not at h; exact hf (funext h)`. Choose the witnesses or unpack the hypotheses as in `⟨j1, hj1⟩ : ∃ j : Fin n, j ≠ j0 := by`. Distinguish the cases in `h : (j0 : ℕ) = 0`. Conclude with `⟨⟨1, by omega⟩, by intro h'; rw [← h'] at h; simp at h⟩`. Conclude with `⟨⟨0, by omega⟩, by intro h'; rw [← h'] at h; simp at h⟩`.

Establish `hq : (q:ℚ) ≠ 0` using `by exact_mod_cast (Fact.out : q.Prime).ne_zero`. Use `⟨fun i j => if i = i0 ∧ j = j1 then 1 else 0, fun j => if j = j1 then 1 else if j = j0 then -((f j1 / f j0 : ZMod q).val : ℤ) else 0, fun i => ((fW i).val : ℚ) / q, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Finset.add_sum_erase _ _ (Finset.mem_univ j1), ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hj1.symm, Finset.mem_univ j0⟩)]`. Rewrite using `[Finset.sum_eq_zero]`. Simplify using `[hj1.symm]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Introduce `j hj`. Simplify using `only [Finset.mem_erase] at hj`. Simplify using `[hj.1, hj.2.1]`.

Introduce `μ hμ`. Establish `: ((∑ i, ((fW i).val : ℤ) * μ i : ℤ) : ZMod q) = 0` using `by push_cast; simpa using hμ`. Rewrite `this` using `[ZMod.intCast_zmod_eq_zero_iff_dvd]`. Take `⟨z, hz⟩` from `this`. Use `⟨z, ?_⟩` and prove the remaining obligations.

Establish `h2 : (∑ i, ((fW i).val : ℚ) * (μ i : ℚ)) = (q:ℚ) * z` using `by exact_mod_cast hz`. Establish `h3 : ∑ i, ((fW i).val : ℚ) / q * (μ i : ℚ) = (∑ i, ((fW i).val : ℚ) * (μ i : ℚ)) / q`. Rewrite using `[Finset.sum_div]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h3, h2]`. Clear the denominators using the available nonvanishing facts. Introduce and unpack `⟨z, hz⟩`. Establish `hv : ∀ i, (Matrix.mulVec (fun i j => if i = i0 ∧ j = j1 then (1:ℤ) else 0 : Matrix (Fin n') (Fin n) ℤ) (fun j => if j = j1 then 1 else if j = j0 then -((f j1 / f j0 : ZMod q).val : ℤ) else 0)) i = if i = i0 then 1 else 0`.

Introduce `i`. Simplify using `only [Matrix.mulVec, dotProduct]`. Rewrite using `[Finset.sum_eq_single j1]`. Simplify using the standard rewrite rules. Introduce `j _ hj`.

Simplify using `[hj]`. Simplify using the standard rewrite rules. Simplify using `only [hv] at hz`. Rewrite `hz` using `[Finset.sum_eq_single i0 (by intro i _ hi; simp [hi]) (by simp)]`. Simplify using `only [if_true, Int.cast_one, mul_one] at hz`.

Establish `h4 : ((fW i0).val : ℚ) = (q:ℚ) * z` using `by rw [hz]; field_simp`. Establish `h5 : ((fW i0).val : ℤ) = (q:ℤ) * z` using `by exact_mod_cast h4`. Establish `h6 : ((((fW i0).val : ℤ)) : ZMod q) = 0` using `by rw [h5]; simp`. Apply `hi0` to reduce the goal to its premises. Simplify using `using h6`.
-/
theorem linear_form_integrality_on_support : LinearFormIntegralityOnSupport := by
  intro q _ n n' fW f
  have swap : ∀ (x : Matrix (Fin n') (Fin n) ℤ) (l : Fin n → ℤ),
      ∑ i, fW i * ((x.mulVec l) i : ZMod q) = ∑ j, compF fW x j * (l j : ZMod q) := by
    intro x l
    simp only [compF, Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro i _; ring
  constructor
  · intro x hx l hl η hη
    exact hη (x.mulVec l) (by rw [swap, hx]; exact hl)
  · intro hn hfW hf
    obtain ⟨i0, hi0⟩ : ∃ i, fW i ≠ 0 := by by_contra h; push Not at h; exact hfW (funext h)
    obtain ⟨j0, hj0⟩ : ∃ j, f j ≠ 0 := by by_contra h; push Not at h; exact hf (funext h)
    obtain ⟨j1, hj1⟩ : ∃ j : Fin n, j ≠ j0 := by
      by_cases h : (j0 : ℕ) = 0
      · exact ⟨⟨1, by omega⟩, by intro h'; rw [← h'] at h; simp at h⟩
      · exact ⟨⟨0, by omega⟩, by intro h'; rw [← h'] at h; simp at h⟩
    have hq : (q:ℚ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
    refine ⟨fun i j => if i = i0 ∧ j = j1 then 1 else 0,
      fun j => if j = j1 then 1 else if j = j0 then -((f j1 / f j0 : ZMod q).val : ℤ) else 0,
      fun i => ((fW i).val : ℚ) / q, ?_, ?_, ?_⟩
    · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j1), ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hj1.symm, Finset.mem_univ j0⟩)]
      rw [Finset.sum_eq_zero]
      · simp [hj1.symm]; field_simp; ring
      · intro j hj
        simp only [Finset.mem_erase] at hj
        simp [hj.1, hj.2.1]
    · intro μ hμ
      have : ((∑ i, ((fW i).val : ℤ) * μ i : ℤ) : ZMod q) = 0 := by push_cast; simpa using hμ
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
      obtain ⟨z, hz⟩ := this
      refine ⟨z, ?_⟩
      have h2 : (∑ i, ((fW i).val : ℚ) * (μ i : ℚ)) = (q:ℚ) * z := by exact_mod_cast hz
      have h3 : ∑ i, ((fW i).val : ℚ) / q * (μ i : ℚ) = (∑ i, ((fW i).val : ℚ) * (μ i : ℚ)) / q := by
        rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro i _; ring
      rw [h3, h2]; field_simp
    · rintro ⟨z, hz⟩
      have hv : ∀ i, (Matrix.mulVec (fun i j => if i = i0 ∧ j = j1 then (1:ℤ) else 0 : Matrix (Fin n') (Fin n) ℤ)
          (fun j => if j = j1 then 1 else if j = j0 then -((f j1 / f j0 : ZMod q).val : ℤ) else 0)) i = if i = i0 then 1 else 0 := by
        intro i
        simp only [Matrix.mulVec, dotProduct]
        rw [Finset.sum_eq_single j1]
        · simp
        · intro j _ hj; simp [hj]
        · simp
      simp only [hv] at hz
      rw [Finset.sum_eq_single i0 (by intro i _ hi; simp [hi]) (by simp)] at hz
      simp only [if_true, Int.cast_one, mul_one] at hz
      have h4 : ((fW i0).val : ℚ) = (q:ℚ) * z := by rw [hz]; field_simp
      have h5 : ((fW i0).val : ℤ) = (q:ℤ) * z := by exact_mod_cast h4
      have h6 : ((((fW i0).val : ℤ)) : ZMod q) = 0 := by rw [h5]; simp
      apply hi0; simpa using h6

/- English proof (translation)
Introduce `q _ n n'`. Establish `gen : ∀ (A B : Type) [AddCommGroup A] [Module (ZMod q) A] [AddCommGroup B] [Module (ZMod q) B] (φ : A →ₗ[ZMod q] B), Function.Surjective φ → Nat.card {x : A // φ x = 0} * Nat.card B = Nat.card A`. Introduce `A B _ _ _ _ φ hφ`. Establish `h1` using `Submodule.card_eq_card_quotient_mul_card (LinearMap.ker φ)`. Establish `h2 : Nat.card (A ⧸ LinearMap.ker φ) = Nat.card B` using `Nat.card_congr (φ.quotKerEquivOfSurjective hφ).toEquiv`.

Establish `h3 : Nat.card {x : A // φ x = 0} = Nat.card (LinearMap.ker φ)` using `rfl`. Rewrite using `[h1, h2, h3]`. Establish `cM : Nat.card (Matrix (Fin n') (Fin n) (ZMod q)) = q ^ (n' * n)` using `by show Nat.card (Fin n' → Fin n → ZMod q) = _`. Simplify using `[Nat.card_eq_fintype_card, ZMod.card, ← pow_mul, mul_comm]`. Establish `cV : ∀ k, Nat.card (Fin k → ZMod q) = q ^ k`.

Introduce `k`. Simplify using `[Nat.card_eq_fintype_card, ZMod.card]`. Prove the components needed by the constructor for the conclusion. Introduce `x0 hx0`. Take `⟨j0, hj0⟩ : ∃ j, x0 j ≠ 0` from `by by_contra h; push Not at h; exact hx0 (funext h)`.

Set `φ : Matrix (Fin n') (Fin n) (ZMod q) →ₗ[ZMod q] (Fin n' → ZMod q)` to `{ toFun := fun x => x.mulVec x0, map_add' := fun x y => Matrix.add_mulVec x y x0, map_smul' := fun c x => Matrix.smul_mulVec c x x0 }`. Use `gen _ _ φ (by` as an intermediate fact. Introduce `y`. Use `⟨fun i j => if j = j0 then y i / x0 j0 else 0, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Simplify using `only [φ, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVec, dotProduct]`. Rewrite using `[Finset.sum_eq_single j0 (by intro j _ hj; simp [hj]) (by simp)]`. Simplify using the standard rewrite rules. Use the proof step `field_simp)`. Rewrite `this` using `[cM, cV]`.

Conclude with `this`. Introduce `fW hfW`. Take `⟨i0, hi0⟩ : ∃ i, fW i ≠ 0` from `by by_contra h; push Not at h; exact hfW (funext h)`. Set `φ : Matrix (Fin n') (Fin n) (ZMod q) →ₗ[ZMod q] (Fin n → ZMod q)` to `{ toFun := fun x => Matrix.vecMul fW x, map_add' := fun x y => Matrix.vecMul_add x y fW, map_smul' := fun c x => Matrix.vecMul_smul fW c x }`. Use `gen _ _ φ (by` as an intermediate fact.

Introduce `y`. Use `⟨fun i j => if i = i0 then y j / fW i0 else 0, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `j`. Simplify using `only [φ, LinearMap.coe_mk, AddHom.coe_mk, Matrix.vecMul, dotProduct]`. Rewrite using `[Finset.sum_eq_single i0 (by intro i _ hi; simp [hi]) (by simp)]`.

Simplify using the standard rewrite rules. Use the proof step `field_simp)`. Rewrite `this` using `[cM, cV]`. Conclude with `this`.
-/
theorem supportVolumeIndex_statement : SupportVolumeIndex := by
  intro q _ n n'
  have gen : ∀ (A B : Type) [AddCommGroup A] [Module (ZMod q) A] [AddCommGroup B] [Module (ZMod q) B]
      (φ : A →ₗ[ZMod q] B), Function.Surjective φ →
      Nat.card {x : A // φ x = 0} * Nat.card B = Nat.card A := by
    intro A B _ _ _ _ φ hφ
    have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker φ)
    have h2 : Nat.card (A ⧸ LinearMap.ker φ) = Nat.card B :=
      Nat.card_congr (φ.quotKerEquivOfSurjective hφ).toEquiv
    have h3 : Nat.card {x : A // φ x = 0} = Nat.card (LinearMap.ker φ) := rfl
    rw [h1, h2, h3]
  have cM : Nat.card (Matrix (Fin n') (Fin n) (ZMod q)) = q ^ (n' * n) := by
    show Nat.card (Fin n' → Fin n → ZMod q) = _
    simp [Nat.card_eq_fintype_card, ZMod.card, ← pow_mul, mul_comm]
  have cV : ∀ k, Nat.card (Fin k → ZMod q) = q ^ k := by
    intro k; simp [Nat.card_eq_fintype_card, ZMod.card]
  constructor
  · intro x0 hx0
    obtain ⟨j0, hj0⟩ : ∃ j, x0 j ≠ 0 := by by_contra h; push Not at h; exact hx0 (funext h)
    let φ : Matrix (Fin n') (Fin n) (ZMod q) →ₗ[ZMod q] (Fin n' → ZMod q) :=
      { toFun := fun x => x.mulVec x0, map_add' := fun x y => Matrix.add_mulVec x y x0,
        map_smul' := fun c x => Matrix.smul_mulVec c x x0 }
    have := gen _ _ φ (by
      intro y
      refine ⟨fun i j => if j = j0 then y i / x0 j0 else 0, ?_⟩
      funext i
      simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single j0 (by intro j _ hj; simp [hj]) (by simp)]
      simp; field_simp)
    rw [cM, cV] at this
    exact this
  · intro fW hfW
    obtain ⟨i0, hi0⟩ : ∃ i, fW i ≠ 0 := by by_contra h; push Not at h; exact hfW (funext h)
    let φ : Matrix (Fin n') (Fin n) (ZMod q) →ₗ[ZMod q] (Fin n → ZMod q) :=
      { toFun := fun x => Matrix.vecMul fW x, map_add' := fun x y => Matrix.vecMul_add x y fW,
        map_smul' := fun c x => Matrix.vecMul_smul fW c x }
    have := gen _ _ φ (by
      intro y
      refine ⟨fun i j => if i = i0 then y j / fW i0 else 0, ?_⟩
      funext j
      simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, Matrix.vecMul, dotProduct]
      rw [Finset.sum_eq_single i0 (by intro i _ hi; simp [hi]) (by simp)]
      simp; field_simp)
    rw [cM, cV] at this
    exact this

/- English proof (translation)
Unfold `NonintegralMatrixPreservesThirdOverlattice`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `l c`. Use `⟨fun _ => l 0, c + l 1, ?_⟩` and prove the remaining obligations. Introduce `i`.

Simplify using `[Matrix.mulVec, dotProduct, Fin.sum_univ_two]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Introduce `i`. Use `⟨0, ?_⟩` and prove the remaining obligations.

Simplify using `[Matrix.mulVec, dotProduct, Fin.sum_univ_two]`. Introduce `h`. Take `⟨z, hz⟩` from `h 0 1`. Simplify using `at hz`. Establish `h3 : (3 : ℚ) * z = 1` using `by rw [hz]; norm_num`.

Establish `: (3 : ℤ) * z = 1` using `by exact_mod_cast h3`. Use linear arithmetic over natural numbers and integers.
-/
theorem weaker_displayed_bound : NonintegralMatrixPreservesThirdOverlattice := by
  unfold NonintegralMatrixPreservesThirdOverlattice
  refine ⟨?_, ?_, ?_⟩
  · intro l c
    refine ⟨fun _ => l 0, c + l 1, ?_⟩
    intro i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    push_cast
    ring
  · intro i
    refine ⟨0, ?_⟩
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · intro h
    obtain ⟨z, hz⟩ := h 0 1
    simp at hz
    have h3 : (3 : ℚ) * z = 1 := by rw [hz]; norm_num
    have : (3 : ℤ) * z = 1 := by exact_mod_cast h3
    omega

end Formalism.HermitianLattices.LocalLatticeBases
