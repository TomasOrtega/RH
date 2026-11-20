import Formalism.GaussValuationBounds.GaussUnit

namespace Formalism.NOK

open scoped ENNReal

section
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
The claim follows from `hU O x hx 1 isUnit_one`.
-/
theorem cval_gaussV_one (hU : GaussUnit) {x : ℝ} (hx : 0 ≤ x) :
    gaussV x (1 : PowerSeries O) = 0 := hU O x hx 1 isUnit_one

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero, cval_gaussV_one hU hx.le]`. Simplify using the standard rewrite rules. Consider the case `succ n ih => rw [pow_succ, hM O x hx, ih]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem cval_gaussV_pow (hM : GaussMul) (hU : GaussUnit) {x : ℝ} (hx : 0 < x)
    (f : PowerSeries O) (n : ℕ) : gaussV x (f ^ n) = n * gaussV x f := by
  induction n with
  | zero => rw [pow_zero, cval_gaussV_one hU hx.le]; simp
  | succ n ih => rw [pow_succ, hM O x hx, ih]; push_cast; ring

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [Finset.prod_range_zero, Finset.sum_range_zero, cval_gaussV_one hU hx.le]`. Consider the case `succ n ih => rw [Finset.prod_range_succ, Finset.sum_range_succ, hM O x hx, ih]`.
-/
theorem cval_gaussV_prod (hM : GaussMul) (hU : GaussUnit) {x : ℝ} (hx : 0 < x)
    (f : ℕ → PowerSeries O) (n : ℕ) :
    gaussV x (∏ s ∈ Finset.range n, f s) = ∑ s ∈ Finset.range n, gaussV x (f s) := by
  induction n with
  | zero => rw [Finset.prod_range_zero, Finset.sum_range_zero, cval_gaussV_one hU hx.le]
  | succ n ih => rw [Finset.prod_range_succ, Finset.sum_range_succ, hM O x hx, ih]

/- English proof (translation)
Establish `h1 : 1 ≤ ℓ ^ s` using `Nat.one_le_pow _ _ (by omega)`. Rewrite using `[hM O x hx, hU O x hx.le u hu, zero_add, hE O ϖ hϖ x hx.le E (ℓ ^ s) h1 hEis hdeg, Nat.cast_pow]`.
-/
theorem cval_gaussV_letter (hM : GaussMul) (hU : GaussUnit) (hE : GaussEis) {ϖ : O}
    (hϖ : Irreducible ϖ) {x : ℝ} (hx : 0 < x) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (E : Polynomial O)
    (u : PowerSeries O) (s : ℕ) (hEis : E.IsEisensteinAt (Ideal.span {ϖ}))
    (hdeg : E.natDegree = ℓ ^ s) (hu : IsUnit u) :
    gaussV x (u * (E : PowerSeries O)) = ENNReal.ofReal (min 1 (x * (ℓ : ℝ) ^ s)) := by
  have h1 : 1 ≤ ℓ ^ s := Nat.one_le_pow _ _ (by omega)
  rw [hM O x hx, hU O x hx.le u hu, zero_add, hE O ϖ hϖ x hx.le E (ℓ ^ s) h1 hEis hdeg,
    Nat.cast_pow]

/- English proof (translation)
Rewrite using `[hC O x hx, IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ]`. Simplify using the standard rewrite rules.
-/
theorem cval_gaussV_C_pow (hC : GaussC) {ϖ : O} (hϖ : Irreducible ϖ) {x : ℝ} (hx : 0 ≤ x)
    (n : ℕ) : gaussV x (PowerSeries.C (ϖ ^ n)) = (n : ℝ≥0∞) := by
  rw [hC O x hx, IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ]
  simp

end

section
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
Establish `hℓ1 : 1 ≤ ℓ` using `by omega`. Establish `hℓR : (2 : ℝ) ≤ ℓ` using `by exact_mod_cast hℓ`. Establish `hℓpos : (0 : ℝ) < ℓ` using `by linarith`. Establish `hℓne : (ℓ : ℝ) ≠ 0` using `hℓpos.ne'`. Establish `hpow1 : (0 : ℝ) < (ℓ : ℝ) ^ s₁` using `pow_pos hℓpos _`.

Establish `hpow2 : (ℓ : ℝ) ^ s₀ * ℓ ≤ (ℓ : ℝ) ^ s₁`. Rewrite using `[← pow_succ]; exact pow_le_pow_right₀ (by linarith) (by omega)`. Use `set x : ℝ := τ / (ℓ : ℝ) ^ s₁ with hxdef`. Establish `hx : 0 < x` using `div_pos hτ0 hpow1`. Establish `hx1 : x * (ℓ : ℝ) ^ s₁ = τ` using `by rw [hxdef]; field_simp`.

Establish `hx0 : x * (ℓ : ℝ) ^ s₀ ≤ τ / ℓ`. Rewrite using `[le_div_iff₀ hℓpos]`. Combine the equalities or inequalities in the displayed calculation. Establish `hVF : ∀ s, gaussV x (u s * (E s : PowerSeries O)) = ENNReal.ofReal (min 1 (x * (ℓ : ℝ) ^ s))` using `fun s => cval_gaussV_letter hM hU hE hϖ hx hℓ1 (E s) (u s) s (hEis s) (hdeg s) (hu s)`. Establish `hprod : gaussV x ((∏ s ∈ Finset.range ell, (u s * (E s : PowerSeries O)) ^ g) ^ 2) ≤ ((2 * g * ell : ℕ) : ℝ≥0∞)`.

Rewrite using `[cval_gaussV_pow hM hU hx, cval_gaussV_prod hM hU hx]`. Establish `hterm : ∀ s ∈ Finset.range ell, gaussV x ((u s * (E s : PowerSeries O)) ^ g) ≤ (g : ℝ≥0∞)`. Introduce `s _`. Rewrite using `[cval_gaussV_pow hM hU hx, hVF s]`. Combine the equalities or inequalities in the displayed calculation.

Apply `mul_le_mul_of_nonneg_left _ (by positivity)` to reduce the goal to its premises. Rewrite using `[← ENNReal.ofReal_one]`. Conclude with `ENNReal.ofReal_le_ofReal (min_le_left _ _)`. Use `_ = g := mul_one _`. Combine the equalities or inequalities in the displayed calculation.

Apply the tactic sequence `rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast <;> ring`. Establish `hR0 : 0 ≤ (a : ℝ) + 2 * g * ell + b₀ / ℓ * τ` using `add_nonneg (by positivity) (mul_nonneg (by positivity) hτ0.le)`. Establish `hR : (a : ℝ≥0∞) + ((2 * g * ell : ℕ) : ℝ≥0∞) + (b₀ : ℝ≥0∞) * ENNReal.ofReal (τ / ℓ) = ENNReal.ofReal ((a : ℝ) + 2 * g * ell + b₀ / ℓ * τ)`. Establish `e1 : (a : ℝ) + 2 * g * ell + b₀ / ℓ * τ = ((a + 2 * g * ell : ℕ) : ℝ) + (b₀ : ℝ) * (τ / ℓ)` using `by push_cast; ring`. Rewrite using `[e1, ENNReal.ofReal_add (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (div_nonneg hτ0.le hℓpos.le)), ENNReal.ofReal_natCast, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]`.

Apply the tactic sequence `push_cast <;> ring`. Establish `hup : gaussV x (PowerSeries.C (ϖ ^ a) * (∏ s ∈ Finset.range ell, (u s * (E s : PowerSeries O)) ^ g) ^ 2 * (u s₀ * (E s₀ : PowerSeries O)) ^ b₀) ≤ ENNReal.ofReal ((a : ℝ) + 2 * g * ell + b₀ / ℓ * τ)`. Rewrite using `[← hR, hM O x hx, hM O x hx, cval_gaussV_C_pow hC hϖ hx.le, cval_gaussV_pow hM hU hx (u s₀ * (E s₀ : PowerSeries O)) b₀, hVF s₀]`. Conclude with `add_le_add (add_le_add le_rfl hprod) (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans hx0)) (by positivity))`. Establish `hQ : gaussV x ((u s₁ * (E s₁ : PowerSeries O)) ^ b₁) = ENNReal.ofReal (b₁ * τ)`.

Rewrite using `[cval_gaussV_pow hM hU hx, hVF s₁, hx1, min_eq_right hτ1, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]`. Take `⟨c, e, hce⟩` from `Ideal.mem_span_pair.mp hmem`. Establish `hlow : min (k : ℝ≥0∞) (ENNReal.ofReal (b₁ * τ)) ≤ gaussV x (PowerSeries.C (ϖ ^ a) * (∏ s ∈ Finset.range ell, (u s * (E s : PowerSeries O)) ^ g) ^ 2 * (u s₀ * (E s₀ : PowerSeries O)) ^ b₀)`. Rewrite using `[← hce]`. Use `le_trans ?_ (hA O x _ _)` and prove the remaining obligations.

Rewrite using `[hM O x hx c, hM O x hx e, cval_gaussV_C_pow hC hϖ hx.le, hQ]`. Conclude with `min_le_min le_add_self le_add_self`. Establish `hRlt : ENNReal.ofReal ((a : ℝ) + 2 * g * ell + b₀ / ℓ * τ) < ENNReal.ofReal (b₁ * τ)` using `(ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt hR0 hlt)).mpr hlt`. Break down `min_le_iff.mp (hlow.trans hup) with h | h` into its components or cases. Rewrite `h` using `[← ENNReal.ofReal_natCast]`.

Conclude with `(ENNReal.ofReal_le_ofReal_iff hR0).mp h`. Conclude with `absurd h (not_le.mpr hRlt)`.
-/
theorem cval_step (hM : GaussMul) (hA : GaussAdd) (hC : GaussC) (hU : GaussUnit)
    (hE : GaussEis) {ϖ : O} (hϖ : Irreducible ϖ) {ℓ : ℕ} (hℓ : 2 ≤ ℓ)
    (E : ℕ → Polynomial O) (u : ℕ → PowerSeries O)
    (hEis : ∀ s, (E s).IsEisensteinAt (Ideal.span {ϖ})) (hdeg : ∀ s, (E s).natDegree = ℓ ^ s)
    (hu : ∀ s, IsUnit (u s)) {ell g a b₀ b₁ s₀ s₁ k : ℕ} (hs : s₀ < s₁)
    (hmem : PowerSeries.C (ϖ ^ a) *
        (∏ s ∈ Finset.range ell, (u s * (E s : PowerSeries O)) ^ g) ^ 2 *
        (u s₀ * (E s₀ : PowerSeries O)) ^ b₀ ∈
      Ideal.span {PowerSeries.C (ϖ ^ k), (u s₁ * (E s₁ : PowerSeries O)) ^ b₁})
    {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    (hlt : (a : ℝ) + 2 * g * ell + b₀ / ℓ * τ < b₁ * τ) :
    (k : ℝ) ≤ (a : ℝ) + 2 * g * ell + b₀ / ℓ * τ := by
  have hℓ1 : 1 ≤ ℓ := by omega
  have hℓR : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hℓpos : (0 : ℝ) < ℓ := by linarith
  have hℓne : (ℓ : ℝ) ≠ 0 := hℓpos.ne'
  have hpow1 : (0 : ℝ) < (ℓ : ℝ) ^ s₁ := pow_pos hℓpos _
  have hpow2 : (ℓ : ℝ) ^ s₀ * ℓ ≤ (ℓ : ℝ) ^ s₁ := by
    rw [← pow_succ]; exact pow_le_pow_right₀ (by linarith) (by omega)
  set x : ℝ := τ / (ℓ : ℝ) ^ s₁ with hxdef
  have hx : 0 < x := div_pos hτ0 hpow1
  have hx1 : x * (ℓ : ℝ) ^ s₁ = τ := by rw [hxdef]; field_simp
  have hx0 : x * (ℓ : ℝ) ^ s₀ ≤ τ / ℓ := by
    rw [le_div_iff₀ hℓpos]
    calc x * (ℓ : ℝ) ^ s₀ * ℓ = x * ((ℓ : ℝ) ^ s₀ * ℓ) := by ring
      _ ≤ x * (ℓ : ℝ) ^ s₁ := mul_le_mul_of_nonneg_left hpow2 hx.le
      _ = τ := hx1
  have hVF : ∀ s, gaussV x (u s * (E s : PowerSeries O)) =
      ENNReal.ofReal (min 1 (x * (ℓ : ℝ) ^ s)) := fun s =>
    cval_gaussV_letter hM hU hE hϖ hx hℓ1 (E s) (u s) s (hEis s) (hdeg s) (hu s)
  have hprod : gaussV x ((∏ s ∈ Finset.range ell, (u s * (E s : PowerSeries O)) ^ g) ^ 2)
      ≤ ((2 * g * ell : ℕ) : ℝ≥0∞) := by
    rw [cval_gaussV_pow hM hU hx, cval_gaussV_prod hM hU hx]
    have hterm : ∀ s ∈ Finset.range ell,
        gaussV x ((u s * (E s : PowerSeries O)) ^ g) ≤ (g : ℝ≥0∞) := by
      intro s _
      rw [cval_gaussV_pow hM hU hx, hVF s]
      calc (g : ℝ≥0∞) * ENNReal.ofReal (min 1 (x * (ℓ : ℝ) ^ s)) ≤ (g : ℝ≥0∞) * 1 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal (min_le_left _ _)
        _ = g := mul_one _
    calc ((2 : ℕ) : ℝ≥0∞) * ∑ s ∈ Finset.range ell, gaussV x ((u s * (E s : PowerSeries O)) ^ g)
        ≤ ((2 : ℕ) : ℝ≥0∞) * ∑ s ∈ Finset.range ell, (g : ℝ≥0∞) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity)
      _ = ((2 * g * ell : ℕ) : ℝ≥0∞) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast <;> ring
  have hR0 : 0 ≤ (a : ℝ) + 2 * g * ell + b₀ / ℓ * τ :=
    add_nonneg (by positivity) (mul_nonneg (by positivity) hτ0.le)
  have hR : (a : ℝ≥0∞) + ((2 * g * ell : ℕ) : ℝ≥0∞) + (b₀ : ℝ≥0∞) * ENNReal.ofReal (τ / ℓ)
      = ENNReal.ofReal ((a : ℝ) + 2 * g * ell + b₀ / ℓ * τ) := by
    have e1 : (a : ℝ) + 2 * g * ell + b₀ / ℓ * τ
        = ((a + 2 * g * ell : ℕ) : ℝ) + (b₀ : ℝ) * (τ / ℓ) := by
      push_cast; ring
    rw [e1, ENNReal.ofReal_add (Nat.cast_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (div_nonneg hτ0.le hℓpos.le)),
      ENNReal.ofReal_natCast, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    push_cast <;> ring
  have hup : gaussV x (PowerSeries.C (ϖ ^ a) *
        (∏ s ∈ Finset.range ell, (u s * (E s : PowerSeries O)) ^ g) ^ 2 *
        (u s₀ * (E s₀ : PowerSeries O)) ^ b₀)
      ≤ ENNReal.ofReal ((a : ℝ) + 2 * g * ell + b₀ / ℓ * τ) := by
    rw [← hR, hM O x hx, hM O x hx, cval_gaussV_C_pow hC hϖ hx.le,
      cval_gaussV_pow hM hU hx (u s₀ * (E s₀ : PowerSeries O)) b₀, hVF s₀]
    exact add_le_add (add_le_add le_rfl hprod)
      (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans hx0)) (by positivity))
  have hQ : gaussV x ((u s₁ * (E s₁ : PowerSeries O)) ^ b₁) = ENNReal.ofReal (b₁ * τ) := by
    rw [cval_gaussV_pow hM hU hx, hVF s₁, hx1, min_eq_right hτ1,
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  obtain ⟨c, e, hce⟩ := Ideal.mem_span_pair.mp hmem
  have hlow : min (k : ℝ≥0∞) (ENNReal.ofReal (b₁ * τ)) ≤ gaussV x (PowerSeries.C (ϖ ^ a) *
        (∏ s ∈ Finset.range ell, (u s * (E s : PowerSeries O)) ^ g) ^ 2 *
        (u s₀ * (E s₀ : PowerSeries O)) ^ b₀) := by
    rw [← hce]
    refine le_trans ?_ (hA O x _ _)
    rw [hM O x hx c, hM O x hx e, cval_gaussV_C_pow hC hϖ hx.le, hQ]
    exact min_le_min le_add_self le_add_self
  have hRlt : ENNReal.ofReal ((a : ℝ) + 2 * g * ell + b₀ / ℓ * τ) < ENNReal.ofReal (b₁ * τ) :=
    (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt hR0 hlt)).mpr hlt
  rcases min_le_iff.mp (hlow.trans hup) with h | h
  · rw [← ENNReal.ofReal_natCast] at h
    exact (ENNReal.ofReal_le_ofReal_iff hR0).mp h
  · exact absurd h (not_le.mpr hRlt)

end

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ ℓ hℓ E u hEis hdeg hu ell g a b₀ b₁ s₀ s₁ k hs h2A hb hmem`. Establish `key : ∀ τ : ℝ, 0 < τ → τ ≤ 1 → (a : ℝ) + 2 * g * ell + b₀ / ℓ * τ < b₁ * τ → (k : ℝ) ≤ (a : ℝ) + 2 * g * ell + b₀ / ℓ * τ` using `fun τ hτ0 hτ1 hlt => cval_step hM hA hC hU hE hϖ hℓ E u hEis hdeg hu hs hmem hτ0 hτ1 hlt`. Establish `hℓpos : (0 : ℝ) < ℓ` using `by exact_mod_cast (by omega : 0 < ℓ)`. Establish `hc0 : 0 ≤ (b₀ : ℝ) / ℓ` using `by positivity`. Establish `hcB : 2 * ((b₀ : ℝ) / ℓ) ≤ b₁`.

Establish `hb' : (2 : ℝ) * b₀ ≤ ℓ * b₁` using `by exact_mod_cast hb`. Rewrite using `[← mul_div_assoc, div_le_iff₀ hℓpos]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hA0 : 0 ≤ (a : ℝ) + 2 * g * ell` using `by positivity`. Generalize the expression as in `(a : ℝ) + 2 * g * ell = A at key h2A hA0 ⊢`.

Generalize the expression as in `(b₀ : ℝ) / ℓ = c at key hc0 hcB ⊢`. Generalize the expression as in `(b₁ : ℝ) = B at key hcB h2A ⊢`. Establish `hD : 0 < B - c` using `by linarith`. Establish `hτs : A / (B - c) < 1` using `by rw [div_lt_one hD]; linarith`. Establish `hτs0 : 0 ≤ A / (B - c)` using `div_nonneg hA0 hD.le`.

Establish `heq : A * B / (B - c) = A + c * (A / (B - c))`. Establish `hDne : B - c ≠ 0` using `hD.ne'`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : (k : ℝ) ≤ A * B / (B - c)`.

Rewrite using `[heq]`. Apply `le_of_forall_pos_le_add` to reduce the goal to its premises. Introduce `ε hε`. Establish `hc1 : (0 : ℝ) < c + 1` using `by linarith`. Establish `hδ : 0 < ε / (c + 1)` using `div_pos hε hc1`.

Establish `hτgt : A / (B - c) < min 1 (A / (B - c) + ε / (c + 1))` using `lt_min hτs (by linarith)`. Establish `hτ0 : 0 < min 1 (A / (B - c) + ε / (c + 1))` using `lt_of_le_of_lt hτs0 hτgt`. Establish `hτ1 : min 1 (A / (B - c) + ε / (c + 1)) ≤ 1` using `min_le_left _ _`. Establish `hτle : min 1 (A / (B - c) + ε / (c + 1)) ≤ A / (B - c) + ε / (c + 1)` using `min_le_right _ _`. Establish `hlt : A + c * min 1 (A / (B - c) + ε / (c + 1)) < B * min 1 (A / (B - c) + ε / (c + 1))`.

Use `(div_lt_iff₀ hD).mp hτgt` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hk` using `key _ hτ0 hτ1 hlt`. Establish `hcδ : c * (ε / (c + 1)) ≤ ε`. Combine the equalities or inequalities in the displayed calculation.

Establish `hm` using `mul_le_mul_of_nonneg_left hτle hc0`. Combine the equalities or inequalities in the displayed calculation. Use `⟨h1, h1.trans ?_⟩` and prove the remaining obligations. Rewrite using `[div_le_iff₀ hD]`. Use polynomial arithmetic with `[mul_nonneg hA0 (sub_nonneg.mpr hcB)]`.
-/
theorem lemmaCVal_of (hM : GaussMul) (hA : GaussAdd) (hC : GaussC) (hU : GaussUnit)
    (hE : GaussEis) : LemmaCVal := by
  intro O _ _ _ ϖ hϖ ℓ hℓ E u hEis hdeg hu ell g a b₀ b₁ s₀ s₁ k hs h2A hb hmem
  have key : ∀ τ : ℝ, 0 < τ → τ ≤ 1 → (a : ℝ) + 2 * g * ell + b₀ / ℓ * τ < b₁ * τ →
      (k : ℝ) ≤ (a : ℝ) + 2 * g * ell + b₀ / ℓ * τ := fun τ hτ0 hτ1 hlt =>
    cval_step hM hA hC hU hE hϖ hℓ E u hEis hdeg hu hs hmem
      hτ0 hτ1 hlt
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast (by omega : 0 < ℓ)
  have hc0 : 0 ≤ (b₀ : ℝ) / ℓ := by positivity
  have hcB : 2 * ((b₀ : ℝ) / ℓ) ≤ b₁ := by
    have hb' : (2 : ℝ) * b₀ ≤ ℓ * b₁ := by exact_mod_cast hb
    rw [← mul_div_assoc, div_le_iff₀ hℓpos]
    linarith
  have hA0 : 0 ≤ (a : ℝ) + 2 * g * ell := by positivity
  generalize (a : ℝ) + 2 * g * ell = A at key h2A hA0 ⊢
  generalize (b₀ : ℝ) / ℓ = c at key hc0 hcB ⊢
  generalize (b₁ : ℝ) = B at key hcB h2A ⊢
  have hD : 0 < B - c := by linarith
  have hτs : A / (B - c) < 1 := by rw [div_lt_one hD]; linarith
  have hτs0 : 0 ≤ A / (B - c) := div_nonneg hA0 hD.le
  have heq : A * B / (B - c) = A + c * (A / (B - c)) := by
    have hDne : B - c ≠ 0 := hD.ne'
    field_simp; ring
  have h1 : (k : ℝ) ≤ A * B / (B - c) := by
    rw [heq]
    apply le_of_forall_pos_le_add
    intro ε hε
    have hc1 : (0 : ℝ) < c + 1 := by linarith
    have hδ : 0 < ε / (c + 1) := div_pos hε hc1
    have hτgt : A / (B - c) < min 1 (A / (B - c) + ε / (c + 1)) := lt_min hτs (by linarith)
    have hτ0 : 0 < min 1 (A / (B - c) + ε / (c + 1)) := lt_of_le_of_lt hτs0 hτgt
    have hτ1 : min 1 (A / (B - c) + ε / (c + 1)) ≤ 1 := min_le_left _ _
    have hτle : min 1 (A / (B - c) + ε / (c + 1)) ≤ A / (B - c) + ε / (c + 1) := min_le_right _ _
    have hlt : A + c * min 1 (A / (B - c) + ε / (c + 1)) < B * min 1 (A / (B - c) + ε / (c + 1)) := by
      have := (div_lt_iff₀ hD).mp hτgt
      linarith
    have hk := key _ hτ0 hτ1 hlt
    have hcδ : c * (ε / (c + 1)) ≤ ε := by
      calc c * (ε / (c + 1)) ≤ (c + 1) * (ε / (c + 1)) :=
            mul_le_mul_of_nonneg_right (by linarith) hδ.le
        _ = ε := by field_simp
    have hm := mul_le_mul_of_nonneg_left hτle hc0
    calc (k : ℝ) ≤ A + c * min 1 (A / (B - c) + ε / (c + 1)) := hk
      _ ≤ A + c * (A / (B - c) + ε / (c + 1)) := by linarith
      _ = A + c * (A / (B - c)) + c * (ε / (c + 1)) := by ring
      _ ≤ A + c * (A / (B - c)) + ε := by linarith
  refine ⟨h1, h1.trans ?_⟩
  rw [div_le_iff₀ hD]
  nlinarith [mul_nonneg hA0 (sub_nonneg.mpr hcB)]

end Formalism.NOK
