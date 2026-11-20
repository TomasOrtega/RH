import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelLossDegreeBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDegreeGapBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHeightOneIdealIffAdditiveValuationPos
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.G NumberField GlobalTheory.IndefiniteRowSideFullHecke.LevelLossDegreeBounds

namespace GlobalTheory.LevelCoprime

open Formalism.FrobeniusOrbits

section Host

variable {R : Ranks} (H : Host R)

/- English proof (translation)
The claim follows from `H.conjE_apply φ x`.
-/
theorem phi_conj (φ : H.E →+* ℂ) (x : H.E) : φ (H.conj x) = starRingEnd ℂ (φ x) :=
  H.conjE_apply φ x

/- English proof (translation)
Apply `H.φ₀.injective` to reduce the goal to its premises. Rewrite using `[phi_conj, phi_conj, Complex.conj_conj]`.
-/
theorem conj_conj (x : H.E) : H.conj (H.conj x) = x := by
  apply H.φ₀.injective
  rw [phi_conj, phi_conj, Complex.conj_conj]

/- English proof (translation)
Apply `H.φ₀.injective` to reduce the goal to its premises. Establish `h1` using `phi_conj H (H.φ₀.comp (σ : H.E →+* H.E)) x`. Conclude with `h1.trans (phi_conj H H.φ₀ (σ x)).symm`.
-/
theorem sigma_conj (σ : H.E ≃ₐ[ℚ] H.E) (x : H.E) : σ (H.conj x) = H.conj (σ x) := by
  apply H.φ₀.injective
  have h1 := phi_conj H (H.φ₀.comp (σ : H.E →+* H.E)) x
  exact h1.trans (phi_conj H H.φ₀ (σ x)).symm

/- English proof (translation)
The claim follows from `H.sqd_sq`.
-/
theorem b_sq : H.sqrtMinusD ^ 2 = -(H.d : H.E) := H.sqd_sq

/- English proof (translation)
Apply `H.φ₀.injective` to reduce the goal to its premises. Establish `h3 : H.φ₀ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ)` using `H.φ₀_mem`. Rewrite using `[phi_conj, map_neg, h3]`. Simplify using the standard rewrite rules.
-/
theorem conj_b : H.conj H.sqrtMinusD = -H.sqrtMinusD := by
  apply H.φ₀.injective
  have h3 : H.φ₀ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem
  rw [phi_conj, map_neg, h3]
  simp

/- English proof (translation)
Establish `hx' : x ∈ IntermediateField.adjoin ℚ {H.sqrtMinusD}` using `hx`. Use `clear hx`. Proceed by induction on `hx' using IntermediateField.adjoin_induction with`. Consider the case `mem y hy => rw [Set.mem_singleton_iff.1 hy]`. Conclude with `h`.

Consider the case `algebraMap r => simp`. Consider the case `add a b _ _ ha hb => rw [map_add, map_add, ha, hb]`. Consider the case `inv a _ ha => rw [map_inv₀, map_inv₀, ha]`. Consider the case `mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]`.
-/
theorem agree_on_K (σ τ : H.E ≃ₐ[ℚ] H.E) (h : σ H.sqrtMinusD = τ H.sqrtMinusD) (x : H.E) (hx : x ∈ H.K) :
    σ x = τ x := by
  have hx' : x ∈ IntermediateField.adjoin ℚ {H.sqrtMinusD} := hx
  clear hx
  induction hx' using IntermediateField.adjoin_induction with
  | mem y hy => rw [Set.mem_singleton_iff.1 hy]; exact h
  | algebraMap r => simp
  | add a b _ _ ha hb => rw [map_add, map_add, ha, hb]
  | inv a _ ha => rw [map_inv₀, map_inv₀, ha]
  | mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]

/- English proof (translation)
Use `haveI : IsGalois ℚ H.E := H.hostE_isGalois`. Establish `hmem : x + H.conj x ∈ (⊥ : IntermediateField ℚ H.E)`. Rewrite using `[← IsGalois.fixedField_top, IntermediateField.mem_fixedField_iff]`. Introduce `σ _`. Establish `hb : σ H.sqrtMinusD = H.sqrtMinusD ∨ σ H.sqrtMinusD = -H.sqrtMinusD`.

Apply `sq_eq_sq_iff_eq_or_eq_neg.1` to reduce the goal to its premises. Rewrite using `[← map_pow, b_sq, map_neg, map_natCast]`. Rewrite using `[map_add, sigma_conj]`. Break down `hb with hb | hb` into its components or cases. Use `agree_on_K H σ 1 hb x hx` as an intermediate fact.

Rewrite using `[this]`. Both sides reduce to the same expression. Use `agree_on_K H σ H.conj (hb.trans (conj_b H).symm) x hx` as an intermediate fact. Rewrite using `[this, conj_conj, add_comm]`. Conclude with `IntermediateField.mem_bot.1 hmem`.
-/
theorem trace_rat (x : H.E) (hx : x ∈ H.K) : ∃ r : ℚ, algebraMap ℚ H.E r = x + H.conj x := by
  haveI : IsGalois ℚ H.E := H.hostE_isGalois
  have hmem : x + H.conj x ∈ (⊥ : IntermediateField ℚ H.E) := by
    rw [← IsGalois.fixedField_top, IntermediateField.mem_fixedField_iff]
    intro σ _
    have hb : σ H.sqrtMinusD = H.sqrtMinusD ∨ σ H.sqrtMinusD = -H.sqrtMinusD := by
      apply sq_eq_sq_iff_eq_or_eq_neg.1
      rw [← map_pow, b_sq, map_neg, map_natCast]
    rw [map_add, sigma_conj]
    rcases hb with hb | hb
    · have := agree_on_K H σ 1 hb x hx
      rw [this]; rfl
    · have := agree_on_K H σ H.conj (hb.trans (conj_b H).symm) x hx
      rw [this, conj_conj, add_comm]
  exact IntermediateField.mem_bot.1 hmem

/- English proof (translation)
Take `⟨r, hr⟩` from `trace_rat H x hx`. Establish `h1 : IsIntegral ℤ (H.conj (x : H.E))` using `IsIntegral.map (H.conj : H.E →+* H.E).toIntAlgHom x.isIntegral_coe`. Establish `h2 : IsIntegral ℤ (algebraMap ℚ H.E r)` using `hr ▸ x.isIntegral_coe.add h1`. Establish `h3 : IsIntegral ℤ r` using `(isIntegral_algebraMap_iff (algebraMap ℚ H.E).injective).1 h2`. Take `⟨a, ha⟩` from `IsIntegrallyClosed.algebraMap_eq_of_integral h3`.

Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[← hr, ← ha]`. Simplify using the standard rewrite rules.
-/
theorem trace_int (x : 𝓞 H.E) (hx : (x : H.E) ∈ H.K) : ∃ a : ℤ, (a : H.E) = x + H.conj x := by
  obtain ⟨r, hr⟩ := trace_rat H x hx
  have h1 : IsIntegral ℤ (H.conj (x : H.E)) :=
    IsIntegral.map (H.conj : H.E →+* H.E).toIntAlgHom x.isIntegral_coe
  have h2 : IsIntegral ℤ (algebraMap ℚ H.E r) := hr ▸ x.isIntegral_coe.add h1
  have h3 : IsIntegral ℤ r := (isIntegral_algebraMap_iff (algebraMap ℚ H.E).injective).1 h2
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h3
  refine ⟨a, ?_⟩
  rw [← hr, ← ha]
  simp

/- English proof (translation)
Establish `h1` using `congrArg H.φ₀ ha`. Establish `h2` using `congrArg H.φ₀ hT`. Rewrite `h1` using `[map_add, phi_conj, map_intCast, Complex.add_conj]`. Rewrite `h2` using `[map_mul, phi_conj, map_natCast, Complex.mul_conj, Complex.normSq_apply]`. Establish `h3 : (a : ℝ) = 2 * (H.φ₀ x).re` using `by exact_mod_cast h1`.

Establish `h4 : (H.φ₀ x).re * (H.φ₀ x).re + (H.φ₀ x).im * (H.φ₀ x).im = (T : ℝ)` using `by exact_mod_cast h2`. Establish `h5 : (a : ℝ) ^ 2 ≤ 4 * T`. Rewrite using `[h3, ← h4]`. Use polynomial arithmetic with `[mul_self_nonneg (H.φ₀ x).im]`. Conclude with `h5` after adjusting the coercions.
-/
theorem trace_sq_le (x : H.E) (a : ℤ) (T : ℕ) (ha : (a : H.E) = x + H.conj x) (hT : x * H.conj x = T) :
    a ^ 2 ≤ 4 * T := by
  have h1 := congrArg H.φ₀ ha
  have h2 := congrArg H.φ₀ hT
  rw [map_add, phi_conj, map_intCast, Complex.add_conj] at h1
  rw [map_mul, phi_conj, map_natCast, Complex.mul_conj, Complex.normSq_apply] at h2
  have h3 : (a : ℝ) = 2 * (H.φ₀ x).re := by exact_mod_cast h1
  have h4 : (H.φ₀ x).re * (H.φ₀ x).re + (H.φ₀ x).im * (H.φ₀ x).im = (T : ℝ) := by exact_mod_cast h2
  have h5 : (a : ℝ) ^ 2 ≤ 4 * T := by
    rw [h3, ← h4]
    nlinarith [mul_self_nonneg (H.φ₀ x).im]
  exact_mod_cast h5

end Host

/- English proof (translation)
Establish `h1 : y = algebraMap ℚ E ((n : ℚ) / 4)`. Rewrite using `[map_div₀, map_intCast, h]`. Simplify using the standard rewrite rules. Rewrite `hy` using `[h1]`. Establish `h3` using `(isIntegral_algebraMap_iff (algebraMap ℚ E).injective).1 hy`.

Take `⟨a, ha⟩` from `IsIntegrallyClosed.algebraMap_eq_of_integral h3`. Use `⟨a, ?_⟩` and prove the remaining obligations. Establish `h4 : (a : ℚ) = (n : ℚ) / 4` using `by simpa using ha`. Establish `h5 : (n : ℚ) = 4 * a` using `by rw [h4]; ring`. Conclude with `h5` after adjusting the coercions.
-/
theorem four_dvd {E : Type} [Field E] [NumberField E] (n : ℤ) (y : E) (hy : IsIntegral ℤ y)
    (h : (n : E) = 4 * y) : (4 : ℤ) ∣ n := by
  have h1 : y = algebraMap ℚ E ((n : ℚ) / 4) := by
    rw [map_div₀, map_intCast, h]
    simp
  rw [h1] at hy
  have h3 := (isIntegral_algebraMap_iff (algebraMap ℚ E).injective).1 hy
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h3
  refine ⟨a, ?_⟩
  have h4 : (a : ℚ) = (n : ℚ) / 4 := by simpa using ha
  have h5 : (n : ℚ) = 4 * a := by rw [h4]; ring
  exact_mod_cast h5

/- English proof (translation)
Introduce `hd`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton.1 (X.piT_cong u)`. Establish `hdiv : ∃ b : 𝓞 D.host.E, X.piT u = 1 + 4 * b`. Establish `h4 : (4 : ℕ) ∣ D.host.QS` using `(show (4 : ℕ) ∣ 2 ^ (D.R.e + 2) from ⟨2 ^ D.R.e, by ring⟩).trans D.host.tower_dvd`. Take `⟨k, hk⟩` from `h4`.

Use `⟨(k * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 : ℕ) * c, ?_⟩` and prove the remaining obligations. Rewrite `hc` using `[hk]`. Move the coercions through the operations in `at hc ⊢`. Take the linear combination `hc`. Take `⟨b, hb⟩` from `hdiv`.

Establish `hn` using `X.piT_norm u`. Establish `hle` using `trace_sq_le D.host _ a _ ha hn`. Establish `hb' : ((X.piT u : 𝓞 D.host.E) : D.host.E) = 1 + 4 * (b : D.host.E)`. Rewrite using `[hb]`. Simplify using `[map_ofNat]`.

Establish `hbi : IsIntegral ℤ (D.host.conj (b : D.host.E))` using `IsIntegral.map (D.host.conj : D.host.E →+* D.host.E).toIntAlgHom b.isIntegral_coe`. Establish `hb0` using `b.isIntegral_coe`. Rewrite `ha`, `hn` using `[hb']`. Simplify using `only [map_add, map_mul, map_one, map_ofNat] at ha hn`. Establish `h1 : (4 : ℤ) ∣ a - 2` using `four_dvd _ _ (hb0.add hbi) (by push_cast; linear_combination ha)`.

Establish `h4 : IsIntegral ℤ (4 : D.host.E)`. Simplify using `using (isIntegral_algebraMap (R := ℤ) (A := D.host.E) (x := 4))`. Establish `h2 : (4 : ℤ) ∣ ((D.mem u).A.T : ℤ) - 1` using `four_dvd _ _ ((hb0.add hbi).add ((h4.mul hb0).mul hbi)) (by push_cast; linear_combination -hn)`. Establish `h3` using `(D.mem u).A.T_prime.two_le`. Take `⟨k, rfl⟩` from `hd`.

Use `set T : ℤ := ((D.mem u).A.T : ℤ) with hT`. Establish `h5 : 5 ≤ T` using `by omega`. Establish `hk : k ≠ 0`. Introduce and unpack `rfl`. Use linear arithmetic over natural numbers and integers.

Establish `hk2 : 1 ≤ k ^ 2`. Use `sq_pos_of_ne_zero hk` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use polynomial arithmetic with `[mul_pow T k 2]`.
-/
theorem not_dvd_trace {D : D7} (X : ErrX D) (u : D.what₂.Word) (a : ℤ)
    (ha : (a : D.host.E) = X.piT u + D.host.conj (X.piT u)) : ¬ (((D.mem u).A.T : ℤ) ∣ a) := by
  intro hd
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (X.piT_cong u)
  have hdiv : ∃ b : 𝓞 D.host.E, X.piT u = 1 + 4 * b := by
    have h4 : (4 : ℕ) ∣ D.host.QS :=
      (show (4 : ℕ) ∣ 2 ^ (D.R.e + 2) from ⟨2 ^ D.R.e, by ring⟩).trans D.host.tower_dvd
    obtain ⟨k, hk⟩ := h4
    refine ⟨(k * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 : ℕ) * c, ?_⟩
    rw [hk] at hc
    push_cast at hc ⊢
    linear_combination hc
  obtain ⟨b, hb⟩ := hdiv
  have hn := X.piT_norm u
  have hle := trace_sq_le D.host _ a _ ha hn
  have hb' : ((X.piT u : 𝓞 D.host.E) : D.host.E) = 1 + 4 * (b : D.host.E) := by
    rw [hb]; simp [map_ofNat]
  have hbi : IsIntegral ℤ (D.host.conj (b : D.host.E)) :=
    IsIntegral.map (D.host.conj : D.host.E →+* D.host.E).toIntAlgHom b.isIntegral_coe
  have hb0 := b.isIntegral_coe
  rw [hb'] at ha hn
  simp only [map_add, map_mul, map_one, map_ofNat] at ha hn
  have h1 : (4 : ℤ) ∣ a - 2 := four_dvd _ _ (hb0.add hbi) (by push_cast; linear_combination ha)
  have h4 : IsIntegral ℤ (4 : D.host.E) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := D.host.E) (x := 4))
  have h2 : (4 : ℤ) ∣ ((D.mem u).A.T : ℤ) - 1 :=
    four_dvd _ _ ((hb0.add hbi).add ((h4.mul hb0).mul hbi)) (by push_cast; linear_combination -hn)
  have h3 := (D.mem u).A.T_prime.two_le
  obtain ⟨k, rfl⟩ := hd
  set T : ℤ := ((D.mem u).A.T : ℤ) with hT
  have h5 : 5 ≤ T := by omega
  have hk : k ≠ 0 := by
    rintro rfl
    omega
  have hk2 : 1 ≤ k ^ 2 := by
    have := sq_pos_of_ne_zero hk
    omega
  nlinarith [mul_pow T k 2]

/- English proof (translation)
Introduce and unpack `⟨h1, h2⟩`. Take `⟨a, ha⟩` from `trace_int D.host (X.piT u) (X.piT_K u)`. Establish `hp` using `(D.mem u).A.T_prime`. Establish `hn` using `X.piT_norm u`. Establish `hT0 : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0` using `Nat.cast_ne_zero.2 hp.ne_zero`.

Rewrite `hT0` using `[← hn]`. Rewrite `h2` using `[← D.embE_conj]`. Establish `i1 : IsIntegral ℤ (D.embE (X.piT u : D.host.E))` using `IsIntegral.map D.embE.toIntAlgHom (X.piT u).isIntegral_coe`. Establish `i2 : IsIntegral ℤ (D.embE (D.host.conj (X.piT u : D.host.E)))` using `IsIntegral.map (D.embE.comp (D.host.conj : D.host.E →+* D.host.E)).toIntAlgHom (X.piT u).isIntegral_coe`. Set `y : 𝓞 D.what₂.LL` to `⟨_, i1⟩`.

Set `z : 𝓞 D.what₂.LL` to `⟨_, i2⟩`. Establish `hy : y ≠ 0` using `fun h => (map_ne_zero D.embE).2 (left_ne_zero_of_mul hT0) (congrArg Subtype.val h)`. Establish `hz : z ≠ 0` using `fun h => (map_ne_zero D.embE).2 (right_ne_zero_of_mul hT0) (congrArg Subtype.val h)`. Establish `m1` using `(GlobalTheory.TypeLoss.mem_heightOneIdeal_iff_additiveValuation_pos (D.plEq w) y hy).2 h1`. Establish `m2` using `(GlobalTheory.TypeLoss.mem_heightOneIdeal_iff_additiveValuation_pos (D.plEq w) z hz).2 h2`.

Establish `e : ((a : ℤ) : 𝓞 D.what₂.LL) = y + z`. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Rewrite using `[map_intCast, map_add]`. Express the relevant statement in the definitionally equal form `_ = D.embE _ + D.embE _`. Rewrite using `[← map_add, ← ha, map_intCast]`.

Establish `m3 : ((a : ℤ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal` using `e ▸ Ideal.add_mem _ m1 m2`. Establish `m4 : (((D.mem u).A.T : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal` using `hw ▸ resChar_mem D w`. Establish `hc : IsCoprime (((D.mem u).A.T : ℕ) : ℤ) a` using `(Nat.prime_iff_prime_int.1 hp).irreducible.coprime_iff_not_dvd.2 (not_dvd_trace X u a ha)`. Take `⟨s, t, hst⟩` from `hc`. Apply `(D.plEq w).isPrime.ne_top` to reduce the goal to its premises.

Rewrite using `[Ideal.eq_top_iff_one]`. Establish `h` using `congrArg (Int.cast : ℤ → 𝓞 D.what₂.LL) hst`. Move the coercions through the operations in `at h`. Rewrite using `[← h]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ m4) (Ideal.mul_mem_left _ _ m3)`.
-/
theorem coprime_conj {D : D7} (X : ErrX D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hw : D.what₂.places.resChar w = (D.mem u).A.T) :
    ¬ (0 < vAdd (D.plEq w) (D.embE (X.piT u : D.host.E)) ∧
      0 < vAdd (D.plEq w) (star (D.embE (X.piT u : D.host.E)))) := by
  rintro ⟨h1, h2⟩
  obtain ⟨a, ha⟩ := trace_int D.host (X.piT u) (X.piT_K u)
  have hp := (D.mem u).A.T_prime
  have hn := X.piT_norm u
  have hT0 : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  rw [← hn] at hT0
  rw [← D.embE_conj] at h2
  have i1 : IsIntegral ℤ (D.embE (X.piT u : D.host.E)) :=
    IsIntegral.map D.embE.toIntAlgHom (X.piT u).isIntegral_coe
  have i2 : IsIntegral ℤ (D.embE (D.host.conj (X.piT u : D.host.E))) :=
    IsIntegral.map (D.embE.comp (D.host.conj : D.host.E →+* D.host.E)).toIntAlgHom (X.piT u).isIntegral_coe
  let y : 𝓞 D.what₂.LL := ⟨_, i1⟩
  let z : 𝓞 D.what₂.LL := ⟨_, i2⟩
  have hy : y ≠ 0 := fun h => (map_ne_zero D.embE).2 (left_ne_zero_of_mul hT0) (congrArg Subtype.val h)
  have hz : z ≠ 0 := fun h => (map_ne_zero D.embE).2 (right_ne_zero_of_mul hT0) (congrArg Subtype.val h)
  have m1 := (GlobalTheory.TypeLoss.mem_heightOneIdeal_iff_additiveValuation_pos (D.plEq w) y hy).2 h1
  have m2 := (GlobalTheory.TypeLoss.mem_heightOneIdeal_iff_additiveValuation_pos (D.plEq w) z hz).2 h2
  have e : ((a : ℤ) : 𝓞 D.what₂.LL) = y + z := by
    apply RingOfIntegers.coe_injective
    rw [map_intCast, map_add]
    change _ = D.embE _ + D.embE _
    rw [← map_add, ← ha, map_intCast]
  have m3 : ((a : ℤ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := e ▸ Ideal.add_mem _ m1 m2
  have m4 : (((D.mem u).A.T : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := hw ▸ resChar_mem D w
  have hc : IsCoprime (((D.mem u).A.T : ℕ) : ℤ) a :=
    (Nat.prime_iff_prime_int.1 hp).irreducible.coprime_iff_not_dvd.2 (not_dvd_trace X u a ha)
  obtain ⟨s, t, hst⟩ := hc
  apply (D.plEq w).isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have h := congrArg (Int.cast : ℤ → 𝓞 D.what₂.LL) hst
  push_cast at h
  rw [← h]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ m4) (Ideal.mul_mem_left _ _ m3)

end GlobalTheory.LevelCoprime
