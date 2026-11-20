import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.StatWPrimeExt
import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.Letters
import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.ResidueSeriesExpansionHolds

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N2

/- English proof (translation)
Introduce `ℓ _ hℓ A _ _ G n _ D _ _ _ _ Λ s H π₀ v hG hπ hL3 hs`. Establish `hprime : ℓ.Prime` using `Fact.out`. Establish `h3 : 3 ≤ ℓ` using `by have := hprime.two_le; omega`. Establish `hℓr : (3 : ℝ) ≤ (ℓ : ℝ)` using `by exact_mod_cast h3`. Establish `hsH : ∀ i, s i ≤ H` using `fun i => (hs i).2 H (hL3 i)`.

Establish `hK : ∀ i, (Λ.pair i).Kills (π₀ ^ ((s i + (ℓ - 2)) / (ℓ - 1)))`. Introduce `i x hx`. Establish `hle : s i ≤ (ℓ - 1) * ((s i + (ℓ - 2)) / (ℓ - 1))`. Establish `h1` using `Nat.div_add_mod (s i + (ℓ - 2)) (ℓ - 1)`. Establish `h2` using `Nat.mod_lt (s i + (ℓ - 2)) (show 0 < ℓ - 1 by omega)`.

Generalize the expression as in `(ℓ - 1) * ((s i + (ℓ - 2)) / (ℓ - 1)) = P at *`. Generalize the expression as in `(s i + (ℓ - 2)) % (ℓ - 1) = R at *`. Use linear arithmetic over natural numbers and integers. Take `⟨d, hd⟩` from `Nat.exists_eq_add_of_le hle`. Establish `e : (π₀ ^ ((s i + (ℓ - 2)) / (ℓ - 1))) • x = (v ^ ((s i + (ℓ - 2)) / (ℓ - 1)) * G.X ^ d) • (G.X ^ s i • x)`.

Rewrite using `[smul_smul, hπ, mul_pow, ← pow_mul, hd, pow_add]`. Put the polynomial expressions in normal form. Rewrite using `[e]`. Conclude with `(Λ.pair i).N'.smul_mem _ ((hs i).1 x hx)`. Establish `hC : ∀ i, (Λ.pair i).Kills ((ℓ : A) ^ cost ℓ 0 (s i))`.

Introduce `i`. Use `cost_bound_kills_obstruction ℓ hℓ A G D (Λ.pair i) (s i) 0 hG (Nat.zero_le _) (hs i).1` as an intermediate fact. Simplify using `using this`. Establish `hcost : ∀ i, (cost ℓ 0 (s i) : ℝ) < (s i : ℝ) * ℓ / ((ℓ : ℝ) - 1) ^ 2 + cW ℓ H`. Introduce `i`.

Establish `hb` using `cost_bound ℓ hℓ 0 (s i) H (Nat.zero_le _) (hsH i)`. Establish `hcw : 1 + Real.logb ℓ ((H : ℝ) + 1) ≤ cW ℓ H` using `Nat.le_ceil _`. Rewrite `hb` using `[Nat.cast_zero, sub_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hQ : ∀ (i : ZMod n) (r : ℕ), (Λ.pair i).Kills ((ℓ : A) ^ r) → (Λ.pair i).Kills ((π₀ + (ℓ : A)) ^ ((s i + (ℓ - 2)) / (ℓ - 1) + r))` using `fun i r hr => residue_quotient_holds A D (Λ.pair i).N (Λ.pair i).N' π₀ ℓ _ _ (hK i) hr`.

Use `⟨fun i a j haj => unconditional_first_statement ℓ hℓ A G D (Λ.pair i) (s i) H a j hG (hsH i) (hs i).1 haj, hK, hQ, fun i => hQ i _ (hC i), fun i => ?_, ?_⟩` and prove the remaining obligations. Establish `hA` using `residue_always_holds ℓ (s i) H (cW ℓ H) (cost ℓ 0 (s i)) h3 (hsH i) (hcost i).le`. Use `⟨hA.1, fun r hr => ?_⟩` and prove the remaining obligations. Establish `hr' : (r : ℝ) ≤ (cost ℓ 0 (s i) : ℝ)` using `by exact_mod_cast hr`. Combine the linear relations using `[hA.2]`.

Introduce `Mi hi hP5 hE10 hdec hind`. Take `⟨-, hfin, -, hcut⟩` from `unit_lemma_prime_case_holds ℓ hℓ A G n D Λ Mi hi s H hG hP5 hE10 hdec hind hL3 hs`. Establish `hL : (0 : ℝ) < (ℓ : ℝ) - 1` using `by linarith`. Establish `hL2 : (0 : ℝ) < (ℓ : ℝ) - 2` using `by linarith`. Establish `hrec : ∀ k, (s (k - 1) : ℝ) ≤ ((Mi k + hi k : ℕ) : ℝ) + (cW ℓ H : ℝ) + 3 + (s k : ℝ) / ((ℓ : ℝ) - 1)`.

Introduce `k`. Establish `h` using `hfin (k - 1) 1`. Simplify using `using h`. Use `⟨fun i => ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `hρ0 : (0 : ℝ) ≤ ((ℓ : ℝ) - 1)⁻¹` using `(inv_pos.mpr hL).le`.

Establish `hρ1 : ((ℓ : ℝ) - 1)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ (by linarith)`. Use `set M : ℝ := ∑ k, ((Mi k + hi k : ℕ) : ℝ) with hM`. Establish `hHM : ∀ k, ((Mi k + hi k : ℕ) : ℝ) ≤ M` using `fun k => Finset.single_le_sum (f := fun k => ((Mi k + hi k : ℕ) : ℝ)) (fun k _ => Nat.cast_nonneg _) (Finset.mem_univ k)`. Use `Summable.of_nonneg_of_le (fun a => ?_) (fun a => ?_) ((summable_geometric_of_lt_one hρ0 hρ1).mul_left (M + (cW ℓ H : ℝ) + 3))` and prove the remaining obligations. Conclude with `div_nonneg (by positivity) (pow_pos hL a).le`.

Rewrite using `[inv_pow, ← div_eq_mul_inv]`. Conclude with `div_le_div_of_nonneg_right (by have := hHM (i + ((a + 1 : ℕ) : ZMod n)); linarith) (pow_pos hL a).le`. Conclude with `residue_series_expansion_holds n (ℓ : ℝ) (cW ℓ H : ℝ) (fun k => (s k : ℝ)) (fun k => ((Mi k + hi k : ℕ) : ℝ)) hℓr (Nat.cast_nonneg _) (fun k => Nat.cast_nonneg _) hrec i`. Introduce `i j Gw hGw hw`. Establish `h1` using `hcut i j Gw hGw hw`.

Establish `h2` using `hcost i`. Establish `hpos : (0 : ℝ) ≤ (ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2` using `by positivity`. Establish `h4` using `mul_le_mul_of_nonneg_right h1 hpos`. Establish `e : ((2 * Gw + (cW ℓ H : ℝ) + 3) * ((ℓ : ℝ) - 1) / ((ℓ : ℝ) - 2) + (H : ℝ) / ((ℓ : ℝ) - 1) ^ j) * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) = (2 * Gw + (cW ℓ H : ℝ) + 3) * (ℓ : ℝ) / (((ℓ : ℝ) - 1) * ((ℓ : ℝ) - 2)) + (H : ℝ) * (ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 2)`. Establish `hL'` using `hL.ne'`.

Establish `hL2'` using `hL2.ne'`. Rewrite using `[pow_add]`. Clear the denominators using the available nonvanishing facts. Rewrite `h4` using `[e]`. Establish `e2 : (s i : ℝ) * ℓ / ((ℓ : ℝ) - 1) ^ 2 = (s i : ℝ) * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2)`.

Rewrite using `[mul_div_assoc]`. Rewrite `h2` using `[e2]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem unit_lemma_prime_extension_holds : StatWPrimeExt := by
  intro ℓ _ hℓ A _ _ G n _ D _ _ _ _ Λ s H π₀ v hG hπ hL3 hs
  have hprime : ℓ.Prime := Fact.out
  have h3 : 3 ≤ ℓ := by have := hprime.two_le; omega
  have hℓr : (3 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast h3
  have hsH : ∀ i, s i ≤ H := fun i => (hs i).2 H (hL3 i)
  have hK : ∀ i, (Λ.pair i).Kills (π₀ ^ ((s i + (ℓ - 2)) / (ℓ - 1))) := by
    intro i x hx
    have hle : s i ≤ (ℓ - 1) * ((s i + (ℓ - 2)) / (ℓ - 1)) := by
      have h1 := Nat.div_add_mod (s i + (ℓ - 2)) (ℓ - 1)
      have h2 := Nat.mod_lt (s i + (ℓ - 2)) (show 0 < ℓ - 1 by omega)
      generalize (ℓ - 1) * ((s i + (ℓ - 2)) / (ℓ - 1)) = P at *
      generalize (s i + (ℓ - 2)) % (ℓ - 1) = R at *
      omega
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    have e : (π₀ ^ ((s i + (ℓ - 2)) / (ℓ - 1))) • x =
        (v ^ ((s i + (ℓ - 2)) / (ℓ - 1)) * G.X ^ d) • (G.X ^ s i • x) := by
      rw [smul_smul, hπ, mul_pow, ← pow_mul, hd, pow_add]; ring_nf
    rw [e]
    exact (Λ.pair i).N'.smul_mem _ ((hs i).1 x hx)
  have hC : ∀ i, (Λ.pair i).Kills ((ℓ : A) ^ cost ℓ 0 (s i)) := by
    intro i
    have := cost_bound_kills_obstruction ℓ hℓ A G D (Λ.pair i) (s i) 0 hG (Nat.zero_le _) (hs i).1
    simpa using this
  have hcost : ∀ i, (cost ℓ 0 (s i) : ℝ) < (s i : ℝ) * ℓ / ((ℓ : ℝ) - 1) ^ 2 + cW ℓ H := by
    intro i
    have hb := cost_bound ℓ hℓ 0 (s i) H (Nat.zero_le _) (hsH i)
    have hcw : 1 + Real.logb ℓ ((H : ℝ) + 1) ≤ cW ℓ H := Nat.le_ceil _
    rw [Nat.cast_zero, sub_zero] at hb
    linarith
  have hQ : ∀ (i : ZMod n) (r : ℕ), (Λ.pair i).Kills ((ℓ : A) ^ r) →
      (Λ.pair i).Kills ((π₀ + (ℓ : A)) ^ ((s i + (ℓ - 2)) / (ℓ - 1) + r)) :=
    fun i r hr => residue_quotient_holds A D (Λ.pair i).N (Λ.pair i).N' π₀ ℓ _ _ (hK i) hr
  refine ⟨fun i a j haj => unconditional_first_statement ℓ hℓ A G D (Λ.pair i) (s i) H a j hG (hsH i) (hs i).1 haj,
    hK, hQ, fun i => hQ i _ (hC i), fun i => ?_, ?_⟩
  · have hA := residue_always_holds ℓ (s i) H (cW ℓ H) (cost ℓ 0 (s i)) h3 (hsH i) (hcost i).le
    refine ⟨hA.1, fun r hr => ?_⟩
    have hr' : (r : ℝ) ≤ (cost ℓ 0 (s i) : ℝ) := by exact_mod_cast hr
    linarith [hA.2]
  · intro Mi hi hP5 hE10 hdec hind
    obtain ⟨-, hfin, -, hcut⟩ :=
      unit_lemma_prime_case_holds ℓ hℓ A G n D Λ Mi hi s H hG hP5 hE10 hdec hind hL3 hs
    have hL : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
    have hL2 : (0 : ℝ) < (ℓ : ℝ) - 2 := by linarith
    have hrec : ∀ k, (s (k - 1) : ℝ) ≤
        ((Mi k + hi k : ℕ) : ℝ) + (cW ℓ H : ℝ) + 3 + (s k : ℝ) / ((ℓ : ℝ) - 1) := by
      intro k
      have h := hfin (k - 1) 1
      simpa using h
    refine ⟨fun i => ⟨?_, ?_⟩, ?_⟩
    · have hρ0 : (0 : ℝ) ≤ ((ℓ : ℝ) - 1)⁻¹ := (inv_pos.mpr hL).le
      have hρ1 : ((ℓ : ℝ) - 1)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
      set M : ℝ := ∑ k, ((Mi k + hi k : ℕ) : ℝ) with hM
      have hHM : ∀ k, ((Mi k + hi k : ℕ) : ℝ) ≤ M := fun k =>
        Finset.single_le_sum (f := fun k => ((Mi k + hi k : ℕ) : ℝ))
          (fun k _ => Nat.cast_nonneg _) (Finset.mem_univ k)
      refine Summable.of_nonneg_of_le (fun a => ?_) (fun a => ?_)
        ((summable_geometric_of_lt_one hρ0 hρ1).mul_left (M + (cW ℓ H : ℝ) + 3))
      · exact div_nonneg (by positivity) (pow_pos hL a).le
      · rw [inv_pow, ← div_eq_mul_inv]
        exact div_le_div_of_nonneg_right
          (by have := hHM (i + ((a + 1 : ℕ) : ZMod n)); linarith) (pow_pos hL a).le
    · exact residue_series_expansion_holds n (ℓ : ℝ) (cW ℓ H : ℝ) (fun k => (s k : ℝ))
        (fun k => ((Mi k + hi k : ℕ) : ℝ)) hℓr (Nat.cast_nonneg _) (fun k => Nat.cast_nonneg _)
        hrec i
    · intro i j Gw hGw hw
      have h1 := hcut i j Gw hGw hw
      have h2 := hcost i
      have hpos : (0 : ℝ) ≤ (ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2 := by positivity
      have h4 := mul_le_mul_of_nonneg_right h1 hpos
      have e : ((2 * Gw + (cW ℓ H : ℝ) + 3) * ((ℓ : ℝ) - 1) / ((ℓ : ℝ) - 2)
            + (H : ℝ) / ((ℓ : ℝ) - 1) ^ j) * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) =
          (2 * Gw + (cW ℓ H : ℝ) + 3) * (ℓ : ℝ) / (((ℓ : ℝ) - 1) * ((ℓ : ℝ) - 2))
            + (H : ℝ) * (ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 2) := by
        have hL' := hL.ne'
        have hL2' := hL2.ne'
        rw [pow_add]
        field_simp
      rw [e] at h4
      have e2 : (s i : ℝ) * ℓ / ((ℓ : ℝ) - 1) ^ 2 = (s i : ℝ) * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) := by
        rw [mul_div_assoc]
      rw [e2] at h2
      linarith

end Formalism.RepresentationBoundsCohomology.N2
