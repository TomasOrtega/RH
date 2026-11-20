import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.FixedMemRange

noncomputable section

namespace PI.OmVe

open PI.VolStabSW PI.VolStabSW.FFHS PI.OmLocU.CntFF Matrix

/- English proof (translation)
Introduce `k K _ _ _ _ σ hσ h2 hne M a haM J hJ hdJ T hT hTu`. Take `⟨i₀, hr, hc, hu⟩` from `hTu`. Take `⟨a', rfl⟩ : ∃ a', a = a' + 1` from `⟨a - 1, by have := i₀.pos; omega⟩`. Use `Fintype.ofFinite k` as an intermediate fact. Establish `: Module.Finite k K` using `Module.finite_of_finrank_pos (by omega)`.

Establish `: Finite K` using `Module.finite_of_finite k`. Use `Fintype.ofFinite K` as an intermediate fact. Establish `hK : Fintype.card K = Fintype.card k ^ 2`. Rewrite using `[Module.card_eq_pow_finrank (K := k), h2]`. Establish `hσ' : ∀ x, (σ : K →+* K) ((σ : K →+* K) x) = x` using `fun x => hσ x`.

Establish `hJ' : ∀ i j, (σ : K →+* K) (J j i) = J i j` using `hJ`. Establish `hu0 : IsUnit (T.submatrix i₀.succAbove i₀.succAbove).det`. Establish `e` using `det_corOne T i₀ hr 1`. Rewrite `e` using `[one_mul]`. Rewrite using `[← e]`.

Conclude with `hu`. Establish `hTt : ∀ c : k, c ≠ 0 → (∀ i j, σ ((T + Matrix.single i₀ i₀ (algebraMap k K c)) j i) = (T + Matrix.single i₀ i₀ (algebraMap k K c)) i j) ∧ IsUnit (T + Matrix.single i₀ i₀ (algebraMap k K c)).det`. Introduce `c hc0`. Use `⟨fun i j => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.add_apply, Matrix.add_apply, map_add, hT, Matrix.single_apply, Matrix.single_apply]`.

Use `congr 1`. Apply the tactic sequence `split_ifs with h1 h2 h2 <;> first | exact AlgEquiv.commutes σ c | exact map_zero σ | (exfalso; tauto)`. Rewrite using `[det_corOne T i₀ hr]`. Conclude with `(isUnit_iff_ne_zero.2 ((map_ne_zero _).2 hc0)).mul hu0`. Establish `hN : ∀ c : k, c ≠ 0 → Nat.card {X : Fin (a' + 1) → Fin M → K // ffGram (σ : K →+* K) J X = T + Matrix.single i₀ i₀ (algebraMap k K c)} = Nat.card {X : Fin (a' + 1) → Fin M → K // ffGram (σ : K →+* K) J X = T + Matrix.single i₀ i₀ (algebraMap k K 1)}`.

Introduce `c hc0`. Establish `e1` using `fFInert2_holds k K σ hσ h2 hne M (a' + 1) haM J hJ hdJ _ (hTt c hc0).1 (hTt c hc0).2`. Establish `e2` using `fFInert2_holds k K σ hσ h2 hne M (a' + 1) haM J hJ hdJ _ (hTt 1 one_ne_zero).1 (hTt 1 one_ne_zero).2`. Conclude with `e1.trans e2.symm` after adjusting the coercions. Establish `hD : ∀ Y : Fin a' → Fin M → K, ffGram (σ : K →+* K) J Y = T.submatrix i₀.succAbove i₀.succAbove → Nat.card {x : Fin M → K // (∀ j, ffH (σ : K →+* K) J (Y j) x = 0) ∧ ffH (σ : K →+* K) J x x = 0 ∧ ¬ ∀ c : K, c • x = 0 → c = 0} = 1`.

Introduce `Y _`. Rewrite using `[Nat.card_eq_one_iff_unique]`. Establish `h0 : ∀ z : Fin M → K, ¬ (∀ c : K, c • z = 0 → c = 0) → z = 0` using `fun z hz => by`. Assume the negation of the conclusion as `h0`. Conclude with `hz (fun c hc => (smul_eq_zero.1 hc).resolve_right h0)`.

Use `⟨⟨fun x y => Subtype.ext ((h0 x.1 x.2.2.2).trans (h0 y.1 y.2.2.2).symm)⟩, ⟨⟨0, ?_⟩⟩⟩` and prove the remaining obligations. Conclude with `⟨fun j => ffH_zero_right _ _ _, ffH_zero_left _ _ _, fun h => one_ne_zero (h 1 (smul_zero 1))⟩`. Establish `hcnt` using `count_gen (σ : K →+* K) J hσ' hJ' T i₀ hr hc hu (by omega) (ι := algebraMap k K) (algebraMap k K).injective (map_zero _) (fun x => fixed_mem_range σ h2 hne _ (ffH_herm (σ : K →+* K) J hσ' hJ' x x).symm) _ 1 hN hD`. Establish `hF0` using `fFInert2_holds k K σ hσ h2 hne M a' (by omega) J hJ hdJ (T.submatrix i₀.succAbove i₀.succAbove) (fun i j => hT _ _) hu0`. Establish `hN1` using `fFInert2_holds k K σ hσ h2 hne M (a' + 1) haM J hJ hdJ _ (hTt 1 one_ne_zero).1 (hTt 1 one_ne_zero).2`.

Establish `h1k : 1 ≤ Nat.card k` using `Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'`. Establish `hKk : Nat.card K = Nat.card k ^ 2` using `by simp only [Nat.card_eq_fintype_card]; exact hK`. Rewrite `hcnt` using `[hKk]`. Establish `hR` using `congrArg (fun n : ℕ => (n : ℝ)) hcnt`. Simplify using `only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub h1k, Nat.cast_one] at hR`.

Rewrite `hR` using `[hF0, hN1]`. Establish `hx : (Nat.card k : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 Nat.card_pos.ne'`. Rewrite `hR` using `[prodInert_closed _ hx M a' (by omega), prodInert_closed _ hx M (a' + 1) haM]`. Take `⟨n, hn⟩ : ∃ n, M = a' + 1 + n` from `⟨M - (a' + 1), by omega⟩`. Establish `eE : 2 * M * (a' + 1) - (a' + 1) ^ 2 = (2 * M * a' - a' ^ 2) + (2 * n + 1)`.

Substitute `hn` using the available equality. Establish `h3 : a' ^ 2 ≤ 2 * (a' + 1 + n) * a'` using `by nlinarith`. Establish `h4 : (a' + 1) ^ 2 ≤ 2 * (a' + 1 + n) * (a' + 1)` using `by nlinarith`. Use `zify [h3, h4]`. Expand and normalize the polynomial expressions, which then agree.

Establish `i1 : Finset.Icc (M - (a' + 1) + 1) M = insert (n + 1) (Finset.Icc (n + 2) M)`. Rewrite using `[show M - (a' + 1) + 1 = n + 1 by omega]`. Conclude with `(Finset.insert_Icc_add_one_left_eq_Icc (by omega)).symm`. Establish `i0 : Finset.Icc (M - (a' + 1)) M = insert n (insert (n + 1) (Finset.Icc (n + 2) M))`. Rewrite using `[show M - (a' + 1) = n by omega, ← Finset.insert_Icc_add_one_left_eq_Icc (show n ≤ M by omega), ← Finset.insert_Icc_add_one_left_eq_Icc (show n + 1 ≤ M by omega)]`.

Both sides reduce to the same expression. Rewrite `hR` using `[show M - a' + 1 = n + 2 by omega, show M - a' = n + 1 by omega, eE, pow_add, i1, Finset.prod_insert (by simp)]`. Rewrite using `[eE, pow_add, i0, Finset.prod_insert (by simp), Finset.prod_insert (by simp)]`. Use `set P0 := ∏ j ∈ Finset.Icc (n + 2) M, (1 - (-1 : ℝ) ^ j * (Nat.card k : ℝ) ^ (-(j : ℤ)))`. Use `set x := (Nat.card k : ℝ)`.

Use `set E0 := 2 * M * a' - a' ^ 2`. Take the linear combination `hR + (x ^ E0 * P0) * keyInert x hx n`.
-/
theorem fFInertB_holds : PI.OmVd.FFInertB := by
  intro k K _ _ _ _ σ hσ h2 hne M a haM J hJ hdJ T hT hTu
  classical
  obtain ⟨i₀, hr, hc, hu⟩ := hTu
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by have := i₀.pos; omega⟩
  have := Fintype.ofFinite k
  have : Module.Finite k K := Module.finite_of_finrank_pos (by omega)
  have : Finite K := Module.finite_of_finite k
  have := Fintype.ofFinite K
  have hK : Fintype.card K = Fintype.card k ^ 2 := by
    rw [Module.card_eq_pow_finrank (K := k), h2]
  have hσ' : ∀ x, (σ : K →+* K) ((σ : K →+* K) x) = x := fun x => hσ x
  have hJ' : ∀ i j, (σ : K →+* K) (J j i) = J i j := hJ
  have hu0 : IsUnit (T.submatrix i₀.succAbove i₀.succAbove).det := by
    have e := det_corOne T i₀ hr 1
    rw [one_mul] at e
    rw [← e]; exact hu
  have hTt : ∀ c : k, c ≠ 0 →
      (∀ i j, σ ((T + Matrix.single i₀ i₀ (algebraMap k K c)) j i) =
        (T + Matrix.single i₀ i₀ (algebraMap k K c)) i j) ∧
      IsUnit (T + Matrix.single i₀ i₀ (algebraMap k K c)).det := by
    intro c hc0
    refine ⟨fun i j => ?_, ?_⟩
    · rw [Matrix.add_apply, Matrix.add_apply, map_add, hT, Matrix.single_apply, Matrix.single_apply]
      congr 1
      split_ifs with h1 h2 h2 <;> first | exact AlgEquiv.commutes σ c | exact map_zero σ | (exfalso; tauto)
    · rw [det_corOne T i₀ hr]
      exact (isUnit_iff_ne_zero.2 ((map_ne_zero _).2 hc0)).mul hu0
  have hN : ∀ c : k, c ≠ 0 → Nat.card {X : Fin (a' + 1) → Fin M → K //
      ffGram (σ : K →+* K) J X = T + Matrix.single i₀ i₀ (algebraMap k K c)} =
      Nat.card {X : Fin (a' + 1) → Fin M → K //
        ffGram (σ : K →+* K) J X = T + Matrix.single i₀ i₀ (algebraMap k K 1)} := by
    intro c hc0
    have e1 := fFInert2_holds k K σ hσ h2 hne M (a' + 1) haM J hJ hdJ _ (hTt c hc0).1 (hTt c hc0).2
    have e2 := fFInert2_holds k K σ hσ h2 hne M (a' + 1) haM J hJ hdJ _ (hTt 1 one_ne_zero).1
      (hTt 1 one_ne_zero).2
    exact_mod_cast e1.trans e2.symm
  have hD : ∀ Y : Fin a' → Fin M → K, ffGram (σ : K →+* K) J Y = T.submatrix i₀.succAbove i₀.succAbove →
      Nat.card {x : Fin M → K // (∀ j, ffH (σ : K →+* K) J (Y j) x = 0) ∧ ffH (σ : K →+* K) J x x = 0 ∧
        ¬ ∀ c : K, c • x = 0 → c = 0} = 1 := by
    intro Y _
    rw [Nat.card_eq_one_iff_unique]
    have h0 : ∀ z : Fin M → K, ¬ (∀ c : K, c • z = 0 → c = 0) → z = 0 := fun z hz => by
      by_contra h0
      exact hz (fun c hc => (smul_eq_zero.1 hc).resolve_right h0)
    refine ⟨⟨fun x y => Subtype.ext ((h0 x.1 x.2.2.2).trans (h0 y.1 y.2.2.2).symm)⟩, ⟨⟨0, ?_⟩⟩⟩
    exact ⟨fun j => ffH_zero_right _ _ _, ffH_zero_left _ _ _, fun h => one_ne_zero (h 1 (smul_zero 1))⟩
  have hcnt := count_gen (σ : K →+* K) J hσ' hJ' T i₀ hr hc hu (by omega) (ι := algebraMap k K)
    (algebraMap k K).injective (map_zero _)
    (fun x => fixed_mem_range σ h2 hne _ (ffH_herm (σ : K →+* K) J hσ' hJ' x x).symm) _ 1 hN hD
  have hF0 := fFInert2_holds k K σ hσ h2 hne M a' (by omega) J hJ hdJ
    (T.submatrix i₀.succAbove i₀.succAbove) (fun i j => hT _ _) hu0
  have hN1 := fFInert2_holds k K σ hσ h2 hne M (a' + 1) haM J hJ hdJ _ (hTt 1 one_ne_zero).1
    (hTt 1 one_ne_zero).2
  have h1k : 1 ≤ Nat.card k := Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'
  have hKk : Nat.card K = Nat.card k ^ 2 := by simp only [Nat.card_eq_fintype_card]; exact hK
  rw [hKk] at hcnt
  have hR := congrArg (fun n : ℕ => (n : ℝ)) hcnt
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub h1k, Nat.cast_one] at hR
  rw [hF0, hN1] at hR
  have hx : (Nat.card k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [prodInert_closed _ hx M a' (by omega), prodInert_closed _ hx M (a' + 1) haM] at hR
  obtain ⟨n, hn⟩ : ∃ n, M = a' + 1 + n := ⟨M - (a' + 1), by omega⟩
  have eE : 2 * M * (a' + 1) - (a' + 1) ^ 2 = (2 * M * a' - a' ^ 2) + (2 * n + 1) := by
    subst hn
    have h3 : a' ^ 2 ≤ 2 * (a' + 1 + n) * a' := by nlinarith
    have h4 : (a' + 1) ^ 2 ≤ 2 * (a' + 1 + n) * (a' + 1) := by nlinarith
    zify [h3, h4]
    ring
  have i1 : Finset.Icc (M - (a' + 1) + 1) M = insert (n + 1) (Finset.Icc (n + 2) M) := by
    rw [show M - (a' + 1) + 1 = n + 1 by omega]
    exact (Finset.insert_Icc_add_one_left_eq_Icc (by omega)).symm
  have i0 : Finset.Icc (M - (a' + 1)) M = insert n (insert (n + 1) (Finset.Icc (n + 2) M)) := by
    rw [show M - (a' + 1) = n by omega, ← Finset.insert_Icc_add_one_left_eq_Icc (show n ≤ M by omega),
      ← Finset.insert_Icc_add_one_left_eq_Icc (show n + 1 ≤ M by omega)]
    rfl
  rw [show M - a' + 1 = n + 2 by omega, show M - a' = n + 1 by omega, eE, pow_add, i1,
    Finset.prod_insert (by simp)] at hR
  rw [eE, pow_add, i0, Finset.prod_insert (by simp), Finset.prod_insert (by simp)]
  set P0 := ∏ j ∈ Finset.Icc (n + 2) M, (1 - (-1 : ℝ) ^ j * (Nat.card k : ℝ) ^ (-(j : ℤ)))
  set x := (Nat.card k : ℝ)
  set E0 := 2 * M * a' - a' ^ 2
  linear_combination hR + (x ^ E0 * P0) * keyInert x hx n

end PI.OmVe
