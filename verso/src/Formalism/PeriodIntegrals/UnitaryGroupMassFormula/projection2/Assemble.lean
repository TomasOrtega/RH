import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.KappaZero

noncomputable section

namespace PI.OneCosetSharp.W

open Loc LocE

/- English proof (translation)
Use extensionality with `l`. Simplify using `only [eN, Pi.single_apply, Fin.ext_iff]`.
-/
theorem eN_eq_single {k : Type} [Field k] {N : ℕ} (i : ℕ) (hi : i < N) :
    eN k N i = Pi.single (⟨i, hi⟩ : Fin N) 1 := by
  ext l
  simp only [eN, Pi.single_apply, Fin.ext_iff]

/- English proof (translation)
Simplify using `only [inX, LinearMap.pi_apply]`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem inX_apply {k : Type} [Field k] {n c : ℕ} (v : Fin n → k) (l : Fin (n + c)) :
    inX k n c v l = if h : l.1 < n then v ⟨l.1, h⟩ else 0 := by
  simp only [inX, LinearMap.pi_apply]
  split_ifs <;> rfl

/- English proof (translation)
Use `⟨fun i => w ⟨i.1, by omega⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `l`. Rewrite using `[inX_apply]`. Use `split_ifs with h`. Both sides reduce to the same expression.

Conclude with `(hw l (not_lt.mp h)).symm`.
-/
theorem inX_of_zero {k : Type} [Field k] {n c : ℕ} (w : Fin (n + c) → k) (hw : ∀ l : Fin (n + c), n ≤ l.1 → w l = 0) :
    ∃ v, inX k n c v = w := by
  refine ⟨fun i => w ⟨i.1, by omega⟩, ?_⟩
  ext l
  rw [inX_apply]
  split_ifs with h
  · rfl
  · exact (hw l (not_lt.mp h)).symm

/- English proof (translation)
Establish `hl' : ¬ l.1 < n` using `not_lt.mpr hl`. Rewrite using `[eN_eq_single s (by omega)]`. Simplify using `[xx1, Matrix.mulVec_single, IsFree, hs, hl', not_le.mpr hs]`.
-/
theorem embedMatrix_basisVec_apply_of_le {k : Type} [Field k] {n' c n : ℕ} (xj : (Fin n' → k) →ₗ[k] (Fin n → k))
    (tt : FC n' (c + 1) n c → k) (s : ℕ) (hs : s < n') (l : Fin (n + c)) (hl : n ≤ l.1) :
    xx1 xj tt (eN k (n' + (c + 1)) s) l = 0 := by
  have hl' : ¬ l.1 < n := not_lt.mpr hl
  rw [eN_eq_single s (by omega)]
  simp [xx1, Matrix.mulVec_single, IsFree, hs, hl', not_le.mpr hs]

/- English proof (translation)
Assume the negation of the conclusion as `H`. Simplify using `only [not_exists, not_not] at H`. Apply `hE` to reduce the goal to its premises. Simplify using `[E1, om, H]`.
-/
theorem sum_step {k : Type} [Field k] [Fintype k] (ψ₀ : AddChar k ℂ) (χ : ℕ → kˣ →* ℂˣ) (k₀ m t j n' c n : ℕ)
    (h : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) (xj : (Fin n' → k) →ₗ[k] (Fin n → k))
    (hE : E1 (n' := n') (c' := c + 1) (n := n) (c := c) (fun u => ψ₀ u) Finset.univ 1
            (om (fun _ => 1) (fun _ => 0) 1 (LinearEquiv.refl k _) h (PhiS ψ₀ χ k₀ m t j n' c n)) xj ≠ 0) :
    ∃ tt, PhiS ψ₀ χ k₀ m t j n' c n (h.symm.toLinearMap ∘ₗ xx1 xj tt) ≠ 0 := by
  by_contra H
  simp only [not_exists, not_not] at H
  apply hE
  simp [E1, om, H]

/- English proof (translation)
Unfold `fIdx`. Rewrite using `[if_neg (by omega), if_pos (by omega)]`. Use linear arithmetic over natural numbers and integers.
-/
theorem fIdx_add_of_lt (k₀ c n i : ℕ) (hi : i < c) : fIdx k₀ c n (k₀ + i) = n + i := by
  unfold fIdx
  rw [if_neg (by omega), if_pos (by omega)]
  omega

/- English proof (translation)
Take `⟨-, -, h4, hj1, hj2, hc, h7, -⟩` from `hn`. Generalize the expression as in `(j - 1) * t = X at h7`. Use linear arithmetic over natural numbers and integers.
-/
theorem Nums.n'_ge {k₀ m t j n' c n : ℕ} (hn : Nums k₀ m t j n' c n) : k₀ ≤ n' := by
  obtain ⟨-, -, h4, hj1, hj2, hc, h7, -⟩ := hn
  generalize (j - 1) * t = X at h7
  omega

/- English proof (translation)
Introduce `k _ _ ψ₀ χ k₀ m t j n' c n hnum h ⟨xj, hE⟩`. Take `⟨tt, htt⟩` from `sum_step ψ₀ χ k₀ m t j n' c n h xj hE`. Take `⟨κ, hκ, hκe⟩` from `hK k ψ₀ χ k₀ m t j n' c n hnum _ htt`. Take `⟨ν, hνR, hνX, hνe⟩` from `hN k n' c n xj tt`. Establish `hk₀` using `Nums.n'_ge hnum`.

Establish `hνinv : ∀ y z, ν z = y → ν⁻¹ y = z`. Introduce `y z hz`. Rewrite using `[← hz]`. Use `show (ν⁻¹ * ν) z = z`. Rewrite using `[inv_mul_cancel]`.

Both sides reduce to the same expression. Establish `g1 : ∀ i < c, (ν⁻¹ * h * κ) (eN k (n + c) (n + i)) = eN k (n + c) (n + i)`. Introduce `i hi`. Establish `e1` using `hκe (k₀ + i) (by omega)`. Rewrite `e1` using `[fIdx_add_of_lt k₀ c n i hi, fIdx_add_of_lt k₀ (c + 1) n' i (by omega)]`.

Use `show ν⁻¹ (h (κ (eN k (n + c) (n + i)))) = eN k (n + c) (n + i)`. Rewrite using `[e1]`. Apply `hνinv` to reduce the goal to its premises. Rewrite using `[hνe i hi]`. Simplify using the standard rewrite rules.

Establish `g2 : ∀ p < n' + (c + 1), (p < k₀ ∨ k₀ + c < p) → ∃ v, (ν⁻¹ * h * κ) (eN k (n + c) (fIdx k₀ c n p)) = inX k n c v`. Introduce `p hp hcase`. Establish `hs : fIdx k₀ (c + 1) n' p < n'`. Unfold `fIdx`. Apply the tactic sequence `split_ifs <;> omega`.

Take `⟨v, hv⟩` from `inX_of_zero (xx1 xj tt (eN k (n' + (c + 1)) (fIdx k₀ (c + 1) n' p))) (fun l hl => embedMatrix_basisVec_apply_of_le xj tt _ hs l hl)`. Use `⟨v, ?_⟩` and prove the remaining obligations. Use `show ν⁻¹ (h (κ (eN k (n + c) (fIdx k₀ c n p)))) = inX k n c v`. Rewrite using `[hκe p hp]`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]`.

Rewrite using `[← hv]`. Conclude with `hνinv _ _ (hνX v)`. Take `⟨γ, hγ, κ', hκ', hg⟩` from `hG k k₀ m t j n' c n hnum (ν⁻¹ * h * κ) g1 g2`. Establish `hκinv` using `(hP k k₀ m t j n' c n hnum κ κ hκ hκ).2`. Use `⟨ν * γ, mul_mem hνR hγ, κ' * κ⁻¹, (hP k k₀ m t j n' c n hnum κ' κ⁻¹ hκ' hκinv).1, ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem claim1_of (hP : PatClosed) (hK : KappaZero) (hN : NElem) (hG : GaStep) : Claim1 := by
  intro k _ _ ψ₀ χ k₀ m t j n' c n hnum h ⟨xj, hE⟩
  obtain ⟨tt, htt⟩ := sum_step ψ₀ χ k₀ m t j n' c n h xj hE
  obtain ⟨κ, hκ, hκe⟩ := hK k ψ₀ χ k₀ m t j n' c n hnum _ htt
  obtain ⟨ν, hνR, hνX, hνe⟩ := hN k n' c n xj tt
  have hk₀ := Nums.n'_ge hnum
  have hνinv : ∀ y z, ν z = y → ν⁻¹ y = z := by
    intro y z hz
    rw [← hz]
    show (ν⁻¹ * ν) z = z
    rw [inv_mul_cancel]
    rfl
  have g1 : ∀ i < c, (ν⁻¹ * h * κ) (eN k (n + c) (n + i)) = eN k (n + c) (n + i) := by
    intro i hi
    have e1 := hκe (k₀ + i) (by omega)
    rw [fIdx_add_of_lt k₀ c n i hi, fIdx_add_of_lt k₀ (c + 1) n' i (by omega)] at e1
    show ν⁻¹ (h (κ (eN k (n + c) (n + i)))) = eN k (n + c) (n + i)
    rw [e1]
    apply hνinv
    rw [hνe i hi]
    simp
  have g2 : ∀ p < n' + (c + 1), (p < k₀ ∨ k₀ + c < p) →
      ∃ v, (ν⁻¹ * h * κ) (eN k (n + c) (fIdx k₀ c n p)) = inX k n c v := by
    intro p hp hcase
    have hs : fIdx k₀ (c + 1) n' p < n' := by
      unfold fIdx
      split_ifs <;> omega
    obtain ⟨v, hv⟩ := inX_of_zero (xx1 xj tt (eN k (n' + (c + 1)) (fIdx k₀ (c + 1) n' p)))
      (fun l hl => embedMatrix_basisVec_apply_of_le xj tt _ hs l hl)
    refine ⟨v, ?_⟩
    show ν⁻¹ (h (κ (eN k (n + c) (fIdx k₀ c n p)))) = inX k n c v
    rw [hκe p hp]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rw [← hv]
    exact hνinv _ _ (hνX v)
  obtain ⟨γ, hγ, κ', hκ', hg⟩ := hG k k₀ m t j n' c n hnum (ν⁻¹ * h * κ) g1 g2
  have hκinv := (hP k k₀ m t j n' c n hnum κ κ hκ hκ).2
  refine ⟨ν * γ, mul_mem hνR hγ, κ' * κ⁻¹,
    (hP k k₀ m t j n' c n hnum κ' κ⁻¹ hκ' hκinv).1, ?_⟩
  calc h = ν * (ν⁻¹ * h * κ) * κ⁻¹ := by group
    _ = ν * γ * (κ' * κ⁻¹) := by rw [hg]; group

end PI.OneCosetSharp.W
