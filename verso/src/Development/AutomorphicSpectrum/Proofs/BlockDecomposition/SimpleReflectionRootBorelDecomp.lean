import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjTransposeAntidiagFixed

noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot

namespace GlobalTheory.CompanionTheory.SwapFactor

section Local
variable {L : Type} [Field L]

def betaU (x : L) (hx : x ≠ 0) : GL (Fin 2) L where
  val := !![-x⁻¹, 1; 0, x]
  inv := !![-x, 1; 0, x⁻¹]
  val_inv := by
    ext p r; fin_cases p <;> fin_cases r <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hx]
  inv_val := by
    ext p r; fin_cases p <;> fin_cases r <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hx]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `p r`. Apply the tactic sequence `fin_cases p <;> fin_cases r <;>`. Simplify using `[betaU, wU, nU, w2, Matrix.mul_apply, Fin.sum_univ_two, hx]`.
-/
theorem wU_mul_nU (x : L) (hx : x ≠ 0) :
    wU L * nU x = betaU x hx * (wU L * nU x⁻¹ * wU L) := by
  apply Units.ext
  ext p r
  fin_cases p <;> fin_cases r <;>
    simp [betaU, wU, nU, w2, Matrix.mul_apply, Fin.sum_univ_two, hx]

/- English proof (translation)
Establish `: ((betaU x hx)⁻¹ : GL (Fin 2) L).val = !![-x, 1; 0, x⁻¹]` using `rfl`. Establish `hw : ∀ M : Matrix (Fin 2) (Fin 2) L, (w2 L * M * w2 L) 1 0 = M 0 1` using `fun M => by`. Simplify using `[w2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]`. Rewrite using `[partner, hw, this]`. Simplify using `[cT]`.
-/
theorem partner_betaU_lower (σ : L →+* L) (x : L) (hx : x ≠ 0) : partner σ (betaU x hx) 1 0 = 0 := by
  have : ((betaU x hx)⁻¹ : GL (Fin 2) L).val = !![-x, 1; 0, x⁻¹] := rfl
  have hw : ∀ M : Matrix (Fin 2) (Fin 2) L, (w2 L * M * w2 L) 1 0 = M 0 1 := fun M => by
    simp [w2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  rw [partner, hw, this]
  simp [cT]

/- English proof (translation)
Establish `h2 : (Q ^ 2) ^ (-o) = Q ^ (-(2 * o))`. Rewrite using `[← zpow_natCast, ← zpow_mul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `h3 : Q ^ (-(-o) * N) * Q ^ (-o * (N - 2)) = Q ^ (2 * o)`. Rewrite using `[← zpow_add₀ hQ]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `h4 : v ^ o = (v ^ (-o))⁻¹` using `by rw [zpow_neg, inv_inv]`.

Rewrite using `[div_zpow, div_zpow, h2, zpow_neg Q (2 * o)]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem arith (u v Q : ℂ) (hQ : Q ≠ 0) (o N : ℤ) :
    u ^ (-o) * Q ^ (-(-o) * N) * (v ^ o * Q ^ (-o * (N - 2))) = ((u / v) / Q ^ 2) ^ (-o) := by
  have h2 : (Q ^ 2) ^ (-o) = Q ^ (-(2 * o)) := by
    rw [← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring
  have h3 : Q ^ (-(-o) * N) * Q ^ (-o * (N - 2)) = Q ^ (2 * o) := by
    rw [← zpow_add₀ hQ]; congr 1; ring
  have h4 : v ^ o = (v ^ (-o))⁻¹ := by rw [zpow_neg, inv_inv]
  rw [div_zpow, div_zpow, h2, zpow_neg Q (2 * o)]
  calc _ = u ^ (-o) * (v ^ (-o))⁻¹ * (Q ^ (-(-o) * N) * Q ^ (-o * (N - 2))) := by rw [h4]; ring
    _ = _ := by rw [h3]; simp [div_eq_mul_inv]

end Local

section Root
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {σ : L →+* L}

/- English proof (translation)
Establish `h1` using `v_eq_exp' (neg_ne_zero.2 hx)`. Rewrite `h1` using `[Valuation.map_neg, v_eq_exp' hx]`. Use `WithZero.exp_injective h1` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem ordL_neg' (x : L) (hx : x ≠ 0) : ordL (-x) = ordL x := by
  have h1 := v_eq_exp' (neg_ne_zero.2 hx)
  rw [Valuation.map_neg, v_eq_exp' hx] at h1
  have := WithZero.exp_injective h1
  omega

/- English proof (translation)
Simplify using `[ordL]`. Both sides reduce to the same expression.
-/
theorem ordL_one' : ordL (1 : L) = 0 := by simp [ordL]; rfl

/- English proof (translation)
Introduce `i j hji`. Rewrite using `[rootHom_val]`. Distinguish the cases in `hI : (∃ p, i = cI n a h p) ∧ ∃ r, j = cI n a h r`. Take `⟨⟨p, rfl⟩, r, rfl⟩` from `hI`. Rewrite using `[blockM_cI]`.

Establish `hlt : (cI n a h r : ℕ) < (cI n a h p : ℕ)` using `hji`. Simplify using `only [cI] at hlt`. Establish `hp : p = 1` using `Fin.ext (by have := p.2; simp only [Fin.val_one]; omega)`. Establish `hr : r = 0` using `Fin.ext (by have := r.2; simp only [Fin.val_zero]; omega)`. Substitute `hp hr` using the available equality.

Both sides reduce to the same expression. Distinguish the cases in `hJ : (∃ p, i = cJ n a h p) ∧ ∃ r, j = cJ n a h r`. Take `⟨⟨p, rfl⟩, r, rfl⟩` from `hJ`. Rewrite using `[blockM_cJ]`. Establish `hlt : (cJ n a h r : ℕ) < (cJ n a h p : ℕ)` using `hji`.

Simplify using `only [cJ] at hlt`. Establish `hp : p = 1` using `Fin.ext (by have := p.2; simp only [Fin.val_one]; omega)`. Establish `hr : r = 0` using `Fin.ext (by have := r.2; simp only [Fin.val_zero]; omega)`. Substitute `hp hr` using the available equality. Conclude with `partner_betaU_lower σ x hx`.

Rewrite using `[blockM_out]`. Conclude with `Matrix.one_apply_ne (ne_of_gt hji)`. Assume the negation of the conclusion as `hc push_neg at hc`. Conclude with `hI ⟨by simpa [eq_comm] using hc.1, by simpa using hc.2⟩`. Assume the negation of the conclusion as `hc push_neg at hc`.

Conclude with `hJ ⟨by simpa using hc.1, by simpa using hc.2⟩`.
-/
theorem isBorel_root (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (x : L) (hx : x ≠ 0) :
    IsBorelU (rootHom σ hσ a h (betaU x hx)) := by
  intro i j hji
  rw [rootHom_val]
  by_cases hI : (∃ p, i = cI n a h p) ∧ ∃ r, j = cI n a h r
  · obtain ⟨⟨p, rfl⟩, r, rfl⟩ := hI
    rw [blockM_cI]
    have hlt : (cI n a h r : ℕ) < (cI n a h p : ℕ) := hji
    simp only [cI] at hlt
    have hp : p = 1 := Fin.ext (by have := p.2; simp only [Fin.val_one]; omega)
    have hr : r = 0 := Fin.ext (by have := r.2; simp only [Fin.val_zero]; omega)
    subst hp hr
    rfl
  by_cases hJ : (∃ p, i = cJ n a h p) ∧ ∃ r, j = cJ n a h r
  · obtain ⟨⟨p, rfl⟩, r, rfl⟩ := hJ
    rw [blockM_cJ]
    have hlt : (cJ n a h r : ℕ) < (cJ n a h p : ℕ) := hji
    simp only [cJ] at hlt
    have hp : p = 1 := Fin.ext (by have := p.2; simp only [Fin.val_one]; omega)
    have hr : r = 0 := Fin.ext (by have := r.2; simp only [Fin.val_zero]; omega)
    subst hp hr
    exact partner_betaU_lower σ x hx
  rw [blockM_out]
  · exact Matrix.one_apply_ne (ne_of_gt hji)
  · by_contra hc
    push_neg at hc
    exact hI ⟨by simpa [eq_comm] using hc.1, by simpa using hc.2⟩
  · by_contra hc
    push_neg at hc
    exact hJ ⟨by simpa using hc.1, by simpa using hc.2⟩

/- English proof (translation)
Establish `e : (⟨a, hk⟩ : Fin n) = cI n a h 0` using `Fin.ext (by simp [cI])`. Rewrite using `[e, rootHom_val, blockM_cI]`. Both sides reduce to the same expression.
-/
theorem diag_a (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (x : L) (hx : x ≠ 0) (hk : a < n) :
    (((rootHom σ hσ a h (betaU x hx) : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) ⟨a, hk⟩ ⟨a, hk⟩ = -x⁻¹ := by
  have e : (⟨a, hk⟩ : Fin n) = cI n a h 0 := Fin.ext (by simp [cI])
  rw [e, rootHom_val, blockM_cI]
  rfl

/- English proof (translation)
Establish `e : (⟨a + 1, hk⟩ : Fin n) = cI n a h 1` using `Fin.ext (by simp [cI])`. Rewrite using `[e, rootHom_val, blockM_cI]`. Both sides reduce to the same expression.
-/
theorem root_hom_diag_entry_eq (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (x : L) (hx : x ≠ 0) (hk : a + 1 < n) :
    (((rootHom σ hσ a h (betaU x hx) : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) ⟨a + 1, hk⟩ ⟨a + 1, hk⟩ = x := by
  have e : (⟨a + 1, hk⟩ : Fin n) = cI n a h 1 := Fin.ext (by simp [cI])
  rw [e, rootHom_val, blockM_cI]
  rfl

/- English proof (translation)
Rewrite using `[rootHom_val, blockM_out]`. Conclude with `Matrix.one_apply_eq k`. Use `left`. Introduce `p e`. Use `congrArg Fin.val e` as an intermediate fact.

Establish `hp` using `p.2`. Simplify using `only [cI] at this`. Use linear arithmetic over natural numbers and integers. Use `left`. Introduce `p e`.

Use `congrArg Fin.val e` as an intermediate fact. Establish `hp` using `p.2`. Simplify using `only [cJ] at this`. Use linear arithmetic over natural numbers and integers.
-/
theorem diag_other (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (x : L) (hx : x ≠ 0) (k : Fin n)
    (hk : k.val < n / 2) (h1 : k.val ≠ a) (h2 : k.val ≠ a + 1) :
    (((rootHom σ hσ a h (betaU x hx) : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) k k = 1 := by
  rw [rootHom_val, blockM_out]
  · exact Matrix.one_apply_eq k
  · left
    intro p e
    have := congrArg Fin.val e
    have hp := p.2
    simp only [cI] at this
    omega
  · left
    intro p e
    have := congrArg Fin.val e
    have hp := p.2
    simp only [cJ] at this
    omega

end Root

/- English proof (translation)
Introduce `L _ _ ϖ σ q n hU a h χ i j hi hj x hx`. Establish `hq : (q : ℂ) ≠ 0`. Establish `: 2 ≤ q` using `hU.2.2.2.2.2.1`. Conclude with `Nat.cast_ne_zero.2 (by omega)`. Use `⟨rootHom σ hU.1 a h (betaU x hx), isBorel_root hU.1 a h x hx, ?_, ?_⟩` and prove the remaining obligations.

Establish `hij : i ≠ j` using `fun e => by`. Use `congrArg Fin.val e` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `ha : a < n` using `by omega`. Establish `ha1 : a + 1 < n` using `by omega`.

Establish `hin : i.val < n` using `by omega`. Establish `hjn : j.val < n` using `by omega`. Unfold `chiDeltaU`. Rewrite using `[Finset.prod_eq_mul i j hij ?_ (by simp) (by simp)]`. Rewrite using `[dif_pos hin, dif_pos hjn]`.

Establish `ei : (⟨i.val, hin⟩ : Fin n) = ⟨a, ha⟩` using `Fin.ext hi`. Establish `ej : (⟨j.val, hjn⟩ : Fin n) = ⟨a + 1, ha1⟩` using `Fin.ext hj`. Rewrite using `[ei, ej, diag_a, root_hom_diag_entry_eq, ordL_neg' _ (inv_ne_zero hx), ordL_inv' hx, hi, hj]`. Establish `hN : ((n : ℤ) - 1 - 2 * ((a + 1 : ℕ) : ℤ)) = ((n : ℤ) - 1 - 2 * (a : ℤ)) - 2` using `by push_cast; ring`. Rewrite using `[hN]`.

Conclude with `arith _ _ _ hq _ _`. Introduce `k _ hk`. Establish `hkn : k.val < n` using `by omega`. Rewrite using `[dif_pos hkn, diag_other hU.1 a h x hx ⟨k.val, hkn⟩ (by simpa using k.2) (fun e => hk.1 (Fin.ext (by simpa [hi] using e))) (fun e => hk.2 (Fin.ext (by simpa [hj] using e))), ordL_one']`. Simplify using the standard rewrite rules.

Simplify using `only [sR, uR, ← map_mul]`. Conclude with `congrArg _ (wU_mul_nU x hx)`.
-/
theorem sR_uR_factor : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ) (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n) (χ : Fin (n / 2) → ℂˣ) (i j : Fin (n / 2)), i.val = a → j.val = a + 1 → ∀ x : L, x ≠ 0 →
    ∃ b : GU σ n, IsBorelU b ∧
      chiDeltaU q (fun k => (χ k : ℂ)) b = (((χ i : ℂ) / (χ j : ℂ)) / (q : ℂ) ^ 2) ^ (-ordL x) ∧
      sR σ hU.1 a h * uR σ hU.1 a h x = b * (sR σ hU.1 a h * uR σ hU.1 a h x⁻¹ * sR σ hU.1 a h) := by
  intro L _ _ ϖ σ q n hU a h χ i j hi hj x hx
  have hq : (q : ℂ) ≠ 0 := by
    have : 2 ≤ q := hU.2.2.2.2.2.1
    exact Nat.cast_ne_zero.2 (by omega)
  refine ⟨rootHom σ hU.1 a h (betaU x hx), isBorel_root hU.1 a h x hx, ?_, ?_⟩
  · have hij : i ≠ j := fun e => by
      have := congrArg Fin.val e
      omega
    have ha : a < n := by omega
    have ha1 : a + 1 < n := by omega
    have hin : i.val < n := by omega
    have hjn : j.val < n := by omega
    unfold chiDeltaU
    rw [Finset.prod_eq_mul i j hij ?_ (by simp) (by simp)]
    · rw [dif_pos hin, dif_pos hjn]
      have ei : (⟨i.val, hin⟩ : Fin n) = ⟨a, ha⟩ := Fin.ext hi
      have ej : (⟨j.val, hjn⟩ : Fin n) = ⟨a + 1, ha1⟩ := Fin.ext hj
      rw [ei, ej, diag_a, root_hom_diag_entry_eq, ordL_neg' _ (inv_ne_zero hx), ordL_inv' hx, hi, hj]
      have hN : ((n : ℤ) - 1 - 2 * ((a + 1 : ℕ) : ℤ)) = ((n : ℤ) - 1 - 2 * (a : ℤ)) - 2 := by
        push_cast; ring
      rw [hN]
      exact arith _ _ _ hq _ _
    · intro k _ hk
      have hkn : k.val < n := by omega
      rw [dif_pos hkn, diag_other hU.1 a h x hx ⟨k.val, hkn⟩ (by simpa using k.2)
        (fun e => hk.1 (Fin.ext (by simpa [hi] using e)))
        (fun e => hk.2 (Fin.ext (by simpa [hj] using e))), ordL_one']
      simp
  · simp only [sR, uR, ← map_mul]
    exact congrArg _ (wU_mul_nU x hx)

end GlobalTheory.CompanionTheory.SwapFactor

end
