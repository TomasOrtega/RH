import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.WeilJacquetShalikaLaw

/- English proof (translation)
Take `⟨a, ha⟩` from `D.R.m_even`. Take `⟨b, hb⟩` from `D.R.t_odd`. Establish `hm : (D.R.m : ℝ) = 2 * (a : ℝ)` using `by rw [ha]; push_cast; ring`. Establish `ht : (D.R.t : ℝ) = 2 * (b : ℝ) + 1` using `by rw [hb]; push_cast; ring`. Unfold `EatT`.

Use `split_ifs with hs`. Use `first`. Consider the case `simp only [Formalism.MainNotions.G.Nm]`. Consider the case `simp only [Formalism.Nm]`. Consider the case `skip`.

Use `⟨D.R.m * (2 * ∑ τ : D.what₂.Tau, Wtau D u τ) + D.R.m * D.R.f * D.R.N D.R.m + (topsOf D.host D.eTau).card * (b + 1) * a * (2 * a + 1), ?_⟩` and prove the remaining obligations. Use `push_cast`. Rewrite using `[hm, ht]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `⟨0, by simp⟩`.
-/
theorem mEatT_nat (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) : ∃ n : ℕ, (D.R.m : ℝ) * EatT D u w = n := by
  classical
  obtain ⟨a, ha⟩ := D.R.m_even
  obtain ⟨b, hb⟩ := D.R.t_odd
  have hm : (D.R.m : ℝ) = 2 * (a : ℝ) := by rw [ha]; push_cast; ring
  have ht : (D.R.t : ℝ) = 2 * (b : ℝ) + 1 := by rw [hb]; push_cast; ring
  unfold EatT
  split_ifs with hs
  · first
    | simp only [Formalism.MainNotions.G.Nm]
    | simp only [Formalism.Nm]
    | skip
    refine ⟨D.R.m * (2 * ∑ τ : D.what₂.Tau, Wtau D u τ) + D.R.m * D.R.f * D.R.N D.R.m +
      (topsOf D.host D.eTau).card * (b + 1) * a * (2 * a + 1), ?_⟩
    push_cast
    rw [hm, ht]
    ring
  · exact ⟨0, by simp⟩

/- English proof (translation)
Rewrite using `[AddValuation.map_pow, ← hw, D.what₂.places.val_resChar w, ← WithTop.coe_nsmul]`. Use `congr 1`.
-/
theorem vAdd_Tpow (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hw : D.what₂.places.resChar w = (D.mem u).A.T) (n : ℕ) :
    D.what₂.places.val w ((((D.mem u).A.T : ℕ) : D.what₂.LL) ^ n) = (((n * D.what₂.places.ramIdx w : ℕ) : ℤ) : WithTop ℤ) := by
  rw [AddValuation.map_pow, ← hw, D.what₂.places.val_resChar w, ← WithTop.coe_nsmul]
  congr 1

/- English proof (translation)
Take `⟨n0, hn0⟩` from `mEatT_nat D u w`. Establish `hT0 : (((D.mem u).A.T : ℕ) : D.what₂.LL) ≠ 0`. Establish `hp` using `D.what₂.places.resChar_prime w`. Rewrite `hp` using `[hw]`. Conclude with `hp.ne_zero` after adjusting the coercions.

Establish `hc0 : (((D.mem u).A.T : ℕ) : D.what₂.LL) ^ n0 ≠ 0` using `pow_ne_zero _ hT0`. Establish `hval` using `vAdd_Tpow D u w hw n0`. Establish `hle : (D.what₂.places.ramIdx w : ℝ) * ((D.R.m : ℝ) * Formalism.MainNotions.product_first_zeroth_parts.ET D u w) ≤ (((n0 * D.what₂.places.ramIdx w : ℕ) : ℤ) : ℝ)` using `by show (D.what₂.places.ramIdx w : ℝ) * ((D.R.m : ℝ) * EatT D u w) ≤ _`. Rewrite using `[hn0]`. Use `push_cast`.

Rewrite using `[mul_comm]`. Take `⟨y', hy'S, hy'⟩` from `h5 w hw _ _ hval hle x hx`. Use `⟨((((D.mem u).A.T : ℕ) : D.what₂.LL) ^ n0)⁻¹ • y', ?_, ((((D.mem u).A.T : ℕ) : D.what₂.LL) ^ n0)⁻¹, y', hy'S, rfl, Or.inr ?_⟩` and prove the remaining obligations. Rewrite using `[map_smulₛₗ, hy', smul_smul, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_smul]`. Both sides reduce to the same expression.

Establish `hinv : D.what₂.places.val w ((((D.mem u).A.T : ℕ) : D.what₂.LL) ^ n0)⁻¹ = ((-((n0 * D.what₂.places.ramIdx w : ℕ) : ℤ) : ℤ) : WithTop ℤ)`. Rewrite using `[AddValuation.map_inv, hval]`. Both sides reduce to the same expression. Establish `hv` using `D.val_eq w _ (inv_ne_zero hc0)`. Rewrite `hv` using `[hinv]`.

Establish `hvz : vAdd (D.plEq w) ((((D.mem u).A.T : ℕ) : D.what₂.LL) ^ n0)⁻¹ = -((n0 * D.what₂.places.ramIdx w : ℕ) : ℤ)` using `(WithTop.coe_injective hv).symm`. Rewrite using `[hvz]`. Use `show (D.what₂.places.ramIdx w : ℝ) * (-((D.R.m : ℝ) * EatT D u w)) ≤ _`. Rewrite using `[hn0]`. Use `push_cast`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem ColGe0_atT (D : D7) (u : D.what₂.Word) (h5 : Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp D u) (w : D.what₂.places.Pl)
    (hw : D.what₂.places.resChar w = (D.mem u).A.T) (x : ((D.fm u).lat 0).V) (hx : x ∈ LT.Nlam D u w) :
    ColGe0 D u w x (-((D.R.m : ℝ) * EatT D u w)) := by
  obtain ⟨n0, hn0⟩ := mEatT_nat D u w
  have hT0 : (((D.mem u).A.T : ℕ) : D.what₂.LL) ≠ 0 := by
    have hp := D.what₂.places.resChar_prime w
    rw [hw] at hp
    exact_mod_cast hp.ne_zero
  have hc0 : (((D.mem u).A.T : ℕ) : D.what₂.LL) ^ n0 ≠ 0 := pow_ne_zero _ hT0
  have hval := vAdd_Tpow D u w hw n0
  have hle : (D.what₂.places.ramIdx w : ℝ) * ((D.R.m : ℝ) * Formalism.MainNotions.product_first_zeroth_parts.ET D u w) ≤
      (((n0 * D.what₂.places.ramIdx w : ℕ) : ℤ) : ℝ) := by
    show (D.what₂.places.ramIdx w : ℝ) * ((D.R.m : ℝ) * EatT D u w) ≤ _
    rw [hn0]
    push_cast
    rw [mul_comm]
  obtain ⟨y', hy'S, hy'⟩ := h5 w hw _ _ hval hle x hx
  refine ⟨((((D.mem u).A.T : ℕ) : D.what₂.LL) ^ n0)⁻¹ • y', ?_,
    ((((D.mem u).A.T : ℕ) : D.what₂.LL) ^ n0)⁻¹, y', hy'S, rfl, Or.inr ?_⟩
  · rw [map_smulₛₗ, hy', smul_smul, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_smul]
    rfl
  · have hinv : D.what₂.places.val w ((((D.mem u).A.T : ℕ) : D.what₂.LL) ^ n0)⁻¹ =
        ((-((n0 * D.what₂.places.ramIdx w : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
      rw [AddValuation.map_inv, hval]
      rfl
    have hv := D.val_eq w _ (inv_ne_zero hc0)
    rw [hinv] at hv
    have hvz : vAdd (D.plEq w) ((((D.mem u).A.T : ℕ) : D.what₂.LL) ^ n0)⁻¹ =
        -((n0 * D.what₂.places.ramIdx w : ℕ) : ℤ) := (WithTop.coe_injective hv).symm
    rw [hvz]
    show (D.what₂.places.ramIdx w : ℝ) * (-((D.R.m : ℝ) * EatT D u w)) ≤ _
    rw [hn0]
    push_cast
    nlinarith

end Formalism.MainNotions.J

end
