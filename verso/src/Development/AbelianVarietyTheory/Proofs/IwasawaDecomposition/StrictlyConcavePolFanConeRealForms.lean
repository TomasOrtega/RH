import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdConeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsStrictIff

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolCell

/- English proof (translation)
Introduce `X _ _ φ N m u w hF hu hS`. Take `⟨h1, h2, h3⟩` from `hS`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `B ⟨t, ht, rfl⟩`. Rewrite using `[(linearOn_iff φ u).1 hu.linear t ht, evalW_sum, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[h1 i]`. Expand and normalize the polynomial expressions, which then agree. Introduce `B hB`. Take `⟨m', γ, c, hγ, hc, rfl⟩` from `hF.cover B hB`.

Establish `hle : ∀ i, (N : ℝ) * φ.evalZ (γ i) ≤ linW w (γ i)` using `fun i => h2 _ (hγ.mem i) (hγ.nonneg i)`. Rewrite using `[(linearOn_iff φ γ).1 hγ.linear c hc, evalW_sum, Finset.mul_sum]`. Establish `hterm : ∀ i, (N : ℝ) * (c i * φ.evalZ (γ i)) ≤ c i * linW w (γ i)` using `fun i => by`. Rewrite using `[mul_left_comm]`. Conclude with `mul_le_mul_of_nonneg_left (hle i) (hc i)`.

Use `⟨Finset.sum_le_sum fun i _ => hterm i, fun he => ?_⟩` and prove the remaining obligations. Establish `heq : ∀ i, (N : ℝ) * (c i * φ.evalZ (γ i)) = c i * linW w (γ i)` using `fun i => (Finset.sum_eq_sum_iff_of_le fun i _ => hterm i).1 he i (Finset.mem_univ i)`. Establish `hd : ∀ i, ∃ d : Fin m → ℝ, (∀ j, 0 ≤ d j) ∧ c i • toReal (γ i) = ∑ j, d j • toReal (u j)`. Introduce `i`. Break down `(hc i).eq_or_lt with h0 | h0` into its components or cases.

Conclude with `⟨0, fun _ => le_rfl, by simp [← h0]⟩`. Establish `hi : (N : ℝ) * φ.evalZ (γ i) = linW w (γ i)`. Use `heq i` as an intermediate fact. Rewrite `this` using `[mul_left_comm]`. Conclude with `mul_left_cancel₀ h0.ne' this`.

Take `⟨k, e, hk, hke⟩` from `h3 _ (hγ.mem i) (hγ.nonneg i) hi`. Use `⟨fun j => c i * e j / k, fun j => by positivity, LinearMap.ext₂ fun a b => ?_⟩` and prove the remaining obligations. Use `LinearMap.congr_fun₂ hke a b` as an intermediate fact. Simplify using `only [LinearMap.smul_apply, LinearMap.sum_apply, nsmul_eq_mul, smul_eq_mul] at this`. Establish `hk' : (k : ℝ) ≠ 0` using `by positivity`.

Establish `this' : (k : ℝ) * (γ i a b : ℝ) = ∑ j, (e j : ℝ) * (u j a b : ℝ)` using `by exact_mod_cast this`. Simplify using `only [LinearMap.smul_apply, LinearMap.sum_apply, toReal_apply, smul_eq_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[this', Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring`. Use `choose d hd0 hd1 using hd`.

Use `⟨fun j => ∑ i, d i j, fun j => Finset.sum_nonneg fun i _ => hd0 i j, ?_⟩` and prove the remaining obligations. Simplify using `only [hd1, Finset.sum_smul]`. Conclude with `Finset.sum_comm`.
-/
theorem strictWith_real : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (φ : InvFun ℤ) (N m : ℕ)
    (u : Fin m → LinearMap.BilinForm ℤ X) (w : (X × X) →₀ ℤ), IsPolFanOn (id : ℤ → ℤ) φ X → IsCone (id : ℤ → ℤ) φ u →
    StrictWith (id : ℤ → ℤ) φ N (linW w) u → (∀ B ∈ rcone u, (N : ℝ) * evalR φ B = evalW w B) ∧
      ∀ B ∈ psdCone (id : ℤ → ℤ) X, (N : ℝ) * evalR φ B ≤ evalW w B ∧ ((N : ℝ) * evalR φ B = evalW w B → B ∈ rcone u) := by
  intro X _ _ φ N m u w hF hu hS
  obtain ⟨h1, h2, h3⟩ := hS
  refine ⟨?_, ?_⟩
  · rintro B ⟨t, ht, rfl⟩
    rw [(linearOn_iff φ u).1 hu.linear t ht, evalW_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h1 i]; ring
  · intro B hB
    obtain ⟨m', γ, c, hγ, hc, rfl⟩ := hF.cover B hB
    have hle : ∀ i, (N : ℝ) * φ.evalZ (γ i) ≤ linW w (γ i) := fun i => h2 _ (hγ.mem i) (hγ.nonneg i)
    rw [(linearOn_iff φ γ).1 hγ.linear c hc, evalW_sum, Finset.mul_sum]
    have hterm : ∀ i, (N : ℝ) * (c i * φ.evalZ (γ i)) ≤ c i * linW w (γ i) := fun i => by
      rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left (hle i) (hc i)
    refine ⟨Finset.sum_le_sum fun i _ => hterm i, fun he => ?_⟩
    have heq : ∀ i, (N : ℝ) * (c i * φ.evalZ (γ i)) = c i * linW w (γ i) :=
      fun i => (Finset.sum_eq_sum_iff_of_le fun i _ => hterm i).1 he i (Finset.mem_univ i)
    have hd : ∀ i, ∃ d : Fin m → ℝ, (∀ j, 0 ≤ d j) ∧ c i • toReal (γ i) = ∑ j, d j • toReal (u j) := by
      intro i
      rcases (hc i).eq_or_lt with h0 | h0
      · exact ⟨0, fun _ => le_rfl, by simp [← h0]⟩
      · have hi : (N : ℝ) * φ.evalZ (γ i) = linW w (γ i) := by
          have := heq i
          rw [mul_left_comm] at this
          exact mul_left_cancel₀ h0.ne' this
        obtain ⟨k, e, hk, hke⟩ := h3 _ (hγ.mem i) (hγ.nonneg i) hi
        refine ⟨fun j => c i * e j / k, fun j => by positivity, LinearMap.ext₂ fun a b => ?_⟩
        have := LinearMap.congr_fun₂ hke a b
        simp only [LinearMap.smul_apply, LinearMap.sum_apply, nsmul_eq_mul, smul_eq_mul] at this
        have hk' : (k : ℝ) ≠ 0 := by positivity
        have this' : (k : ℝ) * (γ i a b : ℝ) = ∑ j, (e j : ℝ) * (u j a b : ℝ) := by exact_mod_cast this
        simp only [LinearMap.smul_apply, LinearMap.sum_apply, toReal_apply, smul_eq_mul]
        calc c i * (γ i a b : ℝ) = c i / k * (k * γ i a b) := by field_simp
          _ = ∑ j, c i * e j / k * u j a b := by
            rw [this', Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    choose d hd0 hd1 using hd
    refine ⟨fun j => ∑ i, d i j, fun j => Finset.sum_nonneg fun i _ => hd0 i j, ?_⟩
    simp only [hd1, Finset.sum_smul]
    exact Finset.sum_comm

end GlobalTheory.PolCell
