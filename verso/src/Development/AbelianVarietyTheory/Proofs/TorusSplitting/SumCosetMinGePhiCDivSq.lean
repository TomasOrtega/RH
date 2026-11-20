import Mathlib
import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.DataAtPointN3
import Formalism.LocalToGlobal.ProjectiveLattices.LiesOverBaseChange
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ETPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaVal

/- English proof (translation)
Introduce `E _ _ cj hcj w₀ hw X _ _ _ Q β hβQ hQnn m hm n y hgen v hv q hq`. Establish `hβpos : ∀ a, 0 ≤ (β : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) a a` using `fun a => by`. Rewrite using `[hβQ a]`. Establish `h' : (0 : ℝ) ≤ Q a` using `by exact_mod_cast hQnn a`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `choose z hz using fun b => Formalism.MainNotions.ModuliIntegralCharts.H1.etPoint_min Q hQnn (y b) m`. Establish `hgen' : ∀ a : X, ∃ u ∈ Submodule.span (𝓞 E) (Set.range y), ∃ t : X, a = u + m • t` using `fun a => by`. Take `⟨u, hu, t, ht⟩` from `hgen a`. Conclude with `⟨u, hu, m • t, by rw [ht, smul_smul, pow_two]⟩`. Establish `hspan` using `Formalism.MainNotions.ModuliIntegralCharts.H1.etSpan_holds E X m hm n y z hgen'`.

Establish `hphi` using `Formalism.MainNotions.ModuliIntegralCharts.H1.phiCSpan_holds E cj hcj X w₀ hw β hβpos n (fun b => y b + m • z b) hspan`. Establish `hsum : Formalism.MainNotions.ModuliIntegralCharts.phiC cj β ≤ ∑ b, (Q (y b + m • z b) : ℝ)`. Use `hphi.trans (le_of_eq (Finset.sum_congr rfl fun b _ => ?_))` and prove the remaining obligations. Establish `h` using `Formalism.MainNotions.ModuliIntegralCharts.H1.two_mul_form_half_unit hcj w₀ hw β (y b + m • z b)`. Rewrite `h` using `[hβQ]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hpt : ∀ b, (((Q (y b + m • z b) : ℚ) / ((m ^ 2 : ℕ) : ℚ) : ℚ) : WithTop ℚ) ≤ v b`. Introduce `b`. Use `hv b _ fun z' => ?_` and prove the remaining obligations. Establish `h : (Q (y b + m • z b) : ℚ) ≤ (Q (m • z' + y b) : ℚ)`.

Rewrite using `[add_comm (m • z')]`. Conclude with `hz b z'` after adjusting the coercions. Conclude with `div_le_div_of_nonneg_right h (by positivity)`. Establish `hR : (0 : ℝ) < (m : ℝ) ^ 2`. Establish `: (0 : ℝ) < m` using `by exact_mod_cast (show 0 < m by omega)`.

Check the signs of the components of the expression. Establish `hqR : (q : ℝ) ≤ ((∑ b, (Q (y b + m • z b) : ℚ) / ((m ^ 2 : ℕ) : ℚ) : ℚ) : ℝ)`. Use `push_cast`. Rewrite using `[← Finset.sum_div]`. Conclude with `hq.trans (div_le_div_of_nonneg_right hsum hR.le)`.

Establish `hqQ : q ≤ ∑ b, (Q (y b + m • z b) : ℚ) / ((m ^ 2 : ℕ) : ℚ)` using `by exact_mod_cast hqR`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem sum_cosetMin_ge_phiC_div_sq : ∀ (E : Type) [Field E] [NumberField E] (cj : E → E), (∀ c : 𝓞 E, ∃ c' : 𝓞 E, (c' : E) = cj c) → ∀ w₀ : 𝓞 E, (w₀ : E) + cj w₀ = 1 → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite ℤ X] (Q : X → ℤ) (β : Formalism.MainNotions.ModuliIntegralCharts.SymB cj X), (∀ a, (β : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) a a = 2 * (Q a : ℝ)) → (∀ a, 0 ≤ Q a) → ∀ (m : ℕ), 2 ≤ m → ∀ (n : ℕ) (y : Fin n → X), (∀ a : X, ∃ u ∈ Submodule.span (𝓞 E) (Set.range y), ∃ t : X, a = u + m ^ 2 • t) → ∀ v : Fin n → WithTop ℚ, (∀ b (q : ℚ), (∀ χ, q ≤ (Q (m • χ + y b) : ℚ) / (m ^ 2 : ℕ)) → (q : WithTop ℚ) ≤ v b) → ∀ q : ℚ, (q : ℝ) ≤ Formalism.MainNotions.ModuliIntegralCharts.phiC cj β / (m : ℝ) ^ 2 → (q : WithTop ℚ) ≤ ∑ b, v b := by
  intro E _ _ cj hcj w₀ hw X _ _ _ Q β hβQ hQnn m hm n y hgen v hv q hq
  have hβpos : ∀ a, 0 ≤ (β : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) a a := fun a => by
    rw [hβQ a]
    have h' : (0 : ℝ) ≤ Q a := by exact_mod_cast hQnn a
    linarith
  choose z hz using fun b => Formalism.MainNotions.ModuliIntegralCharts.H1.etPoint_min Q hQnn (y b) m
  have hgen' : ∀ a : X, ∃ u ∈ Submodule.span (𝓞 E) (Set.range y), ∃ t : X, a = u + m • t := fun a => by
    obtain ⟨u, hu, t, ht⟩ := hgen a
    exact ⟨u, hu, m • t, by rw [ht, smul_smul, pow_two]⟩
  have hspan := Formalism.MainNotions.ModuliIntegralCharts.H1.etSpan_holds E X m hm n y z hgen'
  have hphi := Formalism.MainNotions.ModuliIntegralCharts.H1.phiCSpan_holds E cj hcj X w₀ hw β hβpos n (fun b => y b + m • z b) hspan
  have hsum : Formalism.MainNotions.ModuliIntegralCharts.phiC cj β ≤ ∑ b, (Q (y b + m • z b) : ℝ) := by
    refine hphi.trans (le_of_eq (Finset.sum_congr rfl fun b _ => ?_))
    have h := Formalism.MainNotions.ModuliIntegralCharts.H1.two_mul_form_half_unit hcj w₀ hw β (y b + m • z b)
    rw [hβQ] at h
    linarith
  have hpt : ∀ b, (((Q (y b + m • z b) : ℚ) / ((m ^ 2 : ℕ) : ℚ) : ℚ) : WithTop ℚ) ≤ v b := by
    intro b
    refine hv b _ fun z' => ?_
    have h : (Q (y b + m • z b) : ℚ) ≤ (Q (m • z' + y b) : ℚ) := by
      rw [add_comm (m • z')]
      exact_mod_cast hz b z'
    exact div_le_div_of_nonneg_right h (by positivity)
  have hR : (0 : ℝ) < (m : ℝ) ^ 2 := by
    have : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    positivity
  have hqR : (q : ℝ) ≤ ((∑ b, (Q (y b + m • z b) : ℚ) / ((m ^ 2 : ℕ) : ℚ) : ℚ) : ℝ) := by
    push_cast
    rw [← Finset.sum_div]
    exact hq.trans (div_le_div_of_nonneg_right hsum hR.le)
  have hqQ : q ≤ ∑ b, (Q (y b + m • z b) : ℚ) / ((m ^ 2 : ℕ) : ℚ) := by exact_mod_cast hqR
  calc ((q : ℚ) : WithTop ℚ) ≤ ((∑ b, (Q (y b + m • z b) : ℚ) / ((m ^ 2 : ℕ) : ℚ) : ℚ) : WithTop ℚ) :=
        WithTop.coe_le_coe.2 hqQ
    _ = ∑ b, (((Q (y b + m • z b) : ℚ) / ((m ^ 2 : ℕ) : ℚ) : ℚ) : WithTop ℚ) := WithTop.coe_sum _ _
    _ ≤ ∑ b, v b := Finset.sum_le_sum fun b _ => hpt b

end GlobalTheory.EtaVal
