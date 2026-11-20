import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

/- English proof (translation)
Apply `GlobalTheory.TiltAlgClosed.dvd_of_untilt_dvd` to reduce the goal to its premises. Rewrite using `[GlobalTheory.RingBasics.untilt_σF]`. Generalize the expression as in `x.untilt = y`. Distinguish the cases in `hy : (y : ℂ_[l]) = 0`. Take `rfl : y = 0` from `Subtype.ext hy`.

Simplify using the standard rewrite rules. Use `⟨⟨Per.σC g y / y, (GlobalTheory.RingBasics.mem_OC _).2 ?_⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[norm_div, GlobalTheory.RingBasics.norm_σC, div_self (norm_ne_zero_iff.2 hy)]`. Rewrite using `[GlobalTheory.RingIface.sigO_coe]`. Express the relevant statement in the definitionally equal form `Per.σC g y = (y : ℂ_[l]) * (Per.σC g y / y)`.

Clear the denominators using the available nonvanishing facts.
-/
theorem dvd_σF_self {l : ℕ} [Fact l.Prime] (g : GQ l) (x : Per.Fl l) : x ∣ Per.σF g x := by
  apply GlobalTheory.TiltAlgClosed.dvd_of_untilt_dvd
  rw [GlobalTheory.RingBasics.untilt_σF]
  generalize x.untilt = y
  by_cases hy : (y : ℂ_[l]) = 0
  · obtain rfl : y = 0 := Subtype.ext hy
    simp
  · refine ⟨⟨Per.σC g y / y, (GlobalTheory.RingBasics.mem_OC _).2 ?_⟩, Subtype.ext ?_⟩
    · rw [norm_div, GlobalTheory.RingBasics.norm_σC, div_self (norm_ne_zero_iff.2 hy)]
    · rw [GlobalTheory.RingIface.sigO_coe]
      change Per.σC g y = (y : ℂ_[l]) * (Per.σC g y / y)
      field_simp

/- English proof (translation)
Introduce `l _ K bk`. Establish `h : ∀ g : GQ l, bk.ev X ∣ Per.σA g (bk.ev X)` using `fun g => by`. Rewrite using `[bk.ev_X, GlobalTheory.RingIface.sigA_teich]`. Conclude with `map_dvd (WittVector.teichmuller l) (dvd_σF_self g bk.flat)`. Use `⟨h, fun ρ hρ g => ⟨_, isDiscMap_map (Per.σA g) ?_⟩⟩` and prove the remaining obligations.

Take `⟨c, hc⟩` from `h g`. Establish `h1` using `norm_toDisc_pow_le (l := l) (u := bk.ev X) 1 hρ`. Rewrite `h1` using `[pow_one, pow_one]`. Rewrite using `[hc, map_mul]`. Conclude with `(norm_mul_le _ _).trans ((mul_le_mul h1 (norm_toDisc_le c) (norm_nonneg _) ρ.2).trans (mul_one _).le)`.
-/
theorem galois_discMap : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K),
    (∀ g : GQ l, bk.ev X ∣ Per.σA g (bk.ev X)) ∧ ∀ (ρ : ℝ≥0), 0 < ρ → ∀ g : GQ l,
      ∃ G : bk.DA ρ →+* bk.DA ρ, IsDiscMap (Per.σA g) G := by
  intro l _ K bk
  have h : ∀ g : GQ l, bk.ev X ∣ Per.σA g (bk.ev X) := fun g => by
    rw [bk.ev_X, GlobalTheory.RingIface.sigA_teich]
    exact map_dvd (WittVector.teichmuller l) (dvd_σF_self g bk.flat)
  refine ⟨h, fun ρ hρ g => ⟨_, isDiscMap_map (Per.σA g) ?_⟩⟩
  obtain ⟨c, hc⟩ := h g
  have h1 := norm_toDisc_pow_le (l := l) (u := bk.ev X) 1 hρ
  rw [pow_one, pow_one] at h1
  rw [hc, map_mul]
  exact (norm_mul_le _ _).trans ((mul_le_mul h1 (norm_toDisc_le c) (norm_nonneg _) ρ.2).trans (mul_one _).le)

end GlobalTheory.BSP
