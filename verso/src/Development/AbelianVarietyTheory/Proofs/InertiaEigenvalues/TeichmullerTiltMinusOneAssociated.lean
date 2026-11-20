import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerSubOneAinfPropertiesCompatibleRoots
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.EpsilonAssociated

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.1, (frobeniusEquiv (OCb l) l).symm e, frobeniusEquiv_symm_pow_p (OCb l) l e, h.2⟩`.
-/
theorem isEps_bk {l : ℕ} [Fact l.Prime] {e : OCb l} (h : IsEps e) : GlobalTheory.BKGal.IsEps e :=
  ⟨h.1, (frobeniusEquiv (OCb l) l).symm e, frobeniusEquiv_symm_pow_p (OCb l) l e, h.2⟩

/- English proof (translation)
Introduce `l _ e e' he he'`. Establish `h1 : mu e ∣ mu e'` using `GlobalTheory.MuOfEps.muOf_dvd (isEps_bk he) he'.1`. Establish `h2 : mu e' ∣ mu e` using `GlobalTheory.MuOfEps.muOf_dvd (isEps_bk he') he.1`. Take `⟨a, ha⟩` from `h1`. Take `⟨b, hb⟩` from `h2`.

Establish `hne : mu e ≠ 0` using `GlobalTheory.MuOfEps.muOf_ne_zero (isEps_bk he)`. Establish `hab : a * b = 1`. Establish `h3 : (a * b - 1) * mu e = 0`. Establish `: mu e = mu e * a * b` using `by rw [← ha]; exact hb`. Take the linear combination `-this`.

Conclude with `sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right hne)`. Conclude with `⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha.symm⟩`.
-/
theorem mu_associated : ∀ (l : ℕ) [Fact l.Prime] (e e' : OCb l), IsEps e → IsEps e' →
    Associated (mu e) (mu e') := by
  intro l _ e e' he he'
  have h1 : mu e ∣ mu e' := GlobalTheory.MuOfEps.muOf_dvd (isEps_bk he) he'.1
  have h2 : mu e' ∣ mu e := GlobalTheory.MuOfEps.muOf_dvd (isEps_bk he') he.1
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  have hne : mu e ≠ 0 := GlobalTheory.MuOfEps.muOf_ne_zero (isEps_bk he)
  have hab : a * b = 1 := by
    have h3 : (a * b - 1) * mu e = 0 := by
      have : mu e = mu e * a * b := by rw [← ha]; exact hb
      linear_combination -this
    exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right hne)
  exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha.symm⟩

end GlobalTheory.EpsilonAssociated
