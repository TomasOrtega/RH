import Formalism.DefsOC
import Formalism.ZetaNonvanishing.LandauLemma
import Formalism.ZetaNonvanishing.MellinDeriv

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

namespace LandauMellinIdentity

def Imel (H : ℝ → ℝ) (s : ℂ) : ℂ := ∫ x in Ioi (1:ℝ), (H x : ℂ) * (x : ℂ) ^ (-s - 1)

/- English proof (authored)
Embed the real integrand in the complex numbers, preserving almost-everywhere strong measurability. Its complex norm is the original real function on the integration interval because that function is nonnegative. Thus the assumed weighted integrability gives the norm integrability required by the Mellin differentiation theorem. That theorem gives complex differentiability throughout the half-plane.
-/
lemma imel_differentiableOn {H : ℝ → ℝ} {a : ℝ}
    (hH : AEStronglyMeasurable H (volume.restrict (Ioi 1)))
    (hpos : ∀ x : ℝ, 1 < x → 0 ≤ H x)
    (hint : ∀ σ : ℝ, a < σ → IntegrableOn (fun x : ℝ => H x * x ^ (-σ - 1)) (Ioi 1)) :
    DifferentiableOn ℂ (Imel H) {s : ℂ | a < s.re} := by
  intro s hs
  have hHc : AEStronglyMeasurable (fun x : ℝ => (H x : ℂ)) (volume.restrict (Ioi 1)) :=
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hH)
  have hnorm : ∀ σ : ℝ, a < σ →
      IntegrableOn (fun x : ℝ => ‖(H x : ℂ)‖ * x ^ (-σ - 1)) (Ioi 1) := by
    intro σ hσ
    refine (hint σ hσ).congr_fun (fun x hx => ?_) measurableSet_Ioi
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpos x hx)]
  exact (mellinDeriv (fun x => (H x : ℂ)) a hHc hnorm s hs).differentiableAt
    |>.differentiableWithinAt

end LandauMellinIdentity

open LandauMellinIdentity in
/- English proof (authored)
Landau's lemma extends integrability of the positive Mellin integrand to every real exponent above the lower bound. The Mellin differentiation theorem then makes its transform analytic on that half-plane. Consider the union of the original right half-plane and the real interval above the lower bound. Both parts are connected and meet at the real point one beyond the original boundary, so their union is connected. The proposed continuation is analytic near every point of the union by the two continuation hypotheses. It agrees with the Mellin transform near the common point by the original identity on the open right half-plane. The identity theorem extends this equality across the union, in particular to every real exponent in the larger interval.
-/
theorem landauEq : LandauEq := by
  intro H a b hab hH hpos hb Φ hΦ1 hΦ2 hΦeq
  have hint : ∀ σ : ℝ, a < σ → IntegrableOn (fun x : ℝ => H x * x ^ (-σ - 1)) (Ioi 1) :=
    landauLemma_of mellinDeriv H a b hab hH hpos hb Φ hΦ1 hΦ2 hΦeq
  intro σ hσ
  refine ⟨hint σ hσ, ?_⟩

  have hOpen : IsOpen {s : ℂ | a < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hIan : AnalyticOnNhd ℂ (Imel H) {s : ℂ | a < s.re} :=
    (imel_differentiableOn hH hpos hint).analyticOnNhd hOpen

  set A : Set ℂ := {s : ℂ | b < s.re} with hA
  set B : Set ℂ := (fun t : ℝ => (t : ℂ)) '' Ioi a with hB
  have hb1A : ((b + 1 : ℝ) : ℂ) ∈ A := by simp [hA]
  have hb1B : ((b + 1 : ℝ) : ℂ) ∈ B := ⟨b + 1, by simp; linarith, rfl⟩
  have hAconv : Convex ℝ A := convex_halfSpace_re_gt b
  have hApc : IsPreconnected A := hAconv.isPreconnected
  have hBpc : IsPreconnected B :=
    (isPreconnected_Ioi).image _ Complex.continuous_ofReal.continuousOn
  have hTpc : IsPreconnected (A ∪ B) := IsPreconnected.union _ hb1A hb1B hApc hBpc
  have hTsub : A ∪ B ⊆ {s : ℂ | a < s.re} := by
    rintro s (hs | ⟨t, ht, rfl⟩)
    · show a < s.re
      have : b < s.re := hs
      linarith
    · show a < ((t : ℂ)).re
      simpa using ht
  have hΦan : AnalyticOnNhd ℂ Φ (A ∪ B) := by
    rintro s (hs | ⟨t, ht, rfl⟩)
    · exact hΦ1 s hs
    · by_cases htb : t ≤ b
      · exact hΦ2 t ht htb
      · exact hΦ1 _ (by simpa using lt_of_not_ge htb)
  have hev : Φ =ᶠ[𝓝 ((b + 1 : ℝ) : ℂ)] Imel H := by
    have hAo : IsOpen A := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hAo.mem_nhds hb1A] with s hs
    exact hΦeq s hs
  have heq := hΦan.eqOn_of_preconnected_of_eventuallyEq (hIan.mono hTsub) hTpc
    (Or.inl hb1A) hev
  exact heq (Or.inr ⟨σ, hσ, rfl⟩)

end Formalism
