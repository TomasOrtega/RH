import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFundamentalDomainMassOneCocompactLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetIntegralFundamentalDomainEqMassMulAverageStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

/- English proof (translation)
Use `letI : MeasurableSpace G := borel G`. Use `haveI : BorelSpace G := ⟨rfl⟩`. Take `⟨μ, 𝓕, hμ, h𝓕, h1⟩` from `GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice G Γ hΓ`. Establish `hΨ : Per Γ (fun x => Φ (x + y))` using `⟨hΦ.1.comp (continuous_add_right y), fun γ hγ x => by simp only [add_assoc, hΦ.2 γ hγ]⟩`. Establish `hpres : MeasurePreserving (fun x : G => x - y) μ μ`.

Simplify `measurePreserving_add_right μ (-y)` using `[sub_eq_add_neg]`. Establish `h𝓕' : IsAddFundamentalDomain Γ ((fun x : G => x - y) ⁻¹' 𝓕) μ` using `h𝓕.preimage_of_equiv hpres.quasiMeasurePreserving (e := id) Function.bijective_id (fun γ x => by`. Simplify using `only [id, AddSubgroup.vadd_def, vadd_eq_add]`. Use the proof step `abel)`. Establish `hm' : μ ((fun x : G => x - y) ⁻¹' 𝓕) = 1`.

Rewrite using `[hpres.measure_preimage h𝓕.nullMeasurableSet, h1]`. Establish `hA` using `(GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average G Γ hΓ μ 𝓕 hμ h𝓕 _ hΨ).2.2.2`. Establish `hB` using `(GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average G Γ hΓ μ _ hμ h𝓕' Φ hΦ).2.2.2`. Rewrite `hA` using `[h1]`. Rewrite `hB` using `[hm']`.

Simplify using `only [ENNReal.toReal_one, Complex.ofReal_one, one_mul] at hA hB`. Rewrite using `[← hA, ← hB]`. Establish `hpres2 : MeasurePreserving (fun x : G => x + y) μ μ` using `measurePreserving_add_right μ y`. Establish `hemb : MeasurableEmbedding (fun x : G => x + y)` using `(MeasurableEquiv.addRight y).measurableEmbedding`. Use `hpres2.setIntegral_preimage_emb hemb Φ ((fun x : G => x - y) ⁻¹' 𝓕)` as an intermediate fact.

Rewrite using `[← this]`. Establish `hs : (fun x : G => x + y) ⁻¹' ((fun x : G => x - y) ⁻¹' 𝓕) = 𝓕`. Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite using `[hs]`.
-/
theorem avg_add_right (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] (Γ : AddSubgroup G) (hΓ : IsCoLat Γ) (Φ : G → ℂ) (hΦ : Per Γ Φ) (y : G) :
    avg Γ (fun x => Φ (x + y)) = avg Γ Φ := by
  letI : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice G Γ hΓ
  have hΨ : Per Γ (fun x => Φ (x + y)) :=
    ⟨hΦ.1.comp (continuous_add_right y), fun γ hγ x => by simp only [add_assoc, hΦ.2 γ hγ]⟩

  have hpres : MeasurePreserving (fun x : G => x - y) μ μ := by
    simpa [sub_eq_add_neg] using measurePreserving_add_right μ (-y)
  have h𝓕' : IsAddFundamentalDomain Γ ((fun x : G => x - y) ⁻¹' 𝓕) μ :=
    h𝓕.preimage_of_equiv hpres.quasiMeasurePreserving (e := id) Function.bijective_id (fun γ x => by
      simp only [id, AddSubgroup.vadd_def, vadd_eq_add]; abel)
  have hm' : μ ((fun x : G => x - y) ⁻¹' 𝓕) = 1 := by
    rw [hpres.measure_preimage h𝓕.nullMeasurableSet, h1]
  have hA := (GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average G Γ hΓ μ 𝓕 hμ h𝓕 _ hΨ).2.2.2
  have hB := (GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average G Γ hΓ μ _ hμ h𝓕' Φ hΦ).2.2.2
  rw [h1] at hA
  rw [hm'] at hB
  simp only [ENNReal.toReal_one, Complex.ofReal_one, one_mul] at hA hB
  rw [← hA, ← hB]
  have hpres2 : MeasurePreserving (fun x : G => x + y) μ μ := measurePreserving_add_right μ y
  have hemb : MeasurableEmbedding (fun x : G => x + y) := (MeasurableEquiv.addRight y).measurableEmbedding
  have := hpres2.setIntegral_preimage_emb hemb Φ ((fun x : G => x - y) ⁻¹' 𝓕)
  rw [← this]
  have hs : (fun x : G => x + y) ⁻¹' ((fun x : G => x - y) ⁻¹' 𝓕) = 𝓕 := by
    ext x; simp
  rw [hs]

end GlobalTheory.CuspGeneric
