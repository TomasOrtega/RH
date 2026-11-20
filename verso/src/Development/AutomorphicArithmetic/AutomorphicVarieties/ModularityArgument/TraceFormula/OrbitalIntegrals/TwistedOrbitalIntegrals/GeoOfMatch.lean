import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.GeoTransport

open MeasureTheory NumberField IsDedekindDomain PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Z.Tf.Orb
open PositivityTheory.Rg.Tf.Geo (mapGL incFin galFin)
open scoped ENNReal

/- English proof (translation)
Introduce `hT hC hCC hI hQ hCl k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ hσ n _ _ _ _ μE μk hE hk φ hφ f hf hM γ hγ ν hν`. Take `⟨a1, a2, a3, -⟩` from `hT E n`. Take `⟨b1, b2, b3, -⟩` from `hT k n`. Establish `hσc : Continuous (sigmaGL σ : GL (Fin n) E → GL (Fin n) E)` using `((hC k E).2.2 n).2 σ`. Use `⟨fun δ hδ => ?_, fun hn => ?_⟩` and prove the remaining obligations.

Establish `hδ' : normGL σ δ = incl γ` using `hδ`. Take `⟨hreg, hS⟩` from `hI k E σ hσ n δ γ hγ hδ'`. Establish `hcl : IsClosed ((Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k))`. Establish `: ((Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) = {x | x * γ = γ * x}`. Use extensionality with `x`.

Simplify using `[Subgroup.mem_centralizer_singleton_iff]`. Rewrite using `[this]`. Conclude with `isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)`. Establish `hcm : ∀ a ∈ (Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)), ∀ b ∈ (Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)), Commute a b` using `fun a ha b hb => by`. Rewrite `ha`, `hb` using `[Subgroup.mem_centralizer_singleton_iff]`.

Conclude with `Units.ext (hCC k n γ a b hγ (congrArg Units.val ha) (congrArg Units.val hb))`. Take `⟨μ, hμ, hmap, hq⟩` from `hQ _ _ incl (hCl k E n) μE hE _ _ hcl hcm hS ν hν`. Establish `h1` using `hM.1 δ γ 1 μ ν hreg (by simpa using hδ') hμ hν (by simpa using hmap)`. Establish `hcont : Continuous fun g => φ (twConj (sigmaGL σ) g δ)` using `hφ.1.continuous.comp ((continuous_inv.mul continuous_const).mul hσc)`. Establish `h2` using `hq _ hcont.measurable fun s hs g => by rw [twConj_mul_left _ _ hs]`.

Rewrite using `[one_mul]`. Conclude with `h2.trans h1`. Use `hM.2 γ ν hγ (fun ⟨δ, h, hh⟩ => hn ⟨twConj (sigmaGL σ) h δ, ?_⟩) hν` and prove the remaining obligations. Establish `hl : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1`. Rewrite using `[← sigmaGL_pow, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one', sigmaGL_one]`.

Use `twNorm_twConj_of_pow_eq_one _ hl h δ` as an intermediate fact. Establish `hh' : twNorm (sigmaGL σ) (Module.finrank k E) δ = h * incl γ * h⁻¹` using `hh`. Rewrite `this` using `[hh']`. Use `this.trans ?_` and prove the remaining obligations. Use `show h⁻¹ * (h * incl γ * h⁻¹) * h = incl γ`.

Use `group`.
-/
theorem UpperTheory.V.Z.Tf.Orb.geoOfMatch :
    UpperTheory.V.Z.Tf.Orb.GLTop → UpperTheory.V.Z.Tf.Orb.ExtCont → UpperTheory.V.Z.Tf.Orb.CentComm → UpperTheory.V.Z.Tf.Orb.TwCentImg → UpperTheory.V.Z.Tf.Orb.QuotAlong → UpperTheory.V.Z.Tf.Orb.InclClosed → UpperTheory.V.Z.Tf.Orb.GeoOfMatch := by
  intro hT hC hCC hI hQ hCl k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ hσ n _ _ _ _ μE μk hE hk φ hφ f hf hM γ hγ ν hν
  obtain ⟨a1, a2, a3, -⟩ := hT E n
  obtain ⟨b1, b2, b3, -⟩ := hT k n
  have hσc : Continuous (sigmaGL σ : GL (Fin n) E → GL (Fin n) E) := ((hC k E).2.2 n).2 σ
  refine ⟨fun δ hδ => ?_, fun hn => ?_⟩
  · have hδ' : normGL σ δ = incl γ := hδ
    obtain ⟨hreg, hS⟩ := hI k E σ hσ n δ γ hγ hδ'
    have hcl : IsClosed ((Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) := by
      have : ((Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) = {x | x * γ = γ * x} := by
        ext x; simp [Subgroup.mem_centralizer_singleton_iff]
      rw [this]
      exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
    have hcm : ∀ a ∈ (Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)), ∀ b ∈ (Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)),
        Commute a b := fun a ha b hb => by
      rw [Subgroup.mem_centralizer_singleton_iff] at ha hb
      exact Units.ext (hCC k n γ a b hγ (congrArg Units.val ha) (congrArg Units.val hb))
    obtain ⟨μ, hμ, hmap, hq⟩ := hQ _ _ incl (hCl k E n) μE hE _ _ hcl hcm hS ν hν
    have h1 := hM.1 δ γ 1 μ ν hreg (by simpa using hδ') hμ hν (by simpa using hmap)
    have hcont : Continuous fun g => φ (twConj (sigmaGL σ) g δ) :=
      hφ.1.continuous.comp ((continuous_inv.mul continuous_const).mul hσc)
    have h2 := hq _ hcont.measurable fun s hs g => by rw [twConj_mul_left _ _ hs]
    rw [one_mul]
    exact h2.trans h1
  · refine hM.2 γ ν hγ (fun ⟨δ, h, hh⟩ => hn ⟨twConj (sigmaGL σ) h δ, ?_⟩) hν
    have hl : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1 := by
      rw [← sigmaGL_pow, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one', sigmaGL_one]
    have := twNorm_twConj_of_pow_eq_one _ hl h δ
    have hh' : twNorm (sigmaGL σ) (Module.finrank k E) δ = h * incl γ * h⁻¹ := hh
    rw [hh'] at this
    refine this.trans ?_
    show h⁻¹ * (h * incl γ * h⁻¹) * h = incl γ
    group
