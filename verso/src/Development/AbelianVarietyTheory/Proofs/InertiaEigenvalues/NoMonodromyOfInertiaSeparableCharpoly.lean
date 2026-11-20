import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAttachedHodge

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.TripleLocal GlobalTheory.TypeLeaf

namespace GlobalTheory.WeilDeligne

/- English proof (translation)
Take `⟨k, hk⟩` from `hN`. Establish `hline : ∀ μ : ℂ, ∀ v ∈ f.maxGenEigenspace μ, N v = 0`. Introduce `μ`. Establish `hdim : Module.finrank ℂ (f.maxGenEigenspace μ) ≤ 1`. Rewrite using `[LinearMap.finrank_maxGenEigenspace_eq]`.

Conclude with `Polynomial.rootMultiplicity_le_one_of_separable hf μ`. Take `⟨v₀, hv₀⟩` from `finrank_le_one_iff.mp hdim`. Establish `hgen : ∀ v ∈ f.maxGenEigenspace μ, ∃ c : ℂ, v = c • (v₀ : V)`. Introduce `v hv`. Take `⟨c, hcv⟩` from `hv₀ ⟨v, hv⟩`.

Conclude with `⟨c, (congrArg Subtype.val hcv).symm⟩`. Take `⟨c, hNv⟩` from `hgen _ (Module.End.mapsTo_maxGenEigenspace_of_comm hc μ v₀.2)`. Establish `hpow : ∀ m : ℕ, (N ^ m) (v₀ : V) = c ^ m • (v₀ : V)`. Introduce `m`. Proceed by induction on `m with`.

Consider the case `zero => simp`. Consider the case `succ m ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hNv, smul_smul, ← pow_succ]`. Establish `h0 : N (v₀ : V) = 0`. Establish `hz` using `hpow k`. Rewrite `hz` using `[hk, LinearMap.zero_apply]`.

Break down `smul_eq_zero.mp hz.symm with h | h` into its components or cases. Rewrite using `[hNv, (pow_eq_zero_iff'.mp h).1, zero_smul]`. Rewrite using `[h, map_zero]`. Introduce `v hv`. Take `⟨a, rfl⟩` from `hgen v hv`.

Rewrite using `[map_smul, h0, smul_zero]`. Use extensionality with `v`. Establish `hv : v ∈ ⨆ μ, f.maxGenEigenspace μ`. Rewrite using `[Module.End.iSup_maxGenEigenspace_eq_top]`. Discharge the goal by the elementary cases of `trivial`.

Conclude with `Submodule.iSup_induction _ (motive := fun v => N v = 0) hv hline (map_zero N) (fun x y hx hy => by rw [map_add, hx, hy, add_zero])`.
-/
theorem eq_zero_of_commute_of_separable {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] {f N : Module.End ℂ V} (hf : f.charpoly.Separable)
    (hc : Commute f N) (hN : IsNilpotent N) : N = 0 := by
  obtain ⟨k, hk⟩ := hN

  have hline : ∀ μ : ℂ, ∀ v ∈ f.maxGenEigenspace μ, N v = 0 := by
    intro μ
    have hdim : Module.finrank ℂ (f.maxGenEigenspace μ) ≤ 1 := by
      rw [LinearMap.finrank_maxGenEigenspace_eq]
      exact Polynomial.rootMultiplicity_le_one_of_separable hf μ
    obtain ⟨v₀, hv₀⟩ := finrank_le_one_iff.mp hdim
    have hgen : ∀ v ∈ f.maxGenEigenspace μ, ∃ c : ℂ, v = c • (v₀ : V) := by
      intro v hv
      obtain ⟨c, hcv⟩ := hv₀ ⟨v, hv⟩
      exact ⟨c, (congrArg Subtype.val hcv).symm⟩
    obtain ⟨c, hNv⟩ := hgen _ (Module.End.mapsTo_maxGenEigenspace_of_comm hc μ v₀.2)
    have hpow : ∀ m : ℕ, (N ^ m) (v₀ : V) = c ^ m • (v₀ : V) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hNv, smul_smul, ← pow_succ]
    have h0 : N (v₀ : V) = 0 := by
      have hz := hpow k
      rw [hk, LinearMap.zero_apply] at hz
      rcases smul_eq_zero.mp hz.symm with h | h
      · rw [hNv, (pow_eq_zero_iff'.mp h).1, zero_smul]
      · rw [h, map_zero]
    intro v hv
    obtain ⟨a, rfl⟩ := hgen v hv
    rw [map_smul, h0, smul_zero]
  ext v
  have hv : v ∈ ⨆ μ, f.maxGenEigenspace μ := by
    rw [Module.End.iSup_maxGenEigenspace_eq_top]; trivial
  exact Submodule.iSup_induction _ (motive := fun v => N v = 0) hv hline (map_zero N)
    (fun x y hx hy => by rw [map_add, hx, hy, add_zero])

end GlobalTheory.WeilDeligne

/- English proof (translation)
Introduce `σ hσ`. Proceed by induction on `x using Quotient.inductionOn with`. Consider the case `h a`. Take `⟨n, a⟩` from `a`. Establish `hw : σ ∈ Weil h` using `Ine_le_Weil h hσ`.

Establish `hcomm : Commute (a.ρ ⟨σ, hw⟩) a.N`. Establish `hc` using `a.comm ⟨σ, hw⟩`. Rewrite `hc` using `[deg_eq_zero_iff.mpr hσ, zpow_zero, one_smul]`. Conclude with `hc`. Simplify using `only [WD.mono0, WD.inePol, WD.charPol, dif_pos hw, Quotient.lift_mk, WDRep.Mono0]`.

Introduce `hs`. Conclude with `eq_zero_of_commute_of_separable hs hcomm a.nilpotent`.
-/
theorem GlobalTheory.WeilDeligne.WD.noMonodromy_of_inertia_separable_charpoly (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : GlobalTheory.WeilDeligne.WD h) :
    ∀ σ ∈ Ine (F := E) A, (x.inePol σ).Separable → x.mono0 := by
  intro σ hσ
  induction x using Quotient.inductionOn with
  | h a =>
    obtain ⟨n, a⟩ := a
    have hw : σ ∈ Weil h := Ine_le_Weil h hσ

    have hcomm : Commute (a.ρ ⟨σ, hw⟩) a.N := by
      have hc := a.comm ⟨σ, hw⟩
      rw [deg_eq_zero_iff.mpr hσ, zpow_zero, one_smul] at hc
      exact hc
    simp only [WD.mono0, WD.inePol, WD.charPol, dif_pos hw, Quotient.lift_mk, WDRep.Mono0]
    intro hs
    exact eq_zero_of_commute_of_separable hs hcomm a.nilpotent
