import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DetNeOfTotPos
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensAtGoodOf

noncomputable section

open NumberField Module Formalism.MainNotions.S
open Classical

namespace Formalism.L2.SG.Pf.Cnt.R1

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `φ`. Unfold `Formalism.BasicNotions.Host.emb Formalism.BasicNotions.Host.sigmaOf`. Establish `key : ∃ σ : D.host.E ≃ₐ[ℚ] D.host.E, D.host.φ₀.comp (σ : D.host.E →+* D.host.E) = φ` using `by classical`. Set `f : (D.host.E ≃ₐ[ℚ] D.host.E) → (D.host.E →ₐ[ℚ] ℂ)` to `fun σ => (D.host.φ₀.toRatAlgHom).comp (σ : D.host.E →ₐ[ℚ] D.host.E)`. Establish `hinj : Function.Injective f`.

Introduce `σ τ h`. Use extensionality with `x`. Establish `h1 : D.host.φ₀ (σ x) = D.host.φ₀ (τ x)` using `congrArg (fun g : D.host.E →ₐ[ℚ] ℂ => g x) h`. Conclude with `D.host.φ₀.injective h1`. Establish `hcard : Fintype.card (D.host.E ≃ₐ[ℚ] D.host.E) = Fintype.card (D.host.E →ₐ[ℚ] ℂ)` using `by haveI : IsGalois ℚ D.host.E := inferInstance`.

Rewrite using `[AlgHom.card ℚ D.host.E ℂ, ← IsGalois.card_aut_eq_finrank ℚ D.host.E, Fintype.card_eq_nat_card]`. Take `⟨σ, hσ⟩` from `((Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩).2 φ.toRatAlgHom`. Use `⟨σ, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Establish `h2 : D.host.φ₀ (σ x) = φ x` using `congrArg (fun g : D.host.E →ₐ[ℚ] ℂ => g x) hσ`.

Conclude with `h2`. Take `⟨σ, hσ⟩` from `key`. Use `⟨D.host.gal σ, ?_⟩` and prove the remaining obligations. Simplify using `only [Equiv.symm_apply_apply, MulEquiv.symm_apply_apply]`. Conclude with `hσ`.
-/
theorem emb_surj (D : Formalism.BasicNotions.D7) : Function.Surjective D.host.emb := by
  intro φ
  unfold Formalism.BasicNotions.Host.emb Formalism.BasicNotions.Host.sigmaOf

  have key : ∃ σ : D.host.E ≃ₐ[ℚ] D.host.E, D.host.φ₀.comp (σ : D.host.E →+* D.host.E) = φ := by
    classical
    let f : (D.host.E ≃ₐ[ℚ] D.host.E) → (D.host.E →ₐ[ℚ] ℂ) :=
      fun σ => (D.host.φ₀.toRatAlgHom).comp (σ : D.host.E →ₐ[ℚ] D.host.E)
    have hinj : Function.Injective f := by
      intro σ τ h
      ext x
      have h1 : D.host.φ₀ (σ x) = D.host.φ₀ (τ x) := congrArg (fun g : D.host.E →ₐ[ℚ] ℂ => g x) h
      exact D.host.φ₀.injective h1
    have hcard : Fintype.card (D.host.E ≃ₐ[ℚ] D.host.E) = Fintype.card (D.host.E →ₐ[ℚ] ℂ) := by
      haveI : IsGalois ℚ D.host.E := inferInstance
      rw [AlgHom.card ℚ D.host.E ℂ, ← IsGalois.card_aut_eq_finrank ℚ D.host.E, Fintype.card_eq_nat_card]
    obtain ⟨σ, hσ⟩ := ((Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩).2 φ.toRatAlgHom
    refine ⟨σ, ?_⟩
    ext x
    have h2 : D.host.φ₀ (σ x) = φ x := congrArg (fun g : D.host.E →ₐ[ℚ] ℂ => g x) hσ
    exact h2
  obtain ⟨σ, hσ⟩ := key
  refine ⟨D.host.gal σ, ?_⟩
  simp only [Equiv.symm_apply_apply, MulEquiv.symm_apply_apply]
  exact hσ

/- English proof (translation)
Introduce `D x hx hpos φ`. Take `⟨g, rfl⟩` from `emb_surj D φ`. Distinguish the cases in `hg : g ∈ D.R.Psi`. Establish `h1` using `hpos (D.eTau.symm ⟨g, hg⟩)`. Simplify using `using h1`.

Establish `hmem : g * D.R.cc ∈ D.R.Psi`. Rewrite `hg`, the goal using `[Formalism.HC.Frame.mem_Psi_iff]`. Establish `h2 : g.1.2 = -1` using `(Int.units_eq_one_or _).resolve_left hg`. Rewrite using `[Prod.fst_mul, Prod.snd_mul, h2]`. Use `first`.

Consider the case `rfl`. Consider the case `decide`. Consider the case `(simp [Formalism.HC.Frame.cc]; done)`. Consider the case `(simp [Formalism.HC.Frame.cc, Formalism.HC.c0])`. Establish `h1` using `hpos (D.eTau.symm ⟨g * D.R.cc, hmem⟩)`.

Simplify using `only [Equiv.apply_symm_apply] at h1`. Establish `hc : D.host.conj x = x` using `(Formalism.MainNotions.S.Inh.tie_star D x).symm.trans hx`. Establish `he : D.host.emb (g * D.R.cc) x = D.host.emb g x`. Express the relevant statement in the definitionally equal form `D.host.φ₀ ((D.host.gal.symm (g * D.R.cc)) x) = D.host.φ₀ ((D.host.gal.symm g) x)`. Rewrite using `[map_mul, AlgEquiv.mul_apply]`.

Use `congr 2`. Rewrite `h1` using `[he]`. Conclude with `h1`.
-/
theorem totally_positive_all : TotPosAll := by
  intro D x hx hpos φ
  obtain ⟨g, rfl⟩ := emb_surj D φ
  by_cases hg : g ∈ D.R.Psi
  · have h1 := hpos (D.eTau.symm ⟨g, hg⟩)
    simpa using h1
  · have hmem : g * D.R.cc ∈ D.R.Psi := by
      rw [Formalism.HC.Frame.mem_Psi_iff] at hg ⊢
      have h2 : g.1.2 = -1 := (Int.units_eq_one_or _).resolve_left hg
      rw [Prod.fst_mul, Prod.snd_mul, h2]
      first
        | rfl
        | decide
        | (simp [Formalism.HC.Frame.cc]; done)
        | (simp [Formalism.HC.Frame.cc, Formalism.HC.c0])
    have h1 := hpos (D.eTau.symm ⟨g * D.R.cc, hmem⟩)
    simp only [Equiv.apply_symm_apply] at h1
    have hc : D.host.conj x = x := (Formalism.MainNotions.S.Inh.tie_star D x).symm.trans hx
    have he : D.host.emb (g * D.R.cc) x = D.host.emb g x := by
      change D.host.φ₀ ((D.host.gal.symm (g * D.R.cc)) x) = D.host.φ₀ ((D.host.gal.symm g) x)
      rw [map_mul, AlgEquiv.mul_apply]
      congr 2
    rw [he] at h1
    exact h1

end Formalism.L2.SG.Pf.Cnt.R1

namespace Formalism.L2.SG.Pf.Cnt

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

/- English proof (translation)
The claim follows from `ratPair_of R1.totally_positive_all`.
-/
theorem rational_pair_holds : RatPair := ratPair_of R1.totally_positive_all

end Formalism.L2.SG.Pf.Cnt
