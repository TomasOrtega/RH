import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.FlathTensorProduct
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnitaryIrreducibleAdmissible
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitarySatakeTransformStarParameterEqOfUnitarisa
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Heckecomm
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Filter GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.AutMult
open GlobalTheory.PRep (IsAdmissible fixed)

noncomputable section
namespace GlobalTheory.AntiInvLoc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `hfin` using `(Ideal.finite_factors (differentIdeal_ne_bot (A := 𝓞 F) (B := 𝓞 E))).image (fun P : HeightOneSpectrum (𝓞 E) => P.under (𝓞 F))`. Use `Filter.eventually_cofinite.2 (hfin.subset fun v hv => ?_)` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq] at hv`. Rewrite `hv` using `[GlobalTheory.LFun.isUnram_iff]`. Use `push_neg at hv`.

Take `⟨P, hP, h1⟩` from `hv`. Use `⟨P, ?_, hP⟩` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq]`. Assume the negation of the conclusion as `hnd`. Use `haveI := not_dvd_differentIdeal_iff.1 hnd`.

Conclude with `h1 Ideal.ramificationIdx_eq_one_of_isUnramifiedAt`.
-/
theorem eventually_isUnram : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v := by
  have hfin := (Ideal.finite_factors (differentIdeal_ne_bot (A := 𝓞 F) (B := 𝓞 E))).image
    (fun P : HeightOneSpectrum (𝓞 E) => P.under (𝓞 F))
  refine Filter.eventually_cofinite.2 (hfin.subset fun v hv => ?_)
  simp only [Set.mem_setOf_eq] at hv
  rw [GlobalTheory.LFun.isUnram_iff] at hv
  push_neg at hv
  obtain ⟨P, hP, h1⟩ := hv
  refine ⟨P, ?_, hP⟩
  simp only [Set.mem_setOf_eq]
  by_contra hnd
  haveI := not_dvd_differentIdeal_iff.1 hnd
  exact h1 Ideal.ramificationIdx_eq_one_of_isUnramifiedAt

variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
  {v : HeightOneSpectrum (𝓞 F)}

/- English proof (translation)
Take `⟨w, -, -, hw, -⟩` from `id hv`. Establish `h : w.under (𝓞 F) = v` using `HeightOneSpectrum.ext hw`. Take `⟨e, ⟨-, he⟩, -⟩` from `GlobalTheory.LFun.SplitChart.exists_isSplitChart hc hJ hL.fg hL.span_eq_top h hv hd`. Use `⟨fun g => e.symm (Formalism.UG.P.heckecomm_tr (e g)), fun x y => ?_, fun x => ?_, fun g => ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul, Formalism.UG.P.heckecomm_tr_mul]`.

Simplify using `only [MulEquiv.apply_symm_apply, Formalism.UG.P.heckecomm_tr_tr, MulEquiv.symm_apply_apply]`. Take `⟨a, b, hab⟩` from `Formalism.UG.P.heckecomm_tr_dc Formalism.UG.P.cartan_decomposition_holds E w n (e g)`. Use `⟨e.symm a, (he _).2 (by simpa using a.2), e.symm b, (he _).2 (by simpa using b.2), ?_⟩` and prove the remaining obligations. Use `show e.symm _ = _`. Rewrite using `[hab]`.

Apply `e.injective` to reduce the goal to its premises. Simplify using the standard rewrite rules.
-/
theorem exists_antiInv_split (hc : IsCMExt F E σ) (hJ : IsHermND σ J) (hL : Submodule.IsLattice E L)
    (hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v) (hd : IsSelfDualAt σ J L v) :
    ∃ θ : GLoc σ J v → GLoc σ J v, (∀ x y, θ (x * y) = θ y * θ x) ∧ (∀ x, θ (θ x) = x) ∧
      ∀ g, ∃ a ∈ stabLoc σ J L v, ∃ b ∈ stabLoc σ J L v, θ g = a * g * b := by
  obtain ⟨w, -, -, hw, -⟩ := id hv
  have h : w.under (𝓞 F) = v := HeightOneSpectrum.ext hw
  obtain ⟨e, ⟨-, he⟩, -⟩ := GlobalTheory.LFun.SplitChart.exists_isSplitChart hc hJ hL.fg hL.span_eq_top h hv hd
  refine ⟨fun g => e.symm (Formalism.UG.P.heckecomm_tr (e g)), fun x y => ?_, fun x => ?_, fun g => ?_⟩
  · simp only [map_mul, Formalism.UG.P.heckecomm_tr_mul]
  · simp only [MulEquiv.apply_symm_apply, Formalism.UG.P.heckecomm_tr_tr, MulEquiv.symm_apply_apply]
  · obtain ⟨a, b, hab⟩ := Formalism.UG.P.heckecomm_tr_dc Formalism.UG.P.cartan_decomposition_holds E w n (e g)
    refine ⟨e.symm a, (he _).2 (by simpa using a.2), e.symm b, (he _).2 (by simpa using b.2), ?_⟩
    show e.symm _ = _
    rw [hab]
    apply e.injective
    simp

/- English proof (translation)
Establish `h : w.under (𝓞 F) = v` using `(GlobalTheory.LFun.InertChart.under_eq_iff hw w).2 rfl`. Take `⟨-, ⟨c, hc', -⟩, -, -, hrest⟩` from `(GlobalTheory.LFun.exists_isInertChart σ hc v).2 w h hw`. Take `⟨⟨ϖ, hU⟩, hch⟩` from `hrest c hc'`. Take `⟨e, ⟨-, -, he⟩, -⟩` from `hch n J L hJ hL.fg hL.span_eq_top hd`. Use `⟨fun g => g⁻¹, mul_inv_rev, inv_inv, fun g => ?_⟩` and prove the remaining obligations.

Take `⟨k₁, hk₁, k₂, hk₂, hk⟩` from `GlobalTheory.LFun.ConjParam.inv_mem hU (e g)`. Use `⟨e.symm k₁, (he _).2 (by simpa using hk₁), e.symm k₂, (he _).2 (by simpa using hk₂), ?_⟩` and prove the remaining obligations. Apply `e.injective` to reduce the goal to its premises. Simplify using `[hk]`.
-/
theorem exists_antiInv_inert (hc : IsCMExt F E σ) (hJ : IsHermND σ J) (hL : Submodule.IsLattice E L)
    {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) (hd : IsSelfDualAt σ J L v) :
    ∃ θ : GLoc σ J v → GLoc σ J v, (∀ x y, θ (x * y) = θ y * θ x) ∧ (∀ x, θ (θ x) = x) ∧
      ∀ g, ∃ a ∈ stabLoc σ J L v, ∃ b ∈ stabLoc σ J L v, θ g = a * g * b := by
  have h : w.under (𝓞 F) = v := (GlobalTheory.LFun.InertChart.under_eq_iff hw w).2 rfl
  obtain ⟨-, ⟨c, hc', -⟩, -, -, hrest⟩ := (GlobalTheory.LFun.exists_isInertChart σ hc v).2 w h hw
  obtain ⟨⟨ϖ, hU⟩, hch⟩ := hrest c hc'
  obtain ⟨e, ⟨-, -, he⟩, -⟩ := hch n J L hJ hL.fg hL.span_eq_top hd
  refine ⟨fun g => g⁻¹, mul_inv_rev, inv_inv, fun g => ?_⟩
  obtain ⟨k₁, hk₁, k₂, hk₂, hk⟩ := GlobalTheory.LFun.ConjParam.inv_mem hU (e g)
  refine ⟨e.symm k₁, (he _).2 (by simpa using hk₁), e.symm k₂, (he _).2 (by simpa using hk₂), ?_⟩
  apply e.injective
  simp [hk]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hc n J hJ L hL`. Use `filter_upwards [eventually_isUnram (F := F) (E := E), GlobalTheory.AdelicU.SelfDual.eventually_isSelfDualAt (σ := σ) hJ.2 hL] with v hu hd`. Break down `(GlobalTheory.LFun.exists_isInertChart σ hc v).1 hu with hs | ⟨w, hw⟩` into its components or cases. Conclude with `exists_antiInv_split hc hJ hL hs hd`. Conclude with `exists_antiInv_inert hc hJ hL hw hd`.
-/
theorem eventually_exists_antiInv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L → ∀ᶠ v in cofinite, ∃ θ : GLoc σ J v → GLoc σ J v, (∀ x y, θ (x * y) = θ y * θ x) ∧ (∀ x, θ (θ x) = x) ∧ ∀ g, ∃ a ∈ stabLoc σ J L v, ∃ b ∈ stabLoc σ J L v, θ g = a * g * b := by
  intro F E _ _ _ _ _ σ hc n J hJ L hL
  filter_upwards [eventually_isUnram (F := F) (E := E), GlobalTheory.AdelicU.SelfDual.eventually_isSelfDualAt (σ := σ) hJ.2 hL] with v hu hd
  rcases (GlobalTheory.LFun.exists_isInertChart σ hc v).1 hu with hs | ⟨w, hw⟩
  · exact exists_antiInv_split hc hJ hL hs hd
  · exact exists_antiInv_inert hc hJ hL hw hd

end GlobalTheory.AntiInvLoc
