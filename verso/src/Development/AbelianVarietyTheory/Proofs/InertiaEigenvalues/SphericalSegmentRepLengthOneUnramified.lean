import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientUnramPrinSeriesOfHasSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsClassificationDetCharacterStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedCharOfCuspidalSphericalStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSphericalFactorOfSphericalSubquotientStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivOfSameSatakeParametersStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SphSeg

/- English proof (translation)
Take `rfl : x = fun a => IrrGL.ofChar (μ a) (hμ a)` from `funext hx`. Set `φ` to `multiProdEquiv (stdBlocks (fun a => (IrrGL.ofChar (μ a) (hμ a)).1) hd) fun a => (LocGL.equivRep (IrrRep.det (Fin 1) (μ a) (hμ a))).symm`. Conclude with `(IsSubquotient.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective).trans (PermPrin.isSubquotient_multiProd_prinSeries _ μ)`.
-/
theorem isSubquotient_prodIrr_prinSeries {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = h)
    (μ : Fin h → kˣ →* ℂˣ) (hμ : ∀ a, IsSmoothChar (μ a)) (hx : ∀ a, x a = IrrGL.ofChar (μ a) (hμ a)) :
    IsSubquotient (prodIrr x hd) (prinSeries μ) := by
  obtain rfl : x = fun a => IrrGL.ofChar (μ a) (hμ a) := funext hx
  let φ := multiProdEquiv (stdBlocks (fun a => (IrrGL.ofChar (μ a) (hμ a)).1) hd) fun a =>
    (LocGL.equivRep (IrrRep.det (Fin 1) (μ a) (hμ a))).symm
  exact (IsSubquotient.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective).trans
    (PermPrin.isSubquotient_multiProd_prinSeries _ μ)

end GlobalTheory.SphSeg

namespace GlobalTheory.SphSeg

/- English proof (translation)
Introduce `hLM hSC hZP hGL hBZ k _ _ _ _ _ Δ y hL hS`. Take `⟨N, c⟩` from `y`. Take `⟨hd, hc⟩` from `id hL`. Establish `hsub : IsSubquotient c.rep.ρ (prodIrr Δ.term hd)` using `hc.isSubquotient`. Establish `hsph` using `GlobalTheory.T.isSpherical_factor_of_spherical_subquotient k Δ.len N Δ.term hd _ c.rep.ρ hsub hS`.

Establish `h0 : Δ.term ⟨0, Δ.len_pos⟩ = Δ.first` using `by simp [Segment.term]`. Establish `key : ∀ x z : IrrGL k, x = z → IsSpherical x.rep → IsSpherical z.rep`. Introduce and unpack `_ _ rfl h`. Conclude with `h`. Establish `hU : Δ.first.IsUnramChar` using `GlobalTheory.T.isUnramifiedChar_of_cuspidal_spherical hGL hBZ hZP k Δ.first Δ.isCusp_first (key _ _ h0 (hsph _))`.

Use `⟨?_, hU⟩` and prove the remaining obligations. Take `⟨μ, hμ, hfirst⟩` from `hU`. Establish `hμs` using `isSmoothChar_of_isUnram hμ`. Establish `hterm : ∀ a, Δ.term a = IrrGL.ofChar (μ * absPow k ((a : ℕ) : ℂ)) (hμs.mul (isSmoothChar_absPow _))` using `fun a => by simp only [Segment.term, IrrGL.nu, hfirst, IrrGL.tw_ofChar]`. Establish `hd1 : Δ.d = 1` using `congrArg Sigma.fst hfirst`.

Establish `hN : N = Δ.len`. Establish `h2 : ∑ a, (Δ.term a).1 = N` using `hd`. Rewrite `h2` using `[Segment.sum_term_fst, Segment.deg, hd1, mul_one]`. Conclude with `h2.symm`. Substitute `hN` using the available equality.

Set `Γ` to `Segment.ofChar μ hμs Δ.len Δ.len_pos`. Establish `hterm' : ∀ a, Γ.term a = IrrGL.ofChar (μ * absPow k ((a : ℕ) : ℂ)) (hμs.mul (isSmoothChar_absPow _))` using `fun a => by show (IrrGL.ofChar μ hμs).nu _ = _`. Simplify using `only [IrrGL.nu, IrrGL.tw_ofChar]`. Establish `hd' : ∑ a, (Γ.term a).1 = Δ.len` using `(Segment.sum_term_fst _).trans (mul_one _)`. Establish `hP` using `isSubquotient_prodIrr_prinSeries Δ.term hd _ _ hterm`.

Establish `hP'` using `isSubquotient_prodIrr_prinSeries Γ.term hd' _ _ hterm'`. Set `χ'` to `μ * absPow k (((Δ.len : ℂ) - 1) / 2)`. Establish `hu' : IsUnram χ'` using `fun x hx => by`. Rewrite using `[MonoidHom.mul_apply, hμ x hx, isUnram_absPow k _ x hx, one_mul]`. Establish `hχs : IsSmoothChar χ'` using `isSmoothChar_of_isUnram hu'`.

Take `⟨f, hf⟩` from `embeds_detRep_segment hμs Δ.len_pos hd'`. Take `⟨ϖ, hϖ⟩` from `LocGL.exists_uniformizer k`. Establish `hu : ∀ i : Fin Δ.len, IsUnram (μ * absPow k ((i : ℕ) : ℂ))` using `fun i x hx => by`. Rewrite using `[MonoidHom.mul_apply, hμ x hx, isUnram_absPow k _ x hx, one_mul]`. Set `α : Fin Δ.len → ℂˣ` to `fun i => (μ * absPow k ((i : ℕ) : ℂ)) ϖ`.

Establish `heq : (fun i => unrChar k (α i)) = fun i : Fin Δ.len => μ * absPow k ((i : ℕ) : ℂ)`. Use function extensionality and compare the values at `fun i => (eq_unrChar (hu i) hϖ).symm`. Establish `hA : HasSatake c.rep.ρ α` using `⟨c.rep.irr, hS, by rw [heq]; exact hsub.trans hP⟩`. Establish `hB : HasSatake (IrrRep.det (Fin Δ.len) χ' hχs).ρ α` using `⟨(IrrRep.det (Fin Δ.len) χ' hχs).irr, isSpherical_detRep hu', by rw [heq]; exact (IsSubquotient.of_injective f hf).trans hP'⟩`. Take `⟨E⟩` from `GlobalTheory.T.nonempty_equiv_of_same_satakeParameters hBZ k Δ.len α c.rep (IrrRep.det (Fin Δ.len) χ' hχs) hA hB`.

Establish `hL2` using `(GlobalTheory.T.isLanglandsClassification_detCharacter hSC k Δ.len χ' hχs).of_equiv E.symm`. Establish `hL1` using `hL.isL`. Establish `hm` using `(hLM k).1 _ _ ⟨Δ.len, c⟩ hL1 hL2`. Use `congrArg Multiset.card hm` as an intermediate fact. Simplify using `using this.symm`.
-/
theorem len_eq_one_and_isUnramChar : LanglandsMultisegments → StandardCosocleGL → ZelevinskyPolynomialRing →
    GeometricLemma → BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [CharZero k] (Δ : Segment k) (y : IrrGL k), IsLSeg Δ y.rep → IsSpherical y.rep →
    Δ.len = 1 ∧ Δ.first.IsUnramChar := by
  intro hLM hSC hZP hGL hBZ k _ _ _ _ _ Δ y hL hS
  obtain ⟨N, c⟩ := y
  obtain ⟨hd, hc⟩ := id hL
  have hsub : IsSubquotient c.rep.ρ (prodIrr Δ.term hd) := hc.isSubquotient
  have hsph := GlobalTheory.T.isSpherical_factor_of_spherical_subquotient k Δ.len N Δ.term hd _ c.rep.ρ hsub hS
  have h0 : Δ.term ⟨0, Δ.len_pos⟩ = Δ.first := by simp [Segment.term]
  have key : ∀ x z : IrrGL k, x = z → IsSpherical x.rep → IsSpherical z.rep := by
    rintro _ _ rfl h; exact h
  have hU : Δ.first.IsUnramChar :=
    GlobalTheory.T.isUnramifiedChar_of_cuspidal_spherical hGL hBZ hZP k Δ.first Δ.isCusp_first (key _ _ h0 (hsph _))
  refine ⟨?_, hU⟩
  obtain ⟨μ, hμ, hfirst⟩ := hU
  have hμs := isSmoothChar_of_isUnram hμ
  have hterm : ∀ a, Δ.term a = IrrGL.ofChar (μ * absPow k ((a : ℕ) : ℂ)) (hμs.mul (isSmoothChar_absPow _)) :=
    fun a => by simp only [Segment.term, IrrGL.nu, hfirst, IrrGL.tw_ofChar]
  have hd1 : Δ.d = 1 := congrArg Sigma.fst hfirst
  have hN : N = Δ.len := by
    have h2 : ∑ a, (Δ.term a).1 = N := hd
    rw [Segment.sum_term_fst, Segment.deg, hd1, mul_one] at h2
    exact h2.symm
  subst hN

  let Γ := Segment.ofChar μ hμs Δ.len Δ.len_pos
  have hterm' : ∀ a, Γ.term a = IrrGL.ofChar (μ * absPow k ((a : ℕ) : ℂ)) (hμs.mul (isSmoothChar_absPow _)) :=
    fun a => by
      show (IrrGL.ofChar μ hμs).nu _ = _
      simp only [IrrGL.nu, IrrGL.tw_ofChar]
  have hd' : ∑ a, (Γ.term a).1 = Δ.len := (Segment.sum_term_fst _).trans (mul_one _)
  have hP := isSubquotient_prodIrr_prinSeries Δ.term hd _ _ hterm
  have hP' := isSubquotient_prodIrr_prinSeries Γ.term hd' _ _ hterm'
  let χ' := μ * absPow k (((Δ.len : ℂ) - 1) / 2)
  have hu' : IsUnram χ' := fun x hx => by
    rw [MonoidHom.mul_apply, hμ x hx, isUnram_absPow k _ x hx, one_mul]
  have hχs : IsSmoothChar χ' := isSmoothChar_of_isUnram hu'
  obtain ⟨f, hf⟩ := embeds_detRep_segment hμs Δ.len_pos hd'

  obtain ⟨ϖ, hϖ⟩ := LocGL.exists_uniformizer k
  have hu : ∀ i : Fin Δ.len, IsUnram (μ * absPow k ((i : ℕ) : ℂ)) := fun i x hx => by
    rw [MonoidHom.mul_apply, hμ x hx, isUnram_absPow k _ x hx, one_mul]
  let α : Fin Δ.len → ℂˣ := fun i => (μ * absPow k ((i : ℕ) : ℂ)) ϖ
  have heq : (fun i => unrChar k (α i)) = fun i : Fin Δ.len => μ * absPow k ((i : ℕ) : ℂ) :=
    funext fun i => (eq_unrChar (hu i) hϖ).symm
  have hA : HasSatake c.rep.ρ α := ⟨c.rep.irr, hS, by rw [heq]; exact hsub.trans hP⟩
  have hB : HasSatake (IrrRep.det (Fin Δ.len) χ' hχs).ρ α :=
    ⟨(IrrRep.det (Fin Δ.len) χ' hχs).irr, isSpherical_detRep hu',
      by rw [heq]; exact (IsSubquotient.of_injective f hf).trans hP'⟩
  obtain ⟨E⟩ := GlobalTheory.T.nonempty_equiv_of_same_satakeParameters hBZ k Δ.len α c.rep (IrrRep.det (Fin Δ.len) χ' hχs) hA hB
  have hL2 := (GlobalTheory.T.isLanglandsClassification_detCharacter hSC k Δ.len χ' hχs).of_equiv E.symm
  have hL1 := hL.isL
  have hm := (hLM k).1 _ _ ⟨Δ.len, c⟩ hL1 hL2
  have := congrArg Multiset.card hm
  simpa using this.symm

end GlobalTheory.SphSeg
