import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.CasselmanSuffTemp
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.TotallyDisjointProductIrreducibleOfPolynomialRin
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LanglandsClassificationCuspidalSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.MNolow
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.MCellone
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.MDetjac
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.ExistsComplOfAdmissible

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

/- English proof (translation)
Introduce `hG hB hZ k _ _ _ _ r t V _ _ σ χ hrt hs hi hu hχs hχu`. Establish `hds : IsSmooth (detRep (Fin t) χ)` using `(isSmooth_ofChar_iff _).2 (IsSmoothChar.detChar hχs)`. Establish `hdi : (detRep (Fin t) χ).IsIrreducible` using `isIrreducible_ofChar _`. Establish `hdu : IsUnitarisable (detRep (Fin t) χ)` using `(isUnitarisable_ofChar_iff _).2 (fun g => hχu _)`. Use `set x := IrrGL.of σ hs hi with hx`.

Use `set y := IrrGL.of (detRep (Fin t) χ) hds hdi with hy`. Establish `hd : ∑ a, (![x, y] a).fst = r + t` using `by simp [hx, hy, IrrGL.of]`. Take `⟨e⟩` from `nonempty_prod₂_equiv_prodIrr σ hs hi (detRep (Fin t) χ) hds hdi hd`. Use `GlobalTheory.Parabolic.isIrreducible_of_equiv e.symm ?_` and prove the remaining obligations. Establish `hxu : IsUnitarisable x.rep` using `GlobalTheory.GenericUnitary.isUnitarisable_of_equiv (IrrGL.equivOf σ hs hi) hu`.

Establish `hyu : IsUnitarisable y.rep` using `GlobalTheory.GenericUnitary.isUnitarisable_of_equiv (IrrGL.equivOf (detRep (Fin t) χ) hds hdi) hdu`. Use `UpperTheory.Lit.Mix.ss hB k x y (r + t) hd hxu hyu ?_` and prove the remaining obligations. Use `UpperTheory.Lit.Mix.cellone hG hB k x y (r + t) hd ?_` and prove the remaining obligations. Introduce `q hq hq0 hjm p hc`. Establish `hqt : ∑ a, (q a).fst = t` using `hq`.

Establish `hjm' : jm q hqt (detRep (Fin t) χ) ≠ 0`. Establish `h1` using `(jhMult_ne_zero_iff).1 hjm`. Establish `hsub : IsSubquotient y.rep (detRep (Fin t) χ)`. Establish `f` using `(IrrGL.equivOf (detRep (Fin t) χ) hds hdi)`. Conclude with `IsSubquotient.of_surjective f.toIntertwiningMap (fun w => ⟨f.invFun w, f.right_inv w⟩)`.

Conclude with `(jhMult_ne_zero_iff).2 (IsSubquotient.trans h1 (GlobalTheory.JacquetExact.isSubquotient_jac _ hds hsub))`. Take `⟨A, hA, hnu⟩` from `UpperTheory.Lit.Mix.detjac k t χ hχs q hqt hq0 hjm'`. Assume the negation of the conclusion as `hne`. Establish `hsq` using `(jhMult_ne_zero_iff).1 hne`. Take `⟨s, hsp⟩` from `GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_hasSupport hB hG p`.

Apply the tactic sequence `have hsup := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (t := ![s, A]) (fun a => by fin_cases a <;> simpa) x.snd.rep.irr hsq`. Establish `hmem : (IrrGL.ofChar χ hχs).nu (-(↑t - 1) / 2) ∈ ∑ a, (![s, A] : Fin 2 → _) a`. Rewrite using `[Fin.sum_univ_two]`. Conclude with `Multiset.mem_add.2 (Or.inr hnu)`. Conclude with `UpperTheory.Lit.Mix.nolow hG hB hZ k r t _ x.rep _ χ hχs hrt hsup hxu hχu hmem`.
-/
theorem UpperTheory.Lit.Mix.top :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin r) k) V) (χ : kˣ →* ℂˣ), r < t → IsSmooth σ → σ.IsIrreducible → IsUnitarisable σ → IsSmoothChar χ → IsUnitaryChar χ → (prod₂ σ (detRep (Fin t) χ)).IsIrreducible := by
  intro hG hB hZ k _ _ _ _ r t V _ _ σ χ hrt hs hi hu hχs hχu
  have hds : IsSmooth (detRep (Fin t) χ) :=
    (isSmooth_ofChar_iff _).2 (IsSmoothChar.detChar hχs)
  have hdi : (detRep (Fin t) χ).IsIrreducible := isIrreducible_ofChar _
  have hdu : IsUnitarisable (detRep (Fin t) χ) :=
    (isUnitarisable_ofChar_iff _).2 (fun g => hχu _)
  set x := IrrGL.of σ hs hi with hx
  set y := IrrGL.of (detRep (Fin t) χ) hds hdi with hy
  have hd : ∑ a, (![x, y] a).fst = r + t := by simp [hx, hy, IrrGL.of]
  obtain ⟨e⟩ := nonempty_prod₂_equiv_prodIrr σ hs hi (detRep (Fin t) χ) hds hdi hd
  refine GlobalTheory.Parabolic.isIrreducible_of_equiv e.symm ?_
  have hxu : IsUnitarisable x.rep := GlobalTheory.GenericUnitary.isUnitarisable_of_equiv (IrrGL.equivOf σ hs hi) hu
  have hyu : IsUnitarisable y.rep :=
    GlobalTheory.GenericUnitary.isUnitarisable_of_equiv (IrrGL.equivOf (detRep (Fin t) χ) hds hdi) hdu
  refine UpperTheory.Lit.Mix.ss hB k x y (r + t) hd hxu hyu ?_
  refine UpperTheory.Lit.Mix.cellone hG hB k x y (r + t) hd ?_
  intro q hq hq0 hjm p hc
  have hqt : ∑ a, (q a).fst = t := hq
  have hjm' : jm q hqt (detRep (Fin t) χ) ≠ 0 := by
    have h1 := (jhMult_ne_zero_iff).1 hjm
    have hsub : IsSubquotient y.rep (detRep (Fin t) χ) := by
      have f := (IrrGL.equivOf (detRep (Fin t) χ) hds hdi)
      exact IsSubquotient.of_surjective f.toIntertwiningMap
        (fun w => ⟨f.invFun w, f.right_inv w⟩)
    exact (jhMult_ne_zero_iff).2
      (IsSubquotient.trans h1 (GlobalTheory.JacquetExact.isSubquotient_jac _ hds hsub))
  obtain ⟨A, hA, hnu⟩ := UpperTheory.Lit.Mix.detjac k t χ hχs q hqt hq0 hjm'
  by_contra hne
  have hsq := (jhMult_ne_zero_iff).1 hne
  obtain ⟨s, hsp⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_hasSupport hB hG p
  have hsup := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr
    (t := ![s, A]) (fun a => by fin_cases a <;> simpa) x.snd.rep.irr hsq
  have hmem : (IrrGL.ofChar χ hχs).nu (-(↑t - 1) / 2) ∈ ∑ a, (![s, A] : Fin 2 → _) a := by
    rw [Fin.sum_univ_two]
    exact Multiset.mem_add.2 (Or.inr hnu)
  exact UpperTheory.Lit.Mix.nolow hG hB hZ k r t _ x.rep _ χ hχs hrt hsup hxu hχu hmem
