import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUniqueIsStandardAdeleCharUnramifiedCMBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalSymplecticPointsSelfAnnihilator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardAdelicCharacterLocalComponentNeOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharOfTrace
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DualLatticeDifferentIndex

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

/- English proof (translation)
Use `Prod.ext rfl ?_` and prove the remaining obligations. Use `Subtype.ext (funext fun v => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(sLoc E w y) v = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV E w y v`. Distinguish the cases in `h : v = w`. Substitute `h` using the available equality.

Rewrite using `[GlobalTheory.StdDual.singleV_self]`. Conclude with `(Pi.single_eq_same v y : (Pi.single v y : ∀ u : HeightOneSpectrum (𝓞 E), u.adicCompletion E) v = y)`. Rewrite using `[GlobalTheory.StdDual.singleV_of_ne _ h]`. Conclude with `(Pi.single_eq_of_ne h y : (Pi.single w y : ∀ u : HeightOneSpectrum (𝓞 E), u.adicCompletion E) v = 0)`.
-/
theorem sFin_sLoc_eq (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) :
    sFin E (sLoc E w y) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA E 0 (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV E w y) := by
  classical
  refine Prod.ext rfl ?_
  refine Subtype.ext (funext fun v => ?_)
  change (sLoc E w y) v = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV E w y v
  by_cases h : v = w
  · subst h
    rw [GlobalTheory.StdDual.singleV_self]
    exact (Pi.single_eq_same v y : (Pi.single v y : ∀ u : HeightOneSpectrum (𝓞 E), u.adicCompletion E) v = y)
  · rw [GlobalTheory.StdDual.singleV_of_ne _ h]
    exact (Pi.single_eq_of_ne h y : (Pi.single w y : ∀ u : HeightOneSpectrum (𝓞 E), u.adicCompletion E) v = 0)

/- English proof (translation)
Introduce `E _ _`. Take `⟨ψ, hψ, -⟩` from `GlobalTheory.StdCharUnique.existsUnique_isStdChar E`. Set `L : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf E →+ ℂ` to `AddMonoidHom.mk' (fun x => (GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.traceInf E x : ℂ)) fun a b => by`. Rewrite using `[GlobalTheory.StdCharUnique.traceInf_add, Complex.ofReal_add]`. Establish `hL : Continuous L` using `Complex.continuous_ofReal.comp (GlobalTheory.StdCharUnique.continuous_traceInf E)`.

Establish `hT : ∀ x : E, L (algebraMap E _ x) = ((Algebra.trace ℚ E x : ℚ) : ℂ)` using `fun x => by show ((GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.traceInf E (algebraMap E _ x) : ℝ) : ℂ) = _`. Rewrite using `[GlobalTheory.StdCharUnique.traceInf_algebraMap, Complex.ofReal_ratCast]`. Establish `hinf : ∀ x, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiInf E ψ x = Complex.exp (-(2 * Real.pi * Complex.I * L x))` using `fun x => by`. Rewrite using `[hψ.2, GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.stdInf]`. Use `congr 1`.

Use `show _ * ((GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.traceInf E x : ℝ) : ℂ) = -(_ * ((GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.traceInf E x : ℝ) : ℂ))`. Expand and normalize the polynomial expressions, which then agree. Establish `hv : ∀ v, ∃ y, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiV E ψ v y ≠ 1` using `fun v => by`. Take `⟨y, hy⟩` from `GlobalTheory.StdCharLocal.psiV_ne_one_of_trace (GlobalTheory.StdAdelicChar.isCharAF_inv hψ.1) (fun a => by`. Rewrite using `[Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiInf, AddChar.inv_apply', ← Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiInf, hinf, hT, ← Complex.exp_neg, neg_neg]) v`.

Use `⟨y, fun h1 => hy ?_⟩` and prove the remaining obligations. Rewrite `h1`, the goal using `[Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiV]`. Rewrite using `[AddChar.inv_apply', h1, inv_one]`. Use `⟨ψ, hψ.1.1, hψ.1.2.1, hψ.1.2.2.1, fun x h => GlobalTheory.RatAnnih.adele_rat hψ.1 hv L hL hT hinf x h, fun w => ?_⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `hv w`.

Use `⟨y, ?_⟩` and prove the remaining obligations. Rewrite using `[sFin_sLoc_eq]`. Conclude with `hy`.
-/
theorem exists_stdPsi : ∀ (E : Type) [Field E] [NumberField E], ∃ ψ : AddChar (Ad E) ℂ, StdPsi ψ := by
  intro E _ _
  obtain ⟨ψ, hψ, -⟩ := GlobalTheory.StdCharUnique.existsUnique_isStdChar E
  let L : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf E →+ ℂ :=
    AddMonoidHom.mk' (fun x => (GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.traceInf E x : ℂ)) fun a b => by
      rw [GlobalTheory.StdCharUnique.traceInf_add, Complex.ofReal_add]
  have hL : Continuous L := Complex.continuous_ofReal.comp (GlobalTheory.StdCharUnique.continuous_traceInf E)
  have hT : ∀ x : E, L (algebraMap E _ x) = ((Algebra.trace ℚ E x : ℚ) : ℂ) := fun x => by
    show ((GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.traceInf E (algebraMap E _ x) : ℝ) : ℂ) = _
    rw [GlobalTheory.StdCharUnique.traceInf_algebraMap, Complex.ofReal_ratCast]
  have hinf : ∀ x, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiInf E ψ x = Complex.exp (-(2 * Real.pi * Complex.I * L x)) := fun x => by
    rw [hψ.2, GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.stdInf]
    congr 1
    show _ * ((GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.traceInf E x : ℝ) : ℂ) = -(_ * ((GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.traceInf E x : ℝ) : ℂ))
    ring
  have hv : ∀ v, ∃ y, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiV E ψ v y ≠ 1 := fun v => by
    obtain ⟨y, hy⟩ := GlobalTheory.StdCharLocal.psiV_ne_one_of_trace (GlobalTheory.StdAdelicChar.isCharAF_inv hψ.1) (fun a => by
      rw [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiInf, AddChar.inv_apply', ← Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiInf, hinf, hT, ← Complex.exp_neg, neg_neg]) v
    refine ⟨y, fun h1 => hy ?_⟩
    rw [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiV] at h1 ⊢
    rw [AddChar.inv_apply', h1, inv_one]
  refine ⟨ψ, hψ.1.1, hψ.1.2.1, hψ.1.2.2.1, fun x h => GlobalTheory.RatAnnih.adele_rat hψ.1 hv L hL hT hinf x h, fun w => ?_⟩
  obtain ⟨y, hy⟩ := hv w
  refine ⟨y, ?_⟩
  rw [sFin_sLoc_eq]
  exact hy

end GlobalTheory.CuspGeneric

end
