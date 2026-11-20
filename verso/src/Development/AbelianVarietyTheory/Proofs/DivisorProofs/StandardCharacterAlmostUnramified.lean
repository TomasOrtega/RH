import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnramifiedAwayDifferent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPrimeAdditiveCharacterUnramified
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section
namespace GlobalTheory.PsiStdCond

/- English proof (translation)
Introduce `F _ _ ψ hψ`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hfin : {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ differentIdeal ℤ (𝓞 F)}.Finite` using `Ideal.finite_factors differentIdeal_ne_bot`. Use `Filter.eventually_cofinite.2 (hfin.subset fun v hv => ?_)` and prove the remaining obligations. Assume the negation of the conclusion as `h`.

Conclude with `hv (GlobalTheory.StdCharUnrF.psiUnr_of_not_le F ψ hψ v fun h' => h (Ideal.dvd_iff_le.2 h'))`. Introduce `v`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Take `⟨π, hπ⟩` from `HeightOneSpectrum.valuation_exists_uniformizer F v`.

Use `set c : ℤ := FractionalIdeal.count F v (GlobalTheory.StdDual.codiff F) with hc`. Use `set x : Fv F v := algebraMap F (Fv F v) (π ^ (c - 1)) with hx`. Establish `hmem` using `(GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1 (GlobalTheory.LatVacArith.psi_fin_rat hψ) (GlobalTheory.AdelicU.singleFin v x)).2 (fun β hβ => by`. Establish `e : β * GlobalTheory.AdelicU.singleFin v x = GlobalTheory.AdelicU.singleFin v (x * β v)`. Apply `GlobalTheory.AdelicU.af_ext` to reduce the goal to its premises.

Introduce `u`. Distinguish the cases in `hu : u = v`. Substitute `hu` using the available equality. Rewrite using `[map_mul, GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self]`. Express the relevant statement in the definitionally equal form `β u * x = x * β u`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_mul, GlobalTheory.AdelicU.evalV_singleFin_ne hu, GlobalTheory.AdelicU.evalV_singleFin_ne hu, mul_zero]`. Rewrite using `[e]`. Conclude with `hcon _)`. Establish `h1` using `(GlobalTheory.Idele.mem_adelicIdeal_iff GlobalTheory.StdDual.codiff_ne_zero).1 hmem v`.

Establish `h2 : Valued.v (GlobalTheory.AdelicU.singleFin v x v) = Valued.v x`. Express the relevant statement in the definitionally equal form `Valued.v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ v (GlobalTheory.AdelicU.singleFin v x)) = _`. Rewrite using `[GlobalTheory.AdelicU.evalV_singleFin_self]`. Establish `h3 : Valued.v x = WithZero.exp (-(c - 1))`. Rewrite using `[hx, GlobalTheory.Idele.valued_algebraMap, map_zpow₀, hπ, ← WithZero.exp_zsmul]`.

Use `congr 1`. Simplify using the standard rewrite rules. Rewrite `h1` using `[← hc]`. Rewrite `h1` using `[h2, h3, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem psi_std_conductor : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    (∀ᶠ v in cofinite, PsiUnr ψ v) ∧ ∀ v : Pl F, ∃ x, psiLoc ψ v x ≠ 1 := by
  classical
  intro F _ _ ψ hψ
  refine ⟨?_, ?_⟩
  · have hfin : {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ differentIdeal ℤ (𝓞 F)}.Finite :=
      Ideal.finite_factors differentIdeal_ne_bot
    refine Filter.eventually_cofinite.2 (hfin.subset fun v hv => ?_)
    by_contra h
    exact hv (GlobalTheory.StdCharUnrF.psiUnr_of_not_le F ψ hψ v fun h' => h (Ideal.dvd_iff_le.2 h'))
  · intro v
    by_contra hcon
    push_neg at hcon
    obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer F v
    set c : ℤ := FractionalIdeal.count F v (GlobalTheory.StdDual.codiff F) with hc
    set x : Fv F v := algebraMap F (Fv F v) (π ^ (c - 1)) with hx
    have hmem := (GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1 (GlobalTheory.LatVacArith.psi_fin_rat hψ)
      (GlobalTheory.AdelicU.singleFin v x)).2 (fun β hβ => by
        have e : β * GlobalTheory.AdelicU.singleFin v x = GlobalTheory.AdelicU.singleFin v (x * β v) := by
          apply GlobalTheory.AdelicU.af_ext
          intro u
          by_cases hu : u = v
          · subst hu
            rw [map_mul, GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self]
            change β u * x = x * β u
            ring
          · rw [map_mul, GlobalTheory.AdelicU.evalV_singleFin_ne hu, GlobalTheory.AdelicU.evalV_singleFin_ne hu, mul_zero]
        rw [e]
        exact hcon _)
    have h1 := (GlobalTheory.Idele.mem_adelicIdeal_iff GlobalTheory.StdDual.codiff_ne_zero).1 hmem v
    have h2 : Valued.v (GlobalTheory.AdelicU.singleFin v x v) = Valued.v x := by
      change Valued.v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ v (GlobalTheory.AdelicU.singleFin v x)) = _
      rw [GlobalTheory.AdelicU.evalV_singleFin_self]
    have h3 : Valued.v x = WithZero.exp (-(c - 1)) := by
      rw [hx, GlobalTheory.Idele.valued_algebraMap, map_zpow₀, hπ, ← WithZero.exp_zsmul]
      congr 1
      simp
    rw [← hc] at h1
    rw [h2, h3, WithZero.exp_le_exp] at h1
    omega

end GlobalTheory.PsiStdCond
