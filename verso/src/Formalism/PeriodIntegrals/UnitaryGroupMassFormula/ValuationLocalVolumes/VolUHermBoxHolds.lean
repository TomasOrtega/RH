import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.ThetaExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolUFinal

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
  NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `hψ hs v hv`. Take `⟨hg, -, hd⟩` from `VolUT.typ_arith X v hv`. Establish `hann` using `VolUTr.annX_of X ψ Formalism.L2.SG.Pf.conductor_inverse_different hψ hs v`. Establish `hfin` using `X.B.I.cm.deg2`. Take `⟨hH, -, hO⟩` from `VolUL.sd_facts ψ v hψ hfin hann hd (Fin (D.R.rS + 1) × Fin (D.R.rS + 1))`.

Use `haveI := hH`. Establish `hmax : v.asIdeal.IsMaximal` using `v.isMaximal`. Take `⟨P, hPmax, hPv⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 X.B.I.E) v.asIdeal (by`. Rewrite using `[(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective (𝓞 X.B.I.F) (𝓞 X.B.I.E))]`. Conclude with `bot_le)`.

Take `⟨θ, t, htθ, hnot⟩` from `X.B.I.cm.cmUnram.2.2 P hPmax`. Use `set σ := X.B.I.cm.sig with hσ`. Establish `hσx : ∀ x, σ x = star x` using `fun x => rfl`. Establish `hinv : ∀ y, σ (σ y) = y` using `fun y => by rw [hσx, hσx, star_star]`. Establish `ht : σ (θ : X.B.I.E) = (t : X.B.I.E)` using `by rw [hσx]; exact htθ.symm`.

Establish `hne : (θ : X.B.I.E) ≠ t`. Introduce `h`. Apply `hnot` to reduce the goal to its premises. Establish `: θ - t = 0` using `by ext; simp [h]`. Rewrite using `[this]`.

Conclude with `P.zero_mem`. Establish `hnt : ∃ x, σ x ≠ x` using `⟨θ, by rw [ht]; exact fun h => hne h.symm⟩`. Establish `hfix : star (((θ : X.B.I.E) - t) ^ 2) = ((θ : X.B.I.E) - t) ^ 2`. Establish `htθ' : (t : X.B.I.E) = star (θ : X.B.I.E)` using `htθ`. Establish `h1 : star (t : X.B.I.E) = θ` using `by rw [htθ', star_star]`.

Rewrite using `[star_pow, star_sub, h1, ← htθ']`. Expand and normalize the polynomial expressions, which then agree. Take `⟨f, hf⟩` from `(X.B.I.cm.fixed _).1 hfix`. Establish `hint : IsIntegral ℤ (algebraMap X.B.I.F X.B.I.E f)`. Rewrite using `[hf]`.

Establish `h1 : (((θ - t) ^ 2 : 𝓞 X.B.I.E) : X.B.I.E) = ((θ : X.B.I.E) - t) ^ 2` using `by push_cast; ring`. Rewrite using `[← h1]`. Conclude with `RingOfIntegers.isIntegral_coe _`. Establish `hfint : IsIntegral ℤ f` using `(isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ X.B.I.F X.B.I.E) (algebraMap X.B.I.F X.B.I.E).injective).mp hint`. Use `set e : 𝓞 X.B.I.F := ⟨f, hfint⟩ with he`.

Establish `he2 : ((θ : X.B.I.E) - t) ^ 2 = algebraMap X.B.I.F X.B.I.E (e : X.B.I.F)` using `hf.symm`. Establish `hev : e ∉ v.asIdeal`. Introduce `hm`. Rewrite `hm` using `[← hPv]`. Establish `hm' : algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) e ∈ P` using `hm`.

Establish `heq : algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) e = (θ - t) ^ 2`. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Rewrite using `[← IsScalarTower.algebraMap_apply (𝓞 X.B.I.F) (𝓞 X.B.I.E) X.B.I.E, IsScalarTower.algebraMap_apply (𝓞 X.B.I.F) X.B.I.F X.B.I.E, map_pow, map_sub]`. Conclude with `he2.symm`. Rewrite `hm'` using `[heq]`.

Conclude with `hnot (hPmax.isPrime.mem_of_pow_mem 2 hm')`. Take `⟨θ0, Δ, hθO, hθ, hΔ, hΔ0⟩` from `VolV.theta_exists σ v hinv hnt hfin θ t ht e he2 hev`. Establish `htr` using `VolUTr.TrW.trace_v v σ hinv hnt hfin`. Introduce `c hc`. Conclude with `VolV.hermBox_meas σ v _ hfin htr (gAt_prime X v).ne_zero hg hθO hθ hΔ hΔ0 _ hO c hc`.
-/
theorem volUHermBox_holds {D : D7} (X : HidaSetting D) (ψ : AddChar (AF X.B.I.F) ℂ) : VolUHermBox X ψ := by
  intro hψ hs v hv
  obtain ⟨hg, -, hd⟩ := VolUT.typ_arith X v hv
  have hann := VolUTr.annX_of X ψ Formalism.L2.SG.Pf.conductor_inverse_different hψ hs v
  have hfin := X.B.I.cm.deg2
  obtain ⟨hH, -, hO⟩ := VolUL.sd_facts ψ v hψ hfin hann hd (Fin (D.R.rS + 1) × Fin (D.R.rS + 1))
  haveI := hH
  have hmax : v.asIdeal.IsMaximal := v.isMaximal
  obtain ⟨P, hPmax, hPv⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 X.B.I.E) v.asIdeal
    (by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp
        (FaithfulSMul.algebraMap_injective (𝓞 X.B.I.F) (𝓞 X.B.I.E))]
      exact bot_le)
  obtain ⟨θ, t, htθ, hnot⟩ := X.B.I.cm.cmUnram.2.2 P hPmax
  set σ := X.B.I.cm.sig with hσ
  have hσx : ∀ x, σ x = star x := fun x => rfl
  have hinv : ∀ y, σ (σ y) = y := fun y => by rw [hσx, hσx, star_star]
  have ht : σ (θ : X.B.I.E) = (t : X.B.I.E) := by rw [hσx]; exact htθ.symm
  have hne : (θ : X.B.I.E) ≠ t := by
    intro h
    apply hnot
    have : θ - t = 0 := by ext; simp [h]
    rw [this]; exact P.zero_mem
  have hnt : ∃ x, σ x ≠ x := ⟨θ, by rw [ht]; exact fun h => hne h.symm⟩
  have hfix : star (((θ : X.B.I.E) - t) ^ 2) = ((θ : X.B.I.E) - t) ^ 2 := by
    have htθ' : (t : X.B.I.E) = star (θ : X.B.I.E) := htθ
    have h1 : star (t : X.B.I.E) = θ := by rw [htθ', star_star]
    rw [star_pow, star_sub, h1, ← htθ']
    ring
  obtain ⟨f, hf⟩ := (X.B.I.cm.fixed _).1 hfix
  have hint : IsIntegral ℤ (algebraMap X.B.I.F X.B.I.E f) := by
    rw [hf]
    have h1 : (((θ - t) ^ 2 : 𝓞 X.B.I.E) : X.B.I.E) = ((θ : X.B.I.E) - t) ^ 2 := by push_cast; ring
    rw [← h1]
    exact RingOfIntegers.isIntegral_coe _
  have hfint : IsIntegral ℤ f :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ X.B.I.F X.B.I.E)
      (algebraMap X.B.I.F X.B.I.E).injective).mp hint
  set e : 𝓞 X.B.I.F := ⟨f, hfint⟩ with he
  have he2 : ((θ : X.B.I.E) - t) ^ 2 = algebraMap X.B.I.F X.B.I.E (e : X.B.I.F) := hf.symm
  have hev : e ∉ v.asIdeal := by
    intro hm
    rw [← hPv] at hm
    have hm' : algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) e ∈ P := hm
    have heq : algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) e = (θ - t) ^ 2 := by
      apply RingOfIntegers.coe_injective
      rw [← IsScalarTower.algebraMap_apply (𝓞 X.B.I.F) (𝓞 X.B.I.E) X.B.I.E,
        IsScalarTower.algebraMap_apply (𝓞 X.B.I.F) X.B.I.F X.B.I.E, map_pow, map_sub]
      exact he2.symm
    rw [heq] at hm'
    exact hnot (hPmax.isPrime.mem_of_pow_mem 2 hm')
  obtain ⟨θ0, Δ, hθO, hθ, hΔ, hΔ0⟩ := VolV.theta_exists σ v hinv hnt hfin θ t ht e he2 hev
  have htr := VolUTr.TrW.trace_v v σ hinv hnt hfin
  intro c hc
  exact VolV.hermBox_meas σ v _ hfin htr (gAt_prime X v).ne_zero hg hθO hθ hΔ hΔ0 _ hO c hc

end Formalism.L2.SG.Pf.NcVal
