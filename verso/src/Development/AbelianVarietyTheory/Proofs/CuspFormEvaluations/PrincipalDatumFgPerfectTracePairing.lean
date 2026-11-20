import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory

/- English proof (translation)
The claim follows from `bridge_star_holds D.R D.host x`.
-/
theorem cc_eq_host_conj (D : D7) (x : D.host.E) :
    ReciprocityTheory.ChartRestriction.G.FD.cc x = D.host.conj x :=
  bridge_star_holds D.R D.host x

/- English proof (translation)
Introduce `D`. Establish `hP` using `Formalism.IndefR.Fin.factPrincipalDatum`. Establish `hA` using `AA_ne_zero hP D`. Establish `hone : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0` using `one_ne_zero`. Use `⟨(D.host.AA : Submodule (𝓞 D.host.E) D.host.E), ?_, ?_, fun x => ⟨fun h => ?_, fun h => ?_⟩⟩` and prove the remaining obligations.

Conclude with `FractionalIdeal.fg_of_isNoetherianRing le_rfl _`. Introduce `h0`. Conclude with `hA (FractionalIdeal.coeToSubmodule_eq_bot.1 h0)`. Establish `h1 : ∀ w ∈ D.host.AA * D.host.AAbar, ∀ c : 𝓞 D.host.E, ∃ z : ℤ, Algebra.trace ℚ D.host.E (D.host.xi0 * x * (c • w)) = z`. Introduce `w hw`.

Use `FractionalIdeal.mul_induction_on (C := fun w => ∀ c : 𝓞 D.host.E, ∃ z : ℤ, Algebra.trace ℚ D.host.E (D.host.xi0 * x * (c • w)) = z) hw (fun a ha b hb c => ?_) (fun u v hu hv c => ?_)` and prove the remaining obligations. Take `⟨z, hz⟩` from `h (c • a) (Submodule.smul_mem _ c ha) (D.host.conj b) (conj_mem_AA D hb)`. Use `⟨z, ?_⟩` and prove the remaining obligations. Rewrite `hz` using `[cc_eq_host_conj, conj_conj]`. Rewrite using `[← hz, ← smul_mul_assoc, mul_assoc (D.host.xi0 * x)]`.

Take `⟨z, hz⟩` from `hu c`. Take `⟨z', hz'⟩` from `hv c`. Use `⟨z + z', ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add, mul_add, map_add, hz, hz', Int.cast_add]`. Establish `h2 : x ∈ FractionalIdeal.dual ℤ ℚ (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))`.

Rewrite using `[FractionalIdeal.mem_dual (FractionalIdeal.dual_ne_zero ℤ ℚ hone)]`. Introduce `a ha`. Rewrite `ha` using `[← dual_eq hP D, mul_assoc, FractionalIdeal.mem_singleton_mul]`. Take `⟨w, hw, rfl⟩` from `ha`. Take `⟨z, hz⟩` from `h1 w hw 1`.

Rewrite `hz` using `[one_smul]`. Use `⟨z, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.traceForm_apply, ← mul_assoc, mul_comm x, hz]`. Conclude with `eq_intCast _ _`. Rewrite `h2` using `[FractionalIdeal.dual_dual, FractionalIdeal.mem_one_iff]`.

Take `⟨c, rfl⟩` from `h2`. Conclude with `c.isIntegral_coe`. Introduce `a ha b hb`. Establish `hm : (⟨x, h⟩ : 𝓞 D.host.E) • (a * D.host.conj b) ∈ NAA D` using `Submodule.smul_mem _ _ (FractionalIdeal.mul_mem_mul ha (conj_mem_AAbar D hb))`. Take `⟨z, hz⟩` from `trace_int_of_mem hP D hm`.

Use `⟨z, ?_⟩` and prove the remaining obligations. Rewrite using `[← hz, cc_eq_host_conj, Algebra.smul_def]`. Use `congr 1`. Express the relevant statement in the definitionally equal form `_ = D.host.xi0 * (x * (a * D.host.conj b))`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem principalDatum_trace_perfect : ∀ D : D7, ∃ AA : Submodule (𝓞 D.host.E) D.host.E,
    AA.FG ∧ AA ≠ ⊥ ∧ ∀ x : D.host.E, (∀ a ∈ AA, ∀ b ∈ AA, ∃ z : ℤ,
      Algebra.trace ℚ D.host.E (D.host.xi0 * x * a * ReciprocityTheory.ChartRestriction.G.FD.cc b) = z) ↔
        IsIntegral ℤ x := by
  intro D
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  have hA := AA_ne_zero hP D
  have hone : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 := one_ne_zero
  refine ⟨(D.host.AA : Submodule (𝓞 D.host.E) D.host.E), ?_, ?_, fun x => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact FractionalIdeal.fg_of_isNoetherianRing le_rfl _
  · intro h0
    exact hA (FractionalIdeal.coeToSubmodule_eq_bot.1 h0)
  · have h1 : ∀ w ∈ D.host.AA * D.host.AAbar, ∀ c : 𝓞 D.host.E, ∃ z : ℤ,
        Algebra.trace ℚ D.host.E (D.host.xi0 * x * (c • w)) = z := by
      intro w hw
      refine FractionalIdeal.mul_induction_on (C := fun w => ∀ c : 𝓞 D.host.E, ∃ z : ℤ,
        Algebra.trace ℚ D.host.E (D.host.xi0 * x * (c • w)) = z) hw
        (fun a ha b hb c => ?_) (fun u v hu hv c => ?_)
      · obtain ⟨z, hz⟩ := h (c • a) (Submodule.smul_mem _ c ha) (D.host.conj b) (conj_mem_AA D hb)
        refine ⟨z, ?_⟩
        rw [cc_eq_host_conj, conj_conj] at hz
        rw [← hz, ← smul_mul_assoc, mul_assoc (D.host.xi0 * x)]
      · obtain ⟨z, hz⟩ := hu c
        obtain ⟨z', hz'⟩ := hv c
        refine ⟨z + z', ?_⟩
        rw [smul_add, mul_add, map_add, hz, hz', Int.cast_add]
    have h2 : x ∈ FractionalIdeal.dual ℤ ℚ (FractionalIdeal.dual ℤ ℚ
        (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) := by
      rw [FractionalIdeal.mem_dual (FractionalIdeal.dual_ne_zero ℤ ℚ hone)]
      intro a ha
      rw [← dual_eq hP D, mul_assoc, FractionalIdeal.mem_singleton_mul] at ha
      obtain ⟨w, hw, rfl⟩ := ha
      obtain ⟨z, hz⟩ := h1 w hw 1
      rw [one_smul] at hz
      refine ⟨z, ?_⟩
      rw [Algebra.traceForm_apply, ← mul_assoc, mul_comm x, hz]
      exact eq_intCast _ _
    rw [FractionalIdeal.dual_dual, FractionalIdeal.mem_one_iff] at h2
    obtain ⟨c, rfl⟩ := h2
    exact c.isIntegral_coe
  · intro a ha b hb
    have hm : (⟨x, h⟩ : 𝓞 D.host.E) • (a * D.host.conj b) ∈ NAA D :=
      Submodule.smul_mem _ _ (FractionalIdeal.mul_mem_mul ha (conj_mem_AAbar D hb))
    obtain ⟨z, hz⟩ := trace_int_of_mem hP D hm
    refine ⟨z, ?_⟩
    rw [← hz, cc_eq_host_conj, Algebra.smul_def]
    congr 1
    change _ = D.host.xi0 * (x * (a * D.host.conj b))
    ring

end GlobalTheory
