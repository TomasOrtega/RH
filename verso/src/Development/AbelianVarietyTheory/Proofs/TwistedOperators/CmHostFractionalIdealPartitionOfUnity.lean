import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThPDatumEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HostAAPartition

/- English proof (translation)
Establish `hb : D.host.𝔟 ≠ ⊥`. Introduce `h0`. Establish `h1` using `D.host.𝔟_spec.1`. Rewrite `h1` using `[h0, Ideal.bot_mul]`. Conclude with `differentIdeal_ne_bot h1`.

Establish `hc : D.host.ccE ≠ ⊥`. Unfold `Formalism.BasicNotions.Host.ccE`. Rewrite using `[Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 D.host.K) (𝓞 D.host.E))]`. Conclude with `D.host.ccK_ne_bot`. Unfold `Formalism.BasicNotions.Host.AA Formalism.BasicNotions.Host.AA0`.

Conclude with `mul_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hc) (inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hb))`.
-/
theorem host_AA_ne_zero (D : D7) : D.host.AA ≠ 0 := by
  have hb : D.host.𝔟 ≠ ⊥ := by
    intro h0
    have h1 := D.host.𝔟_spec.1
    rw [h0, Ideal.bot_mul] at h1
    exact differentIdeal_ne_bot h1
  have hc : D.host.ccE ≠ ⊥ := by
    unfold Formalism.BasicNotions.Host.ccE
    rw [Ne, Ideal.map_eq_bot_iff_of_injective
      (FaithfulSMul.algebraMap_injective (𝓞 D.host.K) (𝓞 D.host.E))]
    exact D.host.ccK_ne_bot
  unfold Formalism.BasicNotions.Host.AA Formalism.BasicNotions.Host.AA0
  exact mul_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hc)
    (inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hb))

/- English proof (translation)
Introduce `D`. Use `set I := D.host.AA with hI`. Establish `hne : I ≠ 0` using `host_AA_ne_zero D`. Establish `h1 : (1 : D.host.E) ∈ I * I⁻¹`. Rewrite using `[mul_inv_cancel₀ hne]`.

Conclude with `FractionalIdeal.one_mem_one _`. Establish `key : ∀ z ∈ I * I⁻¹, ∃ (m : ℕ) (a c : Fin m → D.host.E), (∀ i, a i ∈ I) ∧ (∀ i, ∀ x ∈ I, ∃ b : 𝓞 D.host.E, (b : D.host.E) = c i * x) ∧ ∑ i, a i * c i = z`. Introduce `z hz`. Use `FractionalIdeal.mul_induction_on (C := fun z => ∃ (m : ℕ) (a c : Fin m → D.host.E), (∀ i, a i ∈ I) ∧ (∀ i, ∀ x ∈ I, ∃ b : 𝓞 D.host.E, (b : D.host.E) = c i * x) ∧ ∑ i, a i * c i = z) hz ?_ ?_` and prove the remaining obligations. Introduce `u hu v hv`.

Use `⟨1, fun _ => u, fun _ => v, fun _ => hu, ?_, by simp⟩` and prove the remaining obligations. Introduce `_ x hx`. Establish `hvx : v * x ∈ I⁻¹ * I` using `FractionalIdeal.mul_mem_mul hv hx`. Rewrite `hvx` using `[inv_mul_cancel₀ hne, FractionalIdeal.mem_one_iff]`. Take `⟨b, hb⟩` from `hvx`.

Conclude with `⟨b, hb⟩`. Introduce and unpack `u v ⟨m, a, c, ha, hc, rfl⟩ ⟨n, a', c', ha', hc', rfl⟩`. Use `⟨m + n, Fin.append a a', Fin.append c c', ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`. Use `Fin.addCases (fun j => ?_) (fun j => ?_) i` and prove the remaining obligations.

Simplify using `using ha j`. Simplify using `using ha' j`. Introduce `i`. Use `Fin.addCases (fun j => ?_) (fun j => ?_) i` and prove the remaining obligations. Simplify using `using hc j`.

Simplify using `using hc' j`. Rewrite using `[Fin.sum_univ_add]`. Simplify using the standard rewrite rules. Conclude with `key 1 h1`.
-/
theorem host_AA_partition : ∀ (D : D7), ∃ (m : ℕ) (a c : Fin m → D.host.E), (∀ i, a i ∈ D.host.AA) ∧ (∀ i, ∀ x ∈ D.host.AA, ∃ b : 𝓞 D.host.E, (b : D.host.E) = c i * x) ∧ ∑ i, a i * c i = 1 := by
  intro D
  set I := D.host.AA with hI
  have hne : I ≠ 0 := host_AA_ne_zero D
  have h1 : (1 : D.host.E) ∈ I * I⁻¹ := by
    rw [mul_inv_cancel₀ hne]
    exact FractionalIdeal.one_mem_one _
  have key : ∀ z ∈ I * I⁻¹, ∃ (m : ℕ) (a c : Fin m → D.host.E), (∀ i, a i ∈ I) ∧
      (∀ i, ∀ x ∈ I, ∃ b : 𝓞 D.host.E, (b : D.host.E) = c i * x) ∧ ∑ i, a i * c i = z := by
    intro z hz
    refine FractionalIdeal.mul_induction_on (C := fun z => ∃ (m : ℕ) (a c : Fin m → D.host.E),
      (∀ i, a i ∈ I) ∧ (∀ i, ∀ x ∈ I, ∃ b : 𝓞 D.host.E, (b : D.host.E) = c i * x) ∧
        ∑ i, a i * c i = z) hz ?_ ?_
    · intro u hu v hv
      refine ⟨1, fun _ => u, fun _ => v, fun _ => hu, ?_, by simp⟩
      intro _ x hx
      have hvx : v * x ∈ I⁻¹ * I := FractionalIdeal.mul_mem_mul hv hx
      rw [inv_mul_cancel₀ hne, FractionalIdeal.mem_one_iff] at hvx
      obtain ⟨b, hb⟩ := hvx
      exact ⟨b, hb⟩
    · rintro u v ⟨m, a, c, ha, hc, rfl⟩ ⟨n, a', c', ha', hc', rfl⟩
      refine ⟨m + n, Fin.append a a', Fin.append c c', ?_, ?_, ?_⟩
      · intro i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simpa using ha j
        · simpa using ha' j
      · intro i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simpa using hc j
        · simpa using hc' j
      · rw [Fin.sum_univ_add]
        simp
  exact key 1 h1

end GlobalTheory.HostAAPartition
