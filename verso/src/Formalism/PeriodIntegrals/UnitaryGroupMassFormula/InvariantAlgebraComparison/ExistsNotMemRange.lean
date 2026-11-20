import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantAlgebraComparison.InvAlgOfSteps

noncomputable section

namespace PI.UnitaryGroupMassFormula.BridgeInvAlg

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)
open Formalism.L2.SG.AdBridge

namespace GrothendieckRing

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push Not at h`. Establish `h1 : Module.finrank I.F I.E = 1`. Rewrite using `[finrank_eq_one_iff_of_nonzero' (1 : I.E) one_ne_zero]`. Introduce `w`.

Take `⟨c, hc⟩` from `RingHom.mem_range.1 (h w)`. Conclude with `⟨c, by rw [Algebra.smul_def, mul_one, hc]⟩`. Establish `h2` using `I.cm.deg2`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_not_mem_range (I : AutInst) : ∃ ω : I.E, ω ∉ (algebraMap I.F I.E).range := by
  by_contra h
  push Not at h
  have h1 : Module.finrank I.F I.E = 1 := by
    rw [finrank_eq_one_iff_of_nonzero' (1 : I.E) one_ne_zero]
    intro w
    obtain ⟨c, hc⟩ := RingHom.mem_range.1 (h w)
    exact ⟨c, by rw [Algebra.smul_def, mul_one, hc]⟩
  have h2 := I.cm.deg2
  omega

def om (I : AutInst) : I.E := (exists_not_mem_range I).choose

/- English proof (translation)
The claim follows from `(exists_not_mem_range I).choose_spec`.
-/
theorem om_not_mem (I : AutInst) : om I ∉ (algebraMap I.F I.E).range :=
  (exists_not_mem_range I).choose_spec

/- English proof (translation)
Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t hst`. Distinguish the cases in `ht : t = 0`. Substitute `ht` using the available equality. Rewrite `hst` using `[zero_smul, add_zero]`.

Conclude with `⟨(smul_eq_zero.1 hst).resolve_right one_ne_zero, rfl⟩`. It suffices to derive a contradiction. Apply `om_not_mem I` to reduce the goal to its premises. Use `⟨-(s / t), ?_⟩` and prove the remaining obligations. Rewrite `hst` using `[Algebra.smul_def, Algebra.smul_def, mul_one]`.

Establish `ht' : algebraMap I.F I.E t ≠ 0` using `(map_ne_zero _).2 ht`. Rewrite using `[map_neg, map_div₀, neg_eq_iff_eq_neg, div_eq_iff ht']`. Take the linear combination `hst`.
-/
theorem linIndep_one_om (I : AutInst) : LinearIndependent I.F ![(1 : I.E), om I] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    rw [zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.1 hst).resolve_right one_ne_zero, rfl⟩
  · exfalso
    apply om_not_mem I
    refine ⟨-(s / t), ?_⟩
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
    have ht' : algebraMap I.F I.E t ≠ 0 := (map_ne_zero _).2 ht
    rw [map_neg, map_div₀, neg_eq_iff_eq_neg, div_eq_iff ht']
    linear_combination hst

def bE (I : AutInst) : Module.Basis (Fin 2) I.F I.E :=
  basisOfLinearIndependentOfCardEqFinrank (linIndep_one_om I)
    (by rw [Fintype.card_fin, I.cm.deg2])

end GrothendieckRing

open GrothendieckRing

end PI.UnitaryGroupMassFormula.BridgeInvAlg
