import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe

open UpperTheory.V UpperTheory.V.PropA

/- English proof (translation)
Introduce `l _ X _ _ R hgen`. Take `⟨π, hπ⟩` from `hgen`. Set `I : Submodule ℤ_[l] ℤ_[l]` to `IsLocalRing.maximalIdeal ℤ_[l]`. Establish `hsimple : IsSimpleModule ℤ_[l] (ℤ_[l] ⧸ I)` using `isSimpleModule_iff_isCoatom.2 (Ideal.isMaximal_def.1 (IsLocalRing.maximalIdeal.isMaximal ℤ_[l]))`. Set `P : Submodule ℤ_[l] (Fin R → ℤ_[l])` to `Submodule.pi Set.univ (fun _ => I)`.

Set `q : Submodule ℤ_[l] X` to `LinearMap.range ((l : ℤ_[l]) • (1 : Module.End ℤ_[l] X))`. Establish `hle : P ≤ q.comap π`. Introduce `v hv`. Rewrite `hv` using `[Submodule.mem_pi]`. Establish `hex : ∀ i, ∃ w : ℤ_[l], v i = (l : ℤ_[l]) * w`.

Introduce `i`. Establish `hi` using `hv i (Set.mem_univ i)`. Express the relevant statement in the definitionally equal form `v i ∈ IsLocalRing.maximalIdeal ℤ_[l] at hi`. Rewrite `hi` using `[PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton']`. Take `⟨a, ha⟩` from `hi`.

Conclude with `⟨a, by rw [← ha, mul_comm]⟩`. Use `choose w hw using hex`. Establish `hv' : v = (l : ℤ_[l]) • w` using `funext fun i => by simp [hw i]`. Rewrite using `[Submodule.mem_comap, LinearMap.mem_range]`. Use `⟨π w, ?_⟩` and prove the remaining obligations.

Rewrite using `[LinearMap.smul_apply, Module.End.one_apply, hv', map_smul]`. Establish `hφ : Function.Surjective (P.mapQ q π hle)`. Introduce `z`. Use `Submodule.Quotient.induction_on _ z ?_` and prove the remaining obligations. Introduce `x`.

Take `⟨v, rfl⟩` from `hπ x`. Conclude with `⟨Submodule.Quotient.mk v, Submodule.mapQ_apply _ _ _ _⟩`. Establish `h1` using `Module.length_le_of_surjective (P.mapQ q π hle) hφ`. Establish `h2 : Module.length ℤ_[l] ((Fin R → ℤ_[l]) ⧸ P) = R`. Rewrite using `[(Submodule.quotientPi (fun _ : Fin R => I)).length_eq, Module.length_pi_of_fintype]`.

Simplify using `[Module.length_eq_one]`. Conclude with `h1.trans h2.le`.
-/
theorem UpperTheory.V.PropA.cokL :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (R : ℕ), GenBy l R X → cokLen ((l : ℤ_[l]) • (1 : Module.End ℤ_[l] X)) ≤ R := by
  intro l _ X _ _ R hgen
  obtain ⟨π, hπ⟩ := hgen
  classical
  let I : Submodule ℤ_[l] ℤ_[l] := IsLocalRing.maximalIdeal ℤ_[l]
  have hsimple : IsSimpleModule ℤ_[l] (ℤ_[l] ⧸ I) :=
    isSimpleModule_iff_isCoatom.2 (Ideal.isMaximal_def.1 (IsLocalRing.maximalIdeal.isMaximal ℤ_[l]))
  let P : Submodule ℤ_[l] (Fin R → ℤ_[l]) := Submodule.pi Set.univ (fun _ => I)
  let q : Submodule ℤ_[l] X := LinearMap.range ((l : ℤ_[l]) • (1 : Module.End ℤ_[l] X))
  have hle : P ≤ q.comap π := by
    intro v hv
    rw [Submodule.mem_pi] at hv
    have hex : ∀ i, ∃ w : ℤ_[l], v i = (l : ℤ_[l]) * w := by
      intro i
      have hi := hv i (Set.mem_univ i)
      change v i ∈ IsLocalRing.maximalIdeal ℤ_[l] at hi
      rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hi
      obtain ⟨a, ha⟩ := hi
      exact ⟨a, by rw [← ha, mul_comm]⟩
    choose w hw using hex
    have hv' : v = (l : ℤ_[l]) • w := funext fun i => by simp [hw i]
    rw [Submodule.mem_comap, LinearMap.mem_range]
    refine ⟨π w, ?_⟩
    rw [LinearMap.smul_apply, Module.End.one_apply, hv', map_smul]
  have hφ : Function.Surjective (P.mapQ q π hle) := by
    intro z
    refine Submodule.Quotient.induction_on _ z ?_
    intro x
    obtain ⟨v, rfl⟩ := hπ x
    exact ⟨Submodule.Quotient.mk v, Submodule.mapQ_apply _ _ _ _⟩
  have h1 := Module.length_le_of_surjective (P.mapQ q π hle) hφ
  have h2 : Module.length ℤ_[l] ((Fin R → ℤ_[l]) ⧸ P) = R := by
    rw [(Submodule.quotientPi (fun _ : Fin R => I)).length_eq, Module.length_pi_of_fintype]
    simp [Module.length_eq_one]
  exact h1.trans h2.le
