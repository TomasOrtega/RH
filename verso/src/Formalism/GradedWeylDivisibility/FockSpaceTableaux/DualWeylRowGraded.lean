import Formalism.GradedWeylDivisibility.StatementA
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LRowstLemmas

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Introduce `R _ r n ν μ f hf`. Simplify using `only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule] at hf ⊢`. Take `⟨hcol, hadd⟩` from `hf`. Use `⟨?_, fun l j hlj => ?_⟩` and prove the remaining obligations. Introduce `d hd`.

Rewrite `hd` using `[coeff_weightedHomogeneousComponent]`. Use `split_ifs at hd with h`. Conclude with `hcol hd`. Conclude with `absurd rfl hd`. Set `w' : Option (Fin r × Fin n) → (Fin r → ℕ)` to `fun o => Option.elim o 0 (rowW r n)`.

Establish `key : ∀ F : Fin r × Fin n → MvPolynomial (Option (Fin r × Fin n)) R, (∀ v, IsWeightedHomogeneous w' (F v) (rowW r n v)) → ∀ φ : MvPolynomial (Fin r × Fin n) R, weightedHomogeneousComponent w' μ (aeval F φ) = aeval F (weightedHomogeneousComponent (rowW r n) μ φ)`. Introduce `F hF φ`. Use `MvPolynomial.induction_on' φ (fun u a => ?_) (fun p q hp hq => ?_)` and prove the remaining obligations. Establish `hm : IsWeightedHomogeneous w' (aeval F (monomial u a)) (Finsupp.weight (rowW r n) u)`. Rewrite using `[aeval_monomial, Finsupp.prod, Finsupp.weight_apply, Finsupp.sum, algebraMap_eq]`.

Use `(isWeightedHomogeneous_C w' a).mul (IsWeightedHomogeneous.prod u.support (fun i => F i ^ u i) (fun i => u i • rowW r n i) fun i _ => (hF i).pow (u i))` as an intermediate fact. Rewrite `this` using `[zero_add]`. Then use the resulting hypothesis. Establish `hm0 : IsWeightedHomogeneous (rowW r n) (monomial u a) (Finsupp.weight (rowW r n) u)` using `isWeightedHomogeneous_monomial _ _ _ rfl`. Rewrite using `[weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hm), weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hm0)]`. Apply the tactic sequence `split_ifs <;> simp`.

Simplify using `only [map_add, hp, hq]`. Set `G : Fin r × Fin n → MvPolynomial (Option (Fin r × Fin n)) R` to `fun v => if v.2 = j then X (some v) + X none * X (some (v.1, l)) else X (some v)`. Establish `hG : ∀ v, IsWeightedHomogeneous w' (G v) (rowW r n v)`. Introduce `v`. Simplify using `only [G]`.

Use `split_ifs`. Use `(isWeightedHomogeneous_X R w' (some v)).add ?_` and prove the remaining obligations. Use `(isWeightedHomogeneous_X R w' none).mul (isWeightedHomogeneous_X R w' (some (v.1, l)))` as an intermediate fact. Rewrite `this` using `[show w' none = 0 from rfl, zero_add]`. Conclude with `this`.

Conclude with `isWeightedHomogeneous_X R w' (some v)`. Establish `hGs : ∀ v, IsWeightedHomogeneous w' ((fun v : Fin r × Fin n => (X (some v) : MvPolynomial (Option (Fin r × Fin n)) R)) v) (rowW r n v)` using `fun v => isWeightedHomogeneous_X R w' (some v)`. Establish `hA : colAddGen R (r` using `r) l j = aeval G := rfl`. Establish `hB : (rename (R` using `R) (some : Fin r × Fin n → Option (Fin r × Fin n))) = aeval (fun v : Fin r × Fin n => (X (some v) : MvPolynomial (Option (Fin r × Fin n)) R)) := by`. Use extensionality with `v`.

Simplify using the standard rewrite rules. Establish `h1` using `hadd l j hlj`. Rewrite `h1`, the goal using `[hA, hB]`. Rewrite using `[← key G hG, ← key _ hGs, h1]`.
-/
theorem dualWeylModuleRowGraded : DualWeylRowGraded := by
  classical
  intro R _ r n ν μ f hf
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule] at hf ⊢
  obtain ⟨hcol, hadd⟩ := hf
  refine ⟨?_, fun l j hlj => ?_⟩
  · intro d hd
    rw [coeff_weightedHomogeneousComponent] at hd
    split_ifs at hd with h
    · exact hcol hd
    · exact absurd rfl hd
  · let w' : Option (Fin r × Fin n) → (Fin r → ℕ) := fun o => Option.elim o 0 (rowW r n)
    have key : ∀ F : Fin r × Fin n → MvPolynomial (Option (Fin r × Fin n)) R,
        (∀ v, IsWeightedHomogeneous w' (F v) (rowW r n v)) → ∀ φ : MvPolynomial (Fin r × Fin n) R,
        weightedHomogeneousComponent w' μ (aeval F φ) =
          aeval F (weightedHomogeneousComponent (rowW r n) μ φ) := by
      intro F hF φ
      refine MvPolynomial.induction_on' φ (fun u a => ?_) (fun p q hp hq => ?_)
      · have hm : IsWeightedHomogeneous w' (aeval F (monomial u a)) (Finsupp.weight (rowW r n) u) := by
          rw [aeval_monomial, Finsupp.prod, Finsupp.weight_apply, Finsupp.sum, algebraMap_eq]
          have := (isWeightedHomogeneous_C w' a).mul
            (IsWeightedHomogeneous.prod u.support (fun i => F i ^ u i) (fun i => u i • rowW r n i)
              fun i _ => (hF i).pow (u i))
          rwa [zero_add] at this
        have hm0 : IsWeightedHomogeneous (rowW r n) (monomial u a) (Finsupp.weight (rowW r n) u) :=
          isWeightedHomogeneous_monomial _ _ _ rfl
        rw [weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hm),
          weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hm0)]
        split_ifs <;> simp
      · simp only [map_add, hp, hq]
    let G : Fin r × Fin n → MvPolynomial (Option (Fin r × Fin n)) R := fun v =>
      if v.2 = j then X (some v) + X none * X (some (v.1, l)) else X (some v)
    have hG : ∀ v, IsWeightedHomogeneous w' (G v) (rowW r n v) := by
      intro v
      simp only [G]
      split_ifs
      · refine (isWeightedHomogeneous_X R w' (some v)).add ?_
        have := (isWeightedHomogeneous_X R w' none).mul (isWeightedHomogeneous_X R w' (some (v.1, l)))
        rw [show w' none = 0 from rfl, zero_add] at this
        exact this
      · exact isWeightedHomogeneous_X R w' (some v)
    have hGs : ∀ v, IsWeightedHomogeneous w' ((fun v : Fin r × Fin n =>
        (X (some v) : MvPolynomial (Option (Fin r × Fin n)) R)) v) (rowW r n v) :=
      fun v => isWeightedHomogeneous_X R w' (some v)
    have hA : colAddGen R (r := r) l j = aeval G := rfl
    have hB : (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n))) =
        aeval (fun v : Fin r × Fin n => (X (some v) : MvPolynomial (Option (Fin r × Fin n)) R)) := by
      ext v; simp
    have h1 := hadd l j hlj
    rw [hA, hB] at h1 ⊢
    rw [← key G hG, ← key _ hGs, h1]

end Formalism.GradedWeylDivisibility
