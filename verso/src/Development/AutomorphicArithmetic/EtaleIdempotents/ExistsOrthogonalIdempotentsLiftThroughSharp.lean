import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CrystallineComparison
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.TestFactsAlt
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SplitsOfSplitOn
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PSecChart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PPtChart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PMatchVal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PSnBasic
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Introduce `l _ A I _ e he`. Establish `hu : ∀ x : A.obj.U, IsIdempotentElem x → ∃! x₀ : A.obj.A, IsIdempotentElem x₀ ∧ A.obj.sharp x₀ = x` using `(testFacts l A.obj A.property).2.2.2.2`. Establish `s1 : A.obj.sharp 1 = 1` using `map_one _`. Establish `hsub : ∀ a : A.obj.A, IsIdempotentElem a → A.obj.sharp (1 - a) = 1 - A.obj.sharp a` using `(CrystallineSemistableComparison.RL.sharp_cong A.obj).2.2`. Establish `s0 : A.obj.sharp 0 = 0`.

Use `hsub 1 IsIdempotentElem.one` as an intermediate fact. Simplify `this` using `[s1]`. Establish `h` using `fun i => (hu (e i) (he.toOrthogonalIdempotents.idem i)).exists`. Use `choose e₀ h1 h2 using h`. Establish `hz : ∀ a : A.obj.A, IsIdempotentElem a → A.obj.sharp a = 0 → a = 0` using `fun a ha hs => (hu 0 IsIdempotentElem.zero).unique ⟨ha, hs⟩ ⟨IsIdempotentElem.zero, s0⟩`.

Establish `hort : ∀ i j, i ≠ j → e₀ i * e₀ j = 0` using `fun i j hij => hz _ ((h1 i).mul (h1 j)) (by`. Rewrite using `[map_mul, h2, h2]`. Conclude with `he.toOrthogonalIdempotents.ortho hij)`. Establish `hoi : OrthogonalIdempotents e₀` using `⟨h1, fun i j hij => hort i j hij⟩`. Establish `hprod : ∀ s : Finset I, IsIdempotentElem (1 - ∑ i ∈ s, e₀ i) ∧ ∀ i ∈ s, (1 - ∑ k ∈ s, e₀ k) * e₀ i = 0`.

Introduce `s`. Establish `hmul : ∀ i ∈ s, (∑ k ∈ s, e₀ k) * e₀ i = e₀ i`. Introduce `i hi`. Rewrite using `[Finset.sum_mul, Finset.sum_eq_single_of_mem i hi (fun k _ hk => hort k i hk)]`. Conclude with `h1 i`.

Establish `hsq : (∑ k ∈ s, e₀ k) * (∑ k ∈ s, e₀ k) = ∑ k ∈ s, e₀ k`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl hmul`. Use `⟨?_, fun i hi => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(1 - ∑ k ∈ s, e₀ k) * (1 - ∑ k ∈ s, e₀ k) = _`.

Take the linear combination `hsq`. Rewrite using `[sub_mul, one_mul, hmul i hi, sub_self]`. Take `⟨t1, t2⟩` from `hprod Finset.univ`. Establish `ht : A.obj.sharp (1 - ∑ i, e₀ i) = 0`. Establish `hk : ∀ i, A.obj.sharp (1 - ∑ k, e₀ k) * e i = 0` using `fun i => by`.

Rewrite using `[← h2 i, ← map_mul, t2 i (Finset.mem_univ i), s0]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[he.complete, mul_one]`. Use `_ = 0 := by`. Rewrite using `[Finset.mul_sum]`.

Conclude with `Finset.sum_eq_zero fun i _ => hk i`. Establish `hsum : ∑ i, e₀ i = 1`. Use `hz _ t1 ht` as an intermediate fact. Take the linear combination `-this`. Conclude with `⟨e₀, ⟨hoi, hsum⟩, h2⟩`.
-/
theorem UpperTheory.exists_orthogonalIdempotents_lift_through_sharp :
    ∀ (l : ℕ) [Fact l.Prime] (A : Test l) (I : Type) [Fintype I] (e : I → A.obj.U), CompleteOrthogonalIdempotents e →
        ∃ e₀ : I → A.obj.A, CompleteOrthogonalIdempotents e₀ ∧ ∀ i, A.obj.sharp (e₀ i) = e i := by
  intro l _ A I _ e he
  classical
  have hu : ∀ x : A.obj.U, IsIdempotentElem x → ∃! x₀ : A.obj.A, IsIdempotentElem x₀ ∧ A.obj.sharp x₀ = x :=
    (testFacts l A.obj A.property).2.2.2.2
  have s1 : A.obj.sharp 1 = 1 := map_one _
  have hsub : ∀ a : A.obj.A, IsIdempotentElem a → A.obj.sharp (1 - a) = 1 - A.obj.sharp a :=
    (CrystallineSemistableComparison.RL.sharp_cong A.obj).2.2
  have s0 : A.obj.sharp 0 = 0 := by
    have := hsub 1 IsIdempotentElem.one
    simpa [s1] using this
  have h := fun i => (hu (e i) (he.toOrthogonalIdempotents.idem i)).exists
  choose e₀ h1 h2 using h
  have hz : ∀ a : A.obj.A, IsIdempotentElem a → A.obj.sharp a = 0 → a = 0 := fun a ha hs =>
    (hu 0 IsIdempotentElem.zero).unique ⟨ha, hs⟩ ⟨IsIdempotentElem.zero, s0⟩
  have hort : ∀ i j, i ≠ j → e₀ i * e₀ j = 0 := fun i j hij =>
    hz _ ((h1 i).mul (h1 j)) (by
      rw [map_mul, h2, h2]
      exact he.toOrthogonalIdempotents.ortho hij)
  have hoi : OrthogonalIdempotents e₀ := ⟨h1, fun i j hij => hort i j hij⟩

  have hprod : ∀ s : Finset I, IsIdempotentElem (1 - ∑ i ∈ s, e₀ i) ∧
      ∀ i ∈ s, (1 - ∑ k ∈ s, e₀ k) * e₀ i = 0 := by
    intro s
    have hmul : ∀ i ∈ s, (∑ k ∈ s, e₀ k) * e₀ i = e₀ i := by
      intro i hi
      rw [Finset.sum_mul, Finset.sum_eq_single_of_mem i hi
        (fun k _ hk => hort k i hk)]
      exact h1 i
    have hsq : (∑ k ∈ s, e₀ k) * (∑ k ∈ s, e₀ k) = ∑ k ∈ s, e₀ k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl hmul
    refine ⟨?_, fun i hi => ?_⟩
    · change (1 - ∑ k ∈ s, e₀ k) * (1 - ∑ k ∈ s, e₀ k) = _
      linear_combination hsq
    · rw [sub_mul, one_mul, hmul i hi, sub_self]
  obtain ⟨t1, t2⟩ := hprod Finset.univ
  have ht : A.obj.sharp (1 - ∑ i, e₀ i) = 0 := by
    have hk : ∀ i, A.obj.sharp (1 - ∑ k, e₀ k) * e i = 0 := fun i => by
      rw [← h2 i, ← map_mul, t2 i (Finset.mem_univ i), s0]
    calc A.obj.sharp (1 - ∑ k, e₀ k) = A.obj.sharp (1 - ∑ k, e₀ k) * ∑ i, e i := by
          rw [he.complete, mul_one]
      _ = 0 := by
          rw [Finset.mul_sum]
          exact Finset.sum_eq_zero fun i _ => hk i
  have hsum : ∑ i, e₀ i = 1 := by
    have := hz _ t1 ht
    linear_combination -this
  exact ⟨e₀, ⟨hoi, hsum⟩, h2⟩
