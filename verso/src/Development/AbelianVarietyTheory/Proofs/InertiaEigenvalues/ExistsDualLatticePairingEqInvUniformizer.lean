import Mathlib
import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

noncomputable section

namespace GlobalTheory.LocDualInt

section PerfL

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
  [IsScalarTower O (FractionRing O) V]

/- English proof (translation)
Use `haveI : Module.Finite O T := Module.Finite.iff_fg.2 hT.1`. Use `haveI : Module.IsTorsionFree O T := Module.IsTorsionFree.of_smul_eq_zero fun r m h => by`. Establish `h1 : (algebraMap O (FractionRing O) r) • (m : V) = 0`. Rewrite using `[algebraMap_smul]`. Conclude with `congrArg Subtype.val h`.

Break down `smul_eq_zero.1 h1 with h2 | h2` into its components or cases. Use `left`. Conclude with `(IsFractionRing.injective O (FractionRing O)) (by rw [h2, map_zero])`. Use `right`. Conclude with `Subtype.ext h2`.

Use `haveI : Module.Free O T := Module.free_of_finite_type_torsion_free'`. Set `e` to `Module.Free.chooseBasis O T`. Set `w : Module.Free.ChooseBasisIndex O T → V` to `fun i => (e i : V)`. Establish `hliO : LinearIndependent O w` using `e.linearIndependent.map' T.subtype (Submodule.ker_subtype T)`. Establish `hli : LinearIndependent (FractionRing O) w` using `(LinearIndependent.iff_fractionRing O (FractionRing O)).1 hliO`.

Establish `hspO : Submodule.span O (Set.range w) = T`. Establish `h` using `congrArg (Submodule.map T.subtype) e.span_eq`. Rewrite `h` using `[Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]`. Conclude with `h`. Establish `hsp : ⊤ ≤ Submodule.span (FractionRing O) (Set.range w)`.

Rewrite using `[← hT.2]`. Apply `Submodule.span_le.2` to reduce the goal to its premises. Introduce `t ht`. Rewrite `ht` using `[← hspO]`. Conclude with `Submodule.span_subset_span O (FractionRing O) (Set.range w) ht`.

Set `bK` to `Module.Basis.mk hli hsp`. Establish `hbK : ∀ i, bK i = w i` using `fun i => Module.Basis.mk_apply hli hsp i`. Establish `hint : ∀ t ∈ T, ∀ j, bK.repr t j ∈ (1 : Submodule O (FractionRing O))`. Introduce `t ht`. Rewrite `ht` using `[← hspO]`.

Proceed by induction on `ht using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨i, rfl⟩` from `hx`. Introduce `j`. Rewrite using `[← hbK, bK.repr_self, Finsupp.single_apply]`.

Use `split_ifs`. Conclude with `Submodule.mem_one.2 ⟨1, map_one _⟩`. Conclude with `Submodule.zero_mem _`. Consider the case `zero => intro j`. Simplify using the standard rewrite rules.

Consider the case `add x y _ _ hx hy => intro j`. Rewrite using `[map_add, Finsupp.add_apply]`. Conclude with `Submodule.add_mem _ (hx j) (hy j)`. Consider the case `smul a x _ hx`. Introduce `j`.

Rewrite using `[← algebraMap_smul (FractionRing O) a x, map_smul, Finsupp.smul_apply, algebraMap_smul]`. Conclude with `Submodule.smul_mem _ a (hx j)`. Establish `hex : ∃ j, bK.repr v j ∉ (1 : Submodule O (FractionRing O))`. Assume the negation of the conclusion as `hne`. Use `push Not at hne`.

Apply `hv` to reduce the goal to its premises. Rewrite using `[← bK.linearCombination_repr v, Finsupp.linearCombination_apply, Finsupp.sum]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `Submodule.mem_one.1 (hne j)`. Rewrite using `[← ha, algebraMap_smul, hbK]`.

Conclude with `Submodule.smul_mem _ a (e j).2`. Take `⟨j, hj⟩` from `hex`. Conclude with `⟨bK.coord j, fun t ht => hint t ht j, hj⟩`.
-/
theorem exists_form_of_not_mem {T : Submodule O V} (hT : IsLatticeIn T) {v : V} (hv : v ∉ T) :
    ∃ ψ : V →ₗ[FractionRing O] FractionRing O,
      (∀ t ∈ T, ψ t ∈ (1 : Submodule O (FractionRing O))) ∧
        ψ v ∉ (1 : Submodule O (FractionRing O)) := by
  classical
  haveI : Module.Finite O T := Module.Finite.iff_fg.2 hT.1
  haveI : Module.IsTorsionFree O T := Module.IsTorsionFree.of_smul_eq_zero fun r m h => by
    have h1 : (algebraMap O (FractionRing O) r) • (m : V) = 0 := by
      rw [algebraMap_smul]
      exact congrArg Subtype.val h
    rcases smul_eq_zero.1 h1 with h2 | h2
    · left
      exact (IsFractionRing.injective O (FractionRing O)) (by rw [h2, map_zero])
    · right
      exact Subtype.ext h2
  haveI : Module.Free O T := Module.free_of_finite_type_torsion_free'
  let e := Module.Free.chooseBasis O T
  let w : Module.Free.ChooseBasisIndex O T → V := fun i => (e i : V)
  have hliO : LinearIndependent O w := e.linearIndependent.map' T.subtype (Submodule.ker_subtype T)
  have hli : LinearIndependent (FractionRing O) w :=
    (LinearIndependent.iff_fractionRing O (FractionRing O)).1 hliO
  have hspO : Submodule.span O (Set.range w) = T := by
    have h := congrArg (Submodule.map T.subtype) e.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h
    exact h
  have hsp : ⊤ ≤ Submodule.span (FractionRing O) (Set.range w) := by
    rw [← hT.2]
    apply Submodule.span_le.2
    intro t ht
    rw [← hspO] at ht
    exact Submodule.span_subset_span O (FractionRing O) (Set.range w) ht
  let bK := Module.Basis.mk hli hsp
  have hbK : ∀ i, bK i = w i := fun i => Module.Basis.mk_apply hli hsp i

  have hint : ∀ t ∈ T, ∀ j, bK.repr t j ∈ (1 : Submodule O (FractionRing O)) := by
    intro t ht
    rw [← hspO] at ht
    induction ht using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro j
      rw [← hbK, bK.repr_self, Finsupp.single_apply]
      split_ifs
      · exact Submodule.mem_one.2 ⟨1, map_one _⟩
      · exact Submodule.zero_mem _
    | zero => intro j; simp
    | add x y _ _ hx hy => intro j; rw [map_add, Finsupp.add_apply]; exact Submodule.add_mem _ (hx j) (hy j)
    | smul a x _ hx =>
      intro j
      rw [← algebraMap_smul (FractionRing O) a x, map_smul, Finsupp.smul_apply, algebraMap_smul]
      exact Submodule.smul_mem _ a (hx j)
  have hex : ∃ j, bK.repr v j ∉ (1 : Submodule O (FractionRing O)) := by
    by_contra hne
    push Not at hne
    apply hv
    rw [← bK.linearCombination_repr v, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨a, ha⟩ := Submodule.mem_one.1 (hne j)
    rw [← ha, algebraMap_smul, hbK]
    exact Submodule.smul_mem _ a (e j).2
  obtain ⟨j, hj⟩ := hex
  exact ⟨bK.coord j, fun t ht => hint t ht j, hj⟩

/- English proof (translation)
Establish `hu0 : u ≠ 0` using `fun h => hu (h ▸ Submodule.zero_mem _)`. Break down `ValuationRing.isInteger_or_isInteger O u with h | ⟨w, hw⟩` into its components or cases. Conclude with `absurd (Submodule.mem_one.2 h) hu`. Establish `hwu : ¬ IsUnit w`. Introduce `hw'`.

Apply `hu` to reduce the goal to its premises. Use `Submodule.mem_one.2 ⟨((hw'.unit⁻¹ : Oˣ) : O), ?_⟩` and prove the remaining obligations. Establish `h1 : algebraMap O (FractionRing O) ((hw'.unit⁻¹ : Oˣ) : O) * u⁻¹ = 1`. Rewrite using `[← hw, ← map_mul, IsUnit.val_inv_mul, map_one]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[inv_mul_cancel₀ hu0, mul_one]`. Use `_ = u := by rw [← mul_assoc, h1, one_mul]`. Establish `hwm : w ∈ IsLocalRing.maximalIdeal O` using `hwu`. Rewrite `hwm` using `[hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]`. Take `⟨o, rfl⟩` from `hwm`.

Use `⟨o, ?_⟩` and prove the remaining obligations. Rewrite `hw` using `[map_mul]`. Use `symm`. Apply `inv_eq_of_mul_eq_one_right` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_mul_eq_inv_unif {ϖ : O} (hϖ : Irreducible ϖ) {u : FractionRing O}
    (hu : u ∉ (1 : Submodule O (FractionRing O))) :
    ∃ o : O, algebraMap O (FractionRing O) o * u = (algebraMap O (FractionRing O) ϖ)⁻¹ := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Submodule.zero_mem _)
  rcases ValuationRing.isInteger_or_isInteger O u with h | ⟨w, hw⟩
  · exact absurd (Submodule.mem_one.2 h) hu
  have hwu : ¬ IsUnit w := by
    intro hw'
    apply hu
    refine Submodule.mem_one.2 ⟨((hw'.unit⁻¹ : Oˣ) : O), ?_⟩
    have h1 : algebraMap O (FractionRing O) ((hw'.unit⁻¹ : Oˣ) : O) * u⁻¹ = 1 := by
      rw [← hw, ← map_mul, IsUnit.val_inv_mul, map_one]
    calc algebraMap O (FractionRing O) ((hw'.unit⁻¹ : Oˣ) : O)
        = algebraMap O (FractionRing O) ((hw'.unit⁻¹ : Oˣ) : O) * (u⁻¹ * u) := by
          rw [inv_mul_cancel₀ hu0, mul_one]
      _ = u := by rw [← mul_assoc, h1, one_mul]
  have hwm : w ∈ IsLocalRing.maximalIdeal O := hwu
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hwm
  obtain ⟨o, rfl⟩ := hwm
  refine ⟨o, ?_⟩
  rw [map_mul] at hw
  symm
  apply inv_eq_of_mul_eq_one_right
  calc algebraMap O (FractionRing O) ϖ * (algebraMap O (FractionRing O) o * u)
      = (algebraMap O (FractionRing O) ϖ * algebraMap O (FractionRing O) o) * u := by ring
    _ = 1 := by rw [hw, inv_mul_cancel₀ hu0]

end PerfL

section Main

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
  [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)]
  [ContinuousSMul O (FractionRing O)] {VT VT' : Type} [AddCommGroup VT] [Module O VT]
  [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
  [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT] [AddCommGroup VT']
  [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']
  {G : Type} [Group G] [TopologicalSpace G]

/- English proof (translation)
Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective D.T x`. Establish `hv : v ∉ D.T` using `fun h => hx ((Submodule.Quotient.mk_eq_zero _).2 h)`. Take `⟨ψ, hψT, hψv⟩` from `exists_form_of_not_mem hT hv`. Take `⟨f, hf, -⟩` from `hP ψ`. Establish `hfT : f ∈ D.T'` using `fun t ht => by rw [hf]; exact hψT t ht`.

Take `⟨o, ho⟩` from `exists_mul_eq_inv_unif hϖ (u := D.bT v f) (by rw [hf]; exact hψv)`. Use `⟨⟨o • f, D.T'.smul_mem o hfT⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[pairKO_mk]`. Use `congr 1`. Use `show D.bT v (o • f) = _`.

Rewrite using `[map_smul, Algebra.smul_def, ho]`.
-/
theorem exists_dual_pairKO_eq_inv_unif (D : LatData O G VT VT') (hT : IsLatticeIn D.T)
    (hP : PerfectRight D.bT) (ϖ : O) (hϖ : Irreducible ϖ) (x : VT ⧸ D.T) (hx : x ≠ 0) :
    ∃ f : ↥D.T', pairKO D.bT D.T x f = toKO O ((algebraMap O (FractionRing O) ϖ)⁻¹) := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective D.T x
  have hv : v ∉ D.T := fun h => hx ((Submodule.Quotient.mk_eq_zero _).2 h)
  obtain ⟨ψ, hψT, hψv⟩ := exists_form_of_not_mem hT hv
  obtain ⟨f, hf, -⟩ := hP ψ
  have hfT : f ∈ D.T' := fun t ht => by rw [hf]; exact hψT t ht
  obtain ⟨o, ho⟩ := exists_mul_eq_inv_unif hϖ (u := D.bT v f) (by rw [hf]; exact hψv)
  refine ⟨⟨o • f, D.T'.smul_mem o hfT⟩, ?_⟩
  rw [pairKO_mk]
  congr 1
  show D.bT v (o • f) = _
  rw [map_smul, Algebra.smul_def, ho]

end Main

end GlobalTheory.LocDualInt
