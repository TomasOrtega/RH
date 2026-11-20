import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAddFundamentalDomainLatticeDomain
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped Real ContDiff

namespace GlobalTheory

/- English proof (translation)
Use `haveI : ProperSpace E := FiniteDimensional.proper_real E`. Establish `hd : DiscreteTopology M'.toAddSubgroup` using `hM`. Establish `hcl : IsClosed (M' : Set E)` using `AddSubgroup.isClosed_of_discrete (H := M'.toAddSubgroup)`. Establish `hdis : IsDiscrete (M' : Set E)` using `⟨hM⟩`. Establish `hfin : (K ∩ (M' : Set E)).Finite` using `Metric.finite_isBounded_inter_isClosed hdis hK hcl`.

Use `Set.Finite.of_finite_image (f := Subtype.val) (hfin.subset ?_) Subtype.val_injective.injOn` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `⟨hx, x.2⟩`.
-/
theorem finite_inter_of_discrete_submodule {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (M' : Submodule ℤ E) [hM : DiscreteTopology M']
    {K : Set E} (hK : Bornology.IsBounded K) : {x : M' | (x : E) ∈ K}.Finite := by
  haveI : ProperSpace E := FiniteDimensional.proper_real E
  have hd : DiscreteTopology M'.toAddSubgroup := hM
  have hcl : IsClosed (M' : Set E) := AddSubgroup.isClosed_of_discrete (H := M'.toAddSubgroup)
  have hdis : IsDiscrete (M' : Set E) := ⟨hM⟩
  have hfin : (K ∩ (M' : Set E)).Finite :=
    Metric.finite_isBounded_inter_isClosed hdis hK hcl
  refine Set.Finite.of_finite_image (f := Subtype.val) (hfin.subset ?_) Subtype.val_injective.injOn
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨hx, x.2⟩

/- English proof (translation)
Establish `hfin'` using `finite_inter_of_discrete_submodule M' (latticeDomain_isBounded M)`. Rewrite using `[← Set.finite_univ_iff]`. Use `(hfin'.image (M.submoduleOf M').mkQ).subset ?_` and prove the remaining obligations. Introduce `q _`. Take `⟨x, rfl⟩` from `(M.submoduleOf M').mkQ_surjective q`.

Take `⟨a, ha, -⟩` from `existsUnique_add_mem_latticeDomain M (x : E)`. Set `y : M'` to `x + ⟨(a : E), h a.2⟩`. Establish `hy : (y : E) = (x : E) + a` using `rfl`. Use `⟨y, by rw [Set.mem_setOf_eq, hy]; exact ha, ?_⟩` and prove the remaining obligations. Use `show Submodule.Quotient.mk y = Submodule.Quotient.mk x`.

Rewrite using `[Submodule.Quotient.eq]`. Use `show ((y - x : M') : E) ∈ M`. Establish `: ((y - x : M') : E) = (a : E)`. Rewrite using `[Submodule.coe_sub, hy]`. Normalize the expressions using the abelian group laws.

Rewrite using `[this]`. Conclude with `a.2`.
-/
theorem finite_quotient_submoduleOf_of_isZLattice {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (M M' : Submodule ℤ E) [DiscreteTopology M]
    [IsZLattice ℝ M] [DiscreteTopology M'] (h : M ≤ M') :
    Finite (↥M' ⧸ M.submoduleOf M') := by
  have hfin' := finite_inter_of_discrete_submodule M' (latticeDomain_isBounded M)
  rw [← Set.finite_univ_iff]
  refine (hfin'.image (M.submoduleOf M').mkQ).subset ?_
  intro q _
  obtain ⟨x, rfl⟩ := (M.submoduleOf M').mkQ_surjective q
  obtain ⟨a, ha, -⟩ := existsUnique_add_mem_latticeDomain M (x : E)
  let y : M' := x + ⟨(a : E), h a.2⟩
  have hy : (y : E) = (x : E) + a := rfl
  refine ⟨y, by rw [Set.mem_setOf_eq, hy]; exact ha, ?_⟩
  show Submodule.Quotient.mk y = Submodule.Quotient.mk x
  rw [Submodule.Quotient.eq]
  show ((y - x : M') : E) ∈ M
  have : ((y - x : M') : E) = (a : E) := by
    rw [Submodule.coe_sub, hy]; abel
  rw [this]; exact a.2

/- English proof (translation)
Introduce and unpack `g M M' ⟨_, _⟩ ⟨_, _⟩ h`. Conclude with `finite_quotient_submoduleOf_of_isZLattice M M' h`.
-/
theorem finite_quotient_of_isLat_le :
    ∀ {g : ℕ} (M M' : Submodule ℤ (Fl g)), IsLat M → IsLat M' → M ≤ M' →
      Finite (↥M' ⧸ M.submoduleOf M') := by
  rintro g M M' ⟨_, _⟩ ⟨_, _⟩ h
  exact finite_quotient_submoduleOf_of_isZLattice M M' h

end GlobalTheory
