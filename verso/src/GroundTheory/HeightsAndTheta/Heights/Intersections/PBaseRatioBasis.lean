import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StBaseRatioBasis
import GroundTheory.HeightsAndTheta.Heights.Intersections.PWWArithVar
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Assembly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

/- English proof (translation)
Introduce `Ω _ _ ι _ x D hD`. Take `⟨i₀, hi₀⟩` from `hD.2.1.2.2 ()`. Establish `hx : x i₀ ≠ 0`. Introduce `h0`. Apply `hi₀` to reduce the goal to its premises.

Simplify using `[T.baseIdeal, T.multiConeMap, h0]`. Use `set S : Set Ω := Set.range fun j => x j / x i₀ with hS`. Take `⟨u, -, hu⟩` from `exists_maximal_algebraicIndependent (R := ℚ) (∅ : Set Ω) S (Set.empty_subset _) ((algebraicIndependent_empty_iff ℚ Ω).mpr (algebraMap ℚ Ω).injective)`. Establish `huS : u ⊆ S` using `hu.prop.2`. Establish `huI : AlgebraicIndepOn ℚ id u` using `hu.prop.1`.

Establish `hfin : u.Finite` using `(Set.finite_range _).subset huS`. Establish `: Fintype u` using `hfin.fintype`. Use `set d := Fintype.card u`. Set `e : u ≃ Fin d` to `Fintype.equivFin u`. Set `t : Fin d → Ω` to `fun n => (e.symm n : Ω)`.

Establish `hrange : Set.range t = u`. Use extensionality with `a`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, rfl⟩`. Conclude with `(e.symm n).2`.

Introduce `ha`. Conclude with `⟨e ⟨a, ha⟩, by simp [t]⟩`. Establish `ht : AlgebraicIndependent ℚ t` using `huI.comp e.symm e.symm.injective`. Establish `htS : ∀ n, t n ∈ IntermediateField.adjoin ℚ S` using `fun n => IntermediateField.subset_adjoin ℚ S (huS (e.symm n).2)`. Establish `halg : ∀ r ∈ S, IsAlgebraic (IntermediateField.adjoin ℚ (Set.range t)) r`.

Introduce `r hr`. Rewrite using `[hrange]`. Distinguish the cases in `hru : r ∈ u`. Conclude with `isAlgebraic_algebraMap (⟨r, IntermediateField.subset_adjoin ℚ u hru⟩ : IntermediateField.adjoin ℚ u)`. Use `IntermediateField.isAlgebraic_adjoin_iff.mpr ?_` and prove the remaining obligations.

Assume the negation of the conclusion as `hT`. Establish `hins : AlgebraicIndepOn ℚ id (insert r u)` using `(AlgebraicIndepOn.insert_iff hru).mpr ⟨huI, by rw [Set.image_id]; exact hT⟩`. Conclude with `hru (hu.mem_of_prop_insert ⟨hins, Set.insert_subset hr huS⟩)`. Establish `hcone : coneRatios (fun p : (Σ _ : Unit, ι) => x p.2) (fun _ => i₀) = S`. Use extensionality with `a`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨_, j⟩, rfl⟩`. Conclude with `⟨j, rfl⟩`. Introduce and unpack `⟨j, rfl⟩`. Conclude with `⟨⟨(), j⟩, rfl⟩`.

Establish `hA` using `CoordConeArithVar.full Unit (fun _ => ι) Ω (fun p => x p.2) (fun _ => i₀) d t ⟨()⟩ (fun _ => hx) ht (by rw [hcone]; exact htS) (by rw [hcone]; exact halg)`. Rewrite `hA` using `[mCoordIdeal_eq_ker_multiConeMap]`. Establish `hdim` using `hD.2.2.2.symm.trans hA.2.2.2`. Simplify using `only [Fintype.card_unit] at hdim`. Establish `hDd : D + 1 = d + 1 + 1` using `by exact_mod_cast hdim`.

Use `⟨i₀, d, t, hx, by omega, ht, htS, fun j => halg _ ⟨j, rfl⟩⟩` and prove the remaining obligations.
-/
theorem BaseRatioBasis.proof : BaseRatioBasis.Statement := by
  classical
  intro Ω _ _ ι _ x D hD

  obtain ⟨i₀, hi₀⟩ := hD.2.1.2.2 ()
  have hx : x i₀ ≠ 0 := by
    intro h0
    apply hi₀
    simp [T.baseIdeal, T.multiConeMap, h0]

  set S : Set Ω := Set.range fun j => x j / x i₀ with hS
  obtain ⟨u, -, hu⟩ := exists_maximal_algebraicIndependent (R := ℚ) (∅ : Set Ω) S (Set.empty_subset _)
    ((algebraicIndependent_empty_iff ℚ Ω).mpr (algebraMap ℚ Ω).injective)
  have huS : u ⊆ S := hu.prop.2
  have huI : AlgebraicIndepOn ℚ id u := hu.prop.1
  have hfin : u.Finite := (Set.finite_range _).subset huS
  have : Fintype u := hfin.fintype
  set d := Fintype.card u
  let e : u ≃ Fin d := Fintype.equivFin u
  let t : Fin d → Ω := fun n => (e.symm n : Ω)
  have hrange : Set.range t = u := by
    ext a
    constructor
    · rintro ⟨n, rfl⟩
      exact (e.symm n).2
    · intro ha
      exact ⟨e ⟨a, ha⟩, by simp [t]⟩
  have ht : AlgebraicIndependent ℚ t := huI.comp e.symm e.symm.injective
  have htS : ∀ n, t n ∈ IntermediateField.adjoin ℚ S := fun n =>
    IntermediateField.subset_adjoin ℚ S (huS (e.symm n).2)
  have halg : ∀ r ∈ S, IsAlgebraic (IntermediateField.adjoin ℚ (Set.range t)) r := by
    intro r hr
    rw [hrange]
    by_cases hru : r ∈ u
    · exact isAlgebraic_algebraMap
        (⟨r, IntermediateField.subset_adjoin ℚ u hru⟩ : IntermediateField.adjoin ℚ u)
    · refine IntermediateField.isAlgebraic_adjoin_iff.mpr ?_
      by_contra hT
      have hins : AlgebraicIndepOn ℚ id (insert r u) :=
        (AlgebraicIndepOn.insert_iff hru).mpr ⟨huI, by rw [Set.image_id]; exact hT⟩
      exact hru (hu.mem_of_prop_insert ⟨hins, Set.insert_subset hr huS⟩)

  have hcone : coneRatios (fun p : (Σ _ : Unit, ι) => x p.2) (fun _ => i₀) = S := by
    ext a
    constructor
    · rintro ⟨⟨_, j⟩, rfl⟩
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨⟨(), j⟩, rfl⟩
  have hA := CoordConeArithVar.full Unit (fun _ => ι) Ω (fun p => x p.2) (fun _ => i₀) d t ⟨()⟩
    (fun _ => hx) ht (by rw [hcone]; exact htS) (by rw [hcone]; exact halg)
  rw [mCoordIdeal_eq_ker_multiConeMap] at hA
  have hdim := hD.2.2.2.symm.trans hA.2.2.2
  simp only [Fintype.card_unit] at hdim
  have hDd : D + 1 = d + 1 + 1 := by exact_mod_cast hdim
  refine ⟨i₀, d, t, hx, by omega, ht, htS, fun j => halg _ ⟨j, rfl⟩⟩

end

end GroundTheory.Heights₂.Heights.Inter
