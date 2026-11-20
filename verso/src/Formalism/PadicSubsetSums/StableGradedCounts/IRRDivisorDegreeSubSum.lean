import Formalism.PadicSubsetSums.CentralIdempotents.GaloisIrreducibility
import Lemmata.GeneralBFactRightRest.Imports

open Polynomial UniqueFactorizationMonoid

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

open Formalism.GaloisIrreducibility (IsSubSum)

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.general_b_fact_right_rest.goal1 .. | (apply Bl.general_b_fact_right_rest.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right_rest.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_rest.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_rig …`.
-/
theorem exists_le_map_eq {α β : Type*} [DecidableEq β] (f : α → β) (t : Multiset α) :
    ∀ s : Multiset β, s ≤ t.map f → ∃ u ≤ t, u.map f = s := by
  first | exact Bl.general_b_fact_right_rest.goal1 .. | (apply Bl.general_b_fact_right_rest.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right_rest.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_rest.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_right_rest.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_rest.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_right_rest.goal1 α β ‹_› f t s ‹_› | exact @Bl.general_b_fact_right_rest.goal1 α β ‹_› f t s | exact @Bl.general_b_fact_right_rest.goal1 α β ‹_› f t | exact @Bl.general_b_fact_right_rest.goal1 α β ‹_› f | exact @Bl.general_b_fact_right_rest.goal1 α β ‹_› | exact @Bl.general_b_fact_right_rest.goal1 α β | exact @Bl.general_b_fact_right_rest.goal1 α

/- English proof (translation)
Introduce `K _ f a hf`. Establish `hdeg : ∀ t : Multiset K[X], t ≤ normalizedFactors f → t.prod.natDegree = (t.map natDegree).sum`. Introduce `t ht`. Apply `natDegree_multiset_prod` to reduce the goal to its premises. Introduce `h0`.

Conclude with `zero_notMem_normalizedFactors f (Multiset.mem_of_le ht h0)`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, hdvd, rfl⟩`. Establish `hh : h ≠ 0` using `fun h0 => hf (by rw [h0] at hdvd; exact zero_dvd_iff.mp hdvd)`. Establish `hle : normalizedFactors h ≤ normalizedFactors f` using `(dvd_iff_normalizedFactors_le_normalizedFactors hh hf).mp hdvd`.

Use `⟨(normalizedFactors h).map natDegree, Multiset.map_le_map hle, ?_⟩` and prove the remaining obligations. Rewrite using `[← hdeg _ hle]`. Conclude with `natDegree_eq_of_degree_eq (degree_eq_degree_of_associated (prod_normalizedFactors hh))`. Introduce and unpack `⟨s, hs, rfl⟩`. Take `⟨u, hu, rfl⟩` from `exists_le_map_eq natDegree _ s hs`.

Use `⟨u.prod, ?_, hdeg u hu⟩` and prove the remaining obligations. Conclude with `(Multiset.prod_dvd_prod_of_le hu).trans (prod_normalizedFactors hf).dvd`.
-/
theorem divisor_degree_subsum : DivisorDegreeSubSum := by
  classical
  intro K _ f a hf
  have hdeg : ∀ t : Multiset K[X], t ≤ normalizedFactors f →
      t.prod.natDegree = (t.map natDegree).sum := by
    intro t ht
    apply natDegree_multiset_prod
    intro h0
    exact zero_notMem_normalizedFactors f (Multiset.mem_of_le ht h0)
  constructor
  · rintro ⟨h, hdvd, rfl⟩
    have hh : h ≠ 0 := fun h0 => hf (by rw [h0] at hdvd; exact zero_dvd_iff.mp hdvd)
    have hle : normalizedFactors h ≤ normalizedFactors f :=
      (dvd_iff_normalizedFactors_le_normalizedFactors hh hf).mp hdvd
    refine ⟨(normalizedFactors h).map natDegree, Multiset.map_le_map hle, ?_⟩
    rw [← hdeg _ hle]
    exact natDegree_eq_of_degree_eq (degree_eq_degree_of_associated (prod_normalizedFactors hh))
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨u, hu, rfl⟩ := exists_le_map_eq natDegree _ s hs
    refine ⟨u.prod, ?_, hdeg u hu⟩
    exact (Multiset.prod_dvd_prod_of_le hu).trans (prod_normalizedFactors hf).dvd

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
