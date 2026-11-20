import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvFinMkPt

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.FinComm GlobalTheory.VacLine

namespace GlobalTheory.VacLine

/- English proof (translation)
Introduce `F _ _ κ vac hne hcof`. Establish `hS : {v : Pl F | ¬ vac v = indO v}.Finite` using `Filter.eventually_cofinite.mp hcof`. Establish `hz : ∀ v, ∃ z : κ → Fv F v, vac v z ≠ 0` using `fun v => by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Conclude with `hne v (funext h)`. Use `choose z hz using hz`. Use `set S := hS.toFinset with hSdef`. Use `⟨fun i => ∑ v ∈ S, singleFin v (z v i), ?_⟩` and prove the remaining obligations. Establish `hev : ∀ (u : Pl F) (i : κ), evalV F u (∑ v ∈ S, singleFin v (z v i)) = if u ∈ S then z u i else 0`.

Introduce `u i`. Rewrite using `[map_sum]`. Use `split_ifs with hu`. Rewrite using `[Finset.sum_eq_single u]`. Conclude with `GlobalTheory.AdelicU.evalV_singleFin_self u (z u i)`.

Introduce `b _ hb`. Conclude with `GlobalTheory.AdelicU.evalV_singleFin_ne (Ne.symm hb) _`. Introduce `h`. Conclude with `absurd hu h`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `b hb`. Conclude with `GlobalTheory.AdelicU.evalV_singleFin_ne (fun h : u = b => hu (h ▸ hb)) _`. Unfold `vacProd`. Establish `hsub : Function.mulSupport (fun u : Pl F => vac u fun i => evalV F u (∑ v ∈ S, singleFin v (z v i))) ⊆ (S : Set (Pl F))`. Introduce `u hu`.

Assume the negation of the conclusion as `hnot`. Apply `hu` to reduce the goal to its premises. Establish `hmem : u ∉ S` using `hnot`. Establish `hvu : vac u = indO u`. Assume the negation of the conclusion as `h`.

Conclude with `hmem (by rw [hSdef, Set.Finite.mem_toFinset]; exact h)`. Simplify using `only [hev, hmem, if_false]`. Rewrite using `[hvu]`. Simplify using `[indO, Set.indicator, zero_mem]`. Rewrite using `[finprod_eq_prod_of_mulSupport_subset _ hsub, Finset.prod_ne_zero_iff]`.

Introduce `u hu`. Establish `: (fun i => evalV F u (∑ v ∈ S, singleFin v (z v i))) = z u`. Use function extensionality and compare the values at `i`. Rewrite using `[hev, if_pos hu]`. Rewrite using `[this]`.

Conclude with `hz u`.
-/
theorem vacProd_ne_zero_somewhere : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} (vac : ∀ v : Pl F, (κ → Fv F v) → ℂ), (∀ v, vac v ≠ 0) →
    (∀ᶠ v in cofinite, vac v = indO v) → ∃ y : κ → Af F, vacProd vac y ≠ 0 := by
  intro F _ _ κ vac hne hcof
  classical
  have hS : {v : Pl F | ¬ vac v = indO v}.Finite := Filter.eventually_cofinite.mp hcof
  have hz : ∀ v, ∃ z : κ → Fv F v, vac v z ≠ 0 := fun v => by
    by_contra h
    push_neg at h
    exact hne v (funext h)
  choose z hz using hz
  set S := hS.toFinset with hSdef
  refine ⟨fun i => ∑ v ∈ S, singleFin v (z v i), ?_⟩
  have hev : ∀ (u : Pl F) (i : κ), evalV F u (∑ v ∈ S, singleFin v (z v i)) = if u ∈ S then z u i else 0 := by
    intro u i
    rw [map_sum]
    split_ifs with hu
    · rw [Finset.sum_eq_single u]
      · exact GlobalTheory.AdelicU.evalV_singleFin_self u (z u i)
      · intro b _ hb
        exact GlobalTheory.AdelicU.evalV_singleFin_ne (Ne.symm hb) _
      · intro h; exact absurd hu h
    · apply Finset.sum_eq_zero
      intro b hb
      exact GlobalTheory.AdelicU.evalV_singleFin_ne (fun h : u = b => hu (h ▸ hb)) _
  unfold vacProd
  have hsub : Function.mulSupport (fun u : Pl F => vac u fun i => evalV F u (∑ v ∈ S, singleFin v (z v i))) ⊆ (S : Set (Pl F)) := by
    intro u hu
    by_contra hnot
    apply hu
    have hmem : u ∉ S := hnot
    have hvu : vac u = indO u := by
      by_contra h
      exact hmem (by rw [hSdef, Set.Finite.mem_toFinset]; exact h)
    simp only [hev, hmem, if_false]
    rw [hvu]
    simp [indO, Set.indicator, zero_mem]
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub, Finset.prod_ne_zero_iff]
  intro u hu
  have : (fun i => evalV F u (∑ v ∈ S, singleFin v (z v i))) = z u := by
    funext i; rw [hev, if_pos hu]
  rw [this]
  exact hz u

end GlobalTheory.VacLine
