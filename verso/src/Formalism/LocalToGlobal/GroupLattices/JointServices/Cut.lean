import Formalism.LocalToGlobal.GroupLattices.JointServices

open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV

noncomputable section

namespace Formalism.L2.G.ServJoint

/- English proof (translation)
Simplify using `only [Rows.OLat.carrier, Set.mem_setOf_eq] at h ⊢`. Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => exact ⟨0, by simp⟩`. Consider the case `@insert a S ha ih`. Rewrite using `[Finset.sum_insert ha]`.

Take `⟨c1, hc1⟩` from `h a (Finset.mem_insert_self a S)`. Take `⟨c2, hc2⟩` from `ih (fun i hi => h i (Finset.mem_insert_of_mem hi))`. Use `⟨c1 + c2, ?_⟩` and prove the remaining obligations. Rewrite using `[hc1, hc2, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun w _ => ?_)` and prove the remaining obligations.

Simplify using `[add_smul]`.
-/
theorem carrier_sum {O : Type} [CommRing O] {φ : O →+* ℂ} {V : Type} [AddCommGroup V] [Module ℂ V] (M : Rows.OLat O φ V)
    {ι : Type} (S : Finset ι) (f : ι → V) (h : ∀ i ∈ S, f i ∈ M.carrier) : ∑ i ∈ S, f i ∈ M.carrier := by
  classical
  simp only [Rows.OLat.carrier, Set.mem_setOf_eq] at h ⊢
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha]
    obtain ⟨c1, hc1⟩ := h a (Finset.mem_insert_self a S)
    obtain ⟨c2, hc2⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine ⟨c1 + c2, ?_⟩
    rw [hc1, hc2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    simp [add_smul]

/- English proof (translation)
Simplify using `only [Rows.OLat.carrier, Set.mem_setOf_eq]`. Use `⟨fun w => if w = v then 1 else 0, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single v (fun b _ hb => by simp [hb]) (fun h => absurd hv h)]`. Simplify using the standard rewrite rules.
-/
theorem gen_mem_carrier {O : Type} [CommRing O] {φ : O →+* ℂ} {V : Type} [AddCommGroup V] [Module ℂ V] (M : Rows.OLat O φ V)
    {v : V} (hv : v ∈ M.gen) : v ∈ M.carrier := by
  classical
  simp only [Rows.OLat.carrier, Set.mem_setOf_eq]
  refine ⟨fun w => if w = v then 1 else 0, ?_⟩
  rw [Finset.sum_eq_single v (fun b _ hb => by simp [hb]) (fun h => absurd hv h)]
  simp

/- English proof (translation)
Unfold `CutUp`. Introduce and unpack `x ⟨c, hc⟩ hx0`. Establish `hxM : x ∈ (D.what₂.Mtilde μ).carrier`. Rewrite using `[hc]`. Conclude with `carrier_sum _ _ _ (fun w hw => h (c w) w (gen_mem_carrier _ hw))`.

Use `⟨{x}, fun _ => 1, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.coe_singleton, Set.singleton_subset_iff]`. Conclude with `Set.mem_inter hxM hx0`. Simplify using the standard rewrite rules.
-/
theorem cutUp_of_stable (D : D7) (μ : D.what₂.Tup)
    (h : ∀ (a : 𝓞 D.what₂.LL), ∀ x ∈ (D.what₂.Mtilde μ).carrier, D.what₂.embLL (a : D.what₂.LL) • x ∈ (D.what₂.Mtilde μ).carrier) :
    CutUp D μ := by
  classical
  unfold CutUp
  rintro x ⟨c, hc⟩ hx0
  have hxM : x ∈ (D.what₂.Mtilde μ).carrier := by
    rw [hc]
    exact carrier_sum _ _ _ (fun w hw => h (c w) w (gen_mem_carrier _ hw))
  refine ⟨{x}, fun _ => 1, ?_, ?_⟩
  · rw [Finset.coe_singleton, Set.singleton_subset_iff]
    exact Set.mem_inter hxM hx0
  · simp

end Formalism.L2.G.ServJoint

end
