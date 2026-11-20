import Mathlib
import Formalism.PeriodIntegrals.LocJacTyp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.KitShear

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv
attribute [local instance] Sd.finDim

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => h (), fun h _ => h⟩`.
-/
theorem unit_forall {P : Unit → Prop} : (∀ i, P i) ↔ P () := ⟨fun h => h (), fun h _ => h⟩

/- English proof (translation)
Introduce `g r T T' m hS hg hT μ hμ hm l`. Take `⟨D⟩` from `exists_SD hS`. Establish `hp0 : ∀ s t, D.p 0 (D.pt s t) = s` using `fun s t => (D.p_pt s t).1`. Establish `hp1 : ∀ s t, D.p 1 (D.pt s t) = t` using `fun s t => (D.p_pt s t).2`. Establish `hg0 : (g : Fv F v) ≠ 0` using `natCast_ne_zero v hg`.

Establish `hgO : (g : Fv F v) ∈ v.adicCompletionIntegers F` using `natCast_mem _ g`. Establish `hsh : ∀ X : Set (Unit → Fv F v ⊗[F] E), μ ((D.shear id) ⁻¹' X) = μ X` using `haar_shear μ (D.shear id) (Obox (E := E) v Unit) (obox_compact Unit) (obox_open Unit) (obox_nonempty Unit) (D.shear_box id)`. Distinguish the cases in `hl : (l : ℕ) < r`. Establish `ha : alp v r l ^ 2 ≠ 0` using `pow_ne_zero _ (alp_ne_zero v r l)`. Establish `hset : (fun c : Unit → Fv F v ⊗[F] E => c ()) ⁻¹' PPTyp σ v g r T T' l = (D.shear id) ⁻¹' (Set.univ.pi fun _ : Unit => {c | D.pt (alp v r l ^ 2 * ((g : Fv F v)⁻¹) ^ 2) (alp v r l ^ 2 * (g : Fv F v)⁻¹) * c ∈ OEv (E` using `E) v}) := by`.

Use extensionality with `c`. Simplify using `only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq, PPTyp, if_pos hl, unit_forall]`. Rewrite using `[D.mem_sc_mul, D.mem_sc_mul, D.mem_pt_mul, D.shear_first_coordinate, D.shear_second_coordinate]`. Simplify using `only [map_add, (D.p_sig _).1, (D.p_sig _).2, id]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨_, h2⟩, h3, _⟩`. Conclude with `⟨h3, h2⟩`. Introduce and unpack `⟨h3, h2⟩`. Use `⟨⟨?_, h2⟩, h3, ?_⟩` and prove the remaining obligations. Establish `e1 : alp v r l ^ 2 * (g : Fv F v)⁻¹ * D.p 0 (c ()) = (g : Fv F v) * (alp v r l ^ 2 * ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()))) - alp v r l ^ 2 * (g : Fv F v)⁻¹ * D.p 1 (c ())`.

Apply the tactic sequence `field_simp <;> ring`. Rewrite using `[e1]`. Conclude with `sub_mem (mul_mem hgO h3) h2`. Rewrite using `[add_comm (D.p 1 (c ()))]` and apply the resulting hypothesis. Establish `hu : ∀ _ : Unit, IsUnit (D.pt (alp v r l ^ 2 * ((g : Fv F v)⁻¹) ^ 2) (alp v r l ^ 2 * (g : Fv F v)⁻¹))` using `fun _ => D.isUnit_pt (mul_ne_zero ha (pow_ne_zero _ (inv_ne_zero hg0))) (mul_ne_zero ha (inv_ne_zero hg0))`.

Rewrite using `[hset, hsh, BM.box_measure_mul (E := E) v Unit μ _ hu, hm]`. Simplify using `only [Finset.univ_unique, Finset.prod_singleton, D.norm_pt]`. Rewrite using `[absV_mul, absV_mul, absV_mul, absV_pow, absV_pow, absV_inv]`. Establish `hA` using `absV_pos v (alp_ne_zero v r l)`. Establish `hG` using `absV_pos v hg0`.

Clear the denominators using the available nonvanishing facts. Establish `hlr : alp v r l = 1` using `by unfold alp; rw [if_neg hl]`. Take `⟨k, hk⟩` from `hT`. Establish `hk' : ((T : Fv F v) - (T' : Fv F v)) = (g : Fv F v) * (k : Fv F v)`. Use `congrArg (Int.cast : ℤ → Fv F v) hk` as an intermediate fact.

Move the coercions through the operations in `at this`. Conclude with `this`. Establish `hset : (fun c : Unit → Fv F v ⊗[F] E => c ()) ⁻¹' PPTyp σ v g r T T' l = (D.shear id) ⁻¹' ((fun w => w + fun _ : Unit => D.pt ((T : Fv F v) + T') (T : Fv F v)) ⁻¹' (Set.univ.pi fun _ : Unit => {c | D.pt (((g : Fv F v)⁻¹) ^ 2) (g : Fv F v)⁻¹ * c ∈ OEv (E` using `E) v})) := by`. Use extensionality with `c`. Simplify using `only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq, PPTyp, if_neg hl, unit_forall, Pi.add_apply]`.

Rewrite using `[D.mem_sc_mul, D.mem_sc_mul, D.mem_pt_mul]`. Simplify using `only [map_add, D.shear_first_coordinate, D.shear_second_coordinate, hp0, hp1, map_natCast, (D.p_sig _).1, (D.p_sig _).2, id]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨_, h2⟩, h3, _⟩`. Use `⟨?_, h2⟩` and prove the remaining obligations.

Establish `e1 : ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + ((T : Fv F v) + T')) = ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + T + T')` using `by ring`. Rewrite using `[e1]`. Conclude with `h3`. Introduce and unpack `⟨h3, h2⟩`. Establish `e0 : ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + T + T') = ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + ((T : Fv F v) + T'))` using `by ring`.

Use `⟨⟨?_, h2⟩, by rw [e0]; exact h3, ?_⟩` and prove the remaining obligations. Establish `e1 : (g : Fv F v)⁻¹ * (D.p 0 (c ()) + T) = (g : Fv F v) * (((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + ((T : Fv F v) + T'))) - (g : Fv F v)⁻¹ * (D.p 1 (c ()) + T) + (g : Fv F v)⁻¹ * ((T : Fv F v) - T')`. Apply the tactic sequence `field_simp <;> ring`. Establish `e2 : (g : Fv F v)⁻¹ * ((T : Fv F v) - T') = (k : Fv F v)`. Rewrite using `[hk']`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[e1, e2]`. Conclude with `add_mem (sub_mem (mul_mem hgO h3) h2) (intCast_mem _ k)`. Establish `e2 : ((g : Fv F v)⁻¹) ^ 2 * (D.p 1 (c ()) + D.p 0 (c ()) + T + T') = ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + ((T : Fv F v) + T'))` using `by ring`. Rewrite using `[e2]`.

Conclude with `h3`. Establish `hu : ∀ _ : Unit, IsUnit (D.pt (((g : Fv F v)⁻¹) ^ 2) (g : Fv F v)⁻¹)` using `fun _ => D.isUnit_pt (pow_ne_zero _ (inv_ne_zero hg0)) (inv_ne_zero hg0)`. Rewrite using `[hset, hsh, measure_preimage_add_right, BM.box_measure_mul (E := E) v Unit μ _ hu, hm]`. Simplify using `only [Finset.univ_unique, Finset.prod_singleton, D.norm_pt, hlr, absV_one]`. Rewrite using `[absV_mul, absV_pow, absV_inv]`.

Establish `hG` using `absV_pos v hg0`. Clear the denominators using the available nonvanishing facts.
-/
theorem parabolic_volume : VolPP σ v := by
  intro g r T T' m hS hg hT μ hμ hm l
  obtain ⟨D⟩ := exists_SD hS
  have hp0 : ∀ s t, D.p 0 (D.pt s t) = s := fun s t => (D.p_pt s t).1
  have hp1 : ∀ s t, D.p 1 (D.pt s t) = t := fun s t => (D.p_pt s t).2
  have hg0 : (g : Fv F v) ≠ 0 := natCast_ne_zero v hg
  have hgO : (g : Fv F v) ∈ v.adicCompletionIntegers F := natCast_mem _ g
  have hsh : ∀ X : Set (Unit → Fv F v ⊗[F] E), μ ((D.shear id) ⁻¹' X) = μ X :=
    haar_shear μ (D.shear id) (Obox (E := E) v Unit) (obox_compact Unit) (obox_open Unit)
      (obox_nonempty Unit) (D.shear_box id)
  by_cases hl : (l : ℕ) < r
  · have ha : alp v r l ^ 2 ≠ 0 := pow_ne_zero _ (alp_ne_zero v r l)
    have hset : (fun c : Unit → Fv F v ⊗[F] E => c ()) ⁻¹' PPTyp σ v g r T T' l =
        (D.shear id) ⁻¹' (Set.univ.pi fun _ : Unit =>
          {c | D.pt (alp v r l ^ 2 * ((g : Fv F v)⁻¹) ^ 2) (alp v r l ^ 2 * (g : Fv F v)⁻¹) * c ∈
            OEv (E := E) v}) := by
      ext c
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq, PPTyp,
        if_pos hl, unit_forall]
      rw [D.mem_sc_mul, D.mem_sc_mul, D.mem_pt_mul, D.shear_first_coordinate, D.shear_second_coordinate]
      simp only [map_add, (D.p_sig _).1, (D.p_sig _).2, id]
      constructor
      · rintro ⟨⟨_, h2⟩, h3, _⟩
        exact ⟨h3, h2⟩
      · rintro ⟨h3, h2⟩
        refine ⟨⟨?_, h2⟩, h3, ?_⟩
        · have e1 : alp v r l ^ 2 * (g : Fv F v)⁻¹ * D.p 0 (c ()) =
              (g : Fv F v) * (alp v r l ^ 2 * ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()))) -
                alp v r l ^ 2 * (g : Fv F v)⁻¹ * D.p 1 (c ()) := by
            field_simp <;> ring
          rw [e1]
          exact sub_mem (mul_mem hgO h3) h2
        · rwa [add_comm (D.p 1 (c ()))]
    have hu : ∀ _ : Unit, IsUnit (D.pt (alp v r l ^ 2 * ((g : Fv F v)⁻¹) ^ 2) (alp v r l ^ 2 * (g : Fv F v)⁻¹)) :=
      fun _ => D.isUnit_pt (mul_ne_zero ha (pow_ne_zero _ (inv_ne_zero hg0))) (mul_ne_zero ha (inv_ne_zero hg0))
    rw [hset, hsh, BM.box_measure_mul (E := E) v Unit μ _ hu, hm]
    simp only [Finset.univ_unique, Finset.prod_singleton, D.norm_pt]
    rw [absV_mul, absV_mul, absV_mul, absV_pow, absV_pow, absV_inv]
    have hA := absV_pos v (alp_ne_zero v r l)
    have hG := absV_pos v hg0
    field_simp
  · have hlr : alp v r l = 1 := by unfold alp; rw [if_neg hl]
    obtain ⟨k, hk⟩ := hT
    have hk' : ((T : Fv F v) - (T' : Fv F v)) = (g : Fv F v) * (k : Fv F v) := by
      have := congrArg (Int.cast : ℤ → Fv F v) hk
      push_cast at this
      exact this
    have hset : (fun c : Unit → Fv F v ⊗[F] E => c ()) ⁻¹' PPTyp σ v g r T T' l =
        (D.shear id) ⁻¹' ((fun w => w + fun _ : Unit => D.pt ((T : Fv F v) + T') (T : Fv F v)) ⁻¹'
          (Set.univ.pi fun _ : Unit =>
            {c | D.pt (((g : Fv F v)⁻¹) ^ 2) (g : Fv F v)⁻¹ * c ∈ OEv (E := E) v})) := by
      ext c
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq, PPTyp,
        if_neg hl, unit_forall, Pi.add_apply]
      rw [D.mem_sc_mul, D.mem_sc_mul, D.mem_pt_mul]
      simp only [map_add, D.shear_first_coordinate, D.shear_second_coordinate, hp0, hp1, map_natCast, (D.p_sig _).1, (D.p_sig _).2, id]
      constructor
      · rintro ⟨⟨_, h2⟩, h3, _⟩
        refine ⟨?_, h2⟩
        have e1 : ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + ((T : Fv F v) + T')) =
            ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + T + T') := by ring
        rw [e1]; exact h3
      · rintro ⟨h3, h2⟩
        have e0 : ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + T + T') =
            ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + ((T : Fv F v) + T')) := by ring
        refine ⟨⟨?_, h2⟩, by rw [e0]; exact h3, ?_⟩
        · have e1 : (g : Fv F v)⁻¹ * (D.p 0 (c ()) + T) =
              (g : Fv F v) * (((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + ((T : Fv F v) + T'))) -
                (g : Fv F v)⁻¹ * (D.p 1 (c ()) + T) + (g : Fv F v)⁻¹ * ((T : Fv F v) - T') := by
            field_simp <;> ring
          have e2 : (g : Fv F v)⁻¹ * ((T : Fv F v) - T') = (k : Fv F v) := by
            rw [hk']; field_simp
          rw [e1, e2]
          exact add_mem (sub_mem (mul_mem hgO h3) h2) (intCast_mem _ k)
        · have e2 : ((g : Fv F v)⁻¹) ^ 2 * (D.p 1 (c ()) + D.p 0 (c ()) + T + T') =
              ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + ((T : Fv F v) + T')) := by ring
          rw [e2]; exact h3
    have hu : ∀ _ : Unit, IsUnit (D.pt (((g : Fv F v)⁻¹) ^ 2) (g : Fv F v)⁻¹) :=
      fun _ => D.isUnit_pt (pow_ne_zero _ (inv_ne_zero hg0)) (inv_ne_zero hg0)
    rw [hset, hsh, measure_preimage_add_right, BM.box_measure_mul (E := E) v Unit μ _ hu, hm]
    simp only [Finset.univ_unique, Finset.prod_singleton, D.norm_pt, hlr, absV_one]
    rw [absV_mul, absV_pow, absV_inv]
    have hG := absV_pos v hg0
    field_simp

end PI.UnitaryGroupMassFormula.LocJacTyp
