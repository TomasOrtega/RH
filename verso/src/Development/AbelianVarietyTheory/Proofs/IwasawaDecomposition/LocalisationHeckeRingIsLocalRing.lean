import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.HeckeLocN.TLocal

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

A detailed English derivation is pending.
-/
theorem isLocalRing_of_congr {O X : Type} [CommRing O] [IsLocalRing O] [Finite X] [Nonempty X] (T : Subalgebra O (X → O))
    (h : ∀ f ∈ T, ∀ x y, f x - f y ∈ IsLocalRing.maximalIdeal O) : IsLocalRing T := by
  obtain ⟨x⟩ := ‹Nonempty X›
  have key : ∀ f : T, IsUnit ((f : X → O) x) → IsUnit f := by
    intro f hx
    have : Algebra.IsIntegral T (X → O) := Algebra.IsIntegral.tower_top O
    have hu : IsUnit (algebraMap T (X → O) f) := by
      refine Pi.isUnit_iff.2 fun y => ?_
      by_contra hy
      have h1 := add_mem (h f f.2 x y) ((IsLocalRing.mem_maximalIdeal _).2 hy)
      exact (IsLocalRing.mem_maximalIdeal _).1 (by simpa using h1) hx
    have hl := RingHom.IsIntegral.isLocalHom (f := algebraMap T (X → O))
      (fun g => Algebra.IsIntegral.isIntegral g) Subtype.val_injective
    exact hl.map_nonunit f hu
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun f => ?_
  exact (IsLocalRing.isUnit_or_isUnit_one_sub_self ((f : X → O) x)).imp (key f) (key (1 - f))

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Simplify to obtain the desired conclusion from the available facts.
-/
theorem sub_mem_of_ker_eq {O A : Type} [CommRing O] [IsLocalRing O] [Ring A] [Algebra O A] (ψ φ : A →ₐ[O] O)
    (h : RingHom.ker ((IsLocalRing.residue O).comp ψ.toRingHom) = RingHom.ker ((IsLocalRing.residue O).comp φ.toRingHom))
    (a : A) : ψ a - φ a ∈ IsLocalRing.maximalIdeal O := by
  have h1 : a - algebraMap O A (φ a) ∈ RingHom.ker ((IsLocalRing.residue O).comp φ.toRingHom) := by
    rw [RingHom.mem_ker]; simp
  rw [← h, RingHom.mem_ker] at h1
  rw [← IsLocalRing.residue_eq_zero_iff]
  simpa using h1

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Treat this case separately. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem main : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (B : LocBase0 H what₂) (hs : HeckeStd0 B) (hd : FinDimV B)
    (i : LocT B), IsLocalRing (TOf B i) := by
  intro R H what₂ B hs hd i
  have := xFin_of hs hd i
  have := xNe_of hs hd i
  refine isLocalRing_of_congr (TOf B i) fun f hf x y => ?_
  rw [← Ideal.Quotient.eq]
  unfold TOf at hf
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨v, k, hvk, rfl⟩ := hf
    refine Ideal.Quotient.eq.2 ?_
    simp only [hTfun, dif_pos hvk]
    exact sub_mem_of_ker_eq x.1 y.1 (x.2.1.trans y.2.1.symm) _
  | algebraMap r => rfl
  | add f g _ _ hf hg => simp only [Pi.add_apply, map_add, hf, hg]
  | mul f g _ _ hf hg => simp only [Pi.mul_apply, map_mul, hf, hg]

end GlobalTheory.HeckeLocN.TLocal
