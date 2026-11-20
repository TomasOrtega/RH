import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.HeckeLocN.TLocal

/- English proof (translation)
Take `⟨x⟩` from `‹Nonempty X›`. Establish `key : ∀ f : T, IsUnit ((f : X → O) x) → IsUnit f`. Introduce `f hx`. Establish `: Algebra.IsIntegral T (X → O)` using `Algebra.IsIntegral.tower_top O`. Establish `hu : IsUnit (algebraMap T (X → O) f)`.

Use `Pi.isUnit_iff.2 fun y => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hy`. Establish `h1` using `add_mem (h f f.2 x y) ((IsLocalRing.mem_maximalIdeal _).2 hy)`. Conclude with `(IsLocalRing.mem_maximalIdeal _).1 (by simpa using h1) hx`. Establish `hl` using `RingHom.IsIntegral.isLocalHom (f := algebraMap T (X → O)) (fun g => Algebra.IsIntegral.isIntegral g) Subtype.val_injective`.

Conclude with `hl.map_nonunit f hu`. Use `IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun f => ?_` and prove the remaining obligations. Conclude with `(IsLocalRing.isUnit_or_isUnit_one_sub_self ((f : X → O) x)).imp (key f) (key (1 - f))`.
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
Establish `h1 : a - algebraMap O A (φ a) ∈ RingHom.ker ((IsLocalRing.residue O).comp φ.toRingHom)`. Rewrite using `[RingHom.mem_ker]`. Simplify using the standard rewrite rules. Rewrite `h1` using `[← h, RingHom.mem_ker]`. Rewrite using `[← IsLocalRing.residue_eq_zero_iff]`.

Simplify using `using h1`.
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
Introduce `R H what₂ B hs hd i`. Use `xFin_of hs hd i` as an intermediate fact. Use `xNe_of hs hd i` as an intermediate fact. Use `isLocalRing_of_congr (TOf B i) fun f hf x y => ?_` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq]`.

Unfold `TOf at hf`. Proceed by induction on `hf using Algebra.adjoin_induction with`. Consider the case `mem f hf`. Take `⟨v, k, hvk, rfl⟩` from `hf`. Use `Ideal.Quotient.eq.2 ?_` and prove the remaining obligations.

Simplify using `only [hTfun, dif_pos hvk]`. Conclude with `sub_mem_of_ker_eq x.1 y.1 (x.2.1.trans y.2.1.symm) _`. Consider the case `algebraMap r => rfl`. Consider the case `add f g _ _ hf hg => simp only [Pi.add_apply, map_add, hf, hg]`. Consider the case `mul f g _ _ hf hg => simp only [Pi.mul_apply, map_mul, hf, hg]`.
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
