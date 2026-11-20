import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

/- English proof (translation)
Introduce `R _ F U ι V j hE hS`. Establish `hcov : Sieve.generate (Presieve.ofArrows V j) ∈ Scheme.etaleTopology U`. Apply `Precoverage.generate_mem_toGrothendieck` to reduce the goal to its premises. Use `(Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).2 ⟨fun u => ?_, hE⟩` and prove the remaining obligations. Take `⟨i, v, hv⟩` from `hS u`.

Conclude with `⟨i, v, hv⟩`. Establish `hF : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R)))`. Rewrite using `[← isSheaf_iff_isSheaf_of_type]`. Conclude with `(Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).1 F.cond`. Establish `hfor` using `(Presieve.isSheafFor_iff_generate _).2 (hF _ hcov)`.

Rewrite `hfor` using `[Presieve.isSheafFor_arrows_iff_pullbacks]`. Use `⟨fun x hx => ?_, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨t, -, ht⟩` from `hfor (fun _ => 0) (fun i k => by`. Express the relevant statement in the definitionally equal form `(F.obj.map (pullback.fst (j i) (j k)).op).hom 0 = (F.obj.map (pullback.snd (j i) (j k)).op).hom 0`. Rewrite using `[map_zero, map_zero])`.

Establish `h0 : (0 : Sec F U) = t` using `ht 0 (fun i => by`. Express the relevant statement in the definitionally equal form `(F.obj.map (j i).op).hom 0 = 0`. Conclude with `map_zero _)`. Conclude with `(ht x hx).trans h0.symm`. Take `⟨t, ht, -⟩` from `hfor y hy`.

Conclude with `⟨t, ht⟩`.
-/
theorem sec_sep_glue_of_points : ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}) (ι : Type) (V : ι → Scheme.{0}) (j : ∀ i, V i ⟶ U), (∀ i, Etale (j i)) → (∀ u : U, ∃ i v, j i v = u) → (∀ x : Sec F U, (∀ i, Sec.res (j i) x = 0) → x = 0) ∧ ∀ y : ∀ i, Sec F (V i), (∀ i k, Sec.res (pullback.fst (j i) (j k)) (y i) = Sec.res (pullback.snd (j i) (j k)) (y k)) → ∃ x : Sec F U, ∀ i, Sec.res (j i) x = y i := by
  intro R _ F U ι V j hE hS
  have hcov : Sieve.generate (Presieve.ofArrows V j) ∈ Scheme.etaleTopology U := by
    apply Precoverage.generate_mem_toGrothendieck
    refine (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).2 ⟨fun u => ?_, hE⟩
    obtain ⟨i, v, hv⟩ := hS u
    exact ⟨i, v, hv⟩
  have hF : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) := by
    rw [← isSheaf_iff_isSheaf_of_type]
    exact (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).1 F.cond
  have hfor := (Presieve.isSheafFor_iff_generate _).2 (hF _ hcov)
  rw [Presieve.isSheafFor_arrows_iff_pullbacks] at hfor
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · obtain ⟨t, -, ht⟩ := hfor (fun _ => 0) (fun i k => by
      change (F.obj.map (pullback.fst (j i) (j k)).op).hom 0 = (F.obj.map (pullback.snd (j i) (j k)).op).hom 0
      rw [map_zero, map_zero])
    have h0 : (0 : Sec F U) = t := ht 0 (fun i => by
      change (F.obj.map (j i).op).hom 0 = 0
      exact map_zero _)
    exact (ht x hx).trans h0.symm
  · obtain ⟨t, ht, -⟩ := hfor y hy
    exact ⟨t, ht⟩

end GlobalTheory.EtC
