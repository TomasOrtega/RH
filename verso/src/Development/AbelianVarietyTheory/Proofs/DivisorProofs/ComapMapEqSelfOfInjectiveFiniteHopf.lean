import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointsGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpanEqTopOfFinrankFibreEq

open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup Coalgebra Bialgebra

namespace GlobalTheory.PDiv

/- English proof (translation)
Take `⟨e⟩` from `GlobalTheory.HopfShear.shear k A B f`. Use `haveI : Module.Finite k (AlgHom.range (f : B →ₐ[k] A)) := Module.Finite.of_injective (AlgHom.range (f : B →ₐ[k] A)).val.toLinearMap Subtype.val_injective`. Use `haveI : Module.Finite (AlgHom.range (f : B →ₐ[k] A)) A := Module.Finite.of_restrictScalars_finite k _ A`. Use `haveI : IsArtinianRing (AlgHom.range (f : B →ₐ[k] A)) := IsArtinianRing.of_finite k _`. Take `⟨b⟩` from `GlobalTheory.nonempty_basis_of_basis_baseChange (B := AlgHom.range (f : B →ₐ[k] A)) (A := A) (M := A) Subtype.val_injective (((Module.finBasis k _).baseChange A).map e.symm)`.

Use `haveI := Module.Free.of_basis b`. Use `haveI : Nontrivial A := (counitAlgHom k A).domain_nontrivial`. Use `infer_instance`.
-/
theorem faithfullyFlat_range_of_hopf_finite (k A B : Type) [Field k] [CommRing A] [CommRing B]
    [HopfAlgebra k A] [HopfAlgebra k B] [Module.Finite k A] (f : B →ₐc[k] A) :
    Module.FaithfullyFlat (AlgHom.range (f : B →ₐ[k] A)) A := by
  obtain ⟨e⟩ := GlobalTheory.HopfShear.shear k A B f
  haveI : Module.Finite k (AlgHom.range (f : B →ₐ[k] A)) :=
    Module.Finite.of_injective (AlgHom.range (f : B →ₐ[k] A)).val.toLinearMap
      Subtype.val_injective
  haveI : Module.Finite (AlgHom.range (f : B →ₐ[k] A)) A :=
    Module.Finite.of_restrictScalars_finite k _ A
  haveI : IsArtinianRing (AlgHom.range (f : B →ₐ[k] A)) := IsArtinianRing.of_finite k _
  obtain ⟨b⟩ := GlobalTheory.nonempty_basis_of_basis_baseChange (B := AlgHom.range (f : B →ₐ[k] A))
    (A := A) (M := A) Subtype.val_injective (((Module.finBasis k _).baseChange A).map e.symm)
  haveI := Module.Free.of_basis b
  haveI : Nontrivial A := (counitAlgHom k A).domain_nontrivial
  infer_instance

/- English proof (translation)
Introduce `k A B _ _ _ _ _ _ f hf J`. Use `haveI := faithfullyFlat_range_of_hopf_finite k A B f`. Set `g : B →+* AlgHom.range (f : B →ₐ[k] A)` to `(f : B →ₐ[k] A).rangeRestrict.toRingHom`. Establish `hg : Function.Bijective g` using `⟨fun x y h => hf (congrArg Subtype.val h), (f : B →ₐ[k] A).rangeRestrict_surjective⟩`. Establish `h` using `Ideal.comap_map_eq_self_of_faithfullyFlat (B := A) (Ideal.map g J)`.

Rewrite `h` using `[Ideal.map_map]`. Establish `h2` using `congrArg (Ideal.comap g) h`. Rewrite `h2` using `[Ideal.comap_comap, Ideal.comap_map_of_bijective g hg]`. Conclude with `h2`.
-/
theorem comap_map_eq_self_of_hopf_injective : ∀ (k A B : Type) [Field k] [CommRing A] [CommRing B] [HopfAlgebra k A] [HopfAlgebra k B] [Module.Finite k A] (f : B →ₐc[k] A), Function.Injective f → ∀ J : Ideal B, Ideal.comap (f : B →ₐ[k] A) (Ideal.map (f : B →ₐ[k] A) J) = J := by
  intro k A B _ _ _ _ _ _ f hf J
  haveI := faithfullyFlat_range_of_hopf_finite k A B f
  let g : B →+* AlgHom.range (f : B →ₐ[k] A) := (f : B →ₐ[k] A).rangeRestrict.toRingHom
  have hg : Function.Bijective g :=
    ⟨fun x y h => hf (congrArg Subtype.val h), (f : B →ₐ[k] A).rangeRestrict_surjective⟩
  have h := Ideal.comap_map_eq_self_of_faithfullyFlat (B := A) (Ideal.map g J)
  rw [Ideal.map_map] at h
  have h2 := congrArg (Ideal.comap g) h
  rw [Ideal.comap_comap, Ideal.comap_map_of_bijective g hg] at h2
  exact h2

end GlobalTheory.PDiv
