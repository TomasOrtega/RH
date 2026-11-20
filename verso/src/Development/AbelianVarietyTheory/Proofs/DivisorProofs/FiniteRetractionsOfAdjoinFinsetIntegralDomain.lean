import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLtTopOfEssFiniteType
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Use `choose p hpm hp0 using fun x : E => (Algebra.IsIntegral.isIntegral (R := D) x)`. Establish `hfin : (Set.pi Set.univ fun f : F => ((((p f.1).map (algebraMap D T)).roots.toFinset : Finset T) : Set T)).Finite` using `Set.Finite.pi (fun f => Finset.finite_toSet _)`. Use `Set.Finite.of_finite_image (f := fun χ : E →ₐ[D] T => fun f : F => χ f.1) (hfin.subset ?_) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨χ, _, rfl⟩`. Use `Set.mem_univ_pi.2 fun f => ?_` and prove the remaining obligations.

Simplify using `only [Finset.mem_coe, Multiset.mem_toFinset]`. Rewrite using `[Polynomial.mem_roots ((hpm f.1).map (algebraMap D T)).ne_zero, Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def, Polynomial.aeval_algHom_apply, Polynomial.aeval_def, hp0, map_zero]`. Introduce `χ₁ h₁ χ₂ h₂ he`. Apply `AlgHom.ext_of_adjoin_eq_top hF` to reduce the goal to its premises. Introduce and unpack `x (⟨t, rfl⟩ | hx)`.

Establish `e₁` using `AlgHom.congr_fun (show χ₁.comp ι = AlgHom.id D T from h₁) t`. Establish `e₂` using `AlgHom.congr_fun (show χ₂.comp ι = AlgHom.id D T from h₂) t`. Simplify using `only [AlgHom.comp_apply, AlgHom.id_apply] at e₁ e₂`. Rewrite using `[e₁, e₂]`. Conclude with `congrFun he ⟨x, hx⟩`.
-/
theorem finite_retractions_of_adjoin_finset_integral
    (D T E : Type) [CommRing D] [IsDomain D] [CommRing T] [IsDomain T] [Algebra D T]
    [CommRing E] [Algebra D E] [Algebra.IsIntegral D E] (ι : T →ₐ[D] E) (F : Finset E)
    (hF : Algebra.adjoin D (Set.range ι ∪ (F : Set E)) = ⊤) :
    {χ : E →ₐ[D] T | χ.comp ι = AlgHom.id D T}.Finite := by
  classical
  choose p hpm hp0 using fun x : E => (Algebra.IsIntegral.isIntegral (R := D) x)
  have hfin : (Set.pi Set.univ fun f : F =>
      ((((p f.1).map (algebraMap D T)).roots.toFinset : Finset T) : Set T)).Finite :=
    Set.Finite.pi (fun f => Finset.finite_toSet _)
  refine Set.Finite.of_finite_image (f := fun χ : E →ₐ[D] T => fun f : F => χ f.1)
    (hfin.subset ?_) ?_
  · rintro _ ⟨χ, _, rfl⟩
    refine Set.mem_univ_pi.2 fun f => ?_
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    rw [Polynomial.mem_roots ((hpm f.1).map (algebraMap D T)).ne_zero, Polynomial.IsRoot,
      Polynomial.eval_map, ← Polynomial.aeval_def, Polynomial.aeval_algHom_apply,
      Polynomial.aeval_def, hp0, map_zero]
  · intro χ₁ h₁ χ₂ h₂ he
    apply AlgHom.ext_of_adjoin_eq_top hF
    rintro x (⟨t, rfl⟩ | hx)
    · have e₁ := AlgHom.congr_fun (show χ₁.comp ι = AlgHom.id D T from h₁) t
      have e₂ := AlgHom.congr_fun (show χ₂.comp ι = AlgHom.id D T from h₂) t
      simp only [AlgHom.comp_apply, AlgHom.id_apply] at e₁ e₂
      rw [e₁, e₂]
    · exact congrFun he ⟨x, hx⟩

/- English proof (translation)
Introduce `D T E _ _ _ _ _ _ _ _ ι F hF` and use `finite_retractions_of_adjoin_finset_integral D T E ι F hF`.
-/
theorem finite_retractions_of_adjoin_finset_integral' :
    ∀ (D T E : Type) [CommRing D] [IsDomain D] [CommRing T] [IsDomain T] [Algebra D T]
      [CommRing E] [Algebra D E] [Algebra.IsIntegral D E] (ι : T →ₐ[D] E) (F : Finset E),
      Algebra.adjoin D (Set.range ι ∪ (F : Set E)) = ⊤ →
        {χ : E →ₐ[D] T | χ.comp ι = AlgHom.id D T}.Finite :=
  fun D T E _ _ _ _ _ _ _ _ ι F hF => finite_retractions_of_adjoin_finset_integral D T E ι F hF

end GlobalTheory
