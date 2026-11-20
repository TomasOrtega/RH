import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement

/- English proof (translation)
Introduce `K _ _ V A B _ _ _ _ φ f hφ hfin hf`. Use `letI : Algebra A B := φ.toAlgebra`. Use `letI : Algebra A K := (V.subtype.comp f).toAlgebra`. Use `letI : Algebra A V := f.toAlgebra`. Use `haveI : Module.Finite A B := hfin`.

Establish `hfK : Function.Injective (V.subtype.comp f)` using `Subtype.val_injective.comp hf`. Use `haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hφ`. Use `haveI : FaithfulSMul A K := (faithfulSMul_iff_algebraMap_injective A K).mpr hfK`. Use `haveI : IsScalarTower A V K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Use `haveI : Algebra.IsAlgebraic A B := inferInstance`.

Set `y₀ : B →ₐ[A] K` to `IsAlgClosed.lift`. Establish `hmem : ∀ b, y₀ b ∈ V`. Introduce `b`. Establish `h1 : IsIntegral A (y₀ b)` using `(Algebra.IsIntegral.isIntegral b).map y₀`. Establish `h2 : IsIntegral V (y₀ b)` using `h1.tower_top`.

Take `⟨z, hz⟩` from `IsIntegrallyClosed.isIntegral_iff.mp h2`. Rewrite using `[← hz]`. Conclude with `z.2`. Set `y : B →+* V` to `y₀.toRingHom.codRestrict V hmem`. Take `⟨n, g, hg⟩` from `Module.Finite.exists_fin (R := A) (M := B)`.

Use `⟨y, Finset.univ.image (fun i => y₀ (g i)), ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `a`. Conclude with `y₀.commutes a`. Introduce `b show y₀ b ∈ _`. Establish `hb : b ∈ Submodule.span A (Set.range g)`.

Rewrite using `[hg]`. Conclude with `Submodule.mem_top`. Proceed by induction on `hb using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨i, rfl⟩` from `hx`.

Apply `Subfield.subset_closure` to reduce the goal to its premises. Use `right`. Simplify using the standard rewrite rules. Consider the case `zero`. Rewrite using `[map_zero]`.

Conclude with `zero_mem _`. Consider the case `add x z _ _ hx hz`. Rewrite using `[map_add]`. Conclude with `add_mem hx hz`. Consider the case `smul a x _ hx`.

Rewrite using `[map_smul, Algebra.smul_def]`. Use `mul_mem (Subfield.subset_closure ?_) hx` and prove the remaining obligations. Use `left`. Conclude with `⟨a, rfl⟩`.
-/
theorem UpperTheory.V.Ws.Po.finExt :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (V : ValuationSubring K) (A B : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
      (φ : A →+* B) (f : A →+* V), Function.Injective φ → φ.Finite → Function.Injective f →
      ∃ (y : B →+* V) (s : Finset K), y.comp φ = f ∧ ∀ b, (y b : K) ∈ Subfield.closure (Set.range (V.subtype.comp f) ∪ s) := by
  intro K _ _ V A B _ _ _ _ φ f hφ hfin hf
  classical
  letI : Algebra A B := φ.toAlgebra
  letI : Algebra A K := (V.subtype.comp f).toAlgebra
  letI : Algebra A V := f.toAlgebra
  haveI : Module.Finite A B := hfin
  have hfK : Function.Injective (V.subtype.comp f) := Subtype.val_injective.comp hf
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hφ
  haveI : FaithfulSMul A K := (faithfulSMul_iff_algebraMap_injective A K).mpr hfK
  haveI : IsScalarTower A V K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsAlgebraic A B := inferInstance
  let y₀ : B →ₐ[A] K := IsAlgClosed.lift
  have hmem : ∀ b, y₀ b ∈ V := by
    intro b
    have h1 : IsIntegral A (y₀ b) := (Algebra.IsIntegral.isIntegral b).map y₀
    have h2 : IsIntegral V (y₀ b) := h1.tower_top
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
    rw [← hz]
    exact z.2
  let y : B →+* V := y₀.toRingHom.codRestrict V hmem
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := A) (M := B)
  refine ⟨y, Finset.univ.image (fun i => y₀ (g i)), ?_, ?_⟩
  · ext a
    exact y₀.commutes a
  · intro b
    show y₀ b ∈ _
    have hb : b ∈ Submodule.span A (Set.range g) := by
      rw [hg]
      exact Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      apply Subfield.subset_closure
      right
      simp
    | zero =>
      rw [map_zero]
      exact zero_mem _
    | add x z _ _ hx hz =>
      rw [map_add]
      exact add_mem hx hz
    | smul a x _ hx =>
      rw [map_smul, Algebra.smul_def]
      refine mul_mem (Subfield.subset_closure ?_) hx
      left
      exact ⟨a, rfl⟩
