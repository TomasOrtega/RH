import Mathlib

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

/- English proof (translation)
Introduce `A B _ _ _ k _ _`. Use extensionality with `r`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨q, rfl⟩ show Ideal.comap (algebraMap A B) (Ideal.comap _ q.asIdeal) = _`. Rewrite using `[Ideal.comap_comap, ← Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap, ← Ideal.comap_comap, Ideal.eq_bot_of_prime (Ideal.comap _ q.asIdeal), ← RingHom.ker_eq_comap_bot]`.

Introduce `hr`. Express the relevant statement in the definitionally equal form `Ideal.comap (algebraMap A B) r.asIdeal = RingHom.ker (algebraMap A k) at hr`. Use `set f := algebraMap A k with hf`. Set `I` to `RingHom.ker f`. Set `K` to `r.asIdeal.ResidueField`.

Set `g : A →+* K` to `(algebraMap B K).comp (algebraMap A B)`. Establish `hg : RingHom.ker g = I`. Express the relevant statement in the definitionally equal form `RingHom.ker ((algebraMap B K).comp (algebraMap A B)) = RingHom.ker f`. Rewrite using `[← RingHom.comap_ker, Ideal.ker_algebraMap_residueField, hr]`. Establish `hIg : ∀ a ∈ I, g a = 0` using `fun a ha => by rw [← RingHom.mem_ker, hg]; exact ha`.

Set `ι₁ : A ⧸ I →+* k` to `RingHom.kerLift f`. Set `ι₂ : A ⧸ I →+* K` to `Ideal.Quotient.lift I g hIg`. Establish `inj₁ : Function.Injective ι₁` using `RingHom.kerLift_injective f`. Establish `inj₂ : Function.Injective ι₂` using `RingHom.lift_injective_of_ker_le_ideal I hIg hg.le`. Use `letI : Algebra (A ⧸ I) k := ι₁.toAlgebra`.

Use `letI : Algebra (A ⧸ I) K := ι₂.toAlgebra`. Use `haveI : Nontrivial (k ⊗[A ⧸ I] K) := Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain (A ⧸ I) k K inj₁ inj₂`. Use `haveI : SMulCommClass (A ⧸ I) A k := ⟨fun x a y => by`. Simplify using `only [Algebra.smul_def]`. Use the proof step `ring⟩`.

Set `α : k →ₐ[A] k ⊗[A ⧸ I] K` to `Algebra.TensorProduct.includeLeft`. Set `β : B →ₐ[A] k ⊗[A ⧸ I] K` to `{ ((Algebra.TensorProduct.includeRight : K →ₐ[A ⧸ I] k ⊗[A ⧸ I] K).toRingHom.comp (algebraMap B K)) with commutes' := fun a => by`. Express the relevant statement in the definitionally equal form `(1 : k) ⊗ₜ[A ⧸ I] (algebraMap (A ⧸ I) K (Ideal.Quotient.mk I a)) = _`. Rewrite using `[Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one (A := K), ← TensorProduct.smul_tmul, Algebra.smul_def, _root_.mul_one]`. Use `rfl }`.

Set `φ : k ⊗[A] B →ₐ[A] k ⊗[A ⧸ I] K` to `Algebra.TensorProduct.lift α β (fun _ _ => Commute.all _ _)`. Take `⟨m, hm⟩` from `Ideal.exists_maximal (k ⊗[A ⧸ I] K)`. Use `⟨PrimeSpectrum.comap φ.toRingHom ⟨m, hm.isPrime⟩, ?_⟩` and prove the remaining obligations. Use `ext1`. Use `show Ideal.comap _ (Ideal.comap φ.toRingHom m) = r.asIdeal`.

Establish `hcomp : φ.toRingHom.comp (Algebra.TensorProduct.includeRight : B →ₐ[A] k ⊗[A] B).toRingHom = ((Algebra.TensorProduct.includeRight : K →ₐ[A ⧸ I] k ⊗[A ⧸ I] K).toRingHom.comp (algebraMap B K))`. Use extensionality with `b`. Simplify using `[φ, α, β, Algebra.TensorProduct.lift_tmul]`. Rewrite using `[Ideal.comap_comap, hcomp, ← Ideal.comap_comap, Ideal.eq_bot_of_prime (Ideal.comap _ m), ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]`.
-/
theorem range_comap_includeRight_field :
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (k : Type) [Field k] [Algebra A k],
    Set.range (PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] k ⊗[A] B).toRingHom) = {r : PrimeSpectrum B | r.asIdeal.comap (algebraMap A B) = RingHom.ker (algebraMap A k)} := by
  intro A B _ _ _ k _ _
  ext r
  constructor
  · rintro ⟨q, rfl⟩
    show Ideal.comap (algebraMap A B) (Ideal.comap _ q.asIdeal) = _
    rw [Ideal.comap_comap, ← Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap,
      ← Ideal.comap_comap, Ideal.eq_bot_of_prime (Ideal.comap _ q.asIdeal),
      ← RingHom.ker_eq_comap_bot]
  · intro hr
    change Ideal.comap (algebraMap A B) r.asIdeal = RingHom.ker (algebraMap A k) at hr
    set f := algebraMap A k with hf
    let I := RingHom.ker f
    let K := r.asIdeal.ResidueField
    let g : A →+* K := (algebraMap B K).comp (algebraMap A B)
    have hg : RingHom.ker g = I := by
      change RingHom.ker ((algebraMap B K).comp (algebraMap A B)) = RingHom.ker f
      rw [← RingHom.comap_ker, Ideal.ker_algebraMap_residueField, hr]
    have hIg : ∀ a ∈ I, g a = 0 := fun a ha => by rw [← RingHom.mem_ker, hg]; exact ha
    let ι₁ : A ⧸ I →+* k := RingHom.kerLift f
    let ι₂ : A ⧸ I →+* K := Ideal.Quotient.lift I g hIg
    have inj₁ : Function.Injective ι₁ := RingHom.kerLift_injective f
    have inj₂ : Function.Injective ι₂ := RingHom.lift_injective_of_ker_le_ideal I hIg hg.le
    letI : Algebra (A ⧸ I) k := ι₁.toAlgebra
    letI : Algebra (A ⧸ I) K := ι₂.toAlgebra
    haveI : Nontrivial (k ⊗[A ⧸ I] K) :=
      Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain (A ⧸ I) k K inj₁ inj₂
    haveI : SMulCommClass (A ⧸ I) A k := ⟨fun x a y => by
      simp only [Algebra.smul_def]; ring⟩
    let α : k →ₐ[A] k ⊗[A ⧸ I] K := Algebra.TensorProduct.includeLeft
    let β : B →ₐ[A] k ⊗[A ⧸ I] K :=
      { ((Algebra.TensorProduct.includeRight : K →ₐ[A ⧸ I] k ⊗[A ⧸ I] K).toRingHom.comp
          (algebraMap B K)) with
        commutes' := fun a => by
          change (1 : k) ⊗ₜ[A ⧸ I] (algebraMap (A ⧸ I) K (Ideal.Quotient.mk I a)) = _
          rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one (A := K),
            ← TensorProduct.smul_tmul, Algebra.smul_def, _root_.mul_one]
          rfl }
    let φ : k ⊗[A] B →ₐ[A] k ⊗[A ⧸ I] K := Algebra.TensorProduct.lift α β (fun _ _ => Commute.all _ _)
    obtain ⟨m, hm⟩ := Ideal.exists_maximal (k ⊗[A ⧸ I] K)
    refine ⟨PrimeSpectrum.comap φ.toRingHom ⟨m, hm.isPrime⟩, ?_⟩
    ext1
    show Ideal.comap _ (Ideal.comap φ.toRingHom m) = r.asIdeal
    have hcomp : φ.toRingHom.comp (Algebra.TensorProduct.includeRight : B →ₐ[A] k ⊗[A] B).toRingHom =
        ((Algebra.TensorProduct.includeRight : K →ₐ[A ⧸ I] k ⊗[A ⧸ I] K).toRingHom.comp
          (algebraMap B K)) := by
      ext b
      simp [φ, α, β, Algebra.TensorProduct.lift_tmul]
    rw [Ideal.comap_comap, hcomp, ← Ideal.comap_comap, Ideal.eq_bot_of_prime (Ideal.comap _ m),
      ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]

end GlobalTheory
