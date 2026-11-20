import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapEqMk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerAlgebraFiniteProjectiveFaithfullyFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerAlgebraZmodTorsorBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMultilinearFormOfPicTorsionStatement
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.KummerStep

open GlobalTheory.KummerAlg

/- English proof (translation)
The claim follows from `GlobalTheory.T.kummerAlgebra_finite_projective_faithfullyFlat`.
-/
theorem p1 : ∀ (B : Type) [CommRing B] (L : Type) [AddCommGroup L] [Module B L] [Module.Invertible B L] (q : ℕ) (φ : MultilinearMap B (fun _ : Fin q => L) B), 0 < q → (∀ p : Ideal B, p.IsPrime → ∃ e : L, φ (fun _ => e) ∉ p) → Module.Finite B (GlobalTheory.KummerAlg.Alg φ) ∧ Module.Projective B (GlobalTheory.KummerAlg.Alg φ) ∧ Module.FaithfullyFlat B (GlobalTheory.KummerAlg.Alg φ) := GlobalTheory.T.kummerAlgebra_finite_projective_faithfullyFlat
/- English proof (translation)
The claim follows from `GlobalTheory.T.kummerAlgebra_zmod_torsor_bijective`.
-/
theorem p2 : ∀ (B : Type) [CommRing B] (L : Type) [AddCommGroup L] [Module B L] [Module.Invertible B L] (q : ℕ) [NeZero q] (φ : MultilinearMap B (fun _ : Fin q => L) B), IsUnit (q : B) → (∀ p : Ideal B, p.IsPrime → ∃ e : L, φ (fun _ => e) ∉ p) → ∀ (ζ : B) (hζ : ζ ^ q = 1), (∀ k : ℕ, 0 < k → k < q → IsUnit (1 - ζ ^ k)) → Function.Bijective (Algebra.TensorProduct.productMap (Pi.algHom B (fun _ : Multiplicative (ZMod q) => GlobalTheory.KummerAlg.Alg φ) (fun _ => AlgHom.id B (GlobalTheory.KummerAlg.Alg φ))) (Pi.algHom B (fun _ : Multiplicative (ZMod q) => GlobalTheory.KummerAlg.Alg φ) (fun g => (GlobalTheory.KummerAlg.act φ ζ hζ g).toAlgHom))) := GlobalTheory.T.kummerAlgebra_zmod_torsor_bijective
/- English proof (translation)
The claim follows from `GlobalTheory.T.exists_multilinear_form_of_pic_torsion`.
-/
theorem p4 : ∀ (B : Type) [CommRing B] (q : ℕ) (c : CommRing.Pic B), c ^ q = 1 → ∃ φ : MultilinearMap B (fun _ : Fin q => CommRing.Pic.AsModule c) B, ∀ p : Ideal B, p.IsPrime → ∃ e : CommRing.Pic.AsModule c, φ (fun _ => e) ∉ p := GlobalTheory.T.exists_multilinear_form_of_pic_torsion

/- English proof (translation)
Set `f : L →ₗ[B] B` to `s.toLinearMap ∘ₗ gen φ`. Establish `hf : ∀ e : L, f e ^ q = φ (fun _ => e)` using `fun e => by`. Use `congrArg s (prod_gen φ (fun _ => e))` as an intermediate fact. Simplify `this` using `[f, map_prod, Finset.prod_const, AlgHom.commutes]`. Establish `hsurj : Function.Surjective f`.

Rewrite using `[← LinearMap.range_eq_top]`. Assume the negation of the conclusion as `h`. Take `⟨m, hm, hle⟩` from `Ideal.exists_le_maximal (LinearMap.range f) h`. Take `⟨e, he⟩` from `hφ m hm.isPrime`. Apply `he` to reduce the goal to its premises.

Rewrite using `[← hf e]`. Conclude with `Ideal.pow_mem_of_mem _ (hle ⟨e, rfl⟩) q hq`. Conclude with `Module.Free.of_equiv (LinearEquiv.ofBijective f (Module.Invertible.bijective_of_surjective hsurj)).symm`.
-/
theorem free_of_section (B : Type) [CommRing B] (L : Type) [AddCommGroup L] [Module B L]
    [Module.Invertible B L] (q : ℕ) (φ : MultilinearMap B (fun _ : Fin q => L) B) (hq : 0 < q)
    (hφ : ∀ p : Ideal B, p.IsPrime → ∃ e : L, φ (fun _ => e) ∉ p)
    (s : Alg φ →ₐ[B] B) : Module.Free B L := by
  let f : L →ₗ[B] B := s.toLinearMap ∘ₗ gen φ
  have hf : ∀ e : L, f e ^ q = φ (fun _ => e) := fun e => by
    have := congrArg s (prod_gen φ (fun _ => e))
    simpa [f, map_prod, Finset.prod_const, AlgHom.commutes] using this
  have hsurj : Function.Surjective f := by
    rw [← LinearMap.range_eq_top]
    by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (LinearMap.range f) h
    obtain ⟨e, he⟩ := hφ m hm.isPrime
    apply he
    rw [← hf e]
    exact Ideal.pow_mem_of_mem _ (hle ⟨e, rfl⟩) q hq
  exact Module.Free.of_equiv
    (LinearEquiv.ofBijective f (Module.Invertible.bijective_of_surjective hsurj)).symm

/- English proof (translation)
Introduce `B _ q hq hqu ⟨ζ, hζ, hζk⟩ hT c hc`. Use `haveI : NeZero q := ⟨hq.ne'⟩`. Take `⟨φ, hφ⟩` from `p4 B q c hc`. Take `⟨hfin, hproj, hff⟩` from `p1 B (CommRing.Pic.AsModule c) q φ hq hφ`. Take `⟨s⟩` from `hT (Alg φ) hfin hproj hff (act φ ζ hζ) (p2 B (CommRing.Pic.AsModule c) q φ hqu hφ ζ hζ hζk)`.

Use `free_of_section B (CommRing.Pic.AsModule c) q φ hq hφ s` as an intermediate fact. Rewrite using `[← CommRing.Pic.mk_eq_self (M := c), CommRing.Pic.mk_eq_one_iff_free]`. Conclude with `this`.
-/
theorem kummer_step : ∀ (B : Type) [CommRing B] (q : ℕ), 0 < q → IsUnit (q : B) →
    (∃ ζ : B, ζ ^ q = 1 ∧ ∀ k : ℕ, 0 < k → k < q → IsUnit (1 - ζ ^ k)) →
    (∀ (D : Type) [CommRing D] [Algebra B D], Module.Finite B D → Module.Projective B D →
      Module.FaithfullyFlat B D → ∀ act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D),
      Function.Bijective (Algebra.TensorProduct.productMap
        (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id B D))
        (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun g => (act g).toAlgHom))) → Nonempty (D →ₐ[B] B)) →
    ∀ c : CommRing.Pic B, c ^ q = 1 → c = 1 := by
  intro B _ q hq hqu ⟨ζ, hζ, hζk⟩ hT c hc
  haveI : NeZero q := ⟨hq.ne'⟩
  obtain ⟨φ, hφ⟩ := p4 B q c hc
  obtain ⟨hfin, hproj, hff⟩ := p1 B (CommRing.Pic.AsModule c) q φ hq hφ
  obtain ⟨s⟩ := hT (Alg φ) hfin hproj hff (act φ ζ hζ) (p2 B (CommRing.Pic.AsModule c) q φ hqu hφ ζ hζ hζk)
  have := free_of_section B (CommRing.Pic.AsModule c) q φ hq hφ s
  rw [← CommRing.Pic.mk_eq_self (M := c), CommRing.Pic.mk_eq_one_iff_free]
  exact this

end GlobalTheory.KummerStep
