import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenFibMapAlgebraMap
open CategoryTheory Limits
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.LocAcyc

def zmodTensorAct (U B : Type) [CommRing U] [CommRing B] [Algebra U B] (q : ℕ) (D : Type)
    [CommRing D] [Algebra U D] (act : Multiplicative (ZMod q) →* (D ≃ₐ[U] D)) :
    Multiplicative (ZMod q) →* (B ⊗[U] D ≃ₐ[B] B ⊗[U] D) where
  toFun g := Algebra.TensorProduct.congr AlgEquiv.refl (act g)
  map_one' := by
    ext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b x => simp
    | add z w hz hw => simp_all [map_add]
  map_mul' g h := by
    ext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b x => simp
    | add z w hz hw => simp_all [map_add]

/- English proof (translation)
Simplify using `[zmodTensorAct]`.
-/
@[simp] theorem zmodTensorAct_tmul (U B : Type) [CommRing U] [CommRing B] [Algebra U B] (q : ℕ)
    (D : Type) [CommRing D] [Algebra U D] (act : Multiplicative (ZMod q) →* (D ≃ₐ[U] D))
    (b : B) (x : D) (g : Multiplicative (ZMod q)) :
    zmodTensorAct U B q D act g (b ⊗ₜ x) = b ⊗ₜ act g x := by simp [zmodTensorAct]

/- English proof (translation)
Use `haveI : NeZero q := ⟨hq.ne'⟩`. Take `⟨h1, h2, h3, h4⟩` from `hD`. Use `⟨inferInstance, inferInstance, inferInstance, ?_⟩` and prove the remaining obligations. Use `set Φ := Algebra.TensorProduct.productMap (Pi.algHom U (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id U D)) (Pi.algHom U (fun _ : Multiplicative (ZMod q) => D) (fun g => (act g).toAlgHom)) with hΦ`. Use `set ΦB := Algebra.TensorProduct.productMap (Pi.algHom B (fun _ : Multiplicative (ZMod q) => B ⊗[U] D) (fun _ => AlgHom.id B (B ⊗[U] D))) (Pi.algHom B (fun _ : Multiplicative (ZMod q) => B ⊗[U] D) (fun g => (zmodTensorAct U B q D act g).toAlgHom)) with hΦB`.

Set `e1` to `TensorProduct.AlgebraTensorModule.distribBaseChange U B D D`. Set `L` to `(LinearEquiv.ofBijective Φ.toLinearMap h4).lTensor B`. Set `e2` to `TensorProduct.piRight U U B (fun _ : Multiplicative (ZMod q) => D)`. Establish `key : ∀ z, ΦB (e1 z) = e2 (L z)`. Introduce `z`.

Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul b w`. Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul x y`. Use function extensionality and compare the values at `g`. Simplify using `[e1, L, e2, hΦ, hΦB, Algebra.TensorProduct.productMap_apply_tmul]`. Consider the case `add w w' hw hw'`. Simplify using `only [TensorProduct.tmul_add, map_add, hw, hw']`.

Consider the case `add z w hz hw => simp only [map_add, hz, hw]`. Establish `: (ΦB : _ → _) = e2 ∘ L ∘ e1.symm`. Use function extensionality and compare the values at `w`. Simplify using `using key (e1.symm w)`. Rewrite using `[this]`.

Conclude with `e2.bijective.comp (L.bijective.comp e1.symm.bijective)`.
-/
theorem isZModTorsor_tensorBase (U B : Type) [CommRing U] [CommRing B] [Algebra U B] (q : ℕ)
    (D : Type) [CommRing D] [Algebra U D] (act : Multiplicative (ZMod q) →* (D ≃ₐ[U] D))
    (hq : 0 < q) (hD : IsZModTorsor U D q act) :
    IsZModTorsor B (B ⊗[U] D) q (zmodTensorAct U B q D act) := by
  haveI : NeZero q := ⟨hq.ne'⟩
  obtain ⟨h1, h2, h3, h4⟩ := hD
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  set Φ := Algebra.TensorProduct.productMap
      (Pi.algHom U (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id U D))
      (Pi.algHom U (fun _ : Multiplicative (ZMod q) => D) (fun g => (act g).toAlgHom)) with hΦ
  set ΦB := Algebra.TensorProduct.productMap
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => B ⊗[U] D) (fun _ => AlgHom.id B (B ⊗[U] D)))
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => B ⊗[U] D)
        (fun g => (zmodTensorAct U B q D act g).toAlgHom)) with hΦB
  let e1 := TensorProduct.AlgebraTensorModule.distribBaseChange U B D D
  let L := (LinearEquiv.ofBijective Φ.toLinearMap h4).lTensor B
  let e2 := TensorProduct.piRight U U B (fun _ : Multiplicative (ZMod q) => D)
  have key : ∀ z, ΦB (e1 z) = e2 (L z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b w =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
        funext g
        simp [e1, L, e2, hΦ, hΦB, Algebra.TensorProduct.productMap_apply_tmul]
      | add w w' hw hw' =>
        simp only [TensorProduct.tmul_add, map_add, hw, hw']
    | add z w hz hw => simp only [map_add, hz, hw]
  have : (ΦB : _ → _) = e2 ∘ L ∘ e1.symm := by
    funext w
    simpa using key (e1.symm w)
  rw [this]
  exact e2.bijective.comp (L.bijective.comp e1.symm.bijective)

/- English proof (translation)
Introduce `U B _ _ _ q D _ _ act hq hD` and use `⟨_, isZModTorsor_tensorBase U B q D act hq hD⟩`.
-/
theorem exists_isZModTorsor_tensorBase : ∀ (U B : Type) [CommRing U] [CommRing B] [Algebra U B] (q : ℕ) (D : Type) [CommRing D]
    [Algebra U D] (act : Multiplicative (ZMod q) →* (D ≃ₐ[U] D)), 0 < q →
    GlobalTheory.LocAcyc.IsZModTorsor U D q act →
    ∃ actB : Multiplicative (ZMod q) →* (TensorProduct U B D ≃ₐ[B] TensorProduct U B D),
      GlobalTheory.LocAcyc.IsZModTorsor B (TensorProduct U B D) q actB :=
  fun U B _ _ _ q D _ _ act hq hD => ⟨_, isZModTorsor_tensorBase U B q D act hq hD⟩

end GlobalTheory.LocAcyc
