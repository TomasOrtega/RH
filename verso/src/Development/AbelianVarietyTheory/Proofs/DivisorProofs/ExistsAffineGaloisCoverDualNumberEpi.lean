import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackDescentAlongGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section
namespace GlobalTheory.DualCover

variable {A B : Type} [CommRing A] [CommRing B]

def dualMap (g : A →+* B) : DualNumber A →+* DualNumber B :=
  letI : Algebra A B := g.toAlgebra
  (DualNumber.lift ⟨(Algebra.ofId A (DualNumber B), DualNumber.eps), by simp, fun _ ↦ Commute.all _ _⟩).toRingHom

/- English proof (translation)
Use `letI : Algebra A B := g.toAlgebra`. Use `show (DualNumber.lift _ : DualNumber A →ₐ[A] DualNumber B) x = _`. Rewrite using `[DualNumber.lift_apply_apply]`. Apply the tactic sequence `ext <;> simp [Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl', RingHom.algebraMap_toAlgebra]`.
-/
theorem dualMap_apply (g : A →+* B) (x : DualNumber A) :
    dualMap g x = TrivSqZeroExt.inl (g x.fst) + TrivSqZeroExt.inr (g x.snd) := by
  letI : Algebra A B := g.toAlgebra
  show (DualNumber.lift _ : DualNumber A →ₐ[A] DualNumber B) x = _
  rw [DualNumber.lift_apply_apply]
  ext <;> simp [Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl', RingHom.algebraMap_toAlgebra]

/- English proof (translation)
Simplify using `[dualMap_apply]`.
-/
@[simp] theorem dualMap_fst (g : A →+* B) (x : DualNumber A) : (dualMap g x).fst = g x.fst := by
  simp [dualMap_apply]

/- English proof (translation)
Simplify using `[dualMap_apply]`.
-/
@[simp] theorem dualMap_snd (g : A →+* B) (x : DualNumber A) : (dualMap g x).snd = g x.snd := by
  simp [dualMap_apply]

end GlobalTheory.DualCover

namespace GlobalTheory.DualCover
variable {A B : Type} [CommRing A] [CommRing B]

/- English proof (translation)
Use `letI : Algebra A B := g.toAlgebra`. Establish `hc : ∀ a : A, dualMap g (algebraMap A (DualNumber A) a) = algebraMap A (DualNumber B) a`. Introduce `a`. Apply the tactic sequence `ext <;> simp [dualMap_apply, TrivSqZeroExt.algebraMap_eq_inl', RingHom.algebraMap_toAlgebra]`. Set `ψ₀ : DualNumber A →ₐ[A] DualNumber B` to `AlgHom.mk (dualMap g) hc`.

Establish `hψ₀ : ∀ x, ψ₀ x = dualMap g x` using `fun _ ↦ rfl`. Set `j : B →ₐ[A] DualNumber B` to `TrivSqZeroExt.inlAlgHom A B B`. Set `G : TensorProduct A (DualNumber A) B →ₐ[A] DualNumber B` to `Algebra.TensorProduct.lift ψ₀ j (fun _ _ ↦ Commute.all _ _)`. Set `h : DualNumber B → TensorProduct A (DualNumber A) B` to `fun x ↦ (1 : DualNumber A) ⊗ₜ[A] x.fst + (DualNumber.eps : DualNumber A) ⊗ₜ[A] x.snd`. Establish `hadd : ∀ u v, h (u + v) = h u + h v`.

Introduce `u v`. Simplify using `only [h, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TensorProduct.tmul_add]`. Normalize the expressions using the abelian group laws. Establish `hgh : ∀ x, G (h x) = x`. Introduce `x`.

Simplify using `only [h, G, map_add, Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]`. Apply the tactic sequence `ext <;> simp [j, hψ₀, dualMap_apply]`. Establish `hhg : ∀ x, h (G x) = x`. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`.

Consider the case `zero => simp [h]`. Consider the case `tmul a b`. Establish `e1 : a = TrivSqZeroExt.fst a • (1 : DualNumber A) + TrivSqZeroExt.snd a • DualNumber.eps`. Apply the tactic sequence `ext <;> simp`. Establish `f1 : TrivSqZeroExt.fst (ψ₀ a * j b) = TrivSqZeroExt.fst a • b`.

Simplify using `[hψ₀, dualMap_apply, j, Algebra.smul_def, RingHom.algebraMap_toAlgebra]`. Establish `f2 : TrivSqZeroExt.snd (ψ₀ a * j b) = TrivSqZeroExt.snd a • b`. Simplify using `[hψ₀, dualMap_apply, j, Algebra.smul_def, RingHom.algebraMap_toAlgebra, TrivSqZeroExt.algebraMap_eq_inl]`. Use `show (1 : DualNumber A) ⊗ₜ[A] TrivSqZeroExt.fst (ψ₀ a * j b) + (DualNumber.eps : DualNumber A) ⊗ₜ[A] TrivSqZeroExt.snd (ψ₀ a * j b) = a ⊗ₜ[A] b`. Rewrite using `[f1, f2, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.add_tmul, ← e1]`.

Consider the case `add x y hx hy => rw [map_add, hadd, hx, hy]`. Establish `hbij : Function.Bijective G` using `Function.bijective_iff_has_inverse.2 ⟨h, hhg, hgh⟩`. Set `eR : TensorProduct A (DualNumber A) B ≃+* DualNumber B` to `(AlgEquiv.ofBijective G hbij).toRingEquiv`. Use `(CommRingCat.isPushout_tensorProduct A (DualNumber A) B).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) eR.toCommRingCatIso (by simp) (by ext; simp [RingHom.algebraMap_toAlgebra]) ?_ ?_` and prove the remaining obligations. Use `CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_) show G (x ⊗ₜ[A] 1) = dualMap g x` and prove the remaining obligations.

Simplify using `[G, hψ₀]`. Use `CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_) show G (1 ⊗ₜ[A] x) = algebraMap B (DualNumber B) x` and prove the remaining obligations. Simplify using `[G, j, TrivSqZeroExt.algebraMap_eq_inl']`.
-/
theorem isPushout_dualMap (g : A →+* B) :
    IsPushout (CommRingCat.ofHom (algebraMap A (DualNumber A))) (CommRingCat.ofHom g)
      (CommRingCat.ofHom (dualMap g)) (CommRingCat.ofHom (algebraMap B (DualNumber B))) := by
  letI : Algebra A B := g.toAlgebra
  have hc : ∀ a : A, dualMap g (algebraMap A (DualNumber A) a) = algebraMap A (DualNumber B) a := by
    intro a
    ext <;> simp [dualMap_apply, TrivSqZeroExt.algebraMap_eq_inl', RingHom.algebraMap_toAlgebra]
  let ψ₀ : DualNumber A →ₐ[A] DualNumber B := AlgHom.mk (dualMap g) hc
  have hψ₀ : ∀ x, ψ₀ x = dualMap g x := fun _ ↦ rfl
  let j : B →ₐ[A] DualNumber B := TrivSqZeroExt.inlAlgHom A B B
  let G : TensorProduct A (DualNumber A) B →ₐ[A] DualNumber B :=
    Algebra.TensorProduct.lift ψ₀ j (fun _ _ ↦ Commute.all _ _)
  let h : DualNumber B → TensorProduct A (DualNumber A) B := fun x ↦
    (1 : DualNumber A) ⊗ₜ[A] x.fst + (DualNumber.eps : DualNumber A) ⊗ₜ[A] x.snd
  have hadd : ∀ u v, h (u + v) = h u + h v := by
    intro u v
    simp only [h, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TensorProduct.tmul_add]
    abel
  have hgh : ∀ x, G (h x) = x := by
    intro x
    simp only [h, G, map_add, Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]
    ext <;> simp [j, hψ₀, dualMap_apply]
  have hhg : ∀ x, h (G x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp [h]
    | tmul a b =>
      have e1 : a = TrivSqZeroExt.fst a • (1 : DualNumber A) + TrivSqZeroExt.snd a • DualNumber.eps := by
        ext <;> simp
      have f1 : TrivSqZeroExt.fst (ψ₀ a * j b) = TrivSqZeroExt.fst a • b := by
        simp [hψ₀, dualMap_apply, j, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
      have f2 : TrivSqZeroExt.snd (ψ₀ a * j b) = TrivSqZeroExt.snd a • b := by
        simp [hψ₀, dualMap_apply, j, Algebra.smul_def, RingHom.algebraMap_toAlgebra, TrivSqZeroExt.algebraMap_eq_inl]
      show (1 : DualNumber A) ⊗ₜ[A] TrivSqZeroExt.fst (ψ₀ a * j b) +
        (DualNumber.eps : DualNumber A) ⊗ₜ[A] TrivSqZeroExt.snd (ψ₀ a * j b) = a ⊗ₜ[A] b
      rw [f1, f2, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.add_tmul, ← e1]
    | add x y hx hy => rw [map_add, hadd, hx, hy]
  have hbij : Function.Bijective G := Function.bijective_iff_has_inverse.2 ⟨h, hhg, hgh⟩
  let eR : TensorProduct A (DualNumber A) B ≃+* DualNumber B := (AlgEquiv.ofBijective G hbij).toRingEquiv
  refine (CommRingCat.isPushout_tensorProduct A (DualNumber A) B).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    eR.toCommRingCatIso (by simp) (by ext; simp [RingHom.algebraMap_toAlgebra]) ?_ ?_
  · refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
    show G (x ⊗ₜ[A] 1) = dualMap g x
    simp [G, hψ₀]
  · refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
    show G (1 ⊗ₜ[A] x) = algebraMap B (DualNumber B) x
    simp [G, j, TrivSqZeroExt.algebraMap_eq_inl']

end GlobalTheory.DualCover

namespace GlobalTheory.DualCover

/- English proof (translation)
Establish `h2` using `isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_dualMap g)`. Establish `h3 : IsPullback (spMap (dualMap g)) (spMap (algebraMap B (DualNumber B)) ≫ x') (spMap (algebraMap A (DualNumber A)) ≫ x) π` using `(IsPullback.paste_horiz h2.flip hsq.flip).flip`. Establish `he` using `GlobalTheory.GaloisCartDesc.epi_pullback_fst hG (spMap (algebraMap A (DualNumber A)) ≫ x)`. Rewrite using `[← h3.isoPullback_hom_fst]`. Conclude with `epi_comp _ _`.
-/
theorem epi_spMap_dualMap {X Y : Scheme.{0}} {π : X ⟶ Y} {Ga : Type} [Group Ga] {ρ : Ga → (X ⟶ X)}
    (hG : GlobalTheory.ZM.IsGaloisCover Ga ρ π) {A B : Type} [CommRing A] [CommRing B] (g : A →+* B)
    (x : Sp A ⟶ Y) (x' : Sp B ⟶ X) (hsq : IsPullback (spMap g) x' x π) : Epi (spMap (dualMap g)) := by
  have h2 := isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_dualMap g)
  have h3 : IsPullback (spMap (dualMap g)) (spMap (algebraMap B (DualNumber B)) ≫ x')
      (spMap (algebraMap A (DualNumber A)) ≫ x) π :=
    (IsPullback.paste_horiz h2.flip hsq.flip).flip
  have he := GlobalTheory.GaloisCartDesc.epi_pullback_fst hG (spMap (algebraMap A (DualNumber A)) ≫ x)
  rw [← h3.isoPullback_hom_fst]
  exact epi_comp _ _

/- English proof (translation)
Introduce `X Y π Ga _ ρ hG R' _ x`. Use `haveI : IsFinite π := hG.fin`. Use `haveI : IsAffine (pullback x π) := isAffine_of_isAffineHom (pullback.fst x π)`. Set `X'` to `pullback x π`. Set `g₁ : R' →+* Γ(X', ⊤)` to `(Spec.preimage (X'.isoSpec.inv ≫ pullback.fst x π)).hom`.

Establish `hg₁ : spMap g₁ = X'.isoSpec.inv ≫ pullback.fst x π` using `Spec.map_preimage _`. Set `x'' : Sp Γ(X', ⊤) ⟶ X` to `X'.isoSpec.inv ≫ pullback.snd x π`. Establish `hsq : IsPullback (spMap g₁) x'' x π`. Rewrite using `[hg₁]`. Conclude with `IsPullback.of_iso_pullback ⟨by simp [x'', pullback.condition]⟩ X'.isoSpec.symm (by simp) (by simp [x''])`.

Use `⟨Γ(X', ⊤), inferInstance, g₁, x'', dualMap g₁, hsq.w.symm, ?_, ?_, ?_, epi_spMap_dualMap hG g₁ x x'' hsq⟩` and prove the remaining obligations. Use `RingHom.ext fun a ↦ ?_` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [dualMap_apply, TrivSqZeroExt.algebraMap_eq_inl']`. Use `RingHom.ext fun a ↦ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.

Introduce `r`. Use `RingHom.ext fun a ↦ ?_` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [epsScaleR, dualMap_apply] <;> ring`.
-/
theorem exists_dualCover : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)), GlobalTheory.ZM.IsGaloisCover Ga ρ π → ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ Y), ∃ (R'' : Type) (_ : CommRing R'') (g₁ : R' →+* R'') (x'' : Sp R'' ⟶ X) (d₁ : DualNumber R' →+* DualNumber R''), x'' ≫ π = spMap g₁ ≫ x ∧ d₁.comp (algebraMap R' (DualNumber R')) = (algebraMap R'' (DualNumber R'')).comp g₁ ∧ (TrivSqZeroExt.fstHom R'' R'' R'').toRingHom.comp d₁ = g₁.comp (TrivSqZeroExt.fstHom R' R' R').toRingHom ∧ (∀ r : R', d₁.comp (epsScaleR r) = (epsScaleR (g₁ r)).comp d₁) ∧ Epi (spMap d₁) := by
  intro X Y π Ga _ ρ hG R' _ x
  haveI : IsFinite π := hG.fin
  haveI : IsAffine (pullback x π) := isAffine_of_isAffineHom (pullback.fst x π)
  let X' := pullback x π
  let g₁ : R' →+* Γ(X', ⊤) := (Spec.preimage (X'.isoSpec.inv ≫ pullback.fst x π)).hom
  have hg₁ : spMap g₁ = X'.isoSpec.inv ≫ pullback.fst x π := Spec.map_preimage _
  let x'' : Sp Γ(X', ⊤) ⟶ X := X'.isoSpec.inv ≫ pullback.snd x π
  have hsq : IsPullback (spMap g₁) x'' x π := by
    rw [hg₁]
    exact IsPullback.of_iso_pullback ⟨by simp [x'', pullback.condition]⟩ X'.isoSpec.symm (by simp) (by simp [x''])
  refine ⟨Γ(X', ⊤), inferInstance, g₁, x'', dualMap g₁, hsq.w.symm, ?_, ?_, ?_, epi_spMap_dualMap hG g₁ x x'' hsq⟩
  · refine RingHom.ext fun a ↦ ?_
    ext <;> simp [dualMap_apply, TrivSqZeroExt.algebraMap_eq_inl']
  · refine RingHom.ext fun a ↦ ?_
    simp
  · intro r
    refine RingHom.ext fun a ↦ ?_
    ext <;> simp [epsScaleR, dualMap_apply] <;> ring

end GlobalTheory.DualCover
