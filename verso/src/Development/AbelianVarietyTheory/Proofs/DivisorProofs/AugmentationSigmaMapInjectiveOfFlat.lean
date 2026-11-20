import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs.SigInj

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀}
  {R₁ : Type} [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁)

def jj (i : I) : R₁ := Classical.choose (α.surj i.1 i.2)

/- English proof (translation)
The claim follows from `(Classical.choose_spec (α.surj i.1 i.2)).1`.
-/
theorem jj_q (i : I) : α.q (jj α i) = 0 := (Classical.choose_spec (α.surj i.1 i.2)).1

/- English proof (translation)
The claim follows from `(Classical.choose_spec (α.surj i.1 i.2)).2`.
-/
theorem jj_k (i : I) : α.k (jj α i) = i := (Classical.choose_spec (α.surj i.1 i.2)).2

/- English proof (translation)
Establish `h` using `α.inj (y - jj α i) (by rw [map_sub, hq, jj_q, sub_zero]) (by rw [map_sub, hk, jj_k, sub_self])`. Conclude with `sub_eq_zero.mp h`.
-/
theorem eq_jj {y : R₁} {i : I} (hq : α.q y = 0) (hk : α.k y = i) : y = jj α i := by
  have h := α.inj (y - jj α i) (by rw [map_sub, hq, jj_q, sub_zero]) (by rw [map_sub, hk, jj_k, sub_self])
  exact sub_eq_zero.mp h

/- English proof (translation)
The claim follows from `(eq_jj α (by rw [map_add, jj_q, jj_q, add_zero]) (by rw [map_add, jj_k, jj_k]; rfl)).symm`.
-/
theorem jj_add (i i' : I) : jj α (i + i') = jj α i + jj α i' :=
  (eq_jj α (by rw [map_add, jj_q, jj_q, add_zero]) (by rw [map_add, jj_k, jj_k]; rfl)).symm

/- English proof (translation)
The claim follows from `(eq_jj α (by rw [map_smul, jj_q, smul_zero]) (by rw [α.smul, jj_k]; rfl)).symm`.
-/
theorem jj_smul (r : R) (i : I) : jj α (r • i) = π r • jj α i :=
  (eq_jj α (by rw [map_smul, jj_q, smul_zero]) (by rw [α.smul, jj_k]; rfl)).symm

variable {B B₀ : Type} [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀)

def tau (hs : SemiHom π p) : I ⊗[R] B →+ R₁ ⊗[R₀] B₀ :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun i ↦ AddMonoidHom.mk' (fun b ↦ jj α i ⊗ₜ[R₀] p b)
      (fun b b' ↦ by rw [map_add, TensorProduct.tmul_add]))
      (fun i i' ↦ by ext b; simp [jj_add, TensorProduct.add_tmul]))
    (fun r i b ↦ by
      simp only [AddMonoidHom.mk'_apply]
      rw [jj_smul, hs r b, TensorProduct.smul_tmul])

/- English proof (translation)
Simplify using `[tau, TensorProduct.liftAddHom_tmul]`.
-/
theorem tau_tmul (hs : SemiHom π p) (i : I) (b : B) : tau α p hs (i ⊗ₜ b) = jj α i ⊗ₜ[R₀] p b := by
  simp [tau, TensorProduct.liftAddHom_tmul]

end GlobalTheory.Obs.SigInj

open GlobalTheory.Obs.SigInj in
/- English proof (translation)
Introduce `R R₀ _ _ I hI π hπ hk R₁ _ _ α B B₀ _ _ _ _ p hs hp hker _ σ hσ y hy h0`. Establish `hrange : ∀ y : R₁ ⊗[R₀] B₀, ∃ z, tau α p hs z = y - (1 : R₁) ⊗ₜ[R₀] TensorProduct.lid R₀ B₀ (Algebra.TensorProduct.map α.q (AlgHom.id R₀ B₀) y)`. Introduce `y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, by simp⟩`.

Consider the case `tmul x b₀`. Take `⟨b, rfl⟩` from `hp b₀`. Establish `hq' : α.q (x - algebraMap R₀ R₁ (α.q x)) = 0` using `by simp`. Use `⟨⟨α.k (x - algebraMap R₀ R₁ (α.q x)), α.mem _⟩ ⊗ₜ b, ?_⟩` and prove the remaining obligations. Rewrite using `[tau_tmul, ← eq_jj α hq' rfl, Algebra.TensorProduct.map_tmul, TensorProduct.lid_tmul, ← TensorProduct.smul_tmul, TensorProduct.sub_tmul, Algebra.algebraMap_eq_smul_one]`.

Both sides reduce to the same expression. Consider the case `add a c ha hc`. Take `⟨za, hza⟩` from `ha`. Take `⟨zc, hzc⟩` from `hc`. Conclude with `⟨za + zc, by rw [map_add, hza, hzc, map_add, map_add, TensorProduct.tmul_add]; abel⟩`.

Take `⟨z, hz⟩` from `hrange y`. Rewrite `hz` using `[show Algebra.TensorProduct.map α.q (AlgHom.id R₀ B₀) y = 0 from hy, map_zero, TensorProduct.tmul_zero, sub_zero]`. Establish `hμ : ∀ z, σ (tau α p hs z) = TensorProduct.lid R B (LinearMap.rTensor B I.subtype z)`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul i b => rw [tau_tmul, hσ, jj_k]`. Simplify using the standard rewrite rules. Consider the case `add a c ha hc => rw [map_add, map_add, map_add, map_add, ha, hc]`. Establish `hinj : Function.Injective (fun z ↦ TensorProduct.lid R B (LinearMap.rTensor B I.subtype z))` using `(TensorProduct.lid R B).injective.comp (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective)`.

Establish `hz0 : z = 0` using `hinj (by show TensorProduct.lid R B (LinearMap.rTensor B I.subtype z) = TensorProduct.lid R B (LinearMap.rTensor B I.subtype 0)`. Rewrite using `[map_zero, map_zero, ← hμ, hz, h0])`. Rewrite using `[← hz, hz0, map_zero]`.
-/
theorem GlobalTheory.Obs.sig_inj_of_flat : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) [Module.Flat R B] (σ : R₁ ⊗[R₀] B₀ →+ B), α.IsSig p σ → ∀ y, α.KerQ y → σ y = 0 → y = 0 := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α B B₀ _ _ _ _ p hs hp hker _ σ hσ y hy h0
  have hrange : ∀ y : R₁ ⊗[R₀] B₀, ∃ z, tau α p hs z =
      y - (1 : R₁) ⊗ₜ[R₀] TensorProduct.lid R₀ B₀ (Algebra.TensorProduct.map α.q (AlgHom.id R₀ B₀) y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul x b₀ =>
      obtain ⟨b, rfl⟩ := hp b₀
      have hq' : α.q (x - algebraMap R₀ R₁ (α.q x)) = 0 := by simp
      refine ⟨⟨α.k (x - algebraMap R₀ R₁ (α.q x)), α.mem _⟩ ⊗ₜ b, ?_⟩
      rw [tau_tmul, ← eq_jj α hq' rfl, Algebra.TensorProduct.map_tmul, TensorProduct.lid_tmul,
        ← TensorProduct.smul_tmul, TensorProduct.sub_tmul, Algebra.algebraMap_eq_smul_one]
      rfl
    | add a c ha hc =>
      obtain ⟨za, hza⟩ := ha
      obtain ⟨zc, hzc⟩ := hc
      exact ⟨za + zc, by rw [map_add, hza, hzc, map_add, map_add, TensorProduct.tmul_add]; abel⟩
  obtain ⟨z, hz⟩ := hrange y
  rw [show Algebra.TensorProduct.map α.q (AlgHom.id R₀ B₀) y = 0 from hy, map_zero,
    TensorProduct.tmul_zero, sub_zero] at hz
  have hμ : ∀ z, σ (tau α p hs z) = TensorProduct.lid R B (LinearMap.rTensor B I.subtype z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul i b => rw [tau_tmul, hσ, jj_k]; simp
    | add a c ha hc => rw [map_add, map_add, map_add, map_add, ha, hc]
  have hinj : Function.Injective (fun z ↦ TensorProduct.lid R B (LinearMap.rTensor B I.subtype z)) :=
    (TensorProduct.lid R B).injective.comp
      (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective)
  have hz0 : z = 0 := hinj (by
    show TensorProduct.lid R B (LinearMap.rTensor B I.subtype z) =
      TensorProduct.lid R B (LinearMap.rTensor B I.subtype 0)
    rw [map_zero, map_zero, ← hμ, hz, h0])
  rw [← hz, hz0, map_zero]
