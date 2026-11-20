import Formalism.LocalToGlobal.GlobalTheory.BlockActions.InJSymRestrict
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ClassMapEstimateOfPartial

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix
open scoped TensorProduct
open IsDedekindDomain

/- English proof (translation)
Use extensionality with `a b`. Establish `h1` using `h (Pi.single a 1) (Pi.single b 1)`. Rewrite `h1` using `[Formalism.L2.GlobalTheoryTheory.Comp.hform_mulVec_rect]`. Simplify `h1` using `[hform, Pi.single_apply, apply_ite, ite_mul, mul_ite, Finset.sum_ite_eq', Finset.sum_ite_eq]`.
-/
theorem unitary_of_hform {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (J δ : Matrix (Fin n) (Fin n) E)
    (h : ∀ x y, hform σ J (δ *ᵥ x) (δ *ᵥ y) = hform σ J x y) : cT σ δ * J * δ = J := by
  ext a b
  have h1 := h (Pi.single a 1) (Pi.single b 1)
  rw [Formalism.L2.GlobalTheoryTheory.Comp.hform_mulVec_rect] at h1
  simpa [hform, Pi.single_apply, apply_ite, ite_mul, mul_ite, Finset.sum_ite_eq', Finset.sum_ite_eq] using h1

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

/- English proof (translation)
Take `⟨P, hP1, -⟩` from `exists_projP Tf`. Establish `hm : (iXm D).map (RingHom.id D.host.E) = iXm D` using `by ext i j; rfl`. Establish `h1 : HMul.hMul Γ (iXm D) = HMul.hMul (iXm D) δ` using `by have := hE.1; rw [hm] at this; exact this`. Establish `hQ : HMul.hMul (HMul.hMul Γ⁻¹ (iXm D)) δ = iXm D`. Rewrite using `[Matrix.mul_assoc, ← h1, ← Matrix.mul_assoc, nonsing_inv_mul _ hΓ, Matrix.one_mul]`.

Establish `hl : HMul.hMul (HMul.hMul P (HMul.hMul Γ⁻¹ (iXm D))) δ = 1`. Rewrite using `[Matrix.mul_assoc, hQ, hP1]`. Conclude with `Matrix.isUnit_det_of_left_inverse hl`.
-/
theorem isUnit_of_extE (Tf : FormsTiedSym D u Ch chOf) (δ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (Γ : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) (hΓ : IsUnit Γ.det)
    (hE : IsExt D Tf.til.z0 (RingHom.id D.host.E) δ Γ) : IsUnit δ.det := by
  obtain ⟨P, hP1, -⟩ := exists_projP Tf
  have hm : (iXm D).map (RingHom.id D.host.E) = iXm D := by ext i j; rfl
  have h1 : HMul.hMul Γ (iXm D) = HMul.hMul (iXm D) δ := by have := hE.1; rw [hm] at this; exact this
  have hQ : HMul.hMul (HMul.hMul Γ⁻¹ (iXm D)) δ = iXm D := by
    rw [Matrix.mul_assoc, ← h1, ← Matrix.mul_assoc, nonsing_inv_mul _ hΓ, Matrix.one_mul]
  have hl : HMul.hMul (HMul.hMul P (HMul.hMul Γ⁻¹ (iXm D))) δ = 1 := by
    rw [Matrix.mul_assoc, hQ, hP1]
  exact Matrix.isUnit_det_of_left_inverse hl

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Introduce `c c' h`. Take `⟨δ, k, G, hδE, hδi, hkE, hG, hy⟩` from `til_eq_level Tf (crdFacts_of Tf) hSD hdeg v c c' h`. Establish `hku` using `lev_isUnit Tf k G hkE`. Establish `hΓ : IsUnit ((Tf.til.ga c').1.1 * ((Tf.til.ga c)⁻¹).1.1).det`. Rewrite using `[← Units.val_mul]`.

Conclude with `(Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)`. Establish `hδu` using `isUnit_of_extE Tf δ _ hΓ hδE`. Use `set Δ : GL (Fin (D.R.N D.R.m - 1)) D.host.E := ((Matrix.isUnit_iff_isUnit_det δ).mpr hδu).unit with hΔdef`. Establish `hΔv : (Δ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) = δ` using `IsUnit.unit_spec _`. Establish `hΔ : Δ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramP D)` using `by show cT _ (Δ : Matrix _ _ _) * gramP D * (Δ : Matrix _ _ _) = gramP D`.

Rewrite using `[hΔv]`. Conclude with `unitary_of_hform _ _ _ hδi`. Use `set K : GL (Fin (D.R.N D.R.m - 1)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := ((Matrix.isUnit_iff_isUnit_det k).mpr hku).unit with hKdef`. Establish `hKv : K.1 = k` using `IsUnit.unit_spec _`. Establish `hK : K ∈ Tf.clsP.lev.U` using `lev_mem Tf K G (by rw [hKv]; exact hkE) hG`.

Establish `hKU : K ∈ UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)` using `((Tf.clsP.lev.U_eq K).1 hK).1`. Establish `hc : (inclE (F` using `D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)).comp (sigD D : D.host.E →+* D.host.E) = (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)).comp (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by`. Use extensionality with `e`. Simplify using `[sigR, inclE, Algebra.TensorProduct.includeLeftRingHom_apply]`. Establish `hrU : bc (inclE (F` using `D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) Δ ∈ UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := Formalism.UG.P.base_change_mem_holds _ _ _ _ _ _ hc _ Δ hΔ`.

Apply `Tf.clsP.y_bij.1` to reduce the goal to its premises. Use `show (Quotient.mk'' (Tf.clsP.y c) : Cls Tf.clsP.lev) = Quotient.mk'' (Tf.clsP.y c')`. Apply `(DoubleCoset.eq _ _ _ _).2` to reduce the goal to its premises. Use `⟨⟨_, hrU⟩, ?_, ⟨K⁻¹, inv_mem hKU⟩, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨Δ, hΔ, rfl⟩)`.

Conclude with `Subgroup.mem_subgroupOf.2 (inv_mem hK)`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Establish `hKi : k * (K⁻¹).1 = 1`. Rewrite using `[← hKv, ← Units.val_mul, mul_inv_cancel, Units.val_one]`.

Establish `hbc : ((bc (inclE (F` using `D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) Δ : GL _ _) : Matrix _ _ _) = δ.map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by`. Rewrite using `[← hΔv]`. Both sides reduce to the same expression. Establish `e : (Tf.clsP.y c').1.1 = δ.map (inclE (F` using `D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * (Tf.clsP.y c).1.1 * (K⁻¹).1 := by`. Rewrite using `[← hy, Matrix.mul_assoc, hKi, Matrix.mul_one]`.

Rewrite using `[e, ← hbc]`. Both sides reduce to the same expression.
-/
theorem til_injective (Tf : FormsTiedSym D u Ch chOf)
    (hSD : ∀ c, dualSet (sigD D : D.host.E →+* D.host.E) (gramP D) (Tf.clsP.lat c) = (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)))
    (hdeg : Module.finrank ℚ D.host.E < (D.mem u).A.T - 1) (v : (D.mem u).A.vT) :
    Function.Injective (D.fm u).til := by
  intro c c' h
  obtain ⟨δ, k, G, hδE, hδi, hkE, hG, hy⟩ := til_eq_level Tf (crdFacts_of Tf) hSD hdeg v c c' h
  have hku := lev_isUnit Tf k G hkE
  have hΓ : IsUnit ((Tf.til.ga c').1.1 * ((Tf.til.ga c)⁻¹).1.1).det := by
    rw [← Units.val_mul]
    exact (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)
  have hδu := isUnit_of_extE Tf δ _ hΓ hδE
  set Δ : GL (Fin (D.R.N D.R.m - 1)) D.host.E := ((Matrix.isUnit_iff_isUnit_det δ).mpr hδu).unit with hΔdef
  have hΔv : (Δ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) = δ := IsUnit.unit_spec _
  have hΔ : Δ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramP D) := by
    show cT _ (Δ : Matrix _ _ _) * gramP D * (Δ : Matrix _ _ _) = gramP D
    rw [hΔv]; exact unitary_of_hform _ _ _ hδi
  set K : GL (Fin (D.R.N D.R.m - 1)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := ((Matrix.isUnit_iff_isUnit_det k).mpr hku).unit with hKdef
  have hKv : K.1 = k := IsUnit.unit_spec _
  have hK : K ∈ Tf.clsP.lev.U := lev_mem Tf K G (by rw [hKv]; exact hkE) hG
  have hKU : K ∈ UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := ((Tf.clsP.lev.U_eq K).1 hK).1
  have hc : (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)).comp (sigD D : D.host.E →+* D.host.E) =
      (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)).comp (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
    ext e
    simp [sigR, inclE, Algebra.TensorProduct.includeLeftRingHom_apply]
  have hrU : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) Δ ∈ UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
    Formalism.UG.P.base_change_mem_holds _ _ _ _ _ _ hc _ Δ hΔ
  apply Tf.clsP.y_bij.1
  show (Quotient.mk'' (Tf.clsP.y c) : Cls Tf.clsP.lev) = Quotient.mk'' (Tf.clsP.y c')
  apply (DoubleCoset.eq _ _ _ _).2
  refine ⟨⟨_, hrU⟩, ?_, ⟨K⁻¹, inv_mem hKU⟩, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨Δ, hΔ, rfl⟩)
  · exact Subgroup.mem_subgroupOf.2 (inv_mem hK)
  · apply Subtype.ext
    apply Units.ext
    have hKi : k * (K⁻¹).1 = 1 := by
      rw [← hKv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hbc : ((bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) Δ : GL _ _) : Matrix _ _ _) = δ.map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
      rw [← hΔv]; rfl
    have e : (Tf.clsP.y c').1.1 = δ.map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * (Tf.clsP.y c).1.1 * (K⁻¹).1 := by
      rw [← hy, Matrix.mul_assoc, hKi, Matrix.mul_one]
    rw [e, ← hbc]
    rfl

/- English proof (translation)
Introduce `D u Ch chOf Tf` and use `til_injective Tf (hSD D u Ch chOf Tf) (hdeg D u Ch chOf Tf) (hv D u Ch chOf Tf).some`.
-/
theorem class_injective_of_degree
    (hSD : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf),
      ∀ c, dualSet (sigD D : D.host.E →+* D.host.E) (gramP D) (Tf.clsP.lat c) = (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)))
    (hdeg : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i), FormsTiedSym D u Ch chOf →
      Module.finrank ℚ D.host.E < (D.mem u).A.T - 1)
    (hv : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i), FormsTiedSym D u Ch chOf →
      Nonempty (D.mem u).A.vT) :
    ClassMapInjective := fun D u Ch chOf Tf =>
  til_injective Tf (hSD D u Ch chOf Tf) (hdeg D u Ch chOf Tf) (hv D u Ch chOf Tf).some

/- English proof (translation)
Rewrite using `[← Fintype.card_pos_iff, (D.mem u).A.card_vT]`. Simplify using `only [Ranks.f, Ranks.n]`. Check the signs of the components of the expression.
-/
theorem vT_nonempty (D : D7) (u : D.what₂.Word) : Nonempty (D.mem u).A.vT := by
  rw [← Fintype.card_pos_iff, (D.mem u).A.card_vT]
  simp only [Ranks.f, Ranks.n]
  positivity

/- English proof (translation)
The claim follows from `class_injective_of_degree hSD hdeg (fun D u _ _ _ => vT_nonempty D u)`.
-/
theorem classMapInjective_of_finrank_lt
    (hSD : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf),
      ∀ c, dualSet (sigD D : D.host.E →+* D.host.E) (gramP D) (Tf.clsP.lat c) = (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)))
    (hdeg : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i), FormsTiedSym D u Ch chOf →
      Module.finrank ℚ D.host.E < (D.mem u).A.T - 1) :
    ClassMapInjective :=
  class_injective_of_degree hSD hdeg (fun D u _ _ _ => vT_nonempty D u)

end Formalism.L2.GlobalTheoryTheory.Br
