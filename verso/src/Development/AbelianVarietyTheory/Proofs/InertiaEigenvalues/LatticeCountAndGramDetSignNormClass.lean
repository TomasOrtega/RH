import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem

noncomputable section

namespace GlobalTheory.UnitLemma.NormClass

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit Polynomial

section Orb

variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A]

def mulLatEquiv (u : Aˣ) : Submodule O A ≃ Submodule O A where
  toFun := mulLat O (u : A)
  invFun := mulLat O ((u⁻¹ : Aˣ) : A)
  left_inv L := by
    ext y
    simp only [mem_mulLat, inv_inv, Units.inv_mul_cancel_left]
  right_inv L := by
    ext y
    simp only [mem_mulLat, inv_inv, Units.mul_inv_cancel_left]

end Orb

variable {K : UQ}

open Polynomial in
variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A] in
/- English proof (translation)
Unfold `_root_.GlobalTheory.UnitLemma.IsLat at hL ⊢`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `_root_.GlobalTheory.UnitLemma.mulLat`. Conclude with `hL.1.map _`. Unfold `_root_.GlobalTheory.UnitLemma.mulLat`.

Rewrite using `[Submodule.map_coe]`. Establish `e : (⇑(LinearMap.mulLeft O (u : A))) = ⇑(LinearMap.mulLeft E (u : A))` using `rfl`. Rewrite using `[e, Submodule.span_image, hL.2, Submodule.map_top, LinearMap.range_eq_top]`. Introduce `z`. Conclude with `⟨((u⁻¹ : Aˣ) : A) * z, by simp⟩`.
-/
private theorem isLat_mulLat_unit {E : Type} [Field E] [Algebra E A] (u : Aˣ) (L : Submodule O A)
    (hL : _root_.GlobalTheory.UnitLemma.IsLat O E L) : _root_.GlobalTheory.UnitLemma.IsLat O E (_root_.GlobalTheory.UnitLemma.mulLat O (u : A) L) := by
  unfold _root_.GlobalTheory.UnitLemma.IsLat at hL ⊢
  refine ⟨?_, ?_⟩
  · unfold _root_.GlobalTheory.UnitLemma.mulLat
    exact hL.1.map _
  · unfold _root_.GlobalTheory.UnitLemma.mulLat
    rw [Submodule.map_coe]
    have e : (⇑(LinearMap.mulLeft O (u : A))) = ⇑(LinearMap.mulLeft E (u : A)) := rfl
    rw [e, Submodule.span_image, hL.2, Submodule.map_top, LinearMap.range_eq_top]
    intro z
    exact ⟨((u⁻¹ : Aˣ) : A) * z, by simp⟩

open Polynomial in
variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A] in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h z hz`. Conclude with `h _ ((_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat u L _).mpr (by rwa [Units.inv_mul_cancel_left]))`. Introduce `h z hz`. Use `h _ ((_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat u L z).mp hz)` as an intermediate fact.

Rewrite `this` using `[Units.mul_inv_cancel_left]`. Then use the resulting hypothesis.
-/
private theorem forall_mem_mulLat_unit_iff (u : Aˣ) (L : Submodule O A) (P : A → Prop) :
    (∀ z ∈ _root_.GlobalTheory.UnitLemma.mulLat O (u : A) L, P z) ↔ ∀ z ∈ L, P (u * z) := by
  constructor
  · intro h z hz
    exact h _ ((_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat u L _).mpr (by rwa [Units.inv_mul_cancel_left]))
  · intro h z hz
    have := h _ ((_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat u L z).mp hz)
    rwa [Units.mul_inv_cancel_left] at this

open Polynomial in
variable {K : _root_.GlobalTheory.UnitLemma.UQ} in
/- English proof (translation)
Unfold `_root_.GlobalTheory.UnitLemma.InvAlg.herm`. Simplify using `only [map_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem herm_mul_unit_sigma (B : _root_.GlobalTheory.UnitLemma.InvAlg K) (x : B.A) (u : B.Aˣ) (a b : B.A) :
    B.herm (x * (u * B.σ (u : B.A))) a b = B.herm x (u * a) (u * b) := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.herm
  simp only [map_mul]
  congr 1
  ring

open Polynomial in
variable {K : _root_.GlobalTheory.UnitLemma.UQ} in
/- English proof (translation)
Unfold `_root_.GlobalTheory.UnitLemma.InvAlg.X`. Simplify using `only [Set.mem_setOf_eq]`. Use `and_congr ?_ (and_congr ?_ ?_)` and prove the remaining obligations. Use `⟨isLat_mulLat_unit u L, fun h => ?_⟩` and prove the remaining obligations. Use `isLat_mulLat_unit (u⁻¹) _ h` as an intermediate fact.

Establish `hL : _root_.GlobalTheory.UnitLemma.mulLat K.O ((u⁻¹ : B.Aˣ) : B.A) (_root_.GlobalTheory.UnitLemma.mulLat K.O (u : B.A) L) = L` using `(_root_.GlobalTheory.UnitLemma.NormClass.mulLatEquiv u).left_inv L`. Rewrite `this` using `[hL]`. Then use the resulting hypothesis. Rewrite using `[forall_mem_mulLat_unit_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h z hz`.

Rewrite using `[_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat, mul_left_comm, Units.inv_mul_cancel_left]`. Conclude with `h z hz`. Introduce `h z hz`. Use `h z hz` as an intermediate fact. Rewrite `this` using `[_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat, mul_left_comm, Units.inv_mul_cancel_left]`. Then use the resulting hypothesis.

Prove the components needed by the constructor for the conclusion. Introduce `h w`. Rewrite using `[_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat, h, forall_mem_mulLat_unit_iff]`. Simplify using `only [herm_mul_unit_sigma, Units.mul_inv_cancel_left]`. Introduce `h w`.

Use `h (u * w)` as an intermediate fact. Rewrite `this` using `[_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat, Units.inv_mul_cancel_left, forall_mem_mulLat_unit_iff]`. Rewrite using `[this]`. Simplify using `only [herm_mul_unit_sigma]`.
-/
private theorem mem_X_mul_unit_sigma_iff (B : _root_.GlobalTheory.UnitLemma.InvAlg K) (x : B.A) (u : B.Aˣ)
    (L : Submodule K.O B.A) :
    L ∈ B.X (x * (u * B.σ (u : B.A))) ↔ _root_.GlobalTheory.UnitLemma.mulLat K.O (u : B.A) L ∈ B.X x := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.X
  simp only [Set.mem_setOf_eq]
  refine and_congr ?_ (and_congr ?_ ?_)
  · refine ⟨isLat_mulLat_unit u L, fun h => ?_⟩
    have := isLat_mulLat_unit (u⁻¹) _ h
    have hL : _root_.GlobalTheory.UnitLemma.mulLat K.O ((u⁻¹ : B.Aˣ) : B.A) (_root_.GlobalTheory.UnitLemma.mulLat K.O (u : B.A) L) = L :=
      (_root_.GlobalTheory.UnitLemma.NormClass.mulLatEquiv u).left_inv L
    rwa [hL] at this
  · rw [forall_mem_mulLat_unit_iff]
    constructor
    · intro h z hz
      rw [_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat, mul_left_comm, Units.inv_mul_cancel_left]
      exact h z hz
    · intro h z hz
      have := h z hz
      rwa [_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat, mul_left_comm, Units.inv_mul_cancel_left] at this
  · constructor
    · intro h w
      rw [_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat, h, forall_mem_mulLat_unit_iff]
      simp only [herm_mul_unit_sigma, Units.mul_inv_cancel_left]
    · intro h w
      have := h (u * w)
      rw [_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat, Units.inv_mul_cancel_left, forall_mem_mulLat_unit_iff] at this
      rw [this]
      simp only [herm_mul_unit_sigma]

open Polynomial in
variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A] in
/- English proof (translation)
Use extensionality with `y`. Simplify using `only [_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat]`. Rewrite using `[mul_left_comm]`.
-/
private theorem mulLat_unit_comm (u t : Aˣ) (L : Submodule O A) :
    _root_.GlobalTheory.UnitLemma.mulLat O (u : A) (_root_.GlobalTheory.UnitLemma.mulLat O (t : A) L) =
      _root_.GlobalTheory.UnitLemma.mulLat O (t : A) (_root_.GlobalTheory.UnitLemma.mulLat O (u : A) L) := by
  ext y
  simp only [_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat]
  rw [mul_left_comm]

open Polynomial in
variable {K : _root_.GlobalTheory.UnitLemma.UQ} in

/- English proof (translation)
Introduce `K B x u`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `_root_.GlobalTheory.UnitLemma.InvAlg.N _root_.GlobalTheory.UnitLemma.orbSum`. Simplify using `only [one_mul]`. Set `wt : Submodule K.O B.A → ℚ` to `fun L => ((_root_.GlobalTheory.UnitLemma.stabLat K.O L ⊓ B.T).relIndex (_root_.GlobalTheory.UnitLemma.intUnits K.O B.A ⊓ B.T) : ℚ)`.

Establish `hwt : ∀ (t : B.Aˣ) (L : Submodule K.O B.A), wt (_root_.GlobalTheory.UnitLemma.mulLat K.O (t : B.A) L) = wt L`. Introduce `t L`. Simplify using `only [wt, _root_.GlobalTheory.UnitLemma.Orbit.stabLat_mulLat]`. Establish `hrel : ∀ (X : Set (Submodule K.O B.A)) (a b : X), (∃ t ∈ B.T, (b : Submodule K.O B.A) = _root_.GlobalTheory.UnitLemma.mulLat K.O (t : B.A) a) → wt a = wt b`. Introduce and unpack `X a b ⟨t, -, h⟩`.

Rewrite using `[h, hwt]`. Establish `hout : ∀ (X : Set (Submodule K.O B.A)) (o : Quot (fun L M : X => ∃ t ∈ B.T, (M : Submodule K.O B.A) = _root_.GlobalTheory.UnitLemma.mulLat K.O (t : B.A) L)), wt ((Quot.out o : X) : Submodule K.O B.A) = Quot.lift (fun a : X => wt a) (hrel X) o`. Introduce `X o`. Use `conv_rhs => rw [← Quot.out_eq o]`. Use `show (∑ᶠ o : Quot (fun L M : B.X (x * (u * B.σ (u : B.A))) => ∃ t ∈ B.T, (M : Submodule K.O B.A) = _root_.GlobalTheory.UnitLemma.mulLat K.O (t : B.A) L), wt ((Quot.out o : B.X (x * (u * B.σ (u : B.A)))) : Submodule K.O B.A)) = ∑ᶠ o : Quot (fun L M : B.X x => ∃ t ∈ B.T, (M : Submo …`.

Simplify using `only [hout]`. Establish `hφ : ∀ L : B.X (x * (u * B.σ (u : B.A))), _root_.GlobalTheory.UnitLemma.mulLat K.O (u : B.A) L ∈ B.X x` using `fun L => (mem_X_mul_unit_sigma_iff B x u L).mp L.2`. Establish `hψ : ∀ M : B.X x, _root_.GlobalTheory.UnitLemma.mulLat K.O ((u⁻¹ : B.Aˣ) : B.A) M ∈ B.X (x * (u * B.σ (u : B.A)))`. Introduce `M`. Use `(mem_X_mul_unit_sigma_iff B x u _).mpr ?_` and prove the remaining obligations.

Establish `hM : _root_.GlobalTheory.UnitLemma.mulLat K.O (u : B.A) (_root_.GlobalTheory.UnitLemma.mulLat K.O ((u⁻¹ : B.Aˣ) : B.A) M) = M` using `(_root_.GlobalTheory.UnitLemma.NormClass.mulLatEquiv u).right_inv (M : Submodule K.O B.A)`. Rewrite using `[hM]`. Conclude with `M.2`. Set `e : Quot (fun L M : B.X (x * (u * B.σ (u : B.A))) => ∃ t ∈ B.T, (M : Submodule K.O B.A) = _root_.GlobalTheory.UnitLemma.mulLat K.O (t : B.A) L) ≃ Quot (fun L M : B.X x => ∃ t ∈ B.T, (M : Submodule K.O B.A) = _root_.GlobalTheory.UnitLemma.mulLat K.O (t : B.A) L)` to `{ toFun := Quot.map (fun L => ⟨_, hφ L⟩) (by`. Introduce and unpack `a b ⟨t, ht, h⟩`.

Use `⟨t, ht, ?_⟩` and prove the remaining obligations. Use `show _root_.GlobalTheory.UnitLemma.mulLat K.O (u : B.A) b = _`. Rewrite using `[h]`. Conclude with `mulLat_unit_comm u t (a : Submodule K.O B.A))`. Use `invFun := Quot.map (fun M => ⟨_, hψ M⟩) (by`.

Introduce and unpack `a b ⟨t, ht, h⟩`. Use `⟨t, ht, ?_⟩` and prove the remaining obligations. Use `show _root_.GlobalTheory.UnitLemma.mulLat K.O ((u⁻¹ : B.Aˣ) : B.A) b = _`. Rewrite using `[h]`. Conclude with `mulLat_unit_comm u⁻¹ t (a : Submodule K.O B.A))`.

Use `left_inv := by`. Introduce `o`. Proceed by induction on `o using Quot.ind with`. Consider the case `mk L => exact congrArg (Quot.mk _) (Subtype.ext ((_root_.GlobalTheory.UnitLemma.NormClass.mulLatEquiv u).left_inv (L : Submodule K.O B.A)))`. Use `right_inv := by`.

Introduce `o`. Proceed by induction on `o using Quot.ind with`. Consider the case `mk M => exact congrArg (Quot.mk _) (Subtype.ext ((_root_.GlobalTheory.UnitLemma.NormClass.mulLatEquiv u).right_inv (M : Submodule K.O B.A))) }`. Rewrite using `[← finsum_comp_equiv e]`. Use `finsum_congr fun o => ?_` and prove the remaining obligations.

Proceed by induction on `o using Quot.ind with`. Consider the case `mk L => exact (hwt u (L : Submodule K.O B.A)).symm`. Set `φ : B.A ≃ₗ[K.E] B.A` to `{ LinearMap.mulLeft K.E (u : B.A) with invFun := fun z => ((u⁻¹ : B.Aˣ) : B.A) * z left_inv := fun z => Units.inv_mul_cancel_left u z right_inv := fun z => Units.mul_inv_cancel_left u z }`. Establish `e : B.gramDet (x * (u * B.σ (u : B.A))) = (Matrix.of fun i j => B.herm x (((Module.finBasis K.E B.A).map φ) i) (((Module.finBasis K.E B.A).map φ) j)).det`. Unfold `_root_.GlobalTheory.UnitLemma.InvAlg.gramDet`.

Simplify using `only [herm_mul_unit_sigma, Module.Basis.map_apply]`. Both sides reduce to the same expression. Rewrite using `[e, _root_.GlobalTheory.UnitLemma.Orbit.eta_gram]`.
-/
theorem _root_.GlobalTheory.UnitLemma.NormClass.N_norm_class : ∀ (K : _root_.GlobalTheory.UnitLemma.UQ) (B : _root_.GlobalTheory.UnitLemma.InvAlg K) (x : B.A) (u : B.Aˣ),
    B.N (x * (u * B.σ (u : B.A))) = B.N x ∧
      K.eta (B.gramDet (x * (u * B.σ (u : B.A)))) = K.eta (B.gramDet x) := by
  intro K B x u
  refine ⟨?_, ?_⟩
  · unfold _root_.GlobalTheory.UnitLemma.InvAlg.N _root_.GlobalTheory.UnitLemma.orbSum
    simp only [one_mul]
    let wt : Submodule K.O B.A → ℚ := fun L =>
      ((_root_.GlobalTheory.UnitLemma.stabLat K.O L ⊓ B.T).relIndex (_root_.GlobalTheory.UnitLemma.intUnits K.O B.A ⊓ B.T) : ℚ)
    have hwt : ∀ (t : B.Aˣ) (L : Submodule K.O B.A), wt (_root_.GlobalTheory.UnitLemma.mulLat K.O (t : B.A) L) = wt L := by
      intro t L
      simp only [wt, _root_.GlobalTheory.UnitLemma.Orbit.stabLat_mulLat]
    have hrel : ∀ (X : Set (Submodule K.O B.A)) (a b : X),
        (∃ t ∈ B.T, (b : Submodule K.O B.A) = _root_.GlobalTheory.UnitLemma.mulLat K.O (t : B.A) a) → wt a = wt b := by
      rintro X a b ⟨t, -, h⟩
      rw [h, hwt]
    have hout : ∀ (X : Set (Submodule K.O B.A)) (o : Quot (fun L M : X => ∃ t ∈ B.T, (M : Submodule K.O B.A) = _root_.GlobalTheory.UnitLemma.mulLat K.O (t : B.A) L)),
        wt ((Quot.out o : X) : Submodule K.O B.A) = Quot.lift (fun a : X => wt a) (hrel X) o := by
      intro X o
      conv_rhs => rw [← Quot.out_eq o]
    show (∑ᶠ o : Quot (fun L M : B.X (x * (u * B.σ (u : B.A))) => ∃ t ∈ B.T, (M : Submodule K.O B.A) = _root_.GlobalTheory.UnitLemma.mulLat K.O (t : B.A) L), wt ((Quot.out o : B.X (x * (u * B.σ (u : B.A)))) : Submodule K.O B.A)) =
      ∑ᶠ o : Quot (fun L M : B.X x => ∃ t ∈ B.T, (M : Submodule K.O B.A) = _root_.GlobalTheory.UnitLemma.mulLat K.O (t : B.A) L), wt ((Quot.out o : B.X x) : Submodule K.O B.A)
    simp only [hout]
    have hφ : ∀ L : B.X (x * (u * B.σ (u : B.A))), _root_.GlobalTheory.UnitLemma.mulLat K.O (u : B.A) L ∈ B.X x :=
      fun L => (mem_X_mul_unit_sigma_iff B x u L).mp L.2
    have hψ : ∀ M : B.X x, _root_.GlobalTheory.UnitLemma.mulLat K.O ((u⁻¹ : B.Aˣ) : B.A) M ∈ B.X (x * (u * B.σ (u : B.A))) := by
      intro M
      refine (mem_X_mul_unit_sigma_iff B x u _).mpr ?_
      have hM : _root_.GlobalTheory.UnitLemma.mulLat K.O (u : B.A) (_root_.GlobalTheory.UnitLemma.mulLat K.O ((u⁻¹ : B.Aˣ) : B.A) M) = M :=
        (_root_.GlobalTheory.UnitLemma.NormClass.mulLatEquiv u).right_inv (M : Submodule K.O B.A)
      rw [hM]
      exact M.2
    let e : Quot (fun L M : B.X (x * (u * B.σ (u : B.A))) => ∃ t ∈ B.T, (M : Submodule K.O B.A) = _root_.GlobalTheory.UnitLemma.mulLat K.O (t : B.A) L) ≃
        Quot (fun L M : B.X x => ∃ t ∈ B.T, (M : Submodule K.O B.A) = _root_.GlobalTheory.UnitLemma.mulLat K.O (t : B.A) L) :=
      { toFun := Quot.map (fun L => ⟨_, hφ L⟩) (by
          rintro a b ⟨t, ht, h⟩
          refine ⟨t, ht, ?_⟩
          show _root_.GlobalTheory.UnitLemma.mulLat K.O (u : B.A) b = _
          rw [h]
          exact mulLat_unit_comm u t (a : Submodule K.O B.A))
        invFun := Quot.map (fun M => ⟨_, hψ M⟩) (by
          rintro a b ⟨t, ht, h⟩
          refine ⟨t, ht, ?_⟩
          show _root_.GlobalTheory.UnitLemma.mulLat K.O ((u⁻¹ : B.Aˣ) : B.A) b = _
          rw [h]
          exact mulLat_unit_comm u⁻¹ t (a : Submodule K.O B.A))
        left_inv := by
          intro o
          induction o using Quot.ind with
          | mk L => exact congrArg (Quot.mk _) (Subtype.ext ((_root_.GlobalTheory.UnitLemma.NormClass.mulLatEquiv u).left_inv (L : Submodule K.O B.A)))
        right_inv := by
          intro o
          induction o using Quot.ind with
          | mk M => exact congrArg (Quot.mk _) (Subtype.ext ((_root_.GlobalTheory.UnitLemma.NormClass.mulLatEquiv u).right_inv (M : Submodule K.O B.A))) }
    rw [← finsum_comp_equiv e]
    refine finsum_congr fun o => ?_
    induction o using Quot.ind with
    | mk L => exact (hwt u (L : Submodule K.O B.A)).symm
  · let φ : B.A ≃ₗ[K.E] B.A :=
      { LinearMap.mulLeft K.E (u : B.A) with
        invFun := fun z => ((u⁻¹ : B.Aˣ) : B.A) * z
        left_inv := fun z => Units.inv_mul_cancel_left u z
        right_inv := fun z => Units.mul_inv_cancel_left u z }
    have e : B.gramDet (x * (u * B.σ (u : B.A))) =
        (Matrix.of fun i j => B.herm x (((Module.finBasis K.E B.A).map φ) i)
          (((Module.finBasis K.E B.A).map φ) j)).det := by
      unfold _root_.GlobalTheory.UnitLemma.InvAlg.gramDet
      simp only [herm_mul_unit_sigma, Module.Basis.map_apply]
      rfl
    rw [e, _root_.GlobalTheory.UnitLemma.Orbit.eta_gram]

end GlobalTheory.UnitLemma.NormClass
