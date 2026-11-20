import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CardNuGZmod
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.GlRedEqOneIff

noncomputable section

namespace MassDataIdxStImB

open Matrix Formalism.FourierDecayAlt.S3 MassDataIdxStIm MassDataIdxRed
open Formalism.DoubleCosetMeasures (IsUpUni)

section Lift

variable {R S : Type} [CommRing R] [CommRing S] (π : R →+* S) (hπ : Function.Surjective π)

open Classical in

def lift (s : S) : R := if s = 0 then 0 else if s = 1 then 1 else Function.surjInv hπ s

/- English proof (translation)
Simplify using `[lift]`.
-/
theorem lift_zero : lift π hπ 0 = 0 := by
  simp [lift]

/- English proof (translation)
Simplify using `[lift]`.
-/
theorem lift_one [Nontrivial S] : lift π hπ 1 = 1 := by
  simp [lift]

/- English proof (translation)
Unfold `lift`. Use `split_ifs with h0 h1`. Rewrite using `[h0, map_zero]`. Rewrite using `[h1, map_one]`. Conclude with `Function.surjInv_eq hπ s`.
-/
theorem π_lift (s : S) : π (lift π hπ s) = s := by
  unfold lift
  split_ifs with h0 h1
  · rw [h0, map_zero]
  · rw [h1, map_one]
  · exact Function.surjInv_eq hπ s

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, π_lift]`.
-/
theorem map_lift {m n : Type} (x : Matrix m n S) : (x.map (lift π hπ)).map π = x := by
  ext i j
  simp only [Matrix.map_apply, π_lift]

end Lift

section Par

variable {A B : Type} [CommRing A] [CommRing B] {r k : ℕ}

/- English proof (translation)
Take `⟨hu, hd⟩` from `hh`. Use `⟨?_, fun a => by simp [Matrix.map_apply, hd a, h1]⟩` and prove the remaining obligations. Introduce `i j hij`. Simplify using `[Matrix.map_apply, hu hij, h0]`.
-/
theorem isUpUni_map (f : A → B) (h0 : f 0 = 0) (h1 : f 1 = 1) {n : ℕ} {h : Matrix (Fin n) (Fin n) A}
    (hh : IsUpUni h) : IsUpUni (h.map f) := by
  obtain ⟨hu, hd⟩ := hh
  refine ⟨?_, fun a => by simp [Matrix.map_apply, hd a, h1]⟩
  intro i j hij
  simp [Matrix.map_apply, hu hij, h0]

/- English proof (translation)
Simplify using `only [midEmb, Matrix.fromBlocks_map, Matrix.map_zero f h0, Matrix.map_one f h0 h1]`.
-/
theorem midEmb_map (f : A → B) (h0 : f 0 = 0) (h1 : f 1 = 1) (h : Matrix (Fin k) (Fin k) A) :
    (midEmb h).map f = midEmb (h.map f) := by
  simp only [midEmb, Matrix.fromBlocks_map, Matrix.map_zero f h0, Matrix.map_one f h0 h1]

/- English proof (translation)
Take `⟨h11, h33, h21, h31, h32, h, hP, h22⟩` from `hx`. Use `⟨isUpUni_map f h0 h1 h11, isUpUni_map f h0 h1 h33, ?_, ?_, ?_, h.map f, hPP h hP, ?_⟩` and prove the remaining obligations. Use `show (b21 x).map f = 0`. Rewrite using `[h21, Matrix.map_zero f h0]`. Use `show (b31 x).map f = 0`.

Rewrite using `[h31, Matrix.map_zero f h0]`. Use `show (b32 x).map f = 0`. Rewrite using `[h32, Matrix.map_zero f h0]`. Use `show (b22 x).map f = midEmb (h.map f)`. Rewrite using `[h22, midEmb_map f h0 h1]`.
-/
theorem par_map (f : A → B) (h0 : f 0 = 0) (h1 : f 1 = 1) {P : Matrix (Fin k) (Fin k) A → Prop}
    {P' : Matrix (Fin k) (Fin k) B → Prop} (hPP : ∀ h, P h → P' (h.map f))
    {x : Matrix (Idx r k) (Idx r k) A} (hx : Par P x) : Par P' (x.map f) := by
  obtain ⟨h11, h33, h21, h31, h32, h, hP, h22⟩ := hx
  refine ⟨isUpUni_map f h0 h1 h11, isUpUni_map f h0 h1 h33, ?_, ?_, ?_, h.map f, hPP h hP, ?_⟩
  · show (b21 x).map f = 0
    rw [h21, Matrix.map_zero f h0]
  · show (b31 x).map f = 0
    rw [h31, Matrix.map_zero f h0]
  · show (b32 x).map f = 0
    rw [h32, Matrix.map_zero f h0]
  · show (b22 x).map f = midEmb (h.map f)
    rw [h22, midEmb_map f h0 h1]

variable [Nontrivial B] (π : A →+* B) (hπ : Function.Surjective π)

/- English proof (translation)
Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Express the relevant statement in the definitionally equal form `Par P' ((glRed π x : GL (Idx r k) B) : Matrix (Idx r k) (Idx r k) B)`. Rewrite using `[glRed_coe]`.

Conclude with `par_map π (map_zero π) (map_one π) hPP hx`. Introduce `hy`. Establish `hy' : Par P' (y : Matrix (Idx r k) (Idx r k) B)` using `hy`. Establish `hx : Par P ((y : Matrix (Idx r k) (Idx r k) B).map (lift π hπ))` using `par_map _ (lift_zero π hπ) (lift_one π hπ) hlift hy'`. Use `⟨Matrix.GeneralLinearGroup.mk'' _ (par_det hP hx), hx, ?_⟩` and prove the remaining obligations.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[glRed_coe]`. Conclude with `map_lift π hπ _`.
-/
theorem parG_map_glRed {P : Matrix (Fin k) (Fin k) A → Prop} {P' : Matrix (Fin k) (Fin k) B → Prop}
    (hP : GP P) (hP' : GP P') (hPP : ∀ h, P h → P' (h.map π))
    (hlift : ∀ h, P' h → P (h.map (lift π hπ))) :
    (parG (r := r) hP).map (glRed π) = parG (r := r) hP' := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change Par P' ((glRed π x : GL (Idx r k) B) : Matrix (Idx r k) (Idx r k) B)
    rw [glRed_coe]
    exact par_map π (map_zero π) (map_one π) hPP hx
  · intro hy
    have hy' : Par P' (y : Matrix (Idx r k) (Idx r k) B) := hy
    have hx : Par P ((y : Matrix (Idx r k) (Idx r k) B).map (lift π hπ)) :=
      par_map _ (lift_zero π hπ) (lift_one π hπ) hlift hy'
    refine ⟨Matrix.GeneralLinearGroup.mk'' _ (par_det hP hx), hx, ?_⟩
    apply Units.ext
    rw [glRed_coe]
    exact map_lift π hπ _

include hπ in

/- English proof (translation)
The claim follows from `parG_map_glRed π hπ _ _ (fun _ hh => isUpUni_map π (map_zero π) (map_one π) hh) (fun _ hh => isUpUni_map _ (lift_zero π hπ) (lift_one π hπ) hh)`.
-/
theorem nuG_map_glRed : (nuG A r k).map (glRed π) = nuG B r k :=
  parG_map_glRed π hπ _ _ (fun _ hh => isUpUni_map π (map_zero π) (map_one π) hh)
    (fun _ hh => isUpUni_map _ (lift_zero π hπ) (lift_one π hπ) hh)

end Par

/- English proof (translation)
Use `parG_map_glRed π hπ _ _ (fun h hh => ?_) (fun h hh => ?_)` and prove the remaining obligations. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `hh.map π`. Use `isUnit_of_map π hπ _ ?_` and prove the remaining obligations. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, map_lift π hπ]`.

Conclude with `hh`.
-/
theorem sG_map_glRed {A B : Type} [CommRing A] [IsLocalRing A] [Field B] {r k : ℕ} (π : A →+* B)
    (hπ : Function.Surjective π) : (sG A r k).map (glRed π) = sG B r k := by
  refine parG_map_glRed π hπ _ _ (fun h hh => ?_) (fun h hh => ?_)
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact hh.map π
  · refine isUnit_of_map π hπ _ ?_
    rw [RingHom.map_det, RingHom.mapMatrix_apply, map_lift π hπ]
    exact hh

section Grp

/- English proof (translation)
Rewrite using `[Subgroup.map_map, Subgroup.map_map]`. Use `congr 1`. Use extensionality with `x`. Simplify using `[MulAut.conj_apply, map_mul, map_inv]`.
-/
theorem map_conj {G Q : Type} [Group G] [Group Q] (f : G →* Q) (H : Subgroup G) (c : G) :
    (H.map (MulAut.conj c).toMonoidHom).map f = (H.map f).map (MulAut.conj (f c)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, map_mul, map_inv]

variable {K Q : Type} [Group K] [Group Q] (ρ : K →* Q) (S' : Subgroup K)

/- English proof (translation)
Rewrite using `[Subgroup.map_sup, (Subgroup.map_eq_bot_iff ρ.ker).2 le_rfl, sup_bot_eq]`.
-/
theorem map_sup_ker : (S' ⊔ ρ.ker).map ρ = S'.map ρ := by
  rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff ρ.ker).2 le_rfl, sup_bot_eq]

/- English proof (translation)
Use `first`. Consider the case `exact Subgroup.mem_sup_of_normal_right`. Consider the case `exact Subgroup.mem_sup_of_normal_right (s := S') (t := ρ.ker)`.
-/
theorem mem_sup_ker {x : K} : x ∈ S' ⊔ ρ.ker ↔ ∃ s ∈ S', ∃ κ ∈ ρ.ker, s * κ = x := by
  first
    | exact Subgroup.mem_sup_of_normal_right
    | exact Subgroup.mem_sup_of_normal_right (s := S') (t := ρ.ker)

/- English proof (translation)
Use extensionality with `y`. Simplify using `only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨c⁻¹ * ψ x * c, (h x).1 hx, by group⟩`.

Introduce and unpack `⟨h', hh', rfl⟩`. Take `⟨x, hx⟩` from `hψ (c * h' * c⁻¹)`. Use `⟨x, (h x).2 ?_, hx⟩` and prove the remaining obligations. Establish `e : c⁻¹ * (c * h' * c⁻¹) * c = h'` using `by group`. Rewrite using `[hx, e]`.

Conclude with `hh'`.
-/
theorem map_eq_conj (ψ : K →* Q) (hψ : Function.Surjective ψ) (S' : Subgroup K) (H : Subgroup Q) (c : Q)
    (h : ∀ x, x ∈ S' ↔ c⁻¹ * ψ x * c ∈ H) : S'.map ψ = H.map (MulAut.conj c).toMonoidHom := by
  ext y
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨c⁻¹ * ψ x * c, (h x).1 hx, by group⟩
  · rintro ⟨h', hh', rfl⟩
    obtain ⟨x, hx⟩ := hψ (c * h' * c⁻¹)
    refine ⟨x, (h x).2 ?_, hx⟩
    have e : c⁻¹ * (c * h' * c⁻¹) * c = h' := by group
    rw [hx, e]
    exact hh'

end Grp

end MassDataIdxStImB
