import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent

noncomputable section

namespace GlobalTheory.UnitLemma

open Polynomial

namespace InvAlg

variable {K : UQ} (B : InvAlg K)

/- English proof (translation)
Unfold `mulLat`. Rewrite using `[Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, rfl⟩`. Simplify `hz` using `[LinearMap.mulLeft_apply, ← mul_assoc]`.

Introduce `h`. Conclude with `⟨_, h, by simp [LinearMap.mulLeft_apply, ← mul_assoc]⟩`.
-/
theorem torusOrb_mem_mulLat_unit (u : B.Aˣ) (L : Submodule K.O B.A) (y : B.A) :
    y ∈ mulLat K.O (u : B.A) L ↔ ((u⁻¹ : B.Aˣ) : B.A) * y ∈ L := by
  unfold mulLat
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa [LinearMap.mulLeft_apply, ← mul_assoc] using hz
  · intro h
    exact ⟨_, h, by simp [LinearMap.mulLeft_apply, ← mul_assoc]⟩

/- English proof (translation)
Use extensionality with `y`. Simplify using `using torusOrb_mem_mulLat_unit B 1 L y`.
-/
theorem torusOrb_mulLat_one (L : Submodule K.O B.A) : mulLat K.O (1 : B.A) L = L := by
  ext y; simpa using torusOrb_mem_mulLat_unit B 1 L y

/- English proof (translation)
Use extensionality with `y`. Rewrite using `[torusOrb_mem_mulLat_unit, torusOrb_mem_mulLat_unit, torusOrb_mem_mulLat_unit, mul_inv_rev, Units.val_mul, mul_assoc]`.
-/
theorem torusOrb_mulLat_mul (s t : B.Aˣ) (L : Submodule K.O B.A) :
    mulLat K.O ((s : B.A)) (mulLat K.O (t : B.A) L) = mulLat K.O ((s * t : B.Aˣ) : B.A) L := by
  ext y
  rw [torusOrb_mem_mulLat_unit, torusOrb_mem_mulLat_unit, torusOrb_mem_mulLat_unit, mul_inv_rev, Units.val_mul, mul_assoc]

/- English proof (translation)
Rewrite using `[torusOrb_mulLat_mul, inv_mul_cancel, Units.val_one, torusOrb_mulLat_one]`.
-/
theorem torusOrb_mulLat_inv (t : B.Aˣ) (L : Submodule K.O B.A) :
    mulLat K.O ((t⁻¹ : B.Aˣ) : B.A) (mulLat K.O (t : B.A) L) = L := by
  rw [torusOrb_mulLat_mul, inv_mul_cancel, Units.val_one, torusOrb_mulLat_one]

/- English proof (translation)
Establish `h1 : ((t⁻¹ : B.Aˣ) : B.A) = B.σ (t : B.A)` using `Units.inv_eq_of_mul_eq_one_right ht`. Unfold `herm`. Rewrite using `[show B.σ ((t : B.A) * z) = B.σ (t : B.A) * B.σ z from map_mul B.σ _ _, ← h1]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_torus_mul_right_eq_inv_mul_middle (x y : B.A) (t : B.Aˣ) (ht : t ∈ B.T) (z : B.A) :
    B.herm x y ((t : B.A) * z) = B.herm x (((t⁻¹ : B.Aˣ) : B.A) * y) z := by
  have h1 : ((t⁻¹ : B.Aˣ) : B.A) = B.σ (t : B.A) := Units.inv_eq_of_mul_eq_one_right ht
  unfold herm
  rw [show B.σ ((t : B.A) * z) = B.σ (t : B.A) * B.σ z from map_mul B.σ _ _, ← h1]
  congr 1
  ring

/- English proof (translation)
Take `⟨⟨hfg, hsp⟩, hg, hsd⟩` from `hL`. Use `⟨⟨hfg.map _, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff]`. Introduce `a _`. Establish `hmem : ((t⁻¹ : B.Aˣ) : B.A) * a ∈ Submodule.span K.E (L : Set B.A)` using `by rw [hsp]; trivial`.

Establish `h2` using `Submodule.mem_map_of_mem (f := LinearMap.mulLeft K.E (t : B.A)) hmem`. Rewrite `h2` using `[Submodule.map_span]`. Establish `h3 : (LinearMap.mulLeft K.E (t : B.A)) ((((t⁻¹ : B.Aˣ) : B.A) * a)) = a`. Simplify using `[LinearMap.mulLeft_apply, ← mul_assoc]`. Rewrite `h2` using `[h3]`.

Establish `e : ((mulLat K.O (t : B.A) L : Submodule K.O B.A) : Set B.A) = (LinearMap.mulLeft K.E (t : B.A)) '' (L : Set B.A)` using `by show ((L.map (LinearMap.mulLeft K.O (t : B.A)) : Submodule K.O B.A) : Set B.A) = _`. Rewrite using `[Submodule.map_coe]`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `h2`.

Introduce `y hy`. Rewrite `hy`, the goal using `[torusOrb_mem_mulLat_unit]`. Rewrite using `[mul_left_comm]`. Conclude with `hg _ hy`. Introduce `y`.

Rewrite using `[torusOrb_mem_mulLat_unit, hsd]`. Prove the components needed by the constructor for the conclusion. Introduce `h z hz`. Rewrite `hz` using `[torusOrb_mem_mulLat_unit]`. Use `h _ hz` as an intermediate fact.

Rewrite `this` using `[← herm_torus_mul_right_eq_inv_mul_middle B x y t ht]`. Simplify `this` using `[← mul_assoc]`. Introduce `h z hz`. Rewrite using `[← herm_torus_mul_right_eq_inv_mul_middle B x y t ht]`. Apply `h` to reduce the goal to its premises.

Rewrite using `[torusOrb_mem_mulLat_unit]`. Simplify `hz` using `[← mul_assoc]`.
-/
theorem torusOrb_mulLat_mem_X (x : B.A) (t : B.Aˣ) (ht : t ∈ B.T) (L : Submodule K.O B.A) (hL : L ∈ B.X x) :
    mulLat K.O (t : B.A) L ∈ B.X x := by
  obtain ⟨⟨hfg, hsp⟩, hg, hsd⟩ := hL
  refine ⟨⟨hfg.map _, ?_⟩, ?_, ?_⟩
  · rw [eq_top_iff]
    intro a _
    have hmem : ((t⁻¹ : B.Aˣ) : B.A) * a ∈ Submodule.span K.E (L : Set B.A) := by rw [hsp]; trivial
    have h2 := Submodule.mem_map_of_mem (f := LinearMap.mulLeft K.E (t : B.A)) hmem
    rw [Submodule.map_span] at h2
    have h3 : (LinearMap.mulLeft K.E (t : B.A)) ((((t⁻¹ : B.Aˣ) : B.A) * a)) = a := by
      simp [LinearMap.mulLeft_apply, ← mul_assoc]
    rw [h3] at h2
    have e : ((mulLat K.O (t : B.A) L : Submodule K.O B.A) : Set B.A) =
        (LinearMap.mulLeft K.E (t : B.A)) '' (L : Set B.A) := by
      show ((L.map (LinearMap.mulLeft K.O (t : B.A)) : Submodule K.O B.A) : Set B.A) = _
      rw [Submodule.map_coe]
      rfl
    rw [e]
    exact h2
  · intro y hy
    rw [torusOrb_mem_mulLat_unit] at hy ⊢
    rw [mul_left_comm]
    exact hg _ hy
  · intro y
    rw [torusOrb_mem_mulLat_unit, hsd]
    constructor
    · intro h z hz
      rw [torusOrb_mem_mulLat_unit] at hz
      have := h _ hz
      rw [← herm_torus_mul_right_eq_inv_mul_middle B x y t ht] at this
      simpa [← mul_assoc] using this
    · intro h z hz
      rw [← herm_torus_mul_right_eq_inv_mul_middle B x y t ht]
      apply h
      rw [torusOrb_mem_mulLat_unit]
      simpa [← mul_assoc] using hz

def torusOrbRel (x : B.A) (L M : B.X x) : Prop :=
  ∃ t ∈ B.T, (M : Submodule K.O B.A) = mulLat K.O (t : B.A) (L : Submodule K.O B.A)

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, B.T.one_mem, by rw [Units.val_one, torusOrb_mulLat_one]⟩ symm := by rintro L M ⟨t, ht, h⟩ refine ⟨t⁻¹, B.T.inv_mem ht, ?_⟩ rw [h, torusOrb_mulLat_inv] trans := by rintro L M N ⟨s, hs, h1⟩ ⟨t, ht, h2⟩ refine ⟨t * s, B.T.mul_mem ht hs, ?_⟩ rw [h2, h1, torusOrb_mulLat_mul]`.
-/
theorem torusOrb_orbRel_equivalence (x : B.A) : Equivalence (B.torusOrbRel x) where
  refl L := ⟨1, B.T.one_mem, by rw [Units.val_one, torusOrb_mulLat_one]⟩
  symm := by
    rintro L M ⟨t, ht, h⟩
    refine ⟨t⁻¹, B.T.inv_mem ht, ?_⟩
    rw [h, torusOrb_mulLat_inv]
  trans := by
    rintro L M N ⟨s, hs, h1⟩ ⟨t, ht, h2⟩
    refine ⟨t * s, B.T.mul_mem ht hs, ?_⟩
    rw [h2, h1, torusOrb_mulLat_mul]

/- English proof (translation)
The claim follows from `(Equivalence.eqvGen_iff (B.torusOrb_orbRel_equivalence x)).1 (Quot.eqvGen_exact h)`.
-/
theorem torusOrb_orb_mk_eq (x : B.A) {L M : B.X x}
    (h : (Quot.mk (B.torusOrbRel x) L : Orb K.O B.T (B.X x)) = Quot.mk (B.torusOrbRel x) M) : B.torusOrbRel x L M :=
  (Equivalence.eqvGen_iff (B.torusOrb_orbRel_equivalence x)).1 (Quot.eqvGen_exact h)

def torusOrb_orbSplit (x w : B.A) : {L : B.X x // w ∈ (L : Submodule K.O B.A)} ≃
    Σ o : Orb K.O B.T (B.X x), {M : Submodule K.O B.A //
      (∃ t ∈ B.T, M = mulLat K.O (t : B.A) (Quot.out o).1) ∧ w ∈ M} where
  toFun L := ⟨(Quot.mk (B.torusOrbRel x) L.1 : Orb K.O B.T (B.X x)), L.1.1,
    B.torusOrb_orb_mk_eq x (Quot.out_eq (Quot.mk (B.torusOrbRel x) L.1 : Orb K.O B.T (B.X x))), L.2⟩
  invFun p := ⟨⟨p.2.1, by
      obtain ⟨t, ht, h⟩ := p.2.2.1
      rw [h]
      exact B.torusOrb_mulLat_mem_X x t ht _ (Quot.out p.1).2⟩, p.2.2.2⟩
  left_inv L := rfl
  right_inv p := by
    obtain ⟨o, M, h⟩ := p
    refine Sigma.subtype_ext ?_ rfl
    dsimp only
    conv_rhs => rw [← Quot.out_eq o]
    symm
    apply Quot.sound
    exact h.1

/- English proof (translation)
Use `haveI := Fintype.ofFinite (Orb K.O B.T (B.X x))`. Unfold `UU`. Rewrite using `[Nat.card_congr (B.torusOrb_orbSplit x w), Nat.card_sigma, finsum_eq_sum_of_fintype]`.
-/
theorem torusOrb_UU_eq_finsum (x w : B.A) (hfin : Finite (Orb K.O B.T (B.X x)))
    (hfib : ∀ o : Orb K.O B.T (B.X x), Finite {M : Submodule K.O B.A //
      (∃ t ∈ B.T, M = mulLat K.O (t : B.A) (Quot.out o).1) ∧ w ∈ M}) :
    B.UU x w = ∑ᶠ o : Orb K.O B.T (B.X x), Nat.card {M : Submodule K.O B.A //
      (∃ t ∈ B.T, M = mulLat K.O (t : B.A) (Quot.out o).1) ∧ w ∈ M} := by
  haveI := Fintype.ofFinite (Orb K.O B.T (B.X x))
  unfold UU
  rw [Nat.card_congr (B.torusOrb_orbSplit x w), Nat.card_sigma, finsum_eq_sum_of_fintype]

end InvAlg

/- English proof (translation)
Introduce `_ B x w h1 h2` and use `B.torusOrb_UU_eq_finsum x w h1 h2`.
-/
theorem UU_eq_sum_orbits : ∀ (K : UQ) (B : InvAlg K) (x w : B.A), Finite (Orb K.O B.T (B.X x)) →
    (∀ o : Orb K.O B.T (B.X x), Finite {M : Submodule K.O B.A //
      (∃ t ∈ B.T, M = mulLat K.O (t : B.A) (Quot.out o).1) ∧ w ∈ M}) →
    B.UU x w = ∑ᶠ o : Orb K.O B.T (B.X x), Nat.card {M : Submodule K.O B.A //
      (∃ t ∈ B.T, M = mulLat K.O (t : B.A) (Quot.out o).1) ∧ w ∈ M} :=
  fun _ B x w h1 h2 => B.torusOrb_UU_eq_finsum x w h1 h2

end GlobalTheory.UnitLemma
