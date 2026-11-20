import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent

noncomputable section

namespace GlobalTheory.UnitLemma

open Polynomial

namespace InvAlg

variable {K : UQ} (B : InvAlg K)

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Simplify to obtain the desired conclusion from the available facts.

Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
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
By extensionality, compare the relevant components. Simplify to obtain the desired conclusion from the available facts.
-/
theorem torusOrb_mulLat_one (L : Submodule K.O B.A) : mulLat K.O (1 : B.A) L = L := by
  ext y; simpa using torusOrb_mem_mulLat_unit B 1 L y

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.
-/
theorem torusOrb_mulLat_mul (s t : B.Aˣ) (L : Submodule K.O B.A) :
    mulLat K.O ((s : B.A)) (mulLat K.O (t : B.A) L) = mulLat K.O ((s * t : B.Aˣ) : B.A) L := by
  ext y
  rw [torusOrb_mem_mulLat_unit, torusOrb_mem_mulLat_unit, torusOrb_mem_mulLat_unit, mul_inv_rev, Units.val_mul, mul_assoc]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem torusOrb_mulLat_inv (t : B.Aˣ) (L : Submodule K.O B.A) :
    mulLat K.O ((t⁻¹ : B.Aˣ) : B.A) (mulLat K.O (t : B.A) L) = L := by
  rw [torusOrb_mulLat_mul, inv_mul_cancel, Units.val_one, torusOrb_mulLat_one]

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_torus_mul_right_eq_inv_mul_middle (x y : B.A) (t : B.Aˣ) (ht : t ∈ B.T) (z : B.A) :
    B.herm x y ((t : B.A) * z) = B.herm x (((t⁻¹ : B.Aˣ) : B.A) * y) z := by
  have h1 : ((t⁻¹ : B.Aˣ) : B.A) = B.σ (t : B.A) := Units.inv_eq_of_mul_eq_one_right ht
  unfold herm
  rw [show B.σ ((t : B.A) * z) = B.σ (t : B.A) * B.σ z from map_mul B.σ _ _, ← h1]
  congr 1
  ring

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

A detailed English derivation is pending.
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
Supply the required witnesses or components.
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
A detailed English derivation is pending.
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
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem UU_eq_sum_orbits : ∀ (K : UQ) (B : InvAlg K) (x w : B.A), Finite (Orb K.O B.T (B.X x)) →
    (∀ o : Orb K.O B.T (B.X x), Finite {M : Submodule K.O B.A //
      (∃ t ∈ B.T, M = mulLat K.O (t : B.A) (Quot.out o).1) ∧ w ∈ M}) →
    B.UU x w = ∑ᶠ o : Orb K.O B.T (B.X x), Nat.card {M : Submodule K.O B.A //
      (∃ t ∈ B.T, M = mulLat K.O (t : B.A) (Quot.out o).1) ∧ w ∈ M} :=
  fun _ B x w h1 h2 => B.torusOrb_UU_eq_finsum x w h1 h2

end GlobalTheory.UnitLemma
