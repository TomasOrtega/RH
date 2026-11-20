import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsCechDSq
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v

namespace CechDSq

variable {n : ℕ}

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sgn_mul_sgn_of_lt {K : Finset (Fin n)} {j k : Fin n} (hj : j ∈ K) (hjk : j < k) :
    Cech.sgn K k * Cech.sgn (K.erase k) j = -(Cech.sgn K j * Cech.sgn (K.erase j) k) := by
  have h1 : (K.erase k).filter (· < j) = K.filter (· < j) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨-, hz⟩, hzj⟩; exact ⟨hz, hzj⟩
    · rintro ⟨hz, hzj⟩; exact ⟨⟨(hzj.trans hjk).ne, hz⟩, hzj⟩
  have h3 : j ∈ K.filter (· < k) := Finset.mem_filter.2 ⟨hj, hjk⟩
  have h2 : ((K.erase j).filter (· < k)).card + 1 = (K.filter (· < k)).card := by
    rw [Finset.filter_erase, Finset.card_erase_add_one h3]
  unfold Cech.sgn
  rw [h1, ← h2, pow_succ]
  ring

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem sgn_mul_sgn_swap {K : Finset (Fin n)} {j k : Fin n} (hk : k ∈ K) (hj : j ∈ K) (hne : j ≠ k) :
    Cech.sgn K k * Cech.sgn (K.erase k) j = -(Cech.sgn K j * Cech.sgn (K.erase j) k) := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact sgn_mul_sgn_of_lt hj h
  · rw [sgn_mul_sgn_of_lt hk h, neg_neg]

variable {U : Finset (Fin n)} {R : Type u} [CommRing R] {G : Cell U → Type v}
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}

open Classical in

def restrictTo {i : ℕ} (s : Cech.Cochain G i) (K : Cell U) (A : Finset (Fin n)) : G K :=
  if h : ∃ L : Cech.Idx U i, L.1.1 = A ∧ A ⊆ K.1 then
    ρ h.choose.1 K (by rw [h.choose_spec.1]; exact h.choose_spec.2) (s h.choose)
  else 0

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Assume the hypotheses and unpack their components. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem restrictTo_eq {i : ℕ} (s : Cech.Cochain G i) (K : Cell U) (L : Cech.Idx U i)
    (h : L.1.1 ⊆ K.1) : restrictTo (ρ := ρ) s K L.1.1 = ρ L.1 K h (s L) := by
  have hex : ∃ L' : Cech.Idx U i, L'.1.1 = L.1.1 ∧ L.1.1 ⊆ K.1 := ⟨L, rfl, h⟩
  have key : ∀ (L₁ L₂ : Cech.Idx U i) (_ : L₁ = L₂) (h₁ : L₁.1.1 ⊆ K.1) (h₂ : L₂.1.1 ⊆ K.1),
      ρ L₁.1 K h₁ (s L₁) = ρ L₂.1 K h₂ (s L₂) := by
    rintro _ _ rfl _ _; rfl
  rw [restrictTo, dif_pos hex]
  exact key _ _ (Subtype.ext (Subtype.ext hex.choose_spec.1)) _ _

end CechDSq

open CechDSq in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Assume the hypotheses and unpack their components. Both sides reduce to the same expression.

A detailed English derivation is pending.
-/
theorem CechDSq.proof : CechDSq.Statement := by
  intro n U R _ G _ _ ρ hρ i s
  classical
  funext K
  have hcomp : ∀ (I J L : Cell U) (h₁ : I.1 ⊆ J.1) (h₂ : J.1 ⊆ L.1) (x : G I),
      ρ J L h₂ (ρ I J h₁ x) = ρ I L (h₁.trans h₂) x := fun I J L h₁ h₂ x =>
    LinearMap.congr_fun (hρ I J L h₁ h₂) x

  let f : (Σ _ : Fin n, Fin n) → G K.1 := fun p =>
    (Cech.sgn K.1.1 p.1 * Cech.sgn (K.1.1.erase p.1) p.2) •
      restrictTo (ρ := ρ) s K.1 ((K.1.1.erase p.1).erase p.2)
  have step : ∀ k : K.1.1, Cech.sgn K.1.1 k • ρ (Cech.face K k).1 K.1 (Cech.face_subset K k)
      (Cech.d G ρ i s (Cech.face K k)) = ∑ j ∈ K.1.1.erase k, f ⟨k, j⟩ := by
    intro k
    rw [Cech.d_apply, map_sum, Finset.smul_sum]
    refine Eq.trans ?_ (Finset.sum_coe_sort (K.1.1.erase k) (fun j => f ⟨k, j⟩))
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, smul_smul, hcomp, ← restrictTo_eq]
    rfl
  show Cech.d G ρ (i + 1) (Cech.d G ρ i s) K = 0
  rw [Cech.d_apply, Finset.sum_congr rfl fun k _ => step k,
    Finset.sum_coe_sort K.1.1 (fun k => ∑ j ∈ K.1.1.erase k, f ⟨k, j⟩),
    Finset.sum_sigma' K.1.1 (fun k => K.1.1.erase k) (fun k j => f ⟨k, j⟩)]
  refine Finset.sum_involution (fun p _ => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_
  · rintro ⟨k, j⟩ hp
    obtain ⟨hk, hj⟩ := Finset.mem_sigma.1 hp
    obtain ⟨hne, hj⟩ := Finset.mem_erase.1 hj
    simp only [f]
    rw [Finset.erase_right_comm, sgn_mul_sgn_swap hk hj hne, neg_smul, neg_add_cancel]
  · rintro ⟨k, j⟩ hp - h
    obtain ⟨hne, -⟩ := Finset.mem_erase.1 (Finset.mem_sigma.1 hp).2
    exact hne (congrArg Sigma.fst h)
  · rintro ⟨k, j⟩ hp
    obtain ⟨hk, hj⟩ := Finset.mem_sigma.1 hp
    obtain ⟨hne, hj⟩ := Finset.mem_erase.1 hj
    exact Finset.mem_sigma.2 ⟨hj, Finset.mem_erase.2 ⟨hne.symm, hk⟩⟩
  · rintro ⟨k, j⟩ -
    rfl

end

end GroundTheory.Heights₂.Heights.Kleiman
