import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsCechDSq
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v

namespace CechDSq

variable {n : ℕ}

/- English proof (translation)
Establish `h1 : (K.erase k).filter (· < j) = K.filter (· < j)`. Use extensionality with `z`. Simplify using `only [Finset.mem_filter, Finset.mem_erase]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨-, hz⟩, hzj⟩`.

Conclude with `⟨hz, hzj⟩`. Introduce and unpack `⟨hz, hzj⟩`. Conclude with `⟨⟨(hzj.trans hjk).ne, hz⟩, hzj⟩`. Establish `h3 : j ∈ K.filter (· < k)` using `Finset.mem_filter.2 ⟨hj, hjk⟩`. Establish `h2 : ((K.erase j).filter (· < k)).card + 1 = (K.filter (· < k)).card`.

Rewrite using `[Finset.filter_erase, Finset.card_erase_add_one h3]`. Unfold `Cech.sgn`. Rewrite using `[h1, ← h2, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.
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
Break down `lt_or_gt_of_ne hne with h | h` into its components or cases. Conclude with `sgn_mul_sgn_of_lt hj h`. Rewrite using `[sgn_mul_sgn_of_lt hk h, neg_neg]`.
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
Establish `hex : ∃ L' : Cech.Idx U i, L'.1.1 = L.1.1 ∧ L.1.1 ⊆ K.1` using `⟨L, rfl, h⟩`. Establish `key : ∀ (L₁ L₂ : Cech.Idx U i) (_ : L₁ = L₂) (h₁ : L₁.1.1 ⊆ K.1) (h₂ : L₂.1.1 ⊆ K.1), ρ L₁.1 K h₁ (s L₁) = ρ L₂.1 K h₂ (s L₂)`. Introduce and unpack `_ _ rfl _ _`. Both sides reduce to the same expression. Rewrite using `[restrictTo, dif_pos hex]`.

Conclude with `key _ _ (Subtype.ext (Subtype.ext hex.choose_spec.1)) _ _`.
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
Introduce `n U R _ G _ _ ρ hρ i s`. Use function extensionality and compare the values at `K`. Establish `hcomp : ∀ (I J L : Cell U) (h₁ : I.1 ⊆ J.1) (h₂ : J.1 ⊆ L.1) (x : G I), ρ J L h₂ (ρ I J h₁ x) = ρ I L (h₁.trans h₂) x` using `fun I J L h₁ h₂ x => LinearMap.congr_fun (hρ I J L h₁ h₂) x`. Set `f : (Σ _ : Fin n, Fin n) → G K.1` to `fun p => (Cech.sgn K.1.1 p.1 * Cech.sgn (K.1.1.erase p.1) p.2) • restrictTo (ρ := ρ) s K.1 ((K.1.1.erase p.1).erase p.2)`. Establish `step : ∀ k : K.1.1, Cech.sgn K.1.1 k • ρ (Cech.face K k).1 K.1 (Cech.face_subset K k) (Cech.d G ρ i s (Cech.face K k)) = ∑ j ∈ K.1.1.erase k, f ⟨k, j⟩`.

Introduce `k`. Rewrite using `[Cech.d_apply, map_sum, Finset.smul_sum]`. Use `Eq.trans ?_ (Finset.sum_coe_sort (K.1.1.erase k) (fun j => f ⟨k, j⟩))` and prove the remaining obligations. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, smul_smul, hcomp, ← restrictTo_eq]`.

Both sides reduce to the same expression. Use `show Cech.d G ρ (i + 1) (Cech.d G ρ i s) K = 0`. Rewrite using `[Cech.d_apply, Finset.sum_congr rfl fun k _ => step k, Finset.sum_coe_sort K.1.1 (fun k => ∑ j ∈ K.1.1.erase k, f ⟨k, j⟩), Finset.sum_sigma' K.1.1 (fun k => K.1.1.erase k) (fun k j => f ⟨k, j⟩)]`. Use `Finset.sum_involution (fun p _ => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `⟨k, j⟩ hp`.

Take `⟨hk, hj⟩` from `Finset.mem_sigma.1 hp`. Take `⟨hne, hj⟩` from `Finset.mem_erase.1 hj`. Simplify using `only [f]`. Rewrite using `[Finset.erase_right_comm, sgn_mul_sgn_swap hk hj hne, neg_smul, neg_add_cancel]`. Introduce and unpack `⟨k, j⟩ hp - h`.

Take `⟨hne, -⟩` from `Finset.mem_erase.1 (Finset.mem_sigma.1 hp).2`. Conclude with `hne (congrArg Sigma.fst h)`. Introduce and unpack `⟨k, j⟩ hp`. Take `⟨hk, hj⟩` from `Finset.mem_sigma.1 hp`. Take `⟨hne, hj⟩` from `Finset.mem_erase.1 hj`.

Conclude with `Finset.mem_sigma.2 ⟨hj, Finset.mem_erase.2 ⟨hne.symm, hk⟩⟩`. Introduce and unpack `⟨k, j⟩ -`. Both sides reduce to the same expression.
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
