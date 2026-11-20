import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

/- English proof (translation)
Rewrite using `[← Subgroup.comap_map_eq, Subgroup.index_comap]`.
-/
theorem herb_relIndex_map_range {A : Type} [CommGroup A] (f : A →* A) (H : Subgroup A) :
    (H.map f).relIndex f.range = (H ⊔ f.ker).index := by
  rw [← Subgroup.comap_map_eq, Subgroup.index_comap]

/- English proof (translation)
Establish `h1 : (C ⊔ B).relIndex (B ⊔ K) * (B ⊔ K).index = (C ⊔ B).index` using `Subgroup.relIndex_mul_index (sup_le (hCK.trans le_sup_right) le_sup_left)`. Establish `h2 : (C ⊔ B).relIndex (B ⊔ K) = (C ⊔ B ⊓ K).relIndex K`. Establish `e : B ⊔ K = K ⊔ (C ⊔ B)`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `sup_le (le_sup_right.trans le_sup_right) le_sup_left`.

Conclude with `sup_le le_sup_right (sup_le (hCK.trans le_sup_right) le_sup_left)`. Rewrite using `[e, Subgroup.relIndex_sup_right, ← sup_inf_assoc_of_le B hCK, Subgroup.inf_relIndex_right]`. Establish `h3 : C.relIndex (C ⊔ B ⊓ K) * (C ⊔ B ⊓ K).relIndex K = C.relIndex K` using `Subgroup.relIndex_mul_relIndex _ _ _ le_sup_left (sup_le hCK inf_le_right)`. Establish `h4 : C.relIndex (C ⊔ B ⊓ K) = C.relIndex (B ⊓ K)` using `Subgroup.relIndex_sup_left _ _`. Establish `h5 : Nat.card ↥(C ⊓ B) * C.relIndex (B ⊓ K) = Nat.card ↥(B ⊓ K)`.

Establish `e : C ⊓ (B ⊓ K) = C ⊓ B`. Rewrite using `[inf_comm B K, ← inf_assoc, inf_eq_left.2 hCK]`. Rewrite using `[← Subgroup.inf_relIndex_right C, e, ← Subgroup.relIndex_bot_left, ← Subgroup.relIndex_bot_left]`. Conclude with `Subgroup.relIndex_mul_relIndex _ _ _ bot_le (e ▸ inf_le_right)`. Rewrite using `[← h1, h2, ← h3, h4, ← h5]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem herb_lattice {A : Type} [CommGroup A] (B C K : Subgroup A) (hCK : C ≤ K) :
    (C ⊔ B).index * Nat.card ↥(B ⊓ K) =
      (B ⊔ K).index * C.relIndex K * Nat.card ↥(C ⊓ B) := by
  have h1 : (C ⊔ B).relIndex (B ⊔ K) * (B ⊔ K).index = (C ⊔ B).index :=
    Subgroup.relIndex_mul_index (sup_le (hCK.trans le_sup_right) le_sup_left)
  have h2 : (C ⊔ B).relIndex (B ⊔ K) = (C ⊔ B ⊓ K).relIndex K := by
    have e : B ⊔ K = K ⊔ (C ⊔ B) := by
      apply le_antisymm
      · exact sup_le (le_sup_right.trans le_sup_right) le_sup_left
      · exact sup_le le_sup_right (sup_le (hCK.trans le_sup_right) le_sup_left)
    rw [e, Subgroup.relIndex_sup_right, ← sup_inf_assoc_of_le B hCK, Subgroup.inf_relIndex_right]
  have h3 : C.relIndex (C ⊔ B ⊓ K) * (C ⊔ B ⊓ K).relIndex K = C.relIndex K :=
    Subgroup.relIndex_mul_relIndex _ _ _ le_sup_left (sup_le hCK inf_le_right)
  have h4 : C.relIndex (C ⊔ B ⊓ K) = C.relIndex (B ⊓ K) := Subgroup.relIndex_sup_left _ _
  have h5 : Nat.card ↥(C ⊓ B) * C.relIndex (B ⊓ K) = Nat.card ↥(B ⊓ K) := by
    have e : C ⊓ (B ⊓ K) = C ⊓ B := by
      rw [inf_comm B K, ← inf_assoc, inf_eq_left.2 hCK]
    rw [← Subgroup.inf_relIndex_right C, e, ← Subgroup.relIndex_bot_left,
      ← Subgroup.relIndex_bot_left]
    exact Subgroup.relIndex_mul_relIndex _ _ _ bot_le (e ▸ inf_le_right)
  rw [← h1, h2, ← h3, h4, ← h5]
  ring

/- English proof (translation)
Establish `e1` using `Finset.prod_range_succ (fun i => σ^[i] a) p`. Establish `e2` using `Finset.prod_range_succ' (fun i => σ^[i] a) p`. Rewrite `e2` using `[e1]`. Simplify using `only [h, Function.iterate_zero, id, Function.iterate_succ_apply] at e2`. Rewrite using `[nrm_apply, nrm_apply]`.

Conclude with `(mul_right_cancel e2).symm`.
-/
theorem herb_nrm_apply_sigma {A : Type} [CommGroup A] (σ : A →* A) (p : ℕ)
    (h : ∀ a, σ^[p] a = a) (a : A) : nrm σ p (σ a) = nrm σ p a := by
  have e1 := Finset.prod_range_succ (fun i => σ^[i] a) p
  have e2 := Finset.prod_range_succ' (fun i => σ^[i] a) p
  rw [e1] at e2
  simp only [h, Function.iterate_zero, id, Function.iterate_succ_apply] at e2
  rw [nrm_apply, nrm_apply]
  exact (mul_right_cancel e2).symm

/- English proof (translation)
Rewrite using `[nrm_apply, Finset.prod_congr rfl (fun i _ => Function.iterate_fixed ((mem_fix σ b).1 hb) i)]`. Simplify using the standard rewrite rules.
-/
theorem herb_nrm_of_fix {A : Type} [CommGroup A] (σ : A →* A) (p : ℕ) (b : A)
    (hb : b ∈ fix σ) : nrm σ p b = b ^ p := by
  rw [nrm_apply, Finset.prod_congr rfl (fun i _ => Function.iterate_fixed ((mem_fix σ b).1 hb) i)]
  simp

/- English proof (translation)
Introduce `p A _ σ h`. Establish `hker : (dif σ).ker = fix σ`. Use extensionality with `a`. Rewrite using `[MonoidHom.mem_ker, dif_apply, mem_fix, div_eq_one]`. Establish `hCK : (dif σ).range ≤ (nrm σ p).ker`.

Introduce and unpack `_ ⟨a, rfl⟩`. Rewrite using `[MonoidHom.mem_ker, dif_apply, _root_.map_div, herb_nrm_apply_sigma σ p h, div_self']`. Establish `hNB : (nrm σ p).range ≤ fix σ`. Introduce and unpack `_ ⟨a, rfl⟩`. Rewrite using `[mem_fix, ← herb_nrm_apply_sigma σ p h a]`.

Use `conv_lhs => rw [herb_nrm_apply_sigma σ p h a]`. Rewrite using `[nrm_apply, nrm_apply, map_prod]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Function.iterate_succ_apply σ i a, Function.iterate_succ_apply']`. Establish `hpow : pows p (fix σ) = (fix σ).map (nrm σ p)`.

Use extensionality with `x`. Simplify using `only [pows, Subgroup.mem_map, powMonoidHom_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, hb, rfl⟩`. Conclude with `⟨b, hb, herb_nrm_of_fix σ p b hb⟩`.

Introduce and unpack `⟨b, hb, rfl⟩`. Conclude with `⟨b, hb, (herb_nrm_of_fix σ p b hb).symm⟩`. Establish `htor : pTor p (fix σ) = Nat.card ↥(fix σ ⊓ (nrm σ p).ker)`. Unfold `pTor`. Use `Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)` and prove the remaining obligations.

Rewrite using `[Subgroup.mem_inf, MonoidHom.mem_ker]`. Use `and_congr_right fun hx => ?_` and prove the remaining obligations. Rewrite using `[herb_nrm_of_fix σ p x hx]`. Establish `hidx : pIdx p (fix σ) = (fix σ ⊔ (nrm σ p).ker).index * (nrm σ p).range.relIndex (fix σ)`. Unfold `pIdx`.

Rewrite using `[hpow, ← herb_relIndex_map_range]`. Conclude with `(Subgroup.relIndex_mul_relIndex _ _ _ (Subgroup.map_le_range _ _) hNB).symm`. Establish `hl` using `herb_lattice (fix σ) (dif σ).range (nrm σ p).ker hCK`. Rewrite using `[herb_relIndex_map_range, hker, htor, hidx, mul_assoc, hl]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herb_index_identity : ∀ (p : ℕ) (A : Type) [CommGroup A] (σ : A →* A), (∀ a, σ^[p] a = a) → (nrm σ p).range.relIndex (fix σ) * ((dif σ).range.map (dif σ)).relIndex (dif σ).range * pTor p (fix σ) = pIdx p (fix σ) * (dif σ).range.relIndex (nrm σ p).ker * Nat.card ↥((dif σ).range ⊓ fix σ) := by
  intro p A _ σ h
  have hker : (dif σ).ker = fix σ := by
    ext a
    rw [MonoidHom.mem_ker, dif_apply, mem_fix, div_eq_one]
  have hCK : (dif σ).range ≤ (nrm σ p).ker := by
    rintro _ ⟨a, rfl⟩
    rw [MonoidHom.mem_ker, dif_apply, _root_.map_div, herb_nrm_apply_sigma σ p h, div_self']
  have hNB : (nrm σ p).range ≤ fix σ := by
    rintro _ ⟨a, rfl⟩
    rw [mem_fix, ← herb_nrm_apply_sigma σ p h a]
    conv_lhs => rw [herb_nrm_apply_sigma σ p h a]
    rw [nrm_apply, nrm_apply, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Function.iterate_succ_apply σ i a, Function.iterate_succ_apply']
  have hpow : pows p (fix σ) = (fix σ).map (nrm σ p) := by
    ext x
    simp only [pows, Subgroup.mem_map, powMonoidHom_apply]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b, hb, herb_nrm_of_fix σ p b hb⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b, hb, (herb_nrm_of_fix σ p b hb).symm⟩
  have htor : pTor p (fix σ) = Nat.card ↥(fix σ ⊓ (nrm σ p).ker) := by
    unfold pTor
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    rw [Subgroup.mem_inf, MonoidHom.mem_ker]
    refine and_congr_right fun hx => ?_
    rw [herb_nrm_of_fix σ p x hx]
  have hidx : pIdx p (fix σ) =
      (fix σ ⊔ (nrm σ p).ker).index * (nrm σ p).range.relIndex (fix σ) := by
    unfold pIdx
    rw [hpow, ← herb_relIndex_map_range]
    exact (Subgroup.relIndex_mul_relIndex _ _ _ (Subgroup.map_le_range _ _) hNB).symm
  have hl := herb_lattice (fix σ) (dif σ).range (nrm σ p).ker hCK
  rw [herb_relIndex_map_range, hker, htor, hidx, mul_assoc, hl]
  ring

end GlobalTheory.CNorm
