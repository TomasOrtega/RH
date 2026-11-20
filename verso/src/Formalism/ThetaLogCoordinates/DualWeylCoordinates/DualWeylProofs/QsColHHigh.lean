import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QsRemIffAdd
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QsSymDMatEq

noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ} [NeZero n]

def qs_ext (mu : Fin n → ℤ) (I : TIdx mu) : ℤ → Finset (Fin n) :=
  fun c => if h : c ∈ TCols mu then (I ⟨c, h⟩).1 else if c ≤ mu (lastIdx n) then univ else ∅

/- English proof (translation)
Simplify using `[qs_ext, c.2]`.
-/
lemma qs_ext_mem (mu : Fin n → ℤ) (I : TIdx mu) (c : ↥(TCols mu)) : qs_ext mu I c.1 = (I c).1 := by
  simp [qs_ext, c.2]

/- English proof (translation)
Unfold `colH`. Rewrite using `[Finset.filter_true_of_mem (fun m _ => hc.trans (hmu (qb_le_lastIdx m)))]`. Simplify using the standard rewrite rules.
-/
lemma qs_colH_low {mu : Fin n → ℤ} (hmu : Dominant mu) {c : ℤ} (hc : c ≤ mu (lastIdx n)) : colH mu c = n := by
  unfold colH
  rw [Finset.filter_true_of_mem (fun m _ => hc.trans (hmu (qb_le_lastIdx m)))]; simp

/- English proof (translation)
Unfold `colH`. Rewrite using `[Finset.filter_false_of_mem (fun m _ => by have := hmu (Fin.zero_le m); omega)]; simp`.
-/
lemma qs_colH_high {mu : Fin n → ℤ} (hmu : Dominant mu) {c : ℤ} (hc : mu 0 < c) : colH mu c = 0 := by
  unfold colH
  rw [Finset.filter_false_of_mem (fun m _ => by have := hmu (Fin.zero_le m); omega)]; simp

/- English proof (translation)
Unfold `qs_ext`. Use `split_ifs with h1 h2`. Conclude with `(I ⟨c, h1⟩).2`. Rewrite using `[qs_colH_low hmu h2]`. Simplify using the standard rewrite rules.

Rewrite using `[qs_colH_high hmu (by simp only [TCols, mem_Ioc] at h1; omega)]; simp`.
-/
lemma qs_ext_card {mu : Fin n → ℤ} (hmu : Dominant mu) (I : TIdx mu) (c : ℤ) :
    (qs_ext mu I c).card = colH mu c := by
  unfold qs_ext
  split_ifs with h1 h2
  · exact (I ⟨c, h1⟩).2
  · rw [qs_colH_low hmu h2]; simp
  · rw [qs_colH_high hmu (by simp only [TCols, mem_Ioc] at h1; omega)]; simp

def qs_res (mu : Fin n → ℤ) (F : ℤ → Finset (Fin n)) (hF : ∀ c, (F c).card = colH mu c) : TIdx mu :=
  fun c => ⟨F c.1, hF c.1⟩

/- English proof (translation)
Use function extensionality and compare the values at `c`. Unfold `qs_ext`. Use `split_ifs with h1 h2`. Both sides reduce to the same expression. Use `symm`.

Apply `Finset.eq_univ_of_card` to reduce the goal to its premises. Rewrite using `[hF, qs_colH_low hmu h2]`. Simplify using the standard rewrite rules. Use the proof step `symm; rw [← Finset.card_eq_zero, hF, qs_colH_high hmu (by simp only [TCols, mem_Ioc] at h1; omega)]`.
-/
lemma qs_ext_res {mu : Fin n → ℤ} (hmu : Dominant mu) (F : ℤ → Finset (Fin n))
    (hF : ∀ c, (F c).card = colH mu c) : qs_ext mu (qs_res mu F hF) = F := by
  funext c
  unfold qs_ext
  split_ifs with h1 h2
  · rfl
  · symm; apply Finset.eq_univ_of_card; rw [hF, qs_colH_low hmu h2]; simp
  · symm; rw [← Finset.card_eq_zero, hF, qs_colH_high hmu (by simp only [TCols, mem_Ioc] at h1; omega)]

/- English proof (translation)
Introduce `I I' h`. Use function extensionality and compare the values at `c`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← qs_ext_mem, ← qs_ext_mem, h]`.
-/
lemma qs_ext_inj (mu : Fin n → ℤ) : Function.Injective (qs_ext mu) := by
  intro I I' h
  funext c
  apply Subtype.ext
  rw [← qs_ext_mem, ← qs_ext_mem, h]

/- English proof (translation)
Use `split_ifs with hP`. Rewrite using `[Finset.sum_eq_single (qs_res mu F (hF hP))]`. Rewrite using `[if_pos ⟨hP, qs_ext_res hmu F (hF hP)⟩, qs_ext_res hmu]`. Introduce `I _ hI`. Rewrite using `[if_neg]`.

Introduce and unpack `⟨_, h⟩`. Conclude with `hI (qs_ext_inj mu (by rw [h, qs_ext_res hmu]))`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Conclude with `Finset.sum_eq_zero fun I _ => if_neg fun h => hP h.1`.
-/
lemma qs_collapse {M : Type*} [AddCommMonoid M] {mu : Fin n → ℤ} (hmu : Dominant mu) (P : Prop) [Decidable P]
    (F : ℤ → Finset (Fin n)) (hF : P → ∀ c, (F c).card = colH mu c) (f : (ℤ → Finset (Fin n)) → M)
    [∀ I : TIdx mu, Decidable (P ∧ qs_ext mu I = F)] :
    ∑ I : TIdx mu, (if P ∧ qs_ext mu I = F then f (qs_ext mu I) else 0) = if P then f F else 0 := by
  classical
  split_ifs with hP
  · rw [Finset.sum_eq_single (qs_res mu F (hF hP))]
    · rw [if_pos ⟨hP, qs_ext_res hmu F (hF hP)⟩, qs_ext_res hmu]
    · intro I _ hI
      rw [if_neg]
      rintro ⟨_, h⟩
      exact hI (qs_ext_inj mu (by rw [h, qs_ext_res hmu]))
    · intro h; exact absurd (Finset.mem_univ _) h
  · exact Finset.sum_eq_zero fun I _ => if_neg fun h => hP h.1

def qs_ini (h : ℕ) : Finset (Fin n) := univ.filter fun x => x.1 < h

/- English proof (translation)
Unfold `qs_ext`. Use `split_ifs with h1 h2`. Use extensionality with `b`. Rewrite using `[qb_mem_canT]`. Simplify using `[qs_ini]`.

Rewrite using `[qs_colH_low hmu h2]`. Use extensionality with `b`. Simplify using `[qs_ini]`. Rewrite using `[qs_colH_high hmu (by simp only [TCols, mem_Ioc] at h1; omega)]; simp [qs_ini]`.
-/
lemma qs_ext_can {mu : Fin n → ℤ} (hmu : Dominant mu) (c : ℤ) : qs_ext mu (canT mu) c = qs_ini (colH mu c) := by
  unfold qs_ext
  split_ifs with h1 h2
  · ext b; rw [qb_mem_canT]; simp [qs_ini]
  · rw [qs_colH_low hmu h2]; ext b; simp [qs_ini]
  · rw [qs_colH_high hmu (by simp only [TCols, mem_Ioc] at h1; omega)]; simp [qs_ini]

omit [NeZero n] in
/- English proof (translation)
Rewrite using `[qs_mn_eq _ J I hJ hI, minorC, RingHom.map_det]`. Both sides reduce to the same expression.
-/
lemma qs_minorC_eq {h : ℕ} (J I : Finset (Fin n)) (hJ : J.card = h) (hI : I.card = h) :
    minorC J I hJ hI = qs_mn (qs_gC n) J I := by
  rw [qs_mn_eq _ J I hJ hI, minorC, RingHom.map_det]
  rfl

omit [NeZero n] in
/- English proof (translation)
Establish `hc : (univ : Finset (Fin n)).card = n` using `by simp`. Rewrite using `[qs_mn_eq _ _ _ hc hc]`. Establish `h1 : ∀ a, (univ : Finset (Fin n)).orderEmbOfFin hc a = a` using `fun a => (congrFun (Finset.orderEmbOfFin_unique hc (f := id) (fun _ => mem_univ _) strictMono_id) a).symm`. Simplify using `only [h1]`. Use `show _ = algebraMap _ _ (genMat ℤ n).det`.

Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression.
-/
lemma qs_mn_univ : qs_mn (qs_gC n) univ univ = ((detU n : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) := by
  have hc : (univ : Finset (Fin n)).card = n := by simp
  rw [qs_mn_eq _ _ _ hc hc]
  have h1 : ∀ a, (univ : Finset (Fin n)).orderEmbOfFin hc a = a := fun a =>
    (congrFun (Finset.orderEmbOfFin_unique hc (f := id) (fun _ => mem_univ _) strictMono_id) a).symm
  simp only [h1]
  show _ = algebraMap _ _ (genMat ℤ n).det
  rw [RingHom.map_det]; rfl

omit [NeZero n] in
/- English proof (translation)
Rewrite using `[qs_mn_eq g ∅ ∅ (h := 0) rfl rfl]`. Simplify using the standard rewrite rules.
-/
lemma qs_mn_empty {R : Type*} [CommRing R] (g : Matrix (Fin n) (Fin n) R) : qs_mn g ∅ ∅ = 1 := by
  rw [qs_mn_eq g ∅ ∅ (h := 0) rfl rfl]; simp

def qs_TM (lo : ℤ) (S : Finset ℤ) (J I : ℤ → Finset (Fin n)) : GLCoord ℤ n :=
  ((detU n ^ lo : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) * ∏ c ∈ S, qs_mn (qs_gC n) (J c) (I c)

/- English proof (translation)
Establish `h0 : mu (lastIdx n) ≤ mu 0` using `hmu (Fin.zero_le _)`. Establish `hS : Finset.Ioc lo hi = Finset.Ioc lo (mu (lastIdx n)) ∪ (TCols mu ∪ Finset.Ioc (mu 0) hi)`. Rewrite using `[TCols, Finset.Ioc_union_Ioc_eq_Ioc h0 h2, Finset.Ioc_union_Ioc_eq_Ioc h1 (h0.trans h2)]`. Establish `hA : ∏ c ∈ Finset.Ioc lo (mu (lastIdx n)), qs_mn (qs_gC n) (qs_ext mu J c) (qs_ext mu I c) = ((detU n : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) ^ (mu (lastIdx n) - lo).toNat`. Rewrite using `[← Int.card_Ioc, ← Finset.prod_const]`.

Use `Finset.prod_congr rfl fun c hc => ?_` and prove the remaining obligations. Establish `hc2 : c ≤ mu (lastIdx n)` using `(Finset.mem_Ioc.1 hc).2`. Establish `hc1 : c ∉ TCols mu` using `by simp only [TCols, mem_Ioc]; omega`. Simplify using `only [qs_ext, dif_neg hc1, if_pos hc2, qs_mn_univ]`. Establish `hB : ∏ c ∈ TCols mu, qs_mn (qs_gC n) (qs_ext mu J c) (qs_ext mu I c) = ∏ c : ↥(TCols mu), minorC (J c).1 (I c).1 (J c).2 (I c).2`.

Rewrite using `[← Finset.prod_coe_sort]`. Use `Finset.prod_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[qs_ext_mem, qs_ext_mem, qs_minorC_eq]`. Establish `hC : ∏ c ∈ Finset.Ioc (mu 0) hi, qs_mn (qs_gC n) (qs_ext mu J c) (qs_ext mu I c) = 1`. Use `Finset.prod_eq_one fun c hc => ?_` and prove the remaining obligations.

Establish `hc2 : mu 0 < c` using `(Finset.mem_Ioc.1 hc).1`. Establish `hc1 : c ∉ TCols mu` using `by simp only [TCols, mem_Ioc]; omega`. Establish `hc3 : ¬ c ≤ mu (lastIdx n)` using `by omega`. Simplify using `only [qs_ext, dif_neg hc1, if_neg hc3, qs_mn_empty]`. Establish `hU : detU n ^ mu (lastIdx n) = detU n ^ lo * detU n ^ (mu (lastIdx n) - lo).toNat`.

Rewrite using `[← zpow_natCast, ← zpow_add, Int.toNat_of_nonneg (by omega)]; congr 1; omega`. Rewrite using `[qs_TM, hS, Finset.prod_union, Finset.prod_union, hA, hB, hC, TMat, hU, Units.val_mul, Units.val_pow_eq_pow_val]`. Expand and normalize the polynomial expressions, which then agree. Use `Finset.disjoint_left.2 fun x hx hx' => ?_` and prove the remaining obligations. Simplify using `only [TCols, mem_Ioc] at hx hx'`.

Use linear arithmetic over natural numbers and integers. Use `Finset.disjoint_left.2 fun x hx hx' => ?_` and prove the remaining obligations. Simplify using `only [TCols, mem_Ioc, mem_union] at hx hx'`. Use linear arithmetic over natural numbers and integers.
-/
theorem qs_TMat_eq {mu : Fin n → ℤ} (hmu : Dominant mu) (lo hi : ℤ) (h1 : lo ≤ mu (lastIdx n)) (h2 : mu 0 ≤ hi)
    (J I : TIdx mu) : TMat mu J I = qs_TM lo (Finset.Ioc lo hi) (qs_ext mu J) (qs_ext mu I) := by
  have h0 : mu (lastIdx n) ≤ mu 0 := hmu (Fin.zero_le _)
  have hS : Finset.Ioc lo hi = Finset.Ioc lo (mu (lastIdx n)) ∪ (TCols mu ∪ Finset.Ioc (mu 0) hi) := by
    rw [TCols, Finset.Ioc_union_Ioc_eq_Ioc h0 h2, Finset.Ioc_union_Ioc_eq_Ioc h1 (h0.trans h2)]
  have hA : ∏ c ∈ Finset.Ioc lo (mu (lastIdx n)), qs_mn (qs_gC n) (qs_ext mu J c) (qs_ext mu I c) =
      ((detU n : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) ^ (mu (lastIdx n) - lo).toNat := by
    rw [← Int.card_Ioc, ← Finset.prod_const]
    refine Finset.prod_congr rfl fun c hc => ?_
    have hc2 : c ≤ mu (lastIdx n) := (Finset.mem_Ioc.1 hc).2
    have hc1 : c ∉ TCols mu := by simp only [TCols, mem_Ioc]; omega
    simp only [qs_ext, dif_neg hc1, if_pos hc2, qs_mn_univ]
  have hB : ∏ c ∈ TCols mu, qs_mn (qs_gC n) (qs_ext mu J c) (qs_ext mu I c) =
      ∏ c : ↥(TCols mu), minorC (J c).1 (I c).1 (J c).2 (I c).2 := by
    rw [← Finset.prod_coe_sort]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [qs_ext_mem, qs_ext_mem, qs_minorC_eq]
  have hC : ∏ c ∈ Finset.Ioc (mu 0) hi, qs_mn (qs_gC n) (qs_ext mu J c) (qs_ext mu I c) = 1 := by
    refine Finset.prod_eq_one fun c hc => ?_
    have hc2 : mu 0 < c := (Finset.mem_Ioc.1 hc).1
    have hc1 : c ∉ TCols mu := by simp only [TCols, mem_Ioc]; omega
    have hc3 : ¬ c ≤ mu (lastIdx n) := by omega
    simp only [qs_ext, dif_neg hc1, if_neg hc3, qs_mn_empty]
  have hU : detU n ^ mu (lastIdx n) = detU n ^ lo * detU n ^ (mu (lastIdx n) - lo).toNat := by
    rw [← zpow_natCast, ← zpow_add, Int.toNat_of_nonneg (by omega)]; congr 1; omega
  rw [qs_TM, hS, Finset.prod_union, Finset.prod_union, hA, hB, hC, TMat, hU, Units.val_mul, Units.val_pow_eq_pow_val]
  · ring
  · refine Finset.disjoint_left.2 fun x hx hx' => ?_
    simp only [TCols, mem_Ioc] at hx hx'; omega
  · refine Finset.disjoint_left.2 fun x hx hx' => ?_
    simp only [TCols, mem_Ioc, mem_union] at hx hx'; omega

end Formalism.InvariantFactorPaths.ColumnFamilies
