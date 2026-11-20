import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPlaceIsSquareAndNotIsSquare
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RelIndexSquaresSUnitsNumberFieldStatement
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

def adjoinRoot {G : Type} [CommGroup G] (Q : Subgroup G) (d : G) (hd : d * d ∈ Q) :
    Subgroup G where
  carrier := {x | x ∈ Q ∨ x * d ∈ Q}
  one_mem' := Or.inl Q.one_mem
  mul_mem' := by
    rintro a b (ha | ha) (hb | hb)
    · exact Or.inl (Q.mul_mem ha hb)
    · exact Or.inr (by rw [mul_assoc]; exact Q.mul_mem ha hb)
    · exact Or.inr (by rw [mul_right_comm]; exact Q.mul_mem ha hb)
    · refine Or.inl ?_
      have h := Q.mul_mem (Q.mul_mem ha hb) (Q.inv_mem hd)
      have e : a * d * (b * d) * (d * d)⁻¹ = a * b := by
        rw [mul_mul_mul_comm, mul_inv_cancel_right]
      rwa [e] at h
  inv_mem' := by
    rintro a (ha | ha)
    · exact Or.inl (Q.inv_mem ha)
    · refine Or.inr ?_
      have h := Q.mul_mem (Q.inv_mem ha) hd
      have e : (a * d)⁻¹ * (d * d) = a⁻¹ * d := by
        rw [mul_inv, mul_assoc, inv_mul_cancel_left]
      rwa [e] at h

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, -, rfl⟩`. Conclude with `⟨(y : F), by simp [sq]⟩`. Introduce and unpack `⟨r, hr⟩`. Establish `hr0 : r ≠ 0`.

Introduce and unpack `rfl`. Conclude with `x.ne_zero (by simpa using hr)`. Use `⟨Units.mk0 r hr0, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, mem_sUnits]`. Introduce `v hv`.

Establish `h` using `(mem_sUnits F S x).1 hx v hv`. Rewrite `h` using `[hr, map_mul, ← sq]`. Conclude with `(pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 h`. Use `ext`. Simplify using `[hr, sq]`.
-/
theorem mem_sqs_sUnits_iff_isSquare (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (x : Fˣ) (hx : x ∈ sUnits F S) :
    x ∈ sqs (sUnits F S) ↔ IsSquare (x : F) := by
  constructor
  · rintro ⟨y, -, rfl⟩
    exact ⟨(y : F), by simp [sq]⟩
  · rintro ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact x.ne_zero (by simpa using hr)
    refine ⟨Units.mk0 r hr0, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_sUnits]
      intro v hv
      have h := (mem_sUnits F S x).1 hx v hv
      rw [hr, map_mul, ← sq] at h
      exact (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 h
    · ext
      simp [hr, sq]

open NumberField IsDedekindDomain in
open scoped WithZero in
/- English proof (translation)
Distinguish the cases in `hdQ : d ∈ Q`. Rewrite using `[Subgroup.relIndex_eq_one.2]`. Evaluate the numerical expressions. Introduce and unpack `x (hx | hx)`. Conclude with `hx`.

Simplify using `using Q.mul_mem hx (Q.inv_mem hdQ)`. Establish `h2 : Q.relIndex (_root_.GlobalTheory.QNorm.adjoinRoot Q d hd) = 2`. Use `Subgroup.index_eq_two_iff.2 ⟨⟨d, Or.inr hd⟩, fun b => ?_⟩` and prove the remaining obligations. Rewrite using `[xor_iff_iff_not, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul]`. Establish `hsub : ∀ x : G, x ∈ Q → x * d ∈ Q → False` using `fun x hx hxd => hdQ (by simpa using Q.mul_mem (Q.inv_mem hx) hxd)`.

Break down `b.2 with hb | hb` into its components or cases. Conclude with `⟨fun h h' => hsub _ h' h, fun h => absurd hb h⟩`. Conclude with `⟨fun _ h' => hsub _ h' hb, fun _ => hb⟩`. Use linear arithmetic over natural numbers and integers.
-/
private theorem relIndex_adjoinRoot_ne_zero_and_le_two {G : Type} [CommGroup G] (Q : Subgroup G) (d : G)
    (hd : d * d ∈ Q) :
    Q.relIndex (_root_.GlobalTheory.QNorm.adjoinRoot Q d hd) ≠ 0 ∧
      Q.relIndex (_root_.GlobalTheory.QNorm.adjoinRoot Q d hd) ≤ 2 := by
  by_cases hdQ : d ∈ Q
  · rw [Subgroup.relIndex_eq_one.2]
    · norm_num
    · rintro x (hx | hx)
      · exact hx
      · simpa using Q.mul_mem hx (Q.inv_mem hdQ)
  · have h2 : Q.relIndex (_root_.GlobalTheory.QNorm.adjoinRoot Q d hd) = 2 := by
      refine Subgroup.index_eq_two_iff.2 ⟨⟨d, Or.inr hd⟩, fun b => ?_⟩
      rw [xor_iff_iff_not, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul]
      have hsub : ∀ x : G, x ∈ Q → x * d ∈ Q → False := fun x hx hxd =>
        hdQ (by simpa using Q.mul_mem (Q.inv_mem hx) hxd)
      rcases b.2 with hb | hb
      · exact ⟨fun h h' => hsub _ h' h, fun h => absurd hb h⟩
      · exact ⟨fun _ h' => hsub _ h' hb, fun _ => hb⟩
    omega

open NumberField IsDedekindDomain in
open scoped WithZero in
/- English proof (translation)
Rewrite using `[← (_root_.GlobalTheory.QNorm.mem_sUnits F S x).1 hx v hv]`. Conclude with `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (x : F)`.
-/
private theorem valued_algebraMap_eq_one_of_mem_sUnits {F : Type} [Field F] [NumberField F]
    {S : Finset (HeightOneSpectrum (𝓞 F))} {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) {x : Fˣ}
    (hx : x ∈ _root_.GlobalTheory.QNorm.sUnits F S) :
    Valued.v (algebraMap F (v.adicCompletion F) (x : F)) = 1 := by
  rw [← (_root_.GlobalTheory.QNorm.mem_sUnits F S x).1 hx v hv]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (x : F)

open NumberField IsDedekindDomain in
open scoped WithZero in
/- English proof (translation)
Establish `h2 : Valued.v (2 : v.adicCompletion F) = 1`. Establish `h` using `(hS v hv).1`. Rewrite using `[← h, ← map_ofNat (algebraMap F (v.adicCompletion F)) 2]`. Conclude with `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (2 : F)`. Establish `hx0 : algebraMap F (v.adicCompletion F) (x : F) ≠ 0` using `by simp`.

Establish `hy0 : algebraMap F (v.adicCompletion F) (y : F) ≠ 0` using `by simp`. Rewrite using `[Units.val_mul, map_mul]`. Use `set a := algebraMap F (v.adicCompletion F) (x : F)`. Use `set b := algebraMap F (v.adicCompletion F) (y : F)`. Prove the components needed by the constructor for the conclusion.

Introduce `hab`. Prove the components needed by the constructor for the conclusion. Introduce `ha`. Establish `: b = a * b / a` using `by field_simp`. Rewrite using `[this]`.

Conclude with `hab.div ha`. Introduce `hb`. Establish `: a = a * b / b` using `by field_simp`. Rewrite using `[this]`. Conclude with `hab.div hb`.

Introduce `h`. Distinguish the cases in `ha : IsSquare a`. Conclude with `ha.mul (h.1 ha)`. Establish `hb : ¬ IsSquare b` using `fun hb => ha (h.2 hb)`. Conclude with `_root_.GlobalTheory.QNorm.isSquare_mul_of_nonsquare_units F v h2 a b (valued_algebraMap_eq_one_of_mem_sUnits hv hx) (valued_algebraMap_eq_one_of_mem_sUnits hv hy) ha hb`.
-/
private theorem isSquare_mul_iff_of_mem_sUnits {F : Type} [Field F] [NumberField F]
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : _root_.GlobalTheory.QNorm.admitted F S)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) {x y : Fˣ} (hx : x ∈ _root_.GlobalTheory.QNorm.sUnits F S)
    (hy : y ∈ _root_.GlobalTheory.QNorm.sUnits F S) :
    IsSquare (algebraMap F (v.adicCompletion F) ((x * y : Fˣ) : F)) ↔
      (IsSquare (algebraMap F (v.adicCompletion F) (x : F)) ↔
        IsSquare (algebraMap F (v.adicCompletion F) (y : F))) := by
  have h2 : Valued.v (2 : v.adicCompletion F) = 1 := by
    have h := (hS v hv).1
    rw [← h, ← map_ofNat (algebraMap F (v.adicCompletion F)) 2]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (2 : F)
  have hx0 : algebraMap F (v.adicCompletion F) (x : F) ≠ 0 := by simp
  have hy0 : algebraMap F (v.adicCompletion F) (y : F) ≠ 0 := by simp
  rw [Units.val_mul, map_mul]
  set a := algebraMap F (v.adicCompletion F) (x : F)
  set b := algebraMap F (v.adicCompletion F) (y : F)
  constructor
  · intro hab
    constructor
    · intro ha
      have : b = a * b / a := by field_simp
      rw [this]; exact hab.div ha
    · intro hb
      have : a = a * b / b := by field_simp
      rw [this]; exact hab.div hb
  · intro h
    by_cases ha : IsSquare a
    · exact ha.mul (h.1 ha)
    · have hb : ¬ IsSquare b := fun hb => ha (h.2 hb)
      exact _root_.GlobalTheory.QNorm.isSquare_mul_of_nonsquare_units F v h2 a b
        (valued_algebraMap_eq_one_of_mem_sUnits hv hx) (valued_algebraMap_eq_one_of_mem_sUnits hv hy) ha hb

open NumberField IsDedekindDomain in
open scoped WithZero in
/- English proof (translation)
Distinguish the cases in `h : _root_.GlobalTheory.QNorm.sUnits F S ≤ _root_.GlobalTheory.QNorm.sqSub (algebraMap F (v.adicCompletion F))`. Rewrite using `[Subgroup.relIndex_eq_one.2 h]`. Evaluate the numerical expressions. Take `⟨a, haG, haK⟩` from `SetLike.not_le_iff_exists.1 h`. Use `(Subgroup.index_eq_two_iff.2 ⟨⟨a, haG⟩, fun b => ?_⟩).le` and prove the remaining obligations.

Rewrite using `[xor_iff_iff_not, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul, _root_.GlobalTheory.QNorm.mem_sqSub, _root_.GlobalTheory.QNorm.mem_sqSub, isSquare_mul_iff_of_mem_sUnits hS hv b.2 haG]`. Rewrite `haK` using `[_root_.GlobalTheory.QNorm.mem_sqSub]`. The claim follows by propositional logic.
-/
private theorem relIndex_sqSub_le_two_of_not_mem {F : Type} [Field F] [NumberField F]
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : _root_.GlobalTheory.QNorm.admitted F S)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) :
    (_root_.GlobalTheory.QNorm.sqSub (algebraMap F (v.adicCompletion F))).relIndex
      (_root_.GlobalTheory.QNorm.sUnits F S) ≤ 2 := by
  by_cases h : _root_.GlobalTheory.QNorm.sUnits F S ≤ _root_.GlobalTheory.QNorm.sqSub (algebraMap F (v.adicCompletion F))
  · rw [Subgroup.relIndex_eq_one.2 h]; norm_num
  · obtain ⟨a, haG, haK⟩ := SetLike.not_le_iff_exists.1 h
    refine (Subgroup.index_eq_two_iff.2 ⟨⟨a, haG⟩, fun b => ?_⟩).le
    rw [xor_iff_iff_not, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul,
      _root_.GlobalTheory.QNorm.mem_sqSub, _root_.GlobalTheory.QNorm.mem_sqSub,
      isSquare_mul_iff_of_mem_sUnits hS hv b.2 haG]
    rw [_root_.GlobalTheory.QNorm.mem_sqSub] at haK
    tauto

open NumberField IsDedekindDomain in
open scoped WithZero in
/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert v T hvT ih`. Rewrite using `[Finset.iInf_insert, Finset.card_insert_of_notMem hvT, pow_succ']`. Conclude with `Subgroup.relIndex_inf_le.trans (Nat.mul_le_mul (relIndex_sqSub_le_two_of_not_mem hS (hT v (Finset.mem_insert_self v T))) (ih fun w hw => hT w (Finset.mem_insert_of_mem hw)))`.
-/
private theorem relIndex_iInf_sqSub_le_two_pow_card {F : Type} [Field F] [NumberField F]
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : _root_.GlobalTheory.QNorm.admitted F S)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hT : ∀ v ∈ T, v ∉ S) :
    (⨅ v ∈ T, _root_.GlobalTheory.QNorm.sqSub (algebraMap F (v.adicCompletion F))).relIndex
      (_root_.GlobalTheory.QNorm.sUnits F S) ≤ 2 ^ T.card := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert v T hvT ih =>
    rw [Finset.iInf_insert, Finset.card_insert_of_notMem hvT, pow_succ']
    exact Subgroup.relIndex_inf_le.trans (Nat.mul_le_mul
      (relIndex_sqSub_le_two_of_not_mem hS (hT v (Finset.mem_insert_self v T)))
      (ih fun w hw => hT w (Finset.mem_insert_of_mem hw)))

open NumberField IsDedekindDomain in
open scoped WithZero in

/- English proof (translation)
Introduce `F _ _ δ S hS hδ hsq`. Establish `hQ` using `_root_.GlobalTheory.QNorm.relIndex_sqs_sUnits F S`. Use `set G := _root_.GlobalTheory.QNorm.sUnits F S with hGdef`. Use `set n := S.card + Fintype.card (InfinitePlace F) with hndef`. Use `set Q := _root_.GlobalTheory.QNorm.sqs G with hQdef`.

Establish `hQmap : ∀ u : Fˣ, u ∈ Q ↔ ∃ a ∈ G, a ^ 2 = u` using `fun u => by`. Rewrite using `[hQdef]`. Unfold `_root_.GlobalTheory.QNorm.sqs`. Rewrite using `[Subgroup.mem_map]`. Both sides reduce to the same expression.

Establish `hQG : Q ≤ G` using `fun x hx => by`. Take `⟨a, ha, rfl⟩` from `(hQmap x).1 hx`. Conclude with `G.pow_mem ha 2`. Establish `hQmem : ∀ u : Fˣ, u ∈ G → IsSquare (u : F) → u ∈ Q`. Introduce and unpack `u hu ⟨r, hr⟩`.

Establish `hr0 : r ≠ 0`. Introduce and unpack `rfl`. Conclude with `u.ne_zero (by simpa using hr)`. Use `(hQmap u).2 ⟨Units.mk0 r hr0, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hGdef, _root_.GlobalTheory.QNorm.mem_sUnits]`.

Introduce `v hv`. Establish `h` using `(_root_.GlobalTheory.QNorm.mem_sUnits F S u).1 hu v hv`. Rewrite `h` using `[hr, map_mul, ← sq]`. Simplify using `using (pow_eq_one_iff.1 h).resolve_right two_ne_zero`. Use `ext`.

Simplify using `[hr, sq]`. Establish `hn : 1 ≤ n`. Assume the negation of the conclusion as `h`. Establish `h0 : n = 0` using `by omega`. Rewrite `hQ` using `[h0, pow_zero, Subgroup.relIndex_eq_one]`.

Take `⟨a, -, ha⟩` from `(hQmap δ).1 (hQ hδ)`. Conclude with `hsq ⟨a, by rw [← ha]; simp [sq]⟩`. Establish `hdd : δ * δ ∈ Q` using `(hQmap _).2 ⟨δ, hδ, sq δ⟩`. Take `⟨hQA0, hQA⟩` from `relIndex_adjoinRoot_ne_zero_and_le_two Q δ hdd`. Establish `key : ∀ k, k + 1 ≤ n → ∃ T : Finset (HeightOneSpectrum (𝓞 F)), Disjoint S T ∧ T.card = k ∧ (∀ v ∈ T, IsSquare (algebraMap F (v.adicCompletion F) δ)) ∧ ∀ A : Finset (HeightOneSpectrum (𝓞 F)), ∃ u ∈ G, ∀ v ∈ T, (IsSquare (algebraMap F (v.adicCompletion F) u) ↔ v ∉ A)`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `_`. Conclude with `⟨∅, Finset.disjoint_empty_right S, rfl, by simp, fun _ => ⟨1, G.one_mem, by simp⟩⟩`.

Consider the case `succ k ih`. Introduce `hk`. Take `⟨T, hST, hTk, hTδ, hTpat⟩` from `ih (by omega)`. Establish `hTS : ∀ v ∈ T, v ∉ S` using `fun v hv hvS => Finset.disjoint_left.1 hST hvS hv`. Use `set KT := ⨅ v ∈ T, _root_.GlobalTheory.QNorm.sqSub (algebraMap F (v.adicCompletion F)) with hKTdef`.

Establish `hKT : KT.relIndex G ≤ 2 ^ k` using `hTk ▸ relIndex_iInf_sqSub_le_two_pow_card hS T hTS`. Establish `hex : ∃ u ∈ KT ⊓ G, u ∉ _root_.GlobalTheory.QNorm.adjoinRoot Q δ hdd`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hQK : Q ≤ KT ⊓ G`.

Use `le_inf (fun x hx => ?_) hQG` and prove the remaining obligations. Take `⟨a, -, rfl⟩` from `(hQmap x).1 hx`. Rewrite using `[hKTdef, Subgroup.mem_iInf]`. Introduce `v`. Rewrite using `[Subgroup.mem_iInf]`.

Introduce `_`. Rewrite using `[_root_.GlobalTheory.QNorm.mem_sqSub]`. Conclude with `⟨algebraMap F (v.adicCompletion F) (a : F), by simp [sq]⟩`. Establish `h1` using `Subgroup.relIndex_mul_relIndex Q (KT ⊓ G) G hQK inf_le_right`. Rewrite `h1` using `[Subgroup.inf_relIndex_right, hQ]`.

Establish `h2 : Q.relIndex (KT ⊓ G) ≤ 2` using `(Subgroup.relIndex_le_of_le_right (fun u hu => hcon u hu) hQA0).trans hQA`. Establish `h3 : 2 ^ n ≤ 2 * 2 ^ k` using `h1 ▸ Nat.mul_le_mul h2 hKT`. Establish `h4 : 2 * 2 ^ k < 2 ^ n`. Rewrite using `[← pow_succ']; exact Nat.pow_lt_pow_right (by norm_num) (by omega)`. Use linear arithmetic over natural numbers and integers.

Take `⟨u, ⟨huK, huG⟩, huA⟩` from `hex`. Establish `huK' : ∀ v ∈ T, IsSquare (algebraMap F (v.adicCompletion F) u)`. Introduce `v hv`. Establish `huK2 : u ∈ KT` using `huK`. Rewrite `huK2` using `[hKTdef, Subgroup.mem_iInf]`.

Establish `h` using `huK2 v`. Rewrite `h` using `[Subgroup.mem_iInf]`. Conclude with `(_root_.GlobalTheory.QNorm.mem_sqSub _ u).1 (h hv)`. Establish `hnu : ¬ IsSquare (u : F)` using `fun h => huA (Or.inl (hQmem u huG h))`. Establish `hnuδ : ¬ IsSquare ((u : F) * δ)` using `fun h => huA (Or.inr (hQmem (u * δ) (G.mul_mem huG hδ) (by simpa using h)))`.

Take `⟨v, hvST, hvδ, hvu⟩` from `_root_.GlobalTheory.QNorm.exists_place_isSquare_and_not_isSquare F δ u (S ∪ T) δ.ne_zero u.ne_zero hsq hnu hnuδ`. Establish `hvS : v ∉ S` using `fun h => hvST (Finset.mem_union_left _ h)`. Establish `hvT : v ∉ T` using `fun h => hvST (Finset.mem_union_right _ h)`. Use `⟨insert v T, Finset.disjoint_insert_right.2 ⟨hvS, hST⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.card_insert_of_notMem hvT, hTk]`.

Introduce `w hw`. Break down `Finset.mem_insert.1 hw with rfl | hw` into its components or cases. Conclude with `hvδ`. Conclude with `hTδ w hw`. Introduce `A`.

Take `⟨w, hwG, hw⟩` from `hTpat A`. Distinguish the cases in `hwv : (IsSquare (algebraMap F (v.adicCompletion F) w) ↔ v ∉ A)`. Use `⟨w, hwG, fun x hx => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hx with rfl | hx` into its components or cases. Conclude with `hwv`.

Conclude with `hw x hx`. Use `⟨w * u, G.mul_mem hwG huG, fun x hx => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hx with rfl | hx` into its components or cases. Rewrite using `[isSquare_mul_iff_of_mem_sUnits hS hvS hwG huG, iff_false_intro hvu, iff_false]`. Conclude with `not_iff.1 hwv`.

Rewrite using `[isSquare_mul_iff_of_mem_sUnits hS (hTS x hx) hwG huG]`. Rewrite using `[iff_true_intro (huK' x hx), iff_true]`. Conclude with `hw x hx`. Take `⟨T, h1, h2, h3, h4⟩` from `key (n - 1) (by omega)`. Conclude with `⟨T, h1, by omega, h3, h4⟩`.
-/
theorem _root_.GlobalTheory.QNorm.exists_auxiliary_places : ∀ (F : Type) [Field F] [NumberField F] (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), _root_.GlobalTheory.QNorm.admitted F S → δ ∈ _root_.GlobalTheory.QNorm.sUnits F S → ¬ IsSquare (δ : F) → ∃ T : Finset (HeightOneSpectrum (𝓞 F)), Disjoint S T ∧ T.card + 1 = S.card + Fintype.card (InfinitePlace F) ∧ (∀ v ∈ T, IsSquare (algebraMap F (v.adicCompletion F) δ)) ∧ ∀ A : Finset (HeightOneSpectrum (𝓞 F)), ∃ u ∈ _root_.GlobalTheory.QNorm.sUnits F S, ∀ v ∈ T, (IsSquare (algebraMap F (v.adicCompletion F) u) ↔ v ∉ A) := by
  intro F _ _ δ S hS hδ hsq
  classical
  have hQ := _root_.GlobalTheory.QNorm.relIndex_sqs_sUnits F S
  set G := _root_.GlobalTheory.QNorm.sUnits F S with hGdef
  set n := S.card + Fintype.card (InfinitePlace F) with hndef
  set Q := _root_.GlobalTheory.QNorm.sqs G with hQdef
  have hQmap : ∀ u : Fˣ, u ∈ Q ↔ ∃ a ∈ G, a ^ 2 = u := fun u => by
    rw [hQdef]; unfold _root_.GlobalTheory.QNorm.sqs; rw [Subgroup.mem_map]; rfl
  have hQG : Q ≤ G := fun x hx => by
    obtain ⟨a, ha, rfl⟩ := (hQmap x).1 hx
    exact G.pow_mem ha 2
  have hQmem : ∀ u : Fˣ, u ∈ G → IsSquare (u : F) → u ∈ Q := by
    rintro u hu ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact u.ne_zero (by simpa using hr)
    refine (hQmap u).2 ⟨Units.mk0 r hr0, ?_, ?_⟩
    · rw [hGdef, _root_.GlobalTheory.QNorm.mem_sUnits]
      intro v hv
      have h := (_root_.GlobalTheory.QNorm.mem_sUnits F S u).1 hu v hv
      rw [hr, map_mul, ← sq] at h
      simpa using (pow_eq_one_iff.1 h).resolve_right two_ne_zero
    · ext
      simp [hr, sq]
  have hn : 1 ≤ n := by
    by_contra h
    have h0 : n = 0 := by omega
    rw [h0, pow_zero, Subgroup.relIndex_eq_one] at hQ
    obtain ⟨a, -, ha⟩ := (hQmap δ).1 (hQ hδ)
    exact hsq ⟨a, by rw [← ha]; simp [sq]⟩
  have hdd : δ * δ ∈ Q := (hQmap _).2 ⟨δ, hδ, sq δ⟩
  obtain ⟨hQA0, hQA⟩ := relIndex_adjoinRoot_ne_zero_and_le_two Q δ hdd
  have key : ∀ k, k + 1 ≤ n → ∃ T : Finset (HeightOneSpectrum (𝓞 F)), Disjoint S T ∧
      T.card = k ∧ (∀ v ∈ T, IsSquare (algebraMap F (v.adicCompletion F) δ)) ∧
      ∀ A : Finset (HeightOneSpectrum (𝓞 F)), ∃ u ∈ G, ∀ v ∈ T,
        (IsSquare (algebraMap F (v.adicCompletion F) u) ↔ v ∉ A) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨∅, Finset.disjoint_empty_right S, rfl, by simp, fun _ => ⟨1, G.one_mem, by simp⟩⟩
    | succ k ih =>
      intro hk
      obtain ⟨T, hST, hTk, hTδ, hTpat⟩ := ih (by omega)
      have hTS : ∀ v ∈ T, v ∉ S := fun v hv hvS => Finset.disjoint_left.1 hST hvS hv
      set KT := ⨅ v ∈ T, _root_.GlobalTheory.QNorm.sqSub (algebraMap F (v.adicCompletion F)) with hKTdef
      have hKT : KT.relIndex G ≤ 2 ^ k := hTk ▸ relIndex_iInf_sqSub_le_two_pow_card hS T hTS
      have hex : ∃ u ∈ KT ⊓ G, u ∉ _root_.GlobalTheory.QNorm.adjoinRoot Q δ hdd := by
        by_contra hcon
        push_neg at hcon
        have hQK : Q ≤ KT ⊓ G := by
          refine le_inf (fun x hx => ?_) hQG
          obtain ⟨a, -, rfl⟩ := (hQmap x).1 hx
          rw [hKTdef, Subgroup.mem_iInf]
          intro v
          rw [Subgroup.mem_iInf]
          intro _
          rw [_root_.GlobalTheory.QNorm.mem_sqSub]
          exact ⟨algebraMap F (v.adicCompletion F) (a : F), by simp [sq]⟩
        have h1 := Subgroup.relIndex_mul_relIndex Q (KT ⊓ G) G hQK inf_le_right
        rw [Subgroup.inf_relIndex_right, hQ] at h1
        have h2 : Q.relIndex (KT ⊓ G) ≤ 2 :=
          (Subgroup.relIndex_le_of_le_right (fun u hu => hcon u hu) hQA0).trans hQA
        have h3 : 2 ^ n ≤ 2 * 2 ^ k := h1 ▸ Nat.mul_le_mul h2 hKT
        have h4 : 2 * 2 ^ k < 2 ^ n := by
          rw [← pow_succ']; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
        omega
      obtain ⟨u, ⟨huK, huG⟩, huA⟩ := hex
      have huK' : ∀ v ∈ T, IsSquare (algebraMap F (v.adicCompletion F) u) := by
        intro v hv
        have huK2 : u ∈ KT := huK
        rw [hKTdef, Subgroup.mem_iInf] at huK2
        have h := huK2 v
        rw [Subgroup.mem_iInf] at h
        exact (_root_.GlobalTheory.QNorm.mem_sqSub _ u).1 (h hv)
      have hnu : ¬ IsSquare (u : F) := fun h => huA (Or.inl (hQmem u huG h))
      have hnuδ : ¬ IsSquare ((u : F) * δ) := fun h =>
        huA (Or.inr (hQmem (u * δ) (G.mul_mem huG hδ) (by simpa using h)))
      obtain ⟨v, hvST, hvδ, hvu⟩ := _root_.GlobalTheory.QNorm.exists_place_isSquare_and_not_isSquare F δ u (S ∪ T)
        δ.ne_zero u.ne_zero hsq hnu hnuδ
      have hvS : v ∉ S := fun h => hvST (Finset.mem_union_left _ h)
      have hvT : v ∉ T := fun h => hvST (Finset.mem_union_right _ h)
      refine ⟨insert v T, Finset.disjoint_insert_right.2 ⟨hvS, hST⟩, ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hvT, hTk]
      · intro w hw
        rcases Finset.mem_insert.1 hw with rfl | hw
        · exact hvδ
        · exact hTδ w hw
      · intro A
        obtain ⟨w, hwG, hw⟩ := hTpat A
        by_cases hwv : (IsSquare (algebraMap F (v.adicCompletion F) w) ↔ v ∉ A)
        · refine ⟨w, hwG, fun x hx => ?_⟩
          rcases Finset.mem_insert.1 hx with rfl | hx
          · exact hwv
          · exact hw x hx
        · refine ⟨w * u, G.mul_mem hwG huG, fun x hx => ?_⟩
          rcases Finset.mem_insert.1 hx with rfl | hx
          · rw [isSquare_mul_iff_of_mem_sUnits hS hvS hwG huG, iff_false_intro hvu, iff_false]
            exact not_iff.1 hwv
          · rw [isSquare_mul_iff_of_mem_sUnits hS (hTS x hx) hwG huG]
            rw [iff_true_intro (huK' x hx), iff_true]
            exact hw x hx
  obtain ⟨T, h1, h2, h3, h4⟩ := key (n - 1) (by omega)
  exact ⟨T, h1, by omega, h3, h4⟩

end GlobalTheory.QNorm
