import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembDefs
import Formalism.SharpRestriction.GrowthBounds.ValuationLowestDegreeMapFractionField
import Formalism.SharpRestriction.GrowthBounds.GLWeightTheory

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory

section Sm

variable {R : Type} [CommRing R] {ι : Type} {n : ℕ} [NeZero n]

/- English proof (translation)
Introduce `d hd`. Simplify using `only [sDegs, Finset.mem_biUnion] at hd`. Take `⟨m, hm, hdm⟩` from `hd`. Establish `ht : twistSub LL S j (C c : MvPolynomial (ι × Fin n) R) = MvPolynomial.C (coefL R n c)`. Simplify using `[twistSub]`.

Rewrite `hm`, `hdm` using `[ht]`. Rewrite `hdm` using `[MvPolynomial.coeff_C]`. Use `split_ifs at hdm with hm0`. Establish `h1` using `LaurentPolynomial.support_C_mul_T ((algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n)) (MvPolynomial.C c)) 0`. Rewrite `h1` using `[LaurentPolynomial.T_zero, mul_one]`.

Conclude with `Finset.mem_singleton.mp (h1 hdm)`. Simplify using `at hdm`.
-/
private lemma eq_zero_of_mem_sDegs_C (LL : Letters ι) (S : Set ι) (c : R) (j : Fin n) :
    ∀ d ∈ sDegs LL S j (C c : MvPolynomial (ι × Fin n) R), d = 0 := by
  intro d hd
  simp only [sDegs, Finset.mem_biUnion] at hd
  obtain ⟨m, hm, hdm⟩ := hd
  have ht : twistSub LL S j (C c : MvPolynomial (ι × Fin n) R) = MvPolynomial.C (coefL R n c) := by
    simp [twistSub]
  rw [ht] at hm hdm
  rw [MvPolynomial.coeff_C] at hdm
  split_ifs at hdm with hm0
  · have h1 := LaurentPolynomial.support_C_mul_T
      ((algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n)) (MvPolynomial.C c)) 0
    rw [LaurentPolynomial.T_zero, mul_one] at h1
    exact Finset.mem_singleton.mp (h1 hdm)
  · simp at hdm

/- English proof (translation)
Unfold `valS`. Use `Finset.le_inf fun d hd => ?_` and prove the remaining obligations. Rewrite using `[eq_zero_of_mem_sDegs_C LL S c _ d hd]`. Both sides reduce to the same expression.
-/
theorem valS_C_nnR (LL : Letters ι) (S : Set ι) (c : R) :
    0 ≤ valS LL S (C c : MvPolynomial (ι × Fin n) R) := by
  unfold valS
  refine Finset.le_inf fun d hd => ?_
  rw [eq_zero_of_mem_sDegs_C LL S c _ d hd]
  rfl

/- English proof (translation)
Introduce `d hd`. Simplify using `only [sDegs, Finset.mem_biUnion, MvPolynomial.mem_support_iff, Finsupp.mem_support_iff] at hd ⊢`. Take `⟨m, hm, hdm⟩` from `hd`. Establish `h1 : twistSub LL S j (c • F) = MvPolynomial.C (coefL R n c) * twistSub LL S j F`. Rewrite using `[MvPolynomial.smul_eq_C_mul F c, map_mul]`.

Use `congr 1`. Simplify using `[twistSub]`. Establish `key : ∀ q : GLLaurent R n, (coefL R n c * q).coeff d = (algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n)) (MvPolynomial.C c) * q.coeff d`. Introduce `q`. Establish `hs : coefL R n c = AddMonoidAlgebra.single 0 ((algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n)) (MvPolynomial.C c))`.

Rewrite using `[LaurentPolynomial.single_eq_C_mul_T, LaurentPolynomial.T_zero, mul_one]`. Both sides reduce to the same expression. Rewrite using `[hs, AddMonoidAlgebra.coeff_single_zero_mul]`. Rewrite `hm`, `hdm` using `[h1, MvPolynomial.coeff_C_mul]`. Rewrite `hdm` using `[key]`.

Establish `hq : (MvPolynomial.coeff m (twistSub LL S j F)).coeff d ≠ 0` using `right_ne_zero_of_mul hdm`. Use `⟨m, fun h0 => ?_, hq⟩` and prove the remaining obligations. Rewrite `hq` using `[h0]`. Conclude with `hq rfl`.
-/
private lemma sDegs_smul_subset_sDegs (LL : Letters ι) (S : Set ι) (c : R) (F : MvPolynomial (ι × Fin n) R)
    (j : Fin n) : sDegs LL S j (c • F) ⊆ sDegs LL S j F := by
  intro d hd
  simp only [sDegs, Finset.mem_biUnion, MvPolynomial.mem_support_iff, Finsupp.mem_support_iff] at hd ⊢
  obtain ⟨m, hm, hdm⟩ := hd
  have h1 : twistSub LL S j (c • F) = MvPolynomial.C (coefL R n c) * twistSub LL S j F := by
    rw [MvPolynomial.smul_eq_C_mul F c, map_mul]
    congr 1
    simp [twistSub]
  have key : ∀ q : GLLaurent R n, (coefL R n c * q).coeff d =
      (algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n)) (MvPolynomial.C c) * q.coeff d := by
    intro q
    have hs : coefL R n c = AddMonoidAlgebra.single 0
        ((algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n)) (MvPolynomial.C c)) := by
      rw [LaurentPolynomial.single_eq_C_mul_T, LaurentPolynomial.T_zero, mul_one]
      rfl
    rw [hs, AddMonoidAlgebra.coeff_single_zero_mul]
  rw [h1, MvPolynomial.coeff_C_mul] at hm hdm
  rw [key] at hdm
  have hq : (MvPolynomial.coeff m (twistSub LL S j F)).coeff d ≠ 0 := right_ne_zero_of_mul hdm
  refine ⟨m, fun h0 => ?_, hq⟩
  rw [h0] at hq
  exact hq rfl

/- English proof (translation)
Unfold `valS`. Conclude with `Finset.inf_mono (sDegs_smul_subset_sDegs LL S c F _)`.
-/
theorem valS_smul_geR (LL : Letters ι) (S : Set ι) (c : R) (F : MvPolynomial (ι × Fin n) R) :
    valS LL S F ≤ valS LL S (c • F) := by
  unfold valS
  exact Finset.inf_mono (sDegs_smul_subset_sDegs LL S c F _)

/- English proof (translation)
Unfold `lam1S`. Use `Finset.sup_le fun d hd => ?_` and prove the remaining obligations. Rewrite using `[eq_zero_of_mem_sDegs_C LL S c _ d hd]`. Both sides reduce to the same expression.
-/
theorem lowest_weight_C_nonpos (LL : Letters ι) (S : Set ι) (c : R) :
    lam1S LL S (C c : MvPolynomial (ι × Fin n) R) ≤ 0 := by
  unfold lam1S
  refine Finset.sup_le fun d hd => ?_
  rw [eq_zero_of_mem_sDegs_C LL S c _ d hd]
  rfl

/- English proof (translation)
Unfold `lam1S`. Conclude with `Finset.sup_mono (sDegs_smul_subset_sDegs LL S c F _)`.
-/
theorem lowest_weight_smul_le (LL : Letters ι) (S : Set ι) (c : R) (F : MvPolynomial (ι × Fin n) R) :
    lam1S LL S (c • F) ≤ lam1S LL S F := by
  unfold lam1S
  exact Finset.sup_mono (sDegs_smul_subset_sDegs LL S c F _)

/- English proof (translation)
Simplify using `[valS, sDegs]`.
-/
theorem valS_zeroR (LL : Letters ι) (S : Set ι) : valS LL S (0 : MvPolynomial (ι × Fin n) R) = ⊤ := by
  simp [valS, sDegs]

/- English proof (translation)
Simplify using `[lam1S, sDegs]`.
-/
theorem lowest_weight_zero_eq_bot (LL : Letters ι) (S : Set ι) : lam1S LL S (0 : MvPolynomial (ι × Fin n) R) = ⊥ := by
  simp [lam1S, sDegs]

end Sm

section Sat

variable {O : Type} [CommRing O] [IsDomain O] {ι : Type} {n : ℕ} [NeZero n]

/- English proof (translation)
Establish `ha : algebraMap O (KK O) c ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective O (KK O))).mpr hc`. Rewrite using `[MvPolynomial.smul_eq_C_mul x c, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul, smul_smul, inv_mul_cancel₀ ha, one_smul]`.
-/
theorem map_smul_inv (c : O) (hc : c ≠ 0) (x : MvPolynomial (ι × Fin n) O) :
    MvPolynomial.map (algebraMap O (KK O)) x =
      (algebraMap O (KK O) c)⁻¹ • MvPolynomial.map (algebraMap O (KK O)) (c • x) := by
  have ha : algebraMap O (KK O) c ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (KK O))).mpr hc
  rw [MvPolynomial.smul_eq_C_mul x c, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul,
    smul_smul, inv_mul_cancel₀ ha, one_smul]

/- English proof (translation)
Establish `hnz : ∀ z : GLCoord O n, (algebraMap (MvPolynomial (Fin n × Fin n) O) (GLCoord O n)) (MvPolynomial.C c) * z = 0 → z = 0`. Introduce `z hz`. Take `⟨⟨a, s⟩, rfl⟩` from `IsLocalization.mk'_surjective (Submonoid.powers (genMat O n).det) z`. Rewrite `hz` using `[IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_zero_iff]`. Take `⟨t, ht⟩` from `hz`.

Rewrite using `[IsLocalization.mk'_eq_zero_iff]`. Use `⟨t, ?_⟩` and prove the remaining obligations. Establish `hC : (MvPolynomial.C c : MvPolynomial (Fin n × Fin n) O) ≠ 0`. Rewrite using `[Ne, MvPolynomial.C_eq_zero]` and apply the resulting hypothesis. Rewrite `ht` using `[← mul_assoc, mul_comm (t : MvPolynomial (Fin n × Fin n) O), mul_assoc]`.

Conclude with `(mul_eq_zero.mp ht).resolve_left hC`. Introduce `d hd`. Simplify using `only [sDegs, Finset.mem_biUnion, MvPolynomial.mem_support_iff, Finsupp.mem_support_iff] at hd ⊢`. Take `⟨m, hm, hdm⟩` from `hd`. Establish `h1 : twistSub LL S j (c • x) = MvPolynomial.C (coefL O n c) * twistSub LL S j x`.

Rewrite using `[MvPolynomial.smul_eq_C_mul x c, map_mul]`. Use `congr 1`. Simplify using `[twistSub]`. Establish `key : ∀ q : GLLaurent O n, (coefL O n c * q).coeff d = (algebraMap (MvPolynomial (Fin n × Fin n) O) (GLCoord O n)) (MvPolynomial.C c) * q.coeff d`. Introduce `q`.

Establish `hs : coefL O n c = AddMonoidAlgebra.single 0 ((algebraMap (MvPolynomial (Fin n × Fin n) O) (GLCoord O n)) (MvPolynomial.C c))`. Rewrite using `[LaurentPolynomial.single_eq_C_mul_T, LaurentPolynomial.T_zero, mul_one]`. Both sides reduce to the same expression. Rewrite using `[hs, AddMonoidAlgebra.coeff_single_zero_mul]`. Establish `hq : (coefL O n c * MvPolynomial.coeff m (twistSub LL S j x)).coeff d ≠ 0`.

Rewrite using `[key]`. Conclude with `fun h0 => hdm (hnz _ h0)`. Use `⟨m, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[h1, MvPolynomial.coeff_C_mul]`. Introduce `h0`.

Rewrite `hq` using `[h0]`. Conclude with `hq rfl`. Rewrite using `[h1, MvPolynomial.coeff_C_mul]`. Conclude with `hq`.
-/
private lemma sDegs_subset_sDegs_smul_of_ne_zero (LL : Letters ι) (S : Set ι) (c : O) (hc : c ≠ 0) (x : MvPolynomial (ι × Fin n) O)
    (j : Fin n) : sDegs LL S j x ⊆ sDegs LL S j (c • x) := by
  have hnz : ∀ z : GLCoord O n,
      (algebraMap (MvPolynomial (Fin n × Fin n) O) (GLCoord O n)) (MvPolynomial.C c) * z = 0 → z = 0 := by
    intro z hz
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (genMat O n).det) z
    rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_zero_iff] at hz
    obtain ⟨t, ht⟩ := hz
    rw [IsLocalization.mk'_eq_zero_iff]
    refine ⟨t, ?_⟩
    have hC : (MvPolynomial.C c : MvPolynomial (Fin n × Fin n) O) ≠ 0 := by
      rwa [Ne, MvPolynomial.C_eq_zero]
    rw [← mul_assoc, mul_comm (t : MvPolynomial (Fin n × Fin n) O), mul_assoc] at ht
    exact (mul_eq_zero.mp ht).resolve_left hC
  intro d hd
  simp only [sDegs, Finset.mem_biUnion, MvPolynomial.mem_support_iff, Finsupp.mem_support_iff] at hd ⊢
  obtain ⟨m, hm, hdm⟩ := hd
  have h1 : twistSub LL S j (c • x) = MvPolynomial.C (coefL O n c) * twistSub LL S j x := by
    rw [MvPolynomial.smul_eq_C_mul x c, map_mul]
    congr 1
    simp [twistSub]
  have key : ∀ q : GLLaurent O n, (coefL O n c * q).coeff d =
      (algebraMap (MvPolynomial (Fin n × Fin n) O) (GLCoord O n)) (MvPolynomial.C c) * q.coeff d := by
    intro q
    have hs : coefL O n c = AddMonoidAlgebra.single 0
        ((algebraMap (MvPolynomial (Fin n × Fin n) O) (GLCoord O n)) (MvPolynomial.C c)) := by
      rw [LaurentPolynomial.single_eq_C_mul_T, LaurentPolynomial.T_zero, mul_one]
      rfl
    rw [hs, AddMonoidAlgebra.coeff_single_zero_mul]
  have hq : (coefL O n c * MvPolynomial.coeff m (twistSub LL S j x)).coeff d ≠ 0 := by
    rw [key]
    exact fun h0 => hdm (hnz _ h0)
  refine ⟨m, ?_, ?_⟩
  · rw [h1, MvPolynomial.coeff_C_mul]
    intro h0
    rw [h0] at hq
    exact hq rfl
  · rw [h1, MvPolynomial.coeff_C_mul]
    exact hq

/- English proof (translation)
Unfold `valS`. Conclude with `Finset.inf_mono (sDegs_subset_sDegs_smul_of_ne_zero LL S c hc x _)`.
-/
theorem valS_sat (LL : Letters ι) (S : Set ι) (c : O) (hc : c ≠ 0) (x : MvPolynomial (ι × Fin n) O) :
    valS LL S (c • x) ≤ valS LL S x := by
  unfold valS
  exact Finset.inf_mono (sDegs_subset_sDegs_smul_of_ne_zero LL S c hc x _)

/- English proof (translation)
Unfold `lam1S`. Conclude with `Finset.sup_mono (sDegs_subset_sDegs_smul_of_ne_zero LL S c hc x _)`.
-/
theorem lowest_weight_le_smul_nonzero (LL : Letters ι) (S : Set ι) (c : O) (hc : c ≠ 0) (x : MvPolynomial (ι × Fin n) O) :
    lam1S LL S x ≤ lam1S LL S (c • x) := by
  unfold lam1S
  exact Finset.sup_mono (sDegs_subset_sDegs_smul_of_ne_zero LL S c hc x _)

end Sat

section Dec

variable {O : Type} [CommRing O] [IsDomain O] {ι G : Type} (π : ι → G) {n : ℕ} [NeZero n] (LL : Letters ι)
  (Cv Cl : G → Set (Set ι × ℤ)) (F : MvPolynomial (ι × Fin n) O)

def partOf (j : G) (mo : ι × Fin n →₀ ℕ) : ι × Fin n →₀ ℕ := mo.filter fun v => π v.1 = j

def XG (j : G) : Submodule O (MvPolynomial (ι × Fin n) O) where
  carrier := {A | (∀ mo ∈ A.support, mo ∈ F.support.image (partOf π j)) ∧
    (∀ q ∈ Cv j, ((q.2 : ℤ) : WithTop ℤ) ≤ valS LL q.1 A) ∧ ∀ q ∈ Cl j, lam1S LL q.1 A ≤ ((q.2 : ℤ) : WithBot ℤ)}
  add_mem' := by
    rintro A B ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩
    refine ⟨fun mo hmo => ?_, fun q hq => ?_, fun q hq => ?_⟩
    · rcases Finset.mem_union.1 (MvPolynomial.support_add hmo) with h | h
      · exact a1 mo h
      · exact b1 mo h
    · exact le_trans (le_min (a2 q hq) (b2 q hq)) (flt_valS_add LL q.1 A B)
    · exact le_trans (flt_lam1S_add LL q.1 A B) (max_le (a3 q hq) (b3 q hq))
  zero_mem' := by
    refine ⟨fun mo hmo => by simp at hmo, fun q _ => ?_, fun q _ => ?_⟩
    · rw [valS_zeroR]; exact le_top
    · rw [lowest_weight_zero_eq_bot]; exact bot_le
  smul_mem' := by
    rintro c A ⟨a1, a2, a3⟩
    refine ⟨fun mo hmo => a1 mo (MvPolynomial.support_smul hmo), fun q hq => ?_, fun q hq => ?_⟩
    · exact le_trans (a2 q hq) (valS_smul_geR LL q.1 c A)
    · exact le_trans (lowest_weight_smul_le LL q.1 c A) (a3 q hq)

/- English proof (translation)
Conclude with `Iff.rfl`.
-/
theorem mem_XG (j : G) (A : MvPolynomial (ι × Fin n) O) : A ∈ XG π LL Cv Cl F j ↔
    (∀ mo ∈ A.support, mo ∈ F.support.image (partOf π j)) ∧
    (∀ q ∈ Cv j, ((q.2 : ℤ) : WithTop ℤ) ≤ valS LL q.1 A) ∧ ∀ q ∈ Cl j, lam1S LL q.1 A ≤ ((q.2 : ℤ) : WithBot ℤ) := by
  exact Iff.rfl

/- English proof (translation)
Proceed by induction on `h using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨x, hx, rfl⟩` from `hy`. Conclude with `⟨1, fun _ => x, fun _ j => hx j, by simp⟩`. Consider the case `zero`.

Conclude with `⟨0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, by simp⟩`. Consider the case `add y z _ _ hy hz`. Take `⟨N1, A1, h1, rfl⟩` from `hy`. Take `⟨N2, A2, h2, rfl⟩` from `hz`. Use `⟨N1 + N2, Fin.append A1 A2, ?_, ?_⟩` and prove the remaining obligations.

Introduce `i j`. Use `Fin.addCases (fun i => ?_) (fun i => ?_) i` and prove the remaining obligations. Simplify using `[h1]`. Simplify using `[h2]`. Rewrite using `[Fin.sum_univ_add]`.

Simplify using the standard rewrite rules. Consider the case `smul c y _ hy`. Take `⟨N, A, hA, rfl⟩` from `hy`. Take `⟨j0⟩` from `(inferInstance : Nonempty G)`. Use `⟨N, fun i j => if j = j0 then c • A i j else A i j, ?_, ?_⟩` and prove the remaining obligations.

Introduce `i j show (if j = j0 then c • A i j else A i j) ∈ X j split_ifs with hj`. Substitute `hj` using the available equality. Conclude with `(X _).smul_mem c (hA i _)`. Conclude with `hA i j`. Rewrite using `[Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `show c • ∏ j, A i j = ∏ j, (if j = j0 then c • A i j else A i j)`. Rewrite using `[← Finset.mul_prod_erase _ (fun j => A i j) (Finset.mem_univ j0), ← Finset.mul_prod_erase _ (fun j => if j = j0 then c • A i j else A i j) (Finset.mem_univ j0)]`. Simplify using `only [if_pos rfl, eq_self_iff_true, if_true]`. Rewrite using `[Finset.prod_congr rfl (fun j hj => if_neg (Finset.ne_of_mem_erase hj)), smul_mul_assoc]`.
-/
theorem sum_of_span [Fintype G] [Nonempty G] {σ : Type} (X : G → Submodule O (MvPolynomial σ O)) (P : MvPolynomial σ O)
    (h : P ∈ Submodule.span O {y | ∃ x : G → MvPolynomial σ O, (∀ j, x j ∈ X j) ∧ y = ∏ j, x j}) :
    ∃ (N : ℕ) (A : Fin N → G → MvPolynomial σ O), (∀ i j, A i j ∈ X j) ∧ P = ∑ i, ∏ j, A i j := by
  induction h using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨1, fun _ => x, fun _ j => hx j, by simp⟩
  | zero =>
    exact ⟨0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨N1, A1, h1, rfl⟩ := hy
    obtain ⟨N2, A2, h2, rfl⟩ := hz
    refine ⟨N1 + N2, Fin.append A1 A2, ?_, ?_⟩
    · intro i j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp [h1]
      · simp [h2]
    · rw [Fin.sum_univ_add]
      simp
  | smul c y _ hy =>
    obtain ⟨N, A, hA, rfl⟩ := hy
    obtain ⟨j0⟩ := (inferInstance : Nonempty G)
    refine ⟨N, fun i j => if j = j0 then c • A i j else A i j, ?_, ?_⟩
    · intro i j
      show (if j = j0 then c • A i j else A i j) ∈ X j
      split_ifs with hj
      · subst hj
        exact (X _).smul_mem c (hA i _)
      · exact hA i j
    · rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      show c • ∏ j, A i j = ∏ j, (if j = j0 then c • A i j else A i j)
      rw [← Finset.mul_prod_erase _ (fun j => A i j) (Finset.mem_univ j0),
        ← Finset.mul_prod_erase _ (fun j => if j = j0 then c • A i j else A i j) (Finset.mem_univ j0)]
      simp only [if_pos rfl, eq_self_iff_true, if_true]
      rw [Finset.prod_congr rfl (fun j hj => if_neg (Finset.ne_of_mem_erase hj)), smul_mul_assoc]

/- English proof (translation)
Establish `hpart : ∀ j (mo M : ι × Fin n →₀ ℕ), (∀ v ∈ mo.support, π v.1 = j) → (∀ v ∈ M.support, π v.1 ≠ j) → partOf π j (mo + M) = mo`. Introduce `j mo M hmo hM`. Use extensionality with `v`. Simplify using `only [partOf, Finsupp.filter_apply, Finsupp.add_apply]`. Use `split_ifs with h`.

Establish `hMv : M v = 0`. Assume the negation of the conclusion as `hne`. Conclude with `hM v (Finsupp.mem_support_iff.mpr hne) h`. Rewrite using `[hMv, add_zero]`. Establish `hmv : mo v = 0`.

Assume the negation of the conclusion as `hne`. Conclude with `h (hmo v (Finsupp.mem_support_iff.mpr hne))`. Rewrite using `[hmv]`. Establish `hsp` using `hA O G (ι × Fin n) (fun v => π v.1) (XG π LL Cv Cl F) ?h1 ?h2 ?h3 F ?h4`. Conclude with `sum_of_span _ F hsp`.

Introduce `j x hx`. Rewrite using `[MvPolynomial.mem_supported]`. Introduce `v hv`. Take `⟨d, hd, hvd⟩` from `(MvPolynomial.mem_vars v).mp hv`. Take `⟨mo, -, rfl⟩` from `Finset.mem_image.mp (hx.1 d hd)`.

Unfold `partOf at hvd`. Rewrite `hvd` using `[Finsupp.mem_support_iff, Finsupp.filter_apply]`. Assume the negation of the conclusion as `hne`. Conclude with `hvd (if_neg hne)`. Introduce `j`.

Conclude with `⟨F.support.image (partOf π j), fun x hx mo hmo => hx.1 mo hmo⟩`. Introduce `j c x hc hcx`. Take `⟨a1, a2, a3⟩` from `hcx`. Use `⟨fun mo hmo => a1 mo ?_, fun q hq => (a2 q hq).trans (valS_sat LL q.1 c hc x), fun q hq => (lowest_weight_le_smul_nonzero LL q.1 c hc x).trans (a3 q hq)⟩` and prove the remaining obligations. Rewrite using `[MvPolynomial.mem_support_iff, MvPolynomial.coeff_smul, smul_eq_mul]`.

Conclude with `mul_ne_zero hc (MvPolynomial.mem_support_iff.mp hmo)`. Introduce `j`. Take `⟨s, cM, hMs, hcM, hF, hsupp, hvals⟩` from `hS O ι n LL {i | π i = j} F`. Establish `hmem : ∑ M ∈ s, cM M * monomial M 1 ∈ Submodule.span O {y | ∃ x ∈ XG π LL Cv Cl F j, ∃ M ∈ supported O {v : ι × Fin n | π v.1 ≠ j}, y = x * M}`. Use `Submodule.sum_mem _ fun M hM => Submodule.subset_span ⟨cM M, ?_, monomial M 1, ?_, rfl⟩` and prove the remaining obligations.

Use `⟨fun mo hmo => Finset.mem_image.mpr ⟨mo + M, hsupp M hM mo hmo, hpart j mo M ?_ ?_⟩, fun q hq => (hv j q hq).trans (hvals M hM q.1 (hCv j q hq)).1, fun q hq => (hvals M hM q.1 (hCl j q hq)).2.trans (hl j q hq)⟩` and prove the remaining obligations. Introduce `v hv`. Establish `hvars : v ∈ (cM M).vars` using `(MvPolynomial.mem_vars v).mpr ⟨mo, hmo, hv⟩`. Conclude with `(MvPolynomial.mem_supported.mp (hcM M hM)) hvars`. Introduce `v hv`.

Conclude with `hMs M hM v hv`. Rewrite using `[MvPolynomial.mem_supported, MvPolynomial.vars_monomial one_ne_zero]`. Introduce `v hv`. Conclude with `hMs M hM v hv`. Rewrite `hmem` using `[← hF]`. Then use the resulting hypothesis.
-/
theorem decGen (hA : ATL) (hS : ValSlice) [IsPrincipalIdealRing O] [Fintype G] [Nonempty G]
    (hCv : ∀ j, ∀ q ∈ Cv j, q.1 ⊆ {i | π i = j}) (hCl : ∀ j, ∀ q ∈ Cl j, q.1 ⊆ {i | π i = j})
    (hv : ∀ j, ∀ q ∈ Cv j, ((q.2 : ℤ) : WithTop ℤ) ≤ valS LL q.1 F)
    (hl : ∀ j, ∀ q ∈ Cl j, lam1S LL q.1 F ≤ ((q.2 : ℤ) : WithBot ℤ)) :
    ∃ (N : ℕ) (A : Fin N → G → MvPolynomial (ι × Fin n) O),
      (∀ i j, A i j ∈ XG π LL Cv Cl F j) ∧ F = ∑ i, ∏ j, A i j := by
  classical
  have hpart : ∀ j (mo M : ι × Fin n →₀ ℕ), (∀ v ∈ mo.support, π v.1 = j) → (∀ v ∈ M.support, π v.1 ≠ j) →
      partOf π j (mo + M) = mo := by
    intro j mo M hmo hM
    ext v
    simp only [partOf, Finsupp.filter_apply, Finsupp.add_apply]
    split_ifs with h
    · have hMv : M v = 0 := by
        by_contra hne
        exact hM v (Finsupp.mem_support_iff.mpr hne) h
      rw [hMv, add_zero]
    · have hmv : mo v = 0 := by
        by_contra hne
        exact h (hmo v (Finsupp.mem_support_iff.mpr hne))
      rw [hmv]
  have hsp := hA O G (ι × Fin n) (fun v => π v.1) (XG π LL Cv Cl F) ?h1 ?h2 ?h3 F ?h4
  · exact sum_of_span _ F hsp
  · intro j x hx
    rw [MvPolynomial.mem_supported]
    intro v hv
    obtain ⟨d, hd, hvd⟩ := (MvPolynomial.mem_vars v).mp hv
    obtain ⟨mo, -, rfl⟩ := Finset.mem_image.mp (hx.1 d hd)
    unfold partOf at hvd
    rw [Finsupp.mem_support_iff, Finsupp.filter_apply] at hvd
    by_contra hne
    exact hvd (if_neg hne)
  · intro j
    exact ⟨F.support.image (partOf π j), fun x hx mo hmo => hx.1 mo hmo⟩
  · intro j c x hc hcx
    obtain ⟨a1, a2, a3⟩ := hcx
    refine ⟨fun mo hmo => a1 mo ?_, fun q hq => (a2 q hq).trans (valS_sat LL q.1 c hc x),
      fun q hq => (lowest_weight_le_smul_nonzero LL q.1 c hc x).trans (a3 q hq)⟩
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_smul, smul_eq_mul]
    exact mul_ne_zero hc (MvPolynomial.mem_support_iff.mp hmo)
  · intro j
    obtain ⟨s, cM, hMs, hcM, hF, hsupp, hvals⟩ := hS O ι n LL {i | π i = j} F
    have hmem : ∑ M ∈ s, cM M * monomial M 1 ∈ Submodule.span O
        {y | ∃ x ∈ XG π LL Cv Cl F j, ∃ M ∈ supported O {v : ι × Fin n | π v.1 ≠ j}, y = x * M} := by
      refine Submodule.sum_mem _ fun M hM => Submodule.subset_span ⟨cM M, ?_, monomial M 1, ?_, rfl⟩
      · refine ⟨fun mo hmo => Finset.mem_image.mpr ⟨mo + M, hsupp M hM mo hmo, hpart j mo M ?_ ?_⟩,
          fun q hq => (hv j q hq).trans (hvals M hM q.1 (hCv j q hq)).1,
          fun q hq => (hvals M hM q.1 (hCl j q hq)).2.trans (hl j q hq)⟩
        · intro v hv
          have hvars : v ∈ (cM M).vars := (MvPolynomial.mem_vars v).mpr ⟨mo, hmo, hv⟩
          exact (MvPolynomial.mem_supported.mp (hcM M hM)) hvars
        · intro v hv
          exact hMs M hM v hv
      · rw [MvPolynomial.mem_supported, MvPolynomial.vars_monomial one_ne_zero]
        intro v hv
        exact hMs M hM v hv
    rwa [← hF] at hmem

end Dec

end Formalism.MainNotions.Proposition5Numerics
