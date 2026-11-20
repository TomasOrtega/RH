import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.SumIndicesEqSumColumns

noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ}

def ql_be (b : ℕ) (L : LamIdx n b) : Fin n → ℤ := ∑ x ∈ L.1, Pi.single x (1 : ℤ)

/- English proof (translation)
Simplify using `[ql_be, Finset.sum_apply, Pi.single_apply]`.
-/
lemma ql_be_apply (b : ℕ) (L : LamIdx n b) (a : Fin n) : ql_be b L a = if a ∈ L.1 then 1 else 0 := by
  simp [ql_be, Finset.sum_apply, Pi.single_apply]

/- English proof (translation)
Introduce `L L' h`. Apply `Subtype.ext` to reduce the goal to its premises. Use extensionality with `a`. Use `congrFun h a` as an intermediate fact. Rewrite `this` using `[ql_be_apply, ql_be_apply]`.

Apply the tactic sequence `by_cases h1 : a ∈ L.1 <;> by_cases h2 : a ∈ L'.1 <;> simp_all`.
-/
lemma ql_be_inj (b : ℕ) : Function.Injective (ql_be (n := n) b) := by
  intro L L' h
  apply Subtype.ext
  ext a
  have := congrFun h a
  rw [ql_be_apply, ql_be_apply] at this
  by_cases h1 : a ∈ L.1 <;> by_cases h2 : a ∈ L'.1 <;> simp_all

/- English proof (translation)
Rewrite using `[LamMat, qb_evGL_minorC]`. Express the relevant statement in the definitionally equal form `Matrix.det (Matrix.of fun a b => Matrix.diagonal _ _ _) = _`. Rewrite using `[qb_minor_diagonal, qb_prod_single]`. Simplify using `only [Subtype.ext_iff, ql_be]`.
-/
lemma ql_torus (b : ℕ) (k l : LamIdx n b) :
    evGL (torusPt n) (LamMat n b k l) = if k = l then AddMonoidAlgebra.single (ql_be b k) 1 else 0 := by
  rw [LamMat, qb_evGL_minorC]
  change Matrix.det (Matrix.of fun a b => Matrix.diagonal _ _ _) = _
  rw [qb_minor_diagonal, qb_prod_single]
  simp only [Subtype.ext_iff, ql_be]

variable [NeZero n]

def ql_ps (b : ℕ) (mu nu : Fin n → ℤ) : Matrix (TIdx mu × LamIdx n b) (TIdx nu) ℤ :=
  fun y I => ql_P ℤ (ql_E (mu (lastIdx n)) (nu 0 - mu (lastIdx n)).toNat (qs_ext mu y.1)) y.2.1
    (ql_E (mu (lastIdx n)) (nu 0 - mu (lastIdx n)).toNat (qs_ext nu I))

/- English proof (translation)
Simplify `h` using `only [strVert, mem_filter, Fintype.mem_piFinset, mem_Icc]`.
-/
lemma ql_mem_strVert {mu nu : Fin n → ℤ} {b : ℕ} (h : nu ∈ strVert mu b) :
    (∀ a, mu a ≤ nu a ∧ nu a ≤ mu a + 1) ∧ Dominant nu ∧ ∑ a, (nu a - mu a) = (b : ℤ) := by
  simpa only [strVert, mem_filter, Fintype.mem_piFinset, mem_Icc] using h

/- English proof (translation)
Use `set d : GLCoord ℤ n := ((detU n ^ lo : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) with hd`. Use `set k := ql_E lo N (qs_ext mu K) with hk`. Use `set i := ql_E lo N (qs_ext nu I) with hi`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Fintype.sum_prod_type]`.

Use `sum_congr rfl fun K' _ => sum_congr rfl fun L' _ => ?_` and prove the remaining obligations. Rewrite using `[ql_TMat hmu m1 m2, LamMat, qs_minorC_eq, ql_P_cast]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = ∑ k' : Fin N → Finset (Fin n), ∑ L' : LamIdx n b, d * ((∏ j, qs_mn (qs_gC n) (k j) (k' j)) * qs_mn (qs_gC n) L.1 L'.1 * ql_P (GLCoord ℤ n) k' L'.1 i) := by`. Use `sum_indices_eq_sum_columns hmu m1 m2 (fun k' => ∑ L' : LamIdx n b, d * ((∏ j, qs_mn (qs_gC n) (k j) (k' j)) * qs_mn (qs_gC n) L.1 L'.1 * ql_P (GLCoord ℤ n) k' L'.1 i)) ?_` and prove the remaining obligations.

Introduce and unpack `f ⟨j, hj⟩`. Use `sum_eq_zero fun L' _ => ?_` and prove the remaining obligations. Rewrite using `[prod_eq_zero (mem_univ j) (qs_mn_ne _ (by rw [hk, ql_E_card hmu]; exact hj.symm))]; ring`. Use `_ = ∑ k' : Fin N → Finset (Fin n), ∑ L' : Finset (Fin n), d * ((∏ j, qs_mn (qs_gC n) (k j) (k' j)) * qs_mn (qs_gC n) L.1 L' * ql_P (GLCoord ℤ n) k' L' i) := by`. Use `sum_congr rfl fun k' _ => ql_sum_L (b := b) (fun L' => d * ((∏ j, qs_mn (qs_gC n) (k j) (k' j)) * qs_mn (qs_gC n) L.1 L' * ql_P (GLCoord ℤ n) k' L' i)) ?_` and prove the remaining obligations.

Introduce `L' hL'`. Use `show d * (_ * qs_mn (qs_gC n) L.1 L' * _) = 0`. Rewrite using `[qs_mn_ne _ (by rw [L.2]; exact hL'.symm)]; ring`. Use `_ = ∑ i' : Fin N → Finset (Fin n), d * (ql_P (GLCoord ℤ n) k L.1 i' * ∏ j, qs_mn (qs_gC n) (i' j) (i j)) := by`. Rewrite using `[← mul_sum, ← ql_P_equiv]`.

Simplify using `only [mul_sum]`. Use `_ = ∑ I' : TIdx nu, d * (ql_P (GLCoord ℤ n) k L.1 (ql_E lo N (qs_ext nu I')) * ∏ j, qs_mn (qs_gC n) (ql_E lo N (qs_ext nu I') j) (i j)) := by`. Use `symm`. Use `sum_indices_eq_sum_columns hnu n1 n2 (fun i' => d * (ql_P (GLCoord ℤ n) k L.1 i' * ∏ j, qs_mn (qs_gC n) (i' j) (i j))) ?_` and prove the remaining obligations. Introduce and unpack `f ⟨j, hj⟩`.

Use `show d * (_ * ∏ j, qs_mn (qs_gC n) (f j) (i j)) = 0`. Rewrite using `[prod_eq_zero (mem_univ j) (qs_mn_ne _ (by rw [hi, ql_E_card hnu]; exact hj))]; ring`. Use `_ = ∑ I' : TIdx nu, ((ql_P ℤ k L.1 (ql_E lo N (qs_ext nu I')) : ℤ) : GLCoord ℤ n) * TMat nu I' I := by`. Use `sum_congr rfl fun I' _ => ?_` and prove the remaining obligations. Rewrite using `[ql_TMat hnu n1 n2, ql_P_cast]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem ql_core (b : ℕ) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : Dominant nu) {lo : ℤ} {N : ℕ}
    (m1 : lo ≤ mu (lastIdx n)) (m2 : mu 0 ≤ lo + N) (n1 : lo ≤ nu (lastIdx n)) (n2 : nu 0 ≤ lo + N)
    (K : TIdx mu) (L : LamIdx n b) (I : TIdx nu) :
    ∑ y : TIdx mu × LamIdx n b, (TMat mu K y.1 * LamMat n b L y.2) *
        ((ql_P ℤ (ql_E lo N (qs_ext mu y.1)) y.2.1 (ql_E lo N (qs_ext nu I)) : ℤ) : GLCoord ℤ n) =
      ∑ I' : TIdx nu, ((ql_P ℤ (ql_E lo N (qs_ext mu K)) L.1 (ql_E lo N (qs_ext nu I')) : ℤ) : GLCoord ℤ n) *
        TMat nu I' I := by
  set d : GLCoord ℤ n := ((detU n ^ lo : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) with hd
  set k := ql_E lo N (qs_ext mu K) with hk
  set i := ql_E lo N (qs_ext nu I) with hi
  calc ∑ y : TIdx mu × LamIdx n b, (TMat mu K y.1 * LamMat n b L y.2) *
        ((ql_P ℤ (ql_E lo N (qs_ext mu y.1)) y.2.1 i : ℤ) : GLCoord ℤ n)
      = ∑ K' : TIdx mu, ∑ L' : LamIdx n b, d * ((∏ j, qs_mn (qs_gC n) (k j) (ql_E lo N (qs_ext mu K') j)) *
          qs_mn (qs_gC n) L.1 L'.1 * ql_P (GLCoord ℤ n) (ql_E lo N (qs_ext mu K')) L'.1 i) := by
        rw [Fintype.sum_prod_type]
        refine sum_congr rfl fun K' _ => sum_congr rfl fun L' _ => ?_
        rw [ql_TMat hmu m1 m2, LamMat, qs_minorC_eq, ql_P_cast]; ring
    _ = ∑ k' : Fin N → Finset (Fin n), ∑ L' : LamIdx n b, d * ((∏ j, qs_mn (qs_gC n) (k j) (k' j)) *
          qs_mn (qs_gC n) L.1 L'.1 * ql_P (GLCoord ℤ n) k' L'.1 i) := by
        refine sum_indices_eq_sum_columns hmu m1 m2 (fun k' => ∑ L' : LamIdx n b, d * ((∏ j, qs_mn (qs_gC n) (k j) (k' j)) *
          qs_mn (qs_gC n) L.1 L'.1 * ql_P (GLCoord ℤ n) k' L'.1 i)) ?_
        rintro f ⟨j, hj⟩
        refine sum_eq_zero fun L' _ => ?_
        rw [prod_eq_zero (mem_univ j) (qs_mn_ne _ (by rw [hk, ql_E_card hmu]; exact hj.symm))]; ring
    _ = ∑ k' : Fin N → Finset (Fin n), ∑ L' : Finset (Fin n), d * ((∏ j, qs_mn (qs_gC n) (k j) (k' j)) *
          qs_mn (qs_gC n) L.1 L' * ql_P (GLCoord ℤ n) k' L' i) := by
        refine sum_congr rfl fun k' _ => ql_sum_L (b := b) (fun L' => d * ((∏ j, qs_mn (qs_gC n) (k j) (k' j)) *
          qs_mn (qs_gC n) L.1 L' * ql_P (GLCoord ℤ n) k' L' i)) ?_
        intro L' hL'
        show d * (_ * qs_mn (qs_gC n) L.1 L' * _) = 0
        rw [qs_mn_ne _ (by rw [L.2]; exact hL'.symm)]; ring
    _ = ∑ i' : Fin N → Finset (Fin n), d * (ql_P (GLCoord ℤ n) k L.1 i' * ∏ j, qs_mn (qs_gC n) (i' j) (i j)) := by
        rw [← mul_sum, ← ql_P_equiv]; simp only [mul_sum]
    _ = ∑ I' : TIdx nu, d * (ql_P (GLCoord ℤ n) k L.1 (ql_E lo N (qs_ext nu I')) *
          ∏ j, qs_mn (qs_gC n) (ql_E lo N (qs_ext nu I') j) (i j)) := by
        symm
        refine sum_indices_eq_sum_columns hnu n1 n2 (fun i' => d * (ql_P (GLCoord ℤ n) k L.1 i' *
          ∏ j, qs_mn (qs_gC n) (i' j) (i j))) ?_
        rintro f ⟨j, hj⟩
        show d * (_ * ∏ j, qs_mn (qs_gC n) (f j) (i j)) = 0
        rw [prod_eq_zero (mem_univ j) (qs_mn_ne _ (by rw [hi, ql_E_card hnu]; exact hj))]; ring
    _ = ∑ I' : TIdx nu, ((ql_P ℤ k L.1 (ql_E lo N (qs_ext nu I')) : ℤ) : GLCoord ℤ n) * TMat nu I' I := by
        refine sum_congr rfl fun I' _ => ?_
        rw [ql_TMat hnu n1 n2, ql_P_cast]; ring

/- English proof (translation)
Establish `h0 : mu (lastIdx n) ≤ mu 0` using `hmu (Fin.zero_le _)`. Use `((ql_mem_strVert h).1 0).1` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
lemma ql_range {mu nu : Fin n → ℤ} {b : ℕ} (hmu : Dominant mu) (h : nu ∈ strVert mu b) :
    mu (lastIdx n) + ((nu 0 - mu (lastIdx n)).toNat : ℕ) = nu 0 := by
  have h0 : mu (lastIdx n) ≤ mu 0 := hmu (Fin.zero_le _)
  have := ((ql_mem_strVert h).1 0).1
  omega

/- English proof (translation)
Take `⟨hb, hnu, -⟩` from `ql_mem_strVert h`. Establish `hN` using `ql_range hmu h`. Conclude with `ql_core b hmu hnu le_rfl (by rw [hN]; exact (hb 0).1) (hb _).1 hN.ge K L I`.
-/
theorem ql_ps_equiv (b : ℕ) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (h : nu ∈ strVert mu b)
    (K : TIdx mu) (L : LamIdx n b) (I : TIdx nu) :
    ∑ y : TIdx mu × LamIdx n b, (TMat mu K y.1 * LamMat n b L y.2) * ((ql_ps b mu nu y I : ℤ) : GLCoord ℤ n) =
      ∑ I' : TIdx nu, ((ql_ps b mu nu (K, L) I' : ℤ) : GLCoord ℤ n) * TMat nu I' I := by
  obtain ⟨hb, hnu, -⟩ := ql_mem_strVert h
  have hN := ql_range hmu h
  exact ql_core b hmu hnu le_rfl (by rw [hN]; exact (hb 0).1) (hb _).1 hN.ge K L I

/- English proof (translation)
Take `⟨hb, hnu, hs⟩` from `ql_mem_strVert h`. Establish `hN` using `ql_range hmu h`. Use `set lo := mu (lastIdx n) with hlo`. Use `set N := (nu 0 - lo).toNat with hNdef`. Use `set k := ql_E lo N (qs_ext mu (canT mu)) with hk`.

Use `set i := ql_E lo N (qs_ext nu (canT nu)) with hi`. Establish `hmk : ∀ (j : Fin N) a, a ∈ k j ↔ lo + 1 + (j : ℕ) ≤ mu a` using `fun j a => ql_mem_can hmu _ a`. Establish `hmi : ∀ (j : Fin N) a, a ∈ i j ↔ lo + 1 + (j : ℕ) ≤ nu a` using `fun j a => ql_mem_can hnu _ a`. Establish `hU : ∀ a, a ∈ ql_U N (fun j => i j \ k j) ↔ mu a < nu a`. Introduce `a`.

Rewrite using `[ql_mem_U]`. Simplify using `only [mem_sdiff, hmk, hmi]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨j, h1, h2⟩`. Use linear arithmetic over natural numbers and integers.

Introduce `hlt`. Establish `h1 : lo ≤ mu a` using `hmu (qb_le_lastIdx a)`. Establish `h2 : nu a ≤ nu 0` using `hnu (Fin.zero_le a)`. Use `⟨⟨(nu a - lo - 1).toNat, by omega⟩, ?_, ?_⟩` and prove the remaining obligations. Use `show lo + 1 + ((nu a - lo - 1).toNat : ℤ) ≤ nu a`.

Use linear arithmetic over natural numbers and integers. Use `show ¬ lo + 1 + ((nu a - lo - 1).toNat : ℤ) ≤ mu a`. Use linear arithmetic over natural numbers and integers. Establish `hind : ∀ a, (if a ∈ ql_U N (fun j => i j \ k j) then (1 : ℤ) else 0) = nu a - mu a`. Introduce `a`.

Use `hb a` as an intermediate fact. Use `split_ifs with h1`. Rewrite `h1` using `[hU]`. Use linear arithmetic over natural numbers and integers. Rewrite `h1` using `[hU]`.

Use linear arithmetic over natural numbers and integers. Establish `hcard : (ql_U N (fun j => i j \ k j)).card = b`. Establish `: ((ql_U N (fun j => i j \ k j)).card : ℤ) = b`. Rewrite using `[← hs, ← sum_congr rfl fun a _ => hind a, Finset.sum_boole, filter_mem_eq_inter, univ_inter]`. Conclude with `this` after adjusting the coercions.

Use `⟨⟨_, hcard⟩, ?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `a`. Rewrite using `[ql_be_apply, Pi.sub_apply]`. Conclude with `hind a`. Use `Int.isUnit_iff.1 (ql_P_unit k i ?_ ?_)` and prove the remaining obligations.

Introduce `j a ha`. Rewrite `ha` using `[hmk]`. Rewrite using `[hmi]`. Conclude with `ha.trans (hb a).1`. Introduce `j j' hjj`.

Rewrite using `[Finset.disjoint_left]`. Introduce `a h1 h2`. Simplify using `only [mem_sdiff, hmk, hmi] at h1 h2`. Use `hb a` as an intermediate fact. Apply `hjj` to reduce the goal to its premises.

Use `ext`. Use linear arithmetic over natural numbers and integers.
-/
theorem ql_lead (b : ℕ) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (h : nu ∈ strVert mu b) :
    ∃ k0 : LamIdx n b, ql_be b k0 = nu - mu ∧
      (ql_ps b mu nu (canT mu, k0) (canT nu) = 1 ∨ ql_ps b mu nu (canT mu, k0) (canT nu) = -1) := by
  obtain ⟨hb, hnu, hs⟩ := ql_mem_strVert h
  have hN := ql_range hmu h
  set lo := mu (lastIdx n) with hlo
  set N := (nu 0 - lo).toNat with hNdef
  set k := ql_E lo N (qs_ext mu (canT mu)) with hk
  set i := ql_E lo N (qs_ext nu (canT nu)) with hi
  have hmk : ∀ (j : Fin N) a, a ∈ k j ↔ lo + 1 + (j : ℕ) ≤ mu a := fun j a => ql_mem_can hmu _ a
  have hmi : ∀ (j : Fin N) a, a ∈ i j ↔ lo + 1 + (j : ℕ) ≤ nu a := fun j a => ql_mem_can hnu _ a
  have hU : ∀ a, a ∈ ql_U N (fun j => i j \ k j) ↔ mu a < nu a := by
    intro a
    rw [ql_mem_U]
    simp only [mem_sdiff, hmk, hmi]
    constructor
    · rintro ⟨j, h1, h2⟩; omega
    · intro hlt
      have h1 : lo ≤ mu a := hmu (qb_le_lastIdx a)
      have h2 : nu a ≤ nu 0 := hnu (Fin.zero_le a)
      refine ⟨⟨(nu a - lo - 1).toNat, by omega⟩, ?_, ?_⟩
      · show lo + 1 + ((nu a - lo - 1).toNat : ℤ) ≤ nu a; omega
      · show ¬ lo + 1 + ((nu a - lo - 1).toNat : ℤ) ≤ mu a; omega
  have hind : ∀ a, (if a ∈ ql_U N (fun j => i j \ k j) then (1 : ℤ) else 0) = nu a - mu a := by
    intro a
    have := hb a
    split_ifs with h1
    · rw [hU] at h1; omega
    · rw [hU] at h1; omega
  have hcard : (ql_U N (fun j => i j \ k j)).card = b := by
    have : ((ql_U N (fun j => i j \ k j)).card : ℤ) = b := by
      rw [← hs, ← sum_congr rfl fun a _ => hind a, Finset.sum_boole, filter_mem_eq_inter, univ_inter]
    exact_mod_cast this
  refine ⟨⟨_, hcard⟩, ?_, ?_⟩
  · funext a
    rw [ql_be_apply, Pi.sub_apply]
    exact hind a
  · refine Int.isUnit_iff.1 (ql_P_unit k i ?_ ?_)
    · intro j a ha
      rw [hmk] at ha; rw [hmi]; exact ha.trans (hb a).1
    · intro j j' hjj
      rw [Finset.disjoint_left]
      intro a h1 h2
      simp only [mem_sdiff, hmk, hmi] at h1 h2
      have := hb a
      apply hjj; ext; omega

/- English proof (translation)
Introduce `n _ b`. Use `⟨ql_be b, ql_ps b, ql_be_inj b, ql_torus b, fun mu _ nu h => (ql_mem_strVert h).2.1, ?_, fun mu hmu nu h => ql_lead b hmu h, fun mu hmu => hc n mu b hmu⟩` and prove the remaining obligations. Introduce `mu hmu nu h`. Use extensionality with `⟨K, L⟩ I`. Conclude with `ql_ps_equiv b hmu h K L I`.
-/
theorem lamStrip_of (hc : CntLam) : LamStrip := by
  intro n _ b
  refine ⟨ql_be b, ql_ps b, ql_be_inj b, ql_torus b, fun mu _ nu h => (ql_mem_strVert h).2.1, ?_,
    fun mu hmu nu h => ql_lead b hmu h, fun mu hmu => hc n mu b hmu⟩
  intro mu hmu nu h
  ext ⟨K, L⟩ I
  exact ql_ps_equiv b hmu h K L I

end Formalism.InvariantFactorPaths.ColumnFamilies
