import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
open GlobalTheory.CompanionTheory.Ar Matrix

namespace PositivityTheory.UnitarySelfGeneration.GF

variable {r : ℕ}

def trunc {R : Type} [CommRing R] (k : Fin r) (A : Matrix (Fin r) (Fin r) R) : Matrix (Fin r) (Fin r) R :=
  Matrix.of fun i j => if i ≤ k ∧ j ≤ k then A i j else if i = j then 1 else 0

def Uni {R : Type} [CommRing R] (L : Matrix (Fin r) (Fin r) R) : Prop :=
  (∀ k, L k k = 1) ∧ ∀ l k, l < k → L l k = 0

def Up {R : Type} [CommRing R] (C : Matrix (Fin r) (Fin r) R) : Prop := ∀ l k, k < l → C l k = 0

section Ring

variable {R R' : Type} [CommRing R] [CommRing R']

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [trunc, of_apply, map_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem trunc_map (φ : R →+* R') (k : Fin r) (A : Matrix (Fin r) (Fin r) R) :
    trunc k (A.map φ) = (trunc k A).map φ := by
  ext i j
  simp only [trunc, of_apply, map_apply]
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[trunc_map, RingHom.map_det, RingHom.mapMatrix_apply]`.
-/
theorem det_trunc_map (φ : R →+* R') (k : Fin r) (A : Matrix (Fin r) (Fin r) R) :
    (trunc k (A.map φ)).det = φ (trunc k A).det := by
  rw [trunc_map, RingHom.map_det, RingHom.mapMatrix_apply]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun k => by simp [h.1], fun l k hlk => by simp [h.2 l k hlk]⟩`.
-/
theorem Uni.map {L : Matrix (Fin r) (Fin r) R} (h : Uni L) (φ : R →+* R') : Uni (L.map φ) :=
  ⟨fun k => by simp [h.1], fun l k hlk => by simp [h.2 l k hlk]⟩

/- English proof (translation)
Introduce `l k hlk` and use `by simp [h l k hlk]`.
-/
theorem Up.map {L : Matrix (Fin r) (Fin r) R} (h : Up L) (φ : R →+* R') : Up (L.map φ) :=
  fun l k hlk => by simp [h l k hlk]

/- English proof (translation)
Rewrite using `[det_of_isLowerTriangular L (fun i j hij => h.2 i j hij)]`. Simplify using `[h.1]`.
-/
theorem Uni.det {L : Matrix (Fin r) (Fin r) R} (h : Uni L) : L.det = 1 := by
  rw [det_of_isLowerTriangular L (fun i j hij => h.2 i j hij)]
  simp [h.1]

/- English proof (translation)
Use `⟨fun i => ?_, fun i j hij => ?_⟩` and prove the remaining obligations. Simplify using `[GF.trunc, h.1]`. Simplify using `[GF.trunc, h.2 i j hij, hij.ne]`.
-/
theorem Uni.trunc {L : Matrix (Fin r) (Fin r) R} (h : Uni L) (k : Fin r) : Uni (trunc k L) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · simp [GF.trunc, h.1]
  · simp [GF.trunc, h.2 i j hij, hij.ne]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun k => by simp, fun l k h => by simp [h.ne]⟩`.
-/
theorem uni_one : Uni (1 : Matrix (Fin r) (Fin r) R) :=
  ⟨fun k => by simp, fun l k h => by simp [h.ne]⟩

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [trunc, of_apply, mul_apply]`. Distinguish the cases in `hi : i ≤ k`. Distinguish the cases in `hj : j ≤ k`. Simplify using `only [hi, hj, and_self, if_true, true_and, and_true]`.

Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Distinguish the cases in `hl : l ≤ k`. Simplify using `[hl]`. Establish `h1 : j < l` using `lt_of_le_of_lt hj (not_le.1 hl)`. Simplify using `[hl, hC l j h1, h1.ne']`.

Establish `hij : i ≠ j` using `fun e => hj (e ▸ hi)`. Simplify using `only [hi, hj, and_false, if_false, true_and, hij]`. Use `(Finset.sum_eq_zero fun l _ => ?_).symm` and prove the remaining obligations. Distinguish the cases in `hl : l = j`. Substitute `hl` using the available equality.

Simplify using `[hj, hij]`. Simplify using `[hl]`. Simplify using `only [hi, false_and, if_false]`. Rewrite using `[Finset.sum_eq_single i]`. Simplify using `[hi]`.

Introduce `l _ hl`. Simplify using `[Ne.symm hl]`. Simplify using the standard rewrite rules.
-/
theorem trunc_mul (k : Fin r) (A C : Matrix (Fin r) (Fin r) R) (hC : Up C) :
    trunc k (A * C) = trunc k A * trunc k C := by
  ext i j
  simp only [trunc, of_apply, mul_apply]
  by_cases hi : i ≤ k
  · by_cases hj : j ≤ k
    · simp only [hi, hj, and_self, if_true, true_and, and_true]
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases hl : l ≤ k
      · simp [hl]
      · have h1 : j < l := lt_of_le_of_lt hj (not_le.1 hl)
        simp [hl, hC l j h1, h1.ne']
    · have hij : i ≠ j := fun e => hj (e ▸ hi)
      simp only [hi, hj, and_false, if_false, true_and, hij]
      refine (Finset.sum_eq_zero fun l _ => ?_).symm
      by_cases hl : l = j
      · subst hl; simp [hj, hij]
      · simp [hl]
  · simp only [hi, false_and, if_false]
    rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro l _ hl; simp [Ne.symm hl]
    · simp

/- English proof (translation)
Establish `h : BlockTriangular (A * B) id` using `BlockTriangular.mul (fun i j h => hA i j h) (fun i j h => hB i j h)`. Conclude with `fun i j hij => h hij`.
-/
theorem Up.mul {A B : Matrix (Fin r) (Fin r) R} (hA : Up A) (hB : Up B) : Up (A * B) := by
  have h : BlockTriangular (A * B) id :=
    BlockTriangular.mul (fun i j h => hA i j h) (fun i j h => hB i j h)
  exact fun i j hij => h hij

end Ring

variable {F F' : Type} [Field F] [Field F']

/- English proof (translation)
Set `_` to `A.invertibleOfIsUnitDet (IsUnit.mk0 _ h0)`. Establish `h : BlockTriangular A⁻¹ id` using `blockTriangular_inv_of_blockTriangular (fun i j h => hA i j h)`. Conclude with `fun i j hij => h hij`.
-/
theorem Up.inv {A : Matrix (Fin r) (Fin r) F} (hA : Up A) (h0 : A.det ≠ 0) : Up A⁻¹ := by
  let _ := A.invertibleOfIsUnitDet (IsUnit.mk0 _ h0)
  have h : BlockTriangular A⁻¹ id := blockTriangular_inv_of_blockTriangular (fun i j h => hA i j h)
  exact fun i j hij => h hij

/- English proof (translation)
Establish `hx : ∀ k, ∃ x : Fin r → F, trunc k A *ᵥ x = Pi.single k 1` using `fun k => ⟨(trunc k A)⁻¹ *ᵥ Pi.single k 1, by`. Rewrite using `[mulVec_mulVec, mul_nonsing_inv _ (IsUnit.mk0 _ (h k)), one_mulVec]⟩`. Use `choose x hx using hx`. Establish `hup : ∀ l k, k < l → x k l = 0`. Introduce `l k hkl`.

Use `congrFun (hx k) l` as an intermediate fact. Simplify using `only [mulVec, dotProduct, trunc, of_apply, not_le.2 hkl, false_and, if_false] at this`. Rewrite `this` using `[Finset.sum_eq_single l]`. Simplify `this` using `[hkl.ne']`. Introduce `b _ hb`.

Simplify using `[Ne.symm hb]`. Simplify using the standard rewrite rules. Establish `key : ∀ l k, l ≤ k → (A * Matrix.of fun l k => x k l) l k = (Pi.single k 1 : Fin r → F) l`. Introduce `l k hlk`. Rewrite using `[← congrFun (hx k) l]`.

Simplify using `only [mul_apply, mulVec, dotProduct, trunc, of_apply, hlk, true_and]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Distinguish the cases in `hb : b ≤ k`. Simplify using `[hb]`. Simplify using `[hup b k (not_le.1 hb)]`.

Use `⟨Matrix.of fun l k => x k l, hup, fun k => ?_, fun l k hlk => ?_⟩` and prove the remaining obligations. Rewrite using `[key k k le_rfl]`. Simplify using the standard rewrite rules. Rewrite using `[key l k hlk.le]`. Simplify using `[hlk.ne]`.
-/
theorem exists_lu (A : Matrix (Fin r) (Fin r) F) (h : ∀ k, (trunc k A).det ≠ 0) :
    ∃ C, Up C ∧ Uni (A * C) := by
  have hx : ∀ k, ∃ x : Fin r → F, trunc k A *ᵥ x = Pi.single k 1 := fun k =>
    ⟨(trunc k A)⁻¹ *ᵥ Pi.single k 1, by
      rw [mulVec_mulVec, mul_nonsing_inv _ (IsUnit.mk0 _ (h k)), one_mulVec]⟩
  choose x hx using hx
  have hup : ∀ l k, k < l → x k l = 0 := by
    intro l k hkl
    have := congrFun (hx k) l
    simp only [mulVec, dotProduct, trunc, of_apply, not_le.2 hkl, false_and, if_false] at this
    rw [Finset.sum_eq_single l] at this
    · simpa [hkl.ne'] using this
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  have key : ∀ l k, l ≤ k → (A * Matrix.of fun l k => x k l) l k = (Pi.single k 1 : Fin r → F) l := by
    intro l k hlk
    rw [← congrFun (hx k) l]
    simp only [mul_apply, mulVec, dotProduct, trunc, of_apply, hlk, true_and]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : b ≤ k
    · simp [hb]
    · simp [hup b k (not_le.1 hb)]
  refine ⟨Matrix.of fun l k => x k l, hup, fun k => ?_, fun l k hlk => ?_⟩
  · rw [key k k le_rfl]; simp
  · rw [key l k hlk.le]; simp [hlk.ne]

/- English proof (translation)
Establish `h1` using `h.det`. Rewrite `h1` using `[det_mul]`. Use `⟨left_ne_zero_of_mul_eq_one h1, right_ne_zero_of_mul_eq_one h1, fun k => ?_⟩` and prove the remaining obligations. Establish `h2` using `(h.trunc k).det`. Rewrite `h2` using `[trunc_mul k A C hC, det_mul]`.

Conclude with `⟨left_ne_zero_of_mul_eq_one h2, right_ne_zero_of_mul_eq_one h2⟩`.
-/
theorem dets_of_lu {A C : Matrix (Fin r) (Fin r) F} (hC : Up C) (h : Uni (A * C)) :
    A.det ≠ 0 ∧ C.det ≠ 0 ∧ ∀ k, (trunc k A).det ≠ 0 ∧ (trunc k C).det ≠ 0 := by
  have h1 := h.det
  rw [det_mul] at h1
  refine ⟨left_ne_zero_of_mul_eq_one h1, right_ne_zero_of_mul_eq_one h1, fun k => ?_⟩
  have h2 := (h.trunc k).det
  rw [trunc_mul k A C hC, det_mul] at h2
  exact ⟨left_ne_zero_of_mul_eq_one h2, right_ne_zero_of_mul_eq_one h2⟩

/- English proof (translation)
Establish `hL0 : L.det ≠ 0` using `by rw [hL.det]; exact one_ne_zero`. Establish `h1 : Up (Lᵀ)` using `fun i j hij => hL.2 j i hij`. Establish `h2 : Up ((L * W)ᵀ)` using `fun i j hij => h.2 j i hij`. Establish `h3 : Up ((L * W)ᵀ * (Lᵀ)⁻¹)` using `h2.mul (h1.inv (by rwa [det_transpose]))`. Rewrite `h3` using `[transpose_mul, Matrix.mul_assoc, mul_nonsing_inv _ (IsUnit.mk0 _ (by rwa [det_transpose])), Matrix.mul_one]`.

Establish `hoff : ∀ i j, i ≠ j → W i j = 0` using `fun i j hij => (lt_or_gt_of_ne hij).elim (fun h => h3 j i h) (fun h => hW i j h)`. Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Use `h.1 i` as an intermediate fact.

Rewrite `this` using `[mul_apply, Finset.sum_eq_single i]`. Simplify `this` using `[hL.1]`. Introduce `b _ hb`. Simplify using `[hoff b i hb]`. Simplify using the standard rewrite rules.

Rewrite using `[hoff i j hij, one_apply_ne hij]`.
-/
theorem uni_mul_up {L W : Matrix (Fin r) (Fin r) F} (hL : Uni L) (hW : Up W) (h : Uni (L * W)) : W = 1 := by
  have hL0 : L.det ≠ 0 := by rw [hL.det]; exact one_ne_zero
  have h1 : Up (Lᵀ) := fun i j hij => hL.2 j i hij
  have h2 : Up ((L * W)ᵀ) := fun i j hij => h.2 j i hij
  have h3 : Up ((L * W)ᵀ * (Lᵀ)⁻¹) := h2.mul (h1.inv (by rwa [det_transpose]))
  rw [transpose_mul, Matrix.mul_assoc, mul_nonsing_inv _ (IsUnit.mk0 _ (by rwa [det_transpose])),
    Matrix.mul_one] at h3
  have hoff : ∀ i j, i ≠ j → W i j = 0 := fun i j hij =>
    (lt_or_gt_of_ne hij).elim (fun h => h3 j i h) (fun h => hW i j h)
  ext i j
  by_cases hij : i = j
  · subst hij
    have := h.1 i
    rw [mul_apply, Finset.sum_eq_single i] at this
    · simpa [hL.1] using this
    · intro b _ hb; simp [hoff b i hb]
    · simp
  · rw [hoff i j hij, one_apply_ne hij]

/- English proof (translation)
Establish `h0` using `(dets_of_lu hC h).2.1`. Establish `e : A * C' = A * C * (C⁻¹ * C')`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc C, mul_nonsing_inv _ (IsUnit.mk0 _ h0), Matrix.one_mul]`. Use `uni_mul_up h ((hC.inv h0).mul hC') (e ▸ h')` as an intermediate fact. Rewrite using `[e, this, Matrix.mul_one]`.
-/
theorem lu_unique {A C C' : Matrix (Fin r) (Fin r) F} (hC : Up C) (h : Uni (A * C)) (hC' : Up C')
    (h' : Uni (A * C')) : A * C = A * C' := by
  have h0 := (dets_of_lu hC h).2.1
  have e : A * C' = A * C * (C⁻¹ * C') := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc C, mul_nonsing_inv _ (IsUnit.mk0 _ h0), Matrix.one_mul]
  have := uni_mul_up h ((hC.inv h0).mul hC') (e ▸ h')
  rw [e, this, Matrix.mul_one]

/- English proof (translation)
Set `A₀ : Matrix (Fin r) (Fin r) K` to `Matrix.of fun i j => ⟨A i j, hA i j⟩`. Establish `e : A₀.map K.subtype = A` using `rfl`. Take `⟨C₀, h1, h2⟩` from `exists_lu A₀ fun k h0 => ((dets_of_lu hC h).2.2 k).1 (by`. Rewrite using `[← e, det_trunc_map, h0, map_zero])`. Establish `h3` using `h2.map K.subtype`.

Establish `e2 : (A₀ * C₀).map K.subtype = A * C₀.map K.subtype` using `by rw [Matrix.map_mul, e]`. Rewrite `h3` using `[e2]`. Rewrite using `[lu_unique hC h (h1.map K.subtype) h3, ← e2]`. Conclude with `fun i j => ((A₀ * C₀) i j).2`.
-/
theorem lu_mem (K : Subfield F) {A C : Matrix (Fin r) (Fin r) F} (hC : Up C) (h : Uni (A * C))
    (hA : ∀ i j, A i j ∈ K) : ∀ i j, (A * C) i j ∈ K := by
  let A₀ : Matrix (Fin r) (Fin r) K := Matrix.of fun i j => ⟨A i j, hA i j⟩
  have e : A₀.map K.subtype = A := rfl
  obtain ⟨C₀, h1, h2⟩ := exists_lu A₀ fun k h0 => ((dets_of_lu hC h).2.2 k).1 (by
    rw [← e, det_trunc_map, h0, map_zero])
  have h3 := h2.map K.subtype
  have e2 : (A₀ * C₀).map K.subtype = A * C₀.map K.subtype := by rw [Matrix.map_mul, e]
  rw [e2] at h3
  rw [lu_unique hC h (h1.map K.subtype) h3, ← e2]
  exact fun i j => ((A₀ * C₀) i j).2

/- English proof (translation)
Set `N : Matrix (Fin r) (Fin r) (Polynomial F)` to `(Polynomial.X : Polynomial F) • 1 + (1 - Polynomial.X : Polynomial F) • (g⁻¹).map Polynomial.C`. Set `φ` to `algebraMap (Polynomial F) (RatFunc F)`. Establish `hφ : Function.Injective φ` using `IsFractionRing.injective _ _`. Establish `e1 : N.map (Polynomial.evalRingHom (1 : F)) = 1`. Use extensionality with `i j`.

Apply the tactic sequence `by_cases h : i = j <;> simp [N, h, one_apply]`. Establish `e0 : (g.map Polynomial.C * N).map (Polynomial.evalRingHom (0 : F)) = 1`. Rewrite using `[Matrix.map_mul, ← mul_nonsing_inv g (IsUnit.mk0 _ hg)]`. Use `congr 1`. Use extensionality with `i j`.

Simplify using the standard rewrite rules. Use extensionality with `i j`. Apply the tactic sequence `by_cases h : i = j <;> simp [N, h, one_apply]`. Establish `nz : ∀ (M : Matrix (Fin r) (Fin r) (Polynomial F)) (a : F), M.map (Polynomial.evalRingHom a) = 1 → ∀ k, (trunc k (M.map φ)).det ≠ 0`. Introduce `M a hM k h0`.

Rewrite `h0` using `[det_trunc_map, map_eq_zero_iff _ hφ]`. Use `det_trunc_map (Polynomial.evalRingHom a) k M` as an intermediate fact. Rewrite `this` using `[hM, h0, map_zero, (uni_one.trunc k).det]`. Conclude with `one_ne_zero this`. Take `⟨C, hC, hU⟩` from `exists_lu (N.map φ) (nz N 1 e1)`.

Use `⟨_, hU, fun k => ?_⟩` and prove the remaining obligations. Establish `e : g.map (algebraMap F (RatFunc F)) * N.map φ = (g.map Polynomial.C * N).map φ`. Rewrite using `[Matrix.map_mul, Matrix.map_map]`. Both sides reduce to the same expression. Rewrite using `[← Matrix.mul_assoc, trunc_mul _ _ _ hC, det_mul, e]`.

Conclude with `mul_ne_zero (nz _ 0 e0 k) ((dets_of_lu hC hU).2.2 k).2`.
-/
theorem exists_general (g : Matrix (Fin r) (Fin r) F) (hg : g.det ≠ 0) :
    ∃ w : Matrix (Fin r) (Fin r) (RatFunc F), Uni w ∧
      ∀ k, (trunc k (g.map (algebraMap F (RatFunc F)) * w)).det ≠ 0 := by
  let N : Matrix (Fin r) (Fin r) (Polynomial F) :=
    (Polynomial.X : Polynomial F) • 1 + (1 - Polynomial.X : Polynomial F) • (g⁻¹).map Polynomial.C
  let φ := algebraMap (Polynomial F) (RatFunc F)
  have hφ : Function.Injective φ := IsFractionRing.injective _ _
  have e1 : N.map (Polynomial.evalRingHom (1 : F)) = 1 := by
    ext i j
    by_cases h : i = j <;> simp [N, h, one_apply]
  have e0 : (g.map Polynomial.C * N).map (Polynomial.evalRingHom (0 : F)) = 1 := by
    rw [Matrix.map_mul, ← mul_nonsing_inv g (IsUnit.mk0 _ hg)]
    congr 1
    · ext i j; simp
    · ext i j
      by_cases h : i = j <;> simp [N, h, one_apply]
  have nz : ∀ (M : Matrix (Fin r) (Fin r) (Polynomial F)) (a : F), M.map (Polynomial.evalRingHom a) = 1 →
      ∀ k, (trunc k (M.map φ)).det ≠ 0 := by
    intro M a hM k h0
    rw [det_trunc_map, map_eq_zero_iff _ hφ] at h0
    have := det_trunc_map (Polynomial.evalRingHom a) k M
    rw [hM, h0, map_zero, (uni_one.trunc k).det] at this
    exact one_ne_zero this
  obtain ⟨C, hC, hU⟩ := exists_lu (N.map φ) (nz N 1 e1)
  refine ⟨_, hU, fun k => ?_⟩
  have e : g.map (algebraMap F (RatFunc F)) * N.map φ = (g.map Polynomial.C * N).map φ := by
    rw [Matrix.map_mul, Matrix.map_map]
    rfl
  rw [← Matrix.mul_assoc, trunc_mul _ _ _ hC, det_mul, e]
  exact mul_ne_zero (nz _ 0 e0 k) ((dets_of_lu hC hU).2.2 k).2

def fl (M : Matrix (Fin r) (Fin r) F) (i : ℕ) : Submodule F (Fin r → F) := flagStep F (fun k l => M l k) i

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨k, hk, rfl⟩`. Establish `: (fun l => (M * C) l k) = ∑ b, C b k • fun l => M l b`. Use function extensionality and compare the values at `l`. Simplify using `[mul_apply, Finset.sum_apply, mul_comm]`.

Simplify using `only [this]`. Use `Submodule.sum_mem _ fun b _ => ?_` and prove the remaining obligations. Distinguish the cases in `hb : k < b`. Rewrite using `[hC b k hb, zero_smul]`. Conclude with `Submodule.zero_mem _`.

Use `Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, ?_, rfl⟩)` and prove the remaining obligations. Conclude with `lt_of_le_of_lt (Fin.le_def.1 (not_lt.1 hb)) hk`.
-/
theorem fl_mul_le (M C : Matrix (Fin r) (Fin r) F) (hC : Up C) (i : ℕ) : fl (M * C) i ≤ fl M i := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨k, hk, rfl⟩
  have : (fun l => (M * C) l k) = ∑ b, C b k • fun l => M l b := by
    funext l
    simp [mul_apply, Finset.sum_apply, mul_comm]
  simp only [this]
  refine Submodule.sum_mem _ fun b _ => ?_
  by_cases hb : k < b
  · rw [hC b k hb, zero_smul]; exact Submodule.zero_mem _
  · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, ?_, rfl⟩)
    exact lt_of_le_of_lt (Fin.le_def.1 (not_lt.1 hb)) hk

/- English proof (translation)
Use `le_antisymm (fl_mul_le M C hC i) ?_` and prove the remaining obligations. Use `fl_mul_le (M * C) C⁻¹ (hC.inv h0) i` as an intermediate fact. Rewrite `this` using `[Matrix.mul_assoc, mul_nonsing_inv _ (IsUnit.mk0 _ h0), Matrix.mul_one]`. Then use the resulting hypothesis.
-/
theorem fl_mul (M C : Matrix (Fin r) (Fin r) F) (hC : Up C) (h0 : C.det ≠ 0) (i : ℕ) : fl (M * C) i = fl M i := by
  refine le_antisymm (fl_mul_le M C hC i) ?_
  have := fl_mul_le (M * C) C⁻¹ (hC.inv h0) i
  rwa [Matrix.mul_assoc, mul_nonsing_inv _ (IsUnit.mk0 _ h0), Matrix.mul_one] at this

/- English proof (translation)
Unfold `flagStep`. Rewrite using `[Submodule.map_span, Set.image_image]`.
-/
theorem flagStep_map {E E' : Type} [AddCommGroup E] [Module F E] [AddCommGroup E'] [Module F E'] (f : E →ₗ[F] E')
    (b : Fin r → E) (i : ℕ) : (flagStep F b i).map f = flagStep F (fun k => f (b k)) i := by
  unfold flagStep
  rw [Submodule.map_span, Set.image_image]

/- English proof (translation)
Apply `Submodule.map_injective_of_injective (f := Fintype.linearCombination F e) (he.fintypeLinearCombination_injective)` to reduce the goal to its premises. Unfold `fl`. Rewrite using `[flagStep_map, flagStep_map]`. Simplify `h` using `only [Fintype.linearCombination_apply]`.
-/
theorem fl_of_indep {E : Type} [AddCommGroup E] [Module F E] {e : Fin r → E} (he : LinearIndependent F e)
    {M N : Matrix (Fin r) (Fin r) F} {i : ℕ}
    (h : flagStep F (fun k => ∑ l, M l k • e l) i = flagStep F (fun k => ∑ l, N l k • e l) i) : fl M i = fl N i := by
  apply Submodule.map_injective_of_injective (f := Fintype.linearCombination F e)
    (he.fintypeLinearCombination_injective)
  unfold fl
  rw [flagStep_map, flagStep_map]
  simpa only [Fintype.linearCombination_apply] using h

end PositivityTheory.UnitarySelfGeneration.GF
