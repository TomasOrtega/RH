import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.DepFrame

variable {E : Type} [Field E] {n ρ : ℕ}

def FirstRel (x : Matrix (Fin n) (Fin ρ) E) (j : Fin ρ) : Prop :=
  (∀ a : Fin ρ → E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧
    ∃ a : Fin ρ → E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0

/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Break down `lt_or_ge k i with h | h` into its components or cases. Simplify using `[hu i k h]`. Simplify using `[ha k h]`.
-/
theorem mulVec_apply_eq_zero_of_upper {u : Matrix (Fin ρ) (Fin ρ) E}
    (hu : ∀ i k, k < i → u i k = 0) {a : Fin ρ → E} {i : Fin ρ}
    (ha : ∀ k, i ≤ k → a k = 0) : (u *ᵥ a) i = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge k i with h | h
  · simp [hu i k h]
  · simp [ha k h]

/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct]`. Rewrite using `[Finset.sum_eq_single j]`. Simplify using `[hd]`. Introduce `k _ hk`. Break down `lt_or_gt_of_ne hk with h | h` into its components or cases.

Simplify using `[hu j k h]`. Simplify using `[ha k h]`. Simplify using the standard rewrite rules.
-/
theorem mulVec_apply_eq_of_upper {u : Matrix (Fin ρ) (Fin ρ) E}
    (hu : ∀ i k, k < i → u i k = 0) (hd : ∀ i, u i i = 1) {a : Fin ρ → E} {j : Fin ρ}
    (ha : ∀ i, j < i → a i = 0) : (u *ᵥ a) j = a j := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single j]
  · simp [hd]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · simp [hu j k h]
    · simp [ha k h]
  · simp

/- English proof (translation)
Use extensionality with `r`. Simplify using `[Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]`.
-/
theorem sum_smul_transpose (x : Matrix (Fin n) (Fin ρ) E) (a : Fin ρ → E) :
    ∑ i, a i • x.transpose i = x *ᵥ a := by
  ext r
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

/- English proof (translation)
Establish `key : LinearIndependent E xᵀ ↔ ∀ g : Fin ρ → E, x *ᵥ g = 0 → ∀ i, g i = 0`. Use `(Fintype.linearIndependent_iff (R := E) (v := (fun i => xᵀ i : Fin ρ → Fin n → E))).trans ?_` and prove the remaining obligations. Simplify using `only [sum_smul_transpose]`. Rewrite using `[key]`. Prove the components needed by the constructor for the conclusion.

Introduce `h push_neg at h`. Take `⟨g, hg, i₀, hi₀⟩` from `h`. Set `S : Finset (Fin ρ)` to `Finset.univ.filter fun j => ∃ a : Fin ρ → E, a j ≠ 0 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0`. Establish `hlast : ∀ b : Fin ρ → E, x *ᵥ b = 0 → ∀ i, b i ≠ 0 → ∃ k ∈ S, b k ≠ 0`. Introduce `b hb i hi`.

Set `T : Finset (Fin ρ)` to `Finset.univ.filter fun k => b k ≠ 0`. Establish `hT : T.Nonempty` using `⟨i, by simp [T, hi]⟩`. Establish `hk : T.max' hT ∈ T` using `Finset.max'_mem T hT`. Establish `hbk : b (T.max' hT) ≠ 0` using `by simpa [T] using hk`. Use `⟨T.max' hT, ?_, hbk⟩` and prove the remaining obligations.

Simplify using `only [S, Finset.mem_filter, Finset.mem_univ, true_and]`. Use `⟨b, hbk, fun l hl => ?_, hb⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Establish `: l ≤ T.max' hT` using `T.le_max' l (by simp [T, hne])`. Conclude with `absurd hl (not_lt.mpr this)`.

Take `⟨k, hkS, -⟩` from `hlast g hg i₀ hi₀`. Establish `hS : S.Nonempty` using `⟨k, hkS⟩`. Establish `hjS : S.min' hS ∈ S` using `Finset.min'_mem S hS`. Simplify using `only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hjS`. Take `⟨a, haj, hagt, hax⟩` from `hjS`.

Use `⟨S.min' hS, ?_, ?_⟩` and prove the remaining obligations. Introduce `b hb hbx`. Assume the negation of the conclusion as `hne`. Take `⟨i, hi⟩` from `Function.ne_iff.mp hne`. Take `⟨k, hkS, hbk⟩` from `hlast b hbx i hi`.

Establish `hkj : k < S.min' hS`. Assume the negation of the conclusion as `h`. Conclude with `hbk (hb k (not_lt.mp h))`. Conclude with `absurd (S.min'_le k hkS) (not_le.mpr hkj)`. Use `⟨(a (S.min' hS))⁻¹ • a, by simp only [Pi.smul_apply, smul_eq_mul]; exact inv_mul_cancel₀ haj, fun i hi => by simp [hagt i hi], ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.mulVec_smul, hax, smul_zero]`. Introduce and unpack `⟨j, -, a, haj, -, hax⟩ h`. Use `h a hax j` as an intermediate fact. Rewrite `this` using `[haj]`. Conclude with `one_ne_zero this`.
-/
theorem not_linearIndependent_iff_exists (x : Matrix (Fin n) (Fin ρ) E) :
    ¬ LinearIndependent E x.transpose ↔ ∃ j, FirstRel x j := by
  classical
  have key : LinearIndependent E xᵀ ↔ ∀ g : Fin ρ → E, x *ᵥ g = 0 → ∀ i, g i = 0 := by
    refine (Fintype.linearIndependent_iff (R := E)
      (v := (fun i => xᵀ i : Fin ρ → Fin n → E))).trans ?_
    simp only [sum_smul_transpose]
  rw [key]
  constructor
  · intro h
    push_neg at h
    obtain ⟨g, hg, i₀, hi₀⟩ := h
    let S : Finset (Fin ρ) := Finset.univ.filter fun j =>
      ∃ a : Fin ρ → E, a j ≠ 0 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0
    have hlast : ∀ b : Fin ρ → E, x *ᵥ b = 0 → ∀ i, b i ≠ 0 → ∃ k ∈ S, b k ≠ 0 := by
      intro b hb i hi
      let T : Finset (Fin ρ) := Finset.univ.filter fun k => b k ≠ 0
      have hT : T.Nonempty := ⟨i, by simp [T, hi]⟩
      have hk : T.max' hT ∈ T := Finset.max'_mem T hT
      have hbk : b (T.max' hT) ≠ 0 := by simpa [T] using hk
      refine ⟨T.max' hT, ?_, hbk⟩
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨b, hbk, fun l hl => ?_, hb⟩
      by_contra hne
      have : l ≤ T.max' hT := T.le_max' l (by simp [T, hne])
      exact absurd hl (not_lt.mpr this)
    obtain ⟨k, hkS, -⟩ := hlast g hg i₀ hi₀
    have hS : S.Nonempty := ⟨k, hkS⟩
    have hjS : S.min' hS ∈ S := Finset.min'_mem S hS
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hjS
    obtain ⟨a, haj, hagt, hax⟩ := hjS
    refine ⟨S.min' hS, ?_, ?_⟩
    · intro b hb hbx
      by_contra hne
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
      obtain ⟨k, hkS, hbk⟩ := hlast b hbx i hi
      have hkj : k < S.min' hS := by
        by_contra h
        exact hbk (hb k (not_lt.mp h))
      exact absurd (S.min'_le k hkS) (not_le.mpr hkj)
    · refine ⟨(a (S.min' hS))⁻¹ • a, by simp only [Pi.smul_apply, smul_eq_mul]; exact inv_mul_cancel₀ haj, fun i hi => by simp [hagt i hi], ?_⟩
      rw [Matrix.mulVec_smul, hax, smul_zero]
  · rintro ⟨j, -, a, haj, -, hax⟩ h
    have := h a hax j
    rw [haj] at this
    exact one_ne_zero this

/- English proof (translation)
Establish `key : ∀ {j j' : Fin ρ}, FirstRel x j → FirstRel x j' → ¬ j < j'`. Introduce and unpack `j j' ⟨-, a, haj, hagt, hax⟩ ⟨h1, -⟩ hlt`. Establish `h0` using `h1 a (fun i hi => hagt i (lt_of_lt_of_le hlt hi)) hax`. Simplify using `[h0] at haj`. Break down `lt_trichotomy j j' with hl | he | hg` into its components or cases.

Conclude with `absurd hl (key h h')`. Conclude with `he`. Conclude with `absurd hg (key h' h)`.
-/
theorem firstRel_unique (x : Matrix (Fin n) (Fin ρ) E) {j j' : Fin ρ}
    (h : FirstRel x j) (h' : FirstRel x j') : j = j' := by
  have key : ∀ {j j' : Fin ρ}, FirstRel x j → FirstRel x j' → ¬ j < j' := by
    rintro j j' ⟨-, a, haj, hagt, hax⟩ ⟨h1, -⟩ hlt
    have h0 := h1 a (fun i hi => hagt i (lt_of_lt_of_le hlt hi)) hax
    simp [h0] at haj
  rcases lt_trichotomy j j' with hl | he | hg
  · exact absurd hl (key h h')
  · exact he
  · exact absurd hg (key h' h)

/- English proof (translation)
Take `⟨h1, a, haj, hagt, hax⟩` from `h`. Establish `hmv : ∀ b, (x * u) *ᵥ b = x *ᵥ (u *ᵥ b)` using `fun b => (Matrix.mulVec_mulVec b x u).symm`. Use `⟨fun b hb hbx => ?_, v *ᵥ a, ?_, fun i hi => ?_, ?_⟩` and prove the remaining obligations. Establish `hub : u *ᵥ b = 0` using `h1 _ (fun i hi => mulVec_apply_eq_zero_of_upper hu (fun k hk => hb k (le_trans hi hk))) (by rw [← hmv]; exact hbx)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mulVec_apply_eq_of_upper hv hvd hagt, haj]`. Conclude with `mulVec_apply_eq_zero_of_upper hv (fun k hk => hagt k (lt_of_lt_of_le hi hk))`. Rewrite using `[hmv, Matrix.mulVec_mulVec a u v, huv, Matrix.one_mulVec, hax]`.
-/
theorem firstRel_mul (x : Matrix (Fin n) (Fin ρ) E) (j : Fin ρ) {u v : Matrix (Fin ρ) (Fin ρ) E}
    (hu : ∀ i k, k < i → u i k = 0) (hv : ∀ i k, k < i → v i k = 0) (hvd : ∀ i, v i i = 1)
    (huv : u * v = 1) (hvu : v * u = 1) (h : FirstRel x j) : FirstRel (x * u) j := by
  obtain ⟨h1, a, haj, hagt, hax⟩ := h
  have hmv : ∀ b, (x * u) *ᵥ b = x *ᵥ (u *ᵥ b) := fun b => (Matrix.mulVec_mulVec b x u).symm
  refine ⟨fun b hb hbx => ?_, v *ᵥ a, ?_, fun i hi => ?_, ?_⟩
  · have hub : u *ᵥ b = 0 :=
      h1 _ (fun i hi => mulVec_apply_eq_zero_of_upper hu (fun k hk => hb k (le_trans hi hk)))
        (by rw [← hmv]; exact hbx)
    calc b = (v * u) *ᵥ b := by rw [hvu, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, hub, Matrix.mulVec_zero]
  · rw [mulVec_apply_eq_of_upper hv hvd hagt, haj]
  · exact mulVec_apply_eq_zero_of_upper hv (fun k hk => hagt k (lt_of_lt_of_le hi hk))
  · rw [hmv, Matrix.mulVec_mulVec a u v, huv, Matrix.one_mulVec, hax]

/- English proof (translation)
Establish `hdet : u.det = 1`. Rewrite using `[Matrix.det_of_upperTriangular (fun i k h => hu i k h)]`. Simplify using `[hd]`. Establish `hunit : IsUnit u.det` using `by rw [hdet]; exact isUnit_one`. Use `letI : Invertible u := Matrix.invertibleOfIsUnitDet u hunit`.

Establish `huv : u * u⁻¹ = 1` using `Matrix.mul_nonsing_inv u hunit`. Establish `hvu : u⁻¹ * u = 1` using `Matrix.nonsing_inv_mul u hunit`. Establish `hv : ∀ i k, k < i → u⁻¹ i k = 0` using `fun i k h => Matrix.blockTriangular_inv_of_blockTriangular (b := id) (fun i k h => hu i k h) h`. Establish `hvd : ∀ i, u⁻¹ i i = 1`. Introduce `i`.

Establish `e` using `congrFun (congrFun hvu i) i`. Rewrite `e` using `[Matrix.mul_apply, Finset.sum_eq_single i]`. Simplify `e` using `[hd]`. Introduce `k _ hk`. Break down `lt_or_gt_of_ne hk with h | h` into its components or cases.

Simplify using `[hv i k h]`. Simplify using `[hu k i h]`. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Conclude with `firstRel_mul x j hu hv hvd huv hvu`.

Introduce `h`. Use `firstRel_mul (x * u) j hv hu hd hvu huv h` as an intermediate fact. Rewrite `this` using `[Matrix.mul_assoc, huv, Matrix.mul_one]`. Then use the resulting hypothesis.
-/
theorem firstRel_mul_iff (x : Matrix (Fin n) (Fin ρ) E) (j : Fin ρ) (u : Matrix (Fin ρ) (Fin ρ) E)
    (hd : ∀ i, u i i = 1) (hu : ∀ i k, k < i → u i k = 0) :
    FirstRel x j ↔ FirstRel (x * u) j := by
  have hdet : u.det = 1 := by
    rw [Matrix.det_of_upperTriangular (fun i k h => hu i k h)]
    simp [hd]
  have hunit : IsUnit u.det := by rw [hdet]; exact isUnit_one
  letI : Invertible u := Matrix.invertibleOfIsUnitDet u hunit
  have huv : u * u⁻¹ = 1 := Matrix.mul_nonsing_inv u hunit
  have hvu : u⁻¹ * u = 1 := Matrix.nonsing_inv_mul u hunit
  have hv : ∀ i k, k < i → u⁻¹ i k = 0 := fun i k h =>
    Matrix.blockTriangular_inv_of_blockTriangular (b := id) (fun i k h => hu i k h) h
  have hvd : ∀ i, u⁻¹ i i = 1 := by
    intro i
    have e := congrFun (congrFun hvu i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at e
    · simpa [hd] using e
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · simp [hv i k h]
      · simp [hu k i h]
    · simp
  constructor
  · exact firstRel_mul x j hu hv hvd huv hvu
  · intro h
    have := firstRel_mul (x * u) j hv hu hd hvu huv h
    rwa [Matrix.mul_assoc, huv, Matrix.mul_one] at this

/- English proof (translation)
Introduce `E _ n ρ x`. Conclude with `⟨not_linearIndependent_iff_exists x, fun j j' h h' => firstRel_unique x h h', fun j u hd hu => firstRel_mul_iff x j u hd hu⟩`.
-/
theorem dependent_frame_first_relation : ∀ (E : Type) [Field E] (n ρ : ℕ) (x : Matrix (Fin n) (Fin ρ) E), (¬ LinearIndependent E x.transpose ↔ ∃ j : Fin ρ, (∀ a : Fin ρ → E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧ ∃ a : Fin ρ → E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0) ∧ (∀ j j' : Fin ρ, ((∀ a : Fin ρ → E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧ ∃ a : Fin ρ → E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0) → ((∀ a : Fin ρ → E, (∀ i, j' ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧ ∃ a : Fin ρ → E, a j' = 1 ∧ (∀ i, j' < i → a i = 0) ∧ x *ᵥ a = 0) → j = j') ∧ ∀ (j : Fin ρ) (u : Matrix (Fin ρ) (Fin ρ) E), (∀ i, u i i = 1) → (∀ i k, k < i → u i k = 0) → (((∀ a : Fin ρ → E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧ ∃ a : Fin ρ → E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0) ↔ ((∀ a : Fin ρ → E, (∀ i, j ≤ i → a i = 0) → (x * u) *ᵥ a = 0 → a = 0) ∧ ∃ a : Fin ρ → E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ (x * u) *ᵥ a = 0)) := by
  intro E _ n ρ x
  exact ⟨not_linearIndependent_iff_exists x, fun j j' h h' => firstRel_unique x h h',
    fun j u hd hu => firstRel_mul_iff x j u hd hu⟩

end GlobalTheory.DepFrame
