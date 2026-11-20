import Mathlib
import Formalism.PeriodIntegrals.VolNzeroOne

noncomputable section

namespace PI.VolNzeroOne.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

/- English proof (translation)
Establish `h` using `congrFun hv k`. Simplify using `only [Matrix.mulVec, dotProduct, hrow, Pi.zero_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h`. Conclude with `(mul_eq_zero.mp h).resolve_left hd`.
-/
theorem coord_zero_of_row {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (v : Fin n → E)
    (hv : Matrix.mulVec G v = 0) (k i : Fin n) (d : E) (hd : d ≠ 0)
    (hrow : ∀ j, G k j = if j = i then d else 0) : v i = 0 := by
  have h := congrFun hv k
  simp only [Matrix.mulVec, dotProduct, hrow, Pi.zero_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  exact (mul_eq_zero.mp h).resolve_left hd

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc`. Establish `key : ∀ a, ∑ b, gramE σ J X a b * c b = hE σ J (X a) (∑ b, c b • X b)`. Introduce `a`. Simplify using `only [gramE, hE, Formalism.UG.hform, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]`.

Rewrite using `[Finset.sum_comm]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[Finset.sum_comm]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `j _`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `b _`. Expand and normalize the polynomial expressions, which then agree. Establish `hG : Matrix.mulVec (gramE σ J X) c = 0`.

Use function extensionality and compare the values at `a`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.zero_apply]`. Rewrite using `[key, hc]`. Simplify using `[hE, Formalism.UG.hform]`. Establish `hc0` using `Matrix.eq_zero_of_mulVec_eq_zero h hG`.

Introduce `i`. Conclude with `congrFun hc0 i`.
-/
theorem linIndep_of_gram {n M : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → E) (h : (gramE σ J X).det ≠ 0) : LinearIndependent E X := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have key : ∀ a, ∑ b, gramE σ J X a b * c b = hE σ J (X a) (∑ b, c b • X b) := by
    intro a
    simp only [gramE, hE, Formalism.UG.hform, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hG : Matrix.mulVec (gramE σ J X) c = 0 := by
    funext a
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [key, hc]
    simp [hE, Formalism.UG.hform]
  have hc0 := Matrix.eq_zero_of_mulVec_eq_zero h hG
  intro i
  exact congrFun hc0 i

end Alg

section Frames

variable {F E : Type} [Field F] [Field E] [Algebra F E]

/- English proof (translation)
Simplify using `[F0]`.
-/
theorem frameInitialVectors_castSucc {M r : ℕ} (P : Frame E M r) (a : Fin r) : F0 P (Fin.castSucc a) = P.e a := by
  simp [F0]

/- English proof (translation)
Simplify using `[F0]`.
-/
theorem frameInitialVectors_last {M r : ℕ} (P : Frame E M r) : F0 P (Fin.last r) = P.z := by
  simp [F0]

/- English proof (translation)
Simplify using `[tupH, F0]`.
-/
theorem tupH_e {M r : ℕ} (P : Frame E M r) (a : Fin r) :
    tupH P (Fin.castAdd r (Fin.castSucc a)) = P.e a := by
  simp [tupH, F0]

/- English proof (translation)
Simplify using `[tupH, F0]`.
-/
theorem tupH_alt {M r : ℕ} (P : Frame E M r) : tupH P (Fin.castAdd r (Fin.last r)) = P.z := by
  simp [tupH, F0]

/- English proof (translation)
Simplify using `[tupH]`.
-/
theorem tupH_f {M r : ℕ} (P : Frame E M r) (a : Fin r) : tupH P (Fin.natAdd (r + 1) a) = P.f a := by
  simp [tupH]

/- English proof (translation)
Introduce `h`. Establish `h'` using `congrArg Fin.val h`. Simplify using `at h'`. Use linear arithmetic over natural numbers and integers.
-/
theorem iz_ne_ie {r : ℕ} (a : Fin r) :
    (Fin.castAdd r (Fin.last r) : Fin (r + 1 + r)) ≠ Fin.castAdd r (Fin.castSucc a) := by
  intro h
  have h' := congrArg Fin.val h
  simp at h'
  omega

/- English proof (translation)
Introduce `h`. Establish `h'` using `congrArg Fin.val h`. Simplify using `at h'`. Use linear arithmetic over natural numbers and integers.
-/
theorem if_ne_ie {r : ℕ} (a b : Fin r) :
    (Fin.natAdd (r + 1) a : Fin (r + 1 + r)) ≠ Fin.castAdd r (Fin.castSucc b) := by
  intro h
  have h' := congrArg Fin.val h
  simp at h'
  omega

/- English proof (translation)
Introduce `h`. Establish `h'` using `congrArg Fin.val h`. Simplify using `at h'`. Use linear arithmetic over natural numbers and integers.
-/
theorem if_ne_iz {r : ℕ} (a : Fin r) :
    (Fin.natAdd (r + 1) a : Fin (r + 1 + r)) ≠ Fin.castAdd r (Fin.last r) := by
  intro h
  have h' := congrArg Fin.val h
  simp at h'
  omega

/- English proof (translation)
Establish `h'` using `congrArg Fin.val h`. Simplify using `at h'`. Conclude with `Fin.ext h'`.
-/
theorem ie_inj {r : ℕ} {a b : Fin r}
    (h : (Fin.castAdd r (Fin.castSucc a) : Fin (r + 1 + r)) = Fin.castAdd r (Fin.castSucc b)) :
    a = b := by
  have h' := congrArg Fin.val h
  simp at h'
  exact Fin.ext h'

/- English proof (translation)
Establish `h'` using `congrArg Fin.val h`. Simplify using `at h'`. Conclude with `Fin.ext h'`.
-/
theorem if_inj {r : ℕ} {a b : Fin r}
    (h : (Fin.natAdd (r + 1) a : Fin (r + 1 + r)) = Fin.natAdd (r + 1) b) : a = b := by
  have h' := congrArg Fin.val h
  simp at h'
  exact Fin.ext h'

variable {M r : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (P : Frame E M r) (T : F)

/- English proof (translation)
Take `⟨h1, h2, h3, h4, h5, h6, h7⟩` from `hP`. Introduce `j`. Proceed by induction on `j using Fin.addCases with`. Consider the case `left k`. Proceed by induction on `k using Fin.lastCases with`.

Consider the case `last`. Simplify using `only [gramE, tupH_alt, tupH_f]`. Rewrite using `[h5 a, if_neg (iz_ne_ie a)]`. Consider the case `cast c`. Rewrite using `[← hT1]`.

Simplify using `only [gramE, tupH_e, tupH_f]`. Rewrite using `[h3 c a]`. Distinguish the cases in `hca : c = a`. Substitute `hca` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[if_neg hca, if_neg (fun h => hca (ie_inj h)), map_zero]`. Consider the case `right b`. Simplify using `only [gramE, tupH_f]`. Rewrite using `[h2 a b, if_neg (if_ne_ie b a)]`.
-/
theorem row_f (hP : P.IsStd σ J T)
    (hT1 : ∀ i j, σ (gramE σ J (tupH P) j i) = gramE σ J (tupH P) i j) (a : Fin r) :
    ∀ j, gramE σ J (tupH P) (Fin.natAdd (r + 1) a) j =
      if j = Fin.castAdd r (Fin.castSucc a) then 1 else 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hP
  intro j
  induction j using Fin.addCases with
  | left k =>
    induction k using Fin.lastCases with
    | last =>
      simp only [gramE, tupH_alt, tupH_f]
      rw [h5 a, if_neg (iz_ne_ie a)]
    | cast c =>
      rw [← hT1]
      simp only [gramE, tupH_e, tupH_f]
      rw [h3 c a]
      by_cases hca : c = a
      · subst hca
        simp
      · rw [if_neg hca, if_neg (fun h => hca (ie_inj h)), map_zero]
  | right b =>
    simp only [gramE, tupH_f]
    rw [h2 a b, if_neg (if_ne_ie b a)]

/- English proof (translation)
Take `⟨h1, h2, h3, h4, h5, h6, h7⟩` from `hP`. Introduce `j`. Proceed by induction on `j using Fin.addCases with`. Consider the case `left k`. Proceed by induction on `k using Fin.lastCases with`.

Consider the case `last`. Simplify using `only [gramE, tupH_alt]`. Rewrite using `[h6]`. Simplify using the standard rewrite rules. Consider the case `cast c`.

Rewrite using `[← hT1]`. Simplify using `only [gramE, tupH_e, tupH_alt]`. Rewrite using `[h4 c, map_zero, if_neg (fun h => iz_ne_ie c h.symm)]`. Consider the case `right b`. Rewrite using `[← hT1]`.

Simplify using `only [gramE, tupH_alt, tupH_f]`. Rewrite using `[h5 b, map_zero, if_neg (if_ne_iz b)]`.
-/
theorem herm_wCell_last_mul_mulVec_eq_of_inWb (hP : P.IsStd σ J T)
    (hT1 : ∀ i j, σ (gramE σ J (tupH P) j i) = gramE σ J (tupH P) i j) :
    ∀ j, gramE σ J (tupH P) (Fin.castAdd r (Fin.last r)) j =
      if j = Fin.castAdd r (Fin.last r) then algebraMap F E (-T) else 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hP
  intro j
  induction j using Fin.addCases with
  | left k =>
    induction k using Fin.lastCases with
    | last =>
      simp only [gramE, tupH_alt]
      rw [h6]
      simp
    | cast c =>
      rw [← hT1]
      simp only [gramE, tupH_e, tupH_alt]
      rw [h4 c, map_zero, if_neg (fun h => iz_ne_ie c h.symm)]
  | right b =>
    rw [← hT1]
    simp only [gramE, tupH_alt, tupH_f]
    rw [h5 b, map_zero, if_neg (if_ne_iz b)]

/- English proof (translation)
Take `⟨h1, h2, h3, h4, h5, h6, h7⟩` from `hP`. Introduce `j`. Proceed by induction on `j using Fin.addCases with`. Consider the case `left k`. Proceed by induction on `k using Fin.lastCases with`.

Consider the case `last`. Simplify using `only [gramE, tupH_e, tupH_alt]`. Rewrite using `[h4 a, if_neg (fun h => if_ne_iz a h.symm)]`. Consider the case `cast c`. Simplify using `only [gramE, tupH_e]`.

Rewrite using `[h1 a c, if_neg (fun h => if_ne_ie a c h.symm)]`. Consider the case `right b`. Simplify using `only [gramE, tupH_e, tupH_f]`. Rewrite using `[h3 a b]`. Distinguish the cases in `hab : a = b`.

Substitute `hab` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg hab, if_neg (fun h => hab (if_inj h).symm)]`.
-/
theorem row_e (hP : P.IsStd σ J T) (a : Fin r) :
    ∀ j, gramE σ J (tupH P) (Fin.castAdd r (Fin.castSucc a)) j =
      if j = Fin.natAdd (r + 1) a then 1 else 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hP
  intro j
  induction j using Fin.addCases with
  | left k =>
    induction k using Fin.lastCases with
    | last =>
      simp only [gramE, tupH_e, tupH_alt]
      rw [h4 a, if_neg (fun h => if_ne_iz a h.symm)]
    | cast c =>
      simp only [gramE, tupH_e]
      rw [h1 a c, if_neg (fun h => if_ne_ie a c h.symm)]
  | right b =>
    simp only [gramE, tupH_e, tupH_f]
    rw [h3 a b]
    by_cases hab : a = b
    · subst hab
      simp
    · rw [if_neg hab, if_neg (fun h => hab (if_inj h).symm)]

/- English proof (translation)
Establish `hTne : algebraMap F E (-T) ≠ 0`. Rewrite using `[map_neg, neg_ne_zero]`. Conclude with `(map_ne_zero (algebraMap F E)).mpr hP.2.2.2.2.2.2`. Introduce `hdet`. Take `⟨v, hv0, hv⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr hdet`.

Apply `hv0` to reduce the goal to its premises. Use function extensionality and compare the values at `j`. Proceed by induction on `j using Fin.addCases with`. Consider the case `left k`. Proceed by induction on `k using Fin.lastCases with`.

Consider the case `last => exact coord_zero_of_row _ v hv _ _ _ hTne (herm_wCell_last_mul_mulVec_eq_of_inWb σ J P T hP hT1)`. Consider the case `cast c => exact coord_zero_of_row _ v hv _ _ 1 one_ne_zero (row_f σ J P T hP hT1 c)`. Consider the case `right b => exact coord_zero_of_row _ v hv _ _ 1 one_ne_zero (row_e σ J P T hP b)`.
-/
theorem det_gram_tupH_ne_zero (hP : P.IsStd σ J T)
    (hT1 : ∀ i j, σ (gramE σ J (tupH P) j i) = gramE σ J (tupH P) i j) :
    (gramE σ J (tupH P)).det ≠ 0 := by
  have hTne : algebraMap F E (-T) ≠ 0 := by
    rw [map_neg, neg_ne_zero]
    exact (map_ne_zero (algebraMap F E)).mpr hP.2.2.2.2.2.2
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv0
  funext j
  induction j using Fin.addCases with
  | left k =>
    induction k using Fin.lastCases with
    | last => exact coord_zero_of_row _ v hv _ _ _ hTne (herm_wCell_last_mul_mulVec_eq_of_inWb σ J P T hP hT1)
    | cast c => exact coord_zero_of_row _ v hv _ _ 1 one_ne_zero (row_f σ J P T hP hT1 c)
  | right b => exact coord_zero_of_row _ v hv _ _ 1 one_ne_zero (row_e σ J P T hP b)

/- English proof (translation)
Establish `h` using `linIndep_of_gram σ J (tupH P) (det_gram_tupH_ne_zero σ J P T hP hT1)`. Establish `he : F0 P = tupH P ∘ Fin.castAdd r`. Use function extensionality and compare the values at `i`. Simplify using `[tupH]`. Rewrite using `[he]`.

Conclude with `h.comp _ (Fin.castAdd_injective _ _)`.
-/
theorem linearIndependent_frame_with_normal (hP : P.IsStd σ J T)
    (hT1 : ∀ i j, σ (gramE σ J (tupH P) j i) = gramE σ J (tupH P) i j) :
    LinearIndependent E (F0 P) := by
  have h := linIndep_of_gram σ J (tupH P) (det_gram_tupH_ne_zero σ J P T hP hT1)
  have he : F0 P = tupH P ∘ Fin.castAdd r := by
    funext i
    simp [tupH]
  rw [he]
  exact h.comp _ (Fin.castAdd_injective _ _)

/- English proof (translation)
Take `⟨h1, h2, h3, h4, h5, h6, h7⟩` from `hP`. Introduce `i j`. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last`. Proceed by induction on `j using Fin.lastCases with`.

Consider the case `last`. Simplify using `only [gramE, frameInitialVectors_last]`. Rewrite using `[h6]`. Simplify using the standard rewrite rules. Consider the case `cast b`.

Rewrite using `[← hT0]`. Simplify using `only [gramE, frameInitialVectors_last, frameInitialVectors_castSucc]`. Rewrite using `[h4 b, map_zero]`. Simplify using `[(Fin.castSucc_lt_last b).ne]`. Consider the case `cast a`.

Proceed by induction on `j using Fin.lastCases with`. Consider the case `last`. Simplify using `only [gramE, frameInitialVectors_last, frameInitialVectors_castSucc]`. Rewrite using `[h4 a]`. Simplify using `[(Fin.castSucc_lt_last a).ne]`.

Consider the case `cast b`. Simplify using `only [gramE, frameInitialVectors_castSucc]`. Rewrite using `[h1 a b]`. Simplify using `[(Fin.castSucc_lt_last a).ne]`.
-/
theorem gram_frame_with_normal_eq_diag (hP : P.IsStd σ J T)
    (hT0 : ∀ i j, σ (gramE σ J (F0 P) j i) = gramE σ J (F0 P) i j) :
    ∀ i j, gramE σ J (F0 P) i j =
      if i = Fin.last r ∧ j = Fin.last r then algebraMap F E (-T) else 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hP
  intro i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last =>
      simp only [gramE, frameInitialVectors_last]
      rw [h6]
      simp
    | cast b =>
      rw [← hT0]
      simp only [gramE, frameInitialVectors_last, frameInitialVectors_castSucc]
      rw [h4 b, map_zero]
      simp [(Fin.castSucc_lt_last b).ne]
  | cast a =>
    induction j using Fin.lastCases with
    | last =>
      simp only [gramE, frameInitialVectors_last, frameInitialVectors_castSucc]
      rw [h4 a]
      simp [(Fin.castSucc_lt_last a).ne]
    | cast b =>
      simp only [gramE, frameInitialVectors_castSucc]
      rw [h1 a b]
      simp [(Fin.castSucc_lt_last a).ne]

end Frames

end PI.VolNzeroOne.W
