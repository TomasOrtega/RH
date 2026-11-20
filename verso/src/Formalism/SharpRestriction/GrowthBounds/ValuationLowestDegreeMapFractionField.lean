import Formalism.SharpRestriction.GrowthBounds.ValuationLowestDegreeRename
import Formalism.SharpRestriction.GrowthBounds.SourceCleaning

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.G.Joints.StandardMonomialSpace

open Formalism.MainNotions.G

section Base

variable {R R' : Type} [CommRing R] [CommRing R']

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem genMat_eq (R : Type) [CommRing R] (n : ℕ) : genMat R n = Matrix.mvPolynomialX (Fin n) (Fin n) R := by
  rfl

/- English proof (translation)
Rewrite using `[genMat_eq]`. Conclude with `Matrix.det_mvPolynomialX_ne_zero _ _`.
-/
theorem genMat_det_ne_zero (R : Type) [CommRing R] [Nontrivial R] (n : ℕ) : (genMat R n).det ≠ 0 := by
  rw [genMat_eq]
  exact Matrix.det_mvPolynomialX_ne_zero _ _

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[genMat]`.
-/
theorem genMat_map (f : R →+* R') (n : ℕ) : (MvPolynomial.map f).mapMatrix (genMat R n) = genMat R' n := by
  ext a b
  simp [genMat]

/- English proof (translation)
Rewrite using `[RingHom.map_det, genMat_map]`.
-/
theorem genMat_det_map (f : R →+* R') (n : ℕ) : MvPolynomial.map f (genMat R n).det = (genMat R' n).det := by
  rw [RingHom.map_det, genMat_map]

def glMap (f : R →+* R') (n : ℕ) : GLCoord R n →+* GLCoord R' n :=
  IsLocalization.map (M := Submonoid.powers (genMat R n).det) (T := Submonoid.powers (genMat R' n).det)
    (GLCoord R' n) (MvPolynomial.map f) (by
      rintro x ⟨k, rfl⟩
      exact ⟨k, by simp [genMat_det_map]⟩)

/- English proof (translation)
Unfold `glMap`. Conclude with `IsLocalization.map_eq _ _`.
-/
theorem glMap_algebraMap (f : R →+* R') (n : ℕ) (x : MvPolynomial (Fin n × Fin n) R) :
    glMap f n (algebraMap _ (GLCoord R n) x) = algebraMap _ (GLCoord R' n) (MvPolynomial.map f x) := by
  unfold glMap
  exact IsLocalization.map_eq _ _

/- English proof (translation)
Establish `h1 : algebraMap _ (GLCoord R' n) (genMat R' n).det * glMap f n (IsLocalization.Away.invSelf (genMat R n).det) = 1`. Establish `e : algebraMap _ (GLCoord R' n) (genMat R' n).det = glMap f n (algebraMap _ _ (genMat R n).det)`. Rewrite using `[glMap_algebraMap, genMat_det_map]`. Rewrite using `[e, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]`. Establish `h2 : algebraMap _ (GLCoord R' n) (genMat R' n).det * (IsLocalization.Away.invSelf (genMat R' n).det : GLCoord R' n) = 1` using `IsLocalization.Away.mul_invSelf _`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem glMap_invSelf (f : R →+* R') (n : ℕ) :
    glMap f n (IsLocalization.Away.invSelf (genMat R n).det) = IsLocalization.Away.invSelf (genMat R' n).det := by
  have h1 : algebraMap _ (GLCoord R' n) (genMat R' n).det *
      glMap f n (IsLocalization.Away.invSelf (genMat R n).det) = 1 := by
    have e : algebraMap _ (GLCoord R' n) (genMat R' n).det = glMap f n (algebraMap _ _ (genMat R n).det) := by
      rw [glMap_algebraMap, genMat_det_map]
    rw [e, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]
  have h2 : algebraMap _ (GLCoord R' n) (genMat R' n).det *
      (IsLocalization.Away.invSelf (genMat R' n).det : GLCoord R' n) = 1 := IsLocalization.Away.mul_invSelf _
  calc glMap f n (IsLocalization.Away.invSelf (genMat R n).det)
      = glMap f n (IsLocalization.Away.invSelf (genMat R n).det) * (algebraMap _ (GLCoord R' n) (genMat R' n).det *
      (IsLocalization.Away.invSelf (genMat R' n).det : GLCoord R' n)) := by rw [h2, mul_one]
    _ = (algebraMap _ (GLCoord R' n) (genMat R' n).det *
      glMap f n (IsLocalization.Away.invSelf (genMat R n).det)) * IsLocalization.Away.invSelf (genMat R' n).det := by ring
    _ = _ := by rw [h1, one_mul]

/- English proof (translation)
Unfold `glMap`. Use `IsLocalization.map_injective_of_injective' (hN := ?_) (hf' := MvPolynomial.map_injective f hf) ..` and prove the remaining obligations. Introduce and unpack `⟨k, hk⟩`. Conclude with `pow_ne_zero k (genMat_det_ne_zero R' n) hk`.
-/
theorem glMap_injective [IsDomain R'] (f : R →+* R') (hf : Function.Injective f) (n : ℕ) :
    Function.Injective (glMap f n) := by
  unfold glMap
  refine IsLocalization.map_injective_of_injective' (hN := ?_) (hf' := MvPolynomial.map_injective f hf) ..
  rintro ⟨k, hk⟩
  exact pow_ne_zero k (genMat_det_ne_zero R' n) hk

def lMap (f : R →+* R') (n : ℕ) : GLLaurent R n →+* GLLaurent R' n := AddMonoidAlgebra.mapRingHom ℤ (glMap f n)

/- English proof (translation)
Rewrite using `[← LaurentPolynomial.single_eq_C, ← LaurentPolynomial.single_eq_C]`. Conclude with `AddMonoidAlgebra.mapRingHom_single _ _ _`.
-/
theorem lMap_C (f : R →+* R') (n : ℕ) (x : GLCoord R n) :
    lMap f n (LaurentPolynomial.C x) = LaurentPolynomial.C (glMap f n x) := by
  rw [← LaurentPolynomial.single_eq_C, ← LaurentPolynomial.single_eq_C]
  exact AddMonoidAlgebra.mapRingHom_single _ _ _

/- English proof (translation)
Unfold `LaurentPolynomial.T lMap`. Rewrite using `[AddMonoidAlgebra.mapRingHom_single, map_one]`.
-/
theorem lMap_alt (f : R →+* R') (n : ℕ) (k : ℤ) :
    lMap f n (LaurentPolynomial.T k) = LaurentPolynomial.T k := by
  unfold LaurentPolynomial.T lMap
  rw [AddMonoidAlgebra.mapRingHom_single, map_one]

/- English proof (translation)
The claim follows from `AddMonoidAlgebra.coeff_mapRingHom _ _ _`.
-/
theorem lMap_coeff (f : R →+* R') (n : ℕ) (x : GLLaurent R n) (k : ℤ) :
    (lMap f n x).coeff k = glMap f n (x.coeff k) := AddMonoidAlgebra.coeff_mapRingHom _ _ _

/- English proof (translation)
Introduce `x y h`. Use `LaurentPolynomial.ext fun k => glMap_injective f hf n ?_` and prove the remaining obligations. Rewrite using `[← lMap_coeff, ← lMap_coeff, h]`.
-/
theorem lMap_injective [IsDomain R'] (f : R →+* R') (hf : Function.Injective f) (n : ℕ) :
    Function.Injective (lMap f n) := by
  intro x y h
  refine LaurentPolynomial.ext fun k => glMap_injective f hf n ?_
  rw [← lMap_coeff, ← lMap_coeff, h]

/- English proof (translation)
Use extensionality with `k`. Rewrite using `[Finsupp.mem_support_iff, Finsupp.mem_support_iff, lMap_coeff, Ne, Ne, map_eq_zero_iff _ (glMap_injective f hf n)]`.
-/
theorem lMap_support [IsDomain R'] (f : R →+* R') (hf : Function.Injective f) (n : ℕ) (x : GLLaurent R n) :
    (lMap f n x).coeff.support = x.coeff.support := by
  ext k
  rw [Finsupp.mem_support_iff, Finsupp.mem_support_iff, lMap_coeff, Ne, Ne,
    map_eq_zero_iff _ (glMap_injective f hf n)]

/- English proof (translation)
Simplify using `[coefL, lMap_C, glMap_algebraMap]`.
-/
theorem lMap_coefL (f : R →+* R') (n : ℕ) (a : R) : lMap f n (coefL R n a) = coefL R' n (f a) := by
  simp [coefL, lMap_C, glMap_algebraMap]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[gL, lMap_C, glMap_algebraMap, genMat]`.
-/
theorem gL_map (f : R →+* R') (n : ℕ) : (lMap f n).mapMatrix (gL R n) = gL R' n := by
  ext a b
  simp [gL, lMap_C, glMap_algebraMap, genMat]

/- English proof (translation)
Use extensionality with `a b`. Establish `h : MvPolynomial.map f ((genMat R n).adjugate a b) = (genMat R' n).adjugate a b`. Rewrite using `[← genMat_map f, ← RingHom.map_adjugate]`. Both sides reduce to the same expression. Simplify using `[gLinv, lMap_C, glMap_algebraMap, glMap_invSelf, h]`.
-/
theorem gLinv_map (f : R →+* R') (n : ℕ) : (lMap f n).mapMatrix (gLinv R n) = gLinv R' n := by
  ext a b
  have h : MvPolynomial.map f ((genMat R n).adjugate a b) = (genMat R' n).adjugate a b := by
    rw [← genMat_map f, ← RingHom.map_adjugate]; rfl
  simp [gLinv, lMap_C, glMap_algebraMap, glMap_invSelf, h]

/- English proof (translation)
Unfold `twistMat`. Rewrite using `[map_mul, map_mul, gL_map, gLinv_map]`. Use `congr 2`. Use extensionality with `a b`. Distinguish the cases in `hab : a = b`.

Substitute `hab` using the available equality. Apply the tactic sequence `by_cases ha : a = j <;> simp [ha, lMap_alt]`. Simplify using `[hab]`.
-/
theorem twistMat_map (f : R →+* R') (n : ℕ) (j : Fin n) (k : ℤ) :
    (lMap f n).mapMatrix (twistMat R n j k) = twistMat R' n j k := by
  unfold twistMat
  rw [map_mul, map_mul, gL_map, gLinv_map]
  congr 2
  ext a b
  by_cases hab : a = b
  · subst hab
    by_cases ha : a = j <;> simp [ha, lMap_alt]
  · simp [hab]

/- English proof (translation)
Rewrite using `[← twistMat_map f]`. Both sides reduce to the same expression.
-/
theorem twistMat_map_apply (f : R →+* R') (n : ℕ) (j : Fin n) (k : ℤ) (a b : Fin n) :
    lMap f n (twistMat R n j k a b) = twistMat R' n j k a b := by
  rw [← twistMat_map f]; rfl

/- English proof (translation)
Proceed by induction on `A using MvPolynomial.induction_on with`. Consider the case `C a => simp [twistSub, lMap_coefL]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p v hp`. Simplify using `only [map_mul, hp, map_X]`.

Use `congr 1`. Simplify using `only [twistSub, eval₂Hom_X']`. Distinguish the cases in `h1 : v.1 ∈ S`. Apply the tactic sequence `by_cases h2 : LL.vec v.1 = true <;> simp [h1, h2, map_sum, twistMat_map_apply]`. Simplify using `[h1]`.
-/
theorem twistSub_map (f : R →+* R') {ι : Type} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    (A : MvPolynomial (ι × Fin n) R) :
    twistSub LL S j (MvPolynomial.map f A) = MvPolynomial.map (lMap f n) (twistSub LL S j A) := by
  induction A using MvPolynomial.induction_on with
  | C a => simp [twistSub, lMap_coefL]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp only [twistSub, eval₂Hom_X']
    by_cases h1 : v.1 ∈ S
    · by_cases h2 : LL.vec v.1 = true <;> simp [h1, h2, map_sum, twistMat_map_apply]
    · simp [h1]

/- English proof (translation)
Unfold `sDegs`. Rewrite using `[twistSub_map, support_map_of_injective _ (lMap_injective f hf n)]`. Use `Finset.biUnion_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_map, lMap_support f hf]`.
-/
theorem sDegs_map [IsDomain R'] (f : R →+* R') (hf : Function.Injective f) {ι : Type} {n : ℕ} (LL : Letters ι)
    (S : Set ι) (j : Fin n) (A : MvPolynomial (ι × Fin n) R) :
    sDegs LL S j (MvPolynomial.map f A) = sDegs LL S j A := by
  unfold sDegs
  rw [twistSub_map, support_map_of_injective _ (lMap_injective f hf n)]
  refine Finset.biUnion_congr rfl fun m _ => ?_
  rw [coeff_map, lMap_support f hf]

/- English proof (translation)
Unfold `valS`. Rewrite using `[sDegs_map f hf]`.
-/
theorem valS_map [IsDomain R'] (f : R →+* R') (hf : Function.Injective f) {ι : Type} {n : ℕ} [NeZero n]
    (LL : Letters ι) (S : Set ι) (A : MvPolynomial (ι × Fin n) R) :
    valS LL S (MvPolynomial.map f A) = valS LL S A := by
  unfold valS; rw [sDegs_map f hf]

/- English proof (translation)
Unfold `lam1S`. Rewrite using `[sDegs_map f hf]`.
-/
theorem lowest_degree_map_of_injective [IsDomain R'] (f : R →+* R') (hf : Function.Injective f) {ι : Type} {n : ℕ} [NeZero n]
    (LL : Letters ι) (S : Set ι) (A : MvPolynomial (ι × Fin n) R) :
    lam1S LL S (MvPolynomial.map f A) = lam1S LL S A := by
  unfold lam1S; rw [sDegs_map f hf]

end Base

section Coord

variable {R : Type} [CommRing R]

def SuppIn {n : ℕ} (s : Set ℤ) (x : GLLaurent R n) : Prop := ∀ m, x.coeff m ≠ 0 → m ∈ s

/- English proof (translation)
Introduce `_ h` and use `absurd rfl h`.
-/
theorem SuppIn.zero {n : ℕ} (s : Set ℤ) : SuppIn s (0 : GLLaurent R n) := fun _ h => absurd rfl h

/- English proof (translation)
Introduce `m h`. Assume the negation of the conclusion as `hm`. Establish `h1 : x.coeff m = 0` using `by by_contra h1; exact hm (hx m h1)`. Establish `h2 : y.coeff m = 0` using `by by_contra h2; exact hm (hy m h2)`. Apply `h` to reduce the goal to its premises.

Rewrite using `[AddMonoidAlgebra.coeff_add, Finsupp.add_apply, h1, h2, add_zero]`.
-/
theorem SuppIn.add {n : ℕ} {s : Set ℤ} {x y : GLLaurent R n} (hx : SuppIn s x) (hy : SuppIn s y) :
    SuppIn s (x + y) := by
  intro m h
  by_contra hm
  have h1 : x.coeff m = 0 := by by_contra h1; exact hm (hx m h1)
  have h2 : y.coeff m = 0 := by by_contra h2; exact hm (hy m h2)
  apply h
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, h1, h2, add_zero]

/- English proof (translation)
Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty`. Rewrite using `[Finset.sum_empty]`. Conclude with `SuppIn.zero s`. Consider the case `@insert a t ha ih`.

Rewrite using `[Finset.sum_insert ha]`. Conclude with `SuppIn.add (h a (Finset.mem_insert_self a t)) (ih fun b hb => h b (Finset.mem_insert_of_mem hb))`.
-/
theorem SuppIn.sum {n : ℕ} {s : Set ℤ} {α : Type} (t : Finset α) (f : α → GLLaurent R n)
    (h : ∀ a ∈ t, SuppIn s (f a)) : SuppIn s (∑ a ∈ t, f a) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact SuppIn.zero s
  | @insert a t ha ih =>
    rw [Finset.sum_insert ha]
    exact SuppIn.add (h a (Finset.mem_insert_self a t)) (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

/- English proof (translation)
Introduce `m h`. Use `LaurentPolynomial.support_C_mul_T a k (Finsupp.mem_support_iff.mpr h)` as an intermediate fact. Rewrite `this` using `[Finset.mem_singleton]`. Rewrite using `[this]` and apply the resulting hypothesis.
-/
theorem SuppIn.C_mul_T {n : ℕ} {s : Set ℤ} (a : GLCoord R n) (k : ℤ) (hk : k ∈ s) :
    SuppIn s (LaurentPolynomial.C a * LaurentPolynomial.T k) := by
  intro m h
  have := LaurentPolynomial.support_C_mul_T a k (Finsupp.mem_support_iff.mpr h)
  rw [Finset.mem_singleton] at this
  rwa [this]

/- English proof (translation)
Unfold `twistMat`. Rewrite using `[Matrix.mul_apply]`. Use `SuppIn.sum _ _ fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_diagonal]`. Simplify using `only [gL, gLinv, Matrix.map_apply]`.

Distinguish the cases in `hc : c = j`. Rewrite using `[if_pos hc, mul_assoc, LaurentPolynomial.T_mul, ← mul_assoc, ← map_mul]`. Conclude with `SuppIn.C_mul_T _ _ (by simp)`. Rewrite using `[if_neg hc, mul_one, ← map_mul, ← mul_one (LaurentPolynomial.C _), ← LaurentPolynomial.T_zero]`. Conclude with `SuppIn.C_mul_T _ _ (by simp)`.
-/
theorem twistMat_suppIn (n : ℕ) (j : Fin n) (k : ℤ) (a b : Fin n) :
    SuppIn ({0, k} : Set ℤ) (twistMat R n j k a b) := by
  unfold twistMat
  rw [Matrix.mul_apply]
  refine SuppIn.sum _ _ fun c _ => ?_
  rw [Matrix.mul_diagonal]
  simp only [gL, gLinv, Matrix.map_apply]
  by_cases hc : c = j
  · rw [if_pos hc, mul_assoc, LaurentPolynomial.T_mul, ← mul_assoc, ← map_mul]
    exact SuppIn.C_mul_T _ _ (by simp)
  · rw [if_neg hc, mul_one, ← map_mul, ← mul_one (LaurentPolynomial.C _), ← LaurentPolynomial.T_zero]
    exact SuppIn.C_mul_T _ _ (by simp)

/- English proof (translation)
Introduce `k hk`. Unfold `sDegs at hk`. Rewrite `hk` using `[Finset.mem_biUnion]`. Take `⟨m, -, hm⟩` from `hk`. Conclude with `h m k (Finsupp.mem_support_iff.mp hm)`.
-/
theorem sDegs_subset {ι : Type} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n) (G : MvPolynomial (ι × Fin n) R)
    (s : Set ℤ) (h : ∀ m, SuppIn s ((twistSub LL S j G).coeff m)) : ∀ k ∈ sDegs LL S j G, k ∈ s := by
  intro k hk
  unfold sDegs at hk
  rw [Finset.mem_biUnion] at hk
  obtain ⟨m, -, hm⟩ := hk
  exact h m k (Finsupp.mem_support_iff.mp hm)

/- English proof (translation)
Use `sDegs_subset LL S j _ _ fun m => ?_` and prove the remaining obligations. Simplify using `only [twistSub, eval₂Hom_X', hl, hv, if_true, coeff_sum, coeff_C_mul]`. Use `SuppIn.sum _ _ fun b _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_X]`. Use `split_ifs`.

Rewrite using `[mul_one]`. Conclude with `twistMat_suppIn n j 1 b c`. Rewrite using `[mul_zero]`. Conclude with `SuppIn.zero _`.
-/
theorem sDegs_X_vec {ι : Type} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n) (l : ι) (c : Fin n) (hl : l ∈ S)
    (hv : LL.vec l = true) : ∀ k ∈ sDegs LL S j (X (l, c) : MvPolynomial (ι × Fin n) R), k ∈ ({0, 1} : Set ℤ) := by
  classical
  refine sDegs_subset LL S j _ _ fun m => ?_
  simp only [twistSub, eval₂Hom_X', hl, hv, if_true, coeff_sum, coeff_C_mul]
  refine SuppIn.sum _ _ fun b _ => ?_
  rw [coeff_X]
  split_ifs
  · rw [mul_one]; exact twistMat_suppIn n j 1 b c
  · rw [mul_zero]; exact SuppIn.zero _

/- English proof (translation)
Use `sDegs_subset LL S j _ _ fun m => ?_` and prove the remaining obligations. Simplify using `only [twistSub, eval₂Hom_X', hl, hv, if_true, coeff_sum, coeff_C_mul, Bool.false_eq_true, if_false]`. Use `SuppIn.sum _ _ fun b _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_X]`. Use `split_ifs`.

Rewrite using `[mul_one]`. Conclude with `twistMat_suppIn n j (-1) c b`. Rewrite using `[mul_zero]`. Conclude with `SuppIn.zero _`.
-/
theorem sDegs_X_cov {ι : Type} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n) (l : ι) (c : Fin n) (hl : l ∈ S)
    (hv : LL.vec l = false) : ∀ k ∈ sDegs LL S j (X (l, c) : MvPolynomial (ι × Fin n) R), k ∈ ({0, -1} : Set ℤ) := by
  classical
  refine sDegs_subset LL S j _ _ fun m => ?_
  simp only [twistSub, eval₂Hom_X', hl, hv, if_true, coeff_sum, coeff_C_mul, Bool.false_eq_true, if_false]
  refine SuppIn.sum _ _ fun b _ => ?_
  rw [coeff_X]
  split_ifs
  · rw [mul_one]; exact twistMat_suppIn n j (-1) c b
  · rw [mul_zero]; exact SuppIn.zero _

/- English proof (translation)
Simplify using `only [valS, Finset.le_inf_iff, WithTop.coe_le_coe]`.
-/
theorem le_valS_iff {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι) (G : MvPolynomial (ι × Fin n) R)
    (th : ℤ) : (th : WithTop ℤ) ≤ valS LL S G ↔ ∀ k ∈ sDegs LL S (lastIdx n) G, th ≤ k := by
  simp only [valS, Finset.le_inf_iff, WithTop.coe_le_coe]

/- English proof (translation)
Simplify using `only [lam1S, Finset.sup_le_iff, WithBot.coe_le_coe]`.
-/
theorem lowest_degree_le_iff {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι) (G : MvPolynomial (ι × Fin n) R)
    (M : ℤ) : lam1S LL S G ≤ (M : WithBot ℤ) ↔ ∀ k ∈ sDegs LL S (0 : Fin n) G, k ≤ M := by
  simp only [lam1S, Finset.sup_le_iff, WithBot.coe_le_coe]

/- English proof (translation)
Use `⟨fun hv => ⟨?_, ?_⟩, fun hv => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Use `(le_valS_iff LL S _ 0).mpr fun k hk => ?_` and prove the remaining obligations. Apply the tactic sequence `rcases sDegs_X_vec LL S _ l c hl hv k hk with h | h <;> simp_all`. Use `(lowest_degree_le_iff LL S _ 1).mpr fun k hk => ?_` and prove the remaining obligations. Apply the tactic sequence `rcases sDegs_X_vec LL S _ l c hl hv k hk with h | h <;> simp_all`.

Use `(le_valS_iff LL S _ (-1)).mpr fun k hk => ?_` and prove the remaining obligations. Apply the tactic sequence `rcases sDegs_X_cov LL S _ l c hl hv k hk with h | h <;> simp_all`. Use `(lowest_degree_le_iff LL S _ 0).mpr fun k hk => ?_` and prove the remaining obligations. Apply the tactic sequence `rcases sDegs_X_cov LL S _ l c hl hv k hk with h | h <;> simp_all`.
-/
theorem coord_clauses {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι) (l : ι) (hl : l ∈ S) (c : Fin n) :
    (LL.vec l = true → (0 : WithTop ℤ) ≤ valS LL S (X (l, c) : MvPolynomial (ι × Fin n) R) ∧
          lam1S LL S (X (l, c) : MvPolynomial (ι × Fin n) R) ≤ (1 : WithBot ℤ)) ∧
    (LL.vec l = false → (-1 : WithTop ℤ) ≤ valS LL S (X (l, c) : MvPolynomial (ι × Fin n) R) ∧
          lam1S LL S (X (l, c) : MvPolynomial (ι × Fin n) R) ≤ (0 : WithBot ℤ)) := by
  refine ⟨fun hv => ⟨?_, ?_⟩, fun hv => ⟨?_, ?_⟩⟩
  · refine (le_valS_iff LL S _ 0).mpr fun k hk => ?_
    rcases sDegs_X_vec LL S _ l c hl hv k hk with h | h <;> simp_all
  · refine (lowest_degree_le_iff LL S _ 1).mpr fun k hk => ?_
    rcases sDegs_X_vec LL S _ l c hl hv k hk with h | h <;> simp_all
  · refine (le_valS_iff LL S _ (-1)).mpr fun k hk => ?_
    rcases sDegs_X_cov LL S _ l c hl hv k hk with h | h <;> simp_all
  · refine (lowest_degree_le_iff LL S _ 0).mpr fun k hk => ?_
    rcases sDegs_X_cov LL S _ l c hl hv k hk with h | h <;> simp_all

/- English proof (translation)
Set `φ : MvPolynomial (Fin n × Fin n) R →+* GLLaurent R n` to `(LaurentPolynomial.C).comp (algebraMap _ (GLCoord R n))`. Establish `h1 : gL R n = φ.mapMatrix (genMat R n)` using `rfl`. Establish `h2 : gLinv R n = LaurentPolynomial.C (IsLocalization.Away.invSelf (genMat R n).det : GLCoord R n) • φ.mapMatrix (genMat R n).adjugate`. Use extensionality with `a b`. Simplify using `[gLinv, φ]`.

Rewrite using `[h1, h2, Matrix.mul_smul, ← map_mul, Matrix.mul_adjugate]`. Use extensionality with `a b`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using `only [RingHom.mapMatrix_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]`.

Simplify using `only [φ, RingHom.comp_apply]`. Rewrite using `[← map_mul, mul_comm, IsLocalization.Away.mul_invSelf, map_one]`. Simplify using `[hab]`.
-/
theorem gL_mul_gLinv (n : ℕ) : gL R n * gLinv R n = 1 := by
  let φ : MvPolynomial (Fin n × Fin n) R →+* GLLaurent R n :=
    (LaurentPolynomial.C).comp (algebraMap _ (GLCoord R n))
  have h1 : gL R n = φ.mapMatrix (genMat R n) := rfl
  have h2 : gLinv R n = LaurentPolynomial.C (IsLocalization.Away.invSelf (genMat R n).det : GLCoord R n) •
      φ.mapMatrix (genMat R n).adjugate := by
    ext a b
    simp [gLinv, φ]
  rw [h1, h2, Matrix.mul_smul, ← map_mul, Matrix.mul_adjugate]
  ext a b
  by_cases hab : a = b
  · subst hab
    simp only [RingHom.mapMatrix_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    simp only [φ, RingHom.comp_apply]
    rw [← map_mul, mul_comm, IsLocalization.Away.mul_invSelf, map_one]
  · simp [hab]

/- English proof (translation)
Unfold `twistMat`. Rewrite using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Finset.prod_ite_eq' Finset.univ j, if_pos (Finset.mem_univ j), mul_right_comm, ← Matrix.det_mul, gL_mul_gLinv, Matrix.det_one, one_mul]`.
-/
theorem twistMat_det (n : ℕ) (j : Fin n) (k : ℤ) : (twistMat R n j k).det = LaurentPolynomial.T k := by
  unfold twistMat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Finset.prod_ite_eq' Finset.univ j, if_pos (Finset.mem_univ j),
    mul_right_comm, ← Matrix.det_mul, gL_mul_gLinv, Matrix.det_one, one_mul]

/- English proof (translation)
Rewrite using `[RingHom.map_det, RingHom.map_det, ← twistMat_det n j 1, RingHom.map_det, ← Matrix.det_mul]`. Use `congr 1`. Use `Matrix.ext fun a c => ?_` and prove the remaining obligations. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply, map_X]`. Simplify using `only [twistSub, eval₂Hom_X', (hy a).1, (hy a).2, if_true]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `b _`. Rewrite using `[mul_comm]`.
-/
theorem twistSub_det {ι : Type} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n) (y : Fin n → ι)
    (hy : ∀ i, y i ∈ S ∧ LL.vec (y i) = true) :
    twistSub LL S j (Matrix.det (Matrix.of fun a b : Fin n => (X (y a, b) : MvPolynomial (ι × Fin n) R))) =
      MvPolynomial.map (coefL R n) (Matrix.det (Matrix.of fun a b : Fin n => (X (y a, b) : MvPolynomial (ι × Fin n) R)))
        * C (LaurentPolynomial.T 1) := by
  rw [RingHom.map_det, RingHom.map_det, ← twistMat_det n j 1, RingHom.map_det, ← Matrix.det_mul]
  congr 1
  refine Matrix.ext fun a c => ?_
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply, map_X]
  simp only [twistSub, eval₂Hom_X', (hy a).1, (hy a).2, if_true]
  apply Finset.sum_congr rfl
  intro b _
  rw [mul_comm]

/- English proof (translation)
Establish `hM : Submonoid.powers (genMat R n).det ≤ nonZeroDivisors _` using `powers_le_nonZeroDivisors_of_noZeroDivisors (genMat_det_ne_zero R n)`. Introduce `a b h`. Simplify using `only [coefL, RingHom.comp_apply] at h`. Establish `h1` using `congrArg (fun x : GLLaurent R n => x.coeff 0) h`. Simplify using `only [LaurentPolynomial.C_apply, if_true] at h1`.

Conclude with `MvPolynomial.C_injective _ _ (IsLocalization.injective (GLCoord R n) hM h1)`.
-/
theorem coefL_injective [IsDomain R] (n : ℕ) : Function.Injective (coefL R n) := by
  have hM : Submonoid.powers (genMat R n).det ≤ nonZeroDivisors _ :=
    powers_le_nonZeroDivisors_of_noZeroDivisors (genMat_det_ne_zero R n)
  intro a b h
  simp only [coefL, RingHom.comp_apply] at h
  have h1 := congrArg (fun x : GLLaurent R n => x.coeff 0) h
  simp only [LaurentPolynomial.C_apply, if_true] at h1
  exact MvPolynomial.C_injective _ _ (IsLocalization.injective (GLCoord R n) hM h1)

/- English proof (translation)
Establish `hg : Function.Injective (fun v : Fin n × Fin n => (y v.1, v.2))`. Introduce `a b h`. Simplify using `only [Prod.mk.injEq] at h`. Conclude with `Prod.ext (hy h.1) h.2`. Establish `e : Matrix.det (Matrix.of fun a b : Fin n => (X (y a, b) : MvPolynomial (ι × Fin n) R)) = rename (fun v : Fin n × Fin n => (y v.1, v.2)) (genMat R n).det`.

Rewrite using `[AlgHom.map_det]`. Use `congr 1`. Use extensionality with `a b`. Simplify using `[genMat]`. Rewrite using `[e]`.

Conclude with `fun h => genMat_det_ne_zero R n (rename_injective _ hg (by rw [h, map_zero]))`.
-/
theorem detX_ne_zero [Nontrivial R] {ι : Type} {n : ℕ} (y : Fin n → ι) (hy : Function.Injective y) :
    Matrix.det (Matrix.of fun a b : Fin n => (X (y a, b) : MvPolynomial (ι × Fin n) R)) ≠ 0 := by
  have hg : Function.Injective (fun v : Fin n × Fin n => (y v.1, v.2)) := by
    intro a b h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (hy h.1) h.2
  have e : Matrix.det (Matrix.of fun a b : Fin n => (X (y a, b) : MvPolynomial (ι × Fin n) R)) =
      rename (fun v : Fin n × Fin n => (y v.1, v.2)) (genMat R n).det := by
    rw [AlgHom.map_det]
    congr 1
    ext a b
    simp [genMat]
  rw [e]
  exact fun h => genMat_det_ne_zero R n (rename_injective _ hg (by rw [h, map_zero]))

/- English proof (translation)
Use `set d := Matrix.det (Matrix.of fun a b : Fin n => (X (y a, b) : MvPolynomial (ι × Fin n) R)) with hd`. Establish `hc : ∀ m, ((twistSub LL S j d).coeff m) = LaurentPolynomial.C (algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n) (C (d.coeff m))) * LaurentPolynomial.T 1`. Introduce `m`. Rewrite using `[hd, twistSub_det LL S j y hy, mul_comm, coeff_C_mul, coeff_map, mul_comm]`. Both sides reduce to the same expression.

Establish `hM : Submonoid.powers (genMat R n).det ≤ nonZeroDivisors _` using `powers_le_nonZeroDivisors_of_noZeroDivisors (genMat_det_ne_zero R n)`. Establish `hne : ∀ m, d.coeff m ≠ 0 → algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n) (C (d.coeff m)) ≠ 0`. Introduce `m hm h`. Apply `hm` to reduce the goal to its premises. Use `IsLocalization.injective (GLCoord R n) hM (h.trans (map_zero _).symm)` as an intermediate fact.

Conclude with `MvPolynomial.C_injective _ _ (this.trans (map_zero _).symm)`. Take `⟨m0, hm0⟩` from `MvPolynomial.ne_zero_iff.mp (detX_ne_zero (R := R) y hinj)`. Rewrite using `[Finset.eq_singleton_iff_unique_mem]`. Prove the components needed by the constructor for the conclusion. Unfold `sDegs`.

Use `Finset.mem_biUnion.mpr ⟨m0, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[MvPolynomial.mem_support_iff, hc]`. Introduce `h`. Use `LaurentPolynomial.support_coeff_C_mul_T_of_ne_zero (hne m0 hm0) 1` as an intermediate fact. Rewrite `this` using `[h]`.

Simplify using `at this`. Rewrite using `[hc, LaurentPolynomial.support_coeff_C_mul_T_of_ne_zero (hne m0 hm0) 1]`. Simplify using the standard rewrite rules. Introduce `k hk`. Use `sDegs_subset LL S j d {1} (fun m => by rw [hc]; exact SuppIn.C_mul_T _ _ rfl) k hk` as an intermediate fact.

Conclude with `this`.
-/
theorem sDegs_det [IsDomain R] {ι : Type} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n) (y : Fin n → ι)
    (hinj : Function.Injective y) (hy : ∀ i, y i ∈ S ∧ LL.vec (y i) = true) :
    sDegs LL S j (Matrix.det (Matrix.of fun a b : Fin n => (X (y a, b) : MvPolynomial (ι × Fin n) R))) = {1} := by
  set d := Matrix.det (Matrix.of fun a b : Fin n => (X (y a, b) : MvPolynomial (ι × Fin n) R)) with hd
  have hc : ∀ m, ((twistSub LL S j d).coeff m) =
      LaurentPolynomial.C (algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n) (C (d.coeff m))) * LaurentPolynomial.T 1 := by
    intro m
    rw [hd, twistSub_det LL S j y hy, mul_comm, coeff_C_mul, coeff_map, mul_comm]
    rfl
  have hM : Submonoid.powers (genMat R n).det ≤ nonZeroDivisors _ :=
    powers_le_nonZeroDivisors_of_noZeroDivisors (genMat_det_ne_zero R n)
  have hne : ∀ m, d.coeff m ≠ 0 → algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n) (C (d.coeff m)) ≠ 0 := by
    intro m hm h
    apply hm
    have := IsLocalization.injective (GLCoord R n) hM (h.trans (map_zero _).symm)
    exact MvPolynomial.C_injective _ _ (this.trans (map_zero _).symm)
  obtain ⟨m0, hm0⟩ := MvPolynomial.ne_zero_iff.mp (detX_ne_zero (R := R) y hinj)
  rw [Finset.eq_singleton_iff_unique_mem]
  constructor
  · unfold sDegs
    refine Finset.mem_biUnion.mpr ⟨m0, ?_, ?_⟩
    · rw [MvPolynomial.mem_support_iff, hc]
      intro h
      have := LaurentPolynomial.support_coeff_C_mul_T_of_ne_zero (hne m0 hm0) 1
      rw [h] at this
      simp at this
    · rw [hc, LaurentPolynomial.support_coeff_C_mul_T_of_ne_zero (hne m0 hm0) 1]
      simp
  · intro k hk
    have := sDegs_subset LL S j d {1} (fun m => by rw [hc]; exact SuppIn.C_mul_T _ _ rfl) k hk
    exact this

end Coord

/- English proof (translation)
Assemble the required witnesses or components as `⟨valS_map _ (IsFractionRing.injective O (KK O)) LL S A, lowest_degree_map_of_injective _ (IsFractionRing.injective O (KK O)) LL S A⟩`.
-/
theorem valuation_lowest_degree_map_fraction_field (O : Type) [CommRing O] [IsDomain O] (ι : Type) (n : ℕ) [NeZero n] (LL : Letters ι)
    (S : Set ι) (A : MvPolynomial (ι × Fin n) O) :
    valS LL S (MvPolynomial.map (algebraMap O (KK O)) A) = valS LL S A ∧
      lam1S LL S (MvPolynomial.map (algebraMap O (KK O)) A) = lam1S LL S A :=
  ⟨valS_map _ (IsFractionRing.injective O (KK O)) LL S A, lowest_degree_map_of_injective _ (IsFractionRing.injective O (KK O)) LL S A⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun R _ ι κ f n _ LL S A hf => Formalism.MainNotions.SelectionLemmas.valuation_lowest_degree_rename R ι κ f n LL S A hf, fun O _ _ ι n _ LL S A => valuation_lowest_degree_map_fraction_field O ι n LL S A⟩`.
-/
theorem transport_statement_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.SelectionLemmas.TypeDecompositionsCommute D :=
  ⟨fun R _ ι κ f n _ LL S A hf => Formalism.MainNotions.SelectionLemmas.valuation_lowest_degree_rename R ι κ f n LL S A hf,
    fun O _ _ ι n _ LL S A => valuation_lowest_degree_map_fraction_field O ι n LL S A⟩

/- English proof (translation)
Take `⟨s, F₁, G₁, hF, hG⟩` from `exists_finset_rename₂ F G`. Set `t : Finset ι` to `s.image Prod.fst`. Set `e : {x // x ∈ s} → {x // x ∈ t} × Fin n` to `fun v => (⟨v.1.1, Finset.mem_image_of_mem _ v.2⟩, v.1.2)`. Use `⟨t, rename e F₁, rename e G₁, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[rename_rename, hF]`.

Both sides reduce to the same expression. Rewrite using `[rename_rename, hG]`. Both sides reduce to the same expression.
-/
theorem exists_finset_letters {R : Type} [CommRing R] {ι : Type} {n : ℕ} (F G : MvPolynomial (ι × Fin n) R) :
    ∃ (t : Finset ι) (F' G' : MvPolynomial ({x // x ∈ t} × Fin n) R),
      F = rename (fun v : {x // x ∈ t} × Fin n => ((v.1 : ι), v.2)) F' ∧
      G = rename (fun v : {x // x ∈ t} × Fin n => ((v.1 : ι), v.2)) G' := by
  classical
  obtain ⟨s, F₁, G₁, hF, hG⟩ := exists_finset_rename₂ F G
  let t : Finset ι := s.image Prod.fst
  let e : {x // x ∈ s} → {x // x ∈ t} × Fin n := fun v => (⟨v.1.1, Finset.mem_image_of_mem _ v.2⟩, v.1.2)
  refine ⟨t, rename e F₁, rename e G₁, ?_, ?_⟩
  · rw [rename_rename, hF]; rfl
  · rw [rename_rename, hG]; rfl

/- English proof (translation)
Introduce `O _ _ _ ι n _ LL S`. Use `⟨fun F G => ?_, fun l hl c => coord_clauses LL S l hl c, fun y hinj hy => ?_⟩` and prove the remaining obligations. Take `⟨t, F', G', rfl, rfl⟩` from `exists_finset_letters F G`. Establish `hf : Function.Injective (fun i : {x // x ∈ t} => (i : ι))` using `Subtype.val_injective`. Establish `T : ∀ A : MvPolynomial ({x // x ∈ t} × Fin n) O, valS LL S (rename (fun v : {x // x ∈ t} × Fin n => ((v.1 : ι), v.2)) A) = valS (⟨fun i : {x // x ∈ t} => LL.vec i⟩ : Letters {x // x ∈ t}) ((fun i : {x // x ∈ t} => (i : ι)) ⁻¹' S) (MvPolynomial.map (algebraMap O (KK O)) A) ∧ lam1S …`.

Introduce `A`. Establish `h1` using `Formalism.MainNotions.SelectionLemmas.valuation_lowest_degree_rename O {x // x ∈ t} ι (fun i : {x // x ∈ t} => (i : ι)) n LL S A hf`. Establish `h2` using `valuation_lowest_degree_map_fraction_field O {x // x ∈ t} n (⟨fun i : {x // x ∈ t} => LL.vec i⟩ : Letters {x // x ∈ t}) ((fun i : {x // x ∈ t} => (i : ι)) ⁻¹' S) A`. Conclude with `⟨h1.1.trans h2.1.symm, h1.2.trans h2.2.symm⟩`. Take `⟨v1, v2, v3, v4, -, -⟩` from `h (KK O) {x // x ∈ t} (⟨fun i : {x // x ∈ t} => LL.vec i⟩ : Letters {x // x ∈ t}) n ((fun i : {x // x ∈ t} => (i : ι)) ⁻¹' S)`.

Rewrite using `[← map_mul, ← map_add, (T _).1, (T _).1, (T _).1, (T _).1, (T _).2, (T _).2, (T _).2, (T _).2, map_mul, map_add]`. Conclude with `⟨v1 _ _, v2 _ _, v3 _ _, v4 _ _⟩`. Unfold `valS`. Rewrite using `[sDegs_det LL S _ y hinj hy]`. Both sides reduce to the same expression.
-/
theorem valuation_transport_of_lemma (D : Formalism.BasicNotions.D7) (h : Formalism.MainNotions.CovariantDegrees.ValuationsAdditive D) : Formalism.MainNotions.SelectionLemmas.admB2 D := by
  intro O _ _ _ ι n _ LL S
  refine ⟨fun F G => ?_, fun l hl c => coord_clauses LL S l hl c, fun y hinj hy => ?_⟩
  · obtain ⟨t, F', G', rfl, rfl⟩ := exists_finset_letters F G
    have hf : Function.Injective (fun i : {x // x ∈ t} => (i : ι)) := Subtype.val_injective
    have T : ∀ A : MvPolynomial ({x // x ∈ t} × Fin n) O,
        valS LL S (rename (fun v : {x // x ∈ t} × Fin n => ((v.1 : ι), v.2)) A) =
          valS (⟨fun i : {x // x ∈ t} => LL.vec i⟩ : Letters {x // x ∈ t}) ((fun i : {x // x ∈ t} => (i : ι)) ⁻¹' S)
            (MvPolynomial.map (algebraMap O (KK O)) A) ∧
        lam1S LL S (rename (fun v : {x // x ∈ t} × Fin n => ((v.1 : ι), v.2)) A) =
          lam1S (⟨fun i : {x // x ∈ t} => LL.vec i⟩ : Letters {x // x ∈ t}) ((fun i : {x // x ∈ t} => (i : ι)) ⁻¹' S)
            (MvPolynomial.map (algebraMap O (KK O)) A) := by
      intro A
      have h1 := Formalism.MainNotions.SelectionLemmas.valuation_lowest_degree_rename O {x // x ∈ t} ι (fun i : {x // x ∈ t} => (i : ι)) n LL S A hf
      have h2 := valuation_lowest_degree_map_fraction_field O {x // x ∈ t} n (⟨fun i : {x // x ∈ t} => LL.vec i⟩ : Letters {x // x ∈ t})
        ((fun i : {x // x ∈ t} => (i : ι)) ⁻¹' S) A
      exact ⟨h1.1.trans h2.1.symm, h1.2.trans h2.2.symm⟩
    obtain ⟨v1, v2, v3, v4, -, -⟩ := h (KK O) {x // x ∈ t} (⟨fun i : {x // x ∈ t} => LL.vec i⟩ : Letters {x // x ∈ t}) n
      ((fun i : {x // x ∈ t} => (i : ι)) ⁻¹' S)
    rw [← map_mul, ← map_add, (T _).1, (T _).1, (T _).1, (T _).1, (T _).2, (T _).2, (T _).2, (T _).2, map_mul, map_add]
    exact ⟨v1 _ _, v2 _ _, v3 _ _, v4 _ _⟩
  · unfold valS
    rw [sDegs_det LL S _ y hinj hy]
    rfl

section Hom

open Classical in

def suppProj (R : Type) [CommRing R] {σ : Type} (s : Set (σ →₀ ℕ)) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  (basisMonomials σ R).constr R fun m => if m ∈ s then monomial m 1 else 0

open Classical in
/- English proof (translation)
Establish `h : (monomial m a : MvPolynomial σ R) = a • basisMonomials σ R m`. Rewrite using `[coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[h, map_smul, suppProj, Module.Basis.constr_basis]`. Use `split_ifs`. Rewrite using `[coe_basisMonomials]`.

Rewrite using `[smul_zero]`.
-/
theorem suppProj_monomial (R : Type) [CommRing R] {σ : Type} (s : Set (σ →₀ ℕ)) (m : σ →₀ ℕ) (a : R) :
    suppProj R s (monomial m a) = if m ∈ s then monomial m a else 0 := by
  have h : (monomial m a : MvPolynomial σ R) = a • basisMonomials σ R m := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul, suppProj, Module.Basis.constr_basis]
  split_ifs
  · rw [coe_basisMonomials]
  · rw [smul_zero]

open Classical in
/- English proof (translation)
Proceed by induction on `A using MvPolynomial.induction_on' with`. Consider the case `monomial u a`. Rewrite using `[suppProj_monomial]`. Distinguish the cases in `hu : u ∈ s`. Rewrite using `[if_pos hu]`.

Distinguish the cases in `hm : m ∈ s`. Rewrite using `[if_pos hm]`. Rewrite using `[if_neg hm, coeff_monomial, if_neg]`. Introduce and unpack `rfl`. Conclude with `hm hu`.

Rewrite using `[if_neg hu, coeff_zero]`. Distinguish the cases in `hm : m ∈ s`. Rewrite using `[if_pos hm, coeff_monomial, if_neg]`. Introduce and unpack `rfl`. Conclude with `hu hm`.

Rewrite using `[if_neg hm]`. Consider the case `add p q hp hq`. Rewrite using `[map_add, coeff_add, hp, hq, coeff_add]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem coeff_suppProj (R : Type) [CommRing R] {σ : Type} (s : Set (σ →₀ ℕ)) (A : MvPolynomial σ R) (m : σ →₀ ℕ) :
    coeff m (suppProj R s A) = if m ∈ s then coeff m A else 0 := by
  induction A using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [suppProj_monomial]
    by_cases hu : u ∈ s
    · rw [if_pos hu]
      by_cases hm : m ∈ s
      · rw [if_pos hm]
      · rw [if_neg hm, coeff_monomial, if_neg]
        rintro rfl; exact hm hu
    · rw [if_neg hu, coeff_zero]
      by_cases hm : m ∈ s
      · rw [if_pos hm, coeff_monomial, if_neg]
        rintro rfl; exact hu hm
      · rw [if_neg hm]
  | add p q hp hq =>
    rw [map_add, coeff_add, hp, hq, coeff_add]
    split_ifs <;> simp

/- English proof (translation)
Introduce `m hm`. Rewrite `hm` using `[MvPolynomial.mem_support_iff, coeff_suppProj]`. Rewrite using `[MvPolynomial.mem_support_iff]`. Distinguish the cases in `h : m ∈ s`. Rewrite `hm` using `[if_pos h]`. Then use the resulting hypothesis.

Rewrite `hm` using `[if_neg h]`. Conclude with `absurd rfl hm`.
-/
theorem suppProj_support_subset (R : Type) [CommRing R] {σ : Type} (s : Set (σ →₀ ℕ)) (A : MvPolynomial σ R) :
    (suppProj R s A).support ⊆ A.support := by
  intro m hm
  rw [MvPolynomial.mem_support_iff, coeff_suppProj] at hm
  rw [MvPolynomial.mem_support_iff]
  by_cases h : m ∈ s
  · rwa [if_pos h] at hm
  · rw [if_neg h] at hm
    exact absurd rfl hm

/- English proof (translation)
Rewrite using `[MvPolynomial.mem_restrictSupport_iff]`. Introduce `m hm`. Rewrite `hm` using `[Finset.mem_coe, MvPolynomial.mem_support_iff, coeff_suppProj]`. Distinguish the cases in `h : m ∈ s`. Conclude with `h`.

Rewrite `hm` using `[if_neg h]`. Conclude with `absurd rfl hm`.
-/
theorem suppProj_mem (R : Type) [CommRing R] {σ : Type} (s : Set (σ →₀ ℕ)) (A : MvPolynomial σ R) :
    suppProj R s A ∈ restrictSupport R s := by
  rw [MvPolynomial.mem_restrictSupport_iff]
  intro m hm
  rw [Finset.mem_coe, MvPolynomial.mem_support_iff, coeff_suppProj] at hm
  by_cases h : m ∈ s
  · exact h
  · rw [if_neg h] at hm
    exact absurd rfl hm

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[coeff_suppProj]`. Distinguish the cases in `h : m ∈ s`. Rewrite using `[if_pos h]`. Rewrite using `[if_neg h]`.

Rewrite `hA` using `[MvPolynomial.mem_restrictSupport_iff]`. Assume the negation of the conclusion as `hc`. Conclude with `h (hA (by rw [Finset.mem_coe, MvPolynomial.mem_support_iff]; exact fun h0 => hc h0.symm))`.
-/
theorem suppProj_of_mem (R : Type) [CommRing R] {σ : Type} (s : Set (σ →₀ ℕ)) (A : MvPolynomial σ R)
    (hA : A ∈ restrictSupport R s) : suppProj R s A = A := by
  ext m
  rw [coeff_suppProj]
  by_cases h : m ∈ s
  · rw [if_pos h]
  · rw [if_neg h]
    rw [MvPolynomial.mem_restrictSupport_iff] at hA
    by_contra hc
    exact h (hA (by rw [Finset.mem_coe, MvPolynomial.mem_support_iff]; exact fun h0 => hc h0.symm))

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[coeff_suppProj, MvPolynomial.coeff_zero]`. Distinguish the cases in `h : m ∈ s`. Rewrite using `[if_pos h]`. Assume the negation of the conclusion as `hc`.

Rewrite `hA` using `[MvPolynomial.mem_restrictSupport_iff]`. Establish `hmt : m ∈ t` using `hA (by rw [Finset.mem_coe, MvPolynomial.mem_support_iff]; exact hc)`. Conclude with `Set.disjoint_left.mp hst h hmt`. Rewrite using `[if_neg h]`.
-/
theorem suppProj_of_disjoint (R : Type) [CommRing R] {σ : Type} (s t : Set (σ →₀ ℕ)) (A : MvPolynomial σ R)
    (hA : A ∈ restrictSupport R t) (hst : Disjoint s t) : suppProj R s A = 0 := by
  ext m
  rw [coeff_suppProj, MvPolynomial.coeff_zero]
  by_cases h : m ∈ s
  · rw [if_pos h]
    by_contra hc
    rw [MvPolynomial.mem_restrictSupport_iff] at hA
    have hmt : m ∈ t := hA (by rw [Finset.mem_coe, MvPolynomial.mem_support_iff]; exact hc)
    exact Set.disjoint_left.mp hst h hmt
  · rw [if_neg h]

/- English proof (translation)
Rewrite `hA`, the goal using `[MvPolynomial.mem_supported]`. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_coe, MvPolynomial.mem_vars]`. Take `⟨d, hd, hid⟩` from `hi`. Conclude with `hA (by rw [Finset.mem_coe, MvPolynomial.mem_vars]; exact ⟨d, suppProj_support_subset R s A hd, hid⟩)`.
-/
theorem suppProj_mem_supported (R : Type) [CommRing R] {σ : Type} (s : Set (σ →₀ ℕ)) (A : MvPolynomial σ R)
    (v : Set σ) (hA : A ∈ supported R v) : suppProj R s A ∈ supported R v := by
  rw [MvPolynomial.mem_supported] at hA ⊢
  intro i hi
  rw [Finset.mem_coe, MvPolynomial.mem_vars] at hi
  obtain ⟨d, hd, hid⟩ := hi
  exact hA (by rw [Finset.mem_coe, MvPolynomial.mem_vars]; exact ⟨d, suppProj_support_subset R s A hd, hid⟩)

def polComp (R : Type) [CommRing R] {ι : Type} (n : ℕ) (d : ι → ℕ) :
    MvPolynomial (ι × Fin n) R →ₗ[R] MvPolynomial (ι × Fin n) R :=
  suppProj R {m | ∀ i, multideg m i = d i}

/- English proof (translation)
Conclude with `suppProj_mem R _ A`.
-/
theorem polComp_mem_Pol (R : Type) [CommRing R] {ι : Type} (n : ℕ) (d : ι → ℕ) (A : MvPolynomial (ι × Fin n) R) :
    polComp R n d A ∈ Pol R n d := by
  exact suppProj_mem R _ A

/- English proof (translation)
Conclude with `suppProj_of_mem R _ A hA`.
-/
theorem polComp_of_mem (R : Type) [CommRing R] {ι : Type} (n : ℕ) (d : ι → ℕ) (A : MvPolynomial (ι × Fin n) R)
    (hA : A ∈ Pol R n d) : polComp R n d A = A := by
  exact suppProj_of_mem R _ A hA

/- English proof (translation)
Use `suppProj_of_disjoint R _ {m | ∀ i, multideg m i = d' i} A hA ?_` and prove the remaining obligations. Rewrite using `[Set.disjoint_left]`. Introduce `m h1 h2`. Establish `h1' : ∀ i, multideg m i = d i` using `h1`. Establish `h2' : ∀ i, multideg m i = d' i` using `h2`.

Conclude with `hd (funext fun i => (h1' i).symm.trans (h2' i))`.
-/
theorem polComp_of_ne (R : Type) [CommRing R] {ι : Type} (n : ℕ) (d d' : ι → ℕ) (A : MvPolynomial (ι × Fin n) R)
    (hA : A ∈ Pol R n d') (hd : d ≠ d') : polComp R n d A = 0 := by
  refine suppProj_of_disjoint R _ {m | ∀ i, multideg m i = d' i} A hA ?_
  rw [Set.disjoint_left]
  intro m h1 h2
  have h1' : ∀ i, multideg m i = d i := h1
  have h2' : ∀ i, multideg m i = d' i := h2
  exact hd (funext fun i => (h1' i).symm.trans (h2' i))

/- English proof (translation)
Conclude with `suppProj_mem_supported R _ A s hA`.
-/
theorem polComp_mem_supported (R : Type) [CommRing R] {ι : Type} (n : ℕ) (d : ι → ℕ)
    (A : MvPolynomial (ι × Fin n) R) (s : Set (ι × Fin n)) (hA : A ∈ supported R s) :
    polComp R n d A ∈ supported R s := by
  exact suppProj_mem_supported R _ A s hA

/- English proof (translation)
Unfold `multideg`. Simplify using `only [Finsupp.add_apply, Finset.sum_add_distrib]`.
-/
theorem hom_multideg_add {ι : Type} {n : ℕ} (a b : ι × Fin n →₀ ℕ) (i : ι) :
    multideg (a + b) i = multideg a i + multideg b i := by
  unfold multideg
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]

/- English proof (translation)
Unfold `Pol at *`. Rewrite `*` using `[mem_restrictSupport_iff]`. Introduce `m hm`. Take `⟨a, ha, b, hb, rfl⟩` from `Finset.mem_add.mp (support_mul P Q (by simpa using hm))`. Introduce `i`.

Rewrite using `[hom_multideg_add, hP (by simpa using ha) i, hQ (by simpa using hb) i]`. Both sides reduce to the same expression.
-/
theorem hom_Pol_mul (R : Type) [CommRing R] {ι : Type} {n : ℕ} {d d' : ι → ℕ} {P Q : MvPolynomial (ι × Fin n) R}
    (hP : P ∈ Pol R n d) (hQ : Q ∈ Pol R n d') : P * Q ∈ Pol R n (d + d') := by
  classical
  unfold Pol at *
  rw [mem_restrictSupport_iff] at *
  intro m hm
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (support_mul P Q (by simpa using hm))
  intro i
  rw [hom_multideg_add, hP (by simpa using ha) i, hQ (by simpa using hb) i]
  rfl

/- English proof (translation)
Unfold `Pol`. Rewrite using `[mem_restrictSupport_iff]`. Introduce `m hm`. Establish `hm' : coeff m (C a : MvPolynomial (ι × Fin n) R) ≠ 0` using `mem_support_iff.mp (by simpa using hm)`. Rewrite `hm'` using `[coeff_C]`.

Establish `h0 : (0 : ι × Fin n →₀ ℕ) = m`. Assume the negation of the conclusion as `h`. Conclude with `hm' (if_neg h)`. Introduce `i`. Rewrite using `[← h0]`.

Simplify using `[multideg]`.
-/
theorem hom_Pol_C (R : Type) [CommRing R] {ι : Type} {n : ℕ} (a : R) :
    (C a : MvPolynomial (ι × Fin n) R) ∈ Pol R n (0 : ι → ℕ) := by
  classical
  unfold Pol
  rw [mem_restrictSupport_iff]
  intro m hm
  have hm' : coeff m (C a : MvPolynomial (ι × Fin n) R) ≠ 0 := mem_support_iff.mp (by simpa using hm)
  rw [coeff_C] at hm'
  have h0 : (0 : ι × Fin n →₀ ℕ) = m := by
    by_contra h
    exact hm' (if_neg h)
  intro i
  rw [← h0]
  simp [multideg]

open Classical in
/- English proof (translation)
Unfold `Pol`. Rewrite using `[mem_restrictSupport_iff]`. Introduce `m hm`. Establish `hm' : coeff m (C a * X (l, c) : MvPolynomial (ι × Fin n) R) ≠ 0` using `mem_support_iff.mp (by simpa using hm)`. Rewrite `hm'` using `[coeff_C_mul, coeff_X]`.

Establish `h0 : Finsupp.single (l, c) 1 = m`. Assume the negation of the conclusion as `h`. Rewrite `hm'` using `[if_neg h, mul_zero]`. Conclude with `hm' rfl`. Introduce `i`.

Rewrite using `[← h0]`. Unfold `multideg`. Distinguish the cases in `hi : i = l`. Substitute `hi` using the available equality. Simplify using `[Finsupp.single_apply]`.

Simplify using `[hi]`.
-/
theorem hom_Pol_CX (R : Type) [CommRing R] {ι : Type} {n : ℕ} (a : R) (l : ι) (c : Fin n) :
    (C a * X (l, c) : MvPolynomial (ι × Fin n) R) ∈ Pol R n (fun i => if i = l then 1 else 0) := by
  unfold Pol
  rw [mem_restrictSupport_iff]
  intro m hm
  have hm' : coeff m (C a * X (l, c) : MvPolynomial (ι × Fin n) R) ≠ 0 := mem_support_iff.mp (by simpa using hm)
  rw [coeff_C_mul, coeff_X] at hm'
  have h0 : Finsupp.single (l, c) 1 = m := by
    by_contra h
    rw [if_neg h, mul_zero] at hm'
    exact hm' rfl
  intro i
  rw [← h0]
  unfold multideg
  by_cases hi : i = l
  · subst hi
    simp [Finsupp.single_apply]
  · simp [hi]

open Classical in
/- English proof (translation)
Simplify using `only [twistSub, eval₂Hom_X']`. Use `split_ifs`. Conclude with `Submodule.sum_mem _ fun b _ => hom_Pol_CX _ _ _ _`. Conclude with `Submodule.sum_mem _ fun b _ => hom_Pol_CX _ _ _ _`. Use `hom_Pol_CX (GLLaurent R n) (ι := ι) (n := n) 1 v.1 v.2` as an intermediate fact.

Rewrite `this` using `[C_1, one_mul]`. Then use the resulting hypothesis.
-/
theorem hom_twistSub_X_mem {R : Type} [CommRing R] {ι : Type} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    (v : ι × Fin n) : twistSub LL S j (X v : MvPolynomial (ι × Fin n) R) ∈
      Pol (GLLaurent R n) n (fun i => if i = v.1 then 1 else 0) := by
  simp only [twistSub, eval₂Hom_X']
  split_ifs
  · exact Submodule.sum_mem _ fun b _ => hom_Pol_CX _ _ _ _
  · exact Submodule.sum_mem _ fun b _ => hom_Pol_CX _ _ _ _
  · have := hom_Pol_CX (GLLaurent R n) (ι := ι) (n := n) 1 v.1 v.2
    rwa [C_1, one_mul] at this

/- English proof (translation)
Use `MvPolynomial.induction_on_monomial (motive := fun p => ∃ d : ι → ℕ, p ∈ Pol R n d ∧ twistSub LL S j p ∈ Pol (GLLaurent R n) n d) ?_ ?_ m a` and prove the remaining obligations. Introduce `a`. Use `⟨0, hom_Pol_C R a, ?_⟩` and prove the remaining obligations. Establish `: twistSub LL S j (C a : MvPolynomial (ι × Fin n) R) = C (coefL R n a)` using `by simp [twistSub]`. Rewrite using `[this]`.

Conclude with `hom_Pol_C _ _`. Introduce and unpack `p v ⟨d, h1, h2⟩`. Use `⟨d + fun i => if i = v.1 then 1 else 0, hom_Pol_mul R h1 ?_, ?_⟩` and prove the remaining obligations. Use `hom_Pol_CX R (ι := ι) (n := n) 1 v.1 v.2` as an intermediate fact. Rewrite `this` using `[C_1, one_mul]`. Then use the resulting hypothesis.

Rewrite using `[map_mul]`. Conclude with `hom_Pol_mul _ h2 (hom_twistSub_X_mem LL S j v)`.
-/
theorem hom_twistSub_monomial {R : Type} [CommRing R] {ι : Type} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    (m : ι × Fin n →₀ ℕ) (a : R) :
    ∃ d : ι → ℕ, (monomial m a : MvPolynomial (ι × Fin n) R) ∈ Pol R n d ∧
      twistSub LL S j (monomial m a) ∈ Pol (GLLaurent R n) n d := by
  classical
  refine MvPolynomial.induction_on_monomial
    (motive := fun p => ∃ d : ι → ℕ, p ∈ Pol R n d ∧ twistSub LL S j p ∈ Pol (GLLaurent R n) n d) ?_ ?_ m a
  · intro a
    refine ⟨0, hom_Pol_C R a, ?_⟩
    have : twistSub LL S j (C a : MvPolynomial (ι × Fin n) R) = C (coefL R n a) := by simp [twistSub]
    rw [this]
    exact hom_Pol_C _ _
  · rintro p v ⟨d, h1, h2⟩
    refine ⟨d + fun i => if i = v.1 then 1 else 0, hom_Pol_mul R h1 ?_, ?_⟩
    · have := hom_Pol_CX R (ι := ι) (n := n) 1 v.1 v.2
      rwa [C_1, one_mul] at this
    · rw [map_mul]
      exact hom_Pol_mul _ h2 (hom_twistSub_X_mem LL S j v)

/- English proof (translation)
Distinguish the cases in `ha : a = 0`. Rewrite using `[ha, monomial_zero, map_zero]`. Conclude with `Submodule.zero_mem _`. Take `⟨d, h1, h2⟩` from `hom_twistSub_monomial LL S j m a`. Unfold `Pol at h1`.

Rewrite `h1` using `[monomial_mem_restrictSupport]`. Break down `h1 with h1 | h1` into its components or cases. Establish `: (fun i => multideg m i) = d` using `funext h1`. Rewrite using `[this]` and apply the resulting hypothesis. Conclude with `absurd h1 ha`.
-/
theorem hom_twistSub_monomial' {R : Type} [CommRing R] {ι : Type} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    (m : ι × Fin n →₀ ℕ) (a : R) :
    twistSub LL S j (monomial m a) ∈ Pol (GLLaurent R n) n (fun i => multideg m i) := by
  by_cases ha : a = 0
  · rw [ha, monomial_zero, map_zero]; exact Submodule.zero_mem _
  · obtain ⟨d, h1, h2⟩ := hom_twistSub_monomial LL S j m a
    unfold Pol at h1
    rw [monomial_mem_restrictSupport] at h1
    rcases h1 with h1 | h1
    · have : (fun i => multideg m i) = d := funext h1
      rwa [this]
    · exact absurd h1 ha

/- English proof (translation)
Rewrite using `[← support_sum_monomial_coeff A, map_sum]`. Use `Submodule.sum_mem _ fun m hm => ?_` and prove the remaining obligations. Establish `hd : (fun i => multideg m i) = d`. Unfold `Pol at hA`. Rewrite `hA` using `[mem_restrictSupport_iff]`.

Conclude with `funext (hA (by simpa using hm))`. Rewrite using `[← hd]`. Conclude with `hom_twistSub_monomial' LL S j m _`.
-/
theorem twistSub_mem_Pol {R : Type} [CommRing R] {ι : Type} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    (d : ι → ℕ) (A : MvPolynomial (ι × Fin n) R) (hA : A ∈ Pol R n d) :
    twistSub LL S j A ∈ Pol (GLLaurent R n) n d := by
  rw [← support_sum_monomial_coeff A, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hd : (fun i => multideg m i) = d := by
    unfold Pol at hA
    rw [mem_restrictSupport_iff] at hA
    exact funext (hA (by simpa using hm))
  rw [← hd]
  exact hom_twistSub_monomial' LL S j m _

/- English proof (translation)
Proceed by induction on `A using MvPolynomial.induction_on' with`. Consider the case `monomial m a`. Establish `hm : (monomial m a : MvPolynomial (ι × Fin n) R) ∈ Pol R n (fun i => multideg m i)`. Unfold `Pol`. Rewrite using `[monomial_mem_restrictSupport]`.

Conclude with `Or.inl fun i => rfl`. Distinguish the cases in `hd : d = fun i => multideg m i`. Rewrite using `[hd, polComp_of_mem R n _ _ hm, polComp_of_mem _ n _ _ (hom_twistSub_monomial' LL S j m a)]`. Rewrite using `[polComp_of_ne R n _ _ _ hm hd, polComp_of_ne _ n _ _ _ (hom_twistSub_monomial' LL S j m a) hd, map_zero]`. Consider the case `add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]`.
-/
theorem twistSub_polComp {R : Type} [CommRing R] {ι : Type} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    (d : ι → ℕ) (A : MvPolynomial (ι × Fin n) R) :
    twistSub LL S j (polComp R n d A) = polComp (GLLaurent R n) n d (twistSub LL S j A) := by
  classical
  induction A using MvPolynomial.induction_on' with
  | monomial m a =>
    have hm : (monomial m a : MvPolynomial (ι × Fin n) R) ∈ Pol R n (fun i => multideg m i) := by
      unfold Pol
      rw [monomial_mem_restrictSupport]
      exact Or.inl fun i => rfl
    by_cases hd : d = fun i => multideg m i
    · rw [hd, polComp_of_mem R n _ _ hm, polComp_of_mem _ n _ _ (hom_twistSub_monomial' LL S j m a)]
    · rw [polComp_of_ne R n _ _ _ hm hd, polComp_of_ne _ n _ _ _ (hom_twistSub_monomial' LL S j m a) hd, map_zero]
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]

/- English proof (translation)
Introduce `k hk`. Unfold `sDegs at hk ⊢`. Take `⟨m, hm, hmk⟩` from `Finset.mem_biUnion.mp hk`. Rewrite `hm`, `hmk` using `[twistSub_polComp]`. Establish `hc : coeff m (polComp (GLLaurent R n) n d (twistSub LL S j A)) = coeff m (twistSub LL S j A)`.

Establish `h0` using `mem_support_iff.mp hm`. Unfold `polComp at h0 ⊢`. Rewrite `h0`, the goal using `[coeff_suppProj]`. Use `split_ifs at h0 ⊢ with h`. Both sides reduce to the same expression.

Conclude with `absurd rfl h0`. Use `Finset.mem_biUnion.mpr ⟨m, suppProj_support_subset _ _ _ hm, ?_⟩` and prove the remaining obligations. Rewrite `hmk` using `[hc]`. Then use the resulting hypothesis.
-/
theorem sDegs_polComp_subset {R : Type} [CommRing R] {ι : Type} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    (d : ι → ℕ) (A : MvPolynomial (ι × Fin n) R) : sDegs LL S j (polComp R n d A) ⊆ sDegs LL S j A := by
  classical
  intro k hk
  unfold sDegs at hk ⊢
  obtain ⟨m, hm, hmk⟩ := Finset.mem_biUnion.mp hk
  rw [twistSub_polComp] at hm hmk
  have hc : coeff m (polComp (GLLaurent R n) n d (twistSub LL S j A)) = coeff m (twistSub LL S j A) := by
    have h0 := mem_support_iff.mp hm
    unfold polComp at h0 ⊢
    rw [coeff_suppProj] at h0 ⊢
    split_ifs at h0 ⊢ with h
    · rfl
    · exact absurd rfl h0
  refine Finset.mem_biUnion.mpr ⟨m, suppProj_support_subset _ _ _ hm, ?_⟩
  rwa [hc] at hmk

/- English proof (translation)
Unfold `valS`. Conclude with `Finset.inf_mono (sDegs_polComp_subset LL S (lastIdx n) d A)`.
-/
theorem valS_le_polComp {R : Type} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (d : ι → ℕ) (A : MvPolynomial (ι × Fin n) R) : valS LL S A ≤ valS LL S (polComp R n d A) := by
  unfold valS
  exact Finset.inf_mono (sDegs_polComp_subset LL S (lastIdx n) d A)

/- English proof (translation)
Unfold `lam1S`. Conclude with `Finset.sup_mono (sDegs_polComp_subset LL S 0 d A)`.
-/
theorem lowest_degree_compose_le {R : Type} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (d : ι → ℕ) (A : MvPolynomial (ι × Fin n) R) : lam1S LL S (polComp R n d A) ≤ lam1S LL S A := by
  unfold lam1S
  exact Finset.sup_mono (sDegs_polComp_subset LL S 0 d A)

/- English proof (translation)
Use `⟨A.support.image fun m i => multideg m i, ?_⟩` and prove the remaining obligations. Use extensionality with `m`. Rewrite using `[coeff_sum]`. Establish `h : ∀ d : ι → ℕ, coeff m (polComp R n d A) = if (fun i => multideg m i) = d then coeff m A else 0`. Introduce `d`.

Unfold `polComp`. Rewrite using `[coeff_suppProj]`. Use `if_congr ?_ rfl rfl` and prove the remaining obligations. Conclude with `⟨fun h => funext h, fun h i => congrFun h i⟩`. Simplify using `only [h]`.

Rewrite using `[Finset.sum_ite_eq]`. Use `split_ifs with hm`. Both sides reduce to the same expression. Assume the negation of the conclusion as `hne`. Conclude with `hm (Finset.mem_image_of_mem _ (mem_support_iff.mpr hne))`.
-/
theorem exists_sum_polComp (R : Type) [CommRing R] {ι : Type} (n : ℕ) (A : MvPolynomial (ι × Fin n) R) :
    ∃ T : Finset (ι → ℕ), A = ∑ d ∈ T, polComp R n d A := by
  classical
  refine ⟨A.support.image fun m i => multideg m i, ?_⟩
  ext m
  rw [coeff_sum]
  have h : ∀ d : ι → ℕ, coeff m (polComp R n d A) = if (fun i => multideg m i) = d then coeff m A else 0 := by
    intro d
    unfold polComp
    rw [coeff_suppProj]
    refine if_congr ?_ rfl rfl
    exact ⟨fun h => funext h, fun h i => congrFun h i⟩
  simp only [h]
  rw [Finset.sum_ite_eq]
  split_ifs with hm
  · rfl
  · by_contra hne
    exact hm (Finset.mem_image_of_mem _ (mem_support_iff.mpr hne))

end Hom

section SegT

open Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.CovariantDegrees

variable {n' r : ℕ} [NeZero n'] (F : Frames n' r) (j : ℤ)

/- English proof (translation)
Introduce `a b h`. Conclude with `((F.letters j).orderIsoOfFin rfl).strictMono h`.
-/
theorem segE_strictMono : StrictMono (segE F j) := by
  intro a b h
  exact ((F.letters j).orderIsoOfFin rfl).strictMono h

/- English proof (translation)
The claim follows from `((F.letters j).orderIsoOfFin rfl i).2`.
-/
theorem segE_mem (i : Fin (segN F j)) : segE F j i ∈ F.letters j := ((F.letters j).orderIsoOfFin rfl i).2

/- English proof (translation)
Assemble the required witnesses or components as `⟨((F.letters j).orderIsoOfFin rfl).symm ⟨x, hx⟩, by simp [segE]⟩`.
-/
theorem segE_surj {x : ℤ} (hx : x ∈ F.letters j) : ∃ i, segE F j i = x :=
  ⟨((F.letters j).orderIsoOfFin rfl).symm ⟨x, hx⟩, by simp [segE]⟩

/- English proof (translation)
Introduce `a b h`. Simplify using `only [Prod.mk.injEq] at h`. Conclude with `Prod.ext ((segE_strictMono F j).injective h.1) h.2`.
-/
theorem segVar_injective (n : ℕ) : Function.Injective (fun v : Fin (segN F j) × Fin n => (segE F j v.1, v.2)) := by
  intro a b h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext ((segE_strictMono F j).injective h.1) h.2

/- English proof (translation)
Take `⟨q, hq⟩` from `exists_rename_eq_of_vars_subset_range A _ (segVar_injective F j n) (by`. Introduce `v hv`. Take `⟨i, hi⟩` from `segE_surj F j ((mem_supported.mp hA) hv)`. Conclude with `⟨(i, v.2), by simp [hi]⟩)`. Conclude with `⟨q, hq.symm⟩`.
-/
theorem exists_segRen {R : Type} [CommRing R] {n : ℕ} (A : MvPolynomial (ℤ × Fin n) R)
    (hA : A ∈ supported R {v : ℤ × Fin n | v.1 ∈ F.letters j}) : ∃ A₀, A = segRen F j R n A₀ := by
  obtain ⟨q, hq⟩ := exists_rename_eq_of_vars_subset_range A _ (segVar_injective F j n) (by
    intro v hv
    obtain ⟨i, hi⟩ := segE_surj F j ((mem_supported.mp hA) hv)
    exact ⟨(i, v.2), by simp [hi]⟩)
  exact ⟨q, hq.symm⟩

def pre {N : ℕ} (i : Fin (N + 1)) : Set (Fin N) := {k | k.val < i.val}

/- English proof (translation)
Use extensionality with `k`. Use `show k.val < i.val + 1 ↔ k.val ≤ i.val`. Use linear arithmetic over natural numbers and integers.
-/
theorem pre_succ {N : ℕ} (i : Fin N) : pre i.succ = {k : Fin N | k ≤ i} := by
  ext k
  show k.val < i.val + 1 ↔ k.val ≤ i.val
  omega

/- English proof (translation)
Use extensionality with `k`. Conclude with `Iff.rfl`.
-/
theorem pre_castSucc {N : ℕ} (i : Fin N) : pre i.castSucc = {k : Fin N | k < i} := by
  ext k
  exact Iff.rfl

/- English proof (translation)
Use extensionality with `k`. Simplify using `[pre]`.
-/
theorem pre_zero {N : ℕ} : pre (0 : Fin (N + 1)) = (∅ : Set (Fin N)) := by
  ext k; simp [pre]

/- English proof (translation)
Establish `h1 : (segE F j) ⁻¹' {y | y ≤ segE F j i} = pre i.succ`. Rewrite using `[pre_succ]`. Use extensionality with `k`. Simplify using `[(segE_strictMono F j).le_iff_le]`. Establish `h2 : (segE F j) ⁻¹' {y | y < segE F j i} = pre i.castSucc`.

Rewrite using `[pre_castSucc]`. Use extensionality with `k`. Simplify using `[(segE_strictMono F j).lt_iff_lt]`. Establish `a1` using `valuation_lowest_degree_rename R _ ℤ (segE F j) n LZ {y | y ≤ segE F j i} A₀ (segE_strictMono F j).injective`. Establish `a2` using `valuation_lowest_degree_rename R _ ℤ (segE F j) n LZ {y | y < segE F j i} A₀ (segE_strictMono F j).injective`.

Rewrite `a1` using `[h1]`. Rewrite `a2` using `[h2]`. Conclude with `⟨a1.1, a2.1, a1.2, a2.2⟩`.
-/
theorem seg_val {R : Type} [CommRing R] {n : ℕ} [NeZero n] (A₀ : MvPolynomial (Fin (segN F j) × Fin n) R)
    (i : Fin (segN F j)) :
    valS LZ {y | y ≤ segE F j i} (segRen F j R n A₀) = valS (segLL F j) (pre i.succ) A₀ ∧
    valS LZ {y | y < segE F j i} (segRen F j R n A₀) = valS (segLL F j) (pre i.castSucc) A₀ ∧
    lam1S LZ {y | y ≤ segE F j i} (segRen F j R n A₀) = lam1S (segLL F j) (pre i.succ) A₀ ∧
    lam1S LZ {y | y < segE F j i} (segRen F j R n A₀) = lam1S (segLL F j) (pre i.castSucc) A₀ := by
  have h1 : (segE F j) ⁻¹' {y | y ≤ segE F j i} = pre i.succ := by
    rw [pre_succ]; ext k; simp [(segE_strictMono F j).le_iff_le]
  have h2 : (segE F j) ⁻¹' {y | y < segE F j i} = pre i.castSucc := by
    rw [pre_castSucc]; ext k; simp [(segE_strictMono F j).lt_iff_lt]
  have a1 := valuation_lowest_degree_rename R _ ℤ (segE F j) n LZ {y | y ≤ segE F j i} A₀ (segE_strictMono F j).injective
  have a2 := valuation_lowest_degree_rename R _ ℤ (segE F j) n LZ {y | y < segE F j i} A₀ (segE_strictMono F j).injective
  rw [h1] at a1
  rw [h2] at a2
  exact ⟨a1.1, a2.1, a1.2, a2.2⟩

/- English proof (translation)
Simplify using `only [segRen, plEmb, nmEmb, map_mul, rename_rename]`. Both sides reduce to the same expression.
-/
theorem segRen_mul {R : Type} [CommRing R] {K : ℕ} (a : MvPolynomial (Fin (segN F j) × Fin r) R)
    (g : MvPolynomial (Fin (segN F j) × Fin K) R) :
    segRen F j R (r + K) (rename (plVar (K := K)) a * rename (tanVar (r := r)) g) =
      plEmb R r K (segRen F j R r a) * nmEmb R r K (segRen F j R K g) := by
  simp only [segRen, plEmb, nmEmb, map_mul, rename_rename]
  rfl

end SegT

section Empty

variable {R : Type} [CommRing R]

/- English proof (translation)
Proceed by induction on `A using MvPolynomial.induction_on with`. Consider the case `C a => simp [twistSub]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p v hp`. Simplify using `only [map_mul, hp, map_X]`.

Use `congr 1`. Simplify using `[twistSub]`.
-/
theorem twistSub_empty {ι : Type} {n : ℕ} (LL : Letters ι) (j : Fin n) (A : MvPolynomial (ι × Fin n) R) :
    twistSub LL ∅ j A = MvPolynomial.map (coefL R n) A := by
  induction A using MvPolynomial.induction_on with
  | C a => simp [twistSub]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp [twistSub]

/- English proof (translation)
Use `sDegs_subset LL ∅ j A _ fun m => ?_` and prove the remaining obligations. Rewrite using `[twistSub_empty, coeff_map]`. Establish `: coefL R n (coeff m A) = LaurentPolynomial.C (algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n) (C (coeff m A))) * LaurentPolynomial.T 0`. Rewrite using `[LaurentPolynomial.T_zero, mul_one]`. Both sides reduce to the same expression.

Rewrite using `[this]`. Conclude with `SuppIn.C_mul_T _ _ rfl`.
-/
theorem sDegs_empty_subset {ι : Type} {n : ℕ} (LL : Letters ι) (j : Fin n) (A : MvPolynomial (ι × Fin n) R) :
    ∀ k ∈ sDegs LL ∅ j A, k ∈ ({0} : Set ℤ) := by
  refine sDegs_subset LL ∅ j A _ fun m => ?_
  rw [twistSub_empty, coeff_map]
  have : coefL R n (coeff m A) = LaurentPolynomial.C (algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n)
      (C (coeff m A))) * LaurentPolynomial.T 0 := by
    rw [LaurentPolynomial.T_zero, mul_one]; rfl
  rw [this]
  exact SuppIn.C_mul_T _ _ rfl

/- English proof (translation)
Rewrite using `[Finset.eq_singleton_iff_unique_mem]`. Use `⟨?_, fun k hk => sDegs_empty_subset LL j A k hk⟩` and prove the remaining obligations. Take `⟨m0, hm0⟩` from `MvPolynomial.ne_zero_iff.mp hA`. Establish `hne : coefL R n (coeff m0 A) ≠ 0` using `fun h => hm0 (coefL_injective n (h.trans (map_zero _).symm))`. Unfold `sDegs`.

Rewrite using `[twistSub_empty]`. Use `Finset.mem_biUnion.mpr ⟨m0, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[MvPolynomial.mem_support_iff, coeff_map]`. Conclude with `hne`. Rewrite using `[coeff_map, Finsupp.mem_support_iff]`.

Introduce `h0`. Apply `hm0` to reduce the goal to its premises. Establish `hM : Submonoid.powers (genMat R n).det ≤ nonZeroDivisors _` using `powers_le_nonZeroDivisors_of_noZeroDivisors (genMat_det_ne_zero R n)`. Simplify using `only [coefL, RingHom.comp_apply, LaurentPolynomial.C_apply, if_true] at h0`. Conclude with `MvPolynomial.C_injective _ _ ((IsLocalization.injective (GLCoord R n) hM (h0.trans (map_zero _).symm)).trans (map_zero _).symm)`.
-/
theorem sDegs_empty [IsDomain R] {ι : Type} {n : ℕ} (LL : Letters ι) (j : Fin n) (A : MvPolynomial (ι × Fin n) R)
    (hA : A ≠ 0) : sDegs LL ∅ j A = {0} := by
  rw [Finset.eq_singleton_iff_unique_mem]
  refine ⟨?_, fun k hk => sDegs_empty_subset LL j A k hk⟩
  obtain ⟨m0, hm0⟩ := MvPolynomial.ne_zero_iff.mp hA
  have hne : coefL R n (coeff m0 A) ≠ 0 := fun h => hm0 (coefL_injective n (h.trans (map_zero _).symm))
  unfold sDegs
  rw [twistSub_empty]
  refine Finset.mem_biUnion.mpr ⟨m0, ?_, ?_⟩
  · rw [MvPolynomial.mem_support_iff, coeff_map]; exact hne
  · rw [coeff_map, Finsupp.mem_support_iff]
    intro h0
    apply hm0
    have hM : Submonoid.powers (genMat R n).det ≤ nonZeroDivisors _ :=
      powers_le_nonZeroDivisors_of_noZeroDivisors (genMat_det_ne_zero R n)
    simp only [coefL, RingHom.comp_apply, LaurentPolynomial.C_apply, if_true] at h0
    exact MvPolynomial.C_injective _ _ ((IsLocalization.injective (GLCoord R n) hM (h0.trans (map_zero _).symm)).trans
      (map_zero _).symm)

end Empty

section A3

open Formalism.MainNotions.CovariantDegrees

variable {R : Type} [CommRing R]

/- English proof (translation)
Proceed by induction on `v using WithTop.recTopCoe with`. Consider the case `top`. Take `⟨t, ht⟩` from `Bv.exists_le`. Conclude with `⟨t, le_top, fun X hX _ => ht X hX⟩`. Consider the case `coe z => exact ⟨z, le_rfl, fun X _ h => WithTop.coe_le_coe.mp h⟩`.
-/
theorem exists_thr_top (v : WithTop ℤ) (Bv : Finset ℤ) :
    ∃ t : ℤ, (t : WithTop ℤ) ≤ v ∧ ∀ X ∈ Bv, (X : WithTop ℤ) ≤ v → X ≤ t := by
  induction v using WithTop.recTopCoe with
  | top =>
    obtain ⟨t, ht⟩ := Bv.exists_le
    exact ⟨t, le_top, fun X hX _ => ht X hX⟩
  | coe z => exact ⟨z, le_rfl, fun X _ h => WithTop.coe_le_coe.mp h⟩

/- English proof (translation)
Proceed by induction on `v using WithBot.recBotCoe with`. Consider the case `bot`. Take `⟨t, ht⟩` from `(Bl.image (fun x => -x)).exists_le`. Conclude with `⟨-t, bot_le, fun X hX _ => by`. Use `ht (-X) (Finset.mem_image_of_mem _ hX)` as an intermediate fact.

Use the proof step `omega⟩`. Consider the case `coe z => exact ⟨z, le_rfl, fun X _ h => WithBot.coe_le_coe.mp h⟩`.
-/
theorem exists_thr_bot (v : WithBot ℤ) (Bl : Finset ℤ) :
    ∃ t : ℤ, v ≤ (t : WithBot ℤ) ∧ ∀ X ∈ Bl, v ≤ (X : WithBot ℤ) → t ≤ X := by
  induction v using WithBot.recBotCoe with
  | bot =>
    obtain ⟨t, ht⟩ := (Bl.image (fun x => -x)).exists_le
    exact ⟨-t, bot_le, fun X hX _ => by
      have := ht (-X) (Finset.mem_image_of_mem _ hX)
      omega⟩
  | coe z => exact ⟨z, le_rfl, fun X _ h => WithBot.coe_le_coe.mp h⟩

/- English proof (translation)
Distinguish the cases in `h0 : A = 0`. Rewrite using `[h0]`. Conclude with `Submodule.zero_mem _`. Use `choose th hth using fun k : Fin N => exists_thr_top (valS LL {i | i ≤ k} A) Bv`. Use `choose M hM using fun k : Fin N => exists_thr_bot (lam1S LL {i | i ≤ k} A) Bl`.

Establish `hmem : A ∈ {G : MvPolynomial (Fin N × Fin n) R | G ∈ Pol R n B ∧ ∀ i : Fin N, ((th i : ℤ) : WithTop ℤ) ≤ valS LL {j | j ≤ i} G ∧ lam1S LL {j | j ≤ i} G ≤ ((M i : ℤ) : WithBot ℤ)}` using `⟨hA, fun i => ⟨(hth i).1, (hM i).1⟩⟩`. Rewrite `hmem` using `[hA3 th M]`. Use `Submodule.span_mono ?_ hmem` and prove the remaining obligations. Introduce and unpack `G ⟨P, I, hI, hc, rfl⟩`. Use `⟨P, I, hI, fun i => ?_, rfl⟩` and prove the remaining obligations.

Proceed by induction on `i using Fin.cases with`. Consider the case `zero`. Rewrite using `[pre_zero, P.zero]`. Prove the components needed by the constructor for the conclusion. Introduce `X _ hX`.

Unfold `valS at hX`. Rewrite `hX` using `[sDegs_empty LL _ A h0]`. Simplify using `using hX`. Introduce `Y _ hY`. Unfold `lam1S at hY`.

Rewrite `hY` using `[sDegs_empty LL _ A h0]`. Simplify using `using hY`. Consider the case `succ k`. Rewrite using `[pre_succ]`. Conclude with `⟨fun X hX h => ((hth k).2 X hX h).trans (hc k).1, fun Y hY h => (hc k).2.trans ((hM k).2 Y hY h)⟩`.
-/
theorem mem_span_standard_of_bounds [IsDomain R] {N n : ℕ} [NeZero n] (LL : Letters (Fin N)) (B : Fin N → ℕ)
    (hA3 : ∀ th M : Fin N → ℤ, A3at R N n LL B th M) (A : MvPolynomial (Fin N × Fin n) R) (hA : A ∈ Pol R n B)
    (Bv Bl : Finset ℤ) :
    A ∈ Submodule.span R {G | ∃ P : PPath n N LL B, ∃ I : ℤ → Finset (Fin n), IsSt P.mu I ∧
      (∀ i : Fin (N + 1), (∀ X ∈ Bv, (X : WithTop ℤ) ≤ valS LL (pre i) A → X ≤ P.mu i (lastIdx n)) ∧
        (∀ Y ∈ Bl, lam1S LL (pre i) A ≤ (Y : WithBot ℤ) → P.mu i 0 ≤ Y)) ∧ G = Psi R P.mu I} := by
  by_cases h0 : A = 0
  · rw [h0]; exact Submodule.zero_mem _
  choose th hth using fun k : Fin N => exists_thr_top (valS LL {i | i ≤ k} A) Bv
  choose M hM using fun k : Fin N => exists_thr_bot (lam1S LL {i | i ≤ k} A) Bl
  have hmem : A ∈ {G : MvPolynomial (Fin N × Fin n) R | G ∈ Pol R n B ∧ ∀ i : Fin N,
      ((th i : ℤ) : WithTop ℤ) ≤ valS LL {j | j ≤ i} G ∧ lam1S LL {j | j ≤ i} G ≤ ((M i : ℤ) : WithBot ℤ)} :=
    ⟨hA, fun i => ⟨(hth i).1, (hM i).1⟩⟩
  rw [hA3 th M] at hmem
  refine Submodule.span_mono ?_ hmem
  rintro G ⟨P, I, hI, hc, rfl⟩
  refine ⟨P, I, hI, fun i => ?_, rfl⟩
  induction i using Fin.cases with
  | zero =>
    rw [pre_zero, P.zero]
    constructor
    · intro X _ hX
      unfold valS at hX
      rw [sDegs_empty LL _ A h0] at hX
      simpa using hX
    · intro Y _ hY
      unfold lam1S at hY
      rw [sDegs_empty LL _ A h0] at hY
      simpa using hY
  | succ k =>
    rw [pre_succ]
    exact ⟨fun X hX h => ((hth k).2 X hX h).trans (hc k).1, fun Y hY h => (hc k).2.trans ((hM k).2 Y hY h)⟩

/- English proof (translation)
Establish `hmem : Psi R P.mu I ∈ (Submodule.span R {G | ∃ P' : PPath n N LL B, ∃ I : ℤ → Finset (Fin n), IsSt P'.mu I ∧ (∀ i : Fin N, P.mu i.succ (lastIdx n) ≤ P'.mu i.succ (lastIdx n) ∧ P'.mu i.succ 0 ≤ P.mu i.succ 0) ∧ G = Psi R P'.mu I} : Set _)` using `Submodule.subset_span ⟨P, I, hI, fun i => ⟨le_rfl, le_rfl⟩, rfl⟩`. Rewrite `hmem` using `[← hA3 (fun i => P.mu i.succ (lastIdx n)) (fun i => P.mu i.succ 0)]`. Use `⟨hmem.1, fun i => ?_⟩` and prove the remaining obligations. Proceed by induction on `i using Fin.cases with`. Consider the case `zero`.

Rewrite using `[pre_zero, P.zero]`. Prove the components needed by the constructor for the conclusion. Use `(le_valS_iff LL ∅ _ _).mpr fun k hk => ?_` and prove the remaining obligations. Use `sDegs_empty_subset LL _ _ k hk` as an intermediate fact. Simplify the hypotheses and the goal together.

Use `(lowest_degree_le_iff LL ∅ _ _).mpr fun k hk => ?_` and prove the remaining obligations. Use `sDegs_empty_subset LL _ _ k hk` as an intermediate fact. Simplify the hypotheses and the goal together. Consider the case `succ k`. Rewrite using `[pre_succ]`.

Conclude with `hmem.2 k`.
-/
theorem standard_polynomial_mem_bounds {N n : ℕ} [NeZero n] (LL : Letters (Fin N)) (B : Fin N → ℕ)
    (hA3 : ∀ th M : Fin N → ℤ, A3at R N n LL B th M) (P : PPath n N LL B) (I : ℤ → Finset (Fin n))
    (hI : IsSt P.mu I) :
    Psi R P.mu I ∈ Pol R n B ∧ ∀ i : Fin (N + 1),
      ((P.mu i (lastIdx n) : ℤ) : WithTop ℤ) ≤ valS LL (pre i) (Psi R P.mu I) ∧
      lam1S LL (pre i) (Psi R P.mu I) ≤ ((P.mu i 0 : ℤ) : WithBot ℤ) := by
  have hmem : Psi R P.mu I ∈ (Submodule.span R {G | ∃ P' : PPath n N LL B, ∃ I : ℤ → Finset (Fin n), IsSt P'.mu I ∧
      (∀ i : Fin N, P.mu i.succ (lastIdx n) ≤ P'.mu i.succ (lastIdx n) ∧ P'.mu i.succ 0 ≤ P.mu i.succ 0) ∧
      G = Psi R P'.mu I} : Set _) :=
    Submodule.subset_span ⟨P, I, hI, fun i => ⟨le_rfl, le_rfl⟩, rfl⟩
  rw [← hA3 (fun i => P.mu i.succ (lastIdx n)) (fun i => P.mu i.succ 0)] at hmem
  refine ⟨hmem.1, fun i => ?_⟩
  induction i using Fin.cases with
  | zero =>
    rw [pre_zero, P.zero]
    constructor
    · refine (le_valS_iff LL ∅ _ _).mpr fun k hk => ?_
      have := sDegs_empty_subset LL _ _ k hk
      simp_all
    · refine (lowest_degree_le_iff LL ∅ _ _).mpr fun k hk => ?_
      have := sDegs_empty_subset LL _ _ k hk
      simp_all
  | succ k =>
    rw [pre_succ]
    exact hmem.2 k

end A3

section Gen

/- English proof (translation)
Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem x hx`. Proceed by induction on `hb using Submodule.span_induction with`. Consider the case `mem y hy => exact h x hx y hy`. Consider the case `zero => simp`.

Consider the case `add y z _ _ hy hz => rw [map_add, mul_add]`. Conclude with `X.add_mem hy hz`. Consider the case `smul c y _ hy => rw [map_smul, mul_smul_comm]`. Conclude with `X.smul_mem c hy`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [map_add, add_mul]`. Conclude with `X.add_mem hx hy`. Consider the case `smul c x _ hx => rw [map_smul, smul_mul_assoc]`. Conclude with `X.smul_mem c hx`.
-/
theorem span_mul_mem {R A B C : Type} [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] [CommRing C]
    [Algebra R C] (φ : A →ₐ[R] C) (ψ : B →ₐ[R] C) (Sa : Set A) (Sb : Set B) (X : Submodule R C)
    (h : ∀ x ∈ Sa, ∀ y ∈ Sb, φ x * ψ y ∈ X) {a : A} (ha : a ∈ Submodule.span R Sa) {b : B}
    (hb : b ∈ Submodule.span R Sb) : φ a * ψ b ∈ X := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    induction hb using Submodule.span_induction with
    | mem y hy => exact h x hx y hy
    | zero => simp
    | add y z _ _ hy hz => rw [map_add, mul_add]; exact X.add_mem hy hz
    | smul c y _ hy => rw [map_smul, mul_smul_comm]; exact X.smul_mem c hy
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, add_mul]; exact X.add_mem hx hy
  | smul c x _ hx => rw [map_smul, smul_mul_assoc]; exact X.smul_mem c hx

/- English proof (translation)
Take `⟨d, hd, hud⟩` from `(mem_vars_iff_mem_support u).mp hu`. Use `(mem_vars_iff_mem_support _).mpr ⟨Finsupp.mapDomain f d, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[support_rename_of_injective hf]`. Conclude with `Finset.mem_image_of_mem _ hd`. Rewrite using `[Finsupp.mem_support_iff, Finsupp.mapDomain_apply hf]`.

Conclude with `Finsupp.mem_support_iff.mp hud`.
-/
theorem mem_vars_rename_inj {R σ τ : Type} [CommRing R] (f : σ → τ) (hf : Function.Injective f) (p : MvPolynomial σ R)
    {u : σ} (hu : u ∈ p.vars) : f u ∈ (rename f p).vars := by
  classical
  obtain ⟨d, hd, hud⟩ := (mem_vars_iff_mem_support u).mp hu
  refine (mem_vars_iff_mem_support _).mpr ⟨Finsupp.mapDomain f d, ?_, ?_⟩
  · rw [support_rename_of_injective hf]; exact Finset.mem_image_of_mem _ hd
  · rw [Finsupp.mem_support_iff, Finsupp.mapDomain_apply hf]; exact Finsupp.mem_support_iff.mp hud

/- English proof (translation)
Unfold `Pol`. Rewrite using `[mem_restrictSupport_iff]`. Conclude with `⟨fun h m hm => h (Finset.mem_coe.mpr hm), fun h m hm => h m (Finset.mem_coe.mp hm)⟩`.
-/
theorem mem_Pol_iff {R ι : Type} [CommRing R] {n : ℕ} {d : ι → ℕ} {g : MvPolynomial (ι × Fin n) R} :
    g ∈ Pol R n d ↔ ∀ m ∈ g.support, ∀ i, multideg m i = d i := by
  unfold Pol
  rw [mem_restrictSupport_iff]
  exact ⟨fun h m hm => h (Finset.mem_coe.mpr hm), fun h m hm => h m (Finset.mem_coe.mp hm)⟩

/- English proof (translation)
Take `⟨m0, hm0⟩` from `MvPolynomial.ne_zero_iff.mp h0`. Establish `hm : m0 ∈ g.support` using `MvPolynomial.mem_support_iff.mpr hm0`. Use `mem_Pol_iff.mp hg m0 hm i` as an intermediate fact. Rewrite using `[← this]`. Unfold `multideg`.

Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Conclude with `hi c ((mem_vars_iff_mem_support _).mpr ⟨m0, hm, Finsupp.mem_support_iff.mpr hc⟩)`.
-/
theorem pol_deg_zero {R ι : Type} [CommRing R] {n : ℕ} {d : ι → ℕ} {g : MvPolynomial (ι × Fin n) R}
    (hg : g ∈ Pol R n d) (h0 : g ≠ 0) (i : ι) (hi : ∀ c, (i, c) ∉ g.vars) : d i = 0 := by
  obtain ⟨m0, hm0⟩ := MvPolynomial.ne_zero_iff.mp h0
  have hm : m0 ∈ g.support := MvPolynomial.mem_support_iff.mpr hm0
  have := mem_Pol_iff.mp hg m0 hm i
  rw [← this]
  unfold multideg
  refine Finset.sum_eq_zero fun c _ => ?_
  by_contra hc
  exact hi c ((mem_vars_iff_mem_support _).mpr ⟨m0, hm, Finsupp.mem_support_iff.mpr hc⟩)

/- English proof (translation)
Take `⟨m0, hm, hum⟩` from `(mem_vars_iff_mem_support u).mp hu`. Use `mem_Pol_iff.mp hg m0 hm u.1` as an intermediate fact. Rewrite using `[← this]`. Unfold `multideg`. Introduce `h`.

Use `(Finset.sum_eq_zero_iff.mp h) u.2 (Finset.mem_univ _)` as an intermediate fact. Conclude with `(Finsupp.mem_support_iff.mp hum) this`.
-/
theorem pol_vars_deg {R ι : Type} [CommRing R] {n : ℕ} {d : ι → ℕ} {g : MvPolynomial (ι × Fin n) R}
    (hg : g ∈ Pol R n d) {u : ι × Fin n} (hu : u ∈ g.vars) : d u.1 ≠ 0 := by
  obtain ⟨m0, hm, hum⟩ := (mem_vars_iff_mem_support u).mp hu
  have := mem_Pol_iff.mp hg m0 hm u.1
  rw [← this]
  unfold multideg
  intro h
  have := (Finset.sum_eq_zero_iff.mp h) u.2 (Finset.mem_univ _)
  exact (Finsupp.mem_support_iff.mp hum) this

end Gen

section W

open Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.CovariantDegrees

variable {n' r : ℕ} [NeZero n'] (F : Frames n' r) (j : ℤ)

def segPairs0 [NeZero r] (K : ℕ) [NeZero K] (m : ℤ → ℤ) (th : ℤ → ℝ) :
    Set ((Fin (segN F j + 1) → Fin r → ℤ) × (Fin (segN F j + 1) → Fin K → ℤ)) :=
  {q | ∃ b' b'' : Fin (segN F j) → ℕ, (∃ P1 : PPath r (segN F j) (segLL F j) b', P1.mu = q.1) ∧
      (∃ P2 : PPath K (segN F j) (segLL F j) b'', P2.mu = q.2) ∧
      ∀ i : Fin (segN F j),
        (F.IsW j (segE F j i) → b'' i = 0) ∧
        (¬ F.IsW j (segE F j i) →
          (Even (segE F j i) → q.2 i.succ 0 + m (segE F j i) ≤ q.1 i.castSucc (lastIdx r)) ∧
          (¬ Even (segE F j i) → q.2 i.castSucc 0 + m (segE F j i) ≤ q.1 i.succ (lastIdx r)) ∧
          th (segE F j i) ≤ ((q.1 i.castSucc (lastIdx r) : ℤ) : ℝ))}

/- English proof (translation)
Proceed by induction on `v using WithTop.recTopCoe with`. Consider the case `top => exact le_top`. Consider the case `coe z => exact WithTop.coe_le_coe.mpr (Int.ceil_le.mpr (h z rfl))`.
-/
theorem ceil_le_of_geR {v : WithTop ℤ} {t : ℝ} (h : geR v t) : ((⌈t⌉ : ℤ) : WithTop ℤ) ≤ v := by
  induction v using WithTop.recTopCoe with
  | top => exact le_top
  | coe z => exact WithTop.coe_le_coe.mpr (Int.ceil_le.mpr (h z rfl))

/- English proof (translation)
Take `⟨A₀, rfl⟩` from `exists_segRen F j A hA`. Take `⟨G₀, rfl⟩` from `exists_segRen F j G (supported_mono (fun v hv => hv.1) hG)`. Establish `hG₀ : ∀ u ∈ G₀.vars, ¬ F.IsW j (segE F j u.1)` using `fun u hu => ((mem_supported.mp hG) (Finset.mem_coe.mpr (mem_vars_rename_inj _ (segVar_injective F j K) G₀ hu))).2`. Rewrite using `[← segRen_mul]`. Use `⟨_, ?_, rfl⟩` and prove the remaining obligations.

Take `⟨T', hT'⟩` from `exists_sum_polComp R r A₀`. Take `⟨T'', hT''⟩` from `exists_sum_polComp R K G₀`. Establish `hsum : rename (plVar (K` using `K)) A₀ * rename (tanVar (r := r)) G₀ = ∑ d' ∈ T', ∑ d'' ∈ T'', rename (plVar (K := K)) (polComp R r d' A₀) * rename (tanVar (r := r)) (polComp R K d'' G₀) := by conv_lhs => rw [hT', hT'']`. Rewrite using `[map_sum, map_sum, Finset.sum_mul_sum]`. Rewrite using `[SetLike.mem_coe, hsum]`.

Use `Submodule.sum_mem _ fun b' _ => Submodule.sum_mem _ fun b'' _ => ?_` and prove the remaining obligations. Distinguish the cases in `hg0 : polComp R K b'' G₀ = 0`. Rewrite using `[hg0, map_zero, mul_zero]`. Conclude with `Submodule.zero_mem _`. Set `Bv : Finset ℤ` to `(Finset.univ.image fun i => M (segE F j i) + m (segE F j i)) ∪ Finset.univ.image fun i => ⌈th (segE F j i)⌉`.

Set `Bl : Finset ℤ` to `Finset.univ.image fun i => M (segE F j i)`. Establish `ha` using `mem_span_standard_of_bounds (segLL F j) b' (hA3 _ r _ b') (polComp R r b' A₀) (polComp_mem_Pol R r b' A₀) Bv ∅`. Establish `hg` using `mem_span_standard_of_bounds (segLL F j) b'' (hA3 _ K _ b'') (polComp R K b'' G₀) (polComp_mem_Pol R K b'' G₀) ∅ Bl`. Use `span_mul_mem (rename (plVar (K := K))) (rename (tanVar (r := r))) _ _ _ ?_ ha hg` and prove the remaining obligations. Introduce and unpack `_ ⟨P1, I', hI', h1, rfl⟩ _ ⟨P2, I'', hI'', h2, rfl⟩`.

Use `Submodule.subset_span ⟨(P1.mu, P2.mu), ⟨b', b'', ⟨P1, rfl⟩, ⟨P2, rfl⟩, fun i => ⟨fun hW => ?_, fun hW => ?_⟩⟩, I', I'', hI', hI'', rfl⟩` and prove the remaining obligations. Use `pol_deg_zero (polComp_mem_Pol R K b'' G₀) hg0 i fun c hcv => ?_` and prove the remaining obligations. Establish `hs : polComp R K b'' G₀ ∈ supported R (G₀.vars : Set _)` using `polComp_mem_supported R K b'' G₀ _ (mem_supported.mpr (le_refl _))`. Conclude with `hG₀ _ (Finset.mem_coe.mp ((mem_supported.mp hs) (Finset.mem_coe.mpr hcv))) hW`. Take `⟨hE, hO, hR⟩` from `hc (segE F j i) (segE_mem F j i) hW`.

Take `⟨sA1, sA2, -, -⟩` from `seg_val F j A₀ i`. Take `⟨-, -, sG3, sG4⟩` from `seg_val F j G₀ i`. Rewrite `hE` using `[sA2, sG3]`. Rewrite `hO` using `[sA1, sG4]`. Rewrite `hR` using `[sA2]`.

Establish `mem1 : M (segE F j i) + m (segE F j i) ∈ Bv` using `Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))`. Establish `mem2 : ⌈th (segE F j i)⌉ ∈ Bv` using `Finset.mem_union_right _ (Finset.mem_image_of_mem (fun i => ⌈th (segE F j i)⌉) (Finset.mem_univ i))`. Establish `mem3 : M (segE F j i) ∈ Bl` using `Finset.mem_image_of_mem (fun i => M (segE F j i)) (Finset.mem_univ i)`. Use `⟨fun he => ?_, fun ho => ?_, ?_⟩` and prove the remaining obligations. Establish `l` using `(h2 i.succ).2 _ mem3 ((lowest_degree_compose_le _ _ b'' G₀).trans (hE he).1)`.

Establish `v` using `(h1 i.castSucc).1 _ mem1 ((hE he).2.trans (valS_le_polComp _ _ b' A₀))`. Use `show P2.mu i.succ 0 + m _ ≤ P1.mu i.castSucc _`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `l` using `(h2 i.castSucc).2 _ mem3 ((lowest_degree_compose_le _ _ b'' G₀).trans (hO ho).1)`. Establish `v` using `(h1 i.succ).1 _ mem1 ((hO ho).2.trans (valS_le_polComp _ _ b' A₀))`.

Use `show P2.mu i.castSucc 0 + m _ ≤ P1.mu i.succ _`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `v` using `(h1 i.castSucc).1 _ mem2 ((ceil_le_of_geR hR).trans (valS_le_polComp _ _ b' A₀)) show th _ ≤ ((P1.mu i.castSucc _ : ℤ) : ℝ)`. Conclude with `(Int.le_ceil _).trans (by exact_mod_cast v)`.
-/
theorem crit_alt [NeZero r] {K : ℕ} [NeZero K] (R : Type) [CommRing R] [IsDomain R]
    (hA3 : ∀ (N n : ℕ) [NeZero n] (LL : Letters (Fin N)) (B : Fin N → ℕ) (th M : Fin N → ℤ), A3at R N n LL B th M)
    (m : ℤ → ℤ) (th : ℤ → ℝ)
    (A : MvPolynomial (ℤ × Fin r) R) (G : MvPolynomial (ℤ × Fin K) R) (M : ℤ → ℤ)
    (hA : A ∈ supported R {v : ℤ × Fin r | v.1 ∈ F.letters j})
    (hG : G ∈ supported R {v : ℤ × Fin K | v.1 ∈ F.letters j ∧ ¬ F.IsW j v.1})
    (hc : ∀ x ∈ F.letters j, ¬ F.IsW j x →
      (Even x → lam1S LZ {y | y ≤ x} G ≤ ((M x : ℤ) : WithBot ℤ) ∧
          ((M x + m x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y < x} A) ∧
      (¬ Even x → lam1S LZ {y | y < x} G ≤ ((M x : ℤ) : WithBot ℤ) ∧
          ((M x + m x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y ≤ x} A) ∧
      geR (valS LZ {y | y < x} A) (th x)) :
    plEmb R r K A * nmEmb R r K G ∈
      Submodule.map (segRen F j R (r + K)).toLinearMap (XXZ R (segPairs0 F j K m th)) := by
  classical
  obtain ⟨A₀, rfl⟩ := exists_segRen F j A hA
  obtain ⟨G₀, rfl⟩ := exists_segRen F j G (supported_mono (fun v hv => hv.1) hG)
  have hG₀ : ∀ u ∈ G₀.vars, ¬ F.IsW j (segE F j u.1) := fun u hu =>
    ((mem_supported.mp hG) (Finset.mem_coe.mpr (mem_vars_rename_inj _ (segVar_injective F j K) G₀ hu))).2
  rw [← segRen_mul]
  refine ⟨_, ?_, rfl⟩
  obtain ⟨T', hT'⟩ := exists_sum_polComp R r A₀
  obtain ⟨T'', hT''⟩ := exists_sum_polComp R K G₀
  have hsum : rename (plVar (K := K)) A₀ * rename (tanVar (r := r)) G₀ = ∑ d' ∈ T', ∑ d'' ∈ T'',
      rename (plVar (K := K)) (polComp R r d' A₀) * rename (tanVar (r := r)) (polComp R K d'' G₀) := by
    conv_lhs => rw [hT', hT'']
    rw [map_sum, map_sum, Finset.sum_mul_sum]
  rw [SetLike.mem_coe, hsum]
  refine Submodule.sum_mem _ fun b' _ => Submodule.sum_mem _ fun b'' _ => ?_
  by_cases hg0 : polComp R K b'' G₀ = 0
  · rw [hg0, map_zero, mul_zero]; exact Submodule.zero_mem _
  let Bv : Finset ℤ := (Finset.univ.image fun i => M (segE F j i) + m (segE F j i)) ∪
    Finset.univ.image fun i => ⌈th (segE F j i)⌉
  let Bl : Finset ℤ := Finset.univ.image fun i => M (segE F j i)
  have ha := mem_span_standard_of_bounds (segLL F j) b' (hA3 _ r _ b') (polComp R r b' A₀) (polComp_mem_Pol R r b' A₀) Bv ∅
  have hg := mem_span_standard_of_bounds (segLL F j) b'' (hA3 _ K _ b'') (polComp R K b'' G₀) (polComp_mem_Pol R K b'' G₀) ∅ Bl
  refine span_mul_mem (rename (plVar (K := K))) (rename (tanVar (r := r))) _ _ _ ?_ ha hg
  rintro _ ⟨P1, I', hI', h1, rfl⟩ _ ⟨P2, I'', hI'', h2, rfl⟩
  refine Submodule.subset_span ⟨(P1.mu, P2.mu), ⟨b', b'', ⟨P1, rfl⟩, ⟨P2, rfl⟩, fun i => ⟨fun hW => ?_, fun hW => ?_⟩⟩,
    I', I'', hI', hI'', rfl⟩
  · refine pol_deg_zero (polComp_mem_Pol R K b'' G₀) hg0 i fun c hcv => ?_
    have hs : polComp R K b'' G₀ ∈ supported R (G₀.vars : Set _) :=
      polComp_mem_supported R K b'' G₀ _ (mem_supported.mpr (le_refl _))
    exact hG₀ _ (Finset.mem_coe.mp ((mem_supported.mp hs) (Finset.mem_coe.mpr hcv))) hW
  · obtain ⟨hE, hO, hR⟩ := hc (segE F j i) (segE_mem F j i) hW
    obtain ⟨sA1, sA2, -, -⟩ := seg_val F j A₀ i
    obtain ⟨-, -, sG3, sG4⟩ := seg_val F j G₀ i
    rw [sA2, sG3] at hE
    rw [sA1, sG4] at hO
    rw [sA2] at hR
    have mem1 : M (segE F j i) + m (segE F j i) ∈ Bv :=
      Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    have mem2 : ⌈th (segE F j i)⌉ ∈ Bv :=
      Finset.mem_union_right _ (Finset.mem_image_of_mem (fun i => ⌈th (segE F j i)⌉) (Finset.mem_univ i))
    have mem3 : M (segE F j i) ∈ Bl := Finset.mem_image_of_mem (fun i => M (segE F j i)) (Finset.mem_univ i)
    refine ⟨fun he => ?_, fun ho => ?_, ?_⟩
    · have l := (h2 i.succ).2 _ mem3 ((lowest_degree_compose_le _ _ b'' G₀).trans (hE he).1)
      have v := (h1 i.castSucc).1 _ mem1 ((hE he).2.trans (valS_le_polComp _ _ b' A₀))
      show P2.mu i.succ 0 + m _ ≤ P1.mu i.castSucc _
      linarith
    · have l := (h2 i.castSucc).2 _ mem3 ((lowest_degree_compose_le _ _ b'' G₀).trans (hO ho).1)
      have v := (h1 i.succ).1 _ mem1 ((hO ho).2.trans (valS_le_polComp _ _ b' A₀))
      show P2.mu i.castSucc 0 + m _ ≤ P1.mu i.succ _
      linarith
    · have v := (h1 i.castSucc).1 _ mem2 ((ceil_le_of_geR hR).trans (valS_le_polComp _ _ b' A₀))
      show th _ ≤ ((P1.mu i.castSucc _ : ℤ) : ℝ)
      exact (Int.le_ceil _).trans (by exact_mod_cast v)

end W

section One

open Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.CovariantDegrees

variable {n' r : ℕ} [NeZero n'] (F : Frames n' r) (j : ℤ)

/- English proof (translation)
Unfold `ordDeg`. Apply the tactic sequence `split_ifs <;> simp [Finset.sum_add_distrib]`.
-/
theorem ordDeg_add {K : ℕ} (m1 m2 : ℤ × Fin (r + K) →₀ ℕ) (x : ℤ) :
    ordDeg (m1 + m2) x = ordDeg m1 x + ordDeg m2 x := by
  unfold ordDeg
  split_ifs <;> simp [Finset.sum_add_distrib]

/- English proof (translation)
Introduce `mm hmm i`. Take `⟨m1, h1, m2, h2, rfl⟩` from `Finset.mem_add.mp (support_mul _ _ hmm)`. Establish `hf1 : Function.Injective (fun v : Fin (segN F j) × Fin r => (segE F j v.1, Fin.castAdd K v.2))`. Introduce `x y h`. Simplify using `only [Prod.mk.injEq] at h`.

Conclude with `Prod.ext ((segE_strictMono F j).injective h.1) (Fin.castAdd_injective _ _ h.2)`. Establish `hf2 : Function.Injective (fun v : Fin (segN F j) × Fin K => (segE F j v.1, Fin.natAdd r v.2))`. Introduce `x y h`. Simplify using `only [Prod.mk.injEq] at h`. Conclude with `Prod.ext ((segE_strictMono F j).injective h.1) (Fin.natAdd_injective _ _ h.2)`.

Establish `e1 : plEmb R r K (segRen F j R r a) = rename (fun v : Fin (segN F j) × Fin r => (segE F j v.1, Fin.castAdd K v.2)) a`. Simplify using `only [plEmb, segRen, rename_rename]`. Both sides reduce to the same expression. Establish `e2 : nmEmb R r K (segRen F j R K g) = rename (fun v : Fin (segN F j) × Fin K => (segE F j v.1, Fin.natAdd r v.2)) g`. Simplify using `only [nmEmb, segRen, rename_rename]`.

Both sides reduce to the same expression. Rewrite `h1` using `[e1, support_rename_of_injective hf1]`. Rewrite `h2` using `[e2, support_rename_of_injective hf2]`. Take `⟨u1, hu1, rfl⟩` from `Finset.mem_image.mp h1`. Take `⟨u2, hu2, rfl⟩` from `Finset.mem_image.mp h2`.

Establish `d1` using `mem_Pol_iff.mp ha u1 hu1 i`. Establish `d2` using `mem_Pol_iff.mp hg u2 hu2 i`. Establish `hne : ∀ (x : Fin r) (c : Fin K), Fin.castAdd K x ≠ Fin.natAdd r c`. Introduce `x c h`. Use `congrArg Fin.val h` as an intermediate fact.

Simplify using `at this`. Use linear arithmetic over natural numbers and integers. Rewrite using `[ordDeg_add]`. Unfold `ordDeg`. Use `split_ifs with he`.

Establish `z1 : ∀ c : Fin K, Finsupp.mapDomain (fun v : Fin (segN F j) × Fin r => (segE F j v.1, Fin.castAdd K v.2)) u1 (segE F j i, Fin.natAdd r c) = 0`. Introduce `c`. Use `Finsupp.mapDomain_of_notMem_range _ _ ?_` and prove the remaining obligations. Introduce and unpack `⟨v, hv⟩`. Simplify using `only [Prod.mk.injEq] at hv`.

Conclude with `hne _ _ hv.2`. Establish `z2 : ∀ c : Fin K, Finsupp.mapDomain (fun v : Fin (segN F j) × Fin K => (segE F j v.1, Fin.natAdd r v.2)) u2 (segE F j i, Fin.natAdd r c) = u2 (i, c)` using `fun c => Finsupp.mapDomain_apply hf2 u2 (i, c)`. Simplify using `only [z1, z2, Finset.sum_const_zero, zero_add]`. Conclude with `d2`. Establish `z1 : ∀ c : Fin r, Finsupp.mapDomain (fun v : Fin (segN F j) × Fin r => (segE F j v.1, Fin.castAdd K v.2)) u1 (segE F j i, Fin.castAdd K c) = u1 (i, c)` using `fun c => Finsupp.mapDomain_apply hf1 u1 (i, c)`.

Establish `z2 : ∀ c : Fin r, Finsupp.mapDomain (fun v : Fin (segN F j) × Fin K => (segE F j v.1, Fin.natAdd r v.2)) u2 (segE F j i, Fin.castAdd K c) = 0`. Introduce `c`. Use `Finsupp.mapDomain_of_notMem_range _ _ ?_` and prove the remaining obligations. Introduce and unpack `⟨v, hv⟩`. Simplify using `only [Prod.mk.injEq] at hv`.

Conclude with `hne _ _ hv.2.symm`. Simplify using `only [z1, z2, Finset.sum_const_zero, add_zero]`. Conclude with `d1`.
-/
theorem word_ord {R : Type} [CommRing R] {K : ℕ} (b' b'' : Fin (segN F j) → ℕ)
    (a : MvPolynomial (Fin (segN F j) × Fin r) R) (ha : a ∈ Pol R r b')
    (g : MvPolynomial (Fin (segN F j) × Fin K) R) (hg : g ∈ Pol R K b'') :
    ∀ mm ∈ (plEmb R r K (segRen F j R r a) * nmEmb R r K (segRen F j R K g)).support, ∀ i,
      ordDeg mm (segE F j i) = if Even (segE F j i) then b'' i else b' i := by
  classical
  intro mm hmm i
  obtain ⟨m1, h1, m2, h2, rfl⟩ := Finset.mem_add.mp (support_mul _ _ hmm)
  have hf1 : Function.Injective (fun v : Fin (segN F j) × Fin r => (segE F j v.1, Fin.castAdd K v.2)) := by
    intro x y h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext ((segE_strictMono F j).injective h.1) (Fin.castAdd_injective _ _ h.2)
  have hf2 : Function.Injective (fun v : Fin (segN F j) × Fin K => (segE F j v.1, Fin.natAdd r v.2)) := by
    intro x y h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext ((segE_strictMono F j).injective h.1) (Fin.natAdd_injective _ _ h.2)
  have e1 : plEmb R r K (segRen F j R r a) =
      rename (fun v : Fin (segN F j) × Fin r => (segE F j v.1, Fin.castAdd K v.2)) a := by
    simp only [plEmb, segRen, rename_rename]; rfl
  have e2 : nmEmb R r K (segRen F j R K g) =
      rename (fun v : Fin (segN F j) × Fin K => (segE F j v.1, Fin.natAdd r v.2)) g := by
    simp only [nmEmb, segRen, rename_rename]; rfl
  rw [e1, support_rename_of_injective hf1] at h1
  rw [e2, support_rename_of_injective hf2] at h2
  obtain ⟨u1, hu1, rfl⟩ := Finset.mem_image.mp h1
  obtain ⟨u2, hu2, rfl⟩ := Finset.mem_image.mp h2
  have d1 := mem_Pol_iff.mp ha u1 hu1 i
  have d2 := mem_Pol_iff.mp hg u2 hu2 i
  have hne : ∀ (x : Fin r) (c : Fin K), Fin.castAdd K x ≠ Fin.natAdd r c := by
    intro x c h
    have := congrArg Fin.val h
    simp at this
    omega
  rw [ordDeg_add]
  unfold ordDeg
  split_ifs with he
  · have z1 : ∀ c : Fin K, Finsupp.mapDomain (fun v : Fin (segN F j) × Fin r => (segE F j v.1, Fin.castAdd K v.2)) u1
        (segE F j i, Fin.natAdd r c) = 0 := by
      intro c
      refine Finsupp.mapDomain_of_notMem_range _ _ ?_
      rintro ⟨v, hv⟩
      simp only [Prod.mk.injEq] at hv
      exact hne _ _ hv.2
    have z2 : ∀ c : Fin K, Finsupp.mapDomain (fun v : Fin (segN F j) × Fin K => (segE F j v.1, Fin.natAdd r v.2)) u2
        (segE F j i, Fin.natAdd r c) = u2 (i, c) := fun c => Finsupp.mapDomain_apply hf2 u2 (i, c)
    simp only [z1, z2, Finset.sum_const_zero, zero_add]
    exact d2
  · have z1 : ∀ c : Fin r, Finsupp.mapDomain (fun v : Fin (segN F j) × Fin r => (segE F j v.1, Fin.castAdd K v.2)) u1
        (segE F j i, Fin.castAdd K c) = u1 (i, c) := fun c => Finsupp.mapDomain_apply hf1 u1 (i, c)
    have z2 : ∀ c : Fin r, Finsupp.mapDomain (fun v : Fin (segN F j) × Fin K => (segE F j v.1, Fin.natAdd r v.2)) u2
        (segE F j i, Fin.castAdd K c) = 0 := by
      intro c
      refine Finsupp.mapDomain_of_notMem_range _ _ ?_
      rintro ⟨v, hv⟩
      simp only [Prod.mk.injEq] at hv
      exact hne _ _ hv.2.symm
    simp only [z1, z2, Finset.sum_const_zero, add_zero]
    exact d1

def ordSet (K : ℕ) (o : ℤ → ℝ) : Set (ℤ × Fin (r + K) →₀ ℕ) :=
  {mm | ∀ x ∈ F.letters j, ¬ F.IsW j x → (ordDeg mm x : ℝ) ≤ o x}

/- English proof (translation)
Establish `key : ∀ y ∈ Submodule.map (segRen F j R (r + K)).toLinearMap (XXZ R (segPairs0 F j K m th)), suppProj R (ordSet F j K o) y ∈ Submodule.map (segRen F j R (r + K)).toLinearMap (XXZ R (segPairs F j K m th o))`. Introduce `y hy`. Unfold `XXZ at hy`. Rewrite `hy` using `[Submodule.map_span]`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem y hy`. Take `⟨_, ⟨q, ⟨b', b'', ⟨P1, h1⟩, ⟨P2, h2⟩, hcond⟩, I', I'', hI', hI'', rfl⟩, rfl⟩` from `hy`. Take `⟨nu, ka⟩` from `q`. Simplify using `only at h1 h2 hcond hI' hI''`. Substitute `h1` using the available equality.

Substitute `h2` using the available equality. Establish `e : (segRen F j R (r + K)).toLinearMap (PsiPl R P1.mu I' * PsiTan R P2.mu I'') = plEmb R r K (segRen F j R r (Psi R P1.mu I')) * nmEmb R r K (segRen F j R K (Psi R P2.mu I''))` using `segRen_mul F j _ _`. Establish `hw` using `word_ord F j b' b'' _ (hPol r b' P1 I' hI') _ (hPol K b'' P2 I'' hI'')`. Distinguish the cases in `hord : ∀ i, ¬ F.IsW j (segE F j i) → (((if Even (segE F j i) then b'' i else b' i : ℕ)) : ℝ) ≤ o (segE F j i)`. Rewrite using `[suppProj_of_mem]`.

Use `⟨_, Submodule.subset_span ⟨(P1.mu, P2.mu), ⟨b', b'', ⟨P1, rfl⟩, ⟨P2, rfl⟩, fun i => ⟨(hcond i).1, fun hW => ?_⟩⟩, I', I'', hI', hI'', rfl⟩, rfl⟩` and prove the remaining obligations. Take `⟨cE, cO, cR⟩` from `(hcond i).2 hW`. Establish `ho` using `hord i hW`. Use `⟨fun he => ⟨cE he, ?_⟩, fun he => ⟨cO he, ?_⟩, cR⟩` and prove the remaining obligations. Rewrite `ho` using `[if_pos he]`. Then use the resulting hypothesis.

Rewrite `ho` using `[if_neg he]`. Then use the resulting hypothesis. Rewrite using `[e, mem_restrictSupport_iff]`. Introduce `mm hmm x hx hW`. Take `⟨i, rfl⟩` from `segE_surj F j hx`. Rewrite using `[hw mm (Finset.mem_coe.mp hmm) i]`.

Conclude with `hord i hW`. Rewrite using `[suppProj_of_disjoint R _ {mm | ∀ i, ordDeg mm (segE F j i) = if Even (segE F j i) then b'' i else b' i}]`. Conclude with `Submodule.zero_mem _`. Rewrite using `[e, mem_restrictSupport_iff]`. Introduce `mm hmm`.

Conclude with `hw mm (Finset.mem_coe.mp hmm)`. Rewrite using `[Set.disjoint_left]`. Introduce `mm h1 h2`. Apply `hord` to reduce the goal to its premises. Introduce `i hW`.

Rewrite using `[← h2 i]`. Conclude with `h1 _ (segE_mem F j i) hW`. Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add y z _ _ hy hz => rw [map_add]`.

Conclude with `Submodule.add_mem _ hy hz`. Consider the case `smul c y _ hy => rw [map_smul]`. Conclude with `Submodule.smul_mem _ c hy`. Rewrite using `[← suppProj_of_mem R _ x hx2]`. Conclude with `key x hx`.
-/
theorem ord_proj [NeZero r] {K : ℕ} [NeZero K] (R : Type) [CommRing R]
    (hPol : ∀ (n : ℕ) [NeZero n] (b : Fin (segN F j) → ℕ) (P : PPath n (segN F j) (segLL F j) b)
      (I : ℤ → Finset (Fin n)), IsSt P.mu I → Psi R P.mu I ∈ Pol R n b)
    (m : ℤ → ℤ) (th o : ℤ → ℝ) (x : SegRing R r K)
    (hx : x ∈ Submodule.map (segRen F j R (r + K)).toLinearMap (XXZ R (segPairs0 F j K m th)))
    (hx2 : x ∈ restrictSupport R (ordSet F j K o)) :
    x ∈ Submodule.map (segRen F j R (r + K)).toLinearMap (XXZ R (segPairs F j K m th o)) := by
  have key : ∀ y ∈ Submodule.map (segRen F j R (r + K)).toLinearMap (XXZ R (segPairs0 F j K m th)),
      suppProj R (ordSet F j K o) y ∈
        Submodule.map (segRen F j R (r + K)).toLinearMap (XXZ R (segPairs F j K m th o)) := by
    intro y hy
    unfold XXZ at hy
    rw [Submodule.map_span] at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨_, ⟨q, ⟨b', b'', ⟨P1, h1⟩, ⟨P2, h2⟩, hcond⟩, I', I'', hI', hI'', rfl⟩, rfl⟩ := hy
      obtain ⟨nu, ka⟩ := q
      simp only at h1 h2 hcond hI' hI''
      subst h1
      subst h2
      have e : (segRen F j R (r + K)).toLinearMap (PsiPl R P1.mu I' * PsiTan R P2.mu I'') =
          plEmb R r K (segRen F j R r (Psi R P1.mu I')) * nmEmb R r K (segRen F j R K (Psi R P2.mu I'')) :=
        segRen_mul F j _ _
      have hw := word_ord F j b' b'' _ (hPol r b' P1 I' hI') _ (hPol K b'' P2 I'' hI'')
      by_cases hord : ∀ i, ¬ F.IsW j (segE F j i) →
          (((if Even (segE F j i) then b'' i else b' i : ℕ)) : ℝ) ≤ o (segE F j i)
      · rw [suppProj_of_mem]
        · refine ⟨_, Submodule.subset_span ⟨(P1.mu, P2.mu), ⟨b', b'', ⟨P1, rfl⟩, ⟨P2, rfl⟩, fun i =>
            ⟨(hcond i).1, fun hW => ?_⟩⟩, I', I'', hI', hI'', rfl⟩, rfl⟩
          obtain ⟨cE, cO, cR⟩ := (hcond i).2 hW
          have ho := hord i hW
          refine ⟨fun he => ⟨cE he, ?_⟩, fun he => ⟨cO he, ?_⟩, cR⟩
          · rwa [if_pos he] at ho
          · rwa [if_neg he] at ho
        · rw [e, mem_restrictSupport_iff]
          intro mm hmm x hx hW
          obtain ⟨i, rfl⟩ := segE_surj F j hx
          rw [hw mm (Finset.mem_coe.mp hmm) i]
          exact hord i hW
      · rw [suppProj_of_disjoint R _ {mm | ∀ i, ordDeg mm (segE F j i) = if Even (segE F j i) then b'' i else b' i}]
        · exact Submodule.zero_mem _
        · rw [e, mem_restrictSupport_iff]
          intro mm hmm
          exact hw mm (Finset.mem_coe.mp hmm)
        · rw [Set.disjoint_left]
          intro mm h1 h2
          apply hord
          intro i hW
          rw [← h2 i]
          exact h1 _ (segE_mem F j i) hW
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ c hy
  rw [← suppProj_of_mem R _ x hx2]
  exact key x hx

/- English proof (translation)
Use `ord_proj F j R (fun n _ b P I hI => (standard_polynomial_mem_bounds (segLL F j) b (hA3 _ n _ b) P I hI).1) m th o _ (crit_alt F j R hA3 m th A G M hA hG hc) ?_` and prove the remaining obligations. Rewrite using `[mem_restrictSupport_iff]`. Introduce `mm hmm`. Conclude with `ho mm (Finset.mem_coe.mp hmm)`.
-/
theorem crit_words [NeZero r] {K : ℕ} [NeZero K] (R : Type) [CommRing R] [IsDomain R]
    (hA3 : ∀ (N n : ℕ) [NeZero n] (LL : Letters (Fin N)) (B : Fin N → ℕ) (th M : Fin N → ℤ), A3at R N n LL B th M)
    (m : ℤ → ℤ) (th o : ℤ → ℝ)
    (A : MvPolynomial (ℤ × Fin r) R) (G : MvPolynomial (ℤ × Fin K) R) (M : ℤ → ℤ)
    (hA : A ∈ supported R {v : ℤ × Fin r | v.1 ∈ F.letters j})
    (hG : G ∈ supported R {v : ℤ × Fin K | v.1 ∈ F.letters j ∧ ¬ F.IsW j v.1})
    (hc : ∀ x ∈ F.letters j, ¬ F.IsW j x →
      (Even x → lam1S LZ {y | y ≤ x} G ≤ ((M x : ℤ) : WithBot ℤ) ∧
          ((M x + m x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y < x} A) ∧
      (¬ Even x → lam1S LZ {y | y < x} G ≤ ((M x : ℤ) : WithBot ℤ) ∧
          ((M x + m x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y ≤ x} A) ∧
      geR (valS LZ {y | y < x} A) (th x))
    (ho : ∀ mm ∈ (plEmb R r K A * nmEmb R r K G).support, ∀ x ∈ F.letters j, ¬ F.IsW j x → (ordDeg mm x : ℝ) ≤ o x) :
    plEmb R r K A * nmEmb R r K G ∈
      Submodule.map (segRen F j R (r + K)).toLinearMap (XXZ R (segPairs F j K m th o)) := by
  refine ord_proj F j R (fun n _ b P I hI => (standard_polynomial_mem_bounds (segLL F j) b (hA3 _ n _ b) P I hI).1) m th o _
    (crit_alt F j R hA3 m th A G M hA hG hc) ?_
  rw [mem_restrictSupport_iff]
  intro mm hmm
  exact ho mm (Finset.mem_coe.mp hmm)

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Take `⟨hx1, hx2⟩` from `Submodule.mem_inf.mp hx`. Use `ord_proj F j R (fun n _ b P I hI => (standard_polynomial_mem_bounds (segLL F j) b (hA3 _ n _ b) P I hI).1) m th o x ?_ hx2` and prove the remaining obligations. Use `Submodule.span_le.mpr ?_ hx1` and prove the remaining obligations.

Introduce and unpack `_ ⟨A, G, M, hA, hG, hc, rfl⟩`. Conclude with `crit_alt F j R hA3 m th A G M hA hG hc`. Unfold `XXZ`. Rewrite using `[Submodule.map_span, Submodule.span_le]`. Introduce and unpack `_ ⟨_, ⟨q, hq, I', I'', hI', hI'', rfl⟩, rfl⟩`.

Take `⟨b', b'', ⟨P1, h1⟩, ⟨P2, h2⟩, hcond⟩` from `hq`. Take `⟨nu, ka⟩` from `q`. Simplify using `only at h1 h2 hcond hI' hI''`. Substitute `h1` using the available equality. Substitute `h2` using the available equality.

Establish `u1` using `standard_polynomial_mem_bounds (segLL F j) b' (hA3 _ r _ b') P1 I' hI'`. Establish `u2` using `standard_polynomial_mem_bounds (segLL F j) b'' (hA3 _ K _ b'') P2 I'' hI''`. Establish `e : (segRen F j R (r + K)).toLinearMap (PsiPl R P1.mu I' * PsiTan R P2.mu I'') = plEmb R r K (segRen F j R r (Psi R P1.mu I')) * nmEmb R r K (segRen F j R K (Psi R P2.mu I''))` using `segRen_mul F j _ _`. Rewrite using `[SetLike.mem_coe, e]`. Set `M : ℤ → ℤ` to `Function.extend (segE F j) (fun i => if Even (segE F j i) then P2.mu i.succ 0 else P2.mu i.castSucc 0) 0`.

Establish `hM : ∀ i, M (segE F j i) = if Even (segE F j i) then P2.mu i.succ 0 else P2.mu i.castSucc 0` using `fun i => (segE_strictMono F j).injective.extend_apply _ _ i`. Use `space_criterion_clause R n' r K F j m th o _ _ M ?_ ?_ ?_ ?_` and prove the remaining obligations. Use `mem_supported.mpr fun v hv => ?_` and prove the remaining obligations. Take `⟨u, _, rfl⟩` from `mem_vars_rename _ _ (Finset.mem_coe.mp hv)`. Conclude with `segE_mem F j u.1`.

Use `mem_supported.mpr fun v hv => ?_` and prove the remaining obligations. Take `⟨u, hu, rfl⟩` from `mem_vars_rename _ _ (Finset.mem_coe.mp hv)`. Conclude with `⟨segE_mem F j u.1, fun hW => pol_vars_deg u2.1 hu ((hcond u.1).1 hW)⟩`. Introduce `x hx hW`. Take `⟨i, rfl⟩` from `segE_surj F j hx`.

Take `⟨sA1, sA2, -, -⟩` from `seg_val F j (Psi R P1.mu I') i`. Take `⟨-, -, sG3, sG4⟩` from `seg_val F j (Psi R P2.mu I'') i`. Take `⟨cE, cO, cR⟩` from `(hcond i).2 hW`. Rewrite using `[sA1, sA2, sG3, sG4, hM]`. Use `⟨fun he => ⟨?_, ?_⟩, fun he => ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[if_pos he]`. Conclude with `(u2.2 i.succ).2`. Rewrite using `[if_pos he]`. Conclude with `le_trans (WithTop.coe_le_coe.mpr (cE he).1) (u1.2 i.castSucc).1`. Rewrite using `[if_neg he]`.

Conclude with `(u2.2 i.castSucc).2`. Rewrite using `[if_neg he]`. Conclude with `le_trans (WithTop.coe_le_coe.mpr (cO he).1) (u1.2 i.succ).1`. Introduce `z hz`. Establish `h` using `(u1.2 i.castSucc).1`.

Rewrite `h` using `[hz]`. Establish `h' : P1.mu i.castSucc (lastIdx r) ≤ z` using `WithTop.coe_le_coe.mp h`. Conclude with `cR.trans (by exact_mod_cast h')`. Introduce `mm hmm x hx hW`. Take `⟨i, rfl⟩` from `segE_surj F j hx`.

Take `⟨cE, cO, cR⟩` from `(hcond i).2 hW`. Rewrite using `[word_ord F j b' b'' _ u1.1 _ u2.1 mm hmm i]`. Use `split_ifs with he`. Conclude with `(cE he).2`. Conclude with `(cO he).2`.
-/
theorem first_clause_segment_rename [NeZero r] {K : ℕ} [NeZero K] (R : Type) [CommRing R] [IsDomain R]
    (hA3 : ∀ (N n : ℕ) [NeZero n] (LL : Letters (Fin N)) (B : Fin N → ℕ) (th M : Fin N → ℤ), A3at R N n LL B th M)
    (m : ℤ → ℤ) (th o : ℤ → ℝ) :
    XX' R r K F j m th o =
      Submodule.map (segRen F j R (r + K)).toLinearMap (XXZ R (segPairs F j K m th o)) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
    refine ord_proj F j R (fun n _ b P I hI => (standard_polynomial_mem_bounds (segLL F j) b (hA3 _ n _ b) P I hI).1) m th o x ?_ hx2
    refine Submodule.span_le.mpr ?_ hx1
    rintro _ ⟨A, G, M, hA, hG, hc, rfl⟩
    exact crit_alt F j R hA3 m th A G M hA hG hc
  · unfold XXZ
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨q, hq, I', I'', hI', hI'', rfl⟩, rfl⟩
    obtain ⟨b', b'', ⟨P1, h1⟩, ⟨P2, h2⟩, hcond⟩ := hq
    obtain ⟨nu, ka⟩ := q
    simp only at h1 h2 hcond hI' hI''
    subst h1
    subst h2
    have u1 := standard_polynomial_mem_bounds (segLL F j) b' (hA3 _ r _ b') P1 I' hI'
    have u2 := standard_polynomial_mem_bounds (segLL F j) b'' (hA3 _ K _ b'') P2 I'' hI''
    have e : (segRen F j R (r + K)).toLinearMap (PsiPl R P1.mu I' * PsiTan R P2.mu I'') =
        plEmb R r K (segRen F j R r (Psi R P1.mu I')) * nmEmb R r K (segRen F j R K (Psi R P2.mu I'')) :=
      segRen_mul F j _ _
    rw [SetLike.mem_coe, e]
    let M : ℤ → ℤ := Function.extend (segE F j)
      (fun i => if Even (segE F j i) then P2.mu i.succ 0 else P2.mu i.castSucc 0) 0
    have hM : ∀ i, M (segE F j i) = if Even (segE F j i) then P2.mu i.succ 0 else P2.mu i.castSucc 0 :=
      fun i => (segE_strictMono F j).injective.extend_apply _ _ i
    refine space_criterion_clause R n' r K F j m th o _ _ M ?_ ?_ ?_ ?_
    · refine mem_supported.mpr fun v hv => ?_
      obtain ⟨u, _, rfl⟩ := mem_vars_rename _ _ (Finset.mem_coe.mp hv)
      exact segE_mem F j u.1
    · refine mem_supported.mpr fun v hv => ?_
      obtain ⟨u, hu, rfl⟩ := mem_vars_rename _ _ (Finset.mem_coe.mp hv)
      exact ⟨segE_mem F j u.1, fun hW => pol_vars_deg u2.1 hu ((hcond u.1).1 hW)⟩
    · intro x hx hW
      obtain ⟨i, rfl⟩ := segE_surj F j hx
      obtain ⟨sA1, sA2, -, -⟩ := seg_val F j (Psi R P1.mu I') i
      obtain ⟨-, -, sG3, sG4⟩ := seg_val F j (Psi R P2.mu I'') i
      obtain ⟨cE, cO, cR⟩ := (hcond i).2 hW
      rw [sA1, sA2, sG3, sG4, hM]
      refine ⟨fun he => ⟨?_, ?_⟩, fun he => ⟨?_, ?_⟩, ?_⟩
      · rw [if_pos he]; exact (u2.2 i.succ).2
      · rw [if_pos he]; exact le_trans (WithTop.coe_le_coe.mpr (cE he).1) (u1.2 i.castSucc).1
      · rw [if_neg he]; exact (u2.2 i.castSucc).2
      · rw [if_neg he]; exact le_trans (WithTop.coe_le_coe.mpr (cO he).1) (u1.2 i.succ).1
      · intro z hz
        have h := (u1.2 i.castSucc).1
        rw [hz] at h
        have h' : P1.mu i.castSucc (lastIdx r) ≤ z := WithTop.coe_le_coe.mp h
        exact cR.trans (by exact_mod_cast h')
    · intro mm hmm x hx hW
      obtain ⟨i, rfl⟩ := segE_surj F j hx
      obtain ⟨cE, cO, cR⟩ := (hcond i).2 hW
      rw [word_ord F j b' b'' _ u1.1 _ u2.1 mm hmm i]
      split_ifs with he
      · exact (cE he).2
      · exact (cO he).2

end One

section Four0

open Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.CovariantDegrees

def biSet {N r K : ℕ} (b' b'' : Fin N → ℕ) : Set (Fin N × Fin (r + K) →₀ ℕ) :=
  {mm | ∀ i, ∑ c : Fin r, mm (i, Fin.castAdd K c) = b' i ∧ ∑ c : Fin K, mm (i, Fin.natAdd r c) = b'' i}

def biPol (R : Type) [CommRing R] {N r K : ℕ} (b' b'' : Fin N → ℕ) :
    Submodule R (MvPolynomial (Fin N × Fin (r + K)) R) := restrictSupport R (biSet b' b'')

variable {n' r : ℕ} [NeZero n'] (F : Frames n' r) (j : ℤ)

open Classical in

def segL (m : ℤ → ℤ) (th : ℤ → ℝ) : List (PathInequality (segN F j)) :=
  (List.finRange (segN F j)).flatMap fun i =>
    if F.IsW j (segE F j i) then []
    else [if Even (segE F j i) then PathInequality.mix i.succ i.castSucc (m (segE F j i))
          else PathInequality.mix i.castSucc i.succ (m (segE F j i)), PathInequality.nuGe i.castSucc ⌈th (segE F j i)⌉]

def segPPB [NeZero r] (K : ℕ) [NeZero K] (m : ℤ → ℤ) (th : ℤ → ℝ) (B : Fin (segN F j) → ℕ) :
    Set ((Fin (segN F j + 1) → Fin r → ℤ) × (Fin (segN F j + 1) → Fin K → ℤ)) :=
  {q | (∃ P : PPath (r + K) (segN F j) (segLL F j) B, P.mu = joinPT q.1 q.2) ∧ ∀ e ∈ segL F j m th, e.Sat q.1 q.2}

def ordOK (o : ℤ → ℝ) (b' b'' : Fin (segN F j) → ℕ) : Prop :=
  ∀ i, (F.IsW j (segE F j i) → b'' i = 0) ∧
    (¬ F.IsW j (segE F j i) → (Even (segE F j i) → (b'' i : ℝ) ≤ o (segE F j i)) ∧
      (¬ Even (segE F j i) → (b' i : ℝ) ≤ o (segE F j i)))

end Four0

/- English proof (translation)
Assume the negation of the conclusion as `h`. Conclude with `hm (((MvPolynomial.mem_restrictSupport_iff (R := R)).mp hp) (Finset.mem_coe.mpr (mem_support_iff.mpr h)))`.
-/
theorem li_coeff_zero {R σ : Type} [CommRing R] {T : Set (σ →₀ ℕ)} {p : MvPolynomial σ R}
    (hp : p ∈ restrictSupport R T) {m : σ →₀ ℕ} (hm : m ∉ T) : coeff m p = 0 := by
  by_contra h
  exact hm (((MvPolynomial.mem_restrictSupport_iff (R := R)).mp hp) (Finset.mem_coe.mpr (mem_support_iff.mpr h)))

/- English proof (translation)
Rewrite using `[linearIndependent_iff']`. Introduce `s g hs x0 hx0`. Establish `hfil : ∑ x ∈ s with d x = d x0, g x • f x = 0`. Use extensionality with `m`. Rewrite using `[coeff_sum, coeff_zero]`.

Distinguish the cases in `hm : m ∈ T (d x0)`. Establish `h0` using `congrArg (coeff m) hs`. Rewrite `h0` using `[coeff_sum, coeff_zero]`. Rewrite using `[Finset.sum_filter]`. Use `Eq.trans ?_ h0` and prove the remaining obligations.

Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Use `split_ifs with hx`. Both sides reduce to the same expression. Rewrite using `[coeff_smul, li_coeff_zero (hmem x) (fun h => hx (hT _ _ m h hm)), smul_zero]`. Use `Finset.sum_eq_zero fun x hx => ?_` and prove the remaining obligations.

Rewrite using `[coeff_smul, li_coeff_zero (hmem x) (by rw [(Finset.mem_filter.mp hx).2]; exact hm), smul_zero]`. Establish `hk : ∑ x ∈ s.subtype (fun x => d x = d x0), g x • f x = 0`. Rewrite using `[Finset.sum_subtype_eq_sum_filter (f := fun x => g x • f x)]`. Conclude with `hfil`. Conclude with `(linearIndependent_iff'.mp (hli (d x0))) _ (fun x => g x) hk ⟨x0, rfl⟩ (Finset.mem_subtype.mpr hx0)`.
-/
theorem li_graded {R : Type} [CommRing R] {σ ι κ : Type} (f : ι → MvPolynomial σ R) (d : ι → κ)
    (T : κ → Set (σ →₀ ℕ)) (hT : ∀ k k' m, m ∈ T k → m ∈ T k' → k = k')
    (hmem : ∀ x, f x ∈ restrictSupport R (T (d x)))
    (hli : ∀ k, LinearIndependent R (fun x : {x // d x = k} => f x)) : LinearIndependent R f := by
  classical
  rw [linearIndependent_iff']
  intro s g hs x0 hx0
  have hfil : ∑ x ∈ s with d x = d x0, g x • f x = 0 := by
    ext m
    rw [coeff_sum, coeff_zero]
    by_cases hm : m ∈ T (d x0)
    · have h0 := congrArg (coeff m) hs
      rw [coeff_sum, coeff_zero] at h0
      rw [Finset.sum_filter]
      refine Eq.trans ?_ h0
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs with hx
      · rfl
      · rw [coeff_smul, li_coeff_zero (hmem x) (fun h => hx (hT _ _ m h hm)), smul_zero]
    · refine Finset.sum_eq_zero fun x hx => ?_
      rw [coeff_smul, li_coeff_zero (hmem x) (by rw [(Finset.mem_filter.mp hx).2]; exact hm), smul_zero]
  have hk : ∑ x ∈ s.subtype (fun x => d x = d x0), g x • f x = 0 := by
    rw [Finset.sum_subtype_eq_sum_filter (f := fun x => g x • f x)]; exact hfil
  exact (linearIndependent_iff'.mp (hli (d x0))) _ (fun x => g x) hk ⟨x0, rfl⟩ (Finset.mem_subtype.mpr hx0)

abbrev li_Idx (n N : ℕ) (LL : Letters (Fin N)) :=
  {x : (Fin (N + 1) → Fin n → ℤ) × (ℤ → Finset (Fin n)) //
    (∃ B : Fin N → ℕ, ∃ P : PPath n N LL B, P.mu = x.1) ∧ IsSt x.1 x.2}

/- English proof (translation)
Use `li_graded (fun x : li_Idx n N LL => Psi O x.1.1 x.1.2) (fun x => Classical.choose x.2.1) (fun B => {m | ∀ i, multideg m i = B i}) ?_ ?_ ?_` and prove the remaining obligations. Introduce `k k' m h1 h2`. Use function extensionality and compare the values at `i`. Rewrite using `[← h1 i, h2 i]`. Introduce `x`.

Take `⟨P, hP⟩` from `Classical.choose_spec x.2.1`. Establish `h1 : Psi O x.1.1 x.1.2 ∈ Pol O n (Classical.choose x.2.1)`. Rewrite using `[← (h _).2]`. Conclude with `Submodule.subset_span ⟨P, x.1.2, by rw [hP]; exact x.2.2, by rw [hP]⟩`. Conclude with `h1`.

Introduce `B`. Establish `hex : ∀ x : {x : li_Idx n N LL // Classical.choose x.2.1 = B}, ∃ P : PPath n N LL B, P.mu = x.1.1.1`. Introduce and unpack `⟨x, rfl⟩`. Conclude with `Classical.choose_spec x.2.1`. Set `φ : {x : li_Idx n N LL // Classical.choose x.2.1 = B} → {x : PPath n N LL B × (ℤ → Finset (Fin n)) // IsSt x.1.mu x.2}` to `fun x => ⟨(Classical.choose (hex x), x.1.1.2), by show IsSt (Classical.choose (hex x)).mu x.1.1.2`.

Rewrite using `[Classical.choose_spec (hex x)]`. Conclude with `x.1.2.2⟩`. Establish `hφ : Function.Injective φ`. Introduce `x y hxy`. Establish `h1 : (Classical.choose (hex x)).mu = (Classical.choose (hex y)).mu` using `congrArg (fun z => z.1.1.mu) hxy`.

Establish `h2 : x.1.1.2 = y.1.1.2` using `congrArg (fun z => z.1.2) hxy`. Rewrite `h1` using `[Classical.choose_spec (hex x), Classical.choose_spec (hex y)]`. Conclude with `Subtype.ext (Subtype.ext (Prod.ext h1 h2))`. Establish `h3` using `(h B).1.comp φ hφ`. Establish `e : (fun x : {x : li_Idx n N LL // Classical.choose x.2.1 = B} => Psi O x.1.1.1 x.1.1.2) = (fun x : {x : PPath n N LL B × (ℤ → Finset (Fin n)) // IsSt x.1.mu x.2} => Psi O x.1.1.mu x.1.2) ∘ φ`.

Use function extensionality and compare the values at `x`. Use `show Psi O x.1.1.1 x.1.1.2 = Psi O (Classical.choose (hex x)).mu x.1.1.2`. Rewrite using `[Classical.choose_spec (hex x)]`. Rewrite using `[e]`. Conclude with `h3`.
-/
theorem li_allDeg (O : Type) [CommRing O] (N n : ℕ) (LL : Letters (Fin N))
    (h : ∀ B : Fin N → ℕ,
      LinearIndependent O (fun x : {x : PPath n N LL B × (ℤ → Finset (Fin n)) // IsSt x.1.mu x.2} =>
        Psi O x.1.1.mu x.1.2) ∧
      Submodule.span O {G | ∃ P : PPath n N LL B, ∃ I : ℤ → Finset (Fin n), IsSt P.mu I ∧ G = Psi O P.mu I} =
        Pol O n B) :
    LinearIndependent O (fun x : li_Idx n N LL => Psi O x.1.1 x.1.2) := by
  classical
  refine li_graded (fun x : li_Idx n N LL => Psi O x.1.1 x.1.2) (fun x => Classical.choose x.2.1)
    (fun B => {m | ∀ i, multideg m i = B i}) ?_ ?_ ?_
  · intro k k' m h1 h2
    funext i
    rw [← h1 i, h2 i]
  · intro x
    obtain ⟨P, hP⟩ := Classical.choose_spec x.2.1
    have h1 : Psi O x.1.1 x.1.2 ∈ Pol O n (Classical.choose x.2.1) := by
      rw [← (h _).2]
      exact Submodule.subset_span ⟨P, x.1.2, by rw [hP]; exact x.2.2, by rw [hP]⟩
    exact h1
  · intro B
    have hex : ∀ x : {x : li_Idx n N LL // Classical.choose x.2.1 = B}, ∃ P : PPath n N LL B, P.mu = x.1.1.1 := by
      rintro ⟨x, rfl⟩
      exact Classical.choose_spec x.2.1
    let φ : {x : li_Idx n N LL // Classical.choose x.2.1 = B} →
        {x : PPath n N LL B × (ℤ → Finset (Fin n)) // IsSt x.1.mu x.2} :=
      fun x => ⟨(Classical.choose (hex x), x.1.1.2), by
        show IsSt (Classical.choose (hex x)).mu x.1.1.2
        rw [Classical.choose_spec (hex x)]; exact x.1.2.2⟩
    have hφ : Function.Injective φ := by
      intro x y hxy
      have h1 : (Classical.choose (hex x)).mu = (Classical.choose (hex y)).mu :=
        congrArg (fun z => z.1.1.mu) hxy
      have h2 : x.1.1.2 = y.1.1.2 := congrArg (fun z => z.1.2) hxy
      rw [Classical.choose_spec (hex x), Classical.choose_spec (hex y)] at h1
      exact Subtype.ext (Subtype.ext (Prod.ext h1 h2))
    have h3 := (h B).1.comp φ hφ
    have e : (fun x : {x : li_Idx n N LL // Classical.choose x.2.1 = B} => Psi O x.1.1.1 x.1.1.2) =
        (fun x : {x : PPath n N LL B × (ℤ → Finset (Fin n)) // IsSt x.1.mu x.2} => Psi O x.1.1.mu x.1.2) ∘ φ := by
      funext x
      show Psi O x.1.1.1 x.1.1.2 = Psi O (Classical.choose (hex x)).mu x.1.1.2
      rw [Classical.choose_spec (hex x)]
    rw [e]
    exact h3

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a => simp [sumAlgEquiv_C_inl]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p v hp => simp only [map_mul, hp, rename_X, map_X, sumAlgEquiv_X_inl]`.
-/
theorem li_sum_inl {R σ τ : Type} [CommRing R] (p : MvPolynomial σ R) :
    sumAlgEquiv R σ τ (rename Sum.inl p) = MvPolynomial.map C p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [sumAlgEquiv_C_inl]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp => simp only [map_mul, hp, rename_X, map_X, sumAlgEquiv_X_inl]

/- English proof (translation)
Proceed by induction on `q using MvPolynomial.induction_on with`. Consider the case `C a => simp [sumAlgEquiv_C_inl]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p v hp => simp only [map_mul, hp, rename_X, sumAlgEquiv_X_inr]`.
-/
theorem li_sum_inr {R σ τ : Type} [CommRing R] (q : MvPolynomial τ R) :
    sumAlgEquiv R σ τ (rename Sum.inr q) = C q := by
  induction q using MvPolynomial.induction_on with
  | C a => simp [sumAlgEquiv_C_inl]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp => simp only [map_mul, hp, rename_X, sumAlgEquiv_X_inr]

/- English proof (translation)
Rewrite using `[map_mul, li_sum_inl, li_sum_inr, mul_comm, coeff_C_mul, coeff_map, mul_comm, ← smul_eq_C_mul]`.
-/
theorem li_key {R σ τ : Type} [CommRing R] (p : MvPolynomial σ R) (q : MvPolynomial τ R) (m : σ →₀ ℕ) :
    coeff m (sumAlgEquiv R σ τ (rename Sum.inl p * rename Sum.inr q)) = coeff m p • q := by
  rw [map_mul, li_sum_inl, li_sum_inr, mul_comm, coeff_C_mul, coeff_map, mul_comm, ← smul_eq_C_mul]

/- English proof (translation)
Rewrite using `[linearIndependent_iff']`. Introduce `s g hs x0 hx0`. Set `g' : α → β → R` to `fun a b => if (a, b) ∈ s then g (a, b) else 0`. Establish `hs' : ∑ a ∈ s.image Prod.fst, ∑ b ∈ s.image Prod.snd, g' a b • (rename Sum.inl (u a) * rename Sum.inr (v b) : MvPolynomial (σ ⊕ τ) R) = 0`. Rewrite using `[← Finset.sum_product' (s.image Prod.fst) (s.image Prod.snd) (fun a b => g' a b • (rename Sum.inl (u a) * rename Sum.inr (v b) : MvPolynomial (σ ⊕ τ) R)), ← hs]`.

Use `symm`. Use `Finset.sum_subset_zero_on_sdiff ?_ ?_ ?_` and prove the remaining obligations. Introduce `x hx`. Conclude with `Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hx, Finset.mem_image_of_mem _ hx⟩`. Introduce `x hx`.

Establish `hx' : (x.1, x.2) ∉ s` using `(Finset.mem_sdiff.mp hx).2`. Simplify using `only [g', if_neg hx', zero_smul]`. Introduce `x hx`. Establish `hx' : (x.1, x.2) ∈ s` using `hx`. Simplify using `only [g', if_pos hx']`.

Establish `step : ∀ m : σ →₀ ℕ, ∑ b ∈ s.image Prod.snd, (∑ a ∈ s.image Prod.fst, g' a b * coeff m (u a)) • v b = 0`. Introduce `m`. Establish `h1` using `congrArg (fun P => coeff m (sumAlgEquiv R σ τ P)) hs'`. Simplify using `only [map_sum, map_smul, coeff_sum, coeff_smul, li_key, map_zero, coeff_zero] at h1`. Rewrite `h1` using `[Finset.sum_comm]`.

Rewrite using `[← h1]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_smul]`. Conclude with `Finset.sum_congr rfl fun a _ => by rw [mul_smul]`. Establish `hb : ∀ b ∈ s.image Prod.snd, ∀ m : σ →₀ ℕ, ∑ a ∈ s.image Prod.fst, g' a b * coeff m (u a) = 0` using `fun b hb m => linearIndependent_iff'.mp hv _ _ (step m) b hb`.

Establish `ha : ∀ b ∈ s.image Prod.snd, ∑ a ∈ s.image Prod.fst, g' a b • u a = 0`. Introduce `b hb'`. Use extensionality with `m`. Rewrite using `[coeff_sum, coeff_zero, ← hb b hb' m]`. Conclude with `Finset.sum_congr rfl fun a _ => by rw [coeff_smul, smul_eq_mul]`.

Establish `h2` using `linearIndependent_iff'.mp hu _ (fun a => g' a x0.2) (ha x0.2 (Finset.mem_image_of_mem _ hx0)) x0.1 (Finset.mem_image_of_mem _ hx0)`. Establish `hx0' : (x0.1, x0.2) ∈ s` using `hx0`. Simplify `h2` using `only [g', if_pos hx0']`.
-/
theorem li_ext {R : Type} [CommRing R] {σ τ α β : Type} (u : α → MvPolynomial σ R) (v : β → MvPolynomial τ R)
    (hu : LinearIndependent R u) (hv : LinearIndependent R v) :
    LinearIndependent R
      (fun x : α × β => (rename Sum.inl (u x.1) * rename Sum.inr (v x.2) : MvPolynomial (σ ⊕ τ) R)) := by
  classical
  rw [linearIndependent_iff']
  intro s g hs x0 hx0
  let g' : α → β → R := fun a b => if (a, b) ∈ s then g (a, b) else 0
  have hs' : ∑ a ∈ s.image Prod.fst, ∑ b ∈ s.image Prod.snd,
      g' a b • (rename Sum.inl (u a) * rename Sum.inr (v b) : MvPolynomial (σ ⊕ τ) R) = 0 := by
    rw [← Finset.sum_product' (s.image Prod.fst) (s.image Prod.snd)
      (fun a b => g' a b • (rename Sum.inl (u a) * rename Sum.inr (v b) : MvPolynomial (σ ⊕ τ) R)), ← hs]
    symm
    refine Finset.sum_subset_zero_on_sdiff ?_ ?_ ?_
    · intro x hx
      exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hx, Finset.mem_image_of_mem _ hx⟩
    · intro x hx
      have hx' : (x.1, x.2) ∉ s := (Finset.mem_sdiff.mp hx).2
      simp only [g', if_neg hx', zero_smul]
    · intro x hx
      have hx' : (x.1, x.2) ∈ s := hx
      simp only [g', if_pos hx']
  have step : ∀ m : σ →₀ ℕ, ∑ b ∈ s.image Prod.snd, (∑ a ∈ s.image Prod.fst, g' a b * coeff m (u a)) • v b = 0 := by
    intro m
    have h1 := congrArg (fun P => coeff m (sumAlgEquiv R σ τ P)) hs'
    simp only [map_sum, map_smul, coeff_sum, coeff_smul, li_key, map_zero, coeff_zero] at h1
    rw [Finset.sum_comm] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun a _ => by rw [mul_smul]
  have hb : ∀ b ∈ s.image Prod.snd, ∀ m : σ →₀ ℕ, ∑ a ∈ s.image Prod.fst, g' a b * coeff m (u a) = 0 :=
    fun b hb m => linearIndependent_iff'.mp hv _ _ (step m) b hb
  have ha : ∀ b ∈ s.image Prod.snd, ∑ a ∈ s.image Prod.fst, g' a b • u a = 0 := by
    intro b hb'
    ext m
    rw [coeff_sum, coeff_zero, ← hb b hb' m]
    exact Finset.sum_congr rfl fun a _ => by rw [coeff_smul, smul_eq_mul]
  have h2 := linearIndependent_iff'.mp hu _ (fun a => g' a x0.2) (ha x0.2 (Finset.mem_image_of_mem _ hx0)) x0.1
    (Finset.mem_image_of_mem _ hx0)
  have hx0' : (x0.1, x0.2) ∈ s := hx0
  simpa only [g', if_pos hx0'] using h2

open Formalism.MainNotions.SelectionLemmas in
/- English proof (translation)
Introduce `_ _ h` and use `(OrderIso.injective _) (Subtype.ext h)`.
-/
theorem li_segE_injective {n' r : ℕ} [NeZero n'] (F : Frames n' r) (j : ℤ) : Function.Injective (segE F j) :=
  fun _ _ h => (OrderIso.injective _) (Subtype.ext h)

open Formalism.MainNotions.SelectionLemmas in

/- English proof (translation)
Establish `hu` using `li_allDeg O (segN F j) r (segLL F j) (fun B => hA2 _ r _ B)`. Establish `hv` using `li_allDeg O (segN F j) K (segLL F j) (fun B => hA2 _ K _ B)`. Establish `hext` using `li_ext _ _ hu hv`. Set `gv : (Fin (segN F j) × Fin r) ⊕ (Fin (segN F j) × Fin K) → ℤ × Fin (r + K)` to `Sum.elim (fun v => (segE F j v.1, Fin.castAdd K v.2)) (fun v => (segE F j v.1, Fin.natAdd r v.2))`. Establish `hg : Function.Injective gv`.

Introduce and unpack `(a | a) (b | b) hab`. Simplify using `only [gv, Sum.elim_inl, Prod.mk.injEq] at hab`. Conclude with `congrArg Sum.inl (Prod.ext (li_segE_injective F j hab.1) (Fin.castAdd_injective _ _ hab.2))`. Simplify using `only [gv, Sum.elim_inl, Sum.elim_inr, Prod.mk.injEq] at hab`. Use `congrArg Fin.val hab.2` as an intermediate fact.

Simplify using `only [Fin.val_castAdd, Fin.val_natAdd] at this`. Use `a.2.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Simplify using `only [gv, Sum.elim_inl, Sum.elim_inr, Prod.mk.injEq] at hab`. Use `congrArg Fin.val hab.2` as an intermediate fact.

Simplify using `only [Fin.val_castAdd, Fin.val_natAdd] at this`. Use `b.2.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Simplify using `only [gv, Sum.elim_inr, Prod.mk.injEq] at hab`. Conclude with `congrArg Sum.inr (Prod.ext (li_segE_injective F j hab.1) (Fin.natAdd_injective _ _ hab.2))`.

Establish `h3` using `hext.map' (rename gv : _ →ₐ[O] _).toLinearMap (LinearMap.ker_eq_bot.mpr (rename_injective gv hg))`. Set `ψ : {x : ((Fin (segN F j + 1) → Fin r → ℤ) × (Fin (segN F j + 1) → Fin K → ℤ)) × ((ℤ → Finset (Fin r)) × (ℤ → Finset (Fin K))) // x.1 ∈ segPairsAll F j K ∧ IsSt x.1.1 x.2.1 ∧ IsSt x.1.2 x.2.2} → li_Idx r (segN F j) (segLL F j) × li_Idx K (segN F j) (segLL F j)` to `fun x => (⟨(x.1.1.1, x.1.2.1), ⟨by obtain ⟨b', _, h1, _⟩ := x.2.1; exact ⟨b', h1⟩, x.2.2.1⟩⟩, ⟨(x.1.1.2, x.1.2.2), ⟨by obtain ⟨_, b'', _, h2⟩ := x.2.1; exact ⟨b'', h2⟩, x.2.2.2⟩⟩)`. Establish `hψ : Function.Injective ψ`. Introduce `x y hxy`. Establish `h1 : (x.1.1.1, x.1.2.1) = (y.1.1.1, y.1.2.1)` using `congrArg (fun z => z.1.1) hxy`.

Establish `h2 : (x.1.1.2, x.1.2.2) = (y.1.1.2, y.1.2.2)` using `congrArg (fun z => z.2.1) hxy`. Simplify using `only [Prod.mk.injEq] at h1 h2`. Conclude with `Subtype.ext (Prod.ext (Prod.ext h1.1 h2.1) (Prod.ext h1.2 h2.2))`. Establish `h4` using `h3.comp ψ hψ`. Establish `e : (fun x : {x : ((Fin (segN F j + 1) → Fin r → ℤ) × (Fin (segN F j + 1) → Fin K → ℤ)) × ((ℤ → Finset (Fin r)) × (ℤ → Finset (Fin K))) // x.1 ∈ segPairsAll F j K ∧ IsSt x.1.1 x.2.1 ∧ IsSt x.1.2 x.2.2} => segRen F j O (r + K) (PsiPl O x.1.1.1 x.1.2.1 * PsiTan O x.1.1.2 x.1.2.2)) …`.

Use function extensionality and compare the values at `x`. Simplify using `only [Function.comp, AlgHom.toLinearMap_apply, map_mul, rename_rename, segRen, PsiPl, PsiTan, ψ]`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `h4`.
-/
theorem space_statement_linear_independent (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hA2 : ∀ (N n : ℕ) [NeZero n] (LL : Letters (Fin N)) (B : Fin N → ℕ),
      LinearIndependent O (fun x : {x : PPath n N LL B × (ℤ → Finset (Fin n)) // IsSt x.1.mu x.2} =>
        Psi O x.1.1.mu x.1.2) ∧
      Submodule.span O {G | ∃ P : PPath n N LL B, ∃ I : ℤ → Finset (Fin n), IsSt P.mu I ∧ G = Psi O P.mu I} =
        Pol O n B)
    (n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (F : Frames n' r) (j : ℤ) :
    LinearIndependent O (fun x : {x : ((Fin (segN F j + 1) → Fin r → ℤ) × (Fin (segN F j + 1) → Fin K → ℤ)) ×
        ((ℤ → Finset (Fin r)) × (ℤ → Finset (Fin K))) //
        x.1 ∈ segPairsAll F j K ∧ IsSt x.1.1 x.2.1 ∧ IsSt x.1.2 x.2.2} =>
      segRen F j O (r + K) (PsiPl O x.1.1.1 x.1.2.1 * PsiTan O x.1.1.2 x.1.2.2)) := by
  have hu := li_allDeg O (segN F j) r (segLL F j) (fun B => hA2 _ r _ B)
  have hv := li_allDeg O (segN F j) K (segLL F j) (fun B => hA2 _ K _ B)
  have hext := li_ext _ _ hu hv
  let gv : (Fin (segN F j) × Fin r) ⊕ (Fin (segN F j) × Fin K) → ℤ × Fin (r + K) :=
    Sum.elim (fun v => (segE F j v.1, Fin.castAdd K v.2)) (fun v => (segE F j v.1, Fin.natAdd r v.2))
  have hg : Function.Injective gv := by
    rintro (a | a) (b | b) hab
    · simp only [gv, Sum.elim_inl, Prod.mk.injEq] at hab
      exact congrArg Sum.inl (Prod.ext (li_segE_injective F j hab.1) (Fin.castAdd_injective _ _ hab.2))
    · simp only [gv, Sum.elim_inl, Sum.elim_inr, Prod.mk.injEq] at hab
      have := congrArg Fin.val hab.2
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      have := a.2.2
      omega
    · simp only [gv, Sum.elim_inl, Sum.elim_inr, Prod.mk.injEq] at hab
      have := congrArg Fin.val hab.2
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      have := b.2.2
      omega
    · simp only [gv, Sum.elim_inr, Prod.mk.injEq] at hab
      exact congrArg Sum.inr (Prod.ext (li_segE_injective F j hab.1) (Fin.natAdd_injective _ _ hab.2))
  have h3 := hext.map' (rename gv : _ →ₐ[O] _).toLinearMap (LinearMap.ker_eq_bot.mpr (rename_injective gv hg))
  let ψ : {x : ((Fin (segN F j + 1) → Fin r → ℤ) × (Fin (segN F j + 1) → Fin K → ℤ)) ×
        ((ℤ → Finset (Fin r)) × (ℤ → Finset (Fin K))) //
        x.1 ∈ segPairsAll F j K ∧ IsSt x.1.1 x.2.1 ∧ IsSt x.1.2 x.2.2} →
      li_Idx r (segN F j) (segLL F j) × li_Idx K (segN F j) (segLL F j) :=
    fun x => (⟨(x.1.1.1, x.1.2.1), ⟨by obtain ⟨b', _, h1, _⟩ := x.2.1; exact ⟨b', h1⟩, x.2.2.1⟩⟩,
      ⟨(x.1.1.2, x.1.2.2), ⟨by obtain ⟨_, b'', _, h2⟩ := x.2.1; exact ⟨b'', h2⟩, x.2.2.2⟩⟩)
  have hψ : Function.Injective ψ := by
    intro x y hxy
    have h1 : (x.1.1.1, x.1.2.1) = (y.1.1.1, y.1.2.1) := congrArg (fun z => z.1.1) hxy
    have h2 : (x.1.1.2, x.1.2.2) = (y.1.1.2, y.1.2.2) := congrArg (fun z => z.2.1) hxy
    simp only [Prod.mk.injEq] at h1 h2
    exact Subtype.ext (Prod.ext (Prod.ext h1.1 h2.1) (Prod.ext h1.2 h2.2))
  have h4 := h3.comp ψ hψ
  have e : (fun x : {x : ((Fin (segN F j + 1) → Fin r → ℤ) × (Fin (segN F j + 1) → Fin K → ℤ)) ×
        ((ℤ → Finset (Fin r)) × (ℤ → Finset (Fin K))) //
        x.1 ∈ segPairsAll F j K ∧ IsSt x.1.1 x.2.1 ∧ IsSt x.1.2 x.2.2} =>
      segRen F j O (r + K) (PsiPl O x.1.1.1 x.1.2.1 * PsiTan O x.1.1.2 x.1.2.2)) =
      ((rename gv : _ →ₐ[O] _).toLinearMap ∘ fun x : li_Idx r (segN F j) (segLL F j) × li_Idx K (segN F j) (segLL F j) =>
        (rename Sum.inl (Psi O x.1.1.1 x.1.1.2) * rename Sum.inr (Psi O x.2.1.1 x.2.1.2) :
          MvPolynomial ((Fin (segN F j) × Fin r) ⊕ (Fin (segN F j) × Fin K)) O)) ∘ ψ := by
    funext x
    simp only [Function.comp, AlgHom.toLinearMap_apply, map_mul, rename_rename, segRen, PsiPl, PsiTan, ψ]
    rfl
  rw [e]
  exact h4

section Sat

open Formalism.MainNotions.SelectionLemmas

/- English proof (translation)
Rewrite `hf` using `[← Finsupp.range_linearCombination]`. Take `⟨c, rfl⟩` from `hf`. Take `⟨l, hl, hle⟩` from `(Finsupp.mem_span_image_iff_linearCombination R).mp haf`. Establish `hlc : l = a • c` using `hv (by rw [hle, map_smul])`. Use `(Finsupp.mem_span_image_iff_linearCombination R).mpr ⟨c, ?_, rfl⟩` and prove the remaining obligations.

Rewrite `hl`, the goal using `[Finsupp.mem_supported]`. Introduce `x hx`. Apply `hl` to reduce the goal to its premises. Establish `hx' : c x ≠ 0` using `Finsupp.mem_support_iff.mp hx`. Rewrite using `[Finset.mem_coe, Finsupp.mem_support_iff, hlc, Finsupp.smul_apply, smul_eq_mul]`.

Conclude with `mul_ne_zero ha hx'`.
-/
theorem sat_li {R M ι : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M] (v : ι → M)
    (hv : LinearIndependent R v) (s : Set ι) (f : M) (hf : f ∈ Submodule.span R (Set.range v)) (a : R) (ha : a ≠ 0)
    (haf : a • f ∈ Submodule.span R (v '' s)) : f ∈ Submodule.span R (v '' s) := by
  rw [← Finsupp.range_linearCombination] at hf
  obtain ⟨c, rfl⟩ := hf
  obtain ⟨l, hl, hle⟩ := (Finsupp.mem_span_image_iff_linearCombination R).mp haf
  have hlc : l = a • c := hv (by rw [hle, map_smul])
  refine (Finsupp.mem_span_image_iff_linearCombination R).mpr ⟨c, ?_, rfl⟩
  rw [Finsupp.mem_supported] at hl ⊢
  intro x hx
  apply hl
  have hx' : c x ≠ 0 := Finsupp.mem_support_iff.mp hx
  rw [Finset.mem_coe, Finsupp.mem_support_iff, hlc, Finsupp.smul_apply, smul_eq_mul]
  exact mul_ne_zero ha hx'

/- English proof (translation)
Take `⟨q, hq⟩` from `h`. Use `exists_rename_eq_of_vars_subset_range f g hg ?_` and prove the remaining obligations. Introduce `i hi`. Establish `hi' : i ∈ (a • f).vars`. Rewrite `hi` using `[Finset.mem_coe, mem_vars_iff_mem_support]`.

Rewrite using `[mem_vars_iff_mem_support]`. Take `⟨d, hd, hid⟩` from `hi`. Conclude with `⟨d, by rwa [support_smul_eq ha], hid⟩`. Rewrite `hi'` using `[← hq]`. Take `⟨x, _, rfl⟩` from `Finset.mem_image.mp (vars_rename g q hi')`.

Conclude with `⟨x, rfl⟩`.
-/
theorem sat_range {R σ τ : Type*} [CommRing R] [IsDomain R] (g : τ → σ) (hg : Function.Injective g)
    (f : MvPolynomial σ R) (a : R) (ha : a ≠ 0) (h : ∃ q, rename g q = a • f) : ∃ q, rename g q = f := by
  classical
  obtain ⟨q, hq⟩ := h
  refine exists_rename_eq_of_vars_subset_range f g hg ?_
  intro i hi
  have hi' : i ∈ (a • f).vars := by
    rw [Finset.mem_coe, mem_vars_iff_mem_support] at hi
    rw [mem_vars_iff_mem_support]
    obtain ⟨d, hd, hid⟩ := hi
    exact ⟨d, by rwa [support_smul_eq ha], hid⟩
  rw [← hq] at hi'
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp (vars_rename g q hi')
  exact ⟨x, rfl⟩

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce `f _`. Proceed by induction on `f using MvPolynomial.induction_on' with`. Consider the case `monomial u a`. Establish `h1 : monomial u a ∈ Pol O n (fun i => multideg u i)`.

Unfold `Pol`. Rewrite using `[mem_restrictSupport_iff]`. Introduce `d hd`. Use `support_monomial_subset hd` as an intermediate fact. Rewrite `this` using `[Finset.mem_singleton]`.

Substitute `this` using the available equality. Introduce `i`. Both sides reduce to the same expression. Rewrite `h1` using `[← hA2]`. Use `Submodule.span_mono ?_ h1` and prove the remaining obligations.

Introduce and unpack `G ⟨P, I, hI, rfl⟩`. Conclude with `⟨_, P, I, hI, rfl⟩`. Consider the case `add p q hp hq => exact Submodule.add_mem _ (hp trivial) (hq trivial)`.
-/
theorem sat_psi_top (O : Type) [CommRing O]
    (N n : ℕ) (LL : Letters (Fin N))
    (hA2 : ∀ B : Fin N → ℕ,
      Submodule.span O {G | ∃ P : PPath n N LL B, ∃ I : ℤ → Finset (Fin n), IsSt P.mu I ∧ G = Psi O P.mu I} =
        Pol O n B) :
    Submodule.span O {G : MvPolynomial (Fin N × Fin n) O | ∃ (B : Fin N → ℕ) (P : PPath n N LL B)
      (I : ℤ → Finset (Fin n)), IsSt P.mu I ∧ G = Psi O P.mu I} = ⊤ := by
  rw [eq_top_iff]
  intro f _
  induction f using MvPolynomial.induction_on' with
  | monomial u a =>
    have h1 : monomial u a ∈ Pol O n (fun i => multideg u i) := by
      unfold Pol
      rw [mem_restrictSupport_iff]
      intro d hd
      have := support_monomial_subset hd
      rw [Finset.mem_singleton] at this
      subst this
      intro i
      rfl
    rw [← hA2] at h1
    refine Submodule.span_mono ?_ h1
    rintro G ⟨P, I, hI, rfl⟩
    exact ⟨_, P, I, hI, rfl⟩
  | add p q hp hq => exact Submodule.add_mem _ (hp trivial) (hq trivial)

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce `f _`. Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C c`. Use `Submodule.subset_span ⟨C c, 1, ?_⟩` and prove the remaining obligations.

Simplify using the standard rewrite rules. Consider the case `add p q hp hq => exact Submodule.add_mem _ (hp trivial) (hq trivial)`. Consider the case `mul_X p v hp`. Establish `hle : Submodule.span O {G : MvPolynomial (Fin N × Fin (r + K)) O | ∃ (a : MvPolynomial (Fin N × Fin r) O) (b : MvPolynomial (Fin N × Fin K) O), G = rename (plVar (K` using `K)) a * rename (tanVar (r := r)) b} ≤ Submodule.comap (LinearMap.mulRight O (X v : MvPolynomial (Fin N × Fin (r + K)) O)) (Submodule.span O {G : MvPolynomial (Fin N × Fin (r + K)) O | ∃ (a : MvPolynomial (Fin N × Fin r) O) (b : MvPolynomial (Fin N × Fin K) O), G = rename (plVar ( …`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `G ⟨a, b, rfl⟩`. Rewrite using `[SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulRight_apply]`. Take `⟨i, c⟩` from `v`. Use `Fin.addCases (fun c' => ?_) (fun c' => ?_) c` and prove the remaining obligations. Use `Submodule.subset_span ⟨a * X (i, c'), b, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, rename_X]`. Simplify using `only [plVar]`. Expand and normalize the polynomial expressions, which then agree. Use `Submodule.subset_span ⟨a, b * X (i, c'), ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, rename_X]`.

Simplify using `only [tanVar]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `hle (hp trivial)`.
-/
theorem sat_prod_top (O : Type) [CommRing O] (N r K : ℕ) :
    Submodule.span O {G : MvPolynomial (Fin N × Fin (r + K)) O | ∃ (a : MvPolynomial (Fin N × Fin r) O)
      (b : MvPolynomial (Fin N × Fin K) O), G = rename (plVar (K := K)) a * rename (tanVar (r := r)) b} = ⊤ := by
  rw [eq_top_iff]
  intro f _
  induction f using MvPolynomial.induction_on with
  | C c =>
    refine Submodule.subset_span ⟨C c, 1, ?_⟩
    simp
  | add p q hp hq => exact Submodule.add_mem _ (hp trivial) (hq trivial)
  | mul_X p v hp =>
    have hle : Submodule.span O {G : MvPolynomial (Fin N × Fin (r + K)) O | ∃ (a : MvPolynomial (Fin N × Fin r) O)
        (b : MvPolynomial (Fin N × Fin K) O), G = rename (plVar (K := K)) a * rename (tanVar (r := r)) b} ≤
        Submodule.comap (LinearMap.mulRight O (X v : MvPolynomial (Fin N × Fin (r + K)) O))
          (Submodule.span O {G : MvPolynomial (Fin N × Fin (r + K)) O | ∃ (a : MvPolynomial (Fin N × Fin r) O)
            (b : MvPolynomial (Fin N × Fin K) O), G = rename (plVar (K := K)) a * rename (tanVar (r := r)) b}) := by
      rw [Submodule.span_le]
      rintro G ⟨a, b, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulRight_apply]
      obtain ⟨i, c⟩ := v
      refine Fin.addCases (fun c' => ?_) (fun c' => ?_) c
      · refine Submodule.subset_span ⟨a * X (i, c'), b, ?_⟩
        rw [map_mul, rename_X]
        simp only [plVar]
        ring
      · refine Submodule.subset_span ⟨a, b * X (i, c'), ?_⟩
        rw [map_mul, rename_X]
        simp only [tanVar]
        ring
    exact hle (hp trivial)

/- English proof (translation)
Use `set X0 := Formalism.MainNotions.CovariantDegrees.XXZ O {q : (Fin (N + 1) → Fin r → ℤ) × (Fin (N + 1) → Fin K → ℤ) | ∃ b' b'' : Fin N → ℕ, (∃ P1 : PPath r N LL b', P1.mu = q.1) ∧ ∃ P2 : PPath K N LL b'', P2.mu = q.2} with hX0`. Establish `h1 : ∀ (b'' : Fin N → ℕ) (P2 : PPath K N LL b'') (I'' : ℤ → Finset (Fin K)), IsSt P2.mu I'' → ∀ a : MvPolynomial (Fin N × Fin r) O, rename (plVar (K` using `K)) a * rename (tanVar (r := r)) (Psi O P2.mu I'') ∈ X0 := by`. Introduce `b'' P2 I'' hI'' a`. Establish `hle : Submodule.span O {G : MvPolynomial (Fin N × Fin r) O | ∃ (B : Fin N → ℕ) (P : PPath r N LL B) (I : ℤ → Finset (Fin r)), IsSt P.mu I ∧ G = Psi O P.mu I} ≤ Submodule.comap ((LinearMap.mulRight O (rename (tanVar (r` using `r)) (Psi O P2.mu I''))) ∘ₗ (rename (plVar (K := K)) : MvPolynomial (Fin N × Fin r) O →ₐ[O] _).toLinearMap) X0 := by`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `G ⟨b', P1, I', hI', rfl⟩`. Conclude with `Submodule.subset_span ⟨(P1.mu, P2.mu), ⟨b', b'', ⟨P1, rfl⟩, ⟨P2, rfl⟩⟩, I', I'', hI', hI'', rfl⟩`. Use `hle (by rw [sat_psi_top O N r LL hr]; trivial : a ∈ _)` as an intermediate fact. Conclude with `this`. Establish `h2 : ∀ (a : MvPolynomial (Fin N × Fin r) O) (b : MvPolynomial (Fin N × Fin K) O), rename (plVar (K` using `K)) a * rename (tanVar (r := r)) b ∈ X0 := by`.

Introduce `a b`. Establish `hle : Submodule.span O {G : MvPolynomial (Fin N × Fin K) O | ∃ (B : Fin N → ℕ) (P : PPath K N LL B) (I : ℤ → Finset (Fin K)), IsSt P.mu I ∧ G = Psi O P.mu I} ≤ Submodule.comap ((LinearMap.mulLeft O (rename (plVar (K` using `K)) a)) ∘ₗ (rename (tanVar (r := r)) : MvPolynomial (Fin N × Fin K) O →ₐ[O] _).toLinearMap) X0 := by`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `G ⟨b'', P2, I'', hI'', rfl⟩`. Conclude with `h1 b'' P2 I'' hI'' a`.

Use `hle (by rw [sat_psi_top O N K LL hK]; trivial : b ∈ _)` as an intermediate fact. Conclude with `this`. Rewrite using `[eq_top_iff, ← sat_prod_top O N r K, Submodule.span_le]`. Introduce and unpack `G ⟨a, b, rfl⟩`. Conclude with `h2 a b`.
-/
theorem sat_words_top (O : Type) [CommRing O] (N r K : ℕ) (LL : Letters (Fin N))
    (hr : ∀ B : Fin N → ℕ,
      Submodule.span O {G | ∃ P : PPath r N LL B, ∃ I : ℤ → Finset (Fin r), IsSt P.mu I ∧ G = Psi O P.mu I} =
        Pol O r B)
    (hK : ∀ B : Fin N → ℕ,
      Submodule.span O {G | ∃ P : PPath K N LL B, ∃ I : ℤ → Finset (Fin K), IsSt P.mu I ∧ G = Psi O P.mu I} =
        Pol O K B) :
    Formalism.MainNotions.CovariantDegrees.XXZ O {q : (Fin (N + 1) → Fin r → ℤ) × (Fin (N + 1) → Fin K → ℤ) |
      ∃ b' b'' : Fin N → ℕ, (∃ P1 : PPath r N LL b', P1.mu = q.1) ∧ ∃ P2 : PPath K N LL b'', P2.mu = q.2} = ⊤ := by
  set X0 := Formalism.MainNotions.CovariantDegrees.XXZ O {q : (Fin (N + 1) → Fin r → ℤ) × (Fin (N + 1) → Fin K → ℤ) |
      ∃ b' b'' : Fin N → ℕ, (∃ P1 : PPath r N LL b', P1.mu = q.1) ∧ ∃ P2 : PPath K N LL b'', P2.mu = q.2} with hX0

  have h1 : ∀ (b'' : Fin N → ℕ) (P2 : PPath K N LL b'') (I'' : ℤ → Finset (Fin K)), IsSt P2.mu I'' →
      ∀ a : MvPolynomial (Fin N × Fin r) O,
        rename (plVar (K := K)) a * rename (tanVar (r := r)) (Psi O P2.mu I'') ∈ X0 := by
    intro b'' P2 I'' hI'' a
    have hle : Submodule.span O {G : MvPolynomial (Fin N × Fin r) O | ∃ (B : Fin N → ℕ) (P : PPath r N LL B)
        (I : ℤ → Finset (Fin r)), IsSt P.mu I ∧ G = Psi O P.mu I} ≤
        Submodule.comap ((LinearMap.mulRight O (rename (tanVar (r := r)) (Psi O P2.mu I''))) ∘ₗ
          (rename (plVar (K := K)) : MvPolynomial (Fin N × Fin r) O →ₐ[O] _).toLinearMap) X0 := by
      rw [Submodule.span_le]
      rintro G ⟨b', P1, I', hI', rfl⟩
      exact Submodule.subset_span ⟨(P1.mu, P2.mu), ⟨b', b'', ⟨P1, rfl⟩, ⟨P2, rfl⟩⟩, I', I'', hI', hI'', rfl⟩
    have := hle (by rw [sat_psi_top O N r LL hr]; trivial : a ∈ _)
    exact this
  have h2 : ∀ (a : MvPolynomial (Fin N × Fin r) O) (b : MvPolynomial (Fin N × Fin K) O),
      rename (plVar (K := K)) a * rename (tanVar (r := r)) b ∈ X0 := by
    intro a b
    have hle : Submodule.span O {G : MvPolynomial (Fin N × Fin K) O | ∃ (B : Fin N → ℕ) (P : PPath K N LL B)
        (I : ℤ → Finset (Fin K)), IsSt P.mu I ∧ G = Psi O P.mu I} ≤
        Submodule.comap ((LinearMap.mulLeft O (rename (plVar (K := K)) a)) ∘ₗ
          (rename (tanVar (r := r)) : MvPolynomial (Fin N × Fin K) O →ₐ[O] _).toLinearMap) X0 := by
      rw [Submodule.span_le]
      rintro G ⟨b'', P2, I'', hI'', rfl⟩
      exact h1 b'' P2 I'' hI'' a
    have := hle (by rw [sat_psi_top O N K LL hK]; trivial : b ∈ _)
    exact this
  rw [eq_top_iff, ← sat_prod_top O N r K, Submodule.span_le]
  rintro G ⟨a, b, rfl⟩
  exact h2 a b

/- English proof (translation)
Introduce `a b h`. Unfold `segE at h`. Conclude with `((F.letters j).orderIsoOfFin rfl).injective (Subtype.ext h)`.
-/
theorem sat_segE_injective {n' r : ℕ} [NeZero n'] (F : Frames n' r) (j : ℤ) : Function.Injective (segE F j) := by
  intro a b h
  unfold segE at h
  exact ((F.letters j).orderIsoOfFin rfl).injective (Subtype.ext h)

/- English proof (translation)
Introduce `f a ha haf`. Use `set v := (fun x : {x : ((Fin (segN F j + 1) → Fin r → ℤ) × (Fin (segN F j + 1) → Fin K → ℤ)) × ((ℤ → Finset (Fin r)) × (ℤ → Finset (Fin K))) // x.1 ∈ segPairsAll F j K ∧ IsSt x.1.1 x.2.1 ∧ IsSt x.1.2 x.2.2} => segRen F j O (r + K) (PsiPl O x.1.1.1 x.1.2.1 * PsiTan O x.1.1.2 x.1.2 …`. Establish `hsub : segPairs F j K m th o ⊆ segPairsAll F j K`. Introduce and unpack `q ⟨b', b'', hP1, hP2, -⟩`. Conclude with `⟨b', b'', hP1, hP2⟩`.

Establish `hXX : XX' O r K F j m th o = Submodule.span O (v '' {x | x.1.1 ∈ segPairs F j K m th o})`. Rewrite using `[h1, Formalism.MainNotions.CovariantDegrees.XXZ, Submodule.map_span]`. Use `congr 1`. Use extensionality with `G`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨_, ⟨q, hq, I', I'', hI', hI'', rfl⟩, rfl⟩`. Conclude with `⟨⟨(q, (I', I'')), hsub hq, hI', hI''⟩, hq, rfl⟩`. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨_, ⟨x.1.1, hx, x.1.2.1, x.1.2.2, x.2.2.1, x.2.2.2, rfl⟩, rfl⟩`. Establish `hg : Function.Injective (fun w : Fin (segN F j) × Fin (r + K) => (segE F j w.1, w.2))`.

Introduce `x y h`. Simplify using `only [Prod.mk.injEq] at h`. Conclude with `Prod.ext (sat_segE_injective F j h.1) h.2`. Establish `hr : ∃ q, rename (fun w : Fin (segN F j) × Fin (r + K) => (segE F j w.1, w.2)) q = f`. Use `sat_range _ hg f a ha ?_` and prove the remaining obligations.

Rewrite `haf` using `[h1]`. Take `⟨q, _, hq⟩` from `haf`. Conclude with `⟨q, hq⟩`. Take `⟨f₀, hf₀⟩` from `hr`. Establish `htop` using `sat_words_top O (segN F j) r K (segLL F j) (fun B => (hA2 _ r _ B).2) (fun B => (hA2 _ K _ B).2)`.

Establish `hf : f ∈ Submodule.span O (Set.range v)`. Establish `h0 : f₀ ∈ Formalism.MainNotions.CovariantDegrees.XXZ O (segPairsAll F j K)`. Unfold `segPairsAll`. Rewrite using `[htop]`. Discharge the goal by the elementary cases of `trivial`.

Establish `h3 : f ∈ Submodule.map (segRen F j O (r + K)).toLinearMap (Formalism.MainNotions.CovariantDegrees.XXZ O (segPairsAll F j K))` using `⟨f₀, h0, hf₀⟩`. Rewrite `h3` using `[Formalism.MainNotions.CovariantDegrees.XXZ, Submodule.map_span]`. Use `Submodule.span_mono ?_ h3` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨q, hq, I', I'', hI', hI'', rfl⟩, rfl⟩`. Conclude with `⟨⟨(q, (I', I'')), hq, hI', hI''⟩, rfl⟩`.

Rewrite `haf`, the goal using `[hXX]`. Conclude with `sat_li v h2 _ f hf a ha haf`.
-/
theorem space_statement_saturated (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hA2 : ∀ (N n : ℕ) [NeZero n] (LL : Letters (Fin N)) (B : Fin N → ℕ),
      LinearIndependent O (fun x : {x : PPath n N LL B × (ℤ → Finset (Fin n)) // IsSt x.1.mu x.2} =>
        Psi O x.1.1.mu x.1.2) ∧
      Submodule.span O {G | ∃ P : PPath n N LL B, ∃ I : ℤ → Finset (Fin n), IsSt P.mu I ∧ G = Psi O P.mu I} =
        Pol O n B)
    (n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (F : Frames n' r) (j : ℤ) (m : ℤ → ℤ) (th o : ℤ → ℝ)
    (h1 : XX' O r K F j m th o =
      Submodule.map (segRen F j O (r + K)).toLinearMap (Formalism.MainNotions.CovariantDegrees.XXZ O (segPairs F j K m th o)))
    (h2 : LinearIndependent O (fun x : {x : ((Fin (segN F j + 1) → Fin r → ℤ) × (Fin (segN F j + 1) → Fin K → ℤ)) ×
        ((ℤ → Finset (Fin r)) × (ℤ → Finset (Fin K))) //
        x.1 ∈ segPairsAll F j K ∧ IsSt x.1.1 x.2.1 ∧ IsSt x.1.2 x.2.2} =>
      segRen F j O (r + K) (PsiPl O x.1.1.1 x.1.2.1 * PsiTan O x.1.1.2 x.1.2.2))) :
    Formalism.MainNotions.CovariantDegrees.Saturated (XX' O r K F j m th o) := by
  intro f a ha haf
  set v := (fun x : {x : ((Fin (segN F j + 1) → Fin r → ℤ) × (Fin (segN F j + 1) → Fin K → ℤ)) ×
        ((ℤ → Finset (Fin r)) × (ℤ → Finset (Fin K))) //
        x.1 ∈ segPairsAll F j K ∧ IsSt x.1.1 x.2.1 ∧ IsSt x.1.2 x.2.2} =>
      segRen F j O (r + K) (PsiPl O x.1.1.1 x.1.2.1 * PsiTan O x.1.1.2 x.1.2.2)) with hv
  have hsub : segPairs F j K m th o ⊆ segPairsAll F j K := by
    rintro q ⟨b', b'', hP1, hP2, -⟩
    exact ⟨b', b'', hP1, hP2⟩

  have hXX : XX' O r K F j m th o = Submodule.span O (v '' {x | x.1.1 ∈ segPairs F j K m th o}) := by
    rw [h1, Formalism.MainNotions.CovariantDegrees.XXZ, Submodule.map_span]
    congr 1
    ext G
    constructor
    · rintro ⟨_, ⟨q, hq, I', I'', hI', hI'', rfl⟩, rfl⟩
      exact ⟨⟨(q, (I', I'')), hsub hq, hI', hI''⟩, hq, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, ⟨x.1.1, hx, x.1.2.1, x.1.2.2, x.2.2.1, x.2.2.2, rfl⟩, rfl⟩

  have hg : Function.Injective (fun w : Fin (segN F j) × Fin (r + K) => (segE F j w.1, w.2)) := by
    intro x y h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (sat_segE_injective F j h.1) h.2
  have hr : ∃ q, rename (fun w : Fin (segN F j) × Fin (r + K) => (segE F j w.1, w.2)) q = f := by
    refine sat_range _ hg f a ha ?_
    rw [h1] at haf
    obtain ⟨q, _, hq⟩ := haf
    exact ⟨q, hq⟩
  obtain ⟨f₀, hf₀⟩ := hr

  have htop := sat_words_top O (segN F j) r K (segLL F j) (fun B => (hA2 _ r _ B).2) (fun B => (hA2 _ K _ B).2)
  have hf : f ∈ Submodule.span O (Set.range v) := by
    have h0 : f₀ ∈ Formalism.MainNotions.CovariantDegrees.XXZ O (segPairsAll F j K) := by
      unfold segPairsAll
      rw [htop]; trivial
    have h3 : f ∈ Submodule.map (segRen F j O (r + K)).toLinearMap (Formalism.MainNotions.CovariantDegrees.XXZ O (segPairsAll F j K)) :=
      ⟨f₀, h0, hf₀⟩
    rw [Formalism.MainNotions.CovariantDegrees.XXZ, Submodule.map_span] at h3
    refine Submodule.span_mono ?_ h3
    rintro _ ⟨_, ⟨q, hq, I', I'', hI', hI'', rfl⟩, rfl⟩
    exact ⟨⟨(q, (I', I'')), hq, hI', hI''⟩, rfl⟩
  rw [hXX] at haf ⊢
  exact sat_li v h2 _ f hf a ha haf

end Sat

/- English proof (translation)
Unfold `extOne`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem lift_extOne_map {n : ℕ} {P P' : Type} [CommRing P] [CommRing P'] (g : P →+* P') (J : Finset (Fin n)) :
    g (extOne J) = extOne J := by
  unfold extOne
  split_ifs <;> simp

/- English proof (translation)
Simplify using `[wedgeR, map_sum]`.
-/
theorem lift_wedgeR_map {n : ℕ} {P P' : Type} [CommRing P] [CommRing P'] (g : P →+* P') (x : Fin n → P)
    (K : Finset (Fin n) → P) (J : Finset (Fin n)) :
    g (wedgeR x K J) = wedgeR (fun m => g (x m)) (fun J => g (K J)) J := by
  simp [wedgeR, map_sum]

/- English proof (translation)
Simplify using `[contrR, map_sum]`.
-/
theorem lift_contrR_map {n : ℕ} {P P' : Type} [CommRing P] [CommRing P'] (g : P →+* P') (x : Fin n → P)
    (K : Finset (Fin n) → P) (J : Finset (Fin n)) :
    g (contrR x K J) = contrR (fun m => g (x m)) (fun J => g (K J)) J := by
  simp [contrR, map_sum]

/- English proof (translation)
Unfold `colStep`. Use `split_ifs`. Conclude with `lift_wedgeR_map g x K J`. Conclude with `lift_contrR_map g x K J`. Conclude with `lift_contrR_map g x K J`.

Conclude with `lift_wedgeR_map g x K J`. Both sides reduce to the same expression.
-/
theorem lift_colStep_map {n : ℕ} {P P' : Type} [CommRing P] [CommRing P'] (g : P →+* P') (c : ℤ) (hP hN : ℕ)
    (x : Fin n → P) (K : Finset (Fin n) → P) (J : Finset (Fin n)) :
    g (colStep c hP hN x K J) = colStep c hP hN (fun m => g (x m)) (fun J => g (K J)) J := by
  unfold colStep
  split_ifs
  · exact lift_wedgeR_map g x K J
  · exact lift_contrR_map g x K J
  · exact lift_contrR_map g x K J
  · exact lift_wedgeR_map g x K J
  · rfl

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => intro J`. Conclude with `lift_extOne_map _ J`. Consider the case `succ j ih`. Introduce `J`.

Simplify using `only [Kcol]`. Use `split_ifs with h`. Establish `e1 : (fun m => MvPolynomial.map f (letVec R (N` using `N) (n := n) ⟨j, h⟩ m)) = letVec R' ⟨j, h⟩ := by`. Use function extensionality and compare the values at `m`. Simplify using `[letVec]`.

Establish `e2 : (fun J => MvPolynomial.map f (Kcol R mu c j J)) = Kcol R' mu c j` using `funext ih`. Rewrite using `[lift_colStep_map, e1, e2]`. Conclude with `ih J`.
-/
theorem lift_Kcol_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {N n : ℕ}
    (mu : Fin (N + 1) → Fin n → ℤ) (c : ℤ) (j : ℕ) :
    ∀ J : Finset (Fin n), MvPolynomial.map f (Kcol R mu c j J) = Kcol R' mu c j J := by
  induction j with
  | zero => intro J; exact lift_extOne_map _ J
  | succ j ih =>
    intro J
    simp only [Kcol]
    split_ifs with h
    · have e1 : (fun m => MvPolynomial.map f (letVec R (N := N) (n := n) ⟨j, h⟩ m)) = letVec R' ⟨j, h⟩ := by
        funext m; simp [letVec]
      have e2 : (fun J => MvPolynomial.map f (Kcol R mu c j J)) = Kcol R' mu c j := funext ih
      rw [lift_colStep_map, e1, e2]
    · exact ih J

/- English proof (translation)
Unfold `Psi`. Rewrite using `[map_prod]`. Conclude with `Finset.prod_congr rfl fun c _ => lift_Kcol_map f mu c N (I c)`.
-/
theorem Psi_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {N n : ℕ}
    (mu : Fin (N + 1) → Fin n → ℤ) (I : ℤ → Finset (Fin n)) :
    MvPolynomial.map f (Psi R mu I) = Psi R' mu I := by
  unfold Psi
  rw [map_prod]
  exact Finset.prod_congr rfl fun c _ => lift_Kcol_map f mu c N (I c)

/- English proof (translation)
Unfold `PsiPl`. Rewrite using `[map_rename, Psi_map]`.
-/
theorem PsiPl_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {N r K : ℕ}
    (nu : Fin (N + 1) → Fin r → ℤ) (I : ℤ → Finset (Fin r)) :
    MvPolynomial.map f (PsiPl (K := K) R nu I) = PsiPl (K := K) R' nu I := by
  unfold PsiPl
  rw [map_rename, Psi_map]

/- English proof (translation)
Unfold `PsiTan`. Rewrite using `[map_rename, Psi_map]`.
-/
theorem PsiTan_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {N r K : ℕ}
    (ka : Fin (N + 1) → Fin K → ℤ) (I : ℤ → Finset (Fin K)) :
    MvPolynomial.map f (PsiTan (r := r) R ka I) = PsiTan (r := r) R' ka I := by
  unfold PsiTan
  rw [map_rename, Psi_map]

/- English proof (translation)
Introduce `y hy`. Unfold `Formalism.MainNotions.CovariantDegrees.XXZ at hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem G hG`. Take `⟨q, hq, I', I'', h1, h2, rfl⟩` from `hG`.

Use `⟨PsiPl O q.1 I' * PsiTan O q.2 I'', Submodule.subset_span ⟨q, hq, I', I'', h1, h2, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, PsiPl_map, PsiTan_map]`. Consider the case `zero => exact ⟨0, Submodule.zero_mem _, map_zero _⟩`. Consider the case `add u v _ _ hu hv`. Take `⟨x1, hx1, rfl⟩` from `hu`.

Take `⟨x2, hx2, rfl⟩` from `hv`. Conclude with `⟨x1 + x2, Submodule.add_mem _ hx1 hx2, map_add _ _ _⟩`. Consider the case `smul a u _ hu`. Take `⟨x1, hx1, rfl⟩` from `hu`. Take `⟨a', rfl⟩` from `IsLocalRing.residue_surjective a`.

Use `⟨a' • x1, Submodule.smul_mem _ _ hx1, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]`.
-/
theorem XXZ_lift (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {N r K : ℕ}
    (PP : Set ((Fin (N + 1) → Fin r → ℤ) × (Fin (N + 1) → Fin K → ℤ))) :
    ∀ y ∈ Formalism.MainNotions.CovariantDegrees.XXZ (FF O) PP, ∃ x ∈ Formalism.MainNotions.CovariantDegrees.XXZ O PP, MvPolynomial.map (IsLocalRing.residue O) x = y := by
  intro y hy
  unfold Formalism.MainNotions.CovariantDegrees.XXZ at hy
  induction hy using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨q, hq, I', I'', h1, h2, rfl⟩ := hG
    refine ⟨PsiPl O q.1 I' * PsiTan O q.2 I'', Submodule.subset_span ⟨q, hq, I', I'', h1, h2, rfl⟩, ?_⟩
    rw [map_mul, PsiPl_map, PsiTan_map]
  | zero => exact ⟨0, Submodule.zero_mem _, map_zero _⟩
  | add u v _ _ hu hv =>
    obtain ⟨x1, hx1, rfl⟩ := hu
    obtain ⟨x2, hx2, rfl⟩ := hv
    exact ⟨x1 + x2, Submodule.add_mem _ hx1 hx2, map_add _ _ _⟩
  | smul a u _ hu =>
    obtain ⟨x1, hx1, rfl⟩ := hu
    obtain ⟨a', rfl⟩ := IsLocalRing.residue_surjective a
    refine ⟨a' • x1, Submodule.smul_mem _ _ hx1, ?_⟩
    rw [smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]

open Formalism.MainNotions.SelectionLemmas in

/- English proof (translation)
Introduce `A G M hA hG hc ho`. Take `⟨y, hy, hyeq⟩` from `hcrit A G M hA hG hc ho`. Take `⟨x, hx, rfl⟩` from `XXZ_lift O _ y hy`. Use `⟨segRen F j O (r + K) x, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[h1]`.

Conclude with `Submodule.mem_map_of_mem hx`. Rewrite using `[← hyeq]`. Simplify using `only [segRen, AlgHom.toLinearMap_apply]`. Rewrite using `[map_rename]`.
-/
theorem space_statement_sixth_clause (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n' r K : ℕ) [NeZero n']
    [NeZero r] [NeZero K] (F : Frames n' r) (j : ℤ) (m : ℤ → ℤ) (th o : ℤ → ℝ)
    (h1 : XX' O r K F j m th o =
      Submodule.map (segRen F j O (r + K)).toLinearMap (Formalism.MainNotions.CovariantDegrees.XXZ O (segPairs F j K m th o)))
    (hcrit : ∀ (A : MvPolynomial (ℤ × Fin r) (FF O)) (G : MvPolynomial (ℤ × Fin K) (FF O)) (M : ℤ → ℤ),
      A ∈ supported (FF O) {v : ℤ × Fin r | v.1 ∈ F.letters j} →
      G ∈ supported (FF O) {v : ℤ × Fin K | v.1 ∈ F.letters j ∧ ¬ F.IsW j v.1} →
      (∀ x ∈ F.letters j, ¬ F.IsW j x →
        (Even x → lam1S LZ {y | y ≤ x} G ≤ ((M x : ℤ) : WithBot ℤ) ∧
            ((M x + m x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y < x} A) ∧
        (¬ Even x → lam1S LZ {y | y < x} G ≤ ((M x : ℤ) : WithBot ℤ) ∧
            ((M x + m x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y ≤ x} A) ∧
        geR (valS LZ {y | y < x} A) (th x)) →
      (∀ mm ∈ (plEmb (FF O) r K A * nmEmb (FF O) r K G).support, ∀ x ∈ F.letters j, ¬ F.IsW j x →
        (ordDeg mm x : ℝ) ≤ o x) →
      plEmb (FF O) r K A * nmEmb (FF O) r K G ∈
        Submodule.map (segRen F j (FF O) (r + K)).toLinearMap (Formalism.MainNotions.CovariantDegrees.XXZ (FF O) (segPairs F j K m th o))) :
    ∀ (A : MvPolynomial (ℤ × Fin r) (FF O)) (G : MvPolynomial (ℤ × Fin K) (FF O)) (M : ℤ → ℤ),
      A ∈ supported (FF O) {v : ℤ × Fin r | v.1 ∈ F.letters j} →
      G ∈ supported (FF O) {v : ℤ × Fin K | v.1 ∈ F.letters j ∧ ¬ F.IsW j v.1} →
      (∀ x ∈ F.letters j, ¬ F.IsW j x →
        (Even x → lam1S LZ {y | y ≤ x} G ≤ ((M x : ℤ) : WithBot ℤ) ∧
            ((M x + m x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y < x} A) ∧
        (¬ Even x → lam1S LZ {y | y < x} G ≤ ((M x : ℤ) : WithBot ℤ) ∧
            ((M x + m x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y ≤ x} A) ∧
        geR (valS LZ {y | y < x} A) (th x)) →
      (∀ mm ∈ (plEmb (FF O) r K A * nmEmb (FF O) r K G).support, ∀ x ∈ F.letters j, ¬ F.IsW j x →
        (ordDeg mm x : ℝ) ≤ o x) →
      ∃ P ∈ XX' O r K F j m th o,
        MvPolynomial.map (IsLocalRing.residue O) P = plEmb (FF O) r K A * nmEmb (FF O) r K G := by
  intro A G M hA hG hc ho
  obtain ⟨y, hy, hyeq⟩ := hcrit A G M hA hG hc ho
  obtain ⟨x, hx, rfl⟩ := XXZ_lift O _ y hy
  refine ⟨segRen F j O (r + K) x, ?_, ?_⟩
  · rw [h1]
    exact Submodule.mem_map_of_mem hx
  · rw [← hyeq]
    simp only [segRen, AlgHom.toLinearMap_apply]
    rw [map_rename]

section Fin1

open Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.CovariantDegrees

def SpaceStatementAtRing (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : Prop :=
  ∀ (n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K]
    (F : Frames n' r) (L₁ N₁ : ℕ) (j : ℤ) (m : ℤ → ℤ) (th o : ℤ → ℝ),
  F.Valid L₁ N₁ → segN F j + r ≤ K → (∀ x, 0 ≤ m x) →
  XX' O r K F j m th o =
    Submodule.map (segRen F j O (r + K)).toLinearMap (Formalism.MainNotions.CovariantDegrees.XXZ O (segPairs F j K m th o)) ∧
  LinearIndependent O (fun x : {x : ((Fin (segN F j + 1) → Fin r → ℤ) × (Fin (segN F j + 1) → Fin K → ℤ)) ×
        ((ℤ → Finset (Fin r)) × (ℤ → Finset (Fin K))) //
        x.1 ∈ segPairsAll F j K ∧ IsSt x.1.1 x.2.1 ∧ IsSt x.1.2 x.2.2} =>
      segRen F j O (r + K) (PsiPl O x.1.1.1 x.1.2.1 * PsiTan O x.1.1.2 x.1.2.2)) ∧
  Formalism.MainNotions.CovariantDegrees.Saturated (XX' O r K F j m th o) ∧
  (CharZero O → (XX' O r K F j m th o : Set (SegRing O r K)) =
    {f | MvPolynomial.map (algebraMap O (KK O)) f ∈ Submodule.map (segRen F j (KK O) (r + K)).toLinearMap
      (⨆ q ∈ segPairs F j K m th o, Formalism.MainNotions.CovariantDegrees.jointType (KK O) (segLL F j) q.1 q.2)}) ∧
  (∀ (A : MvPolynomial (ℤ × Fin r) O) (G : MvPolynomial (ℤ × Fin K) O) (M : ℤ → ℤ),
    A ∈ supported O {v : ℤ × Fin r | v.1 ∈ F.letters j} →
    G ∈ supported O {v : ℤ × Fin K | v.1 ∈ F.letters j ∧ ¬ F.IsW j v.1} →
    (∀ x ∈ F.letters j, ¬ F.IsW j x →
      (Even x → lam1S LZ {y | y ≤ x} G ≤ ((M x : ℤ) : WithBot ℤ) ∧
          ((M x + m x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y < x} A) ∧
      (¬ Even x → lam1S LZ {y | y < x} G ≤ ((M x : ℤ) : WithBot ℤ) ∧
          ((M x + m x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y ≤ x} A) ∧
      geR (valS LZ {y | y < x} A) (th x)) →
    (∀ mm ∈ (plEmb O r K A * nmEmb O r K G).support, ∀ x ∈ F.letters j, ¬ F.IsW j x → (ordDeg mm x : ℝ) ≤ o x) →
    plEmb O r K A * nmEmb O r K G ∈ XX' O r K F j m th o) ∧
  (∀ (A : MvPolynomial (ℤ × Fin r) (FF O)) (G : MvPolynomial (ℤ × Fin K) (FF O)) (M : ℤ → ℤ),
    A ∈ supported (FF O) {v : ℤ × Fin r | v.1 ∈ F.letters j} →
    G ∈ supported (FF O) {v : ℤ × Fin K | v.1 ∈ F.letters j ∧ ¬ F.IsW j v.1} →
    (∀ x ∈ F.letters j, ¬ F.IsW j x →
      (Even x → lam1S LZ {y | y ≤ x} G ≤ ((M x : ℤ) : WithBot ℤ) ∧
          ((M x + m x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y < x} A) ∧
      (¬ Even x → lam1S LZ {y | y < x} G ≤ ((M x : ℤ) : WithBot ℤ) ∧
          ((M x + m x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y ≤ x} A) ∧
      geR (valS LZ {y | y < x} A) (th x)) →
    (∀ mm ∈ (plEmb (FF O) r K A * nmEmb (FF O) r K G).support, ∀ x ∈ F.letters j, ¬ F.IsW j x →
      (ordDeg mm x : ℝ) ≤ o x) →
    ∃ P ∈ XX' O r K F j m th o,
      MvPolynomial.map (IsLocalRing.residue O) P = plEmb (FF O) r K A * nmEmb (FF O) r K G)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem space_statement_iff_forall_dvr (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.SelectionLemmas.NestedTypeBound D ↔
    ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O),
      SpaceStatementAtRing O := Iff.rfl

def StandardBasisAllData (R : Type) [CommRing R] : Prop :=
  ∀ (N n : ℕ) [NeZero n] (LL : Letters (Fin N)) (B : Fin N → ℕ) (th M : Fin N → ℤ), A3at R N n LL B th M

def FourthClauseAtRing (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : Prop :=
  ∀ (n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K]
    (F : Frames n' r) (L₁ N₁ : ℕ) (j : ℤ) (m : ℤ → ℤ) (th o : ℤ → ℝ),
  F.Valid L₁ N₁ → segN F j + r ≤ K → (∀ x, 0 ≤ m x) →
  (CharZero O → (XX' O r K F j m th o : Set (SegRing O r K)) =
    {f | MvPolynomial.map (algebraMap O (KK O)) f ∈ Submodule.map (segRen F j (KK O) (r + K)).toLinearMap
      (⨆ q ∈ segPairs F j K m th o, Formalism.MainNotions.CovariantDegrees.jointType (KK O) (segLL F j) q.1 q.2)})

/- English proof (translation)
Introduce `n' r K _ _ _ F L₁ N₁ j m th o hV hK hm`. Establish `h1` using `first_clause_segment_rename (K := K) F j O h3 m th o`. Establish `h2` using `space_statement_linear_independent O hA2 n' r K F j`. Conclude with `⟨h1, h2, space_statement_saturated O hA2 n' r K F j m th o h1 h2, h4 n' r K F L₁ N₁ j m th o hV hK hm, fun A G M hA hG hc ho => space_criterion_clause O n' r K F j m th o A G M hA hG hc ho, space_statement_sixth_clause O n' r K F j m th o h1 (fun A G M hA hG hc ho => crit_words F …`.
-/
theorem space_statement_at_ring_of_basis (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hA2 : ∀ (N n : ℕ) [NeZero n] (LL : Letters (Fin N)) (B : Fin N → ℕ),
      LinearIndependent O (fun x : {x : PPath n N LL B × (ℤ → Finset (Fin n)) // IsSt x.1.mu x.2} =>
        Psi O x.1.1.mu x.1.2) ∧
      Submodule.span O {G | ∃ P : PPath n N LL B, ∃ I : ℤ → Finset (Fin n), IsSt P.mu I ∧ G = Psi O P.mu I} =
        Pol O n B)
    (h3 : StandardBasisAllData O) (h3F : StandardBasisAllData (FF O)) (h4 : FourthClauseAtRing O) : SpaceStatementAtRing O := by
  intro n' r K _ _ _ F L₁ N₁ j m th o hV hK hm
  have h1 := first_clause_segment_rename (K := K) F j O h3 m th o
  have h2 := space_statement_linear_independent O hA2 n' r K F j
  exact ⟨h1, h2, space_statement_saturated O hA2 n' r K F j m th o h1 h2, h4 n' r K F L₁ N₁ j m th o hV hK hm,
    fun A G M hA hG hc ho => space_criterion_clause O n' r K F j m th o A G M hA hG hc ho,
    space_statement_sixth_clause O n' r K F j m th o h1
      (fun A G M hA hG hc ho => crit_words F j (FF O) h3F m th o A G M hA hG hc ho)⟩

end Fin1

section Comb

open Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.CovariantDegrees

/- English proof (translation)
Use function extensionality and compare the values at `i`. Establish `h1` using `P.step i`. Establish `h2` using `P'.step i`. Rewrite `h2` using `[← h]`. Distinguish the cases in `hv : LL.vec i = true`.

Rewrite `h1`, `h2` using `[if_pos hv]`. Use `h1.2.2.symm.trans h2.2.2` as an intermediate fact. Conclude with `this` after adjusting the coercions. Rewrite `h1`, `h2` using `[if_neg hv]`. Use `h1.2.2.symm.trans h2.2.2` as an intermediate fact.

Conclude with `this` after adjusting the coercions.
-/
theorem comb_deg_unique {n N : ℕ} {LL : Letters (Fin N)} {b c : Fin N → ℕ} (P : PPath n N LL b)
    (P' : PPath n N LL c) (h : P.mu = P'.mu) : b = c := by
  funext i
  have h1 := P.step i
  have h2 := P'.step i
  rw [← h] at h2
  by_cases hv : LL.vec i = true
  · rw [if_pos hv] at h1 h2
    have := h1.2.2.symm.trans h2.2.2
    exact_mod_cast this
  · rw [if_neg hv] at h1 h2
    have := h1.2.2.symm.trans h2.2.2
    exact_mod_cast this

/- English proof (translation)
Use function extensionality and compare the values at `a`. Establish `hs : ∑ a, (mu a - nu a) = 0` using `by simpa using h.2.2`. Use `(Finset.sum_eq_zero_iff_of_nonneg (fun a _ => sub_nonneg.mpr (h.1 a))).mp hs a (Finset.mem_univ a)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem comb_hstrip_zero {n : ℕ} {nu mu : Fin n → ℤ} (h : HStrip nu mu 0) : mu = nu := by
  funext a
  have hs : ∑ a, (mu a - nu a) = 0 := by simpa using h.2.2
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => sub_nonneg.mpr (h.1 a))).mp hs a (Finset.mem_univ a)
  linarith

/- English proof (translation)
Proceed by induction on `k using Fin.induction with`. Consider the case `zero => exact P.zero`. Consider the case `succ l ih`. Establish `ih'` using `ih (fun l' hl' => h l' (by`. Establish `h1 : l'.val < l.val` using `hl'`.

Use `show l'.val < l.val + 1`. Use the proof step `omega))`. Establish `hB` using `h l (by show l.val < l.val + 1; omega)`. Establish `hs` using `P.step l`. Rewrite `hs` using `[hB]`.

Distinguish the cases in `hv : LL.vec l = true`. Rewrite `hs` using `[if_pos hv]`. Rewrite using `[comb_hstrip_zero hs, ih']`. Rewrite `hs` using `[if_neg hv]`. Rewrite using `[← comb_hstrip_zero hs, ih']`.
-/
theorem comb_zero_of_deg {n N : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} (P : PPath n N LL B) (k : Fin (N + 1))
    (h : ∀ l : Fin N, l.val < k.val → B l = 0) : P.mu k = 0 := by
  induction k using Fin.induction with
  | zero => exact P.zero
  | succ l ih =>
    have ih' := ih (fun l' hl' => h l' (by
      have h1 : l'.val < l.val := hl'
      show l'.val < l.val + 1
      omega))
    have hB := h l (by show l.val < l.val + 1; omega)
    have hs := P.step l
    rw [hB] at hs
    by_cases hv : LL.vec l = true
    · rw [if_pos hv] at hs
      rw [comb_hstrip_zero hs, ih']
    · rw [if_neg hv] at hs
      rw [← comb_hstrip_zero hs, ih']

/- English proof (translation)
Proceed by induction on `k using Fin.induction with`. Consider the case `zero => intro a`. Rewrite using `[P.zero]`. Conclude with `le_rfl`. Consider the case `succ l ih`.

Establish `ih'` using `ih (fun l' hl' => h l' (by`. Establish `h1 : l'.val < l.val` using `hl'`. Use `show l'.val < l.val + 1`. Use the proof step `omega))`. Establish `hv` using `h l (by show l.val < l.val + 1; omega)`.

Establish `hs` using `P.step l`. Rewrite `hs` using `[if_pos hv]`. Introduce `a`. Conclude with `(ih' a).trans (hs.1 a)`.
-/
theorem comb_nonneg_of_vec {n N : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} (P : PPath n N LL B) (k : Fin (N + 1))
    (h : ∀ l : Fin N, l.val < k.val → LL.vec l = true) : ∀ a, 0 ≤ P.mu k a := by
  induction k using Fin.induction with
  | zero => intro a; rw [P.zero]; exact le_rfl
  | succ l ih =>
    have ih' := ih (fun l' hl' => h l' (by
      have h1 : l'.val < l.val := hl'
      show l'.val < l.val + 1
      omega))
    have hv := h l (by show l.val < l.val + 1; omega)
    have hs := P.step l
    rw [if_pos hv] at hs
    intro a
    exact (ih' a).trans (hs.1 a)

variable {n' r : ℕ} [NeZero n'] (F : Frames n' r) (j : ℤ)

/- English proof (translation)
Simplify using `[segLL, LZ]`.
-/
theorem comb_vec (i : Fin (segN F j)) : (segLL F j).vec i = true ↔ Even (segE F j i) := by
  simp [segLL, LZ]

/- English proof (translation)
Take `⟨-, -, -, -, -, h6, -⟩` from `hV`. Proceed by induction on `k with`. Consider the case `zero => exact ⟨0, hk, le_antisymm hxk h0⟩`. Consider the case `succ k ih`. Distinguish the cases in `h1 : x ≤ F.fr J k`.

Conclude with `ih (by omega) h1`. Distinguish the cases in `h2 : x = F.fr J (k + 1)`. Conclude with `⟨k + 1, hk, h2⟩`. Conclude with `absurd hx (h6 J k x hk (not_le.mp h1) (lt_of_le_of_ne hxk h2))`.
-/
theorem comb_frame_top {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (J x : ℤ) (hx : posOf n' x ∈ F.TT) (h0 : F.fr J 0 ≤ x)
    (k : ℕ) (hk : k < r) (hxk : x ≤ F.fr J k) : ∃ i, i < r ∧ x = F.fr J i := by
  obtain ⟨-, -, -, -, -, h6, -⟩ := hV
  induction k with
  | zero => exact ⟨0, hk, le_antisymm hxk h0⟩
  | succ k ih =>
    by_cases h1 : x ≤ F.fr J k
    · exact ih (by omega) h1
    · by_cases h2 : x = F.fr J (k + 1)
      · exact ⟨k + 1, hk, h2⟩
      · exact absurd hx (h6 J k x hk (not_le.mp h1) (lt_of_le_of_ne hxk h2))

/- English proof (translation)
Establish `hx'` using `hx`. Unfold `Frames.letters at hx'`. Rewrite `hx'` using `[Finset.mem_filter, Finset.mem_Icc]`. Take `⟨i, hi, rfl⟩` from `comb_frame_top F hV (j - 1) x hx'.2 hx'.1.1 (r - 1) (Nat.sub_lt (NeZero.pos r) Nat.one_pos) hW`. Conclude with `(hV.2.2.2.2.1 (j - 1) i hi).2`.
-/
theorem comb_W_even [NeZero r] {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (x : ℤ) (hx : x ∈ F.letters j) (hW : F.IsW j x) :
    Even x := by
  classical
  have hx' := hx
  unfold Frames.letters at hx'
  rw [Finset.mem_filter, Finset.mem_Icc] at hx'
  obtain ⟨i, hi, rfl⟩ := comb_frame_top F hV (j - 1) x hx'.2 hx'.1.1 (r - 1)
    (Nat.sub_lt (NeZero.pos r) Nat.one_pos) hW
  exact (hV.2.2.2.2.1 (j - 1) i hi).2

/- English proof (translation)
Unfold `segL`. Rewrite using `[List.mem_flatMap]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, -, hi⟩`. Distinguish the cases in `hW : F.IsW j (segE F j i)`.

Rewrite `hi` using `[if_pos hW]`. Conclude with `absurd hi (List.not_mem_nil)`. Rewrite `hi` using `[if_neg hW]`. Use `⟨i, hW, ?_⟩` and prove the remaining obligations. Simplify using `using hi`.

Introduce and unpack `⟨i, hW, hi⟩`. Use `⟨i, List.mem_finRange i, ?_⟩` and prove the remaining obligations. Rewrite using `[if_neg hW]`. Simplify using `using hi`.
-/
theorem comb_mem_segL (m : ℤ → ℤ) (th : ℤ → ℝ) (e : PathInequality (segN F j)) :
    e ∈ segL F j m th ↔ ∃ i : Fin (segN F j), ¬ F.IsW j (segE F j i) ∧
      (e = (if Even (segE F j i) then PathInequality.mix i.succ i.castSucc (m (segE F j i))
          else PathInequality.mix i.castSucc i.succ (m (segE F j i))) ∨ e = PathInequality.nuGe i.castSucc ⌈th (segE F j i)⌉) := by
  classical
  unfold segL
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨i, -, hi⟩
    by_cases hW : F.IsW j (segE F j i)
    · rw [if_pos hW] at hi
      exact absurd hi (List.not_mem_nil)
    · rw [if_neg hW] at hi
      refine ⟨i, hW, ?_⟩
      simpa using hi
  · rintro ⟨i, hW, hi⟩
    refine ⟨i, List.mem_finRange i, ?_⟩
    rw [if_neg hW]
    simpa using hi

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h i hW`. Establish `h1` using `h _ ((comb_mem_segL F j m th _).mpr ⟨i, hW, Or.inl rfl⟩)`. Establish `h2` using `h _ ((comb_mem_segL F j m th _).mpr ⟨i, hW, Or.inr rfl⟩)`. Use `⟨fun he => ?_, fun he => ?_, ?_⟩` and prove the remaining obligations.

Rewrite `h1` using `[if_pos he]`. Conclude with `h1`. Rewrite `h1` using `[if_neg he]`. Conclude with `h1`. Conclude with `Int.ceil_le.mp h2`.

Introduce `h e he`. Take `⟨i, hW, rfl | rfl⟩` from `(comb_mem_segL F j m th e).mp he`. Take `⟨cE, cO, -⟩` from `h i hW`. Distinguish the cases in `hev : Even (segE F j i)`. Rewrite using `[if_pos hev]`.

Conclude with `cE hev`. Rewrite using `[if_neg hev]`. Conclude with `cO hev`. Conclude with `Int.ceil_le.mpr (h i hW).2.2`.
-/
theorem comb_sat_iff [NeZero r] {K : ℕ} [NeZero K] (m : ℤ → ℤ) (th : ℤ → ℝ)
    (nu : Fin (segN F j + 1) → Fin r → ℤ) (ka : Fin (segN F j + 1) → Fin K → ℤ) :
    (∀ e ∈ segL F j m th, e.Sat nu ka) ↔ ∀ i : Fin (segN F j), ¬ F.IsW j (segE F j i) →
      (Even (segE F j i) → ka i.succ 0 + m (segE F j i) ≤ nu i.castSucc (lastIdx r)) ∧
      (¬ Even (segE F j i) → ka i.castSucc 0 + m (segE F j i) ≤ nu i.succ (lastIdx r)) ∧
      th (segE F j i) ≤ ((nu i.castSucc (lastIdx r) : ℤ) : ℝ) := by
  constructor
  · intro h i hW
    have h1 := h _ ((comb_mem_segL F j m th _).mpr ⟨i, hW, Or.inl rfl⟩)
    have h2 := h _ ((comb_mem_segL F j m th _).mpr ⟨i, hW, Or.inr rfl⟩)
    refine ⟨fun he => ?_, fun he => ?_, ?_⟩
    · rw [if_pos he] at h1; exact h1
    · rw [if_neg he] at h1; exact h1
    · exact Int.ceil_le.mp h2
  · intro h e he
    obtain ⟨i, hW, rfl | rfl⟩ := (comb_mem_segL F j m th e).mp he
    · obtain ⟨cE, cO, -⟩ := h i hW
      by_cases hev : Even (segE F j i)
      · rw [if_pos hev]; exact cE hev
      · rw [if_neg hev]; exact cO hev
    · exact Int.ceil_le.mpr (h i hW).2.2

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c', c'', ⟨Q1, h1⟩, ⟨Q2, h2⟩, hcond⟩`. Establish `e1 : c' = b'` using `comb_deg_unique Q1 P1 h1`. Establish `e2 : c'' = b''` using `comb_deg_unique Q2 P2 h2`. Substitute `e1` using the available equality.

Substitute `e2` using the available equality. Simplify using `only at hcond`. Use `⟨⟨?_, ?_⟩, fun i => ⟨(hcond i).1, fun hW => ⟨fun he => (((hcond i).2 hW).1 he).2, fun he => (((hcond i).2 hW).2.1 he).2⟩⟩⟩` and prove the remaining obligations. Use `(hB1 (segN F j) r K (segLL F j) (c' + c'') hK P1.mu P2.mu).mpr ⟨c', c'', fun i => rfl, ⟨P1, rfl⟩, ⟨P2, rfl⟩, fun i => ?_⟩` and prove the remaining obligations. Unfold `CondC`.

Distinguish the cases in `hW : F.IsW j (segE F j i)`. Establish `hWl : ∀ l : Fin (segN F j), l.val ≤ i.val → F.IsW j (segE F j l)`. Introduce `l hl`. Conclude with `le_trans ((segE_strictMono F j).monotone (Fin.le_def.mpr hl)) hW`. Establish `hev : (segLL F j).vec i = true` using `(comb_vec F j i).mpr (comb_W_even F j hV _ (segE_mem F j i) hW)`.

Rewrite using `[if_pos hev]`. Establish `z : P2.mu i.succ = 0` using `comb_zero_of_deg P2 i.succ (fun l hl => (hcond l).1 (hWl l (by`. Establish `h3 : l.val < i.val + 1` using `hl`. Use the proof step `omega)))`. Establish `nn` using `comb_nonneg_of_vec P1 i.castSucc (fun l hl => (comb_vec F j l).mpr (comb_W_even F j hV _ (segE_mem F j l) (hWl l (by`.

Establish `h3 : l.val < i.val` using `hl`. Use the proof step `omega)))) (lastIdx r)`. Rewrite using `[z]`. Conclude with `nn`. Take `⟨cE, cO, -⟩` from `(hcond i).2 hW`.

Establish `hm'` using `hm (segE F j i)`. Distinguish the cases in `he : Even (segE F j i)`. Rewrite using `[if_pos ((comb_vec F j i).mpr he)]`. Use `(cE he).1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[if_neg (fun h => he ((comb_vec F j i).mp h))]`. Use `(cO he).1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `(comb_sat_iff F j m th P1.mu P2.mu).mpr fun i hW => ?_` and prove the remaining obligations. Take `⟨cE, cO, cR⟩` from `(hcond i).2 hW`.

Conclude with `⟨fun he => (cE he).1, fun he => (cO he).1, cR⟩`. Introduce and unpack `⟨⟨-, hsat⟩, hord⟩`. Establish `hs` using `(comb_sat_iff F j m th P1.mu P2.mu).mp hsat`. Use `⟨b', b'', ⟨P1, rfl⟩, ⟨P2, rfl⟩, fun i => ⟨(hord i).1, fun hW => ?_⟩⟩` and prove the remaining obligations. Take `⟨cE, cO, cR⟩` from `hs i hW`.

Conclude with `⟨fun he => ⟨cE he, ((hord i).2 hW).1 he⟩, fun he => ⟨cO he, ((hord i).2 hW).2 he⟩, cR⟩`.
-/
theorem segPairs_iff (D : Formalism.BasicNotions.D7) (hB1 : Formalism.MainNotions.CovariantDegrees.RotatedSumBound D) [NeZero r] {K : ℕ} [NeZero K] (L₁ N₁ : ℕ)
    (hV : F.Valid L₁ N₁) (hK : segN F j + r ≤ K) (m : ℤ → ℤ) (hm : ∀ x, 0 ≤ m x) (th o : ℤ → ℝ)
    (b' b'' : Fin (segN F j) → ℕ) (P1 : PPath r (segN F j) (segLL F j) b')
    (P2 : PPath K (segN F j) (segLL F j) b'') :
    (P1.mu, P2.mu) ∈ segPairs F j K m th o ↔
      ((P1.mu, P2.mu) ∈ segPPB F j K m th (b' + b'') ∧ ordOK F j o b' b'') := by
  constructor
  · rintro ⟨c', c'', ⟨Q1, h1⟩, ⟨Q2, h2⟩, hcond⟩
    have e1 : c' = b' := comb_deg_unique Q1 P1 h1
    have e2 : c'' = b'' := comb_deg_unique Q2 P2 h2
    subst e1
    subst e2
    simp only at hcond
    refine ⟨⟨?_, ?_⟩, fun i => ⟨(hcond i).1, fun hW => ⟨fun he => (((hcond i).2 hW).1 he).2,
      fun he => (((hcond i).2 hW).2.1 he).2⟩⟩⟩
    · refine (hB1 (segN F j) r K (segLL F j) (c' + c'') hK P1.mu P2.mu).mpr
        ⟨c', c'', fun i => rfl, ⟨P1, rfl⟩, ⟨P2, rfl⟩, fun i => ?_⟩
      unfold CondC
      by_cases hW : F.IsW j (segE F j i)
      · have hWl : ∀ l : Fin (segN F j), l.val ≤ i.val → F.IsW j (segE F j l) := by
          intro l hl
          exact le_trans ((segE_strictMono F j).monotone (Fin.le_def.mpr hl)) hW
        have hev : (segLL F j).vec i = true :=
          (comb_vec F j i).mpr (comb_W_even F j hV _ (segE_mem F j i) hW)
        rw [if_pos hev]
        have z : P2.mu i.succ = 0 := comb_zero_of_deg P2 i.succ (fun l hl => (hcond l).1 (hWl l (by
          have h3 : l.val < i.val + 1 := hl
          omega)))
        have nn := comb_nonneg_of_vec P1 i.castSucc (fun l hl =>
          (comb_vec F j l).mpr (comb_W_even F j hV _ (segE_mem F j l) (hWl l (by
            have h3 : l.val < i.val := hl
            omega)))) (lastIdx r)
        rw [z]
        exact nn
      · obtain ⟨cE, cO, -⟩ := (hcond i).2 hW
        have hm' := hm (segE F j i)
        by_cases he : Even (segE F j i)
        · rw [if_pos ((comb_vec F j i).mpr he)]
          have := (cE he).1
          linarith
        · rw [if_neg (fun h => he ((comb_vec F j i).mp h))]
          have := (cO he).1
          linarith
    · refine (comb_sat_iff F j m th P1.mu P2.mu).mpr fun i hW => ?_
      obtain ⟨cE, cO, cR⟩ := (hcond i).2 hW
      exact ⟨fun he => (cE he).1, fun he => (cO he).1, cR⟩
  · rintro ⟨⟨-, hsat⟩, hord⟩
    have hs := (comb_sat_iff F j m th P1.mu P2.mu).mp hsat
    refine ⟨b', b'', ⟨P1, rfl⟩, ⟨P2, rfl⟩, fun i => ⟨(hord i).1, fun hW => ?_⟩⟩
    obtain ⟨cE, cO, cR⟩ := hs i hW
    exact ⟨fun he => ⟨cE he, ((hord i).2 hW).1 he⟩, fun he => ⟨cO he, ((hord i).2 hW).2 he⟩, cR⟩

/- English proof (translation)
Take `⟨b', b'', hs, h1, h2, -⟩` from `(hB1 (segN F j) r K (segLL F j) B hK q.1 q.2).mp hq.1`. Conclude with `⟨b', b'', funext hs, h1, h2⟩`.
-/
theorem segPPB_paths (D : Formalism.BasicNotions.D7) (hB1 : Formalism.MainNotions.CovariantDegrees.RotatedSumBound D) [NeZero r] {K : ℕ} [NeZero K]
    (hK : segN F j + r ≤ K) (m : ℤ → ℤ) (th : ℤ → ℝ) (B : Fin (segN F j) → ℕ)
    (q : (Fin (segN F j + 1) → Fin r → ℤ) × (Fin (segN F j + 1) → Fin K → ℤ))
    (hq : q ∈ segPPB F j K m th B) :
    ∃ b' b'' : Fin (segN F j) → ℕ, b' + b'' = B ∧ (∃ P1 : PPath r (segN F j) (segLL F j) b', P1.mu = q.1) ∧
      ∃ P2 : PPath K (segN F j) (segLL F j) b'', P2.mu = q.2 := by
  obtain ⟨b', b'', hs, h1, h2, -⟩ := (hB1 (segN F j) r K (segLL F j) B hK q.1 q.2).mp hq.1
  exact ⟨b', b'', funext hs, h1, h2⟩

end Comb

section Jone

open Formalism.MainNotions.CovariantDegrees

variable {Fd : Type} [Field Fd] {N m k : ℕ}

open Classical in

def jone_w (LL : Letters (Fin N)) (S : Set (Fin N)) (e : Fin m → Fin k) : Fin N × Fin k → ℤ :=
  fun v => if v.1 ∈ S ∧ v.2 ∈ Set.range e then (if LL.vec v.1 then 1 else -1) else 0

/- English proof (translation)
Establish `key : ∀ c : Fin m, jone_w LL S e (l, e c) = if l ∈ S then (if LL.vec l then 1 else -1) else 0`. Introduce `c`. Unfold `jone_w`. Distinguish the cases in `hl : l ∈ S`. Establish `h : (l, e c).1 ∈ S ∧ (l, e c).2 ∈ Set.range e` using `⟨hl, c, rfl⟩`.

Rewrite using `[if_pos h, if_pos hl]`. Establish `h : ¬ ((l, e c).1 ∈ S ∧ (l, e c).2 ∈ Set.range e)` using `fun h => hl h.1`. Rewrite using `[if_neg h, if_neg hl]`. Rewrite using `[key a, key b]`.
-/
theorem jone_w_eq (LL : Letters (Fin N)) (S : Set (Fin N)) (e : Fin m → Fin k) (l : Fin N) (a b : Fin m) :
    jone_w LL S e (l, e a) = jone_w LL S e (l, e b) := by
  classical
  have key : ∀ c : Fin m, jone_w LL S e (l, e c) = if l ∈ S then (if LL.vec l then 1 else -1) else 0 := by
    intro c
    unfold jone_w
    by_cases hl : l ∈ S
    · have h : (l, e c).1 ∈ S ∧ (l, e c).2 ∈ Set.range e := ⟨hl, c, rfl⟩
      rw [if_pos h, if_pos hl]
    · have h : ¬ ((l, e c).1 ∈ S ∧ (l, e c).2 ∈ Set.range e) := fun h => hl h.1
      rw [if_neg h, if_neg hl]
  rw [key a, key b]

/- English proof (translation)
Rewrite using `[← mem_weightedHomogeneousSubmodule]`. Simplify using `only [glOpsE, LinearMap.sum_apply]`. Use `Submodule.sum_mem _ fun l _ => ?_` and prove the remaining obligations. Establish `key : ∀ a b, (X (l, e a) * pderiv (l, e b) φ) ∈ weightedHomogeneousSubmodule Fd (jone_w LL S e) t`. Introduce `a b`.

Establish `h1 : (pderiv (l, e b) φ).IsWeightedHomogeneous (jone_w LL S e) (t - jone_w LL S e (l, e b))` using `h.pderiv (sub_add_cancel _ _)`. Establish `h2` using `(isWeightedHomogeneous_X (R := Fd) (jone_w LL S e) (l, e a)).mul h1`. Rewrite `h2` using `[jone_w_eq LL S e l a b, add_sub_cancel]`. Conclude with `h2`. Use `split_ifs`.

Conclude with `key a b`. Rewrite using `[LinearMap.neg_apply]`. Conclude with `Submodule.neg_mem _ (key b a)`. Rewrite using `[LinearMap.zero_apply]`. Conclude with `Submodule.zero_mem _`.
-/
theorem jone_stable (LL : Letters (Fin N)) (S : Set (Fin N)) (e : Fin m → Fin k) (a b : Fin m)
    (φ : MvPolynomial (Fin N × Fin k) Fd) (t : ℤ) (h : φ.IsWeightedHomogeneous (jone_w LL S e) t) :
    (glOpsE Fd LL S e a b φ).IsWeightedHomogeneous (jone_w LL S e) t := by
  classical
  rw [← mem_weightedHomogeneousSubmodule]
  simp only [glOpsE, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun l _ => ?_
  have key : ∀ a b, (X (l, e a) * pderiv (l, e b) φ) ∈ weightedHomogeneousSubmodule Fd (jone_w LL S e) t := by
    intro a b
    have h1 : (pderiv (l, e b) φ).IsWeightedHomogeneous (jone_w LL S e) (t - jone_w LL S e (l, e b)) :=
      h.pderiv (sub_add_cancel _ _)
    have h2 := (isWeightedHomogeneous_X (R := Fd) (jone_w LL S e) (l, e a)).mul h1
    rw [jone_w_eq LL S e l a b, add_sub_cancel] at h2
    exact h2
  split_ifs
  · exact key a b
  · rw [LinearMap.neg_apply]; exact Submodule.neg_mem _ (key b a)
  · rw [LinearMap.zero_apply]; exact Submodule.zero_mem _

/- English proof (translation)
Unfold `Umon at hu`. Proceed by induction on `hu using Submonoid.closure_induction with`. Consider the case `mem u hu`. Take `⟨ab, rfl⟩` from `hu`. Conclude with `fun y hy => jone_stable LL S e _ _ y t hy`.

Consider the case `one => exact fun y hy => hy`. Consider the case `mul u1 u2 _ _ h1 h2 => exact fun y hy => h1 _ (h2 y hy)`.
-/
theorem jone_umon (LL : Letters (Fin N)) (S : Set (Fin N)) (e : Fin m → Fin k) (t : ℤ)
    (u : Module.End Fd (MvPolynomial (Fin N × Fin k) Fd)) (hu : u ∈ Umon (glOpsE Fd LL S e)) :
    ∀ y : MvPolynomial (Fin N × Fin k) Fd, y.IsWeightedHomogeneous (jone_w LL S e) t →
      (u y).IsWeightedHomogeneous (jone_w LL S e) t := by
  unfold Umon at hu
  induction hu using Submonoid.closure_induction with
  | mem u hu =>
    obtain ⟨ab, rfl⟩ := hu
    exact fun y hy => jone_stable LL S e _ _ y t hy
  | one => exact fun y hy => hy
  | mul u1 u2 _ _ h1 h2 => exact fun y hy => h1 _ (h2 y hy)

open Classical in
/- English proof (translation)
Rewrite using `[Finsupp.weight_eq_sum, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Distinguish the cases in `hl : l ∈ S`. Rewrite using `[if_pos hl]`. Establish `h1 : ∀ c, mm (l, c) • jone_w LL S e (l, c) = if c ∈ Set.range e then (if LL.vec l then (mm (l, c) : ℤ) else -(mm (l, c) : ℤ)) else 0`.

Introduce `c`. Simplify using `only [jone_w, hl, true_and]`. Apply the tactic sequence `split_ifs <;> simp`. Repeatedly rewrite using `[h1]`. Rewrite using `[← Fintype.sum_of_injective e he (fun a => if LL.vec l then (mm (l, e a) : ℤ) else -(mm (l, e a) : ℤ)) _ (fun c hc => if_neg hc) (fun a => by simp)]`.

Apply the tactic sequence `split_ifs <;> simp`. Simplify using `[jone_w, hl]`.
-/
theorem jone_weight (LL : Letters (Fin N)) (S : Set (Fin N)) (e : Fin m → Fin k) (he : Function.Injective e)
    (mm : Fin N × Fin k →₀ ℕ) :
    Finsupp.weight (jone_w LL S e) mm =
      ∑ l, if l ∈ S then (if LL.vec l then (∑ a, (mm (l, e a) : ℤ)) else -∑ a, (mm (l, e a) : ℤ)) else 0 := by
  rw [Finsupp.weight_eq_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hl : l ∈ S
  · rw [if_pos hl]
    have h1 : ∀ c, mm (l, c) • jone_w LL S e (l, c) =
        if c ∈ Set.range e then (if LL.vec l then (mm (l, c) : ℤ) else -(mm (l, c) : ℤ)) else 0 := by
      intro c
      simp only [jone_w, hl, true_and]
      split_ifs <;> simp
    simp_rw [h1]
    rw [← Fintype.sum_of_injective e he (fun a => if LL.vec l then (mm (l, e a) : ℤ) else -(mm (l, e a) : ℤ)) _
      (fun c hc => if_neg hc) (fun a => by simp)]
    split_ifs <;> simp
  · simp [jone_w, hl]

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on' with`. Consider the case `monomial u a`. Rewrite using `[X_mul_pderiv_monomial, coeff_smul, coeff_monomial]`. Distinguish the cases in `h : u = mm`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[h]`. Consider the case `add p q hp hq => rw [map_add, mul_add, coeff_add, coeff_add, hp, hq, mul_add]`.
-/
theorem jone_coeff_XD (i : Fin N × Fin k) (p : MvPolynomial (Fin N × Fin k) Fd) (mm : Fin N × Fin k →₀ ℕ) :
    coeff mm (X i * pderiv i p) = (mm i : Fd) * coeff mm p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [X_mul_pderiv_monomial, coeff_smul, coeff_monomial]
    by_cases h : u = mm
    · subst h; simp
    · simp [h]
  | add p q hp hq => rw [map_add, mul_add, coeff_add, coeff_add, hp, hq, mul_add]

open Classical in
/- English proof (translation)
Simplify using `only [glOpsE, LinearMap.sum_apply, coeff_sum]`. Rewrite using `[Int.cast_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Use `split_ifs`. Simplify using `using jone_coeff_XD (l, e a) v mm`.

Simplify using `using jone_coeff_XD (l, e a) v mm`. Simplify using the standard rewrite rules.
-/
theorem jone_coeff_Eaa (LL : Letters (Fin N)) (S : Set (Fin N)) (e : Fin m → Fin k) (a : Fin m)
    (v : MvPolynomial (Fin N × Fin k) Fd) (mm : Fin N × Fin k →₀ ℕ) :
    coeff mm (glOpsE Fd LL S e a a v) =
      ((∑ l, if l ∈ S then (if LL.vec l then (mm (l, e a) : ℤ) else -(mm (l, e a) : ℤ)) else 0 : ℤ) : Fd) *
        coeff mm v := by
  simp only [glOpsE, LinearMap.sum_apply, coeff_sum]
  rw [Int.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs
  · simpa using jone_coeff_XD (l, e a) v mm
  · simpa using jone_coeff_XD (l, e a) v mm
  · simp

/- English proof (translation)
Introduce `mm hmm`. Establish `h : ∀ a, (∑ l, if l ∈ S then (if LL.vec l then (mm (l, e a) : ℤ) else -(mm (l, e a) : ℤ)) else 0 : ℤ) = lam a`. Introduce `a`. Establish `ha : glOpsE Fd LL S e a a v = (lam a : Fd) • v`. Use `(Submodule.mem_iInf _).mp hv a` as an intermediate fact.

Rewrite `this` using `[LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]`. Conclude with `this`. Establish `hc` using `congrArg (coeff mm) ha`. Rewrite `hc` using `[jone_coeff_Eaa, coeff_smul, smul_eq_mul]`. Conclude with `Int.cast_injective (mul_right_cancel₀ hmm hc)`.

Rewrite using `[jone_weight LL S e he]`. Repeatedly rewrite using `[← h]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem jone_wt [CharZero Fd] (LL : Letters (Fin N)) (S : Set (Fin N)) (e : Fin m → Fin k)
    (he : Function.Injective e) (lam : Fin m → ℤ) (v : MvPolynomial (Fin N × Fin k) Fd)
    (hv : v ∈ weightSp (glOpsE Fd LL S e) lam) : v.IsWeightedHomogeneous (jone_w LL S e) (∑ a, lam a) := by
  classical
  intro mm hmm
  have h : ∀ a, (∑ l, if l ∈ S then (if LL.vec l then (mm (l, e a) : ℤ) else -(mm (l, e a) : ℤ)) else 0 : ℤ) = lam a := by
    intro a
    have ha : glOpsE Fd LL S e a a v = (lam a : Fd) • v := by
      have := (Submodule.mem_iInf _).mp hv a
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at this
      exact this
    have hc := congrArg (coeff mm) ha
    rw [jone_coeff_Eaa, coeff_smul, smul_eq_mul] at hc
    exact Int.cast_injective (mul_right_cancel₀ hmm hc)
  rw [jone_weight LL S e he]
  simp_rw [← h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[← mem_weightedHomogeneousSubmodule]`. Use `Submodule.span_le.mpr ?_ hx` and prove the remaining obligations. Introduce and unpack `_ ⟨u, hu, v, hv, rfl⟩`. Conclude with `jone_umon LL S e _ u hu v (jone_wt LL S e he lam v hv.2.1)`.
-/
theorem jone_iso [CharZero Fd] (LL : Letters (Fin N)) (S : Set (Fin N)) (e : Fin m → Fin k)
    (he : Function.Injective e) (lam : Fin m → ℤ) (x : MvPolynomial (Fin N × Fin k) Fd)
    (hx : x ∈ isoSub (glOpsE Fd LL S e) lam) : x.IsWeightedHomogeneous (jone_w LL S e) (∑ a, lam a) := by
  rw [← mem_weightedHomogeneousSubmodule]
  refine Submodule.span_le.mpr ?_ hx
  rintro _ ⟨u, hu, v, hv, rfl⟩
  exact jone_umon LL S e _ u hu v (jone_wt LL S e he lam v hv.2.1)

open Classical in
/- English proof (translation)
Rewrite using `[← Finset.sum_sub_distrib, Finset.sum_eq_single i]`. Rewrite using `[if_pos ((h1 i).mpr (Or.inr rfl)), if_neg h0, sub_zero]`. Introduce `l _ hl`. Distinguish the cases in `h : l ∈ S0`. Rewrite using `[if_pos ((h1 l).mpr (Or.inl h)), if_pos h, sub_self]`.

Rewrite using `[if_neg (fun h' => ((h1 l).mp h').elim h hl), if_neg h, sub_self]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`.
-/
theorem jone_diff (f : Fin N → ℤ) (i : Fin N) (S0 S1 : Set (Fin N)) (h1 : ∀ l, l ∈ S1 ↔ l ∈ S0 ∨ l = i)
    (h0 : i ∉ S0) : (∑ l, if l ∈ S1 then f l else 0) - (∑ l, if l ∈ S0 then f l else 0) = f i := by
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · rw [if_pos ((h1 i).mpr (Or.inr rfl)), if_neg h0, sub_zero]
  · intro l _ hl
    by_cases h : l ∈ S0
    · rw [if_pos ((h1 l).mpr (Or.inl h)), if_pos h, sub_self]
    · rw [if_neg (fun h' => ((h1 l).mp h').elim h hl), if_neg h, sub_self]
  · intro h; exact absurd (Finset.mem_univ i) h

/- English proof (translation)
Introduce `mm hmm i`. Establish `hc : coeff mm x ≠ 0` using `MvPolynomial.mem_support_iff.mp hmm`. Establish `h1` using `jone_iso LL _ e he _ x (hx i.succ) hc`. Establish `h0` using `jone_iso LL _ e he _ x (hx i.castSucc) hc`. Rewrite `h1`, `h0` using `[jone_weight LL _ e he]`.

Establish `hd` using `jone_diff (fun l => if LL.vec l then (∑ a, (mm (l, e a) : ℤ)) else -∑ a, (mm (l, e a) : ℤ)) i {j : Fin N | j.val < i.castSucc.val} {j : Fin N | j.val < i.succ.val} (by`. Introduce `l`. Simplify using `only [Set.mem_ofPred_eq, Fin.val_succ, Fin.val_castSucc, Fin.ext_iff]`. Use the proof step `omega)`. Use the proof step `(by simp)`.

Rewrite `hd` using `[h1, h0]`. Establish `hs` using `P.step i`. Establish `hgoal : (∑ a, (mm (i, e a) : ℤ)) = (b i : ℤ)`. Distinguish the cases in `hv : LL.vec i = true`. Rewrite `hs` using `[if_pos hv]`.

Simplify using `only [hv, if_true] at hd`. Establish `h3` using `hs.2.2`. Rewrite `h3` using `[Finset.sum_sub_distrib]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `hs` using `[if_neg hv]`.

Simplify using `only [hv] at hd`. Establish `h3` using `hs.2.2`. Rewrite `h3` using `[Finset.sum_sub_distrib]`. Simplify using `only [Bool.false_eq_true, if_false] at hd`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `hgoal` after adjusting the coercions.
-/
theorem jone_letter [CharZero Fd] (LL : Letters (Fin N)) (e : Fin m → Fin k) (he : Function.Injective e)
    (b : Fin N → ℕ) (P : PPath m N LL b) (x : MvPolynomial (Fin N × Fin k) Fd)
    (hx : ∀ i : Fin (N + 1), x ∈ isoSub (glOpsE Fd LL {j | j.val < i.val} e) (P.mu i)) :
    ∀ mm ∈ x.support, ∀ i : Fin N, ∑ a, mm (i, e a) = b i := by
  classical
  intro mm hmm i
  have hc : coeff mm x ≠ 0 := MvPolynomial.mem_support_iff.mp hmm
  have h1 := jone_iso LL _ e he _ x (hx i.succ) hc
  have h0 := jone_iso LL _ e he _ x (hx i.castSucc) hc
  rw [jone_weight LL _ e he] at h1 h0
  have hd := jone_diff (fun l => if LL.vec l then (∑ a, (mm (l, e a) : ℤ)) else -∑ a, (mm (l, e a) : ℤ)) i
    {j : Fin N | j.val < i.castSucc.val} {j : Fin N | j.val < i.succ.val}
    (by
      intro l
      simp only [Set.mem_ofPred_eq, Fin.val_succ, Fin.val_castSucc, Fin.ext_iff]
      omega)
    (by simp)
  rw [h1, h0] at hd
  have hs := P.step i
  have hgoal : (∑ a, (mm (i, e a) : ℤ)) = (b i : ℤ) := by
    by_cases hv : LL.vec i = true
    · rw [if_pos hv] at hs
      simp only [hv, if_true] at hd
      have h3 := hs.2.2
      rw [Finset.sum_sub_distrib] at h3
      linarith
    · rw [if_neg hv] at hs
      simp only [hv] at hd
      have h3 := hs.2.2
      rw [Finset.sum_sub_distrib] at h3
      simp only [Bool.false_eq_true, if_false] at hd
      linarith
  exact_mod_cast hgoal

/- English proof (translation)
Introduce `x hx`. Unfold `biPol`. Rewrite using `[mem_restrictSupport_iff]`. Introduce `mm hmm i`. Establish `hx'` using `fun i => Submodule.mem_inf.mp ((Submodule.mem_iInf _).mp hx i)`.

Conclude with `⟨jone_letter LL _ (Fin.castAdd_injective _ _) b' P1 x (fun i => (hx' i).1) mm (Finset.mem_coe.mp hmm) i, jone_letter LL _ (Fin.natAdd_injective _ _) b'' P2 x (fun i => (hx' i).2) mm (Finset.mem_coe.mp hmm) i⟩`.
-/
theorem jointType_le_biPol (Fd : Type) [Field Fd] [CharZero Fd] {N r K : ℕ} (LL : Letters (Fin N))
    (b' b'' : Fin N → ℕ) (P1 : PPath r N LL b') (P2 : PPath K N LL b'') :
    jointType Fd LL P1.mu P2.mu ≤ biPol Fd b' b'' := by
  intro x hx
  unfold biPol
  rw [mem_restrictSupport_iff]
  intro mm hmm i
  have hx' := fun i => Submodule.mem_inf.mp ((Submodule.mem_iInf _).mp hx i)
  exact ⟨jone_letter LL _ (Fin.castAdd_injective _ _) b' P1 x (fun i => (hx' i).1) mm (Finset.mem_coe.mp hmm) i,
    jone_letter LL _ (Fin.natAdd_injective _ _) b'' P2 x (fun i => (hx' i).2) mm (Finset.mem_coe.mp hmm) i⟩

end Jone

section Proj

open Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.CovariantDegrees

/- English proof (translation)
Rewrite using `[Set.disjoint_left]`. Introduce `mm h1 h2`. Conclude with `h ⟨funext fun i => ((h2 i).1.symm.trans (h1 i).1), funext fun i => ((h2 i).2.symm.trans (h1 i).2)⟩`.
-/
theorem proj_biSet_disjoint {N r K : ℕ} {b' b'' c' c'' : Fin N → ℕ} (h : ¬ (b' = c' ∧ b'' = c'')) :
    Disjoint (biSet (r := r) (K := K) c' c'') (biSet (r := r) (K := K) b' b'') := by
  rw [Set.disjoint_left]
  intro mm h1 h2
  exact h ⟨funext fun i => ((h2 i).1.symm.trans (h1 i).1), funext fun i => ((h2 i).2.symm.trans (h1 i).2)⟩

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[coeff_suppProj, coeff_map, coeff_map, coeff_suppProj]`. Use `split_ifs`. Both sides reduce to the same expression. Rewrite using `[map_zero]`.
-/
theorem proj_suppProj_map {R R' σ : Type} [CommRing R] [CommRing R'] (f : R →+* R') (s : Set (σ →₀ ℕ))
    (A : MvPolynomial σ R) : suppProj R' s (MvPolynomial.map f A) = MvPolynomial.map f (suppProj R s A) := by
  classical
  ext m
  rw [coeff_suppProj, coeff_map, coeff_map, coeff_suppProj]
  split_ifs
  · rfl
  · rw [map_zero]

/- English proof (translation)
Use `⟨A.support.image fun mm => (fun i => ∑ c : Fin r, mm (i, Fin.castAdd K c), fun i => ∑ c : Fin K, mm (i, Fin.natAdd r c)), ?_⟩` and prove the remaining obligations. Use extensionality with `m`. Rewrite using `[coeff_sum]`. Establish `h : ∀ d : (Fin N → ℕ) × (Fin N → ℕ), coeff m (suppProj R (biSet d.1 d.2) A) = if ((fun i => ∑ c : Fin r, m (i, Fin.castAdd K c), fun i => ∑ c : Fin K, m (i, Fin.natAdd r c)) : (Fin N → ℕ) × (Fin N → ℕ)) = d then coeff m A else 0`. Introduce `d`.

Rewrite using `[coeff_suppProj]`. Use `if_congr ?_ rfl rfl` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `Prod.ext (funext fun i => (h i).1) (funext fun i => (h i).2)`.

Introduce `h i`. Rewrite using `[← h]`. Conclude with `⟨rfl, rfl⟩`. Simplify using `only [h]`. Rewrite using `[Finset.sum_ite_eq]`.

Use `split_ifs with hm`. Both sides reduce to the same expression. Assume the negation of the conclusion as `hne`. Conclude with `hm (Finset.mem_image_of_mem _ (mem_support_iff.mpr hne))`.
-/
theorem proj_exists_sum (R : Type) [CommRing R] {N r K : ℕ} (A : MvPolynomial (Fin N × Fin (r + K)) R) :
    ∃ T : Finset ((Fin N → ℕ) × (Fin N → ℕ)), A = ∑ d ∈ T, suppProj R (biSet d.1 d.2) A := by
  classical
  refine ⟨A.support.image fun mm => (fun i => ∑ c : Fin r, mm (i, Fin.castAdd K c),
    fun i => ∑ c : Fin K, mm (i, Fin.natAdd r c)), ?_⟩
  ext m
  rw [coeff_sum]
  have h : ∀ d : (Fin N → ℕ) × (Fin N → ℕ), coeff m (suppProj R (biSet d.1 d.2) A) =
      if ((fun i => ∑ c : Fin r, m (i, Fin.castAdd K c), fun i => ∑ c : Fin K, m (i, Fin.natAdd r c)) :
        (Fin N → ℕ) × (Fin N → ℕ)) = d then coeff m A else 0 := by
    intro d
    rw [coeff_suppProj]
    refine if_congr ?_ rfl rfl
    constructor
    · intro h
      exact Prod.ext (funext fun i => (h i).1) (funext fun i => (h i).2)
    · intro h i
      rw [← h]
      exact ⟨rfl, rfl⟩
  simp only [h]
  rw [Finset.sum_ite_eq]
  split_ifs with hm
  · rfl
  · by_contra hne
    exact hm (Finset.mem_image_of_mem _ (mem_support_iff.mpr hne))

/- English proof (translation)
Unfold `biPol`. Rewrite using `[mem_restrictSupport_iff]`. Introduce `mm hmm i`. Take `⟨m1, h1, m2, h2, rfl⟩` from `Finset.mem_add.mp (support_mul _ _ (Finset.mem_coe.mp hmm))`. Establish `hf1 : Function.Injective (plVar (N` using `N) (r := r) (K := K)) := by`.

Introduce `x y h`. Simplify using `only [plVar, Prod.mk.injEq] at h`. Conclude with `Prod.ext h.1 (Fin.castAdd_injective _ _ h.2)`. Establish `hf2 : Function.Injective (tanVar (N` using `N) (r := r) (K := K)) := by`. Introduce `x y h`.

Simplify using `only [tanVar, Prod.mk.injEq] at h`. Conclude with `Prod.ext h.1 (Fin.natAdd_injective _ _ h.2)`. Rewrite `h1` using `[support_rename_of_injective hf1]`. Rewrite `h2` using `[support_rename_of_injective hf2]`. Take `⟨u1, hu1, rfl⟩` from `Finset.mem_image.mp h1`.

Take `⟨u2, hu2, rfl⟩` from `Finset.mem_image.mp h2`. Establish `d1` using `mem_Pol_iff.mp ha u1 hu1 i`. Establish `d2` using `mem_Pol_iff.mp hg u2 hu2 i`. Establish `hne : ∀ (x : Fin r) (c : Fin K), Fin.castAdd K x ≠ Fin.natAdd r c`. Introduce `x c h`.

Use `congrArg Fin.val h` as an intermediate fact. Simplify using `at this`. Use linear arithmetic over natural numbers and integers. Establish `z1 : ∀ c : Fin K, Finsupp.mapDomain (plVar (N` using `N) (r := r) (K := K)) u1 (i, Fin.natAdd r c) = 0 := by`. Introduce `c`.

Use `Finsupp.mapDomain_of_notMem_range _ _ ?_` and prove the remaining obligations. Introduce and unpack `⟨v, hv⟩`. Simplify using `only [plVar, Prod.mk.injEq] at hv`. Conclude with `hne _ _ hv.2`. Establish `z2 : ∀ c : Fin K, Finsupp.mapDomain (tanVar (N` using `N) (r := r) (K := K)) u2 (i, Fin.natAdd r c) = u2 (i, c) := fun c => Finsupp.mapDomain_apply hf2 u2 (i, c)`.

Establish `z3 : ∀ c : Fin r, Finsupp.mapDomain (plVar (N` using `N) (r := r) (K := K)) u1 (i, Fin.castAdd K c) = u1 (i, c) := fun c => Finsupp.mapDomain_apply hf1 u1 (i, c)`. Establish `z4 : ∀ c : Fin r, Finsupp.mapDomain (tanVar (N` using `N) (r := r) (K := K)) u2 (i, Fin.castAdd K c) = 0 := by`. Introduce `c`. Use `Finsupp.mapDomain_of_notMem_range _ _ ?_` and prove the remaining obligations. Introduce and unpack `⟨v, hv⟩`.

Simplify using `only [tanVar, Prod.mk.injEq] at hv`. Conclude with `hne _ _ hv.2.symm`. Prove the components needed by the constructor for the conclusion. Simplify using `only [Finsupp.add_apply, z3, z4, add_zero]`. Conclude with `d1`.

Simplify using `only [Finsupp.add_apply, z1, z2, zero_add]`. Conclude with `d2`.
-/
theorem proj_word_biPol {R : Type} [CommRing R] {N r K : ℕ} (b' b'' : Fin N → ℕ)
    (a : MvPolynomial (Fin N × Fin r) R) (ha : a ∈ Pol R r b')
    (g : MvPolynomial (Fin N × Fin K) R) (hg : g ∈ Pol R K b'') :
    rename (plVar (K := K)) a * rename (tanVar (r := r)) g ∈ biPol R b' b'' := by
  classical
  unfold biPol
  rw [mem_restrictSupport_iff]
  intro mm hmm i
  obtain ⟨m1, h1, m2, h2, rfl⟩ := Finset.mem_add.mp (support_mul _ _ (Finset.mem_coe.mp hmm))
  have hf1 : Function.Injective (plVar (N := N) (r := r) (K := K)) := by
    intro x y h
    simp only [plVar, Prod.mk.injEq] at h
    exact Prod.ext h.1 (Fin.castAdd_injective _ _ h.2)
  have hf2 : Function.Injective (tanVar (N := N) (r := r) (K := K)) := by
    intro x y h
    simp only [tanVar, Prod.mk.injEq] at h
    exact Prod.ext h.1 (Fin.natAdd_injective _ _ h.2)
  rw [support_rename_of_injective hf1] at h1
  rw [support_rename_of_injective hf2] at h2
  obtain ⟨u1, hu1, rfl⟩ := Finset.mem_image.mp h1
  obtain ⟨u2, hu2, rfl⟩ := Finset.mem_image.mp h2
  have d1 := mem_Pol_iff.mp ha u1 hu1 i
  have d2 := mem_Pol_iff.mp hg u2 hu2 i
  have hne : ∀ (x : Fin r) (c : Fin K), Fin.castAdd K x ≠ Fin.natAdd r c := by
    intro x c h
    have := congrArg Fin.val h
    simp at this
    omega
  have z1 : ∀ c : Fin K, Finsupp.mapDomain (plVar (N := N) (r := r) (K := K)) u1 (i, Fin.natAdd r c) = 0 := by
    intro c
    refine Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨v, hv⟩
    simp only [plVar, Prod.mk.injEq] at hv
    exact hne _ _ hv.2
  have z2 : ∀ c : Fin K, Finsupp.mapDomain (tanVar (N := N) (r := r) (K := K)) u2 (i, Fin.natAdd r c) = u2 (i, c) :=
    fun c => Finsupp.mapDomain_apply hf2 u2 (i, c)
  have z3 : ∀ c : Fin r, Finsupp.mapDomain (plVar (N := N) (r := r) (K := K)) u1 (i, Fin.castAdd K c) = u1 (i, c) :=
    fun c => Finsupp.mapDomain_apply hf1 u1 (i, c)
  have z4 : ∀ c : Fin r, Finsupp.mapDomain (tanVar (N := N) (r := r) (K := K)) u2 (i, Fin.castAdd K c) = 0 := by
    intro c
    refine Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨v, hv⟩
    simp only [tanVar, Prod.mk.injEq] at hv
    exact hne _ _ hv.2.symm
  constructor
  · simp only [Finsupp.add_apply, z3, z4, add_zero]
    exact d1
  · simp only [Finsupp.add_apply, z1, z2, zero_add]
    exact d2

def proj_HasPaths {N r K : ℕ} (LL : Letters (Fin N))
    (q : (Fin (N + 1) → Fin r → ℤ) × (Fin (N + 1) → Fin K → ℤ)) : Prop :=
  ∃ b' b'' : Fin N → ℕ, (∃ P1 : PPath r N LL b', P1.mu = q.1) ∧ ∃ P2 : PPath K N LL b'', P2.mu = q.2

/- English proof (translation)
Establish `hle : (⨆ q ∈ Q, jointType Kf LL q.1 q.2) ≤ Submodule.comap (suppProj Kf (biSet (r` using `r) (K := K) c' c'')) (⨆ q ∈ Q', jointType Kf LL q.1 q.2) := by`. Use `iSup₂_le fun q hq y hy => ?_` and prove the remaining obligations. Take `⟨b', b'', ⟨P1, h1⟩, ⟨P2, h2⟩⟩` from `hQ q hq`. Take `⟨nu, ka⟩` from `q`. Simplify using `only at h1 h2 hy`.

Substitute `h1` using the available equality. Substitute `h2` using the available equality. Rewrite using `[Submodule.mem_comap]`. Distinguish the cases in `h : b' = c' ∧ b'' = c''`. Take `⟨rfl, rfl⟩` from `h`.

Rewrite using `[suppProj_of_mem _ _ _ (hJ1 b' b'' P1 P2 hy)]`. Conclude with `(le_iSup₂ (f := fun (q : (Fin (N + 1) → Fin r → ℤ) × (Fin (N + 1) → Fin K → ℤ)) (_ : q ∈ Q') => jointType Kf LL q.1 q.2) (P1.mu, P2.mu) (hQQ P1 P2 hq)) hy`. Rewrite using `[suppProj_of_disjoint _ _ _ _ (hJ1 b' b'' P1 P2 hy) (proj_biSet_disjoint h)]`. Conclude with `Submodule.zero_mem _`. Conclude with `hle hx`.
-/
theorem proj_sup {Kf : Type} [Field Kf] {N r K : ℕ} (LL : Letters (Fin N))
    (hJ1 : ∀ (b' b'' : Fin N → ℕ) (P1 : PPath r N LL b') (P2 : PPath K N LL b''),
      jointType Kf LL P1.mu P2.mu ≤ biPol Kf b' b'')
    (Q Q' : Set ((Fin (N + 1) → Fin r → ℤ) × (Fin (N + 1) → Fin K → ℤ))) (hQ : ∀ q ∈ Q, proj_HasPaths LL q)
    (c' c'' : Fin N → ℕ)
    (hQQ : ∀ (P1 : PPath r N LL c') (P2 : PPath K N LL c''), (P1.mu, P2.mu) ∈ Q → (P1.mu, P2.mu) ∈ Q')
    (x : MvPolynomial (Fin N × Fin (r + K)) Kf) (hx : x ∈ ⨆ q ∈ Q, jointType Kf LL q.1 q.2) :
    suppProj Kf (biSet c' c'') x ∈ ⨆ q ∈ Q', jointType Kf LL q.1 q.2 := by
  have hle : (⨆ q ∈ Q, jointType Kf LL q.1 q.2) ≤
      Submodule.comap (suppProj Kf (biSet (r := r) (K := K) c' c'')) (⨆ q ∈ Q', jointType Kf LL q.1 q.2) := by
    refine iSup₂_le fun q hq y hy => ?_
    obtain ⟨b', b'', ⟨P1, h1⟩, ⟨P2, h2⟩⟩ := hQ q hq
    obtain ⟨nu, ka⟩ := q
    simp only at h1 h2 hy
    subst h1
    subst h2
    rw [Submodule.mem_comap]
    by_cases h : b' = c' ∧ b'' = c''
    · obtain ⟨rfl, rfl⟩ := h
      rw [suppProj_of_mem _ _ _ (hJ1 b' b'' P1 P2 hy)]
      exact (le_iSup₂ (f := fun (q : (Fin (N + 1) → Fin r → ℤ) × (Fin (N + 1) → Fin K → ℤ)) (_ : q ∈ Q') =>
        jointType Kf LL q.1 q.2) (P1.mu, P2.mu) (hQQ P1 P2 hq)) hy
    · rw [suppProj_of_disjoint _ _ _ _ (hJ1 b' b'' P1 P2 hy) (proj_biSet_disjoint h)]
      exact Submodule.zero_mem _
  exact hle hx

/- English proof (translation)
Unfold `XXZ at hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨q, hq, I', I'', hI', hI'', rfl⟩` from `hy`. Take `⟨b', b'', ⟨P1, h1⟩, ⟨P2, h2⟩⟩` from `hQ q hq`.

Take `⟨nu, ka⟩` from `q`. Simplify using `only at h1 h2 hI' hI''`. Substitute `h1` using the available equality. Substitute `h2` using the available equality. Establish `hw : PsiPl R P1.mu I' * PsiTan R P2.mu I'' ∈ biPol R b' b''` using `proj_word_biPol b' b'' _ (hPol1 b' P1 I' hI') _ (hPol2 b'' P2 I'' hI'')`.

Distinguish the cases in `h : b' = c' ∧ b'' = c''`. Take `⟨rfl, rfl⟩` from `h`. Rewrite using `[suppProj_of_mem _ _ _ hw]`. Conclude with `Submodule.subset_span ⟨(P1.mu, P2.mu), hQQ P1 P2 hq, I', I'', hI', hI'', rfl⟩`. Rewrite using `[suppProj_of_disjoint _ _ _ _ hw (proj_biSet_disjoint h)]`.

Conclude with `Submodule.zero_mem _`. Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add y z _ _ hy hz => rw [map_add]`. Conclude with `Submodule.add_mem _ hy hz`.

Consider the case `smul c y _ hy => rw [map_smul]`. Conclude with `Submodule.smul_mem _ c hy`.
-/
theorem proj_words {R : Type} [CommRing R] {N r K : ℕ} (LL : Letters (Fin N))
    (hPol1 : ∀ (b : Fin N → ℕ) (P : PPath r N LL b) (I : ℤ → Finset (Fin r)), IsSt P.mu I → Psi R P.mu I ∈ Pol R r b)
    (hPol2 : ∀ (b : Fin N → ℕ) (P : PPath K N LL b) (I : ℤ → Finset (Fin K)), IsSt P.mu I → Psi R P.mu I ∈ Pol R K b)
    (Q Q' : Set ((Fin (N + 1) → Fin r → ℤ) × (Fin (N + 1) → Fin K → ℤ))) (hQ : ∀ q ∈ Q, proj_HasPaths LL q)
    (c' c'' : Fin N → ℕ)
    (hQQ : ∀ (P1 : PPath r N LL c') (P2 : PPath K N LL c''), (P1.mu, P2.mu) ∈ Q → (P1.mu, P2.mu) ∈ Q')
    (x : MvPolynomial (Fin N × Fin (r + K)) R) (hx : x ∈ XXZ R Q) :
    suppProj R (biSet c' c'') x ∈ XXZ R Q' := by
  unfold XXZ at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨q, hq, I', I'', hI', hI'', rfl⟩ := hy
    obtain ⟨b', b'', ⟨P1, h1⟩, ⟨P2, h2⟩⟩ := hQ q hq
    obtain ⟨nu, ka⟩ := q
    simp only at h1 h2 hI' hI''
    subst h1
    subst h2
    have hw : PsiPl R P1.mu I' * PsiTan R P2.mu I'' ∈ biPol R b' b'' :=
      proj_word_biPol b' b'' _ (hPol1 b' P1 I' hI') _ (hPol2 b'' P2 I'' hI'')
    by_cases h : b' = c' ∧ b'' = c''
    · obtain ⟨rfl, rfl⟩ := h
      rw [suppProj_of_mem _ _ _ hw]
      exact Submodule.subset_span ⟨(P1.mu, P2.mu), hQQ P1 P2 hq, I', I'', hI', hI'', rfl⟩
    · rw [suppProj_of_disjoint _ _ _ _ hw (proj_biSet_disjoint h)]
      exact Submodule.zero_mem _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ c hy

variable {n' r : ℕ} [NeZero n'] (F : Frames n' r) (j : ℤ)

/- English proof (translation)
Introduce and unpack `q ⟨b', b'', h1, h2, -⟩`. Conclude with `⟨b', b'', h1, h2⟩`.
-/
theorem proj_segPairs_hasPaths [NeZero r] {K : ℕ} [NeZero K] (m : ℤ → ℤ) (th o : ℤ → ℝ) :
    ∀ q ∈ segPairs F j K m th o, proj_HasPaths (segLL F j) q := by
  rintro q ⟨b', b'', h1, h2, -⟩
  exact ⟨b', b'', h1, h2⟩

/- English proof (translation)
Establish `hPB : ∀ B, ∀ q ∈ segPPB F j K m th B, proj_HasPaths (segLL F j) q`. Introduce `B q hq`. Take `⟨b', b'', -, h1, h2⟩` from `hpaths B q hq`. Conclude with `⟨b', b'', h1, h2⟩`. Prove the components needed by the constructor for the conclusion.

Introduce `hf`. Unfold `XXZ at hf`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨q, hq, I', I'', hI', hI'', rfl⟩` from `hy`.

Take `⟨b', b'', ⟨P1, h1⟩, ⟨P2, h2⟩⟩` from `proj_segPairs_hasPaths F j m th o q hq`. Take `⟨nu, ka⟩` from `q`. Simplify using `only at h1 h2 hI' hI''`. Substitute `h1` using the available equality. Substitute `h2` using the available equality.

Establish `hq'` using `(hcomb b' b'' P1 P2).mp hq`. Establish `hw : PsiPl O P1.mu I' * PsiTan O P2.mu I'' ∈ biPol O b' b''` using `proj_word_biPol b' b'' _ (hPol r b' P1 I' hI') _ (hPol K b'' P2 I'' hI'')`. Establish `hmem : PsiPl O P1.mu I' * PsiTan O P2.mu I'' ∈ (XXZ O (segPPB F j K m th (b' + b'')) : Set _)` using `Submodule.subset_span ⟨(P1.mu, P2.mu), hq'.1, I', I'', hI', hI'', rfl⟩`. Rewrite `hmem` using `[hB3 (b' + b'')]`. Use `proj_sup (segLL F j) hJ1 (segPPB F j K m th (b' + b'')) (segPairs F j K m th o) (hPB _) b' b'' (fun P1' P2' h => (hcomb b' b'' P1' P2').mpr ⟨h, hq'.2⟩) _ hmem` as an intermediate fact.

Rewrite `this` using `[proj_suppProj_map, suppProj_of_mem _ _ _ hw]`. Then use the resulting hypothesis. Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add y z _ _ hy hz => rw [map_add]`. Conclude with `Submodule.add_mem _ hy hz`.

Consider the case `smul c y _ hy`. Rewrite using `[MvPolynomial.smul_eq_C_mul, map_mul, map_C, ← MvPolynomial.smul_eq_C_mul]`. Conclude with `Submodule.smul_mem _ _ hy`. Introduce `hf`. Take `⟨T, hT⟩` from `proj_exists_sum O f₀`.

Rewrite using `[hT]`. Use `Submodule.sum_mem _ fun d _ => ?_` and prove the remaining obligations. Take `⟨c', c''⟩` from `d`. Use `show suppProj O (biSet c' c'') f₀ ∈ XXZ O (segPairs F j K m th o)`. Establish `hg : MvPolynomial.map (algebraMap O (KK O)) (suppProj O (biSet c' c'') f₀) = suppProj (KK O) (biSet c' c'') (MvPolynomial.map (algebraMap O (KK O)) f₀)` using `(proj_suppProj_map _ _ _).symm`.

Distinguish the cases in `hok : ordOK F j o c' c''`. Establish `h2 : MvPolynomial.map (algebraMap O (KK O)) (suppProj O (biSet c' c'') f₀) ∈ ⨆ q ∈ segPPB F j K m th (c' + c''), jointType (KK O) (segLL F j) q.1 q.2`. Rewrite using `[hg]`. Conclude with `proj_sup (segLL F j) hJ1 (segPairs F j K m th o) (segPPB F j K m th (c' + c'')) (proj_segPairs_hasPaths F j m th o) c' c'' (fun P1 P2 h => ((hcomb c' c'' P1 P2).mp h).1) _ hf`. Establish `h3 : suppProj O (biSet c' c'') f₀ ∈ (XXZ O (segPPB F j K m th (c' + c'')) : Set _)`.

Rewrite using `[hB3 (c' + c'')]`. Conclude with `h2`. Establish `h4` using `proj_words (segLL F j) (hPol r) (hPol K) (segPPB F j K m th (c' + c'')) (segPairs F j K m th o) (hPB _) c' c'' (fun P1 P2 h => (hcomb c' c'' P1 P2).mpr ⟨h, hok⟩) _ h3`. Rewrite `h4` using `[suppProj_of_mem _ _ _ (suppProj_mem O _ f₀)]`. Then use the resulting hypothesis. Establish `h2` using `proj_sup (segLL F j) hJ1 (segPairs F j K m th o) ∅ (proj_segPairs_hasPaths F j m th o) c' c'' (fun P1 P2 h => absurd ((hcomb c' c'' P1 P2).mp h).2 hok) _ hf`.

Rewrite `h2` using `[← hg]`. Simplify using `only [Set.mem_empty_iff_false, iSup_false, iSup_bot, Submodule.mem_bot] at h2`. Establish `h0 : suppProj O (biSet c' c'') f₀ = 0` using `MvPolynomial.map_injective _ (IsFractionRing.injective O (KK O)) (h2.trans (map_zero _).symm)`. Rewrite using `[h0]`. Conclude with `Submodule.zero_mem _`.
-/
theorem proj_claimA [NeZero r] {K : ℕ} [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    (m : ℤ → ℤ) (th o : ℤ → ℝ)
    (hPol : ∀ (n : ℕ) [NeZero n] (b : Fin (segN F j) → ℕ) (P : PPath n (segN F j) (segLL F j) b)
      (I : ℤ → Finset (Fin n)), IsSt P.mu I → Psi O P.mu I ∈ Pol O n b)
    (hJ1 : ∀ (b' b'' : Fin (segN F j) → ℕ) (P1 : PPath r (segN F j) (segLL F j) b')
      (P2 : PPath K (segN F j) (segLL F j) b''), jointType (KK O) (segLL F j) P1.mu P2.mu ≤ biPol (KK O) b' b'')
    (hcomb : ∀ (b' b'' : Fin (segN F j) → ℕ) (P1 : PPath r (segN F j) (segLL F j) b')
      (P2 : PPath K (segN F j) (segLL F j) b''), (P1.mu, P2.mu) ∈ segPairs F j K m th o ↔
        ((P1.mu, P2.mu) ∈ segPPB F j K m th (b' + b'') ∧ ordOK F j o b' b''))
    (hpaths : ∀ (B : Fin (segN F j) → ℕ) (q : (Fin (segN F j + 1) → Fin r → ℤ) × (Fin (segN F j + 1) → Fin K → ℤ)),
      q ∈ segPPB F j K m th B → ∃ b' b'' : Fin (segN F j) → ℕ, b' + b'' = B ∧
        (∃ P1 : PPath r (segN F j) (segLL F j) b', P1.mu = q.1) ∧
        ∃ P2 : PPath K (segN F j) (segLL F j) b'', P2.mu = q.2)
    (hB3 : ∀ B : Fin (segN F j) → ℕ, (XXZ O (segPPB F j K m th B) : Set _) =
      {f | MvPolynomial.map (algebraMap O (KK O)) f ∈
        ⨆ q ∈ segPPB F j K m th B, jointType (KK O) (segLL F j) q.1 q.2})
    (f₀ : MvPolynomial (Fin (segN F j) × Fin (r + K)) O) :
    f₀ ∈ XXZ O (segPairs F j K m th o) ↔ MvPolynomial.map (algebraMap O (KK O)) f₀ ∈
      ⨆ q ∈ segPairs F j K m th o, jointType (KK O) (segLL F j) q.1 q.2 := by
  have hPB : ∀ B, ∀ q ∈ segPPB F j K m th B, proj_HasPaths (segLL F j) q := by
    intro B q hq
    obtain ⟨b', b'', -, h1, h2⟩ := hpaths B q hq
    exact ⟨b', b'', h1, h2⟩
  constructor
  · intro hf
    unfold XXZ at hf
    induction hf using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨q, hq, I', I'', hI', hI'', rfl⟩ := hy
      obtain ⟨b', b'', ⟨P1, h1⟩, ⟨P2, h2⟩⟩ := proj_segPairs_hasPaths F j m th o q hq
      obtain ⟨nu, ka⟩ := q
      simp only at h1 h2 hI' hI''
      subst h1
      subst h2
      have hq' := (hcomb b' b'' P1 P2).mp hq
      have hw : PsiPl O P1.mu I' * PsiTan O P2.mu I'' ∈ biPol O b' b'' :=
        proj_word_biPol b' b'' _ (hPol r b' P1 I' hI') _ (hPol K b'' P2 I'' hI'')
      have hmem : PsiPl O P1.mu I' * PsiTan O P2.mu I'' ∈ (XXZ O (segPPB F j K m th (b' + b'')) : Set _) :=
        Submodule.subset_span ⟨(P1.mu, P2.mu), hq'.1, I', I'', hI', hI'', rfl⟩
      rw [hB3 (b' + b'')] at hmem
      have := proj_sup (segLL F j) hJ1 (segPPB F j K m th (b' + b'')) (segPairs F j K m th o) (hPB _) b' b''
        (fun P1' P2' h => (hcomb b' b'' P1' P2').mpr ⟨h, hq'.2⟩) _ hmem
      rwa [proj_suppProj_map, suppProj_of_mem _ _ _ hw] at this
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy =>
      rw [MvPolynomial.smul_eq_C_mul, map_mul, map_C, ← MvPolynomial.smul_eq_C_mul]
      exact Submodule.smul_mem _ _ hy
  · intro hf
    obtain ⟨T, hT⟩ := proj_exists_sum O f₀
    rw [hT]
    refine Submodule.sum_mem _ fun d _ => ?_
    obtain ⟨c', c''⟩ := d
    show suppProj O (biSet c' c'') f₀ ∈ XXZ O (segPairs F j K m th o)
    have hg : MvPolynomial.map (algebraMap O (KK O)) (suppProj O (biSet c' c'') f₀) =
        suppProj (KK O) (biSet c' c'') (MvPolynomial.map (algebraMap O (KK O)) f₀) :=
      (proj_suppProj_map _ _ _).symm
    by_cases hok : ordOK F j o c' c''
    · have h2 : MvPolynomial.map (algebraMap O (KK O)) (suppProj O (biSet c' c'') f₀) ∈
          ⨆ q ∈ segPPB F j K m th (c' + c''), jointType (KK O) (segLL F j) q.1 q.2 := by
        rw [hg]
        exact proj_sup (segLL F j) hJ1 (segPairs F j K m th o) (segPPB F j K m th (c' + c''))
          (proj_segPairs_hasPaths F j m th o) c' c'' (fun P1 P2 h => ((hcomb c' c'' P1 P2).mp h).1) _ hf
      have h3 : suppProj O (biSet c' c'') f₀ ∈ (XXZ O (segPPB F j K m th (c' + c'')) : Set _) := by
        rw [hB3 (c' + c'')]; exact h2
      have h4 := proj_words (segLL F j) (hPol r) (hPol K) (segPPB F j K m th (c' + c'')) (segPairs F j K m th o)
        (hPB _) c' c'' (fun P1 P2 h => (hcomb c' c'' P1 P2).mpr ⟨h, hok⟩) _ h3
      rwa [suppProj_of_mem _ _ _ (suppProj_mem O _ f₀)] at h4
    · have h2 := proj_sup (segLL F j) hJ1 (segPairs F j K m th o) ∅
        (proj_segPairs_hasPaths F j m th o) c' c'' (fun P1 P2 h => absurd ((hcomb c' c'' P1 P2).mp h).2 hok) _ hf
      rw [← hg] at h2
      simp only [Set.mem_empty_iff_false, iSup_false, iSup_bot, Submodule.mem_bot] at h2
      have h0 : suppProj O (biSet c' c'') f₀ = 0 :=
        MvPolynomial.map_injective _ (IsFractionRing.injective O (KK O)) (h2.trans (map_zero _).symm)
      rw [h0]
      exact Submodule.zero_mem _

/- English proof (translation)
Establish `hA` using `proj_claimA F j O m th o hPol hJ1 hcomb hpaths hB3`. Use extensionality with `f`. Rewrite using `[h1]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨f₀, hf₀, rfl⟩`.

Conclude with `⟨_, (hA f₀).mp hf₀, (map_rename _ _ _).symm⟩`. Introduce and unpack `⟨t, ht, hte⟩`. Establish `hte' : rename (fun v : Fin (segN F j) × Fin (r + K) => (segE F j v.1, v.2)) t = MvPolynomial.map (algebraMap O (KK O)) f` using `hte`. Take `⟨f₀, hf₀⟩` from `exists_rename_eq_of_vars_subset_range f _ (segVar_injective F j (r + K)) (by`. Introduce `i hi`.

Establish `hi' : i ∈ (MvPolynomial.map (algebraMap O (KK O)) f).vars`. Rewrite using `[vars_map_of_injective _ (IsFractionRing.injective O (KK O))]`. Conclude with `Finset.mem_coe.mp hi`. Rewrite `hi'` using `[← hte']`. Take `⟨x, _, rfl⟩` from `mem_vars_rename _ _ hi'`.

Conclude with `⟨x, rfl⟩)`. Use `⟨f₀, ?_, hf₀⟩` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, hA f₀]`. Establish `: MvPolynomial.map (algebraMap O (KK O)) f₀ = t`. Apply `rename_injective _ (segVar_injective F j (r + K))` to reduce the goal to its premises.

Rewrite using `[← map_rename, hf₀, hte']`. Rewrite using `[this]`. Conclude with `ht`.
-/
theorem space_statement_fourth_clause [NeZero r] {K : ℕ} [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    (m : ℤ → ℤ) (th o : ℤ → ℝ)
    (h1 : XX' O r K F j m th o =
      Submodule.map (segRen F j O (r + K)).toLinearMap (XXZ O (segPairs F j K m th o)))
    (hPol : ∀ (n : ℕ) [NeZero n] (b : Fin (segN F j) → ℕ) (P : PPath n (segN F j) (segLL F j) b)
      (I : ℤ → Finset (Fin n)), IsSt P.mu I → Psi O P.mu I ∈ Pol O n b)
    (hJ1 : ∀ (b' b'' : Fin (segN F j) → ℕ) (P1 : PPath r (segN F j) (segLL F j) b')
      (P2 : PPath K (segN F j) (segLL F j) b''), jointType (KK O) (segLL F j) P1.mu P2.mu ≤ biPol (KK O) b' b'')
    (hcomb : ∀ (b' b'' : Fin (segN F j) → ℕ) (P1 : PPath r (segN F j) (segLL F j) b')
      (P2 : PPath K (segN F j) (segLL F j) b''), (P1.mu, P2.mu) ∈ segPairs F j K m th o ↔
        ((P1.mu, P2.mu) ∈ segPPB F j K m th (b' + b'') ∧ ordOK F j o b' b''))
    (hpaths : ∀ (B : Fin (segN F j) → ℕ) (q : (Fin (segN F j + 1) → Fin r → ℤ) × (Fin (segN F j + 1) → Fin K → ℤ)),
      q ∈ segPPB F j K m th B → ∃ b' b'' : Fin (segN F j) → ℕ, b' + b'' = B ∧
        (∃ P1 : PPath r (segN F j) (segLL F j) b', P1.mu = q.1) ∧
        ∃ P2 : PPath K (segN F j) (segLL F j) b'', P2.mu = q.2)
    (hB3 : ∀ B : Fin (segN F j) → ℕ, (XXZ O (segPPB F j K m th B) : Set _) =
      {f | MvPolynomial.map (algebraMap O (KK O)) f ∈
        ⨆ q ∈ segPPB F j K m th B, jointType (KK O) (segLL F j) q.1 q.2}) :
    (XX' O r K F j m th o : Set (SegRing O r K)) =
      {f | MvPolynomial.map (algebraMap O (KK O)) f ∈ Submodule.map (segRen F j (KK O) (r + K)).toLinearMap
        (⨆ q ∈ segPairs F j K m th o, jointType (KK O) (segLL F j) q.1 q.2)} := by
  classical
  have hA := proj_claimA F j O m th o hPol hJ1 hcomb hpaths hB3
  ext f
  rw [h1]
  constructor
  · rintro ⟨f₀, hf₀, rfl⟩
    exact ⟨_, (hA f₀).mp hf₀, (map_rename _ _ _).symm⟩
  · rintro ⟨t, ht, hte⟩
    have hte' : rename (fun v : Fin (segN F j) × Fin (r + K) => (segE F j v.1, v.2)) t =
        MvPolynomial.map (algebraMap O (KK O)) f := hte
    obtain ⟨f₀, hf₀⟩ := exists_rename_eq_of_vars_subset_range f _ (segVar_injective F j (r + K)) (by
      intro i hi
      have hi' : i ∈ (MvPolynomial.map (algebraMap O (KK O)) f).vars := by
        rw [vars_map_of_injective _ (IsFractionRing.injective O (KK O))]
        exact Finset.mem_coe.mp hi
      rw [← hte'] at hi'
      obtain ⟨x, _, rfl⟩ := mem_vars_rename _ _ hi'
      exact ⟨x, rfl⟩)
    refine ⟨f₀, ?_, hf₀⟩
    rw [SetLike.mem_coe, hA f₀]
    have : MvPolynomial.map (algebraMap O (KK O)) f₀ = t := by
      apply rename_injective _ (segVar_injective F j (r + K))
      rw [← map_rename, hf₀, hte']
    rw [this]
    exact ht

end Proj

section Fin2

open Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.CovariantDegrees

def LastInequalityClause (O : Type) [CommRing O] [IsDomain O] : Prop :=
  ∀ (N r K : ℕ) [NeZero r] [NeZero K] (LL : Letters (Fin N)) (B : Fin N → ℕ), N + r ≤ K → ∀ L : List (PathInequality N),
    (XXZ O {q : (Fin (N + 1) → Fin r → ℤ) × (Fin (N + 1) → Fin K → ℤ) |
        (∃ P : PPath (r + K) N LL B, P.mu = joinPT q.1 q.2) ∧ ∀ e ∈ L, e.Sat q.1 q.2} : Set _) =
      {f | MvPolynomial.map (algebraMap O (KK O)) f ∈
        ⨆ q ∈ {q : (Fin (N + 1) → Fin r → ℤ) × (Fin (N + 1) → Fin K → ℤ) |
          (∃ P : PPath (r + K) N LL B, P.mu = joinPT q.1 q.2) ∧ ∀ e ∈ L, e.Sat q.1 q.2}, jointType (KK O) LL q.1 q.2}

/- English proof (translation)
Introduce `N r K _ _ LL B hK L`. Establish `hanti : StrictAnti (fun i : Fin N => N - i.val)`. Introduce `a b hab`. Establish `h1` using `a.2`. Establish `h2` using `b.2`.

Establish `h3 : a.val < b.val` using `hab`. Use `show N - b.val < N - a.val`. Use linear arithmetic over natural numbers and integers. Conclude with `(h p O S N r K LL B (fun i => N - i.val) hK hanti (fun i => Nat.sub_pos_of_lt i.2) _ (fun q hq => hq.1)).2.2 L rfl`.
-/
theorem last_inequality_clause_of_lemma (D : Formalism.BasicNotions.D7) (h : ConclusionB3 D) (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (S : UniformizedDVR p O) : LastInequalityClause O := by
  intro N r K _ _ LL B hK L
  have hanti : StrictAnti (fun i : Fin N => N - i.val) := by
    intro a b hab
    have h1 := a.2
    have h2 := b.2
    have h3 : a.val < b.val := hab
    show N - b.val < N - a.val
    omega
  exact (h p O S N r K LL B (fun i => N - i.val) hK hanti (fun i => Nat.sub_pos_of_lt i.2) _
    (fun q hq => hq.1)).2.2 L rfl

/- English proof (translation)
Introduce `n' r K _ _ _ F L₁ N₁ j m th o hV hK hm hchar`. Establish `: CharZero O` using `hchar`. Conclude with `space_statement_fourth_clause F j O m th o (first_clause_segment_rename (K := K) F j O h3 m th o) (fun n _ b P I hI => (standard_polynomial_mem_bounds (segLL F j) b (h3 _ n _ b) P I hI).1) (fun b' b'' P1 P2 => jointType_le_biPol (KK O) (segLL F j) b' b'' P1 P2) (fun b' b'' P1 P2 …`.
-/
theorem fourth_clause_of_lemmas (D : Formalism.BasicNotions.D7) (hB1 : RotatedSumBound D) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (h3 : StandardBasisAllData O) (hB3 : LastInequalityClause O) : FourthClauseAtRing O := by
  intro n' r K _ _ _ F L₁ N₁ j m th o hV hK hm hchar
  have : CharZero O := hchar
  exact space_statement_fourth_clause F j O m th o (first_clause_segment_rename (K := K) F j O h3 m th o)
    (fun n _ b P I hI => (standard_polynomial_mem_bounds (segLL F j) b (h3 _ n _ b) P I hI).1)
    (fun b' b'' P1 P2 => jointType_le_biPol (KK O) (segLL F j) b' b'' P1 P2)
    (fun b' b'' P1 P2 => segPairs_iff F j D hB1 L₁ N₁ hV hK m hm th o b' b'' P1 P2)
    (fun B q hq => segPPB_paths F j D hB1 hK m th B q hq)
    (fun B => hB3 _ r K (segLL F j) B hK (segL F j m th))

/- English proof (translation)
Rewrite using `[space_statement_iff_forall_dvr]`. Introduce `p _ O _ _ _ S`. Establish `h3 : StandardBasisAllData O` using `fun N n _ LL B th M => (hA3 p O S N n LL B th M).1`. Establish `h3F : StandardBasisAllData (FF O)` using `fun N n _ LL B th M => (hA3 p O S N n LL B th M).2`. Conclude with `space_statement_at_ring_of_basis O (fun N n _ LL B => hA2 O N n LL B) h3 h3F (fourth_clause_of_lemmas D hB1 O h3 (last_inequality_clause_of_lemma D hB3 p O S))`.
-/
theorem space_statement_of_lemmas (D : Formalism.BasicNotions.D7) (hA2 : HyperplaneRank D) (hA3 : DefiniteRankOne D) (hB1 : RotatedSumBound D) (hB3 : ConclusionB3 D) :
    Formalism.MainNotions.SelectionLemmas.NestedTypeBound D := by
  rw [space_statement_iff_forall_dvr]
  intro p _ O _ _ _ S
  have h3 : StandardBasisAllData O := fun N n _ LL B th M => (hA3 p O S N n LL B th M).1
  have h3F : StandardBasisAllData (FF O) := fun N n _ LL B th M => (hA3 p O S N n LL B th M).2
  exact space_statement_at_ring_of_basis O (fun N n _ LL B => hA2 O N n LL B) h3 h3F (fourth_clause_of_lemmas D hB1 O h3 (last_inequality_clause_of_lemma D hB3 p O S))

end Fin2

section Fin3

open Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.CovariantDegrees

/- English proof (translation)
Introduce `p _ O _ _ _ S n' r K _ _ _ Fr j m th o`. Establish `h3 : StandardBasisAllData O` using `fun N n _ LL B th M => (hA3 p O S N n LL B th M).1`. Establish `h3F : StandardBasisAllData (FF O)` using `fun N n _ LL B th M => (hA3 p O S N n LL B th M).2`. Conclude with `⟨fun A G M hA hG hc ho => space_criterion_clause O n' r K Fr j m th o A G M hA hG hc ho, space_statement_sixth_clause O n' r K Fr j m th o (first_clause_segment_rename (K := K) Fr j O h3 m th o) (fun A G M hA hG hc ho => crit_words Fr j (FF O) h3F m th o A G M hA hG hc ho)⟩`.
-/
theorem space_criterion_of_standard_basis (D : Formalism.BasicNotions.D7) (hA3 : DefiniteRankOne D) : Formalism.MainNotions.SourceCleaning.SpaceCriterionModuloUniformiser D := by
  intro p _ O _ _ _ S n' r K _ _ _ Fr j m th o
  have h3 : StandardBasisAllData O := fun N n _ LL B th M => (hA3 p O S N n LL B th M).1
  have h3F : StandardBasisAllData (FF O) := fun N n _ LL B th M => (hA3 p O S N n LL B th M).2
  exact ⟨fun A G M hA hG hc ho => space_criterion_clause O n' r K Fr j m th o A G M hA hG hc ho,
    space_statement_sixth_clause O n' r K Fr j m th o (first_clause_segment_rename (K := K) Fr j O h3 m th o)
      (fun A G M hA hG hc ho => crit_words Fr j (FF O) h3F m th o A G M hA hG hc ho)⟩

end Fin3

end Formalism.MainNotions.G.Joints.StandardMonomialSpace

namespace Formalism.MainNotions.G.Joints

/- English proof (translation)
The claim follows from `StandardMonomialSpace.transport_statement_holds D`.
-/
theorem transport_statement_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.SelectionLemmas.TypeDecompositionsCommute D := StandardMonomialSpace.transport_statement_holds D

/- English proof (translation)
The claim follows from `StandardMonomialSpace.valuation_transport_of_lemma D h`.
-/
theorem valuation_transport_of_lemma (D : Formalism.BasicNotions.D7) (h : Formalism.MainNotions.CovariantDegrees.ValuationsAdditive D) : Formalism.MainNotions.SelectionLemmas.admB2 D := StandardMonomialSpace.valuation_transport_of_lemma D h

/- English proof (translation)
The claim follows from `StandardMonomialSpace.space_statement_of_lemmas D hA2 hA3 hB1 hB3`.
-/
theorem space_statement_of_lemmas (D : Formalism.BasicNotions.D7) (hA2 : Formalism.MainNotions.CovariantDegrees.HyperplaneRank D) (hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D)
    (hB1 : Formalism.MainNotions.CovariantDegrees.RotatedSumBound D) (hB3 : Formalism.MainNotions.CovariantDegrees.ConclusionB3 D) : Formalism.MainNotions.SelectionLemmas.NestedTypeBound D :=
  StandardMonomialSpace.space_statement_of_lemmas D hA2 hA3 hB1 hB3

/- English proof (translation)
The claim follows from `StandardMonomialSpace.space_criterion_of_standard_basis D hA3`.
-/
theorem space_criterion_of_standard_basis (D : Formalism.BasicNotions.D7) (hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D) : Formalism.MainNotions.SourceCleaning.SpaceCriterionModuloUniformiser D :=
  StandardMonomialSpace.space_criterion_of_standard_basis D hA3

end Formalism.MainNotions.G.Joints
