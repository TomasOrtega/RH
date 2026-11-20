import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.FlagDimSt
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

namespace FlagDim

abbrev UIdx (n : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2} ⊕ Fin (n - 1)

def uMat (F : Type) [Field F] (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (UIdx n) F) :=
  Matrix.of fun r c =>
    if h : r < c then X (Sum.inl ⟨(r, c), h⟩)
    else if h' : r = c ∧ r.val + 1 < n then X (Sum.inr ⟨r.val, by omega⟩) else 0

/- English proof (translation)
Simplify using `only [uMat, Matrix.of_apply]`. Rewrite using `[dif_neg (by omega), dif_neg (by omega)]`.
-/
theorem uMat_of_lt (F : Type) [Field F] {n : ℕ} {r c : Fin n} (h : c < r) : uMat F n r c = 0 := by
  simp only [uMat, Matrix.of_apply]
  rw [dif_neg (by omega), dif_neg (by omega)]

/- English proof (translation)
Simplify using `[uMat, hr]`.
-/
theorem uMat_diag (F : Type) [Field F] {n : ℕ} (r : ℕ) (hr : r + 1 < n) :
    uMat F n ⟨r, by omega⟩ ⟨r, by omega⟩ = X (Sum.inr ⟨r, by omega⟩) := by
  simp [uMat, hr]

def toUpper (F : Type) [Field F] (n : ℕ) :
    MvPolynomial (Fin n × Fin n) F →ₐ[F] MvPolynomial (UIdx n) F :=
  aeval fun p => uMat F n p.1 p.2

def flagMinorMap (F : Type) [Field F] (n : ℕ) :
    MRingOver F (PluckerBlocks n n) →ₐ[F] MvPolynomial (Fin n × Fin n) F :=
  aeval fun q : Σ j, PluckerBlocks n n j => flagMinor (genMat F n) q.1 q.2

/- English proof (translation)
Simplify using `only [flagMinor]`. Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression.
-/
theorem flagMinor_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n N1 : ℕ}
    (M : Matrix (Fin n) (Fin N1) R) (j : Fin (n - 1)) (T : PluckerBlocks N1 n j) :
    flagMinor (M.map f) j T = f (flagMinor M j T) := by
  simp only [flagMinor]
  rw [RingHom.map_det]
  rfl

/- English proof (translation)
Use extensionality with `r c`. Simplify using `[genMat, toUpper]`.
-/
theorem toUpper_genMat (F : Type) [Field F] (n : ℕ) :
    (genMat F n).map (toUpper F n) = uMat F n := by
  ext r c
  simp [genMat, toUpper]

/- English proof (translation)
Rewrite using `[AlgHom.comp_apply, flagMinorMap, aeval_X, ← toUpper_genMat F n]`. Conclude with `(flagMinor_map (toUpper F n).toRingHom _ _ _).symm`.
-/
theorem toUpper_flagMinorMap_X (F : Type) [Field F] (n : ℕ) (q : Σ j, PluckerBlocks n n j) :
    (toUpper F n).comp (flagMinorMap F n) (X q) = flagMinor (uMat F n) q.1 q.2 := by
  rw [AlgHom.comp_apply, flagMinorMap, aeval_X, ← toUpper_genMat F n]
  exact (flagMinor_map (toUpper F n).toRingHom _ _ _).symm

def rowCols {n : ℕ} (r : ℕ) (c : Fin n) : Fin (r + 1) → Fin n :=
  fun i => if h : i.val < r ∧ i.val < c.val then ⟨i.val, by omega⟩ else c

/- English proof (translation)
Introduce `a b hab`. Simplify using `only [rowCols]`. Apply the tactic sequence `split_ifs with h1 h2 h2 <;> simp only [Fin.lt_def] at * <;> omega`.
-/
theorem rowCols_strictMono {n : ℕ} (r : ℕ) (c : Fin n) (hc : r ≤ c.val) :
    StrictMono (rowCols r c) := by
  intro a b hab
  simp only [rowCols]
  split_ifs with h1 h2 h2 <;> simp only [Fin.lt_def] at * <;> omega

def colSet {n : ℕ} (r : ℕ) (c : Fin n) : Finset (Fin n) := Finset.univ.image (rowCols r c)

/- English proof (translation)
Rewrite using `[colSet, Finset.card_image_of_injective _ (rowCols_strictMono r c hc).injective]`. Simplify using the standard rewrite rules.
-/
theorem colSet_card {n : ℕ} (r : ℕ) (c : Fin n) (hc : r ≤ c.val) : (colSet r c).card = r + 1 := by
  rw [colSet, Finset.card_image_of_injective _ (rowCols_strictMono r c hc).injective]
  simp

/- English proof (translation)
The claim follows from `(Finset.orderEmbOfFin_unique (colSet_card r c hc) (fun x => Finset.mem_image_of_mem _ (Finset.mem_univ x)) (rowCols_strictMono r c hc)).symm`.
-/
theorem orderEmbOfFin_colSet {n : ℕ} (r : ℕ) (c : Fin n) (hc : r ≤ c.val) :
    ⇑((colSet r c).orderEmbOfFin (colSet_card r c hc)) = rowCols r c :=
  (Finset.orderEmbOfFin_unique (colSet_card r c hc) (fun x => Finset.mem_image_of_mem _ (Finset.mem_univ x))
    (rowCols_strictMono r c hc)).symm

/- English proof (translation)
Establish `hj` using `j.2`. Simplify using `only [flagMinor]`. Rewrite using `[orderEmbOfFin_colSet j.val c hc, Matrix.det_of_isUpperTriangular, Fin.prod_univ_castSucc]`. Use `congr 1`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations.

Simplify using `only [Matrix.submatrix_apply, rowCols, Fin.val_castSucc, dif_pos (And.intro k.2 (by omega : k.val < c.val))]`. Both sides reduce to the same expression. Simplify using `only [Matrix.submatrix_apply, rowCols, Fin.val_last, lt_irrefl, false_and, dif_neg, not_false_eq_true]`. Both sides reduce to the same expression. Introduce `a b hab`.

Simplify using `only [Matrix.submatrix_apply]`. Apply `uMat_of_lt` to reduce the goal to its premises. Simplify using `only [rowCols]`. Establish `hb : b.val < j.val` using `by simp only [id, Fin.lt_def] at hab; omega`. Rewrite using `[dif_pos ⟨hb, by omega⟩]`.

Simplify using `only [Fin.lt_def, Fin.val_castLE] at hab ⊢`. Conclude with `hab`.
-/
theorem flagMinor_uMat_colSet (F : Type) [Field F] {n : ℕ} (j : Fin (n - 1)) (c : Fin n) (hc : j.val ≤ c.val) :
    flagMinor (uMat F n) j ⟨colSet j.val c, colSet_card j.val c hc⟩ =
      (∏ k : Fin j.val, uMat F n ⟨k.val, by omega⟩ ⟨k.val, by omega⟩) * uMat F n ⟨j.val, by omega⟩ c := by
  have hj := j.2
  simp only [flagMinor]
  rw [orderEmbOfFin_colSet j.val c hc, Matrix.det_of_isUpperTriangular, Fin.prod_univ_castSucc]
  · congr 1
    · refine Finset.prod_congr rfl fun k _ => ?_
      simp only [Matrix.submatrix_apply, rowCols, Fin.val_castSucc, dif_pos (And.intro k.2 (by omega : k.val < c.val))]
      rfl
    · simp only [Matrix.submatrix_apply, rowCols, Fin.val_last, lt_irrefl, false_and, dif_neg, not_false_eq_true]
      rfl
  · intro a b hab
    simp only [Matrix.submatrix_apply]
    apply uMat_of_lt
    simp only [rowCols]
    have hb : b.val < j.val := by simp only [id, Fin.lt_def] at hab; omega
    rw [dif_pos ⟨hb, by omega⟩]
    simp only [Fin.lt_def, Fin.val_castLE] at hab ⊢
    exact hab

section RowReduce

variable {K : Type} [Field K] {n : ℕ}

def leadBlock (T : Matrix (Fin n) (Fin n) K) (i : Fin n) : Matrix (Fin i.val) (Fin i.val) K :=
  T.submatrix (Fin.castLE i.2.le) (Fin.castLE i.2.le)

def redCoeff (T : Matrix (Fin n) (Fin n) K) (i : Fin n) : Fin i.val → K :=
  Matrix.vecMul (fun c : Fin i.val => T i (Fin.castLE i.2.le c)) (leadBlock T i)⁻¹

def redMat (T : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i k => if h : k.val < i.val then redCoeff T i ⟨k.val, h⟩ else 0

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Use `symm`. Use `Fintype.sum_of_injective (Fin.castLE i.2.le) (Fin.castLE_injective _) _ _ ?_ ?_` and prove the remaining obligations. Introduce `k hk`. Establish `hki : ¬ k.val < i.val` using `fun h => hk ⟨⟨k.val, h⟩, rfl⟩`.

Simplify using `only [redMat, Matrix.of_apply]`. Rewrite using `[dif_neg hki, zero_mul]`. Introduce `k`. Simplify using `only [redMat, Matrix.of_apply, Fin.val_castLE]`. Rewrite using `[dif_pos k.2]`.
-/
theorem redMat_mul_apply (T : Matrix (Fin n) (Fin n) K) (i c : Fin n) :
    (redMat T * T) i c = ∑ k : Fin i.val, redCoeff T i k * T (Fin.castLE i.2.le k) c := by
  rw [Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE i.2.le) (Fin.castLE_injective _) _ _ ?_ ?_
  · intro k hk
    have hki : ¬ k.val < i.val := fun h => hk ⟨⟨k.val, h⟩, rfl⟩
    simp only [redMat, Matrix.of_apply]
    rw [dif_neg hki, zero_mul]
  · intro k
    simp only [redMat, Matrix.of_apply, Fin.val_castLE]
    rw [dif_pos k.2]

/- English proof (translation)
Rewrite using `[Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, redMat_mul_apply]`. Establish `h1 : Matrix.vecMul (redCoeff T i) (leadBlock T i) = fun c : Fin i.val => T i (Fin.castLE i.2.le c)`. Rewrite using `[redCoeff, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (hT i)), Matrix.vecMul_one]`. Establish `h2` using `congrFun h1 ⟨c.val, hc⟩`. Establish `hcc : (Fin.castLE i.2.le ⟨c.val, hc⟩ : Fin n) = c` using `Fin.ext rfl`.

Simplify using `only [Matrix.vecMul, dotProduct, leadBlock, Matrix.submatrix_apply, hcc] at h2`. Rewrite using `[h2, sub_self]`.
-/
theorem reduce_apply_of_lt (T : Matrix (Fin n) (Fin n) K) (hT : ∀ i, (leadBlock T i).det ≠ 0)
    (i c : Fin n) (hc : c < i) : ((1 - redMat T) * T) i c = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, redMat_mul_apply]
  have h1 : Matrix.vecMul (redCoeff T i) (leadBlock T i) = fun c : Fin i.val => T i (Fin.castLE i.2.le c) := by
    rw [redCoeff, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (hT i)),
      Matrix.vecMul_one]
  have h2 := congrFun h1 ⟨c.val, hc⟩
  have hcc : (Fin.castLE i.2.le ⟨c.val, hc⟩ : Fin n) = c := Fin.ext rfl
  simp only [Matrix.vecMul, dotProduct, leadBlock, Matrix.submatrix_apply, hcc] at h2
  rw [h2, sub_self]

/- English proof (translation)
Establish `hki : ¬ k.val < i.val` using `by omega`. Simplify using `only [redMat, Matrix.sub_apply, Matrix.of_apply, Matrix.one_apply_ne (ne_of_lt h)]`. Rewrite using `[dif_neg hki, sub_zero]`.
-/
theorem reduce_lower (T : Matrix (Fin n) (Fin n) K) (i k : Fin n) (h : i < k) :
    (1 - redMat T) i k = 0 := by
  have hki : ¬ k.val < i.val := by omega
  simp only [redMat, Matrix.sub_apply, Matrix.of_apply, Matrix.one_apply_ne (ne_of_lt h)]
  rw [dif_neg hki, sub_zero]

/- English proof (translation)
Simplify using `only [redMat, Matrix.sub_apply, Matrix.of_apply, Matrix.one_apply_eq]`. Rewrite using `[dif_neg (lt_irrefl _), sub_zero]`.
-/
theorem reduce_diag (T : Matrix (Fin n) (Fin n) K) (i : Fin n) : (1 - redMat T) i i = 1 := by
  simp only [redMat, Matrix.sub_apply, Matrix.of_apply, Matrix.one_apply_eq]
  rw [dif_neg (lt_irrefl _), sub_zero]

end RowReduce

/- English proof (translation)
Establish `hj` using `j.2`. Simplify using `only [flagMinor]`. Establish `key : (E * M).submatrix (Fin.castLE (by omega) : Fin (j.val + 1) → Fin n) (S.1.orderEmbOfFin S.2) = E.submatrix (Fin.castLE (by omega) : Fin (j.val + 1) → Fin n) (Fin.castLE (by omega)) * M.submatrix (Fin.castLE (by omega) : Fin (j.val + 1) → Fin n) (S.1.orderEmbOfFin S.2)`. Use extensionality with `a b`. Simplify using `only [Matrix.submatrix_apply, Matrix.mul_apply]`.

Use `symm`. Use `Fintype.sum_of_injective (Fin.castLE (by omega)) (Fin.castLE_injective _) _ _ ?_ ?_` and prove the remaining obligations. Introduce `k hk`. Establish `hk' : ¬ k.val < j.val + 1` using `fun h => hk ⟨⟨k.val, h⟩, rfl⟩`. Rewrite using `[hE _ _ (by simp only [Fin.lt_def, Fin.val_castLE]; omega), zero_mul]`.

Introduce `k`. Both sides reduce to the same expression. Rewrite using `[key, Matrix.det_mul, Matrix.det_of_isLowerTriangular, Finset.prod_eq_one, one_mul]`. Introduce `i _`. Simplify using `[hE1]`.

Introduce `a b hab`. Simplify using `only [Matrix.submatrix_apply]`. Apply `hE` to reduce the goal to its premises. Simplify using `only [OrderDual.toDual_lt_toDual] at hab`. Simplify using `only [Fin.lt_def, Fin.val_castLE] at hab ⊢`.

Conclude with `hab`.
-/
theorem flagMinor_lowerUni_mul {R : Type} [CommRing R] {n : ℕ} (E M : Matrix (Fin n) (Fin n) R)
    (hE : ∀ i k, i < k → E i k = 0) (hE1 : ∀ i, E i i = 1) (j : Fin (n - 1)) (S : PluckerBlocks n n j) :
    flagMinor (E * M) j S = flagMinor M j S := by
  have hj := j.2
  simp only [flagMinor]
  have key : (E * M).submatrix (Fin.castLE (by omega) : Fin (j.val + 1) → Fin n) (S.1.orderEmbOfFin S.2) =
      E.submatrix (Fin.castLE (by omega) : Fin (j.val + 1) → Fin n) (Fin.castLE (by omega)) *
        M.submatrix (Fin.castLE (by omega) : Fin (j.val + 1) → Fin n) (S.1.orderEmbOfFin S.2) := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    symm
    refine Fintype.sum_of_injective (Fin.castLE (by omega)) (Fin.castLE_injective _) _ _ ?_ ?_
    · intro k hk
      have hk' : ¬ k.val < j.val + 1 := fun h => hk ⟨⟨k.val, h⟩, rfl⟩
      rw [hE _ _ (by simp only [Fin.lt_def, Fin.val_castLE]; omega), zero_mul]
    · intro k
      rfl
  rw [key, Matrix.det_mul, Matrix.det_of_isLowerTriangular, Finset.prod_eq_one, one_mul]
  · intro i _
    simp [hE1]
  · intro a b hab
    simp only [Matrix.submatrix_apply]
    apply hE
    simp only [OrderDual.toDual_lt_toDual] at hab
    simp only [Fin.lt_def, Fin.val_castLE] at hab ⊢
    exact hab

section Generic

variable (F : Type) [Field F] (n : ℕ)

abbrev GenField : Type := FractionRing (MvPolynomial (Fin n × Fin n) F)

def genMatK : Matrix (Fin n) (Fin n) (GenField F n) := (genMat F n).map (algebraMap _ _)

/- English proof (translation)
Establish `e : leadBlock (genMatK F n) i = (leadBlock (genMat F n) i).map (algebraMap _ (GenField F n))` using `rfl`. Rewrite using `[e]`. Express the relevant statement in the definitionally equal form `((algebraMap _ (GenField F n)).mapMatrix (leadBlock (genMat F n) i)).det ≠ 0`. Rewrite using `[← RingHom.map_det]`. Introduce `h`.

Establish `h2` using `IsFractionRing.injective (MvPolynomial (Fin n × Fin n) F) (GenField F n) (h.trans (map_zero _).symm)`. Establish `h3` using `congrArg (MvPolynomial.eval fun p : Fin n × Fin n => if p.1 = p.2 then (1 : F) else 0) h2`. Rewrite `h3` using `[RingHom.map_det, map_zero]`. Establish `e2 : (MvPolynomial.eval fun p : Fin n × Fin n => if p.1 = p.2 then (1 : F) else 0).mapMatrix (leadBlock (genMat F n) i) = 1`. Use extensionality with `a b`.

Simplify using `[leadBlock, genMat, Matrix.one_apply, Fin.ext_iff]`. Rewrite `h3` using `[e2, Matrix.det_one]`. Conclude with `one_ne_zero h3`.
-/
theorem leadBlock_genMatK_det_ne_zero (i : Fin n) : (leadBlock (genMatK F n) i).det ≠ 0 := by
  have e : leadBlock (genMatK F n) i =
      (leadBlock (genMat F n) i).map (algebraMap _ (GenField F n)) := rfl
  rw [e]
  change ((algebraMap _ (GenField F n)).mapMatrix (leadBlock (genMat F n) i)).det ≠ 0
  rw [← RingHom.map_det]
  intro h
  have h2 := IsFractionRing.injective (MvPolynomial (Fin n × Fin n) F) (GenField F n)
    (h.trans (map_zero _).symm)
  have h3 := congrArg (MvPolynomial.eval fun p : Fin n × Fin n => if p.1 = p.2 then (1 : F) else 0) h2
  rw [RingHom.map_det, map_zero] at h3
  have e2 : (MvPolynomial.eval fun p : Fin n × Fin n => if p.1 = p.2 then (1 : F) else 0).mapMatrix
      (leadBlock (genMat F n) i) = 1 := by
    ext a b
    simp [leadBlock, genMat, Matrix.one_apply, Fin.ext_iff]
  rw [e2, Matrix.det_one] at h3
  exact one_ne_zero h3

def genRed : Matrix (Fin n) (Fin n) (GenField F n) := (1 - redMat (genMatK F n)) * genMatK F n

def fromUpper : MvPolynomial (UIdx n) F →ₐ[F] GenField F n :=
  aeval fun u => match u with
    | Sum.inl p => genRed F n p.1.1 p.1.2
    | Sum.inr r => genRed F n ⟨r.val, by omega⟩ ⟨r.val, by omega⟩

/- English proof (translation)
Break down `lt_trichotomy r c with h | h | h` into its components or cases. Simplify using `[uMat, h, fromUpper]`. Substitute `h` using the available equality. Simplify using `[uMat, hr, fromUpper]`. Rewrite using `[uMat_of_lt F h, map_zero, genRed, reduce_apply_of_lt _ (leadBlock_genMatK_det_ne_zero F n) _ _ h]`.
-/
theorem fromUpper_uMat (r c : Fin n) (hr : r.val + 1 < n) :
    fromUpper F n (uMat F n r c) = genRed F n r c := by
  rcases lt_trichotomy r c with h | h | h
  · simp [uMat, h, fromUpper]
  · subst h
    simp [uMat, hr, fromUpper]
  · rw [uMat_of_lt F h, map_zero, genRed,
      reduce_apply_of_lt _ (leadBlock_genMatK_det_ne_zero F n) _ _ h]

/- English proof (translation)
Establish `hj` using `j.2`. Establish `e1 : fromUpper F n (flagMinor (uMat F n) j S) = flagMinor ((uMat F n).map (fromUpper F n).toRingHom) j S` using `(flagMinor_map _ _ _ _).symm`. Rewrite using `[e1, ← flagMinor_map]`. Establish `: flagMinor ((uMat F n).map (fromUpper F n).toRingHom) j S = flagMinor (genRed F n) j S`. Simplify using `only [flagMinor]`.

Use `congr 1`. Use extensionality with `a b`. Simplify using `only [Matrix.submatrix_apply, Matrix.map_apply]`. Conclude with `fromUpper_uMat F n _ _ (by simp only [Fin.val_castLE]; omega)`. Rewrite using `[this, genRed, flagMinor_lowerUni_mul _ _ (reduce_lower _) (reduce_diag _)]`.

Both sides reduce to the same expression.
-/
theorem fromUpper_flagMinor (j : Fin (n - 1)) (S : PluckerBlocks n n j) :
    fromUpper F n (flagMinor (uMat F n) j S) =
      algebraMap _ (GenField F n) (flagMinor (genMat F n) j S) := by
  have hj := j.2
  have e1 : fromUpper F n (flagMinor (uMat F n) j S) =
      flagMinor ((uMat F n).map (fromUpper F n).toRingHom) j S := (flagMinor_map _ _ _ _).symm
  rw [e1, ← flagMinor_map]
  have : flagMinor ((uMat F n).map (fromUpper F n).toRingHom) j S = flagMinor (genRed F n) j S := by
    simp only [flagMinor]
    congr 1
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.map_apply]
    exact fromUpper_uMat F n _ _ (by simp only [Fin.val_castLE]; omega)
  rw [this, genRed, flagMinor_lowerUni_mul _ _ (reduce_lower _) (reduce_diag _)]
  rfl

/- English proof (translation)
Use extensionality with `f`. Simplify using `only [RingHom.mem_ker]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[AlgHom.comp_apply, h, map_zero]`.

Introduce `h`. Establish `key : (fromUpper F n).comp ((toUpper F n).comp (flagMinorMap F n)) = (IsScalarTower.toAlgHom F (MvPolynomial (Fin n × Fin n) F) (GenField F n)).comp (flagMinorMap F n)`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `q`. Rewrite using `[AlgHom.comp_apply, toUpper_flagMinorMap_X, fromUpper_flagMinor, AlgHom.comp_apply, flagMinorMap, aeval_X]`.

Both sides reduce to the same expression. Establish `h2` using `congrArg (fun g : MRingOver F (PluckerBlocks n n) →ₐ[F] GenField F n => g f) key`. Simplify using `only [AlgHom.comp_apply] at h2 h`. Rewrite `h2` using `[h, map_zero, IsScalarTower.coe_toAlgHom']`. Conclude with `IsFractionRing.injective (MvPolynomial (Fin n × Fin n) F) (GenField F n) (h2.symm.trans (map_zero _).symm)`.
-/
theorem ker_flagMinorMap_eq :
    RingHom.ker (flagMinorMap F n) = RingHom.ker ((toUpper F n).comp (flagMinorMap F n)) := by
  ext f
  simp only [RingHom.mem_ker]
  constructor
  · intro h
    rw [AlgHom.comp_apply, h, map_zero]
  · intro h
    have key : (fromUpper F n).comp ((toUpper F n).comp (flagMinorMap F n)) =
        (IsScalarTower.toAlgHom F (MvPolynomial (Fin n × Fin n) F) (GenField F n)).comp
          (flagMinorMap F n) := by
      apply MvPolynomial.algHom_ext
      intro q
      rw [AlgHom.comp_apply, toUpper_flagMinorMap_X, fromUpper_flagMinor, AlgHom.comp_apply,
        flagMinorMap, aeval_X]
      rfl
    have h2 := congrArg (fun g : MRingOver F (PluckerBlocks n n) →ₐ[F] GenField F n => g f) key
    simp only [AlgHom.comp_apply] at h2 h
    rw [h, map_zero, IsScalarTower.coe_toAlgHom'] at h2
    exact IsFractionRing.injective (MvPolynomial (Fin n × Fin n) F) (GenField F n)
      (h2.symm.trans (map_zero _).symm)

end Generic

/- English proof (translation)
Use `⟨Polynomial.C a * Polynomial.X - Polynomial.C b, ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`. Establish `h1` using `congrArg (fun p : Polynomial R => p.coeff 1) h0`. Simplify using `at h1`. Conclude with `ha h1`.

Simplify using `[h]`.
-/
theorem isAlgebraic_of_mul_eq {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {a b : R} {y : A}
    (ha : a ≠ 0) (h : algebraMap R A a * y = algebraMap R A b) : IsAlgebraic R y := by
  refine ⟨Polynomial.C a * Polynomial.X - Polynomial.C b, ?_, ?_⟩
  · intro h0
    have h1 := congrArg (fun p : Polynomial R => p.coeff 1) h0
    simp at h1
    exact ha h1
  · simp [h]

def ltPairsEquiv (n : ℕ) : {p : Fin n × Fin n // p.1 < p.2} ≃ Σ c : Fin n, Fin c.val where
  toFun p := ⟨p.1.2, ⟨p.1.1.val, p.2⟩⟩
  invFun q := ⟨(⟨q.2.val, q.2.2.trans q.1.2⟩, q.1), q.2.2⟩
  left_inv := by rintro ⟨⟨a, b⟩, h⟩; rfl
  right_inv := by rintro ⟨c, k⟩; rfl

/- English proof (translation)
Rewrite using `[Fintype.card_congr (ltPairsEquiv n), Fintype.card_sigma]`. Simplify using `only [Fintype.card_fin]`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]`. Both sides reduce to the same expression.
-/
theorem card_ltPairs (n : ℕ) : Fintype.card {p : Fin n × Fin n // p.1 < p.2} = flagDim n := by
  rw [Fintype.card_congr (ltPairsEquiv n), Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]
  rfl

/- English proof (translation)
Rewrite using `[Fintype.card_sum, card_ltPairs, Fintype.card_fin]`.
-/
theorem card_UIdx (n : ℕ) : Fintype.card (UIdx n) = flagDim n + (n - 1) := by
  rw [Fintype.card_sum, card_ltPairs, Fintype.card_fin]

section Trdeg

variable (F : Type) [Field F] (n : ℕ)

def diagProd (r : ℕ) (hr : r < n) : MvPolynomial (UIdx n) F :=
  ∏ k : Fin r, uMat F n ⟨k.val, by omega⟩ ⟨k.val, by omega⟩

/- English proof (translation)
The claim follows from `Fin.prod_univ_zero _`.
-/
theorem diagProd_zero (h : 0 < n) : diagProd F n 0 h = 1 := Fin.prod_univ_zero _

/- English proof (translation)
Rewrite using `[diagProd, Fin.prod_univ_castSucc]`. Both sides reduce to the same expression.
-/
theorem diagProd_succ (i : ℕ) (h : i + 1 < n) :
    diagProd F n (i + 1) h = diagProd F n i (by omega) * uMat F n ⟨i, by omega⟩ ⟨i, by omega⟩ := by
  rw [diagProd, Fin.prod_univ_castSucc]
  rfl

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem diagProd_congr {r s : ℕ} (hr : r < n) (hs : s < n) (h : r = s) : diagProd F n r hr = diagProd F n s hs := by
  subst h
  rfl

/- English proof (translation)
Rewrite using `[diagProd, Finset.prod_ne_zero_iff]`. Introduce `k _`. Rewrite using `[uMat_diag F k.val (by omega)]`. Conclude with `X_ne_zero _`.
-/
theorem diagProd_ne_zero (r : ℕ) (hr : r < n) : diagProd F n r hr ≠ 0 := by
  rw [diagProd, Finset.prod_ne_zero_iff]
  intro k _
  rw [uMat_diag F k.val (by omega)]
  exact X_ne_zero _

abbrev upperKer : Ideal (MRingOver F (PluckerBlocks n n)) := RingHom.ker ((toUpper F n).comp (flagMinorMap F n))

instance upperKer_isPrime : (upperKer F n).IsPrime := RingHom.ker_isPrime _

abbrev UpperQuot : Type := MRingOver F (PluckerBlocks n n) ⧸ upperKer F n

/- English proof (translation)
Establish `hj` using `j.2`. Break down `Nat.eq_zero_or_pos j.val with h0 | hpos` into its components or cases. Use `⟨1, ?_⟩` and prove the remaining obligations. Rewrite using `[map_one, diagProd_congr F n _ (by omega) h0, diagProd_zero]`. Take `⟨i, hi⟩ : ∃ i : ℕ, j.val = i + 1` from `⟨j.val - 1, by omega⟩`.

Use `⟨Ideal.Quotient.mk _ (X ⟨⟨i, by omega⟩, ⟨colSet i ⟨i, by omega⟩, colSet_card i _ le_rfl⟩⟩), ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.kerLiftAlg_mk, toUpper_flagMinorMap_X]`. Simplify using `only`. Rewrite using `[flagMinor_uMat_colSet F (n := n) ⟨i, by omega⟩ ⟨i, by omega⟩ le_rfl, diagProd_congr F n _ (by omega) hi, diagProd_succ]`. Both sides reduce to the same expression.
-/
theorem exists_diagProd (j : Fin (n - 1)) :
    ∃ a : UpperQuot F n, Ideal.kerLiftAlg ((toUpper F n).comp (flagMinorMap F n)) a =
      diagProd F n j.val (by omega) := by
  have hj := j.2
  rcases Nat.eq_zero_or_pos j.val with h0 | hpos
  · refine ⟨1, ?_⟩
    rw [map_one, diagProd_congr F n _ (by omega) h0, diagProd_zero]
  · obtain ⟨i, hi⟩ : ∃ i : ℕ, j.val = i + 1 := ⟨j.val - 1, by omega⟩
    refine ⟨Ideal.Quotient.mk _ (X ⟨⟨i, by omega⟩, ⟨colSet i ⟨i, by omega⟩, colSet_card i _ le_rfl⟩⟩), ?_⟩
    rw [Ideal.kerLiftAlg_mk, toUpper_flagMinorMap_X]
    simp only
    rw [flagMinor_uMat_colSet F (n := n) ⟨i, by omega⟩ ⟨i, by omega⟩ le_rfl,
      diagProd_congr F n _ (by omega) hi, diagProd_succ]
    rfl

/- English proof (translation)
Set `_` to `(Ideal.kerLiftAlg ((toUpper F n).comp (flagMinorMap F n))).toRingHom.toAlgebra`. Establish `hj` using `j.2`. Take `⟨a, ha⟩` from `exists_diagProd F n j`. Use `isAlgebraic_of_mul_eq (a := a) (b := Ideal.Quotient.mk _ (X ⟨j, ⟨colSet j.val c, colSet_card j.val c hc⟩⟩)) ?_ ?_` and prove the remaining obligations. Introduce `h0`.

Rewrite `ha` using `[h0, map_zero]`. Conclude with `diagProd_ne_zero F n j.val (by omega) ha.symm`. Express the relevant statement in the definitionally equal form `Ideal.kerLiftAlg _ a * _ = Ideal.kerLiftAlg _ _`. Rewrite using `[ha, Ideal.kerLiftAlg_mk, toUpper_flagMinorMap_X]`. Simplify using `only`.

Rewrite using `[flagMinor_uMat_colSet F j c hc, diagProd]`.
-/
theorem isAlgebraic_uMat (j : Fin (n - 1)) (c : Fin n) (hc : j.val ≤ c.val) :
    letI := (Ideal.kerLiftAlg ((toUpper F n).comp (flagMinorMap F n))).toRingHom.toAlgebra
    IsAlgebraic (UpperQuot F n) (uMat F n ⟨j.val, by omega⟩ c) := by
  let _ := (Ideal.kerLiftAlg ((toUpper F n).comp (flagMinorMap F n))).toRingHom.toAlgebra
  have hj := j.2
  obtain ⟨a, ha⟩ := exists_diagProd F n j
  refine isAlgebraic_of_mul_eq (a := a)
    (b := Ideal.Quotient.mk _ (X ⟨j, ⟨colSet j.val c, colSet_card j.val c hc⟩⟩)) ?_ ?_
  · intro h0
    rw [h0, map_zero] at ha
    exact diagProd_ne_zero F n j.val (by omega) ha.symm
  · change Ideal.kerLiftAlg _ a * _ = Ideal.kerLiftAlg _ _
    rw [ha, Ideal.kerLiftAlg_mk, toUpper_flagMinorMap_X]
    simp only
    rw [flagMinor_uMat_colSet F j c hc, diagProd]

/- English proof (translation)
Use `set ι := Ideal.kerLiftAlg ((toUpper F n).comp (flagMinorMap F n))`. Set `_ : Algebra (UpperQuot F n) (MvPolynomial (UIdx n) F)` to `ι.toRingHom.toAlgebra`. Establish `: IsScalarTower F (UpperQuot F n) (MvPolynomial (UIdx n) F)` using `IsScalarTower.of_algebraMap_eq fun c => (ι.commutes c).symm`. Establish `: FaithfulSMul F (UpperQuot F n)` using `(faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap F (UpperQuot F n)).injective`. Establish `: FaithfulSMul (UpperQuot F n) (MvPolynomial (UIdx n) F)` using `(faithfulSMul_iff_algebraMap_injective _ _).2 (Ideal.kerLiftAlg_injective _)`.

Establish `hX : ∀ u : UIdx n, IsAlgebraic (UpperQuot F n) (X u : MvPolynomial (UIdx n) F)`. Introduce and unpack `(⟨⟨r, c⟩, h⟩ | r)`. Establish `e : (X (Sum.inl ⟨(r, c), h⟩) : MvPolynomial (UIdx n) F) = uMat F n r c`. Simplify using `[uMat, h]`. Rewrite using `[e]`.

Establish `hr : r.val < n - 1`. Use `c.2` as an intermediate fact. Simplify using `only [Fin.lt_def] at h`. Use linear arithmetic over natural numbers and integers. Conclude with `isAlgebraic_uMat F n ⟨r.val, hr⟩ c (le_of_lt h)`.

Establish `hr` using `r.2`. Rewrite using `[← uMat_diag F r.val (by omega)]`. Conclude with `isAlgebraic_uMat F n r _ le_rfl`. Establish `: Algebra.IsAlgebraic (UpperQuot F n) (MvPolynomial (UIdx n) F)`. Establish `hall : ∀ x : MvPolynomial (UIdx n) F, x ∈ Subalgebra.algebraicClosure (UpperQuot F n) (MvPolynomial (UIdx n) F)`.

Introduce `x`. Proceed by induction on `x using MvPolynomial.induction_on with`. Consider the case `C a`. Rewrite using `[← MvPolynomial.algebraMap_eq, IsScalarTower.algebraMap_apply F (UpperQuot F n)]`. Conclude with `isAlgebraic_algebraMap _`.

Consider the case `add p q hp hq => exact Subalgebra.add_mem _ hp hq`. Consider the case `mul_X p u hp => exact Subalgebra.mul_mem _ hp (hX u)`. Conclude with `⟨fun x => hall x⟩`. Establish `h` using `trdeg_add_eq F (UpperQuot F n) (A := MvPolynomial (UIdx n) F)`. Rewrite `h` using `[trdeg_eq_zero (R := UpperQuot F n) (A := MvPolynomial (UIdx n) F), add_zero, MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fintype, card_UIdx, Cardinal.lift_natCast]`.

Conclude with `h`.
-/
theorem trdeg_upperQuot :
    Algebra.trdeg F (UpperQuot F n) = ((flagDim n + (n - 1) : ℕ) : Cardinal) := by
  set ι := Ideal.kerLiftAlg ((toUpper F n).comp (flagMinorMap F n))
  let _ : Algebra (UpperQuot F n) (MvPolynomial (UIdx n) F) := ι.toRingHom.toAlgebra
  have : IsScalarTower F (UpperQuot F n) (MvPolynomial (UIdx n) F) :=
    IsScalarTower.of_algebraMap_eq fun c => (ι.commutes c).symm
  have : FaithfulSMul F (UpperQuot F n) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap F (UpperQuot F n)).injective
  have : FaithfulSMul (UpperQuot F n) (MvPolynomial (UIdx n) F) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (Ideal.kerLiftAlg_injective _)
  have hX : ∀ u : UIdx n, IsAlgebraic (UpperQuot F n) (X u : MvPolynomial (UIdx n) F) := by
    rintro (⟨⟨r, c⟩, h⟩ | r)
    · have e : (X (Sum.inl ⟨(r, c), h⟩) : MvPolynomial (UIdx n) F) = uMat F n r c := by
        simp [uMat, h]
      rw [e]
      have hr : r.val < n - 1 := by
        have := c.2
        simp only [Fin.lt_def] at h
        omega
      exact isAlgebraic_uMat F n ⟨r.val, hr⟩ c (le_of_lt h)
    · have hr := r.2
      rw [← uMat_diag F r.val (by omega)]
      exact isAlgebraic_uMat F n r _ le_rfl
  have : Algebra.IsAlgebraic (UpperQuot F n) (MvPolynomial (UIdx n) F) := by
    have hall : ∀ x : MvPolynomial (UIdx n) F,
        x ∈ Subalgebra.algebraicClosure (UpperQuot F n) (MvPolynomial (UIdx n) F) := by
      intro x
      induction x using MvPolynomial.induction_on with
      | C a =>
        rw [← MvPolynomial.algebraMap_eq, IsScalarTower.algebraMap_apply F (UpperQuot F n)]
        exact isAlgebraic_algebraMap _
      | add p q hp hq => exact Subalgebra.add_mem _ hp hq
      | mul_X p u hp => exact Subalgebra.mul_mem _ hp (hX u)
    exact ⟨fun x => hall x⟩
  have h := trdeg_add_eq F (UpperQuot F n) (A := MvPolynomial (UIdx n) F)
  rw [trdeg_eq_zero (R := UpperQuot F n) (A := MvPolynomial (UIdx n) F), add_zero, MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fintype, card_UIdx,
    Cardinal.lift_natCast] at h
  exact h

end Trdeg

section Grading

variable (F : Type) [Field F] (n : ℕ)

def plWeight : (Σ j, PluckerBlocks n n j) → (Fin (n - 1) → ℕ) := fun q => Pi.single q.1 1

def rowWeight : UIdx n → (Fin n → ℕ)
  | Sum.inl p => Pi.single p.1.1 1
  | Sum.inr r => Pi.single ⟨r.val, by omega⟩ 1

def rowsUpTo (j : Fin (n - 1)) : Fin n → ℕ := fun r => if r.val ≤ j.val then 1 else 0

def rowDeg : (Fin (n - 1) → ℕ) →+ (Fin n → ℕ) where
  toFun a := ∑ j, a j • rowsUpTo n j
  map_zero' := by simp
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[rowDeg, rowsUpTo, Finset.sum_apply]`.
-/
theorem rowDeg_apply (a : Fin (n - 1) → ℕ) (r : Fin n) :
    rowDeg n a r = ∑ j, if r.val ≤ j.val then a j else 0 := by
  simp [rowDeg, rowsUpTo, Finset.sum_apply]

/- English proof (translation)
Simplify using `only [rowDeg, AddMonoidHom.coe_mk, ZeroHom.coe_mk]`. Rewrite using `[Finset.sum_eq_single j]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[hb]`.

Simplify using the standard rewrite rules.
-/
theorem rowDeg_single (j : Fin (n - 1)) : rowDeg n (Pi.single j 1) = rowsUpTo n j := by
  simp only [rowDeg, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

/- English proof (translation)
Introduce `a b h`. Use function extensionality and compare the values at `j`. Establish `hj` using `j.2`. Establish `key : ∀ c : Fin (n - 1) → ℕ, rowDeg n c ⟨j.val, by omega⟩ = c j + rowDeg n c ⟨j.val + 1, by omega⟩`. Introduce `c`.

Rewrite using `[rowDeg_apply, rowDeg_apply]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `h1 : j = k`. Substitute `h1` using the available equality.

Simplify using the standard rewrite rules. Establish `h2 : j.val ≠ k.val` using `fun h => h1 (Fin.ext h)`. Distinguish the cases in `h3 : j.val ≤ k.val`. Rewrite using `[if_pos h3, if_neg h1, if_pos (by omega), zero_add]`. Rewrite using `[if_neg h3, if_neg h1, if_neg (by omega), add_zero]`.

Use `_ = c j + ∑ k, if j.val + 1 ≤ k.val then c k else 0 := by`. Rewrite using `[Finset.sum_add_distrib, Finset.sum_ite_eq]`. Simplify using the standard rewrite rules. Establish `h1` using `congrFun h ⟨j.val, by omega⟩`. Establish `h2` using `congrFun h ⟨j.val + 1, by omega⟩`.

Rewrite `h1` using `[key a, key b, h2]`. Use linear arithmetic over natural numbers and integers.
-/
theorem rowDeg_injective : Function.Injective (rowDeg n) := by
  intro a b h
  funext j
  have hj := j.2
  have key : ∀ c : Fin (n - 1) → ℕ,
      rowDeg n c ⟨j.val, by omega⟩ = c j + rowDeg n c ⟨j.val + 1, by omega⟩ := by
    intro c
    rw [rowDeg_apply, rowDeg_apply]
    calc (∑ k, if j.val ≤ k.val then c k else 0)
        = ∑ k, ((if j = k then c k else 0) + if j.val + 1 ≤ k.val then c k else 0) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          by_cases h1 : j = k
          · subst h1
            simp
          · have h2 : j.val ≠ k.val := fun h => h1 (Fin.ext h)
            by_cases h3 : j.val ≤ k.val
            · rw [if_pos h3, if_neg h1, if_pos (by omega), zero_add]
            · rw [if_neg h3, if_neg h1, if_neg (by omega), add_zero]
      _ = c j + ∑ k, if j.val + 1 ≤ k.val then c k else 0 := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq]
          simp
  have h1 := congrFun h ⟨j.val, by omega⟩
  have h2 := congrFun h ⟨j.val + 1, by omega⟩
  rw [key a, key b, h2] at h1
  omega

/- English proof (translation)
Simplify using `only [uMat, Matrix.of_apply]`. Use `split_ifs with h h'`. Conclude with `isWeightedHomogeneous_X F (rowWeight n) _`. Establish `e : (Pi.single r 1 : Fin n → ℕ) = rowWeight n (Sum.inr ⟨r.val, by omega⟩)` using `rfl`. Rewrite using `[e]`.

Conclude with `isWeightedHomogeneous_X F (rowWeight n) _`. Conclude with `isWeightedHomogeneous_zero F (rowWeight n) _`.
-/
theorem uMat_isWeightedHomogeneous (r c : Fin n) :
    IsWeightedHomogeneous (rowWeight n) (uMat F n r c) (Pi.single r 1) := by
  simp only [uMat, Matrix.of_apply]
  split_ifs with h h'
  · exact isWeightedHomogeneous_X F (rowWeight n) _
  · have e : (Pi.single r 1 : Fin n → ℕ) = rowWeight n (Sum.inr ⟨r.val, by omega⟩) := rfl
    rw [e]
    exact isWeightedHomogeneous_X F (rowWeight n) _
  · exact isWeightedHomogeneous_zero F (rowWeight n) _

/- English proof (translation)
Establish `hj` using `j.2`. Use function extensionality and compare the values at `r`. Simplify using `only [Finset.sum_apply, Pi.single_apply, rowsUpTo]`. Use `split_ifs with hr`. Rewrite using `[Finset.sum_eq_single ⟨r.val, by omega⟩]`.

Simplify using the standard rewrite rules. Introduce `b _ hb`. Rewrite using `[if_neg]`. Introduce `h`. Apply `hb` to reduce the goal to its premises.

Use `ext`. Simplify using `only [Fin.ext_iff, Fin.val_castLE] at h`. Simplify using `[h]`. Simplify using the standard rewrite rules. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `i _`. Rewrite using `[if_neg]`. Introduce `h`. Simplify using `only [Fin.ext_iff, Fin.val_castLE] at h`. Use `i.2` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem sum_single_castLE (j : Fin (n - 1)) :
    ∑ i : Fin (j.val + 1), (Pi.single (Fin.castLE (by have := j.2; omega) i : Fin n) 1 : Fin n → ℕ) =
      rowsUpTo n j := by
  have hj := j.2
  funext r
  simp only [Finset.sum_apply, Pi.single_apply, rowsUpTo]
  split_ifs with hr
  · rw [Finset.sum_eq_single ⟨r.val, by omega⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro h
      apply hb
      ext
      simp only [Fin.ext_iff, Fin.val_castLE] at h
      simp [h]
    · simp
  · apply Finset.sum_eq_zero
    intro i _
    rw [if_neg]
    intro h
    simp only [Fin.ext_iff, Fin.val_castLE] at h
    have := i.2
    omega

/- English proof (translation)
Rewrite using `[← sum_single_castLE n j]`. Simplify using `only [flagMinor]`. Rewrite using `[Matrix.det_apply]`. Apply `IsWeightedHomogeneous.sum` to reduce the goal to its premises. Introduce `σ _`.

Establish `hp : IsWeightedHomogeneous (rowWeight n) (∏ i, (uMat F n).submatrix (Fin.castLE (by have` using `j.2; omega)) (S.1.orderEmbOfFin S.2) (σ i) i) (∑ i : Fin (j.val + 1), (Pi.single (Fin.castLE (by have := j.2; omega) i : Fin n) 1 : Fin n → ℕ)) := by`. Rewrite using `[← Equiv.sum_comp σ]`. Apply `IsWeightedHomogeneous.prod` to reduce the goal to its premises. Introduce `i _`. Conclude with `uMat_isWeightedHomogeneous F n _ _`.

Break down `Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h` into its components or cases. Rewrite using `[h, one_smul]`. Conclude with `hp`. Rewrite using `[h, Units.neg_smul, one_smul]`. Conclude with `hp.neg`.
-/
theorem flagMinor_uMat_isWeightedHomogeneous (j : Fin (n - 1)) (S : PluckerBlocks n n j) :
    IsWeightedHomogeneous (rowWeight n) (flagMinor (uMat F n) j S) (rowsUpTo n j) := by
  rw [← sum_single_castLE n j]
  simp only [flagMinor]
  rw [Matrix.det_apply]
  apply IsWeightedHomogeneous.sum
  intro σ _
  have hp : IsWeightedHomogeneous (rowWeight n)
      (∏ i, (uMat F n).submatrix (Fin.castLE (by have := j.2; omega)) (S.1.orderEmbOfFin S.2) (σ i) i)
      (∑ i : Fin (j.val + 1), (Pi.single (Fin.castLE (by have := j.2; omega) i : Fin n) 1 : Fin n → ℕ)) := by
    rw [← Equiv.sum_comp σ]
    apply IsWeightedHomogeneous.prod
    intro i _
    exact uMat_isWeightedHomogeneous F n _ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h, one_smul]
    exact hp
  · rw [h, Units.neg_smul, one_smul]
    exact hp.neg

abbrev upperMap : MRingOver F (PluckerBlocks n n) →ₐ[F] MvPolynomial (UIdx n) F := (toUpper F n).comp (flagMinorMap F n)

/- English proof (translation)
Rewrite using `[f.as_sum, map_sum]`. Apply `IsWeightedHomogeneous.sum` to reduce the goal to its premises. Introduce `m hm`. Establish `ha : a = Finsupp.weight (plWeight n) m` using `(hf (mem_support_iff.1 hm)).symm`. Establish `hC : ∀ c : F, upperMap F n (C c) = C c`.

Introduce `c`. Rewrite using `[← MvPolynomial.algebraMap_eq]`. Conclude with `(upperMap F n).commutes c`. Rewrite using `[monomial_eq, map_mul, hC, map_finsuppProd]`. Apply `IsWeightedHomogeneous.C_mul` to reduce the goal to its premises.

Rewrite using `[ha, Finsupp.weight_apply, Finsupp.sum, map_sum]`. Apply `IsWeightedHomogeneous.prod` to reduce the goal to its premises. Introduce `p _`. Use `show IsWeightedHomogeneous (rowWeight n) (upperMap F n (X p ^ m p)) (rowDeg n (m p • plWeight n p))`. Rewrite using `[map_pow, map_nsmul]`.

Apply `IsWeightedHomogeneous.pow` to reduce the goal to its premises. Rewrite using `[toUpper_flagMinorMap_X, plWeight, rowDeg_single]`. Conclude with `flagMinor_uMat_isWeightedHomogeneous F n _ _`.
-/
theorem upperMap_isWeightedHomogeneous (f : MRingOver F (PluckerBlocks n n)) (a : Fin (n - 1) → ℕ)
    (hf : IsWeightedHomogeneous (plWeight n) f a) :
    IsWeightedHomogeneous (rowWeight n) (upperMap F n f) (rowDeg n a) := by
  rw [f.as_sum, map_sum]
  apply IsWeightedHomogeneous.sum
  intro m hm
  have ha : a = Finsupp.weight (plWeight n) m := (hf (mem_support_iff.1 hm)).symm
  have hC : ∀ c : F, upperMap F n (C c) = C c := by
    intro c
    rw [← MvPolynomial.algebraMap_eq]
    exact (upperMap F n).commutes c
  rw [monomial_eq, map_mul, hC, map_finsuppProd]
  apply IsWeightedHomogeneous.C_mul
  rw [ha, Finsupp.weight_apply, Finsupp.sum, map_sum]
  apply IsWeightedHomogeneous.prod
  intro p _
  show IsWeightedHomogeneous (rowWeight n) (upperMap F n (X p ^ m p)) (rowDeg n (m p • plWeight n p))
  rw [map_pow, map_nsmul]
  apply IsWeightedHomogeneous.pow
  rw [toUpper_flagMinorMap_X, plWeight, rowDeg_single]
  exact flagMinor_uMat_isWeightedHomogeneous F n _ _

/- English proof (translation)
Use `conv_lhs => rw [← sum_weightedHomogeneousComponent (plWeight n) f, finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]`. Rewrite using `[map_sum, map_sum]`. Distinguish the cases in `ha : weightedHomogeneousComponent (plWeight n) a f = 0`. Rewrite using `[ha, map_zero]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `b _`. Distinguish the cases in `hab : b = a`. Substitute `hab` using the available equality. Rewrite using `[ha, map_zero, map_zero]`. Conclude with `(upperMap_isWeightedHomogeneous F n _ b (weightedHomogeneousComponent_isWeightedHomogeneous b f)).weightedHomogeneousComponent_ne _ (fun h => hab (rowDeg_injective n h).symm)`.

Rewrite using `[Finset.sum_eq_single a]`. Conclude with `(upperMap_isWeightedHomogeneous F n _ a (weightedHomogeneousComponent_isWeightedHomogeneous a f)).weightedHomogeneousComponent_same`. Introduce `b _ hb`. Conclude with `(upperMap_isWeightedHomogeneous F n _ b (weightedHomogeneousComponent_isWeightedHomogeneous b f)).weightedHomogeneousComponent_ne _ (fun hab => hb (rowDeg_injective n hab).symm)`. Introduce `h`.

Conclude with `absurd ((Set.Finite.mem_toFinset _).2 ha) h`.
-/
theorem upperMap_weightedHomogeneousComponent (f : MRingOver F (PluckerBlocks n n)) (a : Fin (n - 1) → ℕ) :
    weightedHomogeneousComponent (rowWeight n) (rowDeg n a) (upperMap F n f) =
      upperMap F n (weightedHomogeneousComponent (plWeight n) a f) := by
  classical
  conv_lhs => rw [← sum_weightedHomogeneousComponent (plWeight n) f,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
  rw [map_sum, map_sum]
  by_cases ha : weightedHomogeneousComponent (plWeight n) a f = 0
  · rw [ha, map_zero]
    apply Finset.sum_eq_zero
    intro b _
    by_cases hab : b = a
    · subst hab
      rw [ha, map_zero, map_zero]
    · exact (upperMap_isWeightedHomogeneous F n _ b
        (weightedHomogeneousComponent_isWeightedHomogeneous b f)).weightedHomogeneousComponent_ne _
          (fun h => hab (rowDeg_injective n h).symm)
  · rw [Finset.sum_eq_single a]
    · exact (upperMap_isWeightedHomogeneous F n _ a
        (weightedHomogeneousComponent_isWeightedHomogeneous a f)).weightedHomogeneousComponent_same
    · intro b _ hb
      exact (upperMap_isWeightedHomogeneous F n _ b
        (weightedHomogeneousComponent_isWeightedHomogeneous b f)).weightedHomogeneousComponent_ne _
          (fun hab => hb (rowDeg_injective n hab).symm)
    · intro h
      exact absurd ((Set.Finite.mem_toFinset _).2 ha) h

/- English proof (translation)
Introduce `m hm k`. Establish `ha : Finsupp.weight (plWeight n) m = a` using `hf (mem_support_iff.1 hm)`. Rewrite using `[← ha, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]`. Rewrite using `[Finset.sum_eq_single k]`. Simplify using `[plWeight]`.

Introduce `b _ hb`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `i _`. Simplify using `[plWeight, Ne.symm hb]`. Simplify using the standard rewrite rules.
-/
theorem isMultiHomog_of_isWeightedHomogeneous (f : MRingOver F (PluckerBlocks n n)) (a : Fin (n - 1) → ℕ)
    (hf : IsWeightedHomogeneous (plWeight n) f a) : IsMultiHomog f a := by
  intro m hm k
  have ha : Finsupp.weight (plWeight n) m = a := hf (mem_support_iff.1 hm)
  rw [← ha, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
    Fintype.sum_sigma]
  rw [Finset.sum_eq_single k]
  · simp [plWeight]
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro i _
    simp [plWeight, Ne.symm hb]
  · simp

/- English proof (translation)
Use `⟨{f | f ∈ upperKer F n ∧ ∃ a, IsWeightedHomogeneous (plWeight n) f a}, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `f ⟨_, a, ha⟩`. Conclude with `⟨a, isMultiHomog_of_isWeightedHomogeneous F n f a ha⟩`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `f hf`.

Rewrite using `[← sum_weightedHomogeneousComponent (plWeight n) f, finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]`. Use `Ideal.sum_mem _ fun a _ => Ideal.subset_span ⟨?_, a, weightedHomogeneousComponent_isWeightedHomogeneous a f⟩` and prove the remaining obligations. Rewrite using `[RingHom.mem_ker, ← upperMap_weightedHomogeneousComponent]`. Rewrite `hf` using `[RingHom.mem_ker]`. Rewrite using `[hf, map_zero]`.

Conclude with `Ideal.span_le.2 fun f hf => hf.1`.
-/
theorem upperKer_isMultiHomogIdeal : IsMultiHomogIdeal (upperKer F n) := by
  classical
  refine ⟨{f | f ∈ upperKer F n ∧ ∃ a, IsWeightedHomogeneous (plWeight n) f a}, ?_, ?_⟩
  · rintro f ⟨_, a, ha⟩
    exact ⟨a, isMultiHomog_of_isWeightedHomogeneous F n f a ha⟩
  · apply le_antisymm
    · intro f hf
      rw [← sum_weightedHomogeneousComponent (plWeight n) f,
        finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
      refine Ideal.sum_mem _ fun a _ => Ideal.subset_span ⟨?_, a,
        weightedHomogeneousComponent_isWeightedHomogeneous a f⟩
      rw [RingHom.mem_ker, ← upperMap_weightedHomogeneousComponent]
      rw [RingHom.mem_ker] at hf
      rw [hf, map_zero]
    · exact Ideal.span_le.2 fun f hf => hf.1

end Grading

/- English proof (translation)
Introduce `j`. Establish `hj` using `j.2`. Use `⟨⟨colSet j.val ⟨j.val, by omega⟩, colSet_card j.val _ le_rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.mem_ker, toUpper_flagMinorMap_X]`. Simplify using `only`.

Rewrite using `[flagMinor_uMat_colSet F j ⟨j.val, by omega⟩ le_rfl]`. Establish `e : (∏ k : Fin j.val, uMat F n ⟨k.val, by omega⟩ ⟨k.val, by omega⟩) * uMat F n ⟨j.val, by omega⟩ ⟨j.val, by omega⟩ = diagProd F n (j.val + 1) (by omega)` using `(diagProd_succ F n j.val (by omega)).symm`. Rewrite using `[e]`. Conclude with `diagProd_ne_zero F n _ _`.
-/
theorem upperKer_isRelevant (F : Type) [Field F] (n : ℕ) : IsRelevant (upperKer F n) := by
  intro j
  have hj := j.2
  refine ⟨⟨colSet j.val ⟨j.val, by omega⟩, colSet_card j.val _ le_rfl⟩, ?_⟩
  rw [RingHom.mem_ker, toUpper_flagMinorMap_X]
  simp only
  rw [flagMinor_uMat_colSet F j ⟨j.val, by omega⟩ le_rfl]
  have e : (∏ k : Fin j.val, uMat F n ⟨k.val, by omega⟩ ⟨k.val, by omega⟩) * uMat F n ⟨j.val, by omega⟩ ⟨j.val, by omega⟩ =
      diagProd F n (j.val + 1) (by omega) := (diagProd_succ F n j.val (by omega)).symm
  rw [e]
  exact diagProd_ne_zero F n _ _

end FlagDim

open FlagDim in

/- English proof (translation)
Introduce `F _ n`. Establish `hker : flagIdealOver F n = upperKer F n` using `ker_flagMinorMap_eq F n`. Rewrite using `[hker]`. Use `⟨⟨inferInstance, upperKer_isMultiHomogIdeal F n, upperKer_isRelevant F n⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F, trdeg_upperQuot, Fintype.card_fin, Cardinal.toENat_nat]`.

Both sides reduce to the same expression.
-/
theorem FlagDim.proof : FlagDim.Statement := by
  intro F _ n
  have hker : flagIdealOver F n = upperKer F n := ker_flagMinorMap_eq F n
  rw [hker]
  refine ⟨⟨inferInstance, upperKer_isMultiHomogIdeal F n, upperKer_isRelevant F n⟩, ?_⟩
  rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F, trdeg_upperQuot, Fintype.card_fin,
    Cardinal.toENat_nat]
  rfl

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
