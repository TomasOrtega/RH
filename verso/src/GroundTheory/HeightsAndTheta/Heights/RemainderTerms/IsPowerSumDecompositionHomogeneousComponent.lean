import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.IsFlagIntegralOne
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PHomogeneousComponentMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

def rootRingToReal (f N j k : ℕ) (h : N = j + k) : RootRing f N →+* IndefiniteRowSideFullHecke.RestTerms.Roots f j k :=
  (rename (R := ℝ) (Prod.map id (finCongr h))).toRingHom.comp (MvPolynomial.map (algebraMap ℚ ℝ))

/- English proof (translation)
Apply the tactic sequence `simp only [rootRingToReal, RingHom.comp_apply, map_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X] <;> rfl`.
-/
@[simp] theorem rootRingToReal_X (f N j k : ℕ) (h : N = j + k) (v : Fin f × Fin N) :
    rootRingToReal f N j k h (X v) = X (v.1, finCongr h v.2) := by
  simp only [rootRingToReal, RingHom.comp_apply, map_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    rename_X] <;> rfl

/- English proof (translation)
Simplify using `[rootRingToReal]`.
-/
@[simp] theorem rootRingToReal_C (f N j k : ℕ) (h : N = j + k) (q : ℚ) :
    rootRingToReal f N j k h (C q) = C (q : ℝ) := by
  simp [rootRingToReal]

/- English proof (translation)
Rewrite using `[rootRingToReal, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, IsHomogeneous.rename_isHomogeneous_iff (Function.Injective.prodMap Function.injective_id (finCongr h).injective)]`. Prove the components needed by the constructor for the conclusion. Introduce `hP d hd`. Apply `hP` to reduce the goal to its premises. Rewrite using `[coeff_map]`.

Conclude with `(map_ne_zero_iff _ (algebraMap ℚ ℝ).injective).mpr hd`. Introduce `hP`. Conclude with `hP.map _`.
-/
theorem rootRingToReal_isHomogeneous_iff (f N j k : ℕ) (h : N = j + k) (P : RootRing f N) (n : ℕ) :
    (rootRingToReal f N j k h P).IsHomogeneous n ↔ P.IsHomogeneous n := by
  rw [rootRingToReal, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    IsHomogeneous.rename_isHomogeneous_iff
      (Function.Injective.prodMap Function.injective_id (finCongr h).injective)]
  constructor
  · intro hP d hd
    apply hP
    rw [coeff_map]
    exact (map_ne_zero_iff _ (algebraMap ℚ ℝ).injective).mpr hd
  · intro hP
    exact hP.map _

/- English proof (translation)
Simplify using `[vandermondeOf, map_prod, map_sub]`.
-/
theorem map_vandermondeOf {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {m : ℕ}
    (v : Fin m → R) : φ (vandermondeOf v) = vandermondeOf (fun i => φ (v i)) := by
  simp [vandermondeOf, map_prod, map_sub]

/- English proof (translation)
Establish `hM : (Matrix.of fun a b : Fin m => v a ^ (m - 1 - (b : ℕ))) = (Matrix.vandermonde v).submatrix id Fin.revPerm`. Use extensionality with `a b`. Simplify using `only [Matrix.of_apply, Matrix.submatrix_apply, id, Matrix.vandermonde_apply, Fin.revPerm_apply, Fin.val_rev]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.

Establish `hW : Matrix.vandermonde (fun i => v (Fin.revPerm i)) = (Matrix.vandermonde v).submatrix Fin.revPerm id`. Use extensionality with `a b`. Simplify using `[Matrix.vandermonde_apply]`. Rewrite using `[GroundTheory.Heights₂.Heights.vandermonde, hM, Matrix.det_permute', ← Matrix.det_permute, ← hW, Matrix.det_vandermonde]`. Establish `key : ∀ g : Fin m → Fin m → R, ∏ i, ∏ l ∈ Ioi i, g i l = ∏ i, ∏ l, if i < l then g i l else 1`.

Introduce `g`. Use `prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_filter]`. Use `congr 1`. Use extensionality with `l`.

Simplify using the standard rewrite rules. Rewrite using `[vandermondeOf, key, key]`. Use `conv_rhs => rw [Finset.prod_comm]`. Use `Fintype.prod_equiv Fin.revPerm _ _ (fun i => ?_)` and prove the remaining obligations. Use `Fintype.prod_equiv Fin.revPerm _ _ (fun l => ?_)` and prove the remaining obligations.

Simplify using `[Fin.revPerm_apply, Fin.rev_lt_rev]`.
-/
theorem vandermondeOf_eq_vandermonde {R : Type*} [CommRing R] {m : ℕ} (v : Fin m → R) :
    vandermondeOf v = GroundTheory.Heights₂.Heights.vandermonde v := by
  have hM : (Matrix.of fun a b : Fin m => v a ^ (m - 1 - (b : ℕ))) =
      (Matrix.vandermonde v).submatrix id Fin.revPerm := by
    ext a b
    simp only [Matrix.of_apply, Matrix.submatrix_apply, id, Matrix.vandermonde_apply,
      Fin.revPerm_apply, Fin.val_rev]
    congr 1
    omega
  have hW : Matrix.vandermonde (fun i => v (Fin.revPerm i)) =
      (Matrix.vandermonde v).submatrix Fin.revPerm id := by
    ext a b
    simp [Matrix.vandermonde_apply]
  rw [GroundTheory.Heights₂.Heights.vandermonde, hM, Matrix.det_permute', ← Matrix.det_permute, ← hW,
    Matrix.det_vandermonde]
  have key : ∀ g : Fin m → Fin m → R,
      ∏ i, ∏ l ∈ Ioi i, g i l = ∏ i, ∏ l, if i < l then g i l else 1 := by
    intro g
    refine prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_filter]
    congr 1
    ext l
    simp
  rw [vandermondeOf, key, key]
  conv_rhs => rw [Finset.prod_comm]
  refine Fintype.prod_equiv Fin.revPerm _ _ (fun i => ?_)
  refine Fintype.prod_equiv Fin.revPerm _ _ (fun l => ?_)
  simp [Fin.revPerm_apply, Fin.rev_lt_rev]

/- English proof (translation)
Substitute `h` using the available equality. Simplify using `[blockPowerSum, IndefiniteRowSideFullHecke.RestTerms.psumAt]`.
-/
theorem rootRingToReal_blockPowerSum (f N j k : ℕ) (h : N = j + k) (m : ℕ) (τ : Fin f) :
    rootRingToReal f N j k h (blockPowerSum f N m τ) = IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ := by
  subst h
  simp [blockPowerSum, IndefiniteRowSideFullHecke.RestTerms.psumAt]

/- English proof (translation)
Simplify using `only [smallPowerSum, yRoot, SmallBlock.sign, yIndex, map_sum, map_pow, map_mul, rootRingToReal_C, rootRingToReal_X, IndefiniteRowSideFullHecke.RestTerms.smallPsum, if_true, Rat.cast_one, C_1, one_mul]`. Use `sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Both sides reduce to the same expression.
-/
theorem rootRingToReal_smallPowerSum_last (f r a m : ℕ) (τ : Fin f) :
    rootRingToReal f (r + a) a r (Nat.add_comm r a) (smallPowerSum f r a .last m τ) =
      IndefiniteRowSideFullHecke.RestTerms.smallPsum f a r true m τ := by
  simp only [smallPowerSum, yRoot, SmallBlock.sign, yIndex, map_sum, map_pow, map_mul,
    rootRingToReal_C, rootRingToReal_X, IndefiniteRowSideFullHecke.RestTerms.smallPsum, if_true, Rat.cast_one, C_1, one_mul]
  refine sum_congr rfl fun i _ => ?_
  rfl

/- English proof (translation)
Simplify using `only [smallPowerSum, yRoot, SmallBlock.sign, yIndex, map_sum, map_pow, map_mul, rootRingToReal_C, rootRingToReal_X, IndefiniteRowSideFullHecke.RestTerms.smallPsum, Bool.false_eq_true, if_false, Rat.cast_neg, Rat.cast_one, C_neg, C_1, neg_one_mul, map_neg]`. Use `sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Both sides reduce to the same expression.
-/
theorem rootRingToReal_smallPowerSum_first (f r a m : ℕ) (τ : Fin f) :
    rootRingToReal f (r + a) r a rfl (smallPowerSum f r a .first m τ) =
      IndefiniteRowSideFullHecke.RestTerms.smallPsum f r a false m τ := by
  simp only [smallPowerSum, yRoot, SmallBlock.sign, yIndex, map_sum, map_pow, map_mul,
    rootRingToReal_C, rootRingToReal_X, IndefiniteRowSideFullHecke.RestTerms.smallPsum, Bool.false_eq_true, if_false,
    Rat.cast_neg, Rat.cast_one, C_neg, C_1, neg_one_mul, map_neg]
  refine sum_congr rfl fun i _ => ?_
  rfl

/- English proof (translation)
Rewrite using `[IndefiniteRowSideFullHecke.RestTerms.muClass, smallBlockMu, map_sum]`. Use `sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[← rootRingToReal_smallPowerSum_last]`. Simplify using `[smallPowerSum]`.
-/
theorem rootRingToReal_smallBlockMu_last (f r a : ℕ) :
    rootRingToReal f (r + a) a r (Nat.add_comm r a) (smallBlockMu f r a .last) =
      IndefiniteRowSideFullHecke.RestTerms.muClass f a r true := by
  rw [IndefiniteRowSideFullHecke.RestTerms.muClass, smallBlockMu, map_sum]
  refine sum_congr rfl fun τ _ => ?_
  rw [← rootRingToReal_smallPowerSum_last]
  simp [smallPowerSum]

/- English proof (translation)
Rewrite using `[IndefiniteRowSideFullHecke.RestTerms.muClass, smallBlockMu, map_sum]`. Use `sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[← rootRingToReal_smallPowerSum_first]`. Simplify using `[smallPowerSum]`.
-/
theorem rootRingToReal_smallBlockMu_first (f r a : ℕ) :
    rootRingToReal f (r + a) r a rfl (smallBlockMu f r a .first) =
      IndefiniteRowSideFullHecke.RestTerms.muClass f r a false := by
  rw [IndefiniteRowSideFullHecke.RestTerms.muClass, smallBlockMu, map_sum]
  refine sum_congr rfl fun τ _ => ?_
  rw [← rootRingToReal_smallPowerSum_first]
  simp [smallPowerSum]

/- English proof (translation)
Simplify using `only [fibreClass, IndefiniteRowSideFullHecke.RestTerms.fibClass, if_true, map_prod, map_mul, map_vandermondeOf]`. Use `prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[vandermondeOf_eq_vandermonde, vandermondeOf_eq_vandermonde]`. Use `congr 2`. Use function extensionality and compare the values at `i`.

Apply the tactic sequence `simp only [yRoot, SmallBlock.sign, yIndex, map_mul, rootRingToReal_C, rootRingToReal_X, Rat.cast_one, C_1, one_mul] <;> rfl`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `simp only [zRoot, zIndex, rootRingToReal_X] <;> rfl`.
-/
theorem rootRingToReal_fibreClass_last (f r a : ℕ) :
    rootRingToReal f (r + a) a r (Nat.add_comm r a) (fibreClass f r a .last) =
      IndefiniteRowSideFullHecke.RestTerms.fibClass f a r true := by
  simp only [fibreClass, IndefiniteRowSideFullHecke.RestTerms.fibClass, if_true, map_prod, map_mul, map_vandermondeOf]
  refine prod_congr rfl fun τ _ => ?_
  rw [vandermondeOf_eq_vandermonde, vandermondeOf_eq_vandermonde]
  congr 2
  · funext i
    simp only [yRoot, SmallBlock.sign, yIndex, map_mul, rootRingToReal_C, rootRingToReal_X, Rat.cast_one,
      C_1, one_mul] <;> rfl
  · funext i
    simp only [zRoot, zIndex, rootRingToReal_X] <;> rfl

/- English proof (translation)
Simplify using `only [fibreClass, IndefiniteRowSideFullHecke.RestTerms.fibClass, Bool.false_eq_true, if_false, map_prod, map_mul, map_vandermondeOf]`. Use `prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[vandermondeOf_eq_vandermonde, vandermondeOf_eq_vandermonde]`. Use `congr 2`. Use function extensionality and compare the values at `i`.

Apply the tactic sequence `simp only [yRoot, SmallBlock.sign, yIndex, map_mul, rootRingToReal_C, rootRingToReal_X, Rat.cast_neg, Rat.cast_one, C_neg, C_1, neg_one_mul, map_neg] <;> rfl`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `simp only [zRoot, zIndex, rootRingToReal_X] <;> rfl`.
-/
theorem rootRingToReal_fibreClass_first (f r a : ℕ) :
    rootRingToReal f (r + a) r a rfl (fibreClass f r a .first) =
      IndefiniteRowSideFullHecke.RestTerms.fibClass f r a false := by
  simp only [fibreClass, IndefiniteRowSideFullHecke.RestTerms.fibClass, Bool.false_eq_true, if_false, map_prod, map_mul,
    map_vandermondeOf]
  refine prod_congr rfl fun τ _ => ?_
  rw [vandermondeOf_eq_vandermonde, vandermondeOf_eq_vandermonde]
  congr 2
  · funext i
    simp only [yRoot, SmallBlock.sign, yIndex, map_mul, rootRingToReal_C, rootRingToReal_X, Rat.cast_neg,
      Rat.cast_one, C_neg, C_1, neg_one_mul, map_neg] <;> rfl
  · funext i
    simp only [zRoot, zIndex, rootRingToReal_X] <;> rfl

/- English proof (translation)
Rewrite using `[restPolynomial, IndefiniteRowSideFullHecke.RestTerms.restPoly, map_mul, map_pow, rootRingToReal_smallBlockMu_last, rootRingToReal_fibreClass_last, IndefiniteRowSideFullHecke.RestTerms.nDim, show f * a * r = f * (r * a) by ring]`.
-/
theorem rootRingToReal_restPolynomial_last (f r a : ℕ) :
    rootRingToReal f (r + a) a r (Nat.add_comm r a) (restPolynomial f r a .last) =
      IndefiniteRowSideFullHecke.RestTerms.restPoly f a r true := by
  rw [restPolynomial, IndefiniteRowSideFullHecke.RestTerms.restPoly, map_mul, map_pow, rootRingToReal_smallBlockMu_last,
    rootRingToReal_fibreClass_last, IndefiniteRowSideFullHecke.RestTerms.nDim, show f * a * r = f * (r * a) by ring]

/- English proof (translation)
Rewrite using `[restPolynomial, IndefiniteRowSideFullHecke.RestTerms.restPoly, map_mul, map_pow, rootRingToReal_smallBlockMu_first, rootRingToReal_fibreClass_first, IndefiniteRowSideFullHecke.RestTerms.nDim, Nat.mul_assoc]`.
-/
theorem rootRingToReal_restPolynomial_first (f r a : ℕ) :
    rootRingToReal f (r + a) r a rfl (restPolynomial f r a .first) =
      IndefiniteRowSideFullHecke.RestTerms.restPoly f r a false := by
  rw [restPolynomial, IndefiniteRowSideFullHecke.RestTerms.restPoly, map_mul, map_pow, rootRingToReal_smallBlockMu_first,
    rootRingToReal_fibreClass_first, IndefiniteRowSideFullHecke.RestTerms.nDim, Nat.mul_assoc]

/- English proof (translation)
Rewrite using `[IndefiniteRowSideFullHecke.RestTerms.degPoly, map_mul, map_pow, rootRingToReal_smallBlockMu_last, rootRingToReal_fibreClass_last, IndefiniteRowSideFullHecke.RestTerms.nDim, show f * a * r = f * (r * a) by ring]`.
-/
theorem rootRingToReal_degreePolynomial_last (f r a : ℕ) :
    rootRingToReal f (r + a) a r (Nat.add_comm r a)
        (smallBlockMu f r a .last ^ (f * (r * a)) * fibreClass f r a .last) =
      IndefiniteRowSideFullHecke.RestTerms.degPoly f a r true := by
  rw [IndefiniteRowSideFullHecke.RestTerms.degPoly, map_mul, map_pow, rootRingToReal_smallBlockMu_last,
    rootRingToReal_fibreClass_last, IndefiniteRowSideFullHecke.RestTerms.nDim, show f * a * r = f * (r * a) by ring]

/- English proof (translation)
Rewrite using `[IndefiniteRowSideFullHecke.RestTerms.degPoly, map_mul, map_pow, rootRingToReal_smallBlockMu_first, rootRingToReal_fibreClass_first, IndefiniteRowSideFullHecke.RestTerms.nDim, Nat.mul_assoc]`.
-/
theorem rootRingToReal_degreePolynomial_first (f r a : ℕ) :
    rootRingToReal f (r + a) r a rfl
        (smallBlockMu f r a .first ^ (f * (r * a)) * fibreClass f r a .first) =
      IndefiniteRowSideFullHecke.RestTerms.degPoly f r a false := by
  rw [IndefiniteRowSideFullHecke.RestTerms.degPoly, map_mul, map_pow, rootRingToReal_smallBlockMu_first,
    rootRingToReal_fibreClass_first, IndefiniteRowSideFullHecke.RestTerms.nDim, Nat.mul_assoc]

/- English proof (translation)
The claim follows from `IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow _ _`.
-/
theorem blockPowerSum_isHomogeneous (f N m : ℕ) (τ : Fin f) :
    (blockPowerSum f N m τ).IsHomogeneous m :=
  IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow _ _

/- English proof (translation)
Use `⟨?_, fun m τ => homogeneousComponent_isHomogeneous _ _⟩` and prove the remaining obligations. Establish `hle : ∀ m, m ≤ N → ∀ τ : Fin f, m ≤ topDegree f N + 1`. Introduce `m hm τ`. Establish `hf : 0 < f` using `τ.pos`. Establish `h1 : N - 1 ≤ N * (N - 1) / 2`.

Rewrite using `[Nat.le_div_iff_mul_le (by norm_num)]`. Break down `N with _ | n` into its components or cases. Simplify using the standard rewrite rules. Simplify using `only [Nat.add_sub_cancel]`. Break down `n with _ | n` into its components or cases.

Simplify using the standard rewrite rules. Use the polynomial consequences of the given equalities and inequalities. Establish `h2 : N * (N - 1) / 2 ≤ topDegree f N` using `Nat.le_mul_of_pos_left _ hf`. Use linear arithmetic over natural numbers and integers. Unfold `IsPowerSumDecomposition at hQ ⊢`.

Establish `hcomp : homogeneousComponent (topDegree f N + 1) F = F`. Rewrite using `[homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 hF), if_pos rfl]`. Use `conv_lhs => rw [← hcomp, hQ]`. Simplify using `only [map_sum]`. Use `sum_congr rfl fun m hm => sum_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Rewrite using `[HomogeneousComponentMul.proof _ _ _ _ _ _ (blockPowerSum_isHomogeneous f N m τ), if_pos (hle m (Finset.mem_Icc.1 hm).2 τ)]`.
-/
theorem isPowerSumDecomposition_homogeneousComponent (f N : ℕ) (F : RootRing f N)
    (Q : ℕ → Fin f → RootRing f N) (hF : F.IsHomogeneous (topDegree f N + 1))
    (hQ : IsPowerSumDecomposition f N F Q) :
    IsPowerSumDecomposition f N F
        (fun m τ => homogeneousComponent (topDegree f N + 1 - m) (Q m τ)) ∧
      ∀ m τ, (homogeneousComponent (topDegree f N + 1 - m) (Q m τ)).IsHomogeneous
        (topDegree f N + 1 - m) := by
  refine ⟨?_, fun m τ => homogeneousComponent_isHomogeneous _ _⟩
  have hle : ∀ m, m ≤ N → ∀ τ : Fin f, m ≤ topDegree f N + 1 := by
    intro m hm τ
    have hf : 0 < f := τ.pos
    have h1 : N - 1 ≤ N * (N - 1) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      rcases N with _ | n
      · simp
      · simp only [Nat.add_sub_cancel]
        rcases n with _ | n
        · simp
        · nlinarith
    have h2 : N * (N - 1) / 2 ≤ topDegree f N := Nat.le_mul_of_pos_left _ hf
    omega
  unfold IsPowerSumDecomposition at hQ ⊢
  have hcomp : homogeneousComponent (topDegree f N + 1) F = F := by
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 hF), if_pos rfl]
  conv_lhs => rw [← hcomp, hQ]
  simp only [map_sum]
  refine sum_congr rfl fun m hm => sum_congr rfl fun τ _ => ?_
  rw [HomogeneousComponentMul.proof _ _ _ _ _ _ (blockPowerSum_isHomogeneous f N m τ),
    if_pos (hle m (Finset.mem_Icc.1 hm).2 τ)]

end

end GroundTheory.Heights₂.Heights.RestTerms
