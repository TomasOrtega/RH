import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace HeightDropSingle

open scoped NumberField.AdeleRing

/- English proof (translation)
Simplify using `only [euclidNorm]`. Rewrite using `[Fin.sum_univ_succAbove _ p, hz]`. Simplify using the standard rewrite rules.
-/
theorem euclid_drop {F : Type*} [NormedField F] {n : ℕ} (p : Fin (n + 1)) (z : Fin (n + 1) → F)
    (hz : z p = 0) : euclidNorm z = euclidNorm (fun j => z (p.succAbove j)) := by
  simp only [euclidNorm]
  rw [Fin.sum_univ_succAbove _ p, hz]
  simp

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `(pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_` and prove the remaining obligations. Break down `Fin.eq_self_or_eq_succAbove p i with rfl | ⟨j, rfl⟩` into its components or cases. Rewrite using `[hz, norm_zero]`. Conclude with `norm_nonneg _`.

Conclude with `norm_le_pi_norm (fun j => z (p.succAbove j)) j`. Conclude with `(pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => norm_le_pi_norm z _`.
-/
theorem sup_drop {F : Type*} [NormedField F] {n : ℕ} (p : Fin (n + 1)) (z : Fin (n + 1) → F)
    (hz : z p = 0) : ‖z‖ = ‖fun j => z (p.succAbove j)‖ := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    rcases Fin.eq_self_or_eq_succAbove p i with rfl | ⟨j, rfl⟩
    · rw [hz, norm_zero]; exact norm_nonneg _
    · exact norm_le_pi_norm (fun j => z (p.succAbove j)) j
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => norm_le_pi_norm z _

/- English proof (translation)
Unfold `adelicNorm`. Use `congr 1`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[euclid_drop p (infComp w y) (by show (y p).1 w = 0; rw [hy]; rfl)]`. Both sides reduce to the same expression.

Use `finprod_congr fun v => ?_` and prove the remaining obligations. Rewrite using `[sup_drop p (finComp v y) (by show (y p).2 v = 0; rw [hy]; rfl)]`. Both sides reduce to the same expression.
-/
theorem adelicNorm_drop {K : Type*} [Field K] [NumberField K] {n : ℕ} (p : Fin (n + 1))
    (y : Fin (n + 1) → 𝔸[K]) (hy : y p = 0) :
    adelicNorm y = adelicNorm (fun j => y (p.succAbove j)) := by
  unfold adelicNorm
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [euclid_drop p (infComp w y) (by show (y p).1 w = 0; rw [hy]; rfl)]
    rfl
  · refine finprod_congr fun v => ?_
    rw [sup_drop p (finComp v y) (by show (y p).2 v = 0; rw [hy]; rfl)]
    rfl

/- English proof (translation)
Unfold `Reduction.height`. Establish `: ratVec (Pi.single i (1 : K)) ᵥ* (x : Matrix (Fin n) (Fin n) 𝔸[K]) = x.val i`. Use extensionality with `c`. Simplify using `[ratVec, vecMul, dotProduct, Pi.single_apply]`. Rewrite using `[this, hx, adelicNorm_single_one]`.
-/
theorem height_single {K : Type*} [Field K] [NumberField K] {n : ℕ} (x : GL (Fin n) 𝔸[K]) (i : Fin n)
    (hx : x.val i = Pi.single i 1) : Reduction.height x (Pi.single i (1 : K)) = 1 := by
  unfold Reduction.height
  have : ratVec (Pi.single i (1 : K)) ᵥ* (x : Matrix (Fin n) (Fin n) 𝔸[K]) = x.val i := by
    ext c
    simp [ratVec, vecMul, dotProduct, Pi.single_apply]
  rw [this, hx, adelicNorm_single_one]

end HeightDropSingle

/- English proof (translation)
Introduce `hD hG hK1 hK5e E _ _ _ m k hk hkm ι hι`. Take `⟨n, rfl⟩ : ∃ n, m = n + 1` from `⟨m - 1, by omega⟩`. Take `⟨C, hC⟩` from `hG E n (by omega)`. Establish `hDm` using `hD E (n + 1)`. Establish `hDk` using `hD E k`.

Establish `hDι : ∀ g, Dt (ι g) = Dt g` using `((hK5e E (n + 1) k hkm.le).2 ι hι).2.2.2.1`. Establish `hK` using `(hK1 E (n + 1) (by omega)).2.2.1`. Use `⟨C, fun g u => ⟨fun hu => ?_, fun hu => ?_⟩⟩` and prove the remaining obligations. Take `⟨x, hx⟩ : ∃ x, x = u * ι g` from `⟨_, rfl⟩`. Rewrite using `[← hx]`.

Establish `hDx : Dt x = Dt g` using `by rw [hx, hDm.2.1, hDm.2.2.2.2.1 0 u hu, hDι, one_mul]`. Establish `hrow : x.val (Fin.last n) = Pi.single (Fin.last n) 1`. Use extensionality with `c`. Rewrite using `[hx, Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (Fin.last n)]`. Rewrite using `[hu.2.1, one_mul, hι g]`.

Establish `hk' : ¬ ((Fin.last n : ℕ) < k ∧ (c : ℕ) < k)` using `by simp; omega`. Simplify using `only [embM, Matrix.of_apply, dif_neg hk', Matrix.one_apply, Pi.single_apply, eq_comm]`. Introduce `j _ hj`. Rewrite using `[hu.1 _ _ (lt_of_le_of_ne (Fin.le_last j) hj), zero_mul]`. Simplify using the standard rewrite rules.

Establish `hpos` using `hDk.1 g`. Use `(hK x (Pi.single (Fin.last n) 1) fun h => by simpa using congrFun h (Fin.last n)).trans (le_of_eq ?_)` and prove the remaining obligations. Unfold `ht`. Rewrite using `[HeightDropSingle.height_single x _ hrow, hDx, Real.rpow_neg hpos.le, one_div]`. Take `⟨x, hx⟩ : ∃ x, x = u * ι g` from `⟨_, rfl⟩`.

Rewrite using `[← hx]`. Establish `hDx : Dt x = Dt g` using `by rw [hx, hDm.2.1, hDm.2.2.2.2.1 (k + 1) u hu, hDι, one_mul]`. Use `set p : Fin (n + 1) := ⟨k, hkm⟩ with hp`. Establish `hcol : ∀ i, x.val i p = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) (Ad E)) i p`. Introduce `i`.

Rewrite using `[hx, Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single p]`. Rewrite using `[hι g]`. Establish `hk' : ¬ ((p : ℕ) < k ∧ (p : ℕ) < k)` using `by simp [p]`. Simplify using `only [embM, Matrix.of_apply, dif_neg hk', Matrix.one_apply_eq, mul_one]`. Conclude with `hu.2.2 i p (by simp [p])`.

Introduce `j _ hj`. Rewrite using `[hι g]`. Establish `hk' : ¬ ((j : ℕ) < k ∧ (p : ℕ) < k)` using `by simp [p]`. Simplify using `only [embM, Matrix.of_apply, dif_neg hk', Matrix.one_apply_ne hj, mul_zero]`. Simplify using the standard rewrite rules.

Use `set M' : Matrix (Fin n) (Fin n) (Ad E) := x.val.submatrix p.succAbove p.succAbove with hM'`. Establish `hdet : M'.det = x.val.det`. Rewrite using `[Matrix.det_succ_column x.val p, Finset.sum_eq_single p]`. Rewrite using `[hcol, Matrix.one_apply_eq, mul_one, Even.neg_one_pow ⟨(p : ℕ), rfl⟩, one_mul]`. Introduce `i _ hi`.

Rewrite using `[hcol, Matrix.one_apply_ne hi, mul_zero, zero_mul]`. Simplify using the standard rewrite rules. Establish `hunit : IsUnit M'.det`. Rewrite using `[hdet]`. Conclude with `(Matrix.GeneralLinearGroup.det x).isUnit`.

Set `g' : GA E n` to `M'.nonsingInvUnit hunit`. Establish `hDg' : Dt g' = Dt x`. Establish `: GeneralLinearGroup.det g' = GeneralLinearGroup.det x` using `Units.ext hdet`. Unfold `Dt`. Rewrite using `[this]`.

Take `⟨ξ', hξ'0, hξ'⟩` from `hC g'`. Set `ξ : Fin (n + 1) → E` to `p.insertNth 0 ξ'`. Establish `hξ0 : ξ ≠ 0`. Introduce `h`. Apply `hξ'0` to reduce the goal to its premises.

Use extensionality with `j`. Simplify `congrFun h (p.succAbove j)` using `[ξ]`. Establish `hht : Reduction.height x ξ = Reduction.height g' ξ'`. Unfold `Reduction.height`. Rewrite using `[HeightDropSingle.adelicNorm_drop p]`.

Use `congr 1`. Use extensionality with `c`. Simplify using `only [vecMul, dotProduct]`. Rewrite using `[Fin.sum_univ_succAbove _ p]`. Simplify using `[ξ, ratVec, g', M']`.

Both sides reduce to the same expression. Simplify using `only [vecMul, dotProduct]`. Rewrite using `[Fin.sum_univ_succAbove _ p]`. Simplify using `[ξ, ratVec, hcol, Matrix.one_apply_ne (Fin.succAbove_ne p _)]`. Establish `hpos` using `hDk.1 g`.

Use `(hK x ξ hξ0).trans ?_` and prove the remaining obligations. Unfold `ht at hξ' ⊢`. Rewrite using `[hht, hDx]`. Rewrite `hξ'` using `[hDg', hDx]`. Establish `h1 : Reduction.height g' ξ' ≤ C * Dt g ^ ((n : ℝ)⁻¹)` using `(div_le_iff₀ (Real.rpow_pos_of_pos hpos _)).1 hξ'`.

Rewrite using `[div_le_iff₀ (Real.rpow_pos_of_pos hpos _)]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, ← Real.rpow_add hpos]`. Use `congr 2`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem short_rows_embedding_of : D0 → MinkowskiBoundAlt → K1 → CornerEmbedding → ShortRowsEmbedding := by
  intro hD hG hK1 hK5e E _ _ _ m k hk hkm ι hι
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨C, hC⟩ := hG E n (by omega)
  have hDm := hD E (n + 1)
  have hDk := hD E k
  have hDι : ∀ g, Dt (ι g) = Dt g := ((hK5e E (n + 1) k hkm.le).2 ι hι).2.2.2.1
  have hK := (hK1 E (n + 1) (by omega)).2.2.1
  refine ⟨C, fun g u => ⟨fun hu => ?_, fun hu => ?_⟩⟩
  · obtain ⟨x, hx⟩ : ∃ x, x = u * ι g := ⟨_, rfl⟩
    rw [← hx]
    have hDx : Dt x = Dt g := by rw [hx, hDm.2.1, hDm.2.2.2.2.1 0 u hu, hDι, one_mul]
    have hrow : x.val (Fin.last n) = Pi.single (Fin.last n) 1 := by
      ext c
      rw [hx, Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (Fin.last n)]
      · rw [hu.2.1, one_mul, hι g]
        have hk' : ¬ ((Fin.last n : ℕ) < k ∧ (c : ℕ) < k) := by simp; omega
        simp only [embM, Matrix.of_apply, dif_neg hk', Matrix.one_apply, Pi.single_apply, eq_comm]
      · intro j _ hj
        rw [hu.1 _ _ (lt_of_le_of_ne (Fin.le_last j) hj), zero_mul]
      · simp
    have hpos := hDk.1 g
    refine (hK x (Pi.single (Fin.last n) 1) fun h => by simpa using congrFun h (Fin.last n)).trans (le_of_eq ?_)
    unfold ht
    rw [HeightDropSingle.height_single x _ hrow, hDx, Real.rpow_neg hpos.le, one_div]
  · obtain ⟨x, hx⟩ : ∃ x, x = u * ι g := ⟨_, rfl⟩
    rw [← hx]
    have hDx : Dt x = Dt g := by rw [hx, hDm.2.1, hDm.2.2.2.2.1 (k + 1) u hu, hDι, one_mul]
    set p : Fin (n + 1) := ⟨k, hkm⟩ with hp
    have hcol : ∀ i, x.val i p = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) (Ad E)) i p := by
      intro i
      rw [hx, Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single p]
      · rw [hι g]
        have hk' : ¬ ((p : ℕ) < k ∧ (p : ℕ) < k) := by simp [p]
        simp only [embM, Matrix.of_apply, dif_neg hk', Matrix.one_apply_eq, mul_one]
        exact hu.2.2 i p (by simp [p])
      · intro j _ hj
        rw [hι g]
        have hk' : ¬ ((j : ℕ) < k ∧ (p : ℕ) < k) := by simp [p]
        simp only [embM, Matrix.of_apply, dif_neg hk', Matrix.one_apply_ne hj, mul_zero]
      · simp
    set M' : Matrix (Fin n) (Fin n) (Ad E) := x.val.submatrix p.succAbove p.succAbove with hM'
    have hdet : M'.det = x.val.det := by
      rw [Matrix.det_succ_column x.val p, Finset.sum_eq_single p]
      · rw [hcol, Matrix.one_apply_eq, mul_one, Even.neg_one_pow ⟨(p : ℕ), rfl⟩, one_mul]
      · intro i _ hi
        rw [hcol, Matrix.one_apply_ne hi, mul_zero, zero_mul]
      · simp
    have hunit : IsUnit M'.det := by
      rw [hdet]; exact (Matrix.GeneralLinearGroup.det x).isUnit
    let g' : GA E n := M'.nonsingInvUnit hunit
    have hDg' : Dt g' = Dt x := by
      have : GeneralLinearGroup.det g' = GeneralLinearGroup.det x := Units.ext hdet
      unfold Dt; rw [this]
    obtain ⟨ξ', hξ'0, hξ'⟩ := hC g'
    let ξ : Fin (n + 1) → E := p.insertNth 0 ξ'
    have hξ0 : ξ ≠ 0 := by
      intro h; apply hξ'0; ext j
      simpa [ξ] using congrFun h (p.succAbove j)
    have hht : Reduction.height x ξ = Reduction.height g' ξ' := by
      unfold Reduction.height
      rw [HeightDropSingle.adelicNorm_drop p]
      · congr 1
        ext c
        simp only [vecMul, dotProduct]
        rw [Fin.sum_univ_succAbove _ p]
        simp [ξ, ratVec, g', M']
        rfl
      · simp only [vecMul, dotProduct]
        rw [Fin.sum_univ_succAbove _ p]
        simp [ξ, ratVec, hcol, Matrix.one_apply_ne (Fin.succAbove_ne p _)]
    have hpos := hDk.1 g
    refine (hK x ξ hξ0).trans ?_
    unfold ht at hξ' ⊢
    rw [hht, hDx]
    rw [hDg', hDx] at hξ'
    have h1 : Reduction.height g' ξ' ≤ C * Dt g ^ ((n : ℝ)⁻¹) :=
      (div_le_iff₀ (Real.rpow_pos_of_pos hpos _)).1 hξ'
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hpos _)]
    calc Reduction.height g' ξ' ≤ C * Dt g ^ ((n : ℝ)⁻¹) := h1
      _ = C * Dt g ^ ((((n + 1 : ℕ) : ℝ) - 1)⁻¹ - ((n + 1 : ℕ) : ℝ)⁻¹) * Dt g ^ (((n + 1 : ℕ) : ℝ)⁻¹) := by
        rw [mul_assoc, ← Real.rpow_add hpos]
        congr 2
        push_cast
        ring

end PositivityTheory.AdelicQuotientData

end
