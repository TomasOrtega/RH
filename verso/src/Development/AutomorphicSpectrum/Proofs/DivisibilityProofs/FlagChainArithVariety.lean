import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsChainFirst
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFlagArithVar
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Assembly
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.FlDeg

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open GroundTheory.Heights₂.Heights.LowerBoundFree.FlagRatioTrdeg GroundTheory.Heights₂.Heights.LowerBoundFree.FlagArithVar

/- English proof (translation)
Establish `hy` using `pivot_indep F Ψ n`. Set `δ : PivotIdxLe Ψ n → PivotIdxLe Ψ n` to `fun q => (q.1, ⟨q.2.1, ⟨Fin.castLE (Nat.sub_le n 1) q.2.1, by simp⟩⟩)`. Establish `hz` using `ratio_indep F hy δ (fun q => rfl)`. Set `incl : PivotIdx Ψ n → PivotIdxLe Ψ n` to `fun q => (q.1, ⟨q.2.1, ⟨q.2.2.1, q.2.2.2.le⟩⟩)`. Establish `hincl : Function.Injective incl`.

Introduce and unpack `⟨τ, a, b, hb⟩ ⟨τ', a', b', hb'⟩ h`. Simplify using `only [incl, Prod.mk.injEq, Sigma.mk.inj_iff] at h`. Take `⟨h0, h1, h2⟩` from `h`. Substitute `h0 h1` using the available equality. Simplify using `only [heq_eq_eq, Subtype.mk.injEq] at h2`.

Substitute `h2` using the available equality. Both sides reduce to the same expression. Establish `hrat : (fun q : PivotIdxLe Ψ n => if δ q = q then pivotMinor (genMatFr F Ψ n q.1) q.2.1 q.2.2.1 else pivotMinor (genMatFr F Ψ n q.1) q.2.1 q.2.2.1 / pivotMinor (genMatFr F Ψ n (δ q).1) (δ q).2.1 (δ q).2.2.1) ∘ incl = pivotRatio F Ψ n`. Use function extensionality and compare the values at `q`. Establish `hne : δ (incl q) ≠ incl q`.

Introduce `h`. Use `congrArg (fun r : PivotIdxLe Ψ n => ((r.2.2.1 : Fin n) : ℕ)) h` as an intermediate fact. Simplify using `only [δ, incl, Fin.val_castLE] at this`. Use `q.2.2.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Simplify using `only [Function.comp_apply, hne, if_false]`. Both sides reduce to the same expression. Conclude with `hrat ▸ hz.comp incl hincl`.
-/
theorem pivotRatio_algebraicIndependent (F : Type) [Field F] (Ψ : Type) (n : ℕ) :
    AlgebraicIndependent F (pivotRatio F Ψ n) := by
  classical
  have hy := pivot_indep F Ψ n
  let δ : PivotIdxLe Ψ n → PivotIdxLe Ψ n :=
    fun q => (q.1, ⟨q.2.1, ⟨Fin.castLE (Nat.sub_le n 1) q.2.1, by simp⟩⟩)
  have hz := ratio_indep F hy δ (fun q => rfl)
  let incl : PivotIdx Ψ n → PivotIdxLe Ψ n := fun q => (q.1, ⟨q.2.1, ⟨q.2.2.1, q.2.2.2.le⟩⟩)
  have hincl : Function.Injective incl := by
    rintro ⟨τ, a, b, hb⟩ ⟨τ', a', b', hb'⟩ h
    simp only [incl, Prod.mk.injEq, Sigma.mk.inj_iff] at h
    obtain ⟨h0, h1, h2⟩ := h
    subst h0 h1
    simp only [heq_eq_eq, Subtype.mk.injEq] at h2
    subst h2
    rfl
  have hrat : (fun q : PivotIdxLe Ψ n => if δ q = q then pivotMinor (genMatFr F Ψ n q.1) q.2.1 q.2.2.1 else
      pivotMinor (genMatFr F Ψ n q.1) q.2.1 q.2.2.1 / pivotMinor (genMatFr F Ψ n (δ q).1) (δ q).2.1 (δ q).2.2.1) ∘
        incl = pivotRatio F Ψ n := by
    funext q
    have hne : δ (incl q) ≠ incl q := by
      intro h
      have := congrArg (fun r : PivotIdxLe Ψ n => ((r.2.2.1 : Fin n) : ℕ)) h
      simp only [δ, incl, Fin.val_castLE] at this
      have := q.2.2.2
      omega
    simp only [Function.comp_apply, hne, if_false]
    rfl
  exact hrat ▸ hz.comp incl hincl

/- English proof (translation)
Establish `hj : (j : ℕ) + 1 ≤ m` using `by have := j.2; omega`. Establish `hent : ∀ (a : Fin (m - 1)) (b : Fin m), (a : ℕ) ≤ j → pivotMinor g a b / leadMinor g a ∈ A`. Introduce `a b haj`. Break down `lt_trichotomy (b : ℕ) a with h | h | h` into its components or cases. Rewrite using `[pivotMinor_eq_zero g a b h, zero_div]`.

Conclude with `A.zero_mem`. Establish `e : b = Fin.castLE (Nat.sub_le m 1) a` using `Fin.ext h`. Substitute `e` using the available equality. Use `show leadMinor g a / leadMinor g a ∈ A`. Rewrite using `[div_self (hL a)]`.

Conclude with `A.one_mem`. Conclude with `hA a b haj h`. Set `U : Matrix (Fin (j + 1)) (Fin (j + 1)) K` to `Matrix.of fun r s => pivotMinor g ⟨r, by have := r.2; have := j.2; omega⟩ (S.1.orderEmbOfFin S.2 s) / leadMinor g ⟨r, by have := r.2; have := j.2; omega⟩`. Establish `hP : (pivotMatrix g).submatrix (Fin.castLE hj) (S.1.orderEmbOfFin S.2) = Matrix.diagonal (fun r : Fin (j + 1) => leadMinor g ⟨r, by have` using `r.2; have := j.2; omega⟩) * U := by`. Use extensionality with `r s`.

Rewrite using `[Matrix.diagonal_mul]`. Simplify using `only [Matrix.submatrix_apply, pivotMatrix, Matrix.of_apply, U]`. Rewrite using `[dif_pos (by simp only [Fin.val_castLE]; have := r.2; have := j.2; omega)]`. Rewrite using `[mul_div_cancel₀ _ (hL _)]`. Both sides reduce to the same expression.

Establish `hdet : flagMinor (pivotMatrix g) j S = (∏ r : Fin (j + 1), leadMinor g ⟨r, by have` using `r.2; have := j.2; omega⟩) * U.det := by`. Unfold `flagMinor`. Rewrite using `[hP, Matrix.det_mul, Matrix.det_diagonal]`. Establish `hid` using `FlagPivotIdentity.proof K m g j S`. Rewrite `hid` using `[prod_Iic_fin, hdet]`.

Establish `hne : (∏ r : Fin (j + 1), leadMinor g ⟨r, by have` using `r.2; have := j.2; omega⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun r _ => hL _`. Establish `hU : flagMinor g j S / leadMinor g j = U.det`. Rewrite using `[div_eq_iff (hL j)]`. Apply `mul_right_cancel₀ hne` to reduce the goal to its premises. Take the linear combination `hid`.

Rewrite using `[hU, Matrix.det_apply]`. Use `A.sum_mem fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Units.smul_def]`. Conclude with `zsmul_mem (A.prod_mem fun r _ => hent _ _ (by have := r.2; simp only; omega)) _`.
-/
theorem flag_mem_of_le (F : Type) [Field F] {K : Type} [Field K] [Algebra F K] {m : ℕ}
    (g : Matrix (Fin m) (Fin m) K) (A : IntermediateField F K) (hL : ∀ a, leadMinor g a ≠ 0)
    (j : Fin (m - 1))
    (hA : ∀ (a : Fin (m - 1)) (b : Fin m), (a : ℕ) ≤ j → (a : ℕ) < b → pivotMinor g a b / leadMinor g a ∈ A)
    (S : PluckerBlocks m m j) : flagMinor g j S / leadMinor g j ∈ A := by
  have hj : (j : ℕ) + 1 ≤ m := by have := j.2; omega
  have hent : ∀ (a : Fin (m - 1)) (b : Fin m), (a : ℕ) ≤ j → pivotMinor g a b / leadMinor g a ∈ A := by
    intro a b haj
    rcases lt_trichotomy (b : ℕ) a with h | h | h
    · rw [pivotMinor_eq_zero g a b h, zero_div]
      exact A.zero_mem
    · have e : b = Fin.castLE (Nat.sub_le m 1) a := Fin.ext h
      subst e
      show leadMinor g a / leadMinor g a ∈ A
      rw [div_self (hL a)]
      exact A.one_mem
    · exact hA a b haj h
  let U : Matrix (Fin (j + 1)) (Fin (j + 1)) K := Matrix.of fun r s =>
    pivotMinor g ⟨r, by have := r.2; have := j.2; omega⟩ (S.1.orderEmbOfFin S.2 s) /
      leadMinor g ⟨r, by have := r.2; have := j.2; omega⟩
  have hP : (pivotMatrix g).submatrix (Fin.castLE hj) (S.1.orderEmbOfFin S.2) =
      Matrix.diagonal (fun r : Fin (j + 1) => leadMinor g ⟨r, by have := r.2; have := j.2; omega⟩) * U := by
    ext r s
    rw [Matrix.diagonal_mul]
    simp only [Matrix.submatrix_apply, pivotMatrix, Matrix.of_apply, U]
    rw [dif_pos (by simp only [Fin.val_castLE]; have := r.2; have := j.2; omega)]
    rw [mul_div_cancel₀ _ (hL _)]
    rfl
  have hdet : flagMinor (pivotMatrix g) j S =
      (∏ r : Fin (j + 1), leadMinor g ⟨r, by have := r.2; have := j.2; omega⟩) * U.det := by
    unfold flagMinor
    rw [hP, Matrix.det_mul, Matrix.det_diagonal]
  have hid := FlagPivotIdentity.proof K m g j S
  rw [prod_Iic_fin, hdet] at hid
  have hne : (∏ r : Fin (j + 1), leadMinor g ⟨r, by have := r.2; have := j.2; omega⟩) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun r _ => hL _
  have hU : flagMinor g j S / leadMinor g j = U.det := by
    rw [div_eq_iff (hL j)]
    apply mul_right_cancel₀ hne
    linear_combination hid
  rw [hU, Matrix.det_apply]
  refine A.sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (A.prod_mem fun r _ => hent _ _ (by have := r.2; simp only; omega)) _

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} {K : Type}

abbrev PivPos (j : K → FlBlock Ψ N) : Type := Σ k : K, {b : Fin N // ((j k).2 : ℕ) < b}

def pivPosIncl (j : K → FlBlock Ψ N) (x : PivPos j) : PivotIdx Ψ N := ((j x.1).1, ⟨(j x.1).2, x.2⟩)

/- English proof (translation)
Introduce and unpack `⟨k, b, hb⟩ ⟨k', b', hb'⟩ h`. Simplify using `only [pivPosIncl, Prod.mk.injEq, Sigma.mk.inj_iff] at h`. Take `⟨h0, h1, h2⟩` from `h`. Establish `hk : k = k'` using `hj (Prod.ext h0 h1)`. Substitute `hk` using the available equality.

Simplify using `only [heq_eq_eq, Subtype.mk.injEq] at h2`. Substitute `h2` using the available equality. Both sides reduce to the same expression.
-/
theorem pivPosIncl_injective {j : K → FlBlock Ψ N} (hj : Function.Injective j) :
    Function.Injective (pivPosIncl j) := by
  rintro ⟨k, b, hb⟩ ⟨k', b', hb'⟩ h
  simp only [pivPosIncl, Prod.mk.injEq, Sigma.mk.inj_iff] at h
  obtain ⟨h0, h1, h2⟩ := h
  have hk : k = k' := hj (Prod.ext h0 h1)
  subst hk
  simp only [heq_eq_eq, Subtype.mk.injEq] at h2
  subst h2
  rfl

/- English proof (translation)
Rewrite using `[Fintype.card_sigma, cellDim]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.card_subtype]`. Establish `: (Finset.univ.filter fun b : Fin N => ((j k).2 : ℕ) < b) = Finset.Ioi (Fin.castLE (Nat.sub_le N 1) (j k).2)`. Use extensionality with `b`.

Simplify using `[Fin.lt_def]`. Rewrite using `[this, Fin.card_Ioi]`. Simplify using the standard rewrite rules.
-/
theorem card_pivPos [Fintype K] (j : K → FlBlock Ψ N) : Fintype.card (PivPos j) = cellDim j := by
  rw [Fintype.card_sigma, cellDim]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.card_subtype]
  have : (Finset.univ.filter fun b : Fin N => ((j k).2 : ℕ) < b) =
      Finset.Ioi (Fin.castLE (Nat.sub_le N 1) (j k).2) := by
    ext b
    simp [Fin.lt_def]
  rw [this, Fin.card_Ioi]
  simp

/- English proof (translation)
Substitute `hI` using the available equality. Conclude with `pivotRatio_algebraicIndependent ℚ Ψ N`.
-/
theorem pivotRatio_algebraicIndependent_of_eq (Ψ : Type) (N : ℕ) (I : Algebra ℚ (ΩFl Ψ N))
    (hI : I = OreLocalization.instAlgebra) :
    @AlgebraicIndependent _ ℚ (ΩFl Ψ N) (pivotRatio ℚ Ψ N) _ _ I := by
  subst hI
  exact pivotRatio_algebraicIndependent ℚ Ψ N

/- English proof (translation)
The claim follows from `pivotRatio_algebraicIndependent_of_eq Ψ N _ (Subsingleton.elim _ _)`.
-/
theorem pivotRatio_rat_algebraicIndependent (Ψ : Type) (N : ℕ) :
    AlgebraicIndependent ℚ (pivotRatio ℚ Ψ N : PivotIdx Ψ N → ΩFl Ψ N) :=
  pivotRatio_algebraicIndependent_of_eq Ψ N _ (Subsingleton.elim _ _)

/- English proof (translation)
Set `e : PivPos j ≃ Fin (cellDim j)` to `Fintype.equivFinOfCardEq (card_pivPos j)`. Set `t : Fin (cellDim j) → ΩFl Ψ N` to `fun i => pivotRatio ℚ Ψ N (pivPosIncl j (e.symm i))`. Set `c : ∀ k, PIdx j k` to `fun k => leadIdx Ψ N (j k)`. Establish `hL : ∀ (τ : Ψ) (a : Fin (N - 1)), leadMinor (genMatFr ℚ Ψ N τ) a ≠ 0` using `fun τ a => GenLeadMinorNeZero.full ℚ Ψ N τ a`. Establish `hc : ∀ k, yPart j ⟨k, c k⟩ ≠ 0` using `fun k => by show yFl Ψ N ⟨j k, leadIdx Ψ N (j k)⟩ ≠ 0`.

Rewrite using `[yFl_lead]`. Conclude with `hL _ _`. Establish `hind : AlgebraicIndependent ℚ t`. Conclude with `(pivotRatio_rat_algebraicIndependent Ψ N).comp _ ((pivPosIncl_injective hj.inj).comp e.symm.injective)`. Establish `hmem : ∀ i, t i ∈ IntermediateField.adjoin ℚ (coneRatios (yPart j) c)`.

Introduce `i`. Use `IntermediateField.subset_adjoin ℚ _ ?_` and prove the remaining obligations. Use `show pivotRatio ℚ Ψ N (pivPosIncl j (e.symm i)) ∈ coneRatios (yPart j) c`. Take `⟨k, b, hb⟩` from `e.symm i`. Set `S : PluckerBlocks N N (j k).2` to `⟨Finset.univ.image (pivotCols (j k).2 b), card_image_pivotCols _ b hb.le⟩`.

Use `⟨⟨k, ⟨S.1.orderEmbOfFin S.2, (S.1.orderEmbOfFin S.2).strictMono⟩⟩, ?_⟩` and prove the remaining obligations. Establish `h1` using `flagMinor_eq_yFl Ψ N (j k).1 (j k).2 S`. Establish `h2` using `pivotMinor_eq_flagMinor (genMatFr ℚ Ψ N (j k).1) (j k).2 b hb.le`. Establish `h3` using `yFl_lead Ψ N (j k)`. Use `show yFl Ψ N ⟨j k, ⟨S.1.orderEmbOfFin S.2, (S.1.orderEmbOfFin S.2).strictMono⟩⟩ / yFl Ψ N ⟨j k, leadIdx Ψ N (j k)⟩ = pivotMinor (genMatFr ℚ Ψ N (j k).1) (j k).2 b / leadMinor (genMatFr ℚ Ψ N (j k).1) (j k).2`.

Rewrite using `[h3]`. Use `congr 1`. Conclude with `h1.symm.trans h2.symm`. Establish `halg : ∀ r ∈ coneRatios (yPart j) c, IsAlgebraic (IntermediateField.adjoin ℚ (Set.range t)) r`. Introduce and unpack `_ ⟨⟨k, A⟩, rfl⟩`.

Establish `hT : ∀ (k' : K) (b : Fin N) (h : ((j k').2 : ℕ) < b), pivotMinor (genMatFr ℚ Ψ N (j k').1) (j k').2 b / leadMinor (genMatFr ℚ Ψ N (j k').1) (j k').2 ∈ IntermediateField.adjoin ℚ (Set.range t)` using `fun k' b h => IntermediateField.subset_adjoin ℚ _ ⟨e ⟨k', b, h⟩, by show pivotRatio ℚ Ψ N (pivPosIncl j (e.symm (e ⟨k', b, h⟩))) = _`. Rewrite using `[e.symm_apply_apply]`. Use the proof step `rfl⟩`. Establish `hm : yPart j ⟨k, A⟩ / yPart j ⟨k, c k⟩ ∈ IntermediateField.adjoin ℚ (Set.range t)` using `by show yFl Ψ N ⟨j k, A⟩ / yFl Ψ N ⟨j k, leadIdx Ψ N (j k)⟩ ∈ _`. Rewrite using `[yFl_lead, yFl_eq_flagMinor]`.

Use `flag_mem_of_le ℚ (genMatFr ℚ Ψ N (j k).1) _ (hL _) (j k).2 (fun a b ha hb => ?_) _` and prove the remaining obligations. Take `⟨k', hk'⟩` from `hj.down k ((j k).1, a) rfl ha`. Establish `h` using `hT k' b (by rw [hk']; exact hb)`. Rewrite `h` using `[hk']`. Conclude with `h`.

Conclude with `isAlgebraic_algebraMap (⟨_, hm⟩ : IntermediateField.adjoin ℚ (Set.range t))`. Conclude with `CoordConeArithVar.full K (PIdx j) (ΩFl Ψ N) (yPart j) c (cellDim j) t ‹_› hc hind hmem halg`.
-/
theorem isArithVar_pPart (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (K : Type) [Fintype K] [Nonempty K]
    (j : K → FlBlock Ψ N) (hj : IsChain j) : IsArithVar (PPart j) (cellDim j + 1) := by
  classical
  let e : PivPos j ≃ Fin (cellDim j) := Fintype.equivFinOfCardEq (card_pivPos j)
  let t : Fin (cellDim j) → ΩFl Ψ N := fun i => pivotRatio ℚ Ψ N (pivPosIncl j (e.symm i))
  let c : ∀ k, PIdx j k := fun k => leadIdx Ψ N (j k)
  have hL : ∀ (τ : Ψ) (a : Fin (N - 1)), leadMinor (genMatFr ℚ Ψ N τ) a ≠ 0 := fun τ a =>
    GenLeadMinorNeZero.full ℚ Ψ N τ a
  have hc : ∀ k, yPart j ⟨k, c k⟩ ≠ 0 := fun k => by
    show yFl Ψ N ⟨j k, leadIdx Ψ N (j k)⟩ ≠ 0
    rw [yFl_lead]
    exact hL _ _
  have hind : AlgebraicIndependent ℚ t := by
    exact (pivotRatio_rat_algebraicIndependent Ψ N).comp _
      ((pivPosIncl_injective hj.inj).comp e.symm.injective)
  have hmem : ∀ i, t i ∈ IntermediateField.adjoin ℚ (coneRatios (yPart j) c) := by
    intro i
    refine IntermediateField.subset_adjoin ℚ _ ?_
    show pivotRatio ℚ Ψ N (pivPosIncl j (e.symm i)) ∈ coneRatios (yPart j) c
    obtain ⟨k, b, hb⟩ := e.symm i
    let S : PluckerBlocks N N (j k).2 := ⟨Finset.univ.image (pivotCols (j k).2 b), card_image_pivotCols _ b hb.le⟩
    refine ⟨⟨k, ⟨S.1.orderEmbOfFin S.2, (S.1.orderEmbOfFin S.2).strictMono⟩⟩, ?_⟩
    have h1 := flagMinor_eq_yFl Ψ N (j k).1 (j k).2 S
    have h2 := pivotMinor_eq_flagMinor (genMatFr ℚ Ψ N (j k).1) (j k).2 b hb.le
    have h3 := yFl_lead Ψ N (j k)
    show yFl Ψ N ⟨j k, ⟨S.1.orderEmbOfFin S.2, (S.1.orderEmbOfFin S.2).strictMono⟩⟩ /
      yFl Ψ N ⟨j k, leadIdx Ψ N (j k)⟩ = pivotMinor (genMatFr ℚ Ψ N (j k).1) (j k).2 b /
        leadMinor (genMatFr ℚ Ψ N (j k).1) (j k).2
    rw [h3]
    congr 1
    exact h1.symm.trans h2.symm
  have halg : ∀ r ∈ coneRatios (yPart j) c, IsAlgebraic (IntermediateField.adjoin ℚ (Set.range t)) r := by
    rintro _ ⟨⟨k, A⟩, rfl⟩
    have hT : ∀ (k' : K) (b : Fin N) (h : ((j k').2 : ℕ) < b),
        pivotMinor (genMatFr ℚ Ψ N (j k').1) (j k').2 b / leadMinor (genMatFr ℚ Ψ N (j k').1) (j k').2 ∈
          IntermediateField.adjoin ℚ (Set.range t) := fun k' b h =>
      IntermediateField.subset_adjoin ℚ _ ⟨e ⟨k', b, h⟩, by
        show pivotRatio ℚ Ψ N (pivPosIncl j (e.symm (e ⟨k', b, h⟩))) = _
        rw [e.symm_apply_apply]
        rfl⟩
    have hm : yPart j ⟨k, A⟩ / yPart j ⟨k, c k⟩ ∈ IntermediateField.adjoin ℚ (Set.range t) := by
      show yFl Ψ N ⟨j k, A⟩ / yFl Ψ N ⟨j k, leadIdx Ψ N (j k)⟩ ∈ _
      rw [yFl_lead, yFl_eq_flagMinor]
      refine flag_mem_of_le ℚ (genMatFr ℚ Ψ N (j k).1) _ (hL _) (j k).2 (fun a b ha hb => ?_) _
      obtain ⟨k', hk'⟩ := hj.down k ((j k).1, a) rfl ha
      have h := hT k' b (by rw [hk']; exact hb)
      rw [hk'] at h
      exact h
    exact isAlgebraic_algebraMap (⟨_, hm⟩ : IntermediateField.adjoin ℚ (Set.range t))
  exact CoordConeArithVar.full K (PIdx j) (ΩFl Ψ N) (yPart j) c (cellDim j) t ‹_› hc hind hmem halg

end GlobalTheory.CompanionTheory.Ar.Top.FlDeg
