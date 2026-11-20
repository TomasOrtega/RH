import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFlagRatioTrdeg
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFlagPivotAlgIndep
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFlagPivotIdentity
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

namespace FlagRatioTrdeg

/- English proof (translation)
Rewrite using `[← hx.aevalEquivField.trdeg_eq]`. Establish `: Algebra.IsAlgebraic (MvPolynomial ι F) (FractionRing (MvPolynomial ι F))` using `IsLocalization.isAlgebraic _ (nonZeroDivisors _)`. Conclude with `((IsTranscendenceBasis.mvPolynomial ι F).algebraMap_comp (A := FractionRing (MvPolynomial ι F))).cardinalMk_eq_trdeg.symm`.
-/
theorem trdeg_adjoin_eq {F E ι : Type} [Field F] [Field E] [Algebra F E] {x : ι → E}
    (hx : AlgebraicIndependent F x) :
    Algebra.trdeg F (IntermediateField.adjoin F (Set.range x)) = Cardinal.mk ι := by
  rw [← hx.aevalEquivField.trdeg_eq]
  have : Algebra.IsAlgebraic (MvPolynomial ι F) (FractionRing (MvPolynomial ι F)) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors _)
  exact ((IsTranscendenceBasis.mvPolynomial ι F).algebraMap_comp
    (A := FractionRing (MvPolynomial ι F))).cardinalMk_eq_trdeg.symm

/- English proof (translation)
Set `Kp` to `FractionRing (MvPolynomial ι F)`. Set `Xk : ι → Kp` to `fun i => algebraMap (MvPolynomial ι F) Kp (X i)`. Establish `hXk : ∀ i, Xk i ≠ 0` using `fun i => by`. Simplify using `only [Xk, ne_eq, IsFractionRing.to_map_eq_zero_iff]`. Conclude with `X_ne_zero i`.

Establish `hXind : AlgebraicIndependent F Xk` using `(algebraicIndependent_X ι F).map' (f := IsScalarTower.toAlgHom F (MvPolynomial ι F) Kp) (IsFractionRing.injective _ _)`. Set `d : ι → Kp` to `fun i => if δ i = i then Xk i else Xk i / Xk (δ i)`. Set `c : ι → MvPolynomial ι F` to `fun i => if δ i = i then X i else X i * X (δ i)`. Establish `hdδ : ∀ i, d (δ i) = Xk (δ i)` using `fun i => by simp only [d, hδ, if_true]`. Establish `hcδ : ∀ i, c (δ i) = X (δ i)` using `fun i => by simp only [c, hδ, if_true]`.

Establish `hdc : ∀ i, aeval d (c i) = Xk i`. Introduce `i`. Distinguish the cases in `h : δ i = i`. Simplify using `only [c, d, h, if_true, aeval_X]`. Simplify using `only [c, h, if_false, map_mul, aeval_X]`.

Rewrite using `[hdδ]`. Simplify using `only [d, h, if_false]`. Conclude with `div_mul_cancel₀ _ (hXk _)`. Establish `hc : AlgebraicIndependent F c`. Use `AlgebraicIndependent.of_comp (aeval d) ?_` and prove the remaining obligations.

Establish `: ⇑(aeval d) ∘ c = Xk` using `funext hdc`. Rewrite using `[this]`. Conclude with `hXind`. Set `χ : Kp →ₐ[F] Kp` to `IsFractionRing.liftAlgHom (g := (IsScalarTower.toAlgHom F (MvPolynomial ι F) Kp).comp (aeval c)) ((IsFractionRing.injective (MvPolynomial ι F) Kp).comp (algebraicIndependent_iff_injective_aeval.1 hc))`. Establish `hχX : ∀ j, χ (Xk j) = algebraMap (MvPolynomial ι F) Kp (c j)` using `fun j => by`.

Simplify using `[χ, Xk, IsFractionRing.lift_algebraMap]`. Establish `hχ : ∀ i, χ (d i) = Xk i`. Introduce `i`. Distinguish the cases in `h : δ i = i`. Simplify using `only [d, h, if_true]`.

Rewrite using `[hχX]`. Simplify using `only [c, h, if_true, Xk]`. Simplify using `only [d, h, if_false, map_div₀]`. Rewrite using `[hχX, hχX, hcδ]`. Simplify using `only [c, h, if_false, map_mul]`.

Conclude with `mul_div_cancel_right₀ _ (hXk _)`. Establish `hd : AlgebraicIndependent F d`. Use `AlgebraicIndependent.of_comp χ ?_` and prove the remaining obligations. Establish `: ⇑χ ∘ d = Xk` using `funext hχ`. Rewrite using `[this]`.

Conclude with `hXind`. Set `ψ : Kp →ₐ[F] E` to `IsFractionRing.liftAlgHom (g := aeval y) (algebraicIndependent_iff_injective_aeval.1 hy)`. Establish `hψX : ∀ j, ψ (Xk j) = y j` using `fun j => by`. Simplify using `[ψ, Xk, IsFractionRing.lift_algebraMap]`. Establish `hψ : ⇑ψ ∘ d = fun i => if δ i = i then y i else y i / y (δ i)`.

Use function extensionality and compare the values at `i`. Distinguish the cases in `h : δ i = i`. Simplify using `only [Function.comp_apply, d, h, if_true, hψX]`. Simplify using `only [Function.comp_apply, d, h, if_false, map_div₀, hψX]`. Rewrite using `[← hψ]`.

Conclude with `hd.map' (ψ : Kp →+* E).injective`.
-/
theorem ratio_indep (F : Type) [Field F] {ι E : Type} [Field E] [Algebra F E] [DecidableEq ι] {y : ι → E}
    (hy : AlgebraicIndependent F y) (δ : ι → ι) (hδ : ∀ i, δ (δ i) = δ i) :
    AlgebraicIndependent F (fun i => if δ i = i then y i else y i / y (δ i)) := by
  let Kp := FractionRing (MvPolynomial ι F)
  let Xk : ι → Kp := fun i => algebraMap (MvPolynomial ι F) Kp (X i)
  have hXk : ∀ i, Xk i ≠ 0 := fun i => by
    simp only [Xk, ne_eq, IsFractionRing.to_map_eq_zero_iff]
    exact X_ne_zero i
  have hXind : AlgebraicIndependent F Xk :=
    (algebraicIndependent_X ι F).map' (f := IsScalarTower.toAlgHom F (MvPolynomial ι F) Kp)
      (IsFractionRing.injective _ _)
  let d : ι → Kp := fun i => if δ i = i then Xk i else Xk i / Xk (δ i)
  let c : ι → MvPolynomial ι F := fun i => if δ i = i then X i else X i * X (δ i)
  have hdδ : ∀ i, d (δ i) = Xk (δ i) := fun i => by simp only [d, hδ, if_true]
  have hcδ : ∀ i, c (δ i) = X (δ i) := fun i => by simp only [c, hδ, if_true]
  have hdc : ∀ i, aeval d (c i) = Xk i := by
    intro i
    by_cases h : δ i = i
    · simp only [c, d, h, if_true, aeval_X]
    · simp only [c, h, if_false, map_mul, aeval_X]
      rw [hdδ]
      simp only [d, h, if_false]
      exact div_mul_cancel₀ _ (hXk _)
  have hc : AlgebraicIndependent F c := by
    refine AlgebraicIndependent.of_comp (aeval d) ?_
    have : ⇑(aeval d) ∘ c = Xk := funext hdc
    rw [this]
    exact hXind
  let χ : Kp →ₐ[F] Kp := IsFractionRing.liftAlgHom
    (g := (IsScalarTower.toAlgHom F (MvPolynomial ι F) Kp).comp (aeval c))
    ((IsFractionRing.injective (MvPolynomial ι F) Kp).comp (algebraicIndependent_iff_injective_aeval.1 hc))
  have hχX : ∀ j, χ (Xk j) = algebraMap (MvPolynomial ι F) Kp (c j) := fun j => by
    simp [χ, Xk, IsFractionRing.lift_algebraMap]
  have hχ : ∀ i, χ (d i) = Xk i := by
    intro i
    by_cases h : δ i = i
    · simp only [d, h, if_true]
      rw [hχX]
      simp only [c, h, if_true, Xk]
    · simp only [d, h, if_false, map_div₀]
      rw [hχX, hχX, hcδ]
      simp only [c, h, if_false, map_mul]
      exact mul_div_cancel_right₀ _ (hXk _)
  have hd : AlgebraicIndependent F d := by
    refine AlgebraicIndependent.of_comp χ ?_
    have : ⇑χ ∘ d = Xk := funext hχ
    rw [this]
    exact hXind
  let ψ : Kp →ₐ[F] E := IsFractionRing.liftAlgHom (g := aeval y) (algebraicIndependent_iff_injective_aeval.1 hy)
  have hψX : ∀ j, ψ (Xk j) = y j := fun j => by
    simp [ψ, Xk, IsFractionRing.lift_algebraMap]
  have hψ : ⇑ψ ∘ d = fun i => if δ i = i then y i else y i / y (δ i) := by
    funext i
    by_cases h : δ i = i
    · simp only [Function.comp_apply, d, h, if_true, hψX]
    · simp only [Function.comp_apply, d, h, if_false, map_div₀, hψX]
  rw [← hψ]
  exact hd.map' (ψ : Kp →+* E).injective

def genMatPol (F : Type) [Field F] (Ψ : Type) (n : ℕ) (τ : Ψ) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Ψ × Fin n × Fin n) F) :=
  Matrix.of fun a b => X (τ, a, b)

/- English proof (translation)
Unfold `pivotMinor`. Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression.
-/
theorem pivotMinor_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {m : ℕ}
    (M : Matrix (Fin m) (Fin m) R) (a : Fin (m - 1)) (b : Fin m) :
    pivotMinor (M.map f) a b = f (pivotMinor M a b) := by
  unfold pivotMinor
  rw [RingHom.map_det]
  rfl

/- English proof (translation)
Use extensionality with `a b`. Both sides reduce to the same expression.
-/
theorem genMatFr_eq (F : Type) [Field F] (Ψ : Type) (n : ℕ) (τ : Ψ) :
    genMatFr F Ψ n τ = (genMatPol F Ψ n τ).map (algebraMap _ (GenFrac F Ψ n)) := by
  ext a b
  rfl

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[genMatPol, genMat]`.
-/
theorem genMatPol_eq (F : Type) [Field F] (Ψ : Type) (n : ℕ) (τ : Ψ) :
    genMatPol F Ψ n τ = (genMat F n).map (rename fun p : Fin n × Fin n => (τ, p)).toRingHom := by
  ext a b
  simp [genMatPol, genMat]

abbrev PivotIdxLe (Ψ : Type) (n : ℕ) : Type := Ψ × Σ a : Fin (n - 1), {b : Fin n // (a : ℕ) ≤ b}

/- English proof (translation)
Introduce `_ _ h` and use `rename_injective _ (Prod.mk_right_injective τ) (IsFractionRing.injective (MvPolynomial (Ψ × Fin n × Fin n) F) (GenFrac F Ψ n) h)`.
-/
theorem embed_inj (F : Type) [Field F] (Ψ : Type) (n : ℕ) (τ : Ψ) :
    Function.Injective ((IsScalarTower.toAlgHom F (MvPolynomial (Ψ × Fin n × Fin n) F) (GenFrac F Ψ n)).comp
      (rename fun p : Fin n × Fin n => (τ, p))) := fun _ _ h =>
  rename_injective _ (Prod.mk_right_injective τ)
    (IsFractionRing.injective (MvPolynomial (Ψ × Fin n × Fin n) F) (GenFrac F Ψ n) h)

def embed (F : Type) [Field F] (Ψ : Type) (n : ℕ) (τ : Ψ) :
    FractionRing (MvPolynomial (Fin n × Fin n) F) →ₐ[F] GenFrac F Ψ n :=
  IsFractionRing.liftAlgHom (embed_inj F Ψ n τ)

/- English proof (translation)
Use `show IsFractionRing.lift (embed_inj F Ψ n τ) _ = _`. Rewrite using `[IsFractionRing.lift_algebraMap]`. Both sides reduce to the same expression.
-/
theorem embed_algebraMap (F : Type) [Field F] (Ψ : Type) (n : ℕ) (τ : Ψ) (p : MvPolynomial (Fin n × Fin n) F) :
    embed F Ψ n τ (algebraMap _ _ p) =
      algebraMap (MvPolynomial (Ψ × Fin n × Fin n) F) (GenFrac F Ψ n) (rename (fun q => (τ, q)) p) := by
  show IsFractionRing.lift (embed_inj F Ψ n τ) _ = _
  rw [IsFractionRing.lift_algebraMap]
  rfl

def specAll (F : Type) [Field F] (Ψ : Type) (n : ℕ) (q : Ψ × Fin n × Fin n) : GenFrac F Ψ n :=
  embed F Ψ n q.1 (FlagPivotAlgIndep.spec F n q.2)

/- English proof (translation)
Rewrite using `[genMatPol_eq, pivotMinor_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_rename]`. Establish `e : specAll F Ψ n ∘ (fun p : Fin n × Fin n => (τ, p)) = fun p => embed F Ψ n τ (FlagPivotAlgIndep.spec F n p)`. Both sides reduce to the same expression. Rewrite using `[e, ← comp_aeval_apply, FlagPivotAlgIndep.spec_pivotMinor F n a b hab]`. Rewrite using `[FlagPivotAlgIndep.genFrac, embed_algebraMap, rename_X]`.
-/
theorem specAll_pivotMinor (F : Type) [Field F] (Ψ : Type) (n : ℕ) (τ : Ψ) (a : Fin (n - 1)) (b : Fin n)
    (hab : (a : ℕ) ≤ b) :
    aeval (specAll F Ψ n) (pivotMinor (genMatPol F Ψ n τ) a b) =
      algebraMap (MvPolynomial (Ψ × Fin n × Fin n) F) (GenFrac F Ψ n) (X (τ, Fin.castLE (Nat.sub_le n 1) a, b)) := by
  rw [genMatPol_eq, pivotMinor_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_rename]
  have e : specAll F Ψ n ∘ (fun p : Fin n × Fin n => (τ, p)) = fun p => embed F Ψ n τ (FlagPivotAlgIndep.spec F n p) :=
    rfl
  rw [e, ← comp_aeval_apply, FlagPivotAlgIndep.spec_pivotMinor F n a b hab]
  rw [FlagPivotAlgIndep.genFrac, embed_algebraMap, rename_X]

/- English proof (translation)
Use `AlgebraicIndependent.of_comp (aeval (specAll F Ψ n)) ?_` and prove the remaining obligations. Establish `hfun : ⇑(aeval (specAll F Ψ n)) ∘ (fun q : PivotIdxLe Ψ n => pivotMinor (genMatPol F Ψ n q.1) q.2.1 q.2.2.1) = ⇑(IsScalarTower.toAlgHom F (MvPolynomial (Ψ × Fin n × Fin n) F) (GenFrac F Ψ n)) ∘ ((X : Ψ × Fin n × Fin n → MvPolynomial (Ψ × Fin n × Fin n) F) ∘ fun q : PivotIdxLe Ψ n …`. Use function extensionality and compare the values at `q`. Conclude with `specAll_pivotMinor F Ψ n q.1 q.2.1 q.2.2.1 q.2.2.2`. Rewrite using `[hfun]`.

Use `AlgebraicIndependent.map' ?_ (IsFractionRing.injective _ _)` and prove the remaining obligations. Use `(algebraicIndependent_X _ F).comp _ ?_` and prove the remaining obligations. Introduce and unpack `⟨τ, a, b, hb⟩ ⟨τ', a', b', hb'⟩ h`. Simplify using `only [Prod.mk.injEq] at h`. Take `⟨h0, h1, h2⟩` from `h`.

Establish `h1' : a = a'` using `Fin.ext (by simpa using congrArg Fin.val h1)`. Substitute `h0 h1' h2` using the available equality. Both sides reduce to the same expression.
-/
theorem pol_indep (F : Type) [Field F] (Ψ : Type) (n : ℕ) :
    AlgebraicIndependent F (fun q : PivotIdxLe Ψ n => pivotMinor (genMatPol F Ψ n q.1) q.2.1 q.2.2.1) := by
  refine AlgebraicIndependent.of_comp (aeval (specAll F Ψ n)) ?_
  have hfun : ⇑(aeval (specAll F Ψ n)) ∘
        (fun q : PivotIdxLe Ψ n => pivotMinor (genMatPol F Ψ n q.1) q.2.1 q.2.2.1) =
      ⇑(IsScalarTower.toAlgHom F (MvPolynomial (Ψ × Fin n × Fin n) F) (GenFrac F Ψ n)) ∘
        ((X : Ψ × Fin n × Fin n → MvPolynomial (Ψ × Fin n × Fin n) F) ∘
          fun q : PivotIdxLe Ψ n => (q.1, Fin.castLE (Nat.sub_le n 1) q.2.1, q.2.2.1)) := by
    funext q
    exact specAll_pivotMinor F Ψ n q.1 q.2.1 q.2.2.1 q.2.2.2
  rw [hfun]
  refine AlgebraicIndependent.map' ?_ (IsFractionRing.injective _ _)
  refine (algebraicIndependent_X _ F).comp _ ?_
  rintro ⟨τ, a, b, hb⟩ ⟨τ', a', b', hb'⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h0, h1, h2⟩ := h
  have h1' : a = a' := Fin.ext (by simpa using congrArg Fin.val h1)
  subst h0 h1' h2
  rfl

/- English proof (translation)
Establish `h` using `(pol_indep F Ψ n).map' (f := IsScalarTower.toAlgHom F (MvPolynomial (Ψ × Fin n × Fin n) F) (GenFrac F Ψ n)) (IsFractionRing.injective _ _)`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `q`. Rewrite using `[Function.comp_apply, genMatFr_eq, pivotMinor_map]`. Both sides reduce to the same expression.
-/
theorem pivot_indep (F : Type) [Field F] (Ψ : Type) (n : ℕ) :
    AlgebraicIndependent F (fun q : PivotIdxLe Ψ n => pivotMinor (genMatFr F Ψ n q.1) q.2.1 q.2.2.1) := by
  have h := (pol_indep F Ψ n).map'
    (f := IsScalarTower.toAlgHom F (MvPolynomial (Ψ × Fin n × Fin n) F) (GenFrac F Ψ n))
    (IsFractionRing.injective _ _)
  convert h using 1
  funext q
  rw [Function.comp_apply, genMatFr_eq, pivotMinor_map]
  rfl

/- English proof (translation)
Use `Finset.prod_bij' (fun a ha => ⟨a, by have := Finset.mem_Iic.1 ha; rw [Fin.le_def] at this; omega⟩) (fun r _ => ⟨r, by have := r.2; have := j.2; omega⟩) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `a _`. Conclude with `Finset.mem_univ _`. Introduce `r _`. Rewrite using `[Finset.mem_Iic, Fin.le_def]`.

Use `r.2` as an intermediate fact. Simplify using `only`. Use linear arithmetic over natural numbers and integers. Introduce `a _`. Both sides reduce to the same expression.

Introduce `r _`. Both sides reduce to the same expression. Introduce `a _`. Both sides reduce to the same expression.
-/
theorem prod_Iic_fin {M : Type} [CommMonoid M] {m : ℕ} (f : Fin m → M) (j : Fin m) :
    ∏ a ∈ Finset.Iic j, f a = ∏ r : Fin (j + 1), f ⟨r, by have := r.2; have := j.2; omega⟩ := by
  refine Finset.prod_bij' (fun a ha => ⟨a, by have := Finset.mem_Iic.1 ha; rw [Fin.le_def] at this; omega⟩)
    (fun r _ => ⟨r, by have := r.2; have := j.2; omega⟩) ?_ ?_ ?_ ?_ ?_
  · intro a _; exact Finset.mem_univ _
  · intro r _; rw [Finset.mem_Iic, Fin.le_def]; have := r.2; simp only; omega
  · intro a _; rfl
  · intro r _; rfl
  · intro a _; rfl

/- English proof (translation)
Establish `hj : (j : ℕ) + 1 ≤ m` using `by have := j.2; omega`. Establish `hent : ∀ (a : Fin (m - 1)) (b : Fin m), pivotMinor g a b / leadMinor g a ∈ A`. Introduce `a b`. Break down `lt_trichotomy (b : ℕ) a with h | h | h` into its components or cases. Rewrite using `[pivotMinor_eq_zero g a b h, zero_div]`.

Conclude with `A.zero_mem`. Establish `e : b = Fin.castLE (Nat.sub_le m 1) a` using `Fin.ext h`. Substitute `e` using the available equality. Use `show leadMinor g a / leadMinor g a ∈ A`. Rewrite using `[div_self (hL a)]`.

Conclude with `A.one_mem`. Conclude with `hA a b h`. Set `U : Matrix (Fin (j + 1)) (Fin (j + 1)) K` to `Matrix.of fun r s => pivotMinor g ⟨r, by have := r.2; have := j.2; omega⟩ (S.1.orderEmbOfFin S.2 s) / leadMinor g ⟨r, by have := r.2; have := j.2; omega⟩`. Establish `hP : (pivotMatrix g).submatrix (Fin.castLE hj) (S.1.orderEmbOfFin S.2) = Matrix.diagonal (fun r : Fin (j + 1) => leadMinor g ⟨r, by have` using `r.2; have := j.2; omega⟩) * U := by`. Use extensionality with `r s`.

Rewrite using `[Matrix.diagonal_mul]`. Simplify using `only [Matrix.submatrix_apply, pivotMatrix, Matrix.of_apply, U]`. Rewrite using `[dif_pos (by simp only [Fin.val_castLE]; have := r.2; have := j.2; omega)]`. Rewrite using `[mul_div_cancel₀ _ (hL _)]`. Both sides reduce to the same expression.

Establish `hdet : flagMinor (pivotMatrix g) j S = (∏ r : Fin (j + 1), leadMinor g ⟨r, by have` using `r.2; have := j.2; omega⟩) * U.det := by`. Unfold `flagMinor`. Rewrite using `[hP, Matrix.det_mul, Matrix.det_diagonal]`. Establish `hid` using `FlagPivotIdentity.proof K m g j S`. Rewrite `hid` using `[prod_Iic_fin, hdet]`.

Establish `hne : (∏ r : Fin (j + 1), leadMinor g ⟨r, by have` using `r.2; have := j.2; omega⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun r _ => hL _`. Establish `hU : flagMinor g j S / leadMinor g j = U.det`. Rewrite using `[div_eq_iff (hL j)]`. Apply `mul_right_cancel₀ hne` to reduce the goal to its premises. Take the linear combination `hid`.

Rewrite using `[hU, Matrix.det_apply]`. Use `A.sum_mem fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Units.smul_def]`. Conclude with `zsmul_mem (A.prod_mem fun r _ => hent _ _) _`.
-/
theorem flag_mem (F : Type) [Field F] {K : Type} [Field K] [Algebra F K] {m : ℕ} (g : Matrix (Fin m) (Fin m) K)
    (A : IntermediateField F K) (hL : ∀ a, leadMinor g a ≠ 0)
    (hA : ∀ (a : Fin (m - 1)) (b : Fin m), (a : ℕ) < b → pivotMinor g a b / leadMinor g a ∈ A)
    (j : Fin (m - 1)) (S : PluckerBlocks m m j) : flagMinor g j S / leadMinor g j ∈ A := by
  have hj : (j : ℕ) + 1 ≤ m := by have := j.2; omega
  have hent : ∀ (a : Fin (m - 1)) (b : Fin m), pivotMinor g a b / leadMinor g a ∈ A := by
    intro a b
    rcases lt_trichotomy (b : ℕ) a with h | h | h
    · rw [pivotMinor_eq_zero g a b h, zero_div]
      exact A.zero_mem
    · have e : b = Fin.castLE (Nat.sub_le m 1) a := Fin.ext h
      subst e
      show leadMinor g a / leadMinor g a ∈ A
      rw [div_self (hL a)]
      exact A.one_mem
    · exact hA a b h
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
  exact zsmul_mem (A.prod_mem fun r _ => hent _ _) _

/- English proof (translation)
Rewrite using `[Fintype.card_prod, Fintype.card_sigma]`. Use `congr 1`. Establish `h1 : ∀ a : Fin (n - 1), Fintype.card {b : Fin n // (a : ℕ) < b} = n - 1 - a`. Introduce `a`. Rewrite using `[Fintype.card_subtype]`.

Establish `: (Finset.univ.filter fun b : Fin n => (a : ℕ) < b) = Finset.Ioi (Fin.castLE (Nat.sub_le n 1) a)`. Use extensionality with `b`. Simplify using `[Fin.lt_def]`. Rewrite using `[this, Fin.card_Ioi]`. Simplify using the standard rewrite rules.

Simplify using `only [h1]`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => n - 1 - i) (n - 1)]`. Establish `h2 : ∀ m : ℕ, (∑ i ∈ Finset.range m, (m - i)) * 2 = (m + 1) * m`. Introduce `m`. Proceed by induction on `m with`.

Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[Finset.sum_range_succ']`. Simplify using `only [Nat.add_sub_add_right, Nat.sub_zero]`. Rewrite using `[add_mul, ih]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h3` using `h2 (n - 1)`. Unfold `flagDim`. Break down `Nat.eq_zero_or_pos n with h | h` into its components or cases. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Establish `e : n - 1 + 1 = n` using `by omega`. Rewrite `h3` using `[e]`. Generalize the expression as in `n * (n - 1) = t at h3 ⊢`. Generalize the expression as in `(∑ i ∈ Finset.range (n - 1), (n - 1 - i)) = s at h3 ⊢`.

Use linear arithmetic over natural numbers and integers.
-/
theorem card_pivotIdx (Ψ : Type) [Fintype Ψ] (n : ℕ) :
    Fintype.card (PivotIdx Ψ n) = Fintype.card Ψ * flagDim n := by
  rw [Fintype.card_prod, Fintype.card_sigma]
  congr 1
  have h1 : ∀ a : Fin (n - 1), Fintype.card {b : Fin n // (a : ℕ) < b} = n - 1 - a := by
    intro a
    rw [Fintype.card_subtype]
    have : (Finset.univ.filter fun b : Fin n => (a : ℕ) < b) = Finset.Ioi (Fin.castLE (Nat.sub_le n 1) a) := by
      ext b
      simp [Fin.lt_def]
    rw [this, Fin.card_Ioi]
    simp
  simp only [h1]
  rw [Fin.sum_univ_eq_sum_range (fun i => n - 1 - i) (n - 1)]
  have h2 : ∀ m : ℕ, (∑ i ∈ Finset.range m, (m - i)) * 2 = (m + 1) * m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ']
      simp only [Nat.add_sub_add_right, Nat.sub_zero]
      rw [add_mul, ih]
      ring
  have h3 := h2 (n - 1)
  unfold flagDim
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp
  · have e : n - 1 + 1 = n := by omega
    rw [e] at h3
    generalize n * (n - 1) = t at h3 ⊢
    generalize (∑ i ∈ Finset.range (n - 1), (n - 1 - i)) = s at h3 ⊢
    omega

/- English proof (translation)
Introduce `F _ Ψ _ n`. Establish `hy` using `pivot_indep F Ψ n`. Set `δ : PivotIdxLe Ψ n → PivotIdxLe Ψ n` to `fun q => (q.1, ⟨q.2.1, ⟨Fin.castLE (Nat.sub_le n 1) q.2.1, by simp⟩⟩)`. Establish `hz` using `ratio_indep F hy δ (fun q => rfl)`. Set `incl : PivotIdx Ψ n → PivotIdxLe Ψ n` to `fun q => (q.1, ⟨q.2.1, ⟨q.2.2.1, q.2.2.2.le⟩⟩)`.

Establish `hincl : Function.Injective incl`. Introduce and unpack `⟨τ, a, b, hb⟩ ⟨τ', a', b', hb'⟩ h`. Simplify using `only [incl, Prod.mk.injEq, Sigma.mk.inj_iff] at h`. Take `⟨h0, h1, h2⟩` from `h`. Substitute `h0 h1` using the available equality.

Simplify using `only [heq_eq_eq, Subtype.mk.injEq] at h2`. Substitute `h2` using the available equality. Both sides reduce to the same expression. Establish `hrat : (fun q : PivotIdxLe Ψ n => if δ q = q then pivotMinor (genMatFr F Ψ n q.1) q.2.1 q.2.2.1 else pivotMinor (genMatFr F Ψ n q.1) q.2.1 q.2.2.1 / pivotMinor (genMatFr F Ψ n (δ q).1) (δ q).2.1 (δ q).2.2.1) ∘ incl = pivotRatio F Ψ n`. Use function extensionality and compare the values at `q`.

Establish `hne : δ (incl q) ≠ incl q`. Introduce `h`. Use `congrArg (fun r : PivotIdxLe Ψ n => ((r.2.2.1 : Fin n) : ℕ)) h` as an intermediate fact. Simplify using `only [δ, incl, Fin.val_castLE] at this`. Use `q.2.2.2` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Simplify using `only [Function.comp_apply, hne, if_false]`. Both sides reduce to the same expression. Establish `hpr : AlgebraicIndependent F (pivotRatio F Ψ n)` using `hrat ▸ hz.comp incl hincl`. Establish `hL : ∀ (τ : Ψ) (a : Fin (n - 1)), leadMinor (genMatFr F Ψ n τ) a ≠ 0` using `fun τ a => hy.ne_zero (τ, ⟨a, ⟨Fin.castLE (Nat.sub_le n 1) a, by simp⟩⟩)`.

Establish `hadj : IntermediateField.adjoin F (Set.range (flagMinorRatio F Ψ n)) = IntermediateField.adjoin F (Set.range (pivotRatio F Ψ n))`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[IntermediateField.adjoin_le_iff]`. Introduce and unpack `_ ⟨⟨τ, j, S⟩, rfl⟩`. Use `flag_mem F (genMatFr F Ψ n τ) _ (hL τ) (fun a b hab => ?_) j S` and prove the remaining obligations.

Conclude with `IntermediateField.subset_adjoin F _ ⟨(τ, ⟨a, ⟨b, hab⟩⟩), rfl⟩`. Rewrite using `[IntermediateField.adjoin_le_iff]`. Introduce and unpack `_ ⟨⟨τ, a, b, hab⟩, rfl⟩`. Use `IntermediateField.subset_adjoin F _ ⟨(τ, ⟨a, ⟨Finset.univ.image (pivotCols a b), card_image_pivotCols a b hab.le⟩⟩), ?_⟩` and prove the remaining obligations. Simplify using `only [flagMinorRatio, pivotRatio]`.

Rewrite using `[pivotMinor_eq_flagMinor _ a b hab.le]`. Rewrite using `[hadj, trdeg_adjoin_eq hpr, Cardinal.mk_fintype, card_pivotIdx]`.
-/
theorem proof : FlagRatioTrdeg.Statement := by
  intro F _ Ψ _ n
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
  have hpr : AlgebraicIndependent F (pivotRatio F Ψ n) := hrat ▸ hz.comp incl hincl
  have hL : ∀ (τ : Ψ) (a : Fin (n - 1)), leadMinor (genMatFr F Ψ n τ) a ≠ 0 := fun τ a =>
    hy.ne_zero (τ, ⟨a, ⟨Fin.castLE (Nat.sub_le n 1) a, by simp⟩⟩)
  have hadj : IntermediateField.adjoin F (Set.range (flagMinorRatio F Ψ n)) =
      IntermediateField.adjoin F (Set.range (pivotRatio F Ψ n)) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨⟨τ, j, S⟩, rfl⟩
      refine flag_mem F (genMatFr F Ψ n τ) _ (hL τ) (fun a b hab => ?_) j S
      exact IntermediateField.subset_adjoin F _ ⟨(τ, ⟨a, ⟨b, hab⟩⟩), rfl⟩
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨⟨τ, a, b, hab⟩, rfl⟩
      refine IntermediateField.subset_adjoin F _
        ⟨(τ, ⟨a, ⟨Finset.univ.image (pivotCols a b), card_image_pivotCols a b hab.le⟩⟩), ?_⟩
      simp only [flagMinorRatio, pivotRatio]
      rw [pivotMinor_eq_flagMinor _ a b hab.le]
  rw [hadj, trdeg_adjoin_eq hpr, Cardinal.mk_fintype, card_pivotIdx]

end FlagRatioTrdeg

/- English proof (translation)
The claim follows from `FlagRatioTrdeg.proof`.
-/
theorem FlagRatioTrdeg.full : FlagRatioTrdeg.Statement := FlagRatioTrdeg.proof

end GroundTheory.Heights₂.Heights.LowerBoundFree
