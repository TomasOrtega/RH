import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CardPhiSucc
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.DetMulEqSumProdMulDetSubmatrix
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsoCountOneInert

open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.LocalizedFibreSets

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HermitianSublattices Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms
  Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `hx'`. Apply `h` to reduce the goal to its premises. Apply `Nat.eq_zero_of_le_zero` to reduce the goal to its premises.

Use `show sSup {e : ℕ | x ∈ 𝔭 ^ e} ≤ 0`. Apply `csSup_le'` to reduce the goal to its premises. Introduce `e he`. Assume the negation of the conclusion as `hne`. Conclude with `hx' (Ideal.pow_le_self (by omega) he)`.

Introduce `hx'`. Establish `hbdd : BddAbove {e : ℕ | x ∈ 𝔭 ^ e}`. Establish `h0 : x ∉ ⨅ n : ℕ, 𝔭 ^ n`. Rewrite using `[Ideal.iInf_pow_eq_bot_of_isDomain 𝔭 h𝔭.ne_top]`. Simplify using `using hx`.

Simplify using `only [Submodule.mem_iInf, not_forall] at h0`. Take `⟨n, hn⟩` from `h0`. Use `⟨n, fun e he => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`.

Conclude with `hn (Ideal.pow_le_pow_right hlt.le he)`. Establish `h1 : 1 ≤ sSup {e : ℕ | x ∈ 𝔭 ^ e}` using `le_csSup hbdd (show x ∈ 𝔭 ^ 1 by rwa [pow_one])`. Use `show sSup {e : ℕ | x ∈ 𝔭 ^ e} ≠ 0`. Use linear arithmetic over natural numbers and integers.
-/
theorem vF_ne_zero_iff {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {x : 𝓞 F} (hx : x ≠ 0) :
    vF 𝔭 x ≠ 0 ↔ x ∈ 𝔭 := by
  constructor
  · intro h
    by_contra hx'
    apply h
    apply Nat.eq_zero_of_le_zero
    show sSup {e : ℕ | x ∈ 𝔭 ^ e} ≤ 0
    apply csSup_le'
    intro e he
    by_contra hne
    exact hx' (Ideal.pow_le_self (by omega) he)
  · intro hx'
    have hbdd : BddAbove {e : ℕ | x ∈ 𝔭 ^ e} := by
      have h0 : x ∉ ⨅ n : ℕ, 𝔭 ^ n := by
        rw [Ideal.iInf_pow_eq_bot_of_isDomain 𝔭 h𝔭.ne_top]
        simpa using hx
      simp only [Submodule.mem_iInf, not_forall] at h0
      obtain ⟨n, hn⟩ := h0
      refine ⟨n, fun e he => ?_⟩
      by_contra hlt
      push_neg at hlt
      exact hn (Ideal.pow_le_pow_right hlt.le he)
    have h1 : 1 ≤ sSup {e : ℕ | x ∈ 𝔭 ^ e} :=
      le_csSup hbdd (show x ∈ 𝔭 ^ 1 by rwa [pow_one])
    show sSup {e : ℕ | x ∈ 𝔭 ^ e} ≠ 0
    omega

/- English proof (translation)
Use `set n := Fintype.card ι with hn`. Set `e : ι ≃ Fin n` to `Fintype.equivFin ι`. Use `set d : ι → 𝓞 K ⧸ extP K 𝔭 ^ 1 := fun i => Ideal.Quotient.mk (extP K 𝔭 ^ 1) (algebraMap (𝓞 F) (𝓞 K) (b i)) with hd`. Set `u : Fin n → 𝓞 K` to `fun i => algebraMap (𝓞 F) (𝓞 K) (b (e.symm i))`. Establish `hD : (diagonal u).map (Ideal.Quotient.mk (extP K 𝔭 ^ 1)) = Matrix.reindex e e (diagonal d)`.

Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[u, d, Matrix.reindex_apply]`. Establish `hij' : e.symm i ≠ e.symm j` using `fun h => hij (e.symm.injective h)`.

Simplify using `[u, d, Matrix.reindex_apply, Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij']`. Establish `hcard : Nat.card {γ : Matrix ι ι (𝓞 K ⧸ extP K 𝔭 ^ 1) // γᴴ * diagonal d * γ = diagonal d} = Nat.card {X : Matrix (Fin n) (Fin n) (𝓞 K ⧸ extP K 𝔭 ^ 1) // Xᴴ * Matrix.reindex e e (diagonal d) * X = Matrix.reindex e e (diagonal d)}`. Use `Nat.card_congr (Equiv.subtypeEquiv (Matrix.reindex e e) fun γ => ?_)` and prove the remaining obligations. Simplify using `only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]`. Use `⟨fun h => by rw [h], fun h => (Matrix.reindex e e).injective ?_⟩` and prove the remaining obligations.

Simplify `h` using `only [Matrix.reindex_apply]`. Establish `hu : ∀ i, Formalism.HermitianLattices.Ext.L3.conjO K (u i) = u i` using `fun i => by`. Apply `IsFractionRing.injective (𝓞 K) K` to reduce the goal to its premises. Rewrite using `[Formalism.HermitianLattices.Ext.L3.BallB.algebraMap_conjO, (Fact.out : IsFixF K F)]`. Use `⟨((b (e.symm i) : 𝓞 F) : F), ?_⟩` and prove the remaining obligations.

Use `show algebraMap F K (algebraMap (𝓞 F) F (b (e.symm i))) = _`. Rewrite using `[← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K]`. Establish `hunit : ∀ i, Ideal.span {u i} ⊔ extP K 𝔭 = ⊤` using `fun i => by`. Establish `hF : Ideal.span {b (e.symm i)} ⊔ 𝔭 = ⊤`. Use `h𝔭.1.2 _ (lt_of_le_of_ne le_sup_right fun h => hb (e.symm i) ?_)` and prove the remaining obligations.

Rewrite using `[h]`. Conclude with `Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)`. Establish `h2` using `congrArg (Ideal.map (algebraMap (𝓞 F) (𝓞 K))) hF`. Rewrite `h2` using `[Ideal.map_sup, Ideal.map_span, Set.image_singleton, Ideal.map_top]`. Conclude with `h2`.

Rewrite using `[hcard, ← hD]`. Conclude with `Formalism.HermitianLattices.Ext.L3.IsotropicCounts.isoCount_one hK h𝔭 u hu hunit`.
-/
theorem card_U_diag (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {ι : Type}
    [Fintype ι] [DecidableEq ι] (b : ι → 𝓞 F) (hb : ∀ i, b i ∉ 𝔭) :
    (Nat.card {γ : Matrix ι ι (𝓞 K ⧸ extP K 𝔭 ^ 1) //
      γᴴ * diagonal (fun i => Ideal.Quotient.mk (extP K 𝔭 ^ 1) (algebraMap (𝓞 F) (𝓞 K) (b i))) * γ =
        diagonal (fun i => Ideal.Quotient.mk (extP K 𝔭 ^ 1) (algebraMap (𝓞 F) (𝓞 K) (b i)))} : ℝ) =
      (Ideal.absNorm 𝔭 : ℝ) ^ (Fintype.card ι ^ 2) * alphaStd K 𝔭 (Fintype.card ι) := by
  classical
  set n := Fintype.card ι with hn
  let e : ι ≃ Fin n := Fintype.equivFin ι
  set d : ι → 𝓞 K ⧸ extP K 𝔭 ^ 1 := fun i =>
    Ideal.Quotient.mk (extP K 𝔭 ^ 1) (algebraMap (𝓞 F) (𝓞 K) (b i)) with hd
  let u : Fin n → 𝓞 K := fun i => algebraMap (𝓞 F) (𝓞 K) (b (e.symm i))
  have hD : (diagonal u).map (Ideal.Quotient.mk (extP K 𝔭 ^ 1)) =
      Matrix.reindex e e (diagonal d) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [u, d, Matrix.reindex_apply]
    · have hij' : e.symm i ≠ e.symm j := fun h => hij (e.symm.injective h)
      simp [u, d, Matrix.reindex_apply, Matrix.diagonal_apply_ne _ hij,
        Matrix.diagonal_apply_ne _ hij']
  have hcard : Nat.card {γ : Matrix ι ι (𝓞 K ⧸ extP K 𝔭 ^ 1) // γᴴ * diagonal d * γ = diagonal d} =
      Nat.card {X : Matrix (Fin n) (Fin n) (𝓞 K ⧸ extP K 𝔭 ^ 1) //
        Xᴴ * Matrix.reindex e e (diagonal d) * X = Matrix.reindex e e (diagonal d)} := by
    refine Nat.card_congr (Equiv.subtypeEquiv (Matrix.reindex e e) fun γ => ?_)
    simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
    refine ⟨fun h => by rw [h], fun h => (Matrix.reindex e e).injective ?_⟩
    simpa only [Matrix.reindex_apply] using h
  have hu : ∀ i, Formalism.HermitianLattices.Ext.L3.conjO K (u i) = u i := fun i => by
    apply IsFractionRing.injective (𝓞 K) K
    rw [Formalism.HermitianLattices.Ext.L3.BallB.algebraMap_conjO, (Fact.out : IsFixF K F)]
    refine ⟨((b (e.symm i) : 𝓞 F) : F), ?_⟩
    show algebraMap F K (algebraMap (𝓞 F) F (b (e.symm i))) = _
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K]
  have hunit : ∀ i, Ideal.span {u i} ⊔ extP K 𝔭 = ⊤ := fun i => by
    have hF : Ideal.span {b (e.symm i)} ⊔ 𝔭 = ⊤ := by
      refine h𝔭.1.2 _ (lt_of_le_of_ne le_sup_right fun h => hb (e.symm i) ?_)
      rw [h]
      exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
    have h2 := congrArg (Ideal.map (algebraMap (𝓞 F) (𝓞 K))) hF
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, Ideal.map_top] at h2
    exact h2
  rw [hcard, ← hD]
  exact Formalism.HermitianLattices.Ext.L3.IsotropicCounts.isoCount_one hK h𝔭 u hu hunit

/- English proof (translation)
Rewrite using `[Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add, Matrix.fromBlocks_add, ← Matrix.fromBlocks_zero, Matrix.fromBlocks_inj]`. Simplify using `only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2, -, h4⟩`. Use `⟨h1, ?_, h4⟩` and prove the remaining obligations.

Establish `hR : Rᴴ = -(Q + Pᴴ * Du * Q)`. Rewrite using `[eq_neg_iff_add_eq_zero, ← h2]`. Normalize the expressions using the abelian group laws. Rewrite using `[← Matrix.conjTranspose_conjTranspose R, hR, Matrix.conjTranspose_neg]`. Introduce and unpack `⟨h1, rfl, h4⟩`.

Use `⟨h1, ?_, ?_, h4⟩` and prove the remaining obligations. Rewrite using `[Matrix.conjTranspose_neg, Matrix.conjTranspose_conjTranspose]`. Normalize the expressions using the abelian group laws. Rewrite using `[Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hDu, Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc]`. Normalize the expressions using the abelian group laws.
-/
private theorem fromBlocks_cayley_eq_zero_iff {A : Type*} [CommRing A] [StarRing A] {u z : Type*} [Fintype u] [Fintype z]
    [DecidableEq u] [DecidableEq z] (Du : Matrix u u A) (hDu : Duᴴ = Du) (P : Matrix u u A)
    (Q : Matrix u z A) (R : Matrix z u A) (S : Matrix z z A) :
    Matrix.fromBlocks P Q R S + (Matrix.fromBlocks P Q R S)ᴴ +
        (Matrix.fromBlocks P Q R S)ᴴ * Matrix.fromBlocks Du 0 0 0 * Matrix.fromBlocks P Q R S = 0 ↔
      P + Pᴴ + Pᴴ * Du * P = 0 ∧ R = -(Q + Pᴴ * Du * Q)ᴴ ∧ S + Sᴴ + Qᴴ * Du * Q = 0 := by
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_add, Matrix.fromBlocks_add, ← Matrix.fromBlocks_zero, Matrix.fromBlocks_inj]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  constructor
  · rintro ⟨h1, h2, -, h4⟩
    refine ⟨h1, ?_, h4⟩
    have hR : Rᴴ = -(Q + Pᴴ * Du * Q) := by
      rw [eq_neg_iff_add_eq_zero, ← h2]; abel
    rw [← Matrix.conjTranspose_conjTranspose R, hR, Matrix.conjTranspose_neg]
  · rintro ⟨h1, rfl, h4⟩
    refine ⟨h1, ?_, ?_, h4⟩
    · rw [Matrix.conjTranspose_neg, Matrix.conjTranspose_conjTranspose]; abel
    · rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hDu,
        Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc]
      abel

/- English proof (translation)
Establish `hse : star e = -e` using `Formalism.HermitianLattices.Ext.L3.HermitianSublattices.star_inv_eq_neg he`. Establish `hte : θ * e + star θ * -e = 1` using `by rw [← he]; ring`. Establish `hS0 : ∀ Q : Matrix u z A, (θ * e) • (-(Qᴴ * Du * Q)) + ((θ * e) • (-(Qᴴ * Du * Q)))ᴴ = -(Qᴴ * Du * Q)`. Introduce `Q`. Establish `hM : (-(Qᴴ * Du * Q))ᴴ = -(Qᴴ * Du * Q)`.

Rewrite using `[Matrix.conjTranspose_neg, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hDu, Matrix.mul_assoc]`. Rewrite using `[Matrix.conjTranspose_smul, hM, star_mul', hse, ← add_smul, hte, one_smul]`. Establish `key : ∀ (Q : Matrix u z A) (S : Matrix z z A), (S - (θ * e) • (-(Qᴴ * Du * Q))) + (S - (θ * e) • (-(Qᴴ * Du * Q)))ᴴ = S + Sᴴ + Qᴴ * Du * Q`. Introduce `Q S`. Rewrite using `[Matrix.conjTranspose_sub]`.

Rewrite using `[show S - (θ * e) • (-(Qᴴ * Du * Q)) + (Sᴴ - ((θ * e) • (-(Qᴴ * Du * Q)))ᴴ) = S + Sᴴ - ((θ * e) • (-(Qᴴ * Du * Q)) + ((θ * e) • (-(Qᴴ * Du * Q)))ᴴ) by abel, hS0 Q, sub_neg_eq_add]`. Set `eqv : {Y : Matrix (u ⊕ z) (u ⊕ z) A // Y + Yᴴ + Yᴴ * Matrix.fromBlocks Du 0 0 0 * Y = 0} ≃ ({P : Matrix u u A // P + Pᴴ + Pᴴ * Du * P = 0} × Matrix u z A) × {S : Matrix z z A // S + Sᴴ = 0}` to `{ toFun := fun Y =>`. Establish `h` using `(fromBlocks_cayley_eq_zero_iff Du hDu _ _ _ _).mp (by rw [Matrix.fromBlocks_toBlocks]; exact Y.2)`. Use the proof step `((⟨Y.1.toBlocks₁₁, h.1⟩, Y.1.toBlocks₁₂), ⟨Y.1.toBlocks₂₂ - (θ * e) • (-(Y.1.toBlocks₁₂ᴴ * Du * Y.1.toBlocks₁₂)), by rw [key]; exact h.2.2⟩)`. Use `invFun := fun x => ⟨Matrix.fromBlocks x.1.1.1 x.1.2 (-(x.1.2 + x.1.1.1ᴴ * Du * x.1.2)ᴴ) (x.2.1 + (θ * e) • (-(x.1.2ᴴ * Du * x.1.2))), (fromBlocks_cayley_eq_zero_iff Du hDu _ _ _ _).mpr ⟨x.1.1.2, rfl, by`.

Establish `h` using `key x.1.2 (x.2.1 + (θ * e) • (-(x.1.2ᴴ * Du * x.1.2)))`. Rewrite `h` using `[add_sub_cancel_right]`. Rewrite using `[← h]`. Conclude with `x.2.2⟩⟩`. Use `left_inv := fun Y => by`.

Establish `h` using `(fromBlocks_cayley_eq_zero_iff Du hDu _ _ _ _).mp (by rw [Matrix.fromBlocks_toBlocks]; exact Y.2)`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [sub_add_cancel]`. Rewrite using `[← h.2.1, Matrix.fromBlocks_toBlocks]`. Use `right_inv := fun x => by`.

Use `ext`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using `}`. Rewrite using `[Nat.card_congr eqv, Nat.card_prod, Nat.card_prod]`.
-/
private theorem card_fromBlocks_cayley_eq_mul {A : Type*} [CommRing A] [StarRing A] [Finite A] {u z : Type*} [Fintype u]
    [Fintype z] [DecidableEq u] [DecidableEq z] (Du : Matrix u u A) (hDu : Duᴴ = Du) {θ e : A}
    (he : (θ - star θ) * e = 1) :
    Nat.card {Y : Matrix (u ⊕ z) (u ⊕ z) A // Y + Yᴴ + Yᴴ * Matrix.fromBlocks Du 0 0 0 * Y = 0} =
      Nat.card {P : Matrix u u A // P + Pᴴ + Pᴴ * Du * P = 0} * Nat.card (Matrix u z A) *
        Nat.card {S : Matrix z z A // S + Sᴴ = 0} := by
  have hse : star e = -e := Formalism.HermitianLattices.Ext.L3.HermitianSublattices.star_inv_eq_neg he
  have hte : θ * e + star θ * -e = 1 := by rw [← he]; ring

  have hS0 : ∀ Q : Matrix u z A, (θ * e) • (-(Qᴴ * Du * Q)) + ((θ * e) • (-(Qᴴ * Du * Q)))ᴴ =
      -(Qᴴ * Du * Q) := by
    intro Q
    have hM : (-(Qᴴ * Du * Q))ᴴ = -(Qᴴ * Du * Q) := by
      rw [Matrix.conjTranspose_neg, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, hDu, Matrix.mul_assoc]
    rw [Matrix.conjTranspose_smul, hM, star_mul', hse, ← add_smul, hte, one_smul]
  have key : ∀ (Q : Matrix u z A) (S : Matrix z z A),
      (S - (θ * e) • (-(Qᴴ * Du * Q))) + (S - (θ * e) • (-(Qᴴ * Du * Q)))ᴴ =
        S + Sᴴ + Qᴴ * Du * Q := by
    intro Q S
    rw [Matrix.conjTranspose_sub]
    rw [show S - (θ * e) • (-(Qᴴ * Du * Q)) + (Sᴴ - ((θ * e) • (-(Qᴴ * Du * Q)))ᴴ) =
      S + Sᴴ - ((θ * e) • (-(Qᴴ * Du * Q)) + ((θ * e) • (-(Qᴴ * Du * Q)))ᴴ) by abel, hS0 Q,
      sub_neg_eq_add]
  let eqv : {Y : Matrix (u ⊕ z) (u ⊕ z) A // Y + Yᴴ + Yᴴ * Matrix.fromBlocks Du 0 0 0 * Y = 0} ≃
      ({P : Matrix u u A // P + Pᴴ + Pᴴ * Du * P = 0} × Matrix u z A) ×
        {S : Matrix z z A // S + Sᴴ = 0} :=
    { toFun := fun Y =>
        have h := (fromBlocks_cayley_eq_zero_iff Du hDu _ _ _ _).mp (by rw [Matrix.fromBlocks_toBlocks]; exact Y.2)
        ((⟨Y.1.toBlocks₁₁, h.1⟩, Y.1.toBlocks₁₂),
          ⟨Y.1.toBlocks₂₂ - (θ * e) • (-(Y.1.toBlocks₁₂ᴴ * Du * Y.1.toBlocks₁₂)),
            by rw [key]; exact h.2.2⟩)
      invFun := fun x =>
        ⟨Matrix.fromBlocks x.1.1.1 x.1.2 (-(x.1.2 + x.1.1.1ᴴ * Du * x.1.2)ᴴ)
            (x.2.1 + (θ * e) • (-(x.1.2ᴴ * Du * x.1.2))),
          (fromBlocks_cayley_eq_zero_iff Du hDu _ _ _ _).mpr ⟨x.1.1.2, rfl, by
            have h := key x.1.2 (x.2.1 + (θ * e) • (-(x.1.2ᴴ * Du * x.1.2)))
            rw [add_sub_cancel_right] at h
            rw [← h]; exact x.2.2⟩⟩
      left_inv := fun Y => by
        have h := (fromBlocks_cayley_eq_zero_iff Du hDu _ _ _ _).mp (by rw [Matrix.fromBlocks_toBlocks]; exact Y.2)
        apply Subtype.ext
        simp only [sub_add_cancel]
        rw [← h.2.1, Matrix.fromBlocks_toBlocks]
      right_inv := fun x => by
        ext
        · simp
        · simp
        · simp }
  rw [Nat.card_congr eqv, Nat.card_prod, Nat.card_prod]

/- English proof (translation)
Establish `hse : star e = -e` using `Formalism.HermitianLattices.Ext.L3.HermitianSublattices.star_inv_eq_neg he`. Establish `hst : star (θ - star θ) = -(θ - star θ)` using `by rw [star_sub, star_star]; ring`. Establish `he' : e * (θ - star θ) = 1` using `by rw [mul_comm]; exact he`. Conclude with `Nat.card_congr { toFun := fun S => ⟨(θ - star θ) • S.1, by`. Establish `hS : S.1ᴴ = -S.1` using `eq_neg_of_add_eq_zero_right S.2`.

Rewrite using `[Matrix.conjTranspose_smul, hst, hS, neg_smul, smul_neg, neg_neg]⟩`. Use `invFun := fun M => ⟨e • M.1, by`. Rewrite using `[Matrix.conjTranspose_smul, hse, M.2, neg_smul, add_neg_cancel]⟩`. Use `left_inv := fun S => Subtype.ext (by simp only [smul_smul, he', one_smul])`. Use `right_inv := fun M => Subtype.ext (by simp only [smul_smul, he, one_smul]) }`.
-/
private theorem card_skewHermitian_eq_card_hermitian {A : Type*} [CommRing A] [StarRing A] {z : Type*} {θ e : A}
    (he : (θ - star θ) * e = 1) :
    Nat.card {S : Matrix z z A // S + Sᴴ = 0} = Nat.card {M : Matrix z z A // Mᴴ = M} := by
  have hse : star e = -e := Formalism.HermitianLattices.Ext.L3.HermitianSublattices.star_inv_eq_neg he
  have hst : star (θ - star θ) = -(θ - star θ) := by rw [star_sub, star_star]; ring
  have he' : e * (θ - star θ) = 1 := by rw [mul_comm]; exact he
  exact Nat.card_congr
    { toFun := fun S => ⟨(θ - star θ) • S.1, by
        have hS : S.1ᴴ = -S.1 := eq_neg_of_add_eq_zero_right S.2
        rw [Matrix.conjTranspose_smul, hst, hS, neg_smul, smul_neg, neg_neg]⟩
      invFun := fun M => ⟨e • M.1, by
        rw [Matrix.conjTranspose_smul, hse, M.2, neg_smul, add_neg_cancel]⟩
      left_inv := fun S => Subtype.ext (by simp only [smul_smul, he', one_smul])
      right_inv := fun M => Subtype.ext (by simp only [smul_smul, he, one_smul]) }

/- English proof (translation)
Establish `iden : ∀ P : Matrix u u A, (1 + P * Du)ᴴ * Du * (1 + P * Du) = Du + Du * (P + Pᴴ + Pᴴ * Du * P) * Du`. Introduce `P`. Rewrite using `[Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_mul, hDu]`. Use `noncomm_ring`. Establish `cancel : ∀ X : Matrix u u A, Dv * (Du * X * Du) * Dv = X`.

Introduce `X`. Rewrite using `[← Matrix.mul_assoc Dv (Du * X) Du, ← Matrix.mul_assoc Dv Du X, hvu, Matrix.one_mul, Matrix.mul_assoc X Du Dv, huv, Matrix.mul_one]`. Conclude with `Nat.card_congr { toFun := fun P => ⟨1 + P.1 * Du, by rw [iden, P.2, Matrix.mul_zero, Matrix.zero_mul, add_zero]⟩ invFun := fun γ => ⟨(γ.1 - 1) * Dv, by`. Establish `h1 : 1 + (γ.1 - 1) * Dv * Du = γ.1`. Rewrite using `[Matrix.mul_assoc, hvu, Matrix.mul_one]`.

Normalize the expressions using the abelian group laws. Establish `h2` using `iden ((γ.1 - 1) * Dv)`. Rewrite `h2` using `[h1, γ.2]`. Establish `h3 : Du * ((γ.1 - 1) * Dv + ((γ.1 - 1) * Dv)ᴴ + ((γ.1 - 1) * Dv)ᴴ * Du * ((γ.1 - 1) * Dv)) * Du = 0`. Use `congrArg (fun X => X - Du) h2` as an intermediate fact.

Simplify using `only [sub_self, add_sub_cancel_left] at this`. Conclude with `this.symm`. Establish `h4` using `cancel ((γ.1 - 1) * Dv + ((γ.1 - 1) * Dv)ᴴ + ((γ.1 - 1) * Dv)ᴴ * Du * ((γ.1 - 1) * Dv))`. Rewrite `h4` using `[h3, Matrix.mul_zero, Matrix.zero_mul]`. Conclude with `h4.symm⟩`.

Use `left_inv := fun P => Subtype.ext (by`. Simplify using `only [add_sub_cancel_left, Matrix.mul_assoc, huv, Matrix.mul_one])`. Use `right_inv := fun γ => Subtype.ext (by`. Simplify using `only`. Rewrite using `[Matrix.mul_assoc, hvu, Matrix.mul_one]`.

Use the proof step `abel) }`.
-/
private theorem exists_UJ_umat_eq_of_inUJ {A : Type*} [CommRing A] [StarRing A] {u : Type*} [Fintype u] [DecidableEq u]
    (Du Dv : Matrix u u A) (hDu : Duᴴ = Du) (huv : Du * Dv = 1) (hvu : Dv * Du = 1) :
    Nat.card {P : Matrix u u A // P + Pᴴ + Pᴴ * Du * P = 0} =
      Nat.card {γ : Matrix u u A // γᴴ * Du * γ = Du} := by
  have iden : ∀ P : Matrix u u A, (1 + P * Du)ᴴ * Du * (1 + P * Du) =
      Du + Du * (P + Pᴴ + Pᴴ * Du * P) * Du := by
    intro P
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_mul, hDu]
    noncomm_ring
  have cancel : ∀ X : Matrix u u A, Dv * (Du * X * Du) * Dv = X := by
    intro X
    rw [← Matrix.mul_assoc Dv (Du * X) Du, ← Matrix.mul_assoc Dv Du X, hvu, Matrix.one_mul,
      Matrix.mul_assoc X Du Dv, huv, Matrix.mul_one]
  exact Nat.card_congr
    { toFun := fun P => ⟨1 + P.1 * Du, by rw [iden, P.2, Matrix.mul_zero, Matrix.zero_mul, add_zero]⟩
      invFun := fun γ => ⟨(γ.1 - 1) * Dv, by
        have h1 : 1 + (γ.1 - 1) * Dv * Du = γ.1 := by
          rw [Matrix.mul_assoc, hvu, Matrix.mul_one]; abel
        have h2 := iden ((γ.1 - 1) * Dv)
        rw [h1, γ.2] at h2
        have h3 : Du * ((γ.1 - 1) * Dv + ((γ.1 - 1) * Dv)ᴴ + ((γ.1 - 1) * Dv)ᴴ * Du * ((γ.1 - 1) * Dv)) * Du = 0 := by
          have := congrArg (fun X => X - Du) h2
          simp only [sub_self, add_sub_cancel_left] at this
          exact this.symm
        have h4 := cancel ((γ.1 - 1) * Dv + ((γ.1 - 1) * Dv)ᴴ + ((γ.1 - 1) * Dv)ᴴ * Du * ((γ.1 - 1) * Dv))
        rw [h3, Matrix.mul_zero, Matrix.zero_mul] at h4
        exact h4.symm⟩
      left_inv := fun P => Subtype.ext (by
        simp only [add_sub_cancel_left, Matrix.mul_assoc, huv, Matrix.mul_one])
      right_inv := fun γ => Subtype.ext (by
        simp only
        rw [Matrix.mul_assoc, hvu, Matrix.mul_one]; abel) }

/- English proof (translation)
Introduce `K F _ _ _ _ _ _ _ hK 𝔭 h𝔭 m a ha`. Use `haveI := finite_quot (K := K) h𝔭 1`. Use `haveI : Subsingleton (𝓞 K ⧸ extP K 𝔭 ^ 0) := Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.one_eq_top])`. Take `⟨θ, e, he⟩` from `exists_unit_quot hK h𝔭 1`. Establish `hzero : ∀ i, a i ∈ 𝔭 → Ideal.Quotient.mk (extP K 𝔭 ^ 1) (algebraMap (𝓞 F) (𝓞 K) (a i)) = 0`.

Introduce `i hi`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, pow_one]`. Conclude with `Ideal.mem_map_of_mem _ hi`. Establish `hinv : ∀ i : {i : Fin m // a i ∉ 𝔭}, ∃ v : (𝓞 K ⧸ extP K 𝔭 ^ 1), Ideal.Quotient.mk (extP K 𝔭 ^ 1) (algebraMap (𝓞 F) (𝓞 K) (a i.1)) * v = 1`. Introduce `i`.

Take `⟨y, j, hj, hy⟩` from `h𝔭.exists_inv i.2`. Use `⟨Ideal.Quotient.mk (extP K 𝔭 ^ 1) (algebraMap (𝓞 F) (𝓞 K) y), ?_⟩` and prove the remaining obligations. Establish `h1` using `congrArg (fun x => Ideal.Quotient.mk (extP K 𝔭 ^ 1) (algebraMap (𝓞 F) (𝓞 K) x)) hy`. Simplify using `only [map_add, map_mul, map_one] at h1`. Establish `h2 : Ideal.Quotient.mk (extP K 𝔭 ^ 1) (algebraMap (𝓞 F) (𝓞 K) j) = 0`.

Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, pow_one]`. Conclude with `Ideal.mem_map_of_mem _ hj`. Rewrite `h1` using `[h2, add_zero]`. Conclude with `(mul_comm _ _).trans h1`. Use `choose dv hdv using hinv`.

Take `⟨Du, hDu_def⟩ : ∃ Du : Matrix {i : Fin m // a i ∉ 𝔭} {i : Fin m // a i ∉ 𝔭} (𝓞 K ⧸ extP K 𝔭 ^ 1), Du = Matrix.diagonal (fun i => Ideal.Quotient.mk (extP K 𝔭 ^ 1) (algebraMap (𝓞 F) (𝓞 K) (a i.1)))` from `⟨_, rfl⟩`. Establish `hDuh : Duᴴ = Du`. Rewrite using `[hDu_def, Matrix.diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Rewrite using `[Pi.star_apply, star_mk, starO_ι]`. Establish `huv : Du * Matrix.diagonal dv = 1`. Rewrite using `[hDu_def, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Conclude with `hdv i`. Establish `hvu : Matrix.diagonal dv * Du = 1`. Rewrite using `[hDu_def, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Rewrite using `[mul_comm]`. Conclude with `hdv i`. Set `e' : Fin m ≃ {i : Fin m // a i ∉ 𝔭} ⊕ {i : Fin m // ¬ a i ∉ 𝔭}` to `(Equiv.sumCompl (fun i => a i ∉ 𝔭)).symm`. Establish `hHD : Matrix.fromBlocks Du 0 0 0 = Matrix.reindex e' e' (diagQ K 𝔭 1 a)`. Rewrite using `[hDu_def]`.

Use extensionality with `(i | i) (j | j)`. Simplify using `[e', diagQ, Matrix.diagonal_apply, Subtype.ext_iff]`. Establish `hij : i.1 ≠ j.1` using `fun h => j.2 (h ▸ i.2)`. Simplify using `[e', diagQ, Matrix.diagonal_apply, hij]`. Establish `hij : i.1 ≠ j.1` using `fun h => i.2 (h ▸ j.2)`.

Simplify using `[e', diagQ, Matrix.diagonal_apply, hij]`. Establish `hi : a i.1 ∈ 𝔭` using `not_not.mp i.2`. Simplify using `[e', diagQ, Matrix.diagonal_apply, hzero _ hi]`. Use `first`. Consider the case `exact fun _ => (hzero _ hi).symm`.

Consider the case `(intro _; rw [IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) (𝓞 K ⧸ extP K 𝔭 ^ 1)]; exact (hzero _ hi).symm)`. Establish `h6 : Nat.card {Y : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ 1) // phiQ K 𝔭 1 a Y = 0} = Nat.card {Y : Matrix ({i : Fin m // a i ∉ 𝔭} ⊕ {i : Fin m // ¬ a i ∉ 𝔭}) ({i : Fin m // a i ∉ 𝔭} ⊕ {i : Fin m // ¬ a i ∉ 𝔭}) (𝓞 K ⧸ extP K 𝔭 ^ 1) // Y + Yᴴ + Yᴴ * Matrix.fromBlocks Du 0 0 0 * …`. Use `Nat.card_congr (Equiv.subtypeEquiv (Matrix.reindex e' e') fun Y => ?_)` and prove the remaining obligations. Establish `hre : Matrix.reindex e' e' Y + (Matrix.reindex e' e' Y)ᴴ + (Matrix.reindex e' e' Y)ᴴ * Matrix.reindex e' e' (diagQ K 𝔭 1 a) * Matrix.reindex e' e' Y = Matrix.reindex e' e' (phiQ K 𝔭 1 a Y)`. Unfold `phiQ`.

Simplify using `only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]`. Both sides reduce to the same expression. Rewrite using `[hHD, hre]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Rewrite using `[h]`. Simplify using the standard rewrite rules. Introduce `h`. Apply `(Matrix.reindex e' e').injective` to reduce the goal to its premises. Rewrite using `[h]`.

Simplify using the standard rewrite rules. Establish `hU` using `card_U_diag hK h𝔭 (ι := {i : Fin m // a i ∉ 𝔭}) (fun i => a i.1) (fun i => i.2)`. Rewrite `hU` using `[← hDu_def]`. Establish `hR1 : Nat.card (𝓞 K ⧸ extP K 𝔭 ^ 1) = Ideal.absNorm 𝔭 ^ 2`. Establish `h` using `Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.card_ker_piQ hK (Fact.out) h𝔭 0`.

Establish `htop : RingHom.ker (piQ K 𝔭 0) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `x _`. Rewrite using `[RingHom.mem_ker]`. Conclude with `Subsingleton.elim _ _`.

Rewrite `h` using `[htop]`. Rewrite using `[← h]`. Conclude with `(Nat.card_congr (Equiv.subtypeUnivEquiv (fun x => Submodule.mem_top))).symm`. Establish `hMat : Nat.card (Matrix {i : Fin m // a i ∉ 𝔭} {i : Fin m // ¬ a i ∉ 𝔭} (𝓞 K ⧸ extP K 𝔭 ^ 1)) = ((Ideal.absNorm 𝔭 ^ 2) ^ Fintype.card {i : Fin m // ¬ a i ∉ 𝔭}) ^ Fintype.card {i : Fin m // a i ∉ 𝔭}`. Rewrite using `[show Nat.card (Matrix {i : Fin m // a i ∉ 𝔭} {i : Fin m // ¬ a i ∉ 𝔭} (𝓞 K ⧸ extP K 𝔭 ^ 1)) = Nat.card ({i : Fin m // a i ∉ 𝔭} → {i : Fin m // ¬ a i ∉ 𝔭} → (𝓞 K ⧸ extP K 𝔭 ^ 1)) from rfl, Nat.card_fun, Nat.card_fun, hR1, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]`.

Establish `hherm : Nat.card {M : Matrix {i : Fin m // ¬ a i ∉ 𝔭} {i : Fin m // ¬ a i ∉ 𝔭} (𝓞 K ⧸ extP K 𝔭 ^ 1) // Mᴴ = M} = Ideal.absNorm 𝔭 ^ (Fintype.card {i : Fin m // ¬ a i ∉ 𝔭} * Fintype.card {i : Fin m // ¬ a i ∉ 𝔭})`. Rewrite using `[← Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms.card_hermSub (r := {i : Fin m // ¬ a i ∉ 𝔭}) hK h𝔭 0]`. Conclude with `Nat.card_congr { toFun := fun M => ⟨M.1, Formalism.HermitianLattices.Ext.L3.HermitianSublattices.mem_hermSub.mpr ⟨M.2, fun _ _ => by`. Rewrite using `[RingHom.mem_ker]`. Conclude with `Subsingleton.elim _ _⟩⟩`.

Use `invFun := fun S => ⟨S.1, (Formalism.HermitianLattices.Ext.L3.HermitianSublattices.mem_hermSub.mp S.2).1⟩`. Use `left_inv := fun _ => rfl`. Use `right_inv := fun _ => rfl }`. Establish `hc : cJof 𝔭 a = Fintype.card {i : Fin m // ¬ a i ∉ 𝔭}`. Unfold `cJof`.

Rewrite using `[Fintype.card_subtype]`. Conclude with `congrArg Finset.card (Finset.filter_congr (fun i _ => by`. Rewrite using `[not_not]`. Conclude with `vF_ne_zero_iff h𝔭 (ha i)))`. Establish `hm : Fintype.card {i : Fin m // a i ∉ 𝔭} + Fintype.card {i : Fin m // ¬ a i ∉ 𝔭} = m`.

Rewrite using `[← Fintype.card_sum, Fintype.card_congr e'.symm, Fintype.card_fin]`. Rewrite using `[h6, card_fromBlocks_cayley_eq_mul Du hDuh he, exists_UJ_umat_eq_of_inUJ Du (Matrix.diagonal dv) hDuh huv hvu, card_skewHermitian_eq_card_hermitian he, hherm, hMat]`. Use `push_cast`. Rewrite using `[hU, hc, show m - Fintype.card {i : Fin m // ¬ a i ∉ 𝔭} = Fintype.card {i : Fin m // a i ∉ 𝔭} by omega, show m ^ 2 = (Fintype.card {i : Fin m // a i ∉ 𝔭} + Fintype.card {i : Fin m // ¬ a i ∉ 𝔭}) ^ 2 by rw [hm]]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem phi_mod_p_holds : PhiModP := by
  intro K F _ _ _ _ _ _ _ hK 𝔭 h𝔭 m a ha
  classical
  haveI := finite_quot (K := K) h𝔭 1
  haveI : Subsingleton (𝓞 K ⧸ extP K 𝔭 ^ 0) :=
    Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.one_eq_top])
  obtain ⟨θ, e, he⟩ := exists_unit_quot hK h𝔭 1

  have hzero : ∀ i, a i ∈ 𝔭 →
      Ideal.Quotient.mk (extP K 𝔭 ^ 1) (algebraMap (𝓞 F) (𝓞 K) (a i)) = 0 := by
    intro i hi
    rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]
    exact Ideal.mem_map_of_mem _ hi
  have hinv : ∀ i : {i : Fin m // a i ∉ 𝔭}, ∃ v : (𝓞 K ⧸ extP K 𝔭 ^ 1),
      Ideal.Quotient.mk (extP K 𝔭 ^ 1) (algebraMap (𝓞 F) (𝓞 K) (a i.1)) * v = 1 := by
    intro i
    obtain ⟨y, j, hj, hy⟩ := h𝔭.exists_inv i.2
    refine ⟨Ideal.Quotient.mk (extP K 𝔭 ^ 1) (algebraMap (𝓞 F) (𝓞 K) y), ?_⟩
    have h1 := congrArg (fun x => Ideal.Quotient.mk (extP K 𝔭 ^ 1) (algebraMap (𝓞 F) (𝓞 K) x)) hy
    simp only [map_add, map_mul, map_one] at h1
    have h2 : Ideal.Quotient.mk (extP K 𝔭 ^ 1) (algebraMap (𝓞 F) (𝓞 K) j) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]
      exact Ideal.mem_map_of_mem _ hj
    rw [h2, add_zero] at h1
    exact (mul_comm _ _).trans h1
  choose dv hdv using hinv
  obtain ⟨Du, hDu_def⟩ : ∃ Du : Matrix {i : Fin m // a i ∉ 𝔭} {i : Fin m // a i ∉ 𝔭} (𝓞 K ⧸ extP K 𝔭 ^ 1),
      Du = Matrix.diagonal (fun i => Ideal.Quotient.mk (extP K 𝔭 ^ 1) (algebraMap (𝓞 F) (𝓞 K) (a i.1))) :=
    ⟨_, rfl⟩
  have hDuh : Duᴴ = Du := by
    rw [hDu_def, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    rw [Pi.star_apply, star_mk, starO_ι]
  have huv : Du * Matrix.diagonal dv = 1 := by
    rw [hDu_def, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact hdv i
  have hvu : Matrix.diagonal dv * Du = 1 := by
    rw [hDu_def, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [mul_comm]
    exact hdv i

  let e' : Fin m ≃ {i : Fin m // a i ∉ 𝔭} ⊕ {i : Fin m // ¬ a i ∉ 𝔭} := (Equiv.sumCompl (fun i => a i ∉ 𝔭)).symm
  have hHD : Matrix.fromBlocks Du 0 0 0 = Matrix.reindex e' e' (diagQ K 𝔭 1 a) := by
    rw [hDu_def]
    ext (i | i) (j | j)
    · simp [e', diagQ, Matrix.diagonal_apply, Subtype.ext_iff]
    · have hij : i.1 ≠ j.1 := fun h => j.2 (h ▸ i.2)
      simp [e', diagQ, Matrix.diagonal_apply, hij]
    · have hij : i.1 ≠ j.1 := fun h => i.2 (h ▸ j.2)
      simp [e', diagQ, Matrix.diagonal_apply, hij]
    · have hi : a i.1 ∈ 𝔭 := not_not.mp i.2
      simp [e', diagQ, Matrix.diagonal_apply, hzero _ hi]
      first
      | exact fun _ => (hzero _ hi).symm
      | (intro _; rw [IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) (𝓞 K ⧸ extP K 𝔭 ^ 1)]; exact (hzero _ hi).symm)
  have h6 : Nat.card {Y : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ 1) // phiQ K 𝔭 1 a Y = 0} =
      Nat.card {Y : Matrix ({i : Fin m // a i ∉ 𝔭} ⊕ {i : Fin m // ¬ a i ∉ 𝔭}) ({i : Fin m // a i ∉ 𝔭} ⊕ {i : Fin m // ¬ a i ∉ 𝔭}) (𝓞 K ⧸ extP K 𝔭 ^ 1) //
        Y + Yᴴ + Yᴴ * Matrix.fromBlocks Du 0 0 0 * Y = 0} := by
    refine Nat.card_congr (Equiv.subtypeEquiv (Matrix.reindex e' e') fun Y => ?_)
    have hre : Matrix.reindex e' e' Y + (Matrix.reindex e' e' Y)ᴴ +
        (Matrix.reindex e' e' Y)ᴴ * Matrix.reindex e' e' (diagQ K 𝔭 1 a) * Matrix.reindex e' e' Y =
        Matrix.reindex e' e' (phiQ K 𝔭 1 a Y) := by
      unfold phiQ
      simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
      rfl
    rw [hHD, hre]
    constructor
    · intro h
      rw [h]
      simp
    · intro h
      apply (Matrix.reindex e' e').injective
      rw [h]
      simp

  have hU := card_U_diag hK h𝔭 (ι := {i : Fin m // a i ∉ 𝔭}) (fun i => a i.1) (fun i => i.2)
  rw [← hDu_def] at hU
  have hR1 : Nat.card (𝓞 K ⧸ extP K 𝔭 ^ 1) = Ideal.absNorm 𝔭 ^ 2 := by
    have h := Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.card_ker_piQ hK (Fact.out) h𝔭 0
    have htop : RingHom.ker (piQ K 𝔭 0) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [RingHom.mem_ker]
      exact Subsingleton.elim _ _
    rw [htop] at h
    rw [← h]
    exact (Nat.card_congr (Equiv.subtypeUnivEquiv (fun x => Submodule.mem_top))).symm
  have hMat : Nat.card (Matrix {i : Fin m // a i ∉ 𝔭} {i : Fin m // ¬ a i ∉ 𝔭} (𝓞 K ⧸ extP K 𝔭 ^ 1)) =
      ((Ideal.absNorm 𝔭 ^ 2) ^ Fintype.card {i : Fin m // ¬ a i ∉ 𝔭}) ^ Fintype.card {i : Fin m // a i ∉ 𝔭} := by
    rw [show Nat.card (Matrix {i : Fin m // a i ∉ 𝔭} {i : Fin m // ¬ a i ∉ 𝔭} (𝓞 K ⧸ extP K 𝔭 ^ 1)) = Nat.card ({i : Fin m // a i ∉ 𝔭} → {i : Fin m // ¬ a i ∉ 𝔭} → (𝓞 K ⧸ extP K 𝔭 ^ 1)) from rfl,
      Nat.card_fun, Nat.card_fun, hR1, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have hherm : Nat.card {M : Matrix {i : Fin m // ¬ a i ∉ 𝔭} {i : Fin m // ¬ a i ∉ 𝔭} (𝓞 K ⧸ extP K 𝔭 ^ 1) // Mᴴ = M} =
      Ideal.absNorm 𝔭 ^ (Fintype.card {i : Fin m // ¬ a i ∉ 𝔭} * Fintype.card {i : Fin m // ¬ a i ∉ 𝔭}) := by
    rw [← Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms.card_hermSub (r := {i : Fin m // ¬ a i ∉ 𝔭}) hK h𝔭 0]
    exact Nat.card_congr
      { toFun := fun M => ⟨M.1, Formalism.HermitianLattices.Ext.L3.HermitianSublattices.mem_hermSub.mpr ⟨M.2, fun _ _ => by
            rw [RingHom.mem_ker]; exact Subsingleton.elim _ _⟩⟩
        invFun := fun S => ⟨S.1, (Formalism.HermitianLattices.Ext.L3.HermitianSublattices.mem_hermSub.mp S.2).1⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hc : cJof 𝔭 a = Fintype.card {i : Fin m // ¬ a i ∉ 𝔭} := by
    unfold cJof
    rw [Fintype.card_subtype]
    exact congrArg Finset.card (Finset.filter_congr (fun i _ => by
      rw [not_not]; exact vF_ne_zero_iff h𝔭 (ha i)))
  have hm : Fintype.card {i : Fin m // a i ∉ 𝔭} + Fintype.card {i : Fin m // ¬ a i ∉ 𝔭} = m := by
    rw [← Fintype.card_sum, Fintype.card_congr e'.symm, Fintype.card_fin]
  rw [h6, card_fromBlocks_cayley_eq_mul Du hDuh he, exists_UJ_umat_eq_of_inUJ Du (Matrix.diagonal dv) hDuh huv hvu, card_skewHermitian_eq_card_hermitian he, hherm, hMat]
  push_cast
  rw [hU, hc, show m - Fintype.card {i : Fin m // ¬ a i ∉ 𝔭} = Fintype.card {i : Fin m // a i ∉ 𝔭} by omega,
    show m ^ 2 = (Fintype.card {i : Fin m // a i ∉ 𝔭} + Fintype.card {i : Fin m // ¬ a i ∉ 𝔭}) ^ 2 by rw [hm]]
  ring

/- English proof (translation)
The claim follows from `phiCount_of phi_mod_p_holds`.
-/
theorem phi_counting_holds : PhiCount := phiCount_of phi_mod_p_holds

end Formalism.L2.SG.Pf.LocalizedFibreSets
