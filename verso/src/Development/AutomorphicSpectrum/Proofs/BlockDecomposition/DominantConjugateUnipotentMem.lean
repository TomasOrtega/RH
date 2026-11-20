import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsStrictDom
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPermWOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemIwUIff
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow

noncomputable section

namespace GlobalTheory.CompanionTheory.SatPow

section Contr

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

/- English proof (translation)
Establish `ha' : Valued.v a ≠ 0` using `(Valuation.ne_zero_iff _).2 ha`. Establish `hb' : Valued.v b ≠ 0` using `(Valuation.ne_zero_iff _).2 hb`. Unfold `ordL at h`. Rewrite `h` using `[dif_neg ha', dif_neg hb']`. Establish `hle : WithZero.unzero hb' ≤ WithZero.unzero ha'`.

Rewrite using `[← Multiplicative.toAdd_le]`. Use linear arithmetic over natural numbers and integers. Use `WithZero.coe_le_coe.2 hle` as an intermediate fact. Rewrite `this` using `[WithZero.coe_unzero, WithZero.coe_unzero]`. Then use the resulting hypothesis.
-/
theorem val_le_of_ordL_lt {a b : L} (ha : a ≠ 0) (hb : b ≠ 0) (h : ordL a < ordL b) :
    Valued.v b ≤ Valued.v a := by
  have ha' : Valued.v a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  have hb' : Valued.v b ≠ 0 := (Valuation.ne_zero_iff _).2 hb
  unfold ordL at h
  rw [dif_neg ha', dif_neg hb'] at h
  have hle : WithZero.unzero hb' ≤ WithZero.unzero ha' := by
    rw [← Multiplicative.toAdd_le]; omega
  have := WithZero.coe_le_coe.2 hle
  rwa [WithZero.coe_unzero, WithZero.coe_unzero] at this

/- English proof (translation)
Use `set d : Fin n → L := fun i => (t : Matrix (Fin n) (Fin n) L) i i with hdef`. Establish `htd : (t : Matrix (Fin n) (Fin n) L) = Matrix.diagonal d`. Use extensionality with `a b`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality.

Simplify using `[hdef]`. Rewrite using `[Matrix.diagonal_apply_ne _ hab]`. Conclude with `ht a b hab`. Establish `hd0 : ∀ a, d a ≠ 0`. Introduce `a h0`.

Establish `hm : ((t : Matrix (Fin n) (Fin n) L) * ((t⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) a a = 1`. Rewrite using `[← Units.val_mul, mul_inv_cancel]`. Simplify using the standard rewrite rules. Rewrite `hm` using `[htd, Matrix.diagonal_mul, h0, zero_mul]`. Conclude with `zero_ne_one hm`.

Establish `hpow : ((t ^ k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal fun a => d a ^ k`. Rewrite using `[Units.val_pow_eq_pow_val, htd, Matrix.diagonal_pow]`. Both sides reduce to the same expression. Establish `hinv : (((t ^ k)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal fun a => (d a ^ k)⁻¹`. Use `Units.inv_eq_of_mul_eq_one_right ?_` and prove the remaining obligations.

Rewrite using `[hpow, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Conclude with `mul_inv_cancel₀ (pow_ne_zero _ (hd0 a))`. Rewrite using `[Units.val_mul, Units.val_mul, hpow, hinv, Matrix.mul_diagonal, Matrix.diagonal_mul]`.

Break down `lt_trichotomy i j with hij | hij | hij` into its components or cases. Establish `hle : Valued.v (d i) ≤ Valued.v (d j)` using `val_le_of_ordL_lt (hd0 j) (hd0 i) (hd i j hij)`. Establish `hb : Valued.v (d j) ^ k ≠ 0` using `pow_ne_zero _ ((Valuation.ne_zero_iff _).2 (hd0 j))`. Rewrite using `[map_mul, map_mul, map_inv₀, map_pow, map_pow]`. Combine the equalities or inequalities in the displayed calculation.

Substitute `hij` using the available equality. Rewrite using `[h3, mul_one, mul_inv_cancel₀ (pow_ne_zero _ (hd0 i)), map_one]`. Rewrite using `[h2 i j hij]`. Simplify using the standard rewrite rules.
-/
theorem conj_entries_le_one {t A : GL (Fin n) L} (ht : IsDiagM t) (hd : IsStrictDom t)
    (h1 : ∀ i j, Valued.v ((A : Matrix (Fin n) (Fin n) L) i j) ≤ 1)
    (h2 : ∀ i j, j < i → (A : Matrix (Fin n) (Fin n) L) i j = 0)
    (h3 : ∀ i, (A : Matrix (Fin n) (Fin n) L) i i = 1) (k : ℕ) (i j : Fin n) :
    Valued.v (((t ^ k * A * (t ^ k)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) ≤ 1 := by
  set d : Fin n → L := fun i => (t : Matrix (Fin n) (Fin n) L) i i with hdef
  have htd : (t : Matrix (Fin n) (Fin n) L) = Matrix.diagonal d := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp [hdef]
    · rw [Matrix.diagonal_apply_ne _ hab]; exact ht a b hab
  have hd0 : ∀ a, d a ≠ 0 := by
    intro a h0
    have hm : ((t : Matrix (Fin n) (Fin n) L) * ((t⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) a a = 1 := by
      rw [← Units.val_mul, mul_inv_cancel]; simp
    rw [htd, Matrix.diagonal_mul, h0, zero_mul] at hm
    exact zero_ne_one hm
  have hpow : ((t ^ k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal fun a => d a ^ k := by
    rw [Units.val_pow_eq_pow_val, htd, Matrix.diagonal_pow]
    rfl
  have hinv : (((t ^ k)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal fun a => (d a ^ k)⁻¹ := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hpow, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    exact mul_inv_cancel₀ (pow_ne_zero _ (hd0 a))
  rw [Units.val_mul, Units.val_mul, hpow, hinv, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases lt_trichotomy i j with hij | hij | hij
  · have hle : Valued.v (d i) ≤ Valued.v (d j) := val_le_of_ordL_lt (hd0 j) (hd0 i) (hd i j hij)
    have hb : Valued.v (d j) ^ k ≠ 0 := pow_ne_zero _ ((Valuation.ne_zero_iff _).2 (hd0 j))
    rw [map_mul, map_mul, map_inv₀, map_pow, map_pow]
    calc Valued.v (d i) ^ k * Valued.v ((A : Matrix (Fin n) (Fin n) L) i j) * (Valued.v (d j) ^ k)⁻¹
        ≤ Valued.v (d i) ^ k * 1 * (Valued.v (d j) ^ k)⁻¹ := by gcongr; exact h1 i j
      _ = Valued.v (d i) ^ k / Valued.v (d j) ^ k := by rw [mul_one, div_eq_mul_inv]
      _ ≤ 1 := (div_le_one₀ (zero_lt_iff.2 hb)).2 (pow_le_pow_left' hle k)
  · subst hij
    rw [h3, mul_one, mul_inv_cancel₀ (pow_ne_zero _ (hd0 i)), map_one]
  · rw [h2 i j hij]; simp

/- English proof (translation)
Introduce `L _ _ σ n t u ht hd hu hU k`. Establish `hinv` using `(GlobalTheory.LGrp.mem_GU_iff σ n (u : GL (Fin n) L)).1 u.2`. Establish `huGL : (u : GL (Fin n) L) ∈ IwGL L n` using `hu`. Establish `hU1 : ∀ i j, Valued.v (((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) ≤ 1` using `fun i j => GlobalTheory.CompanionTheory.KUFactsU.iwGL_entries huGL i j`. Establish `hV1 : ∀ i j, Valued.v ((((u : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) ≤ 1` using `fun i j => GlobalTheory.CompanionTheory.KUFactsU.iwGL_entries (inv_mem huGL) i j`.

Establish `hV2 : ∀ i j, j < i → (((u : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0`. Introduce `i j hji`. Rewrite using `[hinv, hU.1 _ _ (Fin.rev_lt_rev.2 hji), map_zero]`. Establish `hV3 : ∀ i, (((u : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = 1`. Introduce `i`.

Rewrite using `[hinv, hU.2, map_one]`. Establish `hmem : t ^ k * u * (t ^ k)⁻¹ ∈ (KU σ n : Set (GU σ n))`. Rewrite using `[IntPtsUnitary.coe_KU, Set.mem_preimage, IntPtsUnitary.coe_GLint]`. Use `⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations. Conclude with `conj_entries_le_one ht hd hU1 hU.1 hU.2 k i j`.

Establish `e : (((t ^ k * u * (t ^ k)⁻¹ : GU σ n) : GL (Fin n) L))⁻¹ = (t : GL (Fin n) L) ^ k * (u : GL (Fin n) L)⁻¹ * ((t : GL (Fin n) L) ^ k)⁻¹`. Simplify using `[mul_assoc]`. Rewrite using `[e]`. Conclude with `conj_entries_le_one ht hd hV1 hV2 hV3 k i j`. Conclude with `hmem`.
-/
theorem conj_unip_mem_KU : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ)
    (t u : GU σ n), IsDiagM (t : GL (Fin n) L) → IsStrictDom (t : GL (Fin n) L) → u ∈ IwU σ n → IsUnipU u →
      ∀ k : ℕ, t ^ k * u * (t ^ k)⁻¹ ∈ KU σ n := by
  intro L _ _ σ n t u ht hd hu hU k
  have hinv := (GlobalTheory.LGrp.mem_GU_iff σ n (u : GL (Fin n) L)).1 u.2
  have huGL : (u : GL (Fin n) L) ∈ IwGL L n := hu
  have hU1 : ∀ i j, Valued.v (((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) ≤ 1 :=
    fun i j => GlobalTheory.CompanionTheory.KUFactsU.iwGL_entries huGL i j
  have hV1 : ∀ i j, Valued.v ((((u : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) ≤ 1 :=
    fun i j => GlobalTheory.CompanionTheory.KUFactsU.iwGL_entries (inv_mem huGL) i j
  have hV2 : ∀ i j, j < i → (((u : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0 := by
    intro i j hji
    rw [hinv, hU.1 _ _ (Fin.rev_lt_rev.2 hji), map_zero]
  have hV3 : ∀ i, (((u : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = 1 := by
    intro i
    rw [hinv, hU.2, map_one]
  have hmem : t ^ k * u * (t ^ k)⁻¹ ∈ (KU σ n : Set (GU σ n)) := by
    rw [IntPtsUnitary.coe_KU, Set.mem_preimage, IntPtsUnitary.coe_GLint]
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · exact conj_entries_le_one ht hd hU1 hU.1 hU.2 k i j
    · have e : (((t ^ k * u * (t ^ k)⁻¹ : GU σ n) : GL (Fin n) L))⁻¹ =
          (t : GL (Fin n) L) ^ k * (u : GL (Fin n) L)⁻¹ * ((t : GL (Fin n) L) ^ k)⁻¹ := by
        simp [mul_assoc]
      rw [e]
      exact conj_entries_le_one ht hd hV1 hV2 hV3 k i j
  exact hmem

end Contr

end GlobalTheory.CompanionTheory.SatPow

end
