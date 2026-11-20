import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Formalism.SatakeDualWeyl.StatementE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGUIffAdjJ
open GlobalTheory.LGrp GlobalTheory.BorelUMod Formalism.UG

namespace GlobalTheory.BorelUMod

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

/- English proof (translation)
Establish `h0 : ϖ ≠ 0` using `fun e => by simp [e] at hϖ; exact WithZero.exp_ne_zero hϖ.symm`. Establish `hk : Valued.v (ϖ ^ k) = WithZero.exp (-k)`. Rewrite using `[map_zpow₀, hϖ, ← WithZero.exp_zsmul]`. Simplify using the standard rewrite rules. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `⟨(ϖ ^ k)⁻¹ * x, ?_, by field_simp⟩` and prove the remaining obligations. Use `show Valued.v ((ϖ ^ k)⁻¹ * x) ≤ 1`. Rewrite using `[map_mul, map_inv₀, hk]`.

Conclude with `(inv_mul_le_one₀ (zero_lt_iff.2 WithZero.exp_ne_zero)).2 hx`. Introduce and unpack `⟨y, hy, rfl⟩ show Valued.v (ϖ ^ k * y) ≤ WithZero.exp (-k)`. Rewrite using `[map_mul, hk]`. Conclude with `(mul_le_mul' le_rfl hy).trans (by rw [mul_one])`.
-/
theorem ball_eq_image {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (k : ℤ) :
    {x : L | Valued.v x ≤ WithZero.exp (-k)} = (fun x => ϖ ^ k * x) '' {x : L | Valued.v x ≤ 1} := by
  have h0 : ϖ ≠ 0 := fun e => by simp [e] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hk : Valued.v (ϖ ^ k) = WithZero.exp (-k) := by
    rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]; simp
  ext x
  constructor
  · intro hx
    refine ⟨(ϖ ^ k)⁻¹ * x, ?_, by field_simp⟩
    show Valued.v ((ϖ ^ k)⁻¹ * x) ≤ 1
    rw [map_mul, map_inv₀, hk]
    exact (inv_mul_le_one₀ (zero_lt_iff.2 WithZero.exp_ne_zero)).2 hx
  · rintro ⟨y, hy, rfl⟩
    show Valued.v (ϖ ^ k * y) ≤ WithZero.exp (-k)
    rw [map_mul, hk]
    exact (mul_le_mul' le_rfl hy).trans (by rw [mul_one])

/- English proof (translation)
Establish `h0 : ϖ ≠ 0` using `fun e => by simp [e] at hϖ; exact WithZero.exp_ne_zero hϖ.symm`. Rewrite using `[ball_eq_image hϖ]`. Conclude with `(Homeomorph.mulLeft₀ (ϖ ^ k) (zpow_ne_zero k h0)).isOpenMap _ (Valued.isOpen_integer L)`.
-/
theorem isOpen_vball {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (k : ℤ) :
    IsOpen {x : L | Valued.v x ≤ WithZero.exp (-k)} := by
  have h0 : ϖ ≠ 0 := fun e => by simp [e] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  rw [ball_eq_image hϖ]
  exact (Homeomorph.mulLeft₀ (ϖ ^ k) (zpow_ne_zero k h0)).isOpenMap _ (Valued.isOpen_integer L)

/- English proof (translation)
Take `⟨-, hv, -, hϖ, -, hq, hcard⟩` from `h`. Use `haveI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).IsNontrivial := ⟨ϖ, by rw [hϖ]; exact WithZero.coe_ne_zero, by rw [hϖ, ← WithZero.coe_one, ne_eq, WithZero.coe_inj]; decide⟩`. Use `letI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).RankOne := Valuation.IsRankOneDiscrete.rankOne _ (e := 2) (by norm_num)`. Establish `hp` using `(Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField (K := L)).2 ⟨(Valued.isClosed_integer L).completeSpace_coe, (Valued.v : Valuation L _).valuationSubring_isDiscreteValuationRing, Nat.finite_of_card_ne_zero (by`. Use `ne_of_eq_of_ne hcard (pow_ne_zero _ (by omega)))⟩` and prove the remaining obligations.

Rewrite using `[ball_eq_image hϖ]`. Conclude with `(isCompact_iff_compactSpace.2 hp).image (continuous_const.mul continuous_id)`.
-/
theorem isCompact_vball [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (k : ℤ) :
    IsCompact {x : L | Valued.v x ≤ WithZero.exp (-k)} := by
  obtain ⟨-, hv, -, hϖ, -, hq, hcard⟩ := h
  haveI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).IsNontrivial :=
    ⟨ϖ, by rw [hϖ]; exact WithZero.coe_ne_zero, by rw [hϖ, ← WithZero.coe_one, ne_eq, WithZero.coe_inj]; decide⟩
  letI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne _ (e := 2) (by norm_num)
  have hp := (Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField
    (K := L)).2 ⟨(Valued.isClosed_integer L).completeSpace_coe,
      (Valued.v : Valuation L _).valuationSubring_isDiscreteValuationRing,
      Nat.finite_of_card_ne_zero (by
        refine ne_of_eq_of_ne hcard (pow_ne_zero _ (by omega)))⟩
  rw [ball_eq_image hϖ]
  exact (isCompact_iff_compactSpace.2 hp).image (continuous_const.mul continuous_id)

/- English proof (translation)
The claim follows from `continuous_matrix fun i j => hσ.comp (continuous_id.matrix_elem j.rev i.rev)`.
-/
theorem continuous_adjJ {σ : L →+* L} (hσ : Continuous σ) (n : ℕ) :
    Continuous (adjJ σ : Matrix (Fin n) (Fin n) L → Matrix (Fin n) (Fin n) L) :=
  continuous_matrix fun i j => hσ.comp (continuous_id.matrix_elem j.rev i.rev)

/- English proof (translation)
Establish `h1 : Topology.IsInducing fun g : GU σ n => Units.embedProduct _ g.1` using `Units.isEmbedding_embedProduct.isInducing.comp Topology.IsInducing.subtypeVal`. Use `Topology.IsInducing.of_comp (g := fun A : Matrix (Fin n) (Fin n) L => (A, MulOpposite.op (adjJ σ A))) (Units.continuous_val.comp continuous_subtype_val) (continuous_id.prodMk (MulOpposite.continuous_op.comp (continuous_adjJ hσ n))) ?_` and prove the remaining obligations. Use `h1 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g`. Simplify using `only [Function.comp_apply, Units.embedProduct_apply, (mem_GU_iff_adjJ σ _).1 g.2]`.
-/
theorem isInducing_GU_val {σ : L →+* L} (hσ : Continuous σ) (n : ℕ) :
    Topology.IsInducing fun g : GU σ n => (g.1.val : Matrix (Fin n) (Fin n) L) := by
  have h1 : Topology.IsInducing fun g : GU σ n => Units.embedProduct _ g.1 :=
    Units.isEmbedding_embedProduct.isInducing.comp Topology.IsInducing.subtypeVal
  refine Topology.IsInducing.of_comp (g := fun A : Matrix (Fin n) (Fin n) L => (A, MulOpposite.op (adjJ σ A)))
    (Units.continuous_val.comp continuous_subtype_val)
    (continuous_id.prodMk (MulOpposite.continuous_op.comp (continuous_adjJ hσ n))) ?_
  convert h1 using 1
  funext g
  simp only [Function.comp_apply, Units.embedProduct_apply, (mem_GU_iff_adjJ σ _).1 g.2]

end GlobalTheory.BorelUMod
