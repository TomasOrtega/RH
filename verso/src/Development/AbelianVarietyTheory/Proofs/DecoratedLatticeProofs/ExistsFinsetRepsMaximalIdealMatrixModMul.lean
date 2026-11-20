import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
import Formalism.LocalToGlobal.Columns.HeckeSp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BlockDetLowUEmb

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke

noncomputable section

namespace GlobalTheory.LowerHecke.MaxReps

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

variable (k D A) in

def maxLat : AddSubgroup (Matrix D A k) where
  carrier := {ν | ∀ i a, valuation k (ν i a) < 1}
  add_mem' ha hb i a := by simpa using Valuation.map_add_lt _ (ha i a) (hb i a)
  zero_mem' i a := by simp
  neg_mem' ha i a := by simpa using ha i a

def mulLat (g : Matrix D D k) : AddSubgroup (Matrix D A k) where
  carrier := {x | ∃ μ : Matrix D A k, (∀ i a, valuation k (μ i a) < 1) ∧ x = g * μ}
  add_mem' := by
    rintro _ _ ⟨μ, hμ, rfl⟩ ⟨μ', hμ', rfl⟩
    exact ⟨μ + μ', fun i a => by simpa using Valuation.map_add_lt _ (hμ i a) (hμ' i a),
      (Matrix.mul_add _ _ _).symm⟩
  zero_mem' := ⟨0, fun i a => by simp, by simp⟩
  neg_mem' := by
    rintro _ ⟨μ, hμ, rfl⟩
    exact ⟨-μ, fun i a => by simpa using hμ i a, (Matrix.mul_neg _ _).symm⟩

/- English proof (translation)
Use `show valuation k _ ≤ 1`. Establish `h0 : valuation k (ϖ : k) ≠ 0` using `by simp`. Rewrite using `[map_mul, map_inv₀, inv_mul_le_iff₀ (zero_lt_iff.2 h0), mul_one, hϖ, le_uniformizer_iff]`. Conclude with `hx`.
-/
theorem inv_mul_mem {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) {x : k} (hx : valuation k x < 1) :
    (ϖ : k)⁻¹ * x ∈ 𝒪[k] := by
  show valuation k _ ≤ 1
  have h0 : valuation k (ϖ : k) ≠ 0 := by simp
  rw [map_mul, map_inv₀, inv_mul_le_iff₀ (zero_lt_iff.2 h0), mul_one, hϖ, le_uniformizer_iff]
  exact hx

def redMap (ϖ : kˣ) (hϖ : valuation k (ϖ : k) = uniformizer k) : maxLat k A D →+ (D → A → 𝓀[k]) where
  toFun ν i a := IsLocalRing.residue 𝒪[k] ⟨(ϖ : k)⁻¹ * (ν : Matrix D A k) i a, inv_mul_mem hϖ (ν.2 i a)⟩
  map_zero' := by
    funext i a
    simp only [AddSubgroup.coe_zero, Matrix.zero_apply, mul_zero, Pi.zero_apply]
    exact map_zero _
  map_add' ν ν' := by
    funext i a
    simp only [Pi.add_apply]
    rw [← map_add]
    congr 1
    ext
    simp [mul_add]

/- English proof (translation)
Take `⟨κ, hκ, κ', hκ', rfl⟩` from `hg`. Establish `hϖ1 : (ϖ : k) ∈ 𝒪[k]` using `(hϖ ▸ uniformizer_lt_one).le`. Set `D0 : Matrix D D k` to `diagonal fun i => (ϖ : k) ^ (1 - indic s i)`. Establish `hD0 : (torusElt k D ϖ (indic s)).1 * D0 = (ϖ : k) • (1 : Matrix D D k)`. Rewrite using `[val_torusElt, diagonal_mul_diagonal, smul_one_eq_diagonal]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[← zpow_add₀ ϖ.ne_zero]`. Simplify using the standard rewrite rules. Use `⟨(κ'⁻¹ : GL D k).1 * D0 * (κ⁻¹ : GL D k).1, ?_, ?_⟩` and prove the remaining obligations.

Use `((GlobalTheory.StepData.mem_KO.1 hκ').2.mul ?_).mul (GlobalTheory.StepData.mem_KO.1 hκ).2` and prove the remaining obligations. Introduce `i j`. Simplify using `only [D0, diagonal_apply]`. Use `split_ifs`. Apply the tactic sequence `by_cases hi : i ∈ s <;> simp [indic, hi, hϖ1]`.

Conclude with `zero_mem _`. Establish `e1 : κ'.1 * (κ'⁻¹ : GL D k).1 = 1` using `Units.mul_inv κ'`. Establish `e2 : κ.1 * (κ⁻¹ : GL D k).1 = 1` using `Units.mul_inv κ`. Simplify using `only [Units.val_mul]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by rw [e1, Matrix.mul_one, hD0, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, e2]`.
-/
theorem exists_int_right_inv {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (s : Finset D) (g : GL D k)
    (hg : ∃ κ ∈ KO k D, ∃ κ' ∈ KO k D, g = κ * torusElt k D ϖ (indic s) * κ') :
    ∃ Q : Matrix D D k, GlobalTheory.StepData.IntM Q ∧ g.1 * Q = (ϖ : k) • (1 : Matrix D D k) := by
  obtain ⟨κ, hκ, κ', hκ', rfl⟩ := hg
  have hϖ1 : (ϖ : k) ∈ 𝒪[k] := (hϖ ▸ uniformizer_lt_one).le
  let D0 : Matrix D D k := diagonal fun i => (ϖ : k) ^ (1 - indic s i)
  have hD0 : (torusElt k D ϖ (indic s)).1 * D0 = (ϖ : k) • (1 : Matrix D D k) := by
    rw [val_torusElt, diagonal_mul_diagonal, smul_one_eq_diagonal]
    congr 1
    funext i
    rw [← zpow_add₀ ϖ.ne_zero]
    simp
  refine ⟨(κ'⁻¹ : GL D k).1 * D0 * (κ⁻¹ : GL D k).1, ?_, ?_⟩
  · refine ((GlobalTheory.StepData.mem_KO.1 hκ').2.mul ?_).mul (GlobalTheory.StepData.mem_KO.1 hκ).2
    intro i j
    simp only [D0, diagonal_apply]
    split_ifs
    · by_cases hi : i ∈ s <;> simp [indic, hi, hϖ1]
    · exact zero_mem _
  · have e1 : κ'.1 * (κ'⁻¹ : GL D k).1 = 1 := Units.mul_inv κ'
    have e2 : κ.1 * (κ⁻¹ : GL D k).1 = 1 := Units.mul_inv κ
    simp only [Units.val_mul]
    calc κ.1 * (torusElt k D ϖ (indic s)).1 * κ'.1 * ((κ'⁻¹ : GL D k).1 * D0 * (κ⁻¹ : GL D k).1)
        = κ.1 * ((torusElt k D ϖ (indic s)).1 * (κ'.1 * (κ'⁻¹ : GL D k).1) * D0) * (κ⁻¹ : GL D k).1 := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [e1, Matrix.mul_one, hD0, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, e2]

end GlobalTheory.LowerHecke.MaxReps

open GlobalTheory.LowerHecke.MaxReps in

/- English proof (translation)
Introduce `k _ _ _ _ A D _ _ _ _ ϖ hϖ s g hg`. Take `⟨Q, hQ, hgQ⟩` from `exists_int_right_inv hϖ s g hg`. Set `M` to `maxLat k A D`. Set `H` to `(mulLat (A := A) g.1).addSubgroupOf M`. Establish `hK : (redMap (D` using `D) (A := A) ϖ hϖ).ker ≤ H := by`.

Introduce `ν hν`. Rewrite `hν` using `[AddMonoidHom.mem_ker]`. Rewrite using `[AddSubgroup.mem_addSubgroupOf]`. Establish `hμ : ∀ i a, valuation k ((ϖ : k)⁻¹ * (ν : Matrix D A k) i a) < 1` using `fun i a => by`. Use `congrFun (congrFun hν i) a` as an intermediate fact.

Simplify using `only [redMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply] at this`. Conclude with `(GlobalTheory.StepData.residue_eq_zero_iff_lt _).1 this`. Use `⟨Q * ((ϖ : k)⁻¹ • (ν : Matrix D A k)), hQ.mul_maxM (fun i a => by simpa using hμ i a), ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.mul_assoc, hgQ, Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ ϖ.ne_zero, one_smul]`. Use `haveI : Finite (M ⧸ (redMap (D := D) (A := A) ϖ hϖ).ker) := Finite.of_equiv _ (QuotientAddGroup.quotientKerEquivRange _).symm.toEquiv`.

Use `haveI : (redMap (D := D) (A := A) ϖ hϖ).ker.FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient`. Use `haveI : H.FiniteIndex := AddSubgroup.finiteIndex_of_le hK`. Use `haveI : Finite (M ⧸ H) := AddSubgroup.finite_quotient_of_finiteIndex`. Use `letI := Fintype.ofFinite (M ⧸ H)`. Use `⟨Finset.univ.image fun q : M ⧸ H => ((Quotient.out q : M) : Matrix D A k), ?_, ?_⟩` and prove the remaining obligations.

Introduce `ν hν`. Take `⟨q, -, rfl⟩` from `Finset.mem_image.1 hν`. Conclude with `(Quotient.out q).2`. Introduce `ν hν`. Establish `key : ∀ q : M ⧸ H, q = (QuotientAddGroup.mk ⟨ν, hν⟩ : M ⧸ H) ↔ ∃ μ : Matrix D A k, (∀ i a, valuation k (μ i a) < 1) ∧ ν - ((Quotient.out q : M) : Matrix D A k) = g.1 * μ`.

Introduce `q`. Use `conv_lhs => rw [← QuotientAddGroup.out_eq' q]`. Rewrite using `[QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]`. Use `exists_congr fun μ => and_congr_right fun _ => ?_` and prove the remaining obligations. Use `show -((Quotient.out q : M) : Matrix D A k) + ν = g.1 * μ ↔ _`.

Rewrite using `[neg_add_eq_sub]`. Use `⟨((Quotient.out (QuotientAddGroup.mk ⟨ν, hν⟩ : M ⧸ H) : M) : Matrix D A k), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), (key _).1 rfl⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `y ⟨hy, hyμ⟩`. Take `⟨q, -, rfl⟩` from `Finset.mem_image.1 hy`. Rewrite using `[(key q).2 hyμ]`.
-/
theorem GlobalTheory.LowerHecke.exists_finset_reps_maxLat_mod_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D) (g : GL D k), (∃ κ ∈ KO k D, ∃ κ' ∈ KO k D, g = κ * torusElt k D ϖ (indic s) * κ') → ∃ N : Finset (Matrix D A k), (∀ ν ∈ N, ∀ i a, valuation k (ν i a) < 1) ∧ ∀ ν : Matrix D A k, (∀ i a, valuation k (ν i a) < 1) → ∃! ν', ν' ∈ N ∧ ∃ μ : Matrix D A k, (∀ i a, valuation k (μ i a) < 1) ∧ ν - ν' = g.1 * μ := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ s g hg
  classical
  obtain ⟨Q, hQ, hgQ⟩ := exists_int_right_inv hϖ s g hg
  let M := maxLat k A D
  let H := (mulLat (A := A) g.1).addSubgroupOf M
  have hK : (redMap (D := D) (A := A) ϖ hϖ).ker ≤ H := by
    intro ν hν
    rw [AddMonoidHom.mem_ker] at hν
    rw [AddSubgroup.mem_addSubgroupOf]
    have hμ : ∀ i a, valuation k ((ϖ : k)⁻¹ * (ν : Matrix D A k) i a) < 1 := fun i a => by
      have := congrFun (congrFun hν i) a
      simp only [redMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply] at this
      exact (GlobalTheory.StepData.residue_eq_zero_iff_lt _).1 this
    refine ⟨Q * ((ϖ : k)⁻¹ • (ν : Matrix D A k)), hQ.mul_maxM (fun i a => by simpa using hμ i a), ?_⟩
    rw [← Matrix.mul_assoc, hgQ, Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ ϖ.ne_zero, one_smul]
  haveI : Finite (M ⧸ (redMap (D := D) (A := A) ϖ hϖ).ker) :=
    Finite.of_equiv _ (QuotientAddGroup.quotientKerEquivRange _).symm.toEquiv
  haveI : (redMap (D := D) (A := A) ϖ hϖ).ker.FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient
  haveI : H.FiniteIndex := AddSubgroup.finiteIndex_of_le hK
  haveI : Finite (M ⧸ H) := AddSubgroup.finite_quotient_of_finiteIndex
  letI := Fintype.ofFinite (M ⧸ H)
  refine ⟨Finset.univ.image fun q : M ⧸ H => ((Quotient.out q : M) : Matrix D A k), ?_, ?_⟩
  · intro ν hν
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hν
    exact (Quotient.out q).2
  · intro ν hν
    have key : ∀ q : M ⧸ H, q = (QuotientAddGroup.mk ⟨ν, hν⟩ : M ⧸ H) ↔
        ∃ μ : Matrix D A k, (∀ i a, valuation k (μ i a) < 1) ∧ ν - ((Quotient.out q : M) : Matrix D A k) = g.1 * μ := by
      intro q
      conv_lhs => rw [← QuotientAddGroup.out_eq' q]
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      refine exists_congr fun μ => and_congr_right fun _ => ?_
      show -((Quotient.out q : M) : Matrix D A k) + ν = g.1 * μ ↔ _
      rw [neg_add_eq_sub]
    refine ⟨((Quotient.out (QuotientAddGroup.mk ⟨ν, hν⟩ : M ⧸ H) : M) : Matrix D A k),
      ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), (key _).1 rfl⟩, ?_⟩
    rintro y ⟨hy, hyμ⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    rw [(key q).2 hyμ]

end
