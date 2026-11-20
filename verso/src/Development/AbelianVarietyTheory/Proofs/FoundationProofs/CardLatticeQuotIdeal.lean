import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.PolarLatticePairs
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaLatticePointMemThetaLatticeOfAdelic
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormEqRelIndexMul

open NumberField IsDedekindDomain Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.IndefiniteRowSideFullHecke.PolarLatticePairs
open scoped Pointwise

noncomputable section

namespace GlobalTheory.MatrixLatticeIndex

/- English proof (translation)
Set `Q` to `A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup`. Set `f : matIn D a d A →+ (Fin d → Fin a → Q)` to `{ toFun := fun z i j => QuotientAddGroup.mk (⟨z.1 i j, z.2 i j⟩ : A.toAddSubgroup) map_zero' := rfl map_add' := fun _ _ => rfl }`. Establish `hf : Function.Surjective f`. Introduce `y`. Use `⟨⟨fun i j => ((y i j).out : A.toAddSubgroup), fun i j => (y i j).out.2⟩, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i j`. Conclude with `QuotientAddGroup.out_eq' (y i j)`. Establish `hker : f.ker = (matIn D a d B).addSubgroupOf (matIn D a d A)`. Use extensionality with `z`. Rewrite using `[AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]`.

Prove the components needed by the constructor for the conclusion. Introduce `h i j`. Conclude with `(QuotientAddGroup.eq_zero_iff _).1 (congrFun (congrFun h i) j)`. Introduce `h`. Use function extensionality and compare the values at `i j`.

Conclude with `(QuotientAddGroup.eq_zero_iff _).2 (h i j)`. Rewrite using `[← hker, Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hf).toEquiv, Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin a), Nat.card_eq_fintype_card (α := Fin d), Fintype.card_fin, Fintype.card_fin, ← pow_mul]`. Both sides reduce to the same expression.
-/
theorem card_matIn (D : D7) (a d : ℕ) (A B : Submodule (𝓞 D.host.E) D.host.E) :
    Nat.card (matIn D a d A ⧸ (matIn D a d B).addSubgroupOf (matIn D a d A)) =
      (B.toAddSubgroup.relIndex A.toAddSubgroup) ^ (a * d) := by
  let Q := A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup
  let f : matIn D a d A →+ (Fin d → Fin a → Q) :=
    { toFun := fun z i j => QuotientAddGroup.mk (⟨z.1 i j, z.2 i j⟩ : A.toAddSubgroup)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hf : Function.Surjective f := by
    intro y
    refine ⟨⟨fun i j => ((y i j).out : A.toAddSubgroup), fun i j => (y i j).out.2⟩, ?_⟩
    funext i j
    exact QuotientAddGroup.out_eq' (y i j)
  have hker : f.ker = (matIn D a d B).addSubgroupOf (matIn D a d A) := by
    ext z
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
    constructor
    · intro h i j
      exact (QuotientAddGroup.eq_zero_iff _).1 (congrFun (congrFun h i) j)
    · intro h
      funext i j
      exact (QuotientAddGroup.eq_zero_iff _).2 (h i j)
  rw [← hker, Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hf).toEquiv,
    Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin a), Nat.card_eq_fintype_card (α := Fin d),
    Fintype.card_fin, Fintype.card_fin, ← pow_mul]
  rfl

/- English proof (translation)
Establish `hq' : (q : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.2 hq`. Establish `hle : (q : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) * J ≤ J`. Combine the equalities or inequalities in the displayed calculation. Establish `h` using `Formalism.L2.LamCM.Dx.absNorm_eq_relIndex_mul J _ (mul_ne_zero hq' hJ) hle`. Establish `he : (((q : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) * J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) = q • (J : Submodule (𝓞 K) K)`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[FractionalIdeal.coe_mul]`. Use `Submodule.mul_le.2 fun x hx y hy => ?_` and prove the remaining obligations. Take `⟨b, hb, rfl⟩` from `(FractionalIdeal.mem_coeIdeal _).1 hx`. Rewrite using `[← Algebra.smul_def]`.

Conclude with `Submodule.smul_mem_smul hb hy`. Use `Submodule.smul_le.2 fun b hb y hy => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def]`. Conclude with `FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hb) hy`. Rewrite `h` using `[he, map_mul, FractionalIdeal.coeIdeal_absNorm]`.

Establish `h0 : FractionalIdeal.absNorm J ≠ 0` using `fun h' => hJ (FractionalIdeal.absNorm_eq_zero_iff.1 h')`. Conclude with `(mul_right_cancel₀ h0 h).symm` after adjusting the coercions.
-/
theorem relIndex_smul {K : Type} [Field K] [NumberField K]
    (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hJ : J ≠ 0) (q : Ideal (𝓞 K)) (hq : q ≠ ⊥) :
    (q • (J : Submodule (𝓞 K) K)).toAddSubgroup.relIndex (J : Submodule (𝓞 K) K).toAddSubgroup =
      Ideal.absNorm q := by
  have hq' : (q : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 hq
  have hle : (q : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) * J ≤ J := by
    calc (q : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) * J ≤ 1 * J :=
          mul_le_mul' FractionalIdeal.coeIdeal_le_one le_rfl
      _ = J := one_mul J
  have h := Formalism.L2.LamCM.Dx.absNorm_eq_relIndex_mul J _ (mul_ne_zero hq' hJ) hle
  have he : (((q : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) * J :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) = q • (J : Submodule (𝓞 K) K) := by
    apply le_antisymm
    · rw [FractionalIdeal.coe_mul]
      refine Submodule.mul_le.2 fun x hx y hy => ?_
      obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
      rw [← Algebra.smul_def]
      exact Submodule.smul_mem_smul hb hy
    · refine Submodule.smul_le.2 fun b hb y hy => ?_
      rw [Algebra.smul_def]
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hb) hy
  rw [he, map_mul, FractionalIdeal.coeIdeal_absNorm] at h
  have h0 : FractionalIdeal.absNorm J ≠ 0 := fun h' => hJ (FractionalIdeal.absNorm_eq_zero_iff.1 h')
  exact_mod_cast (mul_right_cancel₀ h0 h).symm

open GlobalTheory.NormSum.MovedLattice in

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `t ⟨c, hc, m, hm, rfl⟩`. Conclude with `FractionalIdeal.mul_mem_mul (mem_ext D hc) hm`. Rewrite using `[FractionalIdeal.coe_mul]`.

Use `Submodule.mul_le.2 fun x hx y hy => ?_` and prove the remaining obligations. Take `⟨b, hb, rfl⟩` from `(FractionalIdeal.mem_coeIdeal _).1 hx`. Use `clear hx`. Proceed by induction on `hb using Submodule.span_induction with`. Consider the case `mem b hb`.

Take `⟨c, hc, rfl⟩` from `hb`. Conclude with `Submodule.subset_span ⟨c, hc, y, hy, rfl⟩`. Consider the case `zero => rw [map_zero, zero_mul]`. Conclude with `zero_mem _`. Consider the case `add b b' _ _ hb hb' => rw [map_add, add_mul]`.

Conclude with `add_mem hb hb'`. Consider the case `smul r b _ hb`. Rewrite using `[smul_eq_mul, map_mul, mul_assoc, ← Algebra.smul_def]`. Conclude with `Submodule.smul_mem _ r hb`.
-/
theorem coefLat_eq (D : D7) (cc : Ideal (𝓞 D.host.K)) :
    coefLat D cc = ((ext D cc * D.host.AA0 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
      Submodule (𝓞 D.host.E) D.host.E) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro t ⟨c, hc, m, hm, rfl⟩
    exact FractionalIdeal.mul_mem_mul (mem_ext D hc) hm
  · rw [FractionalIdeal.coe_mul]
    refine Submodule.mul_le.2 fun x hx y hy => ?_
    obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
    clear hx
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨c, hc, rfl⟩ := hb
      exact Submodule.subset_span ⟨c, hc, y, hy, rfl⟩
    | zero => rw [map_zero, zero_mul]; exact zero_mem _
    | add b b' _ _ hb hb' => rw [map_add, add_mul]; exact add_mem hb hb'
    | smul r b _ hb =>
      rw [smul_eq_mul, map_mul, mul_assoc, ← Algebra.smul_def]
      exact Submodule.smul_mem _ r hb

end GlobalTheory.MatrixLatticeIndex

open GlobalTheory.NormSum.MovedLattice GlobalTheory.MatrixLatticeIndex in

/- English proof (translation)
Introduce `D cc a d q hcc hq`. Rewrite using `[card_matIn, coefLat_eq, relIndex_smul _ (mul_ne_zero (ext_ne_zero D hcc) (inverseHalfDifferent_ne_zero D)) q hq]`.
-/
theorem GlobalTheory.MatrixLatticeIndex.card_lattice_quot_ideal : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (a d : ℕ) (q : Ideal (𝓞 D.host.E)), cc ≠ ⊥ → q ≠ ⊥ → Nat.card (lat0 D cc a d ⧸ (latQ D cc a d q).addSubgroupOf (lat0 D cc a d)) = Ideal.absNorm q ^ (a * d) := by
  intro D cc a d q hcc hq
  rw [card_matIn, coefLat_eq, relIndex_smul _ (mul_ne_zero (ext_ne_zero D hcc) (inverseHalfDifferent_ne_zero D)) q hq]
