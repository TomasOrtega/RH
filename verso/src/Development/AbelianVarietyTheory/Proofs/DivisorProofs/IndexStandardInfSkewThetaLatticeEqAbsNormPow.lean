import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PtHomInjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardLatticeQuotIdeal
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.SkewIndex

open GlobalTheory.IndefiniteRowSideFullHecke.PolarLatticePairs GlobalTheory.ThetaLatticePoints GlobalTheory.MatrixLatticeIndex GlobalTheory.NormSum.MovedLattice

/- English proof (translation)
Establish `h𝔫' : (𝔫 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.2 h𝔫`. Apply `le_antisymm` to reduce the goal to its premises. Take `⟨I, hI⟩` from `FractionalIdeal.le_one_iff_exists_coeIdeal.1 (inf_le_left : (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ⊓ _ ≤ 1)`. Rewrite using `[← hI]`. Establish `h2 : (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≤ (𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) / 𝔫` using `hI ▸ inf_le_right`.

Rewrite `h2` using `[FractionalIdeal.le_div_iff_mul_le h𝔫', ← FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_le_coeIdeal]`. Rewrite using `[FractionalIdeal.coeIdeal_le_coeIdeal]`. Establish `hs : 𝔪 ⊔ 𝔫 = ⊤` using `Ideal.isCoprime_iff_sup_eq.1 hc`. Combine the equalities or inequalities in the displayed calculation. Use `le_inf FractionalIdeal.coeIdeal_le_one ?_` and prove the remaining obligations.

Rewrite using `[FractionalIdeal.le_div_iff_mul_le h𝔫']`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem one_inf_div {E : Type} [Field E] [NumberField E] (𝔪 𝔫 : Ideal (𝓞 E)) (h𝔫 : 𝔫 ≠ ⊥)
    (hc : IsCoprime 𝔪 𝔫) :
    (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ⊓ ((𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) / 𝔫) = 𝔪 := by
  have h𝔫' : (𝔫 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h𝔫
  apply le_antisymm
  · obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 (inf_le_left : (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ⊓ _ ≤ 1)
    rw [← hI]
    have h2 : (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≤ (𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) / 𝔫 := hI ▸ inf_le_right
    rw [FractionalIdeal.le_div_iff_mul_le h𝔫', ← FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_le_coeIdeal] at h2
    rw [FractionalIdeal.coeIdeal_le_coeIdeal]
    have hs : 𝔪 ⊔ 𝔫 = ⊤ := Ideal.isCoprime_iff_sup_eq.1 hc
    calc I = I * (𝔪 ⊔ 𝔫) := by rw [hs, Ideal.mul_top]
      _ = I * 𝔪 ⊔ I * 𝔫 := Ideal.mul_sup _ _ _
      _ ≤ 𝔪 := sup_le (by first | exact Ideal.mul_le_right | exact Ideal.mul_le_left) h2
  · refine le_inf FractionalIdeal.coeIdeal_le_one ?_
    rw [FractionalIdeal.le_div_iff_mul_le h𝔫']
    calc (𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * 𝔫 ≤ 𝔪 * 1 := mul_le_mul' le_rfl FractionalIdeal.coeIdeal_le_one
      _ = 𝔪 := mul_one _

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Conclude with `le_inf (mul_le_mul' le_rfl inf_le_left) (mul_le_mul' le_rfl inf_le_right)`. Establish `e : A * X ⊓ A * Y = A * (A⁻¹ * (A * X ⊓ A * Y))`. Rewrite using `[← mul_assoc, mul_inv_cancel₀ hA, one_mul]`. Rewrite using `[e]`.

Use `mul_le_mul' le_rfl (le_inf ?_ ?_)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem mul_inf {E : Type} [Field E] [NumberField E] (A X Y : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (hA : A ≠ 0) : A * (X ⊓ Y) = A * X ⊓ A * Y := by
  apply le_antisymm
  · exact le_inf (mul_le_mul' le_rfl inf_le_left) (mul_le_mul' le_rfl inf_le_right)
  · have e : A * X ⊓ A * Y = A * (A⁻¹ * (A * X ⊓ A * Y)) := by
      rw [← mul_assoc, mul_inv_cancel₀ hA, one_mul]
    rw [e]
    refine mul_le_mul' le_rfl (le_inf ?_ ?_)
    · calc A⁻¹ * (A * X ⊓ A * Y) ≤ A⁻¹ * (A * X) := mul_le_mul' le_rfl inf_le_left
        _ = X := by rw [← mul_assoc, inv_mul_cancel₀ hA, one_mul]
    · calc A⁻¹ * (A * X ⊓ A * Y) ≤ A⁻¹ * (A * Y) := mul_le_mul' le_rfl inf_le_right
        _ = Y := by rw [← mul_assoc, inv_mul_cancel₀ hA, one_mul]

variable (D : D7)

def skewEnt (𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E :=
  (𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) /
    ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)

/- English proof (translation)
Simplify using `only [skewLat, skewEnt, Submodule.mem_pi, Set.mem_univ, true_implies]`.
-/
theorem mem_skewLat_iff (𝔪 : Ideal (𝓞 D.host.E)) (N : ℕ) (x : Fin N → D.host.E) :
    x ∈ skewLat D 𝔪 N ↔ ∀ i, x i ∈ (skewEnt D 𝔪 : Submodule (𝓞 D.host.E) D.host.E) := by
  simp only [skewLat, skewEnt, Submodule.mem_pi, Set.mem_univ, true_implies]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem B hB`. Take `⟨c, hc, A, hA, rfl⟩` from `hB`.

Establish `hAe : ∀ i j, A i j ∈ (skewEnt D 𝔪 : Submodule (𝓞 D.host.E) D.host.E)`. Proceed by induction on `hA using Submodule.span_induction with`. Consider the case `mem A hA`. Introduce `i j`. Establish `hj : (Pi.single j (1 : D.host.E) : Fin a → D.host.E) ∈ stdL D a`.

Simplify using `only [stdL, Submodule.mem_pi, Set.mem_univ, true_implies]`. Introduce `k`. Distinguish the cases in `hk : k = j`. Substitute `hk` using the available equality. Simplify using `[Submodule.one_eq_range]`.

Simplify using `[Pi.single_apply, hk]`. Establish `h` using `(mem_skewLat_iff D 𝔪 d _).1 (hA _ hj) i`. Simplify `h` using `[Matrix.mulVec_single]`. Consider the case `zero => intro i j`. Simplify using the standard rewrite rules.

Consider the case `add A B _ _ h1 h2 => intro i j`. Simplify using `using add_mem (h1 i j) (h2 i j)`. Consider the case `smul r A _ h => intro i j`. Simplify using `using Submodule.smul_mem _ r (h i j)`. Introduce `i j`.

Simplify using `only [Matrix.smul_apply, smul_eq_mul]`. Conclude with `FractionalIdeal.mul_mem_mul hc (hAe i j)`. Consider the case `zero => intro i j`. Simplify using the standard rewrite rules. Consider the case `add A B _ _ h1 h2 => intro i j`.

Simplify using `using add_mem (h1 i j) (h2 i j)`. Consider the case `smul r A _ h => intro i j`. Simplify using `using Submodule.smul_mem _ r (h i j)`. Introduce `hx`. Rewrite using `[Matrix.matrix_eq_sum_single x]`.

Use `sum_mem fun i _ => sum_mem fun j _ => ?_` and prove the remaining obligations. Establish `hij` using `hx i j`. Rewrite `hij` using `[FractionalIdeal.coe_mul]`. Use `Submodule.mul_induction_on (C := fun r => Matrix.single i j r ∈ YYl D (stdL D a) (skewLat D 𝔪 d)) hij ?_ ?_` and prove the remaining obligations. Introduce `m hm n hn`.

Use `Submodule.subset_span ⟨m, hm, Matrix.single i j n, Submodule.subset_span fun v hv => ?_, ?_⟩` and prove the remaining obligations. Use `(mem_skewLat_iff D 𝔪 d _).2 fun k => ?_` and prove the remaining obligations. Establish `hvj : v j ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)`. Simplify using `only [stdL, Submodule.mem_pi, Set.mem_univ, true_implies] at hv`. Conclude with `hv j`.

Take `⟨o, ho⟩` from `Submodule.mem_one.1 hvj`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.single_apply, true_and]`. Rewrite using `[Finset.sum_eq_single j (fun l _ hl => by simp [Ne.symm hl]) (by simp)]`.

Simplify using `only [if_true]`. Rewrite using `[← ho, mul_comm, ← Algebra.smul_def]`. Conclude with `Submodule.smul_mem _ o hn`. Establish `hk' : i ≠ k` using `Ne.symm hk`. Simplify using `[Matrix.mulVec, dotProduct, Matrix.single_apply, hk']`.

Rewrite using `[Matrix.smul_single, smul_eq_mul]`. Introduce `x y hx hy`. Simplify `add_mem hx hy` using `[Matrix.single_add]`.
-/
theorem mem_YYl_skew_iff (𝔪 : Ideal (𝓞 D.host.E)) (a d : ℕ) (x : Matrix (Fin d) (Fin a) D.host.E) :
    x ∈ YYl D (stdL D a) (skewLat D 𝔪 d) ↔
      ∀ i j, x i j ∈ ((D.host.AA0 * skewEnt D 𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E) := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem B hB =>
      obtain ⟨c, hc, A, hA, rfl⟩ := hB
      have hAe : ∀ i j, A i j ∈ (skewEnt D 𝔪 : Submodule (𝓞 D.host.E) D.host.E) := by
        induction hA using Submodule.span_induction with
        | mem A hA =>
          intro i j
          have hj : (Pi.single j (1 : D.host.E) : Fin a → D.host.E) ∈ stdL D a := by
            simp only [stdL, Submodule.mem_pi, Set.mem_univ, true_implies]
            intro k
            by_cases hk : k = j
            · subst hk; simp [Submodule.one_eq_range]
            · simp [Pi.single_apply, hk]
          have h := (mem_skewLat_iff D 𝔪 d _).1 (hA _ hj) i
          simpa [Matrix.mulVec_single] using h
        | zero => intro i j; simp
        | add A B _ _ h1 h2 => intro i j; simpa using add_mem (h1 i j) (h2 i j)
        | smul r A _ h => intro i j; simpa using Submodule.smul_mem _ r (h i j)
      intro i j
      simp only [Matrix.smul_apply, smul_eq_mul]
      exact FractionalIdeal.mul_mem_mul hc (hAe i j)
    | zero => intro i j; simp
    | add A B _ _ h1 h2 => intro i j; simpa using add_mem (h1 i j) (h2 i j)
    | smul r A _ h => intro i j; simpa using Submodule.smul_mem _ r (h i j)
  · intro hx
    rw [Matrix.matrix_eq_sum_single x]
    refine sum_mem fun i _ => sum_mem fun j _ => ?_
    have hij := hx i j
    rw [FractionalIdeal.coe_mul] at hij
    refine Submodule.mul_induction_on (C := fun r => Matrix.single i j r ∈ YYl D (stdL D a) (skewLat D 𝔪 d)) hij ?_ ?_
    · intro m hm n hn
      refine Submodule.subset_span ⟨m, hm, Matrix.single i j n, Submodule.subset_span fun v hv => ?_, ?_⟩
      · refine (mem_skewLat_iff D 𝔪 d _).2 fun k => ?_
        have hvj : v j ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
          simp only [stdL, Submodule.mem_pi, Set.mem_univ, true_implies] at hv
          exact hv j
        obtain ⟨o, ho⟩ := Submodule.mem_one.1 hvj
        by_cases hk : k = i
        · subst hk
          simp only [Matrix.mulVec, dotProduct, Matrix.single_apply, true_and]
          rw [Finset.sum_eq_single j (fun l _ hl => by simp [Ne.symm hl]) (by simp)]
          simp only [if_true]
          rw [← ho, mul_comm, ← Algebra.smul_def]
          exact Submodule.smul_mem _ o hn
        · have hk' : i ≠ k := Ne.symm hk
          simp [Matrix.mulVec, dotProduct, Matrix.single_apply, hk']
      · rw [Matrix.smul_single, smul_eq_mul]
    · intro x y hx hy
      simpa [Matrix.single_add] using add_mem hx hy

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨w, hw, A, hA, rfl⟩`. Take `⟨c, hc, rfl⟩` from `(GlobalTheory.CurveLattice.mem_lamOf D ⊤ δ w).1 hw`. Use `⟨((c : D.host.K) : D.host.E) • A, fun i j => ?_, ptHom_smul D ⊤ δ a d c A⟩` and prove the remaining obligations.

Use `(mem_YYl_skew_iff D 𝔪 a d A).1 hA i j` as an intermediate fact. Rewrite using `[Matrix.smul_apply, smul_eq_mul, ← coe_alg, ← Algebra.smul_def]`. Conclude with `Submodule.smul_mem _ _ this`. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Use `AddSubgroup.subset_closure ⟨δ, (GlobalTheory.CurveLattice.mem_lamOf D ⊤ δ δ).2 ⟨1, trivial, by simp⟩, z, (mem_YYl_skew_iff D 𝔪 a d z).2 hz, ?_⟩` and prove the remaining obligations.

Both sides reduce to the same expression.
-/
theorem La_skew_eq_map (δ : ℂ) (𝔪 : Ideal (𝓞 D.host.E)) (a d : ℕ) :
    La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d) =
      (matIn D a d ((D.host.AA0 * skewEnt D 𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E)).map (ptHom D ⊤ δ a d) := by
  apply le_antisymm
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨w, hw, A, hA, rfl⟩
    obtain ⟨c, hc, rfl⟩ := (GlobalTheory.CurveLattice.mem_lamOf D ⊤ δ w).1 hw
    refine ⟨((c : D.host.K) : D.host.E) • A, fun i j => ?_, ptHom_smul D ⊤ δ a d c A⟩
    have := (mem_YYl_skew_iff D 𝔪 a d A).1 hA i j
    rw [Matrix.smul_apply, smul_eq_mul, ← coe_alg, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ this
  · rintro _ ⟨z, hz, rfl⟩
    refine AddSubgroup.subset_closure ⟨δ, (GlobalTheory.CurveLattice.mem_lamOf D ⊤ δ δ).2 ⟨1, trivial, by simp⟩, z,
      (mem_YYl_skew_iff D 𝔪 a d z).2 hz, ?_⟩
    rfl

end GlobalTheory.SkewIndex

namespace GlobalTheory.SkewIndex

open GlobalTheory.IndefiniteRowSideFullHecke.PolarLatticePairs GlobalTheory.ThetaLatticePoints GlobalTheory.MatrixLatticeIndex GlobalTheory.NormSum.MovedLattice

/- English proof (translation)
Introduce `D δ hC 𝔪 h𝔪 hcop a d`. Establish `hδ : δ ≠ 0` using `(GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 ⊤ δ hC).2.1`. Establish `hN : Ideal.absNorm (D.host.conj • 𝔪) = Ideal.absNorm 𝔪` using `UnusedSlot33.HK.absNorm_smul D.host 𝔪`. Establish `h𝔫 : (D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) ≠ ⊥`. Introduce `h`.

Apply `h𝔪` to reduce the goal to its premises. Rewrite using `[← Ideal.absNorm_eq_zero_iff, ← hN, h, Ideal.absNorm_bot]`. Establish `hA` using `inverseHalfDifferent_ne_zero D`. Establish `h𝔪' : (𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.2 h𝔪`. Establish `h𝔫' : ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.2 h𝔫`.

Establish `hJ : D.host.AA0 * skewEnt D 𝔪 ≠ 0` using `mul_ne_zero hA (div_ne_zero h𝔪' h𝔫')`. Establish `hcoef : coefLat D ⊤ = (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)`. Rewrite using `[coefLat_eq, ext, Ideal.map_top, FractionalIdeal.coeIdeal_top, one_mul]`. Establish `hF : D.host.AA0 ⊓ D.host.AA0 * skewEnt D 𝔪 = ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) * (D.host.AA0 * skewEnt D 𝔪)`. Rewrite using `[show D.host.AA0 ⊓ D.host.AA0 * skewEnt D 𝔪 = D.host.AA0 * 1 ⊓ D.host.AA0 * skewEnt D 𝔪 by rw [mul_one]]`.

Rewrite using `[← mul_inf _ _ _ hA, skewEnt, one_inf_div 𝔪 _ h𝔫 hcop, mul_left_comm, mul_div_cancel₀ _ h𝔫']`. Establish `he : ∀ J : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E, ((((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) * J : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E) = (D.host.con …`. Introduce `J`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[FractionalIdeal.coe_mul]`.

Use `Submodule.mul_le.2 fun x hx y hy => ?_` and prove the remaining obligations. Take `⟨b, hb, rfl⟩` from `(FractionalIdeal.mem_coeIdeal _).1 hx`. Rewrite using `[← Algebra.smul_def]`. Conclude with `Submodule.smul_mem_smul hb hy`. Use `Submodule.smul_le.2 fun b hb y hy => ?_` and prove the remaining obligations.

Rewrite using `[Algebra.smul_def]`. Conclude with `FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hb) hy`. Establish `hinf : (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup ⊓ ((D.host.AA0 * skewEnt D 𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup = ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) • ((D.host.AA0 * skewEnt D 𝔪 : Fr …`. Rewrite using `[← he, ← hF, FractionalIdeal.coe_inf]`. Both sides reduce to the same expression.

Use `show (La0 D (tor0 D ⊤ δ) a d).relIndex (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) = _`. Rewrite using `[La0_eq_map, La_skew_eq_map, AddSubgroup.relIndex_map_map_of_injective _ _ (ptHom_injective D ⊤ hδ a d)]`. Establish `hc` using `card_matIn D a d ((D.host.AA0 * skewEnt D 𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E) (coefLat D ⊤)`. Rewrite `hc` using `[hcoef, ← AddSubgroup.inf_relIndex_right, hinf, relIndex_smul _ hJ _ h𝔫, hN]`. Rewrite using `[show lat0 D ⊤ a d = matIn D a d (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) by rw [lat0, hcoef]]`.

Conclude with `hc`.
-/
theorem index_inter_skew : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → ∀ (a d : ℕ), ((La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))).index = Ideal.absNorm 𝔪 ^ (a * d) := by
  intro D δ hC 𝔪 h𝔪 hcop a d
  have hδ : δ ≠ 0 := (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 ⊤ δ hC).2.1
  have hN : Ideal.absNorm (D.host.conj • 𝔪) = Ideal.absNorm 𝔪 := UnusedSlot33.HK.absNorm_smul D.host 𝔪
  have h𝔫 : (D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) ≠ ⊥ := by
    intro h
    apply h𝔪
    rw [← Ideal.absNorm_eq_zero_iff, ← hN, h, Ideal.absNorm_bot]
  have hA := inverseHalfDifferent_ne_zero D
  have h𝔪' : (𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 h𝔪
  have h𝔫' : ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 h𝔫
  have hJ : D.host.AA0 * skewEnt D 𝔪 ≠ 0 := mul_ne_zero hA (div_ne_zero h𝔪' h𝔫')
  have hcoef : coefLat D ⊤ = (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
    rw [coefLat_eq, ext, Ideal.map_top, FractionalIdeal.coeIdeal_top, one_mul]

  have hF : D.host.AA0 ⊓ D.host.AA0 * skewEnt D 𝔪 =
      ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) *
        (D.host.AA0 * skewEnt D 𝔪) := by
    rw [show D.host.AA0 ⊓ D.host.AA0 * skewEnt D 𝔪 = D.host.AA0 * 1 ⊓ D.host.AA0 * skewEnt D 𝔪 by rw [mul_one]]
    rw [← mul_inf _ _ _ hA, skewEnt, one_inf_div 𝔪 _ h𝔫 hcop, mul_left_comm, mul_div_cancel₀ _ h𝔫']
  have he : ∀ J : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E,
      ((((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) * J :
        FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E) =
        (D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) • (J : Submodule (𝓞 D.host.E) D.host.E) := by
    intro J
    apply le_antisymm
    · rw [FractionalIdeal.coe_mul]
      refine Submodule.mul_le.2 fun x hx y hy => ?_
      obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
      rw [← Algebra.smul_def]
      exact Submodule.smul_mem_smul hb hy
    · refine Submodule.smul_le.2 fun b hb y hy => ?_
      rw [Algebra.smul_def]
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hb) hy
  have hinf : (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup ⊓
      ((D.host.AA0 * skewEnt D 𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup =
      ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) • ((D.host.AA0 * skewEnt D 𝔪 :
        FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E)).toAddSubgroup := by
    rw [← he, ← hF, FractionalIdeal.coe_inf]
    rfl
  show (La0 D (tor0 D ⊤ δ) a d).relIndex (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) = _
  rw [La0_eq_map, La_skew_eq_map, AddSubgroup.relIndex_map_map_of_injective _ _ (ptHom_injective D ⊤ hδ a d)]
  have hc := card_matIn D a d ((D.host.AA0 * skewEnt D 𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
    Submodule (𝓞 D.host.E) D.host.E) (coefLat D ⊤)
  rw [hcoef, ← AddSubgroup.inf_relIndex_right, hinf, relIndex_smul _ hJ _ h𝔫, hN] at hc
  rw [show lat0 D ⊤ a d = matIn D a d (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) by rw [lat0, hcoef]]
  exact hc

end GlobalTheory.SkewIndex
