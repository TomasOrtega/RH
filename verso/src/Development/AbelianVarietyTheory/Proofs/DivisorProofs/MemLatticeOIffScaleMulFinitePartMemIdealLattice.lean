import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLsB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeilRepEqLatticeIntertwinerMulCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealExtendConjMulEqAbsNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActAApply
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIntegralSplitIdempotentOverTwo

open NumberField MeasureTheory IsDedekindDomain
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.BotClassDict (finQ)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitLatDict

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

section SlopeTestRemainingChoices

variable {D : D7}

/- English proof (translation)
Rewrite using `[FractionalIdeal.coe_coeIdeal]`. Apply `le_antisymm` to reduce the goal to its premises. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨c, hc, rfl⟩`. Conclude with `(IsLocalization.mem_coeSubmodule _ _).2 ⟨algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c, Ideal.mem_map_of_mem _ hc, rfl⟩`.

Introduce `x hx`. Take `⟨y, hy, rfl⟩` from `(IsLocalization.mem_coeSubmodule _ _).1 hx`. Establish `hy' : y ∈ Submodule.span (𝓞 D.host.E) (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) '' (D.host.ccK : Set (𝓞 D.host.K)))` using `hy`. Use `clear hx hy`. Proceed by induction on `hy' using Submodule.span_induction with`.

Consider the case `mem z hz`. Take `⟨c, hc, rfl⟩` from `hz`. Conclude with `Submodule.subset_span ⟨c, hc, rfl⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`.

Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `add_mem ha hb`. Consider the case `smul o a _ ha`. Rewrite using `[smul_eq_mul, map_mul, ← Algebra.smul_def]`. Conclude with `Submodule.smul_mem _ o ha`.
-/
theorem cE_ccK_eq (D : D7) :
    GlobalTheory.VacRead.cE D D.host.ccK =
      ((D.host.ccE : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E) := by
  rw [FractionalIdeal.coe_coeIdeal]
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨c, hc, rfl⟩
    exact (IsLocalization.mem_coeSubmodule _ _).2
      ⟨algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c, Ideal.mem_map_of_mem _ hc, rfl⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := (IsLocalization.mem_coeSubmodule _ _).1 hx
    have hy' : y ∈ Submodule.span (𝓞 D.host.E)
        (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) '' (D.host.ccK : Set (𝓞 D.host.K))) := hy
    clear hx hy
    induction hy' using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨c, hc, rfl⟩ := hz
      exact Submodule.subset_span ⟨c, hc, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul o a _ ha =>
      rw [smul_eq_mul, map_mul, ← Algebra.smul_def]
      exact Submodule.smul_mem _ o ha

/- English proof (translation)
Establish `ha' : a ∈ ((D.host.ccE : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E) * (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)`. Rewrite using `[← FractionalIdeal.coe_mul]`. Conclude with `ha`. Use `Submodule.mul_induction_on ha' (fun x hx b hb => ?_) (fun x y hx hy => ?_)` and prove the remaining obligations. Rewrite `hx` using `[← cE_ccK_eq]`.

Take `⟨o, ho⟩` from `(GlobalTheory.VacRead.conj_mul_cE_absNorm D D.host.ccK).1 γ hγ x hx`. Distinguish the cases in `hN : (Ideal.absNorm D.host.ccK : D.host.E) = 0`. Rewrite using `[hN, div_zero]`. Conclude with `zero_mem _`. Establish `e : x * b * D.host.conj γ / (Ideal.absNorm D.host.ccK : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E o * b`.

Rewrite using `[show x * b * D.host.conj γ = (D.host.conj γ * x) * b by ring, ho]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e, ← Algebra.smul_def]`. Conclude with `Submodule.smul_mem _ o hb`. Rewrite using `[add_mul, add_div]`.

Conclude with `add_mem hx hy`.
-/
theorem mul_conj_div_absNorm_mem_auxiliaryOrder {a γ : D.host.E} (ha : a ∈ D.host.AA) (hγ : γ ∈ GlobalTheory.VacRead.cE D D.host.ccK) :
    a * D.host.conj γ / (Ideal.absNorm D.host.ccK : D.host.E) ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
  have ha' : a ∈ ((D.host.ccE : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E) *
      (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
    rw [← FractionalIdeal.coe_mul]; exact ha
  refine Submodule.mul_induction_on ha' (fun x hx b hb => ?_) (fun x y hx hy => ?_)
  · rw [← cE_ccK_eq] at hx
    obtain ⟨o, ho⟩ := (GlobalTheory.VacRead.conj_mul_cE_absNorm D D.host.ccK).1 γ hγ x hx
    by_cases hN : (Ideal.absNorm D.host.ccK : D.host.E) = 0
    · rw [hN, div_zero]; exact zero_mem _
    have e : x * b * D.host.conj γ / (Ideal.absNorm D.host.ccK : D.host.E) =
        algebraMap (𝓞 D.host.E) D.host.E o * b := by
      rw [show x * b * D.host.conj γ = (D.host.conj γ * x) * b by ring, ho]
      field_simp
    rw [e, ← Algebra.smul_def]
    exact Submodule.smul_mem _ o hb
  · rw [add_mul, add_div]; exact add_mem hx hy

/- English proof (translation)
Establish `hε' : ε ∈ (D.host.ccE : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)`. Rewrite using `[← FractionalIdeal.mem_coe, ← cE_ccK_eq]`. Conclude with `hε`. Conclude with `FractionalIdeal.mul_mem_mul hε' hb`.
-/
theorem mul_mem_AA {ε b : D.host.E} (hε : ε ∈ GlobalTheory.VacRead.cE D D.host.ccK) (hb : b ∈ D.host.AA0) :
    ε * b ∈ D.host.AA := by
  have hε' : ε ∈ (D.host.ccE : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    rw [← FractionalIdeal.mem_coe, ← cE_ccK_eq]; exact hε
  exact FractionalIdeal.mul_mem_mul hε' hb

/- English proof (translation)
Proceed by induction on `hα using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨c, hc, rfl⟩` from `hy`. Introduce `x hx`. Conclude with `AddSubgroup.subset_closure ⟨c, hc, x, hx, 1, Subring.one_mem _, by rw [mul_one]⟩`.

Consider the case `zero => intro x _`. Rewrite using `[zero_mul, map_zero]`. Conclude with `zero_mem _`. Consider the case `add a b _ _ ha hb => intro x hx`. Rewrite using `[add_mul, map_add]`.

Conclude with `add_mem (ha x hx) (hb x hx)`. Consider the case `smul o a _ ha`. Introduce `x hx`. Establish `e : (o • a) * x = a * (o • x)` using `by rw [Algebra.smul_def, Algebra.smul_def]; ring`. Rewrite using `[e]`.

Conclude with `ha _ (Submodule.smul_mem _ o hx)`.
-/
theorem inc_mem_IhE {cc : Ideal (𝓞 D.host.K)} {α : D.host.E} (hα : α ∈ GlobalTheory.VacRead.cE D cc) :
    ∀ x ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), Formalism.MainNotions.StandardLatticesGL3.inc D (α * x) ∈ Formalism.MainNotions.StandardLatticesGL3.IhE D cc := by
  induction hα using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc, rfl⟩ := hy
    intro x hx
    exact AddSubgroup.subset_closure ⟨c, hc, x, hx, 1, Subring.one_mem _, by rw [mul_one]⟩
  | zero => intro x _; rw [zero_mul, map_zero]; exact zero_mem _
  | add a b _ _ ha hb => intro x hx; rw [add_mul, map_add]; exact add_mem (ha x hx) (hb x hx)
  | smul o a _ ha =>
    intro x hx
    have e : (o • a) * x = a * (o • x) := by rw [Algebra.smul_def, Algebra.smul_def]; ring
    rw [e]; exact ha _ (Submodule.smul_mem _ o hx)

/- English proof (translation)
The claim follows from `Nat.cast_ne_zero.2 fun h => hc (Ideal.absNorm_eq_zero_iff.1 h)`.
-/
theorem absNorm_ne_zero {cc : Ideal (𝓞 D.host.K)} (hc : cc ≠ ⊥) : (Ideal.absNorm cc : D.host.E) ≠ 0 :=
  Nat.cast_ne_zero.2 fun h => hc (Ideal.absNorm_eq_zero_iff.1 h)

/- English proof (translation)
Establish `hr0 : r ≠ 0` using `IsScale.ne_zero hc hr`. Establish `hN` using `absNorm_ne_zero (D := D) hc`. Establish `hs : r * D.host.conj r * ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) = ((Ideal.absNorm cc : ℕ) : D.host.E)` using `hr`. Establish `hN0 : ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ≠ 0` using `fun h => hN (by rw [← hs, h, mul_zero])`. Establish `hcr : D.host.conj r ≠ 0` using `(map_ne_zero _).2 hr0`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨α, hα, γ, hγ, rfl⟩` from `hy`. Introduce `a ha`. Establish `e : r * (a * star (r * D.host.conj α * γ / (Ideal.absNorm cc : D.host.E))) = α * (a * D.host.conj γ / (Ideal.absNorm D.host.ccK : D.host.E))`.

Rewrite using `[GlobalTheory.SplitIdem.star_eq_conj, map_div₀, map_mul, map_mul, GlobalTheory.InertSign.conj_conj, map_natCast, ← hs]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Conclude with `inc_mem_IhE hα _ (mul_conj_div_absNorm_mem_auxiliaryOrder ha hγ)`. Consider the case `zero => intro a _`.

Rewrite using `[star_zero, mul_zero, mul_zero, map_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy`. Introduce `a ha`. Rewrite using `[star_add, mul_add, mul_add, map_add]`.

Conclude with `add_mem (hx a ha) (hy a ha)`. Consider the case `smul o y _ hy`. Introduce `a ha`. Establish `hco : algebraMap (𝓞 D.host.E) D.host.E (GlobalTheory.InertSign.sgO D o) = D.host.conj (algebraMap (𝓞 D.host.E) D.host.E o)` using `rfl`. Establish `e : r * (a * star (o • y)) = r * ((GlobalTheory.InertSign.sgO D o) • a * star y)`.

Rewrite using `[Algebra.smul_def, Algebra.smul_def, GlobalTheory.SplitIdem.star_eq_conj, GlobalTheory.SplitIdem.star_eq_conj, map_mul, hco]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `hy _ ((D.host.AA : Submodule (𝓞 D.host.E) D.host.E).smul_mem _ ha)`.
-/
theorem inc_r_mem_IhE {cc : Ideal (𝓞 D.host.K)} {r : D.host.E} (hc : cc ≠ ⊥) (hr : IsScale D cc r)
    {y : D.host.E} (hy : y ∈ GlobalTheory.VacRead.bInv D cc r) :
    ∀ a ∈ D.host.AA, Formalism.MainNotions.StandardLatticesGL3.inc D (r * (a * star y)) ∈ Formalism.MainNotions.StandardLatticesGL3.IhE D cc := by
  have hr0 : r ≠ 0 := IsScale.ne_zero hc hr
  have hN := absNorm_ne_zero (D := D) hc
  have hs : r * D.host.conj r * ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) = ((Ideal.absNorm cc : ℕ) : D.host.E) := hr
  have hN0 : ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ≠ 0 := fun h => hN (by rw [← hs, h, mul_zero])
  have hcr : D.host.conj r ≠ 0 := (map_ne_zero _).2 hr0
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨α, hα, γ, hγ, rfl⟩ := hy
    intro a ha
    have e : r * (a * star (r * D.host.conj α * γ / (Ideal.absNorm cc : D.host.E))) =
        α * (a * D.host.conj γ / (Ideal.absNorm D.host.ccK : D.host.E)) := by
      rw [GlobalTheory.SplitIdem.star_eq_conj, map_div₀, map_mul, map_mul, GlobalTheory.InertSign.conj_conj, map_natCast, ← hs]
      field_simp
    rw [e]
    exact inc_mem_IhE hα _ (mul_conj_div_absNorm_mem_auxiliaryOrder ha hγ)
  | zero => intro a _; rw [star_zero, mul_zero, mul_zero, map_zero]; exact zero_mem _
  | add x y _ _ hx hy =>
    intro a ha; rw [star_add, mul_add, mul_add, map_add]; exact add_mem (hx a ha) (hy a ha)
  | smul o y _ hy =>
    intro a ha
    have hco : algebraMap (𝓞 D.host.E) D.host.E (GlobalTheory.InertSign.sgO D o) =
        D.host.conj (algebraMap (𝓞 D.host.E) D.host.E o) := rfl
    have e : r * (a * star (o • y)) = r * ((GlobalTheory.InertSign.sgO D o) • a * star y) := by
      rw [Algebra.smul_def, Algebra.smul_def, GlobalTheory.SplitIdem.star_eq_conj, GlobalTheory.SplitIdem.star_eq_conj, map_mul, hco]
      ring
    rw [e]
    exact hy _ ((D.host.AA : Submodule (𝓞 D.host.E) D.host.E).smul_mem _ ha)

/- English proof (translation)
Rewrite using `[← GlobalTheory.BotClassDict.finQ_inclR, ← map_mul]`. Use `congr 1`. Use `show _ = (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] e)`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`.
-/
theorem finQ_pair_tmul (α : Af D.host.F) (e : D.host.E) :
    finQ D (pairA D.host.F 0 α ⊗ₜ[D.host.F] e) =
      finQ D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) * Formalism.MainNotions.StandardLatticesGL3.inc D e := by
  rw [← GlobalTheory.BotClassDict.finQ_inclR, ← map_mul]
  congr 1
  show _ = (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] e)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/- English proof (translation)
Use `(GlobalTheory.BotClassDict.toAfE_int_iff _).1 ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.BotClassDict.toAfE_finQ]`. Conclude with `(GlobalTheory.IdemSupport.mem_intAE_iff _).1 (AddSubgroup.subset_closure ⟨α, hα, 1, rfl⟩)`.
-/
theorem finQ_pair_mem {α : Af D.host.F} (hα : α ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F) :
    finQ D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D := by
  refine (GlobalTheory.BotClassDict.toAfE_int_iff _).1 ?_
  rw [GlobalTheory.BotClassDict.toAfE_finQ]
  exact (GlobalTheory.IdemSupport.mem_intAE_iff _).1 (AddSubgroup.subset_closure ⟨α, hα, 1, rfl⟩)

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero, map_zero]`. Consider the case `tmul α e`. Rewrite using `[GlobalTheory.LatticeStable.liftFin_tmul]`. Use `show (Algebra.TensorProduct.map _ _) _ = 0`.

Rewrite using `[Algebra.TensorProduct.map_tmul]`. Conclude with `TensorProduct.zero_tmul _ _`. Consider the case `add x y hx hy => rw [(GlobalTheory.LatticeStable.liftFin D).map_add, (infPart D).map_add, hx, hy, add_zero]`.
-/
theorem infPart_liftFin (z : Af D.host.F ⊗[D.host.F] D.host.E) : infPart D (GlobalTheory.LatticeStable.liftFin D z) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul α e =>
    rw [GlobalTheory.LatticeStable.liftFin_tmul]
    show (Algebra.TensorProduct.map _ _) _ = 0
    rw [Algebra.TensorProduct.map_tmul]
    exact TensorProduct.zero_tmul _ _
  | add x y hx hy => rw [(GlobalTheory.LatticeStable.liftFin D).map_add, (infPart D).map_add, hx, hy, add_zero]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero, map_zero]`. Consider the case `tmul α e => rw [GlobalTheory.LatticeStable.liftFin_tmul]`. Both sides reduce to the same expression. Consider the case `add x y hx hy => rw [(GlobalTheory.LatticeStable.liftFin D).map_add, (finPart D).map_add, hx, hy]`.
-/
theorem finPart_liftFin (z : Af D.host.F ⊗[D.host.F] D.host.E) : finPart D (GlobalTheory.LatticeStable.liftFin D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul α e => rw [GlobalTheory.LatticeStable.liftFin_tmul]; rfl
  | add x y hx hy => rw [(GlobalTheory.LatticeStable.liftFin D).map_add, (finPart D).map_add, hx, hy]

/- English proof (translation)
Rewrite using `[← GlobalTheory.BotClassDict.finQ_inclR, GlobalTheory.BotClassDict.toAfE_finQ]`. Both sides reduce to the same expression.
-/
theorem toAfE_inc (e : D.host.E) :
    GlobalTheory.BotFormula.toAfE D (Formalism.MainNotions.StandardLatticesGL3.inc D e) = (1 : Af D.host.F) ⊗ₜ[D.host.F] e := by
  rw [← GlobalTheory.BotClassDict.finQ_inclR, GlobalTheory.BotClassDict.toAfE_finQ]; rfl

end SlopeTestRemainingChoices

section Main

variable {D : D7}

/- English proof (translation)
Use `AddSubgroup.subset_closure ⟨1, ?_, fun v hv => (hv trivial).elim, a, ha, Pi.single j y, ?_, Pi.single i 1, ?_, ?_⟩` and prove the remaining obligations. Introduce `v`. Rewrite using `[map_one]`. Conclude with `one_mem _`. Rewrite using `[SetLike.mem_coe, GlobalTheory.VacRead.mem_lsB]`.

Introduce `k`. Distinguish the cases in `h : k = j`. Substitute `h` using the available equality. Rewrite using `[Pi.single_eq_same]`. Conclude with `hy`.

Rewrite using `[Pi.single_eq_of_ne h]`. Conclude with `zero_mem _`. Rewrite using `[SetLike.mem_coe]`. Use `Submodule.mem_pi.2 fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : k = i`.

Substitute `h` using the available equality. Rewrite using `[Pi.single_eq_same]`. Conclude with `Submodule.mem_one.2 ⟨1, map_one _⟩`. Rewrite using `[Pi.single_eq_of_ne h]`. Conclude with `zero_mem _`.

Use extensionality with `i' j'`. Rewrite using `[hG]`. Simplify using `only [Matrix.single_apply, Matrix.of_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.single_apply]`. Apply the tactic sequence `rcases eq_or_ne i' i with rfl | h1 <;> rcases eq_or_ne j' j with rfl | h2`. Simplify using the standard rewrite rules.

Simplify using `[h2, h2.symm]`. Simplify using `[h1, h1.symm]`. Simplify using `[h1, h2, h1.symm, h2.symm]`.
-/
theorem single_mem_latO_gen (S T : HSp D) (hG : S.gram = 1) {cc : Ideal (𝓞 D.host.K)} {r : D.host.E}
    (i : Fin T.rank) (j : Fin S.rank) {a y : D.host.E} (ha : a ∈ D.host.AA) (hy : y ∈ GlobalTheory.VacRead.bInv D cc r) :
    Matrix.single i j (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (a * star y)) ∈
      latO S T (GlobalTheory.VacRead.lsB D cc r S.rank : Set (Fin S.rank → D.host.E))
        (stdL D T.rank : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  refine AddSubgroup.subset_closure ⟨1, ?_, fun v hv => (hv trivial).elim, a, ha, Pi.single j y, ?_,
    Pi.single i 1, ?_, ?_⟩
  · intro v; rw [map_one]; exact one_mem _
  · rw [SetLike.mem_coe, GlobalTheory.VacRead.mem_lsB]
    intro k
    by_cases h : k = j
    · subst h; rw [Pi.single_eq_same]; exact hy
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _
  · rw [SetLike.mem_coe]
    refine Submodule.mem_pi.2 fun k _ => ?_
    by_cases h : k = i
    · subst h; rw [Pi.single_eq_same]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _
  · ext i' j'
    rw [hG]
    simp only [Matrix.single_apply, Matrix.of_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.single_apply]
    rcases eq_or_ne i' i with rfl | h1 <;> rcases eq_or_ne j' j with rfl | h2
    · simp
    · simp [h2, h2.symm]
    · simp [h1, h1.symm]
    · simp [h1, h2, h1.symm, h2.symm]

/- English proof (translation)
Establish `hr0 : r ≠ 0` using `IsScale.ne_zero hc hr`. Establish `hN` using `absNorm_ne_zero (D := D) hc`. Establish `hs : r * D.host.conj r * ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) = ((Ideal.absNorm cc : ℕ) : D.host.E)` using `hr`. Establish `hN0 : ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ≠ 0` using `fun h => hN (by rw [← hs, h, mul_zero])`. Establish `hcr : D.host.conj r ≠ 0` using `(map_ne_zero _).2 hr0`.

Use `set c' : D.host.E := ((c : D.host.K) : D.host.E) with hc'`. Establish `key : ∀ x ∈ Submodule.span (𝓞 D.host.E) {t | ∃ α ∈ GlobalTheory.VacRead.cE D D.host.ccK, ∃ β ∈ GlobalTheory.VacRead.cE D D.host.ccK, t = D.host.conj α * β}, ∀ o : 𝓞 D.host.E, Matrix.single i j (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (r⁻¹ * (c' * a0) * (algebraMap (𝓞 D.host.E) D.host.E o …`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem z hz`.

Take `⟨γ, hγ, ε, hε, rfl⟩` from `hz`. Introduce `o`. Establish `e : r⁻¹ * (c' * a0) * (algebraMap (𝓞 D.host.E) D.host.E o * (D.host.conj γ * ε)) / (Ideal.absNorm D.host.ccK : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E o * ε * a0) * star (r * D.host.conj c' * γ / (Ideal.absNorm cc : D.host.E))`. Rewrite using `[GlobalTheory.SplitIdem.star_eq_conj, map_div₀, map_mul, map_mul, GlobalTheory.InertSign.conj_conj, map_natCast, ← hs]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e]`. Use `single_mem_latO_gen S T hG i j (mul_mem_AA ?_ ha0) (Submodule.subset_span ⟨c', Submodule.subset_span ⟨c, hcc, rfl⟩, γ, hγ, rfl⟩)` and prove the remaining obligations. Rewrite using `[← Algebra.smul_def]`. Conclude with `Submodule.smul_mem _ o hε`. Consider the case `zero`.

Introduce `o`. Rewrite using `[mul_zero, mul_zero, zero_div, TensorProduct.tmul_zero, Matrix.single_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy`. Introduce `o`.

Rewrite using `[mul_add, mul_add, add_div, TensorProduct.tmul_add, Matrix.single_add]`. Conclude with `add_mem (hx o) (hy o)`. Consider the case `smul o' x _ hx`. Introduce `o`. Establish `e : algebraMap (𝓞 D.host.E) D.host.E o * (o' • x) = algebraMap (𝓞 D.host.E) D.host.E (o * o') * x`.

Rewrite using `[Algebra.smul_def, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `hx (o * o')`. Establish `h1` using `key _ (GlobalTheory.VacRead.conj_mul_cE_absNorm D D.host.ccK).2 1`.

Establish `e : r⁻¹ * (c' * a0) * (algebraMap (𝓞 D.host.E) D.host.E 1 * (Ideal.absNorm D.host.ccK : D.host.E)) / (Ideal.absNorm D.host.ccK : D.host.E) = r⁻¹ * (c' * a0)`. Rewrite using `[map_one, one_mul, mul_div_assoc, div_self hN0, mul_one]`. Rewrite `h1` using `[e]`. Then use the resulting hypothesis.
-/
theorem single_mem_latO_core (S T : HSp D) (hG : S.gram = 1) {cc : Ideal (𝓞 D.host.K)} {r : D.host.E}
    (hc : cc ≠ ⊥) (hr : IsScale D cc r) (i : Fin T.rank) (j : Fin S.rank) {c : 𝓞 D.host.K} (hcc : c ∈ cc)
    {a0 : D.host.E} (ha0 : a0 ∈ D.host.AA0) :
    Matrix.single i j (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (r⁻¹ * (((c : D.host.K) : D.host.E) * a0))) ∈
      latO S T (GlobalTheory.VacRead.lsB D cc r S.rank : Set (Fin S.rank → D.host.E))
        (stdL D T.rank : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  have hr0 : r ≠ 0 := IsScale.ne_zero hc hr
  have hN := absNorm_ne_zero (D := D) hc
  have hs : r * D.host.conj r * ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) = ((Ideal.absNorm cc : ℕ) : D.host.E) := hr
  have hN0 : ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ≠ 0 := fun h => hN (by rw [← hs, h, mul_zero])
  have hcr : D.host.conj r ≠ 0 := (map_ne_zero _).2 hr0
  set c' : D.host.E := ((c : D.host.K) : D.host.E) with hc'
  have key : ∀ x ∈ Submodule.span (𝓞 D.host.E)
      {t | ∃ α ∈ GlobalTheory.VacRead.cE D D.host.ccK, ∃ β ∈ GlobalTheory.VacRead.cE D D.host.ccK, t = D.host.conj α * β},
      ∀ o : 𝓞 D.host.E, Matrix.single i j (pairA D.host.F 0 1 ⊗ₜ[D.host.F]
        (r⁻¹ * (c' * a0) * (algebraMap (𝓞 D.host.E) D.host.E o * x) / (Ideal.absNorm D.host.ccK : D.host.E))) ∈
        latO S T (GlobalTheory.VacRead.lsB D cc r S.rank : Set (Fin S.rank → D.host.E))
          (stdL D T.rank : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨γ, hγ, ε, hε, rfl⟩ := hz
      intro o
      have e : r⁻¹ * (c' * a0) * (algebraMap (𝓞 D.host.E) D.host.E o * (D.host.conj γ * ε)) /
          (Ideal.absNorm D.host.ccK : D.host.E) =
          (algebraMap (𝓞 D.host.E) D.host.E o * ε * a0) *
            star (r * D.host.conj c' * γ / (Ideal.absNorm cc : D.host.E)) := by
        rw [GlobalTheory.SplitIdem.star_eq_conj, map_div₀, map_mul, map_mul, GlobalTheory.InertSign.conj_conj, map_natCast, ← hs]
        field_simp
      rw [e]
      refine single_mem_latO_gen S T hG i j (mul_mem_AA ?_ ha0)
        (Submodule.subset_span ⟨c', Submodule.subset_span ⟨c, hcc, rfl⟩, γ, hγ, rfl⟩)
      rw [← Algebra.smul_def]
      exact Submodule.smul_mem _ o hε
    | zero =>
      intro o
      rw [mul_zero, mul_zero, zero_div, TensorProduct.tmul_zero, Matrix.single_zero]
      exact zero_mem _
    | add x y _ _ hx hy =>
      intro o
      rw [mul_add, mul_add, add_div, TensorProduct.tmul_add, Matrix.single_add]
      exact add_mem (hx o) (hy o)
    | smul o' x _ hx =>
      intro o
      have e : algebraMap (𝓞 D.host.E) D.host.E o * (o' • x) = algebraMap (𝓞 D.host.E) D.host.E (o * o') * x := by
        rw [Algebra.smul_def, map_mul]; ring
      rw [e]; exact hx (o * o')
  have h1 := key _ (GlobalTheory.VacRead.conj_mul_cE_absNorm D D.host.ccK).2 1
  have e : r⁻¹ * (c' * a0) * (algebraMap (𝓞 D.host.E) D.host.E 1 * (Ideal.absNorm D.host.ccK : D.host.E)) /
      (Ideal.absNorm D.host.ccK : D.host.E) = r⁻¹ * (c' * a0) := by
    rw [map_one, one_mul, mul_div_assoc, div_self hN0, mul_one]
  rwa [e] at h1

/- English proof (translation)
Set `Ψ : WO S T →+ Formalism.MainNotions.StandardLatticesGL3.AE D` to `AddMonoidHom.mk' (fun u => Formalism.MainNotions.StandardLatticesGL3.inc D r * finQ D (u i j)) (fun x y => by rw [Matrix.add_apply, (finQ D).map_add, mul_add])`. Establish `hle : latO S T (GlobalTheory.VacRead.lsB D cc r S.rank : Set (Fin S.rank → D.host.E)) (stdL D T.rank : Set (Fin T.rank → D.host.E)) (fun _ => True) ≤ (Formalism.MainNotions.StandardLatticesGL3.IhE D cc).comap Ψ`. Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩`. Use `show Formalism.MainNotions.StandardLatticesGL3.inc D r * finQ D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)) ∈ Formalism.MainNotions.StandardLatticesGL3.IhE D cc`.

Rewrite using `[hG]`. Establish `hsum : ∑ k, star (s k) * (1 : Matrix (Fin S.rank) (Fin S.rank) D.host.E) k j = star (s j)`. Simplify using `[Matrix.one_apply]`. Rewrite using `[hsum, finQ_pair_tmul, mul_left_comm, ← map_mul]`. Use `GlobalTheory.FinWeil.ihE_mul D cc (finQ_pair_mem hα) ?_` and prove the remaining obligations.

Establish `hti : t i ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)` using `(Submodule.mem_pi.1 ht) i trivial`. Take `⟨o, ho⟩` from `Submodule.mem_one.1 hti`. Establish `hsj : s j ∈ GlobalTheory.VacRead.bInv D cc r` using `GlobalTheory.VacRead.mem_lsB.1 hs j`. Establish `hat : a * t i ∈ D.host.AA`. Rewrite using `[← ho, mul_comm, ← Algebra.smul_def]`.

Conclude with `(D.host.AA : Submodule (𝓞 D.host.E) D.host.E).smul_mem o ha`. Conclude with `inc_r_mem_IhE hc hr hsj _ hat`. Conclude with `hle hu`.
-/
theorem fwd {cc : Ideal (𝓞 D.host.K)} {r : D.host.E} (hc : cc ≠ ⊥) (hr : IsScale D cc r)
    (S T : HSp D) (hG : S.gram = 1) (u : WO S T)
    (hu : u ∈ latO S T (GlobalTheory.VacRead.lsB D cc r S.rank : Set (Fin S.rank → D.host.E))
        (stdL D T.rank : Set (Fin T.rank → D.host.E)) (fun _ => True)) (i : Fin T.rank) (j : Fin S.rank) :
    Formalism.MainNotions.StandardLatticesGL3.inc D r * finQ D (u i j) ∈ Formalism.MainNotions.StandardLatticesGL3.IhE D cc := by
  let Ψ : WO S T →+ Formalism.MainNotions.StandardLatticesGL3.AE D := AddMonoidHom.mk' (fun u => Formalism.MainNotions.StandardLatticesGL3.inc D r * finQ D (u i j))
    (fun x y => by rw [Matrix.add_apply, (finQ D).map_add, mul_add])
  have hle : latO S T (GlobalTheory.VacRead.lsB D cc r S.rank : Set (Fin S.rank → D.host.E))
      (stdL D T.rank : Set (Fin T.rank → D.host.E)) (fun _ => True) ≤ (Formalism.MainNotions.StandardLatticesGL3.IhE D cc).comap Ψ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩
    show Formalism.MainNotions.StandardLatticesGL3.inc D r * finQ D (pairA D.host.F 0 α ⊗ₜ[D.host.F]
      (a * t i * ∑ k, star (s k) * S.gram k j)) ∈ Formalism.MainNotions.StandardLatticesGL3.IhE D cc
    rw [hG]
    have hsum : ∑ k, star (s k) * (1 : Matrix (Fin S.rank) (Fin S.rank) D.host.E) k j = star (s j) := by
      simp [Matrix.one_apply]
    rw [hsum, finQ_pair_tmul, mul_left_comm, ← map_mul]
    refine GlobalTheory.FinWeil.ihE_mul D cc (finQ_pair_mem hα) ?_
    have hti : t i ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := (Submodule.mem_pi.1 ht) i trivial
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 hti
    have hsj : s j ∈ GlobalTheory.VacRead.bInv D cc r := GlobalTheory.VacRead.mem_lsB.1 hs j
    have hat : a * t i ∈ D.host.AA := by
      rw [← ho, mul_comm, ← Algebra.smul_def]
      exact (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).smul_mem o ha
    exact inc_r_mem_IhE hc hr hsj _ hat
  exact hle hu

set_option maxHeartbeats 400000 in
/- English proof (translation)
Establish `hr0 : r ≠ 0` using `IsScale.ne_zero hc hr`. Rewrite using `[Matrix.matrix_eq_sum_single u]`. Use `sum_mem fun i _ => sum_mem fun j _ => ?_` and prove the remaining obligations. Set `Φ : Formalism.MainNotions.StandardLatticesGL3.AE D →+ WO S T` to `AddMonoidHom.mk' (fun x => Matrix.single i j (GlobalTheory.LatticeStable.liftFin D (GlobalTheory.BotFormula.toAfE D (Formalism.MainNotions.StandardLatticesGL3.inc D r⁻¹ * x)))) (fun x y => by rw [mul_add, (GlobalTheory.BotFormula.toAfE D).map_add, (GlobalTheory.LatticeStable.lift …`. Establish `hle : Formalism.MainNotions.StandardLatticesGL3.IhE D cc ≤ (latO S T (GlobalTheory.VacRead.lsB D cc r S.rank : Set (Fin S.rank → D.host.E)) (stdL D T.rank : Set (Fin T.rank → D.host.E)) (fun _ => True)).comap Φ`.

Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨c, hcc, a0, ha0, s, hsO, rfl⟩`. Use `show Matrix.single i j (GlobalTheory.LatticeStable.liftFin D (GlobalTheory.BotFormula.toAfE D (Formalism.MainNotions.StandardLatticesGL3.inc D r⁻¹ * (Formalism.MainNotions.StandardLatticesGL3.inc D (((c : D.host.K) : D.host.E) * a0) * s)))) ∈ latO S T (GlobalTheory.VacRead.lsB D …`. Establish `hw : finPart D (GlobalTheory.LatticeStable.liftFin D (GlobalTheory.BotFormula.toAfE D s)) ∈ intAE D`. Rewrite using `[finPart_liftFin]`.

Conclude with `(GlobalTheory.IdemSupport.mem_intAE_iff _).2 ((GlobalTheory.BotClassDict.toAfE_int_iff s).2 hsO)`. Establish `e : Matrix.single i j (GlobalTheory.LatticeStable.liftFin D (GlobalTheory.BotFormula.toAfE D (Formalism.MainNotions.StandardLatticesGL3.inc D r⁻¹ * (Formalism.MainNotions.StandardLatticesGL3.inc D (((c : D.host.K) : D.host.E) * a0) * s)))) = GlobalTheory.LatticeStable.liftFin D ( …`. Rewrite using `[Matrix.smul_single]`. Use `congr 1`. Rewrite using `[smul_eq_mul]`.

Apply `GlobalTheory.SplitScalar.adele_ext` to reduce the goal to its premises. Rewrite using `[infPart_liftFin, (infPart D).map_mul, infPart_liftFin, zero_mul]`. Rewrite using `[finPart_liftFin, (finPart D).map_mul, finPart_liftFin] show _ = _ * ((1 : Af D.host.F) ⊗ₜ[D.host.F] (r⁻¹ * (((c : D.host.K) : D.host.E) * a0)))`. Rewrite using `[← toAfE_inc, ← (GlobalTheory.BotFormula.toAfE D).map_mul]`. Use `congr 1`.

Rewrite using `[(Formalism.MainNotions.StandardLatticesGL3.inc D).map_mul r⁻¹]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ hw _ (single_mem_latO_core S T hG hc hr i j hcc ha0)`. Establish `e1 : Formalism.MainNotions.StandardLatticesGL3.inc D r⁻¹ * (Formalism.MainNotions.StandardLatticesGL3.inc D r * finQ D (u i j)) = finQ D (u i j)`.

Rewrite using `[← mul_assoc, ← map_mul (Formalism.MainNotions.StandardLatticesGL3.inc D), inv_mul_cancel₀ hr0, map_one, one_mul]`. Establish `e2 : GlobalTheory.LatticeStable.liftFin D (GlobalTheory.BotFormula.toAfE D (finQ D (u i j))) = u i j`. Rewrite using `[GlobalTheory.BotClassDict.toAfE_finQ]`. Apply `GlobalTheory.SplitScalar.adele_ext` to reduce the goal to its premises. Rewrite using `[infPart_liftFin]`.

Conclude with `(congrFun (congrFun hinf i) j).symm`. Rewrite using `[finPart_liftFin]`. Both sides reduce to the same expression. Establish `hij : Matrix.single i j (u i j) = Φ (Formalism.MainNotions.StandardLatticesGL3.inc D r * finQ D (u i j))` using `by show _ = Matrix.single i j (GlobalTheory.LatticeStable.liftFin D (GlobalTheory.BotFormula.toAfE D (Formalism.MainNotions.StandardLatticesGL3.inc D r⁻¹ * (Formalism.MainNotions.StandardLatticesGL3.inc D r * finQ D (u i j)))))`. Rewrite using `[e1, e2]`.

Rewrite using `[hij]`. Conclude with `hle (h i j)`.
-/
theorem bwd {cc : Ideal (𝓞 D.host.K)} {r : D.host.E} (hc : cc ≠ ⊥) (hr : IsScale D cc r)
    (S T : HSp D) (hG : S.gram = 1) (u : WO S T) (hinf : u.map (infPart D) = 0)
    (h : ∀ i j, Formalism.MainNotions.StandardLatticesGL3.inc D r * finQ D (u i j) ∈ Formalism.MainNotions.StandardLatticesGL3.IhE D cc) :
    u ∈ latO S T (GlobalTheory.VacRead.lsB D cc r S.rank : Set (Fin S.rank → D.host.E))
        (stdL D T.rank : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  have hr0 : r ≠ 0 := IsScale.ne_zero hc hr
  rw [Matrix.matrix_eq_sum_single u]
  refine sum_mem fun i _ => sum_mem fun j _ => ?_
  let Φ : Formalism.MainNotions.StandardLatticesGL3.AE D →+ WO S T := AddMonoidHom.mk'
    (fun x => Matrix.single i j (GlobalTheory.LatticeStable.liftFin D (GlobalTheory.BotFormula.toAfE D (Formalism.MainNotions.StandardLatticesGL3.inc D r⁻¹ * x))))
    (fun x y => by rw [mul_add, (GlobalTheory.BotFormula.toAfE D).map_add, (GlobalTheory.LatticeStable.liftFin D).map_add, Matrix.single_add])
  have hle : Formalism.MainNotions.StandardLatticesGL3.IhE D cc ≤ (latO S T (GlobalTheory.VacRead.lsB D cc r S.rank : Set (Fin S.rank → D.host.E))
      (stdL D T.rank : Set (Fin T.rank → D.host.E)) (fun _ => True)).comap Φ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨c, hcc, a0, ha0, s, hsO, rfl⟩
    show Matrix.single i j (GlobalTheory.LatticeStable.liftFin D (GlobalTheory.BotFormula.toAfE D
      (Formalism.MainNotions.StandardLatticesGL3.inc D r⁻¹ * (Formalism.MainNotions.StandardLatticesGL3.inc D (((c : D.host.K) : D.host.E) * a0) * s)))) ∈
      latO S T (GlobalTheory.VacRead.lsB D cc r S.rank : Set (Fin S.rank → D.host.E))
        (stdL D T.rank : Set (Fin T.rank → D.host.E)) (fun _ => True)
    have hw : finPart D (GlobalTheory.LatticeStable.liftFin D (GlobalTheory.BotFormula.toAfE D s)) ∈ intAE D := by
      rw [finPart_liftFin]
      exact (GlobalTheory.IdemSupport.mem_intAE_iff _).2 ((GlobalTheory.BotClassDict.toAfE_int_iff s).2 hsO)
    have e : Matrix.single i j (GlobalTheory.LatticeStable.liftFin D (GlobalTheory.BotFormula.toAfE D
        (Formalism.MainNotions.StandardLatticesGL3.inc D r⁻¹ * (Formalism.MainNotions.StandardLatticesGL3.inc D (((c : D.host.K) : D.host.E) * a0) * s)))) =
        GlobalTheory.LatticeStable.liftFin D (GlobalTheory.BotFormula.toAfE D s) •
          Matrix.single i j (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (r⁻¹ * (((c : D.host.K) : D.host.E) * a0))) := by
      rw [Matrix.smul_single]
      congr 1
      rw [smul_eq_mul]
      apply GlobalTheory.SplitScalar.adele_ext
      · rw [infPart_liftFin, (infPart D).map_mul, infPart_liftFin, zero_mul]
      · rw [finPart_liftFin, (finPart D).map_mul, finPart_liftFin]
        show _ = _ * ((1 : Af D.host.F) ⊗ₜ[D.host.F] (r⁻¹ * (((c : D.host.K) : D.host.E) * a0)))
        rw [← toAfE_inc, ← (GlobalTheory.BotFormula.toAfE D).map_mul]
        congr 1
        rw [(Formalism.MainNotions.StandardLatticesGL3.inc D).map_mul r⁻¹]
        ring
    rw [e]
    exact GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ hw _ (single_mem_latO_core S T hG hc hr i j hcc ha0)
  have e1 : Formalism.MainNotions.StandardLatticesGL3.inc D r⁻¹ * (Formalism.MainNotions.StandardLatticesGL3.inc D r * finQ D (u i j)) = finQ D (u i j) := by
    rw [← mul_assoc, ← map_mul (Formalism.MainNotions.StandardLatticesGL3.inc D), inv_mul_cancel₀ hr0, map_one, one_mul]
  have e2 : GlobalTheory.LatticeStable.liftFin D (GlobalTheory.BotFormula.toAfE D (finQ D (u i j))) = u i j := by
    rw [GlobalTheory.BotClassDict.toAfE_finQ]
    apply GlobalTheory.SplitScalar.adele_ext
    · rw [infPart_liftFin]; exact (congrFun (congrFun hinf i) j).symm
    · rw [finPart_liftFin]; rfl
  have hij : Matrix.single i j (u i j) = Φ (Formalism.MainNotions.StandardLatticesGL3.inc D r * finQ D (u i j)) := by
    show _ = Matrix.single i j (GlobalTheory.LatticeStable.liftFin D (GlobalTheory.BotFormula.toAfE D
      (Formalism.MainNotions.StandardLatticesGL3.inc D r⁻¹ * (Formalism.MainNotions.StandardLatticesGL3.inc D r * finQ D (u i j)))))
    rw [e1, e2]
  rw [hij]
  exact hle (h i j)

end Main

/- English proof (translation)
Introduce `D S T hG cc r hc hr u hinf`. Conclude with `⟨fun hu i j => fwd hc hr S T hG u hu i j, fun h => bwd hc hr S T hG u hinf h⟩`.
-/
theorem mem_latO_iff_ihE : ∀ (D : D7) (S T : HSp D), S.gram = 1 → ∀ (cc : Ideal (𝓞 D.host.K)) (r : D.host.E), cc ≠ ⊥ → IsScale D cc r →
  ∀ u : WO S T, u.map (infPart D) = 0 →
  (u ∈ latO S T (GlobalTheory.VacRead.lsB D cc r S.rank : Set (Fin S.rank → D.host.E)) (stdL D T.rank : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔
    ∀ i j, Formalism.MainNotions.StandardLatticesGL3.inc D r * finQ D (u i j) ∈ Formalism.MainNotions.StandardLatticesGL3.IhE D cc) := by
  intro D S T hG cc r hc hr u hinf
  exact ⟨fun hu i j => fwd hc hr S T hG u hu i j, fun h => bwd hc hr S T hG u hinf h⟩

end GlobalTheory.SplitLatDict
