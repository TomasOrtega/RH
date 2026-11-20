import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalPeriodRingsDataUnramifiedLaws
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

/- English proof (translation)
Introduce `l _ C H K b hb hx`. Establish `hK` using `K.2`. Establish `hidx : (GK K).index ≠ 0`. Rewrite using `[GK, ← IntermediateField.finrank_eq_fixingSubgroup_index]`. Conclude with `Module.finrank_pos.ne'`.

Establish `hfin : Fintype (GQ l ⧸ GK K)` using `Subgroup.fintypeOfIndexNeZero hidx`. Establish `hmul : ∀ (g h : GQ l) (x : Per.Bcris l), Per.σB (g * h) x = Per.σB g (Per.σB h x)` using `(ActLaws.act_laws l).1`. Establish `hone : ∀ x : Per.Bcris l, Per.σB (1 : GQ l) x = x` using `(ActLaws.act_laws l).2.1`. Establish `hinv : ∀ (g : GQ l) (x : Per.Bcris l), Per.σB g⁻¹ (Per.σB g x) = x` using `fun g x => by`. Rewrite using `[← hmul, inv_mul_cancel, hone]`.

Establish `hfix : ∀ (g : GQ l) (x : ℚ_[l]), Per.σB g (C.qB x) = C.qB x` using `fun g x => (ULaws.u_laws l C).2.1 g _ _ (g.commutes x)`. Establish `hD : IsDomain (Per.BdR l)` using `(BdRField.bdR_isField l).2.2.1.isDomain`. Establish `hB : IsDomain (Per.Bcris l)` using `(ULaws.u_laws l C).2.2.2.1.isDomain C.ι`. Establish `fout : ∀ g : GQ l, ∃ x : ℚ_[l], Per.σB g b = C.qB x * Per.σB (g : GQ l ⧸ GK K).out b` using `fun g => by`. Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul (GK K) g`.

Take `⟨x, hx'⟩` from `hx (h : GQ l)⁻¹ (inv_mem h.2)`. Use `⟨x, ?_⟩` and prove the remaining obligations. Rewrite using `[← hfix (g : GQ l ⧸ GK K).out x, ← map_mul, ← hx', ← hmul, hh, mul_inv_cancel_right]`. Use `choose c hc using fout`. Establish `hP : IsUnit (∏ q : GQ l ⧸ GK K, Per.σB q.out b)`.

Use `H _ (Finset.prod_ne_zero_iff.2 fun q _ h0 => hb ?_) fun g => ⟨∏ q : GQ l ⧸ GK K, c (g * q.out), ?_⟩` and prove the remaining obligations. Rewrite using `[← hinv q.out b, h0, map_zero]`. Rewrite using `[map_prod, map_prod, ← Equiv.prod_comp (MulAction.toPerm g) fun q : GQ l ⧸ GK K => Per.σB q.out b, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun q _ => ?_` and prove the remaining obligations. Establish `e : MulAction.toPerm g q = ((g * q.out : GQ l) : GQ l ⧸ GK K)`.

Rewrite using `[MulAction.toPerm_apply, ← smul_eq_mul, MulAction.Quotient.mk_smul_out]`. Rewrite using `[e, ← hmul, ← hc]`. Establish `hu` using `isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun q : GQ l ⧸ GK K => Per.σB q.out b) (Finset.mem_univ ((1 : GQ l) : GQ l ⧸ GK K))) hP`. Use `hu.map (Per.σB (((1 : GQ l) : GQ l ⧸ GK K).out)⁻¹)` as an intermediate fact. Rewrite `this` using `[hinv]`. Then use the resulting hypothesis.
-/
theorem regular_of_full : ∀ (l : ℕ) [Fact l.Prime] (C : Core l), (∀ b : Per.Bcris l, b ≠ 0 → (∀ g : GQ l, ∃ x : ℚ_[l], Per.σB g b = C.qB x * b) → IsUnit b) → C.Regular := by
  intro l _ C H K b hb hx
  classical
  have hK := K.2
  have hidx : (GK K).index ≠ 0 := by
    rw [GK, ← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact Module.finrank_pos.ne'
  have hfin : Fintype (GQ l ⧸ GK K) := Subgroup.fintypeOfIndexNeZero hidx
  have hmul : ∀ (g h : GQ l) (x : Per.Bcris l), Per.σB (g * h) x = Per.σB g (Per.σB h x) :=
    (ActLaws.act_laws l).1
  have hone : ∀ x : Per.Bcris l, Per.σB (1 : GQ l) x = x := (ActLaws.act_laws l).2.1
  have hinv : ∀ (g : GQ l) (x : Per.Bcris l), Per.σB g⁻¹ (Per.σB g x) = x := fun g x => by
    rw [← hmul, inv_mul_cancel, hone]
  have hfix : ∀ (g : GQ l) (x : ℚ_[l]), Per.σB g (C.qB x) = C.qB x := fun g x =>
    (ULaws.u_laws l C).2.1 g _ _ (g.commutes x)
  have hD : IsDomain (Per.BdR l) := (BdRField.bdR_isField l).2.2.1.isDomain
  have hB : IsDomain (Per.Bcris l) := (ULaws.u_laws l C).2.2.2.1.isDomain C.ι
  have fout : ∀ g : GQ l, ∃ x : ℚ_[l], Per.σB g b = C.qB x * Per.σB (g : GQ l ⧸ GK K).out b := fun g => by
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (GK K) g
    obtain ⟨x, hx'⟩ := hx (h : GQ l)⁻¹ (inv_mem h.2)
    refine ⟨x, ?_⟩
    rw [← hfix (g : GQ l ⧸ GK K).out x, ← map_mul, ← hx', ← hmul, hh, mul_inv_cancel_right]
  choose c hc using fout
  have hP : IsUnit (∏ q : GQ l ⧸ GK K, Per.σB q.out b) := by
    refine H _ (Finset.prod_ne_zero_iff.2 fun q _ h0 => hb ?_) fun g => ⟨∏ q : GQ l ⧸ GK K, c (g * q.out), ?_⟩
    · rw [← hinv q.out b, h0, map_zero]
    · rw [map_prod, map_prod,
        ← Equiv.prod_comp (MulAction.toPerm g) fun q : GQ l ⧸ GK K => Per.σB q.out b,
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun q _ => ?_
      have e : MulAction.toPerm g q = ((g * q.out : GQ l) : GQ l ⧸ GK K) := by
        rw [MulAction.toPerm_apply, ← smul_eq_mul, MulAction.Quotient.mk_smul_out]
      rw [e, ← hmul, ← hc]
  have hu := isUnit_of_dvd_unit
    (Finset.dvd_prod_of_mem (fun q : GQ l ⧸ GK K => Per.σB q.out b) (Finset.mem_univ ((1 : GQ l) : GQ l ⧸ GK K))) hP
  have := hu.map (Per.σB (((1 : GQ l) : GQ l ⧸ GK K).out)⁻¹)
  rwa [hinv] at this

end GlobalTheory.MemLoc
