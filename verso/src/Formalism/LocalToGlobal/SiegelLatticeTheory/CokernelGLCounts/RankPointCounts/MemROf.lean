import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SgnConjIntUp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityUnderRingMap.MemIntegerOfIsIntegralMap

noncomputable section

open scoped Classical Matrix
open ValuativeRel

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Split

variable {D : D7} (Z : LocDat D) (p : PlF D) (g : Formalism.MainNotions.S.Loc.SplitG (Z.M p).L)

/- English proof (translation)
Rewrite `hx` using `[(Z.M p).L.O_def]`. Establish `h` using `hx.map (g.e.toAlgHom.restrictScalars 𝒪[(D.s.atP p).Fp])`. Establish `h1` using `h.map ((AlgHom.fst (D.s.atP p).Fp (D.s.atP p).Fp (D.s.atP p).Fp).restrictScalars 𝒪[(D.s.atP p).Fp])`. Establish `h2` using `h.map ((AlgHom.snd (D.s.atP p).Fp (D.s.atP p).Fp (D.s.atP p).Fp).restrictScalars 𝒪[(D.s.atP p).Fp])`. Conclude with `⟨PI.IntegralDiscriminantMembership.mem_integer_of_isIntegral h1, PI.IntegralDiscriminantMembership.mem_integer_of_isIntegral h2⟩`.
-/
theorem comp_mem {x : (D.s.atP p).Ep} (hx : x ∈ (Z.M p).L.O) :
    (g.e x).1 ∈ 𝒪[(D.s.atP p).Fp] ∧ (g.e x).2 ∈ 𝒪[(D.s.atP p).Fp] := by
  rw [(Z.M p).L.O_def] at hx
  have h := hx.map (g.e.toAlgHom.restrictScalars 𝒪[(D.s.atP p).Fp])
  have h1 := h.map ((AlgHom.fst (D.s.atP p).Fp (D.s.atP p).Fp (D.s.atP p).Fp).restrictScalars 𝒪[(D.s.atP p).Fp])
  have h2 := h.map ((AlgHom.snd (D.s.atP p).Fp (D.s.atP p).Fp (D.s.atP p).Fp).restrictScalars 𝒪[(D.s.atP p).Fp])
  exact ⟨PI.IntegralDiscriminantMembership.mem_integer_of_isIntegral h1, PI.IntegralDiscriminantMembership.mem_integer_of_isIntegral h2⟩

/- English proof (translation)
Unfold `Formalism.MainNotions.S.Loc.Model.R`. Rewrite using `[hs]`. Simplify using `only [Subring.mem_comap, Subring.mem_map]`. Use `⟨(⟨(g.e x).1, h1⟩, ⟨(g.e x).2, h2⟩), ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [RingHom.mem_eqLocus, RingHom.comp_apply]`.

Rewrite using `[Ideal.Quotient.eq, Ideal.mem_span_singleton']`. Take `⟨o, ho, he⟩` from `h3`. Use `⟨⟨o, ho⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Use `show o * (g.q : (D.s.atP p).Fp) = (g.e x).1 - (g.e x).2`.

Rewrite using `[he, mul_comm]`. Both sides reduce to the same expression.
-/
theorem mem_R_of (hs : (Z.M p).split = some g) {x : (D.s.atP p).Ep}
    (h1 : (g.e x).1 ∈ 𝒪[(D.s.atP p).Fp]) (h2 : (g.e x).2 ∈ 𝒪[(D.s.atP p).Fp])
    (h3 : ∃ o ∈ 𝒪[(D.s.atP p).Fp], (g.e x).1 - (g.e x).2 = (g.q : (D.s.atP p).Fp) * o) : x ∈ (Z.M p).R := by
  unfold Formalism.MainNotions.S.Loc.Model.R
  rw [hs]
  simp only [Subring.mem_comap, Subring.mem_map]
  refine ⟨(⟨(g.e x).1, h1⟩, ⟨(g.e x).2, h2⟩), ?_, ?_⟩
  · simp only [RingHom.mem_eqLocus, RingHom.comp_apply]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
    obtain ⟨o, ho, he⟩ := h3
    refine ⟨⟨o, ho⟩, ?_⟩
    apply Subtype.ext
    show o * (g.q : (D.s.atP p).Fp) = (g.e x).1 - (g.e x).2
    rw [he, mul_comm]
  · rfl

def emap (Y : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) :
    Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
  Matrix.of fun a b => g.e.symm ((g.e (Y a b)).1 / (g.q : (D.s.atP p).Fp), -((g.e (Y b a)).2 / (g.q : (D.s.atP p).Fp)))

def lmat (l ρ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) :
    Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
  Matrix.of fun a b => g.e.symm ((g.e (l a b)).1, (g.e (ρ b a)).2)

/- English proof (translation)
Use extensionality with `a b`. Apply `g.e.injective` to reduce the goal to its premises. Simplify using `only [emap, lmat, Matrix.mul_apply, Matrix.of_apply, map_sum, map_mul, AlgEquiv.apply_symm_apply]`. Use `ext`. Simplify using `only [Prod.fst_sum, Prod.fst_mul, Finset.sum_div]`.

Use `Finset.sum_congr rfl (fun c _ => ?_)` and prove the remaining obligations. Simplify using `only [Finset.sum_mul, Finset.sum_div]`. Use `Finset.sum_congr rfl (fun d _ => ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Prod.snd_sum, Prod.snd_mul, Finset.sum_mul, Finset.mul_sum, Finset.sum_div, neg_div, ← Finset.sum_neg_distrib, mul_neg, neg_mul]`.

Use `Finset.sum_comm.trans (Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem emap_mul (l Y ρ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) :
    emap Z p g (l * Y * ρ) = lmat Z p g l ρ * emap Z p g Y * lmat Z p g ρ l := by
  ext a b
  apply g.e.injective
  simp only [emap, lmat, Matrix.mul_apply, Matrix.of_apply, map_sum, map_mul, AlgEquiv.apply_symm_apply]
  ext
  · simp only [Prod.fst_sum, Prod.fst_mul, Finset.sum_div]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    simp only [Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    ring
  · simp only [Prod.snd_sum, Prod.snd_mul, Finset.sum_mul, Finset.mul_sum, Finset.sum_div, neg_div,
      ← Finset.sum_neg_distrib, mul_neg, neg_mul]
    refine Finset.sum_comm.trans (Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_)
    ring

end Split

end Formalism.L2.SG.Pf.FibQ
