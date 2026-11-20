import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.EllFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.CasComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.FrameAd
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.OneTmulMemCenter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfCharInfCharOfCommute
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

namespace UpperTheory.V.Lit.Bor.CasimirCentre

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Use `Algebra.adjoin_induction (p := fun x _ => Commute x (act o)) ?_ (fun r => Algebra.commutes r _) (fun _ _ _ _ hx hy => hx.add_left hy) (fun _ _ _ _ hx hy => hx.mul_left hy) hz` and prove the remaining obligations. Introduce and unpack `_ ⟨τ, u, rfl⟩`. Consider the cases of `o with`. Consider the case `fin k => exact commute_cap_finRep τ u k`. Consider the case `cpt k => exact GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _`.

Consider the case `lie X => exact commute_cap_lie τ u X`.
-/
private theorem zalg_commute {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) (o : Op E a) : Commute z (act o) := by
  refine Algebra.adjoin_induction (p := fun x _ => Commute x (act o)) ?_ (fun r => Algebra.commutes r _)
    (fun _ _ _ _ hx hy => hx.add_left hy) (fun _ _ _ _ hx hy => hx.mul_left hy) hz
  rintro _ ⟨τ, u, rfl⟩
  cases o with
  | fin k => exact commute_cap_finRep τ u k
  | cpt k => exact GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _
  | lie X => exact commute_cap_lie τ u X

/- English proof (translation)
Rewrite using `[shift_apply, shift_apply, map_add, Cm.uC_ιC, ← algebraMap_smul ℂ (r * ell E a X) (1 : Cm.UC E a), map_smul, map_one, algebraMap_smul]`.
-/
private theorem uC_shift (r : ℝ) (X : Lie E a) : Cm.uC E a (shift (Cm.ιC E a) r X) = shift (lie E a) r X := by
  rw [shift_apply, shift_apply, map_add, Cm.uC_ιC, ← algebraMap_smul ℂ (r * ell E a X) (1 : Cm.UC E a), map_smul,
    map_one, algebraMap_smul]

/- English proof (translation)
Establish `hle : Algebra.adjoin ℂ {x : Cm.UC E a | ∃ τ i j, x = Cm.genC τ i j} ≤ Subalgebra.centralizer ℂ {z}`. Use `Algebra.adjoin_le ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨τ, i, j, rfl⟩ _ rfl`. Conclude with `(((h _).sub_right ((h _).smul_right _)).smul_right _).eq`. Rewrite `hle` using `[Cm.adjoin_genC]`.

Conclude with `Subalgebra.mem_center_iff.2 fun x => (hle Algebra.mem_top z rfl).symm`.
-/
private theorem center_of {z : Cm.UC E a} (h : ∀ X, Commute z (Cm.ιC E a X)) : z ∈ Subalgebra.center ℂ (Cm.UC E a) := by
  have hle : Algebra.adjoin ℂ {x : Cm.UC E a | ∃ τ i j, x = Cm.genC τ i j} ≤ Subalgebra.centralizer ℂ {z} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨τ, i, j, rfl⟩ _ rfl
    exact (((h _).sub_right ((h _).smul_right _)).smul_right _).eq
  rw [Cm.adjoin_genC] at hle
  exact Subalgebra.mem_center_iff.2 fun x => (hle Algebra.mem_top z rfl).symm

end UpperTheory.V.Lit.Bor.CasimirCentre

open UpperTheory.V.Lit.Bor.CasimirCentre in
/- English proof (translation)
Introduce `E _ _ _ a n e he π r`. Establish `hL : IsLieHom (shift (Cm.ιC E a) r)` using `(ellFacts E a).2.2.2 _ _ r Cm.isLieHom_ιC`. Establish `hc : cas (shift (Cm.ιC E a) r) e ∈ Subalgebra.center ℂ (Cm.UC E a)` using `center_of fun X => by`. Establish `h` using `casComm E a n e he _ _ hL X`. Establish `h' : Cm.ιC E a X = shift (Cm.ιC E a) r X - (r * ell E a X) • 1` using `by rw [shift_apply, add_sub_cancel_right]`.

Rewrite using `[h']`. Conclude with `h.sub_right ((Commute.one_right _).smul_right _)`. Establish `hz : cas (shift (lie E a) r) e ∈ Zalg E a`. Rewrite using `[Cm.Zalg_eq_map]`. Conclude with `⟨_, hc, by simp only [cas, map_sum, map_sub, map_mul, uC_shift, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]⟩`.

Conclude with `π.exists_scalar hz (zalg_commute hz)`.
-/
theorem UpperTheory.V.Lit.Bor.casPi :
    UpperTheory.V.Lit.Bor.CasPi := by
  intro E _ _ _ a n e he π r
  have hL : IsLieHom (shift (Cm.ιC E a) r) := (ellFacts E a).2.2.2 _ _ r Cm.isLieHom_ιC
  have hc : cas (shift (Cm.ιC E a) r) e ∈ Subalgebra.center ℂ (Cm.UC E a) := center_of fun X => by
    have h := casComm E a n e he _ _ hL X
    have h' : Cm.ιC E a X = shift (Cm.ιC E a) r X - (r * ell E a X) • 1 := by rw [shift_apply, add_sub_cancel_right]
    rw [h']
    exact h.sub_right ((Commute.one_right _).smul_right _)
  have hz : cas (shift (lie E a) r) e ∈ Zalg E a := by
    rw [Cm.Zalg_eq_map]
    exact ⟨_, hc, by simp only [cas, map_sum, map_sub, map_mul, uC_shift, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]⟩
  exact π.exists_scalar hz (zalg_commute hz)
