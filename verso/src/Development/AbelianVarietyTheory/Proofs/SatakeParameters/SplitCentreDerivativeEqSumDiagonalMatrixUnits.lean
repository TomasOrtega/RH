import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitarisableOfIsLocCompCusp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalLetterCentralExponentProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalLetterRealExponentEqZeroIffIsUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

namespace GlobalTheory.CuspRep.ZcTrace

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

def conjPerm : Equiv.Perm (E →+* ℂ) where
  toFun := ComplexEmbedding.conjugate
  invFun := ComplexEmbedding.conjugate
  left_inv τ := by ext x; simp [ComplexEmbedding.conjugate_coe_eq]
  right_inv τ := by ext x; simp [ComplexEmbedding.conjugate_coe_eq]

/- English proof (translation)
Establish `e : ∀ τ : E →+* ℂ, atEmb (conjPerm τ) Complex.I = -atEmb τ Complex.I`. Introduce `τ`. Express the relevant statement in the definitionally equal form `atEmb (ComplexEmbedding.conjugate τ) Complex.I = _`. Rewrite using `[atEmb_conj, Complex.conj_I, atEmb_eq]`. Simplify using the standard rewrite rules.

Establish `h` using `Equiv.sum_comp (conjPerm (E := E)) (fun τ => atEmb τ Complex.I)`. Simplify using `only [e, Finset.sum_neg_distrib] at h`. Establish `h2 : (2 : ℝ) • ∑ τ : E →+* ℂ, atEmb τ Complex.I = 0`. Rewrite using `[two_smul]`. Use `nth_rewrite 1 [← h]`.

Simplify using the standard rewrite rules. Conclude with `(smul_eq_zero.1 h2).resolve_left two_ne_zero`.
-/
theorem sum_atEmb_I : ∑ τ : E →+* ℂ, atEmb τ Complex.I = 0 := by
  have e : ∀ τ : E →+* ℂ, atEmb (conjPerm τ) Complex.I = -atEmb τ Complex.I := by
    intro τ
    change atEmb (ComplexEmbedding.conjugate τ) Complex.I = _
    rw [atEmb_conj, Complex.conj_I, atEmb_eq]; simp
  have h := Equiv.sum_comp (conjPerm (E := E)) (fun τ => atEmb τ Complex.I)
  simp only [e, Finset.sum_neg_distrib] at h
  have h2 : (2 : ℝ) • ∑ τ : E →+* ℂ, atEmb τ Complex.I = 0 := by
    rw [two_smul]; nth_rewrite 1 [← h]; simp
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

/- English proof (translation)
Establish `e : ∀ τ : E →+* ℂ, atEmb τ 1 = Pi.single (InfinitePlace.mk τ) 1`. Apply the tactic sequence `intro τ; unfold atEmb; split_ifs <;> simp`. Simplify using `only [e]`. Use function extensionality and compare the values at `w`. Rewrite using `[Finset.sum_apply]`.

Simplify using `only [Pi.single_apply, Finset.sum_boole]`. Establish `hc : (Finset.univ.filter fun τ : E →+* ℂ => w = InfinitePlace.mk τ).card = 2`. Use `InfinitePlace.card_filter_mk_eq w` as an intermediate fact. Rewrite `this` using `[InfinitePlace.mult_isComplex ⟨w, IsTotallyComplex.isComplex w⟩]`. Rewrite using `[← this]`.

Use `congr 1`. Use extensionality with `τ`. Simplify using `[eq_comm]`. Rewrite using `[hc]`. Simplify using the standard rewrite rules.
-/
theorem sum_atEmb_one : ∑ τ : E →+* ℂ, atEmb τ 1 = (2 : ℝ) • (1 : Cinf E) := by
  classical
  have e : ∀ τ : E →+* ℂ, atEmb τ 1 = Pi.single (InfinitePlace.mk τ) 1 := by
    intro τ; unfold atEmb; split_ifs <;> simp
  simp only [e]
  funext w
  rw [Finset.sum_apply]
  simp only [Pi.single_apply, Finset.sum_boole]
  have hc : (Finset.univ.filter fun τ : E →+* ℂ => w = InfinitePlace.mk τ).card = 2 := by
    have := InfinitePlace.card_filter_mk_eq w
    rw [InfinitePlace.mult_isComplex ⟨w, IsTotallyComplex.isComplex w⟩] at this
    rw [← this]; congr 1; ext τ; simp [eq_comm]
  rw [hc]
  simp

/- English proof (translation)
Simplify using `only [Eop, ← Finset.smul_sum, Finset.sum_sub_distrib, ← map_sum, sum_atEmb_I, sum_atEmb_one, map_zero, smul_zero, sub_zero, map_smul]`. Rewrite using `[← Complex.coe_smul, smul_smul]`. Evaluate the numerical expressions.
-/
theorem sum_Eop (a : ℕ) (i : Fin a) : ∑ τ : E →+* ℂ, Eop τ i i = lieS E a i i 1 := by
  simp only [Eop, ← Finset.smul_sum, Finset.sum_sub_distrib, ← map_sum, sum_atEmb_I, sum_atEmb_one, map_zero,
    smul_zero, sub_zero, map_smul]
  rw [← Complex.coe_smul, smul_smul]
  norm_num

end GlobalTheory.CuspRep.ZcTrace

namespace GlobalTheory.ResW

open GlobalTheory.CuspRep.ZcTrace in

/- English proof (translation)
Introduce `E _ _ _ a`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [sum_Eop, lieS_apply, ← map_sum]`. Unfold `zc`. Use `congr 1`.

Use function extensionality and compare the values at `k l`. Simplify using `[toL, Finset.sum_apply, Matrix.single_apply, eq_comm]`. Simplify using `only [Finset.sum_apply, Pi.single_apply]`. Distinguish the cases in `h : k = l`. Substitute `h` using the available equality.

Simplify using `[ite_apply, Pi.single_apply]`. Simplify using `[ite_apply, Pi.single_apply, h, Ne.symm h]`.
-/
theorem zc_eq_sum_Eop : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), GlobalTheory.ResW.zc E a = ∑ τ : E →+* ℂ, ∑ i : Fin a, GlobalTheory.CuspRep.Eop τ i i := by
  intro E _ _ _ a
  rw [Finset.sum_comm]
  simp only [sum_Eop, lieS_apply, ← map_sum]
  unfold zc
  congr 1
  funext k l
  simp [toL, Finset.sum_apply, Matrix.single_apply, eq_comm]
  simp only [Finset.sum_apply, Pi.single_apply]
  by_cases h : k = l
  · subst h; simp [ite_apply, Pi.single_apply]
  · simp [ite_apply, Pi.single_apply, h, Ne.symm h]

end GlobalTheory.ResW
