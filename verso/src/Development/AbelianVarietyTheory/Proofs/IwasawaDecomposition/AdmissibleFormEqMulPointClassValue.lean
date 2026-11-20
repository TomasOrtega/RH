import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RenVar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemGrassmannianRelationIdealSupMonomialSpanStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleChernFormProdGrassmannianBasisCopiesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleChernFormKillsGrassmannianRelationCopiStatement

noncomputable section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.GrassTop

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def S (H : Host E) (Dw : Datum H) : Submodule ℝ (MvPolynomial ((E →+* ℂ) × ℕ) ℝ) where
  carrier := {P | ∃ β : ℝ, ∀ Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ, GlobalTheory.Schubert.admitted H Dw Θ →
    Θ P = β * Θ (GlobalTheory.LieBase.pointPoly H Dw)}
  zero_mem' := ⟨0, fun Θ _ => by simp⟩
  add_mem' := by
    rintro a b ⟨β, hβ⟩ ⟨β', hβ'⟩
    exact ⟨β + β', fun Θ h => by rw [map_add, hβ Θ h, hβ' Θ h]; ring⟩
  smul_mem' := by
    rintro c a ⟨β, hβ⟩
    exact ⟨c * β, fun Θ h => by rw [map_smul, hβ Θ h, smul_eq_mul]; ring⟩

/- English proof (translation)
Rewrite using `[← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ σ), Function.update_self]`. Use `congr 1`. Use `Finset.prod_congr rfl fun τ hτ => ?_` and prove the remaining obligations. Rewrite using `[Function.update_of_ne (Finset.ne_of_mem_erase hτ)]`.
-/
theorem prod_update {H : Host E} (g : GlobalTheory.AllWt.Psi H → MvPolynomial (Bool × ℕ) ℝ) (σ : GlobalTheory.AllWt.Psi H)
    (h : MvPolynomial (Bool × ℕ) ℝ) :
    ∏ τ, ren τ (Function.update g σ h τ) = ren σ h * ∏ τ ∈ Finset.univ.erase σ, ren τ (g τ) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ σ), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun τ hτ => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hτ)]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `g hg`. Conclude with `⟨_, GlobalTheory.T.admissibleChernForm_prod_grassmannianBasisCopies E H Dw g fun τ => hg τ (Finset.notMem_empty τ)⟩`. Consider the case `insert σ s hσ ih`.

Introduce `g hg`. Establish `key : ∀ h ∈ (J Dw.p Dw.q).restrictScalars ℝ ⊔ Submodule.span ℝ (basis Dw.p Dw.q), ren σ h * ∏ τ ∈ Finset.univ.erase σ, ren τ (g τ) ∈ S H Dw`. Introduce `h hh`. Take `⟨j, hj, b, hb, rfl⟩` from `Submodule.mem_sup.1 hh`. Rewrite using `[map_add, add_mul]`.

Use `add_mem ⟨0, fun Θ hΘ => ?_⟩ ?_` and prove the remaining obligations. Rewrite using `[zero_mul, mul_comm]`. Conclude with `GlobalTheory.T.adm_apply_mul_ren_eq_zero_of_mem_J E H Dw Θ hΘ σ j hj _`. Use `clear hh`. Proceed by induction on `hb using Submodule.span_induction with`.

Consider the case `mem b hb`. Rewrite using `[← prod_update]`. Use `ih _ fun τ hτ => ?_` and prove the remaining obligations. Distinguish the cases in `e : τ = σ`. Substitute `e` using the available equality.

Rewrite using `[Function.update_self]`. Conclude with `hb`. Rewrite using `[Function.update_of_ne e]; exact hg τ (by simp [e, hτ])`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add, add_mul]`.

Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx => rw [map_smul, smul_mul_assoc]`. Conclude with `Submodule.smul_mem _ c hx`. Use `key (g σ) (GlobalTheory.T.mem_grassmannianRelationIdeal_sup_monomialSpan _ _ _)` as an intermediate fact. Rewrite `this` using `[← prod_update, Function.update_eq_self]`. Then use the resulting hypothesis.
-/
theorem prod_ren_mem (H : Host E) (Dw : Datum H) (s : Finset (GlobalTheory.AllWt.Psi H)) :
    ∀ g : GlobalTheory.AllWt.Psi H → MvPolynomial (Bool × ℕ) ℝ, (∀ τ ∉ s, g τ ∈ basis Dw.p Dw.q) →
      ∏ τ, ren τ (g τ) ∈ S H Dw := by
  induction s using Finset.induction_on with
  | empty =>
    intro g hg
    exact ⟨_, GlobalTheory.T.admissibleChernForm_prod_grassmannianBasisCopies E H Dw g fun τ => hg τ (Finset.notMem_empty τ)⟩
  | insert σ s hσ ih =>
    intro g hg
    have key : ∀ h ∈ (J Dw.p Dw.q).restrictScalars ℝ ⊔ Submodule.span ℝ (basis Dw.p Dw.q),
        ren σ h * ∏ τ ∈ Finset.univ.erase σ, ren τ (g τ) ∈ S H Dw := by
      intro h hh
      obtain ⟨j, hj, b, hb, rfl⟩ := Submodule.mem_sup.1 hh
      rw [map_add, add_mul]
      refine add_mem ⟨0, fun Θ hΘ => ?_⟩ ?_
      · rw [zero_mul, mul_comm]
        exact GlobalTheory.T.adm_apply_mul_ren_eq_zero_of_mem_J E H Dw Θ hΘ σ j hj _
      · clear hh
        induction hb using Submodule.span_induction with
        | mem b hb =>
          rw [← prod_update]
          refine ih _ fun τ hτ => ?_
          by_cases e : τ = σ
          · subst e; rw [Function.update_self]; exact hb
          · rw [Function.update_of_ne e]; exact hg τ (by simp [e, hτ])
        | zero => simp
        | add x y _ _ hx hy => rw [map_add, add_mul]; exact add_mem hx hy
        | smul c x _ hx => rw [map_smul, smul_mul_assoc]; exact Submodule.smul_mem _ c hx
    have := key (g σ) (GlobalTheory.T.mem_grassmannianRelationIdeal_sup_monomialSpan _ _ _)
    rwa [← prod_update, Function.update_eq_self] at this

/- English proof (translation)
Distinguish the cases in `h : x.1 (H.rt : E) = H.rt0`. Conclude with `⟨⟨x.1, h⟩, (true, x.2), by simp [renVar]⟩`. Use `⟨⟨conjEmb x.1, GlobalTheory.AllWt.conj_mem h⟩, (false, x.2), ?_⟩` and prove the remaining obligations. Simplify using `[renVar, GlobalTheory.AllWt.conjEmb_conjEmb]`.
-/
theorem var_eq {H : Host E} (x : (E →+* ℂ) × ℕ) : ∃ σ : GlobalTheory.AllWt.Psi H, ∃ y, x = renVar σ y := by
  by_cases h : x.1 (H.rt : E) = H.rt0
  · exact ⟨⟨x.1, h⟩, (true, x.2), by simp [renVar]⟩
  · refine ⟨⟨conjEmb x.1, GlobalTheory.AllWt.conj_mem h⟩, (false, x.2), ?_⟩
    simp [renVar, GlobalTheory.AllWt.conjEmb_conjEmb]

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a`. Introduce `g`. Rewrite using `[C_mul']`. Conclude with `Submodule.smul_mem _ a (prod_ren_mem H Dw Finset.univ g (by simp))`.

Consider the case `add a b ha hb => intro g`. Rewrite using `[add_mul]`. Conclude with `add_mem (ha g) (hb g)`. Consider the case `mul_X P x ih`. Introduce `g`.

Take `⟨σ, y, rfl⟩` from `var_eq (H := H) x`. Establish `e : X (renVar σ y) * ∏ τ, ren τ (g τ) = ∏ τ, ren τ (Function.update g σ (X y * g σ) τ)`. Rewrite using `[prod_update, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ σ), map_mul, ren, rename_X]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[mul_assoc, e]`.

Conclude with `ih _`.
-/
theorem mul_prod_ren_mem (H : Host E) (Dw : Datum H) (P : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) :
    ∀ g : GlobalTheory.AllWt.Psi H → MvPolynomial (Bool × ℕ) ℝ, P * ∏ τ, ren τ (g τ) ∈ S H Dw := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    intro g
    rw [C_mul']
    exact Submodule.smul_mem _ a (prod_ren_mem H Dw Finset.univ g (by simp))
  | add a b ha hb => intro g; rw [add_mul]; exact add_mem (ha g) (hb g)
  | mul_X P x ih =>
    intro g
    obtain ⟨σ, y, rfl⟩ := var_eq (H := H) x
    have e : X (renVar σ y) * ∏ τ, ren τ (g τ) = ∏ τ, ren τ (Function.update g σ (X y * g σ) τ) := by
      rw [prod_update, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ σ), map_mul, ren, rename_X]
      ring
    rw [mul_assoc, e]
    exact ih _

end GlobalTheory.GrassTop

/- English proof (translation)
Introduce `E _ _ _ H Dw P`. Use `GlobalTheory.GrassTop.mul_prod_ren_mem H Dw P (fun _ => 1)` as an intermediate fact. Simplify using `only [map_one, Finset.prod_const_one, mul_one] at this`. Conclude with `this`.
-/
theorem GlobalTheory.GrassTop.span_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (P : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), ∃ β : ℝ, ∀ Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ,
      GlobalTheory.Schubert.admitted H Dw Θ → Θ P = β * Θ (GlobalTheory.LieBase.pointPoly H Dw) := by
  intro E _ _ _ H Dw P
  have := GlobalTheory.GrassTop.mul_prod_ren_mem H Dw P (fun _ => 1)
  simp only [map_one, Finset.prod_const_one, mul_one] at this
  exact this
