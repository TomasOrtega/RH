import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.EntriesZero
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.WspOrth
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.TraceRestrictSupDisjoint

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

/- English proof (translation)
Simplify using `only [evT, ex, AddMonoidAlgebra.lift_single, one_smul]`. Rewrite using `[AddMonoidAlgebra.lift_apply]`. Simplify using `only [Finsupp.sum, cf, smul_eq_mul]`.
-/
private theorem evT_sum {n : ℕ} (θ : Wt n) (c : FR n) :
    evT θ c = ∑ μ ∈ c.coeff.support, cf c μ * evT θ (ex μ) := by
  simp only [evT, ex, AddMonoidAlgebra.lift_single, one_smul]
  rw [AddMonoidAlgebra.lift_apply]
  simp only [Finsupp.sum, cf, smul_eq_mul]

/- English proof (translation)
Introduce `n N _ _ _ σ F hF hσ B c hB hc θ k hk`. Take `⟨s, hs0, hsup, hind⟩` from `wtDec n N F hF ⊤ inferInstance (fun _ _ _ _ => Submodule.mem_top)`. Use `set W : Wt n → Submodule ℂ N := fun μ => wsp F μ ⊓ ⊤ with hW`. Establish `hBW : ∀ μ, ∀ v ∈ W μ, B v ∈ W μ`. Introduce `μ v hv`.

Rewrite `hv`, the goal using `[Submodule.mem_inf]`. Use `⟨?_, Submodule.mem_top⟩` and prove the remaining obligations. Establish `hv1 : IsWeight F μ v` using `hv.1`. Use `show IsWeight F μ (B v)`. Introduce `a`.

Establish `h1` using `congrArg (fun T : Module.End ℂ N => T v) (hB.1 a a)`. Simplify using `only [Module.End.mul_apply] at h1`. Rewrite using `[← h1, hv1 a, map_smul]`. Establish `hσW : ∀ μ, ∀ v ∈ W μ, σ k v = evT θ (ex μ) • v` using `fun μ v hv => (derAt n N σ F hσ).1 μ θ k v hk (Submodule.mem_inf.1 hv).1`. Establish `hfW : ∀ μ, Set.MapsTo (σ k * B) (W μ) (W μ)`.

Introduce `μ v hv`. Use `show σ k (B v) ∈ W μ`. Rewrite using `[hσW μ _ (hBW μ v hv)]`. Conclude with `(W μ).smul_mem _ (hBW μ v hv)`. Establish `hint : DirectSum.IsInternal (fun i : s => W i)`.

Apply `DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top` to reduce the goal to its premises. Conclude with `iSupIndep.comp hind Subtype.val_injective`. Rewrite using `[← hsup, iSup_subtype']`. Establish `hterm : ∀ μ, LinearMap.trace ℂ (W μ) ((σ k * B).restrict (hfW μ)) = evT θ (ex μ) * cf c μ`. Introduce `μ`.

Establish `hr : (σ k * B).restrict (hfW μ) = evT θ (ex μ) • B.restrict (hBW μ)`. Use extensionality with `v`. Simplify using `only [LinearMap.restrict_coe_apply, LinearMap.smul_apply, Module.End.mul_apply, Submodule.coe_smul]`. Conclude with `hσW μ _ (hBW μ v v.2)`. Rewrite using `[hr, map_smul, smul_eq_mul, hc μ]`.

Unfold `trOn`. Rewrite using `[dif_pos (hBW μ)]`. Establish `hz : ∀ μ, μ ∉ s → cf c μ = 0`. Introduce `μ hμ`. Rewrite using `[hc μ, hs0 μ hμ]`.

Unfold `trOn`. Use `split_ifs with h`. Establish `h0 : B.restrict h = 0`. Use extensionality with `x`. Rewrite using `[h0, map_zero]`.

Both sides reduce to the same expression. Rewrite using `[LinearMap.trace_eq_sum_trace_restrict hint (fun i => hfW i)]`. Simplify using `only [hterm]`. Rewrite using `[Finset.sum_coe_sort s (fun μ => evT θ (ex μ) * cf c μ)]`. Combine the equalities or inequalities in the displayed calculation.

Apply `Finset.sum_subset Finset.subset_union_left` to reduce the goal to its premises. Introduce `μ _ hμ`. Rewrite using `[hz μ hμ, mul_zero]`. Use `_ = ∑ μ ∈ s ∪ c.coeff.support, cf c μ * evT θ (ex μ) := Finset.sum_congr rfl (fun μ _ => mul_comm _ _)`. Use `_ = ∑ μ ∈ c.coeff.support, cf c μ * evT θ (ex μ) := by`.

Use `symm`. Apply `Finset.sum_subset Finset.subset_union_right` to reduce the goal to its premises. Introduce `μ _ hμ`. Rewrite using `[show cf c μ = 0 from Finsupp.notMem_support_iff.1 hμ, zero_mul]`. Use `_ = evT θ c := (evT_sum θ c).symm`.
-/
theorem UpperTheory.RealTr.chEv :
    ∀ (n : ℕ) (N : Type) [NormedAddCommGroup N] [InnerProductSpace ℂ N] [FiniteDimensional ℂ N] (σ : UK n →* (N →ₗ[ℂ] N))
      (F : Fin n → Fin n → Module.End ℂ N), UF F → IsDerivK σ F → ∀ B c, Cm F ⊤ B → IsCh F ⊤ B c → ∀ (θ : Wt n) (k : UK n),
      k.1 = diagonal (fun a => Complex.exp (Complex.I * θ a)) → LinearMap.trace ℂ N (σ k * B) = evT θ c := by
  intro n N _ _ _ σ F hF hσ B c hB hc θ k hk
  classical
  obtain ⟨s, hs0, hsup, hind⟩ := wtDec n N F hF ⊤ inferInstance (fun _ _ _ _ => Submodule.mem_top)
  set W : Wt n → Submodule ℂ N := fun μ => wsp F μ ⊓ ⊤ with hW
  have hBW : ∀ μ, ∀ v ∈ W μ, B v ∈ W μ := by
    intro μ v hv
    rw [Submodule.mem_inf] at hv ⊢
    refine ⟨?_, Submodule.mem_top⟩
    have hv1 : IsWeight F μ v := hv.1
    show IsWeight F μ (B v)
    intro a
    have h1 := congrArg (fun T : Module.End ℂ N => T v) (hB.1 a a)
    simp only [Module.End.mul_apply] at h1
    rw [← h1, hv1 a, map_smul]
  have hσW : ∀ μ, ∀ v ∈ W μ, σ k v = evT θ (ex μ) • v := fun μ v hv =>
    (derAt n N σ F hσ).1 μ θ k v hk (Submodule.mem_inf.1 hv).1
  have hfW : ∀ μ, Set.MapsTo (σ k * B) (W μ) (W μ) := by
    intro μ v hv
    show σ k (B v) ∈ W μ
    rw [hσW μ _ (hBW μ v hv)]
    exact (W μ).smul_mem _ (hBW μ v hv)
  have hint : DirectSum.IsInternal (fun i : s => W i) := by
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · exact iSupIndep.comp hind Subtype.val_injective
    · rw [← hsup, iSup_subtype']
  have hterm : ∀ μ, LinearMap.trace ℂ (W μ) ((σ k * B).restrict (hfW μ)) = evT θ (ex μ) * cf c μ := by
    intro μ
    have hr : (σ k * B).restrict (hfW μ) = evT θ (ex μ) • B.restrict (hBW μ) := by
      ext v
      simp only [LinearMap.restrict_coe_apply, LinearMap.smul_apply, Module.End.mul_apply,
        Submodule.coe_smul]
      exact hσW μ _ (hBW μ v v.2)
    rw [hr, map_smul, smul_eq_mul, hc μ]
    unfold trOn
    rw [dif_pos (hBW μ)]
  have hz : ∀ μ, μ ∉ s → cf c μ = 0 := by
    intro μ hμ
    rw [hc μ, hs0 μ hμ]
    unfold trOn
    split_ifs with h
    · have h0 : B.restrict h = 0 := by
        ext x
      rw [h0, map_zero]
    · rfl
  rw [LinearMap.trace_eq_sum_trace_restrict hint (fun i => hfW i)]
  simp only [hterm]
  rw [Finset.sum_coe_sort s (fun μ => evT θ (ex μ) * cf c μ)]
  calc ∑ μ ∈ s, evT θ (ex μ) * cf c μ
        = ∑ μ ∈ s ∪ c.coeff.support, evT θ (ex μ) * cf c μ := by
          apply Finset.sum_subset Finset.subset_union_left
          intro μ _ hμ
          rw [hz μ hμ, mul_zero]
    _ = ∑ μ ∈ s ∪ c.coeff.support, cf c μ * evT θ (ex μ) :=
          Finset.sum_congr rfl (fun μ _ => mul_comm _ _)
    _ = ∑ μ ∈ c.coeff.support, cf c μ * evT θ (ex μ) := by
          symm
          apply Finset.sum_subset Finset.subset_union_right
          intro μ _ hμ
          rw [show cf c μ = 0 from Finsupp.notMem_support_iff.1 hμ, zero_mul]
    _ = evT θ c := (evT_sum θ c).symm
