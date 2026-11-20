import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

/- English proof (translation)
Rewrite using `[(unfold X kerBasic kernel_rows_columns_square_integrable hφ hinv hf x).2, ← integral_mul_left_eq_self (fun y => φ (x⁻¹ * y) * f y) x]`. Simplify using `only [inv_mul_cancel_left]`.
-/
private theorem ker_integral_shift (X : Ctx) {φ f : X.G → ℂ} (hφ : Tst φ)
    (hinv : ∀ γ : X.Γ, ∀ y, f ((γ : X.G) * y) = f y) (hf : MemLp f 2 X.ν) (x : X.G) :
    ∫ y, ker X.Γ φ x y * f y ∂X.ν = ∫ z, φ z * f (x * z) ∂X.μ := by
  rw [(unfold X kerBasic kernel_rows_columns_square_integrable hφ hinv hf x).2,
    ← integral_mul_left_eq_self (fun y => φ (x⁻¹ * y) * f y) x]
  simp only [inv_mul_cancel_left]

/- English proof (translation)
Introduce `hB E _ _ _ n ι _ s`. Take `⟨-, hmul, -, -, -, -, -, -, -, hrat, -, -⟩` from `hB E n s.pos`. Use `choose W hWle hWfd hW using s.fin`. Establish `hfd : FiniteDimensional ℂ (⨆ p : ι × ι, W p.1 p.2 : Submodule ℂ (Sm E n))` using `by haveI : ∀ p : ι × ι, FiniteDimensional ℂ (W p.1 p.2) := fun p => hWfd _ _`. Conclude with `Submodule.finiteDimensional_iSup _`.

Use `⟨⨆ p : ι × ι, W p.1 p.2, iSup_le fun p => hWle _ _, hfd, ?_⟩` and prove the remaining obligations. Introduce `v hv i t`. Use `choose ψ hψ u hu hu' hvu using hv`. Set `X` to `PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds s.D`. Establish `hform : ∀ j, ∀ (γ : ratH E n 0) (y : H E n 0), (ψ j).1 ((γ : H E n 0) * y).1 = (ψ j).1 y.1`.

Introduce `j γ y`. Take `⟨⟨γ₁, γ₂⟩, hγ⟩` from `γ.2`. Establish `h1 : (γ : H E n 0).1 = ratGL E n γ₁` using `by rw [← hγ]; rfl`. Rewrite using `[Prod.fst_mul, h1]`. Conclude with `(s.π.cusp _ (hψ j)).1.left γ₁ y.1`.

Use `set Ft : ι → H E n 0 → ℂ := fun j x => (ψ j).1 x.1 * u j (ldet x) with hFt`. Establish `hinv : ∀ j, ∀ (γ : ratH E n 0) (y : H E n 0), Ft j ((γ : H E n 0) * y) = Ft j y`. Introduce `j γ y`. Simplify using `only [hFt, hform j γ y, hmul, (hrat γ).1, zero_add]`. Establish `hmem : ∀ j, MemLp (Ft j) 2 s.D.ν` using `fun j => (Lp.memLp (v j)).ae_eq (hvu j)`.

Establish `hex : ∀ j, ∃ ψ' ∈ W i j, ∀ g, ψ'.1 g = ∫ y, s.Φ₁ i j y * (fun r => u j (t + r)) (ldet y) * (ψ j).1 (g * y.1) ∂s.D.μ` using `fun j => hW i j (fun r => u j (t + r)) ((hu j).comp (continuous_const.add continuous_id)) (ψ j) (hψ j)`. Use `choose ψ' hψ' hval using hex`. Use `⟨∑ j, ψ' j, Submodule.sum_mem _ fun j _ => (le_iSup (fun p : ι × ι => W p.1 p.2) (i, j)) (hψ' j), fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[s.vecs.rep₁]`. Establish `hsum : (∑ j, ψ' j).1 x.1 = ∑ j, (ψ' j).1 x.1`.

Simplify using `[Submodule.coe_sum]`. Rewrite using `[hsum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `hae : ∫ y, kerH (s.Φ₁ i j) x y * (v j : H E n 0 → ℂ) y ∂s.D.ν = ∫ y, kerH (s.Φ₁ i j) x y * Ft j y ∂s.D.ν` using `integral_congr_ae ((hvu j).mono fun y hy => by simp only [hy, hFt])`. Rewrite using `[hae, hval j]`.

Establish `hs : ∫ y, kerH (s.Φ₁ i j) x y * Ft j y ∂s.D.ν = ∫ z, s.Φ₁ i j z * Ft j (x * z) ∂s.D.μ` using `ker_integral_shift X (φ := s.Φ₁ i j) (f := Ft j) (s.t₁ i j) (hinv j) (hmem j) x`. Use `hs.trans (integral_congr_ae (Filter.Eventually.of_forall fun z => ?_))` and prove the remaining obligations. Use `show s.Φ₁ i j z * ((ψ j).1 (x * z).1 * u j (ldet (x * z))) = s.Φ₁ i j z * u j (t + ldet z) * (ψ j).1 (x.1 * z.1)`. Rewrite using `[hmul, hx, Prod.fst_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.finGen_pf :
    Basic → FinGen := by
  intro hB E _ _ _ n ι _ s
  classical
  obtain ⟨-, hmul, -, -, -, -, -, -, -, hrat, -, -⟩ := hB E n s.pos
  choose W hWle hWfd hW using s.fin
  have hfd : FiniteDimensional ℂ (⨆ p : ι × ι, W p.1 p.2 : Submodule ℂ (Sm E n)) := by
    haveI : ∀ p : ι × ι, FiniteDimensional ℂ (W p.1 p.2) := fun p => hWfd _ _
    exact Submodule.finiteDimensional_iSup _
  refine ⟨⨆ p : ι × ι, W p.1 p.2, iSup_le fun p => hWle _ _, hfd, ?_⟩
  intro v hv i t
  choose ψ hψ u hu hu' hvu using hv
  let X := PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds s.D
  have hform : ∀ j, ∀ (γ : ratH E n 0) (y : H E n 0), (ψ j).1 ((γ : H E n 0) * y).1 = (ψ j).1 y.1 := by
    intro j γ y
    obtain ⟨⟨γ₁, γ₂⟩, hγ⟩ := γ.2
    have h1 : (γ : H E n 0).1 = ratGL E n γ₁ := by rw [← hγ]; rfl
    rw [Prod.fst_mul, h1]
    exact (s.π.cusp _ (hψ j)).1.left γ₁ y.1
  set Ft : ι → H E n 0 → ℂ := fun j x => (ψ j).1 x.1 * u j (ldet x) with hFt
  have hinv : ∀ j, ∀ (γ : ratH E n 0) (y : H E n 0), Ft j ((γ : H E n 0) * y) = Ft j y := by
    intro j γ y
    simp only [hFt, hform j γ y, hmul, (hrat γ).1, zero_add]
  have hmem : ∀ j, MemLp (Ft j) 2 s.D.ν := fun j => (Lp.memLp (v j)).ae_eq (hvu j)
  have hex : ∀ j, ∃ ψ' ∈ W i j, ∀ g, ψ'.1 g =
      ∫ y, s.Φ₁ i j y * (fun r => u j (t + r)) (ldet y) * (ψ j).1 (g * y.1) ∂s.D.μ := fun j =>
    hW i j (fun r => u j (t + r)) ((hu j).comp (continuous_const.add continuous_id)) (ψ j) (hψ j)
  choose ψ' hψ' hval using hex
  refine ⟨∑ j, ψ' j, Submodule.sum_mem _ fun j _ =>
    (le_iSup (fun p : ι × ι => W p.1 p.2) (i, j)) (hψ' j), fun x hx => ?_⟩
  rw [s.vecs.rep₁]
  have hsum : (∑ j, ψ' j).1 x.1 = ∑ j, (ψ' j).1 x.1 := by
    simp [Submodule.coe_sum]
  rw [hsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hae : ∫ y, kerH (s.Φ₁ i j) x y * (v j : H E n 0 → ℂ) y ∂s.D.ν =
      ∫ y, kerH (s.Φ₁ i j) x y * Ft j y ∂s.D.ν :=
    integral_congr_ae ((hvu j).mono fun y hy => by simp only [hy, hFt])
  rw [hae, hval j]
  have hs : ∫ y, kerH (s.Φ₁ i j) x y * Ft j y ∂s.D.ν = ∫ z, s.Φ₁ i j z * Ft j (x * z) ∂s.D.μ :=
    ker_integral_shift X (φ := s.Φ₁ i j) (f := Ft j) (s.t₁ i j) (hinv j) (hmem j) x
  refine hs.trans (integral_congr_ae (Filter.Eventually.of_forall fun z => ?_))
  show s.Φ₁ i j z * ((ψ j).1 (x * z).1 * u j (ldet (x * z))) =
    s.Φ₁ i j z * u j (t + ldet z) * (ψ j).1 (x.1 * z.1)
  rw [hmul, hx, Prod.fst_mul]
  ring
