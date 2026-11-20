import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.SideGTau
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Loc

/- English proof (translation)
Introduce `F _ _ Δ D hD ι hι θ hθ t ht δ τ y hτ hF`. Take `⟨hc, -, hm, hi⟩` from `UpperTheory.V.Z.Sym.Glob.sideGTau`. Use `set x : GA Δ := y⁻¹ * ι δ * θ y with hx`. Establish `hfin : (Function.mulSupport fun v => D.fGv t v (x.1 v)).Finite`. Establish `h1 : ∀ᶠ v in Filter.cofinite, x.1 v ∈ KU (Ov v) (cv v Δ)` using `x.2`.

Use `((Filter.eventually_cofinite.1 h1).union D.Sg.finite_toSet).subset fun v hv => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Simplify using `only [Set.mem_union, Set.mem_setOf_eq, Finset.mem_coe, not_or, not_not] at hn`. Apply `hv` to reduce the goal to its premises. Simplify using `[Dat.fGv, hn.2, hn.1, one]`.

Establish `hne : ∀ v, D.fGv t v (x.1 v) ≠ 0` using `fun v h0 => hF (finprod_eq_zero (fun v => D.fGv t v (x.1 v)) v h0 hfin)`. Establish `hloc : ∀ v, HasTau (x.1 v) (cv v τ)`. Introduce `v`. Establish `h1 : HasTau ((ι δ).1 v) (cv v τ)` using `hm _ _ (cv v) Δ δ _ τ (hι δ v) hτ`. Establish `h2` using `hc _ (cv v Δ) ((ι δ).1 v) (y.1 v) (cv v τ) h1`.

Establish `e : x.1 v = (y.1 v)⁻¹ * (ι δ).1 v * theta _ (y.1 v)`. Rewrite using `[← hθ y v]`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `h2`.

Use `⟨fun v hv => ?_, fun v hv => ?_⟩` and prove the remaining obligations. Establish `h` using `hne v`. Simplify using `only [Dat.fGv, if_pos hv] at h`. Conclude with `(hD.sig v hv).G_supp _ (ht v hv) _ _ (hloc v) h`. Establish `h` using `hne v`.

Simplify using `only [Dat.fGv, if_neg hv] at h`. Establish `hk : x.1 v ∈ KU (Ov v) (cv v Δ)`. Assume the negation of the conclusion as `hn`. Conclude with `h (by simp [one, hn])`. Establish `hint : IsIntegral (Ov v) (cv v τ)` using `hi _ _ _ _ _ hk (hloc v)`.

Take `⟨r, hr⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hint`. Conclude with `⟨r, hr⟩`.
-/
theorem UpperTheory.V.Z.Sym.Glob.sideGSupp :
    ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ ι, IsIotaG ι → ∀ θ : GA Δ →* GA Δ,
    (∀ g v, (θ g).1 v = theta _ (g.1 v)) → ∀ t, D.Cone t → ∀ (δ : U3 Δ) (τ : F) (y : GA Δ), HasTau δ τ →
    D.FG t (y⁻¹ * ι δ * θ y) ≠ 0 → D.admitted t τ ∧ ∀ v ∉ D.Sg, cv v τ ∈ (algebraMap (Ov v) (Kv v)).range := by
  classical
  intro F _ _ Δ D hD ι hι θ hθ t ht δ τ y hτ hF
  obtain ⟨hc, -, hm, hi⟩ := UpperTheory.V.Z.Sym.Glob.sideGTau
  set x : GA Δ := y⁻¹ * ι δ * θ y with hx

  have hfin : (Function.mulSupport fun v => D.fGv t v (x.1 v)).Finite := by
    have h1 : ∀ᶠ v in Filter.cofinite, x.1 v ∈ KU (Ov v) (cv v Δ) := x.2
    refine ((Filter.eventually_cofinite.1 h1).union D.Sg.finite_toSet).subset fun v hv => ?_
    by_contra hn
    simp only [Set.mem_union, Set.mem_setOf_eq, Finset.mem_coe, not_or, not_not] at hn
    apply hv
    simp [Dat.fGv, hn.2, hn.1, one]
  have hne : ∀ v, D.fGv t v (x.1 v) ≠ 0 := fun v h0 =>
    hF (finprod_eq_zero (fun v => D.fGv t v (x.1 v)) v h0 hfin)

  have hloc : ∀ v, HasTau (x.1 v) (cv v τ) := by
    intro v
    have h1 : HasTau ((ι δ).1 v) (cv v τ) := hm _ _ (cv v) Δ δ _ τ (hι δ v) hτ
    have h2 := hc _ (cv v Δ) ((ι δ).1 v) (y.1 v) (cv v τ) h1
    have e : x.1 v = (y.1 v)⁻¹ * (ι δ).1 v * theta _ (y.1 v) := by
      rw [← hθ y v]; rfl
    rw [e]; exact h2
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · have h := hne v
    simp only [Dat.fGv, if_pos hv] at h
    exact (hD.sig v hv).G_supp _ (ht v hv) _ _ (hloc v) h
  · have h := hne v
    simp only [Dat.fGv, if_neg hv] at h
    have hk : x.1 v ∈ KU (Ov v) (cv v Δ) := by
      by_contra hn
      exact h (by simp [one, hn])
    have hint : IsIntegral (Ov v) (cv v τ) := hi _ _ _ _ _ hk (hloc v)
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    exact ⟨r, hr⟩
