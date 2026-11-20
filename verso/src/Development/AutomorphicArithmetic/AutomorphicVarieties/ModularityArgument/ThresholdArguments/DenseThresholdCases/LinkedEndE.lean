import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.PlacesOverFinite.LinkUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.PlacesOverFinite.ChiUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PointTheoremBaseObject
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SymUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SdStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PlDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PrDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsSeed
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TwoRuns
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PrSeedPtOf

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af
/- English proof (translation)
Introduce `hA _ hMod hLev hLam hB0 hS3 hS2 hTw hCyc hRes Ω _ _ _ l _ ι c _ N _ e ψ he hev η σ g₁ B M hM hram L _ _ _ _ Φ C₀ k hB hok hbig hseed`. Take `⟨K, _, _, _, N', w, χ', η', θ, j, hD, hne, hord, hη, hcong, hdisc⟩` from `hseed`. Use `haveI : IsAlgClosure L Ω := { isAlgClosed := IsAlgClosure.isAlgClosed ℚ isAlgebraic := haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic Algebra.IsAlgebraic.tower_top (K := ℚ) L }`. Establish `hM0 : M ≠ 0`. Introduce and unpack `rfl`.

Take `⟨hσ, hc⟩` from `k.c`. Establish `h1 : σ ∈ η.ker` using `k.split ⊤ (by rw [← ValuationSubring.mem_nonunits_iff, Nat.cast_zero]; exact zero_mem _) ⟨by`. Use `mem_Dec.2 (eq_top_iff.2 fun x _ => ?_)` and prove the remaining obligations. Rewrite using `[ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]`. Conclude with `ValuationSubring.mem_top _, hσ⟩`.

Establish `h2` using `k.del ⟨σ, hσ⟩`. Rewrite `h2` using `[hc, hok.del_c]`. Establish `h3 : η σ = 1` using `h1`. Rewrite `h2` using `[h3]`. Conclude with `absurd h2 (by decide)`.

Establish `H : UpperTheory.V.Pr.LinkHyp c N e η σ B M` using `⟨he, hM, hM0, hram, hB, hD.cc⟩`. Establish `hv : Nonempty Φ.V`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_nonempty_iff]`. Use `hbig.1` as an intermediate fact.

Simplify using `[UpperTheory.V.Fr.Frame.d] at this`. Take `⟨v⟩` from `hv`. Establish `hker : η.ker = galOf ℚ K Ω`. Rewrite using `[← hD.η_ker]`. Use extensionality with `s`.

Rewrite using `[MonoidHom.mem_ker, MonoidHom.mem_ker, ← Units.val_eq_one, ← Units.val_eq_one, hη s]`. Conclude with `Iff.rfl` after adjusting the coercions. Use `haveI := hD.imag`. Take `⟨κ, hκ⟩` from `hTw K Ω hD.quad l hok.l_odd hdisc ι σ hD.cc`. Take `⟨hk3, hk2⟩` from `UpperTheory.V.Pr.kaOf hCyc hRes Ω l ι c N e ψ η σ g₁ B M H L Φ k`.

Take `⟨ka, hk2, hka⟩` from `hk2 K hker κ hκ`. Take `⟨c₁, hle, hL, hv3, hv2, f, hf⟩` from `UpperTheory.V.Pr.coefEx l c L Ω _ _ hk3.alg.1 hk2.alg.1`. Use `haveI := UpperTheory.V.Pr.coefIs l c₁`. Take `⟨m₃, hm₃, -, r₃, -, s₃⟩` from `hS3 K L Ω l ι σ N' w χ' η' θ j hD hne M hM0 (by rw [mul_comm]; exact (Nat.mul_dvd_mul_left l hev.two_dvd).trans hM) (UpperTheory.V.Z.Sym.Pl.linkUnr Ω l _ η _ σ g₁ B M L Φ k) (UpperTheory.V.Z.Sym.Pl.chiUnr Ω l c N e ψ χ' j hord hcong M hM L) 2`. Take `⟨m₂, hm₂, -, r₂, -, -, -, s₂⟩` from `hS2 K L Ω l ι σ N' w χ' η' θ j hD κ ka hκ hka 2`.

Take `⟨hfin, a₃, a₂⟩` from `_root_.UpperTheory.Gal.projectedFormsSystemPart.twoRuns_alt hA hMod hLam ι H v hL hk2 hk3 (UpperTheory.Gal.projectedFormsSystemPart.cRealAv hLev hB0 Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 2 ka C₀ (Or.inl rfl) hok hbig hle hf hk2 hv2) (UpperTheory.Gal.projectedFormsSystemPart.cReal …`. Apply the tactic sequence `convert s₂ using 2 with i i i <;> fin_cases i <;> simp [UpperTheory.V.Fr.w]))`. Use the proof step `(fun R₃ => _root_.UpperTheory.V.Pr.seedPtOf_alt hA Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 3 _ R₃ hk3 χ' j hord hcong m₃ hm₃ _ (by`. Apply the tactic sequence `convert s₃ using 2 with i i i <;> fin_cases i <;> simp [UpperTheory.V.Fr.w]))`. Conclude with `⟨UpperTheory.V.Pr.finPtDown l c c₁ f hle hf Φ 3 hfin, a₃, ka, hk2.alg, a₂⟩`.
-/
theorem UpperTheory.Gal.projectedFormsSystemPart.linked_endomorphism_dense :
    GlobalTheory.Published.GlobalArtinReciprocity → UpperTheory.V.W.LocCFTAll → _root_.UpperTheory.V.W.ModUAlt → UpperTheory.V.W.LevEx → UpperTheory.V.W.LamEx → UpperTheory.V.W.ProModularRingExists → _root_.UpperTheory.V.Z.Sym.UnitaryThreeAutomorphyDense → _root_.UpperTheory.V.Sd.Seed2Alt → UpperTheory.V.Sd.Twist → UpperTheory.V.Sd.AlgCyc → UpperTheory.V.Sd.AlgRes → _root_.UpperTheory.V.Z.Sym.Pl.LinkedEndEAlt := by
  intro hA _ hMod hLev hLam hB0 hS3 hS2 hTw hCyc hRes Ω _ _ _ l _ ι c _ N _ e ψ he hev η σ g₁ B M hM hram L _ _ _ _ Φ C₀ k hB hok hbig hseed
  obtain ⟨K, _, _, _, N', w, χ', η', θ, j, hD, hne, hord, hη, hcong, hdisc⟩ := hseed
  haveI : IsAlgClosure L Ω :=
    { isAlgClosed := IsAlgClosure.isAlgClosed ℚ
      isAlgebraic := haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
        Algebra.IsAlgebraic.tower_top (K := ℚ) L }
  have hM0 : M ≠ 0 := by
    rintro rfl
    obtain ⟨hσ, hc⟩ := k.c
    have h1 : σ ∈ η.ker := k.split ⊤ (by rw [← ValuationSubring.mem_nonunits_iff, Nat.cast_zero]; exact zero_mem _) ⟨by
      refine mem_Dec.2 (eq_top_iff.2 fun x _ => ?_)
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      exact ValuationSubring.mem_top _, hσ⟩
    have h2 := k.del ⟨σ, hσ⟩
    rw [hc, hok.del_c] at h2
    have h3 : η σ = 1 := h1
    rw [h3] at h2
    exact absurd h2 (by decide)
  have H : UpperTheory.V.Pr.LinkHyp c N e η σ B M := ⟨he, hM, hM0, hram, hB, hD.cc⟩
  have hv : Nonempty Φ.V := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hbig.1
    simp [UpperTheory.V.Fr.Frame.d] at this
  obtain ⟨v⟩ := hv
  have hker : η.ker = galOf ℚ K Ω := by
    rw [← hD.η_ker]
    ext s
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← Units.val_eq_one, ← Units.val_eq_one, hη s]
    exact_mod_cast Iff.rfl
  haveI := hD.imag
  obtain ⟨κ, hκ⟩ := hTw K Ω hD.quad l hok.l_odd hdisc ι σ hD.cc
  obtain ⟨hk3, hk2⟩ := UpperTheory.V.Pr.kaOf hCyc hRes Ω l ι c N e ψ η σ g₁ B M H L Φ k
  obtain ⟨ka, hk2, hka⟩ := hk2 K hker κ hκ
  obtain ⟨c₁, hle, hL, hv3, hv2, f, hf⟩ := UpperTheory.V.Pr.coefEx l c L Ω _ _ hk3.alg.1 hk2.alg.1
  haveI := UpperTheory.V.Pr.coefIs l c₁
  obtain ⟨m₃, hm₃, -, r₃, -, s₃⟩ := hS3 K L Ω l ι σ N' w χ' η' θ j hD hne M hM0
    (by rw [mul_comm]; exact (Nat.mul_dvd_mul_left l hev.two_dvd).trans hM)
    (UpperTheory.V.Z.Sym.Pl.linkUnr Ω l _ η _ σ g₁ B M L Φ k) (UpperTheory.V.Z.Sym.Pl.chiUnr Ω l c N e ψ χ' j hord hcong M hM L) 2
  obtain ⟨m₂, hm₂, -, r₂, -, -, -, s₂⟩ := hS2 K L Ω l ι σ N' w χ' η' θ j hD κ ka hκ hka 2
  obtain ⟨hfin, a₃, a₂⟩ := _root_.UpperTheory.Gal.projectedFormsSystemPart.twoRuns_alt hA hMod hLam ι H v hL hk2 hk3
    (UpperTheory.Gal.projectedFormsSystemPart.cRealAv hLev hB0 Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 2 ka C₀ (Or.inl rfl) hok hbig hle hf hk2 hv2)
    (UpperTheory.Gal.projectedFormsSystemPart.cRealAv hLev hB0 Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 3 _ C₀ (Or.inr rfl) hok hbig hle hf hk3 hv3)
    (fun R₂ => _root_.UpperTheory.V.Pr.seedPtOf_alt hA Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 2 ka R₂ hk2 χ' j hord hcong m₂ hm₂ _ (by
      convert s₂ using 2 with i i i <;> fin_cases i <;> simp [UpperTheory.V.Fr.w]))
    (fun R₃ => _root_.UpperTheory.V.Pr.seedPtOf_alt hA Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 3 _ R₃ hk3 χ' j hord hcong m₃ hm₃ _ (by
      convert s₃ using 2 with i i i <;> fin_cases i <;> simp [UpperTheory.V.Fr.w]))
  exact ⟨UpperTheory.V.Pr.finPtDown l c c₁ f hle hf Φ 3 hfin, a₃, ka, hk2.alg, a₂⟩
end
