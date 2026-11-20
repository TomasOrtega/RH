import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.LtChar
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.LTCrys
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.EqNegOneOfJumpAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapAlgebraMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FKEqResDeg
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.LocLanglands GlobalTheory.WeilDeligne TensorProduct CompanionTheory.PRW.ACWD GlobalTheory.PZ GlobalTheory.PMC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.PMC.Bridge

/- English proof (translation)
Unfold `phiVB φVB`. Use `congr 1`. Conclude with `LinearMap.ext fun b => (P.PD_φ K b).symm`.
-/
theorem phiVB_eq {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) :
    phiVB P (LL := ↥LL.1) (V := Fin 1 → ↥LL.1) = φVB (P.PD K) (LL := ↥LL.1) (V := Fin 1 → ↥LL.1) := by
  unfold phiVB φVB
  congr 1
  exact LinearMap.ext fun b => (P.PD_φ K b).symm

/- English proof (translation)
Introduce `H E Ω _ _ _ _ _ l _ P AI hT w A h O _ _ _ Bw hB a ha π hπ j₀ LL ψ hc hψ`. Take `⟨τ₀, χ, π', z, h₀, hz, hπ', hχ⟩` from `GlobalTheory.PMC.BrChar.main E Ω l w A h O Bw hB a ha π hπ j₀ LL ψ hc hψ`. Take `⟨h1, h2, h3⟩` from `H l P AI hT Bw.Kw LL χ π' z hz τ₀`. Establish `hrep : Bw.repE LL ψ = lineRep (K` using `Bw.Kw) (LL := LL) (ltChar τ₀ χ) := by`. Use `MonoidHom.ext fun g => LinearMap.ext fun v => funext fun i => ?_` and prove the remaining obligations.

Establish `e : ((ψ (Bw.e.symm g) : GL (Fin 1) ↥LL.1) : Matrix (Fin 1) (Fin 1) ↥LL.1) 0 0 = τ₀ ((χ g : (↥Bw.Kw.1)ˣ) : ↥Bw.Kw.1)` using `Subtype.ext (by`. Use `hχ (Bw.e.symm g)` as an intermediate fact. Rewrite using `[MulEquiv.apply_symm_apply] at this)` and apply the resulting hypothesis. Rewrite using `[Subsingleton.elim i 0]`. Simplify using `[LocBridge.repE, lineRep, ltChar, Matrix.mulVec, dotProduct, e]`.

Establish `hf : resDeg l w = Module.finrank ℚ_[l] ↥(K0 Bw.Kw)` using `(GlobalTheory.AinfK.fK_eq_resDeg Bw h hB).symm`. Rewrite `h1`, `h2`, `h3` using `[← hrep]`. Use `⟨h1, fun x hx => ⟨(τ₀ (π' : ↥Bw.Kw.1))⁻¹, ?_, ?_⟩, fun τ' hτ n => ?_, fun τ' hτ n => ?_⟩` and prove the remaining obligations. Rewrite using `[← hπ']`. Use `push_cast`.

Both sides reduce to the same expression. Rewrite using `[hf, phiVB_eq P Bw.Kw LL]`. Conclude with `h2 x hx`. Establish `e : τ' = τ₀` using `GlobalTheory.PY.LTInh.algHom_ext Bw fun x => Subtype.ext ((hτ x).symm.trans (h₀ x))`. Simplify `h3 τ' n` using `[LocBridge.multE, e]`.

Establish `e : τ' ≠ τ₀` using `fun e => hτ (e ▸ h₀)`. Simplify `h3 τ' n` using `[LocBridge.multE, e]`.
-/
theorem main : GlobalTheory.PMC.LTLoc → GlobalTheory.PY.LTCrys := by
  intro H E Ω _ _ _ _ _ l _ P AI hT w A h O _ _ _ Bw hB a ha π hπ j₀ LL ψ hc hψ
  obtain ⟨τ₀, χ, π', z, h₀, hz, hπ', hχ⟩ := GlobalTheory.PMC.BrChar.main E Ω l w A h O Bw hB a ha π hπ j₀ LL ψ hc hψ
  obtain ⟨h1, h2, h3⟩ := H l P AI hT Bw.Kw LL χ π' z hz τ₀
  have hrep : Bw.repE LL ψ = lineRep (K := Bw.Kw) (LL := LL) (ltChar τ₀ χ) := by
    refine MonoidHom.ext fun g => LinearMap.ext fun v => funext fun i => ?_
    have e : ((ψ (Bw.e.symm g) : GL (Fin 1) ↥LL.1) : Matrix (Fin 1) (Fin 1) ↥LL.1) 0 0 =
        τ₀ ((χ g : (↥Bw.Kw.1)ˣ) : ↥Bw.Kw.1) := Subtype.ext (by
      have := hχ (Bw.e.symm g)
      rwa [MulEquiv.apply_symm_apply] at this)
    rw [Subsingleton.elim i 0]
    simp [LocBridge.repE, lineRep, ltChar, Matrix.mulVec, dotProduct, e]
  have hf : resDeg l w = Module.finrank ℚ_[l] ↥(K0 Bw.Kw) := (GlobalTheory.AinfK.fK_eq_resDeg Bw h hB).symm
  rw [← hrep] at h1 h2 h3
  refine ⟨h1, fun x hx => ⟨(τ₀ (π' : ↥Bw.Kw.1))⁻¹, ?_, ?_⟩, fun τ' hτ n => ?_, fun τ' hτ n => ?_⟩
  · rw [← hπ']
    push_cast
    rfl
  · rw [hf, phiVB_eq P Bw.Kw LL]
    exact h2 x hx
  · have e : τ' = τ₀ := GlobalTheory.PY.LTInh.algHom_ext Bw fun x => Subtype.ext ((hτ x).symm.trans (h₀ x))
    simpa [LocBridge.multE, e] using h3 τ' n
  · have e : τ' ≠ τ₀ := fun e => hτ (e ▸ h₀)
    simpa [LocBridge.multE, e] using h3 τ' n

end GlobalTheory.PMC.Bridge

end
