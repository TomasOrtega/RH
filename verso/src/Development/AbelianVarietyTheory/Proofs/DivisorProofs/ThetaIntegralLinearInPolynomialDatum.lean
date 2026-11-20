import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombRSingleNil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThK.FiniteLevelDerivatives

namespace GlobalTheory.ThK.ThetaLin

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a a' G X om om' hKP hT Φ hΦ Ψ hΨ r`. Establish `hP` using `(GlobalTheory.ThK.Check.isPair_of_isTriple hT).1`. Establish `hsch : GlobalTheory.ThK.PolData B G.M ≤ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a'))`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `Φ ⟨f, -, φ, hSB, hev, rfl⟩`.

Conclude with `GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hev.and hT.geo.hM.std).mono fun v h => h.1.trans h.2)`. Establish `hcond : a + a' + 2 * min (a - G.p) G.p < 2 * a ∨ min (a - G.p) G.p = 0`. Establish `h1` using `hT.geo.eBig`. Establish `h2` using `hT.geo.lt`. Establish `h3 : min (a - G.p) G.p ≤ G.p` using `min_le_right _ _`.

Use `left`. Use linear arithmetic over natural numbers and integers. Establish `hW` using `(GlobalTheory.T.weil_convergence_of_kernel hKP F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hP hcond).1`. Establish `hΦs` using `hsch hΦ`. Establish `hΨs` using `hsch hΨ`.

Establish `hrΦs : r • Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a'))` using `Submodule.smul_mem _ r hΦs`. Establish `pres : ∀ x, ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), om x Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a'))` using `fun x Φ hΦ => (GlobalTheory.WeilM.IsUWeilPair.isUSplitting hT.weil).pres x Φ hΦ`. Use function extensionality and compare the values at `h`. Establish `e : ∀ g, theta om (r • Φ + Ψ) g h = r * theta om Φ g h + theta om Ψ g h` using `fun g => by`. Simplify using `only [theta, map_add, map_smul]`.

Establish `hs : r • om (g, h) Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a'))` using `Submodule.smul_mem _ r (pres _ _ hΦs)`. Rewrite using `[GlobalTheory.WeilM.thetaSum_add F hs (pres _ _ hΨs), GlobalTheory.WeilM.thetaSum_smul]`. Simplify using `only [Model.I, e, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[integral_add (((hW Φ hΦs).1 h).const_mul r) ((hW Ψ hΨs).1 h), integral_const_mul]`.
-/
theorem I_lin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M, ∀ Ψ ∈ GlobalTheory.ThK.PolData B G.M, ∀ r : ℂ,
      G.M.I om (r • Φ + Ψ) = r • G.M.I om Φ + G.M.I om Ψ := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hKP hT Φ hΦ Ψ hΨ r
  have hP := (GlobalTheory.ThK.Check.isPair_of_isTriple hT).1
  have hsch : GlobalTheory.ThK.PolData B G.M ≤ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')) := by
    refine Submodule.span_le.mpr ?_
    rintro Φ ⟨f, -, φ, hSB, hev, rfl⟩
    exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hev.and hT.geo.hM.std).mono fun v h => h.1.trans h.2)
  have hcond : a + a' + 2 * min (a - G.p) G.p < 2 * a ∨ min (a - G.p) G.p = 0 := by
    have h1 := hT.geo.eBig
    have h2 := hT.geo.lt
    have h3 : min (a - G.p) G.p ≤ G.p := min_le_right _ _
    left; omega
  have hW := (GlobalTheory.T.weil_convergence_of_kernel hKP F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hP hcond).1
  have hΦs := hsch hΦ
  have hΨs := hsch hΨ
  have hrΦs : r • Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')) := Submodule.smul_mem _ r hΦs
  have pres : ∀ x, ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), om x Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')) :=
    fun x Φ hΦ => (GlobalTheory.WeilM.IsUWeilPair.isUSplitting hT.weil).pres x Φ hΦ
  funext h
  have e : ∀ g, theta om (r • Φ + Ψ) g h = r * theta om Φ g h + theta om Ψ g h := fun g => by
    simp only [theta, map_add, map_smul]
    have hs : r • om (g, h) Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')) := Submodule.smul_mem _ r (pres _ _ hΦs)
    rw [GlobalTheory.WeilM.thetaSum_add F hs (pres _ _ hΨs), GlobalTheory.WeilM.thetaSum_smul]
  simp only [Model.I, e, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [integral_add (((hW Φ hΦs).1 h).const_mul r) ((hW Ψ hΨs).1 h), integral_const_mul]

end GlobalTheory.ThK.ThetaLin
