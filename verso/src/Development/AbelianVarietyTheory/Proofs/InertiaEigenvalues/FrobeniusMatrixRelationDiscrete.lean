import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineDiscPeriodsFrobeniusEqMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinAinfDiscIsDomainNormBounds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscToDiscInjectiveOfAdicBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfAdicTopologicalBasisOverBreuilKisin
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim

/- English proof (translation)
Introduce `l _ K bk τ hτ d ρ _ s Φ hΦ`. Take `⟨h0, h1⟩` from `bk.ρ₀_pos_lt_one`. Use `haveI : IsDomain (bk.DA bk.ρ₀) := (GlobalTheory.BSP.discAinf_isDomain l K bk bk.ρ₀ h0 h1).1`. Take `⟨ι, ⟨tb⟩⟩` from `GlobalTheory.BSP.AinfTopBasis.main l K bk`. Establish `hinj : Function.Injective bk.iA` using `(GlobalTheory.BSP.toDisc_injective_of_topBasis l K bk (Ainf l) bk.ev ι tb bk.ρ₀ h0 h1).1`.

Establish `hΦS : ∀ x, Φ (bk.iS x) = bk.iS (frobS l bk.a x)` using `fun x => by`. Express the relevant statement in the definitionally equal form `Φ (bk.iA (bk.ev x)) = bk.iA (bk.ev (frobS l bk.a x))`. Rewrite using `[hΦ.ext, bk.ev_frob]`. Establish `he : bk.iS (frobS l bk.a bk.E) ≠ 0`. Express the relevant statement in the definitionally equal form `bk.iA (bk.ev (frobS l bk.a bk.E)) ≠ 0`.

Rewrite using `[bk.ev_frob, ← map_zero bk.iA]`. Conclude with `fun h => bk.frobenius_ev_E_ne_zero hτ (hinj h)`. Establish `hL0 : (l : bk.DA bk.ρ₀) ≠ 0` using `fun h => WittVector.p_nonzero l (OCb l) (hinj (by rw [map_natCast, map_zero]; exact h))`. Establish `hQP : s.X.map (bk.iS.comp (frobS l bk.a)) * s.X'.map (bk.iS.comp (frobS l bk.a)) = ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS (frobS l bk.a bk.E) ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀))`. Rewrite using `[← Matrix.map_mul, s.X_mul, Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_one _ (map_zero _) (map_one _)]`.

Simplify using `only [RingHom.comp_apply, map_mul, map_pow, map_natCast]`. Establish `hc : (l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS (frobS l bk.a bk.E) ^ (2 * s.N) ≠ 0` using `mul_ne_zero (pow_ne_zero _ hL0) (pow_ne_zero _ he)`. Establish `hPQ` using `GlobalTheory.BSP.mul_comm_of_mul_eq_smul_one _ _ _ hc hQP`. Establish `hA : (s.X'.map bk.iS).map Φ = s.X'.map (bk.iS.comp (frobS l bk.a))`. Rewrite using `[Matrix.map_map]`.

Use `congr 1`. Use function extensionality and compare the values at `x`. Conclude with `hΦS x`. Establish `hF : (s.F.map (C : Wq l bk.a →+* bk.S)).map bk.iS = s.F.map (bk.iS.comp C)`. Rewrite using `[Matrix.map_map]`.

Both sides reduce to the same expression. Establish `hX : (s.X.map (frobS l bk.a)).map bk.iS = s.X.map (bk.iS.comp (frobS l bk.a))`. Rewrite using `[Matrix.map_map]`. Both sides reduce to the same expression. Establish `h2` using `congrArg (· * s.X.map (bk.iS.comp (frobS l bk.a))) (s.φ Φ hΦ)`.

Simplify using `only [Matrix.map_mul, hA] at h2`. Rewrite `h2` using `[Matrix.smul_mul, Matrix.mul_assoc (s.W.map Φ), hPQ, Matrix.mul_smul, Matrix.mul_one, smul_smul]`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, hF, hX]`. Use `smul_right_injective (Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) (pow_ne_zero s.N he) ?_` and prove the remaining obligations. Simplify using `only`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem WSeed.crystallineDiscPeriods_frobenius_eq_mul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ),
    ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap WittVector.frobenius Φ →
      ((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) • s.W.map Φ =
        s.W * (s.X' * s.F.map (C : Wq l bk.a →+* bk.S) * s.X.map (frobS l bk.a)).map bk.iS := by
  intro l _ K bk τ hτ d ρ _ s Φ hΦ
  obtain ⟨h0, h1⟩ := bk.ρ₀_pos_lt_one
  haveI : IsDomain (bk.DA bk.ρ₀) := (GlobalTheory.BSP.discAinf_isDomain l K bk bk.ρ₀ h0 h1).1
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.BSP.AinfTopBasis.main l K bk
  have hinj : Function.Injective bk.iA := (GlobalTheory.BSP.toDisc_injective_of_topBasis l K bk (Ainf l) bk.ev ι tb bk.ρ₀ h0 h1).1
  have hΦS : ∀ x, Φ (bk.iS x) = bk.iS (frobS l bk.a x) := fun x => by
    change Φ (bk.iA (bk.ev x)) = bk.iA (bk.ev (frobS l bk.a x))
    rw [hΦ.ext, bk.ev_frob]
  have he : bk.iS (frobS l bk.a bk.E) ≠ 0 := by
    change bk.iA (bk.ev (frobS l bk.a bk.E)) ≠ 0
    rw [bk.ev_frob, ← map_zero bk.iA]
    exact fun h => bk.frobenius_ev_E_ne_zero hτ (hinj h)
  have hL0 : (l : bk.DA bk.ρ₀) ≠ 0 := fun h =>
    WittVector.p_nonzero l (OCb l) (hinj (by rw [map_natCast, map_zero]; exact h))
  have hQP : s.X.map (bk.iS.comp (frobS l bk.a)) * s.X'.map (bk.iS.comp (frobS l bk.a)) =
      ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS (frobS l bk.a bk.E) ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    rw [← Matrix.map_mul, s.X_mul, Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_one _ (map_zero _) (map_one _)]
    simp only [RingHom.comp_apply, map_mul, map_pow, map_natCast]
  have hc : (l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS (frobS l bk.a bk.E) ^ (2 * s.N) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hL0) (pow_ne_zero _ he)
  have hPQ := GlobalTheory.BSP.mul_comm_of_mul_eq_smul_one _ _ _ hc hQP
  have hA : (s.X'.map bk.iS).map Φ = s.X'.map (bk.iS.comp (frobS l bk.a)) := by
    rw [Matrix.map_map]; congr 1; funext x; exact hΦS x
  have hF : (s.F.map (C : Wq l bk.a →+* bk.S)).map bk.iS = s.F.map (bk.iS.comp C) := by
    rw [Matrix.map_map]; rfl
  have hX : (s.X.map (frobS l bk.a)).map bk.iS = s.X.map (bk.iS.comp (frobS l bk.a)) := by
    rw [Matrix.map_map]; rfl
  have h2 := congrArg (· * s.X.map (bk.iS.comp (frobS l bk.a))) (s.φ Φ hΦ)
  simp only [Matrix.map_mul, hA] at h2
  rw [Matrix.smul_mul, Matrix.mul_assoc (s.W.map Φ), hPQ, Matrix.mul_smul, Matrix.mul_one, smul_smul] at h2
  rw [Matrix.map_mul, Matrix.map_mul, hF, hX]
  refine smul_right_injective (Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) (pow_ne_zero s.N he) ?_
  dsimp only
  calc bk.iS (frobS l bk.a bk.E) ^ s.N • (((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) •
        s.W.map Φ)
      = ((l : bk.DA bk.ρ₀) ^ s.c₁ * ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS (frobS l bk.a bk.E) ^ (2 * s.N))) •
        s.W.map Φ := by rw [smul_smul]; congr 1; ring
    _ = _ := h2
    _ = _ := by rw [Matrix.smul_mul]; simp only [Matrix.mul_assoc]

end GlobalTheory.BKLim
