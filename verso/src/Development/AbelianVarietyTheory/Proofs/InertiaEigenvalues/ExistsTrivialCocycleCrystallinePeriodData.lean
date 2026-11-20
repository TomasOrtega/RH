import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim

/- English proof (translation)
Introduce `l _ K bk τ _ d ρ s`. Use `⟨{ s with κ := fun _ => 1, gal := ?_, fix := fun _ _ => rfl, nopole := ?_, log := ?_ }, fun _ => rfl⟩` and prove the remaining obligations. Introduce `g G hG`. Rewrite using `[Matrix.mul_one]`. Conclude with `s.gal g G hG`.

Introduce `g G hG i j`. Take `⟨k, hk⟩` from `s.nopole bk.ι ((ainfHom K g).comp bk.ι)`. Establish `h1` using `map_dvd bk.iA (hk i j)`. Establish `hX : (s.X.map bk.iS).map G = s.X.map (fun x => bk.iA (Per.σA (g : GQ l) (bk.ev x)))`. Use extensionality with `a b`.

Simplify using `only [Matrix.map_apply, BK.iS, RingHom.comp_apply]`. Conclude with `hG.ext _`. Establish `hu : IsUnit (bk.iA ((l : Ainf l) ^ k))`. Rewrite using `[map_pow, map_natCast]`. Conclude with `(isUnit_l_disc l (bk.ev X) bk.ρ₀).pow k`.

Express the relevant statement in the definitionally equal form `bk.iA ((bk.ev bk.E) ^ (2 * s.N)) ∣ bk.iA ((l : Ainf l) ^ k * (s.X'.map bk.ev * s.X.map (fun x => Per.σA (g : GQ l) (bk.ev x))) i j) at h1`. Rewrite `h1` using `[map_mul]`. Rewrite using `[Matrix.mul_one, hX]`. Establish `h2` using `(hu.dvd_mul_left).1 h1`. Use `h2 using 1` and compare the differences between its conclusion and the goal.

Simplify using `only [BK.iS, RingHom.comp_apply, map_pow]`. Simplify using `only [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul, BK.iS, RingHom.comp_apply]`. Introduce `m`. Use `⟨0, 1, fun i j => by simp, fun g G hG i j => ?_⟩` and prove the remaining obligations. Simplify using `[Matrix.map_one]`.
-/
theorem wseed_of_seed : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (s : Seed bk d ρ τ), ∃ s' : WSeed bk d ρ τ, ∀ g, s'.κ g = 1 := by
  intro l _ K bk τ _ d ρ s
  refine ⟨{ s with κ := fun _ => 1, gal := ?_, fix := fun _ _ => rfl, nopole := ?_, log := ?_ }, fun _ => rfl⟩
  · intro g G hG
    rw [Matrix.mul_one]
    exact s.gal g G hG
  · intro g G hG i j
    obtain ⟨k, hk⟩ := s.nopole bk.ι ((ainfHom K g).comp bk.ι)
    have h1 := map_dvd bk.iA (hk i j)
    have hX : (s.X.map bk.iS).map G = s.X.map (fun x => bk.iA (Per.σA (g : GQ l) (bk.ev x))) := by
      ext a b
      simp only [Matrix.map_apply, BK.iS, RingHom.comp_apply]
      exact hG.ext _
    have hu : IsUnit (bk.iA ((l : Ainf l) ^ k)) := by
      rw [map_pow, map_natCast]
      exact (isUnit_l_disc l (bk.ev X) bk.ρ₀).pow k
    change bk.iA ((bk.ev bk.E) ^ (2 * s.N)) ∣ bk.iA ((l : Ainf l) ^ k * (s.X'.map bk.ev * s.X.map (fun x => Per.σA (g : GQ l) (bk.ev x))) i j) at h1
    rw [map_mul] at h1
    rw [Matrix.mul_one, hX]
    have h2 := (hu.dvd_mul_left).1 h1
    convert h2 using 1
    · simp only [BK.iS, RingHom.comp_apply, map_pow]
    · simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul, BK.iS, RingHom.comp_apply]
  · intro m
    refine ⟨0, 1, fun i j => by simp, fun g G hG i j => ?_⟩
    simp [Matrix.map_one]

end GlobalTheory.BKLim
