import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum

set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

/- English proof (translation)
Use function extensionality and compare the values at `i`. Distinguish the cases in `h : i = c`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne h]`.
-/
theorem cast_add_single_one {r : ℕ} (m : Fin r → ℕ) (c : Fin r) :
    (fun i => (((m + Pi.single c 1 : Fin r → ℕ) i : ℕ) : ℝ)) =
      (fun i => (m i : ℝ)) + Pi.single c 1 := by
  funext i
  by_cases h : i = c
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]

/- English proof (translation)
Introduce `ι _ r a b s cs m`. Proceed by induction on `cs generalizing m with`. Consider the case `nil => simp [DL, DLR, coneTerm, Fr, linF]`. Consider the case `cons c cs ih`. Establish `h1 : DL (c :: cs) (coneTerm a b s) m = DL cs (coneTerm a b s) (m + Pi.single c 1) - DL cs (coneTerm a b s) m` using `rfl`.

Establish `h2 : ∀ x : Fin r → ℝ, DLR (c :: cs) (Fr a b s 0) x = DLR cs (Fr a b s 0) (x + Pi.single c 1) - DLR cs (Fr a b s 0) x` using `fun _ => rfl`. Rewrite using `[h1, h2, ih, ih, cast_add_single_one]`.
-/
theorem DL_coneTerm_eq_DLR : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (s : ℂ) (cs : List (Fin r)) (m : Fin r → ℕ),
  DL cs (coneTerm a b s) m = DLR cs (Fr a b s 0) (fun i => (m i : ℝ)) := by
  intro ι _ r a b s cs m
  induction cs generalizing m with
  | nil => simp [DL, DLR, coneTerm, Fr, linF]
  | cons c cs ih =>
    have h1 : DL (c :: cs) (coneTerm a b s) m =
        DL cs (coneTerm a b s) (m + Pi.single c 1) - DL cs (coneTerm a b s) m := rfl
    have h2 : ∀ x : Fin r → ℝ, DLR (c :: cs) (Fr a b s 0) x =
        DLR cs (Fr a b s 0) (x + Pi.single c 1) - DLR cs (Fr a b s 0) x := fun _ => rfl
    rw [h1, h2, ih, ih, cast_add_single_one]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
