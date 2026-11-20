import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEvDefectDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefectCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLieOfAdditive
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

/- English proof (translation)
Introduce `p _ O E _ _ _ hF G d c f hf`. Use `haveI : IsAdicComplete (Ideal.span {(p : O)}) O := hF.complete`. Establish `hinj : Function.Injective (MvPowerSeries.map (σ` using `Fin d) (algebraMap O E)) := by`. Introduce `s t h`. Use extensionality with `α`.

Use `congrArg (MvPowerSeries.coeff α) h` as an intermediate fact. Simplify using `only [MvPowerSeries.coeff_map] at this`. Conclude with `hF.inj this`. Take `⟨hex, hcomp⟩` from `GlobalTheory.QLog.defect_compat p O E hF G d c f hf`. Use `choose s hs _ using fun n : ℕ => hex (p ^ n)`.

Establish `hadd` using `GlobalTheory.QLog.cobOne_ev_defect_dvd p O E hF G d c f hf`. Take `⟨l, hl, huniq⟩` from `GlobalTheory.LieOfAdditive.existsUnique_lie_of_additive p O G (fun n => c.ev n (s n)) (fun n => hadd n (s n) (hs n)) (fun n => hcomp n (s n) (s (n + 1)) (hs n) (hs (n + 1)))`. Use `⟨l, ⟨fun n => In.top_iff.2 ⟨s n, hs n⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `n w φ t hφ ht`. Establish `: t = s n` using `hinj (ht.trans (hs n).symm)`.

Substitute `this` using the available equality. Conclude with `hl n w φ hφ`. Introduce `l' hl'`. Conclude with `huniq l' fun n w φ hφ => hl'.2 n w φ (s n) hφ (hs n)`.
-/
theorem QLog.Chart.existsUnique_isLie : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (f : MvPowerSeries (Fin d) E), QL c.μ ⊤ f → ∃! l : G.dual.Lie, c.IsLie f l := by
  intro p _ O E _ _ _ hF G d c f hf
  haveI : IsAdicComplete (Ideal.span {(p : O)}) O := hF.complete
  have hinj : Function.Injective (MvPowerSeries.map (σ := Fin d) (algebraMap O E)) := by
    intro s t h
    ext α
    have := congrArg (MvPowerSeries.coeff α) h
    simp only [MvPowerSeries.coeff_map] at this
    exact hF.inj this
  obtain ⟨hex, hcomp⟩ := GlobalTheory.QLog.defect_compat p O E hF G d c f hf
  choose s hs _ using fun n : ℕ => hex (p ^ n)
  have hadd := GlobalTheory.QLog.cobOne_ev_defect_dvd p O E hF G d c f hf
  obtain ⟨l, hl, huniq⟩ := GlobalTheory.LieOfAdditive.existsUnique_lie_of_additive p O G (fun n => c.ev n (s n))
    (fun n => hadd n (s n) (hs n)) (fun n => hcomp n (s n) (s (n + 1)) (hs n) (hs (n + 1)))
  refine ⟨l, ⟨fun n => In.top_iff.2 ⟨s n, hs n⟩, ?_⟩, ?_⟩
  · intro n w φ t hφ ht
    have : t = s n := hinj (ht.trans (hs n).symm)
    subst this
    exact hl n w φ hφ
  · intro l' hl'
    exact huniq l' fun n w φ hφ => hl'.2 n w φ (s n) hφ (hs n)

end GlobalTheory
