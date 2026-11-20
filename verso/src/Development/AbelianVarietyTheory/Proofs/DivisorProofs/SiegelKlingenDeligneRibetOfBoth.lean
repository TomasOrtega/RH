import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet

namespace GlobalTheory

/- English proof (translation)
Introduce `a b` and use `⟨a, b⟩`.
-/
theorem siegelKlingenDeligneRibet_of_both :
    GlobalTheory.Published.SiegelKlingen → GlobalTheory.Published.DeligneRibet → GlobalTheory.Published.SiegelKlingenDeligneRibet :=
  fun a b => ⟨a, b⟩

end GlobalTheory
