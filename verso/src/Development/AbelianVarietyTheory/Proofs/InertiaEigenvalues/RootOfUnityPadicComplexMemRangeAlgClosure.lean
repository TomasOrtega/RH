import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory

/- English proof (translation)
Introduce `l _ x m hm hx`. Use `haveI : NeZero m := ⟨hm.ne'⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) m`. Establish `hζ' : IsPrimitiveRoot (algebraMap (Om l) ℂ_[l] ζ) m` using `hζ.map_of_injective (algebraMap (Om l) ℂ_[l]).injective`. Take `⟨i, -, hi⟩` from `hζ'.eq_pow_of_pow_eq_one hx`.

Conclude with `⟨ζ ^ i, by rw [← hi]; exact map_pow (algebraMap (Om l) ℂ_[l]) ζ i⟩`.
-/
theorem rootOfUnity_mem_range_Om : ∀ (l : ℕ) [Fact l.Prime] (x : ℂ_[l]) (m : ℕ), 0 < m → x ^ m = 1 → ∃ z : Om l, (z : ℂ_[l]) = x := by
  intro l _ x m hm hx
  haveI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) m
  have hζ' : IsPrimitiveRoot (algebraMap (Om l) ℂ_[l] ζ) m :=
    hζ.map_of_injective (algebraMap (Om l) ℂ_[l]).injective
  obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one hx
  exact ⟨ζ ^ i, by rw [← hi]; exact map_pow (algebraMap (Om l) ℂ_[l]) ζ i⟩

end GlobalTheory
