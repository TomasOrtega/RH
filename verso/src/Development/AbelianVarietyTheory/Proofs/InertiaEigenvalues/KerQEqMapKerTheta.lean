import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

namespace GlobalTheory.Per

/- English proof (translation)
Use `le_antisymm (fun s hs => ?_) (Ideal.map_le_iff_le_comap.2 fun a ha => GlobalTheory.RingIface.alg_mem_kerP l ha)` and prove the remaining obligations. Take `⟨k, a, h⟩` from `IsLocalization.Away.surj ((l : ℕ) : Formalism.Per.Ainf l) s`. Establish `hu` using `(IsLocalization.Away.algebraMap_isUnit (S := Formalism.Per.AinfP l) ((l : ℕ) : Formalism.Per.Ainf l)).pow k`. Establish `h0 : Formalism.Per.θP l s = 0` using `GlobalTheory.RingBasics.fontaineTheta_eq_zero_of_mem_ker l s (by rwa [pow_one])`. Establish `h1 : Formalism.Per.θP l (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) a) = 0`.

Rewrite using `[← h, map_mul, h0, zero_mul]`. Rewrite `h1` using `[GlobalTheory.RingIface.fontaineTheta_algebraMap]`. Establish `h2 : Formalism.Per.θ l a = 0` using `Subtype.ext h1`. Rewrite using `[← Ideal.mul_unit_mem_iff_mem _ hu, h]`. Conclude with `Ideal.mem_map_of_mem _ h2`.
-/
theorem kerQ_eq_map_ker_theta (l : ℕ) [Fact l.Prime] :
    Formalism.Per.kerP l = (RingHom.ker (Formalism.Per.θ l)).map
      (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l)) := by
  refine le_antisymm (fun s hs => ?_)
    (Ideal.map_le_iff_le_comap.2 fun a ha => GlobalTheory.RingIface.alg_mem_kerP l ha)
  obtain ⟨k, a, h⟩ := IsLocalization.Away.surj ((l : ℕ) : Formalism.Per.Ainf l) s
  have hu := (IsLocalization.Away.algebraMap_isUnit (S := Formalism.Per.AinfP l)
    ((l : ℕ) : Formalism.Per.Ainf l)).pow k
  have h0 : Formalism.Per.θP l s = 0 := GlobalTheory.RingBasics.fontaineTheta_eq_zero_of_mem_ker l s (by rwa [pow_one])
  have h1 : Formalism.Per.θP l (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) a) = 0 := by
    rw [← h, map_mul, h0, zero_mul]
  rw [GlobalTheory.RingIface.fontaineTheta_algebraMap] at h1
  have h2 : Formalism.Per.θ l a = 0 := Subtype.ext h1
  rw [← Ideal.mul_unit_mem_iff_mem _ hu, h]
  exact Ideal.mem_map_of_mem _ h2

end GlobalTheory.Per
