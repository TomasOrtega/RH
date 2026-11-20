import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsTrDataGaussianIntOne

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory

/- English proof (translation)
Establish `himg : ((integralClosure (O0 p) Ω).val : integralClosure (O0 p) Ω → Ω) '' (Set.range (zS T) ∪ Set.range (qS T)) = Set.range T.ζ ∪ Set.range T.qq`. Rewrite using `[Set.image_union, ← Set.range_comp, ← Set.range_comp]`. Both sides reduce to the same expression. Establish `hmap : (towerAlg T).map (integralClosure (O0 p) Ω).val = Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq)`. Rewrite using `[towerAlg, AlgHom.map_adjoin, himg]`.

Rewrite using `[← hmap, Subalgebra.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨s, h, rfl⟩`. Introduce and unpack `⟨t, ht, hts⟩`.

Establish `: t = s` using `Subtype.ext hts`. Conclude with `this ▸ ht`.
-/
theorem towerAlg_mem_iff (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω]
    (T : Tower p Ω) (s : (integralClosure (O0 p) Ω)) :
    s ∈ towerAlg T ↔ (s : Ω) ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq) := by
  have himg : ((integralClosure (O0 p) Ω).val : integralClosure (O0 p) Ω → Ω) ''
      (Set.range (zS T) ∪ Set.range (qS T)) = Set.range T.ζ ∪ Set.range T.qq := by
    rw [Set.image_union, ← Set.range_comp, ← Set.range_comp]
    rfl
  have hmap : (towerAlg T).map (integralClosure (O0 p) Ω).val =
      Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq) := by
    rw [towerAlg, AlgHom.map_adjoin, himg]
  rw [← hmap, Subalgebra.mem_map]
  constructor
  · intro h; exact ⟨s, h, rfl⟩
  · rintro ⟨t, ht, hts⟩
    have : t = s := Subtype.ext hts
    exact this ▸ ht

end GlobalTheory
