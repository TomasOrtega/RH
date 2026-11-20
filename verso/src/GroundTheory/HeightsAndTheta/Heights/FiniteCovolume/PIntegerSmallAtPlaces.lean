import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField

/- English proof (translation)
Introduce `a ha hlt`. Assume the negation of the conclusion as `hne`. Set `b : 𝓞 E` to `⟨a, ha⟩`. Establish `hb : b ≠ 0` using `fun h => hne (congrArg Subtype.val h)`. Set `w : InfinitePlace E` to `Classical.arbitrary _`.

Establish `h1 : 1 ≤ w b` using `InfinitePlace.one_le_of_lt_one hb (fun z _ => hlt z)`. Conclude with `absurd (hlt w) (not_lt.mpr h1)`.
-/
theorem IntegerSmallAtPlaces.proof (E : Type*) [Field E] [NumberField E] :
    IntegerSmallAtPlaces.Statement E := by
  intro a ha hlt
  by_contra hne
  let b : 𝓞 E := ⟨a, ha⟩
  have hb : b ≠ 0 := fun h => hne (congrArg Subtype.val h)
  let w : InfinitePlace E := Classical.arbitrary _
  have h1 : 1 ≤ w b := InfinitePlace.one_le_of_lt_one hb (fun z _ => hlt z)
  exact absurd (hlt w) (not_lt.mpr h1)

end GroundTheory.Heights₂.Heights.FiniteCovolume
