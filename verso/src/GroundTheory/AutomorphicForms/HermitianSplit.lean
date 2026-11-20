import Mathlib
import GroundTheory.AutomorphicForms.UnitarySplit
import GroundTheory.AutomorphicForms.HermitianSpaces

namespace GroundTheory.Automorphic

open Module Matrix

variable {F : Type*} [Field F]
variable {V V' : Type*} [AddCommGroup V] [Module (F × F) V] [AddCommGroup V'] [Module (F × F) V']

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem map_fst_map_conjHom_prod {ι : Type*} (M : Matrix ι ι (F × F)) :
    (M.map (conjHom F (F × F))).map (RingHom.fst F F) = M.map (RingHom.snd F F) := by
  ext i j
  show (conj F (F × F) (M i j)).1 = (M i j).2
  rw [conj_prod]

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem map_snd_map_conjHom_prod {ι : Type*} (M : Matrix ι ι (F × F)) :
    (M.map (conjHom F (F × F))).map (RingHom.snd F F) = M.map (RingHom.fst F F) := by
  ext i j
  show (conj F (F × F) (M i j)).2 = (M i j).1
  rw [conj_prod]

end GroundTheory.Automorphic
