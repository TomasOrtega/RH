import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport

open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RgExh

/- English proof (translation)
Introduce `n V _ _ P l x j hl hx hd`. Proceed by induction on `l with`. Consider the case `nil => simpa using And.intro hx hd`. Consider the case `cons i l ih`. Take `⟨ih1, ih2⟩` from `ih fun k hk => hl k (List.mem_cons_of_mem i hk)`.

Establish `hi : P i` using `hl i List.mem_cons_self`. Simplify using `only [List.map_cons, List.prod_cons, Module.End.mul_apply, List.length_cons]`. Prove the components needed by the constructor for the conclusion. Introduce `A hA k hk`. Take `⟨h1, h2⟩` from `CompanionTheory.D.LK.cre_ne hA`.

Distinguish the cases in `hki : k = i`. Conclude with `hki ▸ hi`. Conclude with `ih1 _ h2 k (Finset.mem_erase.2 ⟨hki, hk⟩)`. Introduce `A hA`. Take `⟨h1, h2⟩` from `CompanionTheory.D.LK.cre_ne hA`.

Establish `h3` using `ih2 _ h2`. Establish `h4` using `Finset.card_erase_add_one h1`. Use linear arithmetic over natural numbers and integers.
-/
theorem suppIn_deg_cre_prod : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (P : Pos n → Prop) (l : List (Pos n)) (x : Cn n V) (j : ℕ),
    (∀ i ∈ l, P i) → SuppIn P x → Deg j x →
      SuppIn P (((l.map cre).prod : Module.End ℂ (Cn n V)) x) ∧
        Deg (j + l.length) (((l.map cre).prod : Module.End ℂ (Cn n V)) x) := by
  intro n V _ _ P l x j hl hx hd
  induction l with
  | nil => simpa using And.intro hx hd
  | cons i l ih =>
    obtain ⟨ih1, ih2⟩ := ih fun k hk => hl k (List.mem_cons_of_mem i hk)
    have hi : P i := hl i List.mem_cons_self
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, List.length_cons]
    constructor
    · intro A hA k hk
      obtain ⟨h1, h2⟩ := CompanionTheory.D.LK.cre_ne hA
      by_cases hki : k = i
      · exact hki ▸ hi
      · exact ih1 _ h2 k (Finset.mem_erase.2 ⟨hki, hk⟩)
    · intro A hA
      obtain ⟨h1, h2⟩ := CompanionTheory.D.LK.cre_ne hA
      have h3 := ih2 _ h2
      have h4 := Finset.card_erase_add_one h1
      omega

end GlobalTheory.CompanionTheory.RgExh
