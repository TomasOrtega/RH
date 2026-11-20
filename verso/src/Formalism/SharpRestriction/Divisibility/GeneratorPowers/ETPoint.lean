import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ETSpan
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCSpan

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField Formalism.MainNotions.ModuliIntegralCharts ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

/- English proof (translation)
Set `S : Set ℕ` to `Set.range fun z : X => (Q (y + R' • z)).toNat`. Establish `hS : S.Nonempty` using `⟨_, 0, rfl⟩`. Take `⟨z, hz⟩` from `Nat.sInf_mem hS`. Use `⟨z, fun z' => ?_⟩` and prove the remaining obligations. Establish `h1 : sInf S ≤ (Q (y + R' • z')).toNat` using `Nat.sInf_le ⟨z', rfl⟩`.

Establish `h2` using `hQ (y + R' • z)`. Establish `h3` using `hQ (y + R' • z')`. Establish `h4 : (Q (y + R' • z)).toNat = sInf S` using `hz`. Use linear arithmetic over natural numbers and integers.
-/
theorem etPoint_min {X : Type} [AddCommGroup X] (Q : X → ℤ) (hQ : ∀ a, 0 ≤ Q a) (y : X) (R' : ℕ) :
    ∃ z : X, ∀ z' : X, Q (y + R' • z) ≤ Q (y + R' • z') := by
  let S : Set ℕ := Set.range fun z : X => (Q (y + R' • z)).toNat
  have hS : S.Nonempty := ⟨_, 0, rfl⟩
  obtain ⟨z, hz⟩ := Nat.sInf_mem hS
  refine ⟨z, fun z' => ?_⟩
  have h1 : sInf S ≤ (Q (y + R' • z')).toNat := Nat.sInf_le ⟨z', rfl⟩
  have h2 := hQ (y + R' • z)
  have h3 := hQ (y + R' • z')
  have h4 : (Q (y + R' • z)).toNat = sInf S := hz
  omega

end Formalism.MainNotions.ModuliIntegralCharts.H1
