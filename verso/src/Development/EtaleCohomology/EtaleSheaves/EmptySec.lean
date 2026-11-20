import Development.EtaleCohomology.EtaleSheaves.A9OfA0A1EigenbasisA6

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafClosedSH0PfEmpty
open LateralTheory.E.E4 LateralTheory.E.LeafClosedSH0Pf

/- English proof (translation)
Introduce `R _ F X hX`. Establish `hb : (⊥ : Sieve X) ∈ Scheme.etaleTopology X`. Conclude with `Scheme.bot_mem_grothendieckTopology X`. Establish `hT` using `Sheaf.isTerminalOfBotCover F X hb`. Establish `hZ : IsZero (F.obj.obj (op X))` using `hT.isZero`.

Conclude with `(ModuleCat.isZero_iff_subsingleton.mp hZ)`.
-/
theorem emptySec : LeafEmptySec := by
  intro R _ F X hX
  have hb : (⊥ : Sieve X) ∈ Scheme.etaleTopology X := by
    exact Scheme.bot_mem_grothendieckTopology X
  have hT := Sheaf.isTerminalOfBotCover F X hb
  have hZ : IsZero (F.obj.obj (op X)) := hT.isZero
  exact (ModuleCat.isZero_iff_subsingleton.mp hZ)

end LateralTheory.E.LeafClosedSH0PfEmpty
