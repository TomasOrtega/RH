import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FibrePointsLEId
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

/- English proof (translation)
Introduce `Z X f _ _`. Establish `hopen : IsOpen (Set.range (pullback.diagonal f))` using `(pullback.diagonal f).isOpenEmbedding.isOpen_range`. Establish `hcl : IsClosedImmersion (diagCompl f).ι` using `IsClosedImmersion.of_isPreimmersion _ (by`. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `hopen.isClosed_compl)`.

Unfold `diagComplHom`. Conclude with `⟨inferInstance, inferInstance⟩`.
-/
theorem diagComplHom_isFinite_etale : ∀ {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f],
    IsFinite (GlobalTheory.EtC.Tr.diagComplHom f) ∧ Etale (GlobalTheory.EtC.Tr.diagComplHom f) := by
  intro Z X f _ _
  have hopen : IsOpen (Set.range (pullback.diagonal f)) :=
    (pullback.diagonal f).isOpenEmbedding.isOpen_range
  have hcl : IsClosedImmersion (diagCompl f).ι :=
    IsClosedImmersion.of_isPreimmersion _ (by
      rw [Scheme.Opens.range_ι]
      exact hopen.isClosed_compl)
  unfold diagComplHom
  exact ⟨inferInstance, inferInstance⟩

end GlobalTheory.EtC.Tr
