import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Express the relevant assertion in an equivalent form by its definition.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.KunnethLefschetz.G.PX.kerRes :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α : B.ι) {N : Z.Opens} (_ : IsAffineOpen N) (h : N ≤ B.V α), RingHom.ker (i.app N).hom = Ideal.span (Set.range (tN B α h)) := by
  intro K _ W Z Y q i π D d B α N hN h
  haveI := B.closed
  have hUV : (⟨N, hN⟩ : Z.affineOpens) ≤ ⟨B.V α, (B.c α).affine⟩ := h
  have key := i.ker.map_ideal hUV
  rw [Scheme.Hom.ker_apply, Scheme.Hom.ker_apply] at key
  change Ideal.map _ (RingHom.ker (i.app (B.V α)).hom) = RingHom.ker (i.app N).hom at key
  rw [(B.c α).ker, Ideal.map_span, ← Set.range_comp] at key
  rw [← key]
  rfl
