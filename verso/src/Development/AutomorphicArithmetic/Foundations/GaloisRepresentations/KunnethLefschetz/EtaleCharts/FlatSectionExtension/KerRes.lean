import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

/- English proof (translation)
Introduce `K _ W Z Y q i π D d B α N hN h`. Use `haveI := B.closed`. Establish `hUV : (⟨N, hN⟩ : Z.affineOpens) ≤ ⟨B.V α, (B.c α).affine⟩` using `h`. Establish `key` using `i.ker.map_ideal hUV`. Rewrite `key` using `[Scheme.Hom.ker_apply, Scheme.Hom.ker_apply]`.

Express the relevant statement in the definitionally equal form `Ideal.map _ (RingHom.ker (i.app (B.V α)).hom) = RingHom.ker (i.app N).hom at key`. Rewrite `key` using `[(B.c α).ker, Ideal.map_span, ← Set.range_comp]`. Rewrite using `[← key]`. Both sides reduce to the same expression.
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
