import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

/- English proof (translation)
Introduce `K _ W Z Y q i π D d B`. Use `⟨?_, ⟨fun x => ?_⟩⟩` and prove the remaining obligations. Establish `: IsZariskiLocalAtSource @Smooth.{0}` using `HasRingHomProperty.instIsZariskiLocalAtSource`. Unfold `cP`. Conclude with `IsZariskiLocalAtSource.sigmaDesc (P := @Smooth.{0}) (fun α => inferInstance)`.

Establish `hx : i x ∈ ⨆ α, B.V α` using `B.cover (Set.mem_univ x)`. Take `⟨α, hα⟩` from `(TopologicalSpace.Opens.mem_iSup).1 hx`. Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : x ∈ Set.range (oW B α).ι := by`. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `hα`.

Establish `h : wI B α ≫ cP B = (oW B α).ι`. Simplify using `[wI, cP]`. Use `⟨wI B α y, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, h, hy]`.
-/
theorem UpperTheory.Gal.KunnethLefschetz.G.PX.wCover :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d), Smooth (cP B) ∧ Surjective (cP B) := by
  intro K _ W Z Y q i π D d B
  refine ⟨?_, ⟨fun x => ?_⟩⟩
  · have : IsZariskiLocalAtSource @Smooth.{0} := HasRingHomProperty.instIsZariskiLocalAtSource
    unfold cP
    exact IsZariskiLocalAtSource.sigmaDesc (P := @Smooth.{0}) (fun α => inferInstance)
  · have hx : i x ∈ ⨆ α, B.V α := B.cover (Set.mem_univ x)
    obtain ⟨α, hα⟩ := (TopologicalSpace.Opens.mem_iSup).1 hx
    obtain ⟨y, hy⟩ : x ∈ Set.range (oW B α).ι := by
      rw [Scheme.Opens.range_ι]
      exact hα
    have h : wI B α ≫ cP B = (oW B α).ι := by
      simp [wI, cP]
    refine ⟨wI B α y, ?_⟩
    rw [← Scheme.Hom.comp_apply, h, hy]
