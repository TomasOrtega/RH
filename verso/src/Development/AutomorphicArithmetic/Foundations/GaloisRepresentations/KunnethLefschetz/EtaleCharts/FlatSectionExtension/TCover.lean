import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

/- English proof (translation)
Introduce `K _ W Z Y q i π D d B T j r hsq`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hloc : IsZariskiLocalAtSource @Smooth.{0}` using `HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Smooth)`. Unfold `eP`. Conclude with `IsZariskiLocalAtSource.sigmaDesc fun p => inferInstance`.

Use `⟨fun x => ?_⟩` and prove the remaining obligations. Establish `hx : r x ∈ i ⁻¹ᵁ (⨆ α, B.V α)` using `B.cover (Set.mem_univ (r x))`. Establish `hx' : i (r x) ∈ (⨆ α, B.V α)` using `hx`. Take `⟨α, hα⟩` from `TopologicalSpace.Opens.mem_iSup.mp hx'`. Establish `h3 : π (j x) = i (r x)`.

Rewrite using `[← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hsq.w]`. Establish `h4 : j x ∈ π ⁻¹ᵁ B.V α`. Express the relevant statement in the definitionally equal form `π (j x) ∈ B.V α`. Rewrite using `[h3]`. Conclude with `hα`.

Take `⟨k, hk⟩` from `TopologicalSpace.Opens.mem_iSup.mp ((B.c α).C_cover h4)`. Set `p : B.ι × Fin d` to `(α, k)`. Establish `hp : x ∈ oT B j p` using `hk`. Set `y : (oT B j p : Scheme.{0})` to `⟨x, hp⟩`. Establish `hc : tI B j p ≫ eP B j = (oT B j p).ι`.

Unfold `tI eP`. Conclude with `Sigma.ι_desc _ _`. Use `⟨tI B j p y, ?_⟩` and prove the remaining obligations. Establish `hy : (tI B j p ≫ eP B j) y = x`. Rewrite using `[hc]`.

Both sides reduce to the same expression. Rewrite using `[← Scheme.Hom.comp_apply]`. Conclude with `hy`.
-/
theorem UpperTheory.Gal.KunnethLefschetz.G.PX.tCover :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y) (r : T ⟶ W), IsPullback j r π i → Smooth (eP B j) ∧ Surjective (eP B j) := by
  intro K _ W Z Y q i π D d B T j r hsq
  refine ⟨?_, ?_⟩
  · have hloc : IsZariskiLocalAtSource @Smooth.{0} :=
      HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Smooth)
    unfold eP
    exact IsZariskiLocalAtSource.sigmaDesc fun p => inferInstance
  · refine ⟨fun x => ?_⟩
    have hx : r x ∈ i ⁻¹ᵁ (⨆ α, B.V α) := B.cover (Set.mem_univ (r x))
    have hx' : i (r x) ∈ (⨆ α, B.V α) := hx
    obtain ⟨α, hα⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
    have h3 : π (j x) = i (r x) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hsq.w]
    have h4 : j x ∈ π ⁻¹ᵁ B.V α := by
      change π (j x) ∈ B.V α
      rw [h3]; exact hα
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp ((B.c α).C_cover h4)
    let p : B.ι × Fin d := (α, k)
    have hp : x ∈ oT B j p := hk
    let y : (oT B j p : Scheme.{0}) := ⟨x, hp⟩
    have hc : tI B j p ≫ eP B j = (oT B j p).ι := by
      unfold tI eP
      exact Sigma.ι_desc _ _
    refine ⟨tI B j p y, ?_⟩
    have hy : (tI B j p ≫ eP B j) y = x := by
      rw [hc]
      rfl
    rw [← Scheme.Hom.comp_apply]
    exact hy
