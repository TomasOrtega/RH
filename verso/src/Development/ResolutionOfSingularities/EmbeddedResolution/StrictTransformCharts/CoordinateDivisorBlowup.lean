import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.Saturation
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChartComputations
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
private theorem etaleChart_restrictOpens_map_comp_affineSpaceFinToSpec {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    (V : U.toScheme.Opens) :
    (V.ι ≫ c.map) ≫ affineSpaceFinToSpec k m = V.ι ≫ (U.ι ≫ p) := by
  rw [Category.assoc, c.comp_struct]

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
private theorem etaleChart_restrictOpens_map_etale {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    (V : U.toScheme.Opens) :
    AlgebraicGeometry.Etale (V.ι ≫ c.map) := by
  have : AlgebraicGeometry.Etale c.map := c.isEtale
  infer_instance

def EtaleChart.restrictOpens {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    (V : U.toScheme.Opens) : EtaleChart (U.ι ≫ p) V m where
  map := V.ι ≫ c.map
  comp_struct := etaleChart_restrictOpens_map_comp_affineSpaceFinToSpec c V
  isEtale := etaleChart_restrictOpens_map_etale c V

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem EtaleChart.restrictOpens_map {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    (V : U.toScheme.Opens) :
    (c.restrictOpens V).map = V.ι ≫ c.map := rfl

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem EtaleChart.restrictIdeal_coordIdeal {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    (V : U.toScheme.Opens) (T : Finset (Fin m)) :
    restrictIdeal (c.coordIdeal T) V = (c.restrictOpens V).coordIdeal T := by
  simp only [restrictIdeal_eq_comap_ι, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, EtaleChart.restrictOpens_map,
    Scheme.IdealSheafData.comap_comp]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem EtaleChart.coordIdeal_ideal_eq_span {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    {V : U.toScheme.Opens} (hV : IsAffineOpen V) (T : Finset (Fin m)) :
    (c.coordIdeal T).ideal ⟨V, hV⟩ = Ideal.span ((c.restrictOpens V).coord '' ↑T) :=
  EtaleChart.ideal_eq_span_coord (c.restrictOpens V) hV (c.coordIdeal T) T
    (c.restrictIdeal_coordIdeal V T)

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem EtaleChart.coordIdeal_singleton_ideal_eq_span {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    {V : U.toScheme.Opens} (hV : IsAffineOpen V) (i : Fin m) :
    (c.coordIdeal {i}).ideal ⟨V, hV⟩ = Ideal.span {(c.restrictOpens V).coord i} := by
  rw [c.coordIdeal_ideal_eq_span hV {i}, Finset.coe_singleton, Set.image_singleton]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem EtaleChart.saturation_mul_coordIdeal {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    (j s : Fin m) (hjs : j ≠ s)
    [QuasiCompact (saturationι (c.coordIdeal {s})
      (c.coordIdeal {j} * c.coordIdeal {s}))] :
    saturation (c.coordIdeal {s}) (c.coordIdeal {j} * c.coordIdeal {s}) = c.coordIdeal {j} := by
  have key : ∀ V : U.toScheme.affineOpens,
      (saturation (c.coordIdeal {s}) (c.coordIdeal {j} * c.coordIdeal {s})).ideal V =
        (c.coordIdeal {j}).ideal V := by
    intro V
    have ht : (c.coordIdeal {s}).ideal V = Ideal.span {(c.restrictOpens V.1).coord s} :=
      c.coordIdeal_singleton_ideal_eq_span V.2 s
    have hu : (c.coordIdeal {j}).ideal V = Ideal.span {(c.restrictOpens V.1).coord j} :=
      c.coordIdeal_singleton_ideal_eq_span V.2 j
    have hfactor : (c.coordIdeal {j} * c.coordIdeal {s}).ideal V =
        Ideal.span {(c.restrictOpens V.1).coord s} * (c.coordIdeal {j}).ideal V := by
      rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, ht]
      exact mul_comm _ _
    have hJ : ∀ g : Γ(U.toScheme, V.1),
        (c.restrictOpens V.1).coord s * g ∈ (c.coordIdeal {j}).ideal V →
          g ∈ (c.coordIdeal {j}).ideal V := by
      intro g hg
      rw [hu] at hg ⊢
      exact mem_span_coord_of_coord_mul_mem V.2 (c.restrictOpens V.1) hjs g hg
    exact saturation_ideal_eq_of_eq_mul _ _ V _ ht _ hfactor hJ
  exact Scheme.IdealSheafData.ext (funext key)

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem EtaleChart.saturation_coordIdeal_self {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ} (c : EtaleChart p U m) (s : Fin m)
    [QuasiCompact (saturationι (c.coordIdeal {s}) (c.coordIdeal {s}))] :
    saturation (c.coordIdeal {s}) (c.coordIdeal {s}) = ⊤ := by
  have key : ∀ V : U.toScheme.affineOpens,
      (saturation (c.coordIdeal {s}) (c.coordIdeal {s})).ideal V = ⊤ := by
    intro V
    have ht : (c.coordIdeal {s}).ideal V = Ideal.span {(c.restrictOpens V.1).coord s} :=
      c.coordIdeal_singleton_ideal_eq_span V.2 s
    exact saturation_ideal_eq_top_of_span_pow_le (c.coordIdeal {s}) (c.coordIdeal {s}) V
      ((c.restrictOpens V.1).coord s) ht 1 (by simp [ht])
  ext V
  simp [key V, Scheme.IdealSheafData.ideal_top, Pi.top_apply]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Simplify to obtain the desired conclusion from the available facts.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
private theorem mem_span_coord_of_coord_pow_mul_mem {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ}
    (hU : IsAffineOpen U) (c : EtaleChart p U m) {j s : Fin m} (hjs : j ≠ s) :
    ∀ (n : ℕ) (x : ↑(X.presheaf.obj (op U))),
      c.coord s ^ n * x ∈ Ideal.span {c.coord j} → x ∈ Ideal.span {c.coord j} := by
  intro n
  induction n with
  | zero =>
      intro x hx
      simpa using hx
  | succ n ih =>
      intro x hx
      refine mem_span_coord_of_coord_mul_mem hU c hjs x (ih (c.coord s * x) ?_)
      have h : c.coord s ^ n * (c.coord s * x) = c.coord s ^ (n + 1) * x := by ring
      rw [h]
      exact hx

/- English proof (translation)
By extensionality, compare the relevant components. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem EtaleChart.saturation_coordIdeal_of_ne {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    (j s : Fin m) (hjs : j ≠ s)
    [QuasiCompact (saturationι (c.coordIdeal {s}) (c.coordIdeal {j}))] :
    saturation (c.coordIdeal {s}) (c.coordIdeal {j}) = c.coordIdeal {j} := by
  ext V f
  have hVs : (c.coordIdeal {s}).ideal V = Ideal.span {(c.restrictOpens V.1).coord s} :=
    c.coordIdeal_singleton_ideal_eq_span V.2 s
  have hVj : (c.coordIdeal {j}).ideal V = Ideal.span {(c.restrictOpens V.1).coord j} :=
    c.coordIdeal_singleton_ideal_eq_span V.2 j
  rw [mem_saturation_ideal_iff (c.coordIdeal {s}) (c.coordIdeal {j}) V
      ((c.restrictOpens V.1).coord s) hVs f, hVj]
  constructor
  · rintro ⟨n, hn⟩
    exact mem_span_coord_of_coord_pow_mul_mem V.2 (c.restrictOpens V.1) hjs n f hn
  · intro hf
    exact ⟨0, by simpa using hf⟩

namespace BlowupChart

variable {X X₁ : Scheme.{u}} {k : Type u} [Field k]
  {p : X ⟶ Spec (CommRingCat.of k)} {π : X₁ ⟶ X} {U : X.Opens} {m : ℕ}
  {c : EtaleChart p U m} {S : Finset (Fin m)} {s : Fin m}

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem restrictIdeal_strictTransform_of_mem_of_ne (B : BlowupChart π c S s)
    (Z D : X.IdealSheafData) [QuasiCompact (strictTransformι π Z D)]
    (hs : s ∈ S) (hZ : restrictIdeal Z U = c.coordIdeal S)
    (j : Fin m) (hj : j ∈ S) (hjs : j ≠ s)
    (hD : restrictIdeal D U = c.coordIdeal {j}) :
    restrictIdeal (Blowup.strictTransform π Z D) B.domain = B.chart.coordIdeal {j} := by
  have hqc : QuasiCompact (saturationι (Z.comap π) (D.comap π)) :=
    inferInstanceAs (QuasiCompact (strictTransformι π Z D))
  have hE : restrictIdeal (Z.comap π) B.domain = B.chart.coordIdeal {s} := by
    have h := B.restrictIdeal_exceptionalIdeal Z hs hZ
    rwa [Blowup.exceptionalIdeal_eq_comap] at h
  have hDrestrict : restrictIdeal (D.comap π) B.domain =
      B.chart.coordIdeal {j} * B.chart.coordIdeal {s} :=
    B.restrictIdeal_comap_coordIdeal_of_mem D j hj hjs hD
  have hq := quasiCompact_saturationι_restrictIdeal (Z.comap π) (D.comap π) B.domain
  rw [hE, hDrestrict] at hq
  have := hq
  rw [strictTransform_eq_saturation, restrictIdeal_saturation (Z.comap π) (D.comap π) B.domain,
    hE, hDrestrict]
  exact B.chart.saturation_mul_coordIdeal j s hjs

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem restrictIdeal_strictTransform_coordIdeal_self (B : BlowupChart π c S s)
    (Z D : X.IdealSheafData) [QuasiCompact (strictTransformι π Z D)]
    (hs : s ∈ S) (hZ : restrictIdeal Z U = c.coordIdeal S)
    (hD : restrictIdeal D U = c.coordIdeal {s}) :
    restrictIdeal (Blowup.strictTransform π Z D) B.domain = ⊤ := by
  have hqc : QuasiCompact (saturationι (Z.comap π) (D.comap π)) :=
    inferInstanceAs (QuasiCompact (strictTransformι π Z D))
  have hE : restrictIdeal (Z.comap π) B.domain = B.chart.coordIdeal {s} := by
    have h := B.restrictIdeal_exceptionalIdeal Z hs hZ
    rwa [Blowup.exceptionalIdeal_eq_comap] at h
  have hDrestrict : restrictIdeal (D.comap π) B.domain = B.chart.coordIdeal {s} :=
    B.restrictIdeal_comap_coordIdeal_self D hD
  have hq := quasiCompact_saturationι_restrictIdeal (Z.comap π) (D.comap π) B.domain
  rw [hE, hDrestrict] at hq
  have := hq
  rw [strictTransform_eq_saturation, restrictIdeal_saturation (Z.comap π) (D.comap π) B.domain,
    hE, hDrestrict]
  exact B.chart.saturation_coordIdeal_self s

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Assume the hypotheses and unpack their components. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem restrictIdeal_strictTransform_coordIdeal_of_notMem (B : BlowupChart π c S s)
    (Z D : X.IdealSheafData) [QuasiCompact (strictTransformι π Z D)]
    (hs : s ∈ S) (hZ : restrictIdeal Z U = c.coordIdeal S)
    (j : Fin m) (hj : j ∉ S)
    (hD : restrictIdeal D U = c.coordIdeal {j}) :
    restrictIdeal (Blowup.strictTransform π Z D) B.domain = B.chart.coordIdeal {j} := by
  have hqc : QuasiCompact (saturationι (Z.comap π) (D.comap π)) :=
    inferInstanceAs (QuasiCompact (strictTransformι π Z D))
  have hjs : j ≠ s := by
    rintro rfl
    exact hj hs
  have hE : restrictIdeal (Z.comap π) B.domain = B.chart.coordIdeal {s} := by
    have h := B.restrictIdeal_exceptionalIdeal Z hs hZ
    rwa [Blowup.exceptionalIdeal_eq_comap] at h
  have hDrestrict : restrictIdeal (D.comap π) B.domain = B.chart.coordIdeal {j} :=
    B.restrictIdeal_comap_coordIdeal_of_not_mem D j hj hD
  have hq := quasiCompact_saturationι_restrictIdeal (Z.comap π) (D.comap π) B.domain
  rw [hE, hDrestrict] at hq
  have := hq
  rw [strictTransform_eq_saturation, restrictIdeal_saturation (Z.comap π) (D.comap π) B.domain,
    hE, hDrestrict]
  exact B.chart.saturation_coordIdeal_of_ne j s hjs

/- English proof (translation)
Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails.

A detailed English derivation is pending.
-/
theorem restrictIdeal_strictTransform_coordIdeal (B : BlowupChart π c S s)
    (Z D : X.IdealSheafData) [QuasiCompact (strictTransformι π Z D)]
    (hs : s ∈ S) (hZ : restrictIdeal Z U = c.coordIdeal S)
    (j : Fin m) (hD : restrictIdeal D U = c.coordIdeal {j}) :
    restrictIdeal (Blowup.strictTransform π Z D) B.domain =
      if j = s then ⊤ else B.chart.coordIdeal {j} := by
  by_cases hj : j = s
  · rw [if_pos hj]
    have hD' : restrictIdeal D U = c.coordIdeal {s} := by rw [hD, hj]
    exact B.restrictIdeal_strictTransform_coordIdeal_self Z D hs hZ hD'
  · rw [if_neg hj]
    by_cases hjS : j ∈ S
    · exact B.restrictIdeal_strictTransform_of_mem_of_ne Z D hs hZ j hjS hj hD
    · exact B.restrictIdeal_strictTransform_coordIdeal_of_notMem Z D hs hZ j hjS hD

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem restrictIdeal_strictTransform_of_eq_top (B : BlowupChart π c S s)
    (Z D : X.IdealSheafData) (hD : restrictIdeal D U = ⊤) :
    restrictIdeal (Blowup.strictTransform π Z D) B.domain = ⊤ := by
  have h1 : restrictIdeal (D.comap π) B.domain = ⊤ := B.restrictIdeal_comap_top D hD
  have h2 : D.comap π ≤ Blowup.strictTransform π Z D := comap_le_strictTransform π Z D
  have h3 : restrictIdeal (D.comap π) B.domain ≤
      restrictIdeal (Blowup.strictTransform π Z D) B.domain := by
    rw [restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι]
    exact Scheme.IdealSheafData.comap_mono (Scheme.Opens.ι B.domain) h2
  rw [h1] at h3
  exact le_antisymm le_top h3

end BlowupChart

end FunctorialResolution.EmbeddedResolution

end
