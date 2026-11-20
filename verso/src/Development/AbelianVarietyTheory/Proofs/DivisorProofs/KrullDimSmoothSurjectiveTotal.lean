import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingNumberFieldTwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimLeZeroOfSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimFiberStalkEqQuotientStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

set_option autoImplicit false
namespace GlobalTheory.SmoothDimTotal
open IsLocalRing

/- English proof (translation)
Rewrite using `[topologicalKrullDim, Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X)), Order.krullDim_eq_iSup_coheight]`. Simplify using `only [ringKrullDim_stalk_eq_coheight]`.
-/
theorem topologicalKrullDim_eq_iSup_stalk (X : Scheme.{0}) :
    topologicalKrullDim X = ⨆ x : X, ringKrullDim (X.presheaf.stalk x) := by
  rw [topologicalKrullDim, Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X)),
    Order.krullDim_eq_iSup_coheight]
  simp only [ringKrullDim_stalk_eq_coheight]

/- English proof (translation)
Use `letI : Algebra (B.presheaf.stalk (π y)) (Y.presheaf.stalk y) := (π.stalkMap y).hom.toAlgebra`. Use `haveI : Module.Flat (B.presheaf.stalk (π y)) (Y.presheaf.stalk y) := Flat.stalkMap π y`. Establish `hc : (maximalIdeal (Y.presheaf.stalk y)).comap (π.stalkMap y).hom = maximalIdeal (B.presheaf.stalk (π y))` using `IsLocalRing.maximalIdeal_comap _`. Use `haveI : (maximalIdeal (Y.presheaf.stalk y)).LiesOver (maximalIdeal (B.presheaf.stalk (π y))) := ⟨hc.symm⟩`. Establish `h` using `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal (B.presheaf.stalk (π y))) (maximalIdeal (Y.presheaf.stalk y))`.

Use `set I : Ideal (Y.presheaf.stalk y) := (maximalIdeal (B.presheaf.stalk (π y))).map (π.stalkMap y).hom with hIdef`. Establish `hI : I ≤ maximalIdeal (Y.presheaf.stalk y)` using `Ideal.map_le_iff_le_comap.2 hc.ge`. Use `haveI : Nontrivial (Y.presheaf.stalk y ⧸ I) := Ideal.Quotient.nontrivial_iff.2 (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top hI)`. Use `haveI : IsLocalRing (Y.presheaf.stalk y ⧸ I) := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective`. Establish `hm : (maximalIdeal (Y.presheaf.stalk y)).map (Ideal.Quotient.mk I) = maximalIdeal (Y.presheaf.stalk y ⧸ I)` using `by haveI := Ideal.IsMaximal.map_of_surjective_of_ker_le (m := maximalIdeal (Y.presheaf.stalk y)) (Ideal.Quotient.mk_surjective (I := I)) (by rw [Ideal.mk_ker]; exact hI)`.

Conclude with `IsLocalRing.eq_maximalIdeal this`. Rewrite using `[← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h, ← hm]`. Both sides reduce to the same expression.
-/
theorem ringKrullDim_stalk_eq_add (B Y : Scheme.{0}) [IsLocallyNoetherian B] [IsLocallyNoetherian Y]
    (π : Y ⟶ B) [Flat π] (y : Y) :
    ringKrullDim (Y.presheaf.stalk y) = ringKrullDim (B.presheaf.stalk (π y)) +
      ringKrullDim (Y.presheaf.stalk y ⧸ (maximalIdeal (B.presheaf.stalk (π y))).map (π.stalkMap y).hom) := by
  letI : Algebra (B.presheaf.stalk (π y)) (Y.presheaf.stalk y) := (π.stalkMap y).hom.toAlgebra
  haveI : Module.Flat (B.presheaf.stalk (π y)) (Y.presheaf.stalk y) := Flat.stalkMap π y
  have hc : (maximalIdeal (Y.presheaf.stalk y)).comap (π.stalkMap y).hom = maximalIdeal (B.presheaf.stalk (π y)) :=
    IsLocalRing.maximalIdeal_comap _
  haveI : (maximalIdeal (Y.presheaf.stalk y)).LiesOver (maximalIdeal (B.presheaf.stalk (π y))) :=
    ⟨hc.symm⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (maximalIdeal (B.presheaf.stalk (π y))) (maximalIdeal (Y.presheaf.stalk y))
  set I : Ideal (Y.presheaf.stalk y) := (maximalIdeal (B.presheaf.stalk (π y))).map (π.stalkMap y).hom with hIdef
  have hI : I ≤ maximalIdeal (Y.presheaf.stalk y) := Ideal.map_le_iff_le_comap.2 hc.ge
  haveI : Nontrivial (Y.presheaf.stalk y ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.2 (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top hI)
  haveI : IsLocalRing (Y.presheaf.stalk y ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hm : (maximalIdeal (Y.presheaf.stalk y)).map (Ideal.Quotient.mk I) = maximalIdeal (Y.presheaf.stalk y ⧸ I) := by
    haveI := Ideal.IsMaximal.map_of_surjective_of_ker_le (m := maximalIdeal (Y.presheaf.stalk y))
      (Ideal.Quotient.mk_surjective (I := I)) (by rw [Ideal.mk_ker]; exact hI)
    exact IsLocalRing.eq_maximalIdeal this
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
    ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h, ← hm]
  rfl

/- English proof (translation)
The claim follows from `GlobalTheory.T.ringKrullDim_fiber_stalk_eq_quotient B Y π b z`.
-/
theorem fibre_stalk (B Y : Scheme.{0}) (π : Y ⟶ B) (b : B) (z : π.fiber b) :
    ringKrullDim ((π.fiber b).presheaf.stalk z) = ringKrullDim (Y.presheaf.stalk (π.fiberι b z) ⧸
      (IsLocalRing.maximalIdeal (B.presheaf.stalk (π (π.fiberι b z)))).map (π.stalkMap (π.fiberι b z)).hom) :=
  GlobalTheory.T.ringKrullDim_fiber_stalk_eq_quotient B Y π b z

/- English proof (translation)
Use `haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := n)`. Conclude with `MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension n) (IsPullback.of_hasPullback π (B.fromSpecResidueField b)) ‹_›`.
-/
theorem smoothOfRelativeDimension_fiber (B Y : Scheme.{0}) (π : Y ⟶ B) (n : ℕ) [SmoothOfRelativeDimension n π] (b : B) :
    SmoothOfRelativeDimension n (π.fiberToSpecResidueField b) := by
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := n)
  exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension n) (IsPullback.of_hasPullback π (B.fromSpecResidueField b)) ‹_›

/- English proof (translation)
Use `haveI : Nonempty X := ⟨x⟩`. Rewrite using `[ringKrullDim_stalk_eq_coheight, ← GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth f n h]`. Conclude with `(Order.coheight_le_krullDim x).trans (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))).ge`.
-/
theorem ringKrullDim_stalk_le_of_smooth (K : Type) [Field K] (X : Scheme.{0}) (f : X ⟶ Spec (.of K)) (n : ℕ)
    (h : SmoothOfRelativeDimension n f) (x : X) : ringKrullDim (X.presheaf.stalk x) ≤ n := by
  haveI : Nonempty X := ⟨x⟩
  rw [ringKrullDim_stalk_eq_coheight, ← GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth f n h]
  exact (Order.coheight_le_krullDim x).trans (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))).ge

/- English proof (translation)
Establish `h` using `fibre_stalk B Y π (π y) (π.asFiber y)`. Rewrite `h` using `[π.fiberι_asFiber]`. Rewrite using `[← h]`. Conclude with `ringKrullDim_stalk_le_of_smooth (B.residueField (π y)) _ (π.fiberToSpecResidueField (π y)) n (smoothOfRelativeDimension_fiber B Y π n (π y)) _`.
-/
theorem fib_le (B Y : Scheme.{0}) (π : Y ⟶ B) (n : ℕ) [SmoothOfRelativeDimension n π] (y : Y) :
    ringKrullDim (Y.presheaf.stalk y ⧸ (IsLocalRing.maximalIdeal (B.presheaf.stalk (π y))).map (π.stalkMap y).hom) ≤ n := by
  have h := fibre_stalk B Y π (π y) (π.asFiber y)
  rw [π.fiberι_asFiber] at h
  rw [← h]
  exact ringKrullDim_stalk_le_of_smooth (B.residueField (π y)) _ (π.fiberToSpecResidueField (π y)) n
    (smoothOfRelativeDimension_fiber B Y π n (π y)) _

/- English proof (translation)
Use `haveI : Smooth π := SmoothOfRelativeDimension.smooth n π`. Take `⟨z, -, hz⟩` from `nonempty_inter_closedPoints (X := π.fiber (π y₀)) (Z := Set.univ) ⟨π.asFiber y₀, trivial⟩ isClosed_univ.isLocallyClosed`. Establish `hmem : π.fiberι (π y₀) z ∈ Set.range (π.fiberι (π y₀))` using `⟨z, rfl⟩`. Rewrite `hmem` using `[π.range_fiberι]`. Use `⟨π.fiberι (π y₀) z, hmem, ?_⟩` and prove the remaining obligations.

Rewrite using `[← fibre_stalk B Y π (π y₀) z]`. Establish `hs` using `smoothOfRelativeDimension_fiber B Y π n (π y₀)`. Conclude with `(GlobalTheory.CutDegree.ringKrullDim_stalk (K := B.residueField (π y₀)) (f' := π.fiberToSpecResidueField (π y₀)) hs (by rwa [mem_closedPoints_iff] at hz)).ge`.
-/
theorem fib_ge (B Y : Scheme.{0}) (π : Y ⟶ B) (n : ℕ) [SmoothOfRelativeDimension n π] (y₀ : Y) :
    ∃ y : Y, π y = π y₀ ∧ (n : WithBot ℕ∞) ≤ ringKrullDim (Y.presheaf.stalk y ⧸ (IsLocalRing.maximalIdeal (B.presheaf.stalk (π y))).map (π.stalkMap y).hom) := by
  haveI : Smooth π := SmoothOfRelativeDimension.smooth n π
  obtain ⟨z, -, hz⟩ := nonempty_inter_closedPoints (X := π.fiber (π y₀)) (Z := Set.univ) ⟨π.asFiber y₀, trivial⟩
    isClosed_univ.isLocallyClosed
  have hmem : π.fiberι (π y₀) z ∈ Set.range (π.fiberι (π y₀)) := ⟨z, rfl⟩
  rw [π.range_fiberι] at hmem
  refine ⟨π.fiberι (π y₀) z, hmem, ?_⟩
  rw [← fibre_stalk B Y π (π y₀) z]
  have hs := smoothOfRelativeDimension_fiber B Y π n (π y₀)
  exact (GlobalTheory.CutDegree.ringKrullDim_stalk (K := B.residueField (π y₀)) (f' := π.fiberToSpecResidueField (π y₀)) hs
    (by rwa [mem_closedPoints_iff] at hz)).ge

/- English proof (translation)
Proceed by induction on `x using WithBot.recBotCoe with`. Consider the case `bot => exact bot_le`. Consider the case `coe m`. Proceed by induction on `m using ENat.recTopCoe with`. Consider the case `top`.

It suffices to derive a contradiction. Establish `h2 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ (((d + 1 : ℕ) : ℕ∞) : WithBot ℕ∞)` using `h`. Conclude with `absurd (WithBot.coe_le_coe.1 h2) (not_le.2 (ENat.coe_lt_top _))`. Consider the case `coe m`. Establish `h' : m ≤ d + 1` using `by exact_mod_cast h`.

Establish `hne' : m ≠ d + 1` using `fun e => hne (by rw [e]; rfl)`. Conclude with `(show m ≤ d by omega)` after adjusting the coercions.
-/
theorem le_of_le_succ_of_ne {x : WithBot ℕ∞} {d : ℕ} (h : x ≤ ((d + 1 : ℕ) : WithBot ℕ∞))
    (hne : x ≠ ((d + 1 : ℕ) : WithBot ℕ∞)) : x ≤ (d : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe m =>
    induction m using ENat.recTopCoe with
    | top =>
      exfalso
      have h2 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ (((d + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := h
      exact absurd (WithBot.coe_le_coe.1 h2) (not_le.2 (ENat.coe_lt_top _))
    | coe m =>
      have h' : m ≤ d + 1 := by exact_mod_cast h
      have hne' : m ≠ d + 1 := fun e => hne (by rw [e]; rfl)
      exact_mod_cast (show m ≤ d by omega)

/- English proof (translation)
Introduce `B Y _ π n d _ hsurj hB`. Use `haveI : Smooth π := SmoothOfRelativeDimension.smooth n π`. Use `haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian π`. Rewrite `hB`, the goal using `[topologicalKrullDim_eq_iSup_stalk]`. Establish `hcast : ((d + 1 : ℕ) : WithBot ℕ∞) + (n : WithBot ℕ∞) = ((d + n + 1 : ℕ) : WithBot ℕ∞)`.

Rewrite using `[← Nat.cast_add]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Apply `le_antisymm` to reduce the goal to its premises. Use `iSup_le fun y => ?_` and prove the remaining obligations.

Rewrite using `[ringKrullDim_stalk_eq_add B Y π y, ← hcast]`. Conclude with `add_le_add (hB ▸ le_iSup (fun b : B => ringKrullDim (B.presheaf.stalk b)) (π y)) (fib_le B Y π n y)`. Choose the witnesses or unpack the hypotheses as in `⟨b, hb⟩ : ∃ b : B, ringKrullDim (B.presheaf.stalk b) = ((d + 1 : ℕ) : WithBot ℕ∞) := by`. Assume the negation of the conclusion as `hno`. Use `push_neg at hno`.

Establish `: (⨆ b : B, ringKrullDim (B.presheaf.stalk b)) ≤ (d : WithBot ℕ∞)` using `iSup_le fun b => le_of_le_succ_of_ne (hB ▸ le_iSup (fun b : B => ringKrullDim (B.presheaf.stalk b)) b) (hno b)`. Rewrite `this` using `[hB]`. Establish `: d + 1 ≤ d` using `by exact_mod_cast this`. Use linear arithmetic over natural numbers and integers. Take `⟨y₀, rfl⟩` from `hsurj b`.

Take `⟨y, hy, hfib⟩` from `fib_ge B Y π n y₀`. Rewrite `hb` using `[← hy]`. Use `le_iSup_of_le y ?_` and prove the remaining obligations. Rewrite using `[ringKrullDim_stalk_eq_add B Y π y, hb, ← hcast]`. Conclude with `add_le_add le_rfl hfib`.
-/
theorem topologicalKrullDim_eq_of_smooth_surjective : ∀ (B Y : Scheme.{0}) [IsLocallyNoetherian B] (π : Y ⟶ B) (n d : ℕ) [SmoothOfRelativeDimension n π], Function.Surjective π → topologicalKrullDim B = (d + 1 : ℕ) → topologicalKrullDim Y = (d + n + 1 : ℕ) := by
  intro B Y _ π n d _ hsurj hB
  haveI : Smooth π := SmoothOfRelativeDimension.smooth n π
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian π
  rw [topologicalKrullDim_eq_iSup_stalk] at hB ⊢
  have hcast : ((d + 1 : ℕ) : WithBot ℕ∞) + (n : WithBot ℕ∞) = ((d + n + 1 : ℕ) : WithBot ℕ∞) := by
    rw [← Nat.cast_add]; congr 1; omega
  apply le_antisymm
  · refine iSup_le fun y => ?_
    rw [ringKrullDim_stalk_eq_add B Y π y, ← hcast]
    exact add_le_add (hB ▸ le_iSup (fun b : B => ringKrullDim (B.presheaf.stalk b)) (π y)) (fib_le B Y π n y)
  · obtain ⟨b, hb⟩ : ∃ b : B, ringKrullDim (B.presheaf.stalk b) = ((d + 1 : ℕ) : WithBot ℕ∞) := by
      by_contra hno
      push_neg at hno
      have : (⨆ b : B, ringKrullDim (B.presheaf.stalk b)) ≤ (d : WithBot ℕ∞) :=
        iSup_le fun b => le_of_le_succ_of_ne (hB ▸ le_iSup (fun b : B => ringKrullDim (B.presheaf.stalk b)) b) (hno b)
      rw [hB] at this
      have : d + 1 ≤ d := by exact_mod_cast this
      omega
    obtain ⟨y₀, rfl⟩ := hsurj b
    obtain ⟨y, hy, hfib⟩ := fib_ge B Y π n y₀
    rw [← hy] at hb
    refine le_iSup_of_le y ?_
    rw [ringKrullDim_stalk_eq_add B Y π y, hb, ← hcast]
    exact add_le_add le_rfl hfib

end GlobalTheory.SmoothDimTotal
