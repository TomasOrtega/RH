import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegPFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Formalism.LocalToGlobal.ProjectiveLattices.UnitIndepOfCharts
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ChartCoverFOfSectionBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsRingHomComplexCompEqOfCountable

noncomputable section

namespace GlobalTheory.Frames

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace ComplexTransfer

/- English proof (translation)
Use `letI := σ.toAlgebra`. Use `haveI : Flat (spMap σ) := by`. Rewrite using `[HasRingHomProperty.Spec_iff (P := @Flat)]`. Conclude with `RingHom.flat_algebraMap_iff.2 inferInstance`. Use `haveI : Surjective (spMap σ) := ⟨fun p => ⟨IsLocalRing.closedPoint Ω, Subsingleton.elim _ _⟩⟩`.

Conclude with `Flat.epi_of_flat_of_surjective _`.
-/
theorem epi_spMap_field {k Ω : Type} [Field k] [Field Ω] (σ : k →+* Ω) : Epi (spMap σ) := by
  letI := σ.toAlgebra
  haveI : Flat (spMap σ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 inferInstance
  haveI : Surjective (spMap σ) := ⟨fun p => ⟨IsLocalRing.closedPoint Ω, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

/- English proof (translation)
Take `⟨n, f, hf⟩` from `Algebra.FiniteType.iff_quotient_mvPolynomial''.1 h`. Use `haveI : Countable (MvPolynomial (Fin n) K) := by`. Rewrite using `[← Cardinal.mk_le_aleph0_iff]`. Use `(MvPolynomial.cardinalMk_le_max).trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.

Conclude with `hf.countable`.
-/
theorem countable_of_finiteType (K A : Type) [CommRing K] [Countable K] [CommRing A] [Algebra K A]
    [h : Algebra.FiniteType K A] : Countable A := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 h
  haveI : Countable (MvPolynomial (Fin n) K) := by
    rw [← Cardinal.mk_le_aleph0_iff]
    refine (MvPolynomial.cardinalMk_le_max).trans ?_
    simp
  exact hf.countable

/- English proof (translation)
Set `s : Set k` to `Set.range φ ∪ Set.range ψ`. Establish `hs : s.Countable` using `(Set.countable_range _).union (Set.countable_range _)`. Set `L` to `IntermediateField.adjoin K s`. Establish `hL : Countable L`. Use `hs.to_subtype` as an intermediate fact.

Rewrite using `[← Cardinal.mk_le_aleph0_iff]`. Use `(IntermediateField.cardinalMk_adjoin_le K s).trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Use `letI : Algebra K ℂ := σ.toAlgebra`. Take `⟨j⟩` from `GlobalTheory.nonempty_algHom_complex_of_countable K L`.

Use `⟨L, inferInstance, inferInstance, L.val, j, φ.codRestrict L.toSubalgebra fun a => IntermediateField.subset_adjoin K s (Or.inl ⟨a, rfl⟩), ψ.codRestrict L.toSubalgebra fun a => IntermediateField.subset_adjoin K s (Or.inr ⟨a, rfl⟩), ?_, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `a`. Both sides reduce to the same expression. Use extensionality with `a`. Both sides reduce to the same expression.

Conclude with `j.toRingHom.injective`.
-/
theorem exists_common_field {K : Type} [Field K] [Countable K] (σ : K →+* ℂ) {A B k : Type} [CommRing A] [Algebra K A]
    [CommRing B] [Algebra K B] [Countable A] [Countable B] [Field k] [Algebra K k]
    (φ : A →ₐ[K] k) (ψ : B →ₐ[K] k) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (ι : L →ₐ[K] k) (j : L →ₐ[K] CAt σ) (φL : A →ₐ[K] L)
      (ψL : B →ₐ[K] L), ι.comp φL = φ ∧ ι.comp ψL = ψ ∧ Function.Injective j := by
  let s : Set k := Set.range φ ∪ Set.range ψ
  have hs : s.Countable := (Set.countable_range _).union (Set.countable_range _)
  let L := IntermediateField.adjoin K s
  have hL : Countable L := by
    have := hs.to_subtype
    rw [← Cardinal.mk_le_aleph0_iff]
    refine (IntermediateField.cardinalMk_adjoin_le K s).trans ?_
    simp
  letI : Algebra K ℂ := σ.toAlgebra
  obtain ⟨j⟩ := GlobalTheory.nonempty_algHom_complex_of_countable K L
  refine ⟨L, inferInstance, inferInstance, L.val, j,
    φ.codRestrict L.toSubalgebra fun a => IntermediateField.subset_adjoin K s (Or.inl ⟨a, rfl⟩),
    ψ.codRestrict L.toSubalgebra fun a => IntermediateField.subset_adjoin K s (Or.inr ⟨a, rfl⟩), ?_, ?_, ?_⟩
  · ext a; rfl
  · ext a; rfl
  · exact j.toRingHom.injective

/- English proof (translation)
Establish `hT : FromTest pts mapR z` using `⟨p, φ, y, hz⟩`. Unfold `evalAt`. Rewrite using `[dif_pos hT]`. Conclude with `(hW f hf S p _ φ _ y _ z hz hT.choose_spec.choose_spec.choose_spec).symm`.
-/
theorem evalAt_of_mapR {K : Type} [Field K]
    (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
    (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
      (S →ₐ[K] T) → pts S → pts T → Prop)
    (hW : EvalWD pts mapR) (f : Rules pts) (hf : IsNatural pts mapR f)
    {S : Type} [CommRing S] [Algebra K S] (p : TRing K) (φ : p.R →ₐ[K] S) (y : pts p.R) (z : pts S)
    (hz : mapR φ y z) : evalAt pts mapR f z = φ (f p y) := by
  have hT : FromTest pts mapR z := ⟨p, φ, y, hz⟩
  unfold evalAt
  rw [dif_pos hT]
  exact (hW f hf S p _ φ _ y _ z hz hT.choose_spec.choose_spec.choose_spec).symm

end ComplexTransfer

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c k _ _ y y'`. Establish `hS : Out.SecBaseChangeSt` using `GlobalTheory.firstFiveLaws.1.secBaseChange`. Establish `hW : EvalWD (K` using `c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) := evalWD_fr (frChartF_of (GlobalTheory.Frames.chartCoverF_of_secBaseChange hS E H Dw l Xo c))`. Establish `hA : AllTest Xo c` using `GlobalTheory.Frames.allTest_of_secBaseChange hS E H Dw l Xo c`. Take `⟨p, φ, y₀, hy⟩` from `hA k y`.

Take `⟨q, ψ, y₁, hy'⟩` from `hA k y'`. Use `haveI := c.fin`. Use `haveI : Countable c.F := ComplexTransfer.countable_of_finiteType ℚ c.F`. Use `haveI : Countable p.R := ComplexTransfer.countable_of_finiteType c.F p.R`. Use `haveI : Countable q.R := ComplexTransfer.countable_of_finiteType c.F q.R`.

Take `⟨L, _, _, ι, j, φL, ψL, hφ, hψ, hj⟩` from `ComplexTransfer.exists_common_field c.F.val.toRingHom φ ψ`. Take `⟨z, hz⟩` from `GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c _ _ (j.comp φL) y₀`. Take `⟨z', hz'⟩` from `GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c _ _ (j.comp ψL) y₁`. Establish `hι : Function.Injective ι` using `ι.toRingHom.injective`. Establish `ev : ∀ f ∈ sec Xo c 0 0, evR Xo c f y = ι (φL (f p y₀)) ∧ evR Xo c f y' = ι (ψL (f q y₁)) ∧ evR Xo c f z = j (φL (f p y₀)) ∧ evR Xo c f z' = j (ψL (f q y₁))`.

Introduce `f hf`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← AlgHom.comp_apply, hφ]`. Conclude with `ComplexTransfer.evalAt_of_mapR _ _ hW f hf.1 p φ y₀ y hy`. Rewrite using `[← AlgHom.comp_apply, hψ]`.

Conclude with `ComplexTransfer.evalAt_of_mapR _ _ hW f hf.1 q ψ y₁ y' hy'`. Conclude with `ComplexTransfer.evalAt_of_mapR _ _ hW f hf.1 p _ y₀ z hz`. Conclude with `ComplexTransfer.evalAt_of_mapR _ _ hW f hf.1 q _ y₁ z' hz'`. Use `⟨z, z', ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `ρ h`.

Establish `e1 : y.x = spMap ι.toRingHom ≫ spMap φL.toRingHom ≫ y₀.x`. Rewrite using `[← Category.assoc, ← Geo.Tor.spMap_comp, hy.1, ← hφ]`. Both sides reduce to the same expression. Establish `e2 : y'.x = spMap ι.toRingHom ≫ spMap ψL.toRingHom ≫ y₁.x`. Rewrite using `[← Category.assoc, ← Geo.Tor.spMap_comp, hy'.1, ← hψ]`.

Both sides reduce to the same expression. Establish `e3 : z.x = spMap j.toRingHom ≫ spMap φL.toRingHom ≫ y₀.x`. Rewrite using `[← Category.assoc, ← Geo.Tor.spMap_comp, hz.1]`. Both sides reduce to the same expression. Establish `e4 : z'.x = spMap j.toRingHom ≫ spMap ψL.toRingHom ≫ y₁.x`.

Rewrite using `[← Category.assoc, ← Geo.Tor.spMap_comp, hz'.1]`. Both sides reduce to the same expression. Use `haveI := ComplexTransfer.epi_spMap_field ι.toRingHom`. Rewrite `h` using `[e1, e2, Category.assoc, cancel_epi]`. Rewrite using `[e3, e4, h]`.

Simplify using `only [Category.assoc]`. Introduce `f hf h`. Take `⟨h1, -, h3, -⟩` from `ev f hf`. Rewrite `h` using `[h1, map_eq_zero_iff ι hι]`. Rewrite using `[h3, h, map_zero]`.

Introduce `f hf a h`. Take `⟨h1, h2, h3, h4⟩` from `ev f hf`. Rewrite `h` using `[h3, h4, ← j.commutes, ← map_mul]`. Rewrite using `[h1, h2, hj h, map_mul, ι.commutes]`.
-/
theorem exists_complex_framed_pair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (k : Type) [Field k] [Algebra c.F k] (y y' : FrPt Xo c k), ∃ z z' : FrPt Xo c (CAt c.F.val.toRingHom), (∀ ρ : Xo.X ⟶ Xo.X, y'.x = y.x ≫ ρ → z'.x = z.x ≫ ρ) ∧ (∀ f ∈ sec Xo c 0 0, evR Xo c f y = 0 → evR Xo c f z = 0) ∧ ∀ f ∈ sec Xo c 0 0, ∀ a : c.F, evR Xo c f z' = algebraMap c.F (CAt c.F.val.toRingHom) a * evR Xo c f z → evR Xo c f y' = algebraMap c.F k a * evR Xo c f y := by
  intro E _ _ _ H Dw l Xo c k _ _ y y'
  have hS : Out.SecBaseChangeSt := GlobalTheory.firstFiveLaws.1.secBaseChange
  have hW : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) :=
    evalWD_fr (frChartF_of (GlobalTheory.Frames.chartCoverF_of_secBaseChange hS E H Dw l Xo c))
  have hA : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange hS E H Dw l Xo c
  obtain ⟨p, φ, y₀, hy⟩ := hA k y
  obtain ⟨q, ψ, y₁, hy'⟩ := hA k y'
  haveI := c.fin
  haveI : Countable c.F := ComplexTransfer.countable_of_finiteType ℚ c.F
  haveI : Countable p.R := ComplexTransfer.countable_of_finiteType c.F p.R
  haveI : Countable q.R := ComplexTransfer.countable_of_finiteType c.F q.R
  obtain ⟨L, _, _, ι, j, φL, ψL, hφ, hψ, hj⟩ :=
    ComplexTransfer.exists_common_field c.F.val.toRingHom φ ψ
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c _ _ (j.comp φL) y₀
  obtain ⟨z', hz'⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c _ _ (j.comp ψL) y₁
  have hι : Function.Injective ι := ι.toRingHom.injective
  have ev : ∀ f ∈ sec Xo c 0 0, evR Xo c f y = ι (φL (f p y₀)) ∧ evR Xo c f y' = ι (ψL (f q y₁)) ∧
      evR Xo c f z = j (φL (f p y₀)) ∧ evR Xo c f z' = j (ψL (f q y₁)) := by
    intro f hf
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← AlgHom.comp_apply, hφ]
      exact ComplexTransfer.evalAt_of_mapR _ _ hW f hf.1 p φ y₀ y hy
    · rw [← AlgHom.comp_apply, hψ]
      exact ComplexTransfer.evalAt_of_mapR _ _ hW f hf.1 q ψ y₁ y' hy'
    · exact ComplexTransfer.evalAt_of_mapR _ _ hW f hf.1 p _ y₀ z hz
    · exact ComplexTransfer.evalAt_of_mapR _ _ hW f hf.1 q _ y₁ z' hz'
  refine ⟨z, z', ?_, ?_, ?_⟩
  · intro ρ h
    have e1 : y.x = spMap ι.toRingHom ≫ spMap φL.toRingHom ≫ y₀.x := by
      rw [← Category.assoc, ← Geo.Tor.spMap_comp, hy.1, ← hφ]; rfl
    have e2 : y'.x = spMap ι.toRingHom ≫ spMap ψL.toRingHom ≫ y₁.x := by
      rw [← Category.assoc, ← Geo.Tor.spMap_comp, hy'.1, ← hψ]; rfl
    have e3 : z.x = spMap j.toRingHom ≫ spMap φL.toRingHom ≫ y₀.x := by
      rw [← Category.assoc, ← Geo.Tor.spMap_comp, hz.1]; rfl
    have e4 : z'.x = spMap j.toRingHom ≫ spMap ψL.toRingHom ≫ y₁.x := by
      rw [← Category.assoc, ← Geo.Tor.spMap_comp, hz'.1]; rfl
    haveI := ComplexTransfer.epi_spMap_field ι.toRingHom
    rw [e1, e2, Category.assoc, cancel_epi] at h
    rw [e3, e4, h]
    simp only [Category.assoc]
  · intro f hf h
    obtain ⟨h1, -, h3, -⟩ := ev f hf
    rw [h1, map_eq_zero_iff ι hι] at h
    rw [h3, h, map_zero]
  · intro f hf a h
    obtain ⟨h1, h2, h3, h4⟩ := ev f hf
    rw [h3, h4, ← j.commutes, ← map_mul] at h
    rw [h1, h2, hj h, map_mul, ι.commutes]

end GlobalTheory.Frames
