import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueModelHasJacobianOrder

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.Ord
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GlobalTheory.SS.Ord

/- English proof (translation)
Use `M.smooth` as an intermediate fact. Use `choose n W hW hd using H1.exists_dim M.Y.hom`. Establish `: IsZariskiLocalAtSource (@SmoothOfRelativeDimension d)` using `HasRingHomProperty.instIsZariskiLocalAtSource`. Use `IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension d) W (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hW x⟩) fun x => ?_` and prove the remaining obligations. Establish `hne : ∃ y : A.left, M.j y ∈ W x`.

Assume the negation of the conclusion as `hc`. Establish `e : M.j ⁻¹ᵁ W x = ⊥` using `le_bot_iff.1 fun y hy => (hc ⟨y, hy⟩).elim`. Establish `h1 : Subsingleton Γ(A.left, M.j ⁻¹ᵁ W x)` using `by rw [e]; infer_instance`. Establish `h2 : Subsingleton Γ(M.Y.left, W x)` using `(j_app_injective M (W x)).subsingleton`. Establish `: Nonempty (W x)` using `⟨⟨x, hW x⟩⟩`.

Conclude with `not_subsingleton _ h2`. Take `⟨y, hy⟩` from `hne`. Rewrite using `[← H1.dim_base (isPullback_j M) (hd x) hA y hy]`. Conclude with `hd x`.
-/
theorem model_smoothOfRelativeDimension {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {A : Over (Sp K)} {d : ℕ} (hA : SmoothOfRelativeDimension d A.hom) (M : Model R A) :
    SmoothOfRelativeDimension d M.Y.hom := by
  have := M.smooth
  choose n W hW hd using H1.exists_dim M.Y.hom
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension d) := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension d) W
    (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hW x⟩) fun x => ?_
  have hne : ∃ y : A.left, M.j y ∈ W x := by
    by_contra hc
    have e : M.j ⁻¹ᵁ W x = ⊥ := le_bot_iff.1 fun y hy => (hc ⟨y, hy⟩).elim
    have h1 : Subsingleton Γ(A.left, M.j ⁻¹ᵁ W x) := by rw [e]; infer_instance
    have h2 : Subsingleton Γ(M.Y.left, W x) := (j_app_injective M (W x)).subsingleton
    have : Nonempty (W x) := ⟨⟨x, hW x⟩⟩
    exact not_subsingleton _ h2
  obtain ⟨y, hy⟩ := hne
  rw [← H1.dim_base (isPullback_j M) (hd x) hA y hy]
  exact hd x

/- English proof (translation)
Introduce `R K _ _ _ _ _ _ A I _ hA M x O hx`. Establish `hM` using `model_smoothOfRelativeDimension hA M`. Take `⟨_, ⟨W, hW, rfl⟩, hxW, hWO⟩` from `M.Y.left.isBasis_affineOpens.exists_subset_of_mem_open hx O.isOpen`. Establish `hW : IsAffineOpen W` using `hW`. Establish `h0` using `HasRingHomProperty.appLE (@SmoothOfRelativeDimension (Fintype.card I)) M.Y.hom hM ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top`.

Take `⟨s, hs, h'⟩` from `(RingHom.locally_iff_isLocalization RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h0`. Establish `hcov` using `hW.self_le_iSup_basicOpen_iff.2 hs hxW`. Take `⟨⟨g, hg⟩, hxg⟩` from `TopologicalSpace.Opens.mem_iSup.1 hcov`. Establish `hl` using `hW.isLocalization_basicOpen g`. Establish `h1` using `h' g hg Γ(M.Y.left, M.Y.left.basicOpen g)`.

Establish `h2 : (cst M (M.Y.left.basicOpen g)).IsStandardSmoothOfRelativeDimension (Fintype.card I)`. Establish `h3` using `RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _ (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv h1`. Establish `e : cst M (M.Y.left.basicOpen g) = (rs _ (M.Y.left.basicOpen_le g)).comp (cst M W)` using `RingHom.ext fun r => (rs_cst M (M.Y.left.basicOpen_le g) r).symm`. Rewrite using `[e]`. Conclude with `h3`.

Take `⟨φ, hC, hφ⟩` from `h2.exists_etale_mvPolynomial`. Set `e` to `Fintype.equivFin I`. Use `⟨M.Y.left.basicOpen g, fun i => φ (MvPolynomial.X (e i)), hW.basicOpen g, hxg, (M.Y.left.basicOpen_le g).trans hWO, ?_⟩` and prove the remaining obligations. Establish `h4` using `RingHom.Etale.respectsIso.2 φ (MvPolynomial.renameEquiv R e).toRingEquiv hφ`. Use `h4 using 1` and compare the differences between its conclusion and the goal.

Use `MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)` and prove the remaining obligations. Simplify using `[← hC]`. Simplify using the standard rewrite rules.
-/
theorem exists_etale_coord : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)) (I : Type) [Fintype I], SmoothOfRelativeDimension (Fintype.card I) A.hom → ∀ (M : Model R A) (x : M.Y.left) (O : M.Y.left.Opens), x ∈ O → ∃ (U : M.Y.left.Opens) (t : I → Γ(M.Y.left, U)), IsAffineOpen U ∧ x ∈ U ∧ U ≤ O ∧ (MvPolynomial.eval₂Hom (cst M U) t).Etale := by
  intro R K _ _ _ _ _ _ A I _ hA M x O hx
  have hM := model_smoothOfRelativeDimension hA M
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWO⟩ := M.Y.left.isBasis_affineOpens.exists_subset_of_mem_open hx O.isOpen
  have hW : IsAffineOpen W := hW
  have h0 := HasRingHomProperty.appLE (@SmoothOfRelativeDimension (Fintype.card I)) M.Y.hom hM
    ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top
  obtain ⟨s, hs, h'⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h0
  have hcov := hW.self_le_iSup_basicOpen_iff.2 hs hxW
  obtain ⟨⟨g, hg⟩, hxg⟩ := TopologicalSpace.Opens.mem_iSup.1 hcov
  have hl := hW.isLocalization_basicOpen g
  have h1 := h' g hg Γ(M.Y.left, M.Y.left.basicOpen g)
  have h2 : (cst M (M.Y.left.basicOpen g)).IsStandardSmoothOfRelativeDimension (Fintype.card I) := by
    have h3 := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
      (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv h1
    have e : cst M (M.Y.left.basicOpen g) = (rs _ (M.Y.left.basicOpen_le g)).comp (cst M W) :=
      RingHom.ext fun r => (rs_cst M (M.Y.left.basicOpen_le g) r).symm
    rw [e]
    exact h3
  obtain ⟨φ, hC, hφ⟩ := h2.exists_etale_mvPolynomial
  let e := Fintype.equivFin I
  refine ⟨M.Y.left.basicOpen g, fun i => φ (MvPolynomial.X (e i)), hW.basicOpen g, hxg,
    (M.Y.left.basicOpen_le g).trans hWO, ?_⟩
  have h4 := RingHom.Etale.respectsIso.2 φ (MvPolynomial.renameEquiv R e).toRingEquiv hφ
  convert h4 using 1
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · simp [← hC]
  · simp

end GlobalTheory.SS.Ord
end
