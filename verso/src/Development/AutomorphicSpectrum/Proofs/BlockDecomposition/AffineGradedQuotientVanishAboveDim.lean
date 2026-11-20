import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Precomp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFiltrationViaTruncation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StableCoverCechVanishingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSmoothCoordinateCover
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinatesRestrictAffineOpenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGradedVanishing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolynomialTransfer
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.GrTop

variable {X : Scheme.{0}}

/- English proof (translation)
Proceed by induction on `hS using Finset.Nonempty.cons_induction with`. Consider the case `singleton a => simp`. Consider the case `cons a s ha hs ih`. Rewrite using `[Finset.cons_eq_insert, Finset.iInf_insert, Finset.prod_insert (by simpa using ha), Scheme.basicOpen_mul, ih]`.
-/
theorem iInf_basicOpen {V : X.Opens} {ι : Type} (f : ι → Γ(X, V)) (S : Finset ι) (hS : S.Nonempty) :
    (⨅ α ∈ S, X.basicOpen (f α)) = X.basicOpen (∏ α ∈ S, f α) := by
  classical
  induction hS using Finset.Nonempty.cons_induction with
  | singleton a => simp
  | cons a s ha hs ih =>
    rw [Finset.cons_eq_insert, Finset.iInf_insert, Finset.prod_insert (by simpa using ha), Scheme.basicOpen_mul, ih]

/- English proof (translation)
Establish `h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension d) (q.appLE ⊤ V le_top).hom` using `HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension d) q inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top`. Establish `key : ∀ x : V, ∃ f : Γ(X, V), (x : X) ∈ X.basicOpen f ∧ Nonempty (Coord q (X.basicOpen f) d)`. Introduce `x`. Take `⟨f, hf, hst⟩` from `GlobalTheory.CompanionTheory.CovEx.exists_basicOpen (RingHom.IsStandardSmoothOfRelativeDimension d) RingHom.isStandardSmoothOfRelativeDimension_respectsIso q hV h x.2`. Take `⟨g, hg, he⟩` from `hst.exists_etale_mvPolynomial`.

Conclude with `⟨f, hf, GlobalTheory.CompanionTheory.CovEx.coord_basicOpen q hV f g hg he⟩`. Use `choose f hf hc using key`. Take `⟨t, ht⟩` from `hV.isCompact.elim_finite_subcover (fun x : V => (X.basicOpen (f x) : Set X)) (fun x => (X.basicOpen (f x)).2) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hf _⟩)`. Use `⟨t, inferInstance, fun a => f a.1, le_antisymm (iSup_le fun a => X.basicOpen_le _) ?_, fun a => hc a.1⟩` and prove the remaining obligations. Introduce `x hx`.

Take `⟨y, hy⟩` from `Set.mem_iUnion.1 (ht hx)`. Take `⟨hy, hxy⟩` from `Set.mem_iUnion.1 hy`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hy⟩, hxy⟩`.
-/
theorem exists_cover {O : Type} [CommRing O] (q : X ⟶ Spec (CommRingCat.of O)) (d : ℕ) [SmoothOfRelativeDimension d q]
    {V : X.Opens} (hV : IsAffineOpen V) :
    ∃ (ι : Type) (_ : Fintype ι) (f : ι → Γ(X, V)), (⨆ α, X.basicOpen (f α)) = V ∧
      ∀ α, Nonempty (Coord q (X.basicOpen (f α)) d) := by
  classical
  have h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension d) (q.appLE ⊤ V le_top).hom :=
    HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension d) q inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  have key : ∀ x : V, ∃ f : Γ(X, V), (x : X) ∈ X.basicOpen f ∧ Nonempty (Coord q (X.basicOpen f) d) := by
    intro x
    obtain ⟨f, hf, hst⟩ := GlobalTheory.CompanionTheory.CovEx.exists_basicOpen (RingHom.IsStandardSmoothOfRelativeDimension d)
      RingHom.isStandardSmoothOfRelativeDimension_respectsIso q hV h x.2
    obtain ⟨g, hg, he⟩ := hst.exists_etale_mvPolynomial
    exact ⟨f, hf, GlobalTheory.CompanionTheory.CovEx.coord_basicOpen q hV f g hg he⟩
  choose f hf hc using key
  obtain ⟨t, ht⟩ := hV.isCompact.elim_finite_subcover (fun x : V => (X.basicOpen (f x) : Set X))
    (fun x => (X.basicOpen (f x)).2) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hf _⟩)
  refine ⟨t, inferInstance, fun a => f a.1, le_antisymm (iSup_le fun a => X.basicOpen_le _) ?_, fun a => hc a.1⟩
  intro x hx
  obtain ⟨y, hy⟩ := Set.mem_iUnion.1 (ht hx)
  obtain ⟨hy, hxy⟩ := Set.mem_iUnion.1 hy
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hy⟩, hxy⟩

end GlobalTheory.CompanionTheory.GrTop

namespace GlobalTheory.CompanionTheory.GrTop

/- English proof (translation)
Establish `hz : ∀ (T : (KS q s {V}).FullSubcategory) (x : (sq (sFil (KS q s {V}) (r : ℤ)) (sFil (KS q s {V}) ((r : ℤ) + 1))).obj T), x = 0`. Introduce `T x`. Take `⟨x, hx⟩` from `x`. Take `⟨y, hy, rfl⟩` from `(Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx`. Establish `hy2 : (show T.obj.B from y) ∈ T.obj.pdPow ((r : ℤ).toNat)` using `hy`.

Rewrite `hy2` using `[Int.toNat_natCast]`. Establish `hy' : (show T.obj.B from y) ∈ T.obj.pdPow s` using `T.obj.pdPow_anti hsr hy2`. Rewrite `hy'` using `[T.property.1.1, Ideal.mem_bot]`. Substitute `hy'` using the available equality. Both sides reduce to the same expression.

Use `⟨fun a b => ?_⟩` and prove the remaining obligations. Take `⟨z, hz1, rfl⟩` from `(CrystallineSemistableComparison.P.cls_surj _ j).1 a`. Take `⟨z', hz1', rfl⟩` from `(CrystallineSemistableComparison.P.cls_surj _ j).1 b`. Establish `e : z = z'` using `funext fun σ => (hz _ _).trans (hz _ _).symm`. Substitute `e` using the available equality.

Both sides reduce to the same expression.
-/
theorem twoVariableSeriesVanishesBelowDegree_one_shiftVariable {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (s r j : ℕ)
    (hsr : s ≤ r) : Subsingleton (HQ (KS q s {V}) (r : ℤ) ((r : ℤ) + 1) j) := by
  have hz : ∀ (T : (KS q s {V}).FullSubcategory)
      (x : (sq (sFil (KS q s {V}) (r : ℤ)) (sFil (KS q s {V}) ((r : ℤ) + 1))).obj T), x = 0 := by
    intro T x
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
    have hy2 : (show T.obj.B from y) ∈ T.obj.pdPow ((r : ℤ).toNat) := hy
    rw [Int.toNat_natCast] at hy2
    have hy' : (show T.obj.B from y) ∈ T.obj.pdPow s := T.obj.pdPow_anti hsr hy2
    rw [T.property.1.1, Ideal.mem_bot] at hy'
    subst hy'
    rfl
  refine ⟨fun a b => ?_⟩
  obtain ⟨z, hz1, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ j).1 a
  obtain ⟨z', hz1', rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ j).1 b
  have e : z = z' := funext fun σ => (hz _ _).trans (hz _ _).symm
  subst e
  rfl

end GlobalTheory.CompanionTheory.GrTop

namespace GlobalTheory.CompanionTheory.GrTop

/- English proof (translation)
Introduce `K _ _ X q d _ V hV s r j hr`. Use `lift r to ℕ using (by omega)`. Establish `hdr : d < r` using `by exact_mod_cast hr`. Break down `le_or_gt s r with hsr | hsr` into its components or cases. Conclude with `twoVariableSeriesVanishesBelowDegree_one_shiftVariable q V s r j hsr`.

Take `⟨ι, _, f, hcov, hc⟩` from `exists_cover q d hV`. Set `U : ι → X.Opens` to `fun α => X.basicOpen (f α)`. Establish `hloc : ∀ S : Finset ι, S.Nonempty → ∀ j, Subsingleton (HU (sq (thFil (smFun X q) (r : ℤ)) (thFil (smFun X q) ((r : ℤ) + 1))) (St (TF 1 s) {⨅ α ∈ S, U α}) j)`. Introduce `S hS j`. Take `⟨α, hα⟩` from `id hS`.

Establish `haff : IsAffineOpen (⨅ α ∈ S, U α)`. Express the relevant statement in the definitionally equal form `IsAffineOpen (⨅ α ∈ S, X.basicOpen (f α))`. Rewrite using `[iInf_basicOpen f S hS]`. Conclude with `hV.basicOpen _`. Take `⟨c', -⟩` from `GlobalTheory.T.coordinates_restrict_affine_open (hc α).some (iInf₂_le α hα) haff`.

Conclude with `GlobalTheory.CompanionTheory.KIso.loc_vanish q hG hP c' r s hdr (by omega) j`. Establish `hglob` using `(GlobalTheory.T.stable_cover_cech_vanishing.1 (sq (thFil (smFun X q) (r : ℤ)) (thFil (smFun X q) ((r : ℤ) + 1))) (TF 1 s) U 0).2.1 hloc j`. Establish `h2 : KS q s (Set.range U) ≤ KS q s {V}`. Introduce and unpack `T ⟨hT, W, ⟨α, rfl⟩, hW⟩`. Conclude with `⟨hT, V, rfl, fun x hx => X.basicOpen_le (f α) (hW hx)⟩`.

Establish `hc' : ∀ W ∈ ({V} : Set X.Opens), W ≤ sSup (Set.range U)`. Introduce `W hW`. Rewrite using `[Set.mem_singleton_iff.1 hW, sSup_range]`. Conclude with `hcov.ge`. Establish `b` using `(GlobalTheory.T.cech_refinement_cohomology_bijective (TF 1 s : ObjectProperty (Thick (smFun X q))) (Or.inl ⟨rfl, 1, s, rfl⟩) (Set.range U) {V} h2 hc' j).1 (r : ℤ) ((r : ℤ) + 1)`.

Establish `: Subsingleton (HQ (KS q s (Set.range U)) (r : ℤ) ((r : ℤ) + 1) j)` using `hglob`. Conclude with `⟨fun a c => b.1 (@Subsingleton.elim _ this _ _)⟩`.
-/
theorem grTop (hG : KH.LocGr) (hP : KH.PolyTf) : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of K)) (d : ℕ) [SmoothOfRelativeDimension d q] (V : X.Opens), IsAffineOpen V →
    ∀ (s : ℕ) (r : ℤ) (j : ℕ), (d : ℤ) < r → Subsingleton (HQ (KS q s {V}) r (r + 1) j) := by
  intro K _ _ X q d _ V hV s r j hr
  lift r to ℕ using (by omega)
  have hdr : d < r := by exact_mod_cast hr
  rcases le_or_gt s r with hsr | hsr
  · exact twoVariableSeriesVanishesBelowDegree_one_shiftVariable q V s r j hsr
  obtain ⟨ι, _, f, hcov, hc⟩ := exists_cover q d hV
  let U : ι → X.Opens := fun α => X.basicOpen (f α)
  have hloc : ∀ S : Finset ι, S.Nonempty → ∀ j, Subsingleton (HU (sq (thFil (smFun X q) (r : ℤ))
      (thFil (smFun X q) ((r : ℤ) + 1))) (St (TF 1 s) {⨅ α ∈ S, U α}) j) := by
    intro S hS j
    obtain ⟨α, hα⟩ := id hS
    have haff : IsAffineOpen (⨅ α ∈ S, U α) := by
      change IsAffineOpen (⨅ α ∈ S, X.basicOpen (f α))
      rw [iInf_basicOpen f S hS]
      exact hV.basicOpen _
    obtain ⟨c', -⟩ := GlobalTheory.T.coordinates_restrict_affine_open (hc α).some (iInf₂_le α hα) haff
    exact GlobalTheory.CompanionTheory.KIso.loc_vanish q hG hP c' r s hdr (by omega) j
  have hglob := (GlobalTheory.T.stable_cover_cech_vanishing.1 (sq (thFil (smFun X q) (r : ℤ)) (thFil (smFun X q) ((r : ℤ) + 1))) (TF 1 s) U 0).2.1
    hloc j
  have h2 : KS q s (Set.range U) ≤ KS q s {V} := by
    rintro T ⟨hT, W, ⟨α, rfl⟩, hW⟩
    exact ⟨hT, V, rfl, fun x hx => X.basicOpen_le (f α) (hW hx)⟩
  have hc' : ∀ W ∈ ({V} : Set X.Opens), W ≤ sSup (Set.range U) := by
    intro W hW
    rw [Set.mem_singleton_iff.1 hW, sSup_range]
    exact hcov.ge
  have b := (GlobalTheory.T.cech_refinement_cohomology_bijective (TF 1 s : ObjectProperty (Thick (smFun X q))) (Or.inl ⟨rfl, 1, s, rfl⟩) (Set.range U) {V} h2 hc' j).1 (r : ℤ) ((r : ℤ) + 1)
  have : Subsingleton (HQ (KS q s (Set.range U)) (r : ℤ) ((r : ℤ) + 1) j) := hglob
  exact ⟨fun a c => b.1 (@Subsingleton.elim _ this _ _)⟩

end GlobalTheory.CompanionTheory.GrTop

namespace GlobalTheory.CompanionTheory.GrTop

/- English proof (translation)
The claim follows from `@grTop GlobalTheory.CompanionTheory.LocGrStep.loc_gr GlobalTheory.CompanionTheory.PolyTfCon.polyTf`.
-/
theorem grTop_main : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (d : ℕ)
    [SmoothOfRelativeDimension d q] (V : X.Opens), IsAffineOpen V → ∀ (s : ℕ) (r : ℤ) (j : ℕ), (d : ℤ) < r →
    Subsingleton (HQ (KS q s {V}) r (r + 1) j) :=
  @grTop GlobalTheory.CompanionTheory.LocGrStep.loc_gr GlobalTheory.CompanionTheory.PolyTfCon.polyTf

end GlobalTheory.CompanionTheory.GrTop
