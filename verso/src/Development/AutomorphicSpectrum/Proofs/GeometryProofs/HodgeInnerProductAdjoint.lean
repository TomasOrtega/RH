import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeHermitianFormExistsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqZeroOfSumEmbeddingSmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.StalkUnitsSymmGm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeAdj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.CompanionTheory.Ar
open Filter Topology Matrix
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.TangentOrigin

section Unif

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

/- English proof (translation)
Unfold `IsTangent`. Establish `e : (1 : epsR ℂ ⟶ A).left = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ η[A].left`. Rewrite using `[Hom.one_def, Over.comp_left]`. Use `congr 1`. Rewrite using `[e, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`.

Establish `: (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ`. Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
theorem isTangent_one' : IsTangent (1 : epsR ℂ ⟶ A) := by
  unfold IsTangent
  have e : (1 : epsR ℂ ⟶ A).left = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ η[A].left := by
    rw [Hom.one_def, Over.comp_left]
    congr 1
  rw [e, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ := by
    ext x
    simp
  rw [this]
  simp

/- English proof (translation)
Establish `hv : IsTangent (1 : epsR ℂ ⟶ A)` using `isTangent_one'`. Establish `hvU` using `(tangent_mem_iff (u := u) hv U).2 h0`. Use `(isDiff_iff hv hU hvU h0 w).2 ?_` and prove the remaining obligations. Rewrite using `[(isDiff_iff hv hU hvU h0 0).1 (GlobalTheory.UnifDifferential.isDiff_one u)]`. Use `RingHom.ext fun s => TrivSqZeroExt.ext rfl ?_` and prove the remaining obligations.

Rewrite using `[jet_snd, jet_snd, map_zero]`. Conclude with `(hw s).symm`.
-/
theorem isDiff_one_of_fderiv (u : HolUnif A L g) {U : A.left.Opens} (hU : IsAffineOpen U)
    (h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U) {w : Fin g → ℂ}
    (hw : ∀ s : Γ(A.left, U), fderiv ℂ (fun z => valAt' (u.ex z).left U s) 0 w = 0) :
    u.IsDiff w (1 : epsR ℂ ⟶ A) := by
  have hv : IsTangent (1 : epsR ℂ ⟶ A) := isTangent_one'
  have hvU := (tangent_mem_iff (u := u) hv U).2 h0
  refine (isDiff_iff hv hU hvU h0 w).2 ?_
  rw [(isDiff_iff hv hU hvU h0 0).1 (GlobalTheory.UnifDifferential.isDiff_one u)]
  refine RingHom.ext fun s => TrivSqZeroExt.ext rfl ?_
  rw [jet_snd, jet_snd, map_zero]
  exact (hw s).symm

def transl (u : HolUnif A L g) (z : Fin g → ℂ) : A ⟶ A := (toUnit A ≫ u.ex z) * 𝟙 A

/- English proof (translation)
Rewrite using `[transl, MonObj.comp_mul, u.ex_add, Category.comp_id, ← Category.assoc, toUnit_unique (u.ex y ≫ toUnit A) (𝟙 _), Category.id_comp]`.
-/
theorem ex_comp_transl (u : HolUnif A L g) (z y : Fin g → ℂ) : u.ex y ≫ transl u z = u.ex (z + y) := by
  rw [transl, MonObj.comp_mul, u.ex_add, Category.comp_id, ← Category.assoc, toUnit_unique (u.ex y ≫ toUnit A) (𝟙 _),
    Category.id_comp]

/- English proof (translation)
Establish `hv : IsTangent (1 : epsR ℂ ⟶ A)` using `isTangent_one'`. Use `set T := transl u z with hT`. Establish `h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ (T.left ⁻¹ᵁ W)`. Establish `e : (u.ex 0 ≫ T).left = (u.ex z).left` using `by rw [hT, ex_comp_transl, add_zero]`. Introduce `p hp`.

Use `hz hp` as an intermediate fact. Rewrite `this` using `[← e]`. Conclude with `this`. Establish `hvU` using `(tangent_mem_iff (u := u) hv _).2 h0`. Establish `e1` using `h _ hvU ((T.left.app W).hom s)`.

Establish `e2` using `GlobalTheory.UnifDifferential.isDiff_one u _ hvU ((T.left.app W).hom s)`. Establish `e3 : fderiv ℂ (fun y => valAt' (u.ex y).left (T.left ⁻¹ᵁ W) ((T.left.app W).hom s)) 0 w = 0`. Rewrite using `[← e1, e2, map_zero]`. Establish `e4 : (fun y => valAt' (u.ex y).left (T.left ⁻¹ᵁ W) ((T.left.app W).hom s)) = fun y => valAt' (u.ex (z + y)).left W s`. Use function extensionality and compare the values at `y`.

Rewrite using `[← GlobalTheory.HomLinear.valAt'_comp_left, hT, ex_comp_transl]`. Rewrite `e3` using `[e4, fderiv_comp_add_left (f := fun y => valAt' (u.ex y).left W s), add_zero]`. Conclude with `e3`.
-/
theorem fderiv_eq_zero_of_isDiff_one (u : HolUnif A L g) {w : Fin g → ℂ} (h : u.IsDiff w (1 : epsR ℂ ⟶ A))
    (z : Fin g → ℂ) {W : A.left.Opens} (hz : ⊤ ≤ (u.ex z).left ⁻¹ᵁ W) (s : Γ(A.left, W)) :
    fderiv ℂ (fun y => valAt' (u.ex y).left W s) z w = 0 := by
  have hv : IsTangent (1 : epsR ℂ ⟶ A) := isTangent_one'
  set T := transl u z with hT
  have h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ (T.left ⁻¹ᵁ W) := by
    have e : (u.ex 0 ≫ T).left = (u.ex z).left := by rw [hT, ex_comp_transl, add_zero]
    intro p hp
    have := hz hp
    rw [← e] at this
    exact this
  have hvU := (tangent_mem_iff (u := u) hv _).2 h0
  have e1 := h _ hvU ((T.left.app W).hom s)
  have e2 := GlobalTheory.UnifDifferential.isDiff_one u _ hvU ((T.left.app W).hom s)
  have e3 : fderiv ℂ (fun y => valAt' (u.ex y).left (T.left ⁻¹ᵁ W) ((T.left.app W).hom s)) 0 w = 0 := by
    rw [← e1, e2, map_zero]
  have e4 : (fun y => valAt' (u.ex y).left (T.left ⁻¹ᵁ W) ((T.left.app W).hom s)) =
      fun y => valAt' (u.ex (z + y)).left W s := by
    funext y
    rw [← GlobalTheory.HomLinear.valAt'_comp_left, hT, ex_comp_transl]
  rw [e4, fderiv_comp_add_left (f := fun y => valAt' (u.ex y).left W s), add_zero] at e3
  exact e3

/- English proof (translation)
Set `pt : (𝟙_ (Over (Sp ℂ))).left` to `(default : PrimeSpectrum ℂ)`. Establish `hsub : ∀ q : (𝟙_ (Over (Sp ℂ))).left, q = pt` using `fun q => Subsingleton.elim (α := PrimeSpectrum ℂ) q pt`. Take `⟨U, hU, hpU, -⟩` from `exists_isAffineOpen_mem_and_subset (x := (u.ex 0).left pt) (U := ⊤) (Set.mem_univ _)`. Establish `h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U`. Introduce `q _`.

Rewrite using `[hsub q]`. Conclude with `hpU`. Establish `hcont : Continuous fun t : ℂ => t • w` using `continuous_id.smul continuous_const`. Establish `hopen : IsOpen ((fun t : ℂ => t • w) ⁻¹' {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ U})` using `(u.hol U 0).1.preimage hcont`. Take `⟨ρ, hρ, hball⟩` from `Metric.isOpen_iff.1 hopen 0 (by simpa using h0)`.

Establish `hconst : ∀ (s : Γ(A.left, U)) (t : ℂ), t ∈ Metric.ball (0 : ℂ) ρ → valAt' (u.ex (t • w)).left U s = valAt' (u.ex ((0 : ℂ) • w)).left U s`. Introduce `s t ht`. Establish `hder : ∀ t ∈ Metric.ball (0 : ℂ) ρ, HasDerivAt (fun t : ℂ => valAt' (u.ex (t • w)).left U s) 0 t`. Introduce `t ht`. Establish `hm : ⊤ ≤ (u.ex (t • w)).left ⁻¹ᵁ U` using `hball ht`.

Establish `hd : DifferentiableAt ℂ (fun y => valAt' (u.ex y).left U s) (t • w)` using `(u.hol U s).2.differentiableAt ((u.hol U s).1.mem_nhds hm)`. Establish `hl : HasDerivAt (fun t : ℂ => t • w) w t`. Simplify using `using (hasDerivAt_id t).smul_const w`. Use `hd.hasFDerivAt.comp_hasDerivAt t hl` as an intermediate fact. Rewrite `this` using `[fderiv_eq_zero_of_isDiff_one u h _ hm s]`.

Conclude with `this`. Conclude with `Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball _ _).isPreconnected (fun t ht => (hder t ht).differentiableAt.differentiableWithinAt) (fun t ht => (hder t ht).deriv) ht (Metric.mem_ball_self hρ)`. Establish `hmem : ∀ t ∈ Metric.ball (0 : ℂ) ρ, t • w ∈ u.Λ`. Introduce `t ht`. Establish `hm : ⊤ ≤ (u.ex (t • w)).left ⁻¹ᵁ U` using `hball ht`.

Establish `hm0 : ⊤ ≤ (u.ex ((0 : ℂ) • w)).left ⁻¹ᵁ U` using `by simpa using h0`. Establish `e : (u.ex (t • w)).left = (u.ex ((0 : ℂ) • w)).left` using `ext_evalPt hU hm hm0 (RingHom.ext fun s => by`. Rewrite using `[← valAt'_eq_evalPt _ _ hm, ← valAt'_eq_evalPt _ _ hm0]`. Conclude with `hconst s t ht)`. Establish `e' : u.ex (t • w) = u.ex ((0 : ℂ) • w)` using `Over.OverMorphism.ext e`.

Rewrite using `[← u.ker, e', zero_smul, ex_zero]`. Assume the negation of the conclusion as `hw`. Use `u.discrete` as an intermediate fact. Take `⟨O, hO, hO0⟩` from `isDiscrete_iff_forall_mem_exists_isOpen.1 (isDiscrete_iff_discreteTopology.2 this) 0 u.Λ.zero_mem`. Establish `hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t • w ∈ O ∧ t ∈ Metric.ball (0 : ℂ) ρ`.

Use `Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_` and prove the remaining obligations. Use `((hcont.tendsto 0).eventually (hO.mem_nhds ?_)).and (Metric.ball_mem_nhds _ hρ)` and prove the remaining obligations. Simplify using `using (hO0.ge rfl).1`. Take `⟨t, ⟨h1, h2⟩, ht⟩` from `(hev.and self_mem_nhdsWithin).exists`. Establish `h3 : t • w = 0` using `hO0.le ⟨h1, hmem t h2⟩`.

Conclude with `hw ((smul_eq_zero.1 h3).resolve_left ht)`.
-/
theorem eq_zero_of_isDiff_one (u : HolUnif A L g) {w : Fin g → ℂ} (h : u.IsDiff w (1 : epsR ℂ ⟶ A)) : w = 0 := by
  let pt : (𝟙_ (Over (Sp ℂ))).left := (default : PrimeSpectrum ℂ)
  have hsub : ∀ q : (𝟙_ (Over (Sp ℂ))).left, q = pt := fun q =>
    Subsingleton.elim (α := PrimeSpectrum ℂ) q pt
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (x := (u.ex 0).left pt) (U := ⊤)
    (Set.mem_univ _)
  have h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := by
    intro q _
    rw [hsub q]
    exact hpU
  have hcont : Continuous fun t : ℂ => t • w := continuous_id.smul continuous_const
  have hopen : IsOpen ((fun t : ℂ => t • w) ⁻¹' {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ U}) := (u.hol U 0).1.preimage hcont
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hopen 0 (by simpa using h0)
  have hconst : ∀ (s : Γ(A.left, U)) (t : ℂ), t ∈ Metric.ball (0 : ℂ) ρ →
      valAt' (u.ex (t • w)).left U s = valAt' (u.ex ((0 : ℂ) • w)).left U s := by
    intro s t ht
    have hder : ∀ t ∈ Metric.ball (0 : ℂ) ρ, HasDerivAt (fun t : ℂ => valAt' (u.ex (t • w)).left U s) 0 t := by
      intro t ht
      have hm : ⊤ ≤ (u.ex (t • w)).left ⁻¹ᵁ U := hball ht
      have hd : DifferentiableAt ℂ (fun y => valAt' (u.ex y).left U s) (t • w) :=
        (u.hol U s).2.differentiableAt ((u.hol U s).1.mem_nhds hm)
      have hl : HasDerivAt (fun t : ℂ => t • w) w t := by
        simpa using (hasDerivAt_id t).smul_const w
      have := hd.hasFDerivAt.comp_hasDerivAt t hl
      rw [fderiv_eq_zero_of_isDiff_one u h _ hm s] at this
      exact this
    exact Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball _ _).isPreconnected
      (fun t ht => (hder t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hder t ht).deriv) ht (Metric.mem_ball_self hρ)
  have hmem : ∀ t ∈ Metric.ball (0 : ℂ) ρ, t • w ∈ u.Λ := by
    intro t ht
    have hm : ⊤ ≤ (u.ex (t • w)).left ⁻¹ᵁ U := hball ht
    have hm0 : ⊤ ≤ (u.ex ((0 : ℂ) • w)).left ⁻¹ᵁ U := by simpa using h0
    have e : (u.ex (t • w)).left = (u.ex ((0 : ℂ) • w)).left := ext_evalPt hU hm hm0 (RingHom.ext fun s => by
      rw [← valAt'_eq_evalPt _ _ hm, ← valAt'_eq_evalPt _ _ hm0]
      exact hconst s t ht)
    have e' : u.ex (t • w) = u.ex ((0 : ℂ) • w) := Over.OverMorphism.ext e
    rw [← u.ker, e', zero_smul, ex_zero]
  by_contra hw
  have := u.discrete
  obtain ⟨O, hO, hO0⟩ := isDiscrete_iff_forall_mem_exists_isOpen.1
    (isDiscrete_iff_discreteTopology.2 this) 0 u.Λ.zero_mem
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t • w ∈ O ∧ t ∈ Metric.ball (0 : ℂ) ρ := by
    refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
    refine ((hcont.tendsto 0).eventually (hO.mem_nhds ?_)).and (Metric.ball_mem_nhds _ hρ)
    simpa using (hO0.ge rfl).1
  obtain ⟨t, ⟨h1, h2⟩, ht⟩ := (hev.and self_mem_nhdsWithin).exists
  have h3 : t • w = 0 := hO0.le ⟨h1, hmem t h2⟩
  exact hw ((smul_eq_zero.1 h3).resolve_left ht)

/- English proof (translation)
Set `pt : (𝟙_ (Over (Sp ℂ))).left` to `(default : PrimeSpectrum ℂ)`. Establish `hsub : ∀ q : (𝟙_ (Over (Sp ℂ))).left, q = pt` using `fun q => Subsingleton.elim (α := PrimeSpectrum ℂ) q pt`. Take `⟨U, hU, hpU, -⟩` from `exists_isAffineOpen_mem_and_subset (x := (u.ex 0).left pt) (U := ⊤) (Set.mem_univ _)`. Use `⟨U, hU, ?_⟩` and prove the remaining obligations. Introduce `q _`.

Rewrite using `[hsub q]`. Conclude with `hpU`.
-/
theorem exists_affine (u : HolUnif A L g) : ∃ U : A.left.Opens, IsAffineOpen U ∧ ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := by
  let pt : (𝟙_ (Over (Sp ℂ))).left := (default : PrimeSpectrum ℂ)
  have hsub : ∀ q : (𝟙_ (Over (Sp ℂ))).left, q = pt := fun q =>
    Subsingleton.elim (α := PrimeSpectrum ℂ) q pt
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (x := (u.ex 0).left pt) (U := ⊤)
    (Set.mem_univ _)
  refine ⟨U, hU, ?_⟩
  intro q _
  rw [hsub q]
  exact hpU

/- English proof (translation)
Take `⟨U, hU, h0⟩` from `exists_affine u`. Establish `hvU` using `(tangent_mem_iff (u := u) hv U).2 h0`. Conclude with `sub_eq_zero.1 (eq_zero_of_isDiff_one u (isDiff_one_of_fderiv u hU h0 fun s => by`. Rewrite using `[map_sub, ← h U hvU s, ← h' U hvU s, sub_self]))`.
-/
theorem eq_of_isDiff (u : HolUnif A L g) {v : epsR ℂ ⟶ A} (hv : IsTangent v) {d d' : Fin g → ℂ}
    (h : u.IsDiff d v) (h' : u.IsDiff d' v) : d = d' := by
  obtain ⟨U, hU, h0⟩ := exists_affine u
  have hvU := (tangent_mem_iff (u := u) hv U).2 h0
  exact sub_eq_zero.1 (eq_zero_of_isDiff_one u (isDiff_one_of_fderiv u hU h0 fun s => by
    rw [map_sub, ← h U hvU s, ← h' U hvU s, sub_self]))

/- English proof (translation)
Use `letI : CommGroup (𝟙_ (Over (Sp ℂ)) ⟶ A) := { (inferInstance : Group (𝟙_ (Over (Sp ℂ)) ⟶ A)) with mul_comm := fun a b => by`. Take `⟨z, rfl⟩` from `u.ex_onto a`. Take `⟨w, rfl⟩` from `u.ex_onto b`. Conclude with `(u.ex_add z w).symm.trans ((congrArg u.ex (add_comm z w)).trans (u.ex_add w z)) }`. Set `ex : (Fin g → ℂ) →+ Additive (𝟙_ (Over (Sp ℂ)) ⟶ A)` to `AddMonoidHom.mk' (fun z => Additive.ofMul (u.ex z)) u.ex_add`.

Set `G' : (Fin g' → ℂ) →+ Additive (𝟙_ (Over (Sp ℂ)) ⟶ A)` to `AddMonoidHom.mk' (fun z => Additive.ofMul (u'.ex z ≫ f)) (fun z w => by`. Express the relevant statement in the definitionally equal form `u'.ex (z + w) ≫ f = (u'.ex z ≫ f) * (u'.ex w ≫ f)`. Rewrite using `[u'.ex_add]`. Conclude with `MonObj.mul_comp _ _ f)`. Establish `hhol` using `GlobalTheory.HomLinear.isHolTo_ex_comp u' f`.

Take `⟨U, hU, h0⟩` from `exists_affine u`. Establish `hker : (ex.ker : Set (Fin g → ℂ)) = u.Λ` using `Set.ext fun z => u.ker z`. Take `⟨F, hF, -⟩` from `GlobalTheory.existsUnique_linear_lift_of_separating (ex := ex) (G := G') u.ex_onto (hker ▸ isDiscrete_iff_discreteTopology.2 u.discrete) (S := {a | ⊤ ≤ (Additive.toMul a).left ⁻¹ᵁ U}) (f := fun (s : Γ(A.left, U)) a => valAt' (Additive.toMul a).left U s) (by rw [← map_zero ex]; ex …`. Introduce `a ha b hb h`. Use `Over.OverMorphism.ext (f := Additive.toMul a) (g := Additive.toMul b) (ext_evalPt (R := ℂ) hU ha hb (RingHom.ext fun s => ?_))` and prove the remaining obligations.

Conclude with `(valAt'_eq_evalPt _ U ha s).symm.trans ((h s).trans (valAt'_eq_evalPt _ U hb s)))`. Use the proof step `(u.hol U 0).1 (by`. Use `(hhol U 0).1` as an intermediate fact. Simplify using `only [Set.mem_univ, true_and] at this`. Conclude with `this) (fun s => (u.hol U s).2) (fun s => by`.

Use `(hhol U s).2` as an intermediate fact. Simplify using `only [Set.mem_univ, true_and] at this`. Conclude with `this) (fun w hw => eq_zero_of_isDiff_one u (isDiff_one_of_fderiv u hU h0 hw))`. Conclude with `⟨F, hF⟩`.
-/
theorem exists_linear_compare {A' : Over (Sp ℂ)} [GrpObj A'] {L' : LB A'.left} {g' : ℕ} (u : HolUnif A L g)
    (u' : HolUnif A' L' g') (f : A' ⟶ A) [IsMonHom f] :
    ∃ F : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, u.ex (F z) = u'.ex z ≫ f := by
  letI : CommGroup (𝟙_ (Over (Sp ℂ)) ⟶ A) :=
    { (inferInstance : Group (𝟙_ (Over (Sp ℂ)) ⟶ A)) with
      mul_comm := fun a b => by
        obtain ⟨z, rfl⟩ := u.ex_onto a
        obtain ⟨w, rfl⟩ := u.ex_onto b
        exact (u.ex_add z w).symm.trans ((congrArg u.ex (add_comm z w)).trans (u.ex_add w z)) }
  let ex : (Fin g → ℂ) →+ Additive (𝟙_ (Over (Sp ℂ)) ⟶ A) :=
    AddMonoidHom.mk' (fun z => Additive.ofMul (u.ex z)) u.ex_add
  let G' : (Fin g' → ℂ) →+ Additive (𝟙_ (Over (Sp ℂ)) ⟶ A) :=
    AddMonoidHom.mk' (fun z => Additive.ofMul (u'.ex z ≫ f)) (fun z w => by
      change u'.ex (z + w) ≫ f = (u'.ex z ≫ f) * (u'.ex w ≫ f)
      rw [u'.ex_add]
      exact MonObj.mul_comp _ _ f)
  have hhol := GlobalTheory.HomLinear.isHolTo_ex_comp u' f
  obtain ⟨U, hU, h0⟩ := exists_affine u
  have hker : (ex.ker : Set (Fin g → ℂ)) = u.Λ := Set.ext fun z => u.ker z
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_separating (ex := ex) (G := G') u.ex_onto
    (hker ▸ isDiscrete_iff_discreteTopology.2 u.discrete)
    (S := {a | ⊤ ≤ (Additive.toMul a).left ⁻¹ᵁ U})
    (f := fun (s : Γ(A.left, U)) a => valAt' (Additive.toMul a).left U s)
    (by rw [← map_zero ex]; exact h0) (by
      intro a ha b hb h
      refine Over.OverMorphism.ext (f := Additive.toMul a) (g := Additive.toMul b)
        (ext_evalPt (R := ℂ) hU ha hb (RingHom.ext fun s => ?_))
      exact (valAt'_eq_evalPt _ U ha s).symm.trans ((h s).trans (valAt'_eq_evalPt _ U hb s)))
    (u.hol U 0).1 (by
      have := (hhol U 0).1
      simp only [Set.mem_univ, true_and] at this
      exact this) (fun s => (u.hol U s).2) (fun s => by
      have := (hhol U s).2
      simp only [Set.mem_univ, true_and] at this
      exact this) (fun w hw => eq_zero_of_isDiff_one u (isDiff_one_of_fderiv u hU h0 hw))
  exact ⟨F, hF⟩

end Unif

section Pull

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {z : Sp ℂ ⟶ X}
  {A : Over (Sp ℂ)} [GrpObj A] {φ : A.left ⟶ G.left}

def push (h : IsGrpPullback A G z φ) {T : Over (Sp ℂ)} (x : T ⟶ A) : Over.mk (T.hom ≫ z) ⟶ G :=
  Over.homMk (x.left ≫ φ) (by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w x]
    rfl)

/- English proof (translation)
Establish `e` using `h.2 T 1 1 (push h 1) (push h 1) rfl rfl`. Rewrite `e` using `[_root_.mul_one]`. Establish `e' : push h 1 * push h 1 = push h (1 : T ⟶ A)` using `Over.OverMorphism.ext e`. Conclude with `congrArg (·.left) (mul_eq_left.1 e')`.
-/
theorem one_left_comp (h : IsGrpPullback A G z φ) (T : Over (Sp ℂ)) :
    (1 : T ⟶ A).left ≫ φ = (1 : Over.mk (T.hom ≫ z) ⟶ G).left := by
  have e := h.2 T 1 1 (push h 1) (push h 1) rfl rfl
  rw [_root_.mul_one] at e
  have e' : push h 1 * push h 1 = push h (1 : T ⟶ A) := Over.OverMorphism.ext e
  exact congrArg (·.left) (mul_eq_left.1 e')

/- English proof (translation)
Rewrite using `[Hom.one_def, Over.comp_left]`. Use `congr 1`.
-/
theorem one_left {Y : Scheme.{0}} (y : Y ⟶ X) : (1 : Over.mk y ⟶ G).left = y ≫ η[G].left := by
  rw [Hom.one_def, Over.comp_left]
  congr 1

def lft (h : IsGrpPullback A G z φ) (v : epsAt z ⟶ G) : epsR ℂ ⟶ A :=
  Over.homMk (h.1.lift v.left (spMap (algebraMap ℂ (DualNumber ℂ))) (Over.w v)) (h.1.lift_snd _ _ _)

/- English proof (translation)
The claim follows from `h.1.lift_fst _ _ _`.
-/
theorem lft_left (h : IsGrpPullback A G z φ) (v : epsAt z ⟶ G) : (lft h v).left ≫ φ = v.left :=
  h.1.lift_fst _ _ _

/- English proof (translation)
The claim follows from `Over.OverMorphism.ext (h.1.hom_ext (e.trans (lft_left h v).symm) (by rw [Over.w, Over.w]))`.
-/
theorem lft_unique (h : IsGrpPullback A G z φ) {v : epsAt z ⟶ G} {v' : epsR ℂ ⟶ A} (e : v'.left ≫ φ = v.left) :
    v' = lft h v :=
  Over.OverMorphism.ext (h.1.hom_ext (e.trans (lft_left h v).symm) (by rw [Over.w, Over.w]))

/- English proof (translation)
Unfold `IsTangent`. Use `h.1.hom_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, lft_left]`. Use `Eq.trans hv ?_` and prove the remaining obligations. Establish `e` using `one_left_comp h (𝟙_ (Over (Sp ℂ)))`.

Rewrite `e` using `[Hom.one_def, toUnit_unit, Category.id_comp]`. Rewrite using `[e, one_left, one_left]`. Simplify using the standard rewrite rules. Rewrite using `[Category.assoc]`. Establish `e1 : (lft h v).left ≫ A.hom = spMap (algebraMap ℂ (DualNumber ℂ))` using `Over.w _`.

Establish `e2 : η[A].left ≫ A.hom = 𝟙 _` using `by simpa using Over.w η[A]`. Rewrite using `[e1, e2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Establish `: (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ`. Use extensionality with `x`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
theorem isTangent_lft (h : IsGrpPullback A G z φ) {v : epsAt z ⟶ G} (hv : IsTanAt G z v) : IsTangent (lft h v) := by
  unfold IsTangent
  refine h.1.hom_ext ?_ ?_
  · rw [Category.assoc, lft_left]
    refine Eq.trans hv ?_
    have e := one_left_comp h (𝟙_ (Over (Sp ℂ)))
    rw [Hom.one_def, toUnit_unit, Category.id_comp] at e
    rw [e, one_left, one_left]
    simp
  · rw [Category.assoc]
    have e1 : (lft h v).left ≫ A.hom = spMap (algebraMap ℂ (DualNumber ℂ)) := Over.w _
    have e2 : η[A].left ≫ A.hom = 𝟙 _ := by simpa using Over.w η[A]
    rw [e1, e2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ := by
      ext x
      simp
    rw [this]
    simp

end Pull

section Gen

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}

/- English proof (translation)
Set `n : (A ⊗ A).left ⟶ (A ⊗ A).left` to `(lift (1 : A ⊗ A ⟶ A) (1 : A ⊗ A ⟶ A)).left`. Take `⟨r, hr, hv⟩` from `exists_gen hL (φ' := rosatiφ A f g) (ε' := rosatiε) (fun V _ k => by`. Establish `p` using `prod_ros f g (1 : A ⊗ A ⟶ A) (1 : A ⊗ A ⟶ A) k`. Rewrite `p` using `[MonObj.one_comp, MonObj.one_comp, _root_.mul_one]`. Use `Eq.trans (DVR.prod_sum₂ (K := Fin 6) (K' := Fin 6) (U := V) _ (c := ∏ i, k (rosatiφ A f g i) ^ rosatiε i) rfl (DVR.prod_neg _ _ p)) ?_` and prove the remaining obligations.

Use the proof step `simp)`. Use the proof step `(LB.mulGen L _ _ _ _ t (LB.invGen L _ _ (LB.pullGen L _ _ t n)))`. Use the proof step `(DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht n)))`. Use `⟨r, ⟨hr, corr_of_val hL fun y J hJ => ?_⟩⟩` and prove the remaining obligations. Establish `e : zero2 A ≫ n = zero2 A` using `by show (lift η[A] η[A] ≫ lift (1 : A ⊗ A ⟶ A) (1 : A ⊗ A ⟶ A)).left = _`.

Use `congr 1`. Rewrite using `[comp_lift]`. Simplify using `[Hom.one_def]`. Rewrite using `[val_pull hJ, hv _ _ y J hJ, val_mul hJ, val_inv, val_pull hJ, val_one, Category.id_comp, e, mul_inv_cancel]`.
-/
theorem exists_isRos_of_gen (hL : L.IsLB) (f g : A ⟶ A) [IsMonHom f] [IsMonHom g]
    (t : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)) (ht : t.IsGen) :
    ∃ r : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε), GlobalTheory.TorusExt.IsRos L f g r := by
  let n : (A ⊗ A).left ⟶ (A ⊗ A).left := (lift (1 : A ⊗ A ⟶ A) (1 : A ⊗ A ⟶ A)).left
  obtain ⟨r, hr, hv⟩ := exists_gen hL (φ' := rosatiφ A f g) (ε' := rosatiε)
    (fun V _ k => by
      have p := prod_ros f g (1 : A ⊗ A ⟶ A) (1 : A ⊗ A ⟶ A) k
      rw [MonObj.one_comp, MonObj.one_comp, _root_.mul_one] at p
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 6) (K' := Fin 6) (U := V) _
        (c := ∏ i, k (rosatiφ A f g i) ^ rosatiε i) rfl (DVR.prod_neg _ _ p)) ?_
      simp)
    (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ (LB.pullGen L _ _ t n)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht n)))
  refine ⟨r, ⟨hr, corr_of_val hL fun y J hJ => ?_⟩⟩
  have e : zero2 A ≫ n = zero2 A := by
    show (lift η[A] η[A] ≫ lift (1 : A ⊗ A ⟶ A) (1 : A ⊗ A ⟶ A)).left = _
    congr 1
    rw [comp_lift]
    simp [Hom.one_def]
  rw [val_pull hJ, hv _ _ y J hJ, val_mul hJ, val_inv, val_pull hJ, val_one, Category.id_comp, e, mul_inv_cancel]

end Gen

section Sab

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}}

/- English proof (translation)
Use `haveI := t.act.hom a`. Use `haveI := t.act.hom (H.bar a)`. Take `⟨u, hu⟩` from `gen_of_lbIso (LBIso.symm (t.adj a))`. Take `⟨v, hv, -⟩` from `exists_gen t.PP.isLB (φ' := rosatiφ t.G (t.act.act a) (t.act.act (H.bar a))) (ε' := rosatiε) (fun U _ k => by`. Establish `p` using `prod_ros (t.act.act a) (t.act.act (H.bar a)) (fst t.G t.G) (snd t.G t.G) k`.

Rewrite `p` using `[lift_fst_snd]`. Simplify using `only [Over.id_left, Category.id_comp] at p`. Use `(DVR.prod_sum₂ (K := ULift.{0} (Finset (Fin 2))) (K' := ULift.{0} (Finset (Fin 2))) (U := U) _ (prod_cube₂ _ _ k) (DVR.prod_neg _ _ (prod_cube₂ _ _ k))).trans (Eq.trans ?_ p.symm)` and prove the remaining obligations. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv]`.

Use the proof step `abel) u hu`. Conclude with `exists_isRos_of_gen t.PP.isLB _ _ v hv`.
-/
theorem SAB_exists_isRos (t : SAB H S) (a : 𝓞 E) :
    ∃ r : LB.Gen (LB.LinComb t.PP.L (rosatiφ t.G (t.act.act a) (t.act.act (H.bar a))) rosatiε),
      GlobalTheory.TorusExt.IsRos t.PP.L (t.act.act a) (t.act.act (H.bar a)) r := by
  haveI := t.act.hom a
  haveI := t.act.hom (H.bar a)
  obtain ⟨u, hu⟩ := gen_of_lbIso (LBIso.symm (t.adj a))
  obtain ⟨v, hv, -⟩ := exists_gen t.PP.isLB (φ' := rosatiφ t.G (t.act.act a) (t.act.act (H.bar a))) (ε' := rosatiε)
    (fun U _ k => by
      have p := prod_ros (t.act.act a) (t.act.act (H.bar a)) (fst t.G t.G) (snd t.G t.G) k
      rw [lift_fst_snd] at p
      simp only [Over.id_left, Category.id_comp] at p
      refine (DVR.prod_sum₂ (K := ULift.{0} (Finset (Fin 2))) (K' := ULift.{0} (Finset (Fin 2))) (U := U) _ (prod_cube₂ _ _ k)
        (DVR.prod_neg _ _ (prod_cube₂ _ _ k))).trans (Eq.trans ?_ p.symm)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) u hu
  exact exists_isRos_of_gen t.PP.isLB _ _ v hv

end Sab

section Fibre

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {z : Sp ℂ ⟶ X} {A : Over (Sp ℂ)} [GrpObj A] {φ : A.left ⟶ G.left}

/- English proof (translation)
Establish `hc : ∀ (T : Over (Sp ℂ)) (x y : T ⟶ A), x * y = y * x` using `fun T x y => Over.OverMorphism.ext (h.1.hom_ext (by`. Rewrite using `[← h.2 T x y (push h x) (push h y) rfl rfl, ← h.2 T y x (push h y) (push h x) rfl rfl, mul_comm]) (by`. Rewrite using `[Over.w, Over.w]))`. Use `⟨?_⟩` and prove the remaining obligations. Establish `e` using `hc (A ⊗ A) (fst A A) (snd A A)`.

Rewrite `e` using `[Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp]`. Establish `b : (β_ A A).hom = lift (snd A A) (fst A A)` using `CartesianMonoidalCategory.hom_ext _ _ (by simp) (by simp)`. Rewrite using `[b]`. Conclude with `e.symm`.
-/
theorem isCommMonObj_of_pullback [IsCommMonObj G] (h : IsGrpPullback A G z φ) : IsCommMonObj A := by
  have hc : ∀ (T : Over (Sp ℂ)) (x y : T ⟶ A), x * y = y * x := fun T x y =>
    Over.OverMorphism.ext (h.1.hom_ext (by
      rw [← h.2 T x y (push h x) (push h y) rfl rfl, ← h.2 T y x (push h y) (push h x) rfl rfl, mul_comm]) (by
      rw [Over.w, Over.w]))
  refine ⟨?_⟩
  have e := hc (A ⊗ A) (fst A A) (snd A A)
  rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at e
  have b : (β_ A A).hom = lift (snd A A) (fst A A) := CartesianMonoidalCategory.hom_ext _ _ (by simp) (by simp)
  rw [b]
  exact e.symm

/- English proof (translation)
Set `f : A ⟶ A` to `Over.homMk (h.1.lift (φ ≫ f₀.left) A.hom (by rw [Category.assoc, Over.w, h.1.w])) (h.1.lift_snd _ _ _)`. Establish `hf : f.left ≫ φ = φ ≫ f₀.left` using `h.1.lift_fst _ _ _`. Use `⟨f, isMonHom_of_mul _ fun T x y => ?_, hf⟩` and prove the remaining obligations. Use `Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w]))` and prove the remaining obligations. Establish `e1` using `h.2 T x y (push h x) (push h y) rfl rfl`.

Establish `e2` using `h.2 T (x ≫ f) (y ≫ f) (push h x ≫ f₀) (push h y ≫ f₀) (by simp [push, hf]) (by simp [push, hf])`. Rewrite using `[Over.comp_left, Category.assoc, hf, ← Category.assoc, ← e1, ← e2, ← Over.comp_left, MonObj.mul_comp]`.
-/
theorem exists_endo (h : IsGrpPullback A G z φ) (f₀ : G ⟶ G) [IsMonHom f₀] :
    ∃ f : A ⟶ A, IsMonHom f ∧ f.left ≫ φ = φ ≫ f₀.left := by
  let f : A ⟶ A := Over.homMk (h.1.lift (φ ≫ f₀.left) A.hom (by rw [Category.assoc, Over.w, h.1.w])) (h.1.lift_snd _ _ _)
  have hf : f.left ≫ φ = φ ≫ f₀.left := h.1.lift_fst _ _ _
  refine ⟨f, isMonHom_of_mul _ fun T x y => ?_, hf⟩
  refine Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w]))
  have e1 := h.2 T x y (push h x) (push h y) rfl rfl
  have e2 := h.2 T (x ≫ f) (y ≫ f) (push h x ≫ f₀) (push h y ≫ f₀)
    (by simp [push, hf]) (by simp [push, hf])
  rw [Over.comp_left, Category.assoc, hf, ← Category.assoc, ← e1, ← e2, ← Over.comp_left, MonObj.mul_comp]

end Fibre

/- English proof (translation)
Unfold `IsTanAt at hv ⊢`. Rewrite using `[Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, MonObj.one_comp]`.
-/
theorem isTanAt_comp {X : Scheme.{0}} {G : Over X} [GrpObj G] {z : Sp ℂ ⟶ X} (f : G ⟶ G) [IsMonHom f]
    {v : epsAt z ⟶ G} (hv : IsTanAt G z v) : IsTanAt G z (v ≫ f) := by
  unfold IsTanAt at hv ⊢
  rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, MonObj.one_comp]

end GlobalTheory.CompanionTheory.Ar.HodgeAdj

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HodgeAdj

/- English proof (translation)
Introduce `E _ _ _ H X t z v w a c hfib hv hw`. Take `⟨V, _, _, ⟨M⟩⟩` from `lieModel_exists X t.G ℂ z`. Take `⟨h, hh, -, -⟩` from `GlobalTheory.T.hodge_hermitian_form_exists E H X t z V M hfib`. Use `haveI := t.act.hom a`. Use `haveI := t.act.hom (H.bar a)`.

Take `⟨x', hx'⟩` from `M.onto _ (isTanAt_comp (t.act.act a) hv)`. Take `⟨y', hy'⟩` from `M.onto _ (isTanAt_comp (t.act.act (H.bar a)) hw)`. Take `⟨x, rfl⟩` from `M.onto v hv`. Take `⟨y, rfl⟩` from `M.onto w hw`. Rewrite using `[← hx', ← hy', hh, hh]`.

It suffices to establish `e : h x' y = h x y' by rw [e]`. Take `⟨hL, -, -, A, _, φ, g, u, Hm, χ, v₁, w₁, α, β, hpb, hAH, e₁, e₂, d₁, d₂, -⟩` from `(hh x y _).2 rfl`. Use `haveI := isCommMonObj_of_pullback hpb`. Take `⟨f, _, hf⟩` from `exists_endo hpb (t.act.act a)`. Take `⟨f', _, hf'⟩` from `exists_endo hpb (t.act.act (H.bar a))`.

Take `⟨F, hF⟩` from `exists_linear_compare u u f`. Take `⟨F', hF'⟩` from `exists_linear_compare u u f'`. Take `⟨r, hr⟩` from `SAB_exists_isRos t a`. Establish `hLφ : (t.PP.L.pull φ).IsLB` using `LB.isLB_pull t.PP.isLB φ`. Take `⟨wi, hwi⟩` from `GlobalTheory.PolBaseChange.lbIso_refl hLφ`.

Take `⟨s, hs, -⟩` from `GlobalTheory.Ex.Arch.FibRos.exists_ros_down hpb t.PP.isLB hLφ hwi (MonObj.one_comp _) (MonObj.one_comp _) hf hf' hr`. Establish `adj` using `(GlobalTheory.FrameValue.genVal_rosati hLφ hAH hF hF' s hs.1 hs.2).1`. Establish `t₁ : IsTangent v₁`. Rewrite using `[lft_unique hpb e₁]`. Conclude with `isTangent_lft hpb (M.tan x)`.

Establish `t₂ : IsTangent w₁`. Rewrite using `[lft_unique hpb e₂]`. Conclude with `isTangent_lft hpb (M.tan y)`. Establish `c₁ : HodgeIP t.G t.PP.L z (M.pt x') (M.pt y) (Real.pi * (β ⬝ᵥ Hm.mulVec (star (F α))))` using `⟨hL, M.tan _, M.tan _, A, inferInstance, φ, g, u, Hm, χ, v₁ ≫ f, w₁, F α, β, hpb, hAH, by rw [hx', Over.comp_left, Over.comp_left, Category.assoc, hf, ← Category.assoc, e₁], e₂, GlobalTheory.HomLinear.isDiff_comp u u f F hF t₁ d₁, d₂, rfl⟩`. Establish `c₂ : HodgeIP t.G t.PP.L z (M.pt x) (M.pt y') (Real.pi * (F' β ⬝ᵥ Hm.mulVec (star α)))` using `⟨hL, M.tan _, M.tan _, A, inferInstance, φ, g, u, Hm, χ, v₁, w₁ ≫ f', α, F' β, hpb, hAH, e₁, by rw [hy', Over.comp_left, Over.comp_left, Category.assoc, hf', ← Category.assoc, e₂], d₁, GlobalTheory.HomLinear.isDiff_comp u u f' F' hF' t₂ d₂, rfl⟩`.

Rewrite using `[← (hh _ _ _).1 c₁, ← (hh _ _ _).1 c₂]`. Use `congr 1`. Use `congrArg (starRingEnd ℂ) (adj α β)` as an intermediate fact. Rewrite `this` using `[conj_hermForm hAH.1, conj_hermForm hAH.1]`. Then use the resulting hypothesis.
-/
theorem hodgeInnerProduct_act_adjoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (z : Spec (CommRingCat.of ℂ) ⟶ X) (v w : epsAt z ⟶ t.G) (a : 𝓞 E) (c : ℂ), (∃ (t' : SAB H (Sp ℂ)) (_ : SABMap t' t z), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L) → IsTanAt t.G z v → IsTanAt t.G z w → (HodgeIP t.G t.PP.L z (v ≫ t.act.act a) w c ↔ HodgeIP t.G t.PP.L z v (w ≫ t.act.act (H.bar a)) c) := by
  intro E _ _ _ H X t z v w a c hfib hv hw
  obtain ⟨V, _, _, ⟨M⟩⟩ := lieModel_exists X t.G ℂ z
  obtain ⟨h, hh, -, -⟩ := GlobalTheory.T.hodge_hermitian_form_exists E H X t z V M hfib
  haveI := t.act.hom a
  haveI := t.act.hom (H.bar a)
  obtain ⟨x', hx'⟩ := M.onto _ (isTanAt_comp (t.act.act a) hv)
  obtain ⟨y', hy'⟩ := M.onto _ (isTanAt_comp (t.act.act (H.bar a)) hw)
  obtain ⟨x, rfl⟩ := M.onto v hv
  obtain ⟨y, rfl⟩ := M.onto w hw
  rw [← hx', ← hy', hh, hh]
  suffices e : h x' y = h x y' by rw [e]
  obtain ⟨hL, -, -, A, _, φ, g, u, Hm, χ, v₁, w₁, α, β, hpb, hAH, e₁, e₂, d₁, d₂, -⟩ := (hh x y _).2 rfl
  haveI := isCommMonObj_of_pullback hpb
  obtain ⟨f, _, hf⟩ := exists_endo hpb (t.act.act a)
  obtain ⟨f', _, hf'⟩ := exists_endo hpb (t.act.act (H.bar a))
  obtain ⟨F, hF⟩ := exists_linear_compare u u f
  obtain ⟨F', hF'⟩ := exists_linear_compare u u f'
  obtain ⟨r, hr⟩ := SAB_exists_isRos t a
  have hLφ : (t.PP.L.pull φ).IsLB := LB.isLB_pull t.PP.isLB φ
  obtain ⟨wi, hwi⟩ := GlobalTheory.PolBaseChange.lbIso_refl hLφ
  obtain ⟨s, hs, -⟩ := GlobalTheory.Ex.Arch.FibRos.exists_ros_down hpb t.PP.isLB hLφ hwi (MonObj.one_comp _) (MonObj.one_comp _) hf hf' hr
  have adj := (GlobalTheory.FrameValue.genVal_rosati hLφ hAH hF hF' s hs.1 hs.2).1
  have t₁ : IsTangent v₁ := by
    rw [lft_unique hpb e₁]
    exact isTangent_lft hpb (M.tan x)
  have t₂ : IsTangent w₁ := by
    rw [lft_unique hpb e₂]
    exact isTangent_lft hpb (M.tan y)
  have c₁ : HodgeIP t.G t.PP.L z (M.pt x') (M.pt y) (Real.pi * (β ⬝ᵥ Hm.mulVec (star (F α)))) :=
    ⟨hL, M.tan _, M.tan _, A, inferInstance, φ, g, u, Hm, χ, v₁ ≫ f, w₁, F α, β, hpb, hAH,
      by rw [hx', Over.comp_left, Over.comp_left, Category.assoc, hf, ← Category.assoc, e₁], e₂,
      GlobalTheory.HomLinear.isDiff_comp u u f F hF t₁ d₁, d₂, rfl⟩
  have c₂ : HodgeIP t.G t.PP.L z (M.pt x) (M.pt y') (Real.pi * (F' β ⬝ᵥ Hm.mulVec (star α))) :=
    ⟨hL, M.tan _, M.tan _, A, inferInstance, φ, g, u, Hm, χ, v₁, w₁ ≫ f', α, F' β, hpb, hAH, e₁,
      by rw [hy', Over.comp_left, Over.comp_left, Category.assoc, hf', ← Category.assoc, e₂], d₁,
      GlobalTheory.HomLinear.isDiff_comp u u f' F' hF' t₂ d₂, rfl⟩
  rw [← (hh _ _ _).1 c₁, ← (hh _ _ _).1 c₂]
  congr 1
  have := congrArg (starRingEnd ℂ) (adj α β)
  rwa [conj_hermForm hAH.1, conj_hermForm hAH.1] at this

end GlobalTheory.CompanionTheory.Ar
