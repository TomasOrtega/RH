import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsWeierstrassCoordinatesOnLine
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolarisedAbelianSchemeLieBasisInvariants
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeDeterminedByInvariants
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.OverHomEqIffForallIsAlgClosedAlgebra
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat.Weber

open GlobalTheory.WeierstrassCurve GlobalTheory.UnifCoord GlobalTheory.PeriodicWeierstrass Filter Topology PeriodPair

/- English proof (translation)
Establish `hw0 : w ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hw`. Establish `hlin : Differentiable ℂ (fun z : ℂ => z • w)` using `by fun_prop`. Establish `hcont : Tendsto (fun z : ℂ => z • w) (𝓝 0) (𝓝 0)`.

Simplify using `using hlin.continuous.tendsto 0`. Establish `hd2 : ∀ j, DifferentiableOn ℂ (fun z : ℂ => F 2 j (z • w)) {z | z • w ∈ Λ}ᶜ` using `fun j => (hd 2 j).comp hlin.differentiableOn fun z hz h => hz ((hΛ _).1 h)`. Establish `hn1 : {z | P z 1 ≠ 0} ∈ 𝓝 (0 : Fin g → ℂ)` using `(ho 1).mem_nhds h1`. Establish `hev1 : ∀ᶠ z : ℂ in 𝓝 0, P (z • w) 1 ≠ 0` using `hcont hn1`. Establish `hoff : ∀ᶠ z : ℂ in 𝓝[≠] 0, P (z • w) 2 ≠ 0`.

Establish `h : ({0} : Set Λ) ∈ 𝓝 (0 : Λ)` using `(isOpen_discrete _).mem_nhds rfl`. Rewrite `h` using `[nhds_subtype_eq_comap, mem_comap]`. Take `⟨s, hs, hs'⟩` from `h`. Establish `h' : ∀ᶠ z : ℂ in 𝓝 0, z • w ∈ s` using `hcont hs`. Use `filter_upwards [mem_nhdsWithin_of_mem_nhds h', self_mem_nhdsWithin] with z hz hz0 h2`.

Use `hs' (show (⟨z • w, (hΛ _).1 h2⟩ : Λ) ∈ Subtype.val ⁻¹' s from hz)` as an intermediate fact. Establish `e : z • w = 0` using `congrArg Subtype.val this`. Conclude with `hz0 ((smul_eq_zero.1 e).resolve_right hw0)`. Establish `hda : ∀ j, DifferentiableAt ℂ (F 1 j) 0` using `fun j => (hd 1 j).differentiableAt hn1`. Establish `h2 : P 0 2 = 0` using `(hΛ 0).2 Λ.zero_mem`.

Use `⟨hw0, fun z => F 2 0 (z • w), fun z => F 2 1 (z • w), fun z => -F 1 0 (z • w), fun _ => rfl, hd2 0, hd2 1, fun l hl z => ?_, fun z hz => ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [add_smul, hper _ _ _ _ hl, and_self]`. Establish `hz2 : P (z • w) 2 ≠ 0` using `fun h => hz ((hΛ _).1 h)`. Rewrite using `[← WeierstrassCurve.Projective.equation_some, ← WeierstrassCurve.Projective.equation_smul _ (isUnit_iff_ne_zero.2 hz2)]`. Use `hE (z • w) using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `i`. Use `fin_cases i`. Simplify `hF 2 0 _ hz2` using `[mul_comm]`. Simplify `hF 2 1 _ hz2` using `[mul_comm]`. Simplify using the standard rewrite rules.

Use `AnalyticAt.neg (DifferentiableOn.analyticAt (s := {z : ℂ | P (z • w) 1 ≠ 0}) ?_ hev1)` and prove the remaining obligations. Conclude with `(hd 1 0).comp hlin.differentiableOn fun z hz => hz`. Use `hF 1 0 0 h1` as an intermediate fact. Rewrite `this` using `[h0, mul_eq_zero]`. Simplify using `[this.resolve_right h1]`.

Establish `h3 : HasDerivAt (fun z : ℂ => z • w) w 0`. Simplify using `using (hasDerivAt_id (0 : ℂ)).smul_const w`. Establish `h4 : HasFDerivAt (F 1 0) (fderiv ℂ (F 1 0) 0) ((0 : ℂ) • w)`. Rewrite using `[zero_smul]`. Conclude with `(hda 0).hasFDerivAt`.

Establish `h5` using `(h4.comp_hasDerivAt (0 : ℂ) h3).neg`. Rewrite `h5` using `[hw, neg_neg]`. Conclude with `h5.deriv`. Use `filter_upwards [mem_nhdsWithin_of_mem_nhds hev1, hoff] with z hz1 hz2`. Apply `mul_right_cancel₀ hz2` to reduce the goal to its premises.

Establish `a` using `hF 1 0 _ hz1`. Establish `b` using `hF 2 0 _ hz2`. Establish `c` using `hF 2 1 _ hz2`. Take the linear combination `-(F 1 0 (z • w)) * c - a + b`. Establish `hs0 : F 1 2 0 = 0`.

Use `hF 1 2 0 h1` as an intermediate fact. Rewrite `this` using `[h2, mul_eq_zero]`. Conclude with `this.resolve_right h1`. Establish `hs : Tendsto (fun z : ℂ => F 1 2 (z • w)) (𝓝[≠] 0) (𝓝 0)`. Use `(hda 2).continuousAt.tendsto.comp hcont` as an intermediate fact.

Rewrite `this` using `[hs0]`. Conclude with `this.mono_left nhdsWithin_le_nhds`. Establish `hprod : ∀ᶠ z : ℂ in 𝓝[≠] 0, F 1 2 (z • w) * F 2 1 (z • w) = 1` using `by filter_upwards [mem_nhdsWithin_of_mem_nhds hev1, hoff] with z hz1 hz2`. Apply `mul_right_cancel₀ hz2` to reduce the goal to its premises. Establish `a` using `hF 1 2 _ hz1`.

Establish `c` using `hF 2 1 _ hz2`. Take the linear combination `(F 1 2 (z • w)) * c + a`. Establish `hs' : Tendsto (fun z : ℂ => F 1 2 (z • w)) (𝓝[≠] 0) (𝓝[≠] 0)` using `tendsto_nhdsWithin_iff.2 ⟨hs, hprod.mono fun z hz => left_ne_zero_of_mul_eq_one hz⟩`. Use `(tendsto_norm_inv_nhdsNE_zero_atTop.comp hs').congr' ?_` and prove the remaining obligations. Use `filter_upwards [hprod] with z hz`.

Simplify using `only [Function.comp_apply]`. Rewrite using `[eq_inv_of_mul_eq_one_right hz]`.
-/
theorem exists_xyt_eq {g : ℕ} (V : WeierstrassCurve ℂ) (Λ : Submodule ℤ (Fin g → ℂ))
    [DiscreteTopology Λ] (P : (Fin g → ℂ) → Fin 3 → ℂ) (F : Fin 3 → Fin 3 → (Fin g → ℂ) → ℂ)
    (hE : ∀ z, V.toProjective.Equation (P z))
    (ho : ∀ i, IsOpen {z | P z i ≠ 0}) (hd : ∀ i j, DifferentiableOn ℂ (F i j) {z | P z i ≠ 0})
    (hF : ∀ i j z, P z i ≠ 0 → F i j z * P z i = P z j) (hΛ : ∀ z, P z 2 = 0 ↔ z ∈ Λ)
    (hper : ∀ i j z l, l ∈ Λ → F i j (z + l) = F i j z) (h0 : P 0 0 = 0) (h1 : P 0 1 ≠ 0)
    (w : Fin g → ℂ) (hw : fderiv ℂ (F 1 0) 0 w = -1) :
    w ≠ 0 ∧ ∃ x y t : ℂ → ℂ, (∀ z, x z = F 2 0 (z • w)) ∧ DifferentiableOn ℂ x {z | z • w ∈ Λ}ᶜ ∧
      DifferentiableOn ℂ y {z | z • w ∈ Λ}ᶜ ∧
      (∀ l : ℂ, l • w ∈ Λ → ∀ z, x (z + l) = x z ∧ y (z + l) = y z) ∧
      (∀ z : ℂ, z • w ∉ Λ → V.toAffine.Equation (x z) (y z)) ∧ AnalyticAt ℂ t 0 ∧ t 0 = 0 ∧
      deriv t 0 = 1 ∧ (∀ᶠ z in nhdsWithin 0 {0}ᶜ, t z * y z = -x z) ∧
      Filter.Tendsto (fun z => ‖y z‖) (nhdsWithin 0 {0}ᶜ) Filter.atTop := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw
  have hlin : Differentiable ℂ (fun z : ℂ => z • w) := by fun_prop
  have hcont : Tendsto (fun z : ℂ => z • w) (𝓝 0) (𝓝 0) := by
    simpa using hlin.continuous.tendsto 0
  have hd2 : ∀ j, DifferentiableOn ℂ (fun z : ℂ => F 2 j (z • w)) {z | z • w ∈ Λ}ᶜ := fun j =>
    (hd 2 j).comp hlin.differentiableOn fun z hz h => hz ((hΛ _).1 h)
  have hn1 : {z | P z 1 ≠ 0} ∈ 𝓝 (0 : Fin g → ℂ) := (ho 1).mem_nhds h1
  have hev1 : ∀ᶠ z : ℂ in 𝓝 0, P (z • w) 1 ≠ 0 := hcont hn1
  have hoff : ∀ᶠ z : ℂ in 𝓝[≠] 0, P (z • w) 2 ≠ 0 := by
    have h : ({0} : Set Λ) ∈ 𝓝 (0 : Λ) := (isOpen_discrete _).mem_nhds rfl
    rw [nhds_subtype_eq_comap, mem_comap] at h
    obtain ⟨s, hs, hs'⟩ := h
    have h' : ∀ᶠ z : ℂ in 𝓝 0, z • w ∈ s := hcont hs
    filter_upwards [mem_nhdsWithin_of_mem_nhds h', self_mem_nhdsWithin] with z hz hz0 h2
    have := hs' (show (⟨z • w, (hΛ _).1 h2⟩ : Λ) ∈ Subtype.val ⁻¹' s from hz)
    have e : z • w = 0 := congrArg Subtype.val this
    exact hz0 ((smul_eq_zero.1 e).resolve_right hw0)
  have hda : ∀ j, DifferentiableAt ℂ (F 1 j) 0 := fun j => (hd 1 j).differentiableAt hn1
  have h2 : P 0 2 = 0 := (hΛ 0).2 Λ.zero_mem
  refine ⟨hw0, fun z => F 2 0 (z • w), fun z => F 2 1 (z • w), fun z => -F 1 0 (z • w), fun _ => rfl,
    hd2 0, hd2 1,
    fun l hl z => ?_, fun z hz => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [add_smul, hper _ _ _ _ hl, and_self]
  · have hz2 : P (z • w) 2 ≠ 0 := fun h => hz ((hΛ _).1 h)
    rw [← WeierstrassCurve.Projective.equation_some,
      ← WeierstrassCurve.Projective.equation_smul _ (isUnit_iff_ne_zero.2 hz2)]
    convert hE (z • w) using 1
    ext i
    fin_cases i
    · simpa [mul_comm] using hF 2 0 _ hz2
    · simpa [mul_comm] using hF 2 1 _ hz2
    · simp
  · refine AnalyticAt.neg (DifferentiableOn.analyticAt (s := {z : ℂ | P (z • w) 1 ≠ 0}) ?_ hev1)
    exact (hd 1 0).comp hlin.differentiableOn fun z hz => hz
  · have := hF 1 0 0 h1
    rw [h0, mul_eq_zero] at this
    simp [this.resolve_right h1]
  · have h3 : HasDerivAt (fun z : ℂ => z • w) w 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).smul_const w
    have h4 : HasFDerivAt (F 1 0) (fderiv ℂ (F 1 0) 0) ((0 : ℂ) • w) := by
      rw [zero_smul]; exact (hda 0).hasFDerivAt
    have h5 := (h4.comp_hasDerivAt (0 : ℂ) h3).neg
    rw [hw, neg_neg] at h5
    exact h5.deriv
  · filter_upwards [mem_nhdsWithin_of_mem_nhds hev1, hoff] with z hz1 hz2
    apply mul_right_cancel₀ hz2
    have a := hF 1 0 _ hz1
    have b := hF 2 0 _ hz2
    have c := hF 2 1 _ hz2
    linear_combination -(F 1 0 (z • w)) * c - a + b
  · have hs0 : F 1 2 0 = 0 := by
      have := hF 1 2 0 h1
      rw [h2, mul_eq_zero] at this
      exact this.resolve_right h1
    have hs : Tendsto (fun z : ℂ => F 1 2 (z • w)) (𝓝[≠] 0) (𝓝 0) := by
      have := (hda 2).continuousAt.tendsto.comp hcont
      rw [hs0] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hprod : ∀ᶠ z : ℂ in 𝓝[≠] 0, F 1 2 (z • w) * F 2 1 (z • w) = 1 := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds hev1, hoff] with z hz1 hz2
      apply mul_right_cancel₀ hz2
      have a := hF 1 2 _ hz1
      have c := hF 2 1 _ hz2
      linear_combination (F 1 2 (z • w)) * c + a
    have hs' : Tendsto (fun z : ℂ => F 1 2 (z • w)) (𝓝[≠] 0) (𝓝[≠] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨hs, hprod.mono fun z hz => left_ne_zero_of_mul_eq_one hz⟩
    refine (tendsto_norm_inv_nhdsNE_zero_atTop.comp hs').congr' ?_
    filter_upwards [hprod] with z hz
    simp only [Function.comp_apply]
    rw [eq_inv_of_mul_eq_one_right hz]

/- English proof (translation)
Introduce `R _ W f A _ φ v h hpb he hv L₁ g u w hw`. Take `⟨c, hc, -⟩` from `GlobalTheory.CoordFn.exists_coordFn R W`. Establish `hover : ∀ z, (u.ex z).left ≫ A.hom = 𝟙 (Sp ℂ)` using `fun z => Over.w (u.ex z)`. Establish `hpt : ∀ z, ∃ (P : Fin 3 → ℂ) (hP : IsUnimodularSol (W.map f) P), (u.ex z).left ≫ φ = ptHom W f P hP` using `fun z => exists_eq_ptHom_of_isLocalRing R W ℂ f ((u.ex z).left ≫ φ) (by`. Rewrite using `[Category.assoc, hpb.w, ← Category.assoc, hover]`.

Conclude with `Category.id_comp _)`. Use `choose P hP hPe using hpt`. Establish `hmem : ∀ z i, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (φ ⁻¹ᵁ coordOpen W i) ↔ P z i ≠ 0` using `fun z i => by`. Rewrite using `[← top_le_ptHom_preimage_iff W f (P z) (hP z), ← hPe, Scheme.Hom.comp_preimage]`. Establish `hset : ∀ i, {z | P z i ≠ 0} = {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (φ ⁻¹ᵁ coordOpen W i)}` using `fun i => Set.ext fun z => (hmem z i).symm`.

Establish `hΛ : ∀ z, P z 2 = 0 ↔ z ∈ u.Λ` using `fun z => by`. Rewrite using `[ptHom_eq_zero_iff W f (P z) (hP z), ← hPe, ← he, ← u.ker]`. Prove the components needed by the constructor for the conclusion. Introduce `e`. Establish `e' : u.ex z = η[A]` using `Over.OverMorphism.ext (hpb.hom_ext e ((hover z).trans (Over.w η[A]).symm))`.

Rewrite using `[e', Hom.one_def]`. Simplify using the standard rewrite rules. Introduce `e`. Rewrite using `[e, Hom.one_def]`. Simplify using `[eSec]`.

Establish `h00` using `eq_zero_and_ne_zero (hP 0) ((hΛ 0).2 u.Λ.zero_mem)`. Use `u.discrete` as an intermediate fact. Establish `hF : ∀ i j z, P z i ≠ 0 → valAt' (u.ex z).left (φ ⁻¹ᵁ coordOpen W i) ((φ.app (coordOpen W i)).hom (c i j)) * P z i = P z j` using `fun i j z hz => by`. Establish `hz'` using `(top_le_ptHom_preimage_iff W f (P z) (hP z) i).2 hz`. Establish `e : valAt' (u.ex z).left (φ ⁻¹ᵁ coordOpen W i) ((φ.app (coordOpen W i)).hom (c i j)) = valAt' (ptHom W f (P z) (hP z)) (coordOpen W i) (c i j)` using `(valAt'_comp (u.ex z).left φ _ _).trans (congrArg (fun k => valAt' k _ _) (hPe z))`.

Rewrite using `[e, valAt'_eq_valAt _ hz']`. Conclude with `hc i j ℂ f (P z) (hP z) hz'`. Use `(exists_xyt_eq (W.map f) u.Λ P (fun i j z => valAt' (u.ex z).left (φ ⁻¹ᵁ coordOpen W i) ((φ.app (coordOpen W i)).hom (c i j))) (fun z => (hP z).equation) (fun i => hset i ▸ (u.hol _ 0).1) (fun i j => hset i ▸ (u.hol _ _).2) hF hΛ (fun i j z l hl => ?_) h00.1 h00.2 w ?_).imp_right …` and prove the remaining obligations. Simplify using `only [u.ex_add, (u.ker l).2 hl, _root_.mul_one]`. Establish `h1 : ⊤ ≤ ptHom W ((algebraMap ℂ (DualNumber ℂ)).comp f) ![DualNumber.eps, -1, 0] h ⁻¹ᵁ coordOpen W 1`.

Rewrite using `[ptHom_preimage_coordOpen]`. Introduce `p _ hp`. Conclude with `p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hp isUnit_one.neg)`. Establish `h2 : ⊤ ≤ v.left ⁻¹ᵁ (φ ⁻¹ᵁ coordOpen W 1)`. Rewrite using `[← Scheme.Hom.comp_preimage, hv]`.

Conclude with `h1`. Rewrite using `[← hw _ h2]`. Establish `e` using `hc 1 0 _ _ _ h h1`. Establish `e2 : ∀ (k : Sp (DualNumber ℂ) ⟶ scheme W) (hk : ⊤ ≤ k ⁻¹ᵁ coordOpen W 1), v.left ≫ φ = k → (v.left.appLE (φ ⁻¹ᵁ coordOpen W 1) ⊤ h2).hom ((φ.app (coordOpen W 1)).hom (c 1 0)) = (k.appLE (coordOpen W 1) ⊤ hk).hom (c 1 0)`. Introduce and unpack `_ hk rfl`.

Rewrite using `[Scheme.Hom.comp_appLE]`. Both sides reduce to the same expression. Rewrite using `[e2 _ h1 hv]`. Establish `e3` using `congrArg TrivSqZeroExt.snd e`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_neg, _root_.mul_one, TrivSqZeroExt.snd_neg, DualNumber.snd_eps] at e3`.

Conclude with `neg_eq_iff_eq_neg.1 e3`.
-/
theorem exists_coord_eq : ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R) (f : R →+* ℂ) (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ scheme W) (v : epsR ℂ ⟶ A) (h : IsUnimodularSol (W.map ((algebraMap ℂ (DualNumber ℂ)).comp f)) ![DualNumber.eps, -1, 0]), IsPullback φ A.hom (toSpec W) (spMap f) → eSec A ≫ φ = spMap f ≫ zero W → v.left ≫ φ = ptHom W ((algebraMap ℂ (DualNumber ℂ)).comp f) ![DualNumber.eps, -1, 0] h → ∀ (L₁ : LB A.left) (g : ℕ) (u : HolUnif A L₁ g) (w : Fin g → ℂ), u.IsDiff w v → w ≠ 0 ∧ ∃ x y t : ℂ → ℂ, (∀ z : ℂ, ∃ (P : Fin 3 → ℂ) (hP : IsUnimodularSol (W.map f) P), (u.ex (z • w)).left ≫ φ = ptHom W f P hP ∧ (P 2 = 0 ↔ z • w ∈ u.Λ) ∧ (P 2 ≠ 0 → x z * P 2 = P 0)) ∧ DifferentiableOn ℂ x {z | z • w ∈ u.Λ}ᶜ ∧ DifferentiableOn ℂ y {z | z • w ∈ u.Λ}ᶜ ∧ (∀ l : ℂ, l • w ∈ u.Λ → ∀ z, x (z + l) = x z ∧ y (z + l) = y z) ∧ (∀ z : ℂ, z • w ∉ u.Λ → (W.map f).toAffine.Equation (x z) (y z)) ∧ AnalyticAt ℂ t 0 ∧ t 0 = 0 ∧ deriv t 0 = 1 ∧ (∀ᶠ z in nhdsWithin 0 {0}ᶜ, t z * y z = -x z) ∧ Filter.Tendsto (fun z => ‖y z‖) (nhdsWithin 0 {0}ᶜ) Filter.atTop := by
  intro R _ W f A _ φ v h hpb he hv L₁ g u w hw
  obtain ⟨c, hc, -⟩ := GlobalTheory.CoordFn.exists_coordFn R W
  have hover : ∀ z, (u.ex z).left ≫ A.hom = 𝟙 (Sp ℂ) := fun z => Over.w (u.ex z)
  have hpt : ∀ z, ∃ (P : Fin 3 → ℂ) (hP : IsUnimodularSol (W.map f) P),
      (u.ex z).left ≫ φ = ptHom W f P hP := fun z =>
    exists_eq_ptHom_of_isLocalRing R W ℂ f ((u.ex z).left ≫ φ) (by
      rw [Category.assoc, hpb.w, ← Category.assoc, hover]
      exact Category.id_comp _)
  choose P hP hPe using hpt
  have hmem : ∀ z i, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (φ ⁻¹ᵁ coordOpen W i) ↔ P z i ≠ 0 := fun z i => by
    rw [← top_le_ptHom_preimage_iff W f (P z) (hP z), ← hPe, Scheme.Hom.comp_preimage]
  have hset : ∀ i, {z | P z i ≠ 0} = {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (φ ⁻¹ᵁ coordOpen W i)} :=
    fun i => Set.ext fun z => (hmem z i).symm
  have hΛ : ∀ z, P z 2 = 0 ↔ z ∈ u.Λ := fun z => by
    rw [ptHom_eq_zero_iff W f (P z) (hP z), ← hPe, ← he, ← u.ker]
    constructor
    · intro e
      have e' : u.ex z = η[A] :=
        Over.OverMorphism.ext (hpb.hom_ext e ((hover z).trans (Over.w η[A]).symm))
      rw [e', Hom.one_def]
      simp
    · intro e
      rw [e, Hom.one_def]
      simp [eSec]
  have h00 := eq_zero_and_ne_zero (hP 0) ((hΛ 0).2 u.Λ.zero_mem)
  have := u.discrete
  have hF : ∀ i j z, P z i ≠ 0 → valAt' (u.ex z).left (φ ⁻¹ᵁ coordOpen W i)
      ((φ.app (coordOpen W i)).hom (c i j)) * P z i = P z j := fun i j z hz => by
    have hz' := (top_le_ptHom_preimage_iff W f (P z) (hP z) i).2 hz
    have e : valAt' (u.ex z).left (φ ⁻¹ᵁ coordOpen W i) ((φ.app (coordOpen W i)).hom (c i j)) =
        valAt' (ptHom W f (P z) (hP z)) (coordOpen W i) (c i j) :=
      (valAt'_comp (u.ex z).left φ _ _).trans (congrArg (fun k => valAt' k _ _) (hPe z))
    rw [e, valAt'_eq_valAt _ hz']
    exact hc i j ℂ f (P z) (hP z) hz'
  refine (exists_xyt_eq (W.map f) u.Λ P (fun i j z => valAt' (u.ex z).left (φ ⁻¹ᵁ coordOpen W i)
    ((φ.app (coordOpen W i)).hom (c i j))) (fun z => (hP z).equation)
    (fun i => hset i ▸ (u.hol _ 0).1) (fun i j => hset i ▸ (u.hol _ _).2) hF hΛ
    (fun i j z l hl => ?_) h00.1 h00.2 w ?_).imp_right fun ⟨x, y, t, hx, h'⟩ =>
      ⟨x, y, t, fun z => ⟨_, hP _, hPe _, hΛ _, fun h2 => (hx z).symm ▸ hF 2 0 _ h2⟩, h'⟩
  · simp only [u.ex_add, (u.ker l).2 hl, _root_.mul_one]
  · have h1 : ⊤ ≤ ptHom W ((algebraMap ℂ (DualNumber ℂ)).comp f) ![DualNumber.eps, -1, 0] h ⁻¹ᵁ
        coordOpen W 1 := by
      rw [ptHom_preimage_coordOpen]
      intro p _ hp
      exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hp isUnit_one.neg)
    have h2 : ⊤ ≤ v.left ⁻¹ᵁ (φ ⁻¹ᵁ coordOpen W 1) := by
      rw [← Scheme.Hom.comp_preimage, hv]
      exact h1
    rw [← hw _ h2]
    have e := hc 1 0 _ _ _ h h1
    have e2 : ∀ (k : Sp (DualNumber ℂ) ⟶ scheme W) (hk : ⊤ ≤ k ⁻¹ᵁ coordOpen W 1),
        v.left ≫ φ = k → (v.left.appLE (φ ⁻¹ᵁ coordOpen W 1) ⊤ h2).hom
          ((φ.app (coordOpen W 1)).hom (c 1 0)) = (k.appLE (coordOpen W 1) ⊤ hk).hom (c 1 0) := by
      rintro _ hk rfl
      rw [Scheme.Hom.comp_appLE]
      rfl
    rw [e2 _ h1 hv]
    have e3 := congrArg TrivSqZeroExt.snd e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_neg, _root_.mul_one,
      TrivSqZeroExt.snd_neg, DualNumber.snd_eps] at e3
    exact neg_eq_iff_eq_neg.1 e3

/- English proof (translation)
Introduce `L W x y t c hc hx hy hp hE ht ht0 ht1 hty hyy`. Establish `hx' : ∀ z ∉ L.lattice, DifferentiableAt ℂ x z` using `fun z hz ↦ hx.differentiableAt (L.isClosed_lattice.isOpen_compl.mem_nhds hz)`. Establish `hy' : ∀ z ∉ L.lattice, DifferentiableAt ℂ y z` using `fun z hz ↦ hy.differentiableAt (L.isClosed_lattice.isOpen_compl.mem_nhds hz)`. Take `⟨lx, ly⟩` from `tendsto_leading W hc ((eventually_ne_notMem_periodLattice L 0).mono hE) ht ht0 ht1 hty hyy`. Take `⟨k, hk⟩` from `exists_eq_of_sq_mul_tendsto L (g := fun z ↦ c ^ 2 * x z) (fun z hz ↦ (hx' z hz).const_mul _) (fun z l hl ↦ by simp only [(hp l hl z).1]) lx`.

Establish `hid : Tendsto (fun z : ℂ ↦ z) (𝓝[≠] 0) (𝓝 0)` using `tendsto_id.mono_left nhdsWithin_le_nhds`. Take `⟨B, C, hB⟩` from `exists_eq_of_cube_mul_tendsto L (g := fun z ↦ c ^ 3 * (2 * y z + W.a₁ * x z + W.a₃)) (fun z hz ↦ by`. Use `hx' z hz` as an intermediate fact. Use `hy' z hz` as an intermediate fact. Use the proof step `fun_prop)`.

Use the proof step `(fun z l hl ↦ by simp only [(hp l hl z).1, (hp l hl z).2])`. Use the proof step `(by`. Use `((ly.const_mul 2).add ((hid.mul lx).const_mul (W.a₁ * c))).add ((hid.pow 3).const_mul (c ^ 3 * W.a₃))` as an intermediate fact. Simplify using `only [mul_neg, _root_.mul_one, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at this`. Conclude with `this.congr fun z ↦ by ring)`.

Establish `key : ∀ z ∉ L.lattice, (℘'[L] z + B * ℘[L] z + C) ^ 2 = 4 * (℘[L] z + k) ^ 3 + c ^ 2 * W.b₂ * (℘[L] z + k) ^ 2 + 2 * (c ^ 4 * W.b₄) * (℘[L] z + k) + c ^ 6 * W.b₆` using `fun z hz ↦ by`. Establish `e` using `hE z hz`. Rewrite `e` using `[WeierstrassCurve.Affine.equation_iff]`. Establish `e1` using `hk z hz`. Rewrite `e1` using `[_root_.one_mul]`.

Rewrite using `[← hB z hz, ← e1]`. Simplify using `only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]`. Take the linear combination `4 * c ^ 6 * e`. Establish `key2 : ∀ p : ℂ, (4 * p ^ 3 - L.g₂ * p - L.g₃) * (B * p + C) = 0 ∧ 4 * p ^ 3 - L.g₂ * p - L.g₃ + (B * p + C) ^ 2 = 4 * (p + k) ^ 3 + c ^ 2 * W.b₂ * (p + k) ^ 2 + 2 * (c ^ 4 * W.b₄) * (p + k) + c ^ 6 * W.b₆` using `fun p ↦ by`. Take `⟨z, hz, rfl⟩` from `exists_weierstrassP_eq L p`.

Establish `e1` using `key z hz`. Establish `e2` using `key (-z) (by simpa using hz)`. Rewrite `e2` using `[weierstrassP_neg, derivWeierstrassP_neg]`. Rewrite using `[← L.derivWeierstrassP_sq z hz]`. Conclude with `⟨by linear_combination ℘'[L] z / 4 * (e1 - e2), by linear_combination (e1 + e2) / 2⟩`.

Establish `hB0 : B = 0`. Take the linear combination `((key2 2).1 - 4 * (key2 1).1 + 6 * (key2 0).1 - 4 * (key2 (-1)).1 + (key2 (-2)).1) / 96`. Establish `hC0 : C = 0`. Take the linear combination `((key2 2).1 - 2 * (key2 1).1 + 2 * (key2 (-1)).1 - (key2 (-2)).1) / 48 + L.g₃ * 0 * hB0`. Establish `q0` using `(key2 0).2`.

Establish `q1` using `(key2 1).2`. Establish `q2` using `(key2 (-1)).2`. Rewrite `q0`, `q1`, `q2` using `[hB0, hC0]`. Establish `r2 : c ^ 2 * W.b₂ = -12 * k` using `by linear_combination (2 * q0 - q1 - q2) / 2`. Introduce `z hz`.

Take the linear combination `hk z hz + r2 / 12`.
-/
theorem x_eq_of_periodic_solution :
    ∀ (L : PeriodPair) (W : WeierstrassCurve ℂ) (x y t : ℂ → ℂ) (c : ℂ), c ≠ 0 →
  DifferentiableOn ℂ x (L.lattice : Set ℂ)ᶜ → DifferentiableOn ℂ y (L.lattice : Set ℂ)ᶜ →
  (∀ l ∈ L.lattice, ∀ z, x (z + l) = x z ∧ y (z + l) = y z) →
  (∀ z, z ∉ L.lattice → W.toAffine.Equation (x z) (y z)) →
  AnalyticAt ℂ t 0 → t 0 = 0 → deriv t 0 = c →
  (∀ᶠ z in nhdsWithin 0 {0}ᶜ, t z * y z = -x z) →
  Filter.Tendsto (fun z => ‖y z‖) (nhdsWithin 0 {0}ᶜ) Filter.atTop →
  ∀ z ∉ L.lattice, c ^ 2 * x z = ℘[L] z - c ^ 2 * W.b₂ / 12 := by
  intro L W x y t c hc hx hy hp hE ht ht0 ht1 hty hyy
  have hx' : ∀ z ∉ L.lattice, DifferentiableAt ℂ x z := fun z hz ↦
    hx.differentiableAt (L.isClosed_lattice.isOpen_compl.mem_nhds hz)
  have hy' : ∀ z ∉ L.lattice, DifferentiableAt ℂ y z := fun z hz ↦
    hy.differentiableAt (L.isClosed_lattice.isOpen_compl.mem_nhds hz)
  obtain ⟨lx, ly⟩ := tendsto_leading W hc
    ((eventually_ne_notMem_periodLattice L 0).mono hE) ht ht0 ht1 hty hyy
  obtain ⟨k, hk⟩ := exists_eq_of_sq_mul_tendsto L (g := fun z ↦ c ^ 2 * x z)
    (fun z hz ↦ (hx' z hz).const_mul _) (fun z l hl ↦ by simp only [(hp l hl z).1]) lx
  have hid : Tendsto (fun z : ℂ ↦ z) (𝓝[≠] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  obtain ⟨B, C, hB⟩ := exists_eq_of_cube_mul_tendsto L
    (g := fun z ↦ c ^ 3 * (2 * y z + W.a₁ * x z + W.a₃))
    (fun z hz ↦ by
      have := hx' z hz
      have := hy' z hz
      fun_prop)
    (fun z l hl ↦ by simp only [(hp l hl z).1, (hp l hl z).2])
    (by
      have := ((ly.const_mul 2).add ((hid.mul lx).const_mul (W.a₁ * c))).add
        ((hid.pow 3).const_mul (c ^ 3 * W.a₃))
      simp only [mul_neg, _root_.mul_one, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow] at this
      exact this.congr fun z ↦ by ring)
  have key : ∀ z ∉ L.lattice, (℘'[L] z + B * ℘[L] z + C) ^ 2 =
      4 * (℘[L] z + k) ^ 3 + c ^ 2 * W.b₂ * (℘[L] z + k) ^ 2 + 2 * (c ^ 4 * W.b₄) * (℘[L] z + k)
        + c ^ 6 * W.b₆ := fun z hz ↦ by
    have e := hE z hz
    rw [WeierstrassCurve.Affine.equation_iff] at e
    have e1 := hk z hz
    rw [_root_.one_mul] at e1
    rw [← hB z hz, ← e1]
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    linear_combination 4 * c ^ 6 * e
  have key2 : ∀ p : ℂ, (4 * p ^ 3 - L.g₂ * p - L.g₃) * (B * p + C) = 0 ∧
      4 * p ^ 3 - L.g₂ * p - L.g₃ + (B * p + C) ^ 2 =
      4 * (p + k) ^ 3 + c ^ 2 * W.b₂ * (p + k) ^ 2 + 2 * (c ^ 4 * W.b₄) * (p + k)
        + c ^ 6 * W.b₆ := fun p ↦ by
    obtain ⟨z, hz, rfl⟩ := exists_weierstrassP_eq L p
    have e1 := key z hz
    have e2 := key (-z) (by simpa using hz)
    rw [weierstrassP_neg, derivWeierstrassP_neg] at e2
    rw [← L.derivWeierstrassP_sq z hz]
    exact ⟨by linear_combination ℘'[L] z / 4 * (e1 - e2), by linear_combination (e1 + e2) / 2⟩
  have hB0 : B = 0 := by
    linear_combination ((key2 2).1 - 4 * (key2 1).1 + 6 * (key2 0).1 - 4 * (key2 (-1)).1
      + (key2 (-2)).1) / 96
  have hC0 : C = 0 := by
    linear_combination ((key2 2).1 - 2 * (key2 1).1 + 2 * (key2 (-1)).1 - (key2 (-2)).1) / 48
      + L.g₃ * 0 * hB0
  have q0 := (key2 0).2
  have q1 := (key2 1).2
  have q2 := (key2 (-1)).2
  rw [hB0, hC0] at q0 q1 q2
  have r2 : c ^ 2 * W.b₂ = -12 * k := by linear_combination (2 * q0 - q1 - q2) / 2
  intro z hz
  linear_combination hk z hz + r2 / 12

/- English proof (translation)
Take `⟨P₀, ψ₀, v, hg, hiso, hψ₀, he, ⟨h, hv⟩, hlie⟩` from `exists_polAV R W hΔ`. Take `⟨PC, ψ, hgC, hψ, -⟩` from `exists_baseChange polBaseChange_holds (spMap f) P₀`. Take `⟨v', hv't, hv'⟩` from `exists_tangent_over f hψ (hlie.1 0)`. Take `⟨u, hu⟩` from `exists_isThetaUnif thetaUnifAV_all PC`. Take `⟨w, hd, -⟩` from `hu.choose_spec.choose_spec.choose_spec.2.1 v' hv't`.

Take `⟨h', h1, h2, h3⟩` from `fibre_over_scheme W f hψ₀ he hv hψ hv'`. Take `⟨hw, x, y, t, hP, hx, hy, hper, heq, ht, ht0, ht1, hty, hlim⟩` from `exists_coord_eq R W f PC.A (ψ ≫ ψ₀) v' h' h1 h2 h3 PC.L PC.g u w hd`. Establish `hg1 : PC.g = 1` using `hgC.trans hg`. Take `⟨L', hL'⟩` from `exists_periodPair_of_lattice_in_line PC.g u.Λ w hg1 hw u.discrete u.full`. Establish `hset : (L'.lattice : Set ℂ) = {z | z • w ∈ u.Λ}` using `Set.ext hL'`.

Establish `key` using `invariants_eq_of_periodic_solution L' (W.map f) x y t 1 one_ne_zero (hset ▸ hx) (hset ▸ hy) (fun l hl => hper l ((hL' l).1 hl)) (fun z hz => heq z fun e => hz ((hL' z).2 e)) ht ht0 ht1 hty hlim`. Establish `kx` using `x_eq_of_periodic_solution L' (W.map f) x y t 1 one_ne_zero (hset ▸ hx) (hset ▸ hy) (fun l hl => hper l ((hL' l).1 hl)) (fun z hz => heq z fun e => hz ((hL' z).2 e)) ht ht0 ht1 hty hlim`. Simplify using `only [one_pow, _root_.one_mul, WeierstrassCurve.map_c₄, WeierstrassCurve.map_c₆, WeierstrassCurve.map_b₂, hb, map_zero, zero_div, sub_zero] at key kx`. Take `⟨m, hm⟩` from `IsAlgClosed.exists_pow_nat_eq lam⁻¹ (n := 2) (by norm_num)`. Establish `hm0 : m ≠ 0`.

Introduce and unpack `rfl`. Conclude with `inv_ne_zero hlam (by simpa using hm.symm)`. Establish `H₀` using `isHomothetic_scalePeriods L m hm0`. Establish `e : (scalePeriods L m hm0).lattice = L'.lattice`. Use `lattice_eq_of_g₂_eq_of_g₃_eq ?_ ?_` and prove the remaining obligations.

Rewrite using `[H₀.g₂_eq, show m ^ 4 = (m ^ 2) ^ 2 by ring, hm, inv_pow, inv_inv]`. Take the linear combination `(key.1 - h4) / 12`. Rewrite using `[H₀.g₃_eq, show m ^ 6 = (m ^ 2) ^ 3 by ring, hm, inv_pow, inv_inv]`. Take the linear combination `(key.2.1 - h6) / 216`. Establish `H : IsHomothetic m L L'` using `fun x => e ▸ H₀ x`.

Set `i : Fin PC.g` to `⟨0, by omega⟩`. Establish `hi : ∀ j : Fin PC.g, j = i` using `fun j => Fin.ext (by have := j.2; omega)`. Establish `hwi : w i ≠ 0` using `fun h => hw (funext fun j => by rw [hi j]; exact h)`. Establish `hc : ∀ z : ℂ, (fun _ => m * w i * z : Fin PC.g → ℂ) = (m * z) • w` using `fun z =>`. Use function extensionality and compare the values at `fun j => by rw [hi j, Pi.smul_apply, smul_eq_mul]; ring`.

Use `⟨P₀, PC, ψ, ψ₀, u, m * w i, hg1, hψ, hu, mul_ne_zero hm0 hwi, fun z => ⟨fun hz => ?_, ?_⟩, fun z => ?_⟩` and prove the remaining obligations. Establish `ez : z = fun _ => m * w i * (z i / (m * w i))` using `funext fun j => by rw [hi j]; field_simp`. Use `⟨_, ?_, ez⟩` and prove the remaining obligations. Rewrite using `[← H, hL', ← hc, ← ez]`. Conclude with `hz`.

Introduce and unpack `⟨l, hl, rfl⟩`. Rewrite using `[hc, ← hL', H]`. Conclude with `hl`. Take `⟨P, hP, e1, e2, e3⟩` from `hP (m * z)`. Use `⟨P, hP, by rw [hc]; exact e1, by rw [e2, ← hL', H], fun h2 => ?_⟩` and prove the remaining obligations.

Rewrite using `[← e3 h2, kx _ fun hz => h2 (e2.2 ((hL' _).1 hz)), H.weierstrassP_mul, hm, inv_inv]`.
-/
theorem exists_model (R : Type) [CommRing R] (f : R →+* ℂ) (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)
    (hb : W.b₂ = 0) (L : PeriodPair) (lam : ℂ) (hlam : lam ≠ 0) (h4 : f W.c₄ = 12 * (lam ^ 2 * L.g₂))
    (h6 : f W.c₆ = 216 * (lam ^ 3 * L.g₃)) :
    ∃ (P₀ : Out.PolAV (Sp R)) (PC : Out.PolAV (Sp ℂ)) (ψ : PC.A.left ⟶ P₀.A.left) (ψ₀ : P₀.A.left ⟶ scheme W)
      (u : HolUnif PC.A PC.L PC.g) (c : ℂ), PC.g = 1 ∧ IsGrpPullback PC.A P₀.A (spMap f) ψ ∧ IsThetaUnif u ∧
      c ≠ 0 ∧ (∀ z, z ∈ u.Λ ↔ ∃ l ∈ L.lattice, z = fun _ => c * l) ∧
      ∀ z : ℂ, ∃ (P : Fin 3 → ℂ) (hP : IsUnimodularSol (W.map f) P),
        (u.ex fun _ => c * z).left ≫ ψ ≫ ψ₀ = ptHom W f P hP ∧ (P 2 = 0 ↔ z ∈ L.lattice) ∧
          (P 2 ≠ 0 → lam * ℘[L] z * P 2 = P 0) := by
  obtain ⟨P₀, ψ₀, v, hg, hiso, hψ₀, he, ⟨h, hv⟩, hlie⟩ := exists_polAV R W hΔ
  obtain ⟨PC, ψ, hgC, hψ, -⟩ := exists_baseChange polBaseChange_holds (spMap f) P₀
  obtain ⟨v', hv't, hv'⟩ := exists_tangent_over f hψ (hlie.1 0)
  obtain ⟨u, hu⟩ := exists_isThetaUnif thetaUnifAV_all PC
  obtain ⟨w, hd, -⟩ := hu.choose_spec.choose_spec.choose_spec.2.1 v' hv't
  obtain ⟨h', h1, h2, h3⟩ := fibre_over_scheme W f hψ₀ he hv hψ hv'
  obtain ⟨hw, x, y, t, hP, hx, hy, hper, heq, ht, ht0, ht1, hty, hlim⟩ :=
    exists_coord_eq R W f PC.A (ψ ≫ ψ₀) v' h' h1 h2 h3 PC.L PC.g u w hd
  have hg1 : PC.g = 1 := hgC.trans hg
  obtain ⟨L', hL'⟩ := exists_periodPair_of_lattice_in_line PC.g u.Λ w hg1 hw u.discrete u.full
  have hset : (L'.lattice : Set ℂ) = {z | z • w ∈ u.Λ} := Set.ext hL'
  have key := invariants_eq_of_periodic_solution L' (W.map f) x y t 1 one_ne_zero (hset ▸ hx) (hset ▸ hy)
    (fun l hl => hper l ((hL' l).1 hl)) (fun z hz => heq z fun e => hz ((hL' z).2 e)) ht ht0 ht1 hty hlim
  have kx := x_eq_of_periodic_solution L' (W.map f) x y t 1 one_ne_zero (hset ▸ hx) (hset ▸ hy)
    (fun l hl => hper l ((hL' l).1 hl)) (fun z hz => heq z fun e => hz ((hL' z).2 e)) ht ht0 ht1 hty hlim
  simp only [one_pow, _root_.one_mul, WeierstrassCurve.map_c₄, WeierstrassCurve.map_c₆, WeierstrassCurve.map_b₂,
    hb, map_zero, zero_div, sub_zero] at key kx
  obtain ⟨m, hm⟩ := IsAlgClosed.exists_pow_nat_eq lam⁻¹ (n := 2) (by norm_num)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact inv_ne_zero hlam (by simpa using hm.symm)
  have H₀ := isHomothetic_scalePeriods L m hm0
  have e : (scalePeriods L m hm0).lattice = L'.lattice := by
    refine lattice_eq_of_g₂_eq_of_g₃_eq ?_ ?_
    · rw [H₀.g₂_eq, show m ^ 4 = (m ^ 2) ^ 2 by ring, hm, inv_pow, inv_inv]
      linear_combination (key.1 - h4) / 12
    · rw [H₀.g₃_eq, show m ^ 6 = (m ^ 2) ^ 3 by ring, hm, inv_pow, inv_inv]
      linear_combination (key.2.1 - h6) / 216
  have H : IsHomothetic m L L' := fun x => e ▸ H₀ x
  let i : Fin PC.g := ⟨0, by omega⟩
  have hi : ∀ j : Fin PC.g, j = i := fun j => Fin.ext (by have := j.2; omega)
  have hwi : w i ≠ 0 := fun h => hw (funext fun j => by rw [hi j]; exact h)
  have hc : ∀ z : ℂ, (fun _ => m * w i * z : Fin PC.g → ℂ) = (m * z) • w := fun z =>
    funext fun j => by rw [hi j, Pi.smul_apply, smul_eq_mul]; ring
  refine ⟨P₀, PC, ψ, ψ₀, u, m * w i, hg1, hψ, hu, mul_ne_zero hm0 hwi, fun z => ⟨fun hz => ?_, ?_⟩, fun z => ?_⟩
  · have ez : z = fun _ => m * w i * (z i / (m * w i)) := funext fun j => by rw [hi j]; field_simp
    refine ⟨_, ?_, ez⟩
    rw [← H, hL', ← hc, ← ez]
    exact hz
  · rintro ⟨l, hl, rfl⟩
    rw [hc, ← hL', H]
    exact hl
  · obtain ⟨P, hP, e1, e2, e3⟩ := hP (m * z)
    refine ⟨P, hP, by rw [hc]; exact e1, by rw [e2, ← hL', H], fun h2 => ?_⟩
    rw [← e3 h2, kx _ fun hz => h2 (e2.2 ((hL' _).1 hz)), H.weierstrassP_mul, hm, inv_inv]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Apply `sq_eq_sq_iff_eq_or_eq_neg.1` to reduce the goal to its premises. Rewrite using `[H.sqrt_neg_disc_sq, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]`. Simplify using the standard rewrite rules.
-/
theorem cmHost_rootComplex_eq_pm_sqrt (H : Host E) : H.rt0 = Complex.I * Real.sqrt H.d ∨ H.rt0 = -(Complex.I * Real.sqrt H.d) := by
  apply sq_eq_sq_iff_eq_or_eq_neg.1
  rw [H.sqrt_neg_disc_sq, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  simp

/- English proof (translation)
Break down `cmHost_rootComplex_eq_pm_sqrt H with h | h` into its components or cases. Conclude with `⟨fun ⟨s, e⟩ => ⟨s.1, s.2, by rw [e, wC, h]⟩, fun ⟨m, n, e⟩ => ⟨(m, n), by rw [e, wC, h]⟩⟩`. Conclude with `⟨fun ⟨s, e⟩ => ⟨s.1 + s.2, -s.2, by rw [e, wC, h]; push_cast; ring⟩, fun ⟨m, n, e⟩ => ⟨(m + n, -n), by rw [e, wC, h]; push_cast; ring⟩⟩`.
-/
theorem exists_wC_iff (H : Host E) (x : ℂ) :
    (∃ s, x = wC H s) ↔ ∃ m n : ℤ, x = (m : ℂ) + n * ((1 + Complex.I * Real.sqrt H.d) / 2) := by
  rcases cmHost_rootComplex_eq_pm_sqrt H with h | h
  · exact ⟨fun ⟨s, e⟩ => ⟨s.1, s.2, by rw [e, wC, h]⟩, fun ⟨m, n, e⟩ => ⟨(m, n), by rw [e, wC, h]⟩⟩
  · exact ⟨fun ⟨s, e⟩ => ⟨s.1 + s.2, -s.2, by rw [e, wC, h]; push_cast; ring⟩,
      fun ⟨m, n, e⟩ => ⟨(m + n, -n), by rw [e, wC, h]; push_cast; ring⟩⟩

/- English proof (translation)
Establish `hm` using `H.d_mod`. Take `⟨k, hk⟩ : ∃ k : ℕ, H.d + 1 = 4 * k` from `⟨(H.d + 1) / 4, by omega⟩`. Establish `hk' : (H.d : ℂ) + 1 = 4 * k` using `by exact_mod_cast hk`. Use `⟨(s.1 * a.1 - k * (s.2 * a.2), s.1 * a.2 + s.2 * a.1 + s.2 * a.2), ?_⟩` and prove the remaining obligations. Simplify using `only [wC]`.

Use `push_cast`. Take the linear combination `(s.2 * a.2 / 4 : ℂ) * H.sqrt_neg_disc_sq - (s.2 * a.2 / 4 : ℂ) * hk'`.
-/
theorem wC_mul (H : Host E) (s a : ℤ × ℤ) : ∃ b, wC H s * wC H a = wC H b := by
  have hm := H.d_mod
  obtain ⟨k, hk⟩ : ∃ k : ℕ, H.d + 1 = 4 * k := ⟨(H.d + 1) / 4, by omega⟩
  have hk' : (H.d : ℂ) + 1 = 4 * k := by exact_mod_cast hk
  refine ⟨(s.1 * a.1 - k * (s.2 * a.2), s.1 * a.2 + s.2 * a.1 + s.2 * a.2), ?_⟩
  simp only [wC]
  push_cast
  linear_combination (s.2 * a.2 / 4 : ℂ) * H.sqrt_neg_disc_sq - (s.2 * a.2 / 4 : ℂ) * hk'

/- English proof (translation)
Take `⟨m, n, e⟩` from `(exists_wC_iff H _).1 ⟨s, rfl⟩`. Establish `hd : 7 ≤ H.d` using `by have := H.d_mod; omega`. Establish `hd' : (7 : ℝ) ≤ H.d` using `by exact_mod_cast hd`. Establish `hs` using `Real.sq_sqrt (Nat.cast_nonneg H.d : (0 : ℝ) ≤ H.d)`. Establish `him : (wC H s).im = n * √H.d / 2` using `by rw [e]; simp; ring`.

Assume the negation of the conclusion as `h0`. Establish `hn : n ≠ 0` using `by rintro rfl; simp [him] at h0`. Establish `h1 : (1 : ℝ) ≤ (n : ℝ) ^ 2` using `by exact_mod_cast (one_le_sq_iff_one_le_abs n).2 (Int.one_le_abs hn)`. Rewrite `h` using `[Complex.normSq_apply, him]`. Use polynomial arithmetic with `[mul_self_nonneg (wC H s).re]`.
-/
theorem im_eq_zero_of_norm (H : Host E) (s : ℤ × ℤ) (h : Complex.normSq (wC H s) = 1) : (wC H s).im = 0 := by
  obtain ⟨m, n, e⟩ := (exists_wC_iff H _).1 ⟨s, rfl⟩
  have hd : 7 ≤ H.d := by have := H.d_mod; omega
  have hd' : (7 : ℝ) ≤ H.d := by exact_mod_cast hd
  have hs := Real.sq_sqrt (Nat.cast_nonneg H.d : (0 : ℝ) ≤ H.d)
  have him : (wC H s).im = n * √H.d / 2 := by rw [e]; simp; ring
  by_contra h0
  have hn : n ≠ 0 := by rintro rfl; simp [him] at h0
  have h1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast (one_le_sq_iff_one_le_abs n).2 (Int.one_le_abs hn)
  rw [Complex.normSq_apply, him] at h
  nlinarith [mul_self_nonneg (wC H s).re]

/- English proof (translation)
Establish `hm0 : m ≠ 0` using `by rintro rfl; simp at h0`. Establish `H₀` using `isHomothetic_scalePeriods L m hm0`. Establish `e` using `lattice_eq_of_g₂_eq_of_g₃_eq (H₀.g₂_eq.trans h2) (H₀.g₃_eq.trans h3)`. Use `(H₀ 1).2 ((hL 1).2 ⟨(1, 0), by simp [wC]⟩)` as an intermediate fact. Rewrite `this` using `[e, _root_.mul_one, hL]`.

Take `⟨s, rfl⟩` from `this`. Conclude with `h0 (im_eq_zero_of_norm H s h1)`.
-/
theorem not_invariant (H : Host E) (L : PeriodPair) (hL : ∀ x, x ∈ L.lattice ↔ ∃ s, x = wC H s) (m : ℂ)
    (h1 : Complex.normSq m = 1) (h0 : m.im ≠ 0) (h2 : (m ^ 4)⁻¹ * L.g₂ = L.g₂) (h3 : (m ^ 6)⁻¹ * L.g₃ = L.g₃) :
    False := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at h0
  have H₀ := isHomothetic_scalePeriods L m hm0
  have e := lattice_eq_of_g₂_eq_of_g₃_eq (H₀.g₂_eq.trans h2) (H₀.g₃_eq.trans h3)
  have := (H₀ 1).2 ((hL 1).2 ⟨(1, 0), by simp [wC]⟩)
  rw [e, _root_.mul_one, hL] at this
  obtain ⟨s, rfl⟩ := this
  exact h0 (im_eq_zero_of_norm H s h1)

/- English proof (translation)
Introduce `h`. Establish `hs` using `Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)`. Establish `hs' : ((√3 : ℝ) : ℂ) ^ 2 = 3` using `by exact_mod_cast hs`. Establish `h6 : ((1 + Complex.I * (√3 : ℝ)) / 2) ^ 3 = -1`. Take the linear combination `(3 / 8 + Complex.I * (√3 : ℝ) / 8) * ((√3 : ℝ) : ℂ) ^ 2 * Complex.I_sq - (3 / 8 + Complex.I * (√3 : ℝ) / 8) * hs'`.

Use `not_invariant H L hL ((1 + Complex.I * (√3 : ℝ)) / 2) ?_ ?_ (by simp [h]) ?_` and prove the remaining obligations. Simplify using `[Complex.normSq_apply]`. Use the polynomial consequences of the given equalities and inequalities. Simplify using the standard rewrite rules. Rewrite using `[show 6 = 3 * 2 by norm_num, pow_mul, h6]; simp`.
-/
theorem g₂_ne_zero (H : Host E) (L : PeriodPair) (hL : ∀ x, x ∈ L.lattice ↔ ∃ s, x = wC H s) : L.g₂ ≠ 0 := by
  intro h
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hs' : ((√3 : ℝ) : ℂ) ^ 2 = 3 := by exact_mod_cast hs
  have h6 : ((1 + Complex.I * (√3 : ℝ)) / 2) ^ 3 = -1 := by
    linear_combination (3 / 8 + Complex.I * (√3 : ℝ) / 8) * ((√3 : ℝ) : ℂ) ^ 2 * Complex.I_sq
      - (3 / 8 + Complex.I * (√3 : ℝ) / 8) * hs'
  refine not_invariant H L hL ((1 + Complex.I * (√3 : ℝ)) / 2) ?_ ?_ (by simp [h]) ?_
  · simp [Complex.normSq_apply]
    nlinarith
  · simp
  · rw [show 6 = 3 * 2 by norm_num, pow_mul, h6]; simp

/- English proof (translation)
Introduce `h` and use `not_invariant H L hL Complex.I (by simp) (by simp) (by simp) (by simp [h])`.
-/
theorem g₃_ne_zero (H : Host E) (L : PeriodPair) (hL : ∀ x, x ∈ L.lattice ↔ ∃ s, x = wC H s) : L.g₃ ≠ 0 :=
  fun h => not_invariant H L hL Complex.I (by simp) (by simp) (by simp) (by simp [h])

/- English proof (translation)
Establish `h2` using `g₂_ne_zero H L hL`. Establish `h3` using `g₃_ne_zero H L hL`. Establish `hD` using `g₂_cube_sub_g₃_sq_ne_zero L`. Use `set lam := L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) with hlam`. Establish `hlam0 : lam ≠ 0` using `div_ne_zero (mul_ne_zero h2 h3) hD`.

Set `R : Subfield ℂ` to `RingHom.eqLocusField (τ : ℂ →+* ℂ) (RingHom.id ℂ)`. Set `j : R` to `⟨_, hj⟩`. Establish `hjv : (j : ℂ) = L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)` using `rfl`. Set `W : WeierstrassCurve R` to `⟨0, 0, 0, -(j * ((j - 1) / 27)) / 4, -(j * ((j - 1) / 27) ^ 2) / 4⟩`. Establish `hb : W.b₂ = 0` using `by simp [W, WeierstrassCurve.b₂]`.

Establish `h4 : R.subtype W.c₄ = 12 * (lam ^ 2 * L.g₂)`. Rewrite using `[show W.c₄ = 12 * (j * ((j - 1) / 27)) by`. Simplify using `only [W, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]`. Use the proof step `ring]`. Simplify using `only [map_mul, map_div₀, map_sub, map_one, map_ofNat, Subfield.coe_subtype, hjv, hlam]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `h6 : R.subtype W.c₆ = 216 * (lam ^ 3 * L.g₃)`. Rewrite using `[show W.c₆ = 216 * (j * ((j - 1) / 27) ^ 2) by`. Simplify using `only [W, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]`.

Use the proof step `ring]`. Simplify using `only [map_mul, map_div₀, map_sub, map_one, map_pow, map_ofNat, Subfield.coe_subtype, hjv, hlam]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hΔ : IsUnit W.Δ`.

Use `isUnit_iff_ne_zero.2 fun h => mul_ne_zero (pow_ne_zero 6 hlam0) hD ?_` and prove the remaining obligations. Establish `e` using `congrArg R.subtype W.c_relation`. Rewrite `e` using `[h, map_sub, map_pow, map_pow, h4, h6, mul_zero, map_zero]`. Take the linear combination `-e / 1728`. Take `⟨P₀, PC, ψ, ψ₀, u, c, hg, hψ, hu, hc, hΛ, hP⟩` from `exists_model R R.subtype W hΔ hb L lam hlam0 h4 h6`.

Establish `hτ : (τ : ℂ →+* ℂ).comp R.subtype = R.subtype` using `RingHom.ext fun x => x.2`. Establish `hτ' : spMap (τ : ℂ →+* ℂ) ≫ spMap R.subtype = spMap R.subtype` using `by show Spec.map _ ≫ Spec.map _ = Spec.map _`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp, hτ]`. Establish `w : ψ ≫ P₀.A.hom = (PC.A.hom ≫ spMap (τ : ℂ →+* ℂ)) ≫ spMap R.subtype`. Rewrite using `[Category.assoc, hτ', hψ.1.w]`.

Establish `e1 : hψ.1.lift _ _ w ≫ ψ = ψ` using `hψ.1.lift_fst _ _ _`. Set `C : Curve H` to `⟨PC, hg, u, hu, c, hc, fun z => by`. Rewrite using `[hΛ]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨l, hl, rfl⟩`.

Take `⟨m, n, rfl⟩` from `(exists_wC_iff H l).1 ((hL l).1 hl)`. Conclude with `⟨m, n, rfl⟩`. Introduce and unpack `⟨m, n, rfl⟩`. Conclude with `⟨_, (hL _).2 ((exists_wC_iff H _).2 ⟨m, n, rfl⟩), rfl⟩⟩`. Use `⟨C, hψ.1.lift _ _ w, hψ.cancel (hψ.congr hτ'.symm e1.symm) (hψ.1.lift_snd _ _ _), fun z z' e hz' => ?_⟩` and prove the remaining obligations.

Take `⟨P, hP1, a1, a2, a3⟩` from `hP z`. Take `⟨Q, hQ1, b1, b2, b3⟩` from `hP z'`. Establish `e2 : (u.ex fun _ => c * z).left ≫ ψ ≫ ψ₀ = spMap (τ : ℂ →+* ℂ) ≫ (u.ex fun _ => c * z').left ≫ ψ ≫ ψ₀`. Establish `e3` using `congrArg (· ≫ ψ ≫ ψ₀) e`. Simplify using `only [Category.assoc] at e3`.

Rewrite `e3` using `[reassoc_of% e1]`. Conclude with `e3`. Establish `hQ2` using `hQ1.map_comp (τ : ℂ →+* ℂ)`. Rewrite `hQ2` using `[hτ]`. Rewrite `e2` using `[a1, b1, SpecMap_ptHom, ptHom_congr W _ _ _ hτ rfl hQ2, ptHom_eq_ptHom_iff]`.

Take `⟨v, hv⟩` from `e2`. Establish `v0 : τ (Q 0) = v * P 0` using `congrFun hv 0`. Establish `v2 : τ (Q 2) = v * P 2` using `congrFun hv 2`. Establish `hQ0 : Q 2 ≠ 0` using `fun h => hz' (b2.1 h)`. Establish `hQ0' : τ (Q 2) ≠ 0` using `by simpa using hQ0`.

Establish `hP0 : P 2 ≠ 0` using `right_ne_zero_of_mul (v2 ▸ hQ0')`. Use `⟨fun h => hP0 (a2.2 h), mul_right_cancel₀ hQ0' ?_⟩` and prove the remaining obligations. Rewrite using `[← map_mul, b3 hQ0, v0, v2, ← a3 hP0]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_conj (H : Host E) (L : PeriodPair) (hL : ∀ x, x ∈ L.lattice ↔ ∃ s, x = wC H s) (τ : ℂ ≃+* ℂ)
    (hj : τ (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) = L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) :
    ∃ (C : Curve H) (io : C.P.A.left ⟶ C.P.A.left), IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io ∧
      ∀ z z', C.pt z ≫ io = spMap (τ : ℂ →+* ℂ) ≫ C.pt z' → z' ∉ L.lattice → z ∉ L.lattice ∧
        L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * ℘[L] z =
          τ (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * ℘[L] z') := by
  have h2 := g₂_ne_zero H L hL
  have h3 := g₃_ne_zero H L hL
  have hD := g₂_cube_sub_g₃_sq_ne_zero L
  set lam := L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) with hlam
  have hlam0 : lam ≠ 0 := div_ne_zero (mul_ne_zero h2 h3) hD
  let R : Subfield ℂ := RingHom.eqLocusField (τ : ℂ →+* ℂ) (RingHom.id ℂ)
  let j : R := ⟨_, hj⟩
  have hjv : (j : ℂ) = L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := rfl
  let W : WeierstrassCurve R := ⟨0, 0, 0, -(j * ((j - 1) / 27)) / 4, -(j * ((j - 1) / 27) ^ 2) / 4⟩
  have hb : W.b₂ = 0 := by simp [W, WeierstrassCurve.b₂]
  have h4 : R.subtype W.c₄ = 12 * (lam ^ 2 * L.g₂) := by
    rw [show W.c₄ = 12 * (j * ((j - 1) / 27)) by
      simp only [W, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]; ring]
    simp only [map_mul, map_div₀, map_sub, map_one, map_ofNat, Subfield.coe_subtype, hjv, hlam]
    field_simp
    ring
  have h6 : R.subtype W.c₆ = 216 * (lam ^ 3 * L.g₃) := by
    rw [show W.c₆ = 216 * (j * ((j - 1) / 27) ^ 2) by
      simp only [W, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]; ring]
    simp only [map_mul, map_div₀, map_sub, map_one, map_pow, map_ofNat, Subfield.coe_subtype, hjv, hlam]
    field_simp
    ring
  have hΔ : IsUnit W.Δ := by
    refine isUnit_iff_ne_zero.2 fun h => mul_ne_zero (pow_ne_zero 6 hlam0) hD ?_
    have e := congrArg R.subtype W.c_relation
    rw [h, map_sub, map_pow, map_pow, h4, h6, mul_zero, map_zero] at e
    linear_combination -e / 1728
  obtain ⟨P₀, PC, ψ, ψ₀, u, c, hg, hψ, hu, hc, hΛ, hP⟩ := exists_model R R.subtype W hΔ hb L lam hlam0 h4 h6
  have hτ : (τ : ℂ →+* ℂ).comp R.subtype = R.subtype := RingHom.ext fun x => x.2
  have hτ' : spMap (τ : ℂ →+* ℂ) ≫ spMap R.subtype = spMap R.subtype := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hτ]
  have w : ψ ≫ P₀.A.hom = (PC.A.hom ≫ spMap (τ : ℂ →+* ℂ)) ≫ spMap R.subtype := by
    rw [Category.assoc, hτ', hψ.1.w]
  have e1 : hψ.1.lift _ _ w ≫ ψ = ψ := hψ.1.lift_fst _ _ _
  let C : Curve H := ⟨PC, hg, u, hu, c, hc, fun z => by
    rw [hΛ]
    constructor
    · rintro ⟨l, hl, rfl⟩
      obtain ⟨m, n, rfl⟩ := (exists_wC_iff H l).1 ((hL l).1 hl)
      exact ⟨m, n, rfl⟩
    · rintro ⟨m, n, rfl⟩
      exact ⟨_, (hL _).2 ((exists_wC_iff H _).2 ⟨m, n, rfl⟩), rfl⟩⟩
  refine ⟨C, hψ.1.lift _ _ w, hψ.cancel (hψ.congr hτ'.symm e1.symm) (hψ.1.lift_snd _ _ _), fun z z' e hz' => ?_⟩
  obtain ⟨P, hP1, a1, a2, a3⟩ := hP z
  obtain ⟨Q, hQ1, b1, b2, b3⟩ := hP z'
  have e2 : (u.ex fun _ => c * z).left ≫ ψ ≫ ψ₀ = spMap (τ : ℂ →+* ℂ) ≫ (u.ex fun _ => c * z').left ≫ ψ ≫ ψ₀ := by
    have e3 := congrArg (· ≫ ψ ≫ ψ₀) e
    simp only [Category.assoc] at e3
    rw [reassoc_of% e1] at e3
    exact e3
  have hQ2 := hQ1.map_comp (τ : ℂ →+* ℂ)
  rw [hτ] at hQ2
  rw [a1, b1, SpecMap_ptHom, ptHom_congr W _ _ _ hτ rfl hQ2, ptHom_eq_ptHom_iff] at e2
  obtain ⟨v, hv⟩ := e2
  have v0 : τ (Q 0) = v * P 0 := congrFun hv 0
  have v2 : τ (Q 2) = v * P 2 := congrFun hv 2
  have hQ0 : Q 2 ≠ 0 := fun h => hz' (b2.1 h)
  have hQ0' : τ (Q 2) ≠ 0 := by simpa using hQ0
  have hP0 : P 2 ≠ 0 := right_ne_zero_of_mul (v2 ▸ hQ0')
  refine ⟨fun h => hP0 (a2.2 h), mul_right_cancel₀ hQ0' ?_⟩
  rw [← map_mul, b3 hQ0, v0, v2, ← a3 hP0]
  ring

section Points

variable {H : Host E} (C : Curve H)

/- English proof (translation)
Rewrite using `[← C.u.ex_add]`. Use `congr 1`. Use function extensionality and compare the values at `_`. Simplify using `[mul_add]`.
-/
theorem ex_add (z z' : ℂ) :
    (C.u.ex fun _ => C.c * (z + z')) = (C.u.ex fun _ => C.c * z) * C.u.ex fun _ => C.c * z' := by
  rw [← C.u.ex_add]
  congr 1
  funext _
  simp [mul_add]

/- English proof (translation)
Establish `i : Fin C.P.g` using `⟨0, by rw [C.g_eq]; omega⟩`. Establish `e` using `ex_add C (z - z') z'`. Rewrite `e` using `[sub_add_cancel]`. Rewrite using `[exists_wC_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Rewrite `e` using `[Over.OverMorphism.ext h]`. Take `⟨m, n, e'⟩` from `(C.lat _).1 ((C.u.ker _).1 (mul_eq_right.1 e.symm))`. Conclude with `⟨m, n, mul_left_cancel₀ C.c_ne (congrFun e' i)⟩`. Introduce and unpack `⟨m, n, h⟩`.

Rewrite `e` using `[(C.u.ker fun _ => C.c * (z - z')).2 ((C.lat _).2 ⟨m, n, by rw [h]⟩), _root_.one_mul]`. Conclude with `congrArg (·.left) e`.
-/
theorem pt_eq_iff (z z' : ℂ) : C.pt z = C.pt z' ↔ ∃ s, z - z' = wC H s := by
  have i : Fin C.P.g := ⟨0, by rw [C.g_eq]; omega⟩
  have e := ex_add C (z - z') z'
  rw [sub_add_cancel] at e
  rw [exists_wC_iff]
  constructor
  · intro h
    rw [Over.OverMorphism.ext h] at e
    obtain ⟨m, n, e'⟩ := (C.lat _).1 ((C.u.ker _).1 (mul_eq_right.1 e.symm))
    exact ⟨m, n, mul_left_cancel₀ C.c_ne (congrFun e' i)⟩
  · rintro ⟨m, n, h⟩
    rw [(C.u.ker fun _ => C.c * (z - z')).2 ((C.lat _).2 ⟨m, n, by rw [h]⟩), _root_.one_mul] at e
    exact congrArg (·.left) e

/- English proof (translation)
The claim follows from `Over.w (C.u.ex _)`.
-/
theorem pt_hom (z : ℂ) : C.pt z ≫ C.P.A.hom = 𝟙 _ := Over.w (C.u.ex _)

/- English proof (translation)
Establish `e` using `ex_add C z (-z)`. Rewrite `e` using `[add_neg_cancel, (C.u.ker _).2 ((C.lat _).2 ⟨0, 0, by simp⟩)]`. Unfold `Curve.pt`. Rewrite using `[← inv_eq_of_mul_eq_one_right e.symm, Hom.inv_def, Over.comp_left]`.
-/
theorem pt_neg (z : ℂ) : C.pt z ≫ (GrpObj.inv : C.P.A ⟶ C.P.A).left = C.pt (-z) := by
  have e := ex_add C z (-z)
  rw [add_neg_cancel, (C.u.ker _).2 ((C.lat _).2 ⟨0, 0, by simp⟩)] at e
  unfold Curve.pt
  rw [← inv_eq_of_mul_eq_one_right e.symm, Hom.inv_def, Over.comp_left]

variable {C} {τ : ℂ ≃+* ℂ} {io : C.P.A.left ⟶ C.P.A.left}
  (h : IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io)
include h

/- English proof (translation)
Establish `ht : (toUnit (Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ spMap (τ : ℂ →+* ℂ)))).left = spMap (τ : ℂ →+* ℂ)`. Simplify using the standard rewrite rules. Establish `e` using `h.2 _ (C.u.ex fun _ => C.c * z) (C.u.ex fun _ => C.c * w) (toUnit _ ≫ C.u.ex fun _ => C.c * z') (toUnit _ ≫ C.u.ex fun _ => C.c * w') (by rw [Over.comp_left, ht]; exact hz.symm) (by rw [Over.comp_left, ht]; exact hw.symm)`. Rewrite `e` using `[← comp_mul, ← ex_add, ← ex_add, Over.comp_left, ht]`. Conclude with `e.symm`.
-/
theorem conj_add {z w z' w' : ℂ} (hz : C.pt z ≫ io = spMap (τ : ℂ →+* ℂ) ≫ C.pt z')
    (hw : C.pt w ≫ io = spMap (τ : ℂ →+* ℂ) ≫ C.pt w') :
    C.pt (z + w) ≫ io = spMap (τ : ℂ →+* ℂ) ≫ C.pt (z' + w') := by
  have ht : (toUnit (Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ spMap (τ : ℂ →+* ℂ)))).left = spMap (τ : ℂ →+* ℂ) := by
    simp
  have e := h.2 _ (C.u.ex fun _ => C.c * z) (C.u.ex fun _ => C.c * w) (toUnit _ ≫ C.u.ex fun _ => C.c * z')
    (toUnit _ ≫ C.u.ex fun _ => C.c * w') (by rw [Over.comp_left, ht]; exact hz.symm)
    (by rw [Over.comp_left, ht]; exact hw.symm)
  rw [← comp_mul, ← ex_add, ← ex_add, Over.comp_left, ht] at e
  exact e.symm

/- English proof (translation)
The claim follows from `h.1.hom_ext e (by rw [pt_hom, pt_hom])`.
-/
theorem conj_inj {z w : ℂ} (e : C.pt z ≫ io = C.pt w ≫ io) : C.pt z = C.pt w :=
  h.1.hom_ext e (by rw [pt_hom, pt_hom])

/- English proof (translation)
Establish `w : (spMap (τ : ℂ →+* ℂ) ≫ C.pt z') ≫ C.P.A.hom = 𝟙 _ ≫ spMap (τ : ℂ →+* ℂ)`. Rewrite using `[Category.assoc, pt_hom]`. Simplify using the standard rewrite rules. Take `⟨y, hy⟩` from `C.u.ex_onto (Over.homMk (h.1.lift _ _ w) (h.1.lift_snd _ _ w))`. Set `i : Fin C.P.g` to `⟨0, by rw [C.g_eq]; omega⟩`.

Establish `hi : ∀ j : Fin C.P.g, j = i` using `fun j => Fin.ext (by have := j.2; have := C.g_eq; omega)`. Establish `ey : (fun _ => C.c * (y i / C.c)) = y` using `funext fun j => by rw [hi j, mul_div_cancel₀ _ C.c_ne]`. Use `⟨y i / C.c, ?_⟩` and prove the remaining obligations. Unfold `Curve.pt at w hy ⊢`. Rewrite using `[ey, hy]`.

Conclude with `h.1.lift_fst _ _ w`.
-/
theorem exists_conj_pt (z' : ℂ) : ∃ z, C.pt z ≫ io = spMap (τ : ℂ →+* ℂ) ≫ C.pt z' := by
  have w : (spMap (τ : ℂ →+* ℂ) ≫ C.pt z') ≫ C.P.A.hom = 𝟙 _ ≫ spMap (τ : ℂ →+* ℂ) := by
    rw [Category.assoc, pt_hom]; simp
  obtain ⟨y, hy⟩ := C.u.ex_onto (Over.homMk (h.1.lift _ _ w) (h.1.lift_snd _ _ w))
  let i : Fin C.P.g := ⟨0, by rw [C.g_eq]; omega⟩
  have hi : ∀ j : Fin C.P.g, j = i := fun j => Fin.ext (by have := j.2; have := C.g_eq; omega)
  have ey : (fun _ => C.c * (y i / C.c)) = y := funext fun j => by rw [hi j, mul_div_cancel₀ _ C.c_ne]
  refine ⟨y i / C.c, ?_⟩
  unfold Curve.pt at w hy ⊢
  rw [ey, hy]
  exact h.1.lift_fst _ _ w

/- English proof (translation)
Establish `: IsCommMonObj C.P.A` using `C.P.isAb.comm`. Use `⟨?_, fun T x y x₀ y₀ hx hy => ?_⟩` and prove the remaining obligations. Establish `: IsIso (GrpObj.inv : C.P.A ⟶ C.P.A).left` using `inferInstanceAs (IsIso ((Over.forget _).map _))`. Establish `p : IsPullback (GrpObj.inv : C.P.A ⟶ C.P.A).left C.P.A.hom C.P.A.hom (𝟙 _)` using `IsPullback.of_horiz_isIso ⟨by simp⟩`. Simplify using `using p.paste_horiz h.1`.

Rewrite using `[h.2 T x⁻¹ y⁻¹ x₀ y₀ (by rw [hx, Hom.inv_def, Over.comp_left, Category.assoc]) (by rw [hy, Hom.inv_def, Over.comp_left, Category.assoc]), ← mul_inv, Hom.inv_def, Over.comp_left, Category.assoc]`.
-/
theorem isGrpPullback_inv :
    IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) ((GrpObj.inv : C.P.A ⟶ C.P.A).left ≫ io) := by
  have : IsCommMonObj C.P.A := C.P.isAb.comm
  refine ⟨?_, fun T x y x₀ y₀ hx hy => ?_⟩
  · have : IsIso (GrpObj.inv : C.P.A ⟶ C.P.A).left := inferInstanceAs (IsIso ((Over.forget _).map _))
    have p : IsPullback (GrpObj.inv : C.P.A ⟶ C.P.A).left C.P.A.hom C.P.A.hom (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by simp⟩
    simpa using p.paste_horiz h.1
  · rw [h.2 T x⁻¹ y⁻¹ x₀ y₀ (by rw [hx, Hom.inv_def, Over.comp_left, Category.assoc])
      (by rw [hy, Hom.inv_def, Over.comp_left, Category.assoc]), ← mul_inv, Hom.inv_def, Over.comp_left,
      Category.assoc]

end Points

/- English proof (translation)
Introduce `E _ _ _ H L n _ hL τ _ hj hW`. Take `⟨C, io, h, hc⟩` from `exists_conj H L hL τ hj`. Establish `hlam0 : L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) ≠ 0` using `div_ne_zero (mul_ne_zero (g₂_ne_zero H L hL) (g₃_ne_zero H L hL)) (g₂_cube_sub_g₃_sq_ne_zero L)`. Establish `hpt : ∀ z z', C.pt z = C.pt z' ↔ z - z' ∈ L.lattice` using `fun z z' => by rw [pt_eq_iff, hL]`. Set `T : ℂ → ℂ → Prop` to `fun z z' => C.pt z ≫ io = spMap (τ : ℂ →+* ℂ) ≫ C.pt z'`.

Establish `h0 : T 0 0`. Take `⟨z, hz⟩` from `exists_conj_pt h 0`. Establish `e` using `conj_add h hz hz`. Rewrite `e` using `[add_zero, ← hz]`. Establish `e' : C.pt z = C.pt 0` using `by simpa [hpt] using conj_inj h e`.

Conclude with `(congrArg (· ≫ io) e').symm.trans hz`. Establish `key : ∀ a, T (wC H a / n) (wC H a / n) ∨ T (-(wC H a / n)) (wC H a / n)` using `fun a => by`. Distinguish the cases in `ha : wC H a / n ∈ L.lattice`. Establish `e' : C.pt (wC H a / n) = C.pt 0` using `by simpa [hpt] using ha left`. Simplify using `only [T, e']`.

Conclude with `h0`. Take `⟨z, hz⟩` from `exists_conj_pt h (wC H a / n)`. Take `⟨hz', e⟩` from `hc _ _ hz ha`. Rewrite `e` using `[hW a ha]`. Break down `(weierstrassP_eq_iff L hz' ha).1 (mul_left_cancel₀ hlam0 e) with e' | e'` into its components or cases.

Conclude with `.inl ((congrArg (· ≫ io) ((hpt _ _).2 e')).symm.trans hz)`. Conclude with `.inr ((congrArg (· ≫ io) ((hpt z (-(wC H a / n))).2 (by simpa using e'))).symm.trans hz)`. Distinguish the cases in `hA : ∀ a, T (wC H a / n) (wC H a / n)`. Conclude with `⟨C, io, h, fun a => by simpa [wC] using hA a⟩`. Take `⟨a, ha⟩` from `not_forall.1 hA`.

Establish `ha'` using `(key a).resolve_left ha`. Use `⟨C, _, isGrpPullback_inv h, fun b => ?_⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, pt_neg, show wC H (1, 0) = 1 by simp [wC], _root_.one_mul]`. Use `(key b).elim (fun hb => ?_) id` and prove the remaining obligations. Establish `hab` using `conj_add h ha' hb`.

Establish `eab : wC H (a + b) / n = wC H a / n + wC H b / n` using `by simp [wC]; ring`. Apply the tactic sequence `rcases key (a + b) with e | e <;> simp only [T, eab, ← hab] at e`. Establish `e' : C.pt (wC H a / n) = C.pt (-(wC H a / n))`. Rewrite using `[hpt]`. Use `(hpt _ _).1 (conj_inj h e) using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree. Conclude with `absurd ((congrArg (· ≫ io) e').trans ha') ha`. Establish `e' : C.pt (-(wC H b / n)) = C.pt (wC H b / n)`. Rewrite using `[hpt]`. Use `(hpt _ _).1 (conj_inj h e) using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e']`. Conclude with `hb`.
-/
theorem fixesCurve_of_weber : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : PeriodPair) (n : ℕ), 0 < n → (∀ x, x ∈ L.lattice ↔ ∃ s, x = wC H s) → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → τ (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) = L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) → (∀ s, wC H s / n ∉ L.lattice → τ (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP (wC H s / n)) = L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP (wC H s / n)) → FixesCurve H τ n := by
  intro E _ _ _ H L n _ hL τ _ hj hW
  obtain ⟨C, io, h, hc⟩ := exists_conj H L hL τ hj
  have hlam0 : L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) ≠ 0 :=
    div_ne_zero (mul_ne_zero (g₂_ne_zero H L hL) (g₃_ne_zero H L hL)) (g₂_cube_sub_g₃_sq_ne_zero L)
  have hpt : ∀ z z', C.pt z = C.pt z' ↔ z - z' ∈ L.lattice := fun z z' => by rw [pt_eq_iff, hL]
  let T : ℂ → ℂ → Prop := fun z z' => C.pt z ≫ io = spMap (τ : ℂ →+* ℂ) ≫ C.pt z'
  have h0 : T 0 0 := by
    obtain ⟨z, hz⟩ := exists_conj_pt h 0
    have e := conj_add h hz hz
    rw [add_zero, ← hz] at e
    have e' : C.pt z = C.pt 0 := by simpa [hpt] using conj_inj h e
    exact (congrArg (· ≫ io) e').symm.trans hz
  have key : ∀ a, T (wC H a / n) (wC H a / n) ∨ T (-(wC H a / n)) (wC H a / n) := fun a => by
    by_cases ha : wC H a / n ∈ L.lattice
    · have e' : C.pt (wC H a / n) = C.pt 0 := by simpa [hpt] using ha
      left
      simp only [T, e']
      exact h0
    · obtain ⟨z, hz⟩ := exists_conj_pt h (wC H a / n)
      obtain ⟨hz', e⟩ := hc _ _ hz ha
      rw [hW a ha] at e
      rcases (weierstrassP_eq_iff L hz' ha).1 (mul_left_cancel₀ hlam0 e) with e' | e'
      · exact .inl ((congrArg (· ≫ io) ((hpt _ _).2 e')).symm.trans hz)
      · exact .inr ((congrArg (· ≫ io) ((hpt z (-(wC H a / n))).2 (by simpa using e'))).symm.trans hz)
  by_cases hA : ∀ a, T (wC H a / n) (wC H a / n)
  · exact ⟨C, io, h, fun a => by simpa [wC] using hA a⟩
  obtain ⟨a, ha⟩ := not_forall.1 hA
  have ha' := (key a).resolve_left ha
  refine ⟨C, _, isGrpPullback_inv h, fun b => ?_⟩
  rw [← Category.assoc, pt_neg, show wC H (1, 0) = 1 by simp [wC], _root_.one_mul]
  refine (key b).elim (fun hb => ?_) id
  have hab := conj_add h ha' hb
  have eab : wC H (a + b) / n = wC H a / n + wC H b / n := by simp [wC]; ring
  rcases key (a + b) with e | e <;> simp only [T, eab, ← hab] at e
  · have e' : C.pt (wC H a / n) = C.pt (-(wC H a / n)) := by
      rw [hpt]; convert (hpt _ _).1 (conj_inj h e) using 1; ring
    exact absurd ((congrArg (· ≫ io) e').trans ha') ha
  · have e' : C.pt (-(wC H b / n)) = C.pt (wC H b / n) := by
      rw [hpt]; convert (hpt _ _).1 (conj_inj h e) using 1; ring
    rw [e']
    exact hb

end GlobalTheory.CompRat.Weber
