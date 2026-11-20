import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult DividedPowers GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DeRham

/- English proof (translation)
Take `⟨n, π, hπ⟩` from `Module.Finite.exists_fin' R M`. Take `⟨s, hs⟩` from `Module.projective_lifting_property π LinearMap.id hπ`. Use `⟨n, fun i ↦ π (Pi.single i 1), fun i ↦ LinearMap.proj i ∘ₗ s, fun c ↦ ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`.

Use extensionality with `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Use `_ = c := LinearMap.congr_fun hs c`.
-/
theorem exists_finite_dualBasis {R : Type} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    ∃ (n : ℕ) (e : Fin n → M) (f : Fin n → Module.Dual R M), ∀ c, ∑ i, f i c • e i = c := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  refine ⟨n, fun i ↦ π (Pi.single i 1), fun i ↦ LinearMap.proj i ∘ₗ s, fun c ↦ ?_⟩
  calc ∑ i, (LinearMap.proj i ∘ₗ s) c • π (Pi.single i 1)
      = π (∑ i, s c i • Pi.single i (1 : R)) := by simp [map_sum, map_smul]
    _ = π (s c) := by
        congr 1; ext j; simp [Finset.sum_apply, Pi.single_apply]
    _ = c := LinearMap.congr_fun hs c

/- English proof (translation)
Introduce `H F _ _ 𝔠 R R' _ _ σ X X' φ hP m`. Use `letI := σ.toAlgebra`. Take `⟨H1, H2, H3, -, -⟩` from `H`. Take `⟨hbc, hF⟩` from `H3 R X.A _ X.ab X.dim R' X'.A φ hP.grp`. Establish `hm : m.IsBC` using `hbc`.

Establish `hF' : PrimitiveSubmodule X'.A = Submodule.span R' (m.pull '' PrimitiveSubmodule X.A)` using `hF`. Establish `ext' : ∀ y z : HdR X'.A, (∀ c, y (m.pull c) = z (m.pull c)) → y = z`. Introduce `y z h`. Use `LinearMap.ext fun c' ↦ ?_` and prove the remaining obligations. Take `⟨w, rfl⟩` from `hm.2 c'`.

Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r c => rw [liftSemi_tmul, map_smul, map_smul, h c]`. Consider the case `add a b ha hb => rw [map_add, map_add, map_add, ha, hb]`. Take `⟨hfin, hproj, -⟩` from `H1.prim X.ab X.dim`.

Take `⟨n, e, f, hef⟩` from `exists_finite_dualBasis (R := R) (M := primDR X.A)`. Establish `key : ∀ (q : primDR X.A →ₗ[R] primDR X.A) (y' : HdR X'.A), (∀ c, y' (m.pull (q c)) = y' (m.pull c)) → y' ∈ Submodule.span R' {x' | ∃ x, (∃ d : HdR X.A, x = d ∘ₗ q) ∧ m.Corr x x'}`. Introduce `q y' hy`. Use `choose g hg using fun i ↦ hm.exists ((f i) ∘ₗ q)`. Establish `hy' : y' = ∑ i, y' (m.pull (e i)) • g i`.

Use `ext' _ _ fun c ↦ ?_` and prove the remaining obligations. Rewrite using `[LinearMap.sum_apply]`. Simplify using `only [LinearMap.smul_apply, smul_eq_mul]`. Establish `hgc : ∀ i, g i (m.pull c) = σ ((f i ∘ₗ q) c)` using `fun i ↦ hg i c`. Simplify using `only [hgc]`.

Rewrite using `[← hy c]`. Use `conv_lhs => rw [← hef (q c)]`. Rewrite using `[map_sum, map_sum]`. Use `Finset.sum_congr rfl fun i _ ↦ ?_` and prove the remaining obligations. Rewrite using `[LinearMap.map_smulₛₗ, map_smul, smul_eq_mul, mul_comm]`.

Both sides reduce to the same expression. Rewrite using `[hy']`. Conclude with `Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨f i, rfl⟩, hg i⟩)`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `eq_top_iff.2 fun y' _ ↦ ?_` and prove the remaining obligations.

Use `Submodule.span_mono ?_ (key LinearMap.id y' fun c ↦ rfl)` and prove the remaining obligations. Introduce and unpack `x' ⟨x, -, hx⟩`. Conclude with `⟨x, hx⟩`. Introduce `y' hy'`. Take `⟨-, ⟨N, hN⟩, -⟩` from `H2 R X.A _ X.ab X.dim`.

Set `P : primDR X.A →ₗ[R] primDR X.A` to `N.projection (PrimitiveSubmodule X.A) hN.symm`. Establish `hP0 : ∀ c ∈ PrimitiveSubmodule X.A, P c = 0` using `fun c hc ↦ Submodule.projection_apply_of_mem_right hN.symm hc`. Establish `hP1 : ∀ c, c - P c ∈ PrimitiveSubmodule X.A` using `fun c ↦ by`. Take `⟨u, v, huv, -⟩` from `Submodule.existsUnique_add_of_isCompl hN c`. Establish `hv : P v = v` using `Submodule.projection_apply_of_mem_left hN.symm v.2`.

Rewrite using `[← huv, map_add, hP0 _ u.2, hv, zero_add, add_sub_cancel_right]`. Conclude with `u.2`. Establish `hy0` using `(Submodule.mem_dualAnnihilator _).1 hy'`. Use `Submodule.span_mono ?_ (key P y' fun c ↦ ?_)` and prove the remaining obligations. Introduce and unpack `x' ⟨x, ⟨d, rfl⟩, hx⟩`.

Use `⟨_, (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ ?_, hx⟩` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, hP0 c hc, map_zero]`. Establish `h0 : y' (m.pull (c - P c)) = 0` using `hy0 _ (hF' ▸ Submodule.subset_span ⟨_, hP1 c, rfl⟩)`. Rewrite `h0` using `[map_sub, map_sub, sub_eq_zero]`. Conclude with `h0.symm`.

Introduce `x x' hx hxx'`. Use `(Submodule.mem_dualAnnihilator _).2 fun w hw ↦ ?_` and prove the remaining obligations. Rewrite `hw` using `[hF']`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem w hw`.

Take `⟨c, hc, rfl⟩` from `hw`. Rewrite using `[hxx' c, (Submodule.mem_dualAnnihilator _).1 hx c hc, map_zero]`. Consider the case `zero => exact map_zero _`. Consider the case `add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]`. Consider the case `smul r a _ ha => rw [map_smul, ha, smul_zero]`.
-/
theorem span_corr_baseChange : GlobalTheory.Published.AbelianDeRham → ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}
    {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {φ : X'.A.left ⟶ X.A.left}, X'.IsPullBy X (spMap σ) φ →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X.A (dp0 R') (𝟙 _) X'.A σ (spMap σ) φ),
    Submodule.span R' {x' | ∃ x, m.Corr x x'} = ⊤ ∧
      Fil X'.A ≤ Submodule.span R' {x' | ∃ x ∈ Fil X.A, m.Corr x x'} ∧
      ∀ x x', x ∈ Fil X.A → m.Corr x x' → x' ∈ Fil X'.A := by
  intro H F _ _ 𝔠 R R' _ _ σ X X' φ hP m
  letI := σ.toAlgebra
  obtain ⟨H1, H2, H3, -, -⟩ := H
  obtain ⟨hbc, hF⟩ := H3 R X.A _ X.ab X.dim R' X'.A φ hP.grp
  have hm : m.IsBC := hbc
  have hF' : PrimitiveSubmodule X'.A = Submodule.span R' (m.pull '' PrimitiveSubmodule X.A) := hF
  have ext' : ∀ y z : HdR X'.A, (∀ c, y (m.pull c) = z (m.pull c)) → y = z := by
    intro y z h
    refine LinearMap.ext fun c' ↦ ?_
    obtain ⟨w, rfl⟩ := hm.2 c'
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul r c => rw [liftSemi_tmul, map_smul, map_smul, h c]
    | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
  obtain ⟨hfin, hproj, -⟩ := H1.prim X.ab X.dim
  obtain ⟨n, e, f, hef⟩ := exists_finite_dualBasis (R := R) (M := primDR X.A)
  have key : ∀ (q : primDR X.A →ₗ[R] primDR X.A) (y' : HdR X'.A),
      (∀ c, y' (m.pull (q c)) = y' (m.pull c)) →
      y' ∈ Submodule.span R' {x' | ∃ x, (∃ d : HdR X.A, x = d ∘ₗ q) ∧ m.Corr x x'} := by
    intro q y' hy
    choose g hg using fun i ↦ hm.exists ((f i) ∘ₗ q)
    have hy' : y' = ∑ i, y' (m.pull (e i)) • g i := by
      refine ext' _ _ fun c ↦ ?_
      rw [LinearMap.sum_apply]
      simp only [LinearMap.smul_apply, smul_eq_mul]
      have hgc : ∀ i, g i (m.pull c) = σ ((f i ∘ₗ q) c) := fun i ↦ hg i c
      simp only [hgc]
      rw [← hy c]
      conv_lhs => rw [← hef (q c)]
      rw [map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [LinearMap.map_smulₛₗ, map_smul, smul_eq_mul, mul_comm]
      rfl
    rw [hy']
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _
      (Submodule.subset_span ⟨_, ⟨f i, rfl⟩, hg i⟩)
  refine ⟨?_, ?_, ?_⟩
  · refine eq_top_iff.2 fun y' _ ↦ ?_
    refine Submodule.span_mono ?_ (key LinearMap.id y' fun c ↦ rfl)
    rintro x' ⟨x, -, hx⟩
    exact ⟨x, hx⟩
  · intro y' hy'
    obtain ⟨-, ⟨N, hN⟩, -⟩ := H2 R X.A _ X.ab X.dim
    let P : primDR X.A →ₗ[R] primDR X.A := N.projection (PrimitiveSubmodule X.A) hN.symm
    have hP0 : ∀ c ∈ PrimitiveSubmodule X.A, P c = 0 := fun c hc ↦
      Submodule.projection_apply_of_mem_right hN.symm hc
    have hP1 : ∀ c, c - P c ∈ PrimitiveSubmodule X.A := fun c ↦ by
      obtain ⟨u, v, huv, -⟩ := Submodule.existsUnique_add_of_isCompl hN c
      have hv : P v = v := Submodule.projection_apply_of_mem_left hN.symm v.2
      rw [← huv, map_add, hP0 _ u.2, hv, zero_add, add_sub_cancel_right]
      exact u.2
    have hy0 := (Submodule.mem_dualAnnihilator _).1 hy'
    refine Submodule.span_mono ?_ (key P y' fun c ↦ ?_)
    · rintro x' ⟨x, ⟨d, rfl⟩, hx⟩
      refine ⟨_, (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ ?_, hx⟩
      rw [LinearMap.comp_apply, hP0 c hc, map_zero]
    · have h0 : y' (m.pull (c - P c)) = 0 :=
        hy0 _ (hF' ▸ Submodule.subset_span ⟨_, hP1 c, rfl⟩)
      rw [map_sub, map_sub, sub_eq_zero] at h0
      exact h0.symm
  · intro x x' hx hxx'
    refine (Submodule.mem_dualAnnihilator _).2 fun w hw ↦ ?_
    rw [hF'] at hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨c, hc, rfl⟩ := hw
      rw [hxx' c, (Submodule.mem_dualAnnihilator _).1 hx c hc, map_zero]
    | zero => exact map_zero _
    | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
    | smul r a _ ha => rw [map_smul, ha, smul_zero]

end GlobalTheory.DeRham
