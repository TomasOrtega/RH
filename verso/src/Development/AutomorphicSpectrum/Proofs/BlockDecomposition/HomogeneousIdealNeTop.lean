import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.GeoNetop

attribute [local instance] MvPolynomial.gradedAlgebra

/- English proof (translation)
Introduce `x hx`. Establish `h0` using `(HomogeneousIdeal.mem_irrelevant_iff _ _).1 hx`. Rewrite `h0` using `[GradedRing.proj_apply]`. Establish `h1 : MvPolynomial.homogeneousComponent 0 x = 0`. Rewrite using `[← MvPolynomial.decomposition.decompose'_apply]`.

Conclude with `h0`. Rewrite `h1` using `[MvPolynomial.homogeneousComponent_zero, MvPolynomial.C_eq_zero]`. Rewrite using `[← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]`. Introduce `m hm`. Establish `hm0 : m ≠ 0`.

Introduce and unpack `rfl`. Conclude with `(MvPolynomial.mem_support_iff.1 hm) h1`. Take `⟨a, ha⟩` from `Finsupp.ne_iff.1 hm0`. Conclude with `⟨a, Set.mem_univ _, ha⟩`.
-/
theorem irrelevant_le_spanX (K : Type) [Field K] (N : ℕ) :
    (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)).toIdeal ≤
      Ideal.span (Set.range (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) K)) := by
  intro x hx
  have h0 := (HomogeneousIdeal.mem_irrelevant_iff _ _).1 hx
  rw [GradedRing.proj_apply] at h0
  have h1 : MvPolynomial.homogeneousComponent 0 x = 0 := by
    rw [← MvPolynomial.decomposition.decompose'_apply]
    exact h0
  rw [MvPolynomial.homogeneousComponent_zero, MvPolynomial.C_eq_zero] at h1
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact (MvPolynomial.mem_support_iff.1 hm) h1
  obtain ⟨a, ha⟩ := Finsupp.ne_iff.1 hm0
  exact ⟨a, Set.mem_univ _, ha⟩

/- English proof (translation)
Establish `h` using `Proj.iSup_basicOpen_eq_top (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) MvPolynomial.X (irrelevant_le_spanX K N)`. Establish `hx : i x ∈ ⨆ j, Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) (MvPolynomial.X j)`. Rewrite using `[h]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨j, hj⟩` from `TopologicalSpace.Opens.mem_iSup.1 hx`.

Conclude with `⟨j, hj⟩`.
-/
theorem exists_chart {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N) (x : X) :
    ∃ j : Fin (N + 1), x ∈ i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j) := by
  have h := Proj.iSup_basicOpen_eq_top (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) MvPolynomial.X
    (irrelevant_le_spanX K N)
  have hx : i x ∈ ⨆ j, Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) (MvPolynomial.X j) := by
    rw [h]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  exact ⟨j, hj⟩

/- English proof (translation)
Apply `HomogeneousLocalization.val_injective` to reduce the goal to its premises. Simplify using `[HomogeneousLocalization.Away.val_mk, Localization.mk_mul, ← map_mul, mul_inv_cancel₀ hc]`.
-/
theorem mk_C_mul_inv {K : Type} [Field K] {N : ℕ} (j : Fin (N + 1)) (c : K) (hc : c ≠ 0)
    (ha : MvPolynomial.C c ∈ grK K N (0 • 1)) (hb : MvPolynomial.C c⁻¹ ∈ grK K N (0 • 1)) :
    HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) 0 (MvPolynomial.C c) ha *
      HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) 0 (MvPolynomial.C c⁻¹) hb = 1 := by
  apply HomogeneousLocalization.val_injective
  simp [HomogeneousLocalization.Away.val_mk, Localization.mk_mul, ← map_mul, mul_inv_cancel₀ hc]

/- English proof (translation)
Establish `hc` using `MvPolynomial.homogeneousComponent_of_mem (m := 0) hf`. Rewrite `hc` using `[MvPolynomial.homogeneousComponent_zero]`. Rewrite using `[MvPolynomial.constantCoeff_eq]`. Distinguish the cases in `hd : 0 = d • 1`. Rewrite `hc` using `[if_pos hd]`.

Establish `hd0 : d = 0` using `by simpa using hd.symm`. Substitute `hd0` using the available equality. Take `⟨c, rfl⟩ : ∃ c, f = MvPolynomial.C c` from `⟨_, hc.symm⟩`. Rewrite using `[MvPolynomial.coeff_zero_C]`. Assume the negation of the conclusion as `hne`.

Take `⟨x⟩` from `hX`. Take `⟨j, hj⟩` from `exists_chart i x`. Use `haveI : Nonempty (i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j)) := ⟨⟨x, hj⟩⟩`. Use `haveI := Scheme.component_nontrivial X (i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j))`. Establish `hb : MvPolynomial.C c⁻¹ ∈ grK K N (0 • 1)`.

Simplify using `using MvPolynomial.isHomogeneous_C (Fin (N + 1)) c⁻¹`. Establish `e` using `congrArg (evV i (MvPolynomial.X j) _ le_rfl) (mk_C_mul_inv j c hne hf hb)`. Rewrite `e` using `[map_mul, map_one, h0 j, zero_mul]`. Conclude with `zero_ne_one e`. Rewrite `hc` using `[if_neg hd, MvPolynomial.C_eq_zero]`.

Conclude with `hc`.
-/
theorem constantCoeff_gen {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N) (hX : Nonempty X)
    {f : MvPolynomial (Fin (N + 1)) K} (d : ℕ) (hf : f ∈ grK K N (d • 1))
    (h0 : ∀ j : Fin (N + 1), evV i (MvPolynomial.X j) (i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j)) le_rfl
      (HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) d f hf) = 0) :
    MvPolynomial.constantCoeff f = 0 := by
  have hc := MvPolynomial.homogeneousComponent_of_mem (m := 0) hf
  rw [MvPolynomial.homogeneousComponent_zero] at hc
  rw [MvPolynomial.constantCoeff_eq]
  by_cases hd : 0 = d • 1
  · rw [if_pos hd] at hc
    have hd0 : d = 0 := by simpa using hd.symm
    subst hd0
    obtain ⟨c, rfl⟩ : ∃ c, f = MvPolynomial.C c := ⟨_, hc.symm⟩
    rw [MvPolynomial.coeff_zero_C]
    by_contra hne
    obtain ⟨x⟩ := hX
    obtain ⟨j, hj⟩ := exists_chart i x
    haveI : Nonempty (i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j)) := ⟨⟨x, hj⟩⟩
    haveI := Scheme.component_nontrivial X (i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j))
    have hb : MvPolynomial.C c⁻¹ ∈ grK K N (0 • 1) := by
      simpa using MvPolynomial.isHomogeneous_C (Fin (N + 1)) c⁻¹
    have e := congrArg (evV i (MvPolynomial.X j) _ le_rfl) (mk_C_mul_inv j c hne hf hb)
    rw [map_mul, map_one, h0 j, zero_mul] at e
    exact zero_ne_one e
  · rw [if_neg hd, MvPolynomial.C_eq_zero] at hc
    exact hc

/- English proof (translation)
Introduce `K _ X N i hX htop`. Establish `hle : homIdeal i ≤ RingHom.ker (MvPolynomial.constantCoeff (σ` using `Fin (N + 1)) (R := K)) := by`. Use `Ideal.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `f ⟨d, hf, h0⟩`. Conclude with `(RingHom.mem_ker).2 (constantCoeff_gen i hX d hf h0)`.

Establish `h1 : (1 : MvPolynomial (Fin (N + 1)) K) ∈ RingHom.ker (MvPolynomial.constantCoeff (σ` using `Fin (N + 1)) (R := K)) := hle (htop ▸ Submodule.mem_top)`. Rewrite `h1` using `[RingHom.mem_ker, map_one]`. Conclude with `one_ne_zero h1`.
-/
theorem homIdeal_ne_top : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N),
    Nonempty X → homIdeal i ≠ ⊤ := by
  intro K _ X N i hX htop
  have hle : homIdeal i ≤ RingHom.ker (MvPolynomial.constantCoeff (σ := Fin (N + 1)) (R := K)) := by
    refine Ideal.span_le.2 ?_
    rintro f ⟨d, hf, h0⟩
    exact (RingHom.mem_ker).2 (constantCoeff_gen i hX d hf h0)
  have h1 : (1 : MvPolynomial (Fin (N + 1)) K) ∈ RingHom.ker (MvPolynomial.constantCoeff (σ := Fin (N + 1)) (R := K)) :=
    hle (htop ▸ Submodule.mem_top)
  rw [RingHom.mem_ker, map_one] at h1
  exact one_ne_zero h1
end GlobalTheory.CompanionTheory.GeoNetop
