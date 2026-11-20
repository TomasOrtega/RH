import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PointsAddCommMonoidStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CharacterMemLatticeOfComul
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SeriesTwoPointsEqSumMulStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ hv _ _ d F hFH k κ hmul hone`. Take `⟨inst, hsum, hzero, hkill⟩` from `GlobalTheory.T.exists_addCommMonoid_algHom_powerSeries_fgLaw p C v O hv d F`. Use `letI := inst`. Take `⟨hfree, hfin, -⟩` from `hFH k`. Establish `hinj : Function.Injective (algebraMap O C)` using `hv.hom_inj`.

Use `haveI : IsDomain O := hinj.isDomain (algebraMap O C)`. Use `set J : Ideal (PS O 1 d) := Ideal.span (Set.range (mulF F.F (p ^ k))) with hJ`. Set `N : AddSubmonoid (PS O 1 d →ₐ[O] O)` to `{ carrier := {φ | (p ^ k) • φ = 0} zero_mem' := nsmul_zero _ add_mem' := by`. Introduce `a b ha hb`. Simplify using `only [Set.mem_setOf_eq] at ha hb ⊢`.

Rewrite using `[nsmul_add, ha, hb, add_zero] }`. Establish `hN : ∀ n : N, Killed F.F (p ^ k) n.1` using `fun n => (hkill _ _).1 n.2`. Establish `hNJ : ∀ n : N, ∀ u ∈ J, n.1 u = 0`. Introduce `n u hu`. Establish `hle : J ≤ RingHom.ker n.1`.

Rewrite using `[hJ, Ideal.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `hN n j`. Conclude with `hle hu`. Set `L : N → (QF F.F (p ^ k) →ₐ[O] O)` to `fun n => Ideal.Quotient.liftₐ J n.1 (hNJ n)`.

Establish `hL : ∀ (n : N) (u : PS O 1 d), L n (Ideal.Quotient.mk J u) = n.1 u` using `fun n u => rfl`. Establish `hLinj : Function.Injective L`. Introduce `a b hab`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `AlgHom.ext` to reduce the goal to its premises.

Introduce `u`. Rewrite using `[← hL, ← hL, hab]`. Use `haveI : Finite N := Finite.of_injective L hLinj`. Set `T : QF F.F (p ^ k) →ₗ[O] (N → C)` to `LinearMap.pi fun n => (Algebra.linearMap O C).comp (L n).toLinearMap`. Establish `hmem : ∀ f : N → C, f ∈ LinearMap.range T ↔ ∃ u : PS O 1 d, ∀ n : N, algebraMap O C (n.1 u) = f n`.

Introduce `f`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨q, rfl⟩`. Take `⟨u, rfl⟩` from `Ideal.Quotient.mk_surjective q`. Conclude with `⟨u, fun n => rfl⟩`.

Introduce and unpack `⟨u, hu⟩`. Conclude with `⟨Ideal.Quotient.mk J u, funext hu⟩`. Establish `hfg : (LinearMap.range T).FG` using `Module.Finite.iff_fg.1 inferInstance`. Establish `hspan : Submodule.span C ((LinearMap.range T : Submodule O (N → C)) : Set (N → C)) = ⊤`. Set `e : N → (PS O 1 d →* C)` to `fun n => ((algebraMap O C).comp (n.1 : PS O 1 d →+* O) : PS O 1 d →+* C).toMonoidHom`.

Establish `he : Function.Injective e`. Introduce `a b hab`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `AlgHom.ext` to reduce the goal to its premises. Introduce `u`.

Conclude with `hinj (DFunLike.congr_fun hab u)`. Establish `hli : LinearIndependent C (fun n : N => (e n : PS O 1 d → C))` using `(linearIndependent_monoidHom (PS O 1 d) C).comp e he`. Establish `htop` using `span_flip_eq_top_iff_linearIndependent.2 hli`. Rewrite using `[eq_top_iff, ← htop]`. Apply `Submodule.span_mono` to reduce the goal to its premises.

Introduce and unpack `_ ⟨u, rfl⟩`. Conclude with `(hmem _).2 ⟨u, fun n => rfl⟩`. Establish `key` using `GlobalTheory.character_mem_lattice_of_comul C v O hv N (LinearMap.range T) hfg hspan ?_ ?_ (fun n => κ n.1) (hone _ hzero) (fun x y => hmul _ _ _ (hN x) (hN y) ((hsum _ _ _).2 rfl))`. Take `⟨u, hu⟩` from `(hmem _).1 key`. Conclude with `⟨u, fun φ hφ => hu ⟨φ, (hkill _ _).2 hφ⟩⟩`.

Introduce `f hf`. Take `⟨u, hu⟩` from `(hmem _).1 hf`. Take `⟨m, g, h, hgh⟩` from `GlobalTheory.T.exists_sum_mul_eval_two_points_of_free_finite_quotient p C v O hv d J hfree hfin (ev (n := 2) ![F.F] u)`. Use `⟨m, fun i n => algebraMap O C (n.1 (g i)), fun i n => algebraMap O C (n.1 (h i)), fun i => (hmem _).2 ⟨g i, fun n => rfl⟩, fun i => (hmem _).2 ⟨h i, fun n => rfl⟩, ?_⟩` and prove the remaining obligations. Introduce `x y`.

Take `⟨Φ, h0, h1, h2⟩` from `(hsum x.1 y.1 (x + y).1).2 rfl`. Rewrite using `[← hu, ← h2, hgh Φ x.1 y.1 h0 h1 (hNJ x) (hNJ y), map_sum]`. Simplify using `only [map_mul]`. Introduce `f hf`. Take `⟨u, hu⟩` from `(hmem _).1 hf`.

Conclude with `⟨_, hu 0⟩`.
-/
theorem character_on_torsion_points_eq_series : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (F : FGLaw O d), FH p F.F → ∀ (k : ℕ) (κ : (PS O 1 d →ₐ[O] O) → C), (∀ φ φ' ψ, Killed F.F (p ^ k) φ → Killed F.F (p ^ k) φ' → IsSum F.F φ φ' ψ → κ ψ = κ φ * κ φ') → (∀ φ, (∀ f, φ f = MvPowerSeries.constantCoeff f) → κ φ = 1) → ∃ u : PS O 1 d, ∀ φ, Killed F.F (p ^ k) φ → algebraMap O C (φ u) = κ φ := by
  intro p _ C _ _ _ v O _ _ hv _ _ d F hFH k κ hmul hone
  obtain ⟨inst, hsum, hzero, hkill⟩ := GlobalTheory.T.exists_addCommMonoid_algHom_powerSeries_fgLaw p C v O hv d F
  letI := inst
  obtain ⟨hfree, hfin, -⟩ := hFH k
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  haveI : IsDomain O := hinj.isDomain (algebraMap O C)
  set J : Ideal (PS O 1 d) := Ideal.span (Set.range (mulF F.F (p ^ k))) with hJ
  let N : AddSubmonoid (PS O 1 d →ₐ[O] O) :=
    { carrier := {φ | (p ^ k) • φ = 0}
      zero_mem' := nsmul_zero _
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [nsmul_add, ha, hb, add_zero] }
  have hN : ∀ n : N, Killed F.F (p ^ k) n.1 := fun n => (hkill _ _).1 n.2
  have hNJ : ∀ n : N, ∀ u ∈ J, n.1 u = 0 := by
    intro n u hu
    have hle : J ≤ RingHom.ker n.1 := by
      rw [hJ, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact hN n j
    exact hle hu
  let L : N → (QF F.F (p ^ k) →ₐ[O] O) := fun n => Ideal.Quotient.liftₐ J n.1 (hNJ n)
  have hL : ∀ (n : N) (u : PS O 1 d), L n (Ideal.Quotient.mk J u) = n.1 u := fun n u => rfl
  have hLinj : Function.Injective L := by
    intro a b hab
    apply Subtype.ext
    apply AlgHom.ext
    intro u
    rw [← hL, ← hL, hab]
  haveI : Finite N := Finite.of_injective L hLinj
  let T : QF F.F (p ^ k) →ₗ[O] (N → C) :=
    LinearMap.pi fun n => (Algebra.linearMap O C).comp (L n).toLinearMap
  have hmem : ∀ f : N → C, f ∈ LinearMap.range T ↔
      ∃ u : PS O 1 d, ∀ n : N, algebraMap O C (n.1 u) = f n := by
    intro f
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective q
      exact ⟨u, fun n => rfl⟩
    · rintro ⟨u, hu⟩
      exact ⟨Ideal.Quotient.mk J u, funext hu⟩
  have hfg : (LinearMap.range T).FG := Module.Finite.iff_fg.1 inferInstance
  have hspan : Submodule.span C ((LinearMap.range T : Submodule O (N → C)) : Set (N → C)) = ⊤ := by
    let e : N → (PS O 1 d →* C) := fun n =>
      ((algebraMap O C).comp (n.1 : PS O 1 d →+* O) : PS O 1 d →+* C).toMonoidHom
    have he : Function.Injective e := by
      intro a b hab
      apply Subtype.ext
      apply AlgHom.ext
      intro u
      exact hinj (DFunLike.congr_fun hab u)
    have hli : LinearIndependent C (fun n : N => (e n : PS O 1 d → C)) :=
      (linearIndependent_monoidHom (PS O 1 d) C).comp e he
    have htop := span_flip_eq_top_iff_linearIndependent.2 hli
    rw [eq_top_iff, ← htop]
    apply Submodule.span_mono
    rintro _ ⟨u, rfl⟩
    exact (hmem _).2 ⟨u, fun n => rfl⟩
  have key := GlobalTheory.character_mem_lattice_of_comul C v O hv N (LinearMap.range T) hfg hspan ?_ ?_
    (fun n => κ n.1) (hone _ hzero)
    (fun x y => hmul _ _ _ (hN x) (hN y) ((hsum _ _ _).2 rfl))
  · obtain ⟨u, hu⟩ := (hmem _).1 key
    exact ⟨u, fun φ hφ => hu ⟨φ, (hkill _ _).2 hφ⟩⟩
  · intro f hf
    obtain ⟨u, hu⟩ := (hmem _).1 hf
    obtain ⟨m, g, h, hgh⟩ := GlobalTheory.T.exists_sum_mul_eval_two_points_of_free_finite_quotient p C v O hv d J hfree hfin (ev (n := 2) ![F.F] u)
    refine ⟨m, fun i n => algebraMap O C (n.1 (g i)), fun i n => algebraMap O C (n.1 (h i)),
      fun i => (hmem _).2 ⟨g i, fun n => rfl⟩, fun i => (hmem _).2 ⟨h i, fun n => rfl⟩, ?_⟩
    intro x y
    obtain ⟨Φ, h0, h1, h2⟩ := (hsum x.1 y.1 (x + y).1).2 rfl
    rw [← hu, ← h2, hgh Φ x.1 y.1 h0 h1 (hNJ x) (hNJ y), map_sum]
    simp only [map_mul]
  · intro f hf
    obtain ⟨u, hu⟩ := (hmem _).1 hf
    exact ⟨_, hu 0⟩

end GlobalTheory
