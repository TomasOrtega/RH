import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NBasisLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapMulLeft
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusSubOneWittTensorLatticeSurjectiveFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisDD

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.NygaardExtension

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x x' hx hx' => simp only [smul_add, map_add, hx, hx']`. Consider the case `tmul r u => simp [TensorProduct.smul_tmul']`.
-/
theorem map_incl_smul {O R R' M : Type} [CommRing O] [CommRing R] [CommRing R'] [Algebra O R]
    [Algebra O R'] [AddCommGroup M] [Module O M] (f : R →ₐ[O] R') (a : R) (y : R ⊗[O] M) :
    TensorProduct.map f.toLinearMap (LinearMap.id : M →ₗ[O] M) (a • y) =
      f a • TensorProduct.map f.toLinearMap (LinearMap.id : M →ₗ[O] M) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [smul_add, map_add, hx, hx']
  | tmul r u => simp [TensorProduct.smul_tmul']

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (E : EtTie W RA RW inclR φR gR πA)

/- English proof (translation)
Take `⟨y, rfl⟩` from `hz`. Conclude with `⟨a • y, map_incl_smul inclR a y⟩`.
-/
theorem TAinf_smul (T : LocLat G Qp LL O) (a : RA) {z : TW RW T} (hz : z ∈ TAinf inclR T) :
    inclR a • z ∈ TAinf inclR T := by
  obtain ⟨y, rfl⟩ := hz
  exact ⟨a • y, map_incl_smul inclR a y⟩

/- English proof (translation)
Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨a', x, hx, rfl⟩` from `hz`. Use `Submodule.subset_span ⟨a * a', x, hx, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_smul, map_mul]`.

Consider the case `zero => rw [smul_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `add_mem hx hy`. Consider the case `smul o x _ hx => rw [smul_comm]`.

Conclude with `Submodule.smul_mem _ o hx`.
-/
theorem NAinf_smul (T : LocLat G Qp LL O) (a : RA) {z : TW RW T} (hz : z ∈ NAinf W E T) :
    inclR a • z ∈ NAinf W E T := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a', x, hx, rfl⟩ := hz
    refine Submodule.subset_span ⟨a * a', x, hx, ?_⟩
    rw [smul_smul, map_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul o x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ o hx

/- English proof (translation)
Substitute `hc` using the available equality. Simplify using `only [GlobalTheory.NL.SandArb.map_mulLeft] at h1 h2`. Use `⟨fun z hz => ?_, fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨y, rfl⟩` from `hz`. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => rw [map_zero, smul_zero]`. Conclude with `zero_mem _`. Consider the case `add x x' hx hx' => rw [map_add, smul_add]`. Conclude with `add_mem hx hx'`. Consider the case `tmul r t`.

Establish `e : inclR (E.io W.X) ^ m • TensorProduct.map inclR.toLinearMap LinearMap.id (r ⊗ₜ[O] t) = inclR r • ((inclR (E.io W.X) ^ m) ⊗ₜ[O] t : TW RW T)`. Simplify using `[TensorProduct.smul_tmul', mul_comm]`. Rewrite using `[e]`. Conclude with `NAinf_smul E T r (h2 t)`. Proceed by induction on `hz using Submodule.span_induction with`.

Consider the case `mem z hz`. Take `⟨a, x, hx, rfl⟩` from `hz`. Take `⟨y, hy⟩` from `h1 x hx`. Rewrite using `[smul_comm]`. Conclude with `TAinf_smul T a ⟨y, hy⟩`.

Consider the case `zero => rw [smul_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `add_mem hx hy`. Consider the case `smul o x _ hx => rw [smul_comm]`.

Conclude with `Submodule.smul_mem _ o hx`.
-/
theorem p5inf_of_sand (T : LocLat G Qp LL O) (c : RW) (m : ℕ) (hc : c = inclR (E.io W.X) ^ m)
    (h1 : ∀ x ∈ W.N T, ∃ y : TW RA T, TWincl inclR T y =
        TensorProduct.map (LinearMap.mulLeft O c) LinearMap.id (E.jD T x))
    (h2 : ∀ t : ↥T.L.T, (c ⊗ₜ[O] t : TW RW T) ∈ Submodule.span O {z : TW RW T | ∃ a : RA, ∃ y ∈ W.N T,
        z = TensorProduct.map (LinearMap.mulLeft O (inclR a)) LinearMap.id (E.jD T y)}) :
    wachInfiniteLevelJumpBound W E T m m := by
  subst hc
  simp only [GlobalTheory.NL.SandArb.map_mulLeft] at h1 h2
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · obtain ⟨y, rfl⟩ := hz
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero, smul_zero]; exact zero_mem _
    | add x x' hx hx' => rw [map_add, smul_add]; exact add_mem hx hx'
    | tmul r t =>
      have e : inclR (E.io W.X) ^ m • TensorProduct.map inclR.toLinearMap LinearMap.id (r ⊗ₜ[O] t) =
          inclR r • ((inclR (E.io W.X) ^ m) ⊗ₜ[O] t : TW RW T) := by
        simp [TensorProduct.smul_tmul', mul_comm]
      rw [e]
      exact NAinf_smul E T r (h2 t)
  · induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, x, hx, rfl⟩ := hz
      obtain ⟨y, hy⟩ := h1 x hx
      rw [smul_comm]
      exact TAinf_smul T a ⟨y, hy⟩
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul o x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ o hx

/- English proof (translation)
Take `⟨c, hc⟩` from `GlobalTheory.WachTensor.exists_basis_jD E T ((W.N_base T hT).basis b)`. Establish `hc' : ∀ j, c j = E.jD T (b j : W.DD T)` using `fun j => by`. Rewrite using `[hc, IsBaseChange.basis_apply b (W.N_base T hT) j]`. Both sides reduce to the same expression. Use `⟨⟨r, fun j => (b j : W.DD T), fun j => (b j).2, fun x hx => ?_, fun y => ?_⟩, hφ⟩` and prove the remaining obligations.

Establish `key : ∀ a : Fin r → LetA O n, x = ∑ j, a j • (b j : W.DD T) ↔ (⟨x, hx⟩ : ↥(W.N T)) = ∑ j, a j • b j`. Introduce `a`. Rewrite using `[Subtype.ext_iff]`. Simplify using the standard rewrite rules. Use `⟨fun j => b.repr ⟨x, hx⟩ j, (key _).2 (b.sum_repr ⟨x, hx⟩).symm, fun a ha => ?_⟩` and prove the remaining obligations.

Rewrite using `[(key a).1 ha, b.repr_sum_self]`. Use `⟨fun j => c.repr y j, ?_, fun a ha => ?_⟩` and prove the remaining obligations. Use `show y = _`. Simplify using `only [← hc']`. Conclude with `(c.sum_repr y).symm`.

Establish `ha' : y = ∑ j, a j • c j` using `by simpa only [← hc'] using ha`. Rewrite using `[ha', c.repr_sum_self]`.
-/
theorem etale_comparison_of_wach_basis (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) {r : ℕ}
    (b : Module.Basis (Fin r) (LetA O n) ↥(W.N T))
    (hφ : ∀ y : TW RW T, TWmap φR T y = y ↔ ∃ t : ↥T.L.T, y = (1 : RW) ⊗ₜ[O] t) : p1et W E T := by
  obtain ⟨c, hc⟩ := GlobalTheory.WachTensor.exists_basis_jD E T ((W.N_base T hT).basis b)
  have hc' : ∀ j, c j = E.jD T (b j : W.DD T) := fun j => by
    rw [hc, IsBaseChange.basis_apply b (W.N_base T hT) j]; rfl
  refine ⟨⟨r, fun j => (b j : W.DD T), fun j => (b j).2, fun x hx => ?_, fun y => ?_⟩, hφ⟩
  · have key : ∀ a : Fin r → LetA O n, x = ∑ j, a j • (b j : W.DD T) ↔
        (⟨x, hx⟩ : ↥(W.N T)) = ∑ j, a j • b j := by
      intro a
      rw [Subtype.ext_iff]
      simp
    refine ⟨fun j => b.repr ⟨x, hx⟩ j, (key _).2 (b.sum_repr ⟨x, hx⟩).symm, fun a ha => ?_⟩
    rw [(key a).1 ha, b.repr_sum_self]
  · refine ⟨fun j => c.repr y j, ?_, fun a ha => ?_⟩
    · show y = _
      simp only [← hc']
      exact (c.sum_repr y).symm
    · have ha' : y = ∑ j, a j • c j := by simpa only [← hc'] using ha
      rw [ha', c.repr_sum_self]

end Generic

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `D HW F l _ K s LL h T hT`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Take `⟨b⟩` from `N_basis D HW F l K s LL h T hT`. Conclude with `etale_comparison_of_wach_basis _ T hT b (GlobalTheory.WittTensorFixed.main l K LL T).2.1`. Take `⟨m, h1, h2⟩` from `GlobalTheory.NL.SandArb.sandwich D HW F l K s LL h T hT`.

Conclude with `⟨m, p5inf_of_sand _ T _ m rfl h1 h2⟩`.
-/
theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW),
    p1eL D.loc D.locA HW F := by
  intro D HW F l _ K s LL h T hT
  refine ⟨?_, ?_⟩
  · obtain ⟨b⟩ := N_basis D HW F l K s LL h T hT
    exact etale_comparison_of_wach_basis _ T hT b (GlobalTheory.WittTensorFixed.main l K LL T).2.1
  · obtain ⟨m, h1, h2⟩ := GlobalTheory.NL.SandArb.sandwich D HW F l K s LL h T hT
    exact ⟨m, p5inf_of_sand _ T _ m rfl h1 h2⟩

end GlobalTheory.NL.NygaardExtension
