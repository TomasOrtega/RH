import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UniformModerateGrowthLevel
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RealSmoothQuadratic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HolomorphicLowestType

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefLift

variable {D : D7}

def lift {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (ν : Measure (GA D S)) (𝓕 : Set (GA D S))
    (Φ : GA D S → WO S T → ℂ) : GA D T → ℂ :=
  fun g => ∫ h in 𝓕, thetaKO om h g (Φ h) ∂ν

def along (S T : HSp D) (ξ : Fin T.rank → D.host.E) (a : Fin S.rank → AE D) : WO S T :=
  Matrix.vecMulVec (fun i => incA D (ξ i)) a

open Classical in

def KEquiv (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (U : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.KMap M) : Prop :=
  ∀ τ, ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (e : ∀ τ', lowT M τ') (w : lowT M τ),
    ((w : M.sm τ) : M.H τ) = M.σ τ k ((e τ : M.sm τ) : M.H τ) →
      U (Function.update e τ w) = rTr V (atTau θ V τ ((M.fr τ)⁻¹ * k * M.fr τ)) (U e)

variable {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}

/- English proof (translation)
Establish `hU` using `(M.ds τ).2.2.1`. Set `P : Submodule ℂ (M.H τ)` to `Submodule.span ℂ {y | ∃ k ∈ Formalism.REAL.Kset (M.ε τ), y = M.σ τ k ((v : M.sm τ) : M.H τ)}`. Establish `hvL : ((v : M.sm τ) : M.H τ) ∈ lowKSub (M.ε τ) (M.lam τ) (M.σ τ)` using `v.2`. Establish `hPle : P ≤ lowKSub (M.ε τ) (M.lam τ) (M.σ τ)` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨k, hk, rfl⟩`.

Conclude with `(h2 τ).2.1 k hk _ hvL)`. Establish `hmul : ∀ a ∈ Formalism.REAL.Kset (M.ε τ), ∀ b ∈ Formalism.REAL.Kset (M.ε τ), a * b ∈ Formalism.REAL.Kset (M.ε τ)`. Introduce `a ha b hb`. Use `⟨mul_mem ha.1 hb.1, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_assoc, hb.2, ← Matrix.mul_assoc, ha.2, Matrix.mul_assoc]`.

Establish `hone : (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ Formalism.REAL.Kset (M.ε τ)` using `⟨one_mem _, by simp⟩`. Establish `hst : IsKStableOn (M.ε τ) (M.σ τ) P`. Introduce `g hg y hy`. Use `Submodule.span_induction (p := fun y _ => M.σ τ g y ∈ P) ?_ ?_ ?_ ?_ hy` and prove the remaining obligations. Introduce and unpack `_ ⟨k, hk, rfl⟩`.

Use `Submodule.subset_span ⟨g * k, hmul g hg k hk, ?_⟩` and prove the remaining obligations. Rewrite using `[hU.1.2 _ (kset_uj hg) _ (kset_uj hk)]`. Both sides reduce to the same expression. Rewrite using `[map_zero]`. Conclude with `P.zero_mem`.

Introduce `x y _ _ hx hy`. Rewrite using `[map_add]`. Conclude with `P.add_mem hx hy`. Introduce `a x _ hx`. Rewrite using `[map_smul]`.

Conclude with `P.smul_mem a hx`. Establish `hP : P = lowKSub (M.ε τ) (M.lam τ) (M.σ τ)`. Use `((h2 τ).2.2.1 P hPle hst).resolve_left fun h0 => hv ?_` and prove the remaining obligations. Establish `: M.σ τ 1 ((v : M.sm τ) : M.H τ) ∈ P` using `Submodule.subset_span ⟨1, hone, rfl⟩`. Rewrite `this` using `[h0, hU.1.1]`.

Conclude with `Subtype.ext (Subtype.ext this)`. Rewrite using `[eq_top_iff]`. Introduce `u _`. Establish `hu : ((u : M.sm τ) : M.H τ) ∈ P` using `hP ▸ u.2`. Establish `key : ∀ y (hy : y ∈ P), (⟨⟨y, h1 τ (hPle hy)⟩, hPle hy⟩ : lowT M τ) ∈ N`.

Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨k, hk, e⟩` from `hy`. Conclude with `hN k hk _ e`.

Consider the case `zero => exact N.zero_mem`. Consider the case `add x y _ _ hx hy => exact N.add_mem hx hy`. Consider the case `smul a x _ hx => exact N.smul_mem a hx`. Conclude with `key _ hu`.
-/
theorem eq_top_of_translates (h1 : LowSm M) (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) (τ : D.what₂.Tau) (N : Submodule ℂ (lowT M τ))
    (v : lowT M τ) (hv : v ≠ 0)
    (hN : ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ u : lowT M τ,
      ((u : M.sm τ) : M.H τ) = M.σ τ k ((v : M.sm τ) : M.H τ) → u ∈ N) : N = ⊤ := by
  have hU := (M.ds τ).2.2.1
  let P : Submodule ℂ (M.H τ) := Submodule.span ℂ {y | ∃ k ∈ Formalism.REAL.Kset (M.ε τ), y = M.σ τ k ((v : M.sm τ) : M.H τ)}
  have hvL : ((v : M.sm τ) : M.H τ) ∈ lowKSub (M.ε τ) (M.lam τ) (M.σ τ) := v.2
  have hPle : P ≤ lowKSub (M.ε τ) (M.lam τ) (M.σ τ) := Submodule.span_le.2 (by
    rintro _ ⟨k, hk, rfl⟩
    exact (h2 τ).2.1 k hk _ hvL)
  have hmul : ∀ a ∈ Formalism.REAL.Kset (M.ε τ), ∀ b ∈ Formalism.REAL.Kset (M.ε τ), a * b ∈ Formalism.REAL.Kset (M.ε τ) := by
    intro a ha b hb
    refine ⟨mul_mem ha.1 hb.1, ?_⟩
    rw [Matrix.mul_assoc, hb.2, ← Matrix.mul_assoc, ha.2, Matrix.mul_assoc]
  have hone : (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ Formalism.REAL.Kset (M.ε τ) := ⟨one_mem _, by simp⟩
  have hst : IsKStableOn (M.ε τ) (M.σ τ) P := by
    intro g hg y hy
    refine Submodule.span_induction (p := fun y _ => M.σ τ g y ∈ P) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨k, hk, rfl⟩
      refine Submodule.subset_span ⟨g * k, hmul g hg k hk, ?_⟩
      rw [hU.1.2 _ (kset_uj hg) _ (kset_uj hk)]
      rfl
    · rw [map_zero]; exact P.zero_mem
    · intro x y _ _ hx hy; rw [map_add]; exact P.add_mem hx hy
    · intro a x _ hx; rw [map_smul]; exact P.smul_mem a hx
  have hP : P = lowKSub (M.ε τ) (M.lam τ) (M.σ τ) := by
    refine ((h2 τ).2.2.1 P hPle hst).resolve_left fun h0 => hv ?_
    have : M.σ τ 1 ((v : M.sm τ) : M.H τ) ∈ P := Submodule.subset_span ⟨1, hone, rfl⟩
    rw [h0, hU.1.1] at this
    exact Subtype.ext (Subtype.ext this)
  rw [eq_top_iff]
  intro u _
  have hu : ((u : M.sm τ) : M.H τ) ∈ P := hP ▸ u.2
  have key : ∀ y (hy : y ∈ P), (⟨⟨y, h1 τ (hPle hy)⟩, hPle hy⟩ : lowT M τ) ∈ N := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, hk, e⟩ := hy
      exact hN k hk _ e
    | zero => exact N.zero_mem
    | add x y _ _ hx hy => exact N.add_mem hx hy
    | smul a x _ hx => exact N.smul_mem a hx
  exact key _ hu

open Classical in

/- English proof (translation)
Establish `key : ∀ s : Finset D.what₂.Tau, B (s.piecewise v v₀) ∈ N`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using hB`. Consider the case `insert τ s hτ ih`.

Establish `e0 : s.piecewise v v₀ τ = v₀ τ` using `Finset.piecewise_eq_of_notMem _ _ _ hτ`. Use `eq_top_of_translates h1 h2 τ (N.comap (B.toLinearMap (s.piecewise v v₀) τ)) (v₀ τ) (h0 τ) fun k hk u hu => hK τ k hk _ u (by rw [e0]; exact hu) ih` as an intermediate fact. Rewrite using `[Finset.piecewise_insert]`. Conclude with `(this.ge Submodule.mem_top : v τ ∈ N.comap (B.toLinearMap (s.piecewise v v₀) τ))`. Simplify using `using key Finset.univ`.
-/
theorem mem_of_translates (h1 : LowSm M) (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) {Y : Type} [AddCommGroup Y] [Module ℂ Y]
    (B : MultilinearMap ℂ (fun τ => lowT M τ) Y) (N : Submodule ℂ Y) (v₀ : ∀ τ, lowT M τ) (h0 : ∀ τ, v₀ τ ≠ 0)
    (hB : B v₀ ∈ N)
    (hK : ∀ τ, ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (v : ∀ ρ, lowT M ρ) (u : lowT M τ),
      ((u : M.sm τ) : M.H τ) = M.σ τ k ((v τ : M.sm τ) : M.H τ) → B v ∈ N → B (Function.update v τ u) ∈ N)
    (v : ∀ τ, lowT M τ) : B v ∈ N := by
  have key : ∀ s : Finset D.what₂.Tau, B (s.piecewise v v₀) ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hB
    | insert τ s hτ ih =>
      have e0 : s.piecewise v v₀ τ = v₀ τ := Finset.piecewise_eq_of_notMem _ _ _ hτ
      have := eq_top_of_translates h1 h2 τ (N.comap (B.toLinearMap (s.piecewise v v₀) τ)) (v₀ τ) (h0 τ)
        fun k hk u hu => hK τ k hk _ u (by rw [e0]; exact hu) ih
      rw [Finset.piecewise_insert]
      exact (this.ge Submodule.mem_top : v τ ∈ N.comap (B.toLinearMap (s.piecewise v v₀) τ))
  simpa using key Finset.univ

end GlobalTheory.DefLift

end
