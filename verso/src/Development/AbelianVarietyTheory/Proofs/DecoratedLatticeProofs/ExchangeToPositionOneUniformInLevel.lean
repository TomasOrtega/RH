import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ToOneSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExchangeEqFiniteTranslateCombOfLevelStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExDownExUpAndExUpExDown
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOfMemSB
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

namespace GlobalTheory.PosOne.Unif

/- English proof (translation)
Simplify using `[comb, Finsupp.linearCombination_apply, smul_eq_mul]`.
-/
theorem comb_eq_lc {G : Type} (e : G →₀ ℂ) (F : G → ℂ) :
    comb e F = Finsupp.linearCombination ℂ F e := by
  simp [comb, Finsupp.linearCombination_apply, smul_eq_mul]

/- English proof (translation)
Use `conv_rhs => rw [comb_eq_lc]`. Simplify using `only [Finsupp.sum, map_sum, map_smul, Finsupp.linearCombination_mapDomain, comb_eq_lc, smul_eq_mul]`. Both sides reduce to the same expression.
-/
theorem comb_translate {G : Type} [Group G] (e : G →₀ ℂ) (f : G → G →₀ ℂ) (F : G → ℂ) :
    comb e (fun g => comb (f g) (fun h => F (h * g))) =
      comb (e.sum fun g a => a • (f g).mapDomain (· * g)) F := by
  conv_rhs => rw [comb_eq_lc]
  simp only [Finsupp.sum, map_sum, map_smul, Finsupp.linearCombination_mapDomain, comb_eq_lc, smul_eq_mul]
  rfl

def conjSub {G : Type} [Group G] (U : Subgroup G) (g : G) : Subgroup G :=
  U.comap (MulAut.conj g⁻¹).toMonoidHom

/- English proof (translation)
Simplify using `[conjSub]`.
-/
theorem mem_conjSub {G : Type} [Group G] (U : Subgroup G) (g u : G) :
    u ∈ conjSub U g ↔ g⁻¹ * u * g ∈ U := by
  simp [conjSub]

/- English proof (translation)
Establish `: (conjSub U g : Set G) = (fun x => g⁻¹ * x * g) ⁻¹' (U : Set G)`. Use extensionality with `x`. Simplify using `[mem_conjSub]`. Rewrite using `[this]`. Conclude with `hU.preimage ((continuous_const.mul continuous_id).mul continuous_const)`.
-/
theorem isOpen_conjSub {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G] (U : Subgroup G)
    (hU : IsOpen (U : Set G)) (g : G) : IsOpen (conjSub U g : Set G) := by
  have : (conjSub U g : Set G) = (fun x => g⁻¹ * x * g) ⁻¹' (U : Set G) := by
    ext x; simp [mem_conjSub]
  rw [this]
  exact hU.preimage ((continuous_const.mul continuous_id).mul continuous_const)

/- English proof (translation)
Introduce `u hu`. Rewrite `hu` using `[mem_conjSub]`. Establish `e1 : u * g = g * (g⁻¹ * u * g)` using `by group`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem fixed_conjSub {G A : Type} [Group G] [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ G A)
    (U : Subgroup G) (v : A) (hv : ∀ u ∈ U, σ u v = v) (g : G) :
    ∀ u ∈ conjSub U g, σ u (σ g v) = σ g v := by
  intro u hu
  rw [mem_conjSub] at hu
  have e1 : u * g = g * (g⁻¹ * u * g) := by group
  calc σ u (σ g v) = σ (u * g) v := by rw [map_mul]; rfl
    _ = σ g (σ (g⁻¹ * u * g) v) := by rw [e1, map_mul]; rfl
    _ = σ g v := by rw [hv _ hu]

end GlobalTheory.PosOne.Unif

namespace GlobalTheory.PosOne.Unif

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ)

/- English proof (translation)
Use `haveI : ν.IsAddHaarMeasure := hsd.1`. Introduce `q`. Proceed by induction on `q with`. Consider the case `zero`. Introduce `_ U _`.

Use `⟨Finsupp.single 1 1, Finsupp.single 1 1, ?_⟩` and prove the remaining obligations. Introduce `A _ _ σ _ l v _ _`. Simplify using `[comb, toOne_one]`. Consider the case `succ q ih`. Introduce `hc U hU`.

Establish `hq1 : 1 ≤ q + 1` using `by omega`. Establish `hqc : q + 1 < c` using `by omega`. Establish `H1` using `fun g : GL (n ⊕ Fin c) k => GlobalTheory.T.exchange_eq_finiteTranslateComb_of_level k n c (q + 1) hq1 hqc ψ hψc hψ1 ν (conjSub U g) (isOpen_conjSub U hU g)`. Use `choose eg eg' heg using H1`. Establish `H2` using `fun g : GL (n ⊕ Fin c) k => ih (by omega) (conjSub U g) (isOpen_conjSub U hU g)`.

Use `choose E E' hE using H2`. Take `⟨e₀, _e₀', he₀⟩` from `ih (by omega) U hU`. Take `⟨_e₁', e₁, he₁⟩` from `GlobalTheory.T.exchange_eq_finiteTranslateComb_of_level k n c (q + 1) hq1 hqc ψ hψc hψ1 ν U hU`. Use `⟨e₀.sum fun g a => a • (eg g).mapDomain (· * g), e₁.sum fun g a => a • (E' g).mapDomain (· * g), ?_⟩` and prove the remaining obligations. Introduce `A _ _ σ hsm l v hl hv`.

Take `⟨l', hl'eq, hl'pos⟩` from `(GlobalTheory.RootEx.Exchange.exchange_isPos k n c (q + 1) hq1 hqc ψ hψc hψ1 ν A σ hsm).2.1 l hl`. Establish `hfun : (⇑l' : A → ℂ) = exDown ν (q + 1) σ ⇑l` using `funext hl'eq`. Establish `htoOne : toOne ν σ (q + 1 + 1) ⇑l = toOne ν σ (q + 1) ⇑l'`. Rewrite using `[hfun]`. Both sides reduce to the same expression.

Establish `hmul : ∀ g h : GL (n ⊕ Fin c) k, σ h (σ g v) = σ (h * g) v`. Introduce `g h`. Rewrite using `[map_mul]`. Both sides reduce to the same expression. Prove the components needed by the constructor for the conclusion.

Rewrite using `[htoOne, (he₀ A σ hsm l' v hl'pos hv).1]`. Establish `: (fun g => l' (σ g v)) = fun g => comb (eg g) (fun h => l (σ (h * g) v))`. Use function extensionality and compare the values at `g`. Rewrite using `[hl'eq, (heg g A σ hsm l (σ g v) (fixed_conjSub σ U v hv g)).1 hl]`. Simplify using `only [hmul]`.

Rewrite using `[this]`. Conclude with `comb_translate e₀ eg (fun g => l (σ g v))`. Establish `hback` using `((GlobalTheory.RootEx.exDown_exUp_and_exUp_exDown k n c (q + 1) hq1 hqc ψ hψc hψ1 ν hsd A σ hsm l v).2 hl).symm`. Rewrite using `[hback, ← hfun, (he₁ A σ hsm l' v hv).2 hl'pos]`. Establish `: (fun g => l' (σ g v)) = fun g => comb (E' g) (fun h => toOne ν σ (q + 1 + 1) l (σ (h * g) v))`.

Use function extensionality and compare the values at `g`. Rewrite using `[(hE g A σ hsm l' (σ g v) hl'pos (fixed_conjSub σ U v hv g)).2, htoOne]`. Simplify using `only [hmul]`. Rewrite using `[this]`. Conclude with `comb_translate e₁ E' (fun g => toOne ν σ (q + 1 + 1) l (σ g v))`.
-/
theorem toOne_comb (ψ : AddChar k Circle) (hψc : Continuous ψ) (hψ1 : ψ ≠ 1) (ν : Measure k)
    (hsd : IsSelfDual ψ ν) : ∀ q : ℕ, q + 1 ≤ c → ∀ (U : Subgroup (GL (n ⊕ Fin c) k)),
    IsOpen (U : Set (GL (n ⊕ Fin c) k)) → ∃ e e' : GL (n ⊕ Fin c) k →₀ ℂ,
    ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)
      (_ : IsSmoothRep σ) (l : A →ₗ[ℂ] ℂ) (v : A), IsNEquiv ψ (q + 1) σ l → (∀ u ∈ U, σ u v = v) →
      toOne ν σ (q + 1) l v = comb e (fun g => l (σ g v)) ∧
        l v = comb e' fun g => toOne ν σ (q + 1) l (σ g v) := by
  haveI : ν.IsAddHaarMeasure := hsd.1
  intro q
  induction q with
  | zero =>
    intro _ U _
    refine ⟨Finsupp.single 1 1, Finsupp.single 1 1, ?_⟩
    intro A _ _ σ _ l v _ _
    simp [comb, toOne_one]
  | succ q ih =>
    intro hc U hU
    have hq1 : 1 ≤ q + 1 := by omega
    have hqc : q + 1 < c := by omega

    have H1 := fun g : GL (n ⊕ Fin c) k =>
      GlobalTheory.T.exchange_eq_finiteTranslateComb_of_level k n c (q + 1) hq1 hqc ψ hψc hψ1 ν (conjSub U g) (isOpen_conjSub U hU g)
    choose eg eg' heg using H1

    have H2 := fun g : GL (n ⊕ Fin c) k => ih (by omega) (conjSub U g) (isOpen_conjSub U hU g)
    choose E E' hE using H2
    obtain ⟨e₀, _e₀', he₀⟩ := ih (by omega) U hU
    obtain ⟨_e₁', e₁, he₁⟩ := GlobalTheory.T.exchange_eq_finiteTranslateComb_of_level k n c (q + 1) hq1 hqc ψ hψc hψ1 ν U hU
    refine ⟨e₀.sum fun g a => a • (eg g).mapDomain (· * g),
      e₁.sum fun g a => a • (E' g).mapDomain (· * g), ?_⟩
    intro A _ _ σ hsm l v hl hv
    obtain ⟨l', hl'eq, hl'pos⟩ :=
      (GlobalTheory.RootEx.Exchange.exchange_isPos k n c (q + 1) hq1 hqc ψ hψc hψ1 ν A σ hsm).2.1 l hl
    have hfun : (⇑l' : A → ℂ) = exDown ν (q + 1) σ ⇑l := funext hl'eq
    have htoOne : toOne ν σ (q + 1 + 1) ⇑l = toOne ν σ (q + 1) ⇑l' := by
      rw [hfun]; rfl
    have hmul : ∀ g h : GL (n ⊕ Fin c) k, σ h (σ g v) = σ (h * g) v := by
      intro g h; rw [map_mul]; rfl
    constructor
    · rw [htoOne, (he₀ A σ hsm l' v hl'pos hv).1]
      have : (fun g => l' (σ g v)) = fun g => comb (eg g) (fun h => l (σ (h * g) v)) := by
        funext g
        rw [hl'eq, (heg g A σ hsm l (σ g v) (fixed_conjSub σ U v hv g)).1 hl]
        simp only [hmul]
      rw [this]; exact comb_translate e₀ eg (fun g => l (σ g v))
    · have hback := ((GlobalTheory.RootEx.exDown_exUp_and_exUp_exDown k n c (q + 1) hq1 hqc ψ hψc hψ1 ν hsd A σ hsm l v).2 hl).symm
      rw [hback, ← hfun, (he₁ A σ hsm l' v hv).2 hl'pos]
      have : (fun g => l' (σ g v)) =
          fun g => comb (E' g) (fun h => toOne ν σ (q + 1 + 1) l (σ (h * g) v)) := by
        funext g
        rw [(hE g A σ hsm l' (σ g v) hl'pos (fixed_conjSub σ U v hv g)).2, htoOne]
        simp only [hmul]
      rw [this]; exact comb_translate e₁ E' (fun g => toOne ν σ (q + 1 + 1) l (σ g v))

end GlobalTheory.PosOne.Unif

open GlobalTheory.PosOne.Unif in
/- English proof (translation)
Introduce `k _ _ _ _ _ _ n _ _ c P hP hPc ψ hψc hψ1 ν hsd U hU`. Take `⟨q, rfl⟩ : ∃ q, P = q + 1` from `⟨P - 1, by omega⟩`. Take `⟨e, e', h⟩` from `toOne_comb k n c ψ hψc hψ1 ν hsd q hPc U hU`. Conclude with `⟨e, e', fun A _ _ σ hsm l v hl hv => h A σ hsm l v hl hv⟩`.
-/
theorem GlobalTheory.PosOne.toOne_uniform : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c P : ℕ) (_ : 1 ≤ P) (_ : P ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (U : Subgroup (GL (n ⊕ Fin c) k)) (_ : IsOpen (U : Set (GL (n ⊕ Fin c) k))), ∃ e e' : GL (n ⊕ Fin c) k →₀ ℂ, ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (l : A →ₗ[ℂ] ℂ) (v : A), IsNEquiv ψ P σ l → (∀ u ∈ U, σ u v = v) → toOne ν σ P l v = comb e (fun g => l (σ g v)) ∧ l v = comb e' fun g => toOne ν σ P l (σ g v) := by
  intro k _ _ _ _ _ _ n _ _ c P hP hPc ψ hψc hψ1 ν hsd U hU
  obtain ⟨q, rfl⟩ : ∃ q, P = q + 1 := ⟨P - 1, by omega⟩
  obtain ⟨e, e', h⟩ := toOne_comb k n c ψ hψc hψ1 ν hsd q hPc U hU
  exact ⟨e, e', fun A _ _ σ hsm l v hl hv => h A σ hsm l v hl hv⟩
