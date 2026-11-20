import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ToOneSucc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOfMemSB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyCompSideMulEq

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

noncomputable section
namespace GlobalTheory.PosOne.ToOnePos

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro _ l hl`. Conclude with `⟨l, fun v => rfl, hl⟩`. Consider the case `succ m ih`.

Introduce `hm l hl`. Take `⟨l', hl'v, hl'⟩` from `(GlobalTheory.RootEx.Exchange.exchange_isPos k n c (m + 1) (by omega) (by omega) ψ hψ hψ1 ν A σ hσ).2.1 l hl`. Take `⟨l₁, hl₁v, hl₁⟩` from `ih (by omega) l' hl'`. Use `⟨l₁, fun v => ?_, hl₁⟩` and prove the remaining obligations. Rewrite using `[hl₁v, toOne_succ]`.

Use `congr 1`. Use function extensionality and compare the values at `w`. Conclude with `hl'v w`.
-/
theorem toOne_lin (ψ : AddChar k Circle) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure]
    {A : Type} [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (hσ : IsSmoothRep σ) :
    ∀ m : ℕ, m + 1 ≤ c → ∀ l : A →ₗ[ℂ] ℂ, IsNEquiv ψ (m + 1) σ l →
      ∃ l₁ : A →ₗ[ℂ] ℂ, (∀ v, l₁ v = toOne ν σ (m + 1) l v) ∧ IsNEquiv ψ 1 σ l₁ := by
  intro m
  induction m with
  | zero => intro _ l hl; exact ⟨l, fun v => rfl, hl⟩
  | succ m ih =>
    intro hm l hl
    obtain ⟨l', hl'v, hl'⟩ := (GlobalTheory.RootEx.Exchange.exchange_isPos k n c (m + 1) (by omega) (by omega) ψ hψ hψ1
      ν A σ hσ).2.1 l hl
    obtain ⟨l₁, hl₁v, hl₁⟩ := ih (by omega) l' hl'
    refine ⟨l₁, fun v => ?_, hl₁⟩
    rw [hl₁v, toOne_succ]
    congr 1
    funext w
    exact hl'v w

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro _ b hb`. Conclude with `⟨b, fun φ v => rfl, hb⟩`. Consider the case `succ m ih`.

Introduce `hm b hb`. Take `⟨b', hb'v, hb'⟩` from `((GlobalTheory.RootEx.Exchange.exchange_isPos k n c (m + 1) (by omega) (by omega) ψ hψ hψ1 ν A σ hσ).2.2 P π b).2 hb`. Take `⟨b₁, hb₁v, hb₁⟩` from `ih (by omega) b' hb'`. Use `⟨b₁, fun φ v => ?_, hb₁⟩` and prove the remaining obligations. Rewrite using `[hb₁v, toOne_succ]`.

Use `congr 1`. Use function extensionality and compare the values at `w`. Conclude with `hb'v φ w`.
-/
theorem toOne_bil (ψ : AddChar k Circle) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure]
    {A : Type} [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (hσ : IsSmoothRep σ)
    {P : Type} [AddCommGroup P] [Module ℂ P] (π : Representation ℂ (GL n k) P) :
    ∀ m : ℕ, m + 1 ≤ c → ∀ b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ, IsPos ψ (m + 1) π σ b →
      ∃ b₁ : P →ₗ[ℂ] A →ₗ[ℂ] ℂ, (∀ φ v, b₁ φ v = toOne ν σ (m + 1) (b φ) v) ∧ IsPos ψ 1 π σ b₁ := by
  intro m
  induction m with
  | zero => intro _ b hb; exact ⟨b, fun φ v => rfl, hb⟩
  | succ m ih =>
    intro hm b hb
    obtain ⟨b', hb'v, hb'⟩ := ((GlobalTheory.RootEx.Exchange.exchange_isPos k n c (m + 1) (by omega) (by omega) ψ hψ hψ1
      ν A σ hσ).2.2 P π b).2 hb
    obtain ⟨b₁, hb₁v, hb₁⟩ := ih (by omega) b' hb'
    refine ⟨b₁, fun φ v => ?_, hb₁⟩
    rw [hb₁v, toOne_succ]
    congr 1
    funext w
    exact hb'v φ w

variable {n' : Type} [Fintype n'] [DecidableEq n']

def omRep (μ : kˣ →* ℂˣ) (hμ : IsOpen (μ.ker : Set kˣ)) : Representation ℂ (GL n k) (SB (Matrix n n' k)) where
  toFun g :=
    { toFun := fun Ψ => ⟨om μ 1 g Ψ.1,
        (GlobalTheory.SplitWeil.om_isSmoothRepresentation k n' n μ hμ).2.2.2.1 1 g Ψ.1 Ψ.2⟩
      map_add' := fun Ψ Ψ' => by
        apply Subtype.ext
        have := (GlobalTheory.SplitWeil.om_isSmoothRepresentation k n' n μ hμ).2.2.1 1 g 1 Ψ.1 Ψ'.1
        simpa using this
      map_smul' := fun z Ψ => by
        apply Subtype.ext
        have := (GlobalTheory.SplitWeil.om_isSmoothRepresentation k n' n μ hμ).2.2.1 1 g z Ψ.1 0
        have h0 : om μ 1 g (0 : Matrix n n' k → ℂ) = 0 := by
          funext x
          simp [om]
        simpa [h0] using this }
  map_one' := by
    ext Ψ : 2
    exact (GlobalTheory.SplitWeil.om_isSmoothRepresentation k n' n μ hμ).1 Ψ.1
  map_mul' g h := by
    ext Ψ : 2
    have := (GlobalTheory.SplitWeil.om_isSmoothRepresentation k n' n μ hμ).2.1 1 1 g h Ψ.1
    simpa using this

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨h1, fun g Ψ v => h2 g Ψ _ v rfl⟩`. Introduce and unpack `⟨h1, h2⟩`. Use `⟨h1, fun g Ψ Ψ₁ v hΨ => ?_⟩` and prove the remaining obligations.

Establish `: Ψ₁ = omRep μ hμ g Ψ` using `Subtype.ext hΨ`. Substitute `this` using the available equality. Conclude with `h2 g Ψ v`.
-/
theorem bilPos_iff (ψ : AddChar k Circle) (μ : kˣ →* ℂˣ) (hμ : IsOpen (μ.ker : Set kˣ)) (p : ℕ)
    {A : Type} [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)
    (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) : BilPos ψ μ p σ B ↔ IsPos ψ p (omRep μ hμ) σ B := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun g Ψ v => h2 g Ψ _ v rfl⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun g Ψ Ψ₁ v hΨ => ?_⟩
    have : Ψ₁ = omRep μ hμ g Ψ := Subtype.ext hΨ
    subst this
    exact h2 g Ψ v

end GlobalTheory.PosOne.ToOnePos

open GlobalTheory.PosOne.ToOnePos in

/- English proof (translation)
Introduce `k _ _ _ _ _ _ n n' _ _ _ _ c P hP hPc ψ hψ hψ1 ν _ A _ _ σ hσ`. Take `⟨m, rfl⟩ : ∃ m, P = m + 1` from `⟨P - 1, by omega⟩`. Use `⟨toOne_lin ψ hψ hψ1 ν σ hσ m hPc, fun μ hμ B hB => ?_⟩` and prove the remaining obligations. Take `⟨B₁, hB₁v, hB₁⟩` from `toOne_bil ψ hψ hψ1 ν σ hσ (omRep μ hμ) m hPc B ((bilPos_iff ψ μ hμ _ σ B).1 hB)`. Conclude with `⟨B₁, hB₁v, (bilPos_iff ψ μ hμ 1 σ B₁).2 hB₁⟩`.
-/
theorem GlobalTheory.PosOne.toOne_isPosOne : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c P : ℕ) (_ : 1 ≤ P) (_ : P ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ), (∀ l : A →ₗ[ℂ] ℂ, IsNEquiv ψ P σ l → ∃ l₁ : A →ₗ[ℂ] ℂ, (∀ v, l₁ v = toOne ν σ P l v) ∧ IsNEquiv ψ 1 σ l₁) ∧ ∀ (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ), BilPos ψ μ P σ B → ∃ B₁ : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ, (∀ Ψ v, B₁ Ψ v = toOne ν σ P (B Ψ) v) ∧ BilPos ψ μ 1 σ B₁ := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c P hP hPc ψ hψ hψ1 ν _ A _ _ σ hσ
  obtain ⟨m, rfl⟩ : ∃ m, P = m + 1 := ⟨P - 1, by omega⟩
  refine ⟨toOne_lin ψ hψ hψ1 ν σ hσ m hPc, fun μ hμ B hB => ?_⟩
  obtain ⟨B₁, hB₁v, hB₁⟩ := toOne_bil ψ hψ hψ1 ν σ hσ (omRep μ hμ) m hPc B ((bilPos_iff ψ μ hμ _ σ B).1 hB)
  exact ⟨B₁, hB₁v, (bilPos_iff ψ μ hμ 1 σ B₁).2 hB₁⟩
