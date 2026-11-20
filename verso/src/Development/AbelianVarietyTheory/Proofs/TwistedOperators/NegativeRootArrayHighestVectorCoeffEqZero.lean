import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsoPartStable

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.SphJet

/- English proof (translation)
Introduce `V _ _ n ε E Λ u hg hu hΛ F hF a b hab`. Establish `hkr : KRel ε (arrE E 1)` using `glRel_kRel ε _ ((arrModule V n ε E 1).1 hg).1`. Establish `hku : KUnit ε E` using `isUnitary_kUnit ε E hu`. Set `φ : Arr V n 1 →ₗ[ℂ] ℂ` to `(innerₛₗ ℂ u).comp ((LinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 → Fin n × Fin n => V) (fun _ => (a, b))).comp (arrOf V n 1))`. It suffices to establish `hle : Vminus ε E Λ u ≤ LinearMap.ker φ by`.

Establish `h0 : φ F = 0` using `hle hF`. Simplify `h0` using `[φ]`. Use `iSup₂_le fun y hy => ?_` and prove the remaining obligations. Take `⟨-, μ, ⟨c, d, hdc, -, rfl⟩, hyh⟩` from `hy`. Rewrite using `[(kLow _ n ε (arrE E 1) _ y hkr hyh).1]`.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `z ⟨w, hw, rfl⟩`. Take `⟨ν, hht, hν⟩` from `GlobalTheory.Jet.VminusComp.word_weight hkr hyh.1 w hw`. Establish `hcw` using `GlobalTheory.Jet.VminusComp.comp_weight hν a b`. Establish `hne : Λ ≠ ν - root a b`.

Introduce `h`. Establish `h1` using `congrArg GlobalTheory.Jet.VminusComp.ht h`. Rewrite `h1` using `[GlobalTheory.Jet.VminusComp.ht_sub, GlobalTheory.Jet.VminusComp.ht_root]`. Rewrite `hht` using `[GlobalTheory.Jet.VminusComp.ht_add, GlobalTheory.Jet.VminusComp.ht_root]`. Establish `h2 : ((d : ℕ) : ℝ) < ((c : ℕ) : ℝ)` using `by exact_mod_cast hdc`.

Establish `h3 : ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ)` using `by exact_mod_cast hab`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h0` using `kWtOrth V n ε E Λ (ν - root a b) u _ hku hΛ.1 hcw hne`. Simplify `h0` using `[φ, arrOf]`.
-/
theorem vminus_coef : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V), GlRel E → IsUnitary ε E → KHighest ε E Λ u → ∀ F ∈ Vminus ε E Λ u, ∀ a b : Fin n, a ≤ b → ⟪u, arrOf V n 1 F (fun _ => (a, b))⟫_ℂ = 0 := by
  intro V _ _ n ε E Λ u hg hu hΛ F hF a b hab
  have hkr : KRel ε (arrE E 1) := glRel_kRel ε _ ((arrModule V n ε E 1).1 hg).1
  have hku : KUnit ε E := isUnitary_kUnit ε E hu

  let φ : Arr V n 1 →ₗ[ℂ] ℂ :=
    (innerₛₗ ℂ u).comp ((LinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 → Fin n × Fin n => V)
      (fun _ => (a, b))).comp (arrOf V n 1))
  suffices hle : Vminus ε E Λ u ≤ LinearMap.ker φ by
    have h0 : φ F = 0 := hle hF
    simpa [φ] using h0

  refine iSup₂_le fun y hy => ?_
  obtain ⟨-, μ, ⟨c, d, hdc, -, rfl⟩, hyh⟩ := hy
  rw [(kLow _ n ε (arrE E 1) _ y hkr hyh).1]
  refine Submodule.span_le.2 ?_
  rintro z ⟨w, hw, rfl⟩

  obtain ⟨ν, hht, hν⟩ := GlobalTheory.Jet.VminusComp.word_weight hkr hyh.1 w hw
  have hcw := GlobalTheory.Jet.VminusComp.comp_weight hν a b
  have hne : Λ ≠ ν - root a b := by
    intro h
    have h1 := congrArg GlobalTheory.Jet.VminusComp.ht h
    rw [GlobalTheory.Jet.VminusComp.ht_sub, GlobalTheory.Jet.VminusComp.ht_root] at h1
    rw [GlobalTheory.Jet.VminusComp.ht_add, GlobalTheory.Jet.VminusComp.ht_root] at hht
    have h2 : ((d : ℕ) : ℝ) < ((c : ℕ) : ℝ) := by exact_mod_cast hdc
    have h3 : ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hab
    linarith

  have h0 := kWtOrth V n ε E Λ (ν - root a b) u _ hku hΛ.1 hcw hne
  simpa [φ, arrOf] using h0

end GlobalTheory.SphJet
