import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IsFixMapIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.SplitUnitElements.SplitS
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.CintIdx

open QuadraticAlgebra Matrix UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

/- English proof (translation)
Apply the tactic sequence `ext <;> simp [sigL.eq_1]`.
-/
private theorem sigL_zero' {K : Type} [Field K] (Δ τ : K) : sigL (0 : EL Δ τ) = 0 := by
  ext <;> simp [sigL.eq_1]

/- English proof (translation)
Rewrite using `[herm.eq_1]`. Simplify using `[sigL_zero']`.
-/
private theorem herm_pair_zero_eq {K : Type} [Field K] (Δ τ : K) (c : K) (m : EL Δ τ) (x : Sp Δ τ) (a : Lsq K Δ) :
    herm c m x ((a, 0) : Sp Δ τ) = algebraMap K (Lsq K Δ) c * x.1 * star a := by
  rw [herm.eq_1]
  simp [sigL_zero']

/- English proof (translation)
Introduce `O K _ _ _ _ _ Δ τ hL hτ hu c d m hD S₀ S₁ h₀ h₁ a ha`. Establish `hs₁` using `One.splitS O K Δ τ hL hτ hu c d m hD S₁ h₁`. Establish `hconj : ∀ S : Set (Sp Δ τ), IsFix O c d m S → ∀ b : Lsq K Δ, ((b, 0) : Sp Δ τ) ∈ S → ((star b, 0) : Sp Δ τ) ∈ S`. Introduce `S hS b hb`. Rewrite using `[← hS.stab]`.

Use `⟨(b, 0), hb, ?_⟩` and prove the remaining obligations. Rewrite using `[semi.eq_1]`. Simplify using `[sigL_zero']`. Establish `hsq : ∀ S : Set (Sp Δ τ), IsFix O c d m S → ∀ b : Lsq K Δ, ((b, 0) : Sp Δ τ) ∈ S → IsInt O (algebraMap K (Lsq K Δ) c * b * b)`. Introduce `S hS b hb`.

Establish `h` using `(hS.dual _).1 (hconj S hS b hb) (b, 0) hb`. Rewrite `h` using `[herm_pair_zero_eq, star_star]`. Conclude with `h`. Rewrite using `[h₁.dual]`. Introduce `x hx`.

Rewrite using `[herm_pair_zero_eq]`. Establish `hx1 : ((x.1, 0) : Sp Δ τ) ∈ S₁` using `hs₁.2.2.1 x hx`. Establish `e1` using `hsq S₁ h₁ x.1 hx1`. Establish `e2` using `hsq S₀ h₀ (star a) (hconj S₀ h₀ a ha)`. Rewrite `e1`, `e2`, the goal using `[IsInt.eq_1]`.

Apply `IsIntegral.of_pow (n := 2) (by norm_num)` to reduce the goal to its premises. Establish `e3 : (algebraMap K (Lsq K Δ) c * x.1 * star a) ^ 2 = (algebraMap K (Lsq K Δ) c * x.1 * x.1) * (algebraMap K (Lsq K Δ) c * star a * star a)`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e3]`. Conclude with `e1.mul e2`.
-/
theorem UpperTheory.V.Z.Sym.Loc.One.fst :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
        τ ∈ (algebraMap O K).range → (∃ u : Oˣ, algebraMap O K u = 2 - τ) → ∀ (c : K) (d m : EL Δ τ), IsDat c d m → ∀ S₀ S₁ : Set (Sp Δ τ), IsFix O c d m S₀ → IsFix O c d m S₁ →
        ∀ a : Lsq K Δ, ((a, 0) : Sp Δ τ) ∈ S₀ → ((a, 0) : Sp Δ τ) ∈ S₁ := by
  intro O K _ _ _ _ _ Δ τ hL hτ hu c d m hD S₀ S₁ h₀ h₁ a ha
  have hs₁ := One.splitS O K Δ τ hL hτ hu c d m hD S₁ h₁
  have hconj : ∀ S : Set (Sp Δ τ), IsFix O c d m S → ∀ b : Lsq K Δ,
      ((b, 0) : Sp Δ τ) ∈ S → ((star b, 0) : Sp Δ τ) ∈ S := by
    intro S hS b hb
    rw [← hS.stab]
    refine ⟨(b, 0), hb, ?_⟩
    rw [semi.eq_1]
    simp [sigL_zero']
  have hsq : ∀ S : Set (Sp Δ τ), IsFix O c d m S → ∀ b : Lsq K Δ,
      ((b, 0) : Sp Δ τ) ∈ S → IsInt O (algebraMap K (Lsq K Δ) c * b * b) := by
    intro S hS b hb
    have h := (hS.dual _).1 (hconj S hS b hb) (b, 0) hb
    rw [herm_pair_zero_eq, star_star] at h
    exact h
  rw [h₁.dual]
  intro x hx
  rw [herm_pair_zero_eq]
  have hx1 : ((x.1, 0) : Sp Δ τ) ∈ S₁ := hs₁.2.2.1 x hx
  have e1 := hsq S₁ h₁ x.1 hx1
  have e2 := hsq S₀ h₀ (star a) (hconj S₀ h₀ a ha)
  rw [IsInt.eq_1] at e1 e2 ⊢
  apply IsIntegral.of_pow (n := 2) (by norm_num)
  have e3 : (algebraMap K (Lsq K Δ) c * x.1 * star a) ^ 2 =
      (algebraMap K (Lsq K Δ) c * x.1 * x.1) * (algebraMap K (Lsq K Δ) c * star a * star a) := by
    ring
  rw [e3]
  exact e1.mul e2
