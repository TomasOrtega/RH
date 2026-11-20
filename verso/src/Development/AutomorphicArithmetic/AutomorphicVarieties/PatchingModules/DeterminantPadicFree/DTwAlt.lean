import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

/- English proof (translation)
Introduce `F G _ _ n D κ la Y hκ hla hY`. Use `set c : F := D.χF D.g₀ with hc`. Establish `hc1 : c - 1 ≠ 0`. Introduce `h`. Apply `D.χ_ne` to reduce the goal to its premises.

Use `ext`. Conclude with `sub_eq_zero.mp h`. Use `set Z : Matrix (Fin n) (Fin n) F := D.r D.g₀ * Y * D.r D.g₀⁻¹ with hZ`. Use `set Y₁ : Matrix (Fin n) (Fin n) F := (c - 1)⁻¹ • (c • Z - c • κ D.g₀ - la D.g₀ - Y) with hY₁`. Establish `key : ∀ g ∈ D.G', κ g = dTw (fun _ => 1) D.r Y₁ g`.

Introduce `g hg`. Establish `hg' : D.g₀⁻¹ * g * D.g₀ ∈ D.G'`. Use `D.G'.mul_mem (D.comm D.g₀⁻¹ g) hg` as an intermediate fact. Simplify using `using this`. Use `set g' := D.g₀⁻¹ * g * D.g₀ with hgg`.

Establish `e : g * D.g₀ = D.g₀ * g'` using `by rw [hgg]; group`. Establish `e' : g'⁻¹ * D.g₀⁻¹ = D.g₀⁻¹ * g⁻¹` using `by rw [hgg]; group`. Establish `h1` using `hκ g trivial D.g₀ trivial`. Establish `h2` using `hla g trivial D.g₀ trivial`. Rewrite `h1` using `[e, hκ D.g₀ trivial g' trivial]`.

Rewrite `h2` using `[e, hla D.g₀ trivial g' trivial]`. Establish `hχ : D.χF g = 1` using `by simp [DetFr.χF, D.χ_triv g hg]`. Rewrite `h2` using `[hχ, ← hc]`. Establish `h3` using `hY g hg`. Establish `h4 : D.r D.g₀ * κ g' * D.r D.g₀⁻¹ + D.r D.g₀ * la g' * D.r D.g₀⁻¹ = D.r g * Z * D.r g⁻¹ - Z`.

Rewrite using `[← add_mul, ← mul_add, hY g' hg', dTw, one_smul, mul_sub, sub_mul, hZ]`. Use `congr 1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← map_mul, ← map_mul, ← map_mul, ← map_mul, e, e']`. Use `_ = _ := by simp only [mul_assoc]`.

Establish `h5 : (c - 1) • κ g = (c - 1) • dTw (fun _ => 1) D.r Y₁ g`. Simplify using `only [dTw, one_smul] at h1 h2 h3 ⊢`. Rewrite using `[hY₁, smul_sub, mul_smul_comm, smul_mul_assoc, smul_inv_smul₀ hc1, smul_inv_smul₀ hc1]`. Simplify using `only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]`. Take the linear combination `(norm := module) c • h4 - c • h1 - h2 - h3`.

Conclude with `smul_right_injective _ hc1 h5`. Use `⟨⟨Y₁, key⟩, Y - Y₁, fun g hg => ?_⟩` and prove the remaining obligations. Establish `h3` using `hY g hg`. Rewrite `h3` using `[key g hg]`. Simplify using `only [dTw, one_smul, mul_sub, sub_mul] at h3 ⊢`.

Rewrite `h3`, the goal using `[← sub_eq_zero]`. Rewrite using `[← h3]`. Normalize the expressions using the abelian group laws.
-/
theorem UpperTheory.V.Pa.Det.eigen :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) (κ la : G → Matrix (Fin n) (Fin n) F) (Y : Matrix (Fin n) (Fin n) F), TwCoc (fun _ => 1) D.r Set.univ κ → TwCoc D.χF D.r Set.univ la → (∀ g ∈ D.G', κ g + la g = dTw (fun _ => 1) D.r Y g) → (∃ Y₁, ∀ g ∈ D.G', κ g = dTw (fun _ => 1) D.r Y₁ g) ∧ ∃ Y₂, ∀ g ∈ D.G', la g = dTw (fun _ => 1) D.r Y₂ g := by
  intro F G _ _ n D κ la Y hκ hla hY
  set c : F := D.χF D.g₀ with hc
  have hc1 : c - 1 ≠ 0 := by
    intro h
    apply D.χ_ne
    ext
    exact sub_eq_zero.mp h
  set Z : Matrix (Fin n) (Fin n) F := D.r D.g₀ * Y * D.r D.g₀⁻¹ with hZ
  set Y₁ : Matrix (Fin n) (Fin n) F := (c - 1)⁻¹ • (c • Z - c • κ D.g₀ - la D.g₀ - Y) with hY₁
  have key : ∀ g ∈ D.G', κ g = dTw (fun _ => 1) D.r Y₁ g := by
    intro g hg
    have hg' : D.g₀⁻¹ * g * D.g₀ ∈ D.G' := by
      have := D.G'.mul_mem (D.comm D.g₀⁻¹ g) hg
      simpa using this
    set g' := D.g₀⁻¹ * g * D.g₀ with hgg
    have e : g * D.g₀ = D.g₀ * g' := by rw [hgg]; group
    have e' : g'⁻¹ * D.g₀⁻¹ = D.g₀⁻¹ * g⁻¹ := by rw [hgg]; group
    have h1 := hκ g trivial D.g₀ trivial
    have h2 := hla g trivial D.g₀ trivial
    rw [e, hκ D.g₀ trivial g' trivial] at h1
    rw [e, hla D.g₀ trivial g' trivial] at h2
    have hχ : D.χF g = 1 := by simp [DetFr.χF, D.χ_triv g hg]
    rw [hχ, ← hc] at h2
    have h3 := hY g hg
    have h4 : D.r D.g₀ * κ g' * D.r D.g₀⁻¹ + D.r D.g₀ * la g' * D.r D.g₀⁻¹
        = D.r g * Z * D.r g⁻¹ - Z := by
      rw [← add_mul, ← mul_add, hY g' hg', dTw, one_smul, mul_sub, sub_mul, hZ]
      congr 1
      calc D.r D.g₀ * (D.r g' * Y * D.r g'⁻¹) * D.r D.g₀⁻¹
          = (D.r D.g₀ * D.r g') * Y * (D.r g'⁻¹ * D.r D.g₀⁻¹) := by simp only [mul_assoc]
        _ = (D.r g * D.r D.g₀) * Y * (D.r D.g₀⁻¹ * D.r g⁻¹) := by
          rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, e, e']
        _ = _ := by simp only [mul_assoc]
    have h5 : (c - 1) • κ g = (c - 1) • dTw (fun _ => 1) D.r Y₁ g := by
      simp only [dTw, one_smul] at h1 h2 h3 ⊢
      rw [hY₁, smul_sub, mul_smul_comm, smul_mul_assoc, smul_inv_smul₀ hc1, smul_inv_smul₀ hc1]
      simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
      linear_combination (norm := module) c • h4 - c • h1 - h2 - h3
    exact smul_right_injective _ hc1 h5
  refine ⟨⟨Y₁, key⟩, Y - Y₁, fun g hg => ?_⟩
  have h3 := hY g hg
  rw [key g hg] at h3
  simp only [dTw, one_smul, mul_sub, sub_mul] at h3 ⊢
  rw [← sub_eq_zero] at h3 ⊢
  rw [← h3]; abel
