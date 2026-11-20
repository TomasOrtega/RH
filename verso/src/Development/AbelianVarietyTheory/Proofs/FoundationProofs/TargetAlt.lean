import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems

open Formalism.MainNotions.N

namespace GlobalTheory.ConjugateIrreducibility

/- English proof (translation)
Use `⟨hne, fun _ _ _ => Submodule.mem_top, fun W _ hinv => ?_⟩` and prove the remaining obligations. Set `W₀ : Submodule k (Fin n → k)` to `W.comap (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k))`. Establish `hmem : ∀ v, v ∈ W₀ ↔ (g : Matrix (Fin n) (Fin n) k).mulVec v ∈ W` using `fun v => by`. Simplify using `[W₀, Matrix.toLin'_apply]`. Establish `hinv₀ : IsInv (MonoidHom.comp r (Subgroup.subtype H)) W₀`.

Introduce `s v hv`. Rewrite `hv`, the goal using `[hmem]`. Establish `key : (g : Matrix (Fin n) (Fin n) k).mulVec ((r s.1 : Matrix (Fin n) (Fin n) k).mulVec v) = (r' s.1 : Matrix (Fin n) (Fin n) k).mulVec ((g : Matrix (Fin n) (Fin n) k).mulVec v)`. Simplify using `[hconj, Matrix.mulVec_mulVec, mul_assoc]`. Establish `h1` using `hinv ⟨s, hHH s s.2⟩ _ hv`.

Simplify using `only [MonoidHom.comp_apply, Subgroup.coe_subtype] at h1 ⊢`. Rewrite using `[key]`. Conclude with `h1`. Establish `hback : ∀ w, ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec w ∈ W₀ ↔ w ∈ W` using `fun w => by`. Rewrite using `[hmem, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`.

Break down `hmin W₀ le_top hinv₀ with h0 | htop` into its components or cases. Use `left`. Rewrite using `[eq_bot_iff]`. Introduce `w hw`. Establish `h1` using `(hback w).mpr hw`.

Rewrite `h1` using `[h0, Submodule.mem_bot]`. Establish `h2` using `congrArg (Matrix.mulVec (g : Matrix (Fin n) (Fin n) k)) h1`. Rewrite `h2` using `[Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.mulVec_zero]`. Rewrite using `[h2]`. Conclude with `Submodule.zero_mem _`.

Use `right`. Rewrite using `[eq_top_iff]`. Introduce `w _`. Conclude with `(hback w).mp (htop ▸ Submodule.mem_top)`.
-/
private theorem isIrrSub_of_conj {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (H H' : Subgroup Γ)
    (hHH : ∀ s ∈ H, s ∈ H') (r r' : Γ →* GL (Fin n) k) (g : GL (Fin n) k)
    (hconj : ∀ s : Γ, (r' : Γ → GL (Fin n) k) s = g * (r : Γ → GL (Fin n) k) s * g⁻¹)
    (hne : (⊤ : Submodule k (Fin n → k)) ≠ ⊥)
    (hmin : ∀ W : Submodule k (Fin n → k), W ≤ ⊤ → IsInv (MonoidHom.comp r (Subgroup.subtype H)) W →
      W = ⊥ ∨ W = ⊤) :
    IsIrrSub (MonoidHom.comp r' (Subgroup.subtype H')) ⊤ := by
  refine ⟨hne, fun _ _ _ => Submodule.mem_top, fun W _ hinv => ?_⟩

  let W₀ : Submodule k (Fin n → k) := W.comap (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k))
  have hmem : ∀ v, v ∈ W₀ ↔ (g : Matrix (Fin n) (Fin n) k).mulVec v ∈ W := fun v => by
    simp [W₀, Matrix.toLin'_apply]
  have hinv₀ : IsInv (MonoidHom.comp r (Subgroup.subtype H)) W₀ := by
    intro s v hv
    rw [hmem] at hv ⊢
    have key : (g : Matrix (Fin n) (Fin n) k).mulVec ((r s.1 : Matrix (Fin n) (Fin n) k).mulVec v) =
        (r' s.1 : Matrix (Fin n) (Fin n) k).mulVec ((g : Matrix (Fin n) (Fin n) k).mulVec v) := by
      simp [hconj, Matrix.mulVec_mulVec, mul_assoc]
    have h1 := hinv ⟨s, hHH s s.2⟩ _ hv
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at h1 ⊢
    rw [key]
    exact h1
  have hback : ∀ w, ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec w ∈ W₀ ↔ w ∈ W := fun w => by
    rw [hmem, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  rcases hmin W₀ le_top hinv₀ with h0 | htop
  · left
    rw [eq_bot_iff]
    intro w hw
    have h1 := (hback w).mpr hw
    rw [h0, Submodule.mem_bot] at h1
    have h2 := congrArg (Matrix.mulVec (g : Matrix (Fin n) (Fin n) k)) h1
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.mulVec_zero] at h2
    rw [h2]
    exact Submodule.zero_mem _
  · right
    rw [eq_top_iff]
    intro w _
    exact (hback w).mp (htop ▸ Submodule.mem_top)

/- English proof (translation)
Take `⟨hne, -, hmin⟩` from `hirr`. Conclude with `isIrrSub_of_conj H H' hHH r r' g hconj hne hmin`.
-/
theorem main {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (H H' : Subgroup Γ) (hHH : ∀ s ∈ H, s ∈ H')
    (r r' : Γ →* GL (Fin n) k) (g : GL (Fin n) k)
    (hconj : ∀ s : Γ, (r' : Γ → GL (Fin n) k) s = g * (r : Γ → GL (Fin n) k) s * g⁻¹)
    (hirr : IsIrrSub (MonoidHom.comp r (Subgroup.subtype H)) ⊤) :
    IsIrrSub (MonoidHom.comp r' (Subgroup.subtype H')) ⊤ := by
  obtain ⟨hne, -, hmin⟩ := hirr
  exact isIrrSub_of_conj H H' hHH r r' g hconj hne hmin

/- English proof (translation)
Introduce `Γ k _ _ n H H' hHH r r' g hconj hirr`. Take `⟨hne, -, hmin⟩` from `hirr`. Conclude with `isIrrSub_of_conj H H' hHH r r' g hconj hne hmin`.
-/
theorem target : ∀ {Γ k : Type} [inst : Group Γ] [inst_1 : Field k] {n : ℕ} (H H' : Subgroup Γ), (∀ s ∈ H, s ∈ H') → ∀ (r r' : Γ →* GL (Fin n) k) (g : GL (Fin n) k), (∀ (s : Γ), (r' : Γ → GL (Fin n) k) s = g * (r : Γ → GL (Fin n) k) s * g⁻¹) → Formalism.MainNotions.N.IsIrrSub (MonoidHom.comp r (Subgroup.subtype H)) ⊤ → Formalism.MainNotions.N.IsIrrSub (MonoidHom.comp r' (Subgroup.subtype H')) ⊤ := by
  intro Γ k _ _ n H H' hHH r r' g hconj hirr
  obtain ⟨hne, -, hmin⟩ := hirr
  exact isIrrSub_of_conj H H' hHH r r' g hconj hne hmin

end GlobalTheory.ConjugateIrreducibility
