import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsBasisOverEmbedding
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EqZeroOfForallEmbeddingSumEqZero

noncomputable section

namespace GlobalTheory.ArcCM

/- English proof (translation)
Take `⟨n, e, c, hind, ha⟩` from `GlobalTheory.exists_basis_over_embedding K σ₀ m a`. Use `⟨n, e, fun b => ∑ i, c i b • F i, ?_, ?_⟩` and prove the remaining obligations. Introduce `r hadd hsm`. Establish `hs : ∀ b, r (∑ i, c i b • F i) = ∑ i, σ₀ (c i b) * r (F i)` using `fun b => by`. Use `map_sum (AddMonoidHom.mk' r hadd) (fun i => c i b • F i) Finset.univ` as an intermediate fact.

Simplify using `only [AddMonoidHom.mk'_apply, hsm] at this`. Conclude with `this`. Simplify using `only [hs, ha, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => by ring` and prove the remaining obligations.

Introduce `K₁ _ _ _ y hy b haveI : CharZero K := σ₀.charZero haveI : FiniteDimensional K K₁ := Module.Finite.of_restrictScalars_finite ℚ K K₁`. Conclude with `congrFun (GlobalTheory.eq_zero_of_forall_embedding_sum_eq_zero K K₁ σ₀ n e y hind hy) b`.
-/
theorem exists_regroup_vectors {K : Type} [Field K] (σ₀ : K →+* ℂ) {M : Type} [AddCommGroup M] [Module K M] {m : ℕ}
    (a : Fin m → ℂ) (F : Fin m → M) :
    ∃ (n : ℕ) (e : Fin n → ℂ) (G : Fin n → M),
      (∀ r : M → ℂ, (∀ x y, r (x + y) = r x + r y) → (∀ (c : K) x, r (c • x) = σ₀ c * r x) →
        ∑ i, a i * r (F i) = ∑ b, e b * r (G b)) ∧
      ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra K K₁] (y : Fin n → K₁),
        (∀ σ₁ : K₁ →+* ℂ, σ₁.comp (algebraMap K K₁) = σ₀ → ∑ b, e b * σ₁ (y b) = 0) → ∀ b, y b = 0 := by
  obtain ⟨n, e, c, hind, ha⟩ := GlobalTheory.exists_basis_over_embedding K σ₀ m a
  refine ⟨n, e, fun b => ∑ i, c i b • F i, ?_, ?_⟩
  · intro r hadd hsm
    have hs : ∀ b, r (∑ i, c i b • F i) = ∑ i, σ₀ (c i b) * r (F i) := fun b => by
      have := map_sum (AddMonoidHom.mk' r hadd) (fun i => c i b • F i) Finset.univ
      simp only [AddMonoidHom.mk'_apply, hsm] at this
      exact this
    simp only [hs, ha, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => by ring
  · intro K₁ _ _ _ y hy b
    haveI : CharZero K := σ₀.charZero
    haveI : FiniteDimensional K K₁ := Module.Finite.of_restrictScalars_finite ℚ K K₁
    exact congrFun (GlobalTheory.eq_zero_of_forall_embedding_sum_eq_zero K K₁ σ₀ n e y hind hy) b

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions GlobalTheory.Shares

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Introduce `D T h j ka CR Tt cc Fm hkill hdet hon f hf`. Take `⟨m, a, F, -, hF⟩` from `hon f fun k => (hf k).1`. Take `⟨n, e, G, h1, h2⟩` from `exists_regroup_vectors (K := T.Q.c.F) T.σ₀ a F`. Establish `hG : ∀ k, ∀ x ∈ ((T.U j T.σ₀).X k).dom, f k x = ∑ b, e b * rdR h j (G b) k x`. Introduce `k x hx`.

Rewrite using `[hF k x hx]`. Use `h1 (fun P => rdR h j P k x) (fun P Q => ?_) (fun c P => ?_)` and prove the remaining obligations. Conclude with `congrFun (congrFun (map_add (rdU (T.U j T.σ₀)) P.1 Q.1) k) x`. Conclude with `congrFun (congrFun (map_smulₛₗ (rdU (T.U j T.σ₀)) c P.1) k) x`. Use `⟨n, e, G, fun b => hdet (G b) ?_, hG⟩` and prove the remaining obligations.

Introduce `K₁ _ _ _ d hd`. Conclude with `h2 K₁ (fun b => d (G b)) (fun σ₁ hσ => hkill K₁ d hd σ₁ hσ n e G f hf hG) b`.
-/
theorem mggOnto_of_detect_fun : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) (Fm : ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁], ((recB h.toLawsCore).Cusp j ka → K₁) → Prop), (∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁] (φ : (recB h.toLawsCore).Cusp j ka → K₁), Fm K₁ φ → ∀ σ₁ : K₁ →+* ℂ, σ₁.comp (algebraMap T.Q.c.F K₁) = T.σ₀ → ∀ (m : ℕ) (a : Fin m → ℂ) (F : Fin m → (recB h.toLawsCore).Cusp j ka) (f : ∀ k : (T.U j T.σ₀).Comp, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ), (∀ k, f k ∈ ((T.U j T.σ₀).X k).SSgt (laR T j ka k) (WeightFamilies.c1 D CR Tt cc j)) → (∀ k, ∀ x ∈ ((T.U j T.σ₀).X k).dom, f k x = ∑ i, a i * rdR h j (F i) k x) → ∑ i, a i * σ₁ (φ (F i)) = 0) → (∀ F : (recB h.toLawsCore).Cusp j ka, (∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁] (φ : (recB h.toLawsCore).Cusp j ka → K₁), Fm K₁ φ → φ F = 0) → F ∈ WeightFamilies.MggK (recB h.toLawsCore) CR Tt cc j ka) → RdOnto h j ka → MggOnto h j CR Tt cc ka := by
  intro D T h j ka CR Tt cc Fm hkill hdet hon f hf
  obtain ⟨m, a, F, -, hF⟩ := hon f fun k => (hf k).1
  obtain ⟨n, e, G, h1, h2⟩ := exists_regroup_vectors (K := T.Q.c.F) T.σ₀ a F
  have hG : ∀ k, ∀ x ∈ ((T.U j T.σ₀).X k).dom, f k x = ∑ b, e b * rdR h j (G b) k x := by
    intro k x hx
    rw [hF k x hx]
    refine h1 (fun P => rdR h j P k x) (fun P Q => ?_) (fun c P => ?_)
    · exact congrFun (congrFun (map_add (rdU (T.U j T.σ₀)) P.1 Q.1) k) x
    · exact congrFun (congrFun (map_smulₛₗ (rdU (T.U j T.σ₀)) c P.1) k) x
  refine ⟨n, e, G, fun b => hdet (G b) ?_, hG⟩
  intro K₁ _ _ _ d hd
  exact h2 K₁ (fun b => d (G b))
    (fun σ₁ hσ => hkill K₁ d hd σ₁ hσ n e G f hf hG) b

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Introduce `D T h j ka CR Tt cc Fm hkill` and use `mggOnto_of_detect_fun D T h j ka CR Tt cc Fm fun K₁ _ _ _ φ hφ => (hkill K₁ φ hφ).2`.
-/
theorem mggOnto_of_detect : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) (Fm : ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁], ((recB h.toLawsCore).Cusp j ka → K₁) → Prop), (∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁] (φ : (recB h.toLawsCore).Cusp j ka → K₁), Fm K₁ φ → IsLinearMap T.Q.c.F φ ∧ ∀ σ₁ : K₁ →+* ℂ, σ₁.comp (algebraMap T.Q.c.F K₁) = T.σ₀ → ∀ (m : ℕ) (a : Fin m → ℂ) (F : Fin m → (recB h.toLawsCore).Cusp j ka) (f : ∀ k : (T.U j T.σ₀).Comp, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ), (∀ k, f k ∈ ((T.U j T.σ₀).X k).SSgt (laR T j ka k) (WeightFamilies.c1 D CR Tt cc j)) → (∀ k, ∀ x ∈ ((T.U j T.σ₀).X k).dom, f k x = ∑ i, a i * rdR h j (F i) k x) → ∑ i, a i * σ₁ (φ (F i)) = 0) → (∀ F : (recB h.toLawsCore).Cusp j ka, (∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁] (φ : (recB h.toLawsCore).Cusp j ka → K₁), Fm K₁ φ → φ F = 0) → F ∈ WeightFamilies.MggK (recB h.toLawsCore) CR Tt cc j ka) → RdOnto h j ka → MggOnto h j CR Tt cc ka :=
  fun D T h j ka CR Tt cc Fm hkill =>
    mggOnto_of_detect_fun D T h j ka CR Tt cc Fm fun K₁ _ _ _ φ hφ => (hkill K₁ φ hφ).2

end GlobalTheory.ArcCM
