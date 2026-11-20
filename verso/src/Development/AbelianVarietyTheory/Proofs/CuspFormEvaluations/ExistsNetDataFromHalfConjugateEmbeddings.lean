import Mathlib
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.NormEuclideanEmbeddingEqNetNorm

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.NetNorms
open scoped ComplexConjugate

namespace GlobalTheory

/- English proof (translation)
Rewrite `h`, the goal using `[Fintype.linearIndependent_iff]`. Introduce `c hc i`. Establish `h1 : ∑ i, conj (c i) • v i = 0`. Use function extensionality and compare the values at `y`. Use `congrArg conj (congrFun hc y)` as an intermediate fact.

Simplify `this` using `[Finset.sum_apply, map_sum]`. Simplify using `using h (fun i => conj (c i)) h1 i`.
-/
theorem linearIndependent_conj_coords {ι κ : Type*} [Fintype ι] (v : ι → κ → ℂ)
    (h : LinearIndependent ℂ v) : LinearIndependent ℂ (fun i y => conj (v i y)) := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro c hc i
  have h1 : ∑ i, conj (c i) • v i = 0 := by
    funext y
    have := congrArg conj (congrFun hc y)
    simpa [Finset.sum_apply, map_sum] using this
  simpa using h (fun i => conj (c i)) h1 i

/- English proof (translation)
Introduce `D B j ka good hgood hsup n ev C H`. Establish `cc : ∀ σ : B.KO →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ`. Introduce `σ`. Use extensionality with `a`. Simplify using the standard rewrite rules.

Set `g : (B.KO →+* ℂ) → (B.KO →+* ℂ)` to `fun σ => if good σ then σ else ComplexEmbedding.conjugate σ`. Establish `hgc : ∀ σ, ¬ good σ → good (ComplexEmbedding.conjugate σ)`. Introduce `σ h`. Assume the negation of the conclusion as `h'`. Conclude with `h ((hgood σ).2 h')`.

Establish `g1 : ∀ σ, good σ → g σ = σ` using `fun σ h => if_pos h`. Establish `g2 : ∀ σ, ¬ good σ → g σ = ComplexEmbedding.conjugate σ` using `fun σ h => if_neg h`. Establish `gg : ∀ σ, good (g σ)`. Introduce `σ`. Distinguish the cases in `h : good σ`.

Rewrite using `[g1 σ h]`. Conclude with `h`. Rewrite using `[g2 σ h]`. Conclude with `hgc σ h`. Establish `gc : ∀ σ, g σ = g (ComplexEmbedding.conjugate σ)`.

Introduce `σ`. Distinguish the cases in `h : good σ`. Rewrite using `[g1 σ h, g2 _ ((hgood σ).1 h), cc]`. Rewrite using `[g2 σ h, g1 _ (hgc σ h)]`. Establish `gs : ∀ σ F, B.supN j ka (g σ) F = B.supN j ka σ F`.

Introduce `σ F`. Distinguish the cases in `h : good σ`. Rewrite using `[g1 σ h]`. Rewrite using `[g2 σ h, hsup]`. Establish `hcast : ∀ (a b : B.KO →+* ℂ) (h : a = b) (y : Fin (n a)) (F : B.Cusp j ka), ev b (finCongr (congrArg n h) y) F = ev a y F`.

Introduce `a b h y F`. Substitute `h` using the available equality. Both sides reduce to the same expression. Set `ev' : ∀ σ, Fin (n (g σ)) → (B.Cusp j ka →ₛₗ[σ] ℂ)` to `fun σ y => { toFun := fun F => if good σ then ev (g σ) y F else conj (ev (g σ) y F) map_add' := by`. Introduce `F G`.

Apply the tactic sequence `split_ifs <;> simp`. Use the proof step `map_smul' := by`. Introduce `a F`. Distinguish the cases in `h : good σ`. Establish `e : g σ a = σ a` using `by rw [g1 σ h]`.

Simplify using `only [if_pos h, map_smulₛₗ, e]`. Establish `e : g σ a = conj (σ a)` using `by rw [g2 σ h]; rfl`. Simplify using `[if_neg h, map_smulₛₗ, e] }`. Establish `e1 : ∀ σ y F, good σ → ev' σ y F = ev (g σ) y F` using `fun σ y F h => if_pos h`. Establish `e2 : ∀ σ y F, ¬ good σ → ev' σ y F = conj (ev (g σ) y F)` using `fun σ y F h => if_neg h`.

Establish `en : ∀ σ y F, ‖ev' σ y F‖ = ‖ev (g σ) y F‖`. Introduce `σ y F`. Distinguish the cases in `h : good σ`. Rewrite using `[e1 σ y F h]`. Rewrite using `[e2 σ y F h, Complex.norm_conj]`.

Use `⟨{ NN := fun σ => Fin (n (g σ)) ev := ev' cj := fun σ => finCongr (congrArg n (gc σ)) ev_conj := ?_ }, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `σ y F`. Distinguish the cases in `h : good σ`. Rewrite using `[e2 _ _ _ ((hgood σ).1 h), e1 _ _ _ h, hcast _ _ (gc σ)]`. Rewrite using `[e1 _ _ _ (hgc σ h), e2 _ _ _ h, hcast _ _ (gc σ), Complex.conj_conj]`.

Introduce `σ F`. Take `⟨y, hy⟩` from `(H _ (gg σ)).1 F`. Use `⟨y, ?_⟩` and prove the remaining obligations. Use `show _ ≤ ‖ev' σ y F‖`. Rewrite using `[en, ← gs]`.

Conclude with `hy`. Introduce `σ y F show ‖ev' σ y F‖ ≤ _`. Rewrite using `[en, ← gs]`. Conclude with `(H _ (gg σ)).2.1 y F`. Introduce `σ show Real.log (16 * (Fintype.card (Fin (n (g σ))) : ℝ)) ≤ C`.

Rewrite using `[Fintype.card_fin]`. Conclude with `(H _ (gg σ)).2.2.1`. Introduce `σ m F hF`. Establish `hI` using `(H _ (gg σ)).2.2.2 m F hF`. Use `show LinearIndependent ℂ (fun i => fun y : Fin (n (g σ)) => ev' σ y (F i))`.

Distinguish the cases in `h : good σ`. Simplify using `only [e1 σ _ _ h]`. Conclude with `hI`. Simplify using `only [e2 σ _ _ h]`. Conclude with `linearIndependent_conj_coords _ hI`.
-/
theorem exists_netData_of_readings_on_half :
    ∀ (D : D7) (B : WeightFamilies.Prov D) (j : ℕ) (ka : WeightFamilies.Wt D j) (good : (B.KO →+* ℂ) → Prop), (∀ σ, good σ ↔ ¬ good (ComplexEmbedding.conjugate σ)) → (∀ σ F, B.supN j ka (ComplexEmbedding.conjugate σ) F = B.supN j ka σ F) → ∀ (n : (B.KO →+* ℂ) → ℕ) (ev : ∀ σ, Fin (n σ) → (B.Cusp j ka →ₛₗ[σ] ℂ)) (C : ℝ), (∀ σ, good σ → (∀ F, ∃ y, B.supN j ka σ F / 4 ≤ ‖ev σ y F‖) ∧ (∀ y F, ‖ev σ y F‖ ≤ B.supN j ka σ F) ∧ Real.log (16 * (n σ : ℝ)) ≤ C ∧ ∀ (m : ℕ) (F : Fin m → B.Cusp j ka), LinearIndependent B.KO F → LinearIndependent ℂ (fun i => fun y => ev σ y (F i))) → ∃ Nt : NetData B j ka, NetMax Nt ∧ NetLeSup Nt ∧ NetSize Nt C ∧ ∀ σ, NetInj Nt σ := by
  classical
  intro D B j ka good hgood hsup n ev C H
  have cc : ∀ σ : B.KO →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ := by
    intro σ
    ext a
    simp
  let g : (B.KO →+* ℂ) → (B.KO →+* ℂ) := fun σ => if good σ then σ else ComplexEmbedding.conjugate σ
  have hgc : ∀ σ, ¬ good σ → good (ComplexEmbedding.conjugate σ) := by
    intro σ h
    by_contra h'
    exact h ((hgood σ).2 h')
  have g1 : ∀ σ, good σ → g σ = σ := fun σ h => if_pos h
  have g2 : ∀ σ, ¬ good σ → g σ = ComplexEmbedding.conjugate σ := fun σ h => if_neg h
  have gg : ∀ σ, good (g σ) := by
    intro σ
    by_cases h : good σ
    · rw [g1 σ h]; exact h
    · rw [g2 σ h]; exact hgc σ h
  have gc : ∀ σ, g σ = g (ComplexEmbedding.conjugate σ) := by
    intro σ
    by_cases h : good σ
    · rw [g1 σ h, g2 _ ((hgood σ).1 h), cc]
    · rw [g2 σ h, g1 _ (hgc σ h)]
  have gs : ∀ σ F, B.supN j ka (g σ) F = B.supN j ka σ F := by
    intro σ F
    by_cases h : good σ
    · rw [g1 σ h]
    · rw [g2 σ h, hsup]
  have hcast : ∀ (a b : B.KO →+* ℂ) (h : a = b) (y : Fin (n a)) (F : B.Cusp j ka),
      ev b (finCongr (congrArg n h) y) F = ev a y F := by
    intro a b h y F
    subst h
    rfl
  let ev' : ∀ σ, Fin (n (g σ)) → (B.Cusp j ka →ₛₗ[σ] ℂ) := fun σ y =>
    { toFun := fun F => if good σ then ev (g σ) y F else conj (ev (g σ) y F)
      map_add' := by
        intro F G
        split_ifs <;> simp
      map_smul' := by
        intro a F
        by_cases h : good σ
        · have e : g σ a = σ a := by rw [g1 σ h]
          simp only [if_pos h, map_smulₛₗ, e]
        · have e : g σ a = conj (σ a) := by rw [g2 σ h]; rfl
          simp [if_neg h, map_smulₛₗ, e] }
  have e1 : ∀ σ y F, good σ → ev' σ y F = ev (g σ) y F := fun σ y F h => if_pos h
  have e2 : ∀ σ y F, ¬ good σ → ev' σ y F = conj (ev (g σ) y F) := fun σ y F h => if_neg h
  have en : ∀ σ y F, ‖ev' σ y F‖ = ‖ev (g σ) y F‖ := by
    intro σ y F
    by_cases h : good σ
    · rw [e1 σ y F h]
    · rw [e2 σ y F h, Complex.norm_conj]
  refine ⟨{ NN := fun σ => Fin (n (g σ))
            ev := ev'
            cj := fun σ => finCongr (congrArg n (gc σ))
            ev_conj := ?_ }, ?_, ?_, ?_, ?_⟩
  · intro σ y F
    by_cases h : good σ
    · rw [e2 _ _ _ ((hgood σ).1 h), e1 _ _ _ h, hcast _ _ (gc σ)]
    · rw [e1 _ _ _ (hgc σ h), e2 _ _ _ h, hcast _ _ (gc σ), Complex.conj_conj]
  · intro σ F
    obtain ⟨y, hy⟩ := (H _ (gg σ)).1 F
    refine ⟨y, ?_⟩
    show _ ≤ ‖ev' σ y F‖
    rw [en, ← gs]
    exact hy
  · intro σ y F
    show ‖ev' σ y F‖ ≤ _
    rw [en, ← gs]
    exact (H _ (gg σ)).2.1 y F
  · intro σ
    show Real.log (16 * (Fintype.card (Fin (n (g σ))) : ℝ)) ≤ C
    rw [Fintype.card_fin]
    exact (H _ (gg σ)).2.2.1
  · intro σ m F hF
    have hI := (H _ (gg σ)).2.2.2 m F hF
    show LinearIndependent ℂ (fun i => fun y : Fin (n (g σ)) => ev' σ y (F i))
    by_cases h : good σ
    · simp only [e1 σ _ _ h]
      exact hI
    · simp only [e2 σ _ _ h]
      exact linearIndependent_conj_coords _ hI

end GlobalTheory
