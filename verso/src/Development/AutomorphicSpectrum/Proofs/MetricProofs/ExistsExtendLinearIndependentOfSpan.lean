import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement

namespace GlobalTheory.CompanionTheory.Ar.Exchange

/- English proof (translation)
Set `v : Fin r ⊕ Fin m → (Fin g → ℂ)` to `Sum.elim w b`. Establish `hs : LinearIndepOn ℂ v (Set.range Sum.inl)`. Rewrite using `[linearIndepOn_range_iff Sum.inl_injective]`. Conclude with `hw`. Take `⟨B, -, hsB, hspan, hB⟩` from `exists_linearIndepOn_extension hs (Set.subset_univ _)`.

Set `S : Finset (Fin m)` to `Finset.univ.filter fun j => Sum.inr j ∈ B`. Set `J : Fin S.card → Fin m` to `S.orderEmbOfFin rfl`. Set `φ : Fin (r + S.card) → Fin r ⊕ Fin m` to `Fin.append Sum.inl (Sum.inr ∘ J)`. Establish `hφ : Function.Injective φ` using `Fin.append_injective_iff.mpr ⟨Sum.inl_injective, Sum.inr_injective.comp (S.orderEmbOfFin rfl).injective, fun _ _ => Sum.inl_ne_inr⟩`. Establish `hJS : ∀ l, J l ∈ S` using `fun l => S.orderEmbOfFin_mem rfl l`.

Establish `hφB : Set.range φ ⊆ B`. Introduce and unpack `_ ⟨l, rfl⟩`. Use `Fin.addCases (fun i => ?_) (fun l => ?_) l` and prove the remaining obligations. Simplify using `only [φ, Fin.append_left]`. Conclude with `hsB ⟨i, rfl⟩`.

Simplify using `only [φ, Fin.append_right, Function.comp_apply]`. Use `hJS l` as an intermediate fact. Simplify `this` using `[S]`. Establish `hBφ : B ⊆ Set.range φ`. Introduce and unpack `(i | j) hx`.

Conclude with `⟨Fin.castAdd _ i, by simp [φ]⟩`. Establish `hj : j ∈ Set.range (S.orderEmbOfFin rfl)`. Rewrite using `[Finset.range_orderEmbOfFin]`. Simplify using `[S, hx]`. Take `⟨l, hl⟩` from `hj`.

Conclude with `⟨Fin.natAdd _ l, by simp [φ, J, hl]⟩`. Establish `hu : LinearIndependent ℂ (v ∘ φ)`. Rewrite using `[← linearIndepOn_range_iff hφ]`. Conclude with `hB.mono hφB`. Establish `hle1 : Submodule.span ℂ (Set.range (v ∘ φ)) ≤ Submodule.span ℂ (Set.range b)`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨l, rfl⟩`. Use `show v (φ l) ∈ _`. Generalize the expression as in `φ l = x`. Break down `x with i | j` into its components or cases.

Conclude with `hwb i`. Conclude with `Submodule.subset_span ⟨j, rfl⟩`. Establish `hle2 : Submodule.span ℂ (Set.range b) ≤ Submodule.span ℂ (Set.range (v ∘ φ))`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`.

Establish `h1 : b j ∈ Submodule.span ℂ (v '' B)` using `hspan ⟨Sum.inr j, Set.mem_univ _, rfl⟩`. Establish `h2 : v '' B ⊆ Set.range (v ∘ φ)`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Take `⟨l, rfl⟩` from `hBφ hx`. Conclude with `⟨l, rfl⟩`.

Conclude with `Submodule.span_mono h2 h1`. Establish `hueq : (Fin.append w fun j => b (J j)) = v ∘ φ`. Use function extensionality and compare the values at `l`. Use `Fin.addCases (fun i => ?_) (fun l => ?_) l` and prove the remaining obligations. Simplify using `[φ, v]`.

Simplify using `[φ, v]`. Use `⟨S.card, J, ?_, ?_⟩` and prove the remaining obligations. Establish `e1` using `finrank_span_eq_card hu`. Establish `e2` using `finrank_span_eq_card hb`. Rewrite `e1` using `[le_antisymm hle1 hle2, e2]`.

Simplify using `using e1.symm`. Rewrite using `[hueq]`. Conclude with `hu`.
-/
theorem exists_completion_by_members (g m r : ℕ) (w : Fin r → Fin g → ℂ) (b : Fin m → Fin g → ℂ)
    (hw : LinearIndependent ℂ w) (hb : LinearIndependent ℂ b)
    (hwb : ∀ a, w a ∈ Submodule.span ℂ (Set.range b)) :
    ∃ (k : ℕ) (J : Fin k → Fin m), r + k = m ∧
      LinearIndependent ℂ (Fin.append w (fun j => b (J j))) := by
  classical
  let v : Fin r ⊕ Fin m → (Fin g → ℂ) := Sum.elim w b
  have hs : LinearIndepOn ℂ v (Set.range Sum.inl) := by
    rw [linearIndepOn_range_iff Sum.inl_injective]
    exact hw
  obtain ⟨B, -, hsB, hspan, hB⟩ := exists_linearIndepOn_extension hs (Set.subset_univ _)
  let S : Finset (Fin m) := Finset.univ.filter fun j => Sum.inr j ∈ B
  let J : Fin S.card → Fin m := S.orderEmbOfFin rfl
  let φ : Fin (r + S.card) → Fin r ⊕ Fin m := Fin.append Sum.inl (Sum.inr ∘ J)
  have hφ : Function.Injective φ :=
    Fin.append_injective_iff.mpr ⟨Sum.inl_injective,
      Sum.inr_injective.comp (S.orderEmbOfFin rfl).injective, fun _ _ => Sum.inl_ne_inr⟩
  have hJS : ∀ l, J l ∈ S := fun l => S.orderEmbOfFin_mem rfl l
  have hφB : Set.range φ ⊆ B := by
    rintro _ ⟨l, rfl⟩
    refine Fin.addCases (fun i => ?_) (fun l => ?_) l
    · simp only [φ, Fin.append_left]
      exact hsB ⟨i, rfl⟩
    · simp only [φ, Fin.append_right, Function.comp_apply]
      have := hJS l
      simpa [S] using this
  have hBφ : B ⊆ Set.range φ := by
    rintro (i | j) hx
    · exact ⟨Fin.castAdd _ i, by simp [φ]⟩
    · have hj : j ∈ Set.range (S.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]
        simp [S, hx]
      obtain ⟨l, hl⟩ := hj
      exact ⟨Fin.natAdd _ l, by simp [φ, J, hl]⟩
  have hu : LinearIndependent ℂ (v ∘ φ) := by
    rw [← linearIndepOn_range_iff hφ]
    exact hB.mono hφB
  have hle1 : Submodule.span ℂ (Set.range (v ∘ φ)) ≤ Submodule.span ℂ (Set.range b) := by
    rw [Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    show v (φ l) ∈ _
    generalize φ l = x
    rcases x with i | j
    · exact hwb i
    · exact Submodule.subset_span ⟨j, rfl⟩
  have hle2 : Submodule.span ℂ (Set.range b) ≤ Submodule.span ℂ (Set.range (v ∘ φ)) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have h1 : b j ∈ Submodule.span ℂ (v '' B) := hspan ⟨Sum.inr j, Set.mem_univ _, rfl⟩
    have h2 : v '' B ⊆ Set.range (v ∘ φ) := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨l, rfl⟩ := hBφ hx
      exact ⟨l, rfl⟩
    exact Submodule.span_mono h2 h1
  have hueq : (Fin.append w fun j => b (J j)) = v ∘ φ := by
    funext l
    refine Fin.addCases (fun i => ?_) (fun l => ?_) l
    · simp [φ, v]
    · simp [φ, v]
  refine ⟨S.card, J, ?_, ?_⟩
  · have e1 := finrank_span_eq_card hu
    have e2 := finrank_span_eq_card hb
    rw [le_antisymm hle1 hle2, e2] at e1
    simpa using e1.symm
  · rw [hueq]
    exact hu

end GlobalTheory.CompanionTheory.Ar.Exchange
