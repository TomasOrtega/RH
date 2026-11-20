import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeakOfRunTh

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

/- English proof (translation)
The claim follows from `(map_sum (Multiset.mapAddMonoidHom g) f Finset.univ).symm`.
-/
private theorem sum_map_eq {ι : Type} [Fintype ι] (f : ι → Multiset ℂ) (g : ℂ → ℂ) :
    ∑ i, (f i).map g = (∑ i, f i).map g :=
  (map_sum (Multiset.mapAddMonoidHom g) f Finset.univ).symm

/- English proof (translation)
Introduce `hAdd hMu hMW hDW E _ _ _ n a b hab ha hb μ e hμ l₁ l₂ lam hlam D₁ D₂ h₁ h₂`. Substitute `hab` using the available equality. Take `⟨D, hnot, hsat, hinf⟩` from `hAdd E a b D₁ D₂ (μ ^ b) (μ ^ a) ha hb`. Establish `hval : ∀ (w : Pl E) (k : ℕ), (μ ^ k).val w = μ.val w ^ k` using `fun w k => MonoidHom.pow_apply μ.1 k _`. Establish `hunr : ∀ {w : Pl E} (k : ℕ), μ.UnrAt w → (μ ^ k).UnrAt w`.

Introduce `w k h x hx`. Establish `e1 : (μ ^ k).loc w x = μ.loc w x ^ k` using `MonoidHom.pow_apply μ.1 k _`. Rewrite using `[e1, h x hx, one_pow]`. Establish `hT` using `(hMu E μ e hμ).2`. Establish `hemb : ∀ {m : ℕ} (C : CD E m) (l : InfinitePlace E → DomWeight m) (k : ℕ), C.Inf (mW l) → ∀ v : InfinitePlace E, ∑ i, ((C.P i).twist (μ ^ k)).infChar v.embedding = (infOfWeight (l v)).map (· + (k : ℂ) * (e v : ℂ) / 2)`.

Introduce `m C l k hC v`. Establish `h1 : ∀ i, ((C.P i).twist (μ ^ k)).infChar v.embedding = ((C.P i).infChar v.embedding).map (· + (k : ℂ) * (e v : ℂ) / 2)` using `fun i => (hT (C.N i) k (C.P i) v).1`. Simplify using `only [h1]`. Rewrite using `[sum_map_eq, hC v.embedding, (hMW E m l v).1]`. Establish `hcon : ∀ {m : ℕ} (C : CD E m) (l : InfinitePlace E → DomWeight m) (k : ℕ), C.Inf (mW l) → ∀ v : InfinitePlace E, ∑ i, ((C.P i).twist (μ ^ k)).infChar (ComplexEmbedding.conjugate v.embedding) = (infOfWeight (l v)).map (fun t => -(t + (k : ℂ) * (e v : ℂ) / 2))`.

Introduce `m C l k hC v`. Establish `h1 : ∀ i, ((C.P i).twist (μ ^ k)).infChar (ComplexEmbedding.conjugate v.embedding) = ((C.P i).infChar (ComplexEmbedding.conjugate v.embedding)).map (· - (k : ℂ) * (e v : ℂ) / 2)` using `fun i => (hT (C.N i) k (C.P i) v).2`. Simplify using `only [h1]`. Rewrite using `[sum_map_eq, hC (ComplexEmbedding.conjugate v.embedding), (hMW E m l v).2, Multiset.map_map]`. Use `Multiset.map_congr rfl fun t _ => ?_` and prove the remaining obligations.

Simplify using `only [Function.comp_apply]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨D, hnot, ?_, ?_⟩` and prove the remaining obligations. Introduce `τ`. Break down `InfinitePlace.embedding_mk_eq τ with h | h` into its components or cases.

Use `⟨lam (InfinitePlace.mk τ), ?_⟩` and prove the remaining obligations. Rewrite using `[hinf τ, ← hlam (InfinitePlace.mk τ), ← hemb D₁ l₁ b h₁, ← hemb D₂ l₂ a h₂, h]`. Take `⟨lam', hl⟩` from `hDW (a + b) (lam (InfinitePlace.mk τ))`. Establish `hτ : τ = ComplexEmbedding.conjugate (InfinitePlace.mk τ).embedding`. Rewrite using `[h]`.

Conclude with `(star_star τ).symm`. Use `⟨lam', ?_⟩` and prove the remaining obligations. Rewrite using `[hinf τ, hl, ← hlam (InfinitePlace.mk τ), Multiset.map_add, Multiset.map_map, Multiset.map_map]`. Establish `e1` using `hcon D₁ l₁ b h₁ (InfinitePlace.mk τ)`. Establish `e2` using `hcon D₂ l₂ a h₂ (InfinitePlace.mk τ)`.

Rewrite `e1`, `e2` using `[← hτ]`. Rewrite using `[e1, e2]`. Both sides reduce to the same expression. Introduce `w B₁ B₂ hu s₁ s₂`. Establish `h` using `hsat w B₁ B₂ (hunr b hu) (hunr a hu) s₁ s₂`.

Rewrite `h` using `[hval, hval]`. Conclude with `h`.
-/
theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.twDataT :
    CDAddG → MuInf → MWAt → DualWt → TwDataT := by
  intro hAdd hMu hMW hDW E _ _ _ n a b hab ha hb μ e hμ l₁ l₂ lam hlam D₁ D₂ h₁ h₂
  subst hab
  obtain ⟨D, hnot, hsat, hinf⟩ := hAdd E a b D₁ D₂ (μ ^ b) (μ ^ a) ha hb
  have hval : ∀ (w : Pl E) (k : ℕ), (μ ^ k).val w = μ.val w ^ k :=
    fun w k => MonoidHom.pow_apply μ.1 k _
  have hunr : ∀ {w : Pl E} (k : ℕ), μ.UnrAt w → (μ ^ k).UnrAt w := by
    intro w k h x hx
    have e1 : (μ ^ k).loc w x = μ.loc w x ^ k := MonoidHom.pow_apply μ.1 k _
    rw [e1, h x hx, one_pow]
  have hT := (hMu E μ e hμ).2
  have hemb : ∀ {m : ℕ} (C : CD E m) (l : InfinitePlace E → DomWeight m) (k : ℕ), C.Inf (mW l) →
      ∀ v : InfinitePlace E, ∑ i, ((C.P i).twist (μ ^ k)).infChar v.embedding =
        (infOfWeight (l v)).map (· + (k : ℂ) * (e v : ℂ) / 2) := by
    intro m C l k hC v
    have h1 : ∀ i, ((C.P i).twist (μ ^ k)).infChar v.embedding =
        ((C.P i).infChar v.embedding).map (· + (k : ℂ) * (e v : ℂ) / 2) :=
      fun i => (hT (C.N i) k (C.P i) v).1
    simp only [h1]
    rw [sum_map_eq, hC v.embedding, (hMW E m l v).1]
  have hcon : ∀ {m : ℕ} (C : CD E m) (l : InfinitePlace E → DomWeight m) (k : ℕ), C.Inf (mW l) →
      ∀ v : InfinitePlace E, ∑ i, ((C.P i).twist (μ ^ k)).infChar (ComplexEmbedding.conjugate v.embedding) =
        (infOfWeight (l v)).map (fun t => -(t + (k : ℂ) * (e v : ℂ) / 2)) := by
    intro m C l k hC v
    have h1 : ∀ i, ((C.P i).twist (μ ^ k)).infChar (ComplexEmbedding.conjugate v.embedding) =
        ((C.P i).infChar (ComplexEmbedding.conjugate v.embedding)).map (· - (k : ℂ) * (e v : ℂ) / 2) :=
      fun i => (hT (C.N i) k (C.P i) v).2
    simp only [h1]
    rw [sum_map_eq, hC (ComplexEmbedding.conjugate v.embedding), (hMW E m l v).2, Multiset.map_map]
    refine Multiset.map_congr rfl fun t _ => ?_
    simp only [Function.comp_apply]
    ring
  refine ⟨D, hnot, ?_, ?_⟩
  · intro τ
    rcases InfinitePlace.embedding_mk_eq τ with h | h
    · refine ⟨lam (InfinitePlace.mk τ), ?_⟩
      rw [hinf τ, ← hlam (InfinitePlace.mk τ), ← hemb D₁ l₁ b h₁, ← hemb D₂ l₂ a h₂, h]
    · obtain ⟨lam', hl⟩ := hDW (a + b) (lam (InfinitePlace.mk τ))
      have hτ : τ = ComplexEmbedding.conjugate (InfinitePlace.mk τ).embedding := by
        rw [h]
        exact (star_star τ).symm
      refine ⟨lam', ?_⟩
      rw [hinf τ, hl, ← hlam (InfinitePlace.mk τ), Multiset.map_add, Multiset.map_map, Multiset.map_map]
      have e1 := hcon D₁ l₁ b h₁ (InfinitePlace.mk τ)
      have e2 := hcon D₂ l₂ a h₂ (InfinitePlace.mk τ)
      rw [← hτ] at e1 e2
      rw [e1, e2]
      rfl
  · intro w B₁ B₂ hu s₁ s₂
    have h := hsat w B₁ B₂ (hunr b hu) (hunr a hu) s₁ s₂
    rw [hval, hval] at h
    exact h
