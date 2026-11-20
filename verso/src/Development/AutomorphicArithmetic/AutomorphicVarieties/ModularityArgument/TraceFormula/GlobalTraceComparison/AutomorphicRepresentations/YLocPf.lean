import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt

open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc

/- English proof (translation)
Introduce `hP hO E _ _ _ n S Z N hS hZ hG π y i hi f hf x hx`. Take `⟨w, b⟩` from `i`. Set `F : ∀ w', Bool → _` to `fun w' b' => if h : w' = w ∧ b' = b then h.1 ▸ f else ((N w' : Set _).indicator 1)`. Establish `hFi : F w b = f` using `by simp [F]`. Establish `hFam : Fam S N {(w, b)} F`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `j hj`. Take `rfl` from `Finset.mem_singleton.mp hj`. Conclude with `⟨hi, by simpa [hFi] using hf⟩`. Introduce and unpack `⟨w', b'⟩ _ hj`.

Establish `hne : ¬ (w' = w ∧ b' = b)`. Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `hj (Finset.mem_singleton_self _)`. Simplify using `[F, hne]`. Establish `h1` using `hO E n S Z N hS hZ hG {(w, b)} F hFam x (y.fix hx)`.

Establish `h2` using `y.act _ (hP E n S Z N hS hZ hG {(w, b)} F hFam) ⟨x, hx⟩`. Establish `h3 : Lw N w b f x = ((y.r (pf S F) ⟨x, hx⟩ : y.Y) : _)`. Rewrite using `[h2]`. Use `show _ = Lv _ _ _ x`. Rewrite using `[h1]`.

Simplify using `[hFi]`. Use `show Lw N w b f x ∈ y.Y`. Rewrite using `[h3]`. Conclude with `(y.r (pf S F) ⟨x, hx⟩).2`.
-/
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.yLoc_pf :
    PfHecke → ProdOp → YLoc := by
  intro hP hO E _ _ _ n S Z N hS hZ hG π y i hi f hf x hx
  classical
  obtain ⟨w, b⟩ := i
  let F : ∀ w', Bool → _ := fun w' b' =>
    if h : w' = w ∧ b' = b then h.1 ▸ f else ((N w' : Set _).indicator 1)
  have hFi : F w b = f := by simp [F]
  have hFam : Fam S N {(w, b)} F := by
    refine ⟨?_, ?_⟩
    · intro j hj
      obtain rfl := Finset.mem_singleton.mp hj
      exact ⟨hi, by simpa [hFi] using hf⟩
    · rintro ⟨w', b'⟩ _ hj
      have hne : ¬ (w' = w ∧ b' = b) := by
        rintro ⟨rfl, rfl⟩
        exact hj (Finset.mem_singleton_self _)
      simp [F, hne]
  have h1 := hO E n S Z N hS hZ hG {(w, b)} F hFam x (y.fix hx)
  have h2 := y.act _ (hP E n S Z N hS hZ hG {(w, b)} F hFam) ⟨x, hx⟩
  have h3 : Lw N w b f x = ((y.r (pf S F) ⟨x, hx⟩ : y.Y) : _) := by
    rw [h2]
    show _ = Lv _ _ _ x
    rw [h1]
    simp [hFi]
  show Lw N w b f x ∈ y.Y
  rw [h3]
  exact (y.r (pf S F) ⟨x, hx⟩).2
