import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LowerRankDatum
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.FrameSignEqHermitianSign

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Avac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Establish `h0 : A.J = 0`. Use extensionality with `i j`. Establish `a` using `h1.herm i j`. Establish `b` using `h2.skew i j`. Rewrite `b` using `[a]`.

Establish `: (2 : E) * A.J i j = 0` using `by linear_combination b`. Simplify using `using this`. Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Take `⟨hrs, M, hM⟩` from `h1.sig w`. Rewrite `hM` using `[h0, Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul]`.

Break down `Nat.eq_zero_or_pos r with hr | hr` into its components or cases. Establish `hs : 0 < s` using `by omega`. Use `congrFun (congrFun hM (Sum.inr ⟨0, hs⟩)) (Sum.inr ⟨0, hs⟩)` as an intermediate fact. Simplify using `at this`. Use `congrFun (congrFun hM (Sum.inl ⟨0, hr⟩)) (Sum.inl ⟨0, hr⟩)` as an intermediate fact.

Simplify using `at this`.
-/
theorem not_herm_skew {B : Base F E} {m r s : ℕ} (hm : 1 ≤ m) {A : Spc F E m} (h1 : A.IsHerm σ B r s)
    (h2 : A.IsSkew σ B r s) : False := by
  have h0 : A.J = 0 := by
    ext i j
    have a := h1.herm i j
    have b := h2.skew i j
    rw [a] at b
    have : (2 : E) * A.J i j = 0 := by linear_combination b
    simpa using this
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨hrs, M, hM⟩ := h1.sig w
  rw [h0, Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul] at hM
  rcases Nat.eq_zero_or_pos r with hr | hr
  · have hs : 0 < s := by omega
    have := congrFun (congrFun hM (Sum.inr ⟨0, hs⟩)) (Sum.inr ⟨0, hs⟩)
    simp at this
  · have := congrFun (congrFun hM (Sum.inl ⟨0, hr⟩)) (Sum.inl ⟨0, hr⟩)
    simp at this

/- English proof (translation)
Take `⟨ε, hε⟩` from `d.ok.frame.1`. Take `⟨ε', hε'⟩` from `L.ok.frame.1`. Establish `s` using `KWhit.rel_sign d ε hε`. Establish `s'` using `KWhit.rel_sign L.sd ε' hε'`. Use `⟨ε, hε, ?_⟩` and prove the remaining obligations.

It suffices to establish `e : ε' = ε by rw [← e]; exact hε'`. Apply the tactic sequence `rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩ <;> rcases L.ok.sign with ⟨hA', hY'⟩ | ⟨hA', hY'⟩`. Rewrite using `[s.1 hY, s'.1 hY']`. Conclude with `(not_herm_skew d.ok.hm hA hA').elim`. Conclude with `(not_herm_skew d.ok.hm hA' hA).elim`.

Rewrite using `[s.2 hY, s'.2 hY']`.
-/
theorem eps_eq {d : SD σ} (L : LD d) : ∃ ε : ℤˣ, d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 ∧
    L.b.1ᵀ * dbl L.Y.J * L.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 := by
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  obtain ⟨ε', hε'⟩ := L.ok.frame.1
  have s := KWhit.rel_sign d ε hε
  have s' := KWhit.rel_sign L.sd ε' hε'
  refine ⟨ε, hε, ?_⟩
  suffices e : ε' = ε by rw [← e]; exact hε'
  rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩ <;> rcases L.ok.sign with ⟨hA', hY'⟩ | ⟨hA', hY'⟩
  · rw [s.1 hY, s'.1 hY']
  · exact (not_herm_skew d.ok.hm hA hA').elim
  · exact (not_herm_skew d.ok.hm hA' hA).elim
  · rw [s.2 hY, s'.2 hY']

end PositivityTheory.SiegelWeilFormula.Avac

end
