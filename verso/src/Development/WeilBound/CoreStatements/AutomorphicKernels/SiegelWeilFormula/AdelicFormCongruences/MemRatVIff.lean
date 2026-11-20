import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LowerRankDatum
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood
import Development.WeilBound.ThetaLifts.LatticeBasics.IsCompactIntV

set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw SiegelEisensteinSeries.Grp PositivityTheory.SiegelWeilFormula.kfour

namespace PositivityTheory.SiegelWeilFormula.Afc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Proceed by induction on `h using AddSubgroup.closure_induction with`. Consider the case `mem x hx => obtain ⟨v, rfl⟩ := hx`. Conclude with `⟨v, rfl⟩`.

Consider the case `zero => exact ⟨0, by funext i; simp [GlobalTheory.ThK.incV]⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨v, rfl⟩` from `hx`. Take `⟨v', rfl⟩` from `hy`. Conclude with `⟨v + v', by funext i; simp [GlobalTheory.ThK.incV]⟩`.

Consider the case `neg x _ hx`. Take `⟨v, rfl⟩` from `hx`. Conclude with `⟨-v, by funext i; simp [GlobalTheory.ThK.incV]⟩`. Introduce and unpack `⟨v, rfl⟩`. Conclude with `AddSubgroup.subset_closure ⟨v, rfl⟩`.
-/
theorem mem_ratV_iff {d : SD σ} (L : LD d) (u : Fin L.n → AE F E) :
    u ∈ L.ratV ↔ ∃ v : Fin L.n → E, u = GlobalTheory.ThK.incV F v := by
  constructor
  · intro h
    induction h using AddSubgroup.closure_induction with
    | mem x hx => obtain ⟨v, rfl⟩ := hx; exact ⟨v, rfl⟩
    | zero => exact ⟨0, by funext i; simp [GlobalTheory.ThK.incV]⟩
    | add x y _ _ hx hy =>
      obtain ⟨v, rfl⟩ := hx
      obtain ⟨v', rfl⟩ := hy
      exact ⟨v + v', by funext i; simp [GlobalTheory.ThK.incV]⟩
    | neg x _ hx =>
      obtain ⟨v, rfl⟩ := hx
      exact ⟨-v, by funext i; simp [GlobalTheory.ThK.incV]⟩
  · rintro ⟨v, rfl⟩
    exact AddSubgroup.subset_closure ⟨v, rfl⟩

/- English proof (translation)
Establish `hD : ∀ p q, σ (dbl Y.J p q) = s * dbl Y.J q p`. Introduce `p q`. Apply the tactic sequence `rcases p with i | i <;> rcases q with j | j <;> simp [dbl, hJ]`. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hσ, hD, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sigma_frame {n : ℕ} {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E} (hσ : ∀ a, σ (σ a) = a) (s : E) (hJ : ∀ i j, σ (Y.J j i) = s * Y.J i j) (k l : Fin n ⊕ Fin n) :
    σ ((b.1ᵀ * dbl Y.J * b.1.map σ) k l) = s * (b.1ᵀ * dbl Y.J * b.1.map σ) l k := by
  have hD : ∀ p q, σ (dbl Y.J p q) = s * dbl Y.J q p := by
    intro p q
    rcases p with i | i <;> rcases q with j | j <;> simp [dbl, hJ]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hσ, hD, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

/- English proof (translation)
Establish `i0 : Fin n` using `⟨0, hn⟩`. Establish `h` using `sigma_frame (b := b) hσ (s : E) hJ (Sum.inl i0) (Sum.inr i0)`. Rewrite `h` using `[hb]`. Simplify using `at h`. Establish `h2 : s * (ε : ℤ) = 1` using `by exact_mod_cast h.symm`.

Establish `h3 : (ε : ℤ) * ε = 1` using `by rw [← Units.val_mul, Int.units_mul_self, Units.val_one]`. Take the linear combination `(-(ε : ℤ)) * h2 + s * h3`.
-/
theorem eps_of_sign {n : ℕ} {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E} (hσ : ∀ a, σ (σ a) = a) (hn : 1 ≤ n) {ε : ℤˣ}
    (hb : FrameEq σ Y b ε) (s : ℤ) (hJ : ∀ i j, σ (Y.J j i) = (s : E) * Y.J i j) : (ε : ℤ) = s := by
  have i0 : Fin n := ⟨0, hn⟩
  have h := sigma_frame (b := b) hσ (s : E) hJ (Sum.inl i0) (Sum.inr i0)
  rw [hb] at h
  simp at h
  have h2 : s * (ε : ℤ) = 1 := by exact_mod_cast h.symm
  have h3 : (ε : ℤ) * ε = 1 := by rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  linear_combination (-(ε : ℤ)) * h2 + s * h3

end PositivityTheory.SiegelWeilFormula.Afc

end
