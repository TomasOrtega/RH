import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.GammaZetaNablaCancel

noncomputable section

open NumberField
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.gamma_zeta_nabla_cancel

open PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.SpectralAccumulation

namespace RegH

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem conj_ne {E : Type} [Field E] [NumberField E] [IsCMField E] (τ : E →+* ℂ) :
    (starRingEnd ℂ).comp τ ≠ τ := by
  intro h
  have hc : (InfinitePlace.mk τ).IsComplex := IsTotallyComplex.isComplex _
  rw [InfinitePlace.isComplex_iff] at hc
  apply hc
  have hr : ComplexEmbedding.IsReal τ := by
    rw [ComplexEmbedding.isReal_iff]
    exact RingHom.ext fun x => by simpa using congrArg (fun f : E →+* ℂ => f x) h
  rcases InfinitePlace.embedding_mk_eq τ with e | e
  · rw [e]; exact hr
  · rw [e, ComplexEmbedding.isReal_iff.1 hr]; exact hr

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem conj_eq_conjugate {E : Type} [Field E] (τ : E →+* ℂ) :
    (starRingEnd ℂ).comp τ = ComplexEmbedding.conjugate τ := RingHom.ext fun _ => rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem mk_conj {E : Type} [Field E] [NumberField E] (τ : E →+* ℂ) :
    InfinitePlace.mk ((starRingEnd ℂ).comp τ) = InfinitePlace.mk τ := by
  rw [conj_eq_conjugate, InfinitePlace.mk_conjugate_eq]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules.
-/
theorem dec_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (τ : E →+* ℂ) :
    decide ((starRingEnd ℂ).comp τ = (InfinitePlace.mk ((starRingEnd ℂ).comp τ)).embedding) =
      !decide (τ = (InfinitePlace.mk τ).embedding) := by
  rw [mk_conj]
  have hne := conj_ne τ
  rcases InfinitePlace.embedding_mk_eq τ with e | e
  · rw [e]
    simp [hne]
  · rw [e, ← conj_eq_conjugate]
    have : τ ≠ (starRingEnd ℂ).comp τ := fun h => hne h.symm
    simp [this]

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem infOf_not {n : ℕ} (lam : Fin n → ℤ) (s : Bool) (a : Fin n) :
    PositivityTheory.RgBcC.infOf lam (!s) a = -PositivityTheory.RgBcC.infOf lam s a := by
  cases s <;> simp [PositivityTheory.RgBcC.infOf]

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem infOf_im {n : ℕ} (lam : Fin n → ℤ) (s : Bool) (a : Fin n) : (PositivityTheory.RgBcC.infOf lam s a).im = 0 := by
  cases s <;> simp [PositivityTheory.RgBcC.infOf]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Apply the first step, then apply the next step to every resulting obligation. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem infOf_sep {n : ℕ} (lam : Fin n → ℤ) (hl : Antitone lam) (s : Bool) (a b : Fin n) (hab : a ≠ b) :
    (1 : ℝ) ≤ ‖PositivityTheory.RgBcC.infOf lam s a - PositivityTheory.RgBcC.infOf lam s b‖ := by
  have key : ∀ a b : Fin n, a < b → (1 : ℝ) ≤ ((lam a : ℝ) - (a : ℕ)) - ((lam b : ℝ) - (b : ℕ)) := by
    intro a b h
    have h1 : lam b ≤ lam a := hl h.le
    have h2 : (a : ℕ) + 1 ≤ (b : ℕ) := h
    have h1' : (lam b : ℝ) ≤ lam a := by exact_mod_cast h1
    have h2' : ((a : ℕ) : ℝ) + 1 ≤ (b : ℕ) := by exact_mod_cast h2
    linarith
  have e : ∀ a b : Fin n, PositivityTheory.RgBcC.infOf lam s a - PositivityTheory.RgBcC.infOf lam s b =
      ((if s then 1 else -1 : ℂ)) * ((((lam a : ℝ) - (a : ℕ)) - ((lam b : ℝ) - (b : ℕ)) : ℝ) : ℂ) := by
    intro a b
    simp only [PositivityTheory.RgBcC.infOf]
    push_cast
    ring
  have hs : ‖(if s then 1 else -1 : ℂ)‖ = 1 := by cases s <;> simp
  rcases lt_or_gt_of_ne hab with h | h
  · rw [e, norm_mul, hs, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (key a b h).trans (le_abs_self _)
  · rw [e, norm_mul, hs, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have := key b a h
    exact le_abs.mpr (Or.inr (by linarith))

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Evaluate the numerical expressions.
-/
theorem infOf_inj {n : ℕ} (lam : Fin n → ℤ) (hl : Antitone lam) (s : Bool) :
    Function.Injective (PositivityTheory.RgBcC.infOf lam s) := by
  intro a b h
  by_contra hab
  have := infOf_sep lam hl s a b hab
  rw [h, sub_self, norm_zero] at this
  norm_num at this

end RegH

open RegH

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

A detailed English derivation is pending.
-/
theorem regDom : RegDom := by
  intro E _ _ _ n l
  refine ⟨fun τ => ⟨?_, ?_⟩, fun τ => ⟨?_, ?_⟩⟩
  · intro x hx
    simp only [mOf, Multiset.mem_map] at hx
    obtain ⟨a, -, rfl⟩ := hx
    exact infOf_im _ _ _
  · simp only [mOf]
    rw [mk_conj, show decide ((starRingEnd ℂ).comp τ = (InfinitePlace.mk τ).embedding) =
        !decide (τ = (InfinitePlace.mk τ).embedding) from by rw [← dec_conj τ, mk_conj], Multiset.map_map]
    congr 1
    funext a
    exact infOf_not _ _ _
  · simp only [mOf]
    exact Multiset.Nodup.map (infOf_inj _ (l _).anti _) Finset.univ.nodup
  · intro x hx y hy hxy
    simp only [mOf, Multiset.mem_map] at hx hy
    obtain ⟨a, -, rfl⟩ := hx
    obtain ⟨b, -, rfl⟩ := hy
    have hab : a ≠ b := fun h => hxy (by rw [h])
    exact le_trans (by norm_num) (infOf_sep _ (l _).anti _ a b hab)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem reg_of (h : GelfInj) : Reg := by
  intro E _ _ _ n l χ hχ
  have e : mOf χ = mOf (fun v => PositivityTheory.RgBcC.infOf (l v).w) := by
    funext τ
    simp only [mOf]
    exact h n _ _ (hχ _ _)
  rw [e]
  exact regDom E n l

end PositivityTheory.Rg.BcB.F.gamma_zeta_nabla_cancel

end
