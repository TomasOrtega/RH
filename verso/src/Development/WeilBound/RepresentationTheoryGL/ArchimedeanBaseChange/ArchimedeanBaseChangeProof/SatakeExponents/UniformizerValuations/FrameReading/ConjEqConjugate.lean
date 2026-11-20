import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.GammaZetaNablaCancel

noncomputable section

open NumberField
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.gamma_zeta_nabla_cancel

open PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.SpectralAccumulation

namespace RegH

/- English proof (translation)
Introduce `h`. Establish `hc : (InfinitePlace.mk τ).IsComplex` using `IsTotallyComplex.isComplex _`. Rewrite `hc` using `[InfinitePlace.isComplex_iff]`. Apply `hc` to reduce the goal to its premises. Establish `hr : ComplexEmbedding.IsReal τ`.

Rewrite using `[ComplexEmbedding.isReal_iff]`. Conclude with `RingHom.ext fun x => by simpa using congrArg (fun f : E →+* ℂ => f x) h`. Break down `InfinitePlace.embedding_mk_eq τ with e | e` into its components or cases. Rewrite using `[e]`. Conclude with `hr`.

Rewrite using `[e, ComplexEmbedding.isReal_iff.1 hr]`. Conclude with `hr`.
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
The claim follows from `RingHom.ext fun _ => rfl`.
-/
theorem conj_eq_conjugate {E : Type} [Field E] (τ : E →+* ℂ) :
    (starRingEnd ℂ).comp τ = ComplexEmbedding.conjugate τ := RingHom.ext fun _ => rfl

/- English proof (translation)
Rewrite using `[conj_eq_conjugate, InfinitePlace.mk_conjugate_eq]`.
-/
theorem mk_conj {E : Type} [Field E] [NumberField E] (τ : E →+* ℂ) :
    InfinitePlace.mk ((starRingEnd ℂ).comp τ) = InfinitePlace.mk τ := by
  rw [conj_eq_conjugate, InfinitePlace.mk_conjugate_eq]

/- English proof (translation)
Rewrite using `[mk_conj]`. Establish `hne` using `conj_ne τ`. Break down `InfinitePlace.embedding_mk_eq τ with e | e` into its components or cases. Rewrite using `[e]`. Simplify using `[hne]`.

Rewrite using `[e, ← conj_eq_conjugate]`. Establish `: τ ≠ (starRingEnd ℂ).comp τ` using `fun h => hne h.symm`. Simplify using `[this]`.
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
Apply the tactic sequence `cases s <;> simp [PositivityTheory.RgBcC.infOf]`.
-/
theorem infOf_not {n : ℕ} (lam : Fin n → ℤ) (s : Bool) (a : Fin n) :
    PositivityTheory.RgBcC.infOf lam (!s) a = -PositivityTheory.RgBcC.infOf lam s a := by
  cases s <;> simp [PositivityTheory.RgBcC.infOf]

/- English proof (translation)
Apply the tactic sequence `cases s <;> simp [PositivityTheory.RgBcC.infOf]`.
-/
theorem infOf_im {n : ℕ} (lam : Fin n → ℤ) (s : Bool) (a : Fin n) : (PositivityTheory.RgBcC.infOf lam s a).im = 0 := by
  cases s <;> simp [PositivityTheory.RgBcC.infOf]

/- English proof (translation)
Establish `key : ∀ a b : Fin n, a < b → (1 : ℝ) ≤ ((lam a : ℝ) - (a : ℕ)) - ((lam b : ℝ) - (b : ℕ))`. Introduce `a b h`. Establish `h1 : lam b ≤ lam a` using `hl h.le`. Establish `h2 : (a : ℕ) + 1 ≤ (b : ℕ)` using `h`. Establish `h1' : (lam b : ℝ) ≤ lam a` using `by exact_mod_cast h1`.

Establish `h2' : ((a : ℕ) : ℝ) + 1 ≤ (b : ℕ)` using `by exact_mod_cast h2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e : ∀ a b : Fin n, PositivityTheory.RgBcC.infOf lam s a - PositivityTheory.RgBcC.infOf lam s b = ((if s then 1 else -1 : ℂ)) * ((((lam a : ℝ) - (a : ℕ)) - ((lam b : ℝ) - (b : ℕ)) : ℝ) : ℂ)`. Introduce `a b`. Simplify using `only [PositivityTheory.RgBcC.infOf]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Apply the tactic sequence `have hs : ‖(if s then 1 else -1 : ℂ)‖ = 1 := by cases s <;> simp`. Break down `lt_or_gt_of_ne hab with h | h` into its components or cases. Rewrite using `[e, norm_mul, hs, one_mul, Complex.norm_real, Real.norm_eq_abs]`.

Conclude with `(key a b h).trans (le_abs_self _)`. Rewrite using `[e, norm_mul, hs, one_mul, Complex.norm_real, Real.norm_eq_abs]`. Use `key b a h` as an intermediate fact. Conclude with `le_abs.mpr (Or.inr (by linarith))`.
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
Introduce `a b h`. Assume the negation of the conclusion as `hab`. Use `infOf_sep lam hl s a b hab` as an intermediate fact. Rewrite `this` using `[h, sub_self, norm_zero]`. Evaluate the numerical expressions using `at this`.
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
Introduce `E _ _ _ n l`. Use `⟨fun τ => ⟨?_, ?_⟩, fun τ => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Introduce `x hx`. Simplify using `only [mOf, Multiset.mem_map] at hx`. Take `⟨a, -, rfl⟩` from `hx`.

Conclude with `infOf_im _ _ _`. Simplify using `only [mOf]`. Rewrite using `[mk_conj, show decide ((starRingEnd ℂ).comp τ = (InfinitePlace.mk τ).embedding) = !decide (τ = (InfinitePlace.mk τ).embedding) from by rw [← dec_conj τ, mk_conj], Multiset.map_map]`. Use `congr 1`. Use function extensionality and compare the values at `a`.

Conclude with `infOf_not _ _ _`. Simplify using `only [mOf]`. Conclude with `Multiset.Nodup.map (infOf_inj _ (l _).anti _) Finset.univ.nodup`. Introduce `x hx y hy hxy`. Simplify using `only [mOf, Multiset.mem_map] at hx hy`.

Take `⟨a, -, rfl⟩` from `hx`. Take `⟨b, -, rfl⟩` from `hy`. Establish `hab : a ≠ b` using `fun h => hxy (by rw [h])`. Conclude with `le_trans (by norm_num) (infOf_sep _ (l _).anti _ a b hab)`.
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
Introduce `E _ _ _ n l χ hχ`. Establish `e : mOf χ = mOf (fun v => PositivityTheory.RgBcC.infOf (l v).w)`. Use function extensionality and compare the values at `τ`. Simplify using `only [mOf]`. Conclude with `h n _ _ (hχ _ _)`.

Rewrite using `[e]`. Conclude with `regDom E n l`.
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
