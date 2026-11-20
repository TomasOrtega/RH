import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SumExpSt
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArithFrobeniusEmbeddingPermCmConjStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineBlockLatticesOverPowerSeriesRingStatement

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

namespace GlobalTheory.ExpLink

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Use extensionality with `x`. Simplify using `[cj, IsCMField.complexConj_apply_apply]`.
-/
theorem cj_cj (τ : E →+* PadicAlgCl l) : cj (cj τ) = τ := by
  ext x; simp [cj, IsCMField.complexConj_apply_apply]

/- English proof (translation)
Introduce `a b h` and use `by rw [← cj_cj a, h, cj_cj]`.
-/
theorem cj_injective : Function.Injective (cj : (E →+* PadicAlgCl l) → (E →+* PadicAlgCl l)) := fun a b h => by
  rw [← cj_cj a, h, cj_cj]

open Classical in

def glue {ι X : Type} [Inhabited X] (inc : ι → (E →+* PadicAlgCl l)) (f g : ι → X) (i : E →+* PadicAlgCl l) : X :=
  if h : ∃ τ, inc τ = i then f h.choose else if h' : ∃ τ, cj (inc τ) = i then g h'.choose else default

/- English proof (translation)
Establish `h : ∃ τ', inc τ' = inc τ` using `⟨τ, rfl⟩`. Rewrite using `[glue, dif_pos h]`. Conclude with `congrArg f (hH.1 h.choose_spec)`.
-/
theorem glue_inc {ι X : Type} [Inhabited X] {inc : ι → (E →+* PadicAlgCl l)} (hH : IsHalf inc) (f g : ι → X) (τ : ι) :
    glue inc f g (inc τ) = f τ := by
  have h : ∃ τ', inc τ' = inc τ := ⟨τ, rfl⟩
  rw [glue, dif_pos h]
  exact congrArg f (hH.1 h.choose_spec)

/- English proof (translation)
Establish `h : ¬ ∃ τ', inc τ' = cj (inc τ)` using `fun ⟨τ', h'⟩ => hH.2.1 τ τ' h'.symm`. Establish `h' : ∃ τ', cj (inc τ') = cj (inc τ)` using `⟨τ, rfl⟩`. Rewrite using `[glue, dif_neg h, dif_pos h']`. Conclude with `congrArg g (hH.1 (cj_injective h'.choose_spec))`.
-/
theorem glue_cj {ι X : Type} [Inhabited X] {inc : ι → (E →+* PadicAlgCl l)} (hH : IsHalf inc) (f g : ι → X) (τ : ι) :
    glue inc f g (cj (inc τ)) = g τ := by
  have h : ¬ ∃ τ', inc τ' = cj (inc τ) := fun ⟨τ', h'⟩ => hH.2.1 τ τ' h'.symm
  have h' : ∃ τ', cj (inc τ') = cj (inc τ) := ⟨τ, rfl⟩
  rw [glue, dif_neg h, dif_pos h']
  exact congrArg g (hH.1 (cj_injective h'.choose_spec))

def labels {ι : Type} (inc : ι → (E →+* PadicAlgCl l)) (P : Par) (W : Wts ι) (mu : ι → ℕ → ℕ) :
    Formalism.CohomologicalDescent.WorkedExample.Labels (E →+* PadicAlgCl l) P.Nr where
  cc := cj
  Φ := Set.range inc
  U := glue inc (fun τ a => W.U P τ (a : ℕ)) (fun τ a => (h0 P : ℤ) - W.U P τ ((Fin.rev a : Fin P.Nr) : ℕ))
  U' := glue inc (fun τ a => Formalism.CohomologicalDescent.UnitNormBounds.UN P.Nr (mu τ) (a : ℕ))
    (fun τ a => (h0 P : ℤ) - Formalism.CohomologicalDescent.UnitNormBounds.UN P.Nr (mu τ) ((Fin.rev a : Fin P.Nr) : ℕ))
  bot := glue inc (fun τ => W.bot P τ) (fun τ => (h0 P : ℤ) - (W.bot P τ + (P.t : ℤ) - 1))

/- English proof (translation)
Establish `h1` using `hOk.block τ (kc P + W.j τ + P.t - 1 - s) (by omega) (by omega)`. Establish `h2` using `hOk.block τ (kc P + W.j τ + P.t - 1) (by omega) (by omega)`. Simplify using `only [Wts.bot, Wts.U, Formalism.CohomologicalDescent.UnitNormBounds.UN, h1, h2]`. Use linear arithmetic over natural numbers and integers.
-/
theorem U_block {ι : Type} {P : Par} {W : Wts ι} (hOk : W.Ok P) (τ : ι) (s : ℕ) (hs : s < P.t) :
    W.U P τ (kc P + W.j τ + P.t - 1 - s) = W.bot P τ + (s : ℤ) := by
  have h1 := hOk.block τ (kc P + W.j τ + P.t - 1 - s) (by omega) (by omega)
  have h2 := hOk.block τ (kc P + W.j τ + P.t - 1) (by omega) (by omega)
  simp only [Wts.bot, Wts.U, Formalism.CohomologicalDescent.UnitNormBounds.UN, h1, h2]
  omega

/- English proof (translation)
Introduce `hBS E Ω _ _ _ _ _ _ l _ hl2 hdisc ι inc hH`. Take `⟨σ, hσF, hσc⟩` from `GlobalTheory.T.exists_arithFrobenius_embedding_perm_cmConj E l hdisc`. Use `choose hf hb using hH.2.2`. Use `set fr : ℕ → ι → ι := fun _ τ => hf (σ (inc τ)) with hfr`. Use `set cjj : ℕ → ι → Bool := fun _ τ => decide (σ (inc τ) ≠ inc (hf (σ (inc τ)))) with hcjj`.

Use `⟨fr, cjj, ?_⟩` and prove the remaining obligations. Introduce `P W hP hOk hbox mu hLk hBF τ`. Take `⟨ep, J, bot, hep, hBP, hJ⟩` from `hBF`. Establish `hall : ∀ i, ∃ τ', i = ep (inc τ') ∨ i = ep (cj (inc τ'))`. Introduce `i`.

Break down `hep with rfl | rfl` into its components or cases. Break down `hb i with h | h` into its components or cases. Conclude with `⟨hf i, Or.inl h⟩`. Conclude with `⟨hf i, Or.inr h⟩`. Break down `hb i with h | h` into its components or cases.

Conclude with `⟨hf i, Or.inr (by rw [cj_cj]; exact h)⟩`. Conclude with `⟨hf i, Or.inl h⟩`. Establish `hUN : ∀ τ' (a : Fin P.Nr), 0 ≤ Formalism.CohomologicalDescent.UnitNormBounds.UN P.Nr (mu τ') a ∧ Formalism.CohomologicalDescent.UnitNormBounds.UN P.Nr (mu τ') a ≤ (h0 P : ℤ)`. Introduce `τ' a`. Establish `h1` using `((hLk τ').2.2.1 a).2`.

Establish `ha` using `a.2`. Establish `h2` using `hbox τ' 0 (by omega)`. Simplify using `only [Wts.U, Formalism.CohomologicalDescent.UnitNormBounds.UN] at h2 ⊢`. Apply the tactic sequence `constructor <;> omega`. Establish `hJb : ∀ i a, 0 ≤ J i a ∧ J i a ≤ (h0 P : ℤ)`.

Introduce `i a`. Apply the tactic sequence `obtain ⟨τ', h | h⟩ := hall i <;> subst h`. Rewrite using `[((hJ τ').1 a).1]`. Conclude with `hUN τ' a`. Rewrite using `[((hJ τ').1 a).2]`.

Use `hUN τ' (Fin.rev a)` as an intermediate fact. Apply the tactic sequence `constructor <;> linarith [this.1, this.2]`. Establish `hbb : ∀ i (s : Fin P.t), 0 ≤ bot i + ((s : ℕ) : ℤ) ∧ bot i + ((s : ℕ) : ℤ) ≤ (h0 P : ℤ)`. Introduce `i s`. Establish `hs` using `s.2`.

Establish `hr` using `hOk.what₂`. Apply the tactic sequence `obtain ⟨τ', h | h⟩ := hall i <;> subst h`. Rewrite using `[(hJ τ').2.1]`. Establish `e` using `U_block hOk τ' s hs`. Establish `b` using `hbox τ' (kc P + W.j τ' + P.t - 1 - s) (by have := hr τ'; omega)`.

Rewrite `b` using `[e]`. Conclude with `b`. Rewrite using `[(hJ τ').2.2]`. Establish `e` using `U_block hOk τ' (P.t - 1 - s) (by omega)`. Establish `b` using `hbox τ' (kc P + W.j τ' + P.t - 1 - (P.t - 1 - s)) (by have := hr τ'; omega)`.

Rewrite `b` using `[e]`. Apply the tactic sequence `constructor <;> omega`. Take `⟨O', F, L', _, _, _, _, _, _, I, _, Wl, u, c, kap, ζ, em, jj, hN⟩` from `GlobalTheory.T.crystalline_block_lattices_over_power_series_ring hBS E Ω l hl2 hdisc σ hσF P.Nr P.t (h0 P) J bot hJb hbb hBP`. Establish `hn : kc P + (reFr W fr cjj).j τ + P.t + (reFr W fr cjj).q τ = P.Nr` using `hOk.what₂ τ`. Unfold `LatticeLink`.

Rewrite using `[hn]`. Use `⟨E →+* PadicAlgCl l, inferInstance, σ, ‹_›, O', F, L', ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, I, ‹_›, Wl, u, c, labels inc P W mu, fun _ => 1 - (P.Nr : ℤ), ep, J, bot, kap, ζ, em, jj, inc, ?_⟩` and prove the remaining obligations. Use `⟨?_, ?_, ?_, hN, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `⟨cj_cj, fun i => hσc i, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`.

Break down `hb i with h | h` into its components or cases. Conclude with `Or.inl ⟨hf i, h.symm⟩`. Conclude with `Or.inr ⟨hf i, by show inc (hf i) = cj i; rw [← cj_cj (inc (hf i)), ← h]⟩`. Introduce `i a`. Take `⟨τ', rfl | rfl⟩ : ∃ τ', i = inc τ' ∨ i = cj (inc τ')` from `⟨hf i, hb i⟩`.

Simplify using `only [labels, glue_inc hH, glue_cj hH]`. Simplify using `only [labels, glue_inc hH, glue_cj hH, cj_cj, Fin.rev_rev, sub_sub_cancel]`. Introduce `i a`. Take `⟨τ', rfl | rfl⟩ : ∃ τ', i = inc τ' ∨ i = cj (inc τ')` from `⟨hf i, hb i⟩`. Simplify using `only [labels, glue_inc hH, glue_cj hH]`.

Simplify using `only [labels, glue_inc hH, glue_cj hH, cj_cj, Fin.rev_rev, sub_sub_cancel]`. Introduce `i`. Take `⟨τ', rfl | rfl⟩ : ∃ τ', i = inc τ' ∨ i = cj (inc τ')` from `⟨hf i, hb i⟩`. Simplify using `only [labels, glue_inc hH, glue_cj hH]`. Simplify using `only [labels, glue_inc hH, glue_cj hH, cj_cj]`.

Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `_ ⟨τ', rfl⟩`. Establish `hr` using `hOk.what₂ τ'`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a b hab`.

Establish `hab' : (a : ℕ) < b` using `hab`. Establish `h1` using `hOk.anti τ' a b hab'.le b.2`. Simplify using `only [labels, glue_inc hH, Wts.U, Formalism.CohomologicalDescent.UnitNormBounds.UN]`. Use linear arithmetic over natural numbers and integers. Introduce `a b hab`.

Establish `hab' : (a : ℕ) < b` using `hab`. Establish `h1` using `(hLk τ').1 hab.le`. Simplify using `only [Formalism.CohomologicalDescent.LD.res] at h1`. Simplify using `only [labels, glue_inc hH, Formalism.CohomologicalDescent.UnitNormBounds.UN]`. Use linear arithmetic over natural numbers and integers.

Introduce `s`. Establish `hs` using `s.2`. Use `⟨⟨kc P + W.j τ' + P.t - 1 - s, by omega⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [labels, glue_inc hH]`. Conclude with `U_block hOk τ' s hs`.

Establish `hp` using `congrArg (Polynomial.map (ZMod.castHom (dvd_refl l) F)) (hLk τ').2.2.2`. Simplify using `only [Polynomial.map_prod, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C] at hp`. Simplify using `only [map_intCast] at hp`. Establish `e1 : ∀ a : Fin P.Nr, (((W.U P τ' (a : ℕ) + (1 - (P.Nr : ℤ)) : ℤ) : F)) = ((((W.lam τ' a : ℤ) - ((a : ℕ) : ℤ) : ℤ)) : F)`. Introduce `a`.

Use `congr 1`. Simplify using `only [Wts.U, Formalism.CohomologicalDescent.UnitNormBounds.UN]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : ∀ a : Fin P.Nr, (((Formalism.CohomologicalDescent.UnitNormBounds.UN P.Nr (mu τ') (a : ℕ) + (1 - (P.Nr : ℤ)) : ℤ) : F)) = ((((mu τ' a : ℤ) - ((a : ℕ) : ℤ) : ℤ)) : F)`. Introduce `a`.

Use `congr 1`. Simplify using `only [Formalism.CohomologicalDescent.UnitNormBounds.UN]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [labels, glue_inc hH, e1, e2]`. Conclude with `hp`.

Use `⟨hep, fun i => ?_, fun i => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `a`. Take `⟨τ', rfl | rfl⟩ : ∃ τ', i = inc τ' ∨ i = cj (inc τ')` from `⟨hf i, hb i⟩`. Simplify using `only [labels, glue_inc hH]`. Conclude with `((hJ τ').1 a).1`.

Simplify using `only [labels, glue_cj hH]`. Conclude with `((hJ τ').1 a).2`. Take `⟨τ', rfl | rfl⟩ : ∃ τ', i = inc τ' ∨ i = cj (inc τ')` from `⟨hf i, hb i⟩`. Simplify using `only [labels, glue_inc hH]`. Conclude with `(hJ τ').2.1`.

Simplify using `only [labels, glue_cj hH]`. Conclude with `(hJ τ').2.2`. Introduce `τ' a`. Simplify using `only [labels, glue_inc hH]`. Both sides reduce to the same expression.

Introduce `τ'`. Simplify using `only [labels, glue_inc hH]`. Both sides reduce to the same expression. Use `show σ (inc τ) = if decide (σ (inc τ) ≠ inc (hf (σ (inc τ)))) = true then cj (inc (hf (σ (inc τ)))) else inc (hf (σ (inc τ)))`. Distinguish the cases in `h : σ (inc τ) = inc (hf (σ (inc τ)))`.

Rewrite using `[decide_eq_false (not_not.mpr h), if_neg Bool.false_ne_true]`. Conclude with `h`. Break down `hb (σ (inc τ)) with h' | h'` into its components or cases. Conclude with `absurd h' h`. Rewrite using `[decide_eq_true h, if_pos rfl]`.

Conclude with `h'`. Introduce `a a' haa'`. Take `rfl : a = a'` from `Fin.ext haa'`. Simplify using `only [labels, glue_inc hH, Formalism.CohomologicalDescent.UnitNormBounds.UN, Formalism.CohomologicalDescent.LD.res]`. Establish `hs` using `(hLk τ).2.1`.

Establish `h2 : (∑ a : Fin P.Nr, (mu τ a : ℤ)) = ∑ a : Fin P.Nr, (W.lam τ a : ℤ)` using `by exact_mod_cast hs`. Simplify using `only [labels, glue_inc hH, Wts.U, Formalism.CohomologicalDescent.UnitNormBounds.UN, Finset.sum_sub_distrib, Finset.sum_add_distrib]`. Combine the linear relations using `[h2]`.
-/
theorem latticeLink_of_blockFor : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ (l : ℤ) ∣ NumberField.discr E → ∀ (ι : Type) (inc : ι → (E →+* PadicAlgCl l)), IsHalf inc → ∃ (fr : ℕ → ι → ι) (cjj : ℕ → ι → Bool), ∀ (P : Par) (W : Wts ι), P.Hyp → W.Ok P → (∀ τ a, a < P.Nr → 0 ≤ W.U P τ a ∧ W.U P τ a ≤ (h0 P : ℤ)) → ∀ mu : ι → ℕ → ℕ, Linked l P.Nr W.lam mu → BlockFor Ω inc P W mu → ∀ τ, LatticeLink P (reFr W fr cjj) l τ (res P.Nr (mu τ)) := by
  intro hBS E Ω _ _ _ _ _ _ l _ hl2 hdisc ι inc hH
  obtain ⟨σ, hσF, hσc⟩ := GlobalTheory.T.exists_arithFrobenius_embedding_perm_cmConj E l hdisc
  choose hf hb using hH.2.2
  classical
  set fr : ℕ → ι → ι := fun _ τ => hf (σ (inc τ)) with hfr
  set cjj : ℕ → ι → Bool := fun _ τ => decide (σ (inc τ) ≠ inc (hf (σ (inc τ)))) with hcjj
  refine ⟨fr, cjj, ?_⟩
  intro P W hP hOk hbox mu hLk hBF τ
  obtain ⟨ep, J, bot, hep, hBP, hJ⟩ := hBF
  have hall : ∀ i, ∃ τ', i = ep (inc τ') ∨ i = ep (cj (inc τ')) := by
    intro i
    rcases hep with rfl | rfl
    · rcases hb i with h | h
      · exact ⟨hf i, Or.inl h⟩
      · exact ⟨hf i, Or.inr h⟩
    · rcases hb i with h | h
      · exact ⟨hf i, Or.inr (by rw [cj_cj]; exact h)⟩
      · exact ⟨hf i, Or.inl h⟩
  have hUN : ∀ τ' (a : Fin P.Nr), 0 ≤ Formalism.CohomologicalDescent.UnitNormBounds.UN P.Nr (mu τ') a ∧
      Formalism.CohomologicalDescent.UnitNormBounds.UN P.Nr (mu τ') a ≤ (h0 P : ℤ) := by
    intro τ' a
    have h1 := ((hLk τ').2.2.1 a).2
    have ha := a.2
    have h2 := hbox τ' 0 (by omega)
    simp only [Wts.U, Formalism.CohomologicalDescent.UnitNormBounds.UN] at h2 ⊢
    constructor <;> omega
  have hJb : ∀ i a, 0 ≤ J i a ∧ J i a ≤ (h0 P : ℤ) := by
    intro i a
    obtain ⟨τ', h | h⟩ := hall i <;> subst h
    · rw [((hJ τ').1 a).1]; exact hUN τ' a
    · rw [((hJ τ').1 a).2]
      have := hUN τ' (Fin.rev a)
      constructor <;> linarith [this.1, this.2]
  have hbb : ∀ i (s : Fin P.t), 0 ≤ bot i + ((s : ℕ) : ℤ) ∧ bot i + ((s : ℕ) : ℤ) ≤ (h0 P : ℤ) := by
    intro i s
    have hs := s.2
    have hr := hOk.what₂
    obtain ⟨τ', h | h⟩ := hall i <;> subst h
    · rw [(hJ τ').2.1]
      have e := U_block hOk τ' s hs
      have b := hbox τ' (kc P + W.j τ' + P.t - 1 - s) (by have := hr τ'; omega)
      rw [e] at b; exact b
    · rw [(hJ τ').2.2]
      have e := U_block hOk τ' (P.t - 1 - s) (by omega)
      have b := hbox τ' (kc P + W.j τ' + P.t - 1 - (P.t - 1 - s)) (by have := hr τ'; omega)
      rw [e] at b
      constructor <;> omega
  obtain ⟨O', F, L', _, _, _, _, _, _, I, _, Wl, u, c, kap, ζ, em, jj, hN⟩ :=
    GlobalTheory.T.crystalline_block_lattices_over_power_series_ring hBS E Ω l hl2 hdisc σ hσF P.Nr P.t (h0 P) J bot hJb hbb hBP
  have hn : kc P + (reFr W fr cjj).j τ + P.t + (reFr W fr cjj).q τ = P.Nr := hOk.what₂ τ
  unfold LatticeLink
  rw [hn]
  refine ⟨E →+* PadicAlgCl l, inferInstance, σ, ‹_›, O', F, L', ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, I, ‹_›, Wl, u, c,
    labels inc P W mu, fun _ => 1 - (P.Nr : ℤ), ep, J, bot, kap, ζ, em, jj, inc, ?_⟩
  refine ⟨?_, ?_, ?_, hN, ?_, ?_, ?_, ?_, ?_⟩
  ·
    refine ⟨cj_cj, fun i => hσc i, ?_, ?_, ?_, ?_⟩
    · intro i
      rcases hb i with h | h
      · exact Or.inl ⟨hf i, h.symm⟩
      · exact Or.inr ⟨hf i, by show inc (hf i) = cj i; rw [← cj_cj (inc (hf i)), ← h]⟩
    · intro i a
      obtain ⟨τ', rfl | rfl⟩ : ∃ τ', i = inc τ' ∨ i = cj (inc τ') := ⟨hf i, hb i⟩
      · simp only [labels, glue_inc hH, glue_cj hH]
      · simp only [labels, glue_inc hH, glue_cj hH, cj_cj, Fin.rev_rev, sub_sub_cancel]
    · intro i a
      obtain ⟨τ', rfl | rfl⟩ : ∃ τ', i = inc τ' ∨ i = cj (inc τ') := ⟨hf i, hb i⟩
      · simp only [labels, glue_inc hH, glue_cj hH]
      · simp only [labels, glue_inc hH, glue_cj hH, cj_cj, Fin.rev_rev, sub_sub_cancel]
    · intro i
      obtain ⟨τ', rfl | rfl⟩ : ∃ τ', i = inc τ' ∨ i = cj (inc τ') := ⟨hf i, hb i⟩
      · simp only [labels, glue_inc hH, glue_cj hH]
      · simp only [labels, glue_inc hH, glue_cj hH, cj_cj]; ring
  ·
    rintro _ ⟨τ', rfl⟩
    have hr := hOk.what₂ τ'
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b hab
      have hab' : (a : ℕ) < b := hab
      have h1 := hOk.anti τ' a b hab'.le b.2
      simp only [labels, glue_inc hH, Wts.U, Formalism.CohomologicalDescent.UnitNormBounds.UN]
      omega
    · intro a b hab
      have hab' : (a : ℕ) < b := hab
      have h1 := (hLk τ').1 hab.le
      simp only [Formalism.CohomologicalDescent.LD.res] at h1
      simp only [labels, glue_inc hH, Formalism.CohomologicalDescent.UnitNormBounds.UN]
      omega
    · intro s
      have hs := s.2
      refine ⟨⟨kc P + W.j τ' + P.t - 1 - s, by omega⟩, ?_⟩
      simp only [labels, glue_inc hH]
      exact U_block hOk τ' s hs
    · have hp := congrArg (Polynomial.map (ZMod.castHom (dvd_refl l) F)) (hLk τ').2.2.2
      simp only [Polynomial.map_prod, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C] at hp
      simp only [map_intCast] at hp
      have e1 : ∀ a : Fin P.Nr, (((W.U P τ' (a : ℕ) + (1 - (P.Nr : ℤ)) : ℤ) : F)) =
          ((((W.lam τ' a : ℤ) - ((a : ℕ) : ℤ) : ℤ)) : F) := by
        intro a; congr 1; simp only [Wts.U, Formalism.CohomologicalDescent.UnitNormBounds.UN]; ring
      have e2 : ∀ a : Fin P.Nr, (((Formalism.CohomologicalDescent.UnitNormBounds.UN P.Nr (mu τ') (a : ℕ) + (1 - (P.Nr : ℤ)) : ℤ) : F)) =
          ((((mu τ' a : ℤ) - ((a : ℕ) : ℤ) : ℤ)) : F) := by
        intro a; congr 1; simp only [Formalism.CohomologicalDescent.UnitNormBounds.UN]; ring
      simp only [labels, glue_inc hH, e1, e2]
      exact hp
  ·
    refine ⟨hep, fun i => ?_, fun i => ?_⟩
    · funext a
      obtain ⟨τ', rfl | rfl⟩ : ∃ τ', i = inc τ' ∨ i = cj (inc τ') := ⟨hf i, hb i⟩
      · simp only [labels, glue_inc hH]; exact ((hJ τ').1 a).1
      · simp only [labels, glue_cj hH]; exact ((hJ τ').1 a).2
    · obtain ⟨τ', rfl | rfl⟩ : ∃ τ', i = inc τ' ∨ i = cj (inc τ') := ⟨hf i, hb i⟩
      · simp only [labels, glue_inc hH]; exact (hJ τ').2.1
      · simp only [labels, glue_cj hH]; exact (hJ τ').2.2
  · intro τ' a
    simp only [labels, glue_inc hH]
    rfl
  · intro τ'
    simp only [labels, glue_inc hH]
    rfl
  ·
    show σ (inc τ) = if decide (σ (inc τ) ≠ inc (hf (σ (inc τ)))) = true then cj (inc (hf (σ (inc τ))))
      else inc (hf (σ (inc τ)))
    by_cases h : σ (inc τ) = inc (hf (σ (inc τ)))
    · rw [decide_eq_false (not_not.mpr h), if_neg Bool.false_ne_true]; exact h
    · rcases hb (σ (inc τ)) with h' | h'
      · exact absurd h' h
      · rw [decide_eq_true h, if_pos rfl]; exact h'
  · intro a a' haa'
    obtain rfl : a = a' := Fin.ext haa'
    simp only [labels, glue_inc hH, Formalism.CohomologicalDescent.UnitNormBounds.UN, Formalism.CohomologicalDescent.LD.res]
  · have hs := (hLk τ).2.1
    have h2 : (∑ a : Fin P.Nr, (mu τ a : ℤ)) = ∑ a : Fin P.Nr, (W.lam τ a : ℤ) := by exact_mod_cast hs
    simp only [labels, glue_inc hH, Wts.U, Formalism.CohomologicalDescent.UnitNormBounds.UN, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    linarith [h2]

end GlobalTheory.ExpLink
