import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPos
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupportSubschemeEmbeddingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetLengthOneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetSegmentLengthTwoStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetSegmentInductionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubSegmentProductStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityConcatStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConcatenatedJacquetMultiplicityFactorizationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConcatApplyEquiv

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg GlobalTheory.CompanionTheory.SegCoarse

namespace GlobalTheory.CompanionTheory.SegCoarse

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Introduce `Δ`. Proceed by induction on `h : Δ.len using Nat.strong_induction_on generalizing Δ with`. Consider the case `_ n ih`. Establish `hp` using `Δ.len_pos`. Break down `Nat.lt_or_ge n 3 with h3 | h3` into its components or cases.

Use `interval_cases n`. Use linear arithmetic over natural numbers and integers. Conclude with `@GlobalTheory.T.fine_jacquet_length_one k _ _ _ _ hA Δ h`. Conclude with `@GlobalTheory.T.fine_jacquet_segment_length_two k _ _ _ _ hA hZ Δ h`. Conclude with `@GlobalTheory.T.fine_jacquet_segment_induction k _ _ _ _ hA Δ (h ▸ h3) fun Δ' hlt => ih _ (h ▸ hlt) Δ' rfl`.
-/
theorem fineJac_all (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation) :
    ∀ Δ : Segment k, FineJac Δ := by
  intro Δ
  induction h : Δ.len using Nat.strong_induction_on generalizing Δ with
  | _ n ih =>
    have hp := Δ.len_pos
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · interval_cases n
      · omega
      · exact @GlobalTheory.T.fine_jacquet_length_one k _ _ _ _ hA Δ h
      · exact @GlobalTheory.T.fine_jacquet_segment_length_two k _ _ _ _ hA hZ Δ h
    · exact @GlobalTheory.T.fine_jacquet_segment_induction k _ _ _ _ hA Δ (h ▸ h3) fun Δ' hlt => ih _ (h ▸ hlt) Δ' rfl

/- English proof (translation)
Use `choose c x hx hcusp hemb using fun a => GlobalTheory.T.support_subscheme_embedding k (y a).1 _ (y a).rep (y a).2.rep.smooth (y a).2.rep.irr`. Establish `hjx : ∀ a, 1 ≤ jm (x a) (hx a) (y a).rep` using `fun a => by`. Take `⟨φ, hφ⟩` from `hemb a`. Use `Model.nontrivial_of_isIrreducible (y a).2.rep.irr` as an intermediate fact. Take `⟨v, hv⟩` from `exists_ne (0 : (y a).2.rep.V)`.

Conclude with `GlobalTheory.CompanionTheory.FrobJm.one_le_jm hA (x a) (hx a) (y a).rep (y a).2.rep.smooth φ ⟨v, fun e => hv (hφ (e.trans (map_zero φ).symm))⟩`. Establish `hcat0 : ∑ i, (concat c x i).1 = N`. Rewrite using `[sum_concat, ← hd]`. Conclude with `Finset.sum_congr rfl fun a _ => hx a`. Establish `hirr : π.IsIrreducible` using `hπ.2.1`.

Establish `hsm : IsSmooth π` using `hπ.hasSupport.isSmooth`. Establish `hle` using `GlobalTheory.T.jacquet_multiplicity_concat hA y hd c x hx hcat0 hjx π hsm (hasFiniteLength_of_isIrreducible hirr)`. Establish `h1' : 1 ≤ jm (concat c x) hcat0 π` using `h1.trans hle`. Take `⟨hl, hfine⟩` from `(fineJac_all hA hZ Δ π hπ).2 _ (concat c x) hcat0 (fun i => hcusp _ _) h1'`. Establish `hc : ∀ a, 0 < c a` using `fun a => by`.

Use `Nat.pos_of_ne_zero fun h0 => ?_` and prove the remaining obligations. Establish `: IsEmpty (Fin (c a))` using `by rw [h0]; infer_instance`. Use `hx a` as an intermediate fact. Rewrite `this` using `[Finset.univ_eq_empty, Finset.sum_empty]`. Conclude with `(hpos a).ne this`.

Establish `hxeq : x = fun a => dec (topCut Δ c hc a)` using `concat_injective (funext fun i => (hfine i).trans (concat_dec_topCut Δ c hc hl i).symm)`. Substitute `hxeq` using the available equality. Use `⟨c, hc, hl, hcat0, hle, fun a => ?_⟩` and prove the remaining obligations. Take `⟨φ, hφ⟩` from `hemb a`. Conclude with `GlobalTheory.T.irreducible_sub_segment_product hA hZ (topCut Δ c hc a) (hx a) (y a).rep (y a).2.rep.smooth (y a).2.rep.irr φ hφ`.
-/
theorem occurs_topCut (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation)
    (Δ : Segment k) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (hπ : IsLSeg Δ π) {s : ℕ} (y : Fin s → IrrGL k) (hd : ∑ a, (y a).1 = N) (hpos : ∀ a, 0 < (y a).1)
    (h1 : 1 ≤ jm y hd π) :
    ∃ (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) (_ : ∑ a, c a = Δ.len)
      (hcat : ∑ i, (concat c (fun a => dec (topCut Δ c hc a)) i).1 = N),
      jm y hd π ≤ jm (concat c (fun a => dec (topCut Δ c hc a))) hcat π ∧
        ∀ a, IsLSeg (topCut Δ c hc a) (y a).rep := by
  choose c x hx hcusp hemb using fun a =>
    GlobalTheory.T.support_subscheme_embedding k (y a).1 _ (y a).rep (y a).2.rep.smooth (y a).2.rep.irr
  have hjx : ∀ a, 1 ≤ jm (x a) (hx a) (y a).rep := fun a => by
    obtain ⟨φ, hφ⟩ := hemb a
    have := Model.nontrivial_of_isIrreducible (y a).2.rep.irr
    obtain ⟨v, hv⟩ := exists_ne (0 : (y a).2.rep.V)
    exact GlobalTheory.CompanionTheory.FrobJm.one_le_jm hA (x a) (hx a) (y a).rep (y a).2.rep.smooth φ
      ⟨v, fun e => hv (hφ (e.trans (map_zero φ).symm))⟩
  have hcat0 : ∑ i, (concat c x i).1 = N := by
    rw [sum_concat, ← hd]
    exact Finset.sum_congr rfl fun a _ => hx a
  have hirr : π.IsIrreducible := hπ.2.1
  have hsm : IsSmooth π := hπ.hasSupport.isSmooth
  have hle := GlobalTheory.T.jacquet_multiplicity_concat hA y hd c x hx hcat0 hjx π hsm (hasFiniteLength_of_isIrreducible hirr)
  have h1' : 1 ≤ jm (concat c x) hcat0 π := h1.trans hle
  obtain ⟨hl, hfine⟩ := (fineJac_all hA hZ Δ π hπ).2 _ (concat c x) hcat0 (fun i => hcusp _ _) h1'
  have hc : ∀ a, 0 < c a := fun a => by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    have : IsEmpty (Fin (c a)) := by rw [h0]; infer_instance
    have := hx a
    rw [Finset.univ_eq_empty, Finset.sum_empty] at this
    exact (hpos a).ne this
  have hxeq : x = fun a => dec (topCut Δ c hc a) :=
    concat_injective (funext fun i => (hfine i).trans (concat_dec_topCut Δ c hc hl i).symm)
  subst hxeq
  refine ⟨c, hc, hl, hcat0, hle, fun a => ?_⟩
  obtain ⟨φ, hφ⟩ := hemb a
  exact GlobalTheory.T.irreducible_sub_segment_product hA hZ (topCut Δ c hc a) (hx a) (y a).rep (y a).2.rep.smooth (y a).2.rep.irr φ hφ

/- English proof (translation)
Introduce `k _ _ _ _ hA hZ Δ N V _ _ π hπ s y hd hpos`. Establish `hdΔ : ∑ a, (dec Δ a).1 = N` using `(sum_dec Δ).trans hπ.deg_eq`. Establish `hone` using `(fineJac_all hA hZ Δ π hπ).1 hdΔ`. Establish `hirr : π.IsIrreducible` using `hπ.2.1`. Establish `hsm : IsSmooth π` using `hπ.hasSupport.isSmooth`.

Establish `hread : ∀ (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) (hl : ∑ a, c a = Δ.len) (hcat : ∑ i, (concat c (fun a => dec (topCut Δ c hc a)) i).1 = N), jm (concat c (fun a => dec (topCut Δ c hc a))) hcat π = 1` using `fun c hc hl hcat => (jm_reindex hl _ _ (concat_dec_topCut Δ c hc hl) hcat hdΔ π).trans hone`. Establish `hB : 1 ≤ jm y hd π → ∃ Γ : Fin s → Segment k, IsTopCut Δ Γ ∧ ∀ a, IsLSeg (Γ a) (y a).rep` using `fun h1 => by`. Take `⟨c, hc, hl, -, -, hL⟩` from `occurs_topCut hA hZ Δ π hπ y hd hpos h1`. Conclude with `⟨topCut Δ c hc, isTopCut_topCut Δ c hc hl, hL⟩`. Establish `hC : jm y hd π ≤ 1`.

Distinguish the cases in `h0 : jm y hd π = 0`. Rewrite using `[h0]`. Conclude with `zero_le_one`. Take `⟨c, hc, hl, hcat, hle, -⟩` from `occurs_topCut hA hZ Δ π hπ y hd hpos (ENat.one_le_iff_ne_zero.2 h0)`. Conclude with `hle.trans (hread c hc hl hcat).le`.

Establish `hD : (∃ Γ : Fin s → Segment k, IsTopCut Δ Γ ∧ ∀ a, IsLSeg (Γ a) (y a).rep) → 1 ≤ jm y hd π`. Introduce and unpack `⟨Γ, hΓ, hL⟩`. Establish `hΓe` using `eq_topCut hΓ`. Use `set c : Fin s → ℕ := fun a => (Γ a).len with hcdef`. Establish `hc : ∀ a, 0 < c a` using `fun a => (Γ a).len_pos`.

Establish `hl : ∑ a, c a = Δ.len` using `hΓ.1`. Establish `hcat : ∑ i, (concat c (fun a => dec (topCut Δ c hc a)) i).1 = N` using `(Fintype.sum_equiv (finCongr hl) _ _ fun i => by rw [concat_dec_topCut Δ c hc hl]; rfl).trans hdΔ`. Establish `hxpos : ∀ a, 0 < ∑ i, (dec (topCut Δ c hc a) i).1` using `fun a => by`. Rewrite using `[sum_dec, deg_topCut]`. Conclude with `Nat.mul_pos (hc a) Δ.d_pos`.

Take `⟨σ, hσ, hσd, h1σ⟩` from `GlobalTheory.T.concatenated_jacquet_multiplicity_factorization hA c (fun a => dec (topCut Δ c hc a)) hxpos hcat π hsm (hasFiniteLength_of_isIrreducible hirr) (hread c hc hl hcat).ge`. Establish `hσpos : ∀ a, 0 < (σ a).1` using `fun a => (hσd a).symm ▸ hxpos a`. Take `⟨c', hc', hl', -, -, hL'⟩` from `occurs_topCut hA hZ Δ π hπ σ hσ hσpos h1σ`. Establish `hsd : ∀ a, ∑ i : Fin (c a), (dec (topCut Δ c hc a) i).1 = c a * Δ.d` using `fun a => (sum_dec _).trans (deg_topCut Δ c hc a)`. Establish `hcc : c' = c` using `funext fun a => by`.

Establish `e1` using `(hL' a).deg_eq`. Rewrite `e1` using `[deg_topCut, hσd a, hsd a]`. Conclude with `Nat.eq_of_mul_eq_mul_right Δ.d_pos e1`. Substitute `hcc` using the available equality. Establish `hσy : σ = y` using `funext fun a => by`.

Establish `h2 : IsLSeg (topCut Δ c hc' a) (y a).rep`. Use `hL a` as an intermediate fact. Rewrite `this` using `[hΓe]`. Conclude with `this`. Conclude with `eq_of_isLSeg (hL' a) h2`.

Substitute `hσy` using the available equality. Conclude with `h1σ`. Use `⟨fun h => le_antisymm hC (hD h), fun h => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h0`. Conclude with `h (hB (ENat.one_le_iff_ne_zero.2 h0))`.
-/
theorem lSegJacquet : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation), LSegJacquet k := by
  intro k _ _ _ _ hA hZ Δ N V _ _ π hπ s y hd hpos
  have hdΔ : ∑ a, (dec Δ a).1 = N := (sum_dec Δ).trans hπ.deg_eq
  have hone := (fineJac_all hA hZ Δ π hπ).1 hdΔ
  have hirr : π.IsIrreducible := hπ.2.1
  have hsm : IsSmooth π := hπ.hasSupport.isSmooth

  have hread : ∀ (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) (hl : ∑ a, c a = Δ.len)
      (hcat : ∑ i, (concat c (fun a => dec (topCut Δ c hc a)) i).1 = N),
      jm (concat c (fun a => dec (topCut Δ c hc a))) hcat π = 1 := fun c hc hl hcat =>
    (jm_reindex hl _ _ (concat_dec_topCut Δ c hc hl) hcat hdΔ π).trans hone
  have hB : 1 ≤ jm y hd π → ∃ Γ : Fin s → Segment k, IsTopCut Δ Γ ∧ ∀ a, IsLSeg (Γ a) (y a).rep := fun h1 => by
    obtain ⟨c, hc, hl, -, -, hL⟩ := occurs_topCut hA hZ Δ π hπ y hd hpos h1
    exact ⟨topCut Δ c hc, isTopCut_topCut Δ c hc hl, hL⟩
  have hC : jm y hd π ≤ 1 := by
    by_cases h0 : jm y hd π = 0
    · rw [h0]; exact zero_le_one
    · obtain ⟨c, hc, hl, hcat, hle, -⟩ := occurs_topCut hA hZ Δ π hπ y hd hpos (ENat.one_le_iff_ne_zero.2 h0)
      exact hle.trans (hread c hc hl hcat).le
  have hD : (∃ Γ : Fin s → Segment k, IsTopCut Δ Γ ∧ ∀ a, IsLSeg (Γ a) (y a).rep) → 1 ≤ jm y hd π := by
    rintro ⟨Γ, hΓ, hL⟩
    have hΓe := eq_topCut hΓ
    set c : Fin s → ℕ := fun a => (Γ a).len with hcdef
    have hc : ∀ a, 0 < c a := fun a => (Γ a).len_pos
    have hl : ∑ a, c a = Δ.len := hΓ.1
    have hcat : ∑ i, (concat c (fun a => dec (topCut Δ c hc a)) i).1 = N :=
      (Fintype.sum_equiv (finCongr hl) _ _ fun i => by rw [concat_dec_topCut Δ c hc hl]; rfl).trans hdΔ
    have hxpos : ∀ a, 0 < ∑ i, (dec (topCut Δ c hc a) i).1 := fun a => by
      rw [sum_dec, deg_topCut]; exact Nat.mul_pos (hc a) Δ.d_pos
    obtain ⟨σ, hσ, hσd, h1σ⟩ := GlobalTheory.T.concatenated_jacquet_multiplicity_factorization hA c (fun a => dec (topCut Δ c hc a)) hxpos hcat π hsm
      (hasFiniteLength_of_isIrreducible hirr) (hread c hc hl hcat).ge
    have hσpos : ∀ a, 0 < (σ a).1 := fun a => (hσd a).symm ▸ hxpos a
    obtain ⟨c', hc', hl', -, -, hL'⟩ := occurs_topCut hA hZ Δ π hπ σ hσ hσpos h1σ
    have hsd : ∀ a, ∑ i : Fin (c a), (dec (topCut Δ c hc a) i).1 = c a * Δ.d := fun a =>
      (sum_dec _).trans (deg_topCut Δ c hc a)
    have hcc : c' = c := funext fun a => by
      have e1 := (hL' a).deg_eq
      rw [deg_topCut, hσd a, hsd a] at e1
      exact Nat.eq_of_mul_eq_mul_right Δ.d_pos e1
    subst hcc
    have hσy : σ = y := funext fun a => by
      have h2 : IsLSeg (topCut Δ c hc' a) (y a).rep := by
        have := hL a
        rw [hΓe] at this
        exact this
      exact eq_of_isLSeg (hL' a) h2
    subst hσy
    exact h1σ
  refine ⟨fun h => le_antisymm hC (hD h), fun h => ?_⟩
  by_contra h0
  exact h (hB (ENat.one_le_iff_ne_zero.2 h0))

end GlobalTheory.CompanionTheory.SegCoarse

end
