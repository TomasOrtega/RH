import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CPAsIdeal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemDeeperLevelIffReductionsSymmetricUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairTable
import Formalism.LocalToGlobal.Divisibility.TiedLemmas
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjComb

open Classical

/- English proof (translation)
The claim follows from `Finset.sum_bij_ne_zero (fun x _ _ => φ x) (fun _ _ _ => Finset.mem_univ _) (fun _ _ _ _ _ _ h => hφ h) (fun b _ hb => by obtain ⟨x, rfl⟩ := hs b hb exact ⟨x, Finset.mem_univ _, by rw [hval]; exact hb, rfl⟩) (fun x _ _ => hval x)`.
-/
theorem sum_eq_of_inj {α β M : Type} [Fintype α] [Fintype β] [AddCommMonoid M] (F : α → M) (G : β → M)
    (φ : α → β) (hφ : Function.Injective φ) (hval : ∀ x, F x = G (φ x)) (hs : ∀ b, G b ≠ 0 → ∃ x, φ x = b) :
    ∑ x, F x = ∑ b, G b :=
  Finset.sum_bij_ne_zero (fun x _ _ => φ x) (fun _ _ _ => Finset.mem_univ _) (fun _ _ _ _ _ _ h => hφ h)
    (fun b _ hb => by
      obtain ⟨x, rfl⟩ := hs b hb
      exact ⟨x, Finset.mem_univ _, by rw [hval]; exact hb, rfl⟩)
    (fun x _ _ => hval x)

/- English proof (translation)
Introduce `κ _ n r hr ρ k hn hrn U hU s fF fN gB hfF hfN hgB`. Substitute `hrn` using the available equality. Establish `hm : U ∈ blockTri (κ` using `κ) (blk2 r) := fun i j h => absurd h (by simp [blk2, i.2, j.2])`. Establish `hR : upperLeftBlock hr U = U` using `Units.ext (Matrix.ext fun i j => by rw [upper_block_val_submatrix hr hm]; rfl)`. Rewrite `hU`, the goal using `[hR]`.

Establish `hUi : U⁻¹ ∈ unip κ r` using `inv_mem hU`. Establish `hinv : ∀ p q : Fin r, q.1 = p.1 + 1 → (U⁻¹).val p q = - U.val p q`. Introduce `p q hpq`. Establish `hlt : p < q` using `by rw [Fin.lt_def]; omega`. Apply the tactic sequence `have h := unip_mul_entry hUi hU hlt (fun l h1 h2 => by`.

Rewrite `h1`, `h2` using `[Fin.lt_def]`. Use the proof step `omega)`. Rewrite `h` using `[inv_mul_cancel, Units.val_one, Matrix.one_apply_ne (ne_of_lt hlt)]`. Conclude with `eq_neg_of_add_eq_zero_left h.symm`. Take `⟨φ, hφl, hφr⟩ : ∃ φ : Fin ρ ⊕ Fin k → Fin r × Fin r, (∀ a, φ (Sum.inl a) = (fN a, fF a)) ∧ (∀ i, φ (Sum.inr i) = (⟨ρ + k - 2 - i.1, by omega⟩, gB i))` from `⟨Sum.elim _ _, fun _ => rfl, fun _ => rfl⟩`.

Use `Eq.trans (Fintype.sum_sum_type (Sum.elim _ _)).symm ?_` and prove the remaining obligations. Rewrite using `[← Fintype.sum_prod_type']`. Use `sum_eq_of_inj _ _ φ ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `(a|i) (b|j) h`. Rewrite `h` using `[hφl, hφl, Prod.mk.injEq]`.

Establish `h1` using `hfF a`. Establish `h2` using `hfF b`. Establish `h3` using `congrArg Fin.val h.2`. Conclude with `congrArg Sum.inl (Fin.ext (by have := a.2; have := b.2; omega))`. Rewrite `h` using `[hφl, hφr, Prod.mk.injEq]`.

Establish `h1` using `hfF a`. Establish `h2` using `hgB j`. Establish `h3` using `congrArg Fin.val h.2`. It suffices to derive a contradiction. Use `a.2` as an intermediate fact.

Use `j.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite `h` using `[hφr, hφl, Prod.mk.injEq]`. Establish `h1` using `hfF b`. Establish `h2` using `hgB i`.

Establish `h3` using `congrArg Fin.val h.2`. It suffices to derive a contradiction. Use `b.2` as an intermediate fact. Use `i.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Rewrite `h` using `[hφr, hφr, Prod.mk.injEq]`. Establish `h1` using `hgB i`. Establish `h2` using `hgB j`. Establish `h3` using `congrArg Fin.val h.2`. Conclude with `congrArg Sum.inr (Fin.ext (by have := i.2; have := j.2; omega))`.

Introduce and unpack `(a|i)`. Rewrite using `[hφl]`. Simplify using `only [Sum.elim_inl]`. Establish `h1` using `hfF a`. Establish `h2` using `hfN a`.

Establish `ha` using `a.2`. Distinguish the cases in `hc : a.1 + 1 < ρ`. Rewrite `h2` using `[if_pos hc]`. Establish `hq : (fF a).1 = (fN a).1 + 1` using `by omega`. Establish `hs : symEdge ρ k (fN a) (fF a)` using `Or.inl ⟨hq, by omega, by omega⟩`.

Establish `hw : GlobalTheory.SeeConjChar.wB ρ k s (fN a) (fF a) = -1`. Apply the tactic sequence `unfold GlobalTheory.SeeConjChar.wB; split_ifs <;> omega`. Establish `hd : (sgnD ρ k (fN a) : κ) = 1` using `by unfold sgnD; rw [if_neg (by omega)]`. Rewrite using `[if_pos hs, hw, hd, hinv _ _ hq]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `h2` using `[if_neg hc]`. Establish `hq : (fF a).1 = (fN a).1 + 1` using `by omega`. Establish `hs : symEdge ρ k (fN a) (fF a)` using `Or.inl ⟨hq, by omega, by omega⟩`. Establish `hw : GlobalTheory.SeeConjChar.wB ρ k s (fN a) (fF a) = 1`.

Apply the tactic sequence `unfold GlobalTheory.SeeConjChar.wB; split_ifs <;> omega`. Establish `hd : (sgnD ρ k (fN a) : κ) = -1` using `by unfold sgnD; rw [if_pos h2]`. Rewrite using `[if_pos hs, hw, hd, hinv _ _ hq]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hφr] show (if hi : i.1 + 1 < k then (if s then 0 else (sgnD ρ k (gB ⟨i.1 + 1, hi⟩) : κ) * (U⁻¹).val (gB ⟨i.1 + 1, hi⟩) (gB i)) else 0) = _`. Establish `h1` using `hgB i`. Establish `hi2` using `i.2`. Distinguish the cases in `hi : i.1 + 1 < k`. Rewrite using `[dif_pos hi]`.

Establish `h3` using `hgB ⟨i.1 + 1, hi⟩`. Simplify using `only at h3`. Establish `hg : gB ⟨i.1 + 1, hi⟩ = ⟨ρ + k - 2 - i.1, by omega⟩` using `Fin.ext (by dsimp only; omega)`. Establish `hq : (gB i).1 = (⟨ρ + k - 2 - i.1, by omega⟩ : Fin r).1 + 1` using `by dsimp only; omega`. Establish `hs : symEdge ρ k (⟨ρ + k - 2 - i.1, by omega⟩ : Fin r) (gB i)` using `Or.inl ⟨hq, by dsimp only; omega, by dsimp only; omega⟩`.

Establish `hd : (sgnD ρ k (⟨ρ + k - 2 - i.1, by omega⟩ : Fin r) : κ) = 1`. Unfold `sgnD; rw [if_neg (by dsimp only; omega)]`. Rewrite using `[hg, if_pos hs, hd, hinv _ _ hq]`. Consider the cases of `s`. Establish `hw : GlobalTheory.SeeConjChar.wB ρ k false (⟨ρ + k - 2 - i.1, by omega⟩ : Fin r) (gB i) = -1`.

Unfold `GlobalTheory.SeeConjChar.wB`. Rewrite using `[if_neg (show ¬ ((⟨ρ + k - 2 - i.1, by omega⟩ : Fin r).1 < ρ) by dsimp only; omega), if_pos (show (⟨ρ + k - 2 - i.1, by omega⟩ : Fin r).1 + 1 < ρ + k by dsimp only; omega)]; rfl`. Rewrite using `[hw]`. Simplify using the standard rewrite rules. Establish `hw : GlobalTheory.SeeConjChar.wB ρ k true (⟨ρ + k - 2 - i.1, by omega⟩ : Fin r) (gB i) = 0`.

Unfold `GlobalTheory.SeeConjChar.wB`. Rewrite using `[if_neg (show ¬ ((⟨ρ + k - 2 - i.1, by omega⟩ : Fin r).1 < ρ) by dsimp only; omega), if_pos (show (⟨ρ + k - 2 - i.1, by omega⟩ : Fin r).1 + 1 < ρ + k by dsimp only; omega)]; rfl`. Rewrite using `[hw]`. Simplify using the standard rewrite rules. Rewrite using `[dif_neg hi, if_neg]`.

Apply the tactic sequence `rintro (⟨h4, h5, h6⟩ | ⟨h4, h5⟩) <;> dsimp only at h4 h5 <;> omega`. Introduce and unpack `⟨p, q⟩ hne dsimp only at hne`. Distinguish the cases in `hs : symEdge ρ k p q`. Use `swap`. Conclude with `absurd (if_neg hs) hne`.

Rewrite `hne` using `[if_pos hs]`. Establish `hw : GlobalTheory.SeeConjChar.wB ρ k s p q ≠ 0` using `fun h => hne (by rw [h]; simp)`. Unfold `GlobalTheory.SeeConjChar.wB at hw`. Establish `hp2` using `p.2`. Establish `hq2` using `q.2`.

Break down `hs with ⟨hq, hp1, hp3⟩ | ⟨hp, hq⟩` into its components or cases. Distinguish the cases in `h1 : p.1 < ρ`. Simplify using `[h1] at hw`. Distinguish the cases in `h2 : p.1 + 1 < ρ + k`. Use `⟨Sum.inr ⟨ρ + k - 2 - p.1, by omega⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[hφr, Prod.mk.injEq]`. Establish `h3` using `hgB ⟨ρ + k - 2 - p.1, by omega⟩`. Simplify using `only at h3`. Conclude with `⟨Fin.ext (by dsimp only; omega), Fin.ext (by omega)⟩`. Distinguish the cases in `h3 : p.1 = ρ + k`.

Use `⟨Sum.inl ⟨ρ - 1, by omega⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hφl, Prod.mk.injEq]`. Establish `h4` using `hfN ⟨ρ - 1, by omega⟩; have h5 := hfF ⟨ρ - 1, by omega⟩`. Simplify using `only at h4 h5`. Rewrite `h4` using `[if_neg (by omega)]`.

Conclude with `⟨Fin.ext (by omega), Fin.ext (by omega)⟩`. Use `⟨Sum.inl ⟨2 * ρ + k - 1 - p.1, by omega⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hφl, Prod.mk.injEq]`. Establish `h4` using `hfN ⟨2 * ρ + k - 1 - p.1, by omega⟩; have h5 := hfF ⟨2 * ρ + k - 1 - p.1, by omega⟩`. Simplify using `only at h4 h5`.

Rewrite `h4` using `[if_pos (by omega)]`. Conclude with `⟨Fin.ext (by omega), Fin.ext (by omega)⟩`. Simplify using `[show p.1 < ρ by omega] at hw`.
-/
theorem conj_residue_reindex : ∀ {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (ρ k : ℕ), n = 2 * ρ + k + 1 → r = n → ∀ U : GL (Fin n) κ, upperLeftBlock hr U ∈ unip κ r → ∀ (s : Bool) (fF fN : Fin ρ → Fin n) (gB : Fin k → Fin n), (∀ a, (fF a).1 = 2 * ρ + k - a.1) → (∀ a, (fN a).1 = if a.1 + 1 < ρ then 2 * ρ + k - (a.1 + 1) else ρ + k) → (∀ i, (gB i).1 = ρ + k - 1 - i.1) → (∑ a, (sgnD ρ k (fN a) : κ) * (U⁻¹).val (fN a) (fF a)) + (∑ i : Fin k, if hi : i.1 + 1 < k then (if s then 0 else (sgnD ρ k (gB ⟨i.1 + 1, hi⟩) : κ) * (U⁻¹).val (gB ⟨i.1 + 1, hi⟩) (gB i)) else 0) = ∑ i : Fin r, ∑ j : Fin r, if symEdge ρ k i j then ((GlobalTheory.SeeConjChar.wB ρ k s i j : ℤ) : κ) * (upperLeftBlock hr U).val i j else 0 := by
  intro κ _ n r hr ρ k hn hrn U hU s fF fN gB hfF hfN hgB
  subst hrn
  have hm : U ∈ blockTri (κ := κ) (blk2 r) := fun i j h => absurd h (by simp [blk2, i.2, j.2])
  have hR : upperLeftBlock hr U = U := Units.ext (Matrix.ext fun i j => by rw [upper_block_val_submatrix hr hm]; rfl)
  rw [hR] at hU ⊢
  have hUi : U⁻¹ ∈ unip κ r := inv_mem hU
  have hinv : ∀ p q : Fin r, q.1 = p.1 + 1 → (U⁻¹).val p q = - U.val p q := by
    intro p q hpq
    have hlt : p < q := by rw [Fin.lt_def]; omega
    have h := unip_mul_entry hUi hU hlt (fun l h1 h2 => by
      rw [Fin.lt_def] at h1 h2; omega)
    rw [inv_mul_cancel, Units.val_one, Matrix.one_apply_ne (ne_of_lt hlt)] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  obtain ⟨φ, hφl, hφr⟩ : ∃ φ : Fin ρ ⊕ Fin k → Fin r × Fin r, (∀ a, φ (Sum.inl a) = (fN a, fF a)) ∧
      (∀ i, φ (Sum.inr i) = (⟨ρ + k - 2 - i.1, by omega⟩, gB i)) := ⟨Sum.elim _ _, fun _ => rfl, fun _ => rfl⟩
  refine Eq.trans (Fintype.sum_sum_type (Sum.elim _ _)).symm ?_
  rw [← Fintype.sum_prod_type']
  refine sum_eq_of_inj _ _ φ ?_ ?_ ?_
  · rintro (a|i) (b|j) h
    · rw [hφl, hφl, Prod.mk.injEq] at h
      have h1 := hfF a; have h2 := hfF b; have h3 := congrArg Fin.val h.2
      exact congrArg Sum.inl (Fin.ext (by have := a.2; have := b.2; omega))
    · rw [hφl, hφr, Prod.mk.injEq] at h
      have h1 := hfF a; have h2 := hgB j; have h3 := congrArg Fin.val h.2
      exfalso; have := a.2; have := j.2; omega
    · rw [hφr, hφl, Prod.mk.injEq] at h
      have h1 := hfF b; have h2 := hgB i; have h3 := congrArg Fin.val h.2
      exfalso; have := b.2; have := i.2; omega
    · rw [hφr, hφr, Prod.mk.injEq] at h
      have h1 := hgB i; have h2 := hgB j; have h3 := congrArg Fin.val h.2
      exact congrArg Sum.inr (Fin.ext (by have := i.2; have := j.2; omega))
  · rintro (a|i)
    · rw [hφl]
      simp only [Sum.elim_inl]
      have h1 := hfF a; have h2 := hfN a; have ha := a.2
      by_cases hc : a.1 + 1 < ρ
      · rw [if_pos hc] at h2
        have hq : (fF a).1 = (fN a).1 + 1 := by omega
        have hs : symEdge ρ k (fN a) (fF a) := Or.inl ⟨hq, by omega, by omega⟩
        have hw : GlobalTheory.SeeConjChar.wB ρ k s (fN a) (fF a) = -1 := by
          unfold GlobalTheory.SeeConjChar.wB; split_ifs <;> omega
        have hd : (sgnD ρ k (fN a) : κ) = 1 := by unfold sgnD; rw [if_neg (by omega)]
        rw [if_pos hs, hw, hd, hinv _ _ hq]; push_cast; ring
      · rw [if_neg hc] at h2
        have hq : (fF a).1 = (fN a).1 + 1 := by omega
        have hs : symEdge ρ k (fN a) (fF a) := Or.inl ⟨hq, by omega, by omega⟩
        have hw : GlobalTheory.SeeConjChar.wB ρ k s (fN a) (fF a) = 1 := by
          unfold GlobalTheory.SeeConjChar.wB; split_ifs <;> omega
        have hd : (sgnD ρ k (fN a) : κ) = -1 := by unfold sgnD; rw [if_pos h2]
        rw [if_pos hs, hw, hd, hinv _ _ hq]; push_cast; ring
    · rw [hφr]
      show (if hi : i.1 + 1 < k then (if s then 0 else (sgnD ρ k (gB ⟨i.1 + 1, hi⟩) : κ) * (U⁻¹).val (gB ⟨i.1 + 1, hi⟩) (gB i)) else 0) = _
      have h1 := hgB i; have hi2 := i.2
      by_cases hi : i.1 + 1 < k
      · rw [dif_pos hi]
        have h3 := hgB ⟨i.1 + 1, hi⟩
        dsimp only at h3
        have hg : gB ⟨i.1 + 1, hi⟩ = ⟨ρ + k - 2 - i.1, by omega⟩ := Fin.ext (by dsimp only; omega)
        have hq : (gB i).1 = (⟨ρ + k - 2 - i.1, by omega⟩ : Fin r).1 + 1 := by dsimp only; omega
        have hs : symEdge ρ k (⟨ρ + k - 2 - i.1, by omega⟩ : Fin r) (gB i) := Or.inl ⟨hq, by dsimp only; omega, by dsimp only; omega⟩
        have hd : (sgnD ρ k (⟨ρ + k - 2 - i.1, by omega⟩ : Fin r) : κ) = 1 := by
          unfold sgnD; rw [if_neg (by dsimp only; omega)]
        rw [hg, if_pos hs, hd, hinv _ _ hq]
        cases s
        · have hw : GlobalTheory.SeeConjChar.wB ρ k false (⟨ρ + k - 2 - i.1, by omega⟩ : Fin r) (gB i) = -1 := by
            unfold GlobalTheory.SeeConjChar.wB
            rw [if_neg (show ¬ ((⟨ρ + k - 2 - i.1, by omega⟩ : Fin r).1 < ρ) by dsimp only; omega), if_pos (show (⟨ρ + k - 2 - i.1, by omega⟩ : Fin r).1 + 1 < ρ + k by dsimp only; omega)]; rfl
          rw [hw]; simp
        · have hw : GlobalTheory.SeeConjChar.wB ρ k true (⟨ρ + k - 2 - i.1, by omega⟩ : Fin r) (gB i) = 0 := by
            unfold GlobalTheory.SeeConjChar.wB
            rw [if_neg (show ¬ ((⟨ρ + k - 2 - i.1, by omega⟩ : Fin r).1 < ρ) by dsimp only; omega), if_pos (show (⟨ρ + k - 2 - i.1, by omega⟩ : Fin r).1 + 1 < ρ + k by dsimp only; omega)]; rfl
          rw [hw]; simp
      · rw [dif_neg hi, if_neg]
        rintro (⟨h4, h5, h6⟩ | ⟨h4, h5⟩) <;> dsimp only at h4 h5 <;> omega
  · rintro ⟨p, q⟩ hne
    dsimp only at hne
    by_cases hs : symEdge ρ k p q
    swap
    · exact absurd (if_neg hs) hne
    rw [if_pos hs] at hne
    have hw : GlobalTheory.SeeConjChar.wB ρ k s p q ≠ 0 := fun h => hne (by rw [h]; simp)
    unfold GlobalTheory.SeeConjChar.wB at hw
    have hp2 := p.2; have hq2 := q.2
    rcases hs with ⟨hq, hp1, hp3⟩ | ⟨hp, hq⟩
    · by_cases h1 : p.1 < ρ
      · simp [h1] at hw
      by_cases h2 : p.1 + 1 < ρ + k
      · refine ⟨Sum.inr ⟨ρ + k - 2 - p.1, by omega⟩, ?_⟩
        rw [hφr, Prod.mk.injEq]
        have h3 := hgB ⟨ρ + k - 2 - p.1, by omega⟩
        dsimp only at h3
        exact ⟨Fin.ext (by dsimp only; omega), Fin.ext (by omega)⟩
      by_cases h3 : p.1 = ρ + k
      · refine ⟨Sum.inl ⟨ρ - 1, by omega⟩, ?_⟩
        rw [hφl, Prod.mk.injEq]
        have h4 := hfN ⟨ρ - 1, by omega⟩; have h5 := hfF ⟨ρ - 1, by omega⟩
        dsimp only at h4 h5
        rw [if_neg (by omega)] at h4
        exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
      · refine ⟨Sum.inl ⟨2 * ρ + k - 1 - p.1, by omega⟩, ?_⟩
        rw [hφl, Prod.mk.injEq]
        have h4 := hfN ⟨2 * ρ + k - 1 - p.1, by omega⟩; have h5 := hfF ⟨2 * ρ + k - 1 - p.1, by omega⟩
        dsimp only at h4 h5
        rw [if_pos (by omega)] at h4
        exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
    · simp [show p.1 < ρ by omega] at hw

end GlobalTheory.SeeConjComb
