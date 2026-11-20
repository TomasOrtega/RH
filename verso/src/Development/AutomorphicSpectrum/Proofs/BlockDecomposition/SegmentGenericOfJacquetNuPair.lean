import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.CuspPairSubGeneric
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsQuotientOfSpehTypeProductIsL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConcatApplyEquiv

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL Zc Zc.Seg GlobalTheory.CompanionTheory.SegCoarse

namespace GlobalTheory.CompanionTheory.SegGenNu

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish `h : Finset.univ.filter (fun b : Fin n => a < b) = Finset.Ioi a`. Use extensionality with `b`. Simplify using the standard rewrite rules. Rewrite using `[h]`. Simplify using `[Fin.val_rev]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem card_after {n : ℕ} (a : Fin n) :
    ∑ b ∈ Finset.univ.filter (fun b => a < b), 1 = (Fin.rev a : ℕ) := by
  have h : Finset.univ.filter (fun b : Fin n => a < b) = Finset.Ioi a := by
    ext b; simp
  rw [h]
  simp [Fin.val_rev]
  omega

/- English proof (translation)
Establish `hc : (dec G a).IsCusp` using `G.isCusp_term _`. Establish `e : topCut G (fun _ => 1) (fun _ => one_pos) a = Segment.single (dec G a) hc`. Use `Segment.ext_first ?_ rfl` and prove the remaining obligations. Use `show G.first.nu ((∑ b ∈ Finset.univ.filter (fun b => a < b), 1 : ℕ) : ℂ) = G.first.nu ((Fin.rev a : ℕ) : ℂ)`. Rewrite using `[card_after]`.

Rewrite using `[e]`. Conclude with `(single_spec hc).2.1`.
-/
theorem isLSeg_fine (G : Segment k) (a : Fin G.len) :
    IsLSeg (topCut G (fun _ => 1) (fun _ => one_pos) a) (dec G a).rep := by
  have hc : (dec G a).IsCusp := G.isCusp_term _
  have e : topCut G (fun _ => 1) (fun _ => one_pos) a = Segment.single (dec G a) hc := by
    refine Segment.ext_first ?_ rfl
    show G.first.nu ((∑ b ∈ Finset.univ.filter (fun b => a < b), 1 : ℕ) : ℂ) = G.first.nu ((Fin.rev a : ℕ) : ℂ)
    rw [card_after]
  rw [e]
  exact (single_spec hc).2.1

/- English proof (translation)
Establish `hd : ∑ a, (dec G a).1 = x.1` using `(sum_dec G).trans h.deg_eq`. Establish `hpos : ∀ a, 0 < (dec G a).1` using `fun a => (G.isCusp_term _).1`. Establish `h1 : jm (dec G) hd x.rep = 1` using `(hJ G x.rep h _ (dec G) hd hpos).1 ⟨_, isTopCut_topCut G (fun _ => 1) (fun _ => one_pos) (by simp), isLSeg_fine G⟩`. Assume the negation of the conclusion as `hn`. Establish `h0` using `(hJ G' x.rep h' _ (dec G) hd hpos).2 hn`.

Rewrite `h0` using `[h1]`. Conclude with `one_ne_zero h0`.
-/
theorem exists_cut (hJ : LSegJacquet k) {G G' : Segment k} {x : IrrGL k} (h : IsLSeg G x.rep)
    (h' : IsLSeg G' x.rep) :
    ∃ Γ : Fin G.len → Segment k, IsTopCut G' Γ ∧ ∀ a, IsLSeg (Γ a) (dec G a).rep := by
  have hd : ∑ a, (dec G a).1 = x.1 := (sum_dec G).trans h.deg_eq
  have hpos : ∀ a, 0 < (dec G a).1 := fun a => (G.isCusp_term _).1
  have h1 : jm (dec G) hd x.rep = 1 :=
    (hJ G x.rep h _ (dec G) hd hpos).1
      ⟨_, isTopCut_topCut G (fun _ => 1) (fun _ => one_pos) (by simp), isLSeg_fine G⟩
  by_contra hn
  have h0 := (hJ G' x.rep h' _ (dec G) hd hpos).2 hn
  rw [h1] at h0
  exact one_ne_zero h0

/- English proof (translation)
Rewrite using `[← h.1]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem card_le_len {G : Segment k} {s : ℕ} {Γ : Fin s → Segment k} (h : IsTopCut G Γ) : s ≤ G.len := by
  rw [← h.1]
  calc s = ∑ _ : Fin s, 1 := by simp
    _ ≤ ∑ a, (Γ a).len := Finset.sum_le_sum fun a _ => (Γ a).len_pos

/- English proof (translation)
Take `⟨Γ, hΓ, hL⟩` from `exists_cut hJ h h'`. Take `⟨Γ', hΓ', -⟩` from `exists_cut hJ h' h`. Establish `hle` using `card_le_len hΓ`. Establish `hle'` using `card_le_len hΓ'`. Establish `hlen : G.len = G'.len` using `le_antisymm hle hle'`.

Establish `hpos` using `G.len_pos`. Set `l : Fin G.len` to `⟨G.len - 1, by omega⟩`. Establish `hl1 : (Γ l).len = 1`. Assume the negation of the conclusion as `hne`. Establish `h2 : 1 < (Γ l).len` using `by have := (Γ l).len_pos; omega`.

Establish `hlt : ∑ _ : Fin G.len, 1 < ∑ a, (Γ a).len` using `Finset.sum_lt_sum (fun a _ => (Γ a).len_pos) ⟨l, Finset.mem_univ _, h2⟩`. Rewrite `hlt` using `[hΓ.1, ← hlen]`. Simplify using `at hlt`. Establish `hb : below Γ l = 0`. Use `Finset.sum_eq_zero fun b hb => ?_` and prove the remaining obligations.

Establish `h3 : (l : ℕ) < b` using `Fin.lt_def.1 (Finset.mem_filter.1 hb).2`. Establish `h4` using `b.2`. Establish `h5 : (l : ℕ) = G.len - 1` using `rfl`. Use linear arithmetic over natural numbers and integers. Establish `hf : (Γ l).first = G'.first`.

Rewrite using `[hΓ.2 l, hb]`. Simplify using the standard rewrite rules. Establish `e : Γ l = Segment.single G'.first G'.isCusp_first` using `Segment.ext_first hf hl1`. Establish `h6 : IsLSeg (Γ l) G'.first.rep`. Rewrite using `[e]`.

Conclude with `(single_spec _).2.1`. Establish `h7 : dec G l = G.first`. Establish `h8 : ((Fin.rev l : Fin G.len) : ℕ) = 0`. Simplify using `only [Fin.val_rev, l]`. Use linear arithmetic over natural numbers and integers.

Use `show G.first.nu (((Fin.rev l : Fin G.len) : ℕ) : ℂ) = G.first`. Rewrite using `[h8]`. Simplify using the standard rewrite rules. Rewrite using `[← h7]`. Conclude with `eq_of_isLSeg (hL l) h6`.
-/
theorem first_eq (hJ : LSegJacquet k) {G G' : Segment k} {x : IrrGL k} (h : IsLSeg G x.rep)
    (h' : IsLSeg G' x.rep) : G.first = G'.first := by
  obtain ⟨Γ, hΓ, hL⟩ := exists_cut hJ h h'
  obtain ⟨Γ', hΓ', -⟩ := exists_cut hJ h' h
  have hle := card_le_len hΓ
  have hle' := card_le_len hΓ'
  have hlen : G.len = G'.len := le_antisymm hle hle'
  have hpos := G.len_pos
  let l : Fin G.len := ⟨G.len - 1, by omega⟩
  have hl1 : (Γ l).len = 1 := by
    by_contra hne
    have h2 : 1 < (Γ l).len := by have := (Γ l).len_pos; omega
    have hlt : ∑ _ : Fin G.len, 1 < ∑ a, (Γ a).len :=
      Finset.sum_lt_sum (fun a _ => (Γ a).len_pos) ⟨l, Finset.mem_univ _, h2⟩
    rw [hΓ.1, ← hlen] at hlt
    simp at hlt
  have hb : below Γ l = 0 := by
    refine Finset.sum_eq_zero fun b hb => ?_
    have h3 : (l : ℕ) < b := Fin.lt_def.1 (Finset.mem_filter.1 hb).2
    have h4 := b.2
    have h5 : (l : ℕ) = G.len - 1 := rfl
    omega
  have hf : (Γ l).first = G'.first := by
    rw [hΓ.2 l, hb]
    simp
  have e : Γ l = Segment.single G'.first G'.isCusp_first := Segment.ext_first hf hl1
  have h6 : IsLSeg (Γ l) G'.first.rep := by
    rw [e]
    exact (single_spec _).2.1
  have h7 : dec G l = G.first := by
    have h8 : ((Fin.rev l : Fin G.len) : ℕ) = 0 := by
      simp only [Fin.val_rev, l]
      omega
    show G.first.nu (((Fin.rev l : Fin G.len) : ℕ) : ℂ) = G.first
    rw [h8]
    simp
  rw [← h7]
  exact eq_of_isLSeg (hL l) h6

/- English proof (translation)
Introduce `Δ N V _ _ π hπ`. Assume the negation of the conclusion as `hg`. Take `⟨α, β, β', hd, hd', hα, hβ, hββ, h1, h2⟩` from `hP N V π hπ.hasSupport.isSmooth hπ.hasSupport.isIrreducible hg`. Establish `hpos : ∀ a, 0 < (![α, β] a).1`. Introduce `a`.

Use `fin_cases a`. Conclude with `hα`. Conclude with `hβ`. Establish `hpos' : ∀ a, 0 < (![β', α.nu 1] a).1`. Introduce `a`.

Use `fin_cases a`. Conclude with `hββ ▸ hβ`. Conclude with `hα`. Establish `hcut : ∃ Γ : Fin 2 → Segment k, IsTopCut Δ Γ ∧ ∀ a, IsLSeg (Γ a) (![α, β] a).rep`. Assume the negation of the conclusion as `hn`.

Establish `h0` using `(hJ Δ π hπ 2 ![α, β] hd hpos).2 hn`. Rewrite `h1` using `[h0]`. Simplify using `at h1`. Establish `hcut' : ∃ Γ : Fin 2 → Segment k, IsTopCut Δ Γ ∧ ∀ a, IsLSeg (Γ a) (![β', α.nu 1] a).rep`. Assume the negation of the conclusion as `hn`.

Establish `h0` using `(hJ Δ π hπ 2 ![β', α.nu 1] hd' hpos').2 hn`. Rewrite `h2` using `[h0]`. Simplify using `at h2`. Take `⟨Γ, hΓ, hL⟩` from `hcut`. Take `⟨Γ', hΓ', hL'⟩` from `hcut'`.

Establish `e1 : IsLSeg ((Γ 0).nu 1) (α.nu 1).rep` using `GlobalTheory.isLSeg_nu (hL 0) 1`. Establish `e2 : IsLSeg (Γ' 1) (α.nu 1).rep` using `hL' 1`. Establish `e3 : (Γ 0).first.nu 1 = (Γ' 1).first` using `first_eq hJ e1 e2`. Establish `hb : below Γ' 1 = 0`. Use `Finset.sum_eq_zero fun b hb => ?_` and prove the remaining obligations.

Establish `h3 : (1 : Fin 2) < b` using `(Finset.mem_filter.1 hb).2`. Conclude with `absurd h3 (by omega)`. Rewrite `e3` using `[hΓ.2 0, hΓ'.2 1, hb, IrrGL.nu_nu]`. Establish `e4 : Δ.first.nu (((below Γ 0 + 1 : ℕ)) : ℂ) = Δ.first.nu ((0 : ℕ) : ℂ)`. Simplify using `using e3`.

Establish `e5` using `(IrrGL.nu_natCast_inj Δ.isCusp_first.1).1 e4`. Use linear arithmetic over natural numbers and integers.
-/
theorem lSegGeneric_of_nuPair (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (_hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hJ : Zc.LSegJacquet k)
    (hP : GlobalTheory.BZSeg.NuPair k) : GlobalTheory.BZSeg.LSegGeneric k := by
  intro Δ N V _ _ π hπ
  by_contra hg
  obtain ⟨α, β, β', hd, hd', hα, hβ, hββ, h1, h2⟩ :=
    hP N V π hπ.hasSupport.isSmooth hπ.hasSupport.isIrreducible hg
  have hpos : ∀ a, 0 < (![α, β] a).1 := by
    intro a
    fin_cases a
    · exact hα
    · exact hβ
  have hpos' : ∀ a, 0 < (![β', α.nu 1] a).1 := by
    intro a
    fin_cases a
    · exact hββ ▸ hβ
    · exact hα
  have hcut : ∃ Γ : Fin 2 → Segment k, IsTopCut Δ Γ ∧ ∀ a, IsLSeg (Γ a) (![α, β] a).rep := by
    by_contra hn
    have h0 := (hJ Δ π hπ 2 ![α, β] hd hpos).2 hn
    rw [h0] at h1
    simp at h1
  have hcut' : ∃ Γ : Fin 2 → Segment k, IsTopCut Δ Γ ∧ ∀ a, IsLSeg (Γ a) (![β', α.nu 1] a).rep := by
    by_contra hn
    have h0 := (hJ Δ π hπ 2 ![β', α.nu 1] hd' hpos').2 hn
    rw [h0] at h2
    simp at h2
  obtain ⟨Γ, hΓ, hL⟩ := hcut
  obtain ⟨Γ', hΓ', hL'⟩ := hcut'
  have e1 : IsLSeg ((Γ 0).nu 1) (α.nu 1).rep := GlobalTheory.isLSeg_nu (hL 0) 1
  have e2 : IsLSeg (Γ' 1) (α.nu 1).rep := hL' 1
  have e3 : (Γ 0).first.nu 1 = (Γ' 1).first := first_eq hJ e1 e2
  have hb : below Γ' 1 = 0 := by
    refine Finset.sum_eq_zero fun b hb => ?_
    have h3 : (1 : Fin 2) < b := (Finset.mem_filter.1 hb).2
    exact absurd h3 (by omega)
  rw [hΓ.2 0, hΓ'.2 1, hb, IrrGL.nu_nu] at e3
  have e4 : Δ.first.nu (((below Γ 0 + 1 : ℕ)) : ℂ) = Δ.first.nu ((0 : ℕ) : ℂ) := by
    simpa using e3
  have e5 := (IrrGL.nu_natCast_inj Δ.isCusp_first.1).1 e4
  omega

end GlobalTheory.CompanionTheory.SegGenNu

end
