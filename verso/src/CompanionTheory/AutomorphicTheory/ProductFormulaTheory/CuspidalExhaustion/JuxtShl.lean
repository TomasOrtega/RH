import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.JuxtDefs
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.JacquetMultiplicityPosImports
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.WordOccursOfSubquotientImports
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ShuffleOfPermImports

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace CompanionTheory.Exh

section Comb

variable {T : Type*}

/- English proof (translation)
Generalize the expression as in `hu : ([] : List T) = u at h`. Proceed by induction on `h with`. Consider the case `nil => rfl`. Consider the case `left _ _ => cases hu`. Consider the case `right _ ih => rw [ih hu]`.
-/
theorem interleave_nil_left {v w : List T} (h : Zc.Comb.Interleave [] v w) : w = v := by
  generalize hu : ([] : List T) = u at h
  induction h with
  | nil => rfl
  | left _ _ => cases hu
  | right _ ih => rw [ih hu]

/- English proof (translation)
Generalize the expression as in `hv : ([] : List T) = v at h`. Proceed by induction on `h with`. Consider the case `nil => rfl`. Consider the case `left _ ih => rw [ih hv]`. Consider the case `right _ _ => cases hv`.
-/
theorem interleave_nil_right {u w : List T} (h : Zc.Comb.Interleave u [] w) : w = u := by
  generalize hv : ([] : List T) = v at h
  induction h with
  | nil => rfl
  | left _ ih => rw [ih hv]
  | right _ _ => cases hv

/- English proof (translation)
Generalize the expression as in `hu : [a] = u at h`. Proceed by induction on `h with`. Consider the case `nil => cases hu`. Consider the case `@left a' u v w h _`. Take `⟨rfl, rfl⟩` from `List.cons.inj hu`.

Conclude with `⟨[], v, rfl, by rw [interleave_nil_left h]; rfl⟩`. Consider the case `@right a' u v w _ ih`. Take `⟨P, Q, rfl, rfl⟩` from `ih hu`. Conclude with `⟨a' :: P, Q, rfl, rfl⟩`.
-/
theorem interleave_single {a : T} {v w : List T} (h : Zc.Comb.Interleave [a] v w) :
    ∃ P Q : List T, v = P ++ Q ∧ w = P ++ a :: Q := by
  generalize hu : [a] = u at h
  induction h with
  | nil => cases hu
  | @left a' u v w h _ =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hu
    exact ⟨[], v, rfl, by rw [interleave_nil_left h]; rfl⟩
  | @right a' u v w _ ih =>
    obtain ⟨P, Q, rfl, rfl⟩ := ih hu
    exact ⟨a' :: P, Q, rfl, rfl⟩

/- English proof (translation)
Consider the cases of `h with`. Consider the case `cons hs hi`. Consider the cases of `hs with`. Consider the case `cons hs' hi'`. Consider the cases of `hs'`.

Rewrite `hi` using `[interleave_nil_right hi']`. Conclude with `interleave_single hi`.
-/
theorem shuffle_two_single {a : T} {D w : List T} (h : Zc.Comb.Shuffle [[a], D] w) :
    ∃ P Q : List T, D = P ++ Q ∧ w = P ++ a :: Q := by
  cases h with
  | cons hs hi =>
    cases hs with
    | cons hs' hi' =>
      cases hs'
      rw [interleave_nil_right hi'] at hi
      exact interleave_single hi

end Comb

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Simplify using `[decW, Segment.single, Segment.term]`.
-/
theorem decW_single (ρ : IrrGL k) (hρ : ρ.IsCusp) : decW (Segment.single ρ hρ) = [ρ] := by
  simp [decW, Segment.single, Segment.term]

/- English proof (translation)
Take `⟨hd1, hsub⟩` from `hσ`. Take `⟨hd2, f, hf⟩` from `he`. Use `GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible σ.2.rep.irr` as an intermediate fact. Establish `hnt : ∃ v, f v ≠ 0`. Take `⟨v, hv⟩` from `exists_ne (0 : σ.2.rep.V)`.

Conclude with `⟨v, fun h => hv (hf (h.trans (f.toLinearMap.map_zero).symm))⟩`. Establish `h1 : 1 ≤ jm l.get hd2 σ.rep` using `GlobalTheory.T.jacquet_multiplicity_pos hA l.get hd2 σ.rep σ.2.rep.smooth f hnt`. Establish `hwd : Wd σ.rep l` using `⟨hd2, by intro h; rw [h] at h1; simp at h1⟩`. Establish `hwd2 : Wd (prodIrr [nxt Δ, b].get hd1) l` using `GlobalTheory.T.word_occurs_of_subquotient _ σ.rep (isSmooth_prodIrr _ _) hsub l hwd`. Establish `hc : (nxt Δ).IsCusp` using `Δ.isCusp_first.nu _`.

Take `⟨L, hL, hsh⟩` from `hW [nxt Δ, b].get hd1 ![Segment.single (nxt Δ) hc, Δ] (by`. Introduce `i`. Use `fin_cases i`. Conclude with `(single_spec hc).2.1`. Conclude with `hb) l hl hwd2`.

Establish `hL' : L.Perm [Segment.single (nxt Δ) hc, Δ]`. Rewrite using `[← Multiset.coe_eq_coe, hL]`. Simplify using `[Fin.univ_val_map]`. Establish `h2` using `GlobalTheory.T.shuffle_of_perm _ _ l hsh (hL'.map decW)`. Rewrite `h2` using `[List.map_cons, List.map_cons, List.map_nil, decW_single]`.

Conclude with `shuffle_two_single h2`.
-/
theorem words_of_subq (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hW : ShlP k) (σ b : IrrGL k) (Δ : Segment k)
    (hb : IsLSeg Δ b.rep) (hσ : SubqL σ [nxt Δ, b]) (l : List (IrrGL k)) (hl : ∀ ρ ∈ l, ρ.IsCusp) (he : EmbL σ l) :
    ∃ P Q : List (IrrGL k), decW Δ = P ++ Q ∧ l = P ++ nxt Δ :: Q := by
  obtain ⟨hd1, hsub⟩ := hσ
  obtain ⟨hd2, f, hf⟩ := he
  have := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible σ.2.rep.irr
  have hnt : ∃ v, f v ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : σ.2.rep.V)
    exact ⟨v, fun h => hv (hf (h.trans (f.toLinearMap.map_zero).symm))⟩
  have h1 : 1 ≤ jm l.get hd2 σ.rep := GlobalTheory.T.jacquet_multiplicity_pos hA l.get hd2 σ.rep σ.2.rep.smooth f hnt
  have hwd : Wd σ.rep l := ⟨hd2, by intro h; rw [h] at h1; simp at h1⟩
  have hwd2 : Wd (prodIrr [nxt Δ, b].get hd1) l :=
    GlobalTheory.T.word_occurs_of_subquotient _ σ.rep (isSmooth_prodIrr _ _) hsub l hwd
  have hc : (nxt Δ).IsCusp := Δ.isCusp_first.nu _
  obtain ⟨L, hL, hsh⟩ := hW [nxt Δ, b].get hd1 ![Segment.single (nxt Δ) hc, Δ] (by
      intro i
      fin_cases i
      · exact (single_spec hc).2.1
      · exact hb) l hl hwd2
  have hL' : L.Perm [Segment.single (nxt Δ) hc, Δ] := by
    rw [← Multiset.coe_eq_coe, hL]
    simp [Fin.univ_val_map]
  have h2 := GlobalTheory.T.shuffle_of_perm _ _ l hsh (hL'.map decW)
  rw [List.map_cons, List.map_cons, List.map_nil, decW_single] at h2
  exact shuffle_two_single h2

end CompanionTheory.Exh

end
