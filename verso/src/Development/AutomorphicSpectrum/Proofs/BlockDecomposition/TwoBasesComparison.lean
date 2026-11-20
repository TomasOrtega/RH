import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic

namespace GlobalTheory.CompanionTheory.LinAlg

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

variable {K : Type} [Field K] {n : ℕ}

/- English proof (translation)
Set `b` to `Module.finBasis K S`. Use `⟨Module.finrank K S, S.subtype ∘ b, ?_, ?_⟩` and prove the remaining obligations. Conclude with `b.linearIndependent.map' S.subtype (Submodule.ker_subtype S)`. Rewrite using `[Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]`.
-/
theorem exists_li_span (S : Submodule K (Fin n → K)) :
    ∃ (a : ℕ) (f : Fin a → Fin n → K), LinearIndependent K f ∧ Submodule.span K (Set.range f) = S := by
  let b := Module.finBasis K S
  refine ⟨Module.finrank K S, S.subtype ∘ b, ?_, ?_⟩
  · exact b.linearIndependent.map' S.subtype (Submodule.ker_subtype S)
  · rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]

/- English proof (translation)
Take `⟨Q, hQ⟩` from `Submodule.exists_isCompl (I.comap W.subtype)`. Establish `hI : (I.comap W.subtype).map W.subtype = I`. Rewrite using `[Submodule.map_comap_subtype]`. Conclude with `inf_eq_right.mpr h`. Use `⟨Q.map W.subtype, Submodule.map_subtype_le W Q, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hI, ← Submodule.map_sup, hQ.sup_eq_top, Submodule.map_subtype_top]`. Rewrite using `[← hI]`. Conclude with `Submodule.disjoint_map W.injective_subtype hQ.disjoint`.
-/
theorem exists_compl_le {I W : Submodule K (Fin n → K)} (h : I ≤ W) :
    ∃ P : Submodule K (Fin n → K), P ≤ W ∧ I ⊔ P = W ∧ Disjoint I P := by
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl (I.comap W.subtype)
  have hI : (I.comap W.subtype).map W.subtype = I := by
    rw [Submodule.map_comap_subtype]; exact inf_eq_right.mpr h
  refine ⟨Q.map W.subtype, Submodule.map_subtype_le W Q, ?_, ?_⟩
  · rw [← hI, ← Submodule.map_sup, hQ.sup_eq_top, Submodule.map_subtype_top]
  · rw [← hI]
    exact Submodule.disjoint_map W.injective_subtype hQ.disjoint

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `rcases i with i | i <;> rfl`.
-/
theorem transpose_fromCols_two {ι κ : Type} (f : ι → Fin n → K) (g : κ → Fin n → K) :
    (fromCols (of f)ᵀ (of g)ᵀ)ᵀ = of (Sum.elim f g) := by
  ext i j
  rcases i with i | i <;> rfl

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `rcases i with i | i | i <;> rfl`.
-/
theorem transpose_fromCols_three {ι κ μ : Type} (f : ι → Fin n → K) (g : κ → Fin n → K)
    (h : μ → Fin n → K) :
    (fromCols (of f)ᵀ (fromCols (of g)ᵀ (of h)ᵀ))ᵀ = of (Sum.elim f (Sum.elim g h)) := by
  ext i j
  rcases i with i | i | i <;> rfl

/- English proof (translation)
Rewrite using `[Set.Sum.elim_range, Submodule.span_union]`.
-/
theorem span_elim {ι κ : Type} (f : ι → Fin n → K) (g : κ → Fin n → K) :
    Submodule.span K (Set.range (Sum.elim f g)) =
      Submodule.span K (Set.range f) ⊔ Submodule.span K (Set.range g) := by
  rw [Set.Sum.elim_range, Submodule.span_union]

/- English proof (translation)
Introduce `K _ n W W'`. Take `⟨P, hPW, hIP, hdP⟩` from `exists_compl_le (inf_le_left : W ⊓ W' ≤ W)`. Take `⟨Q, hQW, hIQ, hdQ⟩` from `exists_compl_le (inf_le_right : W ⊓ W' ≤ W')`. Take `⟨a, f, hf, hfs⟩` from `exists_li_span (W ⊓ W')`. Take `⟨b, g, hg, hgs⟩` from `exists_li_span P`.

Take `⟨c, h, hh, hhs⟩` from `exists_li_span Q`. Establish `hPQ : Disjoint P Q`. Rewrite using `[Submodule.disjoint_def]`. Introduce `x hxP hxQ`. Conclude with `(Submodule.disjoint_def.mp hdP) x (Submodule.mem_inf.mpr ⟨hPW hxP, hQW hxQ⟩) hxP`.

Establish `hIPQ : Disjoint (W ⊓ W') (P ⊔ Q)`. Rewrite using `[Submodule.disjoint_def]`. Introduce `x hxI hx`. Take `⟨p, hp, q, hq, rfl⟩` from `Submodule.mem_sup.mp hx`. Establish `hqI : q ∈ W ⊓ W'`.

Use `Submodule.mem_inf.mpr ⟨?_, hQW hq⟩` and prove the remaining obligations. Establish `hq' : q = (p + q) - p` using `by abel`. Rewrite using `[hq']`. Conclude with `W.sub_mem (Submodule.mem_inf.mp hxI).1 (hPW hp)`. Establish `hq0 : q = 0` using `(Submodule.disjoint_def.mp hdQ) q hqI hq`.

Substitute `hq0` using the available equality. Rewrite `hxI`, the goal using `[add_zero]`. Conclude with `(Submodule.disjoint_def.mp hdP) p hxI hp`. Establish `e2 : ((of f)ᵀ.fromCols (of g)ᵀ)ᵀ = Sum.elim f g` using `transpose_fromCols_two f g`. Establish `e2' : ((of f)ᵀ.fromCols (of h)ᵀ)ᵀ = Sum.elim f h` using `transpose_fromCols_two f h`.

Establish `e3 : ((of f)ᵀ.fromCols ((of g)ᵀ.fromCols (of h)ᵀ))ᵀ = Sum.elim f (Sum.elim g h)` using `transpose_fromCols_three f g h`. Establish `e1 : ((of f)ᵀ)ᵀ = f` using `transpose_transpose (of f)`. Use `⟨a, b, c, (of f)ᵀ, (of g)ᵀ, (of h)ᵀ, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[e3]`. Use `hf.sum_type (hg.sum_type hh ?_) ?_` and prove the remaining obligations.

Rewrite using `[hgs, hhs]`. Conclude with `hPQ`. Rewrite using `[hfs, span_elim, hgs, hhs]`. Conclude with `hIPQ`. Rewrite using `[e1]`.

Conclude with `hfs`. Rewrite using `[e2, span_elim, hfs, hgs, hIP]`. Rewrite using `[e2', span_elim, hfs, hhs, hIQ]`. Rewrite using `[e3, span_elim, span_elim, hfs, hgs, hhs, sup_sup_distrib_left, hIP, hIQ]`.
-/
theorem twoBases : TwoBases := by
  intro K _ n W W'
  obtain ⟨P, hPW, hIP, hdP⟩ := exists_compl_le (inf_le_left : W ⊓ W' ≤ W)
  obtain ⟨Q, hQW, hIQ, hdQ⟩ := exists_compl_le (inf_le_right : W ⊓ W' ≤ W')
  obtain ⟨a, f, hf, hfs⟩ := exists_li_span (W ⊓ W')
  obtain ⟨b, g, hg, hgs⟩ := exists_li_span P
  obtain ⟨c, h, hh, hhs⟩ := exists_li_span Q
  have hPQ : Disjoint P Q := by
    rw [Submodule.disjoint_def]
    intro x hxP hxQ
    exact (Submodule.disjoint_def.mp hdP) x (Submodule.mem_inf.mpr ⟨hPW hxP, hQW hxQ⟩) hxP
  have hIPQ : Disjoint (W ⊓ W') (P ⊔ Q) := by
    rw [Submodule.disjoint_def]
    intro x hxI hx
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hx
    have hqI : q ∈ W ⊓ W' := by
      refine Submodule.mem_inf.mpr ⟨?_, hQW hq⟩
      have hq' : q = (p + q) - p := by abel
      rw [hq']
      exact W.sub_mem (Submodule.mem_inf.mp hxI).1 (hPW hp)
    have hq0 : q = 0 := (Submodule.disjoint_def.mp hdQ) q hqI hq
    subst hq0
    rw [add_zero] at hxI ⊢
    exact (Submodule.disjoint_def.mp hdP) p hxI hp
  have e2 : ((of f)ᵀ.fromCols (of g)ᵀ)ᵀ = Sum.elim f g := transpose_fromCols_two f g
  have e2' : ((of f)ᵀ.fromCols (of h)ᵀ)ᵀ = Sum.elim f h := transpose_fromCols_two f h
  have e3 : ((of f)ᵀ.fromCols ((of g)ᵀ.fromCols (of h)ᵀ))ᵀ = Sum.elim f (Sum.elim g h) :=
    transpose_fromCols_three f g h
  have e1 : ((of f)ᵀ)ᵀ = f := transpose_transpose (of f)
  refine ⟨a, b, c, (of f)ᵀ, (of g)ᵀ, (of h)ᵀ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e3]
    refine hf.sum_type (hg.sum_type hh ?_) ?_
    · rw [hgs, hhs]; exact hPQ
    · rw [hfs, span_elim, hgs, hhs]; exact hIPQ
  · rw [e1]; exact hfs
  · rw [e2, span_elim, hfs, hgs, hIP]
  · rw [e2', span_elim, hfs, hhs, hIQ]
  · rw [e3, span_elim, span_elim, hfs, hgs, hhs, sup_sup_distrib_left, hIP, hIQ]

end GlobalTheory.CompanionTheory.LinAlg
