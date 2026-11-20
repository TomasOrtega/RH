import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsLocFac
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdemAtUniqueOrth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod GlobalTheory.Mem GlobalTheory.Mem.Col2 Formalism.L2.Col Formalism.L2.Forms
open scoped Classical

namespace GlobalTheory.PartialIdemSum

/- English proof (translation)
Rewrite using `[Finset.mul_sum]`. Use `split_ifs with hP`. Rewrite using `[Finset.sum_eq_single P]`. Establish `h1` using `(GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D x (f P) P P hx (hf P hP)).1 rfl`. Rewrite using `[← h1]`.

Conclude with `hx.1.1`. Introduce `P' hP' hne`. Conclude with `(GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D x (f P') P P' hx (hf P' hP')).2 (Ne.symm hne)`. Introduce `h`. Conclude with `absurd hP h`.

Use `Finset.sum_eq_zero fun P' hP' => ?_` and prove the remaining obligations. Use `(GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D x (f P') P P' hx (hf P' hP')).2 ?_` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `hP hP'`.
-/
theorem mul_sum_of_isIdemAt {D : D7} {x : AE D} {P : Formalism.L2.DIV.Pl D.host.E}
    (hx : Formalism.L2.NTheta.IsIdemAt x P) (S : Finset (Formalism.L2.DIV.Pl D.host.E)) (f : Formalism.L2.DIV.Pl D.host.E → AE D)
    (hf : ∀ P' ∈ S, Formalism.L2.NTheta.IsIdemAt (f P') P') :
    x * ∑ P' ∈ S, f P' = if P ∈ S then x else 0 := by
  rw [Finset.mul_sum]
  split_ifs with hP
  · rw [Finset.sum_eq_single P]
    · have h1 := (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D x (f P) P P hx (hf P hP)).1 rfl
      rw [← h1]; exact hx.1.1
    · intro P' hP' hne
      exact (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D x (f P') P P' hx (hf P' hP')).2 (Ne.symm hne)
    · intro h; exact absurd hP h
  · refine Finset.sum_eq_zero fun P' hP' => ?_
    refine (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D x (f P') P P' hx (hf P' hP')).2 ?_
    rintro rfl; exact hP hP'

/- English proof (translation)
Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun P hP => ?_` and prove the remaining obligations. Rewrite using `[mul_sum_of_isIdemAt (hf P hP) S' g hg, if_pos (hS hP)]`.
-/
theorem sum_mul_sum_of_subset {D : D7} (S S' : Finset (Formalism.L2.DIV.Pl D.host.E)) (f g : Formalism.L2.DIV.Pl D.host.E → AE D)
    (hf : ∀ P ∈ S, Formalism.L2.NTheta.IsIdemAt (f P) P) (hg : ∀ P ∈ S', Formalism.L2.NTheta.IsIdemAt (g P) P) (hS : S ⊆ S') :
    (∑ P ∈ S, f P) * ∑ P ∈ S', g P = ∑ P ∈ S, f P := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun P hP => ?_
  rw [mul_sum_of_isIdemAt (hf P hP) S' g hg, if_pos (hS hP)]

/- English proof (translation)
Rewrite using `[mul_comm, mul_sum_of_isIdemAt hx S f hf, if_neg hR]`.
-/
theorem sum_mul_of_not_mem {D : D7} (S : Finset (Formalism.L2.DIV.Pl D.host.E)) (f : Formalism.L2.DIV.Pl D.host.E → AE D)
    (hf : ∀ P ∈ S, Formalism.L2.NTheta.IsIdemAt (f P) P) {x : AE D} {R : Formalism.L2.DIV.Pl D.host.E}
    (hx : Formalism.L2.NTheta.IsIdemAt x R) (hR : R ∉ S) : (∑ P ∈ S, f P) * x = 0 := by
  rw [mul_comm, mul_sum_of_isIdemAt hx S f hf, if_neg hR]

/- English proof (translation)
Introduce `D P₀ ι e e' es hdisj hes he he'`. Take `⟨⟨es₀, hes₀, rfl⟩, -⟩` from `he`. Take `⟨⟨es'', hes'', rfl⟩, hce'⟩` from `he'`. Use `set g : Formalism.L2.DIV.Pl D.host.E → AE D := fun P => if P ∈ P₀ then es₀ P else if h : P ∈ ι then es ⟨P, h⟩ else 0 with hgdef`. Establish `hg : ∀ P ∈ P₀ ∪ ι, Formalism.L2.NTheta.IsIdemAt (g P) P`.

Introduce `P hP`. Distinguish the cases in `h0 : P ∈ P₀`. Simplify using `only [hgdef, if_pos h0]`. Conclude with `hes₀ P h0`. Establish `hι : P ∈ ι`.

Break down `Finset.mem_union.mp hP with h | h` into its components or cases. Conclude with `absurd h h0`. Conclude with `h`. Simplify using `only [hgdef, if_neg h0, dif_pos hι]`. Conclude with `hes ⟨P, hι⟩`.

Use `⟨sum_mul_sum_of_subset _ _ es'' es'' hes'' hes'' subset_rfl, fun Q => ?_⟩` and prove the remaining obligations. Establish `hmapι : Q.map (Function.Embedding.subtype (· ∈ ι)) ⊆ ι`. Introduce `P hP`. Take `⟨PP, -, rfl⟩` from `Finset.mem_map.mp hP`. Conclude with `PP.2`.

Establish `hS : P₀ ∪ Q.map (Function.Embedding.subtype (· ∈ ι)) ⊆ P₀ ∪ ι` using `Finset.union_subset_union subset_rfl hmapι`. Establish `hgS : ∀ P ∈ P₀ ∪ Q.map (Function.Embedding.subtype (· ∈ ι)), Formalism.L2.NTheta.IsIdemAt (g P) P` using `fun P hP => hg P (hS hP)`. Establish `hsum : ∑ P ∈ P₀, es₀ P + ∑ PP ∈ Q, es PP = ∑ P ∈ P₀ ∪ Q.map (Function.Embedding.subtype (· ∈ ι)), g P`. Rewrite using `[Finset.sum_union (Finset.disjoint_of_subset_right hmapι hdisj), Finset.sum_map]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun P hP => ?_` and prove the remaining obligations. Simplify using `only [hgdef, if_pos hP]`. Use `Finset.sum_congr rfl fun PP _ => ?_` and prove the remaining obligations. Establish `hn : (PP : Formalism.L2.DIV.Pl D.host.E) ∉ P₀` using `Finset.disjoint_right.mp hdisj PP.2`. Simplify using `only [hgdef, Function.Embedding.coe_subtype, if_neg hn, dif_pos PP.2]`.

Rewrite using `[hsum]`. Establish `hxy` using `sum_mul_sum_of_subset _ _ g es'' hgS hes'' hS`. Use `⟨⟨⟨g, hgS, rfl⟩, ?_⟩, sum_mul_sum_of_subset _ _ g g hgS hgS subset_rfl, hxy, fun R hR => ?_⟩` and prove the remaining obligations. Use `set x := ∑ P ∈ P₀ ∪ Q.map (Function.Embedding.subtype (· ∈ ι)), g P set y := ∑ P ∈ P₀ ∪ ι, es'' P`. Combine the equalities or inequalities in the displayed calculation.

Use `sum_mul_of_not_mem _ g hgS (hes R) ?_` and prove the remaining obligations. Introduce `hmem`. Break down `Finset.mem_union.mp hmem with h | h` into its components or cases. Conclude with `Finset.disjoint_left.mp hdisj h R.2`. Take `⟨PP, hPP, hPR⟩` from `Finset.mem_map.mp h`.

Establish `: PP = R` using `Subtype.ext hPR`. Conclude with `hR (this ▸ hPP)`.
-/
theorem partial_sums : ∀ (D : D7) (P₀ ι : Finset (Formalism.L2.DIV.Pl D.host.E)) (e e' : AE D) (es : ι → AE D),
    Disjoint P₀ ι → (∀ PP, Formalism.L2.NTheta.IsIdemAt (es PP) PP.1) → IsIdemSum e P₀ → IsIdemSum e' (P₀ ∪ ι) →
    e' * e' = e' ∧ ∀ Q : Finset ι, IsIdemSum (e + ∑ PP ∈ Q, es PP) (P₀ ∪ Q.map (Function.Embedding.subtype (· ∈ ι))) ∧
      (e + ∑ PP ∈ Q, es PP) * (e + ∑ PP ∈ Q, es PP) = e + ∑ PP ∈ Q, es PP ∧
      (e + ∑ PP ∈ Q, es PP) * e' = e + ∑ PP ∈ Q, es PP ∧
      ∀ R, R ∉ Q → (e + ∑ PP ∈ Q, es PP) * es R = 0 := by
  intro D P₀ ι e e' es hdisj hes he he'
  obtain ⟨⟨es₀, hes₀, rfl⟩, -⟩ := he
  obtain ⟨⟨es'', hes'', rfl⟩, hce'⟩ := he'
  set g : Formalism.L2.DIV.Pl D.host.E → AE D :=
    fun P => if P ∈ P₀ then es₀ P else if h : P ∈ ι then es ⟨P, h⟩ else 0 with hgdef
  have hg : ∀ P ∈ P₀ ∪ ι, Formalism.L2.NTheta.IsIdemAt (g P) P := by
    intro P hP
    by_cases h0 : P ∈ P₀
    · simp only [hgdef, if_pos h0]; exact hes₀ P h0
    · have hι : P ∈ ι := by
        rcases Finset.mem_union.mp hP with h | h
        · exact absurd h h0
        · exact h
      simp only [hgdef, if_neg h0, dif_pos hι]; exact hes ⟨P, hι⟩
  refine ⟨sum_mul_sum_of_subset _ _ es'' es'' hes'' hes'' subset_rfl, fun Q => ?_⟩
  have hmapι : Q.map (Function.Embedding.subtype (· ∈ ι)) ⊆ ι := by
    intro P hP
    obtain ⟨PP, -, rfl⟩ := Finset.mem_map.mp hP
    exact PP.2
  have hS : P₀ ∪ Q.map (Function.Embedding.subtype (· ∈ ι)) ⊆ P₀ ∪ ι :=
    Finset.union_subset_union subset_rfl hmapι
  have hgS : ∀ P ∈ P₀ ∪ Q.map (Function.Embedding.subtype (· ∈ ι)), Formalism.L2.NTheta.IsIdemAt (g P) P :=
    fun P hP => hg P (hS hP)
  have hsum : ∑ P ∈ P₀, es₀ P + ∑ PP ∈ Q, es PP =
      ∑ P ∈ P₀ ∪ Q.map (Function.Embedding.subtype (· ∈ ι)), g P := by
    rw [Finset.sum_union (Finset.disjoint_of_subset_right hmapι hdisj), Finset.sum_map]
    congr 1
    · refine Finset.sum_congr rfl fun P hP => ?_
      simp only [hgdef, if_pos hP]
    · refine Finset.sum_congr rfl fun PP _ => ?_
      have hn : (PP : Formalism.L2.DIV.Pl D.host.E) ∉ P₀ := Finset.disjoint_right.mp hdisj PP.2
      simp only [hgdef, Function.Embedding.coe_subtype, if_neg hn, dif_pos PP.2]
  rw [hsum]
  have hxy := sum_mul_sum_of_subset _ _ g es'' hgS hes'' hS
  refine ⟨⟨⟨g, hgS, rfl⟩, ?_⟩, sum_mul_sum_of_subset _ _ g g hgS hgS subset_rfl, hxy, fun R hR => ?_⟩
  · set x := ∑ P ∈ P₀ ∪ Q.map (Function.Embedding.subtype (· ∈ ι)), g P
    set y := ∑ P ∈ P₀ ∪ ι, es'' P
    calc x * cA D x = (x * y) * cA D (x * y) := by rw [hxy]
      _ = (x * cA D x) * (y * cA D y) := by rw [map_mul]; ring
      _ = 0 := by rw [hce', mul_zero]
  · refine sum_mul_of_not_mem _ g hgS (hes R) ?_
    intro hmem
    rcases Finset.mem_union.mp hmem with h | h
    · exact Finset.disjoint_left.mp hdisj h R.2
    · obtain ⟨PP, hPP, hPR⟩ := Finset.mem_map.mp h
      have : PP = R := Subtype.ext hPR
      exact hR (this ▸ hPP)

end GlobalTheory.PartialIdemSum
