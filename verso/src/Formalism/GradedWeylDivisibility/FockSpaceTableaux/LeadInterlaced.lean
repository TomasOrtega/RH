import Formalism.GradedWeylDivisibility.StatementC
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LBidetLemmas

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Use `Nat.eq_zero_of_le_zero ((degreeOf_le_iff).2 ?_)` and prove the remaining obligations. Introduce `m hm`. Rewrite `hm` using `[support_rename_of_injective (Option.some_injective σ)]`. Take `⟨m', -, rfl⟩` from `Finset.mem_image.1 hm`. Conclude with `(Finsupp.mapDomain_notin_range m' none (by simp)).le`.
-/
theorem lclint_degreeOf_none_rename_some {B : Type*} [CommRing B] {σ : Type*}
    (p : MvPolynomial σ B) : degreeOf none (rename (some : σ → Option σ) p) = 0 := by
  classical
  refine Nat.eq_zero_of_le_zero ((degreeOf_le_iff).2 ?_)
  intro m hm
  rw [support_rename_of_injective (Option.some_injective σ)] at hm
  obtain ⟨m', -, rfl⟩ := Finset.mem_image.1 hm
  exact (Finsupp.mapDomain_notin_range m' none (by simp)).le

/- English proof (translation)
Unfold `dualWeyl at hf`. Rewrite `hf` using `[Submodule.mem_inf]`. Establish `h` using `hf.2`. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply] at h`. Conclude with `sub_eq_zero.mp (h l j hlj)`.
-/
private theorem colAddGen_eq_rename_some_of_mem_dualWeyl {B : Type*} [CommRing B] {r n : ℕ}
    {ν : Fin n → ℕ} {f : MvPolynomial (Fin r × Fin n) B} (hf : f ∈ dualWeyl B r n ν)
    {l j : Fin n} (hlj : l < j) :
    colAddGen B l j f = rename some f := by
  unfold dualWeyl at hf
  rw [Submodule.mem_inf] at hf
  have h := hf.2
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply] at h
  exact sub_eq_zero.mp (h l j hlj)

/- English proof (translation)
Introduce `B _ _ r n ν f hf hf0`. Introduce `l j hlj`. Establish `hlt : l < j` using `Fin.lt_iff_val_lt_val.2 (by omega)`. Establish `hdeg : (colLex r n).degree (weightedHomogeneousComponent (pairW (r` using `r) l j) (Finsupp.weight (pairW (r := r) l j) ((colLex r n).degree f)) f) = (colLex r n).degree f := h2 B r n (Fin r × Fin n →₀ ℕ) (pairW (r := r) l j) f`. Establish `hcoeff : coeff ((colLex r n).degree f) (weightedHomogeneousComponent (pairW (r` using `r) l j) (Finsupp.weight (pairW (r := r) l j) ((colLex r n).degree f)) f) = coeff ((colLex r n).degree f) f := by`.

Rewrite using `[coeff_weightedHomogeneousComponent, if_pos rfl]`. Establish `hg0 : weightedHomogeneousComponent (pairW (r` using `r) l j) (Finsupp.weight (pairW (r := r) l j) ((colLex r n).degree f)) f ≠ 0 := by`. Introduce `h`. Establish `hne : coeff ((colLex r n).degree f) f ≠ 0` using `(colLex r n).coeff_degree_ne_zero_iff.mpr hf0`. Apply `hne` to reduce the goal to its premises.

Rewrite using `[← hcoeff, h, coeff_zero]`. Establish `hcol : degreeOf none (colAddGen B l j f) ≤ 0`. Rewrite using `[colAddGen_eq_rename_some_of_mem_dualWeyl hf hlt, lclint_degreeOf_none_rename_some]`. Establish `hcomp` using `h1 B r n l j (Finsupp.weight (pairW (r := r) l j) ((colLex r n).degree f)) 0 f hcol`. Establish `hhom` using `weightedHomogeneousComponent_isWeightedHomogeneous (w := pairW (r := r) l j) (Finsupp.weight (pairW (r := r) l j) ((colLex r n).degree f)) f`.

Establish `key` using `h3 B r n l j hlt 0 0 (Finsupp.weight (pairW (r := r) l j) ((colLex r n).degree f)) _ hg0 hhom (fun b hb => absurd hb (Nat.not_lt_zero _)) hcomp`. Rewrite `key` using `[hdeg]`. Conclude with `key`.
-/
theorem leadInterlaced_of (h1 : CompDeg) (h2 : LeadComp) (h3 : TwoColumn) : LeadInterlaced := by
  intro B _ _ r n ν f hf hf0
  intro l j hlj
  have hlt : l < j := Fin.lt_iff_val_lt_val.2 (by omega)
  have hdeg : (colLex r n).degree
      (weightedHomogeneousComponent (pairW (r := r) l j)
        (Finsupp.weight (pairW (r := r) l j) ((colLex r n).degree f)) f) =
      (colLex r n).degree f :=
    h2 B r n (Fin r × Fin n →₀ ℕ) (pairW (r := r) l j) f
  have hcoeff : coeff ((colLex r n).degree f)
      (weightedHomogeneousComponent (pairW (r := r) l j)
        (Finsupp.weight (pairW (r := r) l j) ((colLex r n).degree f)) f) =
      coeff ((colLex r n).degree f) f := by
    rw [coeff_weightedHomogeneousComponent, if_pos rfl]
  have hg0 : weightedHomogeneousComponent (pairW (r := r) l j)
      (Finsupp.weight (pairW (r := r) l j) ((colLex r n).degree f)) f ≠ 0 := by
    intro h
    have hne : coeff ((colLex r n).degree f) f ≠ 0 :=
      (colLex r n).coeff_degree_ne_zero_iff.mpr hf0
    apply hne
    rw [← hcoeff, h, coeff_zero]
  have hcol : degreeOf none (colAddGen B l j f) ≤ 0 := by
    rw [colAddGen_eq_rename_some_of_mem_dualWeyl hf hlt, lclint_degreeOf_none_rename_some]
  have hcomp := h1 B r n l j
    (Finsupp.weight (pairW (r := r) l j) ((colLex r n).degree f)) 0 f hcol
  have hhom := weightedHomogeneousComponent_isWeightedHomogeneous
    (w := pairW (r := r) l j)
    (Finsupp.weight (pairW (r := r) l j) ((colLex r n).degree f)) f
  have key := h3 B r n l j hlt 0 0
    (Finsupp.weight (pairW (r := r) l j) ((colLex r n).degree f)) _ hg0 hhom
    (fun b hb => absurd hb (Nat.not_lt_zero _)) hcomp
  rw [hdeg] at key
  exact key

end Formalism.GradedWeylDivisibility
