import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
import Development.AbelianVarietyTheory.Definitions.Foundations.FrobLiftWittClosure

noncomputable section
open GlobalTheory.Col PowerSeries

namespace GlobalTheory.Col

open PowerSeries in
/- English proof (translation)
Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => ((j.choose i : ℕ) : R⟦X⟧) * X ^ i) p, add_comm, add_pow]`. Establish `hsub : Finset.range (j + 1) ⊆ Finset.range p` using `Finset.range_subset_range.2 (by omega)`. Rewrite using `[← Finset.sum_subset hsub (fun i _ hi => by`. Rewrite `hi` using `[Finset.mem_range, not_lt]`. Rewrite using `[Nat.choose_eq_zero_of_lt (by omega)]; simp)]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[one_pow, mul_one, mul_comm]`.
-/
private theorem one_add_X_pow_eq_sum_fin_choose {R : Type} [CommRing R] (p j : ℕ) (hj : j < p) :
    (1 + X : R⟦X⟧) ^ j = ∑ i : Fin p, ((j.choose i : ℕ) : R⟦X⟧) * X ^ (i : ℕ) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => ((j.choose i : ℕ) : R⟦X⟧) * X ^ i) p, add_comm, add_pow]
  have hsub : Finset.range (j + 1) ⊆ Finset.range p := Finset.range_subset_range.2 (by omega)
  rw [← Finset.sum_subset hsub (fun i _ hi => by
    rw [Finset.mem_range, not_lt] at hi
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [one_pow, mul_one, mul_comm]

open PowerSeries in
/- English proof (translation)
Establish `htop : Ideal.span {(p : R)} = ⊤` using `Ideal.span_singleton_eq_top.2 hu`. Prove the components needed by the constructor for the conclusion. Introduce `a b`. Establish `h` using `hR.toIsHausdorff.haus (a - b) (fun n => by`. Rewrite using `[htop, Ideal.top_pow, Submodule.top_smul]`.

Conclude with `SModEq.top)`. Conclude with `sub_eq_zero.1 h`.
-/
private theorem subsingleton_of_isUnit_natCast_of_isAdicComplete {R : Type} [CommRing R] (p : ℕ)
    (hR : IsAdicComplete (Ideal.span {(p : R)}) R) (hu : IsUnit (p : R)) : Subsingleton R := by
  have htop : Ideal.span {(p : R)} = ⊤ := Ideal.span_singleton_eq_top.2 hu
  constructor
  intro a b
  have h := hR.toIsHausdorff.haus (a - b) (fun n => by
    rw [htop, Ideal.top_pow, Submodule.top_smul]; exact SModEq.top)
  exact sub_eq_zero.1 h

open PowerSeries in

/- English proof (translation)
Distinguish the cases in `hn : (p : R) ∈ nonunits R`. Use `haveI := hR set e := _root_.GlobalTheory.Col.Model.basis (R := R) p hn`. Establish `he : ∀ i, e i = _root_.GlobalTheory.Col.Model.toUp p (X ^ (i : ℕ))` using `fun i => by show (_root_.GlobalTheory.Col.Model.basis (R := R) p hn) i = _`. Unfold `_root_.GlobalTheory.Col.Model.basis`. Rewrite using `[Module.Basis.mk_apply]`.

Both sides reduce to the same expression. Set `v : Fin p → _root_.GlobalTheory.Col.Model.Up R p` to `fun j => _root_.GlobalTheory.Col.Model.toUp p ((1 + X) ^ (j : ℕ))`. Establish `hv : ∀ j : Fin p, v j = ∑ i : Fin p, (((j : ℕ).choose i : ℕ) : R⟦X⟧) • e i`. Introduce `j`. Simplify using `only [he, Algebra.smul_def, map_natCast]`.

Conclude with `one_add_X_pow_eq_sum_fin_choose p j j.2`. Establish `hrepr : ∀ j i : Fin p, e.repr (v j) i = (((j : ℕ).choose i : ℕ) : R⟦X⟧)`. Introduce `j i`. Rewrite using `[hv, e.repr_sum_self]`. Establish `hdet : e.det v = 1`.

Rewrite using `[Module.Basis.det_apply, Matrix.det_of_upperTriangular]`. Simplify using `[Module.Basis.toMatrix_apply, hrepr]`. Introduce `i j hij`. Simplify using `[Module.Basis.toMatrix_apply, hrepr, Nat.choose_eq_zero_of_lt (show (j : ℕ) < i from hij)]`. Take `⟨hli, hspan⟩` from `(Module.Basis.is_basis_iff_det e).2 (by rw [hdet]; exact isUnit_one)`.

Set `b : Module.Basis (Fin p) R⟦X⟧ (_root_.GlobalTheory.Col.Model.Up R p)` to `Module.Basis.mk hli hspan.ge`. Establish `hb : ∀ i, b i = v i` using `fun i => Module.Basis.mk_apply hli hspan.ge i`. Conclude with `⟨b, hb⟩`. Establish `hu : IsUnit (p : R)` using `by simpa [mem_nonunits_iff] using hn haveI := subsingleton_of_isUnit_natCast_of_isAdicComplete p hR hu haveI : Subsingleton R⟦X⟧ := ⟨fun a b => PowerSeries.ext fun n => Subsingleton.elim _ _⟩ haveI : Subsingleton (_root_.GlobalTheory.Col.Model.Up R p) := ‹Subsingleton R⟦X⟧› haveI …`. Set `b : Module.Basis (Fin p) R⟦X⟧ (_root_.GlobalTheory.Col.Model.Up R p)` to `Module.Basis.ofRepr (LinearEquiv.ofSubsingleton _ _)`.

Establish `hb : ∀ i, b i = _root_.GlobalTheory.Col.Model.toUp p ((1 + X) ^ (i : ℕ))` using `fun i => Subsingleton.elim _ _`. Conclude with `⟨b, hb⟩`.
-/
theorem _root_.GlobalTheory.Col.exists_basis_one_add_X_pow (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime]
    (hR : IsAdicComplete (Ideal.span {(p : R)}) R) :
    ∃ b : @Module.Basis (Fin p) (PowerSeries R) (PowerSeries R) _ _
      (@Algebra.toModule _ _ _ _ (_root_.GlobalTheory.Col.phi (R := R) p hp.out.pos).toRingHom.toAlgebra), ∀ i, b i = (1 + X) ^ (i : ℕ) := by
  by_cases hn : (p : R) ∈ nonunits R
  · haveI := hR
    set e := _root_.GlobalTheory.Col.Model.basis (R := R) p hn
    have he : ∀ i, e i = _root_.GlobalTheory.Col.Model.toUp p (X ^ (i : ℕ)) := fun i => by
      show (_root_.GlobalTheory.Col.Model.basis (R := R) p hn) i = _
      unfold _root_.GlobalTheory.Col.Model.basis
      rw [Module.Basis.mk_apply]
      rfl
    let v : Fin p → _root_.GlobalTheory.Col.Model.Up R p :=
      fun j => _root_.GlobalTheory.Col.Model.toUp p ((1 + X) ^ (j : ℕ))
    have hv : ∀ j : Fin p, v j = ∑ i : Fin p, (((j : ℕ).choose i : ℕ) : R⟦X⟧) • e i := by
      intro j
      simp only [he, Algebra.smul_def, map_natCast]
      exact one_add_X_pow_eq_sum_fin_choose p j j.2
    have hrepr : ∀ j i : Fin p, e.repr (v j) i = (((j : ℕ).choose i : ℕ) : R⟦X⟧) := by
      intro j i
      rw [hv, e.repr_sum_self]
    have hdet : e.det v = 1 := by
      rw [Module.Basis.det_apply, Matrix.det_of_upperTriangular]
      · simp [Module.Basis.toMatrix_apply, hrepr]
      · intro i j hij
        simp [Module.Basis.toMatrix_apply, hrepr, Nat.choose_eq_zero_of_lt (show (j : ℕ) < i from hij)]
    obtain ⟨hli, hspan⟩ := (Module.Basis.is_basis_iff_det e).2 (by rw [hdet]; exact isUnit_one)
    let b : Module.Basis (Fin p) R⟦X⟧ (_root_.GlobalTheory.Col.Model.Up R p) := Module.Basis.mk hli hspan.ge
    have hb : ∀ i, b i = v i := fun i => Module.Basis.mk_apply hli hspan.ge i
    exact ⟨b, hb⟩
  · have hu : IsUnit (p : R) := by simpa [mem_nonunits_iff] using hn
    haveI := subsingleton_of_isUnit_natCast_of_isAdicComplete p hR hu
    haveI : Subsingleton R⟦X⟧ := ⟨fun a b => PowerSeries.ext fun n => Subsingleton.elim _ _⟩
    haveI : Subsingleton (_root_.GlobalTheory.Col.Model.Up R p) := ‹Subsingleton R⟦X⟧›
    haveI : Subsingleton (Fin p →₀ R⟦X⟧) := ⟨fun a b => Finsupp.ext fun i => Subsingleton.elim _ _⟩
    let b : Module.Basis (Fin p) R⟦X⟧ (_root_.GlobalTheory.Col.Model.Up R p) :=
      Module.Basis.ofRepr (LinearEquiv.ofSubsingleton _ _)
    have hb : ∀ i, b i = _root_.GlobalTheory.Col.Model.toUp p ((1 + X) ^ (i : ℕ)) := fun i => Subsingleton.elim _ _
    exact ⟨b, hb⟩

end GlobalTheory.Col
