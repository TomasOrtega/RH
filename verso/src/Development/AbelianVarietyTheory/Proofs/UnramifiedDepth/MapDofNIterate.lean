import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory.InvDerCopiesMap

open MvPowerSeries

variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)

/- English proof (translation)
Use extensionality with `m`. Simplify using `[coeff_map, coeff_pderiv]`.
-/
theorem map_pderiv {σ : Type} (i : σ) (f : MvPowerSeries σ R) :
    MvPowerSeries.map φ (pderiv R i f) = pderiv S i (MvPowerSeries.map φ f) := by
  ext m
  simp [coeff_map, coeff_pderiv]

/- English proof (translation)
Unfold `ev`. Establish `h : HasSubst (fun p : Fin 2 × Fin d => (![pt R d b, 0] : Fin 2 → Pt R n d) p.1 p.2)`. Apply `hasSubst_of_constantCoeff_zero` to reduce the goal to its premises. Introduce and unpack `⟨j, i⟩`. Apply the tactic sequence `fin_cases j <;> simp [pt]`.

Rewrite using `[MvPowerSeries.map_subst h]`. Use `congr 1`. Use function extensionality and compare the values at `⟨j, i⟩`. Apply the tactic sequence `fin_cases j <;> simp [pt]`.
-/
theorem map_ev_axis {d n : ℕ} (b : Fin n) (g : PS R 2 d) :
    MvPowerSeries.map φ (ev (n := n) ![pt R d b, 0] g) =
      ev (n := n) ![pt S d b, 0] (MvPowerSeries.map φ g) := by
  unfold ev
  have h : HasSubst (fun p : Fin 2 × Fin d => (![pt R d b, 0] : Fin 2 → Pt R n d) p.1 p.2) := by
    apply hasSubst_of_constantCoeff_zero
    rintro ⟨j, i⟩
    fin_cases j <;> simp [pt]
  rw [MvPowerSeries.map_subst h]
  congr 1
  funext ⟨j, i⟩
  fin_cases j <;> simp [pt]

/- English proof (translation)
Simplify using `only [DofN, map_sum, map_mul, map_C, map_ev_axis, map_pderiv]`.
-/
theorem map_DofN {d n : ℕ} (F : Fin d → PS R 2 d) (b : Fin n) (u : Fin d → R) (f : PS R n d) :
    MvPowerSeries.map φ (DofN F b u f) =
      DofN (fun i => MvPowerSeries.map φ (F i)) b (fun i => φ (u i)) (MvPowerSeries.map φ f) := by
  simp only [DofN, map_sum, map_mul, map_C, map_ev_axis, map_pderiv]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rfl`. Consider the case `succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', map_DofN, ih]`.
-/
theorem map_DofN_iterate {d n : ℕ} (F : Fin d → PS R 2 d) (b : Fin n) (u : Fin d → R) (k : ℕ)
    (f : PS R n d) :
    MvPowerSeries.map φ ((DofN F b u)^[k] f) =
      (DofN (fun i => MvPowerSeries.map φ (F i)) b (fun i => φ (u i)))^[k] (MvPowerSeries.map φ f) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', map_DofN, ih]

/- English proof (translation)
Unfold `DmonN`. Proceed by induction on `(Finset.univ : Finset ι).toList with`. Consider the case `nil => rfl`. Consider the case `cons l L ih => rw [List.foldr_cons, List.foldr_cons, map_DofN_iterate, ih]`.
-/
theorem map_DmonN {d n : ℕ} (F : Fin d → PS R 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n)
    (u : ι → Fin d → R) (m : ι →₀ ℕ) (f : PS R n d) :
    MvPowerSeries.map φ (DmonN F cp u m f) =
      DmonN (fun i => MvPowerSeries.map φ (F i)) cp (fun l i => φ (u l i)) m (MvPowerSeries.map φ f) := by
  unfold DmonN
  induction (Finset.univ : Finset ι).toList with
  | nil => rfl
  | cons l L ih => rw [List.foldr_cons, List.foldr_cons, map_DofN_iterate, ih]

end GlobalTheory.InvDerCopiesMap

namespace GlobalTheory

/- English proof (translation)
Introduce `S S' _ _ ψ d n F κ _ cp u P f`. Unfold `DpolyN`. Rewrite using `[Finset.sum_subset (MvPolynomial.support_map_subset ψ P) (fun m _ hm => by`. Rewrite using `[MvPolynomial.notMem_support_iff.1 hm, map_zero, zero_mul]), map_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, MvPowerSeries.map_C, InvDerCopiesMap.map_DmonN, MvPolynomial.coeff_map]`.
-/
theorem dpolyN_map : ∀ (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (d n : ℕ) (F : Fin d → PS S 2 d) (κ : Type) [Fintype κ] (cp : κ → Fin n) (u : κ → Fin d → S) (P : MvPolynomial κ S) (f : PS S n d), DpolyN (fun i => MvPowerSeries.map ψ (F i)) cp (fun l j => ψ (u l j)) (MvPolynomial.map ψ P) (MvPowerSeries.map ψ f) = MvPowerSeries.map ψ (DpolyN F cp u P f) := by
  intro S S' _ _ ψ d n F κ _ cp u P f
  unfold DpolyN
  rw [Finset.sum_subset (MvPolynomial.support_map_subset ψ P) (fun m _ hm => by
    rw [MvPolynomial.notMem_support_iff.1 hm, map_zero, zero_mul]), map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, MvPowerSeries.map_C, InvDerCopiesMap.map_DmonN, MvPolynomial.coeff_map]

end GlobalTheory
