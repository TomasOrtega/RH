import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.DofDApply

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.EigenCongruence

variable {R : Type} [CommRing R] {d : ℕ}

def coeffIdeal {σ : Type} (I : Ideal R) : Ideal (MvPowerSeries σ R) where
  carrier := {g | ∀ mo, coeff mo g ∈ I}
  add_mem' := by
    intro a b ha hb mo
    rw [map_add]
    exact I.add_mem (ha mo) (hb mo)
  zero_mem' := by
    intro mo
    rw [map_zero]
    exact I.zero_mem
  smul_mem' := by
    classical
    intro c x hx mo
    rw [smul_eq_mul, coeff_mul]
    exact I.sum_mem fun p _ => I.mul_mem_left _ (hx p.2)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_coeffIdeal {σ : Type} {I : Ideal R} {g : MvPowerSeries σ R} :
    g ∈ coeffIdeal I ↔ ∀ mo, coeff mo g ∈ I := Iff.rfl

/- English proof (translation)
Introduce `mo`. Rewrite using `[coeff_pderiv]`. Conclude with `I.mul_mem_right _ (hg _)`.
-/
theorem pderiv_mem_coeffIdeal {σ : Type} {I : Ideal R} {g : MvPowerSeries σ R}
    (hg : g ∈ coeffIdeal I) (s : σ) : pderiv R s g ∈ coeffIdeal I := by
  intro mo
  rw [coeff_pderiv]
  exact I.mul_mem_right _ (hg _)

/- English proof (translation)
The claim follows from `Ideal.sum_mem _ fun _ _ => Ideal.mul_mem_left _ _ (pderiv_mem_coeffIdeal hg _)`.
-/
theorem dof_mem_coeffIdeal (F : Fin d → PS R 2 d) (v : Fin d → R) {I : Ideal R} {g : PS R 1 d}
    (hg : g ∈ coeffIdeal I) : Dof F v g ∈ coeffIdeal I :=
  Ideal.sum_mem _ fun _ _ => Ideal.mul_mem_left _ _ (pderiv_mem_coeffIdeal hg _)

/- English proof (translation)
Establish `h1 : Dof F v g = Dof F v (g - C c * f) + C c * Dof F v f`. Rewrite using `[← GE.dof_C_mul, ← GE.dof_add, sub_add_cancel]`. Establish `h2 : Dof F v g - C (y * c) * f = Dof F v (g - C c * f) + C c * (Dof F v f - C y * f)`. Rewrite using `[h1, map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h2]`. Conclude with `Ideal.add_mem _ (dof_mem_coeffIdeal F v hg) (Ideal.mul_mem_left _ _ hf)`.
-/
theorem dof_step (F : Fin d → PS R 2 d) (v : Fin d → R) (y c : R) {I : Ideal R} {f g : PS R 1 d}
    (hf : Dof F v f - C y * f ∈ coeffIdeal I) (hg : g - C c * f ∈ coeffIdeal I) :
    Dof F v g - C (y * c) * f ∈ coeffIdeal I := by
  have h1 : Dof F v g = Dof F v (g - C c * f) + C c * Dof F v f := by
    rw [← GE.dof_C_mul, ← GE.dof_add, sub_add_cancel]
  have h2 : Dof F v g - C (y * c) * f =
      Dof F v (g - C c * f) + C c * (Dof F v f - C y * f) := by
    rw [h1, map_mul]; ring
  rw [h2]
  exact Ideal.add_mem _ (dof_mem_coeffIdeal F v hg) (Ideal.mul_mem_left _ _ hf)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using hg`. Consider the case `succ n ih`. Rewrite using `[Function.iterate_succ_apply', pow_succ', mul_assoc]`. Conclude with `dof_step F v y _ hf ih`.
-/
theorem dof_iterate (F : Fin d → PS R 2 d) (v : Fin d → R) (y c : R) {I : Ideal R}
    {f g : PS R 1 d} (hf : Dof F v f - C y * f ∈ coeffIdeal I) (hg : g - C c * f ∈ coeffIdeal I)
    (n : ℕ) : (Dof F v)^[n] g - C (y ^ n * c) * f ∈ coeffIdeal I := by
  induction n with
  | zero => simpa using hg
  | succ n ih =>
    rw [Function.iterate_succ_apply', pow_succ', mul_assoc]
    exact dof_step F v y _ hf ih

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => simp`. Consider the case `cons a L ih`. Rewrite using `[List.foldr_cons, List.map_cons, List.prod_cons]`. Conclude with `dof_iterate F (u a) (y a) _ (hf a) ih (m a)`.
-/
theorem foldr_sub_mem (F : Fin d → PS R 2 d) {I : Ideal R} {ι : Type} (u : ι → Fin d → R)
    (y : ι → R) (f : PS R 1 d) (hf : ∀ l, Dof F (u l) f - C (y l) * f ∈ coeffIdeal I)
    (m : ι → ℕ) (L : List ι) :
    L.foldr (fun l g => (Dof F (u l))^[m l] g) f - C (L.map fun l => y l ^ m l).prod * f ∈
      coeffIdeal I := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.foldr_cons, List.map_cons, List.prod_cons]
    exact dof_iterate F (u a) (y a) _ (hf a) ih (m a)

/- English proof (translation)
Establish `h` using `foldr_sub_mem F u y f hf m (Finset.univ : Finset ι).toList`. Rewrite `h` using `[Finset.prod_map_toList]`. Then use the resulting hypothesis.
-/
theorem dmonOf_sub_mem (F : Fin d → PS R 2 d) {I : Ideal R} {ι : Type} [Fintype ι]
    (u : ι → Fin d → R) (y : ι → R) (f : PS R 1 d)
    (hf : ∀ l, Dof F (u l) f - C (y l) * f ∈ coeffIdeal I) (m : ι →₀ ℕ) :
    DmonOf F u m f - C (∏ l, y l ^ m l) * f ∈ coeffIdeal I := by
  have h := foldr_sub_mem F u y f hf m (Finset.univ : Finset ι).toList
  rwa [Finset.prod_map_toList] at h

end GlobalTheory.EigenCongruence

namespace GlobalTheory

/- English proof (translation)
Introduce `R _ d F I ι _ u y f hf m`. Establish `h` using `EigenCongruence.dmonOf_sub_mem F u y f hf m 0`. Rewrite `h` using `[coeff_zero_eq_constantCoeff, map_sub, map_mul, constantCoeff_C]`. Then use the resulting hypothesis.
-/
theorem constantCoeff_dmonOf_sub_mem :
    ∀ (R : Type) [CommRing R] (d : ℕ) (F : Fin d → PS R 2 d) (I : Ideal R) (ι : Type) [Fintype ι]
      (u : ι → Fin d → R) (y : ι → R) (f : PS R 1 d),
      (∀ l mo, coeff mo (Dof F (u l) f - C (y l) * f) ∈ I) →
      ∀ m : ι →₀ ℕ, constantCoeff (DmonOf F u m f) - (∏ l, y l ^ m l) * constantCoeff f ∈ I := by
  intro R _ d F I ι _ u y f hf m
  have h := EigenCongruence.dmonOf_sub_mem F u y f hf m 0
  rwa [coeff_zero_eq_constantCoeff, map_sub, map_mul, constantCoeff_C] at h

end GlobalTheory
