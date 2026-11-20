import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDegreeEqFormDegree

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagFormDeg (apolar apolar_monomial apolar_X_mul apolar_sum_left)

namespace GlobalTheory.VdmCoeff

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty`. Rewrite using `[Finset.prod_empty, ← MvPolynomial.C_1, MvPolynomial.C_apply, apolar_monomial]`. Simplify using the standard rewrite rules. Consider the case `insert e S he ih`.

Establish `hd (x : U) : MvPolynomial.pderiv x (lin n) = MvPolynomial.C (n x)`. Simplify using `[lin, Pi.single_apply, MvPolynomial.pderiv_X]`. Establish `h1 (x : U) : apolar (MvPolynomial.pderiv x (lin n ^ (S.card + 1))) (∏ e ∈ S, lin (c e)) = ((S.card + 1) * n x) * apolar (lin n ^ S.card) (∏ e ∈ S, lin (c e))`. Use `apolar_sum_left (Finset.univ : Finset Unit) (fun _ => ((S.card + 1) * n x : ℝ)) (fun _ => lin n ^ S.card) (∏ e ∈ S, lin (c e))` as an intermediate fact. Simplify using `only [Finset.univ_unique, Finset.sum_singleton] at this`.

Rewrite using `[← this, MvPolynomial.pderiv_pow, hd]`. Use `congr 2`. Simplify using `only [map_mul, map_add, map_natCast, map_one, Nat.add_sub_cancel]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[Finset.card_insert_of_notMem he, Finset.prod_insert he, Finset.prod_insert he]`. Use `nth_rewrite 2 [lin]`. Rewrite using `[Finset.sum_mul, map_sum]`. Simplify using `only [mul_assoc, MvPolynomial.C_mul', map_smul, smul_mul_assoc, apolar_X_mul, smul_eq_mul, h1, ih]`. Rewrite using `[Nat.factorial_succ, Finset.sum_mul, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem apolar_lin_pow {U E : Type} [Fintype U] (n : U → ℝ) (c : E → U → ℝ) (S : Finset E) :
    apolar (lin n ^ S.card) (∏ e ∈ S, lin (c e)) = S.card.factorial * ∏ e ∈ S, ∑ x, n x * c e x := by
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, ← MvPolynomial.C_1, MvPolynomial.C_apply, apolar_monomial]
    simp
  | insert e S he ih =>
    have hd (x : U) : MvPolynomial.pderiv x (lin n) = MvPolynomial.C (n x) := by
      simp [lin, Pi.single_apply, MvPolynomial.pderiv_X]
    have h1 (x : U) : apolar (MvPolynomial.pderiv x (lin n ^ (S.card + 1))) (∏ e ∈ S, lin (c e)) =
        ((S.card + 1) * n x) * apolar (lin n ^ S.card) (∏ e ∈ S, lin (c e)) := by
      have := apolar_sum_left (Finset.univ : Finset Unit) (fun _ => ((S.card + 1) * n x : ℝ))
        (fun _ => lin n ^ S.card) (∏ e ∈ S, lin (c e))
      simp only [Finset.univ_unique, Finset.sum_singleton] at this
      rw [← this, MvPolynomial.pderiv_pow, hd]
      congr 2
      simp only [map_mul, map_add, map_natCast, map_one, Nat.add_sub_cancel]
      push_cast
      ring
    rw [Finset.card_insert_of_notMem he, Finset.prod_insert he, Finset.prod_insert he]
    nth_rewrite 2 [lin]
    rw [Finset.sum_mul, map_sum]
    simp only [mul_assoc, MvPolynomial.C_mul', map_smul, smul_mul_assoc, apolar_X_mul, smul_eq_mul, h1, ih]
    rw [Nat.factorial_succ, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    push_cast
    ring

variable {ι : Type} [Fintype ι] {r : ι → ℕ}

/- English proof (translation)
Rewrite using `[vdm, Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations. Establish `h (s : Low (r a)) : lin (fun x => rootDiag θ x (some ⟨a, s⟩)) = MvPolynomial.X (⟨a, s.1.1⟩ : Σ a, Fin (r a)) - MvPolynomial.X ⟨a, s.1.2⟩`. Simplify using `[lin, rootDiag, sub_mul, Finset.sum_sub_distrib, apply_ite MvPolynomial.C, ite_mul]`. Simplify using `only [h]`.

Rewrite using `[Finset.prod_sigma']`. Use `Finset.prod_bij (fun s _ => ⟨s.1.2, s.1.1⟩) (fun s _ => by simpa using s.2) ?_ ?_ fun _ _ => rfl` and prove the remaining obligations. Introduce and unpack `⟨⟨i, j⟩, h⟩ _ ⟨⟨i', j'⟩, h'⟩ _ e`. Simplify using `only [Sigma.mk.injEq, heq_eq_eq] at e`. Take `⟨rfl, rfl⟩` from `e`.

Both sides reduce to the same expression. Introduce and unpack `⟨i, j⟩ h`. Conclude with `⟨⟨(j, i), by simpa using h⟩, Finset.mem_univ _, rfl⟩`.
-/
theorem prod_lin_rootDiag (θ : (Σ a, Fin (r a)) → ℝ) :
    ∏ s : Σ a, Low (r a), lin (fun x => rootDiag θ x (some s)) = vdm r := by
  rw [vdm, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun a _ => ?_
  have h (s : Low (r a)) : lin (fun x => rootDiag θ x (some ⟨a, s⟩)) =
      MvPolynomial.X (⟨a, s.1.1⟩ : Σ a, Fin (r a)) - MvPolynomial.X ⟨a, s.1.2⟩ := by
    simp [lin, rootDiag, sub_mul, Finset.sum_sub_distrib, apply_ite MvPolynomial.C, ite_mul]
  simp only [h]
  rw [Finset.prod_sigma']
  refine Finset.prod_bij (fun s _ => ⟨s.1.2, s.1.1⟩) (fun s _ => by simpa using s.2) ?_ ?_ fun _ _ => rfl
  · rintro ⟨⟨i, j⟩, h⟩ _ ⟨⟨i', j'⟩, h'⟩ _ e
    simp only [Sigma.mk.injEq, heq_eq_eq] at e
    obtain ⟨rfl, rfl⟩ := e
    rfl
  · rintro ⟨i, j⟩ h
    exact ⟨⟨(j, i), by simpa using h⟩, Finset.mem_univ _, rfl⟩

def pexp (σ : ∀ a, Equiv.Perm (Fin (r a))) : (Σ a, Fin (r a)) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun x => σ x.1 x.2

/- English proof (translation)
Introduce `σ τ h`. Use extensionality with `a i`. Simplify `DFunLike.congr_fun h ⟨a, i⟩` using `[pexp]`.
-/
theorem pexp_injective : Function.Injective (pexp (r := r)) := by
  intro σ τ h
  ext a i
  simpa [pexp] using DFunLike.congr_fun h ⟨a, i⟩

/- English proof (translation)
Establish `h (a : ι) : ∏ i : Fin (r a), ∏ i' ∈ Finset.Ioi i, (MvPolynomial.X (⟨a, i'⟩ : Σ a, Fin (r a)) - MvPolynomial.X ⟨a, i⟩ : MvPolynomial (Σ a, Fin (r a)) ℝ) = ∑ σ : Equiv.Perm (Fin (r a)), MvPolynomial.C ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, MvPolynomial.X (⟨a, i⟩ : Σ a, Fin (r a)) ^ ( …`. Rewrite using `[← Matrix.det_vandermonde (fun i => (MvPolynomial.X (⟨a, i⟩ : Σ a, Fin (r a)) : MvPolynomial (Σ a, Fin (r a)) ℝ)), ← Matrix.det_transpose, Matrix.det_apply']`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Rewrite using `[vdm]`.

Simplify using `only [h]`. Rewrite using `[Finset.prod_univ_sum, Fintype.piFinset_univ]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_mul_distrib, ← map_prod, MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sigma]`. Both sides reduce to the same expression.
-/
theorem vdm_eq : vdm r = ∑ σ : ∀ a, Equiv.Perm (Fin (r a)),
    MvPolynomial.monomial (pexp σ) (∏ a, ((Equiv.Perm.sign (σ a) : ℤ) : ℝ)) := by
  have h (a : ι) : ∏ i : Fin (r a), ∏ i' ∈ Finset.Ioi i,
      (MvPolynomial.X (⟨a, i'⟩ : Σ a, Fin (r a)) - MvPolynomial.X ⟨a, i⟩ : MvPolynomial (Σ a, Fin (r a)) ℝ) =
      ∑ σ : Equiv.Perm (Fin (r a)), MvPolynomial.C ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∏ i, MvPolynomial.X (⟨a, i⟩ : Σ a, Fin (r a)) ^ (σ i : ℕ) := by
    rw [← Matrix.det_vandermonde (fun i => (MvPolynomial.X (⟨a, i⟩ : Σ a, Fin (r a)) :
      MvPolynomial (Σ a, Fin (r a)) ℝ)), ← Matrix.det_transpose, Matrix.det_apply']
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp
  rw [vdm]
  simp only [h]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib, ← map_prod, MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (by simp),
    Fintype.prod_sigma]
  rfl

/- English proof (translation)
Establish `hc (σ : ∀ a, Equiv.Perm (Fin (r a))) : (vdm r).coeff (pexp σ) = ∏ a, ((Equiv.Perm.sign (σ a) : ℤ) : ℝ)`. Rewrite using `[vdm_eq, MvPolynomial.coeff_sum, Finset.sum_eq_single σ]`. Simplify using the standard rewrite rules. Introduce `τ _ h`. Rewrite using `[MvPolynomial.coeff_monomial, if_neg fun e => h (pexp_injective e)]`.

Simplify using the standard rewrite rules. Establish `hf (σ : ∀ a, Equiv.Perm (Fin (r a))) : ∏ x, ((pexp σ x).factorial : ℝ) = ∏ a, ∏ l ∈ Finset.range (r a), (l.factorial : ℝ)`. Rewrite using `[Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← Fin.prod_univ_eq_prod_range (fun l => (l.factorial : ℝ))]`.

Conclude with `Equiv.prod_comp (σ a) fun i : Fin (r a) => (((i : ℕ).factorial : ℕ) : ℝ)`. Establish `hs (σ : ∀ a, Equiv.Perm (Fin (r a))) : (∏ a, ((Equiv.Perm.sign (σ a) : ℤ) : ℝ)) * ∏ a, ((Equiv.Perm.sign (σ a) : ℤ) : ℝ) = 1`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_eq_one fun a _ => ?_` and prove the remaining obligations. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign (σ a)) with h | h <;> simp [h]`.

Use `nth_rewrite 2 [vdm_eq]`. Rewrite using `[map_sum]`. Simplify using `only [apolar_monomial, hc, hf, mul_left_comm _ (∏ a, ∏ l ∈ Finset.range (r a), (l.factorial : ℝ)), hs]`. Simplify using `[Finset.prod_range_succ, Finset.prod_mul_distrib, Fintype.card_perm, mul_comm]`.
-/
theorem apolar_vdm : apolar (vdm r) (vdm r) = ∏ a, ∏ l ∈ Finset.range (r a + 1), (l.factorial : ℝ) := by
  have hc (σ : ∀ a, Equiv.Perm (Fin (r a))) :
      (vdm r).coeff (pexp σ) = ∏ a, ((Equiv.Perm.sign (σ a) : ℤ) : ℝ) := by
    rw [vdm_eq, MvPolynomial.coeff_sum, Finset.sum_eq_single σ]
    · simp
    · intro τ _ h
      rw [MvPolynomial.coeff_monomial, if_neg fun e => h (pexp_injective e)]
    · simp
  have hf (σ : ∀ a, Equiv.Perm (Fin (r a))) :
      ∏ x, ((pexp σ x).factorial : ℝ) = ∏ a, ∏ l ∈ Finset.range (r a), (l.factorial : ℝ) := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← Fin.prod_univ_eq_prod_range (fun l => (l.factorial : ℝ))]
    exact Equiv.prod_comp (σ a) fun i : Fin (r a) => (((i : ℕ).factorial : ℕ) : ℝ)
  have hs (σ : ∀ a, Equiv.Perm (Fin (r a))) :
      (∏ a, ((Equiv.Perm.sign (σ a) : ℤ) : ℝ)) * ∏ a, ((Equiv.Perm.sign (σ a) : ℤ) : ℝ) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun a _ => ?_
    rcases Int.units_eq_one_or (Equiv.Perm.sign (σ a)) with h | h <;> simp [h]
  nth_rewrite 2 [vdm_eq]
  rw [map_sum]
  simp only [apolar_monomial, hc, hf, mul_left_comm _ (∏ a, ∏ l ∈ Finset.range (r a), (l.factorial : ℝ)), hs]
  simp [Finset.prod_range_succ, Finset.prod_mul_distrib, Fintype.card_perm, mul_comm]

/- English proof (translation)
Introduce `ι _ r I _ c n h θ`. Establish `h1` using `apolar_sum_left Finset.univ c (fun j => lin (fun x => (n j x : ℝ)) ^ Fintype.card (Σ a, Low (r a))) (vdm r)`. Simplify using `only [MvPolynomial.C_mul'] at h1`. Rewrite `h1` using `[h, apolar_vdm]`. Rewrite using `[h1]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← prod_lin_rootDiag θ, ← Finset.card_univ, apolar_lin_pow]`.
-/
theorem coeff_vdm : ∀ (ι : Type) [Fintype ι] (r : ι → ℕ) (I : Type) [Fintype I] (c : I → ℝ) (n : I → (Σ a, Fin (r a)) → ℤ), ∑ j, c j • lin (fun x => (n j x : ℝ)) ^ Fintype.card (Σ a, Low (r a)) = vdm r → ∀ θ : (Σ a, Fin (r a)) → ℝ, ∑ j, c j * ((Fintype.card (Σ a, Low (r a))).factorial * ∏ s : Σ a, Low (r a), ∑ x, (n j x : ℝ) * rootDiag θ x (some s)) = ∏ a, ∏ l ∈ Finset.range (r a + 1), (l.factorial : ℝ) := by
  intro ι _ r I _ c n h θ
  have h1 := apolar_sum_left Finset.univ c
    (fun j => lin (fun x => (n j x : ℝ)) ^ Fintype.card (Σ a, Low (r a))) (vdm r)
  simp only [MvPolynomial.C_mul'] at h1
  rw [h, apolar_vdm] at h1
  rw [h1]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← prod_lin_rootDiag θ, ← Finset.card_univ, apolar_lin_pow]

end GlobalTheory.VdmCoeff
