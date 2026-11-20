import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaSt
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace PositivityTheory.Xgp.fib_mdisc

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Matrix

/- English proof (translation)
Rewrite using `[← mul_assoc, mul_one_div_cancel (by exact_mod_cast n.factorial_ne_zero), one_mul]`.
-/
theorem fac_cancel (n : ℕ) (S : ℂ) : (n.factorial : ℂ) * ((1 / (n.factorial : ℂ)) * S) = S := by
  rw [← mul_assoc, mul_one_div_cancel (by exact_mod_cast n.factorial_ne_zero), one_mul]

/- English proof (translation)
Rewrite using `[Matrix.det_succ_column_zero, Fin.sum_univ_succ]`. Simplify using `[h0, hcol]`.
-/
theorem det_block {d : ℕ} (c : ℂ) (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (h0 : M 0 0 = c) (hcol : ∀ i : Fin d, M i.succ 0 = 0) :
    M.det = c * (M.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [h0, hcol]

noncomputable def phi {d : ℕ} (x : Fin (d + 1) × Equiv.Perm (Fin d)) : Equiv.Perm (Fin (d + 1)) :=
  x.1.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, x.2)

/- English proof (translation)
Simplify using `[phi, Equiv.Perm.decomposeFin_symm_apply_zero, Fin.cycleRange_symm_zero]`.
-/
theorem phi_zero {d : ℕ} (x : Fin (d + 1) × Equiv.Perm (Fin d)) : phi x 0 = x.1 := by
  simp [phi, Equiv.Perm.decomposeFin_symm_apply_zero, Fin.cycleRange_symm_zero]

/- English proof (translation)
Simplify using `[phi, Equiv.Perm.decomposeFin_symm_apply_succ, Fin.cycleRange_symm_succ]`.
-/
theorem phi_succ {d : ℕ} (x : Fin (d + 1) × Equiv.Perm (Fin d)) (j : Fin d) :
    phi x j.succ = x.1.succAbove (x.2 j) := by
  simp [phi, Equiv.Perm.decomposeFin_symm_apply_succ, Fin.cycleRange_symm_succ]

/- English proof (translation)
Use `(Fintype.bijective_iff_injective_and_card _).2 ⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨r, τ⟩ ⟨r', τ'⟩ h`. Establish `h0 : r = r'`. Use `congrArg (fun σ : Equiv.Perm (Fin (d + 1)) => σ 0) h` as an intermediate fact. Simplify `this` using `[phi_zero]`.

Substitute `h0` using the available equality. Establish `h1 : Equiv.Perm.decomposeFin.symm ((0 : Fin (d + 1)), τ) = Equiv.Perm.decomposeFin.symm ((0 : Fin (d + 1)), τ')` using `mul_left_cancel h`. Use `Equiv.Perm.decomposeFin.symm.injective h1` as an intermediate fact. Simplify using `only [Prod.mk.injEq, true_and] at this`. Rewrite using `[this]`.

Simplify using `[Fintype.card_prod, Fintype.card_perm, Fintype.card_fin, Nat.factorial_succ]`.
-/
theorem phi_bijective (d : ℕ) : Function.Bijective (phi (d := d)) := by
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨?_, ?_⟩
  · rintro ⟨r, τ⟩ ⟨r', τ'⟩ h
    have h0 : r = r' := by
      have := congrArg (fun σ : Equiv.Perm (Fin (d + 1)) => σ 0) h
      simpa [phi_zero] using this
    subst h0
    have h1 : Equiv.Perm.decomposeFin.symm ((0 : Fin (d + 1)), τ) =
        Equiv.Perm.decomposeFin.symm ((0 : Fin (d + 1)), τ') := mul_left_cancel h
    have := Equiv.Perm.decomposeFin.symm.injective h1
    simp only [Prod.mk.injEq, true_and] at this
    rw [this]
  · simp [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin, Nat.factorial_succ]

/- English proof (translation)
Simplify using `only [mdisc_eq_sum_perm, fac_cancel]`. Establish `hterm : ∀ σ : Equiv.Perm (Fin (d + 1)), (Matrix.of fun i j => (Matrix.of fun p q : Fin (d + 1) => Fin.cases (Fin.cases (f (σ j)) (fun _ => 0) q) (fun p' => Fin.cases 0 (fun q' => Bm (σ j) p' q') q) p : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) i j).det = f (σ 0) * (Matrix.of fun i j …`. Introduce `σ`. Rewrite using `[det_block (f (σ 0))]`. Use `congr 1`.

Simplify using the standard rewrite rules. Introduce `i`. Simplify using the standard rewrite rules. Simplify using `only [hterm]`. Simplify using `only [Finset.mul_sum]`.

Rewrite using `[← Fintype.sum_prod_type']`. Use `symm`. Use `Fintype.sum_bijective phi (phi_bijective d) _ _ fun x => ?_` and prove the remaining obligations. Simplify using `only [phi_zero, phi_succ]`.
-/
theorem part1 (d : ℕ) (f : Fin (d + 1) → ℂ) (Bm : Fin (d + 1) → Matrix (Fin d) (Fin d) ℂ) :
    ((d + 1).factorial : ℂ) * mdisc (fun r => Matrix.of fun p q : Fin (d + 1) =>
      Fin.cases (Fin.cases (f r) (fun _ => 0) q) (fun p' => Fin.cases 0 (fun q' => Bm r p' q') q) p) =
      ∑ r, f r * ((d.factorial : ℂ) * mdisc fun s => Bm (r.succAbove s)) := by
  classical
  simp only [mdisc_eq_sum_perm, fac_cancel]
  have hterm : ∀ σ : Equiv.Perm (Fin (d + 1)),
      (Matrix.of fun i j => (Matrix.of fun p q : Fin (d + 1) =>
        Fin.cases (Fin.cases (f (σ j)) (fun _ => 0) q)
          (fun p' => Fin.cases 0 (fun q' => Bm (σ j) p' q') q) p : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) i j).det =
        f (σ 0) * (Matrix.of fun i j => Bm (σ j.succ) i j).det := by
    intro σ
    rw [det_block (f (σ 0))]
    · congr 1
    · simp
    · intro i; simp
  simp only [hterm]
  simp only [Finset.mul_sum]
  rw [← Fintype.sum_prod_type']
  symm
  refine Fintype.sum_bijective phi (phi_bijective d) _ _ fun x => ?_
  simp only [phi_zero, phi_succ]

end PositivityTheory.Xgp.fib_mdisc

/- English proof (translation)
Introduce `d`. Use `⟨PositivityTheory.Xgp.fib_mdisc.part1 d, ?_⟩` and prove the remaining obligations. Take `⟨M, hM⟩` from `ReciprocityTheory.AnForm.A.exists_multilinearMap_eq_mdisc (D := d)`. Conclude with `⟨M, fun Bm => by rw [hM], fun π Bm => by rw [hM, ReciprocityTheory.AnForm.A.mdisc_comp_perm]⟩`.
-/
theorem PositivityTheory.Xgp.t_fib_mdisc : ∀ (d : ℕ), (∀ (f : Fin (d + 1) → ℂ) (Bm : Fin (d + 1) → Matrix (Fin d) (Fin d) ℂ), ((d + 1).factorial : ℂ) * mdisc (fun r => Matrix.of fun p q : Fin (d + 1) => Fin.cases (Fin.cases (f r) (fun _ => 0) q) (fun p' => Fin.cases 0 (fun q' => Bm r p' q') q) p) = ∑ r, f r * ((d.factorial : ℂ) * mdisc fun s => Bm (r.succAbove s))) ∧ ∃ Λ : MultilinearMap ℂ (fun _ : Fin d => Matrix (Fin d) (Fin d) ℂ) ℂ, (∀ Bm, Λ Bm = mdisc Bm) ∧ ∀ (π : Equiv.Perm (Fin d)) Bm, Λ (Bm ∘ π) = Λ Bm := by
  intro d
  refine ⟨PositivityTheory.Xgp.fib_mdisc.part1 d, ?_⟩
  obtain ⟨M, hM⟩ := ReciprocityTheory.AnForm.A.exists_multilinearMap_eq_mdisc (D := d)
  exact ⟨M, fun Bm => by rw [hM], fun π Bm => by rw [hM, ReciprocityTheory.AnForm.A.mdisc_comp_perm]⟩
