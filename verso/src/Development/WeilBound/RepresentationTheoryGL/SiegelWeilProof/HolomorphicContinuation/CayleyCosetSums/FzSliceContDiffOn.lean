import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.DerivEqFderivPair
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.AbsArgLtPi

noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

/- English proof (translation)
The claim follows from `((fzHol n m 0).2.2).contDiffOn_of_completeSpace`.
-/
theorem fz_contDiffOn (m : ℕ) : ContDiffOn ℂ ∞ (fun p : ℂ × M2 n => fz m 0 p.1 p.2) (Set.univ ×ˢ DomZ n) :=
  ((fzHol n m 0).2.2).contDiffOn_of_completeSpace

/- English proof (translation)
The claim follows from `deriv_eq_fderiv_pair (fun p : ℂ × M2 n => fz m 0 p.1 p.2) 0 y (((fz_contDiffOn m).contDiffAt ((isOpen_univ.prod isOpen_domZ).mem_nhds ⟨Set.mem_univ _, hy⟩)).differentiableAt (by simp))`.
-/
theorem Fd_eq (m : ℕ) {y : M2 n} (hy : y ∈ DomZ n) :
    Fd m y = fderiv ℂ (fun p : ℂ × M2 n => fz m 0 p.1 p.2) (0, y) (1, 0) :=
  deriv_eq_fderiv_pair (fun p : ℂ × M2 n => fz m 0 p.1 p.2) 0 y
    (((fz_contDiffOn m).contDiffAt ((isOpen_univ.prod isOpen_domZ).mem_nhds ⟨Set.mem_univ _, hy⟩)).differentiableAt
      (by simp))

/- English proof (translation)
Establish `hO : IsOpen (Set.univ ×ˢ DomZ n : Set (ℂ × M2 n))` using `isOpen_univ.prod isOpen_domZ`. Establish `h1 : ContDiffOn ℂ ∞ (fun p : ℂ × M2 n => fderiv ℂ (fun p : ℂ × M2 n => fz m 0 p.1 p.2) p (1, 0)) (Set.univ ×ˢ DomZ n)` using `((fz_contDiffOn m).fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const`. Establish `h2 : ContDiffOn ℂ ∞ (fun y : M2 n => fderiv ℂ (fun p : ℂ × M2 n => fz m 0 p.1 p.2) (0, y) (1, 0)) (DomZ n)` using `h1.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun y hy => ⟨Set.mem_univ _, hy⟩)`. Conclude with `h2.congr fun y hy => Fd_eq m hy`.
-/
theorem Fd_contDiffOn (m : ℕ) : ContDiffOn ℂ ∞ (Fd (n := n) m) (DomZ n) := by
  have hO : IsOpen (Set.univ ×ˢ DomZ n : Set (ℂ × M2 n)) := isOpen_univ.prod isOpen_domZ
  have h1 : ContDiffOn ℂ ∞ (fun p : ℂ × M2 n => fderiv ℂ (fun p : ℂ × M2 n => fz m 0 p.1 p.2) p (1, 0))
      (Set.univ ×ˢ DomZ n) :=
    ((fz_contDiffOn m).fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const
  have h2 : ContDiffOn ℂ ∞ (fun y : M2 n => fderiv ℂ (fun p : ℂ × M2 n => fz m 0 p.1 p.2) (0, y) (1, 0)) (DomZ n) :=
    h1.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun y hy => ⟨Set.mem_univ _, hy⟩)
  exact h2.congr fun y hy => Fd_eq m hy

/- English proof (translation)
Establish `hl : ContDiff ℂ ∞ (fun y : M2 n => ((z : ℂ), y))` using `contDiff_const.prodMk contDiff_id`. Establish `h` using `(fz_contDiffOn (n := n) m).comp hl.contDiffOn (fun y hy => (⟨Set.mem_univ _, hy⟩ : ((z : ℂ), y) ∈ Set.univ ×ˢ DomZ n))`. Conclude with `h`.
-/
theorem fz_slice_contDiffOn (m : ℕ) (z : ℂ) : ContDiffOn ℂ ∞ (fz (n := n) m 0 z) (DomZ n) := by
  have hl : ContDiff ℂ ∞ (fun y : M2 n => ((z : ℂ), y)) := contDiff_const.prodMk contDiff_id
  have h := (fz_contDiffOn (n := n) m).comp hl.contDiffOn (fun y hy => (⟨Set.mem_univ _, hy⟩ : ((z : ℂ), y) ∈ Set.univ ×ˢ DomZ n))
  exact h

/- English proof (translation)
Introduce `n m j x hj1 hj hx`. Use `set U : ℂ × M2 n → ℂ := fun p => fz m 0 p.1 p.2 with hUdef`. Establish `hU : ContDiffOn ℂ ∞ U (Set.univ ×ˢ DomZ n)` using `fz_contDiffOn m`. Establish `hD : IsOpen (DomZ n)` using `isOpen_domZ`. Establish `hO : IsOpen (Set.univ ×ˢ DomZ n : Set (ℂ × M2 n))` using `isOpen_univ.prod hD`.

Establish `expand : ∀ F : M2 n → ℂ, ContDiffOn ℂ ∞ F (DomZ n) → detD (fun T : Matrix (blkA (n` using `n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ => F (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1))) = ∑ σ : Equiv.Perm (blkA (n := n) j), ∑ τ : Equiv.Perm (blkB (n := n) j), (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) * iteratedFDeriv ℂ (Fintype. …`. Introduce `F hF`. Establish `hrw : (fun T : Matrix (blkA (n` using `n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ => F (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1))) = (fun T => detD (fun S => F (x + LQ (blkA j) x T + LR (blkB j) x S))) := by`. Use function extensionality and compare the values at `T`. Use `congr 1`.

Use function extensionality and compare the values at `S`. Rewrite using `[mul_mX, LQ_apply, LR_apply]`. Rewrite using `[hrw]`. Conclude with `detD_detD_comp F (DomZ n) hD hF x hx (LQ (blkA j) x) (LR (blkB j) x)`. Establish `hcomm : ∀ (k : ℕ) (v : Fin k → M2 n), iteratedFDeriv ℂ k (Fd m) x v = deriv (fun z => iteratedFDeriv ℂ k (fz m 0 z) x v) 0` using `fun k v => iFD_deriv_comm U (DomZ n) hD hU x hx k v`.

Establish `hdiff : ∀ (k : ℕ) (v : Fin k → M2 n), DifferentiableAt ℂ (fun z => iteratedFDeriv ℂ k (fz m 0 z) x v) 0`. Introduce `k v`. Establish `e : (fun z => iteratedFDeriv ℂ k (fz m 0 z) x v) = fun z => iteratedFDeriv ℂ k U (z, x) (fun i => ((0 : ℂ), v i))`. Use function extensionality and compare the values at `fun z => iFD_slice U (DomZ n) hD hU z x hx k v`. Rewrite using `[e]`.

Establish `hd : DifferentiableAt ℂ (iteratedFDeriv ℂ k U) (0, x)` using `(hU.contDiffAt (hO.mem_nhds ⟨Set.mem_univ _, hx⟩)).differentiableAt_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top k)`. Establish `hl : DifferentiableAt ℂ (fun z : ℂ => (z, x)) 0` using `differentiableAt_id.prodMk (differentiableAt_const x)`. Conclude with `(ContinuousMultilinearMap.apply ℂ (fun _ : Fin k => ℂ × M2 n) ℂ (fun i => ((0 : ℂ), v i))).differentiableAt.comp (0 : ℂ) (hd.comp (0 : ℂ) hl)`. Rewrite using `[expand (Fd m) (Fd_contDiffOn m)]`. Repeatedly rewrite using `[hcomm]`.

Establish `hsum : deriv (fun z => ∑ σ : Equiv.Perm (blkA (n` using `n) j), ∑ τ : Equiv.Perm (blkB (n := n) j), (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) * iteratedFDeriv ℂ (Fintype.card (blkA (n := n) j) + Fintype.card (blkB (n := n) j)) (fz m 0 z) x (Fin.append (fun i => LQ (blkA j) x (Matrix.single ((Fintype.equivFin (blkA (n := n) j)). …`. Rewrite using `[deriv_fun_sum (fun σ _ => DifferentiableAt.fun_sum (fun τ _ => (hdiff _ _).const_mul _))]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[deriv_fun_sum (fun τ _ => (hdiff _ _).const_mul _)]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Rewrite using `[deriv_const_mul _ (hdiff _ _)]`. Rewrite using `[← hsum]`. Establish `hfz : (fun z => ∑ σ : Equiv.Perm (blkA (n` using `n) j), ∑ τ : Equiv.Perm (blkB (n := n) j), (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) * iteratedFDeriv ℂ (Fintype.card (blkA (n := n) j) + Fintype.card (blkB (n := n) j)) (fz m 0 z) x (Fin.append (fun i => LQ (blkA j) x (Matrix.single ((Fintype.equivFin (blkA (n := n) j)). …`. Use function extensionality and compare the values at `z`. Rewrite using `[← expand (fz m 0 z) (fz_slice_contDiffOn m z), djZ n m 0 j z x hj hx]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hfz]`. Use `set A : ℂ → ℂ := fun z => (∏ i ∈ Finset.range j, ((i : ℂ) - z)) * (∏ i ∈ Finset.range (n - j), ((i : ℂ) - m - z)) with hAdef`. Establish `hA : DifferentiableAt ℂ A 0`. Simplify using `only [hAdef]`.

Conclude with `(DifferentiableAt.fun_finset_prod fun i _ => (differentiableAt_const _).sub differentiableAt_id).mul (DifferentiableAt.fun_finset_prod fun i _ => ((differentiableAt_const _).sub differentiableAt_id))`. Establish `hA0 : A 0 = 0`. Simplify using `only [hAdef]`. Rewrite using `[Finset.prod_eq_zero (i := 0) (by simp; omega) (by simp), zero_mul]`. Establish `hg : DifferentiableAt ℂ (fun z => fz m 0 z x * minorOn (blkA j) (wM x) * minorOn (blkB j) (wM x)⁻¹) 0`.

Establish `h1 : DifferentiableAt ℂ (fun z : ℂ => ((u1 x).det * (ub1 x).det) ^ (-z)) 0` using `(differentiableAt_id.neg).const_cpow (Or.inl (Complex.slitPlane_ne_zero hx.2))`. Simplify using `only [fz]`. Conclude with `(((differentiableAt_const _).mul h1).mul_const _).mul_const _`. Rewrite using `[deriv_fun_mul hA hg, hA0, zero_mul, add_zero]`. Use `congr 1`.

Simplify using `[fz, hF, f0]`.
-/
theorem djFd : DjFd := by
  intro n m j x hj1 hj hx
  set U : ℂ × M2 n → ℂ := fun p => fz m 0 p.1 p.2 with hUdef
  have hU : ContDiffOn ℂ ∞ U (Set.univ ×ˢ DomZ n) := fz_contDiffOn m
  have hD : IsOpen (DomZ n) := isOpen_domZ
  have hO : IsOpen (Set.univ ×ˢ DomZ n : Set (ℂ × M2 n)) := isOpen_univ.prod hD
  have expand : ∀ F : M2 n → ℂ, ContDiffOn ℂ ∞ F (DomZ n) →
      detD (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
        F (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1))) =
      ∑ σ : Equiv.Perm (blkA (n := n) j), ∑ τ : Equiv.Perm (blkB (n := n) j),
        (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) *
        iteratedFDeriv ℂ (Fintype.card (blkA (n := n) j) + Fintype.card (blkB (n := n) j)) F x
          (Fin.append (fun i => LQ (blkA j) x (Matrix.single ((Fintype.equivFin (blkA (n := n) j)).symm i)
              (σ ((Fintype.equivFin (blkA (n := n) j)).symm i)) 1))
            (fun i => LR (blkB j) x (Matrix.single ((Fintype.equivFin (blkB (n := n) j)).symm i)
              (τ ((Fintype.equivFin (blkB (n := n) j)).symm i)) 1))) := by
    intro F hF
    have hrw : (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
        F (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1))) =
        (fun T => detD (fun S => F (x + LQ (blkA j) x T + LR (blkB j) x S))) := by
      funext T; congr 1; funext S; rw [mul_mX, LQ_apply, LR_apply]
    rw [hrw]
    exact detD_detD_comp F (DomZ n) hD hF x hx (LQ (blkA j) x) (LR (blkB j) x)
  have hcomm : ∀ (k : ℕ) (v : Fin k → M2 n), iteratedFDeriv ℂ k (Fd m) x v =
      deriv (fun z => iteratedFDeriv ℂ k (fz m 0 z) x v) 0 := fun k v =>
    iFD_deriv_comm U (DomZ n) hD hU x hx k v
  have hdiff : ∀ (k : ℕ) (v : Fin k → M2 n), DifferentiableAt ℂ (fun z => iteratedFDeriv ℂ k (fz m 0 z) x v) 0 := by
    intro k v
    have e : (fun z => iteratedFDeriv ℂ k (fz m 0 z) x v) =
        fun z => iteratedFDeriv ℂ k U (z, x) (fun i => ((0 : ℂ), v i)) :=
      funext fun z => iFD_slice U (DomZ n) hD hU z x hx k v
    rw [e]
    have hd : DifferentiableAt ℂ (iteratedFDeriv ℂ k U) (0, x) :=
      (hU.contDiffAt (hO.mem_nhds ⟨Set.mem_univ _, hx⟩)).differentiableAt_iteratedFDeriv
        (by exact_mod_cast ENat.natCast_lt_top k)
    have hl : DifferentiableAt ℂ (fun z : ℂ => (z, x)) 0 := differentiableAt_id.prodMk (differentiableAt_const x)
    exact (ContinuousMultilinearMap.apply ℂ (fun _ : Fin k => ℂ × M2 n) ℂ (fun i => ((0 : ℂ), v i))).differentiableAt.comp
      (0 : ℂ) (hd.comp (0 : ℂ) hl)
  rw [expand (Fd m) (Fd_contDiffOn m)]
  simp_rw [hcomm]
  have hsum : deriv (fun z => ∑ σ : Equiv.Perm (blkA (n := n) j), ∑ τ : Equiv.Perm (blkB (n := n) j),
        (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) *
        iteratedFDeriv ℂ (Fintype.card (blkA (n := n) j) + Fintype.card (blkB (n := n) j)) (fz m 0 z) x
          (Fin.append (fun i => LQ (blkA j) x (Matrix.single ((Fintype.equivFin (blkA (n := n) j)).symm i)
              (σ ((Fintype.equivFin (blkA (n := n) j)).symm i)) 1))
            (fun i => LR (blkB j) x (Matrix.single ((Fintype.equivFin (blkB (n := n) j)).symm i)
              (τ ((Fintype.equivFin (blkB (n := n) j)).symm i)) 1)))) 0 =
      ∑ σ : Equiv.Perm (blkA (n := n) j), ∑ τ : Equiv.Perm (blkB (n := n) j),
        (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) *
        deriv (fun z => iteratedFDeriv ℂ (Fintype.card (blkA (n := n) j) + Fintype.card (blkB (n := n) j)) (fz m 0 z) x
          (Fin.append (fun i => LQ (blkA j) x (Matrix.single ((Fintype.equivFin (blkA (n := n) j)).symm i)
              (σ ((Fintype.equivFin (blkA (n := n) j)).symm i)) 1))
            (fun i => LR (blkB j) x (Matrix.single ((Fintype.equivFin (blkB (n := n) j)).symm i)
              (τ ((Fintype.equivFin (blkB (n := n) j)).symm i)) 1)))) 0 := by
    rw [deriv_fun_sum (fun σ _ => DifferentiableAt.fun_sum (fun τ _ => (hdiff _ _).const_mul _))]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [deriv_fun_sum (fun τ _ => (hdiff _ _).const_mul _)]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [deriv_const_mul _ (hdiff _ _)]
  rw [← hsum]
  have hfz : (fun z => ∑ σ : Equiv.Perm (blkA (n := n) j), ∑ τ : Equiv.Perm (blkB (n := n) j),
        (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) *
        iteratedFDeriv ℂ (Fintype.card (blkA (n := n) j) + Fintype.card (blkB (n := n) j)) (fz m 0 z) x
          (Fin.append (fun i => LQ (blkA j) x (Matrix.single ((Fintype.equivFin (blkA (n := n) j)).symm i)
              (σ ((Fintype.equivFin (blkA (n := n) j)).symm i)) 1))
            (fun i => LR (blkB j) x (Matrix.single ((Fintype.equivFin (blkB (n := n) j)).symm i)
              (τ ((Fintype.equivFin (blkB (n := n) j)).symm i)) 1)))) =
      fun z => ((∏ i ∈ Finset.range j, ((i : ℂ) - z)) * (∏ i ∈ Finset.range (n - j), ((i : ℂ) - m - z))) *
        (fz m 0 z x * minorOn (blkA j) (wM x) * minorOn (blkB j) (wM x)⁻¹) := by
    funext z
    rw [← expand (fz m 0 z) (fz_slice_contDiffOn m z), djZ n m 0 j z x hj hx]
    ring
  rw [hfz]
  set A : ℂ → ℂ := fun z => (∏ i ∈ Finset.range j, ((i : ℂ) - z)) * (∏ i ∈ Finset.range (n - j), ((i : ℂ) - m - z))
    with hAdef
  have hA : DifferentiableAt ℂ A 0 := by
    simp only [hAdef]
    exact (DifferentiableAt.fun_finset_prod fun i _ => (differentiableAt_const _).sub differentiableAt_id).mul
      (DifferentiableAt.fun_finset_prod fun i _ => ((differentiableAt_const _).sub differentiableAt_id))
  have hA0 : A 0 = 0 := by
    simp only [hAdef]
    rw [Finset.prod_eq_zero (i := 0) (by simp; omega) (by simp), zero_mul]
  have hg : DifferentiableAt ℂ (fun z => fz m 0 z x * minorOn (blkA j) (wM x) * minorOn (blkB j) (wM x)⁻¹) 0 := by
    have h1 : DifferentiableAt ℂ (fun z : ℂ => ((u1 x).det * (ub1 x).det) ^ (-z)) 0 :=
      (differentiableAt_id.neg).const_cpow (Or.inl (Complex.slitPlane_ne_zero hx.2))
    simp only [fz]
    exact (((differentiableAt_const _).mul h1).mul_const _).mul_const _
  rw [deriv_fun_mul hA hg, hA0, zero_mul, add_zero]
  congr 1
  simp [fz, hF, f0]
