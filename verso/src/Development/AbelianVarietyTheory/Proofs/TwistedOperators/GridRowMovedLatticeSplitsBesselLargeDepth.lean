import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TiltSc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilDatumAnisotropicKernelPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittDecompositionCoreProjMulCoreEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped nonZeroDivisors

namespace GlobalTheory.RowShape

variable {D : D7}

section Generic

open GlobalTheory.SeeSaw.SplitLat

variable {S S₀ : HSp D} {ρ : ℕ}

/- English proof (translation)
Introduce `y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Use `⟨fun i => ?_, fun i => ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `colMul (rat d.e) i ((rat d.qX *ᵥ y) i) ∈ _`.

Rewrite using `[colMul_rat]`. Conclude with `rat_mulVec_mem_latV _ (hX i) _ hy`. Express the relevant statement in the definitionally equal form `colMul (rat d.e') i ((rat d.qY *ᵥ y) i) ∈ _`. Rewrite using `[colMul_rat]`. Conclude with `rat_mulVec_mem_latV _ (hY i) _ hy`.

Conclude with `rat_mulVec_mem_latV d.q0 h0 _ hy`. Introduce and unpack `⟨h1, h3, h2⟩`. Establish `e : y = d.jX *ᵥ (d.pX *ᵥ y) + d.j0 *ᵥ (d.p0 *ᵥ y) + d.jY *ᵥ (d.pY *ᵥ y)`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← Matrix.add_mulVec, d.sum_eq_one, Matrix.one_mulVec]`. Rewrite using `[e, mulVec_eq_sum_colMul d.jX, mulVec_eq_sum_colMul d.jY]`.

Use `add_mem (add_mem (sum_mem fun i _ => h1 i) ?_) (sum_mem fun i _ => h3 i)` and prove the remaining obligations. Conclude with `rat_mulVec_mem_latV d.i₀ hi _ h2`.
-/
theorem monoAt_of_proj (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀)
    (hX : ∀ i : Fin ρ, ∀ x ∈ L, colProj d.qX d.e i *ᵥ x ∈ L)
    (hY : ∀ i : Fin ρ, ∀ x ∈ L, colProj d.qY d.e' i *ᵥ x ∈ L)
    (h0 : ∀ x ∈ L, d.q0 *ᵥ x ∈ L₀) (hi : ∀ x ∈ L₀, d.i₀ *ᵥ x ∈ L) (v : Pl D) : MonoAt d L L₀ v := by
  intro y
  constructor
  · intro hy
    refine ⟨fun i => ?_, fun i => ?_, ?_⟩
    · change colMul (rat d.e) i ((rat d.qX *ᵥ y) i) ∈ _
      rw [colMul_rat]
      exact rat_mulVec_mem_latV _ (hX i) _ hy
    · change colMul (rat d.e') i ((rat d.qY *ᵥ y) i) ∈ _
      rw [colMul_rat]
      exact rat_mulVec_mem_latV _ (hY i) _ hy
    · exact rat_mulVec_mem_latV d.q0 h0 _ hy
  · rintro ⟨h1, h3, h2⟩
    have e : y = d.jX *ᵥ (d.pX *ᵥ y) + d.j0 *ᵥ (d.p0 *ᵥ y) + d.jY *ᵥ (d.pY *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← Matrix.add_mulVec,
        d.sum_eq_one, Matrix.one_mulVec]
    rw [e, mulVec_eq_sum_colMul d.jX, mulVec_eq_sum_colMul d.jY]
    refine add_mem (add_mem (sum_mem fun i _ => h1 i) ?_) (sum_mem fun i _ => h3 i)
    exact rat_mulVec_mem_latV d.i₀ hi _ h2

end Generic

section SlopeTestRemainingChoices

open GlobalTheory.SeeSaw.SplitLat

/- English proof (translation)
Substitute `h` using the available equality. Establish `e : σ + (σ + 1) = 2 * σ + 1` using `by omega`. Rewrite using `[← Fin.sum_congr' f e, Fin.sum_univ_add (fun i : Fin (σ + (σ + 1)) => f (Fin.cast e i)), Fin.sum_univ_succ (fun k : Fin (σ + 1) => f (Fin.cast e (Fin.natAdd σ k)))]`. Establish `hr` using `Equiv.sum_comp (Fin.revPerm (n := σ)) (fun i : Fin σ => f (Fin.cast e (Fin.natAdd σ i.succ)))`. Rewrite using `[← hr, ← add_assoc]`.

Use `congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_` and prove the remaining obligations. Conclude with `Finset.sum_congr rfl fun i _ => congrArg f (Fin.ext rfl)`. Conclude with `congrArg f (Fin.ext rfl)`. Use `Finset.sum_congr rfl fun i _ => congrArg f (Fin.ext ?_)` and prove the remaining obligations. Simplify using `only [Fin.revPerm_apply, Fin.val_cast, Fin.val_natAdd, Fin.val_succ, Fin.val_rev, Fin.val_castLE]`.

Use `i.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem sum_three {M : Type*} [AddCommMonoid M] {c σ : ℕ} (h : c = 2 * σ + 1) (f : Fin c → M) :
    ∑ p, f p = ∑ i : Fin σ, f (Fin.castLE (by omega) i) + f ⟨σ, by omega⟩ +
      ∑ i : Fin σ, f (Fin.castLE (by omega) i).rev := by
  subst h
  have e : σ + (σ + 1) = 2 * σ + 1 := by omega
  rw [← Fin.sum_congr' f e, Fin.sum_univ_add (fun i : Fin (σ + (σ + 1)) => f (Fin.cast e i)),
    Fin.sum_univ_succ (fun k : Fin (σ + 1) => f (Fin.cast e (Fin.natAdd σ k)))]
  have hr := Equiv.sum_comp (Fin.revPerm (n := σ)) (fun i : Fin σ => f (Fin.cast e (Fin.natAdd σ i.succ)))
  rw [← hr, ← add_assoc]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
  · exact Finset.sum_congr rfl fun i _ => congrArg f (Fin.ext rfl)
  · exact congrArg f (Fin.ext rfl)
  · refine Finset.sum_congr rfl fun i _ => congrArg f (Fin.ext ?_)
    simp only [Fin.revPerm_apply, Fin.val_cast, Fin.val_natAdd, Fin.val_succ, Fin.val_rev, Fin.val_castLE]
    have := i.2
    omega

end SlopeTestRemainingChoices

section Dec

open GlobalTheory.SeeSaw.SplitLat

variable {A B : HSp D} {c σ : ℕ} (dd : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) (l : Fin σ → D.host.E) (hl : ∀ a, l a ≠ 0)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem diag_e : (diagDec (besDec dd h) l hl).e =
    dd.a.submatrix id (fun i : Fin σ => Fin.castLE (by omega : σ ≤ c) i) * diagonal l := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem diag_e' : (diagDec (besDec dd h) l hl).e' =
    dd.a.submatrix id (fun i : Fin σ => (Fin.castLE (by omega : σ ≤ c) i).rev) * diagonal (fun a => (star (l a))⁻¹) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem diag_i₀ : (diagDec (besDec dd h) l hl).i₀ = coreMat dd h := rfl

/- English proof (translation)
Use extensionality with `k i`. Simplify using `only [coreMat, GlobalTheory.OrthSumExists.orthDecHsum, Matrix.mul_apply, Matrix.submatrix_apply, id]`. Rewrite using `[← Equiv.sum_comp finSumFinEquiv]`. Simplify using `[Fintype.sum_sum_type, Matrix.one_apply]`. Use `show Matrix.fromCols (frameMat B A dd.ι) (midCol dd h) k (finSumFinEquiv.symm (Fin.castAdd 1 i)) = _`.

Rewrite using `[finSumFinEquiv_symm_apply_castAdd]`. Both sides reduce to the same expression.
-/
theorem coreMat_iA : coreMat dd h * (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)).iA = frameMat B A dd.ι := by
  ext k i
  simp only [coreMat, GlobalTheory.OrthSumExists.orthDecHsum, Matrix.mul_apply, Matrix.submatrix_apply, id]
  rw [← Equiv.sum_comp finSumFinEquiv]
  simp [Fintype.sum_sum_type, Matrix.one_apply]
  show Matrix.fromCols (frameMat B A dd.ι) (midCol dd h) k (finSumFinEquiv.symm (Fin.castAdd 1 i)) = _
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

/- English proof (translation)
Use extensionality with `k i`. Simplify using `only [coreMat, GlobalTheory.OrthSumExists.orthDecHsum, Matrix.mul_apply, Matrix.submatrix_apply, id]`. Rewrite using `[← Equiv.sum_comp finSumFinEquiv]`. Simplify using `[Fintype.sum_sum_type, Matrix.one_apply]`. Use `show Matrix.fromCols (frameMat B A dd.ι) (midCol dd h) k (finSumFinEquiv.symm (Fin.natAdd A.rank (show Fin 1 from i))) = _`.

Rewrite using `[finSumFinEquiv_symm_apply_natAdd]`. Both sides reduce to the same expression.
-/
theorem coreMat_iB : coreMat dd h * (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)).iB = midCol dd h := by
  ext k i
  simp only [coreMat, GlobalTheory.OrthSumExists.orthDecHsum, Matrix.mul_apply, Matrix.submatrix_apply, id]
  rw [← Equiv.sum_comp finSumFinEquiv]
  simp [Fintype.sum_sum_type, Matrix.one_apply]
  show Matrix.fromCols (frameMat B A dd.ι) (midCol dd h) k (finSumFinEquiv.symm (Fin.natAdd A.rank (show Fin 1 from i))) = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

/- English proof (translation)
Rewrite using `[diag_e, diag_e']`. Use function extensionality and compare the values at `k`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.add_apply]`. Rewrite using `[sum_three h]`. Use `congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_` and prove the remaining obligations.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Matrix.mul_diagonal, Matrix.submatrix_apply, id]`. Rewrite using `[mul_assoc, mul_inv_cancel_left₀ (hl i)]`. Use `show _ = ∑ x : Fin 1, midCol dd h k x * u _`. Rewrite using `[Fin.sum_univ_one]`.

Both sides reduce to the same expression. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Matrix.mul_diagonal, Matrix.submatrix_apply, id]`. Rewrite using `[mul_assoc, inv_mul_cancel_left₀ (star_ne_zero.2 (hl i))]`.
-/
theorem row_shape_decomposition (u : Fin c → D.host.E) :
    dd.a *ᵥ u = (diagDec (besDec dd h) l hl).e *ᵥ (fun i => (l i)⁻¹ * u (Fin.castLE (by omega) i)) +
      (midCol dd h : Matrix (Fin B.rank) (Fin (GlobalTheory.SeeSaw.Model.nLine D).rank) D.host.E) *ᵥ (fun _ => u ⟨σ, by omega⟩) +
      (diagDec (besDec dd h) l hl).e' *ᵥ (fun i => star (l i) * u (Fin.castLE (by omega : σ ≤ c) i).rev) := by
  rw [diag_e, diag_e']
  funext k
  simp only [Matrix.mulVec, dotProduct, Pi.add_apply]
  rw [sum_three h]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.mul_diagonal, Matrix.submatrix_apply, id]
    rw [mul_assoc, mul_inv_cancel_left₀ (hl i)]
  · show _ = ∑ x : Fin 1, midCol dd h k x * u _
    rw [Fin.sum_univ_one]
    rfl
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.mul_diagonal, Matrix.submatrix_apply, id]
    rw [mul_assoc, inv_mul_cancel_left₀ (star_ne_zero.2 (hl i))]

end Dec

section Lat

open GlobalTheory.SeeSaw.SplitLat

/- English proof (translation)
Substitute `hx` using the available equality. Simplify using `only [Matrix.mulVec_add, Matrix.mulVec_mulVec, SplitLat.qX_e, SplitLat.qX_i₀, SplitLat.qX_e', SplitLat.wittDecomposition_coreProj_mul_e_eq_zero, SplitLat.wittDecomposition_coreProj_mul_core_eq_one, SplitLat.wittZeroProjection_mul_dualBasis_eq_zero, SplitLat.qY_e, SplitLat.qY_i₀, …`.
-/
theorem coords_of_eq {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {x : Fin S.rank → D.host.E} {w w' : Fin ρ → D.host.E}
    {z : Fin S₀.rank → D.host.E} (hx : x = d.e *ᵥ w + d.i₀ *ᵥ z + d.e' *ᵥ w') :
    d.qX *ᵥ x = w ∧ d.q0 *ᵥ x = z ∧ d.qY *ᵥ x = w' := by
  subst hx
  simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, SplitLat.qX_e, SplitLat.qX_i₀, SplitLat.qX_e', SplitLat.wittDecomposition_coreProj_mul_e_eq_zero,
    SplitLat.wittDecomposition_coreProj_mul_core_eq_one, SplitLat.wittZeroProjection_mul_dualBasis_eq_zero, SplitLat.qY_e, SplitLat.qY_i₀, SplitLat.qY_e', Matrix.one_mulVec, Matrix.zero_mulVec,
    add_zero, zero_add, and_self]

variable {A B : HSp D} {c σ : ℕ} (dd : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) (l : Fin σ → D.host.E) (hl : ∀ a, l a ≠ 0)

/- English proof (translation)
Rewrite using `[diag_e]`. Use function extensionality and compare the values at `k`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.mul_diagonal, Matrix.submatrix_apply, id]`. Rewrite using `[mul_assoc, mul_inv_cancel_left₀ (hl i)]`.
-/
theorem e_single (i : Fin σ) (t : D.host.E) :
    (diagDec (besDec dd h) l hl).e *ᵥ Pi.single i ((l i)⁻¹ * t) =
      dd.a *ᵥ Pi.single (Fin.castLE (by omega : σ ≤ c) i) t := by
  rw [diag_e]
  funext k
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Matrix.mul_diagonal, Matrix.submatrix_apply, id]
  rw [mul_assoc, mul_inv_cancel_left₀ (hl i)]

/- English proof (translation)
Rewrite using `[diag_e']`. Use function extensionality and compare the values at `k`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.mul_diagonal, Matrix.submatrix_apply, id]`. Rewrite using `[mul_assoc, inv_mul_cancel_left₀ (star_ne_zero.2 (hl i))]`.
-/
theorem e'_single (i : Fin σ) (t : D.host.E) :
    (diagDec (besDec dd h) l hl).e' *ᵥ Pi.single i (star (l i) * t) =
      dd.a *ᵥ Pi.single (Fin.castLE (by omega : σ ≤ c) i).rev t := by
  rw [diag_e']
  funext k
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Matrix.mul_diagonal, Matrix.submatrix_apply, id]
  rw [mul_assoc, inv_mul_cancel_left₀ (star_ne_zero.2 (hl i))]

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Use `show ∑ x : Fin 1, midCol dd h k x * t x = _`. Rewrite using `[Fin.sum_univ_one]`. Both sides reduce to the same expression.
-/
theorem midCol_mulVec (t : Fin (GlobalTheory.SeeSaw.Model.nLine D).rank → D.host.E) :
    (midCol dd h : Matrix (Fin B.rank) (Fin (GlobalTheory.SeeSaw.Model.nLine D).rank) D.host.E) *ᵥ t = dd.a *ᵥ Pi.single ⟨σ, by omega⟩ (t (show Fin 1 from 0)) := by
  funext k
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  show ∑ x : Fin 1, midCol dd h k x * t x = _
  rw [Fin.sum_univ_one]
  rfl

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_lat_iff (Λ : Lat A) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (x : Fin B.rank → D.host.E) :
    x ∈ dd.lat Λ 𝔟 ↔ ∃ y ∈ Λ, ∃ u : Fin c → D.host.E, (∀ p, u p ∈ 𝔟 p) ∧ x = frameMat B A dd.ι *ᵥ y + dd.a *ᵥ u :=
  Iff.rfl

/- English proof (translation)
Use `(mem_lat_iff dd Λ 𝔟 _).2 ⟨0, zero_mem _, Pi.single p t, fun q => ?_, by rw [Matrix.mulVec_zero, zero_add]⟩` and prove the remaining obligations. Distinguish the cases in `hq : q = p`. Substitute `hq` using the available equality. Rewrite using `[Pi.single_eq_same]`. Conclude with `ht`.

Rewrite using `[Pi.single_eq_of_ne hq]`. Conclude with `(𝔟 q).zero_mem`.
-/
theorem single_mem_lat (Λ : Lat A) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (p : Fin c) {t : D.host.E}
    (ht : t ∈ 𝔟 p) : dd.a *ᵥ Pi.single p t ∈ dd.lat Λ 𝔟 := by
  refine (mem_lat_iff dd Λ 𝔟 _).2 ⟨0, zero_mem _, Pi.single p t, fun q => ?_, by rw [Matrix.mulVec_zero, zero_add]⟩
  by_cases hq : q = p
  · subst hq; rw [Pi.single_eq_same]; exact ht
  · rw [Pi.single_eq_of_ne hq]; exact (𝔟 q).zero_mem

end Lat

section Split

open GlobalTheory.SeeSaw.SplitLat

variable {A B : HSp D} {c σ : ℕ} (dd : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) (l : Fin σ → D.host.E) (hl : ∀ a, l a ≠ 0)

/- English proof (translation)
Use `set o := GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D) with ho`. Use `set d := diagDec (besDec dd h) l hl with hd`. Establish `key : ∀ x ∈ dd.lat Λ 𝔟, ∃ y ∈ Λ, ∃ u : Fin c → D.host.E, (∀ p, u p ∈ 𝔟 p) ∧ d.qX *ᵥ x = (fun i => (l i)⁻¹ * u (Fin.castLE (by omega : σ ≤ c) i)) ∧ d.q0 *ᵥ x = o.iA *ᵥ y + o.iB *ᵥ (fun _ => u ⟨σ, by omega⟩) ∧ d.qY *ᵥ x = (fun i => star (l i) * u (Fin.castLE (by omega : σ ≤ c) i).r …`. Introduce `x hx`. Take `⟨y, hy, u, hu, rfl⟩` from `(mem_lat_iff dd Λ 𝔟 x).1 hx`.

Use `⟨y, hy, u, hu, coords_of_eq d ?_⟩` and prove the remaining obligations. Rewrite using `[row_shape_decomposition dd h l hl u, hd, diag_i₀, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, coreMat_iA, coreMat_iB]`. Use function extensionality and compare the values at `k`. Simplify using `only [Pi.add_apply]`. Conclude with `(show ∀ a b m e : D.host.E, a + (b + m + e) = b + (a + m) + e from fun _ _ _ _ => by ring) _ _ _ _`.

Use `monoAt_of_proj d _ _ (fun i x hx => ?_) (fun i x hx => ?_) (fun x hx => ?_) (fun x hx => ?_) v` and prove the remaining obligations. Take `⟨y, hy, u, hu, hX, -, -⟩` from `key x hx`. Rewrite using `[colProj_mulVec, hX, hd, e_single dd h l hl]`. Conclude with `single_mem_lat dd Λ 𝔟 _ (hu _)`. Take `⟨y, hy, u, hu, -, -, hY⟩` from `key x hx`.

Rewrite using `[colProj_mulVec, hY, hd, e'_single dd h l hl]`. Conclude with `single_mem_lat dd Λ 𝔟 _ (hu _)`. Take `⟨y, hy, u, hu, -, h0, -⟩` from `key x hx`. Rewrite using `[h0]`. Use `Submodule.add_mem_sup ⟨y, hy, rfl⟩ ⟨fun _ => u ⟨σ, by omega⟩, ?_, rfl⟩` and prove the remaining obligations.

Use `Submodule.mem_pi.2 fun _ _ => ?_` and prove the remaining obligations. Rewrite using `[← hI]`. Conclude with `hu _`. Take `⟨x₁, ⟨y, hy, rfl⟩, x₂, ⟨t, ht, rfl⟩, rfl⟩` from `Submodule.mem_sup.1 hx`. Establish `ht0 : t (show Fin 1 from 0) ∈ 𝔟 ⟨σ, by omega⟩`.

Rewrite using `[hI]`. Conclude with `Submodule.mem_pi.1 ht _ (Set.mem_univ _)`. Use `(mem_lat_iff dd Λ 𝔟 _).2 ⟨y, hy, Pi.single ⟨σ, by omega⟩ (t (show Fin 1 from 0)), fun q => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hq : q = ⟨σ, by omega⟩`. Substitute `hq` using the available equality.

Rewrite using `[Pi.single_eq_same]`. Conclude with `ht0`. Rewrite using `[Pi.single_eq_of_ne hq]`. Conclude with `(𝔟 q).zero_mem`. Use `show d.i₀ *ᵥ (o.iA *ᵥ y + o.iB *ᵥ t) = _`.

Rewrite using `[hd, diag_i₀, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ho, coreMat_iA, coreMat_iB]`. Conclude with `congrArg (frameMat B A dd.ι *ᵥ y + ·) (midCol_mulVec dd h t)`.
-/
theorem auxiliaryLattice_splitsAlongWitt_at_place (Λ : Lat A) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (hI : 𝔟 ⟨σ, by omega⟩ = I) (v : Pl D) :
    MonoAt (diagDec (besDec dd h) l hl) (dd.lat Λ 𝔟)
      (Λ.map ((Matrix.mulVecLin (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)).iA).restrictScalars
          (𝓞 D.host.E)) ⊔
        (latPi (GlobalTheory.SeeSaw.Model.nLine D) I).map
          ((Matrix.mulVecLin (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)).iB).restrictScalars
            (𝓞 D.host.E))) v := by
  set o := GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D) with ho
  set d := diagDec (besDec dd h) l hl with hd

  have key : ∀ x ∈ dd.lat Λ 𝔟, ∃ y ∈ Λ, ∃ u : Fin c → D.host.E, (∀ p, u p ∈ 𝔟 p) ∧
      d.qX *ᵥ x = (fun i => (l i)⁻¹ * u (Fin.castLE (by omega : σ ≤ c) i)) ∧
      d.q0 *ᵥ x = o.iA *ᵥ y + o.iB *ᵥ (fun _ => u ⟨σ, by omega⟩) ∧
      d.qY *ᵥ x = (fun i => star (l i) * u (Fin.castLE (by omega : σ ≤ c) i).rev) := by
    intro x hx
    obtain ⟨y, hy, u, hu, rfl⟩ := (mem_lat_iff dd Λ 𝔟 x).1 hx
    refine ⟨y, hy, u, hu, coords_of_eq d ?_⟩
    rw [row_shape_decomposition dd h l hl u, hd, diag_i₀, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, coreMat_iA,
      coreMat_iB]
    funext k
    simp only [Pi.add_apply]
    exact (show ∀ a b m e : D.host.E, a + (b + m + e) = b + (a + m) + e from fun _ _ _ _ => by ring) _ _ _ _
  refine monoAt_of_proj d _ _ (fun i x hx => ?_) (fun i x hx => ?_) (fun x hx => ?_) (fun x hx => ?_) v
  · obtain ⟨y, hy, u, hu, hX, -, -⟩ := key x hx
    rw [colProj_mulVec, hX, hd, e_single dd h l hl]
    exact single_mem_lat dd Λ 𝔟 _ (hu _)
  · obtain ⟨y, hy, u, hu, -, -, hY⟩ := key x hx
    rw [colProj_mulVec, hY, hd, e'_single dd h l hl]
    exact single_mem_lat dd Λ 𝔟 _ (hu _)
  · obtain ⟨y, hy, u, hu, -, h0, -⟩ := key x hx
    rw [h0]
    refine Submodule.add_mem_sup ⟨y, hy, rfl⟩ ⟨fun _ => u ⟨σ, by omega⟩, ?_, rfl⟩
    refine Submodule.mem_pi.2 fun _ _ => ?_
    rw [← hI]
    exact hu _
  · obtain ⟨x₁, ⟨y, hy, rfl⟩, x₂, ⟨t, ht, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hx
    have ht0 : t (show Fin 1 from 0) ∈ 𝔟 ⟨σ, by omega⟩ := by
      rw [hI]
      exact Submodule.mem_pi.1 ht _ (Set.mem_univ _)
    refine (mem_lat_iff dd Λ 𝔟 _).2 ⟨y, hy, Pi.single ⟨σ, by omega⟩ (t (show Fin 1 from 0)), fun q => ?_, ?_⟩
    · by_cases hq : q = ⟨σ, by omega⟩
      · subst hq; rw [Pi.single_eq_same]; exact ht0
      · rw [Pi.single_eq_of_ne hq]; exact (𝔟 q).zero_mem
    · show d.i₀ *ᵥ (o.iA *ᵥ y + o.iB *ᵥ t) = _
      rw [hd, diag_i₀, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ho, coreMat_iA, coreMat_iB]
      exact congrArg (frameMat B A dd.ι *ᵥ y + ·) (midCol_mulVec dd h t)

end Split

section Row

variable {T : Type} {L : LevCh D T} {sc : Consts}

/- English proof (translation)
Establish `hev : ¬ Odd j`. Take `⟨a, ha⟩` from `D.R.m_even`. Introduce and unpack `⟨b, hb⟩`. Use linear arithmetic over natural numbers and integers. Establish `h1 : D.R.m - 1 - j - σ = σ + 1` using `by omega`.

Establish `h2 : (D.R.m - 2 - j) / 2 = σ` using `by omega`. Rewrite using `[rowId, tiltSc, if_neg hev, FractionalIdeal.spanSingleton_one, one_mul, stairId, lineId, h2]`. Simplify using `only [h1]`.
-/
theorem rowId_mid {j σ : ℕ} (hj : j + 2 * σ + 2 = D.R.m) :
    rowId D j ⟨σ, by omega⟩ = lineId D j := by
  have hev : ¬ Odd j := by
    obtain ⟨a, ha⟩ := D.R.m_even
    rintro ⟨b, hb⟩
    omega
  have h1 : D.R.m - 1 - j - σ = σ + 1 := by omega
  have h2 : (D.R.m - 2 - j) / 2 = σ := by omega
  rw [rowId, tiltSc, if_neg hev, FractionalIdeal.spanSingleton_one, one_mul, stairId, lineId, h2]
  simp only [h1]

/- English proof (translation)
Establish `hjm : j < D.R.m` using `by omega`. Establish `hc : D.R.m - 1 - j = 2 * σ + 1` using `by omega`. Establish `e : rowN G j = (G.rowDec j hjm).lat (G.Λ (.top j)) (rowId D j)` using `by rw [rowN, dif_pos hjm]`. Rewrite using `[e]`. Conclude with `auxiliaryLattice_splitsAlongWitt_at_place (G.rowDec j hjm) hc (lam σ) (lam_ne σ) (G.Λ (.top j)) (rowId D j) (lineId D j) (rowId_mid hj) v`.
-/
theorem monoAt_rowN (G : GridData L sc) (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (v : Pl D) :
    MonoAt (besDecAt G j σ hj) (rowN G j) (coreL G j) v := by
  have hjm : j < D.R.m := by omega
  have hc : D.R.m - 1 - j = 2 * σ + 1 := by omega
  have e : rowN G j = (G.rowDec j hjm).lat (G.Λ (.top j)) (rowId D j) := by rw [rowN, dif_pos hjm]
  rw [e]
  exact auxiliaryLattice_splitsAlongWitt_at_place (G.rowDec j hjm) hc (lam σ) (lam_ne σ) (G.Λ (.top j)) (rowId D j) (lineId D j) (rowId_mid hj) v

end Row

/- English proof (translation)
Use `⟨0, fun _ _ _ => ⟨0, ?_⟩⟩` and prove the remaining obligations. Use `intros`. Conclude with `fun j σ hj v => monoAt_rowN _ j σ hj v`.
-/
theorem big_monoAt_rowN : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j σ (hj : j + 2 * σ + 2 = D.R.m) v, GlobalTheory.FinPl.MonoAt (besDecAt ch.G j σ hj) (GlobalTheory.RowShape.rowN ch.G j) (GlobalTheory.RowShape.coreL ch.G j) v := by
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intros
  exact fun j σ hj v => monoAt_rowN _ j σ hj v

end GlobalTheory.RowShape

end
