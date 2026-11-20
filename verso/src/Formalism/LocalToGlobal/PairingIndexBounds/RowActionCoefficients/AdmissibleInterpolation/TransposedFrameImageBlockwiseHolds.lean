import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.NumericalIdentityScalar
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.HighestVectorFullHolds

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.G.Model.TS

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

namespace PairingSeriesCoefficients

/- English proof (translation)
Rewrite using `[coe_eval₂Hom, eval₂_eq]`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Rewrite using `[RingHom.id_apply, smul_eq_C_mul, mul_comm, map_prod]`. Simplify using `only [map_pow]`.
-/
theorem ev_eq {σ τ K : Type} [Field K] (P : MvPolynomial σ (MvPolynomial τ K)) (d0 : σ → K) :
    eval₂Hom (RingHom.id _) (fun z => C (d0 z)) P = ∑ n ∈ P.support, (∏ i ∈ n.support, d0 i ^ n i) • coeff n P := by
  rw [coe_eval₂Hom, eval₂_eq]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [RingHom.id_apply, smul_eq_C_mul, mul_comm, map_prod]
  simp only [map_pow]

/- English proof (translation)
Establish `hR : R = ∑ n ∈ P.support, monomial n (l (coeff n P))`. Use `MvPolynomial.funext fun d0 => ?_` and prove the remaining obligations. Rewrite using `[h d0, ev_eq, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, eval_monomial, smul_eq_mul, mul_comm]`.

Both sides reduce to the same expression. Rewrite using `[hR, coeff_sum]`. Simplify using `only [coeff_monomial]`. Rewrite using `[Finset.sum_ite_eq' P.support n]`. Use `split_ifs with hn`.

Both sides reduce to the same expression. Rewrite using `[notMem_support_iff.1 hn, map_zero]`.
-/
theorem coeff_of_eval {σ τ K : Type} [Field K] [Infinite K] (P : MvPolynomial σ (MvPolynomial τ K))
    (l : MvPolynomial τ K →ₗ[K] K) (R : MvPolynomial σ K)
    (h : ∀ d0 : σ → K, eval d0 R = l (eval₂Hom (RingHom.id _) (fun z => C (d0 z)) P)) (n : σ →₀ ℕ) :
    coeff n R = l (coeff n P) := by
  classical
  have hR : R = ∑ n ∈ P.support, monomial n (l (coeff n P)) := by
    refine MvPolynomial.funext fun d0 => ?_
    rw [h d0, ev_eq, map_sum, map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_smul, eval_monomial, smul_eq_mul, mul_comm]
    rfl
  rw [hR, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq' P.support n]
  split_ifs with hn
  · rfl
  · rw [notMem_support_iff.1 hn, map_zero]

end PairingSeriesCoefficients

/- English proof (translation)
Introduce `p _ X Kc _ _ _ j P f l R h`. Establish `hc` using `PairingSeriesCoefficients.coeff_of_eval P l R h`. Unfold `pairD`. Rewrite using `[map_sum]`. Simplify using `only [map_smul, smul_eq_mul, hc]`.

Rewrite using `[Finset.sum_subset (Finset.subset_union_left (s₁ := P.support) (s₂ := R.support)), Finset.sum_subset (Finset.subset_union_right (s₁ := P.support) (s₂ := R.support))]`. Introduce `n _ hn`. Rewrite using `[← hc, notMem_support_iff.1 hn, mul_zero]`. Introduce `n _ hn`. Rewrite using `[notMem_support_iff.1 hn, map_zero, mul_zero]`.
-/
theorem pairing_series_linear_form_holds : PairingSeriesLinearForm := by
  intro p _ X Kc _ _ _ j P f l R h
  have hc := PairingSeriesCoefficients.coeff_of_eval P l R h
  unfold pairD
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, hc]
  classical
  rw [Finset.sum_subset (Finset.subset_union_left (s₁ := P.support) (s₂ := R.support)),
    Finset.sum_subset (Finset.subset_union_right (s₁ := P.support) (s₂ := R.support))]
  · intro n _ hn
    rw [← hc, notMem_support_iff.1 hn, mul_zero]
  · intro n _ hn
    rw [notMem_support_iff.1 hn, map_zero, mul_zero]

namespace PairingSeriesCoefficients

section GlobalTheory

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (j : ℕ) (Lk : X.ZA j → X.ZA j → Kc)
  (hne : ∀ x y, Lk x y ≠ 0 → (⟨y.1, y.2.1⟩ : Σ v : X.Pl, Fin (X.G.P.n' v)) = ⟨x.1, x.2.1⟩)

include hne

/- English proof (translation)
Unfold `linP`. Use `IsWeightedHomogeneous.sum _ _ _ fun y _ => ?_` and prove the remaining obligations. Use `beta_reduce`. Distinguish the cases in `h : Lk x y = 0`. Rewrite using `[h, map_zero, map_zero, zero_mul]`.

Conclude with `isWeightedHomogeneous_zero _ _ _`. Establish `h2 : wB X j v s x = wB X j v s y`. Unfold `wB`. Rewrite using `[hne x y h]`. Rewrite using `[h2]`.

Conclude with `(isWeightedHomogeneous_X _ _ y).C_mul _`.
-/
theorem isWeightedHomogeneous_linP (v : X.Pl) (s : Fin (X.G.P.n' v)) (x : X.ZA j) :
    IsWeightedHomogeneous (wB X j v s)
      (linP (fun x y => algebraMap Kc (XspC (X.Pj (j + 1)) Kc) (Lk x y)) x) (wB X j v s x) := by
  unfold linP
  refine IsWeightedHomogeneous.sum _ _ _ fun y _ => ?_
  beta_reduce
  by_cases h : Lk x y = 0
  · rw [h, map_zero, map_zero, zero_mul]
    exact isWeightedHomogeneous_zero _ _ _
  · have h2 : wB X j v s x = wB X j v s y := by
      unfold wB
      rw [hne x y h]
    rw [h2]
    exact (isWeightedHomogeneous_X _ _ y).C_mul _

/- English proof (translation)
Rewrite using `[aeval_monomial, map_one, one_mul, Finsupp.weight_apply]`. Conclude with `IsWeightedHomogeneous.prod _ _ _ fun x _ => (isWeightedHomogeneous_linP X Kc j Lk hne v s x).pow _`.
-/
theorem mono_wh (v : X.Pl) (s : Fin (X.G.P.n' v)) (m : X.ZA j →₀ ℕ) :
    IsWeightedHomogeneous (wB X j v s)
      (aeval (linP fun x y => algebraMap Kc (XspC (X.Pj (j + 1)) Kc) (Lk x y))
        (monomial m (1 : XspC (X.Pj (j + 1)) Kc))) (Finsupp.weight (wB X j v s) m) := by
  rw [aeval_monomial, map_one, one_mul, Finsupp.weight_apply]
  exact IsWeightedHomogeneous.prod _ _ _ fun x _ => (isWeightedHomogeneous_linP X Kc j Lk hne v s x).pow _

/- English proof (translation)
Establish `key : ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)), ∑ a, ∑ b, n ⟨v, (s, a, b)⟩ = ∑ a, ∑ b, m ⟨v, (s, a, b)⟩`. Introduce `v s`. Rewrite using `[← wt_eq, ← wt_eq]`. Assume the negation of the conclusion as `hne'`. Conclude with `h ((mono_wh X Kc j Lk hne v s m).coeff_eq_zero n hne')`.

Unfold `GoodDeg`. Simplify using `only [key]`.
-/
theorem hGd (m n : X.ZA j →₀ ℕ)
    (h : coeff n (aeval (linP fun x y => algebraMap Kc (XspC (X.Pj (j + 1)) Kc) (Lk x y))
        (monomial m (1 : XspC (X.Pj (j + 1)) Kc))) ≠ 0) : GoodDeg X j n ↔ GoodDeg X j m := by
  have key : ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)), ∑ a, ∑ b, n ⟨v, (s, a, b)⟩ = ∑ a, ∑ b, m ⟨v, (s, a, b)⟩ := by
    intro v s
    rw [← wt_eq, ← wt_eq]
    by_contra hne'
    exact h ((mono_wh X Kc j Lk hne v s m).coeff_eq_zero n hne')
  unfold GoodDeg
  simp only [key]

/- English proof (translation)
Conclude with `pr_sub Lk (GoodDeg X j) (hGd X Kc j Lk hne) Q f`.
-/
theorem pairD_linSub (Q : DA X Kc j) (f : MvPowerSeries (X.ZA j) Kc) :
    pairD X Kc j Q (linSub Lk f) =
      pairD X Kc j (aeval (linT fun x y => algebraMap Kc (XspC (X.Pj (j + 1)) Kc) (Lk x y)) Q) f := by
  classical
  exact pr_sub Lk (GoodDeg X j) (hGd X Kc j Lk hne) Q f

omit hne in

/- English proof (translation)
Establish `h : (evD X Kc j d0).comp (aeval (linT fun x y => algebraMap Kc (XspC (X.Pj (j + 1)) Kc) (Lk x y)) : DA X Kc j →ₐ[XspC (X.Pj (j + 1)) Kc] DA X Kc j).toRingHom = evD X Kc j (fun y => ∑ z, Lk z y * d0 z)`. Use `ringHom_ext (fun r => ?_) fun y => ?_` and prove the remaining obligations. Simplify using `[evD]`. Simplify using `only [evD, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, linT, map_sum, map_mul, coe_eval₂Hom, eval₂_C, eval₂_X, RingHom.id_apply, algebraMap_eq]`. Conclude with `RingHom.congr_fun h Q`.
-/
theorem evD_linT (d0 : X.ZA j → Kc) (Q : DA X Kc j) :
    evD X Kc j d0 (aeval (linT fun x y => algebraMap Kc (XspC (X.Pj (j + 1)) Kc) (Lk x y)) Q) =
      evD X Kc j (fun y => ∑ z, Lk z y * d0 z) Q := by
  have h : (evD X Kc j d0).comp
      (aeval (linT fun x y => algebraMap Kc (XspC (X.Pj (j + 1)) Kc) (Lk x y)) :
        DA X Kc j →ₐ[XspC (X.Pj (j + 1)) Kc] DA X Kc j).toRingHom = evD X Kc j (fun y => ∑ z, Lk z y * d0 z) := by
    refine ringHom_ext (fun r => ?_) fun y => ?_
    · simp [evD]
    · simp only [evD, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, linT, map_sum, map_mul,
        coe_eval₂Hom, eval₂_C, eval₂_X, RingHom.id_apply, algebraMap_eq]
  exact RingHom.congr_fun h Q

end GlobalTheory

end PairingSeriesCoefficients

/- English proof (translation)
Introduce `p _ X Kc _ _ _ _ j La La' φ P f l R h`. Rewrite using `[PairingSeriesCoefficients.pairD_linSub X Kc j (bc Kc φ) (fun x y hxy => by`. Assume the negation of the conclusion as `hne`. Conclude with `hxy (bc_ne Kc φ x y fun h' => hne h'.symm)) P f]`. Use `pairing_series_linear_form_holds p X Kc j _ f l R fun d0 => ?_` and prove the remaining obligations.

Rewrite using `[h d0, PairingSeriesCoefficients.evD_linT]`.
-/
theorem frame_change_pairing_holds : XB := by
  intro p _ X Kc _ _ _ _ j La La' φ P f l R h
  rw [PairingSeriesCoefficients.pairD_linSub X Kc j (bc Kc φ) (fun x y hxy => by
    by_contra hne
    exact hxy (bc_ne Kc φ x y fun h' => hne h'.symm)) P f]
  refine pairing_series_linear_form_holds p X Kc j _ f l R fun d0 => ?_
  rw [h d0, PairingSeriesCoefficients.evD_linT]

/- English proof (translation)
Introduce `p _ X Kc _ _ _ j La La' φ d0 b`. Take `⟨v, s⟩` from `b`. Use `Matrix.ext fun a b' => ?_` and prove the remaining obligations. Use `show ∑ z, bc Kc φ z ⟨v, (s, a, b')⟩ * d0 z = _`. Rewrite using `[sum_block X j (fun z => bc Kc φ z ⟨v, (s, a, b')⟩ * d0 z) v s (fun z hz => by`.

Rewrite using `[bc_ne Kc φ z _ hz, zero_mul])]`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, dM, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun b'' _ => Finset.sum_congr rfl fun a' _ => ?_` and prove the remaining obligations.

Rewrite using `[bc_same]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem transposed_frame_image_blockwise_holds : TransposedFrameImageBlockwise := by
  intro p _ X Kc _ _ _ j La La' φ d0 b
  obtain ⟨v, s⟩ := b
  refine Matrix.ext fun a b' => ?_
  show ∑ z, bc Kc φ z ⟨v, (s, a, b')⟩ * d0 z = _
  rw [sum_block X j (fun z => bc Kc φ z ⟨v, (s, a, b')⟩ * d0 z) v s (fun z hz => by
    rw [bc_ne Kc φ z _ hz, zero_mul])]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dM, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b'' _ => Finset.sum_congr rfl fun a' _ => ?_
  rw [bc_same]
  ring

namespace PairingSeriesCoefficients

section Ev

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (j : ℕ)

/- English proof (translation)
Simplify using `only [xd, mulC, map_sum, map_mul, Matrix.transpose_apply, dMat, dM, evD, coe_eval₂Hom, eval₂_X, MvPolynomial.algebraMap_apply, eval₂_C, RingHom.id_apply]`.
-/
theorem evD_xd (b : BX X) (x : Fin (NJ X j) → ℕ → X.G.Kf) (d0 : X.ZA j → Kc) (b' : Fin (NJ X (j + 1))) (i : ℕ) :
    evD X Kc j d0 (xd X Kc j b.1 b.2 x b' i) =
      C (mulC (dM X Kc j b d0).transpose (fun a i => algebraMap X.G.Kf Kc (x a i)) b' i) := by
  simp only [xd, mulC, map_sum, map_mul, Matrix.transpose_apply, dMat, dM, evD, coe_eval₂Hom, eval₂_X, MvPolynomial.algebraMap_apply,
    eval₂_C, RingHom.id_apply]

/- English proof (translation)
Use `Matrix.ext fun b' t => ?_` and prove the remaining obligations. Simplify using `only [Matrix.map_apply, yMat, yV, evD, coe_eval₂Hom, eval₂_C, RingHom.id_apply, RingHom.coe_coe, rename_X]`. Both sides reduce to the same expression.
-/
theorem evD_yMat (b : BX X) (d0 : X.ZA j → Kc) :
    (yMat X Kc j b.1 b.2).map (evD X Kc j d0) =
      (yV Kc (NJ X (j + 1))).map ((rename (emX X (j + 1) b) :
        MvPolynomial (Fin (NJ X (j + 1)) × Fin (NJ X (j + 1))) Kc →ₐ[Kc] XspC (X.Pj (j + 1)) Kc) :
        MvPolynomial (Fin (NJ X (j + 1)) × Fin (NJ X (j + 1))) Kc →+* XspC (X.Pj (j + 1)) Kc) := by
  refine Matrix.ext fun b' t => ?_
  simp only [Matrix.map_apply, yMat, yV, evD, coe_eval₂Hom, eval₂_C, RingHom.id_apply, RingHom.coe_coe, rename_X]
  rfl

end Ev

end PairingSeriesCoefficients

/- English proof (translation)
Introduce `p _ X Kc _ _ j b x d0`. Unfold `tgtD tgtN`. Use `split_ifs with ho`. Rewrite using `[map_hvO, PairingSeriesCoefficients.evD_yMat, ← RingHom.coe_coe (rename (emX X (j + 1) b)), map_hvO]`. Use `congr 1`.

Use function extensionality and compare the values at `b' i`. Rewrite using `[PairingSeriesCoefficients.evD_xd, RingHom.coe_coe, rename_C]`. Rewrite using `[map_hvE, PairingSeriesCoefficients.evD_yMat, ← RingHom.coe_coe (rename (emX X (j + 1) b)), map_hvE]`. Use `congr 1`. Use function extensionality and compare the values at `b' i`.

Rewrite using `[PairingSeriesCoefficients.evD_xd, RingHom.coe_coe, rename_C]`.
-/
theorem frame_change_compatibility_holds : XC := by
  intro p _ X Kc _ _ j b x d0
  unfold tgtD tgtN
  split_ifs with ho
  · rw [map_hvO, PairingSeriesCoefficients.evD_yMat, ← RingHom.coe_coe (rename (emX X (j + 1) b)), map_hvO]
    congr 1
    funext b' i
    rw [PairingSeriesCoefficients.evD_xd, RingHom.coe_coe, rename_C]
  · rw [map_hvE, PairingSeriesCoefficients.evD_yMat, ← RingHom.coe_coe (rename (emX X (j + 1) b)), map_hvE]
    congr 1
    funext b' i
    rw [PairingSeriesCoefficients.evD_xd, RingHom.coe_coe, rename_C]

namespace PairingSeriesCoefficients

section Deg

/- English proof (translation)
Rewrite using `[Matrix.det_apply]`. Use `IsWeightedHomogeneous.sum _ _ _ fun τ _ => ?_` and prove the remaining obligations. Establish `h1 : IsWeightedHomogeneous w (∏ i, M (τ i) i) (m * d)`. Use `IsWeightedHomogeneous.prod (w := w) Finset.univ (fun i => M (τ i) i) (fun _ => d) fun i _ => h (τ i) i` as an intermediate fact. Rewrite `this` using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]`. Then use the resulting hypothesis.

Break down `Int.units_eq_one_or (Equiv.Perm.sign τ) with h2 | h2` into its components or cases. Rewrite using `[h2, one_smul]`. Conclude with `h1`. Rewrite using `[h2, Units.neg_smul, one_smul]`. Conclude with `(mem_weightedHomogeneousSubmodule R w _ _).1 (neg_mem ((mem_weightedHomogeneousSubmodule R w _ _).2 h1))`.
-/
theorem det_wh {σ R : Type} [CommRing R] (w : σ → ℕ) {m : ℕ} (M : Matrix (Fin m) (Fin m) (MvPolynomial σ R)) (d : ℕ)
    (h : ∀ i i', IsWeightedHomogeneous w (M i i') d) : IsWeightedHomogeneous w M.det (m * d) := by
  rw [Matrix.det_apply]
  refine IsWeightedHomogeneous.sum _ _ _ fun τ _ => ?_
  have h1 : IsWeightedHomogeneous w (∏ i, M (τ i) i) (m * d) := by
    have := IsWeightedHomogeneous.prod (w := w) Finset.univ (fun i => M (τ i) i) (fun _ => d) fun i _ => h (τ i) i
    rwa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h2 | h2
  · rw [h2, one_smul]
    exact h1
  · rw [h2, Units.neg_smul, one_smul]
    exact (mem_weightedHomogeneousSubmodule R w _ _).1
      (neg_mem ((mem_weightedHomogeneousSubmodule R w _ _).2 h1))

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (j : ℕ)

/- English proof (translation)
Unfold `Sys.colFac`. Use `det_wh _ _ _ fun i i' => ?_` and prove the remaining obligations. Rewrite using `[Matrix.of_apply]`. Use `IsWeightedHomogeneous.sum _ _ _ fun a _ => ?_` and prove the remaining obligations. Conclude with `(isWeightedHomogeneous_X _ (wB X j v s) (⟨b.1, (b.2, a, I b.1 b.2 c i'.val)⟩ : X.ZA j)).C_mul _`.
-/
theorem colFac_wh (I : X.ColCh j) (v : X.Pl) (s : Fin (X.G.P.n' v)) (b : BX X) (c : ℕ) :
    IsWeightedHomogeneous (wB X j v s) (X.colFac j I b.1 b.2 c)
      (X.colHt b.1 (j + 1) b.2 c * if b = ⟨v, s⟩ then 1 else 0) := by
  unfold Sys.colFac
  refine det_wh _ _ _ fun i i' => ?_
  rw [Matrix.of_apply]
  refine IsWeightedHomogeneous.sum _ _ _ fun a _ => ?_
  exact (isWeightedHomogeneous_X _ (wB X j v s) (⟨b.1, (b.2, a, I b.1 b.2 c i'.val)⟩ : X.ZA j)).C_mul _

/- English proof (translation)
Establish `h1 : X.PI j I i0 = ∏ b : BX X, ∏ c ∈ Finset.range (X.nuv b.1 (j + 1) b.2 1).toNat, (p : MvPolynomial (X.ZA j) (MvPolynomial (X.FrI j) ℤ)) ^ (X.colExp j I i0 b.1 b.2 c) * X.colFac j I b.1 b.2 c`. Rewrite using `[Fintype.prod_sigma]`. Both sides reduce to the same expression. Establish `h2` using `IsWeightedHomogeneous.prod (w := wB X j v s) (Finset.univ : Finset (BX X)) (fun b => ∏ c ∈ Finset.range (X.nuv b.1 (j + 1) b.2 1).toNat, (p : MvPolynomial (X.ZA j) (MvPolynomial (X.FrI j) ℤ)) ^ (X.colExp j I i0 b.1 b.2 c) * X.colFac j I b.1 b.2 c) (fun b => ∑ c ∈ Finset.range (X. …`. Use `IsWeightedHomogeneous.mul ?_ (colFac_wh X j I v s b c)` and prove the remaining obligations.

Establish `h3 : (p : MvPolynomial (X.ZA j) (MvPolynomial (X.FrI j) ℤ)) ^ (X.colExp j I i0 b.1 b.2 c) = C ((p : MvPolynomial (X.FrI j) ℤ) ^ (X.colExp j I i0 b.1 b.2 c))`. Rewrite using `[map_pow, map_natCast]`. Rewrite using `[h3]`. Conclude with `isWeightedHomogeneous_C _ _)`. Rewrite using `[h1]`.

Use `h2 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[Finset.sum_eq_single (⟨v, s⟩ : BX X)]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[hb]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem PI_wh (I : X.ColCh j) (i0 : X.Pl → ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    IsWeightedHomogeneous (wB X j v s) (X.PI j I i0)
      (∑ c ∈ Finset.range (X.nuv v (j + 1) s 1).toNat, X.colHt v (j + 1) s c) := by
  classical
  have h1 : X.PI j I i0 = ∏ b : BX X, ∏ c ∈ Finset.range (X.nuv b.1 (j + 1) b.2 1).toNat,
      (p : MvPolynomial (X.ZA j) (MvPolynomial (X.FrI j) ℤ)) ^ (X.colExp j I i0 b.1 b.2 c) * X.colFac j I b.1 b.2 c := by
    rw [Fintype.prod_sigma]
    rfl
  have h2 := IsWeightedHomogeneous.prod (w := wB X j v s) (Finset.univ : Finset (BX X))
    (fun b => ∏ c ∈ Finset.range (X.nuv b.1 (j + 1) b.2 1).toNat,
      (p : MvPolynomial (X.ZA j) (MvPolynomial (X.FrI j) ℤ)) ^ (X.colExp j I i0 b.1 b.2 c) * X.colFac j I b.1 b.2 c)
    (fun b => ∑ c ∈ Finset.range (X.nuv b.1 (j + 1) b.2 1).toNat,
      (0 + X.colHt b.1 (j + 1) b.2 c * if b = ⟨v, s⟩ then 1 else 0))
    (fun b _ => IsWeightedHomogeneous.prod _ _ _ fun c _ => by
      refine IsWeightedHomogeneous.mul ?_ (colFac_wh X j I v s b c)
      have h3 : (p : MvPolynomial (X.ZA j) (MvPolynomial (X.FrI j) ℤ)) ^ (X.colExp j I i0 b.1 b.2 c) =
          C ((p : MvPolynomial (X.FrI j) ℤ) ^ (X.colExp j I i0 b.1 b.2 c)) := by
        rw [map_pow, map_natCast]
      rw [h3]
      exact isWeightedHomogeneous_C _ _)
  rw [h1]
  convert h2 using 1
  rw [Finset.sum_eq_single (⟨v, s⟩ : BX X)]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Introduce `v s`. Rewrite using `[← wt_eq, PI_wh X j I i0 v s hn, Finset.sum_range]`. Conclude with `sum_colHt X v j s`.
-/
theorem PI_good (I : X.ColCh j) (i0 : X.Pl → ℕ) (n : X.ZA j →₀ ℕ) (hn : coeff n (X.PI j I i0) ≠ 0) : GoodDeg X j n := by
  intro v s
  rw [← wt_eq, PI_wh X j I i0 v s hn, Finset.sum_range]
  exact sum_colHt X v j s

end Deg

end PairingSeriesCoefficients

/- English proof (translation)
Introduce `p _ X Kc _ _ j I i0 f x`. Rewrite using `[Finset.sum_subset (support_map_subset _ _) (fun n _ hn => by rw [notMem_support_iff.1 hn, mul_zero])]`. Unfold `applyD`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun n hn => ?_` and prove the remaining obligations.

Rewrite using `[smul_eval, eval_map, coeff_map, coe_eval₂Hom]`. Use `congr 1`. Unfold `derAt`. Rewrite using `[if_pos (PairingSeriesCoefficients.PI_good X j I i0 n (mem_support_iff.1 hn))]`.
-/
theorem frame_change_group_action_holds : XG := by
  intro p _ X Kc _ _ j I i0 f x
  classical
  rw [Finset.sum_subset (support_map_subset _ _) (fun n _ hn => by rw [notMem_support_iff.1 hn, mul_zero])]
  unfold applyD
  rw [map_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [smul_eval, eval_map, coeff_map, coe_eval₂Hom]
  congr 1
  unfold derAt
  rw [if_pos (PairingSeriesCoefficients.PI_good X j I i0 n (mem_support_iff.1 hn))]

/- English proof (translation)
Introduce `p _ X j`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨v, s⟩, a⟩ ⟨⟨v', s'⟩, a'⟩ h`. Establish `h1` using `congrArg (idxJ X j) h`. Simplify using `only [emX, idxJ_idxI] at h1`.

Consider the cases of `h1`. Both sides reduce to the same expression. Introduce and unpack `⟨⟨v, s⟩, a, t⟩ ⟨⟨v', s'⟩, a', t'⟩ h`. Simplify using `only [xmX] at h`. Consider the cases of `h`.

Both sides reduce to the same expression.
-/
theorem frame_change_injective_holds : XInj := by
  intro p _ X j
  constructor
  · rintro ⟨⟨v, s⟩, a⟩ ⟨⟨v', s'⟩, a'⟩ h
    have h1 := congrArg (idxJ X j) h
    simp only [emX, idxJ_idxI] at h1
    cases h1
    rfl
  · rintro ⟨⟨v, s⟩, a, t⟩ ⟨⟨v', s'⟩, a', t'⟩ h
    simp only [xmX] at h
    cases h
    rfl

end Formalism.L2.PairingIndexBounds.Ent
