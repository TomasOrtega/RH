import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitLinearModelNorm
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnramifiedCharacter
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckePrimeDetection
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RealPoints
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.DifferentiableConjConj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PPSemichar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergTranslateVacuumReadRationalPoints
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsNsmulIntegral
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.AHPhase

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom}

def ahG {W : UnfAt U k x} (Y : UnitAt W) (w : Fin W.g → ℂ) : ℂ :=
  Complex.exp (-(Real.pi / 2 * hermForm Y.Hm w w)) * Y.θ w

/- English proof (translation)
Unfold `ahG`. Rewrite using `[theta_add W Y a w]`. Establish `hs` using `hermForm_swap Y.herm w (W.Pm a)`. Establish `hsc : hermForm Y.Hm w (W.Pm a) - star (hermForm Y.Hm w (W.Pm a)) = 2 * ((hermForm Y.Hm w (W.Pm a)).im : ℂ) * Complex.I`. Rewrite using `[show star (hermForm Y.Hm w (W.Pm a)) = (starRingEnd ℂ) (hermForm Y.Hm w (W.Pm a)) from rfl, Complex.sub_conj]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e : -(↑Real.pi / 2 * hermForm Y.Hm (w + W.Pm a) (w + W.Pm a)) + (↑Real.pi * hermForm Y.Hm w (W.Pm a) + ↑Real.pi / 2 * hermForm Y.Hm (W.Pm a) (W.Pm a)) = ↑Real.pi * Complex.I * ((hermForm Y.Hm w (W.Pm a)).im : ℂ) + -(↑Real.pi / 2 * hermForm Y.Hm w w)`. Rewrite using `[hermForm_add_left, hermForm_add_right, hermForm_add_right, hs]`. Take the linear combination `(↑Real.pi / 2 : ℂ) * hsc`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Complex.exp_add (-(↑Real.pi / 2 * hermForm Y.Hm (w + W.Pm a) (w + W.Pm a)))]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by rw [e, Complex.exp_add]; ring`.
-/
theorem ahG_add_period (W : UnfAt U k x) (Y : UnitAt W) (a : (W.F.Di (W.ik k)).La) (w : Fin W.g → ℂ) :
    ahG Y (w + W.Pm a) =
      Y.χl (W.Pm a) * Complex.exp (Real.pi * Complex.I * (hermForm Y.Hm w (W.Pm a)).im) * ahG Y w := by
  unfold ahG
  rw [theta_add W Y a w]
  have hs := hermForm_swap Y.herm w (W.Pm a)
  have hsc : hermForm Y.Hm w (W.Pm a) - star (hermForm Y.Hm w (W.Pm a)) =
      2 * ((hermForm Y.Hm w (W.Pm a)).im : ℂ) * Complex.I := by
    rw [show star (hermForm Y.Hm w (W.Pm a)) = (starRingEnd ℂ) (hermForm Y.Hm w (W.Pm a)) from rfl, Complex.sub_conj]
    push_cast; ring
  have e : -(↑Real.pi / 2 * hermForm Y.Hm (w + W.Pm a) (w + W.Pm a)) +
      (↑Real.pi * hermForm Y.Hm w (W.Pm a) + ↑Real.pi / 2 * hermForm Y.Hm (W.Pm a) (W.Pm a)) =
      ↑Real.pi * Complex.I * ((hermForm Y.Hm w (W.Pm a)).im : ℂ) + -(↑Real.pi / 2 * hermForm Y.Hm w w) := by
    rw [hermForm_add_left, hermForm_add_right, hermForm_add_right, hs]
    linear_combination (↑Real.pi / 2 : ℂ) * hsc
  calc Complex.exp (-(↑Real.pi / 2 * hermForm Y.Hm (w + W.Pm a) (w + W.Pm a))) *
        (Y.χl (W.Pm a) * Complex.exp (↑Real.pi * hermForm Y.Hm w (W.Pm a) + ↑Real.pi / 2 * hermForm Y.Hm (W.Pm a) (W.Pm a)) * Y.θ w)
      = Y.χl (W.Pm a) * Complex.exp (-(↑Real.pi / 2 * hermForm Y.Hm (w + W.Pm a) (w + W.Pm a)) +
        (↑Real.pi * hermForm Y.Hm w (W.Pm a) + ↑Real.pi / 2 * hermForm Y.Hm (W.Pm a) (W.Pm a))) * Y.θ w := by
        rw [Complex.exp_add (-(↑Real.pi / 2 * hermForm Y.Hm (w + W.Pm a) (w + W.Pm a)))]; ring
    _ = _ := by rw [e, Complex.exp_add]; ring

end GlobalTheory.AHPhase

namespace GlobalTheory.AHPhase

open GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {σ : T.Q.c.F →+* ℂ}
  {hV : T.V ((i : ℕ) + 1) σ = Wc D i}

def colB (b : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) D.host.E)
    (X : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (a : Fin (Vc D i).rank) : Fin D.R.r → D.host.E :=
  fun m => ∑ n, X (Fin.cast (rank_Wc i).symm m) n * b n a

def PinAt (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ)
    (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (ph : ℂ) (b : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) D.host.E)
    (γ g : GA D (Wc D i))
    (hx : (dictW T i σ hV g).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV g).1).dom)
    (Wt : UnfAt (T.U ((i : ℕ) + 1) σ) (dictW T i σ hV g).1 ⟨(dictW T i σ hV g).2, hx⟩) (Y : UnitAt Wt) : Prop :=
  ∀ (X : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (z : Fin (Vc D i).rank → Fin Wt.g → ℂ),
    (∀ a, z a = perVec Wt fun m => ∑ n, X (Fin.cast (rank_Wc i).symm m) n * b n a) →
    Complex.exp (Real.pi / 2 * ∑ a, hermForm Y.Hm (z a) (z a)) *
        thetaAt R.ψ (R.ωP i A.μ0) (R.vacP i) (γ * g) (realPt (Vc D i) (Wc D i) X) =
      ph * (T.cE ((i : ℕ) + 1) σ (dictW T i σ hV g).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) g) * ∏ a, Y.θ (z a)

/- English proof (translation)
Establish `h` using `hp X (fun a => perVec Wt (colB b X a)) fun a => rfl`. Establish `hE : Complex.exp (Real.pi / 2 * ∑ a, hermForm Y.Hm (perVec Wt (colB b X a)) (perVec Wt (colB b X a))) ≠ 0` using `Complex.exp_ne_zero _`. Apply `mul_left_cancel₀ hE` to reduce the goal to its premises. Rewrite using `[h]`. Simplify using `only [ahG, Finset.prod_mul_distrib]`.

Rewrite using `[← Complex.exp_sum]`. Establish `: Complex.exp (Real.pi / 2 * ∑ a, hermForm Y.Hm (perVec Wt (colB b X a)) (perVec Wt (colB b X a))) * Complex.exp (∑ a, -(Real.pi / 2 * hermForm Y.Hm (perVec Wt (colB b X a)) (perVec Wt (colB b X a)))) = 1`. Rewrite using `[← Complex.exp_add, Finset.sum_neg_distrib, Finset.mul_sum, add_neg_cancel, Complex.exp_zero]`. Take the linear combination `(-(ph * (T.cE ((i : ℕ) + 1) σ (dictW T i σ hV g).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) g) * ∏ a, Y.θ (perVec Wt (colB b X a)))) * this`.
-/
theorem thetaAt_eq_prod_ahG {ph : ℂ} {b : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) D.host.E} {γ g : GA D (Wc D i)}
    {hx : (dictW T i σ hV g).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV g).1).dom}
    {Wt : UnfAt (T.U ((i : ℕ) + 1) σ) (dictW T i σ hV g).1 ⟨(dictW T i σ hV g).2, hx⟩} {Y : UnitAt Wt}
    (hp : PinAt T R i σ hV ph b γ g hx Wt Y) (X : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) :
    thetaAt R.ψ (R.ωP i A.μ0) (R.vacP i) (γ * g) (realPt (Vc D i) (Wc D i) X) =
      ph * (T.cE ((i : ℕ) + 1) σ (dictW T i σ hV g).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) g) *
        ∏ a, ahG Y (perVec Wt (colB b X a)) := by
  have h := hp X (fun a => perVec Wt (colB b X a)) fun a => rfl
  have hE : Complex.exp (Real.pi / 2 * ∑ a, hermForm Y.Hm (perVec Wt (colB b X a)) (perVec Wt (colB b X a))) ≠ 0 :=
    Complex.exp_ne_zero _
  apply mul_left_cancel₀ hE
  rw [h]
  simp only [ahG, Finset.prod_mul_distrib]
  rw [← Complex.exp_sum]
  have : Complex.exp (Real.pi / 2 * ∑ a, hermForm Y.Hm (perVec Wt (colB b X a)) (perVec Wt (colB b X a))) *
      Complex.exp (∑ a, -(Real.pi / 2 * hermForm Y.Hm (perVec Wt (colB b X a)) (perVec Wt (colB b X a)))) = 1 := by
    rw [← Complex.exp_add, Finset.sum_neg_distrib, Finset.mul_sum, add_neg_cancel, Complex.exp_zero]
  linear_combination (-(ph * (T.cE ((i : ℕ) + 1) σ (dictW T i σ hV g).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) g) *
    ∏ a, Y.θ (perVec Wt (colB b X a)))) * this

end GlobalTheory.AHPhase

namespace GlobalTheory.AHPhase

open ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom}

def pv (W : UnfAt U k x) (v : Fin r → E) : Fin W.g → ℂ :=
  fun j => perFr (U.X k) x.1 v (relab c σ (W.e j).1) (W.e j).2

/- English proof (translation)
Establish `h : ∀ ρ : E →+* ℂ, Data.emb ρ (v + w) = Data.emb ρ v + Data.emb ρ w` using `fun ρ => by`. Use extensionality with `a`. Simplify using `[Data.emb]`. Unfold `perFr`. Simplify using `only [h]`.

Use `split_ifs`. Simplify using `[Matrix.mulVec_add]`. Simplify using the standard rewrite rules. Simplify using `[hermC, mul_add, Finset.sum_add_distrib]`. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
theorem perFr_add' (X : Data E r) (y : Frame X.Ψ r) (v w : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    perFr X y (v + w) τ i = perFr X y v τ i + perFr X y w τ i := by
  have h : ∀ ρ : E →+* ℂ, Data.emb ρ (v + w) = Data.emb ρ v + Data.emb ρ w := fun ρ => by
    ext a; simp [Data.emb]
  unfold perFr
  simp only [h]
  split_ifs
  · simp [Matrix.mulVec_add]
  · simp
  · simp [hermC, mul_add, Finset.sum_add_distrib]
  · simp
  · simp

def pvHom (W : UnfAt U k x) : (Fin r → E) →+ (Fin W.g → ℂ) :=
  AddMonoidHom.mk' (pv W) fun v w => funext fun j => perFr_add' _ _ _ _ _ _

/- English proof (translation)
Establish `h1 : (N : E) • v = N • v` using `by rw [Nat.cast_smul_eq_nsmul]`. Establish `h2 : pv W (N • v) = N • pv W v` using `map_nsmul (pvHom W) N v`. Rewrite using `[h1, h2, Nat.cast_smul_eq_nsmul]`.
-/
theorem pv_nsmul (W : UnfAt U k x) (N : ℕ) (v : Fin r → E) : pv W ((N : E) • v) = (N : ℂ) • pv W v := by
  have h1 : (N : E) • v = N • v := by rw [Nat.cast_smul_eq_nsmul]
  have h2 : pv W (N • v) = N • pv W v := map_nsmul (pvHom W) N v
  rw [h1, h2, Nat.cast_smul_eq_nsmul]

/- English proof (translation)
The claim follows from `funext fun j => (W.pm_eq a j).symm`.
-/
theorem pv_lat (W : UnfAt U k x) (a : (W.F.Di (W.ik k)).La) : pv W (W.φ k a : Fin r → E) = W.Pm a :=
  funext fun j => (W.pm_eq a j).symm

/- English proof (translation)
Establish `hc : cc (M : E) = M` using `map_natCast _ M`. Simplify using `only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Establish `e2 : cc ((M : E) * v b) = (M : E) * cc (v b)`. Simplify using `only [cc, map_mul, map_natCast]`.

Rewrite using `[e2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_nsmul (G : Matrix (Fin r) (Fin r) E) (N M : ℕ) (u v : Fin r → E) :
    herm G ((N : E) • u) ((M : E) • v) = (N : E) * M * herm G u v := by
  have hc : cc (M : E) = M := map_natCast _ M
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have e2 : cc ((M : E) * v b) = (M : E) * cc (v b) := by
    simp only [cc, map_mul, map_natCast]
  rw [e2]; ring

/- English proof (translation)
Rewrite using `[hermForm_smul_left, show ((M : ℂ) • w) = (((M : ℝ) : ℂ) • w) by norm_cast, hermForm_real_smul_right]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hermForm_nsmul {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (N M : ℕ) (z w : Fin g → ℂ) :
    hermForm Hm ((N : ℂ) • z) ((M : ℂ) • w) = (N : ℂ) * M * hermForm Hm z w := by
  rw [hermForm_smul_left, show ((M : ℂ) • w) = (((M : ℝ) : ℂ) • w) by norm_cast, hermForm_real_smul_right]
  push_cast; ring

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Uc15.exists_nsmul_mem X u`.
-/
theorem exists_nsmul_mem (X : Data E r) (u : Fin r → E) : ∃ N : ℕ, N ≠ 0 ∧ N • u ∈ X.Λ :=
  _root_.UpperTheory.Reformulated.B.Uc15.exists_nsmul_mem X u

end GlobalTheory.AHPhase

namespace GlobalTheory.AHPhase

open ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom}

/- English proof (translation)
Take `⟨N, hN, hu⟩` from `exists_nsmul_mem (U.X k) u`. Take `⟨M, hM, hv⟩` from `exists_nsmul_mem (U.X k) v`. Use `set a := (W.φ k).symm ⟨N • u, hu⟩ with ha`. Use `set b := (W.φ k).symm ⟨M • v, hv⟩ with hb`. Establish `hau : (W.φ k a : Fin r → E) = (N : E) • u`.

Rewrite using `[ha, LinearEquiv.apply_symm_apply, Nat.cast_smul_eq_nsmul]`. Establish `hbv : (W.φ k b : Fin r → E) = (M : E) • v`. Rewrite using `[hb, LinearEquiv.apply_symm_apply, Nat.cast_smul_eq_nsmul]`. Establish `h1` using `Y.c1 a b`. Establish `h2` using `W.isom k a b`.

Rewrite `h1` using `[← pv_lat, ← pv_lat, hau, hbv, pv_nsmul, pv_nsmul, hermForm_nsmul]`. Rewrite `h2` using `[hau, hbv, herm_nsmul]`. Establish `hNM : ((N : ℝ) * M) ≠ 0` using `mul_ne_zero (Nat.cast_ne_zero.2 hN) (Nat.cast_ne_zero.2 hM)`. Establish `h3 : ((N : ℂ) * M * hermForm Y.Hm (pv W u) (pv W v)).im = (N : ℝ) * M * (hermForm Y.Hm (pv W u) (pv W v)).im`. Rewrite using `[show ((N : ℂ) * M) = (((N : ℝ) * M : ℝ) : ℂ) by push_cast; ring, Complex.im_ofReal_mul]`.

Establish `h4 : Algebra.trace ℚ E (-(U.X k).ξ0 * ((N : E) * M * herm (U.X k).Gm u v)) = ((N : ℚ) * M) * Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm u v)`. Establish `e : -(U.X k).ξ0 * ((N : E) * M * herm (U.X k).Gm u v) = (((N : ℚ) * M) : ℚ) • (-(U.X k).ξ0 * herm (U.X k).Gm u v)`. Rewrite using `[Algebra.smul_def]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, map_smul, smul_eq_mul]`. Rewrite `h2` using `[h4]`. Establish `h5 : ((N : ℝ) * M) * (hermForm Y.Hm (pv W u) (pv W v)).im = ((N : ℝ) * M) * ((Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm u v) : ℚ) : ℝ)`. Rewrite using `[← h3, h1]`. Use `congrArg (fun q : ℚ => (q : ℝ)) h2` as an intermediate fact.

Simplify using `only [Rat.cast_intCast, Rat.cast_mul, Rat.cast_natCast] at this`. Conclude with `this`. Conclude with `mul_left_cancel₀ hNM h5`.
-/
theorem im_hermForm_pv (W : UnfAt U k x) (Y : UnitAt W) (u v : Fin r → E) :
    (hermForm Y.Hm (pv W u) (pv W v)).im =
      ((Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm u v) : ℚ) : ℝ) := by
  obtain ⟨N, hN, hu⟩ := exists_nsmul_mem (U.X k) u
  obtain ⟨M, hM, hv⟩ := exists_nsmul_mem (U.X k) v
  set a := (W.φ k).symm ⟨N • u, hu⟩ with ha
  set b := (W.φ k).symm ⟨M • v, hv⟩ with hb
  have hau : (W.φ k a : Fin r → E) = (N : E) • u := by
    rw [ha, LinearEquiv.apply_symm_apply, Nat.cast_smul_eq_nsmul]
  have hbv : (W.φ k b : Fin r → E) = (M : E) • v := by
    rw [hb, LinearEquiv.apply_symm_apply, Nat.cast_smul_eq_nsmul]
  have h1 := Y.c1 a b
  have h2 := W.isom k a b
  rw [← pv_lat, ← pv_lat, hau, hbv, pv_nsmul, pv_nsmul, hermForm_nsmul] at h1
  rw [hau, hbv, herm_nsmul] at h2
  have hNM : ((N : ℝ) * M) ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.2 hN) (Nat.cast_ne_zero.2 hM)
  have h3 : ((N : ℂ) * M * hermForm Y.Hm (pv W u) (pv W v)).im = (N : ℝ) * M * (hermForm Y.Hm (pv W u) (pv W v)).im := by
    rw [show ((N : ℂ) * M) = (((N : ℝ) * M : ℝ) : ℂ) by push_cast; ring, Complex.im_ofReal_mul]
  have h4 : Algebra.trace ℚ E (-(U.X k).ξ0 * ((N : E) * M * herm (U.X k).Gm u v)) =
      ((N : ℚ) * M) * Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm u v) := by
    have e : -(U.X k).ξ0 * ((N : E) * M * herm (U.X k).Gm u v) =
        (((N : ℚ) * M) : ℚ) • (-(U.X k).ξ0 * herm (U.X k).Gm u v) := by
      rw [Algebra.smul_def]; push_cast; ring
    rw [e, map_smul, smul_eq_mul]
  rw [h4] at h2
  have h5 : ((N : ℝ) * M) * (hermForm Y.Hm (pv W u) (pv W v)).im =
      ((N : ℝ) * M) * ((Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm u v) : ℚ) : ℝ) := by
    rw [← h3, h1]
    have := congrArg (fun q : ℚ => (q : ℝ)) h2
    simp only [Rat.cast_intCast, Rat.cast_mul, Rat.cast_natCast] at this
    exact this
  exact mul_left_cancel₀ hNM h5

end GlobalTheory.AHPhase

namespace GlobalTheory.AHPhase

open GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues GlobalTheory.FinTranslate

variable {D : D7}

/- English proof (translation)
Simplify using `only [Pi.smul_apply, smul_eq_mul]; rw [hf.quasi]; ring level := by`. Take `⟨U, hUo, hU⟩` from `hf.level`. Use `⟨U, hUo, fun u hu hi => ?_⟩` and prove the remaining obligations. Establish `e : heisO ψ S T u (c • f) = c • heisO ψ S T u f`. Use function extensionality and compare the values at `w`.

Simplify using `only [heisO, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, hU u hu hi]`. Use `cont := continuous_const.mul hf.cont`. Use `smooth k L hL hfin w := (contDiff_const.mul (hf.smooth k L hL hfin w))`.
-/
theorem theta_smul {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (c : ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T (c • f) where
  quasi γ w := by simp only [Pi.smul_apply, smul_eq_mul]; rw [hf.quasi]; ring
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    refine ⟨U, hUo, fun u hu hi => ?_⟩
    have e : heisO ψ S T u (c • f) = c • heisO ψ S T u f := by
      funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
    rw [e, hU u hu hi]
  cont := continuous_const.mul hf.cont
  smooth k L hL hfin w := (contDiff_const.mul (hf.smooth k L hL hfin w))

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [realPt, Matrix.of_apply, Matrix.add_apply, TensorProduct.tmul_add]`.
-/
theorem realPt_add (S T : HSp D) (X Y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    realPt S T (X + Y) = realPt S T X + realPt S T Y := by
  ext i j
  simp only [realPt, Matrix.of_apply, Matrix.add_apply, TensorProduct.tmul_add]

/- English proof (translation)
Use `set y := ratW T S Y - realPt S T Y with hy`. Establish `hy0 : y.map (infPart D) = 0` using `GlobalTheory.HeisRatRead.ratW_sub_realPt_inf S T Y`. Establish `hX0 : (realPt S T X).map (finPart D) = 0` using `GlobalTheory.FrameConst.realPt_fin S T X`. Establish `hY0 : (realPt S T Y).map (finPart D) = 0` using `GlobalTheory.FrameConst.realPt_fin S T Y`. Establish `hpt : realPt S T (X + Y) = ratW T S Y + (realPt S T X - y)`.

Rewrite using `[realPt_add, hy]`. Normalize the expressions using the abelian group laws. Establish `hrat : ratW T S Y = realPt S T Y + y` using `by rw [hy]; abel`. Rewrite using `[hpt, hf.quasi]`. Simplify using `only [heisO]`.

Rewrite using `[sub_eq_add_neg (realPt S T X) y, ← mul_assoc, ← AddChar.map_add_eq_mul]`. Use `congr 2`. Rewrite using `[hrat, symplOH_add_left, symplOH_add_right, symplOH_add_right, symplOH_neg_right, symplOH_neg_right, symplOH_neg_right, symplOH_self, symplOH_real_fin hy0 hY0, symplOH_fin_real hy0 hX0, symplOH_real_fin hy0 hX0, symplOH_skew (S := S) (T := T) (realPt S T X) (realPt S T Y)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem theta_realPt_add {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (X Y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    f (realPt S T (X + Y)) = ψ (symplOH S T (realPt S T X) (realPt S T Y)) *
      heisO ψ S T (-(ratW T S Y - realPt S T Y)) f (realPt S T X) := by
  set y := ratW T S Y - realPt S T Y with hy
  have hy0 : y.map (infPart D) = 0 := GlobalTheory.HeisRatRead.ratW_sub_realPt_inf S T Y
  have hX0 : (realPt S T X).map (finPart D) = 0 := GlobalTheory.FrameConst.realPt_fin S T X
  have hY0 : (realPt S T Y).map (finPart D) = 0 := GlobalTheory.FrameConst.realPt_fin S T Y
  have hpt : realPt S T (X + Y) = ratW T S Y + (realPt S T X - y) := by
    rw [realPt_add, hy]; abel
  have hrat : ratW T S Y = realPt S T Y + y := by rw [hy]; abel
  rw [hpt, hf.quasi]
  simp only [heisO]
  rw [sub_eq_add_neg (realPt S T X) y, ← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  rw [hrat, symplOH_add_left, symplOH_add_right, symplOH_add_right, symplOH_neg_right, symplOH_neg_right,
    symplOH_neg_right, symplOH_self, symplOH_real_fin hy0 hY0, symplOH_fin_real hy0 hX0, symplOH_real_fin hy0 hX0,
    symplOH_skew (S := S) (T := T) (realPt S T X) (realPt S T Y)]
  ring

end GlobalTheory.AHPhase
