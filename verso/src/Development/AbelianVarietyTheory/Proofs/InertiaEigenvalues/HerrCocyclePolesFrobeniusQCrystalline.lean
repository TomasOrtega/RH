import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ApplyLayers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChiGamPowNeOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicPowerSeriesDataLevIsExpansionAtZeta
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxUnramifiedActsOnLetterIdempotentImage
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenDiscConvergentRingWithExpansions
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWachModulePeriodMapToBcris
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWachLatticeMatricesGammaPhi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEvaluationConvergentSeriesBcris
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBeta
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusSubOneWittTensorLatticeSurjectiveFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NBasisLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapMulLeft
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionXQFrobenius
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCocycleSolutionConv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeOfFrob
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZgFormulaStatement

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.HWL GlobalTheory.HWL.Cmp GlobalTheory.HWL.Cmp.PerMap

namespace GlobalTheory.NL.PoleCrys

section Algebra

open PowerSeries in

/- English proof (translation)
Use `conv_lhs => rw [PowerSeries.eq_shift_mul_X_add_const a]`. Establish `: γ (C (constantCoeff a)) = C (constantCoeff a)` using `γ.commutes _`. Rewrite using `[map_add, map_mul, this, map_add, map_mul, h0]`. Simplify using the standard rewrite rules.
-/
theorem constantCoeff_algHom {L : Type} [CommRing L] (γ : L⟦X⟧ →ₐ[L] L⟦X⟧) (h0 : constantCoeff (γ X) = 0)
    (a : L⟦X⟧) : constantCoeff (γ a) = constantCoeff a := by
  conv_lhs => rw [PowerSeries.eq_shift_mul_X_add_const a]
  have : γ (C (constantCoeff a)) = C (constantCoeff a) := γ.commutes _
  rw [map_add, map_mul, this, map_add, map_mul, h0]
  simp

open PowerSeries in

/- English proof (translation)
Take `⟨z, hz⟩ : (X : L⟦X⟧) ∣ γ X` from `X_dvd_iff.mpr h0`. Establish `h1 : coeff 1 (γ X) = constantCoeff z`. Rewrite using `[hz]`. Simplify using `[coeff_succ_X_mul]`. Establish `key : ∀ k : ℕ, ∀ i, (X : L⟦X⟧) ^ (k + 1) ∣ d i`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro i`. Simplify using `using X_dvd_iff.mpr (hd0 i)`. Consider the case `succ k ih => choose e he using ih`.

Introduce `i`. Establish `h2 : ∑ j, G i j * (z ^ (k + 1) * γ (e j)) = e i`. Apply `mul_left_cancel₀ (pow_ne_zero (k + 1) (X_ne_zero (R := L)))` to reduce the goal to its premises. Rewrite using `[← he i, ← hd i, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[he j, map_mul, map_pow, hz]`. Expand and normalize the polynomial expressions, which then agree. Establish `h3` using `congrArg constantCoeff h2`. Simplify using `only [map_sum, map_mul, map_pow, hG, constantCoeff_algHom γ h0, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h3`. Establish `h4 : constantCoeff (e i) = 0`.

Establish `: constantCoeff (e i) * (constantCoeff z ^ (k + 1) - 1) = 0` using `by linear_combination h3`. Conclude with `(mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr (h1 ▸ hu (k + 1) k.succ_pos))`. Rewrite using `[he i, pow_succ _ (k + 1)]`. Conclude with `mul_dvd_mul_left _ (X_dvd_iff.mpr h4)`. Use extensionality with `k`.

Conclude with `X_pow_dvd_iff.mp (key k i) k k.lt_succ_self`.
-/
theorem eq_zero_of_fixed {L ι : Type} [Field L] [Fintype ι] [DecidableEq ι] (γ : L⟦X⟧ →ₐ[L] L⟦X⟧)
    (h0 : constantCoeff (γ X) = 0) (hu : ∀ k : ℕ, 0 < k → coeff 1 (γ X) ^ k ≠ 1) (G : ι → ι → L⟦X⟧)
    (hG : ∀ i j, constantCoeff (G i j) = if i = j then 1 else 0) (d : ι → L⟦X⟧)
    (hd0 : ∀ i, constantCoeff (d i) = 0) (hd : ∀ i, ∑ j, G i j * γ (d j) = d i) (i : ι) : d i = 0 := by
  obtain ⟨z, hz⟩ : (X : L⟦X⟧) ∣ γ X := X_dvd_iff.mpr h0
  have h1 : coeff 1 (γ X) = constantCoeff z := by
    rw [hz]; simp [coeff_succ_X_mul]
  have key : ∀ k : ℕ, ∀ i, (X : L⟦X⟧) ^ (k + 1) ∣ d i := by
    intro k
    induction k with
    | zero => intro i; simpa using X_dvd_iff.mpr (hd0 i)
    | succ k ih =>
      choose e he using ih
      intro i
      have h2 : ∑ j, G i j * (z ^ (k + 1) * γ (e j)) = e i := by
        apply mul_left_cancel₀ (pow_ne_zero (k + 1) (X_ne_zero (R := L)))
        rw [← he i, ← hd i, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [he j, map_mul, map_pow, hz]
        ring
      have h3 := congrArg constantCoeff h2
      simp only [map_sum, map_mul, map_pow, hG, constantCoeff_algHom γ h0, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true] at h3
      have h4 : constantCoeff (e i) = 0 := by
        have : constantCoeff (e i) * (constantCoeff z ^ (k + 1) - 1) = 0 := by linear_combination h3
        exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr (h1 ▸ hu (k + 1) k.succ_pos))
      rw [he i, pow_succ _ (k + 1)]
      exact mul_dvd_mul_left _ (X_dvd_iff.mpr h4)
  ext k
  exact X_pow_dvd_iff.mp (key k i) k k.lt_succ_self

/- English proof (translation)
Simplify using `only [Fintype.linearCombination_apply, map_sum, hf, Finset.smul_sum, Matrix.mulVec, dotProduct, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[smul_comm, hH, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[smul_smul, mul_comm]`.
-/
theorem semi_coord {A M ι : Type} [CommRing A] [AddCommGroup M] [Module A M] [Fintype ι] (σ : A → A) (f : M →+ M)
    (hf : ∀ a x, f (a • x) = σ a • f x) (e : ι → M) (q : A) (H : Matrix ι ι A)
    (hH : ∀ j, q • f (e j) = ∑ i, H i j • e i) (c : ι → A) :
    q • f (Fintype.linearCombination A e c) = Fintype.linearCombination A e (H.mulVec fun j => σ (c j)) := by
  simp only [Fintype.linearCombination_apply, map_sum, hf, Finset.smul_sum, Matrix.mulVec, dotProduct,
    Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_comm, hH, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, mul_comm]

/- English proof (translation)
Establish `e1 : (fun j => γ ((H.mulVec (fun j => σ (w j)) - w - z') j)) = (H.map γ).mulVec (fun j => σ (γ (w j))) - (fun j => γ (w j)) - fun j => γ (z' j)`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct, hc]`. Establish `e2 : (G.map σ).mulVec (fun j => σ (γ (w j))) = (fun j => σ (w j)) + fun j => σ (z j)`. Use function extensionality and compare the values at `i`.

Rewrite using `[← hw]`. Simplify using `[Matrix.mulVec, dotProduct]`. Rewrite using `[e1, Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hGH, ← Matrix.mulVec_mulVec, e2, Matrix.mulVec_add]`. Take the linear combination `(-1 : ι → A) * hw - hz`.
-/
theorem fixed_diff {A ι : Type} [CommRing A] [Fintype ι] (γ σ : A →+* A) (hc : ∀ a, γ (σ a) = σ (γ a))
    (G H : Matrix ι ι A) (hGH : G * H.map γ = H * G.map σ) (w z z' : ι → A)
    (hw : G.mulVec (fun j => γ (w j)) - w = z)
    (hz : G.mulVec (fun j => γ (z' j)) - z' = H.mulVec (fun j => σ (z j)) - z) :
    G.mulVec (fun j => γ ((H.mulVec (fun j => σ (w j)) - w - z') j)) = H.mulVec (fun j => σ (w j)) - w - z' := by
  have e1 : (fun j => γ ((H.mulVec (fun j => σ (w j)) - w - z') j)) =
      (H.map γ).mulVec (fun j => σ (γ (w j))) - (fun j => γ (w j)) - fun j => γ (z' j) := by
    funext i
    simp [Matrix.mulVec, dotProduct, hc]
  have e2 : (G.map σ).mulVec (fun j => σ (γ (w j))) = (fun j => σ (w j)) + fun j => σ (z j) := by
    funext i
    rw [← hw]
    simp [Matrix.mulVec, dotProduct]
  rw [e1, Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hGH, ← Matrix.mulVec_mulVec, e2,
    Matrix.mulVec_add]
  linear_combination (-1 : ι → A) * hw - hz

/- English proof (translation)
Establish `h1` using `semi_coord σ γ hγ v 1 (Matrix.of G) (fun j => by rw [one_smul, hv]; rfl) a`. Rewrite `h1` using `[one_smul, Fintype.linearCombination_apply, ← hw, hγ, Fintype.linearCombination_apply]`. Apply `((hτ.mul (hτ.map σ)).smul_left_cancel).mp` to reduce the goal to its premises. Rewrite using `[smul_sub, mul_smul, h1, mul_comm, mul_smul, hw, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[smul_smul, smul_smul, smul_smul, ← sub_smul]`. Use `congr 1`. Use `h i` as an intermediate fact. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.of_apply]`. Take the linear combination `this`.
-/
theorem div_unit {S M ι : Type} [CommRing S] [AddCommGroup M] [Module S M] [Fintype ι] (σ : S →+* S) (γ : M →+ M)
    (hγ : ∀ s m, γ (s • m) = σ s • γ m) (v : ι → M) (G : ι → ι → S) (hv : ∀ j, γ (v j) = ∑ i, G i j • v i)
    (τ : S) (hτ : IsUnit τ) (a z : ι → S) (h : ∀ i, τ * ∑ j, G i j * σ (a j) = σ τ * (a i + τ * z i))
    (w : M) (hw : τ • w = ∑ j, a j • v j) : γ w - w = ∑ i, z i • v i := by
  have h1 := semi_coord σ γ hγ v 1 (Matrix.of G) (fun j => by rw [one_smul, hv]; rfl) a
  rw [one_smul, Fintype.linearCombination_apply, ← hw, hγ, Fintype.linearCombination_apply] at h1
  apply ((hτ.mul (hτ.map σ)).smul_left_cancel).mp
  rw [smul_sub, mul_smul, h1, mul_comm, mul_smul, hw, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, smul_smul, smul_smul, ← sub_smul]
  congr 1
  have := h i
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
  linear_combination this

end Algebra

section Layers

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {s : ℕ} {Γ : WGam PD LL O v n s} {R : WSer Γ}

/- English proof (translation)
Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, (R.γ₀_X g).1, map_zero]`.
-/
theorem constantCoeff_γX (R : WSer Γ) (g : Γ.Gam) :
    PowerSeries.constantCoeff (PowerSeries.map (algebraMap O LL) (R.γ₀ g PowerSeries.X)) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, (R.γ₀_X g).1, map_zero]

/- English proof (translation)
Establish `key : ∀ g h : Γ.Gam, PowerSeries.substAlgHom (hasSubst_γ R g) ((PowerSeries.substAlgHom (hasSubst_γ R h) : PowerSeries LL →ₐ[LL] PowerSeries LL) PowerSeries.X) = PowerSeries.map (algebraMap O LL) (R.γ₀ (g * h) PowerSeries.X)`. Introduce `g h`. Rewrite using `[PowerSeries.substAlgHom_X, map_mul, AlgHom.mul_apply]`. Conclude with `(map_algHom_eq (R.γ₀ g) (hasSubst_γ R g) (constantCoeff_γX R g) rfl _).symm`. Use function extensionality and compare the values at `k`.

Use `ringHom_ext_of_X ((PowerSeries.substAlgHom (hasSubst_γ R g) : PowerSeries LL →ₐ[LL] PowerSeries LL).comp (PowerSeries.substAlgHom (hasSubst_γ R h))).toRingHom ((PowerSeries.substAlgHom (hasSubst_γ R h) : PowerSeries LL →ₐ[LL] PowerSeries LL).comp (PowerSeries.substAlgHom (hasSubs …` and prove the remaining obligations. Conclude with `(AlgHom.commutes _ c).trans (AlgHom.commutes _ c).symm`. Conclude with `(key g h).trans ((congrArg (fun x => PowerSeries.map (algebraMap O LL) (R.γ₀ x PowerSeries.X)) (mul_comm g h)).trans (key h g).symm)`. Conclude with `(congrArg PowerSeries.constantCoeff (key g h)).trans (constantCoeff_γX R _)`.
-/
theorem γL_comm (R : WSer Γ) (g h : Γ.Gam) (a : LetA LL n) : γL R g (γL R h a) = γL R h (γL R g a) := by
  have key : ∀ g h : Γ.Gam, PowerSeries.substAlgHom (hasSubst_γ R g)
      ((PowerSeries.substAlgHom (hasSubst_γ R h) : PowerSeries LL →ₐ[LL] PowerSeries LL) PowerSeries.X) =
      PowerSeries.map (algebraMap O LL) (R.γ₀ (g * h) PowerSeries.X) := by
    intro g h
    rw [PowerSeries.substAlgHom_X, map_mul, AlgHom.mul_apply]
    exact (map_algHom_eq (R.γ₀ g) (hasSubst_γ R g) (constantCoeff_γX R g) rfl _).symm
  funext k
  refine ringHom_ext_of_X
    ((PowerSeries.substAlgHom (hasSubst_γ R g) : PowerSeries LL →ₐ[LL] PowerSeries LL).comp
      (PowerSeries.substAlgHom (hasSubst_γ R h))).toRingHom
    ((PowerSeries.substAlgHom (hasSubst_γ R h) : PowerSeries LL →ₐ[LL] PowerSeries LL).comp
      (PowerSeries.substAlgHom (hasSubst_γ R g))).toRingHom (fun c => ?_) ?_ ?_ (a k)
  · exact (AlgHom.commutes _ c).trans (AlgHom.commutes _ c).symm
  · exact (key g h).trans ((congrArg (fun x => PowerSeries.map (algebraMap O LL) (R.γ₀ x PowerSeries.X))
      (mul_comm g h)).trans (key h g).symm)
  · exact (congrArg PowerSeries.constantCoeff (key g h)).trans (constantCoeff_γX R _)

/- English proof (translation)
Establish `hm : ∀ g h, ((Gm (g * h)).map (toL O LL n)) = (Gm g).map (toL O LL n) * ((Gm h).map (toL O LL n)).map (γL R g).toRingHom`. Introduce `g h`. Rewrite using `[h1, Matrix.map_mul]`. Use `congr 1`. Use `ext1 i j`.

Conclude with `toL_γ R g _`. Establish `hv : ∀ g (c : ι → LetA O n), ((Gm g).map (toL O LL n)).mulVec (fun j => γL R g (toL O LL n (c j))) = fun i => toL O LL n ((Gm g).mulVec (fun j => letγ (R.γ₀ g) (c j)) i)`. Introduce `g c`. Use function extensionality and compare the values at `i`. Simplify using `only [Matrix.mulVec, dotProduct, map_sum, map_mul, toL_γ, Matrix.map_apply]`.

Establish `hf` using `fixed_diff (γL R Γ.gam).toRingHom (γL R g).toRingHom (γL_comm R _ _) ((Gm Γ.gam).map (toL O LL n)) ((Gm g).map (toL O LL n)) (by rw [← hm, ← hm, mul_comm]) w (fun j => toL O LL n (z j)) (fun j => toL O LL n (z' j)) hw (by`. Use `(congrArg (· - _) (hv _ _)).trans (Eq.trans ?_ (congrArg (· - _) (hv _ _)).symm)` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Use `congrArg (toL O LL n) (congrFun hz i)` as an intermediate fact. Simplify `this)` using `only [Pi.sub_apply, map_sub]`.

Establish `hc : ∀ a : PowerSeries O, PowerSeries.constantCoeff (PowerSeries.map (algebraMap O LL) a) = algebraMap O LL (PowerSeries.constantCoeff a)` using `fun a => by`. Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Establish `hX : ∀ g, PowerSeries.constantCoeff ((PowerSeries.substAlgHom (hasSubst_γ R g) : PowerSeries LL →ₐ[LL] PowerSeries LL) PowerSeries.X) = 0` using `fun g => by rw [PowerSeries.substAlgHom_X]; exact constantCoeff_γX R g`. Rewrite using `[← sub_eq_zero, ← sub_sub]`. Use function extensionality and compare the values at `i k`.

Use `eq_zero_of_fixed (PowerSeries.substAlgHom (hasSubst_γ R Γ.gam)) (hX _) (fun m hm => ?_) (fun i j => toL O LL n (Gm Γ.gam i j) k) (fun i j => ?_) (fun i => ((((Gm g).map (toL O LL n)).mulVec (fun j => γL R g (w j)) - w - fun j => toL O LL n (z' j)) i) k) (fun i => ?_) (fun i => ?_ …` and prove the remaining obligations. Rewrite using `[PowerSeries.substAlgHom_X, PowerSeries.coeff_map, (R.γ₀_X _).2]`. Conclude with `hu m hm`. Use `(hc (Gm Γ.gam i j k)).trans ?_` and prove the remaining obligations. Rewrite using `[h2]`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `e1 : PowerSeries.constantCoeff (toL O LL n (z' i) k) = 0` using `(hc (z' i k)).trans (by rw [hz0, map_zero])`. Establish `e2 : ∀ j, PowerSeries.constantCoeff (γL R g (w j) k) = 0` using `fun j => (constantCoeff_algHom _ (hX g) _).trans (hw0 j k)`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.sub_apply, Finset.sum_apply, Pi.mul_apply, map_sub, map_sum, map_mul, e1, e2, hw0, mul_zero, Finset.sum_const_zero, sub_zero]`. Use `congrFun (congrFun hf i) k` as an intermediate fact.

Rewrite `this` using `[Matrix.mulVec, dotProduct, Finset.sum_apply]`. Conclude with `this`.
-/
theorem coord_eq (hu : ∀ k : ℕ, 0 < k → algebraMap O LL (Γ.χΓ Γ.gam : O) ^ k ≠ 1) {ι : Type} [Fintype ι]
    [DecidableEq ι] (Gm : Γ.Gam → Matrix ι ι (LetA O n))
    (h1 : ∀ g h, Gm (g * h) = Gm g * (Gm h).map (letγ (R.γ₀ g)))
    (h2 : ∀ g i j k, PowerSeries.constantCoeff (Gm g i j k) = if i = j then 1 else 0)
    (z z' : ι → LetA O n) (w : ι → LetA LL n) (hw0 : ∀ j i, PowerSeries.constantCoeff (w j i) = 0)
    (hw : ((Gm Γ.gam).map (toL O LL n)).mulVec (fun j => γL R Γ.gam (w j)) - w = fun j => toL O LL n (z j))
    (g : Γ.Gam) (hz0 : ∀ j i, PowerSeries.constantCoeff (z' j i) = 0)
    (hz : (Gm Γ.gam).mulVec (fun j => letγ (R.γ₀ Γ.gam) (z' j)) - z' =
      (Gm g).mulVec (fun j => letγ (R.γ₀ g) (z j)) - z) :
    ((Gm g).map (toL O LL n)).mulVec (fun j => γL R g (w j)) = w + fun j => toL O LL n (z' j) := by
  have hm : ∀ g h, ((Gm (g * h)).map (toL O LL n)) =
      (Gm g).map (toL O LL n) * ((Gm h).map (toL O LL n)).map (γL R g).toRingHom := by
    intro g h
    rw [h1, Matrix.map_mul]
    congr 1
    ext1 i j
    exact toL_γ R g _
  have hv : ∀ g (c : ι → LetA O n), ((Gm g).map (toL O LL n)).mulVec (fun j => γL R g (toL O LL n (c j))) =
      fun i => toL O LL n ((Gm g).mulVec (fun j => letγ (R.γ₀ g) (c j)) i) := by
    intro g c
    funext i
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, toL_γ, Matrix.map_apply]
  have hf := fixed_diff (γL R Γ.gam).toRingHom (γL R g).toRingHom (γL_comm R _ _) ((Gm Γ.gam).map (toL O LL n))
    ((Gm g).map (toL O LL n)) (by rw [← hm, ← hm, mul_comm]) w (fun j => toL O LL n (z j))
    (fun j => toL O LL n (z' j)) hw (by
      refine (congrArg (· - _) (hv _ _)).trans (Eq.trans ?_ (congrArg (· - _) (hv _ _)).symm)
      funext i
      have := congrArg (toL O LL n) (congrFun hz i)
      simpa only [Pi.sub_apply, map_sub] using this)
  have hc : ∀ a : PowerSeries O, PowerSeries.constantCoeff (PowerSeries.map (algebraMap O LL) a) =
      algebraMap O LL (PowerSeries.constantCoeff a) := fun a => by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hX : ∀ g, PowerSeries.constantCoeff
      ((PowerSeries.substAlgHom (hasSubst_γ R g) : PowerSeries LL →ₐ[LL] PowerSeries LL) PowerSeries.X) = 0 :=
    fun g => by rw [PowerSeries.substAlgHom_X]; exact constantCoeff_γX R g
  rw [← sub_eq_zero, ← sub_sub]
  funext i k
  refine eq_zero_of_fixed (PowerSeries.substAlgHom (hasSubst_γ R Γ.gam)) (hX _) (fun m hm => ?_)
    (fun i j => toL O LL n (Gm Γ.gam i j) k) (fun i j => ?_)
    (fun i => ((((Gm g).map (toL O LL n)).mulVec (fun j => γL R g (w j)) - w - fun j => toL O LL n (z' j)) i) k)
    (fun i => ?_) (fun i => ?_) i
  · rw [PowerSeries.substAlgHom_X, PowerSeries.coeff_map, (R.γ₀_X _).2]
    exact hu m hm
  · refine (hc (Gm Γ.gam i j k)).trans ?_
    rw [h2]
    split_ifs <;> simp
  · have e1 : PowerSeries.constantCoeff (toL O LL n (z' i) k) = 0 := (hc (z' i k)).trans (by rw [hz0, map_zero])
    have e2 : ∀ j, PowerSeries.constantCoeff (γL R g (w j) k) = 0 := fun j =>
      (constantCoeff_algHom _ (hX g) _).trans (hw0 j k)
    simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, Finset.sum_apply, Pi.mul_apply, map_sub, map_sum, map_mul,
      e1, e2, hw0, mul_zero, Finset.sum_const_zero, sub_zero]
  · have := congrFun (congrFun hf i) k
    rw [Matrix.mulVec, dotProduct, Finset.sum_apply] at this
    exact this

variable {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA] [Algebra O RW]
    {β : RA →+* LL ⊗[Qp] B} {hβ : ∀ (o : O) (r : RA), β (o • r) = algebraMap O LL o • β r}
    {inclR : RA →ₐ[O] RW}

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, 0, by simp, by simp, by simp⟩`.
-/
theorem val_zero (T : LocLat G Qp LL O) : Val β hβ inclR T 0 0 :=
  ⟨1, 0, by simp, by simp, by simp⟩

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simpa using val_zero T`. Consider the case `insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha]`. Conclude with `(h a).add ih`.
-/
theorem val_sum {T : LocLat G Qp LL O} {ι : Type} (S : Finset ι) (j : ι → TW RW T) (z : ι → T.V ⊗[Qp] B)
    (h : ∀ i, Val β hβ inclR T (j i) (z i)) : Val β hβ inclR T (∑ i ∈ S, j i) (∑ i ∈ S, z i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using val_zero T
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha]; exact (h a).add ih

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, (1 : RA) ⊗ₜ[O] t, by simp, by simp [TWincl], βB_tmul β hβ T 1 t⟩`.
-/
theorem val_tmul {T : LocLat G Qp LL O} (t : ↥T.L.T) :
    Val β hβ inclR T ((1 : RW) ⊗ₜ[O] t) ((t : T.V) ⊗ₜ[Qp] (1 : B)) :=
  ⟨1, (1 : RA) ⊗ₜ[O] t, by simp, by simp [TWincl], βB_tmul β hβ T 1 t⟩

variable {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA} {I : WIo R RA RW inclR φR gR πA} (E : WEt I)

/- English proof (translation)
Rewrite using `[← algebraMap_smul R.EE a x, E.γD_smul, R.γE_ext, algebraMap_smul]`.
-/
theorem γD_smulA (T : LocLat G Qp LL O) (g : Γ.Gam) (a : LetA O n) (x : E.DD T) :
    E.γD T g (a • x) = letγ (R.γ₀ g) a • E.γD T g x := by
  rw [← algebraMap_smul R.EE a x, E.γD_smul, R.γE_ext, algebraMap_smul]

/- English proof (translation)
Rewrite using `[← algebraMap_smul R.EE a x, E.φD_smul, R.φE_ext, algebraMap_smul]`.
-/
theorem φD_smulA (T : LocLat G Qp LL O) (a : LetA O n) (x : E.DD T) :
    E.φD T (a • x) = letφ R.φ₀ a • E.φD T x := by
  rw [← algebraMap_smul R.EE a x, E.φD_smul, R.φE_ext, algebraMap_smul]

/- English proof (translation)
Rewrite using `[← algebraMap_smul R.EE a x, E.jD_smul, I.ioE_ext]`.
-/
theorem jD_smulA (T : LocLat G Qp LL O) (a : LetA O n) (x : E.DD T) :
    E.jD T (a • x) = inclR (I.io a) • E.jD T x := by
  rw [← algebraMap_smul R.EE a x, E.jD_smul, I.ioE_ext]

/- English proof (translation)
Use `choose x hx using he`. Establish `hval : ∀ c : ι → LetA O n, Val β hβ inclR T (E.jD T (∑ i, c i • e i)) (∑ i, actS T.V B (β (I.io (c i))) (x i))`. Introduce `c`. Rewrite using `[map_sum]`. Use `val_sum _ _ _ fun i => ?_` and prove the remaining obligations.

Rewrite using `[jD_smulA]`. Conclude with `(hx i).smul _`. Set `a : ι → ↥Dc.C` to `fun j => ⟨_, hC j⟩`. Establish `hτ : IsUnit (Dc.J Dc.t ^ p)`. Rewrite using `[Dc.periodDiscJ_tateElement]`.

Conclude with `(Dc.tb_unit.map (Algebra.TensorProduct.includeRight : B →ₐ[Qp] LL ⊗[Qp] B)).pow p`. Take `⟨w', hw'⟩` from `((Module.End.isUnit_iff _).mp (hτ.map (actS T.V B))).2 (∑ j, actS T.V B (Dc.J (a j)) (x j))`. Use `⟨w', fun g z' hz => ?_⟩` and prove the remaining obligations. Use `letI : Module (LL ⊗[Qp] B) (T.V ⊗[Qp] B) := Module.compHom _ (actS (LL := LL) T.V B).toRingHom`. Establish `key` using `div_unit (Algebra.TensorProduct.map (AlgHom.id Qp LL) ((PD.actB g).toAlgHom.restrictScalars Qp)).toRingHom (actVB PD T.ρ g).toAddMonoidHom (fun s m => map_actS (T.ρ g) ((PD.actB g).toAlgHom.restrictScalars Qp) s m) x (fun i j => β (I.io (Gm (Γ.resΓ g) i j))) (fun j => by`.

Use `Val.unique hinj ?_ (hval fun i => Gm (Γ.resΓ g) i j)` and prove the remaining obligations. Rewrite using `[← h5, E.jD_act]`. Conclude with `Val.map (T.ρ g) (T.actT g) (fun _ => rfl) (gA g) (gR g) _ (hg1 g) (hg2 g) (hx j))`. Use the proof step `(Dc.J Dc.t ^ p) hτ (fun j => Dc.J (a j)) (fun i => β (I.io (z' i))) (fun i => by`. Establish `e1 : Dc.t ^ p * ∑ j, (⟨_, Dc.toL_mem (Gm (Γ.resΓ g) i j)⟩ : ↥Dc.C) * ⟨γL R (Γ.resΓ g) (a j), Dc.γ_mem _ _ (a j).2⟩ = (⟨γL R (Γ.resΓ g) Dc.t, Dc.γ_mem _ _ Dc.t.2⟩ : ↥Dc.C) ^ p * (a i + Dc.t ^ p * ⟨_, Dc.toL_mem (z' i)⟩)`.

Apply `Subtype.ext` to reduce the goal to its premises. Establish `h` using `congrFun hz i`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.add_apply] at h`. Establish `h' : ∑ j, toL O LL n (Gm (Γ.resΓ g) i j) * γL R (Γ.resΓ g) ((Dc.t : LetA LL n) ^ p * w j) = γL R (Γ.resΓ g) Dc.t ^ p * (w i + toL O LL n (z' i))`. Rewrite using `[← h, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_pow]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, AddSubmonoidClass.coe_finset_sum, AddMemClass.coe_add, a, h']`. Expand and normalize the polynomial expressions, which then agree.

Establish `e2` using `congrArg Dc.J e1`. Simplify using `only [map_mul, map_pow, map_sum, map_add, Dc.J_toL, Dc.J_γ] at e2`. Rewrite using `[map_pow]`. Conclude with `e2) w' hw'`. Establish `key' : actVB PD T.ρ g w' - w' = ∑ i, actS T.V B (β (I.io (z' i))) (x i)` using `key`.

Rewrite using `[key']`. Conclude with `hval z'`.
-/
theorem exists_val (hinj : Function.Injective inclR) (gA : G → (RA →ₐ[O] RA))
    (hg1 : ∀ g r, inclR (gA g r) = gR g (inclR r))
    (hg2 : ∀ g r, β (gA g r) =
      Algebra.TensorProduct.map (AlgHom.id Qp LL) ((PD.actB g).toAlgHom.restrictScalars Qp) (β r))
    {tS zS : BdR} (Dc : Disc R (β.comp I.io.toRingHom) tS zS) (T : LocLat G Qp LL O) {ι : Type} [Fintype ι]
    (e : ι → E.DD T) (he : ∀ j, ∃ x, Val β hβ inclR T (E.jD T (e j)) x) (Gm : Γ.Gam → Matrix ι ι (LetA O n))
    (h5 : ∀ g j, E.γD T g (e j) = ∑ i, Gm g i j • e i) (w : ι → LetA LL n) (p : ℕ)
    (hC : ∀ j, (Dc.t : LetA LL n) ^ p * w j ∈ Dc.C) :
    ∃ w' : T.V ⊗[Qp] B, ∀ (g : G) (z' : ι → LetA O n),
      (((Gm (Γ.resΓ g)).map (toL O LL n)).mulVec (fun j => γL R (Γ.resΓ g) (w j)) =
        w + fun j => toL O LL n (z' j)) →
      Val β hβ inclR T (E.jD T (∑ i, z' i • e i)) (actVB PD T.ρ g w' - w') := by
  choose x hx using he
  have hval : ∀ c : ι → LetA O n, Val β hβ inclR T (E.jD T (∑ i, c i • e i))
      (∑ i, actS T.V B (β (I.io (c i))) (x i)) := by
    intro c
    rw [map_sum]
    refine val_sum _ _ _ fun i => ?_
    rw [jD_smulA]
    exact (hx i).smul _
  let a : ι → ↥Dc.C := fun j => ⟨_, hC j⟩
  have hτ : IsUnit (Dc.J Dc.t ^ p) := by
    rw [Dc.periodDiscJ_tateElement]
    exact (Dc.tb_unit.map (Algebra.TensorProduct.includeRight : B →ₐ[Qp] LL ⊗[Qp] B)).pow p
  obtain ⟨w', hw'⟩ := ((Module.End.isUnit_iff _).mp (hτ.map (actS T.V B))).2
    (∑ j, actS T.V B (Dc.J (a j)) (x j))
  refine ⟨w', fun g z' hz => ?_⟩
  letI : Module (LL ⊗[Qp] B) (T.V ⊗[Qp] B) := Module.compHom _ (actS (LL := LL) T.V B).toRingHom
  have key := div_unit
    (Algebra.TensorProduct.map (AlgHom.id Qp LL) ((PD.actB g).toAlgHom.restrictScalars Qp)).toRingHom
    (actVB PD T.ρ g).toAddMonoidHom
    (fun s m => map_actS (T.ρ g) ((PD.actB g).toAlgHom.restrictScalars Qp) s m) x
    (fun i j => β (I.io (Gm (Γ.resΓ g) i j))) (fun j => by
      refine Val.unique hinj ?_ (hval fun i => Gm (Γ.resΓ g) i j)
      rw [← h5, E.jD_act]
      exact Val.map (T.ρ g) (T.actT g) (fun _ => rfl) (gA g) (gR g) _ (hg1 g) (hg2 g) (hx j))
    (Dc.J Dc.t ^ p) hτ (fun j => Dc.J (a j)) (fun i => β (I.io (z' i))) (fun i => by
      have e1 : Dc.t ^ p * ∑ j, (⟨_, Dc.toL_mem (Gm (Γ.resΓ g) i j)⟩ : ↥Dc.C) *
            ⟨γL R (Γ.resΓ g) (a j), Dc.γ_mem _ _ (a j).2⟩ =
          (⟨γL R (Γ.resΓ g) Dc.t, Dc.γ_mem _ _ Dc.t.2⟩ : ↥Dc.C) ^ p *
            (a i + Dc.t ^ p * ⟨_, Dc.toL_mem (z' i)⟩) := by
        apply Subtype.ext
        have h := congrFun hz i
        simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.add_apply] at h
        have h' : ∑ j, toL O LL n (Gm (Γ.resΓ g) i j) * γL R (Γ.resΓ g) ((Dc.t : LetA LL n) ^ p * w j) =
            γL R (Γ.resΓ g) Dc.t ^ p * (w i + toL O LL n (z' i)) := by
          rw [← h, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_mul, map_pow]
          ring
        simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, AddSubmonoidClass.coe_finset_sum,
          AddMemClass.coe_add, a, h']
        ring
      have e2 := congrArg Dc.J e1
      simp only [map_mul, map_pow, map_sum, map_add, Dc.J_toL, Dc.J_γ] at e2
      rw [map_pow]
      exact e2) w' hw'
  have key' : actVB PD T.ρ g w' - w' = ∑ i, actS T.V B (β (I.io (z' i))) (x i) := key
  rw [key']
  exact hval z'

/- English proof (translation)
Use `choose b hb using fun k => PowerSeries.X_dvd_iff.mpr (h k)`. Conclude with `Ideal.mem_span_singleton.mpr ⟨b, funext hb⟩`.
-/
theorem mem_span_letπ {a : LetA O n} (h : ∀ k, PowerSeries.constantCoeff (a k) = 0) :
    a ∈ Ideal.span {(letπ : LetA O n)} := by
  choose b hb using fun k => PowerSeries.X_dvd_iff.mpr (h k)
  exact Ideal.mem_span_singleton.mpr ⟨b, funext hb⟩

end Layers

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {s : ℕ} {Γ : WGam PD LL O v n s} {R : WSer Γ}
    {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
    {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {I : WIo R (O ⊗[Zl] Ai) RW inclR φR gR πA} {E : WEt I} {zl : PowerSeries Zl →+* LetA O n}
    {β : O ⊗[Zl] Ai →+* LL ⊗[Qp] B} {hβ : ∀ (o : O) (r : O ⊗[Zl] Ai), β (o • r) = algebraMap O LL o • β r}

def Solvable (γ φ : LetA O n →ₐ[O] LetA O n) (γ' : LetA LL n → LetA LL n) (Q Λ : LetA O n)
    (C : Set (LetA LL n)) (t : LetA LL n) (r : ℕ) : Prop :=
  ∀ (m k : ℕ) (H Pm Pm' : Matrix (Fin r) (Fin r) (LetA O n)) (y z : Fin r → LetA O n),
    (∀ i j, (H - 1) i j ∈ Ideal.span {(letπ : LetA O n)}) →
    Pm * Pm' = (Q ^ k) • (1 : Matrix (Fin r) (Fin r) (LetA O n)) →
    (γ Q ^ m) • (Pm * H.map φ) = (Q ^ m) • (H * Pm.map γ) → (∀ j, z j ∈ Ideal.span {(letπ : LetA O n)}) →
    (Q ^ m * Λ) • H.mulVec (fun j => γ (y j)) - (Q ^ m * γ Λ) • y =
      (Λ * γ Λ) • (Pm.mulVec (fun j => φ (z j)) - (Q ^ m) • z) →
    ∃ (w : Fin r → LetA LL n) (p : ℕ), (∀ j i, PowerSeries.constantCoeff (w j i) = 0) ∧ (∀ j, t ^ p * w j ∈ C) ∧
      (H.map (toL O LL n)).mulVec (fun j => γ' (w j)) - w = fun j => toL O LL n (z j)

/- English proof (translation)
Take `⟨m, m', Gm, Pm, Pm', h1, h2, h3, h4, h5, h6⟩` from `GlobalTheory.HWL.Mat.wach_matrices Mo T r nb`. Set `e : Fin r → E.DD T` to `fun j => (nb j : E.DD T)`. Set `lin` to `Fintype.linearCombination (LetA O n) e`. Establish `hsur : ∀ x ∈ Mo.N T, ∃ c, lin c = x` using `fun x hx => ⟨nb.equivFun ⟨x, hx⟩, by`. Use `congrArg Subtype.val (nb.sum_equivFun ⟨x, hx⟩)` as an intermediate fact.

Rewrite `this` using `[AddSubmonoidClass.coe_finset_sum]`. Conclude with `(Fintype.linearCombination_apply _ _ _).trans this⟩`. Establish `hlin : Function.Injective lin` using `(injective_iff_map_eq_zero lin).mpr fun c hc => funext (Fintype.linearIndependent_iff.mp (nb.linearIndependent.map' (Mo.N T).subtype (Submodule.ker_subtype _)) c ((Fintype.linearCombination_apply _ _ _).symm.trans hc))`. Establish `hπ : ∀ z, (∃ x ∈ Mo.N T, (letπ : LetA O n) • x = z) → ∃ c, lin c = z ∧ ∀ j k, PowerSeries.constantCoeff (c j k) = 0`. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Take `⟨c, rfl⟩` from `hsur x hx`. Conclude with `⟨(letπ : LetA O n) • c, map_smul _ _ _, fun j k => by simp [letπ]⟩`. Establish `hγ : ∀ g c, E.γD T g (lin c) = lin ((Gm g).mulVec fun j => letγ (R.γ₀ g) (c j))` using `fun g c => by`. Use `semi_coord (letγ (R.γ₀ g)) (E.γD T g).toAddMonoidHom (γD_smulA E T g) e 1 (Gm g) (fun j => by rw [one_smul]; exact h5 g j) c` as an intermediate fact. Rewrite `this` using `[one_smul]`. Then use the resulting hypothesis.

Establish `hφ : ∀ c, R.Q ^ m • E.φD T (lin c) = lin (Pm.mulVec fun j => letφ R.φ₀ (c j))` using `fun c => semi_coord (letφ R.φ₀) (E.φD T).toAddMonoidHom (φD_smulA E T) e (R.Q ^ m) Pm h6 c`. Take `⟨cz, rfl, hz0⟩` from `hπ z hz`. Take `⟨cy, hcy⟩` from `hsur _ hy`. Take `⟨w, p, hw0, hwC, hw⟩` from `hS m m' (Gm Γ.gam) Pm Pm' cy cz (fun i j => mem_span_letπ fun k => by`. Rewrite using `[Matrix.sub_apply, Pi.sub_apply, map_sub, h2, Matrix.one_apply]`.

Apply the tactic sequence `split_ifs <;> simp) h3 (h4 _) (fun j => mem_span_letπ (hz0 j)) (by`. Apply `hlin` to reduce the goal to its premises. Rewrite using `[map_sub, map_smul, map_smul, map_smul, map_sub, map_smul, ← hγ, ← hφ, hcy, γD_smulA, ← smul_sub, ← hyz]`. Simplify using `only [smul_sub, smul_smul]`. Apply the tactic sequence `congr 2 <;> ring)`.

Take `⟨w', hw'⟩` from `exists_val (hβ := hβ) E hinj gA hg1 hg2 Dc T e (fun j => hval _ (nb j).2) Gm h5 w p hwC`. Use `⟨w', fun g z' hz' hzz => ?_⟩` and prove the remaining obligations. Take `⟨c, rfl, hc0⟩` from `hπ z' hz'`. Use `hw' g c (coord_eq hu Gm h1 h2 cz c w hw0 hw _ hc0 (hlin ?_))` and prove the remaining obligations. Rewrite using `[map_sub, map_sub, ← hγ, ← hγ, hzz]`.
-/
theorem core (Mo : WN E zl) (hinj : Function.Injective inclR) (gA : G → (O ⊗[Zl] Ai →ₐ[O] O ⊗[Zl] Ai))
    (hg1 : ∀ g r, inclR (gA g r) = gR g (inclR r))
    (hg2 : ∀ g r, β (gA g r) =
      Algebra.TensorProduct.map (AlgHom.id Qp LL) ((PD.actB g).toAlgHom.restrictScalars Qp) (β r))
    {tS zS : BdR} (Dc : Disc R (β.comp I.io.toRingHom) tS zS)
    (hu : ∀ k : ℕ, 0 < k → algebraMap O LL (Γ.χΓ Γ.gam : O) ^ k ≠ 1) (T : LocLat G Qp LL O) {r : ℕ}
    (nb : Module.Basis (Fin r) (LetA O n) ↥(Mo.N T))
    (hval : ∀ x ∈ Mo.N T, ∃ x', Val β hβ inclR T (E.jD T x) x') (Λ : LetA O n)
    (hS : Solvable (letγ (R.γ₀ Γ.gam)) (letφ R.φ₀) (γL R Γ.gam) R.Q Λ Dc.C Dc.t r) (y z : E.DD T)
    (hy : Λ • y ∈ Mo.N T) (hz : ∃ x ∈ Mo.N T, (letπ : LetA O n) • x = z)
    (hyz : E.γD T Γ.gam y - y = E.φD T z - z) :
    ∃ w' : T.V ⊗[Qp] B, ∀ (g : G) (z' : E.DD T), (∃ x ∈ Mo.N T, (letπ : LetA O n) • x = z') →
      E.γD T Γ.gam z' - z' = E.γD T (Γ.resΓ g) z - z →
      Val β hβ inclR T (E.jD T z') (actVB PD T.ρ g w' - w') := by
  obtain ⟨m, m', Gm, Pm, Pm', h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.HWL.Mat.wach_matrices Mo T r nb
  let e : Fin r → E.DD T := fun j => (nb j : E.DD T)
  let lin := Fintype.linearCombination (LetA O n) e
  have hsur : ∀ x ∈ Mo.N T, ∃ c, lin c = x := fun x hx =>
    ⟨nb.equivFun ⟨x, hx⟩, by
      have := congrArg Subtype.val (nb.sum_equivFun ⟨x, hx⟩)
      rw [AddSubmonoidClass.coe_finset_sum] at this
      exact (Fintype.linearCombination_apply _ _ _).trans this⟩
  have hlin : Function.Injective lin :=
    (injective_iff_map_eq_zero lin).mpr fun c hc => funext (Fintype.linearIndependent_iff.mp
      (nb.linearIndependent.map' (Mo.N T).subtype (Submodule.ker_subtype _)) c
      ((Fintype.linearCombination_apply _ _ _).symm.trans hc))
  have hπ : ∀ z, (∃ x ∈ Mo.N T, (letπ : LetA O n) • x = z) →
      ∃ c, lin c = z ∧ ∀ j k, PowerSeries.constantCoeff (c j k) = 0 := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, rfl⟩ := hsur x hx
    exact ⟨(letπ : LetA O n) • c, map_smul _ _ _, fun j k => by simp [letπ]⟩
  have hγ : ∀ g c, E.γD T g (lin c) = lin ((Gm g).mulVec fun j => letγ (R.γ₀ g) (c j)) := fun g c => by
    have := semi_coord (letγ (R.γ₀ g)) (E.γD T g).toAddMonoidHom (γD_smulA E T g) e 1 (Gm g)
      (fun j => by rw [one_smul]; exact h5 g j) c
    rwa [one_smul] at this
  have hφ : ∀ c, R.Q ^ m • E.φD T (lin c) = lin (Pm.mulVec fun j => letφ R.φ₀ (c j)) := fun c =>
    semi_coord (letφ R.φ₀) (E.φD T).toAddMonoidHom (φD_smulA E T) e (R.Q ^ m) Pm h6 c
  obtain ⟨cz, rfl, hz0⟩ := hπ z hz
  obtain ⟨cy, hcy⟩ := hsur _ hy
  obtain ⟨w, p, hw0, hwC, hw⟩ := hS m m' (Gm Γ.gam) Pm Pm' cy cz
    (fun i j => mem_span_letπ fun k => by
      rw [Matrix.sub_apply, Pi.sub_apply, map_sub, h2, Matrix.one_apply]
      split_ifs <;> simp) h3 (h4 _) (fun j => mem_span_letπ (hz0 j)) (by
      apply hlin
      rw [map_sub, map_smul, map_smul, map_smul, map_sub, map_smul, ← hγ, ← hφ, hcy, γD_smulA, ← smul_sub, ← hyz]
      simp only [smul_sub, smul_smul]
      congr 2 <;> ring)
  obtain ⟨w', hw'⟩ := exists_val (hβ := hβ) E hinj gA hg1 hg2 Dc T e (fun j => hval _ (nb j).2) Gm h5 w p hwC
  refine ⟨w', fun g z' hz' hzz => ?_⟩
  obtain ⟨c, rfl, hc0⟩ := hπ z' hz'
  refine hw' g c (coord_eq hu Gm h1 h2 cz c w hw0 hw _ hc0 (hlin ?_))
  rw [map_sub, map_sub, ← hγ, ← hγ, hzz]

end Core

section Functor

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
    {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {W : LocWach PD LL O v n} (E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA) {s : ℕ} (hs : W.s = s)
    (hp : PD.p.Prime) (hL : LevLaws W) (hI : IoLaws E)
    (β : O ⊗[Zl] Ai →+* LL ⊗[Qp] B)

/- English proof (translation)
Rewrite using `[map_prod, map_prod]`. Use `Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun j hj => ?_` and prove the remaining obligations. Use `clear hj`. Proceed by induction on `j with`. Consider the case `zero => simpa using hX`.

Consider the case `succ j ih`. Rewrite using `[pow_succ', AlgHom.mul_apply, hinj ((hφ3 _).trans (hφ1 _).symm), hφ2]`. Conclude with `ih.map _`.
-/
theorem isUnit_prod (hinj : Function.Injective inclR) (φA : O ⊗[Zl] Ai →ₐ[O] O ⊗[Zl] Ai)
    (hφ1 : ∀ r, inclR (φA r) = φR (inclR r))
    (hφ2 : ∀ r, β (φA r) = Algebra.TensorProduct.map (AlgHom.id Qp LL) PD.φ (β r))
    (hφ3 : ∀ a, inclR (E.io (W.φA a)) = φR (inclR (E.io a))) (hX : IsUnit (β (E.io W.X))) (m : ℕ) :
    IsUnit (β (E.io (∏ j ∈ Finset.range m, (W.φA ^ j) W.X))) := by
  rw [map_prod, map_prod]
  refine Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun j hj => ?_
  clear hj
  induction j with
  | zero => simpa using hX
  | succ j ih =>
    rw [pow_succ', AlgHom.mul_apply, hinj ((hφ3 _).trans (hφ1 _).symm), hφ2]
    exact ih.map _

include hI in
set_option maxHeartbeats 1000000 in

/- English proof (translation)
Substitute `hs` using the available equality. Establish `hβ : ∀ (o : O) (r : O ⊗[Zl] Ai), β (o • r) = algebraMap O LL o • β r`. Introduce `o r`. Proceed by induction on `r using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `add a b ha hb => simp only [smul_add, map_add, ha, hb]`. Consider the case `tmul a w => rw [smul_tmul', hβ₀, hβ₀, smul_tmul', smul_eq_mul, smul_eq_mul, map_mul]`. Establish `hN : nOf W T = W.N T` using `nOf_crys W hT`. Rewrite `nb`, `hu2`, `hy` using `[← hN]`. Establish `ha : ∀ x ∈ aN W T letπ, ∃ x' ∈ nOf W T, (letπ : LetA O n) • x' = x` using `fun x hx => hN ▸ hx`.

Take `⟨nb⟩` from `nb`. Establish `hyz' : W.γD T W.gam y - y = W.φD T z - z`. Establish `: (W.γD T W.gam y - y) + -(W.φD T z - z) = 0` using `hyz`. Conclude with `add_neg_eq_zero.mp this`. Take `⟨w', hw'⟩` from `core (hβ := hβ) (latOf E rfl hp hL hI zl h1 hP) hinj gA hg1 hg2 Dc hu T nb (fun x hx => by`.

Take `⟨y, hy⟩` from `hu2 x hx`. Rewrite `hy` using `[GlobalTheory.NL.SandArb.map_mulLeft, ← map_pow]`. Conclude with `Val.exists (by rw [map_pow]; exact hu1.pow m) hy) Λ hS y z hy (ha z hz) hyz'`. Take `⟨b₀, hb₀⟩` from `hb`. Rewrite `hb₀` using `[GlobalTheory.NL.SandArb.map_mulLeft, ← map_pow]`.

Take `⟨b', hb'⟩` from `Val.exists (hβ := hβ) (T := T) (by rw [map_pow]; exact hu3.pow a) hb₀`. Use `⟨c, ⟨c.2, c.2.1, w' - b', fun g => ?_⟩, hc1⟩` and prove the remaining obligations. Take `⟨t, ht1, ht2⟩` from `hc2 g`. Establish `k1 : Val β hβ inclR T (E.jD T (zz g)) (actVB PD T.ρ g w' - w')` using `hw' g (zz g) (ha _ (hz1 g)) (hz2 g)`. Establish `k2 : Val β hβ inclR T (TWact (gR g) T g b) (actVB PD T.ρ g b')` using `Val.map (T.ρ g) (T.actT g) (fun _ => rfl) (gA g) (gR g) _ (hg1 g) (hg2 g) hb'`.

Establish `k3` using `(val_tmul (β := β) (hβ := hβ) (inclR := inclR) t).add k2`. Rewrite `k3` using `[ht2, show E.jD T (zz g) - (TWact (gR g) T g b - b) + TWact (gR g) T g b = E.jD T (zz g) + b by abel]`. Establish `k4` using `k3.unique hinj (k1.add hb')`. Rewrite `k4` using `[ht1]`. Express the relevant statement in the definitionally equal form `(c : ↥W.GKs → T.V) g ⊗ₜ[Qp] (1 : B) = _`.

Rewrite using `[map_sub, eq_sub_of_add_eq k4]`. Normalize the expressions using the abelian group laws.
-/
theorem mem_of_layers (ιA : Ai →+* B)
    (hβ₀ : ∀ (o : O) (w : Ai), β (o ⊗ₜ[Zl] w) = algebraMap O LL o ⊗ₜ[Qp] ιA w)
    (zl : PowerSeries Zl →+* LetA O n) (h1 : IsCrys PD W.one.ρ)
    (hP : ∀ T, @Module.Projective (PowerSeries Zl) _ ↥(W.N T) _ (Module.compHom _ zl))
    (hinj : Function.Injective inclR) (gA : G → (O ⊗[Zl] Ai →ₐ[O] O ⊗[Zl] Ai))
    (hg1 : ∀ g r, inclR (gA g r) = gR g (inclR r))
    (hg2 : ∀ g r, β (gA g r) =
      Algebra.TensorProduct.map (AlgHom.id Qp LL) ((PD.actB g).toAlgHom.restrictScalars Qp) (β r))
    {tS zS : BdR} (Dc : Disc (serOf W hs hp hL) (β.comp E.io.toRingHom) tS zS)
    (hu : ∀ k : ℕ, 0 < k → algebraMap O LL (W.χΓ W.gam : O) ^ k ≠ 1) (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ)
    {r : ℕ} (nb : Nonempty (Module.Basis (Fin r) (LetA O n) ↥(W.N T))) (u : O ⊗[Zl] Ai) (hu1 : IsUnit (β u))
    (m : ℕ) (hu2 : ∀ x ∈ W.N T, ∃ y : TW (O ⊗[Zl] Ai) T, TWincl inclR T y =
      TensorProduct.map (LinearMap.mulLeft O (inclR u ^ m)) LinearMap.id (E.jD T x)) (Λ : LetA O n)
    (hS : Solvable (W.γA W.gam) W.φA (γL (serOf W hs hp hL) W.gam) W.Q Λ Dc.C Dc.t r) (y z : W.DD T)
    (hy : Λ • y ∈ W.N T) (hz : z ∈ aN W T letπ) (hyz : (y, z) ∈ W.divisibleCocycles T) (zz : ↥W.GKs → W.DD T)
    (hz1 : ∀ g, zz g ∈ aN W T letπ) (hz2 : ∀ g, W.γ T (zz g) - zz g = W.γD T (W.resΓ g) z - z) (b : TW RW T)
    (u' : O ⊗[Zl] Ai) (hu3 : IsUnit (β u')) (a : ℕ)
    (hb : TensorProduct.map (LinearMap.mulLeft O (inclR u' ^ a)) LinearMap.id b ∈ TAinf inclR T)
    (c : ↥(latticeCocycles (resLat T W.GKs))) (hc1 : Submodule.Quotient.mk c = W.cl T ⟨(y, z), hyz⟩)
    (hc2 : ∀ g : ↥W.GKs, ∃ t : ↥T.L.T, (t : T.V) = (c : ↥W.GKs → T.V) g ∧
      (1 : RW) ⊗ₜ[O] t = E.jD T (zz g) - (TWact (gR g) T g b - b)) :
    W.cl T ⟨(y, z), hyz⟩ ∈ H1fIntegralCyclotomicLayer W T := by
  subst hs
  have hβ : ∀ (o : O) (r : O ⊗[Zl] Ai), β (o • r) = algebraMap O LL o • β r := by
    intro o r
    induction r using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [smul_add, map_add, ha, hb]
    | tmul a w => rw [smul_tmul', hβ₀, hβ₀, smul_tmul', smul_eq_mul, smul_eq_mul, map_mul]
  have hN : nOf W T = W.N T := nOf_crys W hT
  rw [← hN] at nb hu2 hy
  have ha : ∀ x ∈ aN W T letπ, ∃ x' ∈ nOf W T, (letπ : LetA O n) • x' = x := fun x hx => hN ▸ hx
  obtain ⟨nb⟩ := nb
  have hyz' : W.γD T W.gam y - y = W.φD T z - z := by
    have : (W.γD T W.gam y - y) + -(W.φD T z - z) = 0 := hyz
    exact add_neg_eq_zero.mp this
  obtain ⟨w', hw'⟩ := core (hβ := hβ) (latOf E rfl hp hL hI zl h1 hP) hinj gA hg1 hg2 Dc hu T nb
    (fun x hx => by
      obtain ⟨y, hy⟩ := hu2 x hx
      rw [GlobalTheory.NL.SandArb.map_mulLeft, ← map_pow] at hy
      exact Val.exists (by rw [map_pow]; exact hu1.pow m) hy) Λ hS y z hy (ha z hz) hyz'
  obtain ⟨b₀, hb₀⟩ := hb
  rw [GlobalTheory.NL.SandArb.map_mulLeft, ← map_pow] at hb₀
  obtain ⟨b', hb'⟩ := Val.exists (hβ := hβ) (T := T) (by rw [map_pow]; exact hu3.pow a) hb₀
  refine ⟨c, ⟨c.2, c.2.1, w' - b', fun g => ?_⟩, hc1⟩
  obtain ⟨t, ht1, ht2⟩ := hc2 g
  have k1 : Val β hβ inclR T (E.jD T (zz g)) (actVB PD T.ρ g w' - w') := hw' g (zz g) (ha _ (hz1 g)) (hz2 g)
  have k2 : Val β hβ inclR T (TWact (gR g) T g b) (actVB PD T.ρ g b') :=
    Val.map (T.ρ g) (T.actT g) (fun _ => rfl) (gA g) (gR g) _ (hg1 g) (hg2 g) hb'
  have k3 := (val_tmul (β := β) (hβ := hβ) (inclR := inclR) t).add k2
  rw [ht2, show E.jD T (zz g) - (TWact (gR g) T g b - b) + TWact (gR g) T g b = E.jD T (zz g) + b by abel] at k3
  have k4 := k3.unique hinj (k1.add hb')
  rw [ht1] at k4
  change (c : ↥W.GKs → T.V) g ⊗ₜ[Qp] (1 : B) = _
  rw [map_sub, eq_sub_of_add_eq k4]
  abel

end Functor

section Concrete

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ} {LL : FinExt l}

/- English proof (translation)
Use `⟨fun g => Algebra.TensorProduct.map (AlgHom.id _ _) (AI.actWHom (g : GQ l)).toAlgHom, Algebra.TensorProduct.map (AlgHom.id _ _) (frobA l), fun g r => ?_, fun g r => ?_, fun r => ?_, fun r => ?_⟩` and prove the remaining obligations. Use `map_map_comm (inclWA l) _ _ (fun w => ?_) r` and prove the remaining obligations. Use extensionality with `k`. Conclude with `(autCb_alg l (AI.actT (g : GQ l)) (w.coeff k)).symm`. Conclude with `beta_map β AI.ιA hβ _ _ (fun w => (AI.ιA_act g w).trans (P.PD_actB K g _).symm) r`.

Use `map_map_comm (inclWA l) _ _ (fun w => ?_) r` and prove the remaining obligations. Use extensionality with `k`. Conclude with `map_pow (algebraMap (OCb l) (Cb l)) (w.coeff k) l`. Use `beta_map β AI.ιA hβ _ _ (fun w => ?_) r` and prove the remaining obligations. Use `Eq.trans ?_ ((AI.ιA_φ w).trans (P.PD_φ K _).symm)` and prove the remaining obligations.

Rewrite using `[WittVector.frobenius_eq_map_frobenius]`. Both sides reduce to the same expression.
-/
theorem exists_actions (K : FinExt l) {β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B} (hβ : IsBeta AI β) :
    ∃ (gA : ↥(GK K) → (RA LL →ₐ[↥(OL LL)] RA LL)) (φA : RA LL →ₐ[↥(OL LL)] RA LL),
      (∀ g r, inclR LL (gA g r) = AI.gRW LL (g : GQ l) (inclR LL r)) ∧
      (∀ g r, β (gA g r) = Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥LL.1)
        (((P.PD K).actB g).toAlgHom.restrictScalars ℚ_[l]) (β r)) ∧
      (∀ r, inclR LL (φA r) = φRW LL (inclR LL r)) ∧
      ∀ r, β (φA r) = Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥LL.1) (P.PD K).φ (β r) := by
  refine ⟨fun g => Algebra.TensorProduct.map (AlgHom.id _ _) (AI.actWHom (g : GQ l)).toAlgHom,
    Algebra.TensorProduct.map (AlgHom.id _ _) (frobA l), fun g r => ?_, fun g r => ?_, fun r => ?_, fun r => ?_⟩
  · refine map_map_comm (inclWA l) _ _ (fun w => ?_) r
    ext k
    exact (autCb_alg l (AI.actT (g : GQ l)) (w.coeff k)).symm
  · exact beta_map β AI.ιA hβ _ _ (fun w => (AI.ιA_act g w).trans (P.PD_actB K g _).symm) r
  · refine map_map_comm (inclWA l) _ _ (fun w => ?_) r
    ext k
    exact map_pow (algebraMap (OCb l) (Cb l)) (w.coeff k) l
  · refine beta_map β AI.ιA hβ _ _ (fun w => ?_) r
    refine Eq.trans ?_ ((AI.ιA_φ w).trans (P.PD_φ K _).symm)
    rw [WittVector.frobenius_eq_map_frobenius]
    rfl

/- English proof (translation)
Take `⟨J, hJ⟩` from `GlobalTheory.HWL.BanachEval.exists_eval l P AI hT K s LL h Γ R I hI β hβ`. Take `⟨Dc, hC, ht⟩` from `GlobalTheory.HWL.Cmp.OpenDisc.exists_disc l P AI hT K s LL h Γ R I hI β hβ J hJ (GlobalTheory.HWL.LevExp.lev_isExp l P K s LL Γ R) (GlobalTheory.HWL.Letter.letter l P AI hT K s LL h Γ R I hI β hβ)`. Conclude with `⟨Dc, fun p w hw => hC _ fun k => by rw [ht]; exact hw k⟩`.
-/
theorem exists_disc' (hT : LocTied l P AI) (h : Good K s LL) (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R)
    (hI : IoW I) {β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B} (hβ : IsBeta AI β) :
    ∃ D : Disc R (β.comp I.io.toRingHom) ((((l : ℚ_[l]) ^ s)⁻¹) • P.ιB P.tB)
        (algebraMap (Om l) P.R.BdR (P.ζQ s)),
      ∀ (p : ℕ) (w : LetA ↥LL.1 (Module.finrank ℚ_[l] ↥(K0 K))), (∀ i, Conv (logS LL ^ p * w i)) →
        (D.t : LetA ↥LL.1 (Module.finrank ℚ_[l] ↥(K0 K))) ^ p * w ∈ D.C := by
  obtain ⟨J, hJ⟩ := GlobalTheory.HWL.BanachEval.exists_eval l P AI hT K s LL h Γ R I hI β hβ
  obtain ⟨Dc, hC, ht⟩ := GlobalTheory.HWL.Cmp.OpenDisc.exists_disc l P AI hT K s LL h Γ R I hI β hβ J hJ
    (GlobalTheory.HWL.LevExp.lev_isExp l P K s LL Γ R) (GlobalTheory.HWL.Letter.letter l P AI hT K s LL h Γ R I hI β hβ)
  exact ⟨Dc, fun p w hw => hC _ fun k => by rw [ht]; exact hw k⟩

end Concrete

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `m k H Pm Pm' y z h1 h2 h3 h4 h5`. Take `⟨w, p, k1, k2, k3⟩` from `GlobalTheory.NL.exists_cocycle_solution_conv D HW l K s LL h r m k J H Pm Pm' y z h1 h2 h3 h4 h5`. Use `⟨w, p, k1, fun j => hC p _ (k2 j), ?_⟩` and prove the remaining obligations. Conclude with `(congrArg (fun f => (H.map (toL _ _ _)).mulVec f - w) (funext fun j => γL_apply (SerL (HW l) (F l) h hL) _ (w j))).trans k3`.
-/
theorem solvable (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime]
    (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (hL : Laws (HW l) (F l) h) (J : Multiset ℕ) (r : ℕ)
    (C : Set (LetA ↥LL.1 (Module.finrank ℚ_[l] ↥(K0 K)))) (t : LetA ↥LL.1 (Module.finrank ℚ_[l] ↥(K0 K)))
    (hC : ∀ (p : ℕ) (w : LetA ↥LL.1 (Module.finrank ℚ_[l] ↥(K0 K))), (∀ i, Conv (logS LL ^ p * w i)) →
      t ^ p * w ∈ C) :
    Solvable (((HW l).W K s LL h).γA ((HW l).W K s LL h).gam) ((HW l).W K s LL h).φA
      (γL (SerL (HW l) (F l) h hL) ((HW l).W K s LL h).gam) ((HW l).W K s LL h).Q
      (J.map fun j => (((HW l).W K s LL h).φA ^ j) ((HW l).W K s LL h).Q).prod C t r := by
  intro m k H Pm Pm' y z h1 h2 h3 h4 h5
  obtain ⟨w, p, k1, k2, k3⟩ := GlobalTheory.NL.exists_cocycle_solution_conv D HW l K s LL h r m k J H Pm Pm' y z h1 h2 h3 h4 h5
  refine ⟨w, p, k1, fun j => hC p _ (k2 j), ?_⟩
  exact (congrArg (fun f => (H.map (toL _ _ _)).mulVec f - w)
    (funext fun j => γL_apply (SerL (HW l) (F l) h hL) _ (w j))).trans k3

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 200000 in

/- English proof (translation)
Introduce `D HW F l _ K s LL h T hT J y z hy hz hyz`. Use `Classical.byContradiction fun hcon => ?_` and prove the remaining obligations. Establish `hL : Laws (HW l) (F l) h` using `Holds.laws (HW l) (F l) h`. Establish `hTied` using `D.locT l`. Take `⟨β, hβ⟩` from `GlobalTheory.HWLBeta.exists_beta l _ _ hTied LL`.

Take `⟨gA, φA, hg1, hg2, hφ1, hφ2⟩` from `exists_actions K hβ`. Take `⟨hX, -, hinj, -, hφ3, -⟩` from `GlobalTheory.NL.IoXQ.main D HW F l K s LL h`. Establish `hXu : IsUnit (β (((F l).E K s LL h).tie.io ((HW l).W K s LL h).X))`. Rewrite using `[hX, hβ]`. Conclude with `((GlobalTheory.TiedMu.tied_mu_units l _ _ hTied).1 1).map (Algebra.TensorProduct.includeRight : (D.loc l).R.B →ₐ[ℚ_[l]] ↥LL.1 ⊗[ℚ_[l]] (D.loc l).R.B)`.

Take `⟨Dc, hC⟩` from `exists_disc' hTied h (GamL (HW l) h) (SerL (HW l) (F l) h hL) (IoL (HW l) (F l) h hL) (ioW (HW l) (F l) h hL) hβ`. Take `⟨m, hm, -⟩` from `GlobalTheory.NL.SandArb.sandwich D HW F l K s LL h T hT`. Take `⟨zz, hz1, hz2, hz3⟩` from `GlobalTheory.T.zg_formula_alt D HW F l K s LL h T hT y z hz hyz`. Take `⟨b, hb⟩` from `(GlobalTheory.WittTensorFixed.main l K LL T).1 (((F l).E K s LL h).tie.jD T y)`. Take `⟨c, hc1, hc2⟩` from `hz3 b hb`.

Take `⟨a, ha⟩` from `GlobalTheory.NL.FrobDenom.main D HW F l K s LL h T hT J y hy b hb J.sup fun _ => Multiset.le_sup`. Conclude with `hcon <| mem_of_layers ((F l).E K s LL h).tie ((HW l).W_s K s LL h) (p_prime (D.loc l) K) hL.lev hL.io β (D.locA l).ιA hβ _ hL.one ((HW l).W_proj K s LL h) hinj gA hg1 hg2 Dc (chi_gam_pow_ne_one h (GamL (HW l) h)) T hT (N_basis_loc (HW l) K s LL h T hT) _ hXu m hm _ (solvable D HW …`.
-/
theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), P7 D HW F := by
  intro D HW F l _ K s LL h T hT J y z hy hz hyz
  refine Classical.byContradiction fun hcon => ?_
  have hL : Laws (HW l) (F l) h := Holds.laws (HW l) (F l) h
  have hTied := D.locT l
  obtain ⟨β, hβ⟩ := GlobalTheory.HWLBeta.exists_beta l _ _ hTied LL
  obtain ⟨gA, φA, hg1, hg2, hφ1, hφ2⟩ := exists_actions K hβ
  obtain ⟨hX, -, hinj, -, hφ3, -⟩ := GlobalTheory.NL.IoXQ.main D HW F l K s LL h
  have hXu : IsUnit (β (((F l).E K s LL h).tie.io ((HW l).W K s LL h).X)) := by
    rw [hX, hβ]
    exact ((GlobalTheory.TiedMu.tied_mu_units l _ _ hTied).1 1).map
      (Algebra.TensorProduct.includeRight : (D.loc l).R.B →ₐ[ℚ_[l]] ↥LL.1 ⊗[ℚ_[l]] (D.loc l).R.B)
  obtain ⟨Dc, hC⟩ := exists_disc' hTied h (GamL (HW l) h) (SerL (HW l) (F l) h hL) (IoL (HW l) (F l) h hL)
    (ioW (HW l) (F l) h hL) hβ
  obtain ⟨m, hm, -⟩ := GlobalTheory.NL.SandArb.sandwich D HW F l K s LL h T hT
  obtain ⟨zz, hz1, hz2, hz3⟩ := GlobalTheory.T.zg_formula_alt D HW F l K s LL h T hT y z hz hyz
  obtain ⟨b, hb⟩ := (GlobalTheory.WittTensorFixed.main l K LL T).1 (((F l).E K s LL h).tie.jD T y)
  obtain ⟨c, hc1, hc2⟩ := hz3 b hb
  obtain ⟨a, ha⟩ := GlobalTheory.NL.FrobDenom.main D HW F l K s LL h T hT J y hy b hb J.sup fun _ => Multiset.le_sup
  exact hcon <| mem_of_layers ((F l).E K s LL h).tie ((HW l).W_s K s LL h) (p_prime (D.loc l) K) hL.lev hL.io β
    (D.locA l).ιA hβ _ hL.one ((HW l).W_proj K s LL h) hinj gA hg1 hg2 Dc
    (chi_gam_pow_ne_one h (GamL (HW l) h)) T hT (N_basis_loc (HW l) K s LL h T hT) _ hXu m hm _
    (solvable D HW F l K s LL h hL J _ _ _ hC) y z hy hz hyz zz hz1 hz2 b _
    (isUnit_prod ((F l).E K s LL h).tie β hinj φA hφ1 hφ2 hφ3 hXu _) a ha c hc1 hc2

end GlobalTheory.NL.PoleCrys
