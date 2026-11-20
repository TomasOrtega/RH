import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactVersion
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlock
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.LocalComponentGL
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.SubstSingleVar
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.AnalyticTransOfAdd
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstUnique

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (at1)
open Formalism.L2.Th1.E (tensor4 matCoord thetaProd)

namespace FormalGroupLawNegation

section Analytic

variable {n : Type} [Fintype n]

/- English proof (translation)
Unfold `tens4`. Use `Finset.analyticAt_fun_prod _ fun a _ => ?_` and prove the remaining obligations. Conclude with `h.comp_of_eq (f := slice a) ((ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 4 × n => ℂ) (a, i)).analyticAt 0)`. Both sides reduce to the same expression.
-/
theorem analyticAt_tens4 {θ : (n → ℂ) → ℂ} (h : AnalyticAt ℂ θ 0) : AnalyticAt ℂ (tens4 θ) 0 := by
  unfold tens4
  refine Finset.analyticAt_fun_prod _ fun a _ => ?_
  exact h.comp_of_eq (f := slice a)
    ((ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 4 × n => ℂ) (a, i)).analyticAt 0)
    rfl

/- English proof (translation)
Unfold `prodFn`. Use `Finset.analyticAt_fun_prod _ fun i _ => ?_` and prove the remaining obligations. Conclude with `(h i).comp_of_eq (f := fun z : n → ℂ => z i) ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : n => ℂ) i).analyticAt 0) rfl`.
-/
theorem analyticAt_prodFn {f : n → ℂ → ℂ} (h : ∀ i, AnalyticAt ℂ (f i) 0) : AnalyticAt ℂ (prodFn f) 0 := by
  unfold prodFn
  refine Finset.analyticAt_fun_prod _ fun i _ => ?_
  exact (h i).comp_of_eq (f := fun z : n → ℂ => z i)
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : n => ℂ) i).analyticAt 0) rfl

/- English proof (translation)
Establish `h1 : Differentiable ℂ (Formalism.L2.Th1.F.opU L s θ)`. Unfold `Formalism.L2.Th1.F.opU Formalism.L2.Th1.F.herm`. Use `fun_prop`. Conclude with `h1.analyticAt 0`.
-/
theorem analyticAt_opU (L : PeriodPair) (s : ℂ) {θ : ℂ → ℂ} (h : Differentiable ℂ θ) :
    AnalyticAt ℂ (Formalism.L2.Th1.F.opU L s θ) 0 := by
  have h1 : Differentiable ℂ (Formalism.L2.Th1.F.opU L s θ) := by
    unfold Formalism.L2.Th1.F.opU Formalism.L2.Th1.F.herm
    fun_prop
  exact h1.analyticAt 0

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty`. Use `⟨by simpa using analyticAt_const, ?_⟩` and prove the remaining obligations. Establish `h0` using `(hLin n (fun _ => 0) (fun _ => 0) analyticAt_const analyticAt_const).2 0`. Simplify using `using h0`.

Consider the case `insert a S ha ih`. Establish `h1 : AnalyticAt ℂ (fun z => c a * F a z) 0` using `analyticAt_const.mul (hF a)`. Simplify using `only [Finset.sum_insert ha]`. Use `⟨h1.add ih.1, ?_⟩` and prove the remaining obligations. Rewrite using `[(hLin n _ _ h1 ih.1).1, (hLin n _ _ (hF a) (hF a)).2 (c a), ih.2]`.
-/
theorem taylorMv_sum [DecidableEq n] (hLin : TaylorMvLinear) {κ : Type} (S : Finset κ) (c : κ → ℂ)
    (F : κ → (n → ℂ) → ℂ) (hF : ∀ x, AnalyticAt ℂ (F x) 0) :
    AnalyticAt ℂ (fun z => ∑ x ∈ S, c x * F x z) 0 ∧
      taylorMv (fun z => ∑ x ∈ S, c x * F x z) = ∑ x ∈ S, MvPowerSeries.C (c x) * taylorMv (F x) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using analyticAt_const, ?_⟩
    have h0 := (hLin n (fun _ => 0) (fun _ => 0) analyticAt_const analyticAt_const).2 0
    simpa using h0
  | insert a S ha ih =>
    have h1 : AnalyticAt ℂ (fun z => c a * F a z) 0 := analyticAt_const.mul (hF a)
    simp only [Finset.sum_insert ha]
    refine ⟨h1.add ih.1, ?_⟩
    rw [(hLin n _ _ h1 ih.1).1, (hLin n _ _ (hF a) (hF a)).2 (c a), ih.2]

end Analytic

section Arith

/- English proof (translation)
Establish `h1 : ‖ι (((Real.sqrt n' : ℝ) : ℂ)⁻¹)‖ = 1`. Rewrite using `[map_inv₀, norm_inv]`. Establish `h2 : ‖ι ((Real.sqrt n' : ℝ) : ℂ)‖ ^ 2 = 1`. Rewrite using `[← norm_pow, ← map_pow, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast, map_natCast]`. Conclude with `Formalism.L2.Th1.E.Tor.norm_natCast l hn'`.

Rewrite using `[(pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2, inv_one]`. Establish `h2 : ‖ι (β x)‖ = 1`. Apply the tactic sequence `rcases hβ.1 x hx with h | h <;> simp [h]`. Establish `h3 : ‖ι (Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE H s x : ℂ)))‖ = 1`. Establish `hs' : (N : ℂ) • s ∈ dualLat H Λb` using `by rw [hsd]; exact hs`.

Take `⟨m, hm⟩` from `hs' x hx`. Establish `hE : altE H ((N : ℂ) • s) x = N * altE H s x` using `by simp [altE]`. Establish `hc : (N : ℂ) * (altE H s x : ℂ) = (m : ℂ)`. Rewrite `hm` using `[hE]`. Conclude with `hm` after adjusting the coercions.

Establish `h4 : ‖ι (Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE H s x : ℂ)))‖ ^ (2 * N) = 1`. Rewrite using `[← norm_pow, ← map_pow, ← Complex.exp_nat_mul]`. Establish `h5 : ((2 * N : ℕ) : ℂ) * (-(Real.pi : ℂ) * Complex.I * (altE H s x : ℂ)) = ((-m : ℤ) : ℂ) * (2 * Real.pi * Complex.I)`. Use `push_cast`. Take the linear combination `(-2 * (Real.pi : ℂ) * Complex.I) * hc`.

Rewrite using `[h5, Complex.exp_int_mul_two_pi_mul_I, map_one, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 h4`. Rewrite using `[map_mul, map_mul, map_mul, norm_mul, norm_mul, norm_mul, h1, h2, h3, mul_one, mul_one, mul_one]`. Conclude with `hε`.
-/
theorem norm_coeff {l : ℕ} [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) {V : Type} [AddCommGroup V] [Module ℂ V]
    (H : Sesq V) (Λb : AddSubgroup V) (hsd : IsSelfDual H Λb) (β : V → ℂ) (hβ : IsSemiChar H Λb β)
    (n' : ℕ) (hn' : ¬ l ∣ n') (ε : ℂ) (hε : ‖ι ε‖ ≤ 1) (s x : V) (N : ℕ) (hN : 0 < N)
    (hs : (N : ℂ) • s ∈ Λb) (hx : x ∈ Λb) :
    ‖ι (ε * ((Real.sqrt n' : ℝ) : ℂ)⁻¹ * β x
      * Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE H s x : ℂ)))‖ ≤ 1 := by
  have h1 : ‖ι (((Real.sqrt n' : ℝ) : ℂ)⁻¹)‖ = 1 := by
    rw [map_inv₀, norm_inv]
    have h2 : ‖ι ((Real.sqrt n' : ℝ) : ℂ)‖ ^ 2 = 1 := by
      rw [← norm_pow, ← map_pow, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _),
        Complex.ofReal_natCast, map_natCast]
      exact Formalism.L2.Th1.E.Tor.norm_natCast l hn'
    rw [(pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2, inv_one]
  have h2 : ‖ι (β x)‖ = 1 := by
    rcases hβ.1 x hx with h | h <;> simp [h]
  have h3 : ‖ι (Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE H s x : ℂ)))‖ = 1 := by
    have hs' : (N : ℂ) • s ∈ dualLat H Λb := by rw [hsd]; exact hs
    obtain ⟨m, hm⟩ := hs' x hx
    have hE : altE H ((N : ℂ) • s) x = N * altE H s x := by simp [altE]
    have hc : (N : ℂ) * (altE H s x : ℂ) = (m : ℂ) := by
      rw [hE] at hm
      exact_mod_cast hm
    have h4 : ‖ι (Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE H s x : ℂ)))‖ ^ (2 * N) = 1 := by
      rw [← norm_pow, ← map_pow, ← Complex.exp_nat_mul]
      have h5 : ((2 * N : ℕ) : ℂ) * (-(Real.pi : ℂ) * Complex.I * (altE H s x : ℂ))
          = ((-m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast
        linear_combination (-2 * (Real.pi : ℂ) * Complex.I) * hc
      rw [h5, Complex.exp_int_mul_two_pi_mul_I, map_one, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 h4
  rw [map_mul, map_mul, map_mul, norm_mul, norm_mul, norm_mul, h1, h2, h3, mul_one, mul_one, mul_one]
  exact hε

/- English proof (translation)
Establish `h1 : (N : ℂ) • (s + x) ∈ Λb`. Rewrite using `[smul_add]`. Conclude with `Λb.add_mem hs (by rw [Nat.cast_smul_eq_nsmul]; exact Λb.nsmul_mem hx N)`. Establish `h2 : relIdx (stdLat L m) Λb • ((N : ℂ) • (s + x)) ∈ stdLat L m` using `AddSubgroup.nsmul_relIndex_mem (stdLat L m) h1`. Establish `h3` using `(AddSubgroup.mem_pi _).1 h2 w (Set.mem_univ w)`.

Establish `h4 : ((N * relIdx (stdLat L m) Λb : ℕ) : ℂ) * (s w + x w) = (relIdx (stdLat L m) Λb • ((N : ℂ) • (s + x))) w`. Simplify using `only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, nsmul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h4]`.

Conclude with `h3`.
-/
theorem trans_mem (L : PeriodPair) {m : Type} (Λb : AddSubgroup (m → ℂ)) (s x : m → ℂ) (N : ℕ)
    (hs : (N : ℂ) • s ∈ Λb) (hx : x ∈ Λb) (w : m) :
    ((N * relIdx (stdLat L m) Λb : ℕ) : ℂ) * (s w + x w) ∈ L.lattice := by
  have h1 : (N : ℂ) • (s + x) ∈ Λb := by
    rw [smul_add]
    exact Λb.add_mem hs (by rw [Nat.cast_smul_eq_nsmul]; exact Λb.nsmul_mem hx N)
  have h2 : relIdx (stdLat L m) Λb • ((N : ℂ) • (s + x)) ∈ stdLat L m :=
    AddSubgroup.nsmul_relIndex_mem (stdLat L m) h1
  have h3 := (AddSubgroup.mem_pi _).1 h2 w (Set.mem_univ w)
  have h4 : ((N * relIdx (stdLat L m) Λb : ℕ) : ℂ) * (s w + x w)
      = (relIdx (stdLat L m) Λb • ((N : ℂ) • (s + x))) w := by
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  rw [h4]
  exact h3

/- English proof (translation)
Assemble the required witnesses or components as `⟨c • fun w : Fin 4 × n => t w.2, fun _ => h, by simp⟩`.
-/
theorem smul_img_mem {n : Type} [Fintype n] (Λ : AddSubgroup (n → ℂ))
    (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) (t : n → ℂ) (c : ℂ) (h : c • t ∈ Λ) :
    c • g (fun w => t w.2) ∈ imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ) :=
  ⟨c • fun w : Fin 4 × n => t w.2, fun _ => h, by simp⟩

end Arith

end FormalGroupLawNegation

open FormalGroupLawNegation

/- English proof (translation)
Introduce `l _ L ι ω₀ lg linv ph hlp hph hTI n _ _ h Λ α β g hD hln ε hε θ hθ hten t N hN hlN hNt O _ τ γ B' hB`. Take `⟨S, hS⟩` from `(hR _ (stdLat L (Fin 4 × n)) (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) hD.idx₁).1`. Establish `hNt'` using `smul_img_mem Λ g t (N : ℂ) hNt`. Establish `hF0 : AnalyticAt ℂ (opU (matH h) t θ) 0` using `hAn _ (matH h) t θ hθ.1 0 (Set.mem_univ _)`. Establish `hth : Differentiable ℂ (Formalism.L2.Th1.F.th0 L (ω₀ / 2))` using `(Formalism.L2.Th1.F.th0Basic L ω₀ hD.per hD.half).1`.

Set `M : Matrix (Fin 4 × n) (Fin 4 × n) ℂ` to `LinearMap.toMatrix' (g.symm : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ))`. Set `c : (Fin 4 × n → ℂ) → ℂ` to `fun x => ε * ((Real.sqrt (relIdx (stdLat L (Fin 4 × n)) (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))) : ℝ) : ℂ)⁻¹ * β x * Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE (stdH L (Fin 4 × n)) (g fun w => t w.2) x : ℂ))`. Set `f : (Fin 4 × n → ℂ) → Fin 4 × n → ℂ → ℂ` to `fun x w => Formalism.L2.Th1.F.opU L (g (fun w => t w.2) w + x w) (Formalism.L2.Th1.F.th0 L (ω₀ / 2))`. Establish `hf : ∀ x w, AnalyticAt ℂ (f x w) 0` using `fun x w => analyticAt_opU L _ hth`. Establish `hfun : (fun y => tens4 (opU (matH h) t θ) (M.mulVec y)) = fun y => ∑ x ∈ S, c x * prodFn (f x) y`.

Use function extensionality and compare the values at `y`. Rewrite using `[LinearMap.toMatrix'_mulVec]`. Conclude with `hA L ω₀ n h Λ α β g hD ε θ hten S hS t y`. Establish `hT : linSubst M (tensor4 (taylorMv (opU (matH h) t θ))) = ∑ x ∈ S, MvPowerSeries.C (c x) * ∏ w, at1 w (Formalism.L2.Th1.F.taylor0 (f x w))`. Rewrite using `[← hT4 n _ hF0, ← hComp _ _ M _ (analyticAt_tens4 hF0), hfun, (taylorMv_sum hLin S c _ fun x => analyticAt_prodFn (hf x)).2]`.

Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[hProd _ _ (hf x)]`. Establish `hM : ∀ (a : Fin 4) (i : n) (w : Fin 4 × n), ∑ j, B' i j * τ (γ (a, j) w) = (M.map (ι : ℂ →+* ℂ_[l])) (a, i) w`. Introduce `a i w`. Rewrite using `[hB a i w]`.

Both sides reduce to the same expression. Establish `hexp : ∀ X : PowerSeries ℂ_[l], (mvExp (-ph) : PowerSeries ℂ_[l]) * (mvExp ph * X) = X`. Introduce `X`. Rewrite using `[← mul_assoc]`. Establish `h1 : (mvExp (-ph) : PowerSeries ℂ_[l]) * mvExp ph = 1` using `Formalism.L2.Th1.C.mvExp_neg (σ := Unit) (f := ph) hph`.

Rewrite using `[h1, one_mul]`. Use `⟨{x // x ∈ S}, inferInstance, fun x => ι (c x), fun x w => (mvExp ph : PowerSeries ℂ_[l]) * (PowerSeries.map (ι : ℂ →+* ℂ_[l]) (Formalism.L2.Th1.F.taylor0 (f x w))).subst lg, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x`. Conclude with `norm_coeff ι _ _ hD.selfDual β hD.betaSemi _ hln ε hε _ _ N hN hNt' (hS.1 x x.2)`. Introduce `x w`.

Use `hTI _ (N * relIdx (stdLat L (Fin 4 × n)) (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))) (Nat.mul_pos hN (Nat.pos_of_ne_zero hD.idx₁)) ?_ (trans_mem L _ _ _ N hNt' (hS.1 x x.2) w)` and prove the remaining obligations. Introduce `hd`. Break down `(Nat.Prime.dvd_mul Fact.out).1 hd with h1 | h1` into its components or cases. Conclude with `hlN h1`. Conclude with `hln h1`.

Unfold `thetaU thetaProd`. Rewrite using `[left_side hlp τ γ B' _ hM, ← map_tensor4, ← map_linSubst, hT, map_sumProd, right_side hlp.1]`. Simplify using `only [hexp]`. Conclude with `(Finset.sum_coe_sort S fun x => MvPowerSeries.C (ι (c x)) * ∏ w, at1 w ((PowerSeries.map (ι : ℂ →+* ℂ_[l]) (Formalism.L2.Th1.F.taylor0 (f x w))).subst lg)).symm`.
-/
theorem quadraticSemicharacterIdentity_of_reformulated_of_taylorMv_of_repsExist_of_opUAnalytic (hA : quadraticSemicharacterIdentityReformulated₂) (hLin : TaylorMvLinear) (hComp : TaylorMvComp)
    (hProd : TaylorMvProd) (hT4 : TaylorMvTens4) (hR : RepsExist) (hAn : OpUAnalytic) : quadraticSemicharacterIdentity := by
  intro l _ L ι ω₀ lg linv ph hlp hph hTI n _ _ h Λ α β g hD hln ε hε θ hθ hten t N hN hlN hNt O _ τ γ B' hB
  classical
  obtain ⟨S, hS⟩ := (hR _ (stdLat L (Fin 4 × n))
    (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) hD.idx₁).1
  have hNt' := smul_img_mem Λ g t (N : ℂ) hNt

  have hF0 : AnalyticAt ℂ (opU (matH h) t θ) 0 := hAn _ (matH h) t θ hθ.1 0 (Set.mem_univ _)
  have hth : Differentiable ℂ (Formalism.L2.Th1.F.th0 L (ω₀ / 2)) := (Formalism.L2.Th1.F.th0Basic L ω₀ hD.per hD.half).1
  let M : Matrix (Fin 4 × n) (Fin 4 × n) ℂ :=
    LinearMap.toMatrix' (g.symm : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ))
  let c : (Fin 4 × n → ℂ) → ℂ := fun x =>
    ε * ((Real.sqrt (relIdx (stdLat L (Fin 4 × n))
              (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))) : ℝ) : ℂ)⁻¹ * β x
            * Complex.exp (-(Real.pi : ℂ) * Complex.I
                * (altE (stdH L (Fin 4 × n)) (g fun w => t w.2) x : ℂ))
  let f : (Fin 4 × n → ℂ) → Fin 4 × n → ℂ → ℂ := fun x w =>
    Formalism.L2.Th1.F.opU L (g (fun w => t w.2) w + x w) (Formalism.L2.Th1.F.th0 L (ω₀ / 2))
  have hf : ∀ x w, AnalyticAt ℂ (f x w) 0 := fun x w => analyticAt_opU L _ hth
  have hfun : (fun y => tens4 (opU (matH h) t θ) (M.mulVec y)) = fun y => ∑ x ∈ S, c x * prodFn (f x) y := by
    funext y
    rw [LinearMap.toMatrix'_mulVec]
    exact hA L ω₀ n h Λ α β g hD ε θ hten S hS t y
  have hT : linSubst M (tensor4 (taylorMv (opU (matH h) t θ))) =
      ∑ x ∈ S, MvPowerSeries.C (c x) * ∏ w, at1 w (Formalism.L2.Th1.F.taylor0 (f x w)) := by
    rw [← hT4 n _ hF0, ← hComp _ _ M _ (analyticAt_tens4 hF0), hfun,
      (taylorMv_sum hLin S c _ fun x => analyticAt_prodFn (hf x)).2]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hProd _ _ (hf x)]
  have hM : ∀ (a : Fin 4) (i : n) (w : Fin 4 × n),
      ∑ j, B' i j * τ (γ (a, j) w) = (M.map (ι : ℂ →+* ℂ_[l])) (a, i) w := by
    intro a i w
    rw [hB a i w]
    rfl
  have hexp : ∀ X : PowerSeries ℂ_[l], (mvExp (-ph) : PowerSeries ℂ_[l]) * (mvExp ph * X) = X := by
    intro X
    rw [← mul_assoc]
    have h1 : (mvExp (-ph) : PowerSeries ℂ_[l]) * mvExp ph = 1 :=
      Formalism.L2.Th1.C.mvExp_neg (σ := Unit) (f := ph) hph
    rw [h1, one_mul]
  refine ⟨{x // x ∈ S}, inferInstance, fun x => ι (c x), fun x w => (mvExp ph : PowerSeries ℂ_[l]) *
      (PowerSeries.map (ι : ℂ →+* ℂ_[l]) (Formalism.L2.Th1.F.taylor0 (f x w))).subst lg, ?_, ?_, ?_⟩
  · intro x
    exact norm_coeff ι _ _ hD.selfDual β hD.betaSemi _ hln ε hε _ _ N hN hNt' (hS.1 x x.2)
  · intro x w
    refine hTI _ (N * relIdx (stdLat L (Fin 4 × n))
      (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))) (Nat.mul_pos hN (Nat.pos_of_ne_zero hD.idx₁)) ?_
      (trans_mem L _ _ _ N hNt' (hS.1 x x.2) w)
    intro hd
    rcases (Nat.Prime.dvd_mul Fact.out).1 hd with h1 | h1
    · exact hlN h1
    · exact hln h1
  · unfold thetaU thetaProd
    rw [left_side hlp τ γ B' _ hM, ← map_tensor4, ← map_linSubst, hT, map_sumProd, right_side hlp.1]
    simp only [hexp]
    exact (Finset.sum_coe_sort S fun x => MvPowerSeries.C (ι (c x)) * ∏ w, at1 w
      ((PowerSeries.map (ι : ℂ →+* ℂ_[l]) (Formalism.L2.Th1.F.taylor0 (f x w))).subst lg)).symm

/- English proof (translation)
The claim follows from `quadraticSemicharacterIdentity_of_reformulated_of_taylorMv_of_repsExist_of_opUAnalytic hA hLin hComp hProd hT4 cosetRepsExist heisenbergAnalytic`.
-/
theorem quadraticSemicharacters_of_taylor_mv (hA : quadraticSemicharacterIdentityReformulated₂) (hLin : TaylorMvLinear) (hComp : TaylorMvComp)
    (hProd : TaylorMvProd) (hT4 : TaylorMvTens4) : quadraticSemicharacterIdentity :=
  quadraticSemicharacterIdentity_of_reformulated_of_taylorMv_of_repsExist_of_opUAnalytic hA hLin hComp hProd hT4 cosetRepsExist heisenbergAnalytic

/- English proof (translation)
Introduce `l _ L ι ω₀ lg linv ph R hR hFr hTI O _ _ τ hEnd hBin hF1 hNm hAd n _ _ h Λ α β g hD hln ε hε θ hθ hten t N hN hlN hNt γ B' hγ hB`. Conclude with `Formalism.L2.Th1.E.generalIntOf ℂ_[l] R hR lg linv ph hFr O τ hEnd hBin hF1 hNm hAd n _ γ hγ (hK l L ι ω₀ lg linv ph hFr.1 hFr.2.2 hTI n h Λ α β g hD hln ε hε θ hθ hten t N hN hlN hNt O τ γ B' hB)`.
-/
theorem ThetaIntegral_of (hK : quadraticSemicharacterIdentity) : ThetaIntegral := by
  intro l _ L ι ω₀ lg linv ph R hR hFr hTI O _ _ τ hEnd hBin hF1 hNm hAd n _ _ h Λ α β g hD hln ε hε θ hθ hten
    t N hN hlN hNt γ B' hγ hB
  exact Formalism.L2.Th1.E.generalIntOf ℂ_[l] R hR lg linv ph hFr O τ hEnd hBin hF1 hNm hAd n _ γ hγ
    (hK l L ι ω₀ lg linv ph hFr.1 hFr.2.2 hTI n h Λ α β g hD hln ε hε θ hθ hten t N hN hlN hNt O τ γ B' hB)

end Formalism.L2.Th1.H
