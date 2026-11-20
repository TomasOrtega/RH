import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictHomApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPurePairIffMonodromyFiltration
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.PrimDecomp GlobalTheory.LocLanglands

noncomputable section

open TensorProduct Module

namespace GlobalTheory.WeilDeligne.PrimDecomp

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/- English proof (translation)
Establish `hq : (1 : ℝ) < ((normV w : ℕ) : ℝ)` using `by exact_mod_cast one_lt_normV w`. Establish `hq0` using `zero_lt_one.trans hq`. It suffices to establish `H : wtSpace a d ≤ Submodule.comap a.N (wtSpace a (d + 2)) from H hv`. Use `iSup₂_le fun α hα v hv => Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem ?_ (a.map_N_eigenspace deg_frob hv))` and prove the remaining obligations. Rewrite using `[norm_mul, hα, Complex.norm_natCast, show (((d + 2 : ℤ) : ℝ) / 2) = 1 + (d : ℝ) / 2 by push_cast; ring, Real.rpow_add hq0, Real.rpow_one]`.
-/
theorem N_mem_wtSpace (a : WDRep h V) {d : ℤ} {v : V} (hv : v ∈ wtSpace a d) :
    a.N v ∈ wtSpace a (d + 2) := by
  have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
  have hq0 := zero_lt_one.trans hq
  suffices H : wtSpace a d ≤ Submodule.comap a.N (wtSpace a (d + 2)) from H hv
  refine iSup₂_le fun α hα v hv => Submodule.mem_iSup_of_mem _
    (Submodule.mem_iSup_of_mem ?_ (a.map_N_eigenspace deg_frob hv))
  rw [norm_mul, hα, Complex.norm_natCast, show (((d + 2 : ℤ) : ℝ) / 2) = 1 + (d : ℝ) / 2 by
    push_cast; ring, Real.rpow_add hq0, Real.rpow_one]

/- English proof (translation)
Establish `hq : (1 : ℝ) < ((normV w : ℕ) : ℝ)` using `by exact_mod_cast one_lt_normV w`. Establish `hq0` using `zero_lt_one.trans hq`. Use `iSupIndep_absSpace (r := fun i : ℤ => ((normV w : ℕ) : ℝ) ^ ((i : ℝ) / 2)) _ fun i j hij => ?_` and prove the remaining obligations. Simplify using `only at hij`. Rewrite `hij` using `[Real.rpow_right_inj hq0 hq.ne']`.

Conclude with `(by linarith : (i : ℝ) = j)` after adjusting the coercions.
-/
theorem iSupIndep_wtSpace (a : WDRep h V) : iSupIndep (wtSpace a) := by
  have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
  have hq0 := zero_lt_one.trans hq
  refine iSupIndep_absSpace (r := fun i : ℤ => ((normV w : ℕ) : ℝ) ^ ((i : ℝ) / 2)) _
    fun i j hij => ?_
  simp only at hij
  rw [Real.rpow_right_inj hq0 hq.ne'] at hij
  exact_mod_cast (by linarith : (i : ℝ) = j)

/- English proof (translation)
Proceed by induction on `j generalizing v with`. Consider the case `zero => simp`. Consider the case `succ j ih`. Simplify using `only [pow_succ', End.mul_apply, a.comm_apply, ih, map_smul, smul_smul]`.
-/
theorem ρ_pow_N (a : WDRep h V) (σ : Weil h) (j : ℕ) (v : V) :
    a.ρ σ ((a.N ^ j) v) = (((normV w : ℕ) : ℂ) ^ deg σ) ^ j • (a.N ^ j) (a.ρ σ v) := by
  induction j generalizing v with
  | zero => simp
  | succ j ih =>
    simp only [pow_succ', End.mul_apply, a.comm_apply, ih, map_smul, smul_smul]

/- English proof (translation)
Rewrite using `[WDRep.spEig, ← Units.val_mul, ← qPow_add, show (((j : ℕ) : ℝ) - (((m + 1 : ℕ) : ℝ) - 1) / 2 + (m : ℝ) / 2) = ((j : ℕ) : ℝ) by push_cast; ring, coe_qPow, Complex.ofReal_natCast, Complex.cpow_natCast]`.
-/
theorem spEig_mul_qPow (m : ℕ) (j : Fin (m + 1)) :
    (WDRep.spEig w (m + 1) j : ℂ) * (qPow w ((m : ℝ) / 2) : ℂ) = ((normV w : ℕ) : ℂ) ^ (j : ℕ) := by
  rw [WDRep.spEig, ← Units.val_mul, ← qPow_add,
    show (((j : ℕ) : ℝ) - (((m + 1 : ℕ) : ℝ) - 1) / 2 + (m : ℝ) / 2) = ((j : ℕ) : ℝ) by
      push_cast; ring, coe_qPow, Complex.ofReal_natCast, Complex.cpow_natCast]

end GlobalTheory.WeilDeligne.PrimDecomp

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A w h V _ _ _ a m hS hB ht htop`. Use `set U := wtSpace a (-(m : ℤ)) with hU`. Establish `hpure` using `ht (frob h) deg_frob`. Establish `hb : ∀ i : ℕ, Set.BijOn (a.N ^ i) (wtSpace a (-(i : ℤ))) (wtSpace a (i : ℤ))`. Introduce `i`.

Use `hpure.2 i` as an intermediate fact. Simplify `this` using `[wtSpace, neg_div]`. Establish `hN2 : ∀ d, ∀ v ∈ wtSpace a d, a.N v ∈ wtSpace a (d + 2)` using `fun d v hv => N_mem_wtSpace a hv`. Establish `hkill : ∀ u ∈ U, (a.N ^ (m + 1)) u = 0`. Introduce `u hu`.

Use `pow_mem_of_degree_two hN2 (m + 1) (e := (m : ℤ) + 2) (by push_cast; ring) hu` as an intermediate fact. Rewrite `this` using `[htop _ (by omega), Submodule.mem_bot]`. Then use the resulting hypothesis. Set `Φ : (Fin (m + 1) → U) →ₗ[ℂ] V` to `∑ j : Fin (m + 1), (a.N ^ (j : ℕ)) ∘ₗ U.subtype ∘ₗ LinearMap.proj j`. Establish `hΦ : ∀ f, Φ f = ∑ j : Fin (m + 1), (a.N ^ (j : ℕ)) (f j : V)` using `by intro f; simp [Φ]`. Establish `hinj : Function.Injective Φ`.

Rewrite using `[← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]`. Introduce `f hf`. Rewrite `hf` using `[LinearMap.mem_ker, hΦ]`. Establish `hi : Function.Injective fun j : Fin (m + 1) => -(m : ℤ) + 2 * ((j : ℕ) : ℤ)`. Introduce `i j hij`.

Simplify using `only at hij`. Conclude with `Fin.ext (by omega)`. Establish `hind` using `(iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp ((iSupIndep_wtSpace a).comp hi) Finset.univ (fun j => (a.N ^ (j : ℕ)) (f j : V)) (fun j _ => pow_mem_of_degree_two hN2 j rfl (f j).2) hf`. Use function extensionality and compare the values at `j`. Apply `Subtype.ext` to reduce the goal to its premises.

Conclude with `eq_zero_of_pow_eq_zero hb (d := -(m : ℤ)) (m := j) (by omega) (f j).2 (hind j (Finset.mem_univ _))`. Establish `hrange : LinearMap.range Φ = strand a.N U m`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨f, rfl⟩`. Rewrite using `[hΦ]`.

Conclude with `Submodule.sum_mem _ fun j _ => Submodule.mem_iSup_of_mem j ⟨f j, (f j).2, rfl⟩`. Use `iSup_le fun j => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨u, hu, rfl⟩`. Use `⟨Pi.single j ⟨u, hu⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hΦ, Finset.sum_eq_single j (fun k _ hk => by simp [Pi.single_eq_of_ne hk]) (by simp)]`.

Simplify using the standard rewrite rules. Set `eT : U ⊗[ℂ] (Fin (m + 1) → ℂ) ≃ₗ[ℂ] strand a.N U m` to `(TensorProduct.piScalarRight ℂ ℂ U (Fin (m + 1))).trans ((LinearEquiv.ofInjective Φ hinj).trans (LinearEquiv.ofEq _ _ hrange))`. Establish `heT : ∀ (x : U) (c : Fin (m + 1) → ℂ), (eT (x ⊗ₜ c) : V) = ∑ j : Fin (m + 1), c j • (a.N ^ (j : ℕ)) (x : V)`. Introduce `x c`. Simplify using `[eT, hΦ, TensorProduct.piScalarRightHom_tmul]`.

Rewrite using `[WD.lpTw_mk, WD.lpSp, WD.lpChar_mk]`. Use `WD.sound (WDRep.Iso.symm ⟨eT, fun σ t => Subtype.ext ?_, fun t => Subtype.ext ?_⟩)` and prove the remaining obligations. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, Submodule.coe_add, hx, hy]`.

Consider the case `tmul x c`. Rewrite using `[WDRep.tensor_ρ, TensorProduct.map_tmul, heT, restrict_ρ_apply, heT, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[WDRep.sp_ρ, diagEnd_apply, WDRep.tw_ρ, LinearMap.smul_apply, Submodule.coe_smul, restrictρ_ρ_apply, map_smul, map_smul, ρ_pow_N, smul_smul, smul_smul]`. Use `congr 1`.

Establish `key : (WDRep.spEig w (m + 1) j : ℂ) ^ deg σ * (qPow w ((m : ℝ) / 2) : ℂ) ^ deg σ = (((normV w : ℕ) : ℂ) ^ deg σ) ^ (j : ℕ)`. Rewrite using `[← mul_zpow, spEig_mul_qPow, ← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul, mul_comm]`. Rewrite using `[← key, coe_qPow]`. Expand and normalize the polynomial expressions, which then agree. Proceed by induction on `t using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, Submodule.coe_add, hx, hy]`. Consider the case `tmul x c`. Establish `hNs : ∀ (k : ℕ) (y : V), a.N ((a.N ^ k) y) = (a.N ^ (k + 1)) y` using `fun k y => by`. Rewrite using `[pow_succ', End.mul_apply]`.

Rewrite using `[WDRep.tensor_N, LinearMap.add_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, WDRep.tw_N, restrictρ_N, LinearMap.zero_apply, zero_tmul, zero_add, heT, restrict_N_apply, heT, map_sum]`. Simplify using `only [map_smul, hNs, WDRep.sp_N]`. Rewrite using `[Fin.sum_univ_succ, Fin.sum_univ_castSucc]`. Simplify using `[shiftEnd_apply, hkill x x.2]`. Conclude with `Finset.sum_congr rfl fun i _ => rfl`.
-/
theorem GlobalTheory.WeilDeligne.PrimDecomp.mk_restrict_strand_eq : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V) (m : ℕ) (hS : ∀ σ, ∀ v ∈ wtSpace a (-(m : ℤ)), a.ρ σ v ∈ wtSpace a (-(m : ℤ))) (hB : IsSubWD a (strand a.N (wtSpace a (-(m : ℤ))) m)), a.Tempered → (∀ k : ℤ, (m : ℤ) < k → wtSpace a k = ⊥) → WD.mk (restrict a _ hB) = ((WD.mk (restrictρ a _ hS)).lpTw ((m : ℝ) / 2)).lpChar (WD.lpSp h (m + 1)) := by
  intro E Ω _ _ _ _ _ A w h V _ _ _ a m hS hB ht htop
  set U := wtSpace a (-(m : ℤ)) with hU
  have hpure := ht (frob h) deg_frob
  have hb : ∀ i : ℕ, Set.BijOn (a.N ^ i) (wtSpace a (-(i : ℤ))) (wtSpace a (i : ℤ)) := by
    intro i
    have := hpure.2 i
    simpa [wtSpace, neg_div] using this
  have hN2 : ∀ d, ∀ v ∈ wtSpace a d, a.N v ∈ wtSpace a (d + 2) := fun d v hv => N_mem_wtSpace a hv
  have hkill : ∀ u ∈ U, (a.N ^ (m + 1)) u = 0 := by
    intro u hu
    have := pow_mem_of_degree_two hN2 (m + 1) (e := (m : ℤ) + 2) (by push_cast; ring) hu
    rwa [htop _ (by omega), Submodule.mem_bot] at this
  let Φ : (Fin (m + 1) → U) →ₗ[ℂ] V :=
    ∑ j : Fin (m + 1), (a.N ^ (j : ℕ)) ∘ₗ U.subtype ∘ₗ LinearMap.proj j
  have hΦ : ∀ f, Φ f = ∑ j : Fin (m + 1), (a.N ^ (j : ℕ)) (f j : V) := by intro f; simp [Φ]
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro f hf
    rw [LinearMap.mem_ker, hΦ] at hf
    have hi : Function.Injective fun j : Fin (m + 1) => -(m : ℤ) + 2 * ((j : ℕ) : ℤ) := by
      intro i j hij
      simp only at hij
      exact Fin.ext (by omega)
    have hind := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp
      ((iSupIndep_wtSpace a).comp hi) Finset.univ (fun j => (a.N ^ (j : ℕ)) (f j : V))
      (fun j _ => pow_mem_of_degree_two hN2 j rfl (f j).2) hf
    funext j
    apply Subtype.ext
    exact eq_zero_of_pow_eq_zero hb (d := -(m : ℤ)) (m := j) (by omega) (f j).2
      (hind j (Finset.mem_univ _))
  have hrange : LinearMap.range Φ = strand a.N U m := by
    apply le_antisymm
    · rintro _ ⟨f, rfl⟩
      rw [hΦ]
      exact Submodule.sum_mem _ fun j _ => Submodule.mem_iSup_of_mem j ⟨f j, (f j).2, rfl⟩
    · refine iSup_le fun j => ?_
      rintro _ ⟨u, hu, rfl⟩
      refine ⟨Pi.single j ⟨u, hu⟩, ?_⟩
      rw [hΦ, Finset.sum_eq_single j (fun k _ hk => by simp [Pi.single_eq_of_ne hk]) (by simp)]
      simp
  let eT : U ⊗[ℂ] (Fin (m + 1) → ℂ) ≃ₗ[ℂ] strand a.N U m :=
    (TensorProduct.piScalarRight ℂ ℂ U (Fin (m + 1))).trans
      ((LinearEquiv.ofInjective Φ hinj).trans (LinearEquiv.ofEq _ _ hrange))
  have heT : ∀ (x : U) (c : Fin (m + 1) → ℂ),
      (eT (x ⊗ₜ c) : V) = ∑ j : Fin (m + 1), c j • (a.N ^ (j : ℕ)) (x : V) := by
    intro x c
    simp [eT, hΦ, TensorProduct.piScalarRightHom_tmul]
  rw [WD.lpTw_mk, WD.lpSp, WD.lpChar_mk]
  refine WD.sound (WDRep.Iso.symm ⟨eT, fun σ t => Subtype.ext ?_, fun t => Subtype.ext ?_⟩)
  · induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, Submodule.coe_add, hx, hy]
    | tmul x c =>
      rw [WDRep.tensor_ρ, TensorProduct.map_tmul, heT, restrict_ρ_apply, heT, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [WDRep.sp_ρ, diagEnd_apply, WDRep.tw_ρ, LinearMap.smul_apply, Submodule.coe_smul,
        restrictρ_ρ_apply, map_smul, map_smul, ρ_pow_N, smul_smul, smul_smul]
      congr 1
      have key : (WDRep.spEig w (m + 1) j : ℂ) ^ deg σ * (qPow w ((m : ℝ) / 2) : ℂ) ^ deg σ =
          (((normV w : ℕ) : ℂ) ^ deg σ) ^ (j : ℕ) := by
        rw [← mul_zpow, spEig_mul_qPow, ← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul,
          mul_comm]
      rw [← key, coe_qPow]
      ring
  · induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, Submodule.coe_add, hx, hy]
    | tmul x c =>
      have hNs : ∀ (k : ℕ) (y : V), a.N ((a.N ^ k) y) = (a.N ^ (k + 1)) y := fun k y => by
        rw [pow_succ', End.mul_apply]
      rw [WDRep.tensor_N, LinearMap.add_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
        WDRep.tw_N, restrictρ_N, LinearMap.zero_apply, zero_tmul, zero_add, heT,
        restrict_N_apply, heT, map_sum]
      simp only [map_smul, hNs, WDRep.sp_N]
      rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
      simp [shiftEnd_apply, hkill x x.2]
      exact Finset.sum_congr rfl fun i _ => rfl
