import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusTateGaloisActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePointsFixedFrobeniusPowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TlLevSurjKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleFreeFinrankTwoMulDim

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.AbVar

variable {K : Type} [Field K] [Fintype K]

local notation "Fr" K => FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)

/- English proof (translation)
Use `haveI := (prod A B).smooth`. Use `haveI : Smooth (prod A B).X.hom := SmoothOfRelativeDimension.smooth (prod A B).dim (prod A B).X.hom`. Take `⟨m, hm⟩` from `GlobalTheory.T.finite_points_fixed_frobenius_power K σ (prod A B).X ({lift x y} : Finset (ptOver K (AlgebraicClosure K) ⟶ (prod A B).X)) inferInstance`. Establish `h : specAut σ ≫ (lift x y : ptOver K (AlgebraicClosure K) ⟶ A.X ⊗ B.X) = specAut ((Fr K) ^ m) ≫ lift x y` using `hm (lift x y) (Finset.mem_singleton_self _)`. Use `⟨m, ?_, ?_⟩` and prove the remaining obligations.

Use `congrArg (fun f => f ≫ fst A.X B.X) h` as an intermediate fact. Simplify using `only [Category.assoc, lift_fst] at this`. Conclude with `this`. Use `congrArg (fun f => f ≫ snd A.X B.X) h` as an intermediate fact. Simplify using `only [Category.assoc, lift_snd] at this`.

Conclude with `this`.
-/
theorem exists_frob_pow_pair (σ : Gal K) (A B : AbVar K) (x : A.Pt) (y : B.Pt) :
    ∃ m : ℕ, specAut σ ≫ x = specAut ((Fr K) ^ m) ≫ x ∧ specAut σ ≫ y = specAut ((Fr K) ^ m) ≫ y := by
  haveI := (prod A B).smooth
  haveI : Smooth (prod A B).X.hom := SmoothOfRelativeDimension.smooth (prod A B).dim (prod A B).X.hom
  obtain ⟨m, hm⟩ := GlobalTheory.T.finite_points_fixed_frobenius_power K σ (prod A B).X
    ({lift x y} : Finset (ptOver K (AlgebraicClosure K) ⟶ (prod A B).X)) inferInstance
  have h : specAut σ ≫ (lift x y : ptOver K (AlgebraicClosure K) ⟶ A.X ⊗ B.X) =
      specAut ((Fr K) ^ m) ≫ lift x y := hm (lift x y) (Finset.mem_singleton_self _)
  refine ⟨m, ?_, ?_⟩
  · have := congrArg (fun f => f ≫ fst A.X B.X) h
    simp only [Category.assoc, lift_fst] at this
    exact this
  · have := congrArg (fun f => f ≫ snd A.X B.X) h
    simp only [Category.assoc, lift_snd] at this
    exact this

variable (l : ℕ) [Fact l.Prime]

/- English proof (translation)
Rewrite using `[← (tl_lev_surj_ker K l A n).2]`. Express the relevant statement in the definitionally equal form `_ ↔ u.lev n * (v.lev n)⁻¹ = 1`. Rewrite using `[mul_inv_eq_one]`.
-/
theorem lev_eq_iff_exists_sub (A : AbVar K) (u v : Tl l A) (n : ℕ) :
    u.lev n = v.lev n ↔ ∃ s : Tl l A, u - v = (l : ℤ_[l]) ^ n • s := by
  rw [← (tl_lev_surj_ker K l A n).2]
  change _ ↔ u.lev n * (v.lev n)⁻¹ = 1
  rw [mul_inv_eq_one]

/- English proof (translation)
Take `⟨s, hs⟩` from `(lev_eq_iff_exists_sub l A u v n).1 h`. Conclude with `(lev_eq_iff_exists_sub l B _ _ n).2 ⟨φ s, by rw [← map_sub, hs, map_smul]⟩`.
-/
theorem lev_linearMap_eq {A B : AbVar K} (φ : Tl l A →ₗ[ℤ_[l]] Tl l B) {u v : Tl l A} {n : ℕ}
    (h : u.lev n = v.lev n) : (φ u).lev n = (φ v).lev n := by
  obtain ⟨s, hs⟩ := (lev_eq_iff_exists_sub l A u v n).1 h
  exact (lev_eq_iff_exists_sub l B _ _ n).2 ⟨φ s, by rw [← map_sub, hs, map_smul]⟩

/- English proof (translation)
Rewrite using `[(GlobalTheory.T.frobenius_tate_galois_action K l A).1, (GlobalTheory.T.frobenius_tate_galois_action K l B).1]`. Use `⟨fun h => h _, fun h σ => ?_⟩` and prove the remaining obligations. Use `LinearMap.ext fun t => Tate.ext fun n => ?_` and prove the remaining obligations. Take `⟨m, hx, hy⟩` from `exists_frob_pow_pair σ A B (t.lev n) ((φ t).lev n)`. Establish `hc` using `LinearMap.congr_fun (Module.End.commute_pow_left_of_commute h.symm m) t`.

Rewrite `hc` using `[← map_pow, ← map_pow]`. Simplify using `only [LinearMap.comp_apply] at hc ⊢`. Express the relevant statement in the definitionally equal form `(φ (galT l A σ t)).lev n = specAut σ ≫ (φ t).lev n`. Rewrite using `[hy, lev_linearMap_eq l φ (u := galT l A σ t) (v := galT l A ((Fr K) ^ m) t) hx, ← hc]`. Both sides reduce to the same expression.
-/
theorem mem_galHomT_iff (A B : AbVar K) (φ : Tl l A →ₗ[ℤ_[l]] Tl l B) :
    φ ∈ galHomT l A B ↔ φ ∘ₗ tend l A (frob A) = tend l B (frob B) ∘ₗ φ := by
  rw [(GlobalTheory.T.frobenius_tate_galois_action K l A).1, (GlobalTheory.T.frobenius_tate_galois_action K l B).1]
  refine ⟨fun h => h _, fun h σ => ?_⟩
  refine LinearMap.ext fun t => Tate.ext fun n => ?_
  obtain ⟨m, hx, hy⟩ := exists_frob_pow_pair σ A B (t.lev n) ((φ t).lev n)
  have hc := LinearMap.congr_fun (Module.End.commute_pow_left_of_commute h.symm m) t
  rw [← map_pow, ← map_pow] at hc
  simp only [LinearMap.comp_apply] at hc ⊢
  change (φ (galT l A σ t)).lev n = specAut σ ≫ (φ t).lev n
  rw [hy, lev_linearMap_eq l φ (u := galT l A σ t) (v := galT l A ((Fr K) ^ m) t) hx, ← hc]
  rfl

/- English proof (translation)
Rewrite `hW` using `[(GlobalTheory.T.frobenius_tate_galois_action K l A).1]`. Establish `hWm : ∀ m : ℕ, ∀ t ∈ W, galT l A ((Fr K) ^ m) t ∈ W`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro t ht`.

Simplify using `using ht`. Consider the case `succ m ih => intro t ht`. Rewrite using `[pow_succ, map_mul, Module.End.mul_apply]`. Conclude with `ih _ (hW _ ht)`. Use `haveI := (tl_free_finrank K l hl A).2.1`.

Establish `key : ∀ n : ℕ, W.mkQ (galT l A σ t) ∈ (IsLocalRing.maximalIdeal ℤ_[l]) ^ n • (⊤ : Submodule ℤ_[l] (Tl l A ⧸ W))`. Introduce `n`. Take `⟨m, hx, -⟩` from `exists_frob_pow_pair σ A A (t.lev n) (t.lev n)`. Take `⟨s, hs⟩` from `(lev_eq_iff_exists_sub l A (galT l A σ t) (galT l A ((Fr K) ^ m) t) n).1 hx`. Establish `e : W.mkQ (galT l A σ t) = (l : ℤ_[l]) ^ n • W.mkQ s`.

Rewrite using `[← map_smul, ← hs, map_sub, Submodule.mkQ_apply W (galT l A ((Fr K) ^ m) t), (Submodule.Quotient.mk_eq_zero W).2 (hWm m t ht), sub_zero]`. Rewrite using `[e]`. Use `Submodule.smul_mem_smul (Ideal.pow_mem_pow ?_ n) Submodule.mem_top` and prove the remaining obligations. Rewrite using `[PadicInt.maximalIdeal_eq_span_p]`. Conclude with `Ideal.mem_span_singleton_self _`.

Establish `h0` using `Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := Tl l A ⧸ W) _ (IsLocalRing.maximalIdeal.isMaximal ℤ_[l]).ne_top`. Establish `h1 : W.mkQ (galT l A σ t) ∈ (⊥ : Submodule ℤ_[l] (Tl l A ⧸ W))` using `h0 ▸ Submodule.mem_iInf _ |>.2 key`. Rewrite `h1` using `[Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Then use the resulting hypothesis.
-/
theorem galT_mem_of_frob (hl : (l : K) ≠ 0) (A : AbVar K) (W : Submodule ℤ_[l] (Tl l A))
    (hW : ∀ t ∈ W, tend l A (frob A) t ∈ W) (σ : Gal K) (t : Tl l A) (ht : t ∈ W) : galT l A σ t ∈ W := by
  rw [(GlobalTheory.T.frobenius_tate_galois_action K l A).1] at hW
  have hWm : ∀ m : ℕ, ∀ t ∈ W, galT l A ((Fr K) ^ m) t ∈ W := by
    intro m
    induction m with
    | zero => intro t ht; simpa using ht
    | succ m ih => intro t ht; rw [pow_succ, map_mul, Module.End.mul_apply]; exact ih _ (hW _ ht)
  haveI := (tl_free_finrank K l hl A).2.1
  have key : ∀ n : ℕ, W.mkQ (galT l A σ t) ∈
      (IsLocalRing.maximalIdeal ℤ_[l]) ^ n • (⊤ : Submodule ℤ_[l] (Tl l A ⧸ W)) := by
    intro n
    obtain ⟨m, hx, -⟩ := exists_frob_pow_pair σ A A (t.lev n) (t.lev n)
    obtain ⟨s, hs⟩ := (lev_eq_iff_exists_sub l A (galT l A σ t) (galT l A ((Fr K) ^ m) t) n).1 hx
    have e : W.mkQ (galT l A σ t) = (l : ℤ_[l]) ^ n • W.mkQ s := by
      rw [← map_smul, ← hs, map_sub, Submodule.mkQ_apply W (galT l A ((Fr K) ^ m) t),
        (Submodule.Quotient.mk_eq_zero W).2 (hWm m t ht), sub_zero]
    rw [e]
    refine Submodule.smul_mem_smul (Ideal.pow_mem_pow ?_ n) Submodule.mem_top
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  have h0 := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := Tl l A ⧸ W) _
    (IsLocalRing.maximalIdeal.isMaximal ℤ_[l]).ne_top
  have h1 : W.mkQ (galT l A σ t) ∈ (⊥ : Submodule ℤ_[l] (Tl l A ⧸ W)) := h0 ▸ Submodule.mem_iInf _ |>.2 key
  rwa [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1

abbrev tv (A : AbVar K) : Tl l A →ₗ[ℤ_[l]] Vl l A := TensorProduct.mk ℤ_[l] ℚ_[l] (Tl l A) 1

instance isLocalizedModule_tv (A : AbVar K) : IsLocalizedModule (nonZeroDivisors ℤ_[l]) (tv l A) := by
  rw [isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ_[l]) ℚ_[l]]
  exact TensorProduct.isBaseChange _ _ _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem galV_tv (A : AbVar K) (σ : Gal K) (t : Tl l A) : galV l A σ (tv l A t) = tv l A (galT l A σ t) := rfl

/- English proof (translation)
Take `⟨⟨t, s⟩, rfl⟩` from `IsLocalizedModule.mk'_surjective (nonZeroDivisors ℤ_[l]) (tv l A) w`. Use `⟨algebraMap ℤ_[l] ℚ_[l] s, t, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Conclude with `nonZeroDivisors.coe_ne_zero s ((IsFractionRing.injective ℤ_[l] ℚ_[l]).eq_iff' (map_zero _) |>.1 h)`. Rewrite using `[algebraMap_smul]`.

Conclude with `IsLocalizedModule.mk'_cancel' (tv l A) t s`.
-/
theorem exists_smul_eq_tv (A : AbVar K) (w : Vl l A) : ∃ (c : ℚ_[l]) (t : Tl l A), c ≠ 0 ∧ c • w = tv l A t := by
  obtain ⟨⟨t, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective (nonZeroDivisors ℤ_[l]) (tv l A) w
  refine ⟨algebraMap ℤ_[l] ℚ_[l] s, t, ?_, ?_⟩
  · intro h
    exact nonZeroDivisors.coe_ne_zero s ((IsFractionRing.injective ℤ_[l] ℚ_[l]).eq_iff' (map_zero _) |>.1 h)
  · rw [algebraMap_smul]
    exact IsLocalizedModule.mk'_cancel' (tv l A) t s

/- English proof (translation)
Use `haveI := (tl_free_finrank K l hl A).1`. Introduce `u v h`. Take `⟨c, hc⟩` from `(IsLocalizedModule.eq_iff_exists (nonZeroDivisors ℤ_[l]) (tv l A)).1 h`. Conclude with `smul_right_injective (Tl l A) (nonZeroDivisors.coe_ne_zero c) hc`.
-/
theorem tv_injective (hl : (l : K) ≠ 0) (A : AbVar K) : Function.Injective (tv l A) := by
  haveI := (tl_free_finrank K l hl A).1
  intro u v h
  obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_iff_exists (nonZeroDivisors ℤ_[l]) (tv l A)).1 h
  exact smul_right_injective (Tl l A) (nonZeroDivisors.coe_ne_zero c) hc

/- English proof (translation)
Rewrite `hW` using `[(GlobalTheory.T.frobenius_tate_galois_action K l A).2]`. Set `W0 : Submodule ℤ_[l] (Tl l A)` to `(W.restrictScalars ℤ_[l]).comap (tv l A)`. Take `⟨c, t, hc, hct⟩` from `exists_smul_eq_tv l A w`. Establish `ht : t ∈ W0`. Express the relevant statement in the definitionally equal form `tv l A t ∈ W`.

Rewrite using `[← hct]`. Conclude with `W.smul_mem c hw`. Establish `hσ : galT l A σ t ∈ W0`. Use `galT_mem_of_frob l hl A W0 (fun u hu => ?_) σ t ht` and prove the remaining obligations. Rewrite using `[(GlobalTheory.T.frobenius_tate_galois_action K l A).1]`.

Express the relevant statement in the definitionally equal form `tv l A (galT l A (Fr K) u) ∈ W`. Rewrite using `[← galV_tv]`. Conclude with `hW _ hu`. Establish `h1 : c • galV l A σ w ∈ W`. Rewrite using `[← map_smul, hct, galV_tv]`.

Conclude with `hσ`. Establish `h2` using `W.smul_mem c⁻¹ h1`. Rewrite `h2` using `[smul_smul, inv_mul_cancel₀ hc, one_smul]`. Then use the resulting hypothesis.
-/
theorem galV_mem_of_frob (hl : (l : K) ≠ 0) (A : AbVar K) (W : Submodule ℚ_[l] (Vl l A))
    (hW : ∀ t ∈ W, vend l A (toEnd0 A (frob A)) t ∈ W) (σ : Gal K) (w : Vl l A) (hw : w ∈ W) :
    galV l A σ w ∈ W := by
  rw [(GlobalTheory.T.frobenius_tate_galois_action K l A).2] at hW
  let W0 : Submodule ℤ_[l] (Tl l A) := (W.restrictScalars ℤ_[l]).comap (tv l A)
  obtain ⟨c, t, hc, hct⟩ := exists_smul_eq_tv l A w
  have ht : t ∈ W0 := by
    change tv l A t ∈ W
    rw [← hct]
    exact W.smul_mem c hw
  have hσ : galT l A σ t ∈ W0 := by
    refine galT_mem_of_frob l hl A W0 (fun u hu => ?_) σ t ht
    rw [(GlobalTheory.T.frobenius_tate_galois_action K l A).1]
    change tv l A (galT l A (Fr K) u) ∈ W
    rw [← galV_tv]
    exact hW _ hu
  have h1 : c • galV l A σ w ∈ W := by
    rw [← map_smul, hct, galV_tv]
    exact hσ
  have h2 := W.smul_mem c⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h2

/- English proof (translation)
Rewrite using `[(GlobalTheory.T.frobenius_tate_galois_action K l A).2, (GlobalTheory.T.frobenius_tate_galois_action K l B).2]`. Use `⟨fun h => h _, fun h σ => ?_⟩` and prove the remaining obligations. Use `haveI := (tl_free_finrank K l hl A).2.1`. Use `haveI := (tl_free_finrank K l hl A).1`. Use `haveI : Module.FinitePresentation ℤ_[l] (Tl l A) := Module.finitePresentation_of_projective _ _`.

Take `⟨ψ, s, hψ⟩` from `Module.FinitePresentation.exists_lift_of_isLocalizedModule (nonZeroDivisors ℤ_[l]) (tv l B) ((φ.restrictScalars ℤ_[l]) ∘ₗ tv l A)`. Use `set c : ℚ_[l] := algebraMap ℤ_[l] ℚ_[l] s with hcdef`. Establish `hc : c ≠ 0` using `fun e => nonZeroDivisors.coe_ne_zero s ((IsFractionRing.injective ℤ_[l] ℚ_[l]).eq_iff' (map_zero _) |>.1 e)`. Establish `hψt : ∀ t, tv l B (ψ t) = c • φ (tv l A t)` using `fun t => by`. Use `LinearMap.congr_fun hψ t` as an intermediate fact.

Rewrite `this` using `[LinearMap.comp_apply]`. Rewrite using `[this, LinearMap.smul_apply, Submonoid.smul_def, ← algebraMap_smul ℚ_[l] (s : ℤ_[l])]`. Both sides reduce to the same expression. Establish `hF : ψ ∘ₗ galT l A (Fr K) = galT l B (Fr K) ∘ₗ ψ`. Use `LinearMap.ext fun t => tv_injective l hl B ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, hψt, ← galV_tv, ← galV_tv, hψt, map_smul]`. Use `congr 1`. Conclude with `LinearMap.congr_fun h (tv l A t)`. Establish `hσ : ψ ∘ₗ galT l A σ = galT l B σ ∘ₗ ψ`. Use `(mem_galHomT_iff l A B ψ).2 ?_ σ` and prove the remaining obligations.

Rewrite using `[(GlobalTheory.T.frobenius_tate_galois_action K l A).1, (GlobalTheory.T.frobenius_tate_galois_action K l B).1]`. Conclude with `hF`. Use `TensorProduct.AlgebraTensorModule.ext fun a t => ?_` and prove the remaining obligations. Establish `e : a ⊗ₜ[ℤ_[l]] t = a • tv l A t`. Rewrite using `[TensorProduct.mk_apply, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]`.

Rewrite using `[e, map_smul, map_smul]`. Use `congr 1`. Use `smul_right_injective (Vl l B) hc ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply]`. Rewrite using `[galV_tv, ← hψt, ← map_smul, ← hψt, galV_tv, ← LinearMap.comp_apply ψ, hσ, LinearMap.comp_apply]`.
-/
theorem mem_galHomV_iff (hl : (l : K) ≠ 0) (A B : AbVar K) (φ : Vl l A →ₗ[ℚ_[l]] Vl l B) :
    φ ∈ galHomV l A B ↔ φ ∘ₗ vend l A (toEnd0 A (frob A)) = vend l B (toEnd0 B (frob B)) ∘ₗ φ := by
  rw [(GlobalTheory.T.frobenius_tate_galois_action K l A).2, (GlobalTheory.T.frobenius_tate_galois_action K l B).2]
  refine ⟨fun h => h _, fun h σ => ?_⟩
  haveI := (tl_free_finrank K l hl A).2.1
  haveI := (tl_free_finrank K l hl A).1
  haveI : Module.FinitePresentation ℤ_[l] (Tl l A) := Module.finitePresentation_of_projective _ _
  obtain ⟨ψ, s, hψ⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule (nonZeroDivisors ℤ_[l])
    (tv l B) ((φ.restrictScalars ℤ_[l]) ∘ₗ tv l A)
  set c : ℚ_[l] := algebraMap ℤ_[l] ℚ_[l] s with hcdef
  have hc : c ≠ 0 := fun e =>
    nonZeroDivisors.coe_ne_zero s ((IsFractionRing.injective ℤ_[l] ℚ_[l]).eq_iff' (map_zero _) |>.1 e)
  have hψt : ∀ t, tv l B (ψ t) = c • φ (tv l A t) := fun t => by
    have := LinearMap.congr_fun hψ t
    rw [LinearMap.comp_apply] at this
    rw [this, LinearMap.smul_apply, Submonoid.smul_def, ← algebraMap_smul ℚ_[l] (s : ℤ_[l])]
    rfl
  have hF : ψ ∘ₗ galT l A (Fr K) = galT l B (Fr K) ∘ₗ ψ := by
    refine LinearMap.ext fun t => tv_injective l hl B ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hψt, ← galV_tv, ← galV_tv, hψt, map_smul]
    congr 1
    exact LinearMap.congr_fun h (tv l A t)
  have hσ : ψ ∘ₗ galT l A σ = galT l B σ ∘ₗ ψ := by
    refine (mem_galHomT_iff l A B ψ).2 ?_ σ
    rw [(GlobalTheory.T.frobenius_tate_galois_action K l A).1, (GlobalTheory.T.frobenius_tate_galois_action K l B).1]
    exact hF
  refine TensorProduct.AlgebraTensorModule.ext fun a t => ?_
  have e : a ⊗ₜ[ℤ_[l]] t = a • tv l A t := by
    rw [TensorProduct.mk_apply, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  rw [e, map_smul, map_smul]
  congr 1
  refine smul_right_injective (Vl l B) hc ?_
  simp only [LinearMap.comp_apply]
  rw [galV_tv, ← hψt, ← map_smul, ← hψt, galV_tv, ← LinearMap.comp_apply ψ, hσ, LinearMap.comp_apply]

end GlobalTheory.AV.AbVar

namespace GlobalTheory.AV.AbVar

/- English proof (translation)
Introduce `_ _ _ l _ hl A B` and use `⟨mem_galHomT_iff l A B, mem_galHomV_iff l hl A B, fun W hW σ t ht => galT_mem_of_frob l hl A W hW σ t ht, fun W hW σ w hw => galV_mem_of_frob l hl A W hW σ w hw⟩`.
-/
theorem galois_iff_frob : ∀ (K : Type) [Field K] [Fintype K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A B : AbVar K), (∀ φ : Tl l A →ₗ[ℤ_[l]] Tl l B, φ ∈ galHomT l A B ↔ φ ∘ₗ tend l A (frob A) = tend l B (frob B) ∘ₗ φ) ∧ (∀ φ : Vl l A →ₗ[ℚ_[l]] Vl l B, φ ∈ galHomV l A B ↔ φ ∘ₗ vend l A (toEnd0 A (frob A)) = vend l B (toEnd0 B (frob B)) ∘ₗ φ) ∧ (∀ W : Submodule ℤ_[l] (Tl l A), (∀ t ∈ W, tend l A (frob A) t ∈ W) → ∀ (σ : Gal K), ∀ t ∈ W, galT l A σ t ∈ W) ∧ ∀ W : Submodule ℚ_[l] (Vl l A), (∀ t ∈ W, vend l A (toEnd0 A (frob A)) t ∈ W) → ∀ (σ : Gal K), ∀ t ∈ W, galV l A σ t ∈ W :=
  fun _ _ _ l _ hl A B => ⟨mem_galHomT_iff l A B, mem_galHomV_iff l hl A B,
    fun W hW σ t ht => galT_mem_of_frob l hl A W hW σ t ht,
    fun W hW σ w hw => galV_mem_of_frob l hl A W hW σ w hw⟩

end GlobalTheory.AV.AbVar
