import Mathlib
import GroundTheory.PAdicHodge.PerfectoidField
import GroundTheory.PAdicHodge.TiltValuation
import GroundTheory.PAdicHodge.TiltField
import GroundTheory.PAdicHodge.KerTheta
import GroundTheory.PAdicHodge.KerFontaineThetaCompFrobeniusEquivSymmPow
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

section Integers

variable {K L : Type*} [NormedField K] [IsUltrametricDist K] [NormedField L] [IsUltrametricDist L]

def integerMap (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖) : normInteger K →+* normInteger L :=
  φ.restrict (normInteger K) (normInteger L) fun x hx =>
    mem_normInteger.2 ((hφ x).trans_le (mem_normInteger.1 hx))

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_integerMap (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (x : normInteger K) :
    (integerMap φ hφ x : L) = φ x :=
  rfl

end Integers

section Tilt

variable {K L : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField L] [IsUltrametricDist L]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField L p]
variable (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖)

local notation "𝒪K♭" => PreTilt (normInteger K) p
local notation "𝒪L♭" => PreTilt (normInteger L) p
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "L♭" => Tilt L NormedField.valuation (normInteger L) normInteger_integers p

def modPMap : ModP (normInteger K) p →+* ModP (normInteger L) p :=
  Ideal.quotientMap _ (integerMap φ hφ) (Ideal.span_le.2 (Set.singleton_subset_iff.2 (by
    rw [SetLike.mem_coe, Ideal.mem_comap, map_natCast]
    exact Ideal.mem_span_singleton_self _)))

omit [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField L p] in
/- English proof (translation)
The claim follows from `Ideal.quotientMap_mk`.
-/
theorem modPMap_mk (a : normInteger K) :
    modPMap φ hφ (Ideal.Quotient.mk (Ideal.span {(p : normInteger K)}) a) =
      Ideal.Quotient.mk (Ideal.span {(p : normInteger L)}) (integerMap φ hφ a) :=
  Ideal.quotientMap_mk

variable (p) in

def preTiltMap : 𝒪K♭ →+* 𝒪L♭ :=
  Perfection.map p (modPMap φ hφ)

/- English proof (translation)
The claim follows from `Perfection.coeff_map _ _ _ _`.
-/
theorem coeff_preTiltMap (x : 𝒪K♭) (n : ℕ) :
    Perfection.coeff (ModP (normInteger L) p) p n (preTiltMap p φ hφ x) =
      modPMap φ hφ (Perfection.coeff (ModP (normInteger K) p) p n x) :=
  Perfection.coeff_map _ _ _ _

/- English proof (translation)
Set `y : ℕ → normInteger K` to `fun n => PreTilt.untilt ((frobeniusEquiv 𝒪K♭ p).symm^[n] x)`. Establish `hy : ∀ n, y (n + 1) ^ p = y n` using `IsPerfectoidField.untilt_iterate_succ_pow p x`. Establish `hx : x = IsPerfectoidField.ofCompatible p y hy` using `IsPerfectoidField.preTilt_ext p fun n => by`. Rewrite using `[IsPerfectoidField.coeff_ofCompatible, IsPerfectoidField.mk_untilt_iterate]`. Establish `hy' : ∀ n, (integerMap φ hφ ∘ y) (n + 1) ^ p = (integerMap φ hφ ∘ y) n` using `fun n => by`.

Simplify using `only [Function.comp_apply, ← map_pow, hy]`. Establish `key : preTiltMap p φ hφ x = IsPerfectoidField.ofCompatible p _ hy'`. Use `IsPerfectoidField.preTilt_ext p fun n => ?_` and prove the remaining obligations. Rewrite using `[IsPerfectoidField.coeff_ofCompatible]`. Express the relevant statement in the definitionally equal form `Perfection.coeff (ModP (normInteger L) p) p n (preTiltMap p φ hφ x) = _`.

Rewrite using `[coeff_preTiltMap]`. Express the relevant statement in the definitionally equal form `modPMap φ hφ (PreTilt.coeff n x) = _`. Rewrite using `[← IsPerfectoidField.mk_untilt_iterate, modPMap_mk]`. Both sides reduce to the same expression. Rewrite using `[key, IsPerfectoidField.untilt_ofCompatible]`.

Both sides reduce to the same expression.
-/
theorem untilt_preTiltMap (x : 𝒪K♭) :
    PreTilt.untilt (preTiltMap p φ hφ x) = integerMap φ hφ (PreTilt.untilt x) := by
  let y : ℕ → normInteger K :=
    fun n => PreTilt.untilt ((frobeniusEquiv 𝒪K♭ p).symm^[n] x)
  have hy : ∀ n, y (n + 1) ^ p = y n := IsPerfectoidField.untilt_iterate_succ_pow p x
  have hx : x = IsPerfectoidField.ofCompatible p y hy :=
    IsPerfectoidField.preTilt_ext p fun n => by
      rw [IsPerfectoidField.coeff_ofCompatible, IsPerfectoidField.mk_untilt_iterate]
  have hy' : ∀ n, (integerMap φ hφ ∘ y) (n + 1) ^ p = (integerMap φ hφ ∘ y) n := fun n => by
    simp only [Function.comp_apply, ← map_pow, hy]
  have key : preTiltMap p φ hφ x = IsPerfectoidField.ofCompatible p _ hy' := by
    refine IsPerfectoidField.preTilt_ext p fun n => ?_
    rw [IsPerfectoidField.coeff_ofCompatible]
    change Perfection.coeff (ModP (normInteger L) p) p n (preTiltMap p φ hφ x) = _
    rw [coeff_preTiltMap]
    change modPMap φ hφ (PreTilt.coeff n x) = _
    rw [← IsPerfectoidField.mk_untilt_iterate, modPMap_mk]
    rfl
  rw [key, IsPerfectoidField.untilt_ofCompatible]
  rfl

/- English proof (translation)
Rewrite using `[untilt_preTiltMap, coe_integerMap]`.
-/
theorem coe_untilt_preTiltMap (x : 𝒪K♭) :
    ((PreTilt.untilt (preTiltMap p φ hφ x) : normInteger L) : L) =
      φ ((PreTilt.untilt x : normInteger K) : K) := by
  rw [untilt_preTiltMap, coe_integerMap]

/- English proof (translation)
Use `(injective_iff_map_eq_zero _).2 fun x hx => ?_` and prove the remaining obligations. Establish `h1` using `coe_untilt_preTiltMap φ hφ x`. Rewrite `h1` using `[hx, IsPerfectoidField.untilt_zero, ZeroMemClass.coe_zero, eq_comm, map_eq_zero_iff φ φ.injective]`. Conclude with `(IsPerfectoidField.untilt_eq_zero_iff p).1 (Subtype.ext h1)`.
-/
theorem preTiltMap_injective : Function.Injective (preTiltMap p φ hφ) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  have h1 := coe_untilt_preTiltMap φ hφ x
  rw [hx, IsPerfectoidField.untilt_zero, ZeroMemClass.coe_zero, eq_comm,
    map_eq_zero_iff φ φ.injective] at h1
  exact (IsPerfectoidField.untilt_eq_zero_iff p).1 (Subtype.ext h1)

/- English proof (translation)
Rewrite using `[preTilt_norm_def, preTilt_norm_def, coe_untilt_preTiltMap, hφ]`.
-/
theorem norm_preTiltMap (x : 𝒪K♭) : ‖preTiltMap p φ hφ x‖ = ‖x‖ := by
  rw [preTilt_norm_def, preTilt_norm_def, coe_untilt_preTiltMap, hφ]

variable (p) in

def tiltMap : K♭ →+* L♭ :=
  IsFractionRing.map (preTiltMap_injective (p := p) φ hφ)

@[simp]
/- English proof (translation)
The claim follows from `IsLocalization.map_eq (M := nonZeroDivisors 𝒪K♭) (S := K♭) (T := nonZeroDivisors 𝒪L♭) (Q := L♭) (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (preTiltMap_injective φ hφ)) a`.
-/
theorem tiltMap_algebraMap (a : 𝒪K♭) :
    tiltMap p φ hφ (algebraMap 𝒪K♭ K♭ a) = algebraMap 𝒪L♭ L♭ (preTiltMap p φ hφ a) :=
  IsLocalization.map_eq (M := nonZeroDivisors 𝒪K♭) (S := K♭) (T := nonZeroDivisors 𝒪L♭)
    (Q := L♭)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (preTiltMap_injective φ hφ)) a

/- English proof (translation)
Take `⟨a, b, hb, h⟩` from `exists_mul_algebraMap_eq x`. Establish `hb' : preTiltMap p φ hφ b ≠ 0` using `(map_ne_zero_iff _ (preTiltMap_injective φ hφ)).2 hb`. Establish `h' : tiltMap p φ hφ x * algebraMap 𝒪L♭ L♭ (preTiltMap p φ hφ b) = algebraMap 𝒪L♭ L♭ (preTiltMap p φ hφ a)`. Rewrite using `[← tiltMap_algebraMap, ← tiltMap_algebraMap, ← map_mul, h]`. Rewrite using `[tiltSharp_eq hb' h', tiltSharp_eq hb h, map_div₀, coe_untilt_preTiltMap, coe_untilt_preTiltMap]`.
-/
theorem tiltSharp_tiltMap (x : K♭) : tiltSharp L p (tiltMap p φ hφ x) = φ (tiltSharp K p x) := by
  obtain ⟨a, b, hb, h⟩ := exists_mul_algebraMap_eq x
  have hb' : preTiltMap p φ hφ b ≠ 0 :=
    (map_ne_zero_iff _ (preTiltMap_injective φ hφ)).2 hb
  have h' : tiltMap p φ hφ x * algebraMap 𝒪L♭ L♭ (preTiltMap p φ hφ b) =
      algebraMap 𝒪L♭ L♭ (preTiltMap p φ hφ a) := by
    rw [← tiltMap_algebraMap, ← tiltMap_algebraMap, ← map_mul, h]
  rw [tiltSharp_eq hb' h', tiltSharp_eq hb h, map_div₀, coe_untilt_preTiltMap,
    coe_untilt_preTiltMap]

/- English proof (translation)
Rewrite using `[← norm_tiltSharp, tiltSharp_tiltMap, hφ, norm_tiltSharp]`.
-/
theorem norm_tiltMap (x : K♭) : ‖tiltMap p φ hφ x‖ = ‖x‖ := by
  rw [← norm_tiltSharp, tiltSharp_tiltMap, hφ, norm_tiltSharp]

/- English proof (translation)
The claim follows from `(tiltMap p φ hφ).injective`.
-/
theorem tiltMap_injective : Function.Injective (tiltMap p φ hφ) :=
  (tiltMap p φ hφ).injective

/- English proof (translation)
Use extensionality with `w`. Use `set a : ℕ → 𝒪K♭ := fun n => ((_root_.frobeniusEquiv 𝒪K♭ p).symm ^ n) (w.coeff n)`. Establish `hw : WittVector.teichmullerSeries a = w` using `WittVector.teichmullerSeries_coeff_eq w`. Establish `hle : ∀ n : ℕ, ‖((f w : normInteger L) : L) - g w‖ ≤ ‖(p : L)‖ ^ (n + 1)`. Introduce `n`.

Take `⟨c, hc⟩` from `WittVector.dvd_sub_sum_teichmullerSeries (p := p) a n`. Rewrite `hc` using `[hw]`. Establish `hS : f (∑ i ∈ Finset.Iic n, WittVector.teichmuller p (a i) * (p : WittVector p 𝒪K♭) ^ i) = g (∑ i ∈ Finset.Iic n, WittVector.teichmuller p (a i) * (p : WittVector p 𝒪K♭) ^ i)`. Simplify using `only [map_sum, map_mul, map_pow, map_natCast, h]`. Establish `hfw : f w = f (∑ i ∈ Finset.Iic n, WittVector.teichmuller p (a i) * (p : WittVector p 𝒪K♭) ^ i) + (p : normInteger L) ^ (n + 1) * f c`.

Rewrite using `[← map_natCast f p, ← map_pow, ← map_mul, ← hc, ← map_add, add_sub_cancel]`. Establish `hgw : g w = g (∑ i ∈ Finset.Iic n, WittVector.teichmuller p (a i) * (p : WittVector p 𝒪K♭) ^ i) + (p : normInteger L) ^ (n + 1) * g c`. Rewrite using `[← map_natCast g p, ← map_pow, ← map_mul, ← hc, ← map_add, add_sub_cancel]`. Rewrite using `[hfw, hgw, hS]`. Establish `hc1` using `mem_normInteger.1 (f c).2`.

Establish `hc2` using `mem_normInteger.1 (g c).2`. Simplify using `only [Subring.coe_add, Subring.coe_mul, SubmonoidClass.coe_pow, Subring.coe_natCast, add_sub_add_left_eq_sub, ← mul_sub, norm_mul, norm_pow]`. Combine the equalities or inequalities in the displayed calculation. Use `IsUltrametricDist.norm_add_le_max ((f c : normInteger L) : L) (-((g c : normInteger L) : L))` as an intermediate fact. Rewrite `this` using `[norm_neg, ← sub_eq_add_neg]`.

Conclude with `this.trans (max_le hc1 hc2)`. Use `_ = _ := mul_one _`. Establish `ht : Filter.Tendsto (fun n : ℕ => ‖(p : L)‖ ^ (n + 1)) Filter.atTop (nhds 0)` using `(tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (IsPerfectoidField.norm_natCast_lt_one (K := L) (p := p))).comp (Filter.tendsto_add_atTop_nat 1)`. Establish `h0 : ‖((f w : normInteger L) : L) - g w‖ ≤ 0` using `ge_of_tendsto' ht hle`. Conclude with `sub_eq_zero.1 (norm_le_zero_iff.1 h0)`.
-/
theorem ringHom_ext_wittVector_preTilt {f g : WittVector p 𝒪K♭ →+* normInteger L}
    (h : ∀ a, f (WittVector.teichmuller p a) = g (WittVector.teichmuller p a)) : f = g := by
  ext w
  set a : ℕ → 𝒪K♭ := fun n => ((_root_.frobeniusEquiv 𝒪K♭ p).symm ^ n) (w.coeff n)
  have hw : WittVector.teichmullerSeries a = w := WittVector.teichmullerSeries_coeff_eq w
  have hle : ∀ n : ℕ, ‖((f w : normInteger L) : L) - g w‖ ≤ ‖(p : L)‖ ^ (n + 1) := by
    intro n
    obtain ⟨c, hc⟩ := WittVector.dvd_sub_sum_teichmullerSeries (p := p) a n
    rw [hw] at hc
    have hS : f (∑ i ∈ Finset.Iic n, WittVector.teichmuller p (a i) * (p : WittVector p 𝒪K♭) ^ i) =
        g (∑ i ∈ Finset.Iic n, WittVector.teichmuller p (a i) * (p : WittVector p 𝒪K♭) ^ i) := by
      simp only [map_sum, map_mul, map_pow, map_natCast, h]
    have hfw : f w = f (∑ i ∈ Finset.Iic n, WittVector.teichmuller p (a i) * (p : WittVector p 𝒪K♭) ^ i)
        + (p : normInteger L) ^ (n + 1) * f c := by
      rw [← map_natCast f p, ← map_pow, ← map_mul, ← hc, ← map_add, add_sub_cancel]
    have hgw : g w = g (∑ i ∈ Finset.Iic n, WittVector.teichmuller p (a i) * (p : WittVector p 𝒪K♭) ^ i)
        + (p : normInteger L) ^ (n + 1) * g c := by
      rw [← map_natCast g p, ← map_pow, ← map_mul, ← hc, ← map_add, add_sub_cancel]
    rw [hfw, hgw, hS]
    have hc1 := mem_normInteger.1 (f c).2
    have hc2 := mem_normInteger.1 (g c).2
    simp only [Subring.coe_add, Subring.coe_mul, SubmonoidClass.coe_pow, Subring.coe_natCast,
      add_sub_add_left_eq_sub, ← mul_sub, norm_mul, norm_pow]
    calc ‖(p : L)‖ ^ (n + 1) * ‖((f c : normInteger L) : L) - g c‖
        ≤ ‖(p : L)‖ ^ (n + 1) * 1 := by
          gcongr
          have := IsUltrametricDist.norm_add_le_max ((f c : normInteger L) : L) (-((g c : normInteger L) : L))
          rw [norm_neg, ← sub_eq_add_neg] at this
          exact this.trans (max_le hc1 hc2)
      _ = _ := mul_one _
  have ht : Filter.Tendsto (fun n : ℕ => ‖(p : L)‖ ^ (n + 1)) Filter.atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _)
      (IsPerfectoidField.norm_natCast_lt_one (K := L) (p := p))).comp
        (Filter.tendsto_add_atTop_nat 1)
  have h0 : ‖((f w : normInteger L) : L) - g w‖ ≤ 0 := ge_of_tendsto' ht hle
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)

/- English proof (translation)
Use `ringHom_ext_wittVector_preTilt (f := (WittVector.fontaineTheta (normInteger L) p).comp (WittVector.map (preTiltMap p φ hφ))) (g := (integerMap φ hφ).comp (WittVector.fontaineTheta (normInteger K) p)) fun a => by` as an intermediate fact. Rewrite using `[RingHom.comp_apply, RingHom.comp_apply, WittVector.map_teichmuller, WittVector.fontaineTheta_teichmuller, WittVector.fontaineTheta_teichmuller, untilt_preTiltMap]`. Conclude with `congrArg (fun F => F w) this`.
-/
theorem fontaineTheta_map_preTiltMap (w : WittVector p 𝒪K♭) :
    WittVector.fontaineTheta (normInteger L) p (WittVector.map (preTiltMap p φ hφ) w) =
      integerMap φ hφ (WittVector.fontaineTheta (normInteger K) p w) := by
  have := ringHom_ext_wittVector_preTilt
    (f := (WittVector.fontaineTheta (normInteger L) p).comp (WittVector.map (preTiltMap p φ hφ)))
    (g := (integerMap φ hφ).comp (WittVector.fontaineTheta (normInteger K) p)) fun a => by
      rw [RingHom.comp_apply, RingHom.comp_apply, WittVector.map_teichmuller,
        WittVector.fontaineTheta_teichmuller, WittVector.fontaineTheta_teichmuller, untilt_preTiltMap]
  exact congrArg (fun F => F w) this

end Tilt

end GroundTheory.PAdicHodge
