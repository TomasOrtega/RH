import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLemVR
import Formalism.FlagUnipotentLattices.ArithmeticIdentityEntries
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.DifferentIdealEqTop

noncomputable section

namespace Formalism.MainNotions.BridgeLemVC

open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.RankOne Formalism.MainNotions.BridgeLemVR nonZeroDivisors

variable {K : Type} [Field K] [NumberField K] [StarRing K]

/- English proof (translation)
The claim follows from `FractionalIdeal.isFractional_of_fg hM.fg`.
-/
theorem isFrac {M : Submodule (𝓞 K) K} (hM : Submodule.IsLattice K M) : IsFractional (𝓞 K)⁰ M :=
  FractionalIdeal.isFractional_of_fg hM.fg

def fracI {M : Submodule (𝓞 K) K} (hM : Submodule.IsLattice K M) : FractionalIdeal (𝓞 K)⁰ K :=
  ⟨M, isFrac hM⟩

/- English proof (translation)
The claim follows from `FractionalIdeal.coe_mk _ _`.
-/
theorem coe_fracI {M : Submodule (𝓞 K) K} (hM : Submodule.IsLattice K M) :
    ((fracI hM : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) = M := FractionalIdeal.coe_mk _ _

/- English proof (translation)
Take `⟨a, ha, h0⟩` from `exists_ne_zero_of_isLattice hM`. Introduce `e`. Establish `h1 : a ∈ fracI hM` using `by rw [← FractionalIdeal.mem_coe, coe_fracI]; exact ha`. Rewrite `h1` using `[e]`. Conclude with `h0 ((FractionalIdeal.mem_zero_iff _).1 h1)`.
-/
theorem frac_ne_zero {M : Submodule (𝓞 K) K} (hM : Submodule.IsLattice K M) : fracI hM ≠ 0 := by
  obtain ⟨a, ha, h0⟩ := exists_ne_zero_of_isLattice hM
  intro e
  have h1 : a ∈ fracI hM := by rw [← FractionalIdeal.mem_coe, coe_fracI]; exact ha
  rw [e] at h1
  exact h0 ((FractionalIdeal.mem_zero_iff _).1 h1)

def fracU {M : Submodule (𝓞 K) K} (hM : Submodule.IsLattice K M) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 _ (frac_ne_zero hM)

/- English proof (translation)
The claim follows from `coe_fracI hM`.
-/
theorem coe_fracU {M : Submodule (𝓞 K) K} (hM : Submodule.IsLattice K M) :
    (((fracU hM : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) = M :=
  coe_fracI hM

/- English proof (translation)
Establish `h1 : ClassGroup.mk K (fracU hM * (fracU hM')⁻¹) = 1`. Rewrite using `[map_mul, map_inv, he, mul_inv_cancel]`. Rewrite `h1` using `[ClassGroup.mk_eq_one_iff]`. Take `⟨⟨a, ha⟩⟩` from `h1`. Establish `hMa : M = Submodule.span (𝓞 K) {a} * M'`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Units.val_mul, FractionalIdeal.coe_mul, ha, coe_fracU]`. Use `⟨a, fun h0 => ?_, hMa⟩` and prove the remaining obligations. Take `⟨x, hx, hx0⟩` from `exists_ne_zero_of_isLattice hM`. Rewrite `hx` using `[hMa, h0, Submodule.mem_span_singleton_mul]`.

Take `⟨y, -, hy⟩` from `hx`. Rewrite `hy` using `[zero_mul]`. Conclude with `hx0 hy.symm`.
-/
theorem exists_eq_span_mul {M M' : Submodule (𝓞 K) K} (hM : Submodule.IsLattice K M)
    (hM' : Submodule.IsLattice K M') (he : ClassGroup.mk K (fracU hM) = ClassGroup.mk K (fracU hM')) :
    ∃ a : K, a ≠ 0 ∧ M = Submodule.span (𝓞 K) {a} * M' := by
  have h1 : ClassGroup.mk K (fracU hM * (fracU hM')⁻¹) = 1 := by
    rw [map_mul, map_inv, he, mul_inv_cancel]
  rw [ClassGroup.mk_eq_one_iff] at h1
  obtain ⟨⟨a, ha⟩⟩ := h1
  have hMa : M = Submodule.span (𝓞 K) {a} * M' := by
    calc M = (((fracU hM * (fracU hM')⁻¹ * fracU hM' : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
          FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by rw [inv_mul_cancel_right, coe_fracU]
      _ = Submodule.span (𝓞 K) {a} * M' := by
          rw [Units.val_mul, FractionalIdeal.coe_mul, ha, coe_fracU]
  refine ⟨a, fun h0 => ?_, hMa⟩
  obtain ⟨x, hx, hx0⟩ := exists_ne_zero_of_isLattice hM
  rw [hMa, h0, Submodule.mem_span_singleton_mul] at hx
  obtain ⟨y, -, hy⟩ := hx
  rw [zero_mul] at hy
  exact hx0 hy.symm

/- English proof (translation)
Establish `intF : ∀ x : cmF K, (x : K) ∈ (1 : Submodule (𝓞 K) K) → IsIntegral ℤ x`. Introduce `x hx`. Take `⟨r, hr⟩` from `Submodule.mem_one.1 hx`. Establish `hK : IsIntegral ℤ (x : K)` using `by rw [← hr]; exact RingOfIntegers.isIntegral_coe r`. Conclude with `(isIntegral_algHom_iff ((cmF K).val.toRingHom.toIntAlgHom) Subtype.val_injective).1 hK`.

Establish `hs' : star u⁻¹ = u⁻¹` using `by rw [star_inv₀, hs]`. Set `x : cmF K` to `⟨u, (mem_cmF_iff K u).2 hs⟩`. Set `y : cmF K` to `⟨u⁻¹, (mem_cmF_iff K _).2 hs'⟩`. Set `t0 : 𝓞 (cmF K)` to `⟨x, intF x hu⟩`. Set `t1 : 𝓞 (cmF K)` to `⟨y, intF y hu'⟩`.

Establish `hxy : t0 * t1 = 1`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Use `show u * u⁻¹ = 1`. Conclude with `mul_inv_cancel₀ hu0`.

Conclude with `⟨⟨t0, t1, hxy, by rw [mul_comm]; exact hxy⟩, rfl⟩`.
-/
theorem exists_unitF {u : K} (hu0 : u ≠ 0) (hu : u ∈ (1 : Submodule (𝓞 K) K))
    (hu' : u⁻¹ ∈ (1 : Submodule (𝓞 K) K)) (hs : star u = u) :
    ∃ t : (𝓞 (cmF K))ˣ, (((t : 𝓞 (cmF K)) : cmF K) : K) = u := by
  have intF : ∀ x : cmF K, (x : K) ∈ (1 : Submodule (𝓞 K) K) → IsIntegral ℤ x := by
    intro x hx
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 hx
    have hK : IsIntegral ℤ (x : K) := by rw [← hr]; exact RingOfIntegers.isIntegral_coe r
    exact (isIntegral_algHom_iff ((cmF K).val.toRingHom.toIntAlgHom) Subtype.val_injective).1 hK
  have hs' : star u⁻¹ = u⁻¹ := by rw [star_inv₀, hs]
  let x : cmF K := ⟨u, (mem_cmF_iff K u).2 hs⟩
  let y : cmF K := ⟨u⁻¹, (mem_cmF_iff K _).2 hs'⟩
  let t0 : 𝓞 (cmF K) := ⟨x, intF x hu⟩
  let t1 : 𝓞 (cmF K) := ⟨y, intF y hu'⟩
  have hxy : t0 * t1 = 1 := by
    apply RingOfIntegers.ext
    apply Subtype.ext
    show u * u⁻¹ = 1
    exact mul_inv_cancel₀ hu0
  exact ⟨⟨t0, t1, hxy, by rw [mul_comm]; exact hxy⟩, rfl⟩

def iota (K : Type) [Field K] [NumberField K] [StarRing K] : (𝓞 (cmF K))ˣ →* K :=
  ((cmF K).val.toRingHom.comp (algebraMap (𝓞 (cmF K)) (cmF K))).toMonoidHom.comp (Units.coeHom _)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem iota_apply (t : (𝓞 (cmF K))ˣ) : iota K t = (((t : 𝓞 (cmF K)) : cmF K) : K) := rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨Units.map (RingOfIntegers.mapRingHom ((cmF K).val.toRingHom)).toMonoidHom v, rfl⟩`.
-/
theorem exists_unitK (v : (𝓞 (cmF K))ˣ) : ∃ w : (𝓞 K)ˣ, algebraMap (𝓞 K) K (w : 𝓞 K) = iota K v :=
  ⟨Units.map (RingOfIntegers.mapRingHom ((cmF K).val.toRingHom)).toMonoidHom v, rfl⟩

/- English proof (translation)
Use extensionality with `y`. Rewrite using `[mem_gmap, Submodule.mem_span_singleton_mul]`. Establish `hs : ∀ z, (LinearEquiv.smulOfNeZero K K b hb).symm z = b⁻¹ * z` using `fun z => rfl`. Prove the components needed by the constructor for the conclusion. Introduce `hy`.

Use `⟨b⁻¹ * y, by rw [← hs]; exact hy, ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_assoc, mul_inv_cancel₀ hb, one_mul]`. Introduce and unpack `⟨n, hn, rfl⟩`. Rewrite using `[hs, ← mul_assoc, inv_mul_cancel₀ hb, one_mul]`. Conclude with `hn`.
-/
theorem gmap_smul {b : K} (hb : b ≠ 0) (N : Submodule (𝓞 K) K) :
    gmap (LinearEquiv.smulOfNeZero K K b hb) N = Submodule.span (𝓞 K) {b} * N := by
  ext y
  rw [mem_gmap, Submodule.mem_span_singleton_mul]
  have hs : ∀ z, (LinearEquiv.smulOfNeZero K K b hb).symm z = b⁻¹ * z := fun z => rfl
  constructor
  · intro hy
    refine ⟨b⁻¹ * y, by rw [← hs]; exact hy, ?_⟩
    rw [← mul_assoc, mul_inv_cancel₀ hb, one_mul]
  · rintro ⟨n, hn, rfl⟩
    rw [hs, ← mul_assoc, inv_mul_cancel₀ hb, one_mul]
    exact hn

/- English proof (translation)
Use extensionality with `y`. Rewrite using `[mem_gmap]`. Both sides reduce to the same expression.
-/
theorem gmap_one (N : Submodule (𝓞 K) K) : gmap (1 : K ≃ₗ[K] K) N = N := by
  ext y
  rw [mem_gmap]
  rfl

/- English proof (translation)
Use extensionality with `y`. Rewrite using `[Submodule.mem_span_singleton_mul]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, hn, rfl⟩`. Rewrite using `[← Algebra.smul_def]`.

Conclude with `N.smul_mem _ hn`. Introduce `hy`. Use `⟨((w⁻¹ : (𝓞 K)ˣ) : 𝓞 K) • y, N.smul_mem _ hy, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, ← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]`.
-/
theorem span_unit_mul (w : (𝓞 K)ˣ) (N : Submodule (𝓞 K) K) :
    Submodule.span (𝓞 K) {algebraMap (𝓞 K) K (w : 𝓞 K)} * N = N := by
  ext y
  rw [Submodule.mem_span_singleton_mul]
  constructor
  · rintro ⟨n, hn, rfl⟩
    rw [← Algebra.smul_def]
    exact N.smul_mem _ hn
  · intro hy
    refine ⟨((w⁻¹ : (𝓞 K)ˣ) : 𝓞 K) • y, N.smul_mem _ hy, ?_⟩
    rw [Algebra.smul_def, ← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]

end Formalism.MainNotions.BridgeLemVC

end
