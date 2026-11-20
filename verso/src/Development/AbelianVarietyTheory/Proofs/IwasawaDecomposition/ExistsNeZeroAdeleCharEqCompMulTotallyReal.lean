import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.AdeleCharTwist

/- English proof (translation)
Establish `hm : ∀ a, g a ∈ Submonoid.unitSphere ℂ` using `fun a => by simpa [Submonoid.unitSphere] using hn a`. Set `χ : C(ℝ, Circle)` to `⟨fun a => ⟨g a, hm a⟩, hc.subtype_mk hm⟩`. Establish `hχ : ∀ s t, χ (s + t) = χ s * χ t` using `fun s t => Subtype.ext (hadd s t)`. Take `⟨L, ⟨hL0, hL⟩, hu⟩` from `Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts χ 0 0 (by rw [Circle.exp_zero]; exact Subtype.ext h0.symm)`. Establish `hL' : ∀ t, Circle.exp (L t) = χ t` using `congrFun hL`.

Establish `hLa : ∀ s t, L (s + t) = L s + L t` using `fun s t => by`. Use `hu ⟨fun t => L (s + t) - L s, by fun_prop⟩ ⟨by simp, by` as an intermediate fact. Use function extensionality and compare the values at `t`. Use `show Circle.exp (L (s + t) - L s) = χ t`. Rewrite using `[Circle.exp_sub, hL', hL', hχ, mul_div_cancel_left]⟩`.

Establish `h2 : L (s + t) - L s = L t` using `DFunLike.congr_fun this t`. Combine the linear equalities and inequalities to obtain the conclusion. Set `l : ℝ →+ ℝ` to `AddMonoidHom.mk' L hLa`. Use `⟨L 1 / (2 * Real.pi), fun t => ?_⟩` and prove the remaining obligations. Establish `h3 : L t = t * L 1`.

Use `map_real_smul l L.continuous t 1` as an intermediate fact. Simplify `this` using `[l]`. Establish `h4 : g t = (Circle.exp (L t) : ℂ)` using `by rw [hL']; rfl`. Establish `hpi : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Rewrite using `[h4, Circle.coe_exp, h3]`.

Use `congr 1`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_eq_exp (g : ℝ → ℂ) (hc : Continuous g) (hn : ∀ t, ‖g t‖ = 1) (h0 : g 0 = 1)
    (hadd : ∀ s t, g (s + t) = g s * g t) :
    ∃ c : ℝ, ∀ t : ℝ, g t = Complex.exp (2 * Real.pi * Complex.I * ((c * t : ℝ) : ℂ)) := by
  have hm : ∀ a, g a ∈ Submonoid.unitSphere ℂ := fun a => by simpa [Submonoid.unitSphere] using hn a
  let χ : C(ℝ, Circle) := ⟨fun a => ⟨g a, hm a⟩, hc.subtype_mk hm⟩
  have hχ : ∀ s t, χ (s + t) = χ s * χ t := fun s t => Subtype.ext (hadd s t)
  obtain ⟨L, ⟨hL0, hL⟩, hu⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts χ 0 0
    (by rw [Circle.exp_zero]; exact Subtype.ext h0.symm)
  have hL' : ∀ t, Circle.exp (L t) = χ t := congrFun hL
  have hLa : ∀ s t, L (s + t) = L s + L t := fun s t => by
    have := hu ⟨fun t => L (s + t) - L s, by fun_prop⟩ ⟨by simp, by
      funext t
      show Circle.exp (L (s + t) - L s) = χ t
      rw [Circle.exp_sub, hL', hL', hχ, mul_div_cancel_left]⟩
    have h2 : L (s + t) - L s = L t := DFunLike.congr_fun this t
    linarith
  let l : ℝ →+ ℝ := AddMonoidHom.mk' L hLa
  refine ⟨L 1 / (2 * Real.pi), fun t => ?_⟩
  have h3 : L t = t * L 1 := by
    have := map_real_smul l L.continuous t 1
    simpa [l] using this
  have h4 : g t = (Circle.exp (L t) : ℂ) := by rw [hL']; rfl
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [h4, Circle.coe_exp, h3]
  congr 1
  push_cast
  field_simp

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pairA_add (x x' : Ainf F) (y y' : Af F) :
    pairA F (x + x') (y + y') = pairA F x y + pairA F x' y' := rfl

/- English proof (translation)
Rewrite using `[← pairA_add, add_zero, zero_add]`. Both sides reduce to the same expression.
-/
theorem algebraMap_eq_pairA (x : F) :
    algebraMap F (AF F) x = pairA F (algebraMap F _ x) 0 + pairA F 0 (algebraMap F _ x) := by
  rw [← pairA_add, add_zero, zero_add]
  rfl

/- English proof (translation)
Introduce `y`. Rewrite using `[mem_closure_iff_nhds]`. Introduce `U hU`. Establish `hc : Continuous fun z : Af F => y - z` using `continuous_const.sub continuous_id`. Establish `hV : (fun z : Af F => y - z) ⁻¹' U ∈ 𝓝 (0 : Af F)` using `hc.continuousAt.preimage_mem_nhds (by simpa using hU)`.

Take `⟨N, hN, hNU⟩` from `GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ hV`. Take `⟨a, β, hβ, e⟩` from `(GlobalTheory.AdLat.strong_approximation_mod_nat F N hN).1 y`. Use `⟨y - N • β, hNU β hβ, a, ?_⟩` and prove the remaining obligations. Rewrite using `[e, add_sub_cancel_right]`.
-/
theorem denseRange_fin : DenseRange (algebraMap F (Af F)) := by
  intro y
  rw [mem_closure_iff_nhds]
  intro U hU
  have hc : Continuous fun z : Af F => y - z := continuous_const.sub continuous_id
  have hV : (fun z : Af F => y - z) ⁻¹' U ∈ 𝓝 (0 : Af F) :=
    hc.continuousAt.preimage_mem_nhds (by simpa using hU)
  obtain ⟨N, hN, hNU⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ hV
  obtain ⟨a, β, hβ, e⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F N hN).1 y
  refine ⟨y - N • β, hNU β hβ, a, ?_⟩
  rw [e, add_sub_cancel_right]

/- English proof (translation)
Establish `h1 : (fun z => ψ (pairA F z 0)) = fun z => ψ' (pairA F z 0)` using `(InfiniteAdeleRing.denseRange_algebraMap F).equalizer (hc.comp (continuous_id.prodMk continuous_const)) (hc'.comp (continuous_id.prodMk continuous_const)) (funext h)`. Establish `h2 : (fun z => ψ (pairA F 0 z)) = fun z => ψ' (pairA F 0 z)` using `denseRange_fin.equalizer (hc.comp (continuous_const.prodMk continuous_id)) (hc'.comp (continuous_const.prodMk continuous_id)) (funext fun a => by`. Establish `e` using `hr a`. Establish `e'` using `hr' a`. Rewrite `e` using `[algebraMap_eq_pairA, ha, h]`.

Rewrite `e'` using `[algebraMap_eq_pairA, ha']`. Conclude with `mul_left_cancel₀ (left_ne_zero_of_mul_eq_one e) (e.trans e'.symm))`. Establish `e : x = pairA F x.1 0 + pairA F 0 x.2`. Rewrite using `[← pairA_add, add_zero, zero_add]`. Both sides reduce to the same expression.

Rewrite using `[e, ha, ha', congrFun h1, congrFun h2]`.
-/
theorem ext_of_inf {ψ ψ' : AF F → ℂ} (hc : Continuous ψ) (hc' : Continuous ψ')
    (ha : ∀ x y, ψ (x + y) = ψ x * ψ y) (ha' : ∀ x y, ψ' (x + y) = ψ' x * ψ' y)
    (hr : ∀ a : F, ψ (algebraMap F _ a) = 1) (hr' : ∀ a : F, ψ' (algebraMap F _ a) = 1)
    (h : ∀ a : F, ψ (pairA F (algebraMap F _ a) 0) = ψ' (pairA F (algebraMap F _ a) 0)) (x : AF F) :
    ψ x = ψ' x := by
  have h1 : (fun z => ψ (pairA F z 0)) = fun z => ψ' (pairA F z 0) :=
    (InfiniteAdeleRing.denseRange_algebraMap F).equalizer
      (hc.comp (continuous_id.prodMk continuous_const)) (hc'.comp (continuous_id.prodMk continuous_const))
      (funext h)
  have h2 : (fun z => ψ (pairA F 0 z)) = fun z => ψ' (pairA F 0 z) :=
    denseRange_fin.equalizer
      (hc.comp (continuous_const.prodMk continuous_id)) (hc'.comp (continuous_const.prodMk continuous_id))
      (funext fun a => by
        have e := hr a
        have e' := hr' a
        rw [algebraMap_eq_pairA, ha, h] at e
        rw [algebraMap_eq_pairA, ha'] at e'
        exact mul_left_cancel₀ (left_ne_zero_of_mul_eq_one e) (e.trans e'.symm))
  have e : x = pairA F x.1 0 + pairA F 0 x.2 := by
    rw [← pairA_add, add_zero, zero_add]
    rfl
  rw [e, ha, ha', congrFun h1, congrFun h2]

/- English proof (translation)
Take `⟨N, hN, h⟩` from `GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ (GlobalTheory.FinTranslate.ker_mem_nhds hψ.1 hψ.2.1)`. Use `⟨N, hN, fun r => ?_⟩` and prove the remaining obligations. Establish `h1 : ψ (pairA F 0 (N • algebraMap F (Af F) r)) = 1` using `h _ fun v => HeightOneSpectrum.coe_mem_adicCompletionIntegers v r`. Establish `h2` using `hψ.2.2.1 ((N : F) * r)`. Rewrite `h1` using `[nsmul_eq_mul, ← map_natCast (algebraMap F (Af F)), ← map_mul]`.

Rewrite `h2` using `[algebraMap_eq_pairA, AddChar.map_add_eq_mul, h1, mul_one]`. Then use the resulting hypothesis.
-/
theorem exists_nsmul_inf {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) :
    ∃ N : ℕ, 0 < N ∧ ∀ r : 𝓞 F, ψ (pairA F (algebraMap F _ ((N : F) * r)) 0) = 1 := by
  obtain ⟨N, hN, h⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ (GlobalTheory.FinTranslate.ker_mem_nhds hψ.1 hψ.2.1)
  refine ⟨N, hN, fun r => ?_⟩
  have h1 : ψ (pairA F 0 (N • algebraMap F (Af F) r)) = 1 :=
    h _ fun v => HeightOneSpectrum.coe_mem_adicCompletionIntegers v r
  have h2 := hψ.2.2.1 ((N : F) * r)
  rw [nsmul_eq_mul, ← map_natCast (algebraMap F (Af F)), ← map_mul] at h1
  rwa [algebraMap_eq_pairA, AddChar.map_add_eq_mul, h1, mul_one] at h2

/- English proof (translation)
Set `e : ∀ w : InfinitePlace F, w.Completion ≃+* ℝ` to `fun w => InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)`. Conclude with `⟨Pi.ringHom fun w => (e w).symm.toRingHom, continuous_pi fun w => (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm.continuous⟩`.
-/
theorem exists_realHom [IsTotallyReal F] : ∃ ρ : ℝ →+* Ainf F, Continuous ρ := by
  let e : ∀ w : InfinitePlace F, w.Completion ≃+* ℝ := fun w =>
    InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)
  exact ⟨Pi.ringHom fun w => (e w).symm.toRingHom, continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm.continuous⟩

/- English proof (translation)
Take `⟨N, hN, hNr⟩` from `exists_nsmul_inf hψ`. Take `⟨ρ, hρ⟩` from `exists_realHom (F := F)`. Establish `hρq : ∀ q : ℚ, ρ (q : ℝ) = algebraMap F (Ainf F) (q : F)` using `fun q => RingHom.congr_fun (RingHom.ext_rat (ρ.comp (Rat.castHom ℝ)) ((algebraMap F (Ainf F)).comp (Rat.castHom F))) q`. Establish `hadd : ∀ x y : Ainf F, ψ (pairA F (x + y) 0) = ψ (pairA F x 0) * ψ (pairA F y 0)` using `fun x y => by`. Rewrite using `[← AddChar.map_add_eq_mul, ← pairA_add, add_zero]`.

Establish `h0 : ψ (pairA F 0 0) = 1` using `ψ.map_zero_eq_one`. Establish `key : ∀ r : 𝓞 F, ∃ c : ℚ, ∀ q : ℚ, ψ (pairA F (algebraMap F _ (q • (r : F))) 0) = Complex.exp (2 * Real.pi * Complex.I * ((q * c : ℚ) : ℂ))` using `fun r => by`. Take `⟨c, hc⟩` from `exists_eq_exp (fun t => ψ (pairA F (ρ t * algebraMap F _ (r : F)) 0)) (hψ.1.comp ((hρ.mul continuous_const).prodMk continuous_const)) (fun t => hψ.2.1 _) (by simp only [map_zero, zero_mul, h0]) (fun s t => by simp only [map_add, add_mul, hadd])`. Establish `hq : ∀ q : ℚ, ψ (pairA F (algebraMap F _ ((q : F) * (r : F))) 0) = Complex.exp (2 * Real.pi * Complex.I * ((c * q : ℝ) : ℂ))` using `fun q => by`. Rewrite using `[← hc, hρq, map_mul]`.

Establish `h1` using `hq N`. Rewrite `h1` using `[Rat.cast_natCast, hNr, eq_comm, Complex.exp_eq_one_iff]`. Take `⟨n, hn⟩` from `h1`. Rewrite `hn` using `[mul_comm (n : ℂ), mul_right_inj' Complex.two_pi_I_ne_zero]`. Establish `hN' : (N : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hN.ne'`.

Use `⟨n / N, fun q => ?_⟩` and prove the remaining obligations. Rewrite using `[Rat.smul_def, hq]`. Use `congr 2`. Move the coercions through the operations in `at hn ⊢`. Rewrite using `[← hn]`.

Clear the denominators using the available nonvanishing facts. Use `choose c hc using key`. Set `b` to `integralBasis F`. Set `φ : F →ₗ[ℚ] ℚ` to `b.constr ℚ fun i => c (RingOfIntegers.basis F i)`. Take `⟨a, ha⟩` from `((Algebra.traceForm ℚ F).toDual (traceForm_nondegenerate ℚ F)).surjective φ`.

Establish `ha' : ∀ x, Algebra.trace ℚ F (a * x) = φ x` using `fun x => by`. Rewrite using `[← ha]`. Both sides reduce to the same expression. Use `⟨a, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[ha', ← b.sum_repr x]`.

Use `Finset.sum_induction _ (fun y : F => ψ (pairA F (algebraMap F _ y) 0) = Complex.exp (2 * Real.pi * Complex.I * ((φ y : ℚ) : ℂ))) (fun y z hy hz => ?_) ?_ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_add, hadd, hy, hz, map_add, ← Complex.exp_add]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [map_zero, h0, Rat.cast_zero, mul_zero, Complex.exp_zero]`. Rewrite using `[map_smul φ, Module.Basis.constr_basis, smul_eq_mul, ← hc, integralBasis_apply]`.
-/
theorem exists_trace [IsTotallyReal F] {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) :
    ∃ a : F, ∀ x : F, ψ (pairA F (algebraMap F _ x) 0) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F (a * x) : ℚ) : ℂ)) := by
  classical
  obtain ⟨N, hN, hNr⟩ := exists_nsmul_inf hψ
  obtain ⟨ρ, hρ⟩ := exists_realHom (F := F)
  have hρq : ∀ q : ℚ, ρ (q : ℝ) = algebraMap F (Ainf F) (q : F) := fun q =>
    RingHom.congr_fun (RingHom.ext_rat (ρ.comp (Rat.castHom ℝ)) ((algebraMap F (Ainf F)).comp (Rat.castHom F))) q
  have hadd : ∀ x y : Ainf F, ψ (pairA F (x + y) 0) = ψ (pairA F x 0) * ψ (pairA F y 0) := fun x y => by
    rw [← AddChar.map_add_eq_mul, ← pairA_add, add_zero]
  have h0 : ψ (pairA F 0 0) = 1 := ψ.map_zero_eq_one
  have key : ∀ r : 𝓞 F, ∃ c : ℚ, ∀ q : ℚ, ψ (pairA F (algebraMap F _ (q • (r : F))) 0) =
      Complex.exp (2 * Real.pi * Complex.I * ((q * c : ℚ) : ℂ)) := fun r => by
    obtain ⟨c, hc⟩ := exists_eq_exp (fun t => ψ (pairA F (ρ t * algebraMap F _ (r : F)) 0))
      (hψ.1.comp ((hρ.mul continuous_const).prodMk continuous_const)) (fun t => hψ.2.1 _)
      (by simp only [map_zero, zero_mul, h0]) (fun s t => by simp only [map_add, add_mul, hadd])
    have hq : ∀ q : ℚ, ψ (pairA F (algebraMap F _ ((q : F) * (r : F))) 0) =
        Complex.exp (2 * Real.pi * Complex.I * ((c * q : ℝ) : ℂ)) := fun q => by
      rw [← hc, hρq, map_mul]
    have h1 := hq N
    rw [Rat.cast_natCast, hNr, eq_comm, Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    rw [mul_comm (n : ℂ), mul_right_inj' Complex.two_pi_I_ne_zero] at hn
    have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    refine ⟨n / N, fun q => ?_⟩
    rw [Rat.smul_def, hq]
    congr 2
    push_cast at hn ⊢
    rw [← hn]
    field_simp
  choose c hc using key
  let b := integralBasis F
  let φ : F →ₗ[ℚ] ℚ := b.constr ℚ fun i => c (RingOfIntegers.basis F i)
  obtain ⟨a, ha⟩ := ((Algebra.traceForm ℚ F).toDual (traceForm_nondegenerate ℚ F)).surjective φ
  have ha' : ∀ x, Algebra.trace ℚ F (a * x) = φ x := fun x => by
    rw [← ha]; rfl
  refine ⟨a, fun x => ?_⟩
  rw [ha', ← b.sum_repr x]
  refine Finset.sum_induction _ (fun y : F => ψ (pairA F (algebraMap F _ y) 0) =
    Complex.exp (2 * Real.pi * Complex.I * ((φ y : ℚ) : ℂ))) (fun y z hy hz => ?_) ?_ fun i _ => ?_
  · rw [map_add, hadd, hy, hz, map_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  · simp only [map_zero, h0, Rat.cast_zero, mul_zero, Complex.exp_zero]
  · rw [map_smul φ, Module.Basis.constr_basis, smul_eq_mul, ← hc, integralBasis_apply]

/- English proof (translation)
Introduce and unpack `rfl`. Take `⟨x, hx⟩` from `hψ.2.2.2`. Use `hx (ext_of_inf (ψ' := fun _ => 1) hψ.1 continuous_const ψ.map_add_eq_mul (fun _ _ => by simp) hψ.2.2.1 (fun _ => rfl) (fun y => by simp [h]) x)` and prove the remaining obligations.
-/
theorem trace_mul_ne_zero {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) {a : F}
    (h : ∀ x : F, ψ (pairA F (algebraMap F _ x) 0) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F (a * x) : ℚ) : ℂ))) : a ≠ 0 := by
  rintro rfl
  obtain ⟨x, hx⟩ := hψ.2.2.2
  refine hx (ext_of_inf (ψ' := fun _ => 1) hψ.1 continuous_const ψ.map_add_eq_mul (fun _ _ => by simp)
    hψ.2.2.1 (fun _ => rfl) (fun y => by simp [h]) x)

/- English proof (translation)
Introduce `F _ _ _ ψ ψ' hψ hψ'`. Take `⟨a, ha⟩` from `exists_trace hψ`. Take `⟨a', ha'⟩` from `exists_trace hψ'`. Establish `h0` using `trace_mul_ne_zero hψ ha`. Use `⟨a' / a, div_ne_zero (trace_mul_ne_zero hψ' ha') h0, ?_⟩` and prove the remaining obligations.

Use `ext_of_inf hψ'.1 (hψ.1.comp (continuous_const.mul continuous_id)) ψ'.map_add_eq_mul (fun x y => by rw [mul_add, ψ.map_add_eq_mul]) hψ'.2.2.1 (fun x => by rw [← map_mul, hψ.2.2.1]) fun x => ?_` and prove the remaining obligations. Establish `e : algebraMap F (AF F) (a' / a) * pairA F (algebraMap F _ x) 0 = pairA F (algebraMap F _ (a' / a * x)) 0` using `Prod.ext (map_mul (algebraMap F (Ainf F)) _ _).symm (mul_zero _)`. Rewrite using `[e, ha, ha', ← mul_assoc, mul_div_cancel₀ _ h0]`.
-/
theorem exists_mul_eq : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ψ ψ' : AddChar (AF F) ℂ), IsCharAF F ψ → IsCharAF F ψ' → ∃ a : F, a ≠ 0 ∧ ∀ x, ψ' x = ψ (algebraMap F (AF F) a * x) := by
  intro F _ _ _ ψ ψ' hψ hψ'
  obtain ⟨a, ha⟩ := exists_trace hψ
  obtain ⟨a', ha'⟩ := exists_trace hψ'
  have h0 := trace_mul_ne_zero hψ ha
  refine ⟨a' / a, div_ne_zero (trace_mul_ne_zero hψ' ha') h0, ?_⟩
  refine ext_of_inf hψ'.1 (hψ.1.comp (continuous_const.mul continuous_id)) ψ'.map_add_eq_mul
    (fun x y => by rw [mul_add, ψ.map_add_eq_mul]) hψ'.2.2.1 (fun x => by rw [← map_mul, hψ.2.2.1]) fun x => ?_
  have e : algebraMap F (AF F) (a' / a) * pairA F (algebraMap F _ x) 0 =
      pairA F (algebraMap F _ (a' / a * x)) 0 :=
    Prod.ext (map_mul (algebraMap F (Ainf F)) _ _).symm (mul_zero _)
  rw [e, ha, ha', ← mul_assoc, mul_div_cancel₀ _ h0]

end GlobalTheory.AdeleCharTwist
