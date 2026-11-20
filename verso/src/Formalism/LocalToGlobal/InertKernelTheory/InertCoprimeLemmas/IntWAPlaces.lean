import Mathlib
import Formalism.PeriodIntegrals.UnimodGenus
import Formalism.PeriodIntegrals.UnitaryApproxFin
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnitaryApproxFin
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntWeak

noncomputable section

open NumberField IsDedekindDomain TensorProduct Matrix

namespace Formalism.L2.KerInert.WAP

def fixF (E : Type) [Field E] [StarRing E] : Subfield E :=
  RingHom.eqLocusField (starRingEnd E) (RingHom.id E)

variable {E : Type} [Field E] [NumberField E] [StarRing E]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_fixF {x : E} : x ∈ fixF E ↔ star x = x := Iff.rfl

def sig (E : Type) [Field E] [StarRing E] : E →ₐ[fixF E] E :=
  { starRingEnd E with commutes' := fun r => r.2 }

def cj (E : Type) [Field E] [StarRing E] : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (starRingEnd E)

def phi (E : Type) [Field E] [StarRing E] : 𝓞 (fixF E) →+* 𝓞 E :=
  RingOfIntegers.mapRingHom (algebraMap (fixF E) E)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem phi_coe (a : 𝓞 (fixF E)) : ((phi E a : 𝓞 E) : E) = ((a : fixF E) : E) := rfl

/- English proof (translation)
Set `f : fixF E` to `⟨(w : E), hw⟩`. Establish `hf : IsIntegral ℤ f`. Establish `hinj : Function.Injective ((algebraMap (fixF E) E).toIntAlgHom)` using `(algebraMap (fixF E) E).injective`. Rewrite using `[← isIntegral_algHom_iff _ hinj]`. Conclude with `w.2`.

Use `⟨⟨f, hf⟩, ?_⟩` and prove the remaining obligations. Conclude with `RingOfIntegers.ext rfl`.
-/
theorem lift_fixed (w : 𝓞 E) (hw : star (w : E) = w) : ∃ r : 𝓞 (fixF E), phi E r = w := by
  let f : fixF E := ⟨(w : E), hw⟩
  have hf : IsIntegral ℤ f := by
    have hinj : Function.Injective ((algebraMap (fixF E) E).toIntAlgHom) := (algebraMap (fixF E) E).injective
    rw [← isIntegral_algHom_iff _ hinj]
    exact w.2
  refine ⟨⟨f, hf⟩, ?_⟩
  exact RingOfIntegers.ext rfl

/- English proof (translation)
Apply `lift_fixed` to reduce the goal to its premises. Rewrite using `[show ((s * cj E s : 𝓞 E) : E) = (s : E) * star (s : E) from rfl, star_mul', star_star, mul_comm]`.
-/
theorem exists_norm (s : 𝓞 E) : ∃ r : 𝓞 (fixF E), phi E r = s * cj E s := by
  apply lift_fixed
  rw [show ((s * cj E s : 𝓞 E) : E) = (s : E) * star (s : E) from rfl, star_mul', star_star, mul_comm]

end Formalism.L2.KerInert.WAP

namespace Formalism.L2.KerInert.WAP

variable {E : Type} [Field E] [NumberField E] [StarRing E]

/- English proof (translation)
Establish `ht : (∀ t : 𝓞 E, algebraMap (𝓞 E) E t = star (algebraMap (𝓞 E) E s) → t ∉ P) ↔ cj E s ∉ P`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `h (cj E s) rfl`. Introduce `h t ht`.

Establish `: t = cj E s` using `RingOfIntegers.ext ht`. Rewrite using `[this]`. Conclude with `h`. Rewrite using `[ht, Ideal.mem_comap, hr, hP.mul_mem_iff_mem_or_mem, not_or]`.
-/
theorem gen_iff (P : Ideal (𝓞 E)) (hP : P.IsPrime) (s : 𝓞 E) (r : 𝓞 (fixF E)) (hr : phi E r = s * cj E s) :
    (s ∉ P ∧ ∀ t : 𝓞 E, algebraMap (𝓞 E) E t = star (algebraMap (𝓞 E) E s) → t ∉ P) ↔
      r ∉ P.comap (phi E) := by
  have ht : (∀ t : 𝓞 E, algebraMap (𝓞 E) E t = star (algebraMap (𝓞 E) E s) → t ∉ P) ↔ cj E s ∉ P := by
    constructor
    · intro h
      exact h (cj E s) rfl
    · intro h t ht
      have : t = cj E s := RingOfIntegers.ext ht
      rw [this]
      exact h
  rw [ht, Ideal.mem_comap, hr, hP.mul_mem_iff_mem_or_mem, not_or]

/- English proof (translation)
Unfold `PI.UG.hcompl`. Use `congr 1`. Use extensionality with `s`. Take `⟨r, hr⟩` from `exists_norm s`. Use `show (s ∉ P ∧ _) ↔ (s ∉ P' ∧ _)`.

Rewrite using `[gen_iff P hP s r hr, gen_iff P' hP' s r hr, h]`.
-/
theorem hcompl_eq (P P' : Ideal (𝓞 E)) (hP : P.IsPrime) (hP' : P'.IsPrime)
    (h : P.comap (phi E) = P'.comap (phi E)) :
    PI.UG.hcompl (K := E) P = PI.UG.hcompl (K := E) P' := by
  unfold PI.UG.hcompl
  congr 1
  ext s
  obtain ⟨r, hr⟩ := exists_norm s
  show (s ∉ P ∧ _) ↔ (s ∉ P' ∧ _)
  rw [gen_iff P hP s r hr, gen_iff P' hP' s r hr, h]

/- English proof (translation)
Unfold `PI.UG.loc`. Rewrite using `[hcompl_eq P P' hP hP' h]`.
-/
theorem loc_eq (P P' : Ideal (𝓞 E)) (hP : P.IsPrime) (hP' : P'.IsPrime)
    (h : P.comap (phi E) = P'.comap (phi E)) {n : ℕ} (N : Submodule (𝓞 E) (PI.UG.Sp E n)) :
    PI.UG.loc (K := E) P N = PI.UG.loc (K := E) P' N := by
  unfold PI.UG.loc
  rw [hcompl_eq P P' hP hP' h]

def tau (y : E) : E →ₗ[fixF E] fixF E where
  toFun e := ⟨e * y + star (e * y), by rw [mem_fixF, star_add, star_star, add_comm]⟩
  map_add' a b := Subtype.ext (by
    show (a + b) * y + star ((a + b) * y) = (a * y + star (a * y)) + (b * y + star (b * y))
    rw [add_mul, star_add]
    ring)
  map_smul' c e := Subtype.ext (by
    show ((c : E) * e) * y + star (((c : E) * e) * y) = (c : E) * (e * y + star (e * y))
    rw [star_mul', star_mul', star_mul', show star (c : E) = c from c.2]
    ring)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tau_coe (y e : E) : ((tau y e : fixF E) : E) = e * y + star (e * y) := rfl

def Phi (v : HeightOneSpectrum (𝓞 (fixF E))) (y : E) :
    E ⊗[fixF E] v.adicCompletion (fixF E) →ₗ[fixF E] v.adicCompletion (fixF E) :=
  (TensorProduct.lid (fixF E) (v.adicCompletion (fixF E))).toLinearMap ∘ₗ (tau y).rTensor _

/- English proof (translation)
Use `show TensorProduct.lid (fixF E) (v.adicCompletion (fixF E)) (LinearMap.rTensor _ (tau y) (e ⊗ₜ r)) = _`. Rewrite using `[LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Algebra.smul_def]`.
-/
theorem Phi_tmul (v : HeightOneSpectrum (𝓞 (fixF E))) (y e : E) (r : v.adicCompletion (fixF E)) :
    Phi v y (e ⊗ₜ r) = algebraMap (fixF E) (v.adicCompletion (fixF E)) (tau y e) * r := by
  show TensorProduct.lid (fixF E) (v.adicCompletion (fixF E)) (LinearMap.rTensor _ (tau y) (e ⊗ₜ r)) = _
  rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Algebra.smul_def]

/- English proof (translation)
Use `show Valued.v ((algebraMap (𝓞 (fixF E)) (fixF E) r : fixF E) : v.adicCompletion (fixF E)) ≤ 1`. Rewrite using `[HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`. Conclude with `v.valuation_le_one r`.
-/
theorem int_mem (v : HeightOneSpectrum (𝓞 (fixF E))) (r : 𝓞 (fixF E)) :
    algebraMap (fixF E) (v.adicCompletion (fixF E)) (algebraMap (𝓞 (fixF E)) (fixF E) r) ∈
      v.adicCompletionIntegers (fixF E) := by
  show Valued.v ((algebraMap (𝓞 (fixF E)) (fixF E) r : fixF E) : v.adicCompletion (fixF E)) ≤ 1
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact v.valuation_le_one r

/- English proof (translation)
Take `⟨r, hr⟩` from `lift_fixed (a * b + cj E (a * b)) (by`. Rewrite using `[show (((a * b + cj E (a * b)) : 𝓞 E) : E) = (a : E) * b + star ((a : E) * b) from rfl, star_add, star_star, add_comm])`. Establish `: tau (b : E) (a : E) = algebraMap (𝓞 (fixF E)) (fixF E) r`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[tau_coe]`.

Use `congrArg (fun z : 𝓞 E => (z : E)) hr` as an intermediate fact. Simplify using `only [phi_coe] at this`. Rewrite using `[show ((algebraMap (𝓞 (fixF E)) (fixF E) r : fixF E) : E) = ((r : fixF E) : E) from rfl, this]`. Both sides reduce to the same expression. Rewrite using `[this]`.

Conclude with `int_mem v r`.
-/
theorem tau_int (v : HeightOneSpectrum (𝓞 (fixF E))) (a b : 𝓞 E) :
    algebraMap (fixF E) (v.adicCompletion (fixF E)) (tau (b : E) (a : E)) ∈ v.adicCompletionIntegers (fixF E) := by
  obtain ⟨r, hr⟩ := lift_fixed (a * b + cj E (a * b)) (by
    rw [show (((a * b + cj E (a * b)) : 𝓞 E) : E) = (a : E) * b + star ((a : E) * b) from rfl,
      star_add, star_star, add_comm])
  have : tau (b : E) (a : E) = algebraMap (𝓞 (fixF E)) (fixF E) r := by
    apply Subtype.ext
    rw [tau_coe]
    have := congrArg (fun z : 𝓞 E => (z : E)) hr
    simp only [phi_coe] at this
    rw [show ((algebraMap (𝓞 (fixF E)) (fixF E) r : fixF E) : E) = ((r : fixF E) : E) from rfl, this]
    rfl
  rw [this]
  exact int_mem v r

/- English proof (translation)
Set `f : 𝓞 E →ₐ[ℤ] E ⊗[fixF E] v.adicCompletion (fixF E)` to `((PI.UnitaryApproxDefs.inclE (F := fixF E) (v.adicCompletion (fixF E))).comp (algebraMap (𝓞 E) E)).toIntAlgHom`. Set `g : (v.adicCompletionIntegers (fixF E)) →ₐ[ℤ] E ⊗[fixF E] v.adicCompletion (fixF E)` to `((Algebra.TensorProduct.includeRight (R := fixF E) (A := E)).toRingHom.comp (v.adicCompletionIntegers (fixF E)).toSubring.subtype).toIntAlgHom`. Establish `hle : PI.UnitaryApproxDefs.tensInt (F` using `fixF E) (v.adicCompletion (fixF E)) (PI.UnitaryApproxDefs.intOE E) (v.adicCompletionIntegers (fixF E)).toSubring ≤ (Algebra.TensorProduct.productMap f g).range.toSubring := by`. Unfold `PI.UnitaryApproxDefs.tensInt`. Rewrite using `[Subring.closure_le]`.

Introduce and unpack `_ (⟨⟨x, a, rfl⟩, rfl⟩ | ⟨y, rfl⟩)`. Use `⟨a ⊗ₜ 1, ?_⟩ show Algebra.TensorProduct.productMap f g (a ⊗ₜ 1) = _` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one]`. Both sides reduce to the same expression. Use `⟨1 ⊗ₜ y, ?_⟩ show Algebra.TensorProduct.productMap f g (1 ⊗ₜ y) = _` and prove the remaining obligations.

Rewrite using `[Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul]`. Both sides reduce to the same expression. Take `⟨t, rfl⟩` from `hle hz`. Use `clear hz hle`. Use `show Phi v (b : E) (Algebra.TensorProduct.productMap f g t) ∈ _`.

Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a c`. Establish `e1 : (Algebra.TensorProduct.productMap f g) (a ⊗ₜ c) = (a : E) ⊗ₜ ((c : v.adicCompletion (fixF E)))`. Rewrite using `[Algebra.TensorProduct.productMap_apply_tmul]`.

Use `show ((a : E) ⊗ₜ (1 : v.adicCompletion (fixF E))) * ((1 : E) ⊗ₜ (c : v.adicCompletion (fixF E))) = _`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Rewrite using `[e1, Phi_tmul]`. Conclude with `mul_mem (tau_int v a b) c.2`. Consider the case `add x y hx hy`.

Rewrite using `[map_add, map_add]`. Conclude with `add_mem hx hy`.
-/
theorem Phi_tensInt (v : HeightOneSpectrum (𝓞 (fixF E))) (b : 𝓞 E) {z : E ⊗[fixF E] v.adicCompletion (fixF E)}
    (hz : z ∈ PI.UnitaryApproxDefs.tensInt (F := fixF E) (v.adicCompletion (fixF E)) (PI.UnitaryApproxDefs.intOE E)
      (v.adicCompletionIntegers (fixF E)).toSubring) :
    Phi v (b : E) z ∈ v.adicCompletionIntegers (fixF E) := by
  let f : 𝓞 E →ₐ[ℤ] E ⊗[fixF E] v.adicCompletion (fixF E) :=
    ((PI.UnitaryApproxDefs.inclE (F := fixF E) (v.adicCompletion (fixF E))).comp (algebraMap (𝓞 E) E)).toIntAlgHom
  let g : (v.adicCompletionIntegers (fixF E)) →ₐ[ℤ] E ⊗[fixF E] v.adicCompletion (fixF E) :=
    ((Algebra.TensorProduct.includeRight (R := fixF E) (A := E)).toRingHom.comp
      (v.adicCompletionIntegers (fixF E)).toSubring.subtype).toIntAlgHom
  have hle : PI.UnitaryApproxDefs.tensInt (F := fixF E) (v.adicCompletion (fixF E)) (PI.UnitaryApproxDefs.intOE E)
      (v.adicCompletionIntegers (fixF E)).toSubring ≤ (Algebra.TensorProduct.productMap f g).range.toSubring := by
    unfold PI.UnitaryApproxDefs.tensInt
    rw [Subring.closure_le]
    rintro _ (⟨⟨x, a, rfl⟩, rfl⟩ | ⟨y, rfl⟩)
    · refine ⟨a ⊗ₜ 1, ?_⟩
      show Algebra.TensorProduct.productMap f g (a ⊗ₜ 1) = _
      rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one]
      rfl
    · refine ⟨1 ⊗ₜ y, ?_⟩
      show Algebra.TensorProduct.productMap f g (1 ⊗ₜ y) = _
      rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul]
      rfl
  obtain ⟨t, rfl⟩ := hle hz
  clear hz hle
  show Phi v (b : E) (Algebra.TensorProduct.productMap f g t) ∈ _
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a c =>
    have e1 : (Algebra.TensorProduct.productMap f g) (a ⊗ₜ c) = (a : E) ⊗ₜ ((c : v.adicCompletion (fixF E))) := by
      rw [Algebra.TensorProduct.productMap_apply_tmul]
      show ((a : E) ⊗ₜ (1 : v.adicCompletion (fixF E))) * ((1 : E) ⊗ₜ (c : v.adicCompletion (fixF E))) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e1, Phi_tmul]
    exact mul_mem (tau_int v a b) c.2
  | add x y hx hy =>
    rw [map_add, map_add]
    exact add_mem hx hy

end Formalism.L2.KerInert.WAP

namespace Formalism.L2.KerInert.WAP

variable {E : Type} [Field E] [NumberField E] [StarRing E]

/- English proof (translation)
Establish `h1 : v.valuation (fixF E) f ≤ 1`. Rewrite using `[← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`. Conclude with `hf`. Establish `h2 : f ∈ (v.valuation (fixF E)).valuationSubring` using `h1`. Rewrite `h2` using `[← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]`.

Take `⟨a, s, hs, hx⟩` from `h2`. Establish `hs1 : s ∉ v.asIdeal` using `hs`. Use `⟨a, s, hs1, ?_⟩` and prove the remaining obligations. Establish `hs' : s ≠ 0` using `fun h => hs1 (h ▸ v.asIdeal.zero_mem)`. Establish `hs0 : algebraMap (𝓞 (fixF E)) (fixF E) s ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective (𝓞 (fixF E)) (fixF E))).mpr hs'`.

Rewrite using `[hx, mul_assoc, inv_mul_cancel₀ hs0, mul_one]`.
-/
theorem loc_of_mem (v : HeightOneSpectrum (𝓞 (fixF E))) (f : fixF E)
    (hf : algebraMap (fixF E) (v.adicCompletion (fixF E)) f ∈ v.adicCompletionIntegers (fixF E)) :
    ∃ a s : 𝓞 (fixF E), s ∉ v.asIdeal ∧
      f * algebraMap (𝓞 (fixF E)) (fixF E) s = algebraMap (𝓞 (fixF E)) (fixF E) a := by
  have h1 : v.valuation (fixF E) f ≤ 1 := by
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hf
  have h2 : f ∈ (v.valuation (fixF E)).valuationSubring := h1
  rw [← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring] at h2
  obtain ⟨a, s, hs, hx⟩ := h2
  have hs1 : s ∉ v.asIdeal := hs
  refine ⟨a, s, hs1, ?_⟩
  have hs' : s ≠ 0 := fun h => hs1 (h ▸ v.asIdeal.zero_mem)
  have hs0 : algebraMap (𝓞 (fixF E)) (fixF E) s ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 (fixF E)) (fixF E))).mpr hs'
  rw [hx, mul_assoc, inv_mul_cancel₀ hs0, mul_one]

def LocInt (v : HeightOneSpectrum (𝓞 (fixF E))) (e : E) : Prop :=
  ∃ (a : 𝓞 E) (s : 𝓞 (fixF E)), s ∉ v.asIdeal ∧ algebraMap (𝓞 E) E (phi E s) * e = algebraMap (𝓞 E) E a

variable {v : HeightOneSpectrum (𝓞 (fixF E))}

/- English proof (translation)
Introduce `h` and use `v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)`.
-/
theorem one_notMem : (1 : 𝓞 (fixF E)) ∉ v.asIdeal := fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)

/- English proof (translation)
Introduce `h` and use `(v.isPrime.mem_or_mem h).elim hs ht`.
-/
theorem mul_notMem {s t : 𝓞 (fixF E)} (hs : s ∉ v.asIdeal) (ht : t ∉ v.asIdeal) : s * t ∉ v.asIdeal :=
  fun h => (v.isPrime.mem_or_mem h).elim hs ht

/- English proof (translation)
Assemble the required witnesses or components as `⟨a, 1, one_notMem, by rw [map_one, map_one, one_mul]⟩`.
-/
theorem locInt_int (a : 𝓞 E) : LocInt v (algebraMap (𝓞 E) E a) :=
  ⟨a, 1, one_notMem, by rw [map_one, map_one, one_mul]⟩

/- English proof (translation)
Take `⟨a₁, s₁, hs₁, h₁⟩` from `h₁`. Take `⟨a₂, s₂, hs₂, h₂⟩` from `h₂`. Use `⟨phi E s₂ * a₁ + phi E s₁ * a₂, s₁ * s₂, mul_notMem hs₁ hs₂, ?_⟩` and prove the remaining obligations. Simplify using `only [map_add, map_mul]`. Rewrite using `[← h₁, ← h₂]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem locInt_add {e₁ e₂ : E} (h₁ : LocInt v e₁) (h₂ : LocInt v e₂) : LocInt v (e₁ + e₂) := by
  obtain ⟨a₁, s₁, hs₁, h₁⟩ := h₁
  obtain ⟨a₂, s₂, hs₂, h₂⟩ := h₂
  refine ⟨phi E s₂ * a₁ + phi E s₁ * a₂, s₁ * s₂, mul_notMem hs₁ hs₂, ?_⟩
  simp only [map_add, map_mul]
  rw [← h₁, ← h₂]
  ring

/- English proof (translation)
Take `⟨a₁, s₁, hs₁, h₁⟩` from `h₁`. Take `⟨a₂, s₂, hs₂, h₂⟩` from `h₂`. Use `⟨a₁ * a₂, s₁ * s₂, mul_notMem hs₁ hs₂, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, map_mul, ← h₁, ← h₂]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem locInt_mul {e₁ e₂ : E} (h₁ : LocInt v e₁) (h₂ : LocInt v e₂) : LocInt v (e₁ * e₂) := by
  obtain ⟨a₁, s₁, hs₁, h₁⟩ := h₁
  obtain ⟨a₂, s₂, hs₂, h₂⟩ := h₂
  refine ⟨a₁ * a₂, s₁ * s₂, mul_notMem hs₁ hs₂, ?_⟩
  rw [map_mul, map_mul, map_mul, ← h₁, ← h₂]
  ring

/- English proof (translation)
Take `⟨a, s, hs, h⟩` from `h`. Use `⟨-a, s, hs, ?_⟩` and prove the remaining obligations. Rewrite using `[map_neg, ← h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem locInt_neg {e : E} (h : LocInt v e) : LocInt v (-e) := by
  obtain ⟨a, s, hs, h⟩ := h
  refine ⟨-a, s, hs, ?_⟩
  rw [map_neg, ← h]
  ring

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `locInt_add h₁ (locInt_neg h₂)`.
-/
theorem locInt_sub {e₁ e₂ : E} (h₁ : LocInt v e₁) (h₂ : LocInt v e₂) : LocInt v (e₁ - e₂) := by
  rw [sub_eq_add_neg]
  exact locInt_add h₁ (locInt_neg h₂)

/- English proof (translation)
Simplify using `using locInt_int (v := v) (0 : 𝓞 E)`.
-/
theorem locInt_zero : LocInt v (0 : E) := by
  simpa using locInt_int (v := v) (0 : 𝓞 E)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using locInt_zero`. Consider the case `insert i s hi ih`. Rewrite using `[Finset.sum_insert hi]`. Conclude with `locInt_add (h i (Finset.mem_insert_self i s)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))`.
-/
theorem locInt_sum {ι : Type} (s : Finset ι) (f : ι → E) (h : ∀ i ∈ s, LocInt v (f i)) :
    LocInt v (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using locInt_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact locInt_add (h i (Finset.mem_insert_self i s)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/- English proof (translation)
The claim follows from `(s : fixF E).2`.
-/
theorem star_phi (s : 𝓞 (fixF E)) : star (algebraMap (𝓞 E) E (phi E s)) = algebraMap (𝓞 E) E (phi E s) :=
  (s : fixF E).2

/- English proof (translation)
Take `⟨a, s, hs, h⟩` from `h`. Use `⟨cj E a, s, hs, ?_⟩` and prove the remaining obligations. Rewrite using `[← star_phi s, ← star_mul', h]`. Both sides reduce to the same expression.
-/
theorem locInt_star {e : E} (h : LocInt v e) : LocInt v (star e) := by
  obtain ⟨a, s, hs, h⟩ := h
  refine ⟨cj E a, s, hs, ?_⟩
  rw [← star_phi s, ← star_mul', h]
  rfl

/- English proof (translation)
Take `⟨a, s, hs, h⟩` from `loc_of_mem v f hf`. Use `⟨phi E a, s, hs, ?_⟩` and prove the remaining obligations. Establish `h'` using `congrArg (fun z : fixF E => (z : E)) h`. Simplify using `only [Subfield.coe_mul] at h'`. Rewrite using `[mul_comm]`.

Conclude with `h'`.
-/
theorem locInt_fix (f : fixF E)
    (hf : algebraMap (fixF E) (v.adicCompletion (fixF E)) f ∈ v.adicCompletionIntegers (fixF E)) :
    LocInt v (f : E) := by
  obtain ⟨a, s, hs, h⟩ := loc_of_mem v f hf
  refine ⟨phi E a, s, hs, ?_⟩
  have h' := congrArg (fun z : fixF E => (z : E)) h
  simp only [Subfield.coe_mul] at h'
  rw [mul_comm]
  exact h'

/- English proof (translation)
Establish `hT : ∀ b : 𝓞 E, LocInt v ((tau (b : E) x : fixF E) : E)`. Introduce `b`. Apply `locInt_fix` to reduce the goal to its premises. Establish `h` using `Phi_tensInt v b hx`. Rewrite `h` using `[show PI.UnitaryApproxDefs.inclE (F := fixF E) (v.adicCompletion (fixF E)) x = x ⊗ₜ 1 from rfl, Phi_tmul, mul_one]`.

Conclude with `h`. Establish `h0` using `hT 1`. Establish `h1` using `hT θ`. Establish `hs : LocInt v (star (θ : E))` using `locInt_int (cj E θ)`. Establish `e : ((θ : E) - star (θ : E)) * x = ((tau (θ : E) x : fixF E) : E) - ((tau ((1 : 𝓞 E) : E) x : fixF E) : E) * star (θ : E)`.

Rewrite using `[tau_coe, tau_coe, show ((1 : 𝓞 E) : E) = 1 from rfl]`. Simplify using `only [star_mul', mul_one]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `locInt_sub h1 (locInt_mul h0 hs)`.
-/
theorem locInt_of_tens (θ : 𝓞 E) {x : E}
    (hx : PI.UnitaryApproxDefs.inclE (F := fixF E) (v.adicCompletion (fixF E)) x ∈
      PI.UnitaryApproxDefs.tensInt (F := fixF E) (v.adicCompletion (fixF E)) (PI.UnitaryApproxDefs.intOE E)
        (v.adicCompletionIntegers (fixF E)).toSubring) :
    LocInt v (((θ : E) - star (θ : E)) * x) := by
  have hT : ∀ b : 𝓞 E, LocInt v ((tau (b : E) x : fixF E) : E) := by
    intro b
    apply locInt_fix
    have h := Phi_tensInt v b hx
    rw [show PI.UnitaryApproxDefs.inclE (F := fixF E) (v.adicCompletion (fixF E)) x = x ⊗ₜ 1 from rfl,
      Phi_tmul, mul_one] at h
    exact h
  have h0 := hT 1
  have h1 := hT θ
  have hs : LocInt v (star (θ : E)) := locInt_int (cj E θ)
  have e : ((θ : E) - star (θ : E)) * x =
      ((tau (θ : E) x : fixF E) : E) - ((tau ((1 : 𝓞 E) : E) x : fixF E) : E) * star (θ : E) := by
    rw [tau_coe, tau_coe, show ((1 : 𝓞 E) : E) = 1 from rfl]
    simp only [star_mul', mul_one]
    ring
  rw [e]
  exact locInt_sub h1 (locInt_mul h0 hs)

/- English proof (translation)
Take `⟨y, hy, h⟩` from `exists_integral_multiples ℤ ℚ s`. Use `⟨y, hy, fun x hx => ⟨⟨y • x, (mem_integralClosure_iff ℤ E).mpr (h x hx)⟩, ?_⟩⟩` and prove the remaining obligations. Use `show (y • x : E) = (y : E) * x`. Conclude with `zsmul_eq_mul _ _`.
-/
theorem exists_int_mul (s : Finset E) :
    ∃ c : ℤ, c ≠ 0 ∧ ∀ x ∈ s, ∃ a : 𝓞 E, algebraMap (𝓞 E) E a = (c : E) * x := by
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ s
  refine ⟨y, hy, fun x hx => ⟨⟨y • x, (mem_integralClosure_iff ℤ E).mpr (h x hx)⟩, ?_⟩⟩
  show (y • x : E) = (y : E) * x
  exact zsmul_eq_mul _ _

end Formalism.L2.KerInert.WAP

namespace Formalism.L2.KerInert.WAP

variable {E : Type} [Field E] [NumberField E] [StarRing E]

/- English proof (translation)
Use extensionality with `i j`. Both sides reduce to the same expression.
-/
theorem cT_sig {m : Type} (M : Matrix m m E) : PI.UnitaryApproxDefs.cT (sig E : E →+* E) M = star M := by
  ext i j
  rfl

/- English proof (translation)
Use `show Algebra.TensorProduct.map (sig E) (AlgHom.id (fixF E) R) (e ⊗ₜ 1) = star e ⊗ₜ 1`. Rewrite using `[Algebra.TensorProduct.map_tmul]`. Both sides reduce to the same expression.
-/
theorem sigR_inclE (R : Type) [CommRing R] [Algebra (fixF E) R] (e : E) :
    PI.UnitaryApproxDefs.sigR (sig E) R (PI.UnitaryApproxDefs.inclE (F := fixF E) R e) =
      PI.UnitaryApproxDefs.inclE (F := fixF E) R (star e) := by
  show Algebra.TensorProduct.map (sig E) (AlgHom.id (fixF E) R) (e ⊗ₜ 1) = star e ⊗ₜ 1
  rw [Algebra.TensorProduct.map_tmul]
  rfl

def glOf {n : ℕ} (M : Matrix (Fin n) (Fin n) E) (h : M ∈ Matrix.unitaryGroup (Fin n) E) : GL (Fin n) E :=
  ⟨M, star M, Matrix.mem_unitaryGroup_iff.mp h, Matrix.mem_unitaryGroup_iff'.mp h⟩

/- English proof (translation)
Establish `key : PI.UnitaryApproxDefs.cT (PI.UnitaryApproxDefs.sigR (sig E) R) (M.map (PI.UnitaryApproxDefs.inclE (F` using `fixF E) R)) = (star M).map (PI.UnitaryApproxDefs.inclE (F := fixF E) R) := by`. Use extensionality with `i j`. Use `show PI.UnitaryApproxDefs.sigR (sig E) R (PI.UnitaryApproxDefs.inclE (F := fixF E) R (M j i)) = PI.UnitaryApproxDefs.inclE (F := fixF E) R (star (M j i))`. Conclude with `sigR_inclE R (M j i)`. Use `show PI.UnitaryApproxDefs.cT (PI.UnitaryApproxDefs.sigR (sig E) R) (M.map (PI.UnitaryApproxDefs.inclE (F := fixF E) R)) * (1 : Matrix (Fin n) (Fin n) E).map (PI.UnitaryApproxDefs.inclE (F := fixF E) R) * M.map (PI.UnitaryApproxDefs.inclE (F := fixF E) R) = (1 : Matrix (Fin n) (Fi …`.

Rewrite using `[key, Matrix.map_one _ (map_zero _) (map_one _), mul_one, ← Matrix.map_mul, Matrix.mem_unitaryGroup_iff'.mp h, Matrix.map_one _ (map_zero _) (map_one _)]`.
-/
theorem map_mem_UPts {n : ℕ} (R : Type) [CommRing R] [Algebra (fixF E) R]
    (M : Matrix (Fin n) (Fin n) E) (h : M ∈ Matrix.unitaryGroup (Fin n) E) :
    Units.map (RingHom.mapMatrix (PI.UnitaryApproxDefs.inclE (F := fixF E) R)).toMonoidHom (glOf M h) ∈
      PI.UnitaryApproxDefs.UPts (sig E) (1 : Matrix (Fin n) (Fin n) E) R := by
  have key : PI.UnitaryApproxDefs.cT (PI.UnitaryApproxDefs.sigR (sig E) R) (M.map (PI.UnitaryApproxDefs.inclE (F := fixF E) R)) =
      (star M).map (PI.UnitaryApproxDefs.inclE (F := fixF E) R) := by
    ext i j
    show PI.UnitaryApproxDefs.sigR (sig E) R (PI.UnitaryApproxDefs.inclE (F := fixF E) R (M j i)) =
      PI.UnitaryApproxDefs.inclE (F := fixF E) R (star (M j i))
    exact sigR_inclE R (M j i)
  show PI.UnitaryApproxDefs.cT (PI.UnitaryApproxDefs.sigR (sig E) R) (M.map (PI.UnitaryApproxDefs.inclE (F := fixF E) R)) *
      (1 : Matrix (Fin n) (Fin n) E).map (PI.UnitaryApproxDefs.inclE (F := fixF E) R) *
        M.map (PI.UnitaryApproxDefs.inclE (F := fixF E) R) =
      (1 : Matrix (Fin n) (Fin n) E).map (PI.UnitaryApproxDefs.inclE (F := fixF E) R)
  rw [key, Matrix.map_one _ (map_zero _) (map_one _), mul_one, ← Matrix.map_mul,
    Matrix.mem_unitaryGroup_iff'.mp h, Matrix.map_one _ (map_zero _) (map_one _)]

def toEquiv {n : ℕ} (γ : GL (Fin n) E) : PI.UG.Sp E n ≃ₗ[E] PI.UG.Sp E n :=
  LinearEquiv.ofLinear (Matrix.toLin' (γ : Matrix (Fin n) (Fin n) E))
    (Matrix.toLin' ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E))
    (by rw [← Matrix.toLin'_mul, Units.mul_inv, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, Units.inv_mul, Matrix.toLin'_one])

/- English proof (translation)
Simplify using `[toEquiv, Matrix.toLin'_apply]`.
-/
theorem toEquiv_apply {n : ℕ} (γ : GL (Fin n) E) (x : PI.UG.Sp E n) :
    toEquiv γ x = (γ : Matrix (Fin n) (Fin n) E) *ᵥ x := by
  simp [toEquiv, Matrix.toLin'_apply]

/- English proof (translation)
Introduce `x y`. Rewrite using `[toEquiv_apply, toEquiv_apply, wa_hStd_apply, wa_hStd_apply]`. Establish `hd : ∀ z w : Fin n → E, Formalism.BasicNotions.stdH E n z w = star z ⬝ᵥ w` using `fun z w => rfl`. Rewrite using `[hd, hd, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose, hγ, Matrix.one_mulVec]`.
-/
theorem toEquiv_isom {n : ℕ} (γ : GL (Fin n) E) (hγ : star (γ : Matrix (Fin n) (Fin n) E) * γ = 1) :
    toEquiv γ ∈ PI.UG.isom (PI.UG.hStd E n) := by
  intro x y
  rw [toEquiv_apply, toEquiv_apply, wa_hStd_apply, wa_hStd_apply]
  have hd : ∀ z w : Fin n → E, Formalism.BasicNotions.stdH E n z w = star z ⬝ᵥ w := fun z w => rfl
  rw [hd, hd, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose,
    hγ, Matrix.one_mulVec]

def MLoc (v : HeightOneSpectrum (𝓞 (fixF E))) {n : ℕ} (M : Matrix (Fin n) (Fin n) E) : Prop := ∀ i j, LocInt v (M i j)

variable {v : HeightOneSpectrum (𝓞 (fixF E))} {n : ℕ}

/- English proof (translation)
Introduce `i j` and use `by rw [Matrix.mul_apply] exact locInt_sum _ _ fun k _ => locInt_mul (hM i k) (hN k j)`.
-/
theorem mloc_mul {M N : Matrix (Fin n) (Fin n) E} (hM : MLoc v M) (hN : MLoc v N) : MLoc v (M * N) := fun i j => by
  rw [Matrix.mul_apply]
  exact locInt_sum _ _ fun k _ => locInt_mul (hM i k) (hN k j)

/- English proof (translation)
Introduce `i j` and use `by rw [Matrix.star_apply] exact locInt_star (hM j i)`.
-/
theorem mloc_star {M : Matrix (Fin n) (Fin n) E} (hM : MLoc v M) : MLoc v (star M) := fun i j => by
  rw [Matrix.star_apply]
  exact locInt_star (hM j i)

/- English proof (translation)
Introduce `i j` and use `by rw [Matrix.sub_apply] exact locInt_sub (hM i j) (hN i j)`.
-/
theorem mloc_sub {M N : Matrix (Fin n) (Fin n) E} (hM : MLoc v M) (hN : MLoc v N) : MLoc v (M - N) := fun i j => by
  rw [Matrix.sub_apply]
  exact locInt_sub (hM i j) (hN i j)

/- English proof (translation)
Introduce `i j` and use `by rw [Matrix.one_apply] split_ifs · simpa using locInt_int (v := v) (1 : 𝓞 E) · exact locInt_zero`.
-/
theorem mloc_one : MLoc v (1 : Matrix (Fin n) (Fin n) E) := fun i j => by
  rw [Matrix.one_apply]
  split_ifs
  · simpa using locInt_int (v := v) (1 : 𝓞 E)
  · exact locInt_zero

/- English proof (translation)
Take `⟨s, hs, hsx⟩` from `hx`. Rewrite `hsx` using `[wa_mem_std]`. Establish `hsum : A *ᵥ x = ∑ i, ∑ j, (Pi.single i (A i j * x j) : PI.UG.Sp E n)`. Use function extensionality and compare the values at `k`. Simplify using `[Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.single_apply]`.

Rewrite using `[hsum]`. Use `Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Take `⟨a, t, ht, hta⟩` from `hA i j`. Take `⟨r, hr⟩` from `hsx j`. Establish `hr' : algebraMap (𝓞 E) E r = algebraMap (𝓞 E) E s * x j`.

Rewrite using `[hr, Pi.smul_apply, Algebra.smul_def]`. Establish `htQ : phi E t ∉ Q`. Rewrite using `[← Ideal.mem_comap, hv]`. Conclude with `ht`. Use `⟨phi E t * s, ?_, ?_⟩` and prove the remaining obligations.

Use `Submonoid.mul_mem _ (Submonoid.subset_closure ⟨htQ, ?_⟩) hs` and prove the remaining obligations. Introduce `t' ht'`. Establish `: t' = phi E t` using `RingOfIntegers.ext (ht'.trans (star_phi t))`. Rewrite using `[this]`. Conclude with `htQ`.

Rewrite using `[wa_mem_std]`. Introduce `k`. Distinguish the cases in `hk : k = i`. Rewrite using `[hk]`. Use `⟨a * r, ?_⟩` and prove the remaining obligations.

Rewrite using `[Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, map_mul, map_mul, ← hta, hr']`. Expand and normalize the polynomial expressions, which then agree. Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, Pi.single_eq_of_ne hk, smul_zero, map_zero]`.
-/
theorem mulVec_loc (Q : Ideal (𝓞 E)) (hv : Q.comap (phi E) = v.asIdeal) {A : Matrix (Fin n) (Fin n) E}
    (hA : MLoc v A) {x : PI.UG.Sp E n} (hx : x ∈ PI.UG.loc (K := E) Q (PI.UG.stdLat E n)) :
    A *ᵥ x ∈ PI.UG.loc (K := E) Q (PI.UG.stdLat E n) := by
  obtain ⟨s, hs, hsx⟩ := hx
  rw [wa_mem_std] at hsx
  have hsum : A *ᵥ x = ∑ i, ∑ j, (Pi.single i (A i j * x j) : PI.UG.Sp E n) := by
    funext k
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.single_apply]
  rw [hsum]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  obtain ⟨a, t, ht, hta⟩ := hA i j
  obtain ⟨r, hr⟩ := hsx j
  have hr' : algebraMap (𝓞 E) E r = algebraMap (𝓞 E) E s * x j := by
    rw [hr, Pi.smul_apply, Algebra.smul_def]
  have htQ : phi E t ∉ Q := by
    rw [← Ideal.mem_comap, hv]
    exact ht
  refine ⟨phi E t * s, ?_, ?_⟩
  · refine Submonoid.mul_mem _ (Submonoid.subset_closure ⟨htQ, ?_⟩) hs
    intro t' ht'
    have : t' = phi E t := RingOfIntegers.ext (ht'.trans (star_phi t))
    rw [this]
    exact htQ
  · rw [wa_mem_std]
    intro k
    by_cases hk : k = i
    · rw [hk]
      refine ⟨a * r, ?_⟩
      rw [Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, map_mul, map_mul, ← hta, hr']
      ring
    · refine ⟨0, ?_⟩
      rw [Pi.smul_apply, Pi.single_eq_of_ne hk, smul_zero, map_zero]

end Formalism.L2.KerInert.WAP

namespace Formalism.L2.KerInert.WAP

/- English proof (translation)
Establish `hc' : (c : E) ≠ 0` using `Int.cast_ne_zero.mpr hc0`. Establish `hcc : ((c * c : ℤ) : E) ≠ 0`. Use `push_cast`. Conclude with `mul_ne_zero hc' hc'`. Set `Y : Matrix (Fin n) (Fin n) E` to `fun i j => (c : E) * ((G i j - γ i j) / ((c * c : ℤ) : E))`.

Establish `hY : MLoc v Y`. Introduce `i j`. Take `⟨s, hs, hsx⟩` from `hcong i j`. Establish `hx : PI.UnitaryApproxDefs.inclE (F` using `fixF E) (v.adicCompletion (fixF E)) ((G i j - γ i j) / ((c * c : ℤ) : E)) ∈ PI.UnitaryApproxDefs.tensInt (F := fixF E) (v.adicCompletion (fixF E)) (PI.UnitaryApproxDefs.intOE E) (v.adicCompletionIntegers (fixF E)).toSubring := by`. Establish `e : PI.UnitaryApproxDefs.inclE (F` using `fixF E) (v.adicCompletion (fixF E)) ((G i j - γ i j) / ((c * c : ℤ) : E)) = s := by`.

Rewrite using `[div_eq_mul_inv, map_mul, map_sub, hsx, mul_comm _ s, mul_assoc, ← map_mul, mul_inv_cancel₀ hcc, map_one, mul_one]`. Rewrite using `[e]`. Conclude with `hs`. Establish `h1` using `locInt_of_tens (v := v) θ hx`. Take `⟨a, ha⟩` from `hcδ`.

Establish `h2 : LocInt v ((c : E) * ((θ : E) - star (θ : E))⁻¹)`. Rewrite using `[← ha]`. Conclude with `locInt_int a`. Establish `e : Y i j = ((c : E) * ((θ : E) - star (θ : E))⁻¹) * (((θ : E) - star (θ : E)) * ((G i j - γ i j) / ((c * c : ℤ) : E)))` using `by show (c : E) * _ = _`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e]`. Conclude with `locInt_mul h2 h1`. Establish `hGi : MLoc v ((c : E) • G)` using `fun i j => by`. Take `⟨a, ha⟩` from `hcG i j`. Rewrite using `[Matrix.smul_apply, smul_eq_mul, ← ha]`.

Conclude with `locInt_int a`. Establish `hγe : γ = G - (c : E) • Y`. Use extensionality with `i j`. Rewrite using `[Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]`. Use `show γ i j = G i j - (c : E) * ((c : E) * ((G i j - γ i j) / ((c * c : ℤ) : E)))`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hsc : star ((c : E) • G) = (c : E) • star G` using `by rw [star_smul, star_intCast]`. Establish `hGG : star G * G = 1` using `Matrix.mem_unitaryGroup_iff'.mp hG`.

Establish `hA : star G * γ = 1 - star ((c : E) • G) * Y`. Rewrite using `[hγe, Matrix.mul_sub, hGG, hsc, Matrix.mul_smul, Matrix.smul_mul]`. Establish `hB : star γ * G = 1 - star Y * ((c : E) • G)`. Rewrite using `[hγe, star_sub, Matrix.sub_mul, hGG, star_smul, star_intCast, Matrix.smul_mul, Matrix.mul_smul]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hA]`. Conclude with `mloc_sub mloc_one (mloc_mul (mloc_star hGi) hY)`. Rewrite using `[hB]`. Conclude with `mloc_sub mloc_one (mloc_mul (mloc_star hY) hGi)`.
-/
theorem local_step {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    (v : HeightOneSpectrum (𝓞 (fixF E))) (θ : 𝓞 E) (hδ : (θ : E) - star (θ : E) ≠ 0) (c : ℤ) (hc0 : c ≠ 0)
    (hcδ : ∃ a : 𝓞 E, algebraMap (𝓞 E) E a = (c : E) * ((θ : E) - star (θ : E))⁻¹)
    (G : Matrix (Fin n) (Fin n) E) (hG : G ∈ Matrix.unitaryGroup (Fin n) E)
    (hcG : ∀ i j, ∃ a : 𝓞 E, algebraMap (𝓞 E) E a = (c : E) * G i j)
    (γ : Matrix (Fin n) (Fin n) E)
    (hcong : ∀ i j, ∃ s ∈ PI.UnitaryApproxDefs.tensInt (F := fixF E) (v.adicCompletion (fixF E))
        (PI.UnitaryApproxDefs.intOE E) (v.adicCompletionIntegers (fixF E)).toSubring,
        PI.UnitaryApproxDefs.inclE (F := fixF E) (v.adicCompletion (fixF E)) (G i j) -
          PI.UnitaryApproxDefs.inclE (F := fixF E) (v.adicCompletion (fixF E)) (γ i j) =
        PI.UnitaryApproxDefs.inclE (F := fixF E) (v.adicCompletion (fixF E)) ((c * c : ℤ) : E) * s) :
    MLoc v (star G * γ) ∧ MLoc v (star γ * G) := by
  have hc' : (c : E) ≠ 0 := Int.cast_ne_zero.mpr hc0
  have hcc : ((c * c : ℤ) : E) ≠ 0 := by
    push_cast
    exact mul_ne_zero hc' hc'
  let Y : Matrix (Fin n) (Fin n) E := fun i j => (c : E) * ((G i j - γ i j) / ((c * c : ℤ) : E))
  have hY : MLoc v Y := by
    intro i j
    obtain ⟨s, hs, hsx⟩ := hcong i j
    have hx : PI.UnitaryApproxDefs.inclE (F := fixF E) (v.adicCompletion (fixF E))
        ((G i j - γ i j) / ((c * c : ℤ) : E)) ∈ PI.UnitaryApproxDefs.tensInt (F := fixF E) (v.adicCompletion (fixF E))
          (PI.UnitaryApproxDefs.intOE E) (v.adicCompletionIntegers (fixF E)).toSubring := by
      have e : PI.UnitaryApproxDefs.inclE (F := fixF E) (v.adicCompletion (fixF E))
          ((G i j - γ i j) / ((c * c : ℤ) : E)) = s := by
        rw [div_eq_mul_inv, map_mul, map_sub, hsx, mul_comm _ s, mul_assoc, ← map_mul, mul_inv_cancel₀ hcc,
          map_one, mul_one]
      rw [e]
      exact hs
    have h1 := locInt_of_tens (v := v) θ hx
    obtain ⟨a, ha⟩ := hcδ
    have h2 : LocInt v ((c : E) * ((θ : E) - star (θ : E))⁻¹) := by
      rw [← ha]
      exact locInt_int a
    have e : Y i j = ((c : E) * ((θ : E) - star (θ : E))⁻¹) *
        (((θ : E) - star (θ : E)) * ((G i j - γ i j) / ((c * c : ℤ) : E))) := by
      show (c : E) * _ = _
      field_simp
    rw [e]
    exact locInt_mul h2 h1
  have hGi : MLoc v ((c : E) • G) := fun i j => by
    obtain ⟨a, ha⟩ := hcG i j
    rw [Matrix.smul_apply, smul_eq_mul, ← ha]
    exact locInt_int a
  have hγe : γ = G - (c : E) • Y := by
    ext i j
    rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    show γ i j = G i j - (c : E) * ((c : E) * ((G i j - γ i j) / ((c * c : ℤ) : E)))
    push_cast
    field_simp
    ring
  have hsc : star ((c : E) • G) = (c : E) • star G := by rw [star_smul, star_intCast]
  have hGG : star G * G = 1 := Matrix.mem_unitaryGroup_iff'.mp hG
  have hA : star G * γ = 1 - star ((c : E) • G) * Y := by
    rw [hγe, Matrix.mul_sub, hGG, hsc, Matrix.mul_smul, Matrix.smul_mul]
  have hB : star γ * G = 1 - star Y * ((c : E) • G) := by
    rw [hγe, star_sub, Matrix.sub_mul, hGG, star_smul, star_intCast, Matrix.smul_mul, Matrix.mul_smul]
  refine ⟨?_, ?_⟩
  · rw [hA]
    exact mloc_sub mloc_one (mloc_mul (mloc_star hGi) hY)
  · rw [hB]
    exact mloc_sub mloc_one (mloc_mul (mloc_star hY) hGi)

end Formalism.L2.KerInert.WAP

namespace Formalism.L2.KerInert

open WAP in

/- English proof (translation)
Introduce `E _ _ _ hCM p hp n L hyp`. Take `⟨P0, hP0m, hP0⟩` from `Ideal.exists_le_maximal (Ideal.span {(p : 𝓞 E)}) (by rw [Ne, Ideal.span_singleton_eq_top]; exact wa_not_isUnit p hp)`. Take `⟨θ, t, hθt, hθP⟩` from `hCM.2.2 P0 hP0m`. Establish `hδ : (θ : E) - star (θ : E) ≠ 0`. Introduce `h0`.

Apply `hθP` to reduce the goal to its premises. Establish `h1 : (θ : E) = (t : E)`. Rewrite using `[show (t : E) = algebraMap (𝓞 E) E t from rfl, hθt]`. Conclude with `sub_eq_zero.mp h0`. Rewrite using `[show θ = t from RingOfIntegers.ext h1, sub_self]`.

Conclude with `P0.zero_mem`. Establish `hp0 : (p : 𝓞 (fixF E)) ≠ 0` using `Nat.cast_ne_zero.mpr hp.ne_zero`. Establish `hfin` using `Ideal.finite_factors (R := 𝓞 (fixF E)) (I := Ideal.span {(p : 𝓞 (fixF E))}) (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hp0)`. Set `T` to `hfin.toFinset`. Set `PS` to `{P : Ideal (𝓞 E) // P.IsMaximal ∧ (p : 𝓞 E) ∈ P}`.

Establish `hPp : ∀ P : PS, (p : 𝓞 (fixF E)) ∈ P.1.comap (phi E)` using `fun P => by`. Rewrite using `[Ideal.mem_comap, map_natCast]`. Conclude with `P.2.2`. Set `vOf : PS → HeightOneSpectrum (𝓞 (fixF E))` to `fun P => { asIdeal := P.1.comap (phi E) isPrime := by have := P.2.1.isPrime; exact Ideal.comap_isPrime _ _ ne_bot := fun h => hp0 (by have := hPp P; rw [h] at this; exact (Ideal.mem_bot).mp this) }`. Establish `hvT : ∀ P : PS, vOf P ∈ T` using `fun P => by`.

Rewrite using `[Set.Finite.mem_toFinset]`. Use `show (vOf P).asIdeal ∣ _`. Rewrite using `[Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `hPp P`. Establish `hyp' : ∀ P : PS, ∃ g ∈ PI.UG.isom (PI.UG.hStd E n), PI.UG.gmap g (PI.UG.loc (K` using `E) P.1 (PI.UG.stdLat E n)) = PI.UG.loc (K := E) P.1 L := fun P => hyp P.1 P.2.1 P.2.2`.

Use `choose G hGi hGl using hyp'`. Set `Gm : HeightOneSpectrum (𝓞 (fixF E)) → Matrix (Fin n) (Fin n) E` to `fun v => if h : ∃ P : PS, vOf P = v then LinearMap.toMatrix' (G h.choose : PI.UG.Sp E n →ₗ[E] PI.UG.Sp E n) else 1`. Establish `hGm : ∀ v, Gm v ∈ Matrix.unitaryGroup (Fin n) E` using `fun v => by`. Distinguish the cases in `h : ∃ P : PS, vOf P = v`. Simplify using `only [Gm, dif_pos h]`.

Conclude with `wa_unitary _ (hGi _)`. Simplify using `only [Gm, dif_neg h]`. Conclude with `one_mem _`. Set `gv : (v : HeightOneSpectrum (𝓞 (fixF E))) → GL (Fin n) (E ⊗[fixF E] v.adicCompletion (fixF E))` to `fun v => Units.map (RingHom.mapMatrix (PI.UnitaryApproxDefs.inclE (F := fixF E) (v.adicCompletion (fixF E)))).toMonoidHom (glOf (Gm v) (hGm v))`. Take `⟨c, hc0, hc⟩` from `exists_int_mul (insert ((θ : E) - star (θ : E))⁻¹ ((T ×ˢ (Finset.univ ×ˢ Finset.univ)).image (fun q : HeightOneSpectrum (𝓞 (fixF E)) × Fin n × Fin n => Gm q.1 q.2.1 q.2.2)))`.

Establish `hD : ((c * c : ℤ) : 𝓞 (fixF E)) ≠ 0` using `Int.cast_ne_zero.mpr (mul_ne_zero hc0 hc0)`. Take `⟨γ, hγ, hcong⟩` from `unitary_approximation_finite (fixF E) E (Fin n) (sig E) (1 : Matrix (Fin n) (Fin n) E) (fun e => star_star e) ⟨(θ : E), fun h => hδ (by rw [show star (θ : E) = (θ : E) from h, sub_self])⟩ (PI.UnitaryApproxDefs.cT_one _) (by simp) T gv (fun v _ => map_mem_UPts _ (Gm v) (hGm v)) (( …`. Establish `hγu : (γ : Matrix (Fin n) (Fin n) E) ∈ Matrix.unitaryGroup (Fin n) E`. Establish `h : PI.UnitaryApproxDefs.cT (sig E : E →+* E) (γ : Matrix (Fin n) (Fin n) E) * 1 * (γ : Matrix (Fin n) (Fin n) E) = 1` using `hγ`. Rewrite `h` using `[mul_one, cT_sig]`.

Conclude with `Matrix.mem_unitaryGroup_iff'.mpr h`. Use `⟨toEquiv γ, toEquiv_isom γ (Matrix.mem_unitaryGroup_iff'.mp hγu), fun P hPm hpP => ?_⟩` and prove the remaining obligations. Set `P' : PS` to `⟨P, hPm, hpP⟩`. Establish `hex : ∃ Q : PS, vOf Q = vOf P'` using `⟨P', rfl⟩`. Establish `hQv : vOf hex.choose = vOf P'` using `hex.choose_spec`.

Establish `hGmv : Gm (vOf P') = LinearMap.toMatrix' (G hex.choose : PI.UG.Sp E n →ₗ[E] PI.UG.Sp E n)`. Simplify using `only [Gm, dif_pos hex]`. Establish `hcomap : hex.choose.1.comap (phi E) = P.comap (phi E)` using `congrArg HeightOneSpectrum.asIdeal hQv`. Establish `hlocStd` using `loc_eq hex.choose.1 P hex.choose.2.1.isPrime hPm.isPrime hcomap (PI.UG.stdLat E n)`. Establish `hlocL` using `loc_eq hex.choose.1 P hex.choose.2.1.isPrime hPm.isPrime hcomap L`.

Establish `hGQ : PI.UG.gmap (G hex.choose) (PI.UG.loc (K` using `E) P (PI.UG.stdLat E n)) = PI.UG.loc (K := E) P L := by`. Rewrite using `[← hlocStd, ← hlocL]`. Conclude with `hGl hex.choose`. Establish `hvT' : vOf P' ∈ T` using `hvT P'`. Establish `hcG : ∀ i j, ∃ a : 𝓞 E, algebraMap (𝓞 E) E a = (c : E) * Gm (vOf P') i j` using `fun i j => hc (Gm (vOf P') i j) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨(vOf P', i, j), by simp [hvT'], rfl⟩))`.

Establish `hcδ` using `hc _ (Finset.mem_insert_self _ _)`. Establish `hcg : ∀ i j, ∃ s ∈ PI.UnitaryApproxDefs.tensInt (F` using `fixF E) ((vOf P').adicCompletion (fixF E)) (PI.UnitaryApproxDefs.intOE E) ((vOf P').adicCompletionIntegers (fixF E)).toSubring, PI.UnitaryApproxDefs.inclE (F := fixF E) ((vOf P').adicCompletion (fixF E)) (Gm (vOf P') i j) - PI.UnitaryApproxDefs.inclE (F := fixF E) ((vOf P').adicC …`. Introduce `i j`. Take `⟨s, hs, h⟩` from `hcong (vOf P') hvT' i j`. Use `⟨s, hs, ?_⟩` and prove the remaining obligations.

Establish `e1 : algebraMap (fixF E) E (((c * c : ℤ) : 𝓞 (fixF E)) : fixF E) = ((c * c : ℤ) : E)` using `by simp`. Rewrite using `[← e1]`. Conclude with `h`. Take `⟨hA, hB⟩` from `local_step (vOf P') θ hδ c hc0 hcδ (Gm (vOf P')) (hGm (vOf P')) hcG (γ : Matrix (Fin n) (Fin n) E) hcg`. Establish `hGu` using `hGm (vOf P')`.

Establish `hGG1 : Gm (vOf P') * star (Gm (vOf P')) = 1` using `Matrix.mem_unitaryGroup_iff.mp hGu`. Establish `hγ1 : (γ : Matrix (Fin n) (Fin n) E) * star (γ : Matrix (Fin n) (Fin n) E) = 1` using `Matrix.mem_unitaryGroup_iff.mp hγu`. Establish `hGA : Gm (vOf P') * (star (Gm (vOf P')) * γ) = γ`. Rewrite using `[← Matrix.mul_assoc, hGG1, Matrix.one_mul]`. Establish `hγB : (γ : Matrix (Fin n) (Fin n) E) * (star (γ : Matrix (Fin n) (Fin n) E) * Gm (vOf P')) = Gm (vOf P')`.

Rewrite using `[← Matrix.mul_assoc, hγ1, Matrix.one_mul]`. Establish `hGx : ∀ x, G hex.choose x = Gm (vOf P') *ᵥ x` using `fun x => by`. Rewrite using `[hGmv, LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe]`. Establish `hv' : P.comap (phi E) = (vOf P').asIdeal` using `rfl`. Rewrite using `[← hGQ]`.

Use extensionality with `y`. Simplify using `only [PI.UG.gmap, Submodule.mem_map, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Use `⟨(star (Gm (vOf P')) * (γ : Matrix (Fin n) (Fin n) E)) *ᵥ x, mulVec_loc P hv' hA hx, ?_⟩` and prove the remaining obligations.

Rewrite using `[hGx, Matrix.mulVec_mulVec, hGA, toEquiv_apply]`. Introduce and unpack `⟨x, hx, rfl⟩`. Use `⟨(star (γ : Matrix (Fin n) (Fin n) E) * Gm (vOf P')) *ᵥ x, mulVec_loc P hv' hB hx, ?_⟩` and prove the remaining obligations. Rewrite using `[toEquiv_apply, Matrix.mulVec_mulVec, hγB, hGx]`.
-/
theorem weak_approximation_places : WAPlaces := by
  intro E _ _ _ hCM p hp n L hyp
  classical
  obtain ⟨P0, hP0m, hP0⟩ := Ideal.exists_le_maximal (Ideal.span {(p : 𝓞 E)})
    (by rw [Ne, Ideal.span_singleton_eq_top]; exact wa_not_isUnit p hp)
  obtain ⟨θ, t, hθt, hθP⟩ := hCM.2.2 P0 hP0m
  have hδ : (θ : E) - star (θ : E) ≠ 0 := by
    intro h0
    apply hθP
    have h1 : (θ : E) = (t : E) := by
      rw [show (t : E) = algebraMap (𝓞 E) E t from rfl, hθt]
      exact sub_eq_zero.mp h0
    rw [show θ = t from RingOfIntegers.ext h1, sub_self]
    exact P0.zero_mem
  have hp0 : (p : 𝓞 (fixF E)) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hfin := Ideal.finite_factors (R := 𝓞 (fixF E)) (I := Ideal.span {(p : 𝓞 (fixF E))})
    (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hp0)
  let T := hfin.toFinset
  let PS := {P : Ideal (𝓞 E) // P.IsMaximal ∧ (p : 𝓞 E) ∈ P}
  have hPp : ∀ P : PS, (p : 𝓞 (fixF E)) ∈ P.1.comap (phi E) := fun P => by
    rw [Ideal.mem_comap, map_natCast]
    exact P.2.2
  let vOf : PS → HeightOneSpectrum (𝓞 (fixF E)) := fun P =>
    { asIdeal := P.1.comap (phi E)
      isPrime := by have := P.2.1.isPrime; exact Ideal.comap_isPrime _ _
      ne_bot := fun h => hp0 (by have := hPp P; rw [h] at this; exact (Ideal.mem_bot).mp this) }
  have hvT : ∀ P : PS, vOf P ∈ T := fun P => by
    rw [Set.Finite.mem_toFinset]
    show (vOf P).asIdeal ∣ _
    rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
    exact hPp P
  have hyp' : ∀ P : PS, ∃ g ∈ PI.UG.isom (PI.UG.hStd E n),
      PI.UG.gmap g (PI.UG.loc (K := E) P.1 (PI.UG.stdLat E n)) = PI.UG.loc (K := E) P.1 L :=
    fun P => hyp P.1 P.2.1 P.2.2
  choose G hGi hGl using hyp'
  let Gm : HeightOneSpectrum (𝓞 (fixF E)) → Matrix (Fin n) (Fin n) E := fun v =>
    if h : ∃ P : PS, vOf P = v then LinearMap.toMatrix' (G h.choose : PI.UG.Sp E n →ₗ[E] PI.UG.Sp E n) else 1
  have hGm : ∀ v, Gm v ∈ Matrix.unitaryGroup (Fin n) E := fun v => by
    by_cases h : ∃ P : PS, vOf P = v
    · simp only [Gm, dif_pos h]
      exact wa_unitary _ (hGi _)
    · simp only [Gm, dif_neg h]
      exact one_mem _
  let gv : (v : HeightOneSpectrum (𝓞 (fixF E))) → GL (Fin n) (E ⊗[fixF E] v.adicCompletion (fixF E)) := fun v =>
    Units.map (RingHom.mapMatrix (PI.UnitaryApproxDefs.inclE (F := fixF E) (v.adicCompletion (fixF E)))).toMonoidHom
      (glOf (Gm v) (hGm v))
  obtain ⟨c, hc0, hc⟩ := exists_int_mul (insert ((θ : E) - star (θ : E))⁻¹
    ((T ×ˢ (Finset.univ ×ˢ Finset.univ)).image
      (fun q : HeightOneSpectrum (𝓞 (fixF E)) × Fin n × Fin n => Gm q.1 q.2.1 q.2.2)))
  have hD : ((c * c : ℤ) : 𝓞 (fixF E)) ≠ 0 := Int.cast_ne_zero.mpr (mul_ne_zero hc0 hc0)
  obtain ⟨γ, hγ, hcong⟩ := unitary_approximation_finite (fixF E) E (Fin n) (sig E) (1 : Matrix (Fin n) (Fin n) E)
    (fun e => star_star e) ⟨(θ : E), fun h => hδ (by rw [show star (θ : E) = (θ : E) from h, sub_self])⟩
    (PI.UnitaryApproxDefs.cT_one _) (by simp) T gv (fun v _ => map_mem_UPts _ (Gm v) (hGm v))
    ((c * c : ℤ) : 𝓞 (fixF E)) hD
  have hγu : (γ : Matrix (Fin n) (Fin n) E) ∈ Matrix.unitaryGroup (Fin n) E := by
    have h : PI.UnitaryApproxDefs.cT (sig E : E →+* E) (γ : Matrix (Fin n) (Fin n) E) * 1 *
        (γ : Matrix (Fin n) (Fin n) E) = 1 := hγ
    rw [mul_one, cT_sig] at h
    exact Matrix.mem_unitaryGroup_iff'.mpr h
  refine ⟨toEquiv γ, toEquiv_isom γ (Matrix.mem_unitaryGroup_iff'.mp hγu), fun P hPm hpP => ?_⟩
  let P' : PS := ⟨P, hPm, hpP⟩
  have hex : ∃ Q : PS, vOf Q = vOf P' := ⟨P', rfl⟩
  have hQv : vOf hex.choose = vOf P' := hex.choose_spec
  have hGmv : Gm (vOf P') = LinearMap.toMatrix' (G hex.choose : PI.UG.Sp E n →ₗ[E] PI.UG.Sp E n) := by
    simp only [Gm, dif_pos hex]
  have hcomap : hex.choose.1.comap (phi E) = P.comap (phi E) := congrArg HeightOneSpectrum.asIdeal hQv
  have hlocStd := loc_eq hex.choose.1 P hex.choose.2.1.isPrime hPm.isPrime hcomap (PI.UG.stdLat E n)
  have hlocL := loc_eq hex.choose.1 P hex.choose.2.1.isPrime hPm.isPrime hcomap L
  have hGQ : PI.UG.gmap (G hex.choose) (PI.UG.loc (K := E) P (PI.UG.stdLat E n)) = PI.UG.loc (K := E) P L := by
    rw [← hlocStd, ← hlocL]
    exact hGl hex.choose
  have hvT' : vOf P' ∈ T := hvT P'
  have hcG : ∀ i j, ∃ a : 𝓞 E, algebraMap (𝓞 E) E a = (c : E) * Gm (vOf P') i j := fun i j =>
    hc (Gm (vOf P') i j) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨(vOf P', i, j), by simp [hvT'], rfl⟩))
  have hcδ := hc _ (Finset.mem_insert_self _ _)
  have hcg : ∀ i j, ∃ s ∈ PI.UnitaryApproxDefs.tensInt (F := fixF E) ((vOf P').adicCompletion (fixF E))
        (PI.UnitaryApproxDefs.intOE E) ((vOf P').adicCompletionIntegers (fixF E)).toSubring,
        PI.UnitaryApproxDefs.inclE (F := fixF E) ((vOf P').adicCompletion (fixF E)) (Gm (vOf P') i j) -
          PI.UnitaryApproxDefs.inclE (F := fixF E) ((vOf P').adicCompletion (fixF E)) ((γ : Matrix (Fin n) (Fin n) E) i j) =
        PI.UnitaryApproxDefs.inclE (F := fixF E) ((vOf P').adicCompletion (fixF E)) ((c * c : ℤ) : E) * s := by
    intro i j
    obtain ⟨s, hs, h⟩ := hcong (vOf P') hvT' i j
    refine ⟨s, hs, ?_⟩
    have e1 : algebraMap (fixF E) E (((c * c : ℤ) : 𝓞 (fixF E)) : fixF E) = ((c * c : ℤ) : E) := by simp
    rw [← e1]
    exact h
  obtain ⟨hA, hB⟩ := local_step (vOf P') θ hδ c hc0 hcδ (Gm (vOf P')) (hGm (vOf P')) hcG
    (γ : Matrix (Fin n) (Fin n) E) hcg
  have hGu := hGm (vOf P')
  have hGG1 : Gm (vOf P') * star (Gm (vOf P')) = 1 := Matrix.mem_unitaryGroup_iff.mp hGu
  have hγ1 : (γ : Matrix (Fin n) (Fin n) E) * star (γ : Matrix (Fin n) (Fin n) E) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp hγu
  have hGA : Gm (vOf P') * (star (Gm (vOf P')) * γ) = γ := by
    rw [← Matrix.mul_assoc, hGG1, Matrix.one_mul]
  have hγB : (γ : Matrix (Fin n) (Fin n) E) * (star (γ : Matrix (Fin n) (Fin n) E) * Gm (vOf P')) = Gm (vOf P') := by
    rw [← Matrix.mul_assoc, hγ1, Matrix.one_mul]
  have hGx : ∀ x, G hex.choose x = Gm (vOf P') *ᵥ x := fun x => by
    rw [hGmv, LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe]
  have hv' : P.comap (phi E) = (vOf P').asIdeal := rfl
  rw [← hGQ]
  ext y
  simp only [PI.UG.gmap, Submodule.mem_map, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(star (Gm (vOf P')) * (γ : Matrix (Fin n) (Fin n) E)) *ᵥ x, mulVec_loc P hv' hA hx, ?_⟩
    rw [hGx, Matrix.mulVec_mulVec, hGA, toEquiv_apply]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(star (γ : Matrix (Fin n) (Fin n) E) * Gm (vOf P')) *ᵥ x, mulVec_loc P hv' hB hx, ?_⟩
    rw [toEquiv_apply, Matrix.mulVec_mulVec, hγB, hGx]

/- English proof (translation)
The claim follows from `weakApprox_of weak_approximation_places`.
-/
theorem weakApprox_of_approx_and_separation : WeakApprox := weakApprox_of weak_approximation_places

end Formalism.L2.KerInert
