import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CircleEqOneOfRePos

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.InjectiveDecompositionAction NumberField IsDedekindDomain
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.Fin.U1

section Comp

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem finite_adele_fst_mul (x y : AF F) : (x * y).1 = x.1 * y.1 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem finite_adele_fst_add (x y : AF F) : (x + y).1 = x.1 + y.1 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem finite_adele_fst_sub (x y : AF F) : (x - y).1 = x.1 - y.1 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem finite_adele_fst_one : (1 : AF F).1 = 1 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem finite_adele_snd_mul (x y : AF F) (v : HeightOneSpectrum (𝓞 F)) : (x * y).2 v = x.2 v * y.2 v := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem finite_adele_snd_add (x y : AF F) (v : HeightOneSpectrum (𝓞 F)) : (x + y).2 v = x.2 v + y.2 v := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem finite_adele_snd_sub (x y : AF F) (v : HeightOneSpectrum (𝓞 F)) : (x - y).2 v = x.2 v - y.2 v := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem finite_adele_snd_one (v : HeightOneSpectrum (𝓞 F)) : (1 : AF F).2 v = 1 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem finite_adele_snd_algebraMap (c : F) (v : HeightOneSpectrum (𝓞 F)) :
    (algebraMap F (AF F) c).2 v = algebraMap F (v.adicCompletion F) c := rfl

abbrev epv (v : HeightOneSpectrum (𝓞 F)) : AF F := pairA F 0 (single v 1)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem epv_fst (v : HeightOneSpectrum (𝓞 F)) : (epv v).1 = 0 := rfl
/- English proof (translation)
Use `first`. Consider the case `exact Pi.single_eq_same v (1 : v.adicCompletion F)`. Consider the case `(simp [epv, pairA, single]; done)`. Consider the case `(simp [epv, pairA, single]; convert Pi.single_eq_same v (1 : v.adicCompletion F); done)`. Consider the case `(simp [epv, pairA, single]; rfl)`.
-/
theorem epv_self (v : HeightOneSpectrum (𝓞 F)) : (epv v).2 v = 1 := by
  classical
  first
  | exact Pi.single_eq_same v (1 : v.adicCompletion F)
  | (simp [epv, pairA, single]; done)
  | (simp [epv, pairA, single]; convert Pi.single_eq_same v (1 : v.adicCompletion F); done)
  | (simp [epv, pairA, single]; rfl)
/- English proof (translation)
Use `first`. Consider the case `exact Pi.single_eq_of_ne h (1 : v.adicCompletion F)`. Consider the case `(simp [epv, pairA, single, h]; done)`. Consider the case `(simp [epv, pairA, single]; convert Pi.single_eq_of_ne h (1 : v.adicCompletion F); done)`. Consider the case `(simp [epv, pairA, single]; rfl)`.
-/
theorem epv_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) : (epv v).2 w = 0 := by
  classical
  first
  | exact Pi.single_eq_of_ne h (1 : v.adicCompletion F)
  | (simp [epv, pairA, single, h]; done)
  | (simp [epv, pairA, single]; convert Pi.single_eq_of_ne h (1 : v.adicCompletion F); done)
  | (simp [epv, pairA, single]; rfl)

/- English proof (translation)
Use `Prod.ext ?_ ?_` and prove the remaining obligations. Rewrite using `[finite_adele_fst_mul, epv_fst, mul_zero]`. Apply `RestrictedProduct.ext` to reduce the goal to its premises. Introduce `w`. Use `(finite_adele_snd_mul (epv v) (epv v) w).trans ?_` and prove the remaining obligations.

Distinguish the cases in `h : w = v`. Substitute `h` using the available equality. Rewrite using `[epv_self, mul_one]`. Conclude with `(epv_self w).symm`. Rewrite using `[epv_ne h, mul_zero]`.

Conclude with `(epv_ne h).symm`.
-/
theorem epv_sq (v : HeightOneSpectrum (𝓞 F)) : epv v * epv v = epv v := by
  refine Prod.ext ?_ ?_
  · rw [finite_adele_fst_mul, epv_fst, mul_zero]
  · apply RestrictedProduct.ext
    intro w
    refine (finite_adele_snd_mul (epv v) (epv v) w).trans ?_
    by_cases h : w = v
    · subst h
      rw [epv_self, mul_one]
      exact (epv_self w).symm
    · rw [epv_ne h, mul_zero]
      exact (epv_ne h).symm

end Comp

section Split

variable {D : D7} (δ : D.host.E) (hδ : D.sp.cm.sig δ = -δ) (hδ0 : δ ≠ 0) (Δ : D.host.F)
  (hΔ : algebraMap D.host.F D.host.E Δ = δ * δ)

include hΔ hδ0 hδ in

/- English proof (translation)
Establish `hc : ∀ (a : AF D.host.F) (x : D.host.E), cA D (a ⊗ₜ[D.host.F] x) = a ⊗ₜ[D.host.F] D.sp.cm.sig x`. Introduce `a x`. Use `first`. Consider the case `rfl`. Consider the case `simp [cA]`.

Establish `h2F : (2 : v.adicCompletion D.host.F) ≠ 0`. Establish `h` using `(algebraMap D.host.F (v.adicCompletion D.host.F)).injective.ne (two_ne_zero (α := D.host.F))`. Rewrite `h` using `[map_ofNat, map_zero]`. Conclude with `h`. Establish `hΔ0 : Δ ≠ 0`.

Introduce and unpack `rfl`. Apply `hδ0` to reduce the goal to its premises. Establish `h0 : δ * δ = 0` using `by rw [← hΔ, map_zero]`. Conclude with `mul_self_eq_zero.mp h0`. Establish `hs0 : s ≠ 0`.

Introduce and unpack `rfl`. Apply `hΔ0` to reduce the goal to its premises. Establish `h0 : algebraMap D.host.F (v.adicCompletion D.host.F) Δ = 0` using `by rw [← hs, mul_zero]`. Conclude with `(map_eq_zero_iff _ (algebraMap D.host.F (v.adicCompletion D.host.F)).injective).mp h0`. Establish `hsv : ∀ t : v.adicCompletion D.host.F, (single v t) v = t`.

Introduce `t`. Use `first`. Consider the case `exact Pi.single_eq_same v t`. Consider the case `(simp [single]; done)`. Consider the case `(simp [single]; convert Pi.single_eq_same v t; done)`.

Consider the case `(simp [single]; rfl)`. Establish `hsw : ∀ (t : v.adicCompletion D.host.F) (w : HeightOneSpectrum (𝓞 D.host.F)), w ≠ v → (single v t) w = 0`. Introduce `t w hw`. Use `first`. Consider the case `exact Pi.single_eq_of_ne hw t`.

Consider the case `(simp [single, hw]; done)`. Consider the case `(simp [single]; convert Pi.single_eq_of_ne hw t; done)`. Consider the case `(simp [single]; rfl)`. Establish `hAF : ∀ x y : AF D.host.F, x.1 = y.1 → (∀ w, x.2 w = y.2 w) → x = y`. Use `by`.

Introduce `x y h1 h2`. Use `Prod.ext h1 ?_` and prove the remaining obligations. Apply `RestrictedProduct.ext` to reduce the goal to its premises. Conclude with `h2`. Take `⟨a, ha⟩ : ∃ a : AF D.host.F, a = pairA D.host.F 0 (single v (2 : v.adicCompletion D.host.F)⁻¹)` from `⟨_, rfl⟩`.

Take `⟨b, hb⟩ : ∃ b : AF D.host.F, b = pairA D.host.F 0 (single v (2 * s)⁻¹)` from `⟨_, rfl⟩`. Establish `ha1 : a.1 = 0` using `by rw [ha]; rfl`. Establish `hb1 : b.1 = 0` using `by rw [hb]; rfl`. Establish `ha2v : a.2 v = (2 : v.adicCompletion D.host.F)⁻¹` using `by rw [ha]; exact hsv _`. Establish `hb2v : b.2 v = (2 * s)⁻¹` using `by rw [hb]; exact hsv _`.

Establish `ha2w : ∀ w, w ≠ v → a.2 w = 0` using `by intro w hw; rw [ha]; exact hsw _ w hw`. Establish `hb2w : ∀ w, w ≠ v → b.2 w = 0` using `by intro w hw; rw [hb]; exact hsw _ w hw`. Establish `hDAv : (DA Δ).2 v = s * s` using `by rw [hs]; exact finite_adele_snd_algebraMap Δ v`. Establish `A1 : a * a + DA Δ * (b * b) = a`. Apply `hAF` to reduce the goal to its premises.

Simplify using `only [finite_adele_fst_add, finite_adele_fst_mul, ha1, hb1]`. Expand and normalize the polynomial expressions, which then agree. Introduce `w`. Simplify using `only [finite_adele_snd_add, finite_adele_snd_mul]`. Distinguish the cases in `hw : w = v`.

Substitute `hw` using the available equality. Rewrite using `[ha2v, hb2v, hDAv]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[ha2w w hw, hb2w w hw]`.

Expand and normalize the polynomial expressions, which then agree. Establish `A2 : a * b + a * b = b`. Apply `hAF` to reduce the goal to its premises. Simplify using `only [finite_adele_fst_add, finite_adele_fst_mul, ha1, hb1]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `w`. Simplify using `only [finite_adele_snd_add, finite_adele_snd_mul]`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[ha2v, hb2v]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[ha2w w hw, hb2w w hw]`. Expand and normalize the polynomial expressions, which then agree. Establish `A3 : a * a - DA Δ * (b * b) = 0`.

Apply `hAF` to reduce the goal to its premises. Simplify using `only [finite_adele_fst_sub, finite_adele_fst_mul, ha1, hb1]`. Rewrite using `[show (0 : AF D.host.F).1 = 0 from rfl]`. Expand and normalize the polynomial expressions, which then agree. Introduce `w`.

Simplify using `only [finite_adele_snd_sub, finite_adele_snd_mul]`. Rewrite using `[show (0 : AF D.host.F).2 w = 0 from rfl]`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[ha2v, hb2v, hDAv]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[ha2w w hw, hb2w w hw]`. Expand and normalize the polynomial expressions, which then agree. Establish `A4 : a + a = epv v`.

Apply `hAF` to reduce the goal to its premises. Simplify using `only [finite_adele_fst_add, ha1, epv_fst]`. Expand and normalize the polynomial expressions, which then agree. Introduce `w`. Simplify using `only [finite_adele_snd_add]`.

Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[ha2v, epv_self, ← two_mul, mul_inv_cancel₀ h2F]`. Rewrite using `[ha2w w hw, epv_ne hw]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨ι, hι⟩ : ∃ f : AF D.host.F →+* AE D, f = algebraMap (AF D.host.F) (AE D)` from `⟨_, rfl⟩`. Establish `hιt : ∀ x : AF D.host.F, ι x = x ⊗ₜ[D.host.F] (1 : D.host.E)` using `by intro x; rw [hι]; rfl`. Take `⟨d, hd⟩ : ∃ d : AE D, d = (1 : AF D.host.F) ⊗ₜ[D.host.F] δ` from `⟨_, rfl⟩`. Establish `kd : d * d = ι (DA Δ)`. Rewrite using `[hd, Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← hΔ, hιt, show algebraMap D.host.F D.host.E Δ = Δ • (1 : D.host.E) from Algebra.algebraMap_eq_smul_one Δ, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]`.

Establish `k1 : ι a * ι a + ι (DA Δ) * (ι b * ι b) = ι a`. Simplify `congrArg ι A1` using `only [map_add, map_mul]`. Establish `k2 : ι a * ι b + ι a * ι b = ι b`. Simplify `congrArg ι A2` using `only [map_add, map_mul]`. Establish `k3 : ι a * ι a - ι (DA Δ) * (ι b * ι b) = 0`.

Simplify `congrArg ι A3` using `only [map_sub, map_mul, map_zero]`. Establish `k4 : ι a + ι a = ι (epv v)`. Simplify `congrArg ι A4` using `only [map_add]`. Establish `hcι : ∀ x, cA D (ι x) = ι x`. Introduce `x`.

Rewrite using `[hιt, hc, map_one]`. Establish `hcd : cA D (ι b * d) = -(ι b * d)`. Rewrite using `[hιt, hd, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, hc, hδ, TensorProduct.tmul_neg]`. Establish `hce : cA D (ι a + ι b * d) = ι a - ι b * d`. Rewrite using `[map_add, hcι, hcd, sub_eq_add_neg]`.

Establish `hsum : ι a + ι b * d + cA D (ι a + ι b * d) = algebraMap (AF D.host.F) (AE D) (epv v)`. Rewrite using `[hce, ← hι, ← k4]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨ι a + ι b * d, ⟨?_, ?_, v, epv v, ?_, hsum⟩, hsum⟩` and prove the remaining obligations. Take the linear combination `k1 + d * k2 + ι b * ι b * kd`.

Rewrite using `[hce]`. Take the linear combination `k3 - ι b * ι b * kd`. Conclude with `⟨single v 1, rfl, epv_self v, fun v' hv' => epv_ne hv'⟩`.
-/
theorem exists_splitIdem' (v : HeightOneSpectrum (𝓞 D.host.F)) (s : v.adicCompletion D.host.F)
    (hs : s * s = algebraMap D.host.F (v.adicCompletion D.host.F) Δ) :
    ∃ e, IsSplitIdem D e ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) (epv v) := by
  classical
  have hc : ∀ (a : AF D.host.F) (x : D.host.E), cA D (a ⊗ₜ[D.host.F] x) = a ⊗ₜ[D.host.F] D.sp.cm.sig x := by
    intro a x
    first
    | rfl
    | simp [cA]
  have h2F : (2 : v.adicCompletion D.host.F) ≠ 0 := by
    have h := (algebraMap D.host.F (v.adicCompletion D.host.F)).injective.ne (two_ne_zero (α := D.host.F))
    rw [map_ofNat, map_zero] at h
    exact h
  have hΔ0 : Δ ≠ 0 := by
    rintro rfl
    apply hδ0
    have h0 : δ * δ = 0 := by rw [← hΔ, map_zero]
    exact mul_self_eq_zero.mp h0
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hΔ0
    have h0 : algebraMap D.host.F (v.adicCompletion D.host.F) Δ = 0 := by rw [← hs, mul_zero]
    exact (map_eq_zero_iff _ (algebraMap D.host.F (v.adicCompletion D.host.F)).injective).mp h0
  have hsv : ∀ t : v.adicCompletion D.host.F, (single v t) v = t := by
    intro t
    first
    | exact Pi.single_eq_same v t
    | (simp [single]; done)
    | (simp [single]; convert Pi.single_eq_same v t; done)
    | (simp [single]; rfl)
  have hsw : ∀ (t : v.adicCompletion D.host.F) (w : HeightOneSpectrum (𝓞 D.host.F)), w ≠ v →
      (single v t) w = 0 := by
    intro t w hw
    first
    | exact Pi.single_eq_of_ne hw t
    | (simp [single, hw]; done)
    | (simp [single]; convert Pi.single_eq_of_ne hw t; done)
    | (simp [single]; rfl)
  have hAF : ∀ x y : AF D.host.F, x.1 = y.1 → (∀ w, x.2 w = y.2 w) → x = y :=
by
    intro x y h1 h2
    refine Prod.ext h1 ?_
    apply RestrictedProduct.ext
    exact h2
  obtain ⟨a, ha⟩ : ∃ a : AF D.host.F, a = pairA D.host.F 0 (single v (2 : v.adicCompletion D.host.F)⁻¹) :=
    ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : AF D.host.F, b = pairA D.host.F 0 (single v (2 * s)⁻¹) := ⟨_, rfl⟩
  have ha1 : a.1 = 0 := by rw [ha]; rfl
  have hb1 : b.1 = 0 := by rw [hb]; rfl
  have ha2v : a.2 v = (2 : v.adicCompletion D.host.F)⁻¹ := by rw [ha]; exact hsv _
  have hb2v : b.2 v = (2 * s)⁻¹ := by rw [hb]; exact hsv _
  have ha2w : ∀ w, w ≠ v → a.2 w = 0 := by intro w hw; rw [ha]; exact hsw _ w hw
  have hb2w : ∀ w, w ≠ v → b.2 w = 0 := by intro w hw; rw [hb]; exact hsw _ w hw
  have hDAv : (DA Δ).2 v = s * s := by rw [hs]; exact finite_adele_snd_algebraMap Δ v
  have A1 : a * a + DA Δ * (b * b) = a := by
    apply hAF
    · simp only [finite_adele_fst_add, finite_adele_fst_mul, ha1, hb1]
      ring
    · intro w
      simp only [finite_adele_snd_add, finite_adele_snd_mul]
      by_cases hw : w = v
      · subst hw
        rw [ha2v, hb2v, hDAv]
        field_simp
        ring
      · rw [ha2w w hw, hb2w w hw]
        ring
  have A2 : a * b + a * b = b := by
    apply hAF
    · simp only [finite_adele_fst_add, finite_adele_fst_mul, ha1, hb1]
      ring
    · intro w
      simp only [finite_adele_snd_add, finite_adele_snd_mul]
      by_cases hw : w = v
      · subst hw
        rw [ha2v, hb2v]
        field_simp
        ring
      · rw [ha2w w hw, hb2w w hw]
        ring
  have A3 : a * a - DA Δ * (b * b) = 0 := by
    apply hAF
    · simp only [finite_adele_fst_sub, finite_adele_fst_mul, ha1, hb1]
      rw [show (0 : AF D.host.F).1 = 0 from rfl]
      ring
    · intro w
      simp only [finite_adele_snd_sub, finite_adele_snd_mul]
      rw [show (0 : AF D.host.F).2 w = 0 from rfl]
      by_cases hw : w = v
      · subst hw
        rw [ha2v, hb2v, hDAv]
        field_simp
        ring
      · rw [ha2w w hw, hb2w w hw]
        ring
  have A4 : a + a = epv v := by
    apply hAF
    · simp only [finite_adele_fst_add, ha1, epv_fst]
      ring
    · intro w
      simp only [finite_adele_snd_add]
      by_cases hw : w = v
      · subst hw
        rw [ha2v, epv_self, ← two_mul, mul_inv_cancel₀ h2F]
      · rw [ha2w w hw, epv_ne hw]
        ring
  obtain ⟨ι, hι⟩ : ∃ f : AF D.host.F →+* AE D, f = algebraMap (AF D.host.F) (AE D) := ⟨_, rfl⟩
  have hιt : ∀ x : AF D.host.F, ι x = x ⊗ₜ[D.host.F] (1 : D.host.E) := by intro x; rw [hι]; rfl
  obtain ⟨d, hd⟩ : ∃ d : AE D, d = (1 : AF D.host.F) ⊗ₜ[D.host.F] δ := ⟨_, rfl⟩
  have kd : d * d = ι (DA Δ) := by
    rw [hd, Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← hΔ, hιt,
      show algebraMap D.host.F D.host.E Δ = Δ • (1 : D.host.E) from Algebra.algebraMap_eq_smul_one Δ,
      ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  have k1 : ι a * ι a + ι (DA Δ) * (ι b * ι b) = ι a := by
    simpa only [map_add, map_mul] using congrArg ι A1
  have k2 : ι a * ι b + ι a * ι b = ι b := by
    simpa only [map_add, map_mul] using congrArg ι A2
  have k3 : ι a * ι a - ι (DA Δ) * (ι b * ι b) = 0 := by
    simpa only [map_sub, map_mul, map_zero] using congrArg ι A3
  have k4 : ι a + ι a = ι (epv v) := by
    simpa only [map_add] using congrArg ι A4
  have hcι : ∀ x, cA D (ι x) = ι x := by
    intro x
    rw [hιt, hc, map_one]
  have hcd : cA D (ι b * d) = -(ι b * d) := by
    rw [hιt, hd, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, hc, hδ, TensorProduct.tmul_neg]
  have hce : cA D (ι a + ι b * d) = ι a - ι b * d := by
    rw [map_add, hcι, hcd, sub_eq_add_neg]
  have hsum : ι a + ι b * d + cA D (ι a + ι b * d) = algebraMap (AF D.host.F) (AE D) (epv v) := by
    rw [hce, ← hι, ← k4]
    ring
  refine ⟨ι a + ι b * d, ⟨?_, ?_, v, epv v, ?_, hsum⟩, hsum⟩
  · linear_combination k1 + d * k2 + ι b * ι b * kd
  · rw [hce]
    linear_combination k3 - ι b * ι b * kd
  · exact ⟨single v 1, rfl, epv_self v, fun v' hv' => epv_ne hv'⟩

include hδ hδ0 hΔ in

/- English proof (translation)
Establish `hAF : ∀ x y : AF D.host.F, x.1 = y.1 → (∀ w, x.2 w = y.2 w) → x = y`. Introduce `x y h1 h2`. Use `Prod.ext h1 ?_` and prove the remaining obligations. Apply `RestrictedProduct.ext` to reduce the goal to its premises. Conclude with `h2`.

Take `⟨ι, hι⟩ : ∃ f : AF D.host.F →+* AE D, f = algebraMap (AF D.host.F) (AE D)` from `⟨_, rfl⟩`. Establish `hιt : ∀ z : AF D.host.F, ι z = z ⊗ₜ[D.host.F] (1 : D.host.E)` using `by intro z; rw [hι]; rfl`. Take `⟨dd, hdd⟩ : ∃ d : AE D, d = (1 : AF D.host.F) ⊗ₜ[D.host.F] δ` from `⟨_, rfl⟩`. Establish `hpt : ∀ p q : AF D.host.F, pt δ p q = ι p + ι q * dd`. Introduce `p q`.

Rewrite using `[hιt, hιt, hdd, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Both sides reduce to the same expression. Introduce `T`. Use `Finset.induction_on T ?_ ?_` and prove the remaining obligations. Introduce `a b h hT`.

Use `⟨a, b, h, rfl, rfl, rfl, fun v _ => ⟨rfl, rfl⟩, fun v hv => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Conclude with `absurd (hT v hv hn) (Finset.notMem_empty v)`. Introduce `v T0 _ ih a b h hT`. Distinguish the cases in `hgood : v ∈ S ∨ (‖a.2 v‖ ≤ 1 ∧ ‖b.2 v‖ ≤ 1)`.

Apply `ih a b h` to reduce the goal to its premises. Introduce `w hw hn`. Break down `Finset.mem_insert.mp (hT w hw hn) with h0 | h0` into its components or cases. Substitute `h0` using the available equality. Break down `hgood with h1 | h1` into its components or cases.

Conclude with `absurd h1 hw`. Conclude with `absurd h1 hn`. Conclude with `h0`. Establish `hvS : v ∉ S` using `fun h0 => hgood (Or.inl h0)`. Establish `hni : 1 < ‖a.2 v‖ ∨ 1 < ‖b.2 v‖`.

Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hgood (Or.inr hc)`. Take `⟨h2v, hΔv⟩` from `hS v hvS`. Establish `hav : a.2 v * a.2 v - algebraMap D.host.F (v.adicCompletion D.host.F) Δ * (b.2 v * b.2 v) = 1`.

Establish `h0` using `congrArg (fun z : AF D.host.F => z.2 v) h`. Simplify using `only [finite_adele_snd_sub, finite_adele_snd_mul, finite_adele_snd_one] at h0`. Rewrite using `[← finite_adele_snd_algebraMap Δ v]`. Conclude with `h0`. Take `⟨s, hs⟩` from `sq_of_nonint (F := D.host.F) (v := v) (Δ := algebraMap D.host.F (v.adicCompletion D.host.F) Δ) (a := a.2 v) (b := b.2 v) h2v hΔv hav hni`.

Take `⟨e, he, hee⟩` from `exists_splitIdem' δ hδ hδ0 Δ hΔ v s hs`. Take `⟨a', ha'⟩ : ∃ a' : AF D.host.F, a' = a - epv v * a + epv v` from `⟨_, rfl⟩`. Take `⟨b', hb'⟩ : ∃ b' : AF D.host.F, b' = b - epv v * b` from `⟨_, rfl⟩`. Establish `ha'1 : a'.1 = a.1` using `by rw [ha', finite_adele_fst_add, finite_adele_fst_sub, finite_adele_fst_mul, epv_fst]; ring`. Establish `hb'1 : b'.1 = b.1` using `by rw [hb', finite_adele_fst_sub, finite_adele_fst_mul, epv_fst]; ring`.

Establish `ha'v : a'.2 v = 1` using `by rw [ha', finite_adele_snd_add, finite_adele_snd_sub, finite_adele_snd_mul, epv_self]; ring`. Establish `hb'v : b'.2 v = 0` using `by rw [hb', finite_adele_snd_sub, finite_adele_snd_mul, epv_self]; ring`. Establish `ha'w : ∀ w, w ≠ v → a'.2 w = a.2 w`. Introduce `w hw`. Rewrite using `[ha', finite_adele_snd_add, finite_adele_snd_sub, finite_adele_snd_mul, epv_ne hw]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hb'w : ∀ w, w ≠ v → b'.2 w = b.2 w`. Introduce `w hw`. Rewrite using `[hb', finite_adele_snd_sub, finite_adele_snd_mul, epv_ne hw]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h' : a' * a' - DA Δ * (b' * b') = 1`. Apply `hAF` to reduce the goal to its premises. Establish `h0` using `congrArg (fun z : AF D.host.F => z.1) h`. Simplify using `only [finite_adele_fst_sub, finite_adele_fst_mul, finite_adele_fst_one] at h0 ⊢`. Rewrite using `[ha'1, hb'1]`.

Conclude with `h0`. Introduce `w`. Establish `h0` using `congrArg (fun z : AF D.host.F => z.2 w) h`. Simplify using `only [finite_adele_snd_sub, finite_adele_snd_mul, finite_adele_snd_one] at h0 ⊢`. Distinguish the cases in `hw : w = v`.

Substitute `hw` using the available equality. Rewrite using `[ha'v, hb'v]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[ha'w w hw, hb'w w hw]`. Conclude with `h0`.

Establish `hX : (((mkU δ hδ Δ hΔ h : FirstPropositionFrame D) : (AE D)ˣ) : AE D) = pt δ a b` using `rfl`. Establish `hX' : (((mkU δ hδ Δ hΔ h' : FirstPropositionFrame D) : (AE D)ˣ) : AE D) = pt δ a' b'` using `rfl`. Establish `hsupp : SuppAtU D e ((mkU δ hδ Δ hΔ h' * (mkU δ hδ Δ hΔ h)⁻¹ : FirstPropositionFrame D) : (AE D)ˣ)`. Unfold `SuppAtU`. Rewrite using `[hee]`.

Take `⟨u, hu⟩ : ∃ u : AE D, u = ((((mkU δ hδ Δ hΔ h)⁻¹ : FirstPropositionFrame D) : (AE D)ˣ) : AE D)` from `⟨_, rfl⟩`. Establish `hXu : pt δ a b * u = 1`. Rewrite using `[← hX, hu]`. Simplify using the standard rewrite rules. Establish `hval : ((((mkU δ hδ Δ hΔ h' * (mkU δ hδ Δ hΔ h)⁻¹ : FirstPropositionFrame D)) : (AE D)ˣ) : AE D) = pt δ a' b' * u`.

Rewrite using `[hu, ← hX']`. Simplify using the standard rewrite rules. Rewrite using `[hval, ← hι]`. Establish `hk : ι (epv v) * ι (epv v) = ι (epv v)` using `by rw [← map_mul, epv_sq]`. Establish `hda : a' = a + epv v * (1 - a)` using `by rw [ha']; ring`.

Establish `hdb : b' = b + epv v * (-b)` using `by rw [hb']; ring`. Rewrite `hXu` using `[hpt]`. Rewrite using `[hpt, hda, hdb, map_add, map_add, map_mul, map_mul, map_sub, map_one, map_neg]`. Take the linear combination `(2 * ι (epv v) - 1 - ι (epv v) * ι (epv v)) * hXu + (u - 1) * hk`. Establish `hlam : lam (mkU δ hδ Δ hΔ h') = lam (mkU δ hδ Δ hΔ h)`.

Establish `h1` using `hsplit e he _ hsupp`. Rewrite `h1` using `[map_mul, map_inv]`. Conclude with `mul_inv_eq_one.mp h1`. Take `⟨a'', b'', h'', hl, h1a, h1b, hSab, hint⟩` from `ih a' b' h' (by`. Introduce `w hw hn`.

Establish `hwv : w ≠ v`. Introduce and unpack `rfl`. Apply `hn` to reduce the goal to its premises. Rewrite using `[ha'v, hb'v]`. Simplify using the standard rewrite rules.

Rewrite `hn` using `[ha'w w hwv, hb'w w hwv]`. Break down `Finset.mem_insert.mp (hT w hw hn) with h0 | h0` into its components or cases. Conclude with `absurd h0 hwv`. Conclude with `h0)`. Use `⟨a'', b'', h'', hl.trans hlam, h1a.trans ha'1, h1b.trans hb'1, fun w hw => ?_, hint⟩` and prove the remaining obligations.

Establish `hwv : w ≠ v` using `fun h0 => hvS (h0 ▸ hw)`. Take `⟨h1, h2⟩` from `hSab w hw`. Conclude with `⟨h1.trans (ha'w w hwv), h2.trans (hb'w w hwv)⟩`.
-/
theorem removal (lam : FirstPropositionFrame D →* Circle)
    (hsplit : ∀ e, IsSplitIdem D e → ∀ x : FirstPropositionFrame D, SuppAtU D e (x : (AE D)ˣ) → lam x = 1)
    (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (hS : ∀ v ∉ S, ‖(2 : v.adicCompletion D.host.F)‖ = 1 ∧
      ‖algebraMap D.host.F (v.adicCompletion D.host.F) Δ‖ = 1) :
    ∀ (T : Finset (HeightOneSpectrum (𝓞 D.host.F))) (a b : AF D.host.F) (h : a * a - DA Δ * (b * b) = 1),
      (∀ v, v ∉ S → ¬ (‖a.2 v‖ ≤ 1 ∧ ‖b.2 v‖ ≤ 1) → v ∈ T) →
      ∃ (a' b' : AF D.host.F) (h' : a' * a' - DA Δ * (b' * b') = 1),
        lam (mkU δ hδ Δ hΔ h') = lam (mkU δ hδ Δ hΔ h) ∧ a'.1 = a.1 ∧ b'.1 = b.1 ∧
        (∀ v ∈ S, a'.2 v = a.2 v ∧ b'.2 v = b.2 v) ∧ ∀ v ∉ S, ‖a'.2 v‖ ≤ 1 ∧ ‖b'.2 v‖ ≤ 1 := by
  classical
  have hAF : ∀ x y : AF D.host.F, x.1 = y.1 → (∀ w, x.2 w = y.2 w) → x = y := by
    intro x y h1 h2
    refine Prod.ext h1 ?_
    apply RestrictedProduct.ext
    exact h2
  obtain ⟨ι, hι⟩ : ∃ f : AF D.host.F →+* AE D, f = algebraMap (AF D.host.F) (AE D) := ⟨_, rfl⟩
  have hιt : ∀ z : AF D.host.F, ι z = z ⊗ₜ[D.host.F] (1 : D.host.E) := by intro z; rw [hι]; rfl
  obtain ⟨dd, hdd⟩ : ∃ d : AE D, d = (1 : AF D.host.F) ⊗ₜ[D.host.F] δ := ⟨_, rfl⟩
  have hpt : ∀ p q : AF D.host.F, pt δ p q = ι p + ι q * dd := by
    intro p q
    rw [hιt, hιt, hdd, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rfl
  intro T
  refine Finset.induction_on T ?_ ?_
  · intro a b h hT
    refine ⟨a, b, h, rfl, rfl, rfl, fun v _ => ⟨rfl, rfl⟩, fun v hv => ?_⟩
    by_contra hn
    exact absurd (hT v hv hn) (Finset.notMem_empty v)
  · intro v T0 _ ih a b h hT
    by_cases hgood : v ∈ S ∨ (‖a.2 v‖ ≤ 1 ∧ ‖b.2 v‖ ≤ 1)
    · apply ih a b h
      intro w hw hn
      rcases Finset.mem_insert.mp (hT w hw hn) with h0 | h0
      · subst h0
        rcases hgood with h1 | h1
        · exact absurd h1 hw
        · exact absurd h1 hn
      · exact h0
    have hvS : v ∉ S := fun h0 => hgood (Or.inl h0)
    have hni : 1 < ‖a.2 v‖ ∨ 1 < ‖b.2 v‖ := by
      by_contra hc
      push_neg at hc
      exact hgood (Or.inr hc)
    obtain ⟨h2v, hΔv⟩ := hS v hvS
    have hav : a.2 v * a.2 v - algebraMap D.host.F (v.adicCompletion D.host.F) Δ * (b.2 v * b.2 v) = 1 := by
      have h0 := congrArg (fun z : AF D.host.F => z.2 v) h
      simp only [finite_adele_snd_sub, finite_adele_snd_mul, finite_adele_snd_one] at h0
      rw [← finite_adele_snd_algebraMap Δ v]
      exact h0
    obtain ⟨s, hs⟩ := sq_of_nonint (F := D.host.F) (v := v)
      (Δ := algebraMap D.host.F (v.adicCompletion D.host.F) Δ) (a := a.2 v) (b := b.2 v) h2v hΔv hav hni
    obtain ⟨e, he, hee⟩ := exists_splitIdem' δ hδ hδ0 Δ hΔ v s hs
    obtain ⟨a', ha'⟩ : ∃ a' : AF D.host.F, a' = a - epv v * a + epv v := ⟨_, rfl⟩
    obtain ⟨b', hb'⟩ : ∃ b' : AF D.host.F, b' = b - epv v * b := ⟨_, rfl⟩
    have ha'1 : a'.1 = a.1 := by rw [ha', finite_adele_fst_add, finite_adele_fst_sub, finite_adele_fst_mul, epv_fst]; ring
    have hb'1 : b'.1 = b.1 := by rw [hb', finite_adele_fst_sub, finite_adele_fst_mul, epv_fst]; ring
    have ha'v : a'.2 v = 1 := by rw [ha', finite_adele_snd_add, finite_adele_snd_sub, finite_adele_snd_mul, epv_self]; ring
    have hb'v : b'.2 v = 0 := by rw [hb', finite_adele_snd_sub, finite_adele_snd_mul, epv_self]; ring
    have ha'w : ∀ w, w ≠ v → a'.2 w = a.2 w := by
      intro w hw
      rw [ha', finite_adele_snd_add, finite_adele_snd_sub, finite_adele_snd_mul, epv_ne hw]
      ring
    have hb'w : ∀ w, w ≠ v → b'.2 w = b.2 w := by
      intro w hw
      rw [hb', finite_adele_snd_sub, finite_adele_snd_mul, epv_ne hw]
      ring
    have h' : a' * a' - DA Δ * (b' * b') = 1 := by
      apply hAF
      · have h0 := congrArg (fun z : AF D.host.F => z.1) h
        simp only [finite_adele_fst_sub, finite_adele_fst_mul, finite_adele_fst_one] at h0 ⊢
        rw [ha'1, hb'1]
        exact h0
      · intro w
        have h0 := congrArg (fun z : AF D.host.F => z.2 w) h
        simp only [finite_adele_snd_sub, finite_adele_snd_mul, finite_adele_snd_one] at h0 ⊢
        by_cases hw : w = v
        · subst hw
          rw [ha'v, hb'v]
          ring
        · rw [ha'w w hw, hb'w w hw]
          exact h0
    have hX : (((mkU δ hδ Δ hΔ h : FirstPropositionFrame D) : (AE D)ˣ) : AE D) = pt δ a b := rfl
    have hX' : (((mkU δ hδ Δ hΔ h' : FirstPropositionFrame D) : (AE D)ˣ) : AE D) = pt δ a' b' := rfl
    have hsupp : SuppAtU D e ((mkU δ hδ Δ hΔ h' * (mkU δ hδ Δ hΔ h)⁻¹ : FirstPropositionFrame D) : (AE D)ˣ) := by
      unfold SuppAtU
      rw [hee]
      obtain ⟨u, hu⟩ : ∃ u : AE D, u = ((((mkU δ hδ Δ hΔ h)⁻¹ : FirstPropositionFrame D) : (AE D)ˣ) : AE D) := ⟨_, rfl⟩
      have hXu : pt δ a b * u = 1 := by
        rw [← hX, hu]
        simp
      have hval : ((((mkU δ hδ Δ hΔ h' * (mkU δ hδ Δ hΔ h)⁻¹ : FirstPropositionFrame D)) : (AE D)ˣ) : AE D) =
          pt δ a' b' * u := by
        rw [hu, ← hX']
        simp
      rw [hval, ← hι]
      have hk : ι (epv v) * ι (epv v) = ι (epv v) := by rw [← map_mul, epv_sq]
      have hda : a' = a + epv v * (1 - a) := by rw [ha']; ring
      have hdb : b' = b + epv v * (-b) := by rw [hb']; ring
      rw [hpt] at hXu
      rw [hpt, hda, hdb, map_add, map_add, map_mul, map_mul, map_sub, map_one, map_neg]
      linear_combination (2 * ι (epv v) - 1 - ι (epv v) * ι (epv v)) * hXu + (u - 1) * hk
    have hlam : lam (mkU δ hδ Δ hΔ h') = lam (mkU δ hδ Δ hΔ h) := by
      have h1 := hsplit e he _ hsupp
      rw [map_mul, map_inv] at h1
      exact mul_inv_eq_one.mp h1
    obtain ⟨a'', b'', h'', hl, h1a, h1b, hSab, hint⟩ := ih a' b' h' (by
      intro w hw hn
      have hwv : w ≠ v := by
        rintro rfl
        apply hn
        rw [ha'v, hb'v]
        simp
      rw [ha'w w hwv, hb'w w hwv] at hn
      rcases Finset.mem_insert.mp (hT w hw hn) with h0 | h0
      · exact absurd h0 hwv
      · exact h0)
    refine ⟨a'', b'', h'', hl.trans hlam, h1a.trans ha'1, h1b.trans hb'1, fun w hw => ?_, hint⟩
    have hwv : w ≠ v := fun h0 => hvS (h0 ▸ hw)
    obtain ⟨h1, h2⟩ := hSab w hw
    exact ⟨h1.trans (ha'w w hwv), h2.trans (hb'w w hwv)⟩

end Split

end Formalism.IndefR.Fin.U1

end
