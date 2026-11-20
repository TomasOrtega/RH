import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsCovolOne
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SchurFunctionSmoothRightInvariant
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
import GroundTheory.GlobalFields.TateThesis.ArchCharsUnitary

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal Matrix

namespace GlobalTheory.CompanionTheory.Glob.CharAF

/- English proof (translation)
Establish `hne : ∀ t, f t ≠ 0` using `fun t h => by`. Use `hn t` as an intermediate fact. Simplify using `[h] at this`. Set `χ : AddChar ℝ ℂˣ` to `{ toFun := fun t => Units.mk0 (f t) (hne t) map_zero_eq_one' := Units.ext (by simp) map_add_eq_mul' := fun a b => Units.ext (by simp [AddChar.map_add_eq_mul]) }`. Establish `hχ : Continuous χ` using `Units.isEmbedding_val₀.continuous_iff.2 hf`.

Take `⟨s, hs, -⟩` from `GroundTheory.Global.existsUnique_addChar_real_units χ hχ`. Establish `hs' : ∀ t : ℝ, f t = Complex.exp (s * t)` using `hs`. Establish `hre : s.re = 0`. Establish `h1` using `hn 1`. Rewrite `h1` using `[hs' 1, Complex.norm_exp]`.

Simplify using `using h1`. Establish `hpi : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Use `⟨s.im / (2 * Real.pi), fun t => ?_⟩` and prove the remaining obligations. Rewrite using `[hs' t]`. Use `congr 1`.

Establish `hs2 : s = (s.im : ℂ) * Complex.I`. Apply the tactic sequence `apply Complex.ext <;> simp [hre]`. Use `push_cast`. Rewrite using `[hs2]`. Simplify using `only [Complex.mul_im, Complex.ofReal_im, Complex.I_im, Complex.ofReal_re, Complex.I_re]`.

Clear the denominators using the available nonvanishing facts. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem real_char (f : AddChar ℝ ℂ) (hf : Continuous f) (hn : ∀ t, ‖f t‖ = 1) :
    ∃ α : ℝ, ∀ t : ℝ, f t = Complex.exp (2 * Real.pi * Complex.I * ((α * t : ℝ) : ℂ)) := by
  have hne : ∀ t, f t ≠ 0 := fun t h => by
    have := hn t
    simp [h] at this
  let χ : AddChar ℝ ℂˣ :=
    { toFun := fun t => Units.mk0 (f t) (hne t)
      map_zero_eq_one' := Units.ext (by simp)
      map_add_eq_mul' := fun a b => Units.ext (by simp [AddChar.map_add_eq_mul]) }
  have hχ : Continuous χ := Units.isEmbedding_val₀.continuous_iff.2 hf
  obtain ⟨s, hs, -⟩ := GroundTheory.Global.existsUnique_addChar_real_units χ hχ
  have hs' : ∀ t : ℝ, f t = Complex.exp (s * t) := hs
  have hre : s.re = 0 := by
    have h1 := hn 1
    rw [hs' 1, Complex.norm_exp] at h1
    simpa using h1
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  refine ⟨s.im / (2 * Real.pi), fun t => ?_⟩
  rw [hs' t]
  congr 1
  have hs2 : s = (s.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hre]
  push_cast
  rw [hs2]
  simp only [Complex.mul_im, Complex.ofReal_im, Complex.I_im, Complex.ofReal_re, Complex.I_re]
  field_simp
  simp
  ring

/- English proof (translation)
Establish `key : ∀ w, ∃ α : ℝ, ∀ t : ℝ, g (Pi.single w t) = Complex.exp (2 * Real.pi * Complex.I * ((α * t : ℝ) : ℂ))` using `fun w => real_char (g.compAddMonoidHom (AddMonoidHom.single (fun _ => ℝ) w)) (show Continuous (fun t : ℝ => g (Pi.single w t)) from hg.comp (continuous_pi fun j => by`. Distinguish the cases in `h : j = w`. Substitute `h` using the available equality. Simplify using `only [Pi.single_eq_same]`. Conclude with `continuous_id`.

Simplify `continuous_const)) (fun t => hn _)` using `[Pi.single_apply, h]`. Use `choose α hα using key`. Use `⟨α, fun x => ?_⟩` and prove the remaining obligations. Establish `hx : x = ∑ w, Pi.single w (x w)` using `(Finset.univ_sum_single x).symm`. Establish `hsum : ∀ s : Finset ι, g (∑ w ∈ s, Pi.single w (x w)) = ∏ w ∈ s, g (Pi.single w (x w))`.

Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert w s hw ih => rw [Finset.sum_insert hw, Finset.prod_insert hw, AddChar.map_add_eq_mul, ih]`. Use `conv_lhs => rw [hx]`.

Rewrite using `[hsum, Finset.prod_congr rfl fun w _ => hα w (x w), ← Complex.exp_sum, ← Finset.mul_sum]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem pi_char {ι : Type} [Fintype ι] [DecidableEq ι] (g : AddChar (ι → ℝ) ℂ) (hg : Continuous g)
    (hn : ∀ x, ‖g x‖ = 1) :
    ∃ α : ι → ℝ, ∀ x, g x = Complex.exp (2 * Real.pi * Complex.I * ((∑ w, α w * x w : ℝ) : ℂ)) := by
  have key : ∀ w, ∃ α : ℝ, ∀ t : ℝ, g (Pi.single w t) =
      Complex.exp (2 * Real.pi * Complex.I * ((α * t : ℝ) : ℂ)) := fun w =>
    real_char (g.compAddMonoidHom (AddMonoidHom.single (fun _ => ℝ) w))
      (show Continuous (fun t : ℝ => g (Pi.single w t)) from hg.comp (continuous_pi fun j => by
        by_cases h : j = w
        · subst h
          simp only [Pi.single_eq_same]
          exact continuous_id
        · simpa [Pi.single_apply, h] using continuous_const)) (fun t => hn _)
  choose α hα using key
  refine ⟨α, fun x => ?_⟩
  have hx : x = ∑ w, Pi.single w (x w) := (Finset.univ_sum_single x).symm
  have hsum : ∀ s : Finset ι, g (∑ w ∈ s, Pi.single w (x w)) = ∏ w ∈ s, g (Pi.single w (x w)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert w s hw ih => rw [Finset.sum_insert hw, Finset.prod_insert hw, AddChar.map_add_eq_mul, ih]
  conv_lhs => rw [hx]
  rw [hsum, Finset.prod_congr rfl fun w _ => hα w (x w), ← Complex.exp_sum, ← Finset.mul_sum]
  push_cast
  rfl

/- English proof (translation)
Establish `hinj : Function.Injective (fun w => ((ρ w : F →+* ℝ) : F →* ℝ))`. Introduce `w w' hww`. Establish `h1 : w.embedding = w'.embedding`. Use extensionality with `x`. Rewrite using `[← hρ, ← hρ]`.

Conclude with `congrArg (fun f : F →* ℝ => ((f x : ℝ) : ℂ)) hww`. Rewrite using `[← InfinitePlace.mk_embedding w, h1, InfinitePlace.mk_embedding]`. Establish `hli` using `(linearIndependent_monoidHom F ℝ).comp _ hinj`. Use function extensionality and compare the values at `w`. Use `Fintype.linearIndependent_iff.1 hli β ?_ w` and prove the remaining obligations.

Use function extensionality and compare the values at `c`. Simplify using `using h c`.
-/
theorem places_indep {F : Type} [Field F] [NumberField F] (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (β : InfinitePlace F → ℝ)
    (h : ∀ c : F, ∑ w, β w * ρ w c = 0) : β = 0 := by
  have hinj : Function.Injective (fun w => ((ρ w : F →+* ℝ) : F →* ℝ)) := by
    intro w w' hww
    have h1 : w.embedding = w'.embedding := by
      ext x
      rw [← hρ, ← hρ]
      exact congrArg (fun f : F →* ℝ => ((f x : ℝ) : ℂ)) hww
    rw [← InfinitePlace.mk_embedding w, h1, InfinitePlace.mk_embedding]
  have hli := (linearIndependent_monoidHom F ℝ).comp _ hinj
  funext w
  refine Fintype.linearIndependent_iff.1 hli β ?_ w
  funext c
  simpa using h c

/- English proof (translation)
Establish `hrat : ∀ c : F, ∃ q : ℚ, ∑ w, α w * ρ w c = q`. Introduce `c`. Take `⟨y, hy, hyi⟩` from `((IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic c)).exists_integral_multiple`. Take `⟨r, hr⟩ : ∃ r : 𝓞 F, (r : F) = (y : F) * c` from `⟨IsIntegralClosure.mk' (𝓞 F) (y • c) hyi, (IsIntegralClosure.algebraMap_mk' (𝓞 F) (y • c) hyi).trans (by simp)⟩`. Take `⟨n, hn⟩` from `hint r`.

Use `⟨n / (N * y), ?_⟩` and prove the remaining obligations. Establish `hyR : (y : ℝ) ≠ 0` using `by exact_mod_cast hy`. Establish `hNR : (N : ℝ) ≠ 0` using `by exact_mod_cast hN.ne'`. Establish `h1 : ∑ w, α w * ρ w ((N : F) * (r : F)) = N * y * ∑ w, α w * ρ w c`. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[hr]`. Simplify using `only [map_mul, map_natCast, map_intCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hn` using `[h1]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion. Use `choose q hq using hrat`. Set `L : F →ₗ[ℚ] ℚ` to `{ toFun := q map_add' := fun x y => by`.

Establish `: ((q (x + y) : ℚ) : ℝ) = ((q x + q y : ℚ) : ℝ)`. Use `push_cast`. Rewrite using `[← hq, ← hq, ← hq, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[map_add]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `this` after adjusting the coercions. Use the proof step `map_smul' := fun t x => by`. Establish `: ((q (t • x) : ℚ) : ℝ) = ((t * q x : ℚ) : ℝ)`. Use `push_cast`.

Rewrite using `[← hq, ← hq, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Establish `: t • x = (t : F) * x` using `by simp [Algebra.smul_def]`. Rewrite using `[this, map_mul, map_ratCast]`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `this }` after adjusting the coercions. Set `a : F` to `((Algebra.traceForm ℚ F).toDual (traceForm_nondegenerate ℚ F)).symm L`. Establish `ha : ∀ c, q c = Algebra.trace ℚ F (a * c)`. Introduce `c`. Establish `h1` using `LinearMap.BilinForm.toDual_def (traceForm_nondegenerate ℚ F) (m := a) (n := c)`.

Rewrite `h1` using `[LinearEquiv.apply_symm_apply, Algebra.traceForm_apply]`. Conclude with `h1`. Use `⟨a, fun w => ?_⟩` and prove the remaining obligations. Establish `h0 : (fun w => α w - ρ w a) = 0`. Use `places_indep ρ hρ _ fun c => ?_` and prove the remaining obligations.

Simplify using `only [sub_mul, Finset.sum_sub_distrib]`. Rewrite using `[hq c, ha c, ← htr (a * c)]`. Simplify using `[map_mul]`. Establish `h1` using `congrFun h0 w`. Simplify `h1` using `[sub_eq_zero]`.
-/
theorem exists_dual {F : Type} [Field F] [NumberField F] (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x)
    (htr : ∀ z : F, ∑ w, ρ w z = ((Algebra.trace ℚ F z : ℚ) : ℝ))
    (α : InfinitePlace F → ℝ) (N : ℕ) (hN : 0 < N)
    (hint : ∀ r : 𝓞 F, ∃ n : ℤ, ∑ w, α w * ρ w ((N : F) * (r : F)) = n) :
    ∃ a : F, ∀ w, α w = ρ w a := by
  have hrat : ∀ c : F, ∃ q : ℚ, ∑ w, α w * ρ w c = q := by
    intro c
    obtain ⟨y, hy, hyi⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic c)).exists_integral_multiple
    obtain ⟨r, hr⟩ : ∃ r : 𝓞 F, (r : F) = (y : F) * c :=
      ⟨IsIntegralClosure.mk' (𝓞 F) (y • c) hyi,
        (IsIntegralClosure.algebraMap_mk' (𝓞 F) (y • c) hyi).trans (by simp)⟩
    obtain ⟨n, hn⟩ := hint r
    refine ⟨n / (N * y), ?_⟩
    have hyR : (y : ℝ) ≠ 0 := by exact_mod_cast hy
    have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have h1 : ∑ w, α w * ρ w ((N : F) * (r : F)) = N * y * ∑ w, α w * ρ w c := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [hr]
      simp only [map_mul, map_natCast, map_intCast]
      ring
    rw [h1] at hn
    push_cast
    field_simp
    linarith
  choose q hq using hrat
  let L : F →ₗ[ℚ] ℚ :=
    { toFun := q
      map_add' := fun x y => by
        have : ((q (x + y) : ℚ) : ℝ) = ((q x + q y : ℚ) : ℝ) := by
          push_cast
          rw [← hq, ← hq, ← hq, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [map_add]
          ring
        exact_mod_cast this
      map_smul' := fun t x => by
        have : ((q (t • x) : ℚ) : ℝ) = ((t * q x : ℚ) : ℝ) := by
          push_cast
          rw [← hq, ← hq, Finset.mul_sum]
          refine Finset.sum_congr rfl fun w _ => ?_
          have : t • x = (t : F) * x := by simp [Algebra.smul_def]
          rw [this, map_mul, map_ratCast]
          ring
        exact_mod_cast this }
  let a : F := ((Algebra.traceForm ℚ F).toDual (traceForm_nondegenerate ℚ F)).symm L
  have ha : ∀ c, q c = Algebra.trace ℚ F (a * c) := by
    intro c
    have h1 := LinearMap.BilinForm.toDual_def (traceForm_nondegenerate ℚ F) (m := a) (n := c)
    rw [LinearEquiv.apply_symm_apply, Algebra.traceForm_apply] at h1
    exact h1
  refine ⟨a, fun w => ?_⟩
  have h0 : (fun w => α w - ρ w a) = 0 := by
    refine places_indep ρ hρ _ fun c => ?_
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [hq c, ha c, ← htr (a * c)]
    simp [map_mul]
  have h1 := congrFun h0 w
  simpa [sub_eq_zero] using h1

/- English proof (translation)
Introduce `F _ _ hF ρ e hρ he heρ ψ hψ`. Establish `htr` using `GlobalTheory.CompanionTheory.SW.CoefEis.sum_places_eq_trace F hF ρ hρ`. Establish `hes : Continuous e.toEquiv.symm` using `(Equiv.continuous_symm_iff e.toEquiv).2 he.isOpenMap`. Set `φ : (InfinitePlace F → ℝ) →+ AF F` to `{ toFun := fun x => pairA F (e.symm x) 0 map_zero' := by`. Rewrite using `[map_zero]`.

Both sides reduce to the same expression. Use the proof step `map_add' := fun x y => by`. Rewrite using `[map_add]`. Conclude with `Prod.ext rfl (add_zero _).symm }`. Establish `hφ : Continuous φ` using `(hes.prodMk continuous_const : Continuous fun x => (e.symm x, (0 : Af F)))`.

Take `⟨α, hα⟩` from `pi_char (ψ.compAddMonoidHom φ) (hψ.1.comp hφ) (fun x => hψ.2.1 _)`. Establish `hinf : ∀ x : Ainf F, ψ (pairA F x 0) = Complex.exp (2 * Real.pi * Complex.I * ((∑ w, α w * e x w : ℝ) : ℂ))` using `fun x => by`. Use `hα (e x)` as an intermediate fact. Simplify `this` using `[φ]`. Establish `hsplit : ∀ c : F, ψ (pairA F (algebraMap F (Ainf F) c) 0) * ψ (pairA F 0 (algebraMap F (Af F) c)) = 1` using `fun c => by`.

Rewrite using `[← AddChar.map_add_eq_mul, ← hψ.2.2.1 c]`. Conclude with `congrArg ψ (Prod.ext (add_zero _) (zero_add _))`. Take `⟨N, hN, hNU⟩` from `(GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.2.2.2.2.2.1 _ (GlobalTheory.FinTranslate.eventually_fin_eq_one hψ)`. Establish `hint : ∀ r : 𝓞 F, ∃ n : ℤ, ∑ w, α w * ρ w ((N : F) * (r : F)) = n`. Introduce `r`.

Establish `hr : algebraMap F (Af F) (r : F) ∈ GlobalTheory.CompanionTheory.SW.Core.Oh F` using `((GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.2.2.2.2.1 _).2 ⟨r, rfl⟩`. Establish `h1 : ψ (pairA F 0 (algebraMap F (Af F) ((N : F) * (r : F)))) = 1`. Use `hNU _ hr` as an intermediate fact. Rewrite using `[map_mul, map_natCast]`. Conclude with `this`.

Establish `h2` using `hsplit ((N : F) * (r : F))`. Rewrite `h2` using `[h1, mul_one, hinf, Complex.exp_eq_one_iff]`. Take `⟨n, hn⟩` from `h2`. Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `hI : (2 * Real.pi * Complex.I : ℂ) ≠ 0` using `Complex.two_pi_I_ne_zero`.

Establish `h3 : ((∑ w, α w * e (algebraMap F (Ainf F) ((N : F) * (r : F))) w : ℝ) : ℂ) = n`. Apply `mul_left_cancel₀ hI` to reduce the goal to its premises. Rewrite using `[hn]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [heρ] at h3`.

Conclude with `h3` after adjusting the coercions. Take `⟨a, ha⟩` from `exists_dual ρ hρ htr α N hN hint`. Establish `hinf' : ∀ x : Ainf F, ψ (pairA F x 0) = Complex.exp (2 * Real.pi * Complex.I * ((∑ w, ρ w a * e x w : ℝ) : ℂ))` using `fun x => by`. Rewrite using `[hinf]`. Simplify using `only [ha]`.

Establish `hfin : ∀ c : F, ψ (pairA F 0 (algebraMap F (Af F) c)) = Complex.exp (-(2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F (a * c) : ℚ) : ℂ))` using `fun c => by`. Establish `h1` using `hsplit c`. Establish `h2 : ((∑ w, ρ w a * e (algebraMap F (Ainf F) c) w : ℝ) : ℂ) = ((Algebra.trace ℚ F (a * c) : ℚ) : ℂ)`. Establish `h3` using `htr (a * c)`. Simplify using `only [map_mul] at h3`.

Simplify using `only [heρ]`. Rewrite using `[h3]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite `h1` using `[hinf', h2]`.

Rewrite using `[neg_mul, Complex.exp_neg]`. Conclude with `eq_inv_of_mul_eq_one_right h1`. Establish `hp : Continuous fun y : Af F => pairA F 0 y` using `continuous_const.prodMk continuous_id`. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`.

Establish `h1 : ∀ x : Ainf F, ψ (pairA F x 0) = 1` using `fun x => by`. Rewrite using `[hinf']`. Simplify using the standard rewrite rules. Establish `h2 : ∀ y : Af F, ψ (pairA F 0 y) = 1`. Introduce `y`.

Establish `hc : Continuous fun y : Af F => ψ (pairA F 0 y)` using `hψ.1.comp hp`. Use `(GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.2.2.2.1.induction_on y (isClosed_eq hc continuous_const) fun c => ?_` and prove the remaining obligations. Rewrite using `[hfin]`. Simplify using the standard rewrite rules. Take `⟨z, hz⟩` from `hψ.2.2.2`.

Apply `hz` to reduce the goal to its premises. Establish `h3 : z = pairA F z.1 0 + pairA F 0 z.2` using `Prod.ext (add_zero _).symm (zero_add _).symm`. Rewrite using `[h3, AddChar.map_add_eq_mul, h1, h2, one_mul]`. Set `ψf : AddChar (Af F) ℂ` to `{ toFun := fun y => ψ (pairA F 0 (algebraMap F (Af F) a⁻¹ * y)) map_zero_eq_one' := by`. Rewrite using `[mul_zero]`.

Conclude with `ψ.map_zero_eq_one`. Use the proof step `map_add_eq_mul' := fun x y => by`. Rewrite using `[mul_add, ← AddChar.map_add_eq_mul]`. Conclude with `congrArg ψ (Prod.ext (add_zero _).symm rfl) }`. Use `⟨a, ha0, hinf', ψf, ⟨?_, fun b => ?_⟩, fun y => ?_⟩` and prove the remaining obligations.

Conclude with `hψ.1.comp (hp.comp (continuous_const.mul continuous_id))`. Use `show ψ (pairA F 0 (algebraMap F (Af F) a⁻¹ * algebraMap F (Af F) b)) = _`. Rewrite using `[← map_mul, hfin, mul_inv_cancel_left₀ ha0]`. Use `show _ = ψ (pairA F 0 (algebraMap F (Af F) a⁻¹ * (algebraMap F (Af F) a * y)))`. Rewrite using `[← mul_assoc, ← map_mul, inv_mul_cancel₀ ha0, map_one, one_mul]`.
-/
theorem exists_char_data : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → IsHomeomorph e → (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∃ a : F, a ≠ 0 ∧ (∀ x : Ainf F, ψ (pairA F x 0) = Complex.exp (2 * Real.pi * Complex.I * ((∑ w, ρ w a * e x w : ℝ) : ℂ))) ∧ ∃ ψf : AddChar (Af F) ℂ, GlobalTheory.CompanionTheory.SW.Core.IsStdChar F ψf ∧ ∀ y : Af F, ψ (pairA F 0 y) = ψf (algebraMap F (Af F) a * y) := by
  intro F _ _ hF ρ e hρ he heρ ψ hψ
  classical
  have htr := GlobalTheory.CompanionTheory.SW.CoefEis.sum_places_eq_trace F hF ρ hρ
  have hes : Continuous e.toEquiv.symm := (Equiv.continuous_symm_iff e.toEquiv).2 he.isOpenMap

  let φ : (InfinitePlace F → ℝ) →+ AF F :=
    { toFun := fun x => pairA F (e.symm x) 0
      map_zero' := by
        rw [map_zero]
        rfl
      map_add' := fun x y => by
        rw [map_add]
        exact Prod.ext rfl (add_zero _).symm }
  have hφ : Continuous φ := (hes.prodMk continuous_const : Continuous fun x => (e.symm x, (0 : Af F)))
  obtain ⟨α, hα⟩ := pi_char (ψ.compAddMonoidHom φ) (hψ.1.comp hφ) (fun x => hψ.2.1 _)
  have hinf : ∀ x : Ainf F, ψ (pairA F x 0) =
      Complex.exp (2 * Real.pi * Complex.I * ((∑ w, α w * e x w : ℝ) : ℂ)) := fun x => by
    have := hα (e x)
    simpa [φ] using this
  have hsplit : ∀ c : F, ψ (pairA F (algebraMap F (Ainf F) c) 0) *
      ψ (pairA F 0 (algebraMap F (Af F) c)) = 1 := fun c => by
    rw [← AddChar.map_add_eq_mul, ← hψ.2.2.1 c]
    exact congrArg ψ (Prod.ext (add_zero _) (zero_add _))

  obtain ⟨N, hN, hNU⟩ := (GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.2.2.2.2.2.1 _ (GlobalTheory.FinTranslate.eventually_fin_eq_one hψ)
  have hint : ∀ r : 𝓞 F, ∃ n : ℤ, ∑ w, α w * ρ w ((N : F) * (r : F)) = n := by
    intro r
    have hr : algebraMap F (Af F) (r : F) ∈ GlobalTheory.CompanionTheory.SW.Core.Oh F :=
      ((GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.2.2.2.2.1 _).2 ⟨r, rfl⟩
    have h1 : ψ (pairA F 0 (algebraMap F (Af F) ((N : F) * (r : F)))) = 1 := by
      have := hNU _ hr
      rw [map_mul, map_natCast]
      exact this
    have h2 := hsplit ((N : F) * (r : F))
    rw [h1, mul_one, hinf, Complex.exp_eq_one_iff] at h2
    obtain ⟨n, hn⟩ := h2
    refine ⟨n, ?_⟩
    have hI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
    have h3 : ((∑ w, α w * e (algebraMap F (Ainf F) ((N : F) * (r : F))) w : ℝ) : ℂ) = n := by
      apply mul_left_cancel₀ hI
      rw [hn]
      ring
    simp only [heρ] at h3
    exact_mod_cast h3
  obtain ⟨a, ha⟩ := exists_dual ρ hρ htr α N hN hint
  have hinf' : ∀ x : Ainf F, ψ (pairA F x 0) =
      Complex.exp (2 * Real.pi * Complex.I * ((∑ w, ρ w a * e x w : ℝ) : ℂ)) := fun x => by
    rw [hinf]
    simp only [ha]
  have hfin : ∀ c : F, ψ (pairA F 0 (algebraMap F (Af F) c)) =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F (a * c) : ℚ) : ℂ)) := fun c => by
    have h1 := hsplit c
    have h2 : ((∑ w, ρ w a * e (algebraMap F (Ainf F) c) w : ℝ) : ℂ) = ((Algebra.trace ℚ F (a * c) : ℚ) : ℂ) := by
      have h3 := htr (a * c)
      simp only [map_mul] at h3
      simp only [heρ]
      rw [h3]
      push_cast
      rfl
    rw [hinf', h2] at h1
    rw [neg_mul, Complex.exp_neg]
    exact eq_inv_of_mul_eq_one_right h1
  have hp : Continuous fun y : Af F => pairA F 0 y := continuous_const.prodMk continuous_id
  have ha0 : a ≠ 0 := by
    rintro rfl
    have h1 : ∀ x : Ainf F, ψ (pairA F x 0) = 1 := fun x => by
      rw [hinf']
      simp
    have h2 : ∀ y : Af F, ψ (pairA F 0 y) = 1 := by
      intro y
      have hc : Continuous fun y : Af F => ψ (pairA F 0 y) := hψ.1.comp hp
      refine (GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.2.2.2.1.induction_on y (isClosed_eq hc continuous_const) fun c => ?_
      rw [hfin]
      simp
    obtain ⟨z, hz⟩ := hψ.2.2.2
    apply hz
    have h3 : z = pairA F z.1 0 + pairA F 0 z.2 := Prod.ext (add_zero _).symm (zero_add _).symm
    rw [h3, AddChar.map_add_eq_mul, h1, h2, one_mul]

  let ψf : AddChar (Af F) ℂ :=
    { toFun := fun y => ψ (pairA F 0 (algebraMap F (Af F) a⁻¹ * y))
      map_zero_eq_one' := by
        rw [mul_zero]
        exact ψ.map_zero_eq_one
      map_add_eq_mul' := fun x y => by
        rw [mul_add, ← AddChar.map_add_eq_mul]
        exact congrArg ψ (Prod.ext (add_zero _).symm rfl) }
  refine ⟨a, ha0, hinf', ψf, ⟨?_, fun b => ?_⟩, fun y => ?_⟩
  · exact hψ.1.comp (hp.comp (continuous_const.mul continuous_id))
  · show ψ (pairA F 0 (algebraMap F (Af F) a⁻¹ * algebraMap F (Af F) b)) = _
    rw [← map_mul, hfin, mul_inv_cancel_left₀ ha0]
  · show _ = ψ (pairA F 0 (algebraMap F (Af F) a⁻¹ * (algebraMap F (Af F) a * y)))
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha0, map_one, one_mul]

end GlobalTheory.CompanionTheory.Glob.CharAF
