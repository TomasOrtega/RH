import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ExpNegGlue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermUnipotentIntegralVariant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermAutomorphicCriterion

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs

namespace PExpFin

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}

omit [NumberField E] [IsTotallyComplex E] in
/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _`. Rewrite using `[Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `i w`.

Simplify using `only [Pi.mul_apply]`. Apply the tactic sequence `split_ifs <;> simp [← Complex.exp_add]`.
-/
theorem aInf_add (r : ℕ) (s t : ℝ) : aInf E N r (s + t) = aInf E N r s * aInf E N r t := by
  apply Units.ext
  change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i w
  simp only [Pi.mul_apply]
  split_ifs <;> simp [← Complex.exp_add]

/- English proof (translation)
Rewrite using `[aT, aT, aT, aInf_add, map_mul]`.
-/
theorem aT_add (r : ℕ) (s t : ℝ) : aT E N r (s + t) = aT E N r s * aT E N r t := by
  rw [aT, aT, aT, aInf_add, map_mul]

/- English proof (translation)
Establish `h : aInf E N r 0 = 1` using `Units.ext (by`. Express the relevant statement in the definitionally equal form `Matrix.diagonal _ = 1`. Rewrite using `[← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i w`.

Use the proof step `simp)`. Rewrite using `[aT, h, map_one]`.
-/
theorem aT_zero (r : ℕ) : aT E N r 0 = 1 := by
  have h : aInf E N r 0 = 1 := Units.ext (by
    change Matrix.diagonal _ = 1
    rw [← Matrix.diagonal_one]
    congr 1
    funext i w
    simp)
  rw [aT, h, map_one]

/- English proof (translation)
Rewrite using `[← aT_add, add_comm, aT_add]`.
-/
theorem aT_comm (r : ℕ) (u v : ℝ) : aT E N r u * aT E N r v = aT E N r v * aT E N r u := by
  rw [← aT_add, add_comm, aT_add]

def Kl (r : ℕ) (s : ℝ) (p : ℂ[X]) (F : GA E N → ℂ) : Prop :=
  ∀ g, ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * F (aT E N r (s * j) * g) = 0

def klSub (r : ℕ) (s : ℝ) (p : ℂ[X]) : Submodule ℂ (GA E N → ℂ) where
  carrier := {F | Kl r s p F}
  add_mem' := fun {F G} (hF : Kl r s p F) (hG : Kl r s p G) g => by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hF g, hG g, add_zero]
  zero_mem' := fun g => by simp
  smul_mem' := fun c F (hF : Kl r s p F) g => by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_zero c, ← hF g, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Introduce `g`. Rewrite using `[← h (aT E N r t * g)]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `show _ * F (aT E N r t * (aT E N r (s * j) * g)) = _`. Rewrite using `[← mul_assoc, ← mul_assoc, aT_comm]`.
-/
theorem kl_translate {r : ℕ} {s : ℝ} {p : ℂ[X]} {F : GA E N → ℂ} (h : Kl r s p F) (t : ℝ) :
    Kl r s p (fun g => F (aT E N r t * g)) := by
  intro g
  rw [← h (aT E N r t * g)]
  refine Finset.sum_congr rfl fun j _ => ?_
  show _ * F (aT E N r t * (aT E N r (s * j) * g)) = _
  rw [← mul_assoc, ← mul_assoc, aT_comm]

/- English proof (translation)
Establish `hle : Submodule.span ℂ (Set.range fun t : ℝ => fun g => F (aT E N r t * g)) ≤ klSub r s p`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨t, rfl⟩`. Conclude with `kl_translate h t`. Conclude with `hle hF'`.
-/
theorem kl_span {r : ℕ} {s : ℝ} {p : ℂ[X]} {F : GA E N → ℂ} (h : Kl r s p F) {F' : GA E N → ℂ}
    (hF' : F' ∈ Submodule.span ℂ (Set.range fun t : ℝ => fun g => F (aT E N r t * g))) : Kl r s p F' := by
  have hle : Submodule.span ℂ (Set.range fun t : ℝ => fun g => F (aT E N r t * g)) ≤ klSub r s p := by
    rw [Submodule.span_le]
    rintro _ ⟨t, rfl⟩
    exact kl_translate h t
  exact hle hF'

/- English proof (translation)
Introduce `g`. Rewrite using `[← h (g * k)]`. Simplify using `only [mul_assoc]`.
-/
theorem kl_right {r : ℕ} {s : ℝ} {p : ℂ[X]} {F : GA E N → ℂ} (h : Kl r s p F) (k : GA E N) :
    Kl r s p (fun g => F (g * k)) := by
  intro g
  rw [← h (g * k)]
  simp only [mul_assoc]

/- English proof (translation)
Introduce `g`. Establish `hd : ∀ j : ℕ, DifferentiableAt ℝ (chart F.1 (aT E N r (s * j) * g)) (oneL E N)` using `fun j => differentiableAt_chart F.2 _`. Establish `hz : (fun x => ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j • chart F.1 (aT E N r (s * j) * g) x) = 0`. Use function extensionality and compare the values at `x`. Distinguish the cases in `hx : IsUnit (Matrix.of x)`.

Simplify using `only [chart, dif_pos hx, smul_eq_mul, Pi.zero_apply]`. Rewrite using `[← h (g * infGL E N hx.unit)]`. Simplify using `only [mul_assoc]`. Simplify using `[chart, dif_neg hx]`. Establish `hs : HasFDerivAt (fun x => ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j • chart F.1 (aT E N r (s * j) * g) x) (∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j • fderiv ℝ (chart F.1 (aT E N r (s * j) * g)) (oneL E N)) (oneL E N)`.

Conclude with `HasFDerivAt.fun_sum fun j _ => (hd j).hasFDerivAt.const_smul (p.coeff j)`. Rewrite `hs` using `[hz]`. Establish `h2` using `congrArg (fun L : Lie E N →L[ℝ] ℂ => L X) (hs.unique (hasFDerivAt_const 0 _))`. Simplify using `only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, zero_apply] at h2`. Simplify `h2` using `only [lie_apply, lieD]`.
-/
theorem kl_lie {r : ℕ} {s : ℝ} {p : ℂ[X]} {F : Sm E N} (h : Kl r s p F.1) (X : Lie E N) :
    Kl r s p (lie E N X F).1 := by
  intro g
  have hd : ∀ j : ℕ, DifferentiableAt ℝ (chart F.1 (aT E N r (s * j) * g)) (oneL E N) :=
    fun j => differentiableAt_chart F.2 _
  have hz : (fun x => ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j • chart F.1 (aT E N r (s * j) * g) x) = 0 := by
    funext x
    by_cases hx : IsUnit (Matrix.of x)
    · simp only [chart, dif_pos hx, smul_eq_mul, Pi.zero_apply]
      rw [← h (g * infGL E N hx.unit)]
      simp only [mul_assoc]
    · simp [chart, dif_neg hx]
  have hs : HasFDerivAt (fun x => ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j • chart F.1 (aT E N r (s * j) * g) x)
      (∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j • fderiv ℝ (chart F.1 (aT E N r (s * j) * g)) (oneL E N))
      (oneL E N) := by
    exact HasFDerivAt.fun_sum fun j _ => (hd j).hasFDerivAt.const_smul (p.coeff j)
  rw [hz] at hs
  have h2 := congrArg (fun L : Lie E N →L[ℝ] ℂ => L X) (hs.unique (hasFDerivAt_const 0 _))
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply,
    smul_eq_mul, zero_apply] at h2
  simpa only [lie_apply, lieD] using h2

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨g, hg⟩ : ∃ g, F g ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Conclude with `h0 (funext hcon)`. Establish `e : ∀ j : ℕ, Complex.exp (c * ((s * j : ℝ) : ℂ)) = Complex.exp (c * s) ^ j`.

Introduce `j`. Rewrite using `[← Complex.exp_nat_mul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `h1` using `h g`. Simplify using `only [hc, e] at h1`. Rewrite using `[Polynomial.IsRoot, Polynomial.eval_eq_sum_range]`. Establish `h2 : (∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * Complex.exp (c * s) ^ j) * F g = 0`. Rewrite using `[← h1, Finset.sum_mul]`.

Conclude with `Finset.sum_congr rfl fun j _ => by ring`. Conclude with `(mul_eq_zero.1 h2).resolve_right hg`.
-/
theorem kl_eigen {r : ℕ} {s : ℝ} {p : ℂ[X]} {F : GA E N → ℂ} (h : Kl r s p F) (h0 : F ≠ 0) {c : ℂ}
    (hc : ∀ (t : ℝ) g, F (aT E N r t * g) = Complex.exp (c * t) * F g) : p.IsRoot (Complex.exp (c * s)) := by
  obtain ⟨g, hg⟩ : ∃ g, F g ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact h0 (funext hcon)
  have e : ∀ j : ℕ, Complex.exp (c * ((s * j : ℝ) : ℂ)) = Complex.exp (c * s) ^ j := by
    intro j
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h1 := h g
  simp only [hc, e] at h1
  rw [Polynomial.IsRoot, Polynomial.eval_eq_sum_range]
  have h2 : (∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * Complex.exp (c * s) ^ j) * F g = 0 := by
    rw [← h1, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  exact (mul_eq_zero.1 h2).resolve_right hg

/- English proof (translation)
Use `set W := Submodule.span ℂ (Set.range fun t : ℝ => fun g => F (aT E N r t * g))`. Set `L : Module.End ℂ (GA E N → ℂ)` to `{ toFun := fun f g => f (aT E N r s * g) map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Establish `hW : ∀ f ∈ W, L f ∈ W`. Establish `hle : W ≤ W.comap L`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨t, rfl⟩`. Use `Submodule.subset_span ⟨t + s, funext fun g => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `F (aT E N r (t + s) * g) = F (aT E N r t * (aT E N r s * g))`. Rewrite using `[aT_add, mul_assoc]`. Conclude with `fun f hf => hle hf`.

Set `L'` to `L.restrict hW`. Establish `hpow : ∀ (i : ℕ) (f : GA E N → ℂ), (L ^ i) f = fun g => f (aT E N r (s * i) * g)`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero`.

Introduce `f`. Use function extensionality and compare the values at `g`. Simplify using `[aT_zero]`. Consider the case `succ i ih`. Introduce `f`.

Use function extensionality and compare the values at `g`. Rewrite using `[pow_succ, Module.End.mul_apply, ih]`. Express the relevant statement in the definitionally equal form `f (aT E N r s * (aT E N r (s * i) * g)) = _`. Rewrite using `[← mul_assoc, ← aT_add]`. Use `congr 3`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hpow' : ∀ (i : ℕ) (x : W), ((L' ^ i) x).1 = (L ^ i) x.1`. Introduce `i`. Proceed by induction on `i with`.

Consider the case `zero => intro x`. Both sides reduce to the same expression. Consider the case `succ i ih`. Introduce `x`. Rewrite using `[pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]`.

Both sides reduce to the same expression. Establish `hF : F ∈ W` using `Submodule.subset_span ⟨0, funext fun g => by simp [aT_zero]⟩`. Use `⟨L'.charpoly, LinearMap.charpoly_monic L', fun g => ?_⟩` and prove the remaining obligations. Establish `h0` using `congrArg (fun T : Module.End ℂ W => (T ⟨F, hF⟩).1 g) (LinearMap.aeval_self_charpoly L')`. Rewrite `h0` using `[Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]`.

Simplify using `only [LinearMap.smul_apply, Submodule.coe_smul, hpow', hpow, Pi.smul_apply, smul_eq_mul, LinearMap.zero_apply, ZeroMemClass.coe_zero, Pi.zero_apply] at h0`. Conclude with `h0`.
-/
theorem exists_kl (r : ℕ) (s : ℝ) (F : GA E N → ℂ)
    (hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun t : ℝ => fun g => F (aT E N r t * g)))) :
    ∃ p : ℂ[X], p.Monic ∧ Kl r s p F := by
  set W := Submodule.span ℂ (Set.range fun t : ℝ => fun g => F (aT E N r t * g))
  let L : Module.End ℂ (GA E N → ℂ) :=
    { toFun := fun f g => f (aT E N r s * g)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hW : ∀ f ∈ W, L f ∈ W := by
    have hle : W ≤ W.comap L := by
      rw [Submodule.span_le]
      rintro _ ⟨t, rfl⟩
      refine Submodule.subset_span ⟨t + s, funext fun g => ?_⟩
      change F (aT E N r (t + s) * g) = F (aT E N r t * (aT E N r s * g))
      rw [aT_add, mul_assoc]
    exact fun f hf => hle hf
  let L' := L.restrict hW
  have hpow : ∀ (i : ℕ) (f : GA E N → ℂ), (L ^ i) f = fun g => f (aT E N r (s * i) * g) := by
    intro i
    induction i with
    | zero =>
      intro f
      funext g
      simp [aT_zero]
    | succ i ih =>
      intro f
      funext g
      rw [pow_succ, Module.End.mul_apply, ih]
      change f (aT E N r s * (aT E N r (s * i) * g)) = _
      rw [← mul_assoc, ← aT_add]
      congr 3
      push_cast
      ring
  have hpow' : ∀ (i : ℕ) (x : W), ((L' ^ i) x).1 = (L ^ i) x.1 := by
    intro i
    induction i with
    | zero => intro x; rfl
    | succ i ih =>
      intro x
      rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
      rfl
  have hF : F ∈ W := Submodule.subset_span ⟨0, funext fun g => by simp [aT_zero]⟩
  refine ⟨L'.charpoly, LinearMap.charpoly_monic L', fun g => ?_⟩
  have h0 := congrArg (fun T : Module.End ℂ W => (T ⟨F, hF⟩).1 g) (LinearMap.aeval_self_charpoly L')
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply] at h0
  simp only [LinearMap.smul_apply, Submodule.coe_smul, hpow', hpow, Pi.smul_apply, smul_eq_mul,
    LinearMap.zero_apply, ZeroMemClass.coe_zero, Pi.zero_apply] at h0
  exact h0

section CT

variable {r : ℕ} [MeasurableSpace (BlockIx N r → Ad E)] [BorelSpace (BlockIx N r → Ad E)]
  (μ : Measure (BlockIx N r → Ad E)) [μ.IsAddHaarMeasure] (𝓕 : Set (BlockIx N r → Ad E))

/- English proof (translation)
Use function extensionality and compare the values at `g`. Conclude with `integral_add (GlobalTheory.CompanionTheory.CTFin.Central.integrable_unip_mul μ 𝓕 h𝓕 hφ.left hφ.level g) (GlobalTheory.CompanionTheory.CTFin.Central.integrable_unip_mul μ 𝓕 h𝓕 hψ.left hψ.level g)`.
-/
theorem ct_add (h𝓕 : IsAddFundamentalDomain (ratN E N r) 𝓕 μ) {φ ψ : Sm E N} (hφ : IsAutForm φ)
    (hψ : IsAutForm ψ) : PositivityTheory.Affgl.CT.ct μ 𝓕 (φ + ψ).1 = PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 + PositivityTheory.Affgl.CT.ct μ 𝓕 ψ.1 := by
  funext g
  exact integral_add (GlobalTheory.CompanionTheory.CTFin.Central.integrable_unip_mul μ 𝓕 h𝓕 hφ.left hφ.level g)
    (GlobalTheory.CompanionTheory.CTFin.Central.integrable_unip_mul μ 𝓕 h𝓕 hψ.left hψ.level g)

omit [BorelSpace (BlockIx N r → Ad E)] [μ.IsAddHaarMeasure] in
/- English proof (translation)
Use function extensionality and compare the values at `g`. Conclude with `integral_smul c _`.
-/
theorem ct_smul (c : ℂ) (φ : Sm E N) :
    PositivityTheory.Affgl.CT.ct μ 𝓕 (c • φ).1 = c • PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 := by
  funext g
  exact integral_smul c _

/- English proof (translation)
Consider the cases of `o with`. Consider the case `fin k`. Establish `e : PositivityTheory.Affgl.CT.ct μ 𝓕 (act (.fin k) φ).1 = fun g => PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 (g * finGL E N k)`. Use function extensionality and compare the values at `g`. Conclude with `congrArg (fun f : (BlockIx N r → Ad E) → ℂ => ∫ x in 𝓕, f x ∂μ) (funext fun x => congrArg φ.1 (mul_assoc _ _ _))`.

Rewrite using `[e]`. Conclude with `kl_right h _`. Consider the case `cpt k`. Establish `e : PositivityTheory.Affgl.CT.ct μ 𝓕 (act (.cpt k) φ).1 = fun g => PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 (g * infGL E N (Unitary.toUnits k))`. Use function extensionality and compare the values at `g`.

Conclude with `congrArg (fun f : (BlockIx N r → Ad E) → ℂ => ∫ x in 𝓕, f x ∂μ) (funext fun x => congrArg φ.1 (mul_assoc _ _ _))`. Rewrite using `[e]`. Conclude with `kl_right h _`. Consider the case `lie X`. Take `⟨F, hF1, hF2⟩` from `GlobalTheory.CompanionTheory.CTSmooth.ct_smooth E N r φ hφ.left hφ.level μ 𝓕 inferInstance h𝓕`.

Establish `e1 : F.1 = PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1` using `funext hF1`. Establish `e2 : (lie E N X F).1 = PositivityTheory.Affgl.CT.ct μ 𝓕 (act (.lie X) φ).1` using `funext (hF2 X)`. Rewrite using `[← e2]`. Conclude with `kl_lie (e1 ▸ h) X`.
-/
theorem kl_act (h𝓕 : IsAddFundamentalDomain (ratN E N r) 𝓕 μ) {s : ℝ} {p : ℂ[X]} {φ : Sm E N}
    (hφ : IsAutForm φ) (h : Kl r s p (PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1)) (o : Op E N) :
    Kl r s p (PositivityTheory.Affgl.CT.ct μ 𝓕 (act o φ).1) := by
  cases o with
  | fin k =>
    have e : PositivityTheory.Affgl.CT.ct μ 𝓕 (act (.fin k) φ).1 = fun g => PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 (g * finGL E N k) := by
      funext g
      exact congrArg (fun f : (BlockIx N r → Ad E) → ℂ => ∫ x in 𝓕, f x ∂μ)
        (funext fun x => congrArg φ.1 (mul_assoc _ _ _))
    rw [e]
    exact kl_right h _
  | cpt k =>
    have e : PositivityTheory.Affgl.CT.ct μ 𝓕 (act (.cpt k) φ).1 =
        fun g => PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 (g * infGL E N (Unitary.toUnits k)) := by
      funext g
      exact congrArg (fun f : (BlockIx N r → Ad E) → ℂ => ∫ x in 𝓕, f x ∂μ)
        (funext fun x => congrArg φ.1 (mul_assoc _ _ _))
    rw [e]
    exact kl_right h _
  | lie X =>
    obtain ⟨F, hF1, hF2⟩ := GlobalTheory.CompanionTheory.CTSmooth.ct_smooth E N r φ hφ.left hφ.level μ 𝓕 inferInstance h𝓕
    have e1 : F.1 = PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 := funext hF1
    have e2 : (lie E N X F).1 = PositivityTheory.Affgl.CT.ct μ 𝓕 (act (.lie X) φ).1 := funext (hF2 X)
    rw [← e2]
    exact kl_lie (e1 ▸ h) X

/- English proof (translation)
Set `W : Submodule ℂ (Sm E N)` to `{ carrier := {φ | φ ∈ V ∧ Kl r s p (PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1)} add_mem' := fun {φ ψ} hφ hψ => ⟨V.add_mem hφ.1 hψ.1, by`. Rewrite using `[ct_add μ 𝓕 h𝓕 (hV.aut φ hφ.1) (hV.aut ψ hψ.1)]`. Conclude with `(klSub r s p).add_mem hφ.2 hψ.2⟩`. Use the proof step `zero_mem' := ⟨V.zero_mem, by`. Establish `: PositivityTheory.Affgl.CT.ct μ 𝓕 (0 : Sm E N).1 = 0`.

Use function extensionality and compare the values at `g`. Simplify using `[PositivityTheory.Affgl.CT.ct]`. Rewrite using `[this]`. Conclude with `(klSub r s p).zero_mem⟩`. Use the proof step `smul_mem' := fun c φ hφ => ⟨V.smul_mem c hφ.1, by`.

Rewrite using `[ct_smul]`. Conclude with `(klSub r s p).smul_mem c hφ.2⟩ }`. Establish `hle : W ≤ V` using `fun φ hφ => hφ.1`. Establish `hst : IsStable W` using `fun o φ hφ => ⟨hV.stable o φ hφ.1, kl_act μ 𝓕 h𝓕 (hV.aut φ hφ.1) hφ.2 o⟩`. Break down `hV.irred W hle hst with hW | hW` into its components or cases.

Establish `: φ₀ ∈ W` using `⟨hφ₀, hk⟩`. Rewrite `this` using `[hW]`. Conclude with `absurd ((Submodule.mem_bot ℂ).1 this) h0`. Introduce `φ hφ`. Rewrite `hφ` using `[← hW]`.

Conclude with `hφ.2`.
-/
theorem kl_all (h𝓕 : IsAddFundamentalDomain (ratN E N r) 𝓕 μ) {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V)
    {s : ℝ} {p : ℂ[X]} {φ₀ : Sm E N} (hφ₀ : φ₀ ∈ V) (h0 : φ₀ ≠ 0) (hk : Kl r s p (PositivityTheory.Affgl.CT.ct μ 𝓕 φ₀.1)) :
    ∀ φ ∈ V, Kl r s p (PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1) := by
  let W : Submodule ℂ (Sm E N) :=
    { carrier := {φ | φ ∈ V ∧ Kl r s p (PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1)}
      add_mem' := fun {φ ψ} hφ hψ => ⟨V.add_mem hφ.1 hψ.1, by
        rw [ct_add μ 𝓕 h𝓕 (hV.aut φ hφ.1) (hV.aut ψ hψ.1)]
        exact (klSub r s p).add_mem hφ.2 hψ.2⟩
      zero_mem' := ⟨V.zero_mem, by
        have : PositivityTheory.Affgl.CT.ct μ 𝓕 (0 : Sm E N).1 = 0 := by
          funext g
          simp [PositivityTheory.Affgl.CT.ct]
        rw [this]
        exact (klSub r s p).zero_mem⟩
      smul_mem' := fun c φ hφ => ⟨V.smul_mem c hφ.1, by
        rw [ct_smul]
        exact (klSub r s p).smul_mem c hφ.2⟩ }
  have hle : W ≤ V := fun φ hφ => hφ.1
  have hst : IsStable W := fun o φ hφ => ⟨hV.stable o φ hφ.1, kl_act μ 𝓕 h𝓕 (hV.aut φ hφ.1) hφ.2 o⟩
  rcases hV.irred W hle hst with hW | hW
  · have : φ₀ ∈ W := ⟨hφ₀, hk⟩
    rw [hW] at this
    exact absurd ((Submodule.mem_bot ℂ).1 this) h0
  · intro φ hφ
    rw [← hW] at hφ
    exact hφ.2

end CT

/- English proof (translation)
Rewrite `h1`, `h2` using `[Complex.exp_eq_exp_iff_exists_int]`. Take `⟨n, hn⟩` from `h1`. Take `⟨m, hm⟩` from `h2`. Simplify using `only [Complex.ofReal_one, mul_one] at hn`. Rewrite `hm` using `[hn]`.

Establish `e : ((n : ℂ) * ((√2 : ℝ) : ℂ) - m) * (2 * Real.pi * Complex.I) = 0` using `by linear_combination hm`. Establish `e2` using `congrArg Complex.re ((mul_eq_zero.1 e).resolve_right Complex.two_pi_I_ne_zero)`. Simplify using `at e2`. Distinguish the cases in `hn0 : n = 0`. Rewrite using `[hn, hn0]`.

Simplify using the standard rewrite rules. Conclude with `absurd (by linarith : (n : ℝ) * √2 = m) ((irrational_sqrt_two.intCast_mul hn0).ne_int m)`.
-/
theorem exp_pair_inj {c c' : ℂ} (h1 : Complex.exp (c * ((1 : ℝ) : ℂ)) = Complex.exp (c' * ((1 : ℝ) : ℂ)))
    (h2 : Complex.exp (c * ((√2 : ℝ) : ℂ)) = Complex.exp (c' * ((√2 : ℝ) : ℂ))) : c = c' := by
  rw [Complex.exp_eq_exp_iff_exists_int] at h1 h2
  obtain ⟨n, hn⟩ := h1
  obtain ⟨m, hm⟩ := h2
  simp only [Complex.ofReal_one, mul_one] at hn
  rw [hn] at hm
  have e : ((n : ℂ) * ((√2 : ℝ) : ℂ) - m) * (2 * Real.pi * Complex.I) = 0 := by linear_combination hm
  have e2 := congrArg Complex.re ((mul_eq_zero.1 e).resolve_right Complex.two_pi_I_ne_zero)
  simp at e2
  by_cases hn0 : n = 0
  · rw [hn, hn0]
    simp
  · exact absurd (by linarith : (n : ℝ) * √2 = m) ((irrational_sqrt_two.intCast_mul hn0).ne_int m)

end PExpFin

open PExpFin in
/- English proof (translation)
Introduce `E _ _ _ N V hV r hr hrN`. Take `⟨φ₀, hφ₀, h0⟩` from `(Submodule.ne_bot_iff _).1 hV.ne_bot`. Take `⟨-, -, -, hDct⟩` from `hD E N`. Set `_ : MeasurableSpace (BlockIx N r → Ad E)` to `borel _`. Establish `_ : BorelSpace (BlockIx N r → Ad E)` using `⟨rfl⟩`.

Take `⟨μ, 𝓕, hμ, h𝓕, -⟩` from `(hDct φ₀ (hV.aut φ₀ hφ₀) r hr hrN).1`. Establish `_` using `hμ`. Establish `hpoly : ∀ s : ℝ, ∃ p : ℂ[X], p.Monic ∧ ∀ φ ∈ V, Kl r s p (PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1)`. Introduce `s`. Take `⟨p, hp, hk⟩` from `exists_kl r s _ (hT E N φ₀ (hV.aut φ₀ hφ₀) r hr hrN (PositivityTheory.Affgl.CT.ct μ 𝓕 φ₀.1) ⟨μ, 𝓕, hμ, h𝓕, rfl⟩)`.

Conclude with `⟨p, hp, kl_all μ 𝓕 h𝓕 hV hφ₀ h0 hk⟩`. Take `⟨p₁, hp₁, hk₁⟩` from `hpoly 1`. Take `⟨p₂, hp₂, hk₂⟩` from `hpoly √2`. Set `f : ℂ → ℂ × ℂ` to `fun c => (Complex.exp (c * ((1 : ℝ) : ℂ)), Complex.exp (c * ((√2 : ℝ) : ℂ)))`. Establish `hfin : ({z | p₁.IsRoot z} ×ˢ {z | p₂.IsRoot z} : Set (ℂ × ℂ)).Finite` using `(Polynomial.finite_setOfPred_isRoot hp₁.ne_zero).prod (Polynomial.finite_setOfPred_isRoot hp₂.ne_zero)`.

Use `(hfin.preimage (f := f) fun c _ c' _ e => exp_pair_inj (congrArg Prod.fst e) (congrArg Prod.snd e)).subset ?_` and prove the remaining obligations. Introduce and unpack `c ⟨φ, hφ, F₀, hCT, F, hFspan, hF0, hFe⟩`. Take `⟨-, huniq⟩` from `hDct φ (hV.aut φ hφ) r hr hrN`. Take `⟨c₁, -, e₁⟩` from `huniq F₀ hCT`. Take `⟨c₂, hc₂, e₂⟩` from `huniq _ ⟨μ, 𝓕, hμ, h𝓕, rfl⟩`.

Establish `eF₀ : F₀ = (c₁ / c₂) • PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1`. Use function extensionality and compare the values at `g`. Rewrite using `[e₁, Pi.smul_apply, e₂, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Establish `hk : ∀ s p, Kl r s p (PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1) → p.IsRoot (Complex.exp (c * s))`.

Introduce `s p h`. Use `kl_eigen (kl_span ?_ hFspan) hF0 hFe` and prove the remaining obligations. Rewrite using `[eF₀]`. Conclude with `(klSub r s p).smul_mem _ h`. Conclude with `⟨hk 1 p₁ (hk₁ φ hφ), hk √2 p₂ (hk₂ φ hφ)⟩`.
-/
theorem expFin_of (hD : Dict) (hT : FinTr) : ExpFin := by
  intro E _ _ _ N V hV r hr hrN
  obtain ⟨φ₀, hφ₀, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  obtain ⟨-, -, -, hDct⟩ := hD E N
  let _ : MeasurableSpace (BlockIx N r → Ad E) := borel _
  have _ : BorelSpace (BlockIx N r → Ad E) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, -⟩ := (hDct φ₀ (hV.aut φ₀ hφ₀) r hr hrN).1
  have _ := hμ
  have hpoly : ∀ s : ℝ, ∃ p : ℂ[X], p.Monic ∧ ∀ φ ∈ V, Kl r s p (PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1) := by
    intro s
    obtain ⟨p, hp, hk⟩ := exists_kl r s _
      (hT E N φ₀ (hV.aut φ₀ hφ₀) r hr hrN (PositivityTheory.Affgl.CT.ct μ 𝓕 φ₀.1) ⟨μ, 𝓕, hμ, h𝓕, rfl⟩)
    exact ⟨p, hp, kl_all μ 𝓕 h𝓕 hV hφ₀ h0 hk⟩
  obtain ⟨p₁, hp₁, hk₁⟩ := hpoly 1
  obtain ⟨p₂, hp₂, hk₂⟩ := hpoly √2
  let f : ℂ → ℂ × ℂ := fun c => (Complex.exp (c * ((1 : ℝ) : ℂ)), Complex.exp (c * ((√2 : ℝ) : ℂ)))
  have hfin : ({z | p₁.IsRoot z} ×ˢ {z | p₂.IsRoot z} : Set (ℂ × ℂ)).Finite :=
    (Polynomial.finite_setOfPred_isRoot hp₁.ne_zero).prod (Polynomial.finite_setOfPred_isRoot hp₂.ne_zero)
  refine (hfin.preimage (f := f) fun c _ c' _ e =>
    exp_pair_inj (congrArg Prod.fst e) (congrArg Prod.snd e)).subset ?_
  rintro c ⟨φ, hφ, F₀, hCT, F, hFspan, hF0, hFe⟩
  obtain ⟨-, huniq⟩ := hDct φ (hV.aut φ hφ) r hr hrN
  obtain ⟨c₁, -, e₁⟩ := huniq F₀ hCT
  obtain ⟨c₂, hc₂, e₂⟩ := huniq _ ⟨μ, 𝓕, hμ, h𝓕, rfl⟩
  have eF₀ : F₀ = (c₁ / c₂) • PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 := by
    funext g
    rw [e₁, Pi.smul_apply, e₂, smul_eq_mul]
    field_simp
  have hk : ∀ s p, Kl r s p (PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1) → p.IsRoot (Complex.exp (c * s)) := by
    intro s p h
    refine kl_eigen (kl_span ?_ hFspan) hF0 hFe
    rw [eF₀]
    exact (klSub r s p).smul_mem _ h
  exact ⟨hk 1 p₁ (hk₁ φ hφ), hk √2 p₂ (hk₂ φ hφ)⟩

end PositivityTheory.Rg.Rs

end
