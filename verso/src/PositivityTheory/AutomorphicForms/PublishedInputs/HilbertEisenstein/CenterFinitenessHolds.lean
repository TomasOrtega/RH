import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SSmooth
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Qminor

open NumberField Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.TR Matrix

/- English proof (translation)
Establish `h : ∀ x, pInf F (sInf F x) = x` using `fun x => (infEq F).symm_apply_apply x`. Establish `h1 : pInf F (infId F u : Ideles F) = u`. Express the relevant statement in the definitionally equal form `pInf F (1 - sInf F 1 + sInf F _) = _`. Simplify using `[h]`. Establish `h2 : pFin F (infId F u : Ideles F) = 1`.

Express the relevant statement in the definitionally equal form `(1 : Af F) - 0 + 0 = 1`. Simplify using the standard rewrite rules. Use `ga_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[TR.pInf_infGL]`. Use extensionality with `i j`.

Apply the tactic sequence `by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h1]`. Rewrite using `[TR.pFin_infGL]`. Use extensionality with `i j`. Apply the tactic sequence `by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h2]`.
-/
private theorem infGL_scalar {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (u : (Rinf F)ˣ) :
    infGL F 2 (GeneralLinearGroup.scalar (Fin 2) u) = GeneralLinearGroup.scalar (Fin 2) (infId F u) := by
  have h : ∀ x, pInf F (sInf F x) = x := fun x => (infEq F).symm_apply_apply x
  have h1 : pInf F (infId F u : Ideles F) = u := by
    change pInf F (1 - sInf F 1 + sInf F _) = _
    simp [h]
  have h2 : pFin F (infId F u : Ideles F) = 1 := by
    change (1 : Af F) - 0 + 0 = 1
    simp
  refine ga_ext ?_ ?_
  · rw [TR.pInf_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h1]
  · rw [TR.pFin_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h2]

/- English proof (translation)
Take `⟨n, hn, e⟩` from `isOfFinOrder_iff_pow_eq_one.1 h`. Establish `e1 : expU z = expU ((n : ℝ)⁻¹ • z) ^ n`. Use `Units.ext (funext fun i => ?_)` and prove the remaining obligations. Establish `: (n : ℝ) ≠ 0` using `by positivity`. Simplify using `only [Units.val_pow_eq_pow_val, Pi.pow_apply, expU_val, ← Real.exp_nat_mul, Pi.smul_apply, smul_eq_mul]`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e1, map_pow, map_pow]`. Establish `e2 : ω.1 ^ n = 1` using `congrArg Subtype.val e`. Conclude with `DFunLike.congr_fun e2 _`.
-/
private theorem fin_expU {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {ω : HChar F} (h : IsOfFinOrder ω)
    (z : Rinf F) : ω.1 (infId F (expU z)) = 1 := by
  obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have e1 : expU z = expU ((n : ℝ)⁻¹ • z) ^ n := by
    refine Units.ext (funext fun i => ?_)
    have : (n : ℝ) ≠ 0 := by positivity
    simp only [Units.val_pow_eq_pow_val, Pi.pow_apply, expU_val, ← Real.exp_nat_mul, Pi.smul_apply, smul_eq_mul]
    congr 1
    field_simp
  rw [e1, map_pow, map_pow]
  have e2 : ω.1 ^ n = 1 := congrArg Subtype.val e
  exact DFunLike.congr_fun e2 _

/- English proof (translation)
Use `Subtype.ext (funext fun g => ?_)` and prove the remaining obligations. Establish `h1` using `hasDerivAt_curve φ g (fun t => GeneralLinearGroup.scalar (Fin 2) (expU (t • z))) (toL (Matrix.scalar (Fin 2) z)) (by simp [TR.expU_zero]) (by`. Use `hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_` and prove the remaining obligations. Distinguish the cases in `e : i = j`. Substitute `e` using the available equality.

Use `((hasDerivAt_id (0 : ℝ)).mul_const (z v)).exp` as an intermediate fact. Simplify using `using this`. Simplify `hasDerivAt_const (0 : ℝ) (0 : ℝ))` using `[Matrix.diagonal_apply, e]`. Establish `h2 : (fun t : ℝ => φ.1 (g * infGL F 2 (GeneralLinearGroup.scalar (Fin 2) (expU (t • z))))) = fun _ => φ.1 g`. Use function extensionality and compare the values at `t`.

Rewrite using `[infGL_scalar, ← GeneralLinearGroup.scalar_commute, hφ, fin_expU h]`. Simplify using the standard rewrite rules. Rewrite `h1` using `[h2]`. Conclude with `h1.unique (hasDerivAt_const _ _)`.
-/
private theorem lie_scalar {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {ω : HChar F} (h : IsOfFinOrder ω)
    {φ : Sm F 2} (hφ : ∀ (z : Ideles F) (g : GA F 2), φ.1 (GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g) (z : Rinf F) : lie F 2 (toL (Matrix.scalar (Fin 2) z)) φ = 0 := by
  refine Subtype.ext (funext fun g => ?_)
  have h1 := hasDerivAt_curve φ g (fun t => GeneralLinearGroup.scalar (Fin 2) (expU (t • z)))
    (toL (Matrix.scalar (Fin 2) z)) (by simp [TR.expU_zero]) (by
      refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_
      by_cases e : i = j
      · subst e
        have := ((hasDerivAt_id (0 : ℝ)).mul_const (z v)).exp
        simpa using this
      · simpa [Matrix.diagonal_apply, e] using hasDerivAt_const (0 : ℝ) (0 : ℝ))
  have h2 : (fun t : ℝ => φ.1 (g * infGL F 2 (GeneralLinearGroup.scalar (Fin 2) (expU (t • z))))) = fun _ => φ.1 g := by
    funext t
    rw [infGL_scalar, ← GeneralLinearGroup.scalar_commute, hφ, fin_expU h]
    simp
  rw [h2] at h1
  exact h1.unique (hasDerivAt_const _ _)

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qf10.casimir E hE k φ h0 h1 h2 u`.
-/
private theorem casimir {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin 2 → Fin 2 → Module.End ℂ V)
    (hE : Formalism.REAL.GlRel E) (k : ℂ) (φ : V) (h0 : E 0 0 φ + E 1 1 φ = 0)
    (h1 : E 0 1 φ - E 1 0 φ = (Complex.I * k) • φ) (h2 : E 0 0 φ - E 1 1 φ = Complex.I • (E 0 1 φ + E 1 0 φ)) (u : ℂ) :
    Formalism.REAL.qdet E (u + 1 / 2) φ = ((u + (k - 1) / 2) * (u - (k - 1) / 2)) • φ :=
  _root_.UpperTheory.Reformulated.B.Qf10.casimir E hE k φ h0 h1 h2 u

/- English proof (translation)
Introduce `_ _ _ F _ _ _ ω c hω φ hc hw hl`. Establish `hcap : ∀ v u, ∃ c : ℂ, TR.cap v u φ = c • φ` using `fun v u => by`. Establish `h0 : Eop v 0 0 φ + Eop v 1 1 φ = 0` using `by classical`. Rewrite using `[← lie_scalar hω hc (Pi.single v 1), TR.Eop, TR.Eop, ← LinearMap.add_apply, ← map_add]`. Use `congr 2`.

Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp`. Use `casimir _ (TR.glRel_Eop v) ((1 : ℕ) : ℂ) φ h0 (hw v) (hl v) u` as an intermediate fact. Use `⟨_, Eq.trans ?_ this⟩` and prove the remaining obligations. Rewrite using `[TR.cap]`.

Evaluate the numerical expressions. Use `Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {φ}) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Proceed by induction on `hz using Algebra.adjoin_induction with`. Consider the case `mem x hx`.

Take `⟨v, u, rfl⟩` from `hx`. Take `⟨c, e⟩` from `hcap v u`. Conclude with `Submodule.mem_span_singleton.2 ⟨c, e.symm⟩`. Consider the case `algebraMap c => exact Submodule.mem_span_singleton.2 ⟨c, rfl⟩`. Consider the case `add x y _ _ hx hy => exact add_mem hx hy`.

Consider the case `mul x y _ _ hx hy`. Take `⟨c, e⟩` from `Submodule.mem_span_singleton.1 hy`. Establish `e' : c • φ = y φ` using `e`. Express the relevant statement in the definitionally equal form `x (y φ) ∈ Submodule.span ℂ {φ}`. Rewrite using `[← e', map_smul]`.

Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem UpperTheory.HilbertEisensteinWeightOne.center_finiteness_holds : SPois → SInt → SSmooth → SZfin := by
  intro _ _ _ F _ _ _ ω c hω φ hc hw hl
  have hcap : ∀ v u, ∃ c : ℂ, TR.cap v u φ = c • φ := fun v u => by
    have h0 : Eop v 0 0 φ + Eop v 1 1 φ = 0 := by
      classical
      rw [← lie_scalar hω hc (Pi.single v 1), TR.Eop, TR.Eop, ← LinearMap.add_apply, ← map_add]
      congr 2
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have := casimir _ (TR.glRel_Eop v) ((1 : ℕ) : ℂ) φ h0 (hw v) (hl v) u
    refine ⟨_, Eq.trans ?_ this⟩
    rw [TR.cap]
    norm_num
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {φ}) (Submodule.span_le.2 ?_)
  rintro _ ⟨z, hz, rfl⟩
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨v, u, rfl⟩ := hx
    obtain ⟨c, e⟩ := hcap v u
    exact Submodule.mem_span_singleton.2 ⟨c, e.symm⟩
  | algebraMap c => exact Submodule.mem_span_singleton.2 ⟨c, rfl⟩
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy =>
    obtain ⟨c, e⟩ := Submodule.mem_span_singleton.1 hy
    have e' : c • φ = y φ := e
    change x (y φ) ∈ Submodule.span ℂ {φ}
    rw [← e', map_smul]
    exact Submodule.smul_mem _ _ hx
