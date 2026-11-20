import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.DescentOfLocalGlobalInputs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar
import GroundTheory.GlobalFields.IdeleGroups.NormOneCompact

set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace DiscreteGroups.T1.Desc

section Ideles

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Take `⟨D, hD, -, hxD⟩` from `GroundTheory.Global.IdeleGroup.exists_isCompact_normOneSubgroup E`. Establish `hcont : Continuous fun y : (AdeleRing (𝓞 E) E)ˣ => ‖((χ y : ℂˣ) : ℂ)‖` using `(Units.continuous_val.comp hc).norm`. Take `⟨M, hM⟩` from `hD.exists_bound_of_continuousOn hcont.continuousOn`. Establish `hb : ∀ y ∈ GroundTheory.Global.IdeleGroup.normOneSubgroup E, ‖((χ y : ℂˣ) : ℂ)‖ ≤ M`. Introduce `y hy`.

Take `⟨k, hk⟩` from `hxD y hy`. Establish `h` using `hM _ hk`. Establish `e : χ (GroundTheory.Global.IdeleGroup.diagonal E k * y) = χ y`. Rewrite using `[map_mul, show χ (GroundTheory.Global.IdeleGroup.diagonal E k) = 1 from hd k, one_mul]`. Rewrite `h` using `[e, Real.norm_of_nonneg (norm_nonneg _)]`.

Conclude with `h`. Establish `key : ∀ y ∈ GroundTheory.Global.IdeleGroup.normOneSubgroup E, ‖((χ y : ℂˣ) : ℂ)‖ ≤ 1`. Introduce `y hy`. Assume the negation of the conclusion as `h`. Use `replace h := not_le.1 h`.

Take `⟨n, hn⟩` from `pow_unbounded_of_one_lt M h`. Establish `h2` using `hb (y ^ n) (pow_mem hy n)`. Rewrite `h2` using `[map_pow, Units.val_pow_eq_pow_val, norm_pow]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `key x hx`.

Establish `h2` using `key x⁻¹ (inv_mem hx)`. Rewrite `h2` using `[map_inv, Units.val_inv_eq_inv_val, norm_inv]`. Establish `hpos : 0 < ‖((χ x : ℂˣ) : ℂ)‖` using `norm_pos_iff.2 (Units.ne_zero _)`. Establish `h3 : 1 ≤ ‖((χ x : ℂˣ) : ℂ)‖`. Assume the negation of the conclusion as `h`.

Use `replace h := not_le.1 h`. Establish `: 1 < ‖((χ x : ℂˣ) : ℂ)‖⁻¹` using `(one_lt_inv₀ hpos).2 h`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_eq_one_of_normOne (χ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (hc : Continuous χ)
    (hd : ∀ k : Eˣ, χ (Units.map (algebraMap E (AdeleRing (𝓞 E) E)).toMonoidHom k) = 1)
    {x : (AdeleRing (𝓞 E) E)ˣ} (hx : x ∈ GroundTheory.Global.IdeleGroup.normOneSubgroup E) :
    ‖((χ x : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨D, hD, -, hxD⟩ := GroundTheory.Global.IdeleGroup.exists_isCompact_normOneSubgroup E
  have hcont : Continuous fun y : (AdeleRing (𝓞 E) E)ˣ => ‖((χ y : ℂˣ) : ℂ)‖ :=
    (Units.continuous_val.comp hc).norm
  obtain ⟨M, hM⟩ := hD.exists_bound_of_continuousOn hcont.continuousOn
  have hb : ∀ y ∈ GroundTheory.Global.IdeleGroup.normOneSubgroup E, ‖((χ y : ℂˣ) : ℂ)‖ ≤ M := by
    intro y hy
    obtain ⟨k, hk⟩ := hxD y hy
    have h := hM _ hk
    have e : χ (GroundTheory.Global.IdeleGroup.diagonal E k * y) = χ y := by
      rw [map_mul, show χ (GroundTheory.Global.IdeleGroup.diagonal E k) = 1 from hd k, one_mul]
    rw [e, Real.norm_of_nonneg (norm_nonneg _)] at h
    exact h
  have key : ∀ y ∈ GroundTheory.Global.IdeleGroup.normOneSubgroup E, ‖((χ y : ℂˣ) : ℂ)‖ ≤ 1 := by
    intro y hy
    by_contra h
    replace h := not_le.1 h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M h
    have h2 := hb (y ^ n) (pow_mem hy n)
    rw [map_pow, Units.val_pow_eq_pow_val, norm_pow] at h2
    linarith
  have h1 := key x hx
  have h2 := key x⁻¹ (inv_mem hx)
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at h2
  have hpos : 0 < ‖((χ x : ℂˣ) : ℂ)‖ := norm_pos_iff.2 (Units.ne_zero _)
  have h3 : 1 ≤ ‖((χ x : ℂˣ) : ℂ)‖ := by
    by_contra h
    replace h := not_le.1 h
    have : 1 < ‖((χ x : ℂˣ) : ℂ)‖⁻¹ := (one_lt_inv₀ hpos).2 h
    linarith
  linarith

/- English proof (translation)
Take `⟨w⟩ : Nonempty (InfinitePlace E)` from `inferInstance`. Establish `hw : w.IsComplex` using `IsTotallyComplex.isComplex w`. Set `e` to `InfinitePlace.Completion.ringEquivComplexOfIsComplex hw`. Establish `hn : ∀ z : ℂ, ‖e.symm z‖ = ‖z‖` using `fun z => by`. Establish `h : ‖e.symm z‖ = ‖e (e.symm z)‖`.

Rewrite using `[InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply]`. Conclude with `((InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _).symm`. Rewrite using `[h, RingEquiv.apply_symm_apply]`. Establish `hec : Continuous e.symm` using `AddMonoidHomClass.continuous_of_bound e.symm 1 fun z => by rw [hn, one_mul]`. Establish `hex : ∀ t : ℝ, ((Real.exp t : ℝ) : ℂ) ≠ 0` using `fun t => Complex.ofReal_ne_zero.2 (Real.exp_pos t).ne'`.

Set `u : ℝ → ℂˣ` to `fun t => Units.mk0 _ (hex t)`. Establish `hu : Continuous u`. Use `Units.continuous_iff.2 ⟨Complex.continuous_ofReal.comp Real.continuous_exp, ?_⟩` and prove the remaining obligations. Conclude with `(Complex.continuous_ofReal.comp Real.continuous_exp).inv₀ hex`. Set `emb : ℝ → (AdeleRing (𝓞 E) E)ˣ` to `fun t => GroundTheory.Global.IdeleGroup.infiniteEmbedding w (Units.map e.symm.toMonoidHom (u t))`.

Establish `hemb : Continuous emb` using `(GroundTheory.Global.IdeleGroup.continuous_infiniteEmbedding w).comp ((Continuous.units_map e.symm.toMonoidHom hec).comp hu)`. Establish `hadd : ∀ s t, emb (s + t) = emb s * emb t` using `fun s t => by`. Establish `: u (s + t) = u s * u t` using `Units.ext (by simp only [u, Units.val_mk0, Units.val_mul, Real.exp_add, Complex.ofReal_mul])`. Simplify using `only [emb, this, map_mul]`. Establish `hmod : ∀ t, (GroundTheory.Global.IdeleGroup.ideleModule E (emb t) : ℝ) = Real.exp t ^ w.mult` using `fun t => by`.

Rewrite using `[GroundTheory.Global.IdeleGroup.ideleModule_infiniteEmbedding]`. Use `congr 1`. Rewrite using `[Units.coe_map]`. Express the relevant statement in the definitionally equal form `‖e.symm ((Real.exp t : ℝ) : ℂ)‖ = _`. Rewrite using `[hn, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos t).le]`.

Establish `hpos : ∀ y, 0 < ‖((χ y : ℂˣ) : ℂ)‖` using `fun y => norm_pos_iff.2 (Units.ne_zero _)`. Set `f : ℝ → ℝ` to `fun t => Real.log ‖((χ (emb t) : ℂˣ) : ℂ)‖`. Establish `fadd : ∀ s t, f (s + t) = f s + f t` using `fun s t => by`. Simplify using `only [f, hadd, map_mul, Units.val_mul, norm_mul]`. Conclude with `Real.log_mul (hpos _).ne' (hpos _).ne'`.

Establish `fcont : Continuous f` using `(((Units.continuous_val.comp hc).comp hemb).norm).log fun t => (hpos _).ne'`. Set `F : ℝ →+ ℝ` to `AddMonoidHom.mk' f fadd`. Establish `hlin : ∀ t, f t = t * f 1` using `fun t => by`. Establish `h` using `(F.toRealLinearMap fcont).map_smul t 1`. Simplify using `only [smul_eq_mul, mul_one] at h`.

Conclude with `h`. Establish `hm : (w.mult : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 InfinitePlace.mult_pos.ne'`. Establish `hrep : ∀ y, ‖((χ y : ℂˣ) : ℂ)‖ = Real.exp (Real.log (GroundTheory.Global.IdeleGroup.ideleModule E y : ℝ) / w.mult * f 1)` using `fun y => by set t := Real.log (GroundTheory.Global.IdeleGroup.ideleModule E y : ℝ) / w.mult with ht`. Establish `heq : GroundTheory.Global.IdeleGroup.ideleModule E (emb t) = GroundTheory.Global.IdeleGroup.ideleModule E y`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[hmod, ← Real.exp_nat_mul, ht, mul_div_cancel₀ _ hm, Real.exp_log (GroundTheory.Global.IdeleGroup.ideleModule E y).2]`. Establish `hmem : y * (emb t)⁻¹ ∈ GroundTheory.Global.IdeleGroup.normOneSubgroup E`. Rewrite using `[GroundTheory.Global.IdeleGroup.mem_normOneSubgroup, map_mul, map_inv, heq, mul_inv_cancel]`. Both sides reduce to the same expression. Establish `h` using `norm_eq_one_of_normOne χ hc hd hmem`.

Rewrite `h` using `[map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv]`. Establish `h' : ‖((χ y : ℂˣ) : ℂ)‖ = ‖((χ (emb t) : ℂˣ) : ℂ)‖` using `(mul_inv_eq_one₀ (hpos _).ne').1 h`. Rewrite using `[← hlin, h']`. Conclude with `(Real.exp_log (hpos _)).symm`. Establish `hf1 : f 1 = 0`.

Establish `h` using `hrep x₀`. Rewrite `h` using `[h0]`. Establish `h' : Real.log (GroundTheory.Global.IdeleGroup.ideleModule E x₀ : ℝ) / w.mult * f 1 = 0` using `Real.exp_eq_one_iff _ |>.1 h.symm`. Establish `hl : Real.log (GroundTheory.Global.IdeleGroup.ideleModule E x₀ : ℝ) ≠ 0` using `Real.log_ne_zero_of_pos_of_ne_one (GroundTheory.Global.IdeleGroup.ideleModule E x₀).2 h1`. Conclude with `(mul_eq_zero.1 h').resolve_left (div_ne_zero hl hm)`.

Rewrite using `[hrep x, hf1, mul_zero, Real.exp_zero]`.
-/
theorem norm_eq_one_of_module [IsTotallyComplex E] (χ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (hc : Continuous χ)
    (hd : ∀ k : Eˣ, χ (Units.map (algebraMap E (AdeleRing (𝓞 E) E)).toMonoidHom k) = 1)
    (x₀ : (AdeleRing (𝓞 E) E)ˣ) (h0 : ‖((χ x₀ : ℂˣ) : ℂ)‖ = 1)
    (h1 : (GroundTheory.Global.IdeleGroup.ideleModule E x₀ : ℝ) ≠ 1) (x : (AdeleRing (𝓞 E) E)ˣ) :
    ‖((χ x : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hw : w.IsComplex := IsTotallyComplex.isComplex w
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
  have hn : ∀ z : ℂ, ‖e.symm z‖ = ‖z‖ := fun z => by
    have h : ‖e.symm z‖ = ‖e (e.symm z)‖ := by
      rw [InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply]
      exact ((InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
        (map_zero _) _).symm
    rw [h, RingEquiv.apply_symm_apply]
  have hec : Continuous e.symm :=
    AddMonoidHomClass.continuous_of_bound e.symm 1 fun z => by rw [hn, one_mul]
  have hex : ∀ t : ℝ, ((Real.exp t : ℝ) : ℂ) ≠ 0 := fun t => Complex.ofReal_ne_zero.2 (Real.exp_pos t).ne'
  let u : ℝ → ℂˣ := fun t => Units.mk0 _ (hex t)
  have hu : Continuous u := by
    refine Units.continuous_iff.2 ⟨Complex.continuous_ofReal.comp Real.continuous_exp, ?_⟩
    exact (Complex.continuous_ofReal.comp Real.continuous_exp).inv₀ hex
  let emb : ℝ → (AdeleRing (𝓞 E) E)ˣ := fun t =>
    GroundTheory.Global.IdeleGroup.infiniteEmbedding w (Units.map e.symm.toMonoidHom (u t))
  have hemb : Continuous emb :=
    (GroundTheory.Global.IdeleGroup.continuous_infiniteEmbedding w).comp
      ((Continuous.units_map e.symm.toMonoidHom hec).comp hu)
  have hadd : ∀ s t, emb (s + t) = emb s * emb t := fun s t => by
    have : u (s + t) = u s * u t := Units.ext (by simp only [u, Units.val_mk0, Units.val_mul, Real.exp_add, Complex.ofReal_mul])
    simp only [emb, this, map_mul]
  have hmod : ∀ t, (GroundTheory.Global.IdeleGroup.ideleModule E (emb t) : ℝ) = Real.exp t ^ w.mult := fun t => by
    rw [GroundTheory.Global.IdeleGroup.ideleModule_infiniteEmbedding]
    congr 1
    rw [Units.coe_map]
    change ‖e.symm ((Real.exp t : ℝ) : ℂ)‖ = _
    rw [hn, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos t).le]
  have hpos : ∀ y, 0 < ‖((χ y : ℂˣ) : ℂ)‖ := fun y => norm_pos_iff.2 (Units.ne_zero _)
  let f : ℝ → ℝ := fun t => Real.log ‖((χ (emb t) : ℂˣ) : ℂ)‖
  have fadd : ∀ s t, f (s + t) = f s + f t := fun s t => by
    simp only [f, hadd, map_mul, Units.val_mul, norm_mul]
    exact Real.log_mul (hpos _).ne' (hpos _).ne'
  have fcont : Continuous f :=
    (((Units.continuous_val.comp hc).comp hemb).norm).log fun t => (hpos _).ne'
  let F : ℝ →+ ℝ := AddMonoidHom.mk' f fadd
  have hlin : ∀ t, f t = t * f 1 := fun t => by
    have h := (F.toRealLinearMap fcont).map_smul t 1
    simp only [smul_eq_mul, mul_one] at h
    exact h
  have hm : (w.mult : ℝ) ≠ 0 := Nat.cast_ne_zero.2 InfinitePlace.mult_pos.ne'
  have hrep : ∀ y, ‖((χ y : ℂˣ) : ℂ)‖ =
      Real.exp (Real.log (GroundTheory.Global.IdeleGroup.ideleModule E y : ℝ) / w.mult * f 1) := fun y => by
    set t := Real.log (GroundTheory.Global.IdeleGroup.ideleModule E y : ℝ) / w.mult with ht
    have heq : GroundTheory.Global.IdeleGroup.ideleModule E (emb t) = GroundTheory.Global.IdeleGroup.ideleModule E y := by
      apply Subtype.ext
      rw [hmod, ← Real.exp_nat_mul, ht, mul_div_cancel₀ _ hm,
        Real.exp_log (GroundTheory.Global.IdeleGroup.ideleModule E y).2]
    have hmem : y * (emb t)⁻¹ ∈ GroundTheory.Global.IdeleGroup.normOneSubgroup E := by
      rw [GroundTheory.Global.IdeleGroup.mem_normOneSubgroup, map_mul, map_inv, heq, mul_inv_cancel]
      rfl
    have h := norm_eq_one_of_normOne χ hc hd hmem
    rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv] at h
    have h' : ‖((χ y : ℂˣ) : ℂ)‖ = ‖((χ (emb t) : ℂˣ) : ℂ)‖ := (mul_inv_eq_one₀ (hpos _).ne').1 h
    rw [← hlin, h']
    exact (Real.exp_log (hpos _)).symm
  have hf1 : f 1 = 0 := by
    have h := hrep x₀
    rw [h0] at h
    have h' : Real.log (GroundTheory.Global.IdeleGroup.ideleModule E x₀ : ℝ) / w.mult * f 1 = 0 :=
      Real.exp_eq_one_iff _ |>.1 h.symm
    have hl : Real.log (GroundTheory.Global.IdeleGroup.ideleModule E x₀ : ℝ) ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (GroundTheory.Global.IdeleGroup.ideleModule E x₀).2 h1
    exact (mul_eq_zero.1 h').resolve_left (div_ne_zero hl hm)
  rw [hrep x, hf1, mul_zero, Real.exp_zero]

/- English proof (translation)
Use `set d := GroundTheory.Global.IdeleGroup.diagonal E (Units.mk0 (2 : E) two_ne_zero) with hdd`. Establish `hd2 : (d : AdeleRing (𝓞 E) E).2 = 2`. Rewrite using `[hdd]`. Express the relevant statement in the definitionally equal form `(algebraMap E (AdeleRing (𝓞 E) E) (2 : E)).2 = 2`. Rewrite using `[map_ofNat]`.

Both sides reduce to the same expression. Establish `hfin : GroundTheory.Global.IdeleGroup.finiteModule x = GroundTheory.Global.IdeleGroup.finiteModule d`. Unfold `GroundTheory.Global.IdeleGroup.finiteModule`. Rewrite using `[h2, hd2]`. Establish `hinf : GroundTheory.Global.IdeleGroup.infiniteModule x = 1`.

Unfold `GroundTheory.Global.IdeleGroup.infiniteModule`. Rewrite using `[h1]`. Conclude with `Finset.prod_eq_one fun w _ => (by rw [norm_one, one_pow] : ‖(1 : w.Completion)‖ ^ w.mult = 1)`. Establish `hd1 : GroundTheory.Global.IdeleGroup.infiniteModule d * GroundTheory.Global.IdeleGroup.finiteModule d = 1`. Rewrite using `[← GroundTheory.Global.IdeleGroup.ideleModule_apply, GroundTheory.Global.IdeleGroup.ideleModule_diagonal]`.

Both sides reduce to the same expression. Establish `hdi : 1 < GroundTheory.Global.IdeleGroup.infiniteModule d`. Rewrite using `[hdd, GroundTheory.Global.IdeleGroup.infiniteModule_diagonal]`. Establish `h2w : ∀ w : InfinitePlace E, w ((Units.mk0 (2 : E) two_ne_zero : Eˣ) : E) = 2` using `fun w => by`. Rewrite using `[Units.val_mk0, ← InfinitePlace.norm_embedding_eq, map_ofNat]`.

Simplify using the standard rewrite rules. Simplify using `only [h2w]`. Rewrite using `[Finset.prod_pow_eq_pow_sum]`. Conclude with `one_lt_pow₀ (by norm_num) (Finset.sum_pos (fun w _ => InfinitePlace.mult_pos) Finset.univ_nonempty).ne'`. Rewrite using `[GroundTheory.Global.IdeleGroup.ideleModule_apply, hinf, one_mul, hfin]`.

Introduce `h`. Rewrite `hd1` using `[h, mul_one]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem module_ne_one_of_two (x : (AdeleRing (𝓞 E) E)ˣ) (h1 : (x : AdeleRing (𝓞 E) E).1 = 1)
    (h2 : (x : AdeleRing (𝓞 E) E).2 = 2) : (GroundTheory.Global.IdeleGroup.ideleModule E x : ℝ) ≠ 1 := by
  classical
  set d := GroundTheory.Global.IdeleGroup.diagonal E (Units.mk0 (2 : E) two_ne_zero) with hdd
  have hd2 : (d : AdeleRing (𝓞 E) E).2 = 2 := by
    rw [hdd]
    change (algebraMap E (AdeleRing (𝓞 E) E) (2 : E)).2 = 2
    rw [map_ofNat]
    rfl
  have hfin : GroundTheory.Global.IdeleGroup.finiteModule x = GroundTheory.Global.IdeleGroup.finiteModule d := by
    unfold GroundTheory.Global.IdeleGroup.finiteModule
    rw [h2, hd2]
  have hinf : GroundTheory.Global.IdeleGroup.infiniteModule x = 1 := by
    unfold GroundTheory.Global.IdeleGroup.infiniteModule
    rw [h1]
    exact Finset.prod_eq_one fun w _ => (by rw [norm_one, one_pow] : ‖(1 : w.Completion)‖ ^ w.mult = 1)
  have hd1 : GroundTheory.Global.IdeleGroup.infiniteModule d * GroundTheory.Global.IdeleGroup.finiteModule d = 1 := by
    rw [← GroundTheory.Global.IdeleGroup.ideleModule_apply, GroundTheory.Global.IdeleGroup.ideleModule_diagonal]
    rfl
  have hdi : 1 < GroundTheory.Global.IdeleGroup.infiniteModule d := by
    rw [hdd, GroundTheory.Global.IdeleGroup.infiniteModule_diagonal]
    have h2w : ∀ w : InfinitePlace E, w ((Units.mk0 (2 : E) two_ne_zero : Eˣ) : E) = 2 := fun w => by
      rw [Units.val_mk0, ← InfinitePlace.norm_embedding_eq, map_ofNat]
      simp
    simp only [h2w]
    rw [Finset.prod_pow_eq_pow_sum]
    exact one_lt_pow₀ (by norm_num)
      (Finset.sum_pos (fun w _ => InfinitePlace.mult_pos) Finset.univ_nonempty).ne'
  rw [GroundTheory.Global.IdeleGroup.ideleModule_apply, hinf, one_mul, hfin]
  intro h
  rw [h, mul_one] at hd1
  linarith

end Ideles

/- English proof (translation)
Introduce `E _ _ _ n hn π hd`. Take `⟨ω, hω⟩` from `GlobalTheory.CuspRep.Central.exists_hasCentChar (CG.mk π)`. Use `⟨ω, ?_, hω⟩` and prove the remaining obligations. Set `u : (FiniteAdeleRing (𝓞 E) E)ˣ` to `Units.map (algebraMap E (FiniteAdeleRing (𝓞 E) E)).toMonoidHom (Units.mk0 (2 : E) two_ne_zero)`. Establish `hu : (u : FiniteAdeleRing (𝓞 E) E) = 2`.

Express the relevant statement in the definitionally equal form `algebraMap E (FiniteAdeleRing (𝓞 E) E) (2 : E) = 2`. Conclude with `map_ofNat _ 2`. Establish `hc : ((ω.1 (finId E u) : ℂˣ) : ℂ) * ((ω.1 (finId E u) : ℂˣ) : ℂ) = 1`. Take `⟨B, hB1, -, hfin, -, -⟩` from `hd`. Establish `hs : GeneralLinearGroup.map (conjFin (IsCMField.complexConj E).toRingEquiv) (GeneralLinearGroup.scalar (Fin n) u) = GeneralLinearGroup.scalar (Fin n) u`.

Establish `hcu : conjFin (IsCMField.complexConj E).toRingEquiv (u : FiniteAdeleRing (𝓞 E) E) = u`. Rewrite using `[hu]`. Conclude with `map_ofNat _ 2`. Use `Matrix.GeneralLinearGroup.ext fun i j => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases hij : i = j <;>`.

Simplify using `[GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply, hij, hcu]`. Use `Submodule.nontrivial_iff_ne_bot.2 π.ne_bot` as an intermediate fact. Take `⟨φ, hφ⟩` from `exists_ne (0 : π.V)`. Choose the witnesses or unpack the hypotheses as in `⟨ψ, hψ⟩ : ∃ ψ, B φ ψ ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Conclude with `hφ (hB1 φ fun ψ => not_not.1 fun h' => h ⟨ψ, h'⟩)`. Establish `h` using `hfin (GeneralLinearGroup.scalar (Fin n) u) φ ψ`. Establish `e1 : π.op (.fin (GeneralLinearGroup.scalar (Fin n) u)) φ = ((ω.1 (finId E u) : ℂˣ) : ℂ) • φ` using `hω u φ`. Establish `e2 : π.op (GlobalTheory.ContraPair.conjOp (.fin (GeneralLinearGroup.scalar (Fin n) u))) ψ = ((ω.1 (finId E u) : ℂˣ) : ℂ) • ψ`. Express the relevant statement in the definitionally equal form `π.op (.fin (GeneralLinearGroup.map (conjFin (IsCMField.complexConj E).toRingEquiv) (GeneralLinearGroup.scalar (Fin n) u))) ψ = _`.

Rewrite using `[hs]`. Conclude with `hω u ψ`. Rewrite `h` using `[e1, e2]`. Simplify using `only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h`. Establish `h' : (((ω.1 (finId E u) : ℂˣ) : ℂ) * ((ω.1 (finId E u) : ℂˣ) : ℂ) - 1) * B φ ψ = 0`.

Take the linear combination `h`. Use `(mul_eq_zero.1 h').resolve_right hψ` as an intermediate fact. Take the linear combination `this`. Establish `hfx : ((finId E u : (AdeleRing (𝓞 E) E)ˣ) : AdeleRing (𝓞 E) E) = ((1 : InfiniteAdeleRing E), (u : FiniteAdeleRing (𝓞 E) E))`. Simplify using `only [finId, corner, sFin, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk]`.

Use `Prod.ext ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(1 : InfiniteAdeleRing E) - 0 + 0 = 1`. Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `(1 : FiniteAdeleRing (𝓞 E) E) - 1 + (u : FiniteAdeleRing (𝓞 E) E) = u`. Simplify using the standard rewrite rules.

Introduce `x`. Use `norm_eq_one_of_module ω.1 ω.2.1 ω.2.2 (finId E u) ?_ ?_ x` and prove the remaining obligations. Establish `h2 : ‖((ω.1 (finId E u) : ℂˣ) : ℂ)‖ ^ 2 = 1` using `by rw [sq, ← norm_mul, hc, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2`. Conclude with `module_ne_one_of_two _ (by rw [hfx]) (by rw [hfx, hu])`.
-/
theorem unitOf : PositivityTheory.Rg.BcB.Desc.UnitOf := by
  intro E _ _ _ n hn π hd
  obtain ⟨ω, hω⟩ := GlobalTheory.CuspRep.Central.exists_hasCentChar (CG.mk π)
  refine ⟨ω, ?_, hω⟩
  let u : (FiniteAdeleRing (𝓞 E) E)ˣ :=
    Units.map (algebraMap E (FiniteAdeleRing (𝓞 E) E)).toMonoidHom (Units.mk0 (2 : E) two_ne_zero)
  have hu : (u : FiniteAdeleRing (𝓞 E) E) = 2 := by
    change algebraMap E (FiniteAdeleRing (𝓞 E) E) (2 : E) = 2
    exact map_ofNat _ 2
  have hc : ((ω.1 (finId E u) : ℂˣ) : ℂ) * ((ω.1 (finId E u) : ℂˣ) : ℂ) = 1 := by
    obtain ⟨B, hB1, -, hfin, -, -⟩ := hd
    have hs : GeneralLinearGroup.map (conjFin (IsCMField.complexConj E).toRingEquiv)
        (GeneralLinearGroup.scalar (Fin n) u) = GeneralLinearGroup.scalar (Fin n) u := by
      have hcu : conjFin (IsCMField.complexConj E).toRingEquiv (u : FiniteAdeleRing (𝓞 E) E) = u := by
        rw [hu]
        exact map_ofNat _ 2
      refine Matrix.GeneralLinearGroup.ext fun i j => ?_
      by_cases hij : i = j <;>
        simp [GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply, hij, hcu]
    have := Submodule.nontrivial_iff_ne_bot.2 π.ne_bot
    obtain ⟨φ, hφ⟩ := exists_ne (0 : π.V)
    obtain ⟨ψ, hψ⟩ : ∃ ψ, B φ ψ ≠ 0 := by
      by_contra h
      exact hφ (hB1 φ fun ψ => not_not.1 fun h' => h ⟨ψ, h'⟩)
    have h := hfin (GeneralLinearGroup.scalar (Fin n) u) φ ψ
    have e1 : π.op (.fin (GeneralLinearGroup.scalar (Fin n) u)) φ = ((ω.1 (finId E u) : ℂˣ) : ℂ) • φ := hω u φ
    have e2 : π.op (GlobalTheory.ContraPair.conjOp (.fin (GeneralLinearGroup.scalar (Fin n) u))) ψ =
        ((ω.1 (finId E u) : ℂˣ) : ℂ) • ψ := by
      change π.op (.fin (GeneralLinearGroup.map (conjFin (IsCMField.complexConj E).toRingEquiv)
        (GeneralLinearGroup.scalar (Fin n) u))) ψ = _
      rw [hs]
      exact hω u ψ
    rw [e1, e2] at h
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    have h' : (((ω.1 (finId E u) : ℂˣ) : ℂ) * ((ω.1 (finId E u) : ℂˣ) : ℂ) - 1) * B φ ψ = 0 := by
      linear_combination h
    have := (mul_eq_zero.1 h').resolve_right hψ
    linear_combination this
  have hfx : ((finId E u : (AdeleRing (𝓞 E) E)ˣ) : AdeleRing (𝓞 E) E) =
      ((1 : InfiniteAdeleRing E), (u : FiniteAdeleRing (𝓞 E) E)) := by
    simp only [finId, corner, sFin, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk]
    refine Prod.ext ?_ ?_
    · change (1 : InfiniteAdeleRing E) - 0 + 0 = 1
      simp
    · change (1 : FiniteAdeleRing (𝓞 E) E) - 1 + (u : FiniteAdeleRing (𝓞 E) E) = u
      simp
  intro x
  refine norm_eq_one_of_module ω.1 ω.2.1 ω.2.2 (finId E u) ?_ ?_ x
  · have h2 : ‖((ω.1 (finId E u) : ℂˣ) : ℂ)‖ ^ 2 = 1 := by rw [sq, ← norm_mul, hc, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2
  · exact module_ne_one_of_two _ (by rw [hfx]) (by rw [hfx, hu])

end DiscreteGroups.T1.Desc

end
