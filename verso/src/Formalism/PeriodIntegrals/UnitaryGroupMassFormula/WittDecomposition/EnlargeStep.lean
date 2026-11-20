import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittDecomposition.Imports

namespace PI.Witt

variable {K V : Type} [Field K] [StarRing K] [CharZero K] [AddCommGroup V] [Module K V]

/- English proof (translation)
Simplify using `only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, map_smul, smul_eq_mul, starRingEnd_apply, RingHom.id_apply]`. Generalize the expression as in `B u u' = A1`. Generalize the expression as in `B u p = A2`. Generalize the expression as in `B p u' = A3`. Generalize the expression as in `B p p = A4`.

Generalize the expression as in `star c = s`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem expand (B : V →ₗ⋆[K] V →ₗ[K] K) (p u u' : V) (c c' : K) :
    B (u + c • p) (u' + c' • p) =
      B u u' + c' * B u p + star c * B p u' + star c * c' * B p p := by
  simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
    starRingEnd_apply, RingHom.id_apply]
  generalize B u u' = A1
  generalize B u p = A2
  generalize B p u' = A3
  generalize B p p = A4
  generalize star c = s
  ring

/- English proof (translation)
Use `set a := B p0 p0 with ha_def`. Establish `ha : star a = a` using `hB p0 p0`. Establish `hr1 : B r p0 = 1` using `by rw [← hB p0 r, h1, star_one]`. Establish `hc : star (-(a / 2)) = -(a / 2)`. Rewrite using `[star_neg, star_div₀, ha, star_ofNat]`.

Use `⟨p0 + (-(a / 2)) • r, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[expand B r p0 p0 (-(a / 2)) (-(a / 2)), h1, hr1, hrr, hc]`. Expand and normalize the polynomial expressions, which then agree. Introduce `u hu`. Simplify using `[hu]`.
-/
theorem partner (B : V →ₗ⋆[K] V →ₗ[K] K) (hB : ∀ x y, star (B x y) = B y x) (r p0 : V)
    (hrr : B r r = 0) (h1 : B p0 r = 1) :
    ∃ p, B p p = 0 ∧ ∀ u, B r u = 0 → B p u = B p0 u := by
  set a := B p0 p0 with ha_def
  have ha : star a = a := hB p0 p0
  have hr1 : B r p0 = 1 := by rw [← hB p0 r, h1, star_one]
  have hc : star (-(a / 2)) = -(a / 2) := by
    rw [star_neg, star_div₀, ha, star_ofNat]
  refine ⟨p0 + (-(a / 2)) • r, ?_, ?_⟩
  · rw [expand B r p0 p0 (-(a / 2)) (-(a / 2)), h1, hr1, hrr, hc]
    ring
  · intro u hu
    simp [hu]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨φ0, hφ0⟩ : ∃ φ : Module.Dual K V, φ r ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hr0 ((Module.forall_dual_apply_eq_zero_iff K r).1 h)`. Use `set φ : V →ₗ[K] K := (φ0 r)⁻¹ • φ0 with hφdef`.

Establish `hφr : φ r = 1` using `by simp [hφdef, hφ0]`. Take `⟨p0, hp0⟩` from `riesz B hB hnd φ`. Take `⟨p, hpp, hpU'⟩` from `partner B hB r p0 (hr r hrU) (by rw [hp0, hφr])`. Establish `hpU : ∀ u ∈ U, B p u = φ u` using `fun u hu => by rw [hpU' u (hr u hu), hp0]`. Use `set e := LinearEquiv.ofInjective f hinj with he`.

Take `⟨χ, hχ⟩` from `LinearMap.exists_extend ((φ.comp U.subtype).comp e.symm.toLinearMap)`. Establish `hχf : ∀ u : U, χ (f u) = φ u` using `fun u => by`. Use `LinearMap.congr_fun hχ (e u)` as an intermediate fact. Simplify `this` using `[he]`. Take `⟨q0, hq0⟩` from `riesz B hB hnd χ`.

Use `set r' : U := ⟨r, hrU⟩ with hr'`. Establish `hφr' : φ (r' : V) = 1` using `hφr`. Establish `hfr : ∀ u : U, B (f r') (f u) = 0` using `fun u => by rw [hf]; exact hr u u.2`. Take `⟨q, hqq, hqU'⟩` from `partner B hB (f r') q0 (hfr r') (by rw [hq0, hχf]; exact hφr')`. Establish `hqU : ∀ u : U, B q (f u) = φ u` using `fun u => by rw [hqU' _ (hfr u), hq0, hχf]`.

Use `set Φ : (U × K) →ₗ[K] V := U.subtype.coprod (LinearMap.toSpanSingleton K V p) with hΦdef`. Use `set Ψ : (U × K) →ₗ[K] V := f.coprod (LinearMap.toSpanSingleton K V q) with hΨdef`. Establish `hΦ : ∀ a : U × K, Φ a = (a.1 : V) + a.2 • p` using `fun a => by simp [hΦdef]`. Establish `hΨ : ∀ a : U × K, Ψ a = f a.1 + a.2 • q` using `fun a => by simp [hΨdef]`. Establish `hpnot : p ∉ U`.

Introduce `hp`. Establish `h1 : B r p = 0` using `hr p hp`. Establish `h2 : B p r = 1` using `by rw [hpU r hrU, hφr]`. Establish `h3` using `hB p r`. Rewrite `h3` using `[h2, h1, star_one]`.

Conclude with `one_ne_zero h3`. Establish `hΦinj : Function.Injective Φ`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce and unpack `⟨u, c⟩ h`. Rewrite `h` using `[hΦ]`.

Establish `hc : c = 0`. Assume the negation of the conclusion as `hc`. Apply `hpnot` to reduce the goal to its premises. Establish `h' : c • p = -(u : V)`. Rewrite using `[← sub_eq_zero, sub_neg_eq_add, add_comm]`.

Conclude with `h`. Establish `: p = c⁻¹ • -(u : V)` using `by rw [← h', smul_smul, inv_mul_cancel₀ hc, one_smul]`. Rewrite using `[this]`. Conclude with `U.smul_mem _ (U.neg_mem u.2)`. Substitute `hc` using the available equality.

Use `Prod.ext ?_ rfl` and prove the remaining obligations. Use `ext`. Simplify using `using h`. Establish `hΨinj : Function.Injective Ψ`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`.

Introduce and unpack `⟨u, c⟩ h`. Rewrite `h` using `[hΨ]`. Establish `hc : c = 0`. Establish `h4` using `congrArg (B (f r')) h`. Rewrite `h4` using `[map_add, map_smul, hfr u, ← hB q (f r'), hqU r', hφr', map_zero]`.

Simplify using `using h4`. Substitute `hc` using the available equality. Establish `hu : f u = 0` using `by simpa using h`. Establish `hu0 : u = 0` using `hinj (by rw [hu, map_zero])`. Substitute `hu0` using the available equality.

Both sides reduce to the same expression. Establish `hlt : U < LinearMap.range Φ`. Rewrite using `[SetLike.lt_iff_le_and_exists]`. Use `⟨fun u hu => ⟨(⟨u, hu⟩, 0), by simp [hΦ]⟩, p, ⟨(0, 1), by simp [hΦ]⟩, hpnot⟩` and prove the remaining obligations. Use `set eΦ := LinearEquiv.ofInjective Φ hΦinj with heΦ`.

Establish `hval : ∀ x : LinearMap.range Φ, (x : V) = Φ (eΦ.symm x)` using `fun x => (congrArg Subtype.val (eΦ.apply_symm_apply x)).symm.trans (LinearEquiv.ofInjective_apply _ _)`. Use `⟨LinearMap.range Φ, hlt, Ψ.comp eΦ.symm.toLinearMap, hΨinj.comp eΦ.symm.injective, ?_, ?_⟩` and prove the remaining obligations. Introduce `x y`. Rewrite using `[hval x, hval y]`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe]`.

Generalize the expression as in `eΦ.symm x = a`. Generalize the expression as in `eΦ.symm y = b`. Take `⟨u, c⟩` from `a`. Take `⟨u', c'⟩` from `b`. Rewrite using `[hΨ, hΨ, hΦ, hΦ]`.

Simplify using `only`. Rewrite using `[expand B q (f u) (f u') c c', expand B p (u : V) (u' : V) c c', hf, hqq, hpp, ← hB q (f u), ← hB p (u : V), hqU u, hqU u', hpU _ u.2, hpU _ u'.2]`. Introduce `u`. Establish `h5 : eΦ.symm ⟨u, hlt.le u.2⟩ = (u, 0)`. Rewrite using `[LinearEquiv.symm_apply_eq]`.

Use `ext`. Rewrite using `[LinearEquiv.ofInjective_apply, hΦ]`. Simplify using the standard rewrite rules. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, h5, hΨ, zero_smul, add_zero]`.
-/
theorem enlarge_step [FiniteDimensional K V] (B : V →ₗ⋆[K] V →ₗ[K] K)
    (hB : ∀ x y, star (B x y) = B y x) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (U : Submodule K V) (f : U →ₗ[K] V) (hinj : Function.Injective f)
    (hf : ∀ x y : U, B (f x) (f y) = B x y)
    (r : V) (hrU : r ∈ U) (hr0 : r ≠ 0) (hr : ∀ u ∈ U, B r u = 0) :
    ∃ (U' : Submodule K V) (hlt : U < U') (f' : U' →ₗ[K] V), Function.Injective f' ∧
      (∀ x y : U', B (f' x) (f' y) = B x y) ∧ ∀ u : U, f' ⟨u, hlt.le u.2⟩ = f u := by
  classical

  obtain ⟨φ0, hφ0⟩ : ∃ φ : Module.Dual K V, φ r ≠ 0 := by
    by_contra h
    push_neg at h
    exact hr0 ((Module.forall_dual_apply_eq_zero_iff K r).1 h)
  set φ : V →ₗ[K] K := (φ0 r)⁻¹ • φ0 with hφdef
  have hφr : φ r = 1 := by simp [hφdef, hφ0]
  obtain ⟨p0, hp0⟩ := riesz B hB hnd φ
  obtain ⟨p, hpp, hpU'⟩ := partner B hB r p0 (hr r hrU) (by rw [hp0, hφr])
  have hpU : ∀ u ∈ U, B p u = φ u := fun u hu => by rw [hpU' u (hr u hu), hp0]

  set e := LinearEquiv.ofInjective f hinj with he
  obtain ⟨χ, hχ⟩ := LinearMap.exists_extend ((φ.comp U.subtype).comp e.symm.toLinearMap)
  have hχf : ∀ u : U, χ (f u) = φ u := fun u => by
    have := LinearMap.congr_fun hχ (e u)
    simpa [he] using this
  obtain ⟨q0, hq0⟩ := riesz B hB hnd χ
  set r' : U := ⟨r, hrU⟩ with hr'
  have hφr' : φ (r' : V) = 1 := hφr
  have hfr : ∀ u : U, B (f r') (f u) = 0 := fun u => by rw [hf]; exact hr u u.2
  obtain ⟨q, hqq, hqU'⟩ := partner B hB (f r') q0 (hfr r') (by rw [hq0, hχf]; exact hφr')
  have hqU : ∀ u : U, B q (f u) = φ u := fun u => by rw [hqU' _ (hfr u), hq0, hχf]

  set Φ : (U × K) →ₗ[K] V := U.subtype.coprod (LinearMap.toSpanSingleton K V p) with hΦdef
  set Ψ : (U × K) →ₗ[K] V := f.coprod (LinearMap.toSpanSingleton K V q) with hΨdef
  have hΦ : ∀ a : U × K, Φ a = (a.1 : V) + a.2 • p := fun a => by simp [hΦdef]
  have hΨ : ∀ a : U × K, Ψ a = f a.1 + a.2 • q := fun a => by simp [hΨdef]
  have hpnot : p ∉ U := by
    intro hp
    have h1 : B r p = 0 := hr p hp
    have h2 : B p r = 1 := by rw [hpU r hrU, hφr]
    have h3 := hB p r
    rw [h2, h1, star_one] at h3
    exact one_ne_zero h3
  have hΦinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨u, c⟩ h
    rw [hΦ] at h
    have hc : c = 0 := by
      by_contra hc
      apply hpnot
      have h' : c • p = -(u : V) := by
        rw [← sub_eq_zero, sub_neg_eq_add, add_comm]; exact h
      have : p = c⁻¹ • -(u : V) := by rw [← h', smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [this]
      exact U.smul_mem _ (U.neg_mem u.2)
    subst hc
    refine Prod.ext ?_ rfl
    ext
    simpa using h
  have hΨinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨u, c⟩ h
    rw [hΨ] at h
    have hc : c = 0 := by
      have h4 := congrArg (B (f r')) h
      rw [map_add, map_smul, hfr u, ← hB q (f r'), hqU r', hφr', map_zero] at h4
      simpa using h4
    subst hc
    have hu : f u = 0 := by simpa using h
    have hu0 : u = 0 := hinj (by rw [hu, map_zero])
    subst hu0
    rfl
  have hlt : U < LinearMap.range Φ := by
    rw [SetLike.lt_iff_le_and_exists]
    refine ⟨fun u hu => ⟨(⟨u, hu⟩, 0), by simp [hΦ]⟩, p, ⟨(0, 1), by simp [hΦ]⟩, hpnot⟩
  set eΦ := LinearEquiv.ofInjective Φ hΦinj with heΦ
  have hval : ∀ x : LinearMap.range Φ, (x : V) = Φ (eΦ.symm x) := fun x =>
    (congrArg Subtype.val (eΦ.apply_symm_apply x)).symm.trans (LinearEquiv.ofInjective_apply _ _)
  refine ⟨LinearMap.range Φ, hlt, Ψ.comp eΦ.symm.toLinearMap, hΨinj.comp eΦ.symm.injective, ?_, ?_⟩
  · intro x y
    rw [hval x, hval y]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    generalize eΦ.symm x = a
    generalize eΦ.symm y = b
    obtain ⟨u, c⟩ := a
    obtain ⟨u', c'⟩ := b
    rw [hΨ, hΨ, hΦ, hΦ]
    dsimp only
    rw [expand B q (f u) (f u') c c', expand B p (u : V) (u' : V) c c', hf, hqq, hpp,
      ← hB q (f u), ← hB p (u : V), hqU u, hqU u', hpU _ u.2, hpU _ u'.2]
  · intro u
    have h5 : eΦ.symm ⟨u, hlt.le u.2⟩ = (u, 0) := by
      rw [LinearEquiv.symm_apply_eq]
      ext
      rw [LinearEquiv.ofInjective_apply, hΦ]
      simp
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h5, hΨ, zero_smul, add_zero]

end PI.Witt
