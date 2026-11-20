import Mathlib

namespace GlobalTheory

open Matrix

/- English proof (translation)
Introduce `E _ r Y _ C hspan s I hI hmem`. Establish `hc : ∀ j, ∃ c : Fin r → E, ∑ k, c k • ((fun a => C.1 a k), (fun a => C.2 a k)) = ((fun a => I a j), (0 : Fin r → E))`. Introduce `j`. Use `hmem j` as an intermediate fact. Rewrite `this` using `[← hspan]`.

Conclude with `(Submodule.mem_span_range_iff_exists_fun E).mp this`. Use `choose c hc using hc`. Set `J : Matrix (Fin r) (Fin s) E` to `Matrix.of fun k j => c j k`. Establish `h1 : C.1 * J = I`. Use extensionality with `a j`.

Use `congrFun (congrArg Prod.fst (hc j)) a` as an intermediate fact. Simplify using `only [Prod.fst_sum, Prod.smul_fst, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this`. Simplify using `only [Matrix.mul_apply, J, Matrix.of_apply]`. Rewrite using `[← this]`. Conclude with `Finset.sum_congr rfl fun k _ => mul_comm _ _`.

Establish `h2 : C.2 * J = 0`. Use extensionality with `a j`. Use `congrFun (congrArg Prod.snd (hc j)) a` as an intermediate fact. Simplify using `only [Prod.snd_sum, Prod.smul_snd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this`. Simplify using `only [Matrix.mul_apply, J, Matrix.of_apply, Matrix.zero_apply]`.

Rewrite using `[← this]`. Conclude with `Finset.sum_congr rfl fun k _ => mul_comm _ _`. Establish `hIinj : Function.Injective I.mulVec` using `Matrix.mulVec_injective_iff.mpr hI`. Establish `hJinj : Function.Injective J.mulVec`. Introduce `x y hxy`.

Apply `hIinj` to reduce the goal to its premises. Rewrite using `[← h1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hxy]`. Set `jL : (Fin s → E) →ₗ[E] (Fin r → E)` to `Matrix.toLin' J`. Establish `hker : LinearMap.ker jL = ⊥` using `LinearMap.ker_eq_bot.mpr (by`. Introduce `x y hxy; exact hJinj (by simpa [jL, Matrix.toLin'_apply] using hxy))`.

Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective jL hker`. Set `Wk` to `LinearMap.ker g`. Set `b` to `Module.finBasis E Wk`. Set `kL : (Fin (Module.finrank E Wk) → E) →ₗ[E] (Fin r → E)` to `Wk.subtype ∘ₗ b.equivFun.symm.toLinearMap`. Establish `hgP : ∀ x, g (x - jL (g x)) = 0`.

Introduce `x`. Rewrite using `[map_sub]`. Use `LinearMap.congr_fun hg (g x)` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, LinearMap.id_apply] at this`. Rewrite using `[this, sub_self]`.

Set `ψ : (Fin r → E) →ₗ[E] Wk` to `LinearMap.codRestrict Wk (LinearMap.id - jL ∘ₗ g) (fun x => by`. Simplify `hgP x)` using `[Wk, LinearMap.mem_ker]`. Set `mL : (Fin r → E) →ₗ[E] (Fin (Module.finrank E Wk) → E)` to `b.equivFun.toLinearMap ∘ₗ ψ`. Establish `hJ : J = LinearMap.toMatrix' jL` using `by simp [jL]`. Use `⟨Module.finrank E Wk, J, LinearMap.toMatrix' kL, LinearMap.toMatrix' g, LinearMap.toMatrix' mL, h1, h2, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hJ, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]`. Rewrite using `[← LinearMap.toMatrix'_comp]`. Establish `: g ∘ₗ kL = 0`. Use `LinearMap.ext fun y => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, LinearMap.zero_apply, kL]`.

Conclude with `(b.equivFun.symm y).2`. Rewrite using `[this, map_zero]`. Rewrite using `[hJ, ← LinearMap.toMatrix'_comp]`. Establish `: mL ∘ₗ jL = 0`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations.

Simplify using `only [LinearMap.comp_apply, LinearMap.zero_apply, mL]`. Establish `: ψ (jL x) = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [ψ, LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, ZeroMemClass.coe_zero]`. Use `LinearMap.congr_fun hg x` as an intermediate fact.

Simplify using `only [LinearMap.comp_apply, LinearMap.id_apply] at this`. Rewrite using `[this, sub_self]`. Rewrite using `[this, map_zero]`. Rewrite using `[this, map_zero]`. Rewrite using `[← LinearMap.toMatrix'_comp]`.

Establish `: mL ∘ₗ kL = LinearMap.id`. Use `LinearMap.ext fun y => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, LinearMap.id_apply, mL]`. Establish `: ψ (kL y) = b.equivFun.symm y`. Apply `Subtype.ext` to reduce the goal to its premises.

Establish `hk : g (kL y) = 0` using `(b.equivFun.symm y).2`. Simplify using `only [ψ, LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, hk, map_zero, sub_zero]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `b.equivFun.apply_symm_apply y`.

Rewrite using `[this, LinearMap.toMatrix'_id]`. Rewrite using `[hJ, ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp, ← map_add, ← LinearMap.toMatrix'_id]`. Use `congr 1`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, mL, kL]`.

Simplify using `only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, Submodule.coe_subtype, ψ, LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]`. Normalize the expressions using the abelian group laws.
-/
theorem exists_adapted_frame_of_isotropic_columns :
    ∀ (E : Type) [Field E] (r : ℕ) (Y : Submodule E ((Fin r → E) × (Fin r → E))),
      Module.finrank E Y = r →
      ∀ (C : Matrix (Fin r) (Fin r) E × Matrix (Fin r) (Fin r) E),
        Submodule.span E (Set.range fun j => ((fun a => C.1 a j), (fun a => C.2 a j))) = Y →
        ∀ (s : ℕ) (I : Matrix (Fin r) (Fin s) E), LinearIndependent E I.transpose →
          (∀ j, ((fun a => I a j), (0 : Fin r → E)) ∈ Y) →
          ∃ (t : ℕ) (J : Matrix (Fin r) (Fin s) E) (K : Matrix (Fin r) (Fin t) E)
            (L : Matrix (Fin s) (Fin r) E) (M : Matrix (Fin t) (Fin r) E),
            C.1 * J = I ∧ C.2 * J = 0 ∧ L * J = 1 ∧ L * K = 0 ∧ M * J = 0 ∧ M * K = 1 ∧
              J * L + K * M = 1 := by
  intro E _ r Y _ C hspan s I hI hmem

  have hc : ∀ j, ∃ c : Fin r → E,
      ∑ k, c k • ((fun a => C.1 a k), (fun a => C.2 a k)) = ((fun a => I a j), (0 : Fin r → E)) := by
    intro j
    have := hmem j
    rw [← hspan] at this
    exact (Submodule.mem_span_range_iff_exists_fun E).mp this
  choose c hc using hc
  let J : Matrix (Fin r) (Fin s) E := Matrix.of fun k j => c j k
  have h1 : C.1 * J = I := by
    ext a j
    have := congrFun (congrArg Prod.fst (hc j)) a
    simp only [Prod.fst_sum, Prod.smul_fst, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [Matrix.mul_apply, J, Matrix.of_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have h2 : C.2 * J = 0 := by
    ext a j
    have := congrFun (congrArg Prod.snd (hc j)) a
    simp only [Prod.snd_sum, Prod.smul_snd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at this
    simp only [Matrix.mul_apply, J, Matrix.of_apply, Matrix.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _

  have hIinj : Function.Injective I.mulVec := Matrix.mulVec_injective_iff.mpr hI
  have hJinj : Function.Injective J.mulVec := by
    intro x y hxy
    apply hIinj
    rw [← h1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hxy]
  let jL : (Fin s → E) →ₗ[E] (Fin r → E) := Matrix.toLin' J
  have hker : LinearMap.ker jL = ⊥ := LinearMap.ker_eq_bot.mpr (by
    intro x y hxy; exact hJinj (by simpa [jL, Matrix.toLin'_apply] using hxy))
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective jL hker
  let Wk := LinearMap.ker g
  let b := Module.finBasis E Wk
  let kL : (Fin (Module.finrank E Wk) → E) →ₗ[E] (Fin r → E) :=
    Wk.subtype ∘ₗ b.equivFun.symm.toLinearMap
  have hgP : ∀ x, g (x - jL (g x)) = 0 := by
    intro x
    rw [map_sub]
    have := LinearMap.congr_fun hg (g x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    rw [this, sub_self]
  let ψ : (Fin r → E) →ₗ[E] Wk :=
    LinearMap.codRestrict Wk (LinearMap.id - jL ∘ₗ g) (fun x => by
      simpa [Wk, LinearMap.mem_ker] using hgP x)
  let mL : (Fin r → E) →ₗ[E] (Fin (Module.finrank E Wk) → E) := b.equivFun.toLinearMap ∘ₗ ψ
  have hJ : J = LinearMap.toMatrix' jL := by simp [jL]
  refine ⟨Module.finrank E Wk, J, LinearMap.toMatrix' kL, LinearMap.toMatrix' g,
    LinearMap.toMatrix' mL, h1, h2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hJ, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
  · rw [← LinearMap.toMatrix'_comp]
    have : g ∘ₗ kL = 0 := by
      refine LinearMap.ext fun y => ?_
      simp only [LinearMap.comp_apply, LinearMap.zero_apply, kL]
      exact (b.equivFun.symm y).2
    rw [this, map_zero]
  · rw [hJ, ← LinearMap.toMatrix'_comp]
    have : mL ∘ₗ jL = 0 := by
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, LinearMap.zero_apply, mL]
      have : ψ (jL x) = 0 := by
        apply Subtype.ext
        simp only [ψ, LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
          LinearMap.comp_apply, ZeroMemClass.coe_zero]
        have := LinearMap.congr_fun hg x
        simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
        rw [this, sub_self]
      rw [this, map_zero]
    rw [this, map_zero]
  · rw [← LinearMap.toMatrix'_comp]
    have : mL ∘ₗ kL = LinearMap.id := by
      refine LinearMap.ext fun y => ?_
      simp only [LinearMap.comp_apply, LinearMap.id_apply, mL]
      have : ψ (kL y) = b.equivFun.symm y := by
        apply Subtype.ext
        have hk : g (kL y) = 0 := (b.equivFun.symm y).2
        simp only [ψ, LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
          LinearMap.comp_apply, hk, map_zero, sub_zero]
        rfl
      rw [this]
      exact b.equivFun.apply_symm_apply y
    rw [this, LinearMap.toMatrix'_id]
  · rw [hJ, ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp, ← map_add,
      ← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, mL, kL]
    simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, Submodule.coe_subtype, ψ,
      LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
    abel

end GlobalTheory
