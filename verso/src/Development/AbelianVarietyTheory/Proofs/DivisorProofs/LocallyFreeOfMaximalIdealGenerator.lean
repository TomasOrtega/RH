import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.InvGlue

/- English proof (translation)
Set `pw : ℕ → Submonoid.powers r` to `fun n => ⟨r ^ n, Submonoid.pow_mem _ (Submonoid.mem_powers r) n⟩`. Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `y hy`. Proceed by induction on `y using Localization.induction_on with`.

Consider the case `H p`. Take `⟨a, s⟩` from `p`. Simplify using `only [LinearMap.toSpanSingleton_apply] at hy`. Rewrite `hy` using `[LocalizedModule.mk_smul_mk, _root_.mul_one]`. Rewrite `hy` using `[← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]`.

Take `⟨u, hu⟩` from `hy`. Simplify using `only [smul_zero] at hu`. Establish `: ((u : A) * (s : A) * a) • m = 0`. Rewrite using `[mul_smul, mul_smul]`. Simplify `hu` using `[Submonoid.smul_def]`.

Take `⟨n, hn⟩` from `hinj _ this`. Rewrite using `[Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff]`. Conclude with `⟨pw n * u * s, by simpa [pw, _root_.mul_assoc] using hn⟩`. Introduce `z`. Proceed by induction on `z using LocalizedModule.induction_on with`.

Consider the case `h x s`. Take `⟨n, a, hn⟩` from `hsurj x`. Use `⟨Localization.mk a (pw n * s), ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.toSpanSingleton_apply]`. Rewrite using `[LocalizedModule.mk_smul_mk, _root_.mul_one, ← hn, ← LocalizedModule.mk_cancel_common_left (pw n) s x]`.

Both sides reduce to the same expression.
-/
theorem bijective_localized {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M] (r : A) (m : M)
    (hsurj : ∀ x : M, ∃ (n : ℕ) (a : A), r ^ n • x = a • m)
    (hinj : ∀ a : A, a • m = 0 → ∃ n : ℕ, r ^ n * a = 0) :
    Function.Bijective (LinearMap.toSpanSingleton (Localization.Away r)
      (LocalizedModule (Submonoid.powers r) M) (LocalizedModule.mk m 1)) := by
  let pw : ℕ → Submonoid.powers r := fun n => ⟨r ^ n, Submonoid.pow_mem _ (Submonoid.mem_powers r) n⟩
  constructor
  · rw [injective_iff_map_eq_zero]
    intro y hy
    induction y using Localization.induction_on with
    | H p =>
      obtain ⟨a, s⟩ := p
      simp only [LinearMap.toSpanSingleton_apply] at hy
      rw [LocalizedModule.mk_smul_mk, _root_.mul_one] at hy
      rw [← LocalizedModule.zero_mk s, LocalizedModule.mk_eq] at hy
      obtain ⟨u, hu⟩ := hy
      simp only [smul_zero] at hu
      have : ((u : A) * (s : A) * a) • m = 0 := by
        rw [mul_smul, mul_smul]; simpa [Submonoid.smul_def] using hu
      obtain ⟨n, hn⟩ := hinj _ this
      rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff]
      exact ⟨pw n * u * s, by simpa [pw, _root_.mul_assoc] using hn⟩
  · intro z
    induction z using LocalizedModule.induction_on with
    | h x s =>
      obtain ⟨n, a, hn⟩ := hsurj x
      refine ⟨Localization.mk a (pw n * s), ?_⟩
      simp only [LinearMap.toSpanSingleton_apply]
      rw [LocalizedModule.mk_smul_mk, _root_.mul_one, ← hn,
        ← LocalizedModule.mk_cancel_common_left (pw n) s x]
      rfl

/- English proof (translation)
Introduce `R O _ _ J _ b M _ _ _ _ hyp`. Use `letI : Module (R ⊗[ℤ] O) M := TensorProduct.Algebra.module`. Set `B` to `Algebra.TensorProduct.basis R b`. Establish `hL : ∀ (m : M) (c : J →₀ R), (B.repr.symm c) • m = Finsupp.linearCombination R (fun i => b i • m) c`. Introduce `m c`.

Proceed by induction on `c using Finsupp.induction_linear with`. Consider the case `zero => simp`. Consider the case `add c d hc hd => rw [map_add, add_smul, hc, hd, map_add]`. Consider the case `single i x`. Rewrite using `[Module.Basis.repr_symm_single, Finsupp.linearCombination_single]`.

Simplify using `only [B, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]`. Conclude with `TensorProduct.Algebra.smul_def x (b i) m`. Establish `hr : ∀ (g : R) (x : M), (algebraMap R (R ⊗[ℤ] O) g) • x = g • x`. Introduce `g x`. Rewrite using `[Algebra.TensorProduct.algebraMap_apply, TensorProduct.Algebra.smul_def, one_smul]`.

Simplify using the standard rewrite rules. Set `G : Set R` to `{g | ∃ m : M, (∀ x : M, ∃ (n : ℕ) (c : J →₀ R), g ^ n • x = Finsupp.linearCombination R (fun i => b i • m) c) ∧ (∀ c : J →₀ R, Finsupp.linearCombination R (fun i => b i • m) c = 0 → ∃ n : ℕ, g ^ n • c = 0)}`. Establish `hG : Ideal.span G = ⊤`. Assume the negation of the conclusion as `h`. Take `⟨p, hp, hGp⟩` from `Ideal.exists_le_maximal _ h`.

Take `⟨g, hg, hgG⟩` from `hyp p hp`. Conclude with `hg (hGp (Ideal.subset_span hgG))`. Set `s : Set (R ⊗[ℤ] O)` to `algebraMap R (R ⊗[ℤ] O) '' G`. Establish `hs : Ideal.span s = ⊤`. Rewrite using `[← Ideal.map_span, hG, Ideal.map_top]`.

Use `GlobalTheory.invertible_of_isLocalizedModule_span s hs (fun r => Localization.Away r.1) (fun r => LocalizedModule (Submonoid.powers r.1) M) (fun r => LocalizedModule.mkLinearMap (Submonoid.powers r.1) M) fun r => ?_` and prove the remaining obligations. Take `⟨g, ⟨m, h1, h2⟩, hg⟩` from `r.2`. Use `GlobalTheory.invertible_of_bijective_toSpanSingleton (e := LocalizedModule.mk m 1) (bijective_localized r.1 m ?_ ?_)` and prove the remaining obligations. Introduce `x`. Take `⟨n, c, hc⟩` from `h1 x`.

Conclude with `⟨n, B.repr.symm c, by rw [← hg, ← map_pow, hr, hL, hc]⟩`. Introduce `a ha`. Establish `ha' : a = B.repr.symm (B.repr a)` using `(B.repr.symm_apply_apply a).symm`. Take `⟨n, hn⟩` from `h2 (B.repr a) (by rw [← hL, ← ha', ha])`. Use `⟨n, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hg, ← map_pow, ← Algebra.smul_def, ha', ← map_smul, hn, map_zero]`.
-/
theorem invertible_of_locally_singly_generated : ∀ (R O : Type) [CommRing R] [CommRing O] (J : Type) [Fintype J] (b : Module.Basis J ℤ O)
    (M : Type) [AddCommGroup M] [Module R M] [Module O M] [SMulCommClass R O M],
    (∀ p : Ideal R, p.IsMaximal → ∃ g : R, g ∉ p ∧ ∃ m : M,
      (∀ x : M, ∃ (n : ℕ) (c : J →₀ R), g ^ n • x = Finsupp.linearCombination R (fun i => b i • m) c) ∧
      (∀ c : J →₀ R, Finsupp.linearCombination R (fun i => b i • m) c = 0 → ∃ n : ℕ, g ^ n • c = 0)) →
    letI : Module (R ⊗[ℤ] O) M := TensorProduct.Algebra.module
    Module.Invertible (R ⊗[ℤ] O) M := by
  intro R O _ _ J _ b M _ _ _ _ hyp
  letI : Module (R ⊗[ℤ] O) M := TensorProduct.Algebra.module
  let B := Algebra.TensorProduct.basis R b
  have hL : ∀ (m : M) (c : J →₀ R),
      (B.repr.symm c) • m = Finsupp.linearCombination R (fun i => b i • m) c := by
    intro m c
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => rw [map_add, add_smul, hc, hd, map_add]
    | single i x =>
      rw [Module.Basis.repr_symm_single, Finsupp.linearCombination_single]
      simp only [B, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul,
        _root_.mul_one]
      exact TensorProduct.Algebra.smul_def x (b i) m
  have hr : ∀ (g : R) (x : M), (algebraMap R (R ⊗[ℤ] O) g) • x = g • x := by
    intro g x
    rw [Algebra.TensorProduct.algebraMap_apply, TensorProduct.Algebra.smul_def, one_smul]
    simp
  let G : Set R := {g | ∃ m : M,
      (∀ x : M, ∃ (n : ℕ) (c : J →₀ R), g ^ n • x = Finsupp.linearCombination R (fun i => b i • m) c) ∧
      (∀ c : J →₀ R, Finsupp.linearCombination R (fun i => b i • m) c = 0 → ∃ n : ℕ, g ^ n • c = 0)}
  have hG : Ideal.span G = ⊤ := by
    by_contra h
    obtain ⟨p, hp, hGp⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨g, hg, hgG⟩ := hyp p hp
    exact hg (hGp (Ideal.subset_span hgG))
  let s : Set (R ⊗[ℤ] O) := algebraMap R (R ⊗[ℤ] O) '' G
  have hs : Ideal.span s = ⊤ := by
    rw [← Ideal.map_span, hG, Ideal.map_top]
  refine GlobalTheory.invertible_of_isLocalizedModule_span s hs (fun r => Localization.Away r.1)
    (fun r => LocalizedModule (Submonoid.powers r.1) M)
    (fun r => LocalizedModule.mkLinearMap (Submonoid.powers r.1) M) fun r => ?_
  obtain ⟨g, ⟨m, h1, h2⟩, hg⟩ := r.2
  refine GlobalTheory.invertible_of_bijective_toSpanSingleton (e := LocalizedModule.mk m 1)
    (bijective_localized r.1 m ?_ ?_)
  · intro x
    obtain ⟨n, c, hc⟩ := h1 x
    exact ⟨n, B.repr.symm c, by rw [← hg, ← map_pow, hr, hL, hc]⟩
  · intro a ha
    have ha' : a = B.repr.symm (B.repr a) := (B.repr.symm_apply_apply a).symm
    obtain ⟨n, hn⟩ := h2 (B.repr a) (by rw [← hL, ← ha', ha])
    refine ⟨n, ?_⟩
    rw [← hg, ← map_pow, ← Algebra.smul_def, ha', ← map_smul, hn, map_zero]

end GlobalTheory.InvGlue
