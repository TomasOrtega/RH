import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.Shin.NrmBasic

section General

variable {G Γ : Type} [Group G] [Group Γ] (φ : Γ →* MulAut G) (s : Γ)

/- English proof (translation)
Simplify using `[nrmG]`.
-/
theorem nrmG_zero (δ : G) : nrmG φ s 0 δ = 1 := by
  simp [nrmG]

/- English proof (translation)
Simplify using `[nrmG, List.range_succ, List.map_append, List.prod_append]`.
-/
theorem nrmG_succ (l : ℕ) (δ : G) : nrmG φ s (l + 1) δ = nrmG φ s l δ * φ (s ^ l) δ := by
  simp [nrmG, List.range_succ, List.map_append, List.prod_append]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `zero => simp [nrmG_zero]`. Consider the case `succ l ih`. Rewrite using `[nrmG_succ, nrmG_succ, ih]`. Establish `h1 : φ (s ^ l) (y⁻¹ * δ * φ s y) = (φ (s ^ l) y)⁻¹ * φ (s ^ l) δ * φ (s ^ (l + 1)) y`.

Rewrite using `[map_mul, map_mul, map_inv, pow_succ, map_mul, MulAut.mul_apply]`. Rewrite using `[h1]`. Use `group`.
-/
theorem nrmG_twConj (l : ℕ) (δ y : G) :
    nrmG φ s l (y⁻¹ * δ * φ s y) = y⁻¹ * nrmG φ s l δ * φ (s ^ l) y := by
  induction l with
  | zero => simp [nrmG_zero]
  | succ l ih =>
    rw [nrmG_succ, nrmG_succ, ih]
    have h1 : φ (s ^ l) (y⁻¹ * δ * φ s y) = (φ (s ^ l) y)⁻¹ * φ (s ^ l) δ * φ (s ^ (l + 1)) y := by
      rw [map_mul, map_mul, map_inv, pow_succ, map_mul, MulAut.mul_apply]
    rw [h1]
    group

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `zero => simp [nrmG_zero]`. Consider the case `succ l ih`. Rewrite using `[nrmG_succ, map_mul, ← mul_assoc, ih, pow_succ', map_mul, MulAut.mul_apply]`.
-/
theorem mul_map_nrmG (l : ℕ) (δ : G) :
    δ * φ s (nrmG φ s l δ) = nrmG φ s l δ * φ (s ^ l) δ := by
  induction l with
  | zero => simp [nrmG_zero]
  | succ l ih =>
    rw [nrmG_succ, map_mul, ← mul_assoc, ih, pow_succ', map_mul, MulAut.mul_apply]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `zero => simp [nrmG_zero]`. Consider the case `succ l ih`. Rewrite using `[nrmG_succ, nrmG_succ, nrmG_succ, ih, map_mul]`. Establish `hc : Commute (nrmG φ s l ε) (φ (s ^ l) δ)`.

Unfold `nrmG`. Apply `Commute.list_prod_left` to reduce the goal to its premises. Introduce `x hx`. Take `⟨i, -, rfl⟩` from `List.mem_map.1 hx`. Conclude with `(h l i).symm`.

Rewrite using `[mul_assoc, mul_assoc, ← mul_assoc (nrmG φ s l ε), hc.eq, mul_assoc]`.
-/
theorem nrmG_mul (l : ℕ) (δ ε : G) (h : ∀ i j : ℕ, Commute (φ (s ^ i) δ) (φ (s ^ j) ε)) :
    nrmG φ s l (δ * ε) = nrmG φ s l δ * nrmG φ s l ε := by
  induction l with
  | zero => simp [nrmG_zero]
  | succ l ih =>
    rw [nrmG_succ, nrmG_succ, nrmG_succ, ih, map_mul]
    have hc : Commute (nrmG φ s l ε) (φ (s ^ l) δ) := by
      unfold nrmG
      apply Commute.list_prod_left
      intro x hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
      exact (h l i).symm
    rw [mul_assoc, mul_assoc, ← mul_assoc (nrmG φ s l ε), hc.eq, mul_assoc]

end General

section Fields

variable {F F' : Type} [Field F] [Field F'] [Algebra F F'] [Finite F']

/- English proof (translation)
Use `haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective`. Rewrite using `[← IsGalois.card_aut_eq_finrank]`. Conclude with `pow_card_eq_one'`.
-/
theorem pow_finrank_eq_one (s : F' ≃ₐ[F] F') : s ^ Module.finrank F F' = 1 := by
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  rw [← IsGalois.card_aut_eq_finrank]
  exact pow_card_eq_one'

/- English proof (translation)
Use `haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Rewrite using `[← IntermediateField.mem_bot, ← IsGalois.fixedField_top, IntermediateField.mem_fixedField_iff]`. Introduce `t _`.

Take `⟨k, rfl⟩` from `Subgroup.mem_zpowers_iff.1 (hs t)`. Establish `h1 : ∀ m : ℕ, (s ^ m) x = x`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => simp`.

Consider the case `succ m ih => rw [pow_succ, AlgEquiv.mul_apply, hx, ih]`. Establish `h2 : ∀ m : ℕ, (s⁻¹ ^ m) x = x`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => simp`.

Consider the case `succ m ih`. Rewrite using `[pow_succ, AlgEquiv.mul_apply]`. Establish `: s⁻¹ x = x` using `by conv_lhs => rw [← hx]`. Conclude with `s.symm_apply_apply x`. Rewrite using `[this, ih]`.

Consider the cases of `k with`. Consider the case `ofNat m => simpa using h1 m`. Consider the case `negSucc m => rw [zpow_negSucc, ← inv_pow]`. Conclude with `h2 (m + 1)`. Introduce and unpack `⟨a, rfl⟩`.

Conclude with `s.commutes a`.
-/
theorem fixed_iff (s : F' ≃ₐ[F] F') (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) (x : F') :
    s x = x ↔ x ∈ Set.range (algebraMap F F') := by
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  constructor
  · intro hx
    rw [← IntermediateField.mem_bot, ← IsGalois.fixedField_top, IntermediateField.mem_fixedField_iff]
    intro t _
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hs t)
    have h1 : ∀ m : ℕ, (s ^ m) x = x := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ, AlgEquiv.mul_apply, hx, ih]
    have h2 : ∀ m : ℕ, (s⁻¹ ^ m) x = x := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ, AlgEquiv.mul_apply]
        have : s⁻¹ x = x := by
          conv_lhs => rw [← hx]
          exact s.symm_apply_apply x
        rw [this, ih]
    cases k with
    | ofNat m => simpa using h1 m
    | negSucc m => rw [zpow_negSucc, ← inv_pow]; exact h2 (m + 1)
  · rintro ⟨a, rfl⟩
    exact s.commutes a

end Fields

/- English proof (translation)
Introduce `F F' _ _ _ _ s hs n`. Establish `hl` using `pow_finrank_eq_one s`. Establish `hinj : Function.Injective (algebraMap F F')` using `(algebraMap F F').injective`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `he : ∀ i j, s ((x : Matrix (Fin n) (Fin n) F') i j) = (x : Matrix (Fin n) (Fin n) F') i j`. Introduce `i j`. Use `congrArg (fun z : GL (Fin n) F' => (z : Matrix (Fin n) (Fin n) F') i j) hx` as an intermediate fact.

Simplify `this` using `[galAct_apply, gal]`. Use `choose M0 hM using fun i j => (fixed_iff s hs _).1 (he i j)`. Set `M : Matrix (Fin n) (Fin n) F` to `Matrix.of M0`. Establish `hdet : (algebraMap F F') (M.det) = (x : Matrix (Fin n) (Fin n) F').det`. Rewrite using `[RingHom.map_det]`.

Use `congr 1`. Use extensionality with `i j`. Conclude with `hM i j`. Establish `hu : IsUnit M`. Rewrite using `[Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]`.

Introduce `h0`. Establish `: (x : Matrix (Fin n) (Fin n) F').det = 0` using `by rw [← hdet, h0, map_zero]`. Conclude with `(Matrix.GeneralLinearGroup.det_ne_zero x) this`. Use `⟨hu.unit, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`.

Simplify using `[incl, gal, M, hM]`. Introduce and unpack `⟨y, rfl⟩`. Use extensionality with `i j`. Simplify using `[galAct_apply, gal, incl]`. Introduce `a b hab`.

Use extensionality with `i j`. Use `congrArg (fun z : GL (Fin n) F' => (z : Matrix (Fin n) (Fin n) F') i j) hab` as an intermediate fact. Conclude with `hinj (by simpa [incl, gal] using this)`. Introduce `δ y`. Unfold `nrm`.

Rewrite using `[nrmG_twConj, hl, map_one, MulAut.one_apply]`. Introduce `δ`. Unfold `nrm`. Rewrite using `[mul_map_nrmG, hl, map_one, MulAut.one_apply]`. Introduce `δ ε h`.

Unfold `nrm`. Conclude with `nrmG_mul _ _ _ _ _ fun i j => h _ _`.
-/
theorem main : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ n : ℕ, (∀ x : GL (Fin n) F', galAct F F' n s x = x ↔ ∃ y, incl F F' n y = x) ∧ Function.Injective (incl F F' n) ∧ (∀ δ y : GL (Fin n) F', nrm s (y⁻¹ * δ * galAct F F' n s y) = y⁻¹ * nrm s δ * y) ∧ (∀ δ : GL (Fin n) F', δ * galAct F F' n s (nrm s δ) = nrm s δ * δ) ∧ ∀ δ ε : GL (Fin n) F', (∀ t u : F' ≃ₐ[F] F', Commute (galAct F F' n t δ) (galAct F F' n u ε)) → nrm s (δ * ε) = nrm s δ * nrm s ε := by
  intro F F' _ _ _ _ s hs n
  have hl := pow_finrank_eq_one s
  have hinj : Function.Injective (algebraMap F F') := (algebraMap F F').injective
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      have he : ∀ i j, s ((x : Matrix (Fin n) (Fin n) F') i j) = (x : Matrix (Fin n) (Fin n) F') i j := by
        intro i j
        have := congrArg (fun z : GL (Fin n) F' => (z : Matrix (Fin n) (Fin n) F') i j) hx
        simpa [galAct_apply, gal] using this
      choose M0 hM using fun i j => (fixed_iff s hs _).1 (he i j)
      let M : Matrix (Fin n) (Fin n) F := Matrix.of M0
      have hdet : (algebraMap F F') (M.det) = (x : Matrix (Fin n) (Fin n) F').det := by
        rw [RingHom.map_det]
        congr 1
        ext i j
        exact hM i j
      have hu : IsUnit M := by
        rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
        intro h0
        have : (x : Matrix (Fin n) (Fin n) F').det = 0 := by rw [← hdet, h0, map_zero]
        exact (Matrix.GeneralLinearGroup.det_ne_zero x) this
      refine ⟨hu.unit, ?_⟩
      ext i j
      simp [incl, gal, M, hM]
    · rintro ⟨y, rfl⟩
      ext i j
      simp [galAct_apply, gal, incl]
  · intro a b hab
    ext i j
    have := congrArg (fun z : GL (Fin n) F' => (z : Matrix (Fin n) (Fin n) F') i j) hab
    exact hinj (by simpa [incl, gal] using this)
  · intro δ y
    unfold nrm
    rw [nrmG_twConj, hl, map_one, MulAut.one_apply]
  · intro δ
    unfold nrm
    rw [mul_map_nrmG, hl, map_one, MulAut.one_apply]
  · intro δ ε h
    unfold nrm
    exact nrmG_mul _ _ _ _ _ fun i j => h _ _

end GlobalTheory.Shin.NrmBasic

end
