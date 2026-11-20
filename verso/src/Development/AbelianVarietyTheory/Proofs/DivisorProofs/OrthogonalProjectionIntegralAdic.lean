import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory
namespace IdempotentUnimodular

/- English proof (translation)
Take `⟨s, b⟩` from `Submodule.basisOfPid (Pi.basisFun O (Fin n)) (LinearMap.range (Matrix.toLin' e))`. Use `⟨s, LinearMap.toMatrix b (Pi.basisFun O (Fin n)) (LinearMap.range (Matrix.toLin' e)).subtype, LinearMap.toMatrix (Pi.basisFun O (Fin n)) b (Matrix.toLin' e).rangeRestrict, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← LinearMap.toMatrix_comp]`. Establish `: (LinearMap.range (Matrix.toLin' e)).subtype ∘ₗ (Matrix.toLin' e).rangeRestrict = Matrix.toLin' e`. Use extensionality with `x`.

Simplify using the standard rewrite rules. Rewrite using `[this, LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']`. Rewrite using `[← LinearMap.toMatrix_comp]`. Establish `: (Matrix.toLin' e).rangeRestrict ∘ₗ (LinearMap.range (Matrix.toLin' e)).subtype = LinearMap.id`. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce and unpack `⟨_, x, rfl⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[Matrix.mulVec_mulVec, he]`. Rewrite using `[this, LinearMap.toMatrix_id]`.
-/
theorem exists_factor {O : Type*} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] {n : ℕ}
    (e : Matrix (Fin n) (Fin n) O) (he : e * e = e) :
    ∃ (s : ℕ) (F : Matrix (Fin n) (Fin s) O) (C : Matrix (Fin s) (Fin n) O),
      F * C = e ∧ C * F = 1 := by
  obtain ⟨s, b⟩ := Submodule.basisOfPid (Pi.basisFun O (Fin n)) (LinearMap.range (Matrix.toLin' e))
  refine ⟨s, LinearMap.toMatrix b (Pi.basisFun O (Fin n)) (LinearMap.range (Matrix.toLin' e)).subtype,
    LinearMap.toMatrix (Pi.basisFun O (Fin n)) b (Matrix.toLin' e).rangeRestrict, ?_, ?_⟩
  · rw [← LinearMap.toMatrix_comp]
    have : (LinearMap.range (Matrix.toLin' e)).subtype ∘ₗ (Matrix.toLin' e).rangeRestrict
        = Matrix.toLin' e := by
      ext x; simp
    rw [this, LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
  · rw [← LinearMap.toMatrix_comp]
    have : (Matrix.toLin' e).rangeRestrict ∘ₗ (LinearMap.range (Matrix.toLin' e)).subtype
        = LinearMap.id := by
      apply LinearMap.ext
      rintro ⟨_, x, rfl⟩
      apply Subtype.ext
      simp [Matrix.mulVec_mulVec, he]
    rw [this, LinearMap.toMatrix_id]

/- English proof (translation)
Establish `hee : e * e = e`. Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`. Simplify using `only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]`.

Conclude with `h2 _ (h1 x)`. Set `e₀ : Matrix (Fin n) (Fin n) O` to `Matrix.of fun i j => ⟨e i j, hint i j⟩`. Establish `he₀ : e₀.map O.subtype = e` using `by ext i j; rfl`. Establish `hee₀ : e₀ * e₀ = e₀`. Apply `Matrix.map_injective (f := O.subtype) Subtype.val_injective` to reduce the goal to its premises.

Use `show (e₀ * e₀).map O.subtype = e₀.map O.subtype`. Rewrite using `[Matrix.map_mul, he₀, hee]`. Take `⟨s, F₀, C₀, hFC₀, hCF₀⟩` from `exists_factor e₀ hee₀`. Set `σ₀ : O →+* O` to `(σ.comp O.subtype).codRestrict O (fun x => hσ x x.2)`. Use `set F := F₀.map O.subtype with hF`.

Use `set C := C₀.map O.subtype with hC`. Establish `hFC : F * C = e` using `by rw [hF, hC, ← Matrix.map_mul, hFC₀, he₀]`. Establish `hCF : C * F = 1`. Rewrite using `[hF, hC, ← Matrix.map_mul, hCF₀]`. Simplify using the standard rewrite rules.

Establish `heF : e * F = F` using `by rw [← hFC, Matrix.mul_assoc, hCF, Matrix.mul_one]`. Establish `hmem : ∀ j, (fun k => F k j) ∈ V`. Introduce `j`. Establish `: (fun k => F k j) = e *ᵥ (fun k => F k j)`. Use function extensionality and compare the values at `k`.

Use `conv_lhs => rw [← heF]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `h1 _`. Establish `hmem' : ∀ y, F *ᵥ y ∈ V`.

Introduce `y`. Rewrite using `[← heF, ← Matrix.mulVec_mulVec]`. Conclude with `h1 _`. Set `φ : V ≃ₗ[K] (Fin s → K)` to `LinearEquiv.ofLinear (Matrix.toLin' C ∘ₗ V.subtype) ((Matrix.toLin' F).codRestrict V (fun y => hmem' y)) (by`. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce `y`. Use `show C *ᵥ (F *ᵥ y) = y`. Rewrite using `[Matrix.mulVec_mulVec, hCF, Matrix.one_mulVec])`. Use the proof step `(by`. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce `x`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show F *ᵥ (C *ᵥ (x : Fin n → K)) = x`. Rewrite using `[Matrix.mulVec_mulVec, hFC, h2 _ x.2])`. Establish `hb : ∀ i k, ((Module.Basis.ofEquivFun φ i : V) : Fin n → K) k = F k i`.

Introduce `i k`. Rewrite using `[Module.Basis.coe_ofEquivFun]`. Use `show (F *ᵥ (Pi.single i 1)) k = F k i`. Simplify using the standard rewrite rules. Use `⟨s, Module.Basis.ofEquivFun φ, ?_⟩` and prove the remaining obligations.

Establish `hG : (Matrix.of fun i j => ∑ k, σ (((Module.Basis.ofEquivFun φ i : V) : Fin n → K) k) * ((Module.Basis.ofEquivFun φ j : V) : Fin n → K) k) = (F.map σ)ᵀ * F`. Use extensionality with `i j`. Simplify using `only [hb, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]`. Rewrite using `[hG]`. Establish `hFe : (F.map σ)ᵀ * e = (F.map σ)ᵀ`.

Use extensionality with `i j`. Use `h3 _ (hmem i) (Pi.single j 1)` as an intermediate fact. Simplify using `only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, Matrix.mulVec_single_one, sub_eq_zero] at this`. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]`. Rewrite `this` using `[Finset.sum_eq_single j (by intro b _ hb; simp [hb]) (by simp)]`.

Simplify using `using this.symm`. Establish `hinv : ((F.map σ)ᵀ * F) * (C * (C.map σ)ᵀ) = 1`. Rewrite using `[← Matrix.mul_assoc, Matrix.mul_assoc _ F, hFC, hFe, ← Matrix.transpose_mul, ← Matrix.map_mul, hCF]`. Simplify using the standard rewrite rules. Establish `hA : (F.map σ)ᵀ * F = ((F₀.map σ₀)ᵀ * F₀).map O.subtype`.

Rewrite using `[Matrix.map_mul]`. Both sides reduce to the same expression. Establish `hB : C * (C.map σ)ᵀ = (C₀ * (C₀.map σ₀)ᵀ).map O.subtype`. Rewrite using `[Matrix.map_mul]`. Both sides reduce to the same expression.

Use `⟨?_, (C * (C.map σ)ᵀ).det, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hA, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `Subtype.property _`. Rewrite using `[hB, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `Subtype.property _`.

Rewrite using `[← Matrix.det_mul, hinv, Matrix.det_one]`.
-/
theorem exists_basis {K : Type*} [Field K] (O : Subring K) [IsPrincipalIdealRing O]
    (σ : K →+* K) (hσ : ∀ x ∈ O, σ x ∈ O) {n : ℕ} (V : Submodule K (Fin n → K))
    (e : Matrix (Fin n) (Fin n) K) (hint : ∀ i j, e i j ∈ O) (h1 : ∀ x, e *ᵥ x ∈ V)
    (h2 : ∀ x ∈ V, e *ᵥ x = x) (h3 : ∀ x ∈ V, ∀ y, ∑ k, σ (x k) * (y - e *ᵥ y) k = 0) :
    ∃ (s : ℕ) (f : Module.Basis (Fin s) K V),
      (Matrix.of fun i j => ∑ k, σ ((f i : Fin n → K) k) * (f j : Fin n → K) k).det ∈ O ∧
      ∃ d ∈ O,
        (Matrix.of fun i j => ∑ k, σ ((f i : Fin n → K) k) * (f j : Fin n → K) k).det * d = 1 := by
  have hee : e * e = e := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
    exact h2 _ (h1 x)
  let e₀ : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨e i j, hint i j⟩
  have he₀ : e₀.map O.subtype = e := by ext i j; rfl
  have hee₀ : e₀ * e₀ = e₀ := by
    apply Matrix.map_injective (f := O.subtype) Subtype.val_injective
    show (e₀ * e₀).map O.subtype = e₀.map O.subtype
    rw [Matrix.map_mul, he₀, hee]
  obtain ⟨s, F₀, C₀, hFC₀, hCF₀⟩ := exists_factor e₀ hee₀
  let σ₀ : O →+* O := (σ.comp O.subtype).codRestrict O (fun x => hσ x x.2)
  set F := F₀.map O.subtype with hF
  set C := C₀.map O.subtype with hC
  have hFC : F * C = e := by rw [hF, hC, ← Matrix.map_mul, hFC₀, he₀]
  have hCF : C * F = 1 := by
    rw [hF, hC, ← Matrix.map_mul, hCF₀]; simp
  have heF : e * F = F := by rw [← hFC, Matrix.mul_assoc, hCF, Matrix.mul_one]
  have hmem : ∀ j, (fun k => F k j) ∈ V := by
    intro j
    have : (fun k => F k j) = e *ᵥ (fun k => F k j) := by
      funext k
      conv_lhs => rw [← heF]
      rfl
    rw [this]; exact h1 _
  have hmem' : ∀ y, F *ᵥ y ∈ V := by
    intro y
    rw [← heF, ← Matrix.mulVec_mulVec]; exact h1 _
  let φ : V ≃ₗ[K] (Fin s → K) := LinearEquiv.ofLinear (Matrix.toLin' C ∘ₗ V.subtype)
    ((Matrix.toLin' F).codRestrict V (fun y => hmem' y))
    (by
      apply LinearMap.ext
      intro y
      show C *ᵥ (F *ᵥ y) = y
      rw [Matrix.mulVec_mulVec, hCF, Matrix.one_mulVec])
    (by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      show F *ᵥ (C *ᵥ (x : Fin n → K)) = x
      rw [Matrix.mulVec_mulVec, hFC, h2 _ x.2])
  have hb : ∀ i k, ((Module.Basis.ofEquivFun φ i : V) : Fin n → K) k = F k i := by
    intro i k
    rw [Module.Basis.coe_ofEquivFun]
    show (F *ᵥ (Pi.single i 1)) k = F k i
    simp
  refine ⟨s, Module.Basis.ofEquivFun φ, ?_⟩
  have hG : (Matrix.of fun i j => ∑ k, σ (((Module.Basis.ofEquivFun φ i : V) : Fin n → K) k) *
      ((Module.Basis.ofEquivFun φ j : V) : Fin n → K) k) = (F.map σ)ᵀ * F := by
    ext i j
    simp only [hb, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [hG]
  have hFe : (F.map σ)ᵀ * e = (F.map σ)ᵀ := by
    ext i j
    have := h3 _ (hmem i) (Pi.single j 1)
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, Matrix.mulVec_single_one,
      sub_eq_zero] at this
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    rw [Finset.sum_eq_single j (by intro b _ hb; simp [hb]) (by simp)] at this
    simpa using this.symm
  have hinv : ((F.map σ)ᵀ * F) * (C * (C.map σ)ᵀ) = 1 := by
    rw [← Matrix.mul_assoc, Matrix.mul_assoc _ F, hFC, hFe, ← Matrix.transpose_mul,
      ← Matrix.map_mul, hCF]
    simp
  have hA : (F.map σ)ᵀ * F = ((F₀.map σ₀)ᵀ * F₀).map O.subtype := by
    rw [Matrix.map_mul]; rfl
  have hB : C * (C.map σ)ᵀ = (C₀ * (C₀.map σ₀)ᵀ).map O.subtype := by
    rw [Matrix.map_mul]; rfl
  refine ⟨?_, (C * (C.map σ)ᵀ).det, ?_, ?_⟩
  · rw [hA, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact Subtype.property _
  · rw [hB, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact Subtype.property _
  · rw [← Matrix.det_mul, hinv, Matrix.det_one]

/- English proof (translation)
Introduce `E _ _ w σ _ hv n V e hint h1 h2 h3`. Use `haveI : IsPrincipalIdealRing (w.adicCompletionIntegers E).toSubring := inferInstanceAs (IsPrincipalIdealRing (w.adicCompletionIntegers E))`. Establish `hO : ∀ x, x ∈ (w.adicCompletionIntegers E).toSubring ↔ Valued.v x ≤ 1` using `fun x => Iff.rfl`. Take `⟨s, f, hd, d, hd', hdd⟩` from `exists_basis (w.adicCompletionIntegers E).toSubring σ (fun x hx => by rw [hO] at hx ⊢; rwa [hv]) V e (fun i j => (hO _).2 (hint i j)) h1 h2 h3`. Use `⟨s, f, ?_⟩` and prove the remaining obligations.

Rewrite `hd`, `hd'` using `[hO]`. Establish `h` using `congrArg Valued.v hdd`. Rewrite `h` using `[map_mul, map_one]`. Use `le_antisymm hd ?_` and prove the remaining obligations. Rewrite using `[← h]`.

Conclude with `mul_le_of_le_one_right' hd'`.
-/
theorem main : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (σ : w.adicCompletion E →+* w.adicCompletion E),
    (∀ x, σ (σ x) = x) → (∀ x, Valued.v (σ x) = Valued.v x) → ∀ (n : ℕ) (V : Submodule (w.adicCompletion E) (Fin n → w.adicCompletion E))
    (e : Matrix (Fin n) (Fin n) (w.adicCompletion E)), (∀ i j, Valued.v (e i j) ≤ 1) → (∀ x, e *ᵥ x ∈ V) →
    (∀ x ∈ V, e *ᵥ x = x) → (∀ x ∈ V, ∀ y, ∑ k, σ (x k) * (y - e *ᵥ y) k = 0) →
    ∃ (s : ℕ) (f : Module.Basis (Fin s) (w.adicCompletion E) V),
      Valued.v (Matrix.of fun i j => ∑ k, σ ((f i : Fin n → w.adicCompletion E) k) * (f j : Fin n → w.adicCompletion E) k).det = 1 := by
  intro E _ _ w σ _ hv n V e hint h1 h2 h3
  haveI : IsPrincipalIdealRing (w.adicCompletionIntegers E).toSubring :=
    inferInstanceAs (IsPrincipalIdealRing (w.adicCompletionIntegers E))
  have hO : ∀ x, x ∈ (w.adicCompletionIntegers E).toSubring ↔ Valued.v x ≤ 1 := fun x => Iff.rfl
  obtain ⟨s, f, hd, d, hd', hdd⟩ := exists_basis (w.adicCompletionIntegers E).toSubring σ
    (fun x hx => by rw [hO] at hx ⊢; rwa [hv]) V e (fun i j => (hO _).2 (hint i j)) h1 h2 h3
  refine ⟨s, f, ?_⟩
  rw [hO] at hd hd'
  have h := congrArg Valued.v hdd
  rw [map_mul, map_one] at h
  refine le_antisymm hd ?_
  rw [← h]
  exact mul_le_of_le_one_right' hd'

end IdempotentUnimodular
end GlobalTheory
