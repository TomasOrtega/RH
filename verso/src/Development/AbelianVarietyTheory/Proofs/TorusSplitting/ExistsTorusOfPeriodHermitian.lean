import Mathlib
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.TorusAtExistsOfParts
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ConjEqNegOfSqEqNegNat

set_option autoImplicit false

namespace GlobalTheory.PeriodTorus

section LinAlg

open Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ComplexOrder MatrixOrder ComplexConjugate

variable {g : ℕ}

/- English proof (translation)
Simplify using `[hermForm, add_dotProduct]`.
-/
theorem hermForm_add_left (Hm : Matrix (Fin g) (Fin g) ℂ) (x y z : Fin g → ℂ) :
    hermForm Hm (x + y) z = hermForm Hm x z + hermForm Hm y z := by
  simp [hermForm, add_dotProduct]

/- English proof (translation)
Simplify using `[hermForm, mulVec_add, dotProduct_add]`.
-/
theorem hermForm_add_right (Hm : Matrix (Fin g) (Fin g) ℂ) (x y z : Fin g → ℂ) :
    hermForm Hm x (y + z) = hermForm Hm x y + hermForm Hm x z := by
  simp [hermForm, mulVec_add, dotProduct_add]

/- English proof (translation)
Simplify using `[hermForm, smul_dotProduct]`.
-/
theorem hermForm_smul_left (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (x z : Fin g → ℂ) :
    hermForm Hm (c • x) z = c * hermForm Hm x z := by
  simp [hermForm, smul_dotProduct]

/- English proof (translation)
Simplify using `[hermForm, mulVec_smul, dotProduct_smul]`.
-/
theorem hermForm_smul_right (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (x z : Fin g → ℂ) :
    hermForm Hm x (c • z) = conj c * hermForm Hm x z := by
  simp [hermForm, mulVec_smul, dotProduct_smul]

/- English proof (translation)
Establish `hsm (r : ℝ) (x : Fin g → ℂ) : r • x = (r : ℂ) • x` using `by ext; simp`. Establish `e1 (d x y : Fin g → ℂ) : (fun k => d k * (x + y) k) = (fun k => d k * x k) + fun k => d k * y k` using `by ext; simp [mul_add]`. Establish `e2 (d : Fin g → ℂ) (c : ℂ) (x : Fin g → ℂ) : (fun k => d k * (c • x) k) = c • fun k => d k * x k` using `by ext; simp [mul_left_comm]`. Establish `h1 : ∀ x ∈ s, ∀ y, (hermForm Hm (fun k => d k * x k) y).im = (hermForm Hm x (fun k => conj (d k) * y k)).im`. Introduce `x hx y`.

Establish `hy : y ∈ Submodule.span ℝ s` using `hs ▸ Submodule.mem_top`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy => exact h x hx y hy`. Consider the case `zero => simp [hermForm, dotProduct, mulVec]`. Consider the case `add y z _ _ hy hz`.

Rewrite using `[e1 (fun k => conj (d k)), hermForm_add_right, hermForm_add_right, Complex.add_im, Complex.add_im, hy, hz]`. Consider the case `smul r y _ hy`. Rewrite using `[hsm, e2 (fun k => conj (d k)), hermForm_smul_right, hermForm_smul_right, Complex.conj_ofReal, Complex.im_ofReal_mul, Complex.im_ofReal_mul, hy]`. Establish `h2 : ∀ x y, (hermForm Hm (fun k => d k * x k) y).im = (hermForm Hm x (fun k => conj (d k) * y k)).im`. Introduce `x y`.

Establish `hx : x ∈ Submodule.span ℝ s` using `hs ▸ Submodule.mem_top`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => exact h1 x hx y`. Consider the case `zero => simp [hermForm]`. Consider the case `add x z _ _ hx hz`.

Rewrite using `[e1, hermForm_add_left, hermForm_add_left, Complex.add_im, Complex.add_im, hx, hz]`. Consider the case `smul r x _ hx`. Rewrite using `[hsm, e2, hermForm_smul_left, hermForm_smul_left, Complex.im_ofReal_mul, Complex.im_ofReal_mul, hx]`. Establish `h3 : ∀ x y, hermForm Hm (fun k => d k * x k) y = hermForm Hm x (fun k => conj (d k) * y k)`. Introduce `x y`.

Use `Complex.ext ?_ (h2 x y)` and prove the remaining obligations. Use `h2 (Complex.I • x) y` as an intermediate fact. Rewrite `this` using `[e2, hermForm_smul_left, hermForm_smul_left]`. Simplify using `using this`. Use extensionality with `a b`.

Use `h3 (Pi.single a 1) (Pi.single b 1)` as an intermediate fact. Simplify using `only [hermForm, dotProduct, mulVec, Pi.star_apply, Pi.single_apply] at this`. Simplify using `only [mul_diagonal, diagonal_mul]`. Simplify `this` using `[apply_ite, mul_comm, eq_comm]`.
-/
theorem commute_of_im (Hm : Matrix (Fin g) (Fin g) ℂ) (d : Fin g → ℂ) (s : Set (Fin g → ℂ))
    (hs : Submodule.span ℝ s = ⊤)
    (h : ∀ x ∈ s, ∀ y ∈ s, (hermForm Hm (fun k => d k * x k) y).im =
      (hermForm Hm x (fun k => conj (d k) * y k)).im) :
    Commute Hm (diagonal d) := by
  have hsm (r : ℝ) (x : Fin g → ℂ) : r • x = (r : ℂ) • x := by ext; simp
  have e1 (d x y : Fin g → ℂ) : (fun k => d k * (x + y) k) = (fun k => d k * x k) + fun k => d k * y k := by
    ext; simp [mul_add]
  have e2 (d : Fin g → ℂ) (c : ℂ) (x : Fin g → ℂ) : (fun k => d k * (c • x) k) = c • fun k => d k * x k := by
    ext; simp [mul_left_comm]
  have h1 : ∀ x ∈ s, ∀ y, (hermForm Hm (fun k => d k * x k) y).im =
      (hermForm Hm x (fun k => conj (d k) * y k)).im := by
    intro x hx y
    have hy : y ∈ Submodule.span ℝ s := hs ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy => exact h x hx y hy
    | zero => simp [hermForm, dotProduct, mulVec]
    | add y z _ _ hy hz =>
      rw [e1 (fun k => conj (d k)), hermForm_add_right, hermForm_add_right, Complex.add_im, Complex.add_im, hy, hz]
    | smul r y _ hy =>
      rw [hsm, e2 (fun k => conj (d k)), hermForm_smul_right, hermForm_smul_right, Complex.conj_ofReal,
        Complex.im_ofReal_mul, Complex.im_ofReal_mul, hy]
  have h2 : ∀ x y, (hermForm Hm (fun k => d k * x k) y).im =
      (hermForm Hm x (fun k => conj (d k) * y k)).im := by
    intro x y
    have hx : x ∈ Submodule.span ℝ s := hs ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx => exact h1 x hx y
    | zero => simp [hermForm]
    | add x z _ _ hx hz =>
      rw [e1, hermForm_add_left, hermForm_add_left, Complex.add_im, Complex.add_im, hx, hz]
    | smul r x _ hx =>
      rw [hsm, e2, hermForm_smul_left, hermForm_smul_left, Complex.im_ofReal_mul, Complex.im_ofReal_mul, hx]
  have h3 : ∀ x y, hermForm Hm (fun k => d k * x k) y = hermForm Hm x (fun k => conj (d k) * y k) := by
    intro x y
    refine Complex.ext ?_ (h2 x y)
    have := h2 (Complex.I • x) y
    rw [e2, hermForm_smul_left, hermForm_smul_left] at this
    simpa using this
  ext a b
  have := h3 (Pi.single a 1) (Pi.single b 1)
  simp only [hermForm, dotProduct, mulVec, Pi.star_apply, Pi.single_apply] at this
  simp only [mul_diagonal, diagonal_mul]
  simpa [apply_ite, mul_comm, eq_comm] using this

/- English proof (translation)
Establish `hP : Hm.PosDef` using `PosDef.of_dotProduct_mulVec_pos hH fun x hx => by`. Establish `h1` using `hpos (star x) (by simpa using hx)`. Rewrite `h1` using `[hermForm, star_star]`. Conclude with `Complex.pos_iff.2 ⟨h1, (hH.im_star_dotProduct_mulVec_self x).symm⟩`. Use `set S := CFC.sqrt Hm with hS`.

Establish `hS0 : 0 ≤ S` using `CFC.sqrt_nonneg Hm`. Establish `hSH : S.IsHermitian` using `(nonneg_iff_posSemidef.1 hS0).isHermitian`. Establish `hSS : S * S = Hm` using `CFC.sqrt_mul_sqrt_self Hm hP.posSemidef.nonneg`. Establish `hform (z w : Fin g → ℂ) : ∑ i, (z ᵥ* S) i * conj ((w ᵥ* S) i) = hermForm Hm z w`. Establish `: star (w ᵥ* S) = S *ᵥ star w` using `by rw [star_vecMul, hSH.eq]`.

Rewrite using `[hermForm, ← hSS, ← mulVec_mulVec, dotProduct_mulVec, ← this]`. Both sides reduce to the same expression. Establish `hinj : Function.Injective (S.vecMulLinear)`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `z hz`.

Assume the negation of the conclusion as `h`. Use `hpos z h` as an intermediate fact. Rewrite `this` using `[← hform, show z ᵥ* S = 0 from hz]`. Simplify using `at this`. Use `⟨S.vecMulLinear.linearEquivOfInjective hinj rfl, hform, fun d hd z => ?_⟩` and prove the remaining obligations.

Establish `hc : Commute S (diagonal d)` using `hd.cfcₙ_nnreal _`. Establish `e (x : Fin g → ℂ) : (fun k => d k * x k) = x ᵥ* diagonal d`. Use extensionality with `k`. Simplify using `[vecMul_diagonal, mul_comm]`. Rewrite using `[e, e]`.

Express the relevant statement in the definitionally equal form `(z ᵥ* diagonal d) ᵥ* S = (z ᵥ* S) ᵥ* diagonal d`. Rewrite using `[vecMul_vecMul, vecMul_vecMul, hc.eq]`.
-/
theorem exists_root (Hm : Matrix (Fin g) (Fin g) ℂ) (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) :
    ∃ φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), (∀ z w, ∑ i, φ z i * conj (φ w i) = hermForm Hm z w) ∧
      ∀ d : Fin g → ℂ, Commute Hm (diagonal d) → ∀ z, φ (fun k => d k * z k) = fun k => d k * φ z k := by
  have hP : Hm.PosDef := PosDef.of_dotProduct_mulVec_pos hH fun x hx => by
    have h1 := hpos (star x) (by simpa using hx)
    rw [hermForm, star_star] at h1
    exact Complex.pos_iff.2 ⟨h1, (hH.im_star_dotProduct_mulVec_self x).symm⟩
  set S := CFC.sqrt Hm with hS
  have hS0 : 0 ≤ S := CFC.sqrt_nonneg Hm
  have hSH : S.IsHermitian := (nonneg_iff_posSemidef.1 hS0).isHermitian
  have hSS : S * S = Hm := CFC.sqrt_mul_sqrt_self Hm hP.posSemidef.nonneg
  have hform (z w : Fin g → ℂ) : ∑ i, (z ᵥ* S) i * conj ((w ᵥ* S) i) = hermForm Hm z w := by
    have : star (w ᵥ* S) = S *ᵥ star w := by rw [star_vecMul, hSH.eq]
    rw [hermForm, ← hSS, ← mulVec_mulVec, dotProduct_mulVec, ← this]
    rfl
  have hinj : Function.Injective (S.vecMulLinear) := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    by_contra h
    have := hpos z h
    rw [← hform, show z ᵥ* S = 0 from hz] at this
    simp at this
  refine ⟨S.vecMulLinear.linearEquivOfInjective hinj rfl, hform, fun d hd z => ?_⟩
  have hc : Commute S (diagonal d) := hd.cfcₙ_nnreal _
  have e (x : Fin g → ℂ) : (fun k => d k * x k) = x ᵥ* diagonal d := by
    ext k; simp [vecMul_diagonal, mul_comm]
  rw [e, e]
  change (z ᵥ* diagonal d) ᵥ* S = (z ᵥ* S) ᵥ* diagonal d
  rw [vecMul_vecMul, vecMul_vecMul, hc.eq]

/- English proof (translation)
Set `L : Submodule ℤ (Fin g → ℂ)` to `P.range.toIntSubmodule`. Use `haveI : DiscreteTopology L := hd`. Use `haveI : IsZLattice ℝ L := ⟨by rw [← hs]; rfl⟩`. Set `b` to `(Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L`. Establish `hc : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = 2 * g`.

Rewrite using `[← Module.finrank_eq_card_basis b]`. Simplify using `[Module.finrank_pi_fintype, mul_comm]`. Use `⟨b.reindex (Fintype.equivFinOfCardEq hc), fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[Module.Basis.range_reindex, Module.Basis.ofZLatticeBasis_span]`. Both sides reduce to the same expression.
-/
theorem exists_basis {A : Type} [AddCommGroup A] (P : A →+ (Fin g → ℂ)) (hd : DiscreteTopology P.range)
    (hs : Submodule.span ℝ (Set.range P) = ⊤) :
    ∃ b : Module.Basis (Fin (2 * g)) ℝ (Fin g → ℂ), ∀ y, y ∈ Submodule.span ℤ (Set.range b) ↔ ∃ a, P a = y := by
  let L : Submodule ℤ (Fin g → ℂ) := P.range.toIntSubmodule
  haveI : DiscreteTopology L := hd
  haveI : IsZLattice ℝ L := ⟨by rw [← hs]; rfl⟩
  let b := (Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L
  have hc : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = 2 * g := by
    rw [← Module.finrank_eq_card_basis b]
    simp [Module.finrank_pi_fintype, mul_comm]
  refine ⟨b.reindex (Fintype.equivFinOfCardEq hc), fun y => ?_⟩
  rw [Module.Basis.range_reindex, Module.Basis.ofZLatticeBasis_span]
  rfl

end LinAlg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

section Host

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.ImaginarySqrtEmbedding.embedding_sqrt_sq_and_conj`. Consider the case `exact _root_.GlobalTheory.ImaginarySqrtEmbedding.embedding_sqrt_sq_and_conj`. Consider the case `(apply _root_.GlobalTheory.ImaginarySqrtEmbedding.embedding_sqrt_sq_and_conj <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.ImaginarySqrtEmbedding.embedding_sqrt_sq_and_conj <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.ImaginarySqrtEmbedding.embedding_sqrt_sq_and_conj <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.ImaginarySqrtEmbedding.embedding_sqrt_sq_and_conj ..)`.
-/
theorem conj_rt (τ : E →+* ℂ) : τ (H.rt : E) ^ 2 = -(H.d : ℂ) ∧
    starRingEnd ℂ (τ (H.rt : E)) = -τ (H.rt : E) := by
  first
  | exact @_root_.GlobalTheory.ImaginarySqrtEmbedding.embedding_sqrt_sq_and_conj
  | exact _root_.GlobalTheory.ImaginarySqrtEmbedding.embedding_sqrt_sq_and_conj
  | (apply _root_.GlobalTheory.ImaginarySqrtEmbedding.embedding_sqrt_sq_and_conj <;> assumption)
  | (intros; apply _root_.GlobalTheory.ImaginarySqrtEmbedding.embedding_sqrt_sq_and_conj <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ImaginarySqrtEmbedding.embedding_sqrt_sq_and_conj <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ImaginarySqrtEmbedding.embedding_sqrt_sq_and_conj ..)

/- English proof (translation)
Take `⟨h1, h2⟩` from `conj_rt (H := H) τ`. Establish `h3 : H.rt0 ≠ -H.rt0` using `fun h => by`. Establish `h0 : H.rt0 = 0` using `by linear_combination h / 2`. Use `H.sqrt_neg_disc_sq` as an intermediate fact. Rewrite `this` using `[h0]`.

Conclude with `H.d_prime.ne_zero (by simpa using this)`. Simplify using `only [Datum.mult, ComplexEmbedding.conjugate_coe_eq, h2]`. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 (h1.trans H.sqrt_neg_disc_sq.symm) with h | h` into its components or cases. Rewrite using `[h, if_pos rfl, if_neg h3.symm]`. Rewrite using `[h, neg_neg, if_pos rfl, if_neg h3.symm, add_comm]`.
-/
theorem mult_add_mult_conj (D : Datum H) (τ : E →+* ℂ) :
    D.mult τ + D.mult (ComplexEmbedding.conjugate τ) = D.p + D.q := by
  obtain ⟨h1, h2⟩ := conj_rt (H := H) τ
  have h3 : H.rt0 ≠ -H.rt0 := fun h => by
    have h0 : H.rt0 = 0 := by linear_combination h / 2
    have := H.sqrt_neg_disc_sq
    rw [h0] at this
    exact H.d_prime.ne_zero (by simpa using this)
  simp only [Datum.mult, ComplexEmbedding.conjugate_coe_eq, h2]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (h1.trans H.sqrt_neg_disc_sq.symm) with h | h
  · rw [h, if_pos rfl, if_neg h3.symm]
  · rw [h, neg_neg, if_pos rfl, if_neg h3.symm, add_comm]

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[cc, IsCMField.complexEmbedding_complexConj]`. Establish `h` using `congrArg (τ.comp (algebraMap (𝓞 E) E)) H.two_weight_eq_one_add_root`. Rewrite `h` using `[map_mul, map_add, map_one, map_ofNat]`.

Express the relevant statement in the definitionally equal form `2 * τ (H.w0 : E) = 1 + τ (H.rt : E) at h`. Establish `h'` using `congrArg (starRingEnd ℂ) h`. Rewrite `h'` using `[map_mul, map_add, map_one, map_ofNat, (conj_rt (H := H) τ).2]`. Establish `: τ ((1 - H.w0 : 𝓞 E) : E) = 1 - τ (H.w0 : E)` using `by simp`. Rewrite using `[this]`.

Take the linear combination `(-h - h') / 2`.
-/
theorem coe_one_sub_w0 : ((1 - H.w0 : 𝓞 E) : E) = cc (H.w0 : E) := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [cc, IsCMField.complexEmbedding_complexConj]
  have h := congrArg (τ.comp (algebraMap (𝓞 E) E)) H.two_weight_eq_one_add_root
  rw [map_mul, map_add, map_one, map_ofNat] at h
  change 2 * τ (H.w0 : E) = 1 + τ (H.rt : E) at h
  have h' := congrArg (starRingEnd ℂ) h
  rw [map_mul, map_add, map_one, map_ofNat, (conj_rt (H := H) τ).2] at h'
  have : τ ((1 - H.w0 : 𝓞 E) : E) = 1 - τ (H.w0 : E) := by simp
  rw [this]
  linear_combination (-h - h') / 2

/- English proof (translation)
Establish `hc (τ : E →+* ℂ) : Nat.card {i // ty i = τ} = D.mult τ`. Unfold `Datum.mult`. Use `split_ifs with h`. Conclude with `(hty τ).1 h`. Conclude with `(hty τ).2 h`.

Use `⟨(Equiv.sigmaCongrRight fun τ => (Finite.equivFinOfCardEq (hc τ)).symm).trans (Equiv.sigmaFiberEquiv ty), fun i => ?_⟩` and prove the remaining obligations. Conclude with `((Finite.equivFinOfCardEq (hc i.1)).symm i.2).2`.
-/
theorem exists_idxEquiv (D : Datum H) {g : ℕ} {ty : Fin g → (E →+* ℂ)} (hty : IsTypeFn H D.p D.q ty) :
    ∃ e : I2.Idx D.mult ≃ Fin g, ∀ i, ty (e i) = i.1 := by
  have hc (τ : E →+* ℂ) : Nat.card {i // ty i = τ} = D.mult τ := by
    unfold Datum.mult
    split_ifs with h
    · exact (hty τ).1 h
    · exact (hty τ).2 h
  refine ⟨(Equiv.sigmaCongrRight fun τ => (Finite.equivFinOfCardEq (hc τ)).symm).trans
    (Equiv.sigmaFiberEquiv ty), fun i => ?_⟩
  exact ((Finite.equivFinOfCardEq (hc i.1)).symm i.2).2

end Host

open TorusAtAssembly in

/- English proof (translation)
Introduce `E _ _ _ H D g ty Pm Hm hty hP hH hpos hEF`. Take `⟨hlin, -, hdisc, hspan, -⟩` from `hP`. Take `⟨e, he⟩` from `exists_idxEquiv D hty`. Take `⟨φ, hφ, hφc⟩` from `exists_root Hm hH hpos`. Take `⟨b₀, hb₀⟩` from `exists_basis Pm hdisc hspan`.

Establish `hlin' (α : 𝓞 E) (a : D.La) : Pm (α • a) = fun k => ty k (α : E) * Pm a k` using `funext (hlin α a)`. Establish `hcomm (α : 𝓞 E) : Commute Hm (Matrix.diagonal fun k => ty k (α : E))`. Use `commute_of_im Hm _ _ hspan ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩ _ ⟨b, rfl⟩`. Establish `: (fun k => starRingEnd ℂ (ty k (α : E)) * Pm b k) = Pm (H.bar α • b)`.

Rewrite using `[hlin', H.bar_eq]`. Simplify using `only [IsCMField.complexEmbedding_complexConj]`. Rewrite using `[this, ← hlin', hEF, hEF, D.adj]`. Set `ψ : (Fin g → ℂ) ≃ₗ[ℂ] I2.Vsp D.mult` to `(φ.trans (LinearEquiv.funCongrLeft ℂ ℂ e)).trans (WithLp.linearEquiv 2 ℂ (I2.Idx D.mult → ℂ)).symm`. Establish `hψ (z : Fin g → ℂ) (i : I2.Idx D.mult) : ψ z i = φ z (e i)` using `rfl`.

Establish `hform (z w : Fin g → ℂ) : I2.Hf (ψ z) (ψ w) = hermForm Hm z w`. Rewrite using `[← hφ, I2.Hf]`. Conclude with `Fintype.sum_equiv e _ _ fun i => by rw [hψ, hψ]`. Establish `hact (α : 𝓞 E) (z : Fin g → ℂ) : ψ (fun k => ty k (α : E) * z k) = I2.act α (ψ z)`. Use extensionality with `i`.

Rewrite using `[hψ, hφc _ (hcomm α)]`. Express the relevant statement in the definitionally equal form `ty (e i) (α : E) * φ z (e i) = i.1 (α : E) * φ z (e i)`. Rewrite using `[he]`. Establish `hact' (α : 𝓞 E) (a : D.La) : I2.act α (ψ (Pm a)) = ψ (Pm (α • a))` using `by rw [hlin', hact]`. Establish `him (a b : D.La) : (I2.Hf (ψ (Pm a)) (ψ (Pm b))).im = D.EF a b` using `by rw [hform, hEF]`.

Establish `hcard : g = Fintype.card (I2.Idx D.mult)` using `by rw [Fintype.card_congr e, Fintype.card_fin]`. Set `Φ : (Fin g → ℂ) ≃ₗ[ℝ] I2.Vsp D.mult` to `ψ.restrictScalars ℝ`. Set `b : Module.Basis (Fin (2 * Fintype.card (I2.Idx D.mult))) ℝ (I2.Vsp D.mult)` to `(b₀.map Φ).reindex (finCongr (by rw [← hcard]))`. Establish `hlat : ∀ y, y ∈ I2.lat b ↔ ∃ a, ψ (Pm a) = y`. Introduce `y`.

Establish `h1 : I2.lat b = (Submodule.span ℤ (Set.range b₀)).map ((Φ : (Fin g → ℂ) →ₗ[ℝ] I2.Vsp D.mult).restrictScalars ℤ)`. Rewrite using `[Submodule.map_span, I2.lat, Module.Basis.range_reindex, ← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[h1, Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨z, hz, rfl⟩`. Take `⟨v, rfl⟩` from `(hb₀ z).1 hz`. Conclude with `⟨v, rfl⟩`. Introduce and unpack `⟨v, rfl⟩`. Conclude with `⟨_, (hb₀ _).2 ⟨v, rfl⟩, rfl⟩`.

Establish `stable : ∀ (α : 𝓞 E) (y : I2.Vsp D.mult), y ∈ I2.lat b → I2.act α y ∈ I2.lat b`. Introduce `α y hy`. Take `⟨v, rfl⟩` from `(hlat y).1 hy`. Conclude with `(hlat _).2 ⟨α • v, (hact' α v).symm⟩`. Establish `par : ∀ y ∈ I2.lat b, ∀ z ∈ I2.lat b, ∃ k : ℤ, (I2.Hf y (I2.act H.w0 z)).im - (I2.Hf y (I2.act (1 - H.w0) z)).im - (I2.Hf y z).im = 2 * k`.

Introduce `y hy z hz`. Take `⟨u, rfl⟩` from `(hlat y).1 hy`. Take `⟨v, rfl⟩` from `(hlat z).1 hz`. Use `⟨D.EF u (H.w0 • v) - D.EF u v, ?_⟩` and prove the remaining obligations. Rewrite using `[hact', hact', him, him, him, sub_smul, one_smul, map_sub]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `perfect : ∀ χ : I2.lat b →+ ℤ, ∃ y ∈ I2.lat b, ∀ z : I2.lat b, (χ z : ℝ) = (I2.Hf y (z : I2.Vsp D.mult)).im`. Introduce `χ`. Set `j : D.La →+ I2.lat b` to `{ toFun := fun v => ⟨ψ (Pm v), (hlat _).2 ⟨v, rfl⟩⟩ map_zero' := by ext1; simp map_add' := fun u v => by ext1; simp }`.

Take `⟨u, hu⟩` from `D.unimod.2 (χ.comp j).toIntLinearMap`. Use `⟨ψ (Pm u), (hlat _).2 ⟨u, rfl⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨z, hz⟩`. Take `⟨v, rfl⟩` from `(hlat z).1 hz`. Rewrite using `[him, hu]`.

Both sides reduce to the same expression. Use `⟨torus (D.p + D.q) (mult_add_mult_conj D) coe_one_sub_w0 stable par perfect, ψ, rfl, fun _ => rfl, hform, hlat, hact, fun a => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `sgnFloor (I2.Hf (ψ (Pm a)) (I2.act H.w0 (ψ (Pm a)))).im = _`. Rewrite using `[hact', him, sgnFloor, Int.floor_intCast]`.
-/
theorem exists_torusOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Pm : D.La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), IsTypeFn H D.p D.q ty → IsPeriod D ty Pm → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ a b, (hermForm Hm (Pm a) (Pm b)).im = D.EF a b) → ∃ (T : I2.PT E) (ψ : (Fin g → ℂ) ≃ₗ[ℂ] I2.Vsp T.dim), IsTorusOf D ty Pm Hm T ψ := by
  intro E _ _ _ H D g ty Pm Hm hty hP hH hpos hEF
  obtain ⟨hlin, -, hdisc, hspan, -⟩ := hP
  obtain ⟨e, he⟩ := exists_idxEquiv D hty
  obtain ⟨φ, hφ, hφc⟩ := exists_root Hm hH hpos
  obtain ⟨b₀, hb₀⟩ := exists_basis Pm hdisc hspan
  have hlin' (α : 𝓞 E) (a : D.La) : Pm (α • a) = fun k => ty k (α : E) * Pm a k := funext (hlin α a)
  have hcomm (α : 𝓞 E) : Commute Hm (Matrix.diagonal fun k => ty k (α : E)) := by
    refine commute_of_im Hm _ _ hspan ?_
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    have : (fun k => starRingEnd ℂ (ty k (α : E)) * Pm b k) = Pm (H.bar α • b) := by
      rw [hlin', H.bar_eq]
      simp only [IsCMField.complexEmbedding_complexConj]
    rw [this, ← hlin', hEF, hEF, D.adj]
  let ψ : (Fin g → ℂ) ≃ₗ[ℂ] I2.Vsp D.mult :=
    (φ.trans (LinearEquiv.funCongrLeft ℂ ℂ e)).trans (WithLp.linearEquiv 2 ℂ (I2.Idx D.mult → ℂ)).symm
  have hψ (z : Fin g → ℂ) (i : I2.Idx D.mult) : ψ z i = φ z (e i) := rfl
  have hform (z w : Fin g → ℂ) : I2.Hf (ψ z) (ψ w) = hermForm Hm z w := by
    rw [← hφ, I2.Hf]
    exact Fintype.sum_equiv e _ _ fun i => by rw [hψ, hψ]
  have hact (α : 𝓞 E) (z : Fin g → ℂ) : ψ (fun k => ty k (α : E) * z k) = I2.act α (ψ z) := by
    ext i
    rw [hψ, hφc _ (hcomm α)]
    change ty (e i) (α : E) * φ z (e i) = i.1 (α : E) * φ z (e i)
    rw [he]
  have hact' (α : 𝓞 E) (a : D.La) : I2.act α (ψ (Pm a)) = ψ (Pm (α • a)) := by rw [hlin', hact]
  have him (a b : D.La) : (I2.Hf (ψ (Pm a)) (ψ (Pm b))).im = D.EF a b := by rw [hform, hEF]
  have hcard : g = Fintype.card (I2.Idx D.mult) := by rw [Fintype.card_congr e, Fintype.card_fin]
  let Φ : (Fin g → ℂ) ≃ₗ[ℝ] I2.Vsp D.mult := ψ.restrictScalars ℝ
  let b : Module.Basis (Fin (2 * Fintype.card (I2.Idx D.mult))) ℝ (I2.Vsp D.mult) :=
    (b₀.map Φ).reindex (finCongr (by rw [← hcard]))
  have hlat : ∀ y, y ∈ I2.lat b ↔ ∃ a, ψ (Pm a) = y := by
    intro y
    have h1 : I2.lat b = (Submodule.span ℤ (Set.range b₀)).map
        ((Φ : (Fin g → ℂ) →ₗ[ℝ] I2.Vsp D.mult).restrictScalars ℤ) := by
      rw [Submodule.map_span, I2.lat, Module.Basis.range_reindex, ← Set.range_comp]
      rfl
    rw [h1, Submodule.mem_map]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨v, rfl⟩ := (hb₀ z).1 hz
      exact ⟨v, rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨_, (hb₀ _).2 ⟨v, rfl⟩, rfl⟩
  have stable : ∀ (α : 𝓞 E) (y : I2.Vsp D.mult), y ∈ I2.lat b → I2.act α y ∈ I2.lat b := by
    intro α y hy
    obtain ⟨v, rfl⟩ := (hlat y).1 hy
    exact (hlat _).2 ⟨α • v, (hact' α v).symm⟩
  have par : ∀ y ∈ I2.lat b, ∀ z ∈ I2.lat b, ∃ k : ℤ,
      (I2.Hf y (I2.act H.w0 z)).im - (I2.Hf y (I2.act (1 - H.w0) z)).im - (I2.Hf y z).im = 2 * k := by
    intro y hy z hz
    obtain ⟨u, rfl⟩ := (hlat y).1 hy
    obtain ⟨v, rfl⟩ := (hlat z).1 hz
    refine ⟨D.EF u (H.w0 • v) - D.EF u v, ?_⟩
    rw [hact', hact', him, him, him, sub_smul, one_smul, map_sub]
    push_cast
    ring
  have perfect : ∀ χ : I2.lat b →+ ℤ, ∃ y ∈ I2.lat b, ∀ z : I2.lat b,
      (χ z : ℝ) = (I2.Hf y (z : I2.Vsp D.mult)).im := by
    intro χ
    let j : D.La →+ I2.lat b :=
      { toFun := fun v => ⟨ψ (Pm v), (hlat _).2 ⟨v, rfl⟩⟩
        map_zero' := by ext1; simp
        map_add' := fun u v => by ext1; simp }
    obtain ⟨u, hu⟩ := D.unimod.2 (χ.comp j).toIntLinearMap
    refine ⟨ψ (Pm u), (hlat _).2 ⟨u, rfl⟩, ?_⟩
    rintro ⟨z, hz⟩
    obtain ⟨v, rfl⟩ := (hlat z).1 hz
    rw [him, hu]
    rfl
  refine ⟨torus (D.p + D.q) (mult_add_mult_conj D) coe_one_sub_w0 stable par perfect, ψ, rfl, fun _ => rfl,
    hform, hlat, hact, fun a => ?_⟩
  change sgnFloor (I2.Hf (ψ (Pm a)) (I2.act H.w0 (ψ (Pm a)))).im = _
  rw [hact', him, sgnFloor, Int.floor_intCast]

end GlobalTheory.PeriodTorus
