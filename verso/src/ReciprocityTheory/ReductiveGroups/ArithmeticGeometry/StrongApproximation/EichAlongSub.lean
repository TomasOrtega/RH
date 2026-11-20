import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.StrongApproximation.EichPreserves

namespace ReciprocityTheory.ChartRestriction.G.SA

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R] {σ : R →+* R}
  {J : Matrix ι ι R}

variable (σ J) in

def tor (e f : ι → R) (l m : R) : Matrix ι ι R :=
  1 + (l - 1) • vecMulVec e (J *ᵥ (σ ∘ f)) + (m - 1) • vecMulVec f (J *ᵥ (σ ∘ e))

variable (σ J) in
/- English proof (translation)
Establish `vmvs : ∀ (s : R) (a w z : ι → R), (s • vecMulVec a w) *ᵥ z = (s * (w ⬝ᵥ z)) • a`. Introduce `s a w z`. Use extensionality with `i`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.vecMulVec, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl (fun j _ => by ring)`.

Unfold `tor`. Rewrite using `[Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, vmvs, vmvs, ← hf_eq, ← hf_eq]`.
-/
theorem tor_mulVec (e f : ι → R) (l m : R) (x : ι → R) :
    tor σ J e f l m *ᵥ x = x + ((l - 1) * hf σ J x f) • e + ((m - 1) * hf σ J x e) • f := by
  have vmvs : ∀ (s : R) (a w z : ι → R), (s • vecMulVec a w) *ᵥ z = (s * (w ⬝ᵥ z)) • a := by
    intro s a w z
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.vecMulVec, Matrix.of_apply,
      Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  unfold tor
  rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, vmvs, vmvs, ← hf_eq, ← hf_eq]

section
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ)
include hσ hJ

/- English proof (translation)
Apply `Matrix.ext_of_mulVec_single` to reduce the goal to its premises. Introduce `j`. Rewrite using `[Matrix.one_mulVec, ← Matrix.mulVec_mulVec]`. Establish `heu : hf σ J e u = 0`. Rewrite using `[← hf_symm (hσ := hσ) (hJ := hJ) (x := u) (y := e), hue, map_zero]`.

Rewrite using `[eich_mulVec (σ := σ) (J := J) e u c (Pi.single j 1)]`. Use `set x : ι → R := Pi.single j 1`. Use `set α := hf σ J x e`. Use `set β := hf σ J x u`. Use `set y := x + α • u - β • e + (c * α) • e with hy`.

Establish `h1 : hf σ J y e = α`. Rewrite using `[hy, hf_add_left, hf_sub_left, hf_add_left, hf_smul_left, hf_smul_left, hf_smul_left, hue, he]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : hf σ J y u = β + α * hf σ J u u`. Rewrite using `[hy, hf_add_left, hf_sub_left, hf_add_left, hf_smul_left, hf_smul_left, hf_smul_left, heu]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[eich_mulVec (σ := σ) (J := J) e (-u) (σ c) y, hf_neg_right, h1, h2]`. Use extensionality with `i`. Simplify using `only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hy]`. Take the linear combination `(α * e i) * hc`.
-/
theorem eich_inv {e u : ι → R} {c : R} (he : hf σ J e e = 0) (hue : hf σ J u e = 0)
    (hc : c + σ c + hf σ J u u = 0) : eich σ J e (-u) (σ c) * eich σ J e u c = 1 := by
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
  have heu : hf σ J e u = 0 := by
    rw [← hf_symm (hσ := hσ) (hJ := hJ) (x := u) (y := e), hue, map_zero]
  rw [eich_mulVec (σ := σ) (J := J) e u c (Pi.single j 1)]
  set x : ι → R := Pi.single j 1
  set α := hf σ J x e
  set β := hf σ J x u
  set y := x + α • u - β • e + (c * α) • e with hy
  have h1 : hf σ J y e = α := by
    rw [hy, hf_add_left, hf_sub_left, hf_add_left, hf_smul_left, hf_smul_left, hf_smul_left, hue, he]
    ring
  have h2 : hf σ J y u = β + α * hf σ J u u := by
    rw [hy, hf_add_left, hf_sub_left, hf_add_left, hf_smul_left, hf_smul_left, hf_smul_left, heu]
    ring
  rw [eich_mulVec (σ := σ) (J := J) e (-u) (σ c) y, hf_neg_right, h1, h2]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hy]
  linear_combination (α * e i) * hc

/- English proof (translation)
Introduce `M hM`. Take `⟨u, c, hue, -, hc, rfl⟩` from `hM`. Rewrite using `[mem_SU_iff]`. Conclude with `⟨eich_det (hσ := hσ) (hJ := hJ) he hue, eich_preserves (hσ := hσ) (hJ := hJ) he hue hc⟩`.
-/
theorem eichAlong_sub {e f : ι → R} (he : hf σ J e e = 0) : eichAlong σ J e f ⊆ SU σ J := by
  intro M hM
  obtain ⟨u, c, hue, -, hc, rfl⟩ := hM
  rw [mem_SU_iff]
  exact ⟨eich_det (hσ := hσ) (hJ := hJ) he hue, eich_preserves (hσ := hσ) (hJ := hJ) he hue hc⟩

/- English proof (translation)
Take `⟨u, c, hue, huf, hc, rfl⟩` from `hM`. Establish `hue' : hf σ J (-u) e = 0` using `by rw [hf_neg_left, hue, neg_zero]`. Establish `huf' : hf σ J (-u) f = 0` using `by rw [hf_neg_left, huf, neg_zero]`. Establish `hc' : σ c + σ (σ c) + hf σ J (-u) (-u) = 0`. Rewrite using `[hσ, hf_neg_left, hf_neg_right, neg_neg]`.

Take the linear combination `hc`. Use `⟨eich σ J e (-u) (σ c), ⟨-u, σ c, hue', huf', hc', rfl⟩, eich_inv hσ hJ he hue hc, ?_⟩` and prove the remaining obligations. Establish `h` using `eich_inv hσ hJ he hue' hc'`. Rewrite `h` using `[neg_neg, hσ]`. Then use the resulting hypothesis.
-/
theorem eichAlong_inv {e f : ι → R} (he : hf σ J e e = 0) {M : Matrix ι ι R}
    (hM : M ∈ eichAlong σ J e f) : ∃ M' ∈ eichAlong σ J e f, M' * M = 1 ∧ M * M' = 1 := by
  obtain ⟨u, c, hue, huf, hc, rfl⟩ := hM
  have hue' : hf σ J (-u) e = 0 := by rw [hf_neg_left, hue, neg_zero]
  have huf' : hf σ J (-u) f = 0 := by rw [hf_neg_left, huf, neg_zero]
  have hc' : σ c + σ (σ c) + hf σ J (-u) (-u) = 0 := by
    rw [hσ, hf_neg_left, hf_neg_right, neg_neg]
    linear_combination hc
  refine ⟨eich σ J e (-u) (σ c), ⟨-u, σ c, hue', huf', hc', rfl⟩, eich_inv hσ hJ he hue hc, ?_⟩
  have h := eich_inv hσ hJ he hue' hc'
  rwa [neg_neg, hσ] at h

variable {e f : ι → R} (he : hf σ J e e = 0) (hff : hf σ J f f = 0)
include he hff

/- English proof (translation)
The claim follows from `Set.union_subset (eichAlong_sub hσ hJ he) (eichAlong_sub hσ hJ hff)`.
-/
theorem eichSet_sub : eichSet σ J e f ⊆ SU σ J :=
  Set.union_subset (eichAlong_sub hσ hJ he) (eichAlong_sub hσ hJ hff)

/- English proof (translation)
Introduce `M hM`. Rewrite `hM` using `[SetLike.mem_coe]`. Proceed by induction on `hM using Submonoid.closure_induction with`. Consider the case `mem x hx => exact eichSet_sub hσ hJ he hff hx`. Consider the case `one`.

Rewrite using `[mem_SU_iff]`. Conclude with `⟨Matrix.det_one, fun x y => by simp⟩`. Consider the case `mul x y _ _ hx hy`. Rewrite `hx`, `hy`, the goal using `[mem_SU_iff]`. Use `⟨by rw [Matrix.det_mul, hx.1, hy.1, one_mul], fun a b => ?_⟩` and prove the remaining obligations.

Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hx.2, hy.2]`.
-/
theorem closure_sub : (Submonoid.closure (eichSet σ J e f) : Set (Matrix ι ι R)) ⊆ SU σ J := by
  intro M hM
  rw [SetLike.mem_coe] at hM
  induction hM using Submonoid.closure_induction with
  | mem x hx => exact eichSet_sub hσ hJ he hff hx
  | one =>
    rw [mem_SU_iff]
    exact ⟨Matrix.det_one, fun x y => by simp⟩
  | mul x y _ _ hx hy =>
    rw [mem_SU_iff] at hx hy ⊢
    refine ⟨by rw [Matrix.det_mul, hx.1, hy.1, one_mul], fun a b => ?_⟩
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hx.2, hy.2]

/- English proof (translation)
Proceed by induction on `hM using Submonoid.closure_induction with`. Consider the case `mem x hx`. Break down `hx with hx | hx` into its components or cases. Take `⟨M', hM', h1, h2⟩` from `eichAlong_inv hσ hJ he hx`. Conclude with `⟨M', Submonoid.subset_closure (Or.inl hM'), h1, h2⟩`.

Take `⟨M', hM', h1, h2⟩` from `eichAlong_inv hσ hJ hff hx`. Conclude with `⟨M', Submonoid.subset_closure (Or.inr hM'), h1, h2⟩`. Consider the case `one => exact ⟨1, Submonoid.one_mem _, mul_one 1, mul_one 1⟩`. Consider the case `mul x y _ _ hx hy`. Take `⟨x', hx'm, hx1, hx2⟩` from `hx`.

Take `⟨y', hy'm, hy1, hy2⟩` from `hy`. Use `⟨y' * x', Submonoid.mul_mem _ hy'm hx'm, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_assoc, ← mul_assoc x' x y, hx1, one_mul, hy1]`. Rewrite using `[mul_assoc, ← mul_assoc y y' x', hy2, one_mul, hx2]`.
-/
theorem closure_inv {M : Matrix ι ι R} (hM : M ∈ Submonoid.closure (eichSet σ J e f)) :
    ∃ M' ∈ Submonoid.closure (eichSet σ J e f), M' * M = 1 ∧ M * M' = 1 := by
  induction hM using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · obtain ⟨M', hM', h1, h2⟩ := eichAlong_inv hσ hJ he hx
      exact ⟨M', Submonoid.subset_closure (Or.inl hM'), h1, h2⟩
    · obtain ⟨M', hM', h1, h2⟩ := eichAlong_inv hσ hJ hff hx
      exact ⟨M', Submonoid.subset_closure (Or.inr hM'), h1, h2⟩
  | one => exact ⟨1, Submonoid.one_mem _, mul_one 1, mul_one 1⟩
  | mul x y _ _ hx hy =>
    obtain ⟨x', hx'm, hx1, hx2⟩ := hx
    obtain ⟨y', hy'm, hy1, hy2⟩ := hy
    refine ⟨y' * x', Submonoid.mul_mem _ hy'm hx'm, ?_, ?_⟩
    · rw [mul_assoc, ← mul_assoc x' x y, hx1, one_mul, hy1]
    · rw [mul_assoc, ← mul_assoc y y' x', hy2, one_mul, hx2]

variable (hef : hf σ J e f = 1)
include hef

/- English proof (translation)
Rewrite using `[← hf_symm (hσ := hσ) (hJ := hJ) (x := e) (y := f), hef, map_one]`.
-/
theorem hf_fe : hf σ J f e = 1 := by
  rw [← hf_symm (hσ := hσ) (hJ := hJ) (x := e) (y := f), hef, map_one]

/- English proof (translation)
Rewrite using `[tor_mulVec σ J e f l m x, tor_mulVec σ J e f l m y, hf_expand (hσ := hσ) (hJ := hJ), he, hff, hef, hf_fe hσ hJ he hff hef]`. Establish `h2 : l * σ m = 1`. Establish `h3` using `congrArg σ hlm`. Rewrite `h3` using `[map_mul, hσ, map_one]`. Take the linear combination `h3`.

Simplify using `only [map_mul, map_sub, map_one]`. Take the linear combination `(σ (hf σ J y f) * hf σ J x e) * hlm + (σ (hf σ J y e) * hf σ J x f) * h2`.
-/
theorem tor_preserves {l m : R} (hlm : m * σ l = 1) (x y : ι → R) :
    hf σ J (tor σ J e f l m *ᵥ x) (tor σ J e f l m *ᵥ y) = hf σ J x y := by
  rw [tor_mulVec σ J e f l m x, tor_mulVec σ J e f l m y, hf_expand (hσ := hσ) (hJ := hJ), he, hff, hef,
    hf_fe hσ hJ he hff hef]
  have h2 : l * σ m = 1 := by
    have h3 := congrArg σ hlm
    rw [map_mul, hσ, map_one] at h3
    linear_combination h3
  simp only [map_mul, map_sub, map_one]
  linear_combination (σ (hf σ J y f) * hf σ J x e) * hlm + (σ (hf σ J y e) * hf σ J x f) * h2

end

end ReciprocityTheory.ChartRestriction.G.SA
