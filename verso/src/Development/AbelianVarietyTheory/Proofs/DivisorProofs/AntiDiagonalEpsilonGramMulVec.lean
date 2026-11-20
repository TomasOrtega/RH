import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChiGrid.SumDual

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E]

/- English proof (translation)
Simplify using `only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]`.
-/
theorem sum_eq_dot {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    ∑ i, ∑ j, star (x i) * G i j * y j = star x ⬝ᵥ G *ᵥ y := by
  simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]

omit [NumberField E] [StarRing E] in
/- English proof (translation)
Simplify using `only [mulVec, dotProduct]`. Rewrite using `[Finset.sum_eq_single p.rev]`. Use `p.2` as an intermediate fact. Simplify using `only [antiDiagonalSignGramMatrix, Fin.val_rev]`. Rewrite using `[if_pos (by omega)]`.

Introduce `q _ hq`. Use `p.2` as an intermediate fact. Simplify using `only [antiDiagonalSignGramMatrix]`. Rewrite using `[if_neg, zero_mul]`. Introduce `h`.

Conclude with `hq (Fin.ext (by rw [Fin.val_rev]; omega))`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem antiDiagonalEpsilonGram_mulVec {c : ℕ} (ε : E) (u : Fin c → E) (p : Fin c) :
    (antiDiagonalSignGramMatrix c ε *ᵥ u) p = (if p = p.rev then ε else 1) * u p.rev := by
  simp only [mulVec, dotProduct]
  rw [Finset.sum_eq_single p.rev]
  · have := p.2
    simp only [antiDiagonalSignGramMatrix, Fin.val_rev]
    rw [if_pos (by omega)]
  · intro q _ hq
    have := p.2
    simp only [antiDiagonalSignGramMatrix]
    rw [if_neg, zero_mul]
    intro h
    exact hq (Fin.ext (by rw [Fin.val_rev]; omega))
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Use extensionality with `i j`. Conclude with `S.herm.eq _ _`.
-/
theorem gram_herm (S : HSpace E) : S.gramᴴ = S.gram := by
  ext i j
  exact S.herm.eq _ _

/- English proof (translation)
Rewrite using `[← sum_eq_dot]`. Use `conv_lhs => rw [← S.frame.sum_repr x, ← S.frame.sum_repr y]`. Simplify using `only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Simplify using `only [RingHom.id_apply, Module.Basis.equivFun_apply, HSpace.gram]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hT_eq (S : HSpace E) (x y : S.V) :
    S.hT x y = star (S.frame.equivFun x) ⬝ᵥ S.gram *ᵥ S.frame.equivFun y := by
  rw [← sum_eq_dot]
  conv_lhs => rw [← S.frame.sum_repr x, ← S.frame.sum_repr y]
  simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [RingHom.id_apply, Module.Basis.equivFun_apply, HSpace.gram]
  ring

/- English proof (translation)
Take `⟨y, rfl⟩` from `S.frame.equivFun.surjective y`. Rewrite using `[S.nondeg.2 y fun x => by rw [hT_eq, h, dotProduct_zero], map_zero]`.
-/
theorem gram_inj (S : HSpace E) (y : Fin S.rank → E) (h : S.gram *ᵥ y = 0) : y = 0 := by
  obtain ⟨y, rfl⟩ := S.frame.equivFun.surjective y
  rw [S.nondeg.2 y fun x => by rw [hT_eq, h, dotProduct_zero], map_zero]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[HSpace.gram, ← h, hT_eq, Matrix.mul_assoc]`. Simplify using `only [Matrix.mul_apply, dotProduct, mulVec, conjTranspose_apply, LinearMap.toMatrix_apply, Pi.star_apply, Module.Basis.equivFun_apply]`.
-/
theorem gram_isom (A B : HSpace E) (ι : A.V →ₗ[E] B.V) (h : HSpace.IsIsomEmb A B ι) :
    (LinearMap.toMatrix A.frame B.frame ι)ᴴ * B.gram * LinearMap.toMatrix A.frame B.frame ι = A.gram := by
  ext i j
  rw [HSpace.gram, ← h, hT_eq, Matrix.mul_assoc]
  simp only [Matrix.mul_apply, dotProduct, mulVec, conjTranspose_apply, LinearMap.toMatrix_apply, Pi.star_apply,
    Module.Basis.equivFun_apply]

/- English proof (translation)
Establish `h2' : aᴴ * G * M = 0`. Use `congrArg conjTranspose h2` as an intermediate fact. Rewrite `this` using `[conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hG, conjTranspose_zero, ← Matrix.mul_assoc]`. Then use the resulting hypothesis. Establish `eM : ∀ y u, Mᴴ *ᵥ G *ᵥ (M *ᵥ y + a *ᵥ u) = J *ᵥ y` using `fun y u => by`. Simplify using `only [mulVec_add, mulVec_mulVec, ← Matrix.mul_assoc, h1, h2, zero_mulVec, add_zero]`.

Establish `ea : ∀ y u, aᴴ *ᵥ G *ᵥ (M *ᵥ y + a *ᵥ u) = antiDiagonalSignGramMatrix c ε *ᵥ u` using `fun y u => by`. Simplify using `only [mulVec_add, mulVec_mulVec, ← Matrix.mul_assoc, h2', h3, zero_mulVec, zero_add]`. Establish `key : ∀ x v y u, ∑ i, ∑ j, star ((M *ᵥ x + a *ᵥ v) i) * G i j * (M *ᵥ y + a *ᵥ u) j = (∑ i, ∑ j, star (x i) * J i j * y j) + ∑ p, (if p = p.rev then ε else 1) * (star (v p) * u p.rev)`. Introduce `x v y u`. Rewrite using `[sum_eq_dot, sum_eq_dot, star_add, add_dotProduct, star_mulVec, star_mulVec, ← dotProduct_mulVec, ← dotProduct_mulVec, eM, ea]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[antiDiagonalEpsilonGram_mulVec, Pi.star_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsg : ∀ p : Fin c, ∃ e : 𝓞 E, (e : E) = (if p = p.rev then ε else 1) ∧ e * e = 1` using `fun p => by split_ifs`.

Break down `hε with rfl | rfl` into its components or cases. Conclude with `⟨1, rfl, by simp⟩`. Conclude with `⟨-1, by simp, by simp⟩`. Conclude with `⟨1, rfl, by simp⟩`. Establish `hst : ∀ z : E, (∃ b : 𝓞 E, (b : E) = z) → ∃ b : 𝓞 E, (b : E) = star z`.

Introduce and unpack `_ ⟨b, rfl⟩`. Conclude with `⟨⟨star (b : E), hs _ b.isIntegral_coe⟩, rfl⟩`. Set `f : ((Fin k → E) × (Fin c → E)) →ₗ[E] (Fin n → E)` to `M.mulVecLin.coprod a.mulVecLin`. Establish `hf : ∀ y u, f (y, u) = M *ᵥ y + a *ᵥ u` using `fun _ _ => rfl`. Establish `finj : Function.Injective f`.

Use `(injective_iff_map_eq_zero f).2 ?_` and prove the remaining obligations. Introduce and unpack `⟨y, u⟩ h`. Rewrite `h` using `[hf]`. Establish `e1` using `eM y u`. Establish `e2` using `ea y u`.

Rewrite `e1`, `e2` using `[h, mulVec_zero, mulVec_zero]`. Use `Prod.ext (hJ y e1.symm) (funext fun p => ?_)` and prove the remaining obligations. Establish `e3` using `congrFun e2 p.rev`. Take `⟨e, he, hee⟩` from `hsg p.rev`. Rewrite `e3` using `[antiDiagonalEpsilonGram_mulVec, ← he, Fin.rev_rev]`.

Establish `he0 : (e : E) ≠ 0`. Introduce `h0`. Establish `: e = 0` using `by exact_mod_cast h0`. Rewrite `hee` using `[this]`. Simplify using `at hee`.

Conclude with `(mul_eq_zero.1 e3.symm).resolve_left he0`. Establish `fsur : Function.Surjective f` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hr])).1 finj`. Use `⟨⟨?_, ?_⟩, fun y' => ⟨?_, fun h => ?_⟩⟩` and prove the remaining obligations. Establish `: L = (Λ.prod (Submodule.pi Set.univ fun p => (𝔟 p : Submodule (𝓞 E) E))).map (f.restrictScalars (𝓞 E))`. Use extensionality with `x`.

Rewrite using `[hL, Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, u, hu, rfl⟩`. Conclude with `⟨(y, u), ⟨hy, fun p _ => hu p⟩, rfl⟩`. Introduce and unpack `⟨⟨y, u⟩, ⟨hy, hu⟩, rfl⟩`.

Conclude with `⟨y, hy, u, fun p => hu p trivial, rfl⟩`. Rewrite using `[this]`. Conclude with `(hΛ.fg.prod (Submodule.fg_pi fun p => FractionalIdeal.fg_of_isNoetherianRing le_rfl _)).map _`. Rewrite using `[eq_top_iff]`. Introduce and unpack `y -`.

Take `⟨⟨y, u⟩, rfl⟩` from `fsur y`. Rewrite using `[hf]`. Use `Submodule.add_mem _ ?_ ?_` and prove the remaining obligations. Establish `hy : y ∈ Submodule.span E (Λ : Set (Fin k → E))` using `by rw [hΛ.span_eq_top]; trivial`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem x hx => exact Submodule.subset_span ((hL _).2 ⟨x, hx, 0, fun p => (𝔟 p).zero_mem, by simp⟩)`. Consider the case `zero => simp`. Consider the case `add x z _ _ hx hz => rw [mulVec_add]`. Conclude with `Submodule.add_mem _ hx hz`. Consider the case `smul r x _ hx => rw [mulVec_smul]`.

Conclude with `Submodule.smul_mem _ r hx`. Rewrite using `[← Finset.univ_sum_single u, mulVec_sum]`. Use `Submodule.sum_mem _ fun p _ => ?_` and prove the remaining obligations. Take `⟨t, ht0, ht⟩` from `FractionalIdeal.exists_ne_zero_mem_isInteger (hb p)`. Establish `ht0' : algebraMap (𝓞 E) E t ≠ 0` using `by simpa using ht0`.

Establish `: (Pi.single p (u p) : Fin c → E) = (u p / algebraMap (𝓞 E) E t) • Pi.single p (algebraMap (𝓞 E) E t)`. Rewrite using `[← Pi.single_smul, smul_eq_mul, div_mul_cancel₀ _ ht0']`. Rewrite using `[this, mulVec_smul]`. Use `Submodule.smul_mem _ _ (Submodule.subset_span ((hL _).2 ⟨0, Λ.zero_mem, Pi.single p (algebraMap (𝓞 E) E t), fun q => ?_, by rw [mulVec_zero, zero_add]⟩))` and prove the remaining obligations. Distinguish the cases in `hq : q = p`.

Substitute `hq` using the available equality. Simplify using `using ht`. Rewrite using `[Pi.single_eq_of_ne hq]`. Conclude with `(𝔟 q).zero_mem`. Introduce `hy' x' hx'`.

Take `⟨y, hy, u, hu, rfl⟩` from `(hL _).1 hy'`. Take `⟨x, hx, v, hv, rfl⟩` from `(hL _).1 hx'`. Take `⟨b, hb1⟩` from `(hΛd y).1 hy x hx`. Establish `: ∀ p : Fin c, ∃ t : 𝓞 E, (t : E) = (if p = p.rev then ε else 1) * (star (v p) * u p.rev)` using `fun p => by`. Take `⟨e, he, -⟩` from `hsg p`.

Use `(FractionalIdeal.mem_inv_iff (hb p)).1 ((hd p _).1 (hu p.rev)) _ (hv p)` as an intermediate fact. Take `⟨t, ht⟩` from `hst _ ((FractionalIdeal.mem_one_iff _).1 this)`. Use `⟨e * t, ?_⟩` and prove the remaining obligations. Rewrite using `[← he, RingOfIntegers.coe_eq_algebraMap, map_mul]`. Use `congr 1`.

Use `ht.trans ?_` and prove the remaining obligations. Rewrite using `[star_mul, star_star]`. Use `choose t ht using this`. Use `⟨b + ∑ p, t p, ?_⟩` and prove the remaining obligations. Rewrite using `[key, ← hb1, ← Finset.sum_congr rfl fun p _ => ht p]`.

Simplify using the standard rewrite rules. Take `⟨⟨y, u⟩, rfl⟩` from `fsur y'`. Rewrite `h`, the goal using `[hf]`. Use `(hL _).2 ⟨y, (hΛd y).2 fun x hx => ?_, u, fun q => ?_, rfl⟩` and prove the remaining obligations. Use `h _ ((hL _).2 ⟨x, hx, 0, fun p => (𝔟 p).zero_mem, rfl⟩)` as an intermediate fact.

Rewrite `this` using `[key]`. Simplify using `using this`. Take `⟨p, rfl⟩` from `Fin.rev_surjective q`. Use `(hd p _).2 ((FractionalIdeal.mem_inv_iff (hb p)).2 fun s hs => ?_)` and prove the remaining obligations. Use `h _ ((hL _).2 ⟨0, Λ.zero_mem, Pi.single p s, fun q => by` as an intermediate fact.

Distinguish the cases in `hq : q = p`. Substitute `hq` using the available equality. Simplify using `using hs`. Rewrite using `[Pi.single_eq_of_ne hq]`. Conclude with `(𝔟 q).zero_mem, rfl⟩)`.

Rewrite `this` using `[key, Finset.sum_eq_single p (fun q _ hq => by rw [Pi.single_eq_of_ne hq]; simp) (fun h => absurd (Finset.mem_univ _) h)]`. Take `⟨b, hb1⟩` from `this`. Take `⟨e, he, hee⟩` from `hsg p`. Rewrite `hb1` using `[← he]`. Establish `hee' : (e : E) * e = 1` using `by exact_mod_cast congrArg (fun z : 𝓞 E => (z : E)) hee`.

Take `⟨t, ht⟩` from `hst (star s * u p.rev) ⟨e * b, by`. Rewrite using `[RingOfIntegers.coe_eq_algebraMap, map_mul]`. Express the relevant statement in the definitionally equal form `(e : E) * (b : E) = _`. Rewrite using `[hb1]`. Simplify using `only [Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero, zero_add, Pi.single_eq_same]`.

Rewrite using `[← mul_assoc, hee', one_mul]⟩`. Use `(FractionalIdeal.mem_one_iff _).2 ⟨t, ht.trans ?_⟩` and prove the remaining obligations. Rewrite using `[star_mul, star_star]`.
-/
theorem selfDual_sum {n k c : ℕ} (hs : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x))
    (G : Matrix (Fin n) (Fin n) E) (J : Matrix (Fin k) (Fin k) E) (M : Matrix (Fin n) (Fin k) E)
    (a : Matrix (Fin n) (Fin c) E) (ε : E) (hε : ε = 1 ∨ ε = -1) (hG : Gᴴ = G) (hJ : ∀ y, J *ᵥ y = 0 → y = 0)
    (h1 : Mᴴ * G * M = J) (h2 : Mᴴ * G * a = 0) (h3 : aᴴ * G * a = antiDiagonalSignGramMatrix c ε) (hr : k + c = n)
    (Λ : Submodule (𝓞 E) (Fin k → E)) (𝔟 : Fin c → FractionalIdeal (𝓞 E)⁰ E)
    (hΛ : Submodule.IsLattice E Λ)
    (hΛd : ∀ y, y ∈ Λ ↔ ∀ x ∈ Λ, ∃ b : 𝓞 E, (b : E) = ∑ i, ∑ j, star (x i) * J i j * y j)
    (hb : ∀ p, 𝔟 p ≠ 0) (hd : ∀ p x, x ∈ 𝔟 p.rev ↔ star x ∈ (𝔟 p)⁻¹)
    (L : Submodule (𝓞 E) (Fin n → E))
    (hL : ∀ x, x ∈ L ↔ ∃ y ∈ Λ, ∃ u : Fin c → E, (∀ p, u p ∈ 𝔟 p) ∧ x = M *ᵥ y + a *ᵥ u) :
    Submodule.IsLattice E L ∧
      ∀ y, y ∈ L ↔ ∀ x ∈ L, ∃ b : 𝓞 E, (b : E) = ∑ i, ∑ j, star (x i) * G i j * y j := by
  classical
  have h2' : aᴴ * G * M = 0 := by
    have := congrArg conjTranspose h2
    rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hG, conjTranspose_zero,
      ← Matrix.mul_assoc] at this
  have eM : ∀ y u, Mᴴ *ᵥ G *ᵥ (M *ᵥ y + a *ᵥ u) = J *ᵥ y := fun y u => by
    simp only [mulVec_add, mulVec_mulVec, ← Matrix.mul_assoc, h1, h2, zero_mulVec, add_zero]
  have ea : ∀ y u, aᴴ *ᵥ G *ᵥ (M *ᵥ y + a *ᵥ u) = antiDiagonalSignGramMatrix c ε *ᵥ u := fun y u => by
    simp only [mulVec_add, mulVec_mulVec, ← Matrix.mul_assoc, h2', h3, zero_mulVec, zero_add]
  have key : ∀ x v y u, ∑ i, ∑ j, star ((M *ᵥ x + a *ᵥ v) i) * G i j * (M *ᵥ y + a *ᵥ u) j =
      (∑ i, ∑ j, star (x i) * J i j * y j) + ∑ p, (if p = p.rev then ε else 1) * (star (v p) * u p.rev) := by
    intro x v y u
    rw [sum_eq_dot, sum_eq_dot, star_add, add_dotProduct, star_mulVec, star_mulVec, ← dotProduct_mulVec,
      ← dotProduct_mulVec, eM, ea]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [antiDiagonalEpsilonGram_mulVec, Pi.star_apply]; ring
  have hsg : ∀ p : Fin c, ∃ e : 𝓞 E, (e : E) = (if p = p.rev then ε else 1) ∧ e * e = 1 := fun p => by
    split_ifs
    · rcases hε with rfl | rfl
      · exact ⟨1, rfl, by simp⟩
      · exact ⟨-1, by simp, by simp⟩
    · exact ⟨1, rfl, by simp⟩
  have hst : ∀ z : E, (∃ b : 𝓞 E, (b : E) = z) → ∃ b : 𝓞 E, (b : E) = star z := by
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨star (b : E), hs _ b.isIntegral_coe⟩, rfl⟩
  let f : ((Fin k → E) × (Fin c → E)) →ₗ[E] (Fin n → E) := M.mulVecLin.coprod a.mulVecLin
  have hf : ∀ y u, f (y, u) = M *ᵥ y + a *ᵥ u := fun _ _ => rfl
  have finj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 ?_
    rintro ⟨y, u⟩ h
    rw [hf] at h
    have e1 := eM y u
    have e2 := ea y u
    rw [h, mulVec_zero, mulVec_zero] at e1 e2
    refine Prod.ext (hJ y e1.symm) (funext fun p => ?_)
    have e3 := congrFun e2 p.rev
    obtain ⟨e, he, hee⟩ := hsg p.rev
    rw [antiDiagonalEpsilonGram_mulVec, ← he, Fin.rev_rev] at e3
    have he0 : (e : E) ≠ 0 := by
      intro h0
      have : e = 0 := by exact_mod_cast h0
      rw [this] at hee; simp at hee
    exact (mul_eq_zero.1 e3.symm).resolve_left he0
  have fsur : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hr])).1 finj
  refine ⟨⟨?_, ?_⟩, fun y' => ⟨?_, fun h => ?_⟩⟩
  · have : L = (Λ.prod (Submodule.pi Set.univ fun p => (𝔟 p : Submodule (𝓞 E) E))).map (f.restrictScalars (𝓞 E)) := by
      ext x
      rw [hL, Submodule.mem_map]
      constructor
      · rintro ⟨y, hy, u, hu, rfl⟩
        exact ⟨(y, u), ⟨hy, fun p _ => hu p⟩, rfl⟩
      · rintro ⟨⟨y, u⟩, ⟨hy, hu⟩, rfl⟩
        exact ⟨y, hy, u, fun p => hu p trivial, rfl⟩
    rw [this]
    exact (hΛ.fg.prod (Submodule.fg_pi fun p => FractionalIdeal.fg_of_isNoetherianRing le_rfl _)).map _
  · rw [eq_top_iff]
    rintro y -
    obtain ⟨⟨y, u⟩, rfl⟩ := fsur y
    rw [hf]
    refine Submodule.add_mem _ ?_ ?_
    · have hy : y ∈ Submodule.span E (Λ : Set (Fin k → E)) := by rw [hΛ.span_eq_top]; trivial
      induction hy using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span ((hL _).2 ⟨x, hx, 0, fun p => (𝔟 p).zero_mem, by simp⟩)
      | zero => simp
      | add x z _ _ hx hz => rw [mulVec_add]; exact Submodule.add_mem _ hx hz
      | smul r x _ hx => rw [mulVec_smul]; exact Submodule.smul_mem _ r hx
    · rw [← Finset.univ_sum_single u, mulVec_sum]
      refine Submodule.sum_mem _ fun p _ => ?_
      obtain ⟨t, ht0, ht⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger (hb p)
      have ht0' : algebraMap (𝓞 E) E t ≠ 0 := by simpa using ht0
      have : (Pi.single p (u p) : Fin c → E) =
          (u p / algebraMap (𝓞 E) E t) • Pi.single p (algebraMap (𝓞 E) E t) := by
        rw [← Pi.single_smul, smul_eq_mul, div_mul_cancel₀ _ ht0']
      rw [this, mulVec_smul]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ((hL _).2 ⟨0, Λ.zero_mem, Pi.single p (algebraMap (𝓞 E) E t), fun q => ?_, by rw [mulVec_zero, zero_add]⟩))
      by_cases hq : q = p
      · subst hq; simpa using ht
      · rw [Pi.single_eq_of_ne hq]; exact (𝔟 q).zero_mem
  · intro hy' x' hx'
    obtain ⟨y, hy, u, hu, rfl⟩ := (hL _).1 hy'
    obtain ⟨x, hx, v, hv, rfl⟩ := (hL _).1 hx'
    obtain ⟨b, hb1⟩ := (hΛd y).1 hy x hx
    have : ∀ p : Fin c, ∃ t : 𝓞 E, (t : E) = (if p = p.rev then ε else 1) * (star (v p) * u p.rev) := fun p => by
      obtain ⟨e, he, -⟩ := hsg p
      have := (FractionalIdeal.mem_inv_iff (hb p)).1 ((hd p _).1 (hu p.rev)) _ (hv p)
      obtain ⟨t, ht⟩ := hst _ ((FractionalIdeal.mem_one_iff _).1 this)
      refine ⟨e * t, ?_⟩
      rw [← he, RingOfIntegers.coe_eq_algebraMap, map_mul]
      congr 1
      refine ht.trans ?_
      rw [star_mul, star_star]
    choose t ht using this
    refine ⟨b + ∑ p, t p, ?_⟩
    rw [key, ← hb1, ← Finset.sum_congr rfl fun p _ => ht p]
    simp
  · obtain ⟨⟨y, u⟩, rfl⟩ := fsur y'
    rw [hf] at h ⊢
    refine (hL _).2 ⟨y, (hΛd y).2 fun x hx => ?_, u, fun q => ?_, rfl⟩
    · have := h _ ((hL _).2 ⟨x, hx, 0, fun p => (𝔟 p).zero_mem, rfl⟩)
      rw [key] at this
      simpa using this
    · obtain ⟨p, rfl⟩ := Fin.rev_surjective q
      refine (hd p _).2 ((FractionalIdeal.mem_inv_iff (hb p)).2 fun s hs => ?_)
      have := h _ ((hL _).2 ⟨0, Λ.zero_mem, Pi.single p s, fun q => by
        by_cases hq : q = p
        · subst hq; simpa using hs
        · rw [Pi.single_eq_of_ne hq]; exact (𝔟 q).zero_mem, rfl⟩)
      rw [key, Finset.sum_eq_single p (fun q _ hq => by rw [Pi.single_eq_of_ne hq]; simp)
        (fun h => absurd (Finset.mem_univ _) h)] at this
      obtain ⟨b, hb1⟩ := this
      obtain ⟨e, he, hee⟩ := hsg p
      rw [← he] at hb1
      have hee' : (e : E) * e = 1 := by exact_mod_cast congrArg (fun z : 𝓞 E => (z : E)) hee
      obtain ⟨t, ht⟩ := hst (star s * u p.rev) ⟨e * b, by
        rw [RingOfIntegers.coe_eq_algebraMap, map_mul]
        change (e : E) * (b : E) = _
        rw [hb1]
        simp only [Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero, zero_add, Pi.single_eq_same]
        rw [← mul_assoc, hee', one_mul]⟩
      refine (FractionalIdeal.mem_one_iff _).2 ⟨t, ht.trans ?_⟩
      rw [star_mul, star_star]

end General

/- English proof (translation)
Introduce `D A B c ε d Λ 𝔟 hε hΛ hb hd`. Conclude with `selfDual_sum Formalism.BasicNotions.Examples₂.star_isIntegral B.gram A.gram (frameMat B A d.ι) d.a ε hε (gram_herm B) (gram_inj A) (gram_isom A B d.ι d.isom) d.perp d.gram d.rank Λ 𝔟 hΛ.1 hΛ.2 hb hd _ fun _ => Iff.rfl`.
-/
theorem isSelfDualC_lat : ∀ (D : D7) (A B : HSp D) (c : ℕ) (ε : D.host.E) (d : HermitianOrthogonalExtensionData A B c ε) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), (ε = 1 ∨ ε = -1) → IsSelfDualC A Λ → (∀ p, 𝔟 p ≠ 0) → (∀ p x, x ∈ 𝔟 p.rev ↔ star x ∈ (𝔟 p)⁻¹) → IsSelfDualC B (d.lat Λ 𝔟) := by
  intro D A B c ε d Λ 𝔟 hε hΛ hb hd
  exact selfDual_sum Formalism.BasicNotions.Examples₂.star_isIntegral B.gram A.gram (frameMat B A d.ι) d.a ε hε (gram_herm B) (gram_inj A)
    (gram_isom A B d.ι d.isom) d.perp d.gram d.rank Λ 𝔟 hΛ.1 hΛ.2 hb hd _ fun _ => Iff.rfl

end GlobalTheory.ChiGrid.SumDual
