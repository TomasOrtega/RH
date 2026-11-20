import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.ImportsBis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChartIncDomain

/- English proof (translation)
Rewrite using `[aeval_def, aeval_def, eval₂_eq, eval₂_eq, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun s hs => ?_` and prove the remaining obligations. Establish `hs' : ∑ i ∈ s.support, s i = d`. Use `hp (mem_support_iff.mp hs)` as an intermediate fact. Simplify `this` using `[Finsupp.weight_apply, Finsupp.sum]`.

Simplify using `only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hs']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem aeval_smul_of_isHomogeneous {R S σ : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {p : MvPolynomial σ R} {d : ℕ} (hp : p.IsHomogeneous d) (c : S) (x : σ → S) :
    aeval (c • x) p = c ^ d * aeval x p := by
  classical
  rw [aeval_def, aeval_def, eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs' : ∑ i ∈ s.support, s i = d := by
    have := hp (mem_support_iff.mp hs)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hs']
  ring

/- English proof (translation)
The claim follows from `IsHomogeneous.sum _ _ _ fun _ _ => (isHomogeneous_X _ _).C_mul _`.
-/
theorem isHomogeneous_linForm {F : Type*} [CommRing F] {n : ℕ} (t : Fin n → F) :
    (linForm t).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun _ _ => (isHomogeneous_X _ _).C_mul _

variable {F : Type} [Field F] {n : ℕ}

/- English proof (translation)
Proceed by induction on `g using MvPolynomial.induction_on with`. Consider the case `C a`. Rewrite using `[aeval_C, IsScalarTower.algebraMap_apply F (MvPolynomial (Fin n) F ⧸ I)]`. Both sides reduce to the same expression. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`.

Consider the case `mul_X p j hp => simp only [map_mul, hp, aeval_X, genPt]`.
-/
theorem aeval_genPt (I : Ideal (MvPolynomial (Fin n) F)) [I.IsPrime] (g : MvPolynomial (Fin n) F) :
    aeval (genPt I) g =
      algebraMap (MvPolynomial (Fin n) F ⧸ I) (FractionRing (MvPolynomial (Fin n) F ⧸ I))
        (Ideal.Quotient.mk I g) := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, IsScalarTower.algebraMap_apply F (MvPolynomial (Fin n) F ⧸ I)]
    rfl
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp => simp only [map_mul, hp, aeval_X, genPt]

/- English proof (translation)
Use `hI.isPrime` as an intermediate fact. Use `set ξ := genPt I`. Use `set τ := aeval ξ (linForm t)`. Establish `hτ : τ ≠ 0`. Rewrite using `[show τ = _ from aeval_genPt I (linForm t), Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `ht`. Establish `hhom : ∀ (p : MvPolynomial (Fin n) F) (d : ℕ), p.IsHomogeneous d → aeval (τ⁻¹ • ξ) p = τ⁻¹ ^ d * aeval ξ p` using `fun p d hp => aeval_smul_of_isHomogeneous hp _ _`. Establish `hcomp : ∀ (g : MvPolynomial (Fin n) F), aeval (τ⁻¹ • ξ) g = ∑ d ∈ Finset.range (g.totalDegree + 1), τ⁻¹ ^ d * aeval ξ (homogeneousComponent d g)`. Introduce `g`. Use `conv_lhs => rw [← sum_homogeneousComponent g]`.

Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun d _ => hhom _ _ (homogeneousComponent_isHomogeneous d g)`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `g hg`. Rewrite `hg` using `[RingHom.mem_ker]`.

Use `set D := g.totalDegree`. Use `set G := ∑ d ∈ Finset.range (D + 1), homogeneousComponent d g * linForm t ^ (D - d)`. Establish `hGξ : aeval ξ G = τ ^ D * aeval (τ⁻¹ • ξ) g`. Rewrite using `[hcomp, Finset.mul_sum, map_sum]`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations.

Establish `hdD : d ≤ D` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)`. Rewrite using `[map_mul, map_pow, ← mul_assoc, mul_comm (aeval ξ _)]`. Use `congr 1`. Rewrite using `[← Nat.sub_add_cancel hdD, pow_add, mul_assoc, ← mul_pow, mul_inv_cancel₀ hτ, one_pow, mul_one, Nat.sub_add_cancel hdD]`. Establish `hGI : G ∈ I`.

Establish `h0 : aeval ξ G = 0`. Rewrite using `[hGξ]`. Establish `: (aeval (τ⁻¹ • ξ) : MvPolynomial (Fin n) F →ₐ[F] _) g = 0` using `hg`. Rewrite using `[this, mul_zero]`. Rewrite `h0` using `[aeval_genPt, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `h0`. Use `set J := I ⊔ Ideal.span {linForm t - 1}`. Establish `h1 : Ideal.Quotient.mk J (linForm t) = 1`. Rewrite using `[← sub_eq_zero, ← map_one (Ideal.Quotient.mk J), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)`.

Establish `hG : Ideal.Quotient.mk J G = Ideal.Quotient.mk J g`. Simplify using `only [G, map_sum, map_mul, map_pow, h1, one_pow, mul_one]`. Rewrite using `[← map_sum, sum_homogeneousComponent]`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, ← hG, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.mem_sup_left hGI`.

Use `sup_le ?_ ?_` and prove the remaining obligations. Introduce `g hg`. Rewrite using `[RingHom.mem_ker]`. Express the relevant statement in the definitionally equal form `aeval (τ⁻¹ • ξ) g = 0`. Rewrite using `[hcomp]`.

Use `Finset.sum_eq_zero fun d _ => ?_` and prove the remaining obligations. Rewrite using `[aeval_genPt, (Ideal.Quotient.eq_zero_iff_mem).mpr (hI.isHomog g hg d), map_zero, mul_zero]`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]`. Express the relevant statement in the definitionally equal form `aeval (τ⁻¹ • ξ) (linForm t - 1) = 0`. Rewrite using `[map_sub, map_one, hhom _ 1 (isHomogeneous_linForm t), pow_one, inv_mul_cancel₀ hτ, sub_self]`.
-/
theorem ker_aeval_eta (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (hI : IsProjPrime I)
    (ht : linForm t ∉ I) :
    have := hI.isPrime
    RingHom.ker (aeval ((aeval (genPt I) (linForm t))⁻¹ • genPt I) :
        MvPolynomial (Fin n) F →ₐ[F] FractionRing (MvPolynomial (Fin n) F ⧸ I)) =
      I ⊔ Ideal.span {linForm t - 1} := by
  have := hI.isPrime
  set ξ := genPt I
  set τ := aeval ξ (linForm t)
  have hτ : τ ≠ 0 := by
    rw [show τ = _ from aeval_genPt I (linForm t), Ne, IsFractionRing.to_map_eq_zero_iff,
      Ideal.Quotient.eq_zero_iff_mem]
    exact ht
  have hhom : ∀ (p : MvPolynomial (Fin n) F) (d : ℕ), p.IsHomogeneous d →
      aeval (τ⁻¹ • ξ) p = τ⁻¹ ^ d * aeval ξ p := fun p d hp => aeval_smul_of_isHomogeneous hp _ _
  have hcomp : ∀ (g : MvPolynomial (Fin n) F), aeval (τ⁻¹ • ξ) g =
      ∑ d ∈ Finset.range (g.totalDegree + 1), τ⁻¹ ^ d * aeval ξ (homogeneousComponent d g) := by
    intro g
    conv_lhs => rw [← sum_homogeneousComponent g]
    rw [map_sum]
    exact Finset.sum_congr rfl fun d _ => hhom _ _ (homogeneousComponent_isHomogeneous d g)
  apply le_antisymm
  · intro g hg
    rw [RingHom.mem_ker] at hg
    set D := g.totalDegree
    set G := ∑ d ∈ Finset.range (D + 1), homogeneousComponent d g * linForm t ^ (D - d)
    have hGξ : aeval ξ G = τ ^ D * aeval (τ⁻¹ • ξ) g := by
      rw [hcomp, Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hdD : d ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
      rw [map_mul, map_pow, ← mul_assoc, mul_comm (aeval ξ _)]
      congr 1
      rw [← Nat.sub_add_cancel hdD, pow_add, mul_assoc, ← mul_pow, mul_inv_cancel₀ hτ, one_pow,
        mul_one, Nat.sub_add_cancel hdD]
    have hGI : G ∈ I := by
      have h0 : aeval ξ G = 0 := by
        rw [hGξ]
        have : (aeval (τ⁻¹ • ξ) : MvPolynomial (Fin n) F →ₐ[F] _) g = 0 := hg
        rw [this, mul_zero]
      rw [aeval_genPt, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h0
      exact h0
    set J := I ⊔ Ideal.span {linForm t - 1}
    have h1 : Ideal.Quotient.mk J (linForm t) = 1 := by
      rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk J), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    have hG : Ideal.Quotient.mk J G = Ideal.Quotient.mk J g := by
      simp only [G, map_sum, map_mul, map_pow, h1, one_pow, mul_one]
      rw [← map_sum, sum_homogeneousComponent]
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← hG, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_left hGI
  · refine sup_le ?_ ?_
    · intro g hg
      rw [RingHom.mem_ker]
      change aeval (τ⁻¹ • ξ) g = 0
      rw [hcomp]
      refine Finset.sum_eq_zero fun d _ => ?_
      rw [aeval_genPt, (Ideal.Quotient.eq_zero_iff_mem).mpr (hI.isHomog g hg d), map_zero, mul_zero]
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
      change aeval (τ⁻¹ • ξ) (linForm t - 1) = 0
      rw [map_sub, map_one, hhom _ 1 (isHomogeneous_linForm t), pow_one, inv_mul_cancel₀ hτ, sub_self]

/- English proof (translation)
Introduce `F _ n e I t hI ht`. Use `hI.isPrime` as an intermediate fact. Use `set J := I ⊔ Ideal.span {linForm t - 1} with hJdef`. Establish `hJ : J.IsPrime`. Rewrite using `[hJdef, ← ker_aeval_eta I t hI ht]`.

Conclude with `RingHom.ker_isPrime _`. Use `set q : MvPolynomial (Fin n) F →+* MvPolynomial (Fin n) F ⧸ J := Ideal.Quotient.mk J with hq`. Use `set ζ : Fin n → MvPolynomial (Fin n) F ⧸ J := fun m => q (X m) with hζ`. Use `set c : Fin n → MvPolynomial (Fin n) F ⧸ J := fun m => q (C (t m)) with hc'`. Establish `hc : ∑ l, c l * ζ l = 1`.

Establish `h1 : q (linForm t) = 1`. Rewrite using `[← sub_eq_zero, ← map_one q, ← map_sub, hq, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)`. Rewrite using `[← h1, linForm, map_sum]`. Simplify using `only [map_mul, hζ, hc']`.

Use `set γ : MvPolynomial (Fin n ⊕ Fin e × Fin n) F →+* MvPolynomial (Fin e × Fin n) (MvPolynomial (Fin n) F ⧸ J) := eval₂Hom (C.comp (q.comp C)) (Sum.elim (fun m => C (ζ m)) (genSubst ζ c)) with hγ`. Establish `hγX : ∀ g, γ (rename Sum.inl g) = C (q g)`. Introduce `g`. Establish `: γ.comp (rename Sum.inl).toRingHom = C.comp q`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises.

Introduce `a`. Simplify using `[hγ]`. Introduce `m`. Simplify using `[hγ, hζ]`. Conclude with `RingHom.congr_fun this g`.

Establish `hker : chartIncIdeal I t e ≤ RingHom.ker γ`. Use `sup_le ?_ ?_` and prove the remaining obligations. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `g hg`. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker]`.

Rewrite using `[hγX, hq, (Ideal.Quotient.eq_zero_iff_mem).mpr hg, map_zero]`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Rewrite using `[SetLike.mem_coe, RingHom.mem_ker]`. Establish `hC : ∑ l, C (c l) * C (ζ l) = (1 : MvPolynomial (Fin e × Fin n) (MvPolynomial (Fin n) F ⧸ J))`.

Rewrite using `[← C_1, ← hc, map_sum]`. Simplify using `only [C_mul]`. Simplify using `only [map_sum, map_mul, hγ, coe_eval₂Hom, eval₂_X, Sum.elim_inl, Sum.elim_inr]`. Simplify using `only [genSubst, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, hC, mul_one, sub_self]`. Use `set γbar : MvPolynomial (Fin n ⊕ Fin e × Fin n) F ⧸ chartIncIdeal I t e →+* MvPolynomial (Fin e × Fin n) (MvPolynomial (Fin n) F ⧸ J) := Ideal.Quotient.lift (chartIncIdeal I t e) γ (fun a ha => RingHom.mem_ker.mp (hker ha)) with hγbar`.

Use `set χ : MvPolynomial (Fin n) F →+* MvPolynomial (Fin n ⊕ Fin e × Fin n) F ⧸ chartIncIdeal I t e := (Ideal.Quotient.mk (chartIncIdeal I t e)).comp (rename Sum.inl).toRingHom with hχ`. Establish `hJX : ∀ a ∈ J, χ a = 0`. Introduce `a ha`. Rewrite using `[hχ, RingHom.comp_apply]`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha)`. Use `set β : MvPolynomial (Fin e × Fin n) (MvPolynomial (Fin n) F ⧸ J) →+* MvPolynomial (Fin n ⊕ Fin e × Fin n) F ⧸ chartIncIdeal I t e := eval₂Hom (Ideal.Quotient.lift J χ hJX) (fun im => Ideal.Quotient.mk (chartIncIdeal I t e) (X (Sum.inr im))) with hβ`. Establish `hβγ : β.comp γ = Ideal.Quotient.mk (chartIncIdeal I t e)`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`.

Simplify using `[hβ, hγ, hq, hχ]`. Introduce and unpack `(m | im)`. Simplify using `[hβ, hγ, hζ, hq, hχ]`. Establish `h0 : Ideal.Quotient.mk (chartIncIdeal I t e) (∑ l, X (Sum.inr (im.1, l)) * X (Sum.inl l)) = 0`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `Ideal.mem_sup_right (Ideal.subset_span ⟨im.1, rfl⟩)`. Simplify using `only [map_sum, map_mul] at h0`. Simplify using `[hβ, hγ, hζ, hc', hq, hχ, genSubst, h0]`. Establish `hleft : ∀ x : MvPolynomial (Fin n ⊕ Fin e × Fin n) F ⧸ chartIncIdeal I t e, β (γbar x) = x`. Introduce `x`.

Take `⟨g, rfl⟩` from `Ideal.Quotient.mk_surjective (I := chartIncIdeal I t e) x`. Rewrite using `[hγbar, Ideal.Quotient.lift_mk]`. Conclude with `RingHom.congr_fun hβγ g`. Establish `hinj : Function.Injective γbar` using `Function.LeftInverse.injective hleft`. Use `⟨(hinj.isDomain γbar :), ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `RingHom.ker χ = J`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce `hg`. Rewrite `hg` using `[RingHom.mem_ker]`.

Establish `h` using `hγX g`. Establish `h' : γbar (χ g) = γ (rename Sum.inl g)`. Rewrite using `[hγbar, hχ, RingHom.comp_apply]`. Conclude with `Ideal.Quotient.lift_mk _ _ _`. Rewrite `h` using `[← h', hg, map_zero, eq_comm, C_eq_zero, hq, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `h`. Introduce `hg`. Conclude with `hJX g hg`.
-/
theorem proof : ChartIncDomain.Statement := by
  intro F _ n e I t hI ht
  have := hI.isPrime
  set J := I ⊔ Ideal.span {linForm t - 1} with hJdef
  have hJ : J.IsPrime := by
    rw [hJdef, ← ker_aeval_eta I t hI ht]
    exact RingHom.ker_isPrime _

  set q : MvPolynomial (Fin n) F →+* MvPolynomial (Fin n) F ⧸ J := Ideal.Quotient.mk J with hq
  set ζ : Fin n → MvPolynomial (Fin n) F ⧸ J := fun m => q (X m) with hζ
  set c : Fin n → MvPolynomial (Fin n) F ⧸ J := fun m => q (C (t m)) with hc'
  have hc : ∑ l, c l * ζ l = 1 := by
    have h1 : q (linForm t) = 1 := by
      rw [← sub_eq_zero, ← map_one q, ← map_sub, hq, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    rw [← h1, linForm, map_sum]
    simp only [map_mul, hζ, hc']

  set γ : MvPolynomial (Fin n ⊕ Fin e × Fin n) F →+* MvPolynomial (Fin e × Fin n) (MvPolynomial (Fin n) F ⧸ J) :=
    eval₂Hom (C.comp (q.comp C)) (Sum.elim (fun m => C (ζ m)) (genSubst ζ c)) with hγ
  have hγX : ∀ g, γ (rename Sum.inl g) = C (q g) := by
    intro g
    have : γ.comp (rename Sum.inl).toRingHom = C.comp q := by
      apply MvPolynomial.ringHom_ext
      · intro a; simp [hγ]
      · intro m; simp [hγ, hζ]
    exact RingHom.congr_fun this g
  have hker : chartIncIdeal I t e ≤ RingHom.ker γ := by
    refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro g hg
      rw [Ideal.mem_comap, RingHom.mem_ker]
      rw [hγX, hq, (Ideal.Quotient.eq_zero_iff_mem).mpr hg, map_zero]
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker]
      have hC : ∑ l, C (c l) * C (ζ l) = (1 : MvPolynomial (Fin e × Fin n) (MvPolynomial (Fin n) F ⧸ J)) := by
        rw [← C_1, ← hc, map_sum]
        simp only [C_mul]
      simp only [map_sum, map_mul, hγ, coe_eval₂Hom, eval₂_X, Sum.elim_inl, Sum.elim_inr]
      simp only [genSubst, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, hC, mul_one,
        sub_self]

  set γbar : MvPolynomial (Fin n ⊕ Fin e × Fin n) F ⧸ chartIncIdeal I t e →+* MvPolynomial (Fin e × Fin n) (MvPolynomial (Fin n) F ⧸ J) :=
    Ideal.Quotient.lift (chartIncIdeal I t e) γ (fun a ha => RingHom.mem_ker.mp (hker ha)) with hγbar
  set χ : MvPolynomial (Fin n) F →+* MvPolynomial (Fin n ⊕ Fin e × Fin n) F ⧸ chartIncIdeal I t e :=
    (Ideal.Quotient.mk (chartIncIdeal I t e)).comp (rename Sum.inl).toRingHom with hχ
  have hJX : ∀ a ∈ J, χ a = 0 := by
    intro a ha
    rw [hχ, RingHom.comp_apply]
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha)

  set β : MvPolynomial (Fin e × Fin n) (MvPolynomial (Fin n) F ⧸ J) →+*
      MvPolynomial (Fin n ⊕ Fin e × Fin n) F ⧸ chartIncIdeal I t e :=
    eval₂Hom (Ideal.Quotient.lift J χ hJX)
      (fun im => Ideal.Quotient.mk (chartIncIdeal I t e) (X (Sum.inr im))) with hβ
  have hβγ : β.comp γ = Ideal.Quotient.mk (chartIncIdeal I t e) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [hβ, hγ, hq, hχ]
    · rintro (m | im)
      · simp [hβ, hγ, hζ, hq, hχ]
      · have h0 : Ideal.Quotient.mk (chartIncIdeal I t e)
            (∑ l, X (Sum.inr (im.1, l)) * X (Sum.inl l)) = 0 := by
          rw [Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.mem_sup_right (Ideal.subset_span ⟨im.1, rfl⟩)
        simp only [map_sum, map_mul] at h0
        simp [hβ, hγ, hζ, hc', hq, hχ, genSubst, h0]
  have hleft : ∀ x : MvPolynomial (Fin n ⊕ Fin e × Fin n) F ⧸ chartIncIdeal I t e, β (γbar x) = x := by
    intro x
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective (I := chartIncIdeal I t e) x
    rw [hγbar, Ideal.Quotient.lift_mk]
    exact RingHom.congr_fun hβγ g
  have hinj : Function.Injective γbar := Function.LeftInverse.injective hleft
  refine ⟨(hinj.isDomain γbar :), ?_⟩
  change RingHom.ker χ = J
  ext g
  constructor
  · intro hg
    rw [RingHom.mem_ker] at hg
    have h := hγX g
    have h' : γbar (χ g) = γ (rename Sum.inl g) := by
      rw [hγbar, hχ, RingHom.comp_apply]
      exact Ideal.Quotient.lift_mk _ _ _
    rw [← h', hg, map_zero, eq_comm, C_eq_zero, hq, Ideal.Quotient.eq_zero_iff_mem] at h
    exact h
  · intro hg
    exact hJX g hg

end ChartIncDomain

end

end GroundTheory.Heights₂.Heights
