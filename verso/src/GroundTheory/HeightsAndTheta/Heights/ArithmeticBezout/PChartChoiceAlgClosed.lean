import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartChoiceAlgClosed
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChartChoiceAlgClosed

variable {F : Type} [Field F] {n e : ℕ}

/- English proof (translation)
Establish `hmem : ∀ G : MvPolynomial (Fin k × Fin n) F, G ∈ incIdeal P k ↔ ∀ v ∈ incidence P k, aeval v G = 0` using `fun G => by`. Simplify using `[incIdeal, Submodule.mem_iInf, RingHom.mem_ker]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h0, h⟩`. Use `⟨h0, ?_⟩` and prove the remaining obligations.

Use extensionality with `G`. Rewrite using `[hmem, Ideal.mem_span_singleton]`. Conclude with `h G`. Introduce and unpack `⟨h0, h⟩`. Use `⟨h0, fun G => ?_⟩` and prove the remaining obligations.

Rewrite using `[← hmem, h, Ideal.mem_span_singleton]`.
-/
theorem isChowForm_iff_span {P : Ideal (MvPolynomial (Fin n) F)} {k : ℕ}
    {g : MvPolynomial (Fin k × Fin n) F} :
    IsChowForm P k g ↔ g ≠ 0 ∧ incIdeal P k = Ideal.span {g} := by
  have hmem : ∀ G : MvPolynomial (Fin k × Fin n) F,
      G ∈ incIdeal P k ↔ ∀ v ∈ incidence P k, aeval v G = 0 := fun G => by
    simp [incIdeal, Submodule.mem_iInf, RingHom.mem_ker]
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨h0, ?_⟩
    ext G
    rw [hmem, Ideal.mem_span_singleton]
    exact h G
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun G => ?_⟩
    rw [← hmem, h, Ideal.mem_span_singleton]

def shiftVar (e n : ℕ) : Fin e × Fin n → Fin (e + 1) × Fin n := fun jm => (jm.1.succ, jm.2)

def splitFirst (F : Type) [Field F] (e n : ℕ) :
    MvPolynomial (Fin (e + 1) × Fin n) F →ₐ[F] MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F) :=
  aeval fun ij => Fin.cases (motive := fun _ => MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F))
    (X ij.2) (fun j => C (X (j, ij.2))) ij.1

def joinFirst (F : Type) [Field F] (e n : ℕ) :
    MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F) →+* MvPolynomial (Fin (e + 1) × Fin n) F :=
  eval₂Hom (rename (shiftVar e n)).toRingHom (fun m => X (0, m))

/- English proof (translation)
Establish `h : (joinFirst F e n).comp (splitFirst F e n).toRingHom = RingHom.id _`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`. Simplify using `[joinFirst, splitFirst, MvPolynomial.algebraMap_eq]`. Introduce and unpack `⟨i, m⟩`.

Apply the tactic sequence `induction i using Fin.cases <;> simp [joinFirst, splitFirst, shiftVar]`. Conclude with `RingHom.congr_fun h p`.
-/
theorem joinFirst_splitFirst (p : MvPolynomial (Fin (e + 1) × Fin n) F) :
    joinFirst F e n (splitFirst F e n p) = p := by
  have h : (joinFirst F e n).comp (splitFirst F e n).toRingHom = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [joinFirst, splitFirst, MvPolynomial.algebraMap_eq]
    · rintro ⟨i, m⟩
      induction i using Fin.cases <;> simp [joinFirst, splitFirst, shiftVar]
  exact RingHom.congr_fun h p

/- English proof (translation)
Simplify using `[joinFirst]`.
-/
theorem joinFirst_C (a : MvPolynomial (Fin e × Fin n) F) :
    joinFirst F e n (C a) = rename (shiftVar e n) a := by
  simp [joinFirst]

/- English proof (translation)
Unfold `specFirst`. Rewrite using `[bind₁_rename]`. Establish `: (specFirstVar (0 : Fin n → F) ∘ shiftVar e n) = X`. Use function extensionality and compare the values at `jm`. Simplify using `[specFirstVar, shiftVar]`.

Rewrite using `[this, bind₁_X_left]`. Both sides reduce to the same expression.
-/
theorem specFirst_rename_shiftVar (q : MvPolynomial (Fin e × Fin n) F) :
    specFirst (rename (shiftVar e n) q) 0 = q := by
  unfold specFirst
  rw [bind₁_rename]
  have : (specFirstVar (0 : Fin n → F) ∘ shiftVar e n) = X := by
    funext jm
    simp [specFirstVar, shiftVar]
  rw [this, bind₁_X_left]
  rfl

/- English proof (translation)
Unfold `specFirst`. Use `conv_lhs => rw [f.as_sum]`. Rewrite using `[map_sum]`. Use `Finset.sum_eq_zero fun s hs => ?_` and prove the remaining obligations. Rewrite using `[bind₁_monomial]`.

Choose the witnesses or unpack the hypotheses as in `⟨i, hi, h0⟩ : ∃ i ∈ s.support, i.1 = 0 := by`. Assume the negation of the conclusion as `hno`. Use `push Not at hno`. Establish `hw` using `congrFun (hf (mem_support_iff.mp hs)) 0`. Rewrite `hw` using `[Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]`.

Establish `: ∑ c ∈ s.support, (s c • groupWeight (e + 1) n c) 0 = 0`. Use `Finset.sum_eq_zero fun c hc => ?_` and prove the remaining obligations. Simplify using `[groupWeight, Ne.symm (hno c hc)]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Finset.prod_eq_zero hi, mul_zero]`.

Take `⟨a, m⟩` from `i`. Simplify using `only at h0`. Substitute `h0` using the available equality. Simplify using `[specFirstVar, zero_pow (Finsupp.mem_support_iff.mp hi)]`.
-/
theorem specFirst_zero_of_isMultiHomog {δ : ℕ} (hδ : 1 ≤ δ) {f : MvPolynomial (Fin (e + 1) × Fin n) F}
    (hf : IsMultiHomog δ f) : specFirst f 0 = 0 := by
  classical
  unfold specFirst
  conv_lhs => rw [f.as_sum]
  rw [map_sum]
  refine Finset.sum_eq_zero fun s hs => ?_
  rw [bind₁_monomial]
  obtain ⟨i, hi, h0⟩ : ∃ i ∈ s.support, i.1 = 0 := by
    by_contra hno
    push Not at hno
    have hw := congrFun (hf (mem_support_iff.mp hs)) 0
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply] at hw
    have : ∑ c ∈ s.support, (s c • groupWeight (e + 1) n c) 0 = 0 := by
      refine Finset.sum_eq_zero fun c hc => ?_
      simp [groupWeight, Ne.symm (hno c hc)]
    omega
  rw [Finset.prod_eq_zero hi, mul_zero]
  obtain ⟨a, m⟩ := i
  simp only at h0
  subst h0
  simp [specFirstVar, zero_pow (Finsupp.mem_support_iff.mp hi)]

/- English proof (translation)
Rewrite using `[eval_map]`. Establish `h : (eval₂Hom (Ideal.Quotient.mk J) (fun m => Ideal.Quotient.mk J (C (t m)))).comp (splitFirst F e n).toRingHom = (Ideal.Quotient.mk J).comp (bind₁ (specFirstVar t)).toRingHom`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`. Simplify using `[splitFirst, MvPolynomial.algebraMap_eq]`.

Introduce and unpack `⟨i, m⟩`. Apply the tactic sequence `induction i using Fin.cases <;> simp [splitFirst, specFirstVar]`. Conclude with `RingHom.congr_fun h f`.
-/
theorem eval_map_splitFirst (J : Ideal (MvPolynomial (Fin e × Fin n) F)) (t : Fin n → F)
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) :
    eval (fun m => Ideal.Quotient.mk J (C (t m))) (map (Ideal.Quotient.mk J) (splitFirst F e n f)) =
      Ideal.Quotient.mk J (specFirst f t) := by
  rw [eval_map]
  have h : (eval₂Hom (Ideal.Quotient.mk J) (fun m => Ideal.Quotient.mk J (C (t m)))).comp
      (splitFirst F e n).toRingHom = (Ideal.Quotient.mk J).comp (bind₁ (specFirstVar t)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [splitFirst, MvPolynomial.algebraMap_eq]
    · rintro ⟨i, m⟩
      induction i using Fin.cases <;> simp [splitFirst, specFirstVar]
  exact RingHom.congr_fun h f

end ChartChoiceAlgClosed

open ChartChoiceAlgClosed in

/- English proof (translation)
Introduce `F _ _ n e I f q hI hf hq`. Take `⟨hf0, hspan⟩` from `isChowForm_iff_span.mp hf`. Establish `hfp : Prime f`. Use `h₁ F n (e + 1) I hI.isPrime hI.isRelevant` as an intermediate fact. Rewrite `this` using `[hspan]`.

Conclude with `(Ideal.span_singleton_prime hf0).mp this`. Take `⟨δ, hδ, hhom⟩` from `h₂ F n (e + 1) I f hI hf`. Establish `hndvd : ¬ rename (shiftVar e n) q ∣ f`. Introduce and unpack `⟨g, hg⟩`. Break down `hfp.2.2 (rename (shiftVar e n) q) g (hg ▸ dvd_refl f) with ⟨h, hh⟩ | ⟨h, hh⟩` into its components or cases.

Use `congrArg (fun p => specFirst p 0) hh` as an intermediate fact. Rewrite `this` using `[specFirst_rename_shiftVar]`. Unfold `specFirst at this`. Rewrite `this` using `[map_mul]`. Establish `h0 : specFirst f 0 = 0` using `specFirst_zero_of_isMultiHomog hδ hhom`.

Unfold `specFirst at h0`. Rewrite `this` using `[h0, zero_mul]`. Conclude with `hq.ne_zero this`. Establish `hunit : IsUnit (rename (shiftVar e n) q)`. Use `isUnit_iff_exists_inv.mpr ⟨h, ?_⟩` and prove the remaining obligations.

Apply `mul_left_cancel₀ hf0` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Use `hunit.map (bind₁ (specFirstVar (0 : Fin n → F)))` as an intermediate fact. Establish `h' : bind₁ (specFirstVar (0 : Fin n → F)) (rename (shiftVar e n) q) = q` using `specFirst_rename_shiftVar q`. Rewrite `this` using `[h']`.

Conclude with `hq.not_isUnit this`. Use `set J : Ideal (MvPolynomial (Fin e × Fin n) F) := Ideal.span {q} with hJ`. Establish `: J.IsPrime` using `(Ideal.span_singleton_prime hq.ne_zero).mpr hq`. Use `set P := map (Ideal.Quotient.mk J) (splitFirst F e n f) with hP`. Establish `hP0 : P ≠ 0`.

Introduce `h0`. Establish `hmem : splitFirst F e n f ∈ RingHom.ker (map (σ` using `Fin n) (Ideal.Quotient.mk J)) := by`. Rewrite using `[RingHom.mem_ker]`. Conclude with `h0`. Rewrite `hmem` using `[MvPolynomial.ker_map, Ideal.mk_ker, hJ, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]`.

Apply `hndvd` to reduce the goal to its premises. Use `map_dvd (joinFirst F e n) hmem` as an intermediate fact. Rewrite `this` using `[joinFirst_splitFirst, joinFirst_C]`. Then use the resulting hypothesis. Set `g : ℕ ↪ F` to `Infinite.natEmbedding F`. Establish `hinj : Function.Injective fun k : ℕ => Ideal.Quotient.mk J (C (g k))`.

Introduce `a b hab`. Apply `g.injective` to reduce the goal to its premises. Apply `(algebraMap F (MvPolynomial (Fin e × Fin n) F ⧸ J)).injective` to reduce the goal to its premises. Conclude with `hab`. Assume the negation of the conclusion as `hall`.

Use `push Not at hall`. Apply `hP0` to reduce the goal to its premises. Use `eq_zero_of_eval_zero_at_prod_finset P (fun _ => (Finset.range (P.totalDegree + 1)).image (fun k : ℕ => Ideal.Quotient.mk J (C (g k)))) (fun i => ?_) (fun x hx => ?_)` and prove the remaining obligations. Rewrite using `[Finset.card_image_of_injective _ hinj, Finset.card_range]`. Conclude with `Nat.lt_succ_of_le (degreeOf_le_totalDegree P i)`.

Use `choose k _ hk using fun i => Finset.mem_image.mp (hx i)`. Establish `hx' : x = fun m => Ideal.Quotient.mk J (C ((fun m => g (k m)) m))`. Use function extensionality and compare the values at `m`. Rewrite using `[← hk m]`. Rewrite using `[hx', hP, eval_map_splitFirst]`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (hall _))`.
-/
theorem ChartChoiceAlgClosed.proof (h₁ : IncIdealPrime.Statement) (h₂ : ChowFormMultiHomog.Statement) :
    ChartChoiceAlgClosed.Statement := by
  intro F _ _ n e I f q hI hf hq
  classical
  obtain ⟨hf0, hspan⟩ := isChowForm_iff_span.mp hf
  have hfp : Prime f := by
    have := h₁ F n (e + 1) I hI.isPrime hI.isRelevant
    rw [hspan] at this
    exact (Ideal.span_singleton_prime hf0).mp this
  obtain ⟨δ, hδ, hhom⟩ := h₂ F n (e + 1) I f hI hf

  have hndvd : ¬ rename (shiftVar e n) q ∣ f := by
    rintro ⟨g, hg⟩
    rcases hfp.2.2 (rename (shiftVar e n) q) g (hg ▸ dvd_refl f) with ⟨h, hh⟩ | ⟨h, hh⟩
    · have := congrArg (fun p => specFirst p 0) hh
      rw [specFirst_rename_shiftVar] at this
      unfold specFirst at this
      rw [map_mul] at this
      have h0 : specFirst f 0 = 0 := specFirst_zero_of_isMultiHomog hδ hhom
      unfold specFirst at h0
      rw [h0, zero_mul] at this
      exact hq.ne_zero this
    · have hunit : IsUnit (rename (shiftVar e n) q) := by
        refine isUnit_iff_exists_inv.mpr ⟨h, ?_⟩
        apply mul_left_cancel₀ hf0
        calc f * (rename (shiftVar e n) q * h) = rename (shiftVar e n) q * (f * h) := by ring
          _ = f * 1 := by rw [← hh, ← hg, mul_one]
      have := hunit.map (bind₁ (specFirstVar (0 : Fin n → F)))
      have h' : bind₁ (specFirstVar (0 : Fin n → F)) (rename (shiftVar e n) q) = q :=
        specFirst_rename_shiftVar q
      rw [h'] at this
      exact hq.not_isUnit this
  set J : Ideal (MvPolynomial (Fin e × Fin n) F) := Ideal.span {q} with hJ
  have : J.IsPrime := (Ideal.span_singleton_prime hq.ne_zero).mpr hq
  set P := map (Ideal.Quotient.mk J) (splitFirst F e n f) with hP
  have hP0 : P ≠ 0 := by
    intro h0
    have hmem : splitFirst F e n f ∈ RingHom.ker (map (σ := Fin n) (Ideal.Quotient.mk J)) := by
      rw [RingHom.mem_ker]; exact h0
    rw [MvPolynomial.ker_map, Ideal.mk_ker, hJ, Ideal.map_span, Set.image_singleton,
      Ideal.mem_span_singleton] at hmem
    apply hndvd
    have := map_dvd (joinFirst F e n) hmem
    rwa [joinFirst_splitFirst, joinFirst_C] at this

  let g : ℕ ↪ F := Infinite.natEmbedding F
  have hinj : Function.Injective fun k : ℕ => Ideal.Quotient.mk J (C (g k)) := by
    intro a b hab
    apply g.injective
    apply (algebraMap F (MvPolynomial (Fin e × Fin n) F ⧸ J)).injective
    exact hab
  by_contra hall
  push Not at hall
  apply hP0
  refine eq_zero_of_eval_zero_at_prod_finset P
    (fun _ => (Finset.range (P.totalDegree + 1)).image (fun k : ℕ => Ideal.Quotient.mk J (C (g k))))
    (fun i => ?_) (fun x hx => ?_)
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
    exact Nat.lt_succ_of_le (degreeOf_le_totalDegree P i)
  · choose k _ hk using fun i => Finset.mem_image.mp (hx i)
    have hx' : x = fun m => Ideal.Quotient.mk J (C ((fun m => g (k m)) m)) := by
      funext m
      rw [← hk m]
    rw [hx', hP, eval_map_splitFirst]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (hall _))

end

end GroundTheory.Heights₂.Heights
