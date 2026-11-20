import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open GroundTheory.Heights₂.Heights.ComplexSets (zeroSet)

variable {n : ℕ}

def graphHom (p : MvPolynomial (Fin n) ℂ) : MvPolynomial (Fin (n + 1)) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  aeval (Fin.snoc (X : Fin n → MvPolynomial (Fin n) ℂ) p : Fin (n + 1) → MvPolynomial (Fin n) ℂ)

def graphIdeal (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : MvPolynomial (Fin n) ℂ) :
    Ideal (MvPolynomial (Fin (n + 1)) ℂ) :=
  J.comap (graphHom p)

def graphPt (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) : Fin (n + 1) → ℂ :=
  Fin.snoc x (eval x p)

/- English proof (translation)
Simplify using `[graphHom]`.
-/
theorem graphHom_X_castSucc (p : MvPolynomial (Fin n) ℂ) (i : Fin n) :
    graphHom p (X (Fin.castSucc i)) = X i := by
  simp [graphHom]

/- English proof (translation)
Simplify using `[graphHom]`.
-/
theorem graphHom_X_last (p : MvPolynomial (Fin n) ℂ) : graphHom p (X (Fin.last n)) = p := by
  simp [graphHom]

/- English proof (translation)
Rewrite using `[graphHom, aeval_rename]`. Establish `: (Fin.snoc (X : Fin n → MvPolynomial (Fin n) ℂ) p : Fin (n + 1) → MvPolynomial (Fin n) ℂ) ∘ Fin.castSucc = X`. Use function extensionality and compare the values at `fun i => by simp`. Rewrite using `[this, aeval_X_left_apply]`.
-/
theorem graphHom_rename (p q : MvPolynomial (Fin n) ℂ) : graphHom p (rename Fin.castSucc q) = q := by
  rw [graphHom, aeval_rename]
  have : (Fin.snoc (X : Fin n → MvPolynomial (Fin n) ℂ) p : Fin (n + 1) → MvPolynomial (Fin n) ℂ) ∘ Fin.castSucc = X :=
    funext fun i => by simp
  rw [this, aeval_X_left_apply]

/- English proof (translation)
Introduce `q` and use `⟨rename Fin.castSucc q, graphHom_rename p q⟩`.
-/
theorem graphHom_surjective (p : MvPolynomial (Fin n) ℂ) : Function.Surjective (graphHom p) :=
  fun q => ⟨rename Fin.castSucc q, graphHom_rename p q⟩

/- English proof (translation)
Establish `h : (eval (graphPt p x) : MvPolynomial (Fin (n + 1)) ℂ →+* ℂ) = (eval x).comp (graphHom p).toRingHom`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`. Simplify using the standard rewrite rules. Introduce `i`.

Use `Fin.lastCases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using `[graphPt, graphHom]`. Simplify using `[graphPt, graphHom]`. Conclude with `congrArg (fun φ : MvPolynomial (Fin (n + 1)) ℂ →+* ℂ => φ q) h`.
-/
theorem eval_graphPt (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) (q : MvPolynomial (Fin (n + 1)) ℂ) :
    eval (graphPt p x) q = eval x (graphHom p q) := by
  have h : (eval (graphPt p x) : MvPolynomial (Fin (n + 1)) ℂ →+* ℂ) =
      (eval x).comp (graphHom p).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [graphPt, graphHom]
      · simp [graphPt, graphHom]
  exact congrArg (fun φ : MvPolynomial (Fin (n + 1)) ℂ →+* ℂ => φ q) h

/- English proof (translation)
Simplify using `[graphPt]`.
-/
theorem graphPt_init (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) : Fin.init (graphPt p x) = x := by
  simp [graphPt]

/- English proof (translation)
Simplify using `[graphPt]`.
-/
theorem graphPt_last (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) : graphPt p x (Fin.last n) = eval x p := by
  simp [graphPt]

/- English proof (translation)
The claim follows from `Ideal.comap_isPrime _ _`.
-/
theorem graphIdeal_isPrime {J : Ideal (MvPolynomial (Fin n) ℂ)} (hJ : J.IsPrime) (p : MvPolynomial (Fin n) ℂ) :
    (graphIdeal J p).IsPrime :=
  Ideal.comap_isPrime _ _

/- English proof (translation)
Introduce `q hq`. Rewrite using `[eval_graphPt]`. Conclude with `hx _ hq`.
-/
theorem graphPt_mem_zeroSet {J : Ideal (MvPolynomial (Fin n) ℂ)} (p : MvPolynomial (Fin n) ℂ) {x : Fin n → ℂ}
    (hx : x ∈ zeroSet J) : graphPt p x ∈ zeroSet (graphIdeal J p) := by
  intro q hq
  rw [eval_graphPt]
  exact hx _ hq

/- English proof (translation)
Introduce `q hq`. Establish `h` using `hx (rename Fin.castSucc q) (by rw [graphIdeal, Ideal.mem_comap, graphHom_rename]; exact hq)`. Rewrite `h` using `[eval_rename]`. Conclude with `h`.
-/
theorem init_mem_zeroSet {J : Ideal (MvPolynomial (Fin n) ℂ)} (p : MvPolynomial (Fin n) ℂ)
    {x : Fin (n + 1) → ℂ} (hx : x ∈ zeroSet (graphIdeal J p)) : Fin.init x ∈ zeroSet J := by
  intro q hq
  have h := hx (rename Fin.castSucc q) (by rw [graphIdeal, Ideal.mem_comap, graphHom_rename]; exact hq)
  rw [eval_rename] at h
  exact h

/- English proof (translation)
Establish `h` using `hx (X (Fin.last n) - rename Fin.castSucc p) (by rw [graphIdeal, Ideal.mem_comap, map_sub, graphHom_X_last, graphHom_rename, sub_self]; exact J.zero_mem)`. Rewrite `h` using `[map_sub, eval_X, eval_rename, sub_eq_zero]`. Rewrite using `[graphPt]`. Use `conv_rhs => rw [← Fin.snoc_init_self x]`. Rewrite using `[h]`.

Both sides reduce to the same expression.
-/
theorem graphPt_init_of_mem_zeroSet {J : Ideal (MvPolynomial (Fin n) ℂ)} (p : MvPolynomial (Fin n) ℂ)
    {x : Fin (n + 1) → ℂ} (hx : x ∈ zeroSet (graphIdeal J p)) : graphPt p (Fin.init x) = x := by
  have h := hx (X (Fin.last n) - rename Fin.castSucc p)
    (by rw [graphIdeal, Ideal.mem_comap, map_sub, graphHom_X_last, graphHom_rename, sub_self]; exact J.zero_mem)
  rw [map_sub, eval_X, eval_rename, sub_eq_zero] at h
  rw [graphPt]
  conv_rhs => rw [← Fin.snoc_init_self x]
  rw [h]
  rfl

/- English proof (translation)
Set `g : MvPolynomial (Fin (n + 1)) ℂ →+* MvPolynomial (Fin n) ℂ ⧸ J` to `(Ideal.Quotient.mk J).comp (graphHom p).toRingHom`. Establish `hg : Function.Surjective g` using `Ideal.Quotient.mk_surjective.comp (graphHom_surjective p)`. Establish `hker : RingHom.ker g = graphIdeal J p`. Rewrite using `[← RingHom.comap_ker, Ideal.mk_ker]`. Both sides reduce to the same expression.

Conclude with `ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hg))`.
-/
theorem ringKrullDim_graphIdeal (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : MvPolynomial (Fin n) ℂ) :
    ringKrullDim (MvPolynomial (Fin (n + 1)) ℂ ⧸ graphIdeal J p) = ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) := by
  let g : MvPolynomial (Fin (n + 1)) ℂ →+* MvPolynomial (Fin n) ℂ ⧸ J :=
    (Ideal.Quotient.mk J).comp (graphHom p).toRingHom
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp (graphHom_surjective p)
  have hker : RingHom.ker g = graphIdeal J p := by
    rw [← RingHom.comap_ker, Ideal.mk_ker]
    rfl
  exact ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hg))

/- English proof (translation)
Rewrite using `[graphIdeal, Ideal.mem_comap, graphHom_X_last]`. Conclude with `hp`.
-/
theorem X_last_not_mem_graphIdeal {J : Ideal (MvPolynomial (Fin n) ℂ)} {p : MvPolynomial (Fin n) ℂ} (hp : p ∉ J) :
    X (Fin.last n) ∉ graphIdeal J p := by
  rw [graphIdeal, Ideal.mem_comap, graphHom_X_last]
  exact hp

/- English proof (translation)
Establish `hs` using `graphHom_surjective p`. Establish `hmap : (graphIdeal J p ⊔ Ideal.span {X (Fin.last n)}).map (graphHom p) = J ⊔ Ideal.span {p}`. Rewrite using `[Ideal.map_sup, graphIdeal, Ideal.map_comap_of_surjective _ hs, Ideal.map_span, Set.image_singleton, graphHom_X_last]`. Rewrite using `[← hmap]`. Use `show _ = Ideal.comap (graphHom p) (Ideal.map (graphHom p) _)`.

Rewrite using `[Ideal.comap_map_of_surjective _ hs]`. Use `(sup_eq_left.mpr ?_).symm` and prove the remaining obligations. Conclude with `le_sup_of_le_left (Ideal.comap_mono bot_le)`.
-/
theorem graphIdeal_sup_span (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : MvPolynomial (Fin n) ℂ) :
    graphIdeal J p ⊔ Ideal.span {X (Fin.last n)} = graphIdeal (J ⊔ Ideal.span {p}) p := by
  have hs := graphHom_surjective p
  have hmap : (graphIdeal J p ⊔ Ideal.span {X (Fin.last n)}).map (graphHom p) = J ⊔ Ideal.span {p} := by
    rw [Ideal.map_sup, graphIdeal, Ideal.map_comap_of_surjective _ hs, Ideal.map_span, Set.image_singleton,
      graphHom_X_last]
  rw [← hmap]
  show _ = Ideal.comap (graphHom p) (Ideal.map (graphHom p) _)
  rw [Ideal.comap_map_of_surjective _ hs]
  refine (sup_eq_left.mpr ?_).symm
  exact le_sup_of_le_left (Ideal.comap_mono bot_le)

/- English proof (translation)
Rewrite using `[graphIdeal_sup_span, graphIdeal]`. Conclude with `Ideal.comap_minimalPrimes_eq_of_surjective (graphHom_surjective p) _`.
-/
theorem minimalPrimes_graphIdeal_sup (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : MvPolynomial (Fin n) ℂ) :
    (graphIdeal J p ⊔ Ideal.span {X (Fin.last n)}).minimalPrimes =
      (fun W => graphIdeal W p) '' (J ⊔ Ideal.span {p}).minimalPrimes := by
  rw [graphIdeal_sup_span, graphIdeal]
  exact Ideal.comap_minimalPrimes_eq_of_surjective (graphHom_surjective p) _

/- English proof (translation)
The claim follows from `Ideal.comap_injective_of_surjective _ (graphHom_surjective p)`.
-/
theorem graphIdeal_injective (p : MvPolynomial (Fin n) ℂ) : Function.Injective (fun W => graphIdeal W p) :=
  Ideal.comap_injective_of_surjective _ (graphHom_surjective p)

/- English proof (translation)
The claim follows from `Ideal.comap_mono h`.
-/
theorem graphIdeal_mono {J W : Ideal (MvPolynomial (Fin n) ℂ)} (p : MvPolynomial (Fin n) ℂ) (h : J ≤ W) :
    graphIdeal J p ≤ graphIdeal W p :=
  Ideal.comap_mono h

end GroundTheory.Heights₂.Heights.Targets
