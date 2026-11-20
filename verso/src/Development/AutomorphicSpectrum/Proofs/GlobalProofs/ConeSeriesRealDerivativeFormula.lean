import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum

set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DerivDLR

variable {ι : Type} [Fintype ι] [DecidableEq ι] {r : ℕ}

/- English proof (translation)
Establish `h : ∀ k, a j k * (x + t • (Pi.single i 1 : Fin r → ℝ)) k = a j k * x k + (if k = i then t * a j i else 0)`. Introduce `k`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Simplify using `[Pi.single_apply, hk]`. Simplify using `only [linF, h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma linF_line (a : ι → Fin r → ℝ) (b : ι → ℝ) (j : ι) (x : Fin r → ℝ) (i : Fin r) (t : ℝ) :
    linF a b j (x + t • (Pi.single i 1 : Fin r → ℝ)) = linF a b j x + t * a j i := by
  have h : ∀ k, a j k * (x + t • (Pi.single i 1 : Fin r → ℝ)) k
      = a j k * x k + (if k = i then t * a j i else 0) := by
    intro k
    by_cases hk : k = i
    · subst hk; simp; ring
    · simp [Pi.single_apply, hk]
  simp only [linF, h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/- English proof (translation)
Establish `: 0 ≤ ∑ i, a j i * y i` using `Finset.sum_nonneg fun i _ => mul_nonneg (ha j i).le (hy i)`. Use `hb j` as an intermediate fact. Unfold `linF`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma linF_pos (a : ι → Fin r → ℝ) (b : ι → ℝ) (ha : ∀ j i, 0 < a j i) (hb : ∀ j, 0 < b j)
    (j : ι) (y : Fin r → ℝ) (hy : ∀ k, 0 ≤ y k) : 0 < linF a b j y := by
  have : 0 ≤ ∑ i, a j i * y i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (ha j i).le (hy i)
  have := hb j
  unfold linF
  linarith

/- English proof (translation)
Establish `hlin : HasDerivAt (fun t : ℝ => linF a b j (x + t • (Pi.single i 1 : Fin r → ℝ))) (a j i) τ`. Establish `: (fun t : ℝ => linF a b j (x + t • (Pi.single i 1 : Fin r → ℝ))) = fun t : ℝ => linF a b j x + t * a j i`. Use function extensionality and compare the values at `t`. Conclude with `linF_line a b j x i t`. Rewrite using `[this]`.

Simplify using `using ((hasDerivAt_id τ).mul_const (a j i)).const_add (linF a b j x)`. Establish `hC` using `hlin.ofReal_comp`. Establish `hslit : ((linF a b j (x + τ • (Pi.single i 1 : Fin r → ℝ)) : ℝ) : ℂ) ∈ Complex.slitPlane` using `Complex.ofReal_mem_slitPlane.2 hpos`. Establish `hpow` using `((hasDerivAt_id _).cpow_const (c := w) hslit)`. Use `(HasDerivAt.scomp τ hpow hC).congr_deriv ?_` and prove the remaining obligations.

Simplify using `only [id, mul_one, smul_eq_mul]`. Both sides reduce to the same expression.
-/
lemma hasDerivAt_factor (a : ι → Fin r → ℝ) (b : ι → ℝ) (w : ℂ) (j : ι) (i : Fin r)
    (x : Fin r → ℝ) (τ : ℝ)
    (hpos : 0 < linF a b j (x + τ • (Pi.single i 1 : Fin r → ℝ))) :
    HasDerivAt (fun t : ℝ => ((linF a b j (x + t • (Pi.single i 1 : Fin r → ℝ)) : ℝ) : ℂ) ^ w)
      ((a j i : ℂ) * (w * ((linF a b j (x + τ • (Pi.single i 1 : Fin r → ℝ)) : ℝ) : ℂ) ^ (w - 1))) τ := by
  have hlin : HasDerivAt (fun t : ℝ => linF a b j (x + t • (Pi.single i 1 : Fin r → ℝ))) (a j i) τ := by
    have : (fun t : ℝ => linF a b j (x + t • (Pi.single i 1 : Fin r → ℝ)))
        = fun t : ℝ => linF a b j x + t * a j i := by
      funext t; exact linF_line a b j x i t
    rw [this]
    simpa using ((hasDerivAt_id τ).mul_const (a j i)).const_add (linF a b j x)
  have hC := hlin.ofReal_comp
  have hslit : ((linF a b j (x + τ • (Pi.single i 1 : Fin r → ℝ)) : ℝ) : ℂ) ∈ Complex.slitPlane :=
    Complex.ofReal_mem_slitPlane.2 hpos
  have hpow := ((hasDerivAt_id _).cpow_const (c := w) hslit)
  refine (HasDerivAt.scomp τ hpow hC).congr_deriv ?_
  simp only [id, mul_one, smul_eq_mul]
  rfl

/- English proof (translation)
Establish `hprod` using `HasDerivAt.fun_finset_prod (u := Finset.univ) (f := fun j (t : ℝ) => ((linF a b j (x + t • (Pi.single i 1 : Fin r → ℝ)) : ℝ) : ℂ) ^ (-s - (β j : ℂ))) (x := τ) (fun j _ => hasDerivAt_factor a b (-s - (β j : ℂ)) j i x τ (linF_pos a b ha hb j _ hy))`. Use `hprod.congr_deriv ?_` and prove the remaining obligations. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `hF : Fr a b s (β + Pi.single j 1) (x + τ • (Pi.single i 1 : Fin r → ℝ)) = ((linF a b j (x + τ • (Pi.single i 1 : Fin r → ℝ)) : ℝ) : ℂ) ^ (-s - (β j : ℂ) - 1) * ∏ k ∈ Finset.univ.erase j, ((linF a b k (x + τ • (Pi.single i 1 : Fin r → ℝ)) : ℝ) : ℂ) ^ (-s - (β k : ℂ))`. Unfold `Fr`.

Rewrite using `[← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]`. Use `congr 1`. Use `congr 1`. Simplify using `only [Pi.add_apply, Pi.single_eq_same]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Use `Finset.prod_congr rfl fun k hk => ?_` and prove the remaining obligations. Establish `hkj : k ≠ j` using `Finset.ne_of_mem_erase hk`. Simplify using `[Pi.single_apply, hkj]`. Rewrite using `[hF, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma hasDerivAt_Fr (a : ι → Fin r → ℝ) (b : ι → ℝ) (ha : ∀ j i, 0 < a j i) (hb : ∀ j, 0 < b j)
    (s : ℂ) (β : ι → ℕ) (i : Fin r) (x : Fin r → ℝ) (τ : ℝ)
    (hy : ∀ k, 0 ≤ (x + τ • (Pi.single i 1 : Fin r → ℝ)) k) :
    HasDerivAt (fun t : ℝ => Fr a b s β (x + t • (Pi.single i 1 : Fin r → ℝ)))
      (∑ j, (-s - (β j : ℂ)) * (a j i : ℂ) *
        Fr a b s (β + Pi.single j 1) (x + τ • (Pi.single i 1 : Fin r → ℝ))) τ := by
  have hprod := HasDerivAt.fun_finset_prod (u := Finset.univ)
    (f := fun j (t : ℝ) => ((linF a b j (x + t • (Pi.single i 1 : Fin r → ℝ)) : ℝ) : ℂ) ^ (-s - (β j : ℂ)))
    (x := τ)
    (fun j _ => hasDerivAt_factor a b (-s - (β j : ℂ)) j i x τ (linF_pos a b ha hb j _ hy))
  refine hprod.congr_deriv ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  have hF : Fr a b s (β + Pi.single j 1) (x + τ • (Pi.single i 1 : Fin r → ℝ))
      = ((linF a b j (x + τ • (Pi.single i 1 : Fin r → ℝ)) : ℝ) : ℂ) ^ (-s - (β j : ℂ) - 1) *
        ∏ k ∈ Finset.univ.erase j,
          ((linF a b k (x + τ • (Pi.single i 1 : Fin r → ℝ)) : ℝ) : ℂ) ^ (-s - (β k : ℂ)) := by
    unfold Fr
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    congr 1
    · congr 1
      simp only [Pi.add_apply, Pi.single_eq_same]
      push_cast
      ring
    · refine Finset.prod_congr rfl fun k hk => ?_
      have hkj : k ≠ j := Finset.ne_of_mem_erase hk
      simp [Pi.single_apply, hkj]
  rw [hF, smul_eq_mul]
  ring

/- English proof (translation)
Proceed by induction on `cs generalizing x with`. Consider the case `nil`. Establish `hy : ∀ k, 0 ≤ (x + τ • (Pi.single i 1 : Fin r → ℝ)) k`. Introduce `k`. Establish `: 0 ≤ τ * (Pi.single i 1 : Fin r → ℝ) k`.

Use `mul_nonneg hτ ?_` and prove the remaining obligations. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hk]`.

Simplify using `using add_nonneg (hx k) this`. Simplify `hasDerivAt_Fr a b ha hb s β i x τ hy` using `[DLR]`. Consider the case `cons c cs ih`. Establish `hxc : ∀ k, 0 ≤ (x + (Pi.single c 1 : Fin r → ℝ)) k`. Introduce `k`.

Establish `: 0 ≤ (Pi.single c 1 : Fin r → ℝ) k`. Distinguish the cases in `hk : k = c`. Substitute `hk` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hk]`.

Simplify using `using add_nonneg (hx k) this`. Establish `hsw : ∀ (G : (Fin r → ℝ) → ℂ) (t : ℝ), DLR (c :: cs) G (x + t • (Pi.single i 1 : Fin r → ℝ)) = DLR cs G ((x + (Pi.single c 1 : Fin r → ℝ)) + t • (Pi.single i 1 : Fin r → ℝ)) - DLR cs G (x + t • (Pi.single i 1 : Fin r → ℝ))`. Introduce `G t`. Establish `: x + t • (Pi.single i 1 : Fin r → ℝ) + (Pi.single c 1 : Fin r → ℝ) = (x + (Pi.single c 1 : Fin r → ℝ)) + t • (Pi.single i 1 : Fin r → ℝ)` using `by abel`. Express the relevant statement in the definitionally equal form `fdR c (DLR cs G) _ = _`.

Simplify using `only [fdR, this]`. Establish `h` using `(ih (x + Pi.single c 1) hxc).sub (ih x hx)`. Use `(h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => hsw _ t)` and prove the remaining obligations. Rewrite using `[← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[hsw, mul_sub]`.
-/
theorem hasDerivAt_DLR_Fr (ι : Type) [Fintype ι] [DecidableEq ι] (r : ℕ) (a : ι → Fin r → ℝ)
    (b : ι → ℝ) (ha : ∀ j i, 0 < a j i) (hb : ∀ j, 0 < b j)
    (s : ℂ) (β : ι → ℕ) (cs : List (Fin r)) (i : Fin r) (x : Fin r → ℝ) (τ : ℝ)
    (hx : ∀ k, 0 ≤ x k) (hτ : 0 ≤ τ) :
    HasDerivAt (fun t : ℝ => DLR cs (Fr a b s β) (x + t • (Pi.single i 1 : Fin r → ℝ)))
      (∑ j, (-s - (β j : ℂ)) * (a j i : ℂ) *
        DLR cs (Fr a b s (β + Pi.single j 1)) (x + τ • (Pi.single i 1 : Fin r → ℝ))) τ := by
  induction cs generalizing x with
  | nil =>
    have hy : ∀ k, 0 ≤ (x + τ • (Pi.single i 1 : Fin r → ℝ)) k := by
      intro k
      have : 0 ≤ τ * (Pi.single i 1 : Fin r → ℝ) k := by
        refine mul_nonneg hτ ?_
        by_cases hk : k = i
        · subst hk; simp
        · simp [Pi.single_apply, hk]
      simpa using add_nonneg (hx k) this
    simpa [DLR] using hasDerivAt_Fr a b ha hb s β i x τ hy
  | cons c cs ih =>
    have hxc : ∀ k, 0 ≤ (x + (Pi.single c 1 : Fin r → ℝ)) k := by
      intro k
      have : 0 ≤ (Pi.single c 1 : Fin r → ℝ) k := by
        by_cases hk : k = c
        · subst hk; simp
        · simp [Pi.single_apply, hk]
      simpa using add_nonneg (hx k) this
    have hsw : ∀ (G : (Fin r → ℝ) → ℂ) (t : ℝ),
        DLR (c :: cs) G (x + t • (Pi.single i 1 : Fin r → ℝ))
          = DLR cs G ((x + (Pi.single c 1 : Fin r → ℝ)) + t • (Pi.single i 1 : Fin r → ℝ))
            - DLR cs G (x + t • (Pi.single i 1 : Fin r → ℝ)) := by
      intro G t
      have : x + t • (Pi.single i 1 : Fin r → ℝ) + (Pi.single c 1 : Fin r → ℝ)
          = (x + (Pi.single c 1 : Fin r → ℝ)) + t • (Pi.single i 1 : Fin r → ℝ) := by abel
      change fdR c (DLR cs G) _ = _
      simp only [fdR, this]
    have h := (ih (x + Pi.single c 1) hxc).sub (ih x hx)
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => hsw _ t)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hsw, mul_sub]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DerivDLR
