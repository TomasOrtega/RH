import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ExistsFunFieldMulEq
import GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsHorizontalOfDimOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

namespace regularityEmbedding_holds

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

abbrev toFrac (P : Ideal (MRing ι)) : MRing ι →+* FractionRing (MRing ι ⧸ P) :=
  (algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P))).comp (Ideal.Quotient.mk P)

omit [Fintype K] [∀ k, Fintype (ι k)] in
/- English proof (translation)
Rewrite using `[RingHom.comp_apply, ← map_zero (algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P))), (IsFractionRing.injective (MRing ι ⧸ P) _).eq_iff, Ideal.Quotient.eq_zero_iff_mem]`.
-/
theorem toFrac_eq_zero {P : Ideal (MRing ι)} [P.IsPrime] {f : MRing ι} : toFrac P f = 0 ↔ f ∈ P := by
  rw [RingHom.comp_apply, ← map_zero (algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P))),
    (IsFractionRing.injective (MRing ι ⧸ P) _).eq_iff, Ideal.Quotient.eq_zero_iff_mem]

omit [Fintype K] in

/- English proof (translation)
Introduce `m hm k'`. Rewrite `hm` using `[MvPolynomial.support_X, Finset.mem_singleton]`. Substitute `hm` using the available equality. Distinguish the cases in `h : k' = k`. Substitute `h classical` using the available equality.

Simplify using `[Finsupp.single_apply]`. Establish `: ∀ j : ι k', (⟨k, i⟩ : Σ k, ι k) ≠ ⟨k', j⟩` using `fun j e => h (congrArg Sigma.fst e).symm classical`. Simplify using `[Finsupp.single_apply, this, h, Pi.single_apply]`.
-/
theorem isMultiHomog_X_single [DecidableEq K] (k : K) (i : ι k) :
    IsMultiHomog (X ⟨k, i⟩ : MRing ι) (Pi.single k 1) := by
  intro m hm k'
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
  subst hm
  by_cases h : k' = k
  · subst h
    classical
    simp [Finsupp.single_apply]
  · have : ∀ j : ι k', (⟨k, i⟩ : Σ k, ι k) ≠ ⟨k', j⟩ := fun j e => h (congrArg Sigma.fst e).symm
    classical
    simp [Finsupp.single_apply, this, h, Pi.single_apply]

def formSub (P : Ideal (MRing ι)) : Submonoid (MRing ι ⧸ P) :=
  Submonoid.closure {y | ∃ (v : MRing ι) (a : K → ℕ), IsMultiHomog v a ∧ v ∉ P ∧ Ideal.Quotient.mk P v = y}

omit [Fintype K] in
/- English proof (translation)
Use `Submonoid.closure_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨v, a, -, hv, rfl⟩`. Conclude with `mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])`.
-/
theorem formSub_le (P : Ideal (MRing ι)) [P.IsPrime] : formSub P ≤ nonZeroDivisors (MRing ι ⧸ P) := by
  refine Submonoid.closure_le.mpr ?_
  rintro _ ⟨v, a, -, hv, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])

abbrev locForms (P : Ideal (MRing ι)) [P.IsPrime] :
    Subalgebra (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) :=
  Localization.subalgebra (FractionRing (MRing ι ⧸ P)) (formSub P) (formSub_le P)

omit [Fintype K] [∀ k, Fintype (ι k)] in
/- English proof (translation)
Introduce `h` and use `nonZeroDivisors.ne_zero hv (Ideal.Quotient.eq_zero_iff_mem.mpr h)`.
-/
theorem not_mem_of_nonZeroDivisor {P : Ideal (MRing ι)} [P.IsPrime] {v : MRing ι}
    (hv : Ideal.Quotient.mk P v ∈ nonZeroDivisors (MRing ι ⧸ P)) : v ∉ P := fun h =>
  nonZeroDivisors.ne_zero hv (Ideal.Quotient.eq_zero_iff_mem.mpr h)

/- English proof (translation)
Use `Subring.closure_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨u, v, a, hv, -, hva, rfl⟩`. Conclude with `⟨Ideal.Quotient.mk P u, Ideal.Quotient.mk P v, Submonoid.subset_closure ⟨v, a, hva, not_mem_of_nonZeroDivisor hv, rfl⟩, rfl⟩`.
-/
theorem funField_le (P : Ideal (MRing ι)) [P.IsPrime] : funField P ≤ (locForms P).toSubring := by
  refine Subring.closure_le.mpr ?_
  rintro _ ⟨u, v, a, hv, -, hva, rfl⟩
  exact ⟨Ideal.Quotient.mk P u, Ideal.Quotient.mk P v,
    Submonoid.subset_closure ⟨v, a, hva, not_mem_of_nonZeroDivisor hv, rfl⟩, rfl⟩

def evalQ (P : Ideal (MRing ι)) (t : (Σ k, ι k) → ℂ) (ht : t ∈ mcPts P) : MRing ι ⧸ P →+* ℂ :=
  Ideal.Quotient.lift P ((eval t).comp (map (Int.castRingHom ℂ))) fun f hf => ht.2 f hf

omit [Fintype K] [∀ k, Fintype (ι k)] in
/- English proof (translation)
The claim follows from `Ideal.Quotient.lift_mk _ _ _`.
-/
theorem evalQ_mk {P : Ideal (MRing ι)} {t : (Σ k, ι k) → ℂ} (ht : t ∈ mcPts P) (f : MRing ι) :
    evalQ P t ht (Ideal.Quotient.mk P f) = eval t (map (Int.castRingHom ℂ) f) :=
  Ideal.Quotient.lift_mk _ _ _

/- English proof (translation)
Take `⟨y, hy⟩` from `y`. Proceed by induction on `hy using Submonoid.closure_induction with`. Consider the case `mem x hx`. Take `⟨v, a, hva, hvP, rfl⟩` from `hx`. Rewrite using `[evalQ_mk]`.

Conclude with `isUnit_iff_ne_zero.mpr (hne v a hva hvP)`. Consider the case `one => simp`. Consider the case `mul x y _ _ hx hy`. Rewrite using `[map_mul]`. Conclude with `hx.mul hy`.
-/
theorem isUnit_evalQ {P : Ideal (MRing ι)} {t : (Σ k, ι k) → ℂ} (ht : t ∈ mcPts P)
    (hne : ∀ (v : MRing ι) (a : K → ℕ), IsMultiHomog v a → v ∉ P → eval t (map (Int.castRingHom ℂ) v) ≠ 0)
    (y : formSub P) : IsUnit (evalQ P t ht y) := by
  obtain ⟨y, hy⟩ := y
  induction hy using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨v, a, hva, hvP, rfl⟩ := hx
    rw [evalQ_mk]
    exact isUnit_iff_ne_zero.mpr (hne v a hva hvP)
  | one => simp
  | mul x y _ _ hx hy =>
    rw [map_mul]
    exact hx.mul hy

def sigmaAt (P : Ideal (MRing ι)) [P.IsPrime] (t : (Σ k, ι k) → ℂ) (ht : t ∈ mcPts P)
    (hne : ∀ (v : MRing ι) (a : K → ℕ), IsMultiHomog v a → v ∉ P → eval t (map (Int.castRingHom ℂ) v) ≠ 0) :
    funField P →+* ℂ :=
  (IsLocalization.lift (M := formSub P) (S := locForms P) (isUnit_evalQ ht hne)).comp
    (Subring.inclusion (funField_le P))

/- English proof (translation)
Establish `key : (Subring.inclusion (funField_le P) x : locForms P) * algebraMap (MRing ι ⧸ P) (locForms P) (Ideal.Quotient.mk P v) = algebraMap (MRing ι ⧸ P) (locForms P) (Ideal.Quotient.mk P u)` using `Subtype.ext hx`. Use `congrArg (IsLocalization.lift (M := formSub P) (S := locForms P) (isUnit_evalQ ht hne)) key` as an intermediate fact. Rewrite `this` using `[map_mul, IsLocalization.lift_eq, IsLocalization.lift_eq, evalQ_mk, evalQ_mk]`. Conclude with `this`.
-/
theorem sigmaAt_spec {P : Ideal (MRing ι)} [P.IsPrime] {t : (Σ k, ι k) → ℂ} (ht : t ∈ mcPts P)
    (hne : ∀ (v : MRing ι) (a : K → ℕ), IsMultiHomog v a → v ∉ P → eval t (map (Int.castRingHom ℂ) v) ≠ 0)
    (x : funField P) {u v : MRing ι}
    (hx : (x : FractionRing (MRing ι ⧸ P)) * toFrac P v = toFrac P u) :
    sigmaAt P t ht hne x * eval t (map (Int.castRingHom ℂ) v) = eval t (map (Int.castRingHom ℂ) u) := by
  have key : (Subring.inclusion (funField_le P) x : locForms P) *
      algebraMap (MRing ι ⧸ P) (locForms P) (Ideal.Quotient.mk P v) =
      algebraMap (MRing ι ⧸ P) (locForms P) (Ideal.Quotient.mk P u) := Subtype.ext hx
  have := congrArg (IsLocalization.lift (M := formSub P) (S := locForms P) (isUnit_evalQ ht hne)) key
  rw [map_mul, IsLocalization.lift_eq, IsLocalization.lift_eq, evalQ_mk, evalQ_mk] at this
  exact this

/- English proof (translation)
Establish `hle : funField P ≤ (RingHom.eqLocus τ₁ τ₂).map (funField P).subtype`. Use `Subring.closure_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨u, v, a, hv, hu, hva, rfl⟩`. Conclude with `⟨⟨_, Subring.subset_closure ⟨u, v, a, hv, hu, hva, rfl⟩⟩, h _ u v a hu hva (not_mem_of_nonZeroDivisor hv) (IsLocalization.mk'_spec _ _ _), rfl⟩`. Use extensionality with `x`.

Take `⟨y, hy, hyx⟩` from `hle x.2`. Establish `: y = x` using `Subtype.ext hyx`. Substitute `this` using the available equality. Conclude with `hy`.
-/
theorem funField_hom_ext {P : Ideal (MRing ι)} [P.IsPrime] {τ₁ τ₂ : funField P →+* ℂ}
    (h : ∀ (x : funField P) (u v : MRing ι) (a : K → ℕ), IsMultiHomog u a → IsMultiHomog v a → v ∉ P →
      (x : FractionRing (MRing ι ⧸ P)) * toFrac P v = toFrac P u → τ₁ x = τ₂ x) : τ₁ = τ₂ := by
  have hle : funField P ≤ (RingHom.eqLocus τ₁ τ₂).map (funField P).subtype := by
    refine Subring.closure_le.mpr ?_
    rintro _ ⟨u, v, a, hv, hu, hva, rfl⟩
    exact ⟨⟨_, Subring.subset_closure ⟨u, v, a, hv, hu, hva, rfl⟩⟩,
      h _ u v a hu hva (not_mem_of_nonZeroDivisor hv) (IsLocalization.mk'_spec _ _ _), rfl⟩
  ext x
  obtain ⟨y, hy, hyx⟩ := hle x.2
  have : y = x := Subtype.ext hyx
  subst this
  exact hy

def chartHom {P : Ideal (MRing ι)} (r : (Σ k, ι k) → funField P) : MRing ι →+* funField P :=
  eval₂Hom (Int.castRingHom _) r

/- English proof (translation)
Establish `: (funField P).subtype.comp (chartHom r) = eval₂Hom (Int.castRingHom _) (fun p => (r p : FractionRing (MRing ι ⧸ P)))` using `MvPolynomial.ringHom_ext (fun n => by simp [chartHom]) (fun p => by simp [chartHom])`. Conclude with `congrArg (fun φ => φ f) this`.
-/
theorem chartHom_coe {P : Ideal (MRing ι)} (r : (Σ k, ι k) → funField P) (f : MRing ι) :
    (chartHom r f : FractionRing (MRing ι ⧸ P)) =
      eval₂Hom (Int.castRingHom _) (fun p => (r p : FractionRing (MRing ι ⧸ P))) f := by
  have : (funField P).subtype.comp (chartHom r) =
      eval₂Hom (Int.castRingHom _) (fun p => (r p : FractionRing (MRing ι ⧸ P))) :=
    MvPolynomial.ringHom_ext (fun n => by simp [chartHom]) (fun p => by simp [chartHom])
  exact congrArg (fun φ => φ f) this

/- English proof (translation)
Establish `: τ.comp (chartHom r) = (eval (fun p => τ (r p))).comp (map (Int.castRingHom ℂ))` using `MvPolynomial.ringHom_ext (fun n => by simp [chartHom]) (fun p => by simp [chartHom])`. Conclude with `congrArg (fun φ => φ f) this`.
-/
theorem chart_eval {P : Ideal (MRing ι)} (τ : funField P →+* ℂ) (r : (Σ k, ι k) → funField P)
    (f : MRing ι) : τ (chartHom r f) = eval (fun p => τ (r p)) (map (Int.castRingHom ℂ) f) := by
  have : τ.comp (chartHom r) = (eval (fun p => τ (r p))).comp (map (Int.castRingHom ℂ)) :=
    MvPolynomial.ringHom_ext (fun n => by simp [chartHom]) (fun p => by simp [chartHom])
  exact congrArg (fun φ => φ f) this

/- English proof (translation)
Simplify using `only [map_prod, map_pow]`. Conclude with `Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ fun h => hj k (toFrac_eq_zero.mp h)`.
-/
theorem toFrac_prod_ne_zero {P : Ideal (MRing ι)} [P.IsPrime] (j : ∀ k, ι k)
    (hj : ∀ k, (X ⟨k, j k⟩ : MRing ι) ∉ P) (a : K → ℕ) :
    toFrac P (∏ k, (X ⟨k, j k⟩ : MRing ι) ^ a k) ≠ 0 := by
  simp only [map_prod, map_pow]
  exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ fun h => hj k (toFrac_eq_zero.mp h)

/- English proof (translation)
Rewrite using `[chartHom_coe]`. Use `conv_lhs => rw [f.as_sum]`. Use `conv_rhs => rw [f.as_sum]`. Rewrite using `[map_sum, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun μ hμ => ?_` and prove the remaining obligations.

Establish `hdeg` using `hf μ hμ`. Rewrite using `[monomial_eq, map_mul, map_mul, mul_assoc]`. Use `congr 1`. Simplify using the standard rewrite rules. Rewrite using `[Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]`.

Simplify using `only [map_prod, map_pow, coe_eval₂Hom, eval₂_X]`. Establish `hm : ∏ k, toFrac P (X ⟨k, j k⟩) ^ a k = ∏ p : Σ k, ι k, toFrac P (X ⟨p.1, j p.1⟩) ^ μ p`. Rewrite using `[Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← hdeg k]`.

Conclude with `(Finset.prod_pow_eq_pow_sum _ _ _).symm`. Rewrite using `[hm, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_pow, hr]`.
-/
theorem chartHom_mul {P : Ideal (MRing ι)} (j : ∀ k, ι k) (r : (Σ k, ι k) → funField P)
    (hr : ∀ p : Σ k, ι k, (r p : FractionRing (MRing ι ⧸ P)) * toFrac P (X ⟨p.1, j p.1⟩) = toFrac P (X p))
    {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) :
    (chartHom r f : FractionRing (MRing ι ⧸ P)) * toFrac P (∏ k, (X ⟨k, j k⟩ : MRing ι) ^ a k) = toFrac P f := by
  classical
  rw [chartHom_coe]
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hdeg := hf μ hμ
  rw [monomial_eq, map_mul, map_mul, mul_assoc]
  congr 1
  · simp
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [map_prod, map_pow, coe_eval₂Hom, eval₂_X]
  have hm : ∏ k, toFrac P (X ⟨k, j k⟩) ^ a k = ∏ p : Σ k, ι k, toFrac P (X ⟨p.1, j p.1⟩) ^ μ p := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← hdeg k]
    exact (Finset.prod_pow_eq_pow_sum _ _ _).symm
  rw [hm, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [← mul_pow, hr]

end regularityEmbedding_holds

open regularityEmbedding_holds in

/- English proof (translation)
Introduce `K _ ι _ P R hP hR hRu`. Establish `: P.IsPrime` using `hP.2.1.1`. Establish `hne : ∀ t ∈ mcPts P, ∀ (v : MRing ι) (a : K → ℕ), IsMultiHomog v a → v ∉ P → eval t (map (Int.castRingHom ℂ) v) ≠ 0` using `fun t ht v a hv hvP => eval_ne_zero_of_dimOne arithVarZero hP (A := HermLine.ofMetrics (fun k => fsMetric (ι k)) (fun k => (a k : ℤ))) ⟨a, fun _ => rfl, hv, hvP⟩ ht`. Set `σ : R → (funField P →+* ℂ)` to `fun t => sigmaAt P (t : (Σ k, ι k) → ℂ) (hR t t.2) (hne t (hR t t.2))`. Establish `hσ : ∀ (t : R) (x : funField P) (u v : MRing ι), (x : FractionRing (MRing ι ⧸ P)) * toFrac P v = toFrac P u → σ t x * eval (t : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) v) = eval (t : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) u)` using `fun t x u v hx => sigmaAt_spec (hR t t.2) (hne t (hR t t.2)) x hx`.

Establish `hratio : ∀ (t : R) (k : K) (i i0 : ι k) (x : funField P), (x : FractionRing (MRing ι ⧸ P)) * toFrac P (X ⟨k, i0⟩) = toFrac P (X ⟨k, i⟩) → σ t x * (t : (Σ k, ι k) → ℂ) ⟨k, i0⟩ = (t : (Σ k, ι k) → ℂ) ⟨k, i⟩`. Introduce `t k i i0 x hx`. Simplify using `using hσ t x _ _ hx`. Establish `hinj : Function.Injective σ`. Introduce `t s hts`.

Establish `hc : ∀ k, ∃ c : ℂ, c ≠ 0 ∧ ∀ i, (t : (Σ k, ι k) → ℂ) ⟨k, i⟩ = c * (s : (Σ k, ι k) → ℂ) ⟨k, i⟩`. Introduce `k`. Take `⟨i0, hi0⟩` from `(hR t t.2).1 k`. Establish `hXP : (X ⟨k, i0⟩ : MRing ι) ∉ P` using `fun h => hi0 (by simpa using (hR t t.2).2 _ h)`. Establish `hs0 : (s : (Σ k, ι k) → ℂ) ⟨k, i0⟩ ≠ 0`.

Simplify using `using hne s (hR s s.2) _ _ (isMultiHomog_X_single k i0) hXP`. Use `⟨(t : (Σ k, ι k) → ℂ) ⟨k, i0⟩ / (s : (Σ k, ι k) → ℂ) ⟨k, i0⟩, div_ne_zero hi0 hs0, fun i => ?_⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `exists_funField_mul_eq (isMultiHomog_X_single k i) (isMultiHomog_X_single k i0) hXP`. Establish `h1` using `hratio t k i i0 x hx`. Establish `h2` using `hratio s k i i0 x hx`.

Rewrite `h1` using `[hts]`. Rewrite using `[← h1, ← h2, div_mul_eq_mul_div, eq_div_iff hs0]`. Expand and normalize the polynomial expressions, which then agree. Use `choose c hc0 hc using hc`. Establish `hSO : SameOrbit (t : (Σ k, ι k) → ℂ) (s : (Σ k, ι k) → ℂ)` using `⟨c, hc0, funext fun p => hc p.1 p.2⟩`.

Establish `hSO' : SameOrbit (t : (Σ k, ι k) → ℂ) (t : (Σ k, ι k) → ℂ)` using `⟨fun _ => 1, fun _ => one_ne_zero, by simp⟩`. Conclude with `Subtype.ext ((hRu t (hR t t.2)).unique ⟨t.2, hSO'⟩ ⟨s.2, hSO⟩)`. Establish `hsurj : Function.Surjective σ`. Introduce `τ`. Use `choose j hj using hP.2.1.2.2`.

Establish `hr : ∀ p : Σ k, ι k, ∃ x : funField P, (x : FractionRing (MRing ι ⧸ P)) * toFrac P (X ⟨p.1, j p.1⟩) = toFrac P (X p)` using `fun p => exists_funField_mul_eq (isMultiHomog_X_single p.1 p.2) (isMultiHomog_X_single p.1 (j p.1)) (hj p.1)`. Use `choose r hr using hr`. Establish `hrj : ∀ k, r ⟨k, j k⟩ = 1` using `fun k => by`. Establish `h0 : toFrac P (X ⟨k, j k⟩) ≠ 0` using `fun h => hj k (toFrac_eq_zero.mp h)`. Conclude with `Subtype.ext (mul_right_cancel₀ h0 ((hr ⟨k, j k⟩).trans (one_mul _).symm))`.

Use `set z : (Σ k, ι k) → ℂ := fun p => τ (r p) with hzdef`. Establish `hzj : ∀ k, z ⟨k, j k⟩ = 1` using `fun k => by simp [z, hrj]`. Establish `hz : z ∈ mcPts P`. Use `⟨fun k => ⟨j k, by rw [hzj]; exact one_ne_zero⟩, fun f hf => ?_⟩` and prove the remaining obligations. Take `⟨S, hS, hPS⟩` from `hP.2.1.2.1`.

Establish `hle : Ideal.span S ≤ RingHom.ker (τ.comp (chartHom r))`. Use `Ideal.span_le.mpr fun g hg => ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `hS g hg`. Establish `hgP : g ∈ P` using `by rw [hPS]; exact Ideal.subset_span hg`. Establish `h1` using `chartHom_mul j r hr ha`.

Rewrite `h1` using `[toFrac_eq_zero.mpr hgP]`. Establish `hφ : chartHom r g = 0` using `Subtype.ext ((mul_eq_zero.mp h1).resolve_right (toFrac_prod_ne_zero j hj a))`. Rewrite using `[SetLike.mem_coe, RingHom.mem_ker, RingHom.comp_apply, hφ, map_zero]`. Rewrite `hf` using `[hPS]`. Use `hle hf` as an intermediate fact.

Rewrite `this` using `[RingHom.mem_ker, RingHom.comp_apply, chart_eval]`. Conclude with `this`. Take `⟨t, ⟨htR, hzt⟩, -⟩` from `hRu z hz`. Use `⟨⟨t, htR⟩, ?_⟩` and prove the remaining obligations. Take `⟨c, -, hczt⟩` from `hzt`.

Establish `hσr : ∀ p, σ ⟨t, htR⟩ (r p) = z p`. Introduce `p`. Establish `h1` using `hratio ⟨t, htR⟩ p.1 p.2 (j p.1) (r p) (hr p)`. Establish `hzp` using `congrFun hczt p`. Establish `hzj'` using `congrFun hczt ⟨p.1, j p.1⟩`.

Rewrite `hzj'` using `[hzj]`. Simplify using `only at h1 hzp hzj'`. Rewrite using `[hzp, ← h1]`. Combine the equalities or inequalities in the displayed calculation. Establish `hagree : ∀ f, σ ⟨t, htR⟩ (chartHom r f) = τ (chartHom r f)`.

Introduce `f`. Rewrite using `[chart_eval, chart_eval]`. Conclude with `congrArg (fun w => eval w (map (Int.castRingHom ℂ) f)) (funext hσr)`. Use `funField_hom_ext fun x u v a hu hv hvP hx => ?_` and prove the remaining obligations. Establish `hxφ : x * chartHom r v = chartHom r u`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `mul_right_cancel₀ (toFrac_prod_ne_zero j hj a)` to reduce the goal to its premises. Rewrite using `[Subring.coe_mul, mul_assoc, chartHom_mul j r hr hv, hx, chartHom_mul j r hr hu]`. Establish `hv0 : τ (chartHom r v) ≠ 0`. Rewrite using `[chart_eval]`.

Conclude with `hne z hz v a hv hvP`. Establish `e1` using `congrArg (σ ⟨t, htR⟩) hxφ`. Establish `e2` using `congrArg τ hxφ`. Rewrite `e1`, `e2` using `[map_mul]`. Rewrite `e1` using `[hagree, hagree]`.

Conclude with `mul_right_cancel₀ hv0 (e1.trans e2.symm)`. Conclude with `⟨Equiv.ofBijective σ ⟨hinj, hsurj⟩, fun t u v a _ _ _ x hx => hσ t x u v hx⟩`.
-/
theorem regularityEmbedding_holds.proof : regularityEmbedding_holds.Statement := by
  intro K _ ι _ P R hP hR hRu
  classical
  have : P.IsPrime := hP.2.1.1
  have hne : ∀ t ∈ mcPts P, ∀ (v : MRing ι) (a : K → ℕ), IsMultiHomog v a → v ∉ P →
      eval t (map (Int.castRingHom ℂ) v) ≠ 0 := fun t ht v a hv hvP =>
    eval_ne_zero_of_dimOne arithVarZero hP
      (A := HermLine.ofMetrics (fun k => fsMetric (ι k)) (fun k => (a k : ℤ))) ⟨a, fun _ => rfl, hv, hvP⟩ ht
  let σ : R → (funField P →+* ℂ) := fun t => sigmaAt P (t : (Σ k, ι k) → ℂ) (hR t t.2) (hne t (hR t t.2))
  have hσ : ∀ (t : R) (x : funField P) (u v : MRing ι),
      (x : FractionRing (MRing ι ⧸ P)) * toFrac P v = toFrac P u →
      σ t x * eval (t : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) v) =
        eval (t : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) u) :=
    fun t x u v hx => sigmaAt_spec (hR t t.2) (hne t (hR t t.2)) x hx

  have hratio : ∀ (t : R) (k : K) (i i0 : ι k) (x : funField P),
      (x : FractionRing (MRing ι ⧸ P)) * toFrac P (X ⟨k, i0⟩) = toFrac P (X ⟨k, i⟩) →
      σ t x * (t : (Σ k, ι k) → ℂ) ⟨k, i0⟩ = (t : (Σ k, ι k) → ℂ) ⟨k, i⟩ := by
    intro t k i i0 x hx
    simpa using hσ t x _ _ hx
  have hinj : Function.Injective σ := by
    intro t s hts
    have hc : ∀ k, ∃ c : ℂ, c ≠ 0 ∧ ∀ i, (t : (Σ k, ι k) → ℂ) ⟨k, i⟩ = c * (s : (Σ k, ι k) → ℂ) ⟨k, i⟩ := by
      intro k
      obtain ⟨i0, hi0⟩ := (hR t t.2).1 k
      have hXP : (X ⟨k, i0⟩ : MRing ι) ∉ P := fun h => hi0 (by simpa using (hR t t.2).2 _ h)
      have hs0 : (s : (Σ k, ι k) → ℂ) ⟨k, i0⟩ ≠ 0 := by
        simpa using hne s (hR s s.2) _ _ (isMultiHomog_X_single k i0) hXP
      refine ⟨(t : (Σ k, ι k) → ℂ) ⟨k, i0⟩ / (s : (Σ k, ι k) → ℂ) ⟨k, i0⟩, div_ne_zero hi0 hs0, fun i => ?_⟩
      obtain ⟨x, hx⟩ := exists_funField_mul_eq (isMultiHomog_X_single k i) (isMultiHomog_X_single k i0) hXP
      have h1 := hratio t k i i0 x hx
      have h2 := hratio s k i i0 x hx
      rw [hts] at h1
      rw [← h1, ← h2, div_mul_eq_mul_div, eq_div_iff hs0]
      ring
    choose c hc0 hc using hc
    have hSO : SameOrbit (t : (Σ k, ι k) → ℂ) (s : (Σ k, ι k) → ℂ) := ⟨c, hc0, funext fun p => hc p.1 p.2⟩
    have hSO' : SameOrbit (t : (Σ k, ι k) → ℂ) (t : (Σ k, ι k) → ℂ) :=
      ⟨fun _ => 1, fun _ => one_ne_zero, by simp⟩
    exact Subtype.ext ((hRu t (hR t t.2)).unique ⟨t.2, hSO'⟩ ⟨s.2, hSO⟩)
  have hsurj : Function.Surjective σ := by
    intro τ
    choose j hj using hP.2.1.2.2
    have hr : ∀ p : Σ k, ι k, ∃ x : funField P,
        (x : FractionRing (MRing ι ⧸ P)) * toFrac P (X ⟨p.1, j p.1⟩) = toFrac P (X p) := fun p =>
      exists_funField_mul_eq (isMultiHomog_X_single p.1 p.2) (isMultiHomog_X_single p.1 (j p.1)) (hj p.1)
    choose r hr using hr
    have hrj : ∀ k, r ⟨k, j k⟩ = 1 := fun k => by
      have h0 : toFrac P (X ⟨k, j k⟩) ≠ 0 := fun h => hj k (toFrac_eq_zero.mp h)
      exact Subtype.ext (mul_right_cancel₀ h0 ((hr ⟨k, j k⟩).trans (one_mul _).symm))
    set z : (Σ k, ι k) → ℂ := fun p => τ (r p) with hzdef
    have hzj : ∀ k, z ⟨k, j k⟩ = 1 := fun k => by simp [z, hrj]
    have hz : z ∈ mcPts P := by
      refine ⟨fun k => ⟨j k, by rw [hzj]; exact one_ne_zero⟩, fun f hf => ?_⟩
      obtain ⟨S, hS, hPS⟩ := hP.2.1.2.1
      have hle : Ideal.span S ≤ RingHom.ker (τ.comp (chartHom r)) := by
        refine Ideal.span_le.mpr fun g hg => ?_
        obtain ⟨a, ha⟩ := hS g hg
        have hgP : g ∈ P := by rw [hPS]; exact Ideal.subset_span hg
        have h1 := chartHom_mul j r hr ha
        rw [toFrac_eq_zero.mpr hgP] at h1
        have hφ : chartHom r g = 0 :=
          Subtype.ext ((mul_eq_zero.mp h1).resolve_right (toFrac_prod_ne_zero j hj a))
        rw [SetLike.mem_coe, RingHom.mem_ker, RingHom.comp_apply, hφ, map_zero]
      rw [hPS] at hf
      have := hle hf
      rw [RingHom.mem_ker, RingHom.comp_apply, chart_eval] at this
      exact this
    obtain ⟨t, ⟨htR, hzt⟩, -⟩ := hRu z hz
    refine ⟨⟨t, htR⟩, ?_⟩
    obtain ⟨c, -, hczt⟩ := hzt
    have hσr : ∀ p, σ ⟨t, htR⟩ (r p) = z p := by
      intro p
      have h1 := hratio ⟨t, htR⟩ p.1 p.2 (j p.1) (r p) (hr p)
      have hzp := congrFun hczt p
      have hzj' := congrFun hczt ⟨p.1, j p.1⟩
      rw [hzj] at hzj'
      simp only at h1 hzp hzj'
      rw [hzp, ← h1]
      calc σ ⟨t, htR⟩ (r p) = σ ⟨t, htR⟩ (r p) * (c p.1 * t ⟨p.1, j p.1⟩) := by rw [← hzj', mul_one]
        _ = c p.1 * (σ ⟨t, htR⟩ (r p) * t ⟨p.1, j p.1⟩) := by ring
    have hagree : ∀ f, σ ⟨t, htR⟩ (chartHom r f) = τ (chartHom r f) := by
      intro f
      rw [chart_eval, chart_eval]
      exact congrArg (fun w => eval w (map (Int.castRingHom ℂ) f)) (funext hσr)
    refine funField_hom_ext fun x u v a hu hv hvP hx => ?_
    have hxφ : x * chartHom r v = chartHom r u := by
      apply Subtype.ext
      apply mul_right_cancel₀ (toFrac_prod_ne_zero j hj a)
      rw [Subring.coe_mul, mul_assoc, chartHom_mul j r hr hv, hx, chartHom_mul j r hr hu]
    have hv0 : τ (chartHom r v) ≠ 0 := by
      rw [chart_eval]
      exact hne z hz v a hv hvP
    have e1 := congrArg (σ ⟨t, htR⟩) hxφ
    have e2 := congrArg τ hxφ
    rw [map_mul] at e1 e2
    rw [hagree, hagree] at e1
    exact mul_right_cancel₀ hv0 (e1.trans e2.symm)
  exact ⟨Equiv.ofBijective σ ⟨hinj, hsurj⟩, fun t u v a _ _ _ x hx => hσ t x u v hx⟩

end

end GroundTheory.Heights₂.Heights.Inter
