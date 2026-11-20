import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.OneLeftSpMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ImplicitFunctionHolomorphicStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AnChart

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.StdSmoothChart

open MvPolynomial

section Poly

variable {R ι : Type} [CommRing R]

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a`. Simplify using `only [eval₂_C]`. Conclude with `(hψ a).comp differentiableOn_fst (fun x hx => hx.1)`. Consider the case `add p q hp hq`.

Simplify using `only [eval₂_add]`. Conclude with `hp.add hq`. Consider the case `mul_X p i hp`. Simplify using `only [eval₂_mul, eval₂_X]`. Conclude with `hp.mul (differentiableOn_pi.1 differentiableOn_snd i)`.
-/
theorem differentiableOn_eval₂ [Fintype ι] {n : ℕ} {B : Set (Fin n → ℂ)}
    (ψ : (Fin n → ℂ) → (R →+* ℂ)) (hψ : ∀ r : R, DifferentiableOn ℂ (fun b => ψ b r) B)
    (p : MvPolynomial ι R) :
    DifferentiableOn ℂ (fun bx : (Fin n → ℂ) × (ι → ℂ) => eval₂ (ψ bx.1) bx.2 p)
      (B ×ˢ Set.univ) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [eval₂_C]
    exact (hψ a).comp differentiableOn_fst (fun x hx => hx.1)
  | add p q hp hq =>
    simp only [eval₂_add]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [eval₂_mul, eval₂_X]
    exact hp.mul (differentiableOn_pi.1 differentiableOn_snd i)

def dirDeriv [Fintype ι] (ψ : R →+* ℂ) (x v : ι → ℂ) (p : MvPolynomial ι R) : ℂ :=
  ∑ i, eval₂ ψ x (pderiv i p) * v i

/- English proof (translation)
Simplify using `[dirDeriv]`.
-/
theorem dirDeriv_C [Fintype ι] (ψ : R →+* ℂ) (x v : ι → ℂ) (a : R) :
    dirDeriv ψ x v (C a) = 0 := by
  simp [dirDeriv]

/- English proof (translation)
Simplify using `[dirDeriv, add_mul, Finset.sum_add_distrib]`.
-/
theorem dirDeriv_add [Fintype ι] (ψ : R →+* ℂ) (x v : ι → ℂ) (p q : MvPolynomial ι R) :
    dirDeriv ψ x v (p + q) = dirDeriv ψ x v p + dirDeriv ψ x v q := by
  simp [dirDeriv, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [dirDeriv, Derivation.leibniz, smul_eq_mul, eval₂_add, eval₂_mul, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]`.
-/
theorem dirDeriv_mul [Fintype ι] (ψ : R →+* ℂ) (x v : ι → ℂ) (p q : MvPolynomial ι R) :
    dirDeriv ψ x v (p * q) = eval₂ ψ x p * dirDeriv ψ x v q + eval₂ ψ x q * dirDeriv ψ x v p := by
  simp only [dirDeriv, Derivation.leibniz, smul_eq_mul, eval₂_add, eval₂_mul, add_mul,
    Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Simplify using `[dirDeriv, pderiv_X, Pi.single_apply, apply_ite]`.
-/
theorem dirDeriv_X [Fintype ι] [DecidableEq ι] (ψ : R →+* ℂ) (x v : ι → ℂ) (i : ι) :
    dirDeriv ψ x v (X i) = v i := by
  simp [dirDeriv, pderiv_X, Pi.single_apply, apply_ite]

/- English proof (translation)
Establish `h` using `ReciprocityTheory.ChartRestriction.G.Geo.Tor.hasFDerivAt_eval (map ψ p) x`. Simplify using `only [eval_map, pderiv_map] at h`. Conclude with `h`.
-/
theorem hasFDerivAt_eval₂ [Fintype ι] [DecidableEq ι] (ψ : R →+* ℂ) (p : MvPolynomial ι R)
    (x : ι → ℂ) :
    HasFDerivAt (fun x => eval₂ ψ x p)
      (∑ i, eval₂ ψ x (pderiv i p) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) i)
      x := by
  have h := ReciprocityTheory.ChartRestriction.G.Geo.Tor.hasFDerivAt_eval (map ψ p) x
  simp only [eval_map, pderiv_map] at h
  exact h

def dualEval (ψ : R →+* ℂ) (x v : ι → ℂ) : MvPolynomial ι R →+* DualNumber ℂ :=
  eval₂Hom ((TrivSqZeroExt.inlHom ℂ ℂ).comp ψ)
    (fun i => TrivSqZeroExt.inl (x i) + TrivSqZeroExt.inr (v i))

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a => simp [dualEval, dirDeriv_C]`. Consider the case `add p q hp hq`. Simplify using `[map_add, hp.1, hp.2, hq.1, hq.2, dirDeriv_add]`. Consider the case `mul_X p i hp`.

Establish `hX : dualEval ψ x v (X i) = TrivSqZeroExt.inl (x i) + TrivSqZeroExt.inr (v i)`. Simplify using `[dualEval]`. Rewrite using `[map_mul, hX]`. Use `⟨by simp [hp.1], ?_⟩` and prove the remaining obligations. Rewrite using `[dirDeriv_mul, dirDeriv_X]`.

Simplify using `[hp.1, hp.2, mul_comm]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dualEval_fst [Fintype ι] (ψ : R →+* ℂ) (x v : ι → ℂ) (p : MvPolynomial ι R) :
    (dualEval ψ x v p).fst = eval₂ ψ x p ∧ (dualEval ψ x v p).snd = dirDeriv ψ x v p := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp [dualEval, dirDeriv_C]
  | add p q hp hq =>
    simp [map_add, hp.1, hp.2, hq.1, hq.2, dirDeriv_add]
  | mul_X p i hp =>
    have hX : dualEval ψ x v (X i) = TrivSqZeroExt.inl (x i) + TrivSqZeroExt.inr (v i) := by
      simp [dualEval]
    rw [map_mul, hX]
    refine ⟨by simp [hp.1], ?_⟩
    rw [dirDeriv_mul, dirDeriv_X]
    simp [hp.1, hp.2, mul_comm]
    ring

end Poly

section Pres

variable {R A ι σ : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype σ]

/- English proof (translation)
Rewrite using `[P.algebraMap_apply, aeval_def, ← coe_eval₂Hom, map_eval₂Hom]`. Both sides reduce to the same expression.
-/
theorem algebraMap_ring_eq (P : Algebra.SubmersivePresentation R A ι σ) (χ : A →+* ℂ)
    (p : MvPolynomial ι R) :
    χ (algebraMap P.Ring A p) =
      eval₂ (χ.comp (algebraMap R A)) (fun i => χ (P.val i)) p := by
  rw [P.algebraMap_apply, aeval_def, ← coe_eval₂Hom, map_eval₂Hom]
  rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨(algebraMap P.Ring A).liftOfSurjective P.algebraMap_surjective ⟨f, by show P.ker ≤ _ rw [← P.span_range_relation_eq_ker, Ideal.span_le] rintro _ ⟨j, rfl⟩; exact hf j⟩, fun p => RingHom.liftOfRightInverse_comp_apply _ _ _ _ p⟩`.
-/
theorem exists_lift (P : Algebra.SubmersivePresentation R A ι σ) {S : Type} [CommRing S]
    (f : MvPolynomial ι R →+* S) (hf : ∀ j, f (P.relation j) = 0) :
    ∃ χ : A →+* S, ∀ p : MvPolynomial ι R, χ (algebraMap P.Ring A p) = f p :=
  ⟨(algebraMap P.Ring A).liftOfSurjective P.algebraMap_surjective ⟨f, by
      show P.ker ≤ _
      rw [← P.span_range_relation_eq_ker, Ideal.span_le]
      rintro _ ⟨j, rfl⟩; exact hf j⟩, fun p => RingHom.liftOfRightInverse_comp_apply _ _ _ _ p⟩

/- English proof (translation)
Use `RingHom.ext fun a => ?_` and prove the remaining obligations. Take `⟨p, rfl⟩` from `P.algebraMap_surjective a`. Conclude with `h p`.
-/
theorem ringHom_ext (P : Algebra.SubmersivePresentation R A ι σ) {χ χ' : A →+* ℂ}
    (h : ∀ p : MvPolynomial ι R, χ (algebraMap P.Ring A p) = χ' (algebraMap P.Ring A p)) :
    χ = χ' := by
  refine RingHom.ext fun a => ?_
  obtain ⟨p, rfl⟩ := P.algebraMap_surjective a
  exact h p

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a`. Rewrite using `[dirDeriv_C, show algebraMap P.Ring A (C a) = algebraMap R A a from (IsScalarTower.algebraMap_apply R P.Ring A a).symm]`. Conclude with `h0 a`. Consider the case `add p q hp hq => rw [map_add, map_add, hp, hq, dirDeriv_add]`.

Consider the case `mul_X p i hp`. Establish `hX : algebraMap P.Ring A (X i) = P.val i` using `by simp`. Rewrite using `[map_mul, hL, dirDeriv_mul, dirDeriv_X, hX, hp, algebraMap_ring_eq]`. Simplify using the standard rewrite rules.
-/
theorem der_eq_dirDeriv [Fintype ι] (P : Algebra.SubmersivePresentation R A ι σ) (χ : A →+* ℂ)
    (D : A →+ ℂ) (h0 : ∀ r, D (algebraMap R A r) = 0)
    (hL : ∀ x y, D (x * y) = χ x * D y + χ y * D x) (p : MvPolynomial ι R) :
    D (algebraMap P.Ring A p) =
      dirDeriv (χ.comp (algebraMap R A)) (fun i => χ (P.val i)) (fun i => D (P.val i)) p := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [dirDeriv_C, show algebraMap P.Ring A (C a) = algebraMap R A a from
      (IsScalarTower.algebraMap_apply R P.Ring A a).symm]
    exact h0 a
  | add p q hp hq => rw [map_add, map_add, hp, hq, dirDeriv_add]
  | mul_X p i hp =>
    have hX : algebraMap P.Ring A (X i) = P.val i := by simp
    rw [map_mul, hL, dirDeriv_mul, dirDeriv_X, hX, hp, algebraMap_ring_eq]
    simp

/- English proof (translation)
Take `⟨E, hE⟩` from `exists_lift P (dualEval ψ x v) (fun j => by`. Use `TrivSqZeroExt.ext ?_ ?_` and prove the remaining obligations. Rewrite using `[(dualEval_fst ψ x v _).1, hx j]`. Both sides reduce to the same expression. Rewrite using `[(dualEval_fst ψ x v _).2, hv j]`.

Use the proof step `rfl)`. Establish `hfst : ∀ a, (E a).fst = χ a` using `fun a => by`. Take `⟨p, rfl⟩` from `P.algebraMap_surjective a`. Rewrite using `[hE, hχ, (dualEval_fst ψ x v _).1]`. Use `⟨⟨⟨fun a => (E a).snd, by simp⟩, fun a b => by simp⟩, fun r => ?_, fun a b => ?_, fun p => ?_⟩` and prove the remaining obligations.

Use `show (E (algebraMap R A r)).snd = 0`. Rewrite using `[IsScalarTower.algebraMap_apply R P.Ring A r, hE, (dualEval_fst ψ x v _).2]`. Conclude with `dirDeriv_C ψ x v r`. Use `show (E (a * b)).snd = χ a * (E b).snd + χ b * (E a).snd`. Simplify using `[map_mul, hfst, mul_comm]`.

Use `show (E _).snd = _`. Rewrite using `[hE, (dualEval_fst ψ x v _).2]`.
-/
theorem exists_der [Fintype ι] (P : Algebra.SubmersivePresentation R A ι σ) (ψ : R →+* ℂ)
    (x v : ι → ℂ) (hx : ∀ j, eval₂ ψ x (P.relation j) = 0)
    (hv : ∀ j, dirDeriv ψ x v (P.relation j) = 0) (χ : A →+* ℂ)
    (hχ : ∀ p : MvPolynomial ι R, χ (algebraMap P.Ring A p) = eval₂ ψ x p) :
    ∃ D : A →+ ℂ, (∀ r, D (algebraMap R A r) = 0) ∧
      (∀ a b, D (a * b) = χ a * D b + χ b * D a) ∧
      ∀ p : MvPolynomial ι R, D (algebraMap P.Ring A p) = dirDeriv ψ x v p := by
  obtain ⟨E, hE⟩ := exists_lift P (dualEval ψ x v) (fun j => by
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [(dualEval_fst ψ x v _).1, hx j]; rfl
    · rw [(dualEval_fst ψ x v _).2, hv j]; rfl)
  have hfst : ∀ a, (E a).fst = χ a := fun a => by
    obtain ⟨p, rfl⟩ := P.algebraMap_surjective a
    rw [hE, hχ, (dualEval_fst ψ x v _).1]
  refine ⟨⟨⟨fun a => (E a).snd, by simp⟩, fun a b => by simp⟩, fun r => ?_, fun a b => ?_,
    fun p => ?_⟩
  · show (E (algebraMap R A r)).snd = 0
    rw [IsScalarTower.algebraMap_apply R P.Ring A r, hE, (dualEval_fst ψ x v _).2]
    exact dirDeriv_C ψ x v r
  · show (E (a * b)).snd = χ a * (E b).snd + χ b * (E a).snd
    simp [map_mul, hfst, mul_comm]
  · show (E _).snd = _
    rw [hE, (dualEval_fst ψ x v _).2]

/- English proof (translation)
Set `ev : MvPolynomial ι R →+* ℂ` to `eval₂Hom (χ.comp (algebraMap R A)) (fun i => χ (P.val i))`. Set `M : Matrix σ σ ℂ` to `ev.mapMatrix P.jacobiMatrix`. Establish `dt : IsUnit M.det`. Establish `: M.det = χ (algebraMap P.Ring A P.jacobiMatrix.det)`. Rewrite using `[algebraMap_ring_eq]`.

Conclude with `(RingHom.map_det ev _).symm`. Rewrite using `[this, ← P.jacobian_eq_jacobiMatrix_det]`. Conclude with `P.jacobian_isUnit.map χ`. Set `u : σ → ℂ` to `Matrix.vecMul w M⁻¹`. Establish `hu : Matrix.vecMul u M = w`.

Simplify using `only [u, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ dt, Matrix.vecMul_one]`. Use `⟨fun i => ∑ j', if i = P.map j' then u j' else 0, fun j => ?_⟩` and prove the remaining obligations. Establish `: ∀ j', ev (pderiv (P.map j') (P.relation j)) = M j' j` using `fun j' => by`. Simplify using `[M, P.jacobiMatrix_apply]`. Rewrite using `[← hu]`.

Simplify using `only [dirDeriv, Finset.mul_sum, Matrix.vecMul, dotProduct]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j' _ => ?_` and prove the remaining obligations. Simplify using `only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Rewrite using `[← this j', mul_comm]`.

Both sides reduce to the same expression.
-/
theorem exists_dir [Fintype ι] (P : Algebra.SubmersivePresentation R A ι σ)
    (χ : A →+* ℂ) (w : σ → ℂ) :
    ∃ v : ι → ℂ, ∀ j, dirDeriv (χ.comp (algebraMap R A)) (fun i => χ (P.val i)) v (P.relation j)
      = w j := by
  classical
  let ev : MvPolynomial ι R →+* ℂ :=
    eval₂Hom (χ.comp (algebraMap R A)) (fun i => χ (P.val i))
  let M : Matrix σ σ ℂ := ev.mapMatrix P.jacobiMatrix
  have dt : IsUnit M.det := by
    have : M.det = χ (algebraMap P.Ring A P.jacobiMatrix.det) := by
      rw [algebraMap_ring_eq]
      exact (RingHom.map_det ev _).symm
    rw [this, ← P.jacobian_eq_jacobiMatrix_det]
    exact P.jacobian_isUnit.map χ
  let u : σ → ℂ := Matrix.vecMul w M⁻¹
  have hu : Matrix.vecMul u M = w := by
    simp only [u, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ dt, Matrix.vecMul_one]
  refine ⟨fun i => ∑ j', if i = P.map j' then u j' else 0, fun j => ?_⟩
  have : ∀ j', ev (pderiv (P.map j') (P.relation j)) = M j' j := fun j' => by
    simp [M, P.jacobiMatrix_apply]
  rw [← hu]
  simp only [dirDeriv, Finset.mul_sum, Matrix.vecMul, dotProduct]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j' _ => ?_
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← this j', mul_comm]
  rfl

end Pres

end GlobalTheory.CompanionTheory.Ar.StdSmoothChart

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.StdSmoothChart

open MvPolynomial

section Family

variable {R A ι σ : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype σ]

/- English proof (translation)
Use `⟨ContinuousLinearMap.pi fun j => ∑ i, eval₂ ψ x (pderiv i (Q j)) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) i, hasFDerivAt_pi.2 fun j => hasFDerivAt_eval₂ ψ (Q j) x, fun v j => ?_⟩` and prove the remaining obligations. Simplify using `[dirDeriv]`.
-/
theorem hasFDerivAt_family [Fintype ι] [DecidableEq ι] {J : Type} [Fintype J] (ψ : R →+* ℂ)
    (Q : J → MvPolynomial ι R) (x : ι → ℂ) :
    ∃ F : (ι → ℂ) →L[ℂ] (J → ℂ), HasFDerivAt (fun x j => eval₂ ψ x (Q j)) F x ∧
      ∀ v j, F v j = dirDeriv ψ x v (Q j) := by
  refine ⟨ContinuousLinearMap.pi fun j => ∑ i, eval₂ ψ x (pderiv i (Q j)) •
    ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) i,
    hasFDerivAt_pi.2 fun j => hasFDerivAt_eval₂ ψ (Q j) x, fun v j => ?_⟩
  simp [dirDeriv]

/- English proof (translation)
Rewrite using `[P.algebraMap_apply, P.aeval_val_relation]`.
-/
theorem algebraMap_relation (P : Algebra.SubmersivePresentation R A ι σ) (j : σ) :
    algebraMap P.Ring A (P.relation j) = 0 := by
  rw [P.algebraMap_apply, P.aeval_val_relation]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Use `(injective_iff_map_eq_zero F).2 fun v hv => ?_` and prove the remaining obligations. Establish `hv' : ∀ j, dirDeriv (χ₀.comp (algebraMap R A)) (fun i => χ₀ (P.val i)) v (Sum.elim P.relation T j) = 0` using `fun j => by rw [← hF, hv]; rfl`. Take `⟨D, h0, hL, hD⟩` from `exists_der P (χ₀.comp (algebraMap R A)) (fun i => χ₀ (P.val i)) v (fun j => by rw [← algebraMap_ring_eq, algebraMap_relation, map_zero]) (fun j => hv' (Sum.inl j)) χ₀ (fun p => algebraMap_ring_eq P χ₀ p)`. Establish `hD0 : D = 0` using `hinj D h0 hL fun c => by`.

Rewrite using `[← hT c, hD]`. Conclude with `hv' (Sum.inr c)`. Use function extensionality and compare the values at `i`. Use `hD (X i)` as an intermediate fact. Rewrite `this` using `[hD0, dirDeriv_X]`.

Conclude with `this.symm`. Introduce `w`. Take `⟨v₁, hv₁⟩` from `exists_dir P χ₀ (fun j => w (Sum.inl j))`. Use `choose Dc h0 hL hDc using hsurj`. Establish `hFc : ∀ c j, F (fun i => Dc c (P.val i)) j = Dc c (algebraMap P.Ring A (Sum.elim P.relation T j))` using `fun c j => by`.

Rewrite using `[hF, der_eq_dirDeriv P χ₀ (Dc c) (h0 c) (hL c)]`. Use `⟨v₁ + ∑ c, (w (Sum.inr c) - F v₁ (Sum.inr c)) • (fun i => Dc c (P.val i)), ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_sum]`. Use function extensionality and compare the values at `j`. Simplify using `only [map_smul, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hFc]`.

Break down `j with j | c'` into its components or cases. Simplify using `only [Sum.elim_inl, algebraMap_relation, map_zero, mul_zero, Finset.sum_const_zero, add_zero]`. Rewrite using `[hF]`. Conclude with `hv₁ j`. Simplify using `only [Sum.elim_inr, hT, hDc, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem bijective_base [Fintype ι] (P : Algebra.SubmersivePresentation R A ι σ) (χ₀ : A →+* ℂ)
    {g : ℕ} (t : Fin g → A) (T : Fin g → MvPolynomial ι R)
    (hT : ∀ c, algebraMap P.Ring A (T c) = t c)
    (hinj : ∀ D : A →+ ℂ, (∀ r, D (algebraMap R A r) = 0) →
      (∀ x y, D (x * y) = χ₀ x * D y + χ₀ y * D x) → (∀ c, D (t c) = 0) → D = 0)
    (hsurj : ∀ c, ∃ D : A →+ ℂ, (∀ r, D (algebraMap R A r) = 0) ∧
      (∀ x y, D (x * y) = χ₀ x * D y + χ₀ y * D x) ∧ ∀ c', D (t c') = if c = c' then 1 else 0)
    (F : (ι → ℂ) →L[ℂ] (σ ⊕ Fin g → ℂ))
    (hF : ∀ v j, F v j = dirDeriv (χ₀.comp (algebraMap R A)) (fun i => χ₀ (P.val i)) v
      (Sum.elim P.relation T j)) :
    Function.Bijective F := by
  classical
  constructor
  · refine (injective_iff_map_eq_zero F).2 fun v hv => ?_
    have hv' : ∀ j, dirDeriv (χ₀.comp (algebraMap R A)) (fun i => χ₀ (P.val i)) v
        (Sum.elim P.relation T j) = 0 := fun j => by rw [← hF, hv]; rfl
    obtain ⟨D, h0, hL, hD⟩ := exists_der P (χ₀.comp (algebraMap R A)) (fun i => χ₀ (P.val i)) v
      (fun j => by rw [← algebraMap_ring_eq, algebraMap_relation, map_zero])
      (fun j => hv' (Sum.inl j)) χ₀ (fun p => algebraMap_ring_eq P χ₀ p)
    have hD0 : D = 0 := hinj D h0 hL fun c => by
      rw [← hT c, hD]; exact hv' (Sum.inr c)
    funext i
    have := hD (X i)
    rw [hD0, dirDeriv_X] at this
    exact this.symm
  · intro w
    obtain ⟨v₁, hv₁⟩ := exists_dir P χ₀ (fun j => w (Sum.inl j))
    choose Dc h0 hL hDc using hsurj
    have hFc : ∀ c j, F (fun i => Dc c (P.val i)) j =
        Dc c (algebraMap P.Ring A (Sum.elim P.relation T j)) := fun c j => by
      rw [hF, der_eq_dirDeriv P χ₀ (Dc c) (h0 c) (hL c)]
    refine ⟨v₁ + ∑ c, (w (Sum.inr c) - F v₁ (Sum.inr c)) • (fun i => Dc c (P.val i)), ?_⟩
    rw [map_add, map_sum]
    funext j
    simp only [map_smul, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hFc]
    rcases j with j | c'
    · simp only [Sum.elim_inl, algebraMap_relation, map_zero, mul_zero, Finset.sum_const_zero,
        add_zero]
      rw [hF]
      exact hv₁ j
    · simp only [Sum.elim_inr, hT, hDc, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      ring

/- English proof (translation)
Substitute `hψ hx` using the available equality. Establish `hv` using `hinj (fun i => D (P.val i)) (funext fun j => by`. Rewrite using `[hF, ← der_eq_dirDeriv P χ D h0 hL]`. Break down `j with j | c` into its components or cases. Simplify using `[algebraMap_relation]`.

Simplify using `[hT, ht])`. Use `AddMonoidHom.ext fun a => ?_` and prove the remaining obligations. Take `⟨p, rfl⟩` from `P.algebraMap_surjective a`. Rewrite using `[der_eq_dirDeriv P χ D h0 hL, hv]`. Simplify using `[dirDeriv]`.
-/
theorem der_zero [Fintype ι] (P : Algebra.SubmersivePresentation R A ι σ) (χ : A →+* ℂ)
    (ψ : R →+* ℂ) (x : ι → ℂ) (hψ : χ.comp (algebraMap R A) = ψ)
    (hx : (fun i => χ (P.val i)) = x) {g : ℕ} (t : Fin g → A) (T : Fin g → MvPolynomial ι R)
    (hT : ∀ c, algebraMap P.Ring A (T c) = t c)
    (F : (ι → ℂ) →L[ℂ] (σ ⊕ Fin g → ℂ))
    (hF : ∀ v j, F v j = dirDeriv ψ x v (Sum.elim P.relation T j))
    (hinj : ∀ v, F v = 0 → v = 0)
    (D : A →+ ℂ) (h0 : ∀ r, D (algebraMap R A r) = 0)
    (hL : ∀ x y, D (x * y) = χ x * D y + χ y * D x) (ht : ∀ c, D (t c) = 0) : D = 0 := by
  subst hψ hx
  have hv := hinj (fun i => D (P.val i)) (funext fun j => by
    rw [hF, ← der_eq_dirDeriv P χ D h0 hL]
    rcases j with j | c
    · simp [algebraMap_relation]
    · simp [hT, ht])
  refine AddMonoidHom.ext fun a => ?_
  obtain ⟨p, rfl⟩ := P.algebraMap_surjective a
  rw [der_eq_dirDeriv P χ D h0 hL, hv]
  simp [dirDeriv]

end Family

section Embed

variable {σ : Type} [Fintype σ] {g : ℕ}

/- English proof (translation)
Rewrite using `[Metric.mem_ball, dist_pi_lt_iff hr]`. Introduce and unpack `(j | c)`. Simplify using `using hr`. Simplify using `using (dist_pi_lt_iff hr).1 (Metric.mem_ball.1 hz) c`.
-/
theorem elim_mem_ball (z : Fin g → ℂ) {r : ℝ} (hr : 0 < r) (hz : z ∈ Metric.ball 0 r) :
    (Sum.elim 0 z : σ ⊕ Fin g → ℂ) ∈ Metric.ball (0 : σ ⊕ Fin g → ℂ) r := by
  rw [Metric.mem_ball, dist_pi_lt_iff hr]
  rintro (j | c)
  · simpa using hr
  · simpa using (dist_pi_lt_iff hr).1 (Metric.mem_ball.1 hz) c

/- English proof (translation)
Use `differentiable_pi.2 ?_` and prove the remaining obligations. Introduce and unpack `(j | c)`. Simplify using `using differentiable_const (0 : ℂ)`. Simplify using `using differentiable_apply c`.
-/
theorem differentiable_elim :
    Differentiable ℂ (fun z : Fin g → ℂ => (Sum.elim 0 z : σ ⊕ Fin g → ℂ)) := by
  refine differentiable_pi.2 ?_
  rintro (j | c)
  · simpa using differentiable_const (0 : ℂ)
  · simpa using differentiable_apply c

end Embed

end GlobalTheory.CompanionTheory.Ar.StdSmoothChart

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.StdSmoothChart

/- English proof (translation)
Introduce `R A _ _ _ _ n g B ψ hB hψ b₀ hb₀ χ₀ t h₀ ht hinj hsurj`. Take `⟨I₀, K₀, _, _, ⟨P⟩⟩` from `Algebra.IsStandardSmooth.out (R := R) (S := A)`. Use `letI := Fintype.ofFinite I₀`. Use `letI := Fintype.ofFinite K₀`. Use `choose T hT using fun c => P.algebraMap_surjective (t c)`.

Take `⟨Q, hQ⟩ : ∃ Q : K₀ ⊕ Fin g → MvPolynomial I₀ R, Q = Sum.elim P.relation T` from `⟨_, rfl⟩`. Take `⟨Φ, hΦd⟩ : ∃ Φ : (Fin n → ℂ) × (I₀ → ℂ) → (K₀ ⊕ Fin g → ℂ), Φ = fun bx j => MvPolynomial.eval₂ (ψ bx.1) bx.2 (Q j)` from `⟨_, rfl⟩`. Take `⟨x₀, hx₀⟩ : ∃ x₀ : I₀ → ℂ, (fun i => χ₀ (P.val i)) = x₀` from `⟨_, rfl⟩`. Establish `hΦ : DifferentiableOn ℂ Φ (B ×ˢ Set.univ)`. Rewrite using `[hΦd]`.

Conclude with `differentiableOn_pi.2 fun j => differentiableOn_eval₂ ψ hψ (Q j)`. Establish `e₀ : ∀ p, MvPolynomial.eval₂ (ψ b₀) x₀ p = χ₀ (algebraMap P.Ring A p)` using `fun p => by`. Rewrite using `[algebraMap_ring_eq, h₀, hx₀]`. Establish `eQ : ∀ (b : Fin n → ℂ) (χ : A →+* ℂ), χ.comp (algebraMap R A) = ψ b → Φ (b, fun i => χ (P.val i)) = Sum.elim (0 : K₀ → ℂ) (fun c => χ (t c))` using `fun b χ hχ => by`. Use function extensionality and compare the values at `j`.

Rewrite using `[hΦd]`. Use `show MvPolynomial.eval₂ (ψ b) _ (Q j) = _`. Rewrite using `[← hχ, ← algebraMap_ring_eq, hQ]`. Break down `j with j | c` into its components or cases. Simplify using `[algebraMap_relation]`.

Simplify using `[hT]`. Establish `Φ₀ : Φ (b₀, x₀) = 0`. Rewrite using `[← hx₀, eQ b₀ χ₀ h₀]`. Use function extensionality and compare the values at `j`. Break down `j with j | c` into its components or cases.

Both sides reduce to the same expression. Conclude with `ht c`. Take `⟨F₀, hF₀, hF₀v⟩` from `hasFDerivAt_family (ψ b₀) Q x₀`. Establish `bij : Function.Bijective F₀` using `bijective_base P χ₀ t T hT hinj hsurj F₀ (by`. Rewrite using `[h₀, hx₀, ← hQ]`.

Conclude with `hF₀v)`. Take `⟨L, hL⟩ : ∃ L : (I₀ → ℂ) ≃L[ℂ] (K₀ ⊕ Fin g → ℂ), (L : (I₀ → ℂ) →L[ℂ] (K₀ ⊕ Fin g → ℂ)) = F₀` from `⟨(LinearEquiv.ofBijective F₀.toLinearMap bij).toContinuousLinearEquiv, by ext; rfl⟩`. Take `⟨ε', δ', X, ε'0, δ'0, hX₀, hXd, hX, hXinv⟩` from `GlobalTheory.T.implicit_function_holomorphic n I₀ (K₀ ⊕ Fin g) (B ×ˢ Set.univ) Φ b₀ x₀ L (hB.prod isOpen_univ) ⟨hb₀, trivial⟩ hΦ (by`. Rewrite using `[hL, hΦd]`. Conclude with `hF₀)`.

Rewrite `hX₀`, `hXd`, `hX`, `hXinv` using `[Φ₀]`. Take `⟨ε'', ε''0, hε''⟩` from `Metric.isOpen_iff.1 hB b₀ hb₀`. Take `⟨ε, hε⟩ : ∃ ε, ε = min ε' ε''` from `⟨_, rfl⟩`. Establish `ε0 : 0 < ε` using `hε ▸ lt_min ε'0 ε''0`. Establish `εa : ε ≤ ε'` using `hε ▸ min_le_left _ _`.

Establish `εb : ε ≤ ε''` using `hε ▸ min_le_right _ _`. Take `⟨δ, hδ⟩ : ∃ δ, δ = min δ' ε` from `⟨_, rfl⟩`. Establish `δ0 : 0 < δ` using `hδ ▸ lt_min δ'0 ε0`. Establish `δa : δ ≤ δ'` using `hδ ▸ min_le_left _ _`. Establish `δb : δ ≤ ε` using `hδ ▸ min_le_right _ _`.

Take `⟨emb, hemb⟩ : ∃ emb : (Fin g → ℂ) → (K₀ ⊕ Fin g → ℂ), emb = fun z => Sum.elim (0 : K₀ → ℂ) z` from `⟨_, rfl⟩`. Establish `inU : ∀ b ∈ ball b₀ ε, ∀ z ∈ ball (0 : Fin g → ℂ) ε, (b, emb z) ∈ ball b₀ ε' ×ˢ ball (0 : K₀ ⊕ Fin g → ℂ) ε'` using `fun b hb z hz => by`. Use `⟨ball_subset_ball εa hb, ?_⟩` and prove the remaining obligations. Rewrite using `[hemb]`. Conclude with `ball_subset_ball εa (elim_mem_ball z ε0 hz)`.

Establish `hev : ∀ b x j, Φ (b, x) j = MvPolynomial.eval₂ (ψ b) x (Q j)` using `fun b x j => by rw [hΦd]`. Establish `rel : ∀ b ∈ ball b₀ ε, ∀ z ∈ ball (0 : Fin g → ℂ) ε, ∀ j, MvPolynomial.eval₂ (ψ b) (X (b, emb z)) (P.relation j) = 0` using `fun b hb z hz j => by`. Use `congrFun (hX _ (inU b hb z hz)).2.1 (Sum.inl j)` as an intermediate fact. Rewrite `this` using `[hev, hQ]`. Rewrite `this`, the goal using `[hemb]`.

Simplify using `using this`. Establish `lf : ∀ (b : Fin n → ℂ) (x : I₀ → ℂ), (∀ j, MvPolynomial.eval₂ (ψ b) x (P.relation j) = 0) → ∃ χ : A →+* ℂ, ∀ p, χ (algebraMap P.Ring A p) = MvPolynomial.eval₂ (ψ b) x p` using `fun b x hx => exists_lift P (MvPolynomial.eval₂Hom (ψ b) x) hx`. Use `choose Ψ₀ hΨ₀ using lf`. Take `⟨Ψ, hΨd⟩ : ∃ Ψ : (Fin n → ℂ) → (Fin g → ℂ) → (A →+* ℂ), Ψ = fun b z => if h : b ∈ ball b₀ ε ∧ z ∈ ball (0 : Fin g → ℂ) ε then Ψ₀ b _ (rel b h.1 z h.2 ) else χ₀` from `⟨_, rfl⟩`. Establish `hΨ : ∀ b ∈ ball b₀ ε, ∀ z ∈ ball (0 : Fin g → ℂ) ε, ∀ p, Ψ b z (algebraMap P.Ring A p) = MvPolynomial.eval₂ (ψ b) (X (b, emb z)) p` using `fun b hb z hz p => by`.

Rewrite using `[hΨd]`. Simplify using `only [dif_pos (show b ∈ ball b₀ ε ∧ z ∈ ball (0 : Fin g → ℂ) ε from ⟨hb, hz⟩)]`. Conclude with `hΨ₀ _ _ _ p`. Establish `hcomp : ∀ b ∈ ball b₀ ε, ∀ z ∈ ball (0 : Fin g → ℂ) ε, (Ψ b z).comp (algebraMap R A) = ψ b` using `fun b hb z hz => RingHom.ext fun r => by`. Rewrite using `[RingHom.comp_apply, IsScalarTower.algebraMap_apply R P.Ring A r, hΨ b hb z hz]`.

Conclude with `MvPolynomial.eval₂_C _ _ _`. Establish `hval : ∀ b ∈ ball b₀ ε, ∀ z ∈ ball (0 : Fin g → ℂ) ε, (fun i => Ψ b z (P.val i)) = X (b, emb z)` using `fun b hb z hz => by`. Use function extensionality and compare the values at `i`. Rewrite using `[show P.val i = algebraMap P.Ring A (MvPolynomial.X i) by simp, hΨ b hb z hz]`. Conclude with `MvPolynomial.eval₂_X _ _ _`.

Establish `emb0 : emb 0 = 0`. Rewrite using `[hemb]`. Use function extensionality and compare the values at `j`. Apply the tactic sequence `rcases j with j | c <;> rfl`. Establish `mb : b₀ ∈ ball b₀ ε` using `mem_ball_self ε0`.

Establish `m0 : (0 : Fin g → ℂ) ∈ ball (0 : Fin g → ℂ) ε` using `mem_ball_self ε0`. Take `⟨e⟩ : Nonempty (I₀ ⊕ Fin g ≃ Fin (Fintype.card (I₀ ⊕ Fin g)))` from `⟨Fintype.equivFin _⟩`. Use `⟨_, fun j => Sum.elim P.val t (e.symm j), ε, δ, Ψ, ε0, δ0, (ball_subset_ball εb).trans hε'', ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `ringHom_ext P fun p => ?_` and prove the remaining obligations. Rewrite using `[hΨ b₀ mb 0 m0, emb0, hX₀, e₀]`.

Introduce `b hb z hz`. Use `⟨hcomp b hb z hz, fun c => ?_, fun D h0 hLD hDt => ?_⟩` and prove the remaining obligations. Use `congrFun (hX _ (inU b hb z hz)).2.1 (Sum.inr c)` as an intermediate fact. Rewrite `this` using `[hev, hQ, hemb]`. Rewrite using `[← hT c, hΨ b hb z hz, hemb]`.

Simplify using `using this`. Take `⟨F, hF, hFv⟩` from `hasFDerivAt_family (ψ b) Q (X (b, emb z))`. Use `der_zero P (Ψ b z) (ψ b) (X (b, emb z)) (hcomp b hb z hz) (hval b hb z hz) t T hT F (by rw [← hQ]; exact hFv) (fun v hv => ?_) D h0 hLD hDt` and prove the remaining obligations. Use `(hX _ (inU b hb z hz)).2.2 v ?_` and prove the remaining obligations. Establish `hF' : HasFDerivAt (fun x => Φ (b, x)) F (X (b, emb z))`.

Rewrite using `[hΦd]`. Conclude with `hF`. Use `show fderiv ℂ (fun x => Φ (b, x)) (X (b, emb z)) v = 0`. Rewrite using `[hF'.fderiv, hv]`. Introduce `a`.

Take `⟨p, rfl⟩` from `P.algebraMap_surjective a`. Establish `hG : DifferentiableOn ℂ (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => (bz.1, X (bz.1, emb bz.2))) (ball b₀ ε ×ˢ ball (0 : Fin g → ℂ) ε)`. Use `differentiableOn_fst.prodMk (hXd.comp (differentiableOn_fst.prodMk ?_) ?_)` and prove the remaining obligations. Rewrite using `[hemb]`. Establish `hdz : Differentiable ℂ (fun z : Fin g → ℂ => (Sum.elim 0 z : K₀ ⊕ Fin g → ℂ))` using `differentiable_elim`.

Conclude with `(hdz.comp (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (Fin g → ℂ)).differentiable).differentiableOn`. Conclude with `fun bz hbz => inU _ hbz.1 _ hbz.2`. Use `DifferentiableOn.congr (f := fun bz : (Fin n → ℂ) × (Fin g → ℂ) => MvPolynomial.eval₂ (ψ bz.1) (X (bz.1, emb bz.2)) p) ?_ fun bz hbz => hΨ _ hbz.1 _ hbz.2 p` and prove the remaining obligations. Conclude with `(differentiableOn_eval₂ ψ hψ p).comp hG fun bz hbz => ⟨hε'' (ball_subset_ball εb hbz.1), trivial⟩`. Conclude with `fun c => ⟨e (Sum.inr c), by simp⟩`.

Introduce `b hb χ hχ hj`. Establish `hb' : b ∈ ball b₀ ε` using `ball_subset_ball δb hb`. Establish `hx : (fun i => χ (P.val i)) ∈ ball x₀ δ'`. Use `(dist_pi_lt_iff δ'0).2 fun i => ?_` and prove the remaining obligations. Use `hj (e (Sum.inl i))` as an intermediate fact.

Rewrite using `[← hx₀, dist_eq_norm]`. Simplify using `only [Equiv.symm_apply_apply, Sum.elim_inl] at this`. Conclude with `this.trans_le δa`. Establish `hz : (fun c => χ (t c)) ∈ ball (0 : Fin g → ℂ) ε`. Use `(dist_pi_lt_iff ε0).2 fun c => ?_` and prove the remaining obligations.

Use `hj (e (Sum.inr c))` as an intermediate fact. Simplify using `only [Equiv.symm_apply_apply, Sum.elim_inr, ht, sub_zero] at this`. Rewrite using `[dist_eq_norm]`. Simplify using `using this.trans_le δb`. Use `⟨hz, ?_⟩` and prove the remaining obligations.

Establish `hinv` using `(hXinv b (ball_subset_ball δa hb) _ hx).2.2`. Rewrite `hinv` using `[eQ b χ hχ]`. Use `ringHom_ext P fun p => ?_` and prove the remaining obligations. Rewrite using `[hΨ b hb' _ hz, hemb]`. Use `show _ = MvPolynomial.eval₂ (ψ b) (X (b, Sum.elim (0 : K₀ → ℂ) fun c => χ (t c))) p`.

Rewrite using `[hinv, algebraMap_ring_eq, hχ]`.
-/
theorem exists_sections : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Algebra.IsStandardSmooth R A] (n g : ℕ) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)), IsOpen B → (∀ r : R, DifferentiableOn ℂ (fun b => ψ b r) B) → ∀ b₀ ∈ B, ∀ (χ₀ : A →+* ℂ) (t : Fin g → A), χ₀.comp (algebraMap R A) = ψ b₀ → (∀ c, χ₀ (t c) = 0) →
  (∀ D : A →+ ℂ, (∀ r, D (algebraMap R A r) = 0) → (∀ x y, D (x * y) = χ₀ x * D y + χ₀ y * D x) → (∀ c, D (t c) = 0) → D = 0) →
  (∀ c, ∃ D : A →+ ℂ, (∀ r, D (algebraMap R A r) = 0) ∧ (∀ x y, D (x * y) = χ₀ x * D y + χ₀ y * D x) ∧ ∀ c', D (t c') = if c = c' then 1 else 0) →
  ∃ (N : ℕ) (f : Fin N → A) (ε δ : ℝ) (Ψ : (Fin n → ℂ) → (Fin g → ℂ) → (A →+* ℂ)), 0 < ε ∧ 0 < δ ∧ ball b₀ ε ⊆ B ∧ Ψ b₀ 0 = χ₀ ∧
    (∀ b ∈ ball b₀ ε, ∀ z ∈ ball (0 : Fin g → ℂ) ε, (Ψ b z).comp (algebraMap R A) = ψ b ∧ (∀ c, Ψ b z (t c) = z c) ∧
      ∀ D : A →+ ℂ, (∀ r, D (algebraMap R A r) = 0) → (∀ x y, D (x * y) = Ψ b z x * D y + Ψ b z y * D x) → (∀ c, D (t c) = 0) → D = 0) ∧
    (∀ a : A, DifferentiableOn ℂ (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => Ψ bz.1 bz.2 a) (ball b₀ ε ×ˢ ball (0 : Fin g → ℂ) ε)) ∧
    (∀ c, ∃ j, f j = t c) ∧
    ∀ b ∈ ball b₀ δ, ∀ χ : A →+* ℂ, χ.comp (algebraMap R A) = ψ b → (∀ j, ‖χ (f j) - χ₀ (f j)‖ < δ) →
      (fun c => χ (t c)) ∈ ball (0 : Fin g → ℂ) ε ∧ χ = Ψ b (fun c => χ (t c)) := by
  intro R A _ _ _ _ n g B ψ hB hψ b₀ hb₀ χ₀ t h₀ ht hinj hsurj
  classical
  obtain ⟨I₀, K₀, _, _, ⟨P⟩⟩ := Algebra.IsStandardSmooth.out (R := R) (S := A)
  letI := Fintype.ofFinite I₀
  letI := Fintype.ofFinite K₀
  choose T hT using fun c => P.algebraMap_surjective (t c)
  obtain ⟨Q, hQ⟩ : ∃ Q : K₀ ⊕ Fin g → MvPolynomial I₀ R, Q = Sum.elim P.relation T := ⟨_, rfl⟩
  obtain ⟨Φ, hΦd⟩ : ∃ Φ : (Fin n → ℂ) × (I₀ → ℂ) → (K₀ ⊕ Fin g → ℂ),
      Φ = fun bx j => MvPolynomial.eval₂ (ψ bx.1) bx.2 (Q j) := ⟨_, rfl⟩
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : I₀ → ℂ, (fun i => χ₀ (P.val i)) = x₀ := ⟨_, rfl⟩
  have hΦ : DifferentiableOn ℂ Φ (B ×ˢ Set.univ) := by
    rw [hΦd]
    exact differentiableOn_pi.2 fun j => differentiableOn_eval₂ ψ hψ (Q j)
  have e₀ : ∀ p, MvPolynomial.eval₂ (ψ b₀) x₀ p = χ₀ (algebraMap P.Ring A p) := fun p => by
    rw [algebraMap_ring_eq, h₀, hx₀]

  have eQ : ∀ (b : Fin n → ℂ) (χ : A →+* ℂ), χ.comp (algebraMap R A) = ψ b →
      Φ (b, fun i => χ (P.val i)) = Sum.elim (0 : K₀ → ℂ) (fun c => χ (t c)) := fun b χ hχ => by
    funext j
    rw [hΦd]
    show MvPolynomial.eval₂ (ψ b) _ (Q j) = _
    rw [← hχ, ← algebraMap_ring_eq, hQ]
    rcases j with j | c
    · simp [algebraMap_relation]
    · simp [hT]
  have Φ₀ : Φ (b₀, x₀) = 0 := by
    rw [← hx₀, eQ b₀ χ₀ h₀]
    funext j
    rcases j with j | c
    · rfl
    · exact ht c
  obtain ⟨F₀, hF₀, hF₀v⟩ := hasFDerivAt_family (ψ b₀) Q x₀
  have bij : Function.Bijective F₀ := bijective_base P χ₀ t T hT hinj hsurj F₀ (by
    rw [h₀, hx₀, ← hQ]; exact hF₀v)
  obtain ⟨L, hL⟩ : ∃ L : (I₀ → ℂ) ≃L[ℂ] (K₀ ⊕ Fin g → ℂ),
      (L : (I₀ → ℂ) →L[ℂ] (K₀ ⊕ Fin g → ℂ)) = F₀ :=
    ⟨(LinearEquiv.ofBijective F₀.toLinearMap bij).toContinuousLinearEquiv, by ext; rfl⟩
  obtain ⟨ε', δ', X, ε'0, δ'0, hX₀, hXd, hX, hXinv⟩ := GlobalTheory.T.implicit_function_holomorphic n I₀ (K₀ ⊕ Fin g)
    (B ×ˢ Set.univ) Φ b₀ x₀ L (hB.prod isOpen_univ) ⟨hb₀, trivial⟩ hΦ (by
      rw [hL, hΦd]; exact hF₀)
  rw [Φ₀] at hX₀ hXd hX hXinv
  obtain ⟨ε'', ε''0, hε''⟩ := Metric.isOpen_iff.1 hB b₀ hb₀
  obtain ⟨ε, hε⟩ : ∃ ε, ε = min ε' ε'' := ⟨_, rfl⟩
  have ε0 : 0 < ε := hε ▸ lt_min ε'0 ε''0
  have εa : ε ≤ ε' := hε ▸ min_le_left _ _
  have εb : ε ≤ ε'' := hε ▸ min_le_right _ _
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = min δ' ε := ⟨_, rfl⟩
  have δ0 : 0 < δ := hδ ▸ lt_min δ'0 ε0
  have δa : δ ≤ δ' := hδ ▸ min_le_left _ _
  have δb : δ ≤ ε := hδ ▸ min_le_right _ _
  obtain ⟨emb, hemb⟩ : ∃ emb : (Fin g → ℂ) → (K₀ ⊕ Fin g → ℂ), emb = fun z => Sum.elim (0 : K₀ → ℂ) z :=
    ⟨_, rfl⟩
  have inU : ∀ b ∈ ball b₀ ε, ∀ z ∈ ball (0 : Fin g → ℂ) ε,
      (b, emb z) ∈ ball b₀ ε' ×ˢ ball (0 : K₀ ⊕ Fin g → ℂ) ε' := fun b hb z hz => by
    refine ⟨ball_subset_ball εa hb, ?_⟩
    rw [hemb]
    exact ball_subset_ball εa (elim_mem_ball z ε0 hz)
  have hev : ∀ b x j, Φ (b, x) j = MvPolynomial.eval₂ (ψ b) x (Q j) := fun b x j => by rw [hΦd]
  have rel : ∀ b ∈ ball b₀ ε, ∀ z ∈ ball (0 : Fin g → ℂ) ε, ∀ j,
      MvPolynomial.eval₂ (ψ b) (X (b, emb z)) (P.relation j) = 0 := fun b hb z hz j => by
    have := congrFun (hX _ (inU b hb z hz)).2.1 (Sum.inl j)
    rw [hev, hQ] at this
    rw [hemb] at this ⊢
    simpa using this
  have lf : ∀ (b : Fin n → ℂ) (x : I₀ → ℂ), (∀ j, MvPolynomial.eval₂ (ψ b) x (P.relation j) = 0) →
      ∃ χ : A →+* ℂ, ∀ p, χ (algebraMap P.Ring A p) = MvPolynomial.eval₂ (ψ b) x p :=
    fun b x hx => exists_lift P (MvPolynomial.eval₂Hom (ψ b) x) hx
  choose Ψ₀ hΨ₀ using lf
  obtain ⟨Ψ, hΨd⟩ : ∃ Ψ : (Fin n → ℂ) → (Fin g → ℂ) → (A →+* ℂ), Ψ = fun b z =>
      if h : b ∈ ball b₀ ε ∧ z ∈ ball (0 : Fin g → ℂ) ε then Ψ₀ b _ (rel b h.1 z h.2 ) else χ₀ :=
    ⟨_, rfl⟩
  have hΨ : ∀ b ∈ ball b₀ ε, ∀ z ∈ ball (0 : Fin g → ℂ) ε, ∀ p,
      Ψ b z (algebraMap P.Ring A p) = MvPolynomial.eval₂ (ψ b) (X (b, emb z)) p :=
    fun b hb z hz p => by
      rw [hΨd]
      simp only [dif_pos (show b ∈ ball b₀ ε ∧ z ∈ ball (0 : Fin g → ℂ) ε from ⟨hb, hz⟩)]
      exact hΨ₀ _ _ _ p
  have hcomp : ∀ b ∈ ball b₀ ε, ∀ z ∈ ball (0 : Fin g → ℂ) ε,
      (Ψ b z).comp (algebraMap R A) = ψ b := fun b hb z hz => RingHom.ext fun r => by
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply R P.Ring A r, hΨ b hb z hz]
    exact MvPolynomial.eval₂_C _ _ _
  have hval : ∀ b ∈ ball b₀ ε, ∀ z ∈ ball (0 : Fin g → ℂ) ε,
      (fun i => Ψ b z (P.val i)) = X (b, emb z) := fun b hb z hz => by
    funext i
    rw [show P.val i = algebraMap P.Ring A (MvPolynomial.X i) by simp, hΨ b hb z hz]
    exact MvPolynomial.eval₂_X _ _ _
  have emb0 : emb 0 = 0 := by
    rw [hemb]
    funext j
    rcases j with j | c <;> rfl
  have mb : b₀ ∈ ball b₀ ε := mem_ball_self ε0
  have m0 : (0 : Fin g → ℂ) ∈ ball (0 : Fin g → ℂ) ε := mem_ball_self ε0
  obtain ⟨e⟩ : Nonempty (I₀ ⊕ Fin g ≃ Fin (Fintype.card (I₀ ⊕ Fin g))) :=
    ⟨Fintype.equivFin _⟩
  refine ⟨_, fun j => Sum.elim P.val t (e.symm j), ε, δ, Ψ, ε0, δ0,
    (ball_subset_ball εb).trans hε'', ?_, ?_, ?_, ?_, ?_⟩
  · refine ringHom_ext P fun p => ?_
    rw [hΨ b₀ mb 0 m0, emb0, hX₀, e₀]
  · intro b hb z hz
    refine ⟨hcomp b hb z hz, fun c => ?_, fun D h0 hLD hDt => ?_⟩
    · have := congrFun (hX _ (inU b hb z hz)).2.1 (Sum.inr c)
      rw [hev, hQ, hemb] at this
      rw [← hT c, hΨ b hb z hz, hemb]
      simpa using this
    · obtain ⟨F, hF, hFv⟩ := hasFDerivAt_family (ψ b) Q (X (b, emb z))
      refine der_zero P (Ψ b z) (ψ b) (X (b, emb z)) (hcomp b hb z hz) (hval b hb z hz) t T hT F
        (by rw [← hQ]; exact hFv) (fun v hv => ?_) D h0 hLD hDt
      refine (hX _ (inU b hb z hz)).2.2 v ?_
      have hF' : HasFDerivAt (fun x => Φ (b, x)) F (X (b, emb z)) := by
        rw [hΦd]; exact hF
      show fderiv ℂ (fun x => Φ (b, x)) (X (b, emb z)) v = 0
      rw [hF'.fderiv, hv]
  · intro a
    obtain ⟨p, rfl⟩ := P.algebraMap_surjective a
    have hG : DifferentiableOn ℂ
        (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => (bz.1, X (bz.1, emb bz.2)))
        (ball b₀ ε ×ˢ ball (0 : Fin g → ℂ) ε) := by
      refine differentiableOn_fst.prodMk (hXd.comp (differentiableOn_fst.prodMk ?_) ?_)
      · rw [hemb]
        have hdz : Differentiable ℂ (fun z : Fin g → ℂ => (Sum.elim 0 z : K₀ ⊕ Fin g → ℂ)) :=
          differentiable_elim
        exact (hdz.comp (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (Fin g → ℂ)).differentiable).differentiableOn
      · exact fun bz hbz => inU _ hbz.1 _ hbz.2
    refine DifferentiableOn.congr (f := fun bz : (Fin n → ℂ) × (Fin g → ℂ) =>
      MvPolynomial.eval₂ (ψ bz.1) (X (bz.1, emb bz.2)) p) ?_ fun bz hbz => hΨ _ hbz.1 _ hbz.2 p
    exact (differentiableOn_eval₂ ψ hψ p).comp hG fun bz hbz =>
      ⟨hε'' (ball_subset_ball εb hbz.1), trivial⟩
  · exact fun c => ⟨e (Sum.inr c), by simp⟩
  · intro b hb χ hχ hj
    have hb' : b ∈ ball b₀ ε := ball_subset_ball δb hb
    have hx : (fun i => χ (P.val i)) ∈ ball x₀ δ' := by
      refine (dist_pi_lt_iff δ'0).2 fun i => ?_
      have := hj (e (Sum.inl i))
      rw [← hx₀, dist_eq_norm]
      simp only [Equiv.symm_apply_apply, Sum.elim_inl] at this
      exact this.trans_le δa
    have hz : (fun c => χ (t c)) ∈ ball (0 : Fin g → ℂ) ε := by
      refine (dist_pi_lt_iff ε0).2 fun c => ?_
      have := hj (e (Sum.inr c))
      simp only [Equiv.symm_apply_apply, Sum.elim_inr, ht, sub_zero] at this
      rw [dist_eq_norm]
      simpa using this.trans_le δb
    refine ⟨hz, ?_⟩
    have hinv := (hXinv b (ball_subset_ball δa hb) _ hx).2.2
    rw [eQ b χ hχ] at hinv
    refine ringHom_ext P fun p => ?_
    rw [hΨ b hb' _ hz, hemb]
    show _ = MvPolynomial.eval₂ (ψ b) (X (b, Sum.elim (0 : K₀ → ℂ) fun c => χ (t c))) p
    rw [hinv, algebraMap_ring_eq, hχ]

end GlobalTheory.CompanionTheory.Ar.StdSmoothChart
