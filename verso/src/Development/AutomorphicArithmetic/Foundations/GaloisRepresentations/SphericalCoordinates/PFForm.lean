import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LineBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

/- English proof (translation)
Set `e : F ≃ₐ[ℚ] F` to `AlgEquiv.ofRingEquiv (f := (IsCMField.complexConj F).toRingEquiv) (fun r => by simp)`. Conclude with `Algebra.trace_eq_of_algEquiv e x`.
-/
private theorem trace_conj {F : Type} [Field F] [NumberField F] [IsCMField F] (x : F) :
    Algebra.trace ℚ F (IsCMField.complexConj F x) = Algebra.trace ℚ F x := by
  let e : F ≃ₐ[ℚ] F := AlgEquiv.ofRingEquiv (f := (IsCMField.complexConj F).toRingEquiv) (fun r => by simp)
  exact Algebra.trace_eq_of_algEquiv e x

/- English proof (translation)
Establish `hnd` using `traceForm_nondegenerate ℚ F`. Establish `: a - b = 0`. Apply `hnd.1` to reduce the goal to its premises. Introduce `x`. Use `show Algebra.trace ℚ F ((a - b) * x) = 0`.

Rewrite using `[sub_mul, map_sub, h, sub_self]`. Conclude with `sub_eq_zero.1 this`.
-/
private theorem trace_strip {F : Type} [Field F] [NumberField F] {a b : F}
    (h : ∀ x : F, Algebra.trace ℚ F (a * x) = Algebra.trace ℚ F (b * x)) : a = b := by
  have hnd := traceForm_nondegenerate ℚ F
  have : a - b = 0 := by
    apply hnd.1
    intro x
    show Algebra.trace ℚ F ((a - b) * x) = 0
    rw [sub_mul, map_sub, h, sub_self]
  exact sub_eq_zero.1 this

/- English proof (translation)
Establish `hnd` using `traceForm_nondegenerate ℚ F`. Use `⟨(LinearMap.BilinForm.toDual _ hnd).symm f.toRatLinearMap, fun x => ?_⟩` and prove the remaining obligations. Conclude with `LinearMap.BilinForm.apply_toDual_symm_apply (hB := hnd) f.toRatLinearMap x`.
-/
private theorem exists_trace_rep {F : Type} [Field F] [NumberField F] (f : F →+ ℚ) :
    ∃ a : F, ∀ x, Algebra.trace ℚ F (a * x) = f x := by
  have hnd := traceForm_nondegenerate ℚ F
  refine ⟨(LinearMap.BilinForm.toDual _ hnd).symm f.toRatLinearMap, fun x => ?_⟩
  exact LinearMap.BilinForm.apply_toDual_symm_apply (hB := hnd) f.toRatLinearMap x

/- English proof (translation)
Use extensionality with `k`. Simplify using `[Finset.sum_apply, Pi.single_apply]`.
-/
private theorem sum_single {F : Type} [Field F] {n : ℕ} (u : Fin n → F) :
    u = ∑ j, u j • (Pi.single j 1 : Fin n → F) := by
  ext k
  simp [Finset.sum_apply, Pi.single_apply]

/- English proof (translation)
Use extensionality with `i j`. Apply `trace_strip` to reduce the goal to its premises. Introduce `x`. Use `h (x • Pi.single j 1) (Pi.single i 1)` as an intermediate fact. Establish `e : ∀ P : Matrix (Fin n) (Fin n) F, (fun k => IsCMField.complexConj F ((Pi.single i 1 : Fin n → F) k)) ⬝ᵥ (P *ᵥ (x • Pi.single j 1)) = P i j * x`.

Introduce `P`. Establish `e1 : (fun k => IsCMField.complexConj F ((Pi.single i 1 : Fin n → F) k)) = (Pi.single i 1 : Fin n → F)`. Use extensionality with `k`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hk]`. Rewrite using `[e1, Matrix.mulVec_smul, Matrix.mulVec_single_one, single_one_dotProduct]`. Simplify using `[mul_comm]`. Rewrite `this` using `[e M, e N]`. Then use the resulting hypothesis.
-/
private theorem form_ext {F : Type} [Field F] [NumberField F] [IsCMField F] {n : ℕ}
    {M N : Matrix (Fin n) (Fin n) F}
    (h : ∀ u w : Fin n → F, Algebra.trace ℚ F ((fun i => IsCMField.complexConj F (w i)) ⬝ᵥ (M *ᵥ u)) =
      Algebra.trace ℚ F ((fun i => IsCMField.complexConj F (w i)) ⬝ᵥ (N *ᵥ u))) : M = N := by
  ext i j
  apply trace_strip
  intro x
  have := h (x • Pi.single j 1) (Pi.single i 1)
  have e : ∀ P : Matrix (Fin n) (Fin n) F,
      (fun k => IsCMField.complexConj F ((Pi.single i 1 : Fin n → F) k)) ⬝ᵥ (P *ᵥ (x • Pi.single j 1)) = P i j * x := by
    intro P
    have e1 : (fun k => IsCMField.complexConj F ((Pi.single i 1 : Fin n → F) k)) = (Pi.single i 1 : Fin n → F) := by
      ext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [Pi.single_apply, hk]
    rw [e1, Matrix.mulVec_smul, Matrix.mulVec_single_one, single_one_dotProduct]
    simp [mul_comm]
  rwa [e M, e N] at this

/- English proof (translation)
Establish `hrep : ∀ i j : Fin n, ∃ a : F, ∀ x, Algebra.trace ℚ F (a * x) = B (x • (Pi.single j 1 : Fin n → F)) (Pi.single i 1)` using `fun i j => exists_trace_rep (((AddMonoidHom.eval (Pi.single i 1 : Fin n → F)).comp B).comp (AddMonoidHom.mk' (fun x : F => x • (Pi.single j 1 : Fin n → F)) (fun a b => add_smul a b _)))`. Use `choose A₀ hA₀ using hrep`. Take `⟨A, hA⟩ : ∃ A : Matrix (Fin n) (Fin n) F, ∀ i j x, Algebra.trace ℚ F (A i j * x) = B (x • (Pi.single j 1 : Fin n → F)) (Pi.single i 1)` from `⟨A₀, hA₀⟩`. Establish `hterm : ∀ (u w : Fin n → F) i j, B (u j • (Pi.single j 1 : Fin n → F)) (w i • (Pi.single i 1 : Fin n → F)) = Algebra.trace ℚ F (IsCMField.complexConj F (w i) * (A i j * u j))`. Introduce `u w i j`.

Establish `e1 : B (u j • (Pi.single j 1 : Fin n → F)) (w i • (Pi.single i 1 : Fin n → F)) = B (IsCMField.complexConj F (w i) • (u j • (Pi.single j 1 : Fin n → F))) (Pi.single i 1)`. Rewrite using `[hadj (IsCMField.complexConj F (w i)) (u j • _), IsCMField.complexConj_apply_apply]`. Rewrite using `[e1, smul_smul, ← hA]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `hform : ∀ u w, B u w = Algebra.trace ℚ F ((fun i => IsCMField.complexConj F (w i)) ⬝ᵥ (A *ᵥ u))`. Introduce `u w`. Use `conv_lhs => rw [sum_single u, sum_single w]`. Simplify using `only [map_sum, AddMonoidHom.finset_sum_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, hterm]`. Use `⟨A, ?_, ?_, hform⟩` and prove the remaining obligations.

Introduce `hdet`. Take `⟨v, hv, hAv⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 hdet`. Conclude with `hv (hnd v fun w => by rw [hform, hAv]; simp)`. Use extensionality with `i j show IsCMField.complexConj F (A j i) = - A i j`. Apply `trace_strip` to reduce the goal to its premises.

Introduce `x`. Establish `h1 : Algebra.trace ℚ F (IsCMField.complexConj F (A j i) * x) = Algebra.trace ℚ F (A j i * IsCMField.complexConj F x)`. Rewrite using `[← trace_conj (A j i * IsCMField.complexConj F x), map_mul (IsCMField.complexConj F), IsCMField.complexConj_apply_apply]`. Rewrite using `[h1, hA, hadj, IsCMField.complexConj_apply_apply, hskew, ← hA, neg_mul, map_neg]`.
-/
private theorem form_core {F : Type} [Field F] [NumberField F] [IsCMField F] {n : ℕ}
    (B : (Fin n → F) →+ (Fin n → F) →+ ℚ)
    (hadj : ∀ (x : F) u w, B (x • u) w = B u (IsCMField.complexConj F x • w))
    (hskew : ∀ u w, B u w = - B w u)
    (hnd : ∀ u, (∀ w, B u w = 0) → u = 0) :
    ∃ A : Matrix (Fin n) (Fin n) F, A.det ≠ 0 ∧ (A.map (IsCMField.complexConj F))ᵀ = -A ∧
      ∀ u w, B u w = Algebra.trace ℚ F ((fun i => IsCMField.complexConj F (w i)) ⬝ᵥ (A *ᵥ u)) := by
  have hrep : ∀ i j : Fin n, ∃ a : F, ∀ x, Algebra.trace ℚ F (a * x) =
      B (x • (Pi.single j 1 : Fin n → F)) (Pi.single i 1) := fun i j =>
    exists_trace_rep (((AddMonoidHom.eval (Pi.single i 1 : Fin n → F)).comp B).comp
      (AddMonoidHom.mk' (fun x : F => x • (Pi.single j 1 : Fin n → F)) (fun a b => add_smul a b _)))
  choose A₀ hA₀ using hrep
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin n) (Fin n) F, ∀ i j x, Algebra.trace ℚ F (A i j * x) =
      B (x • (Pi.single j 1 : Fin n → F)) (Pi.single i 1) := ⟨A₀, hA₀⟩
  have hterm : ∀ (u w : Fin n → F) i j, B (u j • (Pi.single j 1 : Fin n → F)) (w i • (Pi.single i 1 : Fin n → F)) =
      Algebra.trace ℚ F (IsCMField.complexConj F (w i) * (A i j * u j)) := by
    intro u w i j
    have e1 : B (u j • (Pi.single j 1 : Fin n → F)) (w i • (Pi.single i 1 : Fin n → F)) =
        B (IsCMField.complexConj F (w i) • (u j • (Pi.single j 1 : Fin n → F))) (Pi.single i 1) := by
      rw [hadj (IsCMField.complexConj F (w i)) (u j • _), IsCMField.complexConj_apply_apply]
    rw [e1, smul_smul, ← hA]
    congr 1
    ring
  have hform : ∀ u w, B u w = Algebra.trace ℚ F ((fun i => IsCMField.complexConj F (w i)) ⬝ᵥ (A *ᵥ u)) := by
    intro u w
    conv_lhs => rw [sum_single u, sum_single w]
    simp only [map_sum, AddMonoidHom.finset_sum_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, hterm]
  refine ⟨A, ?_, ?_, hform⟩
  · intro hdet
    obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    exact hv (hnd v fun w => by rw [hform, hAv]; simp)
  · ext i j
    show IsCMField.complexConj F (A j i) = - A i j
    apply trace_strip
    intro x
    have h1 : Algebra.trace ℚ F (IsCMField.complexConj F (A j i) * x) =
        Algebra.trace ℚ F (A j i * IsCMField.complexConj F x) := by
      rw [← trace_conj (A j i * IsCMField.complexConj F x), map_mul (IsCMField.complexConj F), IsCMField.complexConj_apply_apply]
    rw [h1, hA, hadj, IsCMField.complexConj_apply_apply, hskew, ← hA, neg_mul, map_neg]

/- English proof (translation)
Establish `hs : ∀ x y, E x y = - E y x`. Introduce `x y`. Establish `h` using `halt (x + y)`. Simplify using `only [map_add, LinearMap.add_apply, halt, zero_add, add_zero] at h`. Conclude with `eq_neg_of_add_eq_zero_right h`.

Proceed by induction on `u using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb, neg_add]`. Consider the case `tmul a x`. Proceed by induction on `w using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add c d hc hd => simp only [map_add, LinearMap.add_apply, hc, hd, neg_add]`. Consider the case `tmul b y`. Simplify using `only [LinearMap.BilinForm.baseChange_tmul]`. Rewrite using `[hs x y]`.

Simplify using `[mul_comm]`.
-/
private theorem bc_skew {La : Type} [AddCommGroup La] (E : LinearMap.BilinForm ℤ La) (halt : ∀ x, E x x = 0)
    (u w : ℚ ⊗[ℤ] La) : E.baseChange ℚ u w = - E.baseChange ℚ w u := by
  have hs : ∀ x y, E x y = - E y x := by
    intro x y
    have h := halt (x + y)
    simp only [map_add, LinearMap.add_apply, halt, zero_add, add_zero] at h
    exact eq_neg_of_add_eq_zero_right h
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb, neg_add]
  | tmul a x =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add c d hc hd => simp only [map_add, LinearMap.add_apply, hc, hd, neg_add]
    | tmul b y =>
      simp only [LinearMap.BilinForm.baseChange_tmul]
      rw [hs x y]
      simp [mul_comm]

/- English proof (translation)
Proceed by induction on `v using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨1, 0, one_ne_zero, by simp⟩`. Consider the case `add a b ha hb`. Take `⟨N, x, hN, hx⟩` from `ha`. Take `⟨M, y, hM, hy⟩` from `hb`.

Use `⟨N * M, M • x + N • y, mul_ne_zero hN hM, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add, TensorProduct.tmul_add, mul_comm N M, mul_smul, hx, mul_comm M N, mul_smul, hy, TensorProduct.tmul_smul, TensorProduct.tmul_smul]`. Consider the case `tmul a x`. Use `⟨a.den, a.num • x, a.den_ne_zero, ?_⟩` and prove the remaining obligations. Rewrite using `[TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul']`.

Use `congr 1`. Rewrite using `[nsmul_eq_mul, zsmul_eq_mul, _root_.mul_one, Rat.den_mul_eq_num]`.
-/
private theorem exists_pure {La : Type} [AddCommGroup La] (v : ℚ ⊗[ℤ] La) :
    ∃ (N : ℕ) (x : La), N ≠ 0 ∧ N • v = (1 : ℚ) ⊗ₜ[ℤ] x := by
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
  | add a b ha hb =>
    obtain ⟨N, x, hN, hx⟩ := ha
    obtain ⟨M, y, hM, hy⟩ := hb
    refine ⟨N * M, M • x + N • y, mul_ne_zero hN hM, ?_⟩
    rw [smul_add, TensorProduct.tmul_add, mul_comm N M, mul_smul, hx, mul_comm M N, mul_smul, hy,
      TensorProduct.tmul_smul, TensorProduct.tmul_smul]
  | tmul a x =>
    refine ⟨a.den, a.num • x, a.den_ne_zero, ?_⟩
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
    congr 1
    rw [nsmul_eq_mul, zsmul_eq_mul, _root_.mul_one, Rat.den_mul_eq_num]

/- English proof (translation)
Take `⟨N, x, hN, hx⟩` from `exists_pure v`. Establish `hx0 : x = 0`. Apply `hE` to reduce the goal to its premises. Use extensionality with `y`. Establish `h1` using `h ((1 : ℚ) ⊗ₜ[ℤ] y)`.

Establish `h2 : E.baseChange ℚ (N • v) ((1 : ℚ) ⊗ₜ[ℤ] y) = 0` using `by simp [h1]`. Rewrite `h2` using `[hx, LinearMap.BilinForm.baseChange_tmul]`. Simplify using `using h2`. Rewrite `hx` using `[hx0, TensorProduct.tmul_zero]`. Establish `: (N : ℚ) • v = 0` using `by rw [Nat.cast_smul_eq_nsmul]; exact hx`.

Conclude with `(smul_eq_zero.1 this).resolve_left (by exact_mod_cast hN)`.
-/
private theorem bc_nondeg {La : Type} [AddCommGroup La] (E : LinearMap.BilinForm ℤ La)
    (hE : Function.Injective E) (v : ℚ ⊗[ℤ] La) (h : ∀ w, E.baseChange ℚ v w = 0) : v = 0 := by
  obtain ⟨N, x, hN, hx⟩ := exists_pure v
  have hx0 : x = 0 := by
    apply hE
    ext y
    have h1 := h ((1 : ℚ) ⊗ₜ[ℤ] y)
    have h2 : E.baseChange ℚ (N • v) ((1 : ℚ) ⊗ₜ[ℤ] y) = 0 := by simp [h1]
    rw [hx, LinearMap.BilinForm.baseChange_tmul] at h2
    simpa using h2
  rw [hx0, TensorProduct.tmul_zero] at hx
  have : (N : ℚ) • v = 0 := by rw [Nat.cast_smul_eq_nsmul]; exact hx
  exact (smul_eq_zero.1 this).resolve_left (by exact_mod_cast hN)

/- English proof (translation)
Introduce `p _ D G L kp σ hF`. Set `E` to `D.EF.baseChange ℚ`. Set `B : (Fin G.n → G.F) →+ (Fin G.n → G.F) →+ ℚ` to `AddMonoidHom.mk' (fun u => AddMonoidHom.mk' (fun w => E (kp.symm u) (kp.symm w)) (by intro a b; simp)) (by intro a b; ext w; simp)`. Establish `hB : ∀ u w, B u w = E (kp.symm u) (kp.symm w)` using `fun _ _ => rfl`. Establish `hsc : ∀ (x : G.F) (u : Fin G.n → G.F), kp.symm (x • u) = L.rep (algebraMap G.F G.C x) (kp.symm u)`.

Introduce `x u`. Apply `kp.injective` to reduce the goal to its premises. Rewrite using `[AddEquiv.apply_symm_apply, hF, AddEquiv.apply_symm_apply, AlgEquiv.commutes]`. Use extensionality with `i`. Simplify using `[Matrix.algebraMap_eq_diagonal, Matrix.mulVec_diagonal]`.

Establish `hsm : ∀ (c : G.C) (u : Fin G.n → G.F), kp.symm (σ c *ᵥ u) = L.rep c (kp.symm u)`. Introduce `c u`. Apply `kp.injective` to reduce the goal to its premises. Rewrite using `[AddEquiv.apply_symm_apply, hF, AddEquiv.apply_symm_apply]`. Take `⟨A, hdet, hskew, hform⟩` from `form_core B (by`.

Introduce `x u w`. Rewrite using `[hB, hB, hsc, hsc, L.adj]`. Use `show E _ (L.rep ((G.star _).unop) _) = _`. Rewrite using `[G.star_F])`. Use the proof step `(by intro u w; exact bc_skew D.EF D.alt _ _)`.

Use the proof step `(by`. Introduce `u hu`. Establish `h0 : kp.symm u = 0` using `bc_nondeg D.EF D.nondeg _ fun w => by`. Use `hu (kp w)` as an intermediate fact. Rewrite `this` using `[hB, AddEquiv.symm_apply_apply]`. Then use the resulting hypothesis.

Simplify using `using congrArg kp h0)`. Establish `hform' : ∀ u w, E u w = Algebra.trace ℚ G.F ((fun i => IsCMField.complexConj G.F (kp w i)) ⬝ᵥ (A *ᵥ kp u))`. Introduce `u w`. Use `hform (kp u) (kp w)` as an intermediate fact. Rewrite `this` using `[hB, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]`. Then use the resulting hypothesis.

Use `⟨A, hdet, hskew, hform', fun c => ?_⟩` and prove the remaining obligations. Apply `form_ext` to reduce the goal to its premises. Introduce `u w`. Establish `hcj : (fun i => IsCMField.complexConj G.F (w i)) ⬝ᵥ (((σ c).map (IsCMField.complexConj G.F))ᵀ * A) *ᵥ u = (fun i => IsCMField.complexConj G.F ((σ c *ᵥ w) i)) ⬝ᵥ (A *ᵥ u)`. Rewrite using `[← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]`.

Use `congr 1`. Use extensionality with `i`. Simplify using `[Matrix.mulVec, dotProduct, map_sum, map_mul]`. Rewrite using `[hcj, ← Matrix.mulVec_mulVec]`. Establish `h1` using `hform (σ (sh G c) *ᵥ u) w`.

Establish `h2` using `hform u (σ c *ᵥ w)`. Rewrite using `[← h1, ← h2, hB, hB, hsm, hsm]`. Establish `h3 : sh G (sh G c) = c` using `G.star_star c`. Establish `h4` using `L.adj (sh G c) (kp.symm u) (kp.symm w)`. Rewrite `h4` using `[h3]`.

Conclude with `h4`.
-/
theorem UpperTheory.Gal.W2.fForm_of :
    UpperTheory.Gal.W2.FForm := by
  intro p _ D G L kp σ hF
  let E := D.EF.baseChange ℚ
  let B : (Fin G.n → G.F) →+ (Fin G.n → G.F) →+ ℚ :=
    AddMonoidHom.mk' (fun u => AddMonoidHom.mk' (fun w => E (kp.symm u) (kp.symm w)) (by intro a b; simp))
      (by intro a b; ext w; simp)
  have hB : ∀ u w, B u w = E (kp.symm u) (kp.symm w) := fun _ _ => rfl
  have hsc : ∀ (x : G.F) (u : Fin G.n → G.F),
      kp.symm (x • u) = L.rep (algebraMap G.F G.C x) (kp.symm u) := by
    intro x u
    apply kp.injective
    rw [AddEquiv.apply_symm_apply, hF, AddEquiv.apply_symm_apply, AlgEquiv.commutes]
    ext i
    simp [Matrix.algebraMap_eq_diagonal, Matrix.mulVec_diagonal]
  have hsm : ∀ (c : G.C) (u : Fin G.n → G.F), kp.symm (σ c *ᵥ u) = L.rep c (kp.symm u) := by
    intro c u
    apply kp.injective
    rw [AddEquiv.apply_symm_apply, hF, AddEquiv.apply_symm_apply]
  obtain ⟨A, hdet, hskew, hform⟩ := form_core B
    (by
      intro x u w
      rw [hB, hB, hsc, hsc, L.adj]
      show E _ (L.rep ((G.star _).unop) _) = _
      rw [G.star_F])
    (by intro u w; exact bc_skew D.EF D.alt _ _)
    (by
      intro u hu
      have h0 : kp.symm u = 0 := bc_nondeg D.EF D.nondeg _ fun w => by
        have := hu (kp w)
        rwa [hB, AddEquiv.symm_apply_apply] at this
      simpa using congrArg kp h0)
  have hform' : ∀ u w, E u w = Algebra.trace ℚ G.F ((fun i => IsCMField.complexConj G.F (kp w i)) ⬝ᵥ (A *ᵥ kp u)) := by
    intro u w
    have := hform (kp u) (kp w)
    rwa [hB, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply] at this
  refine ⟨A, hdet, hskew, hform', fun c => ?_⟩
  apply form_ext
  intro u w
  have hcj : (fun i => IsCMField.complexConj G.F (w i)) ⬝ᵥ
        (((σ c).map (IsCMField.complexConj G.F))ᵀ * A) *ᵥ u =
      (fun i => IsCMField.complexConj G.F ((σ c *ᵥ w) i)) ⬝ᵥ (A *ᵥ u) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    congr 1
    ext i
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rw [hcj, ← Matrix.mulVec_mulVec]
  have h1 := hform (σ (sh G c) *ᵥ u) w
  have h2 := hform u (σ c *ᵥ w)
  rw [← h1, ← h2, hB, hB, hsm, hsm]
  have h3 : sh G (sh G c) = c := G.star_star c
  have h4 := L.adj (sh G c) (kp.symm u) (kp.symm w)
  rw [h3] at h4
  exact h4
