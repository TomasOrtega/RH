import ReciprocityTheory.DualLattices.PrimeHopfOrderStatement

noncomputable section

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

section Transport

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {X Y : Type} [AddCommGroup X] [Fintype X] [DecidableEq X]
  [AddCommGroup Y] [Fintype Y] [DecidableEq Y]

abbrev pbE (e : X ≃+ Y) : (Y → C) ≃ₗ[R] (X → C) := LinearEquiv.funCongrLeft R C e.toEquiv

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma pbE_apply (e : X ≃+ Y) (f : Y → C) (x : X) : pbE (C := C) (R := R) e f x = f (e x) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma pbE_symm_apply (e : X ≃+ Y) (f : X → C) (y : Y) :
    (pbE (C := C) (R := R) e).symm f y = f (e.symm y) := by
  rfl

/- English proof (translation)
The claim follows from `Matrix.det_submatrix_equiv_self e.toEquiv B`.
-/
lemma det_sub (e : X ≃+ Y) (B : Matrix Y Y C) : (B.submatrix e e).det = B.det :=
  Matrix.det_submatrix_equiv_self e.toEquiv B

/- English proof (translation)
Rewrite using `[Submodule.map_span, ← Set.range_comp]`. Establish `h : (fun j x => (B.submatrix e e) x j) = ((pbE (C` using `C) (R := R) e : (Y → C) →ₗ[R] (X → C)) ∘ fun j y => B y j) ∘ e := by`. Use function extensionality and compare the values at `j x`. Both sides reduce to the same expression. Rewrite using `[h, e.surjective.range_comp]`.
-/
lemma map_cols (e : X ≃+ Y) (B : Matrix Y Y C) :
    (Submodule.span R (Set.range fun j y => B y j)).map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) =
      Submodule.span R (Set.range fun j x => (B.submatrix e e) x j) := by
  rw [Submodule.map_span, ← Set.range_comp]
  have h : (fun j x => (B.submatrix e e) x j) =
      ((pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) ∘ fun j y => B y j) ∘ e := by
    funext j x
    rfl
  rw [h, e.surjective.range_comp]

/- English proof (translation)
Take `⟨B, hM, hc⟩` from `h`. Conclude with `⟨B.submatrix e e, by rw [hM, map_cols], by rw [det_sub, hc]⟩`.
-/
lemma hasColen_map (v : Valuation C NNReal) (e : X ≃+ Y) (M : Submodule R (Y → C)) (c : NNReal)
    (h : HasColen R v M c) : HasColen R v (M.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C))) c := by
  obtain ⟨B, hM, hc⟩ := h
  exact ⟨B.submatrix e e, by rw [hM, map_cols], by rw [det_sub, hc]⟩

/- English proof (translation)
Rewrite using `[← Submodule.map_comp]`. Establish `h : ((pbE (C` using `C) (R := R) e.symm : (X → C) →ₗ[R] (Y → C)).comp (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C))) = LinearMap.id := by`. Use `LinearMap.ext fun f => funext fun y => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, pbE_apply, LinearMap.id_apply, AddEquiv.apply_symm_apply]`. Rewrite using `[h, Submodule.map_id]`.
-/
lemma map_pbE_symm (e : X ≃+ Y) (M : Submodule R (Y → C)) :
    (M.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C))).map (pbE (C := C) (R := R) e.symm : (X → C) →ₗ[R] (Y → C)) = M := by
  rw [← Submodule.map_comp]
  have h : ((pbE (C := C) (R := R) e.symm : (X → C) →ₗ[R] (Y → C)).comp
      (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C))) = LinearMap.id := by
    refine LinearMap.ext fun f => funext fun y => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, pbE_apply, LinearMap.id_apply,
      AddEquiv.apply_symm_apply]
  rw [h, Submodule.map_id]

def hopfPull (e : X ≃+ Y) (A : HopfOrder (C := C) R Y) : HopfOrder (C := C) R X where
  carrier := A.carrier.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C))
  lat := by
    obtain ⟨B, hB, hA⟩ := A.lat
    exact ⟨B.submatrix e e, by rwa [det_sub], by rw [hA, map_cols]⟩
  le_int := by
    intro f hf
    rw [Submodule.mem_map_equiv] at hf
    have h := A.le_int hf
    intro x
    obtain ⟨r, hr⟩ := h (e x)
    exact ⟨r, by rw [hr, pbE_symm_apply, AddEquiv.symm_apply_apply]⟩
  one_mem := by
    rw [Submodule.mem_map_equiv]
    convert A.one_mem using 1
    funext y
    simp [pbE_symm_apply]
  mul_mem := fun f g hf hg => by
    rw [Submodule.mem_map_equiv] at hf hg ⊢
    convert A.mul_mem _ _ hf hg using 1
    funext y
    simp only [pbE_symm_apply, Pi.mul_apply]
  comul := by
    intro f hf
    rw [Submodule.mem_map_equiv] at hf
    set g := (pbE (C := C) (R := R) e).symm f with hg
    have hfg : f = pbE (C := C) (R := R) e g := by rw [hg, LinearEquiv.apply_symm_apply]
    let pb2 : (Y × Y → C) →ₗ[R] (X × X → C) :=
      LinearMap.funLeft R C (fun q : X × X => (e q.1, e q.2))
    have h1 : addPull R X f = pb2 (addPull R Y g) := by
      funext q
      rw [hfg]
      simp only [addPull, pb2, LinearMap.funLeft_apply, pbE_apply, map_add]
    rw [h1]
    have h2 := A.comul g hf
    have h3 : (tensorSpan R A.carrier).map pb2 ≤ tensorSpan R (A.carrier.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C))) := by
      rw [tensorSpan, Submodule.map_span_le]
      rintro F ⟨g1, hg1, h1', hh1, rfl⟩
      exact Submodule.subset_span ⟨pbE (C := C) (R := R) e g1, Submodule.mem_map_of_mem hg1,
        pbE (C := C) (R := R) e h1', Submodule.mem_map_of_mem hh1, rfl⟩
    exact h3 (Submodule.mem_map_of_mem h2)
  antipode := fun f hf => by
    rw [Submodule.mem_map_equiv] at hf ⊢
    convert A.antipode _ hf using 1
    funext y
    simp only [pbE_symm_apply, map_neg]

/- English proof (translation)
Use function extensionality and compare the values at `y`. Simplify using `only [pbE_symm_apply, Pi.pow_apply]`.
-/
private theorem pbE_symm_pow (e : X ≃+ Y) (f : X → C) (n : ℕ) :
    (pbE (C := C) (R := R) e).symm (f ^ n) = ((pbE (C := C) (R := R) e).symm f) ^ n := by
  funext y
  simp only [pbE_symm_apply, Pi.pow_apply]

/- English proof (translation)
Rewrite using `[show (hopfPull e A).carrier = A.carrier.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) from rfl]`. Simplify using `only [ReciprocityTheory.PGsh.L2.augIdeal, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.proj_apply, Submodule.mem_map_equiv, pbE_symm_apply, map_zero]`.
-/
lemma mem_augIdeal_pull (e : X ≃+ Y) (A : HopfOrder (C := C) R Y) (f : X → C) :
    f ∈ augIdeal (hopfPull e A).carrier ↔ (pbE (C := C) (R := R) e).symm f ∈ augIdeal A.carrier := by
  rw [show (hopfPull e A).carrier =
      A.carrier.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) from rfl]
  simp only [ReciprocityTheory.PGsh.L2.augIdeal, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.proj_apply,
    Submodule.mem_map_equiv, pbE_symm_apply, map_zero]

end Transport

/- English proof (translation)
Introduce `k`. Simplify using `only [ReciprocityTheory.PGsh.L2.augIdeal, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.proj_apply] at hx ⊢`. Use `⟨?_, by rw [Pi.pow_apply, hx.2, zero_pow (Nat.succ_ne_zero k)]⟩` and prove the remaining obligations. Proceed by induction on `k with`. Consider the case `zero => rw [zero_add, pow_one]`.

Conclude with `hx.1`. Consider the case `succ k ih => rw [pow_succ]`. Conclude with `A.mul_mem _ _ ih hx.1`.
-/
lemma pow_mem_aug {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {X : Type}
    [AddCommGroup X] [Fintype X] [DecidableEq X] (A : HopfOrder (C := C) R X) {x : X → C}
    (hx : x ∈ augIdeal A.carrier) : ∀ k : ℕ, x ^ (k + 1) ∈ augIdeal A.carrier := by
  intro k
  simp only [ReciprocityTheory.PGsh.L2.augIdeal, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.proj_apply] at hx ⊢
  refine ⟨?_, by rw [Pi.pow_apply, hx.2, zero_pow (Nat.succ_ne_zero k)]⟩
  induction k with
  | zero => rw [zero_add, pow_one]; exact hx.1
  | succ k ih => rw [pow_succ]; exact A.mul_mem _ _ ih hx.1

/- English proof (translation)
Take `⟨x, _, δ, hx, hx0, -, -, -, hxp, hδ, -, haug, -, hcol⟩` from `hU3 p C v R hv hp (hopfPull e AK)`. Establish `hxa : x ∈ ReciprocityTheory.PGsh.L2.augIdeal (hopfPull e AK).carrier`. Simplify using `only [ReciprocityTheory.PGsh.L2.augIdeal, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.proj_apply]`. Conclude with `⟨hx, hx0⟩`. Establish `hxK` using `(mem_augIdeal_pull e AK x).1 hxa`.

Use `⟨(pbE (C := C) (R := R) e).symm x, δ, x 1, hxK, ?_, hδ, ?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `k`. Establish `h` using `congrFun hxp (e.symm k)`. Simplify using `only [Pi.pow_apply] at h ⊢`. Rewrite using `[pbE_symm_apply]`.

Conclude with `h`. Establish `key : ∀ F ∈ Submodule.span R {y | ∃ j : ℕ, 1 ≤ j ∧ j < p ∧ y = x ^ j}, ∃ r : R, (pbE (C` using `C) (R := R) e).symm F - r • (pbE (C := C) (R := R) e).symm x ∈ ReciprocityTheory.PGsh.L2.augIdeal AK.carrier * ReciprocityTheory.PGsh.L2.augIdeal AK.carrier := by`. Introduce `F hF`. Proceed by induction on `hF using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨j, hj1, -, rfl⟩` from `hy`. Break down `Nat.lt_or_ge j 2 with hj | hj` into its components or cases. Take `rfl : j = 1` from `by omega`. Use `⟨1, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_one, one_smul, sub_self]`.

Conclude with `zero_mem _`. Take `⟨m, rfl⟩ : ∃ m, j = m + 2` from `⟨j - 2, by omega⟩`. Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[zero_smul, sub_zero, pbE_symm_pow, show m + 2 = (m + 1) + 1 from rfl, pow_succ]`. Conclude with `Submodule.mul_mem_mul (pow_mem_aug AK hxK m) hxK`.

Consider the case `zero`. Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[map_zero, zero_smul, sub_zero]`. Conclude with `zero_mem _`. Consider the case `add a b _ _ ha hb`.

Take `⟨r1, h1⟩` from `ha`. Take `⟨r2, h2⟩` from `hb`. Use `⟨r1 + r2, ?_⟩` and prove the remaining obligations. Use `add_mem h1 h2 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_add, add_smul]`.

Normalize the expressions using the abelian group laws. Consider the case `smul c a _ ha`. Take `⟨r1, h1⟩` from `ha`. Use `⟨c * r1, ?_⟩` and prove the remaining obligations. Use `Submodule.smul_mem _ c h1 using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[map_smul, smul_sub, mul_smul]`. Introduce `f hf`. Establish `hF : pbE (C` using `C) (R := R) e f ∈ ReciprocityTheory.PGsh.L2.augIdeal (hopfPull e AK).carrier := by`. Rewrite using `[mem_augIdeal_pull, LinearEquiv.symm_apply_apply]`. Conclude with `hf`.

Rewrite `hF` using `[haug]`. Take `⟨r, hr⟩` from `key _ hF`. Rewrite `hr` using `[LinearEquiv.symm_apply_apply]`. Conclude with `⟨r, hr⟩`. Establish `hc` using `hasColen_map v e.symm _ _ hcol`.

Rewrite `hc` using `[show (hopfPull e AK).carrier = AK.carrier.map (pbE (C := C) (R := R) e : (K → C) →ₗ[R] (ZMod p → C)) from rfl, map_pbE_symm]`. Then use the resulting hypothesis.
-/
theorem primeHopfOrder_of_addEquiv (hU3 : PrimeHopfOrderStatement) (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C]
    [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C]
    (hv : v.Integers R) (hp : v (p : C) < 1) {K : Type} [AddCommGroup K] [Fintype K]
    [DecidableEq K] (e : ZMod p ≃+ K) (AK : HopfOrder (C := C) R K) :
    ∃ (xK : K → C) (δ : R) (x1 : C), xK ∈ augIdeal AK.carrier ∧
      xK ^ p = (fun a => algebraMap R C δ * xK a) ∧ v (algebraMap R C δ) = v x1 ^ (p - 1) ∧
      (∀ f ∈ augIdeal AK.carrier, ∃ r : R,
        f - r • xK ∈ augIdeal AK.carrier * augIdeal AK.carrier) ∧
      HasColen R v AK.carrier (v x1 ^ (p * (p - 1) / 2)) := by
  obtain ⟨x, _, δ, hx, hx0, -, -, -, hxp, hδ, -, haug, -, hcol⟩ :=
    hU3 p C v R hv hp (hopfPull e AK)
  have hxa : x ∈ ReciprocityTheory.PGsh.L2.augIdeal (hopfPull e AK).carrier := by
    simp only [ReciprocityTheory.PGsh.L2.augIdeal, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.proj_apply]
    exact ⟨hx, hx0⟩
  have hxK := (mem_augIdeal_pull e AK x).1 hxa
  refine ⟨(pbE (C := C) (R := R) e).symm x, δ, x 1, hxK, ?_, hδ, ?_, ?_⟩
  · funext k
    have h := congrFun hxp (e.symm k)
    simp only [Pi.pow_apply] at h ⊢
    rw [pbE_symm_apply]
    exact h
  · have key : ∀ F ∈ Submodule.span R {y | ∃ j : ℕ, 1 ≤ j ∧ j < p ∧ y = x ^ j},
        ∃ r : R, (pbE (C := C) (R := R) e).symm F - r • (pbE (C := C) (R := R) e).symm x ∈
          ReciprocityTheory.PGsh.L2.augIdeal AK.carrier * ReciprocityTheory.PGsh.L2.augIdeal AK.carrier := by
      intro F hF
      induction hF using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨j, hj1, -, rfl⟩ := hy
        rcases Nat.lt_or_ge j 2 with hj | hj
        · obtain rfl : j = 1 := by omega
          refine ⟨1, ?_⟩
          rw [pow_one, one_smul, sub_self]
          exact zero_mem _
        · obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
          refine ⟨0, ?_⟩
          rw [zero_smul, sub_zero, pbE_symm_pow, show m + 2 = (m + 1) + 1 from rfl, pow_succ]
          exact Submodule.mul_mem_mul (pow_mem_aug AK hxK m) hxK
      | zero =>
        refine ⟨0, ?_⟩
        rw [map_zero, zero_smul, sub_zero]
        exact zero_mem _
      | add a b _ _ ha hb =>
        obtain ⟨r1, h1⟩ := ha
        obtain ⟨r2, h2⟩ := hb
        refine ⟨r1 + r2, ?_⟩
        convert add_mem h1 h2 using 1
        rw [map_add, add_smul]
        abel
      | smul c a _ ha =>
        obtain ⟨r1, h1⟩ := ha
        refine ⟨c * r1, ?_⟩
        convert Submodule.smul_mem _ c h1 using 1
        rw [map_smul, smul_sub, mul_smul]
    intro f hf
    have hF : pbE (C := C) (R := R) e f ∈
        ReciprocityTheory.PGsh.L2.augIdeal (hopfPull e AK).carrier := by
      rw [mem_augIdeal_pull, LinearEquiv.symm_apply_apply]
      exact hf
    rw [haug] at hF
    obtain ⟨r, hr⟩ := key _ hF
    rw [LinearEquiv.symm_apply_apply] at hr
    exact ⟨r, hr⟩
  · have hc := hasColen_map v e.symm _ _ hcol
    rwa [show (hopfPull e AK).carrier =
        AK.carrier.map (pbE (C := C) (R := R) e : (K → C) →ₗ[R] (ZMod p → C)) from rfl,
      map_pbE_symm] at hc

end ReciprocityTheory.PGsh.Up
