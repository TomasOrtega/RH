import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaUnique
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

variable {K : Type} [Field K] {n d : ℕ}

variable (K n d) in

def tau : Bp K n d := ∏ e, MvPolynomial.X e

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem mon_congr {M : AddSubmonoid (Gam n d)} {g g' : Gam n d} (h : g = g') (hg : g ∈ M) (hg' : g' ∈ M) :
    mon K g hg = mon K g' hg' := by
  subst h; rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mon_zero (M : AddSubmonoid (Gam n d)) : mon K (0 : Gam n d) M.zero_mem = 1 := rfl

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rw [pow_zero]`. Conclude with `((mon_congr (zero_nsmul g) _ M.zero_mem).trans (mon_zero M)).symm`. Consider the case `succ k ih => rw [pow_succ, ih, mon_mul]`. Conclude with `mon_congr (succ_nsmul g k).symm _ _`.
-/
theorem mon_pow {M : AddSubmonoid (Gam n d)} (g : Gam n d) (hg : g ∈ M) (k : ℕ) :
    mon K g hg ^ k = mon K (k • g) (M.nsmul_mem hg k) := by
  induction k with
  | zero => rw [pow_zero]; exact ((mon_congr (zero_nsmul g) _ M.zero_mem).trans (mon_zero M)).symm
  | succ k ih => rw [pow_succ, ih, mon_mul]; exact mon_congr (succ_nsmul g k).symm _ _

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => rw [Finset.prod_empty]`. Conclude with `(mon_zero M).symm`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, ih, mon_mul]`.

Conclude with `mon_congr (Finset.sum_insert ha).symm _ _`.
-/
theorem mon_prod {M : AddSubmonoid (Gam n d)} (s : Finset (E n d)) (f : E n d → Gam n d) (hf : ∀ e, f e ∈ M) :
    ∏ e ∈ s, mon K (f e) (hf e) = mon K (∑ e ∈ s, f e) (M.sum_mem fun e _ => hf e) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty]; exact (mon_zero M).symm
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ih, mon_mul]
    exact mon_congr (Finset.sum_insert ha).symm _ _

/- English proof (translation)
Rewrite using `[map_prod]`. Simplify using `only [map_pow, poly_X, mon_pow]`. Conclude with `mon_prod _ _ _`.
-/
theorem poly_monomial (S : Finset (Fin d)) (k : E n d → ℕ) :
    poly n K S (∏ e, MvPolynomial.X e ^ k e) =
      mon K (∑ e, k e • oneE e) ((cone S).sum_mem fun e _ => (cone S).nsmul_mem (oneE_mem S e) (k e)) := by
  rw [map_prod]
  simp only [map_pow, poly_X, mon_pow]
  exact mon_prod _ _ _

/- English proof (translation)
Use `⟨N • ∑ e, oneE e, (cone S).nsmul_mem ((cone S).sum_mem fun e _ => oneE_mem S e) N, fun e => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, Finset.sum_apply, oneE, Pi.single_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true, nsmul_eq_mul, mul_one]`. Rewrite using `[map_pow, tau, map_prod]`. Simplify using `only [poly_X]`. Rewrite using `[mon_prod, mon_pow]`.
-/
theorem poly_tau_pow (S : Finset (Fin d)) (N : ℕ) :
    ∃ (g : Gam n d) (hg : g ∈ (cone S : AddSubmonoid (Gam n d))), (∀ e, g e = N) ∧
      poly n K S (tau K n d ^ N) = mon K g hg := by
  refine ⟨N • ∑ e, oneE e, (cone S).nsmul_mem ((cone S).sum_mem fun e _ => oneE_mem S e) N, fun e => ?_, ?_⟩
  · simp only [Pi.smul_apply, Finset.sum_apply, oneE, Pi.single_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true, nsmul_eq_mul, mul_one]
  · rw [map_pow, tau, map_prod]
    simp only [poly_X]
    rw [mon_prod, mon_pow]

/- English proof (translation)
Proceed by induction on `y using AddMonoidAlgebra.induction_linear with`. Consider the case `zero => exact ⟨0, 0, by simp⟩`. Consider the case `add f g hf hg`. Take `⟨N₁, b₁, h₁⟩` from `hf`. Take `⟨N₂, b₂, h₂⟩` from `hg`.

Use `⟨N₁ + N₂, tau K n d ^ N₂ * b₁ + tau K n d ^ N₁ * b₂, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_mul, map_mul, ← h₁, ← h₂, pow_add, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `single m c`. Take `⟨g, hg⟩` from `m`.

Set `N : ℕ` to `∑ e, (g e).natAbs`. Establish `hN : ∀ e, 0 ≤ (N : ℤ) + g e` using `fun e => by`. Establish `h1 : (g e).natAbs ≤ N` using `Finset.single_le_sum (f := fun e => (g e).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)`. Use linear arithmetic over natural numbers and integers. Take `⟨g', hg', hc, hp⟩` from `poly_tau_pow (K := K) (n := n) S N`.

Use `⟨N, c • ∏ e, MvPolynomial.X e ^ ((N : ℤ) + g e).toNat, ?_⟩` and prove the remaining obligations. Establish `h1 : (AddMonoidAlgebra.single ⟨g, hg⟩ c : R0 K n d S) = c • mon K g hg`. Simplify using `[mon]`. Rewrite using `[map_smul, poly_monomial, h1, hp, mul_smul_comm, mon_mul]`. Use `congr 1`.

Use `mon_congr ?_ _ _` and prove the remaining obligations. Use function extensionality and compare the values at `e`. Establish `h2 : (∑ e', ((N : ℤ) + g e').toNat • (oneE e' : Gam n d)) e = ((N : ℤ) + g e).toNat`. Simplify using `[oneE, Finset.sum_apply, Pi.single_apply]`. Rewrite using `[h2, Pi.add_apply, hc, Int.toNat_of_nonneg (hN e)]`.
-/
theorem exists_poly (S : Finset (Fin d)) (y : R0 K n d S) :
    ∃ (N : ℕ) (b : Bp K n d), poly n K S (tau K n d ^ N) * y = poly n K S b := by
  induction y using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, 0, by simp⟩
  | add f g hf hg =>
    obtain ⟨N₁, b₁, h₁⟩ := hf
    obtain ⟨N₂, b₂, h₂⟩ := hg
    refine ⟨N₁ + N₂, tau K n d ^ N₂ * b₁ + tau K n d ^ N₁ * b₂, ?_⟩
    rw [map_add, map_mul, map_mul, ← h₁, ← h₂, pow_add, map_mul]
    ring
  | single m c =>
    obtain ⟨g, hg⟩ := m
    let N : ℕ := ∑ e, (g e).natAbs
    have hN : ∀ e, 0 ≤ (N : ℤ) + g e := fun e => by
      have h1 : (g e).natAbs ≤ N := Finset.single_le_sum (f := fun e => (g e).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)
      omega
    obtain ⟨g', hg', hc, hp⟩ := poly_tau_pow (K := K) (n := n) S N
    refine ⟨N, c • ∏ e, MvPolynomial.X e ^ ((N : ℤ) + g e).toNat, ?_⟩
    have h1 : (AddMonoidAlgebra.single ⟨g, hg⟩ c : R0 K n d S) = c • mon K g hg := by
      simp [mon]
    rw [map_smul, poly_monomial, h1, hp, mul_smul_comm, mon_mul]
    congr 1
    refine mon_congr ?_ _ _
    funext e
    have h2 : (∑ e', ((N : ℤ) + g e').toNat • (oneE e' : Gam n d)) e = ((N : ℤ) + g e).toNat := by
      simp [oneE, Finset.sum_apply, Pi.single_apply]
    rw [h2, Pi.add_apply, hc, Int.toNat_of_nonneg (hN e)]

/- English proof (translation)
Introduce `x y hxy`. Establish `hi : Function.Injective (incl (K` using `K) (le_top : (cone T : AddSubmonoid (Gam n d)) ≤ ⊤)) := AddMonoidAlgebra.mapDomain_injective (AddSubmonoid.inclusion_injective _)`. Apply `hi` to reduce the goal to its premises. Take `⟨g, hg, -, hp⟩` from `poly_tau_pow (K := K) (n := n) T N`. Establish `h` using `congrArg (incl (K := K) (le_top : (cone T : AddSubmonoid (Gam n d)) ≤ ⊤)) hxy`.

Simplify using `only [map_mul, hp, incl_mon] at h`. Establish `hu : IsUnit (mon K g (AddSubmonoid.mem_top g) : Lr K n d)`. Use `isUnit_iff_exists_inv.2 ⟨mon K (-g) (AddSubmonoid.mem_top _), ?_⟩` and prove the remaining obligations. Rewrite using `[mon_mul]`. Conclude with `(mon_congr (add_neg_cancel g) _ _).trans (mon_zero _)`.

Conclude with `hu.mul_left_cancel h`.
-/
theorem mul_injective (T : Finset (Fin d)) (N : ℕ) :
    Function.Injective fun x : R0 K n d T => poly n K T (tau K n d ^ N) * x := by
  intro x y hxy
  have hi : Function.Injective (incl (K := K) (le_top : (cone T : AddSubmonoid (Gam n d)) ≤ ⊤)) :=
    AddMonoidAlgebra.mapDomain_injective (AddSubmonoid.inclusion_injective _)
  apply hi
  obtain ⟨g, hg, -, hp⟩ := poly_tau_pow (K := K) (n := n) T N
  have h := congrArg (incl (K := K) (le_top : (cone T : AddSubmonoid (Gam n d)) ≤ ⊤)) hxy
  simp only [map_mul, hp, incl_mon] at h
  have hu : IsUnit (mon K g (AddSubmonoid.mem_top g) : Lr K n d) := by
    refine isUnit_iff_exists_inv.2 ⟨mon K (-g) (AddSubmonoid.mem_top _), ?_⟩
    rw [mon_mul]
    exact (mon_congr (add_neg_cancel g) _ _).trans (mon_zero _)
  exact hu.mul_left_cancel h

variable {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d)

/- English proof (translation)
Use `haveI := etale_Aa C`. Use `haveI : Module.Flat (Bp K n d) (Aa C) := Algebra.Smooth.flat _ _`. Set `f : R0 K n d T →ₗ[Bp K n d] R0 K n d T` to `LinearMap.mulLeft (Bp K n d) (poly n K T (tau K n d ^ N))`. Establish `hf : Function.Injective f` using `mul_injective T N`. Establish `hl` using `Module.Flat.lTensor_preserves_injective_linearMap (M := Aa C) f hf`.

Set `v : Rb C T` to `toR C T (phi C (tau K n d ^ N))`. Establish `key : ∀ w : TensorProduct (Bp K n d) (Aa C) (R0 K n d T), hb.equiv (f.lTensor (Aa C) w) = v * hb.equiv w`. Introduce `w`. Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `add u u' hu hu' => simp only [map_add, hu, hu', mul_add]`. Consider the case `tmul a x`. Rewrite using `[LinearMap.lTensor_tmul, IsBaseChange.equiv_tmul, IsBaseChange.equiv_tmul]`. Express the relevant statement in the definitionally equal form `toR C T a * θ' (poly n K T (tau K n d ^ N) * x) = toR C T (phi C (tau K n d ^ N)) * (toR C T a * θ' x)`. Rewrite using `[map_mul, hθ']`.

Expand and normalize the polynomial expressions, which then agree. Establish `main : ∀ z' : Rb C T, v * z' = 0 → z' = 0`. Introduce `z' hz'`. Establish `hw : f.lTensor (Aa C) (hb.equiv.symm z') = 0`. Apply `hb.equiv.injective` to reduce the goal to its premises.

Rewrite using `[map_zero, key, LinearEquiv.apply_symm_apply]`. Conclude with `hz'`. Establish `h3` using `hl (hw.trans (map_zero _).symm)`. Conclude with `hb.equiv.symm.map_eq_zero_iff.1 h3`. Conclude with `main z hz`.
-/
theorem eq_zero_of_mul {T : Finset (Fin d)} (θ' : R0 K n d T →ₐ[K] C.R T)
    (hθ' : ∀ b, θ' (poly n K T b) = toR C T (phi C b)) (hb : IsBaseChange (Aa C) (thetaLin C θ' hθ'))
    (N : ℕ) (z : C.R T) (hz : toR C T (phi C (tau K n d ^ N)) * z = 0) : z = 0 := by
  haveI := etale_Aa C
  haveI : Module.Flat (Bp K n d) (Aa C) := Algebra.Smooth.flat _ _
  let f : R0 K n d T →ₗ[Bp K n d] R0 K n d T := LinearMap.mulLeft (Bp K n d) (poly n K T (tau K n d ^ N))
  have hf : Function.Injective f := mul_injective T N
  have hl := Module.Flat.lTensor_preserves_injective_linearMap (M := Aa C) f hf
  let v : Rb C T := toR C T (phi C (tau K n d ^ N))
  have key : ∀ w : TensorProduct (Bp K n d) (Aa C) (R0 K n d T),
      hb.equiv (f.lTensor (Aa C) w) = v * hb.equiv w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add u u' hu hu' => simp only [map_add, hu, hu', mul_add]
    | tmul a x =>
      rw [LinearMap.lTensor_tmul, IsBaseChange.equiv_tmul, IsBaseChange.equiv_tmul]
      change toR C T a * θ' (poly n K T (tau K n d ^ N) * x) = toR C T (phi C (tau K n d ^ N)) * (toR C T a * θ' x)
      rw [map_mul, hθ']
      ring
  have main : ∀ z' : Rb C T, v * z' = 0 → z' = 0 := by
    intro z' hz'
    have hw : f.lTensor (Aa C) (hb.equiv.symm z') = 0 := by
      apply hb.equiv.injective
      rw [map_zero, key, LinearEquiv.apply_symm_apply]
      exact hz'
    have h3 := hl (hw.trans (map_zero _).symm)
    exact hb.equiv.symm.map_eq_zero_iff.1 h3
  exact main z hz

/- English proof (translation)
Use `AlgHom.ext fun y => ?_` and prove the remaining obligations. Take `⟨N, b, h⟩` from `exists_poly S y`. Establish `e₁` using `congrArg θ₁ h`. Establish `e₂` using `congrArg θ₂ h`. Rewrite `e₁` using `[map_mul, h₁, h₁]`.

Rewrite `e₂` using `[map_mul, h₂, h₂]`. Use `sub_eq_zero.1 (eq_zero_of_mul C θ' hθ' hb N _ ?_)` and prove the remaining obligations. Rewrite using `[mul_sub, e₁, e₂, sub_self]`.
-/
theorem theta_unique {S T : Finset (Fin d)} (θ₁ θ₂ : R0 K n d S →ₐ[K] C.R T)
    (h₁ : ∀ b, θ₁ (poly n K S b) = toR C T (phi C b)) (h₂ : ∀ b, θ₂ (poly n K S b) = toR C T (phi C b))
    (θ' : R0 K n d T →ₐ[K] C.R T) (hθ' : ∀ b, θ' (poly n K T b) = toR C T (phi C b))
    (hb : IsBaseChange (Aa C) (thetaLin C θ' hθ')) : θ₁ = θ₂ := by
  refine AlgHom.ext fun y => ?_
  obtain ⟨N, b, h⟩ := exists_poly S y
  have e₁ := congrArg θ₁ h
  have e₂ := congrArg θ₂ h
  rw [map_mul, h₁, h₁] at e₁
  rw [map_mul, h₂, h₂] at e₂
  refine sub_eq_zero.1 (eq_zero_of_mul C θ' hθ' hb N _ ?_)
  rw [mul_sub, e₁, e₂, sub_self]

end GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaUnique
