import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleRingFreeOverFrobeniusImageStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.PsiOp

def Tw {R : Type} [CommRing R] (_φ : R →+* R) : Type := R

instance {R : Type} [CommRing R] (φ : R →+* R) : CommRing (Tw φ) := inferInstanceAs (CommRing R)

instance {R : Type} [CommRing R] (φ : R →+* R) : Algebra R (Tw φ) :=
  @RingHom.toAlgebra R (Tw φ) _ _ φ

variable {R : Type} [CommRing R] (φ : R →+* R) (u : R) (l : ℕ)

def expL : (Fin l → R) →ₗ[R] Tw φ where
  toFun c := (∑ j : Fin l, u ^ (j : ℕ) * φ (c j) : R)
  map_add' c d := by
    show (∑ j : Fin l, u ^ (j : ℕ) * φ (c j + d j) : R) = (∑ j : Fin l, u ^ (j : ℕ) * φ (c j) : R) + ∑ j : Fin l, u ^ (j : ℕ) * φ (d j)
    rw [← Finset.sum_add_distrib]; simp [mul_add]
  map_smul' a c := by
    show (∑ j : Fin l, u ^ (j : ℕ) * φ (a * c j) : R) = φ a * ∑ j : Fin l, u ^ (j : ℕ) * φ (c j)
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]; ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem expL_apply (c : Fin l → R) : (expL φ u l c : R) = ∑ j : Fin l, u ^ (j : ℕ) * φ (c j) := rfl

section Main

variable {φ u l}

/- English proof (translation)
Rewrite using `[Function.bijective_iff_existsUnique]`. Introduce `x`. Take `⟨c, hc, hu⟩` from `hex x`. Conclude with `⟨c, hc.symm, fun d hd => hu d hd.symm⟩`.
-/
theorem expL_bij (hex : ∀ x : R, ∃! c : Fin l → R, x = ∑ j : Fin l, u ^ (j : ℕ) * φ (c j)) :
    Function.Bijective (expL φ u l) := by
  rw [Function.bijective_iff_existsUnique]
  intro x
  obtain ⟨c, hc, hu⟩ := hex x
  exact ⟨c, hc.symm, fun d hd => hu d hd.symm⟩

def bas (hex : ∀ x : R, ∃! c : Fin l → R, x = ∑ j : Fin l, u ^ (j : ℕ) * φ (c j)) :
    Module.Basis (Fin l) R (Tw φ) :=
  Module.Basis.ofEquivFun (LinearEquiv.ofBijective _ (expL_bij hex)).symm

variable (hex : ∀ x : R, ∃! c : Fin l → R, x = ∑ j : Fin l, u ^ (j : ℕ) * φ (c j))

/- English proof (translation)
Rewrite using `[bas, Module.Basis.ofEquivFun_repr_apply, LinearEquiv.ofBijective_symm_apply_apply]`.
-/
theorem repr_expL (c : Fin l → R) (i : Fin l) : (bas hex).repr (expL φ u l c) i = c i := by
  rw [bas, Module.Basis.ofEquivFun_repr_apply, LinearEquiv.ofBijective_symm_apply_apply]

/- English proof (translation)
Establish `h` using `(LinearEquiv.ofBijective (expL φ u l) (expL_bij hex)).apply_symm_apply x`. Rewrite `h` using `[LinearEquiv.ofBijective_apply]`. Use `h using 2` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Rewrite using `[bas, Module.Basis.ofEquivFun_repr_apply]`.
-/
theorem expL_repr (x : Tw φ) : expL φ u l ((bas hex).repr x) = x := by
  have h := (LinearEquiv.ofBijective (expL φ u l) (expL_bij hex)).apply_symm_apply x
  rw [LinearEquiv.ofBijective_apply] at h
  convert h using 2
  funext i
  rw [bas, Module.Basis.ofEquivFun_repr_apply]

/- English proof (translation)
Rewrite using `[bas, Module.Basis.coe_ofEquivFun, LinearEquiv.symm_symm]`. Express the relevant statement in the definitionally equal form `(∑ j : Fin l, u ^ (j : ℕ) * φ ((Pi.single i (1 : R) : Fin l → R) j) : R) = u ^ (i : ℕ)`. Rewrite using `[Finset.sum_eq_single i]`. Simplify using the standard rewrite rules. Introduce `j _ hj`.

Simplify using `[Pi.single_apply, hj]`. Simplify using the standard rewrite rules.
-/
theorem bas_apply (i : Fin l) : (bas hex i : R) = u ^ (i : ℕ) := by
  rw [bas, Module.Basis.coe_ofEquivFun, LinearEquiv.symm_symm]
  change (∑ j : Fin l, u ^ (j : ℕ) * φ ((Pi.single i (1 : R) : Fin l → R) j) : R) = u ^ (i : ℕ)
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_apply, hj]
  · simp

end Main

section Main2

variable {φ u l}
variable (hex : ∀ x : R, ∃! c : Fin l → R, x = ∑ j : Fin l, u ^ (j : ℕ) * φ (c j))

/- English proof (translation)
Use `set d : Fin l → R := fun k => (bas hex).repr y k with hd`. Establish `hy : (y : R) = ∑ k : Fin l, u ^ (k : ℕ) * φ (d k)`. Use `expL_repr hex y` as an intermediate fact. Rewrite `this` using `[expL_apply]`. Conclude with `this.symm`.

Establish `key : (y * bas hex i : Tw φ) = expL φ u l (fun m => (if (i : ℕ) ≤ m then 1 else u) * d (m - i))`. Establish `key' : ∀ Y : R, Y = ∑ k : Fin l, u ^ (k : ℕ) * φ (d k) → Y * u ^ (i : ℕ) = ∑ m : Fin l, u ^ (m : ℕ) * φ ((if (i : ℕ) ≤ m then 1 else u) * d (m - i))`. Introduce `Y hY`. Rewrite using `[hY, Finset.sum_mul]`. Use `Fintype.sum_equiv (Equiv.addRight i) _ _ (fun k => ?_)` and prove the remaining obligations.

Generalize the expression as in `hm : Equiv.addRight i k = m`. Establish `hmk : m - i = k` using `by rw [← hm]; exact add_sub_cancel_right k i`. Establish `hmv : (m : ℕ) = ((k : ℕ) + i) % l` using `by rw [← hm]; exact Fin.val_add k i`. Establish `hk` using `k.2`. Establish `hi` using `i.2`.

Establish `hcase : ((k : ℕ) + i < l ∧ (m : ℕ) = k + i) ∨ (l ≤ (k : ℕ) + i ∧ (m : ℕ) = k + i - l)`. Break down `lt_or_ge ((k : ℕ) + i) l with h | h` into its components or cases. Conclude with `Or.inl ⟨h, by rw [hmv, Nat.mod_eq_of_lt h]⟩`. Conclude with `Or.inr ⟨h, by rw [hmv, Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]⟩`. Rewrite using `[hmk]`.

Use `split_ifs with hle`. Apply the tactic sequence `have hmv2 : (m : ℕ) = k + i := by rcases hcase with ⟨_, h⟩ | ⟨_, h⟩ <;> omega`. Rewrite using `[hmv2, one_mul, pow_add]`. Expand and normalize the polynomial expressions, which then agree. Apply the tactic sequence `have hmv2 : (m : ℕ) = k + i - l := by rcases hcase with ⟨_, h⟩ | ⟨_, h⟩ <;> omega`.

Apply the tactic sequence `have hl2 : l ≤ (k : ℕ) + i := by rcases hcase with ⟨_, h⟩ | ⟨h, _⟩ <;> omega`. Rewrite using `[hmv2, map_mul, ← hu]`. Establish `e : u ^ (k : ℕ) * u ^ (i : ℕ) = u ^ ((k : ℕ) + i - l) * u ^ l`. Rewrite using `[← pow_add, ← pow_add]`. Use `congr 1`.

Use linear arithmetic over natural numbers and integers. Take the linear combination `(φ (d k)) * e`. Rewrite using `[bas_apply]`. Conclude with `key' y hy`. Rewrite using `[key, repr_expL]`.

Simplify using `[hd]`.
-/
theorem repr_mul_pow [NeZero l] (hu : u ^ l = φ u) (y : Tw φ) (i : Fin l) :
    (bas hex).repr (y * bas hex i) i = (bas hex).repr y 0 := by
  set d : Fin l → R := fun k => (bas hex).repr y k with hd
  have hy : (y : R) = ∑ k : Fin l, u ^ (k : ℕ) * φ (d k) := by
    have := expL_repr hex y; rw [expL_apply] at this; exact this.symm
  have key : (y * bas hex i : Tw φ) = expL φ u l (fun m => (if (i : ℕ) ≤ m then 1 else u) * d (m - i)) := by
    have key' : ∀ Y : R, Y = ∑ k : Fin l, u ^ (k : ℕ) * φ (d k) →
        Y * u ^ (i : ℕ) = ∑ m : Fin l, u ^ (m : ℕ) * φ ((if (i : ℕ) ≤ m then 1 else u) * d (m - i)) := by
      intro Y hY
      rw [hY, Finset.sum_mul]
      refine Fintype.sum_equiv (Equiv.addRight i) _ _ (fun k => ?_)
      generalize hm : Equiv.addRight i k = m
      have hmk : m - i = k := by rw [← hm]; exact add_sub_cancel_right k i
      have hmv : (m : ℕ) = ((k : ℕ) + i) % l := by rw [← hm]; exact Fin.val_add k i
      have hk := k.2
      have hi := i.2
      have hcase : ((k : ℕ) + i < l ∧ (m : ℕ) = k + i) ∨ (l ≤ (k : ℕ) + i ∧ (m : ℕ) = k + i - l) := by
        rcases lt_or_ge ((k : ℕ) + i) l with h | h
        · exact Or.inl ⟨h, by rw [hmv, Nat.mod_eq_of_lt h]⟩
        · exact Or.inr ⟨h, by rw [hmv, Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]⟩
      rw [hmk]
      split_ifs with hle
      · have hmv2 : (m : ℕ) = k + i := by rcases hcase with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
        rw [hmv2, one_mul, pow_add]; ring
      · have hmv2 : (m : ℕ) = k + i - l := by rcases hcase with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
        have hl2 : l ≤ (k : ℕ) + i := by rcases hcase with ⟨_, h⟩ | ⟨h, _⟩ <;> omega
        rw [hmv2, map_mul, ← hu]
        have e : u ^ (k : ℕ) * u ^ (i : ℕ) = u ^ ((k : ℕ) + i - l) * u ^ l := by
          rw [← pow_add, ← pow_add]; congr 1; omega
        linear_combination (φ (d k)) * e
    rw [bas_apply]
    exact key' y hy
  rw [key, repr_expL]
  simp [hd]

/- English proof (translation)
Rewrite using `[Algebra.trace_eq_matrix_trace (bas hex), Matrix.trace]`. Simplify using `only [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, repr_mul_pow hex hu]`. Simplify using the standard rewrite rules.
-/
theorem trace_eq [NeZero l] (hu : u ^ l = φ u) (y : Tw φ) :
    Algebra.trace R (Tw φ) y = (l : R) * (bas hex).repr y 0 := by
  classical
  rw [Algebra.trace_eq_matrix_trace (bas hex), Matrix.trace]
  simp only [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, repr_mul_pow hex hu]
  simp

end Main2

section Main3

variable {φ u l}

/- English proof (translation)
Establish `hφγi : ∀ a, φ (γi a) = γi (φ a)` using `fun a => by`. Rewrite using `[← h2 (φ (γi a)), ← hφγ, h1]`. Introduce `x`. Take `⟨c, hc, hu⟩` from `hex (γi x)`. Use `⟨fun j => γ (c j), ?_, ?_⟩` and prove the remaining obligations.

Use `congrArg γ hc` as an intermediate fact. Rewrite `this` using `[h1]`. Rewrite using `[this, map_sum]`. Simplify using `[map_mul, map_pow, hφγ]`. Introduce `d hd`.

Establish `: c = fun j => γi (d j)` using `(hu _ (by rw [hd, map_sum]; simp [map_mul, map_pow, h2, hφγi])).symm`. Use function extensionality and compare the values at `j`. Rewrite using `[this, h1]`.
-/
theorem hex_gam (γ γi : R →+* R) (h1 : ∀ a, γ (γi a) = a) (h2 : ∀ a, γi (γ a) = a)
    (hφγ : ∀ a, φ (γ a) = γ (φ a))
    (hex : ∀ x : R, ∃! c : Fin l → R, x = ∑ j : Fin l, u ^ (j : ℕ) * φ (c j)) :
    ∀ x : R, ∃! c : Fin l → R, x = ∑ j : Fin l, γ u ^ (j : ℕ) * φ (c j) := by
  have hφγi : ∀ a, φ (γi a) = γi (φ a) := fun a => by
    rw [← h2 (φ (γi a)), ← hφγ, h1]
  intro x
  obtain ⟨c, hc, hu⟩ := hex (γi x)
  refine ⟨fun j => γ (c j), ?_, ?_⟩
  · have := congrArg γ hc
    rw [h1] at this
    rw [this, map_sum]
    simp [map_mul, map_pow, hφγ]
  · intro d hd
    have : c = fun j => γi (d j) :=
      (hu _ (by rw [hd, map_sum]; simp [map_mul, map_pow, h2, hφγi])).symm
    funext j
    rw [this, h1]

/- English proof (translation)
Establish `hz` using `expL_repr hex z`. Establish `key : (γ z : R) = ∑ j : Fin l, γ u ^ (j : ℕ) * φ (γ ((bas hex).repr z j))` using `by conv_lhs => rw [← hz]`. Rewrite using `[expL_apply, map_sum]`. Simplify using `[map_mul, map_pow, hφγ]`. Establish `key2 : (γ z : R) = expL φ (γ u) l (fun j => γ ((bas hex).repr z j))` using `key`.

Rewrite using `[key2, repr_expL]`.
-/
theorem repr_gam (γ γi : R →+* R) (h1 : ∀ a, γ (γi a) = a) (h2 : ∀ a, γi (γ a) = a)
    (hφγ : ∀ a, φ (γ a) = γ (φ a))
    (hex : ∀ x : R, ∃! c : Fin l → R, x = ∑ j : Fin l, u ^ (j : ℕ) * φ (c j)) (z : Tw φ) (i : Fin l) :
    (bas (hex_gam γ γi h1 h2 hφγ hex)).repr (γ z) i = γ ((bas hex).repr z i) := by
  have hz := expL_repr hex z
  have key : (γ z : R) = ∑ j : Fin l, γ u ^ (j : ℕ) * φ (γ ((bas hex).repr z j)) := by
    conv_lhs => rw [← hz]
    rw [expL_apply, map_sum]
    simp [map_mul, map_pow, hφγ]
  have key2 : (γ z : R) = expL φ (γ u) l (fun j => γ ((bas hex).repr z j)) := key
  rw [key2, repr_expL]

/- English proof (translation)
Establish `hu' : γ u ^ l = φ (γ u)` using `by rw [← map_pow, hu, hφγ]`. Establish `t1` using `trace_eq hex hu (γ x)`. Establish `t2` using `trace_eq (hex_gam γ γi h1 h2 hφγ hex) hu' (γ x)`. Establish `t3 : (Algebra.trace R (Tw φ)) (γ x) = (l : R) * γ ((bas hex).repr x 0)` using `t2.trans (congrArg _ (repr_gam γ γi h1 h2 hφγ hex x 0))`. Rewrite using `[← sub_eq_zero]`.

Apply `htf` to reduce the goal to its premises. Rewrite using `[mul_sub, ← t1, ← t3, sub_self]`.
-/
theorem coef_gam [NeZero l] (hu : u ^ l = φ u) (γ γi : R →+* R) (h1 : ∀ a, γ (γi a) = a)
    (h2 : ∀ a, γi (γ a) = a) (hφγ : ∀ a, φ (γ a) = γ (φ a))
    (htf : ∀ x : R, (l : R) * x = 0 → x = 0)
    (hex : ∀ x : R, ∃! c : Fin l → R, x = ∑ j : Fin l, u ^ (j : ℕ) * φ (c j)) (x : R) :
    (bas hex).repr (γ x) 0 = γ ((bas hex).repr x 0) := by
  have hu' : γ u ^ l = φ (γ u) := by rw [← map_pow, hu, hφγ]
  have t1 := trace_eq hex hu (γ x)
  have t2 := trace_eq (hex_gam γ γi h1 h2 hφγ hex) hu' (γ x)
  have t3 : (Algebra.trace R (Tw φ)) (γ x) = (l : R) * γ ((bas hex).repr x 0) :=
    t2.trans (congrArg _ (repr_gam γ γi h1 h2 hφγ hex x 0))
  rw [← sub_eq_zero]
  apply htf
  rw [mul_sub, ← t1, ← t3, sub_self]

end Main3

section Psi

variable {φ u l}
variable (hex : ∀ x : R, ∃! c : Fin l → R, x = ∑ j : Fin l, u ^ (j : ℕ) * φ (c j))

def psi [NeZero l] (x : R) : R := (bas hex).repr x 0

/- English proof (translation)
The claim follows from `congrArg (fun f => f 0) ((bas hex).repr.map_add x y)`.
-/
theorem psi_add [NeZero l] (x y : R) : psi hex (x + y) = psi hex x + psi hex y :=
  congrArg (fun f => f 0) ((bas hex).repr.map_add x y)

/- English proof (translation)
The claim follows from `congrArg (fun f => f 0) ((bas hex).repr.map_smul a x)`.
-/
theorem psi_φmul [NeZero l] (a x : R) : psi hex (φ a * x) = a * psi hex x :=
  congrArg (fun f => f 0) ((bas hex).repr.map_smul a x)

/- English proof (translation)
Establish `e1 : (u ^ j * φ a : R) = expL φ u l (Pi.single (⟨j, hj⟩ : Fin l) a)`. Rewrite using `[expL_apply, Finset.sum_eq_single (⟨j, hj⟩ : Fin l)]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Pi.single_apply, hb]`.

Simplify using the standard rewrite rules. Unfold `psi`. Rewrite using `[e1, repr_expL]`. Distinguish the cases in `hj0 : j = 0`. Substitute `hj0` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, Fin.ext_iff, hj0, Ne.symm hj0]`.
-/
theorem psi_single [NeZero l] (j : ℕ) (hj : j < l) (a : R) :
    psi hex (u ^ j * φ a) = if j = 0 then a else 0 := by
  have e1 : (u ^ j * φ a : R) = expL φ u l (Pi.single (⟨j, hj⟩ : Fin l) a) := by
    rw [expL_apply, Finset.sum_eq_single (⟨j, hj⟩ : Fin l)]
    · simp
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  unfold psi
  rw [e1, repr_expL]
  by_cases hj0 : j = 0
  · subst hj0; simp
  · simp [Pi.single_apply, Fin.ext_iff, hj0, Ne.symm hj0]

/- English proof (translation)
The claim follows from `coef_gam hu γ γi h1 h2 hφγ htf hex x`.
-/
theorem psi_gam [NeZero l] (hu : u ^ l = φ u) (γ γi : R →+* R) (h1 : ∀ a, γ (γi a) = a)
    (h2 : ∀ a, γi (γ a) = a) (hφγ : ∀ a, φ (γ a) = γ (φ a))
    (htf : ∀ x : R, (l : R) * x = 0 → x = 0) (x : R) : psi hex (γ x) = γ (psi hex x) :=
  coef_gam hu γ γi h1 h2 hφγ htf hex x

end Psi

end GlobalTheory.PsiOp

namespace GlobalTheory.PsiOp

open Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

/- English proof (translation)
Establish `hH : IsHausdorff (Ideal.span {((PD.p : ℕ) : W.EE)}) W.EE` using `W.EE_complete.toIsHausdorff`. Use `hH.haus x fun k => ?_` and prove the remaining obligations. Take `⟨e, he⟩` from `hx k`. Rewrite using `[SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Conclude with `⟨e, he⟩`.
-/
theorem eq_zero_of_mem_pow (x : W.EE) (hx : ∀ k : ℕ, ∃ e : W.EE, x = ((PD.p : ℕ) : W.EE) ^ k * e) : x = 0 := by
  have hH : IsHausdorff (Ideal.span {((PD.p : ℕ) : W.EE)}) W.EE := W.EE_complete.toIsHausdorff
  refine hH.haus x fun k => ?_
  obtain ⟨e, he⟩ := hx k
  rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  exact ⟨e, he⟩

/- English proof (translation)
Rewrite using `[map_pow]`. Conclude with `W.EE_π.pow m`.
-/
theorem isUnit_πpow (m : ℕ) : IsUnit (algebraMap (LetA O n) W.EE (letπ ^ m)) := by
  rw [map_pow]; exact W.EE_π.pow m

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[← sub_eq_zero]`. Use `eq_zero_of_mem_pow W _ fun k => ?_` and prove the remaining obligations. Take `⟨a, m, hm⟩` from `W.EE_dense x k`. Take `⟨e, he⟩` from `Ideal.mem_span_singleton.1 hm`.

Take `⟨w, hw⟩` from `(isUnit_πpow W m).map f`. Establish `hgt : g (algebraMap (LetA O n) W.EE (letπ ^ m)) = f (algebraMap (LetA O n) W.EE (letπ ^ m))` using `(h _).symm`. Use `set t := algebraMap (LetA O n) W.EE (letπ ^ m) with ht`. Establish `hf` using `congrArg f he`. Establish `hg` using `congrArg g he`.

Simplify using `only [map_mul, map_sub, map_pow, map_natCast] at hf hg`. Rewrite `hf` using `[h a]`. Rewrite `hg` using `[hgt]`. Rewrite `hf`, `hg` using `[← hw]`. Use `⟨(f e - g e) * ↑w⁻¹, ?_⟩` and prove the remaining obligations.

Establish `hw' : (w : W.EE) * ↑w⁻¹ = 1` using `w.mul_inv`. Take the linear combination `(↑w⁻¹ : W.EE) * (hf - hg) - (f x - g x) * hw'`.
-/
theorem hom_ext (f g : W.EE →+* W.EE) (h : ∀ a, f (algebraMap (LetA O n) W.EE a) = g (algebraMap (LetA O n) W.EE a)) :
    f = g := by
  ext x
  rw [← sub_eq_zero]
  refine eq_zero_of_mem_pow W _ fun k => ?_
  obtain ⟨a, m, hm⟩ := W.EE_dense x k
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton.1 hm
  obtain ⟨w, hw⟩ := (isUnit_πpow W m).map f
  have hgt : g (algebraMap (LetA O n) W.EE (letπ ^ m)) = f (algebraMap (LetA O n) W.EE (letπ ^ m)) :=
    (h _).symm
  set t := algebraMap (LetA O n) W.EE (letπ ^ m) with ht
  have hf := congrArg f he
  have hg := congrArg g he
  simp only [map_mul, map_sub, map_pow, map_natCast] at hf hg
  rw [h a] at hf
  rw [hgt] at hg
  rw [← hw] at hf hg
  refine ⟨(f e - g e) * ↑w⁻¹, ?_⟩
  have hw' : (w : W.EE) * ↑w⁻¹ = 1 := w.mul_inv
  linear_combination (↑w⁻¹ : W.EE) * (hf - hg) - (f x - g x) * hw'

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[letφ, letγ, W.γ₀_comm]`.
-/
theorem letφ_letγ (g : W.Gam) (a : LetA O n) :
    letφ W.φ₀ (letγ (W.γ₀ g) a) = letγ (W.γ₀ g) (letφ W.φ₀ a) := by
  funext i
  simp [letφ, letγ, W.γ₀_comm]

/- English proof (translation)
Use `hom_ext W ((W.φE : W.EE →+* W.EE).comp (W.γE g : W.EE →+* W.EE)) ((W.γE g : W.EE →+* W.EE).comp (W.φE : W.EE →+* W.EE)) (fun a => by` as an intermediate fact. Simplify using `only [RingHom.comp_apply, RingHom.coe_coe]`. Rewrite using `[W.γE_ext, W.φE_ext, W.φE_ext, W.γE_ext, letφ_letγ])`. Conclude with `RingHom.congr_fun this x`.
-/
theorem φE_γE (g : W.Gam) (x : W.EE) : W.φE (W.γE g x) = W.γE g (W.φE x) := by
  have := hom_ext W ((W.φE : W.EE →+* W.EE).comp (W.γE g : W.EE →+* W.EE))
    ((W.γE g : W.EE →+* W.EE).comp (W.φE : W.EE →+* W.EE)) (fun a => by
      simp only [RingHom.comp_apply, RingHom.coe_coe]
      rw [W.γE_ext, W.φE_ext, W.φE_ext, W.γE_ext, letφ_letγ])
  exact RingHom.congr_fun this x

/- English proof (translation)
Use `eq_zero_of_mem_pow W x fun k => ?_` and prove the remaining obligations. Take `⟨a, m, hm⟩` from `W.EE_dense x k`. Take `⟨e, he⟩` from `Ideal.mem_span_singleton.1 hm`. Establish `h1 : algebraMap (LetA O n) W.EE (((PD.p : ℕ) : LetA O n) * a) ∈ Ideal.span {((PD.p : ℕ) : W.EE) ^ (k + 1)}`. Rewrite using `[Ideal.mem_span_singleton]`.

Use `⟨-e, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_natCast]`. Take the linear combination `(algebraMap (LetA O n) W.EE (letπ ^ m)) * hx - ((PD.p : ℕ) : W.EE) * he`. Take `⟨b, hb⟩` from `W.EE_sat _ _ h1`. Establish `hab : a = ((PD.p : ℕ) : LetA O n) ^ k * b`.

Establish `h2 : ((PD.p : ℕ) : LetA O n) * (a - ((PD.p : ℕ) : LetA O n) ^ k * b) = 0`. Rewrite using `[mul_sub, hb]`. Expand and normalize the polynomial expressions, which then agree. Use function extensionality and compare the values at `i`. Establish `hi : ((PD.p : ℕ) : PowerSeries O) * (a i - ((PD.p : ℕ) : PowerSeries O) ^ k * b i) = 0`.

Simplify using `using congrFun h2 i`. Use `hO _ hi` as an intermediate fact. Rewrite `this` using `[sub_eq_zero]`. Simplify using `using this`. Take `⟨w, hw⟩` from `isUnit_πpow W m`.

Use `⟨(algebraMap (LetA O n) W.EE b + e) * ↑w⁻¹, ?_⟩` and prove the remaining obligations. Establish `hw' : (w : W.EE) * ↑w⁻¹ = 1` using `w.mul_inv`. Rewrite `he` using `[← hw, hab, map_mul, map_pow, map_natCast]`. Take the linear combination `(↑w⁻¹ : W.EE) * he - x * hw'`.
-/
theorem tf (hO : ∀ c : PowerSeries O, ((PD.p : ℕ) : PowerSeries O) * c = 0 → c = 0)
    (x : W.EE) (hx : ((PD.p : ℕ) : W.EE) * x = 0) : x = 0 := by
  refine eq_zero_of_mem_pow W x fun k => ?_
  obtain ⟨a, m, hm⟩ := W.EE_dense x k
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton.1 hm
  have h1 : algebraMap (LetA O n) W.EE (((PD.p : ℕ) : LetA O n) * a) ∈
      Ideal.span {((PD.p : ℕ) : W.EE) ^ (k + 1)} := by
    rw [Ideal.mem_span_singleton]
    refine ⟨-e, ?_⟩
    rw [map_mul, map_natCast]
    linear_combination (algebraMap (LetA O n) W.EE (letπ ^ m)) * hx - ((PD.p : ℕ) : W.EE) * he
  obtain ⟨b, hb⟩ := W.EE_sat _ _ h1
  have hab : a = ((PD.p : ℕ) : LetA O n) ^ k * b := by
    have h2 : ((PD.p : ℕ) : LetA O n) * (a - ((PD.p : ℕ) : LetA O n) ^ k * b) = 0 := by
      rw [mul_sub, hb]; ring
    funext i
    have hi : ((PD.p : ℕ) : PowerSeries O) * (a i - ((PD.p : ℕ) : PowerSeries O) ^ k * b i) = 0 := by
      simpa using congrFun h2 i
    have := hO _ hi
    rw [sub_eq_zero] at this
    simpa using this
  obtain ⟨w, hw⟩ := isUnit_πpow W m
  refine ⟨(algebraMap (LetA O n) W.EE b + e) * ↑w⁻¹, ?_⟩
  have hw' : (w : W.EE) * ↑w⁻¹ = 1 := w.mul_inv
  rw [← hw, hab, map_mul, map_pow, map_natCast] at he
  linear_combination (↑w⁻¹ : W.EE) * he - x * hw'

/- English proof (translation)
Rewrite using `[W.φE_ext, ← map_pow]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `[letφ, letπ, W.φ₀_X, W.q₀_def, hp]`.
-/
theorem φE_u {l : ℕ} (hp : PD.p = l) :
    W.φE (algebraMap (LetA O n) W.EE (1 + letπ)) = (algebraMap (LetA O n) W.EE (1 + letπ)) ^ l := by
  rw [W.φE_ext, ← map_pow]
  congr 1
  funext i
  simp [letφ, letπ, W.φ₀_X, W.q₀_def, hp]

/- English proof (translation)
Establish `hu : (algebraMap (LetA O n) W.EE (1 + letπ)) ^ l = (W.φE : W.EE →+* W.EE) (algebraMap (LetA O n) W.EE (1 + letπ))` using `(φE_u W hp).symm`. Establish `htf : ∀ x : W.EE, (l : W.EE) * x = 0 → x = 0`. Introduce `x hx`. Use `tf W hO x ?_` and prove the remaining obligations. Rewrite using `[hp]`.

Conclude with `hx`. Use `⟨{ toFun := psi hex, map_add' := psi_add hex, map_smul' := fun o x => ?_ }, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [RingHom.id_apply, Algebra.smul_def]`. Use `psi_φmul hex (algebraMap O W.EE o) x` as an intermediate fact. Rewrite `this` using `[show (W.φE : W.EE →+* W.EE) (algebraMap O W.EE o) = algebraMap O W.EE o from W.φE.commutes o]`. Then use the resulting hypothesis.

Conclude with `fun a x => psi_φmul hex a x`. Introduce `g x`. Establish `h1 : ∀ a, W.γE g (W.γE g⁻¹ a) = a` using `fun a => by`. Rewrite using `[← AlgHom.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgHom.one_apply]`. Establish `h2 : ∀ a, W.γE g⁻¹ (W.γE g a) = a` using `fun a => by`.

Rewrite using `[← AlgHom.mul_apply, ← map_mul, inv_mul_cancel, map_one, AlgHom.one_apply]`. Conclude with `psi_gam hex hu (W.γE g : W.EE →+* W.EE) (W.γE g⁻¹ : W.EE →+* W.EE) h1 h2 (fun a => φE_γE W g a) htf x`. Conclude with `fun j hj a => psi_single hex j hj a`.
-/
theorem psi_exists {l : ℕ} [NeZero l] (hp : PD.p = l)
    (hO : ∀ c : PowerSeries O, ((PD.p : ℕ) : PowerSeries O) * c = 0 → c = 0)
    (hex : ∀ x : W.EE, ∃! c : Fin l → W.EE, x = ∑ j : Fin l,
      (algebraMap (LetA O n) W.EE (1 + letπ)) ^ (j : ℕ) * (W.φE : W.EE →+* W.EE) (c j)) :
    ∃ ψ : W.EE →ₗ[O] W.EE, (∀ a x, ψ (W.φE a * x) = a * ψ x) ∧
      (∀ g x, ψ (W.γE g x) = W.γE g (ψ x)) ∧
      ∀ j < l, ∀ a, ψ (algebraMap (LetA O n) W.EE (1 + letπ) ^ j * W.φE a) = if j = 0 then a else 0 := by
  have hu : (algebraMap (LetA O n) W.EE (1 + letπ)) ^ l =
      (W.φE : W.EE →+* W.EE) (algebraMap (LetA O n) W.EE (1 + letπ)) := (φE_u W hp).symm
  have htf : ∀ x : W.EE, (l : W.EE) * x = 0 → x = 0 := by
    intro x hx
    refine tf W hO x ?_
    rw [hp]; exact hx
  refine ⟨{ toFun := psi hex, map_add' := psi_add hex, map_smul' := fun o x => ?_ }, ?_, ?_, ?_⟩
  · simp only [RingHom.id_apply, Algebra.smul_def]
    have := psi_φmul hex (algebraMap O W.EE o) x
    rwa [show (W.φE : W.EE →+* W.EE) (algebraMap O W.EE o) = algebraMap O W.EE o from
      W.φE.commutes o] at this
  · exact fun a x => psi_φmul hex a x
  · intro g x
    have h1 : ∀ a, W.γE g (W.γE g⁻¹ a) = a := fun a => by
      rw [← AlgHom.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgHom.one_apply]
    have h2 : ∀ a, W.γE g⁻¹ (W.γE g a) = a := fun a => by
      rw [← AlgHom.mul_apply, ← map_mul, inv_mul_cancel, map_one, AlgHom.one_apply]
    exact psi_gam hex hu (W.γE g : W.EE →+* W.EE) (W.γE g⁻¹ : W.EE →+* W.EE) h1 h2
      (fun a => φE_γE W g a) htf x
  · exact fun j hj a => psi_single hex j hj a

end GlobalTheory.PsiOp

namespace GlobalTheory

/- English proof (translation)
Introduce `D HW F l _ K s LL h`. Use `haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩`. Establish `hp : ((D.loc l).PD K).p = l` using `(D.loc l).PD_p K`. Use `GlobalTheory.PsiOp.psi_exists ((HW l).W K s LL h) hp ?_ (fun x => GlobalTheory.T.etaleRing_free_over_frobenius_image D HW F l K s LL h x)` and prove the remaining obligations. Introduce `c hc`.

Break down `mul_eq_zero.1 hc with h0 | h0` into its components or cases. It suffices to derive a contradiction. Rewrite `h0` using `[hp]`. Establish `h1 : ((l : ℕ) : ↥(OL LL)) = 0`. Use `congrArg PowerSeries.constantCoeff h0` as an intermediate fact.

Simplify using `using this`. Establish `h2 : ((l : ℕ) : ↥LL.1) = 0`. Use `congrArg Subtype.val h1` as an intermediate fact. Simplify using `using this`. Conclude with `(Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h2`.

Conclude with `h0`.
-/
theorem psiE_exists : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∃ ψ : W.EE →ₗ[↥(OL LL)] W.EE, (∀ a x, ψ (W.φE a * x) = a * ψ x) ∧ (∀ g x, ψ (W.γE g x) = W.γE g (ψ x)) ∧ ∀ j < l, ∀ a, ψ (algebraMap (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) W.EE ((1 : (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)))) + (letπ : (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))))) ^ j * W.φE a) = if j = 0 then a else 0 := by
  intro D HW F l _ K s LL h
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  refine GlobalTheory.PsiOp.psi_exists ((HW l).W K s LL h) hp ?_ (fun x => GlobalTheory.T.etaleRing_free_over_frobenius_image D HW F l K s LL h x)
  intro c hc
  rcases mul_eq_zero.1 hc with h0 | h0
  · exfalso
    rw [hp] at h0
    have h1 : ((l : ℕ) : ↥(OL LL)) = 0 := by
      have := congrArg PowerSeries.constantCoeff h0
      simpa using this
    have h2 : ((l : ℕ) : ↥LL.1) = 0 := by
      have := congrArg Subtype.val h1
      simpa using this
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h2
  · exact h0

end GlobalTheory
