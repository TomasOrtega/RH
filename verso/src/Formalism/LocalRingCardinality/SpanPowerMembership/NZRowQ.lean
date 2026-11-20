import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowP

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂

section TwoChar

variable {Z V : Type} [CommSemiring Z] [Algebra ℂ Z] [AddCommGroup V] [Module ℂ V]

def twoChar (χ1 χ0 : Z →ₐ[ℂ] ℂ) (E : Module.End ℂ V) (hE : E * E = E) : Z →ₐ[ℂ] Module.End ℂ V :=
  AlgHom.ofLinearMap (χ1.toLinearMap.smulRight E + χ0.toLinearMap.smulRight (1 - E))
    (by simp)
    (fun x y => by
      have hEF : E * (1 - E) = 0 := by rw [mul_sub, mul_one, hE, sub_self]
      have hFE : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hE, sub_self]
      have hFF : (1 - E) * (1 - E) = 1 - E := by rw [mul_sub, mul_one, hFE, sub_zero]
      simp only [LinearMap.add_apply, LinearMap.smulRight_apply, AlgHom.toLinearMap_apply, map_mul, add_mul,
        mul_add, smul_mul_smul_comm, hE, hEF, hFE, hFF, smul_zero, add_zero, zero_add])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem twoChar_apply (χ1 χ0 : Z →ₐ[ℂ] ℂ) (E : Module.End ℂ V) (hE : E * E = E) (z : Z) :
    twoChar χ1 χ0 E hE z = χ1 z • E + χ0 z • (1 - E) := rfl

end TwoChar

def MultT (EE A : Type) : ℕ → Type
  | 0 => EE
  | _ + 1 => A

section MultT

variable (EE A : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
  [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A]

instance MultT.nacg : ∀ j, NormedAddCommGroup (MultT EE A j)
  | 0 => inferInstanceAs (NormedAddCommGroup EE)
  | _ + 1 => inferInstanceAs (NormedAddCommGroup A)

instance MultT.ips : ∀ j, InnerProductSpace ℂ (MultT EE A j)
  | 0 => inferInstanceAs (InnerProductSpace ℂ EE)
  | _ + 1 => inferInstanceAs (InnerProductSpace ℂ A)

instance MultT.fd : ∀ j, FiniteDimensional ℂ (MultT EE A j)
  | 0 => inferInstanceAs (FiniteDimensional ℂ EE)
  | _ + 1 => inferInstanceAs (FiniteDimensional ℂ A)

def castTop : ∀ j, j ≠ 0 → MultT EE A j ≃ₗᵢ[ℂ] A
  | 0, h => absurd rfl h
  | _ + 1, _ => LinearIsometryEquiv.refl ℂ A

variable {EE A}

def ioT (pr : A →ₗ[ℂ] EE) : ∀ j, MultT EE A (j + 1) →ₗ[ℂ] MultT EE A j
  | 0 => pr
  | _ + 1 => LinearMap.id

end MultT

section Coord

variable {n : ℕ} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
  (b : OrthonormalBasis (Fin n) ℂ EE) (a n1 : ℕ) (hn : n ≤ n1) (h1 : n1 ≤ a)

def eP : En a →ₗ[ℂ] En a where
  toFun x := WithLp.toLp 2 fun i => if (i : ℕ) < n1 then x i else 0
  map_add' x y := by
    ext i
    by_cases hi : (i : ℕ) < n1 <;> simp [hi]
  map_smul' c x := by
    ext i
    by_cases hi : (i : ℕ) < n1 <;> simp [hi]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem eP_apply (x : En a) (i : Fin a) : eP a n1 x i = if (i : ℕ) < n1 then x i else 0 := rfl

/- English proof (translation)
Use extensionality with `x i`. Simplify using `only [LinearMap.comp_apply, eP_apply]`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem projection_idem : eP a n1 ∘ₗ eP a n1 = eP a n1 := by
  ext x i
  simp only [LinearMap.comp_apply, eP_apply]
  split_ifs <;> rfl

/- English proof (translation)
Introduce `x y`. Rewrite using `[PiLp.inner_apply, PiLp.inner_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[eP_apply, eP_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem projection_isSelfAdjoint : (eP a n1).IsSymmetric := by
  intro x y
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eP_apply, eP_apply]
  split_ifs <;> simp

include hn h1 in
/- English proof (translation)
The claim follows from `hn.trans h1`.
-/
theorem le_a : n ≤ a := hn.trans h1

def prB (h : n ≤ a) : En a →ₗ[ℂ] EE where
  toFun x := ∑ k : Fin n, x (Fin.castLE h k) • b k
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [mul_smul, Finset.smul_sum]

def secB : EE →ₗ[ℂ] En a where
  toFun y := WithLp.toLp 2 fun i => if hi : (i : ℕ) < n then b.repr y ⟨i, hi⟩ else 0
  map_add' x y := by
    ext i
    by_cases hi : (i : ℕ) < n <;> simp [hi]
  map_smul' c x := by
    ext i
    by_cases hi : (i : ℕ) < n <;> simp [hi]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem secB_apply (y : EE) (i : Fin a) : secB b a y i = if hi : (i : ℕ) < n then b.repr y ⟨i, hi⟩ else 0 := rfl

/- English proof (translation)
Use `show ∑ k : Fin n, secB b a y (Fin.castLE h k) • b k = y`. Use `conv_rhs => rw [← b.sum_repr y]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[secB_apply, dif_pos (show ((Fin.castLE h k : Fin a) : ℕ) < n from k.2)]`. Both sides reduce to the same expression.
-/
theorem prB_secB (h : n ≤ a) (y : EE) : prB b a h (secB b a y) = y := by
  show ∑ k : Fin n, secB b a y (Fin.castLE h k) • b k = y
  conv_rhs => rw [← b.sum_repr y]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [secB_apply, dif_pos (show ((Fin.castLE h k : Fin a) : ℕ) < n from k.2)]
  rfl

/- English proof (translation)
Use extensionality with `i`. Rewrite using `[eP_apply, secB_apply]`. Distinguish the cases in `hi : (i : ℕ) < n`. Rewrite using `[if_pos (lt_of_lt_of_le hi hn)]`. Rewrite using `[dif_neg hi]`.

Simplify using the standard rewrite rules.
-/
theorem eP_secB (hn : n ≤ n1) (y : EE) : eP a n1 (secB b a y) = secB b a y := by
  ext i
  rw [eP_apply, secB_apply]
  by_cases hi : (i : ℕ) < n
  · rw [if_pos (lt_of_lt_of_le hi hn)]
  · rw [dif_neg hi]; simp

/- English proof (translation)
Establish `h2` using `congrArg (fun z => b.repr z k) hu`. Establish `h3 : prB b a h u = ∑ k : Fin n, u (Fin.castLE h k) • b k` using `rfl`. Simplify using `only [h3, map_sum, map_smul, b.repr_self, map_zero] at h2`. Simplify `h2` using `[Finset.sum_apply, Pi.single_apply]`.
-/
theorem coord_of_prB (h : n ≤ a) {u : En a} (hu : prB b a h u = 0) (k : Fin n) : u (Fin.castLE h k) = 0 := by
  have h2 := congrArg (fun z => b.repr z k) hu
  have h3 : prB b a h u = ∑ k : Fin n, u (Fin.castLE h k) • b k := rfl
  simp only [h3, map_sum, map_smul, b.repr_self, map_zero] at h2
  simpa [Finset.sum_apply, Pi.single_apply] using h2

/- English proof (translation)
Rewrite using `[PiLp.inner_apply]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[secB_apply]`. Distinguish the cases in `hi : (i : ℕ) < n`. Use `coord_of_prB b a h hu ⟨i, hi⟩` as an intermediate fact.

Establish `e : Fin.castLE h ⟨i, hi⟩ = i` using `rfl`. Rewrite `this` using `[e]`. Rewrite using `[this]`. Simplify using the standard rewrite rules. Rewrite using `[dif_neg hi]`.

Simplify using the standard rewrite rules.
-/
theorem inner_secB_of_ker (h : n ≤ a) {u : En a} (hu : prB b a h u = 0) (y : EE) :
    inner ℂ u (secB b a y) = 0 := by
  rw [PiLp.inner_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [secB_apply]
  by_cases hi : (i : ℕ) < n
  · have := coord_of_prB b a h hu ⟨i, hi⟩
    have e : Fin.castLE h ⟨i, hi⟩ = i := rfl
    rw [e] at this
    rw [this]; simp
  · rw [dif_neg hi]; simp

/- English proof (translation)
Rewrite using `[← b.repr.inner_map_map y z, PiLp.inner_apply, PiLp.inner_apply]`. Use `(Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ (fun i hi => ?_) (fun k => ?_)).symm` and prove the remaining obligations. Establish `: ¬ (i : ℕ) < n` using `fun hlt => hi ⟨⟨i, hlt⟩, rfl⟩`. Rewrite using `[secB_apply, secB_apply, dif_neg this, dif_neg this]`. Simplify using the standard rewrite rules.

Rewrite using `[secB_apply, secB_apply, dif_pos (show ((Fin.castLE h k : Fin a) : ℕ) < n from k.2), dif_pos (show ((Fin.castLE h k : Fin a) : ℕ) < n from k.2)]`. Both sides reduce to the same expression.
-/
theorem inner_secB (h : n ≤ a) (y z : EE) : inner ℂ (secB b a y) (secB b a z) = inner ℂ y z := by
  rw [← b.repr.inner_map_map y z, PiLp.inner_apply, PiLp.inner_apply]
  refine (Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ (fun i hi => ?_)
    (fun k => ?_)).symm
  · have : ¬ (i : ℕ) < n := fun hlt => hi ⟨⟨i, hlt⟩, rfl⟩
    rw [secB_apply, secB_apply, dif_neg this, dif_neg this]; simp
  · rw [secB_apply, secB_apply, dif_pos (show ((Fin.castLE h k : Fin a) : ℕ) < n from k.2),
      dif_pos (show ((Fin.castLE h k : Fin a) : ℕ) < n from k.2)]
    rfl

/- English proof (translation)
Use extensionality with `k`. Simplify using `[Finset.sum_apply, Pi.single_apply]`.
-/
theorem sum_smul_eb (z : Fin a → ℂ) : ∑ i, z i • eb a i = WithLp.toLp 2 z := by
  ext k
  simp [Finset.sum_apply, Pi.single_apply]

end Coord

end Formalism.BasicNotions.Examples₂.NZ
