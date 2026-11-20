import Mathlib

noncomputable section

open Matrix Module Polynomial

namespace PositivityTheory.RgUd.T.Nil.Orb.BModbound

namespace LaurentWeightBound

variable {k : Type} [Field k] {n : ℕ}

/- English proof (translation)
Use `set N : ℕ := ∑ m ∈ M, m.natAbs with hN`. Establish `hle : ∀ m ∈ M, 0 ≤ m + N`. Introduce `m hm`. Establish `h1 : m.natAbs ≤ N` using `Finset.single_le_sum (f := fun m : ℤ => m.natAbs) (fun _ _ => Nat.zero_le _) hm`. Establish `h2 : -(m.natAbs : ℤ) ≤ m`.

Apply the tactic sequence `rcases Int.natAbs_eq m with h | h <;> omega`. Use linear arithmetic over natural numbers and integers. Set `e : ℤ → ℕ` to `fun m => (m + N).toNat`. Set `p : k[X]` to `∑ m ∈ M, C (c m) * X ^ (e m)`. Establish `heval : ∀ t : kˣ, p.eval (t : k) = 0`.

Introduce `t`. Establish `hx : ∀ m ∈ M, (t : k) ^ (e m) = (t : k) ^ N * ((t ^ m : kˣ) : k)`. Introduce `m hm`. Establish `h3 : ((e m : ℕ) : ℤ) = m + N` using `Int.toNat_of_nonneg (hle m hm)`. Establish `h4 : (t ^ ((e m : ℕ) : ℤ) : kˣ) = t ^ (N : ℤ) * t ^ m`.

Rewrite using `[h3, ← _root_.zpow_add, add_comm]`. Establish `h5` using `congrArg (fun u : kˣ => (u : k)) h4`. Simplify `h5` using `[zpow_natCast]`. Simplify using `only [p, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]`. Rewrite using `[Finset.sum_congr rfl (fun m hm => by rw [hx m hm])]`.

Rewrite using `[show (∑ m ∈ M, c m * ((t : k) ^ N * ((t ^ m : kˣ) : k))) = (t : k) ^ N * ∑ m ∈ M, ((t ^ m : kˣ) : k) * c m by`. Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl (fun m _ => by ring)]`. Rewrite using `[h t, mul_zero]`. Establish `hp : p = 0`. Apply `Polynomial.eq_zero_of_infinite_isRoot` to reduce the goal to its premises.

Establish `hinf : Set.Infinite ({0}ᶜ : Set k)` using `(Set.finite_singleton (0 : k)).infinite_compl`. Use `hinf.mono ?_` and prove the remaining obligations. Introduce `x hx`. Establish `hx' : x ≠ 0` using `hx`. Conclude with `heval (Units.mk0 x hx')`.

Introduce `m hm`. Establish `hc` using `congrArg (fun q : k[X] => q.coeff (e m)) hp`. Simplify using `only [p, finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at hc`. Rewrite `hc` using `[Finset.sum_eq_single m]`. Simplify using `using hc`.

Introduce `b hb hbm`. Establish `: e m ≠ e b`. Introduce `heq`. Establish `h3 : ((e m : ℕ) : ℤ) = m + N` using `Int.toNat_of_nonneg (hle m hm)`. Establish `h4 : ((e b : ℕ) : ℤ) = b + N` using `Int.toNat_of_nonneg (hle b hb)`.

Apply `hbm` to reduce the goal to its premises. Establish `: ((e m : ℕ) : ℤ) = ((e b : ℕ) : ℤ)` using `by rw [heq]`. Use linear arithmetic over natural numbers and integers. Simplify using `[this]`. Introduce `h`.

Conclude with `absurd hm h`.
-/
theorem laurent_coeff_zero [Infinite k] (M : Finset ℤ) (c : ℤ → k)
    (h : ∀ t : kˣ, ∑ m ∈ M, ((t ^ m : kˣ) : k) * c m = 0) : ∀ m ∈ M, c m = 0 := by
  classical
  set N : ℕ := ∑ m ∈ M, m.natAbs with hN
  have hle : ∀ m ∈ M, 0 ≤ m + N := by
    intro m hm
    have h1 : m.natAbs ≤ N := Finset.single_le_sum (f := fun m : ℤ => m.natAbs) (fun _ _ => Nat.zero_le _) hm
    have h2 : -(m.natAbs : ℤ) ≤ m := by
      rcases Int.natAbs_eq m with h | h <;> omega
    omega
  let e : ℤ → ℕ := fun m => (m + N).toNat
  let p : k[X] := ∑ m ∈ M, C (c m) * X ^ (e m)
  have heval : ∀ t : kˣ, p.eval (t : k) = 0 := by
    intro t
    have hx : ∀ m ∈ M, (t : k) ^ (e m) = (t : k) ^ N * ((t ^ m : kˣ) : k) := by
      intro m hm
      have h3 : ((e m : ℕ) : ℤ) = m + N := Int.toNat_of_nonneg (hle m hm)
      have h4 : (t ^ ((e m : ℕ) : ℤ) : kˣ) = t ^ (N : ℤ) * t ^ m := by
        rw [h3, ← _root_.zpow_add, add_comm]
      have h5 := congrArg (fun u : kˣ => (u : k)) h4
      simpa [zpow_natCast] using h5
    simp only [p, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    rw [Finset.sum_congr rfl (fun m hm => by rw [hx m hm])]
    rw [show (∑ m ∈ M, c m * ((t : k) ^ N * ((t ^ m : kˣ) : k))) =
      (t : k) ^ N * ∑ m ∈ M, ((t ^ m : kˣ) : k) * c m by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun m _ => by ring)]
    rw [h t, mul_zero]
  have hp : p = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    have hinf : Set.Infinite ({0}ᶜ : Set k) := (Set.finite_singleton (0 : k)).infinite_compl
    refine hinf.mono ?_
    intro x hx
    have hx' : x ≠ 0 := hx
    exact heval (Units.mk0 x hx')
  intro m hm
  have hc := congrArg (fun q : k[X] => q.coeff (e m)) hp
  simp only [p, finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at hc
  rw [Finset.sum_eq_single m] at hc
  · simpa using hc
  · intro b hb hbm
    have : e m ≠ e b := by
      intro heq
      have h3 : ((e m : ℕ) : ℤ) = m + N := Int.toNat_of_nonneg (hle m hm)
      have h4 : ((e b : ℕ) : ℤ) = b + N := Int.toNat_of_nonneg (hle b hb)
      apply hbm
      have : ((e m : ℕ) : ℤ) = ((e b : ℕ) : ℤ) := by rw [heq]
      omega
    simp [this]
  · intro h; exact absurd hm h

def gt (P : GL (Fin n) k) (w : Fin n → ℤ) (t : kˣ) : Matrix (Fin n) (Fin n) k :=
  P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val

def cut (w : Fin n → ℤ) (m : ℤ) (u : Fin n → k) : Fin n → k := fun i => if w i = m then u i else 0

def prj (P : GL (Fin n) k) (w : Fin n → ℤ) (m : ℤ) (y : Fin n → k) : Fin n → k :=
  P.val *ᵥ cut w m (P⁻¹.val *ᵥ y)

/- English proof (translation)
Simplify using `[prj, mulVec_mulVec]`.
-/
theorem inv_mulVec_prj (P : GL (Fin n) k) (w : Fin n → ℤ) (m : ℤ) (y : Fin n → k) :
    P⁻¹.val *ᵥ prj P w m y = cut w m (P⁻¹.val *ᵥ y) := by
  simp [prj, mulVec_mulVec]

/- English proof (translation)
Simplify using `only [prj, ← mulVec_smul, ← mulVec_sum]`. Rewrite using `[gt, ← mulVec_mulVec, ← mulVec_mulVec]`. Use `congr 1`. Use extensionality with `i`. Simplify using `only [mulVec_diagonal, Finset.sum_apply, Pi.smul_apply, cut, smul_eq_mul, mul_ite, mul_zero]`.

Rewrite using `[Finset.sum_ite_eq]`. Simplify using the standard rewrite rules.
-/
theorem gt_mulVec (P : GL (Fin n) k) (w : Fin n → ℤ) (t : kˣ) (y : Fin n → k) :
    gt P w t *ᵥ y = ∑ m ∈ Finset.univ.image w, ((t ^ m : kˣ) : k) • prj P w m y := by
  classical
  simp only [prj, ← mulVec_smul, ← mulVec_sum]
  rw [gt, ← mulVec_mulVec, ← mulVec_mulVec]
  congr 1
  ext i
  simp only [mulVec_diagonal, Finset.sum_apply, Pi.smul_apply, cut, smul_eq_mul, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

/- English proof (translation)
Establish `h` using `gt_mulVec P w 1 y`. Establish `hg : gt P w 1 = 1`. Simplify using `only [gt, _root_.one_zpow, Units.val_one]`. Rewrite using `[diagonal_one, mul_one, Units.mul_inv]`. Rewrite `h` using `[hg, one_mulVec]`.

Simplify using `using h.symm`.
-/
theorem sum_prj (P : GL (Fin n) k) (w : Fin n → ℤ) (y : Fin n → k) :
    ∑ m ∈ Finset.univ.image w, prj P w m y = y := by
  have h := gt_mulVec P w 1 y
  have hg : gt P w 1 = 1 := by
    simp only [gt, _root_.one_zpow, Units.val_one]
    rw [diagonal_one, mul_one, Units.mul_inv]
  rw [hg, one_mulVec] at h
  simpa using h.symm

/- English proof (translation)
Rewrite using `[gt, ← mulVec_mulVec, ← mulVec_mulVec, inv_mulVec_prj, prj, ← mulVec_smul]`. Use `congr 1`. Use extensionality with `i`. Simplify using `only [mulVec_diagonal, cut, Pi.smul_apply, smul_eq_mul]`. Use `split_ifs with h`.

Rewrite using `[h]`. Simplify using the standard rewrite rules.
-/
theorem gt_prj (P : GL (Fin n) k) (w : Fin n → ℤ) (t : kˣ) (m : ℤ) (y : Fin n → k) :
    gt P w t *ᵥ prj P w m y = ((t ^ m : kˣ) : k) • prj P w m y := by
  rw [gt, ← mulVec_mulVec, ← mulVec_mulVec, inv_mulVec_prj, prj, ← mulVec_smul]
  congr 1
  ext i
  simp only [mulVec_diagonal, cut, Pi.smul_apply, smul_eq_mul]
  split_ifs with h
  · rw [h]
  · simp

/- English proof (translation)
Rewrite using `[prj, inv_mulVec_prj]`. Use `congr 1`. Use extensionality with `i`. Simplify using `only [cut]`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem prj_prj (P : GL (Fin n) k) (w : Fin n → ℤ) (m : ℤ) (y : Fin n → k) :
    prj P w m (prj P w m y) = prj P w m y := by
  rw [prj, inv_mulVec_prj]
  congr 1
  ext i
  simp only [cut]
  split_ifs <;> rfl

/- English proof (translation)
Distinguish the cases in `hm : m ∈ Finset.univ.image w`. Rewrite using `[← Submodule.Quotient.mk_eq_zero]`. Rewrite using `[← Module.forall_dual_apply_eq_zero_iff k]`. Introduce `ℓ`. Establish `key` using `laurent_coeff_zero (Finset.univ.image w) (fun m => ℓ (Submodule.Quotient.mk (p := W) (prj P w m y))) (fun t => by`.

Establish `h1` using `hinv t y hy`. Rewrite `h1` using `[← Submodule.Quotient.mk_eq_zero, gt_mulVec]`. Establish `h2 : (ℓ ∘ₗ W.mkQ) (∑ m ∈ Finset.univ.image w, ((t ^ m : kˣ) : k) • prj P w m y) = 0`. Rewrite using `[LinearMap.comp_apply, Submodule.mkQ_apply, h1, map_zero]`. Rewrite `h2` using `[map_sum]`.

Simplify `h2) m hm` using `only [map_smul, LinearMap.comp_apply, Submodule.mkQ_apply, smul_eq_mul]`. Conclude with `key`. Establish `: prj P w m y = 0`. Rewrite using `[prj]`. Establish `hc : cut w m (P⁻¹.val *ᵥ y) = 0`.

Use extensionality with `i`. Simplify using `only [cut, Pi.zero_apply]`. Use `split_ifs with h`. Conclude with `absurd (Finset.mem_image.2 ⟨i, Finset.mem_univ _, h⟩) hm`. Both sides reduce to the same expression.

Rewrite using `[hc, mulVec_zero]`. Rewrite using `[this]`. Conclude with `W.zero_mem`.
-/
theorem prj_mem [Infinite k] (P : GL (Fin n) k) (w : Fin n → ℤ) (W : Submodule k (Fin n → k))
    (hinv : ∀ t : kˣ, ∀ y ∈ W, gt P w t *ᵥ y ∈ W) (m : ℤ) (y : Fin n → k) (hy : y ∈ W) :
    prj P w m y ∈ W := by
  classical
  by_cases hm : m ∈ Finset.univ.image w
  · rw [← Submodule.Quotient.mk_eq_zero]
    rw [← Module.forall_dual_apply_eq_zero_iff k]
    intro ℓ
    have key := laurent_coeff_zero (Finset.univ.image w)
      (fun m => ℓ (Submodule.Quotient.mk (p := W) (prj P w m y))) (fun t => by
        have h1 := hinv t y hy
        rw [← Submodule.Quotient.mk_eq_zero, gt_mulVec] at h1
        have h2 : (ℓ ∘ₗ W.mkQ) (∑ m ∈ Finset.univ.image w, ((t ^ m : kˣ) : k) • prj P w m y) = 0 := by
          rw [LinearMap.comp_apply, Submodule.mkQ_apply, h1, map_zero]
        rw [map_sum] at h2
        simpa only [map_smul, LinearMap.comp_apply, Submodule.mkQ_apply, smul_eq_mul] using h2) m hm
    exact key
  · have : prj P w m y = 0 := by
      rw [prj]
      have hc : cut w m (P⁻¹.val *ᵥ y) = 0 := by
        ext i
        simp only [cut, Pi.zero_apply]
        split_ifs with h
        · exact absurd (Finset.mem_image.2 ⟨i, Finset.mem_univ _, h⟩) hm
        · rfl
      rw [hc, mulVec_zero]
    rw [this]; exact W.zero_mem

/- English proof (translation)
Take `⟨u, rfl, hu⟩` from `hy`. Rewrite using `[prj, mulVec_mulVec]`. Simplify using `only [Units.inv_mul, one_mulVec]`. Establish `hc : cut w m u = 0`. Use extensionality with `i`.

Simplify using `only [cut, Pi.zero_apply]`. Use `split_ifs with h`. Conclude with `hu i (h ▸ hm)`. Both sides reduce to the same expression. Rewrite using `[hc, mulVec_zero]`.
-/
theorem prj_neg (P : GL (Fin n) k) (w : Fin n → ℤ) (m : ℤ) (hm : m < 0) (y : Fin n → k)
    (hy : ∃ u : Fin n → k, y = P.val *ᵥ u ∧ ∀ i, w i < 0 → u i = 0) : prj P w m y = 0 := by
  obtain ⟨u, rfl, hu⟩ := hy
  rw [prj, mulVec_mulVec]
  simp only [Units.inv_mul, one_mulVec]
  have hc : cut w m u = 0 := by
    ext i
    simp only [cut, Pi.zero_apply]
    split_ifs with h
    · exact hu i (h ▸ hm)
    · rfl
  rw [hc, mulVec_zero]

end LaurentWeightBound

open LaurentWeightBound

variable {k : Type} [Field k] [CharZero k] {n : ℕ}

/- English proof (translation)
Establish `hinv' : ∀ t : kˣ, ∀ y ∈ W, gt P w t *ᵥ y ∈ W` using `fun t y hy => by`. Use `hinv t y hy` as an intermediate fact. Rewrite `this` using `[Matrix.toLin'_apply]`. Then use the resulting hypothesis. Set `S : Set W` to `{y | ∃ m : ℕ, prj P w m (y : Fin n → k) = y}`. Establish `hspan : Submodule.span k S = ⊤`.

Rewrite using `[eq_top_iff]`. Introduce and unpack `⟨y, hy⟩ -`. Establish `hsum` using `sum_prj P w y`. Establish `hmem : ∀ m ∈ Finset.univ.image w, (⟨prj P w m y, prj_mem P w W hinv' m y hy⟩ : W) ∈ Submodule.span k S`. Introduce `m _`.

Distinguish the cases in `hm : m < 0`. Establish `h0 : (⟨prj P w m y, prj_mem P w W hinv' m y hy⟩ : W) = 0` using `Subtype.ext (prj_neg P w m hm y (hpos y hy))`. Rewrite using `[h0]`. Conclude with `Submodule.zero_mem _`. Apply `Submodule.subset_span` to reduce the goal to its premises.

Use `⟨m.toNat, ?_⟩` and prove the remaining obligations. Establish `: ((m.toNat : ℕ) : ℤ) = m` using `Int.toNat_of_nonneg (by omega)`. Simplify using `only [this]`. Conclude with `prj_prj P w m y`. Establish `: (⟨y, hy⟩ : W) = ∑ m ∈ Finset.univ.image w, (⟨prj P w m y, prj_mem P w W hinv' m y hy⟩ : W)`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Submodule.coe_sum]`. Conclude with `hsum.symm`. Rewrite using `[this]`. Conclude with `Submodule.sum_mem _ hmem`.

Take `⟨b, hbS, hbspan, hli⟩` from `exists_linearIndependent k S`. Establish `hfin : Finite b` using `hli.finite`. Set `_ : Fintype b` to `Fintype.ofFinite b`. Set `B : Basis b k W` to `Basis.mk hli (by`. Rewrite using `[Subtype.range_coe, hbspan, hspan])`.

Establish `hwt : ∀ j : b, ∃ m : ℕ, prj P w m ((j : W) : Fin n → k) = (j : W)` using `fun j => hbS j.2`. Use `choose mj hmj using hwt`. Use `⟨∑ j, mj j, fun t => ?_⟩` and prove the remaining obligations. Rewrite using `[← LinearMap.det_toMatrix B]`. Establish `hdiag : LinearMap.toMatrix B B ((Matrix.toLin' (P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val)).restrict (hinv t)) = diagonal (fun j => (t : k) ^ (mj j))`.

Use extensionality with `i j`. Rewrite using `[LinearMap.toMatrix_apply]`. Establish `hfj : (Matrix.toLin' (P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val)).restrict (hinv t) (B j) = (t : k) ^ (mj j) • B j`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[LinearMap.coe_restrict_apply, Matrix.toLin'_apply, Basis.mk_apply, Submodule.coe_smul]`.

Establish `h1` using `gt_prj P w t (mj j) ((j : W) : Fin n → k)`. Rewrite `h1` using `[hmj j]`. Establish `h2 : ((t ^ ((mj j : ℕ) : ℤ) : kˣ) : k) = (t : k) ^ (mj j)` using `by simp [zpow_natCast]`. Rewrite `h1` using `[h2]`. Conclude with `h1`.

Rewrite using `[hfj, map_smul, Basis.repr_self, diagonal_apply]`. Simplify using `only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[hij, Ne.symm hij]`. Rewrite using `[hdiag, det_diagonal, Finset.prod_pow_eq_pow_sum]`.
-/
theorem wt (P : GL (Fin n) k) (w : Fin n → ℤ) (W : Submodule k (Fin n → k))
    (hinv : ∀ t : kˣ, ∀ y ∈ W,
      Matrix.toLin' (P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val) y ∈ W)
    (hpos : ∀ y ∈ W, ∃ u : Fin n → k, y = P.val *ᵥ u ∧ ∀ i, w i < 0 → u i = 0) :
    ∃ m : ℕ, ∀ t : kˣ,
      LinearMap.det ((Matrix.toLin' (P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val)).restrict
        (hinv t)) = (t : k) ^ m := by
  classical
  have hinv' : ∀ t : kˣ, ∀ y ∈ W, gt P w t *ᵥ y ∈ W := fun t y hy => by
    have := hinv t y hy
    rwa [Matrix.toLin'_apply] at this

  let S : Set W := {y | ∃ m : ℕ, prj P w m (y : Fin n → k) = y}
  have hspan : Submodule.span k S = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨y, hy⟩ -
    have hsum := sum_prj P w y
    have hmem : ∀ m ∈ Finset.univ.image w, (⟨prj P w m y, prj_mem P w W hinv' m y hy⟩ : W) ∈ Submodule.span k S := by
      intro m _
      by_cases hm : m < 0
      · have h0 : (⟨prj P w m y, prj_mem P w W hinv' m y hy⟩ : W) = 0 :=
          Subtype.ext (prj_neg P w m hm y (hpos y hy))
        rw [h0]; exact Submodule.zero_mem _
      · apply Submodule.subset_span
        refine ⟨m.toNat, ?_⟩
        have : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg (by omega)
        simp only [this]
        exact prj_prj P w m y
    have : (⟨y, hy⟩ : W) = ∑ m ∈ Finset.univ.image w, (⟨prj P w m y, prj_mem P w W hinv' m y hy⟩ : W) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      exact hsum.symm
    rw [this]
    exact Submodule.sum_mem _ hmem
  obtain ⟨b, hbS, hbspan, hli⟩ := exists_linearIndependent k S
  have hfin : Finite b := hli.finite
  let _ : Fintype b := Fintype.ofFinite b
  let B : Basis b k W := Basis.mk hli (by
    rw [Subtype.range_coe, hbspan, hspan])
  have hwt : ∀ j : b, ∃ m : ℕ, prj P w m ((j : W) : Fin n → k) = (j : W) := fun j => hbS j.2
  choose mj hmj using hwt
  refine ⟨∑ j, mj j, fun t => ?_⟩
  rw [← LinearMap.det_toMatrix B]
  have hdiag : LinearMap.toMatrix B B ((Matrix.toLin' (P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) *
      P⁻¹.val)).restrict (hinv t)) = diagonal (fun j => (t : k) ^ (mj j)) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    have hfj : (Matrix.toLin' (P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val)).restrict (hinv t) (B j)
        = (t : k) ^ (mj j) • B j := by
      apply Subtype.ext
      rw [LinearMap.coe_restrict_apply, Matrix.toLin'_apply, Basis.mk_apply, Submodule.coe_smul]
      have h1 := gt_prj P w t (mj j) ((j : W) : Fin n → k)
      rw [hmj j] at h1
      have h2 : ((t ^ ((mj j : ℕ) : ℤ) : kˣ) : k) = (t : k) ^ (mj j) := by simp [zpow_natCast]
      rw [h2] at h1
      exact h1
    rw [hfj, map_smul, Basis.repr_self, diagonal_apply]
    simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  rw [hdiag, det_diagonal, Finset.prod_pow_eq_pow_sum]

end PositivityTheory.RgUd.T.Nil.Orb.BModbound
