import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.JacRev

open MvPolynomial Matrix

noncomputable section

namespace PI.OddDualWeyl.Low

variable {R : Type*} [CommRing R]

def mnr (R : Type*) [CommRing R] {k n : ℕ} (h : n ≤ k) (ρ : Fin n → Fin k) :
    MvPolynomial (Fin k × Fin k) R :=
  (Matrix.of fun p q : Fin n => (X (ρ p, Fin.castLE h q) : MvPolynomial (Fin k × Fin k) R)).det

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma pMinor_eq {k : ℕ} (σ : Equiv.Perm (Fin k)) (n : ℕ) (h : n ≤ k) :
    pMinor R σ n h = mnr R h (σ ∘ Fin.castLE h) := rfl

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
lemma pMinor_congr {k : ℕ} (σ : Equiv.Perm (Fin k)) {n n' : ℕ} (e : n = n') (h : n ≤ k) (h' : n' ≤ k) :
    pMinor R σ n h = pMinor R σ n' h' := by
  subst e; rfl

/- English proof (translation)
Simplify using `[rowGen]`.
-/
lemma rowGen_X {k : ℕ} (a b : Fin k) (v : Fin k × Fin k) :
    rowGen R a b (X v) = Polynomial.C (X v) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) := by
  simp [rowGen]

/- English proof (translation)
Rewrite using `[mnr, AlgHom.map_det]`. Use `congr 1`. Use extensionality with `p q`. Simplify using `[rowGen_X]`.
-/
lemma rowGen_mnr_mat {k n : ℕ} (h : n ≤ k) (a b : Fin k) (ρ : Fin n → Fin k) :
    rowGen R a b (mnr R h ρ) = (Matrix.of fun p q : Fin n =>
      Polynomial.C (X (ρ p, Fin.castLE h q) : MvPolynomial (Fin k × Fin k) R) +
      (if ρ p = b then Polynomial.X * Polynomial.C (X (a, Fin.castLE h q)) else 0)).det := by
  rw [mnr, AlgHom.map_det]
  congr 1
  ext p q
  simp [rowGen_X]

/- English proof (translation)
Rewrite using `[mnr, RingHom.map_det]`. Use `congr 1`.
-/
lemma C_mnr {k n : ℕ} (h : n ≤ k) (ρ : Fin n → Fin k) :
    (Polynomial.C (mnr R h ρ) : Polynomial (MvPolynomial (Fin k × Fin k) R)) =
      (Matrix.of fun p q : Fin n =>
        Polynomial.C (X (ρ p, Fin.castLE h q) : MvPolynomial (Fin k × Fin k) R)).det := by
  rw [mnr, RingHom.map_det]
  congr 1

/- English proof (translation)
Rewrite using `[rowGen_mnr_mat, C_mnr]`. Use `congr 1`. Use extensionality with `p q`. Simplify using `[hb p]`.
-/
lemma rowGen_mnr_of_not {k n : ℕ} (h : n ≤ k) (a b : Fin k) (ρ : Fin n → Fin k)
    (hb : ∀ p, ρ p ≠ b) : rowGen R a b (mnr R h ρ) = Polynomial.C (mnr R h ρ) := by
  rw [rowGen_mnr_mat, C_mnr]
  congr 1
  ext p q
  simp [hb p]

/- English proof (translation)
Use `set A : Matrix (Fin n) (Fin n) (Polynomial (MvPolynomial (Fin k × Fin k) R)) := Matrix.of fun p q => Polynomial.C (X (ρ p, Fin.castLE h q)) with hA`. Use `set v : Fin n → Polynomial (MvPolynomial (Fin k × Fin k) R) := fun q => Polynomial.C (X (a, Fin.castLE h q)) with hv`. Establish `h1 : (Matrix.of fun p q : Fin n => Polynomial.C (X (ρ p, Fin.castLE h q) : MvPolynomial (Fin k × Fin k) R) + (if ρ p = b then Polynomial.X * Polynomial.C (X (a, Fin.castLE h q)) else 0)) = updateRow A p0 (A p0 + (Polynomial.X : Polynomial (MvPolynomial (Fin k × Fin k) R)) • v)`. Use extensionality with `p q`. Distinguish the cases in `hp : p = p0`.

Substitute `hp` using the available equality. Simplify using `[hA, hv, hp0]`. Establish `: ρ p ≠ b` using `fun e => hp (hρ (e.trans hp0.symm))`. Simplify using `[hA, updateRow_ne hp, this]`. Establish `h2 : updateRow A p0 v = Matrix.of fun p q : Fin n => Polynomial.C (X (Function.update ρ p0 a p, Fin.castLE h q) : MvPolynomial (Fin k × Fin k) R)`.

Use extensionality with `p q`. Distinguish the cases in `hp : p = p0`. Substitute `hp` using the available equality. Simplify using `[hv]`. Simplify using `[hA, updateRow_ne hp, Function.update_of_ne hp]`.

Rewrite using `[rowGen_mnr_mat, h1, det_updateRow_add, updateRow_eq_self, det_updateRow_smul, h2, C_mnr, C_mnr]`.
-/
lemma rowGen_mnr_of_eq {k n : ℕ} (h : n ≤ k) (a b : Fin k) (ρ : Fin n → Fin k)
    (hρ : Function.Injective ρ) (p0 : Fin n) (hp0 : ρ p0 = b) :
    rowGen R a b (mnr R h ρ) = Polynomial.C (mnr R h ρ) +
      Polynomial.X * Polynomial.C (mnr R h (Function.update ρ p0 a)) := by
  classical
  set A : Matrix (Fin n) (Fin n) (Polynomial (MvPolynomial (Fin k × Fin k) R)) :=
    Matrix.of fun p q => Polynomial.C (X (ρ p, Fin.castLE h q)) with hA
  set v : Fin n → Polynomial (MvPolynomial (Fin k × Fin k) R) :=
    fun q => Polynomial.C (X (a, Fin.castLE h q)) with hv
  have h1 : (Matrix.of fun p q : Fin n =>
      Polynomial.C (X (ρ p, Fin.castLE h q) : MvPolynomial (Fin k × Fin k) R) +
      (if ρ p = b then Polynomial.X * Polynomial.C (X (a, Fin.castLE h q)) else 0)) =
      updateRow A p0 (A p0 + (Polynomial.X : Polynomial (MvPolynomial (Fin k × Fin k) R)) • v) := by
    ext p q
    by_cases hp : p = p0
    · subst hp; simp [hA, hv, hp0]
    · have : ρ p ≠ b := fun e => hp (hρ (e.trans hp0.symm))
      simp [hA, updateRow_ne hp, this]
  have h2 : updateRow A p0 v = Matrix.of fun p q : Fin n =>
      Polynomial.C (X (Function.update ρ p0 a p, Fin.castLE h q) : MvPolynomial (Fin k × Fin k) R) := by
    ext p q
    by_cases hp : p = p0
    · subst hp; simp [hv]
    · simp [hA, updateRow_ne hp, Function.update_of_ne hp]
  rw [rowGen_mnr_mat, h1, det_updateRow_add, updateRow_eq_self, det_updateRow_smul, h2, C_mnr, C_mnr]

/- English proof (translation)
Rewrite using `[mnr]`. Apply `det_zero_of_row_eq (i := p0) (j := p1) hne.symm` to reduce the goal to its premises. Use function extensionality and compare the values at `q`. Simplify using `[Function.update_of_ne hne, hp1]`.
-/
lemma mnr_update_eq_zero {k n : ℕ} (h : n ≤ k) (a : Fin k) (ρ : Fin n → Fin k) (p0 p1 : Fin n)
    (hne : p1 ≠ p0) (hp1 : ρ p1 = a) : mnr R h (Function.update ρ p0 a) = 0 := by
  classical
  rw [mnr]
  apply det_zero_of_row_eq (i := p0) (j := p1) hne.symm
  funext q
  simp [Function.update_of_ne hne, hp1]

/- English proof (translation)
Establish `e : (Matrix.of fun x y : Fin n => (X ((ρ ∘ Equiv.swap p q) x, Fin.castLE h y) : MvPolynomial (Fin k × Fin k) R)) = (Matrix.of fun x y : Fin n => (X (ρ x, Fin.castLE h y) : MvPolynomial (Fin k × Fin k) R)).submatrix (Equiv.swap p q) id`. Use extensionality with `x y`. Simplify using the standard rewrite rules. Rewrite using `[mnr, e, det_permute, Equiv.Perm.sign_swap hpq]`. Simplify using `[mnr]`.
-/
lemma mnr_comp_swap {k n : ℕ} (h : n ≤ k) (ρ : Fin n → Fin k) (p q : Fin n) (hpq : p ≠ q) :
    mnr R h (ρ ∘ Equiv.swap p q) = - mnr R h ρ := by
  have e : (Matrix.of fun x y : Fin n =>
      (X ((ρ ∘ Equiv.swap p q) x, Fin.castLE h y) : MvPolynomial (Fin k × Fin k) R)) =
      (Matrix.of fun x y : Fin n =>
        (X (ρ x, Fin.castLE h y) : MvPolynomial (Fin k × Fin k) R)).submatrix (Equiv.swap p q) id := by
    ext x y; simp
  rw [mnr, e, det_permute, Equiv.Perm.sign_swap hpq]
  simp [mnr]

end PI.OddDualWeyl.Low

namespace PI.OddDualWeyl.Low

variable {R : Type*} [CommRing R]

/- English proof (translation)
Establish `h : (Polynomial.C u + Polynomial.X * Polynomial.C v).natDegree ≤ 1` using `by compute_degree`. Use `Polynomial.coeff_pow_of_natDegree_le (m := j) h` as an intermediate fact. Rewrite `this` using `[mul_one]`. Rewrite using `[this]`. Use `congr 1`.

Rewrite using `[mul_comm]`. Simplify using the standard rewrite rules.
-/
lemma coeff_lin_pow {S : Type*} [CommRing S] (u v : S) (j : ℕ) :
    ((Polynomial.C u + Polynomial.X * Polynomial.C v) ^ j).coeff j = v ^ j := by
  have h : (Polynomial.C u + Polynomial.X * Polynomial.C v).natDegree ≤ 1 := by compute_degree
  have := Polynomial.coeff_pow_of_natDegree_le (m := j) h
  rw [mul_one] at this
  rw [this]
  congr 1
  rw [mul_comm]
  simp

/- English proof (translation)
Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨w, rfl⟩` from `hx`. Conclude with `Submodule.subset_span ⟨(a, b, j) :: w, rfl⟩`. Consider the case `zero => simp [rowDiv]`.

Consider the case `add x y _ _ hx hy => simpa [rowDiv] using add_mem hx hy`. Consider the case `smul c x _ hx => simpa [rowDiv] using Submodule.smul_mem _ c hx`.
-/
lemma rowDiv_mem {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (a b : Fin r) (j : ℕ)
    {f : MvPolynomial (Fin r × Fin n) R} (hf : f ∈ weyl R r n hn ν) :
    rowDiv R a b j f ∈ weyl R r n hn ν := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    exact Submodule.subset_span ⟨(a, b, j) :: w, rfl⟩
  | zero => simp [rowDiv]
  | add x y _ _ hx hy => simpa [rowDiv] using add_mem hx hy
  | smul c x _ hx => simpa [rowDiv] using Submodule.smul_mem _ c hx

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨[], rfl⟩`.
-/
lemma hw_mem {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) : hw R hn ν ∈ weyl R r n hn ν :=
  Submodule.subset_span ⟨[], rfl⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma pw_one {k : ℕ} (ν : Fin k → ℕ) : pw R 1 ν = hw R le_rfl ν := rfl

section Step

variable {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (i : Fin n)

/- English proof (translation)
Introduce `e`. Use `congrArg Fin.val e` as an intermediate fact. Simplify using `at this`. Use linear arithmetic over natural numbers and integers.
-/
lemma castLE_ne_of_lt {s : ℕ} (h : s ≤ n + 1) (p : Fin s) (j : Fin (n + 1)) (hj : p.val < j.val) :
    Fin.castLE h p ≠ j := by
  intro e; have := congrArg Fin.val e; simp at this; omega

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite using `[pMinor_eq]`. Apply `rowGen_mnr_of_not` to reduce the goal to its premises. Introduce `p hp`. Conclude with `castLE_ne_of_lt _ p _ (by simp; omega) (σ.injective hp)`.

Rewrite using `[pMinor_eq, pMinor_eq]`. Use `congr 1`. Use function extensionality and compare the values at `p`. Simplify using `only [Function.comp, Equiv.Perm.mul_apply]`. Rewrite using `[Equiv.swap_apply_of_ne_of_ne (castLE_ne_of_lt _ p _ (by simp; omega)) (castLE_ne_of_lt _ p _ (by simp; omega))]`.
-/
lemma stepA (s : Fin (n + 1)) (hs : s.val < i.val) :
    rowGen R (σ i.succ) (σ i.castSucc) (pMinor R σ (s.val + 1) s.isLt) =
      Polynomial.C (pMinor R σ (s.val + 1) s.isLt) ∧
    pMinor R (σ * Equiv.swap i.castSucc i.succ) (s.val + 1) s.isLt = pMinor R σ (s.val + 1) s.isLt := by
  constructor
  · rw [pMinor_eq]
    apply rowGen_mnr_of_not
    intro p hp
    exact castLE_ne_of_lt _ p _ (by simp; omega) (σ.injective hp)
  · rw [pMinor_eq, pMinor_eq]
    congr 1
    funext p
    simp only [Function.comp, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (castLE_ne_of_lt _ p _ (by simp; omega))
      (castLE_ne_of_lt _ p _ (by simp; omega))]

/- English proof (translation)
Establish `hl : Fin.castLE s.isLt (Fin.last s.val) = i.castSucc` using `Fin.ext (by simp [hs])`. Establish `key : (σ * Equiv.swap i.castSucc i.succ) ∘ Fin.castLE s.isLt = Function.update (σ ∘ Fin.castLE s.isLt) (Fin.last s.val) (σ i.succ)`. Use function extensionality and compare the values at `p`. Distinguish the cases in `hp : p = Fin.last s.val`. Substitute `hp` using the available equality.

Simplify using `only [Function.comp, Equiv.Perm.mul_apply, Function.update_self, hl, Equiv.swap_apply_left]`. Establish `hlt` using `Fin.val_lt_last hp`. Rewrite using `[Function.update_of_ne hp]`. Simplify using `only [Function.comp, Equiv.Perm.mul_apply]`. Rewrite using `[Equiv.swap_apply_of_ne_of_ne (castLE_ne_of_lt _ p _ (by simp; omega)) (castLE_ne_of_lt _ p _ (by simp; omega))]`.

Rewrite using `[pMinor_eq, pMinor_eq, key]`. Conclude with `rowGen_mnr_of_eq _ _ _ _ (σ.injective.comp (Fin.castLE_injective _)) _ (by simp only [Function.comp, hl])`.
-/
lemma stepB (s : Fin (n + 1)) (hs : s.val = i.val) :
    rowGen R (σ i.succ) (σ i.castSucc) (pMinor R σ (s.val + 1) s.isLt) =
      Polynomial.C (pMinor R σ (s.val + 1) s.isLt) +
      Polynomial.X * Polynomial.C (pMinor R (σ * Equiv.swap i.castSucc i.succ) (s.val + 1) s.isLt) := by
  classical
  have hl : Fin.castLE s.isLt (Fin.last s.val) = i.castSucc := Fin.ext (by simp [hs])
  have key : (σ * Equiv.swap i.castSucc i.succ) ∘ Fin.castLE s.isLt =
      Function.update (σ ∘ Fin.castLE s.isLt) (Fin.last s.val) (σ i.succ) := by
    funext p
    by_cases hp : p = Fin.last s.val
    · subst hp
      simp only [Function.comp, Equiv.Perm.mul_apply, Function.update_self, hl, Equiv.swap_apply_left]
    · have hlt := Fin.val_lt_last hp
      rw [Function.update_of_ne hp]
      simp only [Function.comp, Equiv.Perm.mul_apply]
      rw [Equiv.swap_apply_of_ne_of_ne (castLE_ne_of_lt _ p _ (by simp; omega))
        (castLE_ne_of_lt _ p _ (by simp; omega))]
  rw [pMinor_eq, pMinor_eq, key]
  exact rowGen_mnr_of_eq _ _ _ _ (σ.injective.comp (Fin.castLE_injective _)) _
    (by simp only [Function.comp, hl])

/- English proof (translation)
Use `set p0 : Fin (s.val + 1) := ⟨i.val, by omega⟩ with hp0`. Use `set p1 : Fin (s.val + 1) := ⟨i.val + 1, by omega⟩ with hp1`. Establish `h0 : Fin.castLE s.isLt p0 = i.castSucc` using `Fin.ext (by simp [hp0])`. Establish `h1 : Fin.castLE s.isLt p1 = i.succ` using `Fin.ext (by simp [hp1])`. Establish `hne : p1 ≠ p0` using `by intro e; have := congrArg Fin.val e; simp [hp0, hp1] at this`.

Prove the components needed by the constructor for the conclusion. Rewrite using `[pMinor_eq, rowGen_mnr_of_eq _ _ _ _ (σ.injective.comp (Fin.castLE_injective _)) p0 (by simp only [Function.comp, h0]), mnr_update_eq_zero _ _ _ p0 p1 hne (by simp only [Function.comp, h1])]`. Simplify using the standard rewrite rules. Establish `key : (σ * Equiv.swap i.castSucc i.succ) ∘ Fin.castLE s.isLt = (σ ∘ Fin.castLE s.isLt) ∘ Equiv.swap p0 p1`. Use function extensionality and compare the values at `p`.

Simplify using `only [Function.comp, Equiv.Perm.mul_apply]`. Use `congr 1`. Rewrite using `[← h0, ← h1, (Fin.castLE_injective s.isLt).swap_apply]`. Rewrite using `[pMinor_eq, pMinor_eq, key, mnr_comp_swap _ _ _ _ hne.symm]`.
-/
lemma stepC (s : Fin (n + 1)) (hs : i.val < s.val) :
    rowGen R (σ i.succ) (σ i.castSucc) (pMinor R σ (s.val + 1) s.isLt) =
      Polynomial.C (pMinor R σ (s.val + 1) s.isLt) ∧
    pMinor R (σ * Equiv.swap i.castSucc i.succ) (s.val + 1) s.isLt = - pMinor R σ (s.val + 1) s.isLt := by
  classical
  set p0 : Fin (s.val + 1) := ⟨i.val, by omega⟩ with hp0
  set p1 : Fin (s.val + 1) := ⟨i.val + 1, by omega⟩ with hp1
  have h0 : Fin.castLE s.isLt p0 = i.castSucc := Fin.ext (by simp [hp0])
  have h1 : Fin.castLE s.isLt p1 = i.succ := Fin.ext (by simp [hp1])
  have hne : p1 ≠ p0 := by intro e; have := congrArg Fin.val e; simp [hp0, hp1] at this
  constructor
  · rw [pMinor_eq, rowGen_mnr_of_eq _ _ _ _ (σ.injective.comp (Fin.castLE_injective _)) p0
      (by simp only [Function.comp, h0]), mnr_update_eq_zero _ _ _ p0 p1 hne
      (by simp only [Function.comp, h1])]
    simp
  · have key : (σ * Equiv.swap i.castSucc i.succ) ∘ Fin.castLE s.isLt =
        (σ ∘ Fin.castLE s.isLt) ∘ Equiv.swap p0 p1 := by
      funext p
      simp only [Function.comp, Equiv.Perm.mul_apply]
      congr 1
      rw [← h0, ← h1, (Fin.castLE_injective s.isLt).swap_apply]
    rw [pMinor_eq, pMinor_eq, key, mnr_comp_swap _ _ _ _ hne.symm]

end Step

end PI.OddDualWeyl.Low

namespace PI.OddDualWeyl.Low

variable {R : Type*} [CommRing R]

/- English proof (translation)
Set `m : Fin (n + 1) → MvPolynomial (Fin (n + 1) × Fin (n + 1)) R` to `fun s => pMinor R σ (s.val + 1) s.isLt`. Set `m' : Fin (n + 1) → MvPolynomial (Fin (n + 1) × Fin (n + 1)) R` to `fun s => pMinor R (σ * Equiv.swap i.castSucc i.succ) (s.val + 1) s.isLt`. Set `c : Fin (n + 1) → ℕ` to `fun s => ν s - nuNext ν s`. Set `ε : Fin (n + 1) → R` to `fun s => if i.val < s.val then -1 else 1`. Establish `hne : ∀ s, s ≠ i.castSucc → rowGen R (σ i.succ) (σ i.castSucc) (m s) = Polynomial.C (m s) ∧ m' s = MvPolynomial.C (ε s) * m s`.

Introduce `s hs`. Establish `: s.val ≠ i.val` using `fun e => hs (Fin.ext (by simp [e]))`. Break down `Nat.lt_or_gt_of_ne this with h | h` into its components or cases. Take `⟨h1, h2⟩` from `stepA (R := R) σ i s h`. Use `⟨h1, ?_⟩` and prove the remaining obligations.

Simplify using `only [m', m, ε, h2, if_neg (by omega : ¬ i.val < s.val), map_one, one_mul]`. Take `⟨h1, h2⟩` from `stepC (R := R) σ i s h`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Simplify using `only [m', m, ε, h2, if_pos h, map_neg, map_one, neg_one_mul]`. Establish `hI : rowGen R (σ i.succ) (σ i.castSucc) (m i.castSucc) = Polynomial.C (m i.castSucc) + Polynomial.X * Polynomial.C (m' i.castSucc)` using `stepB (R := R) σ i i.castSucc (by simp)`.

Establish `hrd : rowDiv R (σ i.succ) (σ i.castSucc) (c i.castSucc) (pw R σ ν) = m' i.castSucc ^ c i.castSucc * ∏ s ∈ Finset.univ.erase i.castSucc, m s ^ c s` using `by show (rowGen R (σ i.succ) (σ i.castSucc) (∏ s, m s ^ c s)).coeff (c i.castSucc) = _`. Rewrite using `[map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i.castSucc)]`. Rewrite using `[Finset.prod_congr rfl (fun s hs => by`. Rewrite using `[map_pow, (hne s (Finset.ne_of_mem_erase hs)).1])]`. Rewrite using `[map_pow, hI, show ∏ s ∈ Finset.univ.erase i.castSucc, (Polynomial.C (m s)) ^ c s = Polynomial.C (∏ s ∈ Finset.univ.erase i.castSucc, m s ^ c s) by simp [map_prod, map_pow], Polynomial.coeff_mul_C, coeff_lin_pow]`.

Use `⟨∏ s ∈ Finset.univ.erase i.castSucc, ε s ^ c s, ?_⟩` and prove the remaining obligations. Rewrite using `[show ν i.castSucc - nuNext ν i.castSucc = c i.castSucc from rfl, hrd, ← MvPolynomial.C_mul']`. Use `show ∏ s, m' s ^ c s = _`. Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ i.castSucc)]`. Rewrite using `[Finset.prod_congr rfl (fun s hs => by rw [(hne s (Finset.ne_of_mem_erase hs)).2])]`.

Simplify using `only [mul_pow, Finset.prod_mul_distrib, map_prod, map_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem step {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (i : Fin n) (ν : Fin (n + 1) → ℕ) :
    ∃ c : R, pw R (σ * Equiv.swap i.castSucc i.succ) ν =
      c • rowDiv R (σ i.succ) (σ i.castSucc) (ν i.castSucc - nuNext ν i.castSucc) (pw R σ ν) := by
  classical
  let m : Fin (n + 1) → MvPolynomial (Fin (n + 1) × Fin (n + 1)) R :=
    fun s => pMinor R σ (s.val + 1) s.isLt
  let m' : Fin (n + 1) → MvPolynomial (Fin (n + 1) × Fin (n + 1)) R :=
    fun s => pMinor R (σ * Equiv.swap i.castSucc i.succ) (s.val + 1) s.isLt
  let c : Fin (n + 1) → ℕ := fun s => ν s - nuNext ν s
  let ε : Fin (n + 1) → R := fun s => if i.val < s.val then -1 else 1
  have hne : ∀ s, s ≠ i.castSucc → rowGen R (σ i.succ) (σ i.castSucc) (m s) = Polynomial.C (m s) ∧
      m' s = MvPolynomial.C (ε s) * m s := by
    intro s hs
    have : s.val ≠ i.val := fun e => hs (Fin.ext (by simp [e]))
    rcases Nat.lt_or_gt_of_ne this with h | h
    · obtain ⟨h1, h2⟩ := stepA (R := R) σ i s h
      refine ⟨h1, ?_⟩
      simp only [m', m, ε, h2, if_neg (by omega : ¬ i.val < s.val), map_one, one_mul]
    · obtain ⟨h1, h2⟩ := stepC (R := R) σ i s h
      refine ⟨h1, ?_⟩
      simp only [m', m, ε, h2, if_pos h, map_neg, map_one, neg_one_mul]
  have hI : rowGen R (σ i.succ) (σ i.castSucc) (m i.castSucc) =
      Polynomial.C (m i.castSucc) + Polynomial.X * Polynomial.C (m' i.castSucc) :=
    stepB (R := R) σ i i.castSucc (by simp)
  have hrd : rowDiv R (σ i.succ) (σ i.castSucc) (c i.castSucc) (pw R σ ν) =
      m' i.castSucc ^ c i.castSucc * ∏ s ∈ Finset.univ.erase i.castSucc, m s ^ c s := by
    show (rowGen R (σ i.succ) (σ i.castSucc) (∏ s, m s ^ c s)).coeff (c i.castSucc) = _
    rw [map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i.castSucc)]
    rw [Finset.prod_congr rfl (fun s hs => by
      rw [map_pow, (hne s (Finset.ne_of_mem_erase hs)).1])]
    rw [map_pow, hI, show ∏ s ∈ Finset.univ.erase i.castSucc, (Polynomial.C (m s)) ^ c s =
      Polynomial.C (∏ s ∈ Finset.univ.erase i.castSucc, m s ^ c s) by simp [map_prod, map_pow],
      Polynomial.coeff_mul_C, coeff_lin_pow]
  refine ⟨∏ s ∈ Finset.univ.erase i.castSucc, ε s ^ c s, ?_⟩
  rw [show ν i.castSucc - nuNext ν i.castSucc = c i.castSucc from rfl, hrd, ← MvPolynomial.C_mul']
  show ∏ s, m' s ^ c s = _
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i.castSucc)]
  rw [Finset.prod_congr rfl (fun s hs => by rw [(hne s (Finset.ne_of_mem_erase hs)).2])]
  simp only [mul_pow, Finset.prod_mul_distrib, map_prod, map_pow]
  ring

/- English proof (translation)
Establish `hσ : σ ∈ Submonoid.closure (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ)`. Rewrite using `[Equiv.Perm.mclosure_swap_castSucc_succ]`. Discharge the goal by the elementary cases of `trivial`. Use `Submonoid.closure_induction_right (motive := fun x _ => pw R x ν ∈ weyl R (n + 1) (n + 1) le_rfl ν) ?_ ?_ hσ` and prove the remaining obligations. Rewrite using `[pw_one]`.

Conclude with `hw_mem _ _`. Introduce `x _ y hy ih`. Take `⟨i, rfl⟩` from `hy`. Take `⟨c, hc⟩` from `step (R := R) x i ν`. Rewrite using `[hc]`.

Conclude with `Submodule.smul_mem _ c (rowDiv_mem _ _ _ _ _ ih)`.
-/
theorem pw_mem {n : ℕ} (ν : Fin (n + 1) → ℕ) (σ : Equiv.Perm (Fin (n + 1))) :
    pw R σ ν ∈ weyl R (n + 1) (n + 1) le_rfl ν := by
  have hσ : σ ∈ Submonoid.closure (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial
  refine Submonoid.closure_induction_right
    (motive := fun x _ => pw R x ν ∈ weyl R (n + 1) (n + 1) le_rfl ν) ?_ ?_ hσ
  · rw [pw_one]; exact hw_mem _ _
  · intro x _ y hy ih
    obtain ⟨i, rfl⟩ := hy
    obtain ⟨c, hc⟩ := step (R := R) x i ν
    rw [hc]
    exact Submodule.smul_mem _ c (rowDiv_mem _ _ _ _ _ ih)

end PI.OddDualWeyl.Low

namespace PI.OddDualWeyl

/- English proof (translation)
Introduce `R _ k ν`. Consider the cases of `k with`. Consider the case `zero`. Establish `: low R ν = hw R (le_refl 0) ν` using `by simp [low, pw, hw]`. Rewrite using `[this]`.

Conclude with `Low.hw_mem _ _`. Consider the case `succ n => exact Low.pw_mem ν _`.
-/
theorem lowestWeightMem : LowMem := by
  intro R _ k ν
  cases k with
  | zero =>
    have : low R ν = hw R (le_refl 0) ν := by simp [low, pw, hw]
    rw [this]; exact Low.hw_mem _ _
  | succ n => exact Low.pw_mem ν _

end PI.OddDualWeyl
