import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.RootAdjoin

def N (p : ℕ) : AddSubmonoid ℚ where
  carrier := {x | 0 ≤ x ∧ ∃ m n : ℕ, (p : ℚ) ^ m * x = n}
  zero_mem' := ⟨le_rfl, 0, 0, by simp⟩
  add_mem' := by
    rintro x y ⟨hx, m, n, h⟩ ⟨hy, m', n', h'⟩
    refine ⟨add_nonneg hx hy, m + m', p ^ m' * n + p ^ m * n', ?_⟩
    push_cast
    rw [← h, ← h']
    ring

abbrev Q (p d : ℕ) := Fin d → N p

variable {p : ℕ} [NeZero p]

/- English proof (translation)
The claim follows from `Nat.cast_ne_zero.2 (NeZero.ne p)`.
-/
theorem p_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne p)

noncomputable def pinv (p : ℕ) [NeZero p] (m : ℕ) : N p :=
  ⟨((p : ℚ) ^ m)⁻¹, by positivity, m, 1, by
    rw [mul_inv_cancel₀ (pow_ne_zero _ p_ne)]; simp⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pinv_coe (m : ℕ) : ((pinv p m : N p) : ℚ) = ((p : ℚ) ^ m)⁻¹ := rfl

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use `p_ne (p := p)` as an intermediate fact. Simplify using `only [AddSubmonoidClass.coe_nsmul, pinv_coe, nsmul_eq_mul, pow_succ]`. Clear the denominators using the available nonvanishing facts.
-/
theorem p_smul_pinv (m : ℕ) : p • pinv p (m + 1) = pinv p m := by
  apply Subtype.ext
  have := p_ne (p := p)
  simp only [AddSubmonoidClass.coe_nsmul, pinv_coe, nsmul_eq_mul, pow_succ]
  field_simp

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih => rw [pow_succ', pow_mul, ← add_assoc, hs, ih]`.
-/
theorem seq_pow {B : Type} [CommMonoid B] (s : ℕ → B) (hs : ∀ m, s (m + 1) ^ p = s m) (m j : ℕ) :
    s (m + j) ^ (p ^ j) = s m := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', pow_mul, ← add_assoc, hs, ih]

/- English proof (translation)
Establish `e : p ^ m' * n = p ^ m * n'`. Establish `: ((p ^ m' * n : ℕ) : ℚ) = ((p ^ m * n' : ℕ) : ℚ)`. Use `push_cast`. Rewrite using `[← h, ← h']`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `this` after adjusting the coercions. Establish `h1` using `seq_pow s hs m m'`. Establish `h2` using `seq_pow s hs m' m`. Rewrite using `[← h1, ← h2, add_comm m' m, ← pow_mul, ← pow_mul, e]`.
-/
theorem seq_eq {B : Type} [CommMonoid B] (s : ℕ → B) (hs : ∀ m, s (m + 1) ^ p = s m) {x : ℚ}
    {m n m' n' : ℕ} (h : (p : ℚ) ^ m * x = n) (h' : (p : ℚ) ^ m' * x = n') :
    s m ^ n = s m' ^ n' := by
  have e : p ^ m' * n = p ^ m * n' := by
    have : ((p ^ m' * n : ℕ) : ℚ) = ((p ^ m * n' : ℕ) : ℚ) := by
      push_cast
      rw [← h, ← h']
      ring
    exact_mod_cast this
  have h1 := seq_pow s hs m m'
  have h2 := seq_pow s hs m' m
  rw [← h1, ← h2, add_comm m' m, ← pow_mul, ← pow_mul, e]

/- English proof (translation)
Use `choose lv nm hl using fun x : N p => x.2.2`. Establish `key : ∀ (x : N p) (m n : ℕ), (p : ℚ) ^ m * (x : ℚ) = n → s (lv x) ^ nm x = s m ^ n` using `fun x m n h => seq_eq s hs (hl x) h`. Use `⟨{ toFun := fun x => s (lv x.toAdd) ^ nm x.toAdd, map_one' := ?_, map_mul' := ?_ }, ?_⟩` and prove the remaining obligations. Use `key (0 : N p) 0 0 (by simp)` as an intermediate fact. Simplify using `using this`.

Introduce `x y set a : N p := x.toAdd set b : N p := y.toAdd`. Establish `hx` using `hl a`. Establish `hy` using `hl b`. Establish `h1 : (p : ℚ) ^ (lv a + lv b) * (a : ℚ) = (p ^ lv b * nm a : ℕ)`. Use `push_cast`.

Rewrite using `[← hx]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : (p : ℚ) ^ (lv a + lv b) * (b : ℚ) = (p ^ lv a * nm b : ℕ)`. Use `push_cast`. Rewrite using `[← hy]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h3 : (p : ℚ) ^ (lv a + lv b) * ((a + b : N p) : ℚ) = (p ^ lv b * nm a + p ^ lv a * nm b : ℕ)`. Rewrite using `[AddSubmonoid.coe_add, mul_add, h1, h2]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `e : (x * y).toAdd = a + b` using `rfl`. Simplify using `only [e]`. Rewrite using `[key _ _ _ h3, key _ _ _ h1, key _ _ _ h2, pow_add]`. Introduce `x m n h`. Conclude with `key x m n h`.
-/
theorem exists_hom {B : Type} [CommMonoid B] (s : ℕ → B) (hs : ∀ m, s (m + 1) ^ p = s m) :
    ∃ Θ : Multiplicative (N p) →* B, ∀ (x : N p) (m n : ℕ), (p : ℚ) ^ m * (x : ℚ) = n →
      Θ (Multiplicative.ofAdd x) = s m ^ n := by
  choose lv nm hl using fun x : N p => x.2.2
  have key : ∀ (x : N p) (m n : ℕ), (p : ℚ) ^ m * (x : ℚ) = n → s (lv x) ^ nm x = s m ^ n :=
    fun x m n h => seq_eq s hs (hl x) h
  refine ⟨{ toFun := fun x => s (lv x.toAdd) ^ nm x.toAdd, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · have := key (0 : N p) 0 0 (by simp)
    simpa using this
  · intro x y
    set a : N p := x.toAdd
    set b : N p := y.toAdd
    have hx := hl a
    have hy := hl b
    have h1 : (p : ℚ) ^ (lv a + lv b) * (a : ℚ) = (p ^ lv b * nm a : ℕ) := by
      push_cast
      rw [← hx]
      ring
    have h2 : (p : ℚ) ^ (lv a + lv b) * (b : ℚ) = (p ^ lv a * nm b : ℕ) := by
      push_cast
      rw [← hy]
      ring
    have h3 : (p : ℚ) ^ (lv a + lv b) * ((a + b : N p) : ℚ) = (p ^ lv b * nm a + p ^ lv a * nm b : ℕ) := by
      rw [AddSubmonoid.coe_add, mul_add, h1, h2]
      push_cast
      ring
    have e : (x * y).toAdd = a + b := rfl
    simp only [e]
    rw [key _ _ _ h3, key _ _ _ h1, key _ _ _ h2, pow_add]
  · intro x m n h
    exact key x m n h

noncomputable def u {d : ℕ} (p : ℕ) [NeZero p] (k : Fin d) (m : ℕ) : Q p d := Pi.single k (pinv p m)

abbrev A (p : ℕ) (D : Type) [CommRing D] (d : ℕ) := AddMonoidAlgebra D (Q p d)

open AddMonoidAlgebra in

noncomputable def J (p : ℕ) [NeZero p] {D : Type} [CommRing D] {d : ℕ} (t : Fin d → D) : Ideal (A p D d) :=
  Ideal.span (Set.range fun k => single (u p k 0) 1 - single 0 (t k))

variable {D : Type} [CommRing D] {d : ℕ} (t : Fin d → D)

abbrev E (p : ℕ) [NeZero p] {D : Type} [CommRing D] {d : ℕ} (t : Fin d → D) := A p D d ⧸ J p t

open AddMonoidAlgebra

noncomputable def cl (a : Q p d) : E p t := Ideal.Quotient.mk (J p t) (single a 1)

/- English proof (translation)
Use `choose lv nm hl using fun k => (a k).2.2`. Use `⟨∑ k, lv k, fun k => p ^ (∑ j, lv j - lv k) * nm k, fun k => ?_⟩` and prove the remaining obligations. Establish `hle : lv k ≤ ∑ j, lv j` using `Finset.single_le_sum (f := lv) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)`. Take `⟨e, he⟩` from `Nat.exists_eq_add_of_le hle`. Use `show (p : ℚ) ^ (∑ j, lv j) * (a k : ℚ) = ((p ^ (∑ j, lv j - lv k) * nm k : ℕ) : ℚ)`.

Rewrite using `[he, Nat.add_sub_cancel_left]`. Use `push_cast`. Rewrite using `[← hl k, pow_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_common (a : Q p d) : ∃ (m : ℕ) (c : Fin d → ℕ), ∀ k, (p : ℚ) ^ m * (a k : ℚ) = c k := by
  choose lv nm hl using fun k => (a k).2.2
  refine ⟨∑ k, lv k, fun k => p ^ (∑ j, lv j - lv k) * nm k, fun k => ?_⟩
  have hle : lv k ≤ ∑ j, lv j := Finset.single_le_sum (f := lv) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hle
  show (p : ℚ) ^ (∑ j, lv j) * (a k : ℚ) = ((p ^ (∑ j, lv j - lv k) * nm k : ℕ) : ℚ)
  rw [he, Nat.add_sub_cancel_left]
  push_cast
  rw [← hl k, pow_add]
  ring

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [AddMonoidAlgebra.one_def]`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, ← ih, single_mul_single, one_mul]`.
-/
theorem single_sum_one {ι : Type} (s : Finset ι) (f : ι → Q p d) :
    (single (∑ j ∈ s, f j) (1 : D) : A p D d) = ∏ j ∈ s, single (f j) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddMonoidAlgebra.one_def]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, ← ih, single_mul_single, one_mul]

/- English proof (translation)
Rewrite using `[Finset.sum_apply, Finset.sum_eq_single k]`. Simplify using `[u]`. Introduce `j _ hj`. Simplify using `[u, Pi.single_eq_of_ne hj.symm]`. Simplify using the standard rewrite rules.
-/
theorem sum_smul_u_apply (c : Fin d → ℕ) (m : ℕ) (k : Fin d) :
    (∑ j, c j • u p j m) k = c k • pinv p m := by
  rw [Finset.sum_apply, Finset.sum_eq_single k]
  · simp [u]
  · intro j _ hj
    simp [u, Pi.single_eq_of_ne hj.symm]
  · simp

/- English proof (translation)
Use function extensionality and compare the values at `k`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `hp` using `pow_ne_zero m (p_ne (p := p))`. Rewrite using `[sum_smul_u_apply]`. Simplify using `only [AddSubmonoidClass.coe_nsmul, pinv_coe, nsmul_eq_mul]`.

Rewrite using `[← h k]`. Clear the denominators using the available nonvanishing facts.
-/
theorem eq_sum_of_common (a : Q p d) {m : ℕ} {c : Fin d → ℕ} (h : ∀ k, (p : ℚ) ^ m * (a k : ℚ) = c k) :
    a = ∑ k, c k • u p k m := by
  funext k
  apply Subtype.ext
  have hp := pow_ne_zero m (p_ne (p := p))
  rw [sum_smul_u_apply]
  simp only [AddSubmonoidClass.coe_nsmul, pinv_coe, nsmul_eq_mul]
  rw [← h k]
  field_simp

/- English proof (translation)
Rewrite using `[cl, single_sum_one, map_prod]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[cl, ← map_pow, single_pow, one_pow]`.
-/
theorem cl_sum (m : ℕ) (c : Fin d → ℕ) : cl t (∑ k, c k • u p k m) = ∏ k, cl t (u p k m) ^ c k := by
  rw [cl, single_sum_one, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [cl, ← map_pow, single_pow, one_pow]

/- English proof (translation)
Use `conv_lhs => rw [eq_sum_of_common a h]`. Conclude with `cl_sum t m c`.
-/
theorem cl_eq_prod (a : Q p d) {m : ℕ} {c : Fin d → ℕ} (h : ∀ k, (p : ℚ) ^ m * (a k : ℚ) = c k) :
    cl t a = ∏ k, cl t (u p k m) ^ c k := by
  conv_lhs => rw [eq_sum_of_common a h]
  exact cl_sum t m c

/- English proof (translation)
Rewrite using `[cl, cl, cl, ← map_mul, single_mul_single, one_mul]`.
-/
theorem cl_add (a b : Q p d) : cl t (a + b) = cl t a * cl t b := by
  rw [cl, cl, cl, ← map_mul, single_mul_single, one_mul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem algebraMap_eq (x : D) :
    algebraMap D (E p t) x = Ideal.Quotient.mk (J p t) (single 0 x) := rfl

/- English proof (translation)
Establish `: single (u p k 0) (1 : D) - single 0 (t k) ∈ J p t` using `Ideal.subset_span ⟨k, rfl⟩`. Conclude with `Ideal.Quotient.eq.2 this`.
-/
theorem cl_zero (k : Fin d) : cl t (u p k 0) = algebraMap D (E p t) (t k) := by
  have : single (u p k 0) (1 : D) - single 0 (t k) ∈ J p t := Ideal.subset_span ⟨k, rfl⟩
  exact Ideal.Quotient.eq.2 this

/- English proof (translation)
Rewrite using `[cl, ← map_pow, single_pow, one_pow, cl]`. Use `congr 2`. Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = k`. Substitute `hj` using the available equality.

Simplify using `[u, p_smul_pinv]`. Simplify using `[u, Pi.single_eq_of_ne hj]`.
-/
theorem cl_succ (k : Fin d) (m : ℕ) : cl t (u p k (m + 1)) ^ p = cl t (u p k m) := by
  rw [cl, ← map_pow, single_pow, one_pow, cl]
  congr 2
  funext j
  by_cases hj : j = k
  · subst hj; simp [u, p_smul_pinv]
  · simp [u, Pi.single_eq_of_ne hj]

abbrev I (p d : ℕ) := {a : Q p d // ∀ k, (a k : ℚ) < 1}

/- English proof (translation)
Take `⟨_, m, n, h⟩` from `x.2`. Use `⟨Int.fract_nonneg _, m, (n - p ^ m * ⌊(x : ℚ)⌋).toNat, ?_⟩` and prove the remaining obligations. Establish `hnn : 0 ≤ (n : ℤ) - p ^ m * ⌊(x : ℚ)⌋`. Establish `: (0 : ℚ) ≤ (p : ℚ) ^ m * Int.fract (x : ℚ)` using `mul_nonneg (by positivity) (Int.fract_nonneg _)`. Establish `e : (p : ℚ) ^ m * Int.fract (x : ℚ) = (((n : ℤ) - p ^ m * ⌊(x : ℚ)⌋ : ℤ) : ℚ)`.

Rewrite using `[Int.fract]`. Use `push_cast`. Rewrite using `[← h]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `this` using `[e]`.

Conclude with `this` after adjusting the coercions. Establish `e2 : (((n - p ^ m * ⌊(x : ℚ)⌋).toNat : ℕ) : ℚ) = (((n : ℤ) - p ^ m * ⌊(x : ℚ)⌋ : ℤ) : ℚ)`. Use `Int.toNat_of_nonneg hnn` as an intermediate fact. Conclude with `this` after adjusting the coercions. Rewrite using `[e2, Int.fract]`.

Use `push_cast`. Rewrite using `[← h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fract_mem (x : N p) : Int.fract (x : ℚ) ∈ N p := by
  obtain ⟨_, m, n, h⟩ := x.2
  refine ⟨Int.fract_nonneg _, m, (n - p ^ m * ⌊(x : ℚ)⌋).toNat, ?_⟩
  have hnn : 0 ≤ (n : ℤ) - p ^ m * ⌊(x : ℚ)⌋ := by
    have : (0 : ℚ) ≤ (p : ℚ) ^ m * Int.fract (x : ℚ) := mul_nonneg (by positivity) (Int.fract_nonneg _)
    have e : (p : ℚ) ^ m * Int.fract (x : ℚ) = (((n : ℤ) - p ^ m * ⌊(x : ℚ)⌋ : ℤ) : ℚ) := by
      rw [Int.fract]
      push_cast
      rw [← h]
      ring
    rw [e] at this
    exact_mod_cast this
  have e2 : (((n - p ^ m * ⌊(x : ℚ)⌋).toNat : ℕ) : ℚ) = (((n : ℤ) - p ^ m * ⌊(x : ℚ)⌋ : ℤ) : ℚ) := by
    have := Int.toNat_of_nonneg hnn
    exact_mod_cast this
  rw [e2, Int.fract]
  push_cast
  rw [← h]
  ring

noncomputable def fr (a : Q p d) : I p d :=
  ⟨fun k => ⟨Int.fract (a k : ℚ), fract_mem _⟩, fun k => Int.fract_lt_one _⟩

noncomputable def T (a : Q p d) : D := ∏ k, t k ^ ⌊(a k : ℚ)⌋₊

/- English proof (translation)
Simplify using `[u, pinv_coe]`.
-/
theorem u_zero_apply_self (k : Fin d) : ((u p k 0 k : N p) : ℚ) = 1 := by
  simp [u, pinv_coe]

/- English proof (translation)
Simplify using `[u, Pi.single_eq_of_ne h]`.
-/
theorem u_zero_apply_ne {j k : Fin d} (h : j ≠ k) : ((u p k 0 j : N p) : ℚ) = 0 := by
  simp [u, Pi.single_eq_of_ne h]

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `j`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show Int.fract (((a + u p k 0) j : N p) : ℚ) = Int.fract (a j : ℚ)`. Distinguish the cases in `h : j = k`.

Substitute `h` using the available equality. Simplify using `[u_zero_apply_self]`. Simplify using `[u_zero_apply_ne h]`.
-/
theorem fr_add (a : Q p d) (k : Fin d) : fr (a + u p k 0) = fr a := by
  apply Subtype.ext
  funext j
  apply Subtype.ext
  show Int.fract (((a + u p k 0) j : N p) : ℚ) = Int.fract (a j : ℚ)
  by_cases h : j = k
  · subst h
    simp [u_zero_apply_self]
  · simp [u_zero_apply_ne h]

/- English proof (translation)
Establish `h : ∀ j, t j ^ ⌊(((a + u p k 0) j : N p) : ℚ)⌋₊ = t j ^ ⌊(a j : ℚ)⌋₊ * (if j = k then t j else 1)`. Introduce `j`. Distinguish the cases in `hj : j = k`. Substitute `hj` using the available equality. Simplify using `only [Pi.add_apply, AddSubmonoid.coe_add, u_zero_apply_self, if_true]`.

Rewrite using `[Nat.floor_add_one (a j).2.1, pow_succ]`. Simplify using `[u_zero_apply_ne hj, hj]`. Simplify using `only [T, h, Finset.prod_mul_distrib]`. Simplify using the standard rewrite rules.
-/
theorem T_add (a : Q p d) (k : Fin d) : T t (a + u p k 0) = T t a * t k := by
  classical
  have h : ∀ j, t j ^ ⌊(((a + u p k 0) j : N p) : ℚ)⌋₊ = t j ^ ⌊(a j : ℚ)⌋₊ * (if j = k then t j else 1) := by
    intro j
    by_cases hj : j = k
    · subst hj
      simp only [Pi.add_apply, AddSubmonoid.coe_add, u_zero_apply_self, if_true]
      rw [Nat.floor_add_one (a j).2.1, pow_succ]
    · simp [u_zero_apply_ne hj, hj]
  simp only [T, h, Finset.prod_mul_distrib]
  simp

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `j`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `Int.fract_eq_self.2 ⟨(i.1 j).2.1, i.2 j⟩`.
-/
theorem fr_of_I (i : I p d) : fr i.1 = i := by
  apply Subtype.ext
  funext j
  apply Subtype.ext
  exact Int.fract_eq_self.2 ⟨(i.1 j).2.1, i.2 j⟩

/- English proof (translation)
Use `Finset.prod_eq_one fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Nat.floor_eq_zero.2 (i.2 k), pow_zero]`.
-/
theorem T_of_I (i : I p d) : T t i.1 = 1 := by
  refine Finset.prod_eq_one fun k _ => ?_
  rw [Nat.floor_eq_zero.2 (i.2 k), pow_zero]

noncomputable def φ : A p D d →+ (I p d →₀ D) :=
  (Finsupp.liftAddHom fun a => (Finsupp.singleAddHom (fr a)).comp
    (AddMonoidHom.mulRight (T t a))).comp coeffAddEquiv.toAddMonoidHom

/- English proof (translation)
Simplify using `[φ, coeffAddEquiv]`.
-/
theorem φ_single (a : Q p d) (c : D) : φ t (single a c) = Finsupp.single (fr a) (c * T t a) := by
  simp [φ, coeffAddEquiv]

/- English proof (translation)
Proceed by induction on `y using AddMonoidAlgebra.induction_linear with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => rw [add_mul, map_add, hx, hy, add_zero]`. Consider the case `single a c`. Rewrite using `[mul_sub, single_mul_single, single_mul_single, map_sub, φ_single, φ_single, fr_add, T_add, add_zero, mul_one, sub_eq_zero]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem φ_mul_gen (y : A p D d) (k : Fin d) :
    φ t (y * (single (u p k 0) 1 - single 0 (t k))) = 0 := by
  induction y using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [add_mul, map_add, hx, hy, add_zero]
  | single a c =>
    rw [mul_sub, single_mul_single, single_mul_single, map_sub, φ_single, φ_single, fr_add, T_add,
      add_zero, mul_one, sub_eq_zero]
    congr 1
    ring

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x h`. Take `⟨k, rfl⟩` from `h`. Conclude with `fun y => φ_mul_gen t y k`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => exact fun z => by rw [mul_add, map_add, hx, hy, add_zero]`. Consider the case `smul a x _ hx => exact fun y => by rw [smul_eq_mul, ← mul_assoc]; exact hx _`.
-/
theorem φ_mul_of_mem {x : A p D d} (hx : x ∈ J p t) : ∀ y, φ t (y * x) = 0 := by
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨k, rfl⟩ := h
    exact fun y => φ_mul_gen t y k
  | zero => simp
  | add x y _ _ hx hy => exact fun z => by rw [mul_add, map_add, hx, hy, add_zero]
  | smul a x _ hx => exact fun y => by rw [smul_eq_mul, ← mul_assoc]; exact hx _

/- English proof (translation)
Simplify using `using φ_mul_of_mem t hx 1`.
-/
theorem φ_of_mem {x : A p D d} (hx : x ∈ J p t) : φ t x = 0 := by
  simpa using φ_mul_of_mem t hx 1

/- English proof (translation)
Rewrite using `[Finsupp.linearCombination_apply, Finsupp.sum, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `: l i • (single i.1 (1 : D) : A p D d) = single i.1 (l i)`. Rewrite using `[smul_single', mul_one]`. Rewrite using `[← this]`.

Both sides reduce to the same expression.
-/
theorem lincomb_eq (l : I p d →₀ D) :
    Finsupp.linearCombination D (fun i : I p d => cl t i.1) l =
      Ideal.Quotient.mk (J p t) (∑ i ∈ l.support, single i.1 (l i)) := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : l i • (single i.1 (1 : D) : A p D d) = single i.1 (l i) := by
    rw [smul_single', mul_one]
  rw [← this]
  rfl

/- English proof (translation)
Rewrite using `[map_sum]`. Use `conv_rhs => rw [← Finsupp.sum_single l]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[φ_single, fr_of_I, T_of_I, mul_one]`.
-/
theorem φ_sum (l : I p d →₀ D) : φ t (∑ i ∈ l.support, single i.1 (l i)) = l := by
  rw [map_sum]
  conv_rhs => rw [← Finsupp.sum_single l]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [φ_single, fr_of_I, T_of_I, mul_one]

/- English proof (translation)
Rewrite using `[linearIndependent_iff]`. Introduce `l hl`. Rewrite `hl` using `[lincomb_eq, Ideal.Quotient.eq_zero_iff_mem]`. Rewrite using `[← φ_sum t l]`. Conclude with `φ_of_mem t hl`.
-/
theorem linInd : LinearIndependent D (fun i : I p d => cl t i.1) := by
  rw [linearIndependent_iff]
  intro l hl
  rw [lincomb_eq, Ideal.Quotient.eq_zero_iff_mem] at hl
  rw [← φ_sum t l]
  exact φ_of_mem t hl

/- English proof (translation)
Use function extensionality and compare the values at `k`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Pi.add_apply, sum_smul_u_apply]`. Simplify using `only [AddSubmonoid.coe_add, AddSubmonoidClass.coe_nsmul, pinv_coe, nsmul_eq_mul]`. Use `show (a k : ℚ) = _ + Int.fract (a k : ℚ)`.

Rewrite using `[natCast_floor_eq_intCast_floor (a k).2.1]`. Simplify using `[Int.floor_add_fract]`.
-/
theorem eq_floor_add_fr (a : Q p d) : a = ∑ k, ⌊(a k : ℚ)⌋₊ • u p k 0 + (fr a).1 := by
  funext k
  apply Subtype.ext
  rw [Pi.add_apply, sum_smul_u_apply]
  simp only [AddSubmonoid.coe_add, AddSubmonoidClass.coe_nsmul, pinv_coe, nsmul_eq_mul]
  show (a k : ℚ) = _ + Int.fract (a k : ℚ)
  rw [natCast_floor_eq_intCast_floor (a k).2.1]
  simp [Int.floor_add_fract]

/- English proof (translation)
Use `conv_lhs => rw [eq_floor_add_fr a]`. Rewrite using `[cl_add, cl_sum, Algebra.smul_def, T, map_prod]`. Use `congr 1`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[cl_zero, map_pow]`.
-/
theorem cl_eq_smul (a : Q p d) : cl t a = T t a • cl t (fr a).1 := by
  conv_lhs => rw [eq_floor_add_fr a]
  rw [cl_add, cl_sum, Algebra.smul_def, T, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [cl_zero, map_pow]

/- English proof (translation)
Establish `: c • (single a (1 : D) : A p D d) = single a c` using `by rw [smul_single', mul_one]`. Rewrite using `[← this]`. Both sides reduce to the same expression.
-/
theorem mk_single (a : Q p d) (c : D) :
    Ideal.Quotient.mk (J p t) (single a c) = c • cl t a := by
  have : c • (single a (1 : D) : A p D d) = single a c := by rw [smul_single', mul_one]
  rw [← this]
  rfl

/- English proof (translation)
Introduce and unpack `x -`. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Proceed by induction on `y using AddMonoidAlgebra.induction_linear with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => rw [map_add]`.

Conclude with `Submodule.add_mem _ hx hy`. Consider the case `single a c`. Rewrite using `[mk_single, cl_eq_smul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨fr a, rfl⟩))`.
-/
theorem spanning : ⊤ ≤ Submodule.span D (Set.range fun i : I p d => cl t i.1) := by
  rintro x -
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction y using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | single a c =>
    rw [mk_single, cl_eq_smul]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨fr a, rfl⟩))

/- English proof (translation)
Apply `Ideal.Quotient.ringHom_ext` to reduce the goal to its premises. Apply `AddMonoidAlgebra.ringHom_ext` to reduce the goal to its premises. Conclude with `h₁`. Introduce `a`. Take `⟨m, c, h⟩` from `exists_common a`.

Use `show g₁ (cl t a) = g₂ (cl t a)`. Rewrite using `[cl_eq_prod t a h, map_prod, map_prod]`. Conclude with `Finset.prod_congr rfl fun k _ => by rw [map_pow, map_pow, h₂]`.
-/
theorem hom_ext {B : Type} [CommRing B] {g₁ g₂ : E p t →+* B}
    (h₁ : ∀ x, g₁ (algebraMap D (E p t) x) = g₂ (algebraMap D (E p t) x))
    (h₂ : ∀ k m, g₁ (cl t (u p k m)) = g₂ (cl t (u p k m))) : g₁ = g₂ := by
  apply Ideal.Quotient.ringHom_ext
  apply AddMonoidAlgebra.ringHom_ext
  · exact h₁
  · intro a
    obtain ⟨m, c, h⟩ := exists_common a
    show g₁ (cl t a) = g₂ (cl t a)
    rw [cl_eq_prod t a h, map_prod, map_prod]
    exact Finset.prod_congr rfl fun k _ => by rw [map_pow, map_pow, h₂]

/- English proof (translation)
Use `choose Θ hΘ using fun k => exists_hom (c k) (hs k)`. Set `θ : Multiplicative (Q p d) →* B` to `{ toFun := fun a => ∏ k, Θ k (Multiplicative.ofAdd (a.toAdd k)) map_one' := Finset.prod_eq_one fun k _ => map_one _ map_mul' := fun x y => by`. Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun k _ => map_mul _ _ _ }`. Establish `hθ : ∀ k m, θ (Multiplicative.ofAdd (u p k m)) = c k m`.

Introduce `k m`. Use `show ∏ j, Θ j (Multiplicative.ofAdd (u p k m j)) = c k m`. Rewrite using `[Finset.prod_eq_single k]`. Use `hΘ k (pinv p m) m 1 (by` as an intermediate fact. Rewrite using `[pinv_coe, mul_inv_cancel₀ (pow_ne_zero _ p_ne)]`.

Use the proof step `simp)`. Simplify `this` using `[u]`. Introduce `j _ hj`. Establish `: u p k m j = 0` using `by simp [u, Pi.single_eq_of_ne hj]`. Rewrite using `[this]`.

Conclude with `map_one _`. Simplify using the standard rewrite rules. Set `g₀ : A p D d →+* B` to `liftNCRingHom f θ fun _ _ => Commute.all _ _`. Establish `hg₀ : ∀ a x, g₀ (single a x) = f x * θ (Multiplicative.ofAdd a)` using `fun a x => liftNC_single _ _ _ _`. Establish `hk : ∀ x ∈ J p t, g₀ x = 0`.

Establish `: J p t ≤ RingHom.ker g₀`. Use `Ideal.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Use `show g₀ _ = 0`. Rewrite using `[map_sub, hg₀, hg₀, hθ, h0, map_one, one_mul]`.

Establish `: θ (Multiplicative.ofAdd 0) = 1` using `map_one θ`. Rewrite using `[this, mul_one, sub_self]`. Conclude with `fun x hx => this hx`. Set `g : E p t →+* B` to `Ideal.Quotient.lift (J p t) g₀ hk`. Establish `hgA : ∀ x, g (algebraMap D (E p t) x) = f x`.

Introduce `x`. Rewrite using `[algebraMap_eq]`. Use `show g₀ _ = _`. Rewrite using `[hg₀]`. Establish `: θ (Multiplicative.ofAdd 0) = 1` using `map_one θ`.

Rewrite using `[this, mul_one]`. Establish `hgr : ∀ k m, g (cl t (u p k m)) = c k m`. Introduce `k m`. Use `show g₀ _ = _`. Rewrite using `[hg₀, hθ, map_one, one_mul]`.

Use `⟨g, ⟨RingHom.ext hgA, hgr⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `g' ⟨h1, h2⟩`. Use `hom_ext t (fun x => ?_) (fun k m => ?_)` and prove the remaining obligations. Rewrite using `[hgA, ← h1]`. Both sides reduce to the same expression.

Rewrite using `[h2, hgr]`.
-/
theorem exists_lift (B : Type) [CommRing B] (f : D →+* B) (c : Fin d → ℕ → B)
    (h0 : ∀ k, c k 0 = f (t k)) (hs : ∀ k m, c k (m + 1) ^ p = c k m) :
    ∃! g : E p t →+* B, g.comp (algebraMap D (E p t)) = f ∧ ∀ k m, g (cl t (u p k m)) = c k m := by
  classical
  choose Θ hΘ using fun k => exists_hom (c k) (hs k)
  let θ : Multiplicative (Q p d) →* B :=
    { toFun := fun a => ∏ k, Θ k (Multiplicative.ofAdd (a.toAdd k))
      map_one' := Finset.prod_eq_one fun k _ => map_one _
      map_mul' := fun x y => by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun k _ => map_mul _ _ _ }
  have hθ : ∀ k m, θ (Multiplicative.ofAdd (u p k m)) = c k m := by
    intro k m
    show ∏ j, Θ j (Multiplicative.ofAdd (u p k m j)) = c k m
    rw [Finset.prod_eq_single k]
    · have := hΘ k (pinv p m) m 1 (by
        rw [pinv_coe, mul_inv_cancel₀ (pow_ne_zero _ p_ne)]; simp)
      simpa [u] using this
    · intro j _ hj
      have : u p k m j = 0 := by simp [u, Pi.single_eq_of_ne hj]
      rw [this]
      exact map_one _
    · simp
  let g₀ : A p D d →+* B := liftNCRingHom f θ fun _ _ => Commute.all _ _
  have hg₀ : ∀ a x, g₀ (single a x) = f x * θ (Multiplicative.ofAdd a) := fun a x =>
    liftNC_single _ _ _ _
  have hk : ∀ x ∈ J p t, g₀ x = 0 := by
    have : J p t ≤ RingHom.ker g₀ := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨k, rfl⟩
      show g₀ _ = 0
      rw [map_sub, hg₀, hg₀, hθ, h0, map_one, one_mul]
      have : θ (Multiplicative.ofAdd 0) = 1 := map_one θ
      rw [this, mul_one, sub_self]
    exact fun x hx => this hx
  let g : E p t →+* B := Ideal.Quotient.lift (J p t) g₀ hk
  have hgA : ∀ x, g (algebraMap D (E p t) x) = f x := by
    intro x
    rw [algebraMap_eq]
    show g₀ _ = _
    rw [hg₀]
    have : θ (Multiplicative.ofAdd 0) = 1 := map_one θ
    rw [this, mul_one]
  have hgr : ∀ k m, g (cl t (u p k m)) = c k m := by
    intro k m
    show g₀ _ = _
    rw [hg₀, hθ, map_one, one_mul]
  refine ⟨g, ⟨RingHom.ext hgA, hgr⟩, ?_⟩
  rintro g' ⟨h1, h2⟩
  refine hom_ext t (fun x => ?_) (fun k m => ?_)
  · rw [hgA, ← h1]
    rfl
  · rw [h2, hgr]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cl_zero_one : cl t (0 : Q p d) = 1 := rfl

/- English proof (translation)
Establish `: ∃ k, (a.1 k : ℚ) ≠ 0`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `ha (Subtype.ext (funext fun k => Subtype.ext (hc k)))`. Take `⟨k, hk⟩` from `this`.

Use `⟨k, ?_⟩` and prove the remaining obligations. Establish `hp : (0 : ℚ) < (p : ℚ) ^ m` using `pow_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne p))) m`. Establish `hpos : (0 : ℚ) < (a.1 k : ℚ)` using `lt_of_le_of_ne (a.1 k).2.1 hk.symm`. Establish `h1 : (0 : ℚ) < c k` using `by rw [← h k]; exact mul_pos hp hpos`. Establish `h2 : (c k : ℚ) < (p : ℚ) ^ m`.

Rewrite using `[← h k]`. Conclude with `mul_lt_of_lt_one_right hp (a.2 k)`. Conclude with `Nat.not_dvd_of_pos_of_lt (by exact_mod_cast h1) (by exact_mod_cast h2)`.
-/
theorem exists_not_dvd (a : I p d) (ha : a ≠ ⟨0, fun k => by simp⟩) {m : ℕ} {c : Fin d → ℕ}
    (h : ∀ k, (p : ℚ) ^ m * (a.1 k : ℚ) = c k) : ∃ k, ¬ p ^ m ∣ c k := by
  have : ∃ k, (a.1 k : ℚ) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact ha (Subtype.ext (funext fun k => Subtype.ext (hc k)))
  obtain ⟨k, hk⟩ := this
  refine ⟨k, ?_⟩
  have hp : (0 : ℚ) < (p : ℚ) ^ m :=
    pow_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne p))) m
  have hpos : (0 : ℚ) < (a.1 k : ℚ) := lt_of_le_of_ne (a.1 k).2.1 hk.symm
  have h1 : (0 : ℚ) < c k := by rw [← h k]; exact mul_pos hp hpos
  have h2 : (c k : ℚ) < (p : ℚ) ^ m := by
    rw [← h k]
    exact mul_lt_of_lt_one_right hp (a.2 k)
  exact Nat.not_dvd_of_pos_of_lt (by exact_mod_cast h1) (by exact_mod_cast h2)

noncomputable def rootExt : RootExt p D t where
  E := E p t
  r k m := cl t (u p k m)
  r_zero := cl_zero t
  r_succ := cl_succ t
  univ B _ f c h0 hs := exists_lift t B f c h0 hs
  ι := I p d
  b := Module.Basis.mk (linInd t) (spanning t)
  a₀ := ⟨0, fun k => by simp⟩
  b_a₀ := by
    rw [Module.Basis.mk_apply]
    exact cl_zero_one t
  mono a ha := by
    obtain ⟨m, c, h⟩ := exists_common a.1
    refine ⟨m, c, ?_, exists_not_dvd a ha h⟩
    rw [Module.Basis.mk_apply]
    exact cl_eq_prod t a.1 h

/- English proof (translation)
Introduce `p hp D _ d t`. Use `haveI : NeZero p := ⟨hp.ne_zero⟩`. Conclude with `⟨rootExt t⟩`.
-/
theorem nonempty_rootExt : ∀ (p : ℕ), p.Prime → ∀ (D : Type) [CommRing D] {d : ℕ} (t : Fin d → D),
    Nonempty (RootExt p D t) := by
  intro p hp D _ d t
  haveI : NeZero p := ⟨hp.ne_zero⟩
  exact ⟨rootExt t⟩

end GlobalTheory.CompanionTheory.RootAdjoin
