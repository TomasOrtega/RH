import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.CellBlock

noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW.CellW

open NumberField Formalism.MainNotions.S Matrix

variable {E : Type} [Field E] [NumberField E]

def pm (L : List (E × ℕ)) : Matrix (Fin (L.map Prod.snd).sum) (Fin (L.map Prod.snd).sum) E :=
  fun a b => ptEntry L a.val b.val

/- English proof (translation)
Use extensionality with `(i | i) (j | j)`. Apply the tactic sequence `show ptEntry ((t, s) :: bs) (i : ℕ) (j : ℕ) = t * (if j = Fin.rev i then (1 : E) else 0)`. Simplify using `only [ptEntry]`. Rewrite using `[if_pos ⟨i.isLt, j.isLt⟩]`. Establish `hiff : ((i : ℕ) + (j : ℕ) + 1 = s) ↔ j = Fin.rev i`.

Rewrite using `[Fin.ext_iff, Fin.val_rev]`. Use linear arithmetic over natural numbers and integers. Distinguish the cases in `h : j = Fin.rev i`. Rewrite using `[if_pos (hiff.mpr h), if_pos h, mul_one]`. Rewrite using `[if_neg (fun h' => h (hiff.mp h')), if_neg h, mul_zero]`.

Apply the tactic sequence `show ptEntry ((t, s) :: bs) (i : ℕ) (s + (j : ℕ)) = 0`. Use `i.isLt` as an intermediate fact. Simplify using `only [ptEntry]`. Rewrite using `[if_neg (by omega), if_neg (by omega)]`. Apply the tactic sequence `show ptEntry ((t, s) :: bs) (s + (i : ℕ)) (j : ℕ) = 0`.

Use `j.isLt` as an intermediate fact. Simplify using `only [ptEntry]`. Rewrite using `[if_neg (by omega), if_neg (by omega)]`. Apply the tactic sequence `show ptEntry ((t, s) :: bs) (s + (i : ℕ)) (s + (j : ℕ)) = ptEntry bs (i : ℕ) (j : ℕ)`. Simplify using `only [ptEntry]`.

Rewrite using `[if_neg (by omega), if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]`.
-/
theorem pm_cons (t : E) (s : ℕ) (bs : List (E × ℕ)) :
    (pm ((t, s) :: bs) : Matrix (Fin (s + (bs.map Prod.snd).sum)) (Fin (s + (bs.map Prod.snd).sum)) E).submatrix
      finSumFinEquiv finSumFinEquiv = fromBlocks (t • revJ E s) 0 0 (pm bs) := by
  ext (i | i) (j | j)
  · show ptEntry ((t, s) :: bs) (i : ℕ) (j : ℕ) = t * (if j = Fin.rev i then (1 : E) else 0)
    simp only [ptEntry]
    rw [if_pos ⟨i.isLt, j.isLt⟩]
    have hiff : ((i : ℕ) + (j : ℕ) + 1 = s) ↔ j = Fin.rev i := by
      rw [Fin.ext_iff, Fin.val_rev]; omega
    by_cases h : j = Fin.rev i
    · rw [if_pos (hiff.mpr h), if_pos h, mul_one]
    · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h, mul_zero]
  · show ptEntry ((t, s) :: bs) (i : ℕ) (s + (j : ℕ)) = 0
    have := i.isLt
    simp only [ptEntry]
    rw [if_neg (by omega), if_neg (by omega)]
  · show ptEntry ((t, s) :: bs) (s + (i : ℕ)) (j : ℕ) = 0
    have := j.isLt
    simp only [ptEntry]
    rw [if_neg (by omega), if_neg (by omega)]
  · show ptEntry ((t, s) :: bs) (s + (i : ℕ)) (s + (j : ℕ)) = ptEntry bs (i : ℕ) (j : ℕ)
    simp only [ptEntry]
    rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]

/- English proof (translation)
The claim follows from `| [], _ => by intro d _ refine ⟨1, one_ne_zero, ?_⟩ rintro Z _ ⟨L0, U0, hL0, hU0, hZ⟩ exact ⟨L0, U0, hL0, hU0, hZ, ⟨0, by ext i; exact absurd i.isLt (by simp)⟩, ⟨0, by ext i; exact absurd i.isLt (by simp)⟩⟩ | (t, s) :: bs, h => by have ht : t ≠ 0 := (h (t, s) List.mem_cons_self). …`.
-/
theorem bd_all : ∀ L : List (E × ℕ), (∀ b ∈ L, b.1 ≠ 0 ∧ 1 ≤ b.2) → BDm (pm L)
  | [], _ => by
    intro d _
    refine ⟨1, one_ne_zero, ?_⟩
    rintro Z _ ⟨L0, U0, hL0, hU0, hZ⟩
    exact ⟨L0, U0, hL0, hU0, hZ, ⟨0, by ext i; exact absurd i.isLt (by simp)⟩,
      ⟨0, by ext i; exact absurd i.isLt (by simp)⟩⟩
  | (t, s) :: bs, h => by
    have ht : t ≠ 0 := (h (t, s) List.mem_cons_self).1
    have ih := bd_all bs (fun b hb => h b (List.mem_cons_of_mem _ hb))
    exact bd_step t ht (pm bs) (pm ((t, s) :: bs)) (pm_cons t s bs) ih

/- English proof (translation)
Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem map_smul' {m n : Type*} (c : 𝓞 E) (X : Matrix m n (𝓞 E)) :
    (c • X).map (algebraMap (𝓞 E) E) = algebraMap (𝓞 E) E c • X.map (algebraMap (𝓞 E) E) := by
  ext i j; simp

/- English proof (translation)
The claim follows from `IsFractionRing.injective (𝓞 E) E h`.
-/
theorem alg_inj {x y : 𝓞 E} (h : algebraMap (𝓞 E) E x = algebraMap (𝓞 E) E y) : x = y :=
  IsFractionRing.injective (𝓞 E) E h

/- English proof (translation)
Establish `hmap : (1 + b • Y).map (fun x => (x : E)) = A`. Use extensionality with `i j`. Use `congrFun (congrFun h i) j` as an intermediate fact. Simplify using `only [Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at this`. Use `show algebraMap (𝓞 E) E ((1 + b • Y) i j) = A i j`.

Rewrite using `[Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Rewrite `this`, the goal using `[Matrix.one_apply_eq]`. Rewrite using `[map_one]`.

Take the linear combination `-this`. Rewrite `this`, the goal using `[Matrix.one_apply_ne hij]`. Rewrite using `[map_zero, zero_add, ← this, sub_zero]`. Use `⟨1 + b • Y, ?_, hmap⟩` and prove the remaining obligations. Introduce `i j`.

Establish `hij` using `congrFun (congrFun hmap i) j`. Simplify using `only [Matrix.map_apply] at hij`. Use `⟨fun h' => alg_inj (by rw [map_zero]; exact hij.trans ((hA i j).1 h')), fun h' => ?_, fun h' => ?_⟩` and prove the remaining obligations. Conclude with `alg_inj (by rw [map_one]; exact hij.trans ((hA i j).2 h'))`. Use `⟨Y i j, ?_⟩` and prove the remaining obligations.

Simplify using `[Matrix.one_apply_ne (ne_of_gt h')]`.
-/
theorem lob_of {N : ℕ} {b : 𝓞 E} {A : Matrix (Fin N) (Fin N) E} (hA : IsLoUni A)
    (Y : Matrix (Fin N) (Fin N) (𝓞 E)) (h : A - 1 = algebraMap (𝓞 E) E b • Y.map (algebraMap (𝓞 E) E)) :
    ∃ A' : Matrix (Fin N) (Fin N) (𝓞 E), LoB b A' ∧ A'.map (fun x => (x : E)) = A := by
  have hmap : (1 + b • Y).map (fun x => (x : E)) = A := by
    ext i j
    have := congrFun (congrFun h i) j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at this
    show algebraMap (𝓞 E) E ((1 + b • Y) i j) = A i j
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq] at this ⊢
      rw [map_one]; linear_combination -this
    · rw [Matrix.one_apply_ne hij] at this ⊢
      rw [map_zero, zero_add, ← this, sub_zero]
  refine ⟨1 + b • Y, ?_, hmap⟩
  intro i j
  have hij := congrFun (congrFun hmap i) j
  simp only [Matrix.map_apply] at hij
  refine ⟨fun h' => alg_inj (by rw [map_zero]; exact hij.trans ((hA i j).1 h')), fun h' => ?_, fun h' => ?_⟩
  · exact alg_inj (by rw [map_one]; exact hij.trans ((hA i j).2 h'))
  · refine ⟨Y i j, ?_⟩
    simp [Matrix.one_apply_ne (ne_of_gt h')]

/- English proof (translation)
Establish `hmap : (1 + b • Y).map (fun x => (x : E)) = A`. Use extensionality with `i j`. Use `congrFun (congrFun h i) j` as an intermediate fact. Simplify using `only [Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at this`. Use `show algebraMap (𝓞 E) E ((1 + b • Y) i j) = A i j`.

Rewrite using `[Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Rewrite `this`, the goal using `[Matrix.one_apply_eq]`. Rewrite using `[map_one]`.

Take the linear combination `-this`. Rewrite `this`, the goal using `[Matrix.one_apply_ne hij]`. Rewrite using `[map_zero, zero_add, ← this, sub_zero]`. Use `⟨1 + b • Y, ?_, hmap⟩` and prove the remaining obligations. Introduce `i j`.

Establish `hij` using `congrFun (congrFun hmap i) j`. Simplify using `only [Matrix.map_apply] at hij`. Use `⟨fun h' => alg_inj (by rw [map_zero]; exact hij.trans ((hA i j).1 h')), fun h' => ?_, fun h' => ?_⟩` and prove the remaining obligations. Conclude with `alg_inj (by rw [map_one]; exact hij.trans ((hA i j).2 h'))`. Use `⟨Y i j, ?_⟩` and prove the remaining obligations.

Simplify using `[Matrix.one_apply_ne (ne_of_lt h')]`.
-/
theorem upb_of {N : ℕ} {b : 𝓞 E} {A : Matrix (Fin N) (Fin N) E} (hA : IsUpUni A)
    (Y : Matrix (Fin N) (Fin N) (𝓞 E)) (h : A - 1 = algebraMap (𝓞 E) E b • Y.map (algebraMap (𝓞 E) E)) :
    ∃ A' : Matrix (Fin N) (Fin N) (𝓞 E), UpB b A' ∧ A'.map (fun x => (x : E)) = A := by
  have hmap : (1 + b • Y).map (fun x => (x : E)) = A := by
    ext i j
    have := congrFun (congrFun h i) j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at this
    show algebraMap (𝓞 E) E ((1 + b • Y) i j) = A i j
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq] at this ⊢
      rw [map_one]; linear_combination -this
    · rw [Matrix.one_apply_ne hij] at this ⊢
      rw [map_zero, zero_add, ← this, sub_zero]
  refine ⟨1 + b • Y, ?_, hmap⟩
  intro i j
  have hij := congrFun (congrFun hmap i) j
  simp only [Matrix.map_apply] at hij
  refine ⟨fun h' => alg_inj (by rw [map_zero]; exact hij.trans ((hA i j).1 h')), fun h' => ?_, fun h' => ?_⟩
  · exact alg_inj (by rw [map_one]; exact hij.trans ((hA i j).2 h'))
  · refine ⟨Y i j, ?_⟩
    simp [Matrix.one_apply_ne (ne_of_lt h')]

/- English proof (translation)
Establish `hpow : D ^ N = D ^ (N - (N - 1)) * D ^ (N - 1)` using `by rw [← pow_add]; congr 1; omega`. Take `⟨AL, hAL⟩` from `intg_adj hLxi`. Take `⟨AU, hAU⟩` from `intg_adj hUxi`. Establish `hA1 : Ly * Lx.adjugate - 1 = algebraMap (𝓞 E) E b • ((D ^ (N - (N - 1)) • (ML * AL)).map (algebraMap (𝓞 E) E))`. Rewrite using `[← lo_mul_adj hLx, ← Matrix.sub_mul, hL, map_smul', Matrix.map_mul, hAL, hpow]`.

Simplify using `only [map_mul, map_pow, Matrix.smul_mul, Matrix.mul_smul, smul_smul]`. Put the polynomial expressions in normal form. Establish `hB1 : Ux.adjugate * Uy - 1 = algebraMap (𝓞 E) E b • ((D ^ (N - (N - 1)) • (AU * MU)).map (algebraMap (𝓞 E) E))`. Rewrite using `[← up_adj_mul hUx, ← Matrix.mul_sub, hU, map_smul', Matrix.map_mul, hAU, hpow]`. Simplify using `only [map_mul, map_pow, Matrix.smul_mul, Matrix.mul_smul, smul_smul]`.

Put the polynomial expressions in normal form. Take `⟨A, hA, hAm⟩` from `lob_of (lo_mul hLy (lo_adj hLx)) _ hA1`. Take `⟨B, hB, hBm⟩` from `upb_of (up_mul (up_adj hUx) hUy) _ hB1`. Use `⟨A, B, hA, hB, ?_⟩` and prove the remaining obligations. Rewrite using `[hAm, hBm]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem close_rel {N : ℕ} {D b : 𝓞 E} (W : Matrix (Fin N) (Fin N) E)
    {Lx Ux Ly Uy : Matrix (Fin N) (Fin N) E} (hLx : IsLoUni Lx) (hUx : IsUpUni Ux) (hLy : IsLoUni Ly)
    (hUy : IsUpUni Uy) (hLxi : Intg D Lx) (hUxi : Intg D Ux)
    (ML MU : Matrix (Fin N) (Fin N) (𝓞 E))
    (hL : Ly - Lx = algebraMap (𝓞 E) E (D ^ N * b) • ML.map (algebraMap (𝓞 E) E))
    (hU : Uy - Ux = algebraMap (𝓞 E) E (D ^ N * b) • MU.map (algebraMap (𝓞 E) E)) :
    ∃ A B : Matrix (Fin N) (Fin N) (𝓞 E), LoB b A ∧ UpB b B ∧
      A.map (fun x => (x : E)) * (Lx * W * Ux) * B.map (fun x => (x : E)) = Ly * W * Uy := by
  have hpow : D ^ N = D ^ (N - (N - 1)) * D ^ (N - 1) := by rw [← pow_add]; congr 1; omega
  obtain ⟨AL, hAL⟩ := intg_adj hLxi
  obtain ⟨AU, hAU⟩ := intg_adj hUxi
  have hA1 : Ly * Lx.adjugate - 1 =
      algebraMap (𝓞 E) E b • ((D ^ (N - (N - 1)) • (ML * AL)).map (algebraMap (𝓞 E) E)) := by
    rw [← lo_mul_adj hLx, ← Matrix.sub_mul, hL, map_smul', Matrix.map_mul, hAL, hpow]
    simp only [map_mul, map_pow, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    ring_nf
  have hB1 : Ux.adjugate * Uy - 1 =
      algebraMap (𝓞 E) E b • ((D ^ (N - (N - 1)) • (AU * MU)).map (algebraMap (𝓞 E) E)) := by
    rw [← up_adj_mul hUx, ← Matrix.mul_sub, hU, map_smul', Matrix.map_mul, hAU, hpow]
    simp only [map_mul, map_pow, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    ring_nf
  obtain ⟨A, hA, hAm⟩ := lob_of (lo_mul hLy (lo_adj hLx)) _ hA1
  obtain ⟨B, hB, hBm⟩ := upb_of (up_mul (up_adj hUx) hUy) _ hB1
  refine ⟨A, B, hA, hB, ?_⟩
  rw [hAm, hBm]
  calc Ly * Lx.adjugate * (Lx * W * Ux) * (Ux.adjugate * Uy)
      = Ly * (Lx.adjugate * Lx) * W * (Ux * Ux.adjugate) * Uy := by simp only [Matrix.mul_assoc]
    _ = Ly * W * Uy := by rw [lo_adj_mul hLx, up_mul_adj hUx, Matrix.mul_one, Matrix.mul_one]

end PI.TermsAtPtFiniteW.CellW

namespace PI.TermsAtPtFiniteW

open NumberField Formalism.MainNotions.S CellW

/- English proof (translation)
Introduce `E _ _ N p b hb`. Take `⟨L, hL, hsum⟩` from `p`. Substitute `hsum` using the available equality. Take `⟨D, hD, hbd⟩` from `bd_all L hL 1 one_ne_zero`. Set `X : Set (Matrix (Fin (L.map Prod.snd).sum) (Fin (L.map Prod.snd).sum) E × Matrix (Fin (L.map Prod.snd).sum) (Fin (L.map Prod.snd).sum) E × Matrix (Fin (L.map Prod.snd).sum) (Fin (L.map Prod.snd).sum) E)` to `{x | IsLoUni x.2.1 ∧ IsUpUni x.2.2 ∧ x.1 = x.2.1 * pm L * x.2.2 ∧ Intg D x.2.1 ∧ Intg D x.2.2}`.

Set `f : (Matrix (Fin (L.map Prod.snd).sum) (Fin (L.map Prod.snd).sum) E × Matrix (Fin (L.map Prod.snd).sum) (Fin (L.map Prod.snd).sum) E × Matrix (Fin (L.map Prod.snd).sum) (Fin (L.map Prod.snd).sum) E) → Bool × Fin (L.map Prod.snd).sum × Fin (L.map Prod.snd).sum → E` to `fun x k => if k.1 then algebraMap (𝓞 E) E D * x.2.2 k.2.1 k.2.2 else algebraMap (𝓞 E) E D * x.2.1 k.2.1 k.2.2`. Establish `hf : ∀ x ∈ X, ∀ k, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = f x k`. Introduce and unpack `x ⟨-, -, -, ⟨L', hL'⟩, ⟨U', hU'⟩⟩ ⟨c, i, j⟩`. Consider the cases of `c`. Conclude with `⟨L' i j, by simpa [f] using congrFun (congrFun hL' i) j⟩`.

Conclude with `⟨U' i j, by simpa [f] using congrFun (congrFun hU' i) j⟩`. Establish `hc : D ^ (L.map Prod.snd).sum * D * b ≠ 0` using `mul_ne_zero (mul_ne_zero (pow_ne_zero _ hD) hD) hb`. Take `⟨Zs, hfin, hZs⟩` from `fin_of_cong X f hf _ hc (fun x y => ∃ A B : Matrix (Fin (L.map Prod.snd).sum) (Fin (L.map Prod.snd).sum) (𝓞 E), LoB b A ∧ UpB b B ∧ A.map (fun x => (x : E)) * x.1 * B.map (fun x => (x : E)) = y.1) (by`. Introduce and unpack `x ⟨hLx, hUx, hx, hLxi, hUxi⟩ y ⟨hLy, hUy, hy, -, -⟩ hxy`. Establish `hDE` using `alg_ne_zero hD`.

Establish `hM : ∀ c : Bool, ∃ M : Matrix (Fin (L.map Prod.snd).sum) (Fin (L.map Prod.snd).sum) (𝓞 E), ∀ i j, algebraMap (𝓞 E) E D * algebraMap (𝓞 E) E (D ^ (L.map Prod.snd).sum * b) * algebraMap (𝓞 E) E (M i j) = f y (c, i, j) - f x (c, i, j)`. Introduce `c`. Use `⟨fun i j => Classical.choose (hxy (c, i, j)), fun i j => ?_⟩` and prove the remaining obligations. Rewrite using `[← Classical.choose_spec (hxy (c, i, j))]`. Simplify using `only [map_mul, map_pow]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨ML, hML⟩` from `hM false`. Take `⟨MU, hMU⟩` from `hM true`. Establish `hL : y.2.1 - x.2.1 = algebraMap (𝓞 E) E (D ^ (L.map Prod.snd).sum * b) • ML.map (algebraMap (𝓞 E) E)`. Use extensionality with `i j`.

Use `hML i j` as an intermediate fact. Simplify using `only [f, Bool.false_eq_true, if_false] at this`. Simplify using `only [Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]`. Apply `mul_left_cancel₀ hDE` to reduce the goal to its premises. Rewrite using `[mul_sub, ← this]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hU : y.2.2 - x.2.2 = algebraMap (𝓞 E) E (D ^ (L.map Prod.snd).sum * b) • MU.map (algebraMap (𝓞 E) E)`. Use extensionality with `i j`. Use `hMU i j` as an intermediate fact. Simplify using `only [f, if_true] at this`.

Simplify using `only [Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]`. Apply `mul_left_cancel₀ hDE` to reduce the goal to its premises. Rewrite using `[mul_sub, ← this]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨A, B, hA, hB, hAB⟩` from `close_rel (pm L) hLx hUx hLy hUy hLxi hUxi ML MU hL hU`.

Conclude with `⟨A, B, hA, hB, by rw [hx, hy]; exact hAB⟩)`. Use `⟨Prod.fst '' Zs, hfin.image _, ?_⟩` and prove the remaining obligations. Introduce `Z hZ hcell`. Take `⟨L1, U1, hL1, hU1, hZe, hL1i, hU1i⟩` from `hbd Z (intg_of_entries hZ) hcell`. Take `⟨y, hy, A, B, hA, hB, hAB⟩` from `hZs (Z, L1, U1) ⟨hL1, hU1, hZe, hL1i, hU1i⟩`.

Conclude with `⟨A, B, hA, hB, ⟨y, hy, hAB.symm⟩⟩`.
-/
theorem cellReduce_holds : CellReduce := by
  intro E _ _ N p b hb
  obtain ⟨L, hL, hsum⟩ := p
  subst hsum
  obtain ⟨D, hD, hbd⟩ := bd_all L hL 1 one_ne_zero
  let X : Set (Matrix (Fin (L.map Prod.snd).sum) (Fin (L.map Prod.snd).sum) E ×
      Matrix (Fin (L.map Prod.snd).sum) (Fin (L.map Prod.snd).sum) E ×
      Matrix (Fin (L.map Prod.snd).sum) (Fin (L.map Prod.snd).sum) E) :=
    {x | IsLoUni x.2.1 ∧ IsUpUni x.2.2 ∧ x.1 = x.2.1 * pm L * x.2.2 ∧ Intg D x.2.1 ∧ Intg D x.2.2}
  let f : (Matrix (Fin (L.map Prod.snd).sum) (Fin (L.map Prod.snd).sum) E ×
      Matrix (Fin (L.map Prod.snd).sum) (Fin (L.map Prod.snd).sum) E ×
      Matrix (Fin (L.map Prod.snd).sum) (Fin (L.map Prod.snd).sum) E) →
      Bool × Fin (L.map Prod.snd).sum × Fin (L.map Prod.snd).sum → E := fun x k =>
    if k.1 then algebraMap (𝓞 E) E D * x.2.2 k.2.1 k.2.2 else algebraMap (𝓞 E) E D * x.2.1 k.2.1 k.2.2
  have hf : ∀ x ∈ X, ∀ k, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = f x k := by
    rintro x ⟨-, -, -, ⟨L', hL'⟩, ⟨U', hU'⟩⟩ ⟨c, i, j⟩
    cases c
    · exact ⟨L' i j, by simpa [f] using congrFun (congrFun hL' i) j⟩
    · exact ⟨U' i j, by simpa [f] using congrFun (congrFun hU' i) j⟩
  have hc : D ^ (L.map Prod.snd).sum * D * b ≠ 0 := mul_ne_zero (mul_ne_zero (pow_ne_zero _ hD) hD) hb
  obtain ⟨Zs, hfin, hZs⟩ := fin_of_cong X f hf _ hc
    (fun x y => ∃ A B : Matrix (Fin (L.map Prod.snd).sum) (Fin (L.map Prod.snd).sum) (𝓞 E), LoB b A ∧ UpB b B ∧
      A.map (fun x => (x : E)) * x.1 * B.map (fun x => (x : E)) = y.1) (by
    rintro x ⟨hLx, hUx, hx, hLxi, hUxi⟩ y ⟨hLy, hUy, hy, -, -⟩ hxy
    have hDE := alg_ne_zero hD
    have hM : ∀ c : Bool, ∃ M : Matrix (Fin (L.map Prod.snd).sum) (Fin (L.map Prod.snd).sum) (𝓞 E),
        ∀ i j, algebraMap (𝓞 E) E D * algebraMap (𝓞 E) E (D ^ (L.map Prod.snd).sum * b) *
          algebraMap (𝓞 E) E (M i j) = f y (c, i, j) - f x (c, i, j) := by
      intro c
      refine ⟨fun i j => Classical.choose (hxy (c, i, j)), fun i j => ?_⟩
      rw [← Classical.choose_spec (hxy (c, i, j))]
      simp only [map_mul, map_pow]; ring
    obtain ⟨ML, hML⟩ := hM false
    obtain ⟨MU, hMU⟩ := hM true
    have hL : y.2.1 - x.2.1 = algebraMap (𝓞 E) E (D ^ (L.map Prod.snd).sum * b) • ML.map (algebraMap (𝓞 E) E) := by
      ext i j
      have := hML i j
      simp only [f, Bool.false_eq_true, if_false] at this
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
      apply mul_left_cancel₀ hDE
      rw [mul_sub, ← this]; ring
    have hU : y.2.2 - x.2.2 = algebraMap (𝓞 E) E (D ^ (L.map Prod.snd).sum * b) • MU.map (algebraMap (𝓞 E) E) := by
      ext i j
      have := hMU i j
      simp only [f, if_true] at this
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
      apply mul_left_cancel₀ hDE
      rw [mul_sub, ← this]; ring
    obtain ⟨A, B, hA, hB, hAB⟩ := close_rel (pm L) hLx hUx hLy hUy hLxi hUxi ML MU hL hU
    exact ⟨A, B, hA, hB, by rw [hx, hy]; exact hAB⟩)
  refine ⟨Prod.fst '' Zs, hfin.image _, ?_⟩
  intro Z hZ hcell
  obtain ⟨L1, U1, hL1, hU1, hZe, hL1i, hU1i⟩ := hbd Z (intg_of_entries hZ) hcell
  obtain ⟨y, hy, A, B, hA, hB, hAB⟩ := hZs (Z, L1, U1) ⟨hL1, hU1, hZe, hL1i, hU1i⟩
  exact ⟨A, B, hA, hB, ⟨y, hy, hAB.symm⟩⟩

end PI.TermsAtPtFiniteW
