import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.CellDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfComps
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.NormOne

noncomputable section

namespace GlobalTheory.CompanionTheory.MoveCell

open Matrix Polynomial

section Generic

variable {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Establish `h` using `RingHom.map_det (Polynomial.evalRingHom x) (A.map C + (X : Polynomial Ω) • B.map C)`. Rewrite `h` using `[Polynomial.coe_evalRingHom]`. Rewrite using `[h]`. Use `congr 1`. Use extensionality with `i j`.

Simplify using `only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, RingHom.mapMatrix_apply, Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_C, smul_eq_mul, Polynomial.eval_mul, Polynomial.eval_X]`.
-/
theorem eval_det_line {Ω : Type} [CommRing Ω] (A B : Matrix n n Ω) (x : Ω) :
    ((A.map C + (X : Polynomial Ω) • B.map C).det).eval x = (A + x • B).det := by
  have h := RingHom.map_det (Polynomial.evalRingHom x) (A.map C + (X : Polynomial Ω) • B.map C)
  rw [Polynomial.coe_evalRingHom] at h
  rw [h]
  congr 1
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, RingHom.mapMatrix_apply, Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_C, smul_eq_mul, Polynomial.eval_mul, Polynomial.eval_X]

/- English proof (translation)
Establish `hP : (A.map C + (X : Polynomial Ω) • B.map C).det ≠ 0`. Introduce `h`. Apply `hs` to reduce the goal to its premises. Rewrite using `[← eval_det_line, h, Polynomial.eval_zero]`. Use `(Polynomial.finite_setOf_isRoot hP).subset fun x hx => ?_` and prove the remaining obligations.

Simplify using `only [Set.mem_setOf_eq, Polynomial.IsRoot.def, eval_det_line]`. Conclude with `hx`.
-/
theorem finite_bad {Ω : Type} [Field Ω] (A B : Matrix n n Ω) {s : Ω} (hs : (A + s • B).det ≠ 0) :
    {x : Ω | (A + x • B).det = 0}.Finite := by
  have hP : (A.map C + (X : Polynomial Ω) • B.map C).det ≠ 0 := by
    intro h
    apply hs
    rw [← eval_det_line, h, Polynomial.eval_zero]
  refine (Polynomial.finite_setOf_isRoot hP).subset fun x hx => ?_
  simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, eval_det_line]
  exact hx

/- English proof (translation)
Establish `hP : (-a).charpoly ≠ 0` using `(Matrix.charpoly_monic _).ne_zero`. Use `(Polynomial.finite_setOf_isRoot hP).subset fun x hx => ?_` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq, Polynomial.IsRoot.def, Matrix.eval_charpoly] at hx ⊢`. Rewrite using `[← hx]`. Use `congr 1`.

Use extensionality with `i j`. Simplify using `[Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply, add_comm]`.
-/
theorem finite_bad_scalar {Ω : Type} [Field Ω] (a : Matrix n n Ω) :
    {x : Ω | (a + x • (1 : Matrix n n Ω)).det = 0}.Finite := by
  have hP : (-a).charpoly ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  refine (Polynomial.finite_setOf_isRoot hP).subset fun x hx => ?_
  simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, Matrix.eval_charpoly] at hx ⊢
  rw [← hx]
  congr 1
  ext i j
  simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply, add_comm]

/- English proof (translation)
Establish `h2 : {x : Ω | ((1 : Matrix n n Ω) + x • c).det = 0}.Finite` using `finite_bad 1 c (s := 0) (by simp)`. Establish `hfin` using `((finite_bad_scalar a).union h2).preimage (f := τ) hτ.injOn`. Take `⟨t, ht⟩` from `hfin.exists_notMem`. Simplify using `only [Set.mem_preimage, Set.mem_union, Set.mem_setOf_eq, not_or] at ht`. Take `⟨h1, h3⟩` from `ht`.

Use `set u : Matrix n n Ω := a + τ t • (1 : Matrix n n Ω) with hu`. Establish `hdet : IsUnit u.det` using `isUnit_iff_ne_zero.2 h1`. Use `⟨-(b * u⁻¹), ?_⟩` and prove the remaining obligations. Establish `key : c - d * -(b * u⁻¹) = ((1 : Matrix n n Ω) + τ t • c) * u⁻¹`. Establish `hcu : c = c * (u * u⁻¹)` using `by rw [Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]`.

Establish `e1 : (1 : Matrix n n Ω) + τ t • c = c * u + d * b`. Rewrite using `[← h, hu, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]`. Normalize the expressions using the abelian group laws. Rewrite using `[e1, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← hcu]`. Simplify using `[Matrix.mul_neg, sub_eq_add_neg]`.

Rewrite using `[key, Matrix.det_mul]`. Conclude with `mul_ne_zero h3 (isUnit_iff_ne_zero.1 (by`. Rewrite using `[Matrix.det_nonsing_inv]`. Conclude with `hdet.ringInverse))`.
-/
theorem exists_Y {Ω : Type} [Field Ω] (τ : ℚ → Ω) (hτ : Function.Injective τ) (c d a b : Matrix n n Ω)
    (h : c * a + d * b = 1) : ∃ Y : Matrix n n Ω, (c - d * Y).det ≠ 0 := by
  have h2 : {x : Ω | ((1 : Matrix n n Ω) + x • c).det = 0}.Finite :=
    finite_bad 1 c (s := 0) (by simp)
  have hfin := ((finite_bad_scalar a).union h2).preimage (f := τ) hτ.injOn
  obtain ⟨t, ht⟩ := hfin.exists_notMem
  simp only [Set.mem_preimage, Set.mem_union, Set.mem_setOf_eq, not_or] at ht
  obtain ⟨h1, h3⟩ := ht
  set u : Matrix n n Ω := a + τ t • (1 : Matrix n n Ω) with hu
  have hdet : IsUnit u.det := isUnit_iff_ne_zero.2 h1
  refine ⟨-(b * u⁻¹), ?_⟩
  have key : c - d * -(b * u⁻¹) = ((1 : Matrix n n Ω) + τ t • c) * u⁻¹ := by
    have hcu : c = c * (u * u⁻¹) := by rw [Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
    have e1 : (1 : Matrix n n Ω) + τ t • c = c * u + d * b := by
      rw [← h, hu, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
      abel
    rw [e1, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← hcu]
    simp [Matrix.mul_neg, sub_eq_add_neg]
  rw [key, Matrix.det_mul]
  exact mul_ne_zero h3 (isUnit_iff_ne_zero.1 (by
    rw [Matrix.det_nonsing_inv]; exact hdet.ringInverse))

/- English proof (translation)
Use `set N := (1 - e) • (1 : Matrix n n R) + e • M with hN`. Establish `h1 : e * (N.det - M.det) = 0`. Establish `hq` using `RingHom.map_det (Ideal.Quotient.mk (Ideal.span {1 - e})) N`. Establish `hq'` using `RingHom.map_det (Ideal.Quotient.mk (Ideal.span {1 - e})) M`. Establish `hm : (Ideal.Quotient.mk (Ideal.span {1 - e})) e = 1`.

Rewrite using `[← map_one (Ideal.Quotient.mk (Ideal.span {1 - e})), Ideal.Quotient.eq]`. Rewrite using `[Ideal.mem_span_singleton]`. Conclude with `⟨-1, by ring⟩`. Establish `he0 : (Ideal.Quotient.mk (Ideal.span {1 - e})) (1 - e) = 0`. Rewrite using `[map_sub, map_one, hm, sub_self]`.

Establish `hmap : (Ideal.Quotient.mk (Ideal.span {1 - e})).mapMatrix N = (Ideal.Quotient.mk (Ideal.span {1 - e})).mapMatrix M`. Use extensionality with `i j`. Simplify using `[hN, Matrix.add_apply, Matrix.smul_apply, he0, hm]`. Establish `hz : (Ideal.Quotient.mk (Ideal.span {1 - e})) N.det = (Ideal.Quotient.mk (Ideal.span {1 - e})) M.det` using `by rw [hq, hq', hmap]`. Rewrite `hz` using `[Ideal.Quotient.eq, Ideal.mem_span_singleton]`.

Take `⟨r, hr⟩` from `hz`. Rewrite using `[hr]`. Take the linear combination `(-r) * he`. Establish `h2 : (1 - e) * (N.det - 1) = 0`. Establish `hq` using `RingHom.map_det (Ideal.Quotient.mk (Ideal.span {e})) N`.

Establish `he0 : (Ideal.Quotient.mk (Ideal.span {e})) e = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self e)`. Establish `hmap : (Ideal.Quotient.mk (Ideal.span {e})).mapMatrix N = 1`. Use extensionality with `i j`. Simplify using `[hN, Matrix.add_apply, Matrix.smul_apply, he0, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `hz : (Ideal.Quotient.mk (Ideal.span {e})) N.det = (Ideal.Quotient.mk (Ideal.span {e})) 1`. Rewrite using `[hq, hmap, Matrix.det_one, map_one]`. Rewrite `hz` using `[Ideal.Quotient.eq, Ideal.mem_span_singleton]`. Take `⟨r, hr⟩` from `hz`. Rewrite using `[hr]`.

Take the linear combination `(-r) * he`. Take the linear combination `h1 + h2`.
-/
theorem det_idem {R : Type} [CommRing R] (e : R) (he : e * e = e) (M : Matrix n n R) :
    ((1 - e) • (1 : Matrix n n R) + e • M).det = 1 - e + e * M.det := by
  set N := (1 - e) • (1 : Matrix n n R) + e • M with hN
  have h1 : e * (N.det - M.det) = 0 := by
    have hq := RingHom.map_det (Ideal.Quotient.mk (Ideal.span {1 - e})) N
    have hq' := RingHom.map_det (Ideal.Quotient.mk (Ideal.span {1 - e})) M
    have hm : (Ideal.Quotient.mk (Ideal.span {1 - e})) e = 1 := by
      rw [← map_one (Ideal.Quotient.mk (Ideal.span {1 - e})), Ideal.Quotient.eq]
      rw [Ideal.mem_span_singleton]
      exact ⟨-1, by ring⟩
    have he0 : (Ideal.Quotient.mk (Ideal.span {1 - e})) (1 - e) = 0 := by
      rw [map_sub, map_one, hm, sub_self]
    have hmap : (Ideal.Quotient.mk (Ideal.span {1 - e})).mapMatrix N =
        (Ideal.Quotient.mk (Ideal.span {1 - e})).mapMatrix M := by
      ext i j
      simp [hN, Matrix.add_apply, Matrix.smul_apply, he0, hm]
    have hz : (Ideal.Quotient.mk (Ideal.span {1 - e})) N.det =
        (Ideal.Quotient.mk (Ideal.span {1 - e})) M.det := by rw [hq, hq', hmap]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at hz
    obtain ⟨r, hr⟩ := hz
    rw [hr]
    linear_combination (-r) * he
  have h2 : (1 - e) * (N.det - 1) = 0 := by
    have hq := RingHom.map_det (Ideal.Quotient.mk (Ideal.span {e})) N
    have he0 : (Ideal.Quotient.mk (Ideal.span {e})) e = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self e)
    have hmap : (Ideal.Quotient.mk (Ideal.span {e})).mapMatrix N = 1 := by
      ext i j
      simp [hN, Matrix.add_apply, Matrix.smul_apply, he0, Matrix.one_apply]
      split_ifs <;> simp
    have hz : (Ideal.Quotient.mk (Ideal.span {e})) N.det = (Ideal.Quotient.mk (Ideal.span {e})) 1 := by
      rw [hq, hmap, Matrix.det_one, map_one]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at hz
    obtain ⟨r, hr⟩ := hz
    rw [hr]
    linear_combination (-r) * he
  linear_combination h1 + h2

end Generic

section Herm

variable {n : Type} [Fintype n] [DecidableEq n] {E : Type} [Field E] [CharZero E]

def IsH (σ : E →+* E) (y : Matrix n n E) : Prop := (y.map σ)ᵀ = y

/- English proof (translation)
Unfold `IsH`. Rewrite using `[← Matrix.ext_iff]`. Both sides reduce to the same expression.
-/
theorem isH_iff (σ : E →+* E) (y : Matrix n n E) : IsH σ y ↔ ∀ i j, σ (y j i) = y i j := by
  unfold IsH
  rw [← Matrix.ext_iff]
  rfl

/- English proof (translation)
Rewrite `*` using `[isH_iff]`. Introduce `i j`. Simplify using `[hy i j, hh i j, map_ratCast]`.
-/
theorem IsH.line {σ : E →+* E} {y h : Matrix n n E} (hy : IsH σ y) (hh : IsH σ h) (t : ℚ) :
    IsH σ (y + (t : E) • h) := by
  rw [isH_iff] at *
  intro i j
  simp [hy i j, hh i j, map_ratCast]

/- English proof (translation)
Rewrite `*` using `[isH_iff]`. Introduce `i j`. Simplify using `[hy i j, hh i j]`.
-/
theorem IsH.sub {σ : E →+* E} {y h : Matrix n n E} (hy : IsH σ y) (hh : IsH σ h) : IsH σ (y - h) := by
  rw [isH_iff] at *
  intro i j
  simp [hy i j, hh i j]

/- English proof (translation)
Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem map_line {Ω : Type} [Field Ω] (ι : E →+* Ω) (y h : Matrix n n E) (t : E) :
    (y + t • h).map ι = y.map ι + ι t • h.map ι := by
  ext i j
  simp

/- English proof (translation)
The claim follows from `ι.injective.comp Rat.cast_injective`.
-/
theorem rat_inj {Ω : Type} [Field Ω] (ι : E →+* Ω) : Function.Injective fun t : ℚ => ι (t : E) :=
  ι.injective.comp Rat.cast_injective

/- English proof (translation)
Establish `e : ∀ x : Ω, (c - d * y.map ι) + x • (-(d * w.map ι)) = c - d * (y.map ι + x • w.map ι)`. Introduce `x`. Rewrite using `[Matrix.mul_add, Matrix.mul_smul, smul_neg]`. Normalize the expressions using the abelian group laws. Establish `hfin` using `finite_bad (c - d * y.map ι) (-(d * w.map ι)) (s := z) (by rw [e]; exact hz)`.

Use `(hfin.preimage (f := fun t : ℚ => ι (t : E)) (rat_inj ι).injOn).subset fun t ht => ?_` and prove the remaining obligations. Simplify using `only [Set.mem_preimage, Set.mem_setOf_eq, e]`. Simplify `ht` using `only [Set.mem_setOf_eq, map_line]`.
-/
theorem line_bad {Ω : Type} [Field Ω] (ι : E →+* Ω) (c d : Matrix n n Ω) (y w : Matrix n n E) {z : Ω}
    (hz : (c - d * (y.map ι + z • w.map ι)).det ≠ 0) :
    {t : ℚ | (c - d * (y + (t : E) • w).map ι).det = 0}.Finite := by
  have e : ∀ x : Ω, (c - d * y.map ι) + x • (-(d * w.map ι)) = c - d * (y.map ι + x • w.map ι) := by
    intro x
    rw [Matrix.mul_add, Matrix.mul_smul, smul_neg]
    abel
  have hfin := finite_bad (c - d * y.map ι) (-(d * w.map ι)) (s := z) (by rw [e]; exact hz)
  refine (hfin.preimage (f := fun t : ℚ => ι (t : E)) (rat_inj ι).injOn).subset fun t ht => ?_
  simp only [Set.mem_preimage, Set.mem_setOf_eq, e]
  simpa only [Set.mem_setOf_eq, map_line] using ht

/- English proof (translation)
Introduce `y hy`. Assume the negation of the conclusion as `hne`. Establish `hfin` using `line_bad ι (c - d * Y) d y h (z := z) (by`. Introduce `h0`. Apply `hne` to reduce the goal to its premises.

Rewrite using `[← h0, Matrix.mul_add, Matrix.mul_add, Matrix.mul_add]`. Use `congr 1`. Use the proof step `abel)`. Apply `Set.infinite_univ (α := ℚ)` to reduce the goal to its premises. Use `hfin.subset fun t _ => ?_` and prove the remaining obligations.

Use `hY _ (hy.line hh t)` as an intermediate fact. Simplify using `only [Set.mem_setOf_eq]`. Rewrite using `[← this, Matrix.mul_add]`. Use `congr 1`. Normalize the expressions using the abelian group laws.
-/
theorem step {Ω : Type} [Field Ω] (σ : E →+* E) (ι : E →+* Ω) (c d Y : Matrix n n Ω)
    (hY : ∀ y, IsH σ y → (c - d * (Y + y.map ι)).det = 0) {h : Matrix n n E} (hh : IsH σ h) (z : Ω) :
    ∀ y, IsH σ y → (c - d * ((Y + z • h.map ι) + y.map ι)).det = 0 := by
  intro y hy
  by_contra hne
  have hfin := line_bad ι (c - d * Y) d y h (z := z) (by
    intro h0
    apply hne
    rw [← h0, Matrix.mul_add, Matrix.mul_add, Matrix.mul_add]
    congr 1
    abel)
  apply Set.infinite_univ (α := ℚ)
  refine hfin.subset fun t _ => ?_
  have := hY _ (hy.line hh t)
  simp only [Set.mem_setOf_eq]
  rw [← this, Matrix.mul_add]
  congr 1
  abel

/- English proof (translation)
Set `S : Matrix n n Ω → Prop` to `fun Y => ∀ y, IsH σ y → (c - d * (Y + y.map ι)).det = 0`. Establish `hS0 : S 0` using `fun y hy => by simpa using h y hy`. Establish `hstep : ∀ Y, S Y → ∀ {h : Matrix n n E}, IsH σ h → ∀ z : Ω, S (Y + z • h.map ι)` using `fun Y hY _ hh z => step σ ι c d Y hY hh z`. Set `Zs : AddSubmonoid (Matrix n n Ω)` to `{ carrier := {W | ∀ Y, S Y → S (Y + W)} add_mem' := fun {a b} ha hb Y hY => by`. Rewrite using `[← add_assoc]`.

Conclude with `hb _ (ha _ hY)`. Use the proof step `zero_mem' := fun Y hY => by simpa using hY }`. Establish `h2 : (2 : Ω) ≠ 0` using `fun h0 => two_ne_zero (α := E) (ι.injective (by rw [map_ofNat, map_zero]; exact h0))`. Establish `hδ' : ι δ ≠ 0` using `(map_ne_zero ι).2 hδ0`. Establish `hsingle : ∀ a b z, Matrix.single a b z ∈ Zs`.

Introduce `a b z Y hY`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Establish `hH : IsH σ (Matrix.single a a (1 : E))`. Rewrite using `[isH_iff]`.

Introduce `i j`. Establish `hc : (a = j ∧ a = i) ↔ (a = i ∧ a = j)` using `and_comm`. Simplify using `only [Matrix.single_apply, apply_ite σ, map_one, map_zero, hc]`. Establish `e : Matrix.single a a z = z • (Matrix.single a a (1 : E)).map ι`. Use extensionality with `i j`.

Apply the tactic sequence `by_cases h1 : i = a <;> by_cases h2 : j = a <;> simp [Matrix.single_apply, h1, h2]`. Rewrite using `[e]`. Conclude with `hstep Y hY hH z`. Establish `hH1 : IsH σ (Matrix.single a b (1 : E) + Matrix.single b a (1 : E))`. Rewrite using `[isH_iff]`.

Introduce `i j`. Simplify using `only [Matrix.add_apply, Matrix.single_apply, map_add]`. Apply the tactic sequence `split_ifs <;> simp_all`. Establish `hH2 : IsH σ (Matrix.single a b δ - Matrix.single b a δ)`. Rewrite using `[isH_iff]`.

Introduce `i j`. Simplify using `only [Matrix.sub_apply, Matrix.single_apply, map_sub]`. Apply the tactic sequence `split_ifs <;> simp_all`. Establish `e : Matrix.single a b z = (z / 2) • (Matrix.single a b (1 : E) + Matrix.single b a (1 : E)).map ι + (z / (2 * ι δ)) • (Matrix.single a b δ - Matrix.single b a δ).map ι`. Establish `hw : z / (2 * ι δ) * ι δ = z / 2` using `by field_simp`.

Establish `hz : z / 2 + z / 2 = z` using `by field_simp; ring`. Use extensionality with `i j`. Simplify using `only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.single_apply, smul_eq_mul, map_add, map_sub, apply_ite ι, map_one, map_zero]`. Distinguish the cases in `p : a = i ∧ b = j`. Distinguish the cases in `q : b = i ∧ a = j`.

Conclude with `absurd (p.1.trans q.1.symm) hab`. Simplify using `only [if_pos p, if_neg q]`. Take the linear combination `(-1) * hz - hw`. Distinguish the cases in `q : b = i ∧ a = j`. Simplify using `only [if_neg p, if_pos q]`.

Take the linear combination `hw`. Simplify using `only [if_neg p, if_neg q]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, ← add_assoc]`. Conclude with `hstep _ (hstep Y hY hH1 _) hH2 _`.

Establish `hall : Y ∈ Zs`. Rewrite using `[Matrix.matrix_eq_sum_single Y]`. Conclude with `Zs.sum_mem fun a _ => Zs.sum_mem fun b _ => hsingle a b _`. Use `hall 0 hS0 0 (by rw [isH_iff]; simp)` as an intermediate fact. Simplify using `using this`.
-/
theorem vanish_all {Ω : Type} [Field Ω] (σ : E →+* E) (ι : E →+* Ω) {δ : E} (hδ0 : δ ≠ 0) (hδ : σ δ = -δ)
    (c d : Matrix n n Ω) (h : ∀ y, IsH σ y → (c - d * y.map ι).det = 0) (Y : Matrix n n Ω) :
    (c - d * Y).det = 0 := by
  let S : Matrix n n Ω → Prop := fun Y => ∀ y, IsH σ y → (c - d * (Y + y.map ι)).det = 0
  have hS0 : S 0 := fun y hy => by simpa using h y hy
  have hstep : ∀ Y, S Y → ∀ {h : Matrix n n E}, IsH σ h → ∀ z : Ω, S (Y + z • h.map ι) :=
    fun Y hY _ hh z => step σ ι c d Y hY hh z
  let Zs : AddSubmonoid (Matrix n n Ω) :=
    { carrier := {W | ∀ Y, S Y → S (Y + W)}
      add_mem' := fun {a b} ha hb Y hY => by
        rw [← add_assoc]
        exact hb _ (ha _ hY)
      zero_mem' := fun Y hY => by simpa using hY }
  have h2 : (2 : Ω) ≠ 0 := fun h0 => two_ne_zero (α := E) (ι.injective (by rw [map_ofNat, map_zero]; exact h0))
  have hδ' : ι δ ≠ 0 := (map_ne_zero ι).2 hδ0
  have hsingle : ∀ a b z, Matrix.single a b z ∈ Zs := by
    intro a b z Y hY
    by_cases hab : a = b
    · subst hab
      have hH : IsH σ (Matrix.single a a (1 : E)) := by
        rw [isH_iff]
        intro i j
        have hc : (a = j ∧ a = i) ↔ (a = i ∧ a = j) := and_comm
        simp only [Matrix.single_apply, apply_ite σ, map_one, map_zero, hc]
      have e : Matrix.single a a z = z • (Matrix.single a a (1 : E)).map ι := by
        ext i j
        by_cases h1 : i = a <;> by_cases h2 : j = a <;> simp [Matrix.single_apply, h1, h2]
      rw [e]
      exact hstep Y hY hH z
    · have hH1 : IsH σ (Matrix.single a b (1 : E) + Matrix.single b a (1 : E)) := by
        rw [isH_iff]
        intro i j
        simp only [Matrix.add_apply, Matrix.single_apply, map_add]
        split_ifs <;> simp_all
      have hH2 : IsH σ (Matrix.single a b δ - Matrix.single b a δ) := by
        rw [isH_iff]
        intro i j
        simp only [Matrix.sub_apply, Matrix.single_apply, map_sub]
        split_ifs <;> simp_all
      have e : Matrix.single a b z = (z / 2) • (Matrix.single a b (1 : E) + Matrix.single b a (1 : E)).map ι +
          (z / (2 * ι δ)) • (Matrix.single a b δ - Matrix.single b a δ).map ι := by
        have hw : z / (2 * ι δ) * ι δ = z / 2 := by field_simp
        have hz : z / 2 + z / 2 = z := by field_simp; ring
        ext i j
        simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.single_apply, smul_eq_mul,
          map_add, map_sub, apply_ite ι, map_one, map_zero]
        by_cases p : a = i ∧ b = j
        · by_cases q : b = i ∧ a = j
          · exact absurd (p.1.trans q.1.symm) hab
          · simp only [if_pos p, if_neg q]
            linear_combination (-1) * hz - hw
        · by_cases q : b = i ∧ a = j
          · simp only [if_neg p, if_pos q]
            linear_combination hw
          · simp only [if_neg p, if_neg q]
            ring
      rw [e, ← add_assoc]
      exact hstep _ (hstep Y hY hH1 _) hH2 _
  have hall : Y ∈ Zs := by
    rw [Matrix.matrix_eq_sum_single Y]
    exact Zs.sum_mem fun a _ => Zs.sum_mem fun b _ => hsingle a b _
  have := hall 0 hS0 0 (by rw [isH_iff]; simp)
  simpa using this

/- English proof (translation)
It suffices to establish `H : ∀ s : Finset (Fin m), ∃ y, IsH σ y ∧ ∀ i ∈ s, (c i - d i * y.map (ι i)).det ≠ 0 by`. Take `⟨y, hy, hs⟩` from `H Finset.univ`. Conclude with `⟨y, hy, fun i => hs i (Finset.mem_univ i)⟩`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`.

Consider the case `empty => exact ⟨0, by rw [isH_iff]; simp, by simp⟩`. Consider the case `insert a s ha ih`. Take `⟨y₁, h₁, g₁⟩` from `ih`. Take `⟨y₂, h₂, g₂⟩` from `h a`. Establish `hfin : ∀ i ∈ insert a s, {t : ℚ | (c i - d i * (y₁ + (t : E) • (y₂ - y₁)).map (ι i)).det = 0}.Finite`.

Introduce `i hi`. Break down `Finset.mem_insert.1 hi with rfl | hi` into its components or cases. Use `line_bad (ι i) _ _ _ _ (z := 1) ?_` and prove the remaining obligations. Establish `e : y₁.map (ι i) + (1 : Ω i) • (y₂ - y₁).map (ι i) = y₂.map (ι i)`. Use extensionality with `p q`.

Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `g₂`. Use `line_bad (ι i) _ _ _ _ (z := 0) ?_` and prove the remaining obligations. Simplify using `using g₁ i hi`.

Establish `hU` using `(Finset.finite_toSet (insert a s)).biUnion hfin`. Take `⟨t, ht⟩` from `hU.exists_notMem`. Simplify using `only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_coe, not_exists] at ht`. Conclude with `⟨_, h₁.line (h₂.sub h₁) t, fun i hi h0 => ht i hi h0⟩`.
-/
theorem exists_common {m : ℕ} (Ω : Fin m → Type) [∀ i, Field (Ω i)] (σ : E →+* E) (ι : ∀ i, E →+* Ω i)
    (c d : ∀ i, Matrix n n (Ω i)) (h : ∀ i, ∃ y, IsH σ y ∧ (c i - d i * y.map (ι i)).det ≠ 0) :
    ∃ y, IsH σ y ∧ ∀ i, (c i - d i * y.map (ι i)).det ≠ 0 := by
  suffices H : ∀ s : Finset (Fin m), ∃ y, IsH σ y ∧ ∀ i ∈ s, (c i - d i * y.map (ι i)).det ≠ 0 by
    obtain ⟨y, hy, hs⟩ := H Finset.univ
    exact ⟨y, hy, fun i => hs i (Finset.mem_univ i)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by rw [isH_iff]; simp, by simp⟩
  | insert a s ha ih =>
    obtain ⟨y₁, h₁, g₁⟩ := ih
    obtain ⟨y₂, h₂, g₂⟩ := h a
    have hfin : ∀ i ∈ insert a s, {t : ℚ | (c i - d i * (y₁ + (t : E) • (y₂ - y₁)).map (ι i)).det = 0}.Finite := by
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · refine line_bad (ι i) _ _ _ _ (z := 1) ?_
        have e : y₁.map (ι i) + (1 : Ω i) • (y₂ - y₁).map (ι i) = y₂.map (ι i) := by
          ext p q
          simp
        rw [e]
        exact g₂
      · refine line_bad (ι i) _ _ _ _ (z := 0) ?_
        simpa using g₁ i hi
    have hU := (Finset.finite_toSet (insert a s)).biUnion hfin
    obtain ⟨t, ht⟩ := hU.exists_notMem
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_coe, not_exists] at ht
    exact ⟨_, h₁.line (h₂.sub h₁) t, fun i hi h0 => ht i hi h0⟩

end Herm

section Main

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Cell

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {p : ℕ}

/- English proof (translation)
Apply `sub_eq_zero.1` to reduce the goal to its premises. Use `GlobalTheory.CompanionTheory.AdeleComp.eq_zero_of_comps D _ (fun w => ?_) (fun v => ?_)` and prove the remaining obligations. Rewrite using `[map_sub, map_mul, he.1 w]`. Simplify using the standard rewrite rules. Apply the tactic sequence `rw [RingHom.map_sub, RingHom.map_mul, he.2 v] split_ifs <;> simp only [mul_one, mul_zero, sub_self]`.
-/
theorem idem_mul {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) : e * e = e := by
  apply sub_eq_zero.1
  refine GlobalTheory.CompanionTheory.AdeleComp.eq_zero_of_comps D _ (fun w => ?_) (fun v => ?_)
  · rw [map_sub, map_mul, he.1 w]
    simp
  · rw [RingHom.map_sub, RingHom.map_mul, he.2 v]
    split_ifs <;> simp only [mul_one, mul_zero, sub_self]

/- English proof (translation)
Set `U` to `AdelicU.matHom _ D.sp.cm.sig (Jst D p) g`. Establish `hM : mat g = U.1` using `rfl`. Establish `hMN : mat g * (U⁻¹).1 = 1` using `by rw [hM]; exact U.mul_inv`. Set `N : Mx D (p + p) (p + p)` to `(U⁻¹).1`. Set `e : Fin p ⊕ Fin p ≃ Fin (p + p)` to `finSumFinEquiv`.

Establish `hprod : (mat g).submatrix e e * N.submatrix e e = 1`. Rewrite using `[Matrix.submatrix_mul_equiv, hMN, Matrix.submatrix_one_equiv]`. Use `⟨(N.submatrix e e).toBlocks₁₂, (N.submatrix e e).toBlocks₂₂, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Establish `h` using `congrFun (congrFun hprod (Sum.inr i)) (Sum.inr j)`.

Rewrite `h` using `[Matrix.mul_apply, Fintype.sum_sum_type]`. Simplify `h` using `[cB, dB, Matrix.add_apply, Matrix.mul_apply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.toBlocks₁₂, Matrix.one_apply, e]`.
-/
theorem exists_right (g : G D p) : ∃ a b : Mx D p p, cB g * a + dB g * b = 1 := by
  let U := AdelicU.matHom _ D.sp.cm.sig (Jst D p) g
  have hM : mat g = U.1 := rfl
  have hMN : mat g * (U⁻¹).1 = 1 := by rw [hM]; exact U.mul_inv
  let N : Mx D (p + p) (p + p) := (U⁻¹).1
  let e : Fin p ⊕ Fin p ≃ Fin (p + p) := finSumFinEquiv
  have hprod : (mat g).submatrix e e * N.submatrix e e = 1 := by
    rw [Matrix.submatrix_mul_equiv, hMN, Matrix.submatrix_one_equiv]
  refine ⟨(N.submatrix e e).toBlocks₁₂, (N.submatrix e e).toBlocks₂₂, ?_⟩
  ext i j
  have h := congrFun (congrFun hprod (Sum.inr i)) (Sum.inr j)
  rw [Matrix.mul_apply, Fintype.sum_sum_type] at h
  simpa [cB, dB, Matrix.add_apply, Matrix.mul_apply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.toBlocks₁₂,
    Matrix.one_apply, e] using h

/- English proof (translation)
Introduce `hU D p S e he g`. Take `⟨m, Ω, inst, φ, -, hiff⟩` from `hU D S e he`. Establish `hee` using `idem_mul he`. Take `⟨a, b, hab⟩` from `exists_right g`. Take `⟨δ, hδ, hδ0⟩` from `Formalism.L2.PairingIndexBounds.Eq.J.exists_skew D`.

Set `σ : D.host.E →+* D.host.E` to `(D.sp.cm.sig : D.host.E →+* D.host.E)`. Set `ι : ∀ i, D.host.E →+* Ω i` to `fun i => (φ i).comp (incA D)`. Set `c : ∀ i, Matrix (Fin p) (Fin p) (Ω i)` to `fun i => (cB g).map (φ i)`. Set `d : ∀ i, Matrix (Fin p) (Fin p) (Ω i)` to `fun i => (dB g).map (φ i)`. Establish `one : ∀ i, ∃ y, IsH σ y ∧ (c i - d i * y.map (ι i)).det ≠ 0`.

Introduce `i`. Take `⟨Y, hY⟩` from `exists_Y (fun t : ℚ => ι i (t : D.host.E)) (rat_inj (ι i)) (c i) (d i) (a.map (φ i)) (b.map (φ i)) (by`. Use `congrArg (φ i).mapMatrix hab` as an intermediate fact. Simplify `this)` using `[map_add, map_mul, map_one, c, d]`. Assume the negation of the conclusion as `hno`.

Use `push Not at hno`. Conclude with `hY (vanish_all σ (ι i) hδ0 hδ (c i) (d i) hno Y)`. Take `⟨y, hy, hall⟩` from `exists_common Ω σ ι c d one`. Use `⟨⟨y, hy⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[det_idem e hee]`.

Use `(hiff _).2 fun i => ?_` and prove the remaining obligations. Establish `hmap : (φ i) (cB g - mm (dB g) (rat y)).det = (c i - d i * y.map (ι i)).det`. Rewrite using `[RingHom.map_det]`. Use `congr 1`. Establish `: mm (dB g) (rat y) = dB g * rat y` using `rfl`.

Rewrite using `[this, map_sub, map_mul]`. Both sides reduce to the same expression. Conclude with `hmap ▸ hall i`.
-/
theorem move_of_unitCrit : UnitCrit → Move := by
  intro hU D p S e he g
  obtain ⟨m, Ω, inst, φ, -, hiff⟩ := hU D S e he
  have hee := idem_mul he
  obtain ⟨a, b, hab⟩ := exists_right g
  obtain ⟨δ, hδ, hδ0⟩ := Formalism.L2.PairingIndexBounds.Eq.J.exists_skew D
  let σ : D.host.E →+* D.host.E := (D.sp.cm.sig : D.host.E →+* D.host.E)
  let ι : ∀ i, D.host.E →+* Ω i := fun i => (φ i).comp (incA D)
  let c : ∀ i, Matrix (Fin p) (Fin p) (Ω i) := fun i => (cB g).map (φ i)
  let d : ∀ i, Matrix (Fin p) (Fin p) (Ω i) := fun i => (dB g).map (φ i)
  have one : ∀ i, ∃ y, IsH σ y ∧ (c i - d i * y.map (ι i)).det ≠ 0 := by
    intro i
    obtain ⟨Y, hY⟩ := exists_Y (fun t : ℚ => ι i (t : D.host.E)) (rat_inj (ι i)) (c i) (d i) (a.map (φ i)) (b.map (φ i)) (by
      have := congrArg (φ i).mapMatrix hab
      simpa [map_add, map_mul, map_one, c, d] using this)
    by_contra hno
    push Not at hno
    exact hY (vanish_all σ (ι i) hδ0 hδ (c i) (d i) hno Y)
  obtain ⟨y, hy, hall⟩ := exists_common Ω σ ι c d one
  refine ⟨⟨y, hy⟩, ?_⟩
  rw [det_idem e hee]
  refine (hiff _).2 fun i => ?_
  have hmap : (φ i) (cB g - mm (dB g) (rat y)).det = (c i - d i * y.map (ι i)).det := by
    rw [RingHom.map_det]
    congr 1
    have : mm (dB g) (rat y) = dB g * rat y := rfl
    rw [this, map_sub, map_mul]
    rfl
  exact hmap ▸ hall i

end Main

end GlobalTheory.CompanionTheory.MoveCell
