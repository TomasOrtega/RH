import Mathlib
import Formalism.PeriodIntegrals.SmithMat
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SmithNormalForm.IsUnitOneAddVecMulVec

namespace PI.SmithWork

open Matrix

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

section General

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Distinguish the cases in `hpi : p = i`. Simplify using `[hpi, Pi.single_apply, add_mul, Finset.sum_add_distrib, ite_mul]`. Distinguish the cases in `hpj : p = j`. Simplify using `[hpi, hpj, Ne.symm hij, Pi.single_apply, add_mul, Finset.sum_add_distrib, ite_mul]`. Simplify using `[hpi, hpj, Pi.single_apply, ite_mul]`.
-/
private theorem sum_pairSingle_mul_eq_ite (i j : ι) (hij : i ≠ j) (x y z w : R) (p : ι) (v : ι → R) :
    ∑ r, (if p = i then Pi.single i x + Pi.single j y
      else if p = j then Pi.single i z + Pi.single j w else Pi.single p 1 : ι → R) r * v r =
      if p = i then x * v i + y * v j else if p = j then z * v i + w * v j else v p := by
  by_cases hpi : p = i
  · simp [hpi, Pi.single_apply, add_mul, Finset.sum_add_distrib, ite_mul]
  · by_cases hpj : p = j
    · simp [hpi, hpj, Ne.symm hij, Pi.single_apply, add_mul, Finset.sum_add_distrib, ite_mul]
    · simp [hpi, hpj, Pi.single_apply, ite_mul]

/- English proof (translation)
Establish `h : (Matrix.of fun p => if p = i then Pi.single i x + Pi.single j y else if p = j then Pi.single i (-b') + Pi.single j a' else Pi.single p 1 : Matrix ι ι R) * (Matrix.of fun p => if p = i then Pi.single i a' + Pi.single j (-y) else if p = j then Pi.single i b' + Pi.single j x els …`. Use extensionality with `p q`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [Matrix.of_apply]`. Rewrite using `[sum_pairSingle_mul_eq_ite i j hij x y (-b') a' p, Matrix.one_apply]`.

Apply the tactic sequence `by_cases hpi : p = i <;> by_cases hpj : p = j <;> by_cases hqi : q = i <;> by_cases hqj : q = j <;>`. Apply the tactic sequence `simp_all [Pi.single_apply, Ne.symm hij] <;>`. Apply the tactic sequence `first | ring1 | linear_combination key | (intro h; exact hqi h.symm) | (intro h; exact hqj h.symm) | (simp only [@eq_comm _ q p])`. Conclude with `(Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse h)`.
-/
private theorem unit_lemma' (i j : ι) (hij : i ≠ j) (x y a' b' : R) (key : x * a' + y * b' = 1) :
    IsUnit (Matrix.of fun p => if p = i then Pi.single i x + Pi.single j y
      else if p = j then Pi.single i (-b') + Pi.single j a' else Pi.single p 1 : Matrix ι ι R) := by
  have h : (Matrix.of fun p => if p = i then Pi.single i x + Pi.single j y
      else if p = j then Pi.single i (-b') + Pi.single j a' else Pi.single p 1 : Matrix ι ι R) * (Matrix.of fun p => if p = i then Pi.single i a' + Pi.single j (-y)
      else if p = j then Pi.single i b' + Pi.single j x else Pi.single p 1 : Matrix ι ι R) = 1 := by
    ext p q
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    rw [sum_pairSingle_mul_eq_ite i j hij x y (-b') a' p, Matrix.one_apply]
    by_cases hpi : p = i <;> by_cases hpj : p = j <;> by_cases hqi : q = i <;> by_cases hqj : q = j <;>
      simp_all [Pi.single_apply, Ne.symm hij] <;>
      first | ring1 | linear_combination key | (intro h; exact hqi h.symm) | (intro h; exact hqj h.symm) | (simp only [@eq_comm _ q p])
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse h)

/- English proof (translation)
Take `⟨d, hd⟩` from `(IsPrincipalIdealRing.principal (Ideal.span {B i c, B j c})).principal`. Establish `ha : B i c ∈ (Submodule.span R {d} : Ideal R)`. Rewrite using `[← hd]`. Conclude with `Ideal.subset_span (Set.mem_insert _ _)`. Establish `hb : B j c ∈ (Submodule.span R {d} : Ideal R)`.

Rewrite using `[← hd]`. Conclude with `Ideal.subset_span (Set.mem_insert_of_mem _ rfl)`. Establish `hdm : d ∈ Ideal.span {B i c, B j c}`. Rewrite using `[hd]`. Conclude with `Submodule.mem_span_singleton_self d`.

Take `⟨a', ha'⟩` from `Ideal.mem_span_singleton'.mp ha`. Take `⟨b', hb'⟩` from `Ideal.mem_span_singleton'.mp hb`. Take `⟨x, y, hxy⟩` from `Ideal.mem_span_pair.mp hdm`. Establish `hd0 : d ≠ 0`. Introduce and unpack `rfl`.

Rewrite `ha'` using `[mul_zero]`. Conclude with `h0 ha'.symm`. Establish `key : x * a' + y * b' = 1`. Apply `mul_right_cancel₀ hd0` to reduce the goal to its premises. Rewrite using `[one_mul, add_mul, mul_assoc, mul_assoc, ha', hb', hxy]`.

Establish `hUB : ((Matrix.of fun p => if p = i then Pi.single i x + Pi.single j y else if p = j then Pi.single i (-b') + Pi.single j a' else Pi.single p 1 : Matrix ι ι R) * B) i c = d`. Simplify using `[Matrix.mul_apply, Pi.single_apply, add_mul, Finset.sum_add_distrib, ite_mul, hxy]`. Use `⟨_, unit_lemma' i j hij x y a' b' key, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hUB]; exact ⟨a', by rw [← ha', mul_comm]⟩`. Rewrite using `[hUB]; exact ⟨b', by rw [← hb', mul_comm]⟩`.
-/
theorem exists_row_gcd (B : Matrix ι ι R) (i j c : ι) (hij : i ≠ j) (h0 : B i c ≠ 0) :
    ∃ U : Matrix ι ι R, IsUnit U ∧ (U * B) i c ∣ B i c ∧ (U * B) i c ∣ B j c := by
  obtain ⟨d, hd⟩ := (IsPrincipalIdealRing.principal (Ideal.span {B i c, B j c})).principal
  have ha : B i c ∈ (Submodule.span R {d} : Ideal R) := by
    rw [← hd]; exact Ideal.subset_span (Set.mem_insert _ _)
  have hb : B j c ∈ (Submodule.span R {d} : Ideal R) := by
    rw [← hd]; exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have hdm : d ∈ Ideal.span {B i c, B j c} := by
    rw [hd]; exact Submodule.mem_span_singleton_self d
  obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton'.mp ha
  obtain ⟨b', hb'⟩ := Ideal.mem_span_singleton'.mp hb
  obtain ⟨x, y, hxy⟩ := Ideal.mem_span_pair.mp hdm
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [mul_zero] at ha'
    exact h0 ha'.symm
  have key : x * a' + y * b' = 1 := by
    apply mul_right_cancel₀ hd0
    rw [one_mul, add_mul, mul_assoc, mul_assoc, ha', hb', hxy]
  have hUB : ((Matrix.of fun p => if p = i then Pi.single i x + Pi.single j y
      else if p = j then Pi.single i (-b') + Pi.single j a' else Pi.single p 1 : Matrix ι ι R) * B) i c = d := by
    simp [Matrix.mul_apply, Pi.single_apply, add_mul, Finset.sum_add_distrib, ite_mul, hxy]
  refine ⟨_, unit_lemma' i j hij x y a' b' key, ?_, ?_⟩
  · rw [hUB]; exact ⟨a', by rw [← ha', mul_comm]⟩
  · rw [hUB]; exact ⟨b', by rw [← hb', mul_comm]⟩

/- English proof (translation)
Take `⟨U, hU, h1, h2⟩` from `exists_row_gcd Bᵀ i j a hij h0`. Establish `e : (B * Uᵀ) a i = (U * Bᵀ) i a`. Establish `h` using `congrFun (congrFun (Matrix.transpose_mul U Bᵀ) a) i`. Rewrite `h` using `[Matrix.transpose_transpose]`. Rewrite using `[← h]`.

Both sides reduce to the same expression. Use `⟨Uᵀ, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `(Matrix.isUnit_iff_isUnit_det _).mpr ?_` and prove the remaining obligations. Rewrite using `[Matrix.det_transpose]`. Conclude with `(Matrix.isUnit_iff_isUnit_det _).mp hU`.

Rewrite using `[e]`. Conclude with `h1`. Rewrite using `[e]`. Conclude with `h2`.
-/
theorem exists_col_gcd (B : Matrix ι ι R) (i j a : ι) (hij : i ≠ j) (h0 : B a i ≠ 0) :
    ∃ V : Matrix ι ι R, IsUnit V ∧ (B * V) a i ∣ B a i ∧ (B * V) a i ∣ B a j := by
  obtain ⟨U, hU, h1, h2⟩ := exists_row_gcd Bᵀ i j a hij h0
  have e : (B * Uᵀ) a i = (U * Bᵀ) i a := by
    have h := congrFun (congrFun (Matrix.transpose_mul U Bᵀ) a) i
    rw [Matrix.transpose_transpose] at h
    rw [← h]
    rfl
  refine ⟨Uᵀ, ?_, ?_, ?_⟩
  · refine (Matrix.isUnit_iff_isUnit_det _).mpr ?_
    rw [Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det _).mp hU
  · rw [e]; exact h1
  · rw [e]; exact h2

/- English proof (translation)
Use `⟨(Equiv.swap i j).toPEquiv.toMatrix, ?_, fun c => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.isUnit_iff_isUnit_det, Matrix.det_permutation]`. Conclude with `(Equiv.Perm.sign _).isUnit.map (Int.castRingHom R)`. Simplify using `[PEquiv.toMatrix_toPEquiv_mul, Matrix.submatrix_apply, Equiv.swap_apply_left]`.
-/
theorem exists_move_row (B : Matrix ι ι R) (i j : ι) :
    ∃ U : Matrix ι ι R, IsUnit U ∧ ∀ c, (U * B) i c = B j c := by
  refine ⟨(Equiv.swap i j).toPEquiv.toMatrix, ?_, fun c => ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_permutation]
    exact (Equiv.Perm.sign _).isUnit.map (Int.castRingHom R)
  · simp [PEquiv.toMatrix_toPEquiv_mul, Matrix.submatrix_apply, Equiv.swap_apply_left]

/- English proof (translation)
Use `⟨(Equiv.swap i j).toPEquiv.toMatrix, ?_, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.isUnit_iff_isUnit_det, Matrix.det_permutation]`. Conclude with `(Equiv.Perm.sign _).isUnit.map (Int.castRingHom R)`. Simplify using `[PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_apply, Equiv.swap_apply_left]`.
-/
theorem exists_move_col (B : Matrix ι ι R) (i j : ι) :
    ∃ V : Matrix ι ι R, IsUnit V ∧ ∀ a, (B * V) a i = B a j := by
  refine ⟨(Equiv.swap i j).toPEquiv.toMatrix, ?_, fun a => ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_permutation]
    exact (Equiv.Perm.sign _).isUnit.map (Int.castRingHom R)
  · simp [PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_apply, Equiv.swap_apply_left]

end General

/- English proof (translation)
Distinguish the cases in `hA : A = 0`. Use `⟨0, 0, ?_, fun i k => by simp⟩` and prove the remaining obligations. Establish `h0 : blk (0 : R) (0 : Matrix (Fin n) (Fin n) R) = A`. Rewrite using `[hA]`. Use extensionality with `a c`.

Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun k => ?_) c <;> simp`. Rewrite using `[h0]`. Conclude with `Eqv.refl A`. Set `S : Set R` to `{r | r ≠ 0 ∧ ∃ B, Eqv A B ∧ B 0 0 = r}`. Establish `hS : S.Nonempty`.

Choose the witnesses or unpack the hypotheses as in `⟨a, c, hac⟩ : ∃ a c, A a c ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hA (by ext a c; simpa using h a c)`. Take `⟨U, hU, h1⟩` from `exists_move_row A 0 a`.

Take `⟨V, hV, h2⟩` from `exists_move_col (U * A) 0 c`. Conclude with `⟨A a c, hac, U * A * V, ((Eqv.refl A).mul_left hU).mul_right hV, by rw [h2, h1]⟩`. Take `⟨b, ⟨hb0, B, hAB, hB⟩, hmin⟩` from `(wellFounded_dvdNotUnit (α := R)).has_min S hS`. Establish `key : ∀ g ∈ S, g ∣ b → b ∣ g`. Introduce and unpack `g hg ⟨x, hx⟩`.

Distinguish the cases in `hxu : IsUnit x`. Take `⟨u, rfl⟩` from `hxu`. Conclude with `⟨↑u⁻¹, by rw [hx]; simp [mul_assoc]⟩`. Conclude with `absurd ⟨hg.1, x, hxu, hx⟩ (hmin g hg)`. Establish `hcol : ∀ B, Eqv A B → B 0 0 = b → ∀ j, b ∣ B j 0`.

Introduce `B hAB hB j`. Distinguish the cases in `hj : j = 0`. Rewrite using `[hj, hB]`. Take `⟨U, hU, h1, h2⟩` from `exists_row_gcd B 0 j 0 (Ne.symm hj) (by rw [hB]; exact hb0)`. Rewrite `h1` using `[hB]`.

Establish `hmem : (U * B) 0 0 ∈ S` using `⟨fun h => hb0 (zero_dvd_iff.1 (h ▸ h1)), U * B, hAB.mul_left hU, rfl⟩`. Conclude with `(key _ hmem h1).trans h2`. Establish `hrow : ∀ B, Eqv A B → B 0 0 = b → ∀ j, b ∣ B 0 j`. Introduce `B hAB hB j`. Distinguish the cases in `hj : j = 0`.

Rewrite using `[hj, hB]`. Take `⟨V, hV, h1, h2⟩` from `exists_col_gcd B 0 j 0 (Ne.symm hj) (by rw [hB]; exact hb0)`. Rewrite `h1` using `[hB]`. Establish `hmem : (B * V) 0 0 ∈ S` using `⟨fun h => hb0 (zero_dvd_iff.1 (h ▸ h1)), B * V, hAB.mul_right hV, rfl⟩`. Conclude with `(key _ hmem h1).trans h2`.

Use `choose t ht using hcol B hAB hB`. Set `t' : Fin (n + 1) → R` to `fun j => if j = 0 then 0 else -t j`. Establish `hL : IsUnit (1 + vecMulVec t' (Pi.single (0 : Fin (n + 1)) (1 : R)))` using `isUnit_one_add_vecMulVec _ _ (by simp [t'])`. Establish `hAB1` using `hAB.mul_left hL`. Establish `e1` using `addRow_apply t' 0 B`.

Generalize the expression as in `(1 + vecMulVec t' (Pi.single (0 : Fin (n + 1)) (1 : R))) * B = B1 at hAB1 e1`. Establish `h1_00 : B1 0 0 = b` using `by rw [e1]; simp [t', hB]`. Establish `h1_c : ∀ i : Fin n, B1 i.succ 0 = 0`. Introduce `i`. Rewrite using `[e1, ht, hB]`.

Simplify using `[t', Fin.succ_ne_zero]`. Expand and normalize the polynomial expressions, which then agree. Use `choose s hs using hrow B1 hAB1 h1_00`. Set `s' : Fin (n + 1) → R` to `fun j => if j = 0 then 0 else -s j`. Establish `hRt : IsUnit (1 + vecMulVec (Pi.single (0 : Fin (n + 1)) (1 : R)) s')` using `isUnit_one_add_vecMulVec _ _ (by simp [s'])`.

Establish `hAB2` using `hAB1.mul_right hRt`. Establish `e2` using `addCol_apply s' 0 B1`. Generalize the expression as in `B1 * (1 + vecMulVec (Pi.single (0 : Fin (n + 1)) (1 : R)) s') = B2 at hAB2 e2`. Establish `h2_00 : B2 0 0 = b` using `by rw [e2]; simp [s', h1_00]`. Establish `h2_c : ∀ i : Fin n, B2 i.succ 0 = 0`.

Introduce `i`. Rewrite using `[e2, h1_c]`. Simplify using the standard rewrite rules. Establish `h2_r : ∀ k : Fin n, B2 0 k.succ = 0`. Introduce `k`.

Rewrite using `[e2, hs, h1_00]`. Simplify using `[s', Fin.succ_ne_zero]`. Use `⟨b, B2.submatrix Fin.succ Fin.succ, ?_, ?_⟩` and prove the remaining obligations. Establish `h` using `eq_blk B2 h2_r h2_c`. Rewrite `h` using `[h2_00]`.

Rewrite using `[← h]`. Conclude with `hAB2`. Introduce `i k`. Establish `hU3 : IsUnit (1 + vecMulVec (Pi.single (0 : Fin (n + 1)) (1 : R)) (Pi.single i.succ 1))` using `isUnit_one_add_vecMulVec _ _ (by simp [Fin.succ_ne_zero])`. Establish `e3` using `addRow_apply (Pi.single (0 : Fin (n + 1)) (1 : R)) i.succ B2`.

Establish `h` using `hrow _ (hAB2.mul_left hU3) (by rw [e3]; simp [h2_00, h2_c]) k.succ`. Rewrite `h` using `[e3]`. Simplify `h` using `[h2_r]`.
-/
theorem exists_blk {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    ∃ (b : R) (D : Matrix (Fin n) (Fin n) R), Eqv A (blk b D) ∧ ∀ i k, b ∣ D i k := by
  by_cases hA : A = 0
  · refine ⟨0, 0, ?_, fun i k => by simp⟩
    have h0 : blk (0 : R) (0 : Matrix (Fin n) (Fin n) R) = A := by
      rw [hA]
      ext a c
      refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun k => ?_) c <;> simp
    rw [h0]
    exact Eqv.refl A
  let S : Set R := {r | r ≠ 0 ∧ ∃ B, Eqv A B ∧ B 0 0 = r}
  have hS : S.Nonempty := by
    obtain ⟨a, c, hac⟩ : ∃ a c, A a c ≠ 0 := by
      by_contra h
      push Not at h
      exact hA (by ext a c; simpa using h a c)
    obtain ⟨U, hU, h1⟩ := exists_move_row A 0 a
    obtain ⟨V, hV, h2⟩ := exists_move_col (U * A) 0 c
    exact ⟨A a c, hac, U * A * V, ((Eqv.refl A).mul_left hU).mul_right hV, by rw [h2, h1]⟩
  obtain ⟨b, ⟨hb0, B, hAB, hB⟩, hmin⟩ := (wellFounded_dvdNotUnit (α := R)).has_min S hS
  have key : ∀ g ∈ S, g ∣ b → b ∣ g := by
    rintro g hg ⟨x, hx⟩
    by_cases hxu : IsUnit x
    · obtain ⟨u, rfl⟩ := hxu
      exact ⟨↑u⁻¹, by rw [hx]; simp [mul_assoc]⟩
    · exact absurd ⟨hg.1, x, hxu, hx⟩ (hmin g hg)
  have hcol : ∀ B, Eqv A B → B 0 0 = b → ∀ j, b ∣ B j 0 := by
    intro B hAB hB j
    by_cases hj : j = 0
    · rw [hj, hB]
    obtain ⟨U, hU, h1, h2⟩ := exists_row_gcd B 0 j 0 (Ne.symm hj) (by rw [hB]; exact hb0)
    rw [hB] at h1
    have hmem : (U * B) 0 0 ∈ S :=
      ⟨fun h => hb0 (zero_dvd_iff.1 (h ▸ h1)), U * B, hAB.mul_left hU, rfl⟩
    exact (key _ hmem h1).trans h2
  have hrow : ∀ B, Eqv A B → B 0 0 = b → ∀ j, b ∣ B 0 j := by
    intro B hAB hB j
    by_cases hj : j = 0
    · rw [hj, hB]
    obtain ⟨V, hV, h1, h2⟩ := exists_col_gcd B 0 j 0 (Ne.symm hj) (by rw [hB]; exact hb0)
    rw [hB] at h1
    have hmem : (B * V) 0 0 ∈ S :=
      ⟨fun h => hb0 (zero_dvd_iff.1 (h ▸ h1)), B * V, hAB.mul_right hV, rfl⟩
    exact (key _ hmem h1).trans h2

  choose t ht using hcol B hAB hB
  let t' : Fin (n + 1) → R := fun j => if j = 0 then 0 else -t j
  have hL : IsUnit (1 + vecMulVec t' (Pi.single (0 : Fin (n + 1)) (1 : R))) :=
    isUnit_one_add_vecMulVec _ _ (by simp [t'])
  have hAB1 := hAB.mul_left hL
  have e1 := addRow_apply t' 0 B
  generalize (1 + vecMulVec t' (Pi.single (0 : Fin (n + 1)) (1 : R))) * B = B1 at hAB1 e1
  have h1_00 : B1 0 0 = b := by rw [e1]; simp [t', hB]
  have h1_c : ∀ i : Fin n, B1 i.succ 0 = 0 := by
    intro i
    rw [e1, ht, hB]
    simp [t', Fin.succ_ne_zero]
    ring

  choose s hs using hrow B1 hAB1 h1_00
  let s' : Fin (n + 1) → R := fun j => if j = 0 then 0 else -s j
  have hRt : IsUnit (1 + vecMulVec (Pi.single (0 : Fin (n + 1)) (1 : R)) s') :=
    isUnit_one_add_vecMulVec _ _ (by simp [s'])
  have hAB2 := hAB1.mul_right hRt
  have e2 := addCol_apply s' 0 B1
  generalize B1 * (1 + vecMulVec (Pi.single (0 : Fin (n + 1)) (1 : R)) s') = B2 at hAB2 e2
  have h2_00 : B2 0 0 = b := by rw [e2]; simp [s', h1_00]
  have h2_c : ∀ i : Fin n, B2 i.succ 0 = 0 := by
    intro i
    rw [e2, h1_c]
    simp
  have h2_r : ∀ k : Fin n, B2 0 k.succ = 0 := by
    intro k
    rw [e2, hs, h1_00]
    simp [s', Fin.succ_ne_zero]
  refine ⟨b, B2.submatrix Fin.succ Fin.succ, ?_, ?_⟩
  · have h := eq_blk B2 h2_r h2_c
    rw [h2_00] at h
    rw [← h]
    exact hAB2
  · intro i k
    have hU3 : IsUnit (1 + vecMulVec (Pi.single (0 : Fin (n + 1)) (1 : R)) (Pi.single i.succ 1)) :=
      isUnit_one_add_vecMulVec _ _ (by simp [Fin.succ_ne_zero])
    have e3 := addRow_apply (Pi.single (0 : Fin (n + 1)) (1 : R)) i.succ B2
    have h := hrow _ (hAB2.mul_left hU3) (by rw [e3]; simp [h2_00, h2_c]) k.succ
    rw [e3] at h
    simpa [h2_r] using h

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `A`. Use `⟨fun i => i.elim0, ?_, fun i => i.elim0⟩` and prove the remaining obligations. Establish `e : A = diagonal (fun i : Fin 0 => i.elim0)`.

Use extensionality with `i`. Conclude with `i.elim0`. Rewrite using `[← e]`. Conclude with `Eqv.refl A`. Consider the case `succ n ih`.

Introduce `A`. Take `⟨b, D, hAD, hbD⟩` from `exists_blk A`. Take `⟨d, hD, hd⟩` from `ih D`. Take `⟨U, V, hU, hV, hUV⟩` from `hD`. Establish `hbd : ∀ i, b ∣ d i`.

Introduce `i`. Establish `h` using `congrFun (congrFun hUV i) i`. Rewrite `h` using `[Matrix.diagonal_apply_eq]`. Rewrite using `[← h, Matrix.mul_apply]`. Use `Finset.dvd_sum fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.mul_apply, Finset.sum_mul]`. Use `Finset.dvd_sum fun m _ => ?_` and prove the remaining obligations. Conclude with `Dvd.dvd.mul_right (Dvd.dvd.mul_left (hbD m l) _) _`. Establish `eb : blk b (diagonal d) = diagonal (Fin.cons b d : Fin (n + 1) → R)`. Use extensionality with `a c`.

Consider the cases of `a using Fin.cases with`. Consider the case `zero`. Consider the cases of `c using Fin.cases with`. Consider the case `zero => simp`. Consider the case `succ k => simp [Matrix.diagonal_apply, (Fin.succ_ne_zero k).symm]`.

Consider the case `succ i`. Consider the cases of `c using Fin.cases with`. Consider the case `zero => simp [Matrix.diagonal_apply, Fin.succ_ne_zero]`. Consider the case `succ k => simp [Matrix.diagonal_apply, Fin.succ_inj]`. Use `⟨Fin.cons b d, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← eb]`. Conclude with `hAD.trans (Eqv.blk ⟨U, V, hU, hV, hUV⟩ b)`. Introduce `i j hij`. Consider the cases of `i using Fin.cases with`. Consider the case `zero`.

Consider the cases of `j using Fin.cases with`. Consider the case `zero => exact dvd_refl _`. Consider the case `succ j' => simpa using hbd j'`. Consider the case `succ i'`. Consider the cases of `j using Fin.cases with`.

Consider the case `zero => exact absurd hij (by simp [Fin.succ_ne_zero])`. Consider the case `succ j' => simpa using hd i' j' (Fin.succ_le_succ_iff.mp hij)`.
-/
theorem smith (n : ℕ) : ∀ A : Matrix (Fin n) (Fin n) R,
    ∃ d : Fin n → R, Eqv A (diagonal d) ∧ ∀ i j, i ≤ j → d i ∣ d j := by
  induction n with
  | zero =>
    intro A
    refine ⟨fun i => i.elim0, ?_, fun i => i.elim0⟩
    have e : A = diagonal (fun i : Fin 0 => i.elim0) := by
      ext i
      exact i.elim0
    rw [← e]
    exact Eqv.refl A
  | succ n ih =>
    intro A
    obtain ⟨b, D, hAD, hbD⟩ := exists_blk A
    obtain ⟨d, hD, hd⟩ := ih D
    obtain ⟨U, V, hU, hV, hUV⟩ := hD
    have hbd : ∀ i, b ∣ d i := by
      intro i
      have h := congrFun (congrFun hUV i) i
      rw [Matrix.diagonal_apply_eq] at h
      rw [← h, Matrix.mul_apply]
      refine Finset.dvd_sum fun l _ => ?_
      rw [Matrix.mul_apply, Finset.sum_mul]
      refine Finset.dvd_sum fun m _ => ?_
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (hbD m l) _) _
    have eb : blk b (diagonal d) = diagonal (Fin.cons b d : Fin (n + 1) → R) := by
      ext a c
      cases a using Fin.cases with
      | zero =>
        cases c using Fin.cases with
        | zero => simp
        | succ k => simp [Matrix.diagonal_apply, (Fin.succ_ne_zero k).symm]
      | succ i =>
        cases c using Fin.cases with
        | zero => simp [Matrix.diagonal_apply, Fin.succ_ne_zero]
        | succ k => simp [Matrix.diagonal_apply, Fin.succ_inj]
    refine ⟨Fin.cons b d, ?_, ?_⟩
    · rw [← eb]
      exact hAD.trans (Eqv.blk ⟨U, V, hU, hV, hUV⟩ b)
    · intro i j hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact dvd_refl _
        | succ j' => simpa using hbd j'
      | succ i' =>
        cases j using Fin.cases with
        | zero => exact absurd hij (by simp [Fin.succ_ne_zero])
        | succ j' => simpa using hd i' j' (Fin.succ_le_succ_iff.mp hij)

end PI.SmithWork
