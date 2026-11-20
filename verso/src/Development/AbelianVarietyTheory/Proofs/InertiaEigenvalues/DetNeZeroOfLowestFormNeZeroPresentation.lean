import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetMemSpanAdjugate

open Matrix GlobalTheory.NewPrime

namespace GlobalTheory.LowDet

section
variable {R m n : Type} [CommRing R]

/- English proof (translation)
Simplify using `only [what₂, Matrix.vecMul_eq_sum]`. Conclude with `Submodule.mem_span_range_iff_exists_fun R`.
-/
theorem mem_rows [Fintype m] (M : Matrix m n R) (v : n → R) : v ∈ what₂ M ↔ ∃ z, z ᵥ* M = v := by
  simp only [what₂, Matrix.vecMul_eq_sum]
  exact Submodule.mem_span_range_iff_exists_fun R

/- English proof (translation)
Use `set Q : Submodule R (n → R) := what₂ P with hQ`. Establish `hrow : ∀ i, (T * G) i = T i ᵥ* G`. Introduce `i`. Use function extensionality and compare the values at `c`. Simplify using `[Matrix.mul_apply, Matrix.vecMul, dotProduct]`.

Establish `hq : Function.Surjective (Q.mkQ ∘ₗ Matrix.vecMulLinear G)`. Introduce `q`. Take `⟨v, rfl⟩` from `Q.mkQ_surjective q`. Take `⟨w, z, hv⟩` from `hG v`. Use `⟨w, ?_⟩` and prove the remaining obligations.

Use `show Q.mkQ (w ᵥ* G) = Q.mkQ v`. Rewrite using `[Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hv, show w ᵥ* G - (w ᵥ* G + z ᵥ* P) = -(z ᵥ* P) by abel]`. Conclude with `Q.neg_mem ((mem_rows P _).2 ⟨z, rfl⟩)`. Establish `hΦ : ∀ v, Q.mkQ v = 0 → ∃ z, Pᵀ *ᵥ z = v`. Introduce `v hv`.

Rewrite `hv` using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Take `⟨z, hz⟩` from `(mem_rows P v).1 hv`. Conclude with `⟨z, by rw [Matrix.mulVec_transpose, hz]⟩`. Establish `hT' : ∀ v, (Q.mkQ ∘ₗ Matrix.vecMulLinear G) (Tᵀ *ᵥ v) = 0`. Introduce `v`.

Use `show Q.mkQ ((Tᵀ *ᵥ v) ᵥ* G) = 0`. Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Matrix.mulVec_transpose, Matrix.vecMul_vecMul, Matrix.vecMul_eq_sum]`. Use `Q.sum_mem fun i _ => Q.smul_mem _ ?_` and prove the remaining obligations. Rewrite using `[hrow]`. Conclude with `hT i`.

Establish `h` using `(GlobalTheory.FitSquare.relations_mem Q.mkQ Q.mkQ_surjective Pᵀ hΦ _ hq Tᵀ hT').1`. Rewrite `h` using `[Matrix.det_transpose, Matrix.det_transpose, h0, Ideal.mem_span_singleton, zero_dvd_iff]`. Conclude with `h`.
-/
theorem det_relations [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (P : Matrix n n R) (G : Matrix m n R)
    (T : Matrix m m R) (hG : ∀ v, ∃ w z, v = w ᵥ* G + z ᵥ* P) (hT : ∀ i, T i ᵥ* G ∈ what₂ P) (h0 : P.det = 0) :
    T.det = 0 := by
  classical
  set Q : Submodule R (n → R) := what₂ P with hQ
  have hrow : ∀ i, (T * G) i = T i ᵥ* G := by
    intro i; funext c; simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
  have hq : Function.Surjective (Q.mkQ ∘ₗ Matrix.vecMulLinear G) := by
    intro q
    obtain ⟨v, rfl⟩ := Q.mkQ_surjective q
    obtain ⟨w, z, hv⟩ := hG v
    refine ⟨w, ?_⟩
    show Q.mkQ (w ᵥ* G) = Q.mkQ v
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hv,
      show w ᵥ* G - (w ᵥ* G + z ᵥ* P) = -(z ᵥ* P) by abel]
    exact Q.neg_mem ((mem_rows P _).2 ⟨z, rfl⟩)
  have hΦ : ∀ v, Q.mkQ v = 0 → ∃ z, Pᵀ *ᵥ z = v := by
    intro v hv
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hv
    obtain ⟨z, hz⟩ := (mem_rows P v).1 hv
    exact ⟨z, by rw [Matrix.mulVec_transpose, hz]⟩
  have hT' : ∀ v, (Q.mkQ ∘ₗ Matrix.vecMulLinear G) (Tᵀ *ᵥ v) = 0 := by
    intro v
    show Q.mkQ ((Tᵀ *ᵥ v) ᵥ* G) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Matrix.mulVec_transpose,
      Matrix.vecMul_vecMul, Matrix.vecMul_eq_sum]
    refine Q.sum_mem fun i _ => Q.smul_mem _ ?_
    rw [hrow]
    exact hT i
  have h := (GlobalTheory.FitSquare.relations_mem Q.mkQ Q.mkQ_surjective Pᵀ hΦ _ hq Tᵀ hT').1
  rw [Matrix.det_transpose, Matrix.det_transpose, h0, Ideal.mem_span_singleton, zero_dvd_iff] at h
  exact h

/- English proof (translation)
Establish `key : ∀ (S : Finset m) (N : m → n → R), f (N + x • S.piecewise V 0) = f N + x * ∑ i ∈ S, f (Function.update N i (V i))`. Introduce `S`. Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => intro N`. Simplify using the standard rewrite rules.

Consider the case `insert a S ha ih`. Introduce `N`. Establish `e : N + x • (insert a S).piecewise V 0 = Function.update N a (N a + x • V a) + x • S.piecewise V 0`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : i = a`.

Substitute `hi` using the available equality. Simplify using `[ha]`. Simplify using `[Finset.piecewise_insert, hi]`. Establish `h1 : f (Function.update N a (N a + x • V a)) = f N + x * f (Function.update N a (V a))`. Rewrite using `[f.map_update_add, f.map_update_smul, Function.update_eq_self, smul_eq_mul]`.

Establish `h2 : ∀ i ∈ S, x * f (Function.update (Function.update N a (N a + x • V a)) i (V i)) = x * f (Function.update N i (V i))`. Introduce `i hi`. Establish `hia : a ≠ i` using `fun h => ha (h ▸ hi)`. Rewrite using `[Function.update_comm hia, f.map_update_add, f.map_update_smul, smul_eq_mul, mul_add, ← mul_assoc, hx, zero_mul, add_zero]`. Use `congr 2`.

Use `conv_rhs => rw [← Function.update_eq_self a (Function.update N i (V i))]`. Rewrite using `[Function.update_of_ne hia]`. Rewrite using `[e, ih, h1, Finset.sum_insert ha, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.sum_congr rfl h2]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `using key Finset.univ M`.
-/
theorem multilinear_add_smul [Fintype m] [DecidableEq m] (f : MultilinearMap R (fun _ : m => n → R) R)
    (M V : m → n → R) (x : R) (hx : x * x = 0) :
    f (M + x • V) = f M + x * ∑ i, f (Function.update M i (V i)) := by
  classical
  have key : ∀ (S : Finset m) (N : m → n → R),
      f (N + x • S.piecewise V 0) = f N + x * ∑ i ∈ S, f (Function.update N i (V i)) := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro N; simp
    | insert a S ha ih =>
      intro N
      have e : N + x • (insert a S).piecewise V 0 =
          Function.update N a (N a + x • V a) + x • S.piecewise V 0 := by
        funext i
        by_cases hi : i = a
        · subst hi; simp [ha]
        · simp [Finset.piecewise_insert, hi]
      have h1 : f (Function.update N a (N a + x • V a)) = f N + x * f (Function.update N a (V a)) := by
        rw [f.map_update_add, f.map_update_smul, Function.update_eq_self, smul_eq_mul]
      have h2 : ∀ i ∈ S, x * f (Function.update (Function.update N a (N a + x • V a)) i (V i)) =
          x * f (Function.update N i (V i)) := by
        intro i hi
        have hia : a ≠ i := fun h => ha (h ▸ hi)
        rw [Function.update_comm hia, f.map_update_add, f.map_update_smul, smul_eq_mul, mul_add,
          ← mul_assoc, hx, zero_mul, add_zero]
        congr 2
        conv_rhs => rw [← Function.update_eq_self a (Function.update N i (V i))]
        rw [Function.update_of_ne hia]
      rw [e, ih, h1, Finset.sum_insert ha, mul_add, Finset.mul_sum, Finset.mul_sum,
        Finset.sum_congr rfl h2]
      ring
  simpa using key Finset.univ M

/- English proof (translation)
Conclude with `multilinear_add_smul (Matrix.detRowAlternating : (m → R) [⋀^m]→ₗ[R] R).toMultilinearMap M V x hx`.
-/
theorem det_add_smul [Fintype m] [DecidableEq m] (M V : Matrix m m R) (x : R) (hx : x * x = 0) :
    (M + x • V).det = M.det + x * ∑ i, (M.updateRow i (V i)).det := by
  exact multilinear_add_smul (Matrix.detRowAlternating : (m → R) [⋀^m]→ₗ[R] R).toMultilinearMap M V x hx

/- English proof (translation)
Establish `hrow : ∀ (A : Matrix m m R) (i : m) (b : m → R), (A.updateRow i b).det = ∑ c, b c * A.adjugate c i`. Introduce `A i b`. Rewrite using `[Matrix.det_eq_sum_mul_adjugate_row _ i]`. Simplify using `[Matrix.adjugate_apply, Matrix.updateRow_idem]`. Establish `hrow1 : ((1 : Matrix n n R).updateRow j k).det = k j`.

Rewrite using `[Matrix.det_eq_sum_mul_adjugate_row _ j]`. Simplify using `only [Matrix.updateRow_self, Matrix.adjugate_apply, Matrix.updateRow_idem]`. Simplify using `only [← Matrix.adjugate_apply, Matrix.adjugate_one, Matrix.one_apply]`. Simplify using the standard rewrite rules. Use `set M := (fromBlocks (Φ.updateRow l 0) (C.updateRow l k) 0 1).updateRow (Sum.inr j) (Sum.elim U U') with hM`.

Establish `hsw : M.submatrix (Equiv.swap (Sum.inl l) (Sum.inr j)) id = fromBlocks (Φ.updateRow l U) (C.updateRow l U') 0 ((1 : Matrix n n R).updateRow j k)`. Apply the tactic sequence `ext (a | a) (b | b) <;>`. Apply the tactic sequence `simp [hM, Equiv.swap_apply_def, Matrix.updateRow_apply, Matrix.one_apply] <;>`. Apply the tactic sequence `split_ifs <;> simp_all`. Establish `h1` using `Matrix.det_permute (Equiv.swap (Sum.inl l) (Sum.inr j)) M`.

Rewrite `h1` using `[hsw, Matrix.det_fromBlocks_zero₂₁, Equiv.Perm.sign_swap (by simp), hrow, hrow1]`. Simplify using `at h1`. Take the linear combination `h1`.
-/
theorem det_block [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (Φ : Matrix m m R) (C : Matrix m n R)
    (l : m) (j : n) (k U' : n → R) (U : m → R) :
    ((fromBlocks (Φ.updateRow l 0) (C.updateRow l k) 0 1).updateRow (Sum.inr j) (Sum.elim U U')).det
      = - (k j * ∑ c, U c * Φ.adjugate c l) := by
  classical
  have hrow : ∀ (A : Matrix m m R) (i : m) (b : m → R), (A.updateRow i b).det = ∑ c, b c * A.adjugate c i := by
    intro A i b
    rw [Matrix.det_eq_sum_mul_adjugate_row _ i]
    simp [Matrix.adjugate_apply, Matrix.updateRow_idem]
  have hrow1 : ((1 : Matrix n n R).updateRow j k).det = k j := by
    rw [Matrix.det_eq_sum_mul_adjugate_row _ j]
    simp only [Matrix.updateRow_self, Matrix.adjugate_apply, Matrix.updateRow_idem]
    simp only [← Matrix.adjugate_apply, Matrix.adjugate_one, Matrix.one_apply]
    simp
  set M := (fromBlocks (Φ.updateRow l 0) (C.updateRow l k) 0 1).updateRow (Sum.inr j) (Sum.elim U U') with hM
  have hsw : M.submatrix (Equiv.swap (Sum.inl l) (Sum.inr j)) id =
      fromBlocks (Φ.updateRow l U) (C.updateRow l U') 0 ((1 : Matrix n n R).updateRow j k) := by
    ext (a | a) (b | b) <;>
      simp [hM, Equiv.swap_apply_def, Matrix.updateRow_apply, Matrix.one_apply] <;>
      split_ifs <;> simp_all
  have h1 := Matrix.det_permute (Equiv.swap (Sum.inl l) (Sum.inr j)) M
  rw [hsw, Matrix.det_fromBlocks_zero₂₁, Equiv.Perm.sign_swap (by simp), hrow, hrow1] at h1
  simp at h1
  linear_combination h1

end

section
variable {A B m n : Type} [CommRing A] [CommRing B] [Fintype m] [Fintype n] (π : B →+* A) (x y : B)
  (hπ : Function.Surjective π) (hker : ∀ b, π b = 0 → b ∈ Ideal.span {x, y}) (G : Matrix m n B) (P : Matrix n n B)

include hπ hker in
/- English proof (translation)
Take `⟨z₀, hz₀⟩` from `(mem_rows _ _).1 h`. Use `set s := Function.surjInv hπ`. Establish `hs : ∀ a, π (s a) = a` using `Function.surjInv_eq hπ`. Establish `hsw : π ∘ (s ∘ w₀) = w₀` using `funext fun i => hs _`. Establish `hsz : π ∘ (s ∘ z₀) = z₀` using `funext fun i => hs _`.

Establish `hr : ∀ c, v c - (s ∘ w₀ ᵥ* G) c - (s ∘ z₀ ᵥ* P) c ∈ Ideal.span {x, y}`. Introduce `c`. Apply `hker` to reduce the goal to its premises. Establish `e` using `congrFun hz₀ c`. Simplify using `only [Pi.sub_apply, Function.comp_apply] at e`.

Rewrite using `[map_sub, map_sub, RingHom.map_vecMul, RingHom.map_vecMul, hsw, hsz]`. Take the linear combination `-e`. Use `choose p q hpq using fun c => Ideal.mem_span_pair.1 (hr c)`. Use `⟨s ∘ w₀, s ∘ z₀, p, q, hsw, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `c`.

Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Take the linear combination `-(hpq c)`.
-/
theorem lift_mod (v : n → B) (w₀ : m → A) (h : π ∘ v - w₀ ᵥ* G.map π ∈ what₂ (P.map π)) :
    ∃ w z p q, π ∘ w = w₀ ∧ v = w ᵥ* G + z ᵥ* P + (x • p + y • q) := by
  classical
  obtain ⟨z₀, hz₀⟩ := (mem_rows _ _).1 h
  set s := Function.surjInv hπ
  have hs : ∀ a, π (s a) = a := Function.surjInv_eq hπ
  have hsw : π ∘ (s ∘ w₀) = w₀ := funext fun i => hs _
  have hsz : π ∘ (s ∘ z₀) = z₀ := funext fun i => hs _
  have hr : ∀ c, v c - (s ∘ w₀ ᵥ* G) c - (s ∘ z₀ ᵥ* P) c ∈ Ideal.span {x, y} := by
    intro c
    apply hker
    have e := congrFun hz₀ c
    simp only [Pi.sub_apply, Function.comp_apply] at e
    rw [map_sub, map_sub, RingHom.map_vecMul, RingHom.map_vecMul, hsw, hsz]
    linear_combination -e
  choose p q hpq using fun c => Ideal.mem_span_pair.1 (hr c)
  refine ⟨s ∘ w₀, s ∘ z₀, p, q, hsw, ?_⟩
  funext c
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination -(hpq c)

include hπ hker in
/- English proof (translation)
Establish `hI : Ideal.span {x, y} ≤ Ideal.jacobson ⊥`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `b (rfl | rfl)`. Conclude with `Ideal.radical_le_jacobson (mem_nilradical.2 hx)`. Conclude with `Ideal.radical_le_jacobson (mem_nilradical.2 hy)`.

Establish `htop : (⊤ : Submodule B (n → B)) ≤ what₂ G ⊔ what₂ P`. Apply `Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hI` to reduce the goal to its premises. Introduce `v _`. Take `⟨w₀, hw₀⟩` from `h (π ∘ v)`. Take `⟨w, z, p, q, -, hv⟩` from `lift_mod π x y hπ hker G P v w₀ hw₀`.

Rewrite using `[hv]`. Use `add_mem (add_mem ?_ ?_) (add_mem ?_ ?_)` and prove the remaining obligations. Conclude with `Submodule.mem_sup_left (Submodule.mem_sup_left ((mem_rows G _).2 ⟨w, rfl⟩))`. Conclude with `Submodule.mem_sup_left (Submodule.mem_sup_right ((mem_rows P _).2 ⟨z, rfl⟩))`. Conclude with `Submodule.mem_sup_right (Submodule.smul_mem_smul (Ideal.subset_span (by simp)) Submodule.mem_top)`.

Conclude with `Submodule.mem_sup_right (Submodule.smul_mem_smul (Ideal.subset_span (by simp)) Submodule.mem_top)`. Take `⟨a, ha, b, hb, hab⟩` from `Submodule.mem_sup.1 (htop Submodule.mem_top : v ∈ what₂ G ⊔ what₂ P)`. Take `⟨w, rfl⟩` from `(mem_rows G a).1 ha`. Take `⟨z, rfl⟩` from `(mem_rows P b).1 hb`. Conclude with `⟨w, z, hab.symm⟩`.
-/
theorem generate (hx : IsNilpotent x) (hy : IsNilpotent y)
    (h : ∀ v₀ : n → A, ∃ w₀, v₀ - w₀ ᵥ* G.map π ∈ what₂ (P.map π)) (v : n → B) :
    ∃ w z, v = w ᵥ* G + z ᵥ* P := by
  classical
  have hI : Ideal.span {x, y} ≤ Ideal.jacobson ⊥ := by
    rw [Ideal.span_le]
    rintro b (rfl | rfl)
    · exact Ideal.radical_le_jacobson (mem_nilradical.2 hx)
    · exact Ideal.radical_le_jacobson (mem_nilradical.2 hy)
  have htop : (⊤ : Submodule B (n → B)) ≤ what₂ G ⊔ what₂ P := by
    apply Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hI
    intro v _
    obtain ⟨w₀, hw₀⟩ := h (π ∘ v)
    obtain ⟨w, z, p, q, -, hv⟩ := lift_mod π x y hπ hker G P v w₀ hw₀
    rw [hv]
    refine add_mem (add_mem ?_ ?_) (add_mem ?_ ?_)
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left ((mem_rows G _).2 ⟨w, rfl⟩))
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right ((mem_rows P _).2 ⟨z, rfl⟩))
    · exact Submodule.mem_sup_right
        (Submodule.smul_mem_smul (Ideal.subset_span (by simp)) Submodule.mem_top)
    · exact Submodule.mem_sup_right
        (Submodule.smul_mem_smul (Ideal.subset_span (by simp)) Submodule.mem_top)
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (htop Submodule.mem_top : v ∈ what₂ G ⊔ what₂ P)
  obtain ⟨w, rfl⟩ := (mem_rows G a).1 ha
  obtain ⟨z, rfl⟩ := (mem_rows P b).1 hb
  exact ⟨w, z, hab.symm⟩

include hπ hker in
/- English proof (translation)
Take `⟨w', z', p, q, hw', hv⟩` from `lift_mod π x y hπ hker G P v w₀ h`. Take `⟨a, b, hab⟩` from `hG p`. Take `⟨c, d, hcd⟩` from `hG q`. Use `⟨w' + x • a + y • c, ?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Simplify using `[hx, hy, ← hw']`. Rewrite using `[mem_rows]`. Use `⟨z' + x • b + y • d, ?_⟩` and prove the remaining obligations. Rewrite using `[hv, hab, hcd]`. Simplify using `only [Matrix.add_vecMul, Matrix.smul_vecMul, smul_add]`.

Normalize the expressions using the abelian group laws.
-/
theorem lift_exact (hx : π x = 0) (hy : π y = 0) (hG : ∀ v, ∃ w z, v = w ᵥ* G + z ᵥ* P)
    (v : n → B) (w₀ : m → A) (h : π ∘ v - w₀ ᵥ* G.map π ∈ what₂ (P.map π)) :
    ∃ w, π ∘ w = w₀ ∧ v - w ᵥ* G ∈ what₂ P := by
  obtain ⟨w', z', p, q, hw', hv⟩ := lift_mod π x y hπ hker G P v w₀ h
  obtain ⟨a, b, hab⟩ := hG p
  obtain ⟨c, d, hcd⟩ := hG q
  refine ⟨w' + x • a + y • c, ?_, ?_⟩
  · funext i
    simp [hx, hy, ← hw']
  · rw [mem_rows]
    refine ⟨z' + x • b + y • d, ?_⟩
    rw [hv, hab, hcd]
    simp only [Matrix.add_vecMul, Matrix.smul_vecMul, smul_add]
    abel

end

section
variable {B m μ : Type} [CommRing B] [Fintype m] [DecidableEq m] [Fintype μ] [DecidableEq μ]

/- English proof (translation)
Use `set E := fromRows D (fromCols (0 : Matrix μ m B) (1 : Matrix μ μ B)) with hE`. Use `set ν : m ⊕ μ → B := Sum.elim (fun _ => 1) (fun _ => y) with hν`. Establish `hsplit : fromRows D (y • fromCols (0 : Matrix μ m B) 1 + x • w) = fromRows D (y • fromCols (0 : Matrix μ m B) 1) + x • fromRows (0 : Matrix m (m ⊕ μ) B) w`. Apply the tactic sequence `ext (i | i) c <;> simp`. Establish `hM : fromRows D (y • fromCols (0 : Matrix μ m B) 1) = of fun i c => ν i * E i c`.

Apply the tactic sequence `ext (i | i) c <;> simp [hν, hE]`. Establish `hprod : ∏ i, ν i = y ^ Fintype.card μ`. Simplify using `[hν, Fintype.prod_sum_type]`. Establish `h0 : ∀ b : m, ((of fun i c => ν i * E i c).updateRow (Sum.inl b) ((fromRows (0 : Matrix m (m ⊕ μ) B) w) (Sum.inl b))).det = 0`. Introduce `b`.

Apply `Matrix.det_eq_zero_of_row_eq_zero (Sum.inl b)` to reduce the goal to its premises. Introduce `c`. Simplify using the standard rewrite rules. Establish `h1 : ∀ j : μ, ((of fun i c => ν i * E i c).updateRow (Sum.inr j) ((fromRows (0 : Matrix m (m ⊕ μ) B) w) (Sum.inr j))).det = y ^ (Fintype.card μ - 1) * (E.updateRow (Sum.inr j) (w j)).det`. Introduce `j`.

Establish `e : (of fun i c => ν i * E i c).updateRow (Sum.inr j) ((fromRows (0 : Matrix m (m ⊕ μ) B) w) (Sum.inr j)) = of fun i c => Function.update ν (Sum.inr j) 1 i * (E.updateRow (Sum.inr j) (w j)) i c`. Use extensionality with `i c`. Distinguish the cases in `hi : i = Sum.inr j`. Substitute `hi` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Matrix.updateRow_ne hi, Function.update_of_ne hi]`. Rewrite using `[e, Matrix.det_mul_column]`. Use `congr 1`. Rewrite using `[Fintype.prod_sum_type]`. Simplify using `only [hν, Function.update_apply, reduceCtorEq, if_false, Sum.elim_inl, Sum.elim_inr, Finset.prod_const_one, one_mul, Sum.inr.injEq]`.

Rewrite using `[Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]`. Use `congr 1`. Simplify using `[Finset.filter_ne', Finset.card_erase_of_mem]`. Rewrite using `[hsplit, det_add_smul _ _ x hx, hM, Matrix.det_mul_column, hprod, hy, zero_mul, zero_add, Fintype.sum_sum_type, Finset.sum_congr rfl (fun b _ => h0 b), Finset.sum_const_zero, zero_add, Finset.sum_congr rfl (fun j _ => h1 j), ← Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_expand (x y : B) (hx : x * x = 0) (hy : y ^ Fintype.card μ = 0) (D : Matrix m (m ⊕ μ) B)
    (w : Matrix μ (m ⊕ μ) B) :
    (fromRows D (y • fromCols 0 1 + x • w)).det = x * y ^ (Fintype.card μ - 1) *
      ∑ j, ((fromRows D (fromCols 0 1)).updateRow (Sum.inr j) (w j)).det := by
  classical
  set E := fromRows D (fromCols (0 : Matrix μ m B) (1 : Matrix μ μ B)) with hE
  set ν : m ⊕ μ → B := Sum.elim (fun _ => 1) (fun _ => y) with hν
  have hsplit : fromRows D (y • fromCols (0 : Matrix μ m B) 1 + x • w) =
      fromRows D (y • fromCols (0 : Matrix μ m B) 1) + x • fromRows (0 : Matrix m (m ⊕ μ) B) w := by
    ext (i | i) c <;> simp
  have hM : fromRows D (y • fromCols (0 : Matrix μ m B) 1) = of fun i c => ν i * E i c := by
    ext (i | i) c <;> simp [hν, hE]
  have hprod : ∏ i, ν i = y ^ Fintype.card μ := by
    simp [hν, Fintype.prod_sum_type]
  have h0 : ∀ b : m, ((of fun i c => ν i * E i c).updateRow (Sum.inl b)
      ((fromRows (0 : Matrix m (m ⊕ μ) B) w) (Sum.inl b))).det = 0 := by
    intro b
    apply Matrix.det_eq_zero_of_row_eq_zero (Sum.inl b)
    intro c
    simp
  have h1 : ∀ j : μ, ((of fun i c => ν i * E i c).updateRow (Sum.inr j)
      ((fromRows (0 : Matrix m (m ⊕ μ) B) w) (Sum.inr j))).det =
      y ^ (Fintype.card μ - 1) * (E.updateRow (Sum.inr j) (w j)).det := by
    intro j
    have e : (of fun i c => ν i * E i c).updateRow (Sum.inr j)
        ((fromRows (0 : Matrix m (m ⊕ μ) B) w) (Sum.inr j)) =
        of fun i c => Function.update ν (Sum.inr j) 1 i * (E.updateRow (Sum.inr j) (w j)) i c := by
      ext i c
      by_cases hi : i = Sum.inr j
      · subst hi; simp
      · simp [Matrix.updateRow_ne hi, Function.update_of_ne hi]
    rw [e, Matrix.det_mul_column]
    congr 1
    rw [Fintype.prod_sum_type]
    simp only [hν, Function.update_apply, reduceCtorEq, if_false, Sum.elim_inl, Sum.elim_inr,
      Finset.prod_const_one, one_mul, Sum.inr.injEq]
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
    congr 1
    simp [Finset.filter_ne', Finset.card_erase_of_mem]
  rw [hsplit, det_add_smul _ _ x hx, hM, Matrix.det_mul_column, hprod, hy, zero_mul, zero_add,
    Fintype.sum_sum_type, Finset.sum_congr rfl (fun b _ => h0 b), Finset.sum_const_zero, zero_add,
    Finset.sum_congr rfl (fun j _ => h1 j), ← Finset.mul_sum]
  ring

end

/- English proof (translation)
Introduce `A B _ _ π x y μ _ a a' Φ' u t η Φ E U k l₀ hπ hker hx0 hy0 hx hy hann hη hrel hgen hΦE hu hk hne hdet`. Use `set s := Function.surjInv hπ`. Establish `hs : ∀ a, π (s a) = a` using `Function.surjInv_eq hπ`. Use `set tπ : Matrix μ (Fin a') A := fun j c => π (t j c) with htπ`. Use `set G : Matrix (Fin a ⊕ μ) (Fin a') B := fromRows (fun b c => s (E b c)) (fun j c => η j * t j c) with hGdef`.

Establish `hGπ : G.map π = fromRows E tπ`. Use extensionality with `(i | i) c`. Conclude with `hs (E i c)`. Use `show π (η i * t i c) = π (t i c)`. Rewrite using `[map_mul, hη, one_mul]`.

Establish `hgen' : ∀ v₀ : Fin a' → A, ∃ w₀ : Fin a ⊕ μ → A, v₀ - w₀ ᵥ* G.map π ∈ what₂ (Φ'.map π)`. Introduce `v₀`. Establish `hv : v₀ ∈ what₂ E ⊔ (what₂ (Φ'.map π) ⊔ what₂ tπ)` using `hgen ▸ Submodule.mem_top`. Take `⟨e, he, f, hf, rfl⟩` from `Submodule.mem_sup.1 hv`. Take `⟨g, hg, h, hh, rfl⟩` from `Submodule.mem_sup.1 hf`.

Take `⟨α, rfl⟩` from `(mem_rows E e).1 he`. Take `⟨β, rfl⟩` from `(mem_rows tπ h).1 hh`. Use `⟨Sum.elim α β, ?_⟩` and prove the remaining obligations. Rewrite using `[hGπ, Matrix.sumElim_vecMul_fromRows]`. Use `hg using 1` and compare the differences between its conclusion and the goal.

Normalize the expressions using the abelian group laws. Establish `hG : ∀ v, ∃ w z, v = w ᵥ* G + z ᵥ* Φ'` using `fun v => generate π x y hπ hker G Φ' ⟨2, by rw [pow_two]; exact hx⟩ ⟨_, hy⟩ hgen' v`. Establish `hr : ∀ b, ∃ r : μ → A, Φ b ᵥ* E - r ᵥ* tπ ∈ what₂ (Φ'.map π)`. Introduce `b`. Take `⟨f, hf, g, hg, hfg⟩` from `Submodule.mem_sup.1 (hΦE b)`.

Take `⟨r, rfl⟩` from `(mem_rows tπ g).1 hg`. Use `⟨r, ?_⟩` and prove the remaining obligations. Establish `e : (Φ * E) b = Φ b ᵥ* E`. Use function extensionality and compare the values at `c`. Simplify using `[Matrix.mul_apply, Matrix.vecMul, dotProduct]`.

Rewrite using `[← e, ← hfg, add_sub_cancel_right]`. Conclude with `hf`. Use `choose r hr using hr`. Use `set C : Matrix (Fin a) μ A := fun b => -r b with hC`. Establish `hD : ∀ b, ∃ d : Fin a ⊕ μ → B, π ∘ d = Sum.elim ((Φ.updateRow l₀ 0) b) ((C.updateRow l₀ k) b) ∧ d ᵥ* G ∈ what₂ Φ'`.

Introduce `b`. Establish `hmem : π ∘ (0 : Fin a' → B) - Sum.elim ((Φ.updateRow l₀ 0) b) ((C.updateRow l₀ k) b) ᵥ* G.map π ∈ what₂ (Φ'.map π)`. Rewrite using `[hGπ, Matrix.sumElim_vecMul_fromRows]`. Distinguish the cases in `hb : b = l₀`. Substitute `hb` using the available equality.

Use `neg_mem hk` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `[htπ]`. Conclude with `Matrix.vecMul_eq_sum _ _`. Use `neg_mem (hr b)` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[Matrix.updateRow_ne hb, Matrix.updateRow_ne hb]`. Use `show π ∘ (0 : Fin a' → B) - (Φ b ᵥ* E + (-r b) ᵥ* tπ) = -(Φ b ᵥ* E - r b ᵥ* tπ)`. Establish `h0 : π ∘ (0 : Fin a' → B) = 0` using `funext fun _ => map_zero π`. Rewrite using `[Matrix.neg_vecMul, h0]`.

Normalize the expressions using the abelian group laws. Take `⟨d, hd, hd'⟩` from `lift_exact π x y hπ hker G Φ' hx0 hy0 hG 0 _ hmem`. Use `⟨d, hd, ?_⟩` and prove the remaining obligations. Simplify using `using neg_mem hd'`. Use `choose D hDπ hD using hD`.

Establish `hσ : ∀ j, ∃ σ : μ → A, (fun c => π (u j c)) - U j ᵥ* E - σ ᵥ* tπ ∈ what₂ (Φ'.map π)`. Introduce `j`. Take `⟨f, hf, g, hg, hfg⟩` from `Submodule.mem_sup.1 (hu j)`. Take `⟨σ, rfl⟩` from `(mem_rows tπ g).1 hg`. Conclude with `⟨σ, by rw [← hfg, add_sub_cancel_right]; exact hf⟩`.

Use `choose σ hσ using hσ`. Establish `hW : ∀ j, ∃ wj : Fin a ⊕ μ → B, π ∘ wj = Sum.elim (U j) (σ j) ∧ u j - wj ᵥ* G ∈ what₂ Φ'`. Introduce `j`. Apply `lift_exact π x y hπ hker G Φ' hx0 hy0 hG (u j)` to reduce the goal to its premises. Rewrite using `[hGπ, Matrix.sumElim_vecMul_fromRows, ← sub_sub]`.

Conclude with `hσ j`. Use `choose W hWπ hW using hW`. Use `set W' : Matrix μ (Fin a ⊕ μ) B := Matrix.of fun j => -W j with hW'`. Use `set T : Matrix (Fin a ⊕ μ) (Fin a ⊕ μ) B := fromRows D (y • fromCols (0 : Matrix μ (Fin a) B) (1 : Matrix μ μ B) + x • W') with hTdef`. Establish `hT : ∀ i, T i ᵥ* G ∈ what₂ Φ'`.

Introduce and unpack `(b | j)`. Conclude with `hD b`. Establish `e1 : (fromCols (0 : Matrix μ (Fin a) B) (1 : Matrix μ μ B)) j = Pi.single (Sum.inr j) 1`. Use function extensionality and compare the values at `i`. Break down `i with i | i` into its components or cases.

Simplify using the standard rewrite rules. Distinguish the cases in `h : i = j`. Rewrite using `[h]`. Simplify using the standard rewrite rules. Simplify using `[h, Ne.symm h]`.

Establish `hTj : T (Sum.inr j) = y • Pi.single (Sum.inr j) 1 + x • (-W j)` using `by show y • (fromCols (0 : Matrix μ (Fin a) B) (1 : Matrix μ μ B)) j + x • W' j = _`. Rewrite using `[e1]`. Both sides reduce to the same expression. Establish `hGr : G.row (Sum.inr j) = η j • t j`. Use function extensionality and compare the values at `c`.

Both sides reduce to the same expression. Establish `e : T (Sum.inr j) ᵥ* G = -(x • u j - (y * η j) • t j) + x • (u j - W j ᵥ* G)`. Rewrite using `[hTj, Matrix.add_vecMul, Matrix.smul_vecMul, Matrix.smul_vecMul, Matrix.single_one_vecMul, Matrix.neg_vecMul, hGr]`. Use function extensionality and compare the values at `c`. Simplify using `only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.sub_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `add_mem (neg_mem (hrel j)) (Submodule.smul_mem _ x (hW j))`. Establish `hTdet` using `det_relations Φ' G T hG hT hdet`. Rewrite `hTdet` using `[hTdef, det_expand x y hx hy D W']`.

Apply `hne` to reduce the goal to its premises. Use `Eq.trans ?_ (hann _ hTdet)` and prove the remaining obligations. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `hN : π.mapMatrix ((fromRows D (fromCols (0 : Matrix μ (Fin a) B) (1 : Matrix μ μ B))).updateRow (Sum.inr j) (W' j)) = (fromBlocks (Φ.updateRow l₀ 0) (C.updateRow l₀ k) 0 1).updateRow (Sum.inr j) (Sum.elim (-U j) (-σ j))`.

Use extensionality with `(i | i) (c | c)`. Rewrite using `[RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.updateRow_ne Sum.inl_ne_inr, Matrix.updateRow_ne Sum.inl_ne_inr, Matrix.fromBlocks_apply₁₁]`. Conclude with `congrFun (hDπ i) (Sum.inl c)`. Rewrite using `[RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.updateRow_ne Sum.inl_ne_inr, Matrix.updateRow_ne Sum.inl_ne_inr, Matrix.fromBlocks_apply₁₂]`. Conclude with `congrFun (hDπ i) (Sum.inr c)`.

Distinguish the cases in `hi : i = j`. Rewrite using `[hi, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.updateRow_self, Matrix.updateRow_self] show π (-(W j (Sum.inl c))) = -(U j c)`. Rewrite using `[map_neg]`. Conclude with `congrArg Neg.neg (congrFun (hWπ j) (Sum.inl c))`. Establish `h : (Sum.inr i : Fin a ⊕ μ) ≠ Sum.inr j` using `fun h => hi (Sum.inr_injective h)`.

Rewrite using `[RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.updateRow_ne h, Matrix.updateRow_ne h, Matrix.fromBlocks_apply₂₁]`. Use `show π ((0 : Matrix μ (Fin a) B) i c) = (0 : Matrix μ (Fin a) A) i c`. Simplify using the standard rewrite rules. Distinguish the cases in `hi : i = j`. Rewrite using `[hi, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.updateRow_self, Matrix.updateRow_self] show π (-(W j (Sum.inr c))) = -(σ j c)`.

Rewrite using `[map_neg]`. Conclude with `congrArg Neg.neg (congrFun (hWπ j) (Sum.inr c))`. Establish `h : (Sum.inr i : Fin a ⊕ μ) ≠ Sum.inr j` using `fun h => hi (Sum.inr_injective h)`. Rewrite using `[RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.updateRow_ne h, Matrix.updateRow_ne h, Matrix.fromBlocks_apply₂₂]`. Use `show π ((1 : Matrix μ μ B) i c) = (1 : Matrix μ μ A) i c`.

Rewrite using `[Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[RingHom.map_det, hN, det_block]`. Simplify using `[Finset.sum_neg_distrib]`.
-/
theorem det_ne_zero : ∀ (A B : Type) [CommRing A] [CommRing B] (π : B →+* A) (x y : B) (μ : Type) [Fintype μ] (a a' : ℕ) (Φ' : Matrix (Fin a') (Fin a') B) (u t : μ → Fin a' → B) (η : μ → B) (Φ : Matrix (Fin a) (Fin a) A) (E : Matrix (Fin a) (Fin a') A) (U : μ → Fin a → A) (k : μ → A) (l₀ : Fin a), Function.Surjective π → (∀ b, π b = 0 → b ∈ Ideal.span {x, y}) → π x = 0 → π y = 0 → x * x = 0 → y ^ Fintype.card μ = 0 → (∀ f, x * y ^ (Fintype.card μ - 1) * f = 0 → π f = 0) → (∀ j, π (η j) = 1) → (∀ j, x • u j - (y * η j) • t j ∈ what₂ Φ') → what₂ E ⊔ (what₂ (Φ'.map π) ⊔ what₂ (fun j c => π (t j c))) = ⊤ → (∀ b, (Φ * E) b ∈ what₂ (Φ'.map π) ⊔ what₂ (fun j c => π (t j c))) → (∀ j, (fun c => π (u j c)) - Matrix.vecMul (U j) E ∈ what₂ (Φ'.map π) ⊔ what₂ (fun j c => π (t j c))) → ∑ j, k j • (fun c => π (t j c)) ∈ what₂ (Φ'.map π) → ∑ j, k j * ∑ c, U j c * Φ.adjugate c l₀ ≠ 0 → Φ'.det ≠ 0 := by
  classical
  intro A B _ _ π x y μ _ a a' Φ' u t η Φ E U k l₀ hπ hker hx0 hy0 hx hy hann hη hrel hgen hΦE hu hk hne hdet
  set s := Function.surjInv hπ
  have hs : ∀ a, π (s a) = a := Function.surjInv_eq hπ
  set tπ : Matrix μ (Fin a') A := fun j c => π (t j c) with htπ
  set G : Matrix (Fin a ⊕ μ) (Fin a') B := fromRows (fun b c => s (E b c)) (fun j c => η j * t j c) with hGdef
  have hGπ : G.map π = fromRows E tπ := by
    ext (i | i) c
    · exact hs (E i c)
    · show π (η i * t i c) = π (t i c)
      rw [map_mul, hη, one_mul]
  have hgen' : ∀ v₀ : Fin a' → A, ∃ w₀ : Fin a ⊕ μ → A, v₀ - w₀ ᵥ* G.map π ∈ what₂ (Φ'.map π) := by
    intro v₀
    have hv : v₀ ∈ what₂ E ⊔ (what₂ (Φ'.map π) ⊔ what₂ tπ) := hgen ▸ Submodule.mem_top
    obtain ⟨e, he, f, hf, rfl⟩ := Submodule.mem_sup.1 hv
    obtain ⟨g, hg, h, hh, rfl⟩ := Submodule.mem_sup.1 hf
    obtain ⟨α, rfl⟩ := (mem_rows E e).1 he
    obtain ⟨β, rfl⟩ := (mem_rows tπ h).1 hh
    refine ⟨Sum.elim α β, ?_⟩
    rw [hGπ, Matrix.sumElim_vecMul_fromRows]
    convert hg using 1
    abel
  have hG : ∀ v, ∃ w z, v = w ᵥ* G + z ᵥ* Φ' := fun v =>
    generate π x y hπ hker G Φ' ⟨2, by rw [pow_two]; exact hx⟩ ⟨_, hy⟩ hgen' v
  have hr : ∀ b, ∃ r : μ → A, Φ b ᵥ* E - r ᵥ* tπ ∈ what₂ (Φ'.map π) := by
    intro b
    obtain ⟨f, hf, g, hg, hfg⟩ := Submodule.mem_sup.1 (hΦE b)
    obtain ⟨r, rfl⟩ := (mem_rows tπ g).1 hg
    refine ⟨r, ?_⟩
    have e : (Φ * E) b = Φ b ᵥ* E := by
      funext c; simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
    rw [← e, ← hfg, add_sub_cancel_right]
    exact hf
  choose r hr using hr
  set C : Matrix (Fin a) μ A := fun b => -r b with hC
  have hD : ∀ b, ∃ d : Fin a ⊕ μ → B,
      π ∘ d = Sum.elim ((Φ.updateRow l₀ 0) b) ((C.updateRow l₀ k) b) ∧ d ᵥ* G ∈ what₂ Φ' := by
    intro b
    have hmem : π ∘ (0 : Fin a' → B) - Sum.elim ((Φ.updateRow l₀ 0) b) ((C.updateRow l₀ k) b) ᵥ* G.map π
        ∈ what₂ (Φ'.map π) := by
      rw [hGπ, Matrix.sumElim_vecMul_fromRows]
      by_cases hb : b = l₀
      · subst hb
        have := neg_mem hk
        convert this using 1
        simp [htπ]
        exact Matrix.vecMul_eq_sum _ _
      · have := neg_mem (hr b)
        convert this using 1
        rw [Matrix.updateRow_ne hb, Matrix.updateRow_ne hb]
        show π ∘ (0 : Fin a' → B) - (Φ b ᵥ* E + (-r b) ᵥ* tπ) = -(Φ b ᵥ* E - r b ᵥ* tπ)
        have h0 : π ∘ (0 : Fin a' → B) = 0 := funext fun _ => map_zero π
        rw [Matrix.neg_vecMul, h0]
        abel
    obtain ⟨d, hd, hd'⟩ := lift_exact π x y hπ hker G Φ' hx0 hy0 hG 0 _ hmem
    refine ⟨d, hd, ?_⟩
    simpa using neg_mem hd'
  choose D hDπ hD using hD
  have hσ : ∀ j, ∃ σ : μ → A, (fun c => π (u j c)) - U j ᵥ* E - σ ᵥ* tπ ∈ what₂ (Φ'.map π) := by
    intro j
    obtain ⟨f, hf, g, hg, hfg⟩ := Submodule.mem_sup.1 (hu j)
    obtain ⟨σ, rfl⟩ := (mem_rows tπ g).1 hg
    exact ⟨σ, by rw [← hfg, add_sub_cancel_right]; exact hf⟩
  choose σ hσ using hσ
  have hW : ∀ j, ∃ wj : Fin a ⊕ μ → B, π ∘ wj = Sum.elim (U j) (σ j) ∧ u j - wj ᵥ* G ∈ what₂ Φ' := by
    intro j
    apply lift_exact π x y hπ hker G Φ' hx0 hy0 hG (u j)
    rw [hGπ, Matrix.sumElim_vecMul_fromRows, ← sub_sub]
    exact hσ j
  choose W hWπ hW using hW
  set W' : Matrix μ (Fin a ⊕ μ) B := Matrix.of fun j => -W j with hW'
  set T : Matrix (Fin a ⊕ μ) (Fin a ⊕ μ) B :=
    fromRows D (y • fromCols (0 : Matrix μ (Fin a) B) (1 : Matrix μ μ B) + x • W') with hTdef
  have hT : ∀ i, T i ᵥ* G ∈ what₂ Φ' := by
    rintro (b | j)
    · exact hD b
    · have e1 : (fromCols (0 : Matrix μ (Fin a) B) (1 : Matrix μ μ B)) j = Pi.single (Sum.inr j) 1 := by
        funext i
        rcases i with i | i
        · simp
        · by_cases h : i = j
          · rw [h]; simp
          · simp [h, Ne.symm h]
      have hTj : T (Sum.inr j) = y • Pi.single (Sum.inr j) 1 + x • (-W j) := by
        show y • (fromCols (0 : Matrix μ (Fin a) B) (1 : Matrix μ μ B)) j + x • W' j = _
        rw [e1]
        rfl
      have hGr : G.row (Sum.inr j) = η j • t j := by
        funext c
        rfl
      have e : T (Sum.inr j) ᵥ* G = -(x • u j - (y * η j) • t j) + x • (u j - W j ᵥ* G) := by
        rw [hTj, Matrix.add_vecMul, Matrix.smul_vecMul, Matrix.smul_vecMul, Matrix.single_one_vecMul,
          Matrix.neg_vecMul, hGr]
        funext c
        simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.sub_apply, smul_eq_mul]
        ring
      rw [e]
      exact add_mem (neg_mem (hrel j)) (Submodule.smul_mem _ x (hW j))
  have hTdet := det_relations Φ' G T hG hT hdet
  rw [hTdef, det_expand x y hx hy D W'] at hTdet
  apply hne
  refine Eq.trans ?_ (hann _ hTdet)
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hN : π.mapMatrix ((fromRows D (fromCols (0 : Matrix μ (Fin a) B) (1 : Matrix μ μ B))).updateRow
      (Sum.inr j) (W' j)) =
      (fromBlocks (Φ.updateRow l₀ 0) (C.updateRow l₀ k) 0 1).updateRow (Sum.inr j)
        (Sum.elim (-U j) (-σ j)) := by
    ext (i | i) (c | c)
    · rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.updateRow_ne Sum.inl_ne_inr,
        Matrix.updateRow_ne Sum.inl_ne_inr, Matrix.fromBlocks_apply₁₁]
      exact congrFun (hDπ i) (Sum.inl c)
    · rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.updateRow_ne Sum.inl_ne_inr,
        Matrix.updateRow_ne Sum.inl_ne_inr, Matrix.fromBlocks_apply₁₂]
      exact congrFun (hDπ i) (Sum.inr c)
    · by_cases hi : i = j
      · rw [hi, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.updateRow_self, Matrix.updateRow_self]
        show π (-(W j (Sum.inl c))) = -(U j c)
        rw [map_neg]
        exact congrArg Neg.neg (congrFun (hWπ j) (Sum.inl c))
      · have h : (Sum.inr i : Fin a ⊕ μ) ≠ Sum.inr j := fun h => hi (Sum.inr_injective h)
        rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.updateRow_ne h, Matrix.updateRow_ne h,
          Matrix.fromBlocks_apply₂₁]
        show π ((0 : Matrix μ (Fin a) B) i c) = (0 : Matrix μ (Fin a) A) i c
        simp
    · by_cases hi : i = j
      · rw [hi, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.updateRow_self, Matrix.updateRow_self]
        show π (-(W j (Sum.inr c))) = -(σ j c)
        rw [map_neg]
        exact congrArg Neg.neg (congrFun (hWπ j) (Sum.inr c))
      · have h : (Sum.inr i : Fin a ⊕ μ) ≠ Sum.inr j := fun h => hi (Sum.inr_injective h)
        rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.updateRow_ne h, Matrix.updateRow_ne h,
          Matrix.fromBlocks_apply₂₂]
        show π ((1 : Matrix μ μ B) i c) = (1 : Matrix μ μ A) i c
        rw [Matrix.one_apply, Matrix.one_apply]
        split_ifs <;> simp
  rw [RingHom.map_det, hN, det_block]
  simp [Finset.sum_neg_distrib]

end GlobalTheory.LowDet
