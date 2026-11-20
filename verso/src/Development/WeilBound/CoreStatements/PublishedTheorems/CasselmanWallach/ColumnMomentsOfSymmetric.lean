import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusLaws

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace MatrixActionSingle

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def act (A : Matrix (Fin n) (Fin n) (Module.End ℂ V)) : Module.End ℂ (PiLp 2 fun _ : Fin n => V) where
  toFun u := WithLp.toLp 2 (fun a => ∑ b, A a b (u b))
  map_add' u w := by ext a; simp [Finset.sum_add_distrib]
  map_smul' c u := by ext a; simp [Finset.smul_sum]

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma act_apply (A : Matrix (Fin n) (Fin n) (Module.End ℂ V)) (u : PiLp 2 fun _ : Fin n => V) (a : Fin n) :
    act A u a = ∑ b, A a b (u b) := rfl

/- English proof (translation)
Use extensionality with `a`. Simplify using `only [act_apply, Matrix.mul_apply, LinearMap.sum_apply, Module.End.mul_apply, map_sum]`. Conclude with `Finset.sum_comm`.
-/
lemma act_mul (A B : Matrix (Fin n) (Fin n) (Module.End ℂ V)) (u : PiLp 2 fun _ : Fin n => V) :
    act (A * B) u = act A (act B u) := by
  ext a
  simp only [act_apply, Matrix.mul_apply, LinearMap.sum_apply, Module.End.mul_apply, map_sum]
  exact Finset.sum_comm

/- English proof (translation)
Proceed by induction on `m generalizing u with`. Consider the case `zero`. Use extensionality with `a`. Simplify using `[act_apply, Matrix.one_apply]`. Rewrite using `[Finset.sum_eq_single a (fun b _ hb => by simp [Ne.symm hb]) (by simp)]`.

Simplify using the standard rewrite rules. Consider the case `succ m ih => rw [pow_succ, act_mul, ih, pow_succ, Module.End.mul_apply]`.
-/
lemma act_pow (A : Matrix (Fin n) (Fin n) (Module.End ℂ V)) (m : ℕ) (u : PiLp 2 fun _ : Fin n => V) :
    act (A ^ m) u = (act A ^ m) u := by
  induction m generalizing u with
  | zero =>
    ext a
    simp [act_apply, Matrix.one_apply]
    rw [Finset.sum_eq_single a (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp
  | succ m ih => rw [pow_succ, act_mul, ih, pow_succ, Module.End.mul_apply]

/- English proof (translation)
Simplify using `[adjSign, eq_comm]`.
-/
lemma adjSign_symm (ε : Fin n → Bool) (a b : Fin n) : adjSign ε a b = adjSign ε b a := by
  simp [adjSign, eq_comm]

/- English proof (translation)
Simplify using `only [PiLp.inner_apply, act_apply, Mm, Md, Matrix.of_apply, sum_inner, inner_sum, LinearMap.smul_apply, inner_smul_right]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[adjSign_symm]`. Conclude with `hu a b _ _`.
-/
lemma adj (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (hu : IsInfUnitary ε E)
    (u w : PiLp 2 fun _ : Fin n => V) :
    inner ℂ (act (Mm E) u) w = inner ℂ u (act (Md ε E) w) := by
  simp only [PiLp.inner_apply, act_apply, Mm, Md, Matrix.of_apply, sum_inner, inner_sum,
    LinearMap.smul_apply, inner_smul_right]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [adjSign_symm]
  exact hu a b _ _

/- English proof (translation)
Rewrite using `[← inner_conj_symm, ← adj ε E hu, inner_conj_symm]`.
-/
lemma adj' (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (hu : IsInfUnitary ε E)
    (u w : PiLp 2 fun _ : Fin n => V) :
    inner ℂ (act (Md ε E) u) w = inner ℂ u (act (Mm E) w) := by
  rw [← inner_conj_symm, ← adj ε E hu, inner_conj_symm]

/- English proof (translation)
Rewrite using `[act_apply, Finset.sum_eq_single e]`. Simplify using `[PiLp.single_apply]`. Introduce `b _ hb`. Simplify using `[PiLp.single_apply, hb]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ e) h`.
-/
lemma act_single (A : Matrix (Fin n) (Fin n) (Module.End ℂ V)) (e a : Fin n) (v : V) :
    act A (PiLp.single 2 e v) a = A a e v := by
  rw [act_apply, Finset.sum_eq_single e]
  · simp [PiLp.single_apply]
  · intro b _ hb
    simp [PiLp.single_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ e) h

/- English proof (translation)
Rewrite using `[PiLp.inner_apply, Finset.sum_eq_single e (fun b _ hb => by simp [hb]) (by simp)]`. Simplify using the standard rewrite rules.
-/
lemma inner_single (e : Fin n) (v : V) (w : PiLp 2 fun _ : Fin n => V) :
    inner ℂ (PiLp.single 2 e v) w = inner ℂ v (w e) := by
  rw [PiLp.inner_apply, Finset.sum_eq_single e (fun b _ hb => by simp [hb]) (by simp)]
  simp

end MatrixActionSingle

open MatrixActionSingle in
/- English proof (translation)
Introduce `h7`. Unfold `ColumnOperatorMoments ForMod`. Introduce `n ε V _ _ E hM v hv e j`. Establish `hu` using `hM.uni`. Establish `hsa : ∀ y z : PiLp 2 (fun _ : Fin n => V), inner ℂ (act (Md ε E * Mm E) y) z = inner ℂ y (act (Md ε E * Mm E) z)`.

Introduce `y z`. Rewrite using `[act_mul, act_mul, adj' ε E hu, adj ε E hu]`. Establish `hxn : ‖(PiLp.single 2 e v : PiLp 2 (fun _ : Fin n => V))‖ = 1`. Rewrite using `[PiLp.norm_single, hv]`. Establish `hn : ‖act (Mm E) (PiLp.single 2 e v : PiLp 2 (fun _ : Fin n => V))‖ ^ 2 = ∑ a, ‖E a e v‖ ^ 2`.

Rewrite using `[PiLp.norm_sq_eq_of_L2]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `act_single (Mm E) e a v` as an intermediate fact. Simplify using `only [Mm, Matrix.of_apply] at this`. Rewrite using `[← this]`.

Both sides reduce to the same expression. Establish `hq : inner ℂ (PiLp.single 2 e v : PiLp 2 (fun _ : Fin n => V)) (act (Md ε E * Mm E) (PiLp.single 2 e v)) = ((∑ a, ‖E a e v‖ ^ 2 : ℝ) : ℂ)`. Rewrite using `[act_mul, ← adj ε E hu, inner_self_eq_norm_sq_to_K, ← hn]`. Use `norm_cast`. Establish `hre : (inner ℂ (PiLp.single 2 e v : PiLp 2 (fun _ : Fin n => V)) (act (Md ε E * Mm E) (PiLp.single 2 e v))).re = ∑ a, ‖E a e v‖ ^ 2`.

Rewrite using `[hq, Complex.ofReal_re]`. Establish `key` using `h7 (PiLp 2 (fun _ : Fin n => V)) (act (Md ε E * Mm E)) hsa (PiLp.single 2 e v) hxn (by rw [hre]; positivity) j`. Rewrite `key` using `[hre, ← act_pow, inner_single, act_single]`. Conclude with `key`.
-/
theorem column_moments_of_symmetric : A7 → ColumnOperatorMoments := by
  intro h7
  unfold ColumnOperatorMoments ForMod
  intro n ε V _ _ E hM v hv e j
  have hu := hM.uni
  have hsa : ∀ y z : PiLp 2 (fun _ : Fin n => V),
      inner ℂ (act (Md ε E * Mm E) y) z = inner ℂ y (act (Md ε E * Mm E) z) := by
    intro y z
    rw [act_mul, act_mul, adj' ε E hu, adj ε E hu]
  have hxn : ‖(PiLp.single 2 e v : PiLp 2 (fun _ : Fin n => V))‖ = 1 := by
    rw [PiLp.norm_single, hv]
  have hn : ‖act (Mm E) (PiLp.single 2 e v : PiLp 2 (fun _ : Fin n => V))‖ ^ 2
      = ∑ a, ‖E a e v‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_congr rfl fun a _ => ?_
    have := act_single (Mm E) e a v
    simp only [Mm, Matrix.of_apply] at this
    rw [← this]
    rfl
  have hq : inner ℂ (PiLp.single 2 e v : PiLp 2 (fun _ : Fin n => V))
      (act (Md ε E * Mm E) (PiLp.single 2 e v)) = ((∑ a, ‖E a e v‖ ^ 2 : ℝ) : ℂ) := by
    rw [act_mul, ← adj ε E hu, inner_self_eq_norm_sq_to_K, ← hn]
    norm_cast
  have hre : (inner ℂ (PiLp.single 2 e v : PiLp 2 (fun _ : Fin n => V))
      (act (Md ε E * Mm E) (PiLp.single 2 e v))).re = ∑ a, ‖E a e v‖ ^ 2 := by
    rw [hq, Complex.ofReal_re]
  have key := h7 (PiLp 2 (fun _ : Fin n => V)) (act (Md ε E * Mm E)) hsa
    (PiLp.single 2 e v) hxn (by rw [hre]; positivity) j
  rw [hre, ← act_pow, inner_single, act_single] at key
  exact key

end PositivityTheory.CW

end
