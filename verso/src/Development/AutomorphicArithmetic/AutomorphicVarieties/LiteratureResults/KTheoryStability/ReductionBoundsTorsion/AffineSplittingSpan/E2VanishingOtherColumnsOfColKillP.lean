import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.HhZero

noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

open PrismSpan

variable {P Q : Type} [Group P] [Group Q]

def ColKillP : Prop :=
  ∀ (P Q : Type) [Group P] [Group Q] (pr : P →* Q) (s : Q →* P), (∀ g, pr (s g) = g) →
    ∀ (u : Q), (∀ g, g * u = u * g) → ∀ (q : ℕ) (f : Polynomial ℝ),
    (∀ c : (Fin (q + 2) → P) → ℝ, InvS (pr.ker : Set P) c → dc c = 0 →
      ∃ e : (Fin (q + 1) → P) → ℝ, InvS (pr.ker : Set P) e ∧
        Polynomial.aeval (mapOp (fun y => (s u)⁻¹ * y * s u) (q + 2)) f c = dc e) →
    ∀ {a : ℕ} (x : Bi P Q (a + 1) (q + 2)), PInv pr x → dv x = 0 →
      ∃ E : Bi P Q (a + 1) (q + 1), PInv pr E ∧ Polynomial.aeval (TcL (s u) (a + 1) (q + 2)) f x = dv E

section
variable (pr : P →* Q) (s : Q →* P) (hs : ∀ g, pr (s g) = g) (u : Q) (hu : ∀ g, g * u = u * g)
include hs hu

/- English proof (translation)
Establish `hpz : ∀ (n : ℕ) (y : Fin n → P), prism (fun p => p * (s u)⁻¹) (0 : (Fin (n + 1) → P) → ℝ) y = 0`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro y`. Both sides reduce to the same expression.

Consider the case `succ n ih`. Introduce `y`. Rewrite using `[prism_succ]`. Establish `: (fun w : Fin (n + 1) → P => (0 : (Fin (n + 2) → P) → ℝ) (Fin.cons (y 0) w)) = 0` using `rfl`. Rewrite using `[this, ih]`.

Simplify using the standard rewrite rules. Rewrite using `[ru_eq pr s hs u hu hz]`. Use function extensionality and compare the values at `x y`. Establish `h` using `prism_dc (fun p => p * (s u)⁻¹) b (z x) (fun j => (s u)⁻¹ * y j * s u)`. Establish `h0 : dc (z x) = 0` using `congrFun hdz x`.

Rewrite `h` using `[h0, hpz, add_zero]`. Simplify using `only [Pi.sub_apply]`. Conclude with `h.symm`.
-/
theorem ru_tc {a b : ℕ} {z : Bi P Q a (b + 2)} (hz : PInv pr z) (hdz : dv z = 0) :
    Ru u z - Tc (s u) z = dv (Tc (s u) (Hv (s u)⁻¹ z)) := by
  have hpz : ∀ (n : ℕ) (y : Fin n → P),
      prism (fun p => p * (s u)⁻¹) (0 : (Fin (n + 1) → P) → ℝ) y = 0 := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      rw [prism_succ]
      have : (fun w : Fin (n + 1) → P => (0 : (Fin (n + 2) → P) → ℝ) (Fin.cons (y 0) w)) = 0 := rfl
      rw [this, ih]
      simp
  rw [ru_eq pr s hs u hu hz]
  funext x y
  have h := prism_dc (fun p => p * (s u)⁻¹) b (z x) (fun j => (s u)⁻¹ * y j * s u)
  have h0 : dc (z x) = 0 := congrFun hdz x
  rw [h0, hpz, add_zero] at h
  simp only [Pi.sub_apply]
  exact h.symm

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => exact ⟨hz, hdz⟩`. Consider the case `succ k ih`. Rewrite using `[pow_succ', Module.End.mul_apply]`.

Take `⟨h1, h2⟩` from `ih`. Generalize the expression as in `((RuL (P := P) u a (b + 2)) ^ k) z = w at h1 h2`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `g x y`. Express the relevant statement in the definitionally equal form `w (fun i => (fun i => pr g * x i) i * u) (fun j => g * y j) = w (fun i => x i * u) y`.

Simplify using `only [mul_assoc]`. Conclude with `h1 g (fun i => x i * u) y`. Use function extensionality and compare the values at `x y`. Conclude with `congrFun (congrFun h2 (fun i => x i * u)) y`.
-/
theorem pow_closed {a b : ℕ} {z : Bi P Q a (b + 2)} (hz : PInv pr z) (hdz : dv z = 0) :
    ∀ k : ℕ, PInv pr (((RuL (P := P) u a (b + 2)) ^ k) z) ∧ dv (((RuL (P := P) u a (b + 2)) ^ k) z) = 0 := by
  intro k
  induction k with
  | zero => exact ⟨hz, hdz⟩
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    obtain ⟨h1, h2⟩ := ih
    generalize ((RuL (P := P) u a (b + 2)) ^ k) z = w at h1 h2
    refine ⟨?_, ?_⟩
    · intro g x y
      change w (fun i => (fun i => pr g * x i) i * u) (fun j => g * y j) = w (fun i => x i * u) y
      simp only [mul_assoc]
      exact h1 g (fun i => x i * u) y
    · funext x y
      exact congrFun (congrFun h2 (fun i => x i * u)) y

/- English proof (translation)
Establish `htr : ∀ (n : ℕ) (G : (Fin (n + 1) → P) → ℝ) (g : P) (y : Fin n → P), prism (fun p => p * (s u)⁻¹) G (fun j => g * y j) = prism (fun p => p * (s u)⁻¹) (fun v => G (fun j => g * v j)) y`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro G g y`. Both sides reduce to the same expression.

Consider the case `succ n ih`. Introduce `G g y`. Rewrite using `[prism_succ, prism_succ]`. Establish `e1 : (Fin.cons (g * y 0) (fun i => g * y i * (s u)⁻¹) : Fin (n + 2) → P) = fun j => g * (Fin.cons (y 0) (fun i => y i * (s u)⁻¹) : Fin (n + 2) → P) j`. Use function extensionality and compare the values at `j`.

Use `Fin.cases ?_ (fun i => ?_) j` and prove the remaining obligations. Simplify using the standard rewrite rules. Simplify using `[mul_assoc]`. Establish `e2 : ∀ v : Fin (n + 1) → P, (Fin.cons (g * y 0) (fun j => g * v j) : Fin (n + 2) → P) = fun j => g * (Fin.cons (y 0) v : Fin (n + 2) → P) j`. Introduce `v`.

Use function extensionality and compare the values at `j`. Use `Fin.cases ?_ (fun i => ?_) j` and prove the remaining obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish `ih'` using `ih (fun w => G (Fin.cons (g * y 0) w)) g (Fin.tail y)`.

Simplify using `only [e2] at ih'`. Simplify using `only [e1]`. Use `congr 1`. Establish `hg : ∀ g : P, pr ((s u)⁻¹ * g * s u) = pr g`. Introduce `g`.

Rewrite using `[map_mul, map_mul, map_inv, hs, mul_assoc, hu (pr g), ← mul_assoc, inv_mul_cancel, one_mul]`. Establish `hTcP : ∀ {c : ℕ} (F : Bi P Q a c), PInv pr F → PInv pr (Tc (s u) F)`. Introduce `c F hF g x y`. Establish `h` using `hF ((s u)⁻¹ * g * s u) x (fun j => (s u)⁻¹ * y j * s u)`. Rewrite `h` using `[hg]`.

Express the relevant statement in the definitionally equal form `F (fun i => pr g * x i) (fun j => (s u)⁻¹ * (g * y j) * s u) = F x (fun j => (s u)⁻¹ * y j * s u)`. Rewrite using `[← h]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Use `group`.

Establish `hHvP : ∀ {c : ℕ} (F : Bi P Q a (c + 1)), PInv pr F → PInv pr (Hv (s u)⁻¹ F)`. Introduce `c F hF g x y`. Express the relevant statement in the definitionally equal form `prism (fun p => p * (s u)⁻¹) (F (fun i => pr g * x i)) (fun j => g * y j) = prism (fun p => p * (s u)⁻¹) (F x) y`. Rewrite using `[htr]`. Use `congr 1`.

Use function extensionality and compare the values at `v`. Conclude with `hF g x v`. Establish `hdvadd : ∀ A B : Bi P Q a (b + 1), dv (A + B) = dv A + dv B`. Introduce `A B`. Use function extensionality and compare the values at `x y`.

Simplify using `[dv, dc, Finset.sum_add_distrib, mul_add]`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Use `⟨0, fun g x y => rfl, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `x y`. Simplify using `[dv, dc]`. Consider the case `succ k ih`. Take `⟨E, hE, hEq⟩` from `ih`. Take `⟨hw1, hw2⟩` from `pow_closed pr s hs u hu hz hdz k`.

Use `⟨Tc (s u) (Hv (s u)⁻¹ (((RuL (P := P) u a (b + 2)) ^ k) z)) + Tc (s u) E, ?_, ?_⟩` and prove the remaining obligations. Introduce `g x y`. Simplify using `only [Pi.add_apply]`. Rewrite using `[hTcP _ (hHvP _ hw1) g x y, hTcP _ hE g x y]`. Establish `h1` using `ru_tc pr s hs u hu hw1 hw2`.

Rewrite using `[pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]`. Generalize the expression as in `((RuL (P := P) u a (b + 2)) ^ k) z = w at hEq h1 hw1 hw2 ⊢`. Generalize the expression as in `((TcL (s u) a (b + 2)) ^ k) z = T at hEq ⊢`. Establish `hsplit : RuL (P` using `P) u a (b + 2) w - TcL (s u) a (b + 2) T = (RuL (P := P) u a (b + 2) w - TcL (s u) a (b + 2) w) + TcL (s u) a (b + 2) (w - T) := by`. Rewrite using `[map_sub]`.

Normalize the expressions using the abelian group laws. Rewrite using `[hsplit, hEq, hdvadd]`. Express the relevant statement in the definitionally equal form `(Ru u w - Tc (s u) w) + Tc (s u) (dv E) = _`. Rewrite using `[h1]`. Both sides reduce to the same expression.
-/
theorem pow_diff {a b : ℕ} {z : Bi P Q a (b + 2)} (hz : PInv pr z) (hdz : dv z = 0) :
    ∀ k : ℕ, ∃ E : Bi P Q a (b + 1), PInv pr E ∧
      ((RuL (P := P) u a (b + 2)) ^ k) z - ((TcL (s u) a (b + 2)) ^ k) z = dv E := by
  have htr : ∀ (n : ℕ) (G : (Fin (n + 1) → P) → ℝ) (g : P) (y : Fin n → P),
      prism (fun p => p * (s u)⁻¹) G (fun j => g * y j) =
        prism (fun p => p * (s u)⁻¹) (fun v => G (fun j => g * v j)) y := by
    intro n
    induction n with
    | zero => intro G g y; rfl
    | succ n ih =>
      intro G g y
      rw [prism_succ, prism_succ]
      have e1 : (Fin.cons (g * y 0) (fun i => g * y i * (s u)⁻¹) : Fin (n + 2) → P) =
          fun j => g * (Fin.cons (y 0) (fun i => y i * (s u)⁻¹) : Fin (n + 2) → P) j := by
        funext j
        refine Fin.cases ?_ (fun i => ?_) j
        · simp
        · simp [mul_assoc]
      have e2 : ∀ v : Fin (n + 1) → P, (Fin.cons (g * y 0) (fun j => g * v j) : Fin (n + 2) → P) =
          fun j => g * (Fin.cons (y 0) v : Fin (n + 2) → P) j := by
        intro v
        funext j
        refine Fin.cases ?_ (fun i => ?_) j
        · simp
        · simp
      have ih' := ih (fun w => G (Fin.cons (g * y 0) w)) g (Fin.tail y)
      simp only [e2] at ih'
      simp only [e1]
      congr 1
  have hg : ∀ g : P, pr ((s u)⁻¹ * g * s u) = pr g := by
    intro g
    rw [map_mul, map_mul, map_inv, hs, mul_assoc, hu (pr g), ← mul_assoc, inv_mul_cancel, one_mul]
  have hTcP : ∀ {c : ℕ} (F : Bi P Q a c), PInv pr F → PInv pr (Tc (s u) F) := by
    intro c F hF g x y
    have h := hF ((s u)⁻¹ * g * s u) x (fun j => (s u)⁻¹ * y j * s u)
    rw [hg] at h
    change F (fun i => pr g * x i) (fun j => (s u)⁻¹ * (g * y j) * s u) = F x (fun j => (s u)⁻¹ * y j * s u)
    rw [← h]
    congr 1
    funext j
    group
  have hHvP : ∀ {c : ℕ} (F : Bi P Q a (c + 1)), PInv pr F → PInv pr (Hv (s u)⁻¹ F) := by
    intro c F hF g x y
    change prism (fun p => p * (s u)⁻¹) (F (fun i => pr g * x i)) (fun j => g * y j) =
      prism (fun p => p * (s u)⁻¹) (F x) y
    rw [htr]
    congr 1
    funext v
    exact hF g x v
  have hdvadd : ∀ A B : Bi P Q a (b + 1), dv (A + B) = dv A + dv B := by
    intro A B
    funext x y
    simp [dv, dc, Finset.sum_add_distrib, mul_add]
  intro k
  induction k with
  | zero =>
    refine ⟨0, fun g x y => rfl, ?_⟩
    funext x y
    simp [dv, dc]
  | succ k ih =>
    obtain ⟨E, hE, hEq⟩ := ih
    obtain ⟨hw1, hw2⟩ := pow_closed pr s hs u hu hz hdz k
    refine ⟨Tc (s u) (Hv (s u)⁻¹ (((RuL (P := P) u a (b + 2)) ^ k) z)) + Tc (s u) E, ?_, ?_⟩
    · intro g x y
      simp only [Pi.add_apply]
      rw [hTcP _ (hHvP _ hw1) g x y, hTcP _ hE g x y]
    · have h1 := ru_tc pr s hs u hu hw1 hw2
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
      generalize ((RuL (P := P) u a (b + 2)) ^ k) z = w at hEq h1 hw1 hw2 ⊢
      generalize ((TcL (s u) a (b + 2)) ^ k) z = T at hEq ⊢
      have hsplit : RuL (P := P) u a (b + 2) w - TcL (s u) a (b + 2) T =
          (RuL (P := P) u a (b + 2) w - TcL (s u) a (b + 2) w) + TcL (s u) a (b + 2) (w - T) := by
        rw [map_sub]
        abel
      rw [hsplit, hEq, hdvadd]
      change (Ru u w - Tc (s u) w) + Tc (s u) (dv E) = _
      rw [h1]
      rfl

/- English proof (translation)
Establish `hdvadd : ∀ A B : Bi P Q a (b + 1), dv (A + B) = dv A + dv B`. Introduce `A B`. Use function extensionality and compare the values at `x y`. Simplify using `[dv, dc, Finset.sum_add_distrib, mul_add]`. Establish `hdvsmul : ∀ (c : ℝ) (A : Bi P Q a (b + 1)), dv (c • A) = c • dv A`.

Introduce `c A`. Use function extensionality and compare the values at `x y`. Simplify using `[dv, dc, Finset.mul_sum, mul_left_comm]`. Proceed by induction on `f using Polynomial.induction_on' with`. Consider the case `add p q hp hq`.

Take `⟨E1, h1, e1⟩` from `hp`. Take `⟨E2, h2, e2⟩` from `hq`. Use `⟨E1 + E2, ?_, ?_⟩` and prove the remaining obligations. Introduce `g x y`. Simplify using `only [Pi.add_apply]`.

Rewrite using `[h1 g x y, h2 g x y]`. Rewrite using `[map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hdvadd, ← e1, ← e2]`. Normalize the expressions using the abelian group laws. Consider the case `monomial n c`. Take `⟨E, hE, e⟩` from `pow_diff pr s hs u hu hz hdz n`.

Use `⟨c • E, ?_, ?_⟩` and prove the remaining obligations. Introduce `g x y`. Simplify using `only [Pi.smul_apply]`. Rewrite using `[hE g x y]`. Rewrite using `[Polynomial.aeval_monomial, Polynomial.aeval_monomial, Module.End.mul_apply, Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply, ← smul_sub, e, hdvsmul]`.
-/
theorem aeval_diff {a b : ℕ} {z : Bi P Q a (b + 2)} (hz : PInv pr z) (hdz : dv z = 0) (f : Polynomial ℝ) :
    ∃ E : Bi P Q a (b + 1), PInv pr E ∧
      Polynomial.aeval (RuL (P := P) u a (b + 2)) f z - Polynomial.aeval (TcL (s u) a (b + 2)) f z = dv E := by
  have hdvadd : ∀ A B : Bi P Q a (b + 1), dv (A + B) = dv A + dv B := by
    intro A B
    funext x y
    simp [dv, dc, Finset.sum_add_distrib, mul_add]
  have hdvsmul : ∀ (c : ℝ) (A : Bi P Q a (b + 1)), dv (c • A) = c • dv A := by
    intro c A
    funext x y
    simp [dv, dc, Finset.mul_sum, mul_left_comm]
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨E1, h1, e1⟩ := hp
    obtain ⟨E2, h2, e2⟩ := hq
    refine ⟨E1 + E2, ?_, ?_⟩
    · intro g x y
      simp only [Pi.add_apply]
      rw [h1 g x y, h2 g x y]
    · rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hdvadd, ← e1, ← e2]
      abel
  | monomial n c =>
    obtain ⟨E, hE, e⟩ := pow_diff pr s hs u hu hz hdz n
    refine ⟨c • E, ?_, ?_⟩
    · intro g x y
      simp only [Pi.smul_apply]
      rw [hE g x y]
    · rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Module.End.mul_apply,
        Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply,
        ← smul_sub, e, hdvsmul]

end

/- English proof (translation)
Introduce `P Q _ _ pr s hs u hu m hm q hq w hw hdw hdh`. Establish `hdvadd : ∀ {a b : ℕ} (A B : Bi P Q a (b + 1)), dv (A + B) = dv A + dv B`. Introduce `a b A B`. Use function extensionality and compare the values at `x y`. Simplify using `[dv, dc, Finset.sum_add_distrib, mul_add]`.

Establish `hdvsmul : ∀ {a b : ℕ} (c : ℝ) (A : Bi P Q a (b + 1)), dv (c • A) = c • dv A`. Introduce `a b c A`. Use function extensionality and compare the values at `x y`. Simplify using `[dv, dc, Finset.mul_sum, mul_left_comm]`. Take `⟨f, hf1, hf⟩` from `hm q hq`.

Take `⟨E1, hE1, e1⟩` from `hK P Q pr s hs u hu q f hf (a := 0) w hw hdw`. Take `⟨E2, hE2, e2⟩` from `aeval_diff pr s hs u hu hw hdw f`. Establish `hfix : RuL (P` using `P) u 1 (q + 2) w = w := by`. Use function extensionality and compare the values at `x y`. Establish `hsa : ∀ j : Fin 1, Fin.succAbove (1 : Fin 2) j = 0`.

Introduce `j`. Use `fin_cases j`. Both sides reduce to the same expression. Establish `h` using `congrFun (congrFun hdh (fun i : Fin 2 => if i = 0 then x 0 * u else x 0)) y`. Simplify using `[dh, dc, Fin.sum_univ_two, hsa] at h`.

Express the relevant statement in the definitionally equal form `w (fun i => x i * u) y = w x y`. Establish `hx1 : (fun i : Fin 1 => x i * u) = fun _ => x 0 * u`. Use function extensionality and compare the values at `i`. Rewrite using `[Subsingleton.elim i 0]`. Establish `hx2 : x = fun _ => x 0`.

Use function extensionality and compare the values at `i`. Rewrite using `[Subsingleton.elim i 0]`. Rewrite using `[hx1]`. Use `conv_rhs => rw [hx2]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hev : ∀ g : Polynomial ℝ, Polynomial.aeval (RuL (P` using `P) u 1 (q + 2)) g w = g.eval 1 • w := by`. Introduce `g`. Proceed by induction on `g using Polynomial.induction_on' with`. Consider the case `add p r hp hr => rw [map_add, LinearMap.add_apply, hp, hr, Polynomial.eval_add, add_smul]`. Consider the case `monomial n c`.

Rewrite using `[Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, Polynomial.eval_monomial, one_pow, mul_one]`. Use `congr 1`. Proceed by induction on `n with`. Consider the case `zero => rfl`. Consider the case `succ n ih => rw [pow_succ, Module.End.mul_apply, hfix, ih]`.

Rewrite `e2` using `[hev, e1]`. Use `⟨(f.eval 1)⁻¹ • (E2 + E1), ?_, ?_⟩` and prove the remaining obligations. Introduce `g x y`. Simplify using `only [Pi.smul_apply, Pi.add_apply]`. Rewrite using `[hE1 g x y, hE2 g x y]`.

Rewrite using `[hdvsmul, hdvadd, ← e2, sub_add_cancel, smul_smul, inv_mul_cancel₀ hf1, one_smul]`.
-/
theorem e2VanishingFirstColumn_of_colKillP (hK : ColKillP) : E2VanishingFirstColumn := by
  intro P Q _ _ pr s hs u hu m hm q hq w hw hdw hdh
  have hdvadd : ∀ {a b : ℕ} (A B : Bi P Q a (b + 1)), dv (A + B) = dv A + dv B := by
    intro a b A B
    funext x y
    simp [dv, dc, Finset.sum_add_distrib, mul_add]
  have hdvsmul : ∀ {a b : ℕ} (c : ℝ) (A : Bi P Q a (b + 1)), dv (c • A) = c • dv A := by
    intro a b c A
    funext x y
    simp [dv, dc, Finset.mul_sum, mul_left_comm]
  obtain ⟨f, hf1, hf⟩ := hm q hq
  obtain ⟨E1, hE1, e1⟩ := hK P Q pr s hs u hu q f hf (a := 0) w hw hdw
  obtain ⟨E2, hE2, e2⟩ := aeval_diff pr s hs u hu hw hdw f
  have hfix : RuL (P := P) u 1 (q + 2) w = w := by
    funext x y
    have hsa : ∀ j : Fin 1, Fin.succAbove (1 : Fin 2) j = 0 := by
      intro j
      fin_cases j
      rfl
    have h := congrFun (congrFun hdh (fun i : Fin 2 => if i = 0 then x 0 * u else x 0)) y
    simp [dh, dc, Fin.sum_univ_two, hsa] at h
    change w (fun i => x i * u) y = w x y
    have hx1 : (fun i : Fin 1 => x i * u) = fun _ => x 0 * u := by
      funext i; rw [Subsingleton.elim i 0]
    have hx2 : x = fun _ => x 0 := by
      funext i; rw [Subsingleton.elim i 0]
    rw [hx1]
    conv_rhs => rw [hx2]
    linarith
  have hev : ∀ g : Polynomial ℝ, Polynomial.aeval (RuL (P := P) u 1 (q + 2)) g w = g.eval 1 • w := by
    intro g
    induction g using Polynomial.induction_on' with
    | add p r hp hr => rw [map_add, LinearMap.add_apply, hp, hr, Polynomial.eval_add, add_smul]
    | monomial n c =>
      rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
        Polynomial.eval_monomial, one_pow, mul_one]
      congr 1
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ, Module.End.mul_apply, hfix, ih]
  rw [hev, e1] at e2
  refine ⟨(f.eval 1)⁻¹ • (E2 + E1), ?_, ?_⟩
  · intro g x y
    simp only [Pi.smul_apply, Pi.add_apply]
    rw [hE1 g x y, hE2 g x y]
  · rw [hdvsmul, hdvadd, ← e2, sub_add_cancel, smul_smul, inv_mul_cancel₀ hf1, one_smul]

/- English proof (translation)
Introduce `P Q _ _ pr s hs u hu m hm p q hq x hx hdx hdh`. Establish `hpz : ∀ (n : ℕ) (y : Fin n → Q), prism (fun v => v * u) (0 : (Fin (n + 1) → Q) → ℝ) y = 0`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro y`.

Both sides reduce to the same expression. Consider the case `succ n ih`. Introduce `y`. Rewrite using `[prism_succ]`. Establish `: (fun w : Fin (n + 1) → Q => (0 : (Fin (n + 2) → Q) → ℝ) (Fin.cons (y 0) w)) = 0` using `rfl`.

Rewrite using `[this, ih]`. Simplify using the standard rewrite rules. Establish `hlin : ∀ (n : ℕ) (k : ℕ) (c : Fin k → ℝ) (F : Fin k → (Fin (n + 1) → Q) → ℝ) (y : Fin n → Q), prism (fun v => v * u) (fun w => ∑ i, c i * F i w) y = ∑ i, c i * prism (fun v => v * u) (F i) y`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero`. Introduce `k c F y`. Express the relevant statement in the definitionally equal form `(0 : ℝ) = ∑ i, c i * (0 : ℝ)`. Simplify using the standard rewrite rules. Consider the case `succ n ih`.

Introduce `k c F y`. Rewrite using `[prism_succ]`. Simplify using `only [prism_succ]`. Rewrite using `[ih k c (fun i w => F i (Fin.cons (y 0) w)) (Fin.tail y), ← Finset.sum_sub_distrib]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Expand and normalize the polynomial expressions, which then agree. Establish `htr : ∀ (n : ℕ) (G : (Fin (n + 1) → Q) → ℝ) (g : Q) (y : Fin n → Q), prism (fun v => v * u) G (fun j => g * y j) = prism (fun v => v * u) (fun v => G (fun j => g * v j)) y`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => intro G g y`. Both sides reduce to the same expression. Consider the case `succ n ih`. Introduce `G g y`. Rewrite using `[prism_succ, prism_succ]`.

Establish `e1 : (Fin.cons (g * y 0) (fun i => g * y i * u) : Fin (n + 2) → Q) = fun j => g * (Fin.cons (y 0) (fun i => y i * u) : Fin (n + 2) → Q) j`. Use function extensionality and compare the values at `j`. Use `Fin.cases ?_ (fun i => ?_) j` and prove the remaining obligations. Simplify using the standard rewrite rules. Simplify using `[mul_assoc]`.

Establish `e2 : ∀ v : Fin (n + 1) → Q, (Fin.cons (g * y 0) (fun j => g * v j) : Fin (n + 2) → Q) = fun j => g * (Fin.cons (y 0) v : Fin (n + 2) → Q) j`. Introduce `v`. Use function extensionality and compare the values at `j`. Use `Fin.cases ?_ (fun i => ?_) j` and prove the remaining obligations. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Establish `ih'` using `ih (fun w => G (Fin.cons (g * y 0) w)) g (Fin.tail y)`. Simplify using `only [e2] at ih'`. Simplify using `only [e1]`. Use `congr 1`.

Set `H : Bi P Q (p + 1) (q + 2)` to `fun x' y => prism (fun v => v * u) (fun x'' => x x'' y) x'`. Establish `hA : dh H = Ru u x - x`. Use function extensionality and compare the values at `x' y`. Establish `h` using `prism_dc (fun v => v * u) p (fun x'' => x x'' y) x'`. Establish `h0 : dc (fun x'' => x x'' y) = 0`.

Use function extensionality and compare the values at `v`. Conclude with `congrFun (congrFun hdh v) y`. Rewrite `h` using `[h0, hpz, add_zero]`. Conclude with `h`. Establish `hB : PInv pr H`.

Introduce `g x' y`. Express the relevant statement in the definitionally equal form `prism (fun v => v * u) (fun x'' => x x'' (fun j => g * y j)) (fun i => pr g * x' i) = prism (fun v => v * u) (fun x'' => x x'' y) x'`. Rewrite using `[htr]`. Use `congr 1`. Use function extensionality and compare the values at `v`.

Conclude with `hx g v y`. Establish `hC : dv H = 0`. Use function extensionality and compare the values at `x' y`. Express the relevant statement in the definitionally equal form `dc (fun y' => prism (fun v => v * u) (fun x'' => x x'' y') x') y = 0`. Simplify using `only [dc]`.

Use `hlin (p + 1) (q + 3) (fun i => (-1) ^ (i : ℕ)) (fun i x'' => x x'' (fun j => y (i.succAbove j))) x'` as an intermediate fact. Rewrite using `[← this]`. Establish `h0 : (fun w => ∑ i : Fin (q + 3), (-1 : ℝ) ^ (i : ℕ) * x w (fun j => y (i.succAbove j))) = 0`. Use function extensionality and compare the values at `w`. Conclude with `congrFun (congrFun hdx w) y`.

Rewrite using `[h0, hpz]`. Establish `hdvadd : ∀ {a b : ℕ} (A B : Bi P Q a (b + 1)), dv (A + B) = dv A + dv B`. Introduce `a b A B`. Use function extensionality and compare the values at `x y`. Simplify using `[dv, dc, Finset.sum_add_distrib, mul_add]`.

Establish `hdvsmul : ∀ {a b : ℕ} (c : ℝ) (A : Bi P Q a (b + 1)), dv (c • A) = c • dv A`. Introduce `a b c A`. Use function extensionality and compare the values at `x y`. Simplify using `[dv, dc, Finset.mul_sum, mul_left_comm]`. Establish `hdhadd : ∀ {a b : ℕ} (A B : Bi P Q (a + 1) b), dh (A + B) = dh A + dh B`.

Introduce `a b A B`. Use function extensionality and compare the values at `x y`. Simplify using `[dh, dc, Finset.sum_add_distrib, mul_add]`. Establish `hdhsmul : ∀ {a b : ℕ} (c : ℝ) (A : Bi P Q (a + 1) b), dh (c • A) = c • dh A`. Introduce `a b c A`.

Use function extensionality and compare the values at `x y`. Simplify using `[dh, dc, Finset.mul_sum, mul_left_comm]`. Establish `hD : ∀ g : Polynomial ℝ, PInv pr (Polynomial.aeval (RuL (P` using `P) u (p + 1) (q + 2)) g H) ∧ dv (Polynomial.aeval (RuL (P := P) u (p + 1) (q + 2)) g H) = 0 := by`. Introduce `g`. Proceed by induction on `g using Polynomial.induction_on' with`.

Consider the case `add r t hr ht`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `g' x' y`. Rewrite using `[map_add, LinearMap.add_apply]`. Simplify using `only [Pi.add_apply]`.

Rewrite using `[hr.1 g' x' y, ht.1 g' x' y]`. Rewrite using `[map_add, LinearMap.add_apply, hdvadd, hr.2, ht.2, add_zero]`. Consider the case `monomial n c`. Rewrite using `[Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]`. Take `⟨h1, h2⟩` from `pow_closed pr s hs u hu hB hC n`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `g' x' y`. Simplify using `only [Pi.smul_apply]`. Rewrite using `[h1 g' x' y]`. Rewrite using `[hdvsmul, h2, smul_zero]`.

Establish `hE : ∀ (g : Polynomial ℝ) (F : Bi P Q (p + 1) (q + 2)), Polynomial.aeval (RuL (P` using `P) u (p + 2) (q + 2)) g (dh F) = dh (Polynomial.aeval (RuL (P := P) u (p + 1) (q + 2)) g F) := by`. Introduce `g F`. Proceed by induction on `g using Polynomial.induction_on' with`. Consider the case `add r t hr ht`. Rewrite using `[map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hr, ht, hdhadd]`.

Consider the case `monomial n c`. Rewrite using `[Polynomial.aeval_monomial, Polynomial.aeval_monomial, Module.End.mul_apply, Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply, hdhsmul]`. Use `congr 1`. Proceed by induction on `n with`. Consider the case `zero => rfl`.

Consider the case `succ n ih`. Rewrite using `[pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]`. Both sides reduce to the same expression. Take `⟨f, hf1, hf⟩` from `hm q hq`. Take `⟨E1, hE1, e1⟩` from `hK P Q pr s hs u hu q f hf (a := p + 1) x hx hdx`.

Take `⟨E2, hE2, e2⟩` from `aeval_diff pr s hs u hu hx hdx f`. Establish `e1' : Polynomial.aeval (TcL (s u) (p + 2) (q + 2)) f x = dv E1` using `e1`. Establish `hfx : Polynomial.aeval (RuL (P` using `P) u (p + 2) (q + 2)) f x = dv E2 + dv E1 := by`. Rewrite using `[← e1', ← e2, sub_add_cancel]`. Use `set c := f.eval 1 with hc`.

Establish `hroot : (f - Polynomial.C c).IsRoot 1` using `by simp [Polynomial.IsRoot, hc]`. Establish `hdiv` using `(Polynomial.mul_divByMonic_eq_iff_isRoot (a := (1 : ℝ))).mpr hroot`. Rewrite `hdiv` using `[mul_comm]`. Use `set g := (f - Polynomial.C c) /ₘ (Polynomial.X - Polynomial.C 1)`. Establish `hkey : Polynomial.aeval (RuL (P` using `P) u (p + 2) (q + 2)) f x - c • x = dh (Polynomial.aeval (RuL (P := P) u (p + 1) (q + 2)) g H) := by`.

Establish `h` using `congrArg (fun r => Polynomial.aeval (RuL (P := P) u (p + 2) (q + 2)) r x) hdiv`. Simplify using `only [map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Module.End.mul_apply, LinearMap.sub_apply, Module.algebraMap_end_apply, map_one, Module.End.one_apply, one_smul] at h`. Rewrite using `[← h, ← hE, hA, map_sub]`. Both sides reduce to the same expression. Take `⟨hG1, hG2⟩` from `hD g`.

Use `⟨-(c⁻¹) • Polynomial.aeval (RuL (P := P) u (p + 1) (q + 2)) g H, c⁻¹ • (E2 + E1), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `g' x' y`. Simplify using `only [Pi.smul_apply]`. Rewrite using `[hG1 g' x' y]`. Rewrite using `[hdvsmul, hG2, smul_zero]`.

Introduce `g' x' y`. Simplify using `only [Pi.smul_apply, Pi.add_apply]`. Rewrite using `[hE1 g' x' y, hE2 g' x' y]`. Rewrite using `[hdhsmul, hdvsmul, hdvadd, ← hkey, ← hfx]`. Rewrite using `[neg_smul, smul_sub, smul_smul, inv_mul_cancel₀ hf1, one_smul]`.

Normalize the expressions using the abelian group laws.
-/
theorem e2VanishingOtherColumns_of_colKillP (hK : ColKillP) : E2VanishingOtherColumns := by
  intro P Q _ _ pr s hs u hu m hm p q hq x hx hdx hdh
  have hpz : ∀ (n : ℕ) (y : Fin n → Q), prism (fun v => v * u) (0 : (Fin (n + 1) → Q) → ℝ) y = 0 := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      rw [prism_succ]
      have : (fun w : Fin (n + 1) → Q => (0 : (Fin (n + 2) → Q) → ℝ) (Fin.cons (y 0) w)) = 0 := rfl
      rw [this, ih]
      simp
  have hlin : ∀ (n : ℕ) (k : ℕ) (c : Fin k → ℝ) (F : Fin k → (Fin (n + 1) → Q) → ℝ) (y : Fin n → Q),
      prism (fun v => v * u) (fun w => ∑ i, c i * F i w) y = ∑ i, c i * prism (fun v => v * u) (F i) y := by
    intro n
    induction n with
    | zero =>
      intro k c F y
      change (0 : ℝ) = ∑ i, c i * (0 : ℝ)
      simp
    | succ n ih =>
      intro k c F y
      rw [prism_succ]
      simp only [prism_succ]
      rw [ih k c (fun i w => F i (Fin.cons (y 0) w)) (Fin.tail y), ← Finset.sum_sub_distrib]
      congr 1
      funext i
      ring
  have htr : ∀ (n : ℕ) (G : (Fin (n + 1) → Q) → ℝ) (g : Q) (y : Fin n → Q),
      prism (fun v => v * u) G (fun j => g * y j) =
        prism (fun v => v * u) (fun v => G (fun j => g * v j)) y := by
    intro n
    induction n with
    | zero => intro G g y; rfl
    | succ n ih =>
      intro G g y
      rw [prism_succ, prism_succ]
      have e1 : (Fin.cons (g * y 0) (fun i => g * y i * u) : Fin (n + 2) → Q) =
          fun j => g * (Fin.cons (y 0) (fun i => y i * u) : Fin (n + 2) → Q) j := by
        funext j
        refine Fin.cases ?_ (fun i => ?_) j
        · simp
        · simp [mul_assoc]
      have e2 : ∀ v : Fin (n + 1) → Q, (Fin.cons (g * y 0) (fun j => g * v j) : Fin (n + 2) → Q) =
          fun j => g * (Fin.cons (y 0) v : Fin (n + 2) → Q) j := by
        intro v
        funext j
        refine Fin.cases ?_ (fun i => ?_) j
        · simp
        · simp
      have ih' := ih (fun w => G (Fin.cons (g * y 0) w)) g (Fin.tail y)
      simp only [e2] at ih'
      simp only [e1]
      congr 1
  let H : Bi P Q (p + 1) (q + 2) := fun x' y => prism (fun v => v * u) (fun x'' => x x'' y) x'
  have hA : dh H = Ru u x - x := by
    funext x' y
    have h := prism_dc (fun v => v * u) p (fun x'' => x x'' y) x'
    have h0 : dc (fun x'' => x x'' y) = 0 := by
      funext v
      exact congrFun (congrFun hdh v) y
    rw [h0, hpz, add_zero] at h
    exact h
  have hB : PInv pr H := by
    intro g x' y
    change prism (fun v => v * u) (fun x'' => x x'' (fun j => g * y j)) (fun i => pr g * x' i) =
      prism (fun v => v * u) (fun x'' => x x'' y) x'
    rw [htr]
    congr 1
    funext v
    exact hx g v y
  have hC : dv H = 0 := by
    funext x' y
    change dc (fun y' => prism (fun v => v * u) (fun x'' => x x'' y') x') y = 0
    simp only [dc]
    have := hlin (p + 1) (q + 3) (fun i => (-1) ^ (i : ℕ)) (fun i x'' => x x'' (fun j => y (i.succAbove j))) x'
    rw [← this]
    have h0 : (fun w => ∑ i : Fin (q + 3), (-1 : ℝ) ^ (i : ℕ) * x w (fun j => y (i.succAbove j))) = 0 := by
      funext w
      exact congrFun (congrFun hdx w) y
    rw [h0, hpz]
  have hdvadd : ∀ {a b : ℕ} (A B : Bi P Q a (b + 1)), dv (A + B) = dv A + dv B := by
    intro a b A B
    funext x y
    simp [dv, dc, Finset.sum_add_distrib, mul_add]
  have hdvsmul : ∀ {a b : ℕ} (c : ℝ) (A : Bi P Q a (b + 1)), dv (c • A) = c • dv A := by
    intro a b c A
    funext x y
    simp [dv, dc, Finset.mul_sum, mul_left_comm]
  have hdhadd : ∀ {a b : ℕ} (A B : Bi P Q (a + 1) b), dh (A + B) = dh A + dh B := by
    intro a b A B
    funext x y
    simp [dh, dc, Finset.sum_add_distrib, mul_add]
  have hdhsmul : ∀ {a b : ℕ} (c : ℝ) (A : Bi P Q (a + 1) b), dh (c • A) = c • dh A := by
    intro a b c A
    funext x y
    simp [dh, dc, Finset.mul_sum, mul_left_comm]
  have hD : ∀ g : Polynomial ℝ, PInv pr (Polynomial.aeval (RuL (P := P) u (p + 1) (q + 2)) g H) ∧
      dv (Polynomial.aeval (RuL (P := P) u (p + 1) (q + 2)) g H) = 0 := by
    intro g
    induction g using Polynomial.induction_on' with
    | add r t hr ht =>
      refine ⟨?_, ?_⟩
      · intro g' x' y
        rw [map_add, LinearMap.add_apply]
        simp only [Pi.add_apply]
        rw [hr.1 g' x' y, ht.1 g' x' y]
      · rw [map_add, LinearMap.add_apply, hdvadd, hr.2, ht.2, add_zero]
    | monomial n c =>
      rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
      obtain ⟨h1, h2⟩ := pow_closed pr s hs u hu hB hC n
      refine ⟨?_, ?_⟩
      · intro g' x' y
        simp only [Pi.smul_apply]
        rw [h1 g' x' y]
      · rw [hdvsmul, h2, smul_zero]
  have hE : ∀ (g : Polynomial ℝ) (F : Bi P Q (p + 1) (q + 2)),
      Polynomial.aeval (RuL (P := P) u (p + 2) (q + 2)) g (dh F) =
        dh (Polynomial.aeval (RuL (P := P) u (p + 1) (q + 2)) g F) := by
    intro g F
    induction g using Polynomial.induction_on' with
    | add r t hr ht =>
      rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hr, ht, hdhadd]
    | monomial n c =>
      rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Module.End.mul_apply,
        Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply, hdhsmul]
      congr 1
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]
        rfl
  obtain ⟨f, hf1, hf⟩ := hm q hq
  obtain ⟨E1, hE1, e1⟩ := hK P Q pr s hs u hu q f hf (a := p + 1) x hx hdx
  obtain ⟨E2, hE2, e2⟩ := aeval_diff pr s hs u hu hx hdx f
  have e1' : Polynomial.aeval (TcL (s u) (p + 2) (q + 2)) f x = dv E1 := e1
  have hfx : Polynomial.aeval (RuL (P := P) u (p + 2) (q + 2)) f x = dv E2 + dv E1 := by
    rw [← e1', ← e2, sub_add_cancel]
  set c := f.eval 1 with hc
  have hroot : (f - Polynomial.C c).IsRoot 1 := by simp [Polynomial.IsRoot, hc]
  have hdiv := (Polynomial.mul_divByMonic_eq_iff_isRoot (a := (1 : ℝ))).mpr hroot
  rw [mul_comm] at hdiv
  set g := (f - Polynomial.C c) /ₘ (Polynomial.X - Polynomial.C 1)
  have hkey : Polynomial.aeval (RuL (P := P) u (p + 2) (q + 2)) f x - c • x =
      dh (Polynomial.aeval (RuL (P := P) u (p + 1) (q + 2)) g H) := by
    have h := congrArg (fun r => Polynomial.aeval (RuL (P := P) u (p + 2) (q + 2)) r x) hdiv
    simp only [map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Module.End.mul_apply,
      LinearMap.sub_apply, Module.algebraMap_end_apply, map_one, Module.End.one_apply, one_smul] at h
    rw [← h, ← hE, hA, map_sub]
    rfl
  obtain ⟨hG1, hG2⟩ := hD g
  refine ⟨-(c⁻¹) • Polynomial.aeval (RuL (P := P) u (p + 1) (q + 2)) g H, c⁻¹ • (E2 + E1), ?_, ?_, ?_, ?_⟩
  · intro g' x' y
    simp only [Pi.smul_apply]
    rw [hG1 g' x' y]
  · rw [hdvsmul, hG2, smul_zero]
  · intro g' x' y
    simp only [Pi.smul_apply, Pi.add_apply]
    rw [hE1 g' x' y, hE2 g' x' y]
  · rw [hdhsmul, hdvsmul, hdvadd, ← hkey, ← hfx]
    rw [neg_smul, smul_sub, smul_smul, inv_mul_cancel₀ hf1, one_smul]
    abel

end PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

end
