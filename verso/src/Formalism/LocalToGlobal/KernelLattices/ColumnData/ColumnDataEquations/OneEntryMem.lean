import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.ZeroInjectionMemFourthPower

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J

open Formalism.L2.PairingIndexBounds.Eq.J Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.Ker.Cd.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq Formalism.L2.Ker

section Gen

variable {n : Type} [Fintype n] [DecidableEq n] {N N' : ℕ}

def ent (k : Fin N' × Fin N) (z : n → Fin N' → Fin N → ℂ) : n → ℂ := fun τ => z τ k.1 k.2

def setE (z : n → Fin N' → Fin N → ℂ) (k : Fin N' × Fin N) (w : n → ℂ) : n → Fin N' → Fin N → ℂ :=
  fun τ i j => if (i, j) = k then w τ else z τ i j

def repl (a : n → ℂ) (s : Finset (Fin N' × Fin N)) (z : n → Fin N' → Fin N → ℂ) : n → Fin N' → Fin N → ℂ :=
  fun τ i j => if (i, j) ∈ s then a τ else z τ i j

omit [Fintype n] [DecidableEq n] in
/- English proof (translation)
Use function extensionality and compare the values at `τ`. Distinguish the cases in `h : p = k`. Substitute `h` using the available equality. Simplify using `[ent, putL]`. Simplify using `[ent, putL, h]`.
-/
theorem ent_putL (k p : Fin N' × Fin N) (x : n → ℂ) : ent p (putL n N N' k x) = if p = k then x else 0 := by
  funext τ
  by_cases h : p = k
  · subst h
    simp [ent, putL]
  · simp [ent, putL, h]

omit [Fintype n] [DecidableEq n] in
/- English proof (translation)
Use function extensionality and compare the values at `τ`. Simplify using `[ent, setE]`.
-/
theorem ent_setE (z : n → Fin N' → Fin N → ℂ) (k : Fin N' × Fin N) (w : n → ℂ) : ent k (setE z k w) = w := by
  funext τ
  simp [ent, setE]

omit [Fintype n] [DecidableEq n] in
/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Unfold `setE ent`. Use `split_ifs with h`. Rewrite using `[← h]`. Both sides reduce to the same expression.
-/
theorem setE_ent (z : n → Fin N' → Fin N → ℂ) (k : Fin N' × Fin N) : setE z k (ent k z) = z := by
  funext τ i j
  unfold setE ent
  split_ifs with h
  · rw [← h]
  · rfl

omit [Fintype n] [DecidableEq n] in
/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Apply the tactic sequence `by_cases h : (i, j) = k <;> simp [setE, putL, h]`.
-/
theorem setE_add (z : n → Fin N' → Fin N → ℂ) (k : Fin N' × Fin N) (w x : n → ℂ) :
    setE z k w + putL n N N' k x = setE z k (w + x) := by
  funext τ i j
  by_cases h : (i, j) = k <;> simp [setE, putL, h]

/- English proof (translation)
Establish `hs : ∀ τ, (∑ i, ∑ j, y τ i j * conj (if (i, j) = k then x τ else 0)) = y τ k.1 k.2 * conj (x τ)`. Introduce `τ`. Rewrite using `[Finset.sum_eq_single k.1, Finset.sum_eq_single k.2]`. Simplify using the standard rewrite rules. Introduce `j _ hj`.

Simplify using `[Prod.ext_iff, hj]`. Simplify using the standard rewrite rules. Introduce `i _ hi`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `j _`.

Simplify using `[Prod.ext_iff, hi]`. Simplify using the standard rewrite rules. Use `show (∑ τ, ∑ i, ∑ j, y τ i j * conj ((putL n N N' k x) τ i j)) / ((Formalism.L2.Th1.F.area L : ℝ) : ℂ) = ∑ i, ∑ j, ent k y i * hOne L n i j * conj (x j)`. Simplify using `only [putL, LinearMap.coe_mk, AddHom.coe_mk]`. Simplify using `only [hs]`.

Simplify using `only [hOne, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, ent]`. Rewrite using `[Finset.sum_div]`. Use `Finset.sum_congr rfl (fun τ _ => ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_put (L : PeriodPair) (y : n → Fin N' → Fin N → ℂ) (k : Fin N' × Fin N) (x : n → ℂ) :
    formV (Formalism.L2.Th1.F.area L) n N N' y (putL n N N' k x) = matH (hOne L n) (ent k y) x := by
  have hs : ∀ τ, (∑ i, ∑ j, y τ i j * conj (if (i, j) = k then x τ else 0)) = y τ k.1 k.2 * conj (x τ) := by
    intro τ
    rw [Finset.sum_eq_single k.1, Finset.sum_eq_single k.2]
    · simp
    · intro j _ hj
      simp [Prod.ext_iff, hj]
    · simp
    · intro i _ hi
      apply Finset.sum_eq_zero
      intro j _
      simp [Prod.ext_iff, hi]
    · simp
  show (∑ τ, ∑ i, ∑ j, y τ i j * conj ((putL n N N' k x) τ i j)) / ((Formalism.L2.Th1.F.area L : ℝ) : ℂ) =
    ∑ i, ∑ j, ent k y i * hOne L n i j * conj (x j)
  simp only [putL, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [hs]
  simp only [hOne, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, ite_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, ent]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  ring

/- English proof (translation)
Unfold `alphaQ qOf`. Rewrite using `[form_put, ent_putL, if_pos rfl]`.
-/
theorem alphaQ_put (c : ℝ) (L : PeriodPair) (k : Fin N' × Fin N) (x : n → ℂ) :
    alphaQ c (formV (Formalism.L2.Th1.F.area L) n N N') (putL n N N' k x) = alphaQ c (matH (hOne L n)) x := by
  unfold alphaQ qOf
  rw [form_put, ent_putL, if_pos rfl]

/- English proof (translation)
Use `⟨fun w _ => ?_, fun x hx w => ?_⟩` and prove the remaining obligations. Establish `e : (fun w => F (setE z k w)) = fun w => F (setE z k 0 + putL n N N' k w)`. Use function extensionality and compare the values at `w'`. Rewrite using `[setE_add, zero_add]`. Rewrite using `[e]`.

Conclude with `AnalyticAt.comp (g := F) (f := fun w => setE z k 0 + putL n N N' k w) (hF.1 _ (Set.mem_univ _)) (analyticAt_const.add ((LinearMap.toContinuousLinearMap (putL n N N' k)).analyticAt w))`. Establish `hX : putL n N N' k x ∈ powLat ΛM N N'`. Introduce `i j`. Distinguish the cases in `h : (i, j) = k`. Simplify using `only [putL, LinearMap.coe_mk, AddHom.coe_mk, h, if_true]`.

Conclude with `hx`. Simplify using `only [putL, LinearMap.coe_mk, AddHom.coe_mk, h, if_false]`. Conclude with `ΛM.zero_mem`. Establish `h` using `hF.2 (putL n N N' k x) hX (setE z k w)`. Simplify using `only [Formalism.L2.Th1.H.opU] at h ⊢`.

Rewrite `h` using `[setE_add, form_put, form_put, ent_setE, ent_putL, if_pos rfl, alphaQ_put]`. Conclude with `h`.
-/
theorem oneEntry_mem (c : ℝ) (L : PeriodPair) (ΛM : AddSubgroup (n → ℂ)) {F : (n → Fin N' → Fin N → ℂ) → ℂ}
    (hF : F ∈ Formalism.L2.Th1.H.Th (formV (Formalism.L2.Th1.F.area L) n N N') (alphaQ c (formV (Formalism.L2.Th1.F.area L) n N N'))
      (powLat ΛM N N')) (z : n → Fin N' → Fin N → ℂ) (k : Fin N' × Fin N) :
    (fun w => F (setE z k w)) ∈ Formalism.L2.Th1.H.Th (matH (hOne L n)) (alphaQ c (matH (hOne L n))) ΛM := by
  refine ⟨fun w _ => ?_, fun x hx w => ?_⟩
  · have e : (fun w => F (setE z k w)) = fun w => F (setE z k 0 + putL n N N' k w) := by
      funext w'
      rw [setE_add, zero_add]
    rw [e]
    exact AnalyticAt.comp (g := F) (f := fun w => setE z k 0 + putL n N N' k w) (hF.1 _ (Set.mem_univ _))
      (analyticAt_const.add ((LinearMap.toContinuousLinearMap (putL n N N' k)).analyticAt w))
  · have hX : putL n N N' k x ∈ powLat ΛM N N' := by
      intro i j
      by_cases h : (i, j) = k
      · simp only [putL, LinearMap.coe_mk, AddHom.coe_mk, h, if_true]
        exact hx
      · simp only [putL, LinearMap.coe_mk, AddHom.coe_mk, h, if_false]
        exact ΛM.zero_mem
    have h := hF.2 (putL n N N' k x) hX (setE z k w)
    simp only [Formalism.L2.Th1.H.opU] at h ⊢
    rw [setE_add, form_put, form_put, ent_setE, ent_putL, if_pos rfl, alphaQ_put] at h
    exact h

/- English proof (translation)
Introduce `F hF`. Choose the witnesses or unpack the hypotheses as in `⟨a₀, ha₀⟩ : ∃ a₀, θ a₀ ≠ 0 := by`. Assume the negation of the conclusion as `hno`. Use `push Not at hno`. Conclude with `hθ0 (funext hno)`.

Establish `step : ∀ (z : n → Fin N' → Fin N → ℂ) (k : Fin N' × Fin N), F z * θ a₀ = F (setE z k a₀) * θ (ent k z)`. Introduce `z k`. Take `⟨a, ha⟩` from `hline _ (oneEntry_mem c L ΛM hF z k)`. Establish `h1 : F (setE z k (ent k z)) = a * θ (ent k z)` using `congrFun ha (ent k z)`. Establish `h2 : F (setE z k a₀) = a * θ a₀` using `congrFun ha a₀`.

Rewrite `h1` using `[setE_ent]`. Rewrite using `[h1, h2]`. Expand and normalize the polynomial expressions, which then agree. Establish `ind : ∀ (s : Finset (Fin N' × Fin N)) (z : n → Fin N' → Fin N → ℂ), F z * θ a₀ ^ s.card = F (repl a₀ s z) * ∏ p ∈ s, θ (ent p z)`. Introduce `s`.

Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `z`. Establish `: repl a₀ (∅ : Finset (Fin N' × Fin N)) z = z`. Use function extensionality and compare the values at `τ i j`.

Simplify using `[repl]`. Simplify using `[this]`. Consider the case `insert k s hk ih`. Introduce `z`. Establish `key` using `step (repl a₀ s z) k`.

Establish `e1 : setE (repl a₀ s z) k a₀ = repl a₀ (insert k s) z`. Use function extensionality and compare the values at `τ i j`. Apply the tactic sequence `by_cases h : (i, j) = k <;> simp [setE, repl, Finset.mem_insert, h]`. Establish `e2 : ent k (repl a₀ s z) = ent k z`. Use function extensionality and compare the values at `τ`.

Simplify using `[ent, repl, hk]`. Rewrite `key` using `[e1, e2]`. Rewrite using `[Finset.card_insert_of_notMem hk, pow_succ, ← mul_assoc, ih z, Finset.prod_insert hk]`. Take the linear combination `(∏ p ∈ s, θ (ent p z)) * key`. Use `⟨F (fun τ _ _ => a₀ τ) / θ a₀ ^ (Finset.univ : Finset (Fin N' × Fin N)).card, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `z`. Establish `h` using `ind Finset.univ z`. Establish `e1 : repl a₀ (Finset.univ : Finset (Fin N' × Fin N)) z = fun τ _ _ => a₀ τ`. Use function extensionality and compare the values at `τ i j`. Simplify using `[repl]`.

Establish `e2 : tensPow θ N N' z = ∏ p : Fin N' × Fin N, θ (ent p z)`. Unfold `tensPow`. Conclude with `(Fintype.prod_prod_type' (f := fun i j => θ fun τ => z τ i j)).symm`. Rewrite `h` using `[e1]`. Use `show F z = _ * tensPow θ N N' z`.

Rewrite using `[e2, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero _ ha₀)]`. Conclude with `h`.
-/
theorem tens_spans (c : ℝ) (L : PeriodPair) (ΛM : AddSubgroup (n → ℂ)) {θ : (n → ℂ) → ℂ} (hθ0 : θ ≠ 0)
    (hline : ∀ G ∈ Formalism.L2.Th1.H.Th (matH (hOne L n)) (alphaQ c (matH (hOne L n))) ΛM, ∃ a : ℂ, G = a • θ)
    (N N' : ℕ) :
    ∀ F ∈ Formalism.L2.Th1.H.Th (formV (Formalism.L2.Th1.F.area L) n N N') (alphaQ c (formV (Formalism.L2.Th1.F.area L) n N N'))
      (powLat ΛM N N'), ∃ a : ℂ, F = a • tensPow θ N N' := by
  intro F hF
  obtain ⟨a₀, ha₀⟩ : ∃ a₀, θ a₀ ≠ 0 := by
    by_contra hno
    push Not at hno
    exact hθ0 (funext hno)
  have step : ∀ (z : n → Fin N' → Fin N → ℂ) (k : Fin N' × Fin N),
      F z * θ a₀ = F (setE z k a₀) * θ (ent k z) := by
    intro z k
    obtain ⟨a, ha⟩ := hline _ (oneEntry_mem c L ΛM hF z k)
    have h1 : F (setE z k (ent k z)) = a * θ (ent k z) := congrFun ha (ent k z)
    have h2 : F (setE z k a₀) = a * θ a₀ := congrFun ha a₀
    rw [setE_ent] at h1
    rw [h1, h2]
    ring
  have ind : ∀ (s : Finset (Fin N' × Fin N)) (z : n → Fin N' → Fin N → ℂ),
      F z * θ a₀ ^ s.card = F (repl a₀ s z) * ∏ p ∈ s, θ (ent p z) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro z
      have : repl a₀ (∅ : Finset (Fin N' × Fin N)) z = z := by
        funext τ i j
        simp [repl]
      simp [this]
    | insert k s hk ih =>
      intro z
      have key := step (repl a₀ s z) k
      have e1 : setE (repl a₀ s z) k a₀ = repl a₀ (insert k s) z := by
        funext τ i j
        by_cases h : (i, j) = k <;> simp [setE, repl, Finset.mem_insert, h]
      have e2 : ent k (repl a₀ s z) = ent k z := by
        funext τ
        simp [ent, repl, hk]
      rw [e1, e2] at key
      rw [Finset.card_insert_of_notMem hk, pow_succ, ← mul_assoc, ih z, Finset.prod_insert hk]
      linear_combination (∏ p ∈ s, θ (ent p z)) * key
  refine ⟨F (fun τ _ _ => a₀ τ) / θ a₀ ^ (Finset.univ : Finset (Fin N' × Fin N)).card, ?_⟩
  funext z
  have h := ind Finset.univ z
  have e1 : repl a₀ (Finset.univ : Finset (Fin N' × Fin N)) z = fun τ _ _ => a₀ τ := by
    funext τ i j
    simp [repl]
  have e2 : tensPow θ N N' z = ∏ p : Fin N' × Fin N, θ (ent p z) := by
    unfold tensPow
    exact (Fintype.prod_prod_type' (f := fun i j => θ fun τ => z τ i j)).symm
  rw [e1] at h
  show F z = _ * tensPow θ N N' z
  rw [e2, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero _ ha₀)]
  exact h

end Gen

variable {D : Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {B : Cd.Base D cc δ}

/- English proof (translation)
Introduce `F hF`. Establish `e : TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ) = Formalism.L2.Th1.F.area B.L` using `B.areaOK`. Establish `h0' : TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') = powLat B.lamM N N'` using `B.lat0OK N N'`. Establish `h1 : F ∈ Formalism.L2.Th1.H.Th (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (alphaQ B.cq (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N')) (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesG …`. Use `Th_congr _ _ _ _ (fun x hx => ?_) hF` and prove the remaining obligations.

Take `⟨m, hm⟩` from `B.qInt0 hS N N' x hx`. Conclude with `al_eq D B.tor x m hm`. Rewrite `h1` using `[e, h0']`. Conclude with `tens_spans B.cq B.L B.lamM (B.thMM_ne_zero hS) (isThM_spans _ _ _ _ _ _ hS B.kappa_ne_zero (B.thMM_spec hS)) N N' F h1`.
-/
theorem thZeroSpans (hS : B.StdOK) (N N' : ℕ) : B.ThZeroSpans N N' := by
  intro F hF
  have e : TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ) = Formalism.L2.Th1.F.area B.L := B.areaOK
  have h0' : TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') = powLat B.lamM N N' := B.lat0OK N N'
  have h1 : F ∈ Formalism.L2.Th1.H.Th (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N')
      (alphaQ B.cq (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N'))
      (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) := by
    refine Th_congr _ _ _ _ (fun x hx => ?_) hF
    obtain ⟨m, hm⟩ := B.qInt0 hS N N' x hx
    exact al_eq D B.tor x m hm
  rw [e, h0'] at h1
  exact tens_spans B.cq B.L B.lamM (B.thMM_ne_zero hS)
    (isThM_spans _ _ _ _ _ _ hS B.kappa_ne_zero (B.thMM_spec hS)) N N' F h1

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J
