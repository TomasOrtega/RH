import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LeadMinor
import Development.WeilBound.CoreStatements.HodgeTatePoints.GeFrame
import Development.WeilBound.CoreStatements.HodgeTatePoints.GaGram
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FinitelyGeneratedHomology
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct Filter

namespace PositivityTheory.HtPt.Ge

section Loc
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

def loc (B : Subalgebra o Ω) (u : Ω) (hu : u ∈ B) : Subring Ω where
  carrier := {a | ∃ n : ℕ, u ^ n * a ∈ B}
  one_mem' := ⟨0, by simp⟩
  zero_mem' := ⟨0, by simp⟩
  neg_mem' := fun ⟨n, h⟩ => ⟨n, by rw [mul_neg]; exact neg_mem h⟩
  mul_mem' := fun ⟨n, h⟩ ⟨n', h'⟩ => ⟨n + n', by
    have := mul_mem h h'
    rwa [mul_mul_mul_comm, ← pow_add] at this⟩
  add_mem' := fun {a b} ⟨n, h⟩ ⟨n', h'⟩ => ⟨n + n', by
    have := add_mem (mul_mem (pow_mem hu n') h) (mul_mem (pow_mem hu n) h')
    convert this using 1
    ring⟩

variable {B : Subalgebra o Ω} {u : Ω} {hu : u ∈ B}

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, by simpa using h⟩`.
-/
theorem loc_of_mem {a : Ω} (h : a ∈ B) : a ∈ loc B u hu := ⟨0, by simpa using h⟩

/- English proof (translation)
Take `⟨n, h⟩` from `h`. Use `filter_upwards [eventually_ge_atTop n] with m hm`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hm`. Use `mul_mem (pow_mem hu d) h` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem loc_ev {a : Ω} (h : a ∈ loc B u hu) : ∀ᶠ n in atTop, u ^ n * a ∈ B := by
  obtain ⟨n, h⟩ := h
  filter_upwards [eventually_ge_atTop n] with m hm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  have := mul_mem (pow_mem hu d) h
  convert this using 1
  ring

/- English proof (translation)
Take `⟨m, h⟩` from `h`. Conclude with `⟨m + n, by rwa [pow_add, mul_assoc]⟩`.
-/
theorem loc_of_pow {a : Ω} (n : ℕ) (h : u ^ n * a ∈ loc B u hu) : a ∈ loc B u hu := by
  obtain ⟨m, h⟩ := h
  exact ⟨m + n, by rwa [pow_add, mul_assoc]⟩

variable {V : Type} [AddCommGroup V] [Module Ω V]

def locM (M : Submodule B V) (u : Ω) (hu : u ∈ B) : AddSubgroup V where
  carrier := {v | ∃ n : ℕ, u ^ n • v ∈ M}
  zero_mem' := ⟨0, by simp⟩
  neg_mem' := fun ⟨n, h⟩ => ⟨n, by rw [smul_neg]; exact neg_mem h⟩
  add_mem' := fun {a b} ⟨n, h⟩ ⟨n', h'⟩ => ⟨n + n', by
    have := add_mem (M.smul_mem ⟨_, pow_mem hu n'⟩ h) (M.smul_mem ⟨_, pow_mem hu n⟩ h')
    simp only [Subalgebra.smul_def, smul_smul, ← pow_add] at this
    rwa [smul_add, add_comm n' n] at *⟩

/- English proof (translation)
Take `⟨n, h⟩` from `ha`. Take `⟨n', h'⟩` from `hv`. Use `⟨n + n', ?_⟩` and prove the remaining obligations. Use `M.smul_mem ⟨_, h⟩ h'` as an intermediate fact. Simplify using `only [Subalgebra.smul_def, smul_smul] at this ⊢`.

Use `this using 2` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem locM_smul {M : Submodule B V} {a : Ω} {v : V} (ha : a ∈ loc B u hu) (hv : v ∈ locM M u hu) :
    a • v ∈ locM M u hu := by
  obtain ⟨n, h⟩ := ha
  obtain ⟨n', h'⟩ := hv
  refine ⟨n + n', ?_⟩
  have := M.smul_mem ⟨_, h⟩ h'
  simp only [Subalgebra.smul_def, smul_smul] at this ⊢
  convert this using 2
  ring

/- English proof (translation)
Take `⟨n, h⟩` from `h`. Use `filter_upwards [eventually_ge_atTop n] with m hm`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hm`. Use `M.smul_mem ⟨_, pow_mem hu d⟩ h` as an intermediate fact. Simplify using `only [Subalgebra.smul_def, smul_smul] at this`.

Rewrite using `[add_comm, pow_add]` and apply the resulting hypothesis.
-/
theorem locM_ev {M : Submodule B V} {v : V} (h : v ∈ locM M u hu) : ∀ᶠ n in atTop, u ^ n • v ∈ M := by
  obtain ⟨n, h⟩ := h
  filter_upwards [eventually_ge_atTop n] with m hm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  have := M.smul_mem ⟨_, pow_mem hu d⟩ h
  simp only [Subalgebra.smul_def, smul_smul] at this
  rwa [add_comm, pow_add]

/- English proof (translation)
Establish `h1 : LinearIndependent Ω (fun a => ι (b a))` using `(LinearIndependent.iff_fractionRing B Ω).1 (b.linearIndependent.map' ι (LinearMap.ker_eq_bot.2 hι))`. Establish `h2 : ∑ a, (u ^ n * T a - (b.repr x a : Ω)) • ι (b a) = 0`. Simplify using `only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, e]`. Use `congrArg ι (b.sum_repr x)` as an intermediate fact. Simplify using `only [map_sum, map_smul, Subalgebra.smul_def] at this`.

Rewrite using `[this, sub_self]`. Use `Fintype.linearIndependent_iff.1 h1 _ h2 a` as an intermediate fact. Conclude with `⟨n, by rw [sub_eq_zero.1 this]; exact (b.repr x a).2⟩`.
-/
theorem coef_mem [IsFractionRing B Ω] {P : Type} [AddCommGroup P] [Module B P] (ι : P →ₗ[B] V)
    (hι : Function.Injective ι) {k : ℕ} (b : Basis (Fin k) B P) (T : Fin k → Ω) (n : ℕ) (x : P)
    (e : u ^ n • ∑ a, T a • ι (b a) = ι x) (a : Fin k) : T a ∈ loc B u hu := by
  have h1 : LinearIndependent Ω (fun a => ι (b a)) :=
    (LinearIndependent.iff_fractionRing B Ω).1 (b.linearIndependent.map' ι (LinearMap.ker_eq_bot.2 hι))
  have h2 : ∑ a, (u ^ n * T a - (b.repr x a : Ω)) • ι (b a) = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, e]
    have := congrArg ι (b.sum_repr x)
    simp only [map_sum, map_smul, Subalgebra.smul_def] at this
    rw [this, sub_self]
  have := Fintype.linearIndependent_iff.1 h1 _ h2 a
  exact ⟨n, by rw [sub_eq_zero.1 this]; exact (b.repr x a).2⟩

/- English proof (translation)
Use `set ψ := ∑ a, T a • φ a with hψ`. Take `⟨S, hS⟩` from `hW`. Take `⟨n, hn⟩` from `((eventually_all_finset S).2 fun z hz => loc_ev (h z (hS ▸ Submodule.subset_span hz))).exists`. Establish `hn' : ∀ z ∈ W, u ^ n * ψ z ∈ B`. Introduce `z hz`.

Rewrite `hz` using `[← hS]`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx => exact hn x hx`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add, mul_add]`.

Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx`. Rewrite using `[Subalgebra.smul_def, map_smul, smul_eq_mul, mul_left_comm]`. Conclude with `mul_mem c.2 hx`. Set `x : Dual B W` to `{ toFun := fun z => ⟨_, hn' z z.2⟩ map_add' := fun z z' => Subtype.ext (by simp [mul_add]) map_smul' := fun c z => Subtype.ext (by simp [Subalgebra.smul_def, mul_left_comm]) }`.

Set `ι : Dual B W →ₗ[B] (W → Ω)` to `{ toFun := fun f z => (f z : Ω) map_add' := fun f g => by ext z; simp map_smul' := fun c f => by ext z; simp [Subalgebra.smul_def] }`. Use `coef_mem ι (fun f g e => LinearMap.ext fun z => Subtype.ext (congrFun e z)) b T n x ?_ a` and prove the remaining obligations. Use extensionality with `z`. Simplify using `[ι, x, hψ, hφ]`.
-/
theorem coef_mem_dual [IsFractionRing B Ω] (W : Submodule B V) (hW : W.FG) {j : ℕ}
    (b : Basis (Fin j) B (Dual B W)) (φ : Fin j → Dual Ω V) (hφ : ∀ a (z : W), (b a z : Ω) = φ a z)
    (T : Fin j → Ω) (h : ∀ z ∈ W, (∑ a, T a • φ a) z ∈ loc B u hu) (a : Fin j) : T a ∈ loc B u hu := by
  set ψ := ∑ a, T a • φ a with hψ
  obtain ⟨S, hS⟩ := hW
  obtain ⟨n, hn⟩ := ((eventually_all_finset S).2 fun z hz =>
    loc_ev (h z (hS ▸ Submodule.subset_span hz))).exists
  have hn' : ∀ z ∈ W, u ^ n * ψ z ∈ B := by
    intro z hz
    rw [← hS] at hz
    induction hz using Submodule.span_induction with
    | mem x hx => exact hn x hx
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, mul_add]; exact add_mem hx hy
    | smul c x _ hx =>
      rw [Subalgebra.smul_def, map_smul, smul_eq_mul, mul_left_comm]; exact mul_mem c.2 hx
  let x : Dual B W :=
    { toFun := fun z => ⟨_, hn' z z.2⟩
      map_add' := fun z z' => Subtype.ext (by simp [mul_add])
      map_smul' := fun c z => Subtype.ext (by simp [Subalgebra.smul_def, mul_left_comm]) }
  let ι : Dual B W →ₗ[B] (W → Ω) :=
    { toFun := fun f z => (f z : Ω)
      map_add' := fun f g => by ext z; simp
      map_smul' := fun c f => by ext z; simp [Subalgebra.smul_def] }
  refine coef_mem ι (fun f g e => LinearMap.ext fun z => Subtype.ext (congrFun e z)) b T n x ?_ a
  ext z
  simp [ι, x, hψ, hφ]

end Loc

/- English proof (translation)
Use `choose cf f1 f2 f3 using hf`. Use `choose cg g1 g2 g3 using hg`. Set `F : Matrix (Fin n) (Fin n) Ω` to `Matrix.of fun a' a => cf a a'`. Set `G : Matrix (Fin n) (Fin n) Ω` to `Matrix.of fun a' a => cg a a'`. Establish `hF : F.BlockTriangular id` using `fun a' a h => f1 a a' h`.

Establish `hG : G.BlockTriangular id` using `fun a' a h => g1 a a' h`. Establish `hdet : IsUnit G.det`. Rewrite using `[Matrix.det_of_upperTriangular hG, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]`. Introduce `a _`. Simplify `hg0 a` using `[G, g2]`.

Use `haveI := G.invertibleOfIsUnitDet hdet`. Establish `hT : (G⁻¹ * F).BlockTriangular id` using `(Matrix.blockTriangular_inv_of_blockTriangular hG).mul hF`. Establish `e : G * (G⁻¹ * F) = F` using `Matrix.mul_nonsing_inv_cancel_left _ _ hdet`. Use `⟨G⁻¹ * F, fun a' a h => hT h, fun a => ?_, fun a => ?_⟩` and prove the remaining obligations. Use `congrFun (congrFun e a) a` as an intermediate fact.

Rewrite `this` using `[Matrix.mul_apply, Finset.sum_eq_single a]`. Rewrite using `[eq_div_iff (hg0 a), ← g2, ← f2, mul_comm]`. Conclude with `this`. Introduce `l _ hl`. Break down `lt_or_gt_of_ne hl with h | h` into its components or cases.

Rewrite using `[hG h, zero_mul]`. Rewrite using `[hT h, mul_zero]`. Simplify using the standard rewrite rules. Simplify using `only [g3, Finset.smul_sum, smul_smul]`. Rewrite using `[f3, Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_smul]`. Use `congr 1`. Use `congrFun (congrFun e l) a` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply]`.

Use `Eq.trans ?_ (this.symm.trans (Finset.sum_congr rfl fun _ _ => mul_comm _ _))` and prove the remaining obligations. Both sides reduce to the same expression.
-/
theorem tri {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {n : ℕ} (w f g : Fin n → V) (df dg : Fin n → Ω)
    (hg0 : ∀ a, dg a ≠ 0)
    (hf : ∀ a, ∃ cf : Fin n → Ω, (∀ a', a < a' → cf a' = 0) ∧ cf a = df a ∧ f a = ∑ a', cf a' • w a')
    (hg : ∀ a, ∃ cf : Fin n → Ω, (∀ a', a < a' → cf a' = 0) ∧ cf a = dg a ∧ g a = ∑ a', cf a' • w a') :
    ∃ T : Matrix (Fin n) (Fin n) Ω, (∀ a' a, a < a' → T a' a = 0) ∧ (∀ a, T a a = df a / dg a) ∧
      ∀ a, f a = ∑ a', T a' a • g a' := by
  choose cf f1 f2 f3 using hf
  choose cg g1 g2 g3 using hg
  let F : Matrix (Fin n) (Fin n) Ω := Matrix.of fun a' a => cf a a'
  let G : Matrix (Fin n) (Fin n) Ω := Matrix.of fun a' a => cg a a'
  have hF : F.BlockTriangular id := fun a' a h => f1 a a' h
  have hG : G.BlockTriangular id := fun a' a h => g1 a a' h
  have hdet : IsUnit G.det := by
    rw [Matrix.det_of_upperTriangular hG, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro a _
    simpa [G, g2] using hg0 a
  haveI := G.invertibleOfIsUnitDet hdet
  have hT : (G⁻¹ * F).BlockTriangular id := (Matrix.blockTriangular_inv_of_blockTriangular hG).mul hF
  have e : G * (G⁻¹ * F) = F := Matrix.mul_nonsing_inv_cancel_left _ _ hdet
  refine ⟨G⁻¹ * F, fun a' a h => hT h, fun a => ?_, fun a => ?_⟩
  · have := congrFun (congrFun e a) a
    rw [Matrix.mul_apply, Finset.sum_eq_single a] at this
    · rw [eq_div_iff (hg0 a), ← g2, ← f2, mul_comm]
      exact this
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hG h, zero_mul]
      · rw [hT h, mul_zero]
    · simp
  · simp only [g3, Finset.smul_sum, smul_smul]
    rw [f3, Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    have := congrFun (congrFun e l) a
    rw [Matrix.mul_apply] at this
    refine Eq.trans ?_ (this.symm.trans (Finset.sum_congr rfl fun _ _ => mul_comm _ _))
    rfl

section
variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ}
  {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
  (D : HTChart A K c p R N Ω)

/- English proof (translation)
Apply the tactic sequence `apply _root_.UpperTheory.Reformulated.B.FinitelyGeneratedHomology.omHT_fg <;> assumption`.
-/
theorem omHT_fg (σ : E →+* K) : (D.omHT σ).FG :=
  by apply _root_.UpperTheory.Reformulated.B.FinitelyGeneratedHomology.omHT_fg <;> assumption

end

end PositivityTheory.HtPt.Ge
