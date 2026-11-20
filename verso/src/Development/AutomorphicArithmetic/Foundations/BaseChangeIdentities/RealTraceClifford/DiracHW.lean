import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.DiracAlg
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.SpnAdj
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.SpnCas
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Gelf2

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

/- English proof (translation)
Use function extensionality and compare the values at `a`. Establish `h1 : (univ.filter fun b : Fin n => a < b ∧ True) = Finset.Ioi a`. Use extensionality with `b`. Simplify using the standard rewrite rules. Establish `h2 : (univ.filter fun b : Fin n => b < a ∧ True) = Finset.Iio a`.

Use extensionality with `b`. Simplify using the standard rewrite rules. Establish `h3 : ((n - 1 - (a : ℕ) : ℕ) : ℝ) = (n : ℝ) - 1 - (a : ℕ)`. Use `a.2` as an intermediate fact. Rewrite using `[Nat.sub_sub, Nat.cast_sub (by omega)]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Formalism.REAL.rhoC, rhoV, eq_self_iff_true]`. Rewrite using `[h1, h2, Fin.card_Ioi, Fin.card_Iio, h3]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem rhoC_true (n : ℕ) : Formalism.REAL.rhoC (fun _ : Fin n => true) = rhoV n := by
  funext a
  have h1 : (univ.filter fun b : Fin n => a < b ∧ True) = Finset.Ioi a := by
    ext b; simp
  have h2 : (univ.filter fun b : Fin n => b < a ∧ True) = Finset.Iio a := by
    ext b; simp
  have h3 : ((n - 1 - (a : ℕ) : ℕ) : ℝ) = (n : ℝ) - 1 - (a : ℕ) := by
    have := a.2
    rw [Nat.sub_sub, Nat.cast_sub (by omega)]
    push_cast
    ring
  simp only [Formalism.REAL.rhoC, rhoV, eq_self_iff_true]
  rw [h1, h2, Fin.card_Ioi, Fin.card_Iio, h3]
  ring

/- English proof (translation)
Simplify using `[Formalism.REAL.nsq, Formalism.REAL.dot, nsq, sq]`.
-/
private theorem nsq_eq {n : ℕ} (u : Fin n → ℝ) : Formalism.REAL.nsq u = nsq u := by
  simp [Formalism.REAL.nsq, Formalism.REAL.dot, nsq, sq]

/- English proof (translation)
Simplify using `[Cas, map_sum, map_mul]`.
-/
private theorem cas_map {A B : Type} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B] {n : ℕ} (φ : A →ₐ[ℂ] B)
    (F : Fin n → Fin n → A) : φ (Cas F) = Cas fun a b => φ (F a b) := by
  simp [Cas, map_sum, map_mul]

/- English proof (translation)
Apply the tactic sequence `by_cases h : a = b <;> simp [spn, map_sum, map_sub, map_mul, h]`.
-/
private theorem spn_map {A B : Type} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B] {n : ℕ} (φ : A →ₐ[ℂ] B)
    (c : Fin n → Fin n → A) (a b : Fin n) : φ (spn c a b) = spn (fun a b => φ (c a b)) a b := by
  by_cases h : a = b <;> simp [spn, map_sum, map_sub, map_mul, h]

/- English proof (translation)
Introduce `a b c d`. Use `congrArg φ (h a b c d)` as an intermediate fact. Simplify using `only [map_sub, map_mul] at this`. Rewrite using `[this]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem gl_map {A B : Type} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B] {n : ℕ} (φ : A →ₐ[ℂ] B)
    {F : Fin n → Fin n → A} (h : GlRel F) : GlRel fun a b => φ (F a b) := by
  intro a b c d
  have := congrArg φ (h a b c d)
  simp only [map_sub, map_mul] at this
  rw [this]
  split_ifs <;> simp

/- English proof (translation)
Introduce `a b d e`. Use `congrArg φ (h a b d e)` as an intermediate fact. Simplify using `only [map_add, map_mul] at this`. Rewrite using `[this]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem clif_map {A B : Type} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B] {n : ℕ} (φ : A →ₐ[ℂ] B)
    {c : Fin n → Fin n → A} (h : Clif c) : Clif fun a b => φ (c a b) := by
  intro a b d e
  have := congrArg φ (h a b d e)
  simp only [map_add, map_mul] at this
  rw [this]
  split_ifs <;> simp

/- English proof (translation)
Simplify using `[Cas, gelA, epow, Finset.sum_ite_eq]`.
-/
private theorem cas_gel {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) : Cas E = gelA E 2 := by
  simp [Cas, gelA, epow, Finset.sum_ite_eq]

/- English proof (translation)
Rewrite using `[← cas_gel, Cas, Cas, Finset.sum_comm]`. Simplify using `[barF]`.
-/
private theorem cas_bar {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) : Cas E = gelA (barF E) 2 := by
  rw [← cas_gel, Cas, Cas, Finset.sum_comm]
  simp [barF]

/- English proof (translation)
Introduce `a b c d`. Establish `e1` using `hP.gl1 a b c d`. Establish `e2` using `hP.gl2 a b c d`. Establish `h : (E1 a b + E2 a b) * (E1 c d + E2 c d) - (E1 c d + E2 c d) * (E1 a b + E2 a b) = (E1 a b * E1 c d - E1 c d * E1 a b) + (E2 a b * E2 c d - E2 c d * E2 a b)`. Simplify using `only [add_mul, mul_add]`.

Rewrite using `[hP.comm a b c d, hP.comm c d a b]`. Normalize the expressions using the abelian group laws. Simplify using `only [kF]`. Rewrite using `[h, e1, e2]`. Apply the tactic sequence `split_ifs <;> abel`.
-/
private theorem kF_gl {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    {E1 E2 : Fin n → Fin n → Module.End ℂ V} (hP : IsPair E1 E2) : GlRel (kF E1 E2) := by
  intro a b c d
  have e1 := hP.gl1 a b c d
  have e2 := hP.gl2 a b c d
  have h : (E1 a b + E2 a b) * (E1 c d + E2 c d) - (E1 c d + E2 c d) * (E1 a b + E2 a b) =
      (E1 a b * E1 c d - E1 c d * E1 a b) + (E2 a b * E2 c d - E2 c d * E2 a b) := by
    simp only [add_mul, mul_add]
    rw [hP.comm a b c d, hP.comm c d a b]
    abel
  simp only [kF]
  rw [h, e1, e2]
  split_ifs <;> abel

/- English proof (translation)
Rewrite using `[gelf2]`. Establish `: ∀ a, infOf lam s a ^ 2 = ((((lam a : ℝ) + rhoV n a) ^ 2 : ℝ) : ℂ)`. Introduce `a`. Apply the tactic sequence `cases s <;> simp [infOf, rhoV] <;> ring`. Simplify using `only [this, nsq]`.

Use `push_cast`. Both sides reduce to the same expression.
-/
private theorem gel_val {n : ℕ} (lam : Fin n → ℤ) (s : Bool) :
    GlobalTheory.Dec.gelfVal (infOf lam s) 2 =
      (((nsq fun a => (lam a : ℝ) + rhoV n a) - nsq (rhoV n) : ℝ) : ℂ) := by
  rw [gelf2]
  have : ∀ a, infOf lam s a ^ 2 = ((((lam a : ℝ) + rhoV n a) ^ 2 : ℝ) : ℂ) := by
    intro a
    cases s <;> simp [infOf, rhoV] <;> ring
  simp only [this, nsq]
  push_cast
  rfl

/- English proof (translation)
Simplify using `only [LSq, nsq, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun a _ => by ring`.
-/
private theorem lsq_eq {n : ℕ} (lam : Fin n → ℤ) :
    LSq lam = 4 * nsq fun a => (lam a : ℝ) + rhoV n a := by
  simp only [LSq, nsq, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/- English proof (translation)
Introduce `n lam V _ _ E1 E2 hP _ h1 h2 J _ _ c η hC κ hκ`. Take `⟨x, hx, hx0⟩` from `(Submodule.ne_bot_iff _).1 hκ`. Establish `hx' : KHighest (fun _ => true) (dg (kF E1 E2) c) κ x` using `hx`. Take `⟨⟨φ, hφ⟩, hcomm, hmadj, hladj, hUF⟩` from `tenF n V J`. Establish `hUFd : UF (dg (kF E1 E2) c)` using `hUF _ c η ⟨kF_gl hP, hP.unitK⟩ hC`.

Set `lfJ : Module.End ℂ V →ₐ[ℂ] Module.End ℂ (Ten J V)` to `lf J`. Set `L1 : Fin n → Fin n → Module.End ℂ (Ten J V)` to `fun a b => lfJ (E1 a b)`. Set `L2 : Fin n → Fin n → Module.End ℂ (Ten J V)` to `fun a b => lfJ (E2 a b)`. Set `C : Fin n → Fin n → Module.End ℂ (Ten J V)` to `fun a b => φ (c a b)`. Establish `hD` using `diracAlg n (Module.End ℂ (Ten J V)) L1 L2 C (gl_map lfJ hP.gl1) (gl_map lfJ hP.gl2) (fun a b d e => by`.

Simplify using `only [L1, L2, ← map_mul]`. Rewrite using `[hP.comm a b d e])`. Use the proof step `(clif_map φ hC.rel)`. Use the proof step `(fun a b d e => by`. Simplify using `only [L1, L2, C, hφ]`.

Conclude with `⟨hcomm _ _, hcomm _ _⟩)`. Use `set T : Fin n → Fin n → Module.End ℂ (Ten J V) := fun a b => (L1 a b - L2 a b) * C b a with hTdef`. Use `set D : Module.End ℂ (Ten J V) := ∑ a, ∑ b, T a b with hDdef`. Establish `hT : ∀ a b (y z : Ten J V), ⟪T a b y, z⟫_ℂ = -⟪y, T b a z⟫_ℂ`. Introduce `a b y z`.

Establish `hP' : L1 a b - L2 a b = lfJ (pF E1 E2 a b)` using `by simp [L1, L2, pF, map_sub]`. Establish `hP'' : L1 b a - L2 b a = lfJ (pF E1 E2 b a)` using `by simp [L1, L2, pF, map_sub]`. Establish `hneg : ∀ u w : V, ⟪pF E1 E2 a b u, w⟫_ℂ = ⟪u, (-(pF E1 E2 b a)) w⟫_ℂ`. Introduce `u w`. Rewrite using `[hP.unitP a b u w]`.

Simplify using `[inner_neg_right]`. Simplify using `only [hTdef, hP', hP'', Module.End.mul_apply, C, hφ]`. Rewrite using `[hladj _ _ hneg, hmadj, hC.adj b a, map_neg]`. Establish `hc` using `LinearMap.congr_fun (hcomm (c a b) (pF E1 E2 b a)) z`. Simplify using `only [Module.End.mul_apply] at hc`.

Rewrite using `[LinearMap.neg_apply, map_neg, inner_neg_right]`. Conclude with `congrArg (fun w => -⟪y, w⟫_ℂ) hc.symm`. Establish `hskew : ∀ y z : Ten J V, ⟪D y, z⟫_ℂ = -⟪y, D z⟫_ℂ`. Introduce `y z`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `[hDdef, LinearMap.sum_apply, sum_inner]`. Use `_ = ∑ a, ∑ b, -⟪y, T b a z⟫_ℂ := by simp_rw [hT]`. Use `_ = -⟪y, D z⟫_ℂ := by`. Rewrite using `[Finset.sum_comm]`. Simplify using `[hDdef, LinearMap.sum_apply, inner_sum, Finset.sum_neg_distrib]`.

Use `set A0 : ℝ := nsq fun a => (lam a : ℝ) + rhoV n a with hA0`. Use `set R : ℝ := nsq (rhoV n) with hR`. Use `set N : ℝ := nsq (κ + rhoV n) with hN`. Establish `g1 : GlobalTheory.Dec.gelfVal (infOf lam true) 2 = ((A0 - R : ℝ) : ℂ)` using `gel_val lam true`. Establish `g2 : GlobalTheory.Dec.gelfVal (infOf lam false) 2 = ((A0 - R : ℝ) : ℂ)` using `gel_val lam false`.

Establish `hc1 : Cas L1 = ((A0 - R : ℝ) : ℂ) • (1 : Module.End ℂ (Ten J V))`. Establish `: Cas E1 = ((A0 - R : ℝ) : ℂ) • (1 : Module.End ℂ V)`. Use extensionality with `v`. Rewrite using `[cas_gel, h1 2 v, g1]`. Simplify using the standard rewrite rules.

Rewrite using `[← cas_map lfJ, this, map_smul, map_one]`. Establish `hc2 : Cas L2 = ((A0 - R : ℝ) : ℂ) • (1 : Module.End ℂ (Ten J V))`. Establish `: Cas E2 = ((A0 - R : ℝ) : ℂ) • (1 : Module.End ℂ V)`. Use extensionality with `v`. Rewrite using `[cas_bar, h2 2 v, g2]`.

Simplify using the standard rewrite rules. Rewrite using `[← cas_map lfJ, this, map_smul, map_one]`. Establish `hspn : (fun a b => spn C a b) = fun a b => φ (spn c a b)`. Use function extensionality and compare the values at `a b`. Conclude with `(spn_map φ c a b).symm`.

Establish `hc3 : Cas (spn C) = ((3 * R : ℝ) : ℂ) • (1 : Module.End ℂ (Ten J V))`. Establish `e : Cas (spn C) = φ (Cas (spn c))`. Rewrite using `[cas_map φ]`. Conclude with `congrArg Cas hspn`. Rewrite using `[e, spnCas n J c η hC, map_smul, map_one]`.

Establish `hdg : (fun a b => L1 a b + L2 a b + spn C a b) = dg (kF E1 E2) c`. Use function extensionality and compare the values at `a b`. Establish `: spn C a b = mt V (spn c a b)` using `by rw [← hφ]; exact congrFun (congrFun hspn a) b`. Simplify using `only [dg, kF, L1, L2, lfJ, map_add, this]`. Establish `hc4 : Cas (dg (kF E1 E2) c) x = ((N - R : ℝ) : ℂ) • x`.

Establish `h` using `Formalism.REAL.kCasSpan (Ten J V) n (fun _ => true) (dg (kF E1 E2) c) κ x (Formalism.REAL.glRel_kRel _ _ hUFd.gl) hx' x (Submodule.mem_sInf.2 fun S hS => hS.1)`. Establish `hk : Formalism.REAL.CasK (fun _ : Fin n => true) (dg (kF E1 E2) c) = Cas (dg (kF E1 E2) c)`. Simplify using `[Formalism.REAL.CasK, Cas]`. Rewrite `h` using `[hk]`. Rewrite using `[h, Formalism.REAL.ckv, rhoC_true, nsq_eq, nsq_eq]`.

Establish `key : D (D x) + D (D x) = ((LSq lam - N : ℝ) : ℂ) • x`. Rewrite `hD` using `[hdg, hc1, hc2, hc3, two_mul, two_mul]`. Establish `h` using `LinearMap.congr_fun hD x`. Simplify using `only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hc4] at h`. Establish `h' : D (D x) + D (D x) = _` using `h`.

Rewrite using `[h', lsq_eq, ← sub_eq_zero]`. Simplify using `only [← add_smul, ← sub_smul]`. Rewrite using `[← hA0]`. Use `zero_smul ℂ x using 2` and compare the differences between its conclusion and the goal. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `e : ⟪x, D (D x)⟫_ℂ = -(((‖D x‖ ^ 2 : ℝ)) : ℂ)`. Establish `h` using `hskew x (D x)`. Rewrite `h` using `[inner_self_eq_norm_sq_to_K]`. Rewrite `h`, the goal using `[eq_neg_iff_add_eq_zero]`.

Rewrite using `[← h]`. Use `push_cast`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish `h3` using `congrArg (fun w => ⟪x, w⟫_ℂ) key`.

Simplify using `only [inner_add_right, inner_smul_right, e, inner_self_eq_norm_sq_to_K] at h3`. Establish `h4 : -(2 * ‖D x‖ ^ 2) = (LSq lam - N) * ‖x‖ ^ 2`. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Use `push_cast`. Move the coercions through the operations in `at h3`.

Take the linear combination `h3`. Establish `hx2 : 0 < ‖x‖ ^ 2`. Use `norm_pos_iff.2 hx0` as an intermediate fact. Check the signs of the components of the expression. Assume the negation of the conclusion as `hlt`.

Establish `: 0 < LSq lam - N` using `sub_pos.2 (not_le.1 hlt)`. Use `mul_pos this hx2` as an intermediate fact. Use polynomial arithmetic with `[sq_nonneg ‖D x‖]`.
-/
theorem UpperTheory.RealTr.diracHW :
    ∀ (n : ℕ) (lam : Fin n → ℤ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
      IsPair E1 E2 → LocF (kF E1 E2) → (∀ m (x : V), gelA E1 m x = GlobalTheory.Dec.gelfVal (infOf lam true) m • x) →
      (∀ m (x : V), gelA (barF E2) m x = GlobalTheory.Dec.gelfVal (infOf lam false) m • x) → ∀ (J : Type) [Fintype J] [DecidableEq J] (c : Fin n → Fin n → Matrix J J ℂ) (η : J → Wt n), ClifMod c η → ∀ κ : Wt n, hw (dg (kF E1 E2) c) κ ≠ ⊥ → LSq lam ≤ nsq (κ + rhoV n) := by
  intro n lam V _ _ E1 E2 hP _ h1 h2 J _ _ c η hC κ hκ
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hκ
  have hx' : KHighest (fun _ => true) (dg (kF E1 E2) c) κ x := hx
  obtain ⟨⟨φ, hφ⟩, hcomm, hmadj, hladj, hUF⟩ := tenF n V J
  have hUFd : UF (dg (kF E1 E2) c) := hUF _ c η ⟨kF_gl hP, hP.unitK⟩ hC
  let lfJ : Module.End ℂ V →ₐ[ℂ] Module.End ℂ (Ten J V) := lf J
  let L1 : Fin n → Fin n → Module.End ℂ (Ten J V) := fun a b => lfJ (E1 a b)
  let L2 : Fin n → Fin n → Module.End ℂ (Ten J V) := fun a b => lfJ (E2 a b)
  let C : Fin n → Fin n → Module.End ℂ (Ten J V) := fun a b => φ (c a b)
  have hD := diracAlg n (Module.End ℂ (Ten J V)) L1 L2 C (gl_map lfJ hP.gl1) (gl_map lfJ hP.gl2)
    (fun a b d e => by
      simp only [L1, L2, ← map_mul]
      rw [hP.comm a b d e])
    (clif_map φ hC.rel)
    (fun a b d e => by
      simp only [L1, L2, C, hφ]
      exact ⟨hcomm _ _, hcomm _ _⟩)
  set T : Fin n → Fin n → Module.End ℂ (Ten J V) := fun a b => (L1 a b - L2 a b) * C b a with hTdef
  set D : Module.End ℂ (Ten J V) := ∑ a, ∑ b, T a b with hDdef
  have hT : ∀ a b (y z : Ten J V), ⟪T a b y, z⟫_ℂ = -⟪y, T b a z⟫_ℂ := by
    intro a b y z
    have hP' : L1 a b - L2 a b = lfJ (pF E1 E2 a b) := by simp [L1, L2, pF, map_sub]
    have hP'' : L1 b a - L2 b a = lfJ (pF E1 E2 b a) := by simp [L1, L2, pF, map_sub]
    have hneg : ∀ u w : V, ⟪pF E1 E2 a b u, w⟫_ℂ = ⟪u, (-(pF E1 E2 b a)) w⟫_ℂ := by
      intro u w
      rw [hP.unitP a b u w]
      simp [inner_neg_right]
    simp only [hTdef, hP', hP'', Module.End.mul_apply, C, hφ]
    rw [hladj _ _ hneg, hmadj, hC.adj b a, map_neg]
    have hc := LinearMap.congr_fun (hcomm (c a b) (pF E1 E2 b a)) z
    simp only [Module.End.mul_apply] at hc
    rw [LinearMap.neg_apply, map_neg, inner_neg_right]
    exact congrArg (fun w => -⟪y, w⟫_ℂ) hc.symm
  have hskew : ∀ y z : Ten J V, ⟪D y, z⟫_ℂ = -⟪y, D z⟫_ℂ := by
    intro y z
    calc ⟪D y, z⟫_ℂ = ∑ a, ∑ b, ⟪T a b y, z⟫_ℂ := by
          simp [hDdef, LinearMap.sum_apply, sum_inner]
      _ = ∑ a, ∑ b, -⟪y, T b a z⟫_ℂ := by simp_rw [hT]
      _ = -⟪y, D z⟫_ℂ := by
          rw [Finset.sum_comm]
          simp [hDdef, LinearMap.sum_apply, inner_sum, Finset.sum_neg_distrib]
  set A0 : ℝ := nsq fun a => (lam a : ℝ) + rhoV n a with hA0
  set R : ℝ := nsq (rhoV n) with hR
  set N : ℝ := nsq (κ + rhoV n) with hN
  have g1 : GlobalTheory.Dec.gelfVal (infOf lam true) 2 = ((A0 - R : ℝ) : ℂ) := gel_val lam true
  have g2 : GlobalTheory.Dec.gelfVal (infOf lam false) 2 = ((A0 - R : ℝ) : ℂ) := gel_val lam false
  have hc1 : Cas L1 = ((A0 - R : ℝ) : ℂ) • (1 : Module.End ℂ (Ten J V)) := by
    have : Cas E1 = ((A0 - R : ℝ) : ℂ) • (1 : Module.End ℂ V) := by
      ext v
      rw [cas_gel, h1 2 v, g1]
      simp
    rw [← cas_map lfJ, this, map_smul, map_one]
  have hc2 : Cas L2 = ((A0 - R : ℝ) : ℂ) • (1 : Module.End ℂ (Ten J V)) := by
    have : Cas E2 = ((A0 - R : ℝ) : ℂ) • (1 : Module.End ℂ V) := by
      ext v
      rw [cas_bar, h2 2 v, g2]
      simp
    rw [← cas_map lfJ, this, map_smul, map_one]
  have hspn : (fun a b => spn C a b) = fun a b => φ (spn c a b) := by
    funext a b
    exact (spn_map φ c a b).symm
  have hc3 : Cas (spn C) = ((3 * R : ℝ) : ℂ) • (1 : Module.End ℂ (Ten J V)) := by
    have e : Cas (spn C) = φ (Cas (spn c)) := by
      rw [cas_map φ]
      exact congrArg Cas hspn
    rw [e, spnCas n J c η hC, map_smul, map_one]
  have hdg : (fun a b => L1 a b + L2 a b + spn C a b) = dg (kF E1 E2) c := by
    funext a b
    have : spn C a b = mt V (spn c a b) := by rw [← hφ]; exact congrFun (congrFun hspn a) b
    simp only [dg, kF, L1, L2, lfJ, map_add, this]
  have hc4 : Cas (dg (kF E1 E2) c) x = ((N - R : ℝ) : ℂ) • x := by
    have h := Formalism.REAL.kCasSpan (Ten J V) n (fun _ => true) (dg (kF E1 E2) c) κ x
      (Formalism.REAL.glRel_kRel _ _ hUFd.gl) hx' x
      (Submodule.mem_sInf.2 fun S hS => hS.1)
    have hk : Formalism.REAL.CasK (fun _ : Fin n => true) (dg (kF E1 E2) c) = Cas (dg (kF E1 E2) c) := by
      simp [Formalism.REAL.CasK, Cas]
    rw [hk] at h
    rw [h, Formalism.REAL.ckv, rhoC_true, nsq_eq, nsq_eq]
  have key : D (D x) + D (D x) = ((LSq lam - N : ℝ) : ℂ) • x := by
    rw [hdg, hc1, hc2, hc3, two_mul, two_mul] at hD
    have h := LinearMap.congr_fun hD x
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, hc4] at h
    have h' : D (D x) + D (D x) = _ := h
    rw [h', lsq_eq, ← sub_eq_zero]
    simp only [← add_smul, ← sub_smul]
    rw [← hA0]
    convert zero_smul ℂ x using 2
    push_cast
    ring
  have e : ⟪x, D (D x)⟫_ℂ = -(((‖D x‖ ^ 2 : ℝ)) : ℂ) := by
    have h := hskew x (D x)
    rw [inner_self_eq_norm_sq_to_K] at h
    rw [eq_neg_iff_add_eq_zero] at h ⊢
    rw [← h]
    push_cast
    simp
    ring
  have h3 := congrArg (fun w => ⟪x, w⟫_ℂ) key
  simp only [inner_add_right, inner_smul_right, e, inner_self_eq_norm_sq_to_K] at h3
  have h4 : -(2 * ‖D x‖ ^ 2) = (LSq lam - N) * ‖x‖ ^ 2 := by
    apply Complex.ofReal_injective
    push_cast
    push_cast at h3
    linear_combination h3
  have hx2 : 0 < ‖x‖ ^ 2 := by
    have := norm_pos_iff.2 hx0
    positivity
  by_contra hlt
  have : 0 < LSq lam - N := sub_pos.2 (not_le.1 hlt)
  have := mul_pos this hx2
  nlinarith [sq_nonneg ‖D x‖]
