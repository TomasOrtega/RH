import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpinGlRelationsAdjointStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LoweringWordsSpanStatement

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexOrder
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

namespace GlobalTheory.CompanionTheory.RealCount.SpinMap

variable {n : ℕ}

def tw {A : Type*} [Ring A] (E : Fin n → Fin n → A) : Fin n → Fin n → A := fun x y => - E y x

/- English proof (translation)
Introduce `a b c d`. Use `h b a d c` as an intermediate fact. Simplify using `only [tw, neg_mul_neg]`. Rewrite using `[this]`. Simplify using `only [eq_comm (a := a) (b := d), eq_comm (a := c) (b := b)]`.

Apply the tactic sequence `split_ifs <;> abel`.
-/
theorem tw_rel {A : Type*} [Ring A] {E : Fin n → Fin n → A} (h : Formalism.REAL.GlRel E) :
    Formalism.REAL.GlRel (tw E) := by
  intro a b c d
  have := h b a d c
  simp only [tw, neg_mul_neg]
  rw [this]
  simp only [eq_comm (a := a) (b := d), eq_comm (a := c) (b := b)]
  split_ifs <;> abel

def wd {A : Type*} [Ring A] (T : Fin n → Fin n → A) (l : List (Fin n × Fin n)) : A :=
  (l.map fun p => T p.1 p.2).prod

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem wd_nil {A : Type*} [Ring A] (T : Fin n → Fin n → A) : wd T [] = 1 := rfl

/- English proof (translation)
Simplify using `[wd]`.
-/
@[simp] theorem wd_cons {A : Type*} [Ring A] (T : Fin n → Fin n → A) (p : Fin n × Fin n)
    (l : List (Fin n × Fin n)) : wd T (p :: l) = T p.1 p.2 * wd T l := by
  simp [wd]

abbrev Lw (n : ℕ) : Type := {l : List (Fin n × Fin n) // ∀ p ∈ l, p.2 < p.1}

section Span

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def lowL (T : Fin n → Fin n → Module.End ℂ V) (q : V) : (Lw n →₀ ℂ) →ₗ[ℂ] V :=
  Finsupp.linearCombination ℂ (fun l : Lw n => wd T l.1 q)

/- English proof (translation)
Simplify using `[lowL]`.
-/
theorem lowL_single (T : Fin n → Fin n → Module.End ℂ V) (q : V) (l : Lw n) (b : ℂ) :
    lowL T q (Finsupp.single l b) = b • wd T l.1 q := by
  simp [lowL]

/- English proof (translation)
Assemble the required witnesses or components as `⟨Finsupp.single ⟨l, hl⟩ 1, by simp [lowL_single]⟩`.
-/
theorem word_mem (T : Fin n → Fin n → Module.End ℂ V) (q : V) (l : List (Fin n × Fin n))
    (hl : ∀ p ∈ l, p.2 < p.1) : wd T l q ∈ LinearMap.range (lowL T q) :=
  ⟨Finsupp.single ⟨l, hl⟩ 1, by simp [lowL_single]⟩

/- English proof (translation)
Introduce and unpack `_ ⟨c, rfl⟩`. Proceed by induction on `c using Finsupp.induction_linear with`. Consider the case `zero => simp`. Consider the case `add f g hf hg => rw [map_add]`. Conclude with `M.add_mem hf hg`.

Consider the case `single l b => rw [lowL_single]`. Conclude with `M.smul_mem _ (h l)`.
-/
theorem range_le (T : Fin n → Fin n → Module.End ℂ V) (q : V) (M : Submodule ℂ V)
    (h : ∀ l : Lw n, wd T l.1 q ∈ M) : LinearMap.range (lowL T q) ≤ M := by
  rintro _ ⟨c, rfl⟩
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add]; exact M.add_mem hf hg
  | single l b => rw [lowL_single]; exact M.smul_mem _ (h l)

/- English proof (translation)
Establish `: LinearMap.range (lowL T q) ≤ (LinearMap.range (lowL T q)).comap (T x y)`. Use `range_le T q _ fun l => ?_` and prove the remaining obligations. Rewrite using `[Submodule.mem_comap]`. Use `word_mem T q ((x, y) :: l.1) (by` as an intermediate fact. Introduce `p hp`.

Break down `List.mem_cons.1 hp with rfl | hp` into its components or cases. Conclude with `hxy`. Conclude with `l.2 p hp)`. Simplify using `using this`. Conclude with `this hr`.
-/
theorem low_stable (T : Fin n → Fin n → Module.End ℂ V) (q : V) {x y : Fin n} (hxy : y < x) {r : V}
    (hr : r ∈ LinearMap.range (lowL T q)) : T x y r ∈ LinearMap.range (lowL T q) := by
  have : LinearMap.range (lowL T q) ≤ (LinearMap.range (lowL T q)).comap (T x y) := by
    refine range_le T q _ fun l => ?_
    rw [Submodule.mem_comap]
    have := word_mem T q ((x, y) :: l.1) (by
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact hxy
      · exact l.2 p hp)
    simpa using this
  exact this hr

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil`. Introduce `a b`. Establish `h1 : q ∈ LinearMap.range (lowL (tw S) q)`. Simplify using `using word_mem (tw S) q [] (by simp)`.

Simplify using `only [wd_nil, Module.End.one_apply]`. Break down `lt_trichotomy a b with h | h | h` into its components or cases. Establish `: S a b q = - (tw S b a q)` using `by simp [tw]`. Rewrite using `[this]`. Conclude with `Submodule.neg_mem _ (low_stable _ q h h1)`.

Substitute `h` using the available equality. Take `⟨m, hm⟩` from `hd a`. Rewrite using `[hm]`. Conclude with `Submodule.smul_mem _ _ h1`. Rewrite using `[hl b a h]`.

Conclude with `Submodule.zero_mem _`. Consider the case `cons p l ih`. Take `⟨x, y⟩` from `p`. Introduce `a b`. Establish `hyx : y < x` using `hw (x, y) (by simp)`.

Establish `ih'` using `ih (fun p hp => hw p (List.mem_cons_of_mem _ hp))`. Use `set w := wd (tw S) l q with hwdef`. Establish `hcomm` using `congrArg (fun f : Module.End ℂ V => f w) (hS a b y x)`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply] at hcomm`. Establish `hval : S a b (wd (tw S) ((x, y) :: l) q) = tw S x y (S a b w) - ((if b = y then S a x else 0) w - (if x = a then S y b else 0) w)`.

Simplify using `only [wd_cons, Module.End.mul_apply, ← hwdef, tw, map_neg, LinearMap.neg_apply]`. Rewrite using `[← hcomm]`. Normalize the expressions using the abelian group laws. Rewrite using `[hval]`. Use `Submodule.sub_mem _ (low_stable _ q hyx (ih' a b)) (Submodule.sub_mem _ ?_ ?_)` and prove the remaining obligations.

Use `split_ifs`. Conclude with `ih' _ _`. Simplify using the standard rewrite rules. Use `split_ifs`. Conclude with `ih' _ _`.

Simplify using the standard rewrite rules.
-/
theorem stable_word {S : Fin n → Fin n → Module.End ℂ V} (hS : Formalism.REAL.GlRel S) (q : V)
    (hd : ∀ a, ∃ m : ℂ, S a a q = m • q) (hl : ∀ a b, a < b → S b a q = 0)
    (l : List (Fin n × Fin n)) (hw : ∀ p ∈ l, p.2 < p.1) :
    ∀ a b, S a b (wd (tw S) l q) ∈ LinearMap.range (lowL (tw S) q) := by
  induction l with
  | nil =>
    intro a b
    have h1 : q ∈ LinearMap.range (lowL (tw S) q) := by
      simpa using word_mem (tw S) q [] (by simp)
    simp only [wd_nil, Module.End.one_apply]
    rcases lt_trichotomy a b with h | h | h
    · have : S a b q = - (tw S b a q) := by simp [tw]
      rw [this]
      exact Submodule.neg_mem _ (low_stable _ q h h1)
    · subst h
      obtain ⟨m, hm⟩ := hd a
      rw [hm]
      exact Submodule.smul_mem _ _ h1
    · rw [hl b a h]; exact Submodule.zero_mem _
  | cons p l ih =>
    obtain ⟨x, y⟩ := p
    intro a b
    have hyx : y < x := hw (x, y) (by simp)
    have ih' := ih (fun p hp => hw p (List.mem_cons_of_mem _ hp))
    set w := wd (tw S) l q with hwdef
    have hcomm := congrArg (fun f : Module.End ℂ V => f w) (hS a b y x)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at hcomm
    have hval : S a b (wd (tw S) ((x, y) :: l) q) =
        tw S x y (S a b w) - ((if b = y then S a x else 0) w - (if x = a then S y b else 0) w) := by
      simp only [wd_cons, Module.End.mul_apply, ← hwdef, tw, map_neg, LinearMap.neg_apply]
      rw [← hcomm]; abel
    rw [hval]
    refine Submodule.sub_mem _ (low_stable _ q hyx (ih' a b)) (Submodule.sub_mem _ ?_ ?_)
    · split_ifs
      · exact ih' _ _
      · simp
    · split_ifs
      · exact ih' _ _
      · simp

/- English proof (translation)
Establish `: LinearMap.range (lowL (tw S) q) ≤ (LinearMap.range (lowL (tw S) q)).comap (S a b)` using `range_le _ q _ fun l => stable_word hS q hd hl l.1 l.2 a b`. Conclude with `this hr`.
-/
theorem stable_all {S : Fin n → Fin n → Module.End ℂ V} (hS : Formalism.REAL.GlRel S) (q : V)
    (hd : ∀ a, ∃ m : ℂ, S a a q = m • q) (hl : ∀ a b, a < b → S b a q = 0) (a b : Fin n) {r : V}
    (hr : r ∈ LinearMap.range (lowL (tw S) q)) : S a b r ∈ LinearMap.range (lowL (tw S) q) := by
  have : LinearMap.range (lowL (tw S) q) ≤ (LinearMap.range (lowL (tw S) q)).comap (S a b) :=
    range_le _ q _ fun l => stable_word hS q hd hl l.1 l.2 a b
  exact this hr

/- English proof (translation)
Establish `hc` using `congrArg (fun f : Module.End ℂ V => f w) (h a a y x)`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, hw, map_smul] at hc`. Establish `hc' : T a a (T y x w) = m • T y x w + ((if a = y then T a x else 0) w - (if x = a then T y a else 0) w)`. Rewrite using `[← hc]`. Normalize the expressions using the abelian group laws.

Rewrite using `[hc']`. Apply the tactic sequence `by_cases h1 : a = y <;> by_cases h2 : x = a`. Substitute `h1` using the available equality. Substitute `h2` using the available equality. Simplify using the standard rewrite rules.

Substitute `h1` using the available equality. Simplify using `[h2, add_smul]`. Substitute `h2` using the available equality. Simplify using `[h1, add_smul, sub_eq_add_neg]`. Simplify using `[h1, h2]`.
-/
theorem eig_step {T : Fin n → Fin n → Module.End ℂ V} (h : Formalism.REAL.GlRel T) (a x y : Fin n) (w : V)
    (m : ℂ) (hw : T a a w = m • w) :
    T a a (T y x w) = (m + ((if a = y then 1 else 0) - (if x = a then 1 else 0))) • T y x w := by
  have hc := congrArg (fun f : Module.End ℂ V => f w) (h a a y x)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hw, map_smul] at hc
  have hc' : T a a (T y x w) = m • T y x w +
      ((if a = y then T a x else 0) w - (if x = a then T y a else 0) w) := by
    rw [← hc]; abel
  rw [hc']
  by_cases h1 : a = y <;> by_cases h2 : x = a
  · subst h1; subst h2; simp
  · subst h1; simp [h2, add_smul]
  · subst h2; simp [h1, add_smul, sub_eq_add_neg]
  · simp [h1, h2]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => exact ⟨μ, fun a => by simpa using ⟨hq a, hz a⟩⟩`. Consider the case `cons p l ih`. Take `⟨x, y⟩` from `p`. Take `⟨m, hm⟩` from `ih`.

Use `⟨fun a => m a + ((if a = y then 1 else 0) - (if x = a then 1 else 0)), fun a => ?_⟩` and prove the remaining obligations. Establish `h1` using `eig_step hS a x y _ _ (hm a).1`. Establish `h2` using `eig_step hE a x y _ _ (hm a).2`. Simplify using `only [wd_cons, Module.End.mul_apply, tw, LinearMap.neg_apply, map_neg]`. Rewrite using `[h1, h2]`.

Prove the components needed by the constructor for the conclusion. Simplify using the standard rewrite rules. Simplify using `only [smul_neg]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem diag_word {Z : Type} [AddCommGroup Z] [Module ℂ Z] {S : Fin n → Fin n → Module.End ℂ V}
    {E : Fin n → Fin n → Module.End ℂ Z} (hS : Formalism.REAL.GlRel S) (hE : Formalism.REAL.GlRel E) (q : V) (z : Z)
    (μ ν : Fin n → ℂ) (hq : ∀ a, S a a q = μ a • q) (hz : ∀ a, E a a z = (μ a + ν a) • z)
    (l : List (Fin n × Fin n)) :
    ∃ m : Fin n → ℂ, ∀ a, S a a (wd (tw S) l q) = m a • wd (tw S) l q ∧
      E a a (wd (tw E) l z) = (m a + ν a) • wd (tw E) l z := by
  induction l with
  | nil => exact ⟨μ, fun a => by simpa using ⟨hq a, hz a⟩⟩
  | cons p l ih =>
    obtain ⟨x, y⟩ := p
    obtain ⟨m, hm⟩ := ih
    refine ⟨fun a => m a + ((if a = y then 1 else 0) - (if x = a then 1 else 0)), fun a => ?_⟩
    have h1 := eig_step hS a x y _ _ (hm a).1
    have h2 := eig_step hE a x y _ _ (hm a).2
    simp only [wd_cons, Module.End.mul_apply, tw, LinearMap.neg_apply, map_neg]
    rw [h1, h2]
    constructor
    · simp
    · simp only [smul_neg]
      congr 2
      ring

/- English proof (translation)
Set `φ₀ : LinearMap.range L →ₗ[ℂ] Z` to `((LinearMap.ker L).liftQ L' h) ∘ₗ (L.quotKerEquivRange.symm : LinearMap.range L →ₗ[ℂ] _)`. Use `⟨φ₀ ∘ₗ Submodule.linearProjOfIsCompl _ _ hc, fun d => ?_, fun k hk => ?_⟩` and prove the remaining obligations. Establish `: Submodule.linearProjOfIsCompl _ _ hc (L d) = ⟨L d, LinearMap.mem_range_self L d⟩` using `Submodule.linearProjOfIsCompl_apply_left hc ⟨L d, LinearMap.mem_range_self L d⟩`. Simplify using `only [LinearMap.comp_apply, this, φ₀]`. Use `erw [LinearMap.quotKerEquivRange_symm_apply_image L d (LinearMap.mem_range_self L d)]`.

Simplify using the standard rewrite rules. Establish `h0 : Submodule.linearProjOfIsCompl _ _ hc k = 0` using `Submodule.linearProjOfIsCompl_apply_right' hc hk`. Rewrite using `[LinearMap.comp_apply, h0, map_zero]`.
-/
theorem exists_factor {D Z : Type*} [AddCommGroup D] [Module ℂ D] [AddCommGroup Z] [Module ℂ Z]
    (L : D →ₗ[ℂ] V) (L' : D →ₗ[ℂ] Z) (h : LinearMap.ker L ≤ LinearMap.ker L') (Q : Submodule ℂ V)
    (hc : IsCompl (LinearMap.range L) Q) :
    ∃ φ : V →ₗ[ℂ] Z, (∀ d, φ (L d) = L' d) ∧ ∀ k ∈ Q, φ k = 0 := by
  let φ₀ : LinearMap.range L →ₗ[ℂ] Z :=
    ((LinearMap.ker L).liftQ L' h) ∘ₗ (L.quotKerEquivRange.symm : LinearMap.range L →ₗ[ℂ] _)
  refine ⟨φ₀ ∘ₗ Submodule.linearProjOfIsCompl _ _ hc, fun d => ?_, fun k hk => ?_⟩
  · have : Submodule.linearProjOfIsCompl _ _ hc (L d) = ⟨L d, LinearMap.mem_range_self L d⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hc ⟨L d, LinearMap.mem_range_self L d⟩
    simp only [LinearMap.comp_apply, this, φ₀]
    erw [LinearMap.quotKerEquivRange_symm_apply_image L d (LinearMap.mem_range_self L d)]
    simp
  · have h0 : Submodule.linearProjOfIsCompl _ _ hc k = 0 := Submodule.linearProjOfIsCompl_apply_right' hc hk
    rw [LinearMap.comp_apply, h0, map_zero]

end Span

section Perp

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def perp (R : Submodule ℂ (ι → ℂ)) : Submodule ℂ (ι → ℂ) where
  carrier := {f | ∀ r ∈ R, star r ⬝ᵥ f = 0}
  add_mem' {x y} hx hy r hr := by rw [dotProduct_add, hx r hr, hy r hr, add_zero]
  zero_mem' r _ := by simp
  smul_mem' s x hx r hr := by rw [dotProduct_smul, hx r hr, smul_zero]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite using `[Submodule.disjoint_def]`. Introduce `x hx hx'`. Use `hx' x hx` as an intermediate fact. Conclude with `dotProduct_star_self_eq_zero.1 this`.

Rewrite using `[codisjoint_iff, eq_top_iff]`. Introduce `f _`. Set `e` to `WithLp.linearEquiv 2 ℂ (ι → ℂ)`. Set `K : Submodule ℂ (EuclideanSpace ℂ ι)` to `R.comap e.toLinearMap`. Take `⟨y, hy, w, hw, h⟩` from `Submodule.exists_add_mem_mem_orthogonal (K := K) (e.symm f)`.

Establish `hf : f = e y + e w` using `by rw [← map_add, ← h]; simp`. Rewrite using `[hf]`. Use `Submodule.add_mem_sup hy ?_` and prove the remaining obligations. Introduce `r hr`. Establish `hr' : e.symm r ∈ K` using `by simpa [K] using hr`.

Use `(Submodule.mem_orthogonal _ _).1 hw _ hr'` as an intermediate fact. Rewrite `this` using `[EuclideanSpace.inner_eq_star_dotProduct]`. Rewrite using `[dotProduct_comm]`. Simplify `this` using `[e]`.
-/
theorem isCompl_perp (R : Submodule ℂ (ι → ℂ)) : IsCompl R (perp R) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    have := hx' x hx
    exact dotProduct_star_self_eq_zero.1 this
  · rw [codisjoint_iff, eq_top_iff]
    intro f _
    let e := WithLp.linearEquiv 2 ℂ (ι → ℂ)
    let K : Submodule ℂ (EuclideanSpace ℂ ι) := R.comap e.toLinearMap
    obtain ⟨y, hy, w, hw, h⟩ := Submodule.exists_add_mem_mem_orthogonal (K := K) (e.symm f)
    have hf : f = e y + e w := by rw [← map_add, ← h]; simp
    rw [hf]
    refine Submodule.add_mem_sup hy ?_
    intro r hr
    have hr' : e.symm r ∈ K := by simpa [K] using hr
    have := (Submodule.mem_orthogonal _ _).1 hw _ hr'
    rw [EuclideanSpace.inner_eq_star_dotProduct] at this
    rw [dotProduct_comm]
    simpa [e] using this

/- English proof (translation)
Introduce `r hr`. Use `hk _ (h r hr)` as an intermediate fact. Rewrite `this` using `[star_mulVec, conjTranspose_conjTranspose, ← dotProduct_mulVec]`. Conclude with `this`.
-/
theorem perp_stable (M : Matrix ι ι ℂ) (R : Submodule ℂ (ι → ℂ)) (h : ∀ r ∈ R, Mᴴ *ᵥ r ∈ R)
    {k : ι → ℂ} (hk : k ∈ perp R) : M *ᵥ k ∈ perp R := by
  intro r hr
  have := hk _ (h r hr)
  rw [star_mulVec, conjTranspose_conjTranspose, ← dotProduct_mulVec] at this
  exact this

end Perp

/- English proof (translation)
Introduce `a b c d`. Use `congrArg f (h a b c d)` as an intermediate fact. Simplify using `only [map_sub, map_mul] at this`. Simplify using `only []`. Rewrite using `[this]`.

Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem glrel_map {A B F : Type*} [Ring A] [Ring B] [FunLike F A B] [RingHomClass F A B] (f : F)
    {E : Fin n → Fin n → A} (h : Formalism.REAL.GlRel E) : Formalism.REAL.GlRel (fun a b => f (E a b)) := by
  intro a b c d
  have := congrArg f (h a b c d)
  simp only [map_sub, map_mul] at this
  simp only []
  rw [this]
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[Finset.sum_map, Finsupp.sum]`. Conclude with `Finset.sum_congr rfl fun t _ => by simp [hcoef]`.
-/
theorem sum_lw {X : Type*} [AddCommGroup X] [Module ℂ X] (d : Lw n →₀ ℂ) (W : List (Fin n × Fin n) → X)
    (coef : List (Fin n × Fin n) → ℂ) (hcoef : ∀ t : Lw n, coef t.1 = d t) :
    ∑ l ∈ d.support.map (Function.Embedding.subtype _), coef l • W l = d.sum (fun t b => b • W t.1) := by
  rw [Finset.sum_map, Finsupp.sum]
  exact Finset.sum_congr rfl fun t _ => by simp [hcoef]

/- English proof (translation)
Introduce `n ι _ _ c hc q hq0 hqd hql Z _ _ E hE ν z hzd hz2`. Take `⟨hrel, hherm⟩` from `GlobalTheory.T.spin_gl_relations_adjoint c hc`. Set `S : Fin n → Fin n → Module.End ℂ (ι → ℂ)` to `fun a b => Matrix.toLinAlgEquiv' (spinM c a b)`. Establish `hSapp : ∀ a b f, S a b f = spinM c a b *ᵥ f` using `fun a b f => Matrix.toLinAlgEquiv'_apply _ _`. Establish `hS : Formalism.REAL.GlRel S` using `glrel_map (Matrix.toLinAlgEquiv' (R := ℂ) (n := ι)) hrel`.

Establish `hwS` using `tw_rel hS`. Establish `hwE` using `tw_rel hE`. Establish `hker : LinearMap.ker (lowL (tw S) q) ≤ LinearMap.ker (lowL (tw E) z)`. Introduce `d hd`. Rewrite `hd`, the goal using `[LinearMap.mem_ker]`.

Set `coef : List (Fin n × Fin n) → ℂ` to `fun l => if h : ∀ p ∈ l, p.2 < p.1 then d ⟨l, h⟩ else 0`. Establish `hcoef : ∀ t : Lw n, coef t.1 = d t` using `fun t => dif_pos t.2`. Establish `key` using `GlobalTheory.T.lowering_words_span (tw S) (tw E) hwS hwE q hq0 (fun a => by`. Simplify using `only [tw, LinearMap.neg_apply, hSapp, hqd a]`. Use `push_cast`.

Use the proof step `simp)`. Use the proof step `(fun a b hab => by simp only [tw, LinearMap.neg_apply, hSapp, hql a b hab, neg_zero]) z`. Use the proof step `(fun i j hij => by`. Establish `: tw E j i = - E i j` using `rfl`. Rewrite using `[this, neg_sq]`.

Conclude with `hz2 i j hij)`. Use the proof step `(d.support.map (Function.Embedding.subtype _)) coef`. Use the proof step `(by`. Introduce `l hl`. Take `⟨t, -, rfl⟩` from `Finset.mem_map.1 hl`.

Conclude with `t.2)`. Use the proof step `(by`. Use `sum_lw d (fun l => wd (tw S) l q) coef hcoef` as an intermediate fact. Rewrite `hd` using `[lowL, Finsupp.linearCombination_apply]`. Conclude with `this.trans hd)`.

Use `sum_lw d (fun l => wd (tw E) l z) coef hcoef` as an intermediate fact. Rewrite using `[lowL, Finsupp.linearCombination_apply]`. Conclude with `this.symm.trans key`. Establish `hcompl` using `isCompl_perp (LinearMap.range (lowL (tw S) q))`. Take `⟨φ, hφ1, hφ2⟩` from `exists_factor _ _ hker _ hcompl`.

Establish `hd' : ∀ a, ∃ m : ℂ, S a a q = m • q` using `fun a => ⟨_, by rw [hSapp]; exact hqd a⟩`. Establish `hl' : ∀ a b, a < b → S b a q = 0` using `fun a b hab => by rw [hSapp]; exact hql a b hab`. Establish `hQ : ∀ a b, ∀ k ∈ perp (LinearMap.range (lowL (tw S) q)), S a b k ∈ perp (LinearMap.range (lowL (tw S) q))`. Introduce `a b k hk`. Rewrite using `[hSapp]`.

Use `perp_stable _ _ (fun r hr => ?_) hk` and prove the remaining obligations. Rewrite using `[hherm, ← hSapp]`. Conclude with `stable_all hS q hd' hl' b a hr`. Establish `hword : ∀ l : Lw n, φ (wd (tw S) l.1 q) = wd (tw E) l.1 z` using `fun l => by`. Use `hφ1 (Finsupp.single l 1)` as an intermediate fact.

Simplify `this` using `[lowL_single]`. Establish `key : ∀ (A : Module.End ℂ (ι → ℂ)) (B : Module.End ℂ Z), (∀ l : Lw n, φ (A (wd (tw S) l.1 q)) = B (wd (tw E) l.1 z)) → (∀ k ∈ perp (LinearMap.range (lowL (tw S) q)), A k ∈ perp (LinearMap.range (lowL (tw S) q))) → ∀ f, φ (A f) = B (φ f)`. Introduce `A B h1 h2 f`. Establish `hf : f ∈ LinearMap.range (lowL (tw S) q) ⊔ perp (LinearMap.range (lowL (tw S) q))`. Rewrite using `[hcompl.sup_eq_top]`.

Discharge the goal by the elementary cases of `trivial`. Take `⟨_, ⟨d, rfl⟩, k, hk, rfl⟩` from `Submodule.mem_sup.1 hf`. Establish `hlin : φ ∘ₗ A ∘ₗ lowL (tw S) q = B ∘ₗ lowL (tw E) z`. Use `Finsupp.lhom_ext fun l b => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, lowL_single, map_smul, h1]`.

Use `LinearMap.congr_fun hlin d` as an intermediate fact. Simplify using `only [LinearMap.comp_apply] at this`. Rewrite using `[map_add, map_add, map_add, hφ2 _ (h2 k hk), hφ2 k hk, hφ1, this]`. Simplify using the standard rewrite rules. Use `⟨φ, ?_, ?_, ?_⟩` and prove the remaining obligations.

Simplify using `using hword ⟨[], by simp⟩`. Introduce `a b hab f`. Rewrite using `[← hSapp]`. Use `key (S a b) (E a b) (fun l => ?_) (hQ a b) f` and prove the remaining obligations. Establish `hlow : ∀ p ∈ (b, a) :: l.1, p.2 < p.1`.

Introduce `p hp`. Break down `List.mem_cons.1 hp with rfl | hp` into its components or cases. Conclude with `hab`. Conclude with `l.2 p hp`. Use `hword ⟨(b, a) :: l.1, hlow⟩` as an intermediate fact.

Simplify using `only [wd_cons, Module.End.mul_apply, tw, LinearMap.neg_apply, map_neg] at this`. Conclude with `neg_injective this`. Introduce `a f`. Rewrite using `[← hSapp]`. Use `key (S a a) (E a a - ((ν a : ℝ) : ℂ) • 1) (fun l => ?_) (hQ a a) f` as an intermediate fact.

Simplify using `using this`. Take `⟨m, hm⟩` from `diag_word hS hE q z (fun a => ((-(rhoV n a) : ℝ) : ℂ)) (fun a => ((ν a : ℝ) : ℂ)) (fun a => by rw [hSapp]; exact hqd a) (fun a => by rw [hzd]; congr 1; push_cast; ring) l.1`. Rewrite using `[(hm a).1, map_smul, hword l]`. Simplify using `[(hm a).2, add_smul]`.
-/
theorem exists_spin_map : ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (c : Fin n → Fin n → Matrix ι ι ℂ), IsCliff c →
    ∀ q : ι → ℂ, q ≠ 0 → (∀ a, spinM c a a *ᵥ q = ((-(rhoV n a) : ℝ) : ℂ) • q) →
    (∀ a b, a < b → spinM c b a *ᵥ q = 0) →
    ∀ {Z : Type} [AddCommGroup Z] [Module ℂ Z] (E : Fin n → Fin n → Module.End ℂ Z), Formalism.REAL.GlRel E →
    ∀ (ν : Fin n → ℝ) (z : Z), (∀ a, E a a z = ((ν a - rhoV n a : ℝ) : ℂ) • z) →
    (∀ i j : Fin n, (j : ℕ) = i + 1 → ((E i j) ^ 2) z = 0) →
    ∃ φ : (ι → ℂ) →ₗ[ℂ] Z, φ q = z ∧ (∀ a b, a < b → ∀ f, φ (spinM c a b *ᵥ f) = E a b (φ f)) ∧
      ∀ a f, φ (spinM c a a *ᵥ f) = E a a (φ f) - ((ν a : ℝ) : ℂ) • φ f := by
  classical
  intro n ι _ _ c hc q hq0 hqd hql Z _ _ E hE ν z hzd hz2
  obtain ⟨hrel, hherm⟩ := GlobalTheory.T.spin_gl_relations_adjoint c hc
  let S : Fin n → Fin n → Module.End ℂ (ι → ℂ) := fun a b => Matrix.toLinAlgEquiv' (spinM c a b)
  have hSapp : ∀ a b f, S a b f = spinM c a b *ᵥ f := fun a b f => Matrix.toLinAlgEquiv'_apply _ _
  have hS : Formalism.REAL.GlRel S := glrel_map (Matrix.toLinAlgEquiv' (R := ℂ) (n := ι)) hrel
  have hwS := tw_rel hS
  have hwE := tw_rel hE
  have hker : LinearMap.ker (lowL (tw S) q) ≤ LinearMap.ker (lowL (tw E) z) := by
    intro d hd
    rw [LinearMap.mem_ker] at hd ⊢
    let coef : List (Fin n × Fin n) → ℂ := fun l => if h : ∀ p ∈ l, p.2 < p.1 then d ⟨l, h⟩ else 0
    have hcoef : ∀ t : Lw n, coef t.1 = d t := fun t => dif_pos t.2
    have key := GlobalTheory.T.lowering_words_span (tw S) (tw E) hwS hwE q hq0
      (fun a => by
        simp only [tw, LinearMap.neg_apply, hSapp, hqd a]
        push_cast
        simp)
      (fun a b hab => by simp only [tw, LinearMap.neg_apply, hSapp, hql a b hab, neg_zero]) z
      (fun i j hij => by
        have : tw E j i = - E i j := rfl
        rw [this, neg_sq]
        exact hz2 i j hij)
      (d.support.map (Function.Embedding.subtype _)) coef
      (by
        intro l hl
        obtain ⟨t, -, rfl⟩ := Finset.mem_map.1 hl
        exact t.2)
      (by
        have := sum_lw d (fun l => wd (tw S) l q) coef hcoef
        rw [lowL, Finsupp.linearCombination_apply] at hd
        exact this.trans hd)
    have := sum_lw d (fun l => wd (tw E) l z) coef hcoef
    rw [lowL, Finsupp.linearCombination_apply]
    exact this.symm.trans key
  have hcompl := isCompl_perp (LinearMap.range (lowL (tw S) q))
  obtain ⟨φ, hφ1, hφ2⟩ := exists_factor _ _ hker _ hcompl
  have hd' : ∀ a, ∃ m : ℂ, S a a q = m • q := fun a => ⟨_, by rw [hSapp]; exact hqd a⟩
  have hl' : ∀ a b, a < b → S b a q = 0 := fun a b hab => by rw [hSapp]; exact hql a b hab
  have hQ : ∀ a b, ∀ k ∈ perp (LinearMap.range (lowL (tw S) q)),
      S a b k ∈ perp (LinearMap.range (lowL (tw S) q)) := by
    intro a b k hk
    rw [hSapp]
    refine perp_stable _ _ (fun r hr => ?_) hk
    rw [hherm, ← hSapp]
    exact stable_all hS q hd' hl' b a hr
  have hword : ∀ l : Lw n, φ (wd (tw S) l.1 q) = wd (tw E) l.1 z := fun l => by
    have := hφ1 (Finsupp.single l 1)
    simpa [lowL_single] using this
  have key : ∀ (A : Module.End ℂ (ι → ℂ)) (B : Module.End ℂ Z),
      (∀ l : Lw n, φ (A (wd (tw S) l.1 q)) = B (wd (tw E) l.1 z)) →
      (∀ k ∈ perp (LinearMap.range (lowL (tw S) q)), A k ∈ perp (LinearMap.range (lowL (tw S) q))) →
      ∀ f, φ (A f) = B (φ f) := by
    intro A B h1 h2 f
    have hf : f ∈ LinearMap.range (lowL (tw S) q) ⊔ perp (LinearMap.range (lowL (tw S) q)) := by
      rw [hcompl.sup_eq_top]; trivial
    obtain ⟨_, ⟨d, rfl⟩, k, hk, rfl⟩ := Submodule.mem_sup.1 hf
    have hlin : φ ∘ₗ A ∘ₗ lowL (tw S) q = B ∘ₗ lowL (tw E) z := by
      refine Finsupp.lhom_ext fun l b => ?_
      simp only [LinearMap.comp_apply, lowL_single, map_smul, h1]
    have := LinearMap.congr_fun hlin d
    simp only [LinearMap.comp_apply] at this
    rw [map_add, map_add, map_add, hφ2 _ (h2 k hk), hφ2 k hk, hφ1, this]
    simp
  refine ⟨φ, ?_, ?_, ?_⟩
  · simpa using hword ⟨[], by simp⟩
  · intro a b hab f
    rw [← hSapp]
    refine key (S a b) (E a b) (fun l => ?_) (hQ a b) f
    have hlow : ∀ p ∈ (b, a) :: l.1, p.2 < p.1 := by
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact hab
      · exact l.2 p hp
    have := hword ⟨(b, a) :: l.1, hlow⟩
    simp only [wd_cons, Module.End.mul_apply, tw, LinearMap.neg_apply, map_neg] at this
    exact neg_injective this
  · intro a f
    rw [← hSapp]
    have := key (S a a) (E a a - ((ν a : ℝ) : ℂ) • 1) (fun l => ?_) (hQ a a) f
    · simpa using this
    · obtain ⟨m, hm⟩ := diag_word hS hE q z (fun a => ((-(rhoV n a) : ℝ) : ℂ)) (fun a => ((ν a : ℝ) : ℂ))
        (fun a => by rw [hSapp]; exact hqd a)
        (fun a => by rw [hzd]; congr 1; push_cast; ring) l.1
      rw [(hm a).1, map_smul, hword l]
      simp [(hm a).2, add_smul]

end GlobalTheory.CompanionTheory.RealCount.SpinMap
