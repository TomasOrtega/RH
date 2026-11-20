import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerBasic

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Unitary

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

def layerWtVecs (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M)
    (k : ℕ) : Set M :=
  {w | ∃ ν ω : Fin n → ℝ, ∃ j ≤ k, IsNCSum ε j ω ∧
    (∃ v ∈ V, v ≠ 0 ∧ ∀ a, E a a v = (ν a : ℂ) • v) ∧ ∀ a, E a a w = ((ν + ω) a : ℂ) • w}

/- English proof (translation)
Take `⟨γ, hγ, rfl⟩` from `hω`. Use `⟨Fin.snoc (α := fun _ => Fin n × Fin n) γ (a, b), fun i => ?_, ?_⟩` and prove the remaining obligations. Use `Fin.lastCases ?_ (fun i => ?_) i` and prove the remaining obligations. Simplify using `using hab`. Simplify using `using hγ i`.

Rewrite using `[Fin.sum_univ_castSucc]`. Simplify using the standard rewrite rules.
-/
theorem isNCSum_add_root {j : ℕ} {ω : Fin n → ℝ} (hω : IsNCSum ε j ω) {a b : Fin n}
    (hab : ε a ≠ ε b) : IsNCSum ε (j + 1) (ω + root a b) := by
  obtain ⟨γ, hγ, rfl⟩ := hω
  refine ⟨Fin.snoc (α := fun _ => Fin n × Fin n) γ (a, b), fun i => ?_, ?_⟩
  · refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa using hab
    · simpa using hγ i
  · rw [Fin.sum_univ_castSucc]
    simp

/- English proof (translation)
Establish `h` using `congrArg (fun T : Module.End ℂ M => T w) (hE c c a b)`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply] at h`. Establish `h2 : E c c (E a b w) = E a b (E c c w) + ((if c = a then E c b else 0) w - (if b = c then E a c else 0) w)`. Rewrite using `[← h]`. Normalize the expressions using the abelian group laws.

Establish `e1 : (if c = a then E c b else 0) w = ((if c = a then 1 else 0 : ℝ) : ℂ) • E a b w`. Distinguish the cases in `h' : c = a`. Substitute `h'` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h']`.

Establish `e2 : (if b = c then E a c else 0) w = ((if c = b then 1 else 0 : ℝ) : ℂ) • E a b w`. Distinguish the cases in `h' : b = c`. Substitute `h'` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h', Ne.symm h']`.

Rewrite using `[h2, hw c, map_smul, e1, e2]`. Simplify using `only [root, Pi.add_apply, Pi.sub_apply, Pi.single_apply]`. Use `push_cast`. Use `module`.
-/
theorem diag_apply_of_weight (hE : IsGlRep E) {ω : Fin n → ℝ} {w : M}
    (hw : ∀ c, E c c w = (ω c : ℂ) • w) (a b c : Fin n) :
    E c c (E a b w) = ((ω + root a b) c : ℂ) • E a b w := by
  have h := congrArg (fun T : Module.End ℂ M => T w) (hE c c a b)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  have h2 : E c c (E a b w) = E a b (E c c w) +
      ((if c = a then E c b else 0) w - (if b = c then E a c else 0) w) := by
    rw [← h]
    abel
  have e1 : (if c = a then E c b else 0) w = ((if c = a then 1 else 0 : ℝ) : ℂ) • E a b w := by
    by_cases h' : c = a
    · subst h'
      simp
    · simp [h']
  have e2 : (if b = c then E a c else 0) w = ((if c = b then 1 else 0 : ℝ) : ℂ) • E a b w := by
    by_cases h' : b = c
    · subst h'
      simp
    · simp [h', Ne.symm h']
  rw [h2, hw c, map_smul, e1, e2]
  simp only [root, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  push_cast
  module

/- English proof (translation)
Use `haveI := hVf`. Establish `hst : ∀ a, ∀ v ∈ V, E a a v ∈ V` using `fun a v hv => hVK a a rfl v hv`. Set `T : Fin n → Module.End ℂ V` to `fun a => (E a a).restrict (hst a)`. Establish `hsym : ∀ a, (T a).IsSymmetric`. Introduce `a`.

Use `LinearMap.IsSymmetric.restrict_invariant (T := E a a) (fun x y => ?_) (hst a)` and prove the remaining obligations. Rewrite using `[hU a a x y]`. Simplify using `[adjSign]`. Establish `hcomm : Pairwise (Function.onFun Commute T)`. Introduce `a c _`.

Establish `h` using `hE a a c c`. Establish `hEc : E a a * E c c = E c c * E a a`. Rewrite using `[← sub_eq_zero, h]`. Distinguish the cases in `hac : a = c`. Substitute `hac` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[hac, Ne.symm hac]`. Use `show T a * T c = T c * T a`. Use `LinearMap.ext fun v => Subtype.ext ?_` and prove the remaining obligations. Use `show E a a (E c c v) = E c c (E a a v)`.

Conclude with `congrArg (fun F : Module.End ℂ M => F (v : M)) hEc`. Establish `htop` using `LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hsym hcomm`. Introduce `x hx`. Establish `hy : (⟨x, hx⟩ : V) ∈ ⨆ χ : Fin n → ℂ, ⨅ i, Module.End.eigenspace (T i) (χ i)`. Rewrite using `[htop]`.

Conclude with `Submodule.mem_top`. Use `show ((⟨x, hx⟩ : V) : M) ∈ _`. Use `Submodule.iSup_induction _ (motive := fun y : V => (y : M) ∈ Submodule.span ℂ _) hy ?_ ?_ ?_` and prove the remaining obligations. Introduce `χ y hy`. Rewrite `hy` using `[Submodule.mem_iInf]`.

Distinguish the cases in `hy0 : y = 0`. Substitute `hy0` using the available equality. Conclude with `Submodule.zero_mem _`. Establish `hreal : ∀ a, (((χ a).re : ℝ) : ℂ) = χ a`. Introduce `a`.

Establish `hev : Module.End.HasEigenvalue (T a) (χ a)` using `by first`. Consider the case `exact Module.End.hasEigenvalue_of_hasEigenvector ⟨hy a, hy0⟩`. Consider the case `exact (Submodule.ne_bot_iff _).2 ⟨y, hy a, hy0⟩`. Conclude with `Complex.conj_eq_iff_re.1 ((hsym a).conj_eigenvalue_eq_self hev)`. Use `Submodule.subset_span ⟨y.2, fun a => (χ a).re, fun a => ?_⟩` and prove the remaining obligations.

Establish `h` using `Module.End.mem_eigenspace_iff.1 (hy a)`. Establish `h'` using `congrArg Subtype.val h`. Simplify using `only [T, LinearMap.restrict_coe_apply, Submodule.coe_smul] at h'`. Rewrite using `[h', hreal a]`. Conclude with `Submodule.zero_mem _`.

Introduce `y z hy hz`. Simplify using `using Submodule.add_mem _ hy hz`.
-/
theorem le_span_weightVecs (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hVf : FiniteDimensional ℂ V)
    (hVK : IsKStableSub ε E V) :
    V ≤ Submodule.span ℂ {v | v ∈ V ∧ ∃ ν : Fin n → ℝ, ∀ a, E a a v = (ν a : ℂ) • v} := by
  haveI := hVf
  have hst : ∀ a, ∀ v ∈ V, E a a v ∈ V := fun a v hv => hVK a a rfl v hv
  let T : Fin n → Module.End ℂ V := fun a => (E a a).restrict (hst a)
  have hsym : ∀ a, (T a).IsSymmetric := by
    intro a
    refine LinearMap.IsSymmetric.restrict_invariant (T := E a a) (fun x y => ?_) (hst a)
    rw [hU a a x y]
    simp [adjSign]
  have hcomm : Pairwise (Function.onFun Commute T) := by
    intro a c _
    have h := hE a a c c
    have hEc : E a a * E c c = E c c * E a a := by
      rw [← sub_eq_zero, h]
      by_cases hac : a = c
      · subst hac
        simp
      · simp [hac, Ne.symm hac]
    show T a * T c = T c * T a
    refine LinearMap.ext fun v => Subtype.ext ?_
    show E a a (E c c v) = E c c (E a a v)
    exact congrArg (fun F : Module.End ℂ M => F (v : M)) hEc
  have htop := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hsym hcomm
  intro x hx
  have hy : (⟨x, hx⟩ : V) ∈ ⨆ χ : Fin n → ℂ, ⨅ i, Module.End.eigenspace (T i) (χ i) := by
    rw [htop]
    exact Submodule.mem_top
  show ((⟨x, hx⟩ : V) : M) ∈ _
  refine Submodule.iSup_induction _ (motive := fun y : V => (y : M) ∈ Submodule.span ℂ _) hy ?_ ?_ ?_
  · intro χ y hy
    rw [Submodule.mem_iInf] at hy
    by_cases hy0 : y = 0
    · subst hy0
      exact Submodule.zero_mem _
    · have hreal : ∀ a, (((χ a).re : ℝ) : ℂ) = χ a := by
        intro a
        have hev : Module.End.HasEigenvalue (T a) (χ a) := by
          first
            | exact Module.End.hasEigenvalue_of_hasEigenvector ⟨hy a, hy0⟩
            | exact (Submodule.ne_bot_iff _).2 ⟨y, hy a, hy0⟩
        exact Complex.conj_eq_iff_re.1 ((hsym a).conj_eigenvalue_eq_self hev)
      refine Submodule.subset_span ⟨y.2, fun a => (χ a).re, fun a => ?_⟩
      have h := Module.End.mem_eigenspace_iff.1 (hy a)
      have h' := congrArg Subtype.val h
      simp only [T, LinearMap.restrict_coe_apply, Submodule.coe_smul] at h'
      rw [h', hreal a]
  · exact Submodule.zero_mem _
  · intro y z hy hz
    simpa using Submodule.add_mem _ hy hz

/- English proof (translation)
Introduce and unpack `w ⟨ν, ω, j, hj, hω, hv, hw⟩`. Conclude with `⟨ν, ω, j, hj.trans h, hω, hv, hw⟩`.
-/
theorem layerWtVecs_mono {k l : ℕ} (h : k ≤ l) : layerWtVecs ε E V k ⊆ layerWtVecs ε E V l := by
  rintro w ⟨ν, ω, j, hj, hω, hv, hw⟩
  exact ⟨ν, ω, j, hj.trans h, hω, hv, hw⟩

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Use `(le_span_weightVecs hE hU hVf hVK).trans (Submodule.span_le.2 fun w hw => ?_)` and prove the remaining obligations. Take `⟨hwV, ν, hν⟩` from `hw`. Distinguish the cases in `hw0 : w = 0`.

Rewrite using `[hw0]`. Conclude with `Submodule.zero_mem _`. Conclude with `Submodule.subset_span ⟨ν, 0, 0, le_refl 0, ⟨Fin.elim0, fun i => Fin.elim0 i, by simp⟩, ⟨w, hwV, hw0, hν⟩, fun a => by simpa using hν a⟩`. Consider the case `succ k ih => show layer ε E V k ⊔ ⨆ (a : Fin n) (b : Fin n) (_ : ε a ≠ ε b), (layer ε E V k).map (E a b) ≤ _`. Use `sup_le (ih.trans (Submodule.span_mono (layerWtVecs_mono (Nat.le_succ k)))) (iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_)` and prove the remaining obligations.

Use `(Submodule.map_mono ih).trans ?_` and prove the remaining obligations. Rewrite using `[Submodule.map_span]`. Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨w, ⟨ν, ω, j, hj, hω, hv, hw⟩, rfl⟩`. Use `⟨ν, ω + root a b, j + 1, by omega, isNCSum_add_root hω hab, hv, fun c => ?_⟩` and prove the remaining obligations.

Rewrite using `[diag_apply_of_weight hE hw a b c, add_assoc]`.
-/
theorem layer_le_span (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hVf : FiniteDimensional ℂ V)
    (hVK : IsKStableSub ε E V) (k : ℕ) :
    layer ε E V k ≤ Submodule.span ℂ (layerWtVecs ε E V k) := by
  induction k with
  | zero =>
    refine (le_span_weightVecs hE hU hVf hVK).trans (Submodule.span_le.2 fun w hw => ?_)
    obtain ⟨hwV, ν, hν⟩ := hw
    by_cases hw0 : w = 0
    · rw [hw0]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨ν, 0, 0, le_refl 0, ⟨Fin.elim0, fun i => Fin.elim0 i, by simp⟩,
        ⟨w, hwV, hw0, hν⟩, fun a => by simpa using hν a⟩
  | succ k ih =>
    show layer ε E V k ⊔ ⨆ (a : Fin n) (b : Fin n) (_ : ε a ≠ ε b), (layer ε E V k).map (E a b) ≤ _
    refine sup_le (ih.trans (Submodule.span_mono (layerWtVecs_mono (Nat.le_succ k))))
      (iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_)
    refine (Submodule.map_mono ih).trans ?_
    rw [Submodule.map_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨w, ⟨ν, ω, j, hj, hω, hv, hw⟩, rfl⟩
    refine ⟨ν, ω + root a b, j + 1, by omega, isNCSum_add_root hω hab, hv, fun c => ?_⟩
    rw [diag_apply_of_weight hE hw a b c, add_assoc]

end Unitary

end ReciprocityTheory.ChartRestriction.DS
