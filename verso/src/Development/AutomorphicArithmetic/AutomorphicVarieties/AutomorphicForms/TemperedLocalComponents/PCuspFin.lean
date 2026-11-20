import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CuspSemisimpleReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.RepNewform
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalFiniteness.TypePoly
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CapCentral
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalFiniteness.ExistsZalgOfCenterU
open NumberField GlobalTheory.CuspRep UpperTheory.V

/- English proof (translation)
Establish `h1 : ∑ i, ∑ j, E j i * E j i = ∑ i, ∑ j, E i j * E i j` using `Finset.sum_comm`. Establish `h2 : ∑ i, ∑ j, E j i * E i j = ∑ i, ∑ j, E i j * E j i` using `Finset.sum_comm`. Simplify using `only [Formalism.REAL.Cas, sub_mul, mul_sub, Finset.sum_sub_distrib, h1, h2]`. Use `module`.
-/
private theorem sqId {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) :
    ∑ i, ∑ j, E i j * E i j = Formalism.REAL.Cas E + (1 / 2 : ℂ) • ∑ i, ∑ j, (E i j - E j i) * (E i j - E j i) := by
  have h1 : ∑ i, ∑ j, E j i * E j i = ∑ i, ∑ j, E i j * E i j := Finset.sum_comm
  have h2 : ∑ i, ∑ j, E j i * E i j = ∑ i, ∑ j, E i j * E j i := Finset.sum_comm
  simp only [Formalism.REAL.Cas, sub_mul, mul_sub, Finset.sum_sub_distrib, h1, h2]
  module

/- English proof (translation)
Establish `hp : ∀ (n : ℕ) (x : M), Ω x = ω • x → ((Ω + D - algebraMap ℂ _ ω) ^ n) x = (D ^ n) x`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro x _`. Both sides reduce to the same expression.

Consider the case `succ n ih`. Introduce `x hx`. Establish `e : (Ω + D - algebraMap ℂ _ ω) x = D x` using `by simp [hx]`. Rewrite using `[pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, e, ih]`. Rewrite using `[← Module.End.mul_apply, h.eq, Module.End.mul_apply, hx, map_smul]`.

Rewrite using `[Polynomial.aeval_comp, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range]`. Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, hp _ x hx]`.
-/
private theorem aevalShift {M : Type} [AddCommGroup M] [Module ℂ M] (Ω D : Module.End ℂ M) (h : Commute Ω D) (ω : ℂ)
    (q : Polynomial ℂ) (x : M) (hx : Ω x = ω • x) :
    Polynomial.aeval (Ω + D) (q.comp (Polynomial.X - Polynomial.C ω)) x = Polynomial.aeval D q x := by
  have hp : ∀ (n : ℕ) (x : M), Ω x = ω • x → ((Ω + D - algebraMap ℂ _ ω) ^ n) x = (D ^ n) x := by
    intro n
    induction n with
    | zero => intro x _; rfl
    | succ n ih =>
      intro x hx
      have e : (Ω + D - algebraMap ℂ _ ω) x = D x := by simp [hx]
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, e, ih]
      rw [← Module.End.mul_apply, h.eq, Module.End.mul_apply, hx, map_smul]
  rw [Polynomial.aeval_comp, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Polynomial.aeval_eq_sum_range,
    Polynomial.aeval_eq_sum_range]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, hp _ x hx]

/- English proof (translation)
Introduce `F _ _ _ a L hL W _ _ _ ρ _ c`. Take `⟨b, hb⟩` from `UpperTheory.V.Af.CuspFin.exists_stdBasis F a`. Establish `hbE : ∀ l, TR.lie F a (b l) = TR.Eop l.1 l.2.1 l.2.2` using `fun l => by rw [hb]; rfl`. Set `S : Subalgebra ℂ (Module.End ℂ (TR.Sm F a))` to `{ carrier := {z | ∃ t : ℂ, ∀ φ : TR.Sm F a, (∀ v u, TR.cap v u φ = c v u • φ) → z φ = t • φ} mul_mem' := by`. Introduce and unpack `x y ⟨s, hs⟩ ⟨t, ht⟩`.

Conclude with `⟨t * s, fun φ h => by rw [Module.End.mul_apply, ht φ h, map_smul, hs φ h, mul_smul]⟩`. Use the proof step `add_mem' := by`. Introduce and unpack `x y ⟨s, hs⟩ ⟨t, ht⟩`. Conclude with `⟨s + t, fun φ h => by rw [LinearMap.add_apply, ht φ h, hs φ h, add_smul]⟩`. Use the proof step `algebraMap_mem' := fun t => ⟨t, fun φ _ => rfl⟩ }`.

Establish `hq : ∀ (v : InfinitePlace F) u, Formalism.REAL.qdet (TR.Eop (a` using `a) v) u = TR.cap v (u - ((a : ℂ) - 1) / 2) := fun v u => by`. Rewrite using `[TR.cap, sub_add_cancel]`. Establish `hS : ∀ (v : InfinitePlace F) u, Formalism.REAL.qdet (TR.Eop (a` using `a) v) u ∈ S := fun v u => ⟨_, fun φ h => by rw [hq]; exact h v _⟩`. Establish `hZ : ∀ (v : InfinitePlace F) u, Formalism.REAL.qdet (TR.Eop (a` using `a) v) u ∈ TR.Zalg F a := fun v u => Algebra.subset_adjoin ⟨v, _, hq v u⟩`. Take `⟨ω, hω⟩ : ∑ v, Formalism.REAL.Cas (TR.Eop (E` from `F) (a := a) v) ∈ S := sum_mem fun v _ => UpperTheory.V.Af.CuspFin.casMem _ _ _ (TR.glRel_Eop v) S (hS v)`.

Establish `hΩ : ∑ v, Formalism.REAL.Cas (TR.Eop (E` using `F) (a := a) v) ∈ TR.Zalg F a := sum_mem fun v _ => UpperTheory.V.Af.CuspFin.casMem _ _ _ (TR.glRel_Eop v) _ (hZ v)`. Establish `hone : TR.oneL F a = ∑ v, ∑ i, b (v, i, i)`. Use function extensionality and compare the values at `i j w`. Simplify using `only [hb, Finset.sum_apply]`. Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.single_apply, Matrix.one_apply, Pi.single_apply, hij, ite_and, ite_apply]`.

Choose the witnesses or unpack the hypotheses as in `⟨t, ht⟩ : TR.lie F a (TR.oneL F a) ∈ S := by`. Rewrite using `[hone]`. Simplify using `only [map_sum, hbE]`. Conclude with `sum_mem fun v _ => GlobalTheory.CuspRep.Central.trace_mem _ (Subalgebra.toSubmodule S) (one_mem S) (hS v)`. Set `X : InfinitePlace F × Fin a × Fin a → TR.Lie F a` to `fun l => b l - b (l.1, l.2.2, l.2.1)`.

Establish `hX : ∀ l i j, X l j i = -X l i j`. Introduce and unpack `⟨v, p, q⟩ i j`. Simplify using `only [X, hb, Pi.sub_apply, neg_sub]`. Simplify using `[Matrix.single_apply, and_comm]`. Take `⟨q, hm, hd, hq0⟩` from `UpperTheory.V.Af.CuspFin.typePoly F a W ρ _ X hX (1 / 2)`.

Establish `hΔ : ∑ l, TR.lie F a (b l) * TR.lie F a (b l) = ∑ v, Formalism.REAL.Cas (TR.Eop (E` using `F) (a := a) v) + (1 / 2 : ℂ) • ∑ l, TR.lie F a (X l) * TR.lie F a (X l) := by`. Simplify using `only [X, map_sub, hbE, Fintype.sum_prod_type]`. Rewrite using `[Finset.smul_sum, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun v _ => sqId (TR.Eop v)`. Establish `hc : Commute (∑ v, Formalism.REAL.Cas (TR.Eop (E` using `F) (a := a) v)) ((1 / 2 : ℂ) • ∑ l, TR.lie F a (X l) * TR.lie F a (X l)) := (Commute.sum_right _ _ _ fun l _ => (TR.Cen.commute_Zalg_act hΩ (.lie (X l))).mul_right (TR.Cen.commute_Zalg_act hΩ (.lie (X l)))).smul_right _`.

Establish `hm' : (q.comp (Polynomial.X - Polynomial.C ω)).Monic` using `hm.comp (Polynomial.monic_X_sub_C ω) (by simp)`. Establish `hd' : 0 < (q.comp (Polynomial.X - Polynomial.C ω)).natDegree`. Rewrite using `[Polynomial.natDegree_comp]`. Simplify using `using hd`. Use `@Submodule.finiteDimensional_of_le _ _ _ _ _ _ _ (UpperTheory.V.Af.CuspFin.eigenFinite_of UpperTheory.V.Af.CuspFin.mem_cuspForms_of _ b _ hm' hd' t L hL) (Submodule.span_mono ?_)` and prove the remaining obligations.

Introduce and unpack `φ ⟨h1, h2, h3, h4⟩`. Conclude with `⟨h1, h2, by rw [hΔ, aevalShift _ _ hc ω q φ (hω φ h4), hq0 φ h3], ht φ h4⟩`.
-/
theorem UpperTheory.V.Af.cuspFormsFiniteReal :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (L : Subgroup (GL (Fin a) (Af F))), IsOpen (L : Set (GL (Fin a) (Af F))) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (TR.Kinf F a) W), GlobalTheory.Published.AutFin.IsContRep ρ → ∀ c : InfinitePlace F → ℂ → ℂ, FiniteDimensional ℂ (Submodule.span ℂ {φ : TR.Sm F a | TR.IsCuspForm φ ∧ (∀ k ∈ L, TR.finRep F a k φ = φ) ∧ (∀ g : GA F a, (fun k : TR.Kinf F a => (TR.cptRep F a k φ).1 g) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) ∧ ∀ v u, TR.cap v u φ = c v u • φ}) := by
  intro F _ _ _ a L hL W _ _ _ ρ _ c
  classical
  obtain ⟨b, hb⟩ := UpperTheory.V.Af.CuspFin.exists_stdBasis F a
  have hbE : ∀ l, TR.lie F a (b l) = TR.Eop l.1 l.2.1 l.2.2 := fun l => by rw [hb]; rfl
  let S : Subalgebra ℂ (Module.End ℂ (TR.Sm F a)) :=
    { carrier := {z | ∃ t : ℂ, ∀ φ : TR.Sm F a, (∀ v u, TR.cap v u φ = c v u • φ) → z φ = t • φ}
      mul_mem' := by
        rintro x y ⟨s, hs⟩ ⟨t, ht⟩
        exact ⟨t * s, fun φ h => by rw [Module.End.mul_apply, ht φ h, map_smul, hs φ h, mul_smul]⟩
      add_mem' := by
        rintro x y ⟨s, hs⟩ ⟨t, ht⟩
        exact ⟨s + t, fun φ h => by rw [LinearMap.add_apply, ht φ h, hs φ h, add_smul]⟩
      algebraMap_mem' := fun t => ⟨t, fun φ _ => rfl⟩ }
  have hq : ∀ (v : InfinitePlace F) u, Formalism.REAL.qdet (TR.Eop (a := a) v) u = TR.cap v (u - ((a : ℂ) - 1) / 2) := fun v u => by
    rw [TR.cap, sub_add_cancel]
  have hS : ∀ (v : InfinitePlace F) u, Formalism.REAL.qdet (TR.Eop (a := a) v) u ∈ S := fun v u => ⟨_, fun φ h => by rw [hq]; exact h v _⟩
  have hZ : ∀ (v : InfinitePlace F) u, Formalism.REAL.qdet (TR.Eop (a := a) v) u ∈ TR.Zalg F a := fun v u =>
    Algebra.subset_adjoin ⟨v, _, hq v u⟩
  obtain ⟨ω, hω⟩ : ∑ v, Formalism.REAL.Cas (TR.Eop (E := F) (a := a) v) ∈ S :=
    sum_mem fun v _ => UpperTheory.V.Af.CuspFin.casMem _ _ _ (TR.glRel_Eop v) S (hS v)
  have hΩ : ∑ v, Formalism.REAL.Cas (TR.Eop (E := F) (a := a) v) ∈ TR.Zalg F a :=
    sum_mem fun v _ => UpperTheory.V.Af.CuspFin.casMem _ _ _ (TR.glRel_Eop v) _ (hZ v)
  have hone : TR.oneL F a = ∑ v, ∑ i, b (v, i, i) := by
    funext i j w
    simp only [hb, Finset.sum_apply]
    by_cases hij : i = j <;> simp [Matrix.single_apply, Matrix.one_apply, Pi.single_apply, hij, ite_and, ite_apply]
  obtain ⟨t, ht⟩ : TR.lie F a (TR.oneL F a) ∈ S := by
    rw [hone]
    simp only [map_sum, hbE]
    exact sum_mem fun v _ => GlobalTheory.CuspRep.Central.trace_mem _ (Subalgebra.toSubmodule S) (one_mem S) (hS v)
  let X : InfinitePlace F × Fin a × Fin a → TR.Lie F a := fun l => b l - b (l.1, l.2.2, l.2.1)
  have hX : ∀ l i j, X l j i = -X l i j := by
    rintro ⟨v, p, q⟩ i j
    simp only [X, hb, Pi.sub_apply, neg_sub]
    simp [Matrix.single_apply, and_comm]
  obtain ⟨q, hm, hd, hq0⟩ := UpperTheory.V.Af.CuspFin.typePoly F a W ρ _ X hX (1 / 2)
  have hΔ : ∑ l, TR.lie F a (b l) * TR.lie F a (b l) = ∑ v, Formalism.REAL.Cas (TR.Eop (E := F) (a := a) v) +
      (1 / 2 : ℂ) • ∑ l, TR.lie F a (X l) * TR.lie F a (X l) := by
    simp only [X, map_sub, hbE, Fintype.sum_prod_type]
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => sqId (TR.Eop v)
  have hc : Commute (∑ v, Formalism.REAL.Cas (TR.Eop (E := F) (a := a) v))
      ((1 / 2 : ℂ) • ∑ l, TR.lie F a (X l) * TR.lie F a (X l)) :=
    (Commute.sum_right _ _ _ fun l _ => (TR.Cen.commute_Zalg_act hΩ (.lie (X l))).mul_right
      (TR.Cen.commute_Zalg_act hΩ (.lie (X l)))).smul_right _
  have hm' : (q.comp (Polynomial.X - Polynomial.C ω)).Monic := hm.comp (Polynomial.monic_X_sub_C ω) (by simp)
  have hd' : 0 < (q.comp (Polynomial.X - Polynomial.C ω)).natDegree := by
    rw [Polynomial.natDegree_comp]; simpa using hd
  refine @Submodule.finiteDimensional_of_le _ _ _ _ _ _ _ (UpperTheory.V.Af.CuspFin.eigenFinite_of UpperTheory.V.Af.CuspFin.mem_cuspForms_of _ b _ hm' hd' t L hL) (Submodule.span_mono ?_)
  rintro φ ⟨h1, h2, h3, h4⟩
  exact ⟨h1, h2, by rw [hΔ, aevalShift _ _ hc ω q φ (hω φ h4), hq0 φ h3], ht φ h4⟩
