import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleUnitaryAdmissible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.KFiniteCoefficientsAnalytic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviModulusOneLinearReductiveExpMulExpStatement

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.LinRed
open scoped InnerProductSpace

namespace GlobalTheory.LeviDense

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => intro v hv; exact ⟨v, hv, by simp⟩`. Consider the case `succ k ih`. Introduce `v hv`. Take `⟨v', hv', hder⟩` from `hd v hv`.

Establish `hderiv : deriv (fun t => ⟪w, T t v⟫_ℂ) = fun t => ⟪w, T t v'⟫_ℂ`. Use function extensionality and compare the values at `t`. Establish `h3 : HasDerivAt (fun s => T (s - t) v) v' t` using `HasDerivAt.comp_sub_const (f := fun s => T s v) t t (by rw [sub_self]; exact hder)`. Establish `h2 : HasDerivAt (fun s => T t (T (s - t) v)) (T t v') t` using `((T t).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h3`. Establish `h1 : HasDerivAt (fun s => T s v) (T t v') t`.

Use `h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)` and prove the remaining obligations. Use `show T s v = T t (T (s - t) v)`. Rewrite using `[← ContinuousLinearMap.comp_apply, ← hT, add_sub_cancel]`. Conclude with `((((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h1)).deriv`. Take `⟨u, hu, hk⟩` from `ih v' hv'`.

Conclude with `⟨u, hu, by rw [iteratedDeriv_succ', hderiv, hk]⟩`.
-/
private theorem exists_iteratedDeriv_inner_semigroup_eq {T : ℝ → V →L[ℂ] V} (hT : ∀ s t, T (s + t) = T s ∘L T t)
    {S : Submodule ℂ V} (hd : ∀ v ∈ S, ∃ v' ∈ S, HasDerivAt (fun t => T t v) v' 0) (w : V) (k : ℕ) :
    ∀ v ∈ S, ∃ u ∈ S, iteratedDeriv k (fun t => ⟪w, T t v⟫_ℂ) = fun t => ⟪w, T t u⟫_ℂ := by
  induction k with
  | zero => intro v hv; exact ⟨v, hv, by simp⟩
  | succ k ih =>
    intro v hv
    obtain ⟨v', hv', hder⟩ := hd v hv
    have hderiv : deriv (fun t => ⟪w, T t v⟫_ℂ) = fun t => ⟪w, T t v'⟫_ℂ := by
      funext t
      have h3 : HasDerivAt (fun s => T (s - t) v) v' t :=
        HasDerivAt.comp_sub_const (f := fun s => T s v) t t (by rw [sub_self]; exact hder)
      have h2 : HasDerivAt (fun s => T t (T (s - t) v)) (T t v') t :=
        ((T t).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h3
      have h1 : HasDerivAt (fun s => T s v) (T t v') t := by
        refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
        show T s v = T t (T (s - t) v)
        rw [← ContinuousLinearMap.comp_apply, ← hT, add_sub_cancel]
      exact ((((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h1)).deriv
    obtain ⟨u, hu, hk⟩ := ih v' hv'
    exact ⟨u, hu, by rw [iteratedDeriv_succ', hderiv, hk]⟩

/- English proof (translation)
Establish `key : ∀ v ∈ S, T t v ∈ S.topologicalClosure`. Introduce `v hv`. Rewrite using `[← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]`. Introduce `w hw`. Establish `hf` using `ha v hv w`.

Establish `hall : ∀ k, iteratedDeriv k (fun s => ⟪w, T s v⟫_ℂ) 0 = 0`. Introduce `k`. Take `⟨u, hu, hk⟩` from `exists_iteratedDeriv_inner_semigroup_eq hT hd w k v hv`. Rewrite using `[hk]`. Simplify using `only [h0, ContinuousLinearMap.one_apply]`.

Conclude with `Submodule.inner_left_of_mem_orthogonal hu hw`. Establish `htop : analyticOrderAt (fun s => ⟪w, T s v⟫_ℂ) 0 = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨m, hm⟩` from `ENat.ne_top_iff_exists.1 hne`. Establish `hle` using `(natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (n := m + 1) (hf 0 (Set.mem_univ _))).2 (fun i _ => hall i)`.

Rewrite `hle` using `[← hm]`. Establish `: m + 1 ≤ m` using `by exact_mod_cast hle`. Use linear arithmetic over natural numbers and integers. Conclude with `hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0) (analyticOrderAt_eq_top.1 htop) (Set.mem_univ t)`. Introduce `x hx`.

Establish `hcl : IsClosed ((T t) ⁻¹' (S.topologicalClosure : Set V))` using `S.isClosed_topologicalClosure.preimage (T t).continuous`. Establish `hx' : x ∈ closure (S : Set V)` using `by rw [← Submodule.topologicalClosure_coe]; exact hx`. Conclude with `closure_minimal (fun v hv => key v hv) hcl hx'`.
-/
theorem oneParameter_mem_closure {T : ℝ → V →L[ℂ] V} (h0 : T 0 = 1) (hT : ∀ s t, T (s + t) = T s ∘L T t)
    {S : Submodule ℂ V} (hd : ∀ v ∈ S, ∃ v' ∈ S, HasDerivAt (fun t => T t v) v' 0)
    (ha : ∀ v ∈ S, ∀ w, AnalyticOnNhd ℝ (fun t => ⟪w, T t v⟫_ℂ) Set.univ) (t : ℝ) :
    ∀ v ∈ S.topologicalClosure, T t v ∈ S.topologicalClosure := by
  have key : ∀ v ∈ S, T t v ∈ S.topologicalClosure := by
    intro v hv
    rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
    intro w hw
    have hf := ha v hv w
    have hall : ∀ k, iteratedDeriv k (fun s => ⟪w, T s v⟫_ℂ) 0 = 0 := by
      intro k
      obtain ⟨u, hu, hk⟩ := exists_iteratedDeriv_inner_semigroup_eq hT hd w k v hv
      rw [hk]
      simp only [h0, ContinuousLinearMap.one_apply]
      exact Submodule.inner_left_of_mem_orthogonal hu hw
    have htop : analyticOrderAt (fun s => ⟪w, T s v⟫_ℂ) 0 = ⊤ := by
      by_contra hne
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hne
      have hle := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (n := m + 1)
        (hf 0 (Set.mem_univ _))).2 (fun i _ => hall i)
      rw [← hm] at hle
      have : m + 1 ≤ m := by exact_mod_cast hle
      omega
    exact hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0)
      (analyticOrderAt_eq_top.1 htop) (Set.mem_univ t)
  intro x hx
  have hcl : IsClosed ((T t) ⁻¹' (S.topologicalClosure : Set V)) :=
    S.isClosed_topologicalClosure.preimage (T t).continuous
  have hx' : x ∈ closure (S : Set V) := by rw [← Submodule.topologicalClosure_coe]; exact hx
  exact closure_minimal (fun v hv => key v hv) hcl hx'

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/- English proof (translation)
Introduce `t₀ _`. Take `⟨U, F, hUo, hgU, hF, hfF⟩` from `hf _ (hX t₀)`. Set `L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] (Fin n → Fin n → ℂ)` to `LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).symm.toLinearMap`. Establish `hL : ∀ A, L A = Matrix.of.symm A` using `fun _ => rfl`. Establish `hE : AnalyticAt ℝ (fun t : ℝ => L (NormedSpace.exp (t • X))) t₀` using `L.analyticAt _ |>.comp ((NormedSpace.exp_analytic (𝕂 := ℝ) _).comp ((analyticAt_id).smul analyticAt_const))`.

Establish `hE' : AnalyticAt ℝ (fun t : ℝ => F (L (NormedSpace.exp (t • X)))) t₀` using `(hF _ (by rw [hL]; exact hgU)).comp hE`. Establish `hev : ∀ᶠ t in nhds t₀, L (NormedSpace.exp (t • X)) ∈ U` using `hE.continuousAt.preimage_mem_nhds (hUo.mem_nhds (by rw [hL]; exact hgU))`. Use `hE'.congr (hev.mono fun t ht => ?_)` and prove the remaining obligations. Establish `h1` using `hfF _ ht (by rw [hL, Equiv.apply_symm_apply]; exact hX t)`. Rewrite `h1` using `[hL, Equiv.apply_symm_apply]`.

Conclude with `h1.symm`.
-/
theorem analytic_exp {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hf : AnalyticOnGroup G f) {X : Matrix (Fin n) (Fin n) ℂ} (hX : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G) :
    AnalyticOnNhd ℝ (fun t : ℝ => f (NormedSpace.exp (t • X))) Set.univ := by
  intro t₀ _
  obtain ⟨U, F, hUo, hgU, hF, hfF⟩ := hf _ (hX t₀)
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] (Fin n → Fin n → ℂ) :=
    LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).symm.toLinearMap
  have hL : ∀ A, L A = Matrix.of.symm A := fun _ => rfl
  have hE : AnalyticAt ℝ (fun t : ℝ => L (NormedSpace.exp (t • X))) t₀ :=
    L.analyticAt _ |>.comp ((NormedSpace.exp_analytic (𝕂 := ℝ) _).comp
      ((analyticAt_id).smul analyticAt_const))
  have hE' : AnalyticAt ℝ (fun t : ℝ => F (L (NormedSpace.exp (t • X)))) t₀ :=
    (hF _ (by rw [hL]; exact hgU)).comp hE
  have hev : ∀ᶠ t in nhds t₀, L (NormedSpace.exp (t • X)) ∈ U :=
    hE.continuousAt.preimage_mem_nhds (hUo.mem_nhds (by rw [hL]; exact hgU))
  refine hE'.congr (hev.mono fun t ht => ?_)
  have h1 := hfF _ ht (by rw [hL, Equiv.apply_symm_apply]; exact hX t)
  rw [hL, Equiv.apply_symm_apply] at h1
  exact h1.symm

/- English proof (translation)
Establish `h2 : A * Aᴴ = 1`. Rewrite using `[← Matrix.star_eq_conjTranspose]`. Conclude with `Matrix.mem_unitaryGroup_iff.1 hu`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem mul_Jm_comm_of_unitary_of_preserves {n : ℕ} (ε : Fin n → Bool) {A : Matrix (Fin n) (Fin n) ℂ}
    (hu : A ∈ Matrix.unitaryGroup (Fin n) ℂ) (hJ : Aᴴ * Formalism.REAL.Jm ε * A = Formalism.REAL.Jm ε) :
    A * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * A := by
  have h2 : A * Aᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.1 hu
  calc A * Formalism.REAL.Jm ε = A * (Aᴴ * Formalism.REAL.Jm ε * A) := by rw [hJ]
    _ = (A * Aᴴ) * Formalism.REAL.Jm ε * A := by simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε * A := by rw [h2, Matrix.one_mul]

end

omit [CompleteSpace V] in

/- English proof (translation)
Take `⟨U, hU, hv, hk⟩` from `h`. Use `⟨U, hU, hv, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨g, hgM, rfl⟩, hgu⟩ w hw`. Use `hk g (Subgroup.mem_inf.2 ⟨?_, hgM⟩) w hw` and prove the remaining obligations. Use `show toM g ∈ Kset ε`.

Use `show toM g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ toM g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * toM g`. Conclude with `⟨hgu, mul_Jm_comm_of_unitary_of_preserves ε hgu g.2⟩`.
-/
theorem isKFinOn_of_isKFinIn {n : ℕ} {ε : Fin n → Bool} {M : Subgroup (UJ ε)}
    {σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)} {v : V} (h : IsKFinIn M σ v) : IsKFinOn (mats M) σ v := by
  obtain ⟨U, hU, hv, hk⟩ := h
  refine ⟨U, hU, hv, ?_⟩
  rintro _ ⟨⟨g, hgM, rfl⟩, hgu⟩ w hw
  refine hk g (Subgroup.mem_inf.2 ⟨?_, hgM⟩) w hw
  show toM g ∈ Kset ε
  show toM g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ toM g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * toM g
  exact ⟨hgu, mul_Jm_comm_of_unitary_of_preserves ε hgu g.2⟩

/- English proof (translation)
Introduce `n ε a j W hW hj V _ _ _ σ hU hI S hS hK hD`. Take `⟨hLR, hdec⟩` from `GlobalTheory.T.leviModulusOne_linearReductive_exp_mul_exp n ε a j W hW hj`. Establish `hadmG : GlobalTheory.LinRed.IsAdmOn (mats (leviOne ε W)) σ` using `hadm n _ hLR V σ hU hI`. Establish `hexp : ∀ X : Matrix (Fin n) (Fin n) ℂ, (∀ t : ℝ, NormedSpace.exp (t • X) ∈ mats (leviOne ε W)) → ∀ x ∈ S.topologicalClosure, σ (NormedSpace.exp X) x ∈ S.topologicalClosure`. Introduce `X hX x hx`.

Establish `h1` using `oneParameter_mem_closure (T := fun t : ℝ => σ (NormedSpace.exp (t • X))) ?_ ?_ (hD X hX) ?_ 1 x hx`. Simplify using `using h1`. Simplify using `only [zero_smul, NormedSpace.exp_zero]`. Conclude with `hU.1.1`. Introduce `s t show σ (NormedSpace.exp ((s + t) • X)) = σ (NormedSpace.exp (s • X)) ∘L σ (NormedSpace.exp (t • X))`.

Rewrite using `[add_smul, Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t)]`. Conclude with `hU.1.2 _ (hX s) _ (hX t)`. Introduce `v hv w`. Conclude with `analytic_exp (han n _ hLR V σ hadmG v w (isKFinOn_of_isKFinIn (hK v hv))) hX`. Establish `hinv : ∀ g ∈ mats (leviOne ε W), ∀ x ∈ S.topologicalClosure, σ g x ∈ S.topologicalClosure`.

Introduce `g hg x hx`. Take `⟨X, Y, hX, hY, rfl⟩` from `hdec g hg`. Establish `hX1 : NormedSpace.exp X ∈ mats (leviOne ε W)` using `by simpa using hX 1`. Establish `hY1 : NormedSpace.exp Y ∈ mats (leviOne ε W)` using `by simpa using hY 1`. Rewrite using `[hU.1.2 _ hX1 _ hY1, ContinuousLinearMap.comp_apply]`.

Conclude with `hexp X hX _ (hexp Y hY x hx)`. Break down `hI S.topologicalClosure S.isClosed_topologicalClosure hinv with h | h` into its components or cases. Establish `hle` using `S.le_topologicalClosure`. Rewrite `hle` using `[h]`. Conclude with `absurd (eq_bot_iff.2 hle) hS`.

Rewrite using `[dense_iff_closure_eq, ← Submodule.topologicalClosure_coe, h, Submodule.top_coe]`.
-/
theorem leviSubmoduleDense (hadm : GlobalTheory.Published.IrreducibleUnitaryAdmissible)
    (han : GlobalTheory.Published.KFiniteCoefficientsAnalytic) : GlobalTheory.Published.LeviSubmoduleDense := by
  intro n ε a j W hW hj V _ _ _ σ hU hI S hS hK hD
  obtain ⟨hLR, hdec⟩ := GlobalTheory.T.leviModulusOne_linearReductive_exp_mul_exp n ε a j W hW hj
  have hadmG : GlobalTheory.LinRed.IsAdmOn (mats (leviOne ε W)) σ := hadm n _ hLR V σ hU hI
  have hexp : ∀ X : Matrix (Fin n) (Fin n) ℂ, (∀ t : ℝ, NormedSpace.exp (t • X) ∈ mats (leviOne ε W)) →
      ∀ x ∈ S.topologicalClosure, σ (NormedSpace.exp X) x ∈ S.topologicalClosure := by
    intro X hX x hx
    have h1 := oneParameter_mem_closure (T := fun t : ℝ => σ (NormedSpace.exp (t • X))) ?_ ?_ (hD X hX) ?_ 1 x hx
    · simpa using h1
    · simp only [zero_smul, NormedSpace.exp_zero]
      exact hU.1.1
    · intro s t
      show σ (NormedSpace.exp ((s + t) • X)) = σ (NormedSpace.exp (s • X)) ∘L σ (NormedSpace.exp (t • X))
      rw [add_smul, Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t)]
      exact hU.1.2 _ (hX s) _ (hX t)
    · intro v hv w
      exact analytic_exp (han n _ hLR V σ hadmG v w (isKFinOn_of_isKFinIn (hK v hv))) hX
  have hinv : ∀ g ∈ mats (leviOne ε W), ∀ x ∈ S.topologicalClosure, σ g x ∈ S.topologicalClosure := by
    intro g hg x hx
    obtain ⟨X, Y, hX, hY, rfl⟩ := hdec g hg
    have hX1 : NormedSpace.exp X ∈ mats (leviOne ε W) := by simpa using hX 1
    have hY1 : NormedSpace.exp Y ∈ mats (leviOne ε W) := by simpa using hY 1
    rw [hU.1.2 _ hX1 _ hY1, ContinuousLinearMap.comp_apply]
    exact hexp X hX _ (hexp Y hY x hx)
  rcases hI S.topologicalClosure S.isClosed_topologicalClosure hinv with h | h
  · have hle := S.le_topologicalClosure
    rw [h] at hle
    exact absurd (eq_bot_iff.2 hle) hS
  · rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe, h, Submodule.top_coe]

end GlobalTheory.LeviDense

end
