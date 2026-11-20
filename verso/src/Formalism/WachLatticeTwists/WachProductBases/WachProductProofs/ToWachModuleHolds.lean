import Formalism.WachLatticeTwists.WachProductBases.Statement
import Formalism.WachLatticeTwists.WachProductBases.WachProductProofs.FreeMembershipHeightOne
import Formalism.CoboundaryTransfers.GammaStableTransfers.GammaStableOfGammaQUnitHolds

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N1

open Formalism.CoboundaryTransfers Finset

/- English proof (translation)
Introduce `O A _ _ _ S ι _ pr D _ _ _ _ W M h M₀ h₀ hrad hP2 hP5 hM hh`. Consider the cases of `nonempty_fintype ι`. Establish `hGQ : S.base.GammaQ` using `(base_wach_holds O A S).2.2 hrad`. Set `N' : Submodule A (ι → D)` to `Submodule.pi Set.univ W.N`. Set `Φ : (ι → D) →ₗ[O] (ι → D)` to `LinearMap.pi (fun i => (W.φ i).comp (LinearMap.proj (pr i)))`.

Set `Γ : (ι → D) →ₗ[O] (ι → D)` to `LinearMap.pi (fun i => (W.γ i).comp (LinearMap.proj i))`. Establish `hΦ : ∀ x i, Φ x i = W.φ i (x (pr i))` using `fun _ _ => rfl`. Establish `hΓ : ∀ x i, Γ x i = W.γ i (x i)` using `fun _ _ => rfl`. Establish `hmem : ∀ x : ι → D, x ∈ N' ↔ ∀ i, x i ∈ W.N i`. Introduce `x`.

Simplify using `[N', Submodule.mem_pi]`. Establish `hΓs : ∀ (a : A) (x : ι → D), Γ (a • x) = S.base.γ a • Γ x`. Introduce `a x`. Use function extensionality and compare the values at `i`. Rewrite using `[hΓ, Pi.smul_apply, W.γ_smul, Pi.smul_apply, hΓ]`.

Both sides reduce to the same expression. Establish `hQbij : Function.Bijective (fun x : ι → D => S.base.Q • x)`. Prove the components needed by the constructor for the conclusion. Introduce `x y hxy`. Use function extensionality and compare the values at `i`.

Conclude with `W.Q_bij.1 (congrFun hxy i)`. Introduce `y choose x hx using fun i => W.Q_bij.2 (y i)`. Conclude with `⟨x, funext hx⟩`. Establish `hΓN : ∀ x ∈ N', ∃ x' ∈ N', Γ x - x = S.base.X • x'`. Introduce `x hx`.

Use `choose x' hx' hx'' using fun i => hP2 i (x i) ((hmem x).1 hx i)`. Conclude with `⟨x', (hmem x').2 hx', funext fun i => hx'' i⟩`. Set `W' : WachMod S.base M₀ (ι → D)` to `{ N := N' φ := Φ γ := Γ φ_smul := by`. Introduce `a x`. Use function extensionality and compare the values at `i`.

Rewrite using `[hΦ, Pi.smul_apply, W.φ_smul, Pi.smul_apply, hΦ]`. Both sides reduce to the same expression. Use `γ_smul := hΓs`. Use `comm := by`. Introduce `x`.

Use function extensionality and compare the values at `i`. Rewrite using `[hΦ, hΓ, hΓ, hΦ, W.comm]`. Use `X_inj := by`. Introduce `x hx`. Use function extensionality and compare the values at `i`.

Apply `W.X_bij.1` to reduce the goal to its premises. Establish `h0 : S.X • x i = 0` using `congrFun hx i`. Simplify using `using h0`. Use `Q_bij := hQbij`. Use `φ_N := by`.

Introduce `x hx`. Rewrite using `[hmem]`. Introduce `i`. Take `⟨k, hk⟩` from `Nat.exists_eq_add_of_le (hM i)`. Rewrite using `[Pi.smul_apply, hΦ, hk, pow_add, mul_comm, mul_smul]`.

Conclude with `(W.N i).smul_mem _ (hP5.1 i _ ((hmem x).1 hx (pr i)))`. Use `γ_N := hΓN`. Use `γ_QN := gammaStableOfGammaQUnit_holds O A S.base M₀ (ι → D) N' Γ hGQ hQbij hΓs hΓN }`. Use `⟨W', rfl, hΦ, hΓ, ?_⟩` and prove the remaining obligations. Introduce `y hy`.

Use `set T := Submodule.span A (W'.φ '' (W'.N : Set (ι → D))) with hT`. Establish `hsingle : ∀ i, (Submodule.span A (W.φ i '' (W.N (pr i) : Set D))).map (LinearMap.single A (fun _ => D) i) ≤ T`. Introduce `i`. Rewrite using `[Submodule.map_span]`. Apply `Submodule.span_mono` to reduce the goal to its premises.

Introduce and unpack `_ ⟨_, ⟨n, hn, rfl⟩, rfl⟩`. Use `⟨Pi.single (pr i) n, ?_, ?_⟩` and prove the remaining obligations. Use `show Pi.single (pr i) n ∈ N'`. Rewrite using `[hmem]`. Introduce `j`.

Distinguish the cases in `hj : j = pr i`. Substitute `hj` using the available equality. Simplify using `using hn`. Rewrite using `[Pi.single_eq_of_ne hj]`. Conclude with `(W.N j).zero_mem`.

Use function extensionality and compare the values at `j show W.φ j ((Pi.single (pr i) n : ι → D) (pr j)) = (Pi.single i (W.φ i n) : ι → D) j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Establish `: pr j ≠ pr i` using `fun h => hj (pr.injective h)`.

Rewrite using `[Pi.single_eq_of_ne hj, Pi.single_eq_of_ne this, map_zero]`. Establish `hsum : S.base.Q ^ h₀ • y = ∑ i, Pi.single i (S.Q ^ h₀ • y i)`. Use function extensionality and compare the values at `j`. Rewrite using `[Finset.sum_apply, Finset.sum_eq_single j]`. Simplify using the standard rewrite rules.

Both sides reduce to the same expression. Introduce `i _ hij`. Rewrite using `[Pi.single_eq_of_ne (Ne.symm hij)]`. Introduce `hj`. Conclude with `absurd (Finset.mem_univ j) hj`.

Rewrite using `[hsum]`. Use `T.sum_mem fun i _ => hsingle i ⟨_, ?_, rfl⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `Nat.exists_eq_add_of_le (hh i)`. Rewrite using `[hk, pow_add, mul_comm, mul_smul]`. Conclude with `Submodule.smul_mem _ _ (hP5.2 i _ ((hmem y).1 hy i))`.
-/
theorem to_wach_module_holds : ToWach := by
  intro O A _ _ _ S ι _ pr D _ _ _ _ W M h M₀ h₀ hrad hP2 hP5 hM hh
  classical
  cases nonempty_fintype ι
  have hGQ : S.base.GammaQ := (base_wach_holds O A S).2.2 hrad
  let N' : Submodule A (ι → D) := Submodule.pi Set.univ W.N
  let Φ : (ι → D) →ₗ[O] (ι → D) := LinearMap.pi (fun i => (W.φ i).comp (LinearMap.proj (pr i)))
  let Γ : (ι → D) →ₗ[O] (ι → D) := LinearMap.pi (fun i => (W.γ i).comp (LinearMap.proj i))
  have hΦ : ∀ x i, Φ x i = W.φ i (x (pr i)) := fun _ _ => rfl
  have hΓ : ∀ x i, Γ x i = W.γ i (x i) := fun _ _ => rfl
  have hmem : ∀ x : ι → D, x ∈ N' ↔ ∀ i, x i ∈ W.N i := by
    intro x
    simp [N', Submodule.mem_pi]
  have hΓs : ∀ (a : A) (x : ι → D), Γ (a • x) = S.base.γ a • Γ x := by
    intro a x
    funext i
    rw [hΓ, Pi.smul_apply, W.γ_smul, Pi.smul_apply, hΓ]
    rfl
  have hQbij : Function.Bijective (fun x : ι → D => S.base.Q • x) := by
    constructor
    · intro x y hxy
      funext i
      exact W.Q_bij.1 (congrFun hxy i)
    · intro y
      choose x hx using fun i => W.Q_bij.2 (y i)
      exact ⟨x, funext hx⟩
  have hΓN : ∀ x ∈ N', ∃ x' ∈ N', Γ x - x = S.base.X • x' := by
    intro x hx
    choose x' hx' hx'' using fun i => hP2 i (x i) ((hmem x).1 hx i)
    exact ⟨x', (hmem x').2 hx', funext fun i => hx'' i⟩
  let W' : WachMod S.base M₀ (ι → D) :=
    { N := N'
      φ := Φ
      γ := Γ
      φ_smul := by
        intro a x
        funext i
        rw [hΦ, Pi.smul_apply, W.φ_smul, Pi.smul_apply, hΦ]
        rfl
      γ_smul := hΓs
      comm := by
        intro x
        funext i
        rw [hΦ, hΓ, hΓ, hΦ, W.comm]
      X_inj := by
        intro x hx
        funext i
        apply W.X_bij.1
        have h0 : S.X • x i = 0 := congrFun hx i
        simpa using h0
      Q_bij := hQbij
      φ_N := by
        intro x hx
        rw [hmem]
        intro i
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (hM i)
        rw [Pi.smul_apply, hΦ, hk, pow_add, mul_comm, mul_smul]
        exact (W.N i).smul_mem _ (hP5.1 i _ ((hmem x).1 hx (pr i)))
      γ_N := hΓN
      γ_QN := gammaStableOfGammaQUnit_holds O A S.base M₀ (ι → D) N' Γ hGQ hQbij hΓs hΓN }
  refine ⟨W', rfl, hΦ, hΓ, ?_⟩
  intro y hy
  set T := Submodule.span A (W'.φ '' (W'.N : Set (ι → D))) with hT
  have hsingle : ∀ i, (Submodule.span A (W.φ i '' (W.N (pr i) : Set D))).map
      (LinearMap.single A (fun _ => D) i) ≤ T := by
    intro i
    rw [Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨_, ⟨n, hn, rfl⟩, rfl⟩
    refine ⟨Pi.single (pr i) n, ?_, ?_⟩
    · show Pi.single (pr i) n ∈ N'
      rw [hmem]
      intro j
      by_cases hj : j = pr i
      · subst hj; simpa using hn
      · rw [Pi.single_eq_of_ne hj]; exact (W.N j).zero_mem
    · funext j
      show W.φ j ((Pi.single (pr i) n : ι → D) (pr j)) = (Pi.single i (W.φ i n) : ι → D) j
      by_cases hj : j = i
      · subst hj; simp
      · have : pr j ≠ pr i := fun h => hj (pr.injective h)
        rw [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne this, map_zero]
  have hsum : S.base.Q ^ h₀ • y = ∑ i, Pi.single i (S.Q ^ h₀ • y i) := by
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simp; rfl
    · intro i _ hij
      rw [Pi.single_eq_of_ne (Ne.symm hij)]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  rw [hsum]
  refine T.sum_mem fun i _ => hsingle i ⟨_, ?_, rfl⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (hh i)
  rw [hk, pow_add, mul_comm, mul_smul]
  exact Submodule.smul_mem _ _ (hP5.2 i _ ((hmem y).1 hy i))

end Formalism.RepresentationBoundsCohomology.N1
