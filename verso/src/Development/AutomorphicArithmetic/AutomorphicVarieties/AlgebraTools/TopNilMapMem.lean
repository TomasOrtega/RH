import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TopNilDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TnFree

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

/- English proof (translation)
Rewrite `hx`, the goal using `[mem_topNil]`. Introduce `i j`. Establish `hpow : ∀ r : ℕ, f ((T i ^ r) x) = (T' i ^ r) (f x)`. Introduce `r`. Proceed by induction on `r with`.

Consider the case `zero => simp`. Consider the case `succ n ih => rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, hf, ih]`. Establish `hle : Submodule.map f (I ^ j • (⊤ : Submodule R M)) ≤ I ^ j • (⊤ : Submodule R M')`. Rewrite using `[Submodule.map_smul'']`. Conclude with `Submodule.smul_mono le_rfl le_top`.

Use `filter_upwards [hx i j] with r hr`. Rewrite using `[← hpow]`. Conclude with `hle ⟨_, hr, rfl⟩`.
-/
private theorem topNil_map_mem {R M M' κ : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (I : Ideal R) (T : κ → Module.End R M)
    (T' : κ → Module.End R M') (f : M →ₗ[R] M') (hf : ∀ i x, f (T i x) = T' i (f x))
    {x : M} (hx : x ∈ topNil I T) : f x ∈ topNil I T' := by
  rw [mem_topNil] at hx ⊢
  intro i j
  have hpow : ∀ r : ℕ, f ((T i ^ r) x) = (T' i ^ r) (f x) := by
    intro r
    induction r with
    | zero => simp
    | succ n ih => rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, hf, ih]
  have hle : Submodule.map f (I ^ j • (⊤ : Submodule R M)) ≤ I ^ j • (⊤ : Submodule R M') := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  filter_upwards [hx i j] with r hr
  rw [← hpow]
  exact hle ⟨_, hr, rfl⟩

/- English proof (translation)
Introduce `R _ _ _ _ κ M _ _ M' _ _ _ _ T T' hT hT' f hf`. Take `⟨_, hsmul, -, -⟩` from `topNil_free R κ M T hT`. Use `⟨le_antisymm ?_ ?_, fun I hI => by rw [hI]; exact hsmul I⟩` and prove the remaining obligations. Rewrite using `[Submodule.map_le_iff_le_comap]`. Introduce `x hx`.

Conclude with `⟨topNil_map_mem _ T T' f hf hx, x, rfl⟩`. Introduce and unpack `y ⟨hy, x, rfl⟩`. Establish `hTx : ∀ i j x, T i (T j x) = T j (T i x)` using `fun i j x => by`. Rewrite using `[← Module.End.mul_apply, (hT i j).eq, Module.End.mul_apply]`. Establish `hT'x : ∀ i j x, T' i (T' j x) = T' j (T' i x)` using `fun i j x => by`.

Rewrite using `[← Module.End.mul_apply, (hT' i j).eq, Module.End.mul_apply]`. Set `S : κ → Module.End R (M × M')` to `fun i => (T i).prodMap (T' i)`. Establish `hS : ∀ i j, Commute (S i) (S j)`. Introduce `i j`. Use `show S i * S j = S j * S i`.

Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `p`. Simplify using `[S, Module.End.mul_apply, hTx i j, hT'x i j]`. Take `⟨⟨C, hC, hstab⟩, -⟩` from `topNil_free R κ (M × M') S hS`. Set `φ : Module.End R (M × M')` to `(LinearMap.inr R M M').comp (f.comp (LinearMap.fst R M M'))`.

Establish `hφ : ∀ i, Commute φ (S i)`. Introduce `i`. Use `show φ * S i = S i * φ`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `p`.

Simplify using `[φ, S, Module.End.mul_apply, hf]`. Establish `hmem : ((x, 0) : M × M') ∈ topNil (IsLocalRing.maximalIdeal R) S ⊔ C`. Rewrite using `[hC.sup_eq_top]`. Conclude with `Submodule.mem_top`. Take `⟨n, hn, c, hc, hnc⟩` from `Submodule.mem_sup.mp hmem`.

Establish `hn1 : n.1 ∈ topNil (IsLocalRing.maximalIdeal R) T` using `topNil_map_mem _ S T (LinearMap.fst R M M') (fun i p => rfl) hn`. Establish `hφc : φ c ∈ C` using `(hstab φ hφ).2 c hc`. Establish `hx : x = n.1 + c.1`. Use `congrArg Prod.fst hnc` as an intermediate fact. Simplify using `using this.symm`.

Establish `hfc : f c.1 ∈ topNil (IsLocalRing.maximalIdeal R) T'`. Establish `: f c.1 = f x - f n.1`. Rewrite using `[hx]`. Simplify using the standard rewrite rules. Rewrite using `[this]`.

Conclude with `Submodule.sub_mem _ hy (topNil_map_mem _ T T' f hf hn1)`. Establish `hφn : φ c ∈ topNil (IsLocalRing.maximalIdeal R) S`. Use `topNil_map_mem _ T' S (LinearMap.inr R M M') (fun i y => by simp [S]) hfc` as an intermediate fact. Simplify `this` using `[φ]`. Establish `h0 : φ c = 0` using `(Submodule.disjoint_def.mp hC.disjoint) _ hφn hφc`.

Establish `hfc0 : f c.1 = 0`. Use `congrArg Prod.snd h0` as an intermediate fact. Simplify `this` using `[φ]`. Use `⟨n.1, hn1, ?_⟩` and prove the remaining obligations. Rewrite using `[hx, map_add, hfc0, add_zero]`.
-/
theorem UpperTheory.V.AlgebraTools.topNil_map :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (κ : Type) (M : Type) [AddCommGroup M] [Module R M] (M' : Type) [AddCommGroup M'] [Module R M'] [Module.Finite R M] [Module.Finite R M'] (T : κ → Module.End R M) (T' : κ → Module.End R M'),
      (∀ i j, Commute (T i) (T j)) → (∀ i j, Commute (T' i) (T' j)) → ∀ f : M →ₗ[R] M', (∀ i x, f (T i x) = T' i (f x)) →
      (topNil (IsLocalRing.maximalIdeal R) T).map f = topNil (IsLocalRing.maximalIdeal R) T' ⊓ LinearMap.range f ∧
      ∀ I : Ideal R, LinearMap.ker f = I • ⊤ → LinearMap.ker f ⊓ topNil (IsLocalRing.maximalIdeal R) T = I • topNil (IsLocalRing.maximalIdeal R) T := by
  intro R _ _ _ _ κ M _ _ M' _ _ _ _ T T' hT hT' f hf
  obtain ⟨_, hsmul, -, -⟩ := topNil_free R κ M T hT
  refine ⟨le_antisymm ?_ ?_, fun I hI => by rw [hI]; exact hsmul I⟩
  · rw [Submodule.map_le_iff_le_comap]
    intro x hx
    exact ⟨topNil_map_mem _ T T' f hf hx, x, rfl⟩
  · rintro y ⟨hy, x, rfl⟩
    have hTx : ∀ i j x, T i (T j x) = T j (T i x) := fun i j x => by
      rw [← Module.End.mul_apply, (hT i j).eq, Module.End.mul_apply]
    have hT'x : ∀ i j x, T' i (T' j x) = T' j (T' i x) := fun i j x => by
      rw [← Module.End.mul_apply, (hT' i j).eq, Module.End.mul_apply]
    let S : κ → Module.End R (M × M') := fun i => (T i).prodMap (T' i)
    have hS : ∀ i j, Commute (S i) (S j) := by
      intro i j
      show S i * S j = S j * S i
      apply LinearMap.ext
      intro p
      simp [S, Module.End.mul_apply, hTx i j, hT'x i j]
    obtain ⟨⟨C, hC, hstab⟩, -⟩ := topNil_free R κ (M × M') S hS
    let φ : Module.End R (M × M') := (LinearMap.inr R M M').comp (f.comp (LinearMap.fst R M M'))
    have hφ : ∀ i, Commute φ (S i) := by
      intro i
      show φ * S i = S i * φ
      apply LinearMap.ext
      intro p
      simp [φ, S, Module.End.mul_apply, hf]
    have hmem : ((x, 0) : M × M') ∈ topNil (IsLocalRing.maximalIdeal R) S ⊔ C := by
      rw [hC.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨n, hn, c, hc, hnc⟩ := Submodule.mem_sup.mp hmem
    have hn1 : n.1 ∈ topNil (IsLocalRing.maximalIdeal R) T :=
      topNil_map_mem _ S T (LinearMap.fst R M M') (fun i p => rfl) hn
    have hφc : φ c ∈ C := (hstab φ hφ).2 c hc
    have hx : x = n.1 + c.1 := by
      have := congrArg Prod.fst hnc
      simpa using this.symm
    have hfc : f c.1 ∈ topNil (IsLocalRing.maximalIdeal R) T' := by
      have : f c.1 = f x - f n.1 := by
        rw [hx]
        simp
      rw [this]
      exact Submodule.sub_mem _ hy (topNil_map_mem _ T T' f hf hn1)
    have hφn : φ c ∈ topNil (IsLocalRing.maximalIdeal R) S := by
      have := topNil_map_mem _ T' S (LinearMap.inr R M M') (fun i y => by simp [S]) hfc
      simpa [φ] using this
    have h0 : φ c = 0 := (Submodule.disjoint_def.mp hC.disjoint) _ hφn hφc
    have hfc0 : f c.1 = 0 := by
      have := congrArg Prod.snd h0
      simpa [φ] using this
    refine ⟨n.1, hn1, ?_⟩
    rw [hx, map_add, hfc0, add_zero]
