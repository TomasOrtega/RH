import Formalism.WachLatticeTwists.WachProductBases.Statement
import Formalism.CoboundaryTransfers.GammaStableTransfers.MemCoboundariesOfIsOneCoboundary
import Formalism.CoboundaryTransfers.GammaStableTransfers.GammaStableOfGammaQUnitHolds
import Formalism.CoboundaryTransfers.GammaStableTransfers.DiffOneSmulOfTower

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N1

open Formalism.CoboundaryTransfers Finset

/- English proof (translation)
Introduce `A _ D₀ D₁ _ _ _ _ f N₀ N₁ l hrat hsat x hx`. Take `⟨k, hk⟩` from `hrat x hx`. Proceed by induction on `k with`. Consider the case `zero => simpa using hk`. Consider the case `succ k ih`.

Apply `ih` to reduce the goal to its premises. Apply `hsat` to reduce the goal to its premises. Rewrite using `[smul_smul, ← pow_succ']` and apply the resulting hypothesis.
-/
theorem kernel_intersection_holds : ComapLeOfSaturated := by
  intro A _ D₀ D₁ _ _ _ _ f N₀ N₁ l hrat hsat x hx
  obtain ⟨k, hk⟩ := hrat x hx
  induction k with
  | zero => simpa using hk
  | succ k ih =>
    apply ih
    apply hsat
    rwa [smul_smul, ← pow_succ']

/- English proof (translation)
Introduce `A _ D₁ D₂ _ _ _ _ f N₁ N₂ π l a hsurj hfN hl hdens hsat hfg`. Establish `hsat' : ∀ (b : ℕ) (d : D₂), (∃ k : ℕ, π ^ k • (l ^ b • d) ∈ N₂) → ∃ k : ℕ, π ^ k • d ∈ N₂`. Introduce `b`. Proceed by induction on `b with`. Consider the case `zero => intro d h`.

Simplify using `using h`. Consider the case `succ b ih`. Introduce `d ⟨k, hk⟩`. Apply `ih` to reduce the goal to its premises. Apply `hsat` to reduce the goal to its premises.

Conclude with `⟨k, by rwa [smul_smul l, ← pow_succ']⟩`. Establish `hpt : ∀ n ∈ N₂, ∃ c : ℕ, ∃ n₁ ∈ N₁, f n₁ = π ^ c • n`. Introduce `n hn`. Take `⟨d, rfl⟩` from `hsurj n`. Take `⟨k, n₁, hn₁, d', hd⟩` from `hdens d`.

Establish `h1 : l ^ a • f d' = π ^ k • f d - f n₁`. Rewrite using `[← map_smul, ← map_smul, hd, map_add]`. Normalize the expressions using the abelian group laws. Take `⟨j, hj⟩` from `hsat' a (f d') ⟨0, by`. Rewrite using `[pow_zero, one_smul, h1]`.

Conclude with `N₂.sub_mem (N₂.smul_mem _ hn) (hfN _ hn₁)⟩`. Take `⟨n₁', hn₁', hf'⟩` from `hl _ hj`. Use `⟨j + k, π ^ j • n₁ + n₁', N₁.add_mem (N₁.smul_mem _ hn₁) hn₁', ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_smul, hf', pow_add, mul_smul, smul_comm (l ^ a), h1, smul_sub]`. Normalize the expressions using the abelian group laws.

Establish `huni : ∀ s : Finset D₂, (∀ x ∈ s, x ∈ N₂) → ∃ c : ℕ, ∀ x ∈ s, ∃ n₁ ∈ N₁, f n₁ = π ^ c • x`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro _; exact ⟨0, by simp⟩`. Consider the case `insert x s hx ih`.

Introduce `h`. Take `⟨c, hc⟩` from `ih (fun y hy => h y (Finset.mem_insert_of_mem hy))`. Take `⟨c', n', hn', hf'⟩` from `hpt x (h x (Finset.mem_insert_self _ _))`. Use `⟨c + c', ?_⟩` and prove the remaining obligations. Introduce `y hy`.

Break down `Finset.mem_insert.1 hy with rfl | hy` into its components or cases. Conclude with `⟨π ^ c • n', N₁.smul_mem _ hn', by rw [map_smul, hf', pow_add, mul_smul]⟩`. Take `⟨n, hn, hf⟩` from `hc y hy`. Conclude with `⟨π ^ c' • n, N₁.smul_mem _ hn, by rw [map_smul, hf, pow_add, mul_comm, mul_smul]⟩`. Take `⟨s, hs⟩` from `hfg`.

Take `⟨c, hc⟩` from `huni s (fun x hx => hs ▸ Submodule.subset_span hx)`. Use `⟨c, fun n hn => ?_⟩` and prove the remaining obligations. Establish `hle : Submodule.span A (s : Set D₂) ≤ (N₁.map f).comap (π ^ c • (LinearMap.id : D₂ →ₗ[A] D₂))`. Rewrite using `[Submodule.span_le]`. Introduce `x hx`.

Take `⟨n₁, h1, h2⟩` from `hc x hx`. Conclude with `⟨n₁, h1, by simpa using h2⟩`. Take `⟨n₁, h1, h2⟩` from `hle (hs ▸ hn)`. Conclude with `⟨n₁, h1, by simpa using h2⟩`.
-/
theorem cokernel_killed_holds : CokernelKilledByPower := by
  intro A _ D₁ D₂ _ _ _ _ f N₁ N₂ π l a hsurj hfN hl hdens hsat hfg
  classical
  have hsat' : ∀ (b : ℕ) (d : D₂), (∃ k : ℕ, π ^ k • (l ^ b • d) ∈ N₂) → ∃ k : ℕ, π ^ k • d ∈ N₂ := by
    intro b
    induction b with
    | zero => intro d h; simpa using h
    | succ b ih =>
      intro d ⟨k, hk⟩
      apply ih
      apply hsat
      exact ⟨k, by rwa [smul_smul l, ← pow_succ']⟩
  have hpt : ∀ n ∈ N₂, ∃ c : ℕ, ∃ n₁ ∈ N₁, f n₁ = π ^ c • n := by
    intro n hn
    obtain ⟨d, rfl⟩ := hsurj n
    obtain ⟨k, n₁, hn₁, d', hd⟩ := hdens d
    have h1 : l ^ a • f d' = π ^ k • f d - f n₁ := by
      rw [← map_smul, ← map_smul, hd, map_add]
      abel
    obtain ⟨j, hj⟩ := hsat' a (f d') ⟨0, by
      rw [pow_zero, one_smul, h1]
      exact N₂.sub_mem (N₂.smul_mem _ hn) (hfN _ hn₁)⟩
    obtain ⟨n₁', hn₁', hf'⟩ := hl _ hj
    refine ⟨j + k, π ^ j • n₁ + n₁', N₁.add_mem (N₁.smul_mem _ hn₁) hn₁', ?_⟩
    rw [map_add, map_smul, hf', pow_add, mul_smul, smul_comm (l ^ a), h1, smul_sub]
    abel
  have huni : ∀ s : Finset D₂, (∀ x ∈ s, x ∈ N₂) →
      ∃ c : ℕ, ∀ x ∈ s, ∃ n₁ ∈ N₁, f n₁ = π ^ c • x := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; exact ⟨0, by simp⟩
    | insert x s hx ih =>
      intro h
      obtain ⟨c, hc⟩ := ih (fun y hy => h y (Finset.mem_insert_of_mem hy))
      obtain ⟨c', n', hn', hf'⟩ := hpt x (h x (Finset.mem_insert_self _ _))
      refine ⟨c + c', ?_⟩
      intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hy
      · exact ⟨π ^ c • n', N₁.smul_mem _ hn', by rw [map_smul, hf', pow_add, mul_smul]⟩
      · obtain ⟨n, hn, hf⟩ := hc y hy
        exact ⟨π ^ c' • n, N₁.smul_mem _ hn, by rw [map_smul, hf, pow_add, mul_comm, mul_smul]⟩
  obtain ⟨s, hs⟩ := hfg
  obtain ⟨c, hc⟩ := huni s (fun x hx => hs ▸ Submodule.subset_span hx)
  refine ⟨c, fun n hn => ?_⟩
  have hle : Submodule.span A (s : Set D₂) ≤
      (N₁.map f).comap (π ^ c • (LinearMap.id : D₂ →ₗ[A] D₂)) := by
    rw [Submodule.span_le]
    intro x hx
    obtain ⟨n₁, h1, h2⟩ := hc x hx
    exact ⟨n₁, h1, by simpa using h2⟩
  obtain ⟨n₁, h1, h2⟩ := hle (hs ▸ hn)
  exact ⟨n₁, h1, by simpa using h2⟩

/- English proof (translation)
Introduce `O A _ _ _ B M D _ _ _ _ W y hQ x hx`. Conclude with `gammaStableOfGammaQUnit_holds O A B y D W.N W.γ hQ W.Q_bij W.γ_smul W.γ_N x hx`.
-/
theorem affineLine_localAcyclicity_of_strictHenselian_points : C3 := by
  intro O A _ _ _ B M D _ _ _ _ W y hQ x hx
  exact gammaStableOfGammaQUnit_holds O A B y D W.N W.γ hQ W.Q_bij W.γ_smul W.γ_N x hx

section Aeval

variable {O : Type} [CommRing O] {M M' : Type} [AddCommGroup M] [Module O M] [AddCommGroup M']
  [Module O M']

/- English proof (translation)
Establish `hpow : ∀ (n : ℕ) (d : M), d ∈ T → f ((g ^ n) d) = (g' ^ n) (f d)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro d _`. Simplify using the standard rewrite rules.

Consider the case `succ n ih`. Introduce `d hd`. Rewrite using `[pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih _ (hT d hd), h d hd]`. Proceed by induction on `q using Polynomial.induction_on' with`. Consider the case `add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]`.

Consider the case `monomial n a`. Simplify using `only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul, hpow n d hd]`.
-/
theorem aeval_intertwine_on (T : Submodule O M) (f : M →ₗ[O] M') (g : M →ₗ[O] M)
    (g' : M' →ₗ[O] M') (hT : ∀ d ∈ T, g d ∈ T) (h : ∀ d ∈ T, f (g d) = g' (f d))
    (q : Polynomial O) (d : M) (hd : d ∈ T) :
    f (Polynomial.aeval g q d) = Polynomial.aeval g' q (f d) := by
  have hpow : ∀ (n : ℕ) (d : M), d ∈ T → f ((g ^ n) d) = (g' ^ n) (f d) := by
    intro n
    induction n with
    | zero => intro d _; simp
    | succ n ih =>
      intro d hd
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih _ (hT d hd), h d hd]
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial n a =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      map_smul, hpow n d hd]

/- English proof (translation)
Establish `hpow : ∀ (n : ℕ) (d : M), d ∈ T → (g ^ n) d ∈ T`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro d hd`. Simplify using `using hd`.

Consider the case `succ n ih`. Introduce `d hd`. Rewrite using `[pow_succ, Module.End.mul_apply]`. Conclude with `ih _ (h d hd)`. Proceed by induction on `q using Polynomial.induction_on' with`.

Consider the case `add p q hp hq`. Simplify using `only [map_add, LinearMap.add_apply]`. Conclude with `T.add_mem hp hq`. Consider the case `monomial n a`. Simplify using `only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]`.

Conclude with `T.smul_mem _ (hpow n d hd)`.
-/
theorem aeval_mem (T : Submodule O M) (g : M →ₗ[O] M) (h : ∀ d ∈ T, g d ∈ T)
    (q : Polynomial O) (d : M) (hd : d ∈ T) : Polynomial.aeval g q d ∈ T := by
  have hpow : ∀ (n : ℕ) (d : M), d ∈ T → (g ^ n) d ∈ T := by
    intro n
    induction n with
    | zero => intro d hd; simpa using hd
    | succ n ih =>
      intro d hd
      rw [pow_succ, Module.End.mul_apply]
      exact ih _ (h d hd)
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, LinearMap.add_apply]
    exact T.add_mem hp hq
  | monomial n a =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact T.smul_mem _ (hpow n d hd)

end Aeval

/- English proof (translation)
Introduce `O A _ _ _ D _ _ _ _ N γ Q y p ρ P _ _ loc γl Ll Ly hloc hP5 hγ hLy hp d hd`. Set `NQ : Submodule O D` to `{ carrier := {d | ∃ k : ℕ, Q ^ k • d ∈ N} add_mem' := by`. Introduce and unpack `a b ⟨k, hk⟩ ⟨k', hk'⟩`. Use `⟨k + k', ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`.

Use `N.add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[pow_add, mul_comm, mul_smul]`. Conclude with `N.smul_mem _ hk`. Rewrite using `[pow_add, mul_smul]`. Conclude with `N.smul_mem _ hk'`.

Use the proof step `zero_mem' := ⟨0, by simp⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c a ⟨k, hk⟩`. Conclude with `⟨k, by rw [smul_comm]; exact N.smul_of_tower_mem c hk⟩ }`. Establish `h1 : Polynomial.aeval γ p d ∈ NQ` using `aeval_mem NQ γ (fun d hd => hγ d hd) p d ⟨y, hd⟩`.

Use `hP5 _ h1 fun x => ?_` and prove the remaining obligations. Rewrite using `[aeval_intertwine_on NQ (loc x) γ (γl x) (fun d hd => hγ d hd) (fun d hd => hloc x d hd) p d ⟨y, hd⟩]`. Conclude with `hp x _ (hLy d hd x)`.
-/
theorem consequence_two_global : GlobalWachProductConsequence := by
  intro O A _ _ _ D _ _ _ _ N γ Q y p ρ P _ _ loc γl Ll Ly hloc hP5 hγ hLy hp d hd
  let NQ : Submodule O D :=
    { carrier := {d | ∃ k : ℕ, Q ^ k • d ∈ N}
      add_mem' := by
        rintro a b ⟨k, hk⟩ ⟨k', hk'⟩
        refine ⟨k + k', ?_⟩
        rw [smul_add]
        refine N.add_mem ?_ ?_
        · rw [pow_add, mul_comm, mul_smul]; exact N.smul_mem _ hk
        · rw [pow_add, mul_smul]; exact N.smul_mem _ hk'
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c a ⟨k, hk⟩
        exact ⟨k, by rw [smul_comm]; exact N.smul_of_tower_mem c hk⟩ }
  have h1 : Polynomial.aeval γ p d ∈ NQ := aeval_mem NQ γ (fun d hd => hγ d hd) p d ⟨y, hd⟩
  refine hP5 _ h1 fun x => ?_
  rw [aeval_intertwine_on NQ (loc x) γ (γl x) (fun d hd => hγ d hd) (fun d hd => hloc x d hd) p d
    ⟨y, hd⟩]
  exact hp x _ (hLy d hd x)

end Formalism.RepresentationBoundsCohomology.N1
