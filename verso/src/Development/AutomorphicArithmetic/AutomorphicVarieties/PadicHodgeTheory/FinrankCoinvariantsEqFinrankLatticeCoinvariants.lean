import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TateDefs
import ReciprocityTheory.GroupCohomology.ImportsAlt
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

/- English proof (translation)
Introduce `l _ G T V _ _ _ _ _ _ _ χ ρ ρT j hj hρ hs`. Use `set N := coSub ((Units.map (algebraMap ℤ_[l] ℚ_[l] : ℤ_[l] →* ℚ_[l])).comp χ) ρ with hN`. Establish `hl : ∀ m : ℕ, (l : ℤ_[l]) ^ m ∈ nonZeroDivisors ℤ_[l]` using `fun m => mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero))`. Establish `hgen : ∀ g x, j (ρT g x - ((χ g : ℤ_[l]ˣ) : ℤ_[l]) • x) = ρ g (j x) - ((((Units.map (algebraMap ℤ_[l] ℚ_[l] : ℤ_[l] →* ℚ_[l])).comp χ) g : ℚ_[l]ˣ) : ℚ_[l]) • j x`. Introduce `g x`.

Rewrite using `[map_sub, hρ, map_smul, ← algebraMap_smul ℚ_[l] ((χ g : ℤ_[l]ˣ) : ℤ_[l]) (j x)]`. Both sides reduce to the same expression. Establish `hρs : ∀ g (c : ℤ_[l]) (v : V), ρ g (c • v) = c • ρ g v` using `fun g c v => by`. Rewrite using `[← algebraMap_smul ℚ_[l] c v, map_smul, algebraMap_smul]`. Set `q : V →ₗ[ℤ_[l]] (V ⧸ N)` to `N.mkQ.restrictScalars ℤ_[l]`.

Establish `hle : coSub χ ρT ≤ LinearMap.ker (q ∘ₗ j)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g, x, rfl⟩`. Express the relevant statement in the definitionally equal form `N.mkQ (j _) = 0`. Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hgen]`.

Conclude with `Submodule.subset_span ⟨g, j x, rfl⟩`. Set `f : (T ⧸ coSub χ ρT) →ₗ[ℤ_[l]] (V ⧸ N)` to `(coSub χ ρT).liftQ (q ∘ₗ j) hle`. Establish `key : ∀ v ∈ N, ∃ c ∈ nonZeroDivisors ℤ_[l], c • v ∈ (coSub χ ρT).map j`. Introduce `v hv`. Proceed by induction on `hv using Submodule.span_induction with`.

Consider the case `mem y hy`. Take `⟨g, x, rfl⟩` from `hy`. Take `⟨m, t, ht⟩` from `hs x`. Use `⟨_, hl m, ρT g t - ((χ g : ℤ_[l]ˣ) : ℤ_[l]) • t, Submodule.subset_span ⟨g, t, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hgen, ht, hρs, smul_sub, smul_comm]`.

Consider the case `zero => exact ⟨1, one_mem _, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨c, hc, hx⟩` from `hx`. Take `⟨d, hd, hy⟩` from `hy`. Use `⟨c * d, mul_mem hc hd, ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_add]`. Use `add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`. Conclude with `Submodule.smul_mem _ _ hx`. Rewrite using `[mul_smul]`.

Conclude with `Submodule.smul_mem _ _ hy`. Consider the case `smul a x _ hx`. Take `⟨c, hc, hx⟩` from `hx`. Take `⟨⟨r, s⟩, hrs⟩` from `IsLocalization.surj (nonZeroDivisors ℤ_[l]) a`. Use `⟨c * s, mul_mem hc s.2, ?_⟩` and prove the remaining obligations.

Establish `: (s : ℤ_[l]) • a • x = r • x`. Rewrite using `[← algebraMap_smul ℚ_[l] (s : ℤ_[l]), smul_smul, mul_comm, hrs, algebraMap_smul]`. Rewrite using `[mul_smul, this, smul_comm]`. Conclude with `Submodule.smul_mem _ _ hx`. Use `haveI : IsLocalizedModule (nonZeroDivisors ℤ_[l]) f := by`.

Use `⟨(isLocalizedModule_id (nonZeroDivisors ℤ_[l]) (V ⧸ N) ℚ_[l]).map_units, ?_, ?_⟩` and prove the remaining obligations. Introduce `y`. Take `⟨v, rfl⟩` from `N.mkQ_surjective y`. Take `⟨m, t, ht⟩` from `hs v`. Use `⟨⟨Submodule.Quotient.mk t, ⟨_, hl m⟩⟩, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(l : ℤ_[l]) ^ m • q v = q (j t)`. Rewrite using `[ht, map_smul]`. Introduce `x y h`. Take `⟨x, rfl⟩` from `(coSub χ ρT).mkQ_surjective x`. Take `⟨y, rfl⟩` from `(coSub χ ρT).mkQ_surjective y`.

Establish `h' : j x - j y ∈ N` using `(Submodule.Quotient.eq N).1 h`. Take `⟨c, hc, t, ht, e⟩` from `key _ h'`. Rewrite `e` using `[← map_sub, ← map_smul]`. Take `rfl` from `hj e`. Use `⟨⟨c, hc⟩, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `c • (coSub χ ρT).mkQ x = c • (coSub χ ρT).mkQ y`. Rewrite using `[← map_smul, ← map_smul]`. Use `(Submodule.Quotient.eq _).2 ?_` and prove the remaining obligations. Rewrite using `[← smul_sub]`. Conclude with `ht`.

Rewrite using `[IsLocalization.finrank_eq ℚ_[l] (nonZeroDivisors ℤ_[l]) le_rfl, IsLocalizedModule.finrank_eq (nonZeroDivisors ℤ_[l]) f le_rfl]`.
-/
theorem UpperTheory.finrank_coinvariants_eq_finrank_lattice_coinvariants :
    ∀ {l : ℕ} [Fact l.Prime] {G T V : Type} [Group G] [AddCommGroup T] [Module ℤ_[l] T] [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] (χ : G →* ℤ_[l]ˣ) (ρ : Representation ℚ_[l] G V) (ρT : Representation ℤ_[l] G T) (j : T →ₗ[ℤ_[l]] V), Function.Injective j → (∀ g x, j (ρT g x) = ρ g (j x)) → (∀ y : V, ∃ m : ℕ, (l : ℤ_[l]) ^ m • y ∈ LinearMap.range j) → finrank ℚ_[l] (V ⧸ coSub ((Units.map (algebraMap ℤ_[l] ℚ_[l] : ℤ_[l] →* ℚ_[l])).comp χ) ρ) = finrank ℤ_[l] (T ⧸ coSub χ ρT) := by
  intro l _ G T V _ _ _ _ _ _ _ χ ρ ρT j hj hρ hs
  set N := coSub ((Units.map (algebraMap ℤ_[l] ℚ_[l] : ℤ_[l] →* ℚ_[l])).comp χ) ρ with hN
  have hl : ∀ m : ℕ, (l : ℤ_[l]) ^ m ∈ nonZeroDivisors ℤ_[l] := fun m =>
    mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero))
  have hgen : ∀ g x, j (ρT g x - ((χ g : ℤ_[l]ˣ) : ℤ_[l]) • x) =
      ρ g (j x) - ((((Units.map (algebraMap ℤ_[l] ℚ_[l] : ℤ_[l] →* ℚ_[l])).comp χ) g : ℚ_[l]ˣ) : ℚ_[l]) • j x := by
    intro g x
    rw [map_sub, hρ, map_smul, ← algebraMap_smul ℚ_[l] ((χ g : ℤ_[l]ˣ) : ℤ_[l]) (j x)]
    rfl
  have hρs : ∀ g (c : ℤ_[l]) (v : V), ρ g (c • v) = c • ρ g v := fun g c v => by
    rw [← algebraMap_smul ℚ_[l] c v, map_smul, algebraMap_smul]
  let q : V →ₗ[ℤ_[l]] (V ⧸ N) := N.mkQ.restrictScalars ℤ_[l]
  have hle : coSub χ ρT ≤ LinearMap.ker (q ∘ₗ j) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, x, rfl⟩
    change N.mkQ (j _) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hgen]
    exact Submodule.subset_span ⟨g, j x, rfl⟩
  let f : (T ⧸ coSub χ ρT) →ₗ[ℤ_[l]] (V ⧸ N) := (coSub χ ρT).liftQ (q ∘ₗ j) hle
  have key : ∀ v ∈ N, ∃ c ∈ nonZeroDivisors ℤ_[l], c • v ∈ (coSub χ ρT).map j := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, x, rfl⟩ := hy
      obtain ⟨m, t, ht⟩ := hs x
      refine ⟨_, hl m, ρT g t - ((χ g : ℤ_[l]ˣ) : ℤ_[l]) • t, Submodule.subset_span ⟨g, t, rfl⟩, ?_⟩
      rw [hgen, ht, hρs, smul_sub, smul_comm]
    | zero => exact ⟨1, one_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, hx⟩ := hx
      obtain ⟨d, hd, hy⟩ := hy
      refine ⟨c * d, mul_mem hc hd, ?_⟩
      rw [smul_add]
      refine add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hx
      · rw [mul_smul]; exact Submodule.smul_mem _ _ hy
    | smul a x _ hx =>
      obtain ⟨c, hc, hx⟩ := hx
      obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (nonZeroDivisors ℤ_[l]) a
      refine ⟨c * s, mul_mem hc s.2, ?_⟩
      have : (s : ℤ_[l]) • a • x = r • x := by
        rw [← algebraMap_smul ℚ_[l] (s : ℤ_[l]), smul_smul, mul_comm, hrs, algebraMap_smul]
      rw [mul_smul, this, smul_comm]
      exact Submodule.smul_mem _ _ hx
  haveI : IsLocalizedModule (nonZeroDivisors ℤ_[l]) f := by
    refine ⟨(isLocalizedModule_id (nonZeroDivisors ℤ_[l]) (V ⧸ N) ℚ_[l]).map_units, ?_, ?_⟩
    · intro y
      obtain ⟨v, rfl⟩ := N.mkQ_surjective y
      obtain ⟨m, t, ht⟩ := hs v
      refine ⟨⟨Submodule.Quotient.mk t, ⟨_, hl m⟩⟩, ?_⟩
      change (l : ℤ_[l]) ^ m • q v = q (j t)
      rw [ht, map_smul]
    · intro x y h
      obtain ⟨x, rfl⟩ := (coSub χ ρT).mkQ_surjective x
      obtain ⟨y, rfl⟩ := (coSub χ ρT).mkQ_surjective y
      have h' : j x - j y ∈ N := (Submodule.Quotient.eq N).1 h
      obtain ⟨c, hc, t, ht, e⟩ := key _ h'
      rw [← map_sub, ← map_smul] at e
      obtain rfl := hj e
      refine ⟨⟨c, hc⟩, ?_⟩
      change c • (coSub χ ρT).mkQ x = c • (coSub χ ρT).mkQ y
      rw [← map_smul, ← map_smul]
      refine (Submodule.Quotient.eq _).2 ?_
      rw [← smul_sub]; exact ht
  rw [IsLocalization.finrank_eq ℚ_[l] (nonZeroDivisors ℤ_[l]) le_rfl,
    IsLocalizedModule.finrank_eq (nonZeroDivisors ℤ_[l]) f le_rfl]
