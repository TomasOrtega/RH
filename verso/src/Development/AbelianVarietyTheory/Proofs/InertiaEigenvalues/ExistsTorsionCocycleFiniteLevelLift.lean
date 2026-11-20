import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.TorsionLevel

/- English proof (translation)
Introduce `l _ K LL _ _ _ O _ _ hgood A' LA' ϖ hϖ c hc hcB r hr n hn hI'`. Take `⟨⟨_, _, _⟩, -⟩` from `hgood`. Use `set p0 : LL := algebraMap O LL ϖ with hp0`. Establish `hp0ne : p0 ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective O LL)).mpr hϖ.ne_zero`. Establish `memI : ∀ x : ↥LA'.T, x ∈ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA'.T) ↔ ∃ y : ↥LA'.T, ϖ ^ n • y = x`.

Introduce `x`. Rewrite using `[Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`. Simplify using the standard rewrite rules. Establish `smulp : ∀ (j : ℕ) (w : A'.V), p0 ^ j • w = ϖ ^ j • w`. Introduce `j w`.

Rewrite using `[hp0, ← map_pow, algebraMap_smul]`. Establish `hmem : ∀ g, p0 ^ n • liftD LA' (c g) ∈ LA'.T`. Introduce `g`. Establish `: p0 ^ n • liftD LA' (c g) = ϖ ^ (n - r) • (p0 ^ r • liftD LA' (c g))`. Rewrite using `[← smulp, smul_smul, ← pow_add, Nat.sub_add_cancel hn]`.

Rewrite using `[this]`. Conclude with `LA'.T.smul_mem _ (hr g)`. Establish `hlift : ∀ v : A'.V ⧸ LA'.T, Submodule.Quotient.mk (p` using `LA'.T) (liftD LA' v) = v := fun v => (Submodule.Quotient.mk_surjective _ v).choose_spec`. Set `F : A'.V ⧸ LA'.T → ↥LA'.T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA'.T)` to `fun v => if h : p0 ^ n • liftD LA' v ∈ LA'.T then Submodule.Quotient.mk ⟨_, h⟩ else 0`. Establish `hc' : ∀ g, (F ∘ c) g = Submodule.Quotient.mk ⟨_, hmem g⟩`.

Introduce `g`. Simplify using `only [F, Function.comp_apply, dif_pos (hmem g)]`. Use `⟨fun g => Submodule.Quotient.mk ⟨_, hmem g⟩, ⟨?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Establish `: (fun g => (Submodule.Quotient.mk ⟨_, hmem g⟩ : ↥LA'.T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA'.T))) = F ∘ c`. Use function extensionality and compare the values at `fun g => (hc' g).symm`.

Rewrite using `[this]`. Conclude with `hc.1.comp F`. Introduce `g h`. Simplify using `only`. Rewrite using `[actQ, Submodule.mapQ_apply, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq, memI]`.

Establish `hd : liftD LA' (c (g * h)) - liftD LA' (c g) - A'.ρ g (liftD LA' (c h)) ∈ LA'.T`. Rewrite using `[← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_sub, hlift, hlift, hc.2 g h]`. Establish `: Submodule.Quotient.mk (p` using `LA'.T) (A'.ρ g (liftD LA' (c h))) = actD LA' g (c h) := by conv_rhs => rw [← hlift (c h)]`. Both sides reduce to the same expression. Rewrite using `[this]`.

Normalize the expressions using the abelian group laws. Use `⟨⟨_, hd⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.coe_smul, ← smulp]`. Use `show p0 ^ n • (liftD LA' (c (g * h)) - liftD LA' (c g) - A'.ρ g (liftD LA' (c h))) = p0 ^ n • liftD LA' (c (g * h)) - (p0 ^ n • liftD LA' (c g) + A'.ρ g (p0 ^ n • liftD LA' (c h)))`. Rewrite using `[map_smul, smul_sub, smul_sub]`.

Normalize the expressions using the abelian group laws. Introduce and unpack `⟨x, hx⟩`. Apply `hcB` to reduce the goal to its premises. Take `⟨t, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Use `⟨Submodule.Quotient.mk ((p0 ^ n)⁻¹ • (t : A'.V)), funext fun g => ?_⟩` and prove the remaining obligations.

Establish `hxg` using `congrFun hx g`. Simplify using `only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply] at hxg ⊢`. Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk (actT LA' g t) - Submodule.Quotient.mk t = _ at hxg`. Rewrite `hxg` using `[← Submodule.Quotient.mk_sub, Submodule.Quotient.eq, memI]`. Take `⟨s, hs⟩` from `hxg`.

Establish `key : A'.ρ g (t : A'.V) - t - p0 ^ n • liftD LA' (c g) = p0 ^ n • (s : A'.V)`. Rewrite using `[smulp n (s : A'.V)]`. Use `congrArg Subtype.val hs` as an intermediate fact. Rewrite `this` using `[Submodule.coe_smul]`. Rewrite using `[this]`.

Both sides reduce to the same expression. Use `conv_rhs => rw [← hlift (c g)]`. Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk (p := LA'.T) (A'.ρ g ((p0 ^ n)⁻¹ • (t : A'.V))) - _ = _`. Rewrite using `[← Submodule.Quotient.mk_sub, Submodule.Quotient.eq]`. Establish `: (A'.ρ g) ((p0 ^ n)⁻¹ • (t : A'.V)) - (p0 ^ n)⁻¹ • (t : A'.V) - liftD LA' (c g) = s`.

Apply `smul_right_injective A'.V (pow_ne_zero n hp0ne)` to reduce the goal to its premises. Simplify using `only [map_smul, ← smul_sub]`. Rewrite using `[smul_sub, smul_inv_smul₀ (pow_ne_zero n hp0ne), key]`. Rewrite using `[this]`. Conclude with `s.2`.

Introduce `h`. Establish `key : ∀ x q : ↥LA'.T, Submodule.Quotient.mk (p` using `(Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA'.T)) q = Submodule.Quotient.mk x → ∃ t ∈ LA'.T, (q : A'.V) = (x : A'.V) + p0 ^ n • t := by`. Introduce `x q hq`. Rewrite `hq` using `[Submodule.Quotient.eq, memI]`. Take `⟨y, hy⟩` from `hq`.

Use `⟨y, y.2, ?_⟩` and prove the remaining obligations. Rewrite using `[smulp n (y : A'.V), ← Submodule.coe_smul, hy, Submodule.coe_sub]`. Normalize the expressions using the abelian group laws. Conclude with `key _ _ (Submodule.Quotient.mk_surjective _ _).choose_spec`.
-/
theorem exists_cocycle_level : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A' : GRep ↥(GK K) ℚ_[l] LL O) (LA' : Lattice (O := O) A'.ρ) (ϖ : O), Irreducible ϖ → ∀ c ∈ divisibleCocycles LA', c ∉ BD LA' → ∀ r : ℕ, (∀ g, (algebraMap O LL ϖ) ^ r • liftD LA' (c g) ∈ LA'.T) → ∀ n : ℕ, r ≤ n → ∀ hI' : StableSub LA' (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA'.T), ∃ c' ∈ quotientCocycles LA' _ hI', c' ∉ BQ LA' _ hI' ∧ ∀ h, ∃ t ∈ LA'.T, Formalism.MainNotions.LocalSituation.liftQ LA' _ (c' h) = (algebraMap O LL ϖ) ^ n • liftD LA' (c h) + (algebraMap O LL ϖ) ^ n • t := by
  intro l _ K LL _ _ _ O _ _ hgood A' LA' ϖ hϖ c hc hcB r hr n hn hI'
  classical
  obtain ⟨⟨_, _, _⟩, -⟩ := hgood
  set p0 : LL := algebraMap O LL ϖ with hp0
  have hp0ne : p0 ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O LL)).mpr hϖ.ne_zero
  have memI : ∀ x : ↥LA'.T, x ∈ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA'.T) ↔
      ∃ y : ↥LA'.T, ϖ ^ n • y = x := by
    intro x
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    simp
  have smulp : ∀ (j : ℕ) (w : A'.V), p0 ^ j • w = ϖ ^ j • w := by
    intro j w; rw [hp0, ← map_pow, algebraMap_smul]
  have hmem : ∀ g, p0 ^ n • liftD LA' (c g) ∈ LA'.T := by
    intro g
    have : p0 ^ n • liftD LA' (c g) = ϖ ^ (n - r) • (p0 ^ r • liftD LA' (c g)) := by
      rw [← smulp, smul_smul, ← pow_add, Nat.sub_add_cancel hn]
    rw [this]; exact LA'.T.smul_mem _ (hr g)
  have hlift : ∀ v : A'.V ⧸ LA'.T, Submodule.Quotient.mk (p := LA'.T) (liftD LA' v) = v :=
    fun v => (Submodule.Quotient.mk_surjective _ v).choose_spec
  let F : A'.V ⧸ LA'.T → ↥LA'.T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA'.T) := fun v =>
    if h : p0 ^ n • liftD LA' v ∈ LA'.T then Submodule.Quotient.mk ⟨_, h⟩ else 0
  have hc' : ∀ g, (F ∘ c) g = Submodule.Quotient.mk ⟨_, hmem g⟩ := by
    intro g; simp only [F, Function.comp_apply, dif_pos (hmem g)]
  refine ⟨fun g => Submodule.Quotient.mk ⟨_, hmem g⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · have : (fun g => (Submodule.Quotient.mk ⟨_, hmem g⟩ :
        ↥LA'.T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA'.T))) = F ∘ c :=
      funext fun g => (hc' g).symm
    rw [this]; exact hc.1.comp F
  · intro g h
    simp only
    rw [actQ, Submodule.mapQ_apply, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq, memI]
    have hd : liftD LA' (c (g * h)) - liftD LA' (c g) - A'.ρ g (liftD LA' (c h)) ∈ LA'.T := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_sub,
        hlift, hlift, hc.2 g h]
      have : Submodule.Quotient.mk (p := LA'.T) (A'.ρ g (liftD LA' (c h))) = actD LA' g (c h) := by
        conv_rhs => rw [← hlift (c h)]
        rfl
      rw [this]; abel
    refine ⟨⟨_, hd⟩, Subtype.ext ?_⟩
    rw [Submodule.coe_smul, ← smulp]
    show p0 ^ n • (liftD LA' (c (g * h)) - liftD LA' (c g) - A'.ρ g (liftD LA' (c h))) =
      p0 ^ n • liftD LA' (c (g * h)) - (p0 ^ n • liftD LA' (c g) + A'.ρ g (p0 ^ n • liftD LA' (c h)))
    rw [map_smul, smul_sub, smul_sub]; abel
  · rintro ⟨x, hx⟩
    apply hcB
    obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine ⟨Submodule.Quotient.mk ((p0 ^ n)⁻¹ • (t : A'.V)), funext fun g => ?_⟩
    have hxg := congrFun hx g
    simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply] at hxg ⊢
    change Submodule.Quotient.mk (actT LA' g t) - Submodule.Quotient.mk t = _ at hxg
    rw [← Submodule.Quotient.mk_sub, Submodule.Quotient.eq, memI] at hxg
    obtain ⟨s, hs⟩ := hxg
    have key : A'.ρ g (t : A'.V) - t - p0 ^ n • liftD LA' (c g) = p0 ^ n • (s : A'.V) := by
      rw [smulp n (s : A'.V)]
      have := congrArg Subtype.val hs
      rw [Submodule.coe_smul] at this
      rw [this]; rfl
    conv_rhs => rw [← hlift (c g)]
    change Submodule.Quotient.mk (p := LA'.T) (A'.ρ g ((p0 ^ n)⁻¹ • (t : A'.V))) - _ = _
    rw [← Submodule.Quotient.mk_sub, Submodule.Quotient.eq]
    have : (A'.ρ g) ((p0 ^ n)⁻¹ • (t : A'.V)) - (p0 ^ n)⁻¹ • (t : A'.V) - liftD LA' (c g) = s := by
      apply smul_right_injective A'.V (pow_ne_zero n hp0ne)
      simp only [map_smul, ← smul_sub]
      rw [smul_sub, smul_inv_smul₀ (pow_ne_zero n hp0ne), key]
    rw [this]; exact s.2
  · intro h
    have key : ∀ x q : ↥LA'.T,
        Submodule.Quotient.mk (p := (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA'.T)) q =
          Submodule.Quotient.mk x → ∃ t ∈ LA'.T, (q : A'.V) = (x : A'.V) + p0 ^ n • t := by
      intro x q hq
      rw [Submodule.Quotient.eq, memI] at hq
      obtain ⟨y, hy⟩ := hq
      refine ⟨y, y.2, ?_⟩
      rw [smulp n (y : A'.V), ← Submodule.coe_smul, hy, Submodule.coe_sub]; abel
    exact key _ _ (Submodule.Quotient.mk_surjective _ _).choose_spec

end GlobalTheory.TorsionLevel
