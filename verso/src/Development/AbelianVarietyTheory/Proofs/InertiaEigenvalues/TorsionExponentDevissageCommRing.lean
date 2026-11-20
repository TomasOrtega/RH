import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
open Filter Topology

namespace GlobalTheory

/- English proof (translation)
Use `letI : TopologicalSpace M := (Ideal.span {a}).adicModuleTopology M`. Establish `hmem : ∀ (n : ℕ) (x : M), x ∈ ((Ideal.span {a}) ^ n • (⊤ : Submodule R M)) ↔ ∃ y : M, a ^ n • y = x`. Introduce `n x`. Rewrite using `[Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`. Simplify using the standard rewrite rules.

Establish `hb` using `fun x₀ : M => (@ModuleFilterBasis.toAddGroupFilterBasis R M _ (Ideal.span {a}).adic_basis.topology _ _ ((Ideal.span {a}).ringFilterBasis.moduleFilterBasis ((Ideal.span {a}).adic_module_basis M))).nhds_hasBasis x₀`. Rewrite using `[continuous_iff_continuousAt]`. Use `forall_congr' fun g₀ => ?_` and prove the remaining obligations. Use `((hb (f g₀)).tendsto_right_iff).trans ?_` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion.

Introduce `h n filter_upwards [h _ ⟨n, rfl⟩] with g hg`. Take `⟨y, hy, hy'⟩` from `hg`. Take `⟨z, rfl⟩` from `(hmem n y).1 hy`. Conclude with `⟨z, hy'.symm⟩`. Introduce and unpack `h _ ⟨n, rfl⟩ filter_upwards [h n] with g hg`.

Take `⟨z, hz⟩` from `hg`. Conclude with `⟨a ^ n • z, (hmem n _).2 ⟨z, rfl⟩, hz.symm⟩`.
-/
theorem continuous_adicModule_span_iff {R M G : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace G] (a : R) (f : G → M) :
    @Continuous G M _ ((Ideal.span {a}).adicModuleTopology M) f ↔
      ∀ (g₀ : G) (n : ℕ), ∀ᶠ g in 𝓝 g₀, ∃ y : M, f g = f g₀ + a ^ n • y := by
  letI : TopologicalSpace M := (Ideal.span {a}).adicModuleTopology M
  have hmem : ∀ (n : ℕ) (x : M), x ∈ ((Ideal.span {a}) ^ n • (⊤ : Submodule R M)) ↔
      ∃ y : M, a ^ n • y = x := by
    intro n x
    rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    simp
  have hb := fun x₀ : M => (@ModuleFilterBasis.toAddGroupFilterBasis R M _
    (Ideal.span {a}).adic_basis.topology _ _
    ((Ideal.span {a}).ringFilterBasis.moduleFilterBasis
      ((Ideal.span {a}).adic_module_basis M))).nhds_hasBasis x₀
  rw [continuous_iff_continuousAt]
  refine forall_congr' fun g₀ => ?_
  refine ((hb (f g₀)).tendsto_right_iff).trans ?_
  constructor
  · intro h n
    filter_upwards [h _ ⟨n, rfl⟩] with g hg
    obtain ⟨y, hy, hy'⟩ := hg
    obtain ⟨z, rfl⟩ := (hmem n y).1 hy
    exact ⟨z, hy'.symm⟩
  · rintro h _ ⟨n, rfl⟩
    filter_upwards [h n] with g hg
    obtain ⟨z, hz⟩ := hg
    exact ⟨a ^ n • z, (hmem n _).2 ⟨z, rfl⟩, hz.symm⟩

/- English proof (translation)
Introduce and unpack `f ⟨hfc, hf⟩ ⟨k, x, hx⟩`. Rewrite `hfc` using `[continuous_adicModule_span_iff]`. Simplify using `only [Pi.smul_apply] at hx`. Take `⟨z'', hz''⟩` from `h'' (fun g => p (f g)) ⟨by`. Rewrite using `[continuous_adicModule_span_iff]`.

Introduce `g₀ n`. Use `filter_upwards [hfc g₀ n] with g hg`. Take `⟨y, hy⟩` from `hg`. Conclude with `⟨p y, by rw [hy, map_add, map_smul]⟩,`. Use `fun g h => by simp only [hf, map_add, hpρ]⟩`.

Use the proof step `⟨k, p x, fun g => by rw [Pi.smul_apply, ← map_smul, hx, map_sub, hpρ]⟩`. Take `⟨z, rfl⟩` from `hp z''`. Simplify using `only [Pi.smul_apply] at hz''`. Establish `hex' : ∀ g, ∃ y, i y = r'' • f g - (ρ g z - z)` using `fun g => (hex _).1 (by rw [map_sub, map_smul, hz'', map_sub, hpρ, sub_self])`. Use `choose f' hf' using hex'`.

Establish `hcoc : @IsCoc R G X' _ _ _ _ _ ((Ideal.span {a}).adicModuleTopology X') ρ' f'`. Use `⟨?_, fun g h => hi ?_⟩` and prove the remaining obligations. Rewrite using `[continuous_adicModule_span_iff]`. Introduce `g₀ n`. Use `filter_upwards [hfc g₀ n, (continuous_adicModule_span_iff a _).1 (hc z) g₀ n] with g hg hg'`.

Take `⟨y, hy⟩` from `hg`. Take `⟨w, hw⟩` from `hg'`. Establish `h1 : i (f' g) = i (f' g₀) + a ^ n • (r'' • y - w)`. Rewrite using `[hf', hf', hy, hw]`. Use `module`.

Establish `h2 : p (r'' • y - w) = 0`. Apply `htf n` to reduce the goal to its premises. Use `congrArg p h1` as an intermediate fact. Rewrite `this` using `[map_add, hex.apply_apply_eq_zero, hex.apply_apply_eq_zero, zero_add, map_smul, eq_comm]`. Then use the resulting hypothesis. Take `⟨u, hu⟩` from `(hex _).1 h2`.

Conclude with `⟨u, hi (by rw [h1, map_add, map_smul, hu])⟩`. Rewrite using `[map_add, hiρ, hf', hf', hf', hf, map_mul]`. Simplify using `only [Module.End.mul_apply, map_sub, map_smul]`. Use `module`. Establish `hw : ∀ g, i (a ^ k • f' g) = ρ g (r'' • x - a ^ k • z) - (r'' • x - a ^ k • z)`.

Introduce `g`. Rewrite using `[map_smul, hf', smul_sub, smul_comm, hx]`. Simplify using `only [map_sub, map_smul]`. Use `module`. Take `⟨k', x₀, hx₀, hpx₀⟩` from `h0 (p (r'' • x - a ^ k • z)) (fun g => by`.

Rewrite using `[← hpρ, ← sub_eq_zero, ← map_sub, ← hw, hex.apply_apply_eq_zero])`. Take `⟨w', hw'⟩` from `(hex (a ^ k' • (r'' • x - a ^ k • z) - x₀)).1 (by rw [map_sub, map_smul, hpx₀, sub_self])`. Take `⟨u, hu⟩` from `h' f' hcoc ⟨k' + k, w', fun g => hi (by`. Rewrite using `[Pi.smul_apply, pow_add, mul_smul, map_smul, hw, map_sub i, hiρ, hw', map_sub (ρ g) _ x₀, hx₀, map_smul (ρ g) (a ^ k')]`. Use the proof step `module)⟩`.

Use `⟨i u + r' • z, fun g => ?_⟩` and prove the remaining obligations. Use `congrArg i (hu g)` as an intermediate fact. Rewrite `this` using `[Pi.smul_apply, map_smul, hf', map_sub, hiρ]`. Rewrite using `[Pi.smul_apply, map_add, map_smul]`. Take the linear combination `(norm := module) this`.
-/
theorem torsionExponent_devissage_commRing {R G X X' X'' : Type} [CommRing R] [Group G] [TopologicalSpace G]
    [AddCommGroup X] [Module R X] [AddCommGroup X'] [Module R X'] [AddCommGroup X''] [Module R X'']
    (a : R) (htf : ∀ (n : ℕ) (z : X''), a ^ n • z = 0 → z = 0)
    (ρ : Representation R G X) (ρ' : Representation R G X') (ρ'' : Representation R G X'')
    (i : X' →ₗ[R] X) (p : X →ₗ[R] X'') (r' r'' : R)
    (hi : Function.Injective i) (hp : Function.Surjective p) (hex : Function.Exact i p)
    (hiρ : ∀ g x, i (ρ' g x) = ρ g (i x)) (hpρ : ∀ g x, p (ρ g x) = ρ'' g (p x))
    (hc : ∀ x, @Continuous G X _ ((Ideal.span {a}).adicModuleTopology X) fun g => ρ g x)
    (h0 : ∀ z, (∀ g, ρ'' g z = z) → ∃ (k : ℕ) (x : X), (∀ g, ρ g x = x) ∧ p x = a ^ k • z)
    (h' : @TorsKilledBy R G X' _ _ _ _ _ ((Ideal.span {a}).adicModuleTopology X') ρ' a r')
    (h'' : @TorsKilledBy R G X'' _ _ _ _ _ ((Ideal.span {a}).adicModuleTopology X'') ρ'' a r'') :
    @TorsKilledBy R G X _ _ _ _ _ ((Ideal.span {a}).adicModuleTopology X) ρ a (r' * r'') := by
  rintro f ⟨hfc, hf⟩ ⟨k, x, hx⟩
  rw [continuous_adicModule_span_iff] at hfc
  simp only [Pi.smul_apply] at hx

  obtain ⟨z'', hz''⟩ := h'' (fun g => p (f g)) ⟨by
      rw [continuous_adicModule_span_iff]
      intro g₀ n
      filter_upwards [hfc g₀ n] with g hg
      obtain ⟨y, hy⟩ := hg
      exact ⟨p y, by rw [hy, map_add, map_smul]⟩,
    fun g h => by simp only [hf, map_add, hpρ]⟩
    ⟨k, p x, fun g => by rw [Pi.smul_apply, ← map_smul, hx, map_sub, hpρ]⟩
  obtain ⟨z, rfl⟩ := hp z''
  simp only [Pi.smul_apply] at hz''
  have hex' : ∀ g, ∃ y, i y = r'' • f g - (ρ g z - z) := fun g =>
    (hex _).1 (by rw [map_sub, map_smul, hz'', map_sub, hpρ, sub_self])
  choose f' hf' using hex'
  have hcoc : @IsCoc R G X' _ _ _ _ _ ((Ideal.span {a}).adicModuleTopology X') ρ' f' := by
    refine ⟨?_, fun g h => hi ?_⟩
    · rw [continuous_adicModule_span_iff]
      intro g₀ n
      filter_upwards [hfc g₀ n, (continuous_adicModule_span_iff a _).1 (hc z) g₀ n] with g hg hg'
      obtain ⟨y, hy⟩ := hg
      obtain ⟨w, hw⟩ := hg'
      have h1 : i (f' g) = i (f' g₀) + a ^ n • (r'' • y - w) := by
        rw [hf', hf', hy, hw]; module
      have h2 : p (r'' • y - w) = 0 := by
        apply htf n
        have := congrArg p h1
        rwa [map_add, hex.apply_apply_eq_zero, hex.apply_apply_eq_zero, zero_add, map_smul,
          eq_comm] at this
      obtain ⟨u, hu⟩ := (hex _).1 h2
      exact ⟨u, hi (by rw [h1, map_add, map_smul, hu])⟩
    · rw [map_add, hiρ, hf', hf', hf', hf, map_mul]
      simp only [Module.End.mul_apply, map_sub, map_smul]
      module

  have hw : ∀ g, i (a ^ k • f' g) = ρ g (r'' • x - a ^ k • z) - (r'' • x - a ^ k • z) := by
    intro g
    rw [map_smul, hf', smul_sub, smul_comm, hx]
    simp only [map_sub, map_smul]
    module
  obtain ⟨k', x₀, hx₀, hpx₀⟩ := h0 (p (r'' • x - a ^ k • z)) (fun g => by
    rw [← hpρ, ← sub_eq_zero, ← map_sub, ← hw, hex.apply_apply_eq_zero])
  obtain ⟨w', hw'⟩ := (hex (a ^ k' • (r'' • x - a ^ k • z) - x₀)).1
    (by rw [map_sub, map_smul, hpx₀, sub_self])
  obtain ⟨u, hu⟩ := h' f' hcoc ⟨k' + k, w', fun g => hi (by
    rw [Pi.smul_apply, pow_add, mul_smul, map_smul, hw, map_sub i, hiρ, hw', map_sub (ρ g) _ x₀,
      hx₀, map_smul (ρ g) (a ^ k')]
    module)⟩
  refine ⟨i u + r' • z, fun g => ?_⟩
  have := congrArg i (hu g)
  rw [Pi.smul_apply, map_smul, hf', map_sub, hiρ] at this
  rw [Pi.smul_apply, map_add, map_smul]
  linear_combination (norm := module) this

/- English proof (translation)
Introduce `l _ G _ _ _ _ _ X _ _ _ _ X' _ _ _ _ X'' _ _ _ _ ρ ρ' ρ'' i p c' c''`. Introduce `hi hp hex hiρ hpρ hc h0 h' h''`. Rewrite using `[pow_add]`. Use `torsionExponent_devissage_commRing (l : ℤ_[l]) ?_ ρ ρ' ρ'' i p _ _ hi hp hex hiρ hpρ hc h0 h' h''` and prove the remaining obligations. Introduce `n z hz`.

Establish `hl : ((l : ℤ_[l]) ^ n) ≠ 0` using `pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)`. Conclude with `(NoZeroSMulDivisors.eq_zero_or_eq_zero_of_smul_eq_zero hz).resolve_left hl`.
-/
theorem torsKilledBy_devissage : ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] [NoZeroSMulDivisors ℤ_[l] X] [IsAdicComplete (Ideal.span {(l : ℤ_[l])}) X] (X' : Type) [AddCommGroup X'] [Module ℤ_[l] X'] [NoZeroSMulDivisors ℤ_[l] X'] [IsAdicComplete (Ideal.span {(l : ℤ_[l])}) X'] (X'' : Type) [AddCommGroup X''] [Module ℤ_[l] X''] [NoZeroSMulDivisors ℤ_[l] X''] [IsAdicComplete (Ideal.span {(l : ℤ_[l])}) X''] (ρ : Representation ℤ_[l] G X) (ρ' : Representation ℤ_[l] G X') (ρ'' : Representation ℤ_[l] G X'') (i : X' →ₗ[ℤ_[l]] X) (p : X →ₗ[ℤ_[l]] X'') (c' c'' : ℕ), letI : TopologicalSpace X := (Ideal.span {(l : ℤ_[l])}).adicModuleTopology X; letI : TopologicalSpace X' := (Ideal.span {(l : ℤ_[l])}).adicModuleTopology X'; letI : TopologicalSpace X'' := (Ideal.span {(l : ℤ_[l])}).adicModuleTopology X''; Function.Injective i → Function.Surjective p → Function.Exact i p → (∀ g x, i (ρ' g x) = ρ g (i x)) → (∀ g x, p (ρ g x) = ρ'' g (p x)) → (∀ x, Continuous fun g => ρ g x) → (∀ z, (∀ g, ρ'' g z = z) → ∃ (k : ℕ) (x : X), (∀ g, ρ g x = x) ∧ p x = (l : ℤ_[l]) ^ k • z) → TorsKilledBy ρ' (l : ℤ_[l]) ((l : ℤ_[l]) ^ c') → TorsKilledBy ρ'' (l : ℤ_[l]) ((l : ℤ_[l]) ^ c'') → TorsKilledBy ρ (l : ℤ_[l]) ((l : ℤ_[l]) ^ (c' + c'')) := by
  intro l _ G _ _ _ _ _ X _ _ _ _ X' _ _ _ _ X'' _ _ _ _ ρ ρ' ρ'' i p c' c''
  intro hi hp hex hiρ hpρ hc h0 h' h''
  rw [pow_add]
  refine torsionExponent_devissage_commRing (l : ℤ_[l]) ?_ ρ ρ' ρ'' i p _ _ hi hp hex hiρ hpρ hc h0 h' h''
  intro n z hz
  have hl : ((l : ℤ_[l]) ^ n) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  exact (NoZeroSMulDivisors.eq_zero_or_eq_zero_of_smul_eq_zero hz).resolve_left hl

end GlobalTheory
