import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.Away

variable {K : Type} [Field K] {n d : ℕ}

/- English proof (translation)
Simplify using `only [mon, AddMonoidAlgebra.single_pow, one_pow]`. Both sides reduce to the same expression.
-/
theorem mon_pow {M : AddSubmonoid (Gam n d)} (c : Gam n d) (hc : c ∈ M) (N : ℕ) :
    mon K c hc ^ N = mon K (N • c) (M.nsmul_mem hc N) := by
  simp only [mon, AddMonoidAlgebra.single_pow, one_pow]
  rfl

/- English proof (translation)
Introduce `x y hxy`. Simplify using `only [incl, AddMonoidAlgebra.mapDomainAlgHom_apply] at hxy`. Conclude with `AddMonoidAlgebra.mapDomain_injective (AddSubmonoid.inclusion_injective h) hxy`.
-/
theorem incl_injective {M M' : AddSubmonoid (Gam n d)} (h : M ≤ M') :
    Function.Injective (incl (K := K) h) := by
  intro x y hxy
  simp only [incl, AddMonoidAlgebra.mapDomainAlgHom_apply] at hxy
  exact AddMonoidAlgebra.mapDomain_injective (AddSubmonoid.inclusion_injective h) hxy

/- English proof (translation)
Proceed by induction on `z using AddMonoidAlgebra.induction_linear with`. Consider the case `zero => exact ⟨0, 0, by simp⟩`. Consider the case `add f g hf hg'`. Take `⟨N₁, a₁, h₁⟩` from `hf`. Take `⟨N₂, a₂, h₂⟩` from `hg'`.

Use `⟨N₁ + N₂, a₁ * mon K c hc ^ N₂ + a₂ * mon K c hc ^ N₁, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_mul, map_mul, ← h₁, ← h₂, pow_add, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `single m k`. Take `⟨N, hN⟩` from `hg m.1 m.2`.

Use `⟨N, AddMonoidAlgebra.single ⟨m.1 + N • c, hN⟩ k, ?_⟩` and prove the remaining obligations. Rewrite using `[mon_pow, incl_mon]`. Simplify using `only [mon, incl, AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.single_mul_single, mul_one]`. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem exists_mul_pow_eq_incl {M M' : AddSubmonoid (Gam n d)} (h : M ≤ M') (c : Gam n d) (hc : c ∈ M)
    (hg : ∀ g ∈ M', ∃ N : ℕ, g + N • c ∈ M) (z : Rg K M') :
    ∃ (N : ℕ) (a : Rg K M), z * incl h (mon K c hc ^ N) = incl h a := by
  induction z using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, 0, by simp⟩
  | add f g hf hg' =>
    obtain ⟨N₁, a₁, h₁⟩ := hf
    obtain ⟨N₂, a₂, h₂⟩ := hg'
    refine ⟨N₁ + N₂, a₁ * mon K c hc ^ N₂ + a₂ * mon K c hc ^ N₁, ?_⟩
    rw [map_add, map_mul, map_mul, ← h₁, ← h₂, pow_add, map_mul]
    ring
  | single m k =>
    obtain ⟨N, hN⟩ := hg m.1 m.2
    refine ⟨N, AddMonoidAlgebra.single ⟨m.1 + N • c, hN⟩ k, ?_⟩
    rw [mon_pow, incl_mon]
    simp only [mon, incl, AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.single_mul_single, mul_one]
    simp
    rfl

/- English proof (translation)
Introduce `K _ n d M M' h c hc hneg hg`. Use `letI := (incl (K := K) h).toRingHom.toAlgebra`. Establish `hal : ∀ x, algebraMap (Rg K M) (Rg K M') x = incl h x` using `fun _ => rfl`. Establish `hu : IsUnit (incl h (mon K c hc))`. Rewrite using `[incl_mon]`.

Use `IsUnit.of_mul_eq_one (mon K (-c) hneg) ?_` and prove the remaining obligations. Rewrite using `[mon_mul]`. Simplify using `only [mon, add_neg_cancel]`. Both sides reduce to the same expression. Use `(isLocalization_iff _ _).2 ⟨?_, fun z => ?_, fun {x y} hxy => ⟨1, ?_⟩⟩` and prove the remaining obligations.

Introduce and unpack `⟨_, N, rfl⟩`. Rewrite using `[hal, map_pow]`. Conclude with `hu.pow N`. Take `⟨N, a, ha⟩` from `exists_mul_pow_eq_incl h c hc hg z`. Conclude with `⟨(a, ⟨mon K c hc ^ N, N, rfl⟩), ha⟩`.

Rewrite using `[incl_injective h hxy]`.
-/
theorem isLocalization_away : ∀ {K : Type} [Field K] {n d : ℕ} {M M' : AddSubmonoid (Gam n d)} (h : M ≤ M') (c : Gam n d) (hc : c ∈ M), -c ∈ M' → (∀ g ∈ M', ∃ N : ℕ, g + N • c ∈ M) → letI := (incl (K := K) h).toRingHom.toAlgebra; IsLocalization.Away (mon K c hc) (Rg K M') := by
  intro K _ n d M M' h c hc hneg hg
  letI := (incl (K := K) h).toRingHom.toAlgebra
  have hal : ∀ x, algebraMap (Rg K M) (Rg K M') x = incl h x := fun _ => rfl
  have hu : IsUnit (incl h (mon K c hc)) := by
    rw [incl_mon]
    refine IsUnit.of_mul_eq_one (mon K (-c) hneg) ?_
    rw [mon_mul]
    simp only [mon, add_neg_cancel]
    rfl
  refine (isLocalization_iff _ _).2 ⟨?_, fun z => ?_, fun {x y} hxy => ⟨1, ?_⟩⟩
  · rintro ⟨_, N, rfl⟩
    rw [hal, map_pow]
    exact hu.pow N
  · obtain ⟨N, a, ha⟩ := exists_mul_pow_eq_incl h c hc hg z
    exact ⟨(a, ⟨mon K c hc ^ N, N, rfl⟩), ha⟩
  · rw [incl_injective h hxy]

end GlobalTheory.CompanionTheory.SurjectionOntoH4.Away
