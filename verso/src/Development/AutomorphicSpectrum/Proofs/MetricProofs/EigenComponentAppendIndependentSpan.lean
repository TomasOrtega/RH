import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIsChart
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicSublatticeCovolumePositiveStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsEigenComponentPolynomial

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.EigIndep

/- English proof (translation)
Introduce `E _ _ V _ _ ρ s₀ I₀ r k v q hF _ hq hli l hl`. Take `⟨c, hc⟩` from `EigCoef.eigComp_eq_combination E s₀`. Take `⟨h1, h2, h3⟩` from `hc V ρ`. Set `π : V →ₗ[ℂ] V` to `∑ a ∈ c.support, c a • ρ a`. Establish `hπ : ∀ x, π x = eigComp ρ s₀ x`.

Introduce `x`. Rewrite using `[h1 x]`. Simplify using `[π, LinearMap.sum_apply]`. Establish `hact : ∀ (b : 𝓞 E) x, π (ρ b x) = s₀ b • π x`. Introduce `b x`.

Establish `e : π (ρ b x) = ρ b (π x)`. Simplify using `only [π, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `congr 1`. Establish `: ρ a * ρ b = ρ b * ρ a` using `by rw [← map_mul, ← map_mul, mul_comm]`.

Conclude with `LinearMap.congr_fun this x`. Rewrite using `[e, EigCoef.mem_eigSp_iff.1 (hπ x ▸ h2 x) b]`. Set `W : Submodule ℂ V` to `Submodule.span ℂ (Set.range fun a => eigComp ρ s₀ (v a))`. Establish `hO : ∀ y ∈ oSpan ρ v, π y ∈ W`. Introduce `y hy`.

Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨a, i, rfl⟩` from `hy`. Rewrite using `[hact, hπ]`. Conclude with `W.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`. Rewrite using `[map_add]`. Conclude with `W.add_mem hx hy`. Consider the case `neg x _ hx`.

Rewrite using `[map_neg]`. Conclude with `W.neg_mem hx`. Establish `hI : ∀ x ∈ I₀, π x ∈ W`. Introduce `x hx`. Take `⟨_, _, hN⟩` from `hF`.

Establish `hm` using `hO _ (AddSubgroup.nsmul_relIndex_mem (oSpan ρ v) hx)`. Rewrite `hm` using `[map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ]`. Establish `hN' : (((oSpan ρ v).relIndex I₀ : ℕ) : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hN`. Conclude with `(W.smul_mem_iff hN').1 hm`. Establish `hS : Submodule.span ℂ (I₀ : Set V) ≤ W.comap π` using `Submodule.span_le.2 hI`.

Establish `hxe : ∑ c, l c • q c ∈ eigSp ρ s₀` using `Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hq c)`. Establish `hW : ∑ c, l c • q c ∈ W`. Establish `h` using `hS hl`. Rewrite `h` using `[Submodule.mem_comap, hπ, h3 _ hxe]`. Conclude with `h`.

Take `⟨m, hm⟩` from `(Submodule.mem_span_range_iff_exists_fun ℂ).1 hW`. Establish `hz` using `Fintype.linearIndependent_iff.1 hli (Fin.append (-m) l) (by`. Rewrite using `[Fin.sum_univ_add]`. Simplify using `only [Fin.append_left, Fin.append_right, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]`. Rewrite using `[hm]`.

Use the proof step `simp)`. Use function extensionality and compare the values at `j`. Use `hz (Fin.natAdd r j)` as an intermediate fact. Simplify using `using this`.
-/
theorem eq_zero_of_sum_mem_span : ∀ (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : 𝓞 E →+* Module.End ℂ V) (s₀ : 𝓞 E →+* ℂ) (I₀ : AddSubgroup V) (r k : ℕ) (v : Fin r → V) (q : Fin k → V),
    IsOFamily ρ I₀ v → (∀ (c : 𝓞 E), ∀ x ∈ I₀, ρ c x ∈ I₀) → (∀ c, q c ∈ eigSp ρ s₀) →
    LinearIndependent ℂ (Fin.append (fun a => eigComp ρ s₀ (v a)) q) →
    ∀ l : Fin k → ℂ, ∑ c, l c • q c ∈ Submodule.span ℂ (I₀ : Set V) → l = 0 := by
  intro E _ _ V _ _ ρ s₀ I₀ r k v q hF _ hq hli l hl
  obtain ⟨c, hc⟩ := EigCoef.eigComp_eq_combination E s₀
  obtain ⟨h1, h2, h3⟩ := hc V ρ
  let π : V →ₗ[ℂ] V := ∑ a ∈ c.support, c a • ρ a
  have hπ : ∀ x, π x = eigComp ρ s₀ x := by
    intro x
    rw [h1 x]
    simp [π, LinearMap.sum_apply]
  have hact : ∀ (b : 𝓞 E) x, π (ρ b x) = s₀ b • π x := by
    intro b x
    have e : π (ρ b x) = ρ b (π x) := by
      simp only [π, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
      refine Finset.sum_congr rfl fun a _ => ?_
      congr 1
      have : ρ a * ρ b = ρ b * ρ a := by rw [← map_mul, ← map_mul, mul_comm]
      exact LinearMap.congr_fun this x
    rw [e, EigCoef.mem_eigSp_iff.1 (hπ x ▸ h2 x) b]
  let W : Submodule ℂ V := Submodule.span ℂ (Set.range fun a => eigComp ρ s₀ (v a))
  have hO : ∀ y ∈ oSpan ρ v, π y ∈ W := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, i, rfl⟩ := hy
      rw [hact, hπ]
      exact W.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add]
      exact W.add_mem hx hy
    | neg x _ hx =>
      rw [map_neg]
      exact W.neg_mem hx
  have hI : ∀ x ∈ I₀, π x ∈ W := by
    intro x hx
    obtain ⟨_, _, hN⟩ := hF
    have hm := hO _ (AddSubgroup.nsmul_relIndex_mem (oSpan ρ v) hx)
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ] at hm
    have hN' : (((oSpan ρ v).relIndex I₀ : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN
    exact (W.smul_mem_iff hN').1 hm
  have hS : Submodule.span ℂ (I₀ : Set V) ≤ W.comap π := Submodule.span_le.2 hI
  have hxe : ∑ c, l c • q c ∈ eigSp ρ s₀ := Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hq c)
  have hW : ∑ c, l c • q c ∈ W := by
    have h := hS hl
    rw [Submodule.mem_comap, hπ, h3 _ hxe] at h
    exact h
  obtain ⟨m, hm⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hW
  have hz := Fintype.linearIndependent_iff.1 hli (Fin.append (-m) l) (by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]
    rw [hm]
    simp)
  funext j
  have := hz (Fin.natAdd r j)
  simpa using this

end GlobalTheory.CompanionTheory.Ar.Cusp.EigIndep
