import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstUnique
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory.MomKapi

open Formalism.L2.Th1.H in

/- English proof (translation)
Establish `h` using `AddSubgroup.nsmul_index_mem (S.addSubgroupOf M) (⟨z, hz⟩ : M)`. Establish `h2 : ((S.addSubgroupOf M).index • (⟨z, hz⟩ : M) : M).1 ∈ S` using `AddSubgroup.mem_addSubgroupOf.1 h`. Simplify `h2` using `[relIdx, AddSubgroup.relIndex]`.
-/
theorem nsmul_relIdx_mem {V : Type*} [AddCommGroup V] (S M : AddSubgroup V) {z : V} (hz : z ∈ M) :
    relIdx S M • z ∈ S := by
  have h := AddSubgroup.nsmul_index_mem (S.addSubgroupOf M) (⟨z, hz⟩ : M)
  have h2 : ((S.addSubgroupOf M).index • (⟨z, hz⟩ : M) : M).1 ∈ S := AddSubgroup.mem_addSubgroupOf.1 h
  simpa [relIdx, AddSubgroup.relIndex] using h2

/- English proof (translation)
Introduce `D cc δ B hcc q _ hcop u hn hnq G hG x hx`. Use `set n := Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Forma …`. Use `set N := Ideal.absNorm cc with hNdef`. Establish `hq : q.Prime` using `Fact.out`. Establish `hnc : Nat.Coprime n q` using `((Nat.Prime.coprime_iff_not_dvd hq).2 hnq).symm`.

Use `⟨n * N, Nat.Coprime.mul_left hnc hcop, fun w => ?_⟩` and prove the remaining obligations. Establish `hδ : δ ≠ 0` using `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.base_linkage_nonempty D cc δ B`. Establish `hNc : ((N : ℕ) : 𝓞 D.host.K) ∈ cc` using `Ideal.absNorm_mem cc`. Use `set w₀ : ℂ := δ * D.host.φ₀ (((((N : ℕ) : 𝓞 D.host.K) : D.host.K) : D.host.E)) with hw₀`. Establish `hw₀mem : w₀ ∈ lamOf D cc δ` using `AddSubgroup.subset_closure ⟨_, hNc, rfl⟩`.

Establish `hz : w₀ • emb4 D x ∈ Formalism.L2.Th1.H.pow4 B.lamM` using `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.gen_mem hw₀mem hx`. Establish `hgC : B.gC (w₀ • emb4 D x) = w₀ • (fun w => D.host.φ₀ ((B.γ₀.g x w : D.host.K) : D.host.E))`. Rewrite using `[map_smul]`. Conclude with `congrArg (w₀ • ·) (B.gC_spec x)`. Establish `hu : u (B.gC (w₀ • emb4 D x)) = w₀ • (fun w => D.host.φ₀ ((G (B.γ₀.g x) w : D.host.K) : D.host.E))`.

Rewrite using `[hgC, map_smul, hG]`. Establish `hM : u (B.gC (w₀ • emb4 D x)) ∈ Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))` using `⟨_, ⟨_, hz, rfl⟩, rfl⟩`. Establish `hS` using `nsmul_relIdx_mem (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) _ hM`. Rewrite `hS` using `[← hndef, hu]`. Establish `hc : n • (w₀ * D.host.φ₀ ((G (B.γ₀.g x) w : D.host.K) : D.host.E)) ∈ B.L.lattice`.

Use `hS w (Set.mem_univ w)` as an intermediate fact. Simplify using `using this`. Take `⟨c, -, hc'⟩` from `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.lam_mem D cc δ _ ((Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.mem_iff B _).1 hc)`. Establish `hC : D.host.φ₀ (((((n * N : ℕ) : D.host.K) * G (B.γ₀.g x) w : D.host.K) : D.host.E)) = D.host.φ₀ ((c : D.host.K) : D.host.E)`. Apply `mul_left_cancel₀ hδ` to reduce the goal to its premises.

Rewrite using `[← hc', hw₀]`. Use `push_cast`. Simplify using `only [map_mul, map_natCast, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hK : (((n * N : ℕ) : D.host.K) * G (B.γ₀.g x) w : D.host.K) = (c : D.host.K)` using `Subtype.coe_injective (D.host.φ₀.injective hC)`.

Conclude with `⟨c, hK.symm⟩`.
-/
theorem denom_prime_to : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → ∀ (q : ℕ) [Fact q.Prime], Nat.Coprime (Ideal.absNorm cc) q → ∀ (u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)), Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) ≠ 0 → ¬ q ∣ Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) → ∀ (G : (Fin 4 × D.what₂.Tau → D.host.K) ≃ₗ[D.host.K] (Fin 4 × D.what₂.Tau → D.host.K)), (∀ v : Fin 4 × D.what₂.Tau → D.host.K, u (fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E)) = fun w => D.host.φ₀ ((G v w : D.host.K) : D.host.E)) → ∀ x : Fin 4 → D.host.E, (∀ a, x a ∈ D.host.AA0) → ∃ s : ℕ, Nat.Coprime s q ∧ ∀ w, (s : D.host.K) * G (B.γ₀.g x) w ∈ (algebraMap (𝓞 D.host.K) D.host.K).range := by
  intro D cc δ B hcc q _ hcop u hn hnq G hG x hx
  set n := Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) with hndef
  set N := Ideal.absNorm cc with hNdef
  have hq : q.Prime := Fact.out
  have hnc : Nat.Coprime n q := ((Nat.Prime.coprime_iff_not_dvd hq).2 hnq).symm
  refine ⟨n * N, Nat.Coprime.mul_left hnc hcop, fun w => ?_⟩
  have hδ : δ ≠ 0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.base_linkage_nonempty D cc δ B

  have hNc : ((N : ℕ) : 𝓞 D.host.K) ∈ cc := Ideal.absNorm_mem cc
  set w₀ : ℂ := δ * D.host.φ₀ (((((N : ℕ) : 𝓞 D.host.K) : D.host.K) : D.host.E)) with hw₀
  have hw₀mem : w₀ ∈ lamOf D cc δ := AddSubgroup.subset_closure ⟨_, hNc, rfl⟩
  have hz : w₀ • emb4 D x ∈ Formalism.L2.Th1.H.pow4 B.lamM := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.gen_mem hw₀mem hx
  have hgC : B.gC (w₀ • emb4 D x) = w₀ • (fun w => D.host.φ₀ ((B.γ₀.g x w : D.host.K) : D.host.E)) := by
    rw [map_smul]
    exact congrArg (w₀ • ·) (B.gC_spec x)
  have hu : u (B.gC (w₀ • emb4 D x)) = w₀ • (fun w => D.host.φ₀ ((G (B.γ₀.g x) w : D.host.K) : D.host.E)) := by
    rw [hgC, map_smul, hG]
  have hM : u (B.gC (w₀ • emb4 D x)) ∈ Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM)) :=
    ⟨_, ⟨_, hz, rfl⟩, rfl⟩
  have hS := nsmul_relIdx_mem (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) _ hM
  rw [← hndef, hu] at hS
  have hc : n • (w₀ * D.host.φ₀ ((G (B.γ₀.g x) w : D.host.K) : D.host.E)) ∈ B.L.lattice := by
    have := hS w (Set.mem_univ w)
    simpa using this
  obtain ⟨c, -, hc'⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.lam_mem D cc δ _ ((Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.mem_iff B _).1 hc)
  have hC : D.host.φ₀ (((((n * N : ℕ) : D.host.K) * G (B.γ₀.g x) w : D.host.K) : D.host.E)) = D.host.φ₀ ((c : D.host.K) : D.host.E) := by
    apply mul_left_cancel₀ hδ
    rw [← hc', hw₀]
    push_cast
    simp only [map_mul, map_natCast, nsmul_eq_mul]
    ring
  have hK : (((n * N : ℕ) : D.host.K) * G (B.γ₀.g x) w : D.host.K) = (c : D.host.K) :=
    Subtype.coe_injective (D.host.φ₀.injective hC)
  exact ⟨c, hK.symm⟩

end GlobalTheory.MomKapi
