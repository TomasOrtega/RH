import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstUnique

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.LatDesc

/- English proof (translation)
Introduce `D cc δ B hcc u hidx v`. Establish `hδ : δ ≠ 0` using `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.base_linkage_nonempty D cc δ B`. Use `set S := Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau) with hS`. Use `set M := Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM)) with hM`. Use `set n := Formalism.L2.Th1.H.relIdx S M with hn`.

Establish `h1 : ∀ x ∈ M, n • x ∈ S`. Introduce `x hx`. Use `AddSubgroup.nsmul_index_mem (S.addSubgroupOf M) (⟨x, hx⟩ : M)` as an intermediate fact. Rewrite `this` using `[AddSubgroup.mem_addSubgroupOf, AddSubmonoidClass.coe_nsmul]`. Conclude with `this`.

Use `set y := B.γ₀.g.symm v with hy`. Take `⟨t, ht, hint⟩` from `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.exists_nat_mul D.host.E (Finset.univ.image y)`. Use `set N := Ideal.absNorm cc with hNdef`. Establish `hN : N ≠ 0`. Rewrite using `[hNdef, Ne, Ideal.absNorm_eq_zero_iff]`.

Conclude with `hcc.1`. Establish `hNc : ((N : 𝓞 D.host.K)) ∈ cc` using `Ideal.absNorm_mem cc`. Establish `hw₀ : δ * (N : ℂ) ∈ lamOf D cc δ`. Use `AddSubgroup.subset_closure ⟨(N : 𝓞 D.host.K), hNc, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.

Establish `hm : (δ * (N : ℂ)) • emb4 D (t • y) ∈ Formalism.L2.Th1.H.pow4 B.lamM` using `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.gen_mem hw₀ fun a => Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.int_mem_inverse_half_different (by`. Use `hint _ (Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩)` as an intermediate fact. Simplify using `using this)`. Use `set V : Fin 4 × D.what₂.Tau → ℂ := fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E) with hV`. Establish `hg : B.gC (emb4 D (t • y)) = (t : ℂ) • V`.

Rewrite using `[show B.gC (emb4 D (t • y)) = _ from B.gC_spec (t • y), map_nsmul, hy, LinearEquiv.apply_symm_apply]`. Use function extensionality and compare the values at `w`. Simplify using `[hV]`. Establish `hmem : (δ * (N : ℂ) * (t : ℂ)) • u V ∈ M`. Use `⟨B.gC ((δ * (N : ℂ)) • emb4 D (t • y)), ⟨_, hm, rfl⟩, ?_⟩` and prove the remaining obligations.

Use `show u (B.gC _) = _`. Rewrite using `[map_smul, hg, smul_smul, map_smul]`. Establish `hS'` using `h1 _ hmem`. Rewrite `hS'` using `[hS, Formalism.L2.Th1.H.mem_stdLat]`. Establish `hc : ∀ w, ∃ c ∈ cc, ((n • ((δ * (N : ℂ) * (t : ℂ)) • u V)) w) = δ * D.host.φ₀ (((c : 𝓞 D.host.K) : D.host.K) : D.host.E)` using `fun w => Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.lam_mem D cc δ _ ((Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.mem_iff B _).1 (hS' w))`.

Use `choose c _ hc using hc`. Establish `hnC : (n : ℂ) ≠ 0` using `by exact_mod_cast hidx`. Establish `hNC : (N : ℂ) ≠ 0` using `by exact_mod_cast hN`. Establish `htC : (t : ℂ) ≠ 0` using `by exact_mod_cast ht.ne'`. Use `⟨fun w => ((c w : 𝓞 D.host.K) : D.host.K) / ((n : D.host.K) * (N : D.host.K) * (t : D.host.K)), ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `w`. Establish `h` using `hc w`. Simplify using `only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul] at h`. Establish `e : D.host.φ₀ (((((c w : 𝓞 D.host.K) : D.host.K) / ((n : D.host.K) * (N : D.host.K) * (t : D.host.K)) : D.host.K)) : D.host.E) = D.host.φ₀ (((c w : 𝓞 D.host.K) : D.host.K) : D.host.E) / ((n : ℂ) * (N : ℂ) * (t : ℂ))`. Use `push_cast`.

Rewrite using `[map_div₀, map_mul, map_mul, map_natCast, map_natCast, map_natCast]`. Rewrite using `[e, eq_div_iff (mul_ne_zero (mul_ne_zero hnC hNC) htC)]`. Apply `mul_left_cancel₀ hδ` to reduce the goal to its premises. Rewrite using `[← h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem unitary_maps_rational : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → ∀ (u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)), Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) ≠ 0 → ∀ v : Fin 4 × D.what₂.Tau → D.host.K, ∃ v' : Fin 4 × D.what₂.Tau → D.host.K, u (fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E)) = fun w => D.host.φ₀ ((v' w : D.host.K) : D.host.E) := by
  intro D cc δ B hcc u hidx v
  have hδ : δ ≠ 0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.base_linkage_nonempty D cc δ B
  set S := Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau) with hS
  set M := Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM)) with hM
  set n := Formalism.L2.Th1.H.relIdx S M with hn

  have h1 : ∀ x ∈ M, n • x ∈ S := by
    intro x hx
    have := AddSubgroup.nsmul_index_mem (S.addSubgroupOf M) (⟨x, hx⟩ : M)
    rw [AddSubgroup.mem_addSubgroupOf, AddSubmonoidClass.coe_nsmul] at this
    exact this

  set y := B.γ₀.g.symm v with hy
  obtain ⟨t, ht, hint⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.exists_nat_mul D.host.E (Finset.univ.image y)
  set N := Ideal.absNorm cc with hNdef
  have hN : N ≠ 0 := by
    rw [hNdef, Ne, Ideal.absNorm_eq_zero_iff]; exact hcc.1
  have hNc : ((N : 𝓞 D.host.K)) ∈ cc := Ideal.absNorm_mem cc
  have hw₀ : δ * (N : ℂ) ∈ lamOf D cc δ := by
    refine AddSubgroup.subset_closure ⟨(N : 𝓞 D.host.K), hNc, ?_⟩
    simp
  have hm : (δ * (N : ℂ)) • emb4 D (t • y) ∈ Formalism.L2.Th1.H.pow4 B.lamM :=
    Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.gen_mem hw₀ fun a => Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.int_mem_inverse_half_different (by
      have := hint _ (Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩)
      simpa using this)
  set V : Fin 4 × D.what₂.Tau → ℂ := fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E) with hV
  have hg : B.gC (emb4 D (t • y)) = (t : ℂ) • V := by
    rw [show B.gC (emb4 D (t • y)) = _ from B.gC_spec (t • y), map_nsmul, hy, LinearEquiv.apply_symm_apply]
    funext w
    simp [hV]
  have hmem : (δ * (N : ℂ) * (t : ℂ)) • u V ∈ M := by
    refine ⟨B.gC ((δ * (N : ℂ)) • emb4 D (t • y)), ⟨_, hm, rfl⟩, ?_⟩
    show u (B.gC _) = _
    rw [map_smul, hg, smul_smul, map_smul]
  have hS' := h1 _ hmem
  rw [hS, Formalism.L2.Th1.H.mem_stdLat] at hS'
  have hc : ∀ w, ∃ c ∈ cc, ((n • ((δ * (N : ℂ) * (t : ℂ)) • u V)) w) = δ * D.host.φ₀ (((c : 𝓞 D.host.K) : D.host.K) : D.host.E) :=
    fun w => Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.lam_mem D cc δ _ ((Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.mem_iff B _).1 (hS' w))
  choose c _ hc using hc
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hidx
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  refine ⟨fun w => ((c w : 𝓞 D.host.K) : D.host.K) / ((n : D.host.K) * (N : D.host.K) * (t : D.host.K)), ?_⟩
  funext w
  have h := hc w
  simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul] at h
  have e : D.host.φ₀ (((((c w : 𝓞 D.host.K) : D.host.K) / ((n : D.host.K) * (N : D.host.K) * (t : D.host.K)) : D.host.K)) : D.host.E)
      = D.host.φ₀ (((c w : 𝓞 D.host.K) : D.host.K) : D.host.E) / ((n : ℂ) * (N : ℂ) * (t : ℂ)) := by
    push_cast
    rw [map_div₀, map_mul, map_mul, map_natCast, map_natCast, map_natCast]
  rw [e, eq_div_iff (mul_ne_zero (mul_ne_zero hnC hNC) htC)]
  apply mul_left_cancel₀ hδ
  rw [← h]
  ring

end GlobalTheory.LatDesc

end
