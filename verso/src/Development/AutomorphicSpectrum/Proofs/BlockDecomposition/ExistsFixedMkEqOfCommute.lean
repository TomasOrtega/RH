import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MetaplecticLowRank.LowC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective

noncomputable section

open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology

namespace GlobalTheory.CompanionTheory.JacquetCentral

/- English proof (translation)
Introduce `G V _ _ _ _ _ π hπ I N hIo hIc M _ s hs M₀ hsI C hfac hcon y hy`. Take `⟨hsm, hfd⟩` from `hπ`. Establish `hj : ∀ (m : M) (z : V), jacquet π N s hs m ((twKer π N 1).mkQ z) = (twKer π N 1).mkQ (π (s m) z)` using `fun m z => rfl`. Establish `hfixI : ∀ v ∈ fixed π I, ∀ g ∈ I, π g v = v`. Introduce `v hv g hg`.

Establish `h` using `hv ⟨g, hg⟩`. Simplify using `using h`. Establish `hy' : ∀ d ∈ M₀, jacquet π N s hs d y = y`. Introduce `d hd`. Establish `h` using `hy ⟨d, hd⟩`.

Simplify using `using h`. Establish `hmul : ∀ (a b : G) (z : V), π a (π b z) = π (a * b) z` using `fun a b z => (LinearMap.congr_fun (map_mul π a b) z).symm`. Establish `hconj : ∀ (g h : G) (z : V), π g (π h z) = π h (π (h⁻¹ * g * h) z)`. Introduce `g h z`. Rewrite using `[hmul, hmul, show h * (h⁻¹ * g * h) = g * h by simp [mul_assoc]]`.

Establish `hN : ∀ x ∈ N, ∀ z : V, (twKer π N 1).mkQ (π x z) = (twKer π N 1).mkQ z`. Introduce `x hx z`. Rewrite using `[Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]`. Conclude with `Submodule.subset_span ⟨⟨x, hx⟩, z, by simp⟩`. Establish `hstep : ∀ u : V, (∀ c ∈ C, π c u = u) → (∀ d ∈ M₀, (twKer π N 1).mkQ (π (s d) u) = (twKer π N 1).mkQ u) → ∃ v ∈ fixed π I, (twKer π N 1).mkQ v = (twKer π N 1).mkQ u`.

Introduce `u hu hd`. Use `GlobalTheory.SmGL.IwahoriOnto.exists_fixed_map_eq hsm hIc (twKer π N 1).mkQ u ?_` and prove the remaining obligations. Introduce `g hg`. Take `⟨d, hdM, x, hx, c, hc, rfl⟩` from `hfac g hg`. Rewrite using `[← hmul, ← hmul, hu c hc, ← hj, hN x hx u, hj]`.

Conclude with `hd d hdM`. Take `⟨w, rfl⟩` from `Submodule.mkQ_surjective (twKer π N 1) y`. Establish `hU : {g : G | π g w = w} ∩ (I : Set G) ∈ 𝓝 (1 : G)` using `Filter.inter_mem ((hsm w).mem_nhds (by simp)) (hIo.mem_nhds I.one_mem)`. Take `⟨t, htc, htC⟩` from `hcon _ hU`. Establish `hcomm : ∀ d ∈ M₀, ∀ z : V, π (s d) (π (s t) z) = π (s t) (π (s d) z)`.

Introduce `d hd z`. Rewrite using `[hmul, hmul, ← map_mul, ← map_mul, htc d hd]`. Establish `hC : ∀ z : V, (∀ c ∈ C, π ((s t)⁻¹ * c * s t) z = z) → ∀ c ∈ C, π c (π (s t) z) = π (s t) z`. Introduce `z hz c hc`. Rewrite using `[hconj c (s t) z, hz c hc]`.

Use `set W : Submodule ℂ (V ⧸ twKer π N 1) := (fixed π I).map (twKer π N 1).mkQ with hW`. Use `haveI : FiniteDimensional ℂ (fixed π I) := hfd I hIo hIc`. Establish `hWfd : FiniteDimensional ℂ W`. Rewrite using `[hW]`. Use `infer_instance`.

Establish `hstepW : ∀ u : V, (∀ c ∈ C, π c u = u) → (∀ d ∈ M₀, (twKer π N 1).mkQ (π (s d) u) = (twKer π N 1).mkQ u) → (twKer π N 1).mkQ u ∈ W`. Introduce `u hu hd`. Take `⟨v, hv, he⟩` from `hstep u hu hd`. Conclude with `Submodule.mem_map.2 ⟨v, hv, he⟩`. Establish `hAW : ∀ z ∈ W, jacquet π N s hs t z ∈ W`.

Introduce `z hz`. Take `⟨v, hv, rfl⟩` from `Submodule.mem_map.1 hz`. Rewrite using `[hj]`. Apply `hstepW` to reduce the goal to its premises. Conclude with `hC v (fun c hc => hfixI v hv _ (htC c hc).2)`.

Introduce `d hd`. Rewrite using `[hcomm d hd, hfixI v hv (s d) (hsI d hd)]`. Establish `hAy : jacquet π N s hs t ((twKer π N 1).mkQ w) ∈ W`. Rewrite using `[hj]`. Apply `hstepW` to reduce the goal to its premises.

Conclude with `hC w (fun c hc => (htC c hc).1)`. Introduce `d hd`. Rewrite using `[hcomm d hd, ← hj t (π (s d) w), ← hj t w, ← hj d w, hy' d hd]`. Establish `hinv : ∀ z : Jacquet π N, jacquet π N s hs t⁻¹ (jacquet π N s hs t z) = z`. Introduce `z`.

Establish `h1` using `LinearMap.congr_fun (map_mul (jacquet π N s hs) t⁻¹ t) z`. Rewrite `h1` using `[inv_mul_cancel, map_one]`. Conclude with `h1.symm`. Set `A : W →ₗ[ℂ] W` to `LinearMap.restrict (jacquet π N s hs t) hAW`. Establish `hAinj : Function.Injective A`.

Introduce `a b hab`. Establish `h : jacquet π N s hs t (a : V ⧸ twKer π N 1) = jacquet π N s hs t (b : V ⧸ twKer π N 1)` using `congrArg Subtype.val hab`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hinv (a : V ⧸ twKer π N 1), h, hinv]`. Take `⟨z, hz⟩` from `(LinearMap.injective_iff_surjective.1 hAinj) ⟨_, hAy⟩`.

Establish `hz' : jacquet π N s hs t (z : V ⧸ twKer π N 1) = jacquet π N s hs t ((twKer π N 1).mkQ w)` using `congrArg Subtype.val hz`. Establish `hzw : (z : V ⧸ twKer π N 1) = (twKer π N 1).mkQ w`. Rewrite using `[← hinv (z : V ⧸ twKer π N 1), hz', hinv]`. Establish `hwW : (twKer π N 1).mkQ w ∈ W`. Rewrite using `[← hzw]`.

Conclude with `z.2`. Take `⟨v, hv, hvz⟩` from `Submodule.mem_map.1 hwW`. Conclude with `⟨v, hv, hvz⟩`.
-/
theorem exists_fixed_mk_eq_of_commute : ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V), IsAdmissible π → ∀ (I N : Subgroup G), IsOpen (I : Set G) → IsCompact (I : Set G) →
    ∀ {M : Type} [Group M] (s : M →* G) (hs : ∀ m, s m ∈ Subgroup.normalizer (N : Set G)) (M₀ : Subgroup M),
    (∀ d ∈ M₀, s d ∈ I) → ∀ (C : Set G), (∀ g ∈ I, ∃ d ∈ M₀, ∃ x ∈ N, ∃ c ∈ C, g = s d * x * c) →
    (∀ U ∈ 𝓝 (1 : G), ∃ t : M, (∀ d ∈ M₀, t * d = d * t) ∧ ∀ c ∈ C, (s t)⁻¹ * c * s t ∈ U) →
    ∀ y : Jacquet π N, y ∈ fixed (jacquet π N s hs) M₀ → ∃ v ∈ fixed π I, (twKer π N 1).mkQ v = y := by
  intro G V _ _ _ _ _ π hπ I N hIo hIc M _ s hs M₀ hsI C hfac hcon y hy
  obtain ⟨hsm, hfd⟩ := hπ
  have hj : ∀ (m : M) (z : V),
      jacquet π N s hs m ((twKer π N 1).mkQ z) = (twKer π N 1).mkQ (π (s m) z) :=
    fun m z => rfl
  have hfixI : ∀ v ∈ fixed π I, ∀ g ∈ I, π g v = v := by
    intro v hv g hg
    have h := hv ⟨g, hg⟩
    simpa using h
  have hy' : ∀ d ∈ M₀, jacquet π N s hs d y = y := by
    intro d hd
    have h := hy ⟨d, hd⟩
    simpa using h
  have hmul : ∀ (a b : G) (z : V), π a (π b z) = π (a * b) z := fun a b z =>
    (LinearMap.congr_fun (map_mul π a b) z).symm
  have hconj : ∀ (g h : G) (z : V), π g (π h z) = π h (π (h⁻¹ * g * h) z) := by
    intro g h z
    rw [hmul, hmul, show h * (h⁻¹ * g * h) = g * h by simp [mul_assoc]]
  have hN : ∀ x ∈ N, ∀ z : V, (twKer π N 1).mkQ (π x z) = (twKer π N 1).mkQ z := by
    intro x hx z
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact Submodule.subset_span ⟨⟨x, hx⟩, z, by simp⟩
  have hstep : ∀ u : V, (∀ c ∈ C, π c u = u) →
      (∀ d ∈ M₀, (twKer π N 1).mkQ (π (s d) u) = (twKer π N 1).mkQ u) →
      ∃ v ∈ fixed π I, (twKer π N 1).mkQ v = (twKer π N 1).mkQ u := by
    intro u hu hd
    refine GlobalTheory.SmGL.IwahoriOnto.exists_fixed_map_eq hsm hIc (twKer π N 1).mkQ u ?_
    intro g hg
    obtain ⟨d, hdM, x, hx, c, hc, rfl⟩ := hfac g hg
    rw [← hmul, ← hmul, hu c hc, ← hj, hN x hx u, hj]
    exact hd d hdM
  obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective (twKer π N 1) y
  have hU : {g : G | π g w = w} ∩ (I : Set G) ∈ 𝓝 (1 : G) :=
    Filter.inter_mem ((hsm w).mem_nhds (by simp)) (hIo.mem_nhds I.one_mem)
  obtain ⟨t, htc, htC⟩ := hcon _ hU
  have hcomm : ∀ d ∈ M₀, ∀ z : V, π (s d) (π (s t) z) = π (s t) (π (s d) z) := by
    intro d hd z
    rw [hmul, hmul, ← map_mul, ← map_mul, htc d hd]
  have hC : ∀ z : V, (∀ c ∈ C, π ((s t)⁻¹ * c * s t) z = z) →
      ∀ c ∈ C, π c (π (s t) z) = π (s t) z := by
    intro z hz c hc
    rw [hconj c (s t) z, hz c hc]
  set W : Submodule ℂ (V ⧸ twKer π N 1) := (fixed π I).map (twKer π N 1).mkQ with hW
  haveI : FiniteDimensional ℂ (fixed π I) := hfd I hIo hIc
  have hWfd : FiniteDimensional ℂ W := by
    rw [hW]
    infer_instance
  have hstepW : ∀ u : V, (∀ c ∈ C, π c u = u) →
      (∀ d ∈ M₀, (twKer π N 1).mkQ (π (s d) u) = (twKer π N 1).mkQ u) →
      (twKer π N 1).mkQ u ∈ W := by
    intro u hu hd
    obtain ⟨v, hv, he⟩ := hstep u hu hd
    exact Submodule.mem_map.2 ⟨v, hv, he⟩
  have hAW : ∀ z ∈ W, jacquet π N s hs t z ∈ W := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hz
    rw [hj]
    apply hstepW
    · exact hC v (fun c hc => hfixI v hv _ (htC c hc).2)
    · intro d hd
      rw [hcomm d hd, hfixI v hv (s d) (hsI d hd)]
  have hAy : jacquet π N s hs t ((twKer π N 1).mkQ w) ∈ W := by
    rw [hj]
    apply hstepW
    · exact hC w (fun c hc => (htC c hc).1)
    · intro d hd
      rw [hcomm d hd, ← hj t (π (s d) w), ← hj t w, ← hj d w, hy' d hd]
  have hinv : ∀ z : Jacquet π N, jacquet π N s hs t⁻¹ (jacquet π N s hs t z) = z := by
    intro z
    have h1 := LinearMap.congr_fun (map_mul (jacquet π N s hs) t⁻¹ t) z
    rw [inv_mul_cancel, map_one] at h1
    exact h1.symm
  let A : W →ₗ[ℂ] W := LinearMap.restrict (jacquet π N s hs t) hAW
  have hAinj : Function.Injective A := by
    intro a b hab
    have h : jacquet π N s hs t (a : V ⧸ twKer π N 1) = jacquet π N s hs t (b : V ⧸ twKer π N 1) :=
      congrArg Subtype.val hab
    apply Subtype.ext
    rw [← hinv (a : V ⧸ twKer π N 1), h, hinv]
  obtain ⟨z, hz⟩ := (LinearMap.injective_iff_surjective.1 hAinj) ⟨_, hAy⟩
  have hz' : jacquet π N s hs t (z : V ⧸ twKer π N 1) = jacquet π N s hs t ((twKer π N 1).mkQ w) :=
    congrArg Subtype.val hz
  have hzw : (z : V ⧸ twKer π N 1) = (twKer π N 1).mkQ w := by
    rw [← hinv (z : V ⧸ twKer π N 1), hz', hinv]
  have hwW : (twKer π N 1).mkQ w ∈ W := by
    rw [← hzw]
    exact z.2
  obtain ⟨v, hv, hvz⟩ := Submodule.mem_map.1 hwW
  exact ⟨v, hv, hvz⟩

end GlobalTheory.CompanionTheory.JacquetCentral
