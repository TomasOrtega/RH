import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.InnerEq

open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc
open scoped InnerProductSpace

namespace UpperTheory.V.Z.GSp4Splitting

section SlopeTestRemainingChoices

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {σ : Un n →* (V →ₗ[ℂ] V)} {E : KMod n}

/- English proof (translation)
Establish `h : σ k * σ k⁻¹ = 1` using `by rw [← map_mul, mul_inv_cancel, map_one]`. Conclude with `LinearMap.congr_fun h y`.
-/
private theorem sig_inv (k : Un n) (y : V) : σ k (σ k⁻¹ y) = y := by
  have h : σ k * σ k⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  exact LinearMap.congr_fun h y

/- English proof (translation)
Establish `h` using `hσ.iso k (σ k⁻¹ c) y`. Rewrite `h` using `[sig_inv]`. Conclude with `h`.
-/
private theorem inner_sig (hσ : IsK σ) (k : Un n) (c y : V) : ⟪c, σ k y⟫_ℂ = ⟪σ k⁻¹ c, y⟫_ℂ := by
  have h := hσ.iso k (σ k⁻¹ c) y
  rw [sig_inv] at h
  exact h

/- English proof (translation)
The claim follows from `(le_iSup (fun t : invA σ E => LinearMap.range t.1) t) ⟨ξ, rfl⟩`.
-/
private theorem range_mem (t : invA σ E) (ξ : E.V →L[ℂ] ℂ) : t.1 ξ ∈ isoSp σ E :=
  (le_iSup (fun t : invA σ E => LinearMap.range t.1) t) ⟨ξ, rfl⟩

/- English proof (translation)
Use `iSup_le fun t => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨ξ, rfl⟩`. Conclude with `h t ξ`.
-/
private theorem iso_le {W : Submodule ℂ V} (h : ∀ (t : invA σ E) ξ, t.1 ξ ∈ W) : isoSp σ E ≤ W := by
  refine iSup_le fun t => ?_
  rintro _ ⟨ξ, rfl⟩
  exact h t ξ

/- English proof (translation)
Establish `h : isoSp σ E ≤ (isoSp σ E).comap B`. Use `iso_le fun t ξ => ?_` and prove the remaining obligations. Establish `ht : B.comp t.1 ∈ invA σ E` using `fun k ξ => by`. Simplify using `only [LinearMap.comp_apply]`. Rewrite using `[t.2 k ξ, hB]`.

Conclude with `range_mem ⟨_, ht⟩ ξ`. Conclude with `h hx`.
-/
private theorem map_iso (B : V →ₗ[ℂ] V) (hB : ∀ k x, B (σ k x) = σ k (B x)) {x : V}
    (hx : x ∈ isoSp σ E) : B x ∈ isoSp σ E := by
  have h : isoSp σ E ≤ (isoSp σ E).comap B := by
    refine iso_le fun t ξ => ?_
    have ht : B.comp t.1 ∈ invA σ E := fun k ξ => by
      simp only [LinearMap.comp_apply]
      rw [t.2 k ξ, hB]
    exact range_mem ⟨_, ht⟩ ξ
  exact h hx

/- English proof (translation)
Establish `h : isoSp σ E ≤ (isoSp σ E).comap (σ k)`. Use `iso_le fun t ξ => ?_` and prove the remaining obligations. Use `show σ k (t.1 ξ) ∈ isoSp σ E`. Rewrite using `[← t.2 k ξ]`. Conclude with `range_mem t _`.

Conclude with `h hx`.
-/
private theorem iso_stable (k : Un n) {x : V} (hx : x ∈ isoSp σ E) : σ k x ∈ isoSp σ E := by
  have h : isoSp σ E ≤ (isoSp σ E).comap (σ k) := by
    refine iso_le fun t ξ => ?_
    show σ k (t.1 ξ) ∈ isoSp σ E
    rw [← t.2 k ξ]
    exact range_mem t _
  exact h hx

/- English proof (translation)
Rewrite `hy`, the goal using `[Submodule.mem_orthogonal]`. Introduce `c hc`. Rewrite using `[inner_sig hσ]`. Conclude with `hy _ (hK _ _ hc)`.
-/
private theorem orth_stable (hσ : IsK σ) {K : Submodule ℂ V} (hK : ∀ k, ∀ x ∈ K, σ k x ∈ K)
    (k : Un n) {y : V} (hy : y ∈ Kᗮ) : σ k y ∈ Kᗮ := by
  rw [Submodule.mem_orthogonal] at hy ⊢
  intro c hc
  rw [inner_sig hσ]
  exact hy _ (hK _ _ hc)

/- English proof (translation)
Use `Submodule.eq_starProjection_of_mem_orthogonal (hK _ _ (K.starProjection_apply_mem x)) ?_` and prove the remaining obligations. Rewrite using `[← map_sub]`. Conclude with `orth_stable hσ hK k (K.sub_starProjection_mem_orthogonal x)`.
-/
private theorem proj_comm (hσ : IsK σ) (K : Submodule ℂ V) [K.HasOrthogonalProjection]
    (hK : ∀ k, ∀ x ∈ K, σ k x ∈ K) (k : Un n) (x : V) :
    K.starProjection (σ k x) = σ k (K.starProjection x) := by
  refine Submodule.eq_starProjection_of_mem_orthogonal (hK _ _ (K.starProjection_apply_mem x)) ?_
  rw [← map_sub]
  exact orth_stable hσ hK k (K.sub_starProjection_mem_orthogonal x)

/- English proof (translation)
Set `D : Submodule ℂ V` to `S ⊓ isoSp σ E`. Use `haveI : FiniteDimensional ℂ D := Submodule.finiteDimensional_inf_left S _`. Use `haveI : CompleteSpace D := FiniteDimensional.complete ℂ D`. Set `C : Submodule ℂ V` to `S ⊓ Dᗮ`. Use `haveI : FiniteDimensional ℂ C := Submodule.finiteDimensional_inf_left S _`.

Use `haveI : CompleteSpace C := FiniteDimensional.complete ℂ C`. Establish `hD : ∀ k, ∀ x ∈ D, σ k x ∈ D` using `fun k x hx => ⟨hS k x hx.1, iso_stable k hx.2⟩`. Establish `hC : ∀ k, ∀ x ∈ C, σ k x ∈ C` using `fun k x hx => ⟨hS k x hx.1, orth_stable hσ hD k hx.2⟩`. Establish `hu : D.starProjection x ∈ D` using `D.starProjection_apply_mem x`. Use `⟨D.starProjection x, hu, ?_⟩` and prove the remaining obligations.

Establish `hc : x - D.starProjection x ∈ C` using `⟨S.sub_mem hx hu.1, D.sub_starProjection_mem_orthogonal x⟩`. Establish `hIC : isoSp σ E ≤ Cᗮ`. Introduce `y hy`. Establish `h1 : C.starProjection y ∈ isoSp σ E` using `map_iso (C.starProjection : V →ₗ[ℂ] V) (fun k z => proj_comm hσ C hC k z) hy`. Establish `h2 : C.starProjection y ∈ C` using `C.starProjection_apply_mem y`.

Establish `h3 : C.starProjection y ∈ D` using `⟨h2.1, h1⟩`. Establish `h0 : C.starProjection y = 0`. Establish `h4 : C.starProjection y ∈ D ⊓ Dᗮ` using `⟨h3, h2.2⟩`. Rewrite `h4` using `[D.inf_orthogonal_eq_bot]`. Conclude with `(Submodule.mem_bot ℂ).1 h4`.

Conclude with `(Submodule.starProjection_apply_eq_zero_iff C).1 h0`. Rewrite using `[Submodule.mem_orthogonal]`. Introduce `y hy`. Establish `h` using `(Submodule.mem_orthogonal _ _).1 (hIC hy) _ hc`. Rewrite using `[← inner_conj_symm, h, map_zero]`.
-/
private theorem core (hσ : IsK σ) (S : Submodule ℂ V) [FiniteDimensional ℂ S]
    (hS : ∀ k, ∀ x ∈ S, σ k x ∈ S) {x : V} (hx : x ∈ S) :
    ∃ u ∈ S ⊓ isoSp σ E, x - u ∈ (isoSp σ E)ᗮ := by
  let D : Submodule ℂ V := S ⊓ isoSp σ E
  haveI : FiniteDimensional ℂ D := Submodule.finiteDimensional_inf_left S _
  haveI : CompleteSpace D := FiniteDimensional.complete ℂ D
  let C : Submodule ℂ V := S ⊓ Dᗮ
  haveI : FiniteDimensional ℂ C := Submodule.finiteDimensional_inf_left S _
  haveI : CompleteSpace C := FiniteDimensional.complete ℂ C
  have hD : ∀ k, ∀ x ∈ D, σ k x ∈ D := fun k x hx => ⟨hS k x hx.1, iso_stable k hx.2⟩
  have hC : ∀ k, ∀ x ∈ C, σ k x ∈ C := fun k x hx => ⟨hS k x hx.1, orth_stable hσ hD k hx.2⟩
  have hu : D.starProjection x ∈ D := D.starProjection_apply_mem x
  refine ⟨D.starProjection x, hu, ?_⟩
  have hc : x - D.starProjection x ∈ C := ⟨S.sub_mem hx hu.1, D.sub_starProjection_mem_orthogonal x⟩
  have hIC : isoSp σ E ≤ Cᗮ := by
    intro y hy
    have h1 : C.starProjection y ∈ isoSp σ E :=
      map_iso (C.starProjection : V →ₗ[ℂ] V) (fun k z => proj_comm hσ C hC k z) hy
    have h2 : C.starProjection y ∈ C := C.starProjection_apply_mem y
    have h3 : C.starProjection y ∈ D := ⟨h2.1, h1⟩
    have h0 : C.starProjection y = 0 := by
      have h4 : C.starProjection y ∈ D ⊓ Dᗮ := ⟨h3, h2.2⟩
      rw [D.inf_orthogonal_eq_bot] at h4
      exact (Submodule.mem_bot ℂ).1 h4
    exact (Submodule.starProjection_apply_eq_zero_iff C).1 h0
  rw [Submodule.mem_orthogonal]
  intro y hy
  have h := (Submodule.mem_orthogonal _ _).1 (hIC hy) _ hc
  rw [← inner_conj_symm, h, map_zero]

end SlopeTestRemainingChoices

end UpperTheory.V.Z.GSp4Splitting

/- English proof (translation)
Introduce `n V _ _ σ hσ E`. Use `haveI : (isoSp σ E).HasOrthogonalProjection := ⟨fun v => by`. Take `⟨S, hfd, hx, hS⟩` from `hσ.fin v`. Use `haveI := hfd`. Take `⟨u, hu, hv⟩` from `core (E := E) hσ S hS hx`.

Conclude with `⟨u, hu.2, hv⟩⟩`. Establish `hIs : ∀ k, ∀ x ∈ isoSp σ E, σ k x ∈ isoSp σ E` using `fun k x hx => iso_stable k hx`. Use `⟨((isoSp σ E).starProjection : V →ₗ[ℂ] V), ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x y`. Conclude with `Submodule.inner_starProjection_left_eq_right _ x y`.

Introduce `x`. Conclude with `(isoSp σ E).starProjection_apply_mem x`. Introduce `x hx`. Conclude with `(Submodule.starProjection_eq_self_iff).2 hx`. Introduce `k`.

Use extensionality with `x`. Conclude with `proj_comm hσ _ hIs k x`. Introduce and unpack `B ⟨B', hadj, hcomm⟩`. Establish `hB : ∀ x ∈ isoSp σ E, B x ∈ isoSp σ E` using `fun x hx => map_iso B (fun k z => LinearMap.congr_fun (hcomm k).1 z) hx`. Establish `hB' : ∀ x ∈ isoSp σ E, B' x ∈ isoSp σ E` using `fun x hx => map_iso B' (fun k z => LinearMap.congr_fun (hcomm k).2 z) hx`.

Use extensionality with `x`. Use `show (isoSp σ E).starProjection (B x) = B ((isoSp σ E).starProjection x)`. Use `Submodule.eq_starProjection_of_mem_orthogonal (hB _ ((isoSp σ E).starProjection_apply_mem x)) ?_` and prove the remaining obligations. Rewrite using `[← map_sub, Submodule.mem_orthogonal]`. Introduce `c hc`.

Establish `h` using `(Submodule.mem_orthogonal _ _).1 ((isoSp σ E).sub_starProjection_mem_orthogonal x) (B' c) (hB' c hc)`. Rewrite using `[← inner_conj_symm, hadj, ← inner_conj_symm, h, map_zero, map_zero]`. Introduce `N hN x hx`. Take `⟨S, hfd, hxS, hS⟩` from `hσ.fin x`. Use `haveI := hfd`.

Use `haveI : FiniteDimensional ℂ (S ⊓ N : Submodule ℂ V) := Submodule.finiteDimensional_inf_left S N`. Take `⟨u, hu, hv⟩` from `core (E := E) hσ (S ⊓ N) (fun k y hy => ⟨hS k y hy.1, hN k y hy.2⟩) ⟨hxS, hx⟩`. Establish `he : (isoSp σ E).starProjection x = u` using `Submodule.eq_starProjection_of_mem_orthogonal hu.2 hv`. Use `show (isoSp σ E).starProjection x ∈ N`. Rewrite using `[he]`.

Conclude with `hu.1.2`.
-/
theorem UpperTheory.V.Z.GSp4Splitting.projEx :
    ProjEx := by
  intro n V _ _ σ hσ E
  haveI : (isoSp σ E).HasOrthogonalProjection := ⟨fun v => by
    obtain ⟨S, hfd, hx, hS⟩ := hσ.fin v
    haveI := hfd
    obtain ⟨u, hu, hv⟩ := core (E := E) hσ S hS hx
    exact ⟨u, hu.2, hv⟩⟩
  have hIs : ∀ k, ∀ x ∈ isoSp σ E, σ k x ∈ isoSp σ E := fun k x hx => iso_stable k hx
  refine ⟨((isoSp σ E).starProjection : V →ₗ[ℂ] V), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    exact Submodule.inner_starProjection_left_eq_right _ x y
  · intro x
    exact (isoSp σ E).starProjection_apply_mem x
  · intro x hx
    exact (Submodule.starProjection_eq_self_iff).2 hx
  · intro k
    ext x
    exact proj_comm hσ _ hIs k x
  · rintro B ⟨B', hadj, hcomm⟩
    have hB : ∀ x ∈ isoSp σ E, B x ∈ isoSp σ E := fun x hx =>
      map_iso B (fun k z => LinearMap.congr_fun (hcomm k).1 z) hx
    have hB' : ∀ x ∈ isoSp σ E, B' x ∈ isoSp σ E := fun x hx =>
      map_iso B' (fun k z => LinearMap.congr_fun (hcomm k).2 z) hx
    ext x
    show (isoSp σ E).starProjection (B x) = B ((isoSp σ E).starProjection x)
    refine Submodule.eq_starProjection_of_mem_orthogonal (hB _ ((isoSp σ E).starProjection_apply_mem x)) ?_
    rw [← map_sub, Submodule.mem_orthogonal]
    intro c hc
    have h := (Submodule.mem_orthogonal _ _).1 ((isoSp σ E).sub_starProjection_mem_orthogonal x) (B' c) (hB' c hc)
    rw [← inner_conj_symm, hadj, ← inner_conj_symm, h, map_zero, map_zero]
  · intro N hN x hx
    obtain ⟨S, hfd, hxS, hS⟩ := hσ.fin x
    haveI := hfd
    haveI : FiniteDimensional ℂ (S ⊓ N : Submodule ℂ V) := Submodule.finiteDimensional_inf_left S N
    obtain ⟨u, hu, hv⟩ := core (E := E) hσ (S ⊓ N) (fun k y hy => ⟨hS k y hy.1, hN k y hy.2⟩) ⟨hxS, hx⟩
    have he : (isoSp σ E).starProjection x = u := Submodule.eq_starProjection_of_mem_orthogonal hu.2 hv
    show (isoSp σ E).starProjection x ∈ N
    rw [he]
    exact hu.1.2
