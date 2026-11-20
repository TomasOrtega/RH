import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SpaceMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CmplPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoRes

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Introduce `O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a hstd X x hres`. Use `haveI := X.noeth`. Use `haveI := (co_res Λ).1`. Take `⟨R, _, _, _, f, hflat, hfx, huniv⟩` from `cmplPt x`. Establish `hmap : ∀ {S T : Type} [CommRing S] [Algebra Λ S] [CommRing T] [Algebra Λ T] (u : X.A →ₐ[Λ] S) (h : S →ₐ[Λ] T), (X.P.map (u : X.A →+* S)).map (h : S →+* T) = X.P.map ((h.comp u : X.A →ₐ[Λ] T) : X.A →+* T)` using `fun _ _ => rfl`.

Use `⟨R, inferInstance, inferInstance, inferInstance, f, ⟨⟨X.pair_map f, X.cont_map f, ?_⟩, ?_⟩, hflat, hfx⟩` and prove the remaining obligations. Rewrite using `[hmap, hfx]`. Introduce `R' _ _ _ P' hP'`. Take `⟨g, hg⟩` from `X.univ R' _ P' hres hP'`. Establish `hgx : (res Λ R').comp g = x`.

Apply `X.hom_ext` to reduce the goal to its premises. Rewrite using `[← hmap, hg, hP'.red]`. Take `⟨h, hh, hu⟩` from `huniv R' g hgx`. Use `⟨h, ?_, fun h' hh' => hu h' ?_⟩` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[hmap, hh, hg]`. Simplify using `only at hh' ⊢`. Apply `X.hom_ext` to reduce the goal to its premises. Rewrite using `[← hmap, hh', hg]`.
-/
theorem UpperTheory.V.Ws.cmplEx :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (Φ : Fr O Γ) (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] (a : O →+* Λ), Φ.Std l a → ∀ (X : Space Φ a) (x : X.A →ₐ[Λ] ResidueField Λ), Φ.IsRes ((residue Λ).comp a) (X.P.map (x : X.A →+* ResidueField Λ)) →
      ∃ (R : Type) (_ : CommRing R) (_ : Algebra Λ R) (_ : IsCO Λ R) (f : X.A →ₐ[Λ] R),
        Φ.IsDef a (X.P.map (x : X.A →+* ResidueField Λ)) (X.P.map (f : X.A →+* R)) ∧ (f : X.A →+* R).Flat ∧ (res Λ R).comp f = x := by
  intro O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a hstd X x hres
  haveI := X.noeth
  haveI := (co_res Λ).1
  obtain ⟨R, _, _, _, f, hflat, hfx, huniv⟩ := cmplPt x
  have hmap : ∀ {S T : Type} [CommRing S] [Algebra Λ S] [CommRing T] [Algebra Λ T]
      (u : X.A →ₐ[Λ] S) (h : S →ₐ[Λ] T),
      (X.P.map (u : X.A →+* S)).map (h : S →+* T) = X.P.map ((h.comp u : X.A →ₐ[Λ] T) : X.A →+* T) :=
    fun _ _ => rfl
  refine ⟨R, inferInstance, inferInstance, inferInstance, f, ⟨⟨X.pair_map f, X.cont_map f, ?_⟩, ?_⟩, hflat, hfx⟩
  · rw [hmap, hfx]
  · intro R' _ _ _ P' hP'
    obtain ⟨g, hg⟩ := X.univ R' _ P' hres hP'
    have hgx : (res Λ R').comp g = x := by
      apply X.hom_ext
      rw [← hmap, hg, hP'.red]
    obtain ⟨h, hh, hu⟩ := huniv R' g hgx
    refine ⟨h, ?_, fun h' hh' => hu h' ?_⟩
    · dsimp only
      rw [hmap, hh, hg]
    · dsimp only at hh' ⊢
      apply X.hom_ext
      rw [← hmap, hh', hg]
