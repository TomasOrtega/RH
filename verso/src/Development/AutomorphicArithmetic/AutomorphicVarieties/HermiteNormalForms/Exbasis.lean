import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulNeZeroLat

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

/- English proof (translation)
Introduce `L _ _ N M hM`. Take `⟨s, hs, hspan, hli⟩` from `exists_linearIndependent L (toL '' M)`. Establish `htop : (⊤ : Submodule L (Fin N → L)) ≤ Submodule.span L (Set.range ((↑) : s → Fin N → L))`. Rewrite using `[Subtype.range_coe, hspan]`. Conclude with `hM.ge`.

Set `B` to `Module.Basis.mk hli htop`. Use `haveI : Fintype s := @Fintype.ofFinite s (Module.Finite.finite_basis B)`. Establish `hcard : Fintype.card s = N`. Rewrite using `[← Module.finrank_eq_card_basis B, Module.finrank_fin_fun]`. Set `e : Fin N ≃ s` to `(Fintype.equivFinOfCardEq hcard).symm`.

Establish `hmem : ∀ a, ∃ y ∈ M, toL y = (e a : Fin N → L)` using `fun a => hs (e a).2`. Use `choose y hyM hy using hmem`. Use `⟨fun i a => y a i, ?_, fun a => hyM a⟩` and prove the remaining obligations. Introduce `h0`. Establish `hli' : LinearIndependent L (fun a => ((e a : s) : Fin N → L))` using `hli.comp e e.injective`.

Set `C : Matrix (Fin N) (Fin N) L` to `fun i a => ((e a : s) : Fin N → L) i`. Establish `hC : IsUnit C`. Rewrite using `[← Matrix.linearIndependent_cols_iff_isUnit]`. Conclude with `hli'`. Set `A : Matrix (Fin N) (Fin N) (𝓞 L)` to `fun i a => y a i`.

Establish `hCA : C = (algebraMap (𝓞 L) L).mapMatrix A`. Use extensionality with `i a`. Simplify using `only [C, A, RingHom.mapMatrix_apply, Matrix.map_apply, ← hy]`. Both sides reduce to the same expression. Establish `hdet : C.det = algebraMap (𝓞 L) L A.det`.

Rewrite using `[hCA]`. Conclude with `(RingHom.map_det (algebraMap (𝓞 L) L) A).symm`. Establish `h0' : A.det = 0` using `h0`. Rewrite `hdet` using `[h0', map_zero]`. Conclude with `(Matrix.isUnit_iff_isUnit_det C |>.mp hC).ne_zero hdet`.
-/
theorem UpperTheory.V.KT.exbasis :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (M : Set (Lat L N)), Spans M →
    ∃ A : Matrix (Fin N) (Fin N) (𝓞 L), A.det ≠ 0 ∧ ∀ a, (fun i => A i a) ∈ M := by
  intro L _ _ N M hM
  classical
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent L (toL '' M)
  have htop : (⊤ : Submodule L (Fin N → L)) ≤ Submodule.span L (Set.range ((↑) : s → Fin N → L)) := by
    rw [Subtype.range_coe, hspan]
    exact hM.ge
  let B := Module.Basis.mk hli htop
  haveI : Fintype s := @Fintype.ofFinite s (Module.Finite.finite_basis B)
  have hcard : Fintype.card s = N := by
    rw [← Module.finrank_eq_card_basis B, Module.finrank_fin_fun]
  let e : Fin N ≃ s := (Fintype.equivFinOfCardEq hcard).symm
  have hmem : ∀ a, ∃ y ∈ M, toL y = (e a : Fin N → L) := fun a => hs (e a).2
  choose y hyM hy using hmem
  refine ⟨fun i a => y a i, ?_, fun a => hyM a⟩
  intro h0
  have hli' : LinearIndependent L (fun a => ((e a : s) : Fin N → L)) := hli.comp e e.injective
  let C : Matrix (Fin N) (Fin N) L := fun i a => ((e a : s) : Fin N → L) i
  have hC : IsUnit C := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hli'
  let A : Matrix (Fin N) (Fin N) (𝓞 L) := fun i a => y a i
  have hCA : C = (algebraMap (𝓞 L) L).mapMatrix A := by
    ext i a
    simp only [C, A, RingHom.mapMatrix_apply, Matrix.map_apply, ← hy]
    rfl
  have hdet : C.det = algebraMap (𝓞 L) L A.det := by
    rw [hCA]
    exact (RingHom.map_det (algebraMap (𝓞 L) L) A).symm
  have h0' : A.det = 0 := h0
  rw [h0', map_zero] at hdet
  exact (Matrix.isUnit_iff_isUnit_det C |>.mp hC).ne_zero hdet
