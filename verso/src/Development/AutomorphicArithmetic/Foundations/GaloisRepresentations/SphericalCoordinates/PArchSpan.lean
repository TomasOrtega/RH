import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LineBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveRealTensorToProdMatrixAlgebrasInfPlaces
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SumOverPlacesFibre

noncomputable section

open NumberField

namespace UpperTheory.Gal.W2

/- English proof (translation)
Rewrite using `[← InfinitePlace.card_add_two_mul_card_eq_rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero F]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem two_mul_card_places (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] :
    2 * Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
  rw [← InfinitePlace.card_add_two_mul_card_eq_rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero F]
  ring

open scoped Classical in
/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.SumOverPlacesFibre.sum_fibre_place F x v`.
-/
private theorem sum_fibre_place (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] (x : F)
    (v : InfinitePlace F) :
    ∑ φ : F →+* ℂ with InfinitePlace.mk φ = v, φ x = ((2 * (v.embedding x).re : ℝ) : ℂ) :=
  _root_.UpperTheory.Reformulated.B.SumOverPlacesFibre.sum_fibre_place F x v

/- English proof (translation)
Establish `h1 : ((Algebra.trace ℚ F x : ℚ) : ℂ) = ∑ φ : F →+* ℂ, φ x`. Establish `h` using `trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := x)`. Rewrite `h` using `[eq_ratCast]`. Set `e : (F →ₐ[ℚ] ℂ) ≃ (F →+* ℂ)` to `{ toFun := fun σ => σ.toRingHom invFun := fun φ => φ.toRatAlgHom left_inv := fun σ => by ext a; rfl right_inv := fun φ => by ext a; rfl }`. Conclude with `h.trans (Fintype.sum_equiv e _ _ fun _ => rfl)`.

Establish `h2 : ∑ φ : F →+* ℂ, φ x = ∑ v : InfinitePlace F, ∑ φ : F →+* ℂ with InfinitePlace.mk φ = v, φ x` using `(Finset.sum_fiberwise _ _ _).symm`. Establish `h3 : ((Algebra.trace ℚ F x : ℚ) : ℂ) = ((∑ v : InfinitePlace F, 2 * (v.embedding x).re : ℝ) : ℂ)`. Rewrite using `[h1, h2, Finset.sum_congr rfl fun v _ => sum_fibre_place F x v, Complex.ofReal_sum]`. Establish `h4 : (((Algebra.trace ℚ F x : ℚ) : ℝ) : ℂ) = ((Algebra.trace ℚ F x : ℚ) : ℂ)`. Use `push_cast`.

Both sides reduce to the same expression. Conclude with `Complex.ofReal_injective (h4.trans h3)`.
-/
private theorem trace_eq_sum_places (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] (x : F) :
    ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ v : InfinitePlace F, 2 * (v.embedding x).re := by
  classical
  have h1 : ((Algebra.trace ℚ F x : ℚ) : ℂ) = ∑ φ : F →+* ℂ, φ x := by
    have h := trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := x)
    rw [eq_ratCast] at h
    let e : (F →ₐ[ℚ] ℂ) ≃ (F →+* ℂ) :=
      { toFun := fun σ => σ.toRingHom
        invFun := fun φ => φ.toRatAlgHom
        left_inv := fun σ => by ext a; rfl
        right_inv := fun φ => by ext a; rfl }
    exact h.trans (Fintype.sum_equiv e _ _ fun _ => rfl)
  have h2 : ∑ φ : F →+* ℂ, φ x =
      ∑ v : InfinitePlace F, ∑ φ : F →+* ℂ with InfinitePlace.mk φ = v, φ x :=
    (Finset.sum_fiberwise _ _ _).symm
  have h3 : ((Algebra.trace ℚ F x : ℚ) : ℂ) = ((∑ v : InfinitePlace F, 2 * (v.embedding x).re : ℝ) : ℂ) := by
    rw [h1, h2, Finset.sum_congr rfl fun v _ => sum_fibre_place F x v, Complex.ofReal_sum]
  have h4 : (((Algebra.trace ℚ F x : ℚ) : ℝ) : ℂ) = ((Algebra.trace ℚ F x : ℚ) : ℂ) := by
    push_cast
    rfl
  exact Complex.ofReal_injective (h4.trans h3)

/- English proof (translation)
Use `eq_top_iff.2 fun y _ => ?_` and prove the remaining obligations. Use `set T := Submodule.span ℝ (Set.range fun (x : Fin n → F) (v : InfinitePlace F) (i : Fin n) => v.embedding (x i)) with hT`. Establish `hs : ∀ (i : Fin n) (g : InfinitePlace F → ℂ), (fun v => Pi.single i (g v) : InfinitePlace F → Fin n → ℂ) ∈ T`. Introduce `i g`. Set `S : (InfinitePlace F → ℂ) →ₗ[ℝ] (InfinitePlace F → Fin n → ℂ)` to `{ toFun := fun g v => Pi.single i (g v) map_add' := fun a b => by funext v; simp [Pi.single_add] map_smul' := fun r a => by`.

Use function extensionality and compare the values at `v j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h] }`.

Establish `hle : Submodule.span ℝ (Set.range fun (a : F) (v : InfinitePlace F) => v.embedding a) ≤ T.comap S`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨a, rfl⟩`. Use `Submodule.subset_span ⟨Pi.single i a, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `v j`.

Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using `[S]`. Simplify using `[S, h]`. Conclude with `hle (by rw [GlobalTheory.LKTrip.HTGroup.span_real_embedding_places]; trivial)`.

Establish `hy : y = ∑ i : Fin n, fun v => (Pi.single i (y v i) : Fin n → ℂ)`. Use function extensionality and compare the values at `v j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Rewrite using `[hy]`. Conclude with `Submodule.sum_mem _ fun i _ => hs i fun v => y v i`.
-/
private theorem span_top (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] (n : ℕ) :
    Submodule.span ℝ (Set.range fun (x : Fin n → F) (v : InfinitePlace F) (i : Fin n) =>
      v.embedding (x i)) = ⊤ := by
  classical
  refine eq_top_iff.2 fun y _ => ?_
  set T := Submodule.span ℝ (Set.range fun (x : Fin n → F) (v : InfinitePlace F) (i : Fin n) =>
    v.embedding (x i)) with hT
  have hs : ∀ (i : Fin n) (g : InfinitePlace F → ℂ),
      (fun v => Pi.single i (g v) : InfinitePlace F → Fin n → ℂ) ∈ T := by
    intro i g
    let S : (InfinitePlace F → ℂ) →ₗ[ℝ] (InfinitePlace F → Fin n → ℂ) :=
      { toFun := fun g v => Pi.single i (g v)
        map_add' := fun a b => by funext v; simp [Pi.single_add]
        map_smul' := fun r a => by
          funext v j
          by_cases h : j = i
          · subst h
            simp
          · simp [h] }
    have hle : Submodule.span ℝ (Set.range fun (a : F) (v : InfinitePlace F) => v.embedding a) ≤
        T.comap S := by
      rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      refine Submodule.subset_span ⟨Pi.single i a, ?_⟩
      funext v j
      by_cases h : j = i
      · subst h
        simp [S]
      · simp [S, h]
    exact hle (by rw [GlobalTheory.LKTrip.HTGroup.span_real_embedding_places]; trivial)
  have hy : y = ∑ i : Fin n, fun v => (Pi.single i (y v i) : Fin n → ℂ) := by
    funext v j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hy]
  exact Submodule.sum_mem _ fun i _ => hs i fun v => y v i

/- English proof (translation)
Introduce `F _ _ _ n`. Use `⟨span_top F n, ?_, trace_eq_sum_places F⟩` and prove the remaining obligations. Rewrite using `[Module.finrank_pi_fintype]`. Simplify using `only [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]`. Rewrite using `[← two_mul_card_places F]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem archSpan_of : ArchSpan := by
  intro F _ _ _ n
  refine ⟨span_top F n, ?_, trace_eq_sum_places F⟩
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  rw [← two_mul_card_places F]
  ring

end UpperTheory.Gal.W2
