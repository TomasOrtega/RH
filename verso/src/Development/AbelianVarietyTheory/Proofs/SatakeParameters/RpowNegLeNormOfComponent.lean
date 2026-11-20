import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeSplitOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatakeBoundOfIsometricSphericalGLStatement
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.SmallRowEigenvalues

noncomputable section

namespace GlobalTheory.RowSatakeBound

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.LatHecke

section Local

variable (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K]

def IsUnitarySatake (r : ℕ) (β : Multiset ℂ) : Prop :=
  β.card = r ∧
  ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V)
    (ρ : Representation ℂ (GL (Fin r) K) V) (v : V),
    (∀ g x, ‖ρ g x‖ = ‖x‖) ∧ v ≠ 0 ∧
    (∀ g, glMap g (std O K r).1 = (std O K r).1 → ρ g v = v) ∧
    ∀ k ≤ r, ∀ s : Finset (GL (Fin r) K),
      Set.BijOn (fun g => glMap g (std O K r).1) s (Subtype.val '' subElem k (std O K r)) →
      ∑ g ∈ s, ρ g v =
        ((((qRes O : ℝ) ^ ((k : ℝ) * ((r : ℝ) - k) / 2) : ℝ) : ℂ) * β.esymm k) • v

/- English proof (translation)
Use `⟨rfl, ℂ, inferInstance, inferInstance, Representation.trivial ℂ _ ℂ, 1, fun g x => by simp, one_ne_zero, fun g _ => by simp, fun k hk s hs => ?_⟩` and prove the remaining obligations. Establish `hcard : s.card = 1`. Establish `h1` using `hs.ncard_eq`. Rewrite `h1` using `[Set.ncard_coe_finset]`. Rewrite using `[h1]`.

Use `interval_cases k`. Rewrite using `[subElem_zero]`. Conclude with `(Set.ncard_image_of_injective _ Subtype.val_injective).trans (Set.ncard_singleton _)`. Rewrite using `[subElem_top]`. Conclude with `(Set.ncard_image_of_injective _ Subtype.val_injective).trans (Set.ncard_singleton _)`.

Use `interval_cases k`. Simplify using `[hcard, Multiset.esymm]`. Simplify using `[hcard, Multiset.esymm, Multiset.powersetCard_one]`.
-/
theorem isUnitarySatake_one : IsUnitarySatake O K 1 {1} := by
  refine ⟨rfl, ℂ, inferInstance, inferInstance, Representation.trivial ℂ _ ℂ, 1,
    fun g x => by simp, one_ne_zero, fun g _ => by simp, fun k hk s hs => ?_⟩
  have hcard : s.card = 1 := by
    have h1 := hs.ncard_eq
    rw [Set.ncard_coe_finset] at h1
    rw [h1]
    interval_cases k
    · rw [subElem_zero]
      exact (Set.ncard_image_of_injective _ Subtype.val_injective).trans (Set.ncard_singleton _)
    · rw [subElem_top]
      exact (Set.ncard_image_of_injective _ Subtype.val_injective).trans (Set.ncard_singleton _)
  interval_cases k
  · simp [hcard, Multiset.esymm]
  · simp [hcard, Multiset.esymm, Multiset.powersetCard_one]

variable {O K}

/- English proof (translation)
Take `⟨hc, V, _, _, ρ, v, hρ, hv, hfix, hT⟩` from `h`. Conclude with `GlobalTheory.T.satake_bound_of_isometric_sphericalGL O K r V ρ v β hc hρ hv hfix hT`.
-/
theorem IsUnitarySatake.norm_le {r : ℕ} {β : Multiset ℂ} (h : IsUnitarySatake O K r β) :
    ∀ b ∈ β, ‖b‖ ≤ (qRes O : ℝ) ^ (((r : ℝ) - 1) / 2) := by
  obtain ⟨hc, V, _, _, ρ, v, hρ, hv, hfix, hT⟩ := h
  exact GlobalTheory.T.satake_bound_of_isometric_sphericalGL O K r V ρ v β hc hρ hv hfix hT

end Local

section Completion

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

/- English proof (translation)
The claim follows from `Formalism.UG.P.tjcosets_finite w`.
-/
theorem finite_residue : Finite (IsLocalRing.ResidueField (w.adicCompletionIntegers E)) :=
  Formalism.UG.P.tjcosets_finite w

/- English proof (translation)
Unfold `qRes normV`. Rewrite using `[Formalism.UG.P.tjcosets_card_residue, Formalism.UG.qV, Ideal.absNorm_apply, Submodule.cardQuot_apply]`.
-/
theorem qRes_eq_normV [Finite (IsLocalRing.ResidueField (w.adicCompletionIntegers E))] :
    qRes (w.adicCompletionIntegers E) = normV w := by
  unfold qRes normV
  rw [Formalism.UG.P.tjcosets_card_residue, Formalism.UG.qV, Ideal.absNorm_apply, Submodule.cardQuot_apply]

def IsUnitarySatakeAt (r : ℕ) (β : Multiset ℂ) : Prop :=
  haveI := finite_residue w
  IsUnitarySatake (w.adicCompletionIntegers E) (w.adicCompletion E) r β

variable {w}

/- English proof (translation)
Use `finite_residue w` as an intermediate fact. Rewrite using `[← qRes_eq_normV w]`. Conclude with `IsUnitarySatake.norm_le h`.
-/
theorem IsUnitarySatakeAt.norm_le {r : ℕ} {β : Multiset ℂ} (h : IsUnitarySatakeAt w r β) :
    ∀ b ∈ β, ‖b‖ ≤ ((normV w : ℕ) : ℝ) ^ (((r : ℝ) - 1) / 2) := by
  have := finite_residue w
  rw [← qRes_eq_normV w]
  exact IsUnitarySatake.norm_le h

end Completion

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def UnitarySphericalComponent : Prop :=
  ∀ (i : N.Loc) (σ : what₂.FT), what₂.isot (N.j i) σ ≠ ⊥ →
    ∀ w : PlE H, IsSplitPl H w → A.unr (A.locW i σ w) →
      IsUnitarySatakeAt w R.r ((A.frobEig (A.locW i σ w)).map (·⁻¹)) ∧
      IsUnitarySatakeAt w R.r (A.frobEig (A.locW i σ w))

/- English proof (translation)
Introduce `i σ hσ w hw hu` and use `(h i σ hσ w hw hu).2.norm_le`.
-/
theorem rowSizeLe_of_component (h : UnitarySphericalComponent N A) :
    GlobalTheory.ThetaExh.RowSizeLe N A :=
  fun i σ hσ w hw hu => (h i σ hσ w hw hu).2.norm_le

/- English proof (translation)
Establish `h1` using `(h i σ hσ w hw hu).1.norm_le α⁻¹ (Multiset.mem_map_of_mem _ hα)`. Establish `h0 : α ≠ 0` using `fun e => A.frobEig_ne_zero _ hu (e ▸ hα)`. Rewrite `h1` using `[norm_inv]`. Rewrite using `[Real.rpow_neg (Nat.cast_nonneg _)]`. Conclude with `inv_le_of_inv_le₀ (norm_pos_iff.2 h0) h1`.
-/
theorem rpow_neg_le_norm_of_component (h : UnitarySphericalComponent N A)
    (i : N.Loc) (σ : what₂.FT) (hσ : what₂.isot (N.j i) σ ≠ ⊥) (w : PlE H) (hw : IsSplitPl H w)
    (hu : A.unr (A.locW i σ w)) (α : ℂ) (hα : α ∈ A.frobEig (A.locW i σ w)) :
    ((normV w : ℕ) : ℝ) ^ (-(((R.r : ℝ) - 1) / 2)) ≤ ‖α‖ := by
  have h1 := (h i σ hσ w hw hu).1.norm_le α⁻¹ (Multiset.mem_map_of_mem _ hα)
  have h0 : α ≠ 0 := fun e => A.frobEig_ne_zero _ hu (e ▸ hα)
  rw [norm_inv] at h1
  rw [Real.rpow_neg (Nat.cast_nonneg _)]
  exact inv_le_of_inv_le₀ (norm_pos_iff.2 h0) h1

/- English proof (translation)
Introduce `_ _ _ N A h` and use `GlobalTheory.IndefiniteRowSideFullHecke.SmallBlockEigenvalues.rowEigSmall_of_le N A (rowSizeLe_of_component N A h)`.
-/
theorem rowEigSmall_of_component : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R)
    (N : NData R H what₂) (A : NAut N),
    UnitarySphericalComponent N A → GlobalTheory.IndefiniteRowSideFullHecke.SmallBlockEigenvalues.RowEigSmall N A :=
  fun _ _ _ N A h => GlobalTheory.IndefiniteRowSideFullHecke.SmallBlockEigenvalues.rowEigSmall_of_le N A (rowSizeLe_of_component N A h)

/- English proof (translation)
The claim follows from `rowEigSmall_of_component _ _ _ N A h`.
-/
theorem rowSize_of_component (h : UnitarySphericalComponent N A) : GlobalTheory.ThetaExh.RowSize N A :=
  rowEigSmall_of_component _ _ _ N A h

end GlobalTheory.RowSatakeBound
