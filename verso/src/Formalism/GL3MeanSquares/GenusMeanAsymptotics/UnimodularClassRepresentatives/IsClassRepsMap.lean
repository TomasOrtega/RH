import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
import Formalism.HermitianLattices.HermitianLatticesProofs.MassBasic

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.RankOne

open Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence

variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mass_eq_sum (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V)
    (s : Finset (Submodule (𝓞 K) V)) (hs : IsClassReps h L s) :
    mass h L = ∑ M ∈ s, ((Nat.card (autL h M) : ℕ) : ℝ)⁻¹ := by
  have hex : ∃ s, IsClassReps h L s := ⟨s, hs⟩
  rw [massBasic_mass_eq h L hex]
  apply Complex.ofReal_injective
  rw [massBasic_sum_cast, massBasic_sum_cast]
  exact latLiftIndep K V h L _ _ (fun _ _ _ => rfl) (fun _ _ _ => rfl) _ _ hex.choose_spec hs

section Transfer

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
  (Φ : Submodule (𝓞 K) V ≃ Submodule (𝓞 K) V') (τ : (V ≃ₗ[K] V) ≃ (V' ≃ₗ[K] V'))
  (hτ : ∀ g, τ g ∈ isom h' ↔ g ∈ isom h)
  (hg : ∀ g M, Φ (gmap g M) = gmap (τ g) (Φ M))
  (hloc : ∀ p : Ideal (𝓞 K), p.IsMaximal → ∀ M, Φ (loc (K := K) p M) = loc (K := K) p (Φ M))
  (hlat : ∀ M, Submodule.IsLattice K (Φ M) ↔ Submodule.IsLattice K M)

include hτ hg hloc hlat

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities.
-/
theorem mem_genus_iff (L M : Submodule (𝓞 K) V) : Φ M ∈ genus h' (Φ L) ↔ M ∈ genus h L := by
  unfold genus SameGenus
  simp only [Set.mem_ofPred_eq, hlat]
  refine and_congr_right fun _ => forall₂_congr fun p hp => ?_
  constructor
  · rintro ⟨g', hg', e⟩
    obtain ⟨g, rfl⟩ := τ.surjective g'
    refine ⟨g, (hτ g).1 hg', Φ.injective ?_⟩
    rw [hg, hloc p hp, hloc p hp, e]
  · rintro ⟨g, hg₁, e⟩
    refine ⟨τ g, (hτ g).2 hg₁, ?_⟩
    rw [← hloc p hp, ← hg, e, hloc p hp]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem isClassReps_map {L : Submodule (𝓞 K) V} {s : Finset (Submodule (𝓞 K) V)}
    (hs : IsClassReps h L s) : IsClassReps h' (Φ L) (s.map Φ.toEmbedding) := by
  constructor
  · intro N hN
    obtain ⟨M, hM, rfl⟩ := Finset.mem_map.1 hN
    exact (mem_genus_iff Φ τ hτ hg hloc hlat L M).2 (hs.1 M hM)
  · intro N hN
    obtain ⟨M, rfl⟩ := Φ.surjective N
    obtain ⟨M₀, ⟨hM₀, g, hg₀, e⟩, huniq⟩ := hs.2 M ((mem_genus_iff Φ τ hτ hg hloc hlat L M).1 hN)
    refine ⟨Φ M₀, ⟨Finset.mem_map.2 ⟨M₀, hM₀, rfl⟩, τ g, (hτ g).2 hg₀, by rw [← hg, e]⟩, ?_⟩
    rintro N₁ ⟨hN₁, g', hg', e'⟩
    obtain ⟨M₁, hM₁, rfl⟩ := Finset.mem_map.1 hN₁
    obtain ⟨g₁, rfl⟩ := τ.surjective g'
    have : M₁ = M₀ := huniq M₁ ⟨hM₁, g₁, (hτ g₁).1 hg', Φ.injective (by rw [hg]; exact e')⟩
    rw [this]; rfl

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem card_autL_eq (M : Submodule (𝓞 K) V) :
    Nat.card (autL h' (Φ M)) = Nat.card (autL h M) := by
  refine (Nat.card_congr (τ.subtypeEquiv fun g => ?_)).symm
  change (g ∈ isom h ∧ gmap g M = M) ↔ (τ g ∈ isom h' ∧ gmap (τ g) (Φ M) = Φ M)
  rw [hτ, ← hg, Φ.injective.eq_iff]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities.
-/
theorem mass_transfer {L : Submodule (𝓞 K) V} (hex : ∃ s, IsClassReps h L s) :
    (∃ s', IsClassReps h' (Φ L) s') ∧ mass h' (Φ L) = mass h L := by
  obtain ⟨s, hs⟩ := hex
  have hs' := isClassReps_map Φ τ hτ hg hloc hlat hs
  refine ⟨⟨_, hs'⟩, ?_⟩
  rw [mass_eq_sum h L s hs, mass_eq_sum h' _ _ hs', Finset.sum_map]
  refine Finset.sum_congr rfl fun M _ => ?_
  rw [Equiv.coe_toEmbedding, card_autL_eq Φ τ hτ hg hloc hlat M]

end Transfer

def mapE (φ : V ≃ₗ[K] V') : Submodule (𝓞 K) V ≃ Submodule (𝓞 K) V' :=
  (Submodule.orderIsoMapComap (φ.restrictScalars (𝓞 K))).toEquiv

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem mem_mapE (φ : V ≃ₗ[K] V') (M : Submodule (𝓞 K) V) (y : V') :
    y ∈ mapE φ M ↔ φ.symm y ∈ M := by
  change y ∈ M.map ((φ.restrictScalars (𝓞 K)) : V →ₗ[𝓞 K] V') ↔ _
  rw [Submodule.mem_map_equiv]; rfl

def conjE (φ : V ≃ₗ[K] V') : (V ≃ₗ[K] V) ≃ (V' ≃ₗ[K] V') where
  toFun g := (φ.symm.trans g).trans φ
  invFun g := (φ.trans g).trans φ.symm
  left_inv g := by ext x; simp
  right_inv g := by ext x; simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem conjE_apply (φ : V ≃ₗ[K] V') (g : V ≃ₗ[K] V) (y : V') :
    conjE φ g y = φ (g (φ.symm y)) := rfl

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem mem_gmap (g : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V) (y : V) :
    y ∈ gmap g M ↔ g.symm y ∈ M := by
  change y ∈ M.map ((g.restrictScalars (𝓞 K)) : V →ₗ[𝓞 K] V) ↔ _
  rw [Submodule.mem_map_equiv]; rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isLattice_mapE (φ : V ≃ₗ[K] V') {M : Submodule (𝓞 K) V} (hM : Submodule.IsLattice K M) :
    Submodule.IsLattice K (mapE φ M) := by
  constructor
  · exact hM.fg.map _
  · have e : ((mapE φ M : Submodule (𝓞 K) V') : Set V') = (φ : V →ₗ[K] V') '' (M : Set V) := rfl
    rw [e, Submodule.span_image, hM.span_eq_top, Submodule.map_top, LinearEquiv.range]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem mapE_symm_mapE (φ : V ≃ₗ[K] V') (M : Submodule (𝓞 K) V) : mapE φ.symm (mapE φ M) = M := by
  ext x; simp [mem_mapE]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem mass_mapE (φ : V ≃ₗ[K] V') {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
    (hφ : ∀ x y, h' (φ x) (φ y) = h x y) {L : Submodule (𝓞 K) V}
    (hex : ∃ s, IsClassReps h L s) :
    (∃ s', IsClassReps h' (mapE φ L) s') ∧ mass h' (mapE φ L) = mass h L := by
  refine mass_transfer (mapE φ) (conjE φ) ?_ ?_ ?_ ?_ hex
  · intro g
    constructor
    · intro H x y
      have := H (φ x) (φ y)
      simpa [conjE_apply, hφ] using this
    · intro H x y
      obtain ⟨x, rfl⟩ := φ.surjective x
      obtain ⟨y, rfl⟩ := φ.surjective y
      simp only [conjE_apply, LinearEquiv.symm_apply_apply, hφ]
      exact H x y
  · intro g M
    ext y
    rw [mem_mapE, mem_gmap, mem_gmap, mem_mapE]
    have e : (conjE φ g).symm y = φ (g.symm (φ.symm y)) := rfl
    rw [e, LinearEquiv.symm_apply_apply]
  · intro p _ M
    ext y
    rw [mem_mapE]
    change (∃ s ∈ hcompl (K := K) p, s • φ.symm y ∈ M) ↔ (∃ s ∈ hcompl (K := K) p, s • y ∈ mapE φ M)
    refine exists_congr fun s => and_congr_right fun _ => ?_
    rw [mem_mapE]
    have : φ.symm (s • y) = s • φ.symm y := (φ.symm.restrictScalars (𝓞 K)).map_smul s y
    rw [this]
  · intro M
    refine ⟨fun H => ?_, isLattice_mapE φ⟩
    have := isLattice_mapE φ.symm H
    rwa [mapE_symm_mapE] at this

end Formalism.HermitianLattices.Ext.L3.RankOne
