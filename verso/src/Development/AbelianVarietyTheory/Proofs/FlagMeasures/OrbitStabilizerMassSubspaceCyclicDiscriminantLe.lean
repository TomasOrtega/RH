import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Formalism.HermitianLattices.HermitianLatticesProofs.IsomAct
import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitStabilizerMassEqWeightedSumFibresStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitStabilizerMassProdEqMulStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitWeightedStabilizerSumMonoSubadditiveStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianGenusMassEqOrbitStabilizerMassStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDiscriminantOrderNeZeroUnimodulaStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeQuotientGensAndIntermediateCountStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteUnitaryStabilizerSubspaceProdStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimitiveHermitianSublatticeDiscriminantGeneratoStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardHermitianLatticesGluedSubspaceComplementStatement

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.FixedSub

section

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem smul_def' (h : V →ₗ⋆[K] V →ₗ[K] K) (g : isom h) (L : Submodule (𝓞 K) V) :
    g • L = gmap (g : V ≃ₗ[K] V) L := rfl

/- English proof (translation)
Establish `H` using `isomAct (𝓞 K) K V h g g.2 L`. Conclude with `⟨H.2.2.2.2.2 hL.1, H.2.2.1.2 hL.2⟩`.
-/
theorem isIntLat_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (g : isom h) (L : Submodule (𝓞 K) V)
    (hL : IsIntLat h L) : IsIntLat h (g • L) := by
  have H := isomAct (𝓞 K) K V h g g.2 L
  exact ⟨H.2.2.2.2.2 hL.1, H.2.2.1.2 hL.2⟩

/- English proof (translation)
The claim follows from `(isomAct (𝓞 K) K V h g g.2 L).1`.
-/
theorem dual_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (g : isom h) (L : Submodule (𝓞 K) V) :
    dual h (g • L) = g • dual h L := (isomAct (𝓞 K) K V h g g.2 L).1

/- English proof (translation)
Unfold `discN`. Rewrite using `[dual_smul]`. Unfold `idxN`. Conclude with `AddSubgroup.relIndex_map_map_of_injective (f := ((g : V ≃ₗ[K] V) : V →+ V)) L.toAddSubgroup (dual h L).toAddSubgroup (g : V ≃ₗ[K] V).injective`.
-/
theorem discN_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (g : isom h) (L : Submodule (𝓞 K) V) :
    discN h (g • L) = discN h L := by
  unfold discN
  rw [dual_smul]
  unfold idxN
  exact AddSubgroup.relIndex_map_map_of_injective (f := ((g : V ≃ₗ[K] V) : V →+ V))
    L.toAddSubgroup (dual h L).toAddSubgroup (g : V ≃ₗ[K] V).injective

/- English proof (translation)
Introduce `g L hL` and use `⟨isIntLat_smul h g L hL.1, (discN_smul h g L).trans hL.2⟩`.
-/
theorem stable_latsDisc (h : V →ₗ⋆[K] V →ₗ[K] K) (n : ℕ) :
    Stable (isom h) (latsDisc (R := 𝓞 K) h n) := fun g L hL =>
  ⟨isIntLat_smul h g L hL.1, (discN_smul h g L).trans hL.2⟩

/- English proof (translation)
Take `⟨t, ht, H⟩` from `H`. Use `⟨t.image (g : V ≃ₗ[K] V), Finset.card_image_le.trans ht, ?_⟩` and prove the remaining obligations. Rewrite using `[dual_smul, H, smul_def', smul_def']`. Unfold `gmap`. Rewrite using `[Submodule.map_sup, Submodule.map_span, Finset.coe_image]`.

Both sides reduce to the same expression.
-/
theorem gens_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (g : isom h) (L : Submodule (𝓞 K) V) (e : ℕ)
    (H : ∃ t : Finset V, t.card ≤ e ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set V)) :
    ∃ t : Finset V, t.card ≤ e ∧ dual h (g • L) = g • L ⊔ Submodule.span (𝓞 K) (t : Set V) := by
  obtain ⟨t, ht, H⟩ := H
  refine ⟨t.image (g : V ≃ₗ[K] V), Finset.card_image_le.trans ht, ?_⟩
  rw [dual_smul, H, smul_def', smul_def']
  unfold gmap
  rw [Submodule.map_sup, Submodule.map_span, Finset.coe_image]
  rfl

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
/- English proof (translation)
Assemble the required witnesses or components as `⟨fun x y => hs.eq (x : V) (y : V)⟩`.
-/
theorem hRes_symm (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (U : Submodule K V) :
    (hRes h U).IsSymm := ⟨fun x y => hs.eq (x : V) (y : V)⟩

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
/- English proof (translation)
Introduce `τ x hx` and use `hp τ (x : V) (fun e => hx (Subtype.ext e))`.
-/
theorem hRes_pd (h : V →ₗ⋆[K] V →ₗ[K] K) (hp : PD h) (U : Submodule K V) :
    PD (hRes h U) := fun τ x hx => hp τ (x : V) (fun e => hx (Subtype.ext e))

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
/- English proof (translation)
Take `⟨τ⟩ : Nonempty (K →+* ℂ)` from `inferInstance`. Prove the components needed by the constructor for the conclusion. Introduce `x hx`. Assume the negation of the conclusion as `h0`. Use `hp τ x h0` as an intermediate fact.

Rewrite `this` using `[hx x]`. Simplify using `at this`. Introduce `x hx`. Assume the negation of the conclusion as `h0`. Use `hp τ x h0` as an intermediate fact.

Rewrite `this` using `[hx x]`. Simplify using `at this`.
-/
theorem pd_nondeg (h : V →ₗ⋆[K] V →ₗ[K] K) (hp : PD h) : h.Nondegenerate := by
  obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
  constructor
  · intro x hx
    by_contra h0
    have := hp τ x h0
    rw [hx x] at this
    simp at this
  · intro x hx
    by_contra h0
    have := hp τ x h0
    rw [hx x] at this
    simp at this

omit [NumberField K] in
/- English proof (translation)
Establish `: IsIntegral ℤ (star (algebraMap (𝓞 K) K r))` using `(RingOfIntegers.isIntegral_coe r).map (starRingEnd K).toIntAlgHom`. Conclude with `⟨⟨_, this⟩, rfl⟩`.
-/
theorem star_int (r : 𝓞 K) : star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) := by
  have : IsIntegral ℤ (star (algebraMap (𝓞 K) K r)) :=
    (RingOfIntegers.isIntegral_coe r).map (starRingEnd K).toIntAlgHom
  exact ⟨⟨_, this⟩, rfl⟩

/- English proof (translation)
Establish `hnd` using `pd_nondeg h hp`. Establish `h0` using `(GlobalTheory.T.hermitianLatticeDiscriminantOrder_ne_zero_unimodular K V h hK hs hnd L hL).1`. Establish `hle : L ≤ dual h L` using `fun x hx => (isomAct_mem_dual h L x).2 fun y hy => hL.2 y hy x hx`. Conclude with `(GlobalTheory.T.lattice_quotient_gens_and_intermediate_count K V L (dual h L) hle h0).1 (dualLattice (𝓞 K) K V h hs hnd star_int L hL.1).1.fg`.
-/
theorem gens_rank [FiniteDimensional K V] (hK : IsCMUnram K) (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hs : h.IsSymm) (hp : PD h) (L : Submodule (𝓞 K) V) (hL : IsIntLat h L) :
    ∃ t : Finset V, t.card ≤ Module.finrank K V ∧
      dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set V) := by
  have hnd := pd_nondeg h hp
  have h0 := (GlobalTheory.T.hermitianLatticeDiscriminantOrder_ne_zero_unimodular K V h hK hs hnd L hL).1
  have hle : L ≤ dual h L := fun x hx => (isomAct_mem_dual h L x).2 fun y hy => hL.2 y hy x hx
  exact (GlobalTheory.T.lattice_quotient_gens_and_intermediate_count K V L (dual h L) hle h0).1
    (dualLattice (𝓞 K) K V h hs hnd star_int L hL.1).1.fg

end

/- English proof (translation)
Introduce `K V _ _ _ _ _ _ _ _ h hK hs hp U n N₀`. Take `⟨φ, hφ⟩` from `GlobalTheory.T.definite_unitary_stabilizer_subspace_prod K V h hK hs hp U`. Establish `hs1` using `hRes_symm h hs U`. Establish `hp1` using `hRes_pd h hp U`. Establish `hs2` using `hRes_symm h hs (perp h U)`.

Establish `hp2` using `hRes_pd h hp (perp h U)`. Use `letI act : MulAction (MulAction.stabilizer (isom h) U) (Submodule (𝓞 K) U × Submodule (𝓞 K) (perp h U)) := { smul := fun γ p => ((φ γ).1 • p.1, (φ γ).2 • p.2) one_smul := fun p => by`. Express the relevant statement in the definitionally equal form `((φ 1).1 • p.1, (φ 1).2 • p.2) = p`. Simplify using the standard rewrite rules. Use `mul_smul := fun a b p => by`.

Express the relevant statement in the definitionally equal form `((φ (a * b)).1 • p.1, (φ (a * b)).2 • p.2) = ((φ a).1 • ((φ b).1 • p.1), (φ a).2 • ((φ b).2 • p.2))`. Simplify using `[mul_smul] }`. Establish `hact : ∀ (γ : MulAction.stabilizer (isom h) U) (p : Submodule (𝓞 K) U × Submodule (𝓞 K) (perp h U)), γ • p = ((φ γ).1 • p.1, (φ γ).2 • p.2)` using `fun _ _ => rfl`. Use `set X : Set (Submodule (𝓞 K) V) := {L : Submodule (𝓞 K) V | IsIntLat h L ∧ discN h L = N₀ ∧ (∃ t : Finset V, t.card ≤ 1 ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set _)) ∧ discN (hRes h U) (latIn U L) = n} with hX`. Use `set A : Set (Submodule (𝓞 K) U) := latsDisc (R := 𝓞 K) (hRes h U) n with hA`.

Use `set B : Set (Submodule (𝓞 K) (perp h U)) := ⋃ n' ∈ Finset.Icc 1 (n * N₀), latsDisc (R := 𝓞 K) (hRes h (perp h U)) n' with hB`. Establish `memB : ∀ M, M ∈ B ↔ IsIntLat (hRes h (perp h U)) M ∧ 1 ≤ discN (hRes h (perp h U)) M ∧ discN (hRes h (perp h U)) M ≤ n * N₀`. Introduce `M`. Simplify using `only [hB, Set.mem_iUnion, Finset.mem_Icc, latsDisc, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨i, hi, h1, rfl⟩`. Conclude with `⟨h1, hi⟩`. Introduce and unpack `⟨h1, hi⟩`. Conclude with `⟨_, hi, h1, rfl⟩`. Establish `sA : Stable (isom (hRes h U)) A` using `stable_latsDisc _ n`.

Establish `sB : Stable (isom (hRes h (perp h U))) B`. Introduce `g M hM`. Rewrite `hM`, the goal using `[memB]`. Rewrite using `[discN_smul]`. Conclude with `⟨isIntLat_smul _ g M hM.1, hM.2⟩`.

Establish `fA : ∀ M ∈ A, Finite (MulAction.stabilizer (isom (hRes h U)) M)` using `fun M hM => (GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K U (hRes h U) hK hs1 hp1 M hM.1.1).2.2.2.1 M hM.1.1`. Establish `fB : ∀ M ∈ B, Finite (MulAction.stabilizer (isom (hRes h (perp h U))) M)` using `fun M hM => (GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K (perp h U) (hRes h (perp h U)) hK hs2 hp2 M ((memB M).1 hM).1.1).2.2.2.1 M ((memB M).1 hM).1.1`. Establish `sX : Stable (MulAction.stabilizer (isom h) U) X`. Introduce and unpack `γ L ⟨h1, h2, h3, h4⟩`. Use `⟨isIntLat_smul h γ.1 L h1, (discN_smul h γ.1 L).trans h2, gens_smul h γ.1 L 1 h3, ?_⟩` and prove the remaining obligations.

Rewrite using `[(hφ γ L).1, discN_smul, h4]`. Establish `sY : Stable (MulAction.stabilizer (isom h) U) (A ×ˢ B)`. Introduce and unpack `γ p ⟨h1, h2⟩`. Conclude with `⟨sA _ _ h1, sB _ _ h2⟩`. Establish `mp : Set.MapsTo (fun L : Submodule (𝓞 K) V => (latIn U L, latIn (perp h U) L)) X (A ×ˢ B)`.

Introduce and unpack `L ⟨h1, h2, h3, h4⟩`. Take `⟨k1, k2, k3, -⟩` from `GlobalTheory.T.primitive_hermitian_sublattice_discriminant_generators K V h hK hs hp L U 1 h1 h3`. Use `⟨⟨k1, h4⟩, (memB _).2 ⟨k2, ?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `Nat.one_le_iff_ne_zero.2 (GlobalTheory.T.hermitianLatticeDiscriminantOrder_ne_zero_unimodular K (perp h U) _ hK hs2 (pd_nondeg _ hp2) _ k2).1`. Rewrite `k3` using `[h2, h4]`.

Conclude with `k3`. Establish `fY : ∀ p ∈ A ×ˢ B, Finite (MulAction.stabilizer (MulAction.stabilizer (isom h) U) p)`. Introduce and unpack `p ⟨h1, h2⟩`. Use `haveI := fA _ h1`. Use `haveI := fB _ h2`.

Use `Finite.of_injective (β := MulAction.stabilizer (isom (hRes h U)) p.1 × MulAction.stabilizer (isom (hRes h (perp h U))) p.2) (fun γ => (⟨(φ γ.1).1, congrArg Prod.fst γ.2⟩, ⟨(φ γ.1).2, congrArg Prod.snd γ.2⟩)) ?_` and prove the remaining obligations. Introduce `a b e`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `φ.injective` to reduce the goal to its premises. Conclude with `Prod.ext (congrArg (fun q => q.1.1) e) (congrArg (fun q => q.2.1) e)`.

Establish `e1` using `GlobalTheory.T.orbitStabilizerMass_eq_weightedSum_fibres (MulAction.stabilizer (isom h) U) _ _ X (A ×ˢ B) (fun L : Submodule (𝓞 K) V => (latIn U L, latIn (perp h U) L)) (fun γ L => Prod.ext (hφ γ L).1 (hφ γ L).2) sX sY mp fY`. Establish `e2` using `GlobalTheory.T.orbitStabilizerMass_prod_eq_mul (MulAction.stabilizer (isom h) U) _ _ _ _ φ A B hact sA sB fA fB`. Establish `e3 : orbMass (isom (hRes h (perp h U))) B ≤ ∑ n' ∈ Finset.Icc 1 (n * N₀), orbMass (isom (hRes h (perp h U))) (latsDisc (R` using `𝓞 K) (hRes h (perp h U)) n') := (GlobalTheory.T.orbitWeightedStabilizerSum_mono_subadditive (isom (hRes h (perp h U))) (Submodule (𝓞 K) (perp h U))).2.2.1 ℕ _ B _ _ subset_rfl`. Take `⟨m1, m2, -⟩` from `GlobalTheory.T.orbitWeightedStabilizerSum_mono_subadditive (MulAction.stabilizer (isom h) U) (Submodule (𝓞 K) U × Submodule (𝓞 K) (perp h U))`. Rewrite using `[e1]`.

Use `(m1 _ (A ×ˢ B) _ (fun _ => (((n * (n * N₀)) ^ (2 * Module.finrank K (perp h U) + 1) : ℕ) : ℝ≥0∞)) subset_rfl ?_).trans ?_` and prove the remaining obligations. Introduce and unpack `⟨M, M'⟩ ⟨h1, h2⟩`. Break down `(X ∩ (fun L : Submodule (𝓞 K) V => (latIn U L, latIn (perp h U) L)) ⁻¹' {(M, M')}).eq_empty_or_nonempty with h0 | ⟨L, ⟨l1, l2, l3, l4⟩, hL⟩` into its components or cases. Simplify using `[h0]`. Establish `eM : latIn U L = M` using `congrArg Prod.fst hL`.

Take `⟨b1, b2, b3⟩` from `(memB M').1 h2`. Establish `g1` using `(GlobalTheory.T.primitive_hermitian_sublattice_discriminant_generators K V h hK hs hp L U 1 l1 l3).2.2.2`. Rewrite `g1` using `[eM]`. Establish `g2` using `gens_rank hK _ hs2 hp2 M' b1`. Establish `cnt` using `GlobalTheory.T.card_hermitianLattices_glued_subspace_complement K V h hK hs hp U M M' _ _ h1.1 b1 g1 g2`.

Establish `sub : X ∩ (fun L : Submodule (𝓞 K) V => (latIn U L, latIn (perp h U) L)) ⁻¹' {(M, M')} ⊆ {L : Submodule (𝓞 K) V | IsIntLat h L ∧ latIn U L = M ∧ latIn (perp h U) L = M'}` using `fun N hN => ⟨hN.1.1, congrArg Prod.fst hN.2, congrArg Prod.snd hN.2⟩`. Establish `le : (discN (hRes h U) M * discN (hRes h (perp h U)) M') ^ (Module.finrank K (perp h U) + 1 + Module.finrank K (perp h U)) ≤ (n * (n * N₀)) ^ (2 * Module.finrank K (perp h U) + 1)`. Establish `e : discN (hRes h U) M = n` using `h1.2`. Rewrite using `[e, show Module.finrank K (perp h U) + 1 + Module.finrank K (perp h U) = 2 * Module.finrank K (perp h U) + 1 by ring]`. Conclude with `Nat.pow_le_pow_left (Nat.mul_le_mul_left n b3) _`.

Establish `fin` using `((Set.encard_le_encard sub).trans cnt).trans (Nat.cast_le.2 le)`. Use `ENat.toENNReal_le.2 fin` as an intermediate fact. Rewrite `this` using `[ENat.toENNReal_coe]`. Then use the resulting hypothesis. Rewrite using `[m2, e2, mul_comm] gcongr`.
-/
theorem orbMass_stabilizer_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ (U : Submodule K V) (n N₀ : ℕ), orbMass (MulAction.stabilizer (isom h) U) {L : Submodule (𝓞 K) V | IsIntLat h L ∧ discN h L = N₀ ∧ (∃ t : Finset V, t.card ≤ 1 ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set _)) ∧ discN (hRes h U) (latIn U L) = n} ≤ orbMass (isom (hRes h U)) (latsDisc (R := 𝓞 K) (hRes h U) n) * (∑ n' ∈ Finset.Icc 1 (n * N₀), orbMass (isom (hRes h (perp h U))) (latsDisc (R := 𝓞 K) (hRes h (perp h U)) n')) * (((n * (n * N₀)) ^ (2 * Module.finrank K (perp h U) + 1) : ℕ) : ℝ≥0∞) := by
  intro K V _ _ _ _ _ _ _ _ h hK hs hp U n N₀
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.definite_unitary_stabilizer_subspace_prod K V h hK hs hp U
  have hs1 := hRes_symm h hs U
  have hp1 := hRes_pd h hp U
  have hs2 := hRes_symm h hs (perp h U)
  have hp2 := hRes_pd h hp (perp h U)
  letI act : MulAction (MulAction.stabilizer (isom h) U)
      (Submodule (𝓞 K) U × Submodule (𝓞 K) (perp h U)) :=
    { smul := fun γ p => ((φ γ).1 • p.1, (φ γ).2 • p.2)
      one_smul := fun p => by
        change ((φ 1).1 • p.1, (φ 1).2 • p.2) = p
        simp
      mul_smul := fun a b p => by
        change ((φ (a * b)).1 • p.1, (φ (a * b)).2 • p.2) =
          ((φ a).1 • ((φ b).1 • p.1), (φ a).2 • ((φ b).2 • p.2))
        simp [mul_smul] }
  have hact : ∀ (γ : MulAction.stabilizer (isom h) U)
      (p : Submodule (𝓞 K) U × Submodule (𝓞 K) (perp h U)),
      γ • p = ((φ γ).1 • p.1, (φ γ).2 • p.2) := fun _ _ => rfl
  set X : Set (Submodule (𝓞 K) V) := {L : Submodule (𝓞 K) V | IsIntLat h L ∧ discN h L = N₀ ∧
    (∃ t : Finset V, t.card ≤ 1 ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set _)) ∧
    discN (hRes h U) (latIn U L) = n} with hX
  set A : Set (Submodule (𝓞 K) U) := latsDisc (R := 𝓞 K) (hRes h U) n with hA
  set B : Set (Submodule (𝓞 K) (perp h U)) :=
    ⋃ n' ∈ Finset.Icc 1 (n * N₀), latsDisc (R := 𝓞 K) (hRes h (perp h U)) n' with hB
  have memB : ∀ M, M ∈ B ↔ IsIntLat (hRes h (perp h U)) M ∧
      1 ≤ discN (hRes h (perp h U)) M ∧ discN (hRes h (perp h U)) M ≤ n * N₀ := by
    intro M
    simp only [hB, Set.mem_iUnion, Finset.mem_Icc, latsDisc, Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, hi, h1, rfl⟩
      exact ⟨h1, hi⟩
    · rintro ⟨h1, hi⟩
      exact ⟨_, hi, h1, rfl⟩
  have sA : Stable (isom (hRes h U)) A := stable_latsDisc _ n
  have sB : Stable (isom (hRes h (perp h U))) B := by
    intro g M hM
    rw [memB] at hM ⊢
    rw [discN_smul]
    exact ⟨isIntLat_smul _ g M hM.1, hM.2⟩
  have fA : ∀ M ∈ A, Finite (MulAction.stabilizer (isom (hRes h U)) M) := fun M hM =>
    (GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K U (hRes h U) hK hs1 hp1 M hM.1.1).2.2.2.1 M hM.1.1
  have fB : ∀ M ∈ B, Finite (MulAction.stabilizer (isom (hRes h (perp h U))) M) := fun M hM =>
    (GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K (perp h U) (hRes h (perp h U)) hK hs2 hp2 M ((memB M).1 hM).1.1).2.2.2.1 M
      ((memB M).1 hM).1.1
  have sX : Stable (MulAction.stabilizer (isom h) U) X := by
    rintro γ L ⟨h1, h2, h3, h4⟩
    refine ⟨isIntLat_smul h γ.1 L h1, (discN_smul h γ.1 L).trans h2, gens_smul h γ.1 L 1 h3, ?_⟩
    rw [(hφ γ L).1, discN_smul, h4]
  have sY : Stable (MulAction.stabilizer (isom h) U) (A ×ˢ B) := by
    rintro γ p ⟨h1, h2⟩
    exact ⟨sA _ _ h1, sB _ _ h2⟩
  have mp : Set.MapsTo (fun L : Submodule (𝓞 K) V => (latIn U L, latIn (perp h U) L)) X (A ×ˢ B) := by
    rintro L ⟨h1, h2, h3, h4⟩
    obtain ⟨k1, k2, k3, -⟩ := GlobalTheory.T.primitive_hermitian_sublattice_discriminant_generators K V h hK hs hp L U 1 h1 h3
    refine ⟨⟨k1, h4⟩, (memB _).2 ⟨k2, ?_, ?_⟩⟩
    · exact Nat.one_le_iff_ne_zero.2
        (GlobalTheory.T.hermitianLatticeDiscriminantOrder_ne_zero_unimodular K (perp h U) _ hK hs2 (pd_nondeg _ hp2) _ k2).1
    · rw [h2, h4] at k3
      exact k3
  have fY : ∀ p ∈ A ×ˢ B, Finite (MulAction.stabilizer (MulAction.stabilizer (isom h) U) p) := by
    rintro p ⟨h1, h2⟩
    haveI := fA _ h1
    haveI := fB _ h2
    refine Finite.of_injective
      (β := MulAction.stabilizer (isom (hRes h U)) p.1 ×
        MulAction.stabilizer (isom (hRes h (perp h U))) p.2)
      (fun γ => (⟨(φ γ.1).1, congrArg Prod.fst γ.2⟩, ⟨(φ γ.1).2, congrArg Prod.snd γ.2⟩)) ?_
    intro a b e
    apply Subtype.ext
    apply φ.injective
    exact Prod.ext (congrArg (fun q => q.1.1) e) (congrArg (fun q => q.2.1) e)
  have e1 := GlobalTheory.T.orbitStabilizerMass_eq_weightedSum_fibres (MulAction.stabilizer (isom h) U) _ _ X (A ×ˢ B)
    (fun L : Submodule (𝓞 K) V => (latIn U L, latIn (perp h U) L))
    (fun γ L => Prod.ext (hφ γ L).1 (hφ γ L).2) sX sY mp fY
  have e2 := GlobalTheory.T.orbitStabilizerMass_prod_eq_mul (MulAction.stabilizer (isom h) U) _ _ _ _ φ A B hact sA sB fA fB
  have e3 : orbMass (isom (hRes h (perp h U))) B ≤ ∑ n' ∈ Finset.Icc 1 (n * N₀),
      orbMass (isom (hRes h (perp h U))) (latsDisc (R := 𝓞 K) (hRes h (perp h U)) n') :=
    (GlobalTheory.T.orbitWeightedStabilizerSum_mono_subadditive (isom (hRes h (perp h U))) (Submodule (𝓞 K) (perp h U))).2.2.1 ℕ _ B _ _ subset_rfl
  obtain ⟨m1, m2, -⟩ := GlobalTheory.T.orbitWeightedStabilizerSum_mono_subadditive (MulAction.stabilizer (isom h) U)
    (Submodule (𝓞 K) U × Submodule (𝓞 K) (perp h U))
  rw [e1]
  refine (m1 _ (A ×ˢ B) _
    (fun _ => (((n * (n * N₀)) ^ (2 * Module.finrank K (perp h U) + 1) : ℕ) : ℝ≥0∞))
    subset_rfl ?_).trans ?_
  · rintro ⟨M, M'⟩ ⟨h1, h2⟩
    rcases (X ∩ (fun L : Submodule (𝓞 K) V => (latIn U L, latIn (perp h U) L)) ⁻¹'
      {(M, M')}).eq_empty_or_nonempty with h0 | ⟨L, ⟨l1, l2, l3, l4⟩, hL⟩
    · simp [h0]
    · have eM : latIn U L = M := congrArg Prod.fst hL
      obtain ⟨b1, b2, b3⟩ := (memB M').1 h2
      have g1 := (GlobalTheory.T.primitive_hermitian_sublattice_discriminant_generators K V h hK hs hp L U 1 l1 l3).2.2.2
      rw [eM] at g1
      have g2 := gens_rank hK _ hs2 hp2 M' b1
      have cnt := GlobalTheory.T.card_hermitianLattices_glued_subspace_complement K V h hK hs hp U M M' _ _ h1.1 b1 g1 g2
      have sub : X ∩ (fun L : Submodule (𝓞 K) V => (latIn U L, latIn (perp h U) L)) ⁻¹' {(M, M')} ⊆
          {L : Submodule (𝓞 K) V | IsIntLat h L ∧ latIn U L = M ∧ latIn (perp h U) L = M'} :=
        fun N hN => ⟨hN.1.1, congrArg Prod.fst hN.2, congrArg Prod.snd hN.2⟩
      have le : (discN (hRes h U) M * discN (hRes h (perp h U)) M') ^
          (Module.finrank K (perp h U) + 1 + Module.finrank K (perp h U)) ≤
          (n * (n * N₀)) ^ (2 * Module.finrank K (perp h U) + 1) := by
        have e : discN (hRes h U) M = n := h1.2
        rw [e, show Module.finrank K (perp h U) + 1 + Module.finrank K (perp h U) =
          2 * Module.finrank K (perp h U) + 1 by ring]
        exact Nat.pow_le_pow_left (Nat.mul_le_mul_left n b3) _
      have fin := ((Set.encard_le_encard sub).trans cnt).trans (Nat.cast_le.2 le)
      have := ENat.toENNReal_le.2 fin
      rwa [ENat.toENNReal_coe] at this
  · rw [m2, e2, mul_comm]
    gcongr

end GlobalTheory.Mass.FixedSub
