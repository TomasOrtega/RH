import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.ForPrimeFlagLattice
import Formalism.HermitianLattices.FinalMass

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Orbit

open MulAction

/- English proof (translation)
Use `Fintype.ofFinite A` as an intermediate fact. Use `Fintype.ofFinite G` as an intermediate fact. Use `Fintype.ofFinite (Quotient (orbitRel A G))` as an intermediate fact. Rewrite using `[finsum_eq_sum_of_fintype]`. Establish `hA : (0 : ℝ) < (Nat.card A : ℝ)` using `by exact_mod_cast Nat.card_pos`.

Establish `h1 : ∀ ω : Quotient (orbitRel A G), ((Nat.card (stabilizer A ω.out) : ℕ) : ℝ)⁻¹ = (Nat.card (orbit A ω.out) : ℝ) / (Nat.card A : ℝ)`. Introduce `ω`. Establish `h` using `MulAction.card_orbit_mul_card_stabilizer_eq_card_group A ω.out`. Establish `h' : (Nat.card (orbit A ω.out) : ℝ) * (Nat.card (stabilizer A ω.out) : ℝ) = (Nat.card A : ℝ)`. Rewrite using `[Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]`.

Conclude with `h` after adjusting the coercions. Establish `hs : (0 : ℝ) < (Nat.card (stabilizer A ω.out) : ℝ)` using `by exact_mod_cast Nat.card_pos`. Use `haveI : Nonempty (orbit A ω.out) := ⟨⟨_, mem_orbit_self _⟩⟩`. Establish `ho : (0 : ℝ) < (Nat.card (orbit A ω.out) : ℝ)` using `by exact_mod_cast Nat.card_pos`. Rewrite using `[← h']`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[Finset.sum_congr rfl fun ω _ => h1 ω, ← Finset.sum_div]`. Use `congr 1`. Establish `h2 : Nat.card G = ∑ ω : Quotient (orbitRel A G), Nat.card (orbit A ω.out)`. Rewrite using `[Nat.card_congr (MulAction.selfEquivSigmaOrbits A G), Nat.card_sigma]`.

Rewrite using `[h2]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem sum_orbits_inv_card_stabilizer (A G : Type) [Group A] [MulAction A G] [Finite A] [Finite G] :
    ∑ᶠ ω : Quotient (orbitRel A G), ((Nat.card (stabilizer A ω.out) : ℕ) : ℝ)⁻¹ =
      (Nat.card G : ℝ) / (Nat.card A : ℝ) := by
  classical
  have := Fintype.ofFinite A
  have := Fintype.ofFinite G
  have := Fintype.ofFinite (Quotient (orbitRel A G))
  rw [finsum_eq_sum_of_fintype]
  have hA : (0 : ℝ) < (Nat.card A : ℝ) := by exact_mod_cast Nat.card_pos
  have h1 : ∀ ω : Quotient (orbitRel A G),
      ((Nat.card (stabilizer A ω.out) : ℕ) : ℝ)⁻¹ = (Nat.card (orbit A ω.out) : ℝ) / (Nat.card A : ℝ) := by
    intro ω
    have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group A ω.out
    have h' : (Nat.card (orbit A ω.out) : ℝ) * (Nat.card (stabilizer A ω.out) : ℝ) = (Nat.card A : ℝ) := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      exact_mod_cast h
    have hs : (0 : ℝ) < (Nat.card (stabilizer A ω.out) : ℝ) := by exact_mod_cast Nat.card_pos
    haveI : Nonempty (orbit A ω.out) := ⟨⟨_, mem_orbit_self _⟩⟩
    have ho : (0 : ℝ) < (Nat.card (orbit A ω.out) : ℝ) := by exact_mod_cast Nat.card_pos
    rw [← h']
    field_simp
  rw [Finset.sum_congr rfl fun ω _ => h1 ω, ← Finset.sum_div]
  congr 1
  have h2 : Nat.card G = ∑ ω : Quotient (orbitRel A G), Nat.card (orbit A ω.out) := by
    rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits A G), Nat.card_sigma]
  rw [h2]
  push_cast
  rfl

end Orbit

/- English proof (translation)
Establish `key : ((Algebra.trace ℚ K (h x x) : ℚ) : ℂ) = ∑ σ : K →ₐ[ℚ] ℂ, σ (h x x)`. Rewrite using `[← eq_ratCast (algebraMap ℚ ℂ), trace_eq_sum_embeddings (E := ℂ)]`. Establish `key' : ((Algebra.trace ℚ K (h x x) : ℚ) : ℝ) = ∑ σ : K →ₐ[ℚ] ℂ, (σ (h x x)).re`. Use `congrArg Complex.re key` as an intermediate fact. Rewrite `this` using `[Complex.re_sum]`.

Rewrite using `[← this]`. Simplify using the standard rewrite rules. Establish `hpos : 0 < ∑ σ : K →ₐ[ℚ] ℂ, (σ (h x x)).re`. Set `σ0 : K →ₐ[ℚ] ℂ` to `IsAlgClosed.lift`. Conclude with `Finset.sum_pos (fun σ _ => hp σ.toRingHom x hx) ⟨σ0, Finset.mem_univ _⟩`.

Conclude with `key' ▸ hpos` after adjusting the coercions.
-/
theorem trace_inner_self_pos {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hp : IsPosDef h) (x : V) (hx : x ≠ 0) :
    0 < Algebra.trace ℚ K (h x x) := by
  have key : ((Algebra.trace ℚ K (h x x) : ℚ) : ℂ) = ∑ σ : K →ₐ[ℚ] ℂ, σ (h x x) := by
    rw [← eq_ratCast (algebraMap ℚ ℂ), trace_eq_sum_embeddings (E := ℂ)]
  have key' : ((Algebra.trace ℚ K (h x x) : ℚ) : ℝ) = ∑ σ : K →ₐ[ℚ] ℂ, (σ (h x x)).re := by
    have := congrArg Complex.re key
    rw [Complex.re_sum] at this
    rw [← this]
    simp
  have hpos : 0 < ∑ σ : K →ₐ[ℚ] ℂ, (σ (h x x)).re := by
    let σ0 : K →ₐ[ℚ] ℂ := IsAlgClosed.lift
    exact Finset.sum_pos (fun σ _ => hp σ.toRingHom x hx) ⟨σ0, Finset.mem_univ _⟩
  exact_mod_cast key' ▸ hpos

section Rows

open Classical

def FibresOrthLatticeOneGenus (D : D7) (u : D.what₂.Word) : Prop :=
  ForPrimeFlagLattice D u fun F0 Λ => ∀ s : Finset (LatV D), IsRowReps D F0 s →
    (∀ Λ' ∈ s, L0X D Λ' (lf D F0) ∈ Formalism.HermitianLatticesTheory.genus (D.sp.X 0).hT (L0X D Λ (lf D F0))) ∧
    ∀ M ∈ Formalism.HermitianLatticesTheory.genus (D.sp.X 0).hT (L0X D Λ (lf D F0)),
      ∑ Λ' ∈ s.filter (fun Λ' => ∃ g ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, Formalism.HermitianLatticesTheory.gmap g M = L0X D Λ' (lf D F0)),
          wRow D F0 Λ' =
        ((Tu D u : ℝ) - 1) ^ D.R.f * ((Nat.card (Formalism.ThetaLiftIndependence.autL (D.sp.X 0).hT M) : ℕ) : ℝ)⁻¹

/- English proof (translation)
Rewrite using `[← Finset.sum_biUnion]`. Use `Finset.sum_congr ?_ fun _ _ => rfl` and prove the remaining obligations. Use extensionality with `a`. Simplify using `only [Finset.mem_biUnion, Finset.mem_filter]`. Prove the components needed by the constructor for the conclusion.

Introduce `ha`. Take `⟨N, ⟨hN, hg⟩, _⟩` from `hreps.2 (c a) (hc a ha)`. Conclude with `⟨N, hN, ha, hg⟩`. Introduce and unpack `⟨N, _, ha, _⟩`. Conclude with `ha`.

Introduce `M hM M' hM' hne`. Rewrite using `[Function.onFun, Finset.disjoint_left]`. Introduce `a ha ha'`. Rewrite `ha`, `ha'` using `[Finset.mem_filter]`. Take `⟨N, _, huniq⟩` from `hreps.2 (c a) (hc a ha.1)`.

Conclude with `hne ((huniq M ⟨hM, ha.2⟩).trans (huniq M' ⟨hM', ha'.2⟩).symm)`.
-/
theorem sum_eq_sum_over_class_reps {K V α : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V)
    (reps : Finset (Submodule (𝓞 K) V)) (hreps : Formalism.ThetaLiftIndependence.IsClassReps h L reps) (s : Finset α)
    (c : α → Submodule (𝓞 K) V) (hc : ∀ a ∈ s, c a ∈ Formalism.HermitianLatticesTheory.genus h L) (w : α → ℝ) :
    ∑ a ∈ s, w a = ∑ M ∈ reps, ∑ a ∈ s.filter (fun a => ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g M = c a), w a := by
  rw [← Finset.sum_biUnion]
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext a
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · intro ha
      obtain ⟨N, ⟨hN, hg⟩, _⟩ := hreps.2 (c a) (hc a ha)
      exact ⟨N, hN, ha, hg⟩
    · rintro ⟨N, _, ha, _⟩
      exact ha
  · intro M hM M' hM' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro a ha ha'
    rw [Finset.mem_filter] at ha ha'
    obtain ⟨N, _, huniq⟩ := hreps.2 (c a) (hc a ha.1)
    exact hne ((huniq M ⟨hM, ha.2⟩).trans (huniq M' ⟨hM', ha'.2⟩).symm)

/- English proof (translation)
Introduce `hT h3 hsp F0 he hz Λ hΛ s hs`. Take `⟨hgen, hfib⟩` from `hR hT h3 hsp F0 he hz Λ hΛ s hs`. Take `⟨⟨reps, hreps⟩, hmass, _⟩` from `Formalism.HermitianLatticesTheory.final_massBasic D.host.E (D.sp.X 0).V (D.sp.X 0).hT (D.sp.X 0).herm (trace_inner_self_pos _ hpos) (L0X D Λ (lf D F0)) (hlat hT h3 hsp F0 he hz Λ hΛ)`. Rewrite using `[hmass reps hreps]`. Unfold `massRows`.

Rewrite using `[sum_eq_sum_over_class_reps (D.sp.X 0).hT _ reps hreps s (fun Λ' => L0X D Λ' (lf D F0)) hgen, Finset.sum_congr rfl fun M hM => hfib M (hreps.1 M hM), ← Finset.mul_sum, mul_comm]`.
-/
theorem gluing_mass_of_fibre_structure (D : D7) (u : D.what₂.Word) (hpos : IsPosDef (D.sp.X 0).hT)
    (hlat : ForPrimeFlagLattice D u fun F0 Λ => Submodule.IsLattice D.host.E (L0X D Λ (lf D F0)))
    (hR : FibresOrthLatticeOneGenus D u) : WordRowsGluing D u := by
  intro hT h3 hsp F0 he hz Λ hΛ s hs
  obtain ⟨hgen, hfib⟩ := hR hT h3 hsp F0 he hz Λ hΛ s hs
  obtain ⟨⟨reps, hreps⟩, hmass, _⟩ := Formalism.HermitianLatticesTheory.final_massBasic D.host.E (D.sp.X 0).V (D.sp.X 0).hT (D.sp.X 0).herm
    (trace_inner_self_pos _ hpos) (L0X D Λ (lf D F0)) (hlat hT h3 hsp F0 he hz Λ hΛ)
  rw [hmass reps hreps]
  unfold massRows
  rw [sum_eq_sum_over_class_reps (D.sp.X 0).hT _ reps hreps s (fun Λ' => L0X D Λ' (lf D F0)) hgen,
    Finset.sum_congr rfl fun M hM => hfib M (hreps.1 M hM), ← Finset.mul_sum, mul_comm]

end Rows

end Formalism.MainNotions.BridgeLemma₂

end
