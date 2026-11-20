import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FiniteDimensionalOfOrtho
import Formalism.HermitianLattices.HermitianLatticesProofs.AutFinite

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

/- English proof (translation)
Establish `hGpos : (0 : ℝ) < Nat.card G` using `by exact_mod_cast Nat.card_pos`. Establish `hos : ∀ t : X, (Nat.card (MulAction.orbit G t) : ℝ) = Nat.card G / Nat.card (MulAction.stabilizer G t)`. Introduce `t`. Establish `h1` using `(MulAction.stabilizer G t).card_mul_index`. Rewrite `h1` using `[MulAction.index_stabilizer, ← Nat.card_coe_set_eq]`.

Establish `hs : (0 : ℝ) < Nat.card (MulAction.stabilizer G t)` using `by exact_mod_cast Nat.card_pos`. Rewrite using `[eq_div_iff hs.ne', ← Nat.cast_mul, mul_comm, h1]`. Take `⟨A', hA'⟩ : ∃ A' : Finset X, ∀ x, x ∈ A' ↔ x ∈ A` from `⟨(Set.toFinite A).toFinset, fun x => Set.Finite.mem_toFinset _⟩`. Establish `hAeq : A = ↑A'` using `Set.ext fun x => (hA' x).symm`. Establish `hcover : A' = T.biUnion (fun t => A'.filter (fun x => ∃ g : G, g • t = x))`.

Use extensionality with `x`. Simplify using `only [Finset.mem_biUnion, Finset.mem_filter]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨t, ⟨htT, g, hg⟩, -⟩` from `hT x ((hA' x).mp hx)`.

Conclude with `⟨t, htT, hx, g, hg⟩`. Introduce and unpack `⟨t, -, hx, -⟩`. Conclude with `hx`. Establish `hdisj : ∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ → Disjoint (A'.filter (fun x => ∃ g : G, g • t₁ = x)) (A'.filter (fun x => ∃ g : G, g • t₂ = x))`. Introduce `t₁ h₁ t₂ h₂ hne`.

Use `Finset.disjoint_left.mpr ?_` and prove the remaining obligations. Introduce `x hx1 hx2`. Simplify using `only [Finset.mem_filter] at hx1 hx2`. Take `⟨t, -, huniq⟩` from `hT x ((hA' x).mp hx1.1)`. Conclude with `hne ((huniq t₁ ⟨h₁, hx1.2⟩).trans (huniq t₂ ⟨h₂, hx2.2⟩).symm)`.

Establish `hcard : ∀ t ∈ T, ((A'.filter (fun x => ∃ g : G, g • t = x)).card : ℝ) = Nat.card (MulAction.orbit G t)`. Introduce `t ht`. Establish `hset : MulAction.orbit G t = ↑(A'.filter (fun x => ∃ g : G, g • t = x))`. Use extensionality with `x`. Simplify using `only [MulAction.mem_orbit_iff, Finset.coe_filter, Set.mem_setOf_eq]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, rfl⟩`. Conclude with `⟨(hA' _).mpr (hA g t (hTA t ht)), g, rfl⟩`. Introduce and unpack `⟨-, g, rfl⟩`. Conclude with `⟨g, rfl⟩`.

Rewrite using `[hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]`. Establish `hsum : (A'.card : ℝ) = ∑ t ∈ T, (Nat.card (MulAction.orbit G t) : ℝ)`. Rewrite using `[hcover, Finset.card_biUnion hdisj, Nat.cast_sum]`. Conclude with `Finset.sum_congr rfl hcard`. Rewrite using `[hAeq, Nat.card_coe_set_eq, Set.ncard_coe_finset, hsum, Finset.sum_div]`.

Use `Finset.sum_congr rfl (fun t _ => ?_)` and prove the remaining obligations. Rewrite using `[hos t, div_div, mul_comm, ← div_div, div_self hGpos.ne', one_div]`.
-/
theorem sum_inv_card_stab {G X : Type*} [Group G] [Finite G] [MulAction G X] (A : Set X)
    [Finite A] (hA : ∀ g : G, ∀ x ∈ A, g • x ∈ A) (T : Finset X) (hTA : ∀ t ∈ T, t ∈ A)
    (hT : ∀ x ∈ A, ∃! t, t ∈ T ∧ ∃ g : G, g • t = x) :
    (Nat.card A : ℝ) / (Nat.card G : ℝ) =
      ∑ t ∈ T, ((Nat.card (MulAction.stabilizer G t) : ℕ) : ℝ)⁻¹ := by
  classical
  have hGpos : (0 : ℝ) < Nat.card G := by exact_mod_cast Nat.card_pos
  have hos : ∀ t : X, (Nat.card (MulAction.orbit G t) : ℝ) =
      Nat.card G / Nat.card (MulAction.stabilizer G t) := by
    intro t
    have h1 := (MulAction.stabilizer G t).card_mul_index
    rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq] at h1
    have hs : (0 : ℝ) < Nat.card (MulAction.stabilizer G t) := by exact_mod_cast Nat.card_pos
    rw [eq_div_iff hs.ne', ← Nat.cast_mul, mul_comm, h1]
  obtain ⟨A', hA'⟩ : ∃ A' : Finset X, ∀ x, x ∈ A' ↔ x ∈ A :=
    ⟨(Set.toFinite A).toFinset, fun x => Set.Finite.mem_toFinset _⟩
  have hAeq : A = ↑A' := Set.ext fun x => (hA' x).symm
  have hcover : A' = T.biUnion (fun t => A'.filter (fun x => ∃ g : G, g • t = x)) := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · intro hx
      obtain ⟨t, ⟨htT, g, hg⟩, -⟩ := hT x ((hA' x).mp hx)
      exact ⟨t, htT, hx, g, hg⟩
    · rintro ⟨t, -, hx, -⟩
      exact hx
  have hdisj : ∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ →
      Disjoint (A'.filter (fun x => ∃ g : G, g • t₁ = x)) (A'.filter (fun x => ∃ g : G, g • t₂ = x)) := by
    intro t₁ h₁ t₂ h₂ hne
    refine Finset.disjoint_left.mpr ?_
    intro x hx1 hx2
    simp only [Finset.mem_filter] at hx1 hx2
    obtain ⟨t, -, huniq⟩ := hT x ((hA' x).mp hx1.1)
    exact hne ((huniq t₁ ⟨h₁, hx1.2⟩).trans (huniq t₂ ⟨h₂, hx2.2⟩).symm)
  have hcard : ∀ t ∈ T, ((A'.filter (fun x => ∃ g : G, g • t = x)).card : ℝ) =
      Nat.card (MulAction.orbit G t) := by
    intro t ht
    have hset : MulAction.orbit G t = ↑(A'.filter (fun x => ∃ g : G, g • t = x)) := by
      ext x
      simp only [MulAction.mem_orbit_iff, Finset.coe_filter, Set.mem_setOf_eq]
      constructor
      · rintro ⟨g, rfl⟩
        exact ⟨(hA' _).mpr (hA g t (hTA t ht)), g, rfl⟩
      · rintro ⟨-, g, rfl⟩
        exact ⟨g, rfl⟩
    rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  have hsum : (A'.card : ℝ) = ∑ t ∈ T, (Nat.card (MulAction.orbit G t) : ℝ) := by
    rw [hcover, Finset.card_biUnion hdisj, Nat.cast_sum]
    exact Finset.sum_congr rfl hcard
  rw [hAeq, Nat.card_coe_set_eq, Set.ncard_coe_finset, hsum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [hos t, div_div, mul_comm, ← div_div, div_self hGpos.ne', one_div]

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.gmap`. Use extensionality with `x`. Simplify using `[Submodule.mem_map]`.
-/
theorem autSub_gmap_one (L : Submodule (𝓞 K) V) : Formalism.HermitianLatticesTheory.gmap (1 : V ≃ₗ[K] V) L = L := by
  unfold Formalism.HermitianLatticesTheory.gmap
  ext x
  simp [Submodule.mem_map]

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.gmap`. Use extensionality with `x`. Simplify using `[Submodule.mem_map]`.
-/
theorem autSub_gmap_mul (a b : V ≃ₗ[K] V) (L : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap (a * b) L = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b L) := by
  unfold Formalism.HermitianLatticesTheory.gmap
  ext x
  simp [Submodule.mem_map]

def autSub (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) : Subgroup (V ≃ₗ[K] V) where
  carrier := Formalism.ThetaLiftIndependence.autL h L
  one_mem' := ⟨one_mem _, autSub_gmap_one L⟩
  mul_mem' := by
    intro a b ha hb
    exact ⟨mul_mem ha.1 hb.1, by rw [autSub_gmap_mul, hb.2, ha.2]⟩
  inv_mem' := by
    intro a ha
    refine ⟨inv_mem ha.1, ?_⟩
    conv_lhs => rw [← ha.2]
    rw [← autSub_gmap_mul, inv_mul_cancel, autSub_gmap_one]

/- English proof (translation)
Use `finiteDimensional_of_ortho hI` as an intermediate fact. Conclude with `Formalism.HermitianLatticesTheory.autFinite K V h hs (trace_pos_of_ortho hK hs hI) L hL`.
-/
theorem finite_autL_of_ortho (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) {I : Submodule (𝓞 K) V} {n : ℕ} (hI : Formalism.HermitianLatticesTheory.IsOrthoLattice h I n)
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) : (Formalism.ThetaLiftIndependence.autL h L).Finite := by
  have := finiteDimensional_of_ortho hI
  exact Formalism.HermitianLatticesTheory.autFinite K V h hs (trace_pos_of_ortho hK hs hI) L hL

/- English proof (translation)
Use `hL` as an intermediate fact. Use `(Formalism.HermitianLatticesTheory.autFinite_short h (trace_pos_of_ortho hK hs hI) L (Algebra.trace ℚ K t)).subset ?_` and prove the remaining obligations. Introduce and unpack `x ⟨hx, rfl⟩`. Conclude with `⟨hx, le_rfl⟩`.
-/
theorem finite_repSet_of_ortho (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) {I : Submodule (𝓞 K) V} {n : ℕ} (hI : Formalism.HermitianLatticesTheory.IsOrthoLattice h I n)
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) (t : K) :
    {x : V | x ∈ L ∧ h x x = t}.Finite := by
  have := hL
  refine (Formalism.HermitianLatticesTheory.autFinite_short h (trace_pos_of_ortho hK hs hI) L
    (Algebra.trace ℚ K t)).subset ?_
  rintro x ⟨hx, rfl⟩
  exact ⟨hx, le_rfl⟩

end Formalism.HermitianLattices.Ext.L3
