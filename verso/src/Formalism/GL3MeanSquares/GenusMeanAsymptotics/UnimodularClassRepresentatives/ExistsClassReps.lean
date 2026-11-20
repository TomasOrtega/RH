import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSmulMem

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace StabilizerLattices

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

variable {h : V →ₗ⋆[K] V →ₗ[K] K}

omit [FiniteDimensional K V] in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
theorem exists_smul_iff (N M : Submodule (𝓞 K) V) :
    (∃ g : Formalism.HermitianLatticesTheory.isom h, g • N = M) ↔ ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g N = M := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g.1, g.2, hg⟩
  · rintro ⟨g, hg, e⟩
    exact ⟨⟨g, hg⟩, e⟩

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
theorem finite_rep (hd : IsTotPosDef h) {M : Submodule (𝓞 K) V} (hM : Submodule.IsLattice K M)
    (n : K) : {x : V | x ∈ M ∧ h x x = n}.Finite := by
  have := hM
  refine (Formalism.HermitianLatticesTheory.autFinite_short h (trace_pos hd) M (Algebra.trace ℚ K n)).subset ?_
  rintro x ⟨hx, rfl⟩
  exact ⟨hx, le_rfl⟩

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem finite_stab_lat (hs : h.IsSymm) (hd : IsTotPosDef h) {M : Submodule (𝓞 K) V}
    (hM : Submodule.IsLattice K M) :
    (MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) M : Set (Formalism.HermitianLatticesTheory.isom h)).Finite := by
  have : Finite (Formalism.ThetaLiftIndependence.autL h M) := (Formalism.HermitianLatticesTheory.autFinite K V h hs (trace_pos hd) M hM).to_subtype
  have : Finite (MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) M) := Finite.of_equiv _ (stabLatEquiv M).symm
  exact Set.toFinite _

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem exists_classReps (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) : ∃ s, Formalism.ThetaLiftIndependence.IsClassReps h L s :=
  (Formalism.ThetaLiftIndependence.classRepsDefinite K V h hs (trace_pos hd) L hL).1

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem exists_pairReps (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (n : K) :
    ∃ sX : Finset (Submodule (𝓞 K) V × V), (∀ t ∈ sX, t ∈ pairs h L n) ∧
      ∀ p ∈ pairs h L n, ∃! t, t ∈ sX ∧ ∃ g : Formalism.HermitianLatticesTheory.isom h, g • t = p := by
  obtain ⟨s, hs1, hs2⟩ := exists_classReps hs hd hL
  refine OrbSum.exists_reps_of_cover (pairs h L n) (pairs_stable hs L n)
    (⋃ M ∈ s, (fun x => (M, x)) '' {x : V | x ∈ M ∧ h x x = n}) ?_ ?_ ?_
  · exact Set.Finite.biUnion s.finite_toSet fun M hM => (finite_rep hd (hs1 M hM).1 n).image _
  · intro c hc
    obtain ⟨M, hM, x, hx, rfl⟩ := Set.mem_iUnion₂.mp hc
    exact ⟨hs1 M hM, hx.1, hx.2⟩
  · intro p hp
    obtain ⟨M, ⟨hM, g, hg, hgM⟩, -⟩ := hs2 p.1 hp.1
    refine ⟨(M, g.symm p.2), Set.mem_iUnion₂.mpr ⟨M, hM, g.symm p.2, ⟨?_, ?_⟩, rfl⟩, ⟨g, hg⟩, ?_⟩
    · rw [← Formalism.HermitianLatticesTheory.isomAct_mem_gmap, hgM]
      exact hp.2.1
    · rw [SplitBAux.symm_mem_isom hg]
      exact hp.2.2
    · exact Prod.ext hgM (LinearEquiv.apply_symm_apply g p.2)

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem sum_pairs_eq_rep (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V} (n : K)
    {s : Finset (Submodule (𝓞 K) V)} (hsr : Formalism.ThetaLiftIndependence.IsClassReps h L s)
    {sX : Finset (Submodule (𝓞 K) V × V)} (hsX : ∀ t ∈ sX, t ∈ pairs h L n)
    (hX : ∀ p ∈ pairs h L n, ∃! t, t ∈ sX ∧ ∃ g : Formalism.HermitianLatticesTheory.isom h, g • t = p) :
    ∑ t ∈ sX, ((Nat.card (MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) t) : ℕ) : ℝ)⁻¹ =
      ∑ M ∈ s, (repCount h M n : ℝ) / ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ) := by
  have key := OrbSum.sum_orbits_on (G := Formalism.HermitianLatticesTheory.isom h) (Prod.fst : Submodule (𝓞 K) V × V → _)
    (fun _ _ => rfl) (pairs h L n) (Formalism.HermitianLatticesTheory.genus h L) (pairs_stable hs L n) (fun p hp => hp.1)
    sX s hsX hsr.1 hX (fun M hM => by simp_rw [exists_smul_iff]; exact hsr.2 M hM)
    (fun M hM => finite_stab_lat hs hd hM.1)
  rw [key]
  refine Finset.sum_congr rfl fun M hM => ?_
  have e1 : Nat.card {p : Submodule (𝓞 K) V × V // p ∈ pairs h L n ∧ p.1 = M} = repCount h M n :=
    Nat.card_congr
      { toFun := fun p => ⟨p.1.2, (congrArg (fun N : Submodule (𝓞 K) V => p.1.2 ∈ N) p.2.2).mp p.2.1.2.1, p.2.1.2.2⟩
        invFun := fun x => ⟨(M, x.1), ⟨hsr.1 M hM, x.2.1, x.2.2⟩, rfl⟩
        left_inv := fun p => Subtype.ext (Prod.ext p.2.2.symm rfl)
        right_inv := fun _ => rfl }
  rw [e1, Nat.card_congr (stabLatEquiv M)]

end StabilizerLattices

end Formalism.HermitianLattices.Ext.L3
