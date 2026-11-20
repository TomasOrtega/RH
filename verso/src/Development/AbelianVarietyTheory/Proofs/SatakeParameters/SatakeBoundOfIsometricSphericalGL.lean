import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatakeParametersBoundedLatticeEigenfunctionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeneralLinearTransitiveOnLatticesOverDVRStatement

open GlobalTheory.LatHecke

namespace GlobalTheory.LatHecke

/- English proof (translation)
Introduce `O K _ _ _ _ _ _ _ r V _ _ ρ v α hcard hnorm hv hinv heig`. Establish `hmul : ∀ (a b : GL (Fin r) K) (x : V), ρ (a * b) x = ρ a (ρ b x)` using `fun a b x => by`. Rewrite using `[map_mul]`. Both sides reduce to the same expression. Establish `hone : ∀ x : V, ρ 1 x = x` using `fun x => by`.

Rewrite using `[map_one]`. Both sides reduce to the same expression. Use `choose γ hγ using (GlobalTheory.T.generalLinear_transitive_on_lattices_over_DVR O K r).1`. Establish `hγ' : ∀ L : Lat O K r, γ L • std O K r = L` using `fun L => Lat.ext (hγ L)`. Set `φ : Lat O K r → V` to `fun L => ρ (γ L) v`.

Establish `hφ : ∀ g : GL (Fin r) K, φ (g • std O K r) = ρ g v`. Introduce `g`. Establish `hfix : ((γ (g • std O K r))⁻¹ * g) • std O K r = std O K r`. Rewrite using `[mul_smul, inv_smul_eq_iff, hγ']`. Establish `h1 : ρ ((γ (g • std O K r))⁻¹ * g) v = v` using `hinv _ (congrArg Subtype.val hfix)`.

Establish `h2 : ρ g v = ρ (γ (g • std O K r) * ((γ (g • std O K r))⁻¹ * g)) v`. Rewrite using `[mul_inv_cancel_left]`. Express the relevant statement in the definitionally equal form `ρ (γ (g • std O K r)) v = ρ g v`. Rewrite using `[h2, hmul, h1]`. Establish `hφg : ∀ (g : GL (Fin r) K) (M : Lat O K r), φ (g • M) = ρ g (φ M)`.

Introduce `g M`. Establish `h1 : g • M = (g * γ M) • std O K r` using `by rw [mul_smul, hγ']`. Rewrite using `[h1, hφ, hmul]`. Establish `hstd : φ (std O K r) = v`. Use `hφ 1` as an intermediate fact.

Rewrite `this` using `[one_smul, hone]`. Then use the resulting hypothesis. Use `GlobalTheory.T.satakeParameters_bounded_lattice_eigenfunction O K r V φ α ‖v‖ hcard ?_ ?_ ?_` and prove the remaining obligations. Introduce `h`. Conclude with `hv (by rw [← hstd, h]; rfl)`. Introduce `L`.

Conclude with `(hnorm _ _).le`. Introduce `k hk L`. Establish `h0 : heckeElem k φ (std O K r) = ((((qRes O : ℝ) ^ ((k : ℝ) * ((r : ℝ) - k) / 2) : ℝ) : ℂ) * α.esymm k) • v`. Rewrite using `[heckeElem_eq_sum, ← heig k hk ((subElem_finite k (std O K r)).toFinset.image γ)]`. Rewrite using `[Finset.sum_image]`.

Introduce `M _ M' _ h`. Rewrite using `[← hγ' M, ← hγ' M', h]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `g hg`. Take `⟨M, hM, rfl⟩` from `Finset.mem_image.1 (Finset.mem_coe.1 hg)`.

Conclude with `⟨M, (Set.Finite.mem_toFinset _).1 hM, (hγ M).symm⟩`. Introduce `g hg g' hg' h`. Take `⟨M, hM, rfl⟩` from `Finset.mem_image.1 (Finset.mem_coe.1 hg)`. Take `⟨M', hM', rfl⟩` from `Finset.mem_image.1 (Finset.mem_coe.1 hg')`. Establish `h' : M = M'` using `Lat.ext (by simpa only [hγ] using h)`.

Rewrite using `[h']`. Introduce and unpack `_ ⟨M, hM, rfl⟩`. Conclude with `⟨γ M, Finset.mem_coe.2 (Finset.mem_image.2 ⟨M, (Set.Finite.mem_toFinset _).2 hM, rfl⟩), hγ M⟩`. Establish `h1 : heckeElem k φ L = ρ (γ L) (heckeElem k φ (std O K r))` using `by conv_lhs => rw [← hγ' L]`. Rewrite using `[heckeElem_smul, heckeElem_eq_sum, heckeElem_eq_sum, map_sum]`.

Conclude with `Finset.sum_congr rfl fun M _ => hφg _ _`. Rewrite using `[h1, h0, map_smul]`.
-/
theorem satake_bound_of_isometric_spherical : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (ρ : Representation ℂ (GL (Fin r) K) V) (v : V) (α : Multiset ℂ), α.card = r → (∀ g x, ‖ρ g x‖ = ‖x‖) → v ≠ 0 → (∀ g, glMap g (std O K r).1 = (std O K r).1 → ρ g v = v) → (∀ k ≤ r, ∀ s : Finset (GL (Fin r) K), Set.BijOn (fun g => glMap g (std O K r).1) s (Subtype.val '' subElem k (std O K r)) → ∑ g ∈ s, ρ g v = ((((qRes O : ℝ) ^ ((k : ℝ) * ((r : ℝ) - k) / 2) : ℝ) : ℂ) * α.esymm k) • v) → ∀ a ∈ α, ‖a‖ ≤ (qRes O : ℝ) ^ (((r : ℝ) - 1) / 2) := by
  intro O K _ _ _ _ _ _ _ r V _ _ ρ v α hcard hnorm hv hinv heig
  classical
  have hmul : ∀ (a b : GL (Fin r) K) (x : V), ρ (a * b) x = ρ a (ρ b x) := fun a b x => by
    rw [map_mul]; rfl
  have hone : ∀ x : V, ρ 1 x = x := fun x => by
    rw [map_one]; rfl
  choose γ hγ using (GlobalTheory.T.generalLinear_transitive_on_lattices_over_DVR O K r).1
  have hγ' : ∀ L : Lat O K r, γ L • std O K r = L := fun L => Lat.ext (hγ L)
  let φ : Lat O K r → V := fun L => ρ (γ L) v

  have hφ : ∀ g : GL (Fin r) K, φ (g • std O K r) = ρ g v := by
    intro g
    have hfix : ((γ (g • std O K r))⁻¹ * g) • std O K r = std O K r := by
      rw [mul_smul, inv_smul_eq_iff, hγ']
    have h1 : ρ ((γ (g • std O K r))⁻¹ * g) v = v :=
      hinv _ (congrArg Subtype.val hfix)
    have h2 : ρ g v = ρ (γ (g • std O K r) * ((γ (g • std O K r))⁻¹ * g)) v := by
      rw [mul_inv_cancel_left]
    change ρ (γ (g • std O K r)) v = ρ g v
    rw [h2, hmul, h1]
  have hφg : ∀ (g : GL (Fin r) K) (M : Lat O K r), φ (g • M) = ρ g (φ M) := by
    intro g M
    have h1 : g • M = (g * γ M) • std O K r := by rw [mul_smul, hγ']
    rw [h1, hφ, hmul]
  have hstd : φ (std O K r) = v := by
    have := hφ 1
    rwa [one_smul, hone] at this
  refine GlobalTheory.T.satakeParameters_bounded_lattice_eigenfunction O K r V φ α ‖v‖ hcard ?_ ?_ ?_
  · intro h
    exact hv (by rw [← hstd, h]; rfl)
  · intro L
    exact (hnorm _ _).le
  · intro k hk L

    have h0 : heckeElem k φ (std O K r)
        = ((((qRes O : ℝ) ^ ((k : ℝ) * ((r : ℝ) - k) / 2) : ℝ) : ℂ) * α.esymm k) • v := by
      rw [heckeElem_eq_sum, ← heig k hk ((subElem_finite k (std O K r)).toFinset.image γ)]
      · rw [Finset.sum_image]
        intro M _ M' _ h
        rw [← hγ' M, ← hγ' M', h]
      · refine ⟨?_, ?_, ?_⟩
        · intro g hg
          obtain ⟨M, hM, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hg)
          exact ⟨M, (Set.Finite.mem_toFinset _).1 hM, (hγ M).symm⟩
        · intro g hg g' hg' h
          obtain ⟨M, hM, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hg)
          obtain ⟨M', hM', rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hg')
          have h' : M = M' := Lat.ext (by simpa only [hγ] using h)
          rw [h']
        · rintro _ ⟨M, hM, rfl⟩
          exact ⟨γ M, Finset.mem_coe.2 (Finset.mem_image.2
            ⟨M, (Set.Finite.mem_toFinset _).2 hM, rfl⟩), hγ M⟩

    have h1 : heckeElem k φ L = ρ (γ L) (heckeElem k φ (std O K r)) := by
      conv_lhs => rw [← hγ' L]
      rw [heckeElem_smul, heckeElem_eq_sum, heckeElem_eq_sum, map_sum]
      exact Finset.sum_congr rfl fun M _ => hφg _ _
    rw [h1, h0, map_smul]
end GlobalTheory.LatHecke
