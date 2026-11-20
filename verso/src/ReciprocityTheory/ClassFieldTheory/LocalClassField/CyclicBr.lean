import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic
import ReciprocityTheory.ClassFieldTheory.LocalClassField.Herbrand
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnitsHerbrand
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsG
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RestrictedMultiplicativeH1Subsingleton
import ReciprocityTheory.ClassFieldTheory.LocalClassField.FinCoh

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

@[reducible] def commGroupOfZpowers {G : Type*} [inst : Group G] (g₀ : G) (hg : ∀ g, g ∈ Subgroup.zpowers g₀) :
    CommGroup G :=
  { inst with
    mul_comm := fun a b => by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg a)
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg b)
      rw [← zpow_add, ← zpow_add, add_comm] }

/- English proof (translation)
Set `_ : CommGroup G` to `commGroupOfZpowers g₀ hg`. Take `⟨e⟩` from `Herbrand.nonempty_groupCohomology_odd M.rho g₀ hg i hi`. Conclude with `⟨(finEquiv M i).toAddEquiv.trans e⟩`.
-/
theorem nonempty_H_odd {R G : Type} [CommRing R] [Group G] [Fintype G] [TopologicalSpace G]
    [IsTopologicalGroup G] [DiscreteTopology G] (M : TRep R G) (g₀ : G) (hg : ∀ g, g ∈ Subgroup.zpowers g₀) (i : ℕ) (hi : Odd i) :
    Nonempty (M.H i ≃+ Herbrand.H1 M.rho g₀) := by
  let _ : CommGroup G := commGroupOfZpowers g₀ hg
  obtain ⟨e⟩ := Herbrand.nonempty_groupCohomology_odd M.rho g₀ hg i hi
  exact ⟨(finEquiv M i).toAddEquiv.trans e⟩

/- English proof (translation)
Set `_ : CommGroup G` to `commGroupOfZpowers g₀ hg`. Take `⟨e⟩` from `Herbrand.nonempty_groupCohomology_even M.rho g₀ hg i h0 hi`. Conclude with `⟨(finEquiv M i).toAddEquiv.trans e⟩`.
-/
theorem nonempty_H_even {R G : Type} [CommRing R] [Group G] [Fintype G] [TopologicalSpace G]
    [IsTopologicalGroup G] [DiscreteTopology G] (M : TRep R G) (g₀ : G) (hg : ∀ g, g ∈ Subgroup.zpowers g₀) (i : ℕ) (h0 : i ≠ 0)
    (hi : Even i) : Nonempty (M.H i ≃+ Herbrand.TateZerothCohomology M.rho g₀) := by
  let _ : CommGroup G := commGroupOfZpowers g₀ hg
  obtain ⟨e⟩ := Herbrand.nonempty_groupCohomology_even M.rho g₀ hg i h0 hi
  exact ⟨(finEquiv M i).toAddEquiv.trans e⟩

/- English proof (translation)
Establish `he : 0 < eK p L` using `eK_pos p L hL`. Take `⟨hU, hU1⟩` from `herbrand_layerU hK hL h g₀ hg`. Take `⟨hZ, -, -, hZ1⟩` from `Herbrand.h_int (trivRep (GalLK p K L) ℤ).rho (fun _ _ => rfl) g₀`. Take `⟨h1, h2⟩` from `Herbrand.h_mul (layerU p K L).rho (layer p K L).rho (trivRep (GalLK p K L) ℤ).rho g₀ (layerUIncl p K L).u.toAddMonoidHom (vLayer p K L).u.toAddMonoidHom (layerUIncl_injective p) (fun x => by`. Use `ker_vLayer p he h` as an intermediate fact.

Conclude with `(LinearMap.mem_ker.symm.trans (by rw [this])).trans LinearMap.mem_range)`. Use the proof step `(vLayer_surjective p he h) (fun c a => (layerUIncl p K L).equiv c a)`. Use the proof step `(fun c b => (vLayer p K L).equiv c b) hU hZ`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Rewrite using `[h2, hU1, one_mul]`.

Conclude with `hZ1`.
-/
theorem herbrand_layer (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    [(subG p K L).Normal] [Fintype (GalLK p K L)] (g₀ : GalLK p K L) (hg : ∀ g, g ∈ Subgroup.zpowers g₀) :
    Herbrand.HFin (layer p K L).rho g₀ ∧ Herbrand.h (layer p K L).rho g₀ = degLK p K L := by
  have he : 0 < eK p L := eK_pos p L hL
  obtain ⟨hU, hU1⟩ := herbrand_layerU hK hL h g₀ hg
  obtain ⟨hZ, -, -, hZ1⟩ := Herbrand.h_int (trivRep (GalLK p K L) ℤ).rho (fun _ _ => rfl) g₀
  obtain ⟨h1, h2⟩ := Herbrand.h_mul (layerU p K L).rho (layer p K L).rho (trivRep (GalLK p K L) ℤ).rho g₀
    (layerUIncl p K L).u.toAddMonoidHom (vLayer p K L).u.toAddMonoidHom (layerUIncl_injective p)
    (fun x => by
      have := ker_vLayer p he h
      exact (LinearMap.mem_ker.symm.trans (by rw [this])).trans LinearMap.mem_range)
    (vLayer_surjective p he h) (fun c a => (layerUIncl p K L).equiv c a)
    (fun c b => (vLayer p K L).equiv c b) hU hZ
  refine ⟨h1, ?_⟩
  rw [h2, hU1, one_mul]
  exact hZ1

/- English proof (translation)
Establish `h1 : Subsingleton ((layer p K L).H 1)` using `quotient_multiplicative_h1_subsingleton p K (subG p K L) (layer p K L) (layerInf p K L) (InflationRestrictionInvariants.invariants_isInvRep (kbarT p K) (subG p K L))`. Establish `hS` using `totallySeparatedSpace_GalLK p K L`. Establish `hT2 : T2Space (GalLK p K L)` using `TotallySeparatedSpace.t2Space`. Establish `hT : T1Space (GalLK p K L)` using `T2Space.t1Space`. Establish `hF : Finite (GalLK p K L)` using `Finite.of_fintype _`.

Establish `hD : DiscreteTopology (GalLK p K L)` using `Finite.instDiscreteTopology`. Take `⟨e⟩` from `nonempty_H_odd (layer p K L) g₀ hg 1 odd_one`. Conclude with `e.symm.toEquiv.subsingleton`.
-/
theorem subsingleton_h1_cyclic_layer (h : K ≤ L) [(subG p K L).Normal] [Fintype (GalLK p K L)] (g₀ : GalLK p K L)
    (hg : ∀ g, g ∈ Subgroup.zpowers g₀) : Subsingleton (Herbrand.H1 (layer p K L).rho g₀) := by
  have h1 : Subsingleton ((layer p K L).H 1) :=
    quotient_multiplicative_h1_subsingleton p K (subG p K L) (layer p K L) (layerInf p K L)
      (InflationRestrictionInvariants.invariants_isInvRep (kbarT p K) (subG p K L))
  have hS := totallySeparatedSpace_GalLK p K L
  have hT2 : T2Space (GalLK p K L) := TotallySeparatedSpace.t2Space
  have hT : T1Space (GalLK p K L) := T2Space.t1Space
  have hF : Finite (GalLK p K L) := Finite.of_fintype _
  have hD : DiscreteTopology (GalLK p K L) := Finite.instDiscreteTopology
  obtain ⟨e⟩ := nonempty_H_odd (layer p K L) g₀ hg 1 odd_one
  exact e.symm.toEquiv.subsingleton

/- English proof (translation)
Use `subsingleton_h1_cyclic_layer h g₀ hg` as an intermediate fact. Establish `h1` using `(herbrand_layer hK hL h g₀ hg).2`. Rewrite `h1` using `[Herbrand.h_eq_card_H0hat]`. Conclude with `h1` after adjusting the coercions.
-/
theorem card_H0hat_layer (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    [(subG p K L).Normal] [Fintype (GalLK p K L)] (g₀ : GalLK p K L) (hg : ∀ g, g ∈ Subgroup.zpowers g₀) :
    Nat.card (Herbrand.TateZerothCohomology (layer p K L).rho g₀) = degLK p K L := by
  have := subsingleton_h1_cyclic_layer h g₀ hg
  have h1 := (herbrand_layer hK hL h g₀ hg).2
  rw [Herbrand.h_eq_card_H0hat] at h1
  exact_mod_cast h1

/- English proof (translation)
Use `finite_GalLK (K := K) hL` as an intermediate fact. Establish `hD : DiscreteTopology (GalLK p K L)` using `discreteTopology_GalLK hL`. Set `_ : Fintype (GalLK p K L)` to `Fintype.ofFinite _`. Take `⟨e⟩` from `nonempty_H_even (layer p K L) g₀ hg 2 two_ne_zero even_two`. Rewrite using `[Nat.card_congr e.toEquiv, card_H0hat_layer hK hL h g₀ hg]`.
-/
theorem card_h2_cyclic_layer (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    [(subG p K L).Normal] (g₀ : GalLK p K L) (hg : ∀ g, g ∈ Subgroup.zpowers g₀) :
    Nat.card ((layer p K L).H 2) = degLK p K L := by
  have := finite_GalLK (K := K) hL
  have hD : DiscreteTopology (GalLK p K L) := discreteTopology_GalLK hL
  let _ : Fintype (GalLK p K L) := Fintype.ofFinite _
  obtain ⟨e⟩ := nonempty_H_even (layer p K L) g₀ hg 2 two_ne_zero even_two
  rw [Nat.card_congr e.toEquiv, card_H0hat_layer hK hL h g₀ hg]

end ReciprocityTheory.DiscreteGroups.LocalClassField
