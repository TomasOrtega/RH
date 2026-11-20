import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.StrongIrrOfOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RegCoset
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CharpolyPowersRatios

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

namespace UpperTheory.V.Th.Det

open UpperTheory.V.U3 UpperTheory.V.Pr

/- English proof (translation)
Take `⟨H, hH⟩` from `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hO h1`. Conclude with `⟨H.toSubgroup, H.isOpen', hH⟩`.
-/
private lemma open_basis {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (O : Set G) (hO : IsOpen O) (h1 : (1 : G) ∈ O) :
    ∃ V : Subgroup G, IsOpen (V : Set G) ∧ (V : Set G) ⊆ O := by
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hO h1
  exact ⟨H.toSubgroup, H.isOpen', hH⟩

/- English proof (translation)
Use `strongIrrOfOpen _ κ m _ (fun f => (hc f).preimage continuous_subtype_val) ?_` and prove the remaining obligations. Introduce `U hU W hW`. Take `⟨O, hO, hOU⟩` from `isOpen_induced_iff.1 hU`. Establish `h1 : (1 : G) ∈ O`. Establish `: (1 : ↥(V ⊓ G')) ∈ (U : Set ↥(V ⊓ G'))` using `U.one_mem`.

Rewrite `this` using `[← hOU]`. Conclude with `this`. Take `⟨V', hV', hsub⟩` from `open_basis (O ∩ V) (hO.inter hV) ⟨h1, V.one_mem⟩`. Use `hirr V' hV' W fun g hg => ?_` and prove the remaining obligations. Establish `h2` using `hsub hg.1`.

Establish `h3 : (⟨g, h2.2, hg.2⟩ : ↥(V ⊓ G')) ∈ (U : Set ↥(V ⊓ G'))`. Rewrite using `[← hOU]`. Conclude with `h2.1`. Conclude with `hW _ h3`.
-/
private lemma strong_of {G κ : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] [Field κ] {m : ℕ} (G' V : Subgroup G) (hV : IsOpen (V : Set G))
    (r : G →* GL (Fin m) κ) (hc : LinClosed (gm r))
    (hirr : ∀ U : Subgroup G, IsOpen (U : Set G) → MatIrr (U ⊓ G') (gm r)) :
    StrongIrr (r.comp (V ⊓ G').subtype) := by
  refine strongIrrOfOpen _ κ m _ (fun f => (hc f).preimage continuous_subtype_val) ?_
  intro U hU W hW
  obtain ⟨O, hO, hOU⟩ := isOpen_induced_iff.1 hU
  have h1 : (1 : G) ∈ O := by
    have : (1 : ↥(V ⊓ G')) ∈ (U : Set ↥(V ⊓ G')) := U.one_mem
    rw [← hOU] at this
    exact this
  obtain ⟨V', hV', hsub⟩ := open_basis (O ∩ V) (hO.inter hV) ⟨h1, V.one_mem⟩
  refine hirr V' hV' W fun g hg => ?_
  have h2 := hsub hg.1
  have h3 : (⟨g, h2.2, hg.2⟩ : ↥(V ⊓ G')) ∈ (U : Set ↥(V ⊓ G')) := by
    rw [← hOU]; exact h2.1
  exact hW _ h3

/- English proof (translation)
Take `⟨V, hV, hsub⟩` from `open_basis ((fun h => s * h) ⁻¹' U) (hU.preimage (continuous_const.mul continuous_id)) (by simpa using hs)`. Conclude with `⟨V, hV, fun h hh => hsub hh⟩`.
-/
private lemma coset_in {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (U : Set G) (hU : IsOpen U) (s : G) (hs : s ∈ U) :
    ∃ V : Subgroup G, IsOpen (V : Set G) ∧ ∀ h ∈ V, s * h ∈ U := by
  obtain ⟨V, hV, hsub⟩ := open_basis ((fun h => s * h) ⁻¹' U) (hU.preimage (continuous_const.mul continuous_id))
    (by simpa using hs)
  exact ⟨V, hV, fun h hh => hsub hh⟩

/- English proof (translation)
Take `⟨s, hs, hs'⟩` from `hne`. Take `⟨V, hV, hsV⟩` from `coset_in U hU s hs`. Take `⟨u, hu, α, hα, hch⟩` from `hsep V hV`. Take `⟨h, hh⟩` from `regCoset _ κ n hn _ (strong_of G' V hV r hc hirr) ⟨u, hu⟩ α hα hch (r s)`. Use `⟨s * h, ⟨hsV _ h.2.1, G'.mul_mem hs' h.2.2⟩, ?_⟩` and prove the remaining obligations.

Simplify using `only [gm, map_mul, Units.val_mul]`. Conclude with `hh`.
-/
private lemma cosetI {G κ : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] [Field κ] {n : ℕ} (hn : n ≤ 3) (G' : Subgroup G)
    (r : G →* GL (Fin n) κ) (hc : LinClosed (gm r))
    (hirr : ∀ U : Subgroup G, IsOpen (U : Set G) → MatIrr (U ⊓ G') (gm r))
    (hsep : ∀ U : Subgroup G, IsOpen (U : Set G) → ∃ u ∈ U ⊓ G', ∃ α : Fin n → κˣ, FreeRatios α ∧
      (gm r u).charpoly = ∏ i, (X - C ((α i : κˣ) : κ)))
    (U : Set G) (hU : IsOpen U) (hne : (U ∩ (G' : Set G)).Nonempty) :
    ∃ σ ∈ U ∩ (G' : Set G), (gm r σ).charpoly.Separable := by
  obtain ⟨s, hs, hs'⟩ := hne
  obtain ⟨V, hV, hsV⟩ := coset_in U hU s hs
  obtain ⟨u, hu, α, hα, hch⟩ := hsep V hV
  obtain ⟨h, hh⟩ := regCoset _ κ n hn _ (strong_of G' V hV r hc hirr) ⟨u, hu⟩ α hα hch (r s)
  refine ⟨s * h, ⟨hsV _ h.2.1, G'.mul_mem hs' h.2.2⟩, ?_⟩
  simp only [gm, map_mul, Units.val_mul]
  exact hh

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.CharpolyPowersRatios.charpoly_pow M a hM ha d hd`.
-/
private lemma charpoly_pow {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (a : Fin n → Kˣ)
    (hM : M.charpoly = ∏ i, (X - C (a i : K))) (ha : FreeRatios a) (d : ℕ) (hd : 0 < d) :
    (M ^ d).charpoly = ∏ i, (X - C ((a i : K) ^ d)) :=
  _root_.UpperTheory.Reformulated.B.CharpolyPowersRatios.charpoly_pow M a hM ha d hd

end UpperTheory.V.Th.Det

/- English proof (translation)
Introduce `l _ G _ _ _ _ _ n hn G' ρ hρ hirr ⟨u, hu, α, hα, hch⟩ U hU hne`. Establish `hc : Pr.LinClosed (Pr.gm ρ)`. Introduce `f`. Establish `h1 : Continuous (Pr.gm ρ)` using `Units.continuous_val.comp hρ`. Establish `h2 : Continuous fun g => f (Pr.gm ρ g)`.

Establish `e : (fun g => f (Pr.gm ρ g)) = fun g => ∑ i, ∑ j, Pr.gm ρ g i j * f (Matrix.single i j 1)`. Use function extensionality and compare the values at `g`. Use `conv_lhs => rw [Matrix.matrix_eq_sum_single (Pr.gm ρ g)]`. Simplify using `only [map_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]`. Rewrite using `[e]`. Use `continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_` and prove the remaining obligations. Conclude with `(h1.matrix_elem i j).mul continuous_const`. Conclude with `isClosed_eq h2 continuous_const`.

Use `cosetI hn G' ρ hc hirr ?_ U hU hne` and prove the remaining obligations. Introduce `V hV`. Use `haveI : Finite (G ⧸ V) := Subgroup.quotient_finite_of_isOpen V hV`. Use `haveI : V.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient`. Take `⟨d, hd, -, hdV⟩` from `Subgroup.exists_pow_mem_of_index_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := V)) u`.

Use `⟨u ^ d, ⟨hdV, G'.pow_mem hu d⟩, fun i => α i ^ d, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j hij m hm`. Simplify using `only [← pow_mul]`. Conclude with `hα i j hij _ (Nat.mul_pos hd hm)`. Use `charpoly_pow _ α hch hα d hd` as an intermediate fact.

Rewrite `this` using `[← map_pow]`. Simplify using `only [Units.val_pow_eq_pow_val]`. Conclude with `this`.
-/
theorem UpperTheory.V.Th.Det.n3small :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] {n : ℕ}, n ≤ 3 → ∀ (G' : Subgroup G) (ρ : G →* GL (Fin n) (Qbar l)), Continuous ρ → (∀ U : Subgroup G, IsOpen (U : Set G) → U3.MatIrr (U ⊓ G') (W.mat ρ)) → (∃ u ∈ G', ∃ α : Fin n → (Qbar l)ˣ, Pr.FreeRatios α ∧ (W.mat ρ u).charpoly = ∏ i, (X - C ((α i : (Qbar l)ˣ) : Qbar l))) → ∀ U : Set G, IsOpen U → (U ∩ (G' : Set G)).Nonempty → ∃ σ ∈ U ∩ (G' : Set G), (W.mat ρ σ).charpoly.Separable := by
  intro l _ G _ _ _ _ _ n hn G' ρ hρ hirr ⟨u, hu, α, hα, hch⟩ U hU hne
  have hc : Pr.LinClosed (Pr.gm ρ) := by
    intro f
    have h1 : Continuous (Pr.gm ρ) := Units.continuous_val.comp hρ
    have h2 : Continuous fun g => f (Pr.gm ρ g) := by
      have e : (fun g => f (Pr.gm ρ g)) = fun g => ∑ i, ∑ j, Pr.gm ρ g i j * f (Matrix.single i j 1) := by
        funext g
        conv_lhs => rw [Matrix.matrix_eq_sum_single (Pr.gm ρ g)]
        simp only [map_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
      rw [e]
      refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
      exact (h1.matrix_elem i j).mul continuous_const
    exact isClosed_eq h2 continuous_const
  refine cosetI hn G' ρ hc hirr ?_ U hU hne
  intro V hV
  haveI : Finite (G ⧸ V) := Subgroup.quotient_finite_of_isOpen V hV
  haveI : V.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨d, hd, -, hdV⟩ := Subgroup.exists_pow_mem_of_index_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := V)) u
  refine ⟨u ^ d, ⟨hdV, G'.pow_mem hu d⟩, fun i => α i ^ d, ?_, ?_⟩
  · intro i j hij m hm
    simp only [← pow_mul]
    exact hα i j hij _ (Nat.mul_pos hd hm)
  · have := charpoly_pow _ α hch hα d hd
    rw [← map_pow] at this
    simp only [Units.val_pow_eq_pow_val]
    exact this
