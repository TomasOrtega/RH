import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.KerResSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.CorInv

open ReciprocityTheory.Gal UpperTheory.V.Base

/- English proof (translation)
Establish `e : (U' ⊓ D).relIndex (U ⊓ D) = U'.relIndex (U ⊓ D)`. Unfold `Subgroup.relIndex`. Use `congr 1`. Use extensionality with `x`. Simplify using `only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]`.

Conclude with `⟨fun h => h.1, fun h => ⟨h, x.2.2⟩⟩`. Rewrite using `[e]`. Establish `k : ∀ K : Subgroup G, U'.relIndex K = Nat.card (K.map (QuotientGroup.mk' U'))` using `fun K => by`. Rewrite using `[← Subgroup.relIndex_ker, QuotientGroup.ker_mk']`. Rewrite using `[k, k]`.

Conclude with `Subgroup.card_dvd_of_le (Subgroup.map_mono inf_le_left)`.
-/
private theorem relIndex_inf_dvd {G : Type} [Group G] (U' U D : Subgroup G) [U'.Normal] :
    (U' ⊓ D).relIndex (U ⊓ D) ∣ U'.relIndex U := by
  have e : (U' ⊓ D).relIndex (U ⊓ D) = U'.relIndex (U ⊓ D) := by
    unfold Subgroup.relIndex
    congr 1
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, x.2.2⟩⟩
  rw [e]
  have k : ∀ K : Subgroup G, U'.relIndex K = Nat.card (K.map (QuotientGroup.mk' U')) := fun K => by
    rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk']
  rw [k, k]
  exact Subgroup.card_dvd_of_le (Subgroup.map_mono inf_le_left)

/- English proof (translation)
Rewrite `hx` using `[← Nat.cast_smul_eq_nsmul R]`. Conclude with `(hn.smul_eq_zero).1 hx`.
-/
private theorem eq_zero_of_nsmul {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] {n : ℕ}
    (hn : IsUnit (n : R)) {x : N} (hx : n • x = 0) : x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul R] at hx
  exact (hn.smul_eq_zero).1 hx

/- English proof (translation)
Introduce `R G M _ _ _ _ _ _ _ _ _ _ ρ hρ U' U _ h hop hu 𝒟 h𝒟`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Establish `h0 : resU ρ h x.1 = 0` using `congrArg Subtype.val hx`.

Conclude with `Subtype.ext (eq_zero_of_nsmul hu (kerResSmul R G M ρ U' U h x.1 h0))`. Use extensionality with `y`. Rewrite using `[selEig, eig_one]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, rfl⟩ g`.

Conclude with `Subtype.ext (restriction_mem_invariant_H1 ρ h x.1 g)`. Introduce `hy`. Establish `hy' : y.1 ∈ invariantsUnderSubgroupH1 ρ U U'` using `fun g => congrArg Subtype.val (hy g)`. Establish `h1` using `corInv R G M ρ hρ U' U h hop y.1 hy'`. Rewrite `h1` using `[← Nat.cast_smul_eq_nsmul R]`.

Take `⟨v, hv⟩` from `hu.exists_left_inv`. Establish `h2` using `Submodule.smul_mem _ v h1`. Rewrite `h2` using `[smul_smul, hv, one_smul]`. Take `⟨x, hx⟩` from `h2`. Establish `hxs : x ∈ LocSel ρ U 𝒟`.

Rewrite using `[mem_locSel]`. Introduce `D hD`. Establish `hu' : IsUnit (((U' ⊓ D).relIndex (U ⊓ D) : ℕ) : R)` using `isUnit_of_dvd_unit (Nat.cast_dvd_cast (relIndex_inf_dvd U' U D)) hu`. Use `eq_zero_of_nsmul hu' (kerResSmul R G M ρ _ _ (inf_le_inf_right D h) _ ?_)` and prove the remaining obligations. Rewrite using `[resU_resU, ← resU_resU ρ inf_le_left h, hx]`.

Conclude with `mem_locSel.1 y.2 D hD`. Conclude with `⟨⟨x, hxs⟩, Subtype.ext hx⟩`.
-/
theorem UpperTheory.V.Base.selUnit :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M), ContAction ρ → ∀ (U' U : Subgroup G) [U'.Normal] (h : U' ≤ U), IsOpen (U'.subgroupOf U : Set U) →
      IsUnit (U'.relIndex U : R) → ∀ (𝒟 : Set (Subgroup G)) (h𝒟 : ConjStable 𝒟),
      Function.Injective (selRes ρ h 𝒟) ∧ LinearMap.range (selRes ρ h 𝒟) = selEig ρ U' h𝒟 U 1 := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ hρ U' U _ h hop hu 𝒟 h𝒟
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h0 : resU ρ h x.1 = 0 := congrArg Subtype.val hx
    exact Subtype.ext (eq_zero_of_nsmul hu (kerResSmul R G M ρ U' U h x.1 h0))
  · ext y
    rw [selEig, eig_one]
    constructor
    · rintro ⟨x, rfl⟩ g
      exact Subtype.ext (restriction_mem_invariant_H1 ρ h x.1 g)
    · intro hy
      have hy' : y.1 ∈ invariantsUnderSubgroupH1 ρ U U' := fun g => congrArg Subtype.val (hy g)
      have h1 := corInv R G M ρ hρ U' U h hop y.1 hy'
      rw [← Nat.cast_smul_eq_nsmul R] at h1
      obtain ⟨v, hv⟩ := hu.exists_left_inv
      have h2 := Submodule.smul_mem _ v h1
      rw [smul_smul, hv, one_smul] at h2
      obtain ⟨x, hx⟩ := h2
      have hxs : x ∈ LocSel ρ U 𝒟 := by
        rw [mem_locSel]
        intro D hD
        have hu' : IsUnit (((U' ⊓ D).relIndex (U ⊓ D) : ℕ) : R) :=
          isUnit_of_dvd_unit (Nat.cast_dvd_cast (relIndex_inf_dvd U' U D)) hu
        refine eq_zero_of_nsmul hu' (kerResSmul R G M ρ _ _ (inf_le_inf_right D h) _ ?_)
        rw [resU_resU, ← resU_resU ρ inf_le_left h, hx]
        exact mem_locSel.1 y.2 D hD
      exact ⟨⟨x, hxs⟩, Subtype.ext hx⟩
