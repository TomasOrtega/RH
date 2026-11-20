import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.MonomialOfComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.MonomialRed
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.PermChar

open IsLocalRing Polynomial Matrix UpperTheory.V

/- English proof (translation)
Introduce `K k B G _ _ _ _ _ r j φ χ hj hpoly hspan hst Z _ u huZ hsep N hN hfi`. Use `haveI := hN`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hd0 : 0 < N.index` using `Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero`.

Set `N' : Subgroup G` to `N.map Z.subtype`. Establish `hcore : u ^ N.index ∈ N'.normalCore` using `by show ∀ c : G, c * u ^ N.index * c⁻¹ ∈ N'`. Introduce `c`. Establish `hz : c * u * c⁻¹ ∈ Z` using `‹Z.Normal›.conj_mem u huZ c`. Establish `hp` using `N.pow_index_mem ⟨c * u * c⁻¹, hz⟩`.

Use `⟨_, hp, ?_⟩` and prove the remaining obligations. Simplify using `[conj_pow]`. Establish `hcomm : ∀ g ∈ N'.normalCore, ∀ h ∈ N'.normalCore, r g * r h = r h * r g`. Introduce `g hg h hh`. Take `⟨g', hg', rfl⟩` from `N'.normalCore_le hg`.

Take `⟨h', hh', rfl⟩` from `N'.normalCore_le hh`. Conclude with `hcon g' hg' h' hh'`. Take `⟨b, π, _, hmono, htrans⟩` from `AlgebraTools.monomialOfComm K G 4 r hspan N'.normalCore hcomm ⟨u ^ N.index, hcore, by rw [map_pow]; exact hsep _ hd0⟩`. Establish `hred` using `AlgebraTools.monomialRed K k B G 4 r j φ χ hj hpoly b π hmono htrans`. Take `⟨s, t, hst'⟩` from `hst`.

Establish `hle : π.ker ≤ (χ s / χ t).ker`. Introduce `g hg`. Rewrite using `[MonoidHom.mem_ker]`. Simplify using `[hred g hg s t]`. Take `⟨h1, h2⟩` from `AlgebraTools.permChar G k π (χ s / χ t) hle`.

Conclude with `hst' _ h1 h2 (pow_orderOf_eq_one _)`.
-/
theorem UpperTheory.V.Ws.exists_noncommuting_images_in_finiteIndex_normal_subgroup :
    ∀ (K k B G : Type) [Field K] [IsAlgClosed K] [Field k] [CommRing B] [Group G] (r : G →* Matrix (Fin 4) (Fin 4) K)
      (j : B →+* K) (φ : B →+* k) (χ : Fin 4 → G →* kˣ), Function.Injective j →
      (∀ g, ∃ p : B[X], p.map j = (r g).charpoly ∧ p.map φ = ∏ i, (X - C (χ i g : k))) →
      Submodule.span K (Set.range r) = ⊤ → (∃ s t, ∀ n : ℕ, 0 < n → n ≤ 4 → (χ s / χ t) ^ n ≠ 1) →
      ∀ (Z : Subgroup G) [Z.Normal] (u : G), u ∈ Z → (∀ d : ℕ, 0 < d → (r u ^ d).charpoly.Separable) →
      ∀ N : Subgroup Z, N.Normal → N.FiniteIndex → ∃ g ∈ N, ∃ h ∈ N, r g * r h ≠ r h * r g := by
  intro K k B G _ _ _ _ _ r j φ χ hj hpoly hspan hst Z _ u huZ hsep N hN hfi
  haveI := hN
  by_contra hcon
  push_neg at hcon
  have hd0 : 0 < N.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  let N' : Subgroup G := N.map Z.subtype
  have hcore : u ^ N.index ∈ N'.normalCore := by
    show ∀ c : G, c * u ^ N.index * c⁻¹ ∈ N'
    intro c
    have hz : c * u * c⁻¹ ∈ Z := ‹Z.Normal›.conj_mem u huZ c
    have hp := N.pow_index_mem ⟨c * u * c⁻¹, hz⟩
    refine ⟨_, hp, ?_⟩
    simp [conj_pow]
  have hcomm : ∀ g ∈ N'.normalCore, ∀ h ∈ N'.normalCore, r g * r h = r h * r g := by
    intro g hg h hh
    obtain ⟨g', hg', rfl⟩ := N'.normalCore_le hg
    obtain ⟨h', hh', rfl⟩ := N'.normalCore_le hh
    exact hcon g' hg' h' hh'
  obtain ⟨b, π, _, hmono, htrans⟩ := AlgebraTools.monomialOfComm K G 4 r hspan N'.normalCore hcomm
    ⟨u ^ N.index, hcore, by rw [map_pow]; exact hsep _ hd0⟩
  have hred := AlgebraTools.monomialRed K k B G 4 r j φ χ hj hpoly b π hmono htrans
  obtain ⟨s, t, hst'⟩ := hst
  have hle : π.ker ≤ (χ s / χ t).ker := by
    intro g hg
    rw [MonoidHom.mem_ker]
    simp [hred g hg s t]
  obtain ⟨h1, h2⟩ := AlgebraTools.permChar G k π (χ s / χ t) hle
  exact hst' _ h1 h2 (pow_orderOf_eq_one _)
