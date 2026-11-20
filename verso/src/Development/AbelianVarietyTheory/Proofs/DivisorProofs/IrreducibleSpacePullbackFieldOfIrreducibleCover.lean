import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem irreducibleSpace_of_open_cover_meeting {P : Type} [TopologicalSpace P] [Nonempty P]
    (S : Set (Set P)) (hopen : ∀ W ∈ S, IsOpen W) (hirr : ∀ W ∈ S, IsPreirreducible W)
    (hcov : ∀ p : P, ∃ W ∈ S, p ∈ W) (hmeet : ∀ W ∈ S, ∀ W' ∈ S, (W ∩ W').Nonempty) :
    IrreducibleSpace P := by
  refine { isPreirreducible_univ := ?_, toNonempty := inferInstance }
  intro u v hu hv ⟨x, _, hxu⟩ ⟨y, _, hyv⟩
  obtain ⟨Wx, hWx, hxW⟩ := hcov x
  obtain ⟨Wy, hWy, hyW⟩ := hcov y
  obtain ⟨w, hwx, hwu, hwy⟩ :=
    hirr Wx hWx u Wy hu (hopen Wy hWy) ⟨x, hxW, hxu⟩ (hmeet Wx hWx Wy hWy)
  obtain ⟨z, hzW, hz⟩ := hirr Wy hWy u v hu hv ⟨w, hwy, hwu⟩ ⟨y, hyW, hyv⟩
  exact ⟨z, trivial, hz⟩

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem scheme_homOfLE_apply_mk {X : Scheme.{0}} {U V : X.Opens} (e : V ≤ U) (x : X) (hx : x ∈ V) :
    (X.homOfLE e) ⟨x, hx⟩ = ⟨x, e hx⟩ := by
  apply Subtype.ext
  have h1 : (X.homOfLE e ≫ U.ι) ⟨x, hx⟩ = V.ι ⟨x, hx⟩ := by rw [X.homOfLE_ι]
  simpa using h1

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem surjective_spMap_of_field {F k : Type} [Field F] [Field k] (f : F →+* k) :
    Surjective (spMap f) := by
  constructor
  intro x
  obtain ⟨y⟩ : Nonempty (Sp k) := inferInstance
  exact ⟨y, Subsingleton.elim _ _⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem irreducibleSpace_pullback_of_cover : ∀ {F : Type} [Field F] {X : Scheme.{0}} (h : X ⟶ Sp F) (k : Type)
    [Field k] (f : F →+* k) (U : X.Opens),
    IsIrreducible (U : Set X) →
    (∀ y ∈ U, ∃ V : X.Opens, V ≤ U ∧ y ∈ V ∧ IrreducibleSpace ↑(pullback (V.ι ≫ h) (spMap f))) →
    IrreducibleSpace ↑(pullback (U.ι ≫ h) (spMap f)) := by
  intro F _ X h k _ f U hU hV
  haveI := surjective_spMap_of_field f
  set q := pullback.fst (U.ι ≫ h) (spMap f) with hq
  have hqs : Function.Surjective q := q.surjective

  have key : ∀ (V : X.Opens) (hVU : V ≤ U), IrreducibleSpace ↑(pullback (V.ι ≫ h) (spMap f)) →
      IsOpen (Set.range (pullback.snd (X.homOfLE hVU) q)) ∧
      IsPreirreducible (Set.range (pullback.snd (X.homOfLE hVU) q)) ∧
      ∀ p, U.ι (q p) ∈ V → p ∈ Set.range (pullback.snd (X.homOfLE hVU) q) := by
    intro V hVU hirrV
    refine ⟨(pullback.snd (X.homOfLE hVU) q).isOpenEmbedding.isOpen_range, ?_, ?_⟩
    · let e : pullback (V.ι ≫ h) (spMap f) ≅ pullback (X.homOfLE hVU) q :=
        pullback.congrHom (by rw [← X.homOfLE_ι hVU, Category.assoc]) rfl ≪≫
          (pullbackRightPullbackFstIso (U.ι ≫ h) (spMap f) (X.homOfLE hVU)).symm
      haveI : IrreducibleSpace ↑(pullback (X.homOfLE hVU) q) :=
        (Scheme.homeoOfIso e).surjective.irreducibleSpace (Scheme.homeoOfIso e).continuous
      rw [← Set.image_univ]
      exact (PreirreducibleSpace.isPreirreducible_univ (X := ↑(pullback (X.homOfLE hVU) q))).image _
        (pullback.snd (X.homOfLE hVU) q).continuous.continuousOn
    · intro p hp
      rw [Scheme.Pullback.range_snd]
      refine ⟨⟨U.ι (q p), hp⟩, ?_⟩
      show (X.homOfLE hVU) ⟨U.ι (q p), hp⟩ = q p
      rw [scheme_homOfLE_apply_mk]
      rfl
  have hUne : (U : Set X).Nonempty := hU.nonempty
  obtain ⟨y₀, hy₀⟩ := hUne
  obtain ⟨p₀, -⟩ := hqs ⟨y₀, hy₀⟩
  haveI : Nonempty ↑(pullback (U.ι ≫ h) (spMap f)) := ⟨p₀⟩
  let S : Set (Set ↑(pullback (U.ι ≫ h) (spMap f))) :=
    {W | ∃ (V : X.Opens) (hVU : V ≤ U), IrreducibleSpace ↑(pullback (V.ι ≫ h) (spMap f)) ∧
      (V : Set X).Nonempty ∧ W = Set.range (pullback.snd (X.homOfLE hVU) q)}
  refine irreducibleSpace_of_open_cover_meeting S ?_ ?_ ?_ ?_
  · rintro W ⟨V, hVU, hi, -, rfl⟩
    exact (key V hVU hi).1
  · rintro W ⟨V, hVU, hi, -, rfl⟩
    exact (key V hVU hi).2.1
  · intro p
    have hyU : U.ι (q p) ∈ U := (q p).2
    obtain ⟨V, hVU, hyV, hi⟩ := hV _ hyU
    exact ⟨_, ⟨V, hVU, hi, ⟨_, hyV⟩, rfl⟩, (key V hVU hi).2.2 p hyV⟩
  · rintro W ⟨V, hVU, hi, ⟨a, ha⟩, rfl⟩ W' ⟨V', hVU', hi', ⟨b, hb⟩, rfl⟩
    obtain ⟨z, hzU, hzV, hzV'⟩ :=
      hU.2 (V : Set X) (V' : Set X) V.isOpen V'.isOpen ⟨a, hVU ha, ha⟩ ⟨b, hVU' hb, hb⟩
    obtain ⟨p, hp⟩ := hqs ⟨z, hzU⟩
    have hpz : U.ι (q p) = z := by rw [hp]; rfl
    exact ⟨p, (key V hVU hi).2.2 p (hpz ▸ hzV), (key V' hVU' hi').2.2 p (hpz ▸ hzV')⟩

end GlobalTheory
