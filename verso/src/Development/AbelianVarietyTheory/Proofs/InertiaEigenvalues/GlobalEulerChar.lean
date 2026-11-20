import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.H1MapSubgroup
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

namespace GlobalTheory.EulerScalars

noncomputable def subquotEquiv {R R' X : Type*} [CommRing R] [CommRing R'] [AddCommGroup X]
    [Module R X] [Module R' X] (Z B : Submodule R X) (Z' B' : Submodule R' X)
    (hZ : ∀ x, x ∈ Z ↔ x ∈ Z') (hB : ∀ x, x ∈ B ↔ x ∈ B') :
    (Z ⧸ B.comap Z.subtype) ≃ (Z' ⧸ B'.comap Z'.subtype) :=
  Quotient.congr (Equiv.subtypeEquivRight hZ) fun a b => by
    rw [Submodule.quotientRel_def, Submodule.quotientRel_def]
    exact hB _

/- English proof (translation)
Introduce `hF hE F Ω _ _ _ _ _ _ l _ Λ M _ _ _ _ _ _ S ρ hl hS hc`. Take `⟨_⟩ : Nonempty (Module (ZMod (l ^ 1)) M)` from `⟨AddCommGroup.zmodModule (n := l ^ 1) (by simpa using hl)⟩`. Take `⟨ρ', hρ'⟩ : ∃ ρ' : Representation (ZMod (l ^ 1)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M, ∀ g m, ρ' g m = ρ g m` from `⟨zmodRep (l ^ 1) ρ, fun _ _ => rfl⟩`. Establish `hc' : ContAction ρ'`. Unfold `ReciprocityTheory.Gal.ContAction at hc ⊢`.

Simplify `hc` using `only [hρ']`. Establish `hd : ∀ c : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) → M, ReciprocityTheory.Gal.d1 ρ c = ReciprocityTheory.Gal.d1 ρ' c`. Introduce `c`. Use function extensionality and compare the values at `p`. Break down `p with ⟨g, h⟩` into its components or cases.

Simplify using `only [ReciprocityTheory.Gal.d1_apply, hρ']`. Establish `e0 : {m : M // m ∈ ReciprocityTheory.Gal.H0 ρ} ≃ {m : M // m ∈ ReciprocityTheory.Gal.H0 ρ'}`. Use `Equiv.subtypeEquivRight fun m => ?_` and prove the remaining obligations. Rewrite using `[ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere, ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere]`. Simplify using `only [hρ']`.

Establish `c0 : Nat.card (ReciprocityTheory.Gal.H0 ρ) = Nat.card (ReciprocityTheory.Gal.H0 ρ')` using `Nat.card_congr e0`. Establish `e1 : ReciprocityTheory.Gal.H1 ρ ≃ ReciprocityTheory.Gal.H1 ρ'` using `subquotEquiv _ _ _ _ (fun f => by rw [ReciprocityTheory.Gal.mem_Z1_iff_cocycle, ReciprocityTheory.Gal.mem_Z1_iff_cocycle]; simp only [hρ']) (fun f => by rw [ReciprocityTheory.Gal.mem_coboundaries1, ReciprocityTheory.Gal.mem_coboundaries1]; simp only [hρ'])`. Establish `e2 : ReciprocityTheory.Gal.H2 ρ ≃ ReciprocityTheory.Gal.H2 ρ'` using `subquotEquiv _ _ _ _ (fun f => by rw [ReciprocityTheory.Gal.mem_cocycles2, ReciprocityTheory.Gal.mem_cocycles2]; simp only [hρ']) (fun f => by rw [ReciprocityTheory.Gal.separated_dvr_second_cohomology_mem, ReciprocityTheory.Gal.separated_dvr_second_cohomology_mem]; simp only [hd] …`. Take `⟨-, f1, f2, -⟩` from `hF F Ω l 1 M S ρ' one_pos hS hc'`. Establish `hreal : ∀ w : InfinitePlace F, ¬ w.IsReal` using `fun w => InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w)`.

Establish `heq` using `hE F Ω l 1 M S ρ' one_pos hS hc' (fun _ => 1) (fun w hw => absurd hw (hreal w))`. Establish `harch : archH0Card S ρ' (fun _ => 1) = Nat.card M ^ InfinitePlace.nrComplexPlaces F` using `by classical`. Unfold `archH0Card`. Rewrite using `[Finset.prod_eq_one, one_mul]`. Introduce `w hw`.

Conclude with `absurd (Finset.mem_filter.mp hw).2 (hreal w)`. Rewrite `heq` using `[harch, IsTotallyComplex.finrank]`. Use `⟨Finite.of_equiv _ e1.symm, Finite.of_equiv _ e2.symm, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.card_congr e1, c0, Nat.card_congr e2]`. Establish `hpos : 0 < Nat.card M ^ InfinitePlace.nrComplexPlaces F` using `pow_pos Nat.card_pos _`.

Apply `Nat.eq_of_mul_eq_mul_right hpos` to reduce the goal to its premises. Rewrite using `[← heq, two_mul, pow_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem global_euler_char : GlobalFiniteness → GlobalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (Λ M : Type) [CommRing Λ] [AddCommGroup M] [Module Λ M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (ρ : Representation Λ (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M), (∀ m : M, l • m = 0) → ContainsAbove S l → ContAction ρ → Finite (H1 ρ) ∧ Finite (H2 ρ) ∧ Nat.card (H1 ρ) = Nat.card (H0 ρ) * Nat.card (H2 ρ) * Nat.card M ^ InfinitePlace.nrComplexPlaces F := by
  intro hF hE F Ω _ _ _ _ _ _ l _ Λ M _ _ _ _ _ _ S ρ hl hS hc

  obtain ⟨_⟩ : Nonempty (Module (ZMod (l ^ 1)) M) :=
    ⟨AddCommGroup.zmodModule (n := l ^ 1) (by simpa using hl)⟩
  obtain ⟨ρ', hρ'⟩ : ∃ ρ' : Representation (ZMod (l ^ 1)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M,
      ∀ g m, ρ' g m = ρ g m := ⟨zmodRep (l ^ 1) ρ, fun _ _ => rfl⟩

  have hc' : ContAction ρ' := by
    unfold ReciprocityTheory.Gal.ContAction at hc ⊢
    simpa only [hρ'] using hc
  have hd : ∀ c : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) → M,
      ReciprocityTheory.Gal.d1 ρ c = ReciprocityTheory.Gal.d1 ρ' c := by
    intro c
    funext p
    rcases p with ⟨g, h⟩
    simp only [ReciprocityTheory.Gal.d1_apply, hρ']
  have e0 : {m : M // m ∈ ReciprocityTheory.Gal.H0 ρ} ≃ {m : M // m ∈ ReciprocityTheory.Gal.H0 ρ'} := by
    refine Equiv.subtypeEquivRight fun m => ?_
    rw [ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere, ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere]
    simp only [hρ']
  have c0 : Nat.card (ReciprocityTheory.Gal.H0 ρ) = Nat.card (ReciprocityTheory.Gal.H0 ρ') := Nat.card_congr e0
  have e1 : ReciprocityTheory.Gal.H1 ρ ≃ ReciprocityTheory.Gal.H1 ρ' :=
    subquotEquiv _ _ _ _
      (fun f => by rw [ReciprocityTheory.Gal.mem_Z1_iff_cocycle, ReciprocityTheory.Gal.mem_Z1_iff_cocycle]; simp only [hρ'])
      (fun f => by rw [ReciprocityTheory.Gal.mem_coboundaries1, ReciprocityTheory.Gal.mem_coboundaries1]; simp only [hρ'])
  have e2 : ReciprocityTheory.Gal.H2 ρ ≃ ReciprocityTheory.Gal.H2 ρ' :=
    subquotEquiv _ _ _ _
      (fun f => by rw [ReciprocityTheory.Gal.mem_cocycles2, ReciprocityTheory.Gal.mem_cocycles2]; simp only [hρ'])
      (fun f => by rw [ReciprocityTheory.Gal.separated_dvr_second_cohomology_mem, ReciprocityTheory.Gal.separated_dvr_second_cohomology_mem]; simp only [hd])

  obtain ⟨-, f1, f2, -⟩ := hF F Ω l 1 M S ρ' one_pos hS hc'
  have hreal : ∀ w : InfinitePlace F, ¬ w.IsReal := fun w =>
    InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w)
  have heq := hE F Ω l 1 M S ρ' one_pos hS hc' (fun _ => 1) (fun w hw => absurd hw (hreal w))

  have harch : archH0Card S ρ' (fun _ => 1) = Nat.card M ^ InfinitePlace.nrComplexPlaces F := by
    classical
    unfold archH0Card
    rw [Finset.prod_eq_one, one_mul]
    intro w hw
    exact absurd (Finset.mem_filter.mp hw).2 (hreal w)
  rw [harch, IsTotallyComplex.finrank] at heq
  refine ⟨Finite.of_equiv _ e1.symm, Finite.of_equiv _ e2.symm, ?_⟩
  rw [Nat.card_congr e1, c0, Nat.card_congr e2]
  have hpos : 0 < Nat.card M ^ InfinitePlace.nrComplexPlaces F := pow_pos Nat.card_pos _
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [← heq, two_mul, pow_add]
  ring

end GlobalTheory.EulerScalars
