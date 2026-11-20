import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGoodEmptyIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPsiLocNeOne
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan

noncomputable section

namespace GlobalTheory.RSNonvan.GoodSet

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Establish `key : (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ ∀ a ∈ w.adicCompletionIntegers E, GroundTheory.Global.localAdelicChar E w (a * x) = 1`. Use `forall_congr' fun y => imp_congr Iff.rfl ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `GlobalTheory.StdCharConductor.psi E (sFin E (sLoc E w (x * y))) = 1 ↔ _`. Rewrite using `[GlobalTheory.StdCharConductor.psi_loc_eq_one_iff, mul_comm]`. Rewrite using `[key, GroundTheory.Global.forall_localAdelicChar_mul_eq_one_iff, GroundTheory.Global.mem_localInvDifferent_iff_valued, hw]`.

Express the relevant statement in the definitionally equal form `_ ↔ x ∈ w.adicCompletionIntegers E`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Both sides reduce to the same expression.
-/
theorem psiLoc_cond (w : HeightOneSpectrum (𝓞 E))
    (hw : FractionalIdeal.count E w ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = 0) (x : w.adicCompletion E) :
    (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ x ∈ Ov E w := by
  have key : (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔
      ∀ a ∈ w.adicCompletionIntegers E, GroundTheory.Global.localAdelicChar E w (a * x) = 1 := by
    refine forall_congr' fun y => imp_congr Iff.rfl ?_
    change GlobalTheory.StdCharConductor.psi E (sFin E (sLoc E w (x * y))) = 1 ↔ _
    rw [GlobalTheory.StdCharConductor.psi_loc_eq_one_iff, mul_comm]
  rw [key, GroundTheory.Global.forall_localAdelicChar_mul_eq_one_iff, GroundTheory.Global.mem_localInvDifferent_iff_valued, hw]
  change _ ↔ x ∈ w.adicCompletionIntegers E
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  rfl

/- English proof (translation)
Use `set N : ℕ := Ideal.absNorm u.asIdeal`. Establish `hN : N ≠ 0`. Use `NumberField.HeightOneSpectrum.one_lt_absNorm u` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hI : Ideal.span {(N : 𝓞 E)} ≠ 0`.

Rewrite using `[Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hN` after adjusting the coercions. Use `(Ideal.finite_factors hI).subset fun w' hw' => ?_` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq] at hw' ⊢`. Rewrite using `[Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]`.

Establish `h1 : ((N : ℤ)) ∈ Ideal.comap (algebraMap ℤ (𝓞 E)) u.asIdeal`. Rewrite using `[Ideal.mem_comap, map_natCast]`. Conclude with `Ideal.absNorm_mem u.asIdeal`. Rewrite `h1` using `[← hw', Ideal.mem_comap, map_natCast]`. Conclude with `h1`.
-/
theorem finite_sameBelow (u : HeightOneSpectrum (𝓞 E)) :
    {w' : HeightOneSpectrum (𝓞 E) | Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal =
      Ideal.comap (algebraMap ℤ (𝓞 E)) u.asIdeal}.Finite := by
  set N : ℕ := Ideal.absNorm u.asIdeal
  have hN : N ≠ 0 := by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm u
    omega
  have hI : Ideal.span {(N : 𝓞 E)} ≠ 0 := by
    rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN
  refine (Ideal.finite_factors hI).subset fun w' hw' => ?_
  simp only [Set.mem_setOf_eq] at hw' ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
  have h1 : ((N : ℤ)) ∈ Ideal.comap (algebraMap ℤ (𝓞 E)) u.asIdeal := by
    rw [Ideal.mem_comap, map_natCast]
    exact Ideal.absNorm_mem u.asIdeal
  rw [← hw', Ideal.mem_comap, map_natCast] at h1
  exact h1

variable [IsTotallyComplex E]

/- English proof (translation)
Establish `hD : {w : HeightOneSpectrum (𝓞 E) | FractionalIdeal.count E w ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0}.Finite` using `FractionalIdeal.finite_factors (K := E) ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)`. Use `set T₁ : Finset (HeightOneSpectrum (𝓞 E)) := T ∪ hD.toFinset`. Use `set S : Set (HeightOneSpectrum (𝓞 E)) := {w' | ∃ u ∈ T₁, Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal = Ideal.comap (algebraMap ℤ (𝓞 E)) u.asIdeal}`. Establish `hS : S.Finite`. Establish `: S = ⋃ u ∈ T₁, {w' : HeightOneSpectrum (𝓞 E) | Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal = Ideal.comap (algebraMap ℤ (𝓞 E)) u.asIdeal}`.

Use extensionality with `w'`. Simplify using `[S]`. Rewrite using `[this]`. Conclude with `T₁.finite_toSet.biUnion fun u _ => finite_sameBelow u`. Establish `hT₁ : ∀ w ∈ T₁, w ∈ hS.toFinset` using `fun w hw => by`.

Rewrite using `[Set.Finite.mem_toFinset]`. Conclude with `⟨w, hw, rfl⟩`. Use `⟨hS.toFinset, fun w hw => hT₁ w (Finset.mem_union_left _ hw), ?_, ?_⟩` and prove the remaining obligations. Introduce `w hw w' hw'`. Rewrite `hw`, the goal using `[Set.Finite.mem_toFinset]`.

Take `⟨u, hu, hwu⟩` from `hw`. Conclude with `⟨u, hu, hw'.trans hwu⟩`. Introduce `w hw x`. Use `psiLoc_cond w ?_ x` and prove the remaining obligations. Assume the negation of the conclusion as `h`.

Conclude with `hw (hT₁ w (Finset.mem_union_right _ (by simpa using h)))`.
-/
theorem exists_isGood_superset (T : Finset (HeightOneSpectrum (𝓞 E))) :
    ∃ T' : Finset (HeightOneSpectrum (𝓞 E)), T ⊆ T' ∧ IsGood T' := by
  classical
  have hD : {w : HeightOneSpectrum (𝓞 E) | FractionalIdeal.count E w ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0}.Finite :=
    FractionalIdeal.finite_factors (K := E) ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
  set T₁ : Finset (HeightOneSpectrum (𝓞 E)) := T ∪ hD.toFinset
  set S : Set (HeightOneSpectrum (𝓞 E)) := {w' | ∃ u ∈ T₁, Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal =
      Ideal.comap (algebraMap ℤ (𝓞 E)) u.asIdeal}
  have hS : S.Finite := by
    have : S = ⋃ u ∈ T₁, {w' : HeightOneSpectrum (𝓞 E) | Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal =
        Ideal.comap (algebraMap ℤ (𝓞 E)) u.asIdeal} := by
      ext w'
      simp [S]
    rw [this]
    exact T₁.finite_toSet.biUnion fun u _ => finite_sameBelow u
  have hT₁ : ∀ w ∈ T₁, w ∈ hS.toFinset := fun w hw => by
    rw [Set.Finite.mem_toFinset]
    exact ⟨w, hw, rfl⟩
  refine ⟨hS.toFinset, fun w hw => hT₁ w (Finset.mem_union_left _ hw), ?_, ?_⟩
  · intro w hw w' hw'
    rw [Set.Finite.mem_toFinset] at hw ⊢
    obtain ⟨u, hu, hwu⟩ := hw
    exact ⟨u, hu, hw'.trans hwu⟩
  · intro w hw x
    refine psiLoc_cond w ?_ x
    by_contra h
    exact hw (hT₁ w (Finset.mem_union_right _ (by simpa using h)))

end GlobalTheory.RSNonvan.GoodSet

/- English proof (translation)
Introduce `_ _ _ _ T` and use `GlobalTheory.RSNonvan.GoodSet.exists_isGood_superset T`.
-/
theorem GlobalTheory.RSNonvan.exists_isGood_superset_all : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E]
    (T : Finset (HeightOneSpectrum (𝓞 E))), ∃ T' : Finset (HeightOneSpectrum (𝓞 E)), T ⊆ T' ∧ IsGood T' :=
  fun _ _ _ _ T => GlobalTheory.RSNonvan.GoodSet.exists_isGood_superset T

end
