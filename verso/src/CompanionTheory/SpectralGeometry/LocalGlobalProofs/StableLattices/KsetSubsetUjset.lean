import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

open Matrix

namespace GlobalTheory.CompanionTheory.DSKType

open CompanionTheory.D.DSIC PI.UpqRep

/- English proof (translation)
Take `⟨h1, h2⟩` from `hg`. Establish `h3 : gᴴ * g = 1`. Simplify `(Matrix.mem_unitaryGroup_iff'.1 h1)` using `[Matrix.star_eq_conjTranspose]`. Use `show inUJ ε g`. Unfold `inUJ`.

Rewrite using `[Matrix.mul_assoc, ← h2, ← Matrix.mul_assoc, h3, Matrix.one_mul]`.
-/
theorem kset_subset_ujset {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) :
    g ∈ UJset ε := by
  obtain ⟨h1, h2⟩ := hg
  have h3 : gᴴ * g = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.1 h1)
  show inUJ ε g
  unfold inUJ
  rw [Matrix.mul_assoc, ← h2, ← Matrix.mul_assoc, h3, Matrix.one_mul]

/- English proof (translation)
Introduce `n ε H _ _ σ S E hσ hM μ x hx0 hfin hhw`. Take `⟨S₀, hfd, hxS, hst⟩` from `hfin`. Establish `hinj : Function.Injective S.subtype` using `S.injective_subtype`. Use `hfd` as an intermediate fact. Establish `hU : FiniteDimensional ℂ (S₀.comap S.subtype)`.

Use `FiniteDimensional.of_injective (LinearMap.codRestrict S₀ (S.subtype ∘ₗ (S₀.comap S.subtype).subtype) (fun y => y.2)) ?_` and prove the remaining obligations. Introduce `a b hab`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `congrArg (fun y : S₀ => (y : H)) hab`.

Establish `hUst : KStab ε E (S₀.comap S.subtype)`. Use `(hS n ε H σ S E hσ hM _ hU).2 ?_` and prove the remaining obligations. Introduce and unpack `g hg _ ⟨v, hv, rfl⟩`. Conclude with `⟨⟨σ g v, hM.stab g (kset_subset_ujset hg) v v.2⟩, hst g hg v hv, rfl⟩`. Establish `hrel : KRel ε E` using `fun a b c d _ _ => hM.gl a b c d`.

Establish `hun : KUnit ε E`. Introduce `a b hab y z`. Use `hM.unit a b y z` as an intermediate fact. Simplify `this` using `[Formalism.REAL.sgn, hab]`. Take `⟨L, hLU, hxL, hLst, hirr, hdom, -⟩` from `hL n ε S E μ x _ hrel hun hx0 hhw hU hUst hxS`.

Establish `hLfd : FiniteDimensional ℂ L` using `Submodule.finiteDimensional_of_le hLU`. Use `⟨L.map S.subtype, inferInstance, (hS n ε H σ S E hσ hM L hLfd).1 hLst, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `S' hle hS'`. Establish `hle' : S'.comap S.subtype ≤ L`. Introduce `y hy`.

Take `⟨z, hz, hzy⟩` from `hle hy`. Rewrite using `[← hinj hzy]` and apply the resulting hypothesis. Establish `hmap : (S'.comap S.subtype).map S.subtype = S'`. Apply `Submodule.map_comap_eq_of_le` to reduce the goal to its premises. Conclude with `hle.trans LinearMap.map_le_range`.

Establish `hst' : KStab ε E (S'.comap S.subtype)`. Use `(hS n ε H σ S E hσ hM _ (Submodule.finiteDimensional_of_le hle')).2 ?_` and prove the remaining obligations. Rewrite using `[hmap]` and apply the resulting hypothesis. Break down `hirr _ hle' hst' with h | h` into its components or cases. Use `left`.

Rewrite using `[← hmap, h, Submodule.map_bot]`. Use `right`. Rewrite using `[← hmap, h]`. Conclude with `⟨x, ⟨x, hxL, rfl⟩, fun h => hx0 (Subtype.ext h), (hW n ε H σ S E hσ hM μ x).1 hhw.1⟩`. Introduce and unpack `ν _ ⟨v, hv, rfl⟩ hv0 hwt`.

Conclude with `hdom ν v hv (fun h => hv0 (by rw [h]; rfl)) ((hW n ε H σ S E hσ hM ν v).2 hwt)`.
-/
theorem typeOfHW (hL : LowSpan) (hS : StabLink) (hW : WtLink) : TypeOfHW := by
  intro n ε H _ _ σ S E hσ hM μ x hx0 hfin hhw
  obtain ⟨S₀, hfd, hxS, hst⟩ := hfin
  have hinj : Function.Injective S.subtype := S.injective_subtype
  have := hfd
  have hU : FiniteDimensional ℂ (S₀.comap S.subtype) := by
    refine FiniteDimensional.of_injective
      (LinearMap.codRestrict S₀ (S.subtype ∘ₗ (S₀.comap S.subtype).subtype) (fun y => y.2)) ?_
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun y : S₀ => (y : H)) hab
  have hUst : KStab ε E (S₀.comap S.subtype) := by
    refine (hS n ε H σ S E hσ hM _ hU).2 ?_
    rintro g hg _ ⟨v, hv, rfl⟩
    exact ⟨⟨σ g v, hM.stab g (kset_subset_ujset hg) v v.2⟩, hst g hg v hv, rfl⟩
  have hrel : KRel ε E := fun a b c d _ _ => hM.gl a b c d
  have hun : KUnit ε E := by
    intro a b hab y z
    have := hM.unit a b y z
    simpa [Formalism.REAL.sgn, hab] using this
  obtain ⟨L, hLU, hxL, hLst, hirr, hdom, -⟩ := hL n ε S E μ x _ hrel hun hx0 hhw hU hUst hxS
  have hLfd : FiniteDimensional ℂ L := Submodule.finiteDimensional_of_le hLU
  refine ⟨L.map S.subtype, inferInstance, (hS n ε H σ S E hσ hM L hLfd).1 hLst, ?_, ?_, ?_⟩
  · intro S' hle hS'
    have hle' : S'.comap S.subtype ≤ L := by
      intro y hy
      obtain ⟨z, hz, hzy⟩ := hle hy
      rwa [← hinj hzy]
    have hmap : (S'.comap S.subtype).map S.subtype = S' := by
      apply Submodule.map_comap_eq_of_le
      exact hle.trans LinearMap.map_le_range
    have hst' : KStab ε E (S'.comap S.subtype) := by
      refine (hS n ε H σ S E hσ hM _ (Submodule.finiteDimensional_of_le hle')).2 ?_
      rwa [hmap]
    rcases hirr _ hle' hst' with h | h
    · left; rw [← hmap, h, Submodule.map_bot]
    · right; rw [← hmap, h]
  · exact ⟨x, ⟨x, hxL, rfl⟩, fun h => hx0 (Subtype.ext h), (hW n ε H σ S E hσ hM μ x).1 hhw.1⟩
  · rintro ν _ ⟨v, hv, rfl⟩ hv0 hwt
    exact hdom ν v hv (fun h => hv0 (by rw [h]; rfl)) ((hW n ε H σ S E hσ hM ν v).2 hwt)

end GlobalTheory.CompanionTheory.DSKType
