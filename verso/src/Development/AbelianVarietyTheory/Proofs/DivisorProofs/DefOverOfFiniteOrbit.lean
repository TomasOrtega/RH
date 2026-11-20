import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import GroundTheory.GlobalFields.ComplexMultiplication.AutCFixed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

/- English proof (translation)
Use `haveI := hk`. Assume the negation of the conclusion as `ha`. Establish `htr : Transcendental k₀ a`. Introduce `halg`. Establish `hdeg` using `IsAlgClosed.degree_eq_one_of_irreducible k₀ (minpoly.irreducible halg.isIntegral)`.

Take `⟨c, hc⟩` from `minpoly.mem_range_of_degree_eq_one k₀ a hdeg`. Conclude with `ha (hc ▸ c.2)`. Establish `hc : ∀ c : k₀, ∃ σ : K ≃ₐ[k₀] K, σ a = a + algebraMap k₀ K c`. Introduce `c`. Establish `htr' : Transcendental k₀ (a + algebraMap k₀ K c)` using `fun h' => htr (by simpa using (h'.isIntegral.sub (isIntegral_algebraMap (x := c))).isAlgebraic)`.

Conclude with `GroundTheory.Global.exists_algEquiv_apply_eq_of_transcendental htr htr'`. Use `Set.infinite_of_injective_forall_mem (f := fun c : k₀ => a + algebraMap k₀ K c) ?_ ?_ h` and prove the remaining obligations. Introduce `c d hcd`. Simplify using `using hcd`. Introduce `c`.

Take `⟨σ, hσ⟩` from `hc c`. Conclude with `⟨σ.toRingEquiv, fun b hb => σ.commutes ⟨b, hb⟩, hσ.symm⟩`.
-/
theorem mem_of_finite_conj {K : Type} [Field K] [IsAlgClosed K] (k₀ : Subfield K) (hk : IsAlgClosed k₀)
    (a : K) (h : Set.Finite {b : K | ∃ σ : K ≃+* K, (∀ c ∈ k₀, σ c = c) ∧ b = σ a}) : a ∈ k₀ := by
  haveI := hk
  by_contra ha
  have htr : Transcendental k₀ a := by
    intro halg
    have hdeg := IsAlgClosed.degree_eq_one_of_irreducible k₀ (minpoly.irreducible halg.isIntegral)
    obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one k₀ a hdeg
    exact ha (hc ▸ c.2)
  have hc : ∀ c : k₀, ∃ σ : K ≃ₐ[k₀] K, σ a = a + algebraMap k₀ K c := by
    intro c
    have htr' : Transcendental k₀ (a + algebraMap k₀ K c) := fun h' =>
      htr (by simpa using (h'.isIntegral.sub (isIntegral_algebraMap (x := c))).isAlgebraic)
    exact GroundTheory.Global.exists_algEquiv_apply_eq_of_transcendental htr htr'
  refine Set.infinite_of_injective_forall_mem (f := fun c : k₀ => a + algebraMap k₀ K c) ?_ ?_ h
  · intro c d hcd
    simpa using hcd
  · intro c
    obtain ⟨σ, hσ⟩ := hc c
    exact ⟨σ.toRingEquiv, fun b hb => σ.commutes ⟨b, hb⟩, hσ.symm⟩

/- English proof (translation)
Introduce `K _ _ k₀ hk Y P hfin`. Set `e` to `SpecToEquivOfLocalRing Y (CommRingCat.of K)`. Set `x` to `(e P).1`. Set `f` to `(e P).2.1`. Establish `hP : P = Spec.map f ≫ Y.fromSpecStalk x` using `(e.left_inv P).symm`.

Set `Φ : {g : Y.presheaf.stalk x ⟶ CommRingCat.of K // IsLocalHom g.hom} → (Sp K ⟶ Y)` to `fun g => e.symm ⟨x, g⟩`. Establish `hΦ : Function.Injective Φ`. Introduce `g₁ g₂ h`. Use `e.symm.injective h` as an intermediate fact. Conclude with `eq_of_heq (Sigma.mk.inj this).2`.

Establish `hloc : ∀ σ : K ≃+* K, IsLocalHom (f ≫ CommRingCat.ofHom σ.toRingHom).hom`. Introduce `σ`. Establish `: IsLocalHom f.hom` using `(e P).2.2`. Use `show IsLocalHom (σ.toRingHom.comp f.hom)`. Use `infer_instance`.

Set `T : Set {g : Y.presheaf.stalk x ⟶ CommRingCat.of K // IsLocalHom g.hom}` to `{g | ∃ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) ∧ g.1 = f ≫ CommRingCat.ofHom σ.toRingHom}`. Establish `hT : T.Finite`. Use `Set.Finite.of_finite_image (hfin.subset ?_) hΦ.injOn` and prove the remaining obligations. Introduce and unpack `_ ⟨g, ⟨σ, hσ, hg⟩, rfl⟩`. Use `⟨σ, hσ, ?_⟩` and prove the remaining obligations.

Use `show Spec.map g.1 ≫ Y.fromSpecStalk x = _`. Rewrite using `[hg, Spec.map_comp, Category.assoc, ← hP]`. Establish `hmem : ∀ s, f.hom s ∈ k₀`. Introduce `s`. Use `mem_of_finite_conj k₀ hk _ ((hT.image fun g => g.1.hom s).subset ?_)` and prove the remaining obligations.

Introduce and unpack `_ ⟨σ, hσ, rfl⟩`. Conclude with `⟨⟨f ≫ CommRingCat.ofHom σ.toRingHom, hloc σ⟩, ⟨σ, hσ, rfl⟩, rfl⟩`. Use `⟨Spec.map (CommRingCat.ofHom (f.hom.codRestrict k₀ hmem)) ≫ Y.fromSpecStalk x, ?_⟩` and prove the remaining obligations. Use `Eq.trans ?_ hP.symm` and prove the remaining obligations. Rewrite using `[← Category.assoc, ← Spec.map_comp]`.

Both sides reduce to the same expression.
-/
theorem defOver_of_finite_orbit : ∀ (K : Type) [Field K] [IsAlgClosed K] (k₀ : Subfield K), IsAlgClosed k₀ →
    ∀ (Y : Scheme.{0}) (P : Sp K ⟶ Y),
    Set.Finite {P' : Sp K ⟶ Y | ∃ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) ∧ P' = spMap σ.toRingHom ≫ P} →
    DefOver k₀ P := by
  intro K _ _ k₀ hk Y P hfin
  classical
  let e := SpecToEquivOfLocalRing Y (CommRingCat.of K)
  let x := (e P).1
  let f := (e P).2.1
  have hP : P = Spec.map f ≫ Y.fromSpecStalk x := (e.left_inv P).symm
  let Φ : {g : Y.presheaf.stalk x ⟶ CommRingCat.of K // IsLocalHom g.hom} → (Sp K ⟶ Y) :=
    fun g => e.symm ⟨x, g⟩
  have hΦ : Function.Injective Φ := by
    intro g₁ g₂ h
    have := e.symm.injective h
    exact eq_of_heq (Sigma.mk.inj this).2
  have hloc : ∀ σ : K ≃+* K, IsLocalHom (f ≫ CommRingCat.ofHom σ.toRingHom).hom := by
    intro σ
    have : IsLocalHom f.hom := (e P).2.2
    show IsLocalHom (σ.toRingHom.comp f.hom)
    infer_instance
  let T : Set {g : Y.presheaf.stalk x ⟶ CommRingCat.of K // IsLocalHom g.hom} :=
    {g | ∃ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) ∧ g.1 = f ≫ CommRingCat.ofHom σ.toRingHom}
  have hT : T.Finite := by
    refine Set.Finite.of_finite_image (hfin.subset ?_) hΦ.injOn
    rintro _ ⟨g, ⟨σ, hσ, hg⟩, rfl⟩
    refine ⟨σ, hσ, ?_⟩
    show Spec.map g.1 ≫ Y.fromSpecStalk x = _
    rw [hg, Spec.map_comp, Category.assoc, ← hP]
  have hmem : ∀ s, f.hom s ∈ k₀ := by
    intro s
    refine mem_of_finite_conj k₀ hk _ ((hT.image fun g => g.1.hom s).subset ?_)
    rintro _ ⟨σ, hσ, rfl⟩
    exact ⟨⟨f ≫ CommRingCat.ofHom σ.toRingHom, hloc σ⟩, ⟨σ, hσ, rfl⟩, rfl⟩
  refine ⟨Spec.map (CommRingCat.ofHom (f.hom.codRestrict k₀ hmem)) ≫ Y.fromSpecStalk x, ?_⟩
  refine Eq.trans ?_ hP.symm
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

end GlobalTheory.Poinc.Sep
