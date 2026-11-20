import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulEqZeroOfMemMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearLiftOfProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftsSqZeroClassifiedByDifferentialsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapNaturalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDifferenceDerivationOfLiftsAddSwapUniqueStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.Obs

/- English proof (translation)
Introduce `R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ s₀ hP C' _ F' L L' n l h`. Take `⟨κ, -, -, hκ, -, -, -⟩` from `h 0`. Set `W : Submodule R (∀ T : C', L'.B T)` to `{ carrier := {m | ∀ T, m T ∈ I.map (algebraMap R (L'.B T))} add_mem' := fun {m m'} hm hm' T ↦ Ideal.add_mem _ (hm T) (hm' T) zero_mem' := fun T ↦ Ideal.zero_mem _ smul_mem' := fun r m hm T ↦ by show r • m T ∈ _`. Rewrite using `[Algebra.smul_def]`. Conclude with `Ideal.mul_mem_left _ _ (hm T) }`.

Establish `hW : ∀ r, π r = 0 → ∀ m ∈ W, r • m = 0`. Introduce `r hr m hm`. Use function extensionality and compare the values at `T`. Use `show r • m T = 0`. Establish `hrI : r ∈ I` using `hk ▸ RingHom.mem_ker.2 hr`.

Establish `h2` using `Ideal.mul_mem_mul (Ideal.mem_map_of_mem (algebraMap R (L'.B T)) hrI) (hm T)`. Rewrite `h2` using `[← sq, map_sq hI]`. Rewrite using `[Algebra.smul_def]`. Simplify using `using h2`. Set `q : (∀ T : C', L'.B T) →ₗ[R] (∀ (T T' : C') (_ : T ⟶ T'), L'.B T')` to `{ toFun := fun m T T' a ↦ m T' - L'.ρ a (m T) map_add' := fun m m' ↦ by funext T T' a; simp only [Pi.add_apply, map_add]; abel map_smul' := fun r m ↦ by`.

Use function extensionality and compare the values at `T T' a`. Simplify using `only [Pi.smul_apply, map_smul, smul_sub, RingHom.id_apply] }`. Set `v : GlobForm s₀ →+ (∀ (T T' : C') (_ : T ⟶ T'), L'.B T')` to `{ toFun := fun w T T' a ↦ κ T T' a (w.1 (n.G.obj T)) map_zero' := by funext T T' a; exact map_zero (κ T T' a) map_add' := fun w w' ↦ by funext T T' a; exact map_add (κ T T' a) _ _ }`. Establish `hv : ∀ (r : R) w, v (π r • w) = r • v w`. Introduce `r w`.

Use function extensionality and compare the values at `T T' a`. Use `show κ T T' a (π r • w.1 (n.G.obj T)) = r • κ T T' a (w.1 (n.G.obj T))`. Establish `hp : L.p (n.G.obj T) (algebraMap R (L.B (n.G.obj T)) r) = algebraMap R₀ _ (π r)`. Establish `h1` using `L.semi (n.G.obj T) r 1`. Rewrite `h1` using `[← Algebra.algebraMap_eq_smul_one, map_one]`.

Rewrite using `[h1, Algebra.algebraMap_eq_smul_one]`. Establish `h3` using `(hκ T T' a).smul (algebraMap R _ r) (w.1 (n.G.obj T))`. Rewrite `h3` using `[hp, algebraMap_smul, AlgHom.commutes]`. Rewrite using `[h3, Algebra.smul_def]`. Establish `hq : ∀ w, ∃ m ∈ W, q m = v w`.

Introduce `w`. Take `⟨κw, σw, zw, hκw, hσw, hc, hz⟩` from `h w`. Take `⟨f, hf⟩` from `H1.mk_eq_zero.1 hc.symm`. Establish `hκκ : ∀ T T' (a : T ⟶ T'), κ T T' a = κw T T' a` using `fun T T' a ↦ (isTheta_add R R₀ I hI π hπ hk _ _ (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) (L'.B T') _ _ ((l T').comp (L.ρ (n.G.map a))) _ _ (hκ T T' a)).2.2.1 (hκw T T' a)`. Use `⟨fun T ↦ σw T (f T), fun T ↦ (sig_basic R R₀ I hI π hπ hk R₁ α _ _ (L'.p T) (L'.semi T) (L'.surj T) (L'.ker T) (σw T) (hσw T)).1 (f T), ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `T T' a`. Establish `hn` using `(sig_natural R R₀ I hI π hπ hk R₁ α _ _ (L'.p T) (L'.semi T) (L'.surj T) (L'.ker T) _ _ (L'.p T') (L'.semi T') (L'.surj T') (L'.ker T') (L'.ρ a) (mp F' a) (L'.nat a) (σw T) (σw T') (hσw T) (hσw T')).1 (f T)`. Establish `hzf : zw.1 T T' a = f T' - extHom R₁ (mp F' a) (f T)`. Rewrite using `[← hf]`. Both sides reduce to the same expression.

Use `show σw T' (f T') - L'.ρ a (σw T (f T)) = κ T T' a (w.1 (n.G.obj T))`. Rewrite using `[hκκ, ← (hz T T' a).2, hzf, map_sub, hn]`. Take `⟨u, hu1, hu2, hu3⟩` from `exists_semilinear_lift_of_projective R R₀ π hπ (GlobForm s₀) hP _ _ W hW q v hv hq`. Conclude with `⟨κ, u, hκ, hu1, hu2, fun w T T' a ↦ (congrFun (congrFun (congrFun (hu3 w) T) T') a).symm⟩`.
-/
theorem exists_cochain_of_isOb1_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Module.Projective R₀ (GlobForm s₀) → ∀ (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L : Pre I π (OAff s₀)) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) (OAff s₀) F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T), (∀ w, L.IsOb1 L' n l α w 0) → ∃ (κ : ∀ (T T' : C') (_ : T ⟶ T'), Ω[(OAff s₀).obj (n.G.obj T)⁄R₀] →+ L'.B T') (u : GlobForm s₀ →+ ∀ T : C', L'.B T), (∀ (T T' : C') (a : T ⟶ T'), IsTheta I (L.p (n.G.obj T)) ((L'.ρ a).comp (l T)) ((l T').comp (L.ρ (n.G.map a))) (κ T T' a)) ∧ (∀ (r : R) w, u (π r • w) = r • u w) ∧ (∀ w T, u w T ∈ I.map (algebraMap R (L'.B T))) ∧ ∀ (w : GlobForm s₀) (T T' : C') (a : T ⟶ T'), κ T T' a (w.1 (n.G.obj T)) = u w T' - L'.ρ a (u w T) := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ s₀ hP C' _ F' L L' n l h
  obtain ⟨κ, -, -, hκ, -, -, -⟩ := h 0
  let W : Submodule R (∀ T : C', L'.B T) :=
    { carrier := {m | ∀ T, m T ∈ I.map (algebraMap R (L'.B T))}
      add_mem' := fun {m m'} hm hm' T ↦ Ideal.add_mem _ (hm T) (hm' T)
      zero_mem' := fun T ↦ Ideal.zero_mem _
      smul_mem' := fun r m hm T ↦ by
        show r • m T ∈ _
        rw [Algebra.smul_def]
        exact Ideal.mul_mem_left _ _ (hm T) }
  have hW : ∀ r, π r = 0 → ∀ m ∈ W, r • m = 0 := by
    intro r hr m hm
    funext T
    show r • m T = 0
    have hrI : r ∈ I := hk ▸ RingHom.mem_ker.2 hr
    have h2 := Ideal.mul_mem_mul (Ideal.mem_map_of_mem (algebraMap R (L'.B T)) hrI) (hm T)
    rw [← sq, map_sq hI] at h2
    rw [Algebra.smul_def]
    simpa using h2
  let q : (∀ T : C', L'.B T) →ₗ[R] (∀ (T T' : C') (_ : T ⟶ T'), L'.B T') :=
    { toFun := fun m T T' a ↦ m T' - L'.ρ a (m T)
      map_add' := fun m m' ↦ by funext T T' a; simp only [Pi.add_apply, map_add]; abel
      map_smul' := fun r m ↦ by
        funext T T' a; simp only [Pi.smul_apply, map_smul, smul_sub, RingHom.id_apply] }
  let v : GlobForm s₀ →+ (∀ (T T' : C') (_ : T ⟶ T'), L'.B T') :=
    { toFun := fun w T T' a ↦ κ T T' a (w.1 (n.G.obj T))
      map_zero' := by funext T T' a; exact map_zero (κ T T' a)
      map_add' := fun w w' ↦ by funext T T' a; exact map_add (κ T T' a) _ _ }
  have hv : ∀ (r : R) w, v (π r • w) = r • v w := by
    intro r w
    funext T T' a
    show κ T T' a (π r • w.1 (n.G.obj T)) = r • κ T T' a (w.1 (n.G.obj T))
    have hp : L.p (n.G.obj T) (algebraMap R (L.B (n.G.obj T)) r) = algebraMap R₀ _ (π r) := by
      have h1 := L.semi (n.G.obj T) r 1
      rw [← Algebra.algebraMap_eq_smul_one, map_one] at h1
      rw [h1, Algebra.algebraMap_eq_smul_one]
    have h3 := (hκ T T' a).smul (algebraMap R _ r) (w.1 (n.G.obj T))
    rw [hp, algebraMap_smul, AlgHom.commutes] at h3
    rw [h3, Algebra.smul_def]
  have hq : ∀ w, ∃ m ∈ W, q m = v w := by
    intro w
    obtain ⟨κw, σw, zw, hκw, hσw, hc, hz⟩ := h w
    obtain ⟨f, hf⟩ := H1.mk_eq_zero.1 hc.symm
    have hκκ : ∀ T T' (a : T ⟶ T'), κ T T' a = κw T T' a := fun T T' a ↦
      (isTheta_add R R₀ I hI π hπ hk _ _ (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) (L'.B T') _ _ ((l T').comp (L.ρ (n.G.map a))) _ _
        (hκ T T' a)).2.2.1 (hκw T T' a)
    refine ⟨fun T ↦ σw T (f T), fun T ↦ (sig_basic R R₀ I hI π hπ hk R₁ α _ _ (L'.p T) (L'.semi T) (L'.surj T)
      (L'.ker T) (σw T) (hσw T)).1 (f T), ?_⟩
    funext T T' a
    have hn := (sig_natural R R₀ I hI π hπ hk R₁ α _ _ (L'.p T) (L'.semi T) (L'.surj T) (L'.ker T) _ _ (L'.p T')
      (L'.semi T') (L'.surj T') (L'.ker T') (L'.ρ a) (mp F' a) (L'.nat a) (σw T) (σw T') (hσw T) (hσw T')).1 (f T)
    have hzf : zw.1 T T' a = f T' - extHom R₁ (mp F' a) (f T) := by
      rw [← hf]; rfl
    show σw T' (f T') - L'.ρ a (σw T (f T)) = κ T T' a (w.1 (n.G.obj T))
    rw [hκκ, ← (hz T T' a).2, hzf, map_sub, hn]
  obtain ⟨u, hu1, hu2, hu3⟩ := exists_semilinear_lift_of_projective R R₀ π hπ (GlobForm s₀) hP _ _ W hW q v hv hq
  exact ⟨κ, u, hκ, hu1, hu2, fun w T T' a ↦ (congrFun (congrFun (congrFun (hu3 w) T) T') a).symm⟩

end GlobalTheory.Obs
