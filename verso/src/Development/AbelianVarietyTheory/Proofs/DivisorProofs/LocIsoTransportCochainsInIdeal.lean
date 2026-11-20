import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleFirstOrderTaylorSqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftsSqZeroClassifiedByDifferentialsStatement

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys

/- English proof (translation)
Use `Ideal.mul_mem_mul hu hv` as an intermediate fact. Rewrite `this` using `[← pow_two, hJ, Ideal.zero_eq_bot, Ideal.mem_bot]`. Then use the resulting hypothesis.
-/
theorem mul_eq_zero_of_mem_sqMap {R : Type} [CommRing R] {I : Ideal R} {B : Type} [CommRing B] [Algebra R B]
    (hJ : I.map (algebraMap R B) ^ 2 = 0) {u v : B} (hu : u ∈ I.map (algebraMap R B))
    (hv : v ∈ I.map (algebraMap R B)) : u * v = 0 := by
  have := Ideal.mul_mem_mul hu hv
  rwa [← pow_two, hJ, Ideal.zero_eq_bot, Ideal.mem_bot] at this

/- English proof (translation)
Use `Ideal.mem_map_of_mem (f : A →+* B) hx` as an intermediate fact. Rewrite `this` using `[Ideal.map_map, AlgHom.comp_algebraMap]`. Then use the resulting hypothesis.
-/
theorem algHom_apply_mem_map {R : Type} [CommRing R] {I : Ideal R} {A B : Type} [CommRing A] [Algebra R A] [CommRing B]
    [Algebra R B] (f : A →ₐ[R] B) {x : A} (hx : x ∈ I.map (algebraMap R A)) : f x ∈ I.map (algebraMap R B) := by
  have := Ideal.mem_map_of_mem (f : A →+* B) hx
  rwa [Ideal.map_map, AlgHom.comp_algebraMap] at this

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨r, -, rfl⟩` from `hy`. Rewrite using `[AlgHom.commutes, AlgHom.commutes]`. Consider the case `zero => rw [map_zero, map_zero]`.

Consider the case `add y y' _ _ h1 h2 => rw [map_add, map_add, h1, h2]`. Consider the case `smul a y hy ih`. Rewrite using `[smul_eq_mul, map_mul, map_mul, ← ih, ← sub_eq_zero, ← sub_mul]`. Conclude with `mul_eq_zero_of_mem_sqMap hJ (h a) (algHom_apply_mem_map f hy)`.
-/
theorem eq_of_sub_mem_map {R : Type} [CommRing R] {I : Ideal R} {A B : Type} [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] (hJ : I.map (algebraMap R B) ^ 2 = 0) (f g : A →ₐ[R] B)
    (h : ∀ b, f b - g b ∈ I.map (algebraMap R B)) {x : A} (hx : x ∈ I.map (algebraMap R A)) : f x = g x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨r, -, rfl⟩ := hy
    rw [AlgHom.commutes, AlgHom.commutes]
  | zero => rw [map_zero, map_zero]
  | add y y' _ _ h1 h2 => rw [map_add, map_add, h1, h2]
  | smul a y hy ih =>
    rw [smul_eq_mul, map_mul, map_mul, ← ih, ← sub_eq_zero, ← sub_mul]
    exact mul_eq_zero_of_mem_sqMap hJ (h a) (algHom_apply_mem_map f hy)

/- English proof (translation)
Introduce `R R₀ _ _ I hI π hπ hk X₀ s₀ S S' Φ`. Establish `hres : ∀ (U V : AffOp X₀) (a : U ⟶ V) (b : S.F.obj U), mp S'.F a (Φ.φ U b) - Φ.φ V (mp S.F a b) ∈ I.map (algebraMap R (S'.F.obj V))` using `fun U V a b ↦ by`. Rewrite using `[← S'.ker V, map_sub, S'.nat a, Φ.red, Φ.red, S.nat a, sub_self]`. Establish `hcomm : ∀ (U V : AffOp X₀) (a : U ⟶ V) (x : S.F.obj U), x ∈ I.map (algebraMap R (S.F.obj U)) → mp S'.F a (Φ.φ U x) = Φ.φ V (mp S.F a x)` using `fun U V a x hx ↦ eq_of_sub_mem_map (map_sq hI _) ((mp S'.F a).comp (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U)) ((Φ.φ V : S.F.obj V →ₐ[R] S'.F.obj V).comp (mp S.F a)) (hres U V a) hx`. Establish `c1 : ∀ z : Z1 S.F, S.IsIdealValuedLiftSystemCocycle z → ∃ z' : Z1 S'.F, S'.IsIdealValuedLiftSystemCocycle z' ∧ ∀ U V a, z'.1 U V a = Φ.φ V (z.1 U V a)`.

Introduce `z hz`. Use `⟨⟨fun U V a ↦ Φ.φ V (z.1 U V a), ?_⟩, fun U V a ↦ ?_, fun _ _ _ ↦ rfl⟩` and prove the remaining obligations. Introduce `U V W a b show Φ.φ W (z.1 U W (a ≫ b)) = mp S'.F b (Φ.φ V (z.1 U V a)) + Φ.φ W (z.1 V W b)`. Rewrite using `[Z1.comp z a b, map_add, hcomm V W b _ (hz U V a)]`. Conclude with `algHom_apply_mem_map (Φ.φ V : S.F.obj V →ₐ[R] S'.F.obj V) (hz U V a)`.

Establish `c2 : ∀ g : C0 S.F, S.IsIdealValuedLiftSystemCochain g → ∀ U V a, d0 S'.F (fun W ↦ Φ.φ W (g W)) U V a = Φ.φ V (d0 S.F g U V a)`. Introduce `g hg U V a`. Rewrite using `[amitsur_d0_apply, amitsur_d0_apply, map_sub, hcomm U V a _ (hg U)]`. Use `⟨c1, c2, fun c hc ↦ ?_⟩` and prove the remaining obligations. Use `Submodule.smul_induction_on hc ?_ ?_` and prove the remaining obligations.

Introduce `r hr c₀ _`. Take `⟨f, rfl⟩` from `H1.mk_surjective _ c₀`. Set `z : Z1 S.F` to `r • (S.coef hI).pullbackOneCocycle f`. Establish `hzI : S.IsIdealValuedLiftSystemCocycle z` using `fun U V a ↦ by show r • (show S.F.obj V from ev f ((S.thick hI).map a)) ∈ I.map (algebraMap R (S.F.obj V))`. Rewrite using `[Algebra.smul_def, mul_comm]`.

Conclude with `Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hr)`. Take `⟨z', -, hz'⟩` from `c1 z hzI`. Use `⟨z, z', hzI, ?_, ?_, hz'⟩` and prove the remaining obligations. Use `show H1.mk _ (r • _) = S.r hI (r • H1.mk _ f)`. Rewrite using `[map_smul, map_smul]`.

Both sides reduce to the same expression. Rewrite using `[map_smul, show S'.r hI (H1.mk _ f) = H1.mk _ ((S'.coef hI).pullbackOneCocycle f) from rfl, ← map_smul, H1.mk_eq_mk]`. Set `ΦH : ∀ W : AffOp X₀, S.thickObj hI W ⟶ S'.thickObj hI W` to `fun W ↦ S.thickHom S' hI (𝟙 W) (Φ.φ W : S.F.obj W →ₐ[R] S'.F.obj W) (fun b ↦ (Φ.red W b).trans (mp_id (OAff s₀) W (S.p W b)).symm)`. Use `⟨fun W ↦ -(r • @id (S'.F.obj W) (ev f (ΦH W))), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `U V a`.

Establish `hz''` using `hz' U V a`. Establish `e1 : @id (S'.F.obj V) (ev f (ΦH U ≫ (S'.thick hI).map a)) = mp S'.F a (@id (S'.F.obj U) (ev f (ΦH U))) + @id (S'.F.obj V) (ev f ((S'.thick hI).map a))` using `ev_comp f (ΦH U) ((S'.thick hI).map a)`. Establish `e2 : @id (S'.F.obj V) (ev f ((S.thick hI).map a ≫ ΦH V)) = Φ.φ V (@id (S.F.obj V) (ev f ((S.thick hI).map a))) + @id (S'.F.obj V) (ev f (ΦH V))` using `ev_comp f ((S.thick hI).map a) (ΦH V)`. Establish `e3 : algebraMap R (S'.F.obj V) r * (@id (S'.F.obj V) (ev f ((S.thick hI).map a ≫ ΦH V)) - @id (S'.F.obj V) (ev f (ΦH U ≫ (S'.thick hI).map a))) = 0`. Take `⟨⟨Q, hQ⟩, tay⟩` from `GlobalTheory.T.crystallineCocycle_firstOrder_taylor_sqZero R R₀ I hI π hπ hk X₀ s₀ S S' U V`.

Take `⟨θ, hθ, -⟩` from `(GlobalTheory.T.algHom_lifts_sqZero_classified_by_differentials R R₀ (S.F.obj U) (Sec s₀ U.unop.1) (S'.F.obj V) I hI π hπ (S.p U) (S.semi U) (S.surj U) (S.ker U) ((mp S'.F a).comp (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U))).1 ((Φ.φ V : S.F.obj V →ₐ[R] S'.F.obj V).comp (mp S.F a)) (hre …`. Establish `t` using `tay Q hQ (ΦH U ≫ (S'.thick hI).map a) ((S.thick hI).map a ≫ ΦH V) θ hθ f`. Establish `t' : @id (S'.F.obj V) (ev f ((S.thick hI).map a ≫ ΦH V)) - @id (S'.F.obj V) (ev f (ΦH U ≫ (S'.thick hI).map a)) ∈ I.map (algebraMap R (S'.F.obj V))`. Rewrite using `[show @id (S'.F.obj V) (ev f ((S.thick hI).map a ≫ ΦH V)) - @id (S'.F.obj V) (ev f (ΦH U ≫ (S'.thick hI).map a)) = _ from t]`. Conclude with `hθ.mem _`.

Conclude with `mul_eq_zero_of_mem_sqMap (map_sq hI _) (Ideal.mem_map_of_mem _ hr) t'`. Use `show -(r • @id (S'.F.obj V) (ev f (ΦH V))) - mp S'.F a (-(r • @id (S'.F.obj U) (ev f (ΦH U)))) = z'.1 U V a - r • @id (S'.F.obj V) (ev f ((S'.thick hI).map a))`. Rewrite using `[hz'']`. Use `show _ = Φ.φ V (r • @id (S.F.obj V) (ev f ((S.thick hI).map a))) - _`. Rewrite using `[map_neg, map_smul, map_smul]`.

Simplify using `only [Algebra.smul_def]`. Take the linear combination `-(algebraMap R (S'.F.obj V) r) * (e1 - e2) - e3`. Introduce and unpack `x y ⟨z₁, z₁', h₁, hx₁, hx₁', e₁⟩ ⟨z₂, z₂', h₂, hy₂, hy₂', e₂⟩`. Use `⟨z₁ + z₂, z₁' + z₂', fun U V a ↦ ?_, ?_, ?_, fun U V a ↦ ?_⟩` and prove the remaining obligations. Use `show z₁.1 U V a + z₂.1 U V a ∈ _`.

Conclude with `Ideal.add_mem _ (h₁ U V a) (h₂ U V a)`. Rewrite using `[map_add, map_add, hx₁, hy₂]`. Rewrite using `[map_add, map_add, hx₁', hy₂']`. Use `show z₁'.1 U V a + z₂'.1 U V a = Φ.φ V (z₁.1 U V a + z₂.1 U V a)`. Rewrite using `[map_add, e₁, e₂]`.
-/
theorem locIso_transport : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (S S' : Sys I π s₀) (Φ : S.LocIso S'), (∀ z : Z1 S.F, S.IsIdealValuedLiftSystemCocycle z → ∃ z' : Z1 S'.F, S'.IsIdealValuedLiftSystemCocycle z' ∧ ∀ U V a, z'.1 U V a = Φ.φ V (z.1 U V a)) ∧ (∀ g : C0 S.F, S.IsIdealValuedLiftSystemCochain g → ∀ U V a, d0 S'.F (fun W ↦ Φ.φ W (g W)) U V a = Φ.φ V (d0 S.F g U V a)) ∧ ∀ c ∈ I • (⊤ : Submodule R (Cr hI π s₀)), ∃ (z : Z1 S.F) (z' : Z1 S'.F), S.IsIdealValuedLiftSystemCocycle z ∧ H1.mk _ z = S.r hI c ∧ H1.mk _ z' = S'.r hI c ∧ ∀ U V a, z'.1 U V a = Φ.φ V (z.1 U V a) := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ S S' Φ
  have hres : ∀ (U V : AffOp X₀) (a : U ⟶ V) (b : S.F.obj U),
      mp S'.F a (Φ.φ U b) - Φ.φ V (mp S.F a b) ∈ I.map (algebraMap R (S'.F.obj V)) := fun U V a b ↦ by
    rw [← S'.ker V, map_sub, S'.nat a, Φ.red, Φ.red, S.nat a, sub_self]
  have hcomm : ∀ (U V : AffOp X₀) (a : U ⟶ V) (x : S.F.obj U), x ∈ I.map (algebraMap R (S.F.obj U)) →
      mp S'.F a (Φ.φ U x) = Φ.φ V (mp S.F a x) := fun U V a x hx ↦
    eq_of_sub_mem_map (map_sq hI _) ((mp S'.F a).comp (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U))
      ((Φ.φ V : S.F.obj V →ₐ[R] S'.F.obj V).comp (mp S.F a)) (hres U V a) hx
  have c1 : ∀ z : Z1 S.F, S.IsIdealValuedLiftSystemCocycle z → ∃ z' : Z1 S'.F, S'.IsIdealValuedLiftSystemCocycle z' ∧ ∀ U V a, z'.1 U V a = Φ.φ V (z.1 U V a) := by
    intro z hz
    refine ⟨⟨fun U V a ↦ Φ.φ V (z.1 U V a), ?_⟩, fun U V a ↦ ?_, fun _ _ _ ↦ rfl⟩
    · intro U V W a b
      show Φ.φ W (z.1 U W (a ≫ b)) = mp S'.F b (Φ.φ V (z.1 U V a)) + Φ.φ W (z.1 V W b)
      rw [Z1.comp z a b, map_add, hcomm V W b _ (hz U V a)]
    · exact algHom_apply_mem_map (Φ.φ V : S.F.obj V →ₐ[R] S'.F.obj V) (hz U V a)
  have c2 : ∀ g : C0 S.F, S.IsIdealValuedLiftSystemCochain g → ∀ U V a,
      d0 S'.F (fun W ↦ Φ.φ W (g W)) U V a = Φ.φ V (d0 S.F g U V a) := by
    intro g hg U V a
    rw [amitsur_d0_apply, amitsur_d0_apply, map_sub, hcomm U V a _ (hg U)]
  refine ⟨c1, c2, fun c hc ↦ ?_⟩
  refine Submodule.smul_induction_on hc ?_ ?_
  · intro r hr c₀ _
    obtain ⟨f, rfl⟩ := H1.mk_surjective _ c₀
    let z : Z1 S.F := r • (S.coef hI).pullbackOneCocycle f
    have hzI : S.IsIdealValuedLiftSystemCocycle z := fun U V a ↦ by
      show r • (show S.F.obj V from ev f ((S.thick hI).map a)) ∈ I.map (algebraMap R (S.F.obj V))
      rw [Algebra.smul_def, mul_comm]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hr)
    obtain ⟨z', -, hz'⟩ := c1 z hzI
    refine ⟨z, z', hzI, ?_, ?_, hz'⟩
    · show H1.mk _ (r • _) = S.r hI (r • H1.mk _ f)
      rw [map_smul, map_smul]
      rfl
    · rw [map_smul, show S'.r hI (H1.mk _ f) = H1.mk _ ((S'.coef hI).pullbackOneCocycle f) from rfl, ← map_smul,
        H1.mk_eq_mk]
      let ΦH : ∀ W : AffOp X₀, S.thickObj hI W ⟶ S'.thickObj hI W := fun W ↦
        S.thickHom S' hI (𝟙 W) (Φ.φ W : S.F.obj W →ₐ[R] S'.F.obj W)
          (fun b ↦ (Φ.red W b).trans (mp_id (OAff s₀) W (S.p W b)).symm)
      refine ⟨fun W ↦ -(r • @id (S'.F.obj W) (ev f (ΦH W))), ?_⟩
      funext U V a
      have hz'' := hz' U V a
      have e1 : @id (S'.F.obj V) (ev f (ΦH U ≫ (S'.thick hI).map a)) =
          mp S'.F a (@id (S'.F.obj U) (ev f (ΦH U))) + @id (S'.F.obj V) (ev f ((S'.thick hI).map a)) :=
        ev_comp f (ΦH U) ((S'.thick hI).map a)
      have e2 : @id (S'.F.obj V) (ev f ((S.thick hI).map a ≫ ΦH V)) =
          Φ.φ V (@id (S.F.obj V) (ev f ((S.thick hI).map a))) + @id (S'.F.obj V) (ev f (ΦH V)) :=
        ev_comp f ((S.thick hI).map a) (ΦH V)
      have e3 : algebraMap R (S'.F.obj V) r * (@id (S'.F.obj V) (ev f ((S.thick hI).map a ≫ ΦH V)) -
          @id (S'.F.obj V) (ev f (ΦH U ≫ (S'.thick hI).map a))) = 0 := by
        obtain ⟨⟨Q, hQ⟩, tay⟩ := GlobalTheory.T.crystallineCocycle_firstOrder_taylor_sqZero R R₀ I hI π hπ hk X₀ s₀ S S' U V
        obtain ⟨θ, hθ, -⟩ := (GlobalTheory.T.algHom_lifts_sqZero_classified_by_differentials R R₀ (S.F.obj U) (Sec s₀ U.unop.1) (S'.F.obj V) I hI π hπ (S.p U)
          (S.semi U) (S.surj U) (S.ker U) ((mp S'.F a).comp (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U))).1
          ((Φ.φ V : S.F.obj V →ₐ[R] S'.F.obj V).comp (mp S.F a)) (hres U V a)
        have t := tay Q hQ (ΦH U ≫ (S'.thick hI).map a) ((S.thick hI).map a ≫ ΦH V) θ hθ f
        have t' : @id (S'.F.obj V) (ev f ((S.thick hI).map a ≫ ΦH V)) -
            @id (S'.F.obj V) (ev f (ΦH U ≫ (S'.thick hI).map a)) ∈ I.map (algebraMap R (S'.F.obj V)) := by
          rw [show @id (S'.F.obj V) (ev f ((S.thick hI).map a ≫ ΦH V)) -
            @id (S'.F.obj V) (ev f (ΦH U ≫ (S'.thick hI).map a)) = _ from t]
          exact hθ.mem _
        exact mul_eq_zero_of_mem_sqMap (map_sq hI _) (Ideal.mem_map_of_mem _ hr) t'
      show -(r • @id (S'.F.obj V) (ev f (ΦH V))) - mp S'.F a (-(r • @id (S'.F.obj U) (ev f (ΦH U)))) =
        z'.1 U V a - r • @id (S'.F.obj V) (ev f ((S'.thick hI).map a))
      rw [hz'']
      show _ = Φ.φ V (r • @id (S.F.obj V) (ev f ((S.thick hI).map a))) - _
      rw [map_neg, map_smul, map_smul]
      simp only [Algebra.smul_def]
      linear_combination -(algebraMap R (S'.F.obj V) r) * (e1 - e2) - e3
  · rintro x y ⟨z₁, z₁', h₁, hx₁, hx₁', e₁⟩ ⟨z₂, z₂', h₂, hy₂, hy₂', e₂⟩
    refine ⟨z₁ + z₂, z₁' + z₂', fun U V a ↦ ?_, ?_, ?_, fun U V a ↦ ?_⟩
    · show z₁.1 U V a + z₂.1 U V a ∈ _
      exact Ideal.add_mem _ (h₁ U V a) (h₂ U V a)
    · rw [map_add, map_add, hx₁, hy₂]
    · rw [map_add, map_add, hx₁', hy₂']
    · show z₁'.1 U V a + z₂'.1 U V a = Φ.φ V (z₁.1 U V a + z₂.1 U V a)
      rw [map_add, e₁, e₂]

end GlobalTheory.LiftSys
