import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCSt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HermitianDatumDirectPowerStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeilPairingPowPolAVEqProdFieldStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

/- English proof (translation)
Use `⟨{ ζ := I.ζ, ζ_prim := I.ζ_prim, ζ_pow := I.ζ_pow ev := fun n a => φ.symm (fun i => I.ev n (e a i)) add := ?_, lin := ?_, ker := ?_, onto := ?_, tower := ?_, isom := ?_ }⟩` and prove the remaining obligations. Introduce `n a b`. Rewrite using `[← map_mul]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Simplify using `[I.add]`. Introduce `n c a`. Apply `φ.injective` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Simplify using `[hact, I.lin]`.

Introduce `n hn a`. Rewrite using `[MulEquiv.map_eq_one_iff, funext_iff]`. Simplify using `only [Pi.one_apply, I.ker n hn]`. Prove the components needed by the constructor for the conclusion. Introduce `h choose b hb using h`.

Use `⟨e.symm b, e.injective ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `[hb i]`. Introduce and unpack `⟨b, rfl⟩ i`. Conclude with `⟨e b i, by simp⟩`.

Introduce `n hn x`. Rewrite using `[← φ.map_eq_one_iff, map_pow, funext_iff]`. Simplify using `only [Pi.pow_apply, Pi.one_apply, I.onto n hn]`. Prove the components needed by the constructor for the conclusion. Introduce `h choose b hb using h`.

Use `⟨e.symm b, φ.injective ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `[hb i]`. Introduce and unpack `⟨a, rfl⟩ i`. Conclude with `⟨e a i, by simp⟩`.

Introduce `n m hn hm a`. Rewrite using `[← map_pow]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `[I.tower n m hn hm]`.

Introduce `n hn a b`. Establish `hz : I.ζ n ^ Dw'.EF a b = ∏ i, I.ζ n ^ Dw.EF (e a i) (e b i)`. Rewrite using `[he]`. Conclude with `map_prod (zpowersHom Fˣ (I.ζ n)) (fun i => Multiplicative.ofAdd (Dw.EF (e a i) (e b i))) Finset.univ`. Rewrite using `[hz]`.

Apply `hw n hn` to reduce the goal to its premises. Introduce `i`. Simplify using `using I.isom n hn (e a i) (e b i)`.
-/
theorem nonempty_tateIso_of_mulEquiv_pi {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    (Dw Dw' : Datum H) (j : ℕ) (e : Dw'.La ≃ₗ[𝓞 E] (Fin j → Dw.La))
    (he : ∀ x y, Dw'.EF x y = ∑ i, Dw.EF (e x i) (e y i))
    (F : Type) [Field F] (Q Q' : Type) [Group Q] [Group Q'] (φ : Q' ≃* (Fin j → Q))
    (act : 𝓞 E → Q → Q) (act' : 𝓞 E → Q' → Q') (hact : ∀ a x i, φ (act' a x) i = act a (φ x i))
    (w : ℕ → Q → Q → Fˣ → Prop) (w' : ℕ → Q' → Q' → Fˣ → Prop)
    (hw : ∀ k, 0 < k → ∀ (x x' : Q') (c : Fin j → Fˣ), (∀ i, w k (φ x i) (φ x' i) (c i)) → w' k x x' (∏ i, c i))
    (I : TateIso Dw F Q act w) : Nonempty (TateIso Dw' F Q' act' w') := by
  refine ⟨{ ζ := I.ζ, ζ_prim := I.ζ_prim, ζ_pow := I.ζ_pow
            ev := fun n a => φ.symm (fun i => I.ev n (e a i))
            add := ?_, lin := ?_, ker := ?_, onto := ?_, tower := ?_, isom := ?_ }⟩
  · intro n a b
    rw [← map_mul]
    congr 1
    funext i
    simp [I.add]
  · intro n c a
    apply φ.injective
    funext i
    simp [hact, I.lin]
  · intro n hn a
    rw [MulEquiv.map_eq_one_iff, funext_iff]
    simp only [Pi.one_apply, I.ker n hn]
    constructor
    · intro h
      choose b hb using h
      refine ⟨e.symm b, e.injective ?_⟩
      funext i
      simp [hb i]
    · rintro ⟨b, rfl⟩ i
      exact ⟨e b i, by simp⟩
  · intro n hn x
    rw [← φ.map_eq_one_iff, map_pow, funext_iff]
    simp only [Pi.pow_apply, Pi.one_apply, I.onto n hn]
    constructor
    · intro h
      choose b hb using h
      refine ⟨e.symm b, φ.injective ?_⟩
      funext i
      simp [hb i]
    · rintro ⟨a, rfl⟩ i
      exact ⟨e a i, by simp⟩
  · intro n m hn hm a
    rw [← map_pow]
    congr 1
    funext i
    simp [I.tower n m hn hm]
  · intro n hn a b
    have hz : I.ζ n ^ Dw'.EF a b = ∏ i, I.ζ n ^ Dw.EF (e a i) (e b i) := by
      rw [he]
      exact map_prod (zpowersHom Fˣ (I.ζ n)) (fun i => Multiplicative.ofAdd (Dw.EF (e a i) (e b i))) Finset.univ
    rw [hz]
    apply hw n hn
    intro i
    simpa using I.isom n hn (e a i) (e b i)

/- English proof (translation)
Set `f : (T ⟶ G') →* (Fin j → (T ⟶ G))` to `MonoidHom.mk' (fun x i => x ≫ p.pr i) (by`. Introduce `x y`. Use function extensionality and compare the values at `i`. Use `p.hom i` as an intermediate fact. Conclude with `MonObj.mul_comp x y (p.pr i))`.

Establish `hf : Function.Bijective f`. Prove the components needed by the constructor for the conclusion. Introduce `x y h`. Apply `p.lim.hom_ext` to reduce the goal to its premises. Introduce and unpack `⟨i⟩`.

Conclude with `congrFun h i`. Introduce `y`. Use `⟨p.lim.lift (Fan.mk T y), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Conclude with `p.lim.fac (Fan.mk T y) ⟨i⟩`.

Conclude with `⟨MulEquiv.ofBijective f hf, fun _ _ => rfl⟩`.
-/
theorem exists_mulEquiv_points_of_isPowGrp {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ}
    (p : IsPowGrp G' G j) (T : Over S) :
    ∃ φ : (T ⟶ G') ≃* (Fin j → (T ⟶ G)), ∀ x i, φ x i = x ≫ p.pr i := by
  let f : (T ⟶ G') →* (Fin j → (T ⟶ G)) := MonoidHom.mk' (fun x i => x ≫ p.pr i) (by
    intro x y
    funext i
    have := p.hom i
    exact MonObj.mul_comp x y (p.pr i))
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply p.lim.hom_ext
      rintro ⟨i⟩
      exact congrFun h i
    · intro y
      refine ⟨p.lim.lift (Fan.mk T y), ?_⟩
      funext i
      exact p.lim.fac (Fan.mk T y) ⟨i⟩
  exact ⟨MulEquiv.ofBijective f hf, fun _ _ => rfl⟩

/- English proof (translation)
Introduce `h1 h2 h4 htw E _ _ _ H R _ _ j A A' pA F _ _ act act' hact Dw I`. Take `⟨Dw', e, he, -, -⟩` from `GlobalTheory.T.hermitian_datum_direct_power E H Dw j`. Take `⟨φ, hφ⟩` from `exists_mulEquiv_points_of_isPowGrp pA.toIsPowGrp (TFK (R := R) F)`. Use `⟨Dw', nonempty_tateIso_of_mulEquiv_pi Dw Dw' j e he F _ _ φ _ _ ?_ _ _ ?_ I⟩` and prove the remaining obligations. Introduce `a x i`.

Simplify using `only [hφ, Category.assoc, hact]`. Introduce `k hk x x' c hc`. Simplify using `only [hφ] at hc`. Conclude with `GlobalTheory.T.weilPairing_powPolAV_eq_prod_field h1 h2 h4 htw R j A A' pA F k hk x x' c hc`.
-/
theorem exists_tateIso_of_isPowPolAV : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (pA : IsPowPolAV A' A j) (F : Type) [Field F] [Algebra (FractionRing R) F] (act : 𝓞 E → (A.A ⟶ A.A)) (act' : 𝓞 E → (A'.A ⟶ A'.A)), (∀ a i, act' a ≫ pA.pr i = pA.pr i ≫ act a) → ∀ (Dw : Datum H) (_I : TateIso Dw F (TFK (R := R) F ⟶ A.A) (fun a x => x ≫ act a) (fun k x x' z => WeilIs A.A A.L k x x' (unitOn z))), ∃ Dw' : Datum H, Nonempty (TateIso Dw' F (TFK (R := R) F ⟶ A'.A) (fun a x => x ≫ act' a) (fun k x x' z => WeilIs A'.A A'.L k x x' (unitOn z))) := by
  intro h1 h2 h4 htw E _ _ _ H R _ _ j A A' pA F _ _ act act' hact Dw I
  obtain ⟨Dw', e, he, -, -⟩ := GlobalTheory.T.hermitian_datum_direct_power E H Dw j
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_points_of_isPowGrp pA.toIsPowGrp (TFK (R := R) F)
  refine ⟨Dw', nonempty_tateIso_of_mulEquiv_pi Dw Dw' j e he F _ _ φ _ _ ?_ _ _ ?_ I⟩
  · intro a x i
    simp only [hφ, Category.assoc, hact]
  · intro k hk x x' c hc
    simp only [hφ] at hc
    exact GlobalTheory.T.weilPairing_powPolAV_eq_prod_field h1 h2 h4 htw R j A A' pA F k hk x x' c hc

end GlobalTheory
