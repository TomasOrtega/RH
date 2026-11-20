import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsHTLatOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsKitWithKitWith
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
import Formalism.LocalToGlobal.ProjectiveLattices.RecCond
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankLineHyperplane
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlgOfFlagClSpec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniqueIntegralLiftNormPInverse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCharExtendsDivisibleLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootsOfUnityAndPValuation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TanEvBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TanEvLinearCombination
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueTangentOfValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelReductionHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilCharSurjectiveAndMapRangeAl
open CategoryTheory AlgebraicGeometry NumberField MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharWeil

/- English proof (translation)
Take `⟨b, hb⟩` from `IsAlgClosed.exists_pow_nat_eq (a : C) (Nat.pos_of_ne_zero hn)`. Establish `hb0 : b ≠ 0`. Introduce and unpack `rfl`. Rewrite `hb` using `[zero_pow hn]`. Conclude with `a.ne_zero hb.symm`.

Conclude with `⟨Units.mk0 b hb0, Units.ext (by simpa using hb)⟩`.
-/
theorem units_root {C : Type} [Field C] [IsAlgClosed C] (n : ℕ) (hn : n ≠ 0) (a : Cˣ) :
    ∃ b : Cˣ, b ^ n = a := by
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (a : C) (Nat.pos_of_ne_zero hn)
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at hb
    exact a.ne_zero hb.symm
  exact ⟨Units.mk0 b hb0, Units.ext (by simpa using hb)⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

/- English proof (translation)
Take `⟨j, hj, hgen⟩` from `P.exists_generic`. Establish `hsq : ∀ Q : Pdiv.specO O O ⟶ P.G, (Q.left ≫ φ) ≫ t.G.hom = (Over.mk (spMap (algebraMap O O) ≫ z)).hom` using `fun Q => by`. Rewrite using `[Category.assoc, hφ.1.w, ← Category.assoc, Over.w Q]`. Both sides reduce to the same expression. Set `ψ : (Pdiv.specO O O ⟶ P.G) →* (Over.mk (spMap (algebraMap O O) ≫ z) ⟶ t.G)` to `MonoidHom.mk' (fun Q => Over.homMk (Q.left ≫ φ) (hsq Q)) fun Q Q' => by ext1`.

Conclude with `(hφ.2 (Pdiv.specO O O) Q Q' (Over.homMk (Q.left ≫ φ) (hsq Q)) (Over.homMk (Q'.left ≫ φ) (hsq Q')) rfl rfl).symm`. Establish `hψ : ∀ Q, (ψ Q).left = Q.left ≫ φ` using `fun Q => rfl`. Establish `hid : spMap (algebraMap O O) = 𝟙 _` using `Spec.map_id _`. Establish `hlift : ∀ w : Over.mk (spMap (algebraMap O O) ≫ z) ⟶ t.G, ∃ Q, ψ Q = w` using `fun w => by`. Use `⟨Over.homMk (hφ.1.lift w.left (spMap (algebraMap O O)) (Over.w w)) (hφ.1.lift_snd _ _ _), ?_⟩` and prove the remaining obligations.

Use `ext1`. Conclude with `hφ.1.lift_fst _ _ _`. Establish `hinj : Function.Injective ψ` using `fun Q Q' h => by ext1`. Use `hφ.1.hom_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[← hψ, ← hψ, h]`.

Rewrite using `[Over.w Q, Over.w Q']`. Set `T : Subgroup (Pdiv.specO O O ⟶ P.G)` to `(powMonoidHom (p ^ n)).ker`. Set `f : T →* Cˣ` to `MonoidHom.mk' (fun Q => Units.map (algebraMap O C : O →* C) (c.χ O (ψ Q))) fun Q Q' => by`. Establish `hQ : (ψ Q) ^ (p ^ n) = 1` using `by rw [← map_pow]; exact (congrArg ψ Q.2).trans (map_one ψ)`. Establish `hQ' : (ψ Q') ^ (p ^ n) = 1` using `by rw [← map_pow]; exact (congrArg ψ Q'.2).trans (map_one ψ)`.

Rewrite using `[Subgroup.coe_mul, map_mul, c.mul O _ _ hQ hQ', map_mul]`. Use `letI : DivisibleBy (Additive Cˣ) ℕ := divisibleByOfSMulRightSurj (Additive Cˣ) ℕ fun {m} hm a => by`. Take `⟨b, hb⟩` from `units_root m hm a.toMul`. Conclude with `⟨Additive.ofMul b, congrArg Additive.ofMul hb⟩`. Use `letI : DivisibleBy (Additive Cˣ) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _`.

Take `⟨k, hk⟩` from `(Module.Baer.of_divisible (Additive Cˣ)).extension_property_addMonoidHom (MonoidHom.toAdditive (j.comp T.subtype)) (fun a b h => Subtype.ext (hj h)) (MonoidHom.toAdditive f)`. Set `κ : GlobalTheory.ChTor.Pts P.A.A →* Cˣ` to `MonoidHom.toAdditive.symm k`. Establish `hκ : ∀ Q : T, κ (j Q) = f Q` using `fun Q => DFunLike.congr_fun hk (Additive.ofMul Q)`. Establish `hk1 : 1 ≤ p ^ n` using `Nat.one_le_pow _ _ (Fact.out : p.Prime).pos`. Take `⟨s₀, ⟨hs₀, hs⟩, -⟩` from `GlobalTheory.HTLat.weil_perfect hk1 κ fun a b _ _ => map_mul κ a b`.

Take `⟨s, hsl⟩` from `(GlobalTheory.tate_free_of_card p (GlobalTheory.ChTor.Pts P.A.A) _ P.card_torsion).2.1 n s₀ hs₀`. Use `⟨s, fun w a hw ha => ?_⟩` and prove the remaining obligations. Take `⟨Q, rfl⟩` from `hlift w`. Establish `hQ : Q ^ (p ^ n) = 1` using `hinj (by rw [map_pow, hw, map_one])`. Establish `haQ : a = j Q`.

Use `(hgen Q a).1 (hφ.1.hom_ext ?_ ?_)` and prove the remaining obligations. Rewrite using `[Category.assoc, ha, Category.assoc]`. Both sides reduce to the same expression. Simplify using `only [Category.assoc]`. Rewrite using `[Over.w Q, P.gen_pull.1.w, ← Category.assoc, Over.w a]`.

Express the relevant statement in the definitionally equal form `𝟙 _ ≫ _ = _ ≫ spMap (algebraMap O O)`. Rewrite using `[hid, Category.id_comp, Category.comp_id]`. Establish `ha1 : a ^ (p ^ n) = 1` using `by rw [haQ, ← map_pow, hQ, map_one]`. Rewrite using `[hsl, hs a ha1, haQ]`. Conclude with `(congrArg Units.val (hκ ⟨Q, hQ⟩)).symm`.
-/
theorem exists_tate_gen {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
    {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ]
    (P : GlobalTheory.HTLat.Point p v O Λ) (z : Sp O ⟶ X) (φ : P.G.left ⟶ t.G.left)
    (hφ : IsGrpPullback P.G t.G z φ) (n : ℕ) (c : TorsChar t z (p ^ n)) :
    ∃ s : P.T, ∀ (w : Over.mk (spMap (algebraMap O O) ≫ z) ⟶ t.G) (a : GlobalTheory.ChTor.Pts P.A.A),
      w ^ (p ^ n) = 1 → a.left ≫ P.gen ≫ φ = spMap (algebraMap O C) ≫ w.left →
      algebraMap O C (c.χ O w : O) = (GlobalTheory.HTLat.weil P.A (p ^ n) a (s.lev n) : C) := by
  classical
  obtain ⟨j, hj, hgen⟩ := P.exists_generic
  have hsq : ∀ Q : Pdiv.specO O O ⟶ P.G,
      (Q.left ≫ φ) ≫ t.G.hom = (Over.mk (spMap (algebraMap O O) ≫ z)).hom := fun Q => by
    rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w Q]
    rfl
  let ψ : (Pdiv.specO O O ⟶ P.G) →* (Over.mk (spMap (algebraMap O O) ≫ z) ⟶ t.G) :=
    MonoidHom.mk' (fun Q => Over.homMk (Q.left ≫ φ) (hsq Q)) fun Q Q' => by
      ext1
      exact (hφ.2 (Pdiv.specO O O) Q Q' (Over.homMk (Q.left ≫ φ) (hsq Q))
        (Over.homMk (Q'.left ≫ φ) (hsq Q')) rfl rfl).symm
  have hψ : ∀ Q, (ψ Q).left = Q.left ≫ φ := fun Q => rfl
  have hid : spMap (algebraMap O O) = 𝟙 _ := Spec.map_id _

  have hlift : ∀ w : Over.mk (spMap (algebraMap O O) ≫ z) ⟶ t.G, ∃ Q, ψ Q = w := fun w => by
    refine ⟨Over.homMk (hφ.1.lift w.left (spMap (algebraMap O O)) (Over.w w)) (hφ.1.lift_snd _ _ _), ?_⟩
    ext1
    exact hφ.1.lift_fst _ _ _
  have hinj : Function.Injective ψ := fun Q Q' h => by
    ext1
    refine hφ.1.hom_ext ?_ ?_
    · rw [← hψ, ← hψ, h]
    · rw [Over.w Q, Over.w Q']
  let T : Subgroup (Pdiv.specO O O ⟶ P.G) := (powMonoidHom (p ^ n)).ker
  let f : T →* Cˣ := MonoidHom.mk' (fun Q => Units.map (algebraMap O C : O →* C) (c.χ O (ψ Q))) fun Q Q' => by
    have hQ : (ψ Q) ^ (p ^ n) = 1 := by rw [← map_pow]; exact (congrArg ψ Q.2).trans (map_one ψ)
    have hQ' : (ψ Q') ^ (p ^ n) = 1 := by rw [← map_pow]; exact (congrArg ψ Q'.2).trans (map_one ψ)
    rw [Subgroup.coe_mul, map_mul, c.mul O _ _ hQ hQ', map_mul]
  letI : DivisibleBy (Additive Cˣ) ℕ := divisibleByOfSMulRightSurj (Additive Cˣ) ℕ fun {m} hm a => by
    obtain ⟨b, hb⟩ := units_root m hm a.toMul
    exact ⟨Additive.ofMul b, congrArg Additive.ofMul hb⟩
  letI : DivisibleBy (Additive Cˣ) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  obtain ⟨k, hk⟩ := (Module.Baer.of_divisible (Additive Cˣ)).extension_property_addMonoidHom
    (MonoidHom.toAdditive (j.comp T.subtype)) (fun a b h => Subtype.ext (hj h)) (MonoidHom.toAdditive f)
  let κ : GlobalTheory.ChTor.Pts P.A.A →* Cˣ := MonoidHom.toAdditive.symm k
  have hκ : ∀ Q : T, κ (j Q) = f Q := fun Q => DFunLike.congr_fun hk (Additive.ofMul Q)
  have hk1 : 1 ≤ p ^ n := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  obtain ⟨s₀, ⟨hs₀, hs⟩, -⟩ := GlobalTheory.HTLat.weil_perfect hk1 κ fun a b _ _ => map_mul κ a b
  obtain ⟨s, hsl⟩ := (GlobalTheory.tate_free_of_card p (GlobalTheory.ChTor.Pts P.A.A) _ P.card_torsion).2.1 n s₀ hs₀
  refine ⟨s, fun w a hw ha => ?_⟩
  obtain ⟨Q, rfl⟩ := hlift w
  have hQ : Q ^ (p ^ n) = 1 := hinj (by rw [map_pow, hw, map_one])
  have haQ : a = j Q := by
    refine (hgen Q a).1 (hφ.1.hom_ext ?_ ?_)
    · rw [Category.assoc, ha, Category.assoc]
      rfl
    · simp only [Category.assoc]
      rw [Over.w Q, P.gen_pull.1.w, ← Category.assoc, Over.w a]
      change 𝟙 _ ≫ _ = _ ≫ spMap (algebraMap O O)
      rw [hid, Category.id_comp, Category.comp_id]
  have ha1 : a ^ (p ^ n) = 1 := by rw [haQ, ← map_pow, hQ, map_one]
  rw [hsl, hs a ha1, haQ]
  exact (congrArg Units.val (hκ ⟨Q, hQ⟩)).symm

end GlobalTheory.CharWeil
