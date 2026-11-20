import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU

def InK {S : Scheme.{0}} (B : Over S) [GrpObj B] (L : LB B.left) {T : Over S} (x : T ⟶ B) : Prop :=
  ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ c : LB.Gen ((translDiff B L x).pull ((fst T B).left ⁻¹ᵁ V).ι), c.IsGen

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] {L : LB B.left} {T T' : Over S}

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem inK_iff_memKL (x : T ⟶ B) : InK B L x ↔ MemKL B L x := Iff.rfl

/- English proof (translation)
The claim follows from `KerPow.locGen_iff _ _ _`.
-/
theorem inK_iff_locGen (x : T ⟶ B) : InK B L x ↔
    KerPow.LocGen L (K := Fin 2) (fst T B).left ![(translPt B x).left, (snd T B).left] ![1, -1] :=
  KerPow.locGen_iff _ _ _

variable (B L) in

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem kTriv_iff_inK : KTriv B L ↔
    ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ S) (x : Over.mk t ⟶ B),
      InK B L x → x = toUnit _ ≫ η[B] :=
  Iff.rfl

/- English proof (translation)
The claim follows from `memKL_one hL T`.
-/
theorem inK_one (hL : L.IsLB) (T : Over S) : InK B L (1 : T ⟶ B) := memKL_one hL T

/- English proof (translation)
The claim follows from `MemKL.comp hx u`.
-/
theorem InK.comp {x : T ⟶ B} (hx : InK B L x) (u : T' ⟶ T) : InK B L (u ≫ x) := MemKL.comp hx u

/- English proof (translation)
Set `τ : T ⊗ B ⟶ T ⊗ B` to `lift (fst T B) (translPt B y)`. Establish `k₁ : τ ≫ fst T B = fst T B` using `lift_fst _ _`. Establish `k₂ : τ ≫ snd T B = translPt B y` using `lift_snd _ _`. Establish `k₃ : τ ≫ translPt B x = translPt B (x * y)`. Express the relevant statement in the definitionally equal form `τ ≫ ((fst T B ≫ x) * snd T B) = (fst T B ≫ (x * y)) * snd T B`.

Rewrite using `[MonObj.comp_mul, k₂, ← Category.assoc, k₁, MonObj.comp_mul, _root_.mul_assoc]`. Both sides reduce to the same expression. Use `((inK_iff_locGen x).1 hx).baseChange τ.left (𝟙 _) ((congrArg (fun q => q.left) k₁).trans (Category.comp_id _).symm) fun k => ?_` and prove the remaining obligations. Use `fin_cases k`. Use `exacts [congrArg (fun q => q.left) k₃, congrArg (fun q => q.left) k₂]`.
-/
theorem InK.translate {x : T ⟶ B} (hx : InK B L x) (y : T ⟶ B) :
    KerPow.LocGen L (K := Fin 2) (fst T B).left ![(translPt B (x * y)).left, (translPt B y).left] ![1, -1] := by
  let τ : T ⊗ B ⟶ T ⊗ B := lift (fst T B) (translPt B y)
  have k₁ : τ ≫ fst T B = fst T B := lift_fst _ _
  have k₂ : τ ≫ snd T B = translPt B y := lift_snd _ _
  have k₃ : τ ≫ translPt B x = translPt B (x * y) := by
    change τ ≫ ((fst T B ≫ x) * snd T B) = (fst T B ≫ (x * y)) * snd T B
    rw [MonObj.comp_mul, k₂, ← Category.assoc, k₁, MonObj.comp_mul, _root_.mul_assoc]
    rfl
  refine ((inK_iff_locGen x).1 hx).baseChange τ.left (𝟙 _)
    ((congrArg (fun q => q.left) k₁).trans (Category.comp_id _).symm) fun k => ?_
  fin_cases k
  exacts [congrArg (fun q => q.left) k₃, congrArg (fun q => q.left) k₂]

/- English proof (translation)
Establish `triv : KerPow.LocGen L (K` using `Fin 0) (fst T B).left ![] ![] := KerPow.locGen_of_trivial hL fun U _ h => by simp`. Use `(inK_iff_locGen _).2 (triv.comb hL (hx.translate x⁻¹) fun U _ h => ?_)` and prove the remaining obligations. Rewrite using `[mul_inv_cancel, KerPow.translPt_one]`. Simplify using `[Fin.prod_univ_two]`.
-/
theorem InK.inv (hL : L.IsLB) {x : T ⟶ B} (hx : InK B L x) : InK B L x⁻¹ := by
  have triv : KerPow.LocGen L (K := Fin 0) (fst T B).left ![] ![] :=
    KerPow.locGen_of_trivial hL fun U _ h => by simp
  refine (inK_iff_locGen _).2 (triv.comb hL (hx.translate x⁻¹) fun U _ h => ?_)
  rw [mul_inv_cancel, KerPow.translPt_one]
  simp [Fin.prod_univ_two]

/- English proof (translation)
Establish `triv : KerPow.LocGen L (K` using `Fin 0) (fst T B).left ![] ![] := KerPow.locGen_of_trivial hL fun U _ h => by simp`. Establish `H` using `triv.comb hL ((inK_iff_locGen y).1 hy) (φ'' := ![(snd T B).left, (translPt B y).left]) (ε'' := ![1, -1]) fun U _ h => by simp [Fin.prod_univ_two]`. Use `(inK_iff_locGen _).2 ((hx.translate y).comb hL H fun U _ h => ?_)` and prove the remaining obligations. Simplify using `[Fin.prod_univ_two]`.
-/
theorem InK.mul (hL : L.IsLB) {x y : T ⟶ B} (hx : InK B L x) (hy : InK B L y) : InK B L (x * y) := by
  have triv : KerPow.LocGen L (K := Fin 0) (fst T B).left ![] ![] :=
    KerPow.locGen_of_trivial hL fun U _ h => by simp
  have H := triv.comb hL ((inK_iff_locGen y).1 hy) (φ'' := ![(snd T B).left, (translPt B y).left]) (ε'' := ![1, -1])
    fun U _ h => by simp [Fin.prod_univ_two]
  refine (inK_iff_locGen _).2 ((hx.translate y).comb hL H fun U _ h => ?_)
  simp [Fin.prod_univ_two]

variable (B) in

def kSubgroup (hL : L.IsLB) (T : Over S) : Subgroup (T ⟶ B) where
  carrier := {x | InK B L x}
  one_mem' := inK_one hL T
  mul_mem' := fun hx hy => InK.mul hL hx hy
  inv_mem' := fun hx => InK.inv hL hx

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
@[simp] theorem mem_kSubgroup (hL : L.IsLB) {x : T ⟶ B} : x ∈ kSubgroup B hL T ↔ InK B L x := Iff.rfl

/- English proof (translation)
The claim follows from `KerPow.eq_one_of_locGen hK x ((inK_iff_locGen x).1 hx)`.
-/
theorem InK.eq_one (hK : KTriv B L) {x : T ⟶ B} (hx : InK B L x) : x = 1 :=
  KerPow.eq_one_of_locGen hK x ((inK_iff_locGen x).1 hx)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun hK _ _ hx => hx.eq_one hK, fun h _ _ _ x hx => h _ x hx⟩`.
-/
theorem kTriv_iff_forall : KTriv B L ↔ ∀ (T : Over S) (x : T ⟶ B), InK B L x → x = 1 :=
  ⟨fun hK _ _ hx => hx.eq_one hK, fun h _ _ _ x hx => h _ x hx⟩

/- English proof (translation)
The claim follows from `memKL_of_push h hL hL' hw x hx`.
-/
theorem inK_of_push {S' : Scheme.{0}} {f : S' ⟶ S} {B' : Over S'} [GrpObj B'] {φ : B'.left ⟶ B.left}
    {L' : LB B'.left} (h : IsGrpPullback B' B f φ) (hL : L.IsLB) (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ))
    {Z : Over S'} (x : Z ⟶ B') (hx : InK B L (pushPt h.1.w x)) : InK B' L' x :=
  memKL_of_push h hL hL' hw x hx

variable (B) in

/- English proof (translation)
Introduce `p`. Use `⟨⊤, trivial, ?_⟩` and prove the remaining obligations. Use `gen_chartPull (chartPullPull _ _ _ rfl) (⟨fun _ => 1⟩ : LB.Gen (translDiff B (Inh.trivLB B.left) x)) ?_` and prove the remaining obligations. Introduce `i j`. Conclude with `(map_one _).trans ((congrArg₂ (· * ·) (Inh.linComb_triv_g _ _ i j) (map_one _)).trans (_root_.one_mul _)).symm`.
-/
theorem inK_triv (x : T ⟶ B) : InK B (Inh.trivLB B.left) x := by
  intro p
  refine ⟨⊤, trivial, ?_⟩
  refine gen_chartPull (chartPullPull _ _ _ rfl)
    (⟨fun _ => 1⟩ : LB.Gen (translDiff B (Inh.trivLB B.left) x)) ?_
  intro i j
  exact (map_one _).trans
    ((congrArg₂ (· * ·) (Inh.linComb_triv_g _ _ i j) (map_one _)).trans (_root_.one_mul _)).symm

/- English proof (translation)
The claim follows from `eq_top_iff.2 fun x _ => inK_triv B x`.
-/
example (T : Over S) : kSubgroup B (Inh.trivLB_isLB B.left) T = ⊤ :=
  eq_top_iff.2 fun x _ => inK_triv B x

/- English proof (translation)
The claim follows from `(Subgroup.eq_bot_iff_forall _).2 fun _ hx => InK.eq_one P.ktriv hx`.
-/
example (P : PolAV S) (T : Over S) : kSubgroup P.A P.isLB T = ⊥ :=
  (Subgroup.eq_bot_iff_forall _).2 fun _ hx => InK.eq_one P.ktriv hx

/- English proof (translation)
Introduce `h` and use `hx (h.eq_one P.ktriv)`.
-/
example (P : PolAV S) (x : T ⟶ P.A) (hx : x ≠ 1) : ¬ InK P.A P.L x := fun h => hx (h.eq_one P.ktriv)

end GlobalTheory.UU
end
