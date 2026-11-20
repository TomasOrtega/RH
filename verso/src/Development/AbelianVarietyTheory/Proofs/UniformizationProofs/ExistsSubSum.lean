import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Definitions.Uniformization.SvalTwistOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfSumMulCoord
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.StalkMapInjectiveOfFlat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsProdB

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.ConvOfProd

/- English proof (translation)
Rewrite using `[Finset.sum_comm, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun β hβ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum]`. Use `congr 1`. Use `symm`.

Use `Finset.sum_bij_ne_zero (fun v _ _ => β + v) (fun v h _ => hS β hβ v h) (fun a _ _ b _ _ e => add_left_cancel e) (fun α _ h => ?_) (fun v _ _ => by rw [add_sub_cancel_left])` and prove the remaining obligations. Conclude with `⟨α - β, by by_contra hn; exact h (hG _ hn), h, add_sub_cancel β α⟩`.
-/
theorem sum_conv {X A : Type} [AddCommGroup X] [CommRing A] (s s' S : Finset X) (F G : X → A)
    (hG : ∀ v ∉ s', G v = 0) (hS : ∀ β ∈ s, ∀ v ∈ s', β + v ∈ S) :
    ∑ α ∈ S, ∑ β ∈ s, F β * G (α - β) = (∑ β ∈ s, F β) * ∑ v ∈ s', G v := by
  classical
  rw [Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun β hβ => ?_
  rw [← Finset.mul_sum]
  congr 1
  symm
  refine Finset.sum_bij_ne_zero (fun v _ _ => β + v) (fun v h _ => hS β hβ v h)
    (fun a _ _ b _ _ e => add_left_cancel e) (fun α _ h => ?_) (fun v _ _ => by rw [add_sub_cancel_left])
  exact ⟨α - β, by by_contra hn; exact h (hG _ hn), h, add_sub_cancel β α⟩

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨S, fun Z r z J _ => by rw [Finset.sum_empty, sub_zero]⟩`. Consider the case `insert i s hi ih`. Take `⟨d, hd⟩` from `ih`. Use `⟨DVR.SecOps.secAdd d (DVR.SecOps.secNeg (p i)), fun Z r z J hJ => ?_⟩` and prove the remaining obligations.

Establish `hm` using `hJ.mem φ r`. Establish `e : sval (DVR.SecOps.secAdd d (DVR.SecOps.secNeg (p i))) r z J = sval d r z J - sval (p i) r z J`. Use `(gs_add r z _ hm _ _).trans ?_` and prove the remaining obligations. Rewrite using `[sub_eq_add_neg]`. Use `congr 1`.

Use `(gs_eq r z _ hm _).trans (Eq.trans ?_ (congrArg Neg.neg (gs_eq r z _ hm _)).symm)` and prove the remaining obligations. Conclude with `(congrArg _ (map_neg _ _)).trans (map_neg _ _)`. Rewrite using `[e, hd Z r z J hJ, Finset.sum_insert hi]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_sub_sum {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {Ix : Type}
    (S : LB.Sec (LB.LinComb L φ ε)) (p : Ix → LB.Sec (LB.LinComb L φ ε)) (s : Finset Ix) :
    ∃ d : LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      sval d r z J = sval S r z J - ∑ i ∈ s, sval (p i) r z J := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨S, fun Z r z J _ => by rw [Finset.sum_empty, sub_zero]⟩
  | insert i s hi ih =>
    obtain ⟨d, hd⟩ := ih
    refine ⟨DVR.SecOps.secAdd d (DVR.SecOps.secNeg (p i)), fun Z r z J hJ => ?_⟩
    have hm := hJ.mem φ r
    have e : sval (DVR.SecOps.secAdd d (DVR.SecOps.secNeg (p i))) r z J = sval d r z J - sval (p i) r z J := by
      refine (gs_add r z _ hm _ _).trans ?_
      rw [sub_eq_add_neg]
      congr 1
      refine (gs_eq r z _ hm _).trans (Eq.trans ?_ (congrArg Neg.neg (gs_eq r z _ hm _)).symm)
      exact (congrArg _ (map_neg _ _)).trans (map_neg _ _)
    rw [e, hd Z r z J hJ, Finset.sum_insert hi]
    ring

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

/- English proof (translation)
Rewrite using `[← Over.w g.pG, ← Over.w (snd T D.P.A), ← Category.assoc, ← Category.assoc]`. Conclude with `congrArg (· ≫ D.P.A.hom) hr.symm`.
-/
theorem over_eq {e : ℕ} (g : GtCoord I D e G) {T : Over (Spec (CommRingCat.of R))} {Z : Scheme.{0}}
    (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ (T ⊗ D.P.A).left) (hr : r ≫ (snd T D.P.A).left = x ≫ g.pG.left) :
    x ≫ ((Over.map (thick R I e)).obj (thickObj R I e G)).hom = r ≫ (T ⊗ D.P.A).hom := by
  rw [← Over.w g.pG, ← Over.w (snd T D.P.A), ← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ D.P.A.hom) hr.symm

/- English proof (translation)
Substitute `hα` using the available equality. Set `FinalForm : Over (Spec (CommRingCat.of R))` to `Over.mk (r ≫ (T ⊗ D.P.A).hom)`. Set `ro : FinalForm ⟶ T ⊗ D.P.A` to `Over.homMk r rfl`. Set `xo : FinalForm ⟶ (Over.map (thick R I e)).obj (thickObj R I e G)` to `Over.homMk x (over_eq g x r hr)`. Establish `h₁` using `H FinalForm ro z J hJ`.

Establish `h₂` using `(val_mul hJ _ _ _).symm.trans ((val_corr hJ (g.t_mul β ga) x).trans (val_mul hJ _ _ _))`. Establish `h₃` using `val_cub D.cub xo (z := z) hJ (DVR.cP D _ β) (DVR.cP D _ ga) g.pG`. Establish `h₄ : xo ≫ g.pG = ro ≫ snd T D.P.A` using `Over.OverMorphism.ext hr.symm`. Rewrite `h₃` using `[DVR.comp_cP, DVR.comp_cP, h₄]`. Establish `h₅` using `congrArg Units.val ((congrArg (val (g.t (β + ga)) x z J * ·) h₃).symm.trans h₂)`.

Rewrite `h₅` using `[Units.val_mul, Units.val_mul]`. Use `(congrArg (· * (val (g.t (β + ga)) x z J).val) h₁).trans ?_` and prove the remaining obligations. Rewrite using `[_root_.mul_mul_mul_comm, ← h₅]`. Conclude with `(_root_.mul_assoc _ _ _).trans (congrArg _ (mul_comm _ _))`.
-/
theorem prod_mul_coord {e : ℕ} (g : GtCoord I D e G) {T : Over (Spec (CommRingCat.of R))} {k l m : ℕ} {β ga α : D.X}
    (hα : β + ga = α) {a : SecBT D T k β} {b : SecBT D T l ga} {c : SecBT D T m α} (H : IsProdB a b c) {Z : Scheme.{0}}
    (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ (T ⊗ D.P.A).left) (hr : r ≫ (snd T D.P.A).left = x ≫ g.pG.left)
    (z : Z) (J) (hJ : Good D.P.L z J) :
    sval c r z J * (val (g.t α) x z J).val =
      sval a r z J * (val (g.t β) x z J).val * (sval b r z J * (val (g.t ga) x z J).val) := by
  subst hα
  let FinalForm : Over (Spec (CommRingCat.of R)) := Over.mk (r ≫ (T ⊗ D.P.A).hom)
  let ro : FinalForm ⟶ T ⊗ D.P.A := Over.homMk r rfl
  let xo : FinalForm ⟶ (Over.map (thick R I e)).obj (thickObj R I e G) := Over.homMk x (over_eq g x r hr)
  have h₁ := H FinalForm ro z J hJ
  have h₂ := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (g.t_mul β ga) x).trans (val_mul hJ _ _ _))
  have h₃ := val_cub D.cub xo (z := z) hJ (DVR.cP D _ β) (DVR.cP D _ ga) g.pG
  have h₄ : xo ≫ g.pG = ro ≫ snd T D.P.A := Over.OverMorphism.ext hr.symm
  rw [DVR.comp_cP, DVR.comp_cP, h₄] at h₃
  have h₅ := congrArg Units.val ((congrArg (val (g.t (β + ga)) x z J * ·) h₃).symm.trans h₂)
  rw [Units.val_mul, Units.val_mul] at h₅
  refine (congrArg (· * (val (g.t (β + ga)) x z J).val) h₁).trans ?_
  rw [_root_.mul_mul_mul_comm, ← h₅]
  exact (_root_.mul_assoc _ _ _).trans (congrArg _ (mul_comm _ _))

/- English proof (translation)
Introduce `R _ _ I D A G _ _ U T k l f g h σ hP hE α₀`. Use `choose p hp using fun α β => exists_isProdB R D T k l β (α - β) α (add_sub_cancel β α) (f β) (g (α - β))`. Use `⟨p α₀, hp α₀, fun e => ?_⟩` and prove the remaining obligations. Take `⟨s, s', hP⟩` from `hP e`. Take `⟨s'', hE⟩` from `hE e`.

Establish `key : ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ (T ⊗ D.P.A).left), r ≫ (snd T D.P.A).left = x ≫ (U.gt e).pG.left → ∀ (z : Z) (J), Good D.P.L z J → (∀ α ∉ s, sval (f α) r z J = 0) ∧ (∀ α ∉ s', sval (g α) r z J = 0) ∧ (∀ α ∉ s'', sval (h α) r z J = 0) ∧ ∑ α ∈ s' …`. Introduce `Z x r hr z J hJ`. Set `FinalForm : Over (Spec (CommRingCat.of R))` to `Over.mk (r ≫ (T ⊗ D.P.A).hom)`. Set `ro : FinalForm ⟶ T ⊗ D.P.A` to `Over.homMk r rfl`. Set `xo : FinalForm ⟶ (Over.map (thick R I e)).obj (thickObj R I e G)` to `Over.homMk x (over_eq (U.gt e) x r hr)`.

Set `rG : FinalForm ⟶ T ⊗ G` to `lift (ro ≫ fst _ _) (xo ≫ fstG I e G)`. Establish `e₁ : rG.left ≫ (snd T G).left = x ≫ (fstG I e G).left` using `congrArg (fun q : FinalForm ⟶ G => q.left) (lift_snd _ _)`. Establish `e₂ : r ≫ (fst T D.P.A).left = rG.left ≫ (fst T G).left` using `congrArg (fun q : FinalForm ⟶ T => q.left) (lift_fst (ro ≫ fst _ _) (xo ≫ fstG I e G)).symm`. Use `choose JG hJG using fun χ : Z ⟶ G.left => exists_chart U.P.L.isLB (χ z)`. Take `⟨a₁, a₂, a₃⟩` from `hP Z x rG.left r e₁ hr e₂ z JG J hJG hJ`.

Take `⟨b₁, b₂⟩` from `hE Z x rG.left r e₁ hr e₂ z JG J hJG hJ`. Conclude with `⟨a₁, a₂, b₁, b₂.symm.trans a₃⟩`. Use `choose d hd using fun α => exists_sub_sum (h α) (p α) s`. Set `S : Finset D.X` to `insert α₀ (s'' ∪ Finset.image₂ (· + ·) s s')`. Establish `hd0` using `GlobalTheory.sval_eq_zero_of_sum_mul_coord R I D e G (U.gt e) (T ⊗ D.P.A) (snd T D.P.A) (Fin 4) (famφT D T) (DegPre.famε (k + l)) d S (fun Z x r hr z J hJ => by`.

Take `⟨-, k₂, k₃, k₄⟩` from `key Z x r hr z J hJ`. Establish `c` using `sum_conv s s' S (fun β => sval (f β) r z J * (val ((U.gt e).t β) x z J).val) (fun β => sval (g β) r z J * (val ((U.gt e).t β) x z J).val) (fun v hv => by rw [k₂ v hv, zero_mul]) (fun β hβ v hv => Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image₂_of_mem hβ hv)) …`. Establish `c' : ∑ α ∈ s'', sval (h α) r z J * (val ((U.gt e).t α) x z J).val = ∑ α ∈ S, sval (h α) r z J * (val ((U.gt e).t α) x z J).val` using `Finset.sum_subset (fun a ha => Finset.mem_insert_of_mem (Finset.mem_union_left _ ha)) (fun a _ ha => by rw [k₃ a ha, zero_mul])`. Rewrite using `[← sub_eq_zero.2 (c'.symm.trans (k₄.trans c.symm)), ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations.

Rewrite using `[hd α Z r z J hJ, sub_mul, Finset.sum_mul]`. Conclude with `congrArg _ (Finset.sum_congr rfl fun β _ => prod_mul_coord (U.gt e) (add_sub_cancel β α) (hp α β) x r hr z J hJ)) α₀ (Finset.mem_insert_self _ _)`. Use `⟨s, fun Z r hl z J hJ => ⟨fun β hβ => ?_, ?_⟩⟩` and prove the remaining obligations. Use `GlobalTheory.LiftTest.main R I D e G (U.gt e) (T ⊗ D.P.A) (snd T D.P.A) _ D.P.L D.P.isLB _ _ _ (p α₀ β) (fun Z x r hr z J hJ => ?_) Z r hl z J hJ` and prove the remaining obligations. Establish `c` using `prod_mul_coord (U.gt e) (add_sub_cancel β α₀) (hp α₀ β) x r hr z J hJ`.

Rewrite `c` using `[(key Z x r hr z J hJ).1 β hβ, zero_mul, zero_mul]`. Conclude with `(Units.mul_left_eq_zero _).1 c`. Establish `c` using `GlobalTheory.LiftTest.main R I D e G (U.gt e) (T ⊗ D.P.A) (snd T D.P.A) _ D.P.L D.P.isLB _ _ _ (d α₀) hd0 Z r hl z J hJ`. Rewrite `c` using `[hd α₀ Z r z J hJ]`. Conclude with `sub_eq_zero.1 c`.
-/
theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (T : Over (Spec (CommRingCat.of R))) (k l : ℕ) (f : ∀ α, SecBT D T k α) (g : ∀ α, SecBT D T l α) (h : ∀ α, SecBT D T (k + l) α) (σ : U.SecGT T (k + l)), U.ProdExp T f g σ → U.ExpT T (k + l) σ h → ConvT I f g h := by
  intro R _ _ I D A G _ _ U T k l f g h σ hP hE α₀
  classical
  choose p hp using fun α β => exists_isProdB R D T k l β (α - β) α (add_sub_cancel β α) (f β) (g (α - β))
  refine ⟨p α₀, hp α₀, fun e => ?_⟩
  obtain ⟨s, s', hP⟩ := hP e
  obtain ⟨s'', hE⟩ := hE e
  have key : ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ (T ⊗ D.P.A).left),
      r ≫ (snd T D.P.A).left = x ≫ (U.gt e).pG.left → ∀ (z : Z) (J), Good D.P.L z J →
      (∀ α ∉ s, sval (f α) r z J = 0) ∧ (∀ α ∉ s', sval (g α) r z J = 0) ∧ (∀ α ∉ s'', sval (h α) r z J = 0) ∧
      ∑ α ∈ s'', sval (h α) r z J * (val ((U.gt e).t α) x z J).val =
        (∑ α ∈ s, sval (f α) r z J * (val ((U.gt e).t α) x z J).val) *
          ∑ α ∈ s', sval (g α) r z J * (val ((U.gt e).t α) x z J).val := by
    intro Z x r hr z J hJ
    let FinalForm : Over (Spec (CommRingCat.of R)) := Over.mk (r ≫ (T ⊗ D.P.A).hom)
    let ro : FinalForm ⟶ T ⊗ D.P.A := Over.homMk r rfl
    let xo : FinalForm ⟶ (Over.map (thick R I e)).obj (thickObj R I e G) := Over.homMk x (over_eq (U.gt e) x r hr)
    let rG : FinalForm ⟶ T ⊗ G := lift (ro ≫ fst _ _) (xo ≫ fstG I e G)
    have e₁ : rG.left ≫ (snd T G).left = x ≫ (fstG I e G).left := congrArg (fun q : FinalForm ⟶ G => q.left) (lift_snd _ _)
    have e₂ : r ≫ (fst T D.P.A).left = rG.left ≫ (fst T G).left :=
      congrArg (fun q : FinalForm ⟶ T => q.left) (lift_fst (ro ≫ fst _ _) (xo ≫ fstG I e G)).symm
    choose JG hJG using fun χ : Z ⟶ G.left => exists_chart U.P.L.isLB (χ z)
    obtain ⟨a₁, a₂, a₃⟩ := hP Z x rG.left r e₁ hr e₂ z JG J hJG hJ
    obtain ⟨b₁, b₂⟩ := hE Z x rG.left r e₁ hr e₂ z JG J hJG hJ
    exact ⟨a₁, a₂, b₁, b₂.symm.trans a₃⟩
  choose d hd using fun α => exists_sub_sum (h α) (p α) s
  let S : Finset D.X := insert α₀ (s'' ∪ Finset.image₂ (· + ·) s s')
  have hd0 := GlobalTheory.sval_eq_zero_of_sum_mul_coord R I D e G (U.gt e) (T ⊗ D.P.A) (snd T D.P.A) (Fin 4)
    (famφT D T) (DegPre.famε (k + l)) d S (fun Z x r hr z J hJ => by
      obtain ⟨-, k₂, k₃, k₄⟩ := key Z x r hr z J hJ
      have c := sum_conv s s' S (fun β => sval (f β) r z J * (val ((U.gt e).t β) x z J).val)
        (fun β => sval (g β) r z J * (val ((U.gt e).t β) x z J).val)
        (fun v hv => by rw [k₂ v hv, zero_mul])
        (fun β hβ v hv => Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image₂_of_mem hβ hv)))
      have c' : ∑ α ∈ s'', sval (h α) r z J * (val ((U.gt e).t α) x z J).val =
          ∑ α ∈ S, sval (h α) r z J * (val ((U.gt e).t α) x z J).val :=
        Finset.sum_subset (fun a ha => Finset.mem_insert_of_mem (Finset.mem_union_left _ ha))
          (fun a _ ha => by rw [k₃ a ha, zero_mul])
      rw [← sub_eq_zero.2 (c'.symm.trans (k₄.trans c.symm)), ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [hd α Z r z J hJ, sub_mul, Finset.sum_mul]
      exact congrArg _ (Finset.sum_congr rfl fun β _ =>
        prod_mul_coord (U.gt e) (add_sub_cancel β α) (hp α β) x r hr z J hJ)) α₀ (Finset.mem_insert_self _ _)
  refine ⟨s, fun Z r hl z J hJ => ⟨fun β hβ => ?_, ?_⟩⟩
  · refine GlobalTheory.LiftTest.main R I D e G (U.gt e) (T ⊗ D.P.A) (snd T D.P.A) _ D.P.L D.P.isLB _ _ _ (p α₀ β)
      (fun Z x r hr z J hJ => ?_) Z r hl z J hJ
    have c := prod_mul_coord (U.gt e) (add_sub_cancel β α₀) (hp α₀ β) x r hr z J hJ
    rw [(key Z x r hr z J hJ).1 β hβ, zero_mul, zero_mul] at c
    exact (Units.mul_left_eq_zero _).1 c
  · have c := GlobalTheory.LiftTest.main R I D e G (U.gt e) (T ⊗ D.P.A) (snd T D.P.A) _ D.P.L D.P.isLB _ _ _ (d α₀) hd0 Z r hl z J hJ
    rw [hd α₀ Z r z J hJ] at c
    exact sub_eq_zero.1 c

end GlobalTheory.ConvOfProd
