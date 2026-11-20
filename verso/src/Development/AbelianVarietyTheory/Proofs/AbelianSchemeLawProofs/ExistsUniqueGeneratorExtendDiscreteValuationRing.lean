import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.GenExtend

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DvrModel

/- English proof (translation)
Use `choose J hJ using fun χ : Z ⟶ X => exists_chart hL (χ z)`. Establish `hv` using `val_corr hJ hc (𝟙 Z)`. Rewrite `hv` using `[val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp]`. Rewrite using `[gen_trans ht r z ha (Good.mem hJ φ r), gen_trans ht' r' z ha' (Good.mem hJ φ' r')]`. Use `congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_) hv` and prove the remaining obligations.

Use `show gm (r ≫ φ k) z (L.U (a k) ⊓ L.U (J (r ≫ φ k))) (L.g (a k) (J (r ≫ φ k))) ^ _ = gm (r' ≫ φ' k) z (L.U (a k) ⊓ L.U (J (r' ≫ φ' k))) (L.g (a k) (J (r' ≫ φ' k))) ^ _`. Rewrite using `[h k]`.
-/
theorem gm_eq_of_corr {X Y Y' Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {I : Type} [Fintype I]
    {φ : I → (Y ⟶ X)} {φ' : I → (Y' ⟶ X)} {ε : I → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    {t' : LB.Gen (LB.LinComb L φ' ε)} (ht : t.IsGen) (ht' : t'.IsGen) (r : Z ⟶ Y) (r' : Z ⟶ Y')
    (h : ∀ i, r ≫ φ i = r' ≫ φ' i)
    (hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t r) (LB.pullGen L _ _ t' r')) (z : Z)
    (a : I → L.ι) (ha : r z ∈ LB.wchart L φ a) (ha' : r' z ∈ LB.wchart L φ' a) :
    gm r z (LB.wchart L φ a) (t.s a) = gm r' z (LB.wchart L φ' a) (t'.s a) := by
  choose J hJ using fun χ : Z ⟶ X => exists_chart hL (χ z)
  have hv := val_corr hJ hc (𝟙 Z)
  rw [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp] at hv
  rw [gen_trans ht r z ha (Good.mem hJ φ r), gen_trans ht' r' z ha' (Good.mem hJ φ' r')]
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_) hv
  show gm (r ≫ φ k) z (L.U (a k) ⊓ L.U (J (r ≫ φ k))) (L.g (a k) (J (r ≫ φ k))) ^ _ =
    gm (r' ≫ φ' k) z (L.U (a k) ⊓ L.U (J (r' ≫ φ' k))) (L.g (a k) (J (r' ≫ φ' k))) ^ _
  rw [h k]

/- English proof (translation)
Establish `hur : res hA' (pullU r' (LB.wchart L φ' a) (t'.s a)) = res hA (pullU r (LB.wchart L φ a) (t.s a))`. Use `unit_ext fun z hz => ?_` and prove the remaining obligations. Rewrite using `[gm_res _ z hA hz, gm_res _ z hA' hz, gm_pull _ r z _ (hA hz), gm_pull _ r' z _ (hA' hz), Category.id_comp, Category.id_comp]`. Conclude with `(gm_eq_of_corr hL ht ht' r r' h hc z a (hA hz) (hA' hz)).symm`. Conclude with `congrArg Units.val hur`.
-/
theorem res_pullU_eq_of_corr {X Y Y' Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {I : Type} [Fintype I]
    {φ : I → (Y ⟶ X)} {φ' : I → (Y' ⟶ X)} {ε : I → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    {t' : LB.Gen (LB.LinComb L φ' ε)} (ht : t.IsGen) (ht' : t'.IsGen) (r : Z ⟶ Y) (r' : Z ⟶ Y')
    (h : ∀ i, r ≫ φ i = r' ≫ φ' i)
    (hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t r) (LB.pullGen L _ _ t' r'))
    (a : I → L.ι) {A : Z.Opens} (hA : A ≤ r ⁻¹ᵁ LB.wchart L φ a)
    (hA' : A ≤ r' ⁻¹ᵁ LB.wchart L φ' a) :
    r'.appLE (LB.wchart L φ' a) A hA' (LB.ts t' a : Γ(Y', LB.wchart L φ' a)ˣ) =
      r.appLE (LB.wchart L φ a) A hA (LB.ts t a : Γ(Y, LB.wchart L φ a)ˣ) := by
  have hur : res hA' (pullU r' (LB.wchart L φ' a) (t'.s a)) =
      res hA (pullU r (LB.wchart L φ a) (t.s a)) := by
    refine unit_ext fun z hz => ?_
    rw [gm_res _ z hA hz, gm_res _ z hA' hz, gm_pull _ r z _ (hA hz), gm_pull _ r' z _ (hA' hz),
      Category.id_comp, Category.id_comp]
    exact (gm_eq_of_corr hL ht ht' r r' h hc z a (hA hz) (hA' hz)).symm
  exact congrArg Units.val hur

/- English proof (translation)
Introduce `V _ _ _ K _ _ _ H X p e hsm hgi he eK heK L hL I _ φ ε t ρ ht hρ hc`. Establish `hK` using `IsPullback.of_hasPullback p (etaK V K)`. Establish `hs` using `IsPullback.of_hasPullback p (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))`. Use `isIntegral_of_geometricallyIntegral hK` as an intermediate fact. Use `isIntegral_of_geometricallyIntegral hs` as an intermediate fact.

Establish `hcomp : ∀ i, eK ≫ pullback.fst p (etaK V K) ≫ φ i = etaK V K ≫ e ≫ φ i` using `fun i => by`. Rewrite using `[← Category.assoc, heK, Category.assoc]`. Take `⟨a₀, h₀⟩` from `LB.mem_of_cover (LB.isLB_linComb hL (fun i => e ≫ φ i) ε) (IsLocalRing.closedPoint V)`. Establish `hA' : LB.wchart L (fun i => etaK V K ≫ e ≫ φ i) a₀ = etaK V K ⁻¹ᵁ LB.wchart L (fun i => e ≫ φ i) a₀` using `wchart_comp L _ _ _`. Establish `hA'' : LB.wchart L (fun i => etaK V K ≫ e ≫ φ i) a₀ ≤ eK ⁻¹ᵁ LB.wchart L (fun i => pullback.fst p (etaK V K) ≫ φ i) a₀`.

Rewrite using `[← wchart_comp, funext hcomp]`. Take `⟨s, ⟨hsu, hsc, hsr⟩, huniq⟩` from `existsUnique_isUnit_appLE_eq hK hs (U := LB.wchart L φ) (g := fun a b ↦ LB.lcg L φ ε a b) (W := LB.wchart L fun k ↦ pullback.fst p (etaK V K) ≫ φ k) (wchart_comp L _ φ) (LB.mem_of_cover (LB.isLB_linComb hL φ ε)) (fun a b ↦ Units.isUnit _) (r := fun a ↦ LB.ts t a) (fun a b ↦ by`. Use `congrArg Units.val ((LB.isGen_iff L t).1 ht a b)` as an intermediate fact. Rewrite `this` using `[LB.lcg_comp]`. Conclude with `this)`.

Use the proof step `(fun a ↦ Units.isUnit _) he heK (a₀ := a₀) (A := LB.wchart L (fun i => e ≫ φ i) a₀) h₀`. Use the proof step `(wchart_comp L e φ a₀).le hA' hA'' (LB.ts ρ a₀).isUnit`. Use the proof step `(res_pullU_eq_of_corr hL ht hρ eK (etaK V K) hcomp hc a₀ hA'' hA'.le)`. Use `⟨⟨fun a ↦ (hsu a).unit⟩, ⟨fun a b ↦ Units.ext (hsc a b), ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `congrArg LB.Gen.mk (funext fun a ↦ Units.ext (hsr a))`.

Introduce and unpack `⟨r'⟩ ⟨h₁, h₂⟩`. Use `huniq (fun a ↦ (r' a).val) ⟨fun a ↦ Units.isUnit _, fun a b ↦ congrArg Units.val (h₁ a b), fun a ↦ congrArg (fun c ↦ (LB.ts c a).val) h₂⟩` as an intermediate fact. Conclude with `congrArg LB.Gen.mk (funext fun a ↦ Units.ext (congrFun this a))`.
-/
theorem existsUnique_gen_extend :
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] (H X : Scheme.{0}) (p : H ⟶ Spec (CommRingCat.of V)) (e : Spec (CommRingCat.of V) ⟶ H), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → ∀ (eK : Spec (CommRingCat.of K) ⟶ pullback p (etaK V K)), eK ≫ pullback.fst p (etaK V K) = etaK V K ≫ e → ∀ (L : LB X), L.IsLB → ∀ (I : Type) [Fintype I] (φ : I → (H ⟶ X)) (ε : I → ℤ) (t : LB.Gen (LB.LinComb L (fun i => pullback.fst p (etaK V K) ≫ φ i) ε)) (ρ : LB.Gen (LB.LinComb L (fun i => e ≫ φ i) ε)), t.IsGen → ρ.IsGen → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eK) (LB.pullGen L _ _ ρ (etaK V K)) → ∃! c : LB.Gen (LB.LinComb L φ ε), c.IsGen ∧ LB.pullGen L _ _ c (pullback.fst p (etaK V K)) = t := by
  intro V _ _ _ K _ _ _ H X p e hsm hgi he eK heK L hL I _ φ ε t ρ ht hρ hc
  have hK := IsPullback.of_hasPullback p (etaK V K)
  have hs := IsPullback.of_hasPullback p
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))
  have := isIntegral_of_geometricallyIntegral hK
  have := isIntegral_of_geometricallyIntegral hs
  have hcomp : ∀ i, eK ≫ pullback.fst p (etaK V K) ≫ φ i = etaK V K ≫ e ≫ φ i := fun i => by
    rw [← Category.assoc, heK, Category.assoc]
  obtain ⟨a₀, h₀⟩ := LB.mem_of_cover (LB.isLB_linComb hL (fun i => e ≫ φ i) ε)
    (IsLocalRing.closedPoint V)
  have hA' : LB.wchart L (fun i => etaK V K ≫ e ≫ φ i) a₀ =
      etaK V K ⁻¹ᵁ LB.wchart L (fun i => e ≫ φ i) a₀ := wchart_comp L _ _ _
  have hA'' : LB.wchart L (fun i => etaK V K ≫ e ≫ φ i) a₀ ≤
      eK ⁻¹ᵁ LB.wchart L (fun i => pullback.fst p (etaK V K) ≫ φ i) a₀ := by
    rw [← wchart_comp, funext hcomp]
  obtain ⟨s, ⟨hsu, hsc, hsr⟩, huniq⟩ := existsUnique_isUnit_appLE_eq hK hs
    (U := LB.wchart L φ) (g := fun a b ↦ LB.lcg L φ ε a b)
    (W := LB.wchart L fun k ↦ pullback.fst p (etaK V K) ≫ φ k)
    (wchart_comp L _ φ) (LB.mem_of_cover (LB.isLB_linComb hL φ ε)) (fun a b ↦ Units.isUnit _)
    (r := fun a ↦ LB.ts t a)
    (fun a b ↦ by
      have := congrArg Units.val ((LB.isGen_iff L t).1 ht a b)
      rw [LB.lcg_comp] at this
      exact this)
    (fun a ↦ Units.isUnit _) he heK (a₀ := a₀) (A := LB.wchart L (fun i => e ≫ φ i) a₀) h₀
    (wchart_comp L e φ a₀).le hA' hA'' (LB.ts ρ a₀).isUnit
    (res_pullU_eq_of_corr hL ht hρ eK (etaK V K) hcomp hc a₀ hA'' hA'.le)
  refine ⟨⟨fun a ↦ (hsu a).unit⟩, ⟨fun a b ↦ Units.ext (hsc a b), ?_⟩, ?_⟩
  · exact congrArg LB.Gen.mk (funext fun a ↦ Units.ext (hsr a))
  · rintro ⟨r'⟩ ⟨h₁, h₂⟩
    have := huniq (fun a ↦ (r' a).val) ⟨fun a ↦ Units.isUnit _,
      fun a b ↦ congrArg Units.val (h₁ a b), fun a ↦ congrArg (fun c ↦ (LB.ts c a).val) h₂⟩
    exact congrArg LB.Gen.mk (funext fun a ↦ Units.ext (congrFun this a))

end GlobalTheory.GenExtend
