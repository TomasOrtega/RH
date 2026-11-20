import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharactersEighthPowerElementaryMatricesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsEighthPowerProjectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsTauCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowCompMonHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackGenMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianHomExtendsUniquelyOverDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.EighthPow

def matAct {X : Type} [AddCommGroup X] (M : Matrix (Fin 8) (Fin 8) ℤ) (t : Fin 8 → X) : Fin 8 → X :=
  fun v => ∑ u, M v u • t u

/- English proof (translation)
Use function extensionality and compare the values at `v`. Simplify using `only [matAct, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, mul_smul]`. Conclude with `Finset.sum_comm`.
-/
theorem matAct_mul {X : Type} [AddCommGroup X] (N M : Matrix (Fin 8) (Fin 8) ℤ) (t : Fin 8 → X) :
    matAct N (matAct M t) = matAct (N * M) t := by
  funext v
  simp only [matAct, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, mul_smul]
  exact Finset.sum_comm

/- English proof (translation)
Use function extensionality and compare the values at `v`. Simplify using `[matAct, Matrix.one_apply, ite_smul]`.
-/
theorem matAct_one {X : Type} [AddCommGroup X] (t : Fin 8 → X) : matAct 1 t = t := by
  funext v
  simp [matAct, Matrix.one_apply, ite_smul]

def matEquiv {X : Type} [AddCommGroup X] (M : Matrix (Fin 8) (Fin 8) ℤ) (h : M.det = 1) :
    (Fin 8 → X) ≃+ (Fin 8 → X) where
  toFun := matAct M
  invFun := matAct M.adjugate
  left_inv t := by rw [matAct_mul, Matrix.adjugate_mul, h, one_smul, matAct_one]
  right_inv t := by rw [matAct_mul, Matrix.mul_adjugate, h, one_smul, matAct_one]
  map_add' s t := by funext v; simp [matAct, smul_add, Finset.sum_add_distrib]

def sumHom {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (c : Fin 8 → (X →+ Y)) : (Fin 8 → X) →+ Y :=
  AddMonoidHom.mk' (fun y => ∑ v, c v (y v)) fun s t => by simp [Finset.sum_add_distrib]

end GlobalTheory.Poinc.EighthPow

open GlobalTheory.Poinc.EighthPow in

/- English proof (translation)
Introduce `R _ _ _ hRb hdvr G _ _ hG D A U G' _ _ hG' D' A' U' W hW pr hpr huniv hL ϖ β hs hp hτ`. Use `haveI := hdvr`. Establish `hext : ∀ v, ∃ p : G' ⟶ G, IsMonHom p ∧ (Over.pullback (jK R)).map p ≫ U.gen.hom = U'.gen.hom ≫ pr v`. Introduce `v`. Establish `h1` using `U'.gen_hom`.

Establish `h2` using `U.gen_hom`. Establish `: IsMonHom U.gen.symm.hom` using `by show IsMonHom U.gen.inv; infer_instance`. Use `haveI := hpr v`. Take `⟨F, ⟨hF, hFe⟩, -⟩` from `GlobalTheory.semiAbelian_hom_extends_uniquely_dvr R (FractionRing R) G' G hG' hG (U'.gen.hom ≫ pr v ≫ U.gen.symm.hom) inferInstance`. Use `⟨F, hF, ?_⟩` and prove the remaining obligations.

Establish `hFe' : (Over.pullback (jK R)).map F = U'.gen.hom ≫ pr v ≫ U.gen.inv` using `hFe`. Rewrite using `[hFe']`. Simplify using the standard rewrite rules. Use `choose pG hpGm hpG using hext`. Establish `hc : ∀ v, ∃ ρ, TorMatch U U' (RingHom.id R) (pG v).left ρ` using `fun v => GlobalTheory.Poinc.HomTor.exists_torMatch R hRb G hG D A U G' hG' D' A' U' (pG v) (hpGm v)`.

Use `choose c hc using hc`. Take `⟨hbij, hmat⟩` from `GlobalTheory.T.characters_eighthPower_elementaryMatrices_alt R hRb hdvr G hG D A U G' hG' D' A' U' W hW pr hpr huniv hL pG hpGm hpG c hc`. Set `Φ : (Fin 8 → D.toPre.X) ≃+ D'.toPre.X` to `AddEquiv.ofBijective (sumHom c) hbij`. Set `Mq : (Fin 8 → D.toPre.X) ≃+ (Fin 8 → D.toPre.X)` to `matEquiv (W + W.transpose) hW.2`. Set `e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X)` to `(Mq.trans Φ).symm`.

Establish `he : ∀ y, Φ (Mq (e y)) = y` using `fun y => (Mq.trans Φ).apply_symm_apply y`. Establish `he' : ∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y` using `he`. Use `⟨e, ?_, ?_⟩` and prove the remaining obligations. Introduce `y r hr`. Establish `hlab` using `fun v => GlobalTheory.T.torsionLabels_eighthPower_projections R hRb hdvr G hG D A U G' hG' D' A' U' W hW pr hpr huniv hL pG hpGm hpG c hc e he' v`.

Use `GlobalTheory.Poinc.E8Order.main R hdvr D.toPre D'.toPre D'.tau_bimult D'.psi_even D.tau_bimult W hW ϖ β hs hp hτ c e he' ?_ y r hr` and prove the remaining obligations. Introduce `v a' b x x' hx hx'`. Conclude with `GlobalTheory.TauFormHom.main R hRb hdvr G hG D A U G' hG' D' A' U' (pG v) (hpGm v) (c v) ((Pi.evalAddMonoidHom (fun _ => D.toPre.X) v).comp e.toAddMonoidHom) (hc v) (hlab v) a' b x x' hx hx'`. Introduce `a b f f₁ m hf hf₁ hcomp hm y`. Establish `hmc` using `hmat a b f f₁ m hf hf₁ hcomp hm`.

Establish `hy : y = Φ (Mq (e y))` using `(he y).symm`. Set `t' : Fin 8 → D.toPre.X` to `fun w => if w = b then Mq (e y) a else 0`. Establish `hmy : m y = Φ t'` using `by conv_lhs => rw [hy] show m (∑ w, c w (Mq (e y) w)) = ∑ w, c w (t' w)`. Establish `hL : m (∑ w, c w (Mq (e y) w)) = c b (Mq (e y) a)`. Rewrite using `[map_sum]`.

Simplify using `[hmc]`. Establish `hR : ∑ w, c w (t' w) = c b (Mq (e y) a)`. Rewrite using `[Finset.sum_eq_single b (fun w _ hw => by simp only [t', if_neg hw, map_zero]) (by simp)]`. Simplify using `only [t', if_pos rfl]`. Rewrite using `[hL, hR]`.

Establish `hkey : Mq (e (m y)) = t'` using `Φ.injective (by rw [he, hmy])`. Introduce `v`. Establish `h` using `congrFun hkey v`. Express the relevant statement in the definitionally equal form `∑ u, (W + W.transpose) v u • e (m y) u = _ at h`. Rewrite using `[h]`.

Both sides reduce to the same expression.
-/
theorem GlobalTheory.Poinc.EighthPow.main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (ϖ : R) (β : LinearMap.BilinForm ℤ D.toPre.X), (∀ a b, β a b = β b a) → (∀ a, 0 ≤ β a a) → (∀ a b' (x : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D.toPre a b' x → ∃ u : Rˣ, (x : FractionRing R) = algebraMap R (FractionRing R) (u : R) * algebraMap R (FractionRing R) ϖ ^ (β a b')) → ∃ e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X), (∀ y r, PsiCoord D'.toPre y r → 0 ≤ qW W β (e y) ∧ Associated r (ϖ ^ (qW W β (e y)).toNat)) ∧ ∀ (a b : Fin 8) (f : G' ⟶ G') (f₁ : A'.A ⟶ A'.A) (m : D'.toPre.X →+ D'.toPre.X), IsMonHom f → MatEnd pr a b f₁ → (Over.pullback (jK R)).map f ≫ U'.gen.hom = U'.gen.hom ≫ f₁ → EndChar U' f m → ∀ y, MatRel W a b (e y) (e (m y)) := by
  intro R _ _ _ hRb hdvr G _ _ hG D A U G' _ _ hG' D' A' U' W hW pr hpr huniv hL ϖ β hs hp hτ
  haveI := hdvr
  have hext : ∀ v, ∃ p : G' ⟶ G, IsMonHom p ∧
      (Over.pullback (jK R)).map p ≫ U.gen.hom = U'.gen.hom ≫ pr v := by
    intro v
    have h1 := U'.gen_hom
    have h2 := U.gen_hom
    have : IsMonHom U.gen.symm.hom := by show IsMonHom U.gen.inv; infer_instance
    haveI := hpr v
    obtain ⟨F, ⟨hF, hFe⟩, -⟩ := GlobalTheory.semiAbelian_hom_extends_uniquely_dvr R (FractionRing R) G' G hG' hG
      (U'.gen.hom ≫ pr v ≫ U.gen.symm.hom) inferInstance
    refine ⟨F, hF, ?_⟩
    have hFe' : (Over.pullback (jK R)).map F = U'.gen.hom ≫ pr v ≫ U.gen.inv := hFe
    rw [hFe']
    simp
  choose pG hpGm hpG using hext
  have hc : ∀ v, ∃ ρ, TorMatch U U' (RingHom.id R) (pG v).left ρ := fun v =>
    GlobalTheory.Poinc.HomTor.exists_torMatch R hRb G hG D A U G' hG' D' A' U' (pG v) (hpGm v)
  choose c hc using hc
  obtain ⟨hbij, hmat⟩ := GlobalTheory.T.characters_eighthPower_elementaryMatrices_alt R hRb hdvr G hG D A U G' hG' D' A' U' W hW pr hpr huniv hL pG hpGm hpG c hc
  let Φ : (Fin 8 → D.toPre.X) ≃+ D'.toPre.X := AddEquiv.ofBijective (sumHom c) hbij
  let Mq : (Fin 8 → D.toPre.X) ≃+ (Fin 8 → D.toPre.X) := matEquiv (W + W.transpose) hW.2
  let e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X) := (Mq.trans Φ).symm
  have he : ∀ y, Φ (Mq (e y)) = y := fun y => (Mq.trans Φ).apply_symm_apply y
  have he' : ∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y := he
  refine ⟨e, ?_, ?_⟩
  · intro y r hr
    have hlab := fun v => GlobalTheory.T.torsionLabels_eighthPower_projections R hRb hdvr G hG D A U G' hG' D' A' U' W hW pr hpr huniv hL pG hpGm hpG c hc e
      he' v
    refine GlobalTheory.Poinc.E8Order.main R hdvr D.toPre D'.toPre D'.tau_bimult D'.psi_even D.tau_bimult W hW ϖ β hs hp hτ c e
      he' ?_ y r hr
    intro v a' b x x' hx hx'
    exact GlobalTheory.TauFormHom.main R hRb hdvr G hG D A U G' hG' D' A' U' (pG v) (hpGm v) (c v)
      ((Pi.evalAddMonoidHom (fun _ => D.toPre.X) v).comp e.toAddMonoidHom) (hc v) (hlab v) a' b x x' hx hx'
  · intro a b f f₁ m hf hf₁ hcomp hm y
    have hmc := hmat a b f f₁ m hf hf₁ hcomp hm
    have hy : y = Φ (Mq (e y)) := (he y).symm
    let t' : Fin 8 → D.toPre.X := fun w => if w = b then Mq (e y) a else 0
    have hmy : m y = Φ t' := by
      conv_lhs => rw [hy]
      show m (∑ w, c w (Mq (e y) w)) = ∑ w, c w (t' w)
      have hL : m (∑ w, c w (Mq (e y) w)) = c b (Mq (e y) a) := by
        rw [map_sum]; simp [hmc]
      have hR : ∑ w, c w (t' w) = c b (Mq (e y) a) := by
        rw [Finset.sum_eq_single b (fun w _ hw => by simp only [t', if_neg hw, map_zero]) (by simp)]
        simp only [t', if_pos rfl]
      rw [hL, hR]
    have hkey : Mq (e (m y)) = t' := Φ.injective (by rw [he, hmy])
    intro v
    have h := congrFun hkey v
    change ∑ u, (W + W.transpose) v u • e (m y) u = _ at h
    rw [h]
    rfl
