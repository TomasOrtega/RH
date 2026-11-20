import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RosLevel
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ToUnitCompLeft
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR (pGl fGl)
open Formalism.L2.Pj GlobalTheory.RayEv GlobalTheory.FormalPoint GlobalTheory.AdicColimit GlobalTheory.RayEv.Transport
open GlobalTheory.TorusInvariance (wVal)
open GlobalTheory.EndRosati (push)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RayEv.Transport

section Helpers

variable {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

/- English proof (translation)
Take `⟨t, hv⟩` from `exists_sec hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => (hF U h).trans (Fintype.prod_empty _).symm) s`. Establish `le : (⊤ : Y.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim` using `fun _ _ => Set.mem_iInter.2 fun k => k.elim`. Use `⟨(Y.presheaf.map (homOfLE le).op).hom (t.f PEmpty.elim), fun Z r z J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[← hv Z r z J hJ, sval_of t r z J PEmpty.elim (fun k => k.elim)]`. Conclude with `(gs_res r z le trivial _).symm`.
-/
theorem exists_fn_of_formal (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (hF : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = 1)
    (s : LB.Sec (LB.LinComb L φ ε)) :
    ∃ a : Γ(Y, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → sval s r z J = gs r z ⊤ a := by
  obtain ⟨t, hv⟩ := exists_sec hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun U _ h => (hF U h).trans (Fintype.prod_empty _).symm) s
  have le : (⊤ : Y.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨(Y.presheaf.map (homOfLE le).op).hom (t.f PEmpty.elim), fun Z r z J hJ => ?_⟩
  rw [← hv Z r z J hJ, sval_of t r z J PEmpty.elim (fun k => k.elim)]
  exact (gs_res r z le trivial _).symm

/- English proof (translation)
Establish `h1 : (adicLevelι J n).appTop.hom (toΓ W a) = 0` using `fn_ext (V := ⊤) fun z _ => (gs_pull (𝟙 _) (adicLevelι J n) z ⊤ trivial _).trans (by`. Rewrite using `[Category.id_comp, h z]`. Conclude with `(DVR.gs_zero (𝟙 _) z ⊤ trivial).symm)`. Establish `h2` using `congrArg (fun q => q.hom (toΓ W a)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ n))))`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2`.

Rewrite `h2` using `[h1, map_zero]`. Establish `h3 : (Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom (toΓ W a) = a`. Simplify using `only [toΓ]`. Conclude with `Iso.inv_hom_id_apply _ _`. Rewrite `h2` using `[h3]`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 h2.symm`.
-/
theorem mem_pow_of_gs {W : Type} [CommRing W] (J : Ideal W) (n : ℕ) (a : W)
    (h : ∀ z, gs (adicLevelι J n) z ⊤ (toΓ W a) = 0) : a ∈ J ^ n := by
  have h1 : (adicLevelι J n).appTop.hom (toΓ W a) = 0 := fn_ext (V := ⊤) fun z _ =>
    (gs_pull (𝟙 _) (adicLevelι J n) z ⊤ trivial _).trans (by
      rw [Category.id_comp, h z]; exact (DVR.gs_zero (𝟙 _) z ⊤ trivial).symm)
  have h2 := congrArg (fun q => q.hom (toΓ W a))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ n))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  rw [h1, map_zero] at h2
  have h3 : (Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom (toΓ W a) = a := by
    simp only [toΓ]; exact Iso.inv_hom_id_apply _ _
  rw [h3] at h2
  exact Ideal.Quotient.eq_zero_iff_mem.1 h2.symm

/- English proof (translation)
Simplify using `only [toΓ]`. Conclude with `Iso.hom_inv_id_apply _ _`.
-/
theorem toΓ_hom {W : Type} [CommRing W] (a : Γ(Sp W, ⊤)) :
    toΓ W ((Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom a) = a := by
  simp only [toΓ]; exact Iso.hom_inv_id_apply _ _

end Helpers

/- English proof (translation)
Introduce `R _ _ I D A G _ _ U W _ φ ξ x' hx b hb g' g hg' hg hfr k σ F hexp`. Substitute `hb` using the available equality. Establish `hL` using `U.LG.isLB`. Establish `hM` using `D.toPre.P.isLB`. Take `⟨a, ha⟩` from `exists_fn_of_formal hL (φ := Sum.elim (fun _ : Fin 1 => x'.left ≫ 𝟙 G.left) (fun _ : PUnit.{1} => x'.left)) (ε := Sum.elim (fun _ => (k : ℤ)) (fun _ => -((k : ℤ) * 1))) (fun U _ h => by simp [Fintype.prod_sum_type]) (pullMulSec σ x'.left (LB.invGen U.LG.L _ _ (GeneratorPullback.p …`.

Establish `h1 : ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp W) (z : Z) (JL), Good U.LG.L z JL → sval σ (r ≫ x'.left) z JL = gs r z ⊤ a * (val g' r z JL ^ k).val`. Introduce `Z r z JL hJL`. Establish `e₁` using `(ha Z r z JL hJL).symm.trans (sval_pullMulSec σ x'.left _ _ r z hJL)`. Rewrite `e₁` using `[val_inv, show val (GeneratorPullback.powGen U.LG.L _ _ g' k) r z JL = val g' r z JL ^ k from map_pow _ _ _]`. Rewrite using `[e₁, _root_.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, _root_.mul_one]`.

Establish `ht : ∀ α, ∃ c : Γ(Sp W, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp W) (z : Z) (JM), Good D.toPre.P.L z JM → sval (F α) (r ≫ ξ.b.left) z JM * (val (ξ.s α) r z JM).val = gs r z ⊤ c * (val g r z JM ^ k).val`. Introduce `α`. Take `⟨c, hc⟩` from `exists_fn_of_formal hM (φ := Sum.elim (fun i => ξ.b.left ≫ D.toPre.famφB α i) (Sum.elim (DegPre.gtφT D.toPre (Over.mk (spMap φ)) ξ.b α) (fun _ : PUnit.{1} => ξ.b.left))) (ε := Sum.elim (DegPre.famε k) (Sum.elim DegPre.gtε (fun _ => -((k : ℤ) * 1)))) (fun U _ h => by`. Establish `e` using `GlobalTheory.ConstTerm.prod_factors (fun i => h (ξ.b.left ≫ D.toPre.famφB α i)) k`. Establish `e₀ : ∀ i, h (DegPre.gtφT D.toPre (Over.mk (spMap φ)) ξ.b α i) = ![h (ξ.b.left ≫ D.toPre.famφB α 1), h (ξ.b.left ≫ D.toPre.famφB α 2), h (ξ.b.left ≫ D.toPre.famφB α 0), h (ξ.b.left ≫ D.toPre.famφB α 3)] i`.

Introduce `i`. Apply the tactic sequence `fin_cases i <;> simp [GlobalTheory.ConstTerm.comp_famφB]`. Simplify using `only [← e₀] at e`. Establish `e₁ : ξ.b.left ≫ D.toPre.famφB α 0 = ξ.b.left` using `Category.comp_id _`. Rewrite using `[Fintype.prod_sum_type, Fintype.prod_sum_type]`.

Simplify using `only [Sum.elim_inl, Sum.elim_inr]`. Rewrite using `[← _root_.mul_assoc, e, e₁]`. Use the proof step `simp)`. Use the proof step `(pullMulSec (F α) ξ.b.left (LB.mulGen D.toPre.P.L _ _ _ _ (ξ.s α) (LB.invGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ g k))) (DVR.mulGen_isGen _ _ _ _ _ _ _ (ξ.isGen α) (DVR.invGen_isGen _ _ _ _ (DVR.powGen_isGen _ _ _ _ hg k))))`. Use `⟨c, fun Z r z JM hJM => ?_⟩` and prove the remaining obligations.

Establish `e₁` using `(hc Z r z JM hJM).symm.trans (sval_pullMulSec (F α) ξ.b.left _ _ r z hJM)`. Rewrite `e₁` using `[val_mul hJM, val_inv, show val (GeneratorPullback.powGen D.toPre.P.L _ _ g k) r z JM = val g r z JM ^ k from map_pow _ _ _]`. Rewrite using `[e₁, Units.val_mul, _root_.mul_assoc, _root_.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, _root_.mul_one]`. Use `choose c hc using ht`. Use `⟨(Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom a, fun α => (Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom (c α), fun Z r z JL hJL => ?_, fun α Z r z JM hJM => ?_, fun e => ?_⟩` and prove the remaining obligations.

Rewrite using `[toΓ_hom]`. Conclude with `h1 Z r z JL hJL`. Rewrite using `[toΓ_hom]`. Conclude with `hc α Z r z JM hJM`. Use `set J := I.map φ`.

Take `⟨S, hS⟩` from `DVR.expandsAt_val U e k σ F (hexp e)`. Establish `hy₁ : reduction I x' e ≫ fGl I G e = adicLevelι J (e + 1) ≫ x'.left` using `reduction_fstG I x' e`. Take `⟨hy₂, hy₃⟩` from `(hasCoords_iff U e ξ _ _).1 (hx e _ (adicLevelι J (e + 1)) (reduction I x' e) hy₁)`. Establish `gM : ∀ z : Sp (W ⧸ J ^ (e + 1)), ∃ JM, Good D.toPre.P.L z JM` using `fun z => by choose C hC using fun ψ : Sp (W ⧸ J ^ (e + 1)) ⟶ D.toPre.P.A.left => exists_chart hM (ψ z)`. Conclude with `⟨C, hC⟩`.

Establish `gL : ∀ z : Sp (W ⧸ J ^ (e + 1)), ∃ JL, Good U.LG.L z JL` using `fun z => by choose C hC using fun ψ : Sp (W ⧸ J ^ (e + 1)) ⟶ G.left => exists_chart hL (ψ z)`. Conclude with `⟨C, hC⟩`. Use `⟨S, fun α hα => mem_pow_of_gs J (e + 1) _ fun z => ?_, mem_pow_of_gs J (e + 1) _ fun z => ?_⟩` and prove the remaining obligations. Take `⟨JM, hJM⟩` from `gM z`. Establish `h0` using `(hS _ (reduction I x' e) z JM hJM).1 α hα`.

Rewrite `h0` using `[hy₂]`. Establish `h2` using `hc α _ (adicLevelι J (e + 1)) z JM hJM`. Rewrite `h2` using `[h0, zero_mul]`. Rewrite using `[toΓ_hom]`. Conclude with `(Units.mul_left_eq_zero _).1 h2.symm`.

Take `⟨JM, hJM⟩` from `gM z`. Take `⟨JL, hJL⟩` from `gL z`. Establish `hE` using `(hS _ (reduction I x' e) z JM hJM).2 (JL (reduction I x' e ≫ fGl I G e)) (hJL _)`. Establish `hw` using `hfr e _ (adicLevelι J (e + 1)) (reduction I x' e) hy₁ z JM JL hJM hJL`. Establish `hsv : DVR.sv U k σ (reduction I x' e ≫ fGl I G e) z (JL (reduction I x' e ≫ fGl I G e)) = sval σ (adicLevelι J (e + 1) ≫ x'.left) z JL`.

Rewrite using `[← hy₁]; exact (sval_of σ _ z JL _ fun _ => by rw [Category.comp_id]).symm`. Establish `hwv : DVR.wv U e (reduction I x' e) z (JM (reduction I x' e ≫ pGl U e)) (JL (reduction I x' e ≫ fGl I G e)) = wVal U e z JM JL (reduction I x' e)` using `rfl`. Establish `hterm : ∀ α ∈ S, sval (F α) (reduction I x' e ≫ pGl U e) z JM * (val (DVR.tG U e α) (reduction I x' e) z JM).val = gs (adicLevelι J (e + 1)) z ⊤ (c α) * (val g (adicLevelι J (e + 1)) z JM ^ k).val` using `fun α _ => by`. Rewrite using `[hy₃ α z JM hJM, hy₂]`. Conclude with `hc α _ _ z JM hJM`.

Rewrite `hE` using `[hsv, h1 _ _ z JL hJL, Finset.sum_congr rfl hterm, ← Finset.sum_mul, hwv, hw, mul_pow, Units.val_mul]`. Establish `hfin : gs (adicLevelι J (e + 1)) z ⊤ a = ∑ α ∈ S, gs (adicLevelι J (e + 1)) z ⊤ (c α)`. Use `(Units.mul_left_inj (wVal U e z JM JL (reduction I x' e) ^ k * val g' (adicLevelι J (e + 1)) z JL ^ k)).1 ?_` and prove the remaining obligations. Rewrite using `[Units.val_mul]`. Take the linear combination `hE`.

Establish `gsub : ∀ x y : Γ(Sp W, ⊤), gs (adicLevelι J (e + 1)) z ⊤ (x - y) = gs (adicLevelι J (e + 1)) z ⊤ x - gs (adicLevelι J (e + 1)) z ⊤ y` using `fun x y => by`. Simplify using `only [gs_eq _ z ⊤ trivial, map_sub]`. Rewrite using `[map_sub, map_sum, toΓ_hom, gsub, DVR.gs_fsum _ z ⊤ trivial, hfin, sub_eq_zero]`. Conclude with `Finset.sum_congr rfl fun α _ => by rw [toΓ_hom]`.
-/
theorem exists_adic_expansion : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (W : Type) [CommRing W] (φ : R →+* W) (ξ : GtPt D.toPre (Over.mk (spMap φ))) (x' : Over.mk (spMap φ) ⟶ G), IsPointOf U ξ x' → ∀ (b : Sp W ⟶ D.toPre.P.A.left), ξ.b.left = b → ∀ (g' : Frame U.LG.L (Y := Sp W) x'.left) (g : Frame D.toPre.P.L b), g'.IsGen → g.IsGen → FrRel U (T := Sp W) x'.left b g' g → ∀ (k : ℕ) (σ : H0 U.LG.L k) (F : ∀ α, D.toPre.SecB k α), (∀ e, U.ExpandsAt e k σ F) → ∃ (s : W) (t : D.toPre.X → W), (∀ (Z : Scheme.{0}) (r : Z ⟶ Sp W) (z : Z) (JL), Good U.LG.L z JL → sval σ (r ≫ x'.left) z JL = gs r z ⊤ (toΓ W s) * (val g' r z JL ^ k).val) ∧ (∀ (α : D.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (z : Z) (JM), Good D.toPre.P.L z JM → sval (F α) (r ≫ b) z JM * (val (ξ.s α) r z JM).val = gs r z ⊤ (toΓ W (t α)) * (val g r z JM ^ k).val) ∧ ∀ e : ℕ, ∃ S : Finset D.toPre.X, (∀ α ∉ S, t α ∈ I.map φ ^ (e + 1)) ∧ s - ∑ α ∈ S, t α ∈ I.map φ ^ (e + 1) := by
  intro R _ _ I D A G _ _ U W _ φ ξ x' hx b hb g' g hg' hg hfr k σ F hexp
  subst hb
  have hL := U.LG.isLB
  have hM := D.toPre.P.isLB

  obtain ⟨a, ha⟩ := exists_fn_of_formal hL
    (φ := Sum.elim (fun _ : Fin 1 => x'.left ≫ 𝟙 G.left) (fun _ : PUnit.{1} => x'.left))
    (ε := Sum.elim (fun _ => (k : ℤ)) (fun _ => -((k : ℤ) * 1)))
    (fun U _ h => by simp [Fintype.prod_sum_type])
    (pullMulSec σ x'.left (LB.invGen U.LG.L _ _ (GeneratorPullback.powGen U.LG.L _ _ g' k))
      (DVR.invGen_isGen _ _ _ _ (DVR.powGen_isGen _ _ _ _ hg' k)))
  have h1 : ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp W) (z : Z) (JL), Good U.LG.L z JL →
      sval σ (r ≫ x'.left) z JL = gs r z ⊤ a * (val g' r z JL ^ k).val := by
    intro Z r z JL hJL
    have e₁ := (ha Z r z JL hJL).symm.trans (sval_pullMulSec σ x'.left _ _ r z hJL)
    rw [val_inv, show val (GeneratorPullback.powGen U.LG.L _ _ g' k) r z JL = val g' r z JL ^ k from map_pow _ _ _] at e₁
    rw [e₁, _root_.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, _root_.mul_one]

  have ht : ∀ α, ∃ c : Γ(Sp W, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp W) (z : Z) (JM), Good D.toPre.P.L z JM →
      sval (F α) (r ≫ ξ.b.left) z JM * (val (ξ.s α) r z JM).val = gs r z ⊤ c * (val g r z JM ^ k).val := by
    intro α
    obtain ⟨c, hc⟩ := exists_fn_of_formal hM
      (φ := Sum.elim (fun i => ξ.b.left ≫ D.toPre.famφB α i)
        (Sum.elim (DegPre.gtφT D.toPre (Over.mk (spMap φ)) ξ.b α) (fun _ : PUnit.{1} => ξ.b.left)))
      (ε := Sum.elim (DegPre.famε k) (Sum.elim DegPre.gtε (fun _ => -((k : ℤ) * 1))))
      (fun U _ h => by
        have e := GlobalTheory.ConstTerm.prod_factors (fun i => h (ξ.b.left ≫ D.toPre.famφB α i)) k
        have e₀ : ∀ i, h (DegPre.gtφT D.toPre (Over.mk (spMap φ)) ξ.b α i) =
            ![h (ξ.b.left ≫ D.toPre.famφB α 1), h (ξ.b.left ≫ D.toPre.famφB α 2),
              h (ξ.b.left ≫ D.toPre.famφB α 0), h (ξ.b.left ≫ D.toPre.famφB α 3)] i := by
          intro i
          fin_cases i <;> simp [GlobalTheory.ConstTerm.comp_famφB]
        simp only [← e₀] at e
        have e₁ : ξ.b.left ≫ D.toPre.famφB α 0 = ξ.b.left := Category.comp_id _
        rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr]
        rw [← _root_.mul_assoc, e, e₁]
        simp)
      (pullMulSec (F α) ξ.b.left
        (LB.mulGen D.toPre.P.L _ _ _ _ (ξ.s α) (LB.invGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ g k)))
        (DVR.mulGen_isGen _ _ _ _ _ _ _ (ξ.isGen α)
          (DVR.invGen_isGen _ _ _ _ (DVR.powGen_isGen _ _ _ _ hg k))))
    refine ⟨c, fun Z r z JM hJM => ?_⟩
    have e₁ := (hc Z r z JM hJM).symm.trans (sval_pullMulSec (F α) ξ.b.left _ _ r z hJM)
    rw [val_mul hJM, val_inv,
      show val (GeneratorPullback.powGen D.toPre.P.L _ _ g k) r z JM = val g r z JM ^ k from map_pow _ _ _] at e₁
    rw [e₁, Units.val_mul, _root_.mul_assoc, _root_.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, _root_.mul_one]
  choose c hc using ht
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom a,
    fun α => (Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom (c α), fun Z r z JL hJL => ?_,
    fun α Z r z JM hJM => ?_, fun e => ?_⟩
  · rw [toΓ_hom]; exact h1 Z r z JL hJL
  · rw [toΓ_hom]; exact hc α Z r z JM hJM
  · set J := I.map φ
    obtain ⟨S, hS⟩ := DVR.expandsAt_val U e k σ F (hexp e)
    have hy₁ : reduction I x' e ≫ fGl I G e = adicLevelι J (e + 1) ≫ x'.left := reduction_fstG I x' e
    obtain ⟨hy₂, hy₃⟩ := (hasCoords_iff U e ξ _ _).1 (hx e _ (adicLevelι J (e + 1)) (reduction I x' e) hy₁)
    have gM : ∀ z : Sp (W ⧸ J ^ (e + 1)), ∃ JM, Good D.toPre.P.L z JM := fun z => by
      choose C hC using fun ψ : Sp (W ⧸ J ^ (e + 1)) ⟶ D.toPre.P.A.left => exists_chart hM (ψ z)
      exact ⟨C, hC⟩
    have gL : ∀ z : Sp (W ⧸ J ^ (e + 1)), ∃ JL, Good U.LG.L z JL := fun z => by
      choose C hC using fun ψ : Sp (W ⧸ J ^ (e + 1)) ⟶ G.left => exists_chart hL (ψ z)
      exact ⟨C, hC⟩
    refine ⟨S, fun α hα => mem_pow_of_gs J (e + 1) _ fun z => ?_, mem_pow_of_gs J (e + 1) _ fun z => ?_⟩
    · obtain ⟨JM, hJM⟩ := gM z
      have h0 := (hS _ (reduction I x' e) z JM hJM).1 α hα
      rw [hy₂] at h0
      have h2 := hc α _ (adicLevelι J (e + 1)) z JM hJM
      rw [h0, zero_mul] at h2
      rw [toΓ_hom]
      exact (Units.mul_left_eq_zero _).1 h2.symm
    · obtain ⟨JM, hJM⟩ := gM z
      obtain ⟨JL, hJL⟩ := gL z
      have hE := (hS _ (reduction I x' e) z JM hJM).2 (JL (reduction I x' e ≫ fGl I G e)) (hJL _)
      have hw := hfr e _ (adicLevelι J (e + 1)) (reduction I x' e) hy₁ z JM JL hJM hJL
      have hsv : DVR.sv U k σ (reduction I x' e ≫ fGl I G e) z (JL (reduction I x' e ≫ fGl I G e)) =
          sval σ (adicLevelι J (e + 1) ≫ x'.left) z JL := by
        rw [← hy₁]; exact (sval_of σ _ z JL _ fun _ => by rw [Category.comp_id]).symm
      have hwv : DVR.wv U e (reduction I x' e) z (JM (reduction I x' e ≫ pGl U e))
          (JL (reduction I x' e ≫ fGl I G e)) = wVal U e z JM JL (reduction I x' e) := rfl
      have hterm : ∀ α ∈ S, sval (F α) (reduction I x' e ≫ pGl U e) z JM *
          (val (DVR.tG U e α) (reduction I x' e) z JM).val =
          gs (adicLevelι J (e + 1)) z ⊤ (c α) * (val g (adicLevelι J (e + 1)) z JM ^ k).val := fun α _ => by
        rw [hy₃ α z JM hJM, hy₂]; exact hc α _ _ z JM hJM
      rw [hsv, h1 _ _ z JL hJL, Finset.sum_congr rfl hterm, ← Finset.sum_mul, hwv, hw, mul_pow,
        Units.val_mul] at hE
      have hfin : gs (adicLevelι J (e + 1)) z ⊤ a = ∑ α ∈ S, gs (adicLevelι J (e + 1)) z ⊤ (c α) := by
        refine (Units.mul_left_inj (wVal U e z JM JL (reduction I x' e) ^ k *
          val g' (adicLevelι J (e + 1)) z JL ^ k)).1 ?_
        rw [Units.val_mul]
        linear_combination hE
      have gsub : ∀ x y : Γ(Sp W, ⊤), gs (adicLevelι J (e + 1)) z ⊤ (x - y) =
          gs (adicLevelι J (e + 1)) z ⊤ x - gs (adicLevelι J (e + 1)) z ⊤ y := fun x y => by
        simp only [gs_eq _ z ⊤ trivial, map_sub]
      rw [map_sub, map_sum, toΓ_hom, gsub, DVR.gs_fsum _ z ⊤ trivial, hfin, sub_eq_zero]
      exact Finset.sum_congr rfl fun α _ => by rw [toΓ_hom]

end GlobalTheory.RayEv.Transport
