import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPtEqUnitMulTh
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsGenSecNear
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.DivDeep

open GlobalTheory.ThetaCompare

/- English proof (translation)
Establish `hG : GlobalFnsSt` using `GlobalTheory.abelianSchemeLaws_all.1.globalFns`. Use `P.isAb.comm` as an intermediate fact. Take `⟨α, hα⟩` from `GlobalTheory.EmbLocal.exists_mulPull hG P m T`. Take `⟨β, hβ⟩` from `GlobalTheory.EmbLocal.exists_mulPull hG P M T`. Establish `a` using `torsFrame_pow hG P hα H hJ`.

Establish `b` using `torsFrame_pow hG P hβ H' hJ`. Establish `rα` using `Reg.two (y := y) (J := J) α hα (snd T P.A) (snd T P.A ^ m) rfl rfl`. Establish `rβ` using `Reg.two (y := y) (J := J) β hβ (snd T P.A) (snd T P.A ^ M) rfl rfl`. Establish `c` using `(((rα.pow hJ (M ^ 2)).mul hJ (rβ.pull hJ (snd T P.A ^ m))).mul hJ ((rβ.pow hJ (m ^ 2)).mul hJ (rα.pull hJ (snd T P.A ^ M))).inv).const hG P.isAb P.isLB hJ (fun U _ h => by`. Simplify using `only [SymLiftOdd.comp_pow', lift_snd, ← pow_mul, mul_comm M m]`.

Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_zpow, ofMul_one]`. Use the proof step `module) x 1`. Simplify using `only [SymLiftOdd.comp_pow', pt_snd, H.1, H'.1, one_pow] at c`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Use `replace a := congrArg Additive.ofMul a`. Use `replace b := congrArg Additive.ofMul b`. Use `replace c := congrArg Additive.ofMul c`. Simplify using `only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_div] at a b c ⊢`. Take the linear combination `(norm := module) (M ^ 2) • a - (m ^ 2) • b + c`.
-/
theorem torsFrame_two_levels {S : Scheme.{0}} (P : PolAV S) {T : Over S} {m M : ℕ}
    {rig rig' : LB.Gen (P.L.pull (eSec P.A))} {x : T ⟶ P.A} {τ τ'} (H : IsTorsFrame P rig m x τ)
    (H' : IsTorsFrame P rig' M x τ') {y : T.left} {J} (hJ : Good P.L y J) :
    (val τ (𝟙 _) y J / val τ' (𝟙 _) y J) ^ (m ^ 2 * M ^ 2) =
      (val rig T.hom y J / val rig' T.hom y J) ^ (m ^ 2 * M ^ 2) := by
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have := P.isAb.comm
  obtain ⟨α, hα⟩ := GlobalTheory.EmbLocal.exists_mulPull hG P m T
  obtain ⟨β, hβ⟩ := GlobalTheory.EmbLocal.exists_mulPull hG P M T
  have a := torsFrame_pow hG P hα H hJ
  have b := torsFrame_pow hG P hβ H' hJ
  have rα := Reg.two (y := y) (J := J) α hα (snd T P.A) (snd T P.A ^ m) rfl rfl
  have rβ := Reg.two (y := y) (J := J) β hβ (snd T P.A) (snd T P.A ^ M) rfl rfl
  have c := (((rα.pow hJ (M ^ 2)).mul hJ (rβ.pull hJ (snd T P.A ^ m))).mul hJ
    ((rβ.pow hJ (m ^ 2)).mul hJ (rα.pull hJ (snd T P.A ^ M))).inv).const hG P.isAb P.isLB hJ (fun U _ h => by
      simp only [SymLiftOdd.comp_pow', lift_snd, ← pow_mul, mul_comm M m]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_zpow, ofMul_one]
      module) x 1
  simp only [SymLiftOdd.comp_pow', pt_snd, H.1, H'.1, one_pow] at c
  apply Additive.ofMul.injective
  replace a := congrArg Additive.ofMul a
  replace b := congrArg Additive.ofMul b
  replace c := congrArg Additive.ofMul c
  simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_div] at a b c ⊢
  linear_combination (norm := module) (M ^ 2) • a - (m ^ 2) • b + c

/- English proof (translation)
Assemble the required witnesses or components as `⟨((Sp K).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom, RingHom.injective _, fun _ => gs_eq (𝟙 _) z ⊤ trivial _⟩`.
-/
theorem exists_cst {K : Type} [Field K] (z : Sp K) : ∃ c : K →+* (Sp K).presheaf.stalk z, Function.Injective c ∧
    ∀ a, gs (𝟙 (Sp K)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a) = c a :=
  ⟨((Sp K).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom, RingHom.injective _,
    fun _ => gs_eq (𝟙 _) z ⊤ trivial _⟩

/- English proof (translation)
Take `⟨P₀, f, f', -, gp, gp', lb, lb', -, hw⟩` from `h`. Use `choose w hw hw' using hw`. Establish `hs : ∀ x, w x ≫ P₀.A.hom = 𝟙 _` using `fun x => by`. Establish `e : (w x ≫ P₀.A.hom) ≫ spMap S'.R.val.toRingHom = 𝟙 _ ≫ spMap S'.R.val.toRingHom`. Rewrite using `[Category.assoc, ← gp'.1.w, ← Category.assoc, hw', Category.assoc, Over.w, Category.id_comp]`.

Conclude with `Category.comp_id _`. Use `haveI : IsFractionRing S'.R Ω' := IsFractionRing.of_field _ _ fun x => by`. Take `⟨a, ha, b, hb, e⟩` from `S'.frac x`. Conclude with `⟨⟨a, ha⟩, ⟨b, hb⟩, e⟩`. Use `haveI : IsPreimmersion (spMap S'.R.val.toRingHom) := IsPreimmersion.of_isLocalization (R := S'.R) (S := Ω') (nonZeroDivisors S'.R)`.

Conclude with `(cancel_mono _).1 e`. Set `x : S.Gam → (baseOver (Sp Ω') ⟶ P₀.A)` to `fun a => Over.homMk (w a) (hs a)`. Take `⟨rig, τ, -, hτ, ht⟩` from `FrameMove.exists_move (T := baseOver (Sp S.R)) (T' := baseOver (Sp Ω')) (h := spMap (φ.comp S.R.val.toRingHom)) gp lb ((Category.comp_id _).trans (Category.id_comp _).symm) ρ.rig_gen (x := ρ.pt) (x' := x) hw ρ.fr_tors`. Take `⟨rig', τ', -, hτ', ht'⟩` from `FrameMove.exists_move (T := baseOver (Sp S'.R)) (T' := baseOver (Sp Ω')) (h := spMap S'.R.val.toRingHom) gp' lb' ((Category.comp_id _).trans (Category.id_comp _).symm) ρ'.rig_gen (x := fun a => ρ'.pt (lab a)) (x' := x) hw' (fun a => ρ'.fr_tors (lab a))`. Take `⟨t, ht⟩` from `ht 1 ρ.th₁`.

Take `⟨t', ht'⟩` from `ht' 1 ρ'.th₁`. Set `z : Sp Ω'` to `IsLocalRing.closedPoint Ω'`. Take `⟨V, hV, hθ⟩` from `GlobalTheory.EmbLocal.exists_isGenSec_near GlobalTheory.abelianSchemeLaws_all.2.secBaseChangeAny P₀ z`. Take `⟨θ, hθ⟩` from `hθ Ω' (𝟙 _) (by rintro _ ⟨v, rfl⟩; rw [Subsingleton.elim v z]; exact hV)`. Take `⟨r, hr⟩` from `hθ t`.

Take `⟨r', hr'⟩` from `hθ t'`. Take `⟨J, hJ⟩` from `ConstFam.exists_good' (Z := (baseOver (Sp Ω')).left) P₀.isLB z`. Take `⟨c, hc, hcv⟩ : ∃ c : Ω' →+* (baseOver (Sp Ω')).left.presheaf.stalk z, Function.Injective c ∧ ∀ a, gs (𝟙 (Sp Ω')) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of Ω')).inv.hom a) = c a` from `exists_cst z`. Establish `pf : ∀ {B : Scheme.{0}} {A T : Over B} {L : LB A.left} (x : T ⟶ A) (τ : LB.Gen (LB.LinComb L (Y` using `T.left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))), powFrame A L x τ 1 = τ := fun x τ => congrArg LB.Gen.mk (funext fun j => zpow_one (τ.s j))`. Establish `v : ∀ a, gs (𝟙 (baseOver (Sp Ω')).left) z ⊤ r * sval (L` using `P₀.L) (φ := fun _ : Fin 1 => (snd (baseOver (Sp Ω')) P₀.A).left) (ε := fun _ => 1) θ (ptSecT P₀.A (x a)).left z J = c (φ (S.th a)) * (val (τ a) (𝟙 _) z J).val := fun a => by`.

Establish `e` using `(sval_smul hr (x a) hJ).symm.trans (ht a _ (by rw [pf]; exact ρ.th_val a) z J hJ)`. Rewrite `e` using `[pf]`. Conclude with `e.trans (congrArg (· * _) ((FrameMove.gs_spMap _ z _).trans (hcv _)))`. Establish `v' : ∀ a, gs (𝟙 (baseOver (Sp Ω')).left) z ⊤ r' * sval (L` using `P₀.L) (φ := fun _ : Fin 1 => (snd (baseOver (Sp Ω')) P₀.A).left) (ε := fun _ => 1) θ (ptSecT P₀.A (x a)).left z J = c (S'.th (lab a)) * (val (τ' a) (𝟙 _) z J).val := fun a => by`. Establish `e` using `(sval_smul hr' (x a) hJ).symm.trans (ht' a _ (by rw [pf]; exact ρ'.th_val (lab a)) z J hJ)`.

Rewrite `e` using `[pf]`. Conclude with `e.trans (congrArg (· * _) ((FrameMove.gs_spMap _ z _).trans (hcv _)))`. Establish `q` using `(torsFrame_two_levels P₀ (hτ a) (hτ' a) hJ).trans (torsFrame_two_levels P₀ (hτ b) (hτ' b) hJ).symm`. Establish `p₁ : 0 < S.r * S.N` using `Nat.mul_pos S.r_pos (by have := S.N_ge; omega)`. Establish `p₂ : 0 < S'.r * S'.N` using `Nat.mul_pos S'.r_pos (by have := S'.N_ge; omega)`.

Use `⟨(S.r * S.N) ^ 2 * (S'.r * S'.N) ^ 2, by positivity, hc ?_⟩` and prove the remaining obligations. Generalize the expression as in `(S.r * S.N) ^ 2 * (S'.r * S'.N) ^ 2 = k at q`. Establish `va` using `v a`. Establish `vb` using `v b`. Establish `va'` using `v' a`.

Establish `vb'` using `v' b`. Generalize the expression as in `val (τ a) (𝟙 _) z J = ua at *`. Generalize the expression as in `val (τ b) (𝟙 _) z J = ub at *`. Generalize the expression as in `val (τ' a) (𝟙 _) z J = ua' at *`. Generalize the expression as in `val (τ' b) (𝟙 _) z J = ub' at *`.

Establish `e : c (S'.th (lab a) * φ (S.th b)) * (ua' * ub).val = c (S'.th (lab b) * φ (S.th a)) * (ub' * ua).val`. Rewrite using `[map_mul, map_mul, Units.val_mul, Units.val_mul, _root_.mul_mul_mul_comm, ← va', ← vb, _root_.mul_mul_mul_comm (c _), ← vb', ← va]`. Expand and normalize the polynomial expressions, which then agree. Establish `q' : (ua' * ub) ^ k = (ub' * ua) ^ k`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Use `replace q := congrArg Additive.ofMul q`. Simplify using `only [ofMul_mul, ofMul_pow, ofMul_div] at q ⊢`. Take the linear combination `(norm := module) -q`. Establish `e'` using `congrArg (· ^ k) e`. Simplify using `only [mul_pow, ← Units.val_pow_eq_pow_val, q'] at e'`.

Rewrite using `[map_pow, map_pow]`. Conclude with `(Units.mul_left_inj _).1 e'`.
-/
theorem same_ratio {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω']
    {S : ThetaSys o Ω} {S' : ThetaSys o' Ω'} {ρ : S.Real} {ε} {ρ' : S'.Real} {ε'} {lab : S.Gam → S'.Gam} {φ : Ω →+* Ω'}
    (h : Same ρ ε ρ' ε' lab φ) (a b : S.Gam) :
    ∃ k, 0 < k ∧ (S'.th (lab a) * φ (S.th b)) ^ k = (S'.th (lab b) * φ (S.th a)) ^ k := by
  obtain ⟨P₀, f, f', -, gp, gp', lb, lb', -, hw⟩ := h
  choose w hw hw' using hw
  have hs : ∀ x, w x ≫ P₀.A.hom = 𝟙 _ := fun x => by
    have e : (w x ≫ P₀.A.hom) ≫ spMap S'.R.val.toRingHom = 𝟙 _ ≫ spMap S'.R.val.toRingHom := by
      rw [Category.assoc, ← gp'.1.w, ← Category.assoc, hw', Category.assoc, Over.w, Category.id_comp]
      exact Category.comp_id _
    haveI : IsFractionRing S'.R Ω' := IsFractionRing.of_field _ _ fun x => by
      obtain ⟨a, ha, b, hb, e⟩ := S'.frac x
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩, e⟩
    haveI : IsPreimmersion (spMap S'.R.val.toRingHom) :=
      IsPreimmersion.of_isLocalization (R := S'.R) (S := Ω') (nonZeroDivisors S'.R)
    exact (cancel_mono _).1 e
  let x : S.Gam → (baseOver (Sp Ω') ⟶ P₀.A) := fun a => Over.homMk (w a) (hs a)
  obtain ⟨rig, τ, -, hτ, ht⟩ := FrameMove.exists_move (T := baseOver (Sp S.R)) (T' := baseOver (Sp Ω'))
    (h := spMap (φ.comp S.R.val.toRingHom)) gp lb ((Category.comp_id _).trans (Category.id_comp _).symm) ρ.rig_gen
    (x := ρ.pt) (x' := x) hw ρ.fr_tors
  obtain ⟨rig', τ', -, hτ', ht'⟩ := FrameMove.exists_move (T := baseOver (Sp S'.R)) (T' := baseOver (Sp Ω'))
    (h := spMap S'.R.val.toRingHom) gp' lb' ((Category.comp_id _).trans (Category.id_comp _).symm) ρ'.rig_gen
    (x := fun a => ρ'.pt (lab a)) (x' := x) hw' (fun a => ρ'.fr_tors (lab a))
  obtain ⟨t, ht⟩ := ht 1 ρ.th₁
  obtain ⟨t', ht'⟩ := ht' 1 ρ'.th₁
  let z : Sp Ω' := IsLocalRing.closedPoint Ω'
  obtain ⟨V, hV, hθ⟩ := GlobalTheory.EmbLocal.exists_isGenSec_near GlobalTheory.abelianSchemeLaws_all.2.secBaseChangeAny P₀ z
  obtain ⟨θ, hθ⟩ := hθ Ω' (𝟙 _) (by rintro _ ⟨v, rfl⟩; rw [Subsingleton.elim v z]; exact hV)
  obtain ⟨r, hr⟩ := hθ t
  obtain ⟨r', hr'⟩ := hθ t'
  obtain ⟨J, hJ⟩ := ConstFam.exists_good' (Z := (baseOver (Sp Ω')).left) P₀.isLB z
  obtain ⟨c, hc, hcv⟩ : ∃ c : Ω' →+* (baseOver (Sp Ω')).left.presheaf.stalk z, Function.Injective c ∧
      ∀ a, gs (𝟙 (Sp Ω')) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of Ω')).inv.hom a) = c a := exists_cst z
  have pf : ∀ {B : Scheme.{0}} {A T : Over B} {L : LB A.left} (x : T ⟶ A)
      (τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))),
      powFrame A L x τ 1 = τ := fun x τ => congrArg LB.Gen.mk (funext fun j => zpow_one (τ.s j))
  have v : ∀ a, gs (𝟙 (baseOver (Sp Ω')).left) z ⊤ r * sval (L := P₀.L) (φ := fun _ : Fin 1 => (snd (baseOver (Sp Ω')) P₀.A).left)
      (ε := fun _ => 1) θ (ptSecT P₀.A (x a)).left z J = c (φ (S.th a)) * (val (τ a) (𝟙 _) z J).val := fun a => by
    have e := (sval_smul hr (x a) hJ).symm.trans (ht a _ (by rw [pf]; exact ρ.th_val a) z J hJ)
    rw [pf] at e
    exact e.trans (congrArg (· * _) ((FrameMove.gs_spMap _ z _).trans (hcv _)))
  have v' : ∀ a, gs (𝟙 (baseOver (Sp Ω')).left) z ⊤ r' * sval (L := P₀.L) (φ := fun _ : Fin 1 => (snd (baseOver (Sp Ω')) P₀.A).left)
      (ε := fun _ => 1) θ (ptSecT P₀.A (x a)).left z J = c (S'.th (lab a)) * (val (τ' a) (𝟙 _) z J).val := fun a => by
    have e := (sval_smul hr' (x a) hJ).symm.trans (ht' a _ (by rw [pf]; exact ρ'.th_val (lab a)) z J hJ)
    rw [pf] at e
    exact e.trans (congrArg (· * _) ((FrameMove.gs_spMap _ z _).trans (hcv _)))
  have q := (torsFrame_two_levels P₀ (hτ a) (hτ' a) hJ).trans (torsFrame_two_levels P₀ (hτ b) (hτ' b) hJ).symm
  have p₁ : 0 < S.r * S.N := Nat.mul_pos S.r_pos (by have := S.N_ge; omega)
  have p₂ : 0 < S'.r * S'.N := Nat.mul_pos S'.r_pos (by have := S'.N_ge; omega)
  refine ⟨(S.r * S.N) ^ 2 * (S'.r * S'.N) ^ 2, by positivity, hc ?_⟩
  generalize (S.r * S.N) ^ 2 * (S'.r * S'.N) ^ 2 = k at q
  have va := v a
  have vb := v b
  have va' := v' a
  have vb' := v' b
  generalize val (τ a) (𝟙 _) z J = ua at *
  generalize val (τ b) (𝟙 _) z J = ub at *
  generalize val (τ' a) (𝟙 _) z J = ua' at *
  generalize val (τ' b) (𝟙 _) z J = ub' at *
  have e : c (S'.th (lab a) * φ (S.th b)) * (ua' * ub).val = c (S'.th (lab b) * φ (S.th a)) * (ub' * ua).val := by
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, _root_.mul_mul_mul_comm, ← va', ← vb, _root_.mul_mul_mul_comm (c _), ← vb', ← va]
    ring
  have q' : (ua' * ub) ^ k = (ub' * ua) ^ k := by
    apply Additive.ofMul.injective
    replace q := congrArg Additive.ofMul q
    simp only [ofMul_mul, ofMul_pow, ofMul_div] at q ⊢
    linear_combination (norm := module) -q
  have e' := congrArg (· ^ k) e
  simp only [mul_pow, ← Units.val_pow_eq_pow_val, q'] at e'
  rw [map_pow, map_pow]
  exact (Units.mul_left_inj _).1 e'

end GlobalTheory.Poinc.DivDeep
