import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RatTors
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescOfPoints
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

namespace GlobalTheory.FitMatch
open GlobalTheory.ArcPull GlobalTheory.ArcDataDescent

section General
variable {F F' : Type} [Field F] [Field F'] {B B₀ Y Y₀ : Scheme.{0}} {M : LB B} {M₀ : LB B₀} {φ : B ⟶ B₀}

/- English proof (translation)
Take `rfl : (fun k => pt k ≫ φ) = pt₀` from `funext hp`. Use `(genRel_iff w t t₀ x z).2 ⟨hp, fun j j₀ h₀ h₁ => ?_⟩` and prove the remaining obligations. Rewrite `H` using `[val_of t _ z J' (fun k => J' (pt k)) (fun k => by rw [Category.id_comp]), val_of t₀ _ z J (fun k => J (pt k ≫ φ)) (fun k => by rw [Category.id_comp])]`. Establish `m₀ : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M₀ (fun k => pt k ≫ φ) j₀` using `Set.mem_iInter.2 h₀`. Establish `m₁ : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M pt j` using `Set.mem_iInter.2 h₁`.

Establish `n₀ : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M₀ (fun k => pt k ≫ φ) (fun k => J (pt k ≫ φ))` using `Set.mem_iInter.2 fun k => hJ (pt k ≫ φ)`. Establish `n₁ : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M pt (fun k => J' (pt k))` using `Set.mem_iInter.2 fun k => hJ' (pt k)`. Establish `a` using `pw_trans ((isGen_iff w).1 hw) pt ε (𝟙 _) z m₀ n₀ m₁ n₁`. Simplify using `only [pw, Category.id_comp] at a`. Establish `key : (∏ k, Geo.Tor.gw w (pt k) z (j₀ k) (j k) ^ ε k) * gm (𝟙 _) z (LB.wchart M pt j) (t.s j) = Units.map (toStk z).toMonoidHom x * gm (𝟙 _) z (LB.wchart M₀ (fun k => pt k ≫ φ) j₀) (t₀.s j₀)`.

Rewrite using `[a, gen_trans ht (𝟙 _) z m₁ n₁, gen_trans ht₀ (𝟙 _) z m₀ n₀]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Establish `e'` using `congrArg Additive.ofMul H`. Simplify using `only [om, ofMul_mul, ofMul_inv] at e' ⊢`. Take the linear combination `(norm := abel) e'`.

Conclude with `congrArg Units.val key`.
-/
theorem genRel_of_gauge {w : LB.Iso M (M₀.pull φ)} (hw : w.IsGen) {K : Type} [Fintype K] {pt : K → (Sp F ⟶ B)}
    {pt₀ : K → (Sp F ⟶ B₀)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb M pt ε)} {t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)}
    (ht : t.IsGen) (ht₀ : t₀.IsGen) (x : Fˣ) (hp : ∀ k, pt k ≫ φ = pt₀ k) (z : Sp F) {J J'} (hJ : Good M₀ z J)
    (hJ' : Good M z J')
    (H : (∏ k, om w z J J' (pt k) ^ ε k) * val t (𝟙 _) z J' = Units.map (toStk z).toMonoidHom x * val t₀ (𝟙 _) z J) :
    GenRel w t t₀ (x : F) := by
  obtain rfl : (fun k => pt k ≫ φ) = pt₀ := funext hp
  refine (genRel_iff w t t₀ x z).2 ⟨hp, fun j j₀ h₀ h₁ => ?_⟩
  rw [val_of t _ z J' (fun k => J' (pt k)) (fun k => by rw [Category.id_comp]),
    val_of t₀ _ z J (fun k => J (pt k ≫ φ)) (fun k => by rw [Category.id_comp])] at H
  have m₀ : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M₀ (fun k => pt k ≫ φ) j₀ := Set.mem_iInter.2 h₀
  have m₁ : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M pt j := Set.mem_iInter.2 h₁
  have n₀ : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M₀ (fun k => pt k ≫ φ) (fun k => J (pt k ≫ φ)) :=
    Set.mem_iInter.2 fun k => hJ (pt k ≫ φ)
  have n₁ : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M pt (fun k => J' (pt k)) :=
    Set.mem_iInter.2 fun k => hJ' (pt k)
  have a := pw_trans ((isGen_iff w).1 hw) pt ε (𝟙 _) z m₀ n₀ m₁ n₁
  simp only [pw, Category.id_comp] at a
  have key : (∏ k, Geo.Tor.gw w (pt k) z (j₀ k) (j k) ^ ε k) * gm (𝟙 _) z (LB.wchart M pt j) (t.s j) =
      Units.map (toStk z).toMonoidHom x * gm (𝟙 _) z (LB.wchart M₀ (fun k => pt k ≫ φ) j₀) (t₀.s j₀) := by
    rw [a, gen_trans ht (𝟙 _) z m₁ n₁, gen_trans ht₀ (𝟙 _) z m₀ n₀]
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul H
    simp only [om, ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'
  exact congrArg Units.val key

/- English proof (translation)
Substitute `h h₀` using the available equality. Use `Iff.trans ?_ (genRel_pull_iff σ w (LB.pullGen _ _ _ t r) (LB.pullGen _ _ _ t₀ r₀) x)` and prove the remaining obligations. Establish `p : (fun k => (spMap σ ≫ r) ≫ pt k) = fun k => spMap σ ≫ r ≫ pt k` using `funext fun _ => Category.assoc _ _ _`. Establish `p₀ : (fun k => (spMap σ ≫ r₀) ≫ pt₀ k) = fun k => spMap σ ≫ r₀ ≫ pt₀ k` using `funext fun _ => Category.assoc _ _ _`. Apply the tactic sequence `refine genRel_congr hM hM₀ w p p₀ (t := LB.pullGen _ _ _ t (spMap σ ≫ r)) (t' := LB.pullGen _ _ _ (LB.pullGen _ _ _ t r) (spMap σ)) (t₀ := LB.pullGen _ _ _ t₀ (spMap σ ≫ r₀)) (t₀' := LB.pullGen _ _ _ (LB.pullGen _ _ _ t₀ r₀) (spMap σ)) (DVR.pullGen_isGen _ _ _ _ ht _) (DVR.pullGe …`.

Rewrite using `[val_pull hJ, val_pull hJ, val_pull hJ, Category.assoc]`.
-/
theorem genRel_ext_iff (hM : M.IsLB) (hM₀ : M₀.IsLB) (w : LB.Iso M (M₀.pull φ)) {K : Type} [Fintype K]
    {pt : K → (Y ⟶ B)} {pt₀ : K → (Y₀ ⟶ B₀)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb M pt ε)}
    {t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)} (ht : t.IsGen) (ht₀ : t₀.IsGen) (σ : F →+* F') (r : Sp F ⟶ Y) (r₀ : Sp F ⟶ Y₀)
    {s : Sp F' ⟶ Y} {s₀ : Sp F' ⟶ Y₀} (h : s = spMap σ ≫ r) (h₀ : s₀ = spMap σ ≫ r₀) (x : F) :
    GenRel w (LB.pullGen _ _ _ t s) (LB.pullGen _ _ _ t₀ s₀) (σ x) ↔
      GenRel w (LB.pullGen _ _ _ t r) (LB.pullGen _ _ _ t₀ r₀) x := by
  subst h h₀
  refine Iff.trans ?_ (genRel_pull_iff σ w (LB.pullGen _ _ _ t r) (LB.pullGen _ _ _ t₀ r₀) x)
  have p : (fun k => (spMap σ ≫ r) ≫ pt k) = fun k => spMap σ ≫ r ≫ pt k := funext fun _ => Category.assoc _ _ _
  have p₀ : (fun k => (spMap σ ≫ r₀) ≫ pt₀ k) = fun k => spMap σ ≫ r₀ ≫ pt₀ k := funext fun _ => Category.assoc _ _ _
  refine genRel_congr hM hM₀ w p p₀ (t := LB.pullGen _ _ _ t (spMap σ ≫ r))
    (t' := LB.pullGen _ _ _ (LB.pullGen _ _ _ t r) (spMap σ)) (t₀ := LB.pullGen _ _ _ t₀ (spMap σ ≫ r₀))
    (t₀' := LB.pullGen _ _ _ (LB.pullGen _ _ _ t₀ r₀) (spMap σ))
    (DVR.pullGen_isGen _ _ _ _ ht _) (DVR.pullGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _) _)
    (DVR.pullGen_isGen _ _ _ _ ht₀ _) (DVR.pullGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht₀ _) _)
    (fun y J hJ => ?_) (fun y J hJ => ?_) _ <;>
  rw [val_pull hJ, val_pull hJ, val_pull hJ, Category.assoc]

/- English proof (translation)
The claim follows from `toStk_valF r _ z (hJ.mem pt r) _`.
-/
theorem toStk_vF {K : Type} [Fintype K] {pt : K → (Y ⟶ B)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb M pt ε)) (r : Sp F ⟶ Y)
    {z : Sp F} {J} (hJ : Good M z J) : toStk z (vF t r J) = (val t r z J).val :=
  toStk_valF r _ z (hJ.mem pt r) _
end General

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {D : DegPre R} {D' : DegPre R'}
  {f : R →+* R'} {C : Type} [Field C] [Algebra (FractionRing R) C] [Algebra (FractionRing R') C]

/- English proof (translation)
The claim follows from `(congrArg (· ≫ spMap f) (Geo.Tor.spMap_comp _ _).symm).trans ((Geo.Tor.spMap_comp _ _).symm.trans ((congrArg spMap (RingHom.ext fun x => hf x)).trans (Geo.Tor.spMap_comp _ _)))`.
-/
theorem tf_comp (hf : Along f C) : (TF (R := R') C).hom ≫ spMap f = (TF (R := R) C).hom :=
  (congrArg (· ≫ spMap f) (Geo.Tor.spMap_comp _ _).symm).trans ((Geo.Tor.spMap_comp _ _).symm.trans
    ((congrArg spMap (RingHom.ext fun x => hf x)).trans (Geo.Tor.spMap_comp _ _)))

/- English proof (translation)
Use `D.P.isAb.proper` as an intermediate fact. Set `g : R' →+* C` to `(algebraMap (FractionRing R') C).comp (algebraMap R' _)`. Establish `hg : Function.Injective g` using `(algebraMap (FractionRing R') C).injective.comp (IsFractionRing.injective _ _)`. Establish `e : spMap g = (TF (R` using `R') C).hom := Geo.Tor.spMap_comp _ _`. Use `ext_of_injective hg (X := Sp R') (π := spMap g) (p := 𝟙 _) (p' := 𝟙 _) (IsPullback.of_vert_isIso ⟨by simp⟩) D.P.A.hom ?_ ?_` and prove the remaining obligations.

Rewrite using `[Category.assoc, gp.1.w, ← Category.assoc, Over.w, Category.assoc]`. Conclude with `(Category.id_comp _).trans ((Category.comp_id _).symm.trans (congrArg _ (Over.w (D.c y)).symm))`. Rewrite using `[e, ← Category.assoc _ (spMap f), tf_comp hf, ← Category.assoc]`. Conclude with `h`.
-/
theorem c_of_field (hf : Along f C) {ψ : D'.P.A.left ⟶ D.P.A.left} (gp : IsGrpPullback D'.P.A D.P.A (spMap f) ψ)
    (x : D'.X) (y : D.X) (h : (DegPre.cF D' C x).left ≫ ψ = (DegPre.cF D C y).left) :
    (D'.c x).left ≫ ψ = spMap f ≫ (D.c y).left := by
  have := D.P.isAb.proper
  let g : R' →+* C := (algebraMap (FractionRing R') C).comp (algebraMap R' _)
  have hg : Function.Injective g := (algebraMap (FractionRing R') C).injective.comp (IsFractionRing.injective _ _)
  have e : spMap g = (TF (R := R') C).hom := Geo.Tor.spMap_comp _ _
  refine ext_of_injective hg (X := Sp R') (π := spMap g) (p := 𝟙 _) (p' := 𝟙 _) (IsPullback.of_vert_isIso ⟨by simp⟩)
    D.P.A.hom ?_ ?_
  · rw [Category.assoc, gp.1.w, ← Category.assoc, Over.w, Category.assoc]
    exact (Category.id_comp _).trans ((Category.comp_id _).symm.trans (congrArg _ (Over.w (D.c y)).symm))
  · rw [e, ← Category.assoc _ (spMap f), tf_comp hf, ← Category.assoc]
    exact h

/- English proof (translation)
Establish `z : Sp C` using `(default : PrimeSpectrum C)`. Establish `hJ : Good D.P.L z ν.J` using `fun p => (top_le_iff_mem _ _ z).1 (ν.good p)`. Establish `hJ' : Good D'.P.L z ν'.J` using `fun p => (top_le_iff_mem _ _ z).1 (ν'.good p)`. Establish `hv : ∀ a, toStk z (wVal ν' ν w a) = (om w z ν.J ν'.J (ν'.eA a).left).val` using `fun a => toStk_valF _ ((D.P.L.pull ψ).U (fun _ => ν.J ((ν'.eA a).left ≫ ψ)) ⊓ D'.P.L.U (ν'.J (ν'.eA a).left)) z ⟨mem_pull.2 (hJ ((ν'.eA a).left ≫ ψ)), hJ' _⟩ _`. Establish `c₀ : ∀ a, (DegPre.cF D C a).left = jFK (R` using `R) C ≫ D.xK a := fun a => Category.assoc _ _ _`.

Establish `c₁ : ∀ a, (DegPre.cF D' C a).left = jFK (R` using `R') C ≫ D'.xK a := fun a => Category.assoc _ _ _`. Establish `pm` using `(maps_iff w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (spMap f) _ (rigPull_le ψ (spMap f) he D.P.L) (fun _ => rfl)).1 hr`. Establish `e` using `pmaps_om (fun _ => he) pm (TF (R := R') C).hom z hJ hJ'`. Rewrite `e` using `[Fintype.prod_unique, zpow_one]`. Use `replace e := (congrArg (fun q => val D.rig q z ν.J) (tf_comp hf).symm).trans e`.

Establish `a₀` using `(congrArg (toStk z) (ν.ψ_eq y)).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) (toStk_vF _ _ hJ) ((toStk_vF _ _ hJ).trans (congrArg Units.val e))))`. Establish `a₁` using `(congrArg (toStk z) (ν'.ψ_eq x)).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) (toStk_vF _ _ hJ') (toStk_vF _ _ hJ')))`. Establish `a₂` using `congrArg (toStk z) hh`. Rewrite `a₂` using `[map_mul, hv, hv, ν'.c_eq, c₁, map_one]`. Set `U` to `Units.map (toStk z).toMonoidHom`.

Establish `b₀ : U (N.ψ y) = _ * (_ * _)` using `Units.ext a₀`. Establish `b₁ : U (N'.ψ x) = _ * _` using `Units.ext a₁`. Establish `b₂ : U h * _ = om w z ν.J ν'.J ((TF (R` using `R') C).hom ≫ eSec D'.P.A) := Units.ext a₂`. Establish `b₃` using `congrArg U hψ`. Rewrite `b₃` using `[map_mul, map_mul, b₀, b₁, ← b₂]`.

Use `genRel_of_gauge hw (DVR.pullGen_isGen _ _ _ _ (D'.psi_gen _) _) (DVR.pullGen_isGen _ _ _ _ (D.psi_gen _) _) s (fun _ => (congrArg (· ≫ ψ) (c₁ _).symm).trans (hc.trans (c₀ _))) z hJ hJ' ?_` and prove the remaining obligations. Rewrite using `[Fintype.prod_unique, val_pull hJ, val_pull hJ', Category.id_comp, Category.id_comp, zpow_neg_one]`. Establish `e'` using `congrArg Additive.ofMul b₃`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [U, ofMul_mul, ofMul_inv] at e' ⊢`.

Take the linear combination `(norm := abel) e'`.
-/
theorem genRel_field (hf : Along f C) {N N' : NumD C} (ν : NumOf D C N) (ν' : NumOf D' C N')
    {ψ : D'.P.A.left ⟶ D.P.A.left} (he : eSec D'.P.A ≫ ψ = spMap f ≫ eSec D.P.A) {w : LB.Iso D'.P.L (D.P.L.pull ψ)}
    (hw : w.IsGen) (hr : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => 1)) D'.rig
      (rigPullOf ψ (spMap f) he D.P.L D.rig)) (x : N'.X) (y : N.X) (h s : Cˣ)
    (hc : (DegPre.cF D' C (ν'.eX x)).left ≫ ψ = (DegPre.cF D C (ν.eX y)).left)
    (hψ : N'.ψ x * h = N.ψ y * s) (hh : (h : C) * wVal ν' ν w (N'.c x) = wVal ν' ν w 1) :
    GenRel w (LB.pullGen _ _ _ (D'.psi (ν'.eX x)) (jFK (R := R') C)) (LB.pullGen _ _ _ (D.psi (ν.eX y)) (jFK (R := R) C))
      (s : C) := by
  have z : Sp C := (default : PrimeSpectrum C)
  have hJ : Good D.P.L z ν.J := fun p => (top_le_iff_mem _ _ z).1 (ν.good p)
  have hJ' : Good D'.P.L z ν'.J := fun p => (top_le_iff_mem _ _ z).1 (ν'.good p)
  have hv : ∀ a, toStk z (wVal ν' ν w a) = (om w z ν.J ν'.J (ν'.eA a).left).val := fun a =>
    toStk_valF _ ((D.P.L.pull ψ).U (fun _ => ν.J ((ν'.eA a).left ≫ ψ)) ⊓ D'.P.L.U (ν'.J (ν'.eA a).left)) z
      ⟨mem_pull.2 (hJ ((ν'.eA a).left ≫ ψ)), hJ' _⟩ _
  have c₀ : ∀ a, (DegPre.cF D C a).left = jFK (R := R) C ≫ D.xK a := fun a => Category.assoc _ _ _
  have c₁ : ∀ a, (DegPre.cF D' C a).left = jFK (R := R') C ≫ D'.xK a := fun a => Category.assoc _ _ _
  have pm := (maps_iff w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (spMap f) _
    (rigPull_le ψ (spMap f) he D.P.L) (fun _ => rfl)).1 hr
  have e := pmaps_om (fun _ => he) pm (TF (R := R') C).hom z hJ hJ'
  rw [Fintype.prod_unique, zpow_one] at e
  replace e := (congrArg (fun q => val D.rig q z ν.J) (tf_comp hf).symm).trans e
  have a₀ := (congrArg (toStk z) (ν.ψ_eq y)).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (toStk_vF _ _ hJ) ((toStk_vF _ _ hJ).trans (congrArg Units.val e))))
  have a₁ := (congrArg (toStk z) (ν'.ψ_eq x)).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (toStk_vF _ _ hJ') (toStk_vF _ _ hJ')))
  have a₂ := congrArg (toStk z) hh
  rw [map_mul, hv, hv, ν'.c_eq, c₁, map_one] at a₂
  let U := Units.map (toStk z).toMonoidHom
  have b₀ : U (N.ψ y) = _ * (_ * _) := Units.ext a₀
  have b₁ : U (N'.ψ x) = _ * _ := Units.ext a₁
  have b₂ : U h * _ = om w z ν.J ν'.J ((TF (R := R') C).hom ≫ eSec D'.P.A) := Units.ext a₂
  have b₃ := congrArg U hψ
  rw [map_mul, map_mul, b₀, b₁, ← b₂] at b₃
  refine genRel_of_gauge hw (DVR.pullGen_isGen _ _ _ _ (D'.psi_gen _) _) (DVR.pullGen_isGen _ _ _ _ (D.psi_gen _) _) s
    (fun _ => (congrArg (· ≫ ψ) (c₁ _).symm).trans (hc.trans (c₀ _))) z hJ hJ' ?_
  rw [Fintype.prod_unique, val_pull hJ, val_pull hJ', Category.id_comp, Category.id_comp, zpow_neg_one]
  have e' := congrArg Additive.ofMul b₃
  apply Additive.ofMul.injective
  simp only [U, ofMul_mul, ofMul_inv] at e' ⊢
  linear_combination (norm := abel) e'

/- English proof (translation)
Introduce `_ E _ _ _ H D l c O _ β O' _ _ _ b a C _ _ _ _ _ _ A u r o M f N' ν' J _ hf u₀ hu ψ he w e ⟨gp, hw, hp, hx, _, hh⟩ hr ha`. Establish `hc : ∀ χ : A.N.X, (DegPre.cF M.P.D.toPre C (ν'.eX (J.e χ))).left ≫ ψ = (DegPre.cF a.D₀ C (A.ν.eX χ)).left` using `fun χ => by`. Rewrite using `[← ν'.c_eq, ← A.ν.c_eq]`. Conclude with `(congrArg (fun q => (ν'.eA q).left ≫ ψ) (J.c_eq χ)).trans (hp _)`. Establish `inj : Function.Injective f` using `fun x y h => IsFractionRing.injective O' (FractionRing O') ((algebraMap (FractionRing O') C).injective ((hf x).symm.trans (by rw [h]; exact hf y)))`.

Use `⟨gp, hw, hr, ha, fun y => ?_, fun F _ _ _ _ uF hF huF y => ?_⟩` and prove the remaining obligations. Take `⟨χ, rfl⟩` from `A.ν.eX.surjective y`. Rewrite using `[hx]`. Conclude with `c_of_field hf gp _ _ (hc χ)`. Take `⟨χ, rfl⟩` from `A.ν.eX.surjective y`.

Establish `k` using `genRel_field hf A.ν ν' he hw hr (J.e χ) χ (J.h (A.N.c χ)) (u ^ (A.be.be χ χ / 2)) (hc χ) (J.ψ_eq χ) ((congrArg (fun q => (J.h (A.N.c χ) : C) * wVal ν' A.ν w q) (J.c_eq χ)).trans (hh _))`. Establish `lift : ∀ (L : Type) [Field L] [Algebra (FractionRing M.W) L] [Algebra (FractionRing O') L], Along f L → jFK (R` using `O') L = spMap (algebraMap (FractionRing M.W) L) ≫ genMap inj := fun L _ _ _ h => (congrArg spMap (IsLocalization.ringHom_ext (nonZeroDivisors O') (RingHom.ext fun x => (h x).symm.trans (congrArg (algebraMap (FractionRing M.W) L) (fracMap_algebraMap inj x).symm)))).trans (Geo.Tor. …`. Establish `t` using `fun (L : Type) [Field L] [Algebra (FractionRing M.W) L] [Algebra (FractionRing O') L] (h : Along f L) => genRel_ext_iff M.P.D.toPre.P.isLB a.D₀.P.isLB w (M.P.D.toPre.psi_gen (ν'.eX (J.e χ))) (a.D₀.psi_gen (A.ν.eX χ)) (algebraMap (FractionRing M.W) L) (𝟙 _) (genMap inj) (s := jFK …`. Rewrite `k` using `[Units.val_zpow_eq_zpow_val, hu, ← map_zpow₀]`. Establish `k'` using `(t F fun x => (hF x).symm).2 ((t C hf).1 k)`.

Rewrite using `[hx, huF, ← A.be_eq, ← map_zpow₀]`. Conclude with `k'`.
-/
theorem match_of_fit : GlobalTheory.UT.LL → AllS fun {_} _ _ _ {H} {_} {_} {_} {_} _ {_} {_} _ _ {_} a {C} _ _ A u _ {_} M f {_} ν' J => ∀ u₀ : M.W, (u : C) = algebraMap (FractionRing M.W) C (algebraMap _ _ u₀) → ∀ ψ (he : eSec M.P.D.toPre.P.A ≫ ψ = spMap f ≫ eSec a.D₀.P.A) w e, Fit A u M f ν' J ψ w e → LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec M.P.D.toPre.P.A) (fun _ => 1)) M.P.D.toPre.rig (rigPullOf ψ (spMap f) he a.D₀.P.L a.D₀.rig) → (letI := H.starRing; ∀ x, (M.P.oD.onB.act x).left ≫ ψ = ψ ≫ (a.oa.onB.act x).left) → GlobalTheory.LN.Match a f u₀ M.P.D.toPre M.P.oD ψ he w e := by
  intro _ E _ _ _ H D l c O _ β O' _ _ _ b a C _ _ _ _ _ _ A u r o M f N' ν' J _ hf u₀ hu ψ he w e
    ⟨gp, hw, hp, hx, _, hh⟩ hr ha
  have hc : ∀ χ : A.N.X, (DegPre.cF M.P.D.toPre C (ν'.eX (J.e χ))).left ≫ ψ = (DegPre.cF a.D₀ C (A.ν.eX χ)).left :=
    fun χ => by
      rw [← ν'.c_eq, ← A.ν.c_eq]
      exact (congrArg (fun q => (ν'.eA q).left ≫ ψ) (J.c_eq χ)).trans (hp _)
  have inj : Function.Injective f := fun x y h => IsFractionRing.injective O' (FractionRing O')
    ((algebraMap (FractionRing O') C).injective ((hf x).symm.trans (by rw [h]; exact hf y)))
  refine ⟨gp, hw, hr, ha, fun y => ?_, fun F _ _ _ _ uF hF huF y => ?_⟩
  · obtain ⟨χ, rfl⟩ := A.ν.eX.surjective y
    rw [hx]
    exact c_of_field hf gp _ _ (hc χ)
  · obtain ⟨χ, rfl⟩ := A.ν.eX.surjective y
    have k := genRel_field hf A.ν ν' he hw hr (J.e χ) χ (J.h (A.N.c χ)) (u ^ (A.be.be χ χ / 2)) (hc χ) (J.ψ_eq χ)
      ((congrArg (fun q => (J.h (A.N.c χ) : C) * wVal ν' A.ν w q) (J.c_eq χ)).trans (hh _))
    have lift : ∀ (L : Type) [Field L] [Algebra (FractionRing M.W) L] [Algebra (FractionRing O') L], Along f L →
        jFK (R := O') L = spMap (algebraMap (FractionRing M.W) L) ≫ genMap inj := fun L _ _ _ h =>
      (congrArg spMap (IsLocalization.ringHom_ext (nonZeroDivisors O') (RingHom.ext fun x =>
        (h x).symm.trans (congrArg (algebraMap (FractionRing M.W) L) (fracMap_algebraMap inj x).symm)))).trans
        (Geo.Tor.spMap_comp _ _)
    have t := fun (L : Type) [Field L] [Algebra (FractionRing M.W) L] [Algebra (FractionRing O') L] (h : Along f L) =>
      genRel_ext_iff M.P.D.toPre.P.isLB a.D₀.P.isLB w (M.P.D.toPre.psi_gen (ν'.eX (J.e χ))) (a.D₀.psi_gen (A.ν.eX χ))
        (algebraMap (FractionRing M.W) L) (𝟙 _) (genMap inj) (s := jFK (R := M.W) L) (Category.comp_id _).symm (lift L h)
        (algebraMap M.W _ u₀ ^ (A.be.be χ χ / 2))
    rw [Units.val_zpow_eq_zpow_val, hu, ← map_zpow₀] at k
    have k' := (t F fun x => (hF x).symm).2 ((t C hf).1 k)
    rw [hx, huF, ← A.be_eq, ← map_zpow₀]
    exact k'

end GlobalTheory.FitMatch
