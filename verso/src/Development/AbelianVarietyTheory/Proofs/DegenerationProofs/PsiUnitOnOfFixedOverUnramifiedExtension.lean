import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.RegVert
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueFactorOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BiextensionSecondLawCommutativityValue

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnramTorsion

open IsLocalRing GlobalTheory.TorusExt GlobalTheory.BXOf

section General

variable {X Y : Scheme.{0}} {L : LB X} {W F : Type} [CommRing W] [IsDomain W] [IsLocalRing W] [Field F]

/- English proof (translation)
Establish `hd : IsDominant (spMap i)`. Prove the components needed by the constructor for the conclusion. Conclude with `(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical i).2 (by rw [(RingHom.injective_iff_ker_eq_bot i).1 hi]; exact bot_le)`. Conclude with `exists_good L hL (closedPoint F) (fun ψ : Sp W ⟶ X => spMap i ≫ ψ) (fun ψ => J₀ (ψ (closedPoint W))) (fun a b e => by rw [ext_of_isDominant (spMap i) e]) (fun ψ => top_le_of_mem ψ (h₀ _) trivial)`.
-/
theorem exists_good_ext [X.IsSeparated] (hL : L.IsLB) (i : W →+* F) (hi : Function.Injective i) (J₀ : X → L.ι)
    (h₀ : ∀ x, x ∈ L.U (J₀ x)) : ∃ J : (Sp F ⟶ X) → L.ι, Good L (closedPoint F) J ∧
      ∀ ψ : Sp W ⟶ X, J (spMap i ≫ ψ) = J₀ (ψ (closedPoint W)) := by
  have hd : IsDominant (spMap i) := by
    constructor
    exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical i).2
      (by rw [(RingHom.injective_iff_ker_eq_bot i).1 hi]; exact bot_le)
  exact exists_good L hL (closedPoint F) (fun ψ : Sp W ⟶ X => spMap i ≫ ψ) (fun ψ => J₀ (ψ (closedPoint W)))
    (fun a b e => by rw [ext_of_isDominant (spMap i) e])
    (fun ψ => top_le_of_mem ψ (h₀ _) trivial)

omit [IsDomain W] in

/- English proof (translation)
Establish `e` using `val_of t (spMap i ≫ r) (closedPoint F) J (fun k => J₀ ((r ≫ φ k) (closedPoint W))) (fun k => by rw [Category.assoc, hJ])`. Establish `m : r (closedPoint W) ∈ LB.wchart L φ (fun k => J₀ ((r ≫ φ k) (closedPoint W)))` using `Set.mem_iInter.2 fun k => h₀ ((r ≫ φ k) (closedPoint W))`. Conclude with `⟨_, (congrArg (fun u => (sig F u : F)) e).trans (congrArg Units.val (sig_nat i r m _).symm)⟩`.
-/
theorem val_integral (i : W →+* F) {J₀ : X → L.ι} (h₀ : ∀ x, x ∈ L.U (J₀ x)) {J : (Sp F ⟶ X) → L.ι}
    (hJ : ∀ ψ : Sp W ⟶ X, J (spMap i ≫ ψ) = J₀ (ψ (closedPoint W))) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp W ⟶ Y) :
    ∃ u : Wˣ, (sig F (val t (spMap i ≫ r) (closedPoint F) J) : F) = i u := by
  have e := val_of t (spMap i ≫ r) (closedPoint F) J (fun k => J₀ ((r ≫ φ k) (closedPoint W)))
    (fun k => by rw [Category.assoc, hJ])
  have m : r (closedPoint W) ∈ LB.wchart L φ (fun k => J₀ ((r ≫ φ k) (closedPoint W))) :=
    Set.mem_iInter.2 fun k => h₀ ((r ≫ φ k) (closedPoint W))
  exact ⟨_, (congrArg (fun u => (sig F u : F)) e).trans (congrArg Units.val (sig_nat i r m _).symm)⟩

/- English proof (translation)
Establish `e1` using `congrArg (fun q => q.hom (((Spec.map (CommRingCat.ofHom f)).app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))) (germ_stalkClosedPointIso_hom (CommRingCat.of S))`. Establish `e2` using `congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))`. Establish `e3` using `congrArg (fun q => q.hom a) (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id`. Conclude with `(congrArg (stalkClosedPointIso (CommRingCat.of S)).hom.hom (gs_eq (spMap f) (closedPoint S) ⊤ trivial _)).trans (e1.trans (e2.trans (congrArg f e3)))`.
-/
theorem stalk_gs_top {A S : Type} [CommRing A] [CommRing S] [IsLocalRing S] (f : A →+* S) (a : A) :
    (stalkClosedPointIso (CommRingCat.of S)).hom.hom
      (gs (spMap f) (closedPoint S) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) = f a := by
  have e1 := congrArg (fun q => q.hom (((Spec.map (CommRingCat.ofHom f)).app ⊤).hom
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))) (germ_stalkClosedPointIso_hom (CommRingCat.of S))
  have e2 := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))
  have e3 := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id
  exact (congrArg (stalkClosedPointIso (CommRingCat.of S)).hom.hom (gs_eq (spMap f) (closedPoint S) ⊤ trivial _)).trans
    (e1.trans (e2.trans (congrArg f e3)))

/- English proof (translation)
Set `a : Γ(Sp A, ⊤)` to `(Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom r`. Establish `hu` using `(Sp A).toRingedSpace.isUnit_res_basicOpen a`. Use `⟨(Sp A).basicOpen a, hu.unit, ?_, fun h => ?_⟩` and prove the remaining obligations. Use `basicOpen_eq_of_affine (R := CommRingCat.of A) r show P ∈ (Spec (CommRingCat.of A)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of A)).inv r)` as an intermediate fact. Rewrite using `[this]`.

Conclude with `hr`. Use `Eq.trans ?_ (stalk_gs_top f r)` and prove the remaining obligations. Conclude with `congrArg (stalkClosedPointIso (CommRingCat.of S)).hom.hom ((gs_unit _ _ _ h hu.unit).symm.trans (gs_res _ _ ((Sp A).basicOpen_le a) h a))`.
-/
theorem exists_unit_near {A S : Type} [CommRing A] [CommRing S] [IsLocalRing S] (f : A →+* S) (P : PrimeSpectrum A)
    (r : A) (hr : r ∉ P.asIdeal) : ∃ (V : (Sp A).Opens) (u : Γ(Sp A, V)ˣ), P ∈ V ∧
      (spMap f (closedPoint S) ∈ V → (sig S (gm (spMap f) (closedPoint S) V u) : S) = f r) := by
  let a : Γ(Sp A, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom r
  have hu := (Sp A).toRingedSpace.isUnit_res_basicOpen a
  refine ⟨(Sp A).basicOpen a, hu.unit, ?_, fun h => ?_⟩
  · have := basicOpen_eq_of_affine (R := CommRingCat.of A) r
    show P ∈ (Spec (CommRingCat.of A)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of A)).inv r)
    rw [this]; exact hr
  · refine Eq.trans ?_ (stalk_gs_top f r)
    exact congrArg (stalkClosedPointIso (CommRingCat.of S)).hom.hom
      ((gs_unit _ _ _ h hu.unit).symm.trans (gs_res _ _ ((Sp A).basicOpen_le a) h a))

end General

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

attribute [local instance] gtGroup

section Abstract

variable {T : Over (Spec (CommRingCat.of R))} (ρ : TF (R := R) F ⟶ T) {z : (TF (R := R) F).left}
  {J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) {U : Type} [CommGroup U]
  (w : ((TF (R := R) F).left.presheaf.stalk z)ˣ →* U)
  (hw : ∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ D.P.A.left)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb D.P.L φ ε)) (r : T.left ⟶ Y), w (val t (ρ.left ≫ r) z J) = 1)
include hJ hw

omit hJ in
/- English proof (translation)
Use `hw _ _ (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift x (lift x' y)).left` as an intermediate fact. Rewrite `this` using `[← Over.comp_left, comp_lift, comp_lift]`. Conclude with `this`.
-/
theorem w_th (x x' y : T ⟶ D.P.A) : w (th D z J (ρ ≫ x) (ρ ≫ x') (ρ ≫ y)) = 1 := by
  have := hw _ _ (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift x (lift x' y)).left
  rw [← Over.comp_left, comp_lift, comp_lift] at this
  exact this

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rw [zero_nsmul, zero_val χ hJ, map_one, pow_zero]`. Consider the case `succ k ih`. Establish `e` using `congrArg w (add_val (k • g) g χ hJ)`. Establish `hk : (k • g).b = ρ ≫ b ^ k` using `by rw [nsmul_b, ← hb]; exact (map_pow (preHom ρ) _ _).symm`.

Establish `e' : w (th D z J (cP D _ χ) (k • g).b g.b) = 1`. Rewrite using `[hk, ← hb, ← comp_cP D ρ]`. Conclude with `w_th ρ w hw _ _ _`. Rewrite `e` using `[map_mul, map_mul, e', _root_.mul_one, ih]`. Rewrite using `[succ_nsmul, e, pow_succ]`.
-/
theorem w_nsmul (g : GtPtF D F) (b : T ⟶ D.P.A) (hb : ρ ≫ b = g.b) (χ : D.X) (k : ℕ) :
    w (charVal (k • g) χ z J) = w (charVal g χ z J) ^ k := by
  induction k with
  | zero => rw [zero_nsmul, zero_val χ hJ, map_one, pow_zero]
  | succ k ih =>
    have e := congrArg w (add_val (k • g) g χ hJ)
    have hk : (k • g).b = ρ ≫ b ^ k := by rw [nsmul_b, ← hb]; exact (map_pow (preHom ρ) _ _).symm
    have e' : w (th D z J (cP D _ χ) (k • g).b g.b) = 1 := by
      rw [hk, ← hb, ← comp_cP D ρ]; exact w_th ρ w hw _ _ _
    rw [map_mul, map_mul, e', _root_.mul_one, ih] at e
    rw [succ_nsmul, e, pow_succ]

/- English proof (translation)
Establish `e : tauVal D F a b z J = _` using `(val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) ((val_inv _ _).trans (congrArg (·⁻¹) (val_pull hJ _ _ _))))`. Establish `h : ((𝟙 (TF (R` using `R) F) :).left ≫ jFK (R := R) F) ≫ (toUnit (TK R)).left = ρ.left ≫ T.hom := (congrArg (· ≫ jK R) (Category.id_comp _)).trans (Over.w ρ).symm`. Establish `r` using `hw _ _ _ _ D.rig T.hom`. Rewrite `r` using `[← h]`. Rewrite using `[e, map_mul, map_mul, map_mul, map_inv, map_inv, map_inv]`.

Conclude with `(congrArg (_ * ·⁻¹) r).trans (by rw [inv_one, _root_.mul_one])`.
-/
theorem w_tau (a b : D.X) : w (tauVal D F a b z J) =
    w (val (D.psi (a + b)) ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) z J) *
      (w (val (D.psi a) ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) z J))⁻¹ *
      (w (val (D.psi b) ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) z J))⁻¹ := by
  have e : tauVal D F a b z J = _ :=
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) ((val_inv _ _).trans (congrArg (·⁻¹) (val_pull hJ _ _ _))))
  have h : ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) ≫ (toUnit (TK R)).left = ρ.left ≫ T.hom :=
    (congrArg (· ≫ jK R) (Category.id_comp _)).trans (Over.w ρ).symm
  have r := hw _ _ _ _ D.rig T.hom
  rw [← h] at r
  rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, map_inv]
  exact (congrArg (_ * ·⁻¹) r).trans (by rw [inv_one, _root_.mul_one])

/- English proof (translation)
Establish `e` using `((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))).symm.trans (val_corr hJ (hE χ) ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F))`. Establish `h : ((𝟙 (TF (R` using `R) F) :).left ≫ jFK (R := R) F) ≫ D.xK χ = ρ.left ≫ (cP D T χ).left := by`. Rewrite using `[← Over.comp_left, comp_cP]`. Conclude with `(congrArg (· ≫ D.xK χ) (Category.id_comp _)).trans (Category.assoc _ _ _).symm`. Establish `r` using `hw _ _ _ _ D.sym (cP D T χ).left`.

Rewrite `r` using `[← h]`. Rewrite using `[← e, map_mul, r, _root_.mul_one]`.
-/
theorem w_even (hE : D.PsiEven) (χ : D.X) :
    w (val (D.psi (-χ)) ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) z J) =
      w (val (D.psi χ) ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) z J) := by
  have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))).symm.trans
    (val_corr hJ (hE χ) ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F))
  have h : ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) ≫ D.xK χ = ρ.left ≫ (cP D T χ).left := by
    rw [← Over.comp_left, comp_cP]
    exact (congrArg (· ≫ D.xK χ) (Category.id_comp _)).trans (Category.assoc _ _ _).symm
  have r := hw _ _ _ _ D.sym (cP D T χ).left
  rw [← h] at r
  rw [← e, map_mul, r, _root_.mul_one]

end Abstract

/- English proof (translation)
Establish `e` using `gtExt_val σ hσ g χ hJ`. Establish `hb` using `gtExt_b σ hσ g`. Rewrite `e`, `hb` using `[hg]`. Establish `hφ : ∀ k, (extMap σ hσ).left ≫ DegPre.gtφ D F g.b χ k = 𝟙 _ ≫ DegPre.gtφ D F g.b χ k`. Introduce `k`.

Rewrite using `[Category.id_comp]`. Use `fin_cases k`. Use `show (extMap σ hσ ≫ (cP D _ χ * g.b)).left = (cP D _ χ * g.b).left`. Rewrite using `[MonObj.comp_mul, comp_cP, ← hb]`. Use `show (extMap σ hσ ≫ cP D _ χ).left = (cP D _ χ).left`.

Rewrite using `[comp_cP]`. Use `show (extMap σ hσ ≫ g.b).left = g.b.left`. Rewrite using `[← hb]`. Use `show (extMap σ hσ ≫ (1 : TF (R := R) F ⟶ D.P.A)).left = (1 : TF (R := R) F ⟶ D.P.A).left`. Rewrite using `[MonObj.comp_one]`.

Use `replace e := e.trans (val_of (g.s χ) _ _ J _ (fun k => congrArg J (hφ k)))`. Establish `n` using `sig_nat σ (𝟙 (Spec (CommRingCat.of F))) (hJ.mem (DegPre.gtφ D F g.b χ) (𝟙 _)) ((g.s χ).s fun k => J (𝟙 _ ≫ DegPre.gtφ D F g.b χ k))`. Rewrite `n` using `[Category.comp_id]`. Conclude with `(congrArg Units.val n).trans (congrArg (fun u => (sig F u : F)) e.symm)`.
-/
theorem charVal_fixed (σ : F →+* F) (hσ : σ.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F)
    (g : GtPtF D F) (hg : gtExt D σ hσ g = g) (χ : D.X) {J} (hJ : Good D.P.L (Z := (TF (R := R) F).left) (closedPoint F) J) :
    σ (sig F (charVal g χ (closedPoint F) J) : F) = (sig F (charVal g χ (closedPoint F) J) : F) := by
  have e := gtExt_val σ hσ g χ hJ
  have hb := gtExt_b σ hσ g
  rw [hg] at e hb
  have hφ : ∀ k, (extMap σ hσ).left ≫ DegPre.gtφ D F g.b χ k = 𝟙 _ ≫ DegPre.gtφ D F g.b χ k := by
    intro k
    rw [Category.id_comp]
    fin_cases k
    · show (extMap σ hσ ≫ (cP D _ χ * g.b)).left = (cP D _ χ * g.b).left
      rw [MonObj.comp_mul, comp_cP, ← hb]
    · show (extMap σ hσ ≫ cP D _ χ).left = (cP D _ χ).left
      rw [comp_cP]
    · show (extMap σ hσ ≫ g.b).left = g.b.left
      rw [← hb]
    · show (extMap σ hσ ≫ (1 : TF (R := R) F ⟶ D.P.A)).left = (1 : TF (R := R) F ⟶ D.P.A).left
      rw [MonObj.comp_one]
  replace e := e.trans (val_of (g.s χ) _ _ J _ (fun k => congrArg J (hφ k)))
  have n := sig_nat σ (𝟙 (Spec (CommRingCat.of F))) (hJ.mem (DegPre.gtφ D F g.b χ) (𝟙 _))
    ((g.s χ).s fun k => J (𝟙 _ ≫ DegPre.gtφ D F g.b χ k))
  rw [Category.comp_id] at n
  exact (congrArg Units.val n).trans (congrArg (fun u => (sig F u : F)) e.symm)

def psiLoc (D : DegPre R) (χ : D.X) (j : D.P.L.ι) : (FractionRing R)ˣ :=
  sig (FractionRing R) (gm (𝟙 (Spec (CommRingCat.of (FractionRing R)))) (closedPoint (FractionRing R))
    (LB.wchart D.P.L (fun _ : PUnit => D.xK χ) fun _ => j) ((D.psi χ).s fun _ => j))

/- English proof (translation)
Take `⟨V₁, u₁, p₁, e₁⟩` from `exists_unit_near (algebraMap R (FractionRing R)) P r hr`. Take `⟨V₂, u₂, p₂, e₂⟩` from `exists_unit_near (algebraMap R (FractionRing R)) P s hs`. Establish `key : ∀ y : (TK R).left, jK R y ∈ V₁ → jK R y ∈ V₂ → gm (jK R) y V₁ u₁ * (gm (jK R) y V₂ u₂)⁻¹ = gm (𝟙 (TK R).left) y (LB.wchart D.P.L (fun _ : PUnit => D.xK χ) fun _ => j₀) ((D.psi χ).s fun _ => j₀)`. Introduce `y h₁ h₂`. Take `rfl : y = closedPoint (FractionRing R)` from `Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _`.

Use `mul_inv_eq_iff_eq_mul.2 (Units.map_injective (f := (stalkClosedPointIso (CommRingCat.of (FractionRing R))).hom.hom.toMonoidHom) (stalkClosedPointIso (CommRingCat.of (FractionRing R))).commRingCatIsoToRingEquiv.injective ?_)` and prove the remaining obligations. Use `Eq.trans ?_ (map_mul (sig (FractionRing R)) _ _).symm` and prove the remaining obligations. Conclude with `Units.ext ((e₁ h₁).trans (h.symm.trans (congrArg ((psiLoc D χ j₀ : FractionRing R) * ·) (e₂ h₂).symm)))`. Use `⟨V₁ ⊓ V₂ ⊓ (D.c χ).left ⁻¹ᵁ D.P.L.U j₀, ⟨⟨p₁, p₂⟩, hj⟩, fun j V _ hV hle hh => ?_⟩` and prove the remaining obligations. Establish `l₁ : V ≤ V₁` using `fun x hx => (hV hx).1.1`.

Establish `l₂ : V ≤ V₂` using `fun x hx => (hV hx).1.2`. Establish `l₃ : V ≤ (show Sp R ⟶ D.P.A.left from (D.c χ).left) ⁻¹ᵁ (D.P.L.U (j PUnit.unit) ⊓ D.P.L.U j₀)` using `fun x hx => ⟨hle hx, (hV hx).2⟩`. Choose the witnesses or unpack the hypotheses as in `⟨u, hu⟩ : ∃ u : Γ(Sp R, V)ˣ, ∀ y : (TK R).left, jK R y ∈ V → gm (jK R) y V u = (gm (jK R ≫ (show Sp R ⟶ D.P.A.left from (D.c χ).left)) y _ (D.P.L.g (j PUnit.unit) j₀))⁻¹ * (gm (jK R) y V₁ u₁ * (gm (jK R) y V₂ u₂)⁻¹) := by`. Use `⟨(res l₃ (pullU (show Sp R ⟶ D.P.A.left from (D.c χ).left) _ (D.P.L.g (j PUnit.unit) j₀)))⁻¹ * (res l₁ u₁ * (res l₂ u₂)⁻¹), fun y hy => ?_⟩` and prove the remaining obligations. Establish `a₁` using `gm_res (jK R) y l₁ hy u₁`.

Establish `a₂` using `gm_res (jK R) y l₂ hy u₂`. Establish `a₃` using `(gm_res (jK R) y l₃ hy _).trans (gm_pull (jK R) (show Sp R ⟶ D.P.A.left from (D.c χ).left) y _ (l₃ hy) (D.P.L.g (j PUnit.unit) j₀))`. Conclude with `(map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_inv _ _).trans (congrArg (·⁻¹) a₃)) ((map_mul _ _ _).trans (congrArg₂ (· * ·) a₁ ((map_inv _ _).trans (congrArg (·⁻¹) a₂)))))`. Use `⟨u.val, u.isUnit, ?_⟩` and prove the remaining obligations. Establish `: pullU (jK R) V u = res hh ((D.psi χ).s j)` using `unit_ext fun y hy => by`.

Establish `p` using `gm_pull (𝟙 _) (jK R) y V hy u`. Rewrite `p` using `[Category.id_comp]`. Use `p.trans (Eq.trans ?_ (gm_res _ y hh hy _).symm)` and prove the remaining obligations. Establish `m₀ : (𝟙 (TK R).left : _ ⟶ _) y ∈ LB.wchart D.P.L (fun _ : PUnit => D.xK χ) fun _ => j₀` using `Set.mem_iInter.2 fun _ => (l₃ hy).2`. Use `Eq.trans ?_ (gen_trans (D.psi_gen χ) (𝟙 _) y (hh hy) m₀).symm` and prove the remaining obligations.

Use `(hu y hy).trans (congrArg₂ (· * ·) ?_ (key y (l₁ hy) (l₂ hy)))` and prove the remaining obligations. Simplify using `only [trF, Category.id_comp, Fintype.prod_unique, zpow_neg_one]`. Both sides reduce to the same expression. Conclude with `congrArg Units.val this`.
-/
theorem psiUnitOn_near (χ : D.X) (P : PrimeSpectrum R) (j₀ : D.P.L.ι) (hj : (D.c χ).left P ∈ D.P.L.U j₀) (r s : R)
    (hr : r ∉ P.asIdeal) (hs : s ∉ P.asIdeal)
    (h : (psiLoc D χ j₀ : FractionRing R) * algebraMap R _ s = algebraMap R _ r) :
    ∃ V : (Sp R).Opens, P ∈ V ∧ PsiUnitOn D χ V := by
  obtain ⟨V₁, u₁, p₁, e₁⟩ := exists_unit_near (algebraMap R (FractionRing R)) P r hr
  obtain ⟨V₂, u₂, p₂, e₂⟩ := exists_unit_near (algebraMap R (FractionRing R)) P s hs
  have key : ∀ y : (TK R).left, jK R y ∈ V₁ → jK R y ∈ V₂ → gm (jK R) y V₁ u₁ * (gm (jK R) y V₂ u₂)⁻¹ =
      gm (𝟙 (TK R).left) y (LB.wchart D.P.L (fun _ : PUnit => D.xK χ) fun _ => j₀) ((D.psi χ).s fun _ => j₀) := by
    intro y h₁ h₂
    obtain rfl : y = closedPoint (FractionRing R) := Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _
    refine mul_inv_eq_iff_eq_mul.2 (Units.map_injective
      (f := (stalkClosedPointIso (CommRingCat.of (FractionRing R))).hom.hom.toMonoidHom)
      (stalkClosedPointIso (CommRingCat.of (FractionRing R))).commRingCatIsoToRingEquiv.injective ?_)
    refine Eq.trans ?_ (map_mul (sig (FractionRing R)) _ _).symm
    exact Units.ext ((e₁ h₁).trans (h.symm.trans (congrArg ((psiLoc D χ j₀ : FractionRing R) * ·) (e₂ h₂).symm)))
  refine ⟨V₁ ⊓ V₂ ⊓ (D.c χ).left ⁻¹ᵁ D.P.L.U j₀, ⟨⟨p₁, p₂⟩, hj⟩, fun j V _ hV hle hh => ?_⟩
  have l₁ : V ≤ V₁ := fun x hx => (hV hx).1.1
  have l₂ : V ≤ V₂ := fun x hx => (hV hx).1.2
  have l₃ : V ≤ (show Sp R ⟶ D.P.A.left from (D.c χ).left) ⁻¹ᵁ (D.P.L.U (j PUnit.unit) ⊓ D.P.L.U j₀) :=
    fun x hx => ⟨hle hx, (hV hx).2⟩
  obtain ⟨u, hu⟩ : ∃ u : Γ(Sp R, V)ˣ, ∀ y : (TK R).left, jK R y ∈ V → gm (jK R) y V u =
      (gm (jK R ≫ (show Sp R ⟶ D.P.A.left from (D.c χ).left)) y _ (D.P.L.g (j PUnit.unit) j₀))⁻¹ * (gm (jK R) y V₁ u₁ * (gm (jK R) y V₂ u₂)⁻¹) := by
    refine ⟨(res l₃ (pullU (show Sp R ⟶ D.P.A.left from (D.c χ).left) _ (D.P.L.g (j PUnit.unit) j₀)))⁻¹ *
      (res l₁ u₁ * (res l₂ u₂)⁻¹), fun y hy => ?_⟩
    have a₁ := gm_res (jK R) y l₁ hy u₁
    have a₂ := gm_res (jK R) y l₂ hy u₂
    have a₃ := (gm_res (jK R) y l₃ hy _).trans (gm_pull (jK R) (show Sp R ⟶ D.P.A.left from (D.c χ).left) y _ (l₃ hy)
      (D.P.L.g (j PUnit.unit) j₀))
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_inv _ _).trans (congrArg (·⁻¹) a₃))
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) a₁ ((map_inv _ _).trans (congrArg (·⁻¹) a₂)))))
  refine ⟨u.val, u.isUnit, ?_⟩
  have : pullU (jK R) V u = res hh ((D.psi χ).s j) := unit_ext fun y hy => by
    have p := gm_pull (𝟙 _) (jK R) y V hy u
    rw [Category.id_comp] at p
    refine p.trans (Eq.trans ?_ (gm_res _ y hh hy _).symm)
    have m₀ : (𝟙 (TK R).left : _ ⟶ _) y ∈
        LB.wchart D.P.L (fun _ : PUnit => D.xK χ) fun _ => j₀ := Set.mem_iInter.2 fun _ => (l₃ hy).2
    refine Eq.trans ?_ (gen_trans (D.psi_gen χ) (𝟙 _) y (hh hy) m₀).symm
    refine (hu y hy).trans (congrArg₂ (· * ·) ?_ (key y (l₁ hy) (l₂ hy)))
    simp only [trF, Category.id_comp, Fintype.prod_unique, zpow_neg_one]
    rfl
  exact congrArg Units.val this

/- English proof (translation)
Use `D.P.isAb.proper` as an intermediate fact. Establish `hE : ValuativeCriterion.Existence D.P.A.hom`. Establish `h : UniversallyClosed D.P.A.hom` using `inferInstance`. Rewrite `h` using `[UniversallyClosed.eq_valuativeCriterion]`. Conclude with `h.1`.

Set `S : ValuativeCommSq D.P.A.hom` to `{ R := W, K := F, i₁ := b.left, i₂ := spMap φ, commSq := ⟨(Over.w b).trans ((Over.w ρ).symm.trans (congrArg (· ≫ spMap φ) hρ))⟩ }`. Take `⟨⟨l, h1, h2⟩⟩` from `hE S`. Conclude with `⟨Over.homMk l h2, Over.OverMorphism.ext ((congrArg (· ≫ l) hρ).trans h1)⟩`.
-/
theorem exists_extend (W : ValuationSubring F) (φ : R →+* W) (ρ : TF (R := R) F ⟶ Over.mk (spMap φ))
    (hρ : ρ.left = spMap W.subtype) (b : TF (R := R) F ⟶ D.P.A) : ∃ b' : Over.mk (spMap φ) ⟶ D.P.A, ρ ≫ b' = b := by
  have := D.P.isAb.proper
  have hE : ValuativeCriterion.Existence D.P.A.hom := by
    have h : UniversallyClosed D.P.A.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  let S : ValuativeCommSq D.P.A.hom :=
    { R := W, K := F, i₁ := b.left, i₂ := spMap φ,
      commSq := ⟨(Over.w b).trans ((Over.w ρ).symm.trans (congrArg (· ≫ spMap φ) hρ))⟩ }
  obtain ⟨⟨l, h1, h2⟩⟩ := hE S
  exact ⟨Over.homMk l h2, Over.OverMorphism.ext ((congrArg (· ≫ l) hρ).trans h1)⟩

/- English proof (translation)
Use `letI : Algebra (FractionRing T) F := FractionRing.liftAlgebra T F`. Establish `: IsScalarTower T (FractionRing T) F` using `FractionRing.isScalarTower_liftAlgebra T F`. Establish `: CharZero (FractionRing T)` using `(algebraMap (FractionRing T) F).charZero`. Take `⟨y, rfl⟩` from `GlobalTheory.GaloisDescent.mem_range_algebraMap_of_forall_algEquiv (K := FractionRing T) x fun σ => h σ.toRingEquiv fun t ht => by`. Use `σ.commutes (algebraMap T (FractionRing T) ⟨t, ht⟩)` as an intermediate fact.

Rewrite `this` using `[← IsScalarTower.algebraMap_apply]`. Then use the resulting hypothesis. Take `⟨v, u, rfl⟩` from `IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hϖ (x := y) (fun e => hx (by rw [e, map_zero]))`. Use `⟨v, u, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]`. Both sides reduce to the same expression.
-/
theorem eq_unit_mul_zpow_of_fixed {F : Type} [Field F] [IsAlgClosed F] [CharZero F] (T : Subring F)
    [IsDiscreteValuationRing T] {ϖ : T} (hϖ : Irreducible ϖ) (x : F) (hx : x ≠ 0)
    (h : ∀ σ : F ≃+* F, (∀ t ∈ T, σ t = t) → σ x = x) : ∃ (v : ℤ) (u : Tˣ), x = ((u : T) : F) * (ϖ : F) ^ v := by
  letI : Algebra (FractionRing T) F := FractionRing.liftAlgebra T F
  have : IsScalarTower T (FractionRing T) F := FractionRing.isScalarTower_liftAlgebra T F
  have : CharZero (FractionRing T) := (algebraMap (FractionRing T) F).charZero
  obtain ⟨y, rfl⟩ := GlobalTheory.GaloisDescent.mem_range_algebraMap_of_forall_algEquiv (K := FractionRing T) x fun σ =>
    h σ.toRingEquiv fun t ht => by
      have := σ.commutes (algebraMap T (FractionRing T) ⟨t, ht⟩)
      rwa [← IsScalarTower.algebraMap_apply] at this
  obtain ⟨v, u, rfl⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hϖ
    (x := y) (fun e => hx (by rw [e, map_zero]))
  refine ⟨v, u, ?_⟩
  rw [Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀, ← IsScalarTower.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply]
  rfl

/- English proof (translation)
Take `⟨W, hW, hloc⟩` from `IsLocalRing.exists_factor_valuationRing T.subtype`. Set `inc : T →+* W` to `T.subtype.codRestrict W.toSubring hW`. Establish `hloc : IsLocalHom inc` using `hloc`. Set `φ' : R →+* W` to `inc.comp φ`. Set `ρ : TF (R` to `R) F ⟶ Over.mk (spMap φ') := Over.homMk (spMap W.subtype) (by show spMap W.subtype ≫ spMap φ' = jFK (R := R) F ≫ jK R`.

Rewrite using `[jFK, jK, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2`. Conclude with `RingHom.ext hφ)`. Use `D.P.isAb.proper` as an intermediate fact. Establish `: D.P.A.left.IsSeparated` using `⟨by rw [← terminal.comp_from D.P.A.hom]; infer_instance⟩`.

Take `⟨J, hJ, eJ⟩` from `exists_good_ext D.P.isLB W.subtype Subtype.val_injective J₀ h₀`. Set `z : (TF (R` to `R) F).left := closedPoint F`. Establish `hJ : Good D.P.L z J` using `hJ`. Take `⟨w, hw⟩ : ∃ w : ((TF (R` from `R) F).left.presheaf.stalk z)ˣ →* W.ValueGroupˣ, ∀ u, (w u : W.ValueGroup) = W.valuation (sig F u : F) := ⟨(Units.map W.valuation.toMonoidWithZeroHom.toMonoidHom).comp (sig F), fun _ => rfl⟩`. Establish `hint : ∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (ψ : K → (Y ⟶ D.P.A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb D.P.L ψ ε)) (r : (Over.mk (spMap φ')).left ⟶ Y), w (val t (ρ.left ≫ r) z J) = 1`.

Introduce `Y K _ ψ ε t r`. Take `⟨u, hu⟩` from `val_integral W.subtype h₀ eJ t r`. Conclude with `Units.ext ((hw _).trans ((congrArg W.valuation hu).trans (W.valuation_unit u)))`. Establish `ϖ0 : W.valuation (ϖ : F) ≠ 0`. Rewrite using `[Valuation.ne_zero_iff]`.

Conclude with `fun e => hϖ.ne_zero (Subtype.ext e)`. Establish `ϖ1 : W.valuation (ϖ : F) ≠ 1` using `fun e => hϖ.not_isUnit (hloc.map_nonunit ϖ ((W.valuation_eq_one_iff (inc ϖ)).2 e))`. Set `t : W.ValueGroupˣ` to `Units.mk0 _ ϖ0`. Establish `inj : ∀ a b : ℤ, t ^ a = t ^ b → a = b` using `fun a b e => by`. Establish `e'` using `congrArg Units.val e`.

Rewrite `e'` using `[Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val]`. Conclude with `zpow_right_injective₀ (zero_lt_iff.2 ϖ0) ϖ1 e'`. Establish `hv : ∀ s (u : Tˣ) (v : ℤ), (sig F s : F) = ((u : T) : F) * (ϖ : F) ^ v → w s = t ^ v` using `fun s u v e => by`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[hw, e, map_mul, map_zpow₀, Units.val_zpow_eq_zpow_val]`.

Conclude with `(congrArg (· * _) (W.valuation_unit (Units.map inc.toMonoidHom u))).trans (_root_.one_mul _)`. Establish `hc : spMap φ' (closedPoint W) = P` using `PrimeSpectrum.ext (Ideal.ext fun r => by`. Rewrite using `[hP]`. Conclude with `⟨fun h e => h (e.map inc), fun h e => h (hloc.map_nonunit _ e)⟩)`. Establish `hψ : ∀ χ, w (val (D.psi χ) ((𝟙 (TF (R` using `R) F) :).left ≫ jFK (R := R) F) z J) = t ^ m χ := fun χ => by`.

Take `⟨u, hu⟩` from `hm χ`. Use `hv _ u _ (Eq.trans ?_ hu)` and prove the remaining obligations. Establish `h : ((𝟙 (TF (R` using `R) F) :).left ≫ jFK (R := R) F) ≫ D.xK χ = ρ.left ≫ (cP D _ χ).left := by`. Rewrite using `[← Over.comp_left, comp_cP]`. Conclude with `(congrArg (· ≫ D.xK χ) (Category.id_comp _)).trans (Category.assoc _ _ _).symm`.

Establish `hj : J (((𝟙 (TF (R` using `R) F) :).left ≫ jFK (R := R) F) ≫ D.xK χ) = J₀ ((D.c χ).left P) := (congrArg J h).trans ((eJ _).trans (congrArg (fun q => J₀ ((D.c χ).left q)) hc))`. Establish `e` using `val_of (D.psi χ) _ z J (fun _ => J₀ ((D.c χ).left P)) fun _ => hj`. Establish `m₀ : (𝟙 (Spec (CommRingCat.of (FractionRing R))) : _ ⟶ _) (closedPoint (FractionRing R)) ∈ LB.wchart D.P.L (fun _ : PUnit => D.xK χ) fun _ => J₀ ((D.c χ).left P)` using `Set.mem_iInter.2 fun _ => by`. Establish `a` using `hJ (((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) ≫ D.xK χ)`. Rewrite `a` using `[hj]`.

Establish `b : closedPoint (FractionRing R) = ((𝟙 (TF (R` using `R) F) :).left ≫ jFK (R := R) F) z := Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _`. Conclude with `(congrArg (fun q => D.xK χ q ∈ D.P.L.U (J₀ ((D.c χ).left P))) b).mpr a`. Establish `n` using `sig_nat (algebraMap (FractionRing R) F) (𝟙 _) m₀ ((D.psi χ).s fun _ => J₀ ((D.c χ).left P))`. Establish `c : (𝟙 (TF (R` using `R) F) :).left ≫ jFK (R := R) F = jFK (R := R) F ≫ 𝟙 _ := (Category.id_comp _).trans (Category.comp_id _).symm`. Conclude with `(congrArg (fun u => (sig F u : F)) (e.trans (congrArg (fun q => gm q z _ _) c))).trans (congrArg Units.val n).symm`.

Use `⟨fun y χ => ?_, fun χ => inj _ _ ((hψ _).symm.trans ((w_even ρ hJ w hint hE χ).trans (hψ _)))⟩` and prove the remaining obligations. Take `⟨p, rfl⟩` from `exists_qkPt (F := F) hM (Or.inl inferInstance) hB hk y`. Take `⟨b, hb⟩` from `exists_extend W φ' ρ rfl p.g.b`. Take `⟨v, u, hu⟩` from `eq_unit_mul_zpow_of_fixed T hϖ (sig F (charVal p.g χ z J) : F) (Units.ne_zero _) fun σ hσ => by`. Establish `hσ' : σ.toRingHom.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F` using `IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => by show σ (algebraMap (FractionRing R) F (algebraMap R _ r)) = algebraMap (FractionRing R) F (algebraMap R _ r)`.

Rewrite using `[← hφ]`. Conclude with `hσ _ (φ r).2)`. Take `⟨a, ha, hg⟩` from `(equiv_iff hB _ _).1 (hfix σ hσ p _ ((qkExt_iff hB _ hσ' _ _).2 rfl))`. Establish `a0 : a = 0`. Establish `: k • a = 0` using `left_eq_add.1 ha`.

Conclude with `(smul_eq_zero.1 (show (k : ℤ) • a = 0 by rw [natCast_zsmul, this])).resolve_left (Int.natCast_ne_zero.2 hk)`. Rewrite `hg` using `[a0, map_zero, add_zero]`. Conclude with `charVal_fixed σ.toRingHom hσ' p.g hg χ hJ`. Establish `e₁` using `w_nsmul ρ hJ w hint p.g b hb χ k`. Rewrite `e₁` using `[qk_nsmul hB, iota_val hB _ _ hJ, w_tau ρ hJ w hint, hψ, hψ, hψ, hv _ u v hu, ← zpow_natCast, ← zpow_mul, ← zpow_sub, ← zpow_sub]`.

Conclude with `⟨v, (inj _ _ e₁).trans (mul_comm _ _)⟩`.
-/
theorem level_step (hM : MulNSt) [IsNoetherianRing R] [IsAlgClosed F] [CharZero F] (hB : D.TauBimult) (hE : D.PsiEven)
    (P : PrimeSpectrum R) (J₀ : D.P.A.left → D.P.L.ι) (h₀ : ∀ x, x ∈ D.P.L.U (J₀ x)) (k : ℕ) (hk : k ≠ 0)
    (T : Subring F) [IsDiscreteValuationRing T] (φ : R →+* T)
    (hφ : ∀ r, (φ r : F) = algebraMap (FractionRing R) F (algebraMap R _ r))
    (hP : ∀ r, r ∈ P.asIdeal ↔ ¬ IsUnit (φ r)) (ϖ : T) (hϖ : Irreducible ϖ) (m : D.X → ℤ)
    (hm : ∀ χ, ∃ u : Tˣ, algebraMap (FractionRing R) F (psiLoc D χ (J₀ ((D.c χ).left P))) = ((u : T) : F) * (ϖ : F) ^ m χ)
    (hfix : ∀ σ : F ≃+* F, (∀ x ∈ T, σ x = x) → ∀ p q : QkPt D F k, QkExt σ.toRingHom p q → QkPt.Equiv D F p q) :
    (∀ y χ, (k : ℤ) ∣ m (y + χ) - m y - m χ) ∧ ∀ χ, m (-χ) = m χ := by
  obtain ⟨W, hW, hloc⟩ := IsLocalRing.exists_factor_valuationRing T.subtype
  let inc : T →+* W := T.subtype.codRestrict W.toSubring hW
  have hloc : IsLocalHom inc := hloc
  let φ' : R →+* W := inc.comp φ
  let ρ : TF (R := R) F ⟶ Over.mk (spMap φ') := Over.homMk (spMap W.subtype) (by
    show spMap W.subtype ≫ spMap φ' = jFK (R := R) F ≫ jK R
    rw [jFK, jK, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hφ)
  have := D.P.isAb.proper
  have : D.P.A.left.IsSeparated := ⟨by rw [← terminal.comp_from D.P.A.hom]; infer_instance⟩
  obtain ⟨J, hJ, eJ⟩ := exists_good_ext D.P.isLB W.subtype Subtype.val_injective J₀ h₀
  let z : (TF (R := R) F).left := closedPoint F
  have hJ : Good D.P.L z J := hJ
  obtain ⟨w, hw⟩ : ∃ w : ((TF (R := R) F).left.presheaf.stalk z)ˣ →* W.ValueGroupˣ,
      ∀ u, (w u : W.ValueGroup) = W.valuation (sig F u : F) :=
    ⟨(Units.map W.valuation.toMonoidWithZeroHom.toMonoidHom).comp (sig F), fun _ => rfl⟩
  have hint : ∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (ψ : K → (Y ⟶ D.P.A.left)) (ε : K → ℤ)
      (t : LB.Gen (LB.LinComb D.P.L ψ ε)) (r : (Over.mk (spMap φ')).left ⟶ Y), w (val t (ρ.left ≫ r) z J) = 1 := by
    intro Y K _ ψ ε t r
    obtain ⟨u, hu⟩ := val_integral W.subtype h₀ eJ t r
    exact Units.ext ((hw _).trans ((congrArg W.valuation hu).trans (W.valuation_unit u)))
  have ϖ0 : W.valuation (ϖ : F) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact fun e => hϖ.ne_zero (Subtype.ext e)
  have ϖ1 : W.valuation (ϖ : F) ≠ 1 := fun e =>
    hϖ.not_isUnit (hloc.map_nonunit ϖ ((W.valuation_eq_one_iff (inc ϖ)).2 e))
  let t : W.ValueGroupˣ := Units.mk0 _ ϖ0
  have inj : ∀ a b : ℤ, t ^ a = t ^ b → a = b := fun a b e => by
    have e' := congrArg Units.val e
    rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val] at e'
    exact zpow_right_injective₀ (zero_lt_iff.2 ϖ0) ϖ1 e'
  have hv : ∀ s (u : Tˣ) (v : ℤ), (sig F s : F) = ((u : T) : F) * (ϖ : F) ^ v → w s = t ^ v := fun s u v e => by
    apply Units.ext
    rw [hw, e, map_mul, map_zpow₀, Units.val_zpow_eq_zpow_val]
    exact (congrArg (· * _) (W.valuation_unit (Units.map inc.toMonoidHom u))).trans (_root_.one_mul _)
  have hc : spMap φ' (closedPoint W) = P := PrimeSpectrum.ext (Ideal.ext fun r => by
    rw [hP]
    exact ⟨fun h e => h (e.map inc), fun h e => h (hloc.map_nonunit _ e)⟩)
  have hψ : ∀ χ, w (val (D.psi χ) ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) z J) = t ^ m χ := fun χ => by
    obtain ⟨u, hu⟩ := hm χ
    refine hv _ u _ (Eq.trans ?_ hu)
    have h : ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) ≫ D.xK χ = ρ.left ≫ (cP D _ χ).left := by
      rw [← Over.comp_left, comp_cP]
      exact (congrArg (· ≫ D.xK χ) (Category.id_comp _)).trans (Category.assoc _ _ _).symm
    have hj : J (((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) ≫ D.xK χ) = J₀ ((D.c χ).left P) :=
      (congrArg J h).trans ((eJ _).trans (congrArg (fun q => J₀ ((D.c χ).left q)) hc))
    have e := val_of (D.psi χ) _ z J (fun _ => J₀ ((D.c χ).left P)) fun _ => hj
    have m₀ : (𝟙 (Spec (CommRingCat.of (FractionRing R))) : _ ⟶ _) (closedPoint (FractionRing R)) ∈
        LB.wchart D.P.L (fun _ : PUnit => D.xK χ) fun _ => J₀ ((D.c χ).left P) := Set.mem_iInter.2 fun _ => by
      have a := hJ (((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) ≫ D.xK χ)
      rw [hj] at a
      have b : closedPoint (FractionRing R) = ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) z :=
        Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _
      exact (congrArg (fun q => D.xK χ q ∈ D.P.L.U (J₀ ((D.c χ).left P))) b).mpr a
    have n := sig_nat (algebraMap (FractionRing R) F) (𝟙 _) m₀ ((D.psi χ).s fun _ => J₀ ((D.c χ).left P))
    have c : (𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F = jFK (R := R) F ≫ 𝟙 _ :=
      (Category.id_comp _).trans (Category.comp_id _).symm
    exact (congrArg (fun u => (sig F u : F)) (e.trans (congrArg (fun q => gm q z _ _) c))).trans
      (congrArg Units.val n).symm
  refine ⟨fun y χ => ?_, fun χ => inj _ _ ((hψ _).symm.trans ((w_even ρ hJ w hint hE χ).trans (hψ _)))⟩
  obtain ⟨p, rfl⟩ := exists_qkPt (F := F) hM (Or.inl inferInstance) hB hk y
  obtain ⟨b, hb⟩ := exists_extend W φ' ρ rfl p.g.b
  obtain ⟨v, u, hu⟩ := eq_unit_mul_zpow_of_fixed T hϖ (sig F (charVal p.g χ z J) : F) (Units.ne_zero _) fun σ hσ => by
    have hσ' : σ.toRingHom.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F :=
      IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => by
        show σ (algebraMap (FractionRing R) F (algebraMap R _ r)) = algebraMap (FractionRing R) F (algebraMap R _ r)
        rw [← hφ]; exact hσ _ (φ r).2)
    obtain ⟨a, ha, hg⟩ := (equiv_iff hB _ _).1 (hfix σ hσ p _ ((qkExt_iff hB _ hσ' _ _).2 rfl))
    have a0 : a = 0 := by
      have : k • a = 0 := left_eq_add.1 ha
      exact (smul_eq_zero.1 (show (k : ℤ) • a = 0 by rw [natCast_zsmul, this])).resolve_left (Int.natCast_ne_zero.2 hk)
    rw [a0, map_zero, add_zero] at hg
    exact charVal_fixed σ.toRingHom hσ' p.g hg χ hJ
  have e₁ := w_nsmul ρ hJ w hint p.g b hb χ k
  rw [qk_nsmul hB, iota_val hB _ _ hJ, w_tau ρ hJ w hint, hψ, hψ, hψ, hv _ u v hu, ← zpow_natCast, ← zpow_mul,
    ← zpow_sub, ← zpow_sub] at e₁
  exact ⟨v, (inj _ _ e₁).trans (mul_comm _ _)⟩

/- English proof (translation)
Introduce `hL _ R _ _ _ _ _ D hB hE P hP n hn H y`. Use `choose J₀ h₀ using fun x : D.P.A.left => exists_chart D.P.isLB x`. Use `ReciprocityTheory.ChartRestriction.G.T0.regVert_valuationRing P.asIdeal hP` as an intermediate fact. Establish `hP0 : P.asIdeal ≠ ⊥` using `fun e => by rw [e, Ideal.height_bot] at hP; exact zero_ne_one hP`. Establish `: IsDiscreteValuationRing (Localization.AtPrime P.asIdeal)` using `((IsDiscreteValuationRing.TFAE (Localization.AtPrime P.asIdeal) (IsLocalization.AtPrime.not_isField R hP0 _)).out 0 1).2 this`.

Establish `: IsFractionRing (Localization.AtPrime P.asIdeal) (FractionRing R)` using `IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.asIdeal.primeCompl _ _`. Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime P.asIdeal)`. Use `choose m u hu using fun χ => IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hπ (psiLoc D χ (J₀ ((D.c χ).left P))).ne_zero`. Establish `key : ∀ j : ℕ, (∀ y χ, ((n ^ j : ℕ) : ℤ) ∣ m (y + χ) - m y - m χ) ∧ ∀ χ, m (-χ) = m χ` using `fun j => by`. Take `⟨T, _, f, hf, hi, hfix⟩` from `H j`.

Establish `hf' : T.subtype.comp f = (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))).comp (algebraMap (Localization.AtPrime P.asIdeal) (FractionRing R))` using `IsLocalization.ringHom_ext P.asIdeal.primeCompl (RingHom.ext fun r => (hf r).trans (congrArg _ (IsScalarTower.algebraMap_apply R (Localization.AtPrime P.asIdeal) (FractionRing R) r)))`. Establish `hf'' : ∀ x, (f x : AlgebraicClosure (FractionRing R)) = algebraMap (FractionRing R) _ (algebraMap _ (FractionRing R) x)` using `RingHom.congr_fun hf'`. Use `level_step hL.mulN hB hE P J₀ h₀ (n ^ j) (pow_ne_zero _ (by omega)) T (f.comp (algebraMap R _)) hf (fun r => ?_) (f π) (hi π hπ) m (fun χ => ⟨Units.map f.toMonoidHom (u χ), ?_⟩) hfix` and prove the remaining obligations. Rewrite using `[← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P.asIdeal) P.asIdeal r]`. Use `⟨fun h e => ?_, fun h e => h (e.map f)⟩` and prove the remaining obligations.

Rewrite `h` using `[hπ.maximalIdeal_eq, Ideal.mem_span_singleton]`. Conclude with `(hi π hπ).not_isUnit (isUnit_of_dvd_unit (map_dvd f h) e)`. Rewrite using `[hu, Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀, ← hf'', ← hf'']`. Both sides reduce to the same expression. Establish `add : ∀ y χ, m (y + χ) = m y + m χ` using `fun y χ => by`.

Establish `: m (y + χ) - m y - m χ = 0`. Use `Int.eq_zero_of_dvd_of_natAbs_lt_natAbs ((key (m (y + χ) - m y - m χ).natAbs).1 y χ) ?_` and prove the remaining obligations. Rewrite using `[Int.natAbs_natCast]`. Conclude with `Nat.lt_pow_self (by omega)`. Use linear arithmetic over natural numbers and integers.

Establish `m0 : m y = 0`. Establish `a` using `add 0 0`. Establish `b` using `add y (-y)`. Rewrite `a` using `[add_zero]`. Rewrite `b` using `[add_neg_cancel, (key 0).2]`.

Use linear arithmetic over natural numbers and integers. Establish `e` using `hu y`. Rewrite `e` using `[m0, zpow_zero, Units.smul_def, Algebra.smul_def, _root_.mul_one]`. Take `⟨⟨r, s⟩, hrs⟩` from `IsLocalization.surj P.asIdeal.primeCompl (u y : Localization.AtPrime P.asIdeal)`. Use `psiUnitOn_near y P _ (h₀ _) r s ?_ s.2 ?_` and prove the remaining obligations.

Conclude with `(IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P.asIdeal) P.asIdeal r).1 (hrs ▸ (u y).isUnit.mul (IsLocalization.map_units _ s))`. Rewrite using `[e, IsScalarTower.algebraMap_apply R (Localization.AtPrime P.asIdeal) (FractionRing R), IsScalarTower.algebraMap_apply R (Localization.AtPrime P.asIdeal) (FractionRing R) r, ← map_mul]`. Conclude with `congrArg _ hrs`.
-/
theorem psiUnitOn_of_unramified : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (D : DegPre R), D.TauBimult → D.PsiEven → ∀ (P : PrimeSpectrum R), P.asIdeal.height = 1 → ∀ (n : ℕ), 2 ≤ n → (∀ (j : ℕ), ∃ (T' : Subring (AlgebraicClosure (FractionRing R))) (_ : IsDiscreteValuationRing T') (f : Localization.AtPrime P.asIdeal →+* T'), (∀ r : R, (f (algebraMap R _ r) : AlgebraicClosure (FractionRing R)) = algebraMap (FractionRing R) _ (algebraMap R _ r)) ∧ (∀ π, Irreducible π → Irreducible (f π)) ∧ ∀ (σ : AlgebraicClosure (FractionRing R) ≃+* AlgebraicClosure (FractionRing R)), (∀ x ∈ T', σ x = x) → ∀ p q : QkPt D (AlgebraicClosure (FractionRing R)) (n ^ j), QkExt σ.toRingHom p q → QkPt.Equiv D _ p q) → ∀ y, ∃ V : (Sp R).Opens, P ∈ V ∧ PsiUnitOn D y V := by
  intro hL _ R _ _ _ _ _ D hB hE P hP n hn H y
  choose J₀ h₀ using fun x : D.P.A.left => exists_chart D.P.isLB x
  have := ReciprocityTheory.ChartRestriction.G.T0.regVert_valuationRing P.asIdeal hP
  have hP0 : P.asIdeal ≠ ⊥ := fun e => by rw [e, Ideal.height_bot] at hP; exact zero_ne_one hP
  have : IsDiscreteValuationRing (Localization.AtPrime P.asIdeal) :=
    ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P.asIdeal)
      (IsLocalization.AtPrime.not_isField R hP0 _)).out 0 1).2 this
  have : IsFractionRing (Localization.AtPrime P.asIdeal) (FractionRing R) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.asIdeal.primeCompl _ _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime P.asIdeal)
  choose m u hu using fun χ => IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hπ
    (psiLoc D χ (J₀ ((D.c χ).left P))).ne_zero
  have key : ∀ j : ℕ, (∀ y χ, ((n ^ j : ℕ) : ℤ) ∣ m (y + χ) - m y - m χ) ∧ ∀ χ, m (-χ) = m χ := fun j => by
    obtain ⟨T, _, f, hf, hi, hfix⟩ := H j
    have hf' : T.subtype.comp f = (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))).comp
        (algebraMap (Localization.AtPrime P.asIdeal) (FractionRing R)) :=
      IsLocalization.ringHom_ext P.asIdeal.primeCompl (RingHom.ext fun r => (hf r).trans
        (congrArg _ (IsScalarTower.algebraMap_apply R (Localization.AtPrime P.asIdeal) (FractionRing R) r)))
    have hf'' : ∀ x, (f x : AlgebraicClosure (FractionRing R)) =
        algebraMap (FractionRing R) _ (algebraMap _ (FractionRing R) x) := RingHom.congr_fun hf'
    refine level_step hL.mulN hB hE P J₀ h₀ (n ^ j) (pow_ne_zero _ (by omega)) T (f.comp (algebraMap R _)) hf
      (fun r => ?_) (f π) (hi π hπ) m (fun χ => ⟨Units.map f.toMonoidHom (u χ), ?_⟩) hfix
    · rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P.asIdeal) P.asIdeal r]
      refine ⟨fun h e => ?_, fun h e => h (e.map f)⟩
      rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at h
      exact (hi π hπ).not_isUnit (isUnit_of_dvd_unit (map_dvd f h) e)
    · rw [hu, Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀, ← hf'', ← hf'']
      rfl
  have add : ∀ y χ, m (y + χ) = m y + m χ := fun y χ => by
    have : m (y + χ) - m y - m χ = 0 := by
      refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs ((key (m (y + χ) - m y - m χ).natAbs).1 y χ) ?_
      rw [Int.natAbs_natCast]
      exact Nat.lt_pow_self (by omega)
    omega
  have m0 : m y = 0 := by
    have a := add 0 0
    have b := add y (-y)
    rw [add_zero] at a
    rw [add_neg_cancel, (key 0).2] at b
    omega
  have e := hu y
  rw [m0, zpow_zero, Units.smul_def, Algebra.smul_def, _root_.mul_one] at e
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj P.asIdeal.primeCompl (u y : Localization.AtPrime P.asIdeal)
  refine psiUnitOn_near y P _ (h₀ _) r s ?_ s.2 ?_
  · exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P.asIdeal) P.asIdeal r).1
      (hrs ▸ (u y).isUnit.mul (IsLocalization.map_units _ s))
  · rw [e, IsScalarTower.algebraMap_apply R (Localization.AtPrime P.asIdeal) (FractionRing R),
      IsScalarTower.algebraMap_apply R (Localization.AtPrime P.asIdeal) (FractionRing R) r, ← map_mul]
    exact congrArg _ hrs

end GlobalTheory.UnramTorsion
