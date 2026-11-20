import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PeriodBalance

variable {R : Type} [CommRing R] [IsDomain R]

def cst (ξ : Spec (CommRingCat.of (FractionRing R))) :
    R →+* (Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ :=
  (((Spec (CommRingCat.of (FractionRing R))).presheaf.germ ⊤ ξ trivial).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom).comp (algebraMap R (FractionRing R))

/- English proof (translation)
The claim follows from `(RingHom.injective (((Spec (CommRingCat.of (FractionRing R))).presheaf.germ ⊤ ξ trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom)).comp (IsFractionRing.injective R (FractionRing R))`.
-/
theorem cst_injective (ξ : Spec (CommRingCat.of (FractionRing R))) : Function.Injective (cst ξ) :=
  (RingHom.injective (((Spec (CommRingCat.of (FractionRing R))).presheaf.germ ⊤ ξ trivial).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom)).comp
    (IsFractionRing.injective R (FractionRing R))

/- English proof (translation)
Establish `hnat` using `congrArg (fun f => (CommRingCat.Hom.hom f) r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hnat`. Conclude with `congrArg ((Spec (CommRingCat.of (FractionRing R))).presheaf.germ ⊤ ξ trivial).hom hnat`.
-/
theorem cst_eq (ξ : Spec (CommRingCat.of (FractionRing R))) (r : R) :
    cst ξ r = ((Spec (CommRingCat.of (FractionRing R))).presheaf.germ ⊤ ξ trivial).hom
      (((jK R).app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by
  have hnat := congrArg (fun f => (CommRingCat.Hom.hom f) r)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hnat
  exact congrArg ((Spec (CommRingCat.of (FractionRing R))).presheaf.germ ⊤ ξ trivial).hom hnat

variable [IsLocalRing R]

/- English proof (translation)
Take `rfl` from `DVR.eq_top_of_closedPoint_mem U hU`. Use `⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom a, ?_⟩` and prove the remaining obligations. Rewrite using `[gm_val _ ξ ⊤ trivial, cst_eq]`. Use `congrArg ((Spec (CommRingCat.of (FractionRing R))).presheaf.germ ⊤ ξ trivial).hom (congrArg ((jK R).app ⊤).hom ?_)` and prove the remaining obligations. Conclude with `(Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of R)) a.val).symm`.
-/
theorem unit_gm (ξ : Spec (CommRingCat.of (FractionRing R))) (U : (Spec (CommRingCat.of R)).Opens)
    (hU : (closedPoint R : Spec (CommRingCat.of R)) ∈ U) (a : Γ(Spec (CommRingCat.of R), U)ˣ) :
    ∃ u : Rˣ, (gm (jK R) ξ U a).val = cst ξ u := by
  obtain rfl := DVR.eq_top_of_closedPoint_mem U hU
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom a, ?_⟩
  rw [gm_val _ ξ ⊤ trivial, cst_eq]
  refine congrArg ((Spec (CommRingCat.of (FractionRing R))).presheaf.germ ⊤ ξ trivial).hom
    (congrArg ((jK R).app ⊤).hom ?_)
  exact (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of R)) a.val).symm

/- English proof (translation)
Establish `h : p (jK R ξ) ∈ U`. Use `DVR.eq_top_of_closedPoint_mem (p ⁻¹ᵁ U) hU` as an intermediate fact. Establish `h2 : jK R ξ ∈ p ⁻¹ᵁ U` using `by rw [this]; trivial`. Conclude with `h2`. Rewrite using `[← gm_pull (jK R) p ξ U h]`.

Conclude with `unit_gm ξ _ hU _`.
-/
theorem unit_gm' (ξ : Spec (CommRingCat.of (FractionRing R))) {X : Scheme.{0}} (p : Spec (CommRingCat.of R) ⟶ X)
    (U : X.Opens) (hU : p (closedPoint R) ∈ U) (a : Γ(X, U)ˣ) :
    ∃ u : Rˣ, (gm (jK R ≫ p) ξ U a).val = cst ξ u := by
  have h : p (jK R ξ) ∈ U := by
    have := DVR.eq_top_of_closedPoint_mem (p ⁻¹ᵁ U) hU
    have h2 : jK R ξ ∈ p ⁻¹ᵁ U := by rw [this]; trivial
    exact h2
  rw [← gm_pull (jK R) p ξ U h]
  exact unit_gm ξ _ hU _

/- English proof (translation)
Use `haveI : IsDominant (jK R) := DVR.isDominant_jK`. Use `choose pick hpk using fun p : Spec (CommRingCat.of R) ⟶ X => exists_chart hL (p (closedPoint R))`. Take `⟨J, hJ, e⟩` from `exists_good L hL ξ (K := {p : Spec (CommRingCat.of R) ⟶ X // p ≫ s = 𝟙 _}) (fun p => jK R ≫ p.1) (fun p => pick p.1) (fun a b h => congrArg pick (ext_of_isDominant_of_isSeparated s (a.2.trans b.2.symm) (jK R) h)) (fun p => by`. Use `DVR.eq_top_of_closedPoint_mem (p.1 ⁻¹ᵁ L.U (pick p.1)) (hpk p.1)` as an intermediate fact. Establish `h2 : jK R ξ ∈ p.1 ⁻¹ᵁ L.U (pick p.1)` using `by rw [this]; trivial`.

Conclude with `h2)`. Conclude with `⟨J, hJ, fun p hp => (e ⟨p, hp⟩).symm ▸ hpk p⟩`.
-/
theorem exists_good_integral (ξ : Spec (CommRingCat.of (FractionRing R))) {X : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    (s : X ⟶ Spec (CommRingCat.of R)) [IsSeparated s] :
    ∃ J, Good L ξ J ∧ ∀ p : Spec (CommRingCat.of R) ⟶ X, p ≫ s = 𝟙 _ →
      p (closedPoint R) ∈ L.U (J (jK R ≫ p)) := by
  haveI : IsDominant (jK R) := DVR.isDominant_jK
  choose pick hpk using fun p : Spec (CommRingCat.of R) ⟶ X => exists_chart hL (p (closedPoint R))
  obtain ⟨J, hJ, e⟩ := exists_good L hL ξ (K := {p : Spec (CommRingCat.of R) ⟶ X // p ≫ s = 𝟙 _})
    (fun p => jK R ≫ p.1) (fun p => pick p.1)
    (fun a b h => congrArg pick (ext_of_isDominant_of_isSeparated s (a.2.trans b.2.symm) (jK R) h))
    (fun p => by
      have := DVR.eq_top_of_closedPoint_mem (p.1 ⁻¹ᵁ L.U (pick p.1)) (hpk p.1)
      have h2 : jK R ξ ∈ p.1 ⁻¹ᵁ L.U (pick p.1) := by rw [this]; trivial
      exact h2)
  exact ⟨J, hJ, fun p hp => (e ⟨p, hp⟩).symm ▸ hpk p⟩

/- English proof (translation)
Take `⟨j, hj, h, e⟩` from `hr`. Establish `hx : D.xK χ = jK R ≫ (D.c χ).left` using `DVR.QForm.ptK_eq D χ`. Establish `hm : (𝟙 (Spec (CommRingCat.of (FractionRing R))) : _ ⟶ _) ξ ∈ LB.wchart D.P.L (fun _ : PUnit => D.xK χ) j` using `h (show ξ ∈ jK R ⁻¹ᵁ ⊤ from trivial)`. Establish `t` using `gen_trans (D.psi_gen χ) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ (hJ.mem (fun _ : PUnit => D.xK χ) (𝟙 _)) hm`. Establish `h1 : (gm (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ (LB.wchart D.P.L (fun _ : PUnit => D.xK χ) j) ((D.psi χ).s j)).val = cst ξ r`.

Use `(gm_val _ ξ _ hm _).trans (Eq.trans ?_ (cst_eq ξ r).symm)` and prove the remaining obligations. Establish `e' : ((jK R).app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = _` using `Eq.trans ?_ e`. Rewrite using `[e']`. Conclude with `(TopCat.Presheaf.germ_res_apply (Spec (CommRingCat.of (FractionRing R))).presheaf (homOfLE h) ξ trivial _).symm`. Use `congr 1`.

Take `⟨u, hu⟩` from `unit_gm' ξ (D.c χ).left (D.P.L.U (J (jK R ≫ (D.c χ).left)) ⊓ D.P.L.U (j PUnit.unit)) ⟨hJc _ (Over.w _), hj trivial⟩ (D.P.L.g (J (jK R ≫ (D.c χ).left)) (j PUnit.unit))`. Establish `h2 : trF (L` using `D.P.L) (fun _ : PUnit => D.xK χ) (fun _ => -1) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ (fun _ => J (𝟙 _ ≫ D.xK χ)) j = (gm (jK R ≫ (D.c χ).left) ξ _ (D.P.L.g (J (jK R ≫ (D.c χ).left)) (j PUnit.unit)))⁻¹ := by`. Rewrite using `[trF, Fintype.prod_unique, zpow_neg_one, Category.id_comp, hx]`. Use `⟨u⁻¹, (congrArg Units.val t).trans ?_⟩` and prove the remaining obligations. Use `(Units.val_mul _ _).trans ?_` and prove the remaining obligations.

Rewrite using `[map_mul]`. Use `congrArg₂ (· * ·) ?_ h1` and prove the remaining obligations. Use `(congrArg Units.val h2).trans ?_` and prove the remaining obligations. Rewrite using `[Units.inv_eq_of_mul_eq_one_left]`. Rewrite using `[hu, ← map_mul, Units.inv_mul, map_one]`.
-/
theorem val_psi (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJ : Good D.P.L ξ J)
    (hJc : ∀ p : Spec (CommRingCat.of R) ⟶ D.P.A.left, p ≫ D.P.A.hom = 𝟙 _ →
      p (closedPoint R) ∈ D.P.L.U (J (jK R ≫ p))) (χ : D.X) (r : R) (hr : PsiCoord D χ r) :
    ∃ u : Rˣ, (val (D.psi χ) (𝟙 _) ξ J).val = cst ξ (u * r) := by
  obtain ⟨j, hj, h, e⟩ := hr
  have hx : D.xK χ = jK R ≫ (D.c χ).left := DVR.QForm.ptK_eq D χ
  have hm : (𝟙 (Spec (CommRingCat.of (FractionRing R))) : _ ⟶ _) ξ ∈ LB.wchart D.P.L (fun _ : PUnit => D.xK χ) j :=
    h (show ξ ∈ jK R ⁻¹ᵁ ⊤ from trivial)
  have t := gen_trans (D.psi_gen χ) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ
    (hJ.mem (fun _ : PUnit => D.xK χ) (𝟙 _)) hm
  have h1 : (gm (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ
      (LB.wchart D.P.L (fun _ : PUnit => D.xK χ) j) ((D.psi χ).s j)).val = cst ξ r := by
    refine (gm_val _ ξ _ hm _).trans (Eq.trans ?_ (cst_eq ξ r).symm)
    have e' : ((jK R).app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = _ := Eq.trans ?_ e
    · rw [e']
      exact (TopCat.Presheaf.germ_res_apply (Spec (CommRingCat.of (FractionRing R))).presheaf (homOfLE h) ξ trivial _).symm
    · congr 1
  obtain ⟨u, hu⟩ := unit_gm' ξ (D.c χ).left (D.P.L.U (J (jK R ≫ (D.c χ).left)) ⊓ D.P.L.U (j PUnit.unit))
    ⟨hJc _ (Over.w _), hj trivial⟩ (D.P.L.g (J (jK R ≫ (D.c χ).left)) (j PUnit.unit))
  have h2 : trF (L := D.P.L) (fun _ : PUnit => D.xK χ) (fun _ => -1) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ
      (fun _ => J (𝟙 _ ≫ D.xK χ)) j = (gm (jK R ≫ (D.c χ).left) ξ _ (D.P.L.g (J (jK R ≫ (D.c χ).left)) (j PUnit.unit)))⁻¹ := by
    rw [trF, Fintype.prod_unique, zpow_neg_one, Category.id_comp, hx]
  refine ⟨u⁻¹, (congrArg Units.val t).trans ?_⟩
  refine (Units.val_mul _ _).trans ?_
  rw [map_mul]
  refine congrArg₂ (· * ·) ?_ h1
  refine (congrArg Units.val h2).trans ?_
  rw [Units.inv_eq_of_mul_eq_one_left]
  rw [hu, ← map_mul, Units.inv_mul, map_one]

omit [IsLocalRing R] in
/- English proof (translation)
The claim follows from `(val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))`.
-/
theorem val_tau (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJ : Good D.P.L ξ J) (a b : D.X) :
    val (D.tau a b) (𝟙 _) ξ J = val (D.psi (a + b)) (𝟙 _) ξ J * (val (D.psi a) (𝟙 _) ξ J)⁻¹ *
      (val (D.psi b) (𝟙 _) ξ J)⁻¹ * (val D.rigK (𝟙 _) ξ J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

/- English proof (translation)
Use `haveI := ρ.onB.hom x`. Use `haveI := ρ.onB.hom (star x)`. Use `haveI : IsProper D.P.A.hom := D.P.isAb.proper`. Take `⟨w, hw, h₀⟩` from `exists_ros GlobalTheory.globalFns_holds D.P.isAb D.P.isLB _ _ (ρ.onB.rosati x)`. Establish `hc` using `ρ.tau_bal x w hw h₀ a b`.

Take `⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R)))` from `⟨⟨⊥, Ideal.isPrime_bot⟩⟩`. Take `⟨J, hJ, hJc⟩` from `exists_good_integral ξ D.P.isLB D.P.A.hom`. Establish `e` using `(val_mul hJ _ _ _).symm.trans (val_corr hJ hc (𝟙 _))`. Establish `e1` using `val_tau D ξ hJ (x • a) b`. Establish `e2` using `val_tau D ξ hJ a (star x • b)`.

Establish `e3` using `val_pull hJ w (D.pt2 a b) (𝟙 _)`. Establish `hp : 𝟙 _ ≫ D.pt2 a b = jK R ≫ (lift (D.c a) (D.c b)).left`. Simplify using `[DegPre.pt2, ← CartesianMonoidalCategory.comp_lift]`. Choose the witnesses or unpack the hypotheses as in `⟨v, hv⟩ : ∃ v : Rˣ, (val w (jK R ≫ (lift (D.c a) (D.c b)).left) ξ J).val = cst ξ v := by`. Use `unit_gm' ξ _ _ (Set.mem_iInter.2 fun k => ?_) _` and prove the remaining obligations.

Apply the tactic sequence `obtain ⟨q, hq⟩ : ∃ q : D.P.A ⊗ D.P.A ⟶ D.P.A, rosatiφ D.P.A (ρ.onB.act x) (ρ.onB.act (star x)) k = q.left := by fin_cases k <;> exact ⟨_, rfl⟩`. Use `hJc ((lift (D.c a) (D.c b)).left ≫ rosatiφ D.P.A (ρ.onB.act x) (ρ.onB.act (star x)) k) (by` as an intermediate fact. Rewrite using `[hq, Category.assoc, Over.w q, Over.w]`. Use the proof step `rfl)`. Conclude with `this`.

Establish `e3'` using `e3.trans (congrArg (fun q => val w q ξ J) hp)`. Establish `e4` using `(congrArg₂ (@HMul.hMul _ _ ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ instHMul) e1 e3').symm.trans (e.trans e2)`. Take `⟨u₁, g₁⟩` from `val_psi D ξ hJ hJc _ _ h₁`. Take `⟨u₂, g₂⟩` from `val_psi D ξ hJ hJc _ _ h₂`. Take `⟨u₃, g₃⟩` from `val_psi D ξ hJ hJc _ _ h₃`.

Take `⟨v₁, f₁⟩` from `val_psi D ξ hJ hJc _ _ k₁`. Take `⟨v₂, f₂⟩` from `val_psi D ξ hJ hJc _ _ k₂`. Take `⟨v₃, f₃⟩` from `val_psi D ξ hJ hJc _ _ k₃`. Establish `key : ∀ {G : Type} [CommGroup G] (A₁ A₂ A₃ B₁ B₂ B₃ Z W : G), A₁ * A₂⁻¹ * A₃⁻¹ * Z⁻¹ * W = B₁ * B₂⁻¹ * B₃⁻¹ * Z⁻¹ → W * A₁ * B₂ * B₃ = B₁ * A₂ * A₃`. Introduce `G _ A₁ A₂ A₃ B₁ B₂ B₃ Z W h`.

Establish `h'` using `congrArg Additive.ofMul h`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv] at h' ⊢`. Rewrite `h'`, the goal using `[← sub_eq_zero]`. Use `Eq.trans ?_ h'` and prove the remaining obligations.

Normalize the expressions using the abelian group laws. Establish `e5` using `congrArg Units.val (key _ _ _ _ _ _ _ _ e4)`. Establish `e6 : cst ξ (v * (u₁ * r₁) * (v₂ * s₂) * (v₃ * s₃)) = cst ξ ((v₁ * s₁) * (u₂ * r₂) * (u₃ * r₃))`. Rewrite using `[map_mul, map_mul, map_mul, map_mul (cst ξ) (_ * _) (_ * r₃), map_mul (cst ξ) (_ * s₁), ← hv, ← g₁, ← g₂, ← g₃, ← f₁, ← f₂, ← f₃]`. Conclude with `e5`.

Establish `e7` using `cst_injective ξ e6`. Use `⟨(v₁ * u₂ * u₃)⁻¹ * (v * u₁ * v₂ * v₃), ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, mul_assoc, Units.inv_mul_eq_iff_eq_mul]`. Use `push_cast`. Take the linear combination `e7`.
-/
theorem coord_balance {O : Type} [Ring O] [StarRing O] (D : DegPre R) [Module O D.X] (ρ : D.OAct O) (x : O)
    (a b : D.X) {r₁ r₂ r₃ s₁ s₂ s₃ : R} (h₁ : PsiCoord D (x • a + b) r₁) (h₂ : PsiCoord D (x • a) r₂)
    (h₃ : PsiCoord D b r₃) (k₁ : PsiCoord D (a + star x • b) s₁) (k₂ : PsiCoord D a s₂)
    (k₃ : PsiCoord D (star x • b) s₃) : ∃ u : Rˣ, u * (r₁ * s₂ * s₃) = s₁ * r₂ * r₃ := by
  haveI := ρ.onB.hom x
  haveI := ρ.onB.hom (star x)
  haveI : IsProper D.P.A.hom := D.P.isAb.proper
  obtain ⟨w, hw, h₀⟩ := exists_ros GlobalTheory.globalFns_holds D.P.isAb D.P.isLB _ _ (ρ.onB.rosati x)
  have hc := ρ.tau_bal x w hw h₀ a b
  obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨J, hJ, hJc⟩ := exists_good_integral ξ D.P.isLB D.P.A.hom
  have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ hc (𝟙 _))
  have e1 := val_tau D ξ hJ (x • a) b
  have e2 := val_tau D ξ hJ a (star x • b)
  have e3 := val_pull hJ w (D.pt2 a b) (𝟙 _)
  have hp : 𝟙 _ ≫ D.pt2 a b = jK R ≫ (lift (D.c a) (D.c b)).left := by
    simp [DegPre.pt2, ← CartesianMonoidalCategory.comp_lift]
  obtain ⟨v, hv⟩ : ∃ v : Rˣ, (val w (jK R ≫ (lift (D.c a) (D.c b)).left) ξ J).val = cst ξ v := by
    refine unit_gm' ξ _ _ (Set.mem_iInter.2 fun k => ?_) _
    obtain ⟨q, hq⟩ : ∃ q : D.P.A ⊗ D.P.A ⟶ D.P.A, rosatiφ D.P.A (ρ.onB.act x) (ρ.onB.act (star x)) k = q.left := by
      fin_cases k <;> exact ⟨_, rfl⟩
    have := hJc ((lift (D.c a) (D.c b)).left ≫ rosatiφ D.P.A (ρ.onB.act x) (ρ.onB.act (star x)) k) (by
      rw [hq, Category.assoc, Over.w q, Over.w]; rfl)
    exact this
  have e3' := e3.trans (congrArg (fun q => val w q ξ J) hp)
  have e4 := (congrArg₂ (@HMul.hMul _ _ ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ instHMul)
    e1 e3').symm.trans (e.trans e2)
  obtain ⟨u₁, g₁⟩ := val_psi D ξ hJ hJc _ _ h₁
  obtain ⟨u₂, g₂⟩ := val_psi D ξ hJ hJc _ _ h₂
  obtain ⟨u₃, g₃⟩ := val_psi D ξ hJ hJc _ _ h₃
  obtain ⟨v₁, f₁⟩ := val_psi D ξ hJ hJc _ _ k₁
  obtain ⟨v₂, f₂⟩ := val_psi D ξ hJ hJc _ _ k₂
  obtain ⟨v₃, f₃⟩ := val_psi D ξ hJ hJc _ _ k₃
  have key : ∀ {G : Type} [CommGroup G] (A₁ A₂ A₃ B₁ B₂ B₃ Z W : G),
      A₁ * A₂⁻¹ * A₃⁻¹ * Z⁻¹ * W = B₁ * B₂⁻¹ * B₃⁻¹ * Z⁻¹ → W * A₁ * B₂ * B₃ = B₁ * A₂ * A₃ := by
    intro G _ A₁ A₂ A₃ B₁ B₂ B₃ Z W h
    have h' := congrArg Additive.ofMul h
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv] at h' ⊢
    rw [← sub_eq_zero] at h' ⊢
    refine Eq.trans ?_ h'
    abel
  have e5 := congrArg Units.val (key _ _ _ _ _ _ _ _ e4)
  have e6 : cst ξ (v * (u₁ * r₁) * (v₂ * s₂) * (v₃ * s₃)) = cst ξ ((v₁ * s₁) * (u₂ * r₂) * (u₃ * r₃)) := by
    rw [map_mul, map_mul, map_mul, map_mul (cst ξ) (_ * _) (_ * r₃), map_mul (cst ξ) (_ * s₁), ← hv, ← g₁, ← g₂,
      ← g₃, ← f₁, ← f₂, ← f₃]
    exact e5
  have e7 := cst_injective ξ e6
  refine ⟨(v₁ * u₂ * u₃)⁻¹ * (v * u₁ * v₂ * v₃), ?_⟩
  rw [Units.val_mul, mul_assoc, Units.inv_mul_eq_iff_eq_mul]
  push_cast
  linear_combination e7

/- English proof (translation)
Establish `h : ‖f u‖ * ‖f (u⁻¹ : Rˣ)‖ = 1` using `by rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]`. Establish `h1` using `hf u`. Establish `h2` using `hf (u⁻¹ : Rˣ)`. Establish `h3` using `norm_nonneg (f u)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem norm_unit {R C : Type} [CommRing R] [NormedField C] (f : R →+* C) (hf : ∀ a, ‖f a‖ ≤ 1) (u : Rˣ) :
    ‖f u‖ = 1 := by
  have h : ‖f u‖ * ‖f (u⁻¹ : Rˣ)‖ = 1 := by rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
  have h1 := hf u
  have h2 := hf (u⁻¹ : Rˣ)
  have h3 := norm_nonneg (f u)
  nlinarith

/- English proof (translation)
Introduce `E _ _ _ H R _ _ _ _ t U C _ _ f p hR hf hne x a b`. Use `letI := H.starRing`. Establish `hex : ∀ χ, ∃ r, PsiCoord U.D.toPre χ r` using `fun χ => ((GlobalTheory.PsiCoordLocal.main R U.D hR χ).1).imp fun _ h => h.1`. Establish `hv : ∀ χ, vPsiAt U.D.toPre f p χ = -Real.logb p ‖f (hex χ).choose‖` using `fun χ => dif_pos (hex χ)`. Establish `hn : ∀ χ, ‖f (hex χ).choose‖ ≠ 0` using `fun χ => norm_ne_zero_iff.2 (hne χ _ (hex χ).choose_spec)`.

Take `⟨u, hu⟩` from `coord_balance U.D.toPre U.oD x a b (hex (x • a + b)).choose_spec (hex (x • a)).choose_spec (hex b).choose_spec (hex (a + H.bar x • b)).choose_spec (hex a).choose_spec (hex (H.bar x • b)).choose_spec`. Establish `h` using `congrArg (fun r => Real.logb p ‖f r‖) hu`. Simplify using `only [map_mul, norm_mul, norm_unit f hf u, one_mul] at h`. Rewrite `h` using `[Real.logb_mul (mul_ne_zero (hn _) (hn _)) (hn _), Real.logb_mul (mul_ne_zero (hn _) (hn _)) (hn _), Real.logb_mul (hn _) (hn _), Real.logb_mul (hn _) (hn _)]`. Simplify using `only [betaAt, hv]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem betaAt_balanced : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (t : SAB H (Sp R)) (U : PELUnif (maximalIdeal R) t) (C : Type) [NormedField C] [IsUltrametricDist C] (f : R →+* C) (p : ℕ), IsIntegrallyClosed R → (∀ a, ‖f a‖ ≤ 1) → (∀ χ r, PsiCoord U.D.toPre χ r → f r ≠ 0) → ∀ (x : 𝓞 E) a b, betaAt U.D.toPre f p (x • a) b = betaAt U.D.toPre f p a (H.bar x • b) := by
  intro E _ _ _ H R _ _ _ _ t U C _ _ f p hR hf hne x a b
  letI := H.starRing
  have hex : ∀ χ, ∃ r, PsiCoord U.D.toPre χ r := fun χ =>
    ((GlobalTheory.PsiCoordLocal.main R U.D hR χ).1).imp fun _ h => h.1
  have hv : ∀ χ, vPsiAt U.D.toPre f p χ = -Real.logb p ‖f (hex χ).choose‖ := fun χ => dif_pos (hex χ)
  have hn : ∀ χ, ‖f (hex χ).choose‖ ≠ 0 := fun χ => norm_ne_zero_iff.2 (hne χ _ (hex χ).choose_spec)
  obtain ⟨u, hu⟩ := coord_balance U.D.toPre U.oD x a b (hex (x • a + b)).choose_spec (hex (x • a)).choose_spec
    (hex b).choose_spec (hex (a + H.bar x • b)).choose_spec (hex a).choose_spec (hex (H.bar x • b)).choose_spec
  have h := congrArg (fun r => Real.logb p ‖f r‖) hu
  simp only [map_mul, norm_mul, norm_unit f hf u, one_mul] at h
  rw [Real.logb_mul (mul_ne_zero (hn _) (hn _)) (hn _), Real.logb_mul (mul_ne_zero (hn _) (hn _)) (hn _),
    Real.logb_mul (hn _) (hn _), Real.logb_mul (hn _) (hn _)] at h
  simp only [betaAt, hv]
  linarith

end GlobalTheory.PeriodBalance
