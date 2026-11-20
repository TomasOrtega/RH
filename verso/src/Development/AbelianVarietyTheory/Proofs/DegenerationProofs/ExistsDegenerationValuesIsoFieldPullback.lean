import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsQkPullEquiv
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitGeneratingSectionPullbackFieldStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.ValuesPullIso
open GlobalTheory.TorusExt GlobalTheory.ArcPull GlobalTheory.ArcTransport
open GlobalTheory.PsiEvenPull (proj)
open ReciprocityTheory.ChartRestriction.G.DVR (cP)

section Val
variable {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

/- English proof (translation)
The claim follows from `((gs_unit r z _ (hJ.mem φ r) _).symm.trans (gs_eq_stalkConst r z (fun w _ => (Subsingleton.elim (α := PrimeSpectrum F) z w) ▸ hJ.mem φ r) _)).symm`.
-/
theorem const_vF (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) {z : Sp F} {J : (Sp F ⟶ X) → L.ι} (hJ : Good L z J) :
    stalkConst z (vF t r J) = (val t r z J).val :=
  ((gs_unit r z _ (hJ.mem φ r) _).symm.trans (gs_eq_stalkConst r z
    (fun w _ => (Subsingleton.elim (α := PrimeSpectrum F) z w) ▸ hJ.mem φ r) _)).symm

/- English proof (translation)
The claim follows from `(gs_eq_stalkConst r z (fun w _ => (Subsingleton.elim (α := PrimeSpectrum F) z w) ▸ hJ.mem φ r) _).symm`.
-/
theorem const_sF (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) {z : Sp F} {J : (Sp F ⟶ X) → L.ι} (hJ : Good L z J) :
    stalkConst z (sF s r J) = sval s r z J :=
  (gs_eq_stalkConst r z (fun w _ => (Subsingleton.elim (α := PrimeSpectrum F) z w) ▸ hJ.mem φ r) _).symm

/- English proof (translation)
The claim follows from `Units.ext ((congrArg (stalkConst z) h).trans (const_vF t r hJ))`.
-/
theorem units_of_vF {t : LB.Gen (LB.LinComb L φ ε)} {r : Sp F ⟶ Y} {z : Sp F} {J : (Sp F ⟶ X) → L.ι}
    (hJ : Good L z J) {u : Fˣ} (h : (u : F) = vF t r J) : stalkUnits z u = val t r z J :=
  Units.ext ((congrArg (stalkConst z) h).trans (const_vF t r hJ))
end Val

section Num
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {N : NumD F} (ν : NumOf D F N) (z : Sp F)

/- English proof (translation)
Introduce `ψ` and use `ν.good ψ trivial`.
-/
theorem good : Good D.P.L z ν.J := fun ψ => ν.good ψ trivial

/- English proof (translation)
The claim follows from `units_of_vF (good ν z) (ν.θ_eq x y u)`.
-/
theorem stalk_θ (x y u : N.A) : stalkUnits z (N.θ x y u) = thS D z ν.J (ν.eA x) (ν.eA y) (ν.eA u) :=
  units_of_vF (good ν z) (ν.θ_eq x y u)

/- English proof (translation)
The claim follows from `units_of_vF (good ν z) (ν.σ_eq x)`.
-/
theorem stalk_σ (x : N.A) : stalkUnits z (N.σ x) = val (Z := Sp F) D.sym (ν.eA x).left z ν.J :=
  units_of_vF (good ν z) (ν.σ_eq x)

/- English proof (translation)
The claim follows from `(const_vF _ _ (good ν z)).trans (congrArg Units.val (val_pull (good ν z) _ _ _).symm)`.
-/
theorem const_rig : stalkConst z (vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig
    (TF (R := R) F).hom ν.J) = (val (Z := Sp F) D.rigK (jFK (R := R) F) z ν.J).val :=
  (const_vF _ _ (good ν z)).trans (congrArg Units.val (val_pull (good ν z) _ _ _).symm)

/- English proof (translation)
The claim follows from `Units.ext ((congrArg (stalkConst z) (ν.ψ_eq χ)).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) (const_vF _ _ (good ν z)) (const_rig ν z))))`.
-/
theorem stalk_ψ (χ : N.X) : stalkUnits z (N.ψ χ) =
    val (Z := Sp F) (D.psi (ν.eX χ)) (jFK (R := R) F) z ν.J * val (Z := Sp F) D.rigK (jFK (R := R) F) z ν.J :=
  Units.ext ((congrArg (stalkConst z) (ν.ψ_eq χ)).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (const_vF _ _ (good ν z)) (const_rig ν z))))

/- English proof (translation)
The claim follows from `(congrArg _ (const_rig ν z).symm).trans ((map_mul _ _ _).symm.trans ((congrArg (stalkConst z) (ν.th_eq x)).trans (const_sF _ _ (good ν z))))`.
-/
theorem stalk_th (x : N.A) : stalkConst z (N.th x) * (val (Z := Sp F) D.rigK (jFK (R := R) F) z ν.J).val =
    sval (Z := Sp F) ν.th (ν.eA x).left z ν.J :=
  (congrArg _ (const_rig ν z).symm).trans ((map_mul _ _ _).symm.trans
    ((congrArg (stalkConst z) (ν.th_eq x)).trans (const_sF _ _ (good ν z))))

/- English proof (translation)
The claim follows from `units_of_vF (good ν z) (h.2 χ)`.
-/
theorem stalk_pt {g : GtPtF D F} {c : N.Gt} (h : ν.Pt g c) (χ : N.X) :
    stalkUnits z (c.s χ) = val (Z := Sp F) (g.s (ν.eX χ)) (𝟙 (Sp F)) z ν.J :=
  units_of_vF (good ν z) (h.2 χ)
end Num

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} (hD : IsPullDeg φ D D') {F : Type} [Field F] [Algebra (FractionRing R) F]
  [Algebra (FractionRing R') F]

/- English proof (translation)
Introduce `a b h` and use `IsFractionRing.injective R (FractionRing R) ((algebraMap (FractionRing R) F).injective ((hF a).trans ((congrArg _ (congrArg _ h)).trans (hF b).symm)))`.
-/
theorem injective_of_compat (hF : ArcPull.Compat φ F) : Function.Injective φ := fun a b h =>
  IsFractionRing.injective R (FractionRing R) ((algebraMap (FractionRing R) F).injective
    ((hF a).trans ((congrArg _ (congrArg _ h)).trans (hF b).symm)))

def pushEquiv (hF : ArcPull.Compat φ F) : (TF (R := R') F ⟶ D'.P.A) ≃* (TF (R := R) F ⟶ D.P.A) :=
  MulEquiv.ofBijective (MonoidHom.mk' (pushF (pull_grp hD) hF.base) (pushF_mul _ _))
    ⟨pushF_injective (pull_grp hD) hF.base, pushF_surjective (pull_grp hD) hF.base⟩

/- English proof (translation)
Establish `hJ` using `good ν z`. Establish `hJ'` using `good ν' z`. Set `Ω : (TF (R` to `R') F ⟶ D'.P.A) → ((Sp F).presheaf.stalk z)ˣ := fun x => om hD.w z ν.J ν'.J x.left`. Take `⟨h, hh⟩ : ∃ h : N'.A → Fˣ, ∀ x, stalkUnits z (h x) = Ω (ν'.eA x) * (Ω 1)⁻¹` from `⟨fun x => (stalkUnits z).symm _, fun x => (stalkUnits z).apply_symm_apply _⟩`. Take `⟨Φ, hΦ⟩ : ∃ Φ : N'.A ≃* N.A, ∀ x, ν.eA (Φ x) = pushF (pull_grp hD) hF.base (ν'.eA x)` from `⟨(ν'.eA.trans (pushEquiv hD hF)).trans ν.eA.symm, fun x => ν.eA.apply_symm_apply _⟩`.

Take `⟨e, he⟩ : ∃ e : N'.X ≃+ N.X, ∀ y, ν.eX (e y) = hD.xe (ν'.eX y)` from `⟨(ν'.eX.trans hD.xe).trans ν.eX.symm, fun x => ν.eX.apply_symm_apply _⟩`. Establish `hc : ∀ χ, ν'.eA (N'.c χ) = cP D' _ (ν'.eX χ)` using `ν'.c_eq`. Establish `a₁ : ∀ χ, jFK (R` using `R') F ≫ D'.xK χ = (cP D' (TF (R := R') F) χ).left := fun χ => (Category.assoc _ _ _).symm`. Establish `a₂ : jFK (R` using `R') F ≫ (1 : TK R' ⟶ D'.P.A).left = (1 : TF (R := R') F ⟶ D'.P.A).left := (Category.assoc _ _ _).symm`. Establish `rig : val (Z` using `Sp F) D.rigK (jFK (R := R) F) z ν.J = Ω 1 * val (Z := Sp F) D'.rigK (jFK (R := R') F) z ν'.J := (rig_val hD (Z := Sp F) _ _ hF.sq hJ hJ').trans (congrArg (fun q => om hD.w z ν.J ν'.J q * val (Z := Sp F) D'.rigK (jFK (R := R') F) z ν'.J) a₂)`.

Use `⟨{ φ := Φ, h := h, lam := (stalkUnits z).symm lam, e := e h_one := ?_, θ_eq := fun x y u => ?_, σ_eq := fun x => ?_, th_eq := fun x => ?_ c_eq := fun χ => ?_, ψ_eq := fun χ => ?_ }, he, fun g g' c c' hg hg' H => ⟨?_, fun χ => ?_⟩⟩` and prove the remaining obligations. Apply `(stalkUnits z).injective` to reduce the goal to its premises. Rewrite using `[hh, map_one, map_one, mul_inv_cancel]`. Apply `(stalkUnits z).injective` to reduce the goal to its premises. Establish `k : thS D z ν.J (pushF (pull_grp hD) hF.base (ν'.eA x)) (pushF (pull_grp hD) hF.base (ν'.eA y)) (pushF (pull_grp hD) hF.base (ν'.eA u)) = Ω (ν'.eA x * ν'.eA y * ν'.eA u) * (Ω (ν'.eA x * ν'.eA y))⁻¹ * (Ω (ν'.eA x * ν'.eA u))⁻¹ * (Ω (ν'.eA y * ν'.eA u))⁻¹ * Ω (ν'.eA x) * Ω (ν'.eA y …` using `thS_push (pull_grp hD) hF.base ((isGen_iff _).1 hD.w_gen) hG hJ hJ' _ _ _`.

Simplify using `only [map_mul, hh, stalk_θ ν, stalk_θ ν', hΦ, k]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv]`. Normalize the expressions using the abelian group laws. Apply `(stalkUnits z).injective` to reduce the goal to its premises.

Establish `k : val (Z` using `Sp F) D.sym (pushF (pull_grp hD) hF.base (ν'.eA x)).left z ν.J = Ω (ν'.eA x)⁻¹ * (Ω (ν'.eA x))⁻¹ * val (Z := Sp F) D'.sym (ν'.eA x).left z ν'.J := PsiEvenPull.sym_pull hG hD (Z := Sp F) (ν'.eA x).left z hJ hJ'`. Simplify using `only [map_mul, map_inv, hh, stalk_σ ν, stalk_σ ν', hΦ, k]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv]`. Normalize the expressions using the abelian group laws.

Apply `(stalkConst z).injective` to reduce the goal to its premises. Establish `k` using `stalk_th ν z (Φ x)`. Establish `k'` using `stalk_th ν' z x`. Rewrite `k` using `[hΦ, rig]`. Establish `k₁` using `k.trans ((hth (ν'.eA x)).trans (congrArg _ k'.symm))`.

Rewrite using `[map_mul, ← stalkUnits_val, map_mul, hh, MulEquiv.apply_symm_apply]`. Use `(Units.mul_left_inj (Ω 1 * val (Z := Sp F) D'.rigK (jFK (R := R') F) z ν'.J)).1 (k₁.trans ?_)` and prove the remaining obligations. Use `(Ω 1).inv_mul` as an intermediate fact. Simplify using `only [Units.val_mul]`. Take the linear combination `(-(lam.val * (Ω (ν'.eA x)).val * stalkConst z (N'.th x) * (val (Z := Sp F) D'.rigK (jFK (R := R') F) z ν'.J).val)) * this`.

Apply `ν.eA.injective` to reduce the goal to its premises. Rewrite using `[hΦ, ν.c_eq, he, hc]`. Conclude with `Over.OverMorphism.ext ((cPoint_proj hD (T := TF (R := R) F) (T' := TF (R := R') F) (𝟙 _) (hF.base.trans (Category.id_comp _).symm) _).trans (Category.id_comp _)).symm`. Apply `(stalkUnits z).injective` to reduce the goal to its premises. Establish `k : val (Z` using `Sp F) (D.psi (hD.xe (ν'.eX χ))) (jFK (R := R) F) z ν.J = (Ω (cP D' _ (ν'.eX χ)))⁻¹ * val (Z := Sp F) (D'.psi (ν'.eX χ)) (jFK (R := R') F) z ν'.J := (psi_val hD (Z := Sp F) _ _ hF.sq hJ hJ' _).trans (congrArg (fun q => (om hD.w z ν.J ν'.J q)⁻¹ * val (Z := Sp F) (D'.psi (ν'.eX χ)) …`.

Rewrite using `[map_mul, hh, stalk_ψ ν, stalk_ψ ν', he, k, rig, hc]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv]`. Normalize the expressions using the abelian group laws. Apply `ν.eA.injective` to reduce the goal to its premises.

Use `hg.1.trans (Eq.trans ?_ (hΦ _).symm)` and prove the remaining obligations. Rewrite using `[hg'.1]`. Conclude with `Over.OverMorphism.ext H.1.symm`. Apply `(stalkUnits z).injective` to reduce the goal to its premises. Establish `k₀` using `pullGt_val hD H (ν'.eX χ) (𝟙 _) hJ hJ'`.

Simplify using `only [Category.id_comp] at k₀`. Establish `k : val (Z` using `Sp F) (g.s (hD.xe (ν'.eX χ))) (𝟙 (Sp F)) z ν.J = (Ω (cP D' _ (ν'.eX χ) * g'.b))⁻¹ * Ω (cP D' _ (ν'.eX χ)) * Ω g'.b * (Ω 1)⁻¹ * val (Z := Sp F) (g'.s (ν'.eX χ)) (𝟙 (Sp F)) z ν'.J := k₀`. Use `show stalkUnits z (c.s (e χ) * h (N'.c χ * c'.b)) = stalkUnits z (c'.s χ * h (N'.c χ) * h c'.b)`. Rewrite using `[map_mul, map_mul, map_mul, hh, hh, hh, stalk_pt ν z hg, stalk_pt ν' z hg', he, k, map_mul, hc, hg'.1]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Simplify using `only [ofMul_mul, ofMul_inv]`. Normalize the expressions using the abelian group laws.
-/
theorem exists_iso_of_th (hG : GlobalFnsSt) (hF : ArcPull.Compat φ F) {N N' : NumD F} (ν : NumOf D F N)
    (ν' : NumOf D' F N') (z : Sp F) (lam : ((Sp F).presheaf.stalk z)ˣ)
    (hth : ∀ x : TF (R := R') F ⟶ D'.P.A, sval (Z := Sp F) ν.th (x.left ≫ proj hD) z ν.J =
      (lam * om hD.w z ν.J ν'.J x.left).val * sval (Z := Sp F) ν'.th x.left z ν'.J) :
    ∃ I : NumD.Iso N' N, (∀ y, ν.eX (I.e y) = hD.xe (ν'.eX y)) ∧
      ∀ (g : GtPtF D F) (g' : GtPtF D' F) (c : N.Gt) (c' : N'.Gt), ν.Pt g c → ν'.Pt g' c' →
        IsPullGtF φ hD F g g' → I.Rel c' c := by
  have hJ := good ν z
  have hJ' := good ν' z
  let Ω : (TF (R := R') F ⟶ D'.P.A) → ((Sp F).presheaf.stalk z)ˣ := fun x => om hD.w z ν.J ν'.J x.left
  obtain ⟨h, hh⟩ : ∃ h : N'.A → Fˣ, ∀ x, stalkUnits z (h x) = Ω (ν'.eA x) * (Ω 1)⁻¹ :=
    ⟨fun x => (stalkUnits z).symm _, fun x => (stalkUnits z).apply_symm_apply _⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : N'.A ≃* N.A, ∀ x, ν.eA (Φ x) = pushF (pull_grp hD) hF.base (ν'.eA x) :=
    ⟨(ν'.eA.trans (pushEquiv hD hF)).trans ν.eA.symm, fun x => ν.eA.apply_symm_apply _⟩
  obtain ⟨e, he⟩ : ∃ e : N'.X ≃+ N.X, ∀ y, ν.eX (e y) = hD.xe (ν'.eX y) :=
    ⟨(ν'.eX.trans hD.xe).trans ν.eX.symm, fun x => ν.eX.apply_symm_apply _⟩
  have hc : ∀ χ, ν'.eA (N'.c χ) = cP D' _ (ν'.eX χ) := ν'.c_eq
  have a₁ : ∀ χ, jFK (R := R') F ≫ D'.xK χ = (cP D' (TF (R := R') F) χ).left := fun χ => (Category.assoc _ _ _).symm
  have a₂ : jFK (R := R') F ≫ (1 : TK R' ⟶ D'.P.A).left = (1 : TF (R := R') F ⟶ D'.P.A).left :=
    (Category.assoc _ _ _).symm
  have rig : val (Z := Sp F) D.rigK (jFK (R := R) F) z ν.J = Ω 1 * val (Z := Sp F) D'.rigK (jFK (R := R') F) z ν'.J :=
    (rig_val hD (Z := Sp F) _ _ hF.sq hJ hJ').trans
      (congrArg (fun q => om hD.w z ν.J ν'.J q * val (Z := Sp F) D'.rigK (jFK (R := R') F) z ν'.J) a₂)
  refine ⟨{
    φ := Φ, h := h, lam := (stalkUnits z).symm lam, e := e
    h_one := ?_, θ_eq := fun x y u => ?_, σ_eq := fun x => ?_, th_eq := fun x => ?_
    c_eq := fun χ => ?_, ψ_eq := fun χ => ?_ }, he, fun g g' c c' hg hg' H => ⟨?_, fun χ => ?_⟩⟩
  · apply (stalkUnits z).injective
    rw [hh, map_one, map_one, mul_inv_cancel]
  · apply (stalkUnits z).injective
    have k : thS D z ν.J (pushF (pull_grp hD) hF.base (ν'.eA x)) (pushF (pull_grp hD) hF.base (ν'.eA y))
        (pushF (pull_grp hD) hF.base (ν'.eA u)) =
        Ω (ν'.eA x * ν'.eA y * ν'.eA u) * (Ω (ν'.eA x * ν'.eA y))⁻¹ * (Ω (ν'.eA x * ν'.eA u))⁻¹ *
          (Ω (ν'.eA y * ν'.eA u))⁻¹ * Ω (ν'.eA x) * Ω (ν'.eA y) * Ω (ν'.eA u) * (Ω 1)⁻¹ *
          thS D' z ν'.J (ν'.eA x) (ν'.eA y) (ν'.eA u) :=
      thS_push (pull_grp hD) hF.base ((isGen_iff _).1 hD.w_gen) hG hJ hJ' _ _ _
    simp only [map_mul, hh, stalk_θ ν, stalk_θ ν', hΦ, k]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · apply (stalkUnits z).injective
    have k : val (Z := Sp F) D.sym (pushF (pull_grp hD) hF.base (ν'.eA x)).left z ν.J =
        Ω (ν'.eA x)⁻¹ * (Ω (ν'.eA x))⁻¹ * val (Z := Sp F) D'.sym (ν'.eA x).left z ν'.J :=
      PsiEvenPull.sym_pull hG hD (Z := Sp F) (ν'.eA x).left z hJ hJ'
    simp only [map_mul, map_inv, hh, stalk_σ ν, stalk_σ ν', hΦ, k]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · apply (stalkConst z).injective
    have k := stalk_th ν z (Φ x)
    have k' := stalk_th ν' z x
    rw [hΦ, rig] at k
    have k₁ := k.trans ((hth (ν'.eA x)).trans (congrArg _ k'.symm))
    rw [map_mul, ← stalkUnits_val, map_mul, hh, MulEquiv.apply_symm_apply]
    refine (Units.mul_left_inj (Ω 1 * val (Z := Sp F) D'.rigK (jFK (R := R') F) z ν'.J)).1 (k₁.trans ?_)
    have := (Ω 1).inv_mul
    simp only [Units.val_mul]
    linear_combination (-(lam.val * (Ω (ν'.eA x)).val * stalkConst z (N'.th x) *
      (val (Z := Sp F) D'.rigK (jFK (R := R') F) z ν'.J).val)) * this
  · apply ν.eA.injective
    rw [hΦ, ν.c_eq, he, hc]
    exact Over.OverMorphism.ext ((cPoint_proj hD (T := TF (R := R) F) (T' := TF (R := R') F) (𝟙 _)
      (hF.base.trans (Category.id_comp _).symm) _).trans (Category.id_comp _)).symm
  · apply (stalkUnits z).injective
    have k : val (Z := Sp F) (D.psi (hD.xe (ν'.eX χ))) (jFK (R := R) F) z ν.J =
        (Ω (cP D' _ (ν'.eX χ)))⁻¹ * val (Z := Sp F) (D'.psi (ν'.eX χ)) (jFK (R := R') F) z ν'.J :=
      (psi_val hD (Z := Sp F) _ _ hF.sq hJ hJ' _).trans (congrArg (fun q => (om hD.w z ν.J ν'.J q)⁻¹ *
        val (Z := Sp F) (D'.psi (ν'.eX χ)) (jFK (R := R') F) z ν'.J) (a₁ _))
    rw [map_mul, hh, stalk_ψ ν, stalk_ψ ν', he, k, rig, hc]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · apply ν.eA.injective
    refine hg.1.trans (Eq.trans ?_ (hΦ _).symm)
    rw [hg'.1]
    exact Over.OverMorphism.ext H.1.symm
  · apply (stalkUnits z).injective
    have k₀ := pullGt_val hD H (ν'.eX χ) (𝟙 _) hJ hJ'
    simp only [Category.id_comp] at k₀
    have k : val (Z := Sp F) (g.s (hD.xe (ν'.eX χ))) (𝟙 (Sp F)) z ν.J =
        (Ω (cP D' _ (ν'.eX χ) * g'.b))⁻¹ * Ω (cP D' _ (ν'.eX χ)) * Ω g'.b * (Ω 1)⁻¹ *
          val (Z := Sp F) (g'.s (ν'.eX χ)) (𝟙 (Sp F)) z ν'.J := k₀
    show stalkUnits z (c.s (e χ) * h (N'.c χ * c'.b)) = stalkUnits z (c'.s χ * h (N'.c χ) * h c'.b)
    rw [map_mul, map_mul, map_mul, hh, hh, hh, stalk_pt ν z hg, stalk_pt ν' z hg', he, k, map_mul, hc, hg'.1]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

/- English proof (translation)
Introduce `hG R K _ _ _ φ D D' hD F _ _ _ hF N N' ν ν'`. Take `⟨c, hc⟩` from `GlobalTheory.T.exists_unit_generatingSection_pullback_field R K φ (injective_of_compat hF) D D' hD ν.th ν'.th ν.th_gen ν'.th_gen`. Set `z : Sp F` to `IsLocalRing.closedPoint F`. Use `exists_iso_of_th hD hG hF ν ν' z (TauTwist.unitAt (Z := Sp F) (TF (R := K) F).hom z c) fun x => ?_` and prove the remaining obligations. Use `hc (Sp F) x.left z ν.J ν'.J (good ν z) (good ν' z)` as an intermediate fact.

Conclude with `this.trans (congrArg (fun q => (TauTwist.unitAt (Z := Sp F) q z c * om hD.w z ν.J ν'.J x.left).val * sval (Z := Sp F) ν'.th x.left z ν'.J) (Over.w x))`.
-/
theorem exists_values_iso : GlobalFnsSt → ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] (φ : R →+* K) (D : DegPre R) (D' : DegPre K) (hD : IsPullDeg φ D D') (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing K) F], ArcPull.Compat φ F → ∀ (N N' : NumD F) (ν : NumOf D F N) (ν' : NumOf D' F N'), ∃ I : NumD.Iso N' N, (∀ y, ν.eX (I.e y) = hD.xe (ν'.eX y)) ∧ ∀ (g : GtPtF D F) (g' : GtPtF D' F) (c : N.Gt) (c' : N'.Gt), ν.Pt g c → ν'.Pt g' c' → IsPullGtF φ hD F g g' → I.Rel c' c := by
  intro hG R K _ _ _ φ D D' hD F _ _ _ hF N N' ν ν'
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_unit_generatingSection_pullback_field R K φ (injective_of_compat hF) D D' hD ν.th ν'.th ν.th_gen ν'.th_gen
  let z : Sp F := IsLocalRing.closedPoint F
  refine exists_iso_of_th hD hG hF ν ν' z (TauTwist.unitAt (Z := Sp F) (TF (R := K) F).hom z c) fun x => ?_
  have := hc (Sp F) x.left z ν.J ν'.J (good ν z) (good ν' z)
  exact this.trans (congrArg (fun q => (TauTwist.unitAt (Z := Sp F) q z c * om hD.w z ν.J ν'.J x.left).val *
    sval (Z := Sp F) ν'.th x.left z ν'.J) (Over.w x))

end GlobalTheory.ValuesPullIso
end
