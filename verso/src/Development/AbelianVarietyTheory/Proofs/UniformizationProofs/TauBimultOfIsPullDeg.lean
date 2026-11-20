import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace TauPull

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

/- English proof (translation)
Introduce `a b hab`. Apply `Units.ext` to reduce the goal to its premises. Establish `e` using `congrArg Units.val hab`. Rewrite `e` using `[gm_val h z V hV, gm_val h z V hV, ← sub_eq_zero, ← map_sub, ← map_sub]`. Rewrite using `[← sub_eq_zero, ← basicOpen_eq_bot_iff]`.

Assume the negation of the conclusion as `hne`. Establish `hm : z ∈ h ⁻¹ᵁ Y.basicOpen (a.val - b.val)` using `hd _ (by`. Assume the negation of the conclusion as `hn`. Conclude with `hne (TopologicalSpace.Opens.not_nonempty_iff_eq_bot _ |>.1 hn))`. Rewrite `hm` using `[Scheme.preimage_basicOpen, Scheme.mem_basicOpen _ _ z hV, e]`.

Conclude with `not_isUnit_zero hm`.
-/
theorem gm_injective_of_dense {Y Z : Scheme.{0}} [IsReduced Y] (h : Z ⟶ Y) (z : Z)
    (hd : ∀ V : Y.Opens, (V : Set Y).Nonempty → h z ∈ V) (V : Y.Opens) (hV : h z ∈ V) :
    Function.Injective (gm h z V) := by
  intro a b hab
  apply Units.ext
  have e := congrArg Units.val hab
  rw [gm_val h z V hV, gm_val h z V hV, ← sub_eq_zero, ← map_sub, ← map_sub] at e
  rw [← sub_eq_zero, ← basicOpen_eq_bot_iff]
  by_contra hne
  have hm : z ∈ h ⁻¹ᵁ Y.basicOpen (a.val - b.val) :=
    hd _ (by
      by_contra hn
      exact hne (TopologicalSpace.Opens.not_nonempty_iff_eq_bot _ |>.1 hn))
  rw [Scheme.preimage_basicOpen, Scheme.mem_basicOpen _ _ z hV, e] at hm
  exact not_isUnit_zero hm

/- English proof (translation)
Introduce `j j' c₁ c₂ c₃`. Establish `dom : IsDominant h` using `⟨dense_iff_inter_open.2 fun U hU hne => ⟨h z, hd ⟨U, hU⟩ hne, z, rfl⟩⟩`. Use `unit_ext fun y hy => congrArg (gm (𝟙 Y) y _) ?_` and prove the remaining obligations. Establish `hz : h z ∈ LB.wchart L φ j ⊓ LB.wchart L φ' j'` using `hd _ ⟨y, hy⟩`. Apply `gm_injective_of_dense h z hd _ hz` to reduce the goal to its premises.

Take `⟨J, hJ, e⟩` from `exists_good L hL z (Sum.elim (fun k => h ≫ φ k) (fun k => h ≫ φ' k)) (Sum.elim j j') (by`. Introduce and unpack `(a | a) (b | b) e`. Use `exacts [c₁ a b (ext_of_isDominant h e), c₃ a b (ext_of_isDominant h e), (c₃ b a (ext_of_isDominant h e.symm)).symm, c₂ a b (ext_of_isDominant h e)]) (by`. Introduce and unpack `(a | a)`. Use `exacts [Set.mem_iInter.1 hz.1 a, Set.mem_iInter.1 hz.2 a])`.

Use `H J hJ` as an intermediate fact. Rewrite `this` using `[val_of t _ z J j (fun k => e (.inl k)), val_of t' _ z J j' (fun k => e (.inr k))]`. Conclude with `(gm_res _ z _ hz _).trans (this.trans (gm_res _ z _ hz _).symm)`.
-/
theorem corr_of_dense {X Y Z : Scheme.{0}} [IsReduced Y] [X.IsSeparated] {L : LB X} (hL : L.IsLB)
    {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')} (h : Z ⟶ Y) (z : Z)
    (hd : ∀ V : Y.Opens, (V : Set Y).Nonempty → h z ∈ V)
    (H : ∀ J, Good L z J → val t h z J = val t' h z J) : LB.Gen.Corr L φ ε φ' ε' t t' := by
  intro j j' c₁ c₂ c₃
  have dom : IsDominant h := ⟨dense_iff_inter_open.2 fun U hU hne => ⟨h z, hd ⟨U, hU⟩ hne, z, rfl⟩⟩
  refine unit_ext fun y hy => congrArg (gm (𝟙 Y) y _) ?_
  have hz : h z ∈ LB.wchart L φ j ⊓ LB.wchart L φ' j' := hd _ ⟨y, hy⟩
  apply gm_injective_of_dense h z hd _ hz
  obtain ⟨J, hJ, e⟩ := exists_good L hL z (Sum.elim (fun k => h ≫ φ k) (fun k => h ≫ φ' k)) (Sum.elim j j') (by
    rintro (a | a) (b | b) e
    exacts [c₁ a b (ext_of_isDominant h e), c₃ a b (ext_of_isDominant h e),
      (c₃ b a (ext_of_isDominant h e.symm)).symm, c₂ a b (ext_of_isDominant h e)]) (by
    rintro (a | a)
    exacts [Set.mem_iInter.1 hz.1 a, Set.mem_iInter.1 hz.2 a])
  have := H J hJ
  rw [val_of t _ z J j (fun k => e (.inl k)), val_of t' _ z J j' (fun k => e (.inr k))] at this
  exact (gm_res _ z _ hz _).trans (this.trans (gm_res _ z _ hz _).symm)

/- English proof (translation)
Take `⟨x, hx⟩` from `hV`. Establish `hz : (jK R z).asIdeal ≤ x.asIdeal`. Establish `h0 : PrimeSpectrum.asIdeal (R` using `FractionRing R) z = ⊥ := @Ideal.eq_bot_of_prime _ _ _ (PrimeSpectrum.isPrime _)`. Introduce `r hr`. Establish `h1 : algebraMap R (FractionRing R) r ∈ PrimeSpectrum.asIdeal (R` using `FractionRing R) z := hr`.

Rewrite `h1` using `[h0, Ideal.mem_bot, map_eq_zero_iff _ (IsFractionRing.injective R (FractionRing R))]`. Rewrite using `[h1]`. Conclude with `zero_mem _`. Conclude with `((PrimeSpectrum.le_iff_specializes _ _).1 hz).mem_open V.isOpen hx`.
-/
theorem jK_mem {R : Type} [CommRing R] [IsDomain R] (z : (TK R).left) (V : (Spec (CommRingCat.of R)).Opens)
    (hV : (V : Set (Spec (CommRingCat.of R))).Nonempty) : jK R z ∈ V := by
  obtain ⟨x, hx⟩ := hV
  have hz : (jK R z).asIdeal ≤ x.asIdeal := by
    have h0 : PrimeSpectrum.asIdeal (R := FractionRing R) z = ⊥ := @Ideal.eq_bot_of_prime _ _ _ (PrimeSpectrum.isPrime _)
    intro r hr
    have h1 : algebraMap R (FractionRing R) r ∈ PrimeSpectrum.asIdeal (R := FractionRing R) z := hr
    rw [h0, Ideal.mem_bot, map_eq_zero_iff _ (IsFractionRing.injective R (FractionRing R))] at h1
    rw [h1]; exact zero_mem _
  exact ((PrimeSpectrum.le_iff_specializes _ _).1 hz).mem_open V.isOpen hx

section OnW

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {W : (Spec (CommRingCat.of R)).Opens}

/- English proof (translation)
The claim follows from `(val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))`.
-/
theorem val_tau {Z : Scheme.{0}} (r : Z ⟶ (TK R).left) {z : Z} {J} (hJ : Good D.P.L z J) (a b : D.X) :
    val (D.tau a b) r z J =
      val (D.psi (a + b)) r z J * (val (D.psi a) r z J)⁻¹ * (val (D.psi b) r z J)⁻¹ * (val D.rigK r z J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

/- English proof (translation)
The claim follows from `(val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))`.
-/
theorem val_tauW (ψW : PsiOn D W) {Z : Scheme.{0}} (r : Z ⟶ (TW W).left) {z : Z} {J} (hJ : Good D.P.L z J)
    (a b : D.X) : val (ψW.tau a b) r z J =
      val (ψW.psi (a + b)) r z J * (val (ψW.psi a) r z J)⁻¹ * (val (ψW.psi b) r z J)⁻¹ * (val (D.rigW W) r z J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

/- English proof (translation)
Establish `sep : D.P.A.left.IsSeparated`. Use `D.P.isAb.proper` as an intermediate fact. Use `⟨?_⟩` and prove the remaining obligations. Rewrite using `[← terminal.comp_from D.P.A.hom]`. Use `infer_instance`.

Take `⟨lam, hl⟩ : ∃ lam : (TK R).left ⟶ (jK R ⁻¹ᵁ W).toScheme, lam ≫ (jK R ⁻¹ᵁ W).ι = 𝟙 _` from `⟨IsOpenImmersion.lift _ (𝟙 _) (by`. Introduce and unpack `_ ⟨y, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `jK_mem y W hW), IsOpenImmersion.lift_fac _ _ _⟩`. Establish `hκ : (lam ≫ jK R ∣_ W) ≫ W.ι = jK R`.

Rewrite using `[Category.assoc, morphismRestrict_ι, ← Category.assoc, hl, Category.id_comp]`. Set `κ : TK R ⟶ TW W` to `Over.homMk (lam ≫ jK R ∣_ W) hκ`. Take `⟨z⟩ : Nonempty (TK R).left` from `inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))`. Establish `red : IsReduced (TW W).left` using `inferInstanceAs (IsReduced W.toScheme)`. Use `corr_of_dense D.P.isLB κ.left z (fun V hV => ?_) fun J hJ => ?_` and prove the remaining obligations.

Establish `h₁ : jK R z ∈ W.ι ''ᵁ V` using `jK_mem z _ (hV.image _)`. Take `⟨y, hy, e⟩` from `h₁`. Establish `e' : W.ι y = W.ι (κ.left z)` using `e.trans (congrArg (fun q => q z) hκ).symm`. Rewrite using `[← W.ι.isOpenEmbedding.injective e']`. Conclude with `hy`.

Establish `vψ : ∀ χ, val (ψW.psi χ) κ.left z J = val (D.psi χ) (𝟙 _) z J` using `fun χ => by`. Use `(val_pull hJ _ _ _).symm.trans ((val_corr hJ (ψW.psi_eq χ) lam).trans (val_pull hJ _ _ _))` as an intermediate fact. Rewrite `this` using `[hl]`. Conclude with `this`. Establish `vρ : val (D.rigW W) κ.left z J = val D.rigK (𝟙 _) z J`.

Use `(val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)` and prove the remaining obligations. Rewrite using `[Category.id_comp]`. Conclude with `congrArg (fun q => val D.rig q z J) hκ`. Establish `vτ : ∀ a b, val (ψW.tau a b) κ.left z J = val (D.tau a b) (𝟙 _) z J` using `fun a b => by`. Rewrite using `[val_tauW ψW _ hJ, val_tau _ hJ, vψ, vψ, vψ, vρ]`.

Establish `e` using `(val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB a a' b) (𝟙 _)).trans (val_mul hJ _ _ _))`. Use `(val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)` and prove the remaining obligations. Rewrite using `[vτ, vτ, vτ, ← e]`. Use `congrArg₂ (· * ·) rfl ((val_cub D.cub κ hJ _ _ _).trans (Eq.trans ?_ (val_cub D.cub (𝟙 (TK R)) hJ (cP D _ a) (cP D _ a') (cP D _ b)).symm))` and prove the remaining obligations. Simplify using `only [comp_cP]`.
-/
theorem tauW_corr (hB : D.TauBimult) (ψW : PsiOn D W) (hW : (W : Set (Spec (CommRingCat.of R))).Nonempty)
    (a a' b : D.X) : LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (ψW.tau (a + a') b)
        (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
          (lift (cP D (TW W) a) (lift (cP D (TW W) a') (cP D (TW W) b))).left))
      (LB.mulGen D.P.L _ _ _ _ (ψW.tau a b) (ψW.tau a' b)) := by
  have sep : D.P.A.left.IsSeparated := by
    have := D.P.isAb.proper
    refine ⟨?_⟩
    rw [← terminal.comp_from D.P.A.hom]
    infer_instance
  obtain ⟨lam, hl⟩ : ∃ lam : (TK R).left ⟶ (jK R ⁻¹ᵁ W).toScheme, lam ≫ (jK R ⁻¹ᵁ W).ι = 𝟙 _ :=
    ⟨IsOpenImmersion.lift _ (𝟙 _) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact jK_mem y W hW), IsOpenImmersion.lift_fac _ _ _⟩
  have hκ : (lam ≫ jK R ∣_ W) ≫ W.ι = jK R := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hl, Category.id_comp]
  let κ : TK R ⟶ TW W := Over.homMk (lam ≫ jK R ∣_ W) hκ
  obtain ⟨z⟩ : Nonempty (TK R).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  have red : IsReduced (TW W).left := inferInstanceAs (IsReduced W.toScheme)
  refine corr_of_dense D.P.isLB κ.left z (fun V hV => ?_) fun J hJ => ?_
  · have h₁ : jK R z ∈ W.ι ''ᵁ V := jK_mem z _ (hV.image _)
    obtain ⟨y, hy, e⟩ := h₁
    have e' : W.ι y = W.ι (κ.left z) := e.trans (congrArg (fun q => q z) hκ).symm
    rw [← W.ι.isOpenEmbedding.injective e']
    exact hy
  · have vψ : ∀ χ, val (ψW.psi χ) κ.left z J = val (D.psi χ) (𝟙 _) z J := fun χ => by
      have := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (ψW.psi_eq χ) lam).trans (val_pull hJ _ _ _))
      rw [hl] at this
      exact this
    have vρ : val (D.rigW W) κ.left z J = val D.rigK (𝟙 _) z J := by
      refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
      rw [Category.id_comp]
      exact congrArg (fun q => val D.rig q z J) hκ
    have vτ : ∀ a b, val (ψW.tau a b) κ.left z J = val (D.tau a b) (𝟙 _) z J := fun a b => by
      rw [val_tauW ψW _ hJ, val_tau _ hJ, vψ, vψ, vψ, vρ]
    have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB a a' b) (𝟙 _)).trans (val_mul hJ _ _ _))
    refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
    rw [vτ, vτ, vτ, ← e]
    refine congrArg₂ (· * ·) rfl ((val_cub D.cub κ hJ _ _ _).trans (Eq.trans ?_
      (val_cub D.cub (𝟙 (TK R)) hJ (cP D _ a) (cP D _ a') (cP D _ b)).symm))
    simp only [comp_cP]

/- English proof (translation)
Use `(val_mul hJ _ _ _).symm.trans ((val_corr hJ (tauW_corr hB ψW ⟨_, (κ.left z).2⟩ a a' b) κ.left).trans (val_mul hJ _ _ _))` as an intermediate fact. Use `Eq.trans (congrArg₂ (· * ·) rfl ?_) this` and prove the remaining obligations. Use `Eq.trans ?_ (val_cub D.cub κ hJ (cP D _ a) (cP D _ a') (cP D _ b)).symm` and prove the remaining obligations. Rewrite using `[comp_cP, comp_cP, comp_cP]`.
-/
theorem tauW_mul (hB : D.TauBimult) (ψW : PsiOn D W) {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TW W)
    {z : T.left} {J} (hJ : Good D.P.L z J) (a a' b : D.X) :
    val (ψW.tau (a + a') b) κ.left z J * th D z J (cP D T a) (cP D T a') (cP D T b) =
      val (ψW.tau a b) κ.left z J * val (ψW.tau a' b) κ.left z J := by
  have := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (tauW_corr hB ψW ⟨_, (κ.left z).2⟩ a a' b) κ.left).trans
    (val_mul hJ _ _ _))
  refine Eq.trans (congrArg₂ (· * ·) rfl ?_) this
  refine Eq.trans ?_ (val_cub D.cub κ hJ (cP D _ a) (cP D _ a') (cP D _ b)).symm
  rw [comp_cP, comp_cP, comp_cP]

end OnW

section Pull

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

/- English proof (translation)
Take `⟨b, hb, hc⟩` from `hD.psi_pr χ`. Establish `e₂` using `(val_corr hJ hc (𝟙 _)).trans (val_pull hJ _ _ _)`. Rewrite `e₂` using `[Category.id_comp]`. Rewrite using `[← e₂]`. Take `⟨p, hp⟩ : ∃ p, p = J (D'.xK χ ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))` from `⟨_, rfl⟩`.

Take `⟨q, hq⟩ : ∃ q, q = J' (D'.xK χ)` from `⟨_, rfl⟩`. Rewrite using `[← hp, ← hq, val_of b _ y J (fun _ => p) (fun _ => by rw [Category.id_comp, hp]), val_of (D'.psi χ) _ y J' (fun _ => q) (fun _ => by rw [Category.id_comp, hq])]`. Establish `m₁ : (𝟙 (TK R').left : _ ⟶ _) y ∈ D'.xK χ ⁻¹ᵁ ((D.P.L.pull (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))).U (fun _ => p) ⊓ D'.P.L.U q)` using `⟨mem_pull.2 (hp ▸ hJ _), hq ▸ hJ' _⟩`. Establish `e₁` using `congrArg (gm (𝟙 (TK R').left) y (D'.xK χ ⁻¹ᵁ ((D.P.L.pull (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))).U (fun _ => p) ⊓ D'.P.L.U q))) (hb (fun _ => p) q)`. Use `(gm_res _ y _ m₁ _).symm.trans (e₁.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_zpow _ _ _).trans ((congrArg (· ^ (-1 : ℤ)) (gm_pull _ (D'.xK χ) y ((D.P.L.pull (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))).U (fun _ => p) ⊓ D'.P.L.U q) m₁ _)).trans ?_)) (gm_res _ y …` and prove the remaining obligations.

Rewrite using `[Category.id_comp]`. Conclude with `zpow_neg_one _`.
-/
theorem val_psiW (hD : IsPullDeg φ D D') {y : (TK R').left} {J J'} (hJ : Good D.P.L y J) (hJ' : Good D'.P.L y J')
    (χ : D'.X) : val (hD.psiW.psi (hD.xe χ)) hD.g y J =
      (gw hD.w (D'.xK χ) y (J (D'.xK χ ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))) (J' (D'.xK χ)))⁻¹ *
        val (D'.psi χ) (𝟙 _) y J' := by
  obtain ⟨b, hb, hc⟩ := hD.psi_pr χ
  have e₂ := (val_corr hJ hc (𝟙 _)).trans (val_pull hJ _ _ _)
  rw [Category.id_comp] at e₂
  rw [← e₂]
  obtain ⟨p, hp⟩ : ∃ p, p = J (D'.xK χ ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = J' (D'.xK χ) := ⟨_, rfl⟩
  rw [← hp, ← hq, val_of b _ y J (fun _ => p) (fun _ => by rw [Category.id_comp, hp]),
    val_of (D'.psi χ) _ y J' (fun _ => q) (fun _ => by rw [Category.id_comp, hq])]
  have m₁ : (𝟙 (TK R').left : _ ⟶ _) y ∈ D'.xK χ ⁻¹ᵁ ((D.P.L.pull (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))).U
      (fun _ => p) ⊓ D'.P.L.U q) := ⟨mem_pull.2 (hp ▸ hJ _), hq ▸ hJ' _⟩
  have e₁ := congrArg (gm (𝟙 (TK R').left) y
    (D'.xK χ ⁻¹ᵁ ((D.P.L.pull (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))).U (fun _ => p) ⊓ D'.P.L.U q)))
    (hb (fun _ => p) q)
  refine (gm_res _ y _ m₁ _).symm.trans (e₁.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((map_zpow _ _ _).trans ((congrArg (· ^ (-1 : ℤ)) (gm_pull _ (D'.xK χ) y
      ((D.P.L.pull (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))).U (fun _ => p) ⊓ D'.P.L.U q) m₁ _)).trans ?_))
      (gm_res _ y _ m₁ _))))
  rw [Category.id_comp]
  exact zpow_neg_one _

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `a a' b`. Use `corr_of_val D'.P.isLB fun y J' hJ' => ?_` and prove the remaining obligations. Use `choose J hJ₀ using fun χ : (TK R').left ⟶ D.P.A.left => exists_chart D.P.isLB (χ y)`. Establish `hJ : Good D.P.L y J` using `hJ₀`. Establish `gp` using `pull_grp hD`.

Set `Φ` to `hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)`. Set `T : Over (Spec (CommRingCat.of R))` to `Over.mk ((TK R').hom ≫ spMap φ)`. Set `κ : T ⟶ TW hD.W` to `Over.homMk hD.g hD.g_comm`. Set `β : (TK R' ⟶ D'.P.A) → (T ⟶ D.P.A)` to `fun x => pushPt gp.1.w x`. Establish `βc : ∀ χ, β (cP D' _ χ) = cP D _ (hD.xe χ)` using `fun χ => Over.OverMorphism.ext (by show ((TK R').hom ≫ (D'.c χ).left) ≫ Φ = ((TK R').hom ≫ spMap φ) ≫ (D.c (hD.xe χ)).left`.

Rewrite using `[Category.assoc, hD.c_pr, Category.assoc])`. Set `Ω : (TK R' ⟶ D'.P.A) → ((TK R').left.presheaf.stalk y)ˣ` to `fun x => gw hD.w x.left y (J (x.left ≫ Φ)) (J' x.left)`. Set `θ : (T ⟶ D.P.A) → (T ⟶ D.P.A) → (T ⟶ D.P.A) → ((TK R').left.presheaf.stalk y)ˣ` to `th D (T := T) y J`. Establish `cub : ∀ a b c : TK R' ⟶ D'.P.A, θ (β a) (β b) (β c) = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ * th D' y J' a b c`. Introduce `a b c`.

Establish `e` using `cub_pull hG hD (T' := TK R') hJ hJ' a b c`. Establish `q : (lift a (lift b c)).left ≫ (cubeMapOf gp).F3 = (lift (β a) (lift (β b) (β c))).left` using `hom_ext_triple _ fun i => by`. Rewrite using `[Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]`. Apply the tactic sequence `fin_cases i <;> simp [x3] <;> rfl`. Rewrite `e` using `[q]`.

Conclude with `e.trans (congrArg₂ (· * ·) (prod_cub a b c (fun q => gw hD.w q y (J (q ≫ Φ)) (J' q))) rfl)`. Establish `vψ : ∀ χ, val (hD.psiW.psi (hD.xe χ)) hD.g y J = (Ω (cP D' _ χ))⁻¹ * val (D'.psi χ) (𝟙 _) y J'` using `fun χ => val_psiW hD hJ hJ' χ`. Establish `vρ : val (D.rigW hD.W) hD.g y J = Ω 1 * val D'.rigK (𝟙 _) y J'`. Establish `pm` using `(maps_iff hD.w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf φ) _ (rigPull_le Φ (specOf φ) hD.he D.P.L) (fun _ => rfl)).1 hD.w_rig`. Establish `a₂ : ((TK R').hom ≫ specOf φ) ≫ eSec D.P.A = (1 : TK R' ⟶ D'.P.A).left ≫ Φ` using `congrArg (fun q => q.left) (map_one (pushHom gp (TK R'))).symm`.

Establish `e` using `pm _ (TK R').hom y (fun _ => J ((1 : TK R' ⟶ D'.P.A).left ≫ Φ)) (fun _ => J' (1 : TK R' ⟶ D'.P.A).left) (fun _ => hJ _) (fun _ => hJ' _)`. Rewrite `e` using `[Fintype.prod_unique, zpow_one]`. Establish `b₁ : hD.g ≫ (toUnit (TW hD.W)).left = (TK R').hom ≫ specOf φ` using `hD.g_comm`. Establish `b₂ : 𝟙 _ ≫ (toUnit (TK R')).left = (TK R').hom` using `Category.id_comp _`. Use `(val_pull hJ _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (val_pull hJ' _ _ _).symm))` and prove the remaining obligations.

Rewrite using `[b₁, b₂]`. Conclude with `(val_of _ _ y J _ (fun _ => congrArg J a₂)).trans e`. Establish `key : val (hD.psiW.tau (hD.xe a + hD.xe a') (hD.xe b)) hD.g y J * θ (cP D T (hD.xe a)) (cP D T (hD.xe a')) (cP D T (hD.xe b)) = val (hD.psiW.tau (hD.xe a) (hD.xe b)) hD.g y J * val (hD.psiW.tau (hD.xe a') (hD.xe b)) hD.g y J` using `tauW_mul hB hD.psiW κ hJ _ _ _`. Rewrite `key` using `[← βc, ← βc, ← βc, cub, val_tauW _ _ hJ, val_tauW _ _ hJ, val_tauW _ _ hJ, ← map_add, ← map_add, ← map_add, ← map_add, vψ, vψ, vψ, vψ, vψ, vψ, vψ, vρ, cPoint_add, cPoint_add, cPoint_add, cPoint_add]`. Use `(val_mul hJ' _ _ _).trans (Eq.trans ?_ (val_mul hJ' _ _ _).symm)` and prove the remaining obligations.

Use `(congrArg₂ (· * ·) rfl (val_cub D'.cub (𝟙 (TK R')) hJ' (cP D' _ a) (cP D' _ a') (cP D' _ b))).trans ?_` and prove the remaining obligations. Rewrite using `[Category.id_comp, Category.id_comp, Category.id_comp, val_tau _ hJ', val_tau _ hJ', val_tau _ hJ']`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Establish `e'` using `congrArg Additive.ofMul key`. Simplify using `only [ofMul_mul, ofMul_inv] at e' ⊢`.

Take the linear combination `(norm := abel) e'`.
-/
theorem tauBimult_pull (hG : GlobalFnsSt) (hD : IsPullDeg φ D D') (hB : D.TauBimult) : D'.TauBimult := by
  intro a a' b
  refine corr_of_val D'.P.isLB fun y J' hJ' => ?_
  choose J hJ₀ using fun χ : (TK R').left ⟶ D.P.A.left => exists_chart D.P.isLB (χ y)
  have hJ : Good D.P.L y J := hJ₀
  have gp := pull_grp hD
  let Φ := hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)
  let T : Over (Spec (CommRingCat.of R)) := Over.mk ((TK R').hom ≫ spMap φ)
  let κ : T ⟶ TW hD.W := Over.homMk hD.g hD.g_comm
  let β : (TK R' ⟶ D'.P.A) → (T ⟶ D.P.A) := fun x => pushPt gp.1.w x
  have βc : ∀ χ, β (cP D' _ χ) = cP D _ (hD.xe χ) := fun χ => Over.OverMorphism.ext (by
    show ((TK R').hom ≫ (D'.c χ).left) ≫ Φ = ((TK R').hom ≫ spMap φ) ≫ (D.c (hD.xe χ)).left
    rw [Category.assoc, hD.c_pr, Category.assoc])
  let Ω : (TK R' ⟶ D'.P.A) → ((TK R').left.presheaf.stalk y)ˣ := fun x => gw hD.w x.left y (J (x.left ≫ Φ)) (J' x.left)
  let θ : (T ⟶ D.P.A) → (T ⟶ D.P.A) → (T ⟶ D.P.A) → ((TK R').left.presheaf.stalk y)ˣ := th D (T := T) y J
  have cub : ∀ a b c : TK R' ⟶ D'.P.A, θ (β a) (β b) (β c) =
        Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ *
          th D' y J' a b c := by
    intro a b c
    have e := cub_pull hG hD (T' := TK R') hJ hJ' a b c
    have q : (lift a (lift b c)).left ≫ (cubeMapOf gp).F3 = (lift (β a) (lift (β b) (β c))).left :=
      hom_ext_triple _ fun i => by
        rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
        fin_cases i <;> simp [x3] <;> rfl
    rw [q] at e
    exact e.trans (congrArg₂ (· * ·) (prod_cub a b c (fun q => gw hD.w q y (J (q ≫ Φ)) (J' q))) rfl)
  have vψ : ∀ χ, val (hD.psiW.psi (hD.xe χ)) hD.g y J = (Ω (cP D' _ χ))⁻¹ * val (D'.psi χ) (𝟙 _) y J' :=
    fun χ => val_psiW hD hJ hJ' χ
  have vρ : val (D.rigW hD.W) hD.g y J = Ω 1 * val D'.rigK (𝟙 _) y J' := by
    have pm := (maps_iff hD.w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf φ) _
      (rigPull_le Φ (specOf φ) hD.he D.P.L) (fun _ => rfl)).1 hD.w_rig
    have a₂ : ((TK R').hom ≫ specOf φ) ≫ eSec D.P.A = (1 : TK R' ⟶ D'.P.A).left ≫ Φ :=
      congrArg (fun q => q.left) (map_one (pushHom gp (TK R'))).symm
    have e := pm _ (TK R').hom y (fun _ => J ((1 : TK R' ⟶ D'.P.A).left ≫ Φ))
      (fun _ => J' (1 : TK R' ⟶ D'.P.A).left) (fun _ => hJ _) (fun _ => hJ' _)
    rw [Fintype.prod_unique, zpow_one] at e
    have b₁ : hD.g ≫ (toUnit (TW hD.W)).left = (TK R').hom ≫ specOf φ := hD.g_comm
    have b₂ : 𝟙 _ ≫ (toUnit (TK R')).left = (TK R').hom := Category.id_comp _
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (val_pull hJ' _ _ _).symm))
    rw [b₁, b₂]
    exact (val_of _ _ y J _ (fun _ => congrArg J a₂)).trans e
  have key : val (hD.psiW.tau (hD.xe a + hD.xe a') (hD.xe b)) hD.g y J *
      θ (cP D T (hD.xe a)) (cP D T (hD.xe a')) (cP D T (hD.xe b)) =
      val (hD.psiW.tau (hD.xe a) (hD.xe b)) hD.g y J * val (hD.psiW.tau (hD.xe a') (hD.xe b)) hD.g y J :=
    tauW_mul hB hD.psiW κ hJ _ _ _
  rw [← βc, ← βc, ← βc, cub, val_tauW _ _ hJ, val_tauW _ _ hJ, val_tauW _ _ hJ, ← map_add, ← map_add, ← map_add,
    ← map_add, vψ, vψ, vψ, vψ, vψ, vψ, vψ, vρ, cPoint_add, cPoint_add, cPoint_add, cPoint_add] at key
  refine (val_mul hJ' _ _ _).trans (Eq.trans ?_ (val_mul hJ' _ _ _).symm)
  refine (congrArg₂ (· * ·) rfl (val_cub D'.cub (𝟙 (TK R')) hJ' (cP D' _ a) (cP D' _ a') (cP D' _ b))).trans ?_
  rw [Category.id_comp, Category.id_comp, Category.id_comp, val_tau _ hJ', val_tau _ hJ', val_tau _ hJ']
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv] at e' ⊢
  linear_combination (norm := abel) e'

end Pull

end TauPull

/- English proof (translation)
Introduce `hG _ _ _ _ _ _ _ _ _ hD hB` and use `TauPull.tauBimult_pull hG hD hB`.
-/
theorem tauBimult_of_isPullDeg : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (_hD : IsPullDeg φ D D'), D.TauBimult → D'.TauBimult :=
  fun hG _ _ _ _ _ _ _ _ _ hD hB => TauPull.tauBimult_pull hG hD hB

end GlobalTheory
