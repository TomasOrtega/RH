import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitTauCoordinateAddNsmulFirstVariable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefiningDegenerationDataTauCoordinateUnit

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.TensPsiCoord

open GlobalTheory.PsiTauCoordRel GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues

/- English proof (translation)
Introduce `R _ _ _ Q D' r W pr xe hT y k hk x hx`. Take `⟨-, -, -, w, -, hpsi⟩` from `hT`. Use `haveI : IsProper D'.P.A.hom := D'.P.isAb.proper`. Use `haveI : IsProper Q.B.hom := Q.isAb.proper`. Take `⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R)))` from `⟨⟨⊥, Ideal.isPrime_bot⟩⟩`.

Take `⟨J', hJ', hc'⟩` from `GlobalTheory.PeriodBalance.exists_good_integral ξ D'.P.isLB D'.P.A.hom`. Take `⟨J, hJ, hc⟩` from `GlobalTheory.PeriodBalance.exists_good_integral ξ Q.M.isLB Q.B.hom`. Establish `E` using `hpsi y ξ J J' hJ hJ'`. Take `⟨j, h, hj, rfl⟩` from `hx`. Take `⟨u₁, g₁⟩` from `val_psi_chart D' ξ hJ' hc' y j hj (h trivial)`.

Establish `eP` using `gm_genVal ξ (D'.psi y) j h`. Choose the witnesses or unpack the hypotheses as in `⟨u₂, e₂⟩ : ∃ u : Rˣ, (gm (D'.xK y) ξ _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y)))).val = GlobalTheory.PeriodBalance.cst ξ u := by`. Use `GlobalTheory.PeriodBalance.unit_gm' ξ (D'.c y).left _ (And.intro (Set.mem_iInter.2 fun I => ?_) ?_) _` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨q, hq⟩ : ∃ q : D'.P.A ⟶ Q.B, tensφ pr I = q.left := by`. Take `⟨⟨a, b⟩, c⟩` from `I`.

Apply the tactic sequence `fin_cases c <;> exact ⟨_, rfl⟩`. Use `hc ((D'.c y).left ≫ tensφ pr I) (by` as an intermediate fact. Rewrite using `[hq, Category.assoc, Over.w q, Over.w]`. Use the proof step `rfl)`. Rewrite `this` using `[← Category.assoc]`.

Conclude with `this`. Conclude with `hc' _ (Over.w _)`. Establish `hv : ∀ i j, ∃ v : Rˣ, val (Q.tau (xe y i) (xe y j)) (𝟙 _) ξ J = GlobalTheory.TauShift.kK ξ (k i j) * GlobalTheory.TauShift.cK ξ v`. Introduce `i j`. Take `⟨u, -, hu⟩` from `hk i j`.

Choose the witnesses or unpack the hypotheses as in `⟨v, hv⟩ : ∃ v : Rˣ, val u (jK R ≫ 𝟙 _) ξ J = Units.map (GlobalTheory.PeriodBalance.cst ξ).toMonoidHom v := by`. Use `val_int ξ hc u (𝟙 _) fun l => ?_` and prove the remaining obligations. Apply the tactic sequence `obtain ⟨q, hq⟩ : ∃ q : 𝟙_ (Over (Sp R)) ⟶ Q.B, GlobalTheory.PolDeg.lamPts (Q.c (xe y i)) (Q.c (xe y j)) l = q.left := by fin_cases l <;> exact ⟨_, rfl⟩`. Rewrite using `[Category.id_comp, hq, Over.w q]`. Both sides reduce to the same expression.

Use `⟨v, (hu ξ J hJ).trans (congrArg₂ (· * ·) ?_ ?_)⟩` and prove the remaining obligations. Use `GlobalTheory.RefTauCoord.gm_unitOn (RingHom.id (FractionRing R)) ξ (k i j)` as an intermediate fact. Rewrite `this` using `[show spMap (RingHom.id (FractionRing R)) = 𝟙 _ by simp]`. Conclude with `Units.ext this`. Rewrite using `[toUnit_left, ← Category.comp_id (jK R)]`.

Conclude with `hv`. Use `choose v hv using hv`. Establish `hc2 : ∀ z : Rˣ, GlobalTheory.TauShift.kK ξ (Units.map (algebraMap R (FractionRing R)).toMonoidHom z) = GlobalTheory.TauShift.cK ξ z` using `fun z => Units.ext rfl`. Use `⟨u₁⁻¹ * u₂ * ∏ i, ∏ j, v i j ^ W i j, Units.map_injective (f := (kst ξ).toMonoidHom) (kst_injective ξ) ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `GlobalTheory.TauShift.kK ξ _ = GlobalTheory.TauShift.kK ξ _`.

Establish `eP' : gm (𝟙 _) ξ (LB.wchart D'.P.L (fun _ : PUnit => D'.xK y) j) ((D'.psi y).s j) = GlobalTheory.TauShift.kK ξ (genVal (D'.psi y) j h)` using `Units.ext eP`. Establish `e₂' : gm (D'.xK y) ξ _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) = GlobalTheory.TauShift.cK ξ u₂` using `Units.ext e₂`. Establish `G` using `g₁.symm.trans (E.trans (by rw [e₂']))`. Rewrite `G` using `[eP']`. Simplify using `only [hv] at G`.

Simplify using `only [map_mul, map_inv, map_prod, map_zpow, mul_zpow, Finset.prod_mul_distrib, hc2] at G ⊢`. Establish `G'` using `congrArg ((GlobalTheory.TauShift.cK ξ u₁)⁻¹ * ·) G`. Simplify using `only [inv_mul_cancel_left] at G'`. Rewrite using `[G']`. The two sides agree by associativity and commutativity.
-/
theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)) (xe : D'.X ≃+ (Fin r → Q.X)), IsTens Q D' W pr xe → ∀ (y : D'.X) (k : Fin r → Fin r → (FractionRing R)ˣ), (∀ i j, Q.TauCoord (xe y i) (xe y j) (k i j)) → ∀ x : (FractionRing R)ˣ, GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsPsiCoord D' y x → ∃ u : Rˣ, x = Units.map (algebraMap R (FractionRing R)).toMonoidHom u * ∏ i, ∏ j, k i j ^ W i j := by
  intro R _ _ _ Q D' r W pr xe hT y k hk x hx
  obtain ⟨-, -, -, w, -, hpsi⟩ := hT
  haveI : IsProper D'.P.A.hom := D'.P.isAb.proper
  haveI : IsProper Q.B.hom := Q.isAb.proper
  obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨J', hJ', hc'⟩ := GlobalTheory.PeriodBalance.exists_good_integral ξ D'.P.isLB D'.P.A.hom
  obtain ⟨J, hJ, hc⟩ := GlobalTheory.PeriodBalance.exists_good_integral ξ Q.M.isLB Q.B.hom
  have E := hpsi y ξ J J' hJ hJ'

  obtain ⟨j, h, hj, rfl⟩ := hx
  obtain ⟨u₁, g₁⟩ := val_psi_chart D' ξ hJ' hc' y j hj (h trivial)
  have eP := gm_genVal ξ (D'.psi y) j h

  obtain ⟨u₂, e₂⟩ : ∃ u : Rˣ, (gm (D'.xK y) ξ _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y)))).val =
      GlobalTheory.PeriodBalance.cst ξ u := by
    refine GlobalTheory.PeriodBalance.unit_gm' ξ (D'.c y).left _ (And.intro (Set.mem_iInter.2 fun I => ?_) ?_) _
    · obtain ⟨q, hq⟩ : ∃ q : D'.P.A ⟶ Q.B, tensφ pr I = q.left := by
        obtain ⟨⟨a, b⟩, c⟩ := I
        fin_cases c <;> exact ⟨_, rfl⟩
      have := hc ((D'.c y).left ≫ tensφ pr I) (by
        rw [hq, Category.assoc, Over.w q, Over.w]; rfl)
      rw [← Category.assoc] at this
      exact this
    · exact hc' _ (Over.w _)

  have hv : ∀ i j, ∃ v : Rˣ, val (Q.tau (xe y i) (xe y j)) (𝟙 _) ξ J =
      GlobalTheory.TauShift.kK ξ (k i j) * GlobalTheory.TauShift.cK ξ v := by
    intro i j
    obtain ⟨u, -, hu⟩ := hk i j
    obtain ⟨v, hv⟩ : ∃ v : Rˣ, val u (jK R ≫ 𝟙 _) ξ J = Units.map (GlobalTheory.PeriodBalance.cst ξ).toMonoidHom v := by
      refine val_int ξ hc u (𝟙 _) fun l => ?_
      obtain ⟨q, hq⟩ : ∃ q : 𝟙_ (Over (Sp R)) ⟶ Q.B,
          GlobalTheory.PolDeg.lamPts (Q.c (xe y i)) (Q.c (xe y j)) l = q.left := by
        fin_cases l <;> exact ⟨_, rfl⟩
      rw [Category.id_comp, hq, Over.w q]; rfl
    refine ⟨v, (hu ξ J hJ).trans (congrArg₂ (· * ·) ?_ ?_)⟩
    · have := GlobalTheory.RefTauCoord.gm_unitOn (RingHom.id (FractionRing R)) ξ (k i j)
      rw [show spMap (RingHom.id (FractionRing R)) = 𝟙 _ by simp] at this
      exact Units.ext this
    · rw [toUnit_left, ← Category.comp_id (jK R)]; exact hv
  choose v hv using hv
  have hc2 : ∀ z : Rˣ, GlobalTheory.TauShift.kK ξ (Units.map (algebraMap R (FractionRing R)).toMonoidHom z) =
      GlobalTheory.TauShift.cK ξ z := fun z => Units.ext rfl
  refine ⟨u₁⁻¹ * u₂ * ∏ i, ∏ j, v i j ^ W i j, Units.map_injective (f := (kst ξ).toMonoidHom) (kst_injective ξ) ?_⟩
  change GlobalTheory.TauShift.kK ξ _ = GlobalTheory.TauShift.kK ξ _
  have eP' : gm (𝟙 _) ξ (LB.wchart D'.P.L (fun _ : PUnit => D'.xK y) j) ((D'.psi y).s j) =
      GlobalTheory.TauShift.kK ξ (genVal (D'.psi y) j h) := Units.ext eP
  have e₂' : gm (D'.xK y) ξ _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) = GlobalTheory.TauShift.cK ξ u₂ :=
    Units.ext e₂
  have G := g₁.symm.trans (E.trans (by rw [e₂']))
  rw [eP'] at G
  simp only [hv] at G
  simp only [map_mul, map_inv, map_prod, map_zpow, mul_zpow, Finset.prod_mul_distrib, hc2] at G ⊢
  have G' := congrArg ((GlobalTheory.TauShift.cK ξ u₁)⁻¹ * ·) G
  simp only [inv_mul_cancel_left] at G'
  rw [G']
  ac_rfl

end GlobalTheory.TensPsiCoord
