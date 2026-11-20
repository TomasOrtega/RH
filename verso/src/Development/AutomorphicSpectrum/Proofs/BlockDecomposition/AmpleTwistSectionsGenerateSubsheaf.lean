import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneratedSubsheafLeOfTwistedSectionMem
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen

namespace GlobalTheory.CompanionTheory.GE.TwGen

/- English proof (translation)
Establish `hL'` using `GlobalTheory.Twist.isLB_lbZPow hH (-n)`. Establish `h₁` using `(GlobalTheory.Twist.epi_map_iff hL' (GlobalTheory.QCoh.sectionsHom s)).2 hs`. Use `GlobalTheory.Twist.preservesColimits_twistFunctor hL'` as an intermediate fact. Set `T` to `GlobalTheory.twistFunctor (GlobalTheory.lbZPow H (-n))`. Set `E : T.obj (∐ fun _ : Fin k => GlobalTheory.QCoh.structureModule X) ⟶ (S : X.Modules)` to `GlobalTheory.Twist.map _ (GlobalTheory.QCoh.sectionsHom s) ≫ (GlobalTheory.Twist.twistZAddIso (S : X.Modules) hH (add_neg_cancel n)).hom ≫ (GlobalTheory.Twist.twistZZeroIso (S : X.Modules) hH).inv`.

Use `haveI hE : Epi E := epi_comp' h₁ inferInstance`. Establish `key : ∀ i, T.map (Sigma.ι (fun _ : Fin k => GlobalTheory.QCoh.structureModule X) i) ≫ E = genHom hH n (s i)` using `fun i => by`. Establish `e : Sigma.ι (fun _ : Fin k => GlobalTheory.QCoh.structureModule X) i ≫ GlobalTheory.QCoh.sectionsHom s = GlobalTheory.QCoh.sectionHom (s i)` using `Sigma.ι_desc _ _`. Rewrite using `[genHom, ← e]`. Express the relevant statement in the definitionally equal form `T.map _ ≫ T.map _ ≫ _ = T.map (_ ≫ _) ≫ _`.

Conclude with `(Category.assoc (T.map _) (T.map _) _).symm`. Set `g : ∀ i : Fin k, T.obj (GlobalTheory.QCoh.structureModule X) ⟶ (B : X.Modules)` to `fun i => factorThruImageSubobject (genHom hH n ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) S.arrow).app ⊤ (s i))) ≫ Subobject.ofLE _ _ (hB i)`. Establish `hg : ∀ i, g i ≫ B.arrow = genHom hH n (s i) ≫ S.arrow` using `fun i => by`. Rewrite using `[← genHom_map_app hH S.arrow n (s i)]`. Conclude with `(Category.assoc _ _ _).trans ((congrArg _ (Subobject.ofLE_arrow _)).trans (imageSubobject_arrow_comp (genHom hH n ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) S.arrow).app ⊤ (s i)))))`.

Set `c` to `PreservesCoproduct.iso T (fun _ : Fin k => GlobalTheory.QCoh.structureModule X)`. Set `t : T.obj (∐ fun _ : Fin k => GlobalTheory.QCoh.structureModule X) ⟶ (B : X.Modules)` to `c.hom ≫ Sigma.desc g`. Establish `ht : t ≫ B.arrow = E ≫ S.arrow`. Establish `hι : ∀ i, Sigma.ι (fun _ : Fin k => T.obj (GlobalTheory.QCoh.structureModule X)) i ≫ c.inv = T.map (Sigma.ι (fun _ : Fin k => GlobalTheory.QCoh.structureModule X) i)` using `fun i => ι_comp_sigmaComparison T _ i`. Establish `h₂ : c.inv ≫ t = Sigma.desc g` using `Iso.inv_hom_id_assoc c _`.

Establish `h₃ : c.inv ≫ t ≫ B.arrow = c.inv ≫ E ≫ S.arrow`. Rewrite using `[← Category.assoc, h₂]`. Use `Sigma.hom_ext _ _ fun i => ?_` and prove the remaining obligations. Rewrite using `[← Category.assoc, Sigma.ι_desc, hg i, ← key i, ← Category.assoc, ← Category.assoc, hι i]`. Both sides reduce to the same expression.

Conclude with `(cancel_epi c.inv).1 h₃`. Use `haveI : StrongEpi E := strongEpi_of_epi E`. Establish `sq : CommSq t E B.arrow S.arrow` using `⟨ht⟩`. Conclude with `Subobject.le_of_comm sq.lift sq.fac_right`.
-/
theorem le_of_epi_sectionsHom {X : Scheme.{0}} {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB)
    {P : X.Modules} (S B : Subobject P) (n : ℤ) {k : ℕ}
    (s : Fin k → Γ(GlobalTheory.twistZ (S : X.Modules) H n, ⊤)) (hs : Epi (GlobalTheory.QCoh.sectionsHom s))
    (hB : ∀ i, genSub hH n ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) S.arrow).app ⊤ (s i)) ≤ B) : S ≤ B := by
  have hL' := GlobalTheory.Twist.isLB_lbZPow hH (-n)
  have h₁ := (GlobalTheory.Twist.epi_map_iff hL' (GlobalTheory.QCoh.sectionsHom s)).2 hs
  have := GlobalTheory.Twist.preservesColimits_twistFunctor hL'
  let T := GlobalTheory.twistFunctor (GlobalTheory.lbZPow H (-n))
  let E : T.obj (∐ fun _ : Fin k => GlobalTheory.QCoh.structureModule X) ⟶ (S : X.Modules) :=
    GlobalTheory.Twist.map _ (GlobalTheory.QCoh.sectionsHom s) ≫
      (GlobalTheory.Twist.twistZAddIso (S : X.Modules) hH (add_neg_cancel n)).hom ≫
      (GlobalTheory.Twist.twistZZeroIso (S : X.Modules) hH).inv
  haveI hE : Epi E := epi_comp' h₁ inferInstance
  have key : ∀ i, T.map (Sigma.ι (fun _ : Fin k => GlobalTheory.QCoh.structureModule X) i) ≫ E =
      genHom hH n (s i) := fun i => by
    have e : Sigma.ι (fun _ : Fin k => GlobalTheory.QCoh.structureModule X) i ≫ GlobalTheory.QCoh.sectionsHom s =
        GlobalTheory.QCoh.sectionHom (s i) := Sigma.ι_desc _ _
    rw [genHom, ← e]
    change T.map _ ≫ T.map _ ≫ _ = T.map (_ ≫ _) ≫ _
    exact (Category.assoc (T.map _) (T.map _) _).symm
  let g : ∀ i : Fin k, T.obj (GlobalTheory.QCoh.structureModule X) ⟶ (B : X.Modules) := fun i =>
    factorThruImageSubobject (genHom hH n ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) S.arrow).app ⊤ (s i))) ≫
      Subobject.ofLE _ _ (hB i)
  have hg : ∀ i, g i ≫ B.arrow = genHom hH n (s i) ≫ S.arrow := fun i => by
    rw [← genHom_map_app hH S.arrow n (s i)]
    exact (Category.assoc _ _ _).trans ((congrArg _ (Subobject.ofLE_arrow _)).trans
      (imageSubobject_arrow_comp
        (genHom hH n ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) S.arrow).app ⊤ (s i)))))
  let c := PreservesCoproduct.iso T (fun _ : Fin k => GlobalTheory.QCoh.structureModule X)
  let t : T.obj (∐ fun _ : Fin k => GlobalTheory.QCoh.structureModule X) ⟶ (B : X.Modules) :=
    c.hom ≫ Sigma.desc g
  have ht : t ≫ B.arrow = E ≫ S.arrow := by
    have hι : ∀ i, Sigma.ι (fun _ : Fin k => T.obj (GlobalTheory.QCoh.structureModule X)) i ≫ c.inv =
        T.map (Sigma.ι (fun _ : Fin k => GlobalTheory.QCoh.structureModule X) i) :=
      fun i => ι_comp_sigmaComparison T _ i
    have h₂ : c.inv ≫ t = Sigma.desc g := Iso.inv_hom_id_assoc c _
    have h₃ : c.inv ≫ t ≫ B.arrow = c.inv ≫ E ≫ S.arrow := by
      rw [← Category.assoc, h₂]
      refine Sigma.hom_ext _ _ fun i => ?_
      rw [← Category.assoc, Sigma.ι_desc, hg i, ← key i, ← Category.assoc, ← Category.assoc,
        hι i]
      rfl
    exact (cancel_epi c.inv).1 h₃
  haveI : StrongEpi E := strongEpi_of_epi E
  have sq : CommSq t E B.arrow S.arrow := ⟨ht⟩
  exact Subobject.le_of_comm sq.lift sq.fac_right

/- English proof (translation)
Introduce `X _ H hA P S hS`. Use `haveI : GlobalTheory.QCoh.IsFiniteQC (S : X.Modules) := ⟨hS.1, hS.2⟩`. Take `⟨n₀, h₀⟩` from `Filter.eventually_atTop.1 (hA.eventually_isGloballyGenerated_twistZ (S : X.Modules))`. Use `⟨n₀, fun n hn B hB => ?_⟩` and prove the remaining obligations. Take `⟨k, s, hs⟩` from `GlobalTheory.QCoh.isGloballyGenerated_iff_spanStalks.1 (h₀ n hn)`.

Conclude with `le_of_epi_sectionsHom hA.isLB S B n s ((GlobalTheory.QCoh.epi_sectionsHom_iff s).2 hs) fun i => hB _ ⟨s i, rfl⟩`.
-/
theorem le_of_genSub_le : ∀ {X : Scheme.{0}} [IsNoetherian X] {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X}
    (hA : GlobalTheory.IsAmpleLB H) {P : X.Modules} (S : Subobject P), IsCoherent (S : X.Modules) →
    ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∀ B : Subobject P,
      (∀ b ∈ twSecs H n S, genSub hA.isLB n b ≤ B) → S ≤ B := by
  intro X _ H hA P S hS
  haveI : GlobalTheory.QCoh.IsFiniteQC (S : X.Modules) := ⟨hS.1, hS.2⟩
  obtain ⟨n₀, h₀⟩ := Filter.eventually_atTop.1
    (hA.eventually_isGloballyGenerated_twistZ (S : X.Modules))
  refine ⟨n₀, fun n hn B hB => ?_⟩
  obtain ⟨k, s, hs⟩ := GlobalTheory.QCoh.isGloballyGenerated_iff_spanStalks.1 (h₀ n hn)
  exact le_of_epi_sectionsHom hA.isLB S B n s ((GlobalTheory.QCoh.epi_sectionsHom_iff s).2 hs)
    fun i => hB _ ⟨s i, rfl⟩

end GlobalTheory.CompanionTheory.GE.TwGen
