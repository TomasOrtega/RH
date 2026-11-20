import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNormalFiniteModelOfFiniteOverOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientSubringDedekindCompatibleEmbed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverIffLocallyOfFiniteTypeAndExistsIsAmpl
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

/- English proof (translation)
Introduce `E _ _ _ H D Xo n N T l h S e β b hS _ hN hβ hb`. Substitute `h` using the available equality. Take `⟨⟨_, _⟩, _, hfr⟩` from `(GlobalTheory.BaseRing.isDedFrac_RZ E H l S e hS hN).2.2 β hβ`. Set `_` to `β.toAlgebra`. Take `⟨W, f₀, hW₀, hfin, -, fa, fs⟩` from `T.fin l rfl (β.comp b) (fun x => (hβ (b x)).trans (hb x))`.

Establish `hsm` using `(Xo l).smooth`. Establish `hnor : Geo.Tor.IsNormalScheme (Xo l).X` using `(GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ (Xo l).s (SmoothOfRelativeDimension.smooth D.dim _)).2.1`. Set `s₁` to `pullback.snd T.s (spMap b)`. Establish `hp : IsPullback (pullback.fst s₁ (spMap β) ≫ pullback.fst T.s (spMap b)) (pullback.snd s₁ (spMap β)) T.s (spMap (β.comp b))`. Rewrite using `[spMap_comp]`.

Conclude with `(IsPullback.of_hasPullback s₁ (spMap β)).paste_horiz (IsPullback.of_hasPullback T.s (spMap b))`. Set `g` to `W.ι ≫ hp.isoPullback.inv`. Establish `g₁ : (g ≫ pullback.fst _ _) ≫ pullback.fst _ _ = W.ι ≫ pullback.fst _ _`. Rewrite using `[Category.assoc, Category.assoc, hp.isoPullback_inv_fst]`. Establish `g₂ : g ≫ pullback.snd _ _ = W.ι ≫ pullback.snd _ _`.

Rewrite using `[Category.assoc, hp.isoPullback_inv_snd]`. Establish `hW : (f₀ ≫ g.isoOpensRange.hom) ≫ g.opensRange.ι = f₀ ≫ g`. Rewrite using `[Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]`. Take `⟨Y, π, jQ, hπ, hY, hproj, hflat, j₂, j₁, jo, jd, jr⟩` from `GlobalTheory.exists_normal_finite_model_of_finite_over_open _ (KA l) _ (Xo l).X s₁ (Xo l).s (f₀ ≫ g ≫ pullback.fst _ _) g.opensRange (f₀ ≫ g.isoOpensRange.hom) (GlobalTheory.ProjSpace.isProjOver_pullback_snd b T.proj) hnor inferInstance (by rw [← Category.assoc]; exact (congrArg …`. Rewrite using `[← Category.assoc]`.

Conclude with `(congrArg (· ≫ _) hW).trans ((Category.assoc _ _ _).trans ((congrArg (f₀ ≫ ·) g₂).trans fs)))`. Take `⟨_, _, _, _, _, mu, -⟩` from `sabPull Out.CubePf.cubePull (π ≫ pullback.fst T.s (spMap b)) T.t`. Establish `hj : (jQ ≫ pullback.fst (π ≫ s₁) (spMap β)) ≫ π ≫ pullback.fst T.s (spMap b) = T.a l rfl`. Rewrite using `[← fa, ← g₁, ← Category.assoc f₀, ← j₁]`. Simplify using `only [Category.assoc]`.

Choose the witnesses or unpack the hypotheses as in `⟨n', hn'⟩ : ∃ n' : SABMap (Xo l).univ.t T.t ((jQ ≫ pullback.fst (π ≫ s₁) (spMap β)) ≫ π ≫ pullback.fst T.s (spMap b)), n'.φ = (T.m l rfl).φ := by`. Rewrite using `[hj]`. Conclude with `⟨_, rfl⟩`. Take `⟨m, hm⟩` from `sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ mu n'`. Establish `hg : ∀ p, p ∈ g.opensRange ↔ pullback.fst T.s (spMap b) (pullback.fst s₁ (spMap β) p) ∈ abLocus T.t.G`.

Introduce `p`. Establish `e : pullback.fst T.s (spMap b) (pullback.fst s₁ (spMap β) p) = pullback.fst T.s (spMap (β.comp b)) (hp.isoPullback.hom p)`. Rewrite using `[← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hp.isoPullback_hom_fst]`. Rewrite using `[e]`. Express the relevant statement in the definitionally equal form `p ∈ Set.range g ↔ hp.isoPullback.hom p ∈ pullback.fst T.s (spMap (β.comp b)) ⁻¹' abLocus T.t.G`.

Rewrite using `[← hW₀]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, rfl⟩`. Rewrite using `[← Scheme.Hom.comp_apply, Category.assoc, Iso.inv_hom_id, Category.comp_id]`. Conclude with `z.2`.

Introduce `hz`. Use `⟨⟨_, hz⟩, ?_⟩` and prove the remaining obligations. Use `(Scheme.Hom.comp_apply _ _ _).trans ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `hp.isoPullback.inv (hp.isoPullback.hom p) = p`. Rewrite using `[← Scheme.Hom.comp_apply, Iso.hom_inv_id]`.

Both sides reduce to the same expression. Use `⟨⟨Y, π ≫ s₁, hY, hproj, hflat, jQ, j₂, jo, jd, _, m, ?_⟩, π ≫ pullback.fst _ _, ?_, mu, ?_, hj, hm.symm.trans hn', ?_⟩` and prove the remaining obligations. Use extensionality with `y`. Use `Iff.trans ?_ (jr y).symm` and prove the remaining obligations. Rewrite using `[Set.mem_preimage, ← abLocus_pullback abLocusOne T.t.semi mu.cart.1, Scheme.Hom.comp_apply]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Set `w : pullback (π ≫ s₁) (spMap β) ⟶ pullback s₁ (spMap β)` to `pullback.lift (pullback.fst _ _ ≫ π) (pullback.snd _ _) (by rw [Category.assoc, pullback.condition])`. Establish `hw : pullback.fst s₁ (spMap β) (w y) = π (pullback.fst (π ≫ s₁) (spMap β) y)`. Rewrite using `[← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst]`.

Use `⟨⟨w y, (hg _).2 (by rw [hw]; exact h)⟩, ?_⟩` and prove the remaining obligations. Conclude with `(Scheme.Hom.comp_apply _ _ _).trans hw`. Introduce and unpack `⟨p, hp⟩ replace hp := (Scheme.Hom.comp_apply _ _ _).symm.trans hp`. Use `(hg p.1).1 p.2` as an intermediate fact. Conclude with `(congrArg (fun z => pullback.fst T.s (spMap b) z ∈ abLocus T.t.G) hp).mp this`.

Simplify using `only [Category.assoc, s₁, pullback.condition]`. Establish `key : ∀ h, IsFinite (pullback.lift (π ≫ pullback.fst T.s (spMap b)) (π ≫ s₁) h)` using `fun h => by`. Establish `e : pullback.lift (π ≫ pullback.fst T.s (spMap b)) (π ≫ s₁) h = π`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[pullback.lift_fst]`.

Rewrite using `[pullback.lift_snd]`. Rewrite using `[e]`. Conclude with `hπ`. Conclude with `key _`. Establish `P₁` using `IsPullback.of_hasPullback T.t.G.hom (pullback.fst T.s (spMap b))`.

Establish `Q` using `GlobalTheory.isQProjOver_of_isPullback (P₁.paste_vert (IsPullback.of_hasPullback T.s (spMap b))) T.qproj`. Establish `P₀` using `IsPullback.of_hasPullback T.t.G.hom (π ≫ pullback.fst T.s (spMap b))`. Set `ψ` to `P₁.lift (pullback.fst T.t.G.hom (π ≫ pullback.fst T.s (spMap b))) (pullback.snd _ _ ≫ π) (by rw [Category.assoc]; exact P₀.w)`. Establish `ψ₁ : ψ ≫ _ = _` using `P₁.lift_fst _ _ _`. Establish `ψ₂ : ψ ≫ _ = _` using `P₁.lift_snd _ _ _`.

Establish `P₂ : IsPullback ψ (pullback.snd T.t.G.hom (π ≫ pullback.fst T.s (spMap b))) (pullback.snd T.t.G.hom (pullback.fst T.s (spMap b))) π` using `IsPullback.of_right (by rw [ψ₁]; exact P₀) ψ₂ P₁`. Establish `: IsFinite ψ` using `MorphismProperty.of_isPullback (P := @IsFinite) P₂.flip hπ`. Establish `R` using `GlobalTheory.isQProjOver_comp_of_isFinite ψ Q`. Rewrite `R` using `[← Category.assoc, ψ₂, Category.assoc]`. Conclude with `R`.
-/
theorem Top.exists_cpt_above : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N) (l : Level H) (h : l.A = N) (S e : ℕ) (β : RZ H S N →+* KA l) (b : RZ H n N →+* RZ H S N), 0 < S → n ∣ S → N ∣ S ^ e → IsInc (RZ H S N).subtype (KA l).val.toRingHom β → IsInc (RZ H n N).subtype (RZ H S N).subtype b → ∃ (C : Cpt (Xo l).s (Xo l).univ.t β) (q : C.X ⟶ T.Z) (hq : q ≫ T.s = C.s ≫ spMap b) (qm : SABMap C.t T.t q), IsFinite (pullback.lift q C.s hq) ∧ C.j ≫ q = T.a l h ∧ C.m.φ ≫ qm.φ = (T.m l h).φ ∧ IsQProjOver (C.t.G.hom ≫ C.s) := by
  intro E _ _ _ H D Xo n N T l h S e β b hS _ hN hβ hb
  subst h
  obtain ⟨⟨_, _⟩, _, hfr⟩ := (GlobalTheory.BaseRing.isDedFrac_RZ E H l S e hS hN).2.2 β hβ
  let _ := β.toAlgebra
  obtain ⟨W, f₀, hW₀, hfin, -, fa, fs⟩ := T.fin l rfl (β.comp b) (fun x => (hβ (b x)).trans (hb x))
  have hsm := (Xo l).smooth
  have hnor : Geo.Tor.IsNormalScheme (Xo l).X :=
    (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ (Xo l).s
      (SmoothOfRelativeDimension.smooth D.dim _)).2.1
  let s₁ := pullback.snd T.s (spMap b)
  have hp : IsPullback (pullback.fst s₁ (spMap β) ≫ pullback.fst T.s (spMap b)) (pullback.snd s₁ (spMap β)) T.s
      (spMap (β.comp b)) := by
    rw [spMap_comp]
    exact (IsPullback.of_hasPullback s₁ (spMap β)).paste_horiz (IsPullback.of_hasPullback T.s (spMap b))
  let g := W.ι ≫ hp.isoPullback.inv
  have g₁ : (g ≫ pullback.fst _ _) ≫ pullback.fst _ _ = W.ι ≫ pullback.fst _ _ := by
    rw [Category.assoc, Category.assoc, hp.isoPullback_inv_fst]
  have g₂ : g ≫ pullback.snd _ _ = W.ι ≫ pullback.snd _ _ := by
    rw [Category.assoc, hp.isoPullback_inv_snd]
  have hW : (f₀ ≫ g.isoOpensRange.hom) ≫ g.opensRange.ι = f₀ ≫ g := by
    rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
  obtain ⟨Y, π, jQ, hπ, hY, hproj, hflat, j₂, j₁, jo, jd, jr⟩ :=
    GlobalTheory.exists_normal_finite_model_of_finite_over_open _ (KA l) _ (Xo l).X s₁ (Xo l).s (f₀ ≫ g ≫ pullback.fst _ _) g.opensRange (f₀ ≫ g.isoOpensRange.hom)
      (GlobalTheory.ProjSpace.isProjOver_pullback_snd b T.proj) hnor inferInstance
      (by rw [← Category.assoc]; exact (congrArg (· ≫ _) hW).trans (Category.assoc _ _ _))
      (by
        rw [← Category.assoc]
        exact (congrArg (· ≫ _) hW).trans ((Category.assoc _ _ _).trans ((congrArg (f₀ ≫ ·) g₂).trans fs)))
  obtain ⟨_, _, _, _, _, mu, -⟩ := sabPull Out.CubePf.cubePull (π ≫ pullback.fst T.s (spMap b)) T.t
  have hj : (jQ ≫ pullback.fst (π ≫ s₁) (spMap β)) ≫ π ≫ pullback.fst T.s (spMap b) = T.a l rfl := by
    rw [← fa, ← g₁, ← Category.assoc f₀, ← j₁]
    simp only [Category.assoc]
  obtain ⟨n', hn'⟩ : ∃ n' : SABMap (Xo l).univ.t T.t
      ((jQ ≫ pullback.fst (π ≫ s₁) (spMap β)) ≫ π ≫ pullback.fst T.s (spMap b)), n'.φ = (T.m l rfl).φ := by
    rw [hj]; exact ⟨_, rfl⟩
  obtain ⟨m, hm⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ mu n'
  have hg : ∀ p, p ∈ g.opensRange ↔ pullback.fst T.s (spMap b) (pullback.fst s₁ (spMap β) p) ∈ abLocus T.t.G := by
    intro p
    have e : pullback.fst T.s (spMap b) (pullback.fst s₁ (spMap β) p) =
        pullback.fst T.s (spMap (β.comp b)) (hp.isoPullback.hom p) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hp.isoPullback_hom_fst]
    rw [e]
    change p ∈ Set.range g ↔ hp.isoPullback.hom p ∈ pullback.fst T.s (spMap (β.comp b)) ⁻¹' abLocus T.t.G
    rw [← hW₀]
    constructor
    · rintro ⟨z, rfl⟩
      rw [← Scheme.Hom.comp_apply, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact z.2
    · intro hz
      refine ⟨⟨_, hz⟩, ?_⟩
      refine (Scheme.Hom.comp_apply _ _ _).trans ?_
      change hp.isoPullback.inv (hp.isoPullback.hom p) = p
      rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
      rfl
  refine ⟨⟨Y, π ≫ s₁, hY, hproj, hflat, jQ, j₂, jo, jd, _, m, ?_⟩, π ≫ pullback.fst _ _, ?_, mu, ?_, hj,
    hm.symm.trans hn', ?_⟩
  · ext y
    refine Iff.trans ?_ (jr y).symm
    rw [Set.mem_preimage, ← abLocus_pullback abLocusOne T.t.semi mu.cart.1, Scheme.Hom.comp_apply]
    constructor
    · intro h
      let w : pullback (π ≫ s₁) (spMap β) ⟶ pullback s₁ (spMap β) :=
        pullback.lift (pullback.fst _ _ ≫ π) (pullback.snd _ _) (by rw [Category.assoc, pullback.condition])
      have hw : pullback.fst s₁ (spMap β) (w y) = π (pullback.fst (π ≫ s₁) (spMap β) y) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst]
      refine ⟨⟨w y, (hg _).2 (by rw [hw]; exact h)⟩, ?_⟩
      exact (Scheme.Hom.comp_apply _ _ _).trans hw
    · rintro ⟨p, hp⟩
      replace hp := (Scheme.Hom.comp_apply _ _ _).symm.trans hp
      have := (hg p.1).1 p.2
      exact (congrArg (fun z => pullback.fst T.s (spMap b) z ∈ abLocus T.t.G) hp).mp this
  · simp only [Category.assoc, s₁, pullback.condition]
  · have key : ∀ h, IsFinite (pullback.lift (π ≫ pullback.fst T.s (spMap b)) (π ≫ s₁) h) := fun h => by
      have e : pullback.lift (π ≫ pullback.fst T.s (spMap b)) (π ≫ s₁) h = π := by
        apply pullback.hom_ext
        · rw [pullback.lift_fst]
        · rw [pullback.lift_snd]
      rw [e]; exact hπ
    exact key _
  · have P₁ := IsPullback.of_hasPullback T.t.G.hom (pullback.fst T.s (spMap b))
    have Q := GlobalTheory.isQProjOver_of_isPullback (P₁.paste_vert (IsPullback.of_hasPullback T.s (spMap b))) T.qproj
    have P₀ := IsPullback.of_hasPullback T.t.G.hom (π ≫ pullback.fst T.s (spMap b))
    let ψ := P₁.lift (pullback.fst T.t.G.hom (π ≫ pullback.fst T.s (spMap b))) (pullback.snd _ _ ≫ π)
      (by rw [Category.assoc]; exact P₀.w)
    have ψ₁ : ψ ≫ _ = _ := P₁.lift_fst _ _ _
    have ψ₂ : ψ ≫ _ = _ := P₁.lift_snd _ _ _
    have P₂ : IsPullback ψ (pullback.snd T.t.G.hom (π ≫ pullback.fst T.s (spMap b)))
        (pullback.snd T.t.G.hom (pullback.fst T.s (spMap b))) π :=
      IsPullback.of_right (by rw [ψ₁]; exact P₀) ψ₂ P₁
    have : IsFinite ψ := MorphismProperty.of_isPullback (P := @IsFinite) P₂.flip hπ
    have R := GlobalTheory.isQProjOver_comp_of_isFinite ψ Q
    rw [← Category.assoc, ψ₂, Category.assoc] at R
    exact R

end GlobalTheory.Models
