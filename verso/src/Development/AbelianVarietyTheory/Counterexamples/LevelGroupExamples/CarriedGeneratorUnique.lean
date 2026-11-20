import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IsLevMove
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.LevelGroupEqTopOfCoprime
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelActionOverlapLeSourceChart

noncomputable section

namespace GlobalTheory.LevelMoveTest

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

/- English proof (translation)
Establish `p1 : IsPullback (snd (Over.mk x) Xo.univ.t.G).left (fst (Over.mk x) Xo.univ.t.G).left Xo.univ.t.G.hom x` using `(IsPullback.of_hasPullback x Xo.univ.t.G.hom).flip`. Establish `p2 : IsPullback (snd (Over.mk (x ≫ ρ)) Xo.univ.t.G).left (fst (Over.mk (x ≫ ρ)) Xo.univ.t.G).left Xo.univ.t.G.hom (x ≫ ρ)` using `(IsPullback.of_hasPullback (x ≫ ρ) Xo.univ.t.G.hom).flip`. Establish `p3` using `p1.paste_horiz ν.cart.1`. Establish `: pm = (p3.isoIsPullback _ _ p2).hom`. Apply `p2.hom_ext` to reduce the goal to its premises.

Rewrite using `[hs]`. Simplify using the standard rewrite rules. Rewrite using `[hf]`. Simplify using the standard rewrite rules. Rewrite using `[this]`.

Use `infer_instance`.
-/
theorem pinned_isIso {S : Type} [CommRing S] {ρ : Xo.X ⟶ Xo.X} (ν : SABMap Xo.univ.t Xo.univ.t ρ)
    (x : Sp S ⟶ Xo.X) (pm : Gx x ⟶ Gx (x ≫ ρ))
    (hf : pm ≫ (fst (Over.mk (x ≫ ρ)) Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left)
    (hs : pm ≫ (snd (Over.mk (x ≫ ρ)) Xo.univ.t.G).left = (snd (Over.mk x) Xo.univ.t.G).left ≫ ν.φ) :
    IsIso pm := by
  have p1 : IsPullback (snd (Over.mk x) Xo.univ.t.G).left (fst (Over.mk x) Xo.univ.t.G).left Xo.univ.t.G.hom x :=
    (IsPullback.of_hasPullback x Xo.univ.t.G.hom).flip
  have p2 : IsPullback (snd (Over.mk (x ≫ ρ)) Xo.univ.t.G).left (fst (Over.mk (x ≫ ρ)) Xo.univ.t.G).left
      Xo.univ.t.G.hom (x ≫ ρ) := (IsPullback.of_hasPullback (x ≫ ρ) Xo.univ.t.G.hom).flip
  have p3 := p1.paste_horiz ν.cart.1
  have : pm = (p3.isoIsPullback _ _ p2).hom := by
    apply p2.hom_ext
    · rw [hs]; simp
    · rw [hf]; simp
  rw [this]; infer_instance

/- English proof (translation)
Use `haveI := pinned_isIso ν x pm hf hs`. Establish `inj : Function.Injective (pm.app ((PPx (x ≫ ρ)).U (fun _ => i))).hom` using `(ConcreteCategory.bijective_of_isIso (pm.app ((PPx (x ≫ ρ)).U (fun _ => i)))).1`. Apply `inj` to reduce the goal to its premises. Set `W : Xo.univ.t.PP.L.ι → (Gx x).Opens` to `fun j => (snd (Over.mk x) Xo.univ.t.G).left ⁻¹ᵁ ((LB.div (Xo.univ.t.PP.L.pull ν.cm.F) Xo.univ.t.PP.L).U ((fun _ => i), j))`. Establish `hW : ∀ j, W j ≤ pm ⁻¹ᵁ (PPx (x ≫ ρ)).U (fun _ => i)` using `fun j => GlobalTheory.LevActCompare.overlap_le_tgt ν.cm.F pm hs i j`.

Use `(Gx x).sheaf.eq_of_locally_eq' W _ (fun j => homOfLE (hW j)) ?_ _ _ ?_` and prove the remaining obligations. Introduce `z hz`. Establish `hc : (snd (Over.mk x) Xo.univ.t.G).left.base z ∈ (⨆ j, Xo.univ.t.PP.L.U j)`. Rewrite using `[Xo.univ.t.PP.isLB.cover]`. Discharge the goal by the elementary cases of `trivial`.

Take `⟨j, hj⟩` from `TopologicalSpace.Opens.mem_iSup.1 hc`. Use `TopologicalSpace.Opens.mem_iSup.2 ⟨j, ?_, hj⟩` and prove the remaining obligations. Use `Set.mem_iInter.2 fun _ => ?_` and prove the remaining obligations. Establish `h1 : (pm ≫ (snd (Over.mk (x ≫ ρ)) Xo.univ.t.G).left).base z ∈ (Xo.univ.t.PP.L.U i : Set _)` using `Set.mem_iInter.1 hz 0`. Rewrite `h1` using `[hs]`.

Conclude with `h1`. Introduce `j`. Conclude with `h i j _ rfl (hW j)`.
-/
theorem carried_generator_unique {S : Type} [CommRing S] {ρ : Xo.X ⟶ Xo.X} (ν : SABMap Xo.univ.t Xo.univ.t ρ)
    (x : Sp S ⟶ Xo.X) (pm : Gx x ⟶ Gx (x ≫ ρ))
    (hf : pm ≫ (fst (Over.mk (x ≫ ρ)) Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left)
    (hs : pm ≫ (snd (Over.mk (x ≫ ρ)) Xo.univ.t.G).left = (snd (Over.mk x) Xo.univ.t.G).left ≫ ν.φ)
    (s' s'' : LB.Sec (PPx (x ≫ ρ)))
    (h : ∀ (i j : Xo.univ.t.PP.L.ι) (W : (Gx x).Opens),
        W = (snd (Over.mk x) Xo.univ.t.G).left ⁻¹ᵁ
          ((LB.div (Xo.univ.t.PP.L.pull ν.cm.F) Xo.univ.t.PP.L).U ((fun _ => i), j)) →
        ∀ (h₁ : W ≤ pm ⁻¹ᵁ (PPx (x ≫ ρ)).U (fun _ => i)),
        (pm.appLE ((PPx (x ≫ ρ)).U (fun _ => i)) W h₁).hom (s'.f (fun _ => i)) =
        (pm.appLE ((PPx (x ≫ ρ)).U (fun _ => i)) W h₁).hom (s''.f (fun _ => i)))
    (i : Xo.univ.t.PP.L.ι) : s'.f (fun _ => i) = s''.f (fun _ => i) := by
  haveI := pinned_isIso ν x pm hf hs
  have inj : Function.Injective (pm.app ((PPx (x ≫ ρ)).U (fun _ => i))).hom :=
    (ConcreteCategory.bijective_of_isIso (pm.app ((PPx (x ≫ ρ)).U (fun _ => i)))).1
  apply inj
  let W : Xo.univ.t.PP.L.ι → (Gx x).Opens := fun j => (snd (Over.mk x) Xo.univ.t.G).left ⁻¹ᵁ
          ((LB.div (Xo.univ.t.PP.L.pull ν.cm.F) Xo.univ.t.PP.L).U ((fun _ => i), j))
  have hW : ∀ j, W j ≤ pm ⁻¹ᵁ (PPx (x ≫ ρ)).U (fun _ => i) := fun j =>
    GlobalTheory.LevActCompare.overlap_le_tgt ν.cm.F pm hs i j
  refine (Gx x).sheaf.eq_of_locally_eq' W _ (fun j => homOfLE (hW j)) ?_ _ _ ?_
  · intro z hz
    have hc : (snd (Over.mk x) Xo.univ.t.G).left.base z ∈ (⨆ j, Xo.univ.t.PP.L.U j) := by
      rw [Xo.univ.t.PP.isLB.cover]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hc
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨j, ?_, hj⟩
    refine Set.mem_iInter.2 fun _ => ?_
    have h1 : (pm ≫ (snd (Over.mk (x ≫ ρ)) Xo.univ.t.G).left).base z ∈ (Xo.univ.t.PP.L.U i : Set _) :=
      Set.mem_iInter.1 hz 0
    rw [hs] at h1
    exact h1
  · intro j
    exact h i j _ rfl (hW j)

/- English proof (translation)
Take `⟨x', o', u', t', e', b', s', g'⟩` from `y'`. Take `⟨x'', o'', u'', t'', e'', b'', s'', g''⟩` from `y''`. Take `⟨hx, hu, pm, w, hf, hs, hc, h⟩` from `h'`. Take `⟨hx2, hu2, pm2, w2, hf2, hs2, hc2, h2⟩` from `h''`. Simplify using `only at hx hu hf hs h hx2 hu2 hf2 hs2 h2 pm pm2`.

Substitute `hx hx2` using the available equality. Take `rfl` from `hw w w2 hc hc2`. Establish `p2 : IsPullback (snd (Over.mk (y.x ≫ ρ)) Xo.univ.t.G).left (fst (Over.mk (y.x ≫ ρ)) Xo.univ.t.G).left Xo.univ.t.G.hom (y.x ≫ ρ)` using `(IsPullback.of_hasPullback (y.x ≫ ρ) Xo.univ.t.G.hom).flip`. Take `rfl : pm = pm2` from `p2.hom_ext (hs.trans hs2.symm) (hf.trans hf2.symm)`. Take `rfl : u' = u''` from `by funext τ i; rw [hu, hu2]`.

Establish `hs' : s' = s''`. Establish `key` using `carried_generator_unique ν y.x pm hf hs s' s'' (fun i j W hW h₁ => by`. Substitute `hW` using the available equality. Conclude with `(h i j _ rfl le_rfl h₁ (GlobalTheory.LevActCompare.levelAction_overlap_le_source_chart ν.cm.F y.x i j)).trans (h2 i j _ rfl le_rfl h₁ (GlobalTheory.LevActCompare.levelAction_overlap_le_source_chart ν.cm.F y.x i j)).symm)`. Take `⟨f', c'⟩` from `s'`.

Take `⟨f'', c''⟩` from `s''`. Choose the witnesses or unpack the hypotheses as in `rfl : f' = f'' := by`. Use function extensionality and compare the values at `i`. Establish `: i = fun _ => i 0` using `funext fun k => congrArg i (Subsingleton.elim _ _)`. Rewrite using `[this]`.

Conclude with `key (i 0)`. Both sides reduce to the same expression. Substitute `hs'` using the available equality. Both sides reduce to the same expression.
-/
theorem frMove_unique {S : Type} [CommRing S] [Algebra c.F S] {ρ : Xo.X ⟶ Xo.X}
    (ν : SABMap Xo.univ.t Xo.univ.t ρ) (hw : ∀ w w', CubIso ν w → CubIso ν w' → w = w')
    (y y' y'' : FrPt Xo c S) (h' : FrMove ρ ν y y') (h'' : FrMove ρ ν y y'') : y' = y'' := by
  obtain ⟨x', o', u', t', e', b', s', g'⟩ := y'
  obtain ⟨x'', o'', u'', t'', e'', b'', s'', g''⟩ := y''
  obtain ⟨hx, hu, pm, w, hf, hs, hc, h⟩ := h'
  obtain ⟨hx2, hu2, pm2, w2, hf2, hs2, hc2, h2⟩ := h''
  dsimp only at hx hu hf hs h hx2 hu2 hf2 hs2 h2 pm pm2
  subst hx hx2
  obtain rfl := hw w w2 hc hc2
  have p2 : IsPullback (snd (Over.mk (y.x ≫ ρ)) Xo.univ.t.G).left (fst (Over.mk (y.x ≫ ρ)) Xo.univ.t.G).left
      Xo.univ.t.G.hom (y.x ≫ ρ) := (IsPullback.of_hasPullback (y.x ≫ ρ) Xo.univ.t.G.hom).flip
  obtain rfl : pm = pm2 := p2.hom_ext (hs.trans hs2.symm) (hf.trans hf2.symm)
  obtain rfl : u' = u'' := by funext τ i; rw [hu, hu2]
  have hs' : s' = s'' := by
    have key := carried_generator_unique ν y.x pm hf hs s' s'' (fun i j W hW h₁ => by
      subst hW
      exact (h i j _ rfl le_rfl h₁ (GlobalTheory.LevActCompare.levelAction_overlap_le_source_chart ν.cm.F y.x i j)).trans
        (h2 i j _ rfl le_rfl h₁ (GlobalTheory.LevActCompare.levelAction_overlap_le_source_chart ν.cm.F y.x i j)).symm)
    obtain ⟨f', c'⟩ := s'
    obtain ⟨f'', c''⟩ := s''
    obtain rfl : f' = f'' := by
      funext i
      have : i = fun _ => i 0 := funext fun k => congrArg i (Subsingleton.elim _ _)
      rw [this]
      exact key (i 0)
    rfl
  subst hs'
  rfl

end GlobalTheory.LevelMoveTest
