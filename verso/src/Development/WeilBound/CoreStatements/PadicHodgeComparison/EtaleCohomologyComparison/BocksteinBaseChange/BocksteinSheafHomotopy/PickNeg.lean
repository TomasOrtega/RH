import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.BockOf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.ReductionLemmas

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace CrystallineSemistableComparison

open GlobalTheory.EtC

namespace CyclicComplexMaps

def semiComp {T S R : Type} [CommRing T] [CommRing S] [CommRing R] {I : GlobalTheory.EtC.Cx T} {J : GlobalTheory.EtC.Cx S} {L : GlobalTheory.EtC.Cx R}
    (τ : SemiMap I J) (ρ : SemiMap J L) : SemiMap I L where
  app U s := (ρ.app U s).comp (τ.app U s)
  nat g s a := by simp only [AddMonoidHom.comp_apply]; rw [ρ.nat, τ.nat]
  comm U s t a := by simp only [AddMonoidHom.comp_apply]; rw [ρ.comm, τ.comm]

/- English proof (translation)
Unfold `pick`. Conclude with `dif_neg h`.
-/
theorem pick_neg' {α : Type*} [Zero α] {P : α → Prop} (h : ¬ ∃ a, P a) : pick P = 0 := by
  unfold pick
  exact dif_neg h

/- English proof (translation)
Take `⟨α, rfl⟩` from `x.mk_surjective`. Rewrite using `[SemiMap.op_spec (0 : SemiMap I J) E n α 0 (fun p s h U x => ?_)]`. Both sides reduce to the same expression. Rewrite using `[Cocycle.coe_zero, CupSpec.ev_zero]`. Both sides reduce to the same expression.
-/
theorem op_zero {S R : Type} [CommRing S] [CommRing R] {I : GlobalTheory.EtC.Cx S} {J : GlobalTheory.EtC.Cx R} (E : Spc) (n : ℤ)
    (x : CohomologyClass ((chains S).obj E) I n) : (0 : SemiMap I J).op.app E n x = 0 := by
  obtain ⟨α, rfl⟩ := x.mk_surjective
  rw [SemiMap.op_spec (0 : SemiMap I J) E n α 0 (fun p s h U x => ?_)]
  · rfl
  · rw [Cocycle.coe_zero, CupSpec.ev_zero]
    rfl

end CyclicComplexMaps

/- English proof (translation)
Introduce `Q q _ _ h i π hπ E n z`. Distinguish the cases in `hρ : ∃ ρ : SemiMap (res (ZMod q) (tw q i)) (res (ZMod Q) ((restr (ZMod.castHom h (ZMod q))).obj (tw q i))), ∀ (U : Scheme.{0}) (a : Sec (tw q i) U), ρ.app U 0 (Sec.map (resι (ZMod q) (tw q i)) a) = Sec.map (resι (ZMod Q) ((restr (ZMod.castHom h (ZMod q))).obj (tw q i))) (show Sec …`. Establish `hρ' : ∀ (U : Scheme.{0}) (a : Sec (tw q i) U), (restrMap (ZMod.castHom h (ZMod q)) (tw q i)).app U 0 (Sec.map (resι (ZMod q) (tw q i)) a) = Sec.map (resι (ZMod Q) ((restr (ZMod.castHom h (ZMod q))).obj (tw q i))) (show Sec ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)) U from a …` using `pick_spec hρ`. Establish `hτ` using `hF.et.red Q q h i`. Set `σ` to `CyclicComplexMaps.semiComp (redMap Q q i) (restrMap (ZMod.castHom h (ZMod q)) (tw q i))`.

Establish `hg : resι (ZMod Q) (tw Q i) ≫ (CyclicComplexMaps.cxHom σ).f 0 = π ≫ resι (ZMod Q) ((restr (ZMod.castHom h (ZMod q))).obj (tw q i))`. Use `CyclicComplexMaps.tw_ext _ _ (fun U ζ => ?_)` and prove the remaining obligations. Take `⟨ξ, hξ⟩` from `CyclicComplexMaps.prim_pow h ζ`. Express the relevant statement in the definitionally equal form `(restrMap (ZMod.castHom h (ZMod q)) (tw q i)).app U 0 ((redMap Q q i).app U 0 (resGen i ζ)) = Sec.map (resι (ZMod Q) ((restr (ZMod.castHom h (ZMod q))).obj (tw q i))) (Sec.map π (twGen i ζ))`. Rewrite using `[hτ U ζ ξ hξ, hπ U ζ ξ hξ]`.

Conclude with `hρ' U (twGen i ξ)`. Take `⟨α, rfl⟩` from `z.mk_surjective`. Take `⟨β, hβ⟩` from `SemiMap.image_exists (redMap Q q i) E n α`. Take `⟨γ, hγ⟩` from `SemiMap.image_exists (restrMap (ZMod.castHom h (ZMod q)) (tw q i)) E n β`. Express the relevant statement in the definitionally equal form `(restrMap (ZMod.castHom h (ZMod q)) (tw q i)).op.app E n ((redMap Q q i).op.app E n (CohomologyClass.mk α)) = _`.

Rewrite using `[SemiMap.op_spec _ E n α β hβ, SemiMap.op_spec _ E n β γ hγ, ← CyclicComplexMaps.cpost_of_aug _ π (CyclicComplexMaps.cxHom σ) hg n (CohomologyClass.mk α), cpost_mk]`. Use `congr 1`. Apply `Cocycle.ext` to reduce the goal to its premises. Apply `CupSpec.ev_ext` to reduce the goal to its premises. Introduce `p s hs U x`.

Rewrite using `[hγ, hβ]`. Conclude with `(CyclicComplexMaps.ev_comp α.1 (CyclicComplexMaps.cxHom σ) p s hs U x).symm`. Establish `h0 : restrMap (ZMod.castHom h (ZMod q)) (tw q i) = 0` using `CyclicComplexMaps.pick_neg' hρ`. Take `⟨y, hy⟩` from `(hF.a8 (ZMod Q) (ZMod q) (ZMod.castHom h (ZMod q)) E (tw q i) n).2 (HK.post _ ((chains _).obj E) π n z)`. Rewrite using `[← hy]`.

Express the relevant statement in the definitionally equal form `(restrMap (ZMod.castHom h (ZMod q)) (tw q i)).op.app E n _ = (restrMap (ZMod.castHom h (ZMod q)) (tw q i)).op.app E n _`. Rewrite using `[h0, CyclicComplexMaps.op_zero, CyclicComplexMaps.op_zero]`.
-/
theorem redSh (hF : FormalIn) : InRedSh := by
  intro Q q _ _ h i π hπ E n z
  by_cases hρ : ∃ ρ : SemiMap (res (ZMod q) (tw q i)) (res (ZMod Q) ((restr (ZMod.castHom h (ZMod q))).obj (tw q i))),
      ∀ (U : Scheme.{0}) (a : Sec (tw q i) U), ρ.app U 0 (Sec.map (resι (ZMod q) (tw q i)) a) =
        Sec.map (resι (ZMod Q) ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)))
          (show Sec ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)) U from a)
  · have hρ' : ∀ (U : Scheme.{0}) (a : Sec (tw q i) U),
        (restrMap (ZMod.castHom h (ZMod q)) (tw q i)).app U 0 (Sec.map (resι (ZMod q) (tw q i)) a) =
          Sec.map (resι (ZMod Q) ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)))
            (show Sec ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)) U from a) := pick_spec hρ
    have hτ := hF.et.red Q q h i
    let σ := CyclicComplexMaps.semiComp (redMap Q q i) (restrMap (ZMod.castHom h (ZMod q)) (tw q i))
    have hg : resι (ZMod Q) (tw Q i) ≫ (CyclicComplexMaps.cxHom σ).f 0 =
        π ≫ resι (ZMod Q) ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)) := by
      refine CyclicComplexMaps.tw_ext _ _ (fun U ζ => ?_)
      obtain ⟨ξ, hξ⟩ := CyclicComplexMaps.prim_pow h ζ
      change (restrMap (ZMod.castHom h (ZMod q)) (tw q i)).app U 0 ((redMap Q q i).app U 0 (resGen i ζ)) =
        Sec.map (resι (ZMod Q) ((restr (ZMod.castHom h (ZMod q))).obj (tw q i))) (Sec.map π (twGen i ζ))
      rw [hτ U ζ ξ hξ, hπ U ζ ξ hξ]
      exact hρ' U (twGen i ξ)
    obtain ⟨α, rfl⟩ := z.mk_surjective
    obtain ⟨β, hβ⟩ := SemiMap.image_exists (redMap Q q i) E n α
    obtain ⟨γ, hγ⟩ := SemiMap.image_exists (restrMap (ZMod.castHom h (ZMod q)) (tw q i)) E n β
    change (restrMap (ZMod.castHom h (ZMod q)) (tw q i)).op.app E n ((redMap Q q i).op.app E n (CohomologyClass.mk α)) = _
    rw [SemiMap.op_spec _ E n α β hβ, SemiMap.op_spec _ E n β γ hγ,
      ← CyclicComplexMaps.cpost_of_aug _ π (CyclicComplexMaps.cxHom σ) hg n (CohomologyClass.mk α), cpost_mk]
    congr 1
    apply Cocycle.ext
    apply CupSpec.ev_ext
    intro p s hs U x
    rw [hγ, hβ]
    exact (CyclicComplexMaps.ev_comp α.1 (CyclicComplexMaps.cxHom σ) p s hs U x).symm
  · have h0 : restrMap (ZMod.castHom h (ZMod q)) (tw q i) = 0 := CyclicComplexMaps.pick_neg' hρ
    obtain ⟨y, hy⟩ := (hF.a8 (ZMod Q) (ZMod q) (ZMod.castHom h (ZMod q)) E (tw q i) n).2
      (HK.post _ ((chains _).obj E) π n z)
    rw [← hy]
    change (restrMap (ZMod.castHom h (ZMod q)) (tw q i)).op.app E n _ = (restrMap (ZMod.castHom h (ZMod q)) (tw q i)).op.app E n _
    rw [h0, CyclicComplexMaps.op_zero, CyclicComplexMaps.op_zero]

/- English proof (translation)
Introduce `hF` and use `bock_of hS (redSh hF) hF`.
-/
theorem bock_tw (hS : InTwSeq) : BocksteinInputFromFormal := fun hF => bock_of hS (redSh hF) hF

end CrystallineSemistableComparison
