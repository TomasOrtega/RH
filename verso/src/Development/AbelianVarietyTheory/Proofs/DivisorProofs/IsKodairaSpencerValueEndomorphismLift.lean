import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSExist

/- English proof (translation)
Introduce `R _ A _ A' _ i h O _ a a' hi z f w hf`. Use `haveI := a.hom z`. Use `haveI := a'.hom z`. Take `⟨k, ⟨d, hd, e⟩, l⟩` from `hf`. Rewrite using `[act_apply]`.

Establish `hm` using `push_mem_liftFil (epsDP R) h h (a.act z) (a'.act z) (e := (hi z).symm) hd`. Establish `hl` using `l.push (a.act z)`. Use `⟨push (dp0 R) (𝟙 _) (a.act z) k, ⟨_, hm, fun c ↦ ?_⟩, hl⟩` and prove the remaining obligations. Establish `kk` using `(homMor (dp0 R) (𝟙 _) (a.act z)).comp (constMor A)`. Establish `hM` using `homMor (epsDP R) (DeRham.epsRed R) (a.act z)`.

Establish `e1` using `GrpMor.pull_pull (constMor A) hM kk (fun _ ↦ rfl) (by simp) c`. Establish `e2` using `GrpMor.pull_pull (homMor (dp0 R) (𝟙 _) (a.act z)) (constMor A) kk (fun _ ↦ rfl) rfl c`. Rewrite using `[push_apply]`. Express the relevant statement in the definitionally equal form `d (hM.pull ((constMor A).pull c)) = _`. Rewrite using `[e1, ← e2, e]`.

Both sides reduce to the same expression.
-/
theorem isKSValue_act : ∀ {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp (DualNumber R))} [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed R) i) {O : Type} [CommRing O] (a : OAct O A) (a' : OAct O A'), (∀ z, (a.act z).left ≫ i = i ≫ (a'.act z).left) → ∀ (z : O) {f : HdR A} {w : epsR R ⟶ A}, IsKSValue h f w → IsKSValue h (act (dp0 R) (𝟙 _) a z f) (w ≫ a.act z) := by
  intro R _ A _ A' _ i h O _ a a' hi z f w hf
  haveI := a.hom z
  haveI := a'.hom z
  obtain ⟨k, ⟨d, hd, e⟩, l⟩ := hf
  rw [act_apply]
  have hm := push_mem_liftFil (epsDP R) h h (a.act z) (a'.act z) (e := (hi z).symm) hd
  have hl := l.push (a.act z)
  refine ⟨push (dp0 R) (𝟙 _) (a.act z) k, ⟨_, hm, fun c ↦ ?_⟩, hl⟩
  have kk := (homMor (dp0 R) (𝟙 _) (a.act z)).comp (constMor A)
  have hM := homMor (epsDP R) (DeRham.epsRed R) (a.act z)
  have e1 := GrpMor.pull_pull (constMor A) hM kk (fun _ ↦ rfl) (by simp) c
  have e2 := GrpMor.pull_pull (homMor (dp0 R) (𝟙 _) (a.act z)) (constMor A) kk (fun _ ↦ rfl) rfl c
  rw [push_apply]
  change d (hM.pull ((constMor A).pull c)) = _
  rw [e1, ← e2, e]
  rfl
end GlobalTheory.KSExist
