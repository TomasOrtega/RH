import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.ResSplitProof

/- English proof (translation)
Establish `h` using `φ.hom.naturality g.op`. Conclude with `congrArg (fun k => ModuleCat.Hom.hom k x) h`.
-/
theorem map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  have h := φ.hom.naturality g.op
  exact congrArg (fun k => ModuleCat.Hom.hom k x) h

/- English proof (translation)
Introduce `hRL hLS hLC R _ F U hU s x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨ι, f, hf⟩` from `hLS U hU _ (hRL R F s U x hx)`. Take `⟨W, j, hj, -, -, hglue⟩` from `hLC U ι f`.

Establish `hP : ∀ a, ∃ y, Sec.map ((GlobalTheory.EtC.res R F).d (↑s) (↑(s + 1))) y = Sec.res (j a) x` using `fun a => hf (W a) (j a) a (hj a)`. Use `choose y hy using hP`. Take `⟨z, hz, -⟩` from `hglue R _ y`. Take `⟨w, -, huniq⟩` from `hglue R _ (fun a => Sec.res (j a) x)`. Use `⟨z, ?_⟩` and prove the remaining obligations.

Establish `h1` using `huniq (Sec.map ((GlobalTheory.EtC.res R F).d (↑s) (↑(s + 1))) z) (fun a => by rw [← map_res, hz a, hy a])`. Establish `h2` using `huniq x (fun a => rfl)`. Conclude with `h1.trans h2.symm`. Introduce and unpack `⟨y, rfl⟩`. Establish `h` using `(GlobalTheory.EtC.res R F).d_comp_d (↑s) (↑(s + 1)) (↑(s + 1 + 1))`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem resSplit : CrystallineSemistableComparison.E.ResLoc → CrystallineSemistableComparison.E.LocSplit → CrystallineSemistableComparison.E.LcCover → CrystallineSemistableComparison.E.ResSplit := by
  intro hRL hLS hLC R _ F U hU s x
  constructor
  · intro hx
    obtain ⟨ι, f, hf⟩ := hLS U hU _ (hRL R F s U x hx)
    obtain ⟨W, j, hj, -, -, hglue⟩ := hLC U ι f
    have hP : ∀ a, ∃ y, Sec.map ((GlobalTheory.EtC.res R F).d (↑s) (↑(s + 1))) y = Sec.res (j a) x :=
      fun a => hf (W a) (j a) a (hj a)
    choose y hy using hP
    obtain ⟨z, hz, -⟩ := hglue R _ y
    obtain ⟨w, -, huniq⟩ := hglue R _ (fun a => Sec.res (j a) x)
    refine ⟨z, ?_⟩
    have h1 := huniq (Sec.map ((GlobalTheory.EtC.res R F).d (↑s) (↑(s + 1))) z)
      (fun a => by rw [← map_res, hz a, hy a])
    have h2 := huniq x (fun a => rfl)
    exact h1.trans h2.symm
  · rintro ⟨y, rfl⟩
    have h := (GlobalTheory.EtC.res R F).d_comp_d (↑s) (↑(s + 1)) (↑(s + 1 + 1))
    calc Sec.map ((GlobalTheory.EtC.res R F).d (↑(s + 1)) (↑(s + 1 + 1)))
          (Sec.map ((GlobalTheory.EtC.res R F).d (↑s) (↑(s + 1))) y)
        = Sec.map ((GlobalTheory.EtC.res R F).d (↑s) (↑(s + 1)) ≫ (GlobalTheory.EtC.res R F).d (↑(s + 1)) (↑(s + 1 + 1))) y := rfl
      _ = Sec.map 0 y := by rw [h]
      _ = 0 := by first | rfl | simp [Sec.map]

end GlobalTheory.CompanionTheory.ResSplitProof
