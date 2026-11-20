import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EtEdge

/- English proof (translation)
Introduce `hExt hNat hIn`. Unfold `CrystallineSemistableComparison.E.InSch at hIn`. Unfold `CrystallineSemistableComparison.E.RepBasic`. Introduce `R _ I X n`. Unfold `CrystallineSemistableComparison.E.Rep`.

Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x`. Take `⟨α, rfl⟩` from `CohomologyClass.mk_surjective x`. Conclude with `⟨_, α, rfl, rfl⟩`. Introduce and unpack `x a ⟨α, -, rfl⟩ m`.

Distinguish the cases in `hm : n + 1 = m`. Conclude with `((hIn R X I (n - 1) n m (by omega) hm).2 α).1`. Rewrite using `[HomologicalComplex.shape I n m (by simpa using hm)]`. Simplify using `[GlobalTheory.EtC.Sec.map]`. Introduce and unpack `x y a b ⟨α, rfl, rfl⟩ ⟨β, rfl, rfl⟩`.

Establish `hs` using `(hExt R (sch.obj X) I n α β).2 0 n (by simp) X (𝟙 X : X ⟶ X)`. Conclude with `⟨⟨α + β, rfl, hs.1⟩, ⟨α - β, rfl, hs.2.1⟩⟩`. Introduce and unpack `a ⟨α, h0, rfl⟩ k hk`. Conclude with `((hIn R X I k n (n + 1) hk rfl).2 α).2.1 h0`. Introduce and unpack `Y f x a ⟨α, rfl, rfl⟩`.

Use `⟨GlobalTheory.EtC.zcomp (Cocycle.ofHom ((chains R).map (sch.map f))) α (zero_add n), rfl, ?_⟩` and prove the remaining obligations. Establish `h2` using `(hNat R (sch.obj X) I n (α : Cochain _ I n) 0 n (by simp) Y).2 (sch.obj Y) (sch.map f) (𝟙 Y : Y ⟶ Y)`. Establish `h1` using `(hNat R (sch.obj X) I n (α : Cochain _ I n) 0 n (by simp) X).1 Y f (𝟙 X : X ⟶ X)`. Establish `e : (Sx.map (sch.map f) (𝟙 Y : Y ⟶ Y) : Sx (sch.obj X) 0 Y) = Sx.res f (𝟙 X : X ⟶ X)` using `by show 𝟙 Y ≫ f = f ≫ 𝟙 X`. Simplify using the standard rewrite rules.

Use `h2.trans ?_` and prove the remaining obligations. Rewrite using `[e]`. Conclude with `h1`.
-/
theorem repBasic : CrystallineSemistableComparison.E.EvExt → CrystallineSemistableComparison.E.EvNat → CrystallineSemistableComparison.E.InSch → CrystallineSemistableComparison.E.RepBasic := by
  intro hExt hNat hIn
  unfold CrystallineSemistableComparison.E.InSch at hIn
  unfold CrystallineSemistableComparison.E.RepBasic
  intro R _ I X n
  unfold CrystallineSemistableComparison.E.Rep
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective x
    exact ⟨_, α, rfl, rfl⟩
  · rintro x a ⟨α, -, rfl⟩ m
    by_cases hm : n + 1 = m
    · exact ((hIn R X I (n - 1) n m (by omega) hm).2 α).1
    · rw [HomologicalComplex.shape I n m (by simpa using hm)]
      simp [GlobalTheory.EtC.Sec.map]
  · rintro x y a b ⟨α, rfl, rfl⟩ ⟨β, rfl, rfl⟩
    have hs := (hExt R (sch.obj X) I n α β).2 0 n (by simp) X (𝟙 X : X ⟶ X)
    exact ⟨⟨α + β, rfl, hs.1⟩, ⟨α - β, rfl, hs.2.1⟩⟩
  · rintro a ⟨α, h0, rfl⟩ k hk
    exact ((hIn R X I k n (n + 1) hk rfl).2 α).2.1 h0
  · rintro Y f x a ⟨α, rfl, rfl⟩
    refine ⟨GlobalTheory.EtC.zcomp (Cocycle.ofHom ((chains R).map (sch.map f))) α (zero_add n), rfl, ?_⟩
    have h2 := (hNat R (sch.obj X) I n (α : Cochain _ I n) 0 n (by simp) Y).2 (sch.obj Y) (sch.map f)
      (𝟙 Y : Y ⟶ Y)
    have h1 := (hNat R (sch.obj X) I n (α : Cochain _ I n) 0 n (by simp) X).1 Y f (𝟙 X : X ⟶ X)
    have e : (Sx.map (sch.map f) (𝟙 Y : Y ⟶ Y) : Sx (sch.obj X) 0 Y) = Sx.res f (𝟙 X : X ⟶ X) := by
      show 𝟙 Y ≫ f = f ≫ 𝟙 X
      simp
    refine h2.trans ?_
    rw [e]
    exact h1

end GlobalTheory.CompanionTheory.EtEdge
