import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection

set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PAlgNat

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `h` using `A.aTo1_coeff (WittVector.teichmuller l a)`. Rewrite `h` using `[WittVector.teichmuller_coeff_zero]`. Establish `h'` using `B.aTo1_coeff (WittVector.teichmuller l (Hom.f f a))`. Rewrite `h'` using `[WittVector.teichmuller_coeff_zero]`. Rewrite using `[h, h', mapAcr_toAcr, mapW, WittVector.map_teichmuller]`.
-/
theorem mapAcris_acrisOfTilt {A B : PAlg l} (f : A ⟶ B) (a : A.A) :
    mapAcr f 1 (A.aTo1 a) = B.aTo1 (Hom.f f a) := by
  have h := A.aTo1_coeff (WittVector.teichmuller l a)
  rw [WittVector.teichmuller_coeff_zero] at h
  have h' := B.aTo1_coeff (WittVector.teichmuller l (Hom.f f a))
  rw [WittVector.teichmuller_coeff_zero] at h'
  rw [h, h', mapAcr_toAcr, mapW, WittVector.map_teichmuller]

/- English proof (translation)
Rewrite using `[expand, expand, map_finsuppSum, Finsupp.sum_mapRange_index (fun k => by simp)]`. Use `Finsupp.sum_congr fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, mapAcris_acrisOfTilt, mapAcr_dxi]`.
-/
theorem mapAcr_expand {A B : PAlg l} (f : A ⟶ B) (c : ℕ →₀ A.A) :
    mapAcr f 1 (A.expand c) = B.expand (c.mapRange (Hom.f f) (map_zero _)) := by
  rw [expand, expand, map_finsuppSum, Finsupp.sum_mapRange_index (fun k => by simp)]
  refine Finsupp.sum_congr fun k _ => ?_
  rw [map_mul, mapAcris_acrisOfTilt, mapAcr_dxi]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `mapU f (A.th (WittVector.teichmuller l a)) = B.th (WittVector.teichmuller l (Hom.f f a))`. Rewrite using `[mapU_th, mapW, WittVector.map_teichmuller]`.
-/
theorem mapU_sharp {A B : PAlg l} (f : A ⟶ B) (a : A.A) :
    mapU f (A.sharp a) = B.sharp (Hom.f f a) := by
  change mapU f (A.th (WittVector.teichmuller l a)) = B.th (WittVector.teichmuller l (Hom.f f a))
  rw [mapU_th, mapW, WittVector.map_teichmuller]

/- English proof (translation)
Rewrite using `[sharpMap_eq, sharpMap_eq, ← mapU_sharp]`. Both sides reduce to the same expression.
-/
theorem mapUnits_unitsOfTilt {A B : PAlg l} (f : A ⟶ B) (a : A.A) :
    mapUn f 1 (A.aToU1 a) = B.aToU1 (Hom.f f a) := by
  rw [sharpMap_eq, sharpMap_eq, ← mapU_sharp]
  rfl

/- English proof (translation)
Rewrite using `[mapAcr_toAcr, mapU_th, uToQ_th]`.
-/
theorem mk_mapAcr_toAcr {A B : PAlg l} (f : A ⟶ B) (n : ℕ) (x : A.W) :
    Ideal.Quotient.mk (B.Fil n 1) (mapAcr f n (A.toAcr n x)) = B.uToQ n (mapU f (A.th x)) := by
  rw [mapAcr_toAcr, mapU_th, uToQ_th]

/- English proof (translation)
Establish `h` using `A.aTo1_coeff (A.sW x)`. Establish `e : (A.sW x).coeff 0 = A.s (x.coeff 0)` using `WittVector.map_coeff _ _ _`. Rewrite `h` using `[e]`. Rewrite using `[h]`. Both sides reduce to the same expression.
-/
theorem algebraMap_eq_acrisOfTilt (A : PAlg l) (x : Ainf l) :
    algebraMap (Ainf l) (A.Acr 1) x = A.aTo1 (A.s (x.coeff 0)) := by
  have h := A.aTo1_coeff (A.sW x)
  have e : (A.sW x).coeff 0 = A.s (x.coeff 0) := WittVector.map_coeff _ _ _
  rw [e] at h
  rw [h]
  rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨mapAcris_acrisOfTilt f, mapAcr_expand f, mapU_sharp f, mapUnits_unitsOfTilt f, mk_mapAcr_toAcr f, algebraMap_eq_acrisOfTilt A⟩`.
-/
theorem expand_nat {l : ℕ} [Fact l.Prime] (A : PAlg l) (B : PAlg l) (f : A ⟶ B) :
    (∀ a, mapAcr f 1 (A.aTo1 a) = B.aTo1 (Hom.f f a)) ∧
    (∀ c : ℕ →₀ A.A, mapAcr f 1 (A.expand c) = B.expand (c.mapRange (Hom.f f) (map_zero _))) ∧
    (∀ a, mapU f (A.sharp a) = B.sharp (Hom.f f a)) ∧
    (∀ a, mapUn f 1 (A.aToU1 a) = B.aToU1 (Hom.f f a)) ∧
    (∀ n x, Ideal.Quotient.mk (B.Fil n 1) (mapAcr f n (A.toAcr n x)) = B.uToQ n (mapU f (A.th x))) ∧
    ∀ x : Ainf l, algebraMap (Ainf l) (A.Acr 1) x = A.aTo1 (A.s (x.coeff 0)) :=
  ⟨mapAcris_acrisOfTilt f, mapAcr_expand f, mapU_sharp f, mapUnits_unitsOfTilt f, mk_mapAcr_toAcr f, algebraMap_eq_acrisOfTilt A⟩

end GlobalTheory.CompanionTheory.PAlgNat
