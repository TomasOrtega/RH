import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPinnedOfIsUnf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameProductCharacterInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetReducedBlockEqResidueDet
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterAtDetRootCongOneOddEqOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIntegralUnitRootNormOneAdele
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinitePartPreservesFormDetNormOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenCongruenceIdelesAndRealFiniteParts

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts GlobalTheory.GeoLevel
open GlobalTheory.Member (FinCong IotaOK)
open GlobalTheory.LevelCusp (IsMatch)
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoLevel.LiftChar

variable {D : D7}

/- English proof (translation)
Establish `e1` using `congrArg (fun z => (Matrix.GeneralLinearGroup.det z : Aˣ)) e`. Simplify using `only [map_mul, map_inv, mul_inv_cancel_comm] at e1`. Conclude with `(S.subtype.map_det y.1).trans (congrArg Units.val e1)`.
-/
theorem det_conj {A : Type} [CommRing A] (S : Subring A) {r : ℕ} (β x : GL (Fin r) A) (y : GL (Fin r) S)
    (e : β * Formalism.UG.bc S.subtype y * β⁻¹ = x) : ((y.1.det : S) : A) = x.1.det := by
  have e1 := congrArg (fun z => (Matrix.GeneralLinearGroup.det z : Aˣ)) e
  simp only [map_mul, map_inv, mul_inv_cancel_comm] at e1
  exact (S.subtype.map_det y.1).trans (congrArg Units.val e1)

/- English proof (translation)
The claim follows from `det_conj _ β x.1 _ (Formalism.L2.DIV.frGL_pullFr β x)`.
-/
theorem det_pullGen {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {r : ℕ}
    (β : GL (Fin r) (E ⊗[F] Formalism.L2.Herm.Af F)) (x : Formalism.L2.DIV.St β) :
    (((Formalism.L2.DIV.pullFr β x).1.det : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) = x.1.1.det :=
  det_conj _ β x.1 _ (Formalism.L2.DIV.frGL_pullFr β x)

/- English proof (translation)
Establish `e3 : (finR V hr κ).1.det = (finE V κ).1.det` using `Matrix.det_reindex_self (finCongr hr) (finE V κ).1`. Establish `e4 : (finE V κ).1.det = swapAE D (finHom V κ).1.det` using `((swapAE D).map_det _).symm`. Establish `e5 : (finHom V κ).1.det = finPart D (matHom V κ).1.det` using `((finPart D).map_det _).symm`. Conclude with `e3.trans (e4.trans (congrArg (swapAE D) e5))`.
-/
theorem det_finR (V : HSp D) {r : ℕ} (hr : V.rank = r) (κ : GA D V) :
    (finR V hr κ).1.det =
      swapAE D (finPart D ((matHom V κ).1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).det) := by
  have e3 : (finR V hr κ).1.det = (finE V κ).1.det :=
    Matrix.det_reindex_self (finCongr hr) (finE V κ).1
  have e4 : (finE V κ).1.det = swapAE D (finHom V κ).1.det := ((swapAE D).map_det _).symm
  have e5 : (finHom V κ).1.det = finPart D (matHom V κ).1.det := ((finPart D).map_det _).symm
  exact e3.trans (e4.trans (congrArg (swapAE D) e5))

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `hP : ∀ P : Ideal (𝓞 D.host.E), P.IsMaximal → ∃ t s : 𝓞 D.host.E, (s : D.host.E) = GlobalTheory.Member.cF D (t : D.host.E) ∧ t - s ∉ P`. Introduce `P hP`. Take `⟨θ, t, ht, hθ⟩` from `D.sp.cm.cmUnram.2.2 P hP`. Conclude with `⟨θ, t, ht, hθ⟩`. Establish `hc : GlobalTheory.Member.cF D ≠ 1`.

Introduce `h`. Take `⟨P, hM⟩` from `Ideal.exists_maximal (𝓞 D.host.E)`. Take `⟨t, s, hs, hts⟩` from `hP P hM`. Rewrite `hs` using `[h]`. Establish `: s = t` using `Subtype.ext hs`.

Rewrite `hts` using `[this, sub_self]`. Conclude with `hts P.zero_mem`. Rewrite `hd` using `[GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers]`. Take `⟨y, hy, ⟨y', hy', hyy⟩, hroot⟩` from `GlobalTheory.AdLat.exists_integral_unit_root D.host.F D.host.E (GlobalTheory.Member.cF D) D.sp.cm.deg2 hc hP _ hd (GlobalTheory.Member.finHom_herm_det D V k).2.1`. Rewrite `hy`, `hy'` using `[← GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers]`.

Use `replace hroot : y = (finHom V k).1.det * sigR (Af D.host.F) D.sp.cm.sig y := hroot`. Take `⟨Y, hY1, hY2, hY3⟩` from `GlobalTheory.DetRootCong.exists_idele D y y' hyy`. Use `⟨Y, ?_, ⟨hY1, hY2 ▸ hy, hY3 ▸ hy'⟩⟩` and prove the remaining obligations. Take `⟨e, he, -⟩` from `GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E`. Establish `he1 : ∀ z, (e z).1 = infPart D z` using `fun z => (he z).1`.

Establish `he2 : ∀ z, (e z).2 = finPart D z` using `fun z => (he z).2`. Establish `hdet : (finHom V k).1.det = finPart D (matHom V k).1.det` using `((finPart D).map_det _).symm`. Establish `hdet' : (infHom V k).1.det = infPart D (matHom V k).1.det` using `((infPart D).map_det _).symm`. Establish `h1 : infHom V k = 1` using `hf`. Establish `hs : infPart D (sigR (AF D.host.F) D.sp.cm.sig (Y : AE D)) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D (Y : AE D))` using `GlobalTheory.DetRootCong.map_sigR _ _ _`.

Use `e.injective (Prod.ext ?_ ?_)` and prove the remaining obligations. Rewrite using `[he1, he1, RingHom.map_mul, hs, ← hdet', h1, hY1, RingHom.map_one, mul_one]`. Conclude with `Matrix.det_one.symm`. Establish `hs'` using `GlobalTheory.DetRootCong.finPart_sigR D (Y : AE D)`. Rewrite `hs'` using `[hY2]`.

Rewrite `hroot` using `[hdet, ← hs', ← RingHom.map_mul]`. Conclude with `(he2 _).trans ((hY2.trans hroot).trans (he2 _).symm)`.
-/
theorem exists_finUnit_root (V : HSp D) (k : GA D V) (hf : k ∈ GfC V) (hd : (finHom V k).1.det ∈ intAE D) :
    ∃ x : (AE D)ˣ, IsDetRoot V k x ∧ FinUnit x := by
  have hP : ∀ P : Ideal (𝓞 D.host.E), P.IsMaximal →
      ∃ t s : 𝓞 D.host.E, (s : D.host.E) = GlobalTheory.Member.cF D (t : D.host.E) ∧ t - s ∉ P := by
    intro P hP
    obtain ⟨θ, t, ht, hθ⟩ := D.sp.cm.cmUnram.2.2 P hP
    exact ⟨θ, t, ht, hθ⟩
  have hc : GlobalTheory.Member.cF D ≠ 1 := by
    intro h
    obtain ⟨P, hM⟩ := Ideal.exists_maximal (𝓞 D.host.E)
    obtain ⟨t, s, hs, hts⟩ := hP P hM
    rw [h] at hs
    have : s = t := Subtype.ext hs
    rw [this, sub_self] at hts
    exact hts P.zero_mem
  rw [GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers] at hd
  obtain ⟨y, hy, ⟨y', hy', hyy⟩, hroot⟩ := GlobalTheory.AdLat.exists_integral_unit_root D.host.F D.host.E (GlobalTheory.Member.cF D)
    D.sp.cm.deg2 hc hP _ hd (GlobalTheory.Member.finHom_herm_det D V k).2.1
  rw [← GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers] at hy hy'
  replace hroot : y = (finHom V k).1.det * sigR (Af D.host.F) D.sp.cm.sig y := hroot
  obtain ⟨Y, hY1, hY2, hY3⟩ := GlobalTheory.DetRootCong.exists_idele D y y' hyy
  refine ⟨Y, ?_, ⟨hY1, hY2 ▸ hy, hY3 ▸ hy'⟩⟩
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have he1 : ∀ z, (e z).1 = infPart D z := fun z => (he z).1
  have he2 : ∀ z, (e z).2 = finPart D z := fun z => (he z).2
  have hdet : (finHom V k).1.det = finPart D (matHom V k).1.det := ((finPart D).map_det _).symm
  have hdet' : (infHom V k).1.det = infPart D (matHom V k).1.det := ((infPart D).map_det _).symm
  have h1 : infHom V k = 1 := hf
  have hs : infPart D (sigR (AF D.host.F) D.sp.cm.sig (Y : AE D)) =
      sigR (Ainf D.host.F) D.sp.cm.sig (infPart D (Y : AE D)) := GlobalTheory.DetRootCong.map_sigR _ _ _
  refine e.injective (Prod.ext ?_ ?_)
  · rw [he1, he1, RingHom.map_mul, hs, ← hdet', h1, hY1, RingHom.map_one, mul_one]
    exact Matrix.det_one.symm
  · have hs' := GlobalTheory.DetRootCong.finPart_sigR D (Y : AE D)
    rw [hY2] at hs'
    rw [hdet, ← hs', ← RingHom.map_mul] at hroot
    exact (he2 _).trans ((hY2.trans hroot).trans (he2 _).symm)

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `e1` using `det_pullGen (F := D.host.F) (E := D.host.E) β ⟨finR V hr κ, h⟩`. Establish `e2` using `e1.trans (det_finR V hr κ)`. Establish `e5 : (finHom V κ).1.det = finPart D (matHom V κ).1.det` using `((finPart D).map_det _).symm`. Establish `e3` using `unswap_int (D := D) (Formalism.L2.DIV.pullFr β ⟨finR V hr κ, h⟩).1.det`. Rewrite using `[e5, ← unswap_swap (finPart D (matHom V κ).1.det), ← e2]`.

Conclude with `e3`.
-/
theorem det_int (V : HSp D) {r : ℕ} (hr : V.rank = r) (β : GL (Fin r) (EAf D)) (κ : GA D V)
    (h : finR V hr κ ∈ Formalism.L2.DIV.St β) : (finHom V κ).1.det ∈ intAE D := by
  have e1 := det_pullGen (F := D.host.F) (E := D.host.E) β ⟨finR V hr κ, h⟩
  have e2 := e1.trans (det_finR V hr κ)
  have e5 : (finHom V κ).1.det = finPart D (matHom V κ).1.det := ((finPart D).map_det _).symm
  have e3 := unswap_int (D := D) (Formalism.L2.DIV.pullFr β ⟨finR V hr κ, h⟩).1.det
  rw [e5, ← unswap_swap (finPart D (matHom V κ).1.det), ← e2]
  exact e3

end GlobalTheory.GeoLevel.LiftChar
