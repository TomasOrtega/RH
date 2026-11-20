import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistLocalIdentity
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacesInjective

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.ChartQuot
open GlobalTheory.FinPl GlobalTheory.FinPlLoc ValuativeRel
variable {D : D7}
section Pt
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
end Pt
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha ha' t J hJ j hj β β'`. Establish `hA` using `hJ.is`. Establish `hj0 : j < B.R.m` using `by omega`. Establish `hle : j + 1 ≤ B.R.m` using `hj.le`. Establish `c1 : ChrEq (J.A.chr (j + 1)) (I.C.mu0 ⟨j, hj0⟩ * I.xi (W.P.I.tup t))` using `hA.chr ⟨j, hj0⟩`.

Establish `c2 : ChrEq (J.A.chr (j + 1 + 1)) (I.C.mu0 ⟨j + 1, hj⟩ * I.xi (W.P.I.tup t))` using `hA.chr ⟨j + 1, hj⟩`. Establish `hF : ∀ b, (J.A.chr (j + 1 + 1) * (J.A.chr (j + 1))⁻¹) (idF (I.rec7 l Z) b) = 1` using `quot_triv (D := I.rec7 l Z) c2 c1 (I.C.isMu0 ⟨j + 1, hj⟩).triv (I.C.isMu0 ⟨j, hj0⟩).triv`. Use `show (J.A.chr (j + 1 + 1) * (J.A.chr (j + 1))⁻¹) _ = (J.A.chr (j + 1 + 1) * (J.A.chr (j + 1))⁻¹) _`. Establish `key : ∀ γ, ∃ k₀ : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X (j + 1)), k₀ ∈ GfC _ ∧ finM _ (rankN (I.rec7 l Z) (j + 1) hle) k₀ = (TC.kStd X u (B.R.N (j + 1))).1 ∧ ∀ x, IsDetRoot _ k₀ x → (J.A.chr (j + 1 + 1) * (J.A.chr (j + 1))⁻¹) (J.A.xr (j + 1) γ) = (J.A.chr (j + 1 + 1) * (J.A.chr (j + …`. Introduce `γ`.

Take `⟨hG, hM, hR⟩` from `hA.kA (j + 1) hle γ`. Break down `Nat.lt_or_ge (j + 1 + 1) B.R.m with h | h` into its components or cases. Use `⟨_, hG, ?_, fun x hx => chr_eq_of_root hF hR hx⟩` and prove the remaining obligations. Rewrite using `[hM, hJ.std (j + 1) h γ]`. Establish `hm : j + 1 + 1 = B.R.m` using `by omega`.

Take `⟨k₀, h₀, hG₀, hM₀, hk, hsupp, hloc⟩` from `hJ.pen (j + 1) hm γ`. Use `⟨k₀, hG₀, hM₀, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hs : ∀ i, (J.G i).s = j` using `fun i => by`. Establish `: (J.G i).s + 1 + 1 = B.R.m` using `(J.G i).hs`. Use linear arithmetic over natural numbers and integers.

Establish `hd : ∀ i, ∃ d : (J.G i).kˣ, valuation (J.G i).k (d : (J.G i).k) = 1 ∧ (J.G i).q.pr (Formalism.L2.Theta.mt _ h₀).det = d` using `fun i => by`. Establish `e : (J.G i).s + 1 = j + 1` using `by rw [hs i]`. Take `⟨g, hg, hmat⟩` from `hloc i e`. Take `⟨d, hd1, hd2⟩` from `exists_unit_det ((J.G i).FX ((J.G i).s + 1) le_rfl) g ((J.E i).le _ _ _ hg)`. Use `⟨d, hd1, ?_⟩` and prove the remaining obligations.

Rewrite using `[← det_cast _ _ e h₀, RingHom.map_det]`. Conclude with `(congrArg Matrix.det hmat).trans hd2`. Use `choose d hd1 hd2 using hd`. Establish `hroot` using `isDetRoot_prod (fun i => (J.G i).q) (_root_.GlobalTheory.TopVol.TwistPlaces.places_injective_alt W hW u a ha ha' t J hJ) hsupp d hd2`. Rewrite `hR` using `[hk]`.

Use `chr_eq_of_root_mul hF hx hroot ?_ hR` and prove the remaining obligations. Rewrite using `[map_prod]`. Use `Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations. Rewrite using `[MonoidHom.mul_apply, MonoidHom.inv_apply, hJ.chr (j + 1) hj, hJ.chr j hj0, eq_on_unit (J.G i).q ((J.E i).mu (j + 1) (by rw [hs i])).1 ((J.E i).mu j (by rw [hs i]; omega)).1 ((J.E i).unr _) ((J.E i).unr _) (d i) (hd1 i), mul_inv_cancel]`. Take `⟨k₁, g1, m1, h1⟩` from `key β`.

Take `⟨k₂, g2, m2, h2⟩` from `key β'`. Take `rfl : k₁ = k₂` from `eq_of_finM _ g1 g2 (m1.trans m2.symm)`. Take `⟨x, hx⟩` from `(GlobalTheory.Member.isDetRoot_laws _ _).1 k₁`. Rewrite using `[h1 x hx, h2 x hx]`.
-/
theorem chr_quot_chart_free_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ j, j + 1 < B.R.m → ∀ β β' : J.Ch₀ (j + 1), J.A.chr (j + 1 + 1) (J.A.xr (j + 1) β) * (J.A.chr (j + 1) (J.A.xr (j + 1) β))⁻¹ = J.A.chr (j + 1 + 1) (J.A.xr (j + 1) β') * (J.A.chr (j + 1) (J.A.xr (j + 1) β'))⁻¹ := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha ha' t J hJ j hj β β'
  have hA := hJ.is
  have hj0 : j < B.R.m := by omega
  have hle : j + 1 ≤ B.R.m := hj.le
  have c1 : ChrEq (J.A.chr (j + 1)) (I.C.mu0 ⟨j, hj0⟩ * I.xi (W.P.I.tup t)) := hA.chr ⟨j, hj0⟩
  have c2 : ChrEq (J.A.chr (j + 1 + 1)) (I.C.mu0 ⟨j + 1, hj⟩ * I.xi (W.P.I.tup t)) := hA.chr ⟨j + 1, hj⟩
  have hF : ∀ b, (J.A.chr (j + 1 + 1) * (J.A.chr (j + 1))⁻¹) (idF (I.rec7 l Z) b) = 1 :=
    quot_triv (D := I.rec7 l Z) c2 c1 (I.C.isMu0 ⟨j + 1, hj⟩).triv (I.C.isMu0 ⟨j, hj0⟩).triv
  show (J.A.chr (j + 1 + 1) * (J.A.chr (j + 1))⁻¹) _ = (J.A.chr (j + 1 + 1) * (J.A.chr (j + 1))⁻¹) _
  have key : ∀ γ, ∃ k₀ : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X (j + 1)), k₀ ∈ GfC _ ∧
      finM _ (rankN (I.rec7 l Z) (j + 1) hle) k₀ = (TC.kStd X u (B.R.N (j + 1))).1 ∧
      ∀ x, IsDetRoot _ k₀ x → (J.A.chr (j + 1 + 1) * (J.A.chr (j + 1))⁻¹) (J.A.xr (j + 1) γ) =
        (J.A.chr (j + 1 + 1) * (J.A.chr (j + 1))⁻¹) x := by
    intro γ
    obtain ⟨hG, hM, hR⟩ := hA.kA (j + 1) hle γ
    rcases Nat.lt_or_ge (j + 1 + 1) B.R.m with h | h
    · refine ⟨_, hG, ?_, fun x hx => chr_eq_of_root hF hR hx⟩
      rw [hM, hJ.std (j + 1) h γ]
    · have hm : j + 1 + 1 = B.R.m := by omega
      obtain ⟨k₀, h₀, hG₀, hM₀, hk, hsupp, hloc⟩ := hJ.pen (j + 1) hm γ
      refine ⟨k₀, hG₀, hM₀, fun x hx => ?_⟩
      have hs : ∀ i, (J.G i).s = j := fun i => by
        have : (J.G i).s + 1 + 1 = B.R.m := (J.G i).hs
        omega
      have hd : ∀ i, ∃ d : (J.G i).kˣ, valuation (J.G i).k (d : (J.G i).k) = 1 ∧
          (J.G i).q.pr (Formalism.L2.Theta.mt _ h₀).det = d := fun i => by
        have e : (J.G i).s + 1 = j + 1 := by rw [hs i]
        obtain ⟨g, hg, hmat⟩ := hloc i e
        obtain ⟨d, hd1, hd2⟩ := exists_unit_det ((J.G i).FX ((J.G i).s + 1) le_rfl) g ((J.E i).le _ _ _ hg)
        refine ⟨d, hd1, ?_⟩
        rw [← det_cast _ _ e h₀, RingHom.map_det]
        exact (congrArg Matrix.det hmat).trans hd2
      choose d hd1 hd2 using hd
      have hroot := isDetRoot_prod (fun i => (J.G i).q)
        (_root_.GlobalTheory.TopVol.TwistPlaces.places_injective_alt W hW u a ha ha' t J hJ) hsupp d hd2
      rw [hk] at hR
      refine chr_eq_of_root_mul hF hx hroot ?_ hR
      rw [map_prod]
      refine Finset.prod_eq_one fun i _ => ?_
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hJ.chr (j + 1) hj, hJ.chr j hj0,
        eq_on_unit (J.G i).q ((J.E i).mu (j + 1) (by rw [hs i])).1 ((J.E i).mu j (by rw [hs i]; omega)).1
          ((J.E i).unr _) ((J.E i).unr _) (d i) (hd1 i), mul_inv_cancel]
  obtain ⟨k₁, g1, m1, h1⟩ := key β
  obtain ⟨k₂, g2, m2, h2⟩ := key β'
  obtain rfl : k₁ = k₂ := eq_of_finM _ g1 g2 (m1.trans m2.symm)
  obtain ⟨x, hx⟩ := (GlobalTheory.Member.isDetRoot_laws _ _).1 k₁
  rw [h1 x hx, h2 x hx]
end GlobalTheory.ChartQuot
end
