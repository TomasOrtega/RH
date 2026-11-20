import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightedProjectiveEmbeddingSep
open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory

namespace GlobalTheory.FlagPlucker

/- English proof (translation)
Take `⟨Q, Ψ, r, P, hP, hr, hΨ, hc, hinj⟩` from `GlobalTheory.AmpleSeparateOverRing.exists_ample_model R X f ι L hL M t ht w hw Finset.univ`. Establish `: LocallyOfFiniteType (Ψ ≫ r)` using `by rw [hΨ]; infer_instance`. Establish `: LocallyOfFiniteType Ψ` using `locallyOfFiniteType_of_comp Ψ r`. Establish `: IsProper (Ψ ≫ r)` using `by rw [hΨ]; infer_instance`. Establish `: IsProper Ψ` using `IsProper.of_comp Ψ r`.

Establish `: LocallyQuasiFinite Ψ` using `GlobalTheory.locallyQuasiFinite_of_finite_geometric_points Ψ fun K _ _ y => by`. Distinguish the cases in `hy : ∃ a : Spec (.of K) ⟶ X, a ≫ Ψ = y`. Take `⟨a, rfl⟩` from `hy`. Establish `hs : {a' : Spec (.of K) ⟶ X | a' ≫ Ψ = a ≫ Ψ}.Finite` using `(hfin K a).subset fun a' ha' => by`. Take `⟨e1, e2⟩` from `hinj K a' a ha'`.

Conclude with `⟨e1, fun i => e2 i (Finset.mem_univ i)⟩`. Conclude with `hs.to_subtype`. Use `haveI : IsEmpty {x : Spec (.of K) ⟶ X // x ≫ Ψ = y} := ⟨fun x => hy ⟨x.1, x.2⟩⟩ infer_instance`. Use `IsFinite.of_isProper_of_locallyQuasiFinite Ψ` as an intermediate fact. Establish `hcls' : CechPic.cls (P.pull Ψ) (LB.isLB_pull hP.isLB Ψ) = CechPic.cls N hN`.

Rewrite using `[hc, hcls]`. Conclude with `Finset.sum_congr rfl fun i _ => natCast_zsmul _ _`. Conclude with `(isAmpleLB_congr (LB.isLB_pull hP.isLB Ψ) hN ((CechPic.cls_eq_iff _ _).1 hcls')).1 (hP.pull_of_isAffineHom Ψ)`.
-/
theorem isAmpleLB_of_finite_fibres (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (hf : IsProper f)
    (ι : Type) [Fintype ι] (L : ι → LB X) (hL : ∀ i, (L i).IsLB) (M : ι → ℕ)
    (t : ∀ i, Fin (M i + 1) → (L i).Sec) (ht : ∀ i, ⨆ m, nonzeroLocus (t i m) = ⊤)
    (hfin : ∀ (K : Type) [Field K] [IsAlgClosed K] (a : Sp K ⟶ X),
      {a' : Sp K ⟶ X | a' ≫ f = a ≫ f ∧
        ∀ i, a' ≫ GlobalTheory.ProjSpace.toProj f (t i) (ht i) = a ≫ GlobalTheory.ProjSpace.toProj f (t i) (ht i)}.Finite)
    (w : ι → ℕ) (hw : ∀ i, 1 ≤ w i) (N : LB X) (hN : N.IsLB)
    (hcls : GlobalTheory.CechPic.cls N hN = ∑ i, w i • GlobalTheory.CechPic.cls (L i) (hL i)) : GlobalTheory.IsAmpleLB N := by
  obtain ⟨Q, Ψ, r, P, hP, hr, hΨ, hc, hinj⟩ :=
    GlobalTheory.AmpleSeparateOverRing.exists_ample_model R X f ι L hL M t ht w hw Finset.univ
  have : LocallyOfFiniteType (Ψ ≫ r) := by rw [hΨ]; infer_instance
  have : LocallyOfFiniteType Ψ := locallyOfFiniteType_of_comp Ψ r
  have : IsProper (Ψ ≫ r) := by rw [hΨ]; infer_instance
  have : IsProper Ψ := IsProper.of_comp Ψ r
  have : LocallyQuasiFinite Ψ := GlobalTheory.locallyQuasiFinite_of_finite_geometric_points Ψ fun K _ _ y => by
    by_cases hy : ∃ a : Spec (.of K) ⟶ X, a ≫ Ψ = y
    · obtain ⟨a, rfl⟩ := hy
      have hs : {a' : Spec (.of K) ⟶ X | a' ≫ Ψ = a ≫ Ψ}.Finite := (hfin K a).subset fun a' ha' => by
        obtain ⟨e1, e2⟩ := hinj K a' a ha'
        exact ⟨e1, fun i => e2 i (Finset.mem_univ i)⟩
      exact hs.to_subtype
    · haveI : IsEmpty {x : Spec (.of K) ⟶ X // x ≫ Ψ = y} := ⟨fun x => hy ⟨x.1, x.2⟩⟩
      infer_instance
  have := IsFinite.of_isProper_of_locallyQuasiFinite Ψ
  have hcls' : CechPic.cls (P.pull Ψ) (LB.isLB_pull hP.isLB Ψ) = CechPic.cls N hN := by
    rw [hc, hcls]
    exact Finset.sum_congr rfl fun i _ => natCast_zsmul _ _
  exact (isAmpleLB_congr (LB.isLB_pull hP.isLB Ψ) hN
    ((CechPic.cls_eq_iff _ _).1 hcls')).1 (hP.pull_of_isAffineHom Ψ)

end GlobalTheory.FlagPlucker

noncomputable section

namespace GlobalTheory.FlagPlucker

open GlobalTheory.FlagMod Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {Z : Scheme.{0}} {π : Z ⟶ Y.X}

open Classical in

def ind (σ : E →+* ℂ) (m : ℕ) : Ix Dw → ℤ :=
  fun ix => ix.elim 0 fun p => if p.1 = σ ∧ (p.2 : ℕ) ≤ m then 1 else 0

def plkU (F : Frames Y π) (Mc : MChart Y) (k : F.J) (σ : E →+* ℂ) :
    Matrix (Fin Mc.n) (Fin (Dw.mult σ)) Γ(Z, F.U k ⊓ π ⁻¹ᵁ Mc.U) :=
  (chg Mc (F.M k).toMChart).map (π.appLE (Mc.U ⊓ (F.M k).U) (F.U k ⊓ π ⁻¹ᵁ Mc.U)
      (fun _ hp => ⟨hp.2, F.le k hp.1⟩)).hom *
    (F.u k σ).map (resG Z (inf_le_left : F.U k ⊓ π ⁻¹ᵁ Mc.U ≤ F.U k))

def plkMinor (F : Frames Y π) (Mc : MChart Y) (k : F.J) (σ : E →+* ℂ) (m : Fin (Dw.mult σ))
    (r : Fin ((m : ℕ) + 1) → Fin Mc.n) : Γ(Z, F.U k ⊓ π ⁻¹ᵁ Mc.U) :=
  ((plkU F Mc k σ).submatrix r (Fin.castLE m.2)).det

abbrev plkNum (Mc : MChart Y) (m : ℕ) : ℕ := Fintype.card (Fin (m + 1) → Fin Mc.n)

def plkIdx (Mc : MChart Y) (m : ℕ) : Fin (plkNum Mc m + 1) → Option (Fin (m + 1) → Fin Mc.n) :=
  Fin.cases none fun i => some ((Fintype.equivFin _).symm i)

/- English proof (translation)
Introduce `_ hp` and use `⟨LB.wchart_le _ _ j PUnit.unit hp, hg trivial⟩`.
-/
theorem plk_le (F : Frames Y π) (Mc : MChart Y) {T : Scheme.{0}} (g : T ⟶ Z) (hg : ⊤ ≤ (g ≫ π) ⁻¹ᵁ Mc.U)
    (e : Ix Dw → ℤ) (j : ((F.LL e).pull g).ι) :
    ((F.LL e).pull g).U j ≤ g ⁻¹ᵁ (F.U (j PUnit.unit) ⊓ π ⁻¹ᵁ Mc.U) :=
  fun _ hp => ⟨LB.wchart_le _ _ j PUnit.unit hp, hg trivial⟩

def plkLoc (F : Frames Y π) (Mc : MChart Y) {T : Scheme.{0}} (g : T ⟶ Z) (hg : ⊤ ≤ (g ≫ π) ⁻¹ᵁ Mc.U)
    (σ : E →+* ℂ) (m : Fin (Dw.mult σ)) (q : Fin (plkNum Mc m + 1)) (j : ((F.LL (ind σ m)).pull g).ι) :
    Γ(T, ((F.LL (ind σ m)).pull g).U j) :=
  match plkIdx Mc m q with
  | none => 0
  | some r => (g.appLE _ _ (plk_le F Mc g hg (ind σ m) j)).hom (plkMinor F Mc (j PUnit.unit) σ m r)

end GlobalTheory.FlagPlucker

end
