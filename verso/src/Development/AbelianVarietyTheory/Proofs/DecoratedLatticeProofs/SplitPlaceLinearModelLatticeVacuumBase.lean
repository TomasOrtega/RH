import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceSectionAddComplementMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFramePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLinearLawHalfVacuumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunSplitPlaceSchroedingerModelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatHalfSplitDatumCompletedLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilHomActionFixOfTrivialAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalCharacterIsUnramifiedOfHeckeUnramStatement

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitLinAt
open GlobalTheory.SplitLinear

variable {D : D7}

/- English proof (translation)
Introduce `D k _ _ _ _ p S T LS LT u hu hh`. Take `⟨ε, hε, hsum⟩` from `p.above`. Establish `he` using `p.split`. Establish `hc : p.e * cA D p.e = 0` using `he.2.1`. Establish `hec` using `GlobalTheory.SplitScalar.isSplitIdem_conj he`.

Break down `hh with h1 | h1` into its components or cases. Establish `k1 : algebraMap (AF D.host.F) (AE D) ε * p.e = p.e`. Rewrite using `[← hsum]`. Take the linear combination `he.1 + hc`. Use `GlobalTheory.PlaceModel.idem_smul_mem hε he.1 k1 hu` as an intermediate fact.

Rewrite `this` using `[(GlobalTheory.PlaceModel.mem_half S T).1 ((GlobalTheory.PlaceModel.isHalf_iff S T).1 h1)]`. Conclude with `(AddSubgroup.mem_inf.1 this).1`. Establish `k1 : algebraMap (AF D.host.F) (AE D) ε * cA D p.e = cA D p.e`. Rewrite using `[← hsum]`. Take the linear combination `hc + hec.1`.

Use `GlobalTheory.PlaceModel.idem_smul_mem hε hec.1 k1 hu` as an intermediate fact. Rewrite `this` using `[(GlobalTheory.PlaceModel.mem_half S T).1 ((GlobalTheory.PlaceModel.isHalf_iff S T).1 h1)]`. Conclude with `(AddSubgroup.mem_inf.1 this).1`.
-/
theorem latHalf : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S T : HSp D) (LS : Lat S) (LT : Lat T) (u : WO S T),
    u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (fun _ => True) →
    (IsHalf p.e u ∨ IsHalf (cA D p.e) u) →
    u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v) := by
  intro D k _ _ _ _ p S T LS LT u hu hh
  obtain ⟨ε, hε, hsum⟩ := p.above
  have he := p.split
  have hc : p.e * cA D p.e = 0 := he.2.1
  have hec := GlobalTheory.SplitScalar.isSplitIdem_conj he
  rcases hh with h1 | h1
  · have k1 : algebraMap (AF D.host.F) (AE D) ε * p.e = p.e := by
      rw [← hsum]; linear_combination he.1 + hc
    have := GlobalTheory.PlaceModel.idem_smul_mem hε he.1 k1 hu
    rw [(GlobalTheory.PlaceModel.mem_half S T).1 ((GlobalTheory.PlaceModel.isHalf_iff S T).1 h1)] at this
    exact (AddSubgroup.mem_inf.1 this).1
  · have k1 : algebraMap (AF D.host.F) (AE D) ε * cA D p.e = cA D p.e := by
      rw [← hsum]; linear_combination hc + hec.1
    have := GlobalTheory.PlaceModel.idem_smul_mem hε hec.1 k1 hu
    rw [(GlobalTheory.PlaceModel.mem_half S T).1 ((GlobalTheory.PlaceModel.isHalf_iff S T).1 h1)] at this
    exact (AddSubgroup.mem_inf.1 this).1

/- English proof (translation)
The claim follows from `GlobalTheory.T.splitPlace_linearLaw_halfVacuum`.
-/
theorem lawAt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (ΛS : Lat S)
    (ΛT : Lat T) (e : AE D) (f₀ : WO S T → ℂ)
    (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)),
    IsWeilDatumO ψ S T χS χT om → IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsSplitIdem D e → IsThetaFunO ψ S T f₀ →
    (∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      IsHalf e u ∨ IsHalf (cA D e) u → heisO ψ S T u f₀ = f₀) →
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) e
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Tm →
    ∀ (g : GA D S) (h : GA D T), SuppAt e S g → SuppAt e T h → ∀ x y : (AE D)ˣ, IsDetAt e S g x → IsDetAt e T h y →
    ∀ Φ : WO S T → ℂ, IsSBHalf e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      fun _ => True) Φ →
      om (g, h) (Tm Φ) = GlobalTheory.SplitLinear.fac S T χS χT x y • Tm fun t => Φ (actO S T g⁻¹ h⁻¹ t) :=
  GlobalTheory.T.splitPlace_linearLaw_halfVacuum

/- English proof (translation)
The claim follows from `GlobalTheory.T.isThetaFun_splitPlaceSchroedingerModel`.
-/
theorem thetaModel : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)
    (ΛS : Lat S) (ΛT : Lat T)
    (e : AE D) (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)),
    IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsSplitIdem D e → IsThetaFunO ψ S T f₀ →
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) e
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Tm →
    ∀ Φ : WO S T → ℂ, IsSBHalf e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      fun _ => True) Φ → IsThetaFunO ψ S T (Tm Φ) :=
  GlobalTheory.T.isThetaFun_splitPlaceSchroedingerModel

/- English proof (translation)
The claim follows from `GlobalTheory.T.isSchwartzBruhatHalf_split_datum_completed_lattice`.
-/
theorem sbHalf : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S T : HSp D) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT →
    ∀ Ψ ∈ SB (Matrix n n' k),
      IsSBHalf p.e (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v))
        (extFun α β Ψ) :=
  GlobalTheory.T.isSchwartzBruhatHalf_split_datum_completed_lattice

/- English proof (translation)
The claim follows from `GlobalTheory.T.weilHomAction_fix_of_trivialAtSplitPlace`.
-/
theorem offAct : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S T : HSp D) (LS : Lat S) (LT : Lat T) (g : GA D S) (h : GA D T),
    g ∈ grpOff S (· = p.v) → h ∈ grpOff T (· = p.v) → ∀ u : WO S T,
    (u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v) ∨ IsHalf p.e u ∨
      IsHalf (cA D p.e) u) → actO S T g h u = u :=
  GlobalTheory.T.weilHomAction_fix_of_trivialAtSplitPlace

/- English proof (translation)
The claim follows from `GlobalTheory.T.splitPlaceLocalCharacter_isUnramified_of_heckeUnramified`.
-/
theorem lamUnram : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (χ : (AE D)ˣ →* Circle) (r : ℝ), GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χ p.v → IsUnram (lam p χ r) :=
  GlobalTheory.T.splitPlaceLocalCharacter_isUnramified_of_heckeUnramified

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.SplitHecke GlobalTheory.ThetaMove in

/- English proof (translation)
Introduce `D k _ _ _ _ p S T n n' _ _ _ _ α β Ψ g h t`. Unfold `extFun`. Distinguish the cases in `ht : IsHalf p.e t`. Rewrite using `[if_pos (isHalf_actO _ _ ht), if_pos ht]`. Use `congr 1`.

Rewrite using `[← GlobalTheory.SplitLinear.subst_eq]`. Unfold `rd GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.subst`. Rewrite using `[← map_inv, Matrix.map_mul, Matrix.map_mul, β.gl_mat, α.gl_mat]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[α.b'b, Matrix.mul_one, ← Matrix.mul_assoc β.b' β.b, β.b'b, Matrix.one_mul]`.

Rewrite using `[if_neg (fun h' => ht (isHalf_of_act _ _ h')), if_neg ht]`.
-/
theorem extFunAct : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S T : HSp D) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    (α : Frame p S n') (β : Frame p T n) (Ψ : Matrix n n' k → ℂ) (g : GL n' k) (h : GL n k) (t : WO S T),
    extFun α β Ψ (actO S T (α.gl g)⁻¹ (β.gl h)⁻¹ t) = extFun α β (fun x => Ψ ((h⁻¹ : GL n k).val * x * g.val)) t := by
  intro D k _ _ _ _ p S T n n' _ _ _ _ α β Ψ g h t
  unfold extFun
  by_cases ht : IsHalf p.e t
  · rw [if_pos (isHalf_actO _ _ ht), if_pos ht]
    congr 1
    rw [← GlobalTheory.SplitLinear.subst_eq]
    unfold rd GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.subst
    rw [← map_inv, Matrix.map_mul, Matrix.map_mul, β.gl_mat, α.gl_mat]
    simp only [Matrix.mul_assoc]
    rw [α.b'b, Matrix.mul_one, ← Matrix.mul_assoc β.b' β.b, β.b'b, Matrix.one_mul]
  · rw [if_neg (fun h' => ht (isHalf_of_act _ _ h')), if_neg ht]

/- English proof (translation)
Take `⟨h1, h2⟩` from `hΨ`. Set `φ : Matrix n n' k ≃ₜ Matrix n n' k` to `{ toFun := fun x => (h⁻¹ : GL n k).val * x * g.val invFun := fun x => h.val * x * (g⁻¹ : GL n' k).val left_inv := fun x => by show h.val * ((h⁻¹ : GL n k).val * x * g.val) * (g⁻¹ : GL n' k).val = x`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]`. Use `right_inv := fun x => by show (h⁻¹ : GL n k).val * (h.val * x * (g⁻¹ : GL n' k).val) * g.val = x`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]`.

Use `continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const`. Use `continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const }`. Establish `: (fun x => c * Ψ ((h⁻¹ : GL n k).val * x * g.val)) = c • (Ψ ∘ φ)` using `rfl`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ c ⟨h1.comp_continuous φ.continuous, h2.comp_homeomorph φ⟩`.
-/
theorem sbSubst {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {Ψ : Matrix n n' k → ℂ}
    (hΨ : Ψ ∈ SB (Matrix n n' k)) (g : GL n' k) (h : GL n k) (c : ℂ) :
    (fun x => c * Ψ ((h⁻¹ : GL n k).val * x * g.val)) ∈ SB (Matrix n n' k) := by
  obtain ⟨h1, h2⟩ := hΨ
  let φ : Matrix n n' k ≃ₜ Matrix n n' k :=
    { toFun := fun x => (h⁻¹ : GL n k).val * x * g.val
      invFun := fun x => h.val * x * (g⁻¹ : GL n' k).val
      left_inv := fun x => by
        show h.val * ((h⁻¹ : GL n k).val * x * g.val) * (g⁻¹ : GL n' k).val = x
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv,
          Matrix.mul_one]
      right_inv := fun x => by
        show (h⁻¹ : GL n k).val * (h.val * x * (g⁻¹ : GL n' k).val) * g.val = x
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul,
          Matrix.mul_one]
      continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
      continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const }
  have : (fun x => c * Ψ ((h⁻¹ : GL n k).val * x * g.val)) = c • (Ψ ∘ φ) := rfl
  rw [this]
  exact Submodule.smul_mem _ c ⟨h1.comp_continuous φ.continuous, h2.comp_homeomorph φ⟩

end GlobalTheory.SplitLinAt
end

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitLinAt
open GlobalTheory.SplitLinear

variable {D : D7} {S T : HSp D}

/- English proof (translation)
The claim follows from `AddSubgroup.closure_mono fun _ ⟨α, hα, _, r⟩ => ⟨α, hα, fun _ h => (h trivial).elim, r⟩`.
-/
theorem latO_le (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F) → Prop) :
    latO S T LS LT P ≤ latO S T LS LT fun _ => True :=
  AddSubgroup.closure_mono fun _ ⟨α, hα, _, r⟩ => ⟨α, hα, fun _ h => (h trivial).elim, r⟩

/- English proof (translation)
Introduce `i j` and use `by rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, ht i j]`.
-/
theorem isHalf_nsmul {e : AE D} {t : WO S T} (ht : IsHalf e t) (m : ℕ) : IsHalf e (m • t) := fun i j => by
  rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, ht i j]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a1, m, hm, a2, a3⟩`. Conclude with `⟨a1, m, hm, fun u hu hh => a2 u (h1 u hu hh) hh, fun t ht => h2 (a3 t ht)⟩`. Introduce and unpack `⟨a1, m, hm, a2, a3⟩`. Conclude with `⟨a1, m, hm, fun u hu hh => a2 u (h2 hu) hh, fun t ht => h1 _ (a3 t ht) (isHalf_nsmul (a1 t ht) m)⟩`.
-/
theorem sbHalf_congr {e : AE D} {Λ Λ' : AddSubgroup (WO S T)} (h1 : ∀ u ∈ Λ', IsHalf e u → u ∈ Λ) (h2 : Λ ≤ Λ')
    {Φ : WO S T → ℂ} : IsSBHalf e Λ Φ ↔ IsSBHalf e Λ' Φ := by
  constructor
  · rintro ⟨a1, m, hm, a2, a3⟩
    exact ⟨a1, m, hm, fun u hu hh => a2 u (h1 u hu hh) hh, fun t ht => h2 (a3 t ht)⟩
  · rintro ⟨a1, m, hm, a2, a3⟩
    exact ⟨a1, m, hm, fun u hu hh => a2 u (h2 hu) hh, fun t ht => h1 _ (a3 t ht) (isHalf_nsmul (a1 t ht) m)⟩

/- English proof (translation)
Use function extensionality and compare the values at `t`. Unfold `halfInd`. Establish `: (t ∈ Λ ∧ IsHalf e t) ↔ (t ∈ Λ' ∧ IsHalf e t)` using `⟨fun h => ⟨h2 h.1, h.2⟩, fun h => ⟨h1 t h.1 h.2, h.2⟩⟩`. Use `split_ifs with ha hb hb`. Both sides reduce to the same expression.

Conclude with `absurd (this.1 ha) hb`. Conclude with `absurd (this.2 hb) ha`. Both sides reduce to the same expression.
-/
theorem halfInd_congr {e : AE D} {Λ Λ' : AddSubgroup (WO S T)} (h1 : ∀ u ∈ Λ', IsHalf e u → u ∈ Λ) (h2 : Λ ≤ Λ') :
    halfInd e Λ = halfInd e Λ' := by
  funext t
  unfold halfInd
  have : (t ∈ Λ ∧ IsHalf e t) ↔ (t ∈ Λ' ∧ IsHalf e t) := ⟨fun h => ⟨h2 h.1, h.2⟩, fun h => ⟨h1 t h.1 h.2, h.2⟩⟩
  split_ifs with ha hb hb
  · rfl
  · exact absurd (this.1 ha) hb
  · exact absurd (this.2 hb) ha
  · rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `H`. Conclude with `⟨fun Φ hΦ => H.trans Φ ((sbHalf_congr h1 h2).2 hΦ), fun Φ hΦ => H.modul Φ ((sbHalf_congr h1 h2).2 hΦ), by rw [← halfInd_congr h1 h2]; exact H.vac⟩`. Introduce `H`. Conclude with `⟨fun Φ hΦ => H.trans Φ ((sbHalf_congr h1 h2).1 hΦ), fun Φ hΦ => H.modul Φ ((sbHalf_congr h1 h2).1 hΦ), by rw [halfInd_congr h1 h2]; exact H.vac⟩`.
-/
theorem placeModel_congr {ψ : AddChar (AF D.host.F) ℂ} {e : AE D} {Λ Λ' : AddSubgroup (WO S T)}
    (h1 : ∀ u ∈ Λ', IsHalf e u → u ∈ Λ) (h2 : Λ ≤ Λ') {c : ℂ} {f₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Tm ↔ IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ' c f₀ Tm := by
  constructor
  · intro H
    exact ⟨fun Φ hΦ => H.trans Φ ((sbHalf_congr h1 h2).2 hΦ), fun Φ hΦ => H.modul Φ ((sbHalf_congr h1 h2).2 hΦ),
      by rw [← halfInd_congr h1 h2]; exact H.vac⟩
  · intro H
    exact ⟨fun Φ hΦ => H.trans Φ ((sbHalf_congr h1 h2).1 hΦ), fun Φ hΦ => H.modul Φ ((sbHalf_congr h1 h2).1 hΦ),
      by rw [halfInd_congr h1 h2]; exact H.vac⟩

section Frames
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

/- English proof (translation)
Unfold `extFun`. Apply the tactic sequence `split_ifs <;> first | rfl | simp`.
-/
theorem extFun_smul (α : Frame p S n') (β : Frame p T n) (Ψ : Matrix n n' k → ℂ) (c : ℂ) (t : WO S T) :
    extFun α β (fun x => c * Ψ x) t = c * extFun α β Ψ t := by
  unfold extFun
  split_ifs <;> first | rfl | simp

/- English proof (translation)
Use function extensionality and compare the values at `t`. Simplify using `only [Pi.add_apply, Pi.smul_apply, extFun]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem extFun_lin (α : Frame p S n') (β : Frame p T n) (Ψ Ψ' : Matrix n n' k → ℂ) (c : ℂ) :
    extFun α β (c • Ψ + Ψ') = c • extFun α β Ψ + extFun α β Ψ' := by
  funext t
  simp only [Pi.add_apply, Pi.smul_apply, extFun]
  split_ifs <;> simp

/- English proof (translation)
Take `⟨x, hx, hpx⟩` from `(GlobalTheory.T.splitPlaceHermitianFrame_properties D k p S n β).2.2.2.2.2 g`. Establish `he : p.e * p.e = p.e` using `p.split.1`. Establish `e1 : ((Matrix.GeneralLinearGroup.det g : kˣ) : k) = p.pr x` using `by rw [hpx]; rfl`. Unfold `IsDetAt`. Rewrite using `[idl_val, e1, p.sec_pr, hx]`.

Take the linear combination `((mt S (β.gl g)).det - 1) * he`.
-/
theorem detFrame (β : Frame p S n) (g : GL n k) : IsDetAt p.e S (β.gl g) (idl p (Matrix.GeneralLinearGroup.det g)) := by
  obtain ⟨x, hx, hpx⟩ := (GlobalTheory.T.splitPlaceHermitianFrame_properties D k p S n β).2.2.2.2.2 g
  have he : p.e * p.e = p.e := p.split.1
  have e1 : ((Matrix.GeneralLinearGroup.det g : kˣ) : k) = p.pr x := by rw [hpx]; rfl
  unfold IsDetAt
  rw [idl_val, e1, p.sec_pr, hx]
  linear_combination ((mt S (β.gl g)).det - 1) * he

end Frames

/- English proof (translation)
Rewrite using `[lam_val, lam_val, GlobalTheory.SplitLinear.fac, splitFacO, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.modFac, MonoidHom.inv_apply, Circle.coe_mul, Circle.coe_inv_eq_conj, Complex.ofReal_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fac_lam {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (χS χT : (AE D)ˣ →* Circle) (a b : kˣ) :
    GlobalTheory.SplitLinear.fac S T χS χT (idl p a) (idl p b) =
      ((lam p χT⁻¹ ((T.rank : ℝ) / 2) a : ℂˣ) : ℂ) * ((lam p χS (-(S.rank : ℝ) / 2) b : ℂˣ) : ℂ) := by
  rw [lam_val, lam_val, GlobalTheory.SplitLinear.fac, splitFacO, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.modFac, MonoidHom.inv_apply, Circle.coe_mul,
    Circle.coe_inv_eq_conj, Complex.ofReal_mul]
  ring

/- English proof (translation)
Introduce `x h1 h2 h3 h4` and use `by rw [MonoidHom.inv_apply, h x h1 h2 h3 h4, inv_one]`.
-/
theorem unram_inv {χ : (AE D)ˣ →* Circle} {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F)}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χ v) : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χ⁻¹ v := fun x h1 h2 h3 h4 => by
  rw [MonoidHom.inv_apply, h x h1 h2 h3 h4, inv_one]

end GlobalTheory.SplitLinAt
end

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitLinAt
open GlobalTheory.SplitLinear

/- English proof (translation)
Introduce `D k _ _ _ _ p ψ S T χS χT om hW`. Use `⟨lam p χT⁻¹ ((T.rank : ℝ) / 2), lam p χS (-(S.rank : ℝ) / 2), fun h => lamUnram D k p _ _ (unram_inv h), fun h => lamUnram D k p _ _ h, ?_⟩` and prove the remaining obligations. Introduce `n n' _ _ _ _ α β LS LT f₀ Ψ f hO`. Take `⟨hsS, hsT, hV, hΨ, hth⟩` from `hO`. Establish `he : IsSplitIdem D p.e` using `p.split`.

Establish `hec : IsSplitIdem D (cA D p.e)` using `GlobalTheory.SplitScalar.isSplitIdem_conj he`. Establish `hA : ∀ u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (fun _ => True), IsHalf p.e u → u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v)` using `fun u hu hh => latHalf D k p S T LS LT u hu (Or.inl hh)`. Establish `hle` using `latO_le (S := S) (T := T) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v)`. Establish `hfix : ∀ u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (fun _ => True), IsHalf p.e u ∨ IsHalf (cA D p.e) u → heisO ψ S T u f₀ = f₀` using `fun u hu hh => hh.elim (fun h1 => hV.2.2 p.e he u (latHalf D k p S T LS LT u hu hh) h1) fun h1 => hV.2.2 _ hec u (latHalf D k p S T LS LT u hu hh) h1`. Use `⟨fun g h => ⟨hsS, hsT, hV, sbSubst hΨ g h _, hth.1, fun Tm hTm => ?_⟩, fun g hg h hh => ?_, fun c Ψ' f' hO' => ?_⟩` and prove the remaining obligations.

Establish `hTm'` using `(placeModel_congr hA hle).1 hTm`. Establish `hSB` using `(sbHalf_congr hA hle).1 (sbHalf D k p S T n n' α β LS LT hsS hsT Ψ hΨ)`. Rewrite using `[hth.2 Tm hTm, lawAt D ψ S T χS χT om LS LT p.e f₀ Tm hW hsS hsT he hV.1 hfix hTm' (α.gl g) (β.gl h) (α.gl_supp g) (β.gl_supp h) _ _ (detFrame α g) (detFrame β h) _ hSB, ← map_smul, fac_lam]`. Use `congr 1`. Use function extensionality and compare the values at `t`.

Rewrite using `[Pi.smul_apply, smul_eq_mul, extFunAct D k p S T n n' α β Ψ g h t, ← extFun_smul]`. Establish `act : ∀ u : WO S T, (u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v) ∨ IsHalf p.e u ∨ IsHalf (cA D p.e) u) → actO S T g h u = u` using `offAct D k p S T LS LT g h hg hh`. Establish `hV' : Vac ψ S T LS LT (· = p.v) (om (g, h) f₀)`. Use `⟨hW.om_pres _ _ hV.1, fun u hu => ?_, fun e' he' u hu hh' => ?_⟩` and prove the remaining obligations. Use `hW.om_heis g h (2 • u) f₀ hV.1` as an intermediate fact.

Rewrite `this` using `[hV.2.1 u hu, act _ (Or.inl (nsmul_mem hu 2))]`. Conclude with `this.symm`. Use `hW.om_heis g h u f₀ hV.1` as an intermediate fact. Rewrite `this` using `[hV.2.2 e' he' u hu hh', act _ (Or.inl hu)]`. Conclude with `this.symm`.

Take `⟨Tm, hTm⟩` from `hth.1`. Establish `hTm'` using `(placeModel_congr hA hle).1 hTm`. Establish `hth0 : ∀ Φ, IsSBHalf p.e (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v)) Φ → IsThetaFunO ψ S T (Tm Φ)` using `fun Φ hΦ => thetaModel D ψ S T LS LT p.e f₀ Tm hW.std hsS hsT he hV.1 hTm' Φ ((sbHalf_congr hA hle).1 hΦ)`. Establish `hPM : IsPlaceModel ψ (symplO S T) (heisO ψ S T) p.e (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v)) 1 (om (g, h) f₀) ((om (g, h)).comp Tm)`. Use `⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[LinearMap.comp_apply, hTm.trans Φ hΦ x hx, hW.om_heis g h x _ (hth0 Φ hΦ), act x (Or.inr (Or.inl hx))]`. Both sides reduce to the same expression. Rewrite using `[LinearMap.comp_apply, hTm.modul Φ hΦ y hy, hW.om_heis g h y _ (hth0 Φ hΦ), act y (Or.inr (Or.inr hy))]`. Both sides reduce to the same expression. Rewrite using `[LinearMap.comp_apply, hTm.vac]`.

Take `⟨f', hf', -⟩` from `((GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D) k p n n' ψ hW.std S T α β LS LT hsS hsT (om (g, h) f₀) hV').1 Ψ hΨ`. Establish `e1 : f' = om (g, h) f`. Rewrite using `[hf'.2.2.2.2.2 _ hPM, hth.2 Tm hTm]`. Both sides reduce to the same expression. Use `⟨hsS, hsT, hV', hΨ, ⟨_, hPM⟩, fun Tm' hTm'' => ?_⟩` and prove the remaining obligations.

Rewrite using `[← e1]`. Conclude with `hf'.2.2.2.2.2 Tm' hTm''`. Take `⟨-, -, -, hΨ', hth'⟩` from `hO'`. Use `⟨hsS, hsT, hV, add_mem (Submodule.smul_mem _ c hΨ) hΨ', hth.1, fun Tm hTm => ?_⟩` and prove the remaining obligations. Rewrite using `[hth.2 Tm hTm, hth'.2 Tm hTm, extFun_lin]`.

Use `beta_reduce`. Rewrite using `[map_add, map_smul]`.
-/
theorem linModelAt : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∃ lS lT : kˣ →* ℂˣ, (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χT p.v → IsUnram lS) ∧ (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χS p.v → IsUnram lT) ∧ ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T) (f₀ : WO S T → ℂ) (Ψ : Matrix n n' k → ℂ) (f : WO S T → ℂ), Over ψ α β LS LT f₀ Ψ f → (∀ (g : GL n' k) (h : GL n k), Over ψ α β LS LT f₀ (fun x => (lS (Matrix.GeneralLinearGroup.det g) : ℂ) * (lT (Matrix.GeneralLinearGroup.det h) : ℂ) * Ψ ((h⁻¹ : GL n k).val * x * g.val)) (om (α.gl g, β.gl h) f)) ∧ (∀ g ∈ grpOff S (· = p.v), ∀ h ∈ grpOff T (· = p.v), Over ψ α β LS LT (om (g, h) f₀) Ψ (om (g, h) f)) ∧ ∀ (c : ℂ) (Ψ' : Matrix n n' k → ℂ) (f' : WO S T → ℂ), Over ψ α β LS LT f₀ Ψ' f' → Over ψ α β LS LT f₀ (c • Ψ + Ψ') (c • f + f') := by
  intro D k _ _ _ _ p ψ S T χS χT om hW
  refine ⟨lam p χT⁻¹ ((T.rank : ℝ) / 2), lam p χS (-(S.rank : ℝ) / 2),
    fun h => lamUnram D k p _ _ (unram_inv h), fun h => lamUnram D k p _ _ h, ?_⟩
  intro n n' _ _ _ _ α β LS LT f₀ Ψ f hO
  obtain ⟨hsS, hsT, hV, hΨ, hth⟩ := hO
  have he : IsSplitIdem D p.e := p.split
  have hec : IsSplitIdem D (cA D p.e) := GlobalTheory.SplitScalar.isSplitIdem_conj he
  have hA : ∀ u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      IsHalf p.e u → u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v) :=
    fun u hu hh => latHalf D k p S T LS LT u hu (Or.inl hh)
  have hle := latO_le (S := S) (T := T) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v)
  have hfix : ∀ u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      IsHalf p.e u ∨ IsHalf (cA D p.e) u → heisO ψ S T u f₀ = f₀ := fun u hu hh =>
    hh.elim (fun h1 => hV.2.2 p.e he u (latHalf D k p S T LS LT u hu hh) h1)
      fun h1 => hV.2.2 _ hec u (latHalf D k p S T LS LT u hu hh) h1
  refine ⟨fun g h => ⟨hsS, hsT, hV, sbSubst hΨ g h _, hth.1, fun Tm hTm => ?_⟩, fun g hg h hh => ?_,
    fun c Ψ' f' hO' => ?_⟩
  ·
    have hTm' := (placeModel_congr hA hle).1 hTm
    have hSB := (sbHalf_congr hA hle).1 (sbHalf D k p S T n n' α β LS LT hsS hsT Ψ hΨ)
    rw [hth.2 Tm hTm, lawAt D ψ S T χS χT om LS LT p.e f₀ Tm hW hsS hsT he hV.1 hfix hTm' (α.gl g) (β.gl h)
      (α.gl_supp g) (β.gl_supp h) _ _ (detFrame α g) (detFrame β h) _ hSB, ← map_smul, fac_lam]
    congr 1
    funext t
    rw [Pi.smul_apply, smul_eq_mul, extFunAct D k p S T n n' α β Ψ g h t, ← extFun_smul]
  ·
    have act : ∀ u : WO S T, (u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
        (· = p.v) ∨ IsHalf p.e u ∨ IsHalf (cA D p.e) u) → actO S T g h u = u := offAct D k p S T LS LT g h hg hh
    have hV' : Vac ψ S T LS LT (· = p.v) (om (g, h) f₀) := by
      refine ⟨hW.om_pres _ _ hV.1, fun u hu => ?_, fun e' he' u hu hh' => ?_⟩
      · have := hW.om_heis g h (2 • u) f₀ hV.1
        rw [hV.2.1 u hu, act _ (Or.inl (nsmul_mem hu 2))] at this
        exact this.symm
      · have := hW.om_heis g h u f₀ hV.1
        rw [hV.2.2 e' he' u hu hh', act _ (Or.inl hu)] at this
        exact this.symm
    obtain ⟨Tm, hTm⟩ := hth.1
    have hTm' := (placeModel_congr hA hle).1 hTm
    have hth0 : ∀ Φ, IsSBHalf p.e (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
        (· = p.v)) Φ → IsThetaFunO ψ S T (Tm Φ) := fun Φ hΦ =>
      thetaModel D ψ S T LS LT p.e f₀ Tm hW.std hsS hsT he hV.1 hTm' Φ ((sbHalf_congr hA hle).1 hΦ)
    have hPM : IsPlaceModel ψ (symplO S T) (heisO ψ S T) p.e
        (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v)) 1 (om (g, h) f₀)
        ((om (g, h)).comp Tm) := by
      refine ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩
      · rw [LinearMap.comp_apply, hTm.trans Φ hΦ x hx, hW.om_heis g h x _ (hth0 Φ hΦ), act x (Or.inr (Or.inl hx))]
        rfl
      · rw [LinearMap.comp_apply, hTm.modul Φ hΦ y hy, hW.om_heis g h y _ (hth0 Φ hΦ), act y (Or.inr (Or.inr hy))]
        rfl
      · rw [LinearMap.comp_apply, hTm.vac]
    obtain ⟨f', hf', -⟩ := ((GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D) k p n n' ψ hW.std S T α β LS LT hsS hsT (om (g, h) f₀) hV').1 Ψ hΨ
    have e1 : f' = om (g, h) f := by
      rw [hf'.2.2.2.2.2 _ hPM, hth.2 Tm hTm]
      rfl
    refine ⟨hsS, hsT, hV', hΨ, ⟨_, hPM⟩, fun Tm' hTm'' => ?_⟩
    rw [← e1]
    exact hf'.2.2.2.2.2 Tm' hTm''
  ·
    obtain ⟨-, -, -, hΨ', hth'⟩ := hO'
    refine ⟨hsS, hsT, hV, add_mem (Submodule.smul_mem _ c hΨ) hΨ', hth.1, fun Tm hTm => ?_⟩
    rw [hth.2 Tm hTm, hth'.2 Tm hTm, extFun_lin]
    beta_reduce
    rw [map_add, map_smul]

end GlobalTheory.SplitLinAt
end
