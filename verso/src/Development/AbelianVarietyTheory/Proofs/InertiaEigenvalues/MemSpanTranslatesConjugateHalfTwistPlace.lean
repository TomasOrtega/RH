import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasShape
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIdempotentPlaceChartFiniteAdelesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameAdjointChartBijectiveConjugateHalfStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitarySupportedAtSplitPlaceLiftStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSupportedUnitaryAdjointActionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParahoricSchwartzMemSpanDatumTranslatesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchwartzBruhatConjHalfLocallyConstantCompactSuppStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section
namespace GlobalTheory.DownLift.ConjHalfGen

/- English proof (translation)
Unfold `LowZero`. Simplify using `only [Matrix.map_apply, map_eq_zero_iff f f.injective]`.
-/
theorem lowZero_map_iff {A B : Type} [CommRing A] [CommRing B] (f : A ≃+* B) {b a : ℕ} (k : ℕ)
    (y : Matrix (Fin b) (Fin a) A) : LowZero k (y.map f) ↔ LowZero k y := by
  unfold LowZero
  simp only [Matrix.map_apply, map_eq_zero_iff f f.injective]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [topL, Matrix.map_apply]`. Apply the tactic sequence `split_ifs <;> simp [hf]`.
-/
theorem topL_map {A B : Type} [Zero A] [Zero B] (f : A → B) (hf : f 0 = 0) {b a : ℕ} (k : ℕ)
    (y : Matrix (Fin b) (Fin a) A) : topL k (y.map f) = (topL k y).map f := by
  ext i j
  simp only [topL, Matrix.map_apply]
  split_ifs <;> simp [hf]

/- English proof (translation)
Rewrite using `[topL_map f (map_zero f), RingHom.map_det]`. Both sides reduce to the same expression.
-/
theorem det_topL_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {b a : ℕ} (k : ℕ)
    (y : Matrix (Fin b) (Fin a) A) : (topL k (y.map f)).det = f (topL k y).det := by
  rw [topL_map f (map_zero f), RingHom.map_det]
  rfl

/- English proof (translation)
The claim follows from `det_topL_map (f : A →+* B) k y`.
-/
theorem det_topL_mapE {A B : Type} [CommRing A] [CommRing B] (f : A ≃+* B) {b a : ℕ} (k : ℕ)
    (y : Matrix (Fin b) (Fin a) A) : (topL k (y.map f)).det = f (topL k y).det :=
  det_topL_map (f : A →+* B) k y

/- English proof (translation)
Establish `h : ∀ PP' ∈ ({PP} : Finset (Pl D.host.E)), LowZero r (y PP') ∧ IsUnit (topL r (y PP')).det`. Introduce `PP' hP`. Rewrite `hP` using `[Finset.mem_singleton]`. Substitute `hP` using the available equality. Conclude with `⟨hz, hu ▸ u.isUnit⟩`.

Unfold `omegaQ`. Rewrite using `[dif_pos h, Finset.prod_eq_single ⟨PP, Finset.mem_singleton_self PP⟩]`. Rewrite using `[_root_.zpow_neg_one]`. Use `congr 4`. Use `ext`.

Simplify using `[hu]`. Introduce `x _ hx`. It suffices to derive a contradiction. Conclude with `hx (Subtype.ext (Finset.mem_singleton.1 x.2))`. Introduce `hx`.

Conclude with `absurd (Finset.mem_attach _ _) hx`.
-/
theorem omegaQ_single {D : D7} {a b : ℕ} (PP : Pl D.host.E) (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) (hz : LowZero r (y PP)) (u : (kP PP)ˣ)
    (hu : (u : kP PP) = (topL r (y PP)).det) :
    omegaQ {PP} r ξ (-1) y = ((ξ PP u : ℂˣ) : ℂ)⁻¹ := by
  have h : ∀ PP' ∈ ({PP} : Finset (Pl D.host.E)), LowZero r (y PP') ∧ IsUnit (topL r (y PP')).det := by
    intro PP' hP
    rw [Finset.mem_singleton] at hP
    subst hP
    exact ⟨hz, hu ▸ u.isUnit⟩
  unfold omegaQ
  rw [dif_pos h, Finset.prod_eq_single ⟨PP, Finset.mem_singleton_self PP⟩]
  · rw [_root_.zpow_neg_one]
    congr 4
    ext
    simp [hu]
  · intro x _ hx
    exfalso
    exact hx (Subtype.ext (Finset.mem_singleton.1 x.2))
  · intro hx
    exact absurd (Finset.mem_attach _ _) hx

/- English proof (translation)
Unfold `omegaQ at h`. Use `split_ifs at h with h'`. Conclude with `h' PP (Finset.mem_singleton_self PP)`. Conclude with `absurd rfl h`.
-/
theorem omegaQ_ne_zero {D : D7} {a b : ℕ} (PP : Pl D.host.E) (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (k : ℤ) (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) (h : omegaQ {PP} r ξ k y ≠ 0) :
    LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det := by
  unfold omegaQ at h
  split_ifs at h with h'
  · exact h' PP (Finset.mem_singleton_self PP)
  · exact absurd rfl h

end GlobalTheory.DownLift.ConjHalfGen
end

noncomputable section
namespace GlobalTheory.DownLift.ConjHalfGen

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D S T βS βT hrn ΛS ΛT N hBF hLS hLT e PP hidem ξ hξ Φ hΦ hlaw`. Take `⟨v, φ, ι, hch⟩` from `GlobalTheory.T.exists_idempotentPlaceChart_finiteAdeles D e PP hidem`. Take `⟨hsurj, hinj, hint, hred⟩` from `GlobalTheory.T.frameAdjoint_chart_bijective_conjugateHalf D S T βS βT e PP v φ ι hidem hch`. Use `haveI : Finite (IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)) := Finite.of_equiv _ ι.toEquiv`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible (GlobalTheory.SplitHecke.Ov D v)`.

Use `choose σ hσH hσ using hsurj`. Use `set ω := omegaQ {PP} T.rank ξ (-1) with hω`. Use `set Φ' : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) → ℂ := fun m => Φ (σ m) with hΦ'`. Use `set Φ₀' : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) → ℂ := fun m => adjDat S T βS βT e ω (σ m) with hΦ₀'`. Use `set ξ' : (IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v))ˣ →* ℂˣ := (ξ PP).comp (Units.map (ι.symm : IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v) ≃+* kP PP).toMonoidHom) with hξ'`.

Establish `hξ'1 : ξ' ≠ 1`. Introduce `h1`. Apply `hξ` to reduce the goal to its premises. Use extensionality with `u`. Establish `h2` using `DFunLike.congr_fun h1 (Units.map (ι : kP PP ≃+* _).toMonoidHom u)`.

Establish `h3 : Units.map (ι.symm : IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v) ≃+* kP PP).toMonoidHom (Units.map (ι : kP PP ≃+* _).toMonoidHom u) = u` using `by ext; simp`. Simplify using `only [hξ', MonoidHom.comp_apply, h3, MonoidHom.one_apply] at h2`. Rewrite using `[h2]`. Both sides reduce to the same expression. Establish `hA : ∀ (z : Matrix (Fin S.rank) (Fin T.rank) (GlobalTheory.SplitHecke.Ov D v)) (u : (IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v))ˣ), LowZero T.rank (z.map (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v))) → (u : IsLocalRing.ResidueField (GlobalTheory.SplitHeck …`.

Introduce `z u hz hu`. Use `set x := σ (z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)))`. Establish `hxH` using `hσH (z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)))`. Establish `hxr` using `hσ (z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)))`. Establish `hxI : IsIntM (frMapAdj S T βS βT x)` using `(hint x hxH).2 ⟨z, hxr⟩`.

Establish `hxR` using `hred x z hxI hxr`. Establish `hLZ : LowZero T.rank (redM PP (frMapAdj S T βS βT x))`. Rewrite using `[← lowZero_map_iff ι, hxR]`. Conclude with `hz`. Establish `hdet : ι (topL T.rank (redM PP (frMapAdj S T βS βT x))).det = (u : IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v))`.

Rewrite using `[hu, ← hxR, det_topL_mapE ι]`. Use `show adjDat S T βS βT e ω x = _`. Unfold `adjDat`. Rewrite using `[if_pos ⟨hxH, hxI⟩, hω, omegaQ_single PP T.rank ξ _ hLZ (Units.map (ι.symm : IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v) ≃+* kP PP).toMonoidHom u)]`. Both sides reduce to the same expression.

Simplify using `[← hdet]`. Establish `hB : ∀ m, Φ₀' m ≠ 0 → ∃ z : Matrix (Fin S.rank) (Fin T.rank) (GlobalTheory.SplitHecke.Ov D v), m = z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) ∧ LowZero T.rank (z.map (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v))) ∧ IsUnit (topL T.rank (z.map (IsL …`. Introduce `m hm`. Establish `hm' : adjDat S T βS βT e ω (σ m) ≠ 0` using `hm`. Unfold `adjDat at hm'`.

Use `split_ifs at hm' with hc`. Take `⟨z, hz⟩` from `(hint (σ m) hc.1).1 hc.2`. Establish `hR` using `hred (σ m) z hc.2 hz`. Take `⟨h1, h2⟩` from `omegaQ_ne_zero PP T.rank ξ (-1) _ hm'`. Use `⟨z, by rw [← hz, hσ], ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hR, lowZero_map_iff ι]`. Conclude with `h1`. Rewrite using `[← hR, det_topL_mapE ι]`. Conclude with `h2.map _`. Conclude with `absurd rfl hm'`.

Establish `hC : ∃ N : ℕ, (∀ m (z : Matrix (Fin S.rank) (Fin T.rank) (GlobalTheory.SplitHecke.Ov D v)), Φ' (m + (ϖ ^ N • z).map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v))) = Φ' m) ∧ ∀ m, Φ' m ≠ 0 → ∃ z : Matrix (Fin S.rank) (Fin T.rank) (GlobalTheory.SplitHecke.Ov D v), al …`. Take `⟨N', hinv, hsupp⟩` from `GlobalTheory.T.schwartzBruhat_conjHalf_locallyConstant_compactSupport D S T βS βT e PP v φ ι hidem hch ΛS ΛT hLS hLT Φ hΦ ϖ hϖ`. Use `⟨N', fun m z => ?_, fun m hm => ?_⟩` and prove the remaining obligations. Conclude with `hinv (σ m) _ (hσH m) (hσH _) z (by rw [hσ, hσ])`. Take `⟨z, hz⟩` from `hsupp (σ m) hm`.

Conclude with `⟨z, by rw [← hσ m]; exact hz⟩`. Establish `hD : ∀ h : GL (Fin S.rank) (GlobalTheory.SplitHecke.Ov D v), LowZero T.rank (h.val.map (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v))) → ∀ m m' : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v), Φ' (h.val.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) …`. Introduce `h hLZ m m'`. Take `⟨κ, hsupp, hGf, hSt, hrκ, hoth, hact⟩` from `GlobalTheory.T.exists_unitary_supported_at_split_place_lift D S T βS βT e PP v φ ι hidem hch ΛS N hBF h`. Establish `hBT : redFn βS PP (finE S κ) ∈ blockTri (blk2 T.rank)`.

Rewrite using `[mem_blockTri]`. Introduce `i j hij`. Establish `hj : j.val < T.rank`. Apply the tactic sequence `by_contra hj; simp only [blk2, if_neg hj] at hij; split_ifs at hij <;> omega`. Establish `hi : T.rank ≤ i.val`.

Assume the negation of the conclusion as `hi`. Simplify using `only [blk2, if_pos (Nat.lt_of_not_le hi)] at hij`. Use linear arithmetic over natural numbers and integers. Establish `h1` using `congrFun (congrFun hrκ i) j`. Simplify using `only [Matrix.map_apply] at h1`.

Establish `h4` using `hLZ i j hi hj`. Simplify using `only [Matrix.map_apply] at h4`. Conclude with `ι.injective ((h1.trans h4).trans (map_zero ι).symm)`. Establish `hmove : ∀ y, σ (h.val.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) * y) = actO S T κ 1 (σ y)`. Introduce `y`.

Use `hinj _ _ (hσH _) (GlobalTheory.SplitHecke.isHalf_actO κ 1 (hσH y)) ?_` and prove the remaining obligations. Rewrite using `[hσ, hact, hσ]`. Use `show Φ (σ _) * adjDat S T βS βT e ω (σ m') = Φ (σ m) * adjDat S T βS βT e ω (σ _)`. Rewrite using `[hmove, hmove]`. Conclude with `hlaw κ hsupp hGf hSt hBT hoth (σ m) (σ m') (hσH m) (hσH m')`.

Establish `hpure` using `GlobalTheory.T.parahoric_schwartz_mem_span_datum_translates_alt (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v) S.rank T.rank hrn ϖ hϖ ξ' hξ'1 Φ' Φ₀' hA hB hC hD`. Apply the tactic sequence `let L : ((Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v)) → ℂ) →ₗ[ℂ] (WO S T → ℂ) := { toFun := fun Ψ x => if IsHalf (cA D e) x then Ψ (rdAdj S T βS βT φ x) else 0 map_add' := fun Ψ Ψ' => by funext x; simp only [Pi.add_apply]; split_ifs <;> simp map_smul' := fun c Ψ => by funex …`. Establish `hLΦ : L Φ' = Φ`. Use function extensionality and compare the values at `x`. Use `show (if IsHalf (cA D e) x then Φ (σ (rdAdj S T βS βT φ x)) else 0) = Φ x`.

Use `split_ifs with hx`. Rewrite using `[hinj _ x (hσH _) hx (hσ _)]`. Assume the negation of the conclusion as `hne`. Conclude with `hx (hΦ.1 x (Ne.symm hne))`. Establish `hmem` using `Submodule.mem_map_of_mem (f := L) hpure`.

Rewrite `hmem` using `[Submodule.map_span, hLΦ]`. Use `Submodule.span_mono ?_ hmem` and prove the remaining obligations. Introduce and unpack `_ ⟨Ψ, ⟨γ, rfl⟩, rfl⟩`. Take `⟨g, hgs, hgx⟩` from `GlobalTheory.T.exists_supported_unitary_adjoint_action D S T βS βT e PP v φ ι hidem hch γ`. Use `⟨g, ?_, ?_⟩` and prove the remaining obligations.

Introduce `i j`. Use `hgs i j` as an intermediate fact. Rewrite using `[Formalism.L2.Theta.cA_cA, add_comm]` and apply the resulting hypothesis. Use function extensionality and compare the values at `x show (if IsHalf (cA D e) x then adjDat S T βS βT e ω (σ (rdAdj S T βS βT φ x * γ.val)) else 0) = adjDat S T βS βT e ω (actO S T 1 g x) split_ifs with hx`. Establish `hgH` using `GlobalTheory.SplitHecke.isHalf_actO 1 g hx`.

Rewrite using `[hinj _ (actO S T 1 g x) (hσH _) hgH (by rw [hσ, hgx])]`. Establish `hgH : ¬ IsHalf (cA D e) (actO S T 1 g x)`. Introduce `h'`. Use `GlobalTheory.SplitHecke.isHalf_actO (1 : GA D S)⁻¹ g⁻¹ h'` as an intermediate fact. Rewrite `this` using `[GlobalTheory.SplitHecke.actO_inv_actO]`.

Conclude with `hx this`. Unfold `adjDat`. Rewrite using `[if_neg (fun h' => hgH h'.1)]`.
-/
theorem mem_span_translT : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)), T.rank ≤ S.rank → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), ∀ N : ℕ, IsBaseFrame S βS ΛS N → Submodule.IsLattice D.host.E ΛS → Submodule.IsLattice D.host.E ΛT → ∀ (e : AE D) (PP : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e PP → ∀ ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ, ξ PP ≠ 1 → ∀ Φ : WO S T → ℂ, IsSBHalf (cA D e) (latH S T ΛS ΛT) Φ → (∀ κ : GA D S, SuppAt e S κ → κ ∈ GfC S → finE S κ ∈ St βS → redFn βS PP (finE S κ) ∈ blockTri (blk2 T.rank) → (∀ PP', PP' ≠ PP → ¬ Formalism.IndefR.Lev.IsConjPl PP PP' → redFn βS PP' (finE S κ) = 1) → ∀ x x' : WO S T, IsHalf (cA D e) x → IsHalf (cA D e) x' → Φ (actO S T κ 1 x) * adjDat S T βS βT e (omegaQ {PP} T.rank ξ (-1)) x' = Φ x * adjDat S T βS βT e (omegaQ {PP} T.rank ξ (-1)) (actO S T κ 1 x')) → Φ ∈ Submodule.span ℂ (translT S T (cA D e) (adjDat S T βS βT e (omegaQ {PP} T.rank ξ (-1)))) := by
  classical
  intro D S T βS βT hrn ΛS ΛT N hBF hLS hLT e PP hidem ξ hξ Φ hΦ hlaw
  obtain ⟨v, φ, ι, hch⟩ := GlobalTheory.T.exists_idempotentPlaceChart_finiteAdeles D e PP hidem
  obtain ⟨hsurj, hinj, hint, hred⟩ := GlobalTheory.T.frameAdjoint_chart_bijective_conjugateHalf D S T βS βT e PP v φ ι hidem hch
  haveI : Finite (IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)) := Finite.of_equiv _ ι.toEquiv
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (GlobalTheory.SplitHecke.Ov D v)
  choose σ hσH hσ using hsurj
  set ω := omegaQ {PP} T.rank ξ (-1) with hω
  set Φ' : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) → ℂ := fun m => Φ (σ m) with hΦ'
  set Φ₀' : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) → ℂ := fun m => adjDat S T βS βT e ω (σ m) with hΦ₀'
  set ξ' : (IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v))ˣ →* ℂˣ :=
    (ξ PP).comp (Units.map (ι.symm : IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v) ≃+* kP PP).toMonoidHom) with hξ'
  have hξ'1 : ξ' ≠ 1 := by
    intro h1
    apply hξ
    ext u
    have h2 := DFunLike.congr_fun h1 (Units.map (ι : kP PP ≃+* _).toMonoidHom u)
    have h3 : Units.map (ι.symm : IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v) ≃+* kP PP).toMonoidHom
        (Units.map (ι : kP PP ≃+* _).toMonoidHom u) = u := by
      ext; simp
    simp only [hξ', MonoidHom.comp_apply, h3, MonoidHom.one_apply] at h2
    rw [h2]; rfl

  have hA : ∀ (z : Matrix (Fin S.rank) (Fin T.rank) (GlobalTheory.SplitHecke.Ov D v)) (u : (IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v))ˣ),
      LowZero T.rank (z.map (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v))) →
      (u : IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)) = (topL T.rank (z.map (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v)))).det →
      Φ₀' (z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v))) = ((ξ' u : ℂˣ) : ℂ)⁻¹ := by
    intro z u hz hu
    set x := σ (z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)))
    have hxH := hσH (z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)))
    have hxr := hσ (z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)))
    have hxI : IsIntM (frMapAdj S T βS βT x) := (hint x hxH).2 ⟨z, hxr⟩
    have hxR := hred x z hxI hxr
    have hLZ : LowZero T.rank (redM PP (frMapAdj S T βS βT x)) := by
      rw [← lowZero_map_iff ι, hxR]; exact hz
    have hdet : ι (topL T.rank (redM PP (frMapAdj S T βS βT x))).det = (u : IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)) := by
      rw [hu, ← hxR, det_topL_mapE ι]
    show adjDat S T βS βT e ω x = _
    unfold adjDat
    rw [if_pos ⟨hxH, hxI⟩, hω, omegaQ_single PP T.rank ξ _ hLZ
      (Units.map (ι.symm : IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v) ≃+* kP PP).toMonoidHom u)]
    · rfl
    · simp [← hdet]
  have hB : ∀ m, Φ₀' m ≠ 0 → ∃ z : Matrix (Fin S.rank) (Fin T.rank) (GlobalTheory.SplitHecke.Ov D v),
      m = z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) ∧
      LowZero T.rank (z.map (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v))) ∧
      IsUnit (topL T.rank (z.map (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v)))).det := by
    intro m hm
    have hm' : adjDat S T βS βT e ω (σ m) ≠ 0 := hm
    unfold adjDat at hm'
    split_ifs at hm' with hc
    · obtain ⟨z, hz⟩ := (hint (σ m) hc.1).1 hc.2
      have hR := hred (σ m) z hc.2 hz
      obtain ⟨h1, h2⟩ := omegaQ_ne_zero PP T.rank ξ (-1) _ hm'
      refine ⟨z, by rw [← hz, hσ], ?_, ?_⟩
      · rw [← hR, lowZero_map_iff ι]; exact h1
      · rw [← hR, det_topL_mapE ι]; exact h2.map _
    · exact absurd rfl hm'

  have hC : ∃ N : ℕ, (∀ m (z : Matrix (Fin S.rank) (Fin T.rank) (GlobalTheory.SplitHecke.Ov D v)),
      Φ' (m + (ϖ ^ N • z).map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v))) = Φ' m) ∧
      ∀ m, Φ' m ≠ 0 → ∃ z : Matrix (Fin S.rank) (Fin T.rank) (GlobalTheory.SplitHecke.Ov D v),
        algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v) (ϖ ^ N) • m = z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) := by
    obtain ⟨N', hinv, hsupp⟩ := GlobalTheory.T.schwartzBruhat_conjHalf_locallyConstant_compactSupport D S T βS βT e PP v φ ι hidem hch ΛS ΛT hLS hLT Φ hΦ ϖ hϖ
    refine ⟨N', fun m z => ?_, fun m hm => ?_⟩
    · exact hinv (σ m) _ (hσH m) (hσH _) z (by rw [hσ, hσ])
    · obtain ⟨z, hz⟩ := hsupp (σ m) hm
      exact ⟨z, by rw [← hσ m]; exact hz⟩

  have hD : ∀ h : GL (Fin S.rank) (GlobalTheory.SplitHecke.Ov D v), LowZero T.rank (h.val.map (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v))) →
      ∀ m m' : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v),
      Φ' (h.val.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) * m) * Φ₀' m' =
        Φ' m * Φ₀' (h.val.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) * m') := by
    intro h hLZ m m'
    obtain ⟨κ, hsupp, hGf, hSt, hrκ, hoth, hact⟩ := GlobalTheory.T.exists_unitary_supported_at_split_place_lift D S T βS βT e PP v φ ι hidem hch ΛS N hBF h
    have hBT : redFn βS PP (finE S κ) ∈ blockTri (blk2 T.rank) := by
      rw [mem_blockTri]
      intro i j hij
      have hj : j.val < T.rank := by
        by_contra hj; simp only [blk2, if_neg hj] at hij; split_ifs at hij <;> omega
      have hi : T.rank ≤ i.val := by
        by_contra hi; simp only [blk2, if_pos (Nat.lt_of_not_le hi)] at hij; omega
      have h1 := congrFun (congrFun hrκ i) j
      simp only [Matrix.map_apply] at h1
      have h4 := hLZ i j hi hj
      simp only [Matrix.map_apply] at h4
      exact ι.injective ((h1.trans h4).trans (map_zero ι).symm)
    have hmove : ∀ y, σ (h.val.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) * y) = actO S T κ 1 (σ y) := by
      intro y
      refine hinj _ _ (hσH _) (GlobalTheory.SplitHecke.isHalf_actO κ 1 (hσH y)) ?_
      rw [hσ, hact, hσ]
    show Φ (σ _) * adjDat S T βS βT e ω (σ m') = Φ (σ m) * adjDat S T βS βT e ω (σ _)
    rw [hmove, hmove]
    exact hlaw κ hsupp hGf hSt hBT hoth (σ m) (σ m') (hσH m) (hσH m')
  have hpure := GlobalTheory.T.parahoric_schwartz_mem_span_datum_translates_alt (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v) S.rank T.rank hrn ϖ hϖ ξ' hξ'1 Φ' Φ₀' hA hB hC hD

  let L : ((Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v)) → ℂ) →ₗ[ℂ] (WO S T → ℂ) :=
    { toFun := fun Ψ x => if IsHalf (cA D e) x then Ψ (rdAdj S T βS βT φ x) else 0
      map_add' := fun Ψ Ψ' => by funext x; simp only [Pi.add_apply]; split_ifs <;> simp
      map_smul' := fun c Ψ => by funext x; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp }
  have hLΦ : L Φ' = Φ := by
    funext x
    show (if IsHalf (cA D e) x then Φ (σ (rdAdj S T βS βT φ x)) else 0) = Φ x
    split_ifs with hx
    · rw [hinj _ x (hσH _) hx (hσ _)]
    · by_contra hne
      exact hx (hΦ.1 x (Ne.symm hne))
  have hmem := Submodule.mem_map_of_mem (f := L) hpure
  rw [Submodule.map_span, hLΦ] at hmem
  refine Submodule.span_mono ?_ hmem
  rintro _ ⟨Ψ, ⟨γ, rfl⟩, rfl⟩
  obtain ⟨g, hgs, hgx⟩ := GlobalTheory.T.exists_supported_unitary_adjoint_action D S T βS βT e PP v φ ι hidem hch γ
  refine ⟨g, ?_, ?_⟩
  · intro i j
    have := hgs i j
    rwa [Formalism.L2.Theta.cA_cA, add_comm]
  · funext x
    show (if IsHalf (cA D e) x then adjDat S T βS βT e ω (σ (rdAdj S T βS βT φ x * γ.val)) else 0) = adjDat S T βS βT e ω (actO S T 1 g x)
    split_ifs with hx
    · have hgH := GlobalTheory.SplitHecke.isHalf_actO 1 g hx
      rw [hinj _ (actO S T 1 g x) (hσH _) hgH (by rw [hσ, hgx])]
    · have hgH : ¬ IsHalf (cA D e) (actO S T 1 g x) := by
        intro h'
        have := GlobalTheory.SplitHecke.isHalf_actO (1 : GA D S)⁻¹ g⁻¹ h'
        rw [GlobalTheory.SplitHecke.actO_inv_actO] at this
        exact hx this
      unfold adjDat
      rw [if_neg (fun h' => hgH h'.1)]

end GlobalTheory.DownLift.ConjHalfGen
end
