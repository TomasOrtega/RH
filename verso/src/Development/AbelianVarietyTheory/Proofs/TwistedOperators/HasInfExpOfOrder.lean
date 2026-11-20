import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivariantOfWave
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DifferentiableOfChar
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdelicCharacterPowEqOneFiniteIdelesOfOrderDvd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqOneOfTrivialFinitePartOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNthRootIdeleFinitePartOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoInfMulProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqMulOfResSNeOne

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx GlobalTheory.Chain NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.StepVac

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum

variable {D : D7}

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, RingHom.map_zero _⟩`. Consider the case `tmul b α => exact ⟨pairA D.host.F 0 α ⊗ₜ[D.host.F] b, rfl⟩`. Consider the case `add x y hx hy`. Take `⟨a, rfl⟩` from `hx`.

Take `⟨b, rfl⟩` from `hy`. Conclude with `⟨a + b, RingHom.map_add _ _ _⟩`.
-/
theorem toEAf_surjective (z : EAf D) : ∃ w : AE D, toEAf D w = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | tmul b α => exact ⟨pairA D.host.F 0 α ⊗ₜ[D.host.F] b, rfl⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, RingHom.map_add _ _ _⟩

/- English proof (translation)
Rewrite using `[map_sum]`. Conclude with `sum_mem h`.
-/
theorem map_sum_mem {R R' ι : Type} [CommRing R] [CommRing R'] (f : R →+* R') (A : Subring R') (p : ι → R) (s : Finset ι)
    (h : ∀ i ∈ s, f (p i) ∈ A) : f (∑ i ∈ s, p i) ∈ A := by
  rw [map_sum]; exact sum_mem h

/- English proof (translation)
Use `split_ifs at h ⊢`. Substitute `h` using the available equality. Conclude with `h1`. Substitute `h` using the available equality. Conclude with `f.map_zero`.
-/
theorem res_ite {R κ : Type} [CommRing R] [CommRing κ] (A : Subring R) (f : A →+* κ) {c z : R} (hc : c ∈ A) (hz : z ∈ A)
    (h1 : f ⟨c, hc⟩ = 1) (p : Prop) [Decidable p] (h : z = if p then c else 0) : f ⟨z, hz⟩ = if p then 1 else 0 := by
  split_ifs at h ⊢
  · subst h; exact h1
  · subst h; exact f.map_zero

/- English proof (translation)
Establish `hee` using `idemSum_mul_self he`. Take `⟨⟨es, hes, hs⟩, hc⟩` from `he`. Use `choose hi h1 using fun PP hP => GlobalTheory.IdemRes.resS_idem_eq_one D (es PP) PP (hes PP hP)`. Establish `h : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E`. Rewrite using `[hs]`.

Conclude with `map_sum_mem (toEAf D) _ es P hi`. Use `⟨h, fun PP hP => ?_⟩` and prove the remaining obligations. Establish `hcross` using `cross_eq_zero (R := AE D) isUnit_natCast (cA D) es P (fun i hi => (hes i hi).1.1) (hs ▸ hc)`. Establish `hm : e * es PP = es PP`. Rewrite using `[hs, Finset.sum_mul, Finset.sum_eq_single PP (fun j hj hji => idemAt_mul (hes j hj) (hes PP hP) (hcross j hj PP hP) (hcross PP hP j hj) hji.symm) (fun h => absurd hP h)]`.

Conclude with `(hes PP hP).1.1`. Establish `: (⟨toEAf D e, h⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * ⟨toEAf D (es PP), hi PP hP⟩ = ⟨toEAf D (es PP), hi PP hP⟩` using `Subtype.ext ((RingHom.map_mul _ _ _).symm.trans (congrArg _ hm))`. Establish `h2` using `congrArg (resS D.host.F PP) this`. Rewrite `h2` using `[RingHom.map_mul, h1 PP hP, mul_one]`. Then use the resulting hypothesis.
-/
theorem res_idemSum {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) :
    ∃ h : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, ∀ PP ∈ P, resS D.host.F PP ⟨toEAf D e, h⟩ = 1 := by
  have hee := idemSum_mul_self he
  obtain ⟨⟨es, hes, hs⟩, hc⟩ := he
  choose hi h1 using fun PP hP => GlobalTheory.IdemRes.resS_idem_eq_one D (es PP) PP (hes PP hP)
  have h : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [hs]; exact map_sum_mem (toEAf D) _ es P hi
  refine ⟨h, fun PP hP => ?_⟩
  have hcross := cross_eq_zero (R := AE D) isUnit_natCast (cA D) es P (fun i hi => (hes i hi).1.1) (hs ▸ hc)
  have hm : e * es PP = es PP := by
    rw [hs, Finset.sum_mul, Finset.sum_eq_single PP (fun j hj hji =>
      idemAt_mul (hes j hj) (hes PP hP) (hcross j hj PP hP) (hcross PP hP j hj) hji.symm) (fun h => absurd hP h)]
    exact (hes PP hP).1.1
  have : (⟨toEAf D e, h⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * ⟨toEAf D (es PP), hi PP hP⟩ =
      ⟨toEAf D (es PP), hi PP hP⟩ := Subtype.ext ((RingHom.map_mul _ _ _).symm.trans (congrArg _ hm))
  have h2 := congrArg (resS D.host.F PP) this
  rwa [RingHom.map_mul, h1 PP hP, mul_one] at h2

def rectOne (κ : Type) [Zero κ] [One κ] (b a : ℕ) : Matrix (Fin b) (Fin a) κ := fun i j => if i.val = j.val then 1 else 0

/- English proof (translation)
Introduce `i j hi hj` and use `if_neg (by omega)`.
-/
theorem lowZero_rectOne (κ : Type) [Zero κ] [One κ] (b a k : ℕ) : LowZero k (rectOne κ b a) :=
  fun i j hi hj => if_neg (by omega)

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[topL, dif_pos ⟨by omega, by omega⟩, rectOne, Matrix.one_apply]`. Simplify using `only [Fin.ext_iff]`.
-/
theorem topL_rectOne (κ : Type) [Zero κ] [One κ] {b a k : ℕ} (ha : k ≤ a) (hb : k ≤ b) : topL k (rectOne κ b a) = 1 := by
  ext i j
  rw [topL, dif_pos ⟨by omega, by omega⟩, rectOne, Matrix.one_apply]
  simp only [Fin.ext_iff]

/- English proof (translation)
Rewrite using `[Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]`.
-/
theorem frame_cancel {A : Type} [CommRing A] {a b : ℕ} (βS : GL (Fin a) A) (βT : GL (Fin b) A) (c : A)
    (I : Matrix (Fin b) (Fin a) A) : (βT⁻¹).val * (c • (βT.val * I * (βS⁻¹).val)) * βS.val = c • I := by
  rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul,
    Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

/- English proof (translation)
Take `⟨h, h1⟩` from `res_idemSum he`. Use `choose s hs using toEAf_surjective (D := D)`. Take `⟨M, hM⟩ : ∃ M : Matrix (Fin T.rank) (Fin S.rank) (EAf D), ∀ c : EAf D, HMul.hMul (HMul.hMul (βT⁻¹).val (c • M)) βS.val = c • rectOne (EAf D) T.rank S.rank` from `⟨_, fun c => frame_cancel βS βT c _⟩`. Set `x : WO S T` to `fun i j => e * s (M i j)`. Establish `hx : frMapO S T βS βT x = toEAf D e • rectOne (EAf D) T.rank S.rank`.

Rewrite using `[← hM]`. Unfold `frMapO`. Use `congr 2`. Use extensionality with `i j`. Conclude with `(RingHom.map_mul _ _ _).trans (congrArg _ (hs _))`.

Establish `hx' : ∀ i j, frMapO S T βS βT x i j = if i.val = j.val then toEAf D e else 0` using `fun i j => by`. Rewrite using `[hx, Matrix.smul_apply, rectOne, smul_eq_mul, mul_ite, mul_one, mul_zero]`. Establish `hi : IsIntM (frMapO S T βS βT x)` using `fun i j => by`. Rewrite using `[hx']`. Use `split_ifs`.

Use `exacts [h, zero_mem _]`. Use `⟨x, fun i j => by rw [← mul_assoc, idemSum_mul_self he], hi, fun PP hP => ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Conclude with `(dif_pos (hi i j)).trans (res_ite _ (resS D.host.F PP) h (hi i j) (h1 PP hP) _ (hx' i j))`.
-/
theorem exists_point (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) {e : AE D}
    {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) : ∃ x : WO S T, IsHalf e x ∧ IsIntM (frMapO S T βS βT x) ∧
      ∀ PP ∈ P, redM PP (frMapO S T βS βT x) = rectOne _ _ _ := by
  obtain ⟨h, h1⟩ := res_idemSum he
  choose s hs using toEAf_surjective (D := D)
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin T.rank) (Fin S.rank) (EAf D), ∀ c : EAf D,
      HMul.hMul (HMul.hMul (βT⁻¹).val (c • M)) βS.val = c • rectOne (EAf D) T.rank S.rank := ⟨_, fun c => frame_cancel βS βT c _⟩
  let x : WO S T := fun i j => e * s (M i j)
  have hx : frMapO S T βS βT x = toEAf D e • rectOne (EAf D) T.rank S.rank := by
    rw [← hM]
    unfold frMapO
    congr 2
    ext i j
    exact (RingHom.map_mul _ _ _).trans (congrArg _ (hs _))
  have hx' : ∀ i j, frMapO S T βS βT x i j = if i.val = j.val then toEAf D e else 0 := fun i j => by
    rw [hx, Matrix.smul_apply, rectOne, smul_eq_mul, mul_ite, mul_one, mul_zero]
  have hi : IsIntM (frMapO S T βS βT x) := fun i j => by
    rw [hx']
    split_ifs
    exacts [h, zero_mem _]
  refine ⟨x, fun i j => by rw [← mul_assoc, idemSum_mul_self he], hi, fun PP hP => ?_⟩
  ext i j
  exact (dif_pos (hi i j)).trans (res_ite _ (resS D.host.F PP) h (hi i j) (h1 PP hP) _ (hx' i j))

/- English proof (translation)
Unfold `omegaG`. Rewrite using `[dif_pos]`. Use `mul_ne_zero (mul_ne_zero (Units.ne_zero _) ?_) ?_` and prove the remaining obligations. Conclude with `Finset.prod_ne_zero_iff.2 fun _ _ => Finset.prod_ne_zero_iff.2 fun _ _ => Units.ne_zero _`. Conclude with `Finset.prod_ne_zero_iff.2 fun _ _ => inv_ne_zero (Units.ne_zero _)`.

Use `⟨fun PP _ => lowZero_rectOne _ _ _ _, fun _ => 1, fun PP => (topL_rectOne _ le_rfl hab).symm, fun PP => Subgroup.one_mem _, ?_⟩` and prove the remaining obligations. Use `L.P.H.one_mem using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `PP`. Conclude with `blockDiagonalExtendByOnePrimeField_one _ _`.
-/
theorem omegaG_rectOne {a b : ℕ} (hab : a ≤ b) (L : LevDat D.host.E ℂ a) (χj : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) :
    omegaG L χj (fun PP => rectOne (kP PP) b a) ≠ 0 := by
  unfold omegaG
  rw [dif_pos]
  · refine mul_ne_zero (mul_ne_zero (Units.ne_zero _) ?_) ?_
    · exact Finset.prod_ne_zero_iff.2 fun _ _ => Finset.prod_ne_zero_iff.2 fun _ _ => Units.ne_zero _
    · exact Finset.prod_ne_zero_iff.2 fun _ _ => inv_ne_zero (Units.ne_zero _)
  · refine ⟨fun PP _ => lowZero_rectOne _ _ _ _, fun _ => 1, fun PP => (topL_rectOne _ le_rfl hab).symm,
      fun PP => Subgroup.one_mem _, ?_⟩
    convert L.P.H.one_mem using 1
    funext PP
    exact blockDiagonalExtendByOnePrimeField_one _ _

/- English proof (translation)
Unfold `omegaQ`. Rewrite using `[dif_pos]`. Conclude with `Finset.prod_ne_zero_iff.2 fun _ _ => zpow_ne_zero _ (Units.ne_zero _)`. Introduce `PP _`. Use `⟨lowZero_rectOne _ _ _ _, ?_⟩` and prove the remaining obligations.

Rewrite using `[topL_rectOne _ ha hb, Matrix.det_one]`. Conclude with `isUnit_one`.
-/
theorem omegaQ_rectOne {a b r : ℕ} (ha : r ≤ a) (hb : r ≤ b) (Q : Finset (Pl D.host.E))
    (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ) : omegaQ Q r ξ k (fun PP => rectOne (kP PP) b a) ≠ 0 := by
  unfold omegaQ
  rw [dif_pos]
  · exact Finset.prod_ne_zero_iff.2 fun _ _ => zpow_ne_zero _ (Units.ne_zero _)
  · intro PP _
    refine ⟨lowZero_rectOne _ _ _ _, ?_⟩
    rw [topL_rectOne _ ha hb, Matrix.det_one]
    exact isUnit_one

/- English proof (translation)
Take `⟨hf, e, he, ⟨Tm, hTm⟩, hall⟩` from `h`. Establish `hinf` using `infPart_idemSum he`. Take `⟨K, hK, hC⟩` from `exists_nsmul_of_frMapO hS.1 hT.1 βS βT`. Take `⟨h1, h2⟩` from `placeModel_span_ne hf.1 hS hT (idemSum_mul_self he) he.2 hinf hTm (isSBHalf_of_red e _ (frMapO S T βS βT) (frMapO_add βS βT) (exists_den_frMapO hS.1.fg hT.1.fg βS βT) ⟨K, hK, fun t ht => hC t (infPart_of_half hinf ht)⟩ _ (fun y => omegaG LS χj y * omegaQ Q LS.r ξ 1 y) fun y y' h …`. Rewrite using `[omegaG_congr LS χj y y' fun PP hP => h PP (Finset.mem_union_left _ hP), omegaQ_congr Q LS.r ξ 1 y y' fun PP hP => h PP (Finset.mem_union_right _ hP)])`.

Rewrite `h1`, `h2` using `[← hall Tm hTm]`. Take `⟨c, hc⟩` from `Finsupp.mem_span_range_iff_exists_finsupp.1 h1`. Use `⟨?_, h2 ?_ fun hz => ?_, fun τ => ?_⟩` and prove the remaining obligations. Rewrite using `[← hc]`. Conclude with `GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hf.1.1 f₀ hf.2.theta _ c.support Subtype.val c fun i _ => i.2`.

Introduce and unpack `rfl`. Take `⟨⟨p, hp⟩, h2⟩` from `hf.2.norm`. Use `h2 p hp` as an intermediate fact. Simplify using `[nrm2] at this`. Take `⟨x, a1, a2, a3⟩` from `exists_point S T βS βT he`.

Use `congrFun hz x` as an intermediate fact. Rewrite `this` using `[if_pos ⟨a1, a2⟩, omegaG_congr LS χj _ (fun PP => rectOne (kP PP) _ _) fun PP hP => a3 PP (Finset.mem_union_left _ hP), omegaQ_congr Q LS.r ξ 1 _ (fun PP => rectOne (kP PP) _ _) fun PP hP => a3 PP (Finset.mem_union_right _ hP)]`. Conclude with `mul_ne_zero (omegaG_rectOne hr LS χj) (omegaQ_rectOne LS.hr (LS.hr.trans hr) Q ξ 1) this`. Rewrite using `[← hc]`. Conclude with `GlobalTheory.FockTranslate.isFockVacAt_sum D ψ θ S T hf.1.1 hf.2.inf f₀ hf.2.theta τ _ (hf.2.fock τ) _ c.support Subtype.val c fun i _ => i.2`.
-/
theorem stepVec_vac {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)} {LS : LevDat D.host.E ℂ S.rank}
    {χj ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {Q : Finset (Pl D.host.E)} {f₀ f : WO S T → ℂ}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (hr : S.rank ≤ T.rank)
    (h : IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT LS χj Q ξ f₀ f) :
    IsThetaFunO ψ S T f ∧ f ≠ 0 ∧ ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f := by
  classical
  obtain ⟨hf, e, he, ⟨Tm, hTm⟩, hall⟩ := h
  have hinf := infPart_idemSum he
  obtain ⟨K, hK, hC⟩ := exists_nsmul_of_frMapO hS.1 hT.1 βS βT
  obtain ⟨h1, h2⟩ := placeModel_span_ne hf.1 hS hT (idemSum_mul_self he) he.2 hinf hTm
    (isSBHalf_of_red e _ (frMapO S T βS βT) (frMapO_add βS βT) (exists_den_frMapO hS.1.fg hT.1.fg βS βT)
      ⟨K, hK, fun t ht => hC t (infPart_of_half hinf ht)⟩ _
      (fun y => omegaG LS χj y * omegaQ Q LS.r ξ 1 y) fun y y' h => by
        rw [omegaG_congr LS χj y y' fun PP hP => h PP (Finset.mem_union_left _ hP),
          omegaQ_congr Q LS.r ξ 1 y y' fun PP hP => h PP (Finset.mem_union_right _ hP)])
  rw [← hall Tm hTm] at h1 h2
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 h1
  refine ⟨?_, h2 ?_ fun hz => ?_, fun τ => ?_⟩
  · rw [← hc]
    exact GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hf.1.1 f₀ hf.2.theta _ c.support Subtype.val c fun i _ => i.2
  · rintro rfl
    obtain ⟨⟨p, hp⟩, h2⟩ := hf.2.norm
    have := h2 p hp
    simp [nrm2] at this
  · obtain ⟨x, a1, a2, a3⟩ := exists_point S T βS βT he
    have := congrFun hz x
    rw [if_pos ⟨a1, a2⟩, omegaG_congr LS χj _ (fun PP => rectOne (kP PP) _ _) fun PP hP =>
      a3 PP (Finset.mem_union_left _ hP), omegaQ_congr Q LS.r ξ 1 _ (fun PP => rectOne (kP PP) _ _) fun PP hP =>
      a3 PP (Finset.mem_union_right _ hP)] at this
    exact mul_ne_zero (omegaG_rectOne hr LS χj) (omegaQ_rectOne LS.hr (LS.hr.trans hr) Q ξ 1) this
  · rw [← hc]
    exact GlobalTheory.FockTranslate.isFockVacAt_sum D ψ θ S T hf.1.1 hf.2.inf f₀ hf.2.theta τ _ (hf.2.fock τ) _ c.support
      Subtype.val c fun i _ => i.2

/- English proof (translation)
Take `⟨n, hn, h0, h1⟩` from `hχ`. Take `⟨m, hm, -, h2⟩` from `hη`. Use `⟨n + m, by push_cast; rw [hn, hm]; ring, h0, fun θ hθ x hx hx' => ?_⟩` and prove the remaining obligations. Establish `hu : θ τ (infPart D (x : AE D)) ≠ 0` using `((x.isUnit.map (infPart D)).map (θ τ)).ne_zero`. Rewrite using `[MonoidHom.mul_apply, Circle.coe_mul, h1 θ hθ x hx hx', h2 θ hθ x hx hx', zpow_add₀ (div_ne_zero hu (by exact_mod_cast norm_ne_zero_iff.2 hu))]`.
-/
theorem hasInfExp_mul {χ η : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} {a b : ℚ} (hχ : HasInfExp D χ τ a)
    (hη : HasInfExp D η τ b) : HasInfExp D (χ * η) τ (a + b) := by
  obtain ⟨n, hn, h0, h1⟩ := hχ
  obtain ⟨m, hm, -, h2⟩ := hη
  refine ⟨n + m, by push_cast; rw [hn, hm]; ring, h0, fun θ hθ x hx hx' => ?_⟩
  have hu : θ τ (infPart D (x : AE D)) ≠ 0 := ((x.isUnit.map (infPart D)).map (θ τ)).ne_zero
  rw [MonoidHom.mul_apply, Circle.coe_mul, h1 θ hθ x hx hx', h2 θ hθ x hx hx',
    zpow_add₀ (div_ne_zero hu (by exact_mod_cast norm_ne_zero_iff.2 hu))]

/- English proof (translation)
Take `⟨n, hn, h0, h1⟩` from `hχ`. Use `⟨-n, by push_cast; rw [hn]; ring, h0, fun θ hθ x hx hx' => ?_⟩` and prove the remaining obligations. Rewrite using `[MonoidHom.inv_apply, Circle.coe_inv, h1 θ hθ x hx hx', zpow_neg]`.
-/
theorem hasInfExp_inv {χ : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} {a : ℚ} (hχ : HasInfExp D χ τ a) :
    HasInfExp D χ⁻¹ τ (-a) := by
  obtain ⟨n, hn, h0, h1⟩ := hχ
  refine ⟨-n, by push_cast; rw [hn]; ring, h0, fun θ hθ x hx hx' => ?_⟩
  rw [MonoidHom.inv_apply, Circle.coe_inv, h1 θ hθ x hx hx', zpow_neg]

/- English proof (translation)
Establish `key` using `GlobalTheory.HeckeFinTrivial.eq_one_of_trivial_on_finite D (c ^ n) ⟨h.1.1.pow n, fun x => by rw [MonoidHom.pow_apply, h.1.2 x, one_pow]⟩ (GlobalTheory.CharOrderFin.char_pow_eq_one_of_orderDvd D c χ h n ho)`. Use `⟨0, by simp, ⟨θ, hθ⟩, fun θ _ x hx _ => ?_⟩` and prove the remaining obligations. Take `⟨y, rfl⟩` from `GlobalTheory.IdeleDiv.exists_pow_eq_of_finPart_eq_one D n hn x hx`. Rewrite using `[zpow_zero, map_pow, show c y ^ n = 1 from key y, Circle.coe_one]`.
-/
theorem hasInfExp_of_order {θ : InfFam D} (hθ : IsInfFam θ) {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E}
    (h : ChrEq c χ) {n : ℕ} (hn : 0 < n) (ho : χ.OrderDvd n) (τ : D.what₂.Tau) : HasInfExp D c τ 0 := by
  have key := GlobalTheory.HeckeFinTrivial.eq_one_of_trivial_on_finite D (c ^ n)
    ⟨h.1.1.pow n, fun x => by rw [MonoidHom.pow_apply, h.1.2 x, one_pow]⟩
    (GlobalTheory.CharOrderFin.char_pow_eq_one_of_orderDvd D c χ h n ho)
  refine ⟨0, by simp, ⟨θ, hθ⟩, fun θ _ x hx _ => ?_⟩
  obtain ⟨y, rfl⟩ := GlobalTheory.IdeleDiv.exists_pow_eq_of_finPart_eq_one D n hn x hx
  rw [zpow_zero, map_pow, show c y ^ n = 1 from key y, Circle.coe_one]

/- English proof (translation)
Take `⟨n, hn, h⟩` from `h`. Conclude with `⟨fun τ => n (D.eTau τ), fun τ => hn _, fun k => (h k).trans (D.eTau.prod_comp _).symm⟩`.
-/
theorem hasInfQ_tau {χ : Formalism.L2.Host.HChar D.host.E} {a : D.R.Psi → ℚ}
    (h : χ.HasInfQ (Formalism.L2.Host.embPsi D.host) a) : χ.HasInfQ (tauE D) fun τ => a (D.eTau τ) := by
  obtain ⟨n, hn, h⟩ := h
  exact ⟨fun τ => n (D.eTau τ), fun τ => hn _, fun k => (h k).trans (D.eTau.prod_comp _).symm⟩

/- English proof (translation)
Take `⟨n, hn, ho⟩` from `hL.xi_fin t`. Establish `h1 : HasInfExp D (L.mu t ((k : ℕ) + 1)) τ (-(D.hc τ).e k)`. Use `hasInfExp_mul (GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hL.mu0 k) (hasInfQ_tau (L.C.isMu0 k).inf) τ) (hasInfExp_of_order hθ (hL.xi t) hn ho τ)` as an intermediate fact. Rewrite `this` using `[add_zero, Formalism.L2.Host.eExp, Equiv.symm_apply_apply]`. Then use the resulting hypothesis. Establish `h2 : HasInfExp D L.eta τ (1 / 2)` using `GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hL.eta (hasInfQ_tau (a := fun _ => 1 / 2) ⟨_, fun _ => by norm_num, L.C.isEta.inf⟩) τ`.

Establish `h3` using `hasInfExp_mul h1 (hasInfExp_inv h2)`. Unfold `Lift.chrStep expS expT`. Distinguish the cases in `hk : Even (k : ℕ)`. Rewrite using `[if_pos hk.add_one, if_pos hk, if_pos hk, sub_zero, sub_eq_add_neg]`. Conclude with `⟨h3, h1⟩`.

Rewrite using `[if_neg (by rwa [Nat.odd_add_one, Nat.not_odd_iff_even]), if_neg hk, if_neg hk, sub_zero, sub_eq_add_neg]`. Conclude with `⟨h1, h3⟩`.
-/
theorem chrStep_exp {T : Type} {L : LevCh D T} {μ0 : T} (hL : L.Is μ0) {θ : InfFam D} (hθ : IsInfFam θ) (t : T)
    (k : Fin D.R.m) (τ : D.what₂.Tau) :
    HasInfExp D (Lift.chrStep (L.mu t) L.eta ((k : ℕ) + 1)).1 τ (expS D k τ) ∧
      HasInfExp D (Lift.chrStep (L.mu t) L.eta ((k : ℕ) + 1)).2 τ (expT D k τ) := by
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  have h1 : HasInfExp D (L.mu t ((k : ℕ) + 1)) τ (-(D.hc τ).e k) := by
    have := hasInfExp_mul (GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hL.mu0 k) (hasInfQ_tau (L.C.isMu0 k).inf) τ)
      (hasInfExp_of_order hθ (hL.xi t) hn ho τ)
    rwa [add_zero, Formalism.L2.Host.eExp, Equiv.symm_apply_apply] at this
  have h2 : HasInfExp D L.eta τ (1 / 2) :=
    GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hL.eta (hasInfQ_tau (a := fun _ => 1 / 2) ⟨_, fun _ => by norm_num, L.C.isEta.inf⟩) τ
  have h3 := hasInfExp_mul h1 (hasInfExp_inv h2)
  unfold Lift.chrStep expS expT
  by_cases hk : Even (k : ℕ)
  · rw [if_pos hk.add_one, if_pos hk, if_pos hk, sub_zero, sub_eq_add_neg]
    exact ⟨h3, h1⟩
  · rw [if_neg (by rwa [Nat.odd_add_one, Nat.not_odd_iff_even]), if_neg hk, if_neg hk, sub_zero, sub_eq_add_neg]
    exact ⟨h1, h3⟩

/- English proof (translation)
Rewrite using `[D.sp.Y_rank _ (min_le_right _ _), min_eq_left hj]`. Both sides reduce to the same expression.
-/
theorem rank_Yc {j : ℕ} (hj : j ≤ D.R.m) : (Yc D j).rank = D.R.r + j * D.R.t := by
  rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left hj]; rfl

/- English proof (translation)
Introduce `D G _ _ Pl0 T A Ks _ _ _ R hL hθ hωY hωX hvY hvX`. Use `⟨fun t k hk => ⟨⟨_, _, hωY t k hk, chrStep_exp hL hθ t k⟩, ?_⟩, fun t k hk => ⟨⟨_, _, hωX t, fun τ => ?_⟩, ?_⟩⟩` and prove the remaining obligations. Take `⟨a, b, c⟩` from `stepVec_vac (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βY k k.2)) (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βY _ hk)) (by rw [rank_Yc k.2.le, rank_Yc hk.le]; nlinarith) (hvY t k hk)`. Conclude with `⟨a, b, c⟩`. Use `chrStep_exp hL hθ t k τ` as an intermediate fact.

Rewrite `this` using `[show (k : ℕ) + 1 = D.R.m by have := k.2; omega]`. Then use the resulting hypothesis. Take `⟨a, b, c⟩` from `stepVec_vac (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βY (D.R.m - 1) (hk ▸ k.2))) (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hL.βX) (by`. Rewrite using `[rank_Yc (Nat.sub_le _ _), D.sp.X'_rank]`. Conclude with `Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) _) (hvX t)`. Conclude with `⟨a, b, c⟩`.
-/
theorem stepsOK : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.toLevCh.Is A.μ0 → IsInfFam R.θ → R.chain_ωY → R.chain_ωX → R.chain_vY → R.chain_vX → StepsOK R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL hθ hωY hωX hvY hvX
  refine ⟨fun t k hk => ⟨⟨_, _, hωY t k hk, chrStep_exp hL hθ t k⟩, ?_⟩, fun t k hk => ⟨⟨_, _, hωX t, fun τ => ?_⟩, ?_⟩⟩
  · obtain ⟨a, b, c⟩ := stepVec_vac (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βY k k.2)) (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βY _ hk))
      (by rw [rank_Yc k.2.le, rank_Yc hk.le]; nlinarith) (hvY t k hk)
    exact ⟨a, b, c⟩
  · have := chrStep_exp hL hθ t k τ
    rwa [show (k : ℕ) + 1 = D.R.m by have := k.2; omega] at this
  · obtain ⟨a, b, c⟩ := stepVec_vac (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βY (D.R.m - 1) (hk ▸ k.2)))
      (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hL.βX) (by
        rw [rank_Yc (Nat.sub_le _ _), D.sp.X'_rank]
        exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) _) (hvX t)
    exact ⟨a, b, c⟩

end GlobalTheory.Chain.StepVac

end
