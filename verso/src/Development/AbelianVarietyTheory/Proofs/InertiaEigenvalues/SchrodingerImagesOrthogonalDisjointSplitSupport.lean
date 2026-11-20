import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaPairingInvariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DatP
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerIntertwinerSchwartzBruhatIsTheta
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddNsmulResidueAssoc
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

noncomputable section

namespace GlobalTheory.BadOrth

variable {D : D7} {S T : HSp D}

/- English proof (translation)
Unfold `thetaIP GlobalTheory.Ker.ipO`. Use `congr 1`. Use function extensionality and compare the values at `w`. Rewrite using `[mul_comm]`. Both sides reduce to the same expression.
-/
theorem thetaIP_eq_ipO (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (f g : WO S T → ℂ) :
    thetaIP μ 𝓕 f g = GlobalTheory.Ker.ipO μ 𝓕 g f := by
  unfold thetaIP GlobalTheory.Ker.ipO
  congr 1; funext w; rw [mul_comm]; rfl

/- English proof (translation)
Rewrite using `[thetaIP_eq_ipO]`. Establish `h` using `GlobalTheory.Size.ipO_heisO hψ hμ.1 hμ.2.1 hg hf y`. Rewrite `h` using `[hfy, hgy, GlobalTheory.Size.ipO_smul_left, GlobalTheory.Size.ipO_smul_right, ← mul_assoc]`. Assume the negation of the conclusion as `hX`. Establish `h1 : b * starRingEnd ℂ a = 1`.

Use `mul_right_cancel₀ hX (h.trans (one_mul _).symm)` as an intermediate fact. Conclude with `this`. Establish `h2 : starRingEnd ℂ a * a = 1`. Rewrite using `[Complex.conj_mul', ha]`. Evaluate the numerical expressions.

Apply `hab` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.
-/
theorem thetaInner_eq_zero_of_eigen {ψ : AddChar (AF D.host.F) ℂ} {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hψ : IsStdChar D ψ (-1)) (hμ : IsCovolOne (ratL T S) μ 𝓕) {f g : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) (y : WO S T) {a b : ℂ} (ha : ‖a‖ = 1) (hab : a ≠ b)
    (hfy : heisO ψ S T y f = a • f) (hgy : heisO ψ S T y g = b • g) : thetaIP μ 𝓕 f g = 0 := by
  rw [thetaIP_eq_ipO]
  have h := GlobalTheory.Size.ipO_heisO hψ hμ.1 hμ.2.1 hg hf y
  rw [hfy, hgy, GlobalTheory.Size.ipO_smul_left, GlobalTheory.Size.ipO_smul_right, ← mul_assoc] at h
  by_contra hX
  have h1 : b * starRingEnd ℂ a = 1 := by
    have := mul_right_cancel₀ hX (h.trans (one_mul _).symm)
    exact this
  have h2 : starRingEnd ℂ a * a = 1 := by
    rw [Complex.conj_mul', ha]; norm_num
  apply hab
  calc a = (b * starRingEnd ℂ a) * a := by rw [h1, one_mul]
    _ = b := by rw [mul_assoc, h2, mul_one]

/- English proof (translation)
Establish `hint : ∀ i ∈ Q, ∀ j ∈ Q, Integrable (fun w => star (f i w) * g j w) (μ.restrict 𝓕)`. Introduce `i hi j hj`. Use `GlobalTheory.Size.integrableOn_mul_conj hψ hμ.1 hμ.2.1 (hg j hj) (hf i hi)` as an intermediate fact. Use `this.congr (ae_of_all _ fun w => ?_)` and prove the remaining obligations. Simplify using `only [mul_comm (g j w)]`.

Both sides reduce to the same expression. Unfold `thetaIP`. Establish `e : (fun w => star ((∑ i ∈ Q, f i) w) * (∑ j ∈ Q, g j) w) = fun w => ∑ i ∈ Q, ∑ j ∈ Q, star (f i w) * g j w`. Use function extensionality and compare the values at `w`. Simplify using `only [Finset.sum_apply, star_sum, Finset.sum_mul, Finset.mul_sum]`.

Conclude with `Finset.sum_comm`. Rewrite using `[e, integral_finset_sum _ fun i hi => integrable_finset_sum _ fun j hj => hint i hi j hj]`. Conclude with `Finset.sum_congr rfl fun i hi => integral_finset_sum _ fun j hj => hint i hi j hj`.
-/
theorem thetaInner_sum_sum {ψ : AddChar (AF D.host.F) ℂ} {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hψ : IsStdChar D ψ (-1)) (hμ : IsCovolOne (ratL T S) μ 𝓕) {ι : Type} (Q : Finset ι) (f g : ι → WO S T → ℂ)
    (hf : ∀ i ∈ Q, IsThetaFunO ψ S T (f i)) (hg : ∀ i ∈ Q, IsThetaFunO ψ S T (g i)) :
    thetaIP μ 𝓕 (∑ i ∈ Q, f i) (∑ j ∈ Q, g j) = ∑ i ∈ Q, ∑ j ∈ Q, thetaIP μ 𝓕 (f i) (g j) := by
  have hint : ∀ i ∈ Q, ∀ j ∈ Q, Integrable (fun w => star (f i w) * g j w) (μ.restrict 𝓕) := by
    intro i hi j hj
    have := GlobalTheory.Size.integrableOn_mul_conj hψ hμ.1 hμ.2.1 (hg j hj) (hf i hi)
    refine this.congr (ae_of_all _ fun w => ?_)
    simp only [mul_comm (g j w)]; rfl
  unfold thetaIP
  have e : (fun w => star ((∑ i ∈ Q, f i) w) * (∑ j ∈ Q, g j) w) =
      fun w => ∑ i ∈ Q, ∑ j ∈ Q, star (f i w) * g j w := by
    funext w
    simp only [Finset.sum_apply, star_sum, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  rw [e, integral_finset_sum _ fun i hi => integrable_finset_sum _ fun j hj => hint i hi j hj]
  exact Finset.sum_congr rfl fun i hi => integral_finset_sum _ fun j hj => hint i hi j hj

end GlobalTheory.BadOrth

namespace GlobalTheory.BadOrth

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in

/- English proof (translation)
Introduce `D S T ΛS ΛT hS hT a ha k hk`. Take `⟨R, hR, hRm⟩` from `GlobalTheory.LatFinMod.latO_finite_mod D S T ΛS ΛT hS.1.fg hT.1.fg (fun _ => True) (k * k) (Nat.mul_pos hk hk)`. Establish `half' : ∀ {b : AE D} {u : WO S T}, IsHalf b u ↔ b • u = u` using `fun {b u} => (PlaceModel.isHalf_iff S T).trans (PlaceModel.mem_half S T)`. Set `r : AE D` to `algebraMap D.host.F (AE D) ((k : D.host.F)⁻¹)`. Establish `hrk : r * (k : AE D) = 1`.

Rewrite using `[← map_natCast (algebraMap D.host.F (AE D)) k, ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hk.ne'), map_one]`. Establish `hrkz : ∀ z : WO S T, r • (k • z) = z` using `fun z => by`. Rewrite using `[← Nat.cast_smul_eq_nsmul (AE D) k z, smul_smul, hrk, one_smul]`. Use `⟨hR.toFinset.image (fun z => a • (r • z)), fun c hc => ?_, fun s hs hks => ?_⟩` and prove the remaining obligations. Take `⟨z, -, rfl⟩` from `Finset.mem_image.1 hc`.

Conclude with `half'.2 (by rw [smul_smul, ha])`. Take `⟨z, hz, u, hu, hzu⟩` from `hRm (k • s) hks`. Use `⟨a • (r • z), Finset.mem_image_of_mem _ (hR.mem_toFinset.2 hz), a • u, PlaceModelSum.idem_smul_latO ha hu, half'.2 (by rw [smul_smul, ha]), ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem finCosets : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ a : AE D, a * a = a → ∀ k : ℕ, 0 < k → ∃ C : Finset (WO S T), (∀ c ∈ C, IsHalf a c) ∧ ∀ s : WO S T, IsHalf a s → k • s ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) → ∃ c ∈ C, ∃ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), IsHalf a u ∧ s = c + k • u := by
  intro D S T ΛS ΛT hS hT a ha k hk
  obtain ⟨R, hR, hRm⟩ := GlobalTheory.LatFinMod.latO_finite_mod D S T ΛS ΛT hS.1.fg hT.1.fg (fun _ => True) (k * k)
    (Nat.mul_pos hk hk)
  have half' : ∀ {b : AE D} {u : WO S T}, IsHalf b u ↔ b • u = u := fun {b u} =>
    (PlaceModel.isHalf_iff S T).trans (PlaceModel.mem_half S T)
  let r : AE D := algebraMap D.host.F (AE D) ((k : D.host.F)⁻¹)
  have hrk : r * (k : AE D) = 1 := by
    rw [← map_natCast (algebraMap D.host.F (AE D)) k, ← map_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 hk.ne'), map_one]
  have hrkz : ∀ z : WO S T, r • (k • z) = z := fun z => by
    rw [← Nat.cast_smul_eq_nsmul (AE D) k z, smul_smul, hrk, one_smul]
  refine ⟨hR.toFinset.image (fun z => a • (r • z)), fun c hc => ?_, fun s hs hks => ?_⟩
  · obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 hc
    exact half'.2 (by rw [smul_smul, ha])
  · obtain ⟨z, hz, u, hu, hzu⟩ := hRm (k • s) hks
    refine ⟨a • (r • z), Finset.mem_image_of_mem _ (hR.mem_toFinset.2 hz), a • u,
      PlaceModelSum.idem_smul_latO ha hu, half'.2 (by rw [smul_smul, ha]), ?_⟩
    calc s = a • (r • (k • s)) := by rw [hrkz, half'.1 hs]
      _ = a • (r • z) + k • (a • u) := by rw [hzu, smul_add, smul_add, mul_smul, hrkz, smul_comm a k u]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in

/- English proof (translation)
Introduce `D ψ S T ΛS ΛT hψ hS hT e he k hk x hx hxL`. Establish `hdual` using `(GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1`. Establish `half' : ∀ {a : AE D} {u : WO S T}, IsHalf a u ↔ a • u = u` using `fun {a u} => (PlaceModel.isHalf_iff S T).trans (PlaceModel.mem_half S T)`. Establish `hce : PlaceModelSum.IsOrthSum (cA D e)` using `⟨Unit, {()}, fun _ => cA D e, fun _ _ => PlaceModelSum.isSplitIdem_cA he, fun i _ j _ h => absurd (Subsingleton.elim j i) h, by rw [Finset.sum_singleton]⟩`. Set `r : AE D` to `algebraMap D.host.F (AE D) ((k : D.host.F)⁻¹)`.

Establish `hrk : r * (k : AE D) = 1`. Rewrite using `[← map_natCast (algebraMap D.host.F (AE D)) k, ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hk.ne'), map_one]`. Establish `hcr : cA D r = r`. Establish `h1 : cA D r * (k : AE D) = 1` using `by rw [← map_natCast (cA D) k, ← map_mul, hrk, map_one]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hnat : ∀ z : WO S T, k • z = (k : AE D) • z` using `fun z => (Nat.cast_smul_eq_nsmul (AE D) k z).symm`. Establish `hrkz : ∀ z : WO S T, r • (k • z) = z` using `fun z => by rw [hnat, smul_smul, hrk, one_smul]`. Establish `hkrz : ∀ z : WO S T, k • (r • z) = z` using `fun z => by rw [hnat, smul_smul, mul_comm, hrk, one_smul]`. Establish `hΛΛ : ∀ y ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), IsHalf e y → ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), ψ (symplO S T u y) = 1`. Introduce `y hy hye u hu`.

Establish `hinf : y.map (infPart D) = 0`. Use `hce.conj.infPart_half ((PlaceModel.isHalf_iff S T).1 ?_)` and prove the remaining obligations. Rewrite using `[cA_cA]`. Conclude with `hye`. Rewrite using `[PlaceModel.symplO_skew, AddChar.map_neg_eq_inv, (hdual y hinf).1 hy u hu, inv_one]`.

Assume the negation of the conclusion as `hno`. Use `push_neg at hno`. Establish `hrx : IsHalf (cA D e) (r • x)` using `half'.2 (by rw [smul_comm, half'.1 hx])`. Establish `hmem` using `hce.mem_of_dual hdual (r • x) ((PlaceModel.isHalf_iff S T).1 hrx) (fun y hy => by`. Take `⟨hy1, hy2⟩` from `AddSubgroup.mem_inf.1 hy`.

Establish `hye : IsHalf e y`. Use `(PlaceModel.isHalf_iff S T).2 hy2` as an intermediate fact. Rewrite `this` using `[cA_cA]`. Then use the resulting hypothesis. Establish `hrye : IsHalf e (r • y)` using `half'.2 (by rw [smul_comm, half'.1 hye])`. Establish `h1` using `hno (r • y) hrye (fun u hu => by`.

Rewrite using `[← hcr, ← PlaceModel.symplO_smul S T, hrkz]`. Conclude with `hΛΛ y hy1 hye u hu)`. Rewrite using `[PlaceModel.symplO_smul S T, hcr])` and apply the resulting hypothesis. Take `⟨h1, h2⟩` from `AddSubgroup.mem_inf.1 hmem`. Conclude with `hxL (r • x) h1 ((PlaceModel.isHalf_iff S T).2 h2) (hkrz x).symm`.
-/
theorem separate : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ e : AE D, IsSplitIdem D e → ∀ k : ℕ, 0 < k → ∀ x : WO S T, IsHalf (cA D e) x → (∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), IsHalf (cA D e) u → x ≠ k • u) → ∃ y : WO S T, IsHalf e y ∧ (∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), ψ (symplO S T (k • u) y) = 1) ∧ ψ (symplO S T x y) ≠ 1 := by
  intro D ψ S T ΛS ΛT hψ hS hT e he k hk x hx hxL
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have half' : ∀ {a : AE D} {u : WO S T}, IsHalf a u ↔ a • u = u := fun {a u} =>
    (PlaceModel.isHalf_iff S T).trans (PlaceModel.mem_half S T)
  have hce : PlaceModelSum.IsOrthSum (cA D e) :=
    ⟨Unit, {()}, fun _ => cA D e, fun _ _ => PlaceModelSum.isSplitIdem_cA he,
      fun i _ j _ h => absurd (Subsingleton.elim j i) h, by rw [Finset.sum_singleton]⟩

  let r : AE D := algebraMap D.host.F (AE D) ((k : D.host.F)⁻¹)
  have hrk : r * (k : AE D) = 1 := by
    rw [← map_natCast (algebraMap D.host.F (AE D)) k, ← map_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 hk.ne'), map_one]
  have hcr : cA D r = r := by
    have h1 : cA D r * (k : AE D) = 1 := by rw [← map_natCast (cA D) k, ← map_mul, hrk, map_one]
    calc cA D r = cA D r * ((k : AE D) * r) := by rw [mul_comm (k : AE D) r, hrk, mul_one]
      _ = r := by rw [← mul_assoc, h1, one_mul]
  have hnat : ∀ z : WO S T, k • z = (k : AE D) • z := fun z => (Nat.cast_smul_eq_nsmul (AE D) k z).symm
  have hrkz : ∀ z : WO S T, r • (k • z) = z := fun z => by rw [hnat, smul_smul, hrk, one_smul]
  have hkrz : ∀ z : WO S T, k • (r • z) = z := fun z => by rw [hnat, smul_smul, mul_comm, hrk, one_smul]

  have hΛΛ : ∀ y ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), IsHalf e y → ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), ψ (symplO S T u y) = 1 := by
    intro y hy hye u hu
    have hinf : y.map (infPart D) = 0 := by
      refine hce.conj.infPart_half ((PlaceModel.isHalf_iff S T).1 ?_)
      rw [cA_cA]; exact hye
    rw [PlaceModel.symplO_skew, AddChar.map_neg_eq_inv, (hdual y hinf).1 hy u hu, inv_one]
  by_contra hno
  push_neg at hno
  have hrx : IsHalf (cA D e) (r • x) := half'.2 (by rw [smul_comm, half'.1 hx])
  have hmem := hce.mem_of_dual hdual (r • x) ((PlaceModel.isHalf_iff S T).1 hrx) (fun y hy => by
    obtain ⟨hy1, hy2⟩ := AddSubgroup.mem_inf.1 hy
    have hye : IsHalf e y := by
      have := (PlaceModel.isHalf_iff S T).2 hy2
      rwa [cA_cA] at this
    have hrye : IsHalf e (r • y) := half'.2 (by rw [smul_comm, half'.1 hye])
    have h1 := hno (r • y) hrye (fun u hu => by
      rw [← hcr, ← PlaceModel.symplO_smul S T, hrkz]
      exact hΛΛ y hy1 hye u hu)
    rwa [PlaceModel.symplO_smul S T, hcr])
  obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.1 hmem
  exact hxL (r • x) h1 ((PlaceModel.isHalf_iff S T).2 h2) (hkrz x).symm

open GlobalTheory.PlaceModel GlobalTheory.PlaceModelSum

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in

/- English proof (translation)
Introduce `D ψ S T ΛS ΛT Pf ea e f₀ Tm μ 𝓕 hψ hS hT hIdem hsplit hee hf₀ hvac hTm hμ Φ₁ Φ₂ hΦ₁ hΦ₂ hdisj Ω hΩt hΩc`. Use `set Λ := (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) with hΛ`. Establish `hea : IsOrthSum ea` using `isOrthSum_of_isIdemSum hIdem`. Establish `hcea : cA D ea * cA D ea = cA D ea` using `by rw [← map_mul, hea.idem]`. Establish `hinf : infPart D (cA D ea) = 0` using `hea.conj.infPart_eq`.

Establish `hce1 : cA D e * cA D e = cA D e` using `by rw [← map_mul, hsplit.1]`. Establish `hecea : e * cA D ea = 0` using `by rw [← hee, mul_assoc, hIdem.2, mul_zero]`. Establish `hcecea : cA D ea * cA D e = cA D e` using `by rw [← map_mul, mul_comm, hee]`. Establish `half' : ∀ {a : AE D} {u : WO S T}, IsHalf a u ↔ a • u = u` using `fun {a u} => (isHalf_iff S T).trans (mem_half S T)`. Establish `hθ : ∀ Φ, IsSBHalf (cA D ea) Λ Φ → IsThetaFunO ψ S T (Tm Φ)` using `fun Φ hΦ => GlobalTheory.SchrTheta.isTheta_placeModel D ψ hψ S T ΛS ΛT hS hT _ hcea hinf f₀ hf₀ Tm hTm Φ hΦ`.

Take `⟨hs₁, k₁, hk₁, hi₁, hl₁⟩` from `hΦ₁`. Take `⟨hs₂, k₂, hk₂, hi₂, hl₂⟩` from `hΦ₂`. Establish `hk : 0 < k₁ * k₂` using `Nat.mul_pos hk₁ hk₂`. Establish `hhalfU : ∀ (m : ℕ) {a : AE D} {u : WO S T}, u ∈ Λ → IsHalf a u → m • u ∈ Λ ∧ IsHalf a (m • u)` using `fun m a u hu hue => ⟨AddSubgroup.nsmul_mem _ hu m, half'.2 (by rw [smul_comm, half'.1 hue])⟩`. Establish `hinv₁ : ∀ u ∈ Λ, IsHalf (cA D ea) u → ∀ t, Φ₁ (t + (k₁ * k₂) • u) = Φ₁ t` using `fun u hu hue t => by`.

Rewrite using `[mul_smul]`. Conclude with `hi₁ _ (hhalfU k₂ hu hue).1 (hhalfU k₂ hu hue).2 t`. Establish `hinv₂ : ∀ u ∈ Λ, IsHalf (cA D ea) u → ∀ t, Φ₂ (t + (k₁ * k₂) • u) = Φ₂ t` using `fun u hu hue t => by`. Rewrite using `[mul_comm, mul_smul]`. Conclude with `hi₂ _ (hhalfU k₁ hu hue).1 (hhalfU k₁ hu hue).2 t`.

Establish `hsup₁ : ∀ t, Φ₁ t ≠ 0 → IsHalf (cA D ea) t ∧ (k₁ * k₂) • t ∈ Λ` using `fun t ht => ⟨hs₁ t ht, by rw [mul_comm, mul_smul]; exact AddSubgroup.nsmul_mem _ (hl₁ t ht) _⟩`. Establish `hsup₂ : ∀ t, Φ₂ t ≠ 0 → IsHalf (cA D ea) t ∧ (k₁ * k₂) • t ∈ Λ` using `fun t ht => ⟨hs₂ t ht, by rw [mul_smul]; exact AddSubgroup.nsmul_mem _ (hl₂ t ht) _⟩`. Generalize the expression as in `k₁ * k₂ = k at hk hinv₁ hinv₂ hsup₁ hsup₂`. Set `L : AddSubgroup (WO S T)` to `AddSubgroup.map (nsmulAddMonoidHom k) (Λ ⊓ half S T (cA D e))`. Establish `memL : ∀ u ∈ Λ, IsHalf (cA D e) u → k • u ∈ L` using `fun u hu hue => AddSubgroup.mem_map.2 ⟨u, AddSubgroup.mem_inf.2 ⟨hu, (isHalf_iff S T).1 hue⟩, rfl⟩`.

Establish `memL' : ∀ x ∈ L, ∃ u ∈ Λ, IsHalf (cA D e) u ∧ x = k • u` using `fun x hx => by`. Take `⟨u, hu, rfl⟩` from `AddSubgroup.mem_map.1 hx`. Conclude with `⟨u, (AddSubgroup.mem_inf.1 hu).1, (isHalf_iff S T).2 (AddSubgroup.mem_inf.1 hu).2, rfl⟩`. Establish `hceu : ∀ u ∈ Λ, cA D e • u ∈ Λ ∧ IsHalf (cA D e) (cA D e • u)` using `fun u hu => ⟨idem_smul_latO hce1 hu, half'.2 (by rw [smul_smul, hce1])⟩`. Take `⟨C, hCh, hC⟩` from `finCosets D S T ΛS ΛT hS hT (cA D e) hce1 k hk`.

Set `mkL : WO S T → WO S T ⧸ L` to `QuotientAddGroup.mk`. Set `Q : Finset (WO S T ⧸ L)` to `C.image mkL`. Set `P : (WO S T → ℂ) → (WO S T ⧸ L) → WO S T → ℂ` to `fun Φ q t => if mkL (cA D e • t) = q then Φ t else 0`. Establish `hcos : ∀ t, IsHalf (cA D ea) t → k • t ∈ Λ → ∃ c ∈ C, ∃ u ∈ Λ, IsHalf (cA D e) u ∧ cA D e • t = c + k • u` using `fun t _ htk => hC _ (half'.2 (by rw [smul_smul, hce1])) (by rw [smul_comm]; exact idem_smul_latO hce1 htk)`. Establish `hcover : ∀ Φ : WO S T → ℂ, (∀ t, Φ t ≠ 0 → IsHalf (cA D ea) t ∧ k • t ∈ Λ) → Φ = ∑ q ∈ Q, P Φ q`.

Introduce `Φ hsup`. Use function extensionality and compare the values at `t`. Rewrite using `[Finset.sum_apply]`. Distinguish the cases in `h0 : Φ t = 0`. Rewrite using `[h0]; exact (Finset.sum_eq_zero fun q _ => by simp only [P, h0, ite_self]).symm`.

Establish `hh` using `hcos t (hsup t h0).1 (hsup t h0).2`. Take `⟨c, hc, u, hu, hh⟩` from `hh`. Take `⟨hue, htc⟩` from `hh`. Establish `hq : mkL (cA D e • t) = mkL c`. Rewrite using `[htc]`.

Use `QuotientAddGroup.eq.2 ?_` and prove the remaining obligations. Establish `: -(c + k • u) + c = -(k • u)` using `by abel`. Rewrite using `[this]`. Conclude with `neg_mem (memL u hu hue)`. Rewrite using `[Finset.sum_eq_single_of_mem (mkL c) (Finset.mem_image_of_mem _ hc) fun q _ hq' => by`.

Simplify using `only [P, hq, if_neg (Ne.symm hq')]]`. Simplify using `only [P, hq, if_true]`. Establish `hSB : ∀ Φ : WO S T → ℂ, (∀ t, Φ t ≠ 0 → IsHalf (cA D ea) t ∧ k • t ∈ Λ) → (∀ u ∈ Λ, IsHalf (cA D ea) u → ∀ t, Φ (t + k • u) = Φ t) → ∀ q, IsSBHalf (cA D ea) Λ (P Φ q)`. Introduce `Φ hsup hinv q`. Establish `hne : ∀ t, P Φ q t ≠ 0 → Φ t ≠ 0` using `fun t ht h0 => ht (by simp only [P, h0, ite_self])`.

Use `⟨fun t ht => (hsup t (hne t ht)).1, k, hk, fun u hu hue t => ?_, fun t ht => (hsup t (hne t ht)).2⟩` and prove the remaining obligations. Establish `hkey : mkL (cA D e • (t + k • u)) = mkL (cA D e • t)`. Simplify using `only [mkL]`. Rewrite using `[smul_add, smul_comm, QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff _).2 (memL _ (hceu u hu).1 (hceu u hu).2), add_zero]`. Simplify using `only [P, hkey, hinv u hu hue t]`.

Establish `hP₁` using `hSB Φ₁ hsup₁ hinv₁`. Establish `hP₂` using `hSB Φ₂ hsup₂ hinv₂`. Establish `hPne : ∀ Φ q t, P Φ q t ≠ 0 → mkL (cA D e • t) = q ∧ Φ t ≠ 0` using `fun Φ q t h => by`. Distinguish the cases in `hq : mkL (cA D e • t) = q`. Use `⟨hq, fun h0 => h ?_⟩` and prove the remaining obligations.

Simplify using `only [P, hq, h0, if_true]`. Conclude with `absurd (by simp only [P, hq, if_false]) h`. Establish `hhalf_ce : ∀ t, IsHalf (cA D ea) t → (e + cA D e) • t = cA D e • t` using `fun t ht => by`. Establish `h0 : e • t = 0` using `by rw [← half'.1 ht, smul_smul, hecea, zero_smul]`. Rewrite using `[add_smul, h0, zero_add]`.

Establish `hdisjP : ∀ q, P Φ₁ q = 0 ∨ P Φ₂ q = 0`. Introduce `q`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Take `⟨t, ht⟩` from `Function.ne_iff.1 hne.1`.

Take `⟨t', ht'⟩` from `Function.ne_iff.1 hne.2`. Take `⟨hq1, h1⟩` from `hPne Φ₁ q t ht`. Take `⟨hq2, h2⟩` from `hPne Φ₂ q t' ht'`. Establish `hL : -(cA D e • t) + cA D e • t' ∈ L` using `QuotientAddGroup.eq.1 (hq1.trans hq2.symm)`. Take `⟨w, hw, hwe, hwk⟩` from `memL' _ hL`.

Establish `hwea : IsHalf (cA D ea) (-w)` using `half'.2 (by rw [smul_neg, ← half'.1 hwe, smul_smul, hcecea])`. Establish `h2' : Φ₂ (t' + k • (-w)) ≠ 0` using `by rw [hinv₂ _ (neg_mem hw) hwea]; exact h2`. Establish `hw' : cA D e • (k • -w) = -(k • w)` using `by rw [smul_comm, smul_neg, half'.1 hwe, smul_neg]`. Establish `hM : (e + cA D e) • t = (e + cA D e) • (t' + k • (-w))`. Rewrite using `[hhalf_ce t (hsup₁ t h1).1, hhalf_ce _ (hsup₂ _ h2').1, smul_add, hw', ← hwk]`.

Normalize the expressions using the abelian group laws. Conclude with `hdisj t (t' + k • (-w)) (fun a b => congrFun (congrFun hM a) b) h1 h2'`. Establish `hmod : ∀ y, IsHalf e y → ∀ Φ, IsSBHalf (cA D ea) Λ Φ → Tm (fun t => ψ (symplO S T t y) * Φ t) = heisO ψ S T y (Tm Φ)` using `fun y hy Φ hΦ => hTm.modul Φ hΦ y (by rw [cA_cA]; exact half'.2 (by rw [← half'.1 hy, smul_smul, mul_comm ea e, hee]))`. Establish `heig : ∀ Φ q (c : WO S T), mkL c = q → ∀ y, IsHalf e y → (∀ u ∈ Λ, ψ (symplO S T (k • u) y) = 1) → (fun t => ψ (symplO S T t y) * P Φ q t) = ψ (symplO S T c y) • P Φ q`. Introduce `Φ q c hc y hy hyL`.

Use function extensionality and compare the values at `t`. Rewrite using `[Pi.smul_apply, smul_eq_mul]`. Distinguish the cases in `hq : mkL (cA D e • t) = q`. Establish `hL : -(cA D e • t) + c ∈ L` using `QuotientAddGroup.eq.1 (hq.trans hc.symm)`. Take `⟨w, hw, hwe, hwk⟩` from `memL' _ hL`.

Establish `h1 : symplO S T t y = symplO S T (cA D e • t) y` using `by rw [symplO_smul S T, cA_cA, half'.1 hy]`. Establish `h2 : cA D e • t = c + k • -w` using `by rw [smul_neg, ← hwk]; abel`. Rewrite using `[h1, h2, symplO_add_left S T, AddChar.map_add_eq_mul, hyL _ (neg_mem hw), mul_one]`. Simplify using `only [P, hq, if_false, mul_zero]`. Establish `hsep : ∀ q ∈ Q, ∀ q' ∈ Q, q ≠ q' → ∃ y, IsHalf e y ∧ ∃ a b : ℂ, ‖a‖ = 1 ∧ a ≠ b ∧ (∀ Φ, (fun t => ψ (symplO S T t y) * P Φ q t) = a • P Φ q) ∧ (∀ Φ, (fun t => ψ (symplO S T t y) * P Φ q' t) = b • P Φ q')`.

Introduce `q hq q' hq' hne`. Take `⟨c, hc, rfl⟩` from `Finset.mem_image.1 hq`. Take `⟨c', hc', rfl⟩` from `Finset.mem_image.1 hq'`. Establish `hx : IsHalf (cA D e) (c - c')` using `half'.2 (by rw [smul_sub, half'.1 (hCh c hc), half'.1 (hCh c' hc')])`. Establish `hxL : ∀ u ∈ Λ, IsHalf (cA D e) u → c - c' ≠ k • u` using `fun u hu hue h => hne (QuotientAddGroup.eq.2 (by`.

Establish `: -c + c' = -(k • u)` using `by rw [← h]; abel`. Rewrite using `[this]`. Conclude with `neg_mem (memL u hu hue)))`. Take `⟨y, hy, hyL, hyx⟩` from `separate D ψ S T ΛS ΛT hψ hS hT e hsplit k hk (c - c') hx hxL`. Use `⟨y, hy, ψ (symplO S T c y), ψ (symplO S T c' y), hψ.1.2.1 _, fun hab => hyx ?_, fun Φ => heig Φ _ c rfl y hy hyL, fun Φ => heig Φ _ c' rfl y hy hyL⟩` and prove the remaining obligations.

Establish `h1 : ψ (symplO S T c y) = ψ (symplO S T (c - c') y) * ψ (symplO S T c' y)`. Rewrite using `[← AddChar.map_add_eq_mul, ← symplO_add_left S T, sub_add_cancel]`. Establish `hne0 : ψ (symplO S T c' y) ≠ 0` using `fun h0 => by`. Use `hψ.1.2.1 (symplO S T c' y)` as an intermediate fact. Rewrite `this` using `[h0, norm_zero]`.

Conclude with `zero_ne_one this`. Conclude with `mul_right_cancel₀ hne0 (h1.symm.trans (hab.trans (one_mul _).symm))`. Establish `eq1 : Tm Φ₁ = ∑ q ∈ Q, Tm (P Φ₁ q)` using `by conv_lhs => rw [hcover Φ₁ hsup₁]`. Conclude with `map_sum Tm _ _`. Establish `eq2 : Ω (Tm Φ₂) = ∑ q ∈ Q, Ω (Tm (P Φ₂ q))` using `by conv_lhs => rw [hcover Φ₂ hsup₂]`.

Rewrite using `[map_sum, map_sum]`. Rewrite using `[eq1, eq2, thetaInner_sum_sum hψ hμ Q _ _ (fun q _ => hθ _ (hP₁ q)) (fun q _ => hΩt _ (hθ _ (hP₂ q)))]`. Use `Finset.sum_eq_zero fun q hq => Finset.sum_eq_zero fun q' hq' => ?_` and prove the remaining obligations. Distinguish the cases in `hqq : q = q'`. Substitute `hqq` using the available equality.

Break down `hdisjP q with h | h` into its components or cases. Rewrite using `[h, map_zero]`. Simplify using `[thetaIP]`. Rewrite using `[h, map_zero, map_zero]`. Simplify using `[thetaIP]`.

Take `⟨y, hy, a, b, ha, hab, h1, h2⟩` from `hsep q hq q' hq' hqq`. Use `thetaInner_eq_zero_of_eigen hψ hμ (hθ _ (hP₁ q)) (hΩt _ (hθ _ (hP₂ q'))) y ha hab ?_ ?_` and prove the remaining obligations. Rewrite using `[← hmod y hy _ (hP₁ q), h1 Φ₁, map_smul]`. Rewrite using `[← hΩc y hy _ (hθ _ (hP₂ q')), ← hmod y hy _ (hP₂ q'), h2 Φ₂, map_smul, map_smul]`.
-/
theorem orth_of_disjoint : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (Pf : Finset (Pl D.host.E)) (ea e : AE D) (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsIdemSum ea Pf → IsSplitIdem D e → e * ea = e → IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f₀ → IsPlaceModel ψ (symplO S T) (heisO ψ S T) (cA D ea) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Tm → IsCovolOne (ratL T S) μ 𝓕 → ∀ Φ₁ Φ₂ : WO S T → ℂ, IsSBHalf (cA D ea) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) Φ₁ → IsSBHalf (cA D ea) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) Φ₂ → (∀ x x' : WO S T, (∀ a b, (e + cA D e) * x a b = (e + cA D e) * x' a b) → Φ₁ x ≠ 0 → Φ₂ x' ≠ 0 → False) → ∀ Ω : Module.End ℂ (WO S T → ℂ), (∀ g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (Ω g)) → (∀ y : WO S T, IsHalf e y → ∀ g, IsThetaFunO ψ S T g → Ω (heisO ψ S T y g) = heisO ψ S T y (Ω g)) → thetaIP μ 𝓕 (Tm Φ₁) (Ω (Tm Φ₂)) = 0 := by
  intro D ψ S T ΛS ΛT Pf ea e f₀ Tm μ 𝓕 hψ hS hT hIdem hsplit hee hf₀ hvac hTm hμ Φ₁ Φ₂ hΦ₁ hΦ₂ hdisj Ω hΩt hΩc
  set Λ := (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) with hΛ
  have hea : IsOrthSum ea := isOrthSum_of_isIdemSum hIdem
  have hcea : cA D ea * cA D ea = cA D ea := by rw [← map_mul, hea.idem]
  have hinf : infPart D (cA D ea) = 0 := hea.conj.infPart_eq
  have hce1 : cA D e * cA D e = cA D e := by rw [← map_mul, hsplit.1]
  have hecea : e * cA D ea = 0 := by rw [← hee, mul_assoc, hIdem.2, mul_zero]
  have hcecea : cA D ea * cA D e = cA D e := by rw [← map_mul, mul_comm, hee]
  have half' : ∀ {a : AE D} {u : WO S T}, IsHalf a u ↔ a • u = u := fun {a u} => (isHalf_iff S T).trans (mem_half S T)
  have hθ : ∀ Φ, IsSBHalf (cA D ea) Λ Φ → IsThetaFunO ψ S T (Tm Φ) := fun Φ hΦ =>
    GlobalTheory.SchrTheta.isTheta_placeModel D ψ hψ S T ΛS ΛT hS hT _ hcea hinf f₀ hf₀ Tm hTm Φ hΦ

  obtain ⟨hs₁, k₁, hk₁, hi₁, hl₁⟩ := hΦ₁
  obtain ⟨hs₂, k₂, hk₂, hi₂, hl₂⟩ := hΦ₂
  have hk : 0 < k₁ * k₂ := Nat.mul_pos hk₁ hk₂
  have hhalfU : ∀ (m : ℕ) {a : AE D} {u : WO S T}, u ∈ Λ → IsHalf a u → m • u ∈ Λ ∧ IsHalf a (m • u) :=
    fun m a u hu hue => ⟨AddSubgroup.nsmul_mem _ hu m, half'.2 (by rw [smul_comm, half'.1 hue])⟩
  have hinv₁ : ∀ u ∈ Λ, IsHalf (cA D ea) u → ∀ t, Φ₁ (t + (k₁ * k₂) • u) = Φ₁ t := fun u hu hue t => by
    rw [mul_smul]; exact hi₁ _ (hhalfU k₂ hu hue).1 (hhalfU k₂ hu hue).2 t
  have hinv₂ : ∀ u ∈ Λ, IsHalf (cA D ea) u → ∀ t, Φ₂ (t + (k₁ * k₂) • u) = Φ₂ t := fun u hu hue t => by
    rw [mul_comm, mul_smul]; exact hi₂ _ (hhalfU k₁ hu hue).1 (hhalfU k₁ hu hue).2 t
  have hsup₁ : ∀ t, Φ₁ t ≠ 0 → IsHalf (cA D ea) t ∧ (k₁ * k₂) • t ∈ Λ := fun t ht =>
    ⟨hs₁ t ht, by rw [mul_comm, mul_smul]; exact AddSubgroup.nsmul_mem _ (hl₁ t ht) _⟩
  have hsup₂ : ∀ t, Φ₂ t ≠ 0 → IsHalf (cA D ea) t ∧ (k₁ * k₂) • t ∈ Λ := fun t ht =>
    ⟨hs₂ t ht, by rw [mul_smul]; exact AddSubgroup.nsmul_mem _ (hl₂ t ht) _⟩
  generalize k₁ * k₂ = k at hk hinv₁ hinv₂ hsup₁ hsup₂

  let L : AddSubgroup (WO S T) := AddSubgroup.map (nsmulAddMonoidHom k) (Λ ⊓ half S T (cA D e))
  have memL : ∀ u ∈ Λ, IsHalf (cA D e) u → k • u ∈ L := fun u hu hue =>
    AddSubgroup.mem_map.2 ⟨u, AddSubgroup.mem_inf.2 ⟨hu, (isHalf_iff S T).1 hue⟩, rfl⟩
  have memL' : ∀ x ∈ L, ∃ u ∈ Λ, IsHalf (cA D e) u ∧ x = k • u := fun x hx => by
    obtain ⟨u, hu, rfl⟩ := AddSubgroup.mem_map.1 hx
    exact ⟨u, (AddSubgroup.mem_inf.1 hu).1, (isHalf_iff S T).2 (AddSubgroup.mem_inf.1 hu).2, rfl⟩
  have hceu : ∀ u ∈ Λ, cA D e • u ∈ Λ ∧ IsHalf (cA D e) (cA D e • u) := fun u hu =>
    ⟨idem_smul_latO hce1 hu, half'.2 (by rw [smul_smul, hce1])⟩
  obtain ⟨C, hCh, hC⟩ := finCosets D S T ΛS ΛT hS hT (cA D e) hce1 k hk
  let mkL : WO S T → WO S T ⧸ L := QuotientAddGroup.mk
  let Q : Finset (WO S T ⧸ L) := C.image mkL
  let P : (WO S T → ℂ) → (WO S T ⧸ L) → WO S T → ℂ := fun Φ q t =>
    if mkL (cA D e • t) = q then Φ t else 0

  have hcos : ∀ t, IsHalf (cA D ea) t → k • t ∈ Λ → ∃ c ∈ C, ∃ u ∈ Λ, IsHalf (cA D e) u ∧ cA D e • t = c + k • u :=
    fun t _ htk => hC _ (half'.2 (by rw [smul_smul, hce1])) (by rw [smul_comm]; exact idem_smul_latO hce1 htk)
  have hcover : ∀ Φ : WO S T → ℂ, (∀ t, Φ t ≠ 0 → IsHalf (cA D ea) t ∧ k • t ∈ Λ) → Φ = ∑ q ∈ Q, P Φ q := by
    intro Φ hsup
    funext t
    rw [Finset.sum_apply]
    by_cases h0 : Φ t = 0
    · rw [h0]; exact (Finset.sum_eq_zero fun q _ => by simp only [P, h0, ite_self]).symm
    · have hh := hcos t (hsup t h0).1 (hsup t h0).2
      obtain ⟨c, hc, u, hu, hh⟩ := hh
      obtain ⟨hue, htc⟩ := hh
      have hq : mkL (cA D e • t) = mkL c := by
        rw [htc]; refine QuotientAddGroup.eq.2 ?_
        have : -(c + k • u) + c = -(k • u) := by abel
        rw [this]
        exact neg_mem (memL u hu hue)
      rw [Finset.sum_eq_single_of_mem (mkL c) (Finset.mem_image_of_mem _ hc) fun q _ hq' => by
        simp only [P, hq, if_neg (Ne.symm hq')]]
      simp only [P, hq, if_true]
  have hSB : ∀ Φ : WO S T → ℂ, (∀ t, Φ t ≠ 0 → IsHalf (cA D ea) t ∧ k • t ∈ Λ) →
      (∀ u ∈ Λ, IsHalf (cA D ea) u → ∀ t, Φ (t + k • u) = Φ t) → ∀ q, IsSBHalf (cA D ea) Λ (P Φ q) := by
    intro Φ hsup hinv q
    have hne : ∀ t, P Φ q t ≠ 0 → Φ t ≠ 0 := fun t ht h0 => ht (by simp only [P, h0, ite_self])
    refine ⟨fun t ht => (hsup t (hne t ht)).1, k, hk, fun u hu hue t => ?_, fun t ht => (hsup t (hne t ht)).2⟩
    have hkey : mkL (cA D e • (t + k • u)) = mkL (cA D e • t) := by
      simp only [mkL]
      rw [smul_add, smul_comm, QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff _).2
        (memL _ (hceu u hu).1 (hceu u hu).2), add_zero]
    simp only [P, hkey, hinv u hu hue t]

  have hP₁ := hSB Φ₁ hsup₁ hinv₁
  have hP₂ := hSB Φ₂ hsup₂ hinv₂

  have hPne : ∀ Φ q t, P Φ q t ≠ 0 → mkL (cA D e • t) = q ∧ Φ t ≠ 0 := fun Φ q t h => by
    by_cases hq : mkL (cA D e • t) = q
    · refine ⟨hq, fun h0 => h ?_⟩
      simp only [P, hq, h0, if_true]
    · exact absurd (by simp only [P, hq, if_false]) h

  have hhalf_ce : ∀ t, IsHalf (cA D ea) t → (e + cA D e) • t = cA D e • t := fun t ht => by
    have h0 : e • t = 0 := by rw [← half'.1 ht, smul_smul, hecea, zero_smul]
    rw [add_smul, h0, zero_add]

  have hdisjP : ∀ q, P Φ₁ q = 0 ∨ P Φ₂ q = 0 := by
    intro q
    by_contra hne
    push_neg at hne
    obtain ⟨t, ht⟩ := Function.ne_iff.1 hne.1
    obtain ⟨t', ht'⟩ := Function.ne_iff.1 hne.2
    obtain ⟨hq1, h1⟩ := hPne Φ₁ q t ht
    obtain ⟨hq2, h2⟩ := hPne Φ₂ q t' ht'
    have hL : -(cA D e • t) + cA D e • t' ∈ L := QuotientAddGroup.eq.1 (hq1.trans hq2.symm)
    obtain ⟨w, hw, hwe, hwk⟩ := memL' _ hL
    have hwea : IsHalf (cA D ea) (-w) := half'.2 (by rw [smul_neg, ← half'.1 hwe, smul_smul, hcecea])
    have h2' : Φ₂ (t' + k • (-w)) ≠ 0 := by rw [hinv₂ _ (neg_mem hw) hwea]; exact h2
    have hw' : cA D e • (k • -w) = -(k • w) := by rw [smul_comm, smul_neg, half'.1 hwe, smul_neg]
    have hM : (e + cA D e) • t = (e + cA D e) • (t' + k • (-w)) := by
      rw [hhalf_ce t (hsup₁ t h1).1, hhalf_ce _ (hsup₂ _ h2').1, smul_add, hw', ← hwk]
      abel
    exact hdisj t (t' + k • (-w)) (fun a b => congrFun (congrFun hM a) b) h1 h2'

  have hmod : ∀ y, IsHalf e y → ∀ Φ, IsSBHalf (cA D ea) Λ Φ →
      Tm (fun t => ψ (symplO S T t y) * Φ t) = heisO ψ S T y (Tm Φ) := fun y hy Φ hΦ =>
    hTm.modul Φ hΦ y (by rw [cA_cA]; exact half'.2 (by rw [← half'.1 hy, smul_smul, mul_comm ea e, hee]))

  have heig : ∀ Φ q (c : WO S T), mkL c = q → ∀ y, IsHalf e y → (∀ u ∈ Λ, ψ (symplO S T (k • u) y) = 1) →
      (fun t => ψ (symplO S T t y) * P Φ q t) = ψ (symplO S T c y) • P Φ q := by
    intro Φ q c hc y hy hyL
    funext t
    rw [Pi.smul_apply, smul_eq_mul]
    by_cases hq : mkL (cA D e • t) = q
    · have hL : -(cA D e • t) + c ∈ L := QuotientAddGroup.eq.1 (hq.trans hc.symm)
      obtain ⟨w, hw, hwe, hwk⟩ := memL' _ hL
      have h1 : symplO S T t y = symplO S T (cA D e • t) y := by rw [symplO_smul S T, cA_cA, half'.1 hy]
      have h2 : cA D e • t = c + k • -w := by rw [smul_neg, ← hwk]; abel
      rw [h1, h2, symplO_add_left S T, AddChar.map_add_eq_mul, hyL _ (neg_mem hw), mul_one]
    · simp only [P, hq, if_false, mul_zero]

  have hsep : ∀ q ∈ Q, ∀ q' ∈ Q, q ≠ q' → ∃ y, IsHalf e y ∧ ∃ a b : ℂ, ‖a‖ = 1 ∧ a ≠ b ∧
      (∀ Φ, (fun t => ψ (symplO S T t y) * P Φ q t) = a • P Φ q) ∧
      (∀ Φ, (fun t => ψ (symplO S T t y) * P Φ q' t) = b • P Φ q') := by
    intro q hq q' hq' hne
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hq
    obtain ⟨c', hc', rfl⟩ := Finset.mem_image.1 hq'
    have hx : IsHalf (cA D e) (c - c') :=
      half'.2 (by rw [smul_sub, half'.1 (hCh c hc), half'.1 (hCh c' hc')])
    have hxL : ∀ u ∈ Λ, IsHalf (cA D e) u → c - c' ≠ k • u := fun u hu hue h => hne (QuotientAddGroup.eq.2 (by
      have : -c + c' = -(k • u) := by rw [← h]; abel
      rw [this]; exact neg_mem (memL u hu hue)))
    obtain ⟨y, hy, hyL, hyx⟩ := separate D ψ S T ΛS ΛT hψ hS hT e hsplit k hk (c - c') hx hxL
    refine ⟨y, hy, ψ (symplO S T c y), ψ (symplO S T c' y), hψ.1.2.1 _, fun hab => hyx ?_,
      fun Φ => heig Φ _ c rfl y hy hyL, fun Φ => heig Φ _ c' rfl y hy hyL⟩
    have h1 : ψ (symplO S T c y) = ψ (symplO S T (c - c') y) * ψ (symplO S T c' y) := by
      rw [← AddChar.map_add_eq_mul, ← symplO_add_left S T, sub_add_cancel]
    have hne0 : ψ (symplO S T c' y) ≠ 0 := fun h0 => by
      have := hψ.1.2.1 (symplO S T c' y)
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    exact mul_right_cancel₀ hne0 (h1.symm.trans (hab.trans (one_mul _).symm))

  have eq1 : Tm Φ₁ = ∑ q ∈ Q, Tm (P Φ₁ q) := by
    conv_lhs => rw [hcover Φ₁ hsup₁]
    exact map_sum Tm _ _
  have eq2 : Ω (Tm Φ₂) = ∑ q ∈ Q, Ω (Tm (P Φ₂ q)) := by
    conv_lhs => rw [hcover Φ₂ hsup₂]
    rw [map_sum, map_sum]
  rw [eq1, eq2, thetaInner_sum_sum hψ hμ Q _ _ (fun q _ => hθ _ (hP₁ q)) (fun q _ => hΩt _ (hθ _ (hP₂ q)))]
  refine Finset.sum_eq_zero fun q hq => Finset.sum_eq_zero fun q' hq' => ?_
  by_cases hqq : q = q'
  · subst hqq
    rcases hdisjP q with h | h
    · rw [h, map_zero]; simp [thetaIP]
    · rw [h, map_zero, map_zero]; simp [thetaIP]
  · obtain ⟨y, hy, a, b, ha, hab, h1, h2⟩ := hsep q hq q' hq' hqq
    refine thetaInner_eq_zero_of_eigen hψ hμ (hθ _ (hP₁ q)) (hΩt _ (hθ _ (hP₂ q'))) y ha hab ?_ ?_
    · rw [← hmod y hy _ (hP₁ q), h1 Φ₁, map_smul]
    · rw [← hΩc y hy _ (hθ _ (hP₂ q')), ← hmod y hy _ (hP₂ q'), h2 Φ₂, map_smul, map_smul]

end GlobalTheory.BadOrth

end
