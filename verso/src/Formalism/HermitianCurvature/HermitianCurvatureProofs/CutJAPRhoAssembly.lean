import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRhoCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKapNrmW
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeomAtGq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutTypeNormMeasMain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_TypeNormMeas_TC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Filter Topology
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.PRhoCut

open Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

namespace Asm

variable {k r : ℕ}

/- English proof (translation)
The claim follows from `Qx8.frame_sub h (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv ⊢; tauto)`.
-/
theorem frame_swap {z b : Fin (2 * r + k + 1) → ℂ} {m : ℕ} {Fr : Fin m → Fin (2 * r + k + 1) → ℂ}
    (h : IsFrameOf k r [z, b] Fr) : IsFrameOf k r [b, z] Fr :=
  Qx8.frame_sub h (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv ⊢; tauto)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2, h3⟩`. Use `⟨h1, h2, fun a v hv => ?_⟩` and prove the remaining obligations. Simplify using `only [List.mem_cons, List.not_mem_nil, or_false] at hv`. Break down `hv with rfl | rfl` into its components or cases.

Conclude with `h3 a _ (by simp)`. Use `h3 a (c • v) (by simp)` as an intermediate fact. Rewrite `this` using `[Qx8.herm_smul_right']`. Conclude with `(mul_eq_zero.1 this).resolve_left (star_ne_zero.2 hc)`. Introduce and unpack `⟨h1, h2, h3⟩`.

Use `⟨h1, h2, fun a v hv => ?_⟩` and prove the remaining obligations. Simplify using `only [List.mem_cons, List.not_mem_nil, or_false] at hv`. Break down `hv with rfl | rfl` into its components or cases. Conclude with `h3 a _ (by simp)`. Rewrite using `[Qx8.herm_smul_right', h3 a b (by simp), mul_zero]`.
-/
theorem frame_smul {z b : Fin (2 * r + k + 1) → ℂ} {c : ℂ} (hc : c ≠ 0) {m : ℕ}
    {Fr : Fin m → Fin (2 * r + k + 1) → ℂ} : IsFrameOf k r [z, c • b] Fr ↔ IsFrameOf k r [z, b] Fr := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun a v hv => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact h3 a _ (by simp)
    · have := h3 a (c • v) (by simp)
      rw [Qx8.herm_smul_right'] at this
      exact (mul_eq_zero.1 this).resolve_left (star_ne_zero.2 hc)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun a v hv => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact h3 a _ (by simp)
    · rw [Qx8.herm_smul_right', h3 a b (by simp), mul_zero]

section Wp

variable {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [Kset, Set.mem_ofPred_eq, frame_smul hc]`.
-/
theorem Kset_smul {z b : Fin (2 * r + k + 1) → ℂ} {c : ℂ} (hc : c ≠ 0) (π : Mx k r → (Wp →L[ℂ] Wp)) (f : ℂ → ℂ) :
    Kset k r z (c • b) π f = Kset k r z b π f := by
  ext x
  simp only [Kset, Set.mem_ofPred_eq, frame_smul hc]

/- English proof (translation)
Unfold `K`. Rewrite using `[Kset_smul hc]`.
-/
theorem K_smul {z b : Fin (2 * r + k + 1) → ℂ} {c : ℂ} (hc : c ≠ 0) (π : Mx k r → (Wp →L[ℂ] Wp)) (f : ℂ → ℂ) :
    K k r z (c • b) π f = K k r z b π f := by
  unfold K; rw [Kset_smul hc]

variable [FiniteDimensional ℂ Wp]

/- English proof (translation)
Set `S : Submodule ℂ Wp` to `{ carrier := Kset k r z b π f add_mem' := fun {x y} hx hy Fr hFr w => by`. Establish `hl` using `Qx8.capRep_lin hFr (z := z) (by simp) hrep hcont w`. Establish `e` using `hl x y 1`. Simplify using `only [one_smul] at e`. Rewrite using `[e, hx Fr hFr w, hy Fr hFr w, smul_add]`.

Use the proof step `zero_mem' := fun Fr hFr w => by`. Rewrite using `[(Qx8.capRep_lin hFr (z := z) (by simp) hrep hcont w).map_zero, smul_zero]`. Use the proof step `smul_mem' := fun c x hx Fr hFr w => by`. Establish `hl` using `Qx8.capRep_lin hFr (z := z) (by simp) hrep hcont w`. Rewrite using `[hl.map_smul, hx Fr hFr w, smul_comm] }`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Conclude with `(Submodule.span_le (p := S)).2 (fun y hy => hy) hx`. Introduce `hx`. Conclude with `Submodule.subset_span hx`.
-/
theorem mem_K {z b : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {f : ℂ → ℂ}
    (hrep : IsCRepOn (UWset k r z) π) (hcont : ContinuousOn π (UWset k r z)) {x : Wp} :
    x ∈ K k r z b π f ↔ x ∈ Kset k r z b π f := by
  let S : Submodule ℂ Wp :=
    { carrier := Kset k r z b π f
      add_mem' := fun {x y} hx hy Fr hFr w => by
        have hl := Qx8.capRep_lin hFr (z := z) (by simp) hrep hcont w
        have e := hl x y 1
        simp only [one_smul] at e
        rw [e, hx Fr hFr w, hy Fr hFr w, smul_add]
      zero_mem' := fun Fr hFr w => by
        rw [(Qx8.capRep_lin hFr (z := z) (by simp) hrep hcont w).map_zero, smul_zero]
      smul_mem' := fun c x hx Fr hFr w => by
        have hl := Qx8.capRep_lin hFr (z := z) (by simp) hrep hcont w
        rw [hl.map_smul, hx Fr hFr w, smul_comm] }
  constructor
  · intro hx
    exact (Submodule.span_le (p := S)).2 (fun y hy => hy) hx
  · intro hx
    exact Submodule.subset_span hx

/- English proof (translation)
Introduce `Fr' hFr' w`. Establish `hhi : h⁻¹ ∈ UWset k r z` using `WeylGroupFacts.uw_inv hh`. Establish `hu` using `WeylGroupFacts.isUnit_of_uh hh.1`. Set `Fr : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ` to `fun a => h⁻¹ *ᵥ Fr' a`. Establish `hFr : IsFrameOf k r [z, b] Fr`.

Use `⟨fun p => CutBP.TNM.tc_inWb hhi (hFr'.1 p), fun p q => ?_, fun a v hv => ?_⟩` and prove the remaining obligations. Use `show herm (Hpk k r) (h⁻¹ *ᵥ Fr' p) (h⁻¹ *ᵥ Fr' q) = _`. Rewrite using `[Qx2.herm_uh hhi.1]`. Conclude with `hFr'.2.1 p q`. Simplify using `only [List.mem_cons, List.not_mem_nil, or_false] at hv`.

Break down `hv with rfl | rfl` into its components or cases. Combine the equalities or inequalities in the displayed calculation. Use `show herm (Hpk k r) (h⁻¹ *ᵥ Fr' a) v = 0`. Rewrite using `[← Qx2.herm_uh hh.1, Qx8.inv_mulVec_uh hh.1]`. Conclude with `hFr'.2.2 a _ (by simp)`.

Establish `hint : ∀ h' ∈ UWset k r z, h' *ᵥ b = b → ∀ v, π h (π h' v) = π (h * h' * h⁻¹) (π h v)`. Introduce `h' hh' _ v`. Establish `e1` using `hrep.2 _ (WeylGroupFacts.uw_mul (WeylGroupFacts.uw_mul hh hh') hhi) h hh`. Rewrite `e1` using `[Matrix.mul_assoc (h * h'), Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]`. Establish `e3` using `hrep.2 h hh h' hh'`.

Combine the equalities or inequalities in the displayed calculation. Establish `e` using `Qx8.capRep_intertwine (frame_swap hFr) hrep hcont hh.1 (π h) hint w x`. Establish `e2 : (fun a => h *ᵥ Fr a) = Fr'` using `funext fun a => Qx8.inv_mulVec_uh hh.1 (Fr' a)`. Rewrite `e` using `[e2]`. Rewrite using `[← e, hx Fr hFr w, map_smul]`.
-/
theorem Kset_uw {z b : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {f : ℂ → ℂ}
    (hrep : IsCRepOn (UWset k r z) π) (hcont : ContinuousOn π (UWset k r z)) {h : Mx k r} (hh : h ∈ UWset k r z)
    {x : Wp} (hx : x ∈ Kset k r z b π f) : π h x ∈ Kset k r z (h *ᵥ b) π f := by
  intro Fr' hFr' w
  have hhi : h⁻¹ ∈ UWset k r z := WeylGroupFacts.uw_inv hh
  have hu := WeylGroupFacts.isUnit_of_uh hh.1
  let Fr : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ := fun a => h⁻¹ *ᵥ Fr' a
  have hFr : IsFrameOf k r [z, b] Fr := by
    refine ⟨fun p => CutBP.TNM.tc_inWb hhi (hFr'.1 p), fun p q => ?_, fun a v hv => ?_⟩
    · show herm (Hpk k r) (h⁻¹ *ᵥ Fr' p) (h⁻¹ *ᵥ Fr' q) = _
      rw [Qx2.herm_uh hhi.1]; exact hFr'.2.1 p q
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · calc herm (Hpk k r) (h⁻¹ *ᵥ Fr' a) v = herm (Hpk k r) (h⁻¹ *ᵥ Fr' a) (h⁻¹ *ᵥ v) := by rw [hhi.2.2]
        _ = herm (Hpk k r) (Fr' a) v := Qx2.herm_uh hhi.1 _ _
        _ = 0 := hFr'.2.2 a v (by simp)
    · show herm (Hpk k r) (h⁻¹ *ᵥ Fr' a) v = 0
      rw [← Qx2.herm_uh hh.1, Qx8.inv_mulVec_uh hh.1]
      exact hFr'.2.2 a _ (by simp)
  have hint : ∀ h' ∈ UWset k r z, h' *ᵥ b = b → ∀ v, π h (π h' v) = π (h * h' * h⁻¹) (π h v) := by
    intro h' hh' _ v
    have e1 := hrep.2 _ (WeylGroupFacts.uw_mul (WeylGroupFacts.uw_mul hh hh') hhi) h hh
    rw [Matrix.mul_assoc (h * h'), Matrix.nonsing_inv_mul _ hu, Matrix.mul_one] at e1
    have e3 := hrep.2 h hh h' hh'
    calc π h (π h' v) = π (h * h') v := by rw [e3]; rfl
      _ = π (h * h' * h⁻¹) (π h v) := by rw [e1]; rfl
  have e := Qx8.capRep_intertwine (frame_swap hFr) hrep hcont hh.1 (π h) hint w x
  have e2 : (fun a => h *ᵥ Fr a) = Fr' := funext fun a => Qx8.inv_mulVec_uh hh.1 (Fr' a)
  rw [e2] at e
  rw [← e, hx Fr hFr w, map_smul]

end Wp

section Proj

variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem sp_congr {K₁ K₂ : Submodule ℂ Wp} (h : K₁ = K₂) : K₁.starProjection = K₂.starProjection := by
  subst h; rfl

/- English proof (translation)
Establish `hhi : h⁻¹ ∈ UWset k r z` using `WeylGroupFacts.uw_inv hh`. Establish `hu` using `WeylGroupFacts.isUnit_of_uh hh.1`. Establish `hinv : ∀ v, π h (π h⁻¹ v) = v`. Introduce `v`. Establish `e` using `hrep.2 _ hh _ hhi`.

Rewrite `e` using `[Matrix.mul_nonsing_inv _ hu, hrep.1]`. Rewrite using `[← ContinuousLinearMap.comp_apply, ← e]`. Both sides reduce to the same expression. Set `Lh : Wp →ₗᵢ[ℂ] Wp` to `{ toLinearMap := (π h : Wp →ₗ[ℂ] Wp), norm_map' := hunit h hh }`. Establish `hin : ∀ u v, inner ℂ (π h u) (π h v) = inner ℂ u v` using `fun u v => Lh.inner_map_map u v`.

Use extensionality with `x`. Simplify using `only [ContinuousLinearMap.comp_apply]`. Use `Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_` and prove the remaining obligations. Rewrite using `[mem_K hrep hcont]`. Conclude with `Kset_uw hrep hcont hh ((mem_K hrep hcont).1 (Submodule.starProjection_apply_mem _ _))`.

Introduce `y hy`. Establish `hy' : π h⁻¹ y ∈ K k r z b π f`. Rewrite `hy`, the goal using `[mem_K hrep hcont]`. Use `Kset_uw hrep hcont hhi hy` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]`. Then use the resulting hypothesis.

Establish `e : x - π h ((K k r z b π f).starProjection (π h⁻¹ x)) = π h (π h⁻¹ x - (K k r z b π f).starProjection (π h⁻¹ x))`. Rewrite using `[map_sub, hinv]`. Rewrite using `[e]`. Use `conv_lhs => rw [← hinv y]`. Rewrite using `[hin]`.

Conclude with `Submodule.starProjection_inner_eq_zero _ _ hy'`.
-/
theorem proj_uw {z b : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {f : ℂ → ℂ}
    (hrep : IsCRepOn (UWset k r z) π) (hcont : ContinuousOn π (UWset k r z))
    (hunit : ∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) {h : Mx k r} (hh : h ∈ UWset k r z) :
    (K k r z (h *ᵥ b) π f).starProjection = (π h).comp ((K k r z b π f).starProjection.comp (π h⁻¹)) := by
  have hhi : h⁻¹ ∈ UWset k r z := WeylGroupFacts.uw_inv hh
  have hu := WeylGroupFacts.isUnit_of_uh hh.1
  have hinv : ∀ v, π h (π h⁻¹ v) = v := by
    intro v
    have e := hrep.2 _ hh _ hhi
    rw [Matrix.mul_nonsing_inv _ hu, hrep.1] at e
    rw [← ContinuousLinearMap.comp_apply, ← e]; rfl
  let Lh : Wp →ₗᵢ[ℂ] Wp := { toLinearMap := (π h : Wp →ₗ[ℂ] Wp), norm_map' := hunit h hh }
  have hin : ∀ u v, inner ℂ (π h u) (π h v) = inner ℂ u v := fun u v => Lh.inner_map_map u v
  ext x
  simp only [ContinuousLinearMap.comp_apply]
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · rw [mem_K hrep hcont]
    exact Kset_uw hrep hcont hh ((mem_K hrep hcont).1 (Submodule.starProjection_apply_mem _ _))
  · intro y hy
    have hy' : π h⁻¹ y ∈ K k r z b π f := by
      rw [mem_K hrep hcont] at hy ⊢
      have := Kset_uw hrep hcont hhi hy
      rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec] at this
    have e : x - π h ((K k r z b π f).starProjection (π h⁻¹ x)) =
        π h (π h⁻¹ x - (K k r z b π f).starProjection (π h⁻¹ x)) := by
      rw [map_sub, hinv]
    rw [e]
    conv_lhs => rw [← hinv y]
    rw [hin]
    exact Submodule.starProjection_inner_eq_zero _ _ hy'

end Proj

def PrDef {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (P : M.Par)
    (z : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp)) (ρ : M.Ty P) (a : Fin (2 * P.r + P.k + 1) → ℂ) :
    Wp →L[ℂ] Wp :=
  haveI := Classical.dec
  if 0 < PRho.nrmW P.k P.r z a then
    (K P.k P.r z (SSn.prWv P.k P.r z a) π (fun w => M.xC P ρ (w - ((P.k : ℂ) - 2) / 2))).starProjection
  else 0

end Asm

open Asm in
/- English proof (translation)
Introduce `hF hC hO hL`. Unfold `PRho.PRhoExists`. Introduce `Wp Wq _ _ _ _ _ _ P Bs hPl hk`. Take `⟨hOK, hz, -, -, -, hπ, -⟩` from `hPl`. Take `⟨-, hrep, hcont, hunit, -, -⟩` from `id hπ`.

Establish `hT : 0 < Tz P.k P.r Bs.z` using `Bs.T_pos`. Take `⟨w, p, hLag⟩` from `hL hO P hOK hk`. Establish `hNF` using `weighted_norm_facts_hold P.k P.r Bs.z hz hT`. Establish `hfr : ∀ a, 0 < PRho.nrmW P.k P.r Bs.z a → ∃ Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ, IsFrameOf P.k P.r [Bs.z, SSn.prWv P.k P.r Bs.z a] Fr`. Introduce `a ha`.

Take `⟨Fr, -, hev⟩` from `hF P.k P.r Bs.z hk hz hT a ha`. Conclude with `⟨Fr a, hev.self_of_nhds⟩`. Use `⟨fun ρ a => PrDef P Bs.z Bs.π ρ a, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `ρ a₀ ha₀`. Establish `ha₀' : 0 < PRho.nrmW P.k P.r Bs.z a₀`.

Establish `: (1 : ℝ) / 4 < PRho.nrmW P.k P.r Bs.z a₀` using `ha₀`. Combine the linear equalities and inequalities to obtain the conclusion. Use `ContDiffAt.contDiffWithinAt ?_` and prove the remaining obligations. Take `⟨Fr, hFr, hev⟩` from `hF P.k P.r Bs.z hk hz hT a₀ ha₀'`. Take `⟨C, hCs, hCeq⟩` from `hC Wp P.k P.r (P.k - 1) Bs.z Bs.π ⟨hrep, hcont⟩ w`.

Establish `hpos : ∀ᶠ a in 𝓝 a₀, 0 < PRho.nrmW P.k P.r Bs.z a` using `(hNF.1.continuous.tendsto a₀).eventually (lt_mem_nhds ha₀')`. Establish `hCF : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun a => C (Fr a)) a₀` using `hCs.contDiffAt.comp a₀ hFr`. Establish `hsm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun a => Polynomial.aeval (C (Fr a)) (p ρ)) a₀`. Simplify using `only [Polynomial.aeval_eq_sum_range]`. Conclude with `ContDiffAt.sum fun i _ => (hCF.pow i).const_smul _`.

Use `hsm.congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [hpos, hev] with a ha hfa`. Use `set b := SSn.prWv P.k P.r Bs.z a with hb`. Establish `hzz : herm (Hpk P.k P.r) Bs.z Bs.z ≠ 0`. Introduce `h0; have : Tz P.k P.r Bs.z = 0 := by unfold Tz; rw [h0]; simp`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hzzT : herm (Hpk P.k P.r) Bs.z Bs.z = ((-(Tz P.k P.r Bs.z) : ℝ) : ℂ)`. Establish `e2` using `Complex.conj_eq_iff_re.1 (Qx2.herm_star Bs.z Bs.z)`. Simplify using `only [Tz, neg_neg]`. Conclude with `e2.symm`.

Establish `hbW : inWb P.k P.r b ∧ herm (Hpk P.k P.r) b Bs.z = 0`. Rewrite using `[hb]`. Prove the components needed by the constructor for the conclusion. Introduce `i hi`. Simplify using `only [SSn.prWv, SSn.wbP, Pi.add_apply, Pi.smul_apply, hz i hi, smul_eq_mul, mul_zero, add_zero]`.

Rewrite using `[if_neg (by omega)]`. Unfold `SSn.prWv`. Rewrite using `[Qx8.herm_add_left', Qx8.herm_smul_left', hzzT]`. Establish `hT0 : ((Tz P.k P.r Bs.z : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hT.ne'`. Clear the denominators using the available nonvanishing facts.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `set s : ℝ := Real.sqrt (PRho.nrmW P.k P.r Bs.z a) with hs`. Establish `hs0 : 0 < s` using `Real.sqrt_pos.2 ha`. Use `set c : ℂ := ((s⁻¹ : ℝ) : ℂ) with hc`.

Establish `hc0 : c ≠ 0` using `by rw [hc]; exact_mod_cast (inv_pos.2 hs0).ne'`. Establish `hbb : herm (Hpk P.k P.r) b b = ((PRho.nrmW P.k P.r Bs.z a : ℝ) : ℂ)`. Establish `e1 : star (herm (Hpk P.k P.r) b b) = herm (Hpk P.k P.r) b b` using `Qx2.herm_star b b`. Establish `e2` using `Complex.conj_eq_iff_re.1 e1`. Rewrite using `[← e2]`.

Both sides reduce to the same expression. Establish `he1 : inWb P.k P.r (c • b)` using `fun i hi => by simp [hbW.1 i hi]`. Establish `he2 : herm (Hpk P.k P.r) (c • b) Bs.z = 0` using `by rw [Qx8.herm_smul_left', hbW.2, mul_zero]`. Establish `he3 : herm (Hpk P.k P.r) (c • b) (c • b) = 1`. Rewrite using `[Qx8.herm_smul_left', Qx8.herm_smul_right', hbb, hc, Complex.star_def, Complex.conj_ofReal]`.

Establish `hss : s * s = PRho.nrmW P.k P.r Bs.z a` using `Real.mul_self_sqrt ha.le`. Rewrite using `[← Complex.ofReal_mul, ← Complex.ofReal_mul, ← hss]`. Clear the denominators using the available nonvanishing facts. Evaluate the numerical expressions. Establish `hfe : IsFrameOf P.k P.r [Bs.z, c • b] (Fr a)` using `(frame_smul hc0).2 hfa`.

Establish `hCv : ∀ v, C (Fr a) v = capRep P.k P.r Bs.π (Fr a) w v` using `hCeq (Fr a) (Qx8.frame_sub hfa (by simp))`. Rewrite using `[hLag Wp Bs.z (c • b) Bs.π hz hT hπ he1 he2 he3 (Fr a) hfe (C (Fr a)) hCv ρ]`. Use `show PrDef P Bs.z Bs.π ρ a = _`. Unfold `PrDef`. Rewrite using `[if_pos ha]`.

Conclude with `sp_congr (K_smul hc0 _ _).symm`. Introduce `h hh ρ a`. Establish `hn : PRho.nrmW P.k P.r Bs.z (h *ᵥ a) = PRho.nrmW P.k P.r Bs.z a` using `hNF.2 h hh a`. Use `show PrDef P Bs.z Bs.π ρ (h *ᵥ a) = (Bs.π h).comp ((PrDef P Bs.z Bs.π ρ a).comp (Bs.π h⁻¹))`. Unfold `PrDef`.

Rewrite using `[hn]`. Use `split_ifs with ha`. Use `(sp_congr ?_).trans (proj_uw hrep hcont hunit hh)` and prove the remaining obligations. Rewrite using `[kap_prWv_mulVec hz hh a]`. Use extensionality with `x`.

Simplify using the standard rewrite rules. Introduce `a ha`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `ρ c hc`. Establish `hpos : 0 < PRho.nrmW P.k P.r Bs.z (c • a)`.

Rewrite using `[nrmW_smul]`. Conclude with `mul_pos (Complex.normSq_pos.2 hc) ha`. Use `show PrDef P Bs.z Bs.π ρ (c • a) = PrDef P Bs.z Bs.π ρ a`. Unfold `PrDef`. Rewrite using `[if_pos hpos, if_pos ha]`.

Conclude with `sp_congr (by rw [SSn.Geom.prWv_eq, SSn.Geom.prW_smul, ← SSn.Geom.prWv_eq]; exact K_smul hc _ _)`. Introduce `ρ x y show inner ℂ (PrDef P Bs.z Bs.π ρ a x) y = inner ℂ x (PrDef P Bs.z Bs.π ρ a y)`. Unfold `PrDef`. Rewrite using `[if_pos ha]`. Conclude with `Submodule.inner_starProjection_left_eq_right _ x y`.

Introduce `ρ ρ' show (PrDef P Bs.z Bs.π ρ a).comp (PrDef P Bs.z Bs.π ρ' a) = if ρ = ρ' then PrDef P Bs.z Bs.π ρ a else 0`. Unfold `PrDef`. Rewrite using `[if_pos ha, if_pos ha]`. Use `split_ifs with hρ`. Substitute `hρ` using the available equality.

Use extensionality with `x`. Simplify using `only [ContinuousLinearMap.comp_apply]`. Conclude with `Submodule.starProjection_eq_self_iff.2 (Submodule.starProjection_apply_mem _ x)`. Use extensionality with `x`. Simplify using `only [ContinuousLinearMap.comp_apply, zero_apply]`.

Rewrite using `[Submodule.starProjection_apply_eq_zero_iff, Submodule.mem_orthogonal]`. Introduce `u hu`. Establish `hu'` using `(mem_K hrep hcont).1 hu`. Establish `hv'` using `(mem_K hrep hcont).1 (Submodule.starProjection_apply_mem (K P.k P.r Bs.z (SSn.prWv P.k P.r Bs.z a) Bs.π (fun w => M.xC P ρ' (w - ((P.k : ℂ) - 2) / 2))) x)`. Take `⟨Y, hY⟩` from `Qx8.xC_sep hOK hρ`.

Use `hO Wp P.k P.r Bs.z (SSn.prWv P.k P.r Bs.z a) Bs.π hz hT ⟨hrep, hcont⟩ hunit (hfr a ha) _ _ u _ hu' hv' ⟨Y + ((P.k : ℂ) - 2) / 2, ?_⟩` and prove the remaining obligations. Simplify using `using hY`. Introduce `ρ x show PrDef P Bs.z Bs.π ρ a x = x ↔ _`. Unfold `PrDef`. Rewrite using `[if_pos ha, Submodule.starProjection_eq_self_iff, mem_K hrep hcont]`.

Conclude with `Iff.rfl`.
-/
theorem rho_projection_assembly : Assembly := by
  intro hF hC hO hL
  unfold PRho.PRhoExists
  intro Wp Wq _ _ _ _ _ _ P Bs hPl hk
  obtain ⟨hOK, hz, -, -, -, hπ, -⟩ := hPl
  obtain ⟨-, hrep, hcont, hunit, -, -⟩ := id hπ
  have hT : 0 < Tz P.k P.r Bs.z := Bs.T_pos
  obtain ⟨w, p, hLag⟩ := hL hO P hOK hk
  have hNF := weighted_norm_facts_hold P.k P.r Bs.z hz hT
  have hfr : ∀ a, 0 < PRho.nrmW P.k P.r Bs.z a →
      ∃ Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ, IsFrameOf P.k P.r [Bs.z, SSn.prWv P.k P.r Bs.z a] Fr := by
    intro a ha
    obtain ⟨Fr, -, hev⟩ := hF P.k P.r Bs.z hk hz hT a ha
    exact ⟨Fr a, hev.self_of_nhds⟩
  refine ⟨fun ρ a => PrDef P Bs.z Bs.π ρ a, ?_, ?_, ?_⟩
  ·
    intro ρ a₀ ha₀
    have ha₀' : 0 < PRho.nrmW P.k P.r Bs.z a₀ := by
      have : (1 : ℝ) / 4 < PRho.nrmW P.k P.r Bs.z a₀ := ha₀
      linarith
    refine ContDiffAt.contDiffWithinAt ?_
    obtain ⟨Fr, hFr, hev⟩ := hF P.k P.r Bs.z hk hz hT a₀ ha₀'
    obtain ⟨C, hCs, hCeq⟩ := hC Wp P.k P.r (P.k - 1) Bs.z Bs.π ⟨hrep, hcont⟩ w
    have hpos : ∀ᶠ a in 𝓝 a₀, 0 < PRho.nrmW P.k P.r Bs.z a :=
      (hNF.1.continuous.tendsto a₀).eventually (lt_mem_nhds ha₀')
    have hCF : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun a => C (Fr a)) a₀ := hCs.contDiffAt.comp a₀ hFr
    have hsm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun a => Polynomial.aeval (C (Fr a)) (p ρ)) a₀ := by
      simp only [Polynomial.aeval_eq_sum_range]
      exact ContDiffAt.sum fun i _ => (hCF.pow i).const_smul _
    refine hsm.congr_of_eventuallyEq ?_
    filter_upwards [hpos, hev] with a ha hfa
    set b := SSn.prWv P.k P.r Bs.z a with hb
    have hzz : herm (Hpk P.k P.r) Bs.z Bs.z ≠ 0 := by
      intro h0; have : Tz P.k P.r Bs.z = 0 := by unfold Tz; rw [h0]; simp
      linarith
    have hzzT : herm (Hpk P.k P.r) Bs.z Bs.z = ((-(Tz P.k P.r Bs.z) : ℝ) : ℂ) := by
      have e2 := Complex.conj_eq_iff_re.1 (Qx2.herm_star Bs.z Bs.z)
      simp only [Tz, neg_neg]; exact e2.symm
    have hbW : inWb P.k P.r b ∧ herm (Hpk P.k P.r) b Bs.z = 0 := by
      rw [hb]
      constructor
      · intro i hi
        simp only [SSn.prWv, SSn.wbP, Pi.add_apply, Pi.smul_apply, hz i hi, smul_eq_mul, mul_zero, add_zero]
        rw [if_neg (by omega)]
      · unfold SSn.prWv
        rw [Qx8.herm_add_left', Qx8.herm_smul_left', hzzT]
        have hT0 : ((Tz P.k P.r Bs.z : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
        field_simp
        push_cast
        ring
    set s : ℝ := Real.sqrt (PRho.nrmW P.k P.r Bs.z a) with hs
    have hs0 : 0 < s := Real.sqrt_pos.2 ha
    set c : ℂ := ((s⁻¹ : ℝ) : ℂ) with hc
    have hc0 : c ≠ 0 := by rw [hc]; exact_mod_cast (inv_pos.2 hs0).ne'
    have hbb : herm (Hpk P.k P.r) b b = ((PRho.nrmW P.k P.r Bs.z a : ℝ) : ℂ) := by
      have e1 : star (herm (Hpk P.k P.r) b b) = herm (Hpk P.k P.r) b b := Qx2.herm_star b b
      have e2 := Complex.conj_eq_iff_re.1 e1
      rw [← e2]; rfl
    have he1 : inWb P.k P.r (c • b) := fun i hi => by simp [hbW.1 i hi]
    have he2 : herm (Hpk P.k P.r) (c • b) Bs.z = 0 := by rw [Qx8.herm_smul_left', hbW.2, mul_zero]
    have he3 : herm (Hpk P.k P.r) (c • b) (c • b) = 1 := by
      rw [Qx8.herm_smul_left', Qx8.herm_smul_right', hbb, hc, Complex.star_def, Complex.conj_ofReal]
      have hss : s * s = PRho.nrmW P.k P.r Bs.z a := Real.mul_self_sqrt ha.le
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← hss]
      field_simp
      norm_num
    have hfe : IsFrameOf P.k P.r [Bs.z, c • b] (Fr a) := (frame_smul hc0).2 hfa
    have hCv : ∀ v, C (Fr a) v = capRep P.k P.r Bs.π (Fr a) w v :=
      hCeq (Fr a) (Qx8.frame_sub hfa (by simp))
    rw [hLag Wp Bs.z (c • b) Bs.π hz hT hπ he1 he2 he3 (Fr a) hfe (C (Fr a)) hCv ρ]
    show PrDef P Bs.z Bs.π ρ a = _
    unfold PrDef
    rw [if_pos ha]
    exact sp_congr (K_smul hc0 _ _).symm
  ·
    intro h hh ρ a
    have hn : PRho.nrmW P.k P.r Bs.z (h *ᵥ a) = PRho.nrmW P.k P.r Bs.z a := hNF.2 h hh a
    show PrDef P Bs.z Bs.π ρ (h *ᵥ a) = (Bs.π h).comp ((PrDef P Bs.z Bs.π ρ a).comp (Bs.π h⁻¹))
    unfold PrDef
    rw [hn]
    split_ifs with ha
    · refine (sp_congr ?_).trans (proj_uw hrep hcont hunit hh)
      rw [kap_prWv_mulVec hz hh a]
    · ext x; simp
  · intro a ha
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro ρ c hc
      have hpos : 0 < PRho.nrmW P.k P.r Bs.z (c • a) := by
        rw [nrmW_smul]; exact mul_pos (Complex.normSq_pos.2 hc) ha
      show PrDef P Bs.z Bs.π ρ (c • a) = PrDef P Bs.z Bs.π ρ a
      unfold PrDef
      rw [if_pos hpos, if_pos ha]
      exact sp_congr (by rw [SSn.Geom.prWv_eq, SSn.Geom.prW_smul, ← SSn.Geom.prWv_eq]; exact K_smul hc _ _)
    · intro ρ x y
      show inner ℂ (PrDef P Bs.z Bs.π ρ a x) y = inner ℂ x (PrDef P Bs.z Bs.π ρ a y)
      unfold PrDef
      rw [if_pos ha]
      exact Submodule.inner_starProjection_left_eq_right _ x y
    · intro ρ ρ'
      show (PrDef P Bs.z Bs.π ρ a).comp (PrDef P Bs.z Bs.π ρ' a) = if ρ = ρ' then PrDef P Bs.z Bs.π ρ a else 0
      unfold PrDef
      rw [if_pos ha, if_pos ha]
      split_ifs with hρ
      · subst hρ
        ext x
        simp only [ContinuousLinearMap.comp_apply]
        exact Submodule.starProjection_eq_self_iff.2 (Submodule.starProjection_apply_mem _ x)
      · ext x
        simp only [ContinuousLinearMap.comp_apply, zero_apply]
        rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.mem_orthogonal]
        intro u hu
        have hu' := (mem_K hrep hcont).1 hu
        have hv' := (mem_K hrep hcont).1 (Submodule.starProjection_apply_mem
          (K P.k P.r Bs.z (SSn.prWv P.k P.r Bs.z a) Bs.π (fun w => M.xC P ρ' (w - ((P.k : ℂ) - 2) / 2))) x)
        obtain ⟨Y, hY⟩ := Qx8.xC_sep hOK hρ
        refine hO Wp P.k P.r Bs.z (SSn.prWv P.k P.r Bs.z a) Bs.π hz hT ⟨hrep, hcont⟩ hunit (hfr a ha) _ _ u _ hu' hv'
          ⟨Y + ((P.k : ℂ) - 2) / 2, ?_⟩
        simpa using hY
    · intro ρ x
      show PrDef P Bs.z Bs.π ρ a x = x ↔ _
      unfold PrDef
      rw [if_pos ha, Submodule.starProjection_eq_self_iff, mem_K hrep hcont]
      exact Iff.rfl

end Formalism.FourierDecayAlt.P.CutMP.JA.PRhoCut
