import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftRuleLevelPoint
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RdVOfEq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RootVectorActionCutoff
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGHead
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AestronglyMeasurableGermIntegrand

open Matrix Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.Qx5

section alg

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Q.Mx k r)}

variable (E) in

abbrev SB (hD : IsOpen D) : Subalgebra ℂ (Module.End ℂ (VS k r 0 D E)) :=
  Algebra.adjoin ℂ (Set.range fun pq : Fin (2 * r + k + 1) × Fin (2 * r + k + 1) => (PBG.E0 (E := E) hD pq.1 pq.2))

def EB (hD : IsOpen D) (p q : Fin (2 * r + k + 1)) : SB E hD :=
  ⟨PBG.E0 hD p q, Algebra.subset_adjoin ⟨(p, q), rfl⟩⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem EB_val (hD : IsOpen D) (p q : Fin (2 * r + k + 1)) :
    ((EB (E := E) hD p q : SB E hD) : Module.End ℂ (VS k r 0 D E)) = PBG.E0 hD p q := rfl

/- English proof (translation)
Introduce `a b c d`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h` using `PBG.level_zero_derivation_relation (E := E) hD a b c d`. Simplify using `only [Subalgebra.coe_sub, Subalgebra.coe_mul, EB_val]`. Rewrite using `[h]`.

Use `congr 1`. Distinguish the cases in `hbc : b = c`. Rewrite using `[if_pos hbc, if_pos hbc]`. Both sides reduce to the same expression. Rewrite using `[if_neg hbc, if_neg hbc]`.

Both sides reduce to the same expression. Distinguish the cases in `hda : d = a`. Rewrite using `[if_pos hda, if_pos hda]`. Both sides reduce to the same expression. Rewrite using `[if_neg hda, if_neg hda]`.

Both sides reduce to the same expression.
-/
theorem EB_gl (hD : IsOpen D) : GlRel (EB (E := E) hD) := by
  intro a b c d
  apply Subtype.ext
  have h := PBG.level_zero_derivation_relation (E := E) hD a b c d
  simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, EB_val]
  rw [h]
  congr 1
  · by_cases hbc : b = c
    · rw [if_pos hbc, if_pos hbc]; rfl
    · rw [if_neg hbc, if_neg hbc]; rfl
  · by_cases hda : d = a
    · rw [if_pos hda, if_pos hda]; rfl
    · rw [if_neg hda, if_neg hda]; rfl

/- English proof (translation)
Unfold `C3.AAx`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Use `split_ifs`. Rewrite using `[map_smul, PBN.MC.map_qminor]`.

Simplify using the standard rewrite rules.
-/
theorem map_AAx {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (φ : A →ₐ[ℂ] B)
    (Eu : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (xi : Fin r → Fin (2 * r + k + 1) → ℂ) (m : ℕ)
    (hm : m ≤ r) (u : ℂ) :
    φ (C3.AAx k r Eu xi m hm u) = C3.AAx k r (fun p q => φ (Eu p q)) xi m hm u := by
  unfold C3.AAx
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs
  · rw [map_smul, PBN.MC.map_qminor]
  · simp

/- English proof (translation)
Unfold `PBP.dz`. Distinguish the cases in `hd : DifferentiableAt ℝ f t`. Rewrite using `[show (fun τ => c • f τ) = c • f from rfl, fderiv_const_smul hd]`. Simplify using `only [ContinuousLinearMap.smul_apply, smul_sub, smul_comm c Complex.I, smul_comm c (1 / 2 : ℂ)]`. Establish `hd' : ¬ DifferentiableAt ℝ (fun τ => c • f τ) t`.

Introduce `h`. Apply `hd` to reduce the goal to its premises. Use `h.const_smul c⁻¹` as an intermediate fact. Establish `e : (c⁻¹ • fun τ => c • f τ) = f` using `by funext τ; simp [smul_smul, inv_mul_cancel₀ hc]`. Rewrite `this` using `[e]`. Then use the resulting hypothesis.

Rewrite using `[fderiv_zero_of_not_differentiableAt hd, fderiv_zero_of_not_differentiableAt hd']`. Simplify using the standard rewrite rules.
-/
theorem dz_const_smul (f : ℂ → E) (c : ℂ) (hc : c ≠ 0) (t : ℂ) :
    PBP.dz (fun τ => c • f τ) t = c • PBP.dz f t := by
  unfold PBP.dz
  by_cases hd : DifferentiableAt ℝ f t
  · rw [show (fun τ => c • f τ) = c • f from rfl, fderiv_const_smul hd]
    simp only [ContinuousLinearMap.smul_apply, smul_sub, smul_comm c Complex.I, smul_comm c (1 / 2 : ℂ)]
  · have hd' : ¬ DifferentiableAt ℝ (fun τ => c • f τ) t := by
      intro h
      apply hd
      have := h.const_smul c⁻¹
      have e : (c⁻¹ • fun τ => c • f τ) = f := by funext τ; simp [smul_smul, inv_mul_cancel₀ hc]
      rwa [e] at this
    rw [fderiv_zero_of_not_differentiableAt hd, fderiv_zero_of_not_differentiableAt hd']
    simp

end alg

section plus

variable {k r j : ℕ}

/- English proof (translation)
Establish `hne : ∀ᶠ τ' in 𝓝 τ, τ' ≠ 0` using `isOpen_ne.mem_nhds hτ`. Establish `hcont : ContinuousAt (fun τ' => x0 k r j hj Z τ' γ) τ`. Establish `hf : Continuous (fun τ' : {τ' : ℂ // τ' ≠ 0} => zfull Z τ'.1)`. Use `continuous_pi fun a => continuous_pi fun b => ?_` and prove the remaining obligations. Simplify using `only [zfull_apply]`.

Use `split_ifs`. Conclude with `continuous_const`. Conclude with `continuous_subtype_val`. Conclude with `continuous_const`. Establish `hfi : Continuous (fun τ' : {τ' : ℂ // τ' ≠ 0} => zfull (Zᴴ)⁻¹ (star τ'.1)⁻¹)`.

Use `continuous_pi fun a => continuous_pi fun b => ?_` and prove the remaining obligations. Simplify using `only [zfull_apply]`. Use `split_ifs`. Conclude with `continuous_const`. Conclude with `(continuous_star.comp continuous_subtype_val).inv₀ fun τ' => star_ne_zero.mpr τ'.2`.

Conclude with `continuous_const`. Establish `hm` using `LeftFubiniLemmas.mMap_cont (k := k) (ρ := r - (j + 1)) hf hfi (fun τ' => (zfull_conjTranspose_inv hZ τ'.2).symm) (continuous_const (y := γ))`. Establish `hc : Continuous (fun τ' : {τ' : ℂ // τ' ≠ 0} => x0 k r j hj Z τ'.1 γ)` using `(Formalism.FourierDecayAlt.P.PBH.castM_cont _).comp hm`. Establish `hon : ContinuousOn (fun τ' => x0 k r j hj Z τ' γ) {τ' : ℂ | τ' ≠ 0}` using `continuousOn_iff_continuous_restrict.mpr hc`. Conclude with `hon.continuousAt (isOpen_ne.mem_nhds hτ)`.

Use `filter_upwards [hne, hcont.preimage_mem_nhds (hD.mem_nhds hx)] with τ' h1 h2`. Conclude with `⟨h1, h2⟩`.
-/
theorem eventually_level_point_mem_open (hj : j + 1 ≤ r) {Z : Matrix (Fin j) (Fin j) ℂ} (hZ : Z.det ≠ 0) {τ : ℂ} (hτ : τ ≠ 0)
    (γ : B.Mat k (r - (j + 1))) {Dm : Set (Q.Mx k r)} (hD : IsOpen Dm) (hx : x0 k r j hj Z τ γ ∈ Dm) :
    ∀ᶠ τ' in 𝓝 τ, τ' ≠ 0 ∧ x0 k r j hj Z τ' γ ∈ Dm := by
  have hne : ∀ᶠ τ' in 𝓝 τ, τ' ≠ 0 := isOpen_ne.mem_nhds hτ
  have hcont : ContinuousAt (fun τ' => x0 k r j hj Z τ' γ) τ := by
    have hf : Continuous (fun τ' : {τ' : ℂ // τ' ≠ 0} => zfull Z τ'.1) := by
      refine continuous_pi fun a => continuous_pi fun b => ?_
      simp only [zfull_apply]
      split_ifs
      · exact continuous_const
      · exact continuous_subtype_val
      · exact continuous_const
    have hfi : Continuous (fun τ' : {τ' : ℂ // τ' ≠ 0} => zfull (Zᴴ)⁻¹ (star τ'.1)⁻¹) := by
      refine continuous_pi fun a => continuous_pi fun b => ?_
      simp only [zfull_apply]
      split_ifs
      · exact continuous_const
      · exact (continuous_star.comp continuous_subtype_val).inv₀ fun τ' => star_ne_zero.mpr τ'.2
      · exact continuous_const
    have hm := LeftFubiniLemmas.mMap_cont (k := k) (ρ := r - (j + 1)) hf hfi
      (fun τ' => (zfull_conjTranspose_inv hZ τ'.2).symm) (continuous_const (y := γ))
    have hc : Continuous (fun τ' : {τ' : ℂ // τ' ≠ 0} => x0 k r j hj Z τ'.1 γ) :=
      (Formalism.FourierDecayAlt.P.PBH.castM_cont _).comp hm
    have hon : ContinuousOn (fun τ' => x0 k r j hj Z τ' γ) {τ' : ℂ | τ' ≠ 0} :=
      continuousOn_iff_continuous_restrict.mpr hc
    exact hon.continuousAt (isOpen_ne.mem_nhds hτ)
  filter_upwards [hne, hcont.preimage_mem_nhds (hD.mem_nhds hx)] with τ' h1 h2
  exact ⟨h1, h2⟩

end plus

section main

variable {k r j : ℕ}

/- English proof (translation)
Introduce `hNf hDmn hL hT hFr k r j hj z z' E _ _ Dm Φ Z γ τ hj1 hH Y`. Take `⟨hz, hz', hD, hDs, ⟨hS, hRe, hLe⟩, hZ, hτ, hγ, hx⟩` from `hH`. Take `⟨m, rfl⟩ : ∃ m, j = m + 1` from `⟨j - 1, by omega⟩`. Use `set x₁ := x0 k r (m + 1) hj Z τ γ with hx₁`. Establish `hxG : x₁ ∈ Q.Glev k r 0` using `SingleEntryHermitianProducts.glev0 (x0_GV hj hZ hτ hγ)`.

Establish `hxGD : x₁ ∈ Q.Glev k r 0 ∩ Dm` using `⟨hxG, hx⟩`. Use `set u : ℂ := (Y : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2 with hu`. Establish `hR : ∀ g ∈ Q.Glev k r 0 ∩ Dm, ∀ p q, C3.InNp k r p q → Q.EH k r p q Φ g = C3.dpsiP k r z' p q • Φ g` using `fun g hg p q hpq => Formalism.FourierDecayAlt.P.rule_of_eq E k r z' Φ g hz' (fun n hn => (hRe g hg n hn).2) p q hpq`. Use `set v₀ := PBG.vK hD Φ hS with hv₀`. Set `La' : SB E hD →ₗ[ℂ] E` to `(PBG.La hD Φ hS x₁).comp (SB E hD).val.toLinearMap`.

Establish `hLa' : ∀ x : SB E hD, La' x = (((x : Module.End ℂ (VS k r 0 Dm E)) v₀ : VS k r 0 Dm E) : Q.Mx k r → E) x₁` using `fun x => rfl`. Establish `hRR : C3.RightRuleFn k r z' (EB hD) La'`. Introduce `x p q hpq`. Conclude with `PBG.La_rule hD z' Φ hS hR x₁ x.1 p q hpq`. Establish `hAA : ∀ (n : ℕ) (hn : n ≤ r), La' (C3.AAx k r (EB hD) (PBG.xi0 x₁) n hn u) = C3.AAop k r n hn u Φ x₁`.

Introduce `n hn`. Use `show PBG.La hD Φ hS x₁ ((SB E hD).val (C3.AAx k r (EB hD) (PBG.xi0 x₁) n hn u)) = _`. Rewrite using `[map_AAx]`. Conclude with `PBG.La_AAx hD Φ hS x₁ hxGD n hn u`. Establish `hvK : ∀ g ∈ Q.Glev k r 0 ∩ Dm, ∀ a : Fin (m + 1) → ℂ, (v₀ : Q.Mx k r → E) (nL k r (m + 1) hj a * g) = psi k r z cStd (nL k r (m + 1) hj a) • (v₀ : Q.Mx k r → E) g`.

Introduce `g hg a`. Establish `hng : nL k r (m + 1) hj a * g ∈ Q.Glev k r 0 ∩ Dm` using `⟨Formalism.FourierDecayAlt.P.Qx3.glev_mul (HeadLetterLemmas.nL_glev0 hj a) hg.1, (hLe g hg a).1⟩`. Use `show cut k r 0 Dm Φ _ = _ • cut k r 0 Dm Φ g`. Rewrite using `[cut_of_mem Φ hng, cut_of_mem Φ hg, (hLe g hg a).2]`. Establish `hxEq : ∀ x : SB E hD, ∀ a : Fin (m + 1) → ℂ, (((x : Module.End ℂ (VS k r 0 Dm E)) v₀ : VS k r 0 Dm E) : Q.Mx k r → E) (nL k r (m + 1) hj a * x₁) = psi k r z cStd (nL k r (m + 1) hj a) • (((x : Module.End ℂ (VS k r 0 Dm E)) v₀ : VS k r 0 Dm E) : Q.Mx k r → E) x₁` using `fun x a => Formalism.FourierDecayAlt.P.adjoin_lower_unipotent E k r (m + 1) hj z Dm hD (fun g hg a => (hLe g hg a).1) x.1 x.2 v₀ hvK x₁ hxGD a`.

Establish `hLL : ∀ (b : Fin (m + 1)) (x : SB E hD), La' (EB hD (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨b, by omega⟩) * x) = (τ * Z⁻¹ b (Fin.last m)) • La' x`. Introduce `b x`. Rewrite using `[hLa', hLa']`. Use `show ((PBG.E0 hD _ _ ((x : Module.End ℂ (VS k r 0 Dm E)) v₀) : VS k r 0 Dm E) : Q.Mx k r → E) x₁ = _`. Rewrite using `[PBG.E0, ev_E hD _ _ _ hxGD, PBG.position_level_zero_coord, PBG.position_level_zero_coord]`.

Establish `h` using `hL E k r (m + 1) hj z Dm _ Z τ γ hj1 hz hD ((x : Module.End ℂ (VS k r 0 Dm E)) v₀).2.1 hZ hτ hγ hx (hxEq x) b`. Rewrite using `[h]`. Both sides reduce to the same expression. Establish `hxi : ∀ (a : Fin (m + 1)) (q : Fin (2 * r + k + 1)), PBG.xi0 x₁ ⟨a, by omega⟩ q = if h : q.val < m + 1 then Z a ⟨q, h⟩ else 0`. Introduce `a q`.

Rewrite using `[hx₁, upper_minor_of_level_point hj Z τ γ ⟨a, by omega⟩ q (by show a.val < m + 1 + 1; omega)]`. Distinguish the cases in `hq : q.val < m + 1`. Rewrite using `[dif_pos (by omega), dif_pos hq, zfull_apply, dif_pos ⟨a.isLt, hq⟩]`. Rewrite using `[dif_neg hq] split_ifs with h1`. Rewrite using `[zfull_apply, dif_neg (by simp; omega), if_neg (by simp; omega)]`.

Both sides reduce to the same expression. Establish `hxl : ∀ q : Fin (2 * r + k + 1), PBG.xi0 x₁ ⟨m + 1, by omega⟩ q = if q.val = m + 1 then τ else 0`. Introduce `q`. Rewrite using `[hx₁, upper_minor_of_level_point hj Z τ γ ⟨m + 1, by omega⟩ q (by simp)]`. Distinguish the cases in `hq : q.val = m + 1`.

Rewrite using `[dif_pos (by omega), if_pos hq, zfull_apply, dif_neg (by simp), if_pos ⟨rfl, hq⟩]`. Rewrite using `[if_neg hq] split_ifs with h1`. Rewrite using `[zfull_apply, dif_neg (by simp), if_neg (by simp; omega)]`. Both sides reduce to the same expression. Establish `hHA` using `Formalism.FourierDecayAlt.P.head_algebra_relations (SB E hD) E k r m (by omega) z' (EB hD) La' (PBG.xi0 x₁) Z τ u (EB_gl hD) hRR hZ hτ hLL hxi hxl`.

Use `set y := C3.AAx k r (EB (E := E) hD) (PBG.xi0 x₁) (m + 1) (by omega) u with hy`. Establish `hcomm` using `(hFr (SB E hD) k r (m + 1) hj (EB (E := E) hD) Z τ τ u γ (EB_gl hD) hZ hτ hτ hγ).2`. Establish `hyE : y * EB (E` using `E) hD (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩) = EB (E := E) hD (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩) * y := hcomm.symm`. Establish `hT1 : La' (EB (E` using `E) hD (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩) * y) = τ • PBP.dz (fun τ' => (((y : Module.End ℂ (VS k r 0 Dm E)) v₀ : VS k r 0 Dm E) : Q.Mx k r → E) (x0 k r (m + 1) hj Z τ' γ)) τ := by`. Rewrite using `[hLa']`.

Use `show ((PBG.E0 hD _ _ ((y : Module.End ℂ (VS k r 0 Dm E)) v₀) : VS k r 0 Dm E) : Q.Mx k r → E) x₁ = _`. Rewrite using `[PBG.E0, ev_E hD _ _ _ hxGD, PBG.position_level_zero_coord]`. Conclude with `hT E k r (m + 1) hj Dm _ Z τ γ hD ((y : Module.End ℂ (VS k r 0 Dm E)) v₀).2.1 hZ hτ hγ hx`. Establish `hev : (fun τ' => (((y : Module.End ℂ (VS k r 0 Dm E)) v₀ : VS k r 0 Dm E) : Q.Mx k r → E) (x0 k r (m + 1) hj Z τ' γ)) =ᶠ[𝓝 τ] fun τ' => C3.AAop k r (m + 1) (by omega) u Φ (x0 k r (m + 1) hj Z τ' γ)` using `by filter_upwards [eventually_level_point_mem_open hj hZ hτ γ hD hx] with τ' ⟨hτ', hx'⟩`. Establish `hxGD' : x0 k r (m + 1) hj Z τ' γ ∈ Q.Glev k r 0 ∩ Dm` using `⟨SingleEntryHermitianProducts.glev0 (x0_GV hj hZ hτ' hγ), hx'⟩`.

Establish `hy' : y = C3.AAx k r (EB (E` using `E) hD) (PBG.xi0 (x0 k r (m + 1) hj Z τ' γ)) (m + 1) (by omega) u := ((hFr (SB E hD) k r (m + 1) hj (EB (E := E) hD) Z τ τ' u γ (EB_gl hD) hZ hτ hτ' hγ).1).symm`. Establish `h1 : (((y : Module.End ℂ (VS k r 0 Dm E)) v₀ : VS k r 0 Dm E) : Q.Mx k r → E) (x0 k r (m + 1) hj Z τ' γ) = C3.AAop k r (m + 1) (by omega) u Φ (x0 k r (m + 1) hj Z τ' γ)`. Rewrite using `[hy']`. Use `show PBG.La hD Φ hS _ ((SB E hD).val (C3.AAx k r (EB (E := E) hD) _ (m + 1) _ u)) = _`. Rewrite using `[map_AAx]`.

Conclude with `PBG.La_AAx hD Φ hS _ hxGD' (m + 1) _ u`. Conclude with `h1`. Establish `hdz : PBP.dz (fun τ' => (((y : Module.End ℂ (VS k r 0 Dm E)) v₀ : VS k r 0 Dm E) : Q.Mx k r → E) (x0 k r (m + 1) hj Z τ' γ)) τ = PBP.dz (fun τ' => C3.AAop k r (m + 1) (by omega) u Φ (x0 k r (m + 1) hj Z τ' γ)) τ`. Unfold `PBP.dz`. Rewrite using `[hev.fderiv_eq]`.

Establish `hvj : (fun τ' => D.vLet k r z z' (m + 1) (by omega) (true, Y) 0 Φ (x0 k r (m + 1) hj Z τ' γ)) =ᶠ[𝓝 τ] fun τ' => (Z.det)⁻¹ • C3.AAop k r (m + 1) (by omega) u Φ (x0 k r (m + 1) hj Z τ' γ)` using `by filter_upwards [eventually_level_point_mem_open hj hZ hτ γ hD hx] with τ' ⟨hτ', _⟩`. Rewrite using `[PBG.letter_plus_component_zero, (hDmn k r (m + 1) hj z z' Z τ' γ hZ hτ' hγ).1]`. Establish `hdzv : PBP.dz (fun τ' => D.vLet k r z z' (m + 1) (by omega) (true, Y) 0 Φ (x0 k r (m + 1) hj Z τ' γ)) τ = (Z.det)⁻¹ • PBP.dz (fun τ' => C3.AAop k r (m + 1) (by omega) u Φ (x0 k r (m + 1) hj Z τ' γ)) τ`. Use `dz_const_smul (fun τ' => C3.AAop k r (m + 1) (by omega) u Φ (x0 k r (m + 1) hj Z τ' γ)) (Z.det)⁻¹ (inv_ne_zero hZ) τ` as an intermediate fact. Unfold `PBP.dz at this ⊢`.

Rewrite using `[hvj.fderiv_eq]`. Conclude with `this`. Establish `hv2 : D.vLet k r z z' (m + 1 + 1) hj (true, Y) 0 Φ x₁ = (Z.det * τ)⁻¹ • C3.AAop k r (m + 1 + 1) hj u Φ x₁`. Rewrite using `[PBG.letter_plus_component_zero, (hDmn k r (m + 1) hj z z' Z τ γ hZ hτ hγ).2]`. Establish `hv1 : D.vLet k r z z' (m + 1) (by omega) (true, Y) 0 Φ x₁ = (Z.det)⁻¹ • C3.AAop k r (m + 1) (by omega) u Φ x₁`.

Rewrite using `[PBG.letter_plus_component_zero, (hDmn k r (m + 1) hj z z' Z τ γ hZ hτ hγ).1]`. Establish `hv0 : D.vLet k r z z' (m + 1) (by omega) (true, Y) 1 Φ x₁ = (Z.det)⁻¹ • C3.AAop k r m (by omega) u Φ x₁`. Rewrite using `[PBG.letter_plus_component_one z z' (m + 1) (by omega) (by omega) Y Φ x₁, (hDmn k r (m + 1) hj z z' Z τ γ hZ hτ hγ).1, PBG.AAop_congr' (show m + 1 - 1 = m by omega)]`. Establish `hmid : La' (y * (algebraMap ℂ (SB E hD) (u - ((m + 1 : ℕ) : ℂ)) + EB (E` using `E) hD (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩))) = (u - ((m + 1 : ℕ) : ℂ)) • C3.AAop k r (m + 1) (by omega) u Φ x₁ + τ • PBP.dz (fun τ' => C3.AAop k r (m + 1) (by omega) u Φ (x0 k r (m + 1) hj Z τ' γ)) τ := by`. Rewrite using `[mul_add, map_add, ← Algebra.commutes, ← Algebra.smul_def, map_smul, hyE, hT1, hdz, hy, hAA]`.

Rewrite `hHA` using `[hmid, hAA, hAA]`. Establish `hk : u - ((m + 1 : ℕ) : ℂ) = (Y : ℂ) + levelZeroKernel k r (m + 1)`. Simplify using `only [hu, levelZeroKernel]`. Move the coercions through the operations in `[Nat.cast_sub (show m + 1 ≤ r by omega)]`. Expand and normalize the polynomial expressions, which then agree.

Use `show D.vLet k r z z' (m + 1 + 1) hj (true, Y) 0 Φ x₁ = ((Y : ℂ) + levelZeroKernel k r (m + 1)) • D.vLet k r z z' (m + 1) (by omega) (true, Y) 0 Φ x₁ + τ • PBP.dz (fun τ' => D.vLet k r z z' (m + 1) (by omega) (true, Y) 0 Φ (x0 k r (m + 1) hj Z τ' γ)) τ - τ • D.vLet k r z z' (m + 1 …`. Rewrite using `[hv2, hv1, hdzv, hv0]`. Establish `hHA' : (Z.det * τ)⁻¹ • C3.AAop k r (m + 1 + 1) hj u Φ x₁ = (Z.det)⁻¹ • ((u - ((m + 1 : ℕ) : ℂ)) • C3.AAop k r (m + 1) (by omega) u Φ x₁ + τ • PBP.dz (fun τ' => C3.AAop k r (m + 1) (by omega) u Φ (x0 k r (m + 1) hj Z τ' γ)) τ) - (τ * (Z.det)⁻¹) • C3.AAop k r m (by omega) u Φ x₁` using `hHA`. Rewrite using `[hHA', hk]`. Use `module`.
-/
theorem plusPosOfParts : CutHL.PlusPosOfParts := by
  intro hNf hDmn hL hT hFr k r j hj z z' E _ _ Dm Φ Z γ τ hj1 hH Y
  obtain ⟨hz, hz', hD, hDs, ⟨hS, hRe, hLe⟩, hZ, hτ, hγ, hx⟩ := hH
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  set x₁ := x0 k r (m + 1) hj Z τ γ with hx₁
  have hxG : x₁ ∈ Q.Glev k r 0 := SingleEntryHermitianProducts.glev0 (x0_GV hj hZ hτ hγ)
  have hxGD : x₁ ∈ Q.Glev k r 0 ∩ Dm := ⟨hxG, hx⟩
  set u : ℂ := (Y : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2 with hu

  have hR : ∀ g ∈ Q.Glev k r 0 ∩ Dm, ∀ p q, C3.InNp k r p q → Q.EH k r p q Φ g = C3.dpsiP k r z' p q • Φ g :=
    fun g hg p q hpq => Formalism.FourierDecayAlt.P.rule_of_eq E k r z' Φ g hz' (fun n hn => (hRe g hg n hn).2) p q hpq

  set v₀ := PBG.vK hD Φ hS with hv₀
  let La' : SB E hD →ₗ[ℂ] E := (PBG.La hD Φ hS x₁).comp (SB E hD).val.toLinearMap
  have hLa' : ∀ x : SB E hD, La' x = (((x : Module.End ℂ (VS k r 0 Dm E)) v₀ : VS k r 0 Dm E) : Q.Mx k r → E) x₁ :=
    fun x => rfl
  have hRR : C3.RightRuleFn k r z' (EB hD) La' := by
    intro x p q hpq
    exact PBG.La_rule hD z' Φ hS hR x₁ x.1 p q hpq

  have hAA : ∀ (n : ℕ) (hn : n ≤ r), La' (C3.AAx k r (EB hD) (PBG.xi0 x₁) n hn u) = C3.AAop k r n hn u Φ x₁ := by
    intro n hn
    show PBG.La hD Φ hS x₁ ((SB E hD).val (C3.AAx k r (EB hD) (PBG.xi0 x₁) n hn u)) = _
    rw [map_AAx]
    exact PBG.La_AAx hD Φ hS x₁ hxGD n hn u

  have hvK : ∀ g ∈ Q.Glev k r 0 ∩ Dm, ∀ a : Fin (m + 1) → ℂ, (v₀ : Q.Mx k r → E) (nL k r (m + 1) hj a * g) =
      psi k r z cStd (nL k r (m + 1) hj a) • (v₀ : Q.Mx k r → E) g := by
    intro g hg a
    have hng : nL k r (m + 1) hj a * g ∈ Q.Glev k r 0 ∩ Dm :=
      ⟨Formalism.FourierDecayAlt.P.Qx3.glev_mul (HeadLetterLemmas.nL_glev0 hj a) hg.1, (hLe g hg a).1⟩
    show cut k r 0 Dm Φ _ = _ • cut k r 0 Dm Φ g
    rw [cut_of_mem Φ hng, cut_of_mem Φ hg, (hLe g hg a).2]
  have hxEq : ∀ x : SB E hD, ∀ a : Fin (m + 1) → ℂ,
      (((x : Module.End ℂ (VS k r 0 Dm E)) v₀ : VS k r 0 Dm E) : Q.Mx k r → E) (nL k r (m + 1) hj a * x₁) =
        psi k r z cStd (nL k r (m + 1) hj a) • (((x : Module.End ℂ (VS k r 0 Dm E)) v₀ : VS k r 0 Dm E) : Q.Mx k r → E) x₁ :=
    fun x a => Formalism.FourierDecayAlt.P.adjoin_lower_unipotent E k r (m + 1) hj z Dm hD (fun g hg a => (hLe g hg a).1) x.1 x.2 v₀ hvK
      x₁ hxGD a

  have hLL : ∀ (b : Fin (m + 1)) (x : SB E hD),
      La' (EB hD (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨b, by omega⟩) * x) = (τ * Z⁻¹ b (Fin.last m)) • La' x := by
    intro b x
    rw [hLa', hLa']
    show ((PBG.E0 hD _ _ ((x : Module.End ℂ (VS k r 0 Dm E)) v₀) : VS k r 0 Dm E) : Q.Mx k r → E) x₁ = _
    rw [PBG.E0, ev_E hD _ _ _ hxGD, PBG.position_level_zero_coord, PBG.position_level_zero_coord]
    have h := hL E k r (m + 1) hj z Dm _ Z τ γ hj1 hz hD ((x : Module.End ℂ (VS k r 0 Dm E)) v₀).2.1 hZ hτ hγ hx
      (hxEq x) b
    rw [h]
    rfl

  have hxi : ∀ (a : Fin (m + 1)) (q : Fin (2 * r + k + 1)),
      PBG.xi0 x₁ ⟨a, by omega⟩ q = if h : q.val < m + 1 then Z a ⟨q, h⟩ else 0 := by
    intro a q
    rw [hx₁, upper_minor_of_level_point hj Z τ γ ⟨a, by omega⟩ q (by show a.val < m + 1 + 1; omega)]
    by_cases hq : q.val < m + 1
    · rw [dif_pos (by omega), dif_pos hq, zfull_apply, dif_pos ⟨a.isLt, hq⟩]
    · rw [dif_neg hq]
      split_ifs with h1
      · rw [zfull_apply, dif_neg (by simp; omega), if_neg (by simp; omega)]
      · rfl
  have hxl : ∀ q : Fin (2 * r + k + 1), PBG.xi0 x₁ ⟨m + 1, by omega⟩ q = if q.val = m + 1 then τ else 0 := by
    intro q
    rw [hx₁, upper_minor_of_level_point hj Z τ γ ⟨m + 1, by omega⟩ q (by simp)]
    by_cases hq : q.val = m + 1
    · rw [dif_pos (by omega), if_pos hq, zfull_apply, dif_neg (by simp), if_pos ⟨rfl, hq⟩]
    · rw [if_neg hq]
      split_ifs with h1
      · rw [zfull_apply, dif_neg (by simp), if_neg (by simp; omega)]
      · rfl

  have hHA := Formalism.FourierDecayAlt.P.head_algebra_relations (SB E hD) E k r m (by omega) z' (EB hD) La' (PBG.xi0 x₁) Z τ u
    (EB_gl hD) hRR hZ hτ hLL hxi hxl

  set y := C3.AAx k r (EB (E := E) hD) (PBG.xi0 x₁) (m + 1) (by omega) u with hy
  have hcomm := (hFr (SB E hD) k r (m + 1) hj (EB (E := E) hD) Z τ τ u γ (EB_gl hD) hZ hτ hτ hγ).2
  have hyE : y * EB (E := E) hD (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩) =
      EB (E := E) hD (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩) * y := hcomm.symm
  have hT1 : La' (EB (E := E) hD (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩) * y) =
      τ • PBP.dz (fun τ' => (((y : Module.End ℂ (VS k r 0 Dm E)) v₀ : VS k r 0 Dm E) : Q.Mx k r → E)
        (x0 k r (m + 1) hj Z τ' γ)) τ := by
    rw [hLa']
    show ((PBG.E0 hD _ _ ((y : Module.End ℂ (VS k r 0 Dm E)) v₀) : VS k r 0 Dm E) : Q.Mx k r → E) x₁ = _
    rw [PBG.E0, ev_E hD _ _ _ hxGD, PBG.position_level_zero_coord]
    exact hT E k r (m + 1) hj Dm _ Z τ γ hD ((y : Module.End ℂ (VS k r 0 Dm E)) v₀).2.1 hZ hτ hγ hx
  have hev : (fun τ' => (((y : Module.End ℂ (VS k r 0 Dm E)) v₀ : VS k r 0 Dm E) : Q.Mx k r → E)
        (x0 k r (m + 1) hj Z τ' γ)) =ᶠ[𝓝 τ]
      fun τ' => C3.AAop k r (m + 1) (by omega) u Φ (x0 k r (m + 1) hj Z τ' γ) := by
    filter_upwards [eventually_level_point_mem_open hj hZ hτ γ hD hx] with τ' ⟨hτ', hx'⟩
    have hxGD' : x0 k r (m + 1) hj Z τ' γ ∈ Q.Glev k r 0 ∩ Dm := ⟨SingleEntryHermitianProducts.glev0 (x0_GV hj hZ hτ' hγ), hx'⟩
    have hy' : y = C3.AAx k r (EB (E := E) hD) (PBG.xi0 (x0 k r (m + 1) hj Z τ' γ)) (m + 1) (by omega) u :=
      ((hFr (SB E hD) k r (m + 1) hj (EB (E := E) hD) Z τ τ' u γ (EB_gl hD) hZ hτ hτ' hγ).1).symm
    have h1 : (((y : Module.End ℂ (VS k r 0 Dm E)) v₀ : VS k r 0 Dm E) : Q.Mx k r → E) (x0 k r (m + 1) hj Z τ' γ) =
        C3.AAop k r (m + 1) (by omega) u Φ (x0 k r (m + 1) hj Z τ' γ) := by
      rw [hy']
      show PBG.La hD Φ hS _ ((SB E hD).val (C3.AAx k r (EB (E := E) hD) _ (m + 1) _ u)) = _
      rw [map_AAx]
      exact PBG.La_AAx hD Φ hS _ hxGD' (m + 1) _ u
    exact h1
  have hdz : PBP.dz (fun τ' => (((y : Module.End ℂ (VS k r 0 Dm E)) v₀ : VS k r 0 Dm E) : Q.Mx k r → E)
      (x0 k r (m + 1) hj Z τ' γ)) τ =
      PBP.dz (fun τ' => C3.AAop k r (m + 1) (by omega) u Φ (x0 k r (m + 1) hj Z τ' γ)) τ := by
    unfold PBP.dz; rw [hev.fderiv_eq]
  have hvj : (fun τ' => D.vLet k r z z' (m + 1) (by omega) (true, Y) 0 Φ (x0 k r (m + 1) hj Z τ' γ)) =ᶠ[𝓝 τ]
      fun τ' => (Z.det)⁻¹ • C3.AAop k r (m + 1) (by omega) u Φ (x0 k r (m + 1) hj Z τ' γ) := by
    filter_upwards [eventually_level_point_mem_open hj hZ hτ γ hD hx] with τ' ⟨hτ', _⟩
    rw [PBG.letter_plus_component_zero, (hDmn k r (m + 1) hj z z' Z τ' γ hZ hτ' hγ).1]
  have hdzv : PBP.dz (fun τ' => D.vLet k r z z' (m + 1) (by omega) (true, Y) 0 Φ (x0 k r (m + 1) hj Z τ' γ)) τ =
      (Z.det)⁻¹ • PBP.dz (fun τ' => C3.AAop k r (m + 1) (by omega) u Φ (x0 k r (m + 1) hj Z τ' γ)) τ := by
    have := dz_const_smul (fun τ' => C3.AAop k r (m + 1) (by omega) u Φ (x0 k r (m + 1) hj Z τ' γ)) (Z.det)⁻¹
      (inv_ne_zero hZ) τ
    unfold PBP.dz at this ⊢
    rw [hvj.fderiv_eq]
    exact this
  have hv2 : D.vLet k r z z' (m + 1 + 1) hj (true, Y) 0 Φ x₁ = (Z.det * τ)⁻¹ • C3.AAop k r (m + 1 + 1) hj u Φ x₁ := by
    rw [PBG.letter_plus_component_zero, (hDmn k r (m + 1) hj z z' Z τ γ hZ hτ hγ).2]
  have hv1 : D.vLet k r z z' (m + 1) (by omega) (true, Y) 0 Φ x₁ = (Z.det)⁻¹ • C3.AAop k r (m + 1) (by omega) u Φ x₁ := by
    rw [PBG.letter_plus_component_zero, (hDmn k r (m + 1) hj z z' Z τ γ hZ hτ hγ).1]
  have hv0 : D.vLet k r z z' (m + 1) (by omega) (true, Y) 1 Φ x₁ = (Z.det)⁻¹ • C3.AAop k r m (by omega) u Φ x₁ := by
    rw [PBG.letter_plus_component_one z z' (m + 1) (by omega) (by omega) Y Φ x₁, (hDmn k r (m + 1) hj z z' Z τ γ hZ hτ hγ).1,
      PBG.AAop_congr' (show m + 1 - 1 = m by omega)]
  have hmid : La' (y * (algebraMap ℂ (SB E hD) (u - ((m + 1 : ℕ) : ℂ)) +
      EB (E := E) hD (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩))) =
      (u - ((m + 1 : ℕ) : ℂ)) • C3.AAop k r (m + 1) (by omega) u Φ x₁ +
        τ • PBP.dz (fun τ' => C3.AAop k r (m + 1) (by omega) u Φ (x0 k r (m + 1) hj Z τ' γ)) τ := by
    rw [mul_add, map_add, ← Algebra.commutes, ← Algebra.smul_def, map_smul, hyE, hT1, hdz, hy, hAA]
  rw [hmid, hAA, hAA] at hHA
  have hk : u - ((m + 1 : ℕ) : ℂ) = (Y : ℂ) + levelZeroKernel k r (m + 1) := by
    simp only [hu, levelZeroKernel]
    push_cast [Nat.cast_sub (show m + 1 ≤ r by omega)]
    ring
  show D.vLet k r z z' (m + 1 + 1) hj (true, Y) 0 Φ x₁ =
    ((Y : ℂ) + levelZeroKernel k r (m + 1)) • D.vLet k r z z' (m + 1) (by omega) (true, Y) 0 Φ x₁ +
      τ • PBP.dz (fun τ' => D.vLet k r z z' (m + 1) (by omega) (true, Y) 0 Φ (x0 k r (m + 1) hj Z τ' γ)) τ -
      τ • D.vLet k r z z' (m + 1) (by omega) (true, Y) 1 Φ x₁
  rw [hv2, hv1, hdzv, hv0]
  have hHA' : (Z.det * τ)⁻¹ • C3.AAop k r (m + 1 + 1) hj u Φ x₁ =
      (Z.det)⁻¹ • ((u - ((m + 1 : ℕ) : ℂ)) • C3.AAop k r (m + 1) (by omega) u Φ x₁ +
        τ • PBP.dz (fun τ' => C3.AAop k r (m + 1) (by omega) u Φ (x0 k r (m + 1) hj Z τ' γ)) τ) -
      (τ * (Z.det)⁻¹) • C3.AAop k r m (by omega) u Φ x₁ := hHA
  rw [hHA', hk]
  module

end main

end Formalism.FourierDecayAlt.P.LevelPointCoordinates
