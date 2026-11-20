import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CongruenceActionMemFrameOrbit
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelActionMemCuspForms
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUnifExpUnique
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEqNsmulOfDvdPairing
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsometryTriangularPeriodsOfFramePointMove

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open scoped Matrix

noncomputable section

namespace GlobalTheory.CongrOrbit

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c σ r U hσ hU hA _hr k γ hγ x hx`. Establish `hx' : lact γ x ∈ (U.X k).dom` using `dom_lact (U.X k) hx ((U.X k).Γ_stab γ hγ)`. Set `b₁ : Frame (U.X k).Ψ r` to `fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)`. Establish `hm₁ : ∀ τ, mat b₁ τ = 1` using `fun τ => rfl`. Establish `hb₁ : b₁ ∈ Bor (U.X k).Ψ r` using `fun τ => ⟨by rw [hm₁]; simp, fun a c hca => by`.

Use `hm₁ τ` as an intermediate fact. Express the relevant statement in the definitionally equal form `Matrix.of (b₁ τ) = 1 at this`. Establish `h2` using `congrFun (congrFun this a) c`. Simplify `h2⟩` using `[Matrix.one_apply_ne (ne_of_gt hca)]`. Establish `hrm : rmul (lact γ x) b₁ = lact γ x`.

Use function extensionality and compare the values at `τ`. Express the relevant statement in the definitionally equal form `mat (lact γ x) τ * mat b₁ τ = lact γ x τ`. Rewrite using `[hm₁, Matrix.mul_one]`. Both sides reduce to the same expression. Take `⟨t, hB⟩ : ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (U.un k ⟨x, hx⟩) (U.un k ⟨lact γ x, hx'⟩)` from `(hU.2.2.2.1 k k ⟨x, hx⟩ ⟨lact γ x, hx'⟩).2 ⟨γ, hγ, b₁, hb₁, by rw [hrm]⟩`.

Take `⟨hrr, hty, -, -, -, g, e, F, ik, φ, hEF, hpt⟩` from `hU`. Take `⟨P, hP, p, hPx, hv, -⟩` from `hpt k ⟨x, hx⟩`. Take `⟨P', hP', p', hPx', hv', -⟩` from `hpt k ⟨lact γ x, hx'⟩`. Establish `hu : F.u (ik k) P' = F.u (ik k) P` using `by rw [← hPx, ← hPx', hB.1]`. Take `⟨h, gam, hex, hh, hiso, hM, -⟩` from `GlobalTheory.T.familyUnif_exp_unique_alt E H Dw l Xo _ g _ F (ik k) (ik k) P' P p' p hu`.

Establish `hM' : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di (ik k)).La), ∃ e, gam a = a + l.M • e`. Introduce `a ha`. Use `Submodule.smul_induction_on ha ?_ ?_` and prove the remaining obligations. Introduce `v hv b _`. Take `⟨c, e, rfl⟩` from `F.t_surj (ik k) b`.

Take `⟨e₁, he₁⟩` from `hM (v • c) (Submodule.smul_mem_smul hv Submodule.mem_top)`. Take `⟨r, hr⟩ : l.M ∣ l.M'` from `Nat.dvd_lcm_left _ _`. Use `⟨e₁ + r • (gam (v • e) - v • e), ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add, ← map_smul, smul_comm v, map_add, he₁, map_nsmul, hr, smul_add, smul_smul, smul_sub]`. Normalize the expressions using the abelian group laws.

Introduce and unpack `x y ⟨e, he⟩ ⟨e', he'⟩`. Conclude with `⟨e + e', by rw [map_add, he, he', smul_add]; abel⟩`. Establish `f₁` using `GlobalTheory.LevelHalf.trivial_mod_of_trivial_on_half E H (F.Di (ik k)) l gam hiso hM'`. Use `choose cf hcf1 hcf2 hcf3 using hB.2.1`. Establish `hcol : ∀ τ i, h.toLinearMap (Pi.single (e.symm ⟨τ, i⟩) 1) = (∑ j, (show ℂ from cf τ i j) • (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ))`.

Introduce `τ i`. Establish `d1` using `(DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F _ P p _ ((U.un k ⟨x, hx⟩).u τ) _ (hv τ) (cf τ i) ((U.un k ⟨lact γ x, hx'⟩).u τ i)).1 (hPx ▸ hcf3 τ i)`. Establish `d0` using `hv' τ i`. Simplify using `only [← hex] at d0`. Establish `d2` using `(ExpChain.isDerivAt0_comp_linear _ (ExpChain.isHolTo_ex F _ P p) h.toLinearMap _ _).1 d0`.

Establish `tn` using `isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ P p`. Conclude with `(tn.2.2 _ (tn.1 _ _ d2)).unique d2 d1`. Set `gm : (U.X k).Λ ≃ₗ[𝓞 E] (U.X k).Λ` to `(φ k).symm ≪≫ₗ gam ≪≫ₗ φ k`. Set `A : (E →+* ℂ) → ℕ → ℕ → ℂ` to `fun τ i j => if hij : i < Dw.mult τ ∧ j < Dw.mult τ then Formalism.L2.PjFree.toC (cf τ ⟨j, hij.2⟩ ⟨i, hij.1⟩) else 0`. Establish `hA0 : ∀ τ i j, j < i → A τ i j = 0`.

Introduce `τ i j hji`. Simplify using `only [A]`. Use `split_ifs with hij`. Conclude with `hcf2 τ _ _ hji`. Both sides reduce to the same expression.

Establish `hAr : ∀ τ, ∀ i < Dw.mult τ, ∀ v : (U.X k).Λ, Formalism.L2.PjFree.perFr (U.X k) x (gm v : Fin r → E) (Formalism.L2.PjFree.relab c σ τ) i = ∑ j ∈ Finset.range (Dw.mult τ), A τ i j * Formalism.L2.PjFree.perFr (U.X k) (lact γ x) (v : Fin r → E) (Formalism.L2.PjFree.relab c σ τ) j`. Introduce `τ i hi v`. Take `⟨v, rfl⟩` from `(φ k).surjective v`. Simplify using `only [gm, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]`. Establish `a1` using `hP (gam v) (e.symm ⟨τ, ⟨i, hi⟩⟩)`.

Rewrite `a1` using `[Equiv.apply_symm_apply]`. Rewrite using `[← a1, hh, Finset.sum_range]`. Use `(apply_of_cols e h.toLinearMap (fun τ i j => cf τ i j) hcol (P' v) τ ⟨i, hi⟩).trans (Finset.sum_congr rfl fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[hP', Equiv.apply_symm_apply]`. Simplify using `only [A]`.

Rewrite using `[dif_pos ⟨hi, j.2⟩]`. Both sides reduce to the same expression. Establish `hgiso : ∀ u v : (U.X k).Λ, Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (gm u : Fin r → E) (gm v : Fin r → E)) = Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (u : Fin r → E) (v : Fin r → E))`. Introduce `u v`. Take `⟨u, rfl⟩` from `(φ k).surjective u`.

Take `⟨v, rfl⟩` from `(φ k).surjective v`. Simplify using `only [gm, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]`. Rewrite using `[← hEF, ← hEF, hiso]`. Apply the tactic sequence `obtain ⟨η, ε, -, hξ, hav, hlat, hisoη⟩ := GlobalTheory.T.exists_rational_isometry_of_trace_isometry E r (U.X k) (U.X k) (fun _ => rfl) gm hgiso`. Establish `hε : ε = 1` using `mul_right_cancel₀ (U.X k).ξ0_ne (hξ.symm.trans (one_mul _).symm)`.

Establish `hUS : IsUStab (U.X k).Gm (U.X k).Λ η` using `⟨fun u v => by rw [hisoη, hε, one_mul], hlat⟩`. Establish `hcong : ∀ w ∈ (U.X k).Λ, ∃ y ∈ (U.X k).Λ, (η : Matrix (Fin r) (Fin r) E) *ᵥ w - w = (l.M : E) • y`. Introduce `w hw`. Take `⟨a, ha⟩` from `(φ k).surjective ⟨w, hw⟩`. Take `⟨e₀, he₀⟩` from `f₁ a`.

Use `⟨(φ k e₀ : Fin r → E), (φ k e₀).2, ?_⟩` and prove the remaining obligations. Establish `h1` using `hav ⟨w, hw⟩`. Establish `h2 : gm ⟨w, hw⟩ = ⟨w, hw⟩ + l.M • φ k e₀`. Simplify using `only [gm, LinearEquiv.trans_apply, ← ha, LinearEquiv.symm_apply_apply, he₀, map_add, map_nsmul]`. Rewrite `h1` using `[h2]`.

Express the relevant statement in the definitionally equal form `(η : Matrix (Fin r) (Fin r) E) *ᵥ w = _ at h1`. Rewrite using `[h1]`. Simplify using `[Nat.cast_smul_eq_nsmul]`. Take `⟨hbij, hrt, -, -⟩` from `GlobalTheory.Relab.relab_good E H l c σ hσ`. Set `ρe` to `Equiv.ofBijective _ hbij`.

Establish `he : ∀ τ, Formalism.L2.PjFree.relab c σ (ρe.symm τ) = τ` using `ρe.apply_symm_apply`. Establish `m1 : ∀ τ ∈ (U.X k).Ψ, Dw.mult (ρe.symm τ) = r - (U.X k).p0` using `fun τ hτ => by`. Unfold `Datum.mult`. Rewrite using `[if_pos ((hrt _).1 (by rw [he]; exact ((hty k).2 τ).1 hτ)), (hty k).1]`. Use linear arithmetic over natural numbers and integers.

Establish `m2 : ∀ τ ∉ (U.X k).Ψ, Dw.mult (ρe.symm τ) = (U.X k).p0` using `fun τ hτ => by`. Unfold `Datum.mult`. Rewrite using `[if_neg (fun h => hτ (((hty k).2 τ).2 (by rw [← he τ]; exact (hrt _).2 h))), (hty k).1]`. Establish `hrel : ∀ τ, ∀ i < Dw.mult (ρe.symm τ), ∀ v ∈ (U.X k).Λ, Formalism.L2.PjFree.perFr (U.X k) x ((η : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i = ∑ j ∈ Finset.range (Dw.mult (ρe.symm τ)), A (ρe.symm τ) i j * Formalism.L2.PjFree.perFr (U.X k) (lact γ x) v τ j` using `fun τ i hi v hv => by`. Use `hAr (ρe.symm τ) i hi ⟨v, hv⟩` as an intermediate fact.

Rewrite `this` using `[he, ← hav]`. Then use the resulting hypothesis. Take `⟨b, hb, hxb, -⟩` from `GlobalTheory.T.frames_differ_by_isometry_and_triangular_of_periods E r (U.X k) (U.X k) η (isMatch_of_isUStab (U.X k) hUS) (fun τ => Dw.mult (ρe.symm τ)) m1 m2 (lact γ x) hx' x hx (fun τ => A (ρe.symm τ)) (fun τ => hA0 _) hrel`. Conclude with `⟨η, hUS, hcong, b, hb, hxb⟩`.
-/
theorem exists_congr_back : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → l.A = 1 → 1 ≤ r → ∀ k, ∀ γ ∈ (U.X k).Γ, ∀ x ∈ (U.X k).dom, ∃ η : GL (Fin r) E, ReciprocityTheory.ChartRestriction.G.FD.IsUStab (U.X k).Gm (U.X k).Λ η ∧ (∀ w ∈ (U.X k).Λ, ∃ y ∈ (U.X k).Λ, Matrix.mulVec (η : Matrix (Fin r) (Fin r) E) w - w = (l.M : E) • y) ∧ ∃ b ∈ ReciprocityTheory.ChartRestriction.G.FD.Bor (U.X k).Ψ r, x = ReciprocityTheory.ChartRestriction.G.FD.rmul (ReciprocityTheory.ChartRestriction.G.FD.lact η (ReciprocityTheory.ChartRestriction.G.FD.lact γ x)) b := by
  classical
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hA _hr k γ hγ x hx
  have hx' : lact γ x ∈ (U.X k).dom := dom_lact (U.X k) hx ((U.X k).Γ_stab γ hγ)

  let b₁ : Frame (U.X k).Ψ r := fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)
  have hm₁ : ∀ τ, mat b₁ τ = 1 := fun τ => rfl
  have hb₁ : b₁ ∈ Bor (U.X k).Ψ r := fun τ => ⟨by rw [hm₁]; simp, fun a c hca => by
    have := hm₁ τ
    change Matrix.of (b₁ τ) = 1 at this
    have h2 := congrFun (congrFun this a) c
    simpa [Matrix.one_apply_ne (ne_of_gt hca)] using h2⟩
  have hrm : rmul (lact γ x) b₁ = lact γ x := by
    funext τ
    change mat (lact γ x) τ * mat b₁ τ = lact γ x τ
    rw [hm₁, Matrix.mul_one]
    rfl
  obtain ⟨t, hB⟩ : ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (U.un k ⟨x, hx⟩) (U.un k ⟨lact γ x, hx'⟩) :=
    (hU.2.2.2.1 k k ⟨x, hx⟩ ⟨lact γ x, hx'⟩).2 ⟨γ, hγ, b₁, hb₁, by rw [hrm]⟩
  obtain ⟨hrr, hty, -, -, -, g, e, F, ik, φ, hEF, hpt⟩ := hU
  obtain ⟨P, hP, p, hPx, hv, -⟩ := hpt k ⟨x, hx⟩
  obtain ⟨P', hP', p', hPx', hv', -⟩ := hpt k ⟨lact γ x, hx'⟩
  have hu : F.u (ik k) P' = F.u (ik k) P := by rw [← hPx, ← hPx', hB.1]
  obtain ⟨h, gam, hex, hh, hiso, hM, -⟩ := GlobalTheory.T.familyUnif_exp_unique_alt E H Dw l Xo _ g _ F (ik k) (ik k) P' P p' p hu

  have hM' : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di (ik k)).La),
      ∃ e, gam a = a + l.M • e := by
    intro a ha
    refine Submodule.smul_induction_on ha ?_ ?_
    · intro v hv b _
      obtain ⟨c, e, rfl⟩ := F.t_surj (ik k) b
      obtain ⟨e₁, he₁⟩ := hM (v • c) (Submodule.smul_mem_smul hv Submodule.mem_top)
      obtain ⟨r, hr⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
      refine ⟨e₁ + r • (gam (v • e) - v • e), ?_⟩
      rw [smul_add, ← map_smul, smul_comm v, map_add, he₁, map_nsmul, hr, smul_add, smul_smul,
        smul_sub]
      abel
    · rintro x y ⟨e, he⟩ ⟨e', he'⟩
      exact ⟨e + e', by rw [map_add, he, he', smul_add]; abel⟩
  have f₁ := GlobalTheory.LevelHalf.trivial_mod_of_trivial_on_half E H (F.Di (ik k)) l gam hiso hM'

  choose cf hcf1 hcf2 hcf3 using hB.2.1
  have hcol : ∀ τ i, h.toLinearMap (Pi.single (e.symm ⟨τ, i⟩) 1) =
      (∑ j, (show ℂ from cf τ i j) • (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ)) := by
    intro τ i
    have d1 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F _ P p _ ((U.un k ⟨x, hx⟩).u τ) _ (hv τ)
      (cf τ i) ((U.un k ⟨lact γ x, hx'⟩).u τ i)).1 (hPx ▸ hcf3 τ i)
    have d0 := hv' τ i
    simp only [← hex] at d0
    have d2 := (ExpChain.isDerivAt0_comp_linear _ (ExpChain.isHolTo_ex F _ P p) h.toLinearMap _ _).1 d0
    have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ P p
    exact (tn.2.2 _ (tn.1 _ _ d2)).unique d2 d1
  let gm : (U.X k).Λ ≃ₗ[𝓞 E] (U.X k).Λ := (φ k).symm ≪≫ₗ gam ≪≫ₗ φ k
  let A : (E →+* ℂ) → ℕ → ℕ → ℂ := fun τ i j =>
    if hij : i < Dw.mult τ ∧ j < Dw.mult τ then Formalism.L2.PjFree.toC (cf τ ⟨j, hij.2⟩ ⟨i, hij.1⟩) else 0
  have hA0 : ∀ τ i j, j < i → A τ i j = 0 := by
    intro τ i j hji
    simp only [A]
    split_ifs with hij
    · exact hcf2 τ _ _ hji
    · rfl
  have hAr : ∀ τ, ∀ i < Dw.mult τ, ∀ v : (U.X k).Λ,
      Formalism.L2.PjFree.perFr (U.X k) x (gm v : Fin r → E) (Formalism.L2.PjFree.relab c σ τ) i =
        ∑ j ∈ Finset.range (Dw.mult τ), A τ i j *
          Formalism.L2.PjFree.perFr (U.X k) (lact γ x) (v : Fin r → E) (Formalism.L2.PjFree.relab c σ τ) j := by
    intro τ i hi v
    obtain ⟨v, rfl⟩ := (φ k).surjective v
    simp only [gm, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    have a1 := hP (gam v) (e.symm ⟨τ, ⟨i, hi⟩⟩)
    rw [Equiv.apply_symm_apply] at a1
    rw [← a1, hh, Finset.sum_range]
    refine (apply_of_cols e h.toLinearMap (fun τ i j => cf τ i j) hcol (P' v) τ ⟨i, hi⟩).trans
      (Finset.sum_congr rfl fun j _ => ?_)
    rw [hP', Equiv.apply_symm_apply]
    simp only [A]
    rw [dif_pos ⟨hi, j.2⟩]
    rfl
  have hgiso : ∀ u v : (U.X k).Λ, Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (gm u : Fin r → E)
      (gm v : Fin r → E)) = Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (u : Fin r → E) (v : Fin r → E)) := by
    intro u v
    obtain ⟨u, rfl⟩ := (φ k).surjective u
    obtain ⟨v, rfl⟩ := (φ k).surjective v
    simp only [gm, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rw [← hEF, ← hEF, hiso]

  obtain ⟨η, ε, -, hξ, hav, hlat, hisoη⟩ := GlobalTheory.T.exists_rational_isometry_of_trace_isometry E r (U.X k) (U.X k) (fun _ => rfl) gm hgiso
  have hε : ε = 1 := mul_right_cancel₀ (U.X k).ξ0_ne (hξ.symm.trans (one_mul _).symm)
  have hUS : IsUStab (U.X k).Gm (U.X k).Λ η := ⟨fun u v => by rw [hisoη, hε, one_mul], hlat⟩
  have hcong : ∀ w ∈ (U.X k).Λ, ∃ y ∈ (U.X k).Λ,
      (η : Matrix (Fin r) (Fin r) E) *ᵥ w - w = (l.M : E) • y := by
    intro w hw
    obtain ⟨a, ha⟩ := (φ k).surjective ⟨w, hw⟩
    obtain ⟨e₀, he₀⟩ := f₁ a
    refine ⟨(φ k e₀ : Fin r → E), (φ k e₀).2, ?_⟩
    have h1 := hav ⟨w, hw⟩
    have h2 : gm ⟨w, hw⟩ = ⟨w, hw⟩ + l.M • φ k e₀ := by
      simp only [gm, LinearEquiv.trans_apply, ← ha, LinearEquiv.symm_apply_apply, he₀, map_add, map_nsmul]
    rw [h2] at h1
    change (η : Matrix (Fin r) (Fin r) E) *ᵥ w = _ at h1
    rw [h1]
    simp [Nat.cast_smul_eq_nsmul]

  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  let ρe := Equiv.ofBijective _ hbij
  have he : ∀ τ, Formalism.L2.PjFree.relab c σ (ρe.symm τ) = τ := ρe.apply_symm_apply
  have m1 : ∀ τ ∈ (U.X k).Ψ, Dw.mult (ρe.symm τ) = r - (U.X k).p0 := fun τ hτ => by
    unfold Datum.mult
    rw [if_pos ((hrt _).1 (by rw [he]; exact ((hty k).2 τ).1 hτ)), (hty k).1]
    omega
  have m2 : ∀ τ ∉ (U.X k).Ψ, Dw.mult (ρe.symm τ) = (U.X k).p0 := fun τ hτ => by
    unfold Datum.mult
    rw [if_neg (fun h => hτ (((hty k).2 τ).2 (by rw [← he τ]; exact (hrt _).2 h))), (hty k).1]
  have hrel : ∀ τ, ∀ i < Dw.mult (ρe.symm τ), ∀ v ∈ (U.X k).Λ,
      Formalism.L2.PjFree.perFr (U.X k) x ((η : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i =
        ∑ j ∈ Finset.range (Dw.mult (ρe.symm τ)), A (ρe.symm τ) i j *
          Formalism.L2.PjFree.perFr (U.X k) (lact γ x) v τ j :=
    fun τ i hi v hv => by
      have := hAr (ρe.symm τ) i hi ⟨v, hv⟩
      rwa [he, ← hav] at this
  obtain ⟨b, hb, hxb, -⟩ := GlobalTheory.T.frames_differ_by_isometry_and_triangular_of_periods E r (U.X k) (U.X k) η (isMatch_of_isUStab (U.X k) hUS)
    (fun τ => Dw.mult (ρe.symm τ)) m1 m2 (lact γ x) hx' x hx (fun τ => A (ρe.symm τ))
    (fun τ => hA0 _) hrel
  exact ⟨η, hUS, hcong, b, hb, hxb⟩

end GlobalTheory.CongrOrbit
