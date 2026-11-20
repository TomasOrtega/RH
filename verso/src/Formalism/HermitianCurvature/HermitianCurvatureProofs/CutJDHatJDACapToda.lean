import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHat
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapAGrp
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PbDegTopOfPolyTop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellValues

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JDAToda

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.Qx2 Formalism.FourierDecayAlt.P.PBN Formalism.FourierDecayAlt.P.PBN.MC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hG, hD⟩`. Use `⟨fun l hl => ?_, hG⟩` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos l.val with h0 | hpos` into its components or cases.

Establish `: l = ⟨0, by omega⟩` using `Fin.ext h0`. Rewrite using `[this, show Dmin k r Bs.z Bs.z' g ⟨0, by omega⟩ = 1 by unfold Dmin; exact Matrix.det_isEmpty]`. Conclude with `one_ne_zero`. Use `hD ⟨l.val - 1, by omega⟩` as an intermediate fact. Establish `e : (⟨(l.val - 1) + 1, by omega⟩ : Fin (r + 2)) = l` using `Fin.ext (by simp; omega)`.

Simplify `this` using `[e]`. Introduce and unpack `⟨hD, hG⟩`. Conclude with `⟨hG, fun a => hD ⟨a.val + 1, by omega⟩ (by show a.val + 1 ≤ r; have := a.isLt; omega)⟩`.
-/
theorem omB_eq {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) : Gauge.OmB Bs = Q.OmPlus k r Bs.z Bs.z' := by
  ext g
  constructor
  · rintro ⟨hG, hD⟩
    refine ⟨fun l hl => ?_, hG⟩
    rcases Nat.eq_zero_or_pos l.val with h0 | hpos
    · have : l = ⟨0, by omega⟩ := Fin.ext h0
      rw [this, show Dmin k r Bs.z Bs.z' g ⟨0, by omega⟩ = 1 by unfold Dmin; exact Matrix.det_isEmpty]
      exact one_ne_zero
    · have := hD ⟨l.val - 1, by omega⟩
      have e : (⟨(l.val - 1) + 1, by omega⟩ : Fin (r + 2)) = l := Fin.ext (by simp; omega)
      simpa [e] using this
  · rintro ⟨hD, hG⟩
    exact ⟨hG, fun a => hD ⟨a.val + 1, by omega⟩ (by show a.val + 1 ≤ r; have := a.isLt; omega)⟩

/- English proof (translation)
Take `⟨μ, _, rfl⟩` from `(Formalism.FourierDecayAlt.P.TwoByOneBlock.UWb_iff g).1 (Formalism.FourierDecayAlt.P5.Rad.glev_last_uwb hg)`. Establish `e : wCell k r (Fin.last r) c * B2.embWb k r μ = bigCell k r c μ`. Rewrite using `[Formalism.FourierDecayAlt.P5.Rad.wCell_last_eq, ← (Formalism.FourierDecayAlt.P.bruhat_big_cell_factorization k r c μ).1]`. Establish `hmin` using `big_cell_minors_holds k r Bs.z Bs.z' c μ Bs.z_mem Bs.z'_mem`. Establish `hζ : herm (Hpk k r) (bigCell k r c μ *ᵥ Bs.z') Bs.z = zetaL k r Bs.z Bs.z' (Fin.last r) (B2.embWb k r μ)`.

Rewrite using `[Formalism.FourierDecayAlt.P5.Rad.zetaL_last, ← Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart Bs.z'_mem, Formalism.FourierDecayAlt.P.BigCellHermitian.bigCell_mulVec_jV, Formalism.FourierDecayAlt.P.TwoByOneBlock.emb_mulVec_jV]`. Establish `hr : Dmin k r Bs.z Bs.z' (bigCell k r c μ) ⟨r, by omega⟩ = ∏ a, c a`. Establish `h` using `hmin.1 (Fin.last r)`. Simplify using `only [Fin.val_last] at h`. Rewrite using `[h]`.

Simplify using the standard rewrite rules. Establish `hP0 : (∏ a, c a) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun a _ => hc a`. Establish `hlast : Dmin k r Bs.z Bs.z' (bigCell k r c μ) (Fin.last (r + 1)) = (∏ a, c a) * zetaL k r Bs.z Bs.z' (Fin.last r) (B2.embWb k r μ)`. Establish `hzeta` using `hmin.2.2 hc`. Rewrite `hzeta` using `[hζ]`.

Unfold `Formalism.QuantumDeterminants.zeta at hzeta`. Rewrite `hzeta` using `[hr]`. Rewrite using `[← hzeta, mul_div_cancel₀ _ hP0]`. Establish `hGf : Gf k r Bs.z Bs.z' (bigCell k r c μ) = Complex.normSq (∏ a, c a) * GGl k r Bs.z Bs.z' (B2.embWb k r μ)`. Unfold `Gf GGl`.

Rewrite using `[hlast, hr, Complex.normSq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1` using `hcg.1`. Rewrite `h1` using `[e, hGf]`. Conclude with `pos_of_mul_pos_right h1 (Complex.normSq_nonneg _)`.
-/
theorem gg_pos {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) {c : Fin r → ℂ} (hc : c ∈ OmX r)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) (hcg : wCell k r (Fin.last r) c * g ∈ Gauge.OmB Bs) :
    0 < GGl k r Bs.z Bs.z' g := by
  obtain ⟨μ, _, rfl⟩ := (Formalism.FourierDecayAlt.P.TwoByOneBlock.UWb_iff g).1 (Formalism.FourierDecayAlt.P5.Rad.glev_last_uwb hg)
  have e : wCell k r (Fin.last r) c * B2.embWb k r μ = bigCell k r c μ := by
    rw [Formalism.FourierDecayAlt.P5.Rad.wCell_last_eq, ← (Formalism.FourierDecayAlt.P.bruhat_big_cell_factorization k r c μ).1]
  have hmin := big_cell_minors_holds k r Bs.z Bs.z' c μ Bs.z_mem Bs.z'_mem
  have hζ : herm (Hpk k r) (bigCell k r c μ *ᵥ Bs.z') Bs.z = zetaL k r Bs.z Bs.z' (Fin.last r) (B2.embWb k r μ) := by
    rw [Formalism.FourierDecayAlt.P5.Rad.zetaL_last, ← Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart Bs.z'_mem, Formalism.FourierDecayAlt.P.BigCellHermitian.bigCell_mulVec_jV,
      Formalism.FourierDecayAlt.P.TwoByOneBlock.emb_mulVec_jV]
  have hr : Dmin k r Bs.z Bs.z' (bigCell k r c μ) ⟨r, by omega⟩ = ∏ a, c a := by
    have h := hmin.1 (Fin.last r)
    simp only [Fin.val_last] at h
    rw [h]
    simp
  have hP0 : (∏ a, c a) ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hc a
  have hlast : Dmin k r Bs.z Bs.z' (bigCell k r c μ) (Fin.last (r + 1)) =
      (∏ a, c a) * zetaL k r Bs.z Bs.z' (Fin.last r) (B2.embWb k r μ) := by
    have hzeta := hmin.2.2 hc
    rw [hζ] at hzeta
    unfold Formalism.QuantumDeterminants.zeta at hzeta
    rw [hr] at hzeta
    rw [← hzeta, mul_div_cancel₀ _ hP0]
  have hGf : Gf k r Bs.z Bs.z' (bigCell k r c μ) =
      Complex.normSq (∏ a, c a) * GGl k r Bs.z Bs.z' (B2.embWb k r μ) := by
    unfold Gf GGl
    rw [hlast, hr, Complex.normSq_mul]
    ring
  have h1 := hcg.1
  rw [e, hGf] at h1
  exact pos_of_mul_pos_right h1 (Complex.normSq_nonneg _)

/- English proof (translation)
Establish `hRR` using `Formalism.FourierDecayAlt.P.right_rule_derivative`. Establish `hLR` using `Formalism.FourierDecayAlt.P.left_rule_cell`. Establish `hTC` using `Formalism.FourierDecayAlt.P.torus_cell`. Establish `hGP` using `Formalism.FourierDecayAlt.P.gauge_positivity`. Use `set D := OmPlus k r Bs.z Bs.z' with hDdef`.

Establish `hD : IsOpen D` using `Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.isOpen_OmPlus Bs.z Bs.z'`. Establish `h1N : (1 : Mx k r) ∈ Nlev k r 0` using `⟨(Formalism.QuantumDeterminants.unipotent_subgroup_holds k r).1, by simp [Glev, UH]⟩`. Establish `hN : ∀ g ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * g ∈ D`. Introduce `g hg n hn`. Establish `hDom` using `Formalism.FourierDecayAlt.P.JCx2.rma_isDom_omPlus (k := k) (r := r) Bs.z_mem Bs.z'_mem`.

Use `hDom.2 g hg n ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one Bs.z, n, hn, (one_mul n).symm⟩ 1 ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one Bs.z', 1, h1N, (one_mul 1).symm⟩` as an intermediate fact. Rewrite `this` using `[Matrix.mul_one]`. Then use the resulting hypothesis. Use `set v₀ : VS k r 0 D (Wq →L[ℂ] Wp) := ⟨cut k r 0 D J, cut_mem hD hf⟩ with hv₀`. Establish `hcellB : ∀ c ∈ OmX r, wCell k r (Fin.last r) c * x.2 ∈ C6.bigPos Bs` using `fun c hc => (Formalism.FourierDecayAlt.P.big_cell_values k r Wp Wq Bs (c, x.2) ⟨hc, hx.2.1, hx.2.2⟩).1`. Establish `hcell : ∀ c ∈ OmX r, wCell k r (Fin.last r) c * x.2 ∈ Glev k r 0 ∩ D`.

Introduce `c hc`. Establish `h` using `hcellB c hc`. Conclude with `⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 h.1, fun l _ => h.2.2 l (by simp), h.2.1⟩`. Establish `hdiff : ∀ x' : SA (Wq →L[ℂ] Wp) hD, ∀ c ∈ OmX r, DifferentiableAt ℝ (fun c' => ((x' : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀ : Mx k r → (Wq →L[ℂ] Wp)) (wCell k r (Fin.last r) c' * x.2)) c` using `fun x' c hc => cell_diff Bs ((x' : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀).2.1 hx.2.1 hx.2.2 hc`. Establish `hWS : ∀ x' : SA (Wq →L[ℂ] Wp) hD, resW ((x' : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀ : Mx k r → (Wq →L[ℂ] Wp)) x.2 ∈ WSm r (Wq →L[ℂ] Wp)` using `fun x' => resG_wsm Bs ((x' : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀).2.1 hx.2.1 hx.2.2`.

Establish `hcl` using `claim hD v₀ x.2 y hRR hLR hTC hGP Bs.z Bs.z' Bs.z_mem Bs.z'_mem hN hf hLf hRf rfl hx.2.1 hcell hdiff hWS r le_rfl 1 (Subalgebra.one_mem _) x.1 hx.1`. Rewrite `hcl` using `[mul_one]`. Establish `eR : Q.crd (Q.vAB r y r).1 (Q.resG k r (Fin.last r) J) x.1 x.2 = (Q.vAB r y r).1 (fun c' => Q.resG k r (Fin.last r) (((1 : SA (Wq →L[ℂ] Wp) hD) : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀ : Mx k r → (Wq →L[ℂ] Wp)) c' x.2) x.1`. Use `(vAB_loc y r _ _ (fun c' hc' => ?_) x.1 hx.1).1` and prove the remaining obligations. Rewrite using `[resG_last, resG_last]`.

Use `congr 1`. Conclude with `(cut_of_mem _ (hcell c' hc')).symm`. Rewrite using `[eR, ← hcl, resG_last, resG_last]`. Use `congr 1`. Establish `hγ` using `hcell x.1 hx.1`.

Establish `e1 : ((qminor (EA (E` using `Wq →L[ℂ] Wp) hD) (C3.xR k r r le_rfl) (C3.xR k r r le_rfl) (y + ((2 * r + k : ℕ) : ℂ) / 2) : SA (Wq →L[ℂ] Wp) hD) : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) = qminor (Eh (E := Wq →L[ℂ] Wp) (i := 0) hD) (cI ∘ C3.xR k r r le_rfl) (cI ∘ C3.xR k r r le_rfl) (y + ((2 * r + k : ℕ) : ℂ) …`. Use `map_qminor (SA (Wq →L[ℂ] Wp) hD).val (EA hD) (C3.xR k r r le_rfl) (C3.xR k r r le_rfl) (y + ((2 * r + k : ℕ) : ℂ) / 2)` as an intermediate fact. Rewrite `this` using `[Subalgebra.coe_val]`. Rewrite using `[this]`. Conclude with `qminor_reindex (Eh hD) cI cI_inj _ _ _`.

Rewrite using `[e1, rep_qminor hD _ _ _ v₀ _ hγ]`. Establish `hpos : posL k r 0 ∘ (cI ∘ C3.xR k r r le_rfl) = C3.xR k r r le_rfl` using `funext fun l => posL_cI _`. Establish `hloc` using `(good_qminor (E := Wq →L[ℂ] Wp) hD (cI ∘ C3.xR k r r le_rfl) (cI ∘ C3.xR k r r le_rfl) (y + ((2 * r + k : ℕ) : ℂ) / 2)).loc (cut k r 0 D J) J (fun x' hx' => cut_of_mem _ hx') _ hγ`. Rewrite `hloc` using `[hpos]`. Rewrite using `[hpos]`.

Conclude with `hloc.symm`.
-/
theorem minorCell_of {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) {J : Mx k r → (Wq →L[ℂ] Wp)}
    (hf : SmoothLev k r 0 (OmPlus k r Bs.z Bs.z') J) (hLf : LeftEq k r Bs.z 0 (OmPlus k r Bs.z Bs.z') J)
    (hRf : RightEq k r Bs.z' 0 (OmPlus k r Bs.z Bs.z') J) (y : ℂ) (x : (Fin r → ℂ) × Mx k r)
    (hx : x ∈ DomR k r Bs.z Bs.z') :
    Q.resG k r (Fin.last r) (qminorOp (EabH (Hpk k r)) (C3.xR k r r le_rfl) (C3.xR k r r le_rfl)
        (y + ((2 * r + k : ℕ) : ℂ) / 2) J) x.1 x.2 =
      Q.crd (Q.vAB r y r).1 (Q.resG k r (Fin.last r) J) x.1 x.2 := by
  have hRR := Formalism.FourierDecayAlt.P.right_rule_derivative
  have hLR := Formalism.FourierDecayAlt.P.left_rule_cell
  have hTC := Formalism.FourierDecayAlt.P.torus_cell
  have hGP := Formalism.FourierDecayAlt.P.gauge_positivity
  set D := OmPlus k r Bs.z Bs.z' with hDdef
  have hD : IsOpen D := Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.isOpen_OmPlus Bs.z Bs.z'
  have h1N : (1 : Mx k r) ∈ Nlev k r 0 :=
    ⟨(Formalism.QuantumDeterminants.unipotent_subgroup_holds k r).1, by simp [Glev, UH]⟩
  have hN : ∀ g ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * g ∈ D := by
    intro g hg n hn
    have hDom := Formalism.FourierDecayAlt.P.JCx2.rma_isDom_omPlus (k := k) (r := r) Bs.z_mem Bs.z'_mem
    have := hDom.2 g hg n ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one Bs.z, n, hn, (one_mul n).symm⟩ 1
      ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one Bs.z', 1, h1N, (one_mul 1).symm⟩
    rwa [Matrix.mul_one] at this
  set v₀ : VS k r 0 D (Wq →L[ℂ] Wp) := ⟨cut k r 0 D J, cut_mem hD hf⟩ with hv₀
  have hcellB : ∀ c ∈ OmX r, wCell k r (Fin.last r) c * x.2 ∈ C6.bigPos Bs := fun c hc =>
    (Formalism.FourierDecayAlt.P.big_cell_values k r Wp Wq Bs (c, x.2) ⟨hc, hx.2.1, hx.2.2⟩).1
  have hcell : ∀ c ∈ OmX r, wCell k r (Fin.last r) c * x.2 ∈ Glev k r 0 ∩ D := by
    intro c hc
    have h := hcellB c hc
    exact ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 h.1, fun l _ => h.2.2 l (by simp), h.2.1⟩
  have hdiff : ∀ x' : SA (Wq →L[ℂ] Wp) hD, ∀ c ∈ OmX r, DifferentiableAt ℝ
      (fun c' => ((x' : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀ : Mx k r → (Wq →L[ℂ] Wp))
        (wCell k r (Fin.last r) c' * x.2)) c :=
    fun x' c hc => cell_diff Bs ((x' : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀).2.1 hx.2.1 hx.2.2 hc
  have hWS : ∀ x' : SA (Wq →L[ℂ] Wp) hD,
      resW ((x' : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀ : Mx k r → (Wq →L[ℂ] Wp)) x.2 ∈ WSm r (Wq →L[ℂ] Wp) :=
    fun x' => resG_wsm Bs ((x' : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀).2.1 hx.2.1 hx.2.2
  have hcl := claim hD v₀ x.2 y hRR hLR hTC hGP Bs.z Bs.z' Bs.z_mem Bs.z'_mem hN hf hLf hRf rfl hx.2.1 hcell hdiff hWS
    r le_rfl 1 (Subalgebra.one_mem _) x.1 hx.1
  rw [mul_one] at hcl
  have eR : Q.crd (Q.vAB r y r).1 (Q.resG k r (Fin.last r) J) x.1 x.2 =
      (Q.vAB r y r).1 (fun c' => Q.resG k r (Fin.last r)
        (((1 : SA (Wq →L[ℂ] Wp) hD) : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀ : Mx k r → (Wq →L[ℂ] Wp)) c' x.2) x.1 := by
    refine (vAB_loc y r _ _ (fun c' hc' => ?_) x.1 hx.1).1
    rw [resG_last, resG_last]
    congr 1
    exact (cut_of_mem _ (hcell c' hc')).symm
  rw [eR, ← hcl, resG_last, resG_last]
  congr 1
  have hγ := hcell x.1 hx.1
  have e1 : ((qminor (EA (E := Wq →L[ℂ] Wp) hD) (C3.xR k r r le_rfl) (C3.xR k r r le_rfl)
      (y + ((2 * r + k : ℕ) : ℂ) / 2) : SA (Wq →L[ℂ] Wp) hD) : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) =
      qminor (Eh (E := Wq →L[ℂ] Wp) (i := 0) hD) (cI ∘ C3.xR k r r le_rfl) (cI ∘ C3.xR k r r le_rfl)
        (y + ((2 * r + k : ℕ) : ℂ) / 2) := by
    have := map_qminor (SA (Wq →L[ℂ] Wp) hD).val (EA hD) (C3.xR k r r le_rfl) (C3.xR k r r le_rfl)
      (y + ((2 * r + k : ℕ) : ℂ) / 2)
    rw [Subalgebra.coe_val] at this
    rw [this]
    exact qminor_reindex (Eh hD) cI cI_inj _ _ _
  rw [e1, rep_qminor hD _ _ _ v₀ _ hγ]
  have hpos : posL k r 0 ∘ (cI ∘ C3.xR k r r le_rfl) = C3.xR k r r le_rfl := funext fun l => posL_cI _
  have hloc := (good_qminor (E := Wq →L[ℂ] Wp) hD (cI ∘ C3.xR k r r le_rfl) (cI ∘ C3.xR k r r le_rfl)
    (y + ((2 * r + k : ℕ) : ℂ) / 2)).loc (cut k r 0 D J) J (fun x' hx' => cut_of_mem _ hx')
    _ hγ
  rw [hpos] at hloc
  rw [hpos]
  exact hloc.symm

/- English proof (translation)
Simplify using `only [Q.uC, Q.mdim, Fin.val_zero, Nat.sub_zero]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem uC_zero (k r : ℕ) (y : ℂ) : Q.uC k r 0 y = y + ((2 * r + k : ℕ) : ℂ) / 2 := by
  simp only [Q.uC, Q.mdim, Fin.val_zero, Nat.sub_zero]
  push_cast
  ring

end Formalism.FourierDecayAlt.P.CutMP.JDAToda

namespace Formalism.FourierDecayAlt.P.CutMP

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P Bs hpl hk y J hJ c hc g hg hcg`. Establish `hGG` using `JDAToda.gg_pos Bs hc hg hcg`. Establish `hx : (c, g) ∈ Q.DomR P.k P.r Bs.z Bs.z'` using `⟨hc, hg, hGG⟩`. Take `⟨hf, hLf, hRf, -⟩` from `hJ`. Rewrite `hf`, `hLf`, `hRf` using `[JDAToda.omB_eq]`.

Establish `hm` using `JDAToda.minorCell_of Bs hf hLf hRf y (c, g) hx`. Establish `hcell` using `Formalism.FourierDecayAlt.P.raising_cell P.k P.r (Wq →L[ℂ] Wp) J (Q.uC P.k P.r 0 y) c g hg`. Simplify using `only [dMul, drF, Q.crd, Q.cmp, ↓reduceIte] at hm ⊢`. Rewrite using `[← hm]`. Simplify using `only [Q.resG, capA]`.

Rewrite using `[hcell, JDAToda.uC_zero, smul_comm]`.
-/
theorem jda_capelli_toda_proof : JDACapToda := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk y J hJ c hc g hg hcg
  have hGG := JDAToda.gg_pos Bs hc hg hcg
  have hx : (c, g) ∈ Q.DomR P.k P.r Bs.z Bs.z' := ⟨hc, hg, hGG⟩
  obtain ⟨hf, hLf, hRf, -⟩ := hJ
  rw [JDAToda.omB_eq] at hf hLf hRf
  have hm := JDAToda.minorCell_of Bs hf hLf hRf y (c, g) hx
  have hcell := Formalism.FourierDecayAlt.P.raising_cell P.k P.r (Wq →L[ℂ] Wp) J (Q.uC P.k P.r 0 y) c g hg
  simp only [dMul, drF, Q.crd, Q.cmp, ↓reduceIte] at hm ⊢
  rw [← hm]
  simp only [Q.resG, capA]
  rw [hcell, JDAToda.uC_zero, smul_comm]

end Formalism.FourierDecayAlt.P.CutMP
