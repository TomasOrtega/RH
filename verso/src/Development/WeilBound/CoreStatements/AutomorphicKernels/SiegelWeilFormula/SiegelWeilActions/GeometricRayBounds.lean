import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.UnipotentBlockCornerEmbedded

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
open PositivityTheory.SiegelWeilFormula.Act.C4 PositivityTheory.SiegelWeilFormula.Act.C4.Bq PositivityTheory.SiegelWeilFormula.Act.C5

namespace PositivityTheory.SiegelWeilFormula.Act.C6

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD σ} {L : LD d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}

/- English proof (translation)
Establish `hσ` using `kfour.sigma_sigma_of_good d.ok.good`. Take `⟨⟨ε, hε⟩, -⟩` from `d.ok.frame`. Take `⟨⟨ε', hε'⟩, -⟩` from `L.ok.frame`. Establish `hee : ε = ε'` using `Afc.eps_eq L hε hε'`. Substitute `hee` using the available equality.

Take `⟨G0, hG0⟩` from `Afc.rat_frame (b := d.b) x hx`. Establish `hx0 : ∀ r, G0 r (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) r (Sum.inl L.i₀)`. Introduce `r`. Apply `kfour.inclR_injective (F := F)` to reduce the goal to its premises. Establish `h1` using `hf r`.

Rewrite `h1` using `[hG0]`. Simplify using `only [incM, Matrix.map_apply] at h1`. Rewrite using `[h1]`. Apply the tactic sequence `by_cases hr : r = Sum.inl L.i₀ <;> simp [Matrix.one_apply, hr]`. Establish `hform` using `form_E hε x hG0`.

Establish `hy` using `yrow_zero hform hx0`. Use `set H := G0.submatrix (emS L) (emS L) with hH_def`. Establish `hH` using `blockH_form L hform hx0 hy`. Establish `hε1 : (((ε : ℤ) : E)) * (((ε : ℤ) : E)) = 1`. Rewrite using `[← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]`.

Establish `hεσ : (σ : E →+* E) (((ε : ℤ) : E)) = ((ε : ℤ) : E)` using `map_intCast _ _`. Take `⟨hHH', hH'H⟩` from `kunf.frame_inv_pf (σ : E →+* E) hσ (((ε : ℤ) : E)) hε1 hεσ H hH`. Use `set H' := Matrix.fromBlocks ((H.toBlocks₂₂.map (σ : E →+* E))ᵀ) ((((ε : ℤ) : E)) • (H.toBlocks₁₂.map (σ : E →+* E))ᵀ) ((((ε : ℤ) : E)) • (H.toBlocks₂₁.map (σ : E →+* E))ᵀ) ((H.toBlocks₁₁.map (σ : E →+* E))ᵀ) with hH'_def`. Establish `hIA : incM F H * incM F H' = 1` using `by rw [← kfour.incM_mul', hHH', Afc.incM_one']`. Establish `hformA : (incM F H)ᵀ * kunf.jw L.n (((ε : ℤ) : AE F E)) * (incM F H).map (cA σ) = kunf.jw L.n (((ε : ℤ) : AE F E))`.

Establish `h1` using `congrArg (incM F) hH`. Rewrite `h1` using `[kfour.incM_mul', kfour.incM_mul', ← Afc.incM_transpose, ← Afc.incM_map_cA, ← QA_eq]`. Conclude with `h1`. Take `⟨g', hg'⟩` from `kunf.exists_of_frame (Y := L.Y) hε' (incM F H) (incM F H') hIA hformA`. Establish `hg'r : g' ∈ rat2 σ L.Y` using `kunf.rat_of_inFrame hg'`.

Establish `hg'i : inFrame L.b g'⁻¹ = incM F H'`. Rewrite using `[GlobalTheory.EisBL.DoubledParabolic.inFrame_inv, hg']`. Conclude with `Matrix.inv_eq_right_inv hIA`. Use `set n := x * L.j g'⁻¹ with hn_def`. Establish `hnF : inFrame d.b n = incM F (G0 * padE L H')`.

Rewrite using `[hn_def, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hG0, inFrame_j, hg'i, padM_incM, kfour.incM_mul']`. Establish `hnq0 : NQ (Sum.inl L.i₀) (Sum.inr L.i₀) (G0 * padE L H')` using `nq_E L hx0 hy hHH'`. Establish `hnr : n ∈ rat2 σ d.Y` using `mul_mem hx (j_rat L (inv_mem hg'r))`. Use `set N0 := G0 * padE L H' with hN0`. Use `set u₀ : Fin L.n → E := fun j => N0 (Sum.inl L.i₀) (Sum.inl (L.em j)) with hu₀`.

Use `set b₀ : Fin L.n → E := fun j => N0 (Sum.inl L.i₀) (Sum.inr (L.em j)) with hb₀`. Use `set z₀ : E := N0 (Sum.inl L.i₀) (Sum.inr L.i₀) + ∑ j, b₀ j * σ (u₀ j) with hz₀`. Establish `hUN0 : M.U (σ : E →+* E) (((ε : ℤ) : E)) N0` using `form_E hε n hnF`. Establish `hpz : σ z₀ = -(((ε : ℤ) : E) * z₀)` using `M.even_im_hermitian_sub hσ hε1 hεσ L.em L.inj L.rng hUN0 hnq0`. Establish `hpd` using `delta_par h hε`.

Establish `hε0 : (((ε : ℤ) : E)) ≠ 0` using `fun h0 => by rw [h0, zero_mul] at hε1; exact zero_ne_one hε1`. Establish `hfix : σ (z₀ / δ) = z₀ / δ`. Rewrite using `[map_div₀, hpz, hpd, neg_div_neg_eq, mul_div_mul_left _ _ hε0]`. Take `⟨a₀, ha₀⟩` from `fixed_in_F d.ok.good.cm (z₀ / δ) hfix`. Set `c : Cr L` to `⟨(GlobalTheory.ThK.incV F u₀, algebraMap F (AF F) a₀), AddSubgroup.subset_closure ⟨u₀, rfl⟩, ⟨a₀, rfl⟩⟩`.

Use `set s := n * (cM c.1)⁻¹ with hs_def`. Establish `hsr : s ∈ rat2 σ d.Y` using `mul_mem hnr (inv_mem (cM_rat' h c.2.1 c.2.2))`. Use `set e : AE F E := ((ε : ℤ) : AE F E) with he_def`. Establish `he : e * e = 1`. Rewrite using `[he_def, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]`.

Establish `hse : (cA σ).toRingHom e = e` using `map_intCast _ _`. Establish `hN : inFrame d.b n = sExp L e (GlobalTheory.ThK.incV F b₀) * inFrame d.b (cM c.1)`. Apply `M.nq_unique (s := (cA σ).toRingHom) (e := e) (i₀ := L.i₀) (cA_inv' hσ) he hse` to reduce the goal to its premises. Conclude with `kunf.frame_eq hε n`. Establish `hUS` using `U_sExp (ε := ε) (L := L) hσ (GlobalTheory.ThK.incV F b₀)`.

Establish `hUC : M.U (cA σ).toRingHom e (inFrame d.b (cM c.1))` using `kunf.frame_eq hε (cM c.1)`. Unfold `M.U at hUS hUC ⊢`. Rewrite using `[Matrix.transpose_mul, Matrix.map_mul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = kunf.jw d.n e := by rw [hUS, hUC]`. Rewrite using `[hnF]`. Conclude with `NQ.map _ hnq0`. Conclude with `NQ.mul (nq_sExp _ _) (nq_cM h _)`. Take `⟨r1, r2, r3, r4⟩` from `row_sC h e (GlobalTheory.ThK.incV F b₀) (GlobalTheory.ThK.incV F u₀) (algebraMap F (AF F) a₀)`.

Introduce `c'`. Rewrite using `[hnF]`. Break down `c' with k | k` into its components or cases. Distinguish the cases in `hk : k = L.i₀`. Substitute `hk` using the available equality.

Rewrite using `[r4]`. Use `hnq0.1 (Sum.inl L.i₀)` as an intermediate fact. Simplify using `only [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] at this`. Simplify using `[incM, this]`. Take `⟨j, rfl⟩` from `(L.rng k).1 hk`.

Rewrite using `[r1]`. Both sides reduce to the same expression. Distinguish the cases in `hk : k = L.i₀`. Substitute `hk` using the available equality. Rewrite using `[r3]`.

Establish `e1 : algebraMap F (AF F) a₀ • inclR (F` using `F) (AF F) δ = inclR (F := F) (AF F) z₀ := by`. Establish `: z₀ = algebraMap F E a₀ * δ` using `by rw [ha₀, div_mul_cancel₀ _ h.δ0]`. Rewrite using `[this, map_mul]`. Use `show algebraMap F (AF F) a₀ • ((1 : AF F) ⊗ₜ[F] δ) = (1 : AF F) ⊗ₜ[F] (algebraMap F E a₀) * (1 : AF F) ⊗ₜ[F] δ`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← Algebra.smul_def, TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← Algebra.algebraMap_eq_smul_one]`.

Rewrite using `[e1, hz₀]`. Simplify using `[incM, GlobalTheory.ThK.incV, GlobalTheory.EisBL.DoubledUnipotentRadical.cA_inclR, map_add, map_sum, map_mul]`. Take `⟨j, rfl⟩` from `(L.rng k).1 hk`. Rewrite using `[r2]`. Both sides reduce to the same expression.

Establish `hS : inFrame d.b s = sExp L e (GlobalTheory.ThK.incV F b₀)`. Establish `h1 : inFrame d.b (cM c.1) * inFrame d.b (cM c.1)⁻¹ = 1`. Rewrite using `[← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, mul_inv_cancel, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]`. Rewrite using `[hs_def, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hN, Matrix.mul_assoc, h1, Matrix.mul_one]`. Use `⟨s, c, g', hsr, w1_conj_sExp_mem_par2 h hS, hg'r, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hg', hG0]`. Both sides reduce to the same expression. Rewrite using `[hs_def, hn_def, map_inv]`. Use `group`.
-/
theorem stab_dec (h : Hyp L nb uM nb' w₁ cM δ) {x : d.G} (hx : x ∈ rat2 σ d.Y) (hf : Fix L x) :
    ∃ (s : d.G) (c : Cr L) (γ' : G2 σ L.Y), s ∈ rat2 σ d.Y ∧ w₁ * s * w₁⁻¹ ∈ par2 σ d.Y ∧ γ' ∈ rat2 σ L.Y ∧
      inFrame L.b γ' = (inFrame d.b x).submatrix (emS L) (emS L) ∧ x = s * (cM c.1 * L.j γ') := by
  have hσ := kfour.sigma_sigma_of_good d.ok.good
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨⟨ε', hε'⟩, -⟩ := L.ok.frame
  have hee : ε = ε' := Afc.eps_eq L hε hε'
  subst hee
  obtain ⟨G0, hG0⟩ := Afc.rat_frame (b := d.b) x hx
  have hx0 : ∀ r, G0 r (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) r (Sum.inl L.i₀) := by
    intro r
    apply kfour.inclR_injective (F := F)
    have h1 := hf r
    rw [hG0] at h1
    simp only [incM, Matrix.map_apply] at h1
    rw [h1]
    by_cases hr : r = Sum.inl L.i₀ <;> simp [Matrix.one_apply, hr]
  have hform := form_E hε x hG0
  have hy := yrow_zero hform hx0
  set H := G0.submatrix (emS L) (emS L) with hH_def
  have hH := blockH_form L hform hx0 hy
  have hε1 : (((ε : ℤ) : E)) * (((ε : ℤ) : E)) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hεσ : (σ : E →+* E) (((ε : ℤ) : E)) = ((ε : ℤ) : E) := map_intCast _ _
  obtain ⟨hHH', hH'H⟩ := kunf.frame_inv_pf (σ : E →+* E) hσ (((ε : ℤ) : E)) hε1 hεσ H hH
  set H' := Matrix.fromBlocks ((H.toBlocks₂₂.map (σ : E →+* E))ᵀ) ((((ε : ℤ) : E)) • (H.toBlocks₁₂.map (σ : E →+* E))ᵀ)
      ((((ε : ℤ) : E)) • (H.toBlocks₂₁.map (σ : E →+* E))ᵀ) ((H.toBlocks₁₁.map (σ : E →+* E))ᵀ) with hH'_def
  have hIA : incM F H * incM F H' = 1 := by rw [← kfour.incM_mul', hHH', Afc.incM_one']
  have hformA : (incM F H)ᵀ * kunf.jw L.n (((ε : ℤ) : AE F E)) * (incM F H).map (cA σ) =
      kunf.jw L.n (((ε : ℤ) : AE F E)) := by
    have h1 := congrArg (incM F) hH
    rw [kfour.incM_mul', kfour.incM_mul', ← Afc.incM_transpose, ← Afc.incM_map_cA, ← QA_eq] at h1
    exact h1
  obtain ⟨g', hg'⟩ := kunf.exists_of_frame (Y := L.Y) hε' (incM F H) (incM F H') hIA hformA
  have hg'r : g' ∈ rat2 σ L.Y := kunf.rat_of_inFrame hg'
  have hg'i : inFrame L.b g'⁻¹ = incM F H' := by
    rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_inv, hg']
    exact Matrix.inv_eq_right_inv hIA
  set n := x * L.j g'⁻¹ with hn_def
  have hnF : inFrame d.b n = incM F (G0 * padE L H') := by
    rw [hn_def, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hG0, inFrame_j, hg'i, padM_incM, kfour.incM_mul']
  have hnq0 : NQ (Sum.inl L.i₀) (Sum.inr L.i₀) (G0 * padE L H') := nq_E L hx0 hy hHH'
  have hnr : n ∈ rat2 σ d.Y := mul_mem hx (j_rat L (inv_mem hg'r))
  set N0 := G0 * padE L H' with hN0
  set u₀ : Fin L.n → E := fun j => N0 (Sum.inl L.i₀) (Sum.inl (L.em j)) with hu₀
  set b₀ : Fin L.n → E := fun j => N0 (Sum.inl L.i₀) (Sum.inr (L.em j)) with hb₀
  set z₀ : E := N0 (Sum.inl L.i₀) (Sum.inr L.i₀) + ∑ j, b₀ j * σ (u₀ j) with hz₀
  have hUN0 : M.U (σ : E →+* E) (((ε : ℤ) : E)) N0 := form_E hε n hnF
  have hpz : σ z₀ = -(((ε : ℤ) : E) * z₀) := M.even_im_hermitian_sub hσ hε1 hεσ L.em L.inj L.rng hUN0 hnq0
  have hpd := delta_par h hε
  have hε0 : (((ε : ℤ) : E)) ≠ 0 := fun h0 => by rw [h0, zero_mul] at hε1; exact zero_ne_one hε1
  have hfix : σ (z₀ / δ) = z₀ / δ := by
    rw [map_div₀, hpz, hpd, neg_div_neg_eq, mul_div_mul_left _ _ hε0]
  obtain ⟨a₀, ha₀⟩ := fixed_in_F d.ok.good.cm (z₀ / δ) hfix
  let c : Cr L := ⟨(GlobalTheory.ThK.incV F u₀, algebraMap F (AF F) a₀), AddSubgroup.subset_closure ⟨u₀, rfl⟩, ⟨a₀, rfl⟩⟩
  set s := n * (cM c.1)⁻¹ with hs_def
  have hsr : s ∈ rat2 σ d.Y := mul_mem hnr (inv_mem (cM_rat' h c.2.1 c.2.2))
  set e : AE F E := ((ε : ℤ) : AE F E) with he_def
  have he : e * e = 1 := by
    rw [he_def, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hse : (cA σ).toRingHom e = e := map_intCast _ _
  have hN : inFrame d.b n = sExp L e (GlobalTheory.ThK.incV F b₀) * inFrame d.b (cM c.1) := by
    apply M.nq_unique (s := (cA σ).toRingHom) (e := e) (i₀ := L.i₀) (cA_inv' hσ) he hse
    · exact kunf.frame_eq hε n
    · have hUS := U_sExp (ε := ε) (L := L) hσ (GlobalTheory.ThK.incV F b₀)
      have hUC : M.U (cA σ).toRingHom e (inFrame d.b (cM c.1)) := kunf.frame_eq hε (cM c.1)
      unfold M.U at hUS hUC ⊢
      rw [Matrix.transpose_mul, Matrix.map_mul]
      calc (inFrame d.b (cM c.1))ᵀ * (sExp L e (GlobalTheory.ThK.incV F b₀))ᵀ * kunf.jw d.n e *
            ((sExp L e (GlobalTheory.ThK.incV F b₀)).map (cA σ).toRingHom * (inFrame d.b (cM c.1)).map (cA σ).toRingHom)
          = (inFrame d.b (cM c.1))ᵀ * ((sExp L e (GlobalTheory.ThK.incV F b₀))ᵀ * kunf.jw d.n e *
            (sExp L e (GlobalTheory.ThK.incV F b₀)).map (cA σ).toRingHom) * (inFrame d.b (cM c.1)).map (cA σ).toRingHom := by
            simp only [Matrix.mul_assoc]
        _ = kunf.jw d.n e := by rw [hUS, hUC]
    · rw [hnF]; exact NQ.map _ hnq0
    · exact NQ.mul (nq_sExp _ _) (nq_cM h _)
    · obtain ⟨r1, r2, r3, r4⟩ := row_sC h e (GlobalTheory.ThK.incV F b₀) (GlobalTheory.ThK.incV F u₀) (algebraMap F (AF F) a₀)
      intro c'
      rw [hnF]
      rcases c' with k | k
      · by_cases hk : k = L.i₀
        · subst hk
          rw [r4]
          have := hnq0.1 (Sum.inl L.i₀)
          simp only [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] at this
          simp [incM, this]
        · obtain ⟨j, rfl⟩ := (L.rng k).1 hk
          rw [r1]; rfl
      · by_cases hk : k = L.i₀
        · subst hk
          rw [r3]
          have e1 : algebraMap F (AF F) a₀ • inclR (F := F) (AF F) δ = inclR (F := F) (AF F) z₀ := by
            have : z₀ = algebraMap F E a₀ * δ := by rw [ha₀, div_mul_cancel₀ _ h.δ0]
            rw [this, map_mul]
            show algebraMap F (AF F) a₀ • ((1 : AF F) ⊗ₜ[F] δ) = (1 : AF F) ⊗ₜ[F] (algebraMap F E a₀) * (1 : AF F) ⊗ₜ[F] δ
            rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← Algebra.smul_def, TensorProduct.tmul_smul,
              TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← Algebra.algebraMap_eq_smul_one]
          rw [e1, hz₀]
          simp [incM, GlobalTheory.ThK.incV, GlobalTheory.EisBL.DoubledUnipotentRadical.cA_inclR, map_add, map_sum, map_mul]
        · obtain ⟨j, rfl⟩ := (L.rng k).1 hk
          rw [r2]; rfl
  have hS : inFrame d.b s = sExp L e (GlobalTheory.ThK.incV F b₀) := by
    have h1 : inFrame d.b (cM c.1) * inFrame d.b (cM c.1)⁻¹ = 1 := by
      rw [← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, mul_inv_cancel, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
    rw [hs_def, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hN, Matrix.mul_assoc, h1, Matrix.mul_one]
  refine ⟨s, c, g', hsr, w1_conj_sExp_mem_par2 h hS, hg'r, ?_, ?_⟩
  · rw [hg', hG0]; rfl
  · rw [hs_def, hn_def, map_inv]; group

end PositivityTheory.SiegelWeilFormula.Act.C6

end
