import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TiedAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensorOneApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalSelfDualLatticeSplitPlaceDecomposition
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIdempotentMulIdemSumEqZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSplitPlaceHermitianFrameGLEmbedding
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPeriodIdealLocalGeneratorAtSplitPointStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StdHomLatticePointIntegralMatrixAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralMatrixSplitPlaceMemStdHomLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HalfDoubleAnn

/- English proof (translation)
Introduce `D k _ _ _ _ q S T`. Take `⟨a₀, ha₀, hne, hdiv⟩` from `GlobalTheory.T.exists_periodIdeal_local_generator_at_split_point D k q`. Use `set c := q.pr (incA D a₀) with hc`. Use `set G : Matrix (Fin S.rank) (Fin S.rank) k := c • (HSpace.gram S).map (fun a => q.pr (incA D a)) with hG`. Establish `hdet : IsUnit G.det`.

Rewrite using `[hG, Matrix.det_smul, isUnit_iff_ne_zero]`. Use `mul_ne_zero (pow_ne_zero _ hne) ?_` and prove the remaining obligations. Establish `h` using `(RingHom.map_det (q.pr.comp (incA D)) (HSpace.gram S)).symm`. Simplify using `only [RingHom.mapMatrix_apply, RingHom.coe_comp] at h`. Express the relevant statement in the definitionally equal form `(Matrix.map (HSpace.gram S) (⇑q.pr ∘ ⇑(incA D))).det ≠ 0`.

Rewrite using `[h]`. Conclude with `(map_ne_zero_iff _ (q.pr.comp (incA D)).injective).2 (GlobalTheory.FrameCont.gram_det_isUnit S).ne_zero`. Set `FS : Frame k S.rank (Fin S.rank)` to `⟨G⁻¹, G, Matrix.nonsing_inv_mul G hdet, Matrix.mul_nonsing_inv G hdet⟩`. Set `FT : Frame k T.rank (Fin T.rank)` to `⟨1, 1, mul_one 1, mul_one 1⟩`. Conclude with `⟨FS, FT, GlobalTheory.T.stdHomLattice_point_integral_matrix_at_split_place D k q S T c hne hdiv FS FT rfl rfl rfl, GlobalTheory.T.integral_matrix_split_place_mem_stdHomLattice D k q S T a₀ ha₀ hne FS FT rfl rfl rfl⟩`.
-/
theorem frames_stdHom : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S T : HSp D), ∃ (FS : Frame k S.rank (Fin S.rank)) (FT : Frame k T.rank (Fin T.rank)), (∀ u ∈ stdHom S T, ∀ r s, (Place.ofSplitPt q).down FS FT u r s ∈ 𝒪[k]) ∧ (∀ t : Matrix (Fin T.rank) (Fin S.rank) k, (∀ r s, t r s ∈ 𝒪[k]) → (Place.ofSplitPt q).up FS FT t ∈ stdHom S T) := by
  intro D k _ _ _ _ q S T
  obtain ⟨a₀, ha₀, hne, hdiv⟩ := GlobalTheory.T.exists_periodIdeal_local_generator_at_split_point D k q
  set c := q.pr (incA D a₀) with hc
  set G : Matrix (Fin S.rank) (Fin S.rank) k := c • (HSpace.gram S).map (fun a => q.pr (incA D a)) with hG
  have hdet : IsUnit G.det := by
    rw [hG, Matrix.det_smul, isUnit_iff_ne_zero]
    refine mul_ne_zero (pow_ne_zero _ hne) ?_
    have h := (RingHom.map_det (q.pr.comp (incA D)) (HSpace.gram S)).symm
    simp only [RingHom.mapMatrix_apply, RingHom.coe_comp] at h
    change (Matrix.map (HSpace.gram S) (⇑q.pr ∘ ⇑(incA D))).det ≠ 0
    rw [h]
    exact (map_ne_zero_iff _ (q.pr.comp (incA D)).injective).2 (GlobalTheory.FrameCont.gram_det_isUnit S).ne_zero
  let FS : Frame k S.rank (Fin S.rank) := ⟨G⁻¹, G, Matrix.nonsing_inv_mul G hdet, Matrix.mul_nonsing_inv G hdet⟩
  let FT : Frame k T.rank (Fin T.rank) := ⟨1, 1, mul_one 1, mul_one 1⟩
  exact ⟨FS, FT, GlobalTheory.T.stdHomLattice_point_integral_matrix_at_split_place D k q S T c hne hdiv FS FT rfl rfl rfl, GlobalTheory.T.integral_matrix_split_place_mem_stdHomLattice D k q S T a₀ ha₀ hne FS FT rfl rfl rfl⟩

variable {D : D7}

/- English proof (translation)
Unfold `symplO hO`. Use `congr 2`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Establish `h : cA D (l c b) = e * cA D (l c b)` using `by conv_lhs => rw [← hl c b]`. Rewrite using `[map_mul, cA_cA]`.

Rewrite using `[Matrix.map_apply]`. Use `conv_lhs => rw [h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem symplO_idem_left (S T : HSp D) {e : AE D} {l : WO S T} (hl : IsHalf (cA D e) l) (u : WO S T) :
    symplO S T u l = symplO S T (u.map (e * ·)) l := by
  unfold symplO hO
  congr 2
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun d _ => ?_
  have h : cA D (l c b) = e * cA D (l c b) := by
    conv_lhs => rw [← hl c b]
    rw [map_mul, cA_cA]
  rw [Matrix.map_apply]
  conv_lhs => rw [h]
  ring

/- English proof (translation)
Establish `h` using `q.sec_pr 1`. Rewrite `h` using `[mul_one]`. Rewrite using `[← h, q.pr_sec, map_one]`.
-/
theorem pr_e {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) : q.pr q.e = 1 := by
  have h := q.sec_pr 1
  rw [mul_one] at h
  rw [← h, q.pr_sec, map_one]

/- English proof (translation)
Rewrite using `[hsum, Finset.sum_mul, Finset.sum_eq_single PP]`. Conclude with `(hes PP hPP).1.1`. Introduce `PP' hPP' hne`. Establish `hs` using `(hes PP hPP).1`. Take `⟨v, ε, h1, h2⟩` from `hs.2.2`.

Take `⟨q, hq, -⟩` from `GlobalTheory.FinPl.SplitPoint.exists_splitPt D v (es PP) ε hs h1 h2`. Establish `hsum' : IsIdemSum (es PP') {PP'}` using `⟨⟨fun _ => es PP', fun P hP => by rw [Finset.mem_singleton] at hP; subst hP; exact hes _ hPP', by simp⟩, (hes PP' hPP').1.2.1⟩`. Use `OutsideOrth.mul_eq_zero D _ (Place.ofSplitPt q) {PP'} PP (es PP') (by rw [Finset.mem_singleton]; exact fun h => hne h.symm) (by rw [show (Place.ofSplitPt q).e = es PP from hq]; exact hes PP hPP) hsum'` as an intermediate fact. Rewrite `this` using `[show (Place.ofSplitPt q).e = es PP from hq]`. Then use the resulting hypothesis. Introduce `h`.

Conclude with `absurd hPP h`.
-/
theorem mul_idem_of_mem {E₂ : AE D} {Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {es : Formalism.L2.DIV.Pl D.host.E → AE D}
    (hes : ∀ PP ∈ Q, Formalism.L2.NTheta.IsIdemAt (es PP) PP) (hsum : E₂ = ∑ PP ∈ Q, es PP) {PP : Formalism.L2.DIV.Pl D.host.E}
    (hPP : PP ∈ Q) : E₂ * es PP = es PP := by
  rw [hsum, Finset.sum_mul, Finset.sum_eq_single PP]
  · exact (hes PP hPP).1.1
  · intro PP' hPP' hne
    have hs := (hes PP hPP).1
    obtain ⟨v, ε, h1, h2⟩ := hs.2.2
    obtain ⟨q, hq, -⟩ := GlobalTheory.FinPl.SplitPoint.exists_splitPt D v (es PP) ε hs h1 h2
    have hsum' : IsIdemSum (es PP') {PP'} :=
      ⟨⟨fun _ => es PP', fun P hP => by rw [Finset.mem_singleton] at hP; subst hP; exact hes _ hPP', by simp⟩,
        (hes PP' hPP').1.2.1⟩
    have := OutsideOrth.mul_eq_zero D _ (Place.ofSplitPt q) {PP'} PP (es PP')
      (by rw [Finset.mem_singleton]; exact fun h => hne h.symm) (by rw [show (Place.ofSplitPt q).e = es PP from hq]; exact hes PP hPP) hsum'
    rwa [show (Place.ofSplitPt q).e = es PP from hq] at this
  · intro h; exact absurd hPP h

end GlobalTheory.HalfDoubleAnn

namespace GlobalTheory.HalfDoubleAnn
variable {D : D7}

/- English proof (translation)
Take `⟨v, ε, h1, h2⟩` from `he.2.2`. Take `⟨q, hq, -⟩` from `GlobalTheory.FinPl.SplitPoint.exists_splitPt D v e ε he h1 h2`. Substitute `hq` using the available equality. Take `⟨FS, FT, hF1, hF2⟩` from `frames_stdHom D _ q S T`. Take `⟨Λ, -, h2, -, h4, -, h6⟩` from `GlobalTheory.SplitSelfDual.selfDual_lattice_split D _ (Place.ofSplitPt q) ψ hψ S T (Fin T.rank) (Fin S.rank) FS FT`.

Establish `hdown : ∀ u : WO S T, (Place.ofSplitPt q).down FS FT (u.map (q.e * ·)) = (Place.ofSplitPt q).down FS FT u`. Introduce `u`. Unfold `Place.down`. Use `congr 2`. Use extensionality with `i j`.

Simplify using `only [Matrix.map_apply]`. Establish `h1 : (Place.ofSplitPt q).π q.e = 1` using `pr_e q`. Rewrite using `[map_mul, h1, one_mul]`. Establish `hhalf : ∀ u : WO S T, IsHalf q.e (u.map (q.e * ·))` using `fun u i j => by`. Rewrite using `[Matrix.map_apply, ← mul_assoc, he.1]`.

Use `set y := x.map (q.e * ·) with hy`. Assume the negation of the conclusion as `hyn`. Establish `hyup : (Place.ofSplitPt q).up FS FT ((Place.ofSplitPt q).down FS FT y) = y` using `Witness.up_down (Place.ofSplitPt q) FS FT (hhalf x)`. Establish `hnint : ¬ ∀ r s, (Place.ofSplitPt q).down FS FT y r s ∈ 𝒪[_]` using `fun hint => hyn (hyup ▸ hF2 _ hint)`. Establish `hyΛ : y ∉ Λ` using `fun hm => hnint ((h4 _).1 (hyup.symm ▸ hm))`.

Take `⟨l, hlΛ, hlc, hl⟩` from `h2 y (hhalf x) hyΛ`. Establish `hlc' : IsHalf (cA D q.e) l` using `hlc`. Establish `hlE : IsHalf (cA D E₂) l` using `fun i j => by`. Rewrite using `[← hlc' i j, ← mul_assoc, ← map_mul, hEe]`. Establish `key` using `H l hlE fun x' hx' _ => by`.

Rewrite using `[symplO_idem_left S T hlc' x', ← Witness.up_down (Place.ofSplitPt q) FS FT (hhalf x'), hdown]`. Conclude with `h6 l hlΛ hlc _ (hF1 x' hx')`. Rewrite `key` using `[symplO_idem_left S T hlc' x, GlobalTheory.SplitScalar.symplO_skew]`. Use `GlobalTheory.SplitSelfDual.psi_neg_eq_one key` as an intermediate fact. Rewrite `this` using `[neg_neg]`.

Conclude with `hl this`.
-/
theorem idem_part_mem (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (E₂ e : AE D)
    (he : IsSplitIdem D e) (hEe : E₂ * e = e) (x : WO S T)
    (H : ∀ y : WO S T, IsHalf (cA D E₂) y → (∀ x' ∈ stdHom S T, IsHalf E₂ x' → ψ (symplO S T x' y) = 1) →
      ψ (symplO S T x y) = 1) :
    x.map (e * ·) ∈ stdHom S T := by
  obtain ⟨v, ε, h1, h2⟩ := he.2.2
  obtain ⟨q, hq, -⟩ := GlobalTheory.FinPl.SplitPoint.exists_splitPt D v e ε he h1 h2
  subst hq
  obtain ⟨FS, FT, hF1, hF2⟩ := frames_stdHom D _ q S T
  obtain ⟨Λ, -, h2, -, h4, -, h6⟩ := GlobalTheory.SplitSelfDual.selfDual_lattice_split D _ (Place.ofSplitPt q) ψ hψ S T (Fin T.rank) (Fin S.rank) FS FT
  have hdown : ∀ u : WO S T, (Place.ofSplitPt q).down FS FT (u.map (q.e * ·)) = (Place.ofSplitPt q).down FS FT u := by
    intro u
    unfold Place.down
    congr 2
    ext i j
    simp only [Matrix.map_apply]
    have h1 : (Place.ofSplitPt q).π q.e = 1 := pr_e q
    rw [map_mul, h1, one_mul]
  have hhalf : ∀ u : WO S T, IsHalf q.e (u.map (q.e * ·)) := fun u i j => by
    rw [Matrix.map_apply, ← mul_assoc, he.1]
  set y := x.map (q.e * ·) with hy
  by_contra hyn
  have hyup : (Place.ofSplitPt q).up FS FT ((Place.ofSplitPt q).down FS FT y) = y := Witness.up_down (Place.ofSplitPt q) FS FT (hhalf x)
  have hnint : ¬ ∀ r s, (Place.ofSplitPt q).down FS FT y r s ∈ 𝒪[_] := fun hint => hyn (hyup ▸ hF2 _ hint)
  have hyΛ : y ∉ Λ := fun hm => hnint ((h4 _).1 (hyup.symm ▸ hm))
  obtain ⟨l, hlΛ, hlc, hl⟩ := h2 y (hhalf x) hyΛ
  have hlc' : IsHalf (cA D q.e) l := hlc
  have hlE : IsHalf (cA D E₂) l := fun i j => by
    rw [← hlc' i j, ← mul_assoc, ← map_mul, hEe]
  have key := H l hlE fun x' hx' _ => by
    rw [symplO_idem_left S T hlc' x', ← Witness.up_down (Place.ofSplitPt q) FS FT (hhalf x'), hdown]
    exact h6 l hlΛ hlc _ (hF1 x' hx')
  rw [symplO_idem_left S T hlc' x, GlobalTheory.SplitScalar.symplO_skew] at key
  have := GlobalTheory.SplitSelfDual.psi_neg_eq_one key
  rw [neg_neg] at this
  exact hl this

/- English proof (translation)
Introduce `D ψ hψ S T Q E₂ hE x hx H`. Take `⟨⟨es, hes, hsum⟩, -⟩` from `hE`. Establish `hx' : x = ∑ PP ∈ Q, x.map (es PP * ·)`. Use extensionality with `i j`. Rewrite using `[Matrix.sum_apply, ← hx i j, hsum, Finset.sum_mul]`.

Both sides reduce to the same expression. Rewrite using `[hx']`. Conclude with `AddSubgroup.sum_mem _ fun PP hPP => idem_part_mem ψ hψ S T E₂ (es PP) (hes PP hPP).1 (mul_idem_of_mem hes hsum hPP) x H`.
-/
theorem mem_of_ann_ann : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (E₂ : AE D), IsIdemSum E₂ Q → ∀ x : WO S T, IsHalf E₂ x → (∀ y : WO S T, IsHalf (cA D E₂) y → (∀ x' ∈ stdHom S T, IsHalf E₂ x' → ψ (symplO S T x' y) = 1) → ψ (symplO S T x y) = 1) → x ∈ stdHom S T := by
  intro D ψ hψ S T Q E₂ hE x hx H
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := hE
  have hx' : x = ∑ PP ∈ Q, x.map (es PP * ·) := by
    ext i j
    rw [Matrix.sum_apply, ← hx i j, hsum, Finset.sum_mul]
    rfl
  rw [hx']
  exact AddSubgroup.sum_mem _ fun PP hPP =>
    idem_part_mem ψ hψ S T E₂ (es PP) (hes PP hPP).1 (mul_idem_of_mem hes hsum hPP) x H

end GlobalTheory.HalfDoubleAnn
