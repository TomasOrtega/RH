import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RealPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFrameOfRealizationModels
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LatticeSpanMembership
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.HeckeFrameShift

open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix
open scoped ComplexConjugate

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Establish `key : ∀ i j, ∑ p, ∑ q, τ (N p i) * τ (G p q) * conj (τ (N q j)) = τ (G i j)` using `fun i j => by`. Use `congrArg τ (hN (Pi.single i 1) (Pi.single j 1))` as an intermediate fact. Simplify using `only [herm, cc, Matrix.mulVec_single_one, Matrix.col_apply, map_sum, map_mul, IsCMField.complexEmbedding_complexConj] at this`. Rewrite using `[this]`. Simplify using `[Pi.single_apply, apply_ite, ite_mul]`.

Establish `e : hermC τ G (N.map τ *ᵥ u) (N.map τ *ᵥ v) = ∑ j, ∑ i, u i * (∑ p, ∑ q, τ (N p i) * τ (G p q) * conj (τ (N q j))) * conj (v j)`. Simplify using `only [hermC, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_congr rfl fun p _ => Finset.sum_comm, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_congr rfl fun p _ => Finset.sum_comm, Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring` and prove the remaining obligations. Rewrite using `[e, Finset.sum_comm]`. Simplify using `only [key, hermC]`.
-/
theorem hermC_mulVec (τ : E →+* ℂ) (G N : Matrix (Fin r) (Fin r) E)
    (hN : ∀ u v, herm G (N *ᵥ u) (N *ᵥ v) = herm G u v) (u v : Fin r → ℂ) :
    hermC τ G (N.map τ *ᵥ u) (N.map τ *ᵥ v) = hermC τ G u v := by
  classical
  have key : ∀ i j, ∑ p, ∑ q, τ (N p i) * τ (G p q) * conj (τ (N q j)) = τ (G i j) := fun i j => by
    have := congrArg τ (hN (Pi.single i 1) (Pi.single j 1))
    simp only [herm, cc, Matrix.mulVec_single_one, Matrix.col_apply, map_sum, map_mul,
      IsCMField.complexEmbedding_complexConj] at this
    rw [this]
    simp [Pi.single_apply, apply_ite, ite_mul]
  have e : hermC τ G (N.map τ *ᵥ u) (N.map τ *ᵥ v) =
      ∑ j, ∑ i, u i * (∑ p, ∑ q, τ (N p i) * τ (G p q) * conj (τ (N q j))) * conj (v j) := by
    simp only [hermC, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun p _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_congr rfl fun p _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  rw [e, Finset.sum_comm]
  simp only [key, hermC]

/- English proof (translation)
Establish `hu : ∀ t : E →+* ℂ, IsUnit (N.map t).det` using `fun t => by`. Establish `h` using `hN.map t`. Rewrite `h` using `[RingHom.map_det]`. Conclude with `h`. Establish `he : ∀ t : E →+* ℂ, Data.emb t (N *ᵥ v) = N.map t *ᵥ Data.emb t v` using `fun t => by`.

Use function extensionality and compare the values at `k`. Simplify using `[Data.emb, Matrix.mulVec, dotProduct, map_sum, map_mul]`. Unfold `perFr`. Distinguish the cases in `h1 : τ ∈ X.Ψ`. Rewrite using `[dif_pos h1, dif_pos ((hΨ _).1 h1)]`.

Distinguish the cases in `h2 : X.p0 + i < r`. Rewrite using `[dif_pos h2, dif_pos (hp ▸ h2), hx τ h1, he, Matrix.mul_inv_rev, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul_cancel_right _ _ (hu _)]`. Simplify using `only [hp]`. Rewrite using `[dif_neg h2, dif_neg (hp ▸ h2)]`. Rewrite using `[dif_neg h1, dif_neg (fun h' => h1 ((hΨ _).2 h'))]`.

Distinguish the cases in `h3 : conjEmb τ ∈ X.Ψ`. Rewrite using `[dif_pos h3, dif_pos ((hΨ _).1 h3)]`. Distinguish the cases in `h2 : X.p0 - 1 - i < r`. Rewrite using `[dif_pos h2, dif_pos (hp ▸ h2), hx _ h3, he]`. Establish `hc : ReciprocityTheory.ChartRestriction.G.FD.col (N.map (conjEmb τ) * mat x' ⟨conjEmb τ, (hΨ _).1 h3⟩) ⟨X.p0 - 1 - i, h2⟩ = N.map (conjEmb τ) *ᵥ ReciprocityTheory.ChartRestriction.G.FD.col (mat x' ⟨conjEmb τ, (hΨ _).1 h3⟩) ⟨X.p0 - 1 - i, h2⟩`.

Use function extensionality and compare the values at `a`. Simplify using `[ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Rewrite using `[hc, hermC_mulVec _ _ _ hNu, hG]`. Simplify using `only [hp]`. Rewrite using `[dif_neg h2, dif_neg (hp ▸ h2)]`.

Rewrite using `[dif_neg h3, dif_neg (fun h' => h3 ((hΨ _).2 h'))]`.
-/
theorem perFr_of_mat (X X' : Data E r) (hΨ : ∀ τ, τ ∈ X.Ψ ↔ τ ∈ X'.Ψ) (hp : X.p0 = X'.p0) (hG : X.Gm = X'.Gm)
    (N : Matrix (Fin r) (Fin r) E) (hN : IsUnit N.det) (hNu : ∀ u v, herm X.Gm (N *ᵥ u) (N *ᵥ v) = herm X.Gm u v)
    (x : Frame X.Ψ r) (x' : Frame X'.Ψ r)
    (hx : ∀ τ (h : τ ∈ X.Ψ), mat x ⟨τ, h⟩ = N.map τ * mat x' ⟨τ, (hΨ τ).1 h⟩)
    (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    perFr X x (N *ᵥ v) τ i = perFr X' x' v τ i := by
  have hu : ∀ t : E →+* ℂ, IsUnit (N.map t).det := fun t => by
    have h := hN.map t
    rw [RingHom.map_det] at h
    exact h
  have he : ∀ t : E →+* ℂ, Data.emb t (N *ᵥ v) = N.map t *ᵥ Data.emb t v := fun t => by
    funext k; simp [Data.emb, Matrix.mulVec, dotProduct, map_sum, map_mul]
  unfold perFr
  by_cases h1 : τ ∈ X.Ψ
  · rw [dif_pos h1, dif_pos ((hΨ _).1 h1)]
    by_cases h2 : X.p0 + i < r
    · rw [dif_pos h2, dif_pos (hp ▸ h2), hx τ h1, he, Matrix.mul_inv_rev, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul_cancel_right _ _ (hu _)]
      simp only [hp]
    · rw [dif_neg h2, dif_neg (hp ▸ h2)]
  · rw [dif_neg h1, dif_neg (fun h' => h1 ((hΨ _).2 h'))]
    by_cases h3 : conjEmb τ ∈ X.Ψ
    · rw [dif_pos h3, dif_pos ((hΨ _).1 h3)]
      by_cases h2 : X.p0 - 1 - i < r
      · rw [dif_pos h2, dif_pos (hp ▸ h2), hx _ h3, he]
        have hc : ReciprocityTheory.ChartRestriction.G.FD.col (N.map (conjEmb τ) * mat x' ⟨conjEmb τ, (hΨ _).1 h3⟩) ⟨X.p0 - 1 - i, h2⟩ =
            N.map (conjEmb τ) *ᵥ ReciprocityTheory.ChartRestriction.G.FD.col (mat x' ⟨conjEmb τ, (hΨ _).1 h3⟩) ⟨X.p0 - 1 - i, h2⟩ := by
          funext a; simp [ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.mul_apply, Matrix.mulVec, dotProduct]
        rw [hc, hermC_mulVec _ _ _ hNu, hG]
        simp only [hp]
      · rw [dif_neg h2, dif_neg (hp ▸ h2)]
    · rw [dif_neg h3, dif_neg (fun h' => h3 ((hΨ _).2 h'))]

end General

end GlobalTheory.HeckeFrameShift

namespace GlobalTheory.HeckeFrameShift

open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped ComplexConjugate TensorProduct

section HidaSetting

variable {D : D7}

/- English proof (translation)
Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `t (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) ((matHom V δ).1 i j)) = _`. Rewrite using `[show (matHom V δ).1 i j = (1 : AF D.host.F) ⊗ₜ[D.host.F] M i j from congrFun (congrFun hM i) j, Algebra.TensorProduct.map_tmul, map_one]`. Conclude with `ht.1 _`.
-/
theorem archM_rat {V : HSp D} {δ : GA D V} {M : Matrix (Fin V.rank) (Fin V.rank) D.host.E}
    (hM : Formalism.L2.Theta.mt V δ = M.map (Formalism.L2.Theta.incA D)) {τ : D.host.E →+* ℂ}
    {t : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ} (ht : Formalism.MainNotions.StandardLattice.IsInfEmb τ t) :
    archM V t δ = M.map τ := by
  ext i j
  change t (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) ((matHom V δ).1 i j)) = _
  rw [show (matHom V δ).1 i j = (1 : AF D.host.F) ⊗ₜ[D.host.F] M i j from congrFun (congrFun hM i) j,
    Algebra.TensorProduct.map_tmul, map_one]
  exact ht.1 _

/- English proof (translation)
Simplify using `only [archM, map_mul, Units.val_mul, Matrix.map_mul]`.
-/
theorem archM_mul (V : HSp D) (t : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (a b : GA D V) :
    archM V t (a * b) = archM V t a * archM V t b := by
  simp only [archM, map_mul, Units.val_mul, Matrix.map_mul]

/- English proof (translation)
Rewrite using `[archM, show infHom V a = 1 from ha, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]`.
-/
theorem archM_fin (V : HSp D) (t : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) {a : GA D V} (ha : a ∈ GfC V) :
    archM V t a = 1 := by
  rw [archM, show infHom V a = 1 from ha, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

/- English proof (translation)
Simplify using `only [herm, dotProduct, Matrix.mulVec, Matrix.neg_apply, Matrix.transpose_apply, Pi.star_apply, Finset.mul_sum, ← Finset.sum_neg_distrib]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by`. Rewrite using `[show star (v b) = cc (v b) from rfl]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_neg_transpose {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (u v : Fin n → D.host.E) :
    herm (-Jᵀ) u v = -(star v ⬝ᵥ J *ᵥ u) := by
  simp only [herm, dotProduct, Matrix.mulVec, Matrix.neg_apply, Matrix.transpose_apply, Pi.star_apply,
    Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by
    rw [show star (v b) = cc (v b) from rfl]; ring

end HidaSetting

end GlobalTheory.HeckeFrameShift

namespace GlobalTheory.HeckeFrameShift

open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped ComplexConjugate TensorProduct

section Shift

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Apply `GlobalTheory.MixModel.rat_injective` to reduce the goal to its premises. Establish `h` using `mt_rel (Wc D i) δ`. Rewrite `h` using `[hM]`. Rewrite using `[GlobalTheory.MixModel.rat_mul, GlobalTheory.MixModel.rat_mul, GlobalTheory.MixModel.rat_conjTranspose]`.

Conclude with `h`. Use `isUnit_iff_ne_zero.2 fun h0 => ?_` and prove the remaining obligations. Establish `h1` using `congrArg Matrix.det (Units.mul_inv (matHom (Wc D i) δ))`. Rewrite `h1` using `[Matrix.det_mul, Matrix.det_one]`. Express the relevant statement in the definitionally equal form `(Formalism.L2.Theta.mt (Wc D i) δ).det * _ = 1 at h1`.

Establish `e : (M.map (Formalism.L2.Theta.incA D)).det = Formalism.L2.Theta.incA D M.det` using `((Formalism.L2.Theta.incA D).map_det M).symm`. Rewrite `h1` using `[hM, e, h0, map_zero, zero_mul]`. Conclude with `zero_ne_one (GlobalTheory.MixModel.incA_injective (D := D) (by rw [map_zero, map_one]; exact h1))`.
-/
theorem unitary_of_mt {i : Fin D.R.m} {δ : GA D (Wc D i)} {M : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E}
    (hM : Formalism.L2.Theta.mt (Wc D i) δ = M.map (Formalism.L2.Theta.incA D)) :
    Mᴴ * (Wc D i).gram * M = (Wc D i).gram ∧ IsUnit M.det := by
  refine ⟨?_, ?_⟩
  · apply GlobalTheory.MixModel.rat_injective
    have h := mt_rel (Wc D i) δ
    rw [hM] at h
    rw [GlobalTheory.MixModel.rat_mul, GlobalTheory.MixModel.rat_mul, GlobalTheory.MixModel.rat_conjTranspose]
    exact h
  · refine isUnit_iff_ne_zero.2 fun h0 => ?_
    have h1 := congrArg Matrix.det (Units.mul_inv (matHom (Wc D i) δ))
    rw [Matrix.det_mul, Matrix.det_one] at h1
    change (Formalism.L2.Theta.mt (Wc D i) δ).det * _ = 1 at h1
    have e : (M.map (Formalism.L2.Theta.incA D)).det = Formalism.L2.Theta.incA D M.det := ((Formalism.L2.Theta.incA D).map_det M).symm
    rw [hM, e, h0, map_zero, zero_mul] at h1
    exact zero_ne_one (GlobalTheory.MixModel.incA_injective (D := D) (by rw [map_zero, map_one]; exact h1))

/- English proof (translation)
Establish `e : res T (sg0 D A) = T.σ₀`. Rewrite using `[show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0]`. Conclude with `res_embLL T hTie.alg hTie.laws.pins.2.2.1`. Establish `hg : GoodEmb T.Q.c (res T (sg0 D A))` using `e ▸ T.toCore.good_σ₀`. Take `rfl : σ = res T (sg0 D A)` from `hσ.trans e.symm`.

Establish `hB0` using `(GlobalTheory.HolDict.BaseFrame.baseFrT_of_tieIn D G Pl0 T0 A T R κ v₀ hMod hTie i _ hg hV).1`. Establish `hB : ∀ c t, t ∈ ((T.U ((i : ℕ) + 1) (res T (sg0 D A))).X c).Ψ → ∃ ρ, t = tauE D ρ` using `fun c t ht => (hB0 c t).1 ht`. Establish `hj : InR D ((i : ℕ) + 1)` using `⟨Nat.le_add_left _ _, i.2⟩`. Establish `hU` using `hTie.laws.unf _ hj _ hg`. Take `⟨hr, hmod⟩` from `hTie.laws.modelW _ hj _ hg`.

Establish `hr0` using `rank_Wc i`. Use `set N : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E := Matrix.reindex (finCongr hr0) (finCongr hr0) M with hN`. Use `set Gr : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E := Matrix.reindex (finCongr hr0) (finCongr hr0) (Wc D i).gram with hGr`. Establish `hGm : ∀ c, ((T.U ((i : ℕ) + 1) (res T (sg0 D A))).X c).Gm = -Grᵀ` using `fun c => by`. Rewrite using `[(hmod c).1]`.

Establish `key : ∀ (W : HSp D) (hW : W = Wc D i) (hr' : W.rank = D.R.r), -(Matrix.reindex (finCongr hr') (finCongr hr') W.gram)ᵀ = -Grᵀ`. Introduce and unpack `W rfl hr'`. Both sides reduce to the same expression. Conclude with `key _ hV hr`. Take `⟨hun, hdet⟩` from `unitary_of_mt hM`.

Establish `hNu : Nᴴ * Gr * N = Gr`. Simplify using `only [hN, hGr, Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hun]`. Establish `hNd : IsUnit N.det` using `by rw [hN, Matrix.det_reindex_self]; exact hdet`. Establish `hherm : ∀ c (u w : Fin D.R.r → D.host.E), herm ((T.U ((i : ℕ) + 1) (res T (sg0 D A))).X c).Gm (N *ᵥ u) (N *ᵥ w) = herm ((T.U ((i : ℕ) + 1) (res T (sg0 D A))).X c).Gm u w`. Introduce `c u w`.

Rewrite using `[hGm, herm_neg_transpose, herm_neg_transpose, Matrix.star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec, ← Matrix.mul_assoc, hNu]`. Establish `hin : a ∈ GfC (Wc D i)`. Take `⟨k₁, k₂, rfl⟩` from `hS.2.2.2.2.2.2.1 a ha`. Take `⟨_e, _ϖ, _h1, _h2, _h3, hα⟩` from `hS.2.2.2.2.2.1`. Conclude with `mul_mem (mul_mem k₁.2.1 hα.1) k₂.2.1`.

Establish `hΨ : ∀ t, t ∈ ((T.U ((i : ℕ) + 1) (res T (sg0 D A))).X (dictW T i _ hV h).1).Ψ ↔ t ∈ ((T.U ((i : ℕ) + 1) (res T (sg0 D A))).X (dictW T i _ hV (h * a)).1).Ψ` using `fun t => by rw [(hU.2.1 _).2 t, (hU.2.1 _).2 t]`. Establish `hx : ∀ t (ht : t ∈ ((T.U ((i : ℕ) + 1) (res T (sg0 D A))).X (dictW T i _ hV h).1).Ψ), mat (dictW T i _ hV h).2 ⟨t, ht⟩ = N.map t * mat (dictW T i _ hV (h * a)).2 ⟨t, (hΨ t).1 ht⟩`. Introduce `t ht`. Take `⟨ρ, hρ⟩` from `hB _ t ht`. Rewrite using `[hfr ρ ⟨t, ht⟩ hρ, hfr' ρ _ hρ, hρ]`.

Establish `e1 : γ * h = (γ * γ'⁻¹) * (γ' * (h * a)) * a⁻¹` using `by group`. Rewrite using `[e1, archM_mul, archM_mul, archM_fin _ _ (inv_mem hin), Matrix.mul_one, archM_rat hM (hMod.inf ρ), Matrix.mul_assoc]`. Simplify using `only [hN, Matrix.reindex_apply]`. Rewrite using `[← Matrix.submatrix_mul_equiv _ _ _ (finCongr hr0).symm _]`. Both sides reduce to the same expression.

Use `⟨fun u τ j => (perFr_of_mat _ _ hΨ ((hU.2.1 _).1.trans (hU.2.1 _).1.symm) ((hGm _).trans (hGm _).symm) N hNd (hherm _) _ _ hx u τ j).symm, hherm _, (hGm _).trans (hGm _).symm, (hmod _).2.trans (hmod _).2.symm⟩` and prove the remaining obligations.
-/
theorem shift_core (hMod : R.IsModels) (hTie : TieIn T R κ v₀) (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hσ : σ = T.σ₀)
    (hV : T.V ((i : ℕ) + 1) σ = Wc D i)
    {P : Formalism.L2.DIV.Pl D.host.E} {p k : ℕ} {α : GA D (Wc D i)} {Rc : Finset (GA D (Wc D i))}
    (hS : IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc) (h : GA D (Wc D i)) {a : GA D (Wc D i)} (ha : a ∈ Rc)
    {γ : GA D (Wc D i)} (hfr : FrAt (R.MW i (sg0 D A)) R.θ (rank_Wc i) (dictW T i σ hV) γ h)
    {γ' : GA D (Wc D i)} (hfr' : FrAt (R.MW i (sg0 D A)) R.θ (rank_Wc i) (dictW T i σ hV) γ' (h * a))
    {M : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E}
    (hM : Formalism.L2.Theta.mt (Wc D i) (γ * γ'⁻¹) = M.map (Formalism.L2.Theta.incA D)) :
    (∀ (u : Fin D.R.r → D.host.E) (τ : D.host.E →+* ℂ) (j : ℕ),
      perFr ((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV (h * a)).1) (dictW T i σ hV (h * a)).2 u τ j = perFr ((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV h).1) (dictW T i σ hV h).2 ((Matrix.reindex (finCongr (rank_Wc i)) (finCongr (rank_Wc i)) M) *ᵥ u) τ j) ∧
    (∀ u w : Fin D.R.r → D.host.E, herm ((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV h).1).Gm ((Matrix.reindex (finCongr (rank_Wc i)) (finCongr (rank_Wc i)) M) *ᵥ u) ((Matrix.reindex (finCongr (rank_Wc i)) (finCongr (rank_Wc i)) M) *ᵥ w) = herm ((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV h).1).Gm u w) ∧
    ((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV (h * a)).1).Gm = ((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV h).1).Gm ∧ ((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV (h * a)).1).ξ0 = ((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV h).1).ξ0 := by
  have e : res T (sg0 D A) = T.σ₀ := by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0]
    exact res_embLL T hTie.alg hTie.laws.pins.2.2.1
  have hg : GoodEmb T.Q.c (res T (sg0 D A)) := e ▸ T.toCore.good_σ₀
  obtain rfl : σ = res T (sg0 D A) := hσ.trans e.symm
  have hB0 := (GlobalTheory.HolDict.BaseFrame.baseFrT_of_tieIn D G Pl0 T0 A T R κ v₀ hMod hTie i _ hg hV).1
  have hB : ∀ c t, t ∈ ((T.U ((i : ℕ) + 1) (res T (sg0 D A))).X c).Ψ → ∃ ρ, t = tauE D ρ := fun c t ht => (hB0 c t).1 ht
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hU := hTie.laws.unf _ hj _ hg
  obtain ⟨hr, hmod⟩ := hTie.laws.modelW _ hj _ hg
  have hr0 := rank_Wc i
  set N : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E := Matrix.reindex (finCongr hr0) (finCongr hr0) M with hN
  set Gr : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E := Matrix.reindex (finCongr hr0) (finCongr hr0) (Wc D i).gram with hGr
  have hGm : ∀ c, ((T.U ((i : ℕ) + 1) (res T (sg0 D A))).X c).Gm = -Grᵀ := fun c => by
    rw [(hmod c).1]
    have key : ∀ (W : HSp D) (hW : W = Wc D i) (hr' : W.rank = D.R.r),
        -(Matrix.reindex (finCongr hr') (finCongr hr') W.gram)ᵀ = -Grᵀ := by
      rintro W rfl hr'
      rfl
    exact key _ hV hr
  obtain ⟨hun, hdet⟩ := unitary_of_mt hM
  have hNu : Nᴴ * Gr * N = Gr := by
    simp only [hN, hGr, Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hun]
  have hNd : IsUnit N.det := by rw [hN, Matrix.det_reindex_self]; exact hdet
  have hherm : ∀ c (u w : Fin D.R.r → D.host.E), herm ((T.U ((i : ℕ) + 1) (res T (sg0 D A))).X c).Gm (N *ᵥ u) (N *ᵥ w) = herm ((T.U ((i : ℕ) + 1) (res T (sg0 D A))).X c).Gm u w := by
    intro c u w
    rw [hGm, herm_neg_transpose, herm_neg_transpose, Matrix.star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec, ← Matrix.mul_assoc, hNu]
  have hin : a ∈ GfC (Wc D i) := by
    obtain ⟨k₁, k₂, rfl⟩ := hS.2.2.2.2.2.2.1 a ha
    obtain ⟨_e, _ϖ, _h1, _h2, _h3, hα⟩ := hS.2.2.2.2.2.1
    exact mul_mem (mul_mem k₁.2.1 hα.1) k₂.2.1
  have hΨ : ∀ t, t ∈ ((T.U ((i : ℕ) + 1) (res T (sg0 D A))).X (dictW T i _ hV h).1).Ψ ↔ t ∈ ((T.U ((i : ℕ) + 1) (res T (sg0 D A))).X (dictW T i _ hV (h * a)).1).Ψ :=
    fun t => by rw [(hU.2.1 _).2 t, (hU.2.1 _).2 t]
  have hx : ∀ t (ht : t ∈ ((T.U ((i : ℕ) + 1) (res T (sg0 D A))).X (dictW T i _ hV h).1).Ψ), mat (dictW T i _ hV h).2 ⟨t, ht⟩ =
      N.map t * mat (dictW T i _ hV (h * a)).2 ⟨t, (hΨ t).1 ht⟩ := by
    intro t ht
    obtain ⟨ρ, hρ⟩ := hB _ t ht
    rw [hfr ρ ⟨t, ht⟩ hρ, hfr' ρ _ hρ, hρ]
    have e1 : γ * h = (γ * γ'⁻¹) * (γ' * (h * a)) * a⁻¹ := by group
    rw [e1, archM_mul, archM_mul, archM_fin _ _ (inv_mem hin), Matrix.mul_one,
      archM_rat hM (hMod.inf ρ), Matrix.mul_assoc]
    simp only [hN, Matrix.reindex_apply]
    rw [← Matrix.submatrix_mul_equiv _ _ _ (finCongr hr0).symm _]
    rfl
  refine ⟨fun u τ j => (perFr_of_mat _ _ hΨ ((hU.2.1 _).1.trans (hU.2.1 _).1.symm) ((hGm _).trans (hGm _).symm) N hNd
    (hherm _) _ _ hx u τ j).symm, hherm _, (hGm _).trans (hGm _).symm, (hmod _).2.trans (hmod _).2.symm⟩

/- English proof (translation)
Rewrite using `[(shift_core hMod hTie i σ hσ hV hS h ha hfr hfr' hM).1]`. Use `congr 1`. Use function extensionality and compare the values at `m`. Simplify using `only [Matrix.reindex_apply, Matrix.mulVec, dotProduct, Matrix.submatrix_apply]`. Conclude with `Equiv.sum_comp (finCongr (rank_Wc i)).symm (fun n => M (Fin.cast (rank_Wc i).symm m) n * v n)`.
-/
theorem perFr_shift (hMod : R.IsModels) (hTie : TieIn T R κ v₀) (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hσ : σ = T.σ₀)
    (hV : T.V ((i : ℕ) + 1) σ = Wc D i)
    {P : Formalism.L2.DIV.Pl D.host.E} {p k : ℕ} {α : GA D (Wc D i)} {Rc : Finset (GA D (Wc D i))}
    (hS : IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc) (h : GA D (Wc D i)) {a : GA D (Wc D i)} (ha : a ∈ Rc)
    {γ : GA D (Wc D i)} (hfr : FrAt (R.MW i (sg0 D A)) R.θ (rank_Wc i) (dictW T i σ hV) γ h)
    {γ' : GA D (Wc D i)} (hfr' : FrAt (R.MW i (sg0 D A)) R.θ (rank_Wc i) (dictW T i σ hV) γ' (h * a))
    {M : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E}
    (hM : Formalism.L2.Theta.mt (Wc D i) (γ * γ'⁻¹) = M.map (Formalism.L2.Theta.incA D))
    (v : Fin (Wc D i).rank → D.host.E) (τ : D.host.E →+* ℂ) (j : ℕ) :
    perFr ((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV (h * a)).1) (dictW T i σ hV (h * a)).2 (fun m => v (Fin.cast (rank_Wc i).symm m)) τ j =
      perFr ((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV h).1) (dictW T i σ hV h).2 (fun m => (M *ᵥ v) (Fin.cast (rank_Wc i).symm m)) τ j := by
  rw [(shift_core hMod hTie i σ hσ hV hS h ha hfr hfr' hM).1]
  congr 1
  funext m
  simp only [Matrix.reindex_apply, Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
  exact Equiv.sum_comp (finCongr (rank_Wc i)).symm (fun n => M (Fin.cast (rank_Wc i).symm m) n * v n)

end Shift

end GlobalTheory.HeckeFrameShift

namespace GlobalTheory.HeckeFrameShift

open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues
open scoped ComplexConjugate

section Period

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom}

/- English proof (translation)
Establish `he : ∀ τ : D.host.E →+* ℂ, Data.emb τ (q • v) = (q : ℂ) • Data.emb τ v` using `fun τ => by`. Use function extensionality and compare the values at `a`. Simplify using `[Data.emb, Rat.smul_def]`. Use function extensionality and compare the values at `j`. Simplify using `only [perVec, Pi.smul_apply, smul_eq_mul]`.

Unfold `perFr`. Use `split_ifs`. Rewrite using `[he, Matrix.mulVec_smul]`. Both sides reduce to the same expression. Simplify using the standard rewrite rules.

Simplify using `only [he, hermC, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul, map_ratCast]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem perVec_qsmul (Wt : UnfAt U k x) (q : ℚ) (v : Fin r → D.host.E) :
    perVec Wt (q • v) = (q : ℂ) • perVec Wt v := by
  have he : ∀ τ : D.host.E →+* ℂ, Data.emb τ (q • v) = (q : ℂ) • Data.emb τ v := fun τ => by
    funext a; simp [Data.emb, Rat.smul_def]
  funext j
  simp only [perVec, Pi.smul_apply, smul_eq_mul]
  unfold perFr
  split_ifs
  · rw [he, Matrix.mulVec_smul]; rfl
  · simp
  · simp only [he, hermC, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul, map_ratCast]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  · simp
  · simp

/- English proof (translation)
Simplify using `only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, RCLike.star_def, Complex.conj_natCast]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hermForm_natCast_smul {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (n m : ℕ) (z w : Fin g → ℂ) :
    hermForm Hm ((n : ℂ) • z) ((m : ℂ) • w) = (n : ℂ) * m * hermForm Hm z w := by
  simp only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
    RCLike.star_def, Complex.conj_natCast]
  ring

/- English proof (translation)
Simplify using `only [herm, cc, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring`.
-/
theorem herm_natCast_smul (G : Matrix (Fin r) (Fin r) D.host.E) (n m : ℕ) (u w : Fin r → D.host.E) :
    herm G ((n : D.host.E) • u) ((m : D.host.E) • w) = (n : D.host.E) * m * herm G u w := by
  simp only [herm, cc, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/- English proof (translation)
Establish `hlat : ∀ a b, (hermForm Y.Hm (perVec Wt (Wt.φ k a : Fin r → D.host.E)) (perVec Wt (Wt.φ k b : Fin r → D.host.E))).im = ((Algebra.trace ℚ D.host.E (-(U.X k).ξ0 * herm (U.X k).Gm (Wt.φ k a : Fin r → D.host.E) (Wt.φ k b)) : ℚ) : ℝ)` using `fun a b => by`. Rewrite using `[perVec_lat, perVec_lat, Y.c1 a b, ← Wt.isom k a b]`. Use `push_cast`. Both sides reduce to the same expression. Take `⟨n, hn, hnu⟩` from `ReciprocityTheory.ChartRestriction.G.FD.LatticeSpanMembership.exists_nat_smul_mem (X := U.X k) u`.

Take `⟨m, hm, hmw⟩` from `ReciprocityTheory.ChartRestriction.G.FD.LatticeSpanMembership.exists_nat_smul_mem (X := U.X k) w`. Establish `h` using `hlat ((Wt.φ k).symm ⟨_, hnu⟩) ((Wt.φ k).symm ⟨_, hmw⟩)`. Simplify using `only [LinearEquiv.apply_symm_apply] at h`. Establish `hs : ∀ (t : ℕ) (y : Fin r → D.host.E), (t : D.host.E) • y = (t : ℚ) • y` using `fun t y => by`. Rewrite using `[Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]`.

Rewrite `h` using `[hs n u, hs m w, perVec_qsmul, perVec_qsmul, ← hs n u, ← hs m w, herm_natCast_smul]`. Simplify using `only [Rat.cast_natCast] at h`. Rewrite `h` using `[hermForm_natCast_smul]`. Establish `ht : Algebra.trace ℚ D.host.E (-(U.X k).ξ0 * ((n : D.host.E) * m * herm (U.X k).Gm u w)) = (n * m : ℚ) * Algebra.trace ℚ D.host.E (-(U.X k).ξ0 * herm (U.X k).Gm u w)`. Rewrite using `[show -(U.X k).ξ0 * ((n : D.host.E) * m * herm (U.X k).Gm u w) = ((n * m : ℚ) : ℚ) • (-(U.X k).ξ0 * herm (U.X k).Gm u w) by rw [Rat.smul_def]; push_cast; ring, map_smul, smul_eq_mul]`.

Rewrite `h` using `[ht]`. Establish `hnm : ((n : ℝ) * m) ≠ 0` using `by positivity`. Establish `h2 : ((n : ℂ) * m * hermForm Y.Hm (perVec Wt u) (perVec Wt w)).im = (n : ℝ) * m * (hermForm Y.Hm (perVec Wt u) (perVec Wt w)).im`. Rewrite using `[show ((n : ℂ) * m) = (((n : ℝ) * m : ℝ) : ℂ) by push_cast; ring, Complex.im_ofReal_mul]`. Rewrite `h` using `[h2]`.

Move the coercions through the operations in `at h`. Conclude with `mul_left_cancel₀ hnm h`.
-/
theorem im_hermForm_perVec (Wt : UnfAt U k x) (Y : UnitAt Wt) (u w : Fin r → D.host.E) :
    (hermForm Y.Hm (perVec Wt u) (perVec Wt w)).im =
      ((Algebra.trace ℚ D.host.E (-(U.X k).ξ0 * herm (U.X k).Gm u w) : ℚ) : ℝ) := by
  have hlat : ∀ a b, (hermForm Y.Hm (perVec Wt (Wt.φ k a : Fin r → D.host.E)) (perVec Wt (Wt.φ k b : Fin r → D.host.E))).im =
      ((Algebra.trace ℚ D.host.E (-(U.X k).ξ0 * herm (U.X k).Gm (Wt.φ k a : Fin r → D.host.E) (Wt.φ k b)) : ℚ) : ℝ) :=
    fun a b => by
      rw [perVec_lat, perVec_lat, Y.c1 a b, ← Wt.isom k a b]
      push_cast
      rfl
  obtain ⟨n, hn, hnu⟩ := ReciprocityTheory.ChartRestriction.G.FD.LatticeSpanMembership.exists_nat_smul_mem (X := U.X k) u
  obtain ⟨m, hm, hmw⟩ := ReciprocityTheory.ChartRestriction.G.FD.LatticeSpanMembership.exists_nat_smul_mem (X := U.X k) w
  have h := hlat ((Wt.φ k).symm ⟨_, hnu⟩) ((Wt.φ k).symm ⟨_, hmw⟩)
  simp only [LinearEquiv.apply_symm_apply] at h
  have hs : ∀ (t : ℕ) (y : Fin r → D.host.E), (t : D.host.E) • y = (t : ℚ) • y := fun t y => by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rw [hs n u, hs m w, perVec_qsmul, perVec_qsmul, ← hs n u, ← hs m w, herm_natCast_smul] at h
  simp only [Rat.cast_natCast] at h
  rw [hermForm_natCast_smul] at h
  have ht : Algebra.trace ℚ D.host.E (-(U.X k).ξ0 * ((n : D.host.E) * m * herm (U.X k).Gm u w)) =
      (n * m : ℚ) * Algebra.trace ℚ D.host.E (-(U.X k).ξ0 * herm (U.X k).Gm u w) := by
    rw [show -(U.X k).ξ0 * ((n : D.host.E) * m * herm (U.X k).Gm u w) =
      ((n * m : ℚ) : ℚ) • (-(U.X k).ξ0 * herm (U.X k).Gm u w) by rw [Rat.smul_def]; push_cast; ring, map_smul, smul_eq_mul]
  rw [ht] at h
  have hnm : ((n : ℝ) * m) ≠ 0 := by positivity
  have h2 : ((n : ℂ) * m * hermForm Y.Hm (perVec Wt u) (perVec Wt w)).im =
      (n : ℝ) * m * (hermForm Y.Hm (perVec Wt u) (perVec Wt w)).im := by
    rw [show ((n : ℂ) * m) = (((n : ℝ) * m : ℝ) : ℂ) by push_cast; ring, Complex.im_ofReal_mul]
  rw [h2] at h
  push_cast at h
  exact mul_left_cancel₀ hnm h

/- English proof (translation)
Establish `hadd1 : ∀ (H : Matrix (Fin g) (Fin g) ℂ) z z' w, hermForm H (z + z') w = hermForm H z w + hermForm H z' w` using `fun H z z' w => by simp only [hermForm, add_dotProduct]`. Establish `hadd2 : ∀ (H : Matrix (Fin g) (Fin g) ℂ) z w w', hermForm H z (w + w') = hermForm H z w + hermForm H z w'` using `fun H z w w' => by simp only [hermForm, star_add, Matrix.mulVec_add, dotProduct_add]`. Establish `hsm1 : ∀ (H : Matrix (Fin g) (Fin g) ℂ) (a : ℂ) z w, hermForm H (a • z) w = a * hermForm H z w` using `fun H a z w => by simp only [hermForm, smul_dotProduct, smul_eq_mul]`. Establish `hsm2 : ∀ (H : Matrix (Fin g) (Fin g) ℂ) (a : ℂ) z w, hermForm H z (a • w) = star a * hermForm H z w` using `fun H a z w => by simp only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]`. Establish `key : ∀ z w, (hermForm Hm' z w).im = (hermForm Hm z w).im` using `fun z w => by`.

Establish `hz : z ∈ Submodule.span ℝ S` using `hS ▸ Submodule.mem_top`. Establish `hw : w ∈ Submodule.span ℝ S` using `hS ▸ Submodule.mem_top`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem a ha`. Proceed by induction on `hw using Submodule.span_induction with`.

Consider the case `mem b hb => exact him a ha b hb`. Consider the case `zero => simp [hermForm]`. Consider the case `add x y _ _ h1 h2 => simp only [hadd2, Complex.add_im, h1, h2]`. Consider the case `smul t x _ h1`. Rewrite using `[← Complex.coe_smul, hsm2, hsm2]`.

Simplify using `[h1]`. Consider the case `zero => simp [hermForm]`. Consider the case `add x y _ _ h1 h2 => simp only [hadd1, Complex.add_im, h1, h2]`. Consider the case `smul t x _ h1`. Rewrite using `[← Complex.coe_smul, hsm1, hsm1]`.

Simplify using `[h1]`. Use `Complex.ext ?_ (key z w)` and prove the remaining obligations. Use `key (Complex.I • z) w` as an intermediate fact. Rewrite `this` using `[hsm1, hsm1]`. Simplify using `using this`.
-/
theorem hermForm_eq_of_im_span {g : ℕ} (S : Set (Fin g → ℂ)) (hS : Submodule.span ℝ S = ⊤)
    (Hm Hm' : Matrix (Fin g) (Fin g) ℂ)
    (him : ∀ a ∈ S, ∀ b ∈ S, (hermForm Hm' a b).im = (hermForm Hm a b).im) (z w : Fin g → ℂ) :
    hermForm Hm' z w = hermForm Hm z w := by
  have hadd1 : ∀ (H : Matrix (Fin g) (Fin g) ℂ) z z' w, hermForm H (z + z') w = hermForm H z w + hermForm H z' w :=
    fun H z z' w => by simp only [hermForm, add_dotProduct]
  have hadd2 : ∀ (H : Matrix (Fin g) (Fin g) ℂ) z w w', hermForm H z (w + w') = hermForm H z w + hermForm H z w' :=
    fun H z w w' => by simp only [hermForm, star_add, Matrix.mulVec_add, dotProduct_add]
  have hsm1 : ∀ (H : Matrix (Fin g) (Fin g) ℂ) (a : ℂ) z w, hermForm H (a • z) w = a * hermForm H z w :=
    fun H a z w => by simp only [hermForm, smul_dotProduct, smul_eq_mul]
  have hsm2 : ∀ (H : Matrix (Fin g) (Fin g) ℂ) (a : ℂ) z w, hermForm H z (a • w) = star a * hermForm H z w :=
    fun H a z w => by simp only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  have key : ∀ z w, (hermForm Hm' z w).im = (hermForm Hm z w).im := fun z w => by
    have hz : z ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
    have hw : w ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem a ha =>
      induction hw using Submodule.span_induction with
      | mem b hb => exact him a ha b hb
      | zero => simp [hermForm]
      | add x y _ _ h1 h2 => simp only [hadd2, Complex.add_im, h1, h2]
      | smul t x _ h1 =>
        rw [← Complex.coe_smul, hsm2, hsm2]
        simp [h1]
    | zero => simp [hermForm]
    | add x y _ _ h1 h2 => simp only [hadd1, Complex.add_im, h1, h2]
    | smul t x _ h1 =>
      rw [← Complex.coe_smul, hsm1, hsm1]
      simp [h1]
  refine Complex.ext ?_ (key z w)
  have := key (Complex.I • z) w
  rw [hsm1, hsm1] at this
  simpa using this

/- English proof (translation)
Simplify using `[hermForm, Matrix.mulVec, dotProduct, Pi.single_apply]`.
-/
theorem hermForm_single {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (j₁ j₂ : Fin g) :
    hermForm Hm (Pi.single j₁ 1) (Pi.single j₂ 1) = Hm j₁ j₂ := by
  classical
  simp [hermForm, Matrix.mulVec, dotProduct, Pi.single_apply]

end Period

end GlobalTheory.HeckeFrameShift

namespace GlobalTheory.HeckeFrameShift

open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues

/- English proof (translation)
Substitute `hg` using the available equality. Both sides reduce to the same expression.
-/
theorem hermForm_cast {g g' : ℕ} (hg : g' = g) (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm (Hm.submatrix (Fin.cast hg) (Fin.cast hg)) (fun j => z (Fin.cast hg j)) (fun j => w (Fin.cast hg j)) =
      hermForm Hm z w := by
  subst hg
  rfl

section PeriodTwo

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} {k k' : U.Comp} {x : (U.X k).dom} {x' : (U.X k').dom}

/- English proof (translation)
Simplify using `only [perVec]`. Rewrite using `[he j j' hj]`. Conclude with `hu _ _`.
-/
theorem perVec_of_perFr (Wt : UnfAt U k x) (Wt' : UnfAt U k' x') (he : ∀ (j : Fin Wt'.g) (j' : Fin Wt.g), (j : ℕ) = j' → Wt'.e j = Wt.e j')
    (u u' : Fin r → D.host.E) (hu : ∀ τ j, perFr (U.X k') x'.1 u τ j = perFr (U.X k) x.1 u' τ j)
    (j : Fin Wt'.g) (j' : Fin Wt.g) (hj : (j : ℕ) = j') : perVec Wt' u j = perVec Wt u' j' := by
  simp only [perVec]
  rw [he j j' hj]
  exact hu _ _

/- English proof (translation)
Establish `hg : Wt'.g = Wt.g`. Establish `e1` using `Fintype.card_congr Wt'.e`. Establish `e2` using `Fintype.card_congr Wt.e`. Simplify using `only [Fintype.card_fin] at e1 e2`. Use linear arithmetic over natural numbers and integers.

Establish `hre : ∀ u, perVec Wt' u = fun j => perVec Wt (N *ᵥ u) (Fin.cast hg j)` using `fun u => funext fun j => hpv u j _ rfl`. Establish `hform : ∀ z w, hermForm Y'.Hm z w = hermForm (Y.Hm.submatrix (Fin.cast hg) (Fin.cast hg)) z w`. Use `hermForm_eq_of_im_span (Set.range Wt'.Pm) Wt'.per.2.2.2.1 _ _ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨b₁, rfl⟩ _ ⟨b₂, rfl⟩`. Rewrite using `[← perVec_lat Wt' b₁, ← perVec_lat Wt' b₂, im_hermForm_perVec, hre, hre, hermForm_cast hg, im_hermForm_perVec, hherm, hG, hξ]`.

Establish `e` using `hform (Pi.single j₁ 1) (Pi.single j₂ 1)`. Rewrite `e` using `[hermForm_single, hermForm_single, Matrix.submatrix_apply]`. Rewrite using `[e]`. Apply the tactic sequence `congr 1 <;> exact Fin.ext (by simpa)`.
-/
theorem hm_eq_of_shift (Wt : UnfAt U k x) (Y : UnitAt Wt) (Wt' : UnfAt U k' x') (Y' : UnitAt Wt')
    (N : Matrix (Fin r) (Fin r) D.host.E)
    (hpv : ∀ (u : Fin r → D.host.E) (j : Fin Wt'.g) (j' : Fin Wt.g), (j : ℕ) = j' → perVec Wt' u j = perVec Wt (N *ᵥ u) j')
    (hherm : ∀ u w : Fin r → D.host.E, herm (U.X k).Gm (N *ᵥ u) (N *ᵥ w) = herm (U.X k).Gm u w)
    (hG : (U.X k').Gm = (U.X k).Gm) (hξ : (U.X k').ξ0 = (U.X k).ξ0)
    (j₁ j₂ : Fin Wt'.g) (j₁' j₂' : Fin Wt.g) (h1 : (j₁ : ℕ) = j₁') (h2 : (j₂ : ℕ) = j₂') : Y'.Hm j₁ j₂ = Y.Hm j₁' j₂' := by
  have hg : Wt'.g = Wt.g := by
    have e1 := Fintype.card_congr Wt'.e
    have e2 := Fintype.card_congr Wt.e
    simp only [Fintype.card_fin] at e1 e2
    omega
  have hre : ∀ u, perVec Wt' u = fun j => perVec Wt (N *ᵥ u) (Fin.cast hg j) :=
    fun u => funext fun j => hpv u j _ rfl
  have hform : ∀ z w, hermForm Y'.Hm z w = hermForm (Y.Hm.submatrix (Fin.cast hg) (Fin.cast hg)) z w := by
    refine hermForm_eq_of_im_span (Set.range Wt'.Pm) Wt'.per.2.2.2.1 _ _ ?_
    rintro _ ⟨b₁, rfl⟩ _ ⟨b₂, rfl⟩
    rw [← perVec_lat Wt' b₁, ← perVec_lat Wt' b₂, im_hermForm_perVec, hre, hre, hermForm_cast hg,
      im_hermForm_perVec, hherm, hG, hξ]
  have e := hform (Pi.single j₁ 1) (Pi.single j₂ 1)
  rw [hermForm_single, hermForm_single, Matrix.submatrix_apply] at e
  rw [e]
  congr 1 <;> exact Fin.ext (by simpa)

end PeriodTwo

end GlobalTheory.HeckeFrameShift

namespace GlobalTheory.HeckeFrameShift

open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

section Witness

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

/- English proof (translation)
Take `⟨hcore, hherm, hG, hξ⟩` from `shift_core hMod hTie i σ hσ hV hS h ha hfr hfr' hM`. Establish `hfr0` using `perFr_shift hMod hTie i σ hσ hV hS h ha hfr hfr' hM`. Conclude with `⟨hfr0, fun v j j' hj => perVec_of_perFr Wt Wt' he _ _ (hfr0 v) j j' hj, hm_eq_of_shift Wt Y Wt' Y' _ (fun u j j' hj => perVec_of_perFr Wt Wt' he _ _ (hcore u) j j' hj) hherm hG hξ⟩`.
-/
theorem frame_shift_witness (hMod : R.IsModels) (hTie : TieIn T R κ v₀) (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hσ : σ = T.σ₀)
    (hV : T.V ((i : ℕ) + 1) σ = Wc D i)
    {P : Formalism.L2.DIV.Pl D.host.E} {p k : ℕ} {α : GA D (Wc D i)} {Rc : Finset (GA D (Wc D i))}
    (hS : IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc) (h : GA D (Wc D i)) {a : GA D (Wc D i)} (ha : a ∈ Rc)
    {γ : GA D (Wc D i)} (hfr : FrAt (R.MW i (sg0 D A)) R.θ (rank_Wc i) (dictW T i σ hV) γ h)
    {γ' : GA D (Wc D i)} (hfr' : FrAt (R.MW i (sg0 D A)) R.θ (rank_Wc i) (dictW T i σ hV) γ' (h * a))
    {M : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E}
    (hM : Formalism.L2.Theta.mt (Wc D i) (γ * γ'⁻¹) = M.map (Formalism.L2.Theta.incA D))
    (hx : (dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV h).1).dom)
    (hx' : (dictW T i σ hV (h * a)).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV (h * a)).1).dom)
    (Wt : UnfAt (T.U ((i : ℕ) + 1) σ) (dictW T i σ hV h).1 ⟨(dictW T i σ hV h).2, hx⟩) (Y : UnitAt Wt)
    (Wt' : UnfAt (T.U ((i : ℕ) + 1) σ) (dictW T i σ hV (h * a)).1 ⟨(dictW T i σ hV (h * a)).2, hx'⟩) (Y' : UnitAt Wt')
    (he : ∀ (j : Fin Wt'.g) (j' : Fin Wt.g), (j : ℕ) = j' → Wt'.e j = Wt.e j') :
    (∀ (v : Fin (Wc D i).rank → D.host.E) (τ : D.host.E →+* ℂ) (j : ℕ),
      perFr ((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV (h * a)).1) (dictW T i σ hV (h * a)).2 (fun m => v (Fin.cast (rank_Wc i).symm m)) τ j =
        perFr ((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV h).1) (dictW T i σ hV h).2 (fun m => (M *ᵥ v) (Fin.cast (rank_Wc i).symm m)) τ j) ∧
    (∀ (v : Fin (Wc D i).rank → D.host.E) (j : Fin Wt'.g) (j' : Fin Wt.g), (j : ℕ) = j' →
      perVec Wt' (fun m => v (Fin.cast (rank_Wc i).symm m)) j =
        perVec Wt (fun m => (M *ᵥ v) (Fin.cast (rank_Wc i).symm m)) j') ∧
    ∀ (j₁ j₂ : Fin Wt'.g) (j₁' j₂' : Fin Wt.g), (j₁ : ℕ) = j₁' → (j₂ : ℕ) = j₂' → Y'.Hm j₁ j₂ = Y.Hm j₁' j₂' := by
  obtain ⟨hcore, hherm, hG, hξ⟩ := shift_core hMod hTie i σ hσ hV hS h ha hfr hfr' hM
  have hfr0 := perFr_shift hMod hTie i σ hσ hV hS h ha hfr hfr' hM
  exact ⟨hfr0, fun v j j' hj => perVec_of_perFr Wt Wt' he _ _ (hfr0 v) j j' hj,
    hm_eq_of_shift Wt Y Wt' Y' _ (fun u j j' hj => perVec_of_perFr Wt Wt' he _ _ (hcore u) j j' hj) hherm hG hξ⟩

end Witness

end GlobalTheory.HeckeFrameShift
