import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasChainW
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CkUniqueCharacterizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CkAdditiveCompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CkRootMultiplicationScalingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CkChainPeriodicRelationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapDegreeFinitePullbackStatement

open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.BundleChernComparison.ChainOne

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
Proceed by induction on `D using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a D`. Establish `h : a ⊗ₜ[ℤ] D = a • NModel.toQ D` using `by simp [NModel.toQ, TensorProduct.smul_tmul']`. Rewrite using `[h, map_smul, map_smul, map_smul, map_smul, map_smul, map_smul, NModel.cDQ_toQ, NModel.vResQ_toQ, GlobalTheory.Vert.Model.vPullQ_toQ, GlobalTheory.Vert.Model.cDQ_toQ, picSymPull_c1Pic, picSymPull_c1Pic, GlobalTheory.Vert.Model.vCls_vPull, NModel.vCls_vRes]`.

Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.
-/
private theorem pull_cDQ {Zn : NModel O} (C : Zn.Comp) {B : GlobalTheory.Vert.Model O} (f : GlobalTheory.Vert.Model.Hom B (Zn.comp C))
    (D : Zn.VDivQ) : picSymPull f.f (picSymPull (Zn.compι C) (Zn.cDQ D)) =
      B.cDQ (GlobalTheory.Vert.Model.vPullQ f.comp_str (NModel.vResQ C D)) := by
  induction D using TensorProduct.induction_on with
  | zero => simp
  | tmul a D =>
    have h : a ⊗ₜ[ℤ] D = a • NModel.toQ D := by simp [NModel.toQ, TensorProduct.smul_tmul']
    rw [h, map_smul, map_smul, map_smul, map_smul, map_smul, map_smul, NModel.cDQ_toQ, NModel.vResQ_toQ,
      GlobalTheory.Vert.Model.vPullQ_toQ, GlobalTheory.Vert.Model.cDQ_toQ, picSymPull_c1Pic, picSymPull_c1Pic,
      GlobalTheory.Vert.Model.vCls_vPull, NModel.vCls_vRes]
  | add a b ha hb => simp only [map_add, ha, hb]

variable (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p]

/- English proof (translation)
Rewrite using `[NModel.vResQ_toQ, NModel.divP, NModel.vRes_div, GlobalTheory.Vert.Model.vPullQ_toQ, GlobalTheory.Vert.Model.vPull_div]`. Both sides reduce to the same expression.
-/
private theorem pull_divP {Zn : NModel O} (C : Zn.Comp) {B : GlobalTheory.Vert.Model O} (f : GlobalTheory.Vert.Model.Hom B (Zn.comp C)) :
    GlobalTheory.Vert.Model.vPullQ f.comp_str (NModel.vResQ C (NModel.toQ (Zn.divP p))) = GlobalTheory.Vert.Model.toQ (B.divP p) := by
  rw [NModel.vResQ_toQ, NModel.divP, NModel.vRes_div, GlobalTheory.Vert.Model.vPullQ_toQ, GlobalTheory.Vert.Model.vPull_div]
  rfl

/- English proof (translation)
Take `⟨hpos, h⟩` from `GlobalTheory.T.cap_degree_finite_pullback O p (Zn.comp C) (GlobalTheory.IsNormalScheme.opens (X := Zn.X) C.opens) B f hf`. Rewrite using `[h D Q, ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]`.
-/
private theorem capDeg_eq_inv {Zn : NModel O} (C : Zn.Comp) {B : GlobalTheory.Vert.Model O} (f : GlobalTheory.Vert.Model.Hom B (Zn.comp C))
    (hf : f.relDim = 0) (D : (Zn.comp C).VDivQ) (Q : PicSym (Zn.comp C).X) :
    (Zn.comp C).capDeg_vp p D Q = (f.fibreDeg 1)⁻¹ * B.capDeg_vp p (GlobalTheory.Vert.Model.vPullQ f.comp_str D) (picSymPull f.f Q) := by
  obtain ⟨hpos, h⟩ := GlobalTheory.T.cap_degree_finite_pullback O p (Zn.comp C) (GlobalTheory.IsNormalScheme.opens (X := Zn.X) C.opens) B f hf
  rw [h D Q, ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]

end GlobalTheory.BundleChernComparison.ChainOne

namespace GlobalTheory.BundleChernComparison.ChainOne

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p]

/- English proof (translation)
Rewrite using `[(GlobalTheory.T.ck_unique_characterization O p B hB E E' φ r k hE hE').2.2 P, Formalism.BasicNotions.DV.ck, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[capDeg_eq_inv p C f hf, (hP i).2]`. Use `congrArg (fun x => (f.fibreDeg 1)⁻¹ * B.capDeg_vp p ((P.toFPair p).Dv i) x) ?_` and prove the remaining obligations. Establish `hx' : picSymPull f.f (picSymPull (Zn.compι C) ((Zn.toITh p d).c1 (F.x' i))) = (B.toITh p).c1 ((P.toFPair p).x' i)`.

Rewrite using `[F.hx i, (P.toFPair p).hx i, map_sub, map_sub, (hP i).1]`. Use `congr 1`. Conclude with `(pull_cDQ C f _).trans (congrArg B.cDQ (hP i).2)`. Simplify using `only [Gk, map_mul, map_sum, map_pow, (hP i).1, hx']`.
-/
private theorem comp_ck {Zn : NModel O} {d r : ℕ} (F : FPair (Zn.toITh p d) r) (C : Zn.Comp)
    {B : GlobalTheory.Vert.Model O} (f : GlobalTheory.Vert.Model.Hom B (Zn.comp C)) (hf : f.relDim = 0) (hB : GlobalTheory.IsNormalScheme B.X)
    {E E' : B.X.Modules} (φ : B.GenIso E E') (hE : GlobalTheory.VB.IsVB E r) (hE' : GlobalTheory.VB.IsVB E' r)
    (P : GlobalTheory.Vert.Model.FlagPair φ r)
    (hP : ∀ i, picSymPull f.f (picSymPull (Zn.compι C) ((Zn.toITh p d).c1 (F.x i))) = (B.toITh p).c1 ((P.toFPair p).x i) ∧
      GlobalTheory.Vert.Model.vPullQ f.comp_str (NModel.vResQ C (F.Dv i)) = (P.toFPair p).Dv i)
    (k : ℕ) (Q : PicSym Zn.X) :
    ∑ i, (Zn.comp C).capDeg_vp p (NModel.vResQ C (F.Dv i))
        (picSymPull (Zn.compι C) (Gk _ k ((Zn.toITh p d).c1 (F.x i)) ((Zn.toITh p d).c1 (F.x' i)) * Q)) =
      (f.fibreDeg 1)⁻¹ * ckP p φ r k (picSymPull f.f (picSymPull (Zn.compι C) Q)) := by
  rw [(GlobalTheory.T.ck_unique_characterization O p B hB E E' φ r k hE hE').2.2 P, Formalism.BasicNotions.DV.ck, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [capDeg_eq_inv p C f hf, (hP i).2]
  refine congrArg (fun x => (f.fibreDeg 1)⁻¹ * B.capDeg_vp p ((P.toFPair p).Dv i) x) ?_
  have hx' : picSymPull f.f (picSymPull (Zn.compι C) ((Zn.toITh p d).c1 (F.x' i))) =
      (B.toITh p).c1 ((P.toFPair p).x' i) := by
    rw [F.hx i, (P.toFPair p).hx i, map_sub, map_sub, (hP i).1]
    congr 1
    exact (pull_cDQ C f _).trans (congrArg B.cDQ (hP i).2)
  simp only [Gk, map_mul, map_sum, map_pow, (hP i).1, hx']

/- English proof (translation)
Set `Pr : Pres B` to `⟨r, E, E, hE, hE, smulHom E (B.const (p : O)), GlobalTheory.Vert.Model.isIso_genRes_map_smulHom E (GlobalTheory.Vert.natCast_ne_zero O p)⟩`. Establish `hroot : IsRootOfP p (B.const (p : O)) 1` using `⟨1, by simp [map_natCast]⟩`. Establish `h` using `(GlobalTheory.T.ck_root_multiplication_scaling O p B hB Pr (B.const (p : O)) 1 (Iso.refl _) hroot (Category.id_comp _).symm k).2 P.fl (picSymPull f.f (picSymPull (Zn.compι C) Q))`. Rewrite using `[h, capDeg_eq_inv p C f hf, pull_divP p C f]`. Simplify using `only [map_mul, map_sum, map_pow, hP]`.

Rewrite using `[mul_left_comm]`. Both sides reduce to the same expression.
-/
private theorem comp_chDiv {Zn : NModel O} {d r : ℕ} (F : FPair (Zn.toITh p d) r) (C : Zn.Comp)
    {B : GlobalTheory.Vert.Model O} (f : GlobalTheory.Vert.Model.Hom B (Zn.comp C)) (hf : f.relDim = 0) (hB : GlobalTheory.IsNormalScheme B.X)
    {E E' : B.X.Modules} (φ : B.GenIso E E') (hE : GlobalTheory.VB.IsVB E r)
    (P : GlobalTheory.Vert.Model.FlagPair φ r)
    (hP : ∀ i, picSymPull f.f (picSymPull (Zn.compι C) ((Zn.toITh p d).c1 (F.x i))) = (B.toITh p).c1 ((P.toFPair p).x i))
    (k : ℕ) (Q : PicSym Zn.X) :
    (k : ℚ) * (Zn.comp C).capDeg_vp p (NModel.vResQ C (NModel.toQ (Zn.divP p)))
        (picSymPull (Zn.compι C) ((∑ l, (Zn.toITh p d).c1 (F.x l) ^ (k - 1)) * Q)) =
      (f.fibreDeg 1)⁻¹ * ckP p (GlobalTheory.Vert.Model.GenIso.smul E (p : O) (GlobalTheory.Vert.natCast_ne_zero O p)) r k
        (picSymPull f.f (picSymPull (Zn.compι C) Q)) := by
  let Pr : Pres B := ⟨r, E, E, hE, hE, smulHom E (B.const (p : O)),
    GlobalTheory.Vert.Model.isIso_genRes_map_smulHom E (GlobalTheory.Vert.natCast_ne_zero O p)⟩
  have hroot : IsRootOfP p (B.const (p : O)) 1 := ⟨1, by simp [map_natCast]⟩
  have h := (GlobalTheory.T.ck_root_multiplication_scaling O p B hB Pr (B.const (p : O)) 1 (Iso.refl _) hroot (Category.id_comp _).symm k).2 P.fl
    (picSymPull f.f (picSymPull (Zn.compι C) Q))
  rw [h, capDeg_eq_inv p C f hf, pull_divP p C f]
  simp only [map_mul, map_sum, map_pow, hP]
  rw [mul_left_comm]
  rfl

end GlobalTheory.BundleChernComparison.ChainOne

namespace GlobalTheory.BundleChernComparison.ChainOne

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p]

/- English proof (translation)
Rewrite using `[Formalism.BasicNotions.DV.ck]`. Simplify using `only [hs]`. Conclude with `Finset.sum_comm.trans (Finset.sum_congr rfl hg)`.
-/
private theorem ck_eq_sum {Zn : NModel O} {d r : ℕ} (F : FPair (Zn.toITh p d) r) (s : Finset Zn.Comp)
    (hs : ∀ Dv Q', Zn.capDeg_vp p d Dv Q' = ∑ C ∈ s, (Zn.comp C).capDeg_vp p (NModel.vResQ C Dv) (picSymPull (Zn.compι C) Q'))
    (g : Zn.Comp → ℚ) (k : ℕ) (Q : PicSym Zn.X)
    (hg : ∀ C ∈ s, ∑ i, (Zn.comp C).capDeg_vp p (NModel.vResQ C (F.Dv i))
        (picSymPull (Zn.compι C) (Gk _ k ((Zn.toITh p d).c1 (F.x i)) ((Zn.toITh p d).c1 (F.x' i)) * Q)) = g C) :
    Formalism.BasicNotions.DV.ck F k Q = ∑ C ∈ s, g C := by
  rw [Formalism.BasicNotions.DV.ck]
  simp only [hs]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl hg)

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(k : ℚ) * Zn.capDeg_vp p d (NModel.toQ (Zn.divP p)) Q = _`. Rewrite using `[hs, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl hg`.
-/
private theorem cap_eq_sum {Zn : NModel O} {d : ℕ} (s : Finset Zn.Comp)
    (hs : ∀ Dv Q', Zn.capDeg_vp p d Dv Q' = ∑ C ∈ s, (Zn.comp C).capDeg_vp p (NModel.vResQ C Dv) (picSymPull (Zn.compι C) Q'))
    (g : Zn.Comp → ℚ) (k : ℕ) (Q : PicSym Zn.X)
    (hg : ∀ C ∈ s, (k : ℚ) * (Zn.comp C).capDeg_vp p (NModel.vResQ C (NModel.toQ (Zn.divP p)))
        (picSymPull (Zn.compι C) Q) = g C) :
    (k : ℚ) * (Zn.toITh p d).capDeg (Zn.toITh p d).divP Q = ∑ C ∈ s, g C := by
  change (k : ℚ) * Zn.capDeg_vp p d (NModel.toQ (Zn.divP p)) Q = _
  rw [hs, Finset.mul_sum]
  exact Finset.sum_congr rfl hg

end GlobalTheory.BundleChernComparison.ChainOne

namespace GlobalTheory.BundleChernComparison.ChainOne

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p]

/- English proof (translation)
Use `choose B f Ch hB using hch`. Take `⟨s, hs⟩ : ∃ s : Finset Zn.Comp, ∀ Dv Q', Zn.capDeg_vp p d Dv Q' = ∑ C ∈ s, (Zn.comp C).capDeg_vp p (NModel.vResQ C Dv) (picSymPull (Zn.compι C) Q')` from `⟨_, NModel.capDeg_vp_eq_sum p _⟩`. Set `aQ : ∀ c, PicSym (B c).X` to `fun c => picSymPull (f c).f (picSymPull (Zn.compι c) Q)`. Set `w : Zn.Comp → ℚ` to `fun c => ((f c).fibreDeg 1)⁻¹`. Set `La : Zn.Comp → ι → ℚ` to `fun c τ' => ckP p (GlobalTheory.Vert.Model.GenIso.smul ((Ch c).lw τ').E' (p : O) (GlobalTheory.Vert.natCast_ne_zero O p)) ((Ch c).lw τ').r k (aQ c)`.

Establish `hLie : Formalism.BasicNotions.DV.ck (lie τ) k Q = ∑ c ∈ s, w c * -(((Ch c).lw τ).ck p k (aQ c))`. Use `ck_eq_sum p (lie τ) s hs _ k Q fun c _ => ?_` and prove the remaining obligations. Take `⟨hBn, hfr, hτ⟩` from `hB c`. Take `⟨hr, -, ⟨P, hP⟩, -⟩` from `hτ τ`. Use `haveI := ((Ch c).lw τ).iso`.

Use `(comp_ck p (lie τ) c (f c) hfr hBn (GlobalTheory.Vert.Model.GenIso.ofHom ((Ch c).lw τ).ψ).symm (hr ▸ ((Ch c).lw τ).vb') (hr ▸ ((Ch c).lw τ).vb) P (fun i => hP i) k Q).trans ?_` and prove the remaining obligations. Establish `e` using `(GlobalTheory.T.ck_additive_composition _ p (B c) hBn _ _ _ (GlobalTheory.Vert.Model.GenIso.ofHom ((Ch c).lw τ).ψ) (Iso.refl _) ((Ch c).lw τ).r k ((Ch c).lw τ).vb ((Ch c).lw τ).vb' ((Ch c).lw τ).vb').2`. Rewrite using `[← hr, e]`. Both sides reduce to the same expression. Establish `hOm : Formalism.BasicNotions.DV.ck (om τ) k Q = ∑ c ∈ s, w c * ((Ch c).oo τ).ck p k (aQ c)`.

Use `ck_eq_sum p (om τ) s hs _ k Q fun c _ => ?_` and prove the remaining obligations. Take `⟨hBn, hfr, hτ⟩` from `hB c`. Take `⟨-, hro, -, ⟨P, hP⟩⟩` from `hτ τ`. Use `haveI := ((Ch c).oo τ).iso`. Use `(comp_ck p (om τ) c (f c) hfr hBn (GlobalTheory.Vert.Model.GenIso.ofHom ((Ch c).oo τ).ψ) (hro ▸ ((Ch c).oo τ).vb) (hro ▸ ((Ch c).oo τ).vb') P (fun i => hP i) k Q).trans ?_` and prove the remaining obligations.

Rewrite using `[← hro]`. Both sides reduce to the same expression. Establish `hK : ∀ τ', (k : ℚ) * (Zn.toITh p d).capDeg (Zn.toITh p d).divP ((∑ l, (Zn.toITh p d).c1 ((lie τ').x l) ^ (k - 1)) * Q) = ∑ c ∈ s, w c * La c τ'`. Introduce `τ'`. Use `cap_eq_sum p s hs _ k _ fun c _ => ?_` and prove the remaining obligations.

Take `⟨hBn, hfr, hτ⟩` from `hB c`. Take `⟨hr, -, ⟨P, hP⟩, -⟩` from `hτ τ'`. Use `haveI := ((Ch c).lw τ').iso`. Use `(comp_chDiv p (lie τ') c (f c) hfr hBn (GlobalTheory.Vert.Model.GenIso.ofHom ((Ch c).lw τ').ψ).symm (hr ▸ ((Ch c).lw τ').vb') P (fun i => (hP i).1) k Q).trans ?_` and prove the remaining obligations. Rewrite using `[← hr]`.

Establish `hc : ∀ c, (1 - ((p : ℚ) ^ (o * k))⁻¹) * (((Ch c).oo τ).ck p k (aQ c) - ((Ch c).lw τ).ck p k (aQ c) + ((p : ℚ) - 1)⁻¹ * La c τ) = ∑ n ∈ Finset.range o, ((p : ℚ) ^ ((n + 1) * k))⁻¹ * La c (φ^[n + 1] τ)`. Introduce `c`. Establish `hBn` using `(hB c).1`. Establish `h` using `GlobalTheory.T.ck_chain_periodic_relation _ p (B c) hBn ι φ o (Ch c) hper k (fun τ' => ckP p (GlobalTheory.Vert.Model.GenIso.smul ((Ch c).lw τ').E' (p : O) (GlobalTheory.Vert.natCast_ne_zero O p)) ((Ch c).lw τ').r k) (fun _ => rfl) τ`. Establish `h2` using `LinearMap.congr_fun h (aQ c)`.

Simplify using `only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.sum_apply, smul_eq_mul] at h2`. Conclude with `h2`. Simplify using `only [hLie, hOm, hK]`. Rewrite using `[Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]`. Simplify using `only [Finset.mul_sum]`.

Use `Eq.trans ?_ Finset.sum_comm.symm` and prove the remaining obligations. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[show ∀ x y z a b : ℚ, a * (x * -y + x * z + x * b / ((p : ℚ) - 1)) = x * (a * (z - y + ((p : ℚ) - 1)⁻¹ * b)) from fun x y z a b => by ring, hc c, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem period_rat {Zn : NModel O} {d : ℕ} {ι : Type} (φ : ι → ι) (o : ℕ) (hper : ∀ τ, φ^[o] τ = τ) {rk rk' : ι → ℕ}
    (lie : ∀ τ, FPair (Zn.toITh p d) (rk τ)) (om : ∀ τ, FPair (Zn.toITh p d) (rk' τ))
    (hch : ∀ c : Zn.Comp, ∃ (B : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B (Zn.comp c))
      (Ch : Chain p B φ o), GlobalTheory.IsNormalScheme B.X ∧ f.relDim = 0 ∧ ∀ τ,
      (Ch.lw τ).r = rk τ ∧ (Ch.oo τ).r = rk' τ ∧
      Reads p (lie τ) (fun x => picSymPull f.f (picSymPull (Zn.compι c) x))
        (fun d => GlobalTheory.Vert.Model.vPullQ f.comp_str (NModel.vResQ c d))
        (haveI := (Ch.lw τ).iso; (GlobalTheory.Vert.Model.GenIso.ofHom (Ch.lw τ).ψ).symm) ∧
      Reads p (om τ) (fun x => picSymPull f.f (picSymPull (Zn.compι c) x))
        (fun d => GlobalTheory.Vert.Model.vPullQ f.comp_str (NModel.vResQ c d))
        (haveI := (Ch.oo τ).iso; GlobalTheory.Vert.Model.GenIso.ofHom (Ch.oo τ).ψ))
    (τ : ι) (k : ℕ) (Q : (Zn.toITh p d).Ch) :
    (1 - ((p : ℚ) ^ (o * k))⁻¹) * (Formalism.BasicNotions.DV.ck (lie τ) k Q + Formalism.BasicNotions.DV.ck (om τ) k Q +
      (k : ℚ) * (Zn.toITh p d).capDeg (Zn.toITh p d).divP
        ((∑ l, (Zn.toITh p d).c1 ((lie τ).x l) ^ (k - 1)) * Q) / ((p : ℚ) - 1)) =
      ∑ n ∈ Finset.range o, ((p : ℚ) ^ ((n + 1) * k))⁻¹ * ((k : ℚ) * (Zn.toITh p d).capDeg (Zn.toITh p d).divP
        ((∑ l, (Zn.toITh p d).c1 ((lie (φ^[n + 1] τ)).x l) ^ (k - 1)) * Q)) := by
  choose B f Ch hB using hch
  obtain ⟨s, hs⟩ : ∃ s : Finset Zn.Comp, ∀ Dv Q', Zn.capDeg_vp p d Dv Q' =
      ∑ C ∈ s, (Zn.comp C).capDeg_vp p (NModel.vResQ C Dv) (picSymPull (Zn.compι C) Q') :=
    ⟨_, NModel.capDeg_vp_eq_sum p _⟩
  let aQ : ∀ c, PicSym (B c).X := fun c => picSymPull (f c).f (picSymPull (Zn.compι c) Q)
  let w : Zn.Comp → ℚ := fun c => ((f c).fibreDeg 1)⁻¹
  let La : Zn.Comp → ι → ℚ := fun c τ' =>
    ckP p (GlobalTheory.Vert.Model.GenIso.smul ((Ch c).lw τ').E' (p : O) (GlobalTheory.Vert.natCast_ne_zero O p)) ((Ch c).lw τ').r k (aQ c)
  have hLie : Formalism.BasicNotions.DV.ck (lie τ) k Q = ∑ c ∈ s, w c * -(((Ch c).lw τ).ck p k (aQ c)) := by
    refine ck_eq_sum p (lie τ) s hs _ k Q fun c _ => ?_
    obtain ⟨hBn, hfr, hτ⟩ := hB c
    obtain ⟨hr, -, ⟨P, hP⟩, -⟩ := hτ τ
    haveI := ((Ch c).lw τ).iso
    refine (comp_ck p (lie τ) c (f c) hfr hBn (GlobalTheory.Vert.Model.GenIso.ofHom ((Ch c).lw τ).ψ).symm
      (hr ▸ ((Ch c).lw τ).vb') (hr ▸ ((Ch c).lw τ).vb) P (fun i => hP i) k Q).trans ?_
    have e := (GlobalTheory.T.ck_additive_composition _ p (B c) hBn _ _ _ (GlobalTheory.Vert.Model.GenIso.ofHom ((Ch c).lw τ).ψ) (Iso.refl _)
      ((Ch c).lw τ).r k ((Ch c).lw τ).vb ((Ch c).lw τ).vb' ((Ch c).lw τ).vb').2
    rw [← hr, e]
    rfl
  have hOm : Formalism.BasicNotions.DV.ck (om τ) k Q = ∑ c ∈ s, w c * ((Ch c).oo τ).ck p k (aQ c) := by
    refine ck_eq_sum p (om τ) s hs _ k Q fun c _ => ?_
    obtain ⟨hBn, hfr, hτ⟩ := hB c
    obtain ⟨-, hro, -, ⟨P, hP⟩⟩ := hτ τ
    haveI := ((Ch c).oo τ).iso
    refine (comp_ck p (om τ) c (f c) hfr hBn (GlobalTheory.Vert.Model.GenIso.ofHom ((Ch c).oo τ).ψ)
      (hro ▸ ((Ch c).oo τ).vb) (hro ▸ ((Ch c).oo τ).vb') P (fun i => hP i) k Q).trans ?_
    rw [← hro]
    rfl
  have hK : ∀ τ', (k : ℚ) * (Zn.toITh p d).capDeg (Zn.toITh p d).divP
      ((∑ l, (Zn.toITh p d).c1 ((lie τ').x l) ^ (k - 1)) * Q) = ∑ c ∈ s, w c * La c τ' := by
    intro τ'
    refine cap_eq_sum p s hs _ k _ fun c _ => ?_
    obtain ⟨hBn, hfr, hτ⟩ := hB c
    obtain ⟨hr, -, ⟨P, hP⟩, -⟩ := hτ τ'
    haveI := ((Ch c).lw τ').iso
    refine (comp_chDiv p (lie τ') c (f c) hfr hBn (GlobalTheory.Vert.Model.GenIso.ofHom ((Ch c).lw τ').ψ).symm
      (hr ▸ ((Ch c).lw τ').vb') P (fun i => (hP i).1) k Q).trans ?_
    rw [← hr]
  have hc : ∀ c, (1 - ((p : ℚ) ^ (o * k))⁻¹) * (((Ch c).oo τ).ck p k (aQ c) - ((Ch c).lw τ).ck p k (aQ c) +
      ((p : ℚ) - 1)⁻¹ * La c τ) = ∑ n ∈ Finset.range o, ((p : ℚ) ^ ((n + 1) * k))⁻¹ * La c (φ^[n + 1] τ) := by
    intro c
    have hBn := (hB c).1
    have h := GlobalTheory.T.ck_chain_periodic_relation _ p (B c) hBn ι φ o (Ch c) hper k
      (fun τ' => ckP p (GlobalTheory.Vert.Model.GenIso.smul ((Ch c).lw τ').E' (p : O) (GlobalTheory.Vert.natCast_ne_zero O p))
        ((Ch c).lw τ').r k) (fun _ => rfl) τ
    have h2 := LinearMap.congr_fun h (aQ c)
    simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.sum_apply,
      smul_eq_mul] at h2
    exact h2
  simp only [hLie, hOm, hK]
  rw [Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  simp only [Finset.mul_sum]
  refine Eq.trans ?_ Finset.sum_comm.symm
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [show ∀ x y z a b : ℚ, a * (x * -y + x * z + x * b / ((p : ℚ) - 1)) = x * (a * (z - y + ((p : ℚ) - 1)⁻¹ * b))
    from fun x y z a b => by ring, hc c, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

end GlobalTheory.BundleChernComparison.ChainOne

namespace GlobalTheory.BundleChernComparison.ChainOne

/- English proof (translation)
Introduce `k hk m _ Q _`. Establish `hq` using `congrArg (fun x : ℚ => (x : ℝ)) (h k (evQ _ Q))`. Establish `hf : (Nat.factorial k : ℝ) = k * (Nat.factorial (k - 1) : ℝ)`. Conclude with `(Nat.mul_factorial_pred (by omega)).symm` after adjusting the coercions. Establish `hk0 : (k : ℝ) ≠ 0` using `by exact_mod_cast (by omega : k ≠ 0)`.

Establish `hf0 : (Nat.factorial (k - 1) : ℝ) ≠ 0` using `by positivity`. Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast (Fact.out : p.Prime).one_lt`. Establish `h1 : (p : ℝ) - 1 ≠ 0` using `by linarith`. Establish `h2 : (1 : ℝ) < (p : ℝ) ^ k` using `one_lt_pow₀ hp1 (by omega)`. Establish `h3 : (p : ℝ) ^ k - 1 ≠ 0` using `by linarith`.

Establish `h4 : (p : ℝ) ^ k ≠ 0` using `by linarith`. Simplify using `only [Finset.range_one, Finset.sum_singleton, zero_add, one_mul, Rat.cast_mul, Rat.cast_sub, Rat.cast_add, Rat.cast_div, Rat.cast_inv, Rat.cast_pow, Rat.cast_natCast, Rat.cast_one] at hq`. Unfold `chk chDiv`. Rewrite using `[hf]`. Generalize the expression as in `((Formalism.BasicNotions.DV.ck M.lieW k (evQ _ Q) : ℚ) : ℝ) = a at hq ⊢`.

Generalize the expression as in `((Formalism.BasicNotions.DV.ck M.omW k (evQ _ Q) : ℚ) : ℝ) = b at hq ⊢`. Generalize the expression as in `((M.Z.capDeg M.Z.divP ((∑ l, M.Z.c1 (M.lieW.x l) ^ (k - 1)) * evQ _ Q) : ℚ) : ℝ) = c at hq ⊢`. Generalize the expression as in `(p : ℝ) ^ k = P at hq h2 h3 h4 ⊢`. Establish `e : a + b = k * c * ((P - 1)⁻¹ - ((p : ℝ) - 1)⁻¹)`. Establish `: (P - 1) * (a + b + k * c / ((p : ℝ) - 1)) = k * c`.

Use `congrArg (fun x => P * x) hq` as an intermediate fact. Simplify using `only [← mul_assoc, mul_sub, mul_inv_cancel₀ h4, mul_one, one_mul] at this`. Conclude with `this`. Clear denominators, using `at this ⊢` for the nonvanishing conditions. Take the linear combination `this`.

Rewrite using `[← add_div, e]`. Clear the denominators using the available nonvanishing facts.
-/
private theorem localW_of_rat {D : D7} {p : ℕ} [Fact p.Prime] {N : ℕ} {rk : Emb D p → ℕ} (M : DV.Mdl D p N rk)
    (h : ∀ (k : ℕ) (Q : M.Z.Ch),
      (1 - ((p : ℚ) ^ (1 * k))⁻¹) * (Formalism.BasicNotions.DV.ck M.lieW k Q + Formalism.BasicNotions.DV.ck M.omW k Q +
        (k : ℚ) * M.Z.capDeg M.Z.divP ((∑ l, M.Z.c1 (M.lieW.x l) ^ (k - 1)) * Q) / ((p : ℚ) - 1)) =
      ∑ n ∈ Finset.range 1, ((p : ℚ) ^ ((n + 1) * k))⁻¹ * ((k : ℚ) * M.Z.capDeg M.Z.divP
        ((∑ l, M.Z.c1 (M.lieW.x l) ^ (k - 1)) * Q))) : LocalW M := by
  intro k hk m _ Q _
  have hq := congrArg (fun x : ℚ => (x : ℝ)) (h k (evQ _ Q))
  have hf : (Nat.factorial k : ℝ) = k * (Nat.factorial (k - 1) : ℝ) := by
    exact_mod_cast (Nat.mul_factorial_pred (by omega)).symm
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hf0 : (Nat.factorial (k - 1) : ℝ) ≠ 0 := by positivity
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (1 : ℝ) < (p : ℝ) ^ k := one_lt_pow₀ hp1 (by omega)
  have h3 : (p : ℝ) ^ k - 1 ≠ 0 := by linarith
  have h4 : (p : ℝ) ^ k ≠ 0 := by linarith
  simp only [Finset.range_one, Finset.sum_singleton, zero_add, one_mul, Rat.cast_mul, Rat.cast_sub, Rat.cast_add,
    Rat.cast_div, Rat.cast_inv, Rat.cast_pow, Rat.cast_natCast, Rat.cast_one] at hq
  unfold chk chDiv
  rw [hf]
  generalize ((Formalism.BasicNotions.DV.ck M.lieW k (evQ _ Q) : ℚ) : ℝ) = a at hq ⊢
  generalize ((Formalism.BasicNotions.DV.ck M.omW k (evQ _ Q) : ℚ) : ℝ) = b at hq ⊢
  generalize ((M.Z.capDeg M.Z.divP ((∑ l, M.Z.c1 (M.lieW.x l) ^ (k - 1)) * evQ _ Q) : ℚ) : ℝ) = c at hq ⊢
  generalize (p : ℝ) ^ k = P at hq h2 h3 h4 ⊢
  have e : a + b = k * c * ((P - 1)⁻¹ - ((p : ℝ) - 1)⁻¹) := by
    have : (P - 1) * (a + b + k * c / ((p : ℝ) - 1)) = k * c := by
      have := congrArg (fun x => P * x) hq
      simp only [← mul_assoc, mul_sub, mul_inv_cancel₀ h4, mul_one, one_mul] at this
      exact this
    field_simp at this ⊢
    linear_combination this
  rw [← add_div, e]
  field_simp

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] in

/- English proof (translation)
The claim follows from `period_rat p (id : Unit → Unit) 1 (fun _ => rfl) (rk := fun _ => r) (rk' := fun _ => r) (fun _ => F) (fun _ => G) (fun c => by obtain ⟨B, f, Ch, h1, h2, h3⟩ := hch c exact ⟨B, f, Ch, h1, h2, fun _ => h3⟩) () k Q`.
-/
private theorem period_one (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] {Zn : NModel O} {d r : ℕ}
    (F G : FPair (Zn.toITh p d) r)
    (hch : ∀ c : Zn.Comp, ∃ (B : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B (Zn.comp c))
      (Ch : Chain p B (id : Unit → Unit) 1), GlobalTheory.IsNormalScheme B.X ∧ f.relDim = 0 ∧
      (Ch.lw ()).r = r ∧ (Ch.oo ()).r = r ∧
      Reads p F (fun x => picSymPull f.f (picSymPull (Zn.compι c) x))
        (fun d => GlobalTheory.Vert.Model.vPullQ f.comp_str (NModel.vResQ c d))
        (haveI := (Ch.lw ()).iso; (GlobalTheory.Vert.Model.GenIso.ofHom (Ch.lw ()).ψ).symm) ∧
      Reads p G (fun x => picSymPull f.f (picSymPull (Zn.compι c) x))
        (fun d => GlobalTheory.Vert.Model.vPullQ f.comp_str (NModel.vResQ c d))
        (haveI := (Ch.oo ()).iso; GlobalTheory.Vert.Model.GenIso.ofHom (Ch.oo ()).ψ))
    (k : ℕ) (Q : (Zn.toITh p d).Ch) :
    (1 - ((p : ℚ) ^ (1 * k))⁻¹) * (Formalism.BasicNotions.DV.ck F k Q + Formalism.BasicNotions.DV.ck G k Q +
      (k : ℚ) * (Zn.toITh p d).capDeg (Zn.toITh p d).divP
        ((∑ l, (Zn.toITh p d).c1 (F.x l) ^ (k - 1)) * Q) / ((p : ℚ) - 1)) =
      ∑ n ∈ Finset.range 1, ((p : ℚ) ^ ((n + 1) * k))⁻¹ * ((k : ℚ) * (Zn.toITh p d).capDeg (Zn.toITh p d).divP
        ((∑ l, (Zn.toITh p d).c1 (F.x l) ^ (k - 1)) * Q)) :=
  period_rat p (id : Unit → Unit) 1 (fun _ => rfl) (rk := fun _ => r) (rk' := fun _ => r) (fun _ => F) (fun _ => G)
    (fun c => by
      obtain ⟨B, f, Ch, h1, h2, h3⟩ := hch c
      exact ⟨B, f, Ch, h1, h2, fun _ => h3⟩) () k Q

/- English proof (translation)
Introduce `D A N j S κ p _ hp W hW z jc hch`. Use `localW_of_rat (mdlOf z jc) ?_` and prove the remaining obligations. Conclude with `haveI := isDiscreteValuationRing_V z.Z.i.c hp hW haveI := charP_residueField_of_mem_nonunits z.Z.i.c hp hW period_one p (Zn := nmodel z.Z) (d := dimFl D.what₂.Tau N) (mdlOf z jc).lieW (mdlOf z jc).omW hch`.
-/
private theorem localW_of_hasChainW : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (p : ℕ) [Fact p.Prime] (hp : p.Prime) (W : ValuationSubring ℂ) (hW : (p : ℂ) ∈ W.nonunits) (z : AdmAt S κ hp hW) (jc : KW p →+* ℂ), HasChainW z jc → LocalW (mdlOf z jc) := by
  intro D A N j S κ p _ hp W hW z jc hch
  refine localW_of_rat (mdlOf z jc) ?_
  exact
    haveI := isDiscreteValuationRing_V z.Z.i.c hp hW
    haveI := charP_residueField_of_mem_nonunits z.Z.i.c hp hW
    period_one p (Zn := nmodel z.Z) (d := dimFl D.what₂.Tau N) (mdlOf z jc).lieW (mdlOf z jc).omW hch

end GlobalTheory.BundleChernComparison.ChainOne

/- English proof (translation)
The claim follows from `GlobalTheory.BundleChernComparison.ChainOne.localW_of_hasChainW`.
-/
theorem _root_.GlobalTheory.T.local_of_has_chain_at_prime : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (p : ℕ) [Fact p.Prime] (hp : p.Prime) (W : ValuationSubring ℂ) (hW : (p : ℂ) ∈ W.nonunits) (z : AdmAt S κ hp hW) (jc : KW p →+* ℂ), HasChainW z jc → LocalW (mdlOf z jc) :=
  GlobalTheory.BundleChernComparison.ChainOne.localW_of_hasChainW

end
