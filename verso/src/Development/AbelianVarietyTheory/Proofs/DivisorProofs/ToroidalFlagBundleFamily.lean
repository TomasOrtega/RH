import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMatrixUniqueUpToTriangularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFlagBundleRankDualStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls
open ReciprocityTheory.ChartRestriction.G.PullbackSections

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCls

attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Consider the cases of `dual`. Conclude with `⟨A, hA, rfl⟩`. Establish `h1 : IsUnit (Matrix.transpose (A.submatrix Fin.rev id)).det`. Rewrite using `[Matrix.det_transpose]`. Use `Matrix.det_permute (Fin.revPerm : Equiv.Perm (Fin r)) A` as an intermediate fact.

Rewrite using `[show A.submatrix Fin.rev id = A.submatrix (Fin.revPerm : Equiv.Perm (Fin r)) id from rfl, this]`. Conclude with `IsUnit.mul ((Units.isUnit (Equiv.Perm.sign Fin.revPerm)).map (Int.castRingHom K)) hA`. Use `⟨(Matrix.transpose (A.submatrix Fin.rev id))⁻¹, Matrix.isUnit_nonsing_inv_det _ h1, ?_⟩` and prove the remaining obligations. Rewrite using `[lieMat, cond_true, Matrix.nonsing_inv_nonsing_inv _ h1]`. Use extensionality with `i j`.

Simplify using the standard rewrite rules.
-/
theorem exists_lieMat_eq (dual : Bool) {r : ℕ} {K : Type} [CommRing K] {A : Matrix (Fin r) (Fin r) K}
    (hA : IsUnit A.det) : ∃ d : Matrix (Fin r) (Fin r) K, IsUnit d.det ∧ lieMat dual d = A := by
  cases dual
  · exact ⟨A, hA, rfl⟩
  · have h1 : IsUnit (Matrix.transpose (A.submatrix Fin.rev id)).det := by
      rw [Matrix.det_transpose]
      have := Matrix.det_permute (Fin.revPerm : Equiv.Perm (Fin r)) A
      rw [show A.submatrix Fin.rev id = A.submatrix (Fin.revPerm : Equiv.Perm (Fin r)) id from rfl, this]
      exact IsUnit.mul ((Units.isUnit (Equiv.Perm.sign Fin.revPerm)).map (Int.castRingHom K)) hA
    refine ⟨(Matrix.transpose (A.submatrix Fin.rev id))⁻¹, Matrix.isUnit_nonsing_inv_det _ h1, ?_⟩
    rw [lieMat, cond_true, Matrix.nonsing_inv_nonsing_inv _ h1]
    ext i j
    simp

section Lie

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}

open scoped CategoryTheory.MonObj in

/- English proof (translation)
Set `U : Fin m → TanM x Z.t.G` to `fun i => LieMet.tanOf (hu.1 i).1`. Establish `hU : ∀ i a, actR Z.t.act a (U i) = φ (embK c τ a) • U i` using `fun i a => LieMet.tan_ext ((hu.1 i).2 a)`. Set `W : Fin m → TanM x Z.t.G` to `fun i => ∑ b, d i b • U b`. Establish `hW : ∀ i a, actR Z.t.act a (W i) = φ (embK c τ a) • W i` using `fun i a => by`. Simplify using `only [W, map_sum, map_smul, hU, Finset.smul_sum]`.

Conclude with `Finset.sum_congr rfl fun b _ => smul_comm _ _ _`. Establish `hs : ∀ a : Fin m → K, ∑ i, a i • W i = ∑ b, Matrix.vecMul a d b • U b` using `fun a => by`. Simplify using `only [W, Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]`. Conclude with `Finset.sum_comm`. Use `⟨fun i => (tv (W i)).left, ⟨fun i => ⟨LieMet.isTan_tv _, fun a => congrArg (fun v => (tv v).left) (hW i a)⟩, fun w hw => ?_⟩, fun i => (LieMet.isComb_iff U (d i) (W i)).2 rfl⟩` and prove the remaining obligations.

Take `⟨a, ha, hu'⟩` from `(existsUnique_congr fun a => LieMet.isComb_iff U a (LieMet.tanOf hw.1)).1 (hu.2 w hw)`. Use `(existsUnique_congr fun a => LieMet.isComb_iff W a (LieMet.tanOf hw.1)).2 ⟨Matrix.vecMul a d⁻¹, ?_, fun b hb => ?_⟩` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[hs, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hd, Matrix.vecMul_one]`. Conclude with `ha`.

Rewrite using `[← hu' _ (hb.trans (hs b)), Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hd, Matrix.vecMul_one]`.
-/
theorem exists_eigBasis_comb {K : Type} [CommRing K] {φ : c.F →+* K} {x : Sp K ⟶ Z.X} {τ : E →+* ℂ} {m : ℕ}
    {u : Fin m → (Sp (DualNumber K) ⟶ Z.t.G.left)} (hu : IsEigBasis Z φ x τ u) {d : Matrix (Fin m) (Fin m) K}
    (hd : IsUnit d.det) : ∃ v, IsEigBasis Z φ x τ v ∧ ∀ i, IsCombAtG Z.t x u (d i) (v i) := by
  let U : Fin m → TanM x Z.t.G := fun i => LieMet.tanOf (hu.1 i).1
  have hU : ∀ i a, actR Z.t.act a (U i) = φ (embK c τ a) • U i := fun i a => LieMet.tan_ext ((hu.1 i).2 a)
  let W : Fin m → TanM x Z.t.G := fun i => ∑ b, d i b • U b
  have hW : ∀ i a, actR Z.t.act a (W i) = φ (embK c τ a) • W i := fun i a => by
    simp only [W, map_sum, map_smul, hU, Finset.smul_sum]
    exact Finset.sum_congr rfl fun b _ => smul_comm _ _ _
  have hs : ∀ a : Fin m → K, ∑ i, a i • W i = ∑ b, Matrix.vecMul a d b • U b := fun a => by
    simp only [W, Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]
    exact Finset.sum_comm
  refine ⟨fun i => (tv (W i)).left, ⟨fun i => ⟨LieMet.isTan_tv _, fun a => congrArg (fun v => (tv v).left) (hW i a)⟩,
    fun w hw => ?_⟩, fun i => (LieMet.isComb_iff U (d i) (W i)).2 rfl⟩
  obtain ⟨a, ha, hu'⟩ := (existsUnique_congr fun a => LieMet.isComb_iff U a (LieMet.tanOf hw.1)).1 (hu.2 w hw)
  refine (existsUnique_congr fun a => LieMet.isComb_iff W a (LieMet.tanOf hw.1)).2
    ⟨Matrix.vecMul a d⁻¹, ?_, fun b hb => ?_⟩
  · beta_reduce
    rw [hs, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hd, Matrix.vecMul_one]
    exact ha
  · rw [← hu' _ (hb.trans (hs b)), Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hd, Matrix.vecMul_one]

/- English proof (translation)
Establish `key : ∀ τ : E →+* ℂ, ∃ w : Fin (Dw.mult τ) → (Sp (DualNumber K) ⟶ Z.t.G.left), IsEigBasis Z φ x τ w ∧ ∀ a (h : emb a = τ) (i : Fin (rk a)), w (Fin.cast ((hr a).trans (congrArg Dw.mult h)) i) = v a i` using `fun τ => by`. Take `⟨a, rfl⟩` from `hb.2 τ`. Establish `gen : ∀ (n : ℕ) (h : rk a = n), ∃ w : Fin n → (Sp (DualNumber K) ⟶ Z.t.G.left), IsEigBasis Z φ x (emb a) w ∧ ∀ i, w (Fin.cast h i) = v a i`. Introduce and unpack `_ rfl`. Conclude with `⟨v a, hv a, fun _ => rfl⟩`.

Take `⟨w, h1, h2⟩` from `gen _ (hr a)`. Use `⟨w, h1, fun a' h i => ?_⟩` and prove the remaining obligations. Take `rfl` from `hb.1 h`. Conclude with `h2 i`. Use `choose w h1 h2 using key`.

Conclude with `⟨⟨w, fun τ i => ((h1 τ).1 i).1, fun τ i => ((h1 τ).1 i).2, fun τ z hz hz' => (h1 τ).2 z ⟨hz, hz'⟩⟩, fun a => funext fun i => h2 _ a rfl i⟩`.
-/
theorem exists_eigFrame_of_bases {K : Type} [CommRing K] {φ : c.F →+* K} {x : Sp K ⟶ Z.X} {ι : Type} {rk : ι → ℕ}
    {emb : ι → (E →+* ℂ)} (hr : ∀ a, rk a = Dw.mult (emb a)) (hb : Function.Bijective emb)
    {v : ∀ a, Fin (rk a) → (Sp (DualNumber K) ⟶ Z.t.G.left)} (hv : ∀ a, IsEigBasis Z φ x (emb a) (v a)) :
    ∃ g : EigFrame Z φ x, ∀ a, (fun i => g.v (emb a) (Fin.cast (hr a) i)) = v a := by
  have key : ∀ τ : E →+* ℂ, ∃ w : Fin (Dw.mult τ) → (Sp (DualNumber K) ⟶ Z.t.G.left), IsEigBasis Z φ x τ w ∧
      ∀ a (h : emb a = τ) (i : Fin (rk a)), w (Fin.cast ((hr a).trans (congrArg Dw.mult h)) i) = v a i := fun τ => by
    obtain ⟨a, rfl⟩ := hb.2 τ
    have gen : ∀ (n : ℕ) (h : rk a = n), ∃ w : Fin n → (Sp (DualNumber K) ⟶ Z.t.G.left),
        IsEigBasis Z φ x (emb a) w ∧ ∀ i, w (Fin.cast h i) = v a i := by
      rintro _ rfl
      exact ⟨v a, hv a, fun _ => rfl⟩
    obtain ⟨w, h1, h2⟩ := gen _ (hr a)
    refine ⟨w, h1, fun a' h i => ?_⟩
    obtain rfl := hb.1 h
    exact h2 i
  choose w h1 h2 using key
  exact ⟨⟨w, fun τ i => ((h1 τ).1 i).1, fun τ i => ((h1 τ).1 i).2, fun τ z hz hz' => (h1 τ).2 z ⟨hz, hz'⟩⟩,
    fun a => funext fun i => h2 _ a rfl i⟩

end Lie

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c Oz _ β Z F _ e ι rk emb dual hr Bs Bg Y M hM jB πB u π fl hu hb K _ _ y xb χ hy hχ x hx`. Substitute `hx` using the available equality. Establish `key : ∀ a, ∃ v, IsEigBasis Z χ (xb ≫ πB ≫ genι Z) (emb a) v ∧ AgreeAt Z (hM a) jB (u a) π (fl a) (dual a) y xb (xb ≫ πB ≫ genι Z) v` using `fun a => by`. Take `⟨V, f, hV, hf⟩` from `hM a ((xb ≫ jB) (IsLocalRing.closedPoint K))`. Establish `hx : ⊤ ≤ (xb ≫ jB) ⁻¹ᵁ V` using `(Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of K) (xb ≫ jB) hV).ge`.

Take `⟨A, hA⟩` from `(GlobalTheory.T.flag_matrix_unique_up_to_triangular Bs Y (M a) (rk a) (hM a) π (fl a) V f hf K y (hy ▸ hx)).1`. Take `⟨d, hd, rfl⟩` from `exists_lieMat_eq (dual a) hA.1`. Establish `h1` using `(hu a).1 V f hf K xb hx (χ.comp e.toRingHom) (by`. Establish `: xb ≫ πB ≫ genStr Z ≫ spMap e.toRingHom = (xb ≫ πB ≫ genStr Z) ≫ spMap e.toRingHom`. Simplify using `only [Category.assoc]`.

Rewrite using `[this, hχ, ← Spec.map_comp]`. Use the proof step `rfl)`. Rewrite `h1` using `[show (χ.comp e.toRingHom).comp e.symm.toRingHom = χ from RingHom.ext fun z => by simp]`. Take `⟨v, hv, hc⟩` from `exists_eigBasis_comb h1 hd`. Conclude with `⟨v, hv, GlobalTheory.T.toroidal_flag_bundle_rank_dual E H Dw l Xo c Oz β Z F e (rk a) (emb a) (dual a) Bs Bg Y (M a) (hM a) jB πB (u a) π (fl a) (hu a) K y xb χ hy hχ v V f hf hx d hd hc hA⟩`.

Use `choose v h1 h2 using key`. Take `⟨g, hg⟩` from `exists_eigFrame_of_bases hr hb h1`. Conclude with `⟨g, hy, rfl, hχ, fun a => by rw [hg a]; exact h2 a⟩`.
-/
theorem exists_bears : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (Oz : Type) [CommRing Oz] (β : Oz →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (ι : Type) (rk : ι → ℕ) (emb : ι → (E →+* ℂ)) (dual : ι → Bool) (hr : ∀ a, rk a = Dw.mult (emb a)) (Bs Bg Y : Scheme.{0}) (M : ι → Bs.Modules) (hM : ∀ a, IsVB (M a) (rk a)) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen Z) (u : ∀ a, FrAssign Z (M a) (rk a) jB) (π : Y ⟶ Bs) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (M a)) (rk a)), (∀ a, IsLieFrames Z e jB πB (M a) (rk a) (emb a) (dual a) (u a)) → Function.Bijective emb → ∀ (K : Type) [CommRing K] [IsLocalRing K] (y : Sp K ⟶ Y) (xb : Sp K ⟶ Bg) (χ : c.F →+* K), y ≫ π = xb ≫ jB → xb ≫ πB ≫ genStr Z = spMap χ → ∀ x : Sp K ⟶ Z.X, x = xb ≫ πB ≫ genι Z → ∃ g : EigFrame Z χ x, Bears Z emb dual hr hM jB πB u π fl y xb g := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z F _ e ι rk emb dual hr Bs Bg Y M hM jB πB u π fl hu hb K _ _ y xb χ hy hχ x hx
  subst hx
  have key : ∀ a, ∃ v, IsEigBasis Z χ (xb ≫ πB ≫ genι Z) (emb a) v ∧
      AgreeAt Z (hM a) jB (u a) π (fl a) (dual a) y xb (xb ≫ πB ≫ genι Z) v := fun a => by
    obtain ⟨V, f, hV, hf⟩ := hM a ((xb ≫ jB) (IsLocalRing.closedPoint K))
    have hx : ⊤ ≤ (xb ≫ jB) ⁻¹ᵁ V :=
      (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of K) (xb ≫ jB) hV).ge
    obtain ⟨A, hA⟩ := (GlobalTheory.T.flag_matrix_unique_up_to_triangular Bs Y (M a) (rk a) (hM a) π (fl a) V f hf K y (hy ▸ hx)).1
    obtain ⟨d, hd, rfl⟩ := exists_lieMat_eq (dual a) hA.1
    have h1 := (hu a).1 V f hf K xb hx (χ.comp e.toRingHom) (by
      have : xb ≫ πB ≫ genStr Z ≫ spMap e.toRingHom = (xb ≫ πB ≫ genStr Z) ≫ spMap e.toRingHom := by
        simp only [Category.assoc]
      rw [this, hχ, ← Spec.map_comp]
      rfl)
    rw [show (χ.comp e.toRingHom).comp e.symm.toRingHom = χ from RingHom.ext fun z => by simp] at h1
    obtain ⟨v, hv, hc⟩ := exists_eigBasis_comb h1 hd
    exact ⟨v, hv, GlobalTheory.T.toroidal_flag_bundle_rank_dual E H Dw l Xo c Oz β Z F e (rk a) (emb a) (dual a) Bs Bg Y (M a) (hM a) jB πB (u a) π
      (fl a) (hu a) K y xb χ hy hχ v V f hf hx d hd hc hA⟩
  choose v h1 h2 using key
  obtain ⟨g, hg⟩ := exists_eigFrame_of_bases hr hb h1
  exact ⟨g, hy, rfl, hχ, fun a => by rw [hg a]; exact h2 a⟩

end GlobalTheory.FlagCls

end
