import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.PrimeSpectrumDualEq
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsHomOfLinearScalingHermForm
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LbIsoPowOfHermFormPullEq
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FamilyUniformisationFibreThetaStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PureTypeVectorSpansQuadraticLattice
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolAVPullbackOfIsLocalRing

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace PureType

/- English proof (translation)
Substitute `hg` using the available equality. Use function extensionality and compare the values at `j`. Rewrite using `[Subsingleton.elim j i]`.
-/
theorem eq_const {g : ℕ} (hg : g = 1) (z : Fin g → ℂ) (i : Fin g) : z = fun _ => z i := by
  subst hg
  funext j
  rw [Subsingleton.elim j i]

/- English proof (translation)
Establish `hs : (0 : ℝ) < Real.sqrt d` using `Real.sqrt_pos.2 (by exact_mod_cast hd)`. Use `set r : ℝ := (hermForm Hm (fun _ => c) (fun _ => c)).re with hr`. Establish `hr0 : 0 < r` using `hpos _ fun h => hc (congrFun h ⟨0, by omega⟩)`. Establish `hre : hermForm Hm (fun _ => c) (fun _ => c) = (r : ℂ)` using `Complex.ext (by simp [hr]) (by simp [PureTypeVector.hermForm_self_im hH])`. Establish `key : ∀ z w : ℂ, hermForm Hm (fun _ => c * z) (fun _ => c * w) = z * starRingEnd ℂ w * r` using `fun z w => by`.

Rewrite using `[← hre, ← PureTypeVector.hermForm_smul_smul]`. Apply the tactic sequence `congr 1 <;> funext _ <;> simp [mul_comm]`. Set `e₁ : Λ` to `⟨_, (hΛ _).2 ⟨1, 0, rfl⟩⟩`. Set `e₂ : Λ` to `⟨_, (hΛ _).2 ⟨0, 1, rfl⟩⟩`. Establish `hN : ((Ef e₂ e₁ : ℤ) : ℝ) = Real.sqrt d / 2 * r`.

Rewrite using `[hE, key]`. Simplify using the standard rewrite rules. Establish `hN0 : 0 < Ef e₂ e₁`. Establish `: (0 : ℝ) < (Ef e₂ e₁ : ℤ)` using `by rw [hN]; positivity`. Conclude with `this` after adjusting the coercions.

Establish `hdvd : ∀ a b : Λ, Ef e₂ e₁ ∣ Ef a b` using `fun a b => by`. Take `⟨m, n, ha⟩` from `(hΛ _).1 a.2`. Take `⟨m', n', hb⟩` from `(hΛ _).1 b.2`. Use `⟨n * m' - m * n', ?_⟩` and prove the remaining obligations. Establish `: ((Ef a b : ℤ) : ℝ) = (Ef e₂ e₁ : ℤ) * (n * m' - m * n')`.

Rewrite using `[hN, hE, ha, hb, key]`. Simplify using `[map_ofNat]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `this` after adjusting the coercions. Set `f : Λ →+ ℤ` to `AddMonoidHom.mk' (fun b => Ef e₂ b / Ef e₂ e₁) fun a b => by`.

Rewrite using `[map_add, Int.add_ediv_of_dvd_left (hdvd _ _)]`. Take `⟨a, ha⟩` from `hb f.toIntLinearMap`. Establish `h1 : Ef a e₁ = 1`. Rewrite using `[ha]`. Conclude with `Int.ediv_self hN0.ne'`.

Establish `h2 : Ef e₂ e₁ = 1` using `Int.eq_one_of_dvd_one hN0.le (h1 ▸ hdvd a e₁)`. Rewrite `hN` using `[h2]`. Establish `h3 : (r : ℂ) = 2 / (Real.sqrt d : ℝ)`. Establish `: r = 2 / Real.sqrt d`. Clear the denominators using the available nonvanishing facts.

Move the coercions through the operations in `at hN`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[this]`. Use `push_cast`. Both sides reduce to the same expression.

Rewrite using `[key, h3]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hermForm_of_isQuadLattice {g : ℕ} (hg : g = 1) {Λ : Submodule ℤ (Fin g → ℂ)} {d : ℕ} (hd : 0 < d) {c : ℂ}
    (hc : c ≠ 0) (hΛ : IsQuadLattice Λ d c) {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) {Ef : LinearMap.BilinForm ℤ Λ}
    (hE : ∀ a b : Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) (hb : Function.Surjective Ef) (z w : ℂ) :
    hermForm Hm (fun _ => c * z) (fun _ => c * w) = 2 * z * starRingEnd ℂ w / Real.sqrt d := by
  have hs : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  set r : ℝ := (hermForm Hm (fun _ => c) (fun _ => c)).re with hr
  have hr0 : 0 < r := hpos _ fun h => hc (congrFun h ⟨0, by omega⟩)
  have hre : hermForm Hm (fun _ => c) (fun _ => c) = (r : ℂ) :=
    Complex.ext (by simp [hr]) (by simp [PureTypeVector.hermForm_self_im hH])
  have key : ∀ z w : ℂ, hermForm Hm (fun _ => c * z) (fun _ => c * w) = z * starRingEnd ℂ w * r := fun z w => by
    rw [← hre, ← PureTypeVector.hermForm_smul_smul]
    congr 1 <;> funext _ <;> simp [mul_comm]
  let e₁ : Λ := ⟨_, (hΛ _).2 ⟨1, 0, rfl⟩⟩
  let e₂ : Λ := ⟨_, (hΛ _).2 ⟨0, 1, rfl⟩⟩
  have hN : ((Ef e₂ e₁ : ℤ) : ℝ) = Real.sqrt d / 2 * r := by
    rw [hE, key]
    simp
  have hN0 : 0 < Ef e₂ e₁ := by
    have : (0 : ℝ) < (Ef e₂ e₁ : ℤ) := by rw [hN]; positivity
    exact_mod_cast this
  have hdvd : ∀ a b : Λ, Ef e₂ e₁ ∣ Ef a b := fun a b => by
    obtain ⟨m, n, ha⟩ := (hΛ _).1 a.2
    obtain ⟨m', n', hb⟩ := (hΛ _).1 b.2
    refine ⟨n * m' - m * n', ?_⟩
    have : ((Ef a b : ℤ) : ℝ) = (Ef e₂ e₁ : ℤ) * (n * m' - m * n') := by
      rw [hN, hE, ha, hb, key]
      simp [map_ofNat]
      ring
    exact_mod_cast this
  let f : Λ →+ ℤ := AddMonoidHom.mk' (fun b => Ef e₂ b / Ef e₂ e₁) fun a b => by
    rw [map_add, Int.add_ediv_of_dvd_left (hdvd _ _)]
  obtain ⟨a, ha⟩ := hb f.toIntLinearMap
  have h1 : Ef a e₁ = 1 := by
    rw [ha]
    exact Int.ediv_self hN0.ne'
  have h2 : Ef e₂ e₁ = 1 := Int.eq_one_of_dvd_one hN0.le (h1 ▸ hdvd a e₁)
  rw [h2] at hN
  have h3 : (r : ℂ) = 2 / (Real.sqrt d : ℝ) := by
    have : r = 2 / Real.sqrt d := by
      field_simp
      push_cast at hN
      linarith
    rw [this]
    push_cast
    rfl
  rw [key, h3]
  ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Take `⟨h₁, h₂, h₃, h₄, h₅⟩` from `h`. Use `⟨fun a => have := h₁ a; inferInstance, fun a b => by simp only [h₂, MonObj.comp_mul], fun s a => by simp only [h₃, Category.assoc], fun a => by simpa only [Category.assoc] using h₄ a, fun a ha => ?_⟩` and prove the remaining obligations. Take `⟨N, hN, hI⟩` from `h₅ a ha`. Use `⟨N, hN, ?_⟩` and prove the remaining obligations. Establish `hP` using `t.PP.isLB`.

Use `LBIso.trans (isLB_lbPow (pull_isLB hP _) _) (isLB_lbPow (pull_isLB (pull_isLB hP _) _) _) (isLB_lbPow hM' _) (lbIso_lbPow (LBIso.chartPull (chartPullSame t.PP.L _ _ _ e.left fun _ => rfl) (chartPullPull _ e.left) (lbIso_refl (pull_isLB hP (φ a).left))) N) ?_` and prove the remaining obligations. Conclude with `LBIso.trans (isLB_lbPow (pull_isLB (pull_isLB hP _) _) _) (isLB_lbPow (pull_isLB hM _) _) (isLB_lbPow hM' _) (LBIso.chartPull (chartPullPowPull _ e.left _) (chartPullPowPull M e.left _) hI) (lbIso_lbPow he.symm _)`.
-/
theorem IsHomFamily.comp {D : Datum H} {R : Type} [CommRing R] {t : SAB H (Sp R)} {B B' : Over (Sp R)} [GrpObj B]
    [GrpObj B'] {M : LB B.left} {M' : LB B'.left} (hM : M.IsLB) (hM' : M'.IsLB) (e : B' ⟶ B) [IsMonHom e]
    (he : LBIso M' (M.pull e.left)) {v : epsR R ⟶ B'} {L : Submodule (𝓞 E) D.La} {ρ : R} {S : Set L}
    {φ : L → (B ⟶ t.G)} (h : IsHomFamily t B M (v ≫ e) L ρ S φ) :
    IsHomFamily t B' M' v L ρ S (fun a => e ≫ φ a) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨fun a => have := h₁ a; inferInstance, fun a b => by simp only [h₂, MonObj.comp_mul],
    fun s a => by simp only [h₃, Category.assoc], fun a => by simpa only [Category.assoc] using h₄ a, fun a ha => ?_⟩
  obtain ⟨N, hN, hI⟩ := h₅ a ha
  refine ⟨N, hN, ?_⟩
  have hP := t.PP.isLB
  refine LBIso.trans (isLB_lbPow (pull_isLB hP _) _) (isLB_lbPow (pull_isLB (pull_isLB hP _) _) _) (isLB_lbPow hM' _)
    (lbIso_lbPow (LBIso.chartPull (chartPullSame t.PP.L _ _ _ e.left fun _ => rfl) (chartPullPull _ e.left)
      (lbIso_refl (pull_isLB hP (φ a).left))) N) ?_
  exact LBIso.trans (isLB_lbPow (pull_isLB (pull_isLB hP _) _) _) (isLB_lbPow (pull_isLB hM _) _) (isLB_lbPow hM' _)
    (LBIso.chartPull (chartPullPowPull _ e.left _) (chartPullPowPull M e.left _) hI) (lbIso_lbPow he.symm _)

/- English proof (translation)
Establish `: M.transpose.conjTranspose.mulVec (star w) = star (M.mulVec w)`. Rewrite using `[Matrix.star_mulVec, ← Matrix.mulVec_transpose]`. Both sides reduce to the same expression. Rewrite using `[hermForm, hermForm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, this, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]`.
-/
theorem hermForm_mulVec {g g' : ℕ} (M : Matrix (Fin g') (Fin g) ℂ) (Hm : Matrix (Fin g') (Fin g') ℂ) (z w : Fin g → ℂ) :
    hermForm (M.transpose * Hm * M.transpose.conjTranspose) z w = hermForm Hm (M.mulVec z) (M.mulVec w) := by
  have : M.transpose.conjTranspose.mulVec (star w) = star (M.mulVec w) := by
    rw [Matrix.star_mulVec, ← Matrix.mulVec_transpose]
    rfl
  rw [hermForm, hermForm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, this, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

/- English proof (translation)
Establish `key` using `hermForm_mulVec (LinearMap.toMatrix' F.toLinearMap) Hm`. Simplify using `only [LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe] at key`. Establish `h` using `pureType_vector_spans_quadratic_lattice E H D g ty Pe _ hP (Matrix.isHermitian_mul_mul_conjTranspose (LinearMap.toMatrix' F.toLinearMap).transpose hH) (fun z hz => by rw [key]; exact hpos _ (F.map_ne_zero_iff.2 hz)) (fun x y => by rw [key, hE]) ρ a hρ a.2`. Simplify `h` using `only [key]`.
-/
theorem hermForm_line {D : Datum H} {g g' : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)}
    (hP : IsPeriod D ty Pe) (F : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g' → ℂ)) {Hm : Matrix (Fin g') (Fin g') ℂ}
    (hH : Hm.IsHermitian) (hpos : ∀ z : Fin g' → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (hE : ∀ a b, (hermForm Hm (F (Pe a)) (F (Pe b))).im = D.EF a b) {ρ : ℂ} (hρ : ρ ^ 2 = -(H.d : ℂ))
    (a : lat hP ρ) :
    (∀ m n : ℤ, ((m : ℂ) + n * ((1 + Complex.I * Real.sqrt H.d) / 2)) • Pe a ∈ Pe.range) ∧
    ∀ z w : ℂ, hermForm Hm (F (z • Pe a)) (F (w • Pe a)) =
      ((D.EF (H.w0 • (a : D.La)) a).natAbs : ℂ) * (2 * z * starRingEnd ℂ w / Real.sqrt H.d) := by
  have key := hermForm_mulVec (LinearMap.toMatrix' F.toLinearMap) Hm
  simp only [LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe] at key
  have h := pureType_vector_spans_quadratic_lattice E H D g ty Pe _ hP
    (Matrix.isHermitian_mul_mul_conjTranspose (LinearMap.toMatrix' F.toLinearMap).transpose hH)
    (fun z hz => by rw [key]; exact hpos _ (F.map_ne_zero_iff.2 hz)) (fun x y => by rw [key, hE]) ρ a hρ a.2
  simpa only [key] using h

/- English proof (translation)
Use `t'.semi.smooth` as an intermediate fact. Use `t'.semi.geomConnected` as an intermediate fact. Take `⟨w, g, -⟩` from `m.lin`. Take `⟨U, hU, hc, -⟩` from `exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := y (IsLocalRing.closedPoint R)) trivial`. Establish `hy : ∀ x, y x ∈ U` using `fun x => (congrArg (fun V => x ∈ V) (Scheme.preimage_eq_top_of_closedPoint_mem y hc)).mpr trivial`.

Use `LocalFibre.connectedSpace_sp R` as an intermediate fact. Establish `: ConnectedSpace t'.G.left` using `GeometricallyConnected.connectedSpace t'.G.hom t'.G.hom.isOpenMap`. Take `⟨-, ws, gs', -⟩` from `t'.sym`. Conclude with `⟨⟨inferInstance, inferInstance, MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 hp, ‹_›⟩, exists_dim_of_preconnected t'.G.hom (eSec t'.G (IsLocalRing.closedPoint R)), fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩, relAmple_pull m.cart.1 t.PP.isLB t'.PP.isLB …`.
-/
theorem polarised_of_sabMap {S : Scheme.{0}} {t : SAB H S} (hp : IsProper t.G.hom) (hA : Out.RelAmple t.G t.PP.L)
    (hK : Out.KTriv t.G t.PP.L) {R : Type} [CommRing R] [IsLocalRing R] {y : Sp R ⟶ S} {t' : SAB H (Sp R)}
    (m : SABMap t' t y) :
    IsAbelianScheme t'.G ∧ (∃ d, SmoothOfRelativeDimension d t'.G.hom) ∧ Out.Sym t'.G t'.PP.L ∧
      Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L ∧ LBIso t'.PP.L (t.PP.L.pull m.φ) := by
  have := t'.semi.smooth
  have := t'.semi.geomConnected
  obtain ⟨w, g, -⟩ := m.lin
  obtain ⟨U, hU, hc, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤)
    (x := y (IsLocalRing.closedPoint R)) trivial
  have hy : ∀ x, y x ∈ U := fun x =>
    (congrArg (fun V => x ∈ V) (Scheme.preimage_eq_top_of_closedPoint_mem y hc)).mpr trivial
  have := LocalFibre.connectedSpace_sp R
  have : ConnectedSpace t'.G.left := GeometricallyConnected.connectedSpace t'.G.hom t'.G.hom.isOpenMap
  obtain ⟨-, ws, gs', -⟩ := t'.sym
  exact ⟨⟨inferInstance, inferInstance, MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 hp, ‹_›⟩,
    exists_dim_of_preconnected t'.G.hom (eSec t'.G (IsLocalRing.closedPoint R)),
    fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩,
    relAmple_pull m.cart.1 t.PP.isLB t'.PP.isLB ((isGen_iff w).1 g) U hU hy hA,
    kTriv_pull m.cart t.PP.isLB t'.PP.isLB ((isGen_iff w).1 g) hK, ⟨w, g⟩⟩

/- English proof (translation)
Use `show _ ≫ spMap (epsScaleR c) ≫ v.left = _`. Rewrite using `[← Category.assoc, ← hv]`. Use `congr 1`. Use `show Spec.map _ ≫ Spec.map _ = Spec.map _`. Rewrite using `[← Spec.map_comp]`.

Use `congr 1`. Apply the tactic sequence `ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem isTangent_scaleVec {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] (c : R) {v : epsR R ⟶ A}
    (hv : IsTangent v) : IsTangent (CMCurveTest.scaleVec c v) := by
  show _ ≫ spMap (epsScaleR c) ≫ v.left = _
  rw [← Category.assoc, ← hv]
  congr 1
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

/- English proof (translation)
Take `⟨hab, ⟨d, hd⟩, hs, ham, hk, hL⟩` from `polarised_of_sabMap Xo.univ.proper Xo.univ.ample Xo.univ.ktriv m`. Set `P : Out.PolAV (Sp ℂ)` to `{ A := t.G, g := d, smoothDim := hd, L := t.PP.L, isLB := t.PP.isLB, ample := ham, ktriv := hk, isAb := hab rigid := ⟨t.PP.rig, t.PP.rigGen⟩, sym := hs }`. Take `⟨u, Hm, χ, F, hAH, -, hD, hθ, hex, hF, hE⟩` from `T.familyUniformisation_fibre_theta hT hW E H D l Xo σ g ty FU i Pe hP P m.φ m.cart hL`. Take `⟨Hm₀, χ₀, Ef, hAH₀, hD₀, -, hθ₀, hE₀, hb⟩` from `hu`. Set `i₀ : Fin PC.g` to `⟨0, by omega⟩`.

Set `G : lat hP ρ → (Fin PC.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ)` to `fun a => F.toLinearMap ∘ₗ LinearMap.toSpanSingleton ℂ _ (Pe a) ∘ₗ (c⁻¹ • LinearMap.proj i₀)`. Establish `hG : ∀ a z, G a (fun _ => c * z) = F (z • Pe a)` using `fun a z => by`. Simplify using `[G, inv_mul_cancel_left₀ hc]`. Establish `hall : ∀ x : Fin PC.g → ℂ, ∃ z, x = fun _ => c * z` using `fun x => ⟨c⁻¹ * x i₀, by rw [mul_inv_cancel_left₀ hc]; exact eq_const hg x i₀⟩`. Establish `hline` using `hermForm_line hP F hAH.1 hAH.2.1 hE hρ`.

Establish `hGΛ : ∀ a, ∀ x ∈ u₀.Λ, G a x ∈ u.Λ` using `fun a x hx => by`. Take `⟨p, q, rfl⟩` from `(hΛ x).1 hx`. Rewrite using `[hG, hF]`. Conclude with `(hline a).1 p q`. Establish `hGH : ∀ a x y, hermForm Hm (G a x) (G a y) = (((FU.Di i).EF (H.w0 • (a : (FU.Di i).La)) a).natAbs : ℂ) * hermForm Hm₀ x y` using `fun a x y => by`.

Take `⟨z, rfl⟩` from `hall x`. Take `⟨w, rfl⟩` from `hall y`. Rewrite using `[hG, hG, (hline a).2, hermForm_of_isQuadLattice hg H.d_prime.pos hc hΛ hAH₀.1 hAH₀.2.1 hE₀ hb.2]`. Use `choose φ hφ hφe using fun a => exists_hom_of_linear_scaling_hermForm PC P u₀ u Hm₀ χ₀ Hm χ hAH₀ hAH (fun k => (hθ₀ k).2) (fun k => (hθ k).1) (G a) _ (hGΛ a) (hGH a)`. Establish `hφz : ∀ a z, (u₀.ex fun _ => c * z) ≫ φ a = u.ex (F (z • Pe a))` using `fun a z => by rw [← hφe, hG]`.

Establish `ext : ∀ f f' : PC.A ⟶ P.A, (∀ z, (u₀.ex fun _ => c * z) ≫ f = (u₀.ex fun _ => c * z) ≫ f') → f = f'`. Introduce `f f' h`. Establish `hs : Smooth PC.A.hom` using `PC.isAb.smooth`. Establish `hp : IsProper P.A.hom` using `P.isAb.proper`. Establish `hr : IsReduced PC.A.left` using `isReduced_of_smooth_complex _ PC.A.hom hs`.

Use `ComplexPoints.over_hom_ext_of_complexPoints fun x => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `u₀.ex_onto x`. Take `⟨z, rfl⟩` from `hall x`. Conclude with `h z`. Establish `hlin : ∀ (s : 𝓞 E) a, φ (s • a) = φ a ≫ t.act.act s` using `fun s a => ext _ _ fun z => by`.

Rewrite using `[← Category.assoc, hφz, hφz]`. Use `Over.OverMorphism.ext (m.cart.1.hom_ext ?_ (by rw [Over.w, Over.w]))` and prove the remaining obligations. Establish `e : z • Pe (s • a : lat hP ρ) = fun k => ty k (s : E) * (z • Pe a) k`. Use function extensionality and compare the values at `k`. Simplify using `only [Submodule.coe_smul, Pi.smul_apply, hP.1, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Use `(hex _).trans ?_` and prove the remaining obligations. Rewrite using `[e, FU.ex_lin i Pe hP, Over.comp_left, Over.comp_left, Category.assoc]`. Use `erw [m.act s, ← hex]`. Both sides reduce to the same expression.

Use `⟨φ, fun v hv => ⟨hφ, fun a b => ext _ _ fun z => ?_, hlin, fun a => ?_, fun a _ => ?_⟩, fun a z => ?_⟩` and prove the remaining obligations. Rewrite using `[MonObj.comp_mul, hφz, hφz, hφz, ← u.ex_add, ← map_add, ← smul_add, ← map_add]`. Both sides reduce to the same expression. Take `⟨w, hw, -⟩` from `hD₀ v hv`. Use `hφ a` as an intermediate fact.

Use `hφ (H.rt • a)` as an intermediate fact. Establish `h₁` using `HomLinear.isDiff_comp u₀ u (φ a) (G a) (hφe a) hv hw`. Establish `h₂` using `HomLinear.isDiff_comp u₀ u (φ (H.rt • a)) (G _) (hφe _) hv hw`. Establish `e : G (H.rt • a) w = ρ • G a w`. Take `⟨z, rfl⟩` from `hall w`.

Rewrite using `[hG, hG, ← map_smul F ρ, smul_comm ρ z, ← period_rt_smul hP a.2]`. Both sides reduce to the same expression. Rewrite `h₂` using `[e]`. Use `⟨![CMCurveTest.scaleVec ρ (v ≫ φ a)], fun j => by fin_cases j; rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[← hlin]`.

Simplify using `using (hD _).unique ⟨HomLinear.isTangent_comp _ hv, h₂⟩ ⟨isTangent_scaleVec ρ (HomLinear.isTangent_comp _ hv), CMCurveTest.isDiff_scaleVec u h₁ ρ⟩`. Conclude with `lbIso_pow_of_hermForm_pull_eq PC P u₀ u Hm₀ χ₀ Hm χ hAH₀ hAH (fun k => (hθ₀ k).2) (fun k => (hθ k).1) (G a) _ (hGΛ a) (hGH a) (φ a) (hφe a)`. Rewrite using `[← hex, ← hφz, Over.comp_left, Category.assoc]`.
-/
theorem exists_isHomFamily_complex (hT : ThetaUnifAV) (hW : Out.WeilSt) {D : Datum H} {l : Level H} {Xo : Moduli D l}
    {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (FU : FamilyUnif Xo σ ty) (i : Fin FU.n)
    {Pe : (FU.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (FU.Di i) ty Pe) {t : SAB H (Sp ℂ)}
    (m : SABMap t Xo.univ.t (FU.u i Pe)) {PC : Out.PolAV (Sp ℂ)} (u₀ : HolUnif PC.A PC.L PC.g) {c : ℂ}
    (hg : PC.g = 1) (hu : IsThetaUnif u₀) (hc : c ≠ 0) (hΛ : IsQuadLattice u₀.Λ H.d c) {ρ : ℂ}
    (hρ : ρ ^ 2 = -(H.d : ℂ)) :
    ∃ φ : lat hP ρ → (PC.A ⟶ t.G),
      (∀ v, IsTangent v → IsHomFamily t PC.A PC.L v (lat hP ρ) ρ Set.univ φ) ∧
      ∀ a z, (u₀.ex fun _ => c * z).left ≫ (φ a).left ≫ m.φ = (FU.ex i Pe (z • Pe a)).left := by
  obtain ⟨hab, ⟨d, hd⟩, hs, ham, hk, hL⟩ := polarised_of_sabMap Xo.univ.proper Xo.univ.ample Xo.univ.ktriv m
  let P : Out.PolAV (Sp ℂ) :=
    { A := t.G, g := d, smoothDim := hd, L := t.PP.L, isLB := t.PP.isLB, ample := ham, ktriv := hk, isAb := hab
      rigid := ⟨t.PP.rig, t.PP.rigGen⟩, sym := hs }
  obtain ⟨u, Hm, χ, F, hAH, -, hD, hθ, hex, hF, hE⟩ :=
    T.familyUniformisation_fibre_theta hT hW E H D l Xo σ g ty FU i Pe hP P m.φ m.cart hL
  obtain ⟨Hm₀, χ₀, Ef, hAH₀, hD₀, -, hθ₀, hE₀, hb⟩ := hu
  let i₀ : Fin PC.g := ⟨0, by omega⟩
  let G : lat hP ρ → (Fin PC.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ) := fun a =>
    F.toLinearMap ∘ₗ LinearMap.toSpanSingleton ℂ _ (Pe a) ∘ₗ (c⁻¹ • LinearMap.proj i₀)
  have hG : ∀ a z, G a (fun _ => c * z) = F (z • Pe a) := fun a z => by
    simp [G, inv_mul_cancel_left₀ hc]
  have hall : ∀ x : Fin PC.g → ℂ, ∃ z, x = fun _ => c * z := fun x =>
    ⟨c⁻¹ * x i₀, by rw [mul_inv_cancel_left₀ hc]; exact eq_const hg x i₀⟩
  have hline := hermForm_line hP F hAH.1 hAH.2.1 hE hρ
  have hGΛ : ∀ a, ∀ x ∈ u₀.Λ, G a x ∈ u.Λ := fun a x hx => by
    obtain ⟨p, q, rfl⟩ := (hΛ x).1 hx
    rw [hG, hF]
    exact (hline a).1 p q
  have hGH : ∀ a x y, hermForm Hm (G a x) (G a y) =
      (((FU.Di i).EF (H.w0 • (a : (FU.Di i).La)) a).natAbs : ℂ) * hermForm Hm₀ x y := fun a x y => by
    obtain ⟨z, rfl⟩ := hall x
    obtain ⟨w, rfl⟩ := hall y
    rw [hG, hG, (hline a).2, hermForm_of_isQuadLattice hg H.d_prime.pos hc hΛ hAH₀.1 hAH₀.2.1 hE₀ hb.2]
  choose φ hφ hφe using fun a => exists_hom_of_linear_scaling_hermForm PC P u₀ u Hm₀ χ₀ Hm χ hAH₀ hAH
    (fun k => (hθ₀ k).2) (fun k => (hθ k).1) (G a) _ (hGΛ a) (hGH a)
  have hφz : ∀ a z, (u₀.ex fun _ => c * z) ≫ φ a = u.ex (F (z • Pe a)) := fun a z => by rw [← hφe, hG]
  have ext : ∀ f f' : PC.A ⟶ P.A, (∀ z, (u₀.ex fun _ => c * z) ≫ f = (u₀.ex fun _ => c * z) ≫ f') → f = f' := by
    intro f f' h
    have hs : Smooth PC.A.hom := PC.isAb.smooth
    have hp : IsProper P.A.hom := P.isAb.proper
    have hr : IsReduced PC.A.left := isReduced_of_smooth_complex _ PC.A.hom hs
    refine ComplexPoints.over_hom_ext_of_complexPoints fun x => ?_
    obtain ⟨x, rfl⟩ := u₀.ex_onto x
    obtain ⟨z, rfl⟩ := hall x
    exact h z
  have hlin : ∀ (s : 𝓞 E) a, φ (s • a) = φ a ≫ t.act.act s := fun s a => ext _ _ fun z => by
    rw [← Category.assoc, hφz, hφz]
    refine Over.OverMorphism.ext (m.cart.1.hom_ext ?_ (by rw [Over.w, Over.w]))
    have e : z • Pe (s • a : lat hP ρ) = fun k => ty k (s : E) * (z • Pe a) k := by
      funext k
      simp only [Submodule.coe_smul, Pi.smul_apply, hP.1, smul_eq_mul]
      ring
    refine (hex _).trans ?_
    rw [e, FU.ex_lin i Pe hP, Over.comp_left, Over.comp_left, Category.assoc]
    erw [m.act s, ← hex]
    rfl
  refine ⟨φ, fun v hv => ⟨hφ, fun a b => ext _ _ fun z => ?_, hlin, fun a => ?_, fun a _ => ?_⟩, fun a z => ?_⟩
  · rw [MonObj.comp_mul, hφz, hφz, hφz, ← u.ex_add, ← map_add, ← smul_add, ← map_add]
    rfl
  · obtain ⟨w, hw, -⟩ := hD₀ v hv
    have := hφ a
    have := hφ (H.rt • a)
    have h₁ := HomLinear.isDiff_comp u₀ u (φ a) (G a) (hφe a) hv hw
    have h₂ := HomLinear.isDiff_comp u₀ u (φ (H.rt • a)) (G _) (hφe _) hv hw
    have e : G (H.rt • a) w = ρ • G a w := by
      obtain ⟨z, rfl⟩ := hall w
      rw [hG, hG, ← map_smul F ρ, smul_comm ρ z, ← period_rt_smul hP a.2]
      rfl
    rw [e] at h₂
    refine ⟨![CMCurveTest.scaleVec ρ (v ≫ φ a)], fun j => by fin_cases j; rfl, ?_⟩
    rw [← hlin]
    simpa using (hD _).unique ⟨HomLinear.isTangent_comp _ hv, h₂⟩
      ⟨isTangent_scaleVec ρ (HomLinear.isTangent_comp _ hv), CMCurveTest.isDiff_scaleVec u h₁ ρ⟩
  · exact lbIso_pow_of_hermForm_pull_eq PC P u₀ u Hm₀ χ₀ Hm χ hAH₀ hAH (fun k => (hθ₀ k).2) (fun k => (hθ k).1)
      (G a) _ (hGΛ a) (hGH a) (φ a) (hφe a)
  · rw [← hex, ← hφz, Over.comp_left, Category.assoc]

end PureType

open PureType in

/- English proof (translation)
Take `⟨_, _, _, _, _, m, -⟩` from `sabPull Out.CubePf.cubePull (FU.u i Pe) Xo.univ.t`. Establish `hB` using `isGrpPullback_pullback P₀.A (spMap (algebraMap k ℂ))`. Take `⟨e, he, heψ⟩` from `grpPullback_iso hB hψ`. Take `⟨v, hv, hv'⟩` from `exists_tangent_over _ hB hv₀`. Establish `hid : spMap (AlgHom.id k ℂ).toRingHom = 𝟙 _` using `Spec.map_id _`.

Use `choose φ hφ hφe using fun ε : ℤˣ => exists_isHomFamily_complex hT hW FU i hP m u₀ hg hu hc hΛ (ρ := ((ε : ℤ) : ℂ) * H.rt0) (by`. Rewrite using `[mul_pow, H.sqrt_neg_disc_sq, ← Int.cast_pow, ← Units.val_pow_eq_pow_val, Int.units_sq]`. Use the proof step `simp)`. Use `⟨FU.u i Pe, _, m, v, fun ε a => e.hom ≫ φ ε a, FU.over_σ i Pe hP, by rw [hid, Category.id_comp], hv, hv', fun ε => ⟨?_, fun a z x hx hx' => ?_⟩⟩` and prove the remaining obligations. Use `IsHomFamily.comp PC.isLB (pull_isLB P₀.isLB _) e.hom ?_ (hφ ε _ (HomLinear.isTangent_comp _ hv))` and prove the remaining obligations.

Conclude with `LBIso.chartPull (chartPullSame P₀.L _ _ _ e.hom.left fun _ => heψ.symm) (chartPullPull _ e.hom.left) hL.symm`. Establish `: x ≫ e.hom.left = (u₀.ex fun _ => c * z).left`. Use `hψ.1.hom_ext (by rw [Category.assoc, heψ]; exact hx) ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, Over.w, Over.w]`. Conclude with `hx'.trans hid`.

Rewrite using `[← hφe, ← this, Over.comp_left, Category.assoc, Category.assoc]`.
-/
theorem cmPoint_complex (hT : ThetaUnifAV) (hW : Out.WeilSt)
    (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n)
    (Pe : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty Pe)
    (k : IntermediateField ℚ ℂ) (hk : KA l ≤ k) (P₀ : Out.PolAV (Sp k)) (v₀ : epsR k ⟶ P₀.A) (hv₀ : IsTangent v₀)
    (PC : Out.PolAV (Sp ℂ)) (ψ : PC.A.left ⟶ P₀.A.left) (u₀ : HolUnif PC.A PC.L PC.g) (c : ℂ) (hg : PC.g = 1)
    (hψ : IsGrpPullback PC.A P₀.A (spMap (algebraMap k ℂ)) ψ) (hL : LBIso PC.L (P₀.L.pull ψ))
    (hu : IsThetaUnif u₀) (hc : c ≠ 0) (hΛ : IsQuadLattice u₀.Λ H.d c) :
    IsSpread FU i hP hk P₀ v₀ ψ u₀ c (fun _ => Set.univ) ℂ (AlgHom.id k ℂ) := by
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (FU.u i Pe) Xo.univ.t
  have hB := isGrpPullback_pullback P₀.A (spMap (algebraMap k ℂ))
  obtain ⟨e, he, heψ⟩ := grpPullback_iso hB hψ
  obtain ⟨v, hv, hv'⟩ := exists_tangent_over _ hB hv₀
  have hid : spMap (AlgHom.id k ℂ).toRingHom = 𝟙 _ := Spec.map_id _
  choose φ hφ hφe using fun ε : ℤˣ => exists_isHomFamily_complex hT hW FU i hP m u₀ hg hu hc hΛ
    (ρ := ((ε : ℤ) : ℂ) * H.rt0) (by
      rw [mul_pow, H.sqrt_neg_disc_sq, ← Int.cast_pow, ← Units.val_pow_eq_pow_val, Int.units_sq]
      simp)
  refine ⟨FU.u i Pe, _, m, v, fun ε a => e.hom ≫ φ ε a, FU.over_σ i Pe hP, by rw [hid, Category.id_comp], hv, hv',
    fun ε => ⟨?_, fun a z x hx hx' => ?_⟩⟩
  · refine IsHomFamily.comp PC.isLB (pull_isLB P₀.isLB _) e.hom ?_ (hφ ε _ (HomLinear.isTangent_comp _ hv))
    exact LBIso.chartPull (chartPullSame P₀.L _ _ _ e.hom.left fun _ => heψ.symm) (chartPullPull _ e.hom.left) hL.symm
  · have : x ≫ e.hom.left = (u₀.ex fun _ => c * z).left := by
      refine hψ.1.hom_ext (by rw [Category.assoc, heψ]; exact hx) ?_
      rw [Category.assoc, Over.w, Over.w]
      exact hx'.trans hid
    rw [← hφe, ← this, Over.comp_left, Category.assoc, Category.assoc]

end GlobalTheory
