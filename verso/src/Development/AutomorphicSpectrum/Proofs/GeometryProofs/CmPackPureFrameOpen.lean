import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TransitionMatrixPeriodFrameStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackEigenPeriodStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorsBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackPureFrameStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveZNeZeroStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GramDetNeZeroLocalBasisCofiniteStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PureTypeLatticesOrthogonalStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsTransitionMatrixGramStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl.CMValue

/- English proof (translation)
Rewrite using `[Matrix.fromRows_fromCols_eq_fromBlocks, Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul, Matrix.det_one, Matrix.det_smul, Matrix.det_nonsing_inv]`. Simplify using `only [Fintype.card_fin, mul_one, Ring.inverse_eq_inv', inv_pow]`. Clear the denominators using the available nonvanishing facts.
-/
theorem det_rows (p q : ℕ) (z₁ z₂ : ℂ) (G : Matrix (Fin q) (Fin q) ℂ) (hz : z₂ ≠ 0) (hG : G.det ≠ 0) :
    (Matrix.fromRows (Matrix.fromCols (z₁ • (1 : Matrix (Fin p) (Fin p) ℂ)) (0 : Matrix (Fin p) (Fin q) ℂ))
      (Matrix.fromCols (0 : Matrix (Fin q) (Fin p) ℂ) (z₂⁻¹ • G⁻¹))).det * (z₂ ^ q * G.det) = z₁ ^ p := by
  rw [Matrix.fromRows_fromCols_eq_fromBlocks, Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul, Matrix.det_one,
    Matrix.det_smul, Matrix.det_nonsing_inv]
  simp only [Fintype.card_fin, mul_one, Ring.inverse_eq_inv', inv_pow]
  field_simp

/- English proof (translation)
Use extensionality with `t`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, rfl⟩`. Conclude with `⟨spMap f s, by simp⟩`. Introduce and unpack `⟨s, rfl⟩`.

Take `⟨s'⟩ : Nonempty (Sp L)` from `inferInstance`. Use `⟨s', ?_⟩` and prove the remaining obligations. Establish `: spMap f s' = s` using `Subsingleton.elim (α := PrimeSpectrum K) _ _`. Simplify using `[this]`.
-/
theorem range_comp {K L : Type} [Field K] [Field L] (f : K →+* L) {Y : Scheme.{0}} (y : Sp K ⟶ Y) :
    Set.range (spMap f ≫ y) = Set.range y := by
  ext t
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨spMap f s, by simp⟩
  · rintro ⟨s, rfl⟩
    obtain ⟨s'⟩ : Nonempty (Sp L) := inferInstance
    refine ⟨s', ?_⟩
    have : spMap f s' = s := Subsingleton.elim (α := PrimeSpectrum K) _ _
    simp [this]

/- English proof (translation)
Use extensionality with `k`. Simplify using `only [tyPart, Pi.smul_apply, smul_eq_mul]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem tyPart_smul {E : Type} [Field E] {g : ℕ} (ty : Fin g → (E →+* ℂ)) (τ : E →+* ℂ) (a : ℂ) (z : Fin g → ℂ) :
    tyPart ty τ (a • z) = a • tyPart ty τ z := by
  ext k
  simp only [tyPart, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

end GlobalTheory.CompanionTheory.Ar.Fl.CMValue

namespace GlobalTheory.CompanionTheory.Ar.Fl.CMValue

/- English proof (translation)
Introduce `h`. Take `⟨r, hr⟩` from `Complex.conj_eq_iff_real.1 h`. Establish `h1` using `H.sqrt_neg_disc_sq`. Rewrite `h1` using `[hr]`. Establish `h2 : r ^ 2 = -(H.d : ℝ)` using `by exact_mod_cast h1`.

Establish `h3 : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`. Use polynomial arithmetic with `[sq_nonneg r]`.
-/
theorem conj_cmHostRoot_ne_self {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    starRingEnd ℂ H.rt0 ≠ H.rt0 := by
  intro h
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h
  have h1 := H.sqrt_neg_disc_sq
  rw [hr] at h1
  have h2 : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast h1
  have h3 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  nlinarith [sq_nonneg r]

end GlobalTheory.CompanionTheory.Ar.Fl.CMValue

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c g ty FU i Z P hP X x hx U τ φ e ρ T v w hty hτ hmem hline he hconst hxi hT hfr`. Establish `hfr0` using `(GlobalTheory.T.cm_pack_pure_frame E H D l Xo c g ty FU i Z P hP X x hx τ hty hτ hxi).2 v w hfr`. Set `f : X.K →+* ℂ` to `algebraMap X.K ℂ`. Establish `hcomp : f.comp X.β = algebraMap c.F ℂ` using `by ext a; rfl`. Set `y' : Sp ℂ ⟶ Xo.XF c` to `spMap f ≫ X.y`.

Establish `hyu : under y' = spMap f ≫ under X.y` using `Category.assoc _ _ _`. Establish `hy'u : under y' = FU.u i P` using `hyu.trans X.pt`. Establish `hy's : y' ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ)`. Rewrite using `[Category.assoc, X.hy, ← hcomp, spMap_comp]`. Establish `hU : Set.range X.y ⊆ U`.

Rewrite using `[← CMValue.range_comp f X.y]`. Conclude with `hmem P y' hP hy'u hy's`. Establish `hF : IsFramed U τ X.β X.y v w` using `⟨hfr0.1, hU, hfr0.2.2⟩`. Take `⟨⟨v', hv'⟩, hv⟩` from `GlobalTheory.T.tangent_vectors_base_change E H Xo.X Xo.univ.t X.K ℂ f (under X.y) (under y') (X.β.comp (tauIn c τ)) D.p v hyu`. Take `⟨⟨w', hw'⟩, hw⟩` from `GlobalTheory.T.tangent_vectors_base_change E H Xo.X Xo.univ.t X.K ℂ f (under X.y) (under y') (X.β.comp (tauIn c (ComplexEmbedding.conjugate τ))) D.q w hyu`.

Establish `hF' : IsFramed U τ (algebraMap c.F ℂ) y' v' w'`. Use `⟨hy's, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[CMValue.range_comp f X.y]`. Conclude with `hU`. Use `(hv v' hv').1 hF.2.2.1` as an intermediate fact.

Rewrite `this` using `[← RingHom.comp_assoc, hcomp]`. Then use the resulting hypothesis. Use `(hw w' hw').1 hF.2.2.2` as an intermediate fact. Rewrite `this` using `[← RingHom.comp_assoc, hcomp]`. Then use the resulting hypothesis. Establish `hz₂ : (Z false).z ≠ 0` using `GlobalTheory.T.curve_z_ne_zero E H _ (Z false)`. Establish `hcard : Fintype.card (Fin D.p ⊕ Fin D.q) = (FU.Di i).p + (FU.Di i).q`.

Simplify using `[(FU.sig i).1, (FU.sig i).2]`. Establish `hTdet : T.det ≠ 0`. Take `⟨T', hT', -, hT'det, -⟩` from `GlobalTheory.T.exists_transition_matrix_gram E H (FU.Di i) (Fin D.p ⊕ Fin D.q) x e hcard he`. Establish `hge` using `(GlobalTheory.T.gram_det_ne_zero_local_basis_cofinite E H (FU.Di i) (Fin D.p ⊕ Fin D.q) e hcard he).1`. Establish `hmul : T * gramE (FU.Di i) e = T' * gramE (FU.Di i) e`.

Use extensionality with `m n`. Simplify using `only [Matrix.mul_apply, gramE, Matrix.of_apply]`. Rewrite using `[← hT m (e n), ← hT' m (e n)]`. Establish `hTT : T = T'`. Establish `hu : IsUnit (gramE (FU.Di i) e).det` using `isUnit_iff_ne_zero.2 hge`.

Rewrite using `[← Matrix.mul_nonsing_inv_cancel_right _ T hu, hmul, Matrix.mul_nonsing_inv_cancel_right _ T' hu]`. Rewrite using `[hTT]`. Conclude with `hT'det hxi`. Establish `hconst'` using `GlobalTheory.T.transition_matrix_period_frame E H D l Xo c g ty FU i U τ φ e x T ρ he hT hTdet hconst`. Establish `orth : ∀ a j, sesq (FU.Di i) (x (.inl a)) (x (.inr j)) = 0 ∧ sesq (FU.Di i) (x (.inr j)) (x (.inl a)) = 0` using `fun a j => GlobalTheory.T.pure_type_lattices_orthogonal E H (FU.Di i) g ty P hP _ _ (hx.1 a) (hx.2 j)`.

Establish `hgram : gramE (FU.Di i) x = Matrix.fromBlocks (gramE (FU.Di i) (x ∘ Sum.inl)) 0 0 (gramE (FU.Di i) (x ∘ Sum.inr))`. Use extensionality with `m n`. Apply the tactic sequence `rcases m with a | j <;> rcases n with b | k`. Both sides reduce to the same expression. Conclude with `(orth a k).1`.

Conclude with `(orth b j).2`. Both sides reduce to the same expression. Establish `hG₀ : (gramE (FU.Di i) (x ∘ Sum.inr)).det ≠ 0`. Establish `h` using `(GlobalTheory.T.gram_det_ne_zero_local_basis_cofinite E H (FU.Di i) (Fin D.p ⊕ Fin D.q) x hcard hxi).1`. Rewrite `h` using `[hgram, Matrix.det_fromBlocks_zero₂₁]`.

Conclude with `right_ne_zero_of_mul h`. Set `G : Matrix (Fin D.q) (Fin D.q) ℂ` to `τ.mapMatrix (gramE (FU.Di i) (x ∘ Sum.inr))`. Establish `hGdet : G.det = τ (gramE (FU.Di i) (x ∘ Sum.inr)).det` using `(RingHom.map_det τ _).symm`. Establish `hG : G.det ≠ 0`. Rewrite using `[hGdet]`.

Conclude with `(map_ne_zero τ).2 hG₀`. Establish `hGu : IsUnit G.det` using `isUnit_iff_ne_zero.2 hG`. Establish `hDV : ∀ a, IsDerivAt0 (fun z => (FU.ex i P z).left) ((Z true).z • tyPart ty τ (P (x (.inl a)))) (v' a).left`. Introduce `a`. Rewrite using `[hv' a]`.

Conclude with `GlobalTheory.T.cm_pack_eigen_period E H D l Xo c g ty FU i Z P hP X true τ ⟨x (.inl a), hx.1 a⟩ (v a) (hfr.1 a)`. Establish `hDW : ∀ j, IsDerivAt0 (fun z => (FU.ex i P z).left) ((Z false).z • tyPart ty (ComplexEmbedding.conjugate τ) (P (x (.inr j)))) (w' j).left`. Introduce `j`. Rewrite using `[hw' j]`. Conclude with `GlobalTheory.T.cm_pack_eigen_period E H D l Xo c g ty FU i Z P hP X false (ComplexEmbedding.conjugate τ) ⟨x (.inr j), hx.2 j⟩ (w j) (hfr.2 j)`.

Establish `hvan : ∀ a, tyPart ty (ComplexEmbedding.conjugate τ) (P (x (.inl a))) = 0`. Introduce `a`. Use extensionality with `k`. Distinguish the cases in `hk : ty k = ComplexEmbedding.conjugate τ`. Establish `: P (x (.inl a)) k = 0`.

Apply `hx.1 a k` to reduce the goal to its premises. Rewrite using `[hk, ComplexEmbedding.conjugate_coe_eq, hτ]`. Simplify `CMValue.conj_cmHostRoot_ne_self H` using `[sgnRt]`. Simplify using `[tyPart, this]`. Simplify using `[tyPart, hk]`.

Establish `hC : ∀ a, tyPart ty τ (∑ m, Matrix.fromCols ((Z true).z • (1 : Matrix (Fin D.p) (Fin D.p) ℂ)) (0 : Matrix (Fin D.p) (Fin D.q) ℂ) a m • P (x m)) = (Z true).z • tyPart ty τ (P (x (.inl a)))`. Introduce `a`. Rewrite using `[← CMValue.tyPart_smul]`. Use `congr 1`. Simplify using `[Fintype.sum_sum_type, Matrix.one_apply, ite_smul]`.

Establish `hB : ∀ n, tyPart ty (ComplexEmbedding.conjugate τ) (P (x n)) = ∑ j, Matrix.fromCols (0 : Matrix (Fin D.q) (Fin D.p) ℂ) ((Z false).z⁻¹ • (1 : Matrix (Fin D.q) (Fin D.q) ℂ)) j n • ((Z false).z • tyPart ty (ComplexEmbedding.conjugate τ) (P (x (.inr j))))`. Introduce `n`. Break down `n with a | k` into its components or cases. Simplify using `[hvan a]`. Simplify using `[Matrix.one_apply, ite_smul, smul_smul, hz₂]`.

Establish `hFm : ∀ j n, ∑ m, Matrix.fromCols (0 : Matrix (Fin D.q) (Fin D.p) ℂ) ((Z false).z⁻¹ • G⁻¹) j m * τ (sesq (FU.Di i) (x m) (x n)) = Matrix.fromCols (0 : Matrix (Fin D.q) (Fin D.p) ℂ) ((Z false).z⁻¹ • (1 : Matrix (Fin D.q) (Fin D.q) ℂ)) j n`. Introduce `j n`. Rewrite using `[Fintype.sum_sum_type]`. Break down `n with a | k` into its components or cases. Simplify using `[(orth a _).2]`.

Establish `h : ((Z false).z⁻¹ • G⁻¹) * G = (Z false).z⁻¹ • (1 : Matrix (Fin D.q) (Fin D.q) ℂ)`. Rewrite using `[Matrix.smul_mul, Matrix.nonsing_inv_mul _ hGu]`. Establish `h'` using `congrFun (congrFun h j) k`. Rewrite `h'` using `[Matrix.mul_apply]`. Simplify `h'` using `[G, gramE, RingHom.mapMatrix_apply]`.

Establish `key` using `hconst' P y' v' w' _ _ _ _ _ hP hy'u hF' hDV hDW hC hB hFm`. Establish `hnat : φ ℂ y' v' w' = f (φ X.K X.y v w)` using `hline.nat X.K ℂ f X.β X.y v w y' v' w' hF rfl hv' hw'`. Establish `hrows` using `CMValue.det_rows D.p D.q (Z true).z (Z false).z G hz₂ hG`. Use `⟨hF, ?_⟩` and prove the remaining obligations. Establish `hτT : τ T.det ≠ 0` using `(map_ne_zero τ).2 hTdet`.

Rewrite `key` using `[hnat]`. Express the relevant statement in the definitionally equal form `f (φ X.K X.y v w) * τ T.det * (Z true).z ^ D.p = _`. Rewrite using `[← hrows, ← hGdet]`. Establish `key' : f (φ X.K X.y v w) * (Matrix.fromRows (Matrix.fromCols ((Z true).z • (1 : Matrix (Fin D.p) (Fin D.p) ℂ)) (0 : Matrix (Fin D.p) (Fin D.q) ℂ)) (Matrix.fromCols (0 : Matrix (Fin D.q) (Fin D.p) ℂ) ((Z false).z⁻¹ • G⁻¹))).det * τ T.det = ρ`. Rewrite using `[key]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[← key']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem GlobalTheory.CompanionTheory.Ar.Fl.CMValue.value_on_cmFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (x : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (hx : IsPure hP x) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ) (T : Matrix (Fin D.p ⊕ Fin D.q) (Fin D.p ⊕ Fin D.q) E) (v : Vecs X.y D.p) (w : Vecs X.y D.q), IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 → (∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P → y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U) → IsLineFn U τ φ → LinearIndependent (𝓞 E) e → IsConstMul U τ φ FU i e ρ → LinearIndependent (𝓞 E) x → IsTransition (FU.Di i) x e T → X.IsCMFrame τ hx v w → IsFramed U τ X.β X.y v w ∧ ((φ X.K X.y v w : X.K) : ℂ) * τ T.det * (Z true).z ^ D.p = ρ * (Z false).z ^ D.q * τ (gramE (FU.Di i) (x ∘ Sum.inr)).det := by
  intro E _ _ _ H D l Xo c g ty FU i Z P hP X x hx U τ φ e ρ T v w hty hτ hmem hline he hconst hxi hT hfr
  have hfr0 := (GlobalTheory.T.cm_pack_pure_frame E H D l Xo c g ty FU i Z P hP X x hx τ hty hτ hxi).2 v w hfr
  let f : X.K →+* ℂ := algebraMap X.K ℂ
  have hcomp : f.comp X.β = algebraMap c.F ℂ := by ext a; rfl
  let y' : Sp ℂ ⟶ Xo.XF c := spMap f ≫ X.y
  have hyu : under y' = spMap f ≫ under X.y := Category.assoc _ _ _
  have hy'u : under y' = FU.u i P := hyu.trans X.pt
  have hy's : y' ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) := by
    rw [Category.assoc, X.hy, ← hcomp, spMap_comp]
  have hU : Set.range X.y ⊆ U := by
    rw [← CMValue.range_comp f X.y]
    exact hmem P y' hP hy'u hy's
  have hF : IsFramed U τ X.β X.y v w := ⟨hfr0.1, hU, hfr0.2.2⟩
  obtain ⟨⟨v', hv'⟩, hv⟩ := GlobalTheory.T.tangent_vectors_base_change E H Xo.X Xo.univ.t X.K ℂ f (under X.y) (under y')
    (X.β.comp (tauIn c τ)) D.p v hyu
  obtain ⟨⟨w', hw'⟩, hw⟩ := GlobalTheory.T.tangent_vectors_base_change E H Xo.X Xo.univ.t X.K ℂ f (under X.y) (under y')
    (X.β.comp (tauIn c (ComplexEmbedding.conjugate τ))) D.q w hyu
  have hF' : IsFramed U τ (algebraMap c.F ℂ) y' v' w' := by
    refine ⟨hy's, ?_, ?_, ?_⟩
    · rw [CMValue.range_comp f X.y]; exact hU
    · have := (hv v' hv').1 hF.2.2.1
      rwa [← RingHom.comp_assoc, hcomp] at this
    · have := (hw w' hw').1 hF.2.2.2
      rwa [← RingHom.comp_assoc, hcomp] at this
  have hz₂ : (Z false).z ≠ 0 := GlobalTheory.T.curve_z_ne_zero E H _ (Z false)
  have hcard : Fintype.card (Fin D.p ⊕ Fin D.q) = (FU.Di i).p + (FU.Di i).q := by
    simp [(FU.sig i).1, (FU.sig i).2]

  have hTdet : T.det ≠ 0 := by
    obtain ⟨T', hT', -, hT'det, -⟩ := GlobalTheory.T.exists_transition_matrix_gram E H (FU.Di i) (Fin D.p ⊕ Fin D.q) x e hcard he
    have hge := (GlobalTheory.T.gram_det_ne_zero_local_basis_cofinite E H (FU.Di i) (Fin D.p ⊕ Fin D.q) e hcard he).1
    have hmul : T * gramE (FU.Di i) e = T' * gramE (FU.Di i) e := by
      ext m n
      simp only [Matrix.mul_apply, gramE, Matrix.of_apply]
      rw [← hT m (e n), ← hT' m (e n)]
    have hTT : T = T' := by
      have hu : IsUnit (gramE (FU.Di i) e).det := isUnit_iff_ne_zero.2 hge
      rw [← Matrix.mul_nonsing_inv_cancel_right _ T hu, hmul, Matrix.mul_nonsing_inv_cancel_right _ T' hu]
    rw [hTT]
    exact hT'det hxi
  have hconst' := GlobalTheory.T.transition_matrix_period_frame E H D l Xo c g ty FU i U τ φ e x T ρ he hT hTdet hconst

  have orth : ∀ a j, sesq (FU.Di i) (x (.inl a)) (x (.inr j)) = 0 ∧ sesq (FU.Di i) (x (.inr j)) (x (.inl a)) = 0 :=
    fun a j => GlobalTheory.T.pure_type_lattices_orthogonal E H (FU.Di i) g ty P hP _ _ (hx.1 a) (hx.2 j)
  have hgram : gramE (FU.Di i) x =
      Matrix.fromBlocks (gramE (FU.Di i) (x ∘ Sum.inl)) 0 0 (gramE (FU.Di i) (x ∘ Sum.inr)) := by
    ext m n
    rcases m with a | j <;> rcases n with b | k
    · rfl
    · exact (orth a k).1
    · exact (orth b j).2
    · rfl
  have hG₀ : (gramE (FU.Di i) (x ∘ Sum.inr)).det ≠ 0 := by
    have h := (GlobalTheory.T.gram_det_ne_zero_local_basis_cofinite E H (FU.Di i) (Fin D.p ⊕ Fin D.q) x hcard hxi).1
    rw [hgram, Matrix.det_fromBlocks_zero₂₁] at h
    exact right_ne_zero_of_mul h
  let G : Matrix (Fin D.q) (Fin D.q) ℂ := τ.mapMatrix (gramE (FU.Di i) (x ∘ Sum.inr))
  have hGdet : G.det = τ (gramE (FU.Di i) (x ∘ Sum.inr)).det := (RingHom.map_det τ _).symm
  have hG : G.det ≠ 0 := by
    rw [hGdet]
    exact (map_ne_zero τ).2 hG₀
  have hGu : IsUnit G.det := isUnit_iff_ne_zero.2 hG

  have hDV : ∀ a, IsDerivAt0 (fun z => (FU.ex i P z).left)
      ((Z true).z • tyPart ty τ (P (x (.inl a)))) (v' a).left := by
    intro a
    rw [hv' a]
    exact GlobalTheory.T.cm_pack_eigen_period E H D l Xo c g ty FU i Z P hP X true τ ⟨x (.inl a), hx.1 a⟩ (v a) (hfr.1 a)
  have hDW : ∀ j, IsDerivAt0 (fun z => (FU.ex i P z).left)
      ((Z false).z • tyPart ty (ComplexEmbedding.conjugate τ) (P (x (.inr j)))) (w' j).left := by
    intro j
    rw [hw' j]
    exact GlobalTheory.T.cm_pack_eigen_period E H D l Xo c g ty FU i Z P hP X false (ComplexEmbedding.conjugate τ)
      ⟨x (.inr j), hx.2 j⟩ (w j) (hfr.2 j)
  have hvan : ∀ a, tyPart ty (ComplexEmbedding.conjugate τ) (P (x (.inl a))) = 0 := by
    intro a
    ext k
    by_cases hk : ty k = ComplexEmbedding.conjugate τ
    · have : P (x (.inl a)) k = 0 := by
        apply hx.1 a k
        rw [hk, ComplexEmbedding.conjugate_coe_eq, hτ]
        simpa [sgnRt] using CMValue.conj_cmHostRoot_ne_self H
      simp [tyPart, this]
    · simp [tyPart, hk]
  have hC : ∀ a, tyPart ty τ (∑ m, Matrix.fromCols ((Z true).z • (1 : Matrix (Fin D.p) (Fin D.p) ℂ))
      (0 : Matrix (Fin D.p) (Fin D.q) ℂ) a m • P (x m)) = (Z true).z • tyPart ty τ (P (x (.inl a))) := by
    intro a
    rw [← CMValue.tyPart_smul]
    congr 1
    simp [Fintype.sum_sum_type, Matrix.one_apply, ite_smul]
  have hB : ∀ n, tyPart ty (ComplexEmbedding.conjugate τ) (P (x n)) =
      ∑ j, Matrix.fromCols (0 : Matrix (Fin D.q) (Fin D.p) ℂ) ((Z false).z⁻¹ • (1 : Matrix (Fin D.q) (Fin D.q) ℂ)) j n •
        ((Z false).z • tyPart ty (ComplexEmbedding.conjugate τ) (P (x (.inr j)))) := by
    intro n
    rcases n with a | k
    · simp [hvan a]
    · simp [Matrix.one_apply, ite_smul, smul_smul, hz₂]
  have hFm : ∀ j n, ∑ m, Matrix.fromCols (0 : Matrix (Fin D.q) (Fin D.p) ℂ) ((Z false).z⁻¹ • G⁻¹) j m *
      τ (sesq (FU.Di i) (x m) (x n)) =
      Matrix.fromCols (0 : Matrix (Fin D.q) (Fin D.p) ℂ) ((Z false).z⁻¹ • (1 : Matrix (Fin D.q) (Fin D.q) ℂ)) j n := by
    intro j n
    rw [Fintype.sum_sum_type]
    rcases n with a | k
    · simp [(orth a _).2]
    · have h : ((Z false).z⁻¹ • G⁻¹) * G = (Z false).z⁻¹ • (1 : Matrix (Fin D.q) (Fin D.q) ℂ) := by
        rw [Matrix.smul_mul, Matrix.nonsing_inv_mul _ hGu]
      have h' := congrFun (congrFun h j) k
      rw [Matrix.mul_apply] at h'
      simpa [G, gramE, RingHom.mapMatrix_apply] using h'
  have key := hconst' P y' v' w' _ _ _ _ _ hP hy'u hF' hDV hDW hC hB hFm
  have hnat : φ ℂ y' v' w' = f (φ X.K X.y v w) := hline.nat X.K ℂ f X.β X.y v w y' v' w' hF rfl hv' hw'
  have hrows := CMValue.det_rows D.p D.q (Z true).z (Z false).z G hz₂ hG
  refine ⟨hF, ?_⟩
  have hτT : τ T.det ≠ 0 := (map_ne_zero τ).2 hTdet
  rw [hnat] at key
  change f (φ X.K X.y v w) * τ T.det * (Z true).z ^ D.p = _
  rw [← hrows, ← hGdet]
  have key' : f (φ X.K X.y v w) * (Matrix.fromRows (Matrix.fromCols ((Z true).z • (1 : Matrix (Fin D.p) (Fin D.p) ℂ))
      (0 : Matrix (Fin D.p) (Fin D.q) ℂ)) (Matrix.fromCols (0 : Matrix (Fin D.q) (Fin D.p) ℂ) ((Z false).z⁻¹ • G⁻¹))).det * τ T.det = ρ := by
    rw [key]
    field_simp
  rw [← key']
  ring
