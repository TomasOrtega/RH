import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryIsomOfIsometry
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeStableAlmostEverywhere
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyReal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductMeasureTransportStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsGramFiberMeasuresStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresContinuityStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresChangeOfFormStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleProjectionsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryActionEulerProductStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompactStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.SWIsom

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

/- English proof (translation)
Establish `key : ∀ (B : Matrix (Fin M) (Fin M) A) (u w : Fin M → A), hform s B u w = (s ∘ u) ⬝ᵥ (B.mulVec w)`. Introduce `B u w`. Simplify using `only [hform, dotProduct, Matrix.mulVec, Function.comp, Finset.mul_sum, mul_assoc]`. Establish `hs : s ∘ (G.mulVec x) = Matrix.vecMul (s ∘ x) (cT s G)`. Use extensionality with `i`.

Simplify using `only [Function.comp, Matrix.mulVec, Matrix.vecMul, dotProduct, cT, map_sum, map_mul, Matrix.transpose_apply, Matrix.map_apply]`. Conclude with `Finset.sum_congr rfl fun j _ => mul_comm _ _`. Rewrite using `[key, key, hs, ← Matrix.dotProduct_mulVec]`. Simplify using `only [Matrix.mulVec_mulVec, Matrix.mul_assoc]`.
-/
theorem hform_conj {A : Type} [CommRing A] {M : ℕ} (s : A →+* A) (J G : Matrix (Fin M) (Fin M) A)
    (x y : Fin M → A) :
    hform s (cT s G * J * G) x y = hform s J (G.mulVec x) (G.mulVec y) := by
  have key : ∀ (B : Matrix (Fin M) (Fin M) A) (u w : Fin M → A),
      hform s B u w = (s ∘ u) ⬝ᵥ (B.mulVec w) := by
    intro B u w
    simp only [hform, dotProduct, Matrix.mulVec, Function.comp, Finset.mul_sum, mul_assoc]
  have hs : s ∘ (G.mulVec x) = Matrix.vecMul (s ∘ x) (cT s G) := by
    ext i
    simp only [Function.comp, Matrix.mulVec, Matrix.vecMul, dotProduct, cT, map_sum, map_mul,
      Matrix.transpose_apply, Matrix.map_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [key, key, hs, ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

def ratAct {M n : ℕ} (g : Matrix (Fin M) (Fin M) E) (X : Fin n → Fin M → E) : Fin n → Fin M → E :=
  fun a => g.mulVec (X a)

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [gramE, hE, hform_conj, ratAct]`.
-/
theorem gramE_ratAct (σ : E →ₐ[F] E) {M n : ℕ} (J g : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → E) :
    gramE σ J (ratAct g X) = gramE σ (cT (σ : E →+* E) g * J * g) X := by
  ext a b
  simp only [gramE, hE, hform_conj, ratAct]

/- English proof (translation)
Use extensionality with `a i`. Simplify using `[ratAct, Matrix.mulVec_mulVec]`.
-/
theorem ratAct_mul {M n : ℕ} (g h : Matrix (Fin M) (Fin M) E) (X : Fin n → Fin M → E) :
    ratAct g (ratAct h X) = ratAct (g * h) X := by
  ext a i
  simp [ratAct, Matrix.mulVec_mulVec]

/- English proof (translation)
Use extensionality with `a i`. Simplify using `[ratAct]`.
-/
theorem ratAct_one {M n : ℕ} (X : Fin n → Fin M → E) :
    ratAct (1 : Matrix (Fin M) (Fin M) E) X = X := by
  ext a i
  simp [ratAct]

/- English proof (translation)
Use extensionality with `a i`. Establish `hG : ((bc (inclR R) g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = (g : Matrix (Fin M) (Fin M) E).map (inclR R)` using `rfl`. Simplify using `only [ratTup, ratAct, actTup, hG, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]`.
-/
theorem ratTup_ratAct (R : Type) [CommRing R] [Algebra F R] {M n : ℕ} (g : GL (Fin M) E)
    (X : Fin n → Fin M → E) :
    ratTup (F := F) R (ratAct (g : Matrix (Fin M) (Fin M) E) X) =
      actTup R (bc (inclR R) g) (ratTup (F := F) R X) := by
  ext a i
  have hG : ((bc (inclR R) g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
      (g : Matrix (Fin M) (Fin M) E).map (inclR R) := rfl
  simp only [ratTup, ratAct, actTup, hG, Matrix.mulVec, dotProduct, map_sum, map_mul,
    Matrix.map_apply]

/- English proof (translation)
Use extensionality with `a i`. Simplify using `[actTup, Matrix.mulVec_mulVec]`.
-/
theorem actTup_mul (R : Type) [CommRing R] [Algebra F R] {M n : ℕ}
    (g h : GL (Fin M) (R ⊗[F] E)) (X : Fin n → Fin M → R ⊗[F] E) :
    actTup R (g * h) X = actTup R g (actTup R h X) := by
  ext a i
  simp [actTup, Matrix.mulVec_mulVec]

/- English proof (translation)
Use extensionality with `a i`. Simplify using `[actTup]`.
-/
theorem actTup_one (R : Type) [CommRing R] [Algebra F R] {M n : ℕ}
    (X : Fin n → Fin M → R ⊗[F] E) : actTup R (1 : GL (Fin M) (R ⊗[F] E)) X = X := by
  ext a i
  simp [actTup]

/- English proof (translation)
Establish `hG : ∀ (S : Type) [CommRing S] [Algebra F S], ((bc (inclR S) g : GL (Fin M) (S ⊗[F] E)) : Matrix (Fin M) (Fin M) (S ⊗[F] E)) = (g : Matrix (Fin M) (Fin M) E).map (inclR S)` using `fun _ _ _ => rfl`. Simplify using `only [actTup, hG, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `congr 1`. Simplify using `[inclR]`.
-/
theorem map_actTup {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']
    (φ : R →ₐ[F] R') {M n : ℕ} (g : GL (Fin M) E) (X : Fin n → Fin M → R ⊗[F] E) (a : Fin n)
    (i : Fin M) :
    Algebra.TensorProduct.map φ (AlgHom.id F E) (actTup R (bc (inclR R) g) X a i) =
      actTup R' (bc (inclR R') g)
        (fun a i => Algebra.TensorProduct.map φ (AlgHom.id F E) (X a i)) a i := by
  have hG : ∀ (S : Type) [CommRing S] [Algebra F S],
      ((bc (inclR S) g : GL (Fin M) (S ⊗[F] E)) : Matrix (Fin M) (Fin M) (S ⊗[F] E)) =
      (g : Matrix (Fin M) (Fin M) E).map (inclR S) := fun _ _ _ => rfl
  simp only [actTup, hG, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  simp [inclR]

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[hCM.2.2.2, hCM.2.2.2, star_star]`.
-/
theorem sigma_sigma [NumberField E] [NumberField F] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (x : E) :
    σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hCM.2.2.2, hCM.2.2.2, star_star]

/- English proof (translation)
Establish `hJc : cT (σ : E →+* E) J = J`. Use extensionality with `i j`. Simplify `hJ.1 i j` using `[cT]`. Establish `hcc : cT (σ : E →+* E) (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E)) = g`. Use extensionality with `i j`.

Simplify using `[cT, sigma_sigma σ hCM]`. Prove the components needed by the constructor for the conclusion. Introduce `i j`. Establish `h` using `congrFun (congrFun (show cT (σ : E →+* E) (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E)) = cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E) by`. Rewrite using `[cT_mul, cT_mul, hJc, hcc, Matrix.mul_assoc]) i) j`.

Conclude with `h`. Establish `hdet : (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E)).det = σ (g : Matrix (Fin M) (Fin M) E).det`. Simplify using `only [cT, Matrix.det_transpose]`. Conclude with `(RingHom.map_det (σ : E →+* E) _).symm`. Establish `hg : (g : Matrix (Fin M) (Fin M) E).det ≠ 0`.

Use `(Matrix.isUnit_iff_isUnit_det _).1 g.isUnit` as an intermediate fact. Conclude with `this.ne_zero`. Rewrite using `[Matrix.det_mul, Matrix.det_mul, hdet]`. Conclude with `mul_ne_zero (mul_ne_zero (by simpa using hg) hJ.2) hg`.
-/
theorem isHermND_conj [NumberField E] [NumberField F] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (g : GL (Fin M) E) :
    IsHermND σ (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E)) := by
  have hJc : cT (σ : E →+* E) J = J := by
    ext i j
    simpa [cT] using hJ.1 i j
  have hcc : cT (σ : E →+* E) (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E)) = g := by
    ext i j
    simp [cT, sigma_sigma σ hCM]
  constructor
  · intro i j
    have h := congrFun (congrFun (show cT (σ : E →+* E)
      (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E)) =
        cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E) by
      rw [cT_mul, cT_mul, hJc, hcc, Matrix.mul_assoc]) i) j
    exact h
  · have hdet : (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E)).det =
        σ (g : Matrix (Fin M) (Fin M) E).det := by
      simp only [cT, Matrix.det_transpose]
      exact (RingHom.map_det (σ : E →+* E) _).symm
    have hg : (g : Matrix (Fin M) (Fin M) E).det ≠ 0 := by
      have := (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
      exact this.ne_zero
    rw [Matrix.det_mul, Matrix.det_mul, hdet]
    exact mul_ne_zero (mul_ne_zero (by simpa using hg) hJ.2) hg

end Alg

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Use `haveI : IsTopologicalRing (R ⊗[F] E) := (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM R).1`. Use `continuous_pi fun a => continuous_pi fun i => ?_` and prove the remaining obligations. Simplify using `only [actTup, Matrix.mulVec, dotProduct]`. Conclude with `continuous_finset_sum _ fun j _ => continuous_const.mul ((continuous_apply j).comp (continuous_apply a))`.
-/
theorem continuous_actTup (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R]
    [T2Space R] {M n : ℕ} (g : GL (Fin M) (R ⊗[F] E)) :
    Continuous (actTup R g : (Fin n → Fin M → R ⊗[F] E) → _) := by
  haveI : IsTopologicalRing (R ⊗[F] E) := (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM R).1
  refine continuous_pi fun a => continuous_pi fun i => ?_
  simp only [actTup, Matrix.mulVec, dotProduct]
  exact continuous_finset_sum _ fun j _ => continuous_const.mul
    ((continuous_apply j).comp (continuous_apply a))

/- English proof (translation)
Use `haveI : BorelSpace (Fin n → Fin M → R ⊗[F] E) := (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM R).2.2.2.2.2.2.2.1 n M`. Conclude with `(continuous_actTup σ hCM R g).measurable`.
-/
theorem measurable_actTup (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R]
    [T2Space R] {M n : ℕ} (g : GL (Fin M) (R ⊗[F] E)) :
    Measurable (actTup R g : (Fin n → Fin M → R ⊗[F] E) → _) := by
  haveI : BorelSpace (Fin n → Fin M → R ⊗[F] E) :=
    (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM R).2.2.2.2.2.2.2.1 n M
  exact (continuous_actTup σ hCM R g).measurable

end Loc

section Theta

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField F] [NumberField E] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_inv (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J) :
    HA.mat R σ J h⁻¹ = (HA.mat R σ J h)⁻¹ := rfl

omit [NumberField F] [NumberField E] in

/- English proof (translation)
Simplify using `only [actW, mat_inv, hmat]`. Rewrite using `[← actTup_mul, ← actTup_mul]`. Use `congr 1`. Use `group`.
-/
theorem act_conj (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M n : ℕ}
    {J J' : Matrix (Fin M) (Fin M) E} (G : GL (Fin M) (R ⊗[F] E)) (e : HA R σ J' → HA R σ J)
    (hmat : ∀ u, HA.mat R σ J (e u) = G * HA.mat R σ J' u * G⁻¹) (u : HA R σ J')
    (Y : Fin n → Fin M → R ⊗[F] E) :
    actTup R G (actW R σ J' u⁻¹ Y) = actW R σ J (e u)⁻¹ (actTup R G Y) := by
  simp only [actW, mat_inv, hmat]
  rw [← actTup_mul, ← actTup_mul]
  congr 1
  group

omit [NumberField F] [NumberField E] in
/- English proof (translation)
Use extensionality with `s hs`. Simplify using `only [Measure.sum_apply _ hs]`. Conclude with `e.tsum_eq (fun k => m k s)`.
-/
theorem sum_reindex {ι κ α : Type} [MeasurableSpace α] (e : ι ≃ κ) (m : κ → Measure α) :
    Measure.sum (fun i => m (e i)) = Measure.sum m := by
  ext s hs
  simp only [Measure.sum_apply _ hs]
  exact e.tsum_eq (fun k => m k s)

def gramEquiv (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (g : GL (Fin M) E)
    (T : Matrix (Fin n) (Fin n) E) :
    {X : Fin n → Fin M → E |
        gramE σ (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E)) X = T} ≃
      {X : Fin n → Fin M → E | gramE σ J X = T} where
  toFun X := ⟨ratAct (g : Matrix (Fin M) (Fin M) E) X.1, by
    have := X.2
    simp only [Set.mem_setOf_eq] at this ⊢
    rw [gramE_ratAct, this]⟩
  invFun Y := ⟨ratAct ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) Y.1, by
    have := Y.2
    simp only [Set.mem_setOf_eq] at this ⊢
    rw [← gramE_ratAct, ratAct_mul, Units.mul_inv, ratAct_one, this]⟩
  left_inv X := by
    apply Subtype.ext
    change ratAct _ (ratAct _ X.1) = X.1
    rw [ratAct_mul, Units.inv_mul, ratAct_one]
  right_inv Y := by
    apply Subtype.ext
    change ratAct _ (ratAct _ Y.1) = Y.1
    rw [ratAct_mul, Units.mul_inv, ratAct_one]

/- English proof (translation)
Establish `hJ'` using `isHermND_conj σ hCM J hJ g`. Take `⟨tg, -, -, -, bs, hact⟩` from `GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M J hJ (AF F)`. Take `⟨tg', -, -, -, bs', hact'⟩` from `GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M _ hJ' (AF F)`. Use `haveI := tg`. Use `haveI := tg'`.

Use `haveI := bs`. Use `haveI := bs'`. Use `haveI : BorelSpace (Fin n → Fin M → AF F ⊗[F] E) := (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)).2.2.2.2.2.2.2.1 n M`. Use `set G : GL (Fin M) (AF F ⊗[F] E) := bc (inclR (AF F)) g with hG`. Establish `hmG` using `measurable_actTup (n := n) σ hCM (AF F) G`.

Establish `hmf : ∀ Y : Fin n → Fin M → AF F ⊗[F] E, Measurable fun h : HA (AF F) σ J => actW (AF F) σ J h⁻¹ Y` using `fun Y => ((hact n).1.comp (continuous_inv.prodMk continuous_const)).measurable`. Establish `hmf' : ∀ Y : Fin n → Fin M → AF F ⊗[F] E, Measurable fun h : HA (AF F) σ _ => actW (AF F) σ _ h⁻¹ Y` using `fun Y => ((hact' n).1.comp (continuous_inv.prodMk continuous_const)).measurable`. Establish `hmass : (μ.map He.symm) (He ⁻¹' 𝓕) = μ 𝓕`. Rewrite using `[He.symm.map_apply]`. Use `congr 1`.

Use extensionality with `x`. Simplify using the standard rewrite rules. Establish `hrest : ((μ.map He.symm).restrict (He ⁻¹' 𝓕)).map He = μ.restrict 𝓕`. Rewrite using `[← He.restrict_map, Measure.map_map He.measurable He.symm.measurable]`. Simplify using the standard rewrite rules.

Unfold `thetaMeas`. Rewrite using `[Measure.map_smul, hmass]`. Use `congr 1`. Rewrite using `[Measure.map_sum hmG.aemeasurable, ← sum_reindex (gramEquiv σ J g T)]`. Use `congr 1`.

Use function extensionality and compare the values at `X`. Rewrite using `[Measure.map_map hmG (hmf' _)]`. Establish `hcomp : (actTup (AF F) G ∘ fun h => actW (AF F) σ _ h⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) = (fun h => actW (AF F) σ J h⁻¹ (ratTup (AF F) ((gramEquiv σ J g T X : _) : Fin n → Fin M → E))) ∘ He`. Use function extensionality and compare the values at `h`. Use `act_conj (AF F) σ G He hmat h (ratTup (AF F) (X : Fin n → Fin M → E))` as an intermediate fact.

Simplify using `only [Function.comp]`. Rewrite using `[this, ← ratTup_ratAct]`. Both sides reduce to the same expression. Rewrite using `[hcomp, ← Measure.map_map (hmf _) He.measurable, hrest]`.
-/
theorem theta_map (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (g : GL (Fin M) E)
    [LocallyCompactSpace (AF F)] [SecondCountableTopology (AF F)] [T2Space (AF F)]
    (He : HA (AF F) σ (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E)) ≃ᵐ
      HA (AF F) σ J)
    (hmat : ∀ u, HA.mat (AF F) σ J (He u) =
      bc (inclR (AF F)) g * HA.mat (AF F) σ _ u * (bc (inclR (AF F)) g)⁻¹)
    (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)) (T : Matrix (Fin n) (Fin n) E) :
    (thetaMeas σ _ (μ.map He.symm) (He ⁻¹' 𝓕)
      {X | gramE σ (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E)) X = T}).map
        (actTup (AF F) (bc (inclR (AF F)) g)) =
      thetaMeas σ J μ 𝓕 {X | gramE σ J X = T} := by
  have hJ' := isHermND_conj σ hCM J hJ g
  obtain ⟨tg, -, -, -, bs, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M J hJ (AF F)
  obtain ⟨tg', -, -, -, bs', hact'⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M _ hJ' (AF F)
  haveI := tg
  haveI := tg'
  haveI := bs
  haveI := bs'
  haveI : BorelSpace (Fin n → Fin M → AF F ⊗[F] E) :=
    (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)).2.2.2.2.2.2.2.1 n M
  set G : GL (Fin M) (AF F ⊗[F] E) := bc (inclR (AF F)) g with hG
  have hmG := measurable_actTup (n := n) σ hCM (AF F) G
  have hmf : ∀ Y : Fin n → Fin M → AF F ⊗[F] E,
      Measurable fun h : HA (AF F) σ J => actW (AF F) σ J h⁻¹ Y := fun Y =>
    ((hact n).1.comp (continuous_inv.prodMk continuous_const)).measurable
  have hmf' : ∀ Y : Fin n → Fin M → AF F ⊗[F] E,
      Measurable fun h : HA (AF F) σ _ => actW (AF F) σ _ h⁻¹ Y := fun Y =>
    ((hact' n).1.comp (continuous_inv.prodMk continuous_const)).measurable
  have hmass : (μ.map He.symm) (He ⁻¹' 𝓕) = μ 𝓕 := by
    rw [He.symm.map_apply]
    congr 1
    ext x
    simp
  have hrest : ((μ.map He.symm).restrict (He ⁻¹' 𝓕)).map He = μ.restrict 𝓕 := by
    rw [← He.restrict_map, Measure.map_map He.measurable He.symm.measurable]
    simp
  unfold thetaMeas
  rw [Measure.map_smul, hmass]
  congr 1
  rw [Measure.map_sum hmG.aemeasurable, ← sum_reindex (gramEquiv σ J g T)]
  congr 1
  funext X
  rw [Measure.map_map hmG (hmf' _)]
  have hcomp : (actTup (AF F) G ∘ fun h => actW (AF F) σ _ h⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) =
      (fun h => actW (AF F) σ J h⁻¹ (ratTup (AF F) ((gramEquiv σ J g T X : _) : Fin n → Fin M → E))) ∘ He := by
    funext h
    have := act_conj (AF F) σ G He hmat h (ratTup (AF F) (X : Fin n → Fin M → E))
    simp only [Function.comp]
    rw [this, ← ratTup_ratAct]
    rfl
  rw [hcomp, ← Measure.map_map (hmf _) He.measurable, hrest]

end Theta

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in

/- English proof (translation)
Establish `hmem : ∀ (J₀ : Matrix (Fin M) (Fin M) E) (x : HA (AF F) σ J₀), HA.mat (AF F) σ J₀ x ∈ HFin (AF F) σ J₀ → (show HR (AF F) σ J₀ from x) ∈ HFinIn (AF F) σ J₀` using `fun _ _ h => h`. Set `up : ∀ J₀ : Matrix (Fin M) (Fin M) E, HFinIn (AF F) σ J₀ → HA (AF F) σ J₀` to `fun _ γ => γ.1`. Establish `hup : ∀ (J₀ : Matrix (Fin M) (Fin M) E) (γ : HFinIn (AF F) σ J₀), HA.mat (AF F) σ J₀ (up J₀ γ) ∈ HFin (AF F) σ J₀` using `fun _ γ => γ.2`. Set `c : HFinIn (AF F) σ J → HFinIn (AF F) σ J'` to `fun γ => ⟨e.symm (up J γ), hmem J' _ ((hrat (e.symm (up J γ))).1 (by`. Rewrite using `[e.apply_symm_apply]`.

Conclude with `hup J γ))⟩`. Establish `hc : Function.Bijective c`. Prove the components needed by the constructor for the conclusion. Introduce `γ δ h`. Establish `h' : e.symm (up J γ) = e.symm (up J δ)` using `congrArg Subtype.val h`.

Conclude with `Subtype.ext (e.symm.injective h')`. Introduce `δ`. Use `⟨⟨e (up J' δ), hmem J _ ((hrat (up J' δ)).2 (hup J' δ))⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `e.symm_apply_apply (up J' δ)`.

Use `IsFundamentalDomain.preimage_of_equiv h𝓕 hq hc ?_` and prove the remaining obligations. Introduce `γ x`. Express the relevant statement in the definitionally equal form `e (e.symm (up J γ) * x) = up J γ * e x`. Rewrite using `[map_mul, e.apply_symm_apply]`.
-/
theorem isFD_pull (σ : E →ₐ[F] E) {M : ℕ} {J J' : Matrix (Fin M) (Fin M) E}
    (e : HA (AF F) σ J' ≃* HA (AF F) σ J)
    (hrat : ∀ u, HA.mat (AF F) σ J (e u) ∈ HFin (AF F) σ J ↔ HA.mat (AF F) σ J' u ∈ HFin (AF F) σ J')
    {μ : Measure (HA (AF F) σ J)} {μ' : Measure (HA (AF F) σ J')}
    (hq : Measure.QuasiMeasurePreserving e μ' μ) {𝓕 : Set (HA (AF F) σ J)}
    (h𝓕 : IsFDH F E σ M J μ 𝓕) : IsFDH F E σ M J' μ' (e ⁻¹' 𝓕) := by
  have hmem : ∀ (J₀ : Matrix (Fin M) (Fin M) E) (x : HA (AF F) σ J₀),
      HA.mat (AF F) σ J₀ x ∈ HFin (AF F) σ J₀ → (show HR (AF F) σ J₀ from x) ∈ HFinIn (AF F) σ J₀ :=
    fun _ _ h => h
  let up : ∀ J₀ : Matrix (Fin M) (Fin M) E, HFinIn (AF F) σ J₀ → HA (AF F) σ J₀ := fun _ γ => γ.1
  have hup : ∀ (J₀ : Matrix (Fin M) (Fin M) E) (γ : HFinIn (AF F) σ J₀),
      HA.mat (AF F) σ J₀ (up J₀ γ) ∈ HFin (AF F) σ J₀ := fun _ γ => γ.2
  let c : HFinIn (AF F) σ J → HFinIn (AF F) σ J' := fun γ =>
    ⟨e.symm (up J γ), hmem J' _ ((hrat (e.symm (up J γ))).1 (by
      rw [e.apply_symm_apply]
      exact hup J γ))⟩
  have hc : Function.Bijective c := by
    constructor
    · intro γ δ h
      have h' : e.symm (up J γ) = e.symm (up J δ) := congrArg Subtype.val h
      exact Subtype.ext (e.symm.injective h')
    · intro δ
      refine ⟨⟨e (up J' δ), hmem J _ ((hrat (up J' δ)).2 (hup J' δ))⟩, ?_⟩
      apply Subtype.ext
      exact e.symm_apply_apply (up J' δ)
  refine IsFundamentalDomain.preimage_of_equiv h𝓕 hq hc ?_
  intro γ x
  change e (e.symm (up J γ) * x) = up J γ * e x
  rw [map_mul, e.apply_symm_apply]

/- English proof (translation)
The claim follows from `GlobalTheory.T.gram_fiber_measures_change_of_form F E σ hCM M J hJ _ (isHermND_conj σ hCM J hJ g) R hR n μ ν m hμ hν hm μ m' hμ hm' (bc (inclR R) g) (GlobalTheory.CompanionTheory.SW.HIsom.JR_conj R σ J g) a ha S`.
-/
theorem local_map (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (g : GL (Fin M) E) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [MeasurableSpace R] [BorelSpace R] (hR : IsLocR R) (n : ℕ)
    (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n))
    (hμ : μ.IsAddHaarMeasure) (hν : ν.IsAddHaarMeasure)
    (m m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
    (hm : IsGramFib R σ J n μ ν m)
    (hm' : IsGramFib R σ (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E)) n μ ν m')
    (a : ℝ≥0) (ha : μ.map (actTup R (bc (inclR R) g)) = a • μ) (S : HermR R σ n) :
    (m' S).map (actTup R (bc (inclR R) g)) = a • m S :=
  GlobalTheory.T.gram_fiber_measures_change_of_form F E σ hCM M J hJ _ (isHermND_conj σ hCM J hJ g) R hR n μ ν m hμ hν hm μ m' hμ hm'
    (bc (inclR R) g) (GlobalTheory.CompanionTheory.SW.HIsom.JR_conj R σ J g) a ha S

/- English proof (translation)
Take `⟨r1, r2, r3, r4, -⟩` from `hR`. Use `haveI := r1`. Use `haveI := r2`. Use `haveI := r3`. Use `haveI := r4`.

Establish `h` using `GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM R d b lam hlam`. Conclude with `⟨h.2.1 n M, h.2.2 n⟩`.
-/
theorem haar_of_loc (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (hR : IsLocR R) {d : ℕ}
    (b : Module.Basis (Fin d) F E) (lam : Measure R) (hlam : lam.IsAddHaarMeasure) (n M : ℕ) :
    (coordW R b lam n M).IsAddHaarMeasure ∧ (coordHerm R σ b lam n).IsAddHaarMeasure := by
  obtain ⟨r1, r2, r3, r4, -⟩ := hR
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  have h := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM R d b lam hlam
  exact ⟨h.2.1 n M, h.2.2 n⟩

/- English proof (translation)
Take `⟨r1, r2, r3, r4, -⟩` from `hR`. Use `haveI := r1`. Use `haveI := r2`. Use `haveI := r3`. Use `haveI := r4`.

Conclude with `measurable_actTup σ hCM R g`.
-/
theorem measurable_of_loc (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] (hR : IsLocR R) {M n : ℕ} (g : GL (Fin M) (R ⊗[F] E)) :
    Measurable (actTup R g : (Fin n → Fin M → R ⊗[F] E) → _) := by
  obtain ⟨r1, r2, r3, r4, -⟩ := hR
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  exact measurable_actTup σ hCM R g

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ g J' hJ'eq n T hT _ hSW`. Substitute `hJ'eq` using the available equality. Establish `hJ'` using `isHermND_conj σ hCM J hJ g`. Introduce `d b laminf lam hinf hlam μ 𝓕 hμ h𝓕 minf m hminf hm`. Take `⟨⟨i1, i2, i3⟩, -⟩` from `GlobalTheory.CompanionTheory.AdeleTop.adele_top F`.

Use `haveI := i1`. Use `haveI := i2`. Use `haveI := i3`. Apply the tactic sequence `obtain ⟨e, hmat, hrat⟩ := GlobalTheory.CompanionTheory.SW.HIsom.unitaryIsom_of_isometry F E σ hCM M J hJ g _ rfl (AF F)`. Take `⟨tg, -, -, -, bs, -⟩` from `GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M J hJ (AF F)`.

Take `⟨tg', -, -, -, bs', -⟩` from `GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M _ hJ' (AF F)`. Use `haveI := tg`. Use `haveI := tg'`. Use `haveI := bs`. Use `haveI := bs'`.

Use `haveI : μ.IsHaarMeasure := hμ`. Set `He` to `e.toHomeomorph.toMeasurableEquiv`. Establish `hμ' : IsHaarH F E σ M _ (μ.map He.symm)` using `ContinuousMulEquiv.isHaarMeasure_map μ e.symm`. Establish `hmm : (μ.map He.symm).map He = μ`. Rewrite using `[Measure.map_map He.measurable He.symm.measurable]`.

Simplify using the standard rewrite rules. Establish `hq : Measure.QuasiMeasurePreserving e (μ.map He.symm) μ` using `(MeasurePreserving.mk He.measurable hmm).quasiMeasurePreserving`. Establish `h𝓕' : IsFDH F E σ M _ (μ.map He.symm) (He ⁻¹' 𝓕)` using `isFD_pull σ e.toMulEquiv hrat hq h𝓕`. Establish `hLi : IsLocR (Ainf F)` using `GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hCM.1`. Establish `hLv : ∀ v, IsLocR (Fv F v)` using `fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v`.

Use `haveI : BorelSpace (Ainf F) := ⟨rfl⟩`. Use `haveI : ∀ v, BorelSpace (Fv F v) := fun _ => ⟨rfl⟩`. Establish `hWi` using `haar_of_loc σ hCM (Ainf F) hLi b laminf hinf.1 n M`. Establish `hWv` using `fun v => haar_of_loc σ hCM (Fv F v) (hLv v) b (lam v) (hlam v).1 n M`. Take `⟨minf', hminf'⟩` from `GlobalTheory.T.exists_gram_fiber_measures F E σ hCM M _ hJ' (Ainf F) hLi n _ _ hWi.1 hWi.2`.

Use `choose m' hm' using fun v => GlobalTheory.T.exists_gram_fiber_measures F E σ hCM M _ hJ' (Fv F v) (hLv v) n _ _ (hWv v).1 (hWv v).2`. Take `⟨cinf, c, hUP, hci, hcv⟩` from `GlobalTheory.T.haar_modulus_gl_action_product_formula F E σ hCM n M g`. Establish `hEul` using `hSW d b laminf lam hinf hlam (μ.map He.symm) (He ⁻¹' 𝓕) hμ' h𝓕' minf' m' hminf' hm'`. Establish `hfin : ∀ v, m v (hermOf (Fv F v) σ T hT) (latV b v) < ⊤`. Introduce `v`.

Use `haveI := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hCM M J hJ (Fv F v) (hLv v) n _ _ (m v) (hWv v).1 (hWv v).2 (hm v) (hermOf (Fv F v) σ T hT)).1`. Conclude with `((GlobalTheory.T.adelic_tuple_projections F E σ hCM d b n M).2.2.2.1 v).1.measure_lt_top`. Establish `hproj : ∀ X : Fin n → Fin M → AF F ⊗[F] E, projInf (actTup (AF F) (bc (inclR (AF F)) g) X) = actTup (Ainf F) (bc (inclR (Ainf F)) g) (projInf X) ∧ ∀ v, projV v (projFin (actTup (AF F) (bc (inclR (AF F)) g) X)) = actTup (Fv F v) (bc (inclR (Fv F v)) g) (projV v (projFin X))`. Introduce `X`. Use `⟨?_, fun v => ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `a i`. Conclude with `map_actTup (fstA F) g X a i`. Establish `h1 : projFin (actTup (AF F) (bc (inclR (AF F)) g) X) = actTup (Af F) (bc (inclR (Af F)) g) (projFin X)`. Use function extensionality and compare the values at `a i`. Conclude with `map_actTup (sndA F) g X a i`.

Rewrite using `[h1]`. Use function extensionality and compare the values at `a i`. Conclude with `map_actTup (evalV F v) g (projFin X) a i`. Establish `key` using `GlobalTheory.T.euler_product_measure_transport F E σ hCM d b n M _ (minf' (hermOf (Ainf F) σ T hT)) (minf (hermOf (Ainf F) σ T hT)) (fun v => m' v (hermOf (Fv F v) σ T hT)) (fun v => m v (hermOf (Fv F v) σ T hT)) (actTup (AF F) (bc (inclR (AF F)) g)) (actTup (Ainf F) (bc (inclR ( …`. Establish `hth` using `theta_map (n := n) σ hCM J hJ g He hmat μ 𝓕 T`.

Rewrite `key` using `[hth]`. Conclude with `key`.
-/
theorem swMeas_of_isometry : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (g : GL (Fin M) E) (J' : Matrix (Fin M) (Fin M) E), J' = cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * g → ∀ n : ℕ, ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → SWMeas σ J' T hT → SWMeas σ J T hT := by
  intro F E _ _ _ _ _ σ hCM M J hJ g J' hJ'eq n T hT _ hSW
  subst hJ'eq
  have hJ' := isHermND_conj σ hCM J hJ g
  intro d b laminf lam hinf hlam μ 𝓕 hμ h𝓕 minf m hminf hm
  obtain ⟨⟨i1, i2, i3⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := i1
  haveI := i2
  haveI := i3
  obtain ⟨e, hmat, hrat⟩ := GlobalTheory.CompanionTheory.SW.HIsom.unitaryIsom_of_isometry F E σ hCM M J hJ g _ rfl (AF F)
  obtain ⟨tg, -, -, -, bs, -⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M J hJ (AF F)
  obtain ⟨tg', -, -, -, bs', -⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M _ hJ' (AF F)
  haveI := tg
  haveI := tg'
  haveI := bs
  haveI := bs'
  haveI : μ.IsHaarMeasure := hμ
  let He := e.toHomeomorph.toMeasurableEquiv
  have hμ' : IsHaarH F E σ M _ (μ.map He.symm) := ContinuousMulEquiv.isHaarMeasure_map μ e.symm
  have hmm : (μ.map He.symm).map He = μ := by
    rw [Measure.map_map He.measurable He.symm.measurable]
    simp
  have hq : Measure.QuasiMeasurePreserving e (μ.map He.symm) μ :=
    (MeasurePreserving.mk He.measurable hmm).quasiMeasurePreserving
  have h𝓕' : IsFDH F E σ M _ (μ.map He.symm) (He ⁻¹' 𝓕) :=
    isFD_pull σ e.toMulEquiv hrat hq h𝓕

  have hLi : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hCM.1
  have hLv : ∀ v, IsLocR (Fv F v) := fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : ∀ v, BorelSpace (Fv F v) := fun _ => ⟨rfl⟩
  have hWi := haar_of_loc σ hCM (Ainf F) hLi b laminf hinf.1 n M
  have hWv := fun v => haar_of_loc σ hCM (Fv F v) (hLv v) b (lam v) (hlam v).1 n M
  obtain ⟨minf', hminf'⟩ := GlobalTheory.T.exists_gram_fiber_measures F E σ hCM M _ hJ' (Ainf F) hLi n _ _ hWi.1 hWi.2
  choose m' hm' using fun v =>
    GlobalTheory.T.exists_gram_fiber_measures F E σ hCM M _ hJ' (Fv F v) (hLv v) n _ _ (hWv v).1 (hWv v).2
  obtain ⟨cinf, c, hUP, hci, hcv⟩ := GlobalTheory.T.haar_modulus_gl_action_product_formula F E σ hCM n M g
  have hEul := hSW d b laminf lam hinf hlam (μ.map He.symm) (He ⁻¹' 𝓕) hμ' h𝓕' minf' m' hminf' hm'
  have hfin : ∀ v, m v (hermOf (Fv F v) σ T hT) (latV b v) < ⊤ := by
    intro v
    haveI := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hCM M J hJ (Fv F v) (hLv v) n _ _ (m v) (hWv v).1 (hWv v).2 (hm v)
      (hermOf (Fv F v) σ T hT)).1
    exact ((GlobalTheory.T.adelic_tuple_projections F E σ hCM d b n M).2.2.2.1 v).1.measure_lt_top
  have hproj : ∀ X : Fin n → Fin M → AF F ⊗[F] E,
      projInf (actTup (AF F) (bc (inclR (AF F)) g) X) =
          actTup (Ainf F) (bc (inclR (Ainf F)) g) (projInf X) ∧
        ∀ v, projV v (projFin (actTup (AF F) (bc (inclR (AF F)) g) X)) =
          actTup (Fv F v) (bc (inclR (Fv F v)) g) (projV v (projFin X)) := by
    intro X
    refine ⟨?_, fun v => ?_⟩
    · funext a i
      exact map_actTup (fstA F) g X a i
    · have h1 : projFin (actTup (AF F) (bc (inclR (AF F)) g) X) =
          actTup (Af F) (bc (inclR (Af F)) g) (projFin X) := by
        funext a i
        exact map_actTup (sndA F) g X a i
      rw [h1]
      funext a i
      exact map_actTup (evalV F v) g (projFin X) a i
  have key := GlobalTheory.T.euler_product_measure_transport F E σ hCM d b n M _ (minf' (hermOf (Ainf F) σ T hT))
    (minf (hermOf (Ainf F) σ T hT)) (fun v => m' v (hermOf (Fv F v) σ T hT))
    (fun v => m v (hermOf (Fv F v) σ T hT)) (actTup (AF F) (bc (inclR (AF F)) g))
    (actTup (Ainf F) (bc (inclR (Ainf F)) g)) (fun v => actTup (Fv F v) (bc (inclR (Fv F v)) g))
    (measurable_actTup σ hCM (AF F) _) (measurable_of_loc σ hCM (Ainf F) hLi _)
    (fun v => measurable_of_loc σ hCM (Fv F v) (hLv v) _) hproj
    ((GlobalTheory.CompanionTheory.SW.LatRat.latV_rational F E σ hCM d b n M).2.1 g) cinf c hUP
    (local_map σ hCM J hJ g (Ainf F) hLi n _ _ hWi.1 hWi.2 minf minf' hminf hminf' cinf
      (hci _ hWi.1) _)
    (fun v => local_map σ hCM J hJ g (Fv F v) (hLv v) n _ _ (hWv v).1 (hWv v).2 (m v) (m' v) (hm v)
      (hm' v) (c v) (hcv v _ (hWv v).1) _) hfin hEul
  have hth := theta_map (n := n) σ hCM J hJ g He hmat μ 𝓕 T
  rw [hth] at key
  exact key

end Main

end GlobalTheory.CompanionTheory.SW.SWIsom
