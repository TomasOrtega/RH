import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CubeTrivialisationOnUniformisingSpace

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory.ThetaBundleSym

section Geometry

variable {X : Over (Sp ℂ)} [LocallyOfFiniteType X.hom] {Z : Type} {ex : Z → (𝟙_ (Over (Sp ℂ)) ⟶ X)}

/- English proof (translation)
Establish `: JacobsonSpace X.left` using `LocallyOfFiniteType.jacobsonSpace X.hom`. Introduce `y hy`. Assume the negation of the conclusion as `hyV`. Take `⟨x, ⟨hxU, hxV⟩, hx⟩` from `nonempty_inter_closedPoints (Z := (U : Set X.left) ∩ (V : Set X.left)ᶜ) ⟨y, hy, hyV⟩ (U.isOpen.isLocallyClosed.inter V.isOpen.isClosed_compl.isLocallyClosed)`. Set `p : 𝟙_ (Over (Sp ℂ)) ⟶ X` to `Over.homMk (pointOfClosedPoint X.hom x hx) (pointOfClosedPoint_comp X.hom x hx)`.

Take `⟨z, hz⟩` from `hex p`. Establish `hp : ∀ W : X.left.Opens, ⊤ ≤ (ex z).left ⁻¹ᵁ W ↔ x ∈ W`. Introduce `W`. Rewrite using `[hz]`. Use `(top_le_preimage_iff_mem (pointOfClosedPoint X.hom x hx) W).trans ?_` and prove the remaining obligations.

Conclude with `(pointOfClosedPoint_apply X.hom x hx _).symm ▸ Iff.rfl`. Conclude with `hxV ((hp V).1 (h z ((hp U).2 hxU)))`.
-/
theorem le_of_complex_points (hex : Function.Surjective ex) {U V : X.left.Opens}
    (h : ∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ U → ⊤ ≤ (ex z).left ⁻¹ᵁ V) : U ≤ V := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  intro y hy
  by_contra hyV
  obtain ⟨x, ⟨hxU, hxV⟩, hx⟩ := nonempty_inter_closedPoints (Z := (U : Set X.left) ∩ (V : Set X.left)ᶜ) ⟨y, hy, hyV⟩
    (U.isOpen.isLocallyClosed.inter V.isOpen.isClosed_compl.isLocallyClosed)
  let p : 𝟙_ (Over (Sp ℂ)) ⟶ X := Over.homMk (pointOfClosedPoint X.hom x hx) (pointOfClosedPoint_comp X.hom x hx)
  obtain ⟨z, hz⟩ := hex p
  have hp : ∀ W : X.left.Opens, ⊤ ≤ (ex z).left ⁻¹ᵁ W ↔ x ∈ W := by
    intro W
    rw [hz]
    refine (top_le_preimage_iff_mem (pointOfClosedPoint X.hom x hx) W).trans ?_
    exact (pointOfClosedPoint_apply X.hom x hx _).symm ▸ Iff.rfl
  exact hxV ((hp V).1 (h z ((hp U).2 hxU)))

/- English proof (translation)
Establish `hle : U ≤ X.left.basicOpen f` using `le_of_complex_points hex fun z hz => (top_le_preimage_basicOpen_iff _ U f).2 (h z hz)`. Conclude with `X.left.toRingedSpace.isUnit_of_isUnit_germ U f fun p hp => (X.left.mem_basicOpen f p hp).1 (hle hp)`.
-/
theorem isUnit_of_complex_points (hex : Function.Surjective ex) {U : X.left.Opens} (f : Γ(X.left, U))
    (h : ∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ U → valAt' (ex z).left U f ≠ 0) : IsUnit f := by
  have hle : U ≤ X.left.basicOpen f := le_of_complex_points hex fun z hz =>
    (top_le_preimage_basicOpen_iff _ U f).2 (h z hz)
  exact X.left.toRingedSpace.isUnit_of_isUnit_germ U f fun p hp =>
    (X.left.mem_basicOpen f p hp).1 (hle hp)

/- English proof (translation)
Use `choose W φ hφ using hv`. Establish `hle : ∀ i, M.U i ≤ W i` using `fun i => le_of_complex_points hex fun z hz => (hφ i z hz).1`. Establish `hval : ∀ i z, ⊤ ≤ (ex z).left ⁻¹ᵁ M.U i → valAt' (ex z).left (M.U i) (resG X.left (hle i) (φ i)) = v i z` using `fun i z hz => (valAt'_res _ (hle i) (φ i) hz).trans (hφ i z hz).2`. Use `⟨⟨fun i => resG X.left (hle i) (φ i), fun i j => hext _ _ _ fun x hx => ?_⟩, hval⟩` and prove the remaining obligations. Take `⟨z, rfl⟩` from `hex x`.

Take `⟨hi, hj⟩` from `(top_le_preimage_inf _ _ _).1 hx`. Rewrite using `[valAt'_mul, valAt'_map _ _ _ hx, valAt'_map _ _ _ hx, hval i z hi, hval j z hj, hc i j z hi hj]`.
-/
theorem exists_sec (hex : Function.Surjective ex)
    (hext : ∀ (U : X.left.Opens) (f f' : Γ(X.left, U)), (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U →
      valAt' x.left U f = valAt' x.left U f') → f = f')
    (M : LB X.left) (v : M.ι → Z → ℂ)
    (hv : ∀ i, ∃ (W : X.left.Opens) (φ : Γ(X.left, W)), ∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ M.U i →
      ⊤ ≤ (ex z).left ⁻¹ᵁ W ∧ valAt' (ex z).left W φ = v i z)
    (hc : ∀ i j z, ⊤ ≤ (ex z).left ⁻¹ᵁ M.U i → ⊤ ≤ (ex z).left ⁻¹ᵁ M.U j →
      v i z = valAt' (ex z).left (M.U i ⊓ M.U j) (M.g i j).val * v j z) :
    ∃ s : M.Sec, ∀ i z, ⊤ ≤ (ex z).left ⁻¹ᵁ M.U i → valAt' (ex z).left (M.U i) (s.f i) = v i z := by
  choose W φ hφ using hv
  have hle : ∀ i, M.U i ≤ W i := fun i => le_of_complex_points hex fun z hz => (hφ i z hz).1
  have hval : ∀ i z, ⊤ ≤ (ex z).left ⁻¹ᵁ M.U i →
      valAt' (ex z).left (M.U i) (resG X.left (hle i) (φ i)) = v i z := fun i z hz =>
    (valAt'_res _ (hle i) (φ i) hz).trans (hφ i z hz).2
  refine ⟨⟨fun i => resG X.left (hle i) (φ i), fun i j => hext _ _ _ fun x hx => ?_⟩, hval⟩
  obtain ⟨z, rfl⟩ := hex x
  obtain ⟨hi, hj⟩ := (top_le_preimage_inf _ _ _).1 hx
  rw [valAt'_mul, valAt'_map _ _ _ hx, valAt'_map _ _ _ hx, hval i z hi, hval j z hj, hc i j z hi hj]

/- English proof (translation)
Take `⟨s, hs⟩` from `exists_sec hex hext M v hv hc`. Establish `hu : ∀ i, IsUnit (s.f i)` using `fun i => isUnit_of_complex_points hex _ fun z hz => by`. Rewrite using `[hs i z hz]`. Conclude with `hne i z hz`. Use `⟨⟨fun i => (hu i).unit⟩, fun i j => Units.ext ?_⟩` and prove the remaining obligations.

Conclude with `s.compat i j`.
-/
theorem exists_gen (hex : Function.Surjective ex)
    (hext : ∀ (U : X.left.Opens) (f f' : Γ(X.left, U)), (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U →
      valAt' x.left U f = valAt' x.left U f') → f = f')
    (M : LB X.left) (v : M.ι → Z → ℂ)
    (hv : ∀ i, ∃ (W : X.left.Opens) (φ : Γ(X.left, W)), ∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ M.U i →
      ⊤ ≤ (ex z).left ⁻¹ᵁ W ∧ valAt' (ex z).left W φ = v i z)
    (hc : ∀ i j z, ⊤ ≤ (ex z).left ⁻¹ᵁ M.U i → ⊤ ≤ (ex z).left ⁻¹ᵁ M.U j →
      v i z = valAt' (ex z).left (M.U i ⊓ M.U j) (M.g i j).val * v j z)
    (hne : ∀ i z, ⊤ ≤ (ex z).left ⁻¹ᵁ M.U i → v i z ≠ 0) :
    ∃ t : M.Gen, t.IsGen := by
  obtain ⟨s, hs⟩ := exists_sec hex hext M v hv hc
  have hu : ∀ i, IsUnit (s.f i) := fun i => isUnit_of_complex_points hex _ fun z hz => by
    rw [hs i z hz]; exact hne i z hz
  refine ⟨⟨fun i => (hu i).unit⟩, fun i j => Units.ext ?_⟩
  exact s.compat i j

end Geometry

section Factors

variable {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ)

def basicFactor (n : Fin g → ℤ) (z : Fin g → ℂ) : ℂ :=
  eC (-(ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z))

def charFactor (a b : Fin g → ℝ) (n n' : Fin g → ℤ) : ℂ :=
  eC (ofRealVec a ⬝ᵥ ofIntVec n' - ofRealVec b ⬝ᵥ ofIntVec n)

/- English proof (translation)
Unfold `eC`. Rewrite using `[← Complex.exp_nat_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eC_nat_mul (k : ℕ) (x : ℂ) : eC (-(k : ℂ) * x) = eC (-x) ^ k := by
  unfold eC
  rw [← Complex.exp_nat_mul]
  congr 1; ring

/- English proof (translation)
Unfold `autFactor charFactor basicFactor`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem autFactor_eq (a b : Fin g → ℝ) (n n' : Fin g → ℤ) (z : Fin g → ℂ) :
    autFactor a b τ n n' z = charFactor a b n n' * basicFactor τ n z := by
  unfold autFactor charFactor basicFactor
  congr 2; ring

/- English proof (translation)
Unfold `basicFactor`. Simplify using `[ofIntVec_neg, Matrix.mulVec_neg]`.
-/
theorem basicFactor_neg (n : Fin g → ℤ) (z : Fin g → ℂ) : basicFactor τ (-n) (-z) = basicFactor τ n z := by
  unfold basicFactor
  simp [ofIntVec_neg, Matrix.mulVec_neg]

/- English proof (translation)
Use `⟨∑ i, if a i = 0 then 0 else n i, ?_⟩` and prove the remaining obligations. Simplify using `only [dotProduct, ofRealVec, ofIntVec, Finset.mul_sum]`. Use `push_cast`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Break down `ha i with h | h` into its components or cases.

Simplify using `[h]`. Rewrite using `[if_neg (by rw [h]; norm_num), h]; push_cast; ring`.
-/
theorem exists_int_two_mul {a : Fin g → ℝ} (ha : ∀ i, a i = 0 ∨ a i = 1 / 2) (n : Fin g → ℤ) :
    ∃ k : ℤ, 2 * (ofRealVec a ⬝ᵥ ofIntVec n) = k := by
  classical
  refine ⟨∑ i, if a i = 0 then 0 else n i, ?_⟩
  simp only [dotProduct, ofRealVec, ofIntVec, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases ha i with h | h
  · simp [h]
  · rw [if_neg (by rw [h]; norm_num), h]; push_cast; ring

/- English proof (translation)
Take `⟨k, hk⟩` from `exists_int_two_mul ha n'`. Take `⟨l, hl⟩` from `exists_int_two_mul hb n`. Rewrite using `[sq, charFactor, ← eC_add, ← eC_int (k - l)]`. Use `congr 1`. Use `push_cast`.

Rewrite using `[← hk, ← hl]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem charFactor_sq {a b : Fin g → ℝ} (ha : ∀ i, a i = 0 ∨ a i = 1 / 2) (hb : ∀ i, b i = 0 ∨ b i = 1 / 2)
    (n n' : Fin g → ℤ) : charFactor a b n n' ^ 2 = 1 := by
  obtain ⟨k, hk⟩ := exists_int_two_mul ha n'
  obtain ⟨l, hl⟩ := exists_int_two_mul hb n
  rw [sq, charFactor, ← eC_add, ← eC_int (k - l)]
  congr 1
  push_cast
  rw [← hk, ← hl]; ring

/- English proof (translation)
Establish `h1 : charFactor a b (-n) (-n') * charFactor a b n n' = 1`. Rewrite using `[charFactor, charFactor, ← eC_add, ← eC_zero]`. Use `congr 1`. Simplify using `[ofIntVec_neg]`. Establish `h2` using `charFactor_sq ha hb n n'`.

Take the linear combination `charFactor a b n n' * h1 - charFactor a b (-n) (-n') * h2`.
-/
theorem charFactor_neg {a b : Fin g → ℝ} (ha : ∀ i, a i = 0 ∨ a i = 1 / 2) (hb : ∀ i, b i = 0 ∨ b i = 1 / 2)
    (n n' : Fin g → ℤ) : charFactor a b (-n) (-n') = charFactor a b n n' := by
  have h1 : charFactor a b (-n) (-n') * charFactor a b n n' = 1 := by
    rw [charFactor, charFactor, ← eC_add, ← eC_zero]
    congr 1
    simp [ofIntVec_neg]
  have h2 := charFactor_sq ha hb n n'
  linear_combination charFactor a b n n' * h1 - charFactor a b (-n) (-n') * h2

def HasFactor (a b : Fin g → ℝ) (m k : ℕ) (f : (Fin g → ℂ) → ℂ) : Prop :=
  Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z,
    f (z + τ *ᵥ ofIntVec n + ofIntVec n') = charFactor a b n n' ^ m * basicFactor τ n z ^ k * f z

variable {τ} {a b : Fin g → ℝ}

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.1.mul h'.1, fun n n' z => by simp only [h.2, h'.2]; ring⟩`.
-/
theorem HasFactor.mul {m k m' k' : ℕ} {f f' : (Fin g → ℂ) → ℂ} (h : HasFactor τ a b m k f)
    (h' : HasFactor τ a b m' k' f') : HasFactor τ a b (m + m') (k + k') (fun z => f z * f' z) :=
  ⟨h.1.mul h'.1, fun n n' z => by simp only [h.2, h'.2]; ring⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.1.pow r, fun n n' z => by simp only [h.2]; rw [mul_pow, mul_pow, pow_mul, pow_mul]⟩`.
-/
theorem HasFactor.pow {m k : ℕ} {f : (Fin g → ℂ) → ℂ} (h : HasFactor τ a b m k f) (r : ℕ) :
    HasFactor τ a b (m * r) (k * r) (fun z => f z ^ r) :=
  ⟨h.1.pow r, fun n n' z => by simp only [h.2]; rw [mul_pow, mul_pow, pow_mul, pow_mul]⟩

/- English proof (translation)
Use `⟨h.1.comp (f := fun z : Fin g → ℂ => -z) (by fun_prop), fun n n' z => ?_⟩` and prove the remaining obligations. Use `h.2 (-n) (-n') (-z)` as an intermediate fact. Rewrite `this` using `[charFactor_neg ha hb, basicFactor_neg]`. Simplify using `only`. Rewrite using `[← this]`.

Use `congr 1`. Simplify using `only [ofIntVec_neg, Matrix.mulVec_neg]`. Normalize the expressions using the abelian group laws.
-/
theorem HasFactor.neg (ha : ∀ i, a i = 0 ∨ a i = 1 / 2) (hb : ∀ i, b i = 0 ∨ b i = 1 / 2)
    {m k : ℕ} {f : (Fin g → ℂ) → ℂ} (h : HasFactor τ a b m k f) : HasFactor τ a b m k (fun z => f (-z)) := by
  refine ⟨h.1.comp (f := fun z : Fin g → ℂ => -z) (by fun_prop), fun n n' z => ?_⟩
  have := h.2 (-n) (-n') (-z)
  rw [charFactor_neg ha hb, basicFactor_neg] at this
  simp only
  rw [← this]
  congr 1
  simp only [ofIntVec_neg, Matrix.mulVec_neg]
  abel

/- English proof (translation)
Use `⟨h.1, fun n n' z => ?_⟩` and prove the remaining obligations. Take `⟨r, rfl⟩` from `hm`. Rewrite using `[h.2, eC_nat_mul, ← two_mul, pow_mul, charFactor_sq ha hb, one_pow, _root_.one_mul, hl]`. Both sides reduce to the same expression.
-/
theorem HasFactor.level (ha : ∀ i, a i = 0 ∨ a i = 1 / 2) (hb : ∀ i, b i = 0 ∨ b i = 1 / 2)
    {m k : ℕ} {f : (Fin g → ℂ) → ℂ} (h : HasFactor τ a b m k f) (hm : Even m) (l : ℕ) (hl : k = l) :
    Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') =
      eC (-(l : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z := by
  refine ⟨h.1, fun n n' z => ?_⟩
  obtain ⟨r, rfl⟩ := hm
  rw [h.2, eC_nat_mul, ← two_mul, pow_mul, charFactor_sq ha hb, one_pow, _root_.one_mul, hl]
  rfl

/- English proof (translation)
Use `⟨?_, fun n n' z => ?_⟩` and prove the remaining obligations. Establish `h3` using `(h2 (Fin g) a b).comp (s := Set.univ) (f := fun z : Fin g → ℂ => (z, (fun i j => τ i j))) (by fun_prop) (fun z _ => h1 (Fin g) hτ)`. Conclude with `differentiableOn_univ.1 h3`. Simplify using `only [pow_one]`. Rewrite using `[thetaQuasiPeriod_holds _ a b z τ n n' hτ.1, autFactor_eq]`.
-/
theorem hasFactor_theta (h1 : SiegelSubDomainStatement) (h2 : ThetaHoloStatement) (hτ : τ ∈ SiegelH (Fin g)) :
    HasFactor τ a b 1 1 (fun z => theta a b z τ) := by
  refine ⟨?_, fun n n' z => ?_⟩
  · have h3 := (h2 (Fin g) a b).comp (s := Set.univ) (f := fun z : Fin g → ℂ => (z, (fun i j => τ i j)))
      (by fun_prop) (fun z _ => h1 (Fin g) hτ)
    exact differentiableOn_univ.1 h3
  · simp only [pow_one]
    rw [thetaQuasiPeriod_holds _ a b z τ n n' hτ.1, autFactor_eq]

end Factors

/- English proof (translation)
Introduce `hext hS hH g τ hτ N hN X ex D hX hrat hNe _ hadd a b ha hb L u hL hu`. Take `⟨hint, hprop, hex, -⟩` from `hX`. Take `⟨rfl, -, -, hfr⟩` from `hu`. Establish `hext'` using `hext X inferInstance inferInstance`. Take `⟨M, rfl⟩ : ∃ M, N = M + 1` from `⟨N - 1, by omega⟩`.

Use `choose h F hh hF hF' hU using hfr`. Establish `fh : ∀ i, HasFactor τ a b 0 (M + 1) (h i)` using `fun i => ⟨(hh i).1, fun n n' z => by`. Rewrite using `[(hh i).2, eC_nat_mul, pow_zero, _root_.one_mul]`. Use the proof step `rfl⟩`. Establish `fF : ∀ i, HasFactor τ a b 1 (M + 2) (F i)` using `fun i => ⟨hF i, fun n n' z => by`.

Rewrite using `[hF' i, eC_nat_mul, autFactor_eq]`. Express the relevant statement in the definitionally equal form `_ * basicFactor τ n z ^ (M + 1) * _ = _`. Use the proof step `ring⟩`. Use `⟨DVR.exists_gen_of_local (V := ℂ) L hL _ _, ?_, ?_⟩` and prove the remaining obligations. Introduce `s`.

Use `⟨⊤, trivial, ?_⟩` and prove the remaining obligations. Establish `hinv : ∀ z, (u.ex z).left ≫ (GrpObj.inv : X ⟶ X).left = (u.ex (-z)).left`. Introduce `z`. Establish `h0 : u.ex (-z) = (u.ex z)⁻¹`. Rewrite using `[eq_inv_iff_mul_eq_one, ← u.ex_add, neg_add_cancel]`.

Conclude with `CubeValues.ex_zero u`. Rewrite using `[h0, ← Over.comp_left]`. Both sides reduce to the same expression. Set `φ : Fin 2 → (X.left ⟶ X.left)` to `![(GrpObj.inv : X ⟶ X).left, 𝟙 _]`. Establish `hchart : ∀ (j : Fin 2 → L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.wchart φ j → ⊤ ≤ (u.ex (-z)).left ⁻¹ᵁ L.U (j 0) ∧ ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j 1)`.

Introduce `j z hz`. Use `(CubeValues.le_preimage_wchart (u.ex z).left L φ j).1 hz` as an intermediate fact. Use `⟨?_, this 1⟩` and prove the remaining obligations. Rewrite using `[← hinv]`. Conclude with `this 0`.

Take `⟨t, ht⟩` from `exists_gen hex hext' (L.LinComb φ ![1, -1]) (fun j z => u.fr (j 0) (-z) / u.fr (j 1) z) (fun j => by`. Take `⟨W, ψ, hψ⟩` from `hrat (M + 3) _ _ (((((fh (j 0)).neg ha hb).mul (fF (j 1))).mul (((fF (j 0)).neg ha hb).pow M)).level ha hb (by convert hNe using 1; ring) _ (by ring)) (((((fF (j 0)).neg ha hb).pow (M + 1)).mul (fh (j 1))).level ha hb (by convert hNe using 1; ring) _ (by ring))`. Use `⟨W, ψ, fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨h0, h1⟩` from `hchart j z hz`. Take `⟨a0, b0⟩` from `(hU (j 0) (-z)).1.1 h0`.

Take `⟨a1, b1⟩` from `(hU (j 1) z).1.1 h1`. Establish `hq : F (j 0) (-z) ^ (M + 1) * h (j 1) z ≠ 0` using `mul_ne_zero (pow_ne_zero _ b0) a1`. Use `⟨(hψ z).1.2 hq, ((hψ z).2 hq).trans ?_⟩` and prove the remaining obligations. Rewrite using `[(hU (j 0) (-z)).2, (hU (j 1) z).2]`. Clear the denominators using the available nonvanishing facts.

Use the proof step `ring)`. Use the proof step `(fun j j' z hz hz' => by`. Take `⟨h0, h1⟩` from `hchart j z hz`. Take `⟨h0', h1'⟩` from `hchart j' z hz'`. Establish `hv` using `CubeValues.val_linComb (u.ex z).left valAt'_rules L φ ![1, -1] j j' hz hz'`.

Rewrite `hv` using `[Fin.prod_univ_two]`. Establish `e0 : (u.ex z).left ≫ φ 0 = (u.ex (-z)).left` using `hinv z`. Establish `e1 : (u.ex z).left ≫ φ 1 = (u.ex z).left` using `Category.comp_id _`. Rewrite `hv` using `[e0, e1]`. Use `Eq.trans ?_ (congrArg (· * (u.fr (j' 0) (-z) / u.fr (j' 1) z)) hv).symm` and prove the remaining obligations.

Establish `c0` using `u.fr_compat (j 0) (j' 0) (-z) ((top_le_preimage_inf _ _ _).2 ⟨h0, h0'⟩)`. Establish `c1` using `u.fr_compat (j 1) (j' 1) z ((top_le_preimage_inf _ _ _).2 ⟨h1, h1'⟩)`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, _root_.zpow_neg]`. Rewrite using `[c0, c1, mul_div_mul_comm, div_eq_mul_inv])`. Use the proof step `(fun j z hz => div_ne_zero (u.fr_ne _ _ (hchart j z hz).1) (u.fr_ne _ _ (hchart j z hz).2))`.

Establish `hφ : (fun k => (X.hom ⁻¹ᵁ ⊤).ι ≫ φ k) = ![(X.hom ⁻¹ᵁ ⊤).ι ≫ (GrpObj.inv : X ⟶ X).left, (X.hom ⁻¹ᵁ ⊤).ι]`. Use function extensionality and compare the values at `k`. Use `fin_cases k`. Both sides reduce to the same expression. Conclude with `Category.comp_id _`.

Rewrite using `[← hφ]`. Conclude with `⟨_, DVR.pullGen_isGen_of_isGen φ _ t ht _⟩`. Establish `fθ : HasFactor τ a b 1 1 (fun z => theta a b z τ)` using `hasFactor_theta hS hH hτ`. Use `exists_sec hex hext' L (fun i z => theta a b z τ * u.fr i z) (fun i => ?_) (fun i j z hi hj => ?_)` and prove the remaining obligations. Take `⟨W, ψ, hψ⟩` from `hrat (M + 2) _ _ (((fθ.mul (fh i)).mul ((fF i).pow M)).level ha hb (by convert hNe using 1; ring) _ (by ring)) (((fF i).pow (M + 1)).level ha hb (by convert hNe using 1; ring) _ (by ring))`.

Use `⟨W, ψ, fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨a0, b0⟩` from `(hU i z).1.1 hz`. Establish `hq : F i z ^ (M + 1) ≠ 0` using `pow_ne_zero _ b0`. Use `⟨(hψ z).1.2 hq, ((hψ z).2 hq).trans ?_⟩` and prove the remaining obligations. Rewrite using `[(hU i z).2]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[u.fr_compat i j z ((top_le_preimage_inf _ _ _).2 ⟨hi, hj⟩)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rigidified_sym_section :
    (∀ (X : Over (Sp ℂ)), IsReduced X.left → LocallyOfFiniteType X.hom → ∀ (U : X.left.Opens) (f f' : Γ(X.left, U)), (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U → valAt' x.left U f = valAt' x.left U f') → f = f') → SiegelSubDomainStatement → ThetaHoloStatement → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (X : Over (Sp ℂ)) (ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (D : (Fin g → Fin N) → X.left.Opens), (IsIntegral X.left ∧ IsProper X.hom ∧ Function.Surjective ex ∧ (∀ z z', ex z = ex z' ↔ z - z' ∈ periodLattice τ) ∧ (∀ (U : (X).left.Opens) (f : Γ((X).left, U)), IsOpen {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (ex w).left U f) {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U}) ∧ (∀ c, IsAffineOpen (D c) ∧ ringKrullDim Γ(X.left, D c) ≤ g ∧ (∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ D c ↔ theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) ≠ 0) ∧ ∃ r : (Fin g → Fin N) → Γ(X.left, D c), (∀ c' z, theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) ≠ 0 → valAt' (ex z).left (D c) (r c') = theta (fun i => ((c' i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) / theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ f : Γ(X.left, D c), ∃ F : MvPolynomial (Fin g → Fin N) ℂ, f = MvPolynomial.eval₂ (RingHom.comp (X.hom.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) r F) ∧ (⨆ c, D c = ⊤)) → (∀ (d : ℕ) (p q : (Fin g → ℂ) → ℂ), (Differentiable ℂ p ∧ ∀ (n n' : Fin g → ℤ) z, p (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * p z) → (Differentiable ℂ q ∧ ∀ (n n' : Fin g → ℤ) z, q (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * q z) → ∃ (U : X.left.Opens) (φ : Γ(X.left, U)), ∀ z, (⊤ ≤ (ex z).left ⁻¹ᵁ U ↔ q z ≠ 0) ∧ (q z ≠ 0 → valAt' (ex z).left U φ = p z / q z)) → Even N → ∀ [GrpObj X], (∀ z w, ex (z + w) = ex z * ex w) → ∀ a b : Fin g → ℝ, (∀ i, a i = 0 ∨ a i = 1 / 2) → (∀ i, b i = 0 ∨ b i = 1 / 2) → ∀ (L : LB X.left) (u : HolUnif X L g), L.IsLB → (u.ex = ex ∧ (∀ z, z ∈ u.Λ ↔ z ∈ periodLattice τ) ∧ (∀ (n n' : Fin g → ℤ) i z, ⊤ ≤ (ex z).left ⁻¹ᵁ L.U i → u.fr i z = autFactor a b τ n n' z * u.fr i (z + τ *ᵥ ofIntVec n + ofIntVec n')) ∧ (∀ i, ∃ h F : (Fin g → ℂ) → ℂ, (Differentiable ℂ h ∧ ∀ (n n' : Fin g → ℤ) z, h (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * h z) ∧ Differentiable ℂ F ∧ (∀ (n n' : Fin g → ℤ) z, F (z + τ *ᵥ ofIntVec n + ofIntVec n') = autFactor a b τ n n' z * eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * F z) ∧ ∀ z, (⊤ ≤ (ex z).left ⁻¹ᵁ L.U i ↔ h z ≠ 0 ∧ F z ≠ 0) ∧ u.fr i z = h z / F z)) → Out.Rigidified X L ∧ Out.Sym X L ∧ ∃ th : L.Sec, u.IsFn th (fun z => theta a b z τ)) := by
  intro hext hS hH g τ hτ N hN X ex D hX hrat hNe _ hadd a b ha hb L u hL hu
  obtain ⟨hint, hprop, hex, -⟩ := hX
  obtain ⟨rfl, -, -, hfr⟩ := hu
  have hext' := hext X inferInstance inferInstance
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  choose h F hh hF hF' hU using hfr
  have fh : ∀ i, HasFactor τ a b 0 (M + 1) (h i) := fun i => ⟨(hh i).1, fun n n' z => by
    rw [(hh i).2, eC_nat_mul, pow_zero, _root_.one_mul]; rfl⟩
  have fF : ∀ i, HasFactor τ a b 1 (M + 2) (F i) := fun i => ⟨hF i, fun n n' z => by
    rw [hF' i, eC_nat_mul, autFactor_eq]
    change _ * basicFactor τ n z ^ (M + 1) * _ = _
    ring⟩
  refine ⟨DVR.exists_gen_of_local (V := ℂ) L hL _ _, ?_, ?_⟩
  · intro s
    refine ⟨⊤, trivial, ?_⟩
    have hinv : ∀ z, (u.ex z).left ≫ (GrpObj.inv : X ⟶ X).left = (u.ex (-z)).left := by
      intro z
      have h0 : u.ex (-z) = (u.ex z)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← u.ex_add, neg_add_cancel]
        exact CubeValues.ex_zero u
      rw [h0, ← Over.comp_left]
      rfl
    let φ : Fin 2 → (X.left ⟶ X.left) := ![(GrpObj.inv : X ⟶ X).left, 𝟙 _]
    have hchart : ∀ (j : Fin 2 → L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.wchart φ j →
        ⊤ ≤ (u.ex (-z)).left ⁻¹ᵁ L.U (j 0) ∧ ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j 1) := by
      intro j z hz
      have := (CubeValues.le_preimage_wchart (u.ex z).left L φ j).1 hz
      refine ⟨?_, this 1⟩
      rw [← hinv]
      exact this 0
    obtain ⟨t, ht⟩ := exists_gen hex hext' (L.LinComb φ ![1, -1])
      (fun j z => u.fr (j 0) (-z) / u.fr (j 1) z) (fun j => by
        obtain ⟨W, ψ, hψ⟩ := hrat (M + 3) _ _
          (((((fh (j 0)).neg ha hb).mul (fF (j 1))).mul (((fF (j 0)).neg ha hb).pow M)).level ha hb
            (by convert hNe using 1; ring) _ (by ring))
          (((((fF (j 0)).neg ha hb).pow (M + 1)).mul (fh (j 1))).level ha hb
            (by convert hNe using 1; ring) _ (by ring))
        refine ⟨W, ψ, fun z hz => ?_⟩
        obtain ⟨h0, h1⟩ := hchart j z hz
        obtain ⟨a0, b0⟩ := (hU (j 0) (-z)).1.1 h0
        obtain ⟨a1, b1⟩ := (hU (j 1) z).1.1 h1
        have hq : F (j 0) (-z) ^ (M + 1) * h (j 1) z ≠ 0 := mul_ne_zero (pow_ne_zero _ b0) a1
        refine ⟨(hψ z).1.2 hq, ((hψ z).2 hq).trans ?_⟩
        rw [(hU (j 0) (-z)).2, (hU (j 1) z).2]
        field_simp
        ring)
      (fun j j' z hz hz' => by
        obtain ⟨h0, h1⟩ := hchart j z hz
        obtain ⟨h0', h1'⟩ := hchart j' z hz'
        have hv := CubeValues.val_linComb (u.ex z).left valAt'_rules L φ ![1, -1] j j' hz hz'
        rw [Fin.prod_univ_two] at hv
        have e0 : (u.ex z).left ≫ φ 0 = (u.ex (-z)).left := hinv z
        have e1 : (u.ex z).left ≫ φ 1 = (u.ex z).left := Category.comp_id _
        rw [e0, e1] at hv
        refine Eq.trans ?_ (congrArg (· * (u.fr (j' 0) (-z) / u.fr (j' 1) z)) hv).symm
        have c0 := u.fr_compat (j 0) (j' 0) (-z) ((top_le_preimage_inf _ _ _).2 ⟨h0, h0'⟩)
        have c1 := u.fr_compat (j 1) (j' 1) z ((top_le_preimage_inf _ _ _).2 ⟨h1, h1'⟩)
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, _root_.zpow_neg]
        rw [c0, c1, mul_div_mul_comm, div_eq_mul_inv])
      (fun j z hz => div_ne_zero (u.fr_ne _ _ (hchart j z hz).1) (u.fr_ne _ _ (hchart j z hz).2))
    have hφ : (fun k => (X.hom ⁻¹ᵁ ⊤).ι ≫ φ k) =
        ![(X.hom ⁻¹ᵁ ⊤).ι ≫ (GrpObj.inv : X ⟶ X).left, (X.hom ⁻¹ᵁ ⊤).ι] := by
      funext k
      fin_cases k
      · rfl
      · exact Category.comp_id _
    rw [← hφ]
    exact ⟨_, DVR.pullGen_isGen_of_isGen φ _ t ht _⟩
  · have fθ : HasFactor τ a b 1 1 (fun z => theta a b z τ) := hasFactor_theta hS hH hτ
    refine exists_sec hex hext' L (fun i z => theta a b z τ * u.fr i z) (fun i => ?_) (fun i j z hi hj => ?_)
    · obtain ⟨W, ψ, hψ⟩ := hrat (M + 2) _ _
        (((fθ.mul (fh i)).mul ((fF i).pow M)).level ha hb (by convert hNe using 1; ring) _ (by ring))
        (((fF i).pow (M + 1)).level ha hb (by convert hNe using 1; ring) _ (by ring))
      refine ⟨W, ψ, fun z hz => ?_⟩
      obtain ⟨a0, b0⟩ := (hU i z).1.1 hz
      have hq : F i z ^ (M + 1) ≠ 0 := pow_ne_zero _ b0
      refine ⟨(hψ z).1.2 hq, ((hψ z).2 hq).trans ?_⟩
      rw [(hU i z).2]
      field_simp
      ring
    · rw [u.fr_compat i j z ((top_le_preimage_inf _ _ _).2 ⟨hi, hj⟩)]
      ring

end GlobalTheory.ThetaBundleSym
