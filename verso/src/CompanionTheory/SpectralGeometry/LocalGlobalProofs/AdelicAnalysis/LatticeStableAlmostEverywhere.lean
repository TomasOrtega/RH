import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.LatRat

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

/- English proof (translation)
Establish `h` using `HeightOneSpectrum.Support.finite (𝓞 F) x`. Use `filter_upwards [h.compl_mem_cofinite] with v hv`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Establish `h2 : Valued.v (algebraMap F (Fv F v) x) = v.valuation F x` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x`. Rewrite using `[h2]`.

Conclude with `not_lt.mp hv`.
-/
theorem eventually_integral (x : F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F := by
  have h := HeightOneSpectrum.Support.finite (𝓞 F) x
  filter_upwards [h.compl_mem_cofinite] with v hv
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h2 : Valued.v (algebraMap F (Fv F v) x) = v.valuation F x :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  rw [h2]
  exact not_lt.mp hv

def latR {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) : Set (Fv F v ⊗[F] E) :=
  {y | ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F}

def Good {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (e : E) : Prop :=
  ∀ k l, algebraMap F (Fv F v) (b.repr (b k * e) l) ∈ v.adicCompletionIntegers F

/- English proof (translation)
Use `conv_lhs => rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr y]`. Rewrite using `[Finset.sum_mul, map_sum, Finsupp.finsetSum_apply]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_assoc, map_smul, Finsupp.smul_apply, smul_eq_mul]`. Use `congr 1`.

Simplify using `[inclR, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.basis_repr_tmul]`.
-/
theorem repr_mul {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (e : E)
    (y : Fv F v ⊗[F] E) (l : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) b).repr (y * inclR (Fv F v) e) l =
      ∑ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k *
        algebraMap F (Fv F v) (b.repr (b k * e) l) := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr y]
  rw [Finset.sum_mul, map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_mul_assoc, map_smul, Finsupp.smul_apply, smul_eq_mul]
  congr 1
  simp [inclR, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.basis_repr_tmul]

/- English proof (translation)
Introduce `l`. Rewrite using `[repr_mul]`. Conclude with `sum_mem fun k _ => mul_mem (hy k) (he k l)`.
-/
theorem mul_mem_latR {d : ℕ} {b : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {e : E}
    (he : Good b v e) {y : Fv F v ⊗[F] E} (hy : y ∈ latR b v) : y * inclR (Fv F v) e ∈ latR b v := by
  intro l
  rw [repr_mul]
  exact sum_mem fun k _ => mul_mem (hy k) (he k l)

/- English proof (translation)
Introduce `k`. Rewrite using `[map_sum, Finsupp.finsetSum_apply]`. Conclude with `sum_mem fun c hc => h c hc k`.
-/
theorem sum_mem_latR {d : ℕ} {b : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {ι : Type}
    (s : Finset ι) (f : ι → Fv F v ⊗[F] E) (h : ∀ c ∈ s, f c ∈ latR b v) : ∑ c ∈ s, f c ∈ latR b v := by
  intro k
  rw [map_sum, Finsupp.finsetSum_apply]
  exact sum_mem fun c hc => h c hc k

/- English proof (translation)
The claim follows from `Filter.eventually_all.2 fun _ => Filter.eventually_all.2 fun _ => eventually_integral _`.
-/
theorem eventually_good {d : ℕ} (b : Module.Basis (Fin d) F E) (e : E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, Good b v e :=
  Filter.eventually_all.2 fun _ => Filter.eventually_all.2 fun _ => eventually_integral _

/- English proof (translation)
The claim follows from `Filter.eventually_all.2 fun _ => Filter.eventually_all.2 fun _ => eventually_good b _`.
-/
theorem eventually_good_matrix {d m : ℕ} (b : Module.Basis (Fin d) F E) (g : Matrix (Fin m) (Fin m) E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i j, Good b v (g i j) :=
  Filter.eventually_all.2 fun _ => Filter.eventually_all.2 fun _ => eventually_good b _

omit [NumberField F] in
/- English proof (translation)
Use function extensionality and compare the values at `a i`. Simplify using `only [rmul, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]`. Conclude with `Finset.sum_comm`.
-/
theorem rmul_rmul (R : Type) [CommRing R] [Algebra F R] {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E)
    (A B : Matrix (Fin n) (Fin n) (R ⊗[F] E)) : rmul R (rmul R X A) B = rmul R X (A * B) := by
  funext a i
  simp only [rmul, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

omit [NumberField F] in
/- English proof (translation)
Use function extensionality and compare the values at `a i`. Simplify using `[rmul, Matrix.one_apply]`.
-/
theorem rmul_one (R : Type) [CommRing R] [Algebra F R] {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) :
    rmul R X 1 = X := by
  funext a i
  simp [rmul, Matrix.one_apply]

/- English proof (translation)
Introduce `a i`. Conclude with `sum_mem_latR _ _ (fun c _ => mul_mem_latR (hg c a) (fun k => hX c i k))`.
-/
theorem rmul_mem {d M n : ℕ} {b : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    {g : Matrix (Fin n) (Fin n) E} (hg : ∀ i j, Good b v (g i j))
    {X : Fin n → Fin M → Fv F v ⊗[F] E} (hX : X ∈ latV b v) :
    rmul (Fv F v) X (g.map (inclR (Fv F v))) ∈ latV b v := by
  intro a i
  exact sum_mem_latR _ _ (fun c _ => mul_mem_latR (hg c a) (fun k => hX c i k))

/- English proof (translation)
Introduce `a i`. Establish `h : actTup (Fv F v) (bc (inclR (Fv F v)) g) X a i = ∑ j, X a j * inclR (Fv F v) ((g : Matrix (Fin M) (Fin M) E) i j)`. Simplify using `only [actTup, Matrix.mulVec, dotProduct]`. Conclude with `Finset.sum_congr rfl fun j _ => mul_comm _ _`. Rewrite using `[h]`.

Conclude with `sum_mem_latR _ _ (fun j _ => mul_mem_latR (hg i j) (fun k => hX a j k))`.
-/
theorem actTup_mem {d M n : ℕ} {b : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    {g : GL (Fin M) E} (hg : ∀ i j, Good b v ((g : Matrix (Fin M) (Fin M) E) i j))
    {X : Fin n → Fin M → Fv F v ⊗[F] E} (hX : X ∈ latV b v) :
    actTup (Fv F v) (bc (inclR (Fv F v)) g) X ∈ latV b v := by
  intro a i
  have h : actTup (Fv F v) (bc (inclR (Fv F v)) g) X a i =
      ∑ j, X a j * inclR (Fv F v) ((g : Matrix (Fin M) (Fin M) E) i j) := by
    simp only [actTup, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [h]
  exact sum_mem_latR _ _ (fun j _ => mul_mem_latR (hg i j) (fun k => hX a j k))

omit [NumberField F] in
/- English proof (translation)
Use function extensionality and compare the values at `a`. Simplify using `only [actTup, Matrix.mulVec_mulVec]`. Rewrite using `[← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mulVec]`.
-/
theorem actTup_inv {M n : ℕ} (R : Type) [CommRing R] [Algebra F R] (g : GL (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) :
    actTup R (bc (inclR R) g⁻¹) (actTup R (bc (inclR R) g) X) = X := by
  funext a
  simp only [actTup, Matrix.mulVec_mulVec]
  rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mulVec]

/- English proof (translation)
Introduce `k`. Rewrite using `[Algebra.TensorProduct.one_def, Algebra.TensorProduct.basis_repr_tmul]`. Simplify using `using h k`.
-/
theorem one_mem_latR {d : ℕ} {b : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (h : ∀ k, algebraMap F (Fv F v) (b.repr 1 k) ∈ v.adicCompletionIntegers F) :
    (1 : Fv F v ⊗[F] E) ∈ latR b v := by
  intro k
  rw [Algebra.TensorProduct.one_def, Algebra.TensorProduct.basis_repr_tmul]
  simpa using h k

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hX a i k`. Simplify `hX a.succ i.succ k` using `[consTup]`. Introduce `hX a`. Use `Fin.cases ?_ (fun a => ?_) a` and prove the remaining obligations.

Introduce `i`. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Introduce `k`. Simplify `one_mem_latR h k` using `[consTup]`. Simplify using `[consTup]`.

Introduce `i`. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Simplify using `[consTup]`. Simplify `hX a i` using `[consTup]`.
-/
theorem consTup_mem_iff {d M n : ℕ} {b : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (h : ∀ k, algebraMap F (Fv F v) (b.repr 1 k) ∈ v.adicCompletionIntegers F)
    (X : Fin n → Fin M → Fv F v ⊗[F] E) : consTup X ∈ latV b v ↔ X ∈ latV b v := by
  constructor
  · intro hX a i k
    simpa [consTup] using hX a.succ i.succ k
  · intro hX a
    refine Fin.cases ?_ (fun a => ?_) a
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · intro k
        simpa [consTup] using one_mem_latR h k
      · simp [consTup]
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [consTup]
      · simpa [consTup] using hX a i

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ _ d b n M`. Use `⟨fun g hg => ?_, fun g => ?_, ?_⟩` and prove the remaining obligations. Use `filter_upwards [eventually_good_matrix b g, eventually_good_matrix b g⁻¹] with v h1 h2 X`. Use `⟨fun hX => ?_, rmul_mem h1⟩` and prove the remaining obligations. Establish `hmul : g.map (inclR (F` using `F) (E := E) (Fv F v)) * g⁻¹.map (inclR (F := F) (E := E) (Fv F v)) = 1 := by`.

Rewrite using `[← Matrix.map_mul, Matrix.mul_nonsing_inv g (isUnit_iff_ne_zero.2 hg), Matrix.map_one _ (map_zero _) (map_one _)]`. Use `rmul_mem h2 hX` as an intermediate fact. Rewrite `this` using `[rmul_rmul, hmul, rmul_one]`. Then use the resulting hypothesis. Use `filter_upwards [eventually_good_matrix b (g : Matrix (Fin M) (Fin M) E), eventually_good_matrix b ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E)] with v h1 h2 X`. Use `⟨fun hX => ?_, actTup_mem h1⟩` and prove the remaining obligations.

Use `actTup_mem (g := g⁻¹) h2 hX` as an intermediate fact. Rewrite `this` using `[actTup_inv]`. Then use the resulting hypothesis. Establish `h0 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k, algebraMap F (Fv F v) (b.repr 1 k) ∈ v.adicCompletionIntegers F` using `Filter.eventually_all.2 fun k => eventually_integral (b.repr (1 : E) k) filter_upwards [h0] with v h X`. Conclude with `consTup_mem_iff h X`.
-/
theorem latV_rational : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ), (∀ g : Matrix (Fin n) (Fin n) E, g.det ≠ 0 → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ X : (Fin n → Fin M → Fv F v ⊗[F] E), rmul (Fv F v) X (g.map (inclR (Fv F v))) ∈ latV b v ↔ X ∈ latV b v) ∧ (∀ g : GL (Fin M) E, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ X : (Fin n → Fin M → Fv F v ⊗[F] E), actTup (Fv F v) (bc (inclR (Fv F v)) g) X ∈ latV b v ↔ X ∈ latV b v) ∧ ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ X : (Fin n → Fin M → Fv F v ⊗[F] E), consTup X ∈ latV b v ↔ X ∈ latV b v := by
  intro F E _ _ _ _ _ σ _ d b n M
  refine ⟨fun g hg => ?_, fun g => ?_, ?_⟩
  · filter_upwards [eventually_good_matrix b g, eventually_good_matrix b g⁻¹] with v h1 h2 X
    refine ⟨fun hX => ?_, rmul_mem h1⟩
    have hmul : g.map (inclR (F := F) (E := E) (Fv F v)) * g⁻¹.map (inclR (F := F) (E := E) (Fv F v)) = 1 := by
      rw [← Matrix.map_mul, Matrix.mul_nonsing_inv g (isUnit_iff_ne_zero.2 hg),
        Matrix.map_one _ (map_zero _) (map_one _)]
    have := rmul_mem h2 hX
    rwa [rmul_rmul, hmul, rmul_one] at this
  · filter_upwards [eventually_good_matrix b (g : Matrix (Fin M) (Fin M) E),
      eventually_good_matrix b ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E)] with v h1 h2 X
    refine ⟨fun hX => ?_, actTup_mem h1⟩
    have := actTup_mem (g := g⁻¹) h2 hX
    rwa [actTup_inv] at this
  · have h0 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k,
        algebraMap F (Fv F v) (b.repr 1 k) ∈ v.adicCompletionIntegers F :=
      Filter.eventually_all.2 fun k => eventually_integral (b.repr (1 : E) k)
    filter_upwards [h0] with v h X
    exact consTup_mem_iff h X

end GlobalTheory.CompanionTheory.SW.LatRat
