import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.RealSignIdele

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Set `e` to `InfinitePlace.Completion.ringEquivRealOfIsReal hw`. Establish `he : Continuous (fun y : w.Completion => e y)` using `(InfinitePlace.Completion.isometryEquivRealOfIsReal hw).continuous`. Set `g : (InfiniteAdeleRing E)ˣ → ℝ` to `fun u => e ((u : InfiniteAdeleRing E) w)`. Establish `hg : Continuous g` using `he.comp ((continuous_apply w).comp Units.continuous_val)`. Establish `hg0 : ∀ u, g u ≠ 0` using `fun u h => by`.

Establish `h1 : (u : InfiniteAdeleRing E) w = 0` using `(map_eq_zero e).mp h`. Conclude with `left_ne_zero_of_mul_eq_one (congrFun u.mul_inv w) h1`. Establish `hg1 : g 1 = 1` using `map_one e`. Assume the negation of the conclusion as `hneg`. Take `⟨v, -, hv⟩` from `isPreconnected_connectedComponent.intermediate_value hu mem_connectedComponent hg.continuousOn (show (0 : ℝ) ∈ Set.Icc (g u) (g 1) from ⟨not_lt.mp hneg, by rw [hg1]; exact zero_le_one⟩)`.

Conclude with `hg0 v hv`.
-/
theorem pos_of_mem_conn {w : InfinitePlace E} (hw : w.IsReal) {u : (InfiniteAdeleRing E)ˣ}
    (hu : u ∈ Subgroup.connectedComponentOfOne (InfiniteAdeleRing E)ˣ) :
    0 < InfinitePlace.Completion.ringEquivRealOfIsReal hw ((u : InfiniteAdeleRing E) w) := by
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  have he : Continuous (fun y : w.Completion => e y) :=
    (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).continuous
  let g : (InfiniteAdeleRing E)ˣ → ℝ := fun u => e ((u : InfiniteAdeleRing E) w)
  have hg : Continuous g := he.comp ((continuous_apply w).comp Units.continuous_val)
  have hg0 : ∀ u, g u ≠ 0 := fun u h => by
    have h1 : (u : InfiniteAdeleRing E) w = 0 := (map_eq_zero e).mp h
    exact left_ne_zero_of_mul_eq_one (congrFun u.mul_inv w) h1
  have hg1 : g 1 = 1 := map_one e
  by_contra hneg
  obtain ⟨v, -, hv⟩ := isPreconnected_connectedComponent.intermediate_value hu mem_connectedComponent
    hg.continuousOn (show (0 : ℝ) ∈ Set.Icc (g u) (g 1) from ⟨not_lt.mp hneg, by rw [hg1]; exact zero_le_one⟩)
  exact hg0 v hv

/- English proof (translation)
Take `⟨m, hm⟩` from `Ideal.mem_span_singleton'.1 h3`. Establish `ea : a = 1 + (3 : ℤ) • m`. Rewrite using `[zsmul_eq_mul, Int.cast_ofNat, mul_comm, hm]`. Expand and normalize the polynomial expressions, which then agree. Set `b` to `RingOfIntegers.basis E`.

Establish `hdet : (Int.castRingHom (ZMod 3)) (Algebra.norm ℤ a) = 1`. Rewrite using `[Algebra.norm_eq_matrix_det b, RingHom.map_det, ea, map_add, map_one, map_zsmul]`. Establish `: (Int.castRingHom (ZMod 3)).mapMatrix (1 + (3 : ℤ) • Algebra.leftMulMatrix b m) = 1`. Use extensionality with `i j`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, eq_intCast, Int.cast_ofNat]`.

Establish `h30 : (3 : ZMod 3) = 0` using `rfl`. Rewrite using `[h30, zero_mul, add_zero, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[this, Matrix.det_one]`. Establish `hu : IsUnit (Algebra.norm ℤ a)` using `ha.map _`.

Break down `Int.isUnit_iff.1 hu with h | h` into its components or cases. Conclude with `h`. Rewrite `hdet` using `[h]`. Conclude with `absurd hdet (by decide)`.
-/
theorem norm_eq_one_of_sub_one_mem {a : 𝓞 E} (ha : IsUnit a) (h3 : a - 1 ∈ Ideal.span {(3 : 𝓞 E)}) :
    Algebra.norm ℤ a = 1 := by
  classical
  obtain ⟨m, hm⟩ := Ideal.mem_span_singleton'.1 h3
  have ea : a = 1 + (3 : ℤ) • m := by
    rw [zsmul_eq_mul, Int.cast_ofNat, mul_comm, hm]; ring
  let b := RingOfIntegers.basis E
  have hdet : (Int.castRingHom (ZMod 3)) (Algebra.norm ℤ a) = 1 := by
    rw [Algebra.norm_eq_matrix_det b, RingHom.map_det, ea, map_add, map_one, map_zsmul]
    have : (Int.castRingHom (ZMod 3)).mapMatrix (1 + (3 : ℤ) • Algebra.leftMulMatrix b m) = 1 := by
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        map_add, map_mul, eq_intCast, Int.cast_ofNat]
      have h30 : (3 : ZMod 3) = 0 := rfl
      rw [h30, zero_mul, add_zero, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    rw [this, Matrix.det_one]
  have hu : IsUnit (Algebra.norm ℤ a) := ha.map _
  rcases Int.isUnit_iff.1 hu with h | h
  · exact h
  · rw [h] at hdet
    exact absurd hdet (by decide)

/- English proof (translation)
Rewrite using `[Complex.norm_real, Real.norm_of_nonneg hr.le]`. Conclude with `div_self (Complex.ofReal_ne_zero.2 hr.ne')`.
-/
theorem div_norm_of_pos {r : ℝ} (hr : 0 < r) : (r : ℂ) / ((‖(r : ℂ)‖ : ℝ) : ℂ) = 1 := by
  rw [Complex.norm_real, Real.norm_of_nonneg hr.le]
  exact div_self (Complex.ofReal_ne_zero.2 hr.ne')

/- English proof (translation)
Rewrite using `[Complex.norm_real, Real.norm_of_nonpos hr.le, Complex.ofReal_neg, div_neg, div_self (Complex.ofReal_ne_zero.2 hr.ne)]`.
-/
theorem div_norm_of_neg {r : ℝ} (hr : r < 0) : (r : ℂ) / ((‖(r : ℂ)‖ : ℝ) : ℂ) = -1 := by
  rw [Complex.norm_real, Real.norm_of_nonpos hr.le, Complex.ofReal_neg, div_neg,
    div_self (Complex.ofReal_ne_zero.2 hr.ne)]

/- English proof (translation)
Introduce `hN`. Establish `cc : ∀ ψ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate ψ) = ψ` using `fun ψ => star_star ψ`. Set `f : (E →+* ℂ) → ℂ` to `fun φ => φ k / ((‖φ k‖ : ℝ) : ℂ)`. Establish `hprod : ∏ φ : E →+* ℂ, φ k = 1`. Use `Algebra.norm_eq_prod_embeddings ℚ ℂ k` as an intermediate fact.

Rewrite `this` using `[hN, map_one]`. Rewrite using `[this]`. Conclude with `Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) _ _ fun φ => rfl`. Establish `habs : ∏ φ : E →+* ℂ, ((‖φ k‖ : ℝ) : ℂ) = 1`. Rewrite using `[← Complex.ofReal_prod, ← norm_prod, hprod, norm_one, Complex.ofReal_one]`.

Establish `h1 : ∏ φ : E →+* ℂ, f φ = 1`. Simplify using `only [f]`. Rewrite using `[Finset.prod_div_distrib, hprod, habs, div_one]`. Establish `hnz : ∀ φ : E →+* ℂ, φ k ≠ 0` using `fun φ => (map_ne_zero φ).2 hk`. Establish `h2 : ∏ φ ∈ Finset.univ.erase w.embedding, f φ = 1`.

Use `Finset.prod_involution (fun φ _ => ComplexEmbedding.conjugate φ) (fun φ _ => ?_) (fun φ hφ => ?_) (fun φ hφ => ?_) (fun φ _ => cc φ)` and prove the remaining obligations. Simplify using `only [f]`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj, div_mul_div_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Establish `hn : ((‖φ k‖ : ℝ) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (hnz φ))`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Introduce `hf heq`. Apply `hf` to reduce the goal to its premises. Establish `hr : ComplexEmbedding.IsReal φ` using `ComplexEmbedding.isReal_iff.2 heq`. Establish `hemb` using `InfinitePlace.embedding_mk_eq_of_isReal hr`.

Establish `hw' : (InfinitePlace.mk φ).IsReal` using `InfinitePlace.isReal_iff.2 (by rw [hemb]; exact hr)`. Establish `hne : InfinitePlace.mk φ ≠ w`. Introduce and unpack `h`. Apply `(Finset.mem_erase.1 hφ).1` to reduce the goal to its premises. Rewrite using `[← hemb, h]`.

Establish `e1 : φ k = ((InfinitePlace.embedding_of_isReal hw' k : ℝ) : ℂ)`. Rewrite using `[InfinitePlace.embedding_of_isReal_apply, hemb]`. Simplify using `only [f]`. Rewrite using `[e1]`. Conclude with `div_norm_of_pos (hpos _ hw' hne)`.

Use `Finset.mem_erase.2 ⟨fun h => (Finset.mem_erase.1 hφ).1 ?_, Finset.mem_univ _⟩` and prove the remaining obligations. Rewrite using `[← cc φ, h]`. Conclude with `ComplexEmbedding.isReal_iff.1 (InfinitePlace.isReal_iff.1 hw)`. Establish `h3 : f w.embedding = -1`. Simplify using `only [f]`.

Rewrite using `[← InfinitePlace.embedding_of_isReal_apply hw]`. Conclude with `div_norm_of_neg hneg`. Rewrite `h1` using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ w.embedding), h2, h3, mul_one]`. Evaluate the numerical expressions using `at h1`.
-/
theorem norm_ne_one_of_sign {w : InfinitePlace E} (hw : w.IsReal) {k : E} (hk : k ≠ 0)
    (hneg : InfinitePlace.embedding_of_isReal hw k < 0)
    (hpos : ∀ (w' : InfinitePlace E) (hw' : w'.IsReal), w' ≠ w → 0 < InfinitePlace.embedding_of_isReal hw' k) :
    Algebra.norm ℚ k ≠ 1 := by
  classical
  intro hN
  have cc : ∀ ψ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate ψ) = ψ := fun ψ => star_star ψ
  let f : (E →+* ℂ) → ℂ := fun φ => φ k / ((‖φ k‖ : ℝ) : ℂ)
  have hprod : ∏ φ : E →+* ℂ, φ k = 1 := by
    have := Algebra.norm_eq_prod_embeddings ℚ ℂ k
    rw [hN, map_one] at this
    rw [this]
    exact Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) _ _ fun φ => rfl
  have habs : ∏ φ : E →+* ℂ, ((‖φ k‖ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_prod, ← norm_prod, hprod, norm_one, Complex.ofReal_one]
  have h1 : ∏ φ : E →+* ℂ, f φ = 1 := by
    simp only [f]
    rw [Finset.prod_div_distrib, hprod, habs, div_one]
  have hnz : ∀ φ : E →+* ℂ, φ k ≠ 0 := fun φ => (map_ne_zero φ).2 hk
  have h2 : ∏ φ ∈ Finset.univ.erase w.embedding, f φ = 1 := by
    refine Finset.prod_involution (fun φ _ => ComplexEmbedding.conjugate φ) (fun φ _ => ?_) (fun φ hφ => ?_)
      (fun φ hφ => ?_) (fun φ _ => cc φ)
    · simp only [f]
      rw [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj, div_mul_div_comm, Complex.mul_conj,
        Complex.normSq_eq_norm_sq]
      have hn : ((‖φ k‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (hnz φ))
      push_cast
      field_simp
    · intro hf heq
      apply hf
      have hr : ComplexEmbedding.IsReal φ := ComplexEmbedding.isReal_iff.2 heq
      have hemb := InfinitePlace.embedding_mk_eq_of_isReal hr
      have hw' : (InfinitePlace.mk φ).IsReal := InfinitePlace.isReal_iff.2 (by rw [hemb]; exact hr)
      have hne : InfinitePlace.mk φ ≠ w := by
        rintro h
        apply (Finset.mem_erase.1 hφ).1
        rw [← hemb, h]
      have e1 : φ k = ((InfinitePlace.embedding_of_isReal hw' k : ℝ) : ℂ) := by
        rw [InfinitePlace.embedding_of_isReal_apply, hemb]
      simp only [f]
      rw [e1]
      exact div_norm_of_pos (hpos _ hw' hne)
    · refine Finset.mem_erase.2 ⟨fun h => (Finset.mem_erase.1 hφ).1 ?_, Finset.mem_univ _⟩
      rw [← cc φ, h]
      exact ComplexEmbedding.isReal_iff.1 (InfinitePlace.isReal_iff.1 hw)
  have h3 : f w.embedding = -1 := by
    simp only [f]
    rw [← InfinitePlace.embedding_of_isReal_apply hw]
    exact div_norm_of_neg hneg
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w.embedding), h2, h3, mul_one] at h1
  norm_num at h1

open GlobalTheory.RayFromArtin GlobalTheory.Mem.LocTriv in

/- English proof (translation)
Introduce `E _ _ w hw hx`. Set `𝔪 : Ideal (𝓞 E)` to `Ideal.span {(3 : 𝓞 E)}`. Establish `hm : 𝔪 ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Introduce `h`.

Establish `h'` using `congrArg (algebraMap (𝓞 E) E) h`. Rewrite `h'` using `[map_ofNat, map_zero]`. Evaluate the numerical expressions using `at h'`. Establish `hle : ((diagUnits E).range ⊔ infConn E).topologicalClosure ≤ rayGrp 𝔪` using `Subgroup.topologicalClosure_minimal _ (sup_le_sup_left (infConn_le_rayIdl 𝔪) _) (Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono le_sup_right (isOpen_rayIdl hm)))`. Take `⟨_, ⟨k, rfl⟩, z, hz, e⟩` from `Subgroup.mem_sup.1 (hle hx)`.

Use `set x := ReciprocityTheory.Neutral.Bridge.HCFR.infIdele E w (-1) with hxdef`. Establish `hku : diagUnits E k = x * z⁻¹` using `eq_mul_inv_of_mul_eq e`. Take `⟨hunit, hcong, hinf⟩` from `inv_mem hz`. Establish `hev : ∀ v, ev v (diagUnits E k : AdeleRing (𝓞 E) E) = ev v ((z⁻¹ : Ideles E) : AdeleRing (𝓞 E) E)`. Introduce `v`.

Rewrite using `[hku, Units.val_mul, map_mul]`. Use `show (x : AdeleRing (𝓞 E) E).2 v * _ = _`. Rewrite using `[hxdef, infIdele_snd, one_mul]`. Establish `hval : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E (k : E) = 1` using `fun v => by`. Rewrite using `[← valued_algebraMap, ← ev_diagUnits, hev]`.

Conclude with `hunit v`. Establish `hcong' : ∀ v : HeightOneSpectrum (𝓞 E), v.asIdeal ∣ 𝔪 → v.valuation E ((k : E) - 1) ≤ rad 𝔪 v` using `fun v hv => by`. Rewrite using `[← valued_algebraMap, map_sub, map_one, ← ev_diagUnits, hev]`. Conclude with `hcong v hv`. Take `⟨a, ha⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E (k : E) fun v => (hval v).le`.

Take `⟨b, hb⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E ((k⁻¹ : Eˣ) : E) fun v => by`. Rewrite using `[Units.val_inv_eq_inv_val, map_inv₀, hval, inv_one]`. Establish `hab : a * b = 1` using `IsFractionRing.injective (𝓞 E) E (by rw [map_mul, ha, hb, map_one, Units.mul_inv])`. Establish `ha1 : a - 1 ∈ 𝔪` using `(mem_iff_rad hm _).2 fun v => by`. Distinguish the cases in `hv : v.asIdeal ∣ 𝔪`.

Establish `e1 : ((a - 1 : 𝓞 E) : E) = (k : E) - 1`. Rewrite using `[RingOfIntegers.coe_eq_algebraMap, map_sub, map_one, ha]`. Rewrite using `[e1]`. Conclude with `hcong' v hv`. Rewrite using `[rad_eq_one hm hv]`.

Conclude with `v.valuation_le_one _`. Establish `hN : Algebra.norm ℚ (k : E) = 1`. Rewrite using `[← ha, ← RingOfIntegers.coe_eq_algebraMap, ← Algebra.coe_norm_int, norm_eq_one_of_sub_one_mem ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, rfl⟩ ha1, Int.cast_one]`. Establish `hcomp : ∀ w' : InfinitePlace E, algebraMap E w'.Completion (k : E) = (x : AdeleRing (𝓞 E) E).1 w' * ((z⁻¹ : Ideles E) : AdeleRing (𝓞 E) E).1 w'` using `fun w' => by`. Use `congrArg (fun t : Ideles E => (t : AdeleRing (𝓞 E) E).1 w') hku` as an intermediate fact.

Simplify using `only [Units.val_mul, Prod.fst_mul, Pi.mul_apply] at this`. Conclude with `this`. Establish `hemb : ∀ (w' : InfinitePlace E) (hw' : w'.IsReal), InfinitePlace.embedding_of_isReal hw' (k : E) = InfinitePlace.Completion.ringEquivRealOfIsReal hw' (algebraMap E w'.Completion (k : E))` using `fun w' hw' => (InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw' ((WithAbs.equiv w'.1).symm (k : E))).symm`. Establish `hpos' : ∀ (w' : InfinitePlace E) (hw' : w'.IsReal), 0 < InfinitePlace.Completion.ringEquivRealOfIsReal hw' (((z⁻¹ : Ideles E) : AdeleRing (𝓞 E) E).1 w')` using `fun w' hw' => pos_of_mem_conn hw' hinf`. Use `norm_ne_one_of_sign hw (k := (k : E)) k.ne_zero ?_ (fun w' hw' hne => ?_) hN` and prove the remaining obligations.

Rewrite using `[hemb, hcomp, hxdef, infIdele_fst_self, Units.val_neg, Units.val_one, neg_one_mul, map_neg]`. Conclude with `neg_neg_of_pos (hpos' w hw)`. Rewrite using `[hemb, hcomp, hxdef, infIdele_fst_ne E w w' hne, one_mul]`. Conclude with `hpos' w' hw'`.
-/
theorem infIdele_neg_one_not_mem :
    ∀ (E : Type) [Field E] [NumberField E] (w : InfinitePlace E), w.IsReal →
      ReciprocityTheory.Neutral.Bridge.HCFR.infIdele E w (-1) ∉ ((diagUnits E).range ⊔ infConn E).topologicalClosure := by
  intro E _ _ w hw hx
  let 𝔪 : Ideal (𝓞 E) := Ideal.span {(3 : 𝓞 E)}
  have hm : 𝔪 ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    intro h
    have h' := congrArg (algebraMap (𝓞 E) E) h
    rw [map_ofNat, map_zero] at h'
    norm_num at h'
  have hle : ((diagUnits E).range ⊔ infConn E).topologicalClosure ≤ rayGrp 𝔪 :=
    Subgroup.topologicalClosure_minimal _ (sup_le_sup_left (infConn_le_rayIdl 𝔪) _)
      (Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono le_sup_right (isOpen_rayIdl hm)))
  obtain ⟨_, ⟨k, rfl⟩, z, hz, e⟩ := Subgroup.mem_sup.1 (hle hx)
  set x := ReciprocityTheory.Neutral.Bridge.HCFR.infIdele E w (-1) with hxdef
  have hku : diagUnits E k = x * z⁻¹ := eq_mul_inv_of_mul_eq e
  obtain ⟨hunit, hcong, hinf⟩ := inv_mem hz

  have hev : ∀ v, ev v (diagUnits E k : AdeleRing (𝓞 E) E) = ev v ((z⁻¹ : Ideles E) : AdeleRing (𝓞 E) E) := by
    intro v
    rw [hku, Units.val_mul, map_mul]
    show (x : AdeleRing (𝓞 E) E).2 v * _ = _
    rw [hxdef, infIdele_snd, one_mul]
  have hval : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E (k : E) = 1 := fun v => by
    rw [← valued_algebraMap, ← ev_diagUnits, hev]
    exact hunit v
  have hcong' : ∀ v : HeightOneSpectrum (𝓞 E), v.asIdeal ∣ 𝔪 → v.valuation E ((k : E) - 1) ≤ rad 𝔪 v :=
    fun v hv => by
      rw [← valued_algebraMap, map_sub, map_one, ← ev_diagUnits, hev]
      exact hcong v hv
  obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E (k : E) fun v => (hval v).le
  obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E ((k⁻¹ : Eˣ) : E) fun v => by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hval, inv_one]
  have hab : a * b = 1 := IsFractionRing.injective (𝓞 E) E (by rw [map_mul, ha, hb, map_one, Units.mul_inv])
  have ha1 : a - 1 ∈ 𝔪 := (mem_iff_rad hm _).2 fun v => by
    by_cases hv : v.asIdeal ∣ 𝔪
    · have e1 : ((a - 1 : 𝓞 E) : E) = (k : E) - 1 := by
        rw [RingOfIntegers.coe_eq_algebraMap, map_sub, map_one, ha]
      rw [e1]
      exact hcong' v hv
    · rw [rad_eq_one hm hv]
      exact v.valuation_le_one _
  have hN : Algebra.norm ℚ (k : E) = 1 := by
    rw [← ha, ← RingOfIntegers.coe_eq_algebraMap, ← Algebra.coe_norm_int,
      norm_eq_one_of_sub_one_mem ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, rfl⟩ ha1, Int.cast_one]

  have hcomp : ∀ w' : InfinitePlace E, algebraMap E w'.Completion (k : E) =
      (x : AdeleRing (𝓞 E) E).1 w' * ((z⁻¹ : Ideles E) : AdeleRing (𝓞 E) E).1 w' := fun w' => by
    have := congrArg (fun t : Ideles E => (t : AdeleRing (𝓞 E) E).1 w') hku
    simp only [Units.val_mul, Prod.fst_mul, Pi.mul_apply] at this
    exact this
  have hemb : ∀ (w' : InfinitePlace E) (hw' : w'.IsReal), InfinitePlace.embedding_of_isReal hw' (k : E) =
      InfinitePlace.Completion.ringEquivRealOfIsReal hw' (algebraMap E w'.Completion (k : E)) := fun w' hw' =>
    (InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw' ((WithAbs.equiv w'.1).symm (k : E))).symm
  have hpos' : ∀ (w' : InfinitePlace E) (hw' : w'.IsReal),
      0 < InfinitePlace.Completion.ringEquivRealOfIsReal hw' (((z⁻¹ : Ideles E) : AdeleRing (𝓞 E) E).1 w') :=
    fun w' hw' => pos_of_mem_conn hw' hinf
  refine norm_ne_one_of_sign hw (k := (k : E)) k.ne_zero ?_ (fun w' hw' hne => ?_) hN
  · rw [hemb, hcomp, hxdef, infIdele_fst_self, Units.val_neg, Units.val_one, neg_one_mul, map_neg]
    exact neg_neg_of_pos (hpos' w hw)
  · rw [hemb, hcomp, hxdef, infIdele_fst_ne E w w' hne, one_mul]
    exact hpos' w' hw'

end GlobalTheory.RealSignIdele
