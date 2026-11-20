import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjLowUni

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt Filter
open scoped ContDiff Topology

namespace GlobalTheory.SchurNear

variable {E : Type} [Field E] [NumberField E] {α : Type}

/- English proof (translation)
The claim follows from `RestrictedProduct.continuous_eval w`.
-/
theorem continuous_pLoc (w : HeightOneSpectrum (𝓞 E)) : Continuous (pLoc E w) :=
  RestrictedProduct.continuous_eval w

/- English proof (translation)
Use `⟨⟨fun w => (pLoc E w x)⁻¹, Eventually.of_forall h1⟩, h1, ?_⟩` and prove the remaining obligations. Use `Subtype.ext (funext fun w => ?_)` and prove the remaining obligations. Conclude with `mul_inv_cancel₀ (h0 w)`.
-/
theorem exists_inv (x : Af E) (h0 : ∀ w, pLoc E w x ≠ 0)
    (h1 : ∀ w : HeightOneSpectrum (𝓞 E), (pLoc E w x)⁻¹ ∈ w.adicCompletionIntegers E) :
    ∃ y ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E, x * y = 1 := by
  refine ⟨⟨fun w => (pLoc E w x)⁻¹, Eventually.of_forall h1⟩, h1, ?_⟩
  refine Subtype.ext (funext fun w => ?_)
  exact mul_inv_cancel₀ (h0 w)

/- English proof (translation)
Establish `h : ∀ w ∈ S, ∀ᶠ a in l, pLoc E w (f a) ≠ 0 ∧ (pLoc E w (f a))⁻¹ ∈ w.adicCompletionIntegers E`. Introduce `w _`. Establish `h1 : Tendsto (fun a => pLoc E w (f a)) l (𝓝 1)`. Use `((continuous_pLoc w).tendsto 1).comp hf` as an intermediate fact. Rewrite `this` using `[map_one]`. Then use the resulting hypothesis.

Establish `h2 : Tendsto (fun a => (pLoc E w (f a))⁻¹) l (𝓝 1)`. Use `h1.inv₀ one_ne_zero` as an intermediate fact. Rewrite `this` using `[inv_one]`. Then use the resulting hypothesis. Use `(h1.eventually_ne one_ne_zero).and ?_` and prove the remaining obligations. Conclude with `h2.eventually ((Valued.isOpen_valuationSubring _).mem_nhds (one_mem (w.adicCompletionIntegers E)))`.

Use `filter_upwards [(eventually_all_finset S).2 h, hS] with a ha hb`. Use `exists_inv _ (fun w => ?_) (fun w => ?_)` and prove the remaining obligations. Distinguish the cases in `hw : w ∈ S`. Conclude with `(ha w hw).1`. Rewrite using `[hb w hw]`.

Conclude with `one_ne_zero`. Distinguish the cases in `hw : w ∈ S`. Conclude with `(ha w hw).2`. Rewrite using `[hb w hw, inv_one]`. Conclude with `one_mem _`.
-/
theorem eventually_inv (S : Finset (HeightOneSpectrum (𝓞 E))) {l : Filter α} {f : α → Af E}
    (hf : Tendsto f l (𝓝 1)) (hS : ∀ᶠ a in l, ∀ w ∉ S, pLoc E w (f a) = 1) :
    ∀ᶠ a in l, ∃ y ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E, f a * y = 1 := by
  have h : ∀ w ∈ S, ∀ᶠ a in l, pLoc E w (f a) ≠ 0 ∧ (pLoc E w (f a))⁻¹ ∈ w.adicCompletionIntegers E := by
    intro w _
    have h1 : Tendsto (fun a => pLoc E w (f a)) l (𝓝 1) := by
      have := ((continuous_pLoc w).tendsto 1).comp hf
      rwa [map_one] at this
    have h2 : Tendsto (fun a => (pLoc E w (f a))⁻¹) l (𝓝 1) := by
      have := h1.inv₀ one_ne_zero
      rwa [inv_one] at this
    refine (h1.eventually_ne one_ne_zero).and ?_
    exact h2.eventually ((Valued.isOpen_valuationSubring _).mem_nhds (one_mem (w.adicCompletionIntegers E)))
  filter_upwards [(eventually_all_finset S).2 h, hS] with a ha hb
  refine exists_inv _ (fun w => ?_) (fun w => ?_)
  · by_cases hw : w ∈ S
    · exact (ha w hw).1
    · rw [hb w hw]; exact one_ne_zero
  · by_cases hw : w ∈ S
    · exact (ha w hw).2
    · rw [hb w hw, inv_one]; exact one_mem _

/- English proof (translation)
Introduce `W hW`. Establish `hO` using `GroundTheory.Global.isCompact_integralFiniteAdeles E`. Establish `hN : ∀ᶠ c in 𝓝 (1 : Af E), ∀ y ∈ (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (Af E)), 1 + (1 - c) * y ∈ W`. Use `hO.eventually_forall_of_forall_eventually fun y _ => ?_` and prove the remaining obligations. Establish `hc : Continuous fun z : Af E × Af E => 1 + (1 - z.1) * z.2` using `by fun_prop`.

Establish `h` using `hc.tendsto ((1 : Af E), y)`. Simplify using `only [sub_self, zero_mul, add_zero] at h`. Conclude with `h hW`. Express the relevant statement in the definitionally equal form `∀ᶠ a in l, Ring.inverse (f a) ∈ W`. Use `filter_upwards [hf.eventually hN, eventually_inv S hf hS] with a ha ⟨y, hy, hxy⟩`.

Establish `hu : IsUnit (f a)` using `IsUnit.of_mul_eq_one y hxy`. Establish `: Ring.inverse (f a) = 1 + (1 - f a) * y`. Establish `h1` using `Ring.inverse_mul_cancel _ hu`. Take the linear combination `(1 - Ring.inverse (f a)) * hxy + y * h1`. Rewrite using `[this]`.

Conclude with `ha y hy`.
-/
theorem tendsto_inverse (S : Finset (HeightOneSpectrum (𝓞 E))) {l : Filter α} {f : α → Af E}
    (hf : Tendsto f l (𝓝 1)) (hS : ∀ᶠ a in l, ∀ w ∉ S, pLoc E w (f a) = 1) :
    Tendsto (fun a => Ring.inverse (f a)) l (𝓝 1) := by
  intro W hW
  have hO := GroundTheory.Global.isCompact_integralFiniteAdeles E
  have hN : ∀ᶠ c in 𝓝 (1 : Af E), ∀ y ∈ (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (Af E)),
      1 + (1 - c) * y ∈ W := by
    refine hO.eventually_forall_of_forall_eventually fun y _ => ?_
    have hc : Continuous fun z : Af E × Af E => 1 + (1 - z.1) * z.2 := by fun_prop
    have h := hc.tendsto ((1 : Af E), y)
    simp only [sub_self, zero_mul, add_zero] at h
    exact h hW
  change ∀ᶠ a in l, Ring.inverse (f a) ∈ W
  filter_upwards [hf.eventually hN, eventually_inv S hf hS] with a ha ⟨y, hy, hxy⟩
  have hu : IsUnit (f a) := IsUnit.of_mul_eq_one y hxy
  have : Ring.inverse (f a) = 1 + (1 - f a) * y := by
    have h1 := Ring.inverse_mul_cancel _ hu
    linear_combination (1 - Ring.inverse (f a)) * hxy + y * h1
  rw [this]; exact ha y hy

/- English proof (translation)
Establish `hd : Tendsto (fun a => (g a).det) l (𝓝 1)`. Use `((continuous_id.matrix_det (X := Matrix (Fin n) (Fin n) (Af E))).tendsto 1).comp hg` as an intermediate fact. Simplify `this` using `[Function.comp_def]`. Establish `hdS : ∀ᶠ a in l, ∀ w ∉ S, pLoc E w (g a).det = 1` using `by filter_upwards [hS] with a ha w hw`. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, ha w hw, Matrix.det_one]`.

Establish `hu : ∀ᶠ a in l, IsUnit (g a).det` using `by filter_upwards [eventually_inv S hd hdS] with a ⟨y, _, hy⟩`. Conclude with `IsUnit.of_mul_eq_one y hy`. Establish `hadj : Tendsto (fun a => (g a).adjugate) l (𝓝 1)`. Use `((continuous_id.matrix_adjugate (X := Matrix (Fin n) (Fin n) (Af E))).tendsto 1).comp hg` as an intermediate fact. Simplify `this` using `[Function.comp_def]`.

Establish `hi : Tendsto (fun a => (g a)⁻¹) l (𝓝 1)`. Use `(tendsto_inverse S hd hdS).smul hadj` as an intermediate fact. Simplify `this` using `only [one_smul, Matrix.inv_def]`. Use `⟨hu, hi, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.isInducing_embedProduct.tendsto_nhds_iff]`.

Establish `h2` using `(MulOpposite.continuous_op.tendsto _).comp hi`. Establish `h3` using `hg.prodMk_nhds h2`. Use `Tendsto.congr' ?_ h3` and prove the remaining obligations. Use `filter_upwards [hu] with a ha`. Simplify using `only [Function.comp, Units.embedProduct_apply, Matrix.coe_units_inv, coe_mkGL ha]`.
-/
theorem matrix_near (S : Finset (HeightOneSpectrum (𝓞 E))) {n : ℕ} {l : Filter α}
    {g : α → Matrix (Fin n) (Fin n) (Af E)}
    (hg : Tendsto g l (𝓝 1)) (hS : ∀ᶠ a in l, ∀ w ∉ S, (g a).map (pLoc E w) = 1) :
    (∀ᶠ a in l, IsUnit (g a).det) ∧ Tendsto (fun a => (g a)⁻¹) l (𝓝 1) ∧
      Tendsto (fun a => mkGL (g a)) l (𝓝 1) := by
  have hd : Tendsto (fun a => (g a).det) l (𝓝 1) := by
    have := ((continuous_id.matrix_det (X := Matrix (Fin n) (Fin n) (Af E))).tendsto 1).comp hg
    simpa [Function.comp_def] using this
  have hdS : ∀ᶠ a in l, ∀ w ∉ S, pLoc E w (g a).det = 1 := by
    filter_upwards [hS] with a ha w hw
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ha w hw, Matrix.det_one]
  have hu : ∀ᶠ a in l, IsUnit (g a).det := by
    filter_upwards [eventually_inv S hd hdS] with a ⟨y, _, hy⟩
    exact IsUnit.of_mul_eq_one y hy
  have hadj : Tendsto (fun a => (g a).adjugate) l (𝓝 1) := by
    have := ((continuous_id.matrix_adjugate (X := Matrix (Fin n) (Fin n) (Af E))).tendsto 1).comp hg
    simpa [Function.comp_def] using this
  have hi : Tendsto (fun a => (g a)⁻¹) l (𝓝 1) := by
    have := (tendsto_inverse S hd hdS).smul hadj
    simpa only [one_smul, Matrix.inv_def] using this
  refine ⟨hu, hi, ?_⟩
  rw [Units.isInducing_embedProduct.tendsto_nhds_iff]
  have h2 := (MulOpposite.continuous_op.tendsto _).comp hi
  have h3 := hg.prodMk_nhds h2
  refine Tendsto.congr' ?_ h3
  filter_upwards [hu] with a ha
  simp only [Function.comp, Units.embedProduct_apply, Matrix.coe_units_inv, coe_mkGL ha]

section Alg
variable {R T : Type} [CommRing R] [CommRing T] {m r : ℕ}

/- English proof (translation)
Rewrite using `[blk, Matrix.submatrix_one_equiv, Matrix.fromBlocks_one]`.
-/
theorem blk_one : blk (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = Matrix.fromBlocks 1 0 0 1 := by
  rw [blk, Matrix.submatrix_one_equiv, Matrix.fromBlocks_one]

/- English proof (translation)
Rewrite using `[Aof, blk_one, Matrix.toBlocks_fromBlocks₁₁]`.
-/
theorem Aof_one : Aof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 1 := by
  rw [Aof, blk_one, Matrix.toBlocks_fromBlocks₁₁]
/- English proof (translation)
Rewrite using `[Bof, blk_one, Matrix.toBlocks_fromBlocks₁₂]`.
-/
theorem Bof_one : Bof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 0 := by
  rw [Bof, blk_one, Matrix.toBlocks_fromBlocks₁₂]
/- English proof (translation)
Rewrite using `[Cof, blk_one, Matrix.toBlocks_fromBlocks₂₁]`.
-/
theorem Cof_one : Cof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 0 := by
  rw [Cof, blk_one, Matrix.toBlocks_fromBlocks₂₁]
/- English proof (translation)
Rewrite using `[Dof, blk_one, Matrix.toBlocks_fromBlocks₂₂]`.
-/
theorem Dof_one : Dof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 1 := by
  rw [Dof, blk_one, Matrix.toBlocks_fromBlocks₂₂]

/- English proof (translation)
Rewrite using `[conjLowUni, mul_one, lowUni, lowUni, unblk, unblk, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]`. Simplify using the standard rewrite rules.
-/
theorem conj_one (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) : conjLowUni Y 1 = 1 := by
  rw [conjLowUni, mul_one, lowUni, lowUni, unblk, unblk, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp

/- English proof (translation)
Rewrite using `[lowUni, lowUni, unblk, unblk, ← Matrix.submatrix_map, Matrix.fromBlocks_map]`. Simplify using the standard rewrite rules.
-/
theorem lowUni_map (p : R →+* T) (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) :
    (lowUni Y).map p = lowUni (Y.map p) := by
  rw [lowUni, lowUni, unblk, unblk, ← Matrix.submatrix_map, Matrix.fromBlocks_map]
  simp

/- English proof (translation)
Rewrite using `[← conj_one (Y.map p), conjLowUni, conjLowUni, Matrix.map_mul, Matrix.map_mul, lowUni_map, lowUni_map, hk, Matrix.map_neg _ (map_neg p)]`.
-/
theorem conj_map (p : R →+* T) (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R)
    (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (hk : k.map p = 1) :
    (conjLowUni Y k).map p = 1 := by
  rw [← conj_one (Y.map p), conjLowUni, conjLowUni, Matrix.map_mul, Matrix.map_mul, lowUni_map, lowUni_map, hk,
    Matrix.map_neg _ (map_neg p)]

/- English proof (translation)
Rewrite using `[← Dof_one (m := m), ← h]`. Both sides reduce to the same expression.
-/
theorem Dof_map (p : R →+* T) (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : M.map p = 1) :
    (Dof M).map p = 1 := by
  rw [← Dof_one (m := m), ← h]; rfl

/- English proof (translation)
Establish `hA : (Aof M).map p = 1` using `by rw [← Aof_one (r := r), ← h]; rfl`. Establish `hB : (Bof M).map p = 0` using `by rw [← Bof_one (m := m) (r := r), ← h]; rfl`. Rewrite using `[Scof, Matrix.map_sub _ (map_sub p), Matrix.map_mul, Matrix.map_mul, hA, hB]`. Simplify using the standard rewrite rules.
-/
theorem Scof_map (p : R →+* T) (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : M.map p = 1) :
    (Scof M).map p = 1 := by
  have hA : (Aof M).map p = 1 := by rw [← Aof_one (r := r), ← h]; rfl
  have hB : (Bof M).map p = 0 := by rw [← Bof_one (m := m) (r := r), ← h]; rfl
  rw [Scof, Matrix.map_sub _ (map_sub p), Matrix.map_mul, Matrix.map_mul, hA, hB]
  simp

variable [TopologicalSpace R] [IsTopologicalRing R]

/- English proof (translation)
The claim follows from `(Continuous.matrix_fromBlocks continuous_const continuous_const continuous_id continuous_const).matrix_submatrix _ _`.
-/
theorem continuous_lowUni : Continuous (lowUni : Matrix (Fin (r + 1)) (Fin (m + 1)) R → _) :=
  (Continuous.matrix_fromBlocks continuous_const continuous_const continuous_id continuous_const).matrix_submatrix _ _

/- English proof (translation)
Establish `h1 : Continuous fun z => lowUni (f z)` using `continuous_lowUni.comp hf`. Establish `h2 : Continuous fun z => lowUni (-f z)` using `continuous_lowUni.comp hf.neg`. Conclude with `(h1.matrix_mul hg).matrix_mul h2`.
-/
theorem continuous_conj {Z : Type} [TopologicalSpace Z] {f : Z → Matrix (Fin (r + 1)) (Fin (m + 1)) R}
    {g : Z → Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun z => conjLowUni (f z) (g z)) := by
  have h1 : Continuous fun z => lowUni (f z) := continuous_lowUni.comp hf
  have h2 : Continuous fun z => lowUni (-f z) := continuous_lowUni.comp hf.neg
  exact (h1.matrix_mul hg).matrix_mul h2

/- English proof (translation)
Establish `hc : Continuous fun z : Matrix (Fin a) (Fin b) R × Matrix (Fin b) (Fin c) R => z.1 * z.2` using `Continuous.matrix_mul (A := fun z : Matrix (Fin a) (Fin b) R × Matrix (Fin b) (Fin c) R => z.1) (B := fun z => z.2) continuous_fst continuous_snd`. Establish `h` using `(hc.tendsto (x, y)).comp (hf.prodMk_nhds hg)`. Simplify `h` using `only [Function.comp_def]`.
-/
theorem tendsto_mul {a b c : ℕ} {l : Filter α} {f : α → Matrix (Fin a) (Fin b) R} {g : α → Matrix (Fin b) (Fin c) R}
    {x : Matrix (Fin a) (Fin b) R} {y : Matrix (Fin b) (Fin c) R} (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (fun t => f t * g t) l (𝓝 (x * y)) := by
  have hc : Continuous fun z : Matrix (Fin a) (Fin b) R × Matrix (Fin b) (Fin c) R => z.1 * z.2 :=
    Continuous.matrix_mul (A := fun z : Matrix (Fin a) (Fin b) R × Matrix (Fin b) (Fin c) R => z.1)
      (B := fun z => z.2) continuous_fst continuous_snd
  have h := (hc.tendsto (x, y)).comp (hf.prodMk_nhds hg)
  simpa only [Function.comp_def] using h

end Alg

/- English proof (translation)
Establish `hA : Tendsto (fun a => Aof (g a)) l (𝓝 1)`. Rewrite using `[← Aof_one (r := r)]`. Conclude with `(Continuous.tendsto (f := Aof) (continuous_matrix fun i j => continuous_id.matrix_elem _ _) _).comp hg`. Establish `hB : Tendsto (fun a => Bof (g a)) l (𝓝 0)`. Rewrite using `[← Bof_one]`.

Conclude with `(Continuous.tendsto (f := Bof) (continuous_matrix fun i j => continuous_id.matrix_elem _ _) _).comp hg`. Establish `hC : Tendsto (fun a => Cof (g a)) l (𝓝 0)`. Rewrite using `[← Cof_one]`. Conclude with `(Continuous.tendsto (f := Cof) (continuous_matrix fun i j => continuous_id.matrix_elem _ _) _).comp hg`. Establish `hD : Tendsto (fun a => Dof (g a)) l (𝓝 1)`.

Rewrite using `[← Dof_one (m := m)]`. Conclude with `(Continuous.tendsto (f := Dof) (continuous_matrix fun i j => continuous_id.matrix_elem _ _) _).comp hg`. Take `⟨hu, hi, hm⟩` from `matrix_near S hD (hS.mono fun a ha w hw => Dof_map _ _ (ha w hw))`. Establish `hSc : Tendsto (fun a => Scof (g a)) l (𝓝 1)`. Use `hA.sub (tendsto_mul (tendsto_mul hB hi) hC)` as an intermediate fact.

Simplify `this` using `only [Scof, Matrix.mul_zero, sub_zero]`. Use `⟨hu, hm, (matrix_near S hSc (hS.mono fun a ha w hw => Scof_map _ _ (ha w hw))).2.2, ?_, ?_⟩` and prove the remaining obligations. Simplify `tendsto_mul hi hC` using `only [Yof, Matrix.mul_zero]`. Simplify `tendsto_mul hB hi` using `only [Xof, Matrix.zero_mul]`.
-/
theorem blocks_near (S : Finset (HeightOneSpectrum (𝓞 E))) {m r : ℕ} {l : Filter α}
    {g : α → Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)}
    (hg : Tendsto g l (𝓝 1)) (hS : ∀ᶠ a in l, ∀ w ∉ S, (g a).map (pLoc E w) = 1) :
    (∀ᶠ a in l, IsUnit (Dof (g a)).det) ∧ Tendsto (fun a => mkGL (Dof (g a))) l (𝓝 1) ∧
      Tendsto (fun a => mkGL (Scof (g a))) l (𝓝 1) ∧ Tendsto (fun a => Yof (g a)) l (𝓝 0) ∧
      Tendsto (fun a => Xof (g a)) l (𝓝 0) := by
  have hA : Tendsto (fun a => Aof (g a)) l (𝓝 1) := by
    rw [← Aof_one (r := r)]
    exact (Continuous.tendsto (f := Aof) (continuous_matrix fun i j => continuous_id.matrix_elem _ _) _).comp hg
  have hB : Tendsto (fun a => Bof (g a)) l (𝓝 0) := by
    rw [← Bof_one]
    exact (Continuous.tendsto (f := Bof) (continuous_matrix fun i j => continuous_id.matrix_elem _ _) _).comp hg
  have hC : Tendsto (fun a => Cof (g a)) l (𝓝 0) := by
    rw [← Cof_one]
    exact (Continuous.tendsto (f := Cof) (continuous_matrix fun i j => continuous_id.matrix_elem _ _) _).comp hg
  have hD : Tendsto (fun a => Dof (g a)) l (𝓝 1) := by
    rw [← Dof_one (m := m)]
    exact (Continuous.tendsto (f := Dof) (continuous_matrix fun i j => continuous_id.matrix_elem _ _) _).comp hg
  obtain ⟨hu, hi, hm⟩ := matrix_near S hD (hS.mono fun a ha w hw => Dof_map _ _ (ha w hw))
  have hSc : Tendsto (fun a => Scof (g a)) l (𝓝 1) := by
    have := hA.sub (tendsto_mul (tendsto_mul hB hi) hC)
    simpa only [Scof, Matrix.mul_zero, sub_zero] using this
  refine ⟨hu, hm, (matrix_near S hSc (hS.mono fun a ha w hw => Scof_map _ _ (ha w hw))).2.2, ?_, ?_⟩
  · simpa only [Yof, Matrix.mul_zero] using tendsto_mul hi hC
  · simpa only [Xof, Matrix.zero_mul] using tendsto_mul hB hi

/- English proof (translation)
Introduce `l`. Prove the components needed by the constructor for the conclusion. Establish `hc : Continuous fun z : GL (Fin (m + r + 1 + 1)) (Af E) × Z => conjLowUni (π z.2) z.1.val` using `continuous_conj (f := fun z : GL (Fin (m + r + 1 + 1)) (Af E) × Z => π z.2) (g := fun z => z.1.val) (hπ.comp continuous_snd) (Units.continuous_val.comp continuous_fst)`. Use `hc.tendsto (1, z₀)` as an intermediate fact. Simplify using `only [Units.val_one, conj_one] at this`.

Conclude with `this.mono_left inf_le_left`. Use `eventually_inf_principal.2 (Eventually.of_forall fun z hz w hw => conj_map _ _ _ ?_)` and prove the remaining obligations. Conclude with `congrArg Units.val (hz w hw)`.
-/
theorem conj_near (S : Finset (HeightOneSpectrum (𝓞 E))) {m r : ℕ} {Z : Type} [TopologicalSpace Z]
    (π : Z → Matrix (Fin (r + 1)) (Fin (m + 1)) (Af E)) (hπ : Continuous π) (z₀ : Z) :
    let l : Filter (GL (Fin (m + r + 1 + 1)) (Af E) × Z) :=
      𝓝 (1, z₀) ⊓ 𝓟 {z | ∀ w ∉ S, Matrix.GeneralLinearGroup.map (pLoc E w) z.1 = 1}
    Tendsto (fun z : GL (Fin (m + r + 1 + 1)) (Af E) × Z => conjLowUni (π z.2) z.1.val) l (𝓝 1) ∧
      ∀ᶠ z in l, ∀ w ∉ S, (conjLowUni (π z.2) z.1.val).map (pLoc E w) = 1 := by
  intro l
  constructor
  · have hc : Continuous fun z : GL (Fin (m + r + 1 + 1)) (Af E) × Z => conjLowUni (π z.2) z.1.val :=
      continuous_conj (f := fun z : GL (Fin (m + r + 1 + 1)) (Af E) × Z => π z.2) (g := fun z => z.1.val)
        (hπ.comp continuous_snd) (Units.continuous_val.comp continuous_fst)
    have := hc.tendsto (1, z₀)
    simp only [Units.val_one, conj_one] at this
    exact this.mono_left inf_le_left
  · refine eventually_inf_principal.2 (Eventually.of_forall fun z hz w hw => conj_map _ _ _ ?_)
    exact congrArg Units.val (hz w hw)

/- English proof (translation)
Introduce `E _ _ m r S Uβ Ub hβ hb Krow Kcol hrow hcol`. Establish `hO` using `GroundTheory.Global.isCompact_integralFiniteAdeles E`. Establish `hOo : (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (Af E)) ∈ 𝓝 (0 : Af E)` using `GroundTheory.Global.isOpen_integralFiniteAdeles.mem_nhds (zero_mem _)`. Use `set KY : Set (Matrix (Fin (r + 1)) (Fin (m + 1)) (Af E)) := {Y | ∀ i j, Y i j ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E} with hKY`. Establish `hK : IsCompact KY`.

Use `isCompact_pi_infinite (X := fun _ : Fin (r + 1) => Fin (m + 1) → Af E) (fun _ => isCompact_pi_infinite (fun _ : Fin (m + 1) => hO))` as an intermediate fact. Conclude with `this`. Establish `h1 : ∀ᶠ k in 𝓝 (1 : GL (Fin (m + r + 1 + 1)) (Af E)), ∀ Y ∈ KY, (∀ w ∉ S, Matrix.GeneralLinearGroup.map (pLoc E w) k = 1) → IsUnit (Dof (conjLowUni Y k.val)).det ∧ mkGL (Dof (conjLowUni Y k.val)) ∈ Ub ∧ mkGL (Scof (conjLowUni Y k.val)) ∈ Uβ ∧ ∀ i j, Yof (conjLowUni Y k.val) i j ∈ …`. Use `hK.eventually_forall_of_forall_eventually fun Y _ => ?_` and prove the remaining obligations. Take `⟨a, b⟩` from `conj_near S id continuous_id Y`.

Take `⟨c1, c2, c3, c4, -⟩` from `blocks_near S a b`. Use `eventually_inf_principal.1 (c1.and ((c2.eventually (hb.mem_nhds Ub.one_mem)).and ((c3.eventually (hβ.mem_nhds Uβ.one_mem)).and ?_)))` and prove the remaining obligations. Use `eventually_all.2 fun i => eventually_all.2 fun j => ?_` and prove the remaining obligations. Conclude with `(((continuous_id.matrix_elem i j).tendsto 0).comp c4).eventually hOo`. Establish `h2 : ∀ᶠ k in 𝓝 (1 : GL (Fin (m + r + 1 + 1)) (Af E)), ∀ z ∈ KY ×ˢ (Krow ×ˢ Kcol), (∀ w ∉ S, Matrix.GeneralLinearGroup.map (pLoc E w) k = 1) → (∑ j, ∑ l, z.2.1 j * Xof (conjLowUni z.1 k.val) j l * z.2.2 l) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E`.

Use `(hK.prod (hrow.prod hcol)).eventually_forall_of_forall_eventually fun z₀ _ => ?_` and prove the remaining obligations. Take `⟨a, b⟩` from `conj_near S Prod.fst continuous_fst z₀`. Take `⟨-, -, -, -, c⟩` from `blocks_near S a b`. Use `eventually_inf_principal.1 (Tendsto.eventually (p := fun x => x ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) ?_ hOo)` and prove the remaining obligations. Establish `hc : Continuous fun t : Matrix (Fin (m + 1)) (Fin (r + 1)) (Af E) × (Fin (m + 1) → Af E) × (Fin (r + 1) → Af E) => ∑ j, ∑ l, t.2.1 j * t.1 j l * t.2.2 l` using `by fun_prop`.

Establish `h3` using `(hc.tendsto (0, z₀.2)).comp (c.prodMk_nhds (((continuous_snd.comp continuous_snd).tendsto (1, z₀)).mono_left inf_le_left))`. Simplify using `only [Matrix.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero] at h3`. Conclude with `h3`. Use `⟨_, h1.and h2, fun k hk hS Y hY => ?_⟩` and prove the remaining obligations. Take `⟨a, b, c, d⟩` from `hk.1 Y hY hS`.

Conclude with `⟨a, b, c, d, fun ρ hρ γ hγ => hk.2 (Y, ρ, γ) ⟨hY, hρ, hγ⟩ hS⟩`.
-/
theorem blocks_small : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (Uβ : Subgroup (GL (Fin (m + 1)) (Af E))) (Ub : Subgroup (GL (Fin (r + 1)) (Af E))), IsOpen (Uβ : Set (GL (Fin (m + 1)) (Af E))) → IsOpen (Ub : Set (GL (Fin (r + 1)) (Af E))) → ∀ (Krow : Set (Fin (m + 1) → Af E)) (Kcol : Set (Fin (r + 1) → Af E)), IsCompact Krow → IsCompact Kcol → ∃ W ∈ 𝓝 (1 : GL (Fin (m + r + 1 + 1)) (Af E)), ∀ k ∈ W, (∀ w ∉ S, Matrix.GeneralLinearGroup.map (pLoc E w) k = 1) → ∀ Y : Matrix (Fin (r + 1)) (Fin (m + 1)) (Af E), (∀ i j, Y i j ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) → IsUnit (Dof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))).det ∧ mkGL (Dof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))) ∈ Ub ∧ mkGL (Scof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))) ∈ Uβ ∧ (∀ i j, Yof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) i j ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) ∧ ∀ ρ ∈ Krow, ∀ γ ∈ Kcol, (∑ j, ∑ l, ρ j * Xof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) j l * γ l) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E := by
  intro E _ _ m r S Uβ Ub hβ hb Krow Kcol hrow hcol
  have hO := GroundTheory.Global.isCompact_integralFiniteAdeles E
  have hOo : (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (Af E)) ∈ 𝓝 (0 : Af E) :=
    GroundTheory.Global.isOpen_integralFiniteAdeles.mem_nhds (zero_mem _)
  set KY : Set (Matrix (Fin (r + 1)) (Fin (m + 1)) (Af E)) :=
    {Y | ∀ i j, Y i j ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E} with hKY
  have hK : IsCompact KY := by
    have := isCompact_pi_infinite (X := fun _ : Fin (r + 1) => Fin (m + 1) → Af E)
      (fun _ => isCompact_pi_infinite (fun _ : Fin (m + 1) => hO))
    exact this
  have h1 : ∀ᶠ k in 𝓝 (1 : GL (Fin (m + r + 1 + 1)) (Af E)), ∀ Y ∈ KY,
      (∀ w ∉ S, Matrix.GeneralLinearGroup.map (pLoc E w) k = 1) →
      IsUnit (Dof (conjLowUni Y k.val)).det ∧ mkGL (Dof (conjLowUni Y k.val)) ∈ Ub ∧
        mkGL (Scof (conjLowUni Y k.val)) ∈ Uβ ∧
        ∀ i j, Yof (conjLowUni Y k.val) i j ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E := by
    refine hK.eventually_forall_of_forall_eventually fun Y _ => ?_
    obtain ⟨a, b⟩ := conj_near S id continuous_id Y
    obtain ⟨c1, c2, c3, c4, -⟩ := blocks_near S a b
    refine eventually_inf_principal.1 (c1.and ((c2.eventually (hb.mem_nhds Ub.one_mem)).and
      ((c3.eventually (hβ.mem_nhds Uβ.one_mem)).and ?_)))
    refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
    exact (((continuous_id.matrix_elem i j).tendsto 0).comp c4).eventually hOo
  have h2 : ∀ᶠ k in 𝓝 (1 : GL (Fin (m + r + 1 + 1)) (Af E)), ∀ z ∈ KY ×ˢ (Krow ×ˢ Kcol),
      (∀ w ∉ S, Matrix.GeneralLinearGroup.map (pLoc E w) k = 1) →
      (∑ j, ∑ l, z.2.1 j * Xof (conjLowUni z.1 k.val) j l * z.2.2 l) ∈
        GroundTheory.Global.integralFiniteAdeles (𝓞 E) E := by
    refine (hK.prod (hrow.prod hcol)).eventually_forall_of_forall_eventually fun z₀ _ => ?_
    obtain ⟨a, b⟩ := conj_near S Prod.fst continuous_fst z₀
    obtain ⟨-, -, -, -, c⟩ := blocks_near S a b
    refine eventually_inf_principal.1 (Tendsto.eventually (p := fun x => x ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) ?_ hOo)
    have hc : Continuous fun t : Matrix (Fin (m + 1)) (Fin (r + 1)) (Af E) × (Fin (m + 1) → Af E) × (Fin (r + 1) → Af E) =>
        ∑ j, ∑ l, t.2.1 j * t.1 j l * t.2.2 l := by fun_prop
    have h3 := (hc.tendsto (0, z₀.2)).comp (c.prodMk_nhds
      (((continuous_snd.comp continuous_snd).tendsto (1, z₀)).mono_left inf_le_left))
    simp only [Matrix.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero] at h3
    exact h3
  refine ⟨_, h1.and h2, fun k hk hS Y hY => ?_⟩
  obtain ⟨a, b, c, d⟩ := hk.1 Y hY hS
  exact ⟨a, b, c, d, fun ρ hρ γ hγ => hk.2 (Y, ρ, γ) ⟨hY, hρ, hγ⟩ hS⟩

end GlobalTheory.SchurNear
