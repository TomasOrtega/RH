import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE
import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactStandardMaximalStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.CompanionTheory.Iwasawa

/- English proof (translation)
Use `continuous_iff_isClosed.2 fun C hC => ?_` and prove the remaining obligations. Establish `hD : IsClosed (P ∩ f ⁻¹' C)` using `hf.preimage_isClosed_of_isClosed hP hC`. Use `hD.mul_right_of_isCompact hK using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Take `⟨p, hp, k, hk, rfl⟩` from `hd x`. Conclude with `Set.mem_mul.2 ⟨p, ⟨hp, by simpa [Set.mem_preimage, hv p hp k hk] using hx⟩, k, hk, rfl⟩`. Introduce and unpack `⟨p, ⟨hp, hc⟩, k, hk, rfl⟩`. Simplify `hc` using `[Set.mem_preimage, hv p hp k hk]`.
-/
theorem continuous_of_mul_compact {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {P K : Set G} {f : G → ℝ}
    (hP : IsClosed P) (hK : IsCompact K) (hf : ContinuousOn f P)
    (hd : ∀ x, ∃ p ∈ P, ∃ k ∈ K, x = p * k) (hv : ∀ p ∈ P, ∀ k ∈ K, f (p * k) = f p) : Continuous f := by
  refine continuous_iff_isClosed.2 fun C hC => ?_
  have hD : IsClosed (P ∩ f ⁻¹' C) := hf.preimage_isClosed_of_isClosed hP hC
  convert hD.mul_right_of_isCompact hK using 1
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp, k, hk, rfl⟩ := hd x
    exact Set.mem_mul.2 ⟨p, ⟨hp, by simpa [Set.mem_preimage, hv p hp k hk] using hx⟩, k, hk, rfl⟩
  · rintro ⟨p, ⟨hp, hc⟩, k, hk, rfl⟩
    simpa [Set.mem_preimage, hv p hp k hk] using hc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

/- English proof (translation)
The claim follows from `GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)`.
-/
theorem topRing_AE : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)

/- English proof (translation)
Use `haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F`. Conclude with `GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := AF F)`.
-/
theorem t2Space_cm_host_adeles : T2Space (AE F E) := by
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  exact GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := AF F)

/- English proof (translation)
Use `haveI := topRing_AE (F := F) (E := E)`. Use `infer_instance`.
-/
theorem topologicalGroup_unitary_double : IsTopologicalGroup (G2 σ Y) := by
  haveI := topRing_AE (F := F) (E := E)
  infer_instance

def parT (x : G2 σ Y) : Matrix (Fin n) (Fin n) (AE F E) := (mat2 x * dC n (AE F E)).toRows₁

/- English proof (translation)
The claim follows from `Units.continuous_val.comp continuous_subtype_val`.
-/
theorem continuous_mat2 : Continuous (mat2 : G2 σ Y → _) :=
  Units.continuous_val.comp continuous_subtype_val

/- English proof (translation)
Use `haveI := topRing_AE (F := F) (E := E)`. Establish `h : Continuous fun x : G2 σ Y => mat2 x * dC n (AE F E)` using `continuous_mat2.matrix_mul continuous_const`. Conclude with `continuous_matrix fun i j => h.matrix_elem _ _`.
-/
theorem continuous_parT : Continuous (parT : G2 σ Y → _) := by
  haveI := topRing_AE (F := F) (E := E)
  have h : Continuous fun x : G2 σ Y => mat2 x * dC n (AE F E) := continuous_mat2.matrix_mul continuous_const
  exact continuous_matrix fun i j => h.matrix_elem _ _

/- English proof (translation)
Rewrite using `[parT, isPar_iff.1 h, dC, diagCols, Matrix.fromRows_mul, Matrix.one_mul, Matrix.toRows₁_fromRows]`.
-/
theorem parT_eq {p : G2 σ Y} {t : GL (Fin n) (AE F E)} (h : IsPar p t) : parT p = t.1 := by
  rw [parT, isPar_iff.1 h, dC, diagCols, Matrix.fromRows_mul, Matrix.one_mul, Matrix.toRows₁_fromRows]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, h⟩`. Establish `h'` using `IsPar.inv h`. Rewrite using `[parT_eq h, parT_eq h']`. Conclude with `⟨isPar_iff.1 h, isPar_iff.1 h', Units.mul_inv t, Units.inv_mul t⟩`.

Introduce and unpack `⟨h1, -, h3, h4⟩`. Conclude with `⟨⟨parT x, parT x⁻¹, h3, h4⟩, isPar_iff.2 h1⟩`.
-/
theorem exists_isPar_iff {x : G2 σ Y} : (∃ t, IsPar x t) ↔ mat2 x * dC n (AE F E) = dC n (AE F E) * parT x ∧
    mat2 x⁻¹ * dC n (AE F E) = dC n (AE F E) * parT x⁻¹ ∧ parT x * parT x⁻¹ = 1 ∧ parT x⁻¹ * parT x = 1 := by
  constructor
  · rintro ⟨t, h⟩
    have h' := IsPar.inv h
    rw [parT_eq h, parT_eq h']
    exact ⟨isPar_iff.1 h, isPar_iff.1 h', Units.mul_inv t, Units.inv_mul t⟩
  · rintro ⟨h1, -, h3, h4⟩
    exact ⟨⟨parT x, parT x⁻¹, h3, h4⟩, isPar_iff.2 h1⟩

/- English proof (translation)
Use `haveI := topRing_AE (F := F) (E := E)`. Use `haveI := t2Space_cm_host_adeles (F := F) (E := E)`. Use `haveI := topologicalGroup_unitary_double (σ := σ) (Y := Y)`. Establish `ci : Continuous fun x : G2 σ Y => parT x⁻¹` using `continuous_parT.comp continuous_inv`. Establish `cm : Continuous fun x : G2 σ Y => mat2 x⁻¹` using `continuous_mat2.comp continuous_inv`.

Establish `e : (par2 σ Y : Set (G2 σ Y)) = {x | mat2 x * dC n (AE F E) = dC n (AE F E) * parT x} ∩ ({x | mat2 x⁻¹ * dC n (AE F E) = dC n (AE F E) * parT x⁻¹} ∩ ({x | parT x * parT x⁻¹ = 1} ∩ {x | parT x⁻¹ * parT x = 1}))`. Use extensionality with `x`. Conclude with `mem_parabolic_GL2_iff.trans exists_isPar_iff`. Rewrite using `[e]`. Conclude with `(isClosed_eq (continuous_mat2.matrix_mul continuous_const) (continuous_const.matrix_mul continuous_parT)).inter ((isClosed_eq (cm.matrix_mul continuous_const) (continuous_const.matrix_mul ci)).inter ((isClosed_eq (continuous_parT.matrix_mul ci) continuous_const).inter (isClosed_e …`.
-/
theorem isClosed_siegel_stabiliser : IsClosed (par2 σ Y : Set (G2 σ Y)) := by
  haveI := topRing_AE (F := F) (E := E)
  haveI := t2Space_cm_host_adeles (F := F) (E := E)
  haveI := topologicalGroup_unitary_double (σ := σ) (Y := Y)
  have ci : Continuous fun x : G2 σ Y => parT x⁻¹ := continuous_parT.comp continuous_inv
  have cm : Continuous fun x : G2 σ Y => mat2 x⁻¹ := continuous_mat2.comp continuous_inv
  have e : (par2 σ Y : Set (G2 σ Y)) = {x | mat2 x * dC n (AE F E) = dC n (AE F E) * parT x} ∩
      ({x | mat2 x⁻¹ * dC n (AE F E) = dC n (AE F E) * parT x⁻¹} ∩
      ({x | parT x * parT x⁻¹ = 1} ∩ {x | parT x⁻¹ * parT x = 1})) := by
    ext x
    exact mem_parabolic_GL2_iff.trans exists_isPar_iff
  rw [e]
  exact (isClosed_eq (continuous_mat2.matrix_mul continuous_const) (continuous_const.matrix_mul continuous_parT)).inter
    ((isClosed_eq (cm.matrix_mul continuous_const) (continuous_const.matrix_mul ci)).inter
    ((isClosed_eq (continuous_parT.matrix_mul ci) continuous_const).inter
    (isClosed_eq (ci.matrix_mul continuous_parT) continuous_const)))

def parU (p : par2 σ Y) : GL (Fin n) (AE F E) :=
  ⟨parT p.1, parT p.1⁻¹, (exists_isPar_iff.1 (mem_parabolic_GL2_iff.1 p.2)).2.2.1, (exists_isPar_iff.1 (mem_parabolic_GL2_iff.1 p.2)).2.2.2⟩

/- English proof (translation)
The claim follows from `isPar_iff.2 (exists_isPar_iff.1 (mem_parabolic_GL2_iff.1 p.2)).1`.
-/
theorem isPar_parU (p : par2 σ Y) : IsPar p.1 (parU p) := isPar_iff.2 (exists_isPar_iff.1 (mem_parabolic_GL2_iff.1 p.2)).1

/- English proof (translation)
Use `haveI := topRing_AE (F := F) (E := E)`. Use `haveI := topologicalGroup_unitary_double (σ := σ) (Y := Y)`. Conclude with `Units.continuous_iff.2 ⟨continuous_parT.comp continuous_subtype_val, continuous_parT.comp (continuous_inv.comp continuous_subtype_val)⟩`.
-/
theorem continuous_parU : Continuous (parU : par2 σ Y → GL (Fin n) (AE F E)) := by
  haveI := topRing_AE (F := F) (E := E)
  haveI := topologicalGroup_unitary_double (σ := σ) (Y := Y)
  exact Units.continuous_iff.2 ⟨continuous_parT.comp continuous_subtype_val,
    continuous_parT.comp (continuous_inv.comp continuous_subtype_val)⟩

/- English proof (translation)
Use `haveI := topRing_AE (F := F) (E := E)`. Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `Units.continuous_val.matrix_det`. Conclude with `Units.continuous_coe_inv.matrix_det`.
-/
theorem continuous_detGL : Continuous (Matrix.GeneralLinearGroup.det : GL (Fin n) (AE F E) → (AE F E)ˣ) := by
  haveI := topRing_AE (F := F) (E := E)
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_det
  · exact Units.continuous_coe_inv.matrix_det

/- English proof (translation)
Use `haveI := topologicalGroup_unitary_double (σ := σ) (Y := Y)`. Establish `v1 : ∀ p t, IsPar p t → a p = (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ)` using `fun p t h => by`. Simplify using `using ha.val p t h 1 K.one_mem`. Use `⟨continuous_of_mul_compact (P := par2 σ Y) isClosed_siegel_stabiliser hK ?_ ?_ ?_, fun x => ?_⟩` and prove the remaining obligations. Use `continuousOn_iff_continuous_restrict.2 ?_` and prove the remaining obligations.

Conclude with `(NNReal.continuous_coe.comp (GlobalTheory.Doubling.continuous_absE.comp (continuous_detGL.comp continuous_parU))).congr fun p => (v1 _ _ (isPar_parU p)).symm`. Introduce `x`. Take `⟨p, t, h, k, hk, e⟩` from `ha.iwa x`. Conclude with `⟨p, mem_parabolic_GL2_iff.2 ⟨t, h⟩, k, hk, e⟩`. Introduce `p hp k hk`.

Take `⟨t, h⟩` from `mem_parabolic_GL2_iff.1 hp`. Rewrite using `[ha.val p t h k hk, v1 p t h]`. Take `⟨p, t, h, k, hk, rfl⟩` from `ha.iwa x`. Rewrite using `[ha.val p t h k hk]`. Establish `u : absE F E (Matrix.GeneralLinearGroup.det t) ≠ 0` using `fun h0 => by`.

Establish `e` using `map_mul (absE F E) (Matrix.GeneralLinearGroup.det t) (Matrix.GeneralLinearGroup.det t)⁻¹`. Rewrite `e` using `[mul_inv_cancel, map_one, h0, zero_mul]`. Conclude with `one_ne_zero e`. Conclude with `pos_iff_ne_zero.2 u` after adjusting the coercions.
-/
theorem continuous_pos {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ}
    (hK : IsCompact (K : Set (G2 σ Y))) (ha : IsHgt K a) : Continuous a ∧ ∀ x, 0 < a x := by
  haveI := topologicalGroup_unitary_double (σ := σ) (Y := Y)
  have v1 : ∀ p t, IsPar p t → a p = (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) := fun p t h => by
    simpa using ha.val p t h 1 K.one_mem
  refine ⟨continuous_of_mul_compact (P := par2 σ Y) isClosed_siegel_stabiliser hK ?_ ?_ ?_, fun x => ?_⟩
  · refine continuousOn_iff_continuous_restrict.2 ?_
    exact (NNReal.continuous_coe.comp (GlobalTheory.Doubling.continuous_absE.comp (continuous_detGL.comp continuous_parU))).congr
      fun p => (v1 _ _ (isPar_parU p)).symm
  · intro x
    obtain ⟨p, t, h, k, hk, e⟩ := ha.iwa x
    exact ⟨p, mem_parabolic_GL2_iff.2 ⟨t, h⟩, k, hk, e⟩
  · intro p hp k hk
    obtain ⟨t, h⟩ := mem_parabolic_GL2_iff.1 hp
    rw [ha.val p t h k hk, v1 p t h]
  · obtain ⟨p, t, h, k, hk, rfl⟩ := ha.iwa x
    rw [ha.val p t h k hk]
    have u : absE F E (Matrix.GeneralLinearGroup.det t) ≠ 0 := fun h0 => by
      have e := map_mul (absE F E) (Matrix.GeneralLinearGroup.det t) (Matrix.GeneralLinearGroup.det t)⁻¹
      rw [mul_inv_cancel, map_one, h0, zero_mul] at e
      exact one_ne_zero e
    exact_mod_cast pos_iff_ne_zero.2 u

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n Y r s hB hn hY b K a hb hK ha` and use `continuous_pos (GlobalTheory.T.isCompact_standard_maximal F E σ B n Y r s hB hn hY b K a hb hK ha) ha`.
-/
theorem height_continuous_pos : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → Continuous a ∧ ∀ x, 0 < a x :=
  fun F E _ _ _ _ _ σ B n Y r s hB hn hY b K a hb hK ha =>
    continuous_pos (GlobalTheory.T.isCompact_standard_maximal F E σ B n Y r s hB hn hY b K a hb hK ha) ha

end GlobalTheory.CompanionTheory.Iwasawa
