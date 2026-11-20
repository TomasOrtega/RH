import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNonzeroIntSmulMemOfIsLattice

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.InertSph Matrix Filter
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LatAlmostAll

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

/- English proof (translation)
The claim follows from `a.2.2`.
-/
theorem eventually_integral (a : AF F) : ∀ᶠ v : Pl F in cofinite, evFin F v a ∈ v.adicCompletionIntegers F :=
  a.2.2

/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, hv, y, hy, rfl⟩` from `hz`. Rewrite using `[smul_smul]`. Use `AddSubgroup.subset_closure ⟨b * a, ?_, ?_, y, hy, rfl⟩` and prove the remaining obligations.

Introduce `u hu`. Rewrite using `[smul_eq_mul, mul_left_comm, ← smul_eq_mul u a, ha u hu, mul_zero]`. Rewrite using `[map_mul]`. Conclude with `mul_mem hb hv`. Consider the case `zero => rw [smul_zero]`.

Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [smul_neg]`. Conclude with `neg_mem hx`.
-/
theorem smul_mem_latAt (X : Spc F E n) (w : Pl F) {b : AF F} (hb : evFin F w b ∈ w.adicCompletionIntegers F)
    {z : Fin n → AE F E} (hz : z ∈ latAt X w) : b • z ∈ latAt X w := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hv, y, hy, rfl⟩ := hz
    rw [smul_smul]
    refine AddSubgroup.subset_closure ⟨b * a, ?_, ?_, y, hy, rfl⟩
    · intro u hu
      rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u a, ha u hu, mul_zero]
    · rw [map_mul]
      exact mul_mem hb hv
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.IntSmulMemLatticeTwistedOperators.exists_nonzero_int_smul_mem_of_isLattice`. Consider the case `exact _root_.GlobalTheory.IntSmulMemLatticeTwistedOperators.exists_nonzero_int_smul_mem_of_isLattice`. Consider the case `(apply _root_.GlobalTheory.IntSmulMemLatticeTwistedOperators.exists_nonzero_int_smul_mem_of_isLattice <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.IntSmulMemLatticeTwistedOperators.exists_nonzero_int_smul_mem_of_isLattice <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.IntSmulMemLatticeTwistedOperators.exists_nonzero_int_smul_mem_of_isLattice <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.IntSmulMemLatticeTwistedOperators.exists_nonzero_int_smul_mem_of_isLattice ..)`.
-/
theorem exists_int_smul_mem (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsLattice E) (v : Fin n → E) :
    ∃ c : ℤ, c ≠ 0 ∧ c • v ∈ L := by
  first
  | exact @_root_.GlobalTheory.IntSmulMemLatticeTwistedOperators.exists_nonzero_int_smul_mem_of_isLattice
  | exact _root_.GlobalTheory.IntSmulMemLatticeTwistedOperators.exists_nonzero_int_smul_mem_of_isLattice
  | (apply _root_.GlobalTheory.IntSmulMemLatticeTwistedOperators.exists_nonzero_int_smul_mem_of_isLattice <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntSmulMemLatticeTwistedOperators.exists_nonzero_int_smul_mem_of_isLattice <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntSmulMemLatticeTwistedOperators.exists_nonzero_int_smul_mem_of_isLattice <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntSmulMemLatticeTwistedOperators.exists_nonzero_int_smul_mem_of_isLattice ..)

/- English proof (translation)
Establish `key : ∀ L' : Submodule (𝓞 E) (Fin n → E), L'.FG → ∃ c : ℤ, c ≠ 0 ∧ ∀ y ∈ L', c • (N *ᵥ y) ∈ L`. Introduce `L' hL'`. Proceed by induction on `L', hL' using Submodule.fg_induction with`. Consider the case `singleton x`. Take `⟨c, hc, hx⟩` from `exists_int_smul_mem L hL (N *ᵥ x)`.

Use `⟨c, hc, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨r, rfl⟩` from `Submodule.mem_span_singleton.1 hy`. Rewrite using `[Matrix.mulVec_smul, smul_comm]`. Conclude with `L.smul_mem r hx`. Consider the case `sup A B _ _ hA hB`.

Take `⟨c, hc, hA⟩` from `hA`. Take `⟨d, hd, hB⟩` from `hB`. Use `⟨c * d, mul_ne_zero hc hd, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 hy`. Rewrite using `[Matrix.mulVec_add, smul_add]`.

Use `add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`. Conclude with `zsmul_mem (hA a ha) d`. Rewrite using `[mul_smul]`. Conclude with `zsmul_mem (hB b hb) c`.

Conclude with `key L hL.fg`.
-/
theorem exists_int_mulVec_mem (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsLattice E) (N : Matrix (Fin n) (Fin n) E) :
    ∃ c : ℤ, c ≠ 0 ∧ ∀ y ∈ L, c • (N *ᵥ y) ∈ L := by
  have key : ∀ L' : Submodule (𝓞 E) (Fin n → E), L'.FG → ∃ c : ℤ, c ≠ 0 ∧ ∀ y ∈ L', c • (N *ᵥ y) ∈ L := by
    intro L' hL'
    induction L', hL' using Submodule.fg_induction with
    | singleton x =>
      obtain ⟨c, hc, hx⟩ := exists_int_smul_mem L hL (N *ᵥ x)
      refine ⟨c, hc, fun y hy => ?_⟩
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [Matrix.mulVec_smul, smul_comm]
      exact L.smul_mem r hx
    | sup A B _ _ hA hB =>
      obtain ⟨c, hc, hA⟩ := hA
      obtain ⟨d, hd, hB⟩ := hB
      refine ⟨c * d, mul_ne_zero hc hd, fun y hy => ?_⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
      rw [Matrix.mulVec_add, smul_add]
      refine add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact zsmul_mem (hA a ha) d
      · rw [mul_smul]; exact zsmul_mem (hB b hb) c
  exact key L hL.fg

/- English proof (translation)
Take `⟨c, hc, hN⟩` from `exists_int_mulVec_mem X.L hL N`. Use `filter_upwards [eventually_integral (algebraMap F (AF F) (c : F)⁻¹)] with w hw z hz`. Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, hv, y, hy, rfl⟩` from `hz`.

Establish `h1 : (a • fun i => inclR (F` using `F) (AF F) ((c • (N *ᵥ y)) i)) ∈ latAt X w := AddSubgroup.subset_closure ⟨a, ha, hv, _, hN y hy, rfl⟩`. Establish `h2` using `smul_mem_latAt X w hw h1`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[Matrix.mulVec_smul, smul_comm]`. Use `congr 1`.

Use extensionality with `i`. Establish `hc' : (c : F) ≠ 0` using `Int.cast_ne_zero.2 hc`. Establish `h3 : (incM F N *ᵥ fun i => inclR (F` using `F) (AF F) (y i)) i = inclR (F := F) (AF F) ((N *ᵥ y) i) := (RingHom.map_mulVec (inclR (F := F) (AF F)) N y i).symm`. Rewrite using `[h3, Pi.smul_apply, Pi.smul_apply, map_zsmul, algebraMap_smul, ← Int.cast_smul_eq_zsmul F, smul_smul, inv_mul_cancel₀ hc', one_smul]`. Consider the case `zero => rw [Matrix.mulVec_zero]`.

Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [Matrix.mulVec_add]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [Matrix.mulVec_neg]`. Conclude with `neg_mem hx`.
-/
theorem eventually_incM (X : Spc F E n) (hL : X.L.IsLattice E) (N : Matrix (Fin n) (Fin n) E) :
    ∀ᶠ w : Pl F in cofinite, ∀ z ∈ latAt X w, incM F N *ᵥ z ∈ latAt X w := by
  obtain ⟨c, hc, hN⟩ := exists_int_mulVec_mem X.L hL N
  filter_upwards [eventually_integral (algebraMap F (AF F) (c : F)⁻¹)] with w hw z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hv, y, hy, rfl⟩ := hz
    have h1 : (a • fun i => inclR (F := F) (AF F) ((c • (N *ᵥ y)) i)) ∈ latAt X w :=
      AddSubgroup.subset_closure ⟨a, ha, hv, _, hN y hy, rfl⟩
    have h2 := smul_mem_latAt X w hw h1
    convert h2 using 1
    rw [Matrix.mulVec_smul, smul_comm]
    congr 1
    ext i
    have hc' : (c : F) ≠ 0 := Int.cast_ne_zero.2 hc
    have h3 : (incM F N *ᵥ fun i => inclR (F := F) (AF F) (y i)) i = inclR (F := F) (AF F) ((N *ᵥ y) i) :=
      (RingHom.map_mulVec (inclR (F := F) (AF F)) N y i).symm
    rw [h3, Pi.smul_apply, Pi.smul_apply, map_zsmul, algebraMap_smul, ← Int.cast_smul_eq_zsmul F, smul_smul,
      inv_mul_cancel₀ hc', one_smul]
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mulVec_neg]; exact neg_mem hx

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => exact Eventually.of_forall fun w z _ => by simp [zero_mem]`. Consider the case `tmul a e`. Establish `h : Matrix.single i j (a ⊗ₜ[F] e : AE F E) = a • incM F (Matrix.single i j e)`. Use extensionality with `k l`.

Simplify using `only [incM, Matrix.smul_apply, Matrix.map_apply, Matrix.single_apply]`. Use `split_ifs`. Simplify using `[inclR, TensorProduct.smul_tmul']`. Simplify using the standard rewrite rules. Use `filter_upwards [eventually_integral a, eventually_incM X hL (Matrix.single i j e)] with w hw h2 z hz`.

Rewrite using `[h, Matrix.smul_mulVec]`. Conclude with `smul_mem_latAt X w hw (h2 z hz)`. Consider the case `add s t hs ht => filter_upwards [hs, ht] with w h1 h2 z hz`. Rewrite using `[Matrix.single_add, Matrix.add_mulVec]`. Conclude with `add_mem (h1 z hz) (h2 z hz)`.
-/
theorem eventually_single (X : Spc F E n) (hL : X.L.IsLattice E) (i j : Fin n) (t : AE F E) :
    ∀ᶠ w : Pl F in cofinite, ∀ z ∈ latAt X w, Matrix.single i j t *ᵥ z ∈ latAt X w := by
  induction t using TensorProduct.induction_on with
  | zero => exact Eventually.of_forall fun w z _ => by simp [zero_mem]
  | tmul a e =>
    have h : Matrix.single i j (a ⊗ₜ[F] e : AE F E) = a • incM F (Matrix.single i j e) := by
      ext k l
      simp only [incM, Matrix.smul_apply, Matrix.map_apply, Matrix.single_apply]
      split_ifs
      · simp [inclR, TensorProduct.smul_tmul']
      · simp
    filter_upwards [eventually_integral a, eventually_incM X hL (Matrix.single i j e)] with w hw h2 z hz
    rw [h, Matrix.smul_mulVec]
    exact smul_mem_latAt X w hw (h2 z hz)
  | add s t hs ht =>
    filter_upwards [hs, ht] with w h1 h2 z hz
    rw [Matrix.single_add, Matrix.add_mulVec]
    exact add_mem (h1 z hz) (h2 z hz)

/- English proof (translation)
Establish `h : ∀ᶠ w : Pl F in cofinite, ∀ i j, ∀ z ∈ latAt X w, Matrix.single i j (M i j) *ᵥ z ∈ latAt X w` using `eventually_all.2 fun i => eventually_all.2 fun j => eventually_single X hL i j (M i j)`. Use `filter_upwards [h] with w hw z hz`. Rewrite using `[Matrix.matrix_eq_sum_single M, Matrix.sum_mulVec]`. Use `sum_mem fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.sum_mulVec]`.

Conclude with `sum_mem fun j _ => hw i j z hz`.
-/
theorem eventually_mulVec_mem (X : Spc F E n) (hL : X.L.IsLattice E) (M : Matrix (Fin n) (Fin n) (AE F E)) :
    ∀ᶠ w : Pl F in cofinite, ∀ z ∈ latAt X w, M *ᵥ z ∈ latAt X w := by
  have h : ∀ᶠ w : Pl F in cofinite, ∀ i j, ∀ z ∈ latAt X w, Matrix.single i j (M i j) *ᵥ z ∈ latAt X w :=
    eventually_all.2 fun i => eventually_all.2 fun j => eventually_single X hL i j (M i j)
  filter_upwards [h] with w hw z hz
  rw [Matrix.matrix_eq_sum_single M, Matrix.sum_mulVec]
  refine sum_mem fun i _ => ?_
  rw [Matrix.sum_mulVec]
  exact sum_mem fun j _ => hw i j z hz

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n X hL g`. Establish `h` using `(eventually_mulVec_mem X hL (mat g)).and (eventually_mulVec_mem X hL (mat g⁻¹))`. Use `⟨(eventually_cofinite.1 h).toFinset, fun w hw z hz => ?_⟩` and prove the remaining obligations. Simplify using `only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hw`. Conclude with `⟨hw.1 z hz, hw.2 z hz⟩`.
-/
theorem exists_finset_keeps : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n), X.L.IsLattice E → ∀ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J,
    ∃ S₁ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), ∀ w ∉ S₁, ∀ z ∈ GlobalTheory.InertSph.latAt X w,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g *ᵥ z ∈ GlobalTheory.InertSph.latAt X w ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g⁻¹ *ᵥ z ∈ GlobalTheory.InertSph.latAt X w := by
  intro F E _ _ _ _ _ σ n X hL g
  have h := (eventually_mulVec_mem X hL (mat g)).and (eventually_mulVec_mem X hL (mat g⁻¹))
  refine ⟨(eventually_cofinite.1 h).toFinset, fun w hw z hz => ?_⟩
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hw
  exact ⟨hw.1 z hz, hw.2 z hz⟩

end GlobalTheory.LatAlmostAll
