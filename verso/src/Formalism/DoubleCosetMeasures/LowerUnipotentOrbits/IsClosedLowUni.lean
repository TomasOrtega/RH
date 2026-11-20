import Formalism.DoubleCosetMeasures.Statement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.GLRealOpen
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.GlR

open MeasureTheory Measure Topology Matrix

namespace Formalism.DoubleCosetMeasures.P

namespace GeneralLinearIntegersOpenCompact

/- English proof (translation)
Establish `hint : (interior (K₁ : Set G)).Nonempty` using `⟨1, by rw [hKo.interior_eq]; exact K₁.one_mem⟩`. Set `K₀ : TopologicalSpace.PositiveCompacts G` to `⟨⟨K₁, hKc⟩, hint⟩`. Establish `: LocallyCompactSpace G` using `hKc.locallyCompactSpace_of_mem_nhds_of_group (hKo.mem_nhds K₁.one_mem)`. Establish `: SigmaCompactSpace G` using `⟨⟨fun m => (L m : Set G), hLc, Set.eq_univ_of_forall fun g => Set.mem_iUnion.2 (hcov g)⟩⟩`. Use `⟨haarMeasure K₀, inferInstance, ?_, inferInstance, haarMeasure_self⟩` and prove the remaining obligations.

Prove the components needed by the constructor for the conclusion. Introduce `g`. Take `⟨m, hm⟩` from `hcov g`. Establish `hreg : (Measure.map (· * g) (haarMeasure K₀)).Regular` using `Regular.map (Homeomorph.mulRight g)`. Establish `e` using `isMulLeftInvariant_eq_smul_of_regular (Measure.map (· * g) (haarMeasure K₀)) (haarMeasure K₀)`.

Establish `hL : Measure.map (· * g) (haarMeasure K₀) (L m) = haarMeasure K₀ (L m)`. Rewrite using `[map_apply (measurable_mul_const g) (hLo m).measurableSet]`. Use `congr 1`. Use extensionality with `x`. Simplify using `[Set.mem_preimage, (L m).mul_mem_cancel_right hm]`.

Establish `hpos : haarMeasure K₀ (L m) ≠ 0` using `((hLo m).measure_pos _ ⟨1, (L m).one_mem⟩).ne'`. Establish `hfin : haarMeasure K₀ (L m) ≠ ⊤` using `(hLc m).measure_lt_top.ne`. Establish `hc : haarScalarFactor (Measure.map (· * g) (haarMeasure K₀)) (haarMeasure K₀) = 1`. Establish `h2` using `congrArg (fun ν : Measure G => ν (L m)) e`. Simplify using `only [hL, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h2`.

Establish `h3 : (1 : ENNReal) * haarMeasure K₀ (L m) = (haarScalarFactor (Measure.map (· * g) (haarMeasure K₀)) (haarMeasure K₀) : ENNReal) * haarMeasure K₀ (L m)` using `by rw [one_mul]; exact h2`. Establish `h4` using `(ENNReal.mul_left_inj hpos hfin).1 h3`. Conclude with `h4.symm` after adjusting the coercions. Rewrite `e` using `[hc, one_smul]`. Conclude with `e`.
-/
theorem haar_of_cover {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] (K₁ : Subgroup G) (hKo : IsOpen (K₁ : Set G))
    (hKc : IsCompact (K₁ : Set G)) (L : ℕ → Subgroup G) (hLo : ∀ m, IsOpen (L m : Set G))
    (hLc : ∀ m, IsCompact (L m : Set G)) (hcov : ∀ g : G, ∃ m, g ∈ L m) :
    ∃ μ : Measure G, μ.IsMulLeftInvariant ∧ μ.IsMulRightInvariant ∧ SFinite μ ∧
      μ (K₁ : Set G) = 1 := by
  have hint : (interior (K₁ : Set G)).Nonempty := ⟨1, by rw [hKo.interior_eq]; exact K₁.one_mem⟩
  let K₀ : TopologicalSpace.PositiveCompacts G := ⟨⟨K₁, hKc⟩, hint⟩
  have : LocallyCompactSpace G :=
    hKc.locallyCompactSpace_of_mem_nhds_of_group (hKo.mem_nhds K₁.one_mem)
  have : SigmaCompactSpace G := ⟨⟨fun m => (L m : Set G), hLc,
    Set.eq_univ_of_forall fun g => Set.mem_iUnion.2 (hcov g)⟩⟩
  refine ⟨haarMeasure K₀, inferInstance, ?_, inferInstance, haarMeasure_self⟩
  constructor
  intro g
  obtain ⟨m, hm⟩ := hcov g
  have hreg : (Measure.map (· * g) (haarMeasure K₀)).Regular := Regular.map (Homeomorph.mulRight g)
  have e := isMulLeftInvariant_eq_smul_of_regular (Measure.map (· * g) (haarMeasure K₀)) (haarMeasure K₀)
  have hL : Measure.map (· * g) (haarMeasure K₀) (L m) = haarMeasure K₀ (L m) := by
    rw [map_apply (measurable_mul_const g) (hLo m).measurableSet]
    congr 1
    ext x
    simp [Set.mem_preimage, (L m).mul_mem_cancel_right hm]
  have hpos : haarMeasure K₀ (L m) ≠ 0 := ((hLo m).measure_pos _ ⟨1, (L m).one_mem⟩).ne'
  have hfin : haarMeasure K₀ (L m) ≠ ⊤ := (hLc m).measure_lt_top.ne
  have hc : haarScalarFactor (Measure.map (· * g) (haarMeasure K₀)) (haarMeasure K₀) = 1 := by
    have h2 := congrArg (fun ν : Measure G => ν (L m)) e
    simp only [hL, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h2
    have h3 : (1 : ENNReal) * haarMeasure K₀ (L m) =
        (haarScalarFactor (Measure.map (· * g) (haarMeasure K₀)) (haarMeasure K₀) : ENNReal) *
          haarMeasure K₀ (L m) := by rw [one_mul]; exact h2
    have h4 := (ENNReal.mul_left_inj hpos hfin).1 h3
    exact_mod_cast h4.symm
  rw [hc, one_smul] at e
  exact e

section Alg

variable {K : Type} [CommRing K]

noncomputable def glR (R : Subring K) (n : ℕ) : Subgroup (GL (Fin n) K) :=
  _root_.UpperTheory.Reformulated.B.GeneralLinearGroupOverSubring.glR R n

def Dg {n : ℕ} (δ : Fin n → Kˣ) : GL (Fin n) K :=
  ⟨Matrix.diagonal (fun a => (δ a : K)), Matrix.diagonal (fun a => (((δ a)⁻¹ : Kˣ) : K)),
    by rw [Matrix.diagonal_mul_diagonal]; simp, by rw [Matrix.diagonal_mul_diagonal]; simp⟩

/- English proof (translation)
Simplify using `only [Units.val_mul]`. Use `show (diagonal (fun a => (((δ a)⁻¹ : Kˣ) : K)) * (g : Matrix (Fin n) (Fin n) K) * diagonal (fun a => (δ a : K))) a b = _`. Rewrite using `[mul_diagonal, diagonal_mul]`.
-/
theorem conj_entry {n : ℕ} (δ : Fin n → Kˣ) (g : GL (Fin n) K) (a b : Fin n) :
    (((Dg δ)⁻¹ * g * Dg δ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b =
      (((δ a)⁻¹ : Kˣ) : K) * (g : Matrix (Fin n) (Fin n) K) a b * (δ b : K) := by
  simp only [Units.val_mul]
  show (diagonal (fun a => (((δ a)⁻¹ : Kˣ) : K)) * (g : Matrix (Fin n) (Fin n) K) *
    diagonal (fun a => (δ a : K))) a b = _
  rw [mul_diagonal, diagonal_mul]

/- English proof (translation)
Use `choose k hk using fun p : Fin n × Fin n => hx (x p.1 p.2)`. Use `⟨Finset.univ.sup k, fun m hm a b => ?_⟩` and prove the remaining obligations. Break down `hstr a b with h | ⟨rfl, h⟩ | h` into its components or cases. Simplify using `[h, R.zero_mem]`. Rewrite using `[h, mul_one, Units.inv_mul]`.

Conclude with `R.one_mem`. Take `⟨d, hd⟩ : ∃ d, e b = e a + (d + 1)` from `⟨e b - e a - 1, by omega⟩`. Establish `hk' : k (a, b) ≤ m * (d + 1)` using `le_trans (Finset.le_sup (f := k) (Finset.mem_univ (a, b))) (le_trans hm (Nat.le_mul_of_pos_right m (Nat.succ_pos d)))`. Establish `hu : (((ϖ ^ (m * e a))⁻¹ : Kˣ) : K) * ((ϖ ^ (m * e a) : Kˣ) : K) = 1` using `Units.inv_mul _`. Establish `eq : (((ϖ ^ (m * e a))⁻¹ : Kˣ) : K) * x a b * ((ϖ ^ (m * e b) : Kˣ) : K) = (ϖ : K) ^ (m * (d + 1) - k (a, b)) * ((ϖ : K) ^ k (a, b) * x a b)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hd, mul_add, pow_add, Units.val_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by`. Rewrite using `[hu, mul_one, Units.val_pow_eq_pow_val, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hk', mul_comm]`.

Rewrite using `[eq]`. Conclude with `R.mul_mem (R.pow_mem hϖ _) (hk (a, b))`.
-/
theorem exists_pow_int (R : Subring K) (ϖ : Kˣ) (hϖ : (ϖ : K) ∈ R)
    (hx : ∀ x : K, ∃ m : ℕ, (ϖ : K) ^ m * x ∈ R) {n : ℕ} (e : Fin n → ℕ)
    (x : Matrix (Fin n) (Fin n) K)
    (hstr : ∀ a b, x a b = 0 ∨ (a = b ∧ x a b = 1) ∨ e a < e b) :
    ∃ m0 : ℕ, ∀ m, m0 ≤ m → ∀ a b,
      (((ϖ ^ (m * e a))⁻¹ : Kˣ) : K) * x a b * ((ϖ ^ (m * e b) : Kˣ) : K) ∈ R := by
  choose k hk using fun p : Fin n × Fin n => hx (x p.1 p.2)
  refine ⟨Finset.univ.sup k, fun m hm a b => ?_⟩
  rcases hstr a b with h | ⟨rfl, h⟩ | h
  · simp [h, R.zero_mem]
  · rw [h, mul_one, Units.inv_mul]; exact R.one_mem
  · obtain ⟨d, hd⟩ : ∃ d, e b = e a + (d + 1) := ⟨e b - e a - 1, by omega⟩
    have hk' : k (a, b) ≤ m * (d + 1) :=
      le_trans (Finset.le_sup (f := k) (Finset.mem_univ (a, b)))
        (le_trans hm (Nat.le_mul_of_pos_right m (Nat.succ_pos d)))
    have hu : (((ϖ ^ (m * e a))⁻¹ : Kˣ) : K) * ((ϖ ^ (m * e a) : Kˣ) : K) = 1 := Units.inv_mul _
    have eq : (((ϖ ^ (m * e a))⁻¹ : Kˣ) : K) * x a b * ((ϖ ^ (m * e b) : Kˣ) : K) =
        (ϖ : K) ^ (m * (d + 1) - k (a, b)) * ((ϖ : K) ^ k (a, b) * x a b) := by
      calc _ = x a b * ((ϖ ^ (m * (d + 1)) : Kˣ) : K) *
            ((((ϖ ^ (m * e a))⁻¹ : Kˣ) : K) * ((ϖ ^ (m * e a) : Kˣ) : K)) := by
            rw [hd, mul_add, pow_add, Units.val_mul]; ring
        _ = _ := by
            rw [hu, mul_one, Units.val_pow_eq_pow_val, ← mul_assoc, ← pow_add,
              Nat.sub_add_cancel hk', mul_comm]
    rw [eq]
    exact R.mul_mem (R.pow_mem hϖ _) (hk (a, b))

/- English proof (translation)
Proceed by induction on `s with`. Consider the case `nil => intro j k h`. Simplify `h` using `[revIn]`. Consider the case `cons c s ih`. Introduce `j k h`.

Simplify using `only [revIn] at h`. Apply the tactic sequence `by_cases h1 : j < c <;> by_cases h2 : k < c <;> simp only [h1, h2, if_true, if_false] at h`. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers.

Use `ih (Nat.add_left_cancel h)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem revIn_inj (s : List ℕ) : Function.Injective (revIn s) := by
  induction s with
  | nil => intro j k h; simpa [revIn] using h
  | cons c s ih =>
    intro j k h
    simp only [revIn] at h
    by_cases h1 : j < c <;> by_cases h2 : k < c <;> simp only [h1, h2, if_true, if_false] at h
    · omega
    · omega
    · omega
    · have := ih (Nat.add_left_cancel h); omega

/- English proof (translation)
Proceed by induction on `s with`. Consider the case `nil => intro j h`. Simplify using `at h`. Consider the case `cons c s ih`. Introduce `j h`.

Simplify using `only [List.sum_cons] at h ⊢`. Simplify using `only [revIn]`. Use `split_ifs with h1`. Use linear arithmetic over natural numbers and integers. Use `ih (j - c) (by omega); omega` as an intermediate fact.
-/
theorem revIn_lt (s : List ℕ) : ∀ j, j < s.sum → revIn s j < s.sum := by
  induction s with
  | nil => intro j h; simp at h
  | cons c s ih =>
    intro j h
    simp only [List.sum_cons] at h ⊢
    simp only [revIn]
    split_ifs with h1
    · omega
    · have := ih (j - c) (by omega); omega

def ptInv (s : List ℕ) (t : ℕ → Kˣ) : Matrix (Fin s.sum) (Fin s.sum) K :=
  fun a b => if (a : ℕ) = revIn s b then (((t (blk s b))⁻¹ : Kˣ) : K) else 0

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single ⟨revIn s a, revIn_lt s a a.2⟩]`. Simplify using `only [pt, ptInv, if_true]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality.

Simplify using the standard rewrite rules. Establish `: revIn s a ≠ revIn s b` using `fun h => hab (Fin.ext (revIn_inj s h))`. Simplify using `[this, hab]`. Introduce `k _ hk`. Simplify using `only [pt]`.

Rewrite using `[if_neg (fun h => hk (Fin.ext h)), zero_mul]`. Simplify using the standard rewrite rules.
-/
theorem pt_mul_ptInv (s : List ℕ) (t : ℕ → Kˣ) : pt s t * ptInv s t = (1 : Matrix _ _ K) := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single ⟨revIn s a, revIn_lt s a a.2⟩]
  · simp only [pt, ptInv, if_true]
    by_cases hab : a = b
    · subst hab; simp
    · have : revIn s a ≠ revIn s b := fun h => hab (Fin.ext (revIn_inj s h))
      simp [this, hab]
  · intro k _ hk
    simp only [pt]
    rw [if_neg (fun h => hk (Fin.ext h)), zero_mul]
  · simp

/- English proof (translation)
The claim follows from `mul_eq_one_comm.1 (pt_mul_ptInv s t)`.
-/
theorem ptInv_mul_pt (s : List ℕ) (t : ℕ → Kˣ) : ptInv s t * pt s t = (1 : Matrix _ _ K) :=
  mul_eq_one_comm.1 (pt_mul_ptInv s t)

end Alg

section Top

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.GLRealOpen.glR_open R hR n`.
-/
theorem glR_open (R : Subring K) (hR : IsOpen (R : Set K)) (n : ℕ) :
    IsOpen (glR R n : Set (GL (Fin n) K)) :=
  _root_.UpperTheory.Reformulated.B.GLRealOpen.glR_open R hR n

/- English proof (translation)
Set `S : Set (Matrix (Fin n) (Fin n) K)` to `Set.pi Set.univ (fun _ => Set.pi Set.univ (fun _ => (R : Set K)))`. Establish `hS : IsCompact S` using `isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => hR))`. Establish `hS' : IsCompact (MulOpposite.unop ⁻¹' S : Set (Matrix (Fin n) (Fin n) K)ᵐᵒᵖ)` using `MulOpposite.opHomeomorph.isCompact_preimage.mp hS`. Use `Units.isClosedEmbedding_embedProduct.isCompact_preimage (hS.prod hS')` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨fun a _ b _ => h1 a b, fun a _ b _ => h2 a b⟩`. Introduce and unpack `⟨h1, h2⟩`.

Conclude with `⟨fun a b => h1 a (Set.mem_univ _) b (Set.mem_univ _), fun a b => h2 a (Set.mem_univ _) b (Set.mem_univ _)⟩`.
-/
theorem glR_compact [T2Space K] (R : Subring K) (hR : IsCompact (R : Set K)) (n : ℕ) :
    IsCompact (glR R n : Set (GL (Fin n) K)) := by
  let S : Set (Matrix (Fin n) (Fin n) K) :=
    Set.pi Set.univ (fun _ => Set.pi Set.univ (fun _ => (R : Set K)))
  have hS : IsCompact S := isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => hR))
  have hS' : IsCompact (MulOpposite.unop ⁻¹' S : Set (Matrix (Fin n) (Fin n) K)ᵐᵒᵖ) :=
    MulOpposite.opHomeomorph.isCompact_preimage.mp hS
  have := Units.isClosedEmbedding_embedProduct.isCompact_preimage (hS.prod hS')
  convert this using 1
  ext g
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun a _ b _ => h1 a b, fun a _ b _ => h2 a b⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun a b => h1 a (Set.mem_univ _) b (Set.mem_univ _),
      fun a b => h2 a (Set.mem_univ _) b (Set.mem_univ _)⟩

/- English proof (translation)
Establish `e : {x : Matrix (Fin n) (Fin n) K | IsUpUni x} = (⋂ i, ⋂ j, ⋂ (_ : j < i), {x | x i j = 0}) ∩ ⋂ a, {x | x a a = 1}`. Use extensionality with `x`. Simplify using `[IsUpUni, Matrix.IsUpperTriangular, Matrix.BlockTriangular]`. Rewrite using `[e]`. Conclude with `(isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_eq (continuous_id.matrix_elem i j) continuous_const).inter (isClosed_iInter fun a => isClosed_eq (continuous_id.matrix_elem a a) continuous_const)`.
-/
theorem isClosed_upUni [T2Space K] (n : ℕ) :
    IsClosed {x : Matrix (Fin n) (Fin n) K | IsUpUni x} := by
  have e : {x : Matrix (Fin n) (Fin n) K | IsUpUni x} =
      (⋂ i, ⋂ j, ⋂ (_ : j < i), {x | x i j = 0}) ∩ ⋂ a, {x | x a a = 1} := by
    ext x; simp [IsUpUni, Matrix.IsUpperTriangular, Matrix.BlockTriangular]
  rw [e]
  exact (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (continuous_id.matrix_elem i j) continuous_const).inter
    (isClosed_iInter fun a => isClosed_eq (continuous_id.matrix_elem a a) continuous_const)

/- English proof (translation)
Establish `e : {x : Matrix (Fin n) (Fin n) K | IsLowUni x} = (⋂ i, ⋂ j, ⋂ (_ : i < j), {x | x i j = 0}) ∩ ⋂ a, {x | x a a = 1}`. Use extensionality with `x`. Simplify using `[IsLowUni, Matrix.IsLowerTriangular, Matrix.BlockTriangular]`. Rewrite using `[e]`. Conclude with `(isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_eq (continuous_id.matrix_elem i j) continuous_const).inter (isClosed_iInter fun a => isClosed_eq (continuous_id.matrix_elem a a) continuous_const)`.
-/
theorem isClosed_lowUni [T2Space K] (n : ℕ) :
    IsClosed {x : Matrix (Fin n) (Fin n) K | IsLowUni x} := by
  have e : {x : Matrix (Fin n) (Fin n) K | IsLowUni x} =
      (⋂ i, ⋂ j, ⋂ (_ : i < j), {x | x i j = 0}) ∩ ⋂ a, {x | x a a = 1} := by
    ext x; simp [IsLowUni, Matrix.IsLowerTriangular, Matrix.BlockTriangular]
  rw [e]
  exact (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (continuous_id.matrix_elem i j) continuous_const).inter
    (isClosed_iInter fun a => isClosed_eq (continuous_id.matrix_elem a a) continuous_const)

end Top

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

/- English proof (translation)
Set `δ : ℕ → Fin n → Kˣ` to `fun m a => ϖ ^ (m * e a)`. Set `f : ℕ → GL (Fin n) K → GL (Fin n) K` to `fun m g => (Dg (δ m))⁻¹ * g * Dg (δ m)`. Establish `hf : ∀ m, Continuous (f m)` using `fun m => (continuous_const.mul continuous_id).mul continuous_const`. Set `M : ℕ → Subgroup (GL (Fin n) K)` to `fun m => (glR R n).comap (MulAut.conj (Dg (δ m))⁻¹).toMonoidHom`. Establish `hMset : ∀ m, (M m : Set (GL (Fin n) K)) = f m ⁻¹' (glR R n : Set _)`.

Introduce `m`. Use extensionality with `g`. Use `show (MulAut.conj (Dg (δ m))⁻¹) g ∈ glR R n ↔ (Dg (δ m))⁻¹ * g * Dg (δ m) ∈ glR R n`. Rewrite using `[MulAut.conj_apply, inv_inv]`. Set `L : ℕ → Subgroup H` to `fun m => (M m).comap H.subtype`.

Establish `hemb : IsClosedEmbedding (H.subtype)` using `hH.isClosedEmbedding_subtypeVal`. Establish `hK : (intSub R H : Set H) = H.subtype ⁻¹' (glR R n : Set _)` using `by ext g; rfl`. Establish `hL : ∀ m, (L m : Set H) = H.subtype ⁻¹' (M m : Set _)` using `fun m => rfl`. Use `haar_of_cover (intSub R H) ?_ ?_ L ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[hK]`.

Conclude with `(glR_open R hRo n).preimage continuous_subtype_val`. Rewrite using `[hK]`. Conclude with `hemb.isCompact_preimage (glR_compact R hRc n)`. Introduce `m`. Rewrite using `[hL, hMset]`.

Conclude with `((glR_open R hRo n).preimage (hf m)).preimage continuous_subtype_val`. Introduce `m`. Rewrite using `[hL, hMset]`. Establish `hc : IsCompact (f m ⁻¹' (glR R n : Set _))`. Set `h : GL (Fin n) K ≃ₜ GL (Fin n) K` to `(Homeomorph.mulLeft (Dg (δ m))⁻¹).trans (Homeomorph.mulRight (Dg (δ m)))`.

Conclude with `h.isCompact_preimage.2 (glR_compact R hRc n)`. Conclude with `hemb.isCompact_preimage hc`. Introduce `g`. Take `⟨m1, hm1⟩` from `exists_pow_int R ϖ hϖ hx e _ (hstr g g.2)`. Take `⟨m2, hm2⟩` from `exists_pow_int R ϖ hϖ hx e _ (hstr (g : GL (Fin n) K)⁻¹ (H.inv_mem g.2))`.

Use `⟨max m1 m2, ?_⟩` and prove the remaining obligations. Establish `hmem : (g : GL (Fin n) K) ∈ (M (max m1 m2) : Set _)`. Rewrite using `[hMset]`. Use `⟨fun a b => ?_, fun a b => ?_⟩` and prove the remaining obligations. Use `show (((Dg (δ (max m1 m2)))⁻¹ * (g : GL (Fin n) K) * Dg (δ (max m1 m2)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b ∈ R`.

Rewrite using `[conj_entry]`. Conclude with `hm1 _ (le_max_left _ _) a b`. Establish `hinv : (f (max m1 m2) g)⁻¹ = (Dg (δ (max m1 m2)))⁻¹ * (g : GL (Fin n) K)⁻¹ * Dg (δ (max m1 m2))`. Simplify using `[f, mul_assoc]`. Use `show (((f (max m1 m2) g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b ∈ R`.

Rewrite using `[hinv, conj_entry]`. Conclude with `hm2 _ (le_max_right _ _) a b`. Conclude with `hmem`.
-/
theorem haar_closed [T2Space K] (R : Subring K) (hRo : IsOpen (R : Set K))
    (hRc : IsCompact (R : Set K)) (ϖ : Kˣ) (hϖ : (ϖ : K) ∈ R)
    (hx : ∀ x : K, ∃ m : ℕ, (ϖ : K) ^ m * x ∈ R) {n : ℕ}
    (H : Subgroup (GL (Fin n) K)) (hH : IsClosed (H : Set (GL (Fin n) K))) (e : Fin n → ℕ)
    (hstr : ∀ g ∈ H, ∀ a b, (g : Matrix (Fin n) (Fin n) K) a b = 0 ∨
      (a = b ∧ (g : Matrix (Fin n) (Fin n) K) a b = 1) ∨ e a < e b) :
    ∃ μ : Measure H, μ.IsMulLeftInvariant ∧ μ.IsMulRightInvariant ∧ SFinite μ ∧
      μ (intSub R H : Set H) = 1 := by
  let δ : ℕ → Fin n → Kˣ := fun m a => ϖ ^ (m * e a)
  let f : ℕ → GL (Fin n) K → GL (Fin n) K := fun m g => (Dg (δ m))⁻¹ * g * Dg (δ m)
  have hf : ∀ m, Continuous (f m) := fun m =>
    (continuous_const.mul continuous_id).mul continuous_const
  let M : ℕ → Subgroup (GL (Fin n) K) := fun m =>
    (glR R n).comap (MulAut.conj (Dg (δ m))⁻¹).toMonoidHom
  have hMset : ∀ m, (M m : Set (GL (Fin n) K)) = f m ⁻¹' (glR R n : Set _) := by
    intro m; ext g
    show (MulAut.conj (Dg (δ m))⁻¹) g ∈ glR R n ↔ (Dg (δ m))⁻¹ * g * Dg (δ m) ∈ glR R n
    rw [MulAut.conj_apply, inv_inv]
  let L : ℕ → Subgroup H := fun m => (M m).comap H.subtype
  have hemb : IsClosedEmbedding (H.subtype) := hH.isClosedEmbedding_subtypeVal
  have hK : (intSub R H : Set H) = H.subtype ⁻¹' (glR R n : Set _) := by ext g; rfl
  have hL : ∀ m, (L m : Set H) = H.subtype ⁻¹' (M m : Set _) := fun m => rfl
  refine haar_of_cover (intSub R H) ?_ ?_ L ?_ ?_ ?_
  · rw [hK]; exact (glR_open R hRo n).preimage continuous_subtype_val
  · rw [hK]; exact hemb.isCompact_preimage (glR_compact R hRc n)
  · intro m; rw [hL, hMset]
    exact ((glR_open R hRo n).preimage (hf m)).preimage continuous_subtype_val
  · intro m; rw [hL, hMset]
    have hc : IsCompact (f m ⁻¹' (glR R n : Set _)) := by
      let h : GL (Fin n) K ≃ₜ GL (Fin n) K :=
        (Homeomorph.mulLeft (Dg (δ m))⁻¹).trans (Homeomorph.mulRight (Dg (δ m)))
      exact h.isCompact_preimage.2 (glR_compact R hRc n)
    exact hemb.isCompact_preimage hc
  · intro g
    obtain ⟨m1, hm1⟩ := exists_pow_int R ϖ hϖ hx e _ (hstr g g.2)
    obtain ⟨m2, hm2⟩ := exists_pow_int R ϖ hϖ hx e _ (hstr (g : GL (Fin n) K)⁻¹ (H.inv_mem g.2))
    refine ⟨max m1 m2, ?_⟩
    have hmem : (g : GL (Fin n) K) ∈ (M (max m1 m2) : Set _) := by
      rw [hMset]
      refine ⟨fun a b => ?_, fun a b => ?_⟩
      · show (((Dg (δ (max m1 m2)))⁻¹ * (g : GL (Fin n) K) * Dg (δ (max m1 m2)) : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) a b ∈ R
        rw [conj_entry]; exact hm1 _ (le_max_left _ _) a b
      · have hinv : (f (max m1 m2) g)⁻¹ =
            (Dg (δ (max m1 m2)))⁻¹ * (g : GL (Fin n) K)⁻¹ * Dg (δ (max m1 m2)) := by
          simp [f, mul_assoc]
        show (((f (max m1 m2) g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b ∈ R
        rw [hinv, conj_entry]; exact hm2 _ (le_max_right _ _) a b
    exact hmem

/- English proof (translation)
The claim follows from `(isClosed_upUni n).preimage Units.continuous_val`.
-/
theorem upUni_closed [T2Space K] (n : ℕ) : IsClosed (upUniG K n : Set (GL (Fin n) K)) :=
  (isClosed_upUni n).preimage Units.continuous_val

/- English proof (translation)
Establish `e : (lowW K s t : Set (GL (Fin s.sum) K)) = (fun g : GL (Fin s.sum) K => (g : Matrix (Fin s.sum) (Fin s.sum) K)) ⁻¹' {x | IsLowUni x} ∩ (fun g : GL (Fin s.sum) K => ptInv s t * (g : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t) ⁻¹' {x | IsLowUni x}`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hg, h, hh, he⟩`. Use `⟨hg, ?_⟩` and prove the remaining obligations.

Use `show IsLowUni (ptInv s t * (g : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t)`. Rewrite using `[Matrix.mul_assoc, he, ← Matrix.mul_assoc, ptInv_mul_pt, Matrix.one_mul]`. Conclude with `hh`. Introduce and unpack `⟨hg, hh⟩`. Use `⟨hg, _, hh, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, pt_mul_ptInv, Matrix.one_mul]`. Rewrite using `[e]`. Conclude with `((isClosed_lowUni _).preimage Units.continuous_val).inter ((isClosed_lowUni _).preimage ((continuous_const.mul Units.continuous_val).mul continuous_const))`.
-/
theorem lowW_closed [T2Space K] (s : List ℕ) (t : ℕ → Kˣ) :
    IsClosed (lowW K s t : Set (GL (Fin s.sum) K)) := by
  have e : (lowW K s t : Set (GL (Fin s.sum) K)) =
      (fun g : GL (Fin s.sum) K => (g : Matrix (Fin s.sum) (Fin s.sum) K)) ⁻¹' {x | IsLowUni x} ∩
      (fun g : GL (Fin s.sum) K => ptInv s t * (g : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t) ⁻¹'
        {x | IsLowUni x} := by
    ext g
    constructor
    · rintro ⟨hg, h, hh, he⟩
      refine ⟨hg, ?_⟩
      show IsLowUni (ptInv s t * (g : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t)
      rw [Matrix.mul_assoc, he, ← Matrix.mul_assoc, ptInv_mul_pt, Matrix.one_mul]; exact hh
    · rintro ⟨hg, hh⟩
      refine ⟨hg, _, hh, ?_⟩
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, pt_mul_ptInv, Matrix.one_mul]
  rw [e]
  exact ((isClosed_lowUni _).preimage Units.continuous_val).inter ((isClosed_lowUni _).preimage
    ((continuous_const.mul Units.continuous_val).mul continuous_const))

end GeneralLinearIntegersOpenCompact

open GeneralLinearIntegersOpenCompact

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

/- English proof (translation)
Introduce `K _ _ _ _ _ R hRo hRc ⟨ϖ, hϖ, hx⟩ s t`. Use `⟨haar_closed R hRo hRc ϖ hϖ hx (lowW K s t) (lowW_closed s t) (fun a => s.sum - a.val) ?_, haar_closed R hRo hRc ϖ hϖ hx (upUniG K s.sum) (upUni_closed s.sum) Fin.val ?_⟩` and prove the remaining obligations. Introduce `g hg a b`. Break down `lt_trichotomy a b with h | rfl | h` into its components or cases. Use the proof step `left; exact hg.1.1 (by simpa using h)`.

Use `right`. Use `left`. Conclude with `⟨rfl, hg.1.2 a⟩`. Use `right`. Use `right`.

Use `a.2` as an intermediate fact. Use `b.2` as an intermediate fact. Establish `: b.val < a.val` using `h`. Use `show s.sum - a.val < s.sum - b.val`. Use linear arithmetic over natural numbers and integers.

Introduce `g hg a b`. Break down `lt_trichotomy a b with h | rfl | h` into its components or cases. Use `right`. Use `right`. Conclude with `h`.

Use `right`. Use `left`. Conclude with `⟨rfl, hg.2 a⟩`. Use `left`. Conclude with `hg.1 h`.
-/
theorem haarExists : Formalism.DoubleCosetMeasures.HaarExists := by
  intro K _ _ _ _ _ R hRo hRc ⟨ϖ, hϖ, hx⟩ s t
  refine ⟨haar_closed R hRo hRc ϖ hϖ hx (lowW K s t) (lowW_closed s t)
    (fun a => s.sum - a.val) ?_, haar_closed R hRo hRc ϖ hϖ hx (upUniG K s.sum)
    (upUni_closed s.sum) Fin.val ?_⟩
  · intro g hg a b
    rcases lt_trichotomy a b with h | rfl | h
    · left; exact hg.1.1 (by simpa using h)
    · right; left; exact ⟨rfl, hg.1.2 a⟩
    · right; right
      have := a.2; have := b.2
      have : b.val < a.val := h
      show s.sum - a.val < s.sum - b.val
      omega
  · intro g hg a b
    rcases lt_trichotomy a b with h | rfl | h
    · right; right; exact h
    · right; left; exact ⟨rfl, hg.2 a⟩
    · left; exact hg.1 h

end Formalism.DoubleCosetMeasures.P
