import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace HermitianFormNormLemmas

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

/- English proof (translation)
Establish `: SecondCountableTopology (Matrix (Fin k) (Fin k) (Ad E))` using `inferInstanceAs (SecondCountableTopology (Fin k → Fin k → Ad E))`. Establish `: SecondCountableTopology (Matrix (Fin k) (Fin k) (Ad E))ᵐᵒᵖ` using `MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology`. Conclude with `Units.isEmbedding_embedProduct.secondCountableTopology`.
-/
theorem sc_GA : SecondCountableTopology (GA E k) := by
  have : SecondCountableTopology (Matrix (Fin k) (Fin k) (Ad E)) :=
    inferInstanceAs (SecondCountableTopology (Fin k → Fin k → Ad E))
  have : SecondCountableTopology (Matrix (Fin k) (Fin k) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

attribute [local instance] sc_GA

/- English proof (translation)
The claim follows from `inferInstance`.
-/
theorem borel_GA : BorelSpace (GA E k) := inferInstance

attribute [local instance] borel_GA

/- English proof (translation)
The claim follows from `inferInstance`.
-/
theorem sf_adele : SigmaFinite (GroundTheory.Global.adeleMeasure E) := inferInstance

attribute [local instance] sf_adele

/- English proof (translation)
The claim follows from `inferInstance`.
-/
theorem neg_adele : (GroundTheory.Global.adeleMeasure E).IsNegInvariant := inferInstance

attribute [local instance] neg_adele

/- English proof (translation)
The claim follows from `inferInstance`.
-/
theorem vec_sf (ι : Type) [Fintype ι] : SigmaFinite (vecMeasure E ι) := inferInstance

/- English proof (translation)
The claim follows from `inferInstance`.
-/
theorem vec_add (ι : Type) [Fintype ι] : (vecMeasure E ι).IsAddLeftInvariant := inferInstance

/- English proof (translation)
The claim follows from `inferInstance`.
-/
theorem vec_neg (ι : Type) [Fintype ι] : (vecMeasure E ι).IsNegInvariant := inferInstance

attribute [local instance] vec_sf vec_add vec_neg

/- English proof (translation)
The claim follows from `continuous_posU _`.
-/
theorem cont_blk (j : ℕ) : Continuous (fun x : UnipotentBlockColumnIndex k j j → Ad E => (blkU x : GA E k)) :=
  continuous_posU _

/- English proof (translation)
The claim follows from `(((cont_blk j).comp continuous_fst).mul continuous_snd).measurable`.
-/
theorem meas_blkmul (j : ℕ) :
    Measurable (fun p : (UnipotentBlockColumnIndex k j j → Ad E) × GA E k => blkU p.1 * p.2) :=
  (((cont_blk j).comp continuous_fst).mul continuous_snd).measurable

/- English proof (translation)
The claim follows from `continuous_inv.measurable`.
-/
theorem meas_inv : Measurable (fun h : GA E k => h⁻¹) := continuous_inv.measurable

/- English proof (translation)
The claim follows from `(continuous_const_mul u).measurable`.
-/
theorem meas_lmul (u : GA E k) : Measurable (fun h : GA E k => u * h) := (continuous_const_mul u).measurable

/- English proof (translation)
The claim follows from `(continuous_mul_const u).measurable`.
-/
theorem meas_rmul (u : GA E k) : Measurable (fun h : GA E k => h * u) := (continuous_mul_const u).measurable

/- English proof (translation)
The claim follows from `(continuous_fst.mul continuous_snd).measurable`.
-/
theorem measurable_mt_mul : Measurable (fun p : GA E k × GA E k => p.1 * p.2) :=
  (continuous_fst.mul continuous_snd).measurable

/- English proof (translation)
Use `show ((1 : Matrix (Fin k) (Fin k) (Ad E)) + posM Subtype.val x) i c = _`. Rewrite using `[Matrix.add_apply]`. Use `congr 1`. Rewrite using `[posM, Matrix.sum_apply]`. Use `split_ifs with h`.

Rewrite using `[Finset.sum_eq_single (⟨(i, c), h.1, h.2.ge, h.2.le⟩ : UnipotentBlockColumnIndex k j j)]`. Use `first`. Consider the case `exact Matrix.single_apply_same _ _ _`. Consider the case `simp [Matrix.single_apply]`. Introduce `t _ ht`.

Apply `Matrix.single_apply_of_ne` to reduce the goal to its premises. Introduce and unpack `⟨h1, h2⟩`. Conclude with `ht (Subtype.ext (Prod.ext h1 h2))`. Introduce `hn`. Conclude with `absurd (Finset.mem_univ _) hn`.

Use `Finset.sum_eq_zero fun t _ => Matrix.single_apply_of_ne _ _ _ _ _ ?_` and prove the remaining obligations. Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `h ⟨t.2.1, le_antisymm t.2.2.2 t.2.2.1⟩`.
-/
theorem blk_val {j : ℕ} (x : UnipotentBlockColumnIndex k j j → Ad E) (i c : Fin k) :
    (blkU x : GA E k).val i c = (1 : Matrix (Fin k) (Fin k) (Ad E)) i c +
      if h : (i : ℕ) < j ∧ (c : ℕ) = j then x ⟨(i, c), h.1, h.2.ge, h.2.le⟩ else 0 := by
  show ((1 : Matrix (Fin k) (Fin k) (Ad E)) + posM Subtype.val x) i c = _
  rw [Matrix.add_apply]
  congr 1
  rw [posM, Matrix.sum_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨(i, c), h.1, h.2.ge, h.2.le⟩ : UnipotentBlockColumnIndex k j j)]
    · first
      | exact Matrix.single_apply_same _ _ _
      | simp [Matrix.single_apply]
    · intro t _ ht
      apply Matrix.single_apply_of_ne
      rintro ⟨h1, h2⟩
      exact ht (Subtype.ext (Prod.ext h1 h2))
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · refine Finset.sum_eq_zero fun t _ => Matrix.single_apply_of_ne _ _ _ _ _ ?_
    rintro ⟨rfl, rfl⟩
    exact h ⟨t.2.1, le_antisymm t.2.2.2 t.2.2.1⟩

/- English proof (translation)
Rewrite using `[Units.val_mul, Matrix.mul_apply]`. Simplify using `only [blk_val, add_mul, Finset.sum_add_distrib]`. Use `congr 1`. Use `first`. Consider the case `rw [← Matrix.mul_apply, Matrix.one_mul]`.

Consider the case `simp [Matrix.one_apply]`. Rewrite using `[Finset.sum_eq_single ⟨j, hj⟩]`. Distinguish the cases in `h : (i : ℕ) < j`. Rewrite using `[dif_pos (show (i : ℕ) < j ∧ ((⟨j, hj⟩ : Fin k) : ℕ) = j from ⟨h, rfl⟩), dif_pos h]`. Rewrite using `[dif_neg (fun h' : (i : ℕ) < j ∧ ((⟨j, hj⟩ : Fin k) : ℕ) = j => h h'.1), dif_neg h]`.

Introduce `m _ hm`. Rewrite using `[dif_neg, zero_mul]`. Introduce and unpack `⟨_, h2⟩`. Conclude with `hm (Fin.ext h2)`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem blk_mul_val (j : ℕ) (hj : j < k) (x : UnipotentBlockColumnIndex k j j → Ad E) (B : GA E k) (i c : Fin k) :
    (blkU x * B).val i c = B.val i c +
      (if h : (i : ℕ) < j then x ⟨(i, ⟨j, hj⟩), h, le_rfl, le_rfl⟩ else 0) * B.val ⟨j, hj⟩ c := by
  rw [Units.val_mul, Matrix.mul_apply]
  simp only [blk_val, add_mul, Finset.sum_add_distrib]
  congr 1
  · first
    | rw [← Matrix.mul_apply, Matrix.one_mul]
    | simp [Matrix.one_apply]
  · rw [Finset.sum_eq_single ⟨j, hj⟩]
    · by_cases h : (i : ℕ) < j
      · rw [dif_pos (show (i : ℕ) < j ∧ ((⟨j, hj⟩ : Fin k) : ℕ) = j from ⟨h, rfl⟩), dif_pos h]
      · rw [dif_neg (fun h' : (i : ℕ) < j ∧ ((⟨j, hj⟩ : Fin k) : ℕ) = j => h h'.1), dif_neg h]
    · intro m _ hm
      rw [dif_neg, zero_mul]
      rintro ⟨_, h2⟩
      exact hm (Fin.ext h2)
    · intro h
      exact absurd (Finset.mem_univ _) h

/- English proof (translation)
The claim follows from `posU_add _ x y`.
-/
theorem bU_add {j : ℕ} (x y : UnipotentBlockColumnIndex k j j → Ad E) : (blkU (x + y) : GA E k) = blkU x * blkU y :=
  posU_add _ x y

/- English proof (translation)
The claim follows from `posU_zero _`.
-/
theorem bU_zero {j : ℕ} : (blkU (0 : UnipotentBlockColumnIndex k j j → Ad E) : GA E k) = 1 := posU_zero _

/- English proof (translation)
Rewrite using `[← bU_add, add_neg_cancel, bU_zero]`.
-/
theorem bU_mul_neg {j : ℕ} (x : UnipotentBlockColumnIndex k j j → Ad E) : (blkU x : GA E k) * blkU (-x) = 1 := by
  rw [← bU_add, add_neg_cancel, bU_zero]

/- English proof (translation)
Rewrite using `[← bU_add, neg_add_cancel, bU_zero]`.
-/
theorem bU_neg_mul {j : ℕ} (x : UnipotentBlockColumnIndex k j j → Ad E) : (blkU (-x) : GA E k) * blkU x = 1 := by
  rw [← bU_add, neg_add_cancel, bU_zero]

/- English proof (translation)
The claim follows from `inv_eq_of_mul_eq_one_right (bU_mul_neg x)`.
-/
theorem bU_inv {j : ℕ} (x : UnipotentBlockColumnIndex k j j → Ad E) : (blkU x : GA E k)⁻¹ = blkU (-x) :=
  inv_eq_of_mul_eq_one_right (bU_mul_neg x)

/- English proof (translation)
Introduce `i c h` and use `hg i c (by omega)`.
-/
theorem blk_succ {j : ℕ} {g : GA E k} (hg : GlobalTheory j g) : GlobalTheory (j + 1) g :=
  fun i c h => hg i c (by omega)

/- English proof (translation)
Introduce `i c h`. Rewrite using `[blk_val, dif_neg, add_zero]`. Introduce and unpack `⟨h1, h2⟩`. Use linear arithmetic over natural numbers and integers.
-/
theorem blk_blkU_succ {j : ℕ} (x : UnipotentBlockColumnIndex k j j → Ad E) : GlobalTheory (j + 1) (blkU x : GA E k) := by
  intro i c h
  rw [blk_val, dif_neg, add_zero]
  rintro ⟨h1, h2⟩
  omega

/- English proof (translation)
Use `⟨fun i c hci => ?_, fun i => ?_, fun i c hc => ?_⟩` and prove the remaining obligations. Establish `hci' : (c : ℕ) < i` using `hci`. Rewrite using `[blk_val, dif_neg, add_zero, Matrix.one_apply_ne (hci.ne')]`. Introduce and unpack `⟨h1, h2⟩`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[blk_val, dif_neg, add_zero, Matrix.one_apply_eq]`. Introduce and unpack `⟨h1, h2⟩`. Use linear arithmetic over natural numbers and integers. Rewrite using `[blk_val, dif_neg, add_zero]`. Introduce and unpack `⟨h1, h2⟩`.

Use linear arithmetic over natural numbers and integers.
-/
theorem UU_blk {j : ℕ} (x : UnipotentBlockColumnIndex k j j → Ad E) : UU j (blkU x : GA E k) := by
  refine ⟨fun i c hci => ?_, fun i => ?_, fun i c hc => ?_⟩
  · have hci' : (c : ℕ) < i := hci
    rw [blk_val, dif_neg, add_zero, Matrix.one_apply_ne (hci.ne')]
    rintro ⟨h1, h2⟩
    omega
  · rw [blk_val, dif_neg, add_zero, Matrix.one_apply_eq]
    rintro ⟨h1, h2⟩
    omega
  · rw [blk_val, dif_neg, add_zero]
    rintro ⟨h1, h2⟩
    omega

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ _ hci => Matrix.one_apply_ne (hci.ne'), fun i => Matrix.one_apply_eq i, fun _ _ _ => rfl⟩`.
-/
theorem UU_one (j : ℕ) : UU j (1 : GA E k) :=
  ⟨fun _ _ hci => Matrix.one_apply_ne (hci.ne'), fun i => Matrix.one_apply_eq i, fun _ _ _ => rfl⟩

/- English proof (translation)
The claim follows from `Units.ext (Matrix.ext fun i c => hu.2.2 i c c.isLt)`.
-/
theorem UU_top (u : GA E k) (hu : UU k u) : u = 1 :=
  Units.ext (Matrix.ext fun i c => hu.2.2 i c c.isLt)

/- English proof (translation)
Establish `hc : ∀ i c : Fin k, Continuous fun g : GA E k => g.val i c` using `fun i c => Units.continuous_val.matrix_elem i c`. Establish `e : {g : GA E k | UU j g} = (⋂ i : Fin k, ⋂ c : Fin k, ⋂ (_ : c < i), {g : GA E k | g.val i c = 0}) ∩ ((⋂ i : Fin k, {g : GA E k | g.val i i = 1}) ∩ (⋂ i : Fin k, ⋂ c : Fin k, ⋂ (_ : (c : ℕ) < j), {g : GA E k | g.val i c = (1 : Matrix (Fin k) (Fin k) (Ad E)) i c}))`. Use extensionality with `g`. Simplify using `only [UU, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]`. Rewrite using `[e]`.

Conclude with `IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun c => isClosed_iInter fun _ => isClosed_eq (hc i c) continuous_const) (IsClosed.inter (isClosed_iInter fun i => isClosed_eq (hc i i) continuous_const) (isClosed_iInter fun i => isClosed_iInter fun c => isClosed_iInter fu …`.
-/
theorem isClosed_UU (j : ℕ) : IsClosed {g : GA E k | UU j g} := by
  have hc : ∀ i c : Fin k, Continuous fun g : GA E k => g.val i c := fun i c =>
    Units.continuous_val.matrix_elem i c
  have e : {g : GA E k | UU j g} =
      (⋂ i : Fin k, ⋂ c : Fin k, ⋂ (_ : c < i), {g : GA E k | g.val i c = 0}) ∩
      ((⋂ i : Fin k, {g : GA E k | g.val i i = 1}) ∩
      (⋂ i : Fin k, ⋂ c : Fin k, ⋂ (_ : (c : ℕ) < j),
        {g : GA E k | g.val i c = (1 : Matrix (Fin k) (Fin k) (Ad E)) i c})) := by
    ext g
    simp only [UU, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [e]
  exact IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun c => isClosed_iInter fun _ =>
      isClosed_eq (hc i c) continuous_const)
    (IsClosed.inter (isClosed_iInter fun i => isClosed_eq (hc i i) continuous_const)
      (isClosed_iInter fun i => isClosed_iInter fun c => isClosed_iInter fun _ =>
        isClosed_eq (hc i c) continuous_const))

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `hn`. Use `⟨fun i c hci => ?_, fun i => ?_, fun i c hc => ?_⟩` and prove the remaining obligations. Establish `hci' : (c : ℕ) < i` using `hci`. Rewrite using `[blk_mul_val j hj, h1 i c hci]`. Distinguish the cases in `h : (i : ℕ) < j`.

Rewrite using `[h1 ⟨j, hj⟩ c (show (c : ℕ) < j by omega), mul_zero, add_zero]`. Rewrite using `[dif_neg h, zero_mul, add_zero]`. Rewrite using `[blk_mul_val j hj, h2 i]`. Distinguish the cases in `h : (i : ℕ) < j`. Rewrite using `[h1 ⟨j, hj⟩ i (show (i : ℕ) < j from h), mul_zero, add_zero]`.

Rewrite using `[dif_neg h, zero_mul, add_zero]`. Establish `hc' : (c : ℕ) < j` using `hc`. Rewrite using `[blk_mul_val j hj, h3 i c (by omega), h1 ⟨j, hj⟩ c (show (c : ℕ) < j from hc'), mul_zero, add_zero]`.
-/
theorem UU_blk_mul {j : ℕ} (hj : j < k) (x : UnipotentBlockColumnIndex k j j → Ad E) (n : GA E k) (hn : UU (j + 1) n) :
    UU j (blkU x * n) := by
  obtain ⟨h1, h2, h3⟩ := hn
  refine ⟨fun i c hci => ?_, fun i => ?_, fun i c hc => ?_⟩
  · have hci' : (c : ℕ) < i := hci
    rw [blk_mul_val j hj, h1 i c hci]
    by_cases h : (i : ℕ) < j
    · rw [h1 ⟨j, hj⟩ c (show (c : ℕ) < j by omega), mul_zero, add_zero]
    · rw [dif_neg h, zero_mul, add_zero]
  · rw [blk_mul_val j hj, h2 i]
    by_cases h : (i : ℕ) < j
    · rw [h1 ⟨j, hj⟩ i (show (i : ℕ) < j from h), mul_zero, add_zero]
    · rw [dif_neg h, zero_mul, add_zero]
  · have hc' : (c : ℕ) < j := hc
    rw [blk_mul_val j hj, h3 i c (by omega), h1 ⟨j, hj⟩ c (show (c : ℕ) < j from hc'), mul_zero,
      add_zero]

def colU (u : GA E k) (j : ℕ) : UnipotentBlockColumnIndex k j j → Ad E := fun t => u.val t.1.1 t.1.2

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `hu`. Use `⟨fun i c hci => ?_, fun i => ?_, fun i c hc => ?_⟩` and prove the remaining obligations. Establish `hci' : (c : ℕ) < i` using `hci`. Rewrite using `[blk_mul_val j hj, h1 i c hci]`. Distinguish the cases in `h : (i : ℕ) < j`.

Rewrite using `[h1 ⟨j, hj⟩ c (show (c : ℕ) < j by omega), mul_zero, add_zero]`. Rewrite using `[dif_neg h, zero_mul, add_zero]`. Rewrite using `[blk_mul_val j hj, h2 i]`. Distinguish the cases in `h : (i : ℕ) < j`. Rewrite using `[h1 ⟨j, hj⟩ i (show (i : ℕ) < j from h), mul_zero, add_zero]`.

Rewrite using `[dif_neg h, zero_mul, add_zero]`. Establish `hc' : (c : ℕ) < j + 1` using `hc`. Rewrite using `[blk_mul_val j hj]`. Break down `Nat.lt_or_ge (c : ℕ) j with hcj | hcj` into its components or cases. Rewrite using `[h3 i c hcj, h1 ⟨j, hj⟩ c (show (c : ℕ) < j from hcj), mul_zero, add_zero]`.

Establish `hcj' : c = ⟨j, hj⟩` using `Fin.ext (show (c : ℕ) = j by omega)`. Substitute `hcj'` using the available equality. Distinguish the cases in `h : (i : ℕ) < j`. Establish `hne : i ≠ ⟨j, hj⟩` using `fun e => by subst e; exact lt_irrefl j h`. Rewrite using `[dif_pos h, h2 ⟨j, hj⟩, mul_one, Matrix.one_apply_ne hne]`.

Use `show u.val i ⟨j, hj⟩ + -u.val i ⟨j, hj⟩ = 0`. Use `first`. Consider the case `exact add_neg_cancel _`. Consider the case `simp`. Rewrite using `[dif_neg h, zero_mul, add_zero]`.

Break down `Nat.lt_or_ge j (i : ℕ) with hij | hij` into its components or cases. Establish `hne : i ≠ ⟨j, hj⟩` using `fun e => by subst e; exact lt_irrefl j hij`. Rewrite using `[h1 i ⟨j, hj⟩ (show j < (i : ℕ) from hij), Matrix.one_apply_ne hne]`. Establish `hi : i = ⟨j, hj⟩` using `Fin.ext (show (i : ℕ) = j by omega)`. Substitute `hi` using the available equality.

Rewrite using `[h2, Matrix.one_apply_eq]`.
-/
theorem UU_col {j : ℕ} (hj : j < k) (u : GA E k) (hu : UU j u) : UU (j + 1) (blkU (-colU u j) * u) := by
  obtain ⟨h1, h2, h3⟩ := hu
  refine ⟨fun i c hci => ?_, fun i => ?_, fun i c hc => ?_⟩
  · have hci' : (c : ℕ) < i := hci
    rw [blk_mul_val j hj, h1 i c hci]
    by_cases h : (i : ℕ) < j
    · rw [h1 ⟨j, hj⟩ c (show (c : ℕ) < j by omega), mul_zero, add_zero]
    · rw [dif_neg h, zero_mul, add_zero]
  · rw [blk_mul_val j hj, h2 i]
    by_cases h : (i : ℕ) < j
    · rw [h1 ⟨j, hj⟩ i (show (i : ℕ) < j from h), mul_zero, add_zero]
    · rw [dif_neg h, zero_mul, add_zero]
  · have hc' : (c : ℕ) < j + 1 := hc
    rw [blk_mul_val j hj]
    rcases Nat.lt_or_ge (c : ℕ) j with hcj | hcj
    · rw [h3 i c hcj, h1 ⟨j, hj⟩ c (show (c : ℕ) < j from hcj), mul_zero, add_zero]
    · have hcj' : c = ⟨j, hj⟩ := Fin.ext (show (c : ℕ) = j by omega)
      subst hcj'
      by_cases h : (i : ℕ) < j
      · have hne : i ≠ ⟨j, hj⟩ := fun e => by subst e; exact lt_irrefl j h
        rw [dif_pos h, h2 ⟨j, hj⟩, mul_one, Matrix.one_apply_ne hne]
        show u.val i ⟨j, hj⟩ + -u.val i ⟨j, hj⟩ = 0
        first
        | exact add_neg_cancel _
        | simp
      · rw [dif_neg h, zero_mul, add_zero]
        rcases Nat.lt_or_ge j (i : ℕ) with hij | hij
        · have hne : i ≠ ⟨j, hj⟩ := fun e => by subst e; exact lt_irrefl j hij
          rw [h1 i ⟨j, hj⟩ (show j < (i : ℕ) from hij), Matrix.one_apply_ne hne]
        · have hi : i = ⟨j, hj⟩ := Fin.ext (show (i : ℕ) = j by omega)
          subst hi
          rw [h2, Matrix.one_apply_eq]

/- English proof (translation)
Assemble the required witnesses or components as `⟨colU u j, blkU (-colU u j) * u, UU_col hj u hu, by rw [← mul_assoc, bU_mul_neg, one_mul]⟩`.
-/
theorem UU_split {j : ℕ} (hj : j < k) (u : GA E k) (hu : UU j u) :
    ∃ (y : UnipotentBlockColumnIndex k j j → Ad E) (u' : GA E k), UU (j + 1) u' ∧ u = blkU y * u' :=
  ⟨colU u j, blkU (-colU u j) * u, UU_col hj u hu, by rw [← mul_assoc, bU_mul_neg, one_mul]⟩

/- English proof (translation)
Use `first`. Consider the case `rfl`. Consider the case `simp only [nuD]`.
-/
theorem nuD_zero : nuD E k 0 = Measure.dirac 1 := by
  first
  | rfl
  | simp only [nuD]

/- English proof (translation)
Use `first`. Consider the case `rfl`. Consider the case `simp only [nuD]`.
-/
theorem nuD_succ (d : ℕ) : nuD E k (d + 1) =
    Measure.map (fun p : (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → Ad E) × GA E k => blkU p.1 * p.2)
      ((vecMeasure E (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)))).prod (nuD E k d)) := by
  first
  | rfl
  | simp only [nuD]

/- English proof (translation)
The claim follows from `| 0 => by rw [nuD_zero]; infer_instance | d + 1 => by haveI := sf_nuD d; rw [nuD_succ]; infer_instance`.
-/
theorem sf_nuD : ∀ d, SFinite (nuD E k d)
  | 0 => by rw [nuD_zero]; infer_instance
  | d + 1 => by haveI := sf_nuD d; rw [nuD_succ]; infer_instance

attribute [local instance] sf_nuD

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[nuD_succ]`. Use `_ = ∫⁻ p, F (blkU p.1 * p.2) ∂(vecMeasure E (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)))).prod (nuD E k d) := lintegral_map hF (meas_blkmul _)`. Use `_ = _ := lintegral_prod (fun p : (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → Ad E) × GA E k => F (blkU p.1 * p.2)) (hF.comp (meas_blkmul _)).aemeasurable`.
-/
theorem lint_succ (d : ℕ) (F : GA E k → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ h, F h ∂nuD E k (d + 1) = ∫⁻ x, ∫⁻ n, F (blkU x * n) ∂nuD E k d
      ∂vecMeasure E (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1))) := by
  calc ∫⁻ h, F h ∂nuD E k (d + 1)
      = ∫⁻ h, F h ∂Measure.map (fun p : (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → Ad E) × GA E k =>
          blkU p.1 * p.2) ((vecMeasure E (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)))).prod (nuD E k d)) := by
        rw [nuD_succ]
    _ = ∫⁻ p, F (blkU p.1 * p.2) ∂(vecMeasure E (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)))).prod (nuD E k d) :=
        lintegral_map hF (meas_blkmul _)
    _ = _ := lintegral_prod (fun p : (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → Ad E) × GA E k =>
          F (blkU p.1 * p.2)) (hF.comp (meas_blkmul _)).aemeasurable

abbrev Props (d : ℕ) : Prop :=
  SFinite (nuD E k d) ∧ (∀ᵐ u ∂nuD E k d, UU (k - d) u) ∧
    Measure.map (fun h => h⁻¹) (nuD E k d) = nuD E k d ∧
    (∀ u : GA E k, UU (k - d) u → Measure.map (fun h => u * h) (nuD E k d) = nuD E k d) ∧
    ∀ g : GA E k, GlobalTheory (k - d) g → ∀ F : GA E k → ℝ≥0∞, Measurable F →
      ∫⁻ h, F (g * h * g⁻¹) ∂nuD E k d = ENNReal.ofReal (Dt g)⁻¹ ^ d * ∫⁻ h, F h ∂nuD E k d

/- English proof (translation)
Rewrite using `[nuD_zero]`. Conclude with `lintegral_dirac' _ hG`.
-/
theorem lint_dirac (G : GA E k → ℝ≥0∞) (hG : Measurable G) : ∫⁻ h, G h ∂nuD E k 0 = G 1 := by
  rw [nuD_zero]
  exact lintegral_dirac' _ hG

/- English proof (translation)
Use `⟨inferInstance, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[nuD_zero]`. Conclude with `(ae_dirac_iff (isClosed_UU _).measurableSet).2 (UU_one _)`. Use `Measure.ext_of_lintegral _ fun F hF => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Introduce `u hu`. Establish `hu1 : u = 1` using `UU_top u (by simpa using hu)`. Substitute `hu1` using the available equality. Use `Measure.ext_of_lintegral _ fun F hF => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Introduce `g _ F hF`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem props_zero : Props (E := E) (k := k) 0 := by
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · rw [nuD_zero]
    exact (ae_dirac_iff (isClosed_UU _).measurableSet).2 (UU_one _)
  · refine Measure.ext_of_lintegral _ fun F hF => ?_
    calc ∫⁻ h, F h ∂Measure.map (fun h => h⁻¹) (nuD E k 0)
        = ∫⁻ h, F h⁻¹ ∂nuD E k 0 := lintegral_map hF meas_inv
      _ = F 1⁻¹ := lint_dirac (fun h => F h⁻¹) (hF.comp meas_inv)
      _ = F 1 := by rw [inv_one]
      _ = ∫⁻ h, F h ∂nuD E k 0 := (lint_dirac F hF).symm
  · intro u hu
    have hu1 : u = 1 := UU_top u (by simpa using hu)
    subst hu1
    refine Measure.ext_of_lintegral _ fun F hF => ?_
    calc ∫⁻ h, F h ∂Measure.map (fun h => (1 : GA E k) * h) (nuD E k 0)
        = ∫⁻ h, F (1 * h) ∂nuD E k 0 := lintegral_map hF (meas_lmul 1)
      _ = ∫⁻ h, F h ∂nuD E k 0 := by simp only [one_mul]
  · intro g _ F hF
    calc ∫⁻ h, F (g * h * g⁻¹) ∂nuD E k 0 = F (g * 1 * g⁻¹) :=
          lint_dirac (fun h => F (g * h * g⁻¹)) (hF.comp ((meas_lmul g).mul_const g⁻¹))
      _ = F 1 := by rw [mul_one, mul_inv_cancel]
      _ = ENNReal.ofReal (Dt g)⁻¹ ^ 0 * ∫⁻ h, F h ∂nuD E k 0 := by rw [pow_zero, one_mul, lint_dirac F hF]

/- English proof (translation)
Take `⟨-, hae, hinv, hleft, hconj⟩` from `ih`. Establish `hkd : k - d = k - (d + 1) + 1` using `by omega`. Rewrite `hae`, `hleft`, `hconj` using `[hkd]`. Establish `hj : k - (d + 1) < k` using `by omega`. Establish `iinv : ∀ G : GA E k → ℝ≥0∞, Measurable G → ∫⁻ n, G n⁻¹ ∂nuD E k d = ∫⁻ n, G n ∂nuD E k d`.

Introduce `G hG`. Combine the equalities or inequalities in the displayed calculation. Establish `ileft : ∀ u : GA E k, UU (k - (d + 1) + 1) u → ∀ G : GA E k → ℝ≥0∞, Measurable G → ∫⁻ n, G (u * n) ∂nuD E k d = ∫⁻ n, G n ∂nuD E k d`. Introduce `u hu G hG`. Combine the equalities or inequalities in the displayed calculation.

Establish `iconj : ∀ x : UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → Ad E, ∀ G : GA E k → ℝ≥0∞, Measurable G → ∫⁻ n, G (blkU x * n * blkU (-x)) ∂nuD E k d = ∫⁻ n, G n ∂nuD E k d`. Introduce `x G hG`. Establish `h1` using `hconj (blkU x) (blk_blkU_succ x) G hG`. Rewrite `h1` using `[hDt _ _ (UU_blk x), inv_one, ENNReal.ofReal_one, one_pow, one_mul, bU_inv]`. Conclude with `h1`.

Establish `iconj' : ∀ x : UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → Ad E, ∀ G : GA E k → ℝ≥0∞, Measurable G → ∫⁻ n, G (blkU (-x) * n * blkU x) ∂nuD E k d = ∫⁻ n, G n ∂nuD E k d`. Introduce `x G hG`. Establish `h1` using `iconj (-x) G hG`. Rewrite `h1` using `[neg_neg]`. Conclude with `h1`.

Use `⟨inferInstance, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[nuD_succ, ae_map_iff (meas_blkmul _).aemeasurable (isClosed_UU _).measurableSet]`. Establish `h0 : ∀ᵐ p ∂(vecMeasure E (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)))).prod (nuD E k d), UU (k - (d + 1) + 1) p.2`. Rewrite `hae`, the goal using `[ae_iff]`. Establish `hs : {p : (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → Ad E) × GA E k | ¬UU (k - (d + 1) + 1) p.2} = Set.univ ×ˢ {n | ¬UU (k - (d + 1) + 1) n}`.

Use extensionality with `p`. Simplify using the standard rewrite rules. Rewrite using `[hs, Measure.prod_prod, hae, mul_zero]`. Conclude with `h0.mono fun p hp => UU_blk_mul hj p.1 p.2 hp`. Use `Measure.ext_of_lintegral _ fun F hF => ?_` and prove the remaining obligations.

Establish `hI : ∀ x : UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → Ad E, ∫⁻ n, F (blkU x * n)⁻¹ ∂nuD E k d = ∫⁻ n, F (blkU (-x) * n) ∂nuD E k d`. Introduce `x`. Combine the equalities or inequalities in the displayed calculation. Consider the case `rw [← mul_assoc, ← mul_assoc, bU_neg_mul, one_mul]`. Consider the case `(rw [← bU_inv]; group))`.

Use `_ = ∫⁻ n, F (blkU (-x) * n) ∂nuD E k d := iconj x (fun n => F (blkU (-x) * n)) (hF.comp (meas_lmul _))`. Establish `hH : Measurable fun u : GA E k => ∫⁻ n, F (u * n) ∂nuD E k d` using `(hF.comp measurable_mt_mul).lintegral_prod_right'`. Combine the equalities or inequalities in the displayed calculation. Introduce `u hu`. Take `⟨y, u', hu', rfl⟩` from `UU_split hj u hu`.

Use `Measure.ext_of_lintegral _ fun F hF => ?_` and prove the remaining obligations. Establish `hL : ∀ x : UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → Ad E, ∫⁻ n, F (blkU y * u' * (blkU x * n)) ∂nuD E k d = ∫⁻ n, F (blkU (y + x) * n) ∂nuD E k d`. Introduce `x`. Establish `hG : Measurable fun m : GA E k => F (blkU y * m)` using `hF.comp (meas_lmul _)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← bU_inv]`. Use the proof step `group)`. Use `_ = ∫⁻ n, F (blkU y * (n * blkU x)) ∂nuD E k d := ileft u' hu' (fun n => F (blkU y * (n * blkU x))) (hG.comp (meas_rmul _))`. Use `_ = ∫⁻ n, F (blkU y * (blkU x * (blkU (-x) * n * blkU x))) ∂nuD E k d := lintegral_congr fun n => congrArg F (by`. Rewrite using `[← bU_inv]`.

Use the proof step `group)`. Use `_ = ∫⁻ n, F (blkU y * (blkU x * n)) ∂nuD E k d := iconj' x (fun n => F (blkU y * (blkU x * n))) (hG.comp (meas_lmul _))`. Use `_ = ∫⁻ n, F (blkU (y + x) * n) ∂nuD E k d := lintegral_congr fun n => congrArg F (by rw [bU_add, mul_assoc])`. Combine the equalities or inequalities in the displayed calculation. Introduce `g hg F hF`.

Establish `hg' : GlobalTheory (k - (d + 1) + 1) g` using `blk_succ hg`. Establish `hH : Measurable fun u : GA E k => ∫⁻ n, F (u * n) ∂nuD E k d` using `(hF.comp measurable_mt_mul).lintegral_prod_right'`. Establish `hc : Measurable fun x : UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → Ad E => g * blkU x * g⁻¹` using `((continuous_mul_const g⁻¹).comp ((continuous_const_mul g).comp (cont_blk _))).measurable`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[lint_succ d F hF, pow_succ, mul_assoc]`.
-/
theorem props_succ (hDt : ∀ j (u : GA E k), UU j u → Dt u = 1)
    (hMod : ∀ j < k, ∀ g : GA E k, GlobalTheory j g → ∀ F : GA E k → ℝ≥0∞, Measurable F →
      ∫⁻ x : UnipotentBlockColumnIndex k j j → Ad E, F (g * blkU x * g⁻¹) ∂vecMeasure E _ =
        ENNReal.ofReal (Dt g)⁻¹ * ∫⁻ x : UnipotentBlockColumnIndex k j j → Ad E, F (blkU x) ∂vecMeasure E _)
    (d : ℕ) (hd : d + 1 ≤ k) (ih : Props (E := E) (k := k) d) : Props (E := E) (k := k) (d + 1) := by
  obtain ⟨-, hae, hinv, hleft, hconj⟩ := ih
  have hkd : k - d = k - (d + 1) + 1 := by omega
  rw [hkd] at hae hleft hconj
  have hj : k - (d + 1) < k := by omega

  have iinv : ∀ G : GA E k → ℝ≥0∞, Measurable G →
      ∫⁻ n, G n⁻¹ ∂nuD E k d = ∫⁻ n, G n ∂nuD E k d := by
    intro G hG
    calc ∫⁻ n, G n⁻¹ ∂nuD E k d = ∫⁻ n, G n ∂Measure.map (fun h => h⁻¹) (nuD E k d) :=
          (lintegral_map hG meas_inv).symm
      _ = ∫⁻ n, G n ∂nuD E k d := by rw [hinv]
  have ileft : ∀ u : GA E k, UU (k - (d + 1) + 1) u → ∀ G : GA E k → ℝ≥0∞, Measurable G →
      ∫⁻ n, G (u * n) ∂nuD E k d = ∫⁻ n, G n ∂nuD E k d := by
    intro u hu G hG
    calc ∫⁻ n, G (u * n) ∂nuD E k d = ∫⁻ n, G n ∂Measure.map (fun h => u * h) (nuD E k d) :=
          (lintegral_map hG (meas_lmul u)).symm
      _ = ∫⁻ n, G n ∂nuD E k d := by rw [hleft u hu]
  have iconj : ∀ x : UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → Ad E, ∀ G : GA E k → ℝ≥0∞, Measurable G →
      ∫⁻ n, G (blkU x * n * blkU (-x)) ∂nuD E k d = ∫⁻ n, G n ∂nuD E k d := by
    intro x G hG
    have h1 := hconj (blkU x) (blk_blkU_succ x) G hG
    rw [hDt _ _ (UU_blk x), inv_one, ENNReal.ofReal_one, one_pow, one_mul, bU_inv] at h1
    exact h1
  have iconj' : ∀ x : UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → Ad E, ∀ G : GA E k → ℝ≥0∞, Measurable G →
      ∫⁻ n, G (blkU (-x) * n * blkU x) ∂nuD E k d = ∫⁻ n, G n ∂nuD E k d := by
    intro x G hG
    have h1 := iconj (-x) G hG
    rw [neg_neg] at h1
    exact h1
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  ·
    rw [nuD_succ, ae_map_iff (meas_blkmul _).aemeasurable (isClosed_UU _).measurableSet]
    have h0 : ∀ᵐ p ∂(vecMeasure E (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)))).prod (nuD E k d),
        UU (k - (d + 1) + 1) p.2 := by
      rw [ae_iff] at hae ⊢
      have hs : {p : (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → Ad E) × GA E k | ¬UU (k - (d + 1) + 1) p.2} =
          Set.univ ×ˢ {n | ¬UU (k - (d + 1) + 1) n} := by
        ext p
        simp
      rw [hs, Measure.prod_prod, hae, mul_zero]
    exact h0.mono fun p hp => UU_blk_mul hj p.1 p.2 hp
  ·
    refine Measure.ext_of_lintegral _ fun F hF => ?_
    have hI : ∀ x : UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → Ad E,
        ∫⁻ n, F (blkU x * n)⁻¹ ∂nuD E k d = ∫⁻ n, F (blkU (-x) * n) ∂nuD E k d := by
      intro x
      calc ∫⁻ n, F (blkU x * n)⁻¹ ∂nuD E k d = ∫⁻ n, F (n⁻¹ * blkU (-x)) ∂nuD E k d :=
            lintegral_congr fun n => by rw [_root_.mul_inv_rev, bU_inv]
        _ = ∫⁻ n, F (n * blkU (-x)) ∂nuD E k d :=
            iinv (fun n => F (n * blkU (-x))) (hF.comp (meas_rmul _))
        _ = ∫⁻ n, F (blkU (-x) * (blkU x * n * blkU (-x))) ∂nuD E k d :=
            lintegral_congr fun n => congrArg F (by
              first
              | rw [← mul_assoc, ← mul_assoc, bU_neg_mul, one_mul]
              | (rw [← bU_inv]; group))
        _ = ∫⁻ n, F (blkU (-x) * n) ∂nuD E k d :=
            iconj x (fun n => F (blkU (-x) * n)) (hF.comp (meas_lmul _))
    have hH : Measurable fun u : GA E k => ∫⁻ n, F (u * n) ∂nuD E k d :=
      (hF.comp measurable_mt_mul).lintegral_prod_right'
    calc ∫⁻ h, F h ∂Measure.map (fun h => h⁻¹) (nuD E k (d + 1))
        = ∫⁻ h, F h⁻¹ ∂nuD E k (d + 1) := lintegral_map hF meas_inv
      _ = ∫⁻ x, ∫⁻ n, F (blkU x * n)⁻¹ ∂nuD E k d ∂vecMeasure E (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1))) :=
          lint_succ d _ (hF.comp meas_inv)
      _ = ∫⁻ x, ∫⁻ n, F (blkU (-x) * n) ∂nuD E k d ∂vecMeasure E (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1))) :=
          lintegral_congr hI
      _ = ∫⁻ x, ∫⁻ n, F (blkU x * n) ∂nuD E k d ∂vecMeasure E (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1))) :=
          lintegral_neg_eq_self (fun x : UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → Ad E =>
            ∫⁻ n, F (blkU x * n) ∂nuD E k d)
      _ = ∫⁻ h, F h ∂nuD E k (d + 1) := (lint_succ d F hF).symm
  ·
    intro u hu
    obtain ⟨y, u', hu', rfl⟩ := UU_split hj u hu
    refine Measure.ext_of_lintegral _ fun F hF => ?_
    have hL : ∀ x : UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → Ad E,
        ∫⁻ n, F (blkU y * u' * (blkU x * n)) ∂nuD E k d = ∫⁻ n, F (blkU (y + x) * n) ∂nuD E k d := by
      intro x
      have hG : Measurable fun m : GA E k => F (blkU y * m) := hF.comp (meas_lmul _)
      calc ∫⁻ n, F (blkU y * u' * (blkU x * n)) ∂nuD E k d
          = ∫⁻ n, F (blkU y * (u' * blkU x * n)) ∂nuD E k d :=
            lintegral_congr fun n => congrArg F (by simp only [mul_assoc])
        _ = ∫⁻ n, F (blkU y * (u' * blkU x * (blkU (-x) * n * blkU x))) ∂nuD E k d :=
            (iconj' x (fun n => F (blkU y * (u' * blkU x * n))) (hG.comp (meas_lmul _))).symm
        _ = ∫⁻ n, F (blkU y * (u' * n * blkU x)) ∂nuD E k d :=
            lintegral_congr fun n => congrArg F (by
              rw [← bU_inv]; group)
        _ = ∫⁻ n, F (blkU y * (n * blkU x)) ∂nuD E k d :=
            ileft u' hu' (fun n => F (blkU y * (n * blkU x))) (hG.comp (meas_rmul _))
        _ = ∫⁻ n, F (blkU y * (blkU x * (blkU (-x) * n * blkU x))) ∂nuD E k d :=
            lintegral_congr fun n => congrArg F (by
              rw [← bU_inv]; group)
        _ = ∫⁻ n, F (blkU y * (blkU x * n)) ∂nuD E k d :=
            iconj' x (fun n => F (blkU y * (blkU x * n))) (hG.comp (meas_lmul _))
        _ = ∫⁻ n, F (blkU (y + x) * n) ∂nuD E k d :=
            lintegral_congr fun n => congrArg F (by rw [bU_add, mul_assoc])
    calc ∫⁻ h, F h ∂Measure.map (fun h => blkU y * u' * h) (nuD E k (d + 1))
        = ∫⁻ h, F (blkU y * u' * h) ∂nuD E k (d + 1) := lintegral_map hF (meas_lmul _)
      _ = ∫⁻ x, ∫⁻ n, F (blkU y * u' * (blkU x * n)) ∂nuD E k d
            ∂vecMeasure E (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1))) :=
          lint_succ d _ (hF.comp (meas_lmul _))
      _ = ∫⁻ x, ∫⁻ n, F (blkU (y + x) * n) ∂nuD E k d
            ∂vecMeasure E (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1))) := lintegral_congr hL
      _ = ∫⁻ x, ∫⁻ n, F (blkU x * n) ∂nuD E k d ∂vecMeasure E (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1))) :=
          lintegral_add_left_eq_self (fun x : UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → Ad E =>
            ∫⁻ n, F (blkU x * n) ∂nuD E k d) y
      _ = ∫⁻ h, F h ∂nuD E k (d + 1) := (lint_succ d F hF).symm
  ·
    intro g hg F hF
    have hg' : GlobalTheory (k - (d + 1) + 1) g := blk_succ hg
    have hH : Measurable fun u : GA E k => ∫⁻ n, F (u * n) ∂nuD E k d :=
      (hF.comp measurable_mt_mul).lintegral_prod_right'
    have hc : Measurable fun x : UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → Ad E => g * blkU x * g⁻¹ :=
      ((continuous_mul_const g⁻¹).comp ((continuous_const_mul g).comp (cont_blk _))).measurable
    calc ∫⁻ h, F (g * h * g⁻¹) ∂nuD E k (d + 1)
        = ∫⁻ x, ∫⁻ n, F (g * (blkU x * n) * g⁻¹) ∂nuD E k d
            ∂vecMeasure E (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1))) :=
          lint_succ d (fun h => F (g * h * g⁻¹)) (hF.comp ((meas_lmul g).mul_const g⁻¹))
      _ = ∫⁻ x, ∫⁻ n, F (g * blkU x * g⁻¹ * (g * n * g⁻¹)) ∂nuD E k d
            ∂vecMeasure E (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1))) :=
          lintegral_congr fun x => lintegral_congr fun n => congrArg F (by group)
      _ = ∫⁻ x, ENNReal.ofReal (Dt g)⁻¹ ^ d * ∫⁻ n, F (g * blkU x * g⁻¹ * n) ∂nuD E k d
            ∂vecMeasure E (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1))) :=
          lintegral_congr fun x =>
            hconj g hg' (fun n => F (g * blkU x * g⁻¹ * n)) (hF.comp (meas_lmul _))
      _ = ENNReal.ofReal (Dt g)⁻¹ ^ d * ∫⁻ x, ∫⁻ n, F (g * blkU x * g⁻¹ * n) ∂nuD E k d
            ∂vecMeasure E (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1))) :=
          lintegral_const_mul _ (hH.comp hc)
      _ = ENNReal.ofReal (Dt g)⁻¹ ^ d * (ENNReal.ofReal (Dt g)⁻¹ * ∫⁻ x, ∫⁻ n, F (blkU x * n) ∂nuD E k d
            ∂vecMeasure E (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)))) :=
          congrArg (fun t => ENNReal.ofReal (Dt g)⁻¹ ^ d * t)
            (hMod _ hj g hg (fun u => ∫⁻ n, F (u * n) ∂nuD E k d) hH)
      _ = ENNReal.ofReal (Dt g)⁻¹ ^ (d + 1) * ∫⁻ h, F h ∂nuD E k (d + 1) := by
          rw [lint_succ d F hF, pow_succ, mul_assoc]

/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero => intro _`. Conclude with `props_zero`. Consider the case `succ d ih => intro hd; exact props_succ hDt hMod d hd (ih (by omega))`.
-/
theorem props (hDt : ∀ j (u : GA E k), UU j u → Dt u = 1)
    (hMod : ∀ j < k, ∀ g : GA E k, GlobalTheory j g → ∀ F : GA E k → ℝ≥0∞, Measurable F →
      ∫⁻ x : UnipotentBlockColumnIndex k j j → Ad E, F (g * blkU x * g⁻¹) ∂vecMeasure E _ =
        ENNReal.ofReal (Dt g)⁻¹ * ∫⁻ x : UnipotentBlockColumnIndex k j j → Ad E, F (blkU x) ∂vecMeasure E _) :
    ∀ d ≤ k, Props (E := E) (k := k) d := by
  intro d
  induction d with
  | zero => intro _; exact props_zero
  | succ d ih => intro hd; exact props_succ hDt hMod d hd (ih (by omega))

end HermitianFormNormLemmas

/- English proof (translation)
Introduce `hD0 hM E _ _ _ k d hd`. Conclude with `HermitianFormNormLemmas.props (hD0 E k).2.2.2.2.1 (hM E k) d hd`.
-/
theorem monic_polynomial_is_matrix_charpoly : D0 → ColumnConjugationMeasure → N1 := by
  intro hD0 hM E _ _ _ k d hd
  exact HermitianFormNormLemmas.props (hD0 E k).2.2.2.2.1 (hM E k) d hd

end PositivityTheory.AdelicQuotientData

end
