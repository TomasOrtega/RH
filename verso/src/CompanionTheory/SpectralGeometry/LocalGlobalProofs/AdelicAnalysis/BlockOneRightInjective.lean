import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.StabFirst

section Blocks

variable {K : Type} [CommRing K] {M : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma blockOne_zero_zero (t : K) (A : Matrix (Fin M) (Fin M) K) :
    blockOne t A 0 0 = t := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma blockOne_zero_succ (t : K) (A : Matrix (Fin M) (Fin M) K) (j : Fin M) :
    blockOne t A 0 j.succ = 0 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma blockOne_succ_zero (t : K) (A : Matrix (Fin M) (Fin M) K) (i : Fin M) :
    blockOne t A i.succ 0 = 0 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma blockOne_succ_succ (t : K) (A : Matrix (Fin M) (Fin M) K) (i j : Fin M) :
    blockOne t A i.succ j.succ = A i j := rfl

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_succ]`.
-/
lemma blockOne_mul (a b : K) (A B : Matrix (Fin M) (Fin M) K) :
    blockOne a A * blockOne b B = blockOne (a * b) (A * B) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>`. Simplify using `[Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]`.
-/
lemma blockOne_one : blockOne (1 : K) (1 : Matrix (Fin M) (Fin M) K) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `using congrFun (congrFun h i.succ) j.succ`.
-/
lemma blockOne_right_injective {a b : K} {A B : Matrix (Fin M) (Fin M) K}
    (h : blockOne a A = blockOne b B) : A = B := by
  ext i j
  simpa using congrFun (congrFun h i.succ) j.succ

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp`.
-/
lemma map_blockOne {L : Type} [CommRing L] (φ : K →+* L) (a : K) (A : Matrix (Fin M) (Fin M) K) :
    (blockOne a A).map φ = blockOne (φ a) (A.map φ) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp [cT]`.
-/
lemma cT_blockOne (σ : K →+* K) (a : K) (A : Matrix (Fin M) (Fin M) K) :
    cT σ (blockOne a A) = blockOne (σ a) (cT σ A) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp [cT]

def blockHom : Matrix (Fin M) (Fin M) K →* Matrix (Fin (M + 1)) (Fin (M + 1)) K where
  toFun A := blockOne 1 A
  map_one' := blockOne_one
  map_mul' A B := by rw [blockOne_mul, one_mul]

def blockGL : GL (Fin M) K →* GL (Fin (M + 1)) K := Units.map blockHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma coe_blockGL (g : GL (Fin M) K) :
    ((blockGL g : GL (Fin (M + 1)) K) : Matrix (Fin (M + 1)) (Fin (M + 1)) K) =
      blockOne 1 (g : Matrix (Fin M) (Fin M) K) := rfl

/- English proof (translation)
Introduce `a b h`. Apply `Units.ext` to reduce the goal to its premises. Apply `blockOne_right_injective (a := (1 : K)) (b := 1)` to reduce the goal to its premises. Simplify `congrArg (fun g : GL (Fin (M + 1)) K => (g : Matrix (Fin (M + 1)) (Fin (M + 1)) K)) h` using `[coe_blockGL]`.
-/
lemma blockGL_injective : Function.Injective (blockGL : GL (Fin M) K → GL (Fin (M + 1)) K) := by
  intro a b h
  apply Units.ext
  apply blockOne_right_injective (a := (1 : K)) (b := 1)
  simpa [coe_blockGL] using congrArg (fun g : GL (Fin (M + 1)) K =>
    (g : Matrix (Fin (M + 1)) (Fin (M + 1)) K)) h

/- English proof (translation)
Establish `hg' : cT σ (g : Matrix (Fin M) (Fin M) K) * J * (g : Matrix (Fin M) (Fin M) K) = J` using `hg`. Express the relevant statement in the definitionally equal form `cT σ (blockOne 1 (g : Matrix (Fin M) (Fin M) K)) * blockOne s J * blockOne 1 (g : Matrix (Fin M) (Fin M) K) = blockOne s J`. Rewrite using `[cT_blockOne, blockOne_mul, blockOne_mul, hg', map_one, one_mul, mul_one]`.
-/
lemma blockGL_mem_UJ (σ : K →+* K) (J : Matrix (Fin M) (Fin M) K) (s : K) {g : GL (Fin M) K}
    (hg : g ∈ UJ σ J) : blockGL g ∈ UJ σ (blockOne s J) := by
  have hg' : cT σ (g : Matrix (Fin M) (Fin M) K) * J * (g : Matrix (Fin M) (Fin M) K) = J := hg
  change cT σ (blockOne 1 (g : Matrix (Fin M) (Fin M) K)) * blockOne s J *
    blockOne 1 (g : Matrix (Fin M) (Fin M) K) = blockOne s J
  rw [cT_blockOne, blockOne_mul, blockOne_mul, hg', map_one, one_mul, mul_one]

/- English proof (translation)
Establish `hg' : cT σ (blockOne 1 (g : Matrix (Fin M) (Fin M) K)) * blockOne s J * blockOne 1 (g : Matrix (Fin M) (Fin M) K) = blockOne s J` using `hg`. Rewrite `hg'` using `[cT_blockOne, blockOne_mul, blockOne_mul]`. Conclude with `blockOne_right_injective hg'`.
-/
lemma of_blockGL_mem_UJ (σ : K →+* K) (J : Matrix (Fin M) (Fin M) K) (s : K) {g : GL (Fin M) K}
    (hg : blockGL g ∈ UJ σ (blockOne s J)) : g ∈ UJ σ J := by
  have hg' : cT σ (blockOne 1 (g : Matrix (Fin M) (Fin M) K)) * blockOne s J *
    blockOne 1 (g : Matrix (Fin M) (Fin M) K) = blockOne s J := hg
  rw [cT_blockOne, blockOne_mul, blockOne_mul] at hg'
  exact blockOne_right_injective hg'

/- English proof (translation)
Establish `h1 : ∀ k, (cT σ h * blockOne s J) 0 k = blockOne s J 0 k`. Introduce `k`. Rewrite using `[Matrix.mul_apply, Fin.sum_univ_succ]`. Simplify using `[cT, h00, hi0]`. Establish `h2 : ∀ j : Fin M, h 0 j.succ = 0`.

Introduce `j`. Establish `e` using `congrFun (congrFun hm 0) j.succ`. Rewrite `e` using `[Matrix.mul_apply]`. Simplify using `only [h1] at e`. Rewrite `e` using `[Fin.sum_univ_succ]`.

Simplify using `at e`. Conclude with `(hs.mul_right_eq_zero).1 e`. Use extensionality with `i j`. Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>`. Simplify using `[h00, hi0, h2]`.
-/
lemma eq_blockOne_of_col (σ : K →+* K) (J : Matrix (Fin M) (Fin M) K) {s : K} (hs : IsUnit s)
    {h : Matrix (Fin (M + 1)) (Fin (M + 1)) K} (hm : cT σ h * blockOne s J * h = blockOne s J)
    (h00 : h 0 0 = 1) (hi0 : ∀ i : Fin M, h i.succ 0 = 0) :
    h = blockOne 1 (h.submatrix Fin.succ Fin.succ) := by
  have h1 : ∀ k, (cT σ h * blockOne s J) 0 k = blockOne s J 0 k := by
    intro k
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    simp [cT, h00, hi0]
  have h2 : ∀ j : Fin M, h 0 j.succ = 0 := by
    intro j
    have e := congrFun (congrFun hm 0) j.succ
    rw [Matrix.mul_apply] at e
    simp only [h1] at e
    rw [Fin.sum_univ_succ] at e
    simp at e
    exact (hs.mul_right_eq_zero).1 e
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [h00, hi0, h2]

/- English proof (translation)
Use `set A := (h : Matrix (Fin (M + 1)) (Fin (M + 1)) K) with hA`. Use `set B := ((h⁻¹ : GL (Fin (M + 1)) K) : Matrix (Fin (M + 1)) (Fin (M + 1)) K) with hB`. Establish `hAB : A * B = 1` using `by rw [hA, hB]; exact Units.mul_inv h`. Establish `hBA : B * A = 1` using `by rw [hA, hB]; exact Units.inv_mul h`. Establish `eA` using `eq_blockOne_of_col σ J hs (h := A) hm h00 hi0`.

Establish `hcol : ∀ a, (B * A) a 0 = B a 0`. Introduce `a`. Rewrite using `[Matrix.mul_apply, Fin.sum_univ_succ]`. Simplify using `[h00, hi0]`. Establish `hB00 : B 0 0 = 1` using `by rw [← hcol, hBA]; simp`.

Establish `hBi0 : ∀ i : Fin M, B i.succ 0 = 0`. Introduce `i`. Rewrite using `[← hcol, hBA]`. Simplify using `[Matrix.one_apply, Fin.succ_ne_zero]`. Establish `eB` using `eq_blockOne_of_col σ J hs (h := B) ((UJ σ (blockOne s J)).inv_mem hm) hB00 hBi0`.

Establish `e1 : A.submatrix Fin.succ Fin.succ * B.submatrix Fin.succ Fin.succ = 1`. Apply `blockOne_right_injective (a := (1 : K)) (b := 1)` to reduce the goal to its premises. Rewrite using `[← one_mul (1 : K), ← blockOne_mul, ← eA, ← eB, hAB, one_mul, blockOne_one]`. Establish `e2 : B.submatrix Fin.succ Fin.succ * A.submatrix Fin.succ Fin.succ = 1`. Apply `blockOne_right_injective (a := (1 : K)) (b := 1)` to reduce the goal to its premises.

Rewrite using `[← one_mul (1 : K), ← blockOne_mul, ← eA, ← eB, hBA, one_mul, blockOne_one]`. Use `⟨⟨A.submatrix Fin.succ Fin.succ, B.submatrix Fin.succ Fin.succ, e1, e2⟩, ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[coe_blockGL]`. Conclude with `eA.symm`.
-/
lemma exists_blockGL (σ : K →+* K) (J : Matrix (Fin M) (Fin M) K) {s : K} (hs : IsUnit s)
    {h : GL (Fin (M + 1)) K} (hm : h ∈ UJ σ (blockOne s J))
    (h00 : (h : Matrix (Fin (M + 1)) (Fin (M + 1)) K) 0 0 = 1)
    (hi0 : ∀ i : Fin M, (h : Matrix (Fin (M + 1)) (Fin (M + 1)) K) i.succ 0 = 0) :
    ∃ g : GL (Fin M) K, blockGL g = h := by
  set A := (h : Matrix (Fin (M + 1)) (Fin (M + 1)) K) with hA
  set B := ((h⁻¹ : GL (Fin (M + 1)) K) : Matrix (Fin (M + 1)) (Fin (M + 1)) K) with hB
  have hAB : A * B = 1 := by rw [hA, hB]; exact Units.mul_inv h
  have hBA : B * A = 1 := by rw [hA, hB]; exact Units.inv_mul h
  have eA := eq_blockOne_of_col σ J hs (h := A) hm h00 hi0
  have hcol : ∀ a, (B * A) a 0 = B a 0 := by
    intro a
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    simp [h00, hi0]
  have hB00 : B 0 0 = 1 := by rw [← hcol, hBA]; simp
  have hBi0 : ∀ i : Fin M, B i.succ 0 = 0 := by
    intro i
    rw [← hcol, hBA]
    simp [Matrix.one_apply, Fin.succ_ne_zero]
  have eB := eq_blockOne_of_col σ J hs (h := B) ((UJ σ (blockOne s J)).inv_mem hm) hB00 hBi0
  have e1 : A.submatrix Fin.succ Fin.succ * B.submatrix Fin.succ Fin.succ = 1 := by
    apply blockOne_right_injective (a := (1 : K)) (b := 1)
    rw [← one_mul (1 : K), ← blockOne_mul, ← eA, ← eB, hAB, one_mul, blockOne_one]
  have e2 : B.submatrix Fin.succ Fin.succ * A.submatrix Fin.succ Fin.succ = 1 := by
    apply blockOne_right_injective (a := (1 : K)) (b := 1)
    rw [← one_mul (1 : K), ← blockOne_mul, ← eA, ← eB, hBA, one_mul, blockOne_one]
  refine ⟨⟨A.submatrix Fin.succ Fin.succ, B.submatrix Fin.succ Fin.succ, e1, e2⟩, ?_⟩
  apply Units.ext
  rw [coe_blockGL]
  exact eA.symm

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(blockOne 1 (g : Matrix (Fin M) (Fin M) K)).map φ = blockOne 1 ((g : Matrix (Fin M) (Fin M) K).map φ)`. Rewrite using `[map_blockOne, map_one]`.
-/
lemma bc_blockGL {L : Type} [CommRing L] (φ : K →+* L) (g : GL (Fin M) K) :
    bc φ (blockGL g) = blockGL (bc φ g) := by
  apply Units.ext
  change (blockOne 1 (g : Matrix (Fin M) (Fin M) K)).map φ =
    blockOne 1 ((g : Matrix (Fin M) (Fin M) K).map φ)
  rw [map_blockOne, map_one]

/- English proof (translation)
Simplify using `[Matrix.mulVec, dotProduct, Fin.sum_univ_succ]`.
-/
lemma mulVec_first (A : Matrix (Fin (M + 1)) (Fin (M + 1)) K) (a : Fin (M + 1)) :
    A.mulVec (Fin.cons 1 (fun _ => 0)) a = A a 0 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/- English proof (translation)
Use extensionality with `a`. Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) a <;>`. Simplify using `[Matrix.mulVec, dotProduct, Fin.sum_univ_succ]`.
-/
lemma blockOne_mulVec_cons (A : Matrix (Fin M) (Fin M) K) (x : Fin M → K) :
    (blockOne 1 A).mulVec (Fin.cons 0 x) = Fin.cons 0 (A.mulVec x) := by
  ext a
  refine Fin.cases ?_ (fun i => ?_) a <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/- English proof (translation)
Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j`. Conclude with `continuous_const`. Conclude with `continuous_const`. Conclude with `continuous_const`.

Conclude with `continuous_id.matrix_elem i j`.
-/
lemma continuous_blockOne [TopologicalSpace K] :
    Continuous (fun A : Matrix (Fin M) (Fin M) K => blockOne (1 : K) A) := by
  refine continuous_matrix fun i j => ?_
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact continuous_id.matrix_elem i j

end Blocks

section Grp

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (s : E)

/- English proof (translation)
The claim follows from `map_blockOne (inclR (F := F) R) s J`.
-/
lemma JR_blockOne : JR (F := F) R (blockOne s J) = blockOne (inclR (F := F) R s) (JR (F := F) R J) :=
  map_blockOne (inclR (F := F) R) s J

/- English proof (translation)
Unfold `HR`. Rewrite using `[JR_blockOne]`. Conclude with `blockGL_mem_UJ _ _ _ hg`.
-/
lemma blockGL_mem_HR {g : GL (Fin M) (R ⊗[F] E)} (hg : g ∈ HR R σ J) :
    blockGL g ∈ HR R σ (blockOne s J) := by
  unfold HR
  rw [JR_blockOne]
  exact blockGL_mem_UJ _ _ _ hg

/- English proof (translation)
Unfold `HR at hg ⊢`. Rewrite `hg` using `[JR_blockOne]`. Conclude with `of_blockGL_mem_UJ _ _ _ hg`.
-/
lemma of_blockGL_mem_HR {g : GL (Fin M) (R ⊗[F] E)} (hg : blockGL g ∈ HR R σ (blockOne s J)) :
    g ∈ HR R σ J := by
  unfold HR at hg ⊢
  rw [JR_blockOne] at hg
  exact of_blockGL_mem_UJ _ _ _ hg

def mkHA (g : GL (Fin M) (R ⊗[F] E)) (hg : g ∈ HR R σ J) : HA R σ J :=
  (⟨g, hg⟩ : HR R σ J)

/- English proof (translation)
The claim follows from `Subtype.property (p := fun g => g ∈ HR R σ J) u`.
-/
lemma mat_mem (u : HA R σ J) : HA.mat R σ J u ∈ HR R σ J :=
  Subtype.property (p := fun g => g ∈ HR R σ J) u

/- English proof (translation)
Introduce `_ _ h` and use `Subtype.ext (p := fun g => g ∈ HR R σ J) h`.
-/
lemma mat_injective : Function.Injective (HA.mat R σ J) :=
  fun _ _ h => Subtype.ext (p := fun g => g ∈ HR R σ J) h

def iotaHom : HA R σ J →* HA R σ (blockOne s J) where
  toFun u := mkHA R σ _ (blockGL (HA.mat R σ J u)) (blockGL_mem_HR R σ J s (mat_mem R σ J u))
  map_one' := mat_injective R σ _ (map_one (blockGL (K := R ⊗[F] E) (M := M)))
  map_mul' a b := mat_injective R σ _
    (map_mul (blockGL (K := R ⊗[F] E) (M := M)) (HA.mat R σ J a) (HA.mat R σ J b))

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma mat_iotaHom (u : HA R σ J) :
    HA.mat R σ _ (iotaHom R σ J s u) = blockGL (HA.mat R σ J u) := rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `e`. Establish `e' : ∀ a, (HA.mat R σ _ h : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) a 0 = (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E) a`. Introduce `a`. Conclude with `(mulVec_first _ a).symm.trans (congrFun (congrFun e 0) a)`.

Conclude with `⟨by simpa using e' 0, fun i => by simpa using e' i.succ⟩`. Introduce and unpack `⟨h0, hi⟩`. Use function extensionality and compare the values at `c a`. Express the relevant statement in the definitionally equal form `(HA.mat R σ _ h : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)).mulVec _ a = _`. Rewrite using `[mulVec_first]`.

Use `Fin.cases ?_ (fun i => ?_) a` and prove the remaining obligations. Simplify using `using h0`. Simplify using `using hi i`.
-/
lemma act_first_iff {n : ℕ} (h : HA R σ (blockOne s J)) :
    actW R σ _ h (fun _ : Fin n.succ => Fin.cons 1 (fun _ => 0)) =
        (fun _ : Fin n.succ => Fin.cons 1 (fun _ => 0)) ↔
      ((HA.mat R σ _ h : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) 0 0 = 1 ∧
        ∀ i : Fin M, (HA.mat R σ _ h : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) i.succ 0 = 0) := by
  constructor
  · intro e
    have e' : ∀ a, (HA.mat R σ _ h : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) a 0 =
        (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E) a := by
      intro a
      exact (mulVec_first _ a).symm.trans (congrFun (congrFun e 0) a)
    exact ⟨by simpa using e' 0, fun i => by simpa using e' i.succ⟩
  · rintro ⟨h0, hi⟩
    funext c a
    change (HA.mat R σ _ h : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)).mulVec _ a = _
    rw [mulVec_first]
    refine Fin.cases ?_ (fun i => ?_) a
    · simpa using h0
    · simpa using hi i

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, rfl⟩`. Rewrite using `[mat_iotaHom, coe_blockGL]`. Conclude with `⟨rfl, fun _ => rfl⟩`. Introduce and unpack `⟨h0, hi⟩`.

Establish `hu : IsUnit (inclR (F` using `F) R s) := (isUnit_iff_ne_zero.2 hs).map (inclR (F := F) R)`. Establish `hm : HA.mat R σ _ h ∈ UJ (sigR R σ) (blockOne (inclR (F` using `F) R s) (JR (F := F) R J)) := by`. Use `mat_mem R σ _ h` as an intermediate fact. Unfold `HR at this`. Rewrite `this` using `[JR_blockOne]`. Then use the resulting hypothesis.

Take `⟨g, hg⟩` from `exists_blockGL _ _ hu hm h0 hi`. Establish `hgm : g ∈ HR R σ J`. Apply `of_blockGL_mem_HR R σ J s` to reduce the goal to its premises. Rewrite using `[hg]`. Conclude with `mat_mem R σ _ h`.

Conclude with `⟨mkHA R σ J g hgm, mat_injective R σ _ hg⟩`.
-/
lemma mem_range_iff (hs : s ≠ 0) (h : HA R σ (blockOne s J)) :
    h ∈ (iotaHom R σ J s).range ↔
      ((HA.mat R σ _ h : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) 0 0 = 1 ∧
        ∀ i : Fin M, (HA.mat R σ _ h : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) i.succ 0 = 0) := by
  constructor
  · rintro ⟨u, rfl⟩
    rw [mat_iotaHom, coe_blockGL]
    exact ⟨rfl, fun _ => rfl⟩
  · rintro ⟨h0, hi⟩
    have hu : IsUnit (inclR (F := F) R s) := (isUnit_iff_ne_zero.2 hs).map (inclR (F := F) R)
    have hm : HA.mat R σ _ h ∈ UJ (sigR R σ) (blockOne (inclR (F := F) R s) (JR (F := F) R J)) := by
      have := mat_mem R σ _ h
      unfold HR at this
      rwa [JR_blockOne] at this
    obtain ⟨g, hg⟩ := exists_blockGL _ _ hu hm h0 hi
    have hgm : g ∈ HR R σ J := by
      apply of_blockGL_mem_HR R σ J s
      rw [hg]
      exact mat_mem R σ _ h
    exact ⟨mkHA R σ J g hgm, mat_injective R σ _ hg⟩

/- English proof (translation)
Rewrite using `[mat_iotaHom]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨γ, hγ, e⟩`. Break down `subsingleton_or_nontrivial (R ⊗[F] E) with hK | hK` into its components or cases. Establish `: Subsingleton (GL (Fin M) (R ⊗[F] E))` using `inferInstance`.

Rewrite using `[Subsingleton.elim (HA.mat R σ J u) 1]`. Conclude with `one_mem _`. Establish `inj : Function.Injective (inclR (F` using `F) (E := E) R) := by`. Conclude with `RingHom.injective _`. Establish `ent : ∀ a b, inclR (F` using `F) R ((γ : Matrix (Fin (M + 1)) (Fin (M + 1)) E) a b) = blockOne 1 (HA.mat R σ J u : Matrix (Fin M) (Fin M) (R ⊗[F] E)) a b := by`.

Introduce `a b`. Conclude with `congrFun (congrFun (congrArg (fun g : GL (Fin (M + 1)) (R ⊗[F] E) => (g : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E))) e) a) b`. Establish `h0 : (γ : Matrix (Fin (M + 1)) (Fin (M + 1)) E) 0 0 = 1` using `inj (by rw [ent]; simp)`. Establish `hi : ∀ i : Fin M, (γ : Matrix (Fin (M + 1)) (Fin (M + 1)) E) i.succ 0 = 0` using `fun i => inj (by rw [ent]; simp)`. Take `⟨g, rfl⟩` from `exists_blockGL _ _ (isUnit_iff_ne_zero.2 hs) hγ h0 hi`.

Use `⟨g, of_blockGL_mem_UJ _ _ _ hγ, ?_⟩` and prove the remaining obligations. Apply `blockGL_injective` to reduce the goal to its premises. Rewrite using `[← bc_blockGL]`. Conclude with `e`. Introduce and unpack `⟨g, hg, e⟩`.

Conclude with `⟨blockGL g, blockGL_mem_UJ _ _ _ hg, by rw [bc_blockGL, e]⟩`.
-/
lemma mem_HFin_iff (hs : s ≠ 0) (u : HA R σ J) :
    HA.mat R σ _ (iotaHom R σ J s u) ∈ HFin R σ (blockOne s J) ↔ HA.mat R σ J u ∈ HFin R σ J := by
  rw [mat_iotaHom]
  constructor
  · rintro ⟨γ, hγ, e⟩
    rcases subsingleton_or_nontrivial (R ⊗[F] E) with hK | hK
    · have : Subsingleton (GL (Fin M) (R ⊗[F] E)) := inferInstance
      rw [Subsingleton.elim (HA.mat R σ J u) 1]
      exact one_mem _
    · have inj : Function.Injective (inclR (F := F) (E := E) R) := by
        exact RingHom.injective _
      have ent : ∀ a b, inclR (F := F) R ((γ : Matrix (Fin (M + 1)) (Fin (M + 1)) E) a b) =
          blockOne 1 (HA.mat R σ J u : Matrix (Fin M) (Fin M) (R ⊗[F] E)) a b := by
        intro a b
        exact congrFun (congrFun (congrArg (fun g : GL (Fin (M + 1)) (R ⊗[F] E) =>
          (g : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E))) e) a) b
      have h0 : (γ : Matrix (Fin (M + 1)) (Fin (M + 1)) E) 0 0 = 1 :=
        inj (by rw [ent]; simp)
      have hi : ∀ i : Fin M, (γ : Matrix (Fin (M + 1)) (Fin (M + 1)) E) i.succ 0 = 0 :=
        fun i => inj (by rw [ent]; simp)
      obtain ⟨g, rfl⟩ := exists_blockGL _ _ (isUnit_iff_ne_zero.2 hs) hγ h0 hi
      refine ⟨g, of_blockGL_mem_UJ _ _ _ hγ, ?_⟩
      apply blockGL_injective
      rw [← bc_blockGL]
      exact e
  · rintro ⟨g, hg, e⟩
    exact ⟨blockGL g, blockGL_mem_UJ _ _ _ hg, by rw [bc_blockGL, e]⟩

/- English proof (translation)
Use function extensionality and compare the values at `a`. Use `Fin.cases ?_ (fun c => ?_) a` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Express the relevant statement in the definitionally equal form `(blockOne 1 (HA.mat R σ J u : Matrix (Fin M) (Fin M) (R ⊗[F] E))).mulVec (Fin.cons 1 (fun _ => 0)) i = (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E) i`. Rewrite using `[mulVec_first]`.

Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) i <;> simp`. Conclude with `blockOne_mulVec_cons _ _`.
-/
lemma act_iota {n : ℕ} (u : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E) :
    actW R σ _ (iotaHom R σ J s u) (consTup X) = consTup (actW R σ J u X) := by
  funext a
  refine Fin.cases ?_ (fun c => ?_) a
  · funext i
    change (blockOne 1 (HA.mat R σ J u : Matrix (Fin M) (Fin M) (R ⊗[F] E))).mulVec
      (Fin.cons 1 (fun _ => 0)) i = (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E) i
    rw [mulVec_first]
    refine Fin.cases ?_ (fun i => ?_) i <;> simp
  · exact blockOne_mulVec_cons _ _

section Top

variable [TopologicalSpace R]

def pairMap {N : ℕ} (J' : Matrix (Fin N) (Fin N) E) (h : HA R σ J') :
    Matrix (Fin N) (Fin N) (R ⊗[F] E) × (Matrix (Fin N) (Fin N) (R ⊗[F] E))ᵐᵒᵖ :=
  Units.embedProduct _ (HA.mat R σ J' h)

/- English proof (translation)
The claim follows from `(Units.isEmbedding_embedProduct).comp (IsEmbedding.subtypeVal (p := fun g => g ∈ HR R σ J'))`.
-/
lemma isEmbedding_pairMap {N : ℕ} (J' : Matrix (Fin N) (Fin N) E) :
    IsEmbedding (pairMap R σ J') :=
  (Units.isEmbedding_embedProduct).comp
    (IsEmbedding.subtypeVal (p := fun g => g ∈ HR R σ J'))

/- English proof (translation)
Rewrite using `[(isEmbedding_pairMap R σ (blockOne s J)).isInducing.continuous_iff]`. Establish `hp` using `(isEmbedding_pairMap R σ J).continuous`. Establish `: pairMap R σ (blockOne s J) ∘ iotaHom R σ J s = fun u => (blockOne 1 (pairMap R σ J u).1, MulOpposite.op (blockOne 1 (MulOpposite.unop (pairMap R σ J u).2)))` using `rfl`. Rewrite using `[this]`. Conclude with `(continuous_blockOne.comp hp.fst).prodMk (MulOpposite.continuous_op.comp (continuous_blockOne.comp (MulOpposite.continuous_unop.comp hp.snd)))`.
-/
lemma continuous_iotaHom : Continuous (iotaHom R σ J s) := by
  rw [(isEmbedding_pairMap R σ (blockOne s J)).isInducing.continuous_iff]
  have hp := (isEmbedding_pairMap R σ J).continuous
  have : pairMap R σ (blockOne s J) ∘ iotaHom R σ J s = fun u =>
      (blockOne 1 (pairMap R σ J u).1,
        MulOpposite.op (blockOne 1 (MulOpposite.unop (pairMap R σ J u).2))) := rfl
  rw [this]
  exact (continuous_blockOne.comp hp.fst).prodMk
    (MulOpposite.continuous_op.comp
      (continuous_blockOne.comp (MulOpposite.continuous_unop.comp hp.snd)))

/- English proof (translation)
Establish `hp` using `(isEmbedding_pairMap R σ (blockOne s J)).continuous`. Set `P : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E) × (Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E))ᵐᵒᵖ → Matrix (Fin M) (Fin M) (R ⊗[F] E) × (Matrix (Fin M) (Fin M) (R ⊗[F] E))ᵐᵒᵖ` to `fun p => (p.1.submatrix Fin.succ Fin.succ, MulOpposite.op ((MulOpposite.unop p.2).submatrix Fin.succ Fin.succ))`. Establish `hP : Continuous P`. Use `Continuous.prodMk ?_ ?_` and prove the remaining obligations. Conclude with `continuous_fst.matrix_submatrix _ _`.

Conclude with `MulOpposite.continuous_op.comp ((MulOpposite.continuous_unop.comp continuous_snd).matrix_submatrix _ _)`. Use `IsEmbedding.of_comp (continuous_iotaHom R σ J s) (hP.comp hp) ?_` and prove the remaining obligations. Establish `: (P ∘ pairMap R σ (blockOne s J)) ∘ iotaHom R σ J s = pairMap R σ J`. Use function extensionality and compare the values at `u`. Both sides reduce to the same expression.

Rewrite using `[this]`. Conclude with `isEmbedding_pairMap R σ J`.
-/
lemma isEmbedding_iotaHom : IsEmbedding (iotaHom R σ J s) := by
  have hp := (isEmbedding_pairMap R σ (blockOne s J)).continuous
  let P : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E) × (Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E))ᵐᵒᵖ →
      Matrix (Fin M) (Fin M) (R ⊗[F] E) × (Matrix (Fin M) (Fin M) (R ⊗[F] E))ᵐᵒᵖ :=
    fun p => (p.1.submatrix Fin.succ Fin.succ,
      MulOpposite.op ((MulOpposite.unop p.2).submatrix Fin.succ Fin.succ))
  have hP : Continuous P := by
    refine Continuous.prodMk ?_ ?_
    · exact continuous_fst.matrix_submatrix _ _
    · exact MulOpposite.continuous_op.comp
        ((MulOpposite.continuous_unop.comp continuous_snd).matrix_submatrix _ _)
  refine IsEmbedding.of_comp (continuous_iotaHom R σ J s) (hP.comp hp) ?_
  have : (P ∘ pairMap R σ (blockOne s J)) ∘ iotaHom R σ J s = pairMap R σ J := by
    funext u
    rfl
  rw [this]
  exact isEmbedding_pairMap R σ J

/- English proof (translation)
Establish `hp` using `(isEmbedding_pairMap R σ (blockOne s J)).continuous`. Establish `e : Set.range (iotaHom R σ J s) = {h | (pairMap R σ (blockOne s J) h).1 0 0 = 1} ∩ ⋂ i : Fin M, {h | (pairMap R σ (blockOne s J) h).1 i.succ 0 = 0}`. Use extensionality with `h`. Use `mem_range_iff R σ J s hs h` as an intermediate fact. Simplify using `only [MonoidHom.mem_range] at this`.

Simplify using `only [Set.mem_range, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]`. Conclude with `this`. Rewrite using `[e]`. Use `IsClosed.inter (isClosed_eq (hp.fst.matrix_elem 0 0) continuous_const) ?_` and prove the remaining obligations. Conclude with `isClosed_iInter fun i => isClosed_eq (hp.fst.matrix_elem i.succ 0) continuous_const`.
-/
lemma isClosed_range_iotaHom [T2Space (R ⊗[F] E)] (hs : s ≠ 0) :
    IsClosed (Set.range (iotaHom R σ J s)) := by
  have hp := (isEmbedding_pairMap R σ (blockOne s J)).continuous
  have e : Set.range (iotaHom R σ J s) =
      {h | (pairMap R σ (blockOne s J) h).1 0 0 = 1} ∩
        ⋂ i : Fin M, {h | (pairMap R σ (blockOne s J) h).1 i.succ 0 = 0} := by
    ext h
    have := mem_range_iff R σ J s hs h
    simp only [MonoidHom.mem_range] at this
    simp only [Set.mem_range, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    exact this
  rw [e]
  refine IsClosed.inter (isClosed_eq (hp.fst.matrix_elem 0 0) continuous_const) ?_
  exact isClosed_iInter fun i => isClosed_eq (hp.fst.matrix_elem i.succ 0) continuous_const

end Top

end Grp

/- English proof (translation)
Use `haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩`. Set `b` to `Algebra.TensorProduct.basis R (Module.finBasis F E)`. Establish `hc : Continuous b.equivFun.toLinearMap` using `IsModuleTopology.continuous_of_linearMap _`. Conclude with `T2Space.of_injective_continuous b.equivFun.injective hc`.
-/
lemma t2_tensor_product {F E : Type} [Field F] [Field E] [Algebra F E] [Module.Finite F E] (R : Type)
    [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    T2Space (R ⊗[F] E) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  let b := Algebra.TensorProduct.basis R (Module.finBasis F E)
  have hc : Continuous b.equivFun.toLinearMap :=
    IsModuleTopology.continuous_of_linearMap _
  exact T2Space.of_injective_continuous b.equivFun.injective hc

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J _ t ht R _ _ _ _ _`. Establish `hs : algebraMap F E t ≠ 0`. Simplify using `using ht`. Use `haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)`. Use `haveI : T2Space (R ⊗[F] E) := t2_tensor_product R`.

Use `⟨iotaHom R σ J (algebraMap F E t), ?_, fun _ => rfl, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `⟨isEmbedding_iotaHom R σ J _, isClosed_range_iotaHom R σ J _ hs⟩`. Introduce `h`. Rewrite using `[mem_range_iff R σ J _ hs h]`. Conclude with `(act_first_iff R σ J _ (n := 0) h).symm`.

Conclude with `fun u => mem_HFin_iff R σ J _ hs u`. Conclude with `fun u n X => act_iota R σ J _ u X`.
-/
theorem stab_first :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (t : F), t ≠ 0 → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R], ∃ ι : HA R σ J →* HA R σ (blockOne (algebraMap F E t) J), IsClosedEmbedding ι ∧ (∀ u, (HA.mat R σ _ (ι u) : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) = blockOne 1 (HA.mat R σ J u : Matrix (Fin M) (Fin M) (R ⊗[F] E))) ∧ (∀ h, h ∈ ι.range ↔ actW R σ _ h (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) = (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) ∧ (∀ u, HA.mat R σ _ (ι u) ∈ HFin R σ (blockOne (algebraMap F E t) J) ↔ HA.mat R σ J u ∈ HFin R σ J) ∧ ∀ (u : HA R σ J) (n : ℕ) (X : Fin n → Fin M → R ⊗[F] E), actW R σ _ (ι u) (consTup X) = consTup (actW R σ J u X) := by
  intro F E _ _ _ _ _ σ hCM M J _ t ht R _ _ _ _ _
  have hs : algebraMap F E t ≠ 0 := by
    simpa using ht
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  haveI : T2Space (R ⊗[F] E) := t2_tensor_product R
  refine ⟨iotaHom R σ J (algebraMap F E t), ?_, fun _ => rfl, ?_, ?_, ?_⟩
  · exact ⟨isEmbedding_iotaHom R σ J _, isClosed_range_iotaHom R σ J _ hs⟩
  · intro h
    rw [mem_range_iff R σ J _ hs h]
    exact (act_first_iff R σ J _ (n := 0) h).symm
  · exact fun u => mem_HFin_iff R σ J _ hs u
  · exact fun u n X => act_iota R σ J _ u X

end GlobalTheory.CompanionTheory.SW.StabFirst
