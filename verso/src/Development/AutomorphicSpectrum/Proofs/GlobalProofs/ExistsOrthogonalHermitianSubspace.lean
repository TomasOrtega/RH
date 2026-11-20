import Mathlib
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Formalism.FormalDegreeBessel.StatementG
open Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.JStable

open Module in

/- English proof (translation)
Set `v : Set (EuclideanSpace ℂ ι)` to `Set.range (fun i => ((stdOrthonormalBasis ℂ W i : W) : EuclideanSpace ℂ ι))`. Apply the tactic sequence `have hon : Orthonormal ℂ (fun i => ((stdOrthonormalBasis ℂ W i : W) : EuclideanSpace ℂ ι)) := (stdOrthonormalBasis ℂ W).orthonormal.comp_linearIsometry W.subtypeₗᵢ`. Establish `hv : Orthonormal ℂ ((↑) : v → EuclideanSpace ℂ ι)` using `(orthonormal_subtype_range hon.linearIndependent.injective).2 hon`. Take `⟨u, bu, hvu, hbu⟩` from `hv.exists_orthonormalBasis_extension`. Establish `hcard : Fintype.card u = Fintype.card ι` using `(finrank_eq_card_basis bu.toBasis).symm.trans finrank_euclideanSpace`.

Set `e : u ≃ ι` to `Fintype.equivOfCardEq hcard`. Use `⟨bu.reindex e, e '' {x | (x : EuclideanSpace ℂ ι) ∈ v}, ?_⟩` and prove the remaining obligations. Establish `himg : (bu.reindex e) '' (e '' {x | (x : EuclideanSpace ℂ ι) ∈ v}) = v`. Rewrite using `[Set.image_image]`. Use extensionality with `y`.

Simplify using `only [OrthonormalBasis.reindex_apply, Equiv.symm_apply_apply, hbu, Set.mem_image, Set.mem_ofPred_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `hx`. Introduce `hy`.

Conclude with `⟨⟨y, hvu hy⟩, hy, rfl⟩`. Rewrite using `[himg]`. Establish `hr : W.subtype '' Set.range (stdOrthonormalBasis ℂ W) = v` using `(Set.range_comp _ _).symm`. Rewrite using `[← hr, Submodule.span_image, ← (stdOrthonormalBasis ℂ W).coe_toBasis, (stdOrthonormalBasis ℂ W).toBasis.span_eq, Submodule.map_subtype_top]`.
-/
theorem exists_adapted_onb {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Submodule ℂ (EuclideanSpace ℂ ι)) :
    ∃ (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι)) (T : Set ι),
      W = Submodule.span ℂ (b '' T) := by
  classical
  let v : Set (EuclideanSpace ℂ ι) := Set.range (fun i => ((stdOrthonormalBasis ℂ W i : W) : EuclideanSpace ℂ ι))
  have hon : Orthonormal ℂ (fun i => ((stdOrthonormalBasis ℂ W i : W) : EuclideanSpace ℂ ι)) :=
    (stdOrthonormalBasis ℂ W).orthonormal.comp_linearIsometry W.subtypeₗᵢ
  have hv : Orthonormal ℂ ((↑) : v → EuclideanSpace ℂ ι) :=
    (orthonormal_subtype_range hon.linearIndependent.injective).2 hon
  obtain ⟨u, bu, hvu, hbu⟩ := hv.exists_orthonormalBasis_extension
  have hcard : Fintype.card u = Fintype.card ι :=
    (finrank_eq_card_basis bu.toBasis).symm.trans finrank_euclideanSpace
  let e : u ≃ ι := Fintype.equivOfCardEq hcard
  refine ⟨bu.reindex e, e '' {x | (x : EuclideanSpace ℂ ι) ∈ v}, ?_⟩
  have himg : (bu.reindex e) '' (e '' {x | (x : EuclideanSpace ℂ ι) ∈ v}) = v := by
    rw [Set.image_image]
    ext y
    simp only [OrthonormalBasis.reindex_apply, Equiv.symm_apply_apply, hbu, Set.mem_image,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨⟨y, hvu hy⟩, hy, rfl⟩
  rw [himg]
  have hr : W.subtype '' Set.range (stdOrthonormalBasis ℂ W) = v := (Set.range_comp _ _).symm
  rw [← hr, Submodule.span_image, ← (stdOrthonormalBasis ℂ W).coe_toBasis,
    (stdOrthonormalBasis ℂ W).toBasis.span_eq, Submodule.map_subtype_top]

variable {n : ℕ} (ε : Fin n → Bool)

def ext0 (s : Bool) : EuclideanSpace ℂ {i : Fin n // ε i = s} →ₗ[ℂ] (Fin n → ℂ) where
  toFun x a := if h : ε a = s then x ⟨a, h⟩ else 0
  map_add' x y := by
    funext a
    by_cases h : ε a = s <;> simp [h]
  map_smul' c x := by
    funext a
    by_cases h : ε a = s <;> simp [h]

def res0 (s : Bool) (v : Fin n → ℂ) : EuclideanSpace ℂ {i : Fin n // ε i = s} :=
  WithLp.toLp 2 fun i => v i

/- English proof (translation)
Simplify using `only [ext0, LinearMap.coe_mk, AddHom.coe_mk, dif_neg h]`.
-/
lemma extendByZero_apply_of_ne {s : Bool} (x : EuclideanSpace ℂ {i : Fin n // ε i = s}) {a : Fin n}
    (h : ε a ≠ s) : ext0 ε s x a = 0 := by
  simp only [ext0, LinearMap.coe_mk, AddHom.coe_mk, dif_neg h]

/- English proof (translation)
Use function extensionality and compare the values at `a`. Establish `hJ : (Formalism.REAL.Jm ε *ᵥ v) a = (if ε a then 1 else -1) * v a`. Simplify using `[Formalism.REAL.Jm, Matrix.mulVec_diagonal]`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hJ, ext0, LinearMap.coe_mk, AddHom.coe_mk, res0]`. Apply the tactic sequence `cases s <;> cases h : ε a <;> simp <;> ring`.
-/
lemma extendByZero_restrict_eigen_projection (s : Bool) (v : Fin n → ℂ) :
    ext0 ε s (res0 ε s v) =
      (1 / 2 : ℂ) • (v + (if s then (1 : ℂ) else -1) • (Formalism.REAL.Jm ε *ᵥ v)) := by
  funext a
  have hJ : (Formalism.REAL.Jm ε *ᵥ v) a = (if ε a then 1 else -1) * v a := by
    simp [Formalism.REAL.Jm, Matrix.mulVec_diagonal]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hJ, ext0, LinearMap.coe_mk, AddHom.coe_mk, res0]
  cases s <;> cases h : ε a <;> simp <;> ring

/- English proof (translation)
Use function extensionality and compare the values at `a`. Simplify using `only [Pi.add_apply, ext0, LinearMap.coe_mk, AddHom.coe_mk, res0]`. Apply the tactic sequence `cases h : ε a <;> simp`.
-/
lemma eq_extendByZero_restrict_sum (v : Fin n → ℂ) :
    v = ext0 ε true (res0 ε true v) + ext0 ε false (res0 ε false v) := by
  funext a
  simp only [Pi.add_apply, ext0, LinearMap.coe_mk, AddHom.coe_mk, res0]
  cases h : ε a <;> simp

/- English proof (translation)
Rewrite using `[← Fintype.sum_subtype_add_sum_subtype (fun a => ε a = s) (fun a => star (ext0 ε s x a) * ext0 ε s y a)]`. Establish `h2 : ∑ a : {a // ¬ ε a = s}, star (ext0 ε s x a) * ext0 ε s y a = 0` using `Finset.sum_eq_zero (fun a _ => by rw [extendByZero_apply_of_ne ε x a.2, star_zero, zero_mul])`. Rewrite using `[h2, add_zero, PiLp.inner_apply]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Establish `hx : ∀ z : EuclideanSpace ℂ {i : Fin n // ε i = s}, ext0 ε s z i.1 = z i`.

Introduce `z`. Simplify using `only [ext0, LinearMap.coe_mk, AddHom.coe_mk, dif_pos i.2]`. Rewrite using `[hx x, hx y]`. Simplify using `[mul_comm]`.
-/
lemma sum_extendByZero_fin_eq_sum_of_eq (s : Bool) (x y : EuclideanSpace ℂ {i : Fin n // ε i = s}) :
    ∑ a, star (ext0 ε s x a) * ext0 ε s y a = inner ℂ x y := by
  classical
  rw [← Fintype.sum_subtype_add_sum_subtype (fun a => ε a = s)
    (fun a => star (ext0 ε s x a) * ext0 ε s y a)]
  have h2 : ∑ a : {a // ¬ ε a = s}, star (ext0 ε s x a) * ext0 ε s y a = 0 :=
    Finset.sum_eq_zero (fun a _ => by rw [extendByZero_apply_of_ne ε x a.2, star_zero, zero_mul])
  rw [h2, add_zero, PiLp.inner_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hx : ∀ z : EuclideanSpace ℂ {i : Fin n // ε i = s}, ext0 ε s z i.1 = z i := by
    intro z
    simp only [ext0, LinearMap.coe_mk, AddHom.coe_mk, dif_pos i.2]
  rw [hx x, hx y]
  simp [mul_comm]

/- English proof (translation)
Use `choose b T hT using fun s : Bool => exists_adapted_onb (W.comap (ext0 ε s))`. Establish `hres : ∀ (s : Bool) (v : Fin n → ℂ), v ∈ W → res0 ε s v ∈ W.comap (ext0 ε s)`. Introduce `s v hv`. Rewrite using `[Submodule.mem_comap, extendByZero_restrict_eigen_projection]`. Conclude with `W.smul_mem _ (W.add_mem hv (W.smul_mem _ (hW v hv)))`.

Establish `hdecomp : W = (W.comap (ext0 ε true)).map (ext0 ε true) ⊔ (W.comap (ext0 ε false)).map (ext0 ε false)`. Use `le_antisymm (fun v hv => ?_) (sup_le (Submodule.map_le_iff_le_comap.2 le_rfl) (Submodule.map_le_iff_le_comap.2 le_rfl))` and prove the remaining obligations. Rewrite using `[eq_extendByZero_restrict_sum ε v]`. Conclude with `Submodule.add_mem_sup (Submodule.mem_map_of_mem (hres true v hv)) (Submodule.mem_map_of_mem (hres false v hv))`. Take `⟨M, hM⟩ : ∃ M : Matrix (Fin n) (Fin n) ℂ, ∀ i j, M i j = ext0 ε (ε j) (b (ε j) ⟨j, rfl⟩) i` from `⟨Matrix.of fun i j => ext0 ε (ε j) (b (ε j) ⟨j, rfl⟩) i, fun _ _ => rfl⟩`.

Establish `hcol : ∀ (s : Bool) (i' : {i : Fin n // ε i = s}) (a : Fin n), M a i'.1 = ext0 ε s (b s i') a`. Introduce and unpack `s ⟨j, rfl⟩ a`. Conclude with `hM a j`. Establish `hMM : Mᴴ * M = 1`. Use extensionality with `j l`.

Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]`. Distinguish the cases in `hjl : ε j = ε l`. Establish `h1 : ∀ a, M a j = ext0 ε (ε j) (b (ε j) ⟨j, rfl⟩) a` using `fun a => hcol (ε j) ⟨j, rfl⟩ a`. Establish `h2 : ∀ a, M a l = ext0 ε (ε j) (b (ε j) ⟨l, hjl.symm⟩) a` using `fun a => hcol (ε j) ⟨l, hjl.symm⟩ a`. Simplify using `only [h1, h2]`.

Rewrite using `[sum_extendByZero_fin_eq_sum_of_eq, orthonormal_iff_ite.1 (b (ε j)).orthonormal]`. Simplify using `only [Subtype.mk.injEq]`. Establish `hne : j ≠ l` using `fun h => hjl (h ▸ rfl)`. Rewrite using `[if_neg hne]`. Use `Finset.sum_eq_zero (fun i _ => ?_)` and prove the remaining obligations.

Distinguish the cases in `hi : ε i = ε j`. Rewrite using `[hM i l, extendByZero_apply_of_ne ε _ (fun h => hjl (hi.symm.trans h)), mul_zero]`. Rewrite using `[hM i j, extendByZero_apply_of_ne ε _ hi, star_zero, zero_mul]`. Establish `hMM' : M * Mᴴ = 1` using `mul_eq_one_comm.1 hMM`. Establish `hJ : M * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * M`.

Establish `hJd : Formalism.REAL.Jm ε = Matrix.diagonal (fun a => if ε a then (1 : ℂ) else -1)` using `rfl`. Use extensionality with `i j`. Rewrite using `[hJd, Matrix.mul_diagonal, Matrix.diagonal_mul]`. Distinguish the cases in `hi : ε i = ε j`. Simplify using `only [hi]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hM i j, extendByZero_apply_of_ne ε _ hi]`. Expand and normalize the polynomial expressions, which then agree. Establish `hunit : M ∈ Matrix.unitaryGroup (Fin n) ℂ`. Rewrite using `[Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]`.

Conclude with `hMM`. Set `u : (Matrix (Fin n) (Fin n) ℂ)ˣ` to `⟨M, Mᴴ, hMM', hMM⟩`. Establish `hUJ : u ∈ Formalism.REAL.UJ ε` using `by show Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε`. Rewrite using `[Matrix.mul_assoc, ← hJ, ← Matrix.mul_assoc, hMM, Matrix.one_mul]`. Set `gu : Formalism.REAL.UJ ε` to `⟨u, hUJ⟩`.

Establish `hK : M ∈ Formalism.REAL.Kset ε` using `⟨hunit, hJ⟩`. Set `k : Formalism.REAL.KG ε` to `⟨gu, (Formalism.REAL.mem_KG ε gu).2 hK⟩`. Set `S : Set (Fin n)` to `{j | (⟨j, rfl⟩ : {i : Fin n // ε i = ε j}) ∈ T (ε j)}`. Use `⟨k, S, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `W = (Submodule.span ℂ (Set.range fun j : S => (Pi.single (j : Fin n) (1 : ℂ) : Fin n → ℂ))).map M.mulVecLin`.

Establish `hMcol : ∀ (s : Bool) (i' : {i : Fin n // ε i = s}), M *ᵥ Pi.single i'.1 1 = ext0 ε s (b s i')`. Introduce `s i'`. Use function extensionality and compare the values at `a`. Rewrite using `[Matrix.mulVec_single_one, Matrix.col_apply, hcol s i' a]`. Establish `hmemS : ∀ (s : Bool) (i' : {i : Fin n // ε i = s}), i' ∈ T s → i'.1 ∈ S`.

Introduce and unpack `s ⟨j, rfl⟩ hi'`. Conclude with `hi'`. Establish `hset : ⇑(ext0 ε true) '' (⇑(b true) '' T true) ∪ ⇑(ext0 ε false) '' (⇑(b false) '' T false) = Set.range (⇑M.mulVecLin ∘ fun j : S => (Pi.single (j : Fin n) (1 : ℂ) : Fin n → ℂ))`. Use extensionality with `x`. Simplify using `only [Set.mem_union, Set.mem_image, Set.mem_range, Function.comp_apply, Matrix.mulVecLin_apply]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `(⟨y, ⟨i', hi', rfl⟩, rfl⟩ | ⟨y, ⟨i', hi', rfl⟩, rfl⟩)`. Conclude with `⟨⟨i'.1, hmemS true i' hi'⟩, hMcol true i'⟩`. Conclude with `⟨⟨i'.1, hmemS false i' hi'⟩, hMcol false i'⟩`. Introduce and unpack `⟨⟨j, hj⟩, rfl⟩`.

Establish `htr : ∀ (s : Bool) (h : ε j = s), (⟨j, h⟩ : {i : Fin n // ε i = s}) ∈ T s`. Introduce and unpack `s rfl`. Conclude with `hj`. Establish `hback : ∀ (s : Bool) (i' : {i : Fin n // ε i = s}), i' ∈ T s → ∃ y, (∃ a ∈ T s, b s a = y) ∧ ext0 ε s y = M *ᵥ Pi.single i'.1 1` using `fun s i' hi' => ⟨b s i', ⟨i', hi', rfl⟩, (hMcol s i').symm⟩`. Break down `Bool.eq_false_or_eq_true (ε j) with h | h` into its components or cases.

Conclude with `Or.inl (hback _ ⟨j, h⟩ (htr _ h))`. Conclude with `Or.inr (hback _ ⟨j, h⟩ (htr _ h))`. Use `conv_lhs => rw [hdecomp, hT true, hT false]`. Rewrite using `[Submodule.map_span, Submodule.map_span, Submodule.map_span, ← Submodule.span_union, hset, Set.range_comp]`.
-/
theorem exists_KG_coordinate (W : Submodule ℂ (Fin n → ℂ))
    (hW : ∀ v ∈ W, Formalism.REAL.Jm ε *ᵥ v ∈ W) :
    ∃ (k : Formalism.REAL.KG ε) (S : Set (Fin n)),
      W = (Submodule.span ℂ (Set.range fun j : S => (Pi.single (j : Fin n) (1 : ℂ) : Fin n → ℂ))).map
        (Formalism.REAL.toMK k).mulVecLin := by
  classical
  choose b T hT using fun s : Bool => exists_adapted_onb (W.comap (ext0 ε s))
  have hres : ∀ (s : Bool) (v : Fin n → ℂ), v ∈ W → res0 ε s v ∈ W.comap (ext0 ε s) := by
    intro s v hv
    rw [Submodule.mem_comap, extendByZero_restrict_eigen_projection]
    exact W.smul_mem _ (W.add_mem hv (W.smul_mem _ (hW v hv)))
  have hdecomp : W = (W.comap (ext0 ε true)).map (ext0 ε true) ⊔
      (W.comap (ext0 ε false)).map (ext0 ε false) := by
    refine le_antisymm (fun v hv => ?_) (sup_le (Submodule.map_le_iff_le_comap.2 le_rfl)
      (Submodule.map_le_iff_le_comap.2 le_rfl))
    rw [eq_extendByZero_restrict_sum ε v]
    exact Submodule.add_mem_sup (Submodule.mem_map_of_mem (hres true v hv))
      (Submodule.mem_map_of_mem (hres false v hv))
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin n) (Fin n) ℂ,
      ∀ i j, M i j = ext0 ε (ε j) (b (ε j) ⟨j, rfl⟩) i :=
    ⟨Matrix.of fun i j => ext0 ε (ε j) (b (ε j) ⟨j, rfl⟩) i, fun _ _ => rfl⟩
  have hcol : ∀ (s : Bool) (i' : {i : Fin n // ε i = s}) (a : Fin n),
      M a i'.1 = ext0 ε s (b s i') a := by
    rintro s ⟨j, rfl⟩ a
    exact hM a j
  have hMM : Mᴴ * M = 1 := by
    ext j l
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
    by_cases hjl : ε j = ε l
    · have h1 : ∀ a, M a j = ext0 ε (ε j) (b (ε j) ⟨j, rfl⟩) a := fun a => hcol (ε j) ⟨j, rfl⟩ a
      have h2 : ∀ a, M a l = ext0 ε (ε j) (b (ε j) ⟨l, hjl.symm⟩) a :=
        fun a => hcol (ε j) ⟨l, hjl.symm⟩ a
      simp only [h1, h2]
      rw [sum_extendByZero_fin_eq_sum_of_eq, orthonormal_iff_ite.1 (b (ε j)).orthonormal]
      simp only [Subtype.mk.injEq]
    · have hne : j ≠ l := fun h => hjl (h ▸ rfl)
      rw [if_neg hne]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      by_cases hi : ε i = ε j
      · rw [hM i l, extendByZero_apply_of_ne ε _ (fun h => hjl (hi.symm.trans h)), mul_zero]
      · rw [hM i j, extendByZero_apply_of_ne ε _ hi, star_zero, zero_mul]
  have hMM' : M * Mᴴ = 1 := mul_eq_one_comm.1 hMM
  have hJ : M * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * M := by
    have hJd : Formalism.REAL.Jm ε = Matrix.diagonal (fun a => if ε a then (1 : ℂ) else -1) := rfl
    ext i j
    rw [hJd, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hi : ε i = ε j
    · simp only [hi]
      ring
    · rw [hM i j, extendByZero_apply_of_ne ε _ hi]
      ring
  have hunit : M ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    exact hMM
  let u : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨M, Mᴴ, hMM', hMM⟩
  have hUJ : u ∈ Formalism.REAL.UJ ε := by
    show Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε
    rw [Matrix.mul_assoc, ← hJ, ← Matrix.mul_assoc, hMM, Matrix.one_mul]
  let gu : Formalism.REAL.UJ ε := ⟨u, hUJ⟩
  have hK : M ∈ Formalism.REAL.Kset ε := ⟨hunit, hJ⟩
  let k : Formalism.REAL.KG ε := ⟨gu, (Formalism.REAL.mem_KG ε gu).2 hK⟩
  let S : Set (Fin n) := {j | (⟨j, rfl⟩ : {i : Fin n // ε i = ε j}) ∈ T (ε j)}
  refine ⟨k, S, ?_⟩
  change W = (Submodule.span ℂ (Set.range fun j : S => (Pi.single (j : Fin n) (1 : ℂ) : Fin n → ℂ))).map
    M.mulVecLin
  have hMcol : ∀ (s : Bool) (i' : {i : Fin n // ε i = s}),
      M *ᵥ Pi.single i'.1 1 = ext0 ε s (b s i') := by
    intro s i'
    funext a
    rw [Matrix.mulVec_single_one, Matrix.col_apply, hcol s i' a]
  have hmemS : ∀ (s : Bool) (i' : {i : Fin n // ε i = s}), i' ∈ T s → i'.1 ∈ S := by
    rintro s ⟨j, rfl⟩ hi'
    exact hi'
  have hset : ⇑(ext0 ε true) '' (⇑(b true) '' T true) ∪ ⇑(ext0 ε false) '' (⇑(b false) '' T false) =
      Set.range (⇑M.mulVecLin ∘ fun j : S => (Pi.single (j : Fin n) (1 : ℂ) : Fin n → ℂ)) := by
    ext x
    simp only [Set.mem_union, Set.mem_image, Set.mem_range, Function.comp_apply,
      Matrix.mulVecLin_apply]
    constructor
    · rintro (⟨y, ⟨i', hi', rfl⟩, rfl⟩ | ⟨y, ⟨i', hi', rfl⟩, rfl⟩)
      · exact ⟨⟨i'.1, hmemS true i' hi'⟩, hMcol true i'⟩
      · exact ⟨⟨i'.1, hmemS false i' hi'⟩, hMcol false i'⟩
    · rintro ⟨⟨j, hj⟩, rfl⟩
      have htr : ∀ (s : Bool) (h : ε j = s), (⟨j, h⟩ : {i : Fin n // ε i = s}) ∈ T s := by
        rintro s rfl
        exact hj
      have hback : ∀ (s : Bool) (i' : {i : Fin n // ε i = s}), i' ∈ T s →
          ∃ y, (∃ a ∈ T s, b s a = y) ∧ ext0 ε s y = M *ᵥ Pi.single i'.1 1 :=
        fun s i' hi' => ⟨b s i', ⟨i', hi', rfl⟩, (hMcol s i').symm⟩
      rcases Bool.eq_false_or_eq_true (ε j) with h | h
      · exact Or.inl (hback _ ⟨j, h⟩ (htr _ h))
      · exact Or.inr (hback _ ⟨j, h⟩ (htr _ h))
  conv_lhs => rw [hdecomp, hT true, hT false]
  rw [Submodule.map_span, Submodule.map_span, Submodule.map_span, ← Submodule.span_union, hset,
    Set.range_comp]

end GlobalTheory.CompanionTheory.JStable
