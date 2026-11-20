import Formalism.HarderNarasimhan.StatementPl
import Formalism.HarderNarasimhan.DefsPl
import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PlaceSplit
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.GramBlock

open Module NumberField

noncomputable section

namespace Formalism.HN

section HtImageAux

/- English proof (translation)
Simplify using `[placePart, Submodule.mem_iInf]`.
-/
theorem mem_place_part_iff {P ι : Type*} [Fintype P] [Fintype ι] {v : P}
    {x : EuclideanSpace ℝ (P × ι × Fin 2)} :
    x ∈ placePart v ↔ ∀ p : P × ι × Fin 2, p.1 ≠ v → x p = 0 := by
  simp [placePart, Submodule.mem_iInf]

/- English proof (translation)
Rewrite `hx`, `hy` using `[mem_place_part_iff]`. Rewrite using `[PiLp.inner_apply]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `p _`. Distinguish the cases in `hp : p.1 = v`.

Rewrite using `[hy p (by rw [hp]; exact h)]`. Simplify using the standard rewrite rules. Rewrite using `[hx p hp]`. Simplify using the standard rewrite rules.
-/
theorem place_part_orthogonal {P ι : Type*} [Fintype P] [Fintype ι] {v w : P} (h : v ≠ w)
    (x : EuclideanSpace ℝ (P × ι × Fin 2)) (hx : x ∈ placePart v)
    (y : EuclideanSpace ℝ (P × ι × Fin 2)) (hy : y ∈ placePart w) : inner ℝ x y = 0 := by
  rw [mem_place_part_iff] at hx hy
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro p _
  by_cases hp : p.1 = v
  · rw [hy p (by rw [hp]; exact h)]
    simp
  · rw [hx p hp]
    simp

/- English proof (translation)
Proceed by induction on `hx using Submodule.iSup_induction' with`. Consider the case `mem i y hy`. Use `⟨Pi.single i y, fun v => ?_, by simp⟩` and prove the remaining obligations. Distinguish the cases in `h : v = i`. Substitute `h` using the available equality.

Simplify using `using hy`. Simplify using `[h]`. Consider the case `zero => exact ⟨0, fun v => zero_mem _, by simp⟩`. Consider the case `add y z _ _ ihy ihz`. Take `⟨f, hf, rfl⟩` from `ihy`.

Take `⟨g, hg, rfl⟩` from `ihz`. Conclude with `⟨f + g, fun v => add_mem (hf v) (hg v), by simp [Finset.sum_add_distrib]⟩`.
-/
theorem exists_decomp_of_mem_iSup {P E : Type*} [Fintype P] [AddCommGroup E] [Module ℝ E]
    (p : P → Submodule ℝ E) {x : E} (hx : x ∈ ⨆ v, p v) :
    ∃ f : P → E, (∀ v, f v ∈ p v) ∧ ∑ v, f v = x := by
  classical
  induction hx using Submodule.iSup_induction' with
  | mem i y hy =>
    refine ⟨Pi.single i y, fun v => ?_, by simp⟩
    by_cases h : v = i
    · subst h
      simpa using hy
    · simp [h]
  | zero => exact ⟨0, fun v => zero_mem _, by simp⟩
  | add y z _ _ ihy ihz =>
    obtain ⟨f, hf, rfl⟩ := ihy
    obtain ⟨g, hg, rfl⟩ := ihz
    exact ⟨f + g, fun v => add_mem (hf v) (hg v), by simp [Finset.sum_add_distrib]⟩

/- English proof (translation)
Introduce `t ht`. Rewrite `ht` using `[hT]`. Take `⟨f, hf, rfl⟩` from `exists_decomp_of_mem_iSup (fun w => T ⊓ Ev w) ht`. Rewrite using `[sum_inner]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `w _`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Conclude with `hx _ (hf w)`. Conclude with `hEv w v hw _ (hf w).2 x hxv`.
-/
theorem inner_zero_of_orthogonal_parts {P E : Type*} [Fintype P] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (Ev : P → Submodule ℝ E) (hEv : ∀ v w, v ≠ w → ∀ x ∈ Ev v, ∀ y ∈ Ev w, inner ℝ x y = 0)
    (T : Submodule ℝ E) (hT : T = ⨆ v, T ⊓ Ev v) {v : P} {x : E} (hxv : x ∈ Ev v)
    (hx : ∀ t ∈ T ⊓ Ev v, inner ℝ t x = 0) : ∀ t ∈ T, inner ℝ t x = 0 := by
  intro t ht
  rw [hT] at ht
  obtain ⟨f, hf, rfl⟩ := exists_decomp_of_mem_iSup (fun w => T ⊓ Ev w) ht
  rw [sum_inner]
  apply Finset.sum_eq_zero
  intro w _
  by_cases hw : w = v
  · subst hw
    exact hx _ (hf w)
  · exact hEv w v hw _ (hf w).2 x hxv

/- English proof (translation)
Establish `key : ∀ v, S ⊓ Tᗮ ⊓ Ev v = S ⊓ Ev v ⊓ (T ⊓ Ev v)ᗮ`. Introduce `v`. Use extensionality with `x`. Simplify using `only [Submodule.mem_inf]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨hxS, hxT⟩, hxv⟩`. Use `⟨⟨hxS, hxv⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.mem_orthogonal]`. Introduce `u hu`. Conclude with `(Submodule.mem_orthogonal T x).1 hxT u hu.1`.

Introduce and unpack `⟨⟨hxS, hxv⟩, hx⟩`. Use `⟨⟨hxS, ?_⟩, hxv⟩` and prove the remaining obligations. Rewrite using `[Submodule.mem_orthogonal]`. Conclude with `inner_zero_of_orthogonal_parts Ev hEv T hT hxv (fun t ht => (Submodule.mem_orthogonal _ x).1 hx t ht)`. Use `⟨?_, fun v => ?_⟩` and prove the remaining obligations.

Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Take `⟨hxS, hxT⟩` from `Submodule.mem_inf.1 hx`. Rewrite `hxS` using `[hS]`. Take `⟨f, hf, rfl⟩` from `exists_decomp_of_mem_iSup (fun w => S ⊓ Ev w) hxS`.

Use `Submodule.sum_mem _ fun w _ => Submodule.mem_iSup_of_mem w ?_` and prove the remaining obligations. Rewrite using `[key w]`. Use `Submodule.mem_inf.2 ⟨hf w, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.mem_orthogonal]`. Introduce `t ht`.

Establish `h0 : inner ℝ t (∑ u, f u) = 0` using `(Submodule.mem_orthogonal T _).1 hxT t ht.1`. Rewrite `h0` using `[inner_sum, Finset.sum_eq_single w]`. Conclude with `h0`. Introduce `u _ hu`. Conclude with `hEv w u (Ne.symm hu) t ht.2 (f u) (hf u).2`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ w) h`. Conclude with `iSup_le fun w => inf_le_left`. Establish `h` using `Submodule.finrank_add_inf_finrank_orthogonal (inf_le_inf_right (Ev v) hTS)`. Rewrite using `[key v, inf_comm (S ⊓ Ev v)]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem orthogonal_complement_place_split {P E : Type*} [Fintype P] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Ev : P → Submodule ℝ E) (hEv : ∀ v w, v ≠ w → ∀ x ∈ Ev v, ∀ y ∈ Ev w, inner ℝ x y = 0)
    (S T : Submodule ℝ E) (hS : S = ⨆ v, S ⊓ Ev v) (hT : T = ⨆ v, T ⊓ Ev v) (hTS : T ≤ S) :
    S ⊓ Tᗮ = (⨆ v, S ⊓ Tᗮ ⊓ Ev v) ∧
    ∀ v, finrank ℝ (S ⊓ Tᗮ ⊓ Ev v : Submodule ℝ E) + finrank ℝ (T ⊓ Ev v : Submodule ℝ E) =
      finrank ℝ (S ⊓ Ev v : Submodule ℝ E) := by
  classical
  have key : ∀ v, S ⊓ Tᗮ ⊓ Ev v = S ⊓ Ev v ⊓ (T ⊓ Ev v)ᗮ := by
    intro v
    ext x
    simp only [Submodule.mem_inf]
    constructor
    · rintro ⟨⟨hxS, hxT⟩, hxv⟩
      refine ⟨⟨hxS, hxv⟩, ?_⟩
      rw [Submodule.mem_orthogonal]
      intro u hu
      exact (Submodule.mem_orthogonal T x).1 hxT u hu.1
    · rintro ⟨⟨hxS, hxv⟩, hx⟩
      refine ⟨⟨hxS, ?_⟩, hxv⟩
      rw [Submodule.mem_orthogonal]
      exact inner_zero_of_orthogonal_parts Ev hEv T hT hxv
        (fun t ht => (Submodule.mem_orthogonal _ x).1 hx t ht)
  refine ⟨?_, fun v => ?_⟩
  · apply le_antisymm
    · intro x hx
      obtain ⟨hxS, hxT⟩ := Submodule.mem_inf.1 hx
      rw [hS] at hxS
      obtain ⟨f, hf, rfl⟩ := exists_decomp_of_mem_iSup (fun w => S ⊓ Ev w) hxS
      refine Submodule.sum_mem _ fun w _ => Submodule.mem_iSup_of_mem w ?_
      rw [key w]
      refine Submodule.mem_inf.2 ⟨hf w, ?_⟩
      rw [Submodule.mem_orthogonal]
      intro t ht
      have h0 : inner ℝ t (∑ u, f u) = 0 := (Submodule.mem_orthogonal T _).1 hxT t ht.1
      rw [inner_sum, Finset.sum_eq_single w] at h0
      · exact h0
      · intro u _ hu
        exact hEv w u (Ne.symm hu) t ht.2 (f u) (hf u).2
      · intro h
        exact absurd (Finset.mem_univ w) h
    · exact iSup_le fun w => inf_le_left
  · have h := Submodule.finrank_add_inf_finrank_orthogonal (inf_le_inf_right (Ev v) hTS)
    rw [key v, inf_comm (S ⊓ Ev v)]
    omega

/- English proof (translation)
Use `set K := Submodule.span ℝ (N : Set E) with hK`. Establish `hKU : K ≤ Submodule.span ℝ (L : Set E)` using `Submodule.span_mono (by exact_mod_cast h)`. Establish `hcoe : (Formalism.F.quot L N : Set E) = (Kᗮ.starProjection : E →ₗ[ℝ] E) '' (L : Set E)`. Simplify using `only [Formalism.F.quot, Submodule.map_coe]`. Both sides reduce to the same expression.

Rewrite using `[hcoe, Submodule.span_image]`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Simplify using `only [ContinuousLinearMap.coe_coe]`. Use `Submodule.mem_inf.2 ⟨?_, ?_⟩` and prove the remaining obligations.

Establish `h1 : x - Kᗮ.starProjection x ∈ K`. Establish `h3` using `Kᗮ.sub_starProjection_mem_orthogonal x`. Rewrite `h3` using `[Submodule.orthogonal_orthogonal]`. Then use the resulting hypothesis. Establish `h2 : Kᗮ.starProjection x = x - (x - Kᗮ.starProjection x)` using `by abel`. Rewrite using `[h2]`.

Conclude with `Submodule.sub_mem _ hx (hKU h1)`. Conclude with `(Kᗮ.orthogonalProjection x).2`. Introduce `y hy`. Take `⟨hyU, hyK⟩` from `Submodule.mem_inf.1 hy`. Conclude with `⟨y, hyU, Submodule.starProjection_eq_self_iff.2 hyK⟩`.
-/
theorem span_quotient_lattice_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L N : Submodule ℤ E) (h : N ≤ L) :
    Submodule.span ℝ (Formalism.F.quot L N : Set E) =
      Submodule.span ℝ (L : Set E) ⊓ (Submodule.span ℝ (N : Set E))ᗮ := by
  set K := Submodule.span ℝ (N : Set E) with hK
  have hKU : K ≤ Submodule.span ℝ (L : Set E) := Submodule.span_mono (by exact_mod_cast h)
  have hcoe : (Formalism.F.quot L N : Set E) =
      (Kᗮ.starProjection : E →ₗ[ℝ] E) '' (L : Set E) := by
    simp only [Formalism.F.quot, Submodule.map_coe]
    rfl
  rw [hcoe, Submodule.span_image]
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    simp only [ContinuousLinearMap.coe_coe]
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · have h1 : x - Kᗮ.starProjection x ∈ K := by
        have h3 := Kᗮ.sub_starProjection_mem_orthogonal x
        rwa [Submodule.orthogonal_orthogonal] at h3
      have h2 : Kᗮ.starProjection x = x - (x - Kᗮ.starProjection x) := by abel
      rw [h2]
      exact Submodule.sub_mem _ hx (hKU h1)
    · exact (Kᗮ.orthogonalProjection x).2
  · intro y hy
    obtain ⟨hyU, hyK⟩ := Submodule.mem_inf.1 hy
    exact ⟨y, hyU, Submodule.starProjection_eq_self_iff.2 hyK⟩

end HtImageAux

section HtImageReal

def htImageCv {P ι : Type*} [Fintype P] [Fintype ι] (y : EuclideanSpace ℝ (P × ι × Fin 2))
    (v : P) : ι → ℂ :=
  fun i => ⟨y (v, i, 0), y (v, i, 1)⟩

def htImageMap {P ι κ : Type*} [Fintype P] [Fintype ι] [Fintype κ] (M : P → Matrix κ ι ℂ) :
    EuclideanSpace ℝ (P × ι × Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (P × κ × Fin 2) where
  toFun y := WithLp.toLp 2 (fun p => if p.2.2 = 0 then ((M p.1).mulVec (htImageCv y p.1) p.2.1).re
      else ((M p.1).mulVec (htImageCv y p.1) p.2.1).im)
  map_add' y z := by
    have h : ∀ v, htImageCv (y + z) v = htImageCv y v + htImageCv z v := by
      intro v; funext i; apply Complex.ext <;> simp [htImageCv]
    ext p
    simp only [h, Matrix.mulVec_add, PiLp.add_apply]
    split_ifs <;> simp
  map_smul' r y := by
    have h : ∀ v, htImageCv (r • y) v = r • htImageCv y v := by
      intro v; funext i; apply Complex.ext <;> simp [htImageCv]
    ext p
    simp only [h, Matrix.mulVec_smul, PiLp.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

/- English proof (translation)
Use extensionality with `⟨v, i, j⟩`. Establish `h1` using `congrArg Complex.re (congrFun (h v) i)`. Establish `h2` using `congrArg Complex.im (congrFun (h v) i)`. Use `fin_cases j`. Conclude with `h1`.

Conclude with `h2`.
-/
theorem htImageCv_ext {P ι : Type*} [Fintype P] [Fintype ι] {y z : EuclideanSpace ℝ (P × ι × Fin 2)}
    (h : ∀ v, htImageCv y v = htImageCv z v) : y = z := by
  ext ⟨v, i, j⟩
  have h1 := congrArg Complex.re (congrFun (h v) i)
  have h2 := congrArg Complex.im (congrFun (h v) i)
  fin_cases j
  · exact h1
  · exact h2

/- English proof (translation)
Use function extensionality and compare the values at `i`. Apply the tactic sequence `apply Complex.ext <;> simp [htImageCv, htImageMap]`.
-/
theorem htImageCv_map {P ι κ : Type*} [Fintype P] [Fintype ι] [Fintype κ] (M : P → Matrix κ ι ℂ)
    (y : EuclideanSpace ℝ (P × ι × Fin 2)) (v : P) :
    htImageCv (htImageMap M y) v = (M v).mulVec (htImageCv y v) := by
  funext i
  apply Complex.ext <;> simp [htImageCv, htImageMap]

/- English proof (translation)
Rewrite `hy` using `[mem_place_part_iff]`. Use function extensionality and compare the values at `i`. Apply `Complex.ext` to reduce the goal to its premises. Simplify `hy (w, i, 0) h` using `[htImageCv]`. Simplify `hy (w, i, 1) h` using `[htImageCv]`.
-/
theorem htImageCv_zero_of_mem {P ι : Type*} [Fintype P] [Fintype ι] {v w : P} (h : w ≠ v)
    {y : EuclideanSpace ℝ (P × ι × Fin 2)} (hy : y ∈ placePart v) : htImageCv y w = 0 := by
  rw [mem_place_part_iff] at hy
  funext i
  apply Complex.ext
  · simpa [htImageCv] using hy (w, i, 0) h
  · simpa [htImageCv] using hy (w, i, 1) h

/- English proof (translation)
Rewrite using `[mem_place_part_iff]`. Introduce `p hp`. Establish `h0 : htImageCv y p.1 = 0` using `htImageCv_zero_of_mem hp hy`. Simplify using `[htImageMap, h0]`.
-/
theorem htImage_map_mem {P ι κ : Type*} [Fintype P] [Fintype ι] [Fintype κ]
    (M : P → Matrix κ ι ℂ) {v : P} {y : EuclideanSpace ℝ (P × ι × Fin 2)} (hy : y ∈ placePart v) :
    htImageMap M y ∈ placePart v := by
  rw [mem_place_part_iff]
  intro p hp
  have h0 : htImageCv y p.1 = 0 := htImageCv_zero_of_mem hp hy
  simp [htImageMap, h0]

/- English proof (translation)
Rewrite `hy` using `[mem_place_part_iff]`. Rewrite using `[EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]`. Use `congr 1`. Rewrite using `[Fintype.sum_prod_type, Finset.sum_eq_single v]`. Rewrite using `[Fintype.sum_prod_type]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[Fin.sum_univ_two]`. Simplify using `only [PiLp.toLp_apply, htImageCv, Complex.sq_norm, Complex.normSq_apply, Real.norm_eq_abs, sq_abs]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `w _ hw`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `q _`. Simplify using `[hy (w, q) hw]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ v) h`.
-/
theorem htImage_norm_placePart {P ι : Type*} [Fintype P] [Fintype ι] {v : P}
    {y : EuclideanSpace ℝ (P × ι × Fin 2)} (hy : y ∈ placePart v) :
    ‖y‖ = ‖(WithLp.toLp 2 (htImageCv y v) : EuclideanSpace ℂ ι)‖ := by
  rw [mem_place_part_iff] at hy
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  rw [Fintype.sum_prod_type, Finset.sum_eq_single v]
  · rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    rw [Fin.sum_univ_two]
    simp only [PiLp.toLp_apply, htImageCv, Complex.sq_norm, Complex.normSq_apply,
      Real.norm_eq_abs, sq_abs]
    ring
  · intro w _ hw
    apply Finset.sum_eq_zero
    intro q _
    simp [hy (w, q) hw]
  · intro h
    exact absurd (Finset.mem_univ v) h

/- English proof (translation)
Rewrite using `[htImage_norm_placePart (htImage_map_mem M hy), htImage_norm_placePart hy, htImageCv_map]`. Use `le_of_eq_of_le ?_ ((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (M v))).le_opNorm _)` and prove the remaining obligations. Simplify using `[Matrix.toEuclideanLin_apply]`.
-/
theorem htImage_map_norm {P ι κ : Type*} [Fintype P] [Fintype ι] [Fintype κ] [DecidableEq ι]
    (M : P → Matrix κ ι ℂ) {v : P} {y : EuclideanSpace ℝ (P × ι × Fin 2)} (hy : y ∈ placePart v) :
    ‖htImageMap M y‖ ≤
      ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (M v))‖ * ‖y‖ := by
  rw [htImage_norm_placePart (htImage_map_mem M hy), htImage_norm_placePart hy, htImageCv_map]
  refine le_of_eq_of_le ?_
    ((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (M v))).le_opNorm _)
  simp [Matrix.toEuclideanLin_apply]

variable {K : Type*} [Field K] [NumberField K] [StarRing K]
  {V ι : Type*} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
  {W κ : Type*} [AddCommGroup W] [Module K W] [Fintype κ] [DecidableEq κ]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Apply the tactic sequence `apply Complex.ext <;> simp [htImageCv, Formalism.HermitianLatticesTheory.realize, Formalism.HermitianLatticesTheory.realizeRaw]`.
-/
theorem htImageCv_realize (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (x : V)
    (v : InfinitePlace K) :
    htImageCv (Formalism.HermitianLatticesTheory.realize b X x) v = Formalism.HermitianLatticesTheory.fcoord b X v x := by
  funext i
  apply Complex.ext <;> simp [htImageCv, Formalism.HermitianLatticesTheory.realize, Formalism.HermitianLatticesTheory.realizeRaw]

/- English proof (translation)
Take `⟨v⟩ : Nonempty (InfinitePlace K)` from `inferInstance`. Establish `h1 : Formalism.HermitianLatticesTheory.fcoord b X v x = 0`. Rewrite using `[← htImageCv_realize, h]`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `apply Complex.ext <;> simp [htImageCv]`.

Establish `h2 : Formalism.HermitianLatticesTheory.vecAt b v x = 0`. Establish `h3` using `congrArg (fun w => (X v).mulVec w) h1`. Simplify using `only [Formalism.HermitianLatticesTheory.fcoord, Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h3`. Rewrite `h3` using `[Matrix.mul_nonsing_inv _ (hX v), Matrix.one_mulVec]`. Then use the resulting hypothesis. Apply `b.repr.injective` to reduce the goal to its premises.

Use extensionality with `i`. Establish `h4` using `congrFun h2 i`. Simplify `h4` using `[Formalism.HermitianLatticesTheory.vecAt]`.
-/
theorem htImage_realize_eq_zero (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) {x : V} (h : Formalism.HermitianLatticesTheory.realize b X x = 0) : x = 0 := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace K) := inferInstance
  have h1 : Formalism.HermitianLatticesTheory.fcoord b X v x = 0 := by
    rw [← htImageCv_realize, h]
    funext i
    apply Complex.ext <;> simp [htImageCv]
  have h2 : Formalism.HermitianLatticesTheory.vecAt b v x = 0 := by
    have h3 := congrArg (fun w => (X v).mulVec w) h1
    simp only [Formalism.HermitianLatticesTheory.fcoord, Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h3
    rwa [Matrix.mul_nonsing_inv _ (hX v), Matrix.one_mulVec] at h3
  apply b.repr.injective
  ext i
  have h4 := congrFun h2 i
  simpa [Formalism.HermitianLatticesTheory.vecAt] using h4

def htImageMat (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (b' : Basis κ K W)
    (X' : InfinitePlace K → Matrix κ κ ℂ) (φ : V →ₗ[K] W) (v : InfinitePlace K) :
    Matrix κ ι ℂ :=
  (X' v)⁻¹ * (LinearMap.toMatrix b b' φ).map v.embedding * X v

/- English proof (translation)
Apply `htImageCv_ext` to reduce the goal to its premises. Introduce `v`. Rewrite using `[htImageCv_map, htImageCv_realize, htImageCv_realize]`. Simplify using `only [htImageMat, Formalism.HermitianLatticesTheory.fcoord, Matrix.mulVec_mulVec]`. Rewrite using `[Matrix.mul_assoc _ (X v), Matrix.mul_nonsing_inv _ (hX v), Matrix.mul_one, ← Matrix.mulVec_mulVec]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `only [Formalism.HermitianLatticesTheory.vecAt]`. Rewrite using `[← LinearMap.toMatrix_mulVec_repr b b' φ x, RingHom.map_mulVec]`. Both sides reduce to the same expression.
-/
theorem htImage_map_realize (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (hX : ∀ v, IsUnit (X v).det)
    (φ : V →ₗ[K] W) (x : V) :
    htImageMap (htImageMat b X b' X' φ) (Formalism.HermitianLatticesTheory.realize b X x) =
      Formalism.HermitianLatticesTheory.realize b' X' (φ x) := by
  apply htImageCv_ext
  intro v
  rw [htImageCv_map, htImageCv_realize, htImageCv_realize]
  simp only [htImageMat, Formalism.HermitianLatticesTheory.fcoord, Matrix.mulVec_mulVec]
  rw [Matrix.mul_assoc _ (X v), Matrix.mul_nonsing_inv _ (hX v), Matrix.mul_one,
    ← Matrix.mulVec_mulVec]
  congr 1
  funext i
  simp only [Formalism.HermitianLatticesTheory.vecAt]
  rw [← LinearMap.toMatrix_mulVec_repr b b' φ x, RingHom.map_mulVec]
  rfl

end HtImageReal

/- English proof (translation)
Use `show y ∈ AddSubgroup.map ρ N.toAddSubgroup ↔ _`. Simplify using the standard rewrite rules.
-/
theorem htImage_mem_zl {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E)
    (N : Submodule R V) (y : E) : y ∈ zl ρ N ↔ ∃ x ∈ N, ρ x = y := by
  show y ∈ AddSubgroup.map ρ N.toAddSubgroup ↔ _
  simp

/- English proof (translation)
Introduce `y hy`. Rewrite `hy`, the goal using `[htImage_mem_zl]`. Take `⟨x, hx, rfl⟩` from `hy`. Conclude with `⟨x, h hx, rfl⟩`.
-/
theorem htImage_zl_mono {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E)
    {N N' : Submodule R V} (h : N ≤ N') : zl ρ N ≤ zl ρ N' := by
  intro y hy
  rw [htImage_mem_zl] at hy ⊢
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨x, h hx, rfl⟩

/- English proof (translation)
Introduce `K V ι W κ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b X b' X' hX hX' φ A hA`. Use `set ρ := Formalism.HermitianLatticesTheory.realize b X with hρ`. Use `set ρ' := Formalism.HermitianLatticesTheory.realize b' X' with hρ'`. Use `set A₀ := A ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) with hA₀`. Use `set I := A.map (φ.restrictScalars (𝓞 K)) with hI`.

Use `set Φ := htImageMap (htImageMat b X b' X' φ) with hΦ`. Establish `hΦρ : ∀ x, Φ (ρ x) = ρ' (φ x)` using `htImage_map_realize b X b' X' hX φ`. Establish `hinj' : ∀ w, ρ' w = 0 → w = 0` using `fun w hw => htImage_realize_eq_zero b' X' hX' hw`. Use `set L := zl ρ A with hL`. Use `set N := zl ρ A₀ with hN`.

Use `set U := Submodule.span ℝ (N : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) with hU`. Establish `hNL : N ≤ L` using `htImage_zl_mono ρ inf_le_left`. Establish `hUker : U ≤ LinearMap.ker Φ`. Use `Submodule.span_le.2 fun y hy => ?_` and prove the remaining obligations. Take `⟨x, hx, rfl⟩` from `(htImage_mem_zl ρ A₀ y).1 hy`.

Establish `hφ : φ x = 0` using `by simpa [A₀] using (Submodule.mem_inf.1 hx).2`. Use `show Φ (ρ x) = 0`. Rewrite using `[hΦρ, hφ, map_zero]`. Establish `hsat : IsSat ρ A A₀`. Use `⟨inf_le_left, hNL, fun y hyL hyU => ?_⟩` and prove the remaining obligations.

Take `⟨x, hx, rfl⟩` from `(htImage_mem_zl ρ A y).1 hyL`. Establish `h0 : Φ (ρ x) = 0` using `hUker hyU`. Rewrite `h0` using `[hΦρ]`. Establish `hφ : φ x = 0` using `hinj' _ h0`. Conclude with `(htImage_mem_zl ρ A₀ _).2 ⟨x, Submodule.mem_inf.2 ⟨hx, by simpa using hφ⟩, rfl⟩`.

Use `⟨hsat, ?_⟩` and prove the remaining obligations. Establish `hA₀fg : A₀.FG` using `Submodule.FG.of_le hA inf_le_left`. Establish `hIfg : I.FG` using `hA.map _`. Take `⟨hLatA, hrkA, -⟩` from `h1 K V ι b X hX A hA`. Take `⟨hLatA₀, hrkA₀, -⟩` from `h1 K V ι b X hX A₀ hA₀fg`.

Take `⟨hLatI, hrkI, -⟩` from `h1 K W κ b' X' hX' I hIfg`. Use `haveI hLd : DiscreteTopology L := hLatA.2`. Use `haveI hId : DiscreteTopology (zl ρ' I) := hLatI.2`. Take `⟨hQd, hrkQ, -⟩` from `Formalism.F.degQuot _ L N hLd hsat.2`. Use `set Q := Formalism.F.quot L N with hQ`.

Use `haveI := hQd`. Establish `hπU : ∀ y ∈ U, Uᗮ.starProjection y = 0`. Introduce `y hy`. Rewrite using `[Submodule.starProjection_orthogonal_val, (Submodule.starProjection_eq_self_iff).2 hy, sub_self]`. Establish `hπ : ∀ z, Φ (Uᗮ.starProjection z) = Φ z`.

Introduce `z`. Rewrite using `[Submodule.starProjection_orthogonal_val, map_sub]`. Establish `: Φ (U.starProjection z) = 0` using `hUker (Submodule.starProjection_apply_mem U z)`. Rewrite using `[this, sub_zero]`. Establish `hmemQ : ∀ q, q ∈ Q ↔ ∃ x ∈ A, Uᗮ.starProjection (ρ x) = q`.

Introduce `q`. Simplify using `only [hQ, Formalism.F.quot, Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, rfl⟩`. Take `⟨x, hx, rfl⟩` from `(htImage_mem_zl ρ A z).1 hz`.

Conclude with `⟨x, hx, rfl⟩`. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨ρ x, (htImage_mem_zl ρ A _).2 ⟨x, hx, rfl⟩, rfl⟩`. Establish `hmaps : ∀ q : Q, ((Φ.restrictScalars ℤ).comp Q.subtype) q ∈ zl ρ' I`. Introduce and unpack `⟨q, hq⟩`.

Take `⟨x, hx, rfl⟩` from `(hmemQ q).1 hq`. Use `show Φ (Uᗮ.starProjection (ρ x)) ∈ zl ρ' I`. Rewrite using `[hπ, hΦρ]`. Conclude with `(htImage_mem_zl ρ' I _).2 ⟨φ x, Submodule.mem_map_of_mem hx, rfl⟩`. Use `set f := LinearMap.codRestrict (zl ρ' I) ((Φ.restrictScalars ℤ).comp Q.subtype) hmaps with hf`.

Establish `hfinj : Function.Injective f`. Use `(injective_iff_map_eq_zero f).2 fun ⟨q, hq⟩ h0 => ?_` and prove the remaining obligations. Establish `h0' : Φ q = 0` using `congrArg Subtype.val h0`. Take `⟨x, hx, rfl⟩` from `(hmemQ q).1 hq`. Rewrite `h0'` using `[hπ, hΦρ]`.

Establish `hφ : φ x = 0` using `hinj' _ h0'`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show Uᗮ.starProjection (ρ x) = 0`. Conclude with `hπU _ (Submodule.subset_span ((htImage_mem_zl ρ A₀ _).2 ⟨x, Submodule.mem_inf.2 ⟨hx, by simpa using hφ⟩, rfl⟩))`. Establish `hfsurj : Function.Surjective f`.

Introduce and unpack `⟨w, hw⟩`. Take `⟨i, hi, rfl⟩` from `(htImage_mem_zl ρ' I w).1 hw`. Take `⟨x, hx, rfl⟩` from `Submodule.mem_map.1 hi`. Use `⟨⟨Uᗮ.starProjection (ρ x), (hmemQ _).2 ⟨x, hx, rfl⟩⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Use `show Φ (Uᗮ.starProjection (ρ x)) = ρ' (φ x)`.

Rewrite using `[hπ, hΦρ]`. Set `e` to `LinearEquiv.ofBijective f ⟨hfinj, hfsurj⟩`. Establish `hrkQI : Formalism.F.rk Q = Formalism.F.rk (zl ρ' I)` using `LinearEquiv.finrank_eq e`. Establish `hd : 0 < Module.finrank ℚ K` using `Module.finrank_pos`. Use `set s := rkK I with hs_def`.

Establish `hs : rkK A = rkK A₀ + s`. Establish `e1 : Formalism.F.rk L = Module.finrank ℚ K * rkK A` using `hrkA`. Establish `e2 : Formalism.F.rk N = Module.finrank ℚ K * rkK A₀` using `hrkA₀`. Establish `e3 : Formalism.F.rk (zl ρ' I) = Module.finrank ℚ K * s` using `hrkI`. Establish `: Module.finrank ℚ K * rkK A = Module.finrank ℚ K * (rkK A₀ + s)`.

Rewrite using `[mul_add, ← e1, ← e2, ← e3, ← hrkQI, hrkQ]`. Conclude with `Nat.eq_of_mul_eq_mul_left hd this`. Take `⟨hsplitA, hdimA⟩` from `h2 K V ι b X hX A hA`. Take `⟨hsplitA₀, hdimA₀⟩` from `h2 K V ι b X hX A₀ hA₀fg`. Establish `horth : ∀ v w : InfinitePlace K, v ≠ w → ∀ x ∈ (placePart v : Submodule ℝ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))), ∀ y ∈ (placePart w : Submodule ℝ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))), inner ℝ x y = 0` using `fun v w h x hx y hy => place_part_orthogonal h x hx y hy`.

Establish `horth' : ∀ v w : InfinitePlace K, v ≠ w → ∀ x ∈ (placePart v : Submodule ℝ (EuclideanSpace ℝ (InfinitePlace K × κ × Fin 2))), ∀ y ∈ (placePart w : Submodule ℝ (EuclideanSpace ℝ (InfinitePlace K × κ × Fin 2))), inner ℝ x y = 0` using `fun v w h x hx y hy => place_part_orthogonal h x hx y hy`. Establish `hS' : Submodule.span ℝ (L : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) = ⨆ v, Submodule.span ℝ (L : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) ⊓ placePart v` using `hsplitA`. Establish `hT' : U = ⨆ v, U ⊓ placePart v` using `hsplitA₀`. Establish `hTS : U ≤ Submodule.span ℝ (L : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)))` using `Submodule.span_mono hNL`. Take `⟨hWsplit, hWdim⟩` from `orthogonal_complement_place_split (E := EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) (fun v => placePart v) horth _ U hS' hT' hTS`.

Establish `hWspan` using `span_quotient_lattice_eq L N hNL`. Establish `hfr : ∀ v, Module.finrank ℝ (Submodule.span ℝ (Q : Set _) ⊓ placePart v : Submodule ℝ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) = 2 * s`. Introduce `v`. Establish `a1 : Module.finrank ℝ (Submodule.span ℝ (L : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) ⊓ Uᗮ ⊓ placePart v : Submodule ℝ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) + Module.finrank ℝ (U ⊓ placePart v : Submodule ℝ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) …` using `hWdim v`. Establish `a2 : Module.finrank ℝ (Submodule.span ℝ (L : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) ⊓ placePart v : Submodule ℝ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) = 2 * rkK A` using `hdimA v`.

Establish `a3 : Module.finrank ℝ (U ⊓ placePart v : Submodule ℝ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) = 2 * rkK A₀` using `hdimA₀ v`. Establish `a4 : Module.finrank ℝ (Submodule.span ℝ (Q : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) ⊓ placePart v : Submodule ℝ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) = Module.finrank ℝ (Submodule.span ℝ (L : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) ⊓ Uᗮ ⊓ …`. Rewrite using `[hWspan]`. Use linear arithmetic over natural numbers and integers. Set `u` to `Module.finBasis ℤ Q`.

Set `u' : Fin (Module.finrank ℤ Q) → EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)` to `fun i => (u i : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))`. Establish `hli : LinearIndependent ℝ u'` using `Formalism.F.linearIndependent_coe_basis''' Q u`. Establish `hspan : Submodule.span ℝ (Set.range u') = Submodule.span ℝ (Q : Set _)`. Rewrite using `[← Submodule.span_span_of_tower ℤ ℝ (Set.range u')]`. Conclude with `congrArg (fun M : Submodule ℤ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) => Submodule.span ℝ (M : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)))) (Formalism.F.span_range_coe_basis' Q u)`.

Establish `hcovQ : Formalism.F.covol Q = Real.sqrt (Matrix.gram ℝ u').det` using `Formalism.F.covolEqGram _ Q _ u`. Establish `hcovI : Formalism.F.covol (zl ρ' I) = Real.sqrt (Matrix.gram ℝ (fun i => Φ (u' i))).det`. Rewrite using `[Formalism.F.covolEqGram _ (zl ρ' I) _ (u.map e)]`. Use `congr 3`. Establish `hG` using `(h3 (InfinitePlace K) _ _ (Fin (Module.finrank ℤ Q)) (fun v => placePart v) (fun v => placePart v) Φ (fun v => opNormAt b X b' X' v φ) (Submodule.span ℝ (Q : Set _)) u' horth horth' (fun v => norm_nonneg _) (fun v x hx => ⟨htImage_map_mem _ hx, htImage_map_norm _ hx⟩) (by rw [hWs …`.

Simplify using `only [hfr] at hG`. Use `set C := ∏ v, opNormAt b X b' X' v φ ^ (2 * s) with hC`. Establish `hC0 : 0 ≤ C` using `Finset.prod_nonneg fun v _ => pow_nonneg (norm_nonneg _) _`. Establish `hC2 : (∏ v, opNormAt b X b' X' v φ ^ (2 * (2 * s))) = C ^ 2`. Rewrite using `[hC, ← Finset.prod_pow]`.

Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[← pow_mul]`. Put the polynomial expressions in normal form. Rewrite `hG` using `[hC2]`. Establish `hsq : Real.sqrt (Matrix.gram ℝ (fun i => Φ (u' i))).det ≤ C * Real.sqrt (Matrix.gram ℝ u').det`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC0]`. Establish `hsR : (rkK A : ℝ) - rkK A₀ = s` using `by rw [hs]; push_cast; ring`. Establish `h2pow : (2 : ℝ) ^ ((nPl K : ℝ) * (s : ℝ)) = 2 ^ (nPl K * s)`. Rewrite using `[← Nat.cast_mul, Real.rpow_natCast]`.

Unfold `ht htQ`. Rewrite using `[hsR, h2pow, hcovQ, ← hs_def, hcovI]`. Establish `ha : 0 ≤ (2 : ℝ) ^ (nPl K * s) * |(NumberField.discr K : ℝ)| ^ (-(s : ℝ) / 2)`. Check the signs of the components of the expression. Combine the equalities or inequalities in the displayed calculation.
-/
theorem htImage_of (h1 : PlLat) (h2 : PlaceSplit) (h3 : GramBlock) : HtImage := by
  intro K V ι W κ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b X b' X' hX hX' φ A hA
  classical
  set ρ := Formalism.HermitianLatticesTheory.realize b X with hρ
  set ρ' := Formalism.HermitianLatticesTheory.realize b' X' with hρ'
  set A₀ := A ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) with hA₀
  set I := A.map (φ.restrictScalars (𝓞 K)) with hI
  set Φ := htImageMap (htImageMat b X b' X' φ) with hΦ
  have hΦρ : ∀ x, Φ (ρ x) = ρ' (φ x) := htImage_map_realize b X b' X' hX φ
  have hinj' : ∀ w, ρ' w = 0 → w = 0 := fun w hw => htImage_realize_eq_zero b' X' hX' hw
  set L := zl ρ A with hL
  set N := zl ρ A₀ with hN
  set U := Submodule.span ℝ (N : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) with hU
  have hNL : N ≤ L := htImage_zl_mono ρ inf_le_left
  have hUker : U ≤ LinearMap.ker Φ := by
    refine Submodule.span_le.2 fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := (htImage_mem_zl ρ A₀ y).1 hy
    have hφ : φ x = 0 := by simpa [A₀] using (Submodule.mem_inf.1 hx).2
    show Φ (ρ x) = 0
    rw [hΦρ, hφ, map_zero]
  have hsat : IsSat ρ A A₀ := by
    refine ⟨inf_le_left, hNL, fun y hyL hyU => ?_⟩
    obtain ⟨x, hx, rfl⟩ := (htImage_mem_zl ρ A y).1 hyL
    have h0 : Φ (ρ x) = 0 := hUker hyU
    rw [hΦρ] at h0
    have hφ : φ x = 0 := hinj' _ h0
    exact (htImage_mem_zl ρ A₀ _).2 ⟨x, Submodule.mem_inf.2 ⟨hx, by simpa using hφ⟩, rfl⟩
  refine ⟨hsat, ?_⟩
  have hA₀fg : A₀.FG := Submodule.FG.of_le hA inf_le_left
  have hIfg : I.FG := hA.map _
  obtain ⟨hLatA, hrkA, -⟩ := h1 K V ι b X hX A hA
  obtain ⟨hLatA₀, hrkA₀, -⟩ := h1 K V ι b X hX A₀ hA₀fg
  obtain ⟨hLatI, hrkI, -⟩ := h1 K W κ b' X' hX' I hIfg
  haveI hLd : DiscreteTopology L := hLatA.2
  haveI hId : DiscreteTopology (zl ρ' I) := hLatI.2
  obtain ⟨hQd, hrkQ, -⟩ := Formalism.F.degQuot _ L N hLd hsat.2
  set Q := Formalism.F.quot L N with hQ
  haveI := hQd

  have hπU : ∀ y ∈ U, Uᗮ.starProjection y = 0 := by
    intro y hy
    rw [Submodule.starProjection_orthogonal_val, (Submodule.starProjection_eq_self_iff).2 hy,
      sub_self]
  have hπ : ∀ z, Φ (Uᗮ.starProjection z) = Φ z := by
    intro z
    rw [Submodule.starProjection_orthogonal_val, map_sub]
    have : Φ (U.starProjection z) = 0 := hUker (Submodule.starProjection_apply_mem U z)
    rw [this, sub_zero]
  have hmemQ : ∀ q, q ∈ Q ↔ ∃ x ∈ A, Uᗮ.starProjection (ρ x) = q := by
    intro q
    simp only [hQ, Formalism.F.quot, Submodule.mem_map]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨x, hx, rfl⟩ := (htImage_mem_zl ρ A z).1 hz
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨ρ x, (htImage_mem_zl ρ A _).2 ⟨x, hx, rfl⟩, rfl⟩
  have hmaps : ∀ q : Q, ((Φ.restrictScalars ℤ).comp Q.subtype) q ∈ zl ρ' I := by
    rintro ⟨q, hq⟩
    obtain ⟨x, hx, rfl⟩ := (hmemQ q).1 hq
    show Φ (Uᗮ.starProjection (ρ x)) ∈ zl ρ' I
    rw [hπ, hΦρ]
    exact (htImage_mem_zl ρ' I _).2 ⟨φ x, Submodule.mem_map_of_mem hx, rfl⟩
  set f := LinearMap.codRestrict (zl ρ' I) ((Φ.restrictScalars ℤ).comp Q.subtype) hmaps with hf
  have hfinj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 fun ⟨q, hq⟩ h0 => ?_
    have h0' : Φ q = 0 := congrArg Subtype.val h0
    obtain ⟨x, hx, rfl⟩ := (hmemQ q).1 hq
    rw [hπ, hΦρ] at h0'
    have hφ : φ x = 0 := hinj' _ h0'
    apply Subtype.ext
    show Uᗮ.starProjection (ρ x) = 0
    exact hπU _ (Submodule.subset_span
      ((htImage_mem_zl ρ A₀ _).2 ⟨x, Submodule.mem_inf.2 ⟨hx, by simpa using hφ⟩, rfl⟩))
  have hfsurj : Function.Surjective f := by
    rintro ⟨w, hw⟩
    obtain ⟨i, hi, rfl⟩ := (htImage_mem_zl ρ' I w).1 hw
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hi
    refine ⟨⟨Uᗮ.starProjection (ρ x), (hmemQ _).2 ⟨x, hx, rfl⟩⟩, Subtype.ext ?_⟩
    show Φ (Uᗮ.starProjection (ρ x)) = ρ' (φ x)
    rw [hπ, hΦρ]
  let e := LinearEquiv.ofBijective f ⟨hfinj, hfsurj⟩

  have hrkQI : Formalism.F.rk Q = Formalism.F.rk (zl ρ' I) := LinearEquiv.finrank_eq e
  have hd : 0 < Module.finrank ℚ K := Module.finrank_pos
  set s := rkK I with hs_def
  have hs : rkK A = rkK A₀ + s := by
    have e1 : Formalism.F.rk L = Module.finrank ℚ K * rkK A := hrkA
    have e2 : Formalism.F.rk N = Module.finrank ℚ K * rkK A₀ := hrkA₀
    have e3 : Formalism.F.rk (zl ρ' I) = Module.finrank ℚ K * s := hrkI
    have : Module.finrank ℚ K * rkK A = Module.finrank ℚ K * (rkK A₀ + s) := by
      rw [mul_add, ← e1, ← e2, ← e3, ← hrkQI, hrkQ]
    exact Nat.eq_of_mul_eq_mul_left hd this

  obtain ⟨hsplitA, hdimA⟩ := h2 K V ι b X hX A hA
  obtain ⟨hsplitA₀, hdimA₀⟩ := h2 K V ι b X hX A₀ hA₀fg
  have horth : ∀ v w : InfinitePlace K, v ≠ w →
      ∀ x ∈ (placePart v : Submodule ℝ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))),
      ∀ y ∈ (placePart w : Submodule ℝ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))),
      inner ℝ x y = 0 :=
    fun v w h x hx y hy => place_part_orthogonal h x hx y hy
  have horth' : ∀ v w : InfinitePlace K, v ≠ w →
      ∀ x ∈ (placePart v : Submodule ℝ (EuclideanSpace ℝ (InfinitePlace K × κ × Fin 2))),
      ∀ y ∈ (placePart w : Submodule ℝ (EuclideanSpace ℝ (InfinitePlace K × κ × Fin 2))),
      inner ℝ x y = 0 :=
    fun v w h x hx y hy => place_part_orthogonal h x hx y hy
  have hS' : Submodule.span ℝ (L : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) =
      ⨆ v, Submodule.span ℝ (L : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) ⊓
        placePart v := hsplitA
  have hT' : U = ⨆ v, U ⊓ placePart v := hsplitA₀
  have hTS : U ≤ Submodule.span ℝ (L : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) :=
    Submodule.span_mono hNL
  obtain ⟨hWsplit, hWdim⟩ := orthogonal_complement_place_split
    (E := EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) (fun v => placePart v) horth
    _ U hS' hT' hTS
  have hWspan := span_quotient_lattice_eq L N hNL
  have hfr : ∀ v, Module.finrank ℝ (Submodule.span ℝ (Q : Set _) ⊓ placePart v :
      Submodule ℝ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) = 2 * s := by
    intro v
    have a1 : Module.finrank ℝ (Submodule.span ℝ (L : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) ⊓ Uᗮ ⊓ placePart v :
        Submodule ℝ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) +
        Module.finrank ℝ (U ⊓ placePart v : Submodule ℝ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) =
        Module.finrank ℝ (Submodule.span ℝ (L : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) ⊓ placePart v :
        Submodule ℝ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) := hWdim v
    have a2 : Module.finrank ℝ (Submodule.span ℝ (L : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) ⊓ placePart v :
        Submodule ℝ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) = 2 * rkK A := hdimA v
    have a3 : Module.finrank ℝ (U ⊓ placePart v : Submodule ℝ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) =
        2 * rkK A₀ := hdimA₀ v
    have a4 : Module.finrank ℝ (Submodule.span ℝ (Q : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) ⊓ placePart v :
        Submodule ℝ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) =
        Module.finrank ℝ (Submodule.span ℝ (L : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) ⊓ Uᗮ ⊓ placePart v :
        Submodule ℝ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) := by
      rw [hWspan]
    omega

  let u := Module.finBasis ℤ Q
  let u' : Fin (Module.finrank ℤ Q) → EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) :=
    fun i => (u i : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))
  have hli : LinearIndependent ℝ u' := Formalism.F.linearIndependent_coe_basis''' Q u
  have hspan : Submodule.span ℝ (Set.range u') = Submodule.span ℝ (Q : Set _) := by
    rw [← Submodule.span_span_of_tower ℤ ℝ (Set.range u')]
    exact congrArg (fun M : Submodule ℤ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) =>
      Submodule.span ℝ (M : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))))
      (Formalism.F.span_range_coe_basis' Q u)
  have hcovQ : Formalism.F.covol Q = Real.sqrt (Matrix.gram ℝ u').det :=
    Formalism.F.covolEqGram _ Q _ u
  have hcovI : Formalism.F.covol (zl ρ' I) = Real.sqrt (Matrix.gram ℝ (fun i => Φ (u' i))).det := by
    rw [Formalism.F.covolEqGram _ (zl ρ' I) _ (u.map e)]
    congr 3

  have hG := (h3 (InfinitePlace K) _ _ (Fin (Module.finrank ℤ Q)) (fun v => placePart v)
    (fun v => placePart v) Φ (fun v => opNormAt b X b' X' v φ) (Submodule.span ℝ (Q : Set _)) u'
    horth horth' (fun v => norm_nonneg _)
    (fun v x hx => ⟨htImage_map_mem _ hx, htImage_map_norm _ hx⟩)
    (by rw [hWspan]; exact hWsplit) hli hspan).1
  simp only [hfr] at hG

  set C := ∏ v, opNormAt b X b' X' v φ ^ (2 * s) with hC
  have hC0 : 0 ≤ C := Finset.prod_nonneg fun v _ => pow_nonneg (norm_nonneg _) _
  have hC2 : (∏ v, opNormAt b X b' X' v φ ^ (2 * (2 * s))) = C ^ 2 := by
    rw [hC, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← pow_mul]; ring_nf
  rw [hC2] at hG
  have hsq : Real.sqrt (Matrix.gram ℝ (fun i => Φ (u' i))).det ≤
      C * Real.sqrt (Matrix.gram ℝ u').det := by
    calc Real.sqrt (Matrix.gram ℝ (fun i => Φ (u' i))).det
        ≤ Real.sqrt (C ^ 2 * (Matrix.gram ℝ u').det) := Real.sqrt_le_sqrt hG
      _ = C * Real.sqrt (Matrix.gram ℝ u').det := by
        rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC0]
  have hsR : (rkK A : ℝ) - rkK A₀ = s := by rw [hs]; push_cast; ring
  have h2pow : (2 : ℝ) ^ ((nPl K : ℝ) * (s : ℝ)) = 2 ^ (nPl K * s) := by
    rw [← Nat.cast_mul, Real.rpow_natCast]
  unfold ht htQ
  rw [hsR, h2pow, hcovQ, ← hs_def, hcovI]
  have ha : 0 ≤ (2 : ℝ) ^ (nPl K * s) * |(NumberField.discr K : ℝ)| ^ (-(s : ℝ) / 2) := by
    positivity
  calc (2 : ℝ) ^ (nPl K * s) * |(NumberField.discr K : ℝ)| ^ (-(s : ℝ) / 2) *
        Real.sqrt (Matrix.gram ℝ (fun i => Φ (u' i))).det
      ≤ (2 : ℝ) ^ (nPl K * s) * |(NumberField.discr K : ℝ)| ^ (-(s : ℝ) / 2) *
        (C * Real.sqrt (Matrix.gram ℝ u').det) := mul_le_mul_of_nonneg_left hsq ha
    _ = C * ((2 : ℝ) ^ (nPl K * s) * |(NumberField.discr K : ℝ)| ^ (-(s : ℝ) / 2) *
        Real.sqrt (Matrix.gram ℝ u').det) := by ring

/- English proof (translation)
The claim follows from `htImage_of place_lattice_structure place_decomposition gram_block_determinant`.
-/
theorem height_image_formula : HtImage := htImage_of place_lattice_structure place_decomposition gram_block_determinant

end Formalism.HN
