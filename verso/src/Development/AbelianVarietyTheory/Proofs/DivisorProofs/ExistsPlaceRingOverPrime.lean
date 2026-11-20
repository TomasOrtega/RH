import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacGlueIndicator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeAtFinitePlaceEqIntegralSpanGenerato
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeLocalDarbouxCoordsBounded
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneCo

noncomputable section

namespace GlobalTheory.ThK.PlaneCo.VacSB

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `hn : n₁ + 2 = n` using `hH.rank.symm`. Use `set e : Fin n₁ ⊕ Fin 2 ≃ Fin n := finSumFinEquiv.trans (finCongr hn) with he`. Use `set Q' : Matrix (Fin n) (Fin n) E := (planeMat H).submatrix id e.symm with hQ'`. Establish `hP : planeCoef H = Q'⁻¹.submatrix e id`. Rewrite using `[planeCoef, dif_pos hn]`.

Establish `hsurj : Function.Surjective Q'.mulVec`. Establish `hrange : ∀ z ∈ X.L, z ∈ LinearMap.range Q'.mulVecLin`. Introduce `z hz`. Take `⟨s, t, u, -, -, -, rfl⟩` from `hH.split z hz`. Use `⟨(Sum.elim u ![s, t]) ∘ e.symm, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.mulVecLin_apply, hQ', Matrix.submatrix_mulVec_equiv]`. Use function extensionality and compare the values at `i`. Simplify using `only [Equiv.symm_symm, Function.comp_apply, Equiv.symm_apply_apply, id]`. Establish `: (fun x => (Sum.elim u ![s, t] ∘ e.symm) (e x)) = Sum.elim u ![s, t]`. Use function extensionality and compare the values at `x`.

Simplify using the standard rewrite rules. Rewrite using `[Function.comp_def, this]`. Simplify using `[planeMat, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]`. Expand and normalize the polynomial expressions, which then agree. Establish `htop : LinearMap.range Q'.mulVecLin = ⊤`.

Rewrite using `[eq_top_iff, ← hL.span_eq_top, Submodule.span_le]`. Conclude with `hrange`. Introduce `z`. Take `⟨w, hw⟩` from `(LinearMap.range_eq_top.1 htop) z`. Conclude with `⟨w, hw⟩`.

Establish `hU : IsUnit Q'` using `Matrix.mulVec_surjective_iff_isUnit.1 hsurj`. Establish `hdet : IsUnit Q'.det` using `(Matrix.isUnit_iff_isUnit_det Q').1 hU`. Establish `hQ : planeMat H = Q'.submatrix id e`. Rewrite using `[hQ']`. Use extensionality with `i k`.

Simplify using the standard rewrite rules. Rewrite using `[hP, hQ, ← Matrix.submatrix_mul Q'⁻¹ Q' e id e Function.bijective_id, Matrix.nonsing_inv_mul _ hdet, Matrix.submatrix_one_equiv]`.
-/
theorem planeCoef_mul_planeMat (σ : E →ₐ[F] E) (B : Base F E) {n n₁ j₀ j₁ : ℕ} (X : Spc F E n) (X₁ : Spc F E n₁)
    (H : Plane E n n₁) (hL : X.L.IsLattice E) (hH : H.IsAdapted σ B X X₁ j₀ j₁) : planeCoef H * planeMat H = 1 := by
  classical
  have hn : n₁ + 2 = n := hH.rank.symm
  set e : Fin n₁ ⊕ Fin 2 ≃ Fin n := finSumFinEquiv.trans (finCongr hn) with he
  set Q' : Matrix (Fin n) (Fin n) E := (planeMat H).submatrix id e.symm with hQ'
  have hP : planeCoef H = Q'⁻¹.submatrix e id := by
    rw [planeCoef, dif_pos hn]
  have hsurj : Function.Surjective Q'.mulVec := by
    have hrange : ∀ z ∈ X.L, z ∈ LinearMap.range Q'.mulVecLin := by
      intro z hz
      obtain ⟨s, t, u, -, -, -, rfl⟩ := hH.split z hz
      refine ⟨(Sum.elim u ![s, t]) ∘ e.symm, ?_⟩
      rw [Matrix.mulVecLin_apply, hQ', Matrix.submatrix_mulVec_equiv]
      funext i
      simp only [Equiv.symm_symm, Function.comp_apply, Equiv.symm_apply_apply, id]
      have : (fun x => (Sum.elim u ![s, t] ∘ e.symm) (e x)) = Sum.elim u ![s, t] := by
        funext x; simp
      rw [Function.comp_def, this]
      simp [planeMat, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]
      ring
    have htop : LinearMap.range Q'.mulVecLin = ⊤ := by
      rw [eq_top_iff, ← hL.span_eq_top, Submodule.span_le]
      exact hrange
    intro z
    obtain ⟨w, hw⟩ := (LinearMap.range_eq_top.1 htop) z
    exact ⟨w, hw⟩
  have hU : IsUnit Q' := Matrix.mulVec_surjective_iff_isUnit.1 hsurj
  have hdet : IsUnit Q'.det := (Matrix.isUnit_iff_isUnit_det Q').1 hU
  have hQ : planeMat H = Q'.submatrix id e := by
    rw [hQ']; ext i k; simp
  rw [hP, hQ, ← Matrix.submatrix_mul Q'⁻¹ Q' e id e Function.bijective_id, Matrix.nonsing_inv_mul _ hdet,
    Matrix.submatrix_one_equiv]

variable (F) in

/- English proof (translation)
Establish `hsm : ∀ (e : E), ∀ x ∈ L, e • x ∈ Submodule.span F (L : Set (Fin n → E))`. Introduce `e x hx`. Take `⟨y, hy0, hy⟩` from `exists_integral_multiples ℤ ℚ (L := E) {e}`. Establish `hi` using `hy e (Finset.mem_singleton_self e)`. Set `o : 𝓞 E` to `⟨y • e, hi⟩`.

Establish `hyF : (y : F) ≠ 0` using `Int.cast_ne_zero.2 hy0`. Establish `hox : o • x = (y : F) • (e • x)`. Rewrite using `[← algebraMap_smul E o x]`. Use `show (y • e) • x = _`. Rewrite using `[smul_assoc, ← Int.cast_smul_eq_zsmul F]`.

Establish `: e • x = (y : F)⁻¹ • (o • x)` using `by rw [hox, inv_smul_smul₀ hyF]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span (L.smul_mem o hx))`. Establish `hsm' : ∀ (e : E), ∀ z ∈ Submodule.span F (L : Set (Fin n → E)), e • z ∈ Submodule.span F (L : Set (Fin n → E))`. Introduce `e z hz`.

Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx => exact hsm e x hx`. Consider the case `zero => rw [smul_zero]`. Conclude with `zero_mem _`. Consider the case `add a b _ _ ha hb => rw [smul_add]`.

Conclude with `add_mem ha hb`. Consider the case `smul c a _ ha => rw [smul_comm]`. Conclude with `Submodule.smul_mem _ _ ha`. Use `Submodule.eq_top_iff'.2 fun z => ?_` and prove the remaining obligations. Establish `hz : z ∈ Submodule.span E (L : Set (Fin n → E))` using `by rw [hL.span_eq_top]; trivial`.

Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx => exact Submodule.subset_span hx`. Consider the case `zero => exact zero_mem _`. Consider the case `add a b _ _ ha hb => exact add_mem ha hb`. Consider the case `smul c a _ ha => exact hsm' c a ha`.
-/
theorem span_lattice_eq_top {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsLattice E) :
    Submodule.span F (L : Set (Fin n → E)) = ⊤ := by
  have hsm : ∀ (e : E), ∀ x ∈ L, e • x ∈ Submodule.span F (L : Set (Fin n → E)) := by
    intro e x hx
    obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := E) {e}
    have hi := hy e (Finset.mem_singleton_self e)
    let o : 𝓞 E := ⟨y • e, hi⟩
    have hyF : (y : F) ≠ 0 := Int.cast_ne_zero.2 hy0
    have hox : o • x = (y : F) • (e • x) := by
      rw [← algebraMap_smul E o x]
      show (y • e) • x = _
      rw [smul_assoc, ← Int.cast_smul_eq_zsmul F]
    have : e • x = (y : F)⁻¹ • (o • x) := by rw [hox, inv_smul_smul₀ hyF]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (L.smul_mem o hx))
  have hsm' : ∀ (e : E), ∀ z ∈ Submodule.span F (L : Set (Fin n → E)),
      e • z ∈ Submodule.span F (L : Set (Fin n → E)) := by
    intro e z hz
    induction hz using Submodule.span_induction with
    | mem x hx => exact hsm e x hx
    | zero => rw [smul_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
    | smul c a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ _ ha
  refine Submodule.eq_top_iff'.2 fun z => ?_
  have hz : z ∈ Submodule.span E (L : Set (Fin n → E)) := by rw [hL.span_eq_top]; trivial
  induction hz using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul c a _ ha => exact hsm' c a ha

variable (F) in

/- English proof (translation)
Use `set P := Submodule.span F {m : Matrix (Fin n) (Fin d) E | ∃ x ∈ LX, ∃ y ∈ LW, m = Matrix.vecMulVec x y}`. Establish `hX'` using `span_lattice_eq_top F LX hX`. Establish `hW'` using `span_lattice_eq_top F LW hW`. Establish `all : ∀ x y, Matrix.vecMulVec x y ∈ P`. Introduce `x y`.

Establish `hx : x ∈ Submodule.span F (LX : Set (Fin n → E))` using `by rw [hX']; trivial`. Establish `hy : y ∈ Submodule.span F (LW : Set (Fin d → E))` using `by rw [hW']; trivial`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem y hy => exact Submodule.subset_span ⟨x, hx, y, hy, rfl⟩`. Consider the case `zero`. Rewrite using `[show Matrix.vecMulVec x (0 : Fin d → E) = 0 by ext; simp [Matrix.vecMulVec_apply]]; exact zero_mem _`. Consider the case `add a b _ _ ha hb`. Rewrite using `[show Matrix.vecMulVec x (a + b) = Matrix.vecMulVec x a + Matrix.vecMulVec x b by ext; simp [Matrix.vecMulVec_apply, mul_add]]`.

Conclude with `add_mem ha hb`. Consider the case `smul c a _ ha`. Rewrite using `[show Matrix.vecMulVec x (c • a) = c • Matrix.vecMulVec x a by ext; simp [Matrix.vecMulVec_apply, mul_smul_comm]]`. Conclude with `Submodule.smul_mem _ _ ha`. Consider the case `zero`.

Rewrite using `[show Matrix.vecMulVec (0 : Fin n → E) y = 0 by ext; simp [Matrix.vecMulVec_apply]]; exact zero_mem _`. Consider the case `add a b _ _ ha hb`. Rewrite using `[show Matrix.vecMulVec (a + b) y = Matrix.vecMulVec a y + Matrix.vecMulVec b y by ext; simp [Matrix.vecMulVec_apply, add_mul]]`. Conclude with `add_mem ha hb`. Consider the case `smul c a _ ha`.

Rewrite using `[show Matrix.vecMulVec (c • a) y = c • Matrix.vecMulVec a y by ext; simp [Matrix.vecMulVec_apply, smul_mul_assoc]]`. Conclude with `Submodule.smul_mem _ _ ha`. Use `Submodule.eq_top_iff'.2 fun m => ?_` and prove the remaining obligations. Rewrite using `[Matrix.matrix_eq_sum_single m]`. Use `Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations.

Establish `: Matrix.single i j (m i j) = Matrix.vecMulVec (Pi.single i (m i j)) (Pi.single j 1)`. Use extensionality with `a b`. Simplify using `only [Matrix.single_apply, Matrix.vecMulVec_apply, Pi.single_apply]`. Distinguish the cases in `h1 : a = i`. Substitute `h1` using the available equality.

Distinguish the cases in `h2 : b = j`. Substitute `h2` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h2, Ne.symm h2]`. Simplify using `[h1, Ne.symm h1]`.

Rewrite using `[this]`. Conclude with `all _ _`.
-/
theorem span_vecMulVec {n d : ℕ} (LX : Submodule (𝓞 E) (Fin n → E)) (LW : Submodule (𝓞 E) (Fin d → E))
    (hX : LX.IsLattice E) (hW : LW.IsLattice E) :
    Submodule.span F {m : Matrix (Fin n) (Fin d) E | ∃ x ∈ LX, ∃ y ∈ LW, m = Matrix.vecMulVec x y} = ⊤ := by
  classical
  set P := Submodule.span F {m : Matrix (Fin n) (Fin d) E | ∃ x ∈ LX, ∃ y ∈ LW, m = Matrix.vecMulVec x y}
  have hX' := span_lattice_eq_top F LX hX
  have hW' := span_lattice_eq_top F LW hW
  have all : ∀ x y, Matrix.vecMulVec x y ∈ P := by
    intro x y
    have hx : x ∈ Submodule.span F (LX : Set (Fin n → E)) := by rw [hX']; trivial
    have hy : y ∈ Submodule.span F (LW : Set (Fin d → E)) := by rw [hW']; trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
      induction hy using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span ⟨x, hx, y, hy, rfl⟩
      | zero =>
        rw [show Matrix.vecMulVec x (0 : Fin d → E) = 0 by ext; simp [Matrix.vecMulVec_apply]]; exact zero_mem _
      | add a b _ _ ha hb =>
        rw [show Matrix.vecMulVec x (a + b) = Matrix.vecMulVec x a + Matrix.vecMulVec x b by
          ext; simp [Matrix.vecMulVec_apply, mul_add]]
        exact add_mem ha hb
      | smul c a _ ha =>
        rw [show Matrix.vecMulVec x (c • a) = c • Matrix.vecMulVec x a by
          ext; simp [Matrix.vecMulVec_apply, mul_smul_comm]]
        exact Submodule.smul_mem _ _ ha
    | zero =>
      rw [show Matrix.vecMulVec (0 : Fin n → E) y = 0 by ext; simp [Matrix.vecMulVec_apply]]; exact zero_mem _
    | add a b _ _ ha hb =>
      rw [show Matrix.vecMulVec (a + b) y = Matrix.vecMulVec a y + Matrix.vecMulVec b y by
        ext; simp [Matrix.vecMulVec_apply, add_mul]]
      exact add_mem ha hb
    | smul c a _ ha =>
      rw [show Matrix.vecMulVec (c • a) y = c • Matrix.vecMulVec a y by
        ext; simp [Matrix.vecMulVec_apply, smul_mul_assoc]]
      exact Submodule.smul_mem _ _ ha
  refine Submodule.eq_top_iff'.2 fun m => ?_
  rw [Matrix.matrix_eq_sum_single m]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  have : Matrix.single i j (m i j) = Matrix.vecMulVec (Pi.single i (m i j)) (Pi.single j 1) := by
    ext a b
    simp only [Matrix.single_apply, Matrix.vecMulVec_apply, Pi.single_apply]
    by_cases h1 : a = i
    · subst h1
      by_cases h2 : b = j
      · subst h2; simp
      · simp [h2, Ne.symm h2]
    · simp [h1, Ne.symm h1]
  rw [this]; exact all _ _

/- English proof (translation)
Establish `he : ∀ k, (fun j => if k = j then (1 : Fv F v) else 0) ∈ Submodule.span (Fv F v) (S : Set (K → Fv F v))`. Introduce `k`. Rewrite using `[hsp]`. Discharge the goal by the elementary cases of `trivial`. Use `choose N f gg hfg using fun k => Submodule.mem_span_set'.1 (he k)`.

Take `⟨t, ht0, ht⟩` from `GlobalTheory.LatBound.exists_mul_mem_integers v (fun p : (Σ k, Fin (N k)) => f p.1 p.2)`. Establish `hte : ∀ k, t • (fun j => if k = j then (1 : Fv F v) else 0) ∈ S`. Introduce `k`. Rewrite using `[← hfg k, Finset.smul_sum]`. Use `AddSubgroup.sum_mem _ fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[smul_smul]`. Conclude with `hS _ (ht ⟨k, i⟩) _ (gg k i).2`. Set `U : Set (K → Fv F v)` to `(fun x k => t⁻¹ * x k) ⁻¹' (Set.univ.pi fun _ => (v.adicCompletionIntegers F : Set (Fv F v)))`. Establish `hU : IsOpen U`. Use `IsOpen.preimage (by fun_prop) (isOpen_set_pi Set.finite_univ fun _ _ => ?_)` and prove the remaining obligations.

Conclude with `Valued.isOpen_valuationSubring (v.adicCompletion F)`. Establish `h0 : (0 : K → Fv F v) ∈ U` using `fun k _ => by show t⁻¹ * 0 ∈ v.adicCompletionIntegers F`. Rewrite using `[mul_zero]`. Conclude with `zero_mem _`. Establish `hUS : U ⊆ S`.

Introduce `x hx`. Rewrite using `[pi_eq_sum_univ x]`. Use `AddSubgroup.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Establish `: x k • (fun j => if k = j then (1 : Fv F v) else 0) = (t⁻¹ * x k) • t • (fun j => if k = j then (1 : Fv F v) else 0)`. Rewrite using `[smul_smul, mul_comm t⁻¹, mul_assoc, inv_mul_cancel₀ ht0, mul_one]`.

Rewrite using `[this]`. Conclude with `hS _ (hx k (Set.mem_univ _)) _ (hte k)`. Conclude with `AddSubgroup.isOpen_of_mem_nhds S (g := 0) (Filter.mem_of_superset (hU.mem_nhds h0) hUS)`.
-/
theorem isOpen_of_span (v : HeightOneSpectrum (𝓞 F)) {K : Type} [Fintype K]
    (S : AddSubgroup (K → Fv F v)) (hS : ∀ c ∈ v.adicCompletionIntegers F, ∀ y ∈ S, c • y ∈ S)
    (hsp : Submodule.span (Fv F v) (S : Set (K → Fv F v)) = ⊤) : IsOpen (S : Set (K → Fv F v)) := by
  classical
  have he : ∀ k, (fun j => if k = j then (1 : Fv F v) else 0) ∈ Submodule.span (Fv F v) (S : Set (K → Fv F v)) := by
    intro k; rw [hsp]; trivial
  choose N f gg hfg using fun k => Submodule.mem_span_set'.1 (he k)
  obtain ⟨t, ht0, ht⟩ := GlobalTheory.LatBound.exists_mul_mem_integers v (fun p : (Σ k, Fin (N k)) => f p.1 p.2)
  have hte : ∀ k, t • (fun j => if k = j then (1 : Fv F v) else 0) ∈ S := by
    intro k
    rw [← hfg k, Finset.smul_sum]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    rw [smul_smul]
    exact hS _ (ht ⟨k, i⟩) _ (gg k i).2
  let U : Set (K → Fv F v) := (fun x k => t⁻¹ * x k) ⁻¹' (Set.univ.pi fun _ => (v.adicCompletionIntegers F : Set (Fv F v)))
  have hU : IsOpen U := by
    refine IsOpen.preimage (by fun_prop) (isOpen_set_pi Set.finite_univ fun _ _ => ?_)
    exact Valued.isOpen_valuationSubring (v.adicCompletion F)
  have h0 : (0 : K → Fv F v) ∈ U := fun k _ => by
    show t⁻¹ * 0 ∈ v.adicCompletionIntegers F
    rw [mul_zero]; exact zero_mem _
  have hUS : U ⊆ S := by
    intro x hx
    rw [pi_eq_sum_univ x]
    refine AddSubgroup.sum_mem _ fun k _ => ?_
    have : x k • (fun j => if k = j then (1 : Fv F v) else 0) =
        (t⁻¹ * x k) • t • (fun j => if k = j then (1 : Fv F v) else 0) := by
      rw [smul_smul, mul_comm t⁻¹, mul_assoc, inv_mul_cancel₀ ht0, mul_one]
    rw [this]
    exact hS _ (hx k (Set.mem_univ _)) _ (hte k)
  exact AddSubgroup.isOpen_of_mem_nhds S (g := 0) (Filter.mem_of_superset (hU.mem_nhds h0) hUS)

variable (F) in

def fRat {n d n₁ d₁ : ℕ} (H : Plane E n n₁) (H' : Plane E d d₁) :
    Matrix (Fin n) (Fin d) E →ₗ[F] (Kc F E d₁ n₁ → F) where
  toFun g k := (bE F E).repr ((planeCoef H * g * (planeCoef H')ᵀ) (posS k.1).1 (posS k.1).2) k.2
  map_add' a b := by funext k; simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c a := by funext k; simp [Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
Apply the tactic sequence `rintro (j|a) (j'|a') h <;> simp_all [posS]`.
-/
theorem posS_injective {d₁ n₁ : ℕ} : Function.Injective (posS (d₁ := d₁) (n₁ := n₁)) := by
  rintro (j|a) (j'|a') h <;> simp_all [posS]

/- English proof (translation)
Introduce `t`. Set `s : Ic d₁ n₁ → E` to `fun i => (bE F E).equivFun.symm (fun j => t (i, j))`. Set `C : Matrix (Fin n₁ ⊕ Fin 2) (Fin d₁ ⊕ Fin 2) E` to `fun p q => ∑ i, if posS i = (p, q) then s i else 0`. Establish `hC : ∀ i, C (posS i).1 (posS i).2 = s i`. Introduce `i`.

Simplify using `only [C, Prod.mk.eta]`. Rewrite using `[Finset.sum_eq_single i]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[posS_injective.ne hb]`.

Simplify using the standard rewrite rules. Use `⟨planeMat H * C * (planeMat H')ᵀ, funext fun k => ?_⟩` and prove the remaining obligations. Establish `e : planeCoef H * (planeMat H * C * (planeMat H')ᵀ) * (planeCoef H')ᵀ = C`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.transpose_mul, Matrix.mul_assoc]`.

Use `_ = C := by`. Rewrite using `[planeCoef_mul_planeMat σ B X X₁ H hXL hH, planeCoef_mul_planeMat σ B W W₁ H' hWL hH']`. Simplify using the standard rewrite rules. Use `show (bE F E).repr ((planeCoef H * (planeMat H * C * (planeMat H')ᵀ) * (planeCoef H')ᵀ) (posS k.1).1 (posS k.1).2) k.2 = t k`. Rewrite using `[e, hC]`.

Use `show (bE F E).repr ((bE F E).equivFun.symm (fun j => t (k.1, j))) k.2 = t k`. Rewrite using `[← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]`.
-/
theorem fRat_surjective (σ : E →ₐ[F] E) (B : Base F E) {n d n₁ d₁ i₀ i₁ j₀ j₁ : ℕ} (X : Spc F E n) (W : Spc F E d)
    (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁) (H' : Plane E d d₁) (hXL : X.L.IsLattice E)
    (hWL : W.L.IsLattice E) (hH : H.IsAdapted σ B X X₁ j₀ j₁) (hH' : H'.IsAdapted σ B W W₁ i₀ i₁) :
    Function.Surjective (fRat F H H') := by
  classical
  intro t
  let s : Ic d₁ n₁ → E := fun i => (bE F E).equivFun.symm (fun j => t (i, j))
  let C : Matrix (Fin n₁ ⊕ Fin 2) (Fin d₁ ⊕ Fin 2) E := fun p q => ∑ i, if posS i = (p, q) then s i else 0
  have hC : ∀ i, C (posS i).1 (posS i).2 = s i := by
    intro i
    simp only [C, Prod.mk.eta]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [posS_injective.ne hb]
    · simp
  refine ⟨planeMat H * C * (planeMat H')ᵀ, funext fun k => ?_⟩
  have e : planeCoef H * (planeMat H * C * (planeMat H')ᵀ) * (planeCoef H')ᵀ = C := by
    calc planeCoef H * (planeMat H * C * (planeMat H')ᵀ) * (planeCoef H')ᵀ
        = (planeCoef H * planeMat H) * C * (planeCoef H' * planeMat H')ᵀ := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = C := by
          rw [planeCoef_mul_planeMat σ B X X₁ H hXL hH, planeCoef_mul_planeMat σ B W W₁ H' hWL hH']
          simp
  show (bE F E).repr ((planeCoef H * (planeMat H * C * (planeMat H')ᵀ) * (planeCoef H')ᵀ) (posS k.1).1 (posS k.1).2) k.2 = t k
  rw [e, hC]
  show (bE F E).repr ((bE F E).equivFun.symm (fun j => t (k.1, j))) k.2 = t k
  rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

/- English proof (translation)
Simplify using `only [coefLin, LinearMap.coe_mk, AddHom.coe_mk, incM, Matrix.map_mul, Matrix.transpose_map]`.
-/
theorem coefLin_incM {n d n₁ d₁ : ℕ} (H : Plane E n n₁) (H' : Plane E d d₁) (g : Matrix (Fin n) (Fin d) E) :
    coefLin (F := F) H H' (incM F g) = incM F (planeCoef H * g * (planeCoef H')ᵀ) := by
  simp only [coefLin, LinearMap.coe_mk, AddHom.coe_mk, incM, Matrix.map_mul, Matrix.transpose_map]

/- English proof (translation)
Use `show (Algebra.TensorProduct.basis (AF F) (bE F E)).repr ((1 : AF F) ⊗ₜ[F] e) j = _`. Rewrite using `[Algebra.TensorProduct.basis_repr_tmul]`. Simplify using the standard rewrite rules.
-/
theorem bA_repr_inclR (e : E) (j : Fin (Module.finrank F E)) :
    (bA F E).repr (inclR (F := F) (AF F) e) j = algebraMap F (AF F) ((bE F E).repr e j) := by
  show (Algebra.TensorProduct.basis (AF F) (bE F E)).repr ((1 : AF F) ⊗ₜ[F] e) j = _
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp

/- English proof (translation)
Rewrite using `[map_smul]`. Simplify using `only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul, map_mul, GlobalTheory.EmbChart.evFin_atPlace]`. Use `congr 1`. Use `show evFin F v ((bA F E).repr (sI H H' (incM F g) k.1) k.2) = _`. Simplify using `only [sI, coefLin_incM]`.

Rewrite using `[show incM F (planeCoef H * g * (planeCoef H')ᵀ) (posS k.1).1 (posS k.1).2 = inclR (F := F) (AF F) ((planeCoef H * g * (planeCoef H')ᵀ) (posS k.1).1 (posS k.1).2) from rfl, bA_repr_inclR]`. Conclude with `(evFin F v).commutes _`.
-/
theorem evFin_planeT_smul_incM (σ : E →ₐ[F] E) {n d n₁ d₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (H : Plane E n n₁)
    (H' : Plane E d d₁) (v : Pl F) (c : Fv F v) (g : Matrix (Fin n) (Fin d) E) (k : Kc F E d₁ n₁) :
    evFin F v ((planeT σ X W H H' (GlobalTheory.EmbChart.atPlace v c • incM F g)).1.1 k) =
      c * algebraMap F (Fv F v) (fRat F H H' g k) := by
  rw [map_smul]
  simp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul, map_mul, GlobalTheory.EmbChart.evFin_atPlace]
  congr 1
  show evFin F v ((bA F E).repr (sI H H' (incM F g) k.1) k.2) = _
  simp only [sI, coefLin_incM]
  rw [show incM F (planeCoef H * g * (planeCoef H')ᵀ) (posS k.1).1 (posS k.1).2 =
    inclR (F := F) (AF F) ((planeCoef H * g * (planeCoef H')ᵀ) (posS k.1).1 (posS k.1).2) from rfl, bA_repr_inclR]
  exact (evFin F v).commutes _

end GlobalTheory.ThK.PlaneCo.VacSB

namespace GlobalTheory.ThK.PlaneCo.VacSB

/- English proof (translation)
Set `ι : (K → F) →ₗ[F] (K → Fv F v)` to `LinearMap.pi fun k => (Algebra.linearMap F (Fv F v)).comp (LinearMap.proj k)`. Establish `hι : ι '' T ⊆ ((Submodule.span (Fv F v) S).restrictScalars F : Set (K → Fv F v))`. Introduce and unpack `_ ⟨t, ht, rfl⟩`. Conclude with `Submodule.subset_span (hTS t ht)`. Establish `hsub : Submodule.map ι (Submodule.span F T) ≤ (Submodule.span (Fv F v) S).restrictScalars F`.

Rewrite using `[Submodule.map_span]`. Conclude with `Submodule.span_le.2 hι`. Use `Submodule.eq_top_iff'.2 fun y => ?_` and prove the remaining obligations. Rewrite using `[pi_eq_sum_univ y]`. Use `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_` and prove the remaining obligations.

Establish `h1 : ι (fun j => if k = j then 1 else 0) ∈ Submodule.map ι (Submodule.span F T)` using `Submodule.mem_map_of_mem (by rw [hT]; trivial)`. Establish `h2` using `hsub h1`. Establish `h3 : ι (fun j => if k = j then 1 else 0) = fun j => if k = j then (1 : Fv F v) else 0`. Use function extensionality and compare the values at `j`. Simplify using `only [ι, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, Algebra.linearMap_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Rewrite `h2` using `[h3]`. Conclude with `h2`.
-/
theorem base_span {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {K : Type} [Fintype K]
    (T : Set (K → F)) (hT : Submodule.span F T = ⊤) (S : Set (K → Fv F v))
    (hTS : ∀ t ∈ T, (fun k => algebraMap F (Fv F v) (t k)) ∈ S) : Submodule.span (Fv F v) S = ⊤ := by
  classical
  let ι : (K → F) →ₗ[F] (K → Fv F v) := LinearMap.pi fun k => (Algebra.linearMap F (Fv F v)).comp (LinearMap.proj k)
  have hι : ι '' T ⊆ ((Submodule.span (Fv F v) S).restrictScalars F : Set (K → Fv F v)) := by
    rintro _ ⟨t, ht, rfl⟩
    exact Submodule.subset_span (hTS t ht)
  have hsub : Submodule.map ι (Submodule.span F T) ≤ (Submodule.span (Fv F v) S).restrictScalars F := by
    rw [Submodule.map_span]; exact Submodule.span_le.2 hι
  refine Submodule.eq_top_iff'.2 fun y => ?_
  rw [pi_eq_sum_univ y]
  refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
  have h1 : ι (fun j => if k = j then 1 else 0) ∈ Submodule.map ι (Submodule.span F T) :=
    Submodule.mem_map_of_mem (by rw [hT]; trivial)
  have h2 := hsub h1
  have h3 : ι (fun j => if k = j then 1 else 0) = fun j => if k = j then (1 : Fv F v) else 0 := by
    funext j; simp only [ι, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, Algebra.linearMap_apply]
    split_ifs <;> simp
  rw [h3] at h2
  exact h2

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ H H' hB hX hW hH hH' v`. Take `⟨M, _, g, hg⟩` from `GlobalTheory.LatParam.latAtV_param X W hX.lat hW.lat v`. Use `set O := v.adicCompletionIntegers F`. Set `w : M → Kc F E d₁ n₁ → Fv F v` to `fun m k => algebraMap F (Fv F v) (fRat F H H' (g m) k)`. Establish `hΦ : ∀ (a : M → Fv F v) k, evFin F v ((planeT σ X W H H' (∑ m, GlobalTheory.EmbChart.atPlace v (a m) • incM F (g m))).1.1 k) = ∑ m, a m * w m k`.

Introduce `a k`. Rewrite using `[map_sum]`. Simplify using `only [Prod.fst_sum, Finset.sum_apply, map_sum]`. Conclude with `Finset.sum_congr rfl fun m _ => evFin_planeT_smul_incM σ X W H H' v (a m) (g m) k`. Establish `hrange : latS σ X W H H' v = Set.range (fun a : M → O => ∑ m, ((a m : Fv F v)) • w m)`.

Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨γ, hγ, hy⟩`. Take `⟨a, rfl⟩` from `(hg γ).1 hγ`. Use `⟨a, funext fun k => ?_⟩` and prove the remaining obligations.

Rewrite using `[hy k, hΦ]`. Simplify using `[Finset.sum_apply, smul_eq_mul]`. Introduce and unpack `⟨a, rfl⟩`. Use `⟨_, (hg _).2 ⟨a, rfl⟩, fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[hΦ]`.

Simplify using `[Finset.sum_apply, smul_eq_mul]`. Set `S : AddSubgroup (Kc F E d₁ n₁ → Fv F v)` to `{ carrier := Set.range (fun a : M → O => ∑ m, ((a m : Fv F v)) • w m) add_mem' := by`. Introduce and unpack `_ _ ⟨a, rfl⟩ ⟨b, rfl⟩`. Conclude with `⟨a + b, by simp [add_smul, Finset.sum_add_distrib]⟩`. Use the proof step `zero_mem' := ⟨0, by simp⟩`.

Use the proof step `neg_mem' := by`. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `⟨-a, by simp [neg_smul]⟩ }`. Establish `hSset : (S : Set (Kc F E d₁ n₁ → Fv F v)) = latS σ X W H H' v` using `hrange.symm`. Establish `hO : ∀ c ∈ O, ∀ y ∈ S, c • y ∈ S`.

Introduce and unpack `c hc _ ⟨a, rfl⟩`. Conclude with `⟨fun m => ⟨c, hc⟩ * a m, by simp [Finset.smul_sum, smul_smul]⟩`. Establish `hcpt : IsCompact (S : Set (Kc F E d₁ n₁ → Fv F v))` using `by haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v`. Use `isCompact_range ?_` and prove the remaining obligations. Conclude with `continuous_finset_sum _ fun m _ => Continuous.smul (f := fun a : M → O => ((a m : O) : Fv F v)) (continuous_subtype_val.comp (continuous_apply m)) continuous_const`.

Establish `hmem : ∀ x ∈ X.L, ∀ y ∈ W.L, (fun k => algebraMap F (Fv F v) (fRat F H H' (Matrix.vecMulVec x y) k)) ∈ S`. Introduce `x hx y hy`. Use `show _ ∈ (S : Set (Kc F E d₁ n₁ → Fv F v))`. Rewrite using `[hSset]`. Use `⟨GlobalTheory.EmbChart.atPlace v 1 • incM F (Matrix.vecMulVec x y), AddSubgroup.subset_closure ⟨GlobalTheory.EmbChart.atPlace v 1, GlobalTheory.VacAny.at_atPlace 1, ?_, x, hx, y, hy, rfl⟩, fun k => ?_⟩` and prove the remaining obligations.

Rewrite using `[GlobalTheory.EmbChart.evFin_atPlace]`. Conclude with `one_mem _`. Rewrite using `[evFin_planeT_smul_incM, one_mul]`. Establish `hspF : Submodule.span F {t | ∃ x ∈ X.L, ∃ y ∈ W.L, t = fRat F H H' (Matrix.vecMulVec x y)} = ⊤`. Establish `e : {t | ∃ x ∈ X.L, ∃ y ∈ W.L, t = fRat F H H' (Matrix.vecMulVec x y)} = fRat F H H' '' {m : Matrix (Fin n) (Fin d) E | ∃ x ∈ X.L, ∃ y ∈ W.L, m = Matrix.vecMulVec x y}`.

Use extensionality with `t`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, y, hy, rfl⟩`. Conclude with `⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩`. Introduce and unpack `⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩`.

Conclude with `⟨x, hx, y, hy, rfl⟩`. Rewrite using `[e, Submodule.span_image, span_vecMulVec F X.L W.L hX.lat hW.lat, Submodule.map_top, LinearMap.range_eq_top]`. Conclude with `fRat_surjective σ B X W X₁ W₁ H H' hX.lat hW.lat hH hH'`. Establish `hsp : Submodule.span (Fv F v) (S : Set (Kc F E d₁ n₁ → Fv F v)) = ⊤` using `base_span v _ hspF _ fun t ⟨x, hx, y, hy, ht⟩ => ht ▸ hmem x hx y hy`. Establish `hopen` using `isOpen_of_span v S hO hsp`.

Establish `hcl : IsClosed (S : Set (Kc F E d₁ n₁ → Fv F v))` using `hcpt.isClosed`. Use `show Set.indicator (latS σ X W H H' v) 1 ∈ GlobalTheory.WeilM.SB _`. Rewrite using `[← hSset]`. Use `set U : Set (Kc F E d₁ n₁ → Fv F v) := (S : Set (Kc F E d₁ n₁ → Fv F v)) with hU`. Use `⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_, HasCompactSupport.intro hcpt fun x hx => Set.indicator_of_notMem hx _⟩` and prove the remaining obligations.

Distinguish the cases in `hx : x ∈ U`. Conclude with `⟨U, hopen, hx, fun y hy => by simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩`. Conclude with `⟨Uᶜ, hcl.isOpen_compl, hx, fun y hy => by rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩`.
-/
theorem vacS_mem_SB : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (H : Plane E n n₁) (H' : Plane E d d₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ v, vacS σ X W H H' v ∈ SB _ := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ H H' hB hX hW hH hH' v
  classical
  obtain ⟨M, _, g, hg⟩ := GlobalTheory.LatParam.latAtV_param X W hX.lat hW.lat v
  set O := v.adicCompletionIntegers F
  let w : M → Kc F E d₁ n₁ → Fv F v := fun m k => algebraMap F (Fv F v) (fRat F H H' (g m) k)
  have hΦ : ∀ (a : M → Fv F v) k, evFin F v ((planeT σ X W H H'
      (∑ m, GlobalTheory.EmbChart.atPlace v (a m) • incM F (g m))).1.1 k) = ∑ m, a m * w m k := by
    intro a k
    rw [map_sum]
    simp only [Prod.fst_sum, Finset.sum_apply, map_sum]
    exact Finset.sum_congr rfl fun m _ => evFin_planeT_smul_incM σ X W H H' v (a m) (g m) k
  have hrange : latS σ X W H H' v = Set.range (fun a : M → O => ∑ m, ((a m : Fv F v)) • w m) := by
    ext y; constructor
    · rintro ⟨γ, hγ, hy⟩
      obtain ⟨a, rfl⟩ := (hg γ).1 hγ
      refine ⟨a, funext fun k => ?_⟩
      rw [hy k, hΦ]; simp [Finset.sum_apply, smul_eq_mul]
    · rintro ⟨a, rfl⟩
      refine ⟨_, (hg _).2 ⟨a, rfl⟩, fun k => ?_⟩
      rw [hΦ]; simp [Finset.sum_apply, smul_eq_mul]
  let S : AddSubgroup (Kc F E d₁ n₁ → Fv F v) :=
    { carrier := Set.range (fun a : M → O => ∑ m, ((a m : Fv F v)) • w m)
      add_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a + b, by simp [add_smul, Finset.sum_add_distrib]⟩
      zero_mem' := ⟨0, by simp⟩
      neg_mem' := by
        rintro _ ⟨a, rfl⟩
        exact ⟨-a, by simp [neg_smul]⟩ }
  have hSset : (S : Set (Kc F E d₁ n₁ → Fv F v)) = latS σ X W H H' v := hrange.symm
  have hO : ∀ c ∈ O, ∀ y ∈ S, c • y ∈ S := by
    rintro c hc _ ⟨a, rfl⟩
    exact ⟨fun m => ⟨c, hc⟩ * a m, by simp [Finset.smul_sum, smul_smul]⟩
  have hcpt : IsCompact (S : Set (Kc F E d₁ n₁ → Fv F v)) := by
    haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
    refine isCompact_range ?_
    exact continuous_finset_sum _ fun m _ =>
      Continuous.smul (f := fun a : M → O => ((a m : O) : Fv F v)) (continuous_subtype_val.comp (continuous_apply m))
        continuous_const
  have hmem : ∀ x ∈ X.L, ∀ y ∈ W.L, (fun k => algebraMap F (Fv F v) (fRat F H H' (Matrix.vecMulVec x y) k)) ∈ S := by
    intro x hx y hy
    show _ ∈ (S : Set (Kc F E d₁ n₁ → Fv F v))
    rw [hSset]
    refine ⟨GlobalTheory.EmbChart.atPlace v 1 • incM F (Matrix.vecMulVec x y), AddSubgroup.subset_closure
      ⟨GlobalTheory.EmbChart.atPlace v 1, GlobalTheory.VacAny.at_atPlace 1, ?_, x, hx, y, hy, rfl⟩, fun k => ?_⟩
    · rw [GlobalTheory.EmbChart.evFin_atPlace]; exact one_mem _
    · rw [evFin_planeT_smul_incM, one_mul]
  have hspF : Submodule.span F {t | ∃ x ∈ X.L, ∃ y ∈ W.L, t = fRat F H H' (Matrix.vecMulVec x y)} = ⊤ := by
    have e : {t | ∃ x ∈ X.L, ∃ y ∈ W.L, t = fRat F H H' (Matrix.vecMulVec x y)} =
        fRat F H H' '' {m : Matrix (Fin n) (Fin d) E | ∃ x ∈ X.L, ∃ y ∈ W.L, m = Matrix.vecMulVec x y} := by
      ext t; constructor
      · rintro ⟨x, hx, y, hy, rfl⟩; exact ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩; exact ⟨x, hx, y, hy, rfl⟩
    rw [e, Submodule.span_image, span_vecMulVec F X.L W.L hX.lat hW.lat, Submodule.map_top,
      LinearMap.range_eq_top]
    exact fRat_surjective σ B X W X₁ W₁ H H' hX.lat hW.lat hH hH'
  have hsp : Submodule.span (Fv F v) (S : Set (Kc F E d₁ n₁ → Fv F v)) = ⊤ :=
    base_span v _ hspF _ fun t ⟨x, hx, y, hy, ht⟩ => ht ▸ hmem x hx y hy
  have hopen := isOpen_of_span v S hO hsp
  have hcl : IsClosed (S : Set (Kc F E d₁ n₁ → Fv F v)) := hcpt.isClosed
  show Set.indicator (latS σ X W H H' v) 1 ∈ GlobalTheory.WeilM.SB _
  rw [← hSset]
  set U : Set (Kc F E d₁ n₁ → Fv F v) := (S : Set (Kc F E d₁ n₁ → Fv F v)) with hU
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_,
    HasCompactSupport.intro hcpt fun x hx => Set.indicator_of_notMem hx _⟩
  by_cases hx : x ∈ U
  · exact ⟨U, hopen, hx, fun y hy => by simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
  · exact ⟨Uᶜ, hcl.isOpen_compl, hx, fun y hy => by rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩

end GlobalTheory.ThK.PlaneCo.VacSB
