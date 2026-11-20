import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.Normal
import Formalism.WachLatticeTwists.RamifiedBlockRings.RightIdealImageOfSurjective

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

/- English proof (translation)
Introduce `EA δ`. Set `q : Polynomial K` to `∏ i ∈ Finset.Ioo 0 t, (Polynomial.X - Polynomial.C (α i))`. Establish `hEA : EA = Polynomial.aeval A q` using `by show EA = Polynomial.aeval A (∏ i ∈ Finset.Ioo 0 t, (Polynomial.X - Polynomial.C (α i)))`. Rewrite using `[← tailProd (fun i => Polynomial.X - Polynomial.C (α i)) t, map_list_prod, List.map_map]`. Use `congrArg List.prod (List.map_congr_left fun i _ => ?_)` and prove the remaining obligations.

Simplify using `[Algebra.algebraMap_eq_smul_one]`. Establish `hp : A.charpoly = (Polynomial.X - Polynomial.C (α 0)) * q`. Rewrite using `[hA, Finset.range_eq_Ico, Finset.prod_eq_prod_Ico_succ_bot (by omega)]`. Use `congr 1`. Establish `hδq : q.eval (α 0) = δ`.

Simplify using `[q, δ, Polynomial.eval_prod]`. Establish `hδ : δ ≠ 0`. Use `Finset.prod_ne_zero_iff.mpr fun i hi => ?_` and prove the remaining obligations. Rewrite `hi` using `[Finset.mem_Ioo]`. Introduce `h`.

Use `hα 0 i (by omega) hi.2 (sub_eq_zero.mp h)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hCH : Polynomial.aeval A ((Polynomial.X - Polynomial.C (α 0)) * q) = 0`. Rewrite using `[← hp]`. Conclude with `Matrix.aeval_self_charpoly A`.

Establish `hAE : A * EA = α 0 • EA`. Establish `h1` using `hCH`. Rewrite `h1` using `[map_mul, ← hEA]`. Establish `h2 : Polynomial.aeval A (Polynomial.X - Polynomial.C (α 0)) = A - α 0 • 1`. Simplify using `[Algebra.algebraMap_eq_smul_one]`.

Rewrite `h1` using `[h2, sub_mul, sub_eq_zero]`. Rewrite using `[h1]`. Simplify using the standard rewrite rules. Establish `hsq : EA * EA = δ • EA`. Take `⟨h, hh⟩` from `Polynomial.X_sub_C_dvd_sub_C_eval (a := α 0) (p := q)`.

Rewrite `hh` using `[hδq]`. Establish `h3 : q * q = Polynomial.C δ * q + h * ((Polynomial.X - Polynomial.C (α 0)) * q)`. Establish `: q = Polynomial.C δ + (Polynomial.X - Polynomial.C (α 0)) * h` using `by rw [← hh]; ring`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hEA, ← map_mul, h3, map_add, map_mul, map_mul _ h, hCH, mul_zero, add_zero, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]`.

Use `⟨hsq, ?_, hAE, hδ⟩` and prove the remaining obligations. Set `φ : Module.End K (S → K)` to `Matrix.toLin' A`. Establish `hφc : φ.charpoly = A.charpoly` using `Matrix.charpoly_toLin' A`. Apply `le_antisymm` to reduce the goal to its premises. Establish `h1 : LinearMap.range EA.mulVecLin ≤ φ.eigenspace (α 0)`.

Introduce and unpack `_ ⟨v, rfl⟩`. Rewrite using `[Module.End.mem_eigenspace_iff]`. Use `show A.mulVec (EA.mulVec v) = α 0 • EA.mulVec v`. Rewrite using `[Matrix.mulVec_mulVec, hAE, Matrix.smul_mulVec]`. Establish `h2 : Polynomial.rootMultiplicity (α 0) φ.charpoly = 1`.

Establish `hq0 : q ≠ 0` using `fun h => hδ (by rw [← hδq, h]; simp)`. Rewrite using `[hφc, hp, Polynomial.rootMultiplicity_mul (mul_ne_zero (Polynomial.X_sub_C_ne_zero _) hq0), Polynomial.rootMultiplicity_X_sub_C_self, Polynomial.rootMultiplicity_eq_zero (by rw [Polynomial.IsRoot, hδq]; exact hδ)]`. Combine the equalities or inequalities in the displayed calculation. Establish `hroot : φ.charpoly.IsRoot (α 0)`. Rewrite using `[hφc, hp, Polynomial.IsRoot, Polynomial.eval_mul]`.

Simplify using the standard rewrite rules. Take `⟨v, hv⟩` from `((Module.End.hasEigenvalue_iff_isRoot_charpoly φ (α 0)).mpr hroot).exists_hasEigenvector`. Establish `h1` using `Module.End.aeval_apply_of_hasEigenvector (p := q) hv`. Establish `h2 : Polynomial.aeval φ q = Matrix.toLin' EA`. Rewrite using `[hEA]`.

Conclude with `(Polynomial.aeval_algHom_apply (Matrix.toLinAlgEquiv' : Matrix S S K ≃ₐ[K] _) A q)`. Rewrite `h1` using `[h2, hδq]`. Assume the negation of the conclusion as `hlt`. Establish `h0 : EA.rank = 0` using `by omega`. Establish `h3 : LinearMap.range EA.mulVecLin = ⊥` using `Submodule.finrank_eq_zero.mp h0`.

Establish `h4 : EA.mulVecLin v ∈ LinearMap.range EA.mulVecLin` using `LinearMap.mem_range_self _ v`. Rewrite `h4` using `[h3, Submodule.mem_bot]`. Establish `h5 : δ • v = 0` using `by rw [← h1]; exact h4`. Conclude with `hv.2 ((smul_eq_zero.mp h5).resolve_left hδ)`.
-/
theorem eCore {K : Type} [Field K] {S : Type} [Fintype S] [DecidableEq S] (A : Matrix S S K) (t : ℕ)
    (α : ℕ → K) (ht : 1 ≤ t)
    (hA : A.charpoly = ∏ i ∈ Finset.range t, (Polynomial.X - Polynomial.C (α i)))
    (hα : ∀ i j, i < t → j < t → α i = α j → i = j) :
    let EA := ((List.range t).tail.map fun i => A - α i • (1 : Matrix S S K)).prod
    let δ := ∏ i ∈ Finset.Ioo 0 t, (α 0 - α i)
    EA * EA = δ • EA ∧ EA.rank = 1 ∧ A * EA = α 0 • EA ∧ δ ≠ 0 := by
  intro EA δ
  let q : Polynomial K := ∏ i ∈ Finset.Ioo 0 t, (Polynomial.X - Polynomial.C (α i))
  have hEA : EA = Polynomial.aeval A q := by
    show EA = Polynomial.aeval A (∏ i ∈ Finset.Ioo 0 t, (Polynomial.X - Polynomial.C (α i)))
    rw [← tailProd (fun i => Polynomial.X - Polynomial.C (α i)) t, map_list_prod, List.map_map]
    refine congrArg List.prod (List.map_congr_left fun i _ => ?_)
    simp [Algebra.algebraMap_eq_smul_one]
  have hp : A.charpoly = (Polynomial.X - Polynomial.C (α 0)) * q := by
    rw [hA, Finset.range_eq_Ico, Finset.prod_eq_prod_Ico_succ_bot (by omega)]
    congr 1
  have hδq : q.eval (α 0) = δ := by
    simp [q, δ, Polynomial.eval_prod]
  have hδ : δ ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun i hi => ?_
    rw [Finset.mem_Ioo] at hi
    intro h
    have := hα 0 i (by omega) hi.2 (sub_eq_zero.mp h)
    omega
  have hCH : Polynomial.aeval A ((Polynomial.X - Polynomial.C (α 0)) * q) = 0 := by
    rw [← hp]; exact Matrix.aeval_self_charpoly A
  have hAE : A * EA = α 0 • EA := by
    have h1 := hCH
    rw [map_mul, ← hEA] at h1
    have h2 : Polynomial.aeval A (Polynomial.X - Polynomial.C (α 0)) = A - α 0 • 1 := by
      simp [Algebra.algebraMap_eq_smul_one]
    rw [h2, sub_mul, sub_eq_zero] at h1
    rw [h1]; simp
  have hsq : EA * EA = δ • EA := by
    obtain ⟨h, hh⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (a := α 0) (p := q)
    rw [hδq] at hh
    have h3 : q * q = Polynomial.C δ * q + h * ((Polynomial.X - Polynomial.C (α 0)) * q) := by
      have : q = Polynomial.C δ + (Polynomial.X - Polynomial.C (α 0)) * h := by rw [← hh]; ring
      calc q * q = (Polynomial.C δ + (Polynomial.X - Polynomial.C (α 0)) * h) * q := by rw [← this]
        _ = _ := by ring
    rw [hEA, ← map_mul, h3, map_add, map_mul, map_mul _ h, hCH, mul_zero, add_zero,
      Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  refine ⟨hsq, ?_, hAE, hδ⟩
  let φ : Module.End K (S → K) := Matrix.toLin' A
  have hφc : φ.charpoly = A.charpoly := Matrix.charpoly_toLin' A
  apply le_antisymm
  · have h1 : LinearMap.range EA.mulVecLin ≤ φ.eigenspace (α 0) := by
      rintro _ ⟨v, rfl⟩
      rw [Module.End.mem_eigenspace_iff]
      show A.mulVec (EA.mulVec v) = α 0 • EA.mulVec v
      rw [Matrix.mulVec_mulVec, hAE, Matrix.smul_mulVec]
    have h2 : Polynomial.rootMultiplicity (α 0) φ.charpoly = 1 := by
      have hq0 : q ≠ 0 := fun h => hδ (by rw [← hδq, h]; simp)
      rw [hφc, hp, Polynomial.rootMultiplicity_mul (mul_ne_zero (Polynomial.X_sub_C_ne_zero _) hq0),
        Polynomial.rootMultiplicity_X_sub_C_self,
        Polynomial.rootMultiplicity_eq_zero (by rw [Polynomial.IsRoot, hδq]; exact hδ)]
    calc EA.rank = Module.finrank K (LinearMap.range EA.mulVecLin) := rfl
      _ ≤ Module.finrank K (φ.eigenspace (α 0)) := Submodule.finrank_mono h1
      _ ≤ 1 := h2 ▸ LinearMap.finrank_eigenspace_le φ (α 0)
  · have hroot : φ.charpoly.IsRoot (α 0) := by
      rw [hφc, hp, Polynomial.IsRoot, Polynomial.eval_mul]; simp
    obtain ⟨v, hv⟩ := ((Module.End.hasEigenvalue_iff_isRoot_charpoly φ (α 0)).mpr hroot).exists_hasEigenvector
    have h1 := Module.End.aeval_apply_of_hasEigenvector (p := q) hv
    have h2 : Polynomial.aeval φ q = Matrix.toLin' EA := by
      rw [hEA]
      exact (Polynomial.aeval_algHom_apply (Matrix.toLinAlgEquiv' : Matrix S S K ≃ₐ[K] _) A q)
    rw [h2, hδq] at h1
    by_contra hlt
    have h0 : EA.rank = 0 := by omega
    have h3 : LinearMap.range EA.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h0
    have h4 : EA.mulVecLin v ∈ LinearMap.range EA.mulVecLin := LinearMap.mem_range_self _ v
    rw [h3, Submodule.mem_bot] at h4
    have h5 : δ • v = 0 := by rw [← h1]; exact h4
    exact hv.2 ((smul_eq_zero.mp h5).resolve_left hδ)

/- English proof (translation)
Take `⟨P, Q, dd, hdd, hPQ, hQP, rfl⟩` from `idem_normal_form e he`. Set `J : Matrix d {a // dd a = 1} K` to `Matrix.of fun a i => if a = i.1 then 1 else 0`. Establish `hJJ : J.transpose * J = 1`. Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, J, Matrix.of_apply, Matrix.one_apply]`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Establish `h' : i.1 ≠ j.1` using `fun e => hij (Subtype.ext e)`. Simplify using `[hij, h', Ne.symm h']`.

Establish `hJD : J * J.transpose = Matrix.diagonal dd`. Use extensionality with `a b`. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, J, Matrix.of_apply]`. Distinguish the cases in `ha : dd a = 1`. Rewrite using `[Finset.sum_eq_single ⟨a, ha⟩]`.

Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using `[ha]`. Simplify using `[Matrix.diagonal_apply_ne _ hab, Ne.symm hab]`. Introduce `i _ hi`.

Establish `: a ≠ i.1` using `fun e => hi (Subtype.ext e.symm)`. Simplify using `[this]`. Introduce `h`. Conclude with `absurd (mem_univ _) h`. Establish `h0 : dd a = 0` using `(hdd a).resolve_right ha`.

Rewrite using `[Finset.sum_eq_zero fun i _ => by`. Establish `: a ≠ i.1` using `fun e => ha (e ▸ i.2)`. Simplify using `[this]]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality.

Simplify using `[h0]`. Simplify using `[Matrix.diagonal_apply_ne _ hab]`. Use `⟨{a // dd a = 1}, inferInstance, inferInstance, P * J, J.transpose * Q, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc J, hJD, ← Matrix.mul_assoc]`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc Q, hQP, Matrix.one_mul, hJJ]`.
-/
theorem idem_factor {K : Type} [Field K] {d : Type} [Fintype d] [DecidableEq d] (e : Matrix d d K)
    (he : e * e = e) : ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (U : Matrix d S K)
      (W : Matrix S d K), U * W = e ∧ W * U = 1 := by
  obtain ⟨P, Q, dd, hdd, hPQ, hQP, rfl⟩ := idem_normal_form e he
  let J : Matrix d {a // dd a = 1} K := Matrix.of fun a i => if a = i.1 then 1 else 0
  have hJJ : J.transpose * J = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, J, Matrix.of_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij; simp
    · have h' : i.1 ≠ j.1 := fun e => hij (Subtype.ext e)
      simp [hij, h', Ne.symm h']
  have hJD : J * J.transpose = Matrix.diagonal dd := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.transpose_apply, J, Matrix.of_apply]
    by_cases ha : dd a = 1
    · rw [Finset.sum_eq_single ⟨a, ha⟩]
      · by_cases hab : a = b
        · subst hab; simp [ha]
        · simp [Matrix.diagonal_apply_ne _ hab, Ne.symm hab]
      · intro i _ hi
        have : a ≠ i.1 := fun e => hi (Subtype.ext e.symm)
        simp [this]
      · intro h; exact absurd (mem_univ _) h
    · have h0 : dd a = 0 := (hdd a).resolve_right ha
      rw [Finset.sum_eq_zero fun i _ => by
        have : a ≠ i.1 := fun e => ha (e ▸ i.2)
        simp [this]]
      by_cases hab : a = b
      · subst hab; simp [h0]
      · simp [Matrix.diagonal_apply_ne _ hab]
  refine ⟨{a // dd a = 1}, inferInstance, inferInstance, P * J, J.transpose * Q, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc J, hJD, ← Matrix.mul_assoc]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q, hQP, Matrix.one_mul, hJJ]

/- English proof (translation)
Introduce `K _ d _ _ e x t α ht he hex hxe hpoly hα E`. Take `⟨S, _, _, U, W, hUW, hWU⟩` from `idem_factor e he`. Set `A : Matrix S S K` to `W * x * U`. Establish `hx : x = U * A * W` using `by show x = U * (W * x * U) * W`. Establish `: U * (W * x * U) * W = (U * W) * x * (U * W)` using `by simp only [Matrix.mul_assoc]`.

Rewrite using `[this, hUW, hex, hxe]`. Establish `hsand : ∀ B B' : Matrix S S K, (U * B * W) * (U * B' * W) = U * (B * B') * W`. Introduce `B B'`. Establish `: (U * B * W) * (U * B' * W) = U * B * (W * U) * B' * W` using `by simp only [Matrix.mul_assoc]`. Rewrite using `[this, hWU, Matrix.mul_one]`.

Simplify using `only [Matrix.mul_assoc]`. Establish `he1 : e = U * (1 : Matrix S S K) * W` using `by rw [Matrix.mul_one, hUW]`. Establish `hf : ∀ i, x - α i • e = U * (A - α i • 1) * W`. Introduce `i`. Rewrite using `[Matrix.mul_sub, Matrix.sub_mul, ← hx, Matrix.mul_smul, Matrix.smul_mul, ← he1]`.

Establish `hlist : ∀ l : List ℕ, e * (l.map fun i => x - α i • e).prod = U * (l.map fun i => A - α i • (1 : Matrix S S K)).prod * W`. Introduce `l`. Proceed by induction on `l with`. Consider the case `nil => simp [hUW]`. Consider the case `cons i l ih`.

Simplify using `only [List.map_cons, List.prod_cons]`. Establish `h1 : e * ((x - α i • e) * (l.map fun i => x - α i • e).prod) = (x - α i • e) * (e * (l.map fun i => x - α i • e).prod)`. Establish `h2 : e * (x - α i • e) = (x - α i • e) * e`. Rewrite using `[mul_sub, sub_mul, hex, hxe, Matrix.mul_smul, Matrix.smul_mul]`. Rewrite using `[← mul_assoc, h2, mul_assoc]`.

Rewrite using `[h1, ih, hf, hsand]`. Establish `hchar : A.charpoly = ∏ i ∈ Finset.range t, (Polynomial.X - Polynomial.C (α i))`. Rewrite using `[← hpoly]`. Unfold `blockPoly Matrix.charpoly Matrix.charmatrix`. Set `C' : K →+* Polynomial K` to `Polynomial.C`.

Establish `hUW' : U.map C' * W.map C' = e.map C'` using `by rw [← Matrix.map_mul, hUW]`. Establish `hWU' : W.map C' * U.map C' = 1`. Rewrite using `[← Matrix.map_mul, hWU, Matrix.map_one _ C'.map_zero C'.map_one]`. Establish `hx' : x.map C' = U.map C' * A.map C' * W.map C'`. Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul, ← hx]`.

Establish `h1 : (Polynomial.X : Polynomial K) • e.map C' - x.map C' + (1 - e).map C' = 1 + U.map C' * (((Polynomial.X : Polynomial K) • 1 - A.map C' - 1) * W.map C')`. Establish `h2 : (1 - e).map C' = 1 - e.map C'`. Use extensionality with `i j`. Apply the tactic sequence `by_cases hij : i = j <;> simp [hij, Matrix.one_apply]`. Rewrite using `[h2, hx', ← hUW']`.

Simplify using `only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_assoc]`. Normalize the expressions using the abelian group laws. Rewrite using `[h1, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, hWU', Matrix.mul_one]`. Use `congr 1`. Use extensionality with `i j`.

Apply the tactic sequence `by_cases hij : i = j <;> simp [hij, Matrix.one_apply, C']`. Take `⟨h1, h2, h3, h4⟩` from `eCore A t α ht hchar hα`. Use `set EA := ((List.range t).tail.map fun i => A - α i • (1 : Matrix S S K)).prod with hEAdef`. Establish `hE : E = U * EA * W` using `hlist _`. Establish `hEA : EA = W * E * U`.

Rewrite using `[hE]`. Establish `: W * (U * EA * W) * U = (W * U) * EA * (W * U)` using `by simp only [Matrix.mul_assoc]`. Rewrite using `[this, hWU, Matrix.one_mul, Matrix.mul_one]`. Use `⟨?_, ?_, ?_, ?_, ?_, h4⟩` and prove the remaining obligations. Rewrite using `[hE, hsand, h1, Matrix.mul_smul, Matrix.smul_mul]`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[← h2, hE]`. Conclude with `(Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)`. Rewrite using `[← h2]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hE, hx, hsand, h3, Matrix.mul_smul, Matrix.smul_mul]`. Rewrite using `[hE, he1, hsand, Matrix.one_mul]`. Rewrite using `[hE, he1, hsand, Matrix.mul_one]`.
-/
theorem eMat : StatEMat := by
  intro K _ d _ _ e x t α ht he hex hxe hpoly hα E
  obtain ⟨S, _, _, U, W, hUW, hWU⟩ := idem_factor e he
  let A : Matrix S S K := W * x * U
  have hx : x = U * A * W := by
    show x = U * (W * x * U) * W
    have : U * (W * x * U) * W = (U * W) * x * (U * W) := by simp only [Matrix.mul_assoc]
    rw [this, hUW, hex, hxe]
  have hsand : ∀ B B' : Matrix S S K, (U * B * W) * (U * B' * W) = U * (B * B') * W := by
    intro B B'
    have : (U * B * W) * (U * B' * W) = U * B * (W * U) * B' * W := by simp only [Matrix.mul_assoc]
    rw [this, hWU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have he1 : e = U * (1 : Matrix S S K) * W := by rw [Matrix.mul_one, hUW]
  have hf : ∀ i, x - α i • e = U * (A - α i • 1) * W := by
    intro i
    rw [Matrix.mul_sub, Matrix.sub_mul, ← hx, Matrix.mul_smul, Matrix.smul_mul, ← he1]
  have hlist : ∀ l : List ℕ, e * (l.map fun i => x - α i • e).prod =
      U * (l.map fun i => A - α i • (1 : Matrix S S K)).prod * W := by
    intro l
    induction l with
    | nil => simp [hUW]
    | cons i l ih =>
      simp only [List.map_cons, List.prod_cons]
      have h1 : e * ((x - α i • e) * (l.map fun i => x - α i • e).prod) =
          (x - α i • e) * (e * (l.map fun i => x - α i • e).prod) := by
        have h2 : e * (x - α i • e) = (x - α i • e) * e := by
          rw [mul_sub, sub_mul, hex, hxe, Matrix.mul_smul, Matrix.smul_mul]
        rw [← mul_assoc, h2, mul_assoc]
      rw [h1, ih, hf, hsand]
  have hchar : A.charpoly = ∏ i ∈ Finset.range t, (Polynomial.X - Polynomial.C (α i)) := by
    rw [← hpoly]
    unfold blockPoly Matrix.charpoly Matrix.charmatrix
    let C' : K →+* Polynomial K := Polynomial.C
    have hUW' : U.map C' * W.map C' = e.map C' := by rw [← Matrix.map_mul, hUW]
    have hWU' : W.map C' * U.map C' = 1 := by
      rw [← Matrix.map_mul, hWU, Matrix.map_one _ C'.map_zero C'.map_one]
    have hx' : x.map C' = U.map C' * A.map C' * W.map C' := by
      rw [← Matrix.map_mul, ← Matrix.map_mul, ← hx]
    have h1 : (Polynomial.X : Polynomial K) • e.map C' - x.map C' + (1 - e).map C' =
        1 + U.map C' * (((Polynomial.X : Polynomial K) • 1 - A.map C' - 1) * W.map C') := by
      have h2 : (1 - e).map C' = 1 - e.map C' := by
        ext i j
        by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
      rw [h2, hx', ← hUW']
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_assoc]
      abel
    rw [h1, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, hWU', Matrix.mul_one]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply, C']
  obtain ⟨h1, h2, h3, h4⟩ := eCore A t α ht hchar hα
  set EA := ((List.range t).tail.map fun i => A - α i • (1 : Matrix S S K)).prod with hEAdef
  have hE : E = U * EA * W := hlist _
  have hEA : EA = W * E * U := by
    rw [hE]
    have : W * (U * EA * W) * U = (W * U) * EA * (W * U) := by simp only [Matrix.mul_assoc]
    rw [this, hWU, Matrix.one_mul, Matrix.mul_one]
  refine ⟨?_, ?_, ?_, ?_, ?_, h4⟩
  · rw [hE, hsand, h1, Matrix.mul_smul, Matrix.smul_mul]
  · apply le_antisymm
    · rw [← h2, hE]
      exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
    · rw [← h2]
      calc EA.rank = (W * E * U).rank := congrArg Matrix.rank hEA
        _ ≤ E.rank := (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · rw [hE, hx, hsand, h3, Matrix.mul_smul, Matrix.smul_mul]
  · rw [hE, he1, hsand, Matrix.one_mul]
  · rw [hE, he1, hsand, Matrix.mul_one]

end Formalism.RepresentationBoundsCohomology.ringDataObjects
