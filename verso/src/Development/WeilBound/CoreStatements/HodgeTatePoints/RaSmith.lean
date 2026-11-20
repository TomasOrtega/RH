import Development.WeilBound.CoreStatements.HodgeTatePoints.RaCpaf
import ReciprocityTheory.DualLattices.CotangentSurjective
import ReciprocityTheory.DualLattices.BlockOneMulMulBlockOne
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Ra

section lattice

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

/- English proof (translation)
Take `⟨m, g, hg⟩` from `Submodule.fg_iff_exists_fin_generating_family.1 hL`. Set `e : ι ≃ Fin (Fintype.card ι)` to `Fintype.equivFin ι`. Set `A : Matrix (Fin (Fintype.card ι)) (Fin m) R` to `Matrix.of fun i k => g k (e.symm i)`. Take `⟨P, Q, a, hP, hQ, hD⟩` from `ReciprocityTheory.PGsh.Up.Smith.smith_mat hv _ m A`. Establish `hPv : P⁻¹ * P = 1` using `Matrix.nonsing_inv_mul _ hP`.

Establish `hQv : Q * Q⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hQ`. Establish `hAQ : A * Q = P⁻¹ * (P * A * Q)`. Simplify using `only [← Matrix.mul_assoc, hPv, Matrix.one_mul]`. Establish `hA : A = P⁻¹ * (P * A * Q) * Q⁻¹`. Rewrite using `[← hAQ, Matrix.mul_assoc, hQv, Matrix.mul_one]`.

Set `Λ : Matrix ι ι R` to `Matrix.of fun j i => P⁻¹ (e i) (e j)`. Set `ε : ι → R` to `fun j => if (e j : ℕ) < m then a (e j) else 0`. Establish `hΛ : Λ = ((P⁻¹).submatrix e e)ᵀ`. Use extensionality with `j i`. Both sides reduce to the same expression.

Establish `hdet : IsUnit Λ.det`. Rewrite using `[hΛ, Matrix.det_transpose, Matrix.det_submatrix_equiv_self]`. Conclude with `(Matrix.isUnit_nonsing_inv_det_iff).2 hP`. Use `⟨Λ, ε, hdet, le_antisymm ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[← hg, Submodule.span_le]`.

Introduce and unpack `_ ⟨l, rfl⟩`. Establish `hgl : g l = ∑ k : Fin m, ∑ j : Fin (Fintype.card ι), (Q⁻¹ k l * (P * A * Q) j k) • Λ (e.symm j)`. Use extensionality with `i`. Establish `h1 : A (e i) l = (P⁻¹ * (P * A * Q) * Q⁻¹) (e i) l` using `by rw [← hA]`. Establish `h2 : A (e i) l = g l i` using `by simp [A]`.

Rewrite using `[← h2, h1, Matrix.mul_apply]`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply (M := P⁻¹)]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Simplify using `only [Λ, Matrix.of_apply, Equiv.apply_symm_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[SetLike.mem_coe, hgl]`. Use `Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hD j k]`.

Distinguish the cases in `hkj : (k : ℕ) = (j : ℕ)`. Establish `hj : ((e (e.symm j)) : ℕ) < m`. Rewrite using `[Equiv.apply_symm_apply, ← hkj]`. Conclude with `k.2`. Establish `hε : ε (e.symm j) = a j`.

Simplify using `only [ε, if_pos hj, Equiv.apply_symm_apply]`. Rewrite using `[if_pos hkj, mul_smul, ← hε]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨e.symm j, rfl⟩)`. Rewrite using `[if_neg hkj, mul_zero, zero_smul]`. Conclude with `Submodule.zero_mem _`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Use `show ε j • Λ j ∈ L`. Distinguish the cases in `hj : (e j : ℕ) < m`. Establish `hsum : ε j • Λ j = ∑ l : Fin m, Q l ⟨e j, hj⟩ • g l`.

Use extensionality with `i`. Establish `h1 : (A * Q) (e i) ⟨e j, hj⟩ = (P⁻¹ * (P * A * Q)) (e i) ⟨e j, hj⟩` using `by rw [← hAQ]`. Establish `h2 : (A * Q) (e i) ⟨e j, hj⟩ = ∑ l, Q l ⟨e j, hj⟩ * g l i`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Simplify using `[A, mul_comm]`. Establish `h3 : (P⁻¹ * (P * A * Q)) (e i) ⟨e j, hj⟩ = a (e j) * P⁻¹ (e i) (e j)`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (e j)]`. Rewrite using `[hD]`. Simplify using `[mul_comm]`.

Introduce `b _ hb`. Rewrite using `[hD, if_neg, mul_zero]`. Introduce `h`. Conclude with `hb (Fin.ext h.symm)`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[← h2, h1, h3]`. Simplify using `only [ε, if_pos hj, Λ, Matrix.of_apply]`. Rewrite using `[hsum, ← hg]`.

Conclude with `Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)`. Establish `: ε j = 0` using `if_neg hj`. Rewrite using `[this, zero_smul]`. Conclude with `Submodule.zero_mem _`.
-/
theorem exists_smith_basis (hv : v.Integers R) {ι : Type} [Fintype ι] [DecidableEq ι]
    (L : Submodule R (ι → R)) (hL : L.FG) :
    ∃ (Λ : Matrix ι ι R) (ε : ι → R), IsUnit Λ.det ∧
      L = Submodule.span R (Set.range fun j => ε j • Λ j) := by
  obtain ⟨m, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hL
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let A : Matrix (Fin (Fintype.card ι)) (Fin m) R := Matrix.of fun i k => g k (e.symm i)
  obtain ⟨P, Q, a, hP, hQ, hD⟩ := ReciprocityTheory.PGsh.Up.Smith.smith_mat hv _ m A
  have hPv : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hP
  have hQv : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv _ hQ
  have hAQ : A * Q = P⁻¹ * (P * A * Q) := by
    simp only [← Matrix.mul_assoc, hPv, Matrix.one_mul]
  have hA : A = P⁻¹ * (P * A * Q) * Q⁻¹ := by
    rw [← hAQ, Matrix.mul_assoc, hQv, Matrix.mul_one]
  let Λ : Matrix ι ι R := Matrix.of fun j i => P⁻¹ (e i) (e j)
  let ε : ι → R := fun j => if (e j : ℕ) < m then a (e j) else 0
  have hΛ : Λ = ((P⁻¹).submatrix e e)ᵀ := by
    ext j i; rfl
  have hdet : IsUnit Λ.det := by
    rw [hΛ, Matrix.det_transpose, Matrix.det_submatrix_equiv_self]
    exact (Matrix.isUnit_nonsing_inv_det_iff).2 hP
  refine ⟨Λ, ε, hdet, le_antisymm ?_ ?_⟩
  · rw [← hg, Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    have hgl : g l = ∑ k : Fin m, ∑ j : Fin (Fintype.card ι),
        (Q⁻¹ k l * (P * A * Q) j k) • Λ (e.symm j) := by
      ext i
      have h1 : A (e i) l = (P⁻¹ * (P * A * Q) * Q⁻¹) (e i) l := by rw [← hA]
      have h2 : A (e i) l = g l i := by simp [A]
      rw [← h2, h1, Matrix.mul_apply]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply (M := P⁻¹)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Λ, Matrix.of_apply, Equiv.apply_symm_apply]
      ring
    rw [SetLike.mem_coe, hgl]
    refine Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun j _ => ?_
    rw [hD j k]
    by_cases hkj : (k : ℕ) = (j : ℕ)
    · have hj : ((e (e.symm j)) : ℕ) < m := by
        rw [Equiv.apply_symm_apply, ← hkj]; exact k.2
      have hε : ε (e.symm j) = a j := by
        simp only [ε, if_pos hj, Equiv.apply_symm_apply]
      rw [if_pos hkj, mul_smul, ← hε]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e.symm j, rfl⟩)
    · rw [if_neg hkj, mul_zero, zero_smul]
      exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    show ε j • Λ j ∈ L
    by_cases hj : (e j : ℕ) < m
    · have hsum : ε j • Λ j = ∑ l : Fin m, Q l ⟨e j, hj⟩ • g l := by
        ext i
        have h1 : (A * Q) (e i) ⟨e j, hj⟩ = (P⁻¹ * (P * A * Q)) (e i) ⟨e j, hj⟩ := by rw [← hAQ]
        have h2 : (A * Q) (e i) ⟨e j, hj⟩ = ∑ l, Q l ⟨e j, hj⟩ * g l i := by
          rw [Matrix.mul_apply]
          refine Finset.sum_congr rfl fun l _ => ?_
          simp [A, mul_comm]
        have h3 : (P⁻¹ * (P * A * Q)) (e i) ⟨e j, hj⟩ = a (e j) * P⁻¹ (e i) (e j) := by
          rw [Matrix.mul_apply, Finset.sum_eq_single (e j)]
          · rw [hD]; simp [mul_comm]
          · intro b _ hb
            rw [hD, if_neg, mul_zero]
            intro h
            exact hb (Fin.ext h.symm)
          · intro h; exact absurd (Finset.mem_univ _) h
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rw [← h2, h1, h3]
        simp only [ε, if_pos hj, Λ, Matrix.of_apply]
      rw [hsum, ← hg]
      exact Submodule.sum_mem _ fun l _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
    · have : ε j = 0 := if_neg hj
      rw [this, zero_smul]
      exact Submodule.zero_mem _

noncomputable def rowEquiv {ι : Type} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι R) (h : IsUnit Λ.det) :
    (ι → R) ≃ₗ[R] (ι → R) :=
  LinearEquiv.ofLinear (Matrix.vecMulLinear Λ) (Matrix.vecMulLinear Λ⁻¹)
    (LinearMap.ext fun x => by
      simp [Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ h])
    (LinearMap.ext fun x => by
      simp [Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ h])

/- English proof (translation)
Use `show x ᵥ* Λ = _`. Rewrite using `[Matrix.vecMul_eq_sum]`.
-/
theorem rowEquiv_apply {ι : Type} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι R)
    (h : IsUnit Λ.det) (x : ι → R) : rowEquiv Λ h x = ∑ j, x j • Λ j := by
  show x ᵥ* Λ = _
  rw [Matrix.vecMul_eq_sum]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.map_le_iff_le_comap]`. Introduce `x hx`. Rewrite using `[Submodule.mem_comap]`. Use `show rowEquiv Λ h x ∈ _`.

Rewrite using `[rowEquiv_apply]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Take `⟨r, hr⟩` from `Ideal.mem_span_singleton'.1 (hx j (Set.mem_univ j))`. Rewrite using `[← hr, mul_smul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Use `⟨Pi.single j (ε j), ?_, ?_⟩` and prove the remaining obligations. Introduce `k _`. Distinguish the cases in `hk : k = j`.

Substitute `hk` using the available equality. Simplify using `using Ideal.mem_span_singleton_self (ε k)`. Simplify using `[Pi.single_eq_of_ne hk]`. Use `show rowEquiv Λ h _ = _`. Rewrite using `[rowEquiv_apply, Finset.sum_eq_single j]`.

Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Pi.single_eq_of_ne hb]`. Introduce `hj`. Conclude with `absurd (Finset.mem_univ _) hj`.
-/
theorem map_rowEquiv {ι : Type} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι R)
    (h : IsUnit Λ.det) (ε : ι → R) :
    (Submodule.pi Set.univ fun j => (Ideal.span {ε j} : Submodule R R)).map
        (rowEquiv Λ h : (ι → R) →ₗ[R] (ι → R)) =
      Submodule.span R (Set.range fun j => ε j • Λ j) := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    intro x hx
    rw [Submodule.mem_comap]
    show rowEquiv Λ h x ∈ _
    rw [rowEquiv_apply]
    refine Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 (hx j (Set.mem_univ j))
    rw [← hr, mul_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine ⟨Pi.single j (ε j), ?_, ?_⟩
    · intro k _
      by_cases hk : k = j
      · subst hk
        simpa using Ideal.mem_span_singleton_self (ε k)
      · simp [Pi.single_eq_of_ne hk]
    · show rowEquiv Λ h _ = _
      rw [rowEquiv_apply, Finset.sum_eq_single j]
      · simp
      · intro b _ hb; simp [Pi.single_eq_of_ne hb]
      · intro hj; exact absurd (Finset.mem_univ _) hj

/- English proof (translation)
Rewrite `hc` using `[← map_rowEquiv Λ h ε]`. Take `⟨x, hx, hxe⟩` from `hc`. Establish `hx' : x = Pi.single j c`. Apply `(rowEquiv Λ h).injective` to reduce the goal to its premises. Establish `: rowEquiv Λ h x = c • Λ j` using `hxe`.

Rewrite using `[this, rowEquiv_apply, Finset.sum_eq_single j]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Pi.single_eq_of_ne hb]`. Introduce `hj`.

Conclude with `absurd (Finset.mem_univ _) hj`. Use `hx j (Set.mem_univ j)` as an intermediate fact. Rewrite `this` using `[hx', Pi.single_eq_same]`. Conclude with `Ideal.mem_span_singleton.1 this`.
-/
theorem dvd_of_smul_row_mem {ι : Type} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι R)
    (h : IsUnit Λ.det) (ε : ι → R) (c : R) (j : ι)
    (hc : c • Λ j ∈ Submodule.span R (Set.range fun j => ε j • Λ j)) : ε j ∣ c := by
  rw [← map_rowEquiv Λ h ε] at hc
  obtain ⟨x, hx, hxe⟩ := hc
  have hx' : x = Pi.single j c := by
    apply (rowEquiv Λ h).injective
    have : rowEquiv Λ h x = c • Λ j := hxe
    rw [this, rowEquiv_apply, Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · intro hj; exact absurd (Finset.mem_univ _) hj
  have := hx j (Set.mem_univ j)
  rw [hx', Pi.single_eq_same] at this
  exact Ideal.mem_span_singleton.1 this

/- English proof (translation)
Set `e : ι ≃ Fin (Fintype.card ι)` to `Fintype.equivFin ι`. Set `T : Submodule R (ι → R)` to `Submodule.pi Set.univ fun j => (Ideal.span {ε j} : Submodule R R)`. Establish `E1 : ((ι → R) ⧸ T) ≃ₗ[R] ((ι → R) ⧸ Submodule.span R (Set.range fun j => ε j • Λ j))` using `Submodule.Quotient.equiv T _ (rowEquiv Λ h) (map_rowEquiv Λ h ε)`. Establish `E2 : ((ι → R) ⧸ T) ≃ₗ[R] ((j : ι) → R ⧸ Ideal.span {ε j})` using `Submodule.quotientPi fun j => (Ideal.span {ε j} : Submodule R R)`. Establish `E3` using `LinearEquiv.piCongrLeft R (fun j : ι => R ⧸ Ideal.span {ε j}) e.symm`.

Use `⟨Fintype.card ι, fun i => ε (e.symm i), ⟨((E.trans E1.symm).trans E2).trans E3.symm⟩, ?_⟩` and prove the remaining obligations. Conclude with `Equiv.prod_comp e.symm fun j => v (algebraMap R C (ε j))`.
-/
theorem hasLen_quot_rows {ι : Type} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι R)
    (h : IsUnit Λ.det) (ε : ι → R) {M : Type} [AddCommGroup M] [Module R M]
    (E : M ≃ₗ[R] ((ι → R) ⧸ Submodule.span R (Set.range fun j => ε j • Λ j))) :
    HasLen v R M (∏ j, v (algebraMap R C (ε j))) := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let T : Submodule R (ι → R) := Submodule.pi Set.univ fun j => (Ideal.span {ε j} : Submodule R R)
  have E1 : ((ι → R) ⧸ T) ≃ₗ[R] ((ι → R) ⧸ Submodule.span R (Set.range fun j => ε j • Λ j)) :=
    Submodule.Quotient.equiv T _ (rowEquiv Λ h) (map_rowEquiv Λ h ε)
  have E2 : ((ι → R) ⧸ T) ≃ₗ[R] ((j : ι) → R ⧸ Ideal.span {ε j}) :=
    Submodule.quotientPi fun j => (Ideal.span {ε j} : Submodule R R)
  have E3 := LinearEquiv.piCongrLeft R (fun j : ι => R ⧸ Ideal.span {ε j}) e.symm
  refine ⟨Fintype.card ι, fun i => ε (e.symm i), ⟨((E.trans E1.symm).trans E2).trans E3.symm⟩, ?_⟩
  exact Equiv.prod_comp e.symm fun j => v (algebraMap R C (ε j))

end lattice

/- English proof (translation)
Introduce `p _ C _ _ _ v R _ _ hv hp ι _ _ AA`. Establish `hp1 : p - 1 ≠ 0`. Use `(Fact.out : p.Prime).two_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨-, -, cp, hcp, -, -⟩` from `cpaf p C v R hv hp (ι → ZMod p) AA 0`.

Establish `hcoord : ∀ i, (Pi.single i cp : ι → R) ∈ afLat p AA.carrier`. Introduce `i`. Take `⟨g, hg, c, hc, -, h⟩` from `cpaf p C v R hv hp (ι → ZMod p) AA (Pi.evalAddMonoidHom _ i)`. Establish `hvc : v (algebraMap R C cp) = v (algebraMap R C c)` using `(pow_left_inj₀ zero_le zero_le hp1).1 (hcp.trans hc.symm)`. Take `⟨u, hu⟩ : c ∣ cp` from `hv.dvd_of_le hvc.le`.

Establish `hmem : (Pi.single i c : ι → R) ∈ afLat p AA.carrier`. Use `⟨g, (Submodule.mem_inf.1 hg).1, fun x => ?_⟩` and prove the remaining obligations. Establish `hs : ∑ k, (Pi.single i c : ι → R) k * ((x k).val : R) = c * ((x i).val : R)`. Rewrite using `[Finset.sum_eq_single i]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Simplify using `[Pi.single_eq_of_ne hb]`. Introduce `hi`. Conclude with `absurd (Finset.mem_univ _) hi`. Rewrite using `[hs, map_mul, map_natCast]`.

Conclude with `(h x).1`. Establish `: (Pi.single i cp : ι → R) = u • (Pi.single i c : ι → R)`. Use extensionality with `k`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality.

Simplify using `[hu, mul_comm]`. Simplify using `[Pi.single_eq_of_ne hk]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hmem`. Establish `hscale : ∀ l : ι → R, cp • l ∈ afLat p AA.carrier`.

Introduce `l`. Establish `: cp • l = ∑ i, l i • (Pi.single i cp : ι → R)`. Use extensionality with `k`. Simplify using `[Finset.sum_apply, Pi.single_apply, mul_comm]`. Rewrite using `[this]`.

Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hcoord i)`. Take `⟨Λ, ε, hdet, hL⟩` from `exists_smith_basis hv _ (hfg p C v R hv hp ι AA)`. Use `⟨Λ, ε, hdet, hL, fun j => ?_, ?_⟩` and prove the remaining obligations. Establish `hd : ε j ∣ cp` using `dvd_of_smul_row_mem Λ hdet ε cp j (hL ▸ hscale (Λ j))`. Take `⟨t, ht⟩` from `hd`.

Establish `hle : v (algebraMap R C cp) ≤ v (algebraMap R C (ε j))`. Rewrite using `[ht, map_mul, map_mul]`. Conclude with `mul_le_of_le_one_right' (hv.map_le_one t)`. Rewrite using `[← hcp]`. Conclude with `pow_le_pow_left₀ zero_le hle _`.

Take `⟨E⟩` from `hquot p C v R hv hp ι AA`. Conclude with `hasLen_quot_rows Λ hdet ε (E.trans (Submodule.quotEquivOfEq _ _ hL))`.
-/
theorem smith_of (hfg : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), (afLat p AA.carrier).FG)
    (hquot : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), Nonempty (AFQuot p AA.carrier ≃ₗ[R] ((ι → R) ⧸ afLat p AA.carrier))) :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), ∃ (Λ : Matrix ι ι R) (ε : ι → R), IsUnit Λ.det ∧ afLat p AA.carrier = Submodule.span R (Set.range fun j => ε j • Λ j) ∧ (∀ j, v (p : C) ≤ v (algebraMap R C (ε j)) ^ (p - 1)) ∧ HasLen v R (AFQuot p AA.carrier) (∏ j, v (algebraMap R C (ε j))) := by
  intro p _ C _ _ _ v R _ _ hv hp ι _ _ AA
  have hp1 : p - 1 ≠ 0 := by
    have := (Fact.out : p.Prime).two_le
    omega
  obtain ⟨-, -, cp, hcp, -, -⟩ := cpaf p C v R hv hp (ι → ZMod p) AA 0
  have hcoord : ∀ i, (Pi.single i cp : ι → R) ∈ afLat p AA.carrier := by
    intro i
    obtain ⟨g, hg, c, hc, -, h⟩ :=
      cpaf p C v R hv hp (ι → ZMod p) AA (Pi.evalAddMonoidHom _ i)
    have hvc : v (algebraMap R C cp) = v (algebraMap R C c) :=
      (pow_left_inj₀ zero_le zero_le hp1).1 (hcp.trans hc.symm)
    obtain ⟨u, hu⟩ : c ∣ cp := hv.dvd_of_le hvc.le
    have hmem : (Pi.single i c : ι → R) ∈ afLat p AA.carrier := by
      refine ⟨g, (Submodule.mem_inf.1 hg).1, fun x => ?_⟩
      have hs : ∑ k, (Pi.single i c : ι → R) k * ((x k).val : R) = c * ((x i).val : R) := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro b _ hb; simp [Pi.single_eq_of_ne hb]
        · intro hi; exact absurd (Finset.mem_univ _) hi
      rw [hs, map_mul, map_natCast]
      exact (h x).1
    have : (Pi.single i cp : ι → R) = u • (Pi.single i c : ι → R) := by
      ext k
      by_cases hk : k = i
      · subst hk; simp [hu, mul_comm]
      · simp [Pi.single_eq_of_ne hk]
    rw [this]
    exact Submodule.smul_mem _ _ hmem
  have hscale : ∀ l : ι → R, cp • l ∈ afLat p AA.carrier := by
    intro l
    have : cp • l = ∑ i, l i • (Pi.single i cp : ι → R) := by
      ext k
      simp [Finset.sum_apply, Pi.single_apply, mul_comm]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hcoord i)
  obtain ⟨Λ, ε, hdet, hL⟩ := exists_smith_basis hv _ (hfg p C v R hv hp ι AA)
  refine ⟨Λ, ε, hdet, hL, fun j => ?_, ?_⟩
  · have hd : ε j ∣ cp := dvd_of_smul_row_mem Λ hdet ε cp j (hL ▸ hscale (Λ j))
    obtain ⟨t, ht⟩ := hd
    have hle : v (algebraMap R C cp) ≤ v (algebraMap R C (ε j)) := by
      rw [ht, map_mul, map_mul]
      exact mul_le_of_le_one_right' (hv.map_le_one t)
    rw [← hcp]
    exact pow_le_pow_left₀ zero_le hle _
  · obtain ⟨E⟩ := hquot p C v R hv hp ι AA
    exact hasLen_quot_rows Λ hdet ε (E.trans (Submodule.quotEquivOfEq _ _ hL))

end PositivityTheory.HtPt.Ra
