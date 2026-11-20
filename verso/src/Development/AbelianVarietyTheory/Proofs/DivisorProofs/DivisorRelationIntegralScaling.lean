import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O
open scoped TensorProduct

/- English proof (translation)
Introduce `D A N j S κ s Φ hm h0 P k`. Use `set n : ℕ := ((P.ab k).n : ℕ) with hn`. Establish `hnpos : 0 < n` using `(P.ab k).n.pos`. Establish `hn0 : (n : ℚ) ≠ 0` using `Nat.cast_ne_zero.2 hnpos.ne'`. Use `set Dn : ℕ := ∏ x : DV.Rt D.what₂.Tau N, (P.dirQ x.1 x.2).den with hDn`.

Establish `hDpos : 0 < Dn` using `Finset.prod_pos fun _ _ => Rat.den_pos _`. Establish `hc : ∀ x : DV.Rt D.what₂.Tau N, ∃ c : ℤ, (c : ℚ) = (Dn : ℚ) * P.dirQ x.1 x.2`. Introduce `x`. Take `⟨e, he⟩ : (P.dirQ x.1 x.2).den ∣ Dn` from `Finset.dvd_prod_of_mem _ (Finset.mem_univ x)`. Use `⟨e * (P.dirQ x.1 x.2).num, ?_⟩` and prove the remaining obligations.

Rewrite using `[he, Nat.cast_mul, mul_comm ((P.dirQ x.1 x.2).den : ℚ), mul_assoc, Rat.den_mul_eq_num]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `choose c hc using hc`. Use `set X : (Φ.C k).Y.Dv := (Dn : ℤ) • (P.ab k).D + ∑ x, ((n : ℤ) * c x) • divOf (Φ.C k) (rootExp S x) + ((n * Dn : ℕ) : ℤ) • P.bd k with hX`.

Establish `key : ∀ (z : ℤ) (v : (Φ.C k).Y.Dv), (1:ℚ) ⊗ₜ[ℤ] (z • v) = (z : ℚ) ⊗ₜ v`. Introduce `z v`. Rewrite using `[← TensorProduct.smul_tmul, zsmul_eq_mul, mul_one]`. Establish `h1 : (1 : ℚ) ⊗ₜ[ℤ] X = 1 ⊗ₜ 0`. Establish `h` using `P.qDiv_ab k`.

Establish `e1 : ((Dn : ℤ) : ℚ) ⊗ₜ[ℤ] (P.ab k).D = ((n * Dn : ℕ) : ℚ) • qDiv (P.ab k)`. Rewrite using `[qDiv, TensorProduct.smul_tmul', smul_eq_mul, ← hn]`. Use `congr 1`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Establish `e2 : ∀ x, (((n : ℤ) * c x : ℤ) : ℚ) ⊗ₜ[ℤ] divOf (Φ.C k) (rootExp S x) = ((n * Dn : ℕ) : ℚ) • (P.dirQ x.1 x.2 ⊗ₜ[ℤ] divOf (Φ.C k) (rootExp S x))`. Introduce `x`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul]`. Use `congr 1`. Use `push_cast`.

Rewrite using `[hc x]`. Expand and normalize the polynomial expressions, which then agree. Establish `e3 : (((n * Dn : ℕ) : ℤ) : ℚ) ⊗ₜ[ℤ] P.bd k = ((n * Dn : ℕ) : ℚ) • ((1:ℚ) ⊗ₜ[ℤ] P.bd k)`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Use `push_cast`.

Both sides reduce to the same expression. Rewrite using `[TensorProduct.tmul_zero, hX, TensorProduct.tmul_add, TensorProduct.tmul_add, TensorProduct.tmul_sum, key, key]`. Simplify using `only [key]`. Rewrite using `[e1, e3]`. Simplify using `only [e2]`.

Rewrite using `[← Finset.smul_sum, ← smul_add, ← smul_add, h]`. Establish `: qL Φ k P.dirQ - 1 ⊗ₜ P.bd k + ∑ x, P.dirQ x.1 x.2 ⊗ₜ[ℤ] divOf (Φ.C k) (rootExp S x) + (1:ℚ) ⊗ₜ[ℤ] P.bd k = 0` using `by rw [qL]; abel`. Rewrite using `[this, smul_zero]`. Take `⟨q, hq, hqX⟩` from `one_tmul_eq_iff.1 h1`. Establish `hqX' : (q : ℤ) • X = 0` using `by rw [natCast_zsmul]; simpa using hqX`.

Use `⟨q * (n * Dn), ((q * (n * Dn) : ℕ) : ℤ), (q : ℤ) * Dn, fun x => (q : ℤ) * ((n : ℤ) * c x), Nat.mul_pos hq (Nat.mul_pos hnpos hDpos), by push_cast; rfl, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `: (n : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 hnpos.ne' push_cast`. Clear the denominators using the available nonvanishing facts. Introduce `x`. Use `congrArg (Rat.cast : ℚ → ℝ) (hc x)` as an intermediate fact.

Move the coercions through the operations in `at this`. Rewrite using `[show P.dir x.1 x.2 = ((P.dirQ x.1 x.2 : ℚ) : ℝ) from rfl]`. Use `push_cast`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← hqX', hX, smul_add, smul_add, Finset.smul_sum]`. Simplify using `only [smul_smul]`. Use `push_cast`. Normalize the expressions using the abelian group laws.
-/
theorem GlobalTheory.ShFam.PolDat.exists_intRel_bd_ab_roots : ∀ {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ}
    {Φ : s.Flag} {hm : ∀ k, Mets (Φ.C k) (cxSt D.what₂.LL)} {h0 : RefMets Φ} (P : PolDat s Φ hm h0) (k : s.Comp),
    ∃ (d : ℕ) (kb ka : ℤ) (kx : DV.Rt D.what₂.Tau N → ℤ), 0 < d ∧ (kb : ℝ) = d ∧
      (ka : ℝ) = d * (((P.ab k).n : ℕ) : ℝ)⁻¹ ∧ (∀ x, (kx x : ℝ) = d * P.dir x.1 x.2) ∧
      kb • P.bd k + ka • (P.ab k).D + ∑ x, kx x • divOf (Φ.C k) (rootExp S x) = 0 := by
  intro D A N j S κ s Φ hm h0 P k
  classical
  set n : ℕ := ((P.ab k).n : ℕ) with hn
  have hnpos : 0 < n := (P.ab k).n.pos
  have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hnpos.ne'
  set Dn : ℕ := ∏ x : DV.Rt D.what₂.Tau N, (P.dirQ x.1 x.2).den with hDn
  have hDpos : 0 < Dn := Finset.prod_pos fun _ _ => Rat.den_pos _
  have hc : ∀ x : DV.Rt D.what₂.Tau N, ∃ c : ℤ, (c : ℚ) = (Dn : ℚ) * P.dirQ x.1 x.2 := by
    intro x
    obtain ⟨e, he⟩ : (P.dirQ x.1 x.2).den ∣ Dn := Finset.dvd_prod_of_mem _ (Finset.mem_univ x)
    refine ⟨e * (P.dirQ x.1 x.2).num, ?_⟩
    rw [he, Nat.cast_mul, mul_comm ((P.dirQ x.1 x.2).den : ℚ), mul_assoc, Rat.den_mul_eq_num]
    push_cast; ring
  choose c hc using hc
  set X : (Φ.C k).Y.Dv := (Dn : ℤ) • (P.ab k).D + ∑ x, ((n : ℤ) * c x) • divOf (Φ.C k) (rootExp S x) +
    ((n * Dn : ℕ) : ℤ) • P.bd k with hX
  have key : ∀ (z : ℤ) (v : (Φ.C k).Y.Dv), (1:ℚ) ⊗ₜ[ℤ] (z • v) = (z : ℚ) ⊗ₜ v := by
    intro z v; rw [← TensorProduct.smul_tmul, zsmul_eq_mul, mul_one]
  have h1 : (1 : ℚ) ⊗ₜ[ℤ] X = 1 ⊗ₜ 0 := by
    have h := P.qDiv_ab k
    have e1 : ((Dn : ℤ) : ℚ) ⊗ₜ[ℤ] (P.ab k).D = ((n * Dn : ℕ) : ℚ) • qDiv (P.ab k) := by
      rw [qDiv, TensorProduct.smul_tmul', smul_eq_mul, ← hn]; congr 1; push_cast; field_simp
    have e2 : ∀ x, (((n : ℤ) * c x : ℤ) : ℚ) ⊗ₜ[ℤ] divOf (Φ.C k) (rootExp S x) =
        ((n * Dn : ℕ) : ℚ) • (P.dirQ x.1 x.2 ⊗ₜ[ℤ] divOf (Φ.C k) (rootExp S x)) := by
      intro x; rw [TensorProduct.smul_tmul', smul_eq_mul]; congr 1; push_cast; rw [hc x]; ring
    have e3 : (((n * Dn : ℕ) : ℤ) : ℚ) ⊗ₜ[ℤ] P.bd k = ((n * Dn : ℕ) : ℚ) • ((1:ℚ) ⊗ₜ[ℤ] P.bd k) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]; push_cast; rfl
    rw [TensorProduct.tmul_zero, hX, TensorProduct.tmul_add, TensorProduct.tmul_add, TensorProduct.tmul_sum, key, key]
    simp only [key]
    rw [e1, e3]; simp only [e2]
    rw [← Finset.smul_sum, ← smul_add, ← smul_add, h]
    have : qL Φ k P.dirQ - 1 ⊗ₜ P.bd k + ∑ x, P.dirQ x.1 x.2 ⊗ₜ[ℤ] divOf (Φ.C k) (rootExp S x) +
        (1:ℚ) ⊗ₜ[ℤ] P.bd k = 0 := by rw [qL]; abel
    rw [this, smul_zero]
  obtain ⟨q, hq, hqX⟩ := one_tmul_eq_iff.1 h1
  have hqX' : (q : ℤ) • X = 0 := by rw [natCast_zsmul]; simpa using hqX
  refine ⟨q * (n * Dn), ((q * (n * Dn) : ℕ) : ℤ), (q : ℤ) * Dn, fun x => (q : ℤ) * ((n : ℤ) * c x),
    Nat.mul_pos hq (Nat.mul_pos hnpos hDpos), by push_cast; rfl, ?_, ?_, ?_⟩
  · have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hnpos.ne'
    push_cast; field_simp
  · intro x
    have := congrArg (Rat.cast : ℚ → ℝ) (hc x)
    push_cast at this
    rw [show P.dir x.1 x.2 = ((P.dirQ x.1 x.2 : ℚ) : ℝ) from rfl]
    push_cast; rw [this]; ring
  · rw [← hqX', hX, smul_add, smul_add, Finset.smul_sum]
    simp only [smul_smul]
    push_cast
    abel
