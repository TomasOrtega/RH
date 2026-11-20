import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

open MvPowerSeries in

/- English proof (translation)
Establish `h : ⁅MvPolynomial.pderiv (R` using `k) i, MvPolynomial.pderiv (R := k) j⁆ = 0 := by`. Apply `MvPolynomial.derivation_ext` to reduce the goal to its premises. Introduce `n`. Rewrite using `[Derivation.commutator_apply, MvPolynomial.pderiv_X, MvPolynomial.pderiv_X]`. Apply the tactic sequence `by_cases hj : j = n <;> by_cases hi : i = n <;>`.

Simplify using `[Pi.single_apply, hj, hi]`. Use `DFunLike.congr_fun h p` as an intermediate fact. Rewrite `this` using `[Derivation.commutator_apply]`. Simplify `this` using `[sub_eq_zero]`.
-/
theorem _root_.GlobalTheory.minorHarm_pderiv_comm {σ k : Type*} [CommRing k] (i j : σ)
    (p : MvPolynomial σ k) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
  classical
  have h : ⁅MvPolynomial.pderiv (R := k) i, MvPolynomial.pderiv (R := k) j⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro n
    rw [Derivation.commutator_apply, MvPolynomial.pderiv_X, MvPolynomial.pderiv_X]
    by_cases hj : j = n <;> by_cases hi : i = n <;>
      simp [Pi.single_apply, hj, hi]
  have := DFunLike.congr_fun h p
  rw [Derivation.commutator_apply] at this
  simpa [sub_eq_zero] using this

open MvPowerSeries in

/- English proof (translation)
Rewrite `hp` using `[MvPolynomial.supported_eq_adjoin_X]`. Proceed by induction on `hp using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨s, hs, rfl⟩` from `hx`. Conclude with `MvPolynomial.pderiv_X_of_ne (fun h => hv (h ▸ hs))`.

Consider the case `algebraMap r => rw [MvPolynomial.algebraMap_eq, MvPolynomial.pderiv_C]`. Consider the case `add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]`. Consider the case `mul x y _ _ hx hy => rw [MvPolynomial.pderiv_mul, hx, hy]`. Simplify using the standard rewrite rules.
-/
theorem _root_.GlobalTheory.minorHarm_pderiv_eq_zero {σ k : Type*} [CommRing k] {S : Set σ}
    {p : MvPolynomial σ k} (hp : p ∈ MvPolynomial.supported k S) {v : σ} (hv : v ∉ S) :
    MvPolynomial.pderiv v p = 0 := by
  classical
  rw [MvPolynomial.supported_eq_adjoin_X] at hp
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    exact MvPolynomial.pderiv_X_of_ne (fun h => hv (h ▸ hs))
  | algebraMap r => rw [MvPolynomial.algebraMap_eq, MvPolynomial.pderiv_C]
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | mul x y _ _ hx hy => rw [MvPolynomial.pderiv_mul, hx, hy]; simp

open MvPowerSeries in
/- English proof (translation)
Rewrite `hp`, the goal using `[MvPolynomial.supported_eq_adjoin_X]`. Proceed by induction on `hp using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨s, hs, rfl⟩` from `hx`. Rewrite using `[MvPolynomial.pderiv_X]`.

Distinguish the cases in `h : w = s`. Substitute `h` using the available equality. Simplify using `only [Pi.single_eq_same]`. Conclude with `Subalgebra.one_mem _`. Rewrite using `[Pi.single_eq_of_ne' h]`.

Conclude with `Subalgebra.zero_mem _`. Consider the case `algebraMap r`. Rewrite using `[MvPolynomial.algebraMap_eq, MvPolynomial.pderiv_C]`. Conclude with `Subalgebra.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`.

Conclude with `Subalgebra.add_mem _ hx hy`. Consider the case `mul x y hx' hy' hx hy`. Rewrite using `[MvPolynomial.pderiv_mul]`. Conclude with `Subalgebra.add_mem _ (Subalgebra.mul_mem _ hx hy') (Subalgebra.mul_mem _ hx' hy)`.
-/
private theorem pderiv_mem_supported' {σ k : Type*} [CommRing k] {S : Set σ}
    {p : MvPolynomial σ k} (hp : p ∈ MvPolynomial.supported k S) (w : σ) :
    MvPolynomial.pderiv w p ∈ MvPolynomial.supported k S := by
  classical
  rw [MvPolynomial.supported_eq_adjoin_X] at hp ⊢
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    rw [MvPolynomial.pderiv_X]
    by_cases h : w = s
    · subst h; simp only [Pi.single_eq_same]; exact Subalgebra.one_mem _
    · rw [Pi.single_eq_of_ne' h]; exact Subalgebra.zero_mem _
  | algebraMap r =>
    rw [MvPolynomial.algebraMap_eq, MvPolynomial.pderiv_C]; exact Subalgebra.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Subalgebra.add_mem _ hx hy
  | mul x y hx' hy' hx hy =>
    rw [MvPolynomial.pderiv_mul]
    exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ hx hy') (Subalgebra.mul_mem _ hx' hy)

open MvPowerSeries in

/- English proof (translation)
Introduce `k _ T _ _ r n col m P hP τ τ' hdisj i i'`. Set `S : Set ((Σ τ : T, Fin (r τ)) × Fin n)` to `{x | ∃ c, col x.1.1 c = x.2}`. Establish `hPS : P ∈ MvPolynomial.supported k S`. Rewrite using `[hP]`. Use `Subalgebra.prod_mem _ fun σ _ => Subalgebra.prod_mem _ fun s _ => ?_` and prove the remaining obligations.

Use `Subalgebra.pow_mem _ ?_ _` and prove the remaining obligations. Rewrite using `[Matrix.det_apply]`. Use `Subalgebra.sum_mem _ fun π _ => ?_` and prove the remaining obligations. Rewrite using `[Units.smul_def]`. Use `Subalgebra.zsmul_mem _ (Subalgebra.prod_mem _ fun a _ => ?_) _` and prove the remaining obligations.

Rewrite using `[Matrix.of_apply, MvPolynomial.supported_eq_adjoin_X]`. Conclude with `Algebra.subset_adjoin ⟨_, ⟨_, rfl⟩, rfl⟩`. Use `Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations. Distinguish the cases in `hb : ∃ c, col τ c = b`. Take `⟨c, rfl⟩` from `hb`.

Establish `hnot : ((⟨τ', i'⟩ : Σ τ : T, Fin (r τ)), col τ c) ∉ S`. Introduce and unpack `⟨c', hc'⟩`. Conclude with `hdisj c c' hc'.symm`. Rewrite using `[_root_.GlobalTheory.minorHarm_pderiv_eq_zero hPS hnot, map_zero]`. Establish `hnot : ((⟨τ, i⟩ : Σ τ : T, Fin (r τ)), b) ∉ S` using `hb`.

Conclude with `_root_.GlobalTheory.minorHarm_pderiv_eq_zero (pderiv_mem_supported' hPS _) hnot`.
-/
theorem _root_.GlobalTheory.minors_disjoint_columns_harmonic :
    ∀ (k : Type) [CommRing k] (T : Type) [Fintype T] [DecidableEq T] (r : T → ℕ) (n : ℕ) (col : ∀ τ, Fin (r τ) → Fin n) (m : ∀ τ, Fin (r τ) → ℕ) (P : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k), P = (∏ τ, ∏ s : Fin (r τ), (Matrix.of fun a i : Fin (s.val + 1) => (MvPolynomial.X ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)), col τ (Fin.castLE s.isLt i)) : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k)).det ^ m τ s) → ∀ τ τ' : T, (∀ i i', col τ i ≠ col τ' i') → ∀ (i : Fin (r τ)) (i' : Fin (r τ')), ∑ b : Fin n, MvPolynomial.pderiv ((⟨τ, i⟩ : Σ τ : T, Fin (r τ)), b) (MvPolynomial.pderiv ((⟨τ', i'⟩ : Σ τ : T, Fin (r τ)), b) P) = 0 := by
  intro k _ T _ _ r n col m P hP τ τ' hdisj i i'
  let S : Set ((Σ τ : T, Fin (r τ)) × Fin n) := {x | ∃ c, col x.1.1 c = x.2}
  have hPS : P ∈ MvPolynomial.supported k S := by
    rw [hP]
    refine Subalgebra.prod_mem _ fun σ _ => Subalgebra.prod_mem _ fun s _ => ?_
    refine Subalgebra.pow_mem _ ?_ _
    rw [Matrix.det_apply]
    refine Subalgebra.sum_mem _ fun π _ => ?_
    rw [Units.smul_def]
    refine Subalgebra.zsmul_mem _ (Subalgebra.prod_mem _ fun a _ => ?_) _
    rw [Matrix.of_apply, MvPolynomial.supported_eq_adjoin_X]
    exact Algebra.subset_adjoin ⟨_, ⟨_, rfl⟩, rfl⟩
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases hb : ∃ c, col τ c = b
  · obtain ⟨c, rfl⟩ := hb
    have hnot : ((⟨τ', i'⟩ : Σ τ : T, Fin (r τ)), col τ c) ∉ S := by
      rintro ⟨c', hc'⟩
      exact hdisj c c' hc'.symm
    rw [_root_.GlobalTheory.minorHarm_pderiv_eq_zero hPS hnot, map_zero]
  · have hnot : ((⟨τ, i⟩ : Σ τ : T, Fin (r τ)), b) ∉ S := hb
    exact _root_.GlobalTheory.minorHarm_pderiv_eq_zero
      (pderiv_mem_supported' hPS _) hnot

end GlobalTheory
