import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfAdicTopologicalBasisOverBreuilKisinStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscCoefficientsTopologicallyFreeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBoundedOfPhiEquationDiscStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeedCoeffRecurrenceStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP

/- English proof (translation)
Rewrite using `[← bk.ev_frob, frobS_X, map_pow]`.
-/
theorem frobenius_ev_X_eq {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) :
    WittVector.frobenius (bk.ev X) = bk.ev X ^ l := by
  rw [← bk.ev_frob, frobS_X, map_pow]

/- English proof (translation)
The claim follows from `NNReal.rpow_pos (Nat.cast_pos.2 hl.out.pos)`.
-/
theorem BK.ρ₀_pos' {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) : 0 < bk.ρ₀ :=
  NNReal.rpow_pos (Nat.cast_pos.2 hl.out.pos)

/- English proof (translation)
The claim follows from `NNReal.rpow_lt_one_of_one_lt_of_neg (Nat.one_lt_cast.2 hl.out.one_lt) (neg_neg_of_pos (one_div_pos.2 (Nat.cast_pos.2 bk.deg_pos)))`.
-/
theorem BK.ρ₀_lt_one' {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) : bk.ρ₀ < 1 :=
  NNReal.rpow_lt_one_of_one_lt_of_neg (Nat.one_lt_cast.2 hl.out.one_lt)
    (neg_neg_of_pos (one_div_pos.2 (Nat.cast_pos.2 bk.deg_pos)))

/- English proof (translation)
Introduce `U hU`. Establish `hs : ∀ a, ((fun i => f (i, a)) ⁻¹' U)ᶜ.Finite` using `fun a => h a hU`. Rewrite using `[Filter.mem_map, Filter.mem_cofinite]`. Use `(Set.finite_iUnion fun a => (hs a).image (fun i => (i, a))).subset ?_` and prove the remaining obligations. Introduce and unpack `⟨i, a⟩ hia`.

Conclude with `Set.mem_iUnion.2 ⟨a, i, hia, rfl⟩`.
-/
theorem tendsto_cofinite_prod_of_finite {ι α E : Type} [Finite α] [TopologicalSpace E] {x : E}
    (f : ι × α → E) (h : ∀ a, Filter.Tendsto (fun i => f (i, a)) Filter.cofinite (nhds x)) :
    Filter.Tendsto f Filter.cofinite (nhds x) := by
  intro U hU
  have hs : ∀ a, ((fun i => f (i, a)) ⁻¹' U)ᶜ.Finite := fun a => h a hU
  rw [Filter.mem_map, Filter.mem_cofinite]
  refine (Set.finite_iUnion fun a => (hs a).image (fun i => (i, a))).subset ?_
  rintro ⟨i, a⟩ hia
  exact Set.mem_iUnion.2 ⟨a, i, hia, rfl⟩

/- English proof (translation)
Introduce `l _ K bk τ hτ d ρ hρ s`. Take `⟨ι, ⟨TB⟩⟩` from `GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk`. Establish `hρ0` using `bk.ρ₀_pos'`. Establish `hρ1` using `bk.ρ₀_lt_one'`. Establish `hj0 : ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)‖ ≤ bk.ρ₀`.

Simplify using `using norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) 1 hρ0`. Set `j0 : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀` to `Disc.map (l := l) (u := (X : bk.S)) (ρ := bk.ρ₀) (u' := bk.ev X) (ρ' := bk.ρ₀) bk.ev hj0`. Establish `hj0d : IsDiscMap bk.ev j0` using `isDiscMap_map _ _`. Establish `hΦ0 : ‖toDisc l (bk.ev X) bk.ρ₀ (WittVector.frobenius (bk.ev X))‖ ≤ bk.ρ₀`. Rewrite using `[frobenius_ev_X_eq]`.

Use `(norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) l hρ0).trans ?_` and prove the remaining obligations. Conclude with `pow_le_of_le_one (by positivity) (by exact_mod_cast hρ1.le) (Fact.out : l.Prime).ne_zero`. Set `Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀` to `Disc.map (l := l) (u := bk.ev X) (ρ := bk.ρ₀) (u' := bk.ev X) (ρ' := bk.ρ₀) WittVector.frobenius hΦ0`. Establish `hΦ : IsDiscMap WittVector.frobenius Φ` using `isDiscMap_map _ _`. Take `⟨cD, hc1, hc2, hc3, hc4, hc5, -, -, -⟩` from `GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk (Ainf l) bk.ev ι TB bk.ρ₀ hρ0 hρ1 j0 hj0d`.

Establish `hrec` using `GlobalTheory.T.seed_coeff_recurrence_alt l K bk τ hτ d ρ hρ s ι TB j0 hj0d cD hc1 hc2 hc5 hc3 Φ hΦ`. Set `V : ι → Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)` to `fun i => s.W * (s.W'.map (cD i)).map j0`. Set `Vκ : ι × (Fin d × Fin d) → bk.DA bk.ρ₀` to `fun p => V p.1 p.2.1 p.2.2`. Set `c : ι × (Fin d × Fin d) → ι × (Fin d × Fin d) → Ainf l` to `fun p q => if p.2 = q.2 then bk.ev (TB.c q.1 (WittVector.frobenius (TB.b p.1))) else 0`. Establish `hcfin : ∀ p (n : ℕ), {q | c p q ∉ (bk.J ^ n).map bk.ev}.Finite`.

Introduce and unpack `⟨i, ab⟩ n`. Use `((TB.fin (WittVector.frobenius (TB.b i)) n).image fun i₁ => (i₁, ab)).subset ?_` and prove the remaining obligations. Introduce and unpack `⟨i₁, ab'⟩ hq`. Distinguish the cases in `e : ab = ab'`. Substitute `e` using the available equality.

Use `⟨i₁, fun hm => hq ?_, rfl⟩` and prove the remaining obligations. Simplify using `only [c, if_pos rfl]`. Conclude with `Ideal.mem_map_of_mem _ hm`. Conclude with `(hq (by simp [c, e])).elim`. Establish `hj0c : Continuous j0` using `AddMonoidHomClass.continuous_of_bound j0 1 fun y => (hj0d.norm_le y).trans (one_mul _).ge`.

Establish `hV : Filter.Tendsto Vκ Filter.cofinite (nhds 0)`. Use `tendsto_cofinite_prod_of_finite Vκ fun ab => ?_` and prove the remaining obligations. Use `tendsto_finsetSum (Finset.univ : Finset (Fin d)) fun m _ => (tendsto_const_nhds (x := s.W ab.1 m)).mul ((hj0c.tendsto 0).comp (hc4 (s.W' m ab.2)))` as an intermediate fact. Simplify `this` using `[Vκ, V, Matrix.mul_apply]`. Establish `hrecκ : ∀ q, HasSum (fun p => Φ (Vκ p) * toDisc l (bk.ev X) bk.ρ₀ (c p q)) (toDisc l (bk.ev X) bk.ρ₀ (bk.ev bk.E) ^ (2 * s.N) * Vκ q)`.

Introduce and unpack `⟨i₁, a, b⟩`. Establish `hg : Function.Injective (fun i : ι => (i, (a, b)))` using `fun x y h => (Prod.mk.inj h).1`. Use `(hg.hasSum_iff ?_).1 ?_` and prove the remaining obligations. Introduce and unpack `⟨i, a', b'⟩ hx`. Establish `hne : (a', b') ≠ (a, b)` using `fun e => hx ⟨i, by simp [e]⟩`.

Simplify using `[c, hne]`. Use `hrec i₁ a b using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using `[c, Vκ, V]`. Both sides reduce to the same expression.

Take `⟨k, v, hv1, hv2⟩` from `GlobalTheory.T.exists_bounded_of_phi_equation_disc l K bk (Ainf l) bk.ev ι TB WittVector.frobenius (frobenius_ev_X_eq bk) Φ hΦ _ c hcfin (2 * s.N) Vκ hV hrecκ`. Use `⟨ι, TB, k, fun i => Matrix.of fun a b => v (i, (a, b)), fun i => (l : bk.DS bk.ρ₀) ^ k • s.W'.map (cD i), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `n a b`. Establish `hg : Function.Injective (fun i : ι => (i, (a, b)))` using `fun x y h => (Prod.mk.inj h).1`. Conclude with `(hv2 n).preimage hg.injOn`.

Introduce `j hj i`. Establish `e` using `IsDiscMap.unique hj hj0d`. Substitute `e` using the available equality. Use extensionality with `a b`. Use `show (s.W * ((l : bk.DS bk.ρ₀) ^ k • s.W'.map (cD i)).map j0) a b = bk.iA (v (i, (a, b)))`.

Rewrite using `[hv1]`. Simplify using `only [Vκ, V, Matrix.mul_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, map_natCast, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun m _ => by ring`. Introduce `a b`. Establish `hs` using `(hasSum_sum (s := (Finset.univ : Finset (Fin d))) fun m _ => (hc5 (s.W' m b)).mul_left (s.W a m)).mul_left ((l : bk.DA bk.ρ₀) ^ k)`.

Establish `hW` using `congrFun (congrFun s.W_mul a) b`. Rewrite `hW` using `[Matrix.mul_apply]`. Rewrite `hs` using `[hW]`. Establish `hf : (fun i => bk.iA ((Matrix.of fun a b => v (i, (a, b))) a b * TB.b i)) = fun i => (l : bk.DA bk.ρ₀) ^ k * ∑ m, s.W a m * (j0 (cD i (s.W' m b)) * toDisc l (bk.ev X) bk.ρ₀ (TB.b i))`. Use function extensionality and compare the values at `i`.

Rewrite using `[map_mul, Matrix.of_apply, hv1]`. Simplify using `only [Vκ, V, Matrix.mul_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun m _ => by ring`. Establish `hval : bk.iA ((l : Ainf l) ^ k * τ ^ (2 * s.N) * if a = b then 1 else 0) = (l : bk.DA bk.ρ₀) ^ k * (bk.iA τ ^ (2 * s.N) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀))) a b`. Rewrite using `[Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]`.

Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[hf, hval]`. Conclude with `hs`.
-/
theorem exists_bounded_periods : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ), ∃ (ι : Type) (TB : TopBasis bk.ev bk.J ι) (k : ℕ) (v : ι → Matrix (Fin d) (Fin d) (Ainf l)) (Z : ι → Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), (∀ (n : ℕ) (a b : Fin d), {i | v i a b ∉ (bk.J ^ n).map bk.ev}.Finite) ∧ (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → ∀ i, s.W * (Z i).map j = (v i).map bk.iA) ∧ ∀ a b : Fin d, HasSum (fun i => bk.iA (v i a b * TB.b i)) (bk.iA ((l : Ainf l) ^ k * τ ^ (2 * s.N) * if a = b then 1 else 0)) := by
  intro l _ K bk τ hτ d ρ hρ s
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have hρ0 := bk.ρ₀_pos'
  have hρ1 := bk.ρ₀_lt_one'
  have hj0 : ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)‖ ≤ bk.ρ₀ := by
    simpa using norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) 1 hρ0
  let j0 : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀ :=
    Disc.map (l := l) (u := (X : bk.S)) (ρ := bk.ρ₀) (u' := bk.ev X) (ρ' := bk.ρ₀) bk.ev hj0
  have hj0d : IsDiscMap bk.ev j0 := isDiscMap_map _ _
  have hΦ0 : ‖toDisc l (bk.ev X) bk.ρ₀ (WittVector.frobenius (bk.ev X))‖ ≤ bk.ρ₀ := by
    rw [frobenius_ev_X_eq]
    refine (norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) l hρ0).trans ?_
    exact pow_le_of_le_one (by positivity) (by exact_mod_cast hρ1.le) (Fact.out : l.Prime).ne_zero
  let Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀ :=
    Disc.map (l := l) (u := bk.ev X) (ρ := bk.ρ₀) (u' := bk.ev X) (ρ' := bk.ρ₀) WittVector.frobenius hΦ0
  have hΦ : IsDiscMap WittVector.frobenius Φ := isDiscMap_map _ _
  obtain ⟨cD, hc1, hc2, hc3, hc4, hc5, -, -, -⟩ := GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk (Ainf l) bk.ev ι TB bk.ρ₀ hρ0 hρ1 j0 hj0d
  have hrec := GlobalTheory.T.seed_coeff_recurrence_alt l K bk τ hτ d ρ hρ s ι TB j0 hj0d cD hc1 hc2 hc5 hc3 Φ hΦ
  let V : ι → Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀) := fun i => s.W * (s.W'.map (cD i)).map j0
  let Vκ : ι × (Fin d × Fin d) → bk.DA bk.ρ₀ := fun p => V p.1 p.2.1 p.2.2
  let c : ι × (Fin d × Fin d) → ι × (Fin d × Fin d) → Ainf l := fun p q =>
    if p.2 = q.2 then bk.ev (TB.c q.1 (WittVector.frobenius (TB.b p.1))) else 0
  have hcfin : ∀ p (n : ℕ), {q | c p q ∉ (bk.J ^ n).map bk.ev}.Finite := by
    rintro ⟨i, ab⟩ n
    refine ((TB.fin (WittVector.frobenius (TB.b i)) n).image fun i₁ => (i₁, ab)).subset ?_
    rintro ⟨i₁, ab'⟩ hq
    by_cases e : ab = ab'
    · subst e
      refine ⟨i₁, fun hm => hq ?_, rfl⟩
      simp only [c, if_pos rfl]
      exact Ideal.mem_map_of_mem _ hm
    · exact (hq (by simp [c, e])).elim
  have hj0c : Continuous j0 :=
    AddMonoidHomClass.continuous_of_bound j0 1 fun y => (hj0d.norm_le y).trans (one_mul _).ge
  have hV : Filter.Tendsto Vκ Filter.cofinite (nhds 0) := by
    refine tendsto_cofinite_prod_of_finite Vκ fun ab => ?_
    have := tendsto_finsetSum (Finset.univ : Finset (Fin d)) fun m _ =>
      (tendsto_const_nhds (x := s.W ab.1 m)).mul ((hj0c.tendsto 0).comp (hc4 (s.W' m ab.2)))
    simpa [Vκ, V, Matrix.mul_apply] using this
  have hrecκ : ∀ q, HasSum (fun p => Φ (Vκ p) * toDisc l (bk.ev X) bk.ρ₀ (c p q))
      (toDisc l (bk.ev X) bk.ρ₀ (bk.ev bk.E) ^ (2 * s.N) * Vκ q) := by
    rintro ⟨i₁, a, b⟩
    have hg : Function.Injective (fun i : ι => (i, (a, b))) := fun x y h => (Prod.mk.inj h).1
    refine (hg.hasSum_iff ?_).1 ?_
    · rintro ⟨i, a', b'⟩ hx
      have hne : (a', b') ≠ (a, b) := fun e => hx ⟨i, by simp [e]⟩
      simp [c, hne]
    · convert hrec i₁ a b using 1
      · funext i
        simp [c, Vκ, V]
      · rfl
  obtain ⟨k, v, hv1, hv2⟩ := GlobalTheory.T.exists_bounded_of_phi_equation_disc l K bk (Ainf l) bk.ev ι TB WittVector.frobenius (frobenius_ev_X_eq bk)
    Φ hΦ _ c hcfin (2 * s.N) Vκ hV hrecκ
  refine ⟨ι, TB, k, fun i => Matrix.of fun a b => v (i, (a, b)),
    fun i => (l : bk.DS bk.ρ₀) ^ k • s.W'.map (cD i), ?_, ?_, ?_⟩
  · intro n a b
    have hg : Function.Injective (fun i : ι => (i, (a, b))) := fun x y h => (Prod.mk.inj h).1
    exact (hv2 n).preimage hg.injOn
  · intro j hj i
    have e := IsDiscMap.unique hj hj0d
    subst e
    ext a b
    show (s.W * ((l : bk.DS bk.ρ₀) ^ k • s.W'.map (cD i)).map j0) a b = bk.iA (v (i, (a, b)))
    rw [hv1]
    simp only [Vκ, V, Matrix.mul_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow,
      map_natCast, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  · intro a b
    have hs := (hasSum_sum (s := (Finset.univ : Finset (Fin d))) fun m _ =>
      (hc5 (s.W' m b)).mul_left (s.W a m)).mul_left ((l : bk.DA bk.ρ₀) ^ k)
    have hW := congrFun (congrFun s.W_mul a) b
    rw [Matrix.mul_apply] at hW
    rw [hW] at hs
    have hf : (fun i => bk.iA ((Matrix.of fun a b => v (i, (a, b))) a b * TB.b i)) =
        fun i => (l : bk.DA bk.ρ₀) ^ k * ∑ m, s.W a m * (j0 (cD i (s.W' m b)) * toDisc l (bk.ev X) bk.ρ₀ (TB.b i)) := by
      funext i
      rw [map_mul, Matrix.of_apply, hv1]
      simp only [Vκ, V, Matrix.mul_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun m _ => by ring
    have hval : bk.iA ((l : Ainf l) ^ k * τ ^ (2 * s.N) * if a = b then 1 else 0) =
        (l : bk.DA bk.ρ₀) ^ k * (bk.iA τ ^ (2 * s.N) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀))) a b := by
      rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> simp
    rw [hf, hval]
    exact hs

end GlobalTheory.BSP
