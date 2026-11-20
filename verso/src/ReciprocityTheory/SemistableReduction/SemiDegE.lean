import ReciprocityTheory.SemistableReduction.SemiDegSt

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

/- English proof (translation)
Take `⟨s, hsB, hspan, hli⟩` from `exists_linearIndependent K (B : Set (Fin r → K))`. Establish `hfin : s.Finite` using `by first`. Consider the case `exact hli.setFinite`. Consider the case `exact Set.toFinite s`. Consider the case `exact (Set.finite_coe_iff.mp hli.finite)`.

Use `haveI : Fintype s := hfin.fintype`. Set `e` to `Fintype.equivFin s`. Use `⟨Fintype.card s, fun i => ((e.symm i : s) : Fin r → K), fun i => hsB (e.symm i).2, hli.comp _ e.symm.injective, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Establish `hx' : x ∈ Submodule.span K s`.

Rewrite using `[hspan]`. Conclude with `Submodule.subset_span hx`. Establish `hr : Set.range (fun i => ((e.symm i : s) : Fin r → K)) = s`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨i, rfl⟩`. Conclude with `(e.symm i).2`. Introduce `hy`. Conclude with `⟨e ⟨y, hy⟩, by simp⟩`. Rewrite using `[hr]`.

Conclude with `hx'`.
-/
theorem exists_kBasisIn {K : Type} [Field K] [NumberField K] {r : ℕ}
    (B : Submodule (𝓞 K) (Fin r → K)) : ∃ (k : ℕ) (b : Fin k → Fin r → K), IsKBasisIn B b := by
  classical
  obtain ⟨s, hsB, hspan, hli⟩ := exists_linearIndependent K (B : Set (Fin r → K))
  have hfin : s.Finite := by
    first
    | exact hli.setFinite
    | exact Set.toFinite s
    | exact (Set.finite_coe_iff.mp hli.finite)
  haveI : Fintype s := hfin.fintype
  let e := Fintype.equivFin s
  refine ⟨Fintype.card s, fun i => ((e.symm i : s) : Fin r → K), fun i => hsB (e.symm i).2,
    hli.comp _ e.symm.injective, ?_⟩
  intro x hx
  have hx' : x ∈ Submodule.span K s := by
    rw [hspan]
    exact Submodule.subset_span hx
  have hr : Set.range (fun i => ((e.symm i : s) : Fin r → K)) = s := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm i).2
    · intro hy
      exact ⟨e ⟨y, hy⟩, by simp⟩
  rw [hr]
  exact hx'

/- English proof (translation)
Take `⟨hmem, hli, -⟩` from `hb`. Assume the negation of the conclusion as `hk`. Establish `i : Fin k` using `⟨0, Nat.pos_of_ne_zero hk⟩`. Conclude with `hli.ne_zero i ((Submodule.mem_bot _).mp (hmem i))`.
-/
theorem kBasisIn_bot_eq {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (b : Fin k → Fin r → K) (hb : IsKBasisIn (⊥ : Submodule (𝓞 K) (Fin r → K)) b) : k = 0 := by
  obtain ⟨hmem, hli, -⟩ := hb
  by_contra hk
  have i : Fin k := ⟨0, Nat.pos_of_ne_zero hk⟩
  exact hli.ne_zero i ((Submodule.mem_bot _).mp (hmem i))

/- English proof (translation)
Take `⟨-, -, hspan⟩` from `hb`. Establish `hB : B = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Establish `h` using `hspan x hx`.

Simplify `h` using `[Set.range_eq_empty]`. Substitute `hB` using the available equality. Simplify using `[latDeg, Set.range_eq_empty]`.
-/
theorem latDeg_zero_fam {K : Type} [Field K] [NumberField K] {r : ℕ}
    (H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (B : Submodule (𝓞 K) (Fin r → K))
    (b : Fin 0 → Fin r → K) (hb : IsKBasisIn B b) : latDeg H B b = 0 := by
  obtain ⟨-, -, hspan⟩ := hb
  have hB : B = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h := hspan x hx
    simpa [Set.range_eq_empty] using h
  subst hB
  simp [latDeg, Set.range_eq_empty]

/- English proof (translation)
Take `⟨hmem, hli, hspan⟩` from `hb`. Take `⟨G, hG⟩` from `id hB`. Establish `hcoef : ∀ g ∈ G, ∃ c : Fin k → K, g = ∑ i, c i • b i`. Introduce `g hg`. Establish `hgB : g ∈ B`.

Rewrite using `[← hG]`. Conclude with `Submodule.subset_span hg`. Conclude with `((Submodule.mem_span_range_iff_exists_fun K).mp (hspan g hgB)).imp fun c hc => hc.symm`. Use `choose! c hc using hcoef`. Take `⟨β, hβ⟩` from `IsLocalization.exist_integer_multiples (M := nonZeroDivisors (𝓞 K)) (S := K) (G ×ˢ (Finset.univ : Finset (Fin k))) (fun p => c p.1 p.2)`.

Establish `hβS : ∀ x ∈ B, (β : 𝓞 K) • x ∈ Submodule.span (𝓞 K) (Set.range b)`. Introduce `x hx`. Rewrite `hx` using `[← hG]`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem g hg`.

Rewrite using `[hc g hg, Finset.smul_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Take `⟨t, ht⟩` from `hβ (g, i) (Finset.mem_product.mpr ⟨hg, Finset.mem_univ _⟩)`. Rewrite using `[← smul_assoc]`. Simplify using `only at ht`.

Rewrite using `[← ht, algebraMap_smul]`. Conclude with `Submodule.smul_mem _ t (Submodule.subset_span ⟨i, rfl⟩)`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`. Rewrite using `[smul_add]`.

Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx`. Rewrite using `[smul_comm]`. Conclude with `Submodule.smul_mem _ a hx`. Establish `hβ0 : (β : 𝓞 K) ≠ 0` using `nonZeroDivisors.coe_ne_zero β`.

Establish `hint : IsIntegral ℤ (β : 𝓞 K)` using `Algebra.IsIntegral.isIntegral _`. Establish `hp0 : (minpoly ℤ (β : 𝓞 K)).coeff 0 ≠ 0`. Introduce `h0`. Take `⟨q, hq⟩` from `Polynomial.X_dvd_sub_C (p := minpoly ℤ (β : 𝓞 K))`. Rewrite `hq` using `[h0, map_zero, sub_zero]`.

Establish `hmon : q.Monic` using `Polynomial.monic_X.of_mul_monic_left (hq ▸ minpoly.monic hint)`. Establish `hq0 : Polynomial.aeval (β : 𝓞 K) q = 0`. Establish `h` using `minpoly.aeval ℤ (β : 𝓞 K)`. Rewrite `h` using `[hq, map_mul, Polynomial.aeval_X]`. Conclude with `(mul_eq_zero.mp h).resolve_left hβ0`.

Establish `hdeg : (minpoly ℤ (β : 𝓞 K)).degree ≤ q.degree` using `by first`. Consider the case `exact minpoly.min ℤ (β : 𝓞 K) hmon hq0`. Consider the case `exact minpoly.min (A := ℤ) (x := (β : 𝓞 K)) hmon hq0`. Rewrite `hdeg` using `[hq, Polynomial.degree_mul, Polynomial.degree_X, Polynomial.degree_eq_natDegree hmon.ne_zero]`. Establish `h2 : 1 + q.natDegree ≤ q.natDegree` using `by exact_mod_cast hdeg`.

Use linear arithmetic over natural numbers and integers. Take `⟨q, hq⟩` from `Polynomial.X_dvd_sub_C (p := minpoly ℤ (β : 𝓞 K))`. Establish `hdiv : (((minpoly ℤ (β : 𝓞 K)).coeff 0 : ℤ) : 𝓞 K) = (β : 𝓞 K) * (-(Polynomial.aeval (β : 𝓞 K) q))`. Establish `h` using `congrArg (Polynomial.aeval (β : 𝓞 K)) hq`. Simplify using `only [map_sub, Polynomial.aeval_C, map_mul, Polynomial.aeval_X, minpoly.aeval, zero_sub] at h`.

Rewrite using `[mul_neg, ← h, neg_neg, eq_intCast]`. Use `set m : ℤ := (minpoly ℤ (β : 𝓞 K)).coeff 0 with hm`. Establish `hmS : ∀ x ∈ B, m • x ∈ Submodule.span (𝓞 K) (Set.range b)`. Introduce `x hx`. Rewrite using `[← Int.cast_smul_eq_zsmul (𝓞 K), hdiv, mul_smul]`.

Conclude with `hβS _ (Submodule.smul_mem _ _ hx)`. Establish `hfinB : Module.Finite ℤ B` using `by haveI : Module.Finite (𝓞 K) B := Module.Finite.iff_fg.mpr hB`. Conclude with `Module.Finite.trans (𝓞 K) B`. Use `haveI hfg : AddGroup.FG B := Module.Finite.iff_addGroup_fg.mp hfinB`. Set `N : Submodule (𝓞 K) B` to `(Submodule.span (𝓞 K) (Set.range b)).comap B.subtype`.

Use `haveI hfgQ : AddGroup.FG (B ⧸ N.toAddSubgroup) := by first`. Consider the case `exact AddGroup.fg_of_surjective (QuotientAddGroup.mk'_surjective N.toAddSubgroup)`. Consider the case `exact QuotientAddGroup.fg N.toAddSubgroup`. Consider the case `infer_instance`. Establish `htors : IsAddTorsion (B ⧸ N.toAddSubgroup)`.

Introduce `y`. Proceed by induction on `y using QuotientAddGroup.induction_on with`. Consider the case `H x`. Use `(isOfFinAddOrder_iff_nsmul_eq_zero).mpr ⟨m.natAbs, Int.natAbs_pos.mpr hp0, ?_⟩` and prove the remaining obligations. Rewrite using `[← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]`.

Use `show (m.natAbs • (x : Fin r → K)) ∈ Submodule.span (𝓞 K) (Set.range b)`. Establish `e1 : (m.natAbs • (x : Fin r → K)) = ((m.natAbs : ℤ) • (x : Fin r → K))` using `by simp`. Rewrite using `[e1]`. Break down `Int.natAbs_eq m with h | h` into its components or cases. Rewrite using `[← h]`.

Conclude with `hmS _ x.2`. Rewrite using `[show ((m.natAbs : ℤ)) = -m by omega, neg_smul]`. Conclude with `Submodule.neg_mem _ (hmS _ x.2)`. Establish `hfinQ : Finite (B ⧸ N.toAddSubgroup)` using `by first`. Consider the case `exact AddCommGroup.finite_of_fg_torsion _ htors`.

Consider the case `exact AddCommGroup.finite_of_fg_torsion htors`. Establish `: N.toAddSubgroup.index ≠ 0` using `AddSubgroup.index_ne_zero_of_finite`. Conclude with `this`.
-/
theorem spanIdx_ne_zero {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (B : Submodule (𝓞 K) (Fin r → K)) (b : Fin k → Fin r → K) (hB : B.FG)
    (hb : IsKBasisIn B b) : spanIdx B b ≠ 0 := by
  classical
  obtain ⟨hmem, hli, hspan⟩ := hb
  obtain ⟨G, hG⟩ := id hB
  have hcoef : ∀ g ∈ G, ∃ c : Fin k → K, g = ∑ i, c i • b i := by
    intro g hg
    have hgB : g ∈ B := by
      rw [← hG]
      exact Submodule.subset_span hg
    exact ((Submodule.mem_span_range_iff_exists_fun K).mp (hspan g hgB)).imp fun c hc => hc.symm
  choose! c hc using hcoef
  obtain ⟨β, hβ⟩ := IsLocalization.exist_integer_multiples (M := nonZeroDivisors (𝓞 K)) (S := K)
    (G ×ˢ (Finset.univ : Finset (Fin k))) (fun p => c p.1 p.2)
  have hβS : ∀ x ∈ B, (β : 𝓞 K) • x ∈ Submodule.span (𝓞 K) (Set.range b) := by
    intro x hx
    rw [← hG] at hx
    induction hx using Submodule.span_induction with
    | mem g hg =>
      rw [hc g hg, Finset.smul_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      obtain ⟨t, ht⟩ := hβ (g, i) (Finset.mem_product.mpr ⟨hg, Finset.mem_univ _⟩)
      rw [← smul_assoc]
      simp only at ht
      rw [← ht, algebraMap_smul]
      exact Submodule.smul_mem _ t (Submodule.subset_span ⟨i, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [smul_add]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [smul_comm]
      exact Submodule.smul_mem _ a hx
  have hβ0 : (β : 𝓞 K) ≠ 0 := nonZeroDivisors.coe_ne_zero β
  have hint : IsIntegral ℤ (β : 𝓞 K) := Algebra.IsIntegral.isIntegral _
  have hp0 : (minpoly ℤ (β : 𝓞 K)).coeff 0 ≠ 0 := by
    intro h0
    obtain ⟨q, hq⟩ := Polynomial.X_dvd_sub_C (p := minpoly ℤ (β : 𝓞 K))
    rw [h0, map_zero, sub_zero] at hq
    have hmon : q.Monic := Polynomial.monic_X.of_mul_monic_left (hq ▸ minpoly.monic hint)
    have hq0 : Polynomial.aeval (β : 𝓞 K) q = 0 := by
      have h := minpoly.aeval ℤ (β : 𝓞 K)
      rw [hq, map_mul, Polynomial.aeval_X] at h
      exact (mul_eq_zero.mp h).resolve_left hβ0
    have hdeg : (minpoly ℤ (β : 𝓞 K)).degree ≤ q.degree := by
      first
      | exact minpoly.min ℤ (β : 𝓞 K) hmon hq0
      | exact minpoly.min (A := ℤ) (x := (β : 𝓞 K)) hmon hq0
    rw [hq, Polynomial.degree_mul, Polynomial.degree_X,
      Polynomial.degree_eq_natDegree hmon.ne_zero] at hdeg
    have h2 : 1 + q.natDegree ≤ q.natDegree := by exact_mod_cast hdeg
    omega
  obtain ⟨q, hq⟩ := Polynomial.X_dvd_sub_C (p := minpoly ℤ (β : 𝓞 K))
  have hdiv : (((minpoly ℤ (β : 𝓞 K)).coeff 0 : ℤ) : 𝓞 K) =
      (β : 𝓞 K) * (-(Polynomial.aeval (β : 𝓞 K) q)) := by
    have h := congrArg (Polynomial.aeval (β : 𝓞 K)) hq
    simp only [map_sub, Polynomial.aeval_C, map_mul, Polynomial.aeval_X, minpoly.aeval,
      zero_sub] at h
    rw [mul_neg, ← h, neg_neg, eq_intCast]
  set m : ℤ := (minpoly ℤ (β : 𝓞 K)).coeff 0 with hm
  have hmS : ∀ x ∈ B, m • x ∈ Submodule.span (𝓞 K) (Set.range b) := by
    intro x hx
    rw [← Int.cast_smul_eq_zsmul (𝓞 K), hdiv, mul_smul]
    exact hβS _ (Submodule.smul_mem _ _ hx)
  have hfinB : Module.Finite ℤ B := by
    haveI : Module.Finite (𝓞 K) B := Module.Finite.iff_fg.mpr hB
    exact Module.Finite.trans (𝓞 K) B
  haveI hfg : AddGroup.FG B := Module.Finite.iff_addGroup_fg.mp hfinB
  let N : Submodule (𝓞 K) B := (Submodule.span (𝓞 K) (Set.range b)).comap B.subtype
  haveI hfgQ : AddGroup.FG (B ⧸ N.toAddSubgroup) := by
    first
    | exact AddGroup.fg_of_surjective (QuotientAddGroup.mk'_surjective N.toAddSubgroup)
    | exact QuotientAddGroup.fg N.toAddSubgroup
    | infer_instance
  have htors : IsAddTorsion (B ⧸ N.toAddSubgroup) := by
    intro y
    induction y using QuotientAddGroup.induction_on with
    | H x =>
      refine (isOfFinAddOrder_iff_nsmul_eq_zero).mpr ⟨m.natAbs, Int.natAbs_pos.mpr hp0, ?_⟩
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
      show (m.natAbs • (x : Fin r → K)) ∈ Submodule.span (𝓞 K) (Set.range b)
      have e1 : (m.natAbs • (x : Fin r → K)) = ((m.natAbs : ℤ) • (x : Fin r → K)) := by simp
      rw [e1]
      rcases Int.natAbs_eq m with h | h
      · rw [← h]
        exact hmS _ x.2
      · rw [show ((m.natAbs : ℤ)) = -m by omega, neg_smul]
        exact Submodule.neg_mem _ (hmS _ x.2)
  have hfinQ : Finite (B ⧸ N.toAddSubgroup) := by
    first
    | exact AddCommGroup.finite_of_fg_torsion _ htors
    | exact AddCommGroup.finite_of_fg_torsion htors
  have : N.toAddSubgroup.index ≠ 0 := AddSubgroup.index_ne_zero_of_finite
  exact this

/- English proof (translation)
Establish `hSC : (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup ≤ C.toAddSubgroup`. Introduce `x hx`. Conclude with `(Submodule.span_le.mpr (Set.range_subset_iff.mpr hbC.1)) hx`. Establish `hCB' : C.toAddSubgroup ≤ B.toAddSubgroup` using `fun x hx => hCB hx`. Establish `hmul` using `AddSubgroup.relIndex_mul_relIndex _ _ _ hSC hCB'`.

Establish `hne : (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex B.toAddSubgroup ≠ 0` using `spanIdx_ne_zero B b hB hbB`. Establish `h1 : (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex C.toAddSubgroup ≤ (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex B.toAddSubgroup` using `Nat.le_of_dvd (Nat.pos_of_ne_zero hne) ⟨_, hmul.symm⟩`. Establish `h2 : 0 < (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex C.toAddSubgroup`. Use `Nat.pos_of_ne_zero fun h => hne ?_` and prove the remaining obligations. Rewrite using `[← hmul, h, zero_mul]`.

Unfold `latDeg`. Establish `h3 : Real.log (((Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex C.toAddSubgroup : ℕ) : ℝ) ≤ Real.log (((Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex B.toAddSubgroup : ℕ) : ℝ)` using `Real.log_le_log (by exact_mod_cast h2) (by exact_mod_cast h1)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem latDeg_le_of_le {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (C B : Submodule (𝓞 K) (Fin r → K))
    (b : Fin k → Fin r → K) (hCB : C ≤ B) (hB : B.FG) (hbC : IsKBasisIn C b)
    (hbB : IsKBasisIn B b) : latDeg H C b ≤ latDeg H B b := by
  have hSC : (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup ≤ C.toAddSubgroup := by
    intro x hx
    exact (Submodule.span_le.mpr (Set.range_subset_iff.mpr hbC.1)) hx
  have hCB' : C.toAddSubgroup ≤ B.toAddSubgroup := fun x hx => hCB hx
  have hmul := AddSubgroup.relIndex_mul_relIndex _ _ _ hSC hCB'
  have hne : (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex B.toAddSubgroup ≠ 0 :=
    spanIdx_ne_zero B b hB hbB
  have h1 : (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex C.toAddSubgroup ≤
      (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex B.toAddSubgroup :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hne) ⟨_, hmul.symm⟩
  have h2 : 0 < (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex C.toAddSubgroup := by
    refine Nat.pos_of_ne_zero fun h => hne ?_
    rw [← hmul, h, zero_mul]
  unfold latDeg
  have h3 : Real.log (((Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex
      C.toAddSubgroup : ℕ) : ℝ) ≤ Real.log (((Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex
      B.toAddSubgroup : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast h2) (by exact_mod_cast h1)
  linarith

/- English proof (translation)
Distinguish the cases in `ha : a = 0`. Substitute `ha` using the available equality. Simplify using the standard rewrite rules. Establish `h1 : ((Algebra.norm ℚ a : ℚ) : ℂ) = ∏ σ : K →+* ℂ, σ a`. Establish `h` using `Algebra.norm_eq_prod_embeddings ℚ ℂ a`.

Simplify using `only [eq_ratCast] at h`. Rewrite using `[h]`. Conclude with `Fintype.prod_bijective (fun σ : K →ₐ[ℚ] ℂ => (σ : K →+* ℂ)) ⟨fun σ τ h => AlgHom.coe_ringHom_injective h, fun τ => ⟨τ.toRatAlgHom, RingHom.ext fun x => rfl⟩⟩ _ _ (fun σ => rfl)`. Rewrite using `[← Real.log_prod (s := Finset.univ) (f := fun σ : K →+* ℂ => ‖σ a‖) (fun σ _ => norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr ha)), ← norm_prod, ← h1]`. Use `first`.

Consider the case `rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]`. Consider the case `simp [Complex.norm_ratCast]`. Consider the case `simp`.
-/
theorem sum_log_norm_emb {K : Type} [Field K] [NumberField K] (a : K) :
    ∑ σ : K →+* ℂ, Real.log ‖σ a‖ = Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| := by
  by_cases ha : a = 0
  · subst ha
    simp
  · have h1 : ((Algebra.norm ℚ a : ℚ) : ℂ) = ∏ σ : K →+* ℂ, σ a := by
      have h := Algebra.norm_eq_prod_embeddings ℚ ℂ a
      simp only [eq_ratCast] at h
      rw [h]
      exact Fintype.prod_bijective (fun σ : K →ₐ[ℚ] ℂ => (σ : K →+* ℂ))
        ⟨fun σ τ h => AlgHom.coe_ringHom_injective h,
          fun τ => ⟨τ.toRatAlgHom, RingHom.ext fun x => rfl⟩⟩ _ _ (fun σ => rfl)
    rw [← Real.log_prod (s := Finset.univ) (f := fun σ : K →+* ℂ => ‖σ a‖)
      (fun σ _ => norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr ha)), ← norm_prod,
      ← h1]
    first
    | rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
    | simp [Complex.norm_ratCast]
    | simp

def embMat {K : Type} [Field K] [NumberField K] {r k : ℕ} (σ : K →+* ℂ)
    (b : Fin k → Fin r → K) : Matrix (Fin r) (Fin k) ℂ :=
  Matrix.of fun a i => σ (b i a)

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_assoc]`. Simplify using `[gramC, embMat, Matrix.mul_apply, Matrix.mulVec, dotProduct, embVec]`.
-/
theorem gramC_eq {K : Type} [Field K] [NumberField K] {r k : ℕ} (H : Matrix (Fin r) (Fin r) ℂ)
    (σ : K →+* ℂ) (b : Fin k → Fin r → K) :
    gramC H σ b = (embMat σ b)ᴴ * H * embMat σ b := by
  ext i j
  rw [Matrix.mul_assoc]
  simp [gramC, embMat, Matrix.mul_apply, Matrix.mulVec, dotProduct, embVec]

/- English proof (translation)
Set `A : Matrix (Fin r) (Fin k) K` to `Matrix.of fun a i => b i a`. Establish `hA : Function.Injective (Matrix.toLin' A)`. Introduce `x y hxy`. Establish `hinj : Function.Injective A.mulVec`. Rewrite using `[Matrix.mulVec_injective_iff]`.

Conclude with `hli`. Conclude with `hinj (by simpa [Matrix.toLin'_apply] using hxy)`. Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective (Matrix.toLin' A) (LinearMap.ker_eq_bot.mpr hA)`. Establish `hBA : LinearMap.toMatrix' g * A = 1`. Establish `h` using `congrArg LinearMap.toMatrix' hg`.

Rewrite `h` using `[LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id]`. Then use the resulting hypothesis. Establish `hE : embMat σ b = A.map σ`. Use extensionality with `a i`. Both sides reduce to the same expression. Establish `hBA' : (LinearMap.toMatrix' g).map σ * A.map σ = 1`.

Rewrite using `[← Matrix.map_mul, hBA, Matrix.map_one σ (map_zero σ) (map_one σ)]`. Introduce `x y hxy`. Rewrite `hxy` using `[hE]`. Use `congrArg ((LinearMap.toMatrix' g).map σ).mulVec hxy` as an intermediate fact. Simplify `this` using `[Matrix.mulVec_mulVec, hBA']`.
-/
theorem embMat_injective {K : Type} [Field K] [NumberField K] {r k : ℕ} (S : HermForm K r)
    (σ : K →+* ℂ) (b : Fin k → Fin r → K) (hli : LinearIndependent K b) :
    Function.Injective (embMat σ b).mulVec := by
  classical
  let A : Matrix (Fin r) (Fin k) K := Matrix.of fun a i => b i a
  have hA : Function.Injective (Matrix.toLin' A) := by
    intro x y hxy
    have hinj : Function.Injective A.mulVec := by
      rw [Matrix.mulVec_injective_iff]
      exact hli
    exact hinj (by simpa [Matrix.toLin'_apply] using hxy)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' A)
    (LinearMap.ker_eq_bot.mpr hA)
  have hBA : LinearMap.toMatrix' g * A = 1 := by
    have h := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at h
  have hE : embMat σ b = A.map σ := by
    ext a i
    rfl
  have hBA' : (LinearMap.toMatrix' g).map σ * A.map σ = 1 := by
    rw [← Matrix.map_mul, hBA, Matrix.map_one σ (map_zero σ) (map_one σ)]
  intro x y hxy
  rw [hE] at hxy
  have := congrArg ((LinearMap.toMatrix' g).map σ).mulVec hxy
  simpa [Matrix.mulVec_mulVec, hBA'] using this

/- English proof (translation)
Rewrite using `[gramC_eq]`. Conclude with `hH.conjTranspose_mul_mul_same (embMat_injective S σ b hli)`.
-/
theorem gramC_posDef {K : Type} [Field K] [NumberField K] {r k : ℕ} (S : HermForm K r)
    (H : Matrix (Fin r) (Fin r) ℂ) (hH : H.PosDef) (σ : K →+* ℂ) (b : Fin k → Fin r → K)
    (hli : LinearIndependent K b) : (gramC H σ b).PosDef := by
  rw [gramC_eq]
  exact hH.conjTranspose_mul_mul_same (embMat_injective S σ b hli)

end ReciprocityTheory.MultiplicativeHeights.SemiPt
