import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFrobEqMulField

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

namespace UpperTheory.Kd.C7.LangPolynomialRoots

open GlobalTheory.LangWitt

variable {p : ℕ} [hp : Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]
  {W : Type} [CommRing W]

end UpperTheory.Kd.C7.LangPolynomialRoots

/- English proof (translation)
Establish `h2 : 2 ≤ p` using `hp.out.two_le`. Establish `hdeg : (Polynomial.X ^ p - Polynomial.C lam * Polynomial.X - Polynomial.C c : Polynomial K).natDegree = p`. Rewrite using `[Polynomial.natDegree_sub_C, Polynomial.natDegree_sub_eq_left_of_natDegree_lt, Polynomial.natDegree_X_pow]`. Rewrite using `[Polynomial.natDegree_X_pow]`. Conclude with `lt_of_le_of_lt ((Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le) (by omega)`.

Take `⟨e, he⟩` from `IsAlgClosed.exists_root (Polynomial.X ^ p - Polynomial.C lam * Polynomial.X - Polynomial.C c : Polynomial K) (by`. Establish `hne : (Polynomial.X ^ p - Polynomial.C lam * Polynomial.X - Polynomial.C c : Polynomial K) ≠ 0`. Introduce `h`. Rewrite `hdeg` using `[h, Polynomial.natDegree_zero]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[Polynomial.degree_eq_natDegree hne, hdeg]`. Conclude with `hp.out.ne_zero)` after adjusting the coercions. Use `⟨e, ?_⟩` and prove the remaining obligations. Simplify using `only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C] at he`. Conclude with `sub_eq_zero.mp he`.
-/
private theorem exists_pow_char_sub_mul_eq {K : Type} [Field K] [IsAlgClosed K] (p : ℕ) [hp : Fact p.Prime]
    (lam c : K) : ∃ e : K, e ^ p - lam * e = c := by
  have h2 : 2 ≤ p := hp.out.two_le
  have hdeg : (Polynomial.X ^ p - Polynomial.C lam * Polynomial.X - Polynomial.C c : Polynomial K).natDegree = p := by
    rw [Polynomial.natDegree_sub_C, Polynomial.natDegree_sub_eq_left_of_natDegree_lt,
      Polynomial.natDegree_X_pow]
    rw [Polynomial.natDegree_X_pow]
    exact lt_of_le_of_lt ((Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le) (by omega)
  obtain ⟨e, he⟩ := IsAlgClosed.exists_root
    (Polynomial.X ^ p - Polynomial.C lam * Polynomial.X - Polynomial.C c : Polynomial K)
    (by
      have hne : (Polynomial.X ^ p - Polynomial.C lam * Polynomial.X - Polynomial.C c : Polynomial K) ≠ 0 := by
        intro h
        rw [h, Polynomial.natDegree_zero] at hdeg
        omega
      rw [Polynomial.degree_eq_natDegree hne, hdeg]
      exact_mod_cast hp.out.ne_zero)
  refine ⟨e, ?_⟩
  simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C] at he
  exact sub_eq_zero.mp he

/- English proof (translation)
Take `⟨n, f, g, rfl⟩` from `Submodule.mem_span_set'.mp hu`. Use `choose e he using fun i => exists_pow_char_sub_mul_eq (K := K) p lam (f i)`. Use `⟨∑ i, e i • (g i : E), Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (g i).2)), ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations.

Establish `hg : ψ (g i : E) = g i` using `(g i).2`. Rewrite using `[hψs, hg, smul_smul, ← sub_smul, he]`.
-/
private theorem exists_mem_span_fixed_sub_smul_eq {K E : Type} [Field K] [IsAlgClosed K] (p : ℕ) [hp : Fact p.Prime]
    [AddCommGroup E] [Module K E] (ψ : E →+ E)
    (hψs : ∀ (c : K) (v : E), ψ (c • v) = c ^ p • ψ v) (lam : K) (u : E)
    (hu : u ∈ Submodule.span K {v : E | ψ v = v}) :
    ∃ z ∈ Submodule.span K {v : E | ψ v = v}, ψ z - lam • z = u := by
  obtain ⟨n, f, g, rfl⟩ := Submodule.mem_span_set'.mp hu
  choose e he using fun i => exists_pow_char_sub_mul_eq (K := K) p lam (f i)
  refine ⟨∑ i, e i • (g i : E),
    Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (g i).2)), ?_⟩
  rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hg : ψ (g i : E) = g i := (g i).2
  rw [hψs, hg, smul_smul, ← sub_smul, he]

/- English proof (translation)
Use `set U := Submodule.span K {v : E | ψ v = v} with hU`. Assume the negation of the conclusion as `hne`. Take `⟨w0, -, hw0⟩` from `SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hne)`. Use `set w : ℕ → E := fun i => (⇑ψ)^[i] w0 with hw`. Establish `hwsucc : ∀ i, w (i + 1) = ψ (w i)` using `fun i => Function.iterate_succ_apply' _ _ _`.

Use `set W : ℕ → Submodule K E := fun i => U ⊔ Submodule.span K (Set.range fun j : Fin i => w j) with hW`. Establish `hex : ∃ r, w r ∈ W r`. Assume the negation of the conclusion as `hno`. Use `push_neg at hno`. Establish `hmono : ∀ i, i ≤ Module.finrank K (W i)`.

Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => exact Nat.zero_le _`. Consider the case `succ i ih`. Establish `hlt : W i < W (i + 1)`.

Use `lt_of_le_of_ne ?_ ?_` and prove the remaining obligations. Use `sup_le_sup_left (Submodule.span_mono ?_) _` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `⟨Fin.castSucc j, rfl⟩`. Introduce `heq`.

Apply `hno i` to reduce the goal to its premises. Rewrite using `[heq]`. Conclude with `Submodule.mem_sup_right (Submodule.subset_span ⟨Fin.last i, rfl⟩)`. Use `Submodule.finrank_lt_finrank_of_lt hlt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `h1` using `hmono (Module.finrank K E + 1)`. Establish `h2` using `Submodule.finrank_le (W (Module.finrank K E + 1))`. Use linear arithmetic over natural numbers and integers. Take `⟨r, hr, hmin⟩ : ∃ r, w r ∈ W r ∧ ∀ i < r, w i ∉ W i` from `⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩`. Choose the witnesses or unpack the hypotheses as in `⟨s, rfl⟩ : ∃ s, r = s + 1 := by`.

Use `⟨r - 1, ?_⟩` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos r with h0 | h0` into its components or cases. It suffices to derive a contradiction. Substitute `h0` using the available equality. Apply `hw0` to reduce the goal to its premises.

Simplify `hr` using `[W, w]`. Use linear arithmetic over natural numbers and integers. Take `⟨u, hu, y, hy, hsum⟩` from `Submodule.mem_sup.mp hr`. Take `⟨a, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun K).mp hy`. Establish `ha0 : a 0 ≠ 0`.

Introduce `ha`. Take `⟨u', hu'U, hu'⟩` from `exists_mem_span_fixed_sub_smul_eq p ψ hψs 0 u hu`. Rewrite `hu'` using `[zero_smul, sub_zero]`. Use `choose b hb using fun i : Fin (s + 1) => exists_pow_char_sub_mul_eq (K := K) p 0 (a i)`. Simplify using `only [zero_mul, sub_zero] at hb`.

Apply `hmin s (by omega)` to reduce the goal to its premises. Establish `key : ψ (w s) = ψ (u' + ∑ i : Fin s, b i.succ • w i)`. Rewrite using `[← hwsucc, ← hsum, map_add, hu', map_sum, Fin.sum_univ_succ, ha, zero_smul, zero_add]`. Use `congr 1`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations.

Rewrite using `[hψs, hb, ← hwsucc]`. Both sides reduce to the same expression. Rewrite using `[hψi key]`. Conclude with `Submodule.add_mem _ (Submodule.mem_sup_left hu'U) (Submodule.mem_sup_right (Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))))`. Use `set a' : ℕ → K := fun i => if h : i < s + 1 then a ⟨i, h⟩ else 0 with ha'`.

Establish `ha'0 : a' 0 = a 0` using `by simp [a']`. Establish `hsum' : u + ∑ i ∈ Finset.range (s + 1), a' i • w i = w (s + 1)`. Rewrite using `[← hsum, ← Fin.sum_univ_eq_sum_range (fun i => a' i • w i) (s + 1)]`. Use `congr 1`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations.

Simplify using `only [ha', dif_pos i.2, Fin.eta]`. Set `Xs : ℕ → Polynomial K` to `fun n => Nat.rec (Polynomial.C (a' 0) * Polynomial.X ^ p) (fun i P => P ^ p + Polynomial.C (a' (i + 1)) * Polynomial.X ^ p) n`. Establish `hXs0 : Xs 0 = Polynomial.C (a' 0) * Polynomial.X ^ p` using `rfl`. Establish `hXsS : ∀ i, Xs (i + 1) = Xs i ^ p + Polynomial.C (a' (i + 1)) * Polynomial.X ^ p` using `fun i => rfl`. Establish `h2p : 2 ≤ p` using `hp.out.two_le`.

Establish `hdvd : ∀ i, Polynomial.X ^ p ∣ Xs i`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => rw [hXs0]`. Conclude with `dvd_mul_left _ _`.

Consider the case `succ i ih`. Rewrite using `[hXsS]`. Conclude with `dvd_add (ih.trans (dvd_pow_self _ hp.out.ne_zero)) (dvd_mul_left _ _)`. Establish `hdeg : ∀ i, (Xs i).natDegree = p ^ (i + 1)`. Introduce `i`.

Proceed by induction on `i with`. Consider the case `zero`. Rewrite using `[hXs0, Polynomial.natDegree_C_mul_X_pow _ _ (by rwa [ha'0]), pow_one]`. Consider the case `succ i ih`. Establish `hle : p ≤ p ^ (i + 1)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hXsS, Polynomial.natDegree_add_eq_left_of_natDegree_lt, Polynomial.natDegree_pow, ih, ← pow_succ']`. Rewrite using `[Polynomial.natDegree_pow, ih]`. Combine the equalities or inequalities in the displayed calculation. Take `⟨h, hh⟩ : Polynomial.X ^ 2 ∣ Xs s` from `(pow_dvd_pow _ h2p).trans (hdvd s)`.

Establish `hh0 : h ≠ 0`. Introduce and unpack `rfl`. Use `hdeg s` as an intermediate fact. Rewrite `this` using `[hh, mul_zero, Polynomial.natDegree_zero]`. Conclude with `absurd this.symm (pow_ne_zero _ hp.out.ne_zero)`.

Use `set g : Polynomial K := Polynomial.X * h - Polynomial.C 1 with hg`. Establish `hgdeg : g.natDegree = h.natDegree + 1`. Rewrite using `[hg, Polynomial.natDegree_sub_C, Polynomial.natDegree_X_mul hh0]`. Establish `hgne : g ≠ 0`. Introduce `h0`.

Rewrite `hgdeg` using `[h0, Polynomial.natDegree_zero]`. Use linear arithmetic over natural numbers and integers. Establish `hgd : g.degree ≠ 0`. Rewrite using `[Polynomial.degree_eq_natDegree hgne, hgdeg]`. Conclude with `Nat.succ_ne_zero h.natDegree` after adjusting the coercions.

Take `⟨t, ht⟩` from `IsAlgClosed.exists_root g hgd`. Establish `hth : t * h.eval t = 1`. Simplify `ht` using `[g, Polynomial.IsRoot, sub_eq_zero]`. Establish `ht0 : t ≠ 0`. Introduce and unpack `rfl`.

Simplify using `at hth`. Use `set x : ℕ → K := fun i => (Xs i).eval t with hx`. Establish `hx0 : x 0 = a' 0 * t ^ p` using `by simp [x, hXs0]`. Establish `hxS : ∀ i, x (i + 1) = x i ^ p + a' (i + 1) * t ^ p`. Introduce `i`.

Simplify using `[x, hXsS]`. Establish `hxs : x s = t`. Simplify using `only [x, hh, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]`. Take the linear combination `t * hth`. Use `set y : E := ∑ i ∈ Finset.range (s + 1), x i • w i with hy'`.

Establish `hψy : ψ y = t ^ p • u + y`. Establish `e1 : ψ y = ∑ i ∈ Finset.range (s + 1), x i ^ p • w (i + 1)`. Rewrite using `[hy', map_sum]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[hψs, hwsucc]`.

Rewrite using `[e1, Finset.sum_range_succ, hxs, ← hsum', hy', Finset.sum_range_succ', Finset.sum_range_succ', hx0]`. Simplify using `only [hxS, add_smul, Finset.sum_add_distrib, smul_add, Finset.smul_sum, smul_smul, mul_comm (t ^ p)]`. Normalize the expressions using the abelian group laws. Establish `hyU : y ∉ U`. Introduce `hyU'`.

Apply `hmin s (by omega)` to reduce the goal to its premises. Establish `hsplit : y = ∑ i ∈ Finset.range s, x i • w i + t • w s`. Rewrite using `[hy', Finset.sum_range_succ, hxs]`. Establish `hmemS : ∑ i ∈ Finset.range s, x i • w i ∈ W s`. Apply `Submodule.mem_sup_right` to reduce the goal to its premises.

Rewrite using `[← Fin.sum_univ_eq_sum_range (fun i => x i • w i) s]`. Conclude with `Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))`. Establish `htw : t • w s ∈ W s`. Establish `e2 : t • w s = y - ∑ i ∈ Finset.range s, x i • w i`. Rewrite using `[hsplit]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e2]`. Conclude with `Submodule.sub_mem _ (Submodule.mem_sup_left hyU') hmemS`. Establish `h3` using `Submodule.smul_mem _ t⁻¹ htw`. Rewrite `h3` using `[smul_smul, inv_mul_cancel₀ ht0, one_smul]`. Then use the resulting hypothesis.

Take `⟨z, hzU, hz⟩` from `exists_mem_span_fixed_sub_smul_eq p ψ hψs 1 (-(t ^ p • u)) (U.neg_mem (U.smul_mem _ hu))`. Establish `hz' : ψ z = z - t ^ p • u`. Rewrite `hz` using `[one_smul, sub_eq_iff_eq_add]`. Rewrite using `[hz]`. Normalize the expressions using the abelian group laws.

Establish `hfix : ψ (y + z) = y + z`. Rewrite using `[map_add, hψy, hz']`. Normalize the expressions using the abelian group laws. Apply `hyU` to reduce the goal to its premises. Establish `hyz : y + z ∈ U` using `Submodule.subset_span hfix`.

Establish `h4` using `U.sub_mem hyz hzU`. Simplify using `using h4`.
-/
private theorem span_fixed_eq_whole_of_semilinear_injective {K E : Type} [Field K] [IsAlgClosed K] (p : ℕ) [hp : Fact p.Prime]
    [AddCommGroup E] [Module K E] [FiniteDimensional K E] (ψ : E →+ E)
    (hψs : ∀ (c : K) (v : E), ψ (c • v) = c ^ p • ψ v) (hψi : Function.Injective ψ) :
    Submodule.span K {v : E | ψ v = v} = ⊤ := by
  classical
  set U := Submodule.span K {v : E | ψ v = v} with hU
  by_contra hne
  obtain ⟨w0, -, hw0⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hne)
  set w : ℕ → E := fun i => (⇑ψ)^[i] w0 with hw
  have hwsucc : ∀ i, w (i + 1) = ψ (w i) := fun i => Function.iterate_succ_apply' _ _ _
  set W : ℕ → Submodule K E := fun i => U ⊔ Submodule.span K (Set.range fun j : Fin i => w j)
    with hW
  have hex : ∃ r, w r ∈ W r := by
    by_contra hno
    push_neg at hno
    have hmono : ∀ i, i ≤ Module.finrank K (W i) := by
      intro i
      induction i with
      | zero => exact Nat.zero_le _
      | succ i ih =>
        have hlt : W i < W (i + 1) := by
          refine lt_of_le_of_ne ?_ ?_
          · refine sup_le_sup_left (Submodule.span_mono ?_) _
            rintro _ ⟨j, rfl⟩
            exact ⟨Fin.castSucc j, rfl⟩
          · intro heq
            apply hno i
            rw [heq]
            exact Submodule.mem_sup_right (Submodule.subset_span ⟨Fin.last i, rfl⟩)
        have := Submodule.finrank_lt_finrank_of_lt hlt
        omega
    have h1 := hmono (Module.finrank K E + 1)
    have h2 := Submodule.finrank_le (W (Module.finrank K E + 1))
    omega
  obtain ⟨r, hr, hmin⟩ : ∃ r, w r ∈ W r ∧ ∀ i < r, w i ∉ W i :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := by
    refine ⟨r - 1, ?_⟩
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · exfalso
      subst h0
      apply hw0
      simpa [W, w] using hr
    · omega
  obtain ⟨u, hu, y, hy, hsum⟩ := Submodule.mem_sup.mp hr
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hy
  have ha0 : a 0 ≠ 0 := by
    intro ha
    obtain ⟨u', hu'U, hu'⟩ := exists_mem_span_fixed_sub_smul_eq p ψ hψs 0 u hu
    rw [zero_smul, sub_zero] at hu'
    choose b hb using fun i : Fin (s + 1) => exists_pow_char_sub_mul_eq (K := K) p 0 (a i)
    simp only [zero_mul, sub_zero] at hb
    apply hmin s (by omega)
    have key : ψ (w s) = ψ (u' + ∑ i : Fin s, b i.succ • w i) := by
      rw [← hwsucc, ← hsum, map_add, hu', map_sum, Fin.sum_univ_succ, ha, zero_smul, zero_add]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hψs, hb, ← hwsucc]
      rfl
    rw [hψi key]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hu'U) (Submodule.mem_sup_right
      (Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))))
  set a' : ℕ → K := fun i => if h : i < s + 1 then a ⟨i, h⟩ else 0 with ha'
  have ha'0 : a' 0 = a 0 := by simp [a']
  have hsum' : u + ∑ i ∈ Finset.range (s + 1), a' i • w i = w (s + 1) := by
    rw [← hsum, ← Fin.sum_univ_eq_sum_range (fun i => a' i • w i) (s + 1)]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [ha', dif_pos i.2, Fin.eta]
  let Xs : ℕ → Polynomial K := fun n => Nat.rec (Polynomial.C (a' 0) * Polynomial.X ^ p)
    (fun i P => P ^ p + Polynomial.C (a' (i + 1)) * Polynomial.X ^ p) n
  have hXs0 : Xs 0 = Polynomial.C (a' 0) * Polynomial.X ^ p := rfl
  have hXsS : ∀ i, Xs (i + 1) = Xs i ^ p + Polynomial.C (a' (i + 1)) * Polynomial.X ^ p :=
    fun i => rfl
  have h2p : 2 ≤ p := hp.out.two_le
  have hdvd : ∀ i, Polynomial.X ^ p ∣ Xs i := by
    intro i
    induction i with
    | zero => rw [hXs0]; exact dvd_mul_left _ _
    | succ i ih =>
      rw [hXsS]
      exact dvd_add (ih.trans (dvd_pow_self _ hp.out.ne_zero)) (dvd_mul_left _ _)
  have hdeg : ∀ i, (Xs i).natDegree = p ^ (i + 1) := by
    intro i
    induction i with
    | zero =>
      rw [hXs0, Polynomial.natDegree_C_mul_X_pow _ _ (by rwa [ha'0]), pow_one]
    | succ i ih =>
      have hle : p ≤ p ^ (i + 1) := by
        calc p = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ (i + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      rw [hXsS, Polynomial.natDegree_add_eq_left_of_natDegree_lt, Polynomial.natDegree_pow, ih,
        ← pow_succ']
      rw [Polynomial.natDegree_pow, ih]
      calc (Polynomial.C (a' (i + 1)) * Polynomial.X ^ p).natDegree ≤ p :=
            (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_pow_le p)
        _ < p * p ^ (i + 1) := by nlinarith
  obtain ⟨h, hh⟩ : Polynomial.X ^ 2 ∣ Xs s := (pow_dvd_pow _ h2p).trans (hdvd s)
  have hh0 : h ≠ 0 := by
    rintro rfl
    have := hdeg s
    rw [hh, mul_zero, Polynomial.natDegree_zero] at this
    exact absurd this.symm (pow_ne_zero _ hp.out.ne_zero)
  set g : Polynomial K := Polynomial.X * h - Polynomial.C 1 with hg
  have hgdeg : g.natDegree = h.natDegree + 1 := by
    rw [hg, Polynomial.natDegree_sub_C, Polynomial.natDegree_X_mul hh0]
  have hgne : g ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hgdeg
    omega
  have hgd : g.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hgne, hgdeg]
    exact_mod_cast Nat.succ_ne_zero h.natDegree
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_root g hgd
  have hth : t * h.eval t = 1 := by
    simpa [g, Polynomial.IsRoot, sub_eq_zero] using ht
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at hth
  set x : ℕ → K := fun i => (Xs i).eval t with hx
  have hx0 : x 0 = a' 0 * t ^ p := by simp [x, hXs0]
  have hxS : ∀ i, x (i + 1) = x i ^ p + a' (i + 1) * t ^ p := by
    intro i
    simp [x, hXsS]
  have hxs : x s = t := by
    simp only [x, hh, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    linear_combination t * hth
  set y : E := ∑ i ∈ Finset.range (s + 1), x i • w i with hy'
  have hψy : ψ y = t ^ p • u + y := by
    have e1 : ψ y = ∑ i ∈ Finset.range (s + 1), x i ^ p • w (i + 1) := by
      rw [hy', map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hψs, hwsucc]
    rw [e1, Finset.sum_range_succ, hxs, ← hsum', hy', Finset.sum_range_succ',
      Finset.sum_range_succ', hx0]
    simp only [hxS, add_smul, Finset.sum_add_distrib, smul_add, Finset.smul_sum, smul_smul,
      mul_comm (t ^ p)]
    abel
  have hyU : y ∉ U := by
    intro hyU'
    apply hmin s (by omega)
    have hsplit : y = ∑ i ∈ Finset.range s, x i • w i + t • w s := by
      rw [hy', Finset.sum_range_succ, hxs]
    have hmemS : ∑ i ∈ Finset.range s, x i • w i ∈ W s := by
      apply Submodule.mem_sup_right
      rw [← Fin.sum_univ_eq_sum_range (fun i => x i • w i) s]
      exact Submodule.sum_mem _
        (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    have htw : t • w s ∈ W s := by
      have e2 : t • w s = y - ∑ i ∈ Finset.range s, x i • w i := by
        rw [hsplit]
        abel
      rw [e2]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left hyU') hmemS
    have h3 := Submodule.smul_mem _ t⁻¹ htw
    rwa [smul_smul, inv_mul_cancel₀ ht0, one_smul] at h3
  obtain ⟨z, hzU, hz⟩ := exists_mem_span_fixed_sub_smul_eq p ψ hψs 1 (-(t ^ p • u)) (U.neg_mem (U.smul_mem _ hu))
  have hz' : ψ z = z - t ^ p • u := by
    rw [one_smul, sub_eq_iff_eq_add] at hz
    rw [hz]
    abel
  have hfix : ψ (y + z) = y + z := by
    rw [map_add, hψy, hz']
    abel
  apply hyU
  have hyz : y + z ∈ U := Submodule.subset_span hfix
  have h4 := U.sub_mem hyz hzU
  simpa using h4

/- English proof (translation)
Establish `hp0 : p ≠ 0` using `(Fact.out : p.Prime).ne_zero`. Establish `hNN : N * N⁻¹ = 1` using `Matrix.mul_nonsing_inv N hN`. Set `ψ : (Fin d → K) →+ (Fin d → K)` to `{ toFun := fun v => Matrix.mulVec N⁻¹ (fun i => v i ^ p) map_zero' := by`. Establish `e : (fun i => (0 : Fin d → K) i ^ p) = 0`. Use extensionality with `i`.

Simplify using `[hp0]`. Simplify using `only [e, Matrix.mulVec_zero]`. Use the proof step `map_add' := by`. Introduce `u v`. Establish `e : (fun i => (u + v) i ^ p) = (fun i => u i ^ p) + (fun i => v i ^ p)`.

Use extensionality with `i`. Simplify using `[add_pow_char]`. Simplify using `only [e, Matrix.mulVec_add] }`. Establish `hψ : ∀ v, ψ v = Matrix.mulVec N⁻¹ (fun i => v i ^ p)` using `fun v => rfl`. Establish `hback : ∀ v, Matrix.mulVec N (ψ v) = fun i => v i ^ p`.

Introduce `v`. Rewrite using `[hψ, Matrix.mulVec_mulVec, hNN, Matrix.one_mulVec]`. Establish `hψs : ∀ (c : K) (v : Fin d → K), ψ (c • v) = c ^ p • ψ v`. Introduce `c v`. Establish `e : (fun i => (c • v) i ^ p) = c ^ p • (fun i => v i ^ p)`.

Use extensionality with `i`. Simplify using `[mul_pow]`. Rewrite using `[hψ, hψ, e, Matrix.mulVec_smul]`. Establish `hψi : Function.Injective ψ`. Introduce `u v huv`.

Establish `e` using `congrArg (fun z => Matrix.mulVec N z) huv`. Simplify using `only [hback] at e`. Use extensionality with `i`. Conclude with `frobenius_inj K p (congrFun e i)`. Establish `hspan` using `span_fixed_eq_whole_of_semilinear_injective (K := K) p ψ hψs hψi`.

Take `⟨b, hbS, hbspan, hbli⟩` from `exists_linearIndependent K {v : Fin d → K | ψ v = v}`. Establish `htop : ⊤ ≤ Submodule.span K (Set.range ((↑) : b → (Fin d → K)))`. Rewrite using `[Subtype.range_coe, hbspan, hspan]`. Set `B` to `Module.Basis.mk hbli htop`. Set `e` to `B.reindex (B.indexEquiv (Pi.basisFun K (Fin d)))`.

Establish `heS : ∀ j, ψ (e j) = e j`. Introduce `j`. Establish `: (e j : Fin d → K) ∈ b`. Simplify using `only [e, B, Module.Basis.reindex_apply, Module.Basis.mk_apply]`. Conclude with `Subtype.mem _`.

Conclude with `hbS this`. Use `⟨Matrix.of fun i j => e j i, ?_, ?_⟩` and prove the remaining obligations. Establish `hli : LinearIndependent K (fun j => Matrix.transpose (Matrix.of fun i j => e j i) j)`. Establish `: (fun j => Matrix.transpose (Matrix.of fun i j => e j i) j) = fun j => e j`. Use extensionality with `j i`.

Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `e.linearIndependent`. Conclude with `(Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_cols_iff_isUnit.mp hli)`. Use extensionality with `i j`.

Establish `h1` using `congrFun (hback (e j)) i`. Rewrite `h1` using `[heS]`. Simplify using `only [Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply]`. Rewrite using `[← h1]`. Simplify using `[Matrix.mulVec, dotProduct]`.
-/
private theorem exists_matrix_frob_map_eq_mul {K : Type} [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime]
    [CharP K p] (d : ℕ) (N : Matrix (Fin d) (Fin d) K) (hN : IsUnit N.det) :
    ∃ V : Matrix (Fin d) (Fin d) K, IsUnit V.det ∧ V.map (fun x => x ^ p) = N * V := by
  classical
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hNN : N * N⁻¹ = 1 := Matrix.mul_nonsing_inv N hN
  let ψ : (Fin d → K) →+ (Fin d → K) :=
    { toFun := fun v => Matrix.mulVec N⁻¹ (fun i => v i ^ p)
      map_zero' := by
        have e : (fun i => (0 : Fin d → K) i ^ p) = 0 := by
          ext i
          simp [hp0]
        simp only [e, Matrix.mulVec_zero]
      map_add' := by
        intro u v
        have e : (fun i => (u + v) i ^ p) = (fun i => u i ^ p) + (fun i => v i ^ p) := by
          ext i
          simp [add_pow_char]
        simp only [e, Matrix.mulVec_add] }
  have hψ : ∀ v, ψ v = Matrix.mulVec N⁻¹ (fun i => v i ^ p) := fun v => rfl
  have hback : ∀ v, Matrix.mulVec N (ψ v) = fun i => v i ^ p := by
    intro v
    rw [hψ, Matrix.mulVec_mulVec, hNN, Matrix.one_mulVec]
  have hψs : ∀ (c : K) (v : Fin d → K), ψ (c • v) = c ^ p • ψ v := by
    intro c v
    have e : (fun i => (c • v) i ^ p) = c ^ p • (fun i => v i ^ p) := by
      ext i
      simp [mul_pow]
    rw [hψ, hψ, e, Matrix.mulVec_smul]
  have hψi : Function.Injective ψ := by
    intro u v huv
    have e := congrArg (fun z => Matrix.mulVec N z) huv
    simp only [hback] at e
    ext i
    exact frobenius_inj K p (congrFun e i)
  have hspan := span_fixed_eq_whole_of_semilinear_injective (K := K) p ψ hψs hψi
  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent K {v : Fin d → K | ψ v = v}
  have htop : ⊤ ≤ Submodule.span K (Set.range ((↑) : b → (Fin d → K))) := by
    rw [Subtype.range_coe, hbspan, hspan]
  let B := Module.Basis.mk hbli htop
  let e := B.reindex (B.indexEquiv (Pi.basisFun K (Fin d)))
  have heS : ∀ j, ψ (e j) = e j := by
    intro j
    have : (e j : Fin d → K) ∈ b := by
      simp only [e, B, Module.Basis.reindex_apply, Module.Basis.mk_apply]
      exact Subtype.mem _
    exact hbS this
  refine ⟨Matrix.of fun i j => e j i, ?_, ?_⟩
  · have hli : LinearIndependent K (fun j => Matrix.transpose (Matrix.of fun i j => e j i) j) := by
      have : (fun j => Matrix.transpose (Matrix.of fun i j => e j i) j) = fun j => e j := by
        ext j i
        rfl
      rw [this]
      exact e.linearIndependent
    exact (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_cols_iff_isUnit.mp hli)
  · ext i j
    have h1 := congrFun (hback (e j)) i
    rw [heS] at h1
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply]
    rw [← h1]
    simp [Matrix.mulVec, dotProduct]

/- English proof (translation)
Introduce `R _ p hp σ hσ hu hroot d N hN`. Take `⟨hdom, hprime, hcompl, hfrob, hperf⟩` from `hσ`. Establish `hpnu : ¬ IsUnit (p : R)` using `hprime.not_unit`. Establish `hItop : Ideal.span {(p : R)} ≠ ⊤`. Rewrite using `[Ne, Ideal.span_singleton_eq_top]`.

Conclude with `hpnu`. Use `haveI hmax : (Ideal.span {(p : R)}).IsMaximal := by`. Use `⟨⟨hItop, fun J hJ => ?_⟩⟩` and prove the remaining obligations. Take `⟨x, hxJ, hxI⟩` from `SetLike.exists_of_lt hJ`. Conclude with `Ideal.eq_top_of_isUnit_mem J hxJ (hu x hxI)`.

Use `letI : Field (R ⧸ Ideal.span {(p : R)}) := Ideal.Quotient.field _`. Use `haveI : CharP (R ⧸ Ideal.span {(p : R)}) p := CharP.quotient R p (mem_nonunits_iff.mpr hpnu)`. Use `set π := Ideal.Quotient.mk (Ideal.span {(p : R)}) with hπ`. Use `haveI : IsAlgClosed (R ⧸ Ideal.span {(p : R)}) := by`. Use `IsAlgClosed.of_exists_root _ fun P hPm hPirr => ?_` and prove the remaining obligations.

Take `⟨Q, hQmap, hQdeg, hQm⟩` from `Polynomial.lifts_and_natDegree_eq_and_monic ((Polynomial.mem_lifts P).mpr (Polynomial.map_surjective π Ideal.Quotient.mk_surjective P)) hPm`. Take `⟨x, hx⟩` from `hroot Q hQm (by rw [hQdeg]; exact hPirr.natDegree_pos)`. Use `⟨π x, ?_⟩` and prove the remaining obligations. Rewrite using `[← hQmap, Polynomial.eval_map, Polynomial.eval₂_at_apply]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mpr hx`.

Establish `hπσ : ∀ x, π (σ x) = π x ^ p` using `fun x => (Ideal.Quotient.eq.mpr (hfrob x)).trans (map_pow _ _ _)`. Establish `hp0 : π (p : R) = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)`. Establish `hdiv : ∀ (q : R) (M : Matrix (Fin d) (Fin d) R), (∀ i j, M i j ∈ Ideal.span {q}) → ∃ C : Matrix (Fin d) (Fin d) R, M = q • C`. Introduce `q M hM`. Use `choose C hC using fun i j => Ideal.mem_span_singleton'.mp (hM i j)`.

Use `⟨Matrix.of C, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Rewrite using `[Matrix.smul_apply, Matrix.of_apply, ← hC, smul_eq_mul, mul_comm]`. Establish `hσsmul : ∀ (c : R) (M : Matrix (Fin d) (Fin d) R), (c • M).map σ = σ c • M.map σ`. Introduce `c M`.

Use extensionality with `i j`. Simplify using the standard rewrite rules. Establish `hσp : ∀ n : ℕ, σ ((p : R) ^ n) = (p : R) ^ n` using `fun n => by simp`. Establish `hunit : ∀ V : Matrix (Fin d) (Fin d) R, IsUnit (V.map π).det → IsUnit V.det`. Introduce `V hV`.

Use `hu _ fun hmem => hV.ne_zero ?_` and prove the remaining obligations. Establish `h0 : π V.det = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr hmem`. Rewrite `h0` using `[RingHom.map_det, RingHom.mapMatrix_apply]`. Conclude with `h0`. Establish `hNb : IsUnit (N.map π).det`.

Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `hN.map π`. Take `⟨Vb, hVb, hVbeq⟩` from `exists_matrix_frob_map_eq_mul p d (N.map π) hNb`. Establish `step : ∀ (n : ℕ) (V : Matrix (Fin d) (Fin d) R), (V.map π = Vb ∧ ∃ C : Matrix (Fin d) (Fin d) R, V.map σ - N * V = ((p : R) ^ (n + 1)) • C) → ∃ X : Matrix (Fin d) (Fin d) R, ((V + ((p : R) ^ (n + 1)) • X).map π = Vb ∧ ∃ C : Matrix (Fin d) (Fin d) R, (V + ((p : R) ^ (n + 1)) • X). …`. Introduce and unpack `n V ⟨hV, C, hC⟩`.

Establish `hdetV : IsUnit (N * V).det`. Rewrite using `[Matrix.det_mul]`. Conclude with `hN.mul (hunit V (hV ▸ hVb))`. Establish `hND : N * V * (N * V)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hdetV`. Establish `hAS : ∀ c : R, ∃ y e : R, σ y - y + c = (p : R) * e`.

Introduce `c`. Establish `hmon : (Polynomial.X ^ p + (Polynomial.C c - Polynomial.X) : Polynomial R).Monic`. Apply `Polynomial.monic_X_pow_add` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Use `(Polynomial.degree_sub_le _ _).trans (max_le ?_ Polynomial.degree_X_le)` and prove the remaining obligations.

Conclude with `Polynomial.degree_C_le.trans (by norm_num)`. Use `_ < p := by exact_mod_cast hp.out.one_lt`. Establish `hdeg : 0 < (Polynomial.X ^ p + (Polynomial.C c - Polynomial.X) : Polynomial R).natDegree`. Rewrite using `[Polynomial.natDegree_add_eq_left_of_degree_lt, Polynomial.natDegree_X_pow]`. Conclude with `hp.out.pos`.

Rewrite using `[Polynomial.degree_X_pow]`. Combine the equalities or inequalities in the displayed calculation. Use `(Polynomial.degree_sub_le _ _).trans (max_le ?_ Polynomial.degree_X_le)` and prove the remaining obligations. Conclude with `Polynomial.degree_C_le.trans (by norm_num)`. Use `_ < p := by exact_mod_cast hp.out.one_lt`.

Take `⟨y, hy⟩` from `hroot _ hmon hdeg`. Establish `hmem : σ y - y + c ∈ Ideal.span {(p : R)}`. Establish `h2 : y ^ p + (c - y) ∈ Ideal.span {(p : R)}` using `by simpa using hy`. Establish `h3` using `Ideal.add_mem _ (hfrob y) h2`. Use `h3 using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree. Take `⟨e, he⟩` from `Ideal.mem_span_singleton'.mp hmem`. Conclude with `⟨y, e, by rw [← he, mul_comm]⟩`. Use `choose Yf Ef hYE using fun i j => hAS (((N * V)⁻¹ * C) i j)`. Establish `h2 : (Matrix.of Yf).map σ - Matrix.of Yf + (N * V)⁻¹ * C = (p : R) • Matrix.of Ef`.

Use extensionality with `i j`. Simplify using `only [Matrix.add_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]`. Conclude with `hYE i j`. Establish `h2' : N * V * (Matrix.of Yf).map σ = N * V * Matrix.of Yf + (p : R) • (N * V * Matrix.of Ef) - C`. Establish `h4` using `congrArg (fun M => N * V * M) h2`.

Simplify using `only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc, hND, Matrix.one_mul] at h4`. Rewrite using `[← h4]`. Normalize the expressions using the abelian group laws. Establish `h1 : V.map σ = N * V + ((p : R) ^ (n + 1)) • C`. Rewrite using `[← hC]`.

Normalize the expressions using the abelian group laws. Use `⟨V * Matrix.of Yf, ?_, N * V * Matrix.of Ef + ((p : R) ^ n) • (C * (Matrix.of Yf).map σ), ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.map_add _ (map_add π), hV]`. Use `add_zero Vb` and compare the differences between its conclusion and the goal. Use extensionality with `i j`.

Simplify using `[hp0]`. Rewrite using `[Matrix.map_add _ (map_add σ), hσsmul, hσp, Matrix.map_mul, h1]`. Simplify using `only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc]`. Rewrite using `[h2']`. Simplify using `only [smul_add, smul_sub, smul_smul, ← pow_add, ← pow_succ']`.

Establish `e1 : (p : R) ^ (n + 1 + (n + 1)) = (p : R) ^ (n + 1 + 1 + n)` using `by ring`. Establish `e2 : (p : R) ^ (n + 1) * (p : R) = (p : R) ^ (n + 1 + 1)` using `by ring`. Rewrite using `[e1, e2]`. Normalize the expressions using the abelian group laws. Establish `hV0 : ∃ V0 : Matrix (Fin d) (Fin d) R, V0.map π = Vb ∧ ∃ C : Matrix (Fin d) (Fin d) R, V0.map σ - N * V0 = ((p : R) ^ (0 + 1)) • C` using `by set V0 := Vb.map (Function.surjInv (f := π) Ideal.Quotient.mk_surjective) with hV0def`.

Establish `hV0π : V0.map π = Vb`. Use extensionality with `i j`. Simplify using `[V0, Function.surjInv_eq]`. Use `⟨V0, hV0π, hdiv _ _ fun i j => ?_⟩` and prove the remaining obligations. Rewrite using `[zero_add, pow_one, ← Ideal.Quotient.eq_zero_iff_mem]`.

Establish `hm : (V0.map σ - N * V0).map π = 0`. Rewrite using `[Matrix.map_sub _ (map_sub π), Matrix.map_mul, hV0π, ← hVbeq, sub_eq_zero, ← hV0π]`. Use extensionality with `i j`. Simplify using `[hπσ]`. Conclude with `congrFun (congrFun hm i) j`.

Take `⟨V0, hV0⟩` from `hV0`. Use `choose X hX using step`. Set `F : (n : ℕ) → {V : Matrix (Fin d) (Fin d) R // V.map π = Vb ∧ ∃ C : Matrix (Fin d) (Fin d) R, V.map σ - N * V = ((p : R) ^ (n + 1)) • C}` to `fun n => Nat.rec (motive := fun n => {V : Matrix (Fin d) (Fin d) R // V.map π = Vb ∧ ∃ C : Matrix (Fin d) (Fin d) R, V.map σ - N * V = ((p : R) ^ (n + 1)) • C}) ⟨V0, hV0⟩ (fun n W => ⟨W.1 + ((p : R) ^ (n + 1)) • X n W.1 W.2, hX n W.1 W.2⟩) n`. Establish `hF : ∀ n, (F (n + 1)).1 = (F n).1 + ((p : R) ^ (n + 1)) • X n (F n).1 (F n).2` using `fun n => rfl`. Establish `hIpow : ∀ n : ℕ, (Ideal.span {(p : R)} ^ n • ⊤ : Submodule R R) = Ideal.span {(p : R) ^ n}`.

Introduce `n`. Rewrite using `[smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]`. Establish `hcauchy : ∀ m k i j, (F (m + k)).1 i j - (F m).1 i j ∈ Ideal.span {(p : R) ^ m}`. Introduce `m k i j`. Proceed by induction on `k with`.

Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[← add_assoc, hF, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_sub_right_comm]`. Use `Ideal.add_mem _ ih (Ideal.mem_span_singleton.mpr ?_)` and prove the remaining obligations. Conclude with `Dvd.dvd.mul_right (pow_dvd_pow _ (by omega)) _`.

Establish `hlim : ∀ i j, ∃ L : R, ∀ n, (F n).1 i j - L ∈ Ideal.span {(p : R) ^ n}`. Introduce `i j`. Take `⟨L, hL⟩` from `hcompl.toIsPrecomplete.prec (f := fun n => (F n).1 i j) (fun {m n} hmn => by`. Rewrite using `[SModEq.sub_mem, hIpow]`. Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hmn`.

Rewrite using `[← neg_sub]`. Conclude with `neg_mem (hcauchy m k i j))`. Use `⟨L, fun n => ?_⟩` and prove the remaining obligations. Establish `h` using `hL n`. Rewrite `h` using `[SModEq.sub_mem, hIpow]`.

Conclude with `h`. Use `choose L hL using hlim`. Establish `hmulmem : ∀ (q : R) (A M : Matrix (Fin d) (Fin d) R), (∀ i j, M i j ∈ Ideal.span {q}) → ∀ i j, (A * M) i j ∈ Ideal.span {q}`. Introduce `q A M hM i j`. Rewrite using `[Matrix.mul_apply]`.

Conclude with `Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hM k j)`. Establish `hσmem : ∀ (q : ℕ) (x : R), x ∈ Ideal.span {(p : R) ^ q} → σ x ∈ Ideal.span {(p : R) ^ q}`. Introduce `q x hx`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.mp hx`. Rewrite using `[map_mul, hσp]`.

Conclude with `Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)`. Use `⟨Matrix.of L, ?_, ?_⟩` and prove the remaining obligations. Apply `hunit` to reduce the goal to its premises. Establish `h1 : (Matrix.of L).map π = Vb`. Rewrite using `[← (F 1).2.1]`.

Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.of_apply]`. Rewrite using `[eq_comm, Ideal.Quotient.eq]`. Simplify using `using hL i j 1`. Rewrite using `[h1]`.

Conclude with `hVb`. Rewrite using `[← sub_eq_zero]`. Use extensionality with `i j`. Rewrite using `[Matrix.zero_apply]`. Apply `hcompl.toIsHausdorff.haus` to reduce the goal to its premises.

Introduce `n`. Rewrite using `[SModEq.sub_mem, sub_zero, hIpow]`. Take `⟨C, hC⟩` from `(F n).2.2`. Establish `hdiff : ∀ a b, (Matrix.of L - (F n).1) a b ∈ Ideal.span {(p : R) ^ n}`. Introduce `a b`.

Rewrite using `[Matrix.sub_apply, Matrix.of_apply, ← neg_sub]`. Conclude with `neg_mem (hL a b n)`. Establish `hsplit : ((Matrix.of L).map σ - N * Matrix.of L) = ((Matrix.of L - (F n).1).map σ - N * (Matrix.of L - (F n).1)) + ((p : R) ^ (n + 1)) • C`. Rewrite using `[← hC, Matrix.map_sub _ (map_sub σ), Matrix.mul_sub]`. Normalize the expressions using the abelian group laws.

Rewrite using `[hsplit, Matrix.add_apply, Matrix.sub_apply]`. Use `Ideal.add_mem _ (Ideal.sub_mem _ ?_ (hmulmem _ _ _ hdiff i j)) ?_` and prove the remaining obligations. Conclude with `hσmem _ _ (hdiff i j)`. Rewrite using `[Matrix.smul_apply, smul_eq_mul]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton.mpr (pow_dvd_pow _ (by omega)))`.
-/
theorem UpperTheory.Kd.C7.pLangR :
    UpperTheory.Kd.C7.SLangR := by
  intro R _ p hp σ hσ hu hroot d N hN
  obtain ⟨hdom, hprime, hcompl, hfrob, hperf⟩ := hσ
  have hpnu : ¬ IsUnit (p : R) := hprime.not_unit
  have hItop : Ideal.span {(p : R)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact hpnu
  haveI hmax : (Ideal.span {(p : R)}).IsMaximal := by
    refine ⟨⟨hItop, fun J hJ => ?_⟩⟩
    obtain ⟨x, hxJ, hxI⟩ := SetLike.exists_of_lt hJ
    exact Ideal.eq_top_of_isUnit_mem J hxJ (hu x hxI)
  letI : Field (R ⧸ Ideal.span {(p : R)}) := Ideal.Quotient.field _
  haveI : CharP (R ⧸ Ideal.span {(p : R)}) p := CharP.quotient R p (mem_nonunits_iff.mpr hpnu)
  set π := Ideal.Quotient.mk (Ideal.span {(p : R)}) with hπ
  haveI : IsAlgClosed (R ⧸ Ideal.span {(p : R)}) := by
    refine IsAlgClosed.of_exists_root _ fun P hPm hPirr => ?_
    obtain ⟨Q, hQmap, hQdeg, hQm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
      ((Polynomial.mem_lifts P).mpr (Polynomial.map_surjective π Ideal.Quotient.mk_surjective P)) hPm
    obtain ⟨x, hx⟩ := hroot Q hQm (by rw [hQdeg]; exact hPirr.natDegree_pos)
    refine ⟨π x, ?_⟩
    rw [← hQmap, Polynomial.eval_map, Polynomial.eval₂_at_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  have hπσ : ∀ x, π (σ x) = π x ^ p := fun x =>
    (Ideal.Quotient.eq.mpr (hfrob x)).trans (map_pow _ _ _)
  have hp0 : π (p : R) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hdiv : ∀ (q : R) (M : Matrix (Fin d) (Fin d) R), (∀ i j, M i j ∈ Ideal.span {q}) →
      ∃ C : Matrix (Fin d) (Fin d) R, M = q • C := by
    intro q M hM
    choose C hC using fun i j => Ideal.mem_span_singleton'.mp (hM i j)
    refine ⟨Matrix.of C, ?_⟩
    ext i j
    rw [Matrix.smul_apply, Matrix.of_apply, ← hC, smul_eq_mul, mul_comm]
  have hσsmul : ∀ (c : R) (M : Matrix (Fin d) (Fin d) R), (c • M).map σ = σ c • M.map σ := by
    intro c M
    ext i j
    simp
  have hσp : ∀ n : ℕ, σ ((p : R) ^ n) = (p : R) ^ n := fun n => by simp
  have hunit : ∀ V : Matrix (Fin d) (Fin d) R, IsUnit (V.map π).det → IsUnit V.det := by
    intro V hV
    refine hu _ fun hmem => hV.ne_zero ?_
    have h0 : π V.det = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [RingHom.map_det, RingHom.mapMatrix_apply] at h0
    exact h0
  have hNb : IsUnit (N.map π).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hN.map π
  obtain ⟨Vb, hVb, hVbeq⟩ := exists_matrix_frob_map_eq_mul p d (N.map π) hNb
  have step : ∀ (n : ℕ) (V : Matrix (Fin d) (Fin d) R), (V.map π = Vb ∧
      ∃ C : Matrix (Fin d) (Fin d) R, V.map σ - N * V = ((p : R) ^ (n + 1)) • C) →
      ∃ X : Matrix (Fin d) (Fin d) R, ((V + ((p : R) ^ (n + 1)) • X).map π = Vb ∧
        ∃ C : Matrix (Fin d) (Fin d) R, (V + ((p : R) ^ (n + 1)) • X).map σ -
          N * (V + ((p : R) ^ (n + 1)) • X) = ((p : R) ^ (n + 1 + 1)) • C) := by
    rintro n V ⟨hV, C, hC⟩
    have hdetV : IsUnit (N * V).det := by
      rw [Matrix.det_mul]
      exact hN.mul (hunit V (hV ▸ hVb))
    have hND : N * V * (N * V)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdetV
    have hAS : ∀ c : R, ∃ y e : R, σ y - y + c = (p : R) * e := by
      intro c
      have hmon : (Polynomial.X ^ p + (Polynomial.C c - Polynomial.X) : Polynomial R).Monic := by
        apply Polynomial.monic_X_pow_add
        calc (Polynomial.C c - Polynomial.X : Polynomial R).degree ≤ 1 := by
              refine (Polynomial.degree_sub_le _ _).trans (max_le ?_ Polynomial.degree_X_le)
              exact Polynomial.degree_C_le.trans (by norm_num)
          _ < p := by exact_mod_cast hp.out.one_lt
      have hdeg : 0 < (Polynomial.X ^ p + (Polynomial.C c - Polynomial.X) : Polynomial R).natDegree := by
        rw [Polynomial.natDegree_add_eq_left_of_degree_lt, Polynomial.natDegree_X_pow]
        · exact hp.out.pos
        · rw [Polynomial.degree_X_pow]
          calc (Polynomial.C c - Polynomial.X : Polynomial R).degree ≤ 1 := by
                refine (Polynomial.degree_sub_le _ _).trans (max_le ?_ Polynomial.degree_X_le)
                exact Polynomial.degree_C_le.trans (by norm_num)
            _ < p := by exact_mod_cast hp.out.one_lt
      obtain ⟨y, hy⟩ := hroot _ hmon hdeg
      have hmem : σ y - y + c ∈ Ideal.span {(p : R)} := by
        have h2 : y ^ p + (c - y) ∈ Ideal.span {(p : R)} := by simpa using hy
        have h3 := Ideal.add_mem _ (hfrob y) h2
        convert h3 using 1
        ring
      obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.mp hmem
      exact ⟨y, e, by rw [← he, mul_comm]⟩
    choose Yf Ef hYE using fun i j => hAS (((N * V)⁻¹ * C) i j)
    have h2 : (Matrix.of Yf).map σ - Matrix.of Yf + (N * V)⁻¹ * C = (p : R) • Matrix.of Ef := by
      ext i j
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply,
        smul_eq_mul]
      exact hYE i j
    have h2' : N * V * (Matrix.of Yf).map σ =
        N * V * Matrix.of Yf + (p : R) • (N * V * Matrix.of Ef) - C := by
      have h4 := congrArg (fun M => N * V * M) h2
      simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc, hND,
        Matrix.one_mul] at h4
      rw [← h4]
      abel
    have h1 : V.map σ = N * V + ((p : R) ^ (n + 1)) • C := by
      rw [← hC]
      abel
    refine ⟨V * Matrix.of Yf, ?_, N * V * Matrix.of Ef + ((p : R) ^ n) • (C * (Matrix.of Yf).map σ), ?_⟩
    · rw [Matrix.map_add _ (map_add π), hV]
      convert add_zero Vb
      ext i j
      simp [hp0]
    · rw [Matrix.map_add _ (map_add σ), hσsmul, hσp, Matrix.map_mul, h1]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc]
      rw [h2']
      simp only [smul_add, smul_sub, smul_smul, ← pow_add, ← pow_succ']
      have e1 : (p : R) ^ (n + 1 + (n + 1)) = (p : R) ^ (n + 1 + 1 + n) := by ring
      have e2 : (p : R) ^ (n + 1) * (p : R) = (p : R) ^ (n + 1 + 1) := by ring
      rw [e1, e2]
      abel
  have hV0 : ∃ V0 : Matrix (Fin d) (Fin d) R, V0.map π = Vb ∧
      ∃ C : Matrix (Fin d) (Fin d) R, V0.map σ - N * V0 = ((p : R) ^ (0 + 1)) • C := by
    set V0 := Vb.map (Function.surjInv (f := π) Ideal.Quotient.mk_surjective) with hV0def
    have hV0π : V0.map π = Vb := by
      ext i j
      simp [V0, Function.surjInv_eq]
    refine ⟨V0, hV0π, hdiv _ _ fun i j => ?_⟩
    rw [zero_add, pow_one, ← Ideal.Quotient.eq_zero_iff_mem]
    have hm : (V0.map σ - N * V0).map π = 0 := by
      rw [Matrix.map_sub _ (map_sub π), Matrix.map_mul, hV0π, ← hVbeq, sub_eq_zero, ← hV0π]
      ext i j
      simp [hπσ]
    exact congrFun (congrFun hm i) j
  obtain ⟨V0, hV0⟩ := hV0
  choose X hX using step
  let F : (n : ℕ) → {V : Matrix (Fin d) (Fin d) R // V.map π = Vb ∧
      ∃ C : Matrix (Fin d) (Fin d) R, V.map σ - N * V = ((p : R) ^ (n + 1)) • C} :=
    fun n => Nat.rec (motive := fun n => {V : Matrix (Fin d) (Fin d) R // V.map π = Vb ∧
      ∃ C : Matrix (Fin d) (Fin d) R, V.map σ - N * V = ((p : R) ^ (n + 1)) • C}) ⟨V0, hV0⟩
      (fun n W => ⟨W.1 + ((p : R) ^ (n + 1)) • X n W.1 W.2, hX n W.1 W.2⟩) n
  have hF : ∀ n, (F (n + 1)).1 = (F n).1 + ((p : R) ^ (n + 1)) • X n (F n).1 (F n).2 := fun n => rfl
  have hIpow : ∀ n : ℕ, (Ideal.span {(p : R)} ^ n • ⊤ : Submodule R R) = Ideal.span {(p : R) ^ n} := by
    intro n
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  have hcauchy : ∀ m k i j, (F (m + k)).1 i j - (F m).1 i j ∈ Ideal.span {(p : R) ^ m} := by
    intro m k i j
    induction k with
    | zero => simp
    | succ k ih =>
      rw [← add_assoc, hF, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_sub_right_comm]
      refine Ideal.add_mem _ ih (Ideal.mem_span_singleton.mpr ?_)
      exact Dvd.dvd.mul_right (pow_dvd_pow _ (by omega)) _
  have hlim : ∀ i j, ∃ L : R, ∀ n, (F n).1 i j - L ∈ Ideal.span {(p : R) ^ n} := by
    intro i j
    obtain ⟨L, hL⟩ := hcompl.toIsPrecomplete.prec (f := fun n => (F n).1 i j) (fun {m n} hmn => by
      rw [SModEq.sub_mem, hIpow]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      rw [← neg_sub]
      exact neg_mem (hcauchy m k i j))
    refine ⟨L, fun n => ?_⟩
    have h := hL n
    rw [SModEq.sub_mem, hIpow] at h
    exact h
  choose L hL using hlim
  have hmulmem : ∀ (q : R) (A M : Matrix (Fin d) (Fin d) R), (∀ i j, M i j ∈ Ideal.span {q}) →
      ∀ i j, (A * M) i j ∈ Ideal.span {q} := by
    intro q A M hM i j
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hM k j)
  have hσmem : ∀ (q : ℕ) (x : R), x ∈ Ideal.span {(p : R) ^ q} → σ x ∈ Ideal.span {(p : R) ^ q} := by
    intro q x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [map_mul, hσp]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  refine ⟨Matrix.of L, ?_, ?_⟩
  · apply hunit
    have h1 : (Matrix.of L).map π = Vb := by
      rw [← (F 1).2.1]
      ext i j
      simp only [Matrix.map_apply, Matrix.of_apply]
      rw [eq_comm, Ideal.Quotient.eq]
      simpa using hL i j 1
    rw [h1]
    exact hVb
  · rw [← sub_eq_zero]
    ext i j
    rw [Matrix.zero_apply]
    apply hcompl.toIsHausdorff.haus
    intro n
    rw [SModEq.sub_mem, sub_zero, hIpow]
    obtain ⟨C, hC⟩ := (F n).2.2
    have hdiff : ∀ a b, (Matrix.of L - (F n).1) a b ∈ Ideal.span {(p : R) ^ n} := by
      intro a b
      rw [Matrix.sub_apply, Matrix.of_apply, ← neg_sub]
      exact neg_mem (hL a b n)
    have hsplit : ((Matrix.of L).map σ - N * Matrix.of L) =
        ((Matrix.of L - (F n).1).map σ - N * (Matrix.of L - (F n).1)) + ((p : R) ^ (n + 1)) • C := by
      rw [← hC, Matrix.map_sub _ (map_sub σ), Matrix.mul_sub]
      abel
    rw [hsplit, Matrix.add_apply, Matrix.sub_apply]
    refine Ideal.add_mem _ (Ideal.sub_mem _ ?_ (hmulmem _ _ _ hdiff i j)) ?_
    · exact hσmem _ _ (hdiff i j)
    · rw [Matrix.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton.mpr (pow_dvd_pow _ (by omega)))
