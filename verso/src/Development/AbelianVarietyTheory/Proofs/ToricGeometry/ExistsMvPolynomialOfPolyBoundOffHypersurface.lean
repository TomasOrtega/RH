import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import ReciprocityTheory.ThetaQuasiPeriods.Change
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PolyGrowthStatementPf
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EntireApplyEqOfPeriodicOfSpanReal

open Filter Topology Asymptotics

namespace GlobalTheory

open Filter Topology Asymptotics in
/- English proof (translation)
Use `(pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_` and prove the remaining obligations. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Simplify using `only [Fin.cons_zero]`. Combine the linear relations using `[norm_nonneg x']`. Simplify using `only [Fin.cons_succ]`.

Combine the linear relations using `[norm_le_pi_norm x' i, norm_nonneg j]`.
-/
private theorem norm_cons_le_lemma_4 {d : ℕ} (j : ℂ) (x' : Fin d → ℂ) :
    ‖(Fin.cons j x' : Fin (d + 1) → ℂ)‖ ≤ ‖j‖ + ‖x'‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [Fin.cons_zero]; linarith [norm_nonneg x']
  · simp only [Fin.cons_succ]; linarith [norm_le_pi_norm x' i, norm_nonneg j]

open Filter Topology Asymptotics in
/- English proof (translation)
Establish `h1 : 1 + ‖x‖ ≤ (1 + ‖j‖) * (1 + ‖x'‖)`. Use `norm_cons_le_lemma_4 j x'` as an intermediate fact. Rewrite `this` using `[← hx]`. Use polynomial arithmetic with `[norm_nonneg j, norm_nonneg x']`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem norm_le_of_bound_cons_lemma {d m : ℕ} {C : ℝ} {g : (Fin (d + 1) → ℂ) → ℂ}
    {x : Fin (d + 1) → ℂ} (j : ℂ) (x' : Fin d → ℂ) (hx : x = Fin.cons j x')
    (h : ‖g x‖ ≤ C * (1 + ‖x‖) ^ m) :
    ‖g x‖ ≤ |C| * (1 + ‖j‖) ^ m * (1 + ‖x'‖) ^ m := by
  have h1 : 1 + ‖x‖ ≤ (1 + ‖j‖) * (1 + ‖x'‖) := by
    have := norm_cons_le_lemma_4 j x'
    rw [← hx] at this
    nlinarith [norm_nonneg j, norm_nonneg x']
  calc ‖g x‖ ≤ C * (1 + ‖x‖) ^ m := h
    _ ≤ |C| * (1 + ‖x‖) ^ m := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * ((1 + ‖j‖) * (1 + ‖x'‖)) ^ m :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 m) (abs_nonneg C)
    _ = |C| * (1 + ‖j‖) ^ m * (1 + ‖x'‖) ^ m := by rw [mul_pow, mul_assoc]

open Filter Topology Asymptotics in
/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `r g hn hr hg hb`. Establish `hc : ∀ s, r.eval s ≠ 0`.

Introduce `s h0`. Apply `hr` to reduce the goal to its premises. Rewrite `h0` using `[Polynomial.eq_C_of_natDegree_eq_zero hn, Polynomial.eval_C]`. Rewrite using `[Polynomial.eq_C_of_natDegree_eq_zero hn, h0, map_zero]`. Establish `hU : {s | r.eval s ≠ 0} = Set.univ` using `Set.eq_univ_of_forall hc`.

Rewrite `hg` using `[hU]`. Take `⟨p, hp, hgp⟩` from `_root_.GlobalTheory.entire_exists_polynomial_of_poly_bound (differentiableOn_univ.mp hg) (C := K) (m := m) (fun z => hb z (hc z))`. Conclude with `⟨p, hp, fun s _ => hgp s⟩`. Consider the case `succ n ih`. Introduce `r g hn hr hg hb`.

Take `⟨c, hc⟩` from `Complex.exists_root (f := r) (by`. Rewrite using `[Polynomial.degree_eq_natDegree hr, hn]`. Conclude with `Nat.succ_pos n)` after adjusting the coercions. Use `set r' := r /ₘ (Polynomial.X - Polynomial.C c) with hr'def`. Establish `hfac : (Polynomial.X - Polynomial.C c) * r' = r` using `Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hc`.

Establish `hr'0 : r' ≠ 0`. Introduce and unpack `h`. Apply `hr` to reduce the goal to its premises. Rewrite using `[← hfac, h, mul_zero]`. Establish `hdeg : r'.natDegree = n`.

Use `Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero c) hr'0` as an intermediate fact. Rewrite `this` using `[hfac, hn, Polynomial.natDegree_X_sub_C]`. Use linear arithmetic over natural numbers and integers. Establish `heval : ∀ z, r.eval z = (z - c) * r'.eval z`. Introduce `z`.

Rewrite using `[← hfac, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]`. Establish `hopen : IsOpen {z : ℂ | r'.eval z ≠ 0}` using `isOpen_ne_fun (Polynomial.continuous r') continuous_const`. Establish `hopenr : IsOpen {z : ℂ | r.eval z ≠ 0}` using `isOpen_ne_fun (Polynomial.continuous r) continuous_const`. Use `set g' := Function.update g c (limUnder (𝓝[≠] c) g) with hg'def`. Establish `hoff : ∀ z, z ≠ c → g' z = g z` using `fun z hz => Function.update_of_ne hz _ _`.

Establish `key : r'.eval c ≠ 0 → DifferentiableAt ℂ g' c ∧ ‖g' c‖ ≤ K * (1 + ‖c‖) ^ m`. Introduce `hc'`. Use `set S := {z : ℂ | r'.eval z ≠ 0} ∩ Metric.ball c 1 with hSdef`. Establish `hSn : S ∈ 𝓝 c` using `(hopen.inter Metric.isOpen_ball).mem_nhds ⟨hc', Metric.mem_ball_self one_pos⟩`. Establish `hS : DifferentiableOn ℂ g (S \ {c})`.

Use `hg.mono ?_` and prove the remaining obligations. Introduce and unpack `z ⟨⟨hz1, -⟩, hz2⟩`. Use `show r.eval z ≠ 0`. Rewrite using `[heval]`. Conclude with `mul_ne_zero (sub_ne_zero.mpr hz2) hz1`.

Establish `hbdd : BddAbove (norm ∘ g '' (S \ {c}))`. Use `⟨|K| * (2 + ‖c‖) ^ m, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨z, ⟨⟨hz1, hz3⟩, hz2⟩, rfl⟩`. Establish `hrz : r.eval z ≠ 0`. Rewrite using `[heval]`.

Conclude with `mul_ne_zero (sub_ne_zero.mpr hz2) hz1`. Establish `hzc : ‖z - c‖ < 1` using `mem_ball_iff_norm.mp hz3`. Establish `hzn : ‖z‖ ≤ 1 + ‖c‖`. Use `norm_sub_norm_le z c` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the equalities or inequalities in the displayed calculation. Establish `hU` using `Complex.differentiableOn_update_limUnder_of_bddAbove hSn hS hbdd`. Establish `hd : DifferentiableAt ℂ g' c` using `(hU c (mem_of_mem_nhds hSn)).differentiableAt hSn`. Use `⟨hd, ?_⟩` and prove the remaining obligations. Establish `hcont : ContinuousAt (fun z => ‖g' z‖ - K * (1 + ‖z‖) ^ m) c` using `hd.continuousAt.norm.sub (by fun_prop)`.

Establish `hev : ∀ᶠ z in 𝓝[≠] c, ‖g' z‖ - K * (1 + ‖z‖) ^ m ≤ 0` using `by filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hSn] with z hzc hzS`. Establish `hz : z ≠ c` using `hzc`. Establish `hrz : r.eval z ≠ 0`. Rewrite using `[heval]`. Conclude with `mul_ne_zero (sub_ne_zero.mpr hz) hzS.1`.

Rewrite using `[hoff z hz]`. Combine the linear relations using `[hb z hrz]`. Use `le_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) hev` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hdiff : DifferentiableOn ℂ g' {s | r'.eval s ≠ 0}`.

Introduce `s hs`. Distinguish the cases in `hsc : s = c`. Substitute `hsc` using the available equality. Conclude with `(key hs).1.differentiableWithinAt`. Establish `hrs : r.eval s ≠ 0`.

Rewrite using `[heval]`. Conclude with `mul_ne_zero (sub_ne_zero.mpr hsc) hs`. Establish `hgs : DifferentiableAt ℂ g s` using `(hg s hrs).differentiableAt (hopenr.mem_nhds hrs)`. Establish `heq : g =ᶠ[𝓝 s] g'` using `Filter.eventuallyEq_of_mem (isOpen_ne.mem_nhds hsc) (fun z hz => (hoff z hz).symm)`. Conclude with `(hgs.congr_of_eventuallyEq heq.symm).differentiableWithinAt`.

Establish `hbound : ∀ s, r'.eval s ≠ 0 → ‖g' s‖ ≤ K * (1 + ‖s‖) ^ m`. Introduce `s hs`. Distinguish the cases in `hsc : s = c`. Substitute `hsc` using the available equality. Conclude with `(key hs).2`.

Establish `hrs : r.eval s ≠ 0`. Rewrite using `[heval]`. Conclude with `mul_ne_zero (sub_ne_zero.mpr hsc) hs`. Rewrite using `[hoff s hsc]`. Conclude with `hb s hrs`.

Take `⟨p, hp, hgp⟩` from `ih r' g' hdeg hr'0 hdiff hbound`. Use `⟨p, hp, fun s hs => ?_⟩` and prove the remaining obligations. Establish `hsc : s ≠ c`. Introduce and unpack `rfl`. Apply `hs` to reduce the goal to its premises.

Rewrite using `[heval, sub_self, zero_mul]`. Establish `hs' : r'.eval s ≠ 0`. Introduce `h0`. Apply `hs` to reduce the goal to its premises. Rewrite using `[heval, h0, mul_zero]`.

Rewrite using `[← hoff s hsc]`. Conclude with `hgp s hs'`.
-/
private theorem polynomial_of_bound_off_roots_lemma_2 {m : ℕ} {K : ℝ} :
    ∀ (n : ℕ) (r : Polynomial ℂ) (g : ℂ → ℂ), r.natDegree = n → r ≠ 0 →
      DifferentiableOn ℂ g {s | r.eval s ≠ 0} →
      (∀ s, r.eval s ≠ 0 → ‖g s‖ ≤ K * (1 + ‖s‖) ^ m) →
      ∃ p : Polynomial ℂ, p.natDegree ≤ m ∧ ∀ s, r.eval s ≠ 0 → g s = p.eval s := by
  intro n
  induction n with
  | zero =>
    intro r g hn hr hg hb
    have hc : ∀ s, r.eval s ≠ 0 := by
      intro s h0
      apply hr
      rw [Polynomial.eq_C_of_natDegree_eq_zero hn, Polynomial.eval_C] at h0
      rw [Polynomial.eq_C_of_natDegree_eq_zero hn, h0, map_zero]
    have hU : {s | r.eval s ≠ 0} = Set.univ := Set.eq_univ_of_forall hc
    rw [hU] at hg
    obtain ⟨p, hp, hgp⟩ :=
      _root_.GlobalTheory.entire_exists_polynomial_of_poly_bound (differentiableOn_univ.mp hg) (C := K) (m := m)
        (fun z => hb z (hc z))
    exact ⟨p, hp, fun s _ => hgp s⟩
  | succ n ih =>
    intro r g hn hr hg hb
    obtain ⟨c, hc⟩ := Complex.exists_root (f := r) (by
      rw [Polynomial.degree_eq_natDegree hr, hn]; exact_mod_cast Nat.succ_pos n)
    set r' := r /ₘ (Polynomial.X - Polynomial.C c) with hr'def
    have hfac : (Polynomial.X - Polynomial.C c) * r' = r :=
      Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hc
    have hr'0 : r' ≠ 0 := by
      rintro h; apply hr; rw [← hfac, h, mul_zero]
    have hdeg : r'.natDegree = n := by
      have := Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero c) hr'0
      rw [hfac, hn, Polynomial.natDegree_X_sub_C] at this
      omega
    have heval : ∀ z, r.eval z = (z - c) * r'.eval z := by
      intro z; rw [← hfac, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C]
    have hopen : IsOpen {z : ℂ | r'.eval z ≠ 0} :=
      isOpen_ne_fun (Polynomial.continuous r') continuous_const
    have hopenr : IsOpen {z : ℂ | r.eval z ≠ 0} :=
      isOpen_ne_fun (Polynomial.continuous r) continuous_const
    set g' := Function.update g c (limUnder (𝓝[≠] c) g) with hg'def
    have hoff : ∀ z, z ≠ c → g' z = g z := fun z hz => Function.update_of_ne hz _ _
    have key : r'.eval c ≠ 0 → DifferentiableAt ℂ g' c ∧ ‖g' c‖ ≤ K * (1 + ‖c‖) ^ m := by
      intro hc'
      set S := {z : ℂ | r'.eval z ≠ 0} ∩ Metric.ball c 1 with hSdef
      have hSn : S ∈ 𝓝 c :=
        (hopen.inter Metric.isOpen_ball).mem_nhds ⟨hc', Metric.mem_ball_self one_pos⟩
      have hS : DifferentiableOn ℂ g (S \ {c}) := by
        refine hg.mono ?_
        rintro z ⟨⟨hz1, -⟩, hz2⟩
        show r.eval z ≠ 0
        rw [heval]; exact mul_ne_zero (sub_ne_zero.mpr hz2) hz1
      have hbdd : BddAbove (norm ∘ g '' (S \ {c})) := by
        refine ⟨|K| * (2 + ‖c‖) ^ m, ?_⟩
        rintro _ ⟨z, ⟨⟨hz1, hz3⟩, hz2⟩, rfl⟩
        have hrz : r.eval z ≠ 0 := by
          rw [heval]; exact mul_ne_zero (sub_ne_zero.mpr hz2) hz1
        have hzc : ‖z - c‖ < 1 := mem_ball_iff_norm.mp hz3
        have hzn : ‖z‖ ≤ 1 + ‖c‖ := by
          have := norm_sub_norm_le z c; linarith
        calc ‖g z‖ ≤ K * (1 + ‖z‖) ^ m := hb z hrz
          _ ≤ |K| * (1 + ‖z‖) ^ m := mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
          _ ≤ |K| * (2 + ‖c‖) ^ m :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) m)
              (abs_nonneg K)
      have hU := Complex.differentiableOn_update_limUnder_of_bddAbove hSn hS hbdd
      have hd : DifferentiableAt ℂ g' c := (hU c (mem_of_mem_nhds hSn)).differentiableAt hSn
      refine ⟨hd, ?_⟩
      have hcont : ContinuousAt (fun z => ‖g' z‖ - K * (1 + ‖z‖) ^ m) c :=
        hd.continuousAt.norm.sub (by fun_prop)
      have hev : ∀ᶠ z in 𝓝[≠] c, ‖g' z‖ - K * (1 + ‖z‖) ^ m ≤ 0 := by
        filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hSn] with z hzc hzS
        have hz : z ≠ c := hzc
        have hrz : r.eval z ≠ 0 := by
          rw [heval]; exact mul_ne_zero (sub_ne_zero.mpr hz) hzS.1
        rw [hoff z hz]
        linarith [hb z hrz]
      have := le_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) hev
      linarith
    have hdiff : DifferentiableOn ℂ g' {s | r'.eval s ≠ 0} := by
      intro s hs
      by_cases hsc : s = c
      · subst hsc
        exact (key hs).1.differentiableWithinAt
      · have hrs : r.eval s ≠ 0 := by
          rw [heval]; exact mul_ne_zero (sub_ne_zero.mpr hsc) hs
        have hgs : DifferentiableAt ℂ g s := (hg s hrs).differentiableAt (hopenr.mem_nhds hrs)
        have heq : g =ᶠ[𝓝 s] g' :=
          Filter.eventuallyEq_of_mem (isOpen_ne.mem_nhds hsc) (fun z hz => (hoff z hz).symm)
        exact (hgs.congr_of_eventuallyEq heq.symm).differentiableWithinAt
    have hbound : ∀ s, r'.eval s ≠ 0 → ‖g' s‖ ≤ K * (1 + ‖s‖) ^ m := by
      intro s hs
      by_cases hsc : s = c
      · subst hsc; exact (key hs).2
      · have hrs : r.eval s ≠ 0 := by
          rw [heval]; exact mul_ne_zero (sub_ne_zero.mpr hsc) hs
        rw [hoff s hsc]; exact hb s hrs
    obtain ⟨p, hp, hgp⟩ := ih r' g' hdeg hr'0 hdiff hbound
    refine ⟨p, hp, fun s hs => ?_⟩
    have hsc : s ≠ c := by
      rintro rfl; apply hs; rw [heval, sub_self, zero_mul]
    have hs' : r'.eval s ≠ 0 := by
      intro h0; apply hs; rw [heval, h0, mul_zero]
    rw [← hoff s hsc]; exact hgp s hs'

open Filter Topology Asymptotics in
/- English proof (translation)
Establish `hU : IsOpen ((↑(ρ.roots.toFinset.erase a) : Set ℂ)ᶜ)` using `(Finset.finite_toSet _).isClosed.isOpen_compl`. Establish `ha : a ∈ ((↑(ρ.roots.toFinset.erase a) : Set ℂ)ᶜ)` using `by simp`. Use `filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hU.mem_nhds ha)] with t ht htU h0`. Apply `htU` to reduce the goal to its premises. Simplify using `only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hρ, Polynomial.IsRoot.def, h0, Set.mem_singleton_iff, true_and]`.

Conclude with `ht`.
-/
private theorem polynomial_eventually_ne_zero_lemma_3 {ρ : Polynomial ℂ} (hρ : ρ ≠ 0) (a : ℂ) :
    ∀ᶠ t in 𝓝[≠] a, ρ.eval t ≠ 0 := by
  have hU : IsOpen ((↑(ρ.roots.toFinset.erase a) : Set ℂ)ᶜ) :=
    (Finset.finite_toSet _).isClosed.isOpen_compl
  have ha : a ∈ ((↑(ρ.roots.toFinset.erase a) : Set ℂ)ᶜ) := by simp
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hU.mem_nhds ha)] with t ht htU h0
  apply htU
  simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Multiset.mem_toFinset,
    Polynomial.mem_roots hρ, Polynomial.IsRoot.def, h0, Set.mem_singleton_iff, true_and]
  exact ht

open Filter Topology Asymptotics in

/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`. Introduce `m q f C _ _ _`. Use `⟨MvPolynomial.C (f 0), fun x _ => ?_⟩` and prove the remaining obligations.

Rewrite using `[MvPolynomial.eval_C, Subsingleton.elim x 0]`. Consider the case `succ d ih`. Introduce `m q f C hq hf hb`. Use `set Q := MvPolynomial.finSuccEquiv ℂ d q with hQ`. Establish `hQ0 : Q ≠ 0`.

Rewrite using `[hQ]`. Conclude with `(map_ne_zero_iff _ (MvPolynomial.finSuccEquiv ℂ d).injective).mpr hq`. Use `set qs : ℂ → MvPolynomial (Fin d) ℂ := fun j => Polynomial.eval (MvPolynomial.C j) Q with hqsdef`. Establish `hqs : ∀ j x', MvPolynomial.eval x' (qs j) = MvPolynomial.eval (Fin.cons j x') q`. Introduce `j x'`.

Rewrite using `[MvPolynomial.eval_eq_eval_mv_eval', Polynomial.eval_map, hqsdef, ← Polynomial.eval₂_hom, MvPolynomial.eval_C]`. Establish `hopen : IsOpen {x : Fin (d + 1) → ℂ | MvPolynomial.eval x q ≠ 0}` using `isOpen_ne_fun (MvPolynomial.continuous_eval q) continuous_const`. Use `set B := {j : ℂ | qs j = 0} with hBdef`. Establish `hB : B.Finite`. Use `((Q.roots.toFinset.finite_toSet).preimage (MvPolynomial.C_injective (Fin d) ℂ).injOn).subset ?_` and prove the remaining obligations.

Introduce `j hj`. Simplify using `only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hQ0, Polynomial.IsRoot.def]`. Conclude with `hj`. Use `set emb := hB.infinite_compl.natEmbedding`. Use `set v : ℕ → ℂ := fun k => (emb k : ℂ) with hvdef`.

Establish `hvinj : Function.Injective v` using `Subtype.val_injective.comp emb.injective`. Establish `hvB : ∀ k, qs (v k) ≠ 0` using `fun k => (emb k).2`. Establish `hnode : ∀ k, ∃ P : MvPolynomial (Fin d) ℂ, ∀ x' : Fin d → ℂ, MvPolynomial.eval x' (qs (v k)) ≠ 0 → f (Fin.cons (v k) x') = MvPolynomial.eval x' P`. Introduce `k`. Use `ih m (qs (v k)) (fun x' => f (Fin.cons (v k) x')) (|C| * (1 + ‖v k‖) ^ m) (hvB k) ?_ ?_` and prove the remaining obligations.

Establish `hc : Differentiable ℂ (fun x' : Fin d → ℂ => (Fin.cons (v k) x' : Fin (d + 1) → ℂ))` using `differentiable_pi.2 fun i => Fin.cases (by simpa using differentiable_const (v k)) (fun i => by simpa using differentiable_apply i) i`. Use `hf.comp hc.differentiableOn ?_` and prove the remaining obligations. Introduce `x' hx'`. Use `show MvPolynomial.eval (Fin.cons (v k) x') q ≠ 0`. Rewrite using `[← hqs]`.

Conclude with `hx'`. Introduce `x' hx'`. Rewrite `hx'` using `[hqs]`. Use `norm_le_of_bound_cons_lemma (v k) x' rfl (hb _ hx')` as an intermediate fact. Simplify using `using this`.

Use `choose P hP using hnode`. Use `set s := Finset.range (m + 1) with hsdef`. Use `set Pm : MvPolynomial (Fin (d + 1)) ℂ := ∑ k ∈ s, Polynomial.aeval (MvPolynomial.X 0) (Lagrange.basis s v k) * MvPolynomial.rename Fin.succ (P k) with hPmdef`. Establish `hPm : ∀ x : Fin (d + 1) → ℂ, MvPolynomial.eval x Pm = ∑ k ∈ s, (Lagrange.basis s v k).eval (x 0) * MvPolynomial.eval (Fin.tail x) (P k)`. Introduce `x`.

Establish `hA : ∀ φ : Polynomial ℂ, MvPolynomial.eval x (Polynomial.aeval (MvPolynomial.X 0) φ) = φ.eval (x 0)`. Introduce `φ`. Proceed by induction on `φ using Polynomial.induction_on' with`. Consider the case `add p₁ p₂ h₁ h₂ => simp only [map_add, Polynomial.eval_add, h₁, h₂]`. Consider the case `monomial n a => simp [Polynomial.aeval_monomial, Polynomial.eval_monomial]`.

Rewrite using `[hPmdef, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, MvPolynomial.eval_rename, hA]`. Both sides reduce to the same expression. Establish `hgen : ∀ x : Fin (d + 1) → ℂ, MvPolynomial.eval x q ≠ 0 → (∀ k ∈ s, MvPolynomial.eval (Fin.tail x) (qs (v k)) ≠ 0) → f x = MvPolynomial.eval x Pm`.

Introduce `x hx hxs`. Use `set x' := Fin.tail x`. Establish `hxc : (Fin.cons (x 0) x' : Fin (d + 1) → ℂ) = x` using `Fin.cons_self_tail x`. Use `set r := Polynomial.map (MvPolynomial.eval x') Q with hrdef`. Establish `hr : ∀ t, r.eval t = MvPolynomial.eval (Fin.cons t x') q`.

Introduce `t`. Rewrite using `[MvPolynomial.eval_eq_eval_mv_eval']`. Establish `hr0 : r ≠ 0`. Introduce `h0`. Apply `hx` to reduce the goal to its premises.

Rewrite using `[← hxc, ← hr, h0, Polynomial.eval_zero]`. Establish `hc : Differentiable ℂ (fun t : ℂ => (Fin.cons t x' : Fin (d + 1) → ℂ))` using `differentiable_pi.2 fun i => Fin.cases (by simpa using differentiable_id) (fun i => by simpa using differentiable_const (x' i)) i`. Take `⟨φ, hφdeg, hφ⟩` from `polynomial_of_bound_off_roots_lemma_2 (m := m) (K := |C| * (1 + ‖x'‖) ^ m) r.natDegree r (fun t => f (Fin.cons t x')) rfl hr0 (hf.comp hc.differentiableOn (fun t ht => by show MvPolynomial.eval (Fin.cons t x') q ≠ 0`. Rewrite using `[← hr]`. Conclude with `ht))`.

Use the proof step `(fun t ht => by`. Rewrite `ht` using `[hr]`. Use `norm_le_of_bound_cons_lemma t x' rfl (hb _ ht)` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Establish `hinterp` using `Lagrange.eq_interpolate (s := s) (v := v) (f := φ) hvinj.injOn (by`.

Rewrite using `[hsdef, Finset.card_range]`. Conclude with `(Polynomial.degree_le_of_natDegree_le hφdeg).trans_lt (by exact_mod_cast Nat.lt_succ_self m))`. Establish `hx0 : f x = φ.eval (x 0)`. Use `hφ (x 0) (by rw [hr, hxc]; exact hx)` as an intermediate fact. Rewrite using `[← this, hxc]`.

Rewrite using `[hx0, hinterp, Lagrange.interpolate_apply, Polynomial.eval_finset_sum, hPm]`. Use `Finset.sum_congr rfl fun k hk => ?_` and prove the remaining obligations. Rewrite using `[Polynomial.eval_mul, Polynomial.eval_C, mul_comm]`. Use `congr 1`. Establish `hk' : r.eval (v k) ≠ 0` using `by rw [hr, ← hqs]; exact hxs k hk`.

Rewrite using `[← hφ (v k) hk']`. Conclude with `hP k x' (hxs k hk)`. Use `⟨Pm, fun x hx => ?_⟩` and prove the remaining obligations. Use `set x' := Fin.tail x`. Establish `hxc : (Fin.cons (x 0) x' : Fin (d + 1) → ℂ) = x` using `Fin.cons_self_tail x`.

Use `set R := ∏ k ∈ s, qs (v k) with hRdef`. Establish `hR0 : R ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => hvB k`. Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : ∃ y, MvPolynomial.eval y R ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Conclude with `hR0 (MvPolynomial.funext fun y => by rw [h y, map_zero])`. Use `set w : Fin d → ℂ := y - x'`. Use `set ρ := _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.PG.lineHom x' w R`. Establish `hρ : ∀ t, ρ.eval t = MvPolynomial.eval (fun i => x' i + w i * t) R` using `fun t => _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.PG.eval_lineHom x' w R t`. Establish `hρ0 : ρ ≠ 0`.

Introduce `h0`. Apply `hy` to reduce the goal to its premises. Use `hρ 1` as an intermediate fact. Rewrite `this` using `[h0, Polynomial.eval_zero]`. Establish `hy' : (fun i => x' i + w i * 1) = y`.

Use function extensionality and compare the values at `i`. Simplify using `[w]`. Rewrite `this` using `[hy']`. Conclude with `this.symm`. Use `set γ : ℂ → Fin (d + 1) → ℂ := fun t => Fin.cons (x 0) (fun i => x' i + w i * t)`.

Establish `hγ : Continuous γ`. Use `continuous_pi fun i => Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Simplify `continuous_const` using `[γ]`. Simplify using `only [γ, Fin.cons_succ]`. Use `fun_prop`.

Establish `hγ0 : γ 0 = x`. Simplify using `only [γ, mul_zero, add_zero]`. Conclude with `hxc`. Establish `hfx : ContinuousAt f x` using `(hf x hx).continuousWithinAt.continuousAt (hopen.mem_nhds hx)`. Establish `hγc : Tendsto γ (𝓝 0) (𝓝 x)`.

Use `hγ.tendsto 0` as an intermediate fact. Rewrite `this` using `[hγ0]`. Then use the resulting hypothesis. Establish `h1 : Tendsto (fun t => f (γ t)) (𝓝[≠] 0) (𝓝 (f x))` using `(hfx.tendsto.comp hγc).mono_left nhdsWithin_le_nhds`. Establish `h2 : Tendsto (fun t => MvPolynomial.eval (γ t) Pm) (𝓝[≠] 0) (𝓝 (MvPolynomial.eval x Pm))` using `((MvPolynomial.continuous_eval Pm).continuousAt.tendsto.comp hγc).mono_left nhdsWithin_le_nhds`. Establish `hq : ∀ᶠ t in 𝓝[≠] (0 : ℂ), MvPolynomial.eval (γ t) q ≠ 0`.

Establish `hcq : ContinuousAt (fun t => MvPolynomial.eval (γ t) q) 0` using `((MvPolynomial.continuous_eval q).comp hγ).continuousAt`. Use `hcq.eventually_ne (by simpa [hγ0] using hx)` as an intermediate fact. Conclude with `this.filter_mono nhdsWithin_le_nhds`. Establish `heq : (fun t => f (γ t)) =ᶠ[𝓝[≠] 0] (fun t => MvPolynomial.eval (γ t) Pm)` using `by filter_upwards [hq, polynomial_eventually_ne_zero_lemma_3 hρ0 0] with t ht hρt`. Use `hgen (γ t) ht fun k hk => ?_` and prove the remaining obligations.

Rewrite `hρt` using `[hρ, hRdef, map_prod]`. Use `Finset.prod_ne_zero_iff.mp hρt k hk` as an intermediate fact. Simplify `this` using `[γ, Fin.tail_cons]`. Conclude with `tendsto_nhds_unique_of_eventuallyEq h1 h2 heq`.
-/
theorem _root_.GlobalTheory.exists_mvPolynomial_of_poly_bound_off_hypersurface :
    ∀ (d m : ℕ) (q : MvPolynomial (Fin d) ℂ) (f : (Fin d → ℂ) → ℂ) (C : ℝ), q ≠ 0 →
      DifferentiableOn ℂ f {x | MvPolynomial.eval x q ≠ 0} →
      (∀ x, MvPolynomial.eval x q ≠ 0 → ‖f x‖ ≤ C * (1 + ‖x‖) ^ m) →
      ∃ p : MvPolynomial (Fin d) ℂ, ∀ x, MvPolynomial.eval x q ≠ 0 →
        f x = MvPolynomial.eval x p := by
  intro d
  induction d with
  | zero =>
    intro m q f C _ _ _
    refine ⟨MvPolynomial.C (f 0), fun x _ => ?_⟩
    rw [MvPolynomial.eval_C, Subsingleton.elim x 0]
  | succ d ih =>
    intro m q f C hq hf hb
    set Q := MvPolynomial.finSuccEquiv ℂ d q with hQ
    have hQ0 : Q ≠ 0 := by
      rw [hQ]; exact (map_ne_zero_iff _ (MvPolynomial.finSuccEquiv ℂ d).injective).mpr hq
    set qs : ℂ → MvPolynomial (Fin d) ℂ := fun j => Polynomial.eval (MvPolynomial.C j) Q
      with hqsdef
    have hqs : ∀ j x', MvPolynomial.eval x' (qs j) = MvPolynomial.eval (Fin.cons j x') q := by
      intro j x'
      rw [MvPolynomial.eval_eq_eval_mv_eval', Polynomial.eval_map, hqsdef,
        ← Polynomial.eval₂_hom, MvPolynomial.eval_C]
    have hopen : IsOpen {x : Fin (d + 1) → ℂ | MvPolynomial.eval x q ≠ 0} :=
      isOpen_ne_fun (MvPolynomial.continuous_eval q) continuous_const
    set B := {j : ℂ | qs j = 0} with hBdef
    have hB : B.Finite := by
      refine ((Q.roots.toFinset.finite_toSet).preimage
        (MvPolynomial.C_injective (Fin d) ℂ).injOn).subset ?_
      intro j hj
      simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset,
        Polynomial.mem_roots hQ0, Polynomial.IsRoot.def]
      exact hj
    set emb := hB.infinite_compl.natEmbedding
    set v : ℕ → ℂ := fun k => (emb k : ℂ) with hvdef
    have hvinj : Function.Injective v := Subtype.val_injective.comp emb.injective
    have hvB : ∀ k, qs (v k) ≠ 0 := fun k => (emb k).2
    have hnode : ∀ k, ∃ P : MvPolynomial (Fin d) ℂ, ∀ x' : Fin d → ℂ,
        MvPolynomial.eval x' (qs (v k)) ≠ 0 → f (Fin.cons (v k) x') = MvPolynomial.eval x' P := by
      intro k
      refine ih m (qs (v k)) (fun x' => f (Fin.cons (v k) x')) (|C| * (1 + ‖v k‖) ^ m) (hvB k)
        ?_ ?_
      · have hc : Differentiable ℂ (fun x' : Fin d → ℂ => (Fin.cons (v k) x' : Fin (d + 1) → ℂ)) :=
          differentiable_pi.2 fun i => Fin.cases (by simpa using differentiable_const (v k))
            (fun i => by simpa using differentiable_apply i) i
        refine hf.comp hc.differentiableOn ?_
        intro x' hx'
        show MvPolynomial.eval (Fin.cons (v k) x') q ≠ 0
        rw [← hqs]; exact hx'
      · intro x' hx'
        rw [hqs] at hx'
        have := norm_le_of_bound_cons_lemma (v k) x' rfl (hb _ hx')
        simpa using this
    choose P hP using hnode
    set s := Finset.range (m + 1) with hsdef
    set Pm : MvPolynomial (Fin (d + 1)) ℂ := ∑ k ∈ s,
      Polynomial.aeval (MvPolynomial.X 0) (Lagrange.basis s v k) *
        MvPolynomial.rename Fin.succ (P k) with hPmdef
    have hPm : ∀ x : Fin (d + 1) → ℂ, MvPolynomial.eval x Pm =
        ∑ k ∈ s, (Lagrange.basis s v k).eval (x 0) * MvPolynomial.eval (Fin.tail x) (P k) := by
      intro x
      have hA : ∀ φ : Polynomial ℂ,
          MvPolynomial.eval x (Polynomial.aeval (MvPolynomial.X 0) φ) = φ.eval (x 0) := by
        intro φ
        induction φ using Polynomial.induction_on' with
        | add p₁ p₂ h₁ h₂ => simp only [map_add, Polynomial.eval_add, h₁, h₂]
        | monomial n a => simp [Polynomial.aeval_monomial, Polynomial.eval_monomial]
      rw [hPmdef, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, MvPolynomial.eval_rename, hA]
      rfl
    have hgen : ∀ x : Fin (d + 1) → ℂ, MvPolynomial.eval x q ≠ 0 →
        (∀ k ∈ s, MvPolynomial.eval (Fin.tail x) (qs (v k)) ≠ 0) →
        f x = MvPolynomial.eval x Pm := by
      intro x hx hxs
      set x' := Fin.tail x
      have hxc : (Fin.cons (x 0) x' : Fin (d + 1) → ℂ) = x := Fin.cons_self_tail x
      set r := Polynomial.map (MvPolynomial.eval x') Q with hrdef
      have hr : ∀ t, r.eval t = MvPolynomial.eval (Fin.cons t x') q := by
        intro t; rw [MvPolynomial.eval_eq_eval_mv_eval']
      have hr0 : r ≠ 0 := by
        intro h0; apply hx; rw [← hxc, ← hr, h0, Polynomial.eval_zero]
      have hc : Differentiable ℂ (fun t : ℂ => (Fin.cons t x' : Fin (d + 1) → ℂ)) :=
        differentiable_pi.2 fun i => Fin.cases (by simpa using differentiable_id)
          (fun i => by simpa using differentiable_const (x' i)) i
      obtain ⟨φ, hφdeg, hφ⟩ := polynomial_of_bound_off_roots_lemma_2 (m := m) (K := |C| * (1 + ‖x'‖) ^ m)
        r.natDegree r (fun t => f (Fin.cons t x')) rfl hr0
        (hf.comp hc.differentiableOn (fun t ht => by
          show MvPolynomial.eval (Fin.cons t x') q ≠ 0
          rw [← hr]; exact ht))
        (fun t ht => by
          rw [hr] at ht
          have := norm_le_of_bound_cons_lemma t x' rfl (hb _ ht)
          calc _ ≤ _ := this
            _ = _ := by ring)
      have hinterp := Lagrange.eq_interpolate (s := s) (v := v) (f := φ) hvinj.injOn
        (by
          rw [hsdef, Finset.card_range]
          exact (Polynomial.degree_le_of_natDegree_le hφdeg).trans_lt
            (by exact_mod_cast Nat.lt_succ_self m))
      have hx0 : f x = φ.eval (x 0) := by
        have := hφ (x 0) (by rw [hr, hxc]; exact hx)
        rw [← this, hxc]
      rw [hx0, hinterp, Lagrange.interpolate_apply, Polynomial.eval_finset_sum, hPm]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Polynomial.eval_mul, Polynomial.eval_C, mul_comm]
      congr 1
      have hk' : r.eval (v k) ≠ 0 := by rw [hr, ← hqs]; exact hxs k hk
      rw [← hφ (v k) hk']
      exact hP k x' (hxs k hk)
    refine ⟨Pm, fun x hx => ?_⟩
    set x' := Fin.tail x
    have hxc : (Fin.cons (x 0) x' : Fin (d + 1) → ℂ) = x := Fin.cons_self_tail x
    set R := ∏ k ∈ s, qs (v k) with hRdef
    have hR0 : R ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hvB k
    obtain ⟨y, hy⟩ : ∃ y, MvPolynomial.eval y R ≠ 0 := by
      by_contra h
      push_neg at h
      exact hR0 (MvPolynomial.funext fun y => by rw [h y, map_zero])
    set w : Fin d → ℂ := y - x'
    set ρ := _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.PG.lineHom x' w R
    have hρ : ∀ t, ρ.eval t = MvPolynomial.eval (fun i => x' i + w i * t) R :=
      fun t => _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.PG.eval_lineHom x' w R t
    have hρ0 : ρ ≠ 0 := by
      intro h0
      apply hy
      have := hρ 1
      rw [h0, Polynomial.eval_zero] at this
      have hy' : (fun i => x' i + w i * 1) = y := by
        funext i; simp [w]
      rw [hy'] at this
      exact this.symm
    set γ : ℂ → Fin (d + 1) → ℂ := fun t => Fin.cons (x 0) (fun i => x' i + w i * t)
    have hγ : Continuous γ := by
      refine continuous_pi fun i => Fin.cases ?_ (fun i => ?_) i
      · simpa [γ] using continuous_const
      · simp only [γ, Fin.cons_succ]; fun_prop
    have hγ0 : γ 0 = x := by
      simp only [γ, mul_zero, add_zero]; exact hxc
    have hfx : ContinuousAt f x :=
      (hf x hx).continuousWithinAt.continuousAt (hopen.mem_nhds hx)
    have hγc : Tendsto γ (𝓝 0) (𝓝 x) := by
      have := hγ.tendsto 0
      rwa [hγ0] at this
    have h1 : Tendsto (fun t => f (γ t)) (𝓝[≠] 0) (𝓝 (f x)) :=
      (hfx.tendsto.comp hγc).mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun t => MvPolynomial.eval (γ t) Pm) (𝓝[≠] 0)
        (𝓝 (MvPolynomial.eval x Pm)) :=
      ((MvPolynomial.continuous_eval Pm).continuousAt.tendsto.comp hγc).mono_left
        nhdsWithin_le_nhds
    have hq : ∀ᶠ t in 𝓝[≠] (0 : ℂ), MvPolynomial.eval (γ t) q ≠ 0 := by
      have hcq : ContinuousAt (fun t => MvPolynomial.eval (γ t) q) 0 :=
        ((MvPolynomial.continuous_eval q).comp hγ).continuousAt
      have := hcq.eventually_ne (by simpa [hγ0] using hx)
      exact this.filter_mono nhdsWithin_le_nhds
    have heq : (fun t => f (γ t)) =ᶠ[𝓝[≠] 0] (fun t => MvPolynomial.eval (γ t) Pm) := by
      filter_upwards [hq, polynomial_eventually_ne_zero_lemma_3 hρ0 0] with t ht hρt
      refine hgen (γ t) ht fun k hk => ?_
      rw [hρ, hRdef, map_prod] at hρt
      have := Finset.prod_ne_zero_iff.mp hρt k hk
      simpa [γ, Fin.tail_cons] using this
    exact tendsto_nhds_unique_of_eventuallyEq h1 h2 heq

end GlobalTheory
