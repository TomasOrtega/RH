import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.FibreStB

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def psumQ (δ k : ℕ) : MvPolynomial (Fin δ) ℤ :=
  (esymmAlgHom_fin_surjective ℤ (le_refl δ)
    ⟨psum (Fin δ) ℤ k, psum_isSymmetric _ _ _⟩).choose

/- English proof (translation)
Establish `h` using `(esymmAlgHom_fin_surjective ℤ (le_refl δ) ⟨psum (Fin δ) ℤ k, psum_isSymmetric _ _ _⟩).choose_spec`. Establish `h2` using `congrArg Subtype.val h`. Use `first`. Consider the case `(rw [esymmAlgHom_apply] at h2; exact h2)`. Consider the case `exact h2`.

Consider the case `simpa [psumQ, esymmAlgHom_apply] using h2`.
-/
theorem aeval_psumQ (δ k : ℕ) :
    aeval (fun i : Fin δ => esymm (Fin δ) ℤ (i + 1)) (psumQ δ k) = psum (Fin δ) ℤ k := by
  have h := (esymmAlgHom_fin_surjective ℤ (le_refl δ)
    ⟨psum (Fin δ) ℤ k, psum_isSymmetric _ _ _⟩).choose_spec
  have h2 := congrArg Subtype.val h
  first
  | (rw [esymmAlgHom_apply] at h2; exact h2)
  | exact h2
  | simpa [psumQ, esymmAlgHom_apply] using h2

/- English proof (translation)
Establish `h` using `congrArg (aeval f) (aeval_psumQ δ k)`. Rewrite `h` using `[← AlgHom.comp_apply, MvPolynomial.comp_aeval]`. Simplify using `only [MvPolynomial.aeval_esymm_eq_multiset_esymm] at h`. Rewrite using `[h]`. Simplify using `[MvPolynomial.psum]`.
-/
theorem sum_pow_eq_aeval_psumQ {S : Type*} [CommRing S] {δ : ℕ} (f : Fin δ → S) (k : ℕ) :
    ∑ i, f i ^ k =
      aeval (fun i : Fin δ => (Finset.univ.val.map f).esymm (i + 1)) (psumQ δ k) := by
  have h := congrArg (aeval f) (aeval_psumQ δ k)
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval] at h
  simp only [MvPolynomial.aeval_esymm_eq_multiset_esymm] at h
  rw [h]
  simp [MvPolynomial.psum]

/- English proof (translation)
Take `⟨l, rfl⟩ : ∃ l : List S, (l : Multiset S) = s` from `⟨_, (Quotient.exists_rep s).choose_spec⟩`. Rewrite `hn` using `[Multiset.coe_card]`. Substitute `hn` using the available equality. Establish `hs : (Finset.univ.val.map l.get : Multiset S) = (l : Multiset S)` using `by first`. Consider the case `rw [Fin.univ_val_map, List.ofFn_get]`.

Consider the case `simp [Fin.univ_val_map, List.ofFn_get]`. Establish `key` using `sum_pow_eq_aeval_psumQ l.get k`. Rewrite `key` using `[hs]`. Apply the tactic sequence `rw [← key, Finset.sum_eq_multiset_sum, ← hs, Multiset.map_map] <;> rfl`.
-/
theorem multiset_sum_pow_eq {S : Type*} [CommRing S] (s : Multiset S) {n : ℕ}
    (hn : Multiset.card s = n) (k : ℕ) :
    (s.map (· ^ k)).sum = aeval (fun i : Fin n => s.esymm (i + 1)) (psumQ n k) := by
  obtain ⟨l, rfl⟩ : ∃ l : List S, (l : Multiset S) = s := ⟨_, (Quotient.exists_rep s).choose_spec⟩
  rw [Multiset.coe_card] at hn
  subst hn
  have hs : (Finset.univ.val.map l.get : Multiset S) = (l : Multiset S) := by
    first
    | rw [Fin.univ_val_map, List.ofFn_get]
    | simp [Fin.univ_val_map, List.ofFn_get]
  have key := sum_pow_eq_aeval_psumQ l.get k
  rw [hs] at key
  rw [← key, Finset.sum_eq_multiset_sum, ← hs, Multiset.map_map] <;> rfl

def psumC {R : Type*} [CommRing R] (p : Polynomial R) (n k : ℕ) : R :=
  aeval (fun i : Fin n => (-1) ^ (i.val + 1) * p.coeff (n - (i.val + 1))) (psumQ n k)

/- English proof (translation)
Unfold `psumC`. Proceed by induction on `psumQ n k using MvPolynomial.induction_on`. Use `next a => simp`. Use `next P1 P2 h1 h2 => simp only [map_add, h1, h2]`. Use `next P1 i h1 => simp [h1, Polynomial.coeff_map]`.
-/
theorem map_psumC {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (p : Polynomial R)
    (n k : ℕ) : φ (psumC p n k) = psumC (p.map φ) n k := by
  unfold psumC
  induction psumQ n k using MvPolynomial.induction_on
  next a => simp
  next P1 P2 h1 h2 => simp only [map_add, h1, h2]
  next P1 i h1 => simp [h1, Polynomial.coeff_map]

/- English proof (translation)
Rewrite using `[multiset_sum_pow_eq p.roots hroots k, psumC]`. Use `congrArg (fun F => aeval F (psumQ _ k)) (funext fun i => ?_)` and prove the remaining obligations. Establish `hi : (i : ℕ) + 1 ≤ p.natDegree` using `i.isLt`. Rewrite using `[Polynomial.coeff_eq_esymm_roots_of_card hroots (Nat.sub_le _ _), hm.leadingCoeff, Nat.sub_sub_self hi, one_mul, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]`. Simplify using the standard rewrite rules.
-/
theorem sum_roots_pow {K : Type*} [Field K] (p : Polynomial K) (hm : p.Monic)
    (hroots : Multiset.card p.roots = p.natDegree) (k : ℕ) :
    (p.roots.map (· ^ k)).sum = psumC p p.natDegree k := by
  rw [multiset_sum_pow_eq p.roots hroots k, psumC]
  refine congrArg (fun F => aeval F (psumQ _ k)) (funext fun i => ?_)
  have hi : (i : ℕ) + 1 ≤ p.natDegree := i.isLt
  rw [Polynomial.coeff_eq_esymm_roots_of_card hroots (Nat.sub_le _ _), hm.leadingCoeff,
    Nat.sub_sub_self hi, one_mul, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp

variable {ι : Type} [Fintype ι] {Ω : Type*} [Field Ω] {D : ℕ} {x : ι → Ω} {e : Fin (D + 1) → ι}

def Gen.S (G : Gen x e) (j : ℕ) : MvPolynomial (Fin (D + 1)) ℤ :=
  psumC G.P G.P.natDegree j

def Gen.TrP (G : Gen x e) (H : Polynomial (MvPolynomial (Fin (D + 1)) ℤ)) :
    MvPolynomial (Fin (D + 1)) ℤ :=
  ∑ j ∈ Finset.range (H.natDegree + 1), H.coeff j * G.S j

variable [DecidableEq ι] (G : Gen x e)

/- English proof (translation)
Establish `hm : (G.P.map (deh w 0)).Monic` using `G.monic.map _`. Establish `hd : (G.P.map (deh w 0)).natDegree = G.P.natDegree` using `G.monic.natDegree_map _`. Establish `hc : Multiset.card (G.P.map (deh w 0)).roots = (G.P.map (deh w 0)).natDegree` using `by first`. Consider the case `exact Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _)`. Consider the case `exact (IsAlgClosed.splits _).card_roots`.

Consider the case `exact (Polynomial.natDegree_eq_card_roots' (IsAlgClosed.splits _)).symm`. Rewrite using `[sum_roots_pow _ hm hc j, hd, Gen.S, map_psumC]`.
-/
theorem Gen.deh_S {w : Fin (D + 1) → ℂ} (j : ℕ) :
    deh w 0 (G.S j) = ((G.P.map (deh w 0)).roots.map (· ^ j)).sum := by
  have hm : (G.P.map (deh w 0)).Monic := G.monic.map _
  have hd : (G.P.map (deh w 0)).natDegree = G.P.natDegree := G.monic.natDegree_map _
  have hc : Multiset.card (G.P.map (deh w 0)).roots = (G.P.map (deh w 0)).natDegree := by
    first
    | exact Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _)
    | exact (IsAlgClosed.splits _).card_roots
    | exact (Polynomial.natDegree_eq_card_roots' (IsAlgClosed.splits _)).symm
  rw [sum_roots_pow _ hm hc j, hd, Gen.S, map_psumC]

/- English proof (translation)
Establish `hP1 : G.P ≠ 1`. Introduce `h1`. Establish `h2` using `G.root`. Rewrite `h2` using `[h1, Polynomial.eval₂_one]`. Conclude with `one_ne_zero h2`.

Establish `hdecomp : H %ₘ G.P + G.P * (H /ₘ G.P) = H` using `by first`. Consider the case `exact Polynomial.modByMonic_add_div H G.monic`. Consider the case `exact Polynomial.modByMonic_add_div H G.P`. Consider the case `exact Polynomial.modByMonic_add_div H G.P G.monic`. Establish `hr : (H %ₘ G.P).eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ) = 0`.

Establish `h1` using `congrArg (Polynomial.eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ)) hdecomp`. Rewrite `h1` using `[Polynomial.eval₂_add, Polynomial.eval₂_mul, G.root, zero_mul, add_zero, hH]`. Conclude with `h1`. Establish `hcoef` using `G.min (H %ₘ G.P) (Polynomial.natDegree_modByMonic_lt H G.monic hP1) hr`. Establish `hrw : (H %ₘ G.P).map (deh w 0) = 0`.

Use extensionality with `j`. Rewrite using `[Polynomial.coeff_map, Polynomial.coeff_zero]`. Conclude with `hw.ker _ (hcoef j)`. Establish `hPρ : G.P.eval₂ (deh w 0) ρ = 0`. Establish `h3` using `(Polynomial.mem_roots (G.monic.map _).ne_zero).mp hρ`.

Rewrite `h3` using `[Polynomial.IsRoot.def, Polynomial.eval_map]`. Then use the resulting hypothesis. Establish `h2` using `congrArg (Polynomial.eval₂ (deh w 0) ρ) hdecomp`. Rewrite `h2` using `[Polynomial.eval₂_add, Polynomial.eval₂_mul, hPρ, zero_mul, add_zero]`. Rewrite using `[← h2, ← Polynomial.eval_map, hrw, Polynomial.eval_zero]`.
-/
private theorem eval₂_deh_eq_zero_of_mem_roots {w : Fin (D + 1) → ℂ} (hw : G.Good w)
    (H : Polynomial (MvPolynomial (Fin (D + 1)) ℤ))
    (hH : H.eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ) = 0) {ρ : ℂ}
    (hρ : ρ ∈ (G.P.map (deh w 0)).roots) : H.eval₂ (deh w 0) ρ = 0 := by
  have hP1 : G.P ≠ 1 := by
    intro h1
    have h2 := G.root
    rw [h1, Polynomial.eval₂_one] at h2
    exact one_ne_zero h2
  have hdecomp : H %ₘ G.P + G.P * (H /ₘ G.P) = H := by
    first
    | exact Polynomial.modByMonic_add_div H G.monic
    | exact Polynomial.modByMonic_add_div H G.P
    | exact Polynomial.modByMonic_add_div H G.P G.monic
  have hr : (H %ₘ G.P).eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ) = 0 := by
    have h1 := congrArg (Polynomial.eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ)) hdecomp
    rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, G.root, zero_mul, add_zero, hH] at h1
    exact h1
  have hcoef := G.min (H %ₘ G.P) (Polynomial.natDegree_modByMonic_lt H G.monic hP1) hr
  have hrw : (H %ₘ G.P).map (deh w 0) = 0 := by
    ext j
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    exact hw.ker _ (hcoef j)
  have hPρ : G.P.eval₂ (deh w 0) ρ = 0 := by
    have h3 := (Polynomial.mem_roots (G.monic.map _).ne_zero).mp hρ
    rwa [Polynomial.IsRoot.def, Polynomial.eval_map] at h3
  have h2 := congrArg (Polynomial.eval₂ (deh w 0) ρ) hdecomp
  rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, hPρ, zero_mul, add_zero] at h2
  rw [← h2, ← Polynomial.eval_map, hrw, Polynomial.eval_zero]

/- English proof (translation)
Establish `hx : ∀ j, deh x (e 0) (X j) = x j / x (e 0)` using `fun j => by simp [deh]`. Establish `hz : ∀ j, deh (G.zOf w ρ) (e 0) (X j) = G.zOf w ρ j / G.zOf w ρ (e 0)` using `fun j => by simp [deh]`. Establish `hzj : ∀ j, G.zOf w ρ j = w 0 * ((G.Q j).eval₂ (deh w 0) ρ / deh w 0 G.dd)` using `fun j => rfl`. Establish `hd` using `hw.dd`. Establish `h0` using `hw.w0`.

Rewrite using `[hz, hzj, hzj]`. Distinguish the cases in `hxe : x (e 0) = 0`. Establish `hq : ∀ j, (G.Q j).eval₂ (deh w 0) ρ = 0`. Introduce `j`. Use `eval₂_deh_eq_zero_of_mem_roots G hw (G.Q j) ?_ hρ` and prove the remaining obligations.

Rewrite using `[← G.hQ j, hx, hxe, div_zero, mul_zero]`. Simplify using `[hq]`. Establish `hxs : (G.Q (e 0) - Polynomial.C G.dd).eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ) = 0`. Rewrite using `[Polynomial.eval₂_sub, Polynomial.eval₂_C, ← G.hQ (e 0), hx, div_self hxe, mul_one, sub_self]`. Establish `h1` using `eval₂_deh_eq_zero_of_mem_roots G hw _ hxs hρ`.

Rewrite `h1` using `[Polynomial.eval₂_sub, Polynomial.eval₂_C, sub_eq_zero]`. Rewrite using `[h1]`. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `first | done | ring`.
-/
private theorem deh_dd_mul_deh_zOf_X_eq_eval₂_Q {w : Fin (D + 1) → ℂ} (hw : G.Good w) (i : ι) {ρ : ℂ}
    (hρ : ρ ∈ (G.P.map (deh w 0)).roots) :
    deh w 0 G.dd * deh (G.zOf w ρ) (e 0) (X i) = (G.Q i).eval₂ (deh w 0) ρ := by
  have hx : ∀ j, deh x (e 0) (X j) = x j / x (e 0) := fun j => by simp [deh]
  have hz : ∀ j, deh (G.zOf w ρ) (e 0) (X j) = G.zOf w ρ j / G.zOf w ρ (e 0) :=
    fun j => by simp [deh]
  have hzj : ∀ j, G.zOf w ρ j = w 0 * ((G.Q j).eval₂ (deh w 0) ρ / deh w 0 G.dd) := fun j => rfl
  have hd := hw.dd
  have h0 := hw.w0
  rw [hz, hzj, hzj]
  by_cases hxe : x (e 0) = 0
  · have hq : ∀ j, (G.Q j).eval₂ (deh w 0) ρ = 0 := by
      intro j
      refine eval₂_deh_eq_zero_of_mem_roots G hw (G.Q j) ?_ hρ
      rw [← G.hQ j, hx, hxe, div_zero, mul_zero]
    simp [hq]
  · have hxs : (G.Q (e 0) - Polynomial.C G.dd).eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ) = 0 := by
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_C, ← G.hQ (e 0), hx, div_self hxe, mul_one,
        sub_self]
    have h1 := eval₂_deh_eq_zero_of_mem_roots G hw _ hxs hρ
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_C, sub_eq_zero] at h1
    rw [h1]
    field_simp
    first | done | ring

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on`. Use `next a =>`. Apply the tactic sequence `refine ⟨0, Polynomial.C (MvPolynomial.C a), ?_, fun ρ _ => ?_⟩ <;> (rw [pow_zero, one_mul, Polynomial.eval₂_C]; simp [deh])`. Use `next f1 f2 h1 h2 =>`. Take `⟨N1, H1, hx1, hw1⟩` from `h1`.

Take `⟨N2, H2, hx2, hw2⟩` from `h2`. Use `⟨N1 + N2, Polynomial.C (G.dd ^ N2) * H1 + Polynomial.C (G.dd ^ N1) * H2, ?_, fun ρ hρ => ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_C, ← hx1, ← hx2, map_add, map_pow, map_pow]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_C, ← hw1 ρ hρ, ← hw2 ρ hρ, map_add, map_pow, map_pow]`.

Expand and normalize the polynomial expressions, which then agree. Use `next f1 i h1 =>`. Take `⟨N, H, hx1, hw1⟩` from `h1`. Use `⟨N + 1, H * G.Q i, ?_, fun ρ hρ => ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_mul, ← hx1, ← G.hQ i, map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Polynomial.eval₂_mul, ← hw1 ρ hρ, ← deh_dd_mul_deh_zOf_X_eq_eval₂_Q G hw i hρ, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem exists_pow_mul_eq_eval₂_theta {w : Fin (D + 1) → ℂ} (hw : G.Good w) (f : MvPolynomial ι ℤ) :
    ∃ (N : ℕ) (H : Polynomial (MvPolynomial (Fin (D + 1)) ℤ)),
      deh (x ∘ e) 0 G.dd ^ N * deh x (e 0) f = H.eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ) ∧
      ∀ ρ ∈ (G.P.map (deh w 0)).roots,
        deh w 0 G.dd ^ N * deh (G.zOf w ρ) (e 0) f = H.eval₂ (deh w 0) ρ := by
  induction f using MvPolynomial.induction_on
  next a =>
    refine ⟨0, Polynomial.C (MvPolynomial.C a), ?_, fun ρ _ => ?_⟩ <;>
      (rw [pow_zero, one_mul, Polynomial.eval₂_C]; simp [deh])
  next f1 f2 h1 h2 =>
    obtain ⟨N1, H1, hx1, hw1⟩ := h1
    obtain ⟨N2, H2, hx2, hw2⟩ := h2
    refine ⟨N1 + N2, Polynomial.C (G.dd ^ N2) * H1 + Polynomial.C (G.dd ^ N1) * H2, ?_,
      fun ρ hρ => ?_⟩
    · rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_mul, Polynomial.eval₂_C,
        Polynomial.eval₂_C, ← hx1, ← hx2, map_add, map_pow, map_pow]
      ring
    · rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_mul, Polynomial.eval₂_C,
        Polynomial.eval₂_C, ← hw1 ρ hρ, ← hw2 ρ hρ, map_add, map_pow, map_pow]
      ring
  next f1 i h1 =>
    obtain ⟨N, H, hx1, hw1⟩ := h1
    refine ⟨N + 1, H * G.Q i, ?_, fun ρ hρ => ?_⟩
    · rw [Polynomial.eval₂_mul, ← hx1, ← G.hQ i, map_mul]
      ring
    · rw [Polynomial.eval₂_mul, ← hw1 ρ hρ, ← deh_dd_mul_deh_zOf_X_eq_eval₂_Q G hw i hρ, map_mul]
      ring

/- English proof (translation)
Take `⟨N, H, hx, hwr⟩` from `exists_pow_mul_eq_eval₂_theta G hw f`. Establish `hker : deh (x ∘ e) 0 (G.dd ^ N * g - G.TrP H) = 0`. Rewrite using `[map_sub, map_mul, h, ← hTr H, ← hx, ← hsc, map_pow, sub_self]`. Establish `hwk` using `hw.ker _ hker`. Rewrite `hwk` using `[map_sub, map_mul, map_pow, sub_eq_zero]`.

Establish `hTrw : deh w 0 (G.TrP H) = ((G.P.map (deh w 0)).roots.map fun ρ => H.eval₂ (deh w 0) ρ).sum`. Rewrite using `[Gen.TrP, map_sum]`. Simplify using `only [map_mul, G.deh_S, Polynomial.eval₂_eq_sum_range]`. Generalize the expression as in `(G.P.map (deh w 0)).roots = s`. Use `Multiset.induction_on s ?_ ?_` and prove the remaining obligations.

Simplify using the standard rewrite rules. Introduce `a s ih`. Simplify using `[Multiset.map_cons, Multiset.sum_cons, mul_add, Finset.sum_add_distrib, ih]`. Establish `hdN : deh w 0 G.dd ^ N ≠ 0` using `pow_ne_zero _ hw.dd`. Apply `mul_left_cancel₀ hdN` to reduce the goal to its premises.

Rewrite using `[hwk, hTrw, ← Multiset.sum_map_mul_left]`. Use `congr 1`. Conclude with `Multiset.map_congr rfl fun ρ hρ => (hwr ρ hρ).symm`.
-/
theorem Gen.trace_w {w : Fin (D + 1) → ℂ} (hw : G.Good w) (Tr : Ω → Ω)
    (hTr : ∀ H, Tr (H.eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ)) = deh (x ∘ e) 0 (G.TrP H))
    (hsc : ∀ (m : MvPolynomial (Fin (D + 1)) ℤ) (F : MvPolynomial ι ℤ),
      Tr (deh (x ∘ e) 0 m * deh x (e 0) F) = deh (x ∘ e) 0 m * Tr (deh x (e 0) F))
    {f : MvPolynomial ι ℤ} {g : MvPolynomial (Fin (D + 1)) ℤ}
    (h : deh (x ∘ e) 0 g = Tr (deh x (e 0) f)) :
    deh w 0 g = ((G.P.map (deh w 0)).roots.map fun ρ => deh (G.zOf w ρ) (e 0) f).sum := by
  obtain ⟨N, H, hx, hwr⟩ := exists_pow_mul_eq_eval₂_theta G hw f
  have hker : deh (x ∘ e) 0 (G.dd ^ N * g - G.TrP H) = 0 := by
    rw [map_sub, map_mul, h, ← hTr H, ← hx, ← hsc, map_pow, sub_self]
  have hwk := hw.ker _ hker
  rw [map_sub, map_mul, map_pow, sub_eq_zero] at hwk
  have hTrw : deh w 0 (G.TrP H) =
      ((G.P.map (deh w 0)).roots.map fun ρ => H.eval₂ (deh w 0) ρ).sum := by
    rw [Gen.TrP, map_sum]
    simp only [map_mul, G.deh_S, Polynomial.eval₂_eq_sum_range]
    generalize (G.P.map (deh w 0)).roots = s
    refine Multiset.induction_on s ?_ ?_
    · simp
    · intro a s ih
      simp [Multiset.map_cons, Multiset.sum_cons, mul_add, Finset.sum_add_distrib, ih]
  have hdN : deh w 0 G.dd ^ N ≠ 0 := pow_ne_zero _ hw.dd
  apply mul_left_cancel₀ hdN
  rw [hwk, hTrw, ← Multiset.sum_map_mul_left]
  congr 1
  exact Multiset.map_congr rfl fun ρ hρ => (hwr ρ hρ).symm

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

open Polynomial IntermediateField

/- English proof (translation)
Take `⟨a, b, hab, heq⟩` from `Finite.exists_ne_map_eq_of_infinite (fun n : ℤ => F⟮α + (n : E) * β⟯)`. Establish `ha : α + (a : E) * β ∈ F⟮α + (b : E) * β⟯`. Rewrite using `[← heq]`. Conclude with `IntermediateField.mem_adjoin_simple_self F _`. Establish `hb : α + (b : E) * β ∈ F⟮α + (b : E) * β⟯` using `IntermediateField.mem_adjoin_simple_self F _`.

Establish `hne : (a : E) - b ≠ 0`. Rewrite using `[sub_ne_zero]`. Conclude with `hab` after adjusting the coercions. Establish `hβ : β ∈ F⟮α + (b : E) * β⟯`. Establish `hsub` using `sub_mem ha hb`.

Establish `h1 : (α + (a : E) * β) - (α + (b : E) * β) = ((a : E) - b) * β` using `by ring`. Rewrite `hsub` using `[h1]`. Establish `hc : (a : E) - b ∈ F⟮α + (b : E) * β⟯` using `sub_mem (intCast_mem _ a) (intCast_mem _ b)`. Use `mul_mem (inv_mem hc) hsub` as an intermediate fact. Rewrite `this` using `[← mul_assoc, inv_mul_cancel₀ hne, one_mul]`. Then use the resulting hypothesis.

Use `⟨b, ?_, hβ⟩` and prove the remaining obligations. Use `sub_mem hb (mul_mem (intCast_mem _ b) hβ)` as an intermediate fact. Simplify using `using this`.
-/
private lemma exists_int_primitive_element_pair {F E : Type*} [Field F] [Field E] [Algebra F E]
    [CharZero E] [Finite (IntermediateField F E)] (α β : E) :
    ∃ n : ℤ, α ∈ F⟮α + (n : E) * β⟯ ∧ β ∈ F⟮α + (n : E) * β⟯ := by
  obtain ⟨a, b, hab, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n : ℤ => F⟮α + (n : E) * β⟯)
  have ha : α + (a : E) * β ∈ F⟮α + (b : E) * β⟯ := by
    rw [← heq]; exact IntermediateField.mem_adjoin_simple_self F _
  have hb : α + (b : E) * β ∈ F⟮α + (b : E) * β⟯ := IntermediateField.mem_adjoin_simple_self F _
  have hne : (a : E) - b ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hab
  have hβ : β ∈ F⟮α + (b : E) * β⟯ := by
    have hsub := sub_mem ha hb
    have h1 : (α + (a : E) * β) - (α + (b : E) * β) = ((a : E) - b) * β := by ring
    rw [h1] at hsub
    have hc : (a : E) - b ∈ F⟮α + (b : E) * β⟯ := sub_mem (intCast_mem _ a) (intCast_mem _ b)
    have := mul_mem (inv_mem hc) hsub
    rwa [← mul_assoc, inv_mul_cancel₀ hne, one_mul] at this
  refine ⟨b, ?_, hβ⟩
  have := sub_mem hb (mul_mem (intCast_mem _ b) hβ)
  simpa using this

/- English proof (translation)
Use `haveI hfinite : Finite (IntermediateField F E) := by first`. Consider the case `exact inferInstance`. Consider the case `exact Field.finite_intermediateField_of_exists_primitive_element F E (Field.exists_primitive_element F E)`. Consider the case `exact Field.finite_intermediateField_of_exists_primitive_element (Field.exists_primitive_element F E)`. Consider the case `exact (Field.exists_primitive_element_iff_finite_intermediateField F E).mp ⟨inferInstance, Field.exists_primitive_element F E⟩`.

Consider the case `exact Field.exists_primitive_element_iff_finite_intermediateField.mp ⟨inferInstance, Field.exists_primitive_element F E⟩`. Establish `key : ∀ s : Finset ι, ∃ c : ι → ℤ, ∀ i ∈ s, v i ∈ F⟮∑ j, (c j : E) * v j⟯`. Introduce `s`. Use `Finset.induction_on s ⟨0, by simp⟩ ?_` and prove the remaining obligations. Introduce `j s _ ih`.

Take `⟨c, hc⟩` from `ih`. Take `⟨n, hα, hβ⟩` from `exists_int_primitive_element_pair (F := F) (∑ i, (c i : E) * v i) (v j)`. Use `⟨c + Pi.single j n, ?_⟩` and prove the remaining obligations. Establish `h2 : ∑ i, (((Pi.single j n : ι → ℤ) i : ℤ) : E) * v i = (n : E) * v j`. Rewrite using `[Fintype.sum_eq_single j (fun i hi => by simp [Pi.single_apply, hi])]`.

Simplify using the standard rewrite rules. Establish `hsum : ∑ i, (((c + Pi.single j n : ι → ℤ) i : ℤ) : E) * v i = ∑ i, (c i : E) * v i + (n : E) * v j`. Simplify using `only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib, h2]`. Rewrite using `[hsum]`. Introduce `i hi`.

Break down `Finset.mem_insert.mp hi with rfl | hi` into its components or cases. Conclude with `hβ`. Conclude with `(IntermediateField.adjoin_simple_le_iff.mpr hα) (hc i hi)`. Take `⟨c, hc⟩` from `key Finset.univ`. Use `⟨c, top_le_iff.mp ?_⟩` and prove the remaining obligations.

Rewrite using `[← hv, IntermediateField.adjoin_le_iff]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `hc i (Finset.mem_univ i)`.
-/
theorem exists_int_primitive {F E : Type*} [Field F] [Field E] [Algebra F E] [CharZero F]
    [CharZero E] [FiniteDimensional F E] {ι : Type*} [Fintype ι] (v : ι → E)
    (hv : adjoin F (Set.range v) = ⊤) : ∃ c : ι → ℤ, F⟮∑ i, (c i : E) * v i⟯ = ⊤ := by
  classical
  haveI hfinite : Finite (IntermediateField F E) := by
    first
    | exact inferInstance
    | exact Field.finite_intermediateField_of_exists_primitive_element F E
        (Field.exists_primitive_element F E)
    | exact Field.finite_intermediateField_of_exists_primitive_element
        (Field.exists_primitive_element F E)
    | exact (Field.exists_primitive_element_iff_finite_intermediateField F E).mp
        ⟨inferInstance, Field.exists_primitive_element F E⟩
    | exact Field.exists_primitive_element_iff_finite_intermediateField.mp
        ⟨inferInstance, Field.exists_primitive_element F E⟩
  have key : ∀ s : Finset ι, ∃ c : ι → ℤ, ∀ i ∈ s, v i ∈ F⟮∑ j, (c j : E) * v j⟯ := by
    intro s
    refine Finset.induction_on s ⟨0, by simp⟩ ?_
    intro j s _ ih
    obtain ⟨c, hc⟩ := ih
    obtain ⟨n, hα, hβ⟩ := exists_int_primitive_element_pair (F := F) (∑ i, (c i : E) * v i) (v j)
    refine ⟨c + Pi.single j n, ?_⟩
    have h2 : ∑ i, (((Pi.single j n : ι → ℤ) i : ℤ) : E) * v i = (n : E) * v j := by
      rw [Fintype.sum_eq_single j (fun i hi => by simp [Pi.single_apply, hi])]
      simp
    have hsum : ∑ i, (((c + Pi.single j n : ι → ℤ) i : ℤ) : E) * v i =
        ∑ i, (c i : E) * v i + (n : E) * v j := by
      simp only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib, h2]
    rw [hsum]
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hβ
    · exact (IntermediateField.adjoin_simple_le_iff.mpr hα) (hc i hi)
  obtain ⟨c, hc⟩ := key Finset.univ
  refine ⟨c, top_le_iff.mp ?_⟩
  rw [← hv, IntermediateField.adjoin_le_iff]
  rintro _ ⟨i, rfl⟩
  exact hc i (Finset.mem_univ i)

/- English proof (translation)
Establish `hint : IsIntegral K θ` using `IsIntegral.of_finite K θ`. Establish `hmon` using `minpoly.monic hint`. Establish `hsep : (minpoly K θ).Separable` using `Algebra.IsSeparable.isSeparable K θ`. Establish `hc : Multiset.card ((minpoly K θ).map (algebraMap K (AlgebraicClosure K))).roots = ((minpoly K θ).map (algebraMap K (AlgebraicClosure K))).natDegree` using `by first`. Consider the case `exact Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _)`.

Consider the case `exact (IsAlgClosed.splits _).card_roots`. Consider the case `exact (Polynomial.natDegree_eq_card_roots' (IsAlgClosed.splits _)).symm`. Establish `hnd : ((minpoly K θ).map (algebraMap K (AlgebraicClosure K))).roots.Nodup` using `Polynomial.nodup_roots hsep.map`. Establish `hadj : Algebra.adjoin K {θ} = ⊤` using `by first`. Consider the case `rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hθ, IntermediateField.top_toSubalgebra]`.

Consider the case `rw [← IntermediateField.adjoin_simple_toSubalgebra_of_integral hint, hθ, IntermediateField.top_toSubalgebra]`. Consider the case `rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (fun x hx => (Set.mem_singleton_iff.mp hx) ▸ hint.isAlgebraic), hθ, IntermediateField.top_toSubalgebra]`. Establish `hinj : Function.Injective (fun σ : E →ₐ[K] AlgebraicClosure K => σ θ)`. Introduce `σ τ h`. Conclude with `AlgHom.ext_of_adjoin_eq_top hadj (fun x hx => by rw [Set.mem_singleton_iff.mp hx]; exact h)`.

Establish `hfin : Module.finrank K E = (minpoly K θ).natDegree`. Rewrite using `[← IntermediateField.finrank_top', ← hθ, IntermediateField.adjoin.finrank hint]`. Establish `himg : Finset.univ.image (fun σ : E →ₐ[K] AlgebraicClosure K => σ θ) = ((minpoly K θ).map (algebraMap K (AlgebraicClosure K))).roots.toFinset`. Apply `Finset.eq_of_subset_of_card_le` to reduce the goal to its premises. Introduce `y hy`.

Take `⟨σ, -, rfl⟩` from `Finset.mem_image.mp hy`. Rewrite using `[Multiset.mem_toFinset, Polynomial.mem_roots (hmon.map _).ne_zero]`. Use `first`. Consider the case `rw [Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]`. Consider the case `simp [Polynomial.eval_map, ← Polynomial.aeval_def, Polynomial.aeval_algHom_apply]`.

Rewrite using `[Multiset.toFinset_card_of_nodup hnd, hc, hmon.natDegree_map, Finset.card_image_of_injective _ hinj, Finset.card_univ, ← hfin]`. Conclude with `(AlgHom.card K E (AlgebraicClosure K)).ge`. Apply `(algebraMap K (AlgebraicClosure K)).injective` to reduce the goal to its premises. Rewrite using `[map_psumC, ← hmon.natDegree_map (algebraMap K (AlgebraicClosure K)), ← sum_roots_pow _ (hmon.map _) hc j]`. Use `first`.

Consider the case `rw [trace_eq_sum_embeddings (AlgebraicClosure K)]`. Consider the case `rw [trace_eq_sum_embeddings]`. Consider the case `rw [Algebra.trace_eq_sum_embeddings (AlgebraicClosure K)]`. Simplify using `only [map_pow]`. Establish `hsum` using `Finset.sum_image (s := Finset.univ) (g := fun σ : E →ₐ[K] AlgebraicClosure K => σ θ) (f := fun y => y ^ j) (fun σ _ τ _ h => hinj h)`.

Rewrite `hsum` using `[himg]`. Rewrite using `[← hsum, Finset.sum_eq_multiset_sum, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd]`.
-/
theorem trace_pow_eq_psumC {K E : Type*} [Field K] [Field E] [Algebra K E] [CharZero K]
    [FiniteDimensional K E] {θ : E} (hθ : K⟮θ⟯ = ⊤) (j : ℕ) :
    Algebra.trace K E (θ ^ j) = psumC (minpoly K θ) (minpoly K θ).natDegree j := by
  classical
  have hint : IsIntegral K θ := IsIntegral.of_finite K θ
  have hmon := minpoly.monic hint
  have hsep : (minpoly K θ).Separable := Algebra.IsSeparable.isSeparable K θ
  have hc : Multiset.card ((minpoly K θ).map (algebraMap K (AlgebraicClosure K))).roots =
      ((minpoly K θ).map (algebraMap K (AlgebraicClosure K))).natDegree := by
    first
    | exact Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _)
    | exact (IsAlgClosed.splits _).card_roots
    | exact (Polynomial.natDegree_eq_card_roots' (IsAlgClosed.splits _)).symm
  have hnd : ((minpoly K θ).map (algebraMap K (AlgebraicClosure K))).roots.Nodup :=
    Polynomial.nodup_roots hsep.map
  have hadj : Algebra.adjoin K {θ} = ⊤ := by
    first
    | rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hθ,
        IntermediateField.top_toSubalgebra]
    | rw [← IntermediateField.adjoin_simple_toSubalgebra_of_integral hint, hθ,
        IntermediateField.top_toSubalgebra]
    | rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
          (fun x hx => (Set.mem_singleton_iff.mp hx) ▸ hint.isAlgebraic), hθ,
        IntermediateField.top_toSubalgebra]
  have hinj : Function.Injective (fun σ : E →ₐ[K] AlgebraicClosure K => σ θ) := by
    intro σ τ h
    exact AlgHom.ext_of_adjoin_eq_top hadj (fun x hx => by rw [Set.mem_singleton_iff.mp hx]; exact h)
  have hfin : Module.finrank K E = (minpoly K θ).natDegree := by
    rw [← IntermediateField.finrank_top', ← hθ, IntermediateField.adjoin.finrank hint]
  have himg : Finset.univ.image (fun σ : E →ₐ[K] AlgebraicClosure K => σ θ) =
      ((minpoly K θ).map (algebraMap K (AlgebraicClosure K))).roots.toFinset := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp hy
      rw [Multiset.mem_toFinset, Polynomial.mem_roots (hmon.map _).ne_zero]
      first
      | rw [Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def,
          Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
      | simp [Polynomial.eval_map, ← Polynomial.aeval_def, Polynomial.aeval_algHom_apply]
    · rw [Multiset.toFinset_card_of_nodup hnd, hc, hmon.natDegree_map,
        Finset.card_image_of_injective _ hinj, Finset.card_univ, ← hfin]
      exact (AlgHom.card K E (AlgebraicClosure K)).ge
  apply (algebraMap K (AlgebraicClosure K)).injective
  rw [map_psumC, ← hmon.natDegree_map (algebraMap K (AlgebraicClosure K)),
    ← sum_roots_pow _ (hmon.map _) hc j]
  first
  | rw [trace_eq_sum_embeddings (AlgebraicClosure K)]
  | rw [trace_eq_sum_embeddings]
  | rw [Algebra.trace_eq_sum_embeddings (AlgebraicClosure K)]
  simp only [map_pow]
  have hsum := Finset.sum_image (s := Finset.univ)
    (g := fun σ : E →ₐ[K] AlgebraicClosure K => σ θ) (f := fun y => y ^ j)
    (fun σ _ τ _ h => hinj h)
  rw [himg] at hsum
  rw [← hsum, Finset.sum_eq_multiset_sum, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd]

/- English proof (translation)
Use `choose b hb using fun i => IsLocalization.integerNormalization_map_to_map (M := nonZeroDivisors A) (q i)`. Use `⟨∏ i, (b i : A), fun i => C (∏ j ∈ Finset.univ.erase i, (b j : A)) * IsLocalization.integerNormalization (nonZeroDivisors A) (q i), ?_, fun i => ?_⟩` and prove the remaining obligations. Conclude with `Finset.prod_ne_zero_iff.mpr fun i _ => nonZeroDivisors.coe_ne_zero (b i)`. Rewrite using `[Polynomial.map_mul, hb i, Polynomial.map_C, ← algebraMap_smul K (b i : A) (q i), Polynomial.smul_eq_C_mul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]`. Simplify using `only [map_mul, Polynomial.C_mul, mul_assoc]`.
-/
theorem exists_clear {A K : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] {ι : Type*} [Fintype ι] (q : ι → K[X]) :
    ∃ (b : A) (Q : ι → A[X]), b ≠ 0 ∧
      ∀ i, (Q i).map (algebraMap A K) = C (algebraMap A K b) * q i := by
  classical
  choose b hb using fun i =>
    IsLocalization.integerNormalization_map_to_map (M := nonZeroDivisors A) (q i)
  refine ⟨∏ i, (b i : A), fun i => C (∏ j ∈ Finset.univ.erase i, (b j : A)) *
    IsLocalization.integerNormalization (nonZeroDivisors A) (q i), ?_, fun i => ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun i _ => nonZeroDivisors.coe_ne_zero (b i)
  · rw [Polynomial.map_mul, hb i, Polynomial.map_C, ← algebraMap_smul K (b i : A) (q i),
      Polynomial.smul_eq_C_mul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    simp only [map_mul, Polynomial.C_mul, mul_assoc]

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
