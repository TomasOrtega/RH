import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCLoc

namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

/- English proof (translation)
Unfold `KB.mix`. Rewrite using `[Complex.re_sum]`. Use `Finset.sum_le_sum fun u hu => ?_` and prove the remaining obligations. Rewrite using `[Complex.re_ofReal_mul]`. Conclude with `mul_le_mul_of_nonneg_left ((Complex.re_le_norm _).trans ((hB u hu).trans (le_max_left _ _))) (hθ u)`.
-/
theorem re_mix_le (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (ε : ℝ) (i : ℕ) (U : Finset (List C.Letter))
    (θ : List C.Letter → ℝ) (hθ : ∀ a, 0 ≤ θ a) (p : C.LPt) (B : List C.Letter → ℝ)
    (hB : ∀ u ∈ U, ‖KB.gN S v ε i u p p‖ ≤ B u) :
    (KB.mix S v ε i U θ p p).re ≤ ∑ u ∈ U, θ u * max (B u) 0 := by
  unfold KB.mix
  rw [Complex.re_sum]
  refine Finset.sum_le_sum fun u hu => ?_
  rw [Complex.re_ofReal_mul]
  exact mul_le_mul_of_nonneg_left
    ((Complex.re_le_norm _).trans ((hB u hu).trans (le_max_left _ _))) (hθ u)

/- English proof (translation)
Use `set Y : Finset α := {p, q} with hY`. Set `e : Fin 2 → Y` to `![⟨p, by simp [Y]⟩, ⟨q, by simp [Y]⟩]`. Establish `hN` using `Matrix.PosSemidef.submatrix h e`. Establish `hqp : G q p = conj (G p q)`. Establish `h0` using `hN.1.apply 1 0`.

Simplify using `[e] at h0`. Rewrite using `[← h0]`. Distinguish the cases in `hw : G p q = 0`. Rewrite using `[hw, norm_zero, mul_zero]`. Check the signs of the components of the expression.

Use `set w := G p q with hwdef`. Use `set ζ : ℂ := conj w / (‖w‖ : ℂ) with hζ`. Establish `hw' : (‖w‖ : ℂ) ≠ 0` using `by exact_mod_cast (norm_ne_zero_iff.2 hw)`. Establish `hcw : conj w * w = (‖w‖ : ℂ) ^ 2` using `Complex.conj_mul' w`. Establish `h1 : ζ * w = ‖w‖`.

Rewrite using `[hζ, div_mul_eq_mul_div, hcw, pow_two, mul_div_assoc, div_self hw', mul_one]`. Establish `h2 : conj ζ * conj w = ‖w‖`. Rewrite using `[← map_mul, h1, Complex.conj_ofReal]`. Establish `hnz : ‖ζ‖ = 1`. Rewrite using `[hζ, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.2 hw)]`.

Establish `h3 : conj ζ * ζ = 1`. Rewrite using `[Complex.conj_mul', hnz]`. Simplify using the standard rewrite rules. Establish `key` using `hN.re_dotProduct_nonneg ![1, -ζ]`. Establish `hform : star (![1, -ζ] : Fin 2 → ℂ) ⬝ᵥ Matrix.mulVec ((Matrix.of fun x y : Y => G x y).submatrix e e) ![1, -ζ] = G p p - ζ * w - conj ζ * G q p + conj ζ * ζ * G q q`.

Simplify using `[dotProduct, Matrix.mulVec, Fin.sum_univ_two, e, w]`. Apply the tactic sequence `try ring`. Rewrite `key` using `[hform, hqp, h1, h2, h3, one_mul]`. Simplify using `only [RCLike.re_to_complex, Complex.sub_re, Complex.add_re, Complex.ofReal_re] at key`. Establish `ha` using `Complex.re_le_norm (G p p)`.

Establish `hb` using `Complex.re_le_norm (G q q)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private lemma two_mul_norm_le_add_of_psdOn_pair {α : Type} [DecidableEq α] (G : α → α → ℂ) (p q : α) (hpq : p ≠ q)
    (h : TB.PSDOn ({p, q} : Finset α) G) : 2 * ‖G p q‖ ≤ ‖G p p‖ + ‖G q q‖ := by
  set Y : Finset α := {p, q} with hY
  let e : Fin 2 → Y := ![⟨p, by simp [Y]⟩, ⟨q, by simp [Y]⟩]
  have hN := Matrix.PosSemidef.submatrix h e
  have hqp : G q p = conj (G p q) := by
    have h0 := hN.1.apply 1 0
    simp [e] at h0
    rw [← h0]
  by_cases hw : G p q = 0
  · rw [hw, norm_zero, mul_zero]
    positivity
  set w := G p q with hwdef
  set ζ : ℂ := conj w / (‖w‖ : ℂ) with hζ
  have hw' : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hw)
  have hcw : conj w * w = (‖w‖ : ℂ) ^ 2 := Complex.conj_mul' w
  have h1 : ζ * w = ‖w‖ := by
    rw [hζ, div_mul_eq_mul_div, hcw, pow_two, mul_div_assoc, div_self hw', mul_one]
  have h2 : conj ζ * conj w = ‖w‖ := by
    rw [← map_mul, h1, Complex.conj_ofReal]
  have hnz : ‖ζ‖ = 1 := by
    rw [hζ, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.2 hw)]
  have h3 : conj ζ * ζ = 1 := by
    rw [Complex.conj_mul', hnz]
    simp
  have key := hN.re_dotProduct_nonneg ![1, -ζ]
  have hform : star (![1, -ζ] : Fin 2 → ℂ) ⬝ᵥ
      Matrix.mulVec ((Matrix.of fun x y : Y => G x y).submatrix e e) ![1, -ζ] =
      G p p - ζ * w - conj ζ * G q p + conj ζ * ζ * G q q := by
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, e, w]
    try ring
  rw [hform, hqp, h1, h2, h3, one_mul] at key
  simp only [RCLike.re_to_complex, Complex.sub_re, Complex.add_re, Complex.ofReal_re] at key
  have ha := Complex.re_le_norm (G p p)
  have hb := Complex.re_le_norm (G q q)
  linarith

/- English proof (translation)
Distinguish the cases in `hpq : p = q`. Substitute `hpq` using the available equality. Conclude with `hp`. Establish `hps` using `hpos v ε hε j hj w {p, q}`. Establish `hcs` using `two_mul_norm_le_add_of_psdOn_pair (S.gramLoc v ε j (w.1 v)) p q hpq hps`.

Unfold `KB.gN at hp hq ⊢`. Rewrite `hp`, `hq`, the goal using `[norm_div]`. Break down `(norm_nonneg (S.sizeAt v (w.1 v) : ℂ)).eq_or_lt with h0 | hs` into its components or cases. Rewrite `hp`, the goal using `[← h0, div_zero]`. Conclude with `hp`.

Rewrite `hp`, `hq`, the goal using `[div_le_iff₀ hs]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem gN_entry (S : C.HidaSetting E Wp Wq) (hpos : C.ThmPPos S) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r + 1) (w : S.W) (p q : C.LPt) (B : ℝ) (hp : ‖KB.gN S v ε j (w.1 v) p p‖ ≤ B)
    (hq : ‖KB.gN S v ε j (w.1 v) q q‖ ≤ B) : ‖KB.gN S v ε j (w.1 v) p q‖ ≤ B := by
  by_cases hpq : p = q
  · subst hpq
    exact hp
  have hps := hpos v ε hε j hj w {p, q}
  have hcs := two_mul_norm_le_add_of_psdOn_pair (S.gramLoc v ε j (w.1 v)) p q hpq hps
  unfold KB.gN at hp hq ⊢
  rw [norm_div] at hp hq ⊢
  rcases (norm_nonneg (S.sizeAt v (w.1 v) : ℂ)).eq_or_lt with h0 | hs
  · rw [← h0, div_zero] at hp ⊢
    exact hp
  · rw [div_le_iff₀ hs] at hp hq ⊢
    linarith

/- English proof (translation)
Establish `hk : (n - 1) * C.Kst = (n - 2) * C.Kst + C.Kst`. Establish `: n - 1 = (n - 2) + 1` using `by omega`. Rewrite using `[this, add_mul, one_mul]`. Establish `hl2 : b + (n - 1) - 1 = b + n - 2` using `by omega`. Take `⟨Ba, hBa⟩` from `hIH a ha (by omega)`.

Rewrite `hBa` using `[hl2]`. Take `⟨w, rfl⟩` from `exists_word_of_admissible_at_place S ha`. Establish `hsup : ∃ B : ℝ, ∀ p ∈ ({h} : Finset C.LPt), ∀ t : ℂ, t ≠ 0 → ‖KB.gN S v ε (b + n - 2) (w.1 v) (p ++ [(n - 1, t)]) (p ++ [(n - 1, t)])‖ ≤ B` using `⟨Ba, fun p hp t ht => by rw [Finset.mem_singleton] at hp; subst hp; exact hBa t ht⟩`. Take `⟨hcont, Pua, Paa, hblk, ⟨B', hB'⟩, hlim⟩` from `hGL ε hε b n hb hn hbn (w.1 v) ha {h} (by simp [hh]) hsup`. Take `⟨Up, θp, Um, θm, hUp, hUm, hLB⟩` from `hLL b (n - 1) hb (by omega) (by omega) (w.1 v) ha (by omega)`.

Establish `hBu : ∀ u ∈ Up ∪ Um, LocSup S v ε (n - 1) b u h`. Introduce `u hu`. Break down `Finset.mem_union.1 hu with hu | hu` into its components or cases. Conclude with `hIH u (hUp.2 u hu).1 (by have := (hUp.2 u hu).2; omega)`. Conclude with `hIH u (hUm.2 u hu).1 (by have := (hUm.2 u hu).2; omega)`.

Use `choose! Bu hBu' using hBu`. Use `set Bp := ∑ u ∈ Up, θp u * max (Bu u) 0 with hBp`. Use `set Bq := ∑ u ∈ Um, θm u * max (Bu u) 0 with hBq`. Establish `hBp0 : 0 ≤ Bp` using `Finset.sum_nonneg fun u _ => mul_nonneg (hUp.1.1 u) (le_max_right _ _)`. Establish `hBq0 : 0 ≤ Bq` using `Finset.sum_nonneg fun u _ => mul_nonneg (hUm.1.1 u) (le_max_right _ _)`.

Use `set Bt := max (max Ba 0) (Bp + Bq) with hBt`. Establish `hBt0 : 0 ≤ Bt` using `(le_max_right _ _).trans (le_max_left _ _)`. Take `⟨i1, i2, hcov, -⟩` from `pbc_lstdFacts 1 1 one_pos`. Use `i1` as an intermediate fact. Use `i2` as an intermediate fact.

Establish `hgR : (0 : ℝ) < S.g` using `by exact_mod_cast hg`. Take `⟨Lm, j1, j2, hLm⟩` from `GlobalTheory.dual_smul_mem (Lstd 1 1) (S.g : ℝ) hgR.ne'`. Use `j1` as an intermediate fact. Use `j2` as an intermediate fact. Take `⟨Cs, -, hCsum⟩` from `pbc_lstdSum`.

Take `⟨hsm, -⟩` from `hCsum 1 1 (S.g : ℝ) (fun _ => Λ b (n - 1) v) one_pos hgR (fun _ => hΛ0)`. Set `D : Fin 1 → C.LPt → C.LPt → ℂ → ℂ` to `fun _ p q c => KB.gN S v ε (b + n - 1) (w.1 v) (p ++ [(n, c)]) (q ++ [(n, c)])`. Set `U : Fin 1 → C.LPt × ℂ → C.LPt × ℂ → ℂ` to `fun _ p q => KB.gN S v ε (b + n - 2) (w.1 v) (p.1 ++ [(n - 1, p.2⁻¹)]) (q.1 ++ [(n - 1, q.2⁻¹)])`. Establish `hGD : GermData {h} U (fun _ => Pua) (fun _ => Paa) (fun _ σ p q => KB.hatB S v ε b n (w.1 v) σ p q)`. Use `⟨fun _ Xs hXs => hblk Xs hXs, ⟨max Ba B' ⊔ 0, le_max_right _ _, fun _ p hp x hx => ?_⟩, fun _ p hp q hq σ => (hlim p hp q hq σ).1, fun _ p hp q hq σ => (hlim p hp q hq σ).2.1, fun _ p hp q hq σ => (hlim p hp q hq σ).2.2⟩` and prove the remaining obligations.

Rewrite `hp` using `[Finset.mem_singleton]`. Substitute `hp` using the available equality. Use `⟨(hBa x⁻¹ (inv_ne_zero hx)).trans ?_, (hB' p (Finset.mem_singleton_self p) x hx).trans ?_⟩` and prove the remaining obligations. Conclude with `(le_max_left _ _).trans (le_max_left _ _)`. Conclude with `(le_max_right _ _).trans (le_max_left _ _)`.

Establish `hD : ∀ (v' : Fin 1) (z : ℂ), z ≠ 0 → TB.PSDOn ({h} : Finset C.LPt) (fun p q => D v' p q z)`. Introduce `v' z _`. Use `PBB.gN_psd S hpos v ε hε (b + n - 1) (by omega) w (({h} : Finset C.LPt).image fun p => p ++ [(n, z)])` as an intermediate fact. Conclude with `JCx1.decay.psd_pull _ _ this {h} (fun p => p ++ [(n, z)]) (fun p hp => Finset.mem_image_of_mem _ hp)`. Establish `hF : ∀ σ ∈ crystallineComparison.dualSet (Lstd 1 1), ∀ x : crystallineComparison.V 1, Good x → Good (x + (S.g : ℝ) • σ) → ‖phi {h} (fun _ _ => (1 : ℂ)) U x (x + (S.g : ℝ) • σ)‖ ≤ Bt * crystallineComparison.mL C.Kst (fun _ => Λ b (n - 1) v) ((S.g : ℝ) • σ)`.

Introduce `σ _ x hx hx'`. Use `set t := (x 0)⁻¹ with ht_def`. Use `set t' := ((x + (S.g : ℝ) • σ) 0)⁻¹ with ht'_def`. Establish `ht : t ≠ 0` using `inv_ne_zero (hx 0)`. Establish `ht' : t' ≠ 0` using `inv_ne_zero (hx' 0)`.

Establish `ephi : phi {h} (fun _ _ => (1 : ℂ)) U x (x + (S.g : ℝ) • σ) = KB.gN S v ε (b + n - 2) (w.1 v) (h ++ [(n - 1, t)]) (h ++ [(n - 1, t')])`. Simplify using `[phi, U, t, t']`. Rewrite using `[ephi, mL_one]`. Use `set a0 := ‖((S.g : ℝ) • σ) 0‖`. Establish `ediff : t⁻¹ - t'⁻¹ = -(((S.g : ℝ) • σ) 0)`.

Simplify using `only [t, t', inv_inv, Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Apply the tactic sequence `have hcs : ‖KB.gN S v ε (b + n - 2) (w.1 v) (h ++ [(n - 1, t)]) (h ++ [(n - 1, t')])‖ ≤ Ba := gN_entry S hpos v ε hε _ (by omega) w _ _ Ba (hBa t ht) (hBa t' ht')`. Take `⟨u, hu, hB⟩` from `hLB ε hε t t' {h} ht ht' (by simp [hh])`. Establish `hob` using `offdiag_bound _ _ _ h {h} (Finset.mem_singleton_self h) hB (Λ b (n - 1) v ^ C.Kst * Bp) (Λ b (n - 1) v ^ C.Kst * Bq) ?_ ?_`.

Use `rotate_left`. Simplify using `only`. Rewrite using `[show (((Λ b (n - 1) v ^ C.Kst : ℝ) : ℂ) * KB.mix S v ε (b + (n - 1) - 1) Up θp (h ++ [(n - 1, t)]) (h ++ [(n - 1, t)])).re = Λ b (n - 1) v ^ C.Kst * (KB.mix S v ε (b + (n - 1) - 1) Up θp (h ++ [(n - 1, t)]) (h ++ [(n - 1, t)])).re from Complex.re_ofReal_mul _ _]`. Use `mul_le_mul_of_nonneg_left ?_ (pow_nonneg hΛ0 _)` and prove the remaining obligations. Rewrite using `[hl2]`.

Conclude with `re_mix_le S v ε _ Up θp hUp.1.1 _ Bu fun u hu => by`. Use `hBu' u (Finset.mem_union_left _ hu) t ht` as an intermediate fact. Rewrite `this` using `[hl2]`. Then use the resulting hypothesis. Simplify using `only`. Rewrite using `[show (((Λ b (n - 1) v ^ C.Kst : ℝ) : ℂ) * KB.mix S v ε (b + (n - 1) - 1) Um θm (h ++ [(n - 1, t')]) (h ++ [(n - 1, t')])).re = Λ b (n - 1) v ^ C.Kst * (KB.mix S v ε (b + (n - 1) - 1) Um θm (h ++ [(n - 1, t')]) (h ++ [(n - 1, t')])).re from Complex.re_ofReal_mul _ _]`.

Use `mul_le_mul_of_nonneg_left ?_ (pow_nonneg hΛ0 _)` and prove the remaining obligations. Rewrite using `[hl2]`. Conclude with `re_mix_le S v ε _ Um θm hUm.1.1 _ Bu fun u hu => by`. Use `hBu' u (Finset.mem_union_right _ hu) t' ht'` as an intermediate fact. Rewrite `this` using `[hl2]`. Then use the resulting hypothesis.

Rewrite `hob` using `[hl2, norm_mul, norm_mul, hu, one_mul, norm_pow, ediff, norm_neg]`. Use `set X := ‖KB.gN S v ε (b + n - 2) (w.1 v) (h ++ [(n - 1, t)]) (h ++ [(n - 1, t')])‖ with hX`. Establish `hX0 : 0 ≤ X` using `norm_nonneg _`. Establish `hl : a0 ^ C.Kst * X ≤ Λ b (n - 1) v ^ C.Kst * (Bp + Bq)`. Establish `h1 : (a0 ^ C.Kst * X) ^ 2 ≤ (Λ b (n - 1) v ^ C.Kst * (Bp + Bq)) ^ 2`.

Use `hob.trans ?_` and prove the remaining obligations. Establish `hL` using `pow_nonneg hΛ0 C.Kst`. Use polynomial arithmetic with `[mul_nonneg hL hBp0, mul_nonneg hL hBq0, mul_nonneg (mul_nonneg hL hL) (mul_nonneg hBp0 hBq0)]`. Conclude with `(pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 h1`. Unfold `crystallineComparison.mfac`.

Use `split_ifs with h0`. Rewrite using `[mul_one]`. Conclude with `hcs.trans ((le_max_left _ _).trans (le_max_left _ _))`. Establish `ha0 : 0 < a0` using `lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)`. Rewrite using `[mul_min_of_nonneg _ _ hBt0, mul_one]`.

Use `le_min (hcs.trans ((le_max_left _ _).trans (le_max_left _ _))) ?_` and prove the remaining obligations. Establish `h2 : X ≤ (Λ b (n - 1) v / a0) ^ C.Kst * (Bp + Bq)`. Rewrite using `[div_pow, div_mul_eq_mul_div, le_div_iff₀ (pow_pos ha0 _)]`. Combine the linear relations using `[hl]`. Use `h2.trans ?_` and prove the remaining obligations.

Rewrite using `[mul_comm]`. Conclude with `mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (div_nonneg hΛ0 ha0.le) _)`. Use `⟨(∏ _v : Fin 1, KB.dlB S b n) * ∑' σ : crystallineComparison.dualSet (Lstd 1 1), Bt * crystallineComparison.mL C.Kst (fun _ => Λ b (n - 1) v) ((S.g : ℝ) • (σ : crystallineComparison.V 1)), fun t ht => ?_⟩` and prove the remaining obligations. Establish `hH` using `herglotz_germ (H := C.LPt) (f := 1) {h} (fun _ _ => 1) (psd_single_one h) D hD (fun _ p hp q hq => (hcont p hp q hq).1) (fun _ p hp q hq => (hcont p hp q hq).2) (S.g : ℝ) hgR (fun _ => KB.dlB S b n) (fun _ => dlB_pos S hg b n) U (fun _ => Pua) (fun _ => Paa) (fun _ σ p q => KB.ha …`. Rewrite `hH` using `[hcov, Finset.sum_singleton]`.

Establish `hgood : Good (fun _ : Fin 1 => t)` using `fun _ => ht`. Establish `hN : Nz {h} (fun _ _ => (1 : ℂ)) D (fun _ => t) = (KB.gN S v ε (b + n - 1) (w.1 v) (h ++ [(n, t)]) (h ++ [(n, t)])).re`. Simplify using `[Nz, hgood, Fz, D]`. Rewrite `hH` using `[hN, one_pow, one_mul]`. Establish `h0` using `psd_diag _ _ (PBB.gN_psd S hpos v ε hε (b + n - 1) (by omega) w {h ++ [(n, t)]}) (Finset.mem_singleton_self _)`.

Establish `hc` using `Complex.nonneg_iff.1 h0`. Establish `e : KB.gN S v ε (b + n - 1) (w.1 v) (h ++ [(n, t)]) (h ++ [(n, t)]) = ((KB.gN S v ε (b + n - 1) (w.1 v) (h ++ [(n, t)]) (h ++ [(n, t)])).re : ℂ)` using `Complex.ext (by simp) (by simp [hc.2.symm])`. Rewrite using `[e, Complex.norm_real, Real.norm_of_nonneg hc.1]`. Conclude with `hH`.
-/
theorem locSup_step (S : C.HidaSetting E Wp Wq) (hpos : C.ThmPPos S) (hg : 0 < S.g) (v : Fin S.f)
    (Λ : ℕ → ℕ → Fin S.f → ℝ) (hLL : KB.LiftLoc S v fun b s => Λ b s v) (hGL : KB.GermLoc S v)
    (ε : ℝ) (hε : 0 < ε) (n : ℕ) (hn : 2 ≤ n) (b : ℕ) (hb : 1 ≤ b) (hbn : b + n ≤ S.G.r + 2)
    (hΛ0 : 0 ≤ Λ b (n - 1) v) (h : C.LPt) (hh : D.ptSize h = b - 1)
    (hIH : ∀ u, D.AdmAt S v u → u.length + (n - 2) * C.Kst ≤ S.Ntop → LocSup S v ε (n - 1) b u h)
    (a : List C.Letter) (ha : D.AdmAt S v a) (hlen : a.length + (n - 1) * C.Kst ≤ S.Ntop) :
    LocSup S v ε n b a h := by
  have hk : (n - 1) * C.Kst = (n - 2) * C.Kst + C.Kst := by
    have : n - 1 = (n - 2) + 1 := by omega
    rw [this, add_mul, one_mul]
  have hl2 : b + (n - 1) - 1 = b + n - 2 := by omega
  obtain ⟨Ba, hBa⟩ := hIH a ha (by omega)
  rw [hl2] at hBa
  obtain ⟨w, rfl⟩ := exists_word_of_admissible_at_place S ha

  have hsup : ∃ B : ℝ, ∀ p ∈ ({h} : Finset C.LPt), ∀ t : ℂ, t ≠ 0 →
      ‖KB.gN S v ε (b + n - 2) (w.1 v) (p ++ [(n - 1, t)]) (p ++ [(n - 1, t)])‖ ≤ B :=
    ⟨Ba, fun p hp t ht => by rw [Finset.mem_singleton] at hp; subst hp; exact hBa t ht⟩
  obtain ⟨hcont, Pua, Paa, hblk, ⟨B', hB'⟩, hlim⟩ :=
    hGL ε hε b n hb hn hbn (w.1 v) ha {h} (by simp [hh]) hsup

  obtain ⟨Up, θp, Um, θm, hUp, hUm, hLB⟩ := hLL b (n - 1) hb (by omega) (by omega) (w.1 v) ha (by omega)
  have hBu : ∀ u ∈ Up ∪ Um, LocSup S v ε (n - 1) b u h := by
    intro u hu
    rcases Finset.mem_union.1 hu with hu | hu
    · exact hIH u (hUp.2 u hu).1 (by have := (hUp.2 u hu).2; omega)
    · exact hIH u (hUm.2 u hu).1 (by have := (hUm.2 u hu).2; omega)
  choose! Bu hBu' using hBu
  set Bp := ∑ u ∈ Up, θp u * max (Bu u) 0 with hBp
  set Bq := ∑ u ∈ Um, θm u * max (Bu u) 0 with hBq
  have hBp0 : 0 ≤ Bp := Finset.sum_nonneg fun u _ => mul_nonneg (hUp.1.1 u) (le_max_right _ _)
  have hBq0 : 0 ≤ Bq := Finset.sum_nonneg fun u _ => mul_nonneg (hUm.1.1 u) (le_max_right _ _)
  set Bt := max (max Ba 0) (Bp + Bq) with hBt
  have hBt0 : 0 ≤ Bt := (le_max_right _ _).trans (le_max_left _ _)

  obtain ⟨i1, i2, hcov, -⟩ := pbc_lstdFacts 1 1 one_pos
  have := i1; have := i2
  have hgR : (0 : ℝ) < S.g := by exact_mod_cast hg
  obtain ⟨Lm, j1, j2, hLm⟩ := GlobalTheory.dual_smul_mem (Lstd 1 1) (S.g : ℝ) hgR.ne'
  have := j1; have := j2
  obtain ⟨Cs, -, hCsum⟩ := pbc_lstdSum
  obtain ⟨hsm, -⟩ := hCsum 1 1 (S.g : ℝ) (fun _ => Λ b (n - 1) v) one_pos hgR (fun _ => hΛ0)
  let D : Fin 1 → C.LPt → C.LPt → ℂ → ℂ := fun _ p q c =>
    KB.gN S v ε (b + n - 1) (w.1 v) (p ++ [(n, c)]) (q ++ [(n, c)])
  let U : Fin 1 → C.LPt × ℂ → C.LPt × ℂ → ℂ := fun _ p q =>
    KB.gN S v ε (b + n - 2) (w.1 v) (p.1 ++ [(n - 1, p.2⁻¹)]) (q.1 ++ [(n - 1, q.2⁻¹)])
  have hGD : GermData {h} U (fun _ => Pua) (fun _ => Paa) (fun _ σ p q => KB.hatB S v ε b n (w.1 v) σ p q) := by
    refine ⟨fun _ Xs hXs => hblk Xs hXs, ⟨max Ba B' ⊔ 0, le_max_right _ _, fun _ p hp x hx => ?_⟩,
      fun _ p hp q hq σ => (hlim p hp q hq σ).1, fun _ p hp q hq σ => (hlim p hp q hq σ).2.1,
      fun _ p hp q hq σ => (hlim p hp q hq σ).2.2⟩
    rw [Finset.mem_singleton] at hp; subst hp
    refine ⟨(hBa x⁻¹ (inv_ne_zero hx)).trans ?_, (hB' p (Finset.mem_singleton_self p) x hx).trans ?_⟩
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · exact (le_max_right _ _).trans (le_max_left _ _)
  have hD : ∀ (v' : Fin 1) (z : ℂ), z ≠ 0 → TB.PSDOn ({h} : Finset C.LPt) (fun p q => D v' p q z) := by
    intro v' z _
    have := PBB.gN_psd S hpos v ε hε (b + n - 1) (by omega) w (({h} : Finset C.LPt).image fun p => p ++ [(n, z)])
    exact JCx1.decay.psd_pull _ _ this {h} (fun p => p ++ [(n, z)]) (fun p hp => Finset.mem_image_of_mem _ hp)

  have hF : ∀ σ ∈ crystallineComparison.dualSet (Lstd 1 1), ∀ x : crystallineComparison.V 1, Good x → Good (x + (S.g : ℝ) • σ) →
      ‖phi {h} (fun _ _ => (1 : ℂ)) U x (x + (S.g : ℝ) • σ)‖ ≤
        Bt * crystallineComparison.mL C.Kst (fun _ => Λ b (n - 1) v) ((S.g : ℝ) • σ) := by
    intro σ _ x hx hx'
    set t := (x 0)⁻¹ with ht_def
    set t' := ((x + (S.g : ℝ) • σ) 0)⁻¹ with ht'_def
    have ht : t ≠ 0 := inv_ne_zero (hx 0)
    have ht' : t' ≠ 0 := inv_ne_zero (hx' 0)
    have ephi : phi {h} (fun _ _ => (1 : ℂ)) U x (x + (S.g : ℝ) • σ) =
        KB.gN S v ε (b + n - 2) (w.1 v) (h ++ [(n - 1, t)]) (h ++ [(n - 1, t')]) := by
      simp [phi, U, t, t']
    rw [ephi, mL_one]
    set a0 := ‖((S.g : ℝ) • σ) 0‖
    have ediff : t⁻¹ - t'⁻¹ = -(((S.g : ℝ) • σ) 0) := by
      simp only [t, t', inv_inv, Pi.add_apply]; ring

    have hcs : ‖KB.gN S v ε (b + n - 2) (w.1 v) (h ++ [(n - 1, t)]) (h ++ [(n - 1, t')])‖ ≤ Ba :=
      gN_entry S hpos v ε hε _ (by omega) w _ _ Ba (hBa t ht) (hBa t' ht')

    obtain ⟨u, hu, hB⟩ := hLB ε hε t t' {h} ht ht' (by simp [hh])
    have hob := offdiag_bound _ _ _ h {h} (Finset.mem_singleton_self h) hB
      (Λ b (n - 1) v ^ C.Kst * Bp) (Λ b (n - 1) v ^ C.Kst * Bq) ?_ ?_
    rotate_left
    · simp only
      rw [show (((Λ b (n - 1) v ^ C.Kst : ℝ) : ℂ) * KB.mix S v ε (b + (n - 1) - 1) Up θp (h ++ [(n - 1, t)])
          (h ++ [(n - 1, t)])).re = Λ b (n - 1) v ^ C.Kst * (KB.mix S v ε (b + (n - 1) - 1) Up θp (h ++ [(n - 1, t)])
          (h ++ [(n - 1, t)])).re from Complex.re_ofReal_mul _ _]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hΛ0 _)
      rw [hl2]
      exact re_mix_le S v ε _ Up θp hUp.1.1 _ Bu fun u hu => by
        have := hBu' u (Finset.mem_union_left _ hu) t ht; rwa [hl2] at this
    · simp only
      rw [show (((Λ b (n - 1) v ^ C.Kst : ℝ) : ℂ) * KB.mix S v ε (b + (n - 1) - 1) Um θm (h ++ [(n - 1, t')])
          (h ++ [(n - 1, t')])).re = Λ b (n - 1) v ^ C.Kst * (KB.mix S v ε (b + (n - 1) - 1) Um θm
          (h ++ [(n - 1, t')]) (h ++ [(n - 1, t')])).re from Complex.re_ofReal_mul _ _]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hΛ0 _)
      rw [hl2]
      exact re_mix_le S v ε _ Um θm hUm.1.1 _ Bu fun u hu => by
        have := hBu' u (Finset.mem_union_right _ hu) t' ht'; rwa [hl2] at this
    rw [hl2, norm_mul, norm_mul, hu, one_mul, norm_pow, ediff, norm_neg] at hob
    set X := ‖KB.gN S v ε (b + n - 2) (w.1 v) (h ++ [(n - 1, t)]) (h ++ [(n - 1, t')])‖ with hX
    have hX0 : 0 ≤ X := norm_nonneg _
    have hl : a0 ^ C.Kst * X ≤ Λ b (n - 1) v ^ C.Kst * (Bp + Bq) := by
      have h1 : (a0 ^ C.Kst * X) ^ 2 ≤ (Λ b (n - 1) v ^ C.Kst * (Bp + Bq)) ^ 2 := by
        refine hob.trans ?_
        have hL := pow_nonneg hΛ0 C.Kst
        nlinarith [mul_nonneg hL hBp0, mul_nonneg hL hBq0, mul_nonneg (mul_nonneg hL hL) (mul_nonneg hBp0 hBq0)]
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 h1
    unfold crystallineComparison.mfac
    split_ifs with h0
    · rw [mul_one]; exact hcs.trans ((le_max_left _ _).trans (le_max_left _ _))
    · have ha0 : 0 < a0 := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      rw [mul_min_of_nonneg _ _ hBt0, mul_one]
      refine le_min (hcs.trans ((le_max_left _ _).trans (le_max_left _ _))) ?_
      have h2 : X ≤ (Λ b (n - 1) v / a0) ^ C.Kst * (Bp + Bq) := by
        rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (pow_pos ha0 _)]
        linarith [hl]
      refine h2.trans ?_
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (div_nonneg hΛ0 ha0.le) _)
  refine ⟨(∏ _v : Fin 1, KB.dlB S b n) *
    ∑' σ : crystallineComparison.dualSet (Lstd 1 1), Bt * crystallineComparison.mL C.Kst (fun _ => Λ b (n - 1) v) ((S.g : ℝ) • (σ : crystallineComparison.V 1)),
    fun t ht => ?_⟩
  have hH := herglotz_germ (H := C.LPt) (f := 1) {h} (fun _ _ => 1) (psd_single_one h) D hD
    (fun _ p hp q hq => (hcont p hp q hq).1) (fun _ p hp q hq => (hcont p hp q hq).2) (S.g : ℝ) hgR
    (fun _ => KB.dlB S b n) (fun _ => dlB_pos S hg b n) U (fun _ => Pua) (fun _ => Paa)
    (fun _ σ p q => KB.hatB S v ε b n (w.1 v) σ p q) hGD (fun _ _ _ _ => rfl) (Lstd 1 1) Lm hLm
    (fun σ => Bt * crystallineComparison.mL C.Kst (fun _ => Λ b (n - 1) v) ((S.g : ℝ) • σ)) (hsm.mul_left Bt) hF
    (fun _ => t) {fun _ => t} (by simp)
  rw [hcov, Finset.sum_singleton] at hH
  have hgood : Good (fun _ : Fin 1 => t) := fun _ => ht
  have hN : Nz {h} (fun _ _ => (1 : ℂ)) D (fun _ => t) =
      (KB.gN S v ε (b + n - 1) (w.1 v) (h ++ [(n, t)]) (h ++ [(n, t)])).re := by
    simp [Nz, hgood, Fz, D]
  rw [hN, one_pow, one_mul] at hH
  have h0 := psd_diag _ _ (PBB.gN_psd S hpos v ε hε (b + n - 1) (by omega) w {h ++ [(n, t)]})
    (Finset.mem_singleton_self _)
  have hc := Complex.nonneg_iff.1 h0
  have e : KB.gN S v ε (b + n - 1) (w.1 v) (h ++ [(n, t)]) (h ++ [(n, t)]) =
      ((KB.gN S v ε (b + n - 1) (w.1 v) (h ++ [(n, t)]) (h ++ [(n, t)])).re : ℂ) :=
    Complex.ext (by simp) (by simp [hc.2.symm])
  rw [e, Complex.norm_real, Real.norm_of_nonneg hc.1]
  exact hH

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro h0`. Use linear arithmetic over natural numbers and integers. Consider the case `succ m ih`.

Introduce `_ b hb hbn h hh a ha hlen`. Break down `Nat.eq_zero_or_pos m with rfl | hm` into its components or cases. Conclude with `locSup_one S hI v ε hε b hb (by omega) a ha h hh`. Use `locSup_step S hpos hg v Λ hLL hGL ε hε (m + 1) (by omega) b hb hbn (by rw [Nat.add_sub_cancel]; exact hΛ0 b m hb hm (by omega)) h hh ?_ a ha hlen` and prove the remaining obligations. Introduce `u hu hulen`.

Establish `e1 : m + 1 - 2 = m - 1` using `by omega`. Rewrite `hulen` using `[e1]`. Rewrite using `[Nat.add_sub_cancel]`. Conclude with `ih hm b hb (by omega) h hh u hu hulen`.
-/
theorem locSup_all (S : C.HidaSetting E Wp Wq) (hpos : C.ThmPPos S) (hI : KB.IntAll S) (hg : 0 < S.g) (v : Fin S.f)
    (Λ : ℕ → ℕ → Fin S.f → ℝ) (hLL : KB.LiftLoc S v fun b s => Λ b s v) (hGL : KB.GermLoc S v)
    (hΛ0 : ∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ S.G.r + 1 → 0 ≤ Λ b s v) (ε : ℝ) (hε : 0 < ε) :
    ∀ n, 1 ≤ n → ∀ b, 1 ≤ b → b + n ≤ S.G.r + 2 → ∀ h, D.ptSize h = b - 1 → ∀ a, D.AdmAt S v a →
      a.length + (n - 1) * C.Kst ≤ S.Ntop → LocSup S v ε n b a h := by
  intro n
  induction n with
  | zero => intro h0; omega
  | succ m ih =>
    intro _ b hb hbn h hh a ha hlen
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact locSup_one S hI v ε hε b hb (by omega) a ha h hh
    · refine locSup_step S hpos hg v Λ hLL hGL ε hε (m + 1) (by omega) b hb hbn
        (by rw [Nat.add_sub_cancel]; exact hΛ0 b m hb hm (by omega)) h hh ?_ a ha hlen
      intro u hu hulen
      have e1 : m + 1 - 2 = m - 1 := by omega
      rw [e1] at hulen
      rw [Nat.add_sub_cancel]
      exact ih hm b hb (by omega) h hh u hu hulen

end

end Formalism.FourierDecayAlt.P.PBC
