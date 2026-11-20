import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AddCurveStableOfIntegralGaugedFormalGroupLawStatement
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

noncomputable section

namespace GlobalTheory.RowLaw.CvGroup

variable {C : Type} [Field C]

/- English proof (translation)
Unfold `alongCv`. Use `show MvPowerSeries.coeff (Finsupp.single () m) _ = MvPowerSeries.coeff (Finsupp.single () m) _`. Rewrite using `[MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha), MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero hb)]`. Use `finsum_congr fun e => ?_` and prove the remaining obligations. Use `congr 1`.

Use `set J : Ideal (PowerSeries C) := Ideal.span {(PowerSeries.X : PowerSeries C) ^ n} with hJ`. Establish `hq : ∀ i, Ideal.Quotient.mk J (a i) = Ideal.Quotient.mk J (b i)`. Introduce `i`. Rewrite using `[Ideal.Quotient.eq, hJ, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]`. Introduce `k hk`.

Rewrite using `[map_sub, hab i k hk, sub_self]`. Establish `hp : Ideal.Quotient.mk J (e.prod fun s k => a s ^ k) = Ideal.Quotient.mk J (e.prod fun s k => b s ^ k)`. Unfold `Finsupp.prod`. Rewrite using `[map_prod, map_prod]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations.

Rewrite using `[map_pow, map_pow, hq]`. Rewrite `hp` using `[Ideal.Quotient.eq, hJ, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]`. Use `hp m hm` as an intermediate fact. Rewrite `this` using `[map_sub, sub_eq_zero]`. Conclude with `this`.
-/
theorem alongCv_congr {σ : Type} [Finite σ] {a b : σ → PowerSeries C}
    (ha : ∀ i, PowerSeries.constantCoeff (a i) = 0) (hb : ∀ i, PowerSeries.constantCoeff (b i) = 0) {n : ℕ}
    (hab : ∀ i, ∀ m < n, PowerSeries.coeff m (a i) = PowerSeries.coeff m (b i)) (f : MvPowerSeries σ C)
    (m : ℕ) (hm : m < n) :
    PowerSeries.coeff m (alongCv a f) = PowerSeries.coeff m (alongCv b f) := by
  unfold alongCv
  show MvPowerSeries.coeff (Finsupp.single () m) _ = MvPowerSeries.coeff (Finsupp.single () m) _
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha),
    MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero hb)]
  refine finsum_congr fun e => ?_
  congr 1
  set J : Ideal (PowerSeries C) := Ideal.span {(PowerSeries.X : PowerSeries C) ^ n} with hJ
  have hq : ∀ i, Ideal.Quotient.mk J (a i) = Ideal.Quotient.mk J (b i) := by
    intro i
    rw [Ideal.Quotient.eq, hJ, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
    intro k hk
    rw [map_sub, hab i k hk, sub_self]
  have hp : Ideal.Quotient.mk J (e.prod fun s k => a s ^ k) = Ideal.Quotient.mk J (e.prod fun s k => b s ^ k) := by
    unfold Finsupp.prod
    rw [map_prod, map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [map_pow, map_pow, hq]
  rw [Ideal.Quotient.eq, hJ, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at hp
  have := hp m hm
  rw [map_sub, sub_eq_zero] at this
  exact this

/- English proof (translation)
Rewrite using `[alongCv_congr (b := fun _ => 0) ha (fun _ => map_zero _) (fun i k hk => by rw [hab i k hk, map_zero]) f m hm, alongCv_zero hf, map_zero]`.
-/
theorem alongCv_low {σ : Type} [Finite σ] {a : σ → PowerSeries C}
    (ha : ∀ i, PowerSeries.constantCoeff (a i) = 0) {n : ℕ}
    (hab : ∀ i, ∀ m < n, PowerSeries.coeff m (a i) = 0) {f : MvPowerSeries σ C}
    (hf : MvPowerSeries.constantCoeff f = 0) (m : ℕ) (hm : m < n) :
    PowerSeries.coeff m (alongCv a f) = 0 := by
  rw [alongCv_congr (b := fun _ => 0) ha (fun _ => map_zero _) (fun i k hk => by rw [hab i k hk, map_zero]) f m hm,
    alongCv_zero hf, map_zero]

/- English proof (translation)
The claim follows from `constantCoeff_subst_zero (τ := Unit) ha hf`.
-/
theorem constantCoeff_alongCv {σ : Type} [Finite σ] {a : σ → PowerSeries C}
    (ha : ∀ i, PowerSeries.constantCoeff (a i) = 0) {f : MvPowerSeries σ C}
    (hf : MvPowerSeries.constantCoeff f = 0) : PowerSeries.constantCoeff (alongCv a f) = 0 :=
  constantCoeff_subst_zero (τ := Unit) ha hf

/- English proof (translation)
Unfold `alongCv`. Rewrite using `[MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hp) (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)]`.
-/
theorem alongCv_comp {σ : Type} [Finite σ] {a : σ → PowerSeries C}
    (ha : ∀ i, PowerSeries.constantCoeff (a i) = 0) {p : σ → MvPowerSeries σ C}
    (hp : ∀ i, MvPowerSeries.constantCoeff (p i) = 0) (f : MvPowerSeries σ C) :
    alongCv (fun i => alongCv a (p i)) f = alongCv a (MvPowerSeries.subst p f) := by
  unfold alongCv
  rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hp)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)]

/- English proof (translation)
Unfold `alongCv`. Conclude with `MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) i`.
-/
theorem alongCv_X {σ : Type} [Finite σ] {a : σ → PowerSeries C}
    (ha : ∀ i, PowerSeries.constantCoeff (a i) = 0) (i : σ) :
    alongCv a (MvPowerSeries.X i) = a i := by
  unfold alongCv
  exact MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) i

variable {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] {X : RawChart C d I κ}

/- English proof (translation)
Rewrite using `[← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, H.lin i 0 (by simp), MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.constantCoeff_X]`.
-/
theorem lg_const (H : RLaw X V) (i : κ) : MvPowerSeries.constantCoeff (X.lg i) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, H.lin i 0 (by simp),
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.constantCoeff_X]

/- English proof (translation)
Rewrite using `[alongCv_comp hγ (lg_const H), H.exlg, alongCv_X hγ]`.
-/
theorem ex_lg (H : RLaw X V) {γ : κ → PowerSeries C} (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) (i : κ) :
    alongCv (fun j => alongCv γ (X.lg j)) (X.ex i) = γ i := by
  rw [alongCv_comp hγ (lg_const H), H.exlg, alongCv_X hγ]

/- English proof (translation)
Rewrite using `[alongCv_comp ha H.exc, H.lgex, alongCv_X ha]`.
-/
theorem lg_ex (H : RLaw X V) {a : κ → PowerSeries C} (ha : ∀ i, PowerSeries.constantCoeff (a i) = 0) (i : κ) :
    alongCv (fun j => alongCv a (X.ex j)) (X.lg i) = a i := by
  rw [alongCv_comp ha H.exc, H.lgex, alongCv_X ha]

/- English proof (translation)
Establish `hlg1 : ∀ j, MvPowerSeries.coeff (Finsupp.single j 1) (X.lg i) = if j = i then 1 else 0` using `fun j => by`. Rewrite using `[H.lin i _ (by rw [Finsupp.degree_single]), MvPowerSeries.coeff_X]`. Distinguish the cases in `hji : j = i`. Rewrite using `[hji, if_pos rfl, if_pos rfl]`. Rewrite using `[if_neg hji, if_neg]`.

Introduce `h`. Conclude with `hji (Finsupp.single_left_injective one_ne_zero h)`. Rewrite using `[coeff_alongCv_low hn hγ (lg_const H i)]`. Simplify using `only [hlg1, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.
-/
theorem coeff_lg_low (H : RLaw X V) {γ : κ → PowerSeries C} {n : ℕ} (hn : 1 ≤ n)
    (hγ : ∀ i, ∀ m < n, PowerSeries.coeff m (γ i) = 0) (i : κ) :
    PowerSeries.coeff n (alongCv γ (X.lg i)) = PowerSeries.coeff n (γ i) := by
  classical
  have hlg1 : ∀ j, MvPowerSeries.coeff (Finsupp.single j 1) (X.lg i) = if j = i then 1 else 0 := fun j => by
    rw [H.lin i _ (by rw [Finsupp.degree_single]), MvPowerSeries.coeff_X]
    by_cases hji : j = i
    · rw [hji, if_pos rfl, if_pos rfl]
    · rw [if_neg hji, if_neg]
      intro h
      exact hji (Finsupp.single_left_injective one_ne_zero h)
  rw [coeff_alongCv_low hn hγ (lg_const H i)]
  simp only [hlg1, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Use `⟨γ, hγ, fun i m hm => ?_⟩` and prove the remaining obligations. Establish `: m = 0` using `by omega`. Rewrite using `[this, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_add, constantCoeff_alongCv (fun i => (hγ i).1) (lg_const H i), add_zero]`.

Consider the case `succ n ih`. Take `⟨δ, hδ, hlow⟩` from `ih`. Take `⟨s, hs, hL, -⟩` from `hA γ δ hγ hδ`. Establish `hs0 : ∀ i, PowerSeries.constantCoeff (s i) = 0` using `fun i => (hs i).1`. Establish `hslow : ∀ i, ∀ m < n + 1, PowerSeries.coeff m (s i) = 0`.

Introduce `i m hm`. Rewrite using `[← ex_lg H hs0 i]`. Conclude with `alongCv_low (fun j => constantCoeff_alongCv hs0 (lg_const H j)) (fun j k hk => by rw [hL j]; exact hlow j k hk) (H.exc i) m hm`. Establish `hε : IsCv V fun i => -s i` using `fun i => ⟨by rw [map_neg, hs0, neg_zero], fun k => by rw [map_neg]; exact ((hs i).2 k).neg⟩`. Establish `hεlow : ∀ i, ∀ m < n + 1, PowerSeries.coeff m (-s i) = 0` using `fun i m hm => by`.

Rewrite using `[map_neg, hslow i m hm, neg_zero]`. Take `⟨δ', hδ', hL', -⟩` from `hA δ _ hδ hε`. Use `⟨δ', hδ', fun i m hm => ?_⟩` and prove the remaining obligations. Rewrite using `[hL' i, ← add_assoc, map_add]`. Distinguish the cases in `hmn : m < n + 1`.

Rewrite using `[hlow i m hmn, alongCv_low (fun j => (hε j).1) hεlow (lg_const H i) m hmn, add_zero]`. Establish `: m = n + 1` using `by omega`. Rewrite using `[this, ← hL i, coeff_lg_low H (by omega) hslow, coeff_lg_low H (by omega) hεlow, map_neg, add_neg_cancel]`.
-/
theorem approx_neg (H : RLaw X V) (hA : X.AddCvSt V) {γ : κ → PowerSeries C} (hγ : IsCv V γ) (n : ℕ) :
    ∃ δ : κ → PowerSeries C, IsCv V δ ∧
      ∀ i, ∀ m < n + 1, PowerSeries.coeff m (alongCv γ (X.lg i) + alongCv δ (X.lg i)) = 0 := by
  induction n with
  | zero =>
    refine ⟨γ, hγ, fun i m hm => ?_⟩
    have : m = 0 := by omega
    rw [this, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_add,
      constantCoeff_alongCv (fun i => (hγ i).1) (lg_const H i), add_zero]
  | succ n ih =>
    obtain ⟨δ, hδ, hlow⟩ := ih
    obtain ⟨s, hs, hL, -⟩ := hA γ δ hγ hδ
    have hs0 : ∀ i, PowerSeries.constantCoeff (s i) = 0 := fun i => (hs i).1
    have hslow : ∀ i, ∀ m < n + 1, PowerSeries.coeff m (s i) = 0 := by
      intro i m hm
      rw [← ex_lg H hs0 i]
      exact alongCv_low (fun j => constantCoeff_alongCv hs0 (lg_const H j))
        (fun j k hk => by rw [hL j]; exact hlow j k hk) (H.exc i) m hm
    have hε : IsCv V fun i => -s i := fun i =>
      ⟨by rw [map_neg, hs0, neg_zero], fun k => by rw [map_neg]; exact ((hs i).2 k).neg⟩
    have hεlow : ∀ i, ∀ m < n + 1, PowerSeries.coeff m (-s i) = 0 := fun i m hm => by
      rw [map_neg, hslow i m hm, neg_zero]
    obtain ⟨δ', hδ', hL', -⟩ := hA δ _ hδ hε
    refine ⟨δ', hδ', fun i m hm => ?_⟩
    rw [hL' i, ← add_assoc, map_add]
    by_cases hmn : m < n + 1
    · rw [hlow i m hmn, alongCv_low (fun j => (hε j).1) hεlow (lg_const H i) m hmn, add_zero]
    · have : m = n + 1 := by omega
      rw [this, ← hL i, coeff_lg_low H (by omega) hslow, coeff_lg_low H (by omega) hεlow, map_neg, add_neg_cancel]

/- English proof (translation)
Establish `h0 : ∀ j, PowerSeries.constantCoeff (-alongCv γ (X.lg j)) = 0` using `fun j => by`. Rewrite using `[map_neg, constantCoeff_alongCv (fun i => (hγ i).1) (lg_const H j), neg_zero]`. Use `⟨fun i => alongCv (fun j => -alongCv γ (X.lg j)) (X.ex i), fun i => ⟨constantCoeff_alongCv h0 (H.exc i), fun n => ?_⟩, lg_ex H h0⟩` and prove the remaining obligations. Take `⟨δ, hδ, hlow⟩` from `approx_neg H hA hγ n`. Establish `hδ0 : ∀ i, PowerSeries.constantCoeff (δ i) = 0` using `fun i => (hδ i).1`.

Rewrite using `[alongCv_congr (b := fun j => alongCv δ (X.lg j)) h0 (fun j => constantCoeff_alongCv hδ0 (lg_const H j)) (n := n + 1) (fun j m hm => by`. Use `hlow j m hm` as an intermediate fact. Rewrite `this` using `[map_add]`. Rewrite using `[map_neg]`. Conclude with `neg_eq_of_add_eq_zero_right this) _ n (Nat.lt_succ_self n), ex_lg H hδ0]`.

Conclude with `(hδ i).2 n`.
-/
theorem exists_neg (H : RLaw X V) (hA : X.AddCvSt V) {γ : κ → PowerSeries C} (hγ : IsCv V γ) :
    ∃ δ : κ → PowerSeries C, IsCv V δ ∧ ∀ i, alongCv δ (X.lg i) = -alongCv γ (X.lg i) := by
  have h0 : ∀ j, PowerSeries.constantCoeff (-alongCv γ (X.lg j)) = 0 := fun j => by
    rw [map_neg, constantCoeff_alongCv (fun i => (hγ i).1) (lg_const H j), neg_zero]
  refine ⟨fun i => alongCv (fun j => -alongCv γ (X.lg j)) (X.ex i), fun i => ⟨constantCoeff_alongCv h0 (H.exc i), fun n => ?_⟩,
    lg_ex H h0⟩
  obtain ⟨δ, hδ, hlow⟩ := approx_neg H hA hγ n
  have hδ0 : ∀ i, PowerSeries.constantCoeff (δ i) = 0 := fun i => (hδ i).1
  rw [alongCv_congr (b := fun j => alongCv δ (X.lg j)) h0 (fun j => constantCoeff_alongCv hδ0 (lg_const H j))
    (n := n + 1) (fun j m hm => by
      have := hlow j m hm
      rw [map_add] at this
      rw [map_neg]
      exact neg_eq_of_add_eq_zero_right this) _ n (Nat.lt_succ_self n), ex_lg H hδ0]
  exact (hδ i).2 n

/- English proof (translation)
The claim follows from `X.constantCoeff_sg (H.axes 0) v`.
-/
theorem sg_const (H : RLaw X V) (v : κ → C) : MvPowerSeries.constantCoeff (X.sg v) = 0 :=
  X.constantCoeff_sg (H.axes 0) v

/- English proof (translation)
Introduce `_` and use `⟨map_zero _, fun n => by rw [map_zero]; exact VF.Ge.zero 0⟩`.
-/
theorem isCv_zero {σ : Type} : IsCv V fun _ : σ => (0 : PowerSeries C) := fun _ =>
  ⟨map_zero _, fun n => by rw [map_zero]; exact VF.Ge.zero 0⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ => 0, fun _ => 0, isCv_zero, isCv_zero, fun i => alongCv_zero (lg_const H i), fun q => by rw [alongCv_zero (sg_const H _), sub_zero]; rfl⟩`.
-/
theorem zero_mem (H : RLaw X V) (g : Fin 2) : 0 ∈ Cv X V g :=
  ⟨fun _ => 0, fun _ => 0, isCv_zero, isCv_zero, fun i => alongCv_zero (lg_const H i), fun q => by
    rw [alongCv_zero (sg_const H _), sub_zero]; rfl⟩

/- English proof (translation)
Introduce and unpack `a ⟨γ, lam, hγ, hlam, h1, h2⟩ b ⟨γ', lam', hγ', hlam', h1', h2'⟩`. Take `⟨γ'', hγ'', hL, hS⟩` from `hA γ γ' hγ hγ'`. Use `⟨γ'', fun q => lam q + lam' q + (alongCv γ'' (X.sg (X.u (1 - g) q)) - alongCv γ (X.sg (X.u (1 - g) q)) - alongCv γ' (X.sg (X.u (1 - g) q))), hγ'', ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `q`. Take `⟨c0, cI⟩` from `hS (X.u (1 - g) q) (H.uint (1 - g) q)`.

Use `⟨?_, fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_add, (hlam q).1, (hlam' q).1, c0]`. Simplify using the standard rewrite rules. Rewrite using `[map_add, map_add]`. Conclude with `(((hlam q).2 n).add ((hlam' q).2 n)).add (cI n)`.

Introduce `i`. Rewrite using `[hL i, h1 i, h1' i]`. Both sides reduce to the same expression. Introduce `q show a.2 q + b.2 q = _`. Rewrite using `[h2 q, h2' q]`.

Simplify using `only`. Normalize the expressions using the abelian group laws.
-/
theorem add_mem (H : RLaw X V) (hA : X.AddCvSt V) (g : Fin 2) :
    ∀ a ∈ Cv X V g, ∀ b ∈ Cv X V g, a + b ∈ Cv X V g := by
  rintro a ⟨γ, lam, hγ, hlam, h1, h2⟩ b ⟨γ', lam', hγ', hlam', h1', h2'⟩
  obtain ⟨γ'', hγ'', hL, hS⟩ := hA γ γ' hγ hγ'
  refine ⟨γ'', fun q => lam q + lam' q + (alongCv γ'' (X.sg (X.u (1 - g) q)) - alongCv γ (X.sg (X.u (1 - g) q)) -
    alongCv γ' (X.sg (X.u (1 - g) q))), hγ'', ?_, ?_, ?_⟩
  · intro q
    obtain ⟨c0, cI⟩ := hS (X.u (1 - g) q) (H.uint (1 - g) q)
    refine ⟨?_, fun n => ?_⟩
    · rw [map_add, map_add, (hlam q).1, (hlam' q).1, c0]
      simp
    · rw [map_add, map_add]
      exact (((hlam q).2 n).add ((hlam' q).2 n)).add (cI n)
  · intro i
    rw [hL i, h1 i, h1' i]
    rfl
  · intro q
    show a.2 q + b.2 q = _
    rw [h2 q, h2' q]
    dsimp only
    abel

/- English proof (translation)
Introduce and unpack `a ⟨γ, lam, hγ, hlam, h1, h2⟩`. Take `⟨δ, hδ, hneg⟩` from `exists_neg H hA hγ`. Take `⟨s, hs, hL, hS⟩` from `hA γ δ hγ hδ`. Establish `hs0 : s = fun _ => 0`. Use function extensionality and compare the values at `i`.

Rewrite using `[← ex_lg H (fun j => (hs j).1) i]`. Establish `: (fun j => alongCv s (X.lg j)) = fun _ => 0`. Use function extensionality and compare the values at `j`. Rewrite using `[hL j, hneg j, add_neg_cancel]`. Rewrite using `[this, alongCv_zero (H.exc i)]`.

Use `⟨δ, fun q => -lam q - (alongCv s (X.sg (X.u (1 - g) q)) - alongCv γ (X.sg (X.u (1 - g) q)) - alongCv δ (X.sg (X.u (1 - g) q))), hδ, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `q`. Take `⟨c0, cI⟩` from `hS (X.u (1 - g) q) (H.uint (1 - g) q)`. Use `⟨?_, fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, map_neg, (hlam q).1, c0]`.

Simplify using the standard rewrite rules. Rewrite using `[map_sub, map_neg]`. Conclude with `((hlam q).2 n).neg.sub (cI n)`. Introduce `i`. Rewrite using `[hneg i, h1 i]`.

Both sides reduce to the same expression. Introduce `q show -a.2 q = _ dsimp only`. Rewrite using `[h2 q, hs0, alongCv_zero (sg_const H _)]`. Normalize the expressions using the abelian group laws.
-/
theorem neg_mem (H : RLaw X V) (hA : X.AddCvSt V) (g : Fin 2) : ∀ a ∈ Cv X V g, -a ∈ Cv X V g := by
  rintro a ⟨γ, lam, hγ, hlam, h1, h2⟩
  obtain ⟨δ, hδ, hneg⟩ := exists_neg H hA hγ
  obtain ⟨s, hs, hL, hS⟩ := hA γ δ hγ hδ
  have hs0 : s = fun _ => 0 := by
    funext i
    rw [← ex_lg H (fun j => (hs j).1) i]
    have : (fun j => alongCv s (X.lg j)) = fun _ => 0 := by
      funext j
      rw [hL j, hneg j, add_neg_cancel]
    rw [this, alongCv_zero (H.exc i)]
  refine ⟨δ, fun q => -lam q - (alongCv s (X.sg (X.u (1 - g) q)) - alongCv γ (X.sg (X.u (1 - g) q)) -
    alongCv δ (X.sg (X.u (1 - g) q))), hδ, ?_, ?_, ?_⟩
  · intro q
    obtain ⟨c0, cI⟩ := hS (X.u (1 - g) q) (H.uint (1 - g) q)
    refine ⟨?_, fun n => ?_⟩
    · rw [map_sub, map_neg, (hlam q).1, c0]
      simp
    · rw [map_sub, map_neg]
      exact ((hlam q).2 n).neg.sub (cI n)
  · intro i
    rw [hneg i, h1 i]
    rfl
  · intro q
    show -a.2 q = _
    dsimp only
    rw [h2 q, hs0, alongCv_zero (sg_const H _)]
    abel

/- English proof (translation)
Introduce and unpack `a ⟨γ, lam, hγ, hlam, h1, h2⟩`. Establish `hτ : PowerSeries.constantCoeff (s • (PowerSeries.X : PowerSeries C)) = 0` using `by simp`. Establish `hcv : ∀ {σ : Type} (δ : σ → PowerSeries C), IsCv V δ → IsCv V fun i => PowerSeries.rescale s (δ i)`. Introduce `σ δ hδ i`. Use `⟨?_, fun n => ?_⟩` and prove the remaining obligations.

Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, PowerSeries.coeff_zero_eq_constantCoeff_apply, (hδ i).1, mul_zero]`. Rewrite using `[PowerSeries.coeff_rescale]`. Conclude with `(hs.pow n).mul_int ((hδ i).2 n)`. Establish `hal : ∀ f, alongCv (fun i => PowerSeries.rescale s (γ i)) f = PowerSeries.rescale s (alongCv γ f)`. Introduce `f`.

Simplify using `only [PowerSeries.rescale_eq_subst]`. Conclude with `alongCv_repar (fun i => (hγ i).1) hτ f`. Use `⟨fun i => PowerSeries.rescale s (γ i), fun q => PowerSeries.rescale s (lam q), hcv γ hγ, hcv lam hlam, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`. Rewrite using `[hal, h1 i]`.

Introduce `q show PowerSeries.rescale s (a.2 q) = _`. Rewrite using `[hal, h2 q, map_sub]`.
-/
theorem rescale_mem (g : Fin 2) (s : C) (hs : V.Ge 0 s) : ∀ a ∈ Cv X V g,
    ((fun i => PowerSeries.rescale s (a.1 i), fun q => PowerSeries.rescale s (a.2 q)) :
      ((κ → PowerSeries C) × (JJ I g → PowerSeries C))) ∈ Cv X V g := by
  rintro a ⟨γ, lam, hγ, hlam, h1, h2⟩
  have hτ : PowerSeries.constantCoeff (s • (PowerSeries.X : PowerSeries C)) = 0 := by simp
  have hcv : ∀ {σ : Type} (δ : σ → PowerSeries C), IsCv V δ → IsCv V fun i => PowerSeries.rescale s (δ i) := by
    intro σ δ hδ i
    refine ⟨?_, fun n => ?_⟩
    · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, (hδ i).1, mul_zero]
    · rw [PowerSeries.coeff_rescale]
      exact (hs.pow n).mul_int ((hδ i).2 n)
  have hal : ∀ f, alongCv (fun i => PowerSeries.rescale s (γ i)) f = PowerSeries.rescale s (alongCv γ f) := by
    intro f
    simp only [PowerSeries.rescale_eq_subst]
    exact alongCv_repar (fun i => (hγ i).1) hτ f
  refine ⟨fun i => PowerSeries.rescale s (γ i), fun q => PowerSeries.rescale s (lam q), hcv γ hγ, hcv lam hlam, ?_, ?_⟩
  · intro i
    rw [hal, h1 i]
  · intro q
    show PowerSeries.rescale s (a.2 q) = _
    rw [hal, h2 q, map_sub]

end GlobalTheory.RowLaw.CvGroup

/- English proof (translation)
Introduce `C _ V d _ I _ κ _ X H g`. Establish `hA` using `GlobalTheory.T.addCurveStable_of_integralGaugedFormalGroupLaw C V d I κ X H`. Conclude with `⟨CvGroup.zero_mem H g, CvGroup.add_mem H hA g, CvGroup.neg_mem H hA g, fun s hs => CvGroup.rescale_mem g s hs⟩`.
-/
theorem GlobalTheory.RowLaw.cv_group : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g, (0 ∈ Cv X V g) ∧ (∀ a ∈ Cv X V g, ∀ b ∈ Cv X V g, a + b ∈ Cv X V g) ∧ (∀ a ∈ Cv X V g, -a ∈ Cv X V g) ∧ (∀ s : C, V.Ge 0 s → ∀ a ∈ Cv X V g, ((fun i => PowerSeries.rescale s (a.1 i), fun q => PowerSeries.rescale s (a.2 q)) : ((κ → PowerSeries C) × (JJ I g → PowerSeries C))) ∈ Cv X V g) := by
  intro C _ V d _ I _ κ _ X H g
  have hA := GlobalTheory.T.addCurveStable_of_integralGaugedFormalGroupLaw C V d I κ X H
  exact ⟨CvGroup.zero_mem H g, CvGroup.add_mem H hA g, CvGroup.neg_mem H hA g, fun s hs => CvGroup.rescale_mem g s hs⟩
