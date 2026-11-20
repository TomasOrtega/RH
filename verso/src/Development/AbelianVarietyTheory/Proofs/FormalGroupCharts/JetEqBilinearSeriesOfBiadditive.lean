import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MvPowerSeriesJetEqCalculus

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
namespace GlobalTheory.ChartCmp.BilAdd

variable {k : Type} [CommRing k] {d : ℕ}

/- English proof (translation)
The claim follows from `MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => h p.1 p.2`.
-/
theorem hasSubst_pts {n l : ℕ} (a : Fin l → Pt k n d) (h : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) :
    MvPowerSeries.HasSubst (fun p : Fin l × Fin d => a p.1 p.2) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => h p.1 p.2

/- English proof (translation)
The claim follows from `MvPowerSeries.subst_add (hasSubst_pts a h) f g`.
-/
theorem ev_add {n l : ℕ} (a : Fin l → Pt k n d) (h : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) (f g : PS k l d) :
    ev a (f + g) = ev a f + ev a g :=
  MvPowerSeries.subst_add (hasSubst_pts a h) f g

/- English proof (translation)
The claim follows from `MvPowerSeries.subst_X (hasSubst_pts a h) (j, i)`.
-/
theorem ev_pt {n l : ℕ} (a : Fin l → Pt k n d) (h : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) (j : Fin l) (i : Fin d) :
    ev a (pt k d j i) = a j i :=
  MvPowerSeries.subst_X (hasSubst_pts a h) (j, i)

/- English proof (translation)
The claim follows from `MvPowerSeries.subst_comp_subst_apply (hasSubst_pts a ha) (hasSubst_pts b hb) f`.
-/
theorem ev_ev {n l r : ℕ} (a : Fin l → Pt k n d) (b : Fin n → Pt k r d)
    (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) (hb : ∀ j i, MvPowerSeries.constantCoeff (b j i) = 0)
    (f : PS k l d) : ev b (ev a f) = ev (fun j i => ev b (a j i)) f :=
  MvPowerSeries.subst_comp_subst_apply (hasSubst_pts a ha) (hasSubst_pts b hb) f

/- English proof (translation)
The claim follows from `MvPowerSeries.constantCoeff_X _`.
-/
theorem const_pt {n : ℕ} (j : Fin n) (i : Fin d) : MvPowerSeries.constantCoeff (pt k d j i) = 0 :=
  MvPowerSeries.constantCoeff_X _

/- English proof (translation)
Use `MvPowerSeries.subst_self (σ := Fin n × Fin d) (R := k)` as an intermediate fact. Conclude with `congrFun this f`.
-/
theorem ev_id {n : ℕ} (f : PS k n d) : ev (fun j => pt k d j) f = f := by
  have := MvPowerSeries.subst_self (σ := Fin n × Fin d) (R := k)
  exact congrFun this f

def degIn (j : Fin 2) (e : Fin 2 × Fin d →₀ ℕ) : ℕ := ∑ i, e (j, i)

/- English proof (translation)
Establish `h : ev (n` using `2) (fun l => if l = j then pt k d l + pt k d l else pt k d l) g = MvPowerSeries.rescale (fun p : Fin 2 × Fin d => if p.1 = j then (2 : k) else 1) g := by`. Rewrite using `[MvPowerSeries.rescale_eq_subst]`. Unfold `ev`. Use `congr 1`. Use function extensionality and compare the values at `p`.

Distinguish the cases in `hp : p.1 = j`. Substitute `hp` using the available equality. Simplify using `[pt, two_smul]`. Simplify using `[hp, pt]`. Rewrite using `[h, MvPowerSeries.coeff_rescale]`.

Use `congr 1`. Rewrite using `[Finsupp.prod_fintype _ _ (by simp), Fintype.prod_prod_type, degIn, ← Finset.prod_pow_eq_pow_sum, Finset.prod_eq_single j]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[hb]`.

Simplify using the standard rewrite rules.
-/
theorem coeff_double (j : Fin 2) (g : PS k 2 d) (e : Fin 2 × Fin d →₀ ℕ) :
    MvPowerSeries.coeff e (ev (n := 2) (fun l => if l = j then pt k d l + pt k d l else pt k d l) g) =
      2 ^ degIn j e * MvPowerSeries.coeff e g := by
  have h : ev (n := 2) (fun l => if l = j then pt k d l + pt k d l else pt k d l) g =
      MvPowerSeries.rescale (fun p : Fin 2 × Fin d => if p.1 = j then (2 : k) else 1) g := by
    rw [MvPowerSeries.rescale_eq_subst]
    unfold ev
    congr 1
    funext p
    by_cases hp : p.1 = j
    · subst hp
      simp [pt, two_smul]
    · simp [hp, pt]
  rw [h, MvPowerSeries.coeff_rescale]
  congr 1
  rw [Finsupp.prod_fintype _ _ (by simp), Fintype.prod_prod_type, degIn, ← Finset.prod_pow_eq_pow_sum,
    Finset.prod_eq_single j]
  · simp
  · intro b _ hb; simp [hb]
  · simp

/- English proof (translation)
Establish `h0 : ((2 : ℚ) ^ a - 2) ≠ 0`. Introduce `h`. Apply `ha` to reduce the goal to its premises. Establish `: (2 : ℚ) ^ a = 2 ^ 1` using `by linarith`. Conclude with `(pow_right_injective₀ (by norm_num) (by norm_num)) this`.

Establish `hu : IsUnit ((2 : k) ^ a - 2)`. Use `(IsUnit.mk0 _ h0).map (algebraMap ℚ k)` as an intermediate fact. Simplify `this` using `[map_ofNat]`. Apply `hu.mul_right_eq_zero.mp` to reduce the goal to its premises. Take the linear combination `h`.
-/
theorem eq_zero_of_double [Algebra ℚ k] {a : ℕ} (ha : a ≠ 1) {c : k} (h : 2 ^ a * c = c + c) : c = 0 := by
  have h0 : ((2 : ℚ) ^ a - 2) ≠ 0 := by
    intro h
    apply ha
    have : (2 : ℚ) ^ a = 2 ^ 1 := by linarith
    exact (pow_right_injective₀ (by norm_num) (by norm_num)) this
  have hu : IsUnit ((2 : k) ^ a - 2) := by
    have := (IsUnit.mk0 _ h0).map (algebraMap ℚ k)
    simpa [map_ofNat] using this
  apply hu.mul_right_eq_zero.mp
  linear_combination h

/- English proof (translation)
Establish `key : ∀ f : Fin d → ℕ, ∑ i, f i = 1 → ∃ i, ∀ i', f i' = if i = i' then 1 else 0`. Introduce `f hf`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, f i ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`.

Simplify using `[hc] at hf`. Use `⟨i, fun i' => ?_⟩` and prove the remaining obligations. Rewrite `hf` using `[← Finset.add_sum_erase _ _ (Finset.mem_univ i)]`. Use `split_ifs with h`. Substitute `h` using the available equality.

Use linear arithmetic over natural numbers and integers. Use `Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _) (Finset.mem_erase.mpr ⟨fun hh => h hh.symm, Finset.mem_univ i'⟩ : i' ∈ Finset.univ.erase i)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨i, hi⟩` from `key _ h0`. Take `⟨j, hj⟩` from `key _ h1`.

Use `⟨i, j, ?_⟩` and prove the remaining obligations. Use extensionality with `⟨l, p⟩`. Use `fin_cases l`. Simplify using `[hi, Finsupp.single_apply]`. Simplify using `[hj, Finsupp.single_apply]`.
-/
theorem exists_single {e : Fin 2 × Fin d →₀ ℕ} (h0 : degIn 0 e = 1) (h1 : degIn 1 e = 1) :
    ∃ i j, e = Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1 := by
  have key : ∀ f : Fin d → ℕ, ∑ i, f i = 1 → ∃ i, ∀ i', f i' = if i = i' then 1 else 0 := by
    intro f hf
    obtain ⟨i, hi⟩ : ∃ i, f i ≠ 0 := by
      by_contra hc
      push Not at hc
      simp [hc] at hf
    refine ⟨i, fun i' => ?_⟩
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hf
    split_ifs with h
    · subst h
      omega
    · have := Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _)
        (Finset.mem_erase.mpr ⟨fun hh => h hh.symm, Finset.mem_univ i'⟩ : i' ∈ Finset.univ.erase i)
      omega
  obtain ⟨i, hi⟩ := key _ h0
  obtain ⟨j, hj⟩ := key _ h1
  refine ⟨i, j, ?_⟩
  ext ⟨l, p⟩
  fin_cases l
  · simp [hi, Finsupp.single_apply]
  · simp [hj, Finsupp.single_apply]

/- English proof (translation)
Simplify using `only [bilSer, map_sum, pt, MvPowerSeries.coeff_C_mul, MvPowerSeries.X, MvPowerSeries.monomial_mul_monomial, MvPowerSeries.coeff_monomial]`. Simplify using the standard rewrite rules.
-/
theorem coeff_bilSer (β : Matrix (Fin d) (Fin d) k) (e : Fin 2 × Fin d →₀ ℕ) :
    MvPowerSeries.coeff e (bilSer β (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      ∑ i, ∑ j, if e = Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1 then β i j else 0 := by
  simp only [bilSer, map_sum, pt, MvPowerSeries.coeff_C_mul, MvPowerSeries.X, MvPowerSeries.monomial_mul_monomial,
    MvPowerSeries.coeff_monomial]
  simp

/- English proof (translation)
Establish `h0` using `DFunLike.congr_fun h (0, i)`. Establish `h1` using `DFunLike.congr_fun h (1, j)`. Simplify using `[Finsupp.single_apply] at h0 h1`. Conclude with `⟨h0.symm, h1.symm⟩`.
-/
theorem single_inj {i j i' j' : Fin d}
    (h : (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1 : Fin 2 × Fin d →₀ ℕ) =
      Finsupp.single ((0 : Fin 2), i') 1 + Finsupp.single ((1 : Fin 2), j') 1) : i = i' ∧ j = j' := by
  have h0 := DFunLike.congr_fun h (0, i)
  have h1 := DFunLike.congr_fun h (1, j)
  simp [Finsupp.single_apply] at h0 h1
  exact ⟨h0.symm, h1.symm⟩

/- English proof (translation)
Introduce `e he`. Use `Eq.trans ?_ (coeff_bilSer _ e).symm` and prove the remaining obligations. Distinguish the cases in `hex : ∃ i j, e = Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1`. Take `⟨i, j, rfl⟩` from `hex`. Rewrite using `[Finset.sum_eq_single i, Finset.sum_eq_single j, if_pos rfl]`.

Introduce `b _ hb`. Conclude with `if_neg fun hh => hb (single_inj hh).2.symm`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Conclude with `Finset.sum_eq_zero fun c _ => if_neg fun hh => hb (single_inj hh).1.symm`.

Simplify using the standard rewrite rules. Establish `hz : MvPowerSeries.coeff e g = 0`. Establish `: ∃ j, degIn j e ≠ 1`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`.

Conclude with `hex (exists_single (hc 0) (hc 1))`. Take `⟨j, hj⟩` from `this`. Use `h j e he` as an intermediate fact. Rewrite `this` using `[coeff_double, map_add]`. Conclude with `eq_zero_of_double hj this`.

Rewrite using `[hz]`. Use `symm`. Conclude with `Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => if_neg fun hh => hex ⟨i, j, hh⟩`.
-/
theorem jeq_bil_of_double [Algebra ℚ k] (m : ℕ) (g : PS k 2 d)
    (h : ∀ j : Fin 2, JEq m (ev (n := 2) (fun l => if l = j then pt k d l + pt k d l else pt k d l) g) (g + g)) :
    JEq m g (bilSer (fun i j => MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1) g)
      (pt k (n := 2) d 0) (pt k (n := 2) d 1)) := by
  intro e he
  refine Eq.trans ?_ (coeff_bilSer _ e).symm
  by_cases hex : ∃ i j, e = Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1
  · obtain ⟨i, j, rfl⟩ := hex
    rw [Finset.sum_eq_single i, Finset.sum_eq_single j, if_pos rfl]
    · intro b _ hb
      exact if_neg fun hh => hb (single_inj hh).2.symm
    · simp
    · intro b _ hb
      exact Finset.sum_eq_zero fun c _ => if_neg fun hh => hb (single_inj hh).1.symm
    · simp
  · have hz : MvPowerSeries.coeff e g = 0 := by
      have : ∃ j, degIn j e ≠ 1 := by
        by_contra hc
        push Not at hc
        exact hex (exists_single (hc 0) (hc 1))
      obtain ⟨j, hj⟩ := this
      have := h j e he
      rw [coeff_double, map_add] at this
      exact eq_zero_of_double hj this
    rw [hz]
    symm
    exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => if_neg fun hh => hex ⟨i, j, hh⟩

/- English proof (translation)
Rewrite using `[ev_ev _ _ _ hb]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Apply the tactic sequence `fin_cases j <;> rfl`. Introduce `j i fin_cases j`.

Conclude with `hu i`. Conclude with `hv i`.
-/
theorem ev_pair (b : Fin 3 → Pt k 2 d) (hb : ∀ j i, MvPowerSeries.constantCoeff (b j i) = 0) (g : PS k 2 d)
    (u v : Pt k 3 d) (hu : ∀ i, MvPowerSeries.constantCoeff (u i) = 0) (hv : ∀ i, MvPowerSeries.constantCoeff (v i) = 0) :
    ev b (ev ![u, v] g) = ev ![fun i => ev b (u i), fun i => ev b (v i)] g := by
  rw [ev_ev _ _ _ hb]
  · congr 1
    funext j
    fin_cases j <;> rfl
  · intro j i
    fin_cases j
    · exact hu i
    · exact hv i

/- English proof (translation)
Introduce `k _ _ d m g h1 h2`. Establish `hsub` using `(GlobalTheory.ChartCmp.JCalc.jeq_calculus k m).2.2.2.1`. Establish `hid : ev (n` using `2) ![pt k (n := 2) d 0, pt k (n := 2) d 1] g = g := by`. Use `Eq.trans ?_ (ev_id g)` and prove the remaining obligations. Use `congr 1`.

Use function extensionality and compare the values at `j`. Apply the tactic sequence `fin_cases j <;> rfl`. Establish `hc : ∀ (s : Fin 3) i, MvPowerSeries.constantCoeff (pt k (n` using `3) d s i) = 0 := fun s i => const_pt s i`. Establish `hc2 : ∀ (s t : Fin 3) i, MvPowerSeries.constantCoeff ((pt k (n` using `3) d s + pt k (n := 3) d t) i) = 0 := by`. Introduce `s t i`.

Simplify using `[hc]`. Apply `jeq_bil_of_double` to reduce the goal to its premises. Introduce `j`. Use `fin_cases j`. Establish `hb : ∀ (s : Fin 3) i, MvPowerSeries.constantCoeff ((![pt k (n` using `2) d 0, pt k (n := 2) d 0, pt k (n := 2) d 1] : Fin 3 → Pt k 2 d) s i) = 0 := by`.

Introduce `s i`. Apply the tactic sequence `fin_cases s <;> exact const_pt _ _`. Use `hsub d 3 2 _ _ _ _ hb hb (fun _ _ => JEq.refl _ _) h1` as an intermediate fact. Rewrite `this` using `[ev_add _ hb, ev_pair _ hb _ _ _ (hc2 _ _) (hc _), ev_pair _ hb _ _ _ (hc _) (hc _), ev_pair _ hb _ _ _ (hc _) (hc _)]`. Simplify using `only [Pi.add_apply, ev_add _ hb, ev_pt _ hb] at this`.

Use `this using 2` and compare the differences between its conclusion and the goal. Apply the tactic sequence `funext l fin_cases l <;> rfl`. Conclude with `hid.symm`. Conclude with `hid.symm`. Establish `hb : ∀ (s : Fin 3) i, MvPowerSeries.constantCoeff ((![pt k (n` using `2) d 0, pt k (n := 2) d 1, pt k (n := 2) d 1] : Fin 3 → Pt k 2 d) s i) = 0 := by`.

Introduce `s i`. Apply the tactic sequence `fin_cases s <;> exact const_pt _ _`. Use `hsub d 3 2 _ _ _ _ hb hb (fun _ _ => JEq.refl _ _) h2` as an intermediate fact. Rewrite `this` using `[ev_add _ hb, ev_pair _ hb _ _ _ (hc _) (hc2 _ _), ev_pair _ hb _ _ _ (hc _) (hc _), ev_pair _ hb _ _ _ (hc _) (hc _)]`. Simplify using `only [Pi.add_apply, ev_add _ hb, ev_pt _ hb] at this`.

Use `this using 2` and compare the differences between its conclusion and the goal. Apply the tactic sequence `funext l fin_cases l <;> rfl`. Conclude with `hid.symm`. Conclude with `hid.symm`.
-/
theorem jeq_bilSer_of_biadditive : ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d m : ℕ) (g : PS k 2 d), JEq m (ev (n := 3) ![pt k (n := 3) d 0 + pt k (n := 3) d 1, pt k (n := 3) d 2] g) (ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 2] g + ev (n := 3) ![pt k (n := 3) d 1, pt k (n := 3) d 2] g) → JEq m (ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 1 + pt k (n := 3) d 2] g) (ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 1] g + ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 2] g) → JEq m g (bilSer (fun i j => MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1) g) (pt k (n := 2) d 0) (pt k (n := 2) d 1)) := by
  intro k _ _ d m g h1 h2
  have hsub := (GlobalTheory.ChartCmp.JCalc.jeq_calculus k m).2.2.2.1
  have hid : ev (n := 2) ![pt k (n := 2) d 0, pt k (n := 2) d 1] g = g := by
    refine Eq.trans ?_ (ev_id g)
    congr 1
    funext j
    fin_cases j <;> rfl
  have hc : ∀ (s : Fin 3) i, MvPowerSeries.constantCoeff (pt k (n := 3) d s i) = 0 := fun s i => const_pt s i
  have hc2 : ∀ (s t : Fin 3) i, MvPowerSeries.constantCoeff ((pt k (n := 3) d s + pt k (n := 3) d t) i) = 0 := by
    intro s t i
    simp [hc]
  apply jeq_bil_of_double
  intro j
  fin_cases j
  · have hb : ∀ (s : Fin 3) i, MvPowerSeries.constantCoeff
        ((![pt k (n := 2) d 0, pt k (n := 2) d 0, pt k (n := 2) d 1] : Fin 3 → Pt k 2 d) s i) = 0 := by
      intro s i
      fin_cases s <;> exact const_pt _ _
    have := hsub d 3 2 _ _ _ _ hb hb (fun _ _ => JEq.refl _ _) h1
    rw [ev_add _ hb, ev_pair _ hb _ _ _ (hc2 _ _) (hc _), ev_pair _ hb _ _ _ (hc _) (hc _),
      ev_pair _ hb _ _ _ (hc _) (hc _)] at this
    simp only [Pi.add_apply, ev_add _ hb, ev_pt _ hb] at this
    convert this using 2
    · funext l
      fin_cases l <;> rfl
    · exact hid.symm
    · exact hid.symm
  · have hb : ∀ (s : Fin 3) i, MvPowerSeries.constantCoeff
        ((![pt k (n := 2) d 0, pt k (n := 2) d 1, pt k (n := 2) d 1] : Fin 3 → Pt k 2 d) s i) = 0 := by
      intro s i
      fin_cases s <;> exact const_pt _ _
    have := hsub d 3 2 _ _ _ _ hb hb (fun _ _ => JEq.refl _ _) h2
    rw [ev_add _ hb, ev_pair _ hb _ _ _ (hc _) (hc2 _ _), ev_pair _ hb _ _ _ (hc _) (hc _),
      ev_pair _ hb _ _ _ (hc _) (hc _)] at this
    simp only [Pi.add_apply, ev_add _ hb, ev_pt _ hb] at this
    convert this using 2
    · funext l
      fin_cases l <;> rfl
    · exact hid.symm
    · exact hid.symm

end GlobalTheory.ChartCmp.BilAdd
