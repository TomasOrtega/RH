import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLaw

/- English proof (translation)
Establish `hsa : MvPowerSeries.HasSubst a` using `MvPowerSeries.hasSubst_of_constantCoeff_zero ha`. Establish `hsb : MvPowerSeries.HasSubst b` using `MvPowerSeries.hasSubst_of_constantCoeff_zero hb`. Establish `hq : ∀ i, Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries C) ^ (m + 1)}) (a i) = Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries C) ^ (m + 1)}) (b i)`. Introduce `i`. Rewrite using `[Ideal.Quotient.eq, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]`.

Introduce `k hk`. Rewrite using `[map_sub, h i k (by omega), sub_self]`. Establish `hp : ∀ e : κ →₀ ℕ, PowerSeries.coeff m (e.prod fun s n => a s ^ n) = PowerSeries.coeff m (e.prod fun s n => b s ^ n)`. Introduce `e`. Establish `h1 : Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries C) ^ (m + 1)}) (e.prod fun s n => a s ^ n) = Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries C) ^ (m + 1)}) (e.prod fun s n => b s ^ n)`.

Simplify using `only [Finsupp.prod, map_prod, map_pow, hq]`. Rewrite `h1` using `[Ideal.Quotient.eq, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]`. Establish `h2` using `h1 m (by omega)`. Rewrite `h2` using `[map_sub, sub_eq_zero]`. Then use the resulting hypothesis. Use `show MvPowerSeries.coeff (Finsupp.single () m) (MvPowerSeries.subst a f) = MvPowerSeries.coeff (Finsupp.single () m) (MvPowerSeries.subst b f)`.

Rewrite using `[MvPowerSeries.coeff_subst hsa, MvPowerSeries.coeff_subst hsb]`. Use `finsum_congr fun e => ?_` and prove the remaining obligations. Conclude with `congrArg (fun z => MvPowerSeries.coeff e f • z) (hp e)`.
-/
theorem coeff_alongCv_congr {C : Type} [Field C] {κ : Type} [Finite κ] {a b : κ → PowerSeries C}
    (ha : ∀ i, PowerSeries.constantCoeff (a i) = 0) (hb : ∀ i, PowerSeries.constantCoeff (b i) = 0)
    (f : MvPowerSeries κ C) (m : ℕ)
    (h : ∀ i, ∀ k ≤ m, PowerSeries.coeff k (a i) = PowerSeries.coeff k (b i)) :
    PowerSeries.coeff m (alongCv a f) = PowerSeries.coeff m (alongCv b f) := by
  have hsa : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have hsb : MvPowerSeries.HasSubst b := MvPowerSeries.hasSubst_of_constantCoeff_zero hb
  have hq : ∀ i, Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries C) ^ (m + 1)}) (a i) =
      Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries C) ^ (m + 1)}) (b i) := by
    intro i
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
    intro k hk
    rw [map_sub, h i k (by omega), sub_self]
  have hp : ∀ e : κ →₀ ℕ, PowerSeries.coeff m (e.prod fun s n => a s ^ n) =
      PowerSeries.coeff m (e.prod fun s n => b s ^ n) := by
    intro e
    have h1 : Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries C) ^ (m + 1)}) (e.prod fun s n => a s ^ n) =
        Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries C) ^ (m + 1)}) (e.prod fun s n => b s ^ n) := by
      simp only [Finsupp.prod, map_prod, map_pow, hq]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at h1
    have h2 := h1 m (by omega)
    rwa [map_sub, sub_eq_zero] at h2
  show MvPowerSeries.coeff (Finsupp.single () m) (MvPowerSeries.subst a f) =
    MvPowerSeries.coeff (Finsupp.single () m) (MvPowerSeries.subst b f)
  rw [MvPowerSeries.coeff_subst hsa, MvPowerSeries.coeff_subst hsb]
  refine finsum_congr fun e => ?_
  exact congrArg (fun z => MvPowerSeries.coeff e f • z) (hp e)

/- English proof (translation)
Use `choose N hN using h`. Use `⟨(Finset.range (m + 1)).sup N, fun k hk => hN k _ ?_⟩` and prove the remaining obligations. Conclude with `Finset.le_sup (f := N) (Finset.mem_range.2 (by omega))`.
-/
theorem exists_forall_le_of_eventually {P : ℕ → ℕ → Prop} (h : ∀ m, ∃ n0, ∀ n ≥ n0, P m n) (m : ℕ) :
    ∃ n, ∀ k ≤ m, P k n := by
  choose N hN using h
  refine ⟨(Finset.range (m + 1)).sup N, fun k hk => hN k _ ?_⟩
  exact Finset.le_sup (f := N) (Finset.mem_range.2 (by omega))

/- English proof (translation)
Introduce `C _ V d _ I _ κ _ X hR g a b ha hlim`. Use `choose γ lam hγ hlam hlg hsg using ha`. Establish `hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0`. Introduce `i`. Use `hR.lin i 0 (by simp)` as an intermediate fact.

Simplify using `using this`. Establish `hslg : MvPowerSeries.HasSubst X.lg` using `MvPowerSeries.hasSubst_of_constantCoeff_zero hlg0`. Establish `hsex : MvPowerSeries.HasSubst X.ex` using `MvPowerSeries.hasSubst_of_constantCoeff_zero hR.exc`. Establish `hsγ : ∀ n, MvPowerSeries.HasSubst (γ n)` using `fun n => MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => (hγ n i).1`. Establish `ha0 : ∀ n i, PowerSeries.constantCoeff ((a n).1 i) = 0`.

Introduce `n i`. Rewrite using `[← hlg n i]`. Conclude with `MvPowerSeries.constantCoeff_subst_eq_zero (hsγ n) (fun i => (hγ n i).1) (hlg0 i)`. Establish `hb0 : ∀ i, PowerSeries.constantCoeff (b.1 i) = 0`. Introduce `i`.

Take `⟨n, hn⟩` from `hlim 0`. Use `(hn n le_rfl).1 i` as an intermediate fact. Rewrite `this` using `[PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Rewrite using `[← this, ha0]`. Establish `hsb : MvPowerSeries.HasSubst b.1` using `MvPowerSeries.hasSubst_of_constantCoeff_zero hb0`.

Establish `hγeq : ∀ n i, γ n i = alongCv (a n).1 (X.ex i)`. Introduce `n i`. Establish `h1 : (a n).1 = fun j => MvPowerSeries.subst (γ n) (X.lg j)` using `funext fun j => (hlg n j).symm`. Rewrite using `[h1]`. Use `show γ n i = MvPowerSeries.subst (fun j => MvPowerSeries.subst (γ n) (X.lg j)) (X.ex i)`.

Rewrite using `[← MvPowerSeries.subst_comp_subst_apply hslg (hsγ n), hR.exlg, MvPowerSeries.subst_X (hsγ n)]`. Set `Γ : κ → PowerSeries C` to `fun i => alongCv b.1 (X.ex i)`. Establish `hΓ0 : ∀ i, PowerSeries.constantCoeff (Γ i) = 0` using `fun i => MvPowerSeries.constantCoeff_subst_eq_zero hsb hb0 (hR.exc i)`. Establish `key : ∀ m, ∃ n, (∀ i, ∀ k ≤ m, PowerSeries.coeff k (γ n i) = PowerSeries.coeff k (Γ i)) ∧ ∀ q, PowerSeries.coeff m (lam n q) = PowerSeries.coeff m (b.2 q + alongCv Γ (X.sg (X.u (1 - g) q)))`. Introduce `m`.

Take `⟨n, hn⟩` from `exists_forall_le_of_eventually hlim m`. Establish `h1 : ∀ i, ∀ k ≤ m, PowerSeries.coeff k (γ n i) = PowerSeries.coeff k (Γ i)`. Introduce `i k hk`. Rewrite using `[hγeq]`. Conclude with `coeff_alongCv_congr (ha0 n) hb0 _ k fun j k' hk' => (hn k' (hk'.trans hk)).1 j`.

Use `⟨n, h1, fun q => ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, ← (hn m le_rfl).2 q, hsg n q, map_sub, coeff_alongCv_congr (fun i => (hγ n i).1) hΓ0 _ m h1, sub_add_cancel]`. Use `⟨Γ, fun q => b.2 q + alongCv Γ (X.sg (X.u (1 - g) q)), fun i => ⟨hΓ0 i, fun m => ?_⟩, fun q => ⟨?_, fun m => ?_⟩, fun i => ?_, fun q => by simp⟩` and prove the remaining obligations. Take `⟨n, hn, -⟩` from `key m`. Rewrite using `[← hn i m le_rfl]`.

Conclude with `(hγ n i).2 m`. Take `⟨n, -, hn⟩` from `key 0`. Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← hn q, PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Conclude with `(hlam n q).1`. Take `⟨n, -, hn⟩` from `key m`.

Rewrite using `[← hn q]`. Conclude with `(hlam n q).2 m`. Use `show MvPowerSeries.subst (fun j => MvPowerSeries.subst b.1 (X.ex j)) (X.lg i) = b.1 i`. Rewrite using `[← MvPowerSeries.subst_comp_subst_apply hsex hsb, hR.lgex, MvPowerSeries.subst_X hsb]`.
-/
theorem cv_closed_under_limits : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g (a : ℕ → ((κ → PowerSeries C) × (JJ I g → PowerSeries C))) (b : ((κ → PowerSeries C) × (JJ I g → PowerSeries C))), (∀ n, a n ∈ Cv X V g) → (∀ m, ∃ n0, ∀ n ≥ n0, (∀ i, PowerSeries.coeff m ((a n).1 i) = PowerSeries.coeff m (b.1 i)) ∧ ∀ q, PowerSeries.coeff m ((a n).2 q) = PowerSeries.coeff m (b.2 q)) → b ∈ Cv X V g := by
  intro C _ V d _ I _ κ _ X hR g a b ha hlim
  choose γ lam hγ hlam hlg hsg using ha
  have hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0 := by
    intro i
    have := hR.lin i 0 (by simp)
    simpa using this
  have hslg : MvPowerSeries.HasSubst X.lg := MvPowerSeries.hasSubst_of_constantCoeff_zero hlg0
  have hsex : MvPowerSeries.HasSubst X.ex := MvPowerSeries.hasSubst_of_constantCoeff_zero hR.exc
  have hsγ : ∀ n, MvPowerSeries.HasSubst (γ n) := fun n =>
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => (hγ n i).1
  have ha0 : ∀ n i, PowerSeries.constantCoeff ((a n).1 i) = 0 := by
    intro n i
    rw [← hlg n i]
    exact MvPowerSeries.constantCoeff_subst_eq_zero (hsγ n) (fun i => (hγ n i).1) (hlg0 i)
  have hb0 : ∀ i, PowerSeries.constantCoeff (b.1 i) = 0 := by
    intro i
    obtain ⟨n, hn⟩ := hlim 0
    have := (hn n le_rfl).1 i
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_zero_eq_constantCoeff_apply] at this
    rw [← this, ha0]
  have hsb : MvPowerSeries.HasSubst b.1 := MvPowerSeries.hasSubst_of_constantCoeff_zero hb0
  have hγeq : ∀ n i, γ n i = alongCv (a n).1 (X.ex i) := by
    intro n i
    have h1 : (a n).1 = fun j => MvPowerSeries.subst (γ n) (X.lg j) := funext fun j => (hlg n j).symm
    rw [h1]
    show γ n i = MvPowerSeries.subst (fun j => MvPowerSeries.subst (γ n) (X.lg j)) (X.ex i)
    rw [← MvPowerSeries.subst_comp_subst_apply hslg (hsγ n), hR.exlg, MvPowerSeries.subst_X (hsγ n)]
  let Γ : κ → PowerSeries C := fun i => alongCv b.1 (X.ex i)
  have hΓ0 : ∀ i, PowerSeries.constantCoeff (Γ i) = 0 := fun i =>
    MvPowerSeries.constantCoeff_subst_eq_zero hsb hb0 (hR.exc i)
  have key : ∀ m, ∃ n, (∀ i, ∀ k ≤ m, PowerSeries.coeff k (γ n i) = PowerSeries.coeff k (Γ i)) ∧
      ∀ q, PowerSeries.coeff m (lam n q) = PowerSeries.coeff m (b.2 q + alongCv Γ (X.sg (X.u (1 - g) q))) := by
    intro m
    obtain ⟨n, hn⟩ := exists_forall_le_of_eventually hlim m
    have h1 : ∀ i, ∀ k ≤ m, PowerSeries.coeff k (γ n i) = PowerSeries.coeff k (Γ i) := by
      intro i k hk
      rw [hγeq]
      exact coeff_alongCv_congr (ha0 n) hb0 _ k fun j k' hk' => (hn k' (hk'.trans hk)).1 j
    refine ⟨n, h1, fun q => ?_⟩
    rw [map_add, ← (hn m le_rfl).2 q, hsg n q, map_sub,
      coeff_alongCv_congr (fun i => (hγ n i).1) hΓ0 _ m h1, sub_add_cancel]
  refine ⟨Γ, fun q => b.2 q + alongCv Γ (X.sg (X.u (1 - g) q)), fun i => ⟨hΓ0 i, fun m => ?_⟩,
    fun q => ⟨?_, fun m => ?_⟩, fun i => ?_, fun q => by simp⟩
  · obtain ⟨n, hn, -⟩ := key m
    rw [← hn i m le_rfl]
    exact (hγ n i).2 m
  · obtain ⟨n, -, hn⟩ := key 0
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← hn q, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (hlam n q).1
  · obtain ⟨n, -, hn⟩ := key m
    rw [← hn q]
    exact (hlam n q).2 m
  · show MvPowerSeries.subst (fun j => MvPowerSeries.subst b.1 (X.ex j)) (X.lg i) = b.1 i
    rw [← MvPowerSeries.subst_comp_subst_apply hsex hsb, hR.lgex, MvPowerSeries.subst_X hsb]

end GlobalTheory.RowLaw
