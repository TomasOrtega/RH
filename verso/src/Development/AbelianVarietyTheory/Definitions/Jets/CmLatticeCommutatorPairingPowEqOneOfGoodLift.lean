import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEqLatticeCurve

noncomputable section
open PowerSeries
open scoped ComplexConjugate

namespace GlobalTheory.MomOne

def wK (d : ℕ) : ℂ := (1 + Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2

def InOK (d : ℕ) (z : ℂ) : Prop := ∃ u v : ℤ, z = (u : ℂ) + (v : ℂ) * wK d

def Split (d q : ℕ) : Prop := (q = 2 ∧ d % 8 = 7) ∨ (q ≠ 2 ∧ jacobiSym (-(d : ℤ)) q = 1)

def eis (d k : ℕ) : ℂ := ∑' w : {w : ℂ // InOK d w ∧ w ≠ 0}, 1 / (w : ℂ) ^ (2 * k)

def discr (d : ℕ) : ℂ := (60 * eis d 2) ^ 3 - 27 * (140 * eis d 3) ^ 2

def IsOK (d : ℕ) (L : PeriodPair) : Prop := ∀ z : ℂ, z ∈ L.lattice ↔ InOK d z

def h1 (d : ℕ) (z w : ℂ) : ℂ := ((2 / Real.sqrt d : ℝ) : ℂ) * (z * conj w)

def U1 (d : ℕ) (x : ℂ) (F : ℂ → ℂ) : ℂ → ℂ :=
  fun z => F (z + x) * Complex.exp (-(Real.pi : ℂ) * h1 d z x - (Real.pi : ℂ) / 2 * h1 d x x)

def W1 (d : ℕ) (x : ℂ) (F : ℂ → ℂ) : ℂ → ℂ :=
  fun z => Complex.exp ((Real.pi : ℂ) * Complex.I * ((Complex.normSq x : ℝ) : ℂ)) * U1 d x F z

def kap1 (d : ℕ) (x y : ℂ) : ℂ := Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * (((h1 d x y).im : ℝ) : ℂ))

def IsTh (d : ℕ) (θ : ℂ → ℂ) : Prop :=
  Differentiable ℂ θ ∧ θ 0 = 1 ∧ (∀ z, θ (-z) = θ z) ∧ (∀ x, InOK d x → W1 d x θ = θ) ∧
    ∀ z, θ z = 0 → InOK d (z - 1 / 2)

def PrimeTo (d q : ℕ) (t : ℂ) : Prop := ∃ s : ℕ, 0 < s ∧ Nat.Coprime s q ∧ InOK d ((s : ℂ) * t)

def tay (G : ℂ → ℂ) : ℂ⟦X⟧ := PowerSeries.mk fun n => iteratedDeriv n G 0 / (n.factorial : ℂ)

def Ell (L : PeriodPair) (φ : ℂ → ℂ) : Prop := Meromorphic φ ∧ ∀ l ∈ L.lattice, ∀ z, φ (z + l) = φ z

variable {q : ℕ} [Fact q.Prime]

def zc (a : ℤ_[q]) : ℂ_[q] := algebraMap ℚ_[q] ℂ_[q] (a : ℚ_[q])

def logS : ℂ_[q]⟦X⟧ := PowerSeries.mk fun n => if n = 0 then 0 else (-1) ^ (n + 1) / (n : ℂ_[q])

def mulS (a : ℤ_[q]) : ℂ_[q]⟦X⟧ := PowerSeries.mk fun n => if n = 0 then 0 else zc (Ring.choose a n)

def DT (f : ℂ_[q]⟦X⟧) : ℂ_[q]⟦X⟧ := (1 + X) * derivative ℂ_[q] f

def Bd (C : ℝ) (f : ℂ_[q]⟦X⟧) : Prop := ∀ n, ‖coeff n f‖ ≤ C

def Bdd (f : ℂ_[q]⟦X⟧) : Prop := ∃ C, Bd C f

def ev (f : ℂ_[q]⟦X⟧) (x : ℂ_[q]) : ℂ_[q] := ∑' n, coeff n f * x ^ n

def shiftS (ζ : ℂ_[q]) (f : ℂ_[q]⟦X⟧) : ℂ_[q]⟦X⟧ :=
  PowerSeries.mk fun n => ∑' m, coeff m f * ((m.choose n : ℂ_[q]) * ζ ^ n * (ζ - 1) ^ (m - n))

def hat (ι : ℂ ≃+* ℂ_[q]) (ℓ : ℂ_[q]⟦X⟧) (G : ℂ → ℂ) : ℂ_[q]⟦X⟧ :=
  (PowerSeries.map (ι : ℂ →+* ℂ_[q]) (tay G)).subst ℓ

structure Mdl (q : ℕ) [Fact q.Prime] where

  ι : ℂ ≃+* ℂ_[q]

  L : PeriodPair

  c : ℂ

  W : WeierstrassCurve ℂ_[q]

namespace Mdl
variable (M : Mdl q)

def Ok : Prop :=
  M.c ≠ 0 ∧ ‖M.W.a₁‖ ≤ 1 ∧ ‖M.W.a₂‖ ≤ 1 ∧ ‖M.W.a₃‖ ≤ 1 ∧ ‖M.W.a₄‖ ≤ 1 ∧ ‖M.W.a₆‖ ≤ 1 ∧ ‖M.W.Δ‖ = 1 ∧
    M.W.c₄ / 12 = M.ι (M.L.g₂ / M.c ^ 4) ∧ M.W.c₆ / 216 = M.ι (M.L.g₃ / M.c ^ 6)

def x (z : ℂ) : ℂ := M.L.weierstrassP z / M.c ^ 2 - M.ι.symm (M.W.b₂ / 12)

def y (z : ℂ) : ℂ :=
  (M.L.derivWeierstrassP z / M.c ^ 3 - M.ι.symm M.W.a₁ * M.x z - M.ι.symm M.W.a₃) / 2

open Classical in

def u (z : ℂ) : ℂ := if z ∈ M.L.lattice then 0 else -M.x z / M.y z

open Classical in

def w (z : ℂ) : ℂ := if z ∈ M.L.lattice then 0 else -1 / M.y z

def Small (z : ℂ) : Prop := z ∈ M.L.lattice ∨ 1 < ‖M.ι (M.x z)‖

def Chart (ℓ : ℂ_[q]⟦X⟧) : Prop :=
  M.Ok ∧ constantCoeff ℓ = 0 ∧ Bd 1 (hat M.ι ℓ M.u) ∧ ‖coeff 1 (hat M.ι ℓ M.u)‖ = 1

def MChart (ω : ℂ_[q]) : Prop := M.Chart (C ω * logS)

def At (ω ζ : ℂ_[q]) (z : ℂ) : Prop :=
  M.Small z ∧ ‖ζ - 1‖ < 1 ∧ ev (hat M.ι (C ω * logS) M.u) (ζ - 1) = M.ι (M.u z)

end Mdl

def Good (ι : ℂ ≃+* ℂ_[q]) (d n s : ℕ) (y : ℂ) : Prop :=
  ∃ v : ℂ, InOK d v ∧ ‖ι (conj v)‖ ≤ (q : ℝ) ^ (-(2 * n : ℤ)) ∧ y = (s : ℂ) * v / (q : ℂ) ^ n

def ThetaLaws (ι : ℂ ≃+* ℂ_[q]) (d : ℕ) (ω : ℂ_[q]) (θ : ℂ → ℂ) : Prop :=
  (∀ t, PrimeTo d q t → Bd 1 (hat ι (C ω * logS) (U1 d t θ))) ∧
  (∀ (t y : ℂ) (n s : ℕ), Nat.Coprime s q → InOK d ((s : ℂ) * t) → Good ι d n s y →
    ι (kap1 d 1 y) ^ (q ^ n) = 1 ∧
    hat ι (C ω * logS) (W1 d y (U1 d t θ)) = shiftS (ι (kap1 d 1 y)) (hat ι (C ω * logS) (U1 d t θ))) ∧
  ∀ (a m : ℕ) (c : Fin m → ℂ_[q]) (s : Fin m → ℂ) (t : ℂ) (B : ℝ), (∀ j, PrimeTo d q (s j)) → PrimeTo d q t →
    Bd B (∑ j, C (c j) * hat ι (C ω * logS) (U1 d (s j) θ) ^ a) →
    Bd B (∑ j, C (c j) * hat ι (C ω * logS) (U1 d t (U1 d (s j) θ)) ^ a)

namespace Basic
open Filter Topology

/- English proof (translation)
Use extensionality with `n`. Simplify using `[logS, coeff_log]`.
-/
theorem logS_eq : (logS : ℂ_[q]⟦X⟧) = PowerSeries.log ℂ_[q] := by
  ext n; simp [logS, coeff_log]

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[map_sub, coeff_map, binomialSeries_coeff, smul_eq_mul, mul_one, mulS, coeff_mk, coeff_one]`. Break down `n with _ | n` into its components or cases. Simplify using the standard rewrite rules. Simplify using `only [Nat.succ_ne_zero, if_false, sub_zero]`.

Both sides reduce to the same expression.
-/
theorem mulS_eq (a : ℤ_[q]) :
    mulS a = PowerSeries.map ((algebraMap ℚ_[q] ℂ_[q]).comp PadicInt.Coe.ringHom) (binomialSeries ℤ_[q] a) - 1 := by
  ext n
  rw [map_sub, coeff_map, binomialSeries_coeff, smul_eq_mul, mul_one, mulS, coeff_mk, coeff_one]
  rcases n with _ | n
  · simp
  · simp only [Nat.succ_ne_zero, if_false, sub_zero]; rfl

/- English proof (translation)
Establish `h1 : eis d k = ∑' w : ({w : ℂ | InOK d w ∧ w ≠ 0} : Set ℂ), (fun z : ℂ => (z ^ (2 * k))⁻¹) w`. Simplify using `only [eis, one_div]`. Both sides reduce to the same expression. Establish `h2 : L.G (2 * k) = ∑' w : (L.lattice : Set ℂ), (fun z : ℂ => (z ^ (2 * k))⁻¹) w` using `rfl`. Rewrite using `[h1, h2, tsum_subtype _ fun z : ℂ => (z ^ (2 * k))⁻¹, tsum_subtype _ fun z : ℂ => (z ^ (2 * k))⁻¹]`.

Use `tsum_congr fun z => ?_` and prove the remaining obligations. Distinguish the cases in `hz : z = 0`. Substitute `hz` using the available equality. Simplify using `[Set.indicator, hk.ne']`. Establish `e : z ∈ {w : ℂ | InOK d w ∧ w ≠ 0} ↔ z ∈ (L.lattice : Set ℂ)` using `by simp [hz, h z]`.

Distinguish the cases in `hL : z ∈ (L.lattice : Set ℂ)`. Rewrite using `[Set.indicator_of_mem hL, Set.indicator_of_mem (e.2 hL)]`. Rewrite using `[Set.indicator_of_notMem hL, Set.indicator_of_notMem (fun h' => hL (e.1 h'))]`.
-/
theorem eis_eq {d : ℕ} {L : PeriodPair} (h : IsOK d L) {k : ℕ} (hk : 0 < k) : eis d k = L.G (2 * k) := by
  have h1 : eis d k = ∑' w : ({w : ℂ | InOK d w ∧ w ≠ 0} : Set ℂ), (fun z : ℂ => (z ^ (2 * k))⁻¹) w := by
    simp only [eis, one_div]; rfl
  have h2 : L.G (2 * k) = ∑' w : (L.lattice : Set ℂ), (fun z : ℂ => (z ^ (2 * k))⁻¹) w := rfl
  rw [h1, h2, tsum_subtype _ fun z : ℂ => (z ^ (2 * k))⁻¹, tsum_subtype _ fun z : ℂ => (z ^ (2 * k))⁻¹]
  refine tsum_congr fun z => ?_
  by_cases hz : z = 0
  · subst hz; simp [Set.indicator, hk.ne']
  · have e : z ∈ {w : ℂ | InOK d w ∧ w ≠ 0} ↔ z ∈ (L.lattice : Set ℂ) := by simp [hz, h z]
    by_cases hL : z ∈ (L.lattice : Set ℂ)
    · rw [Set.indicator_of_mem hL, Set.indicator_of_mem (e.2 hL)]
    · rw [Set.indicator_of_notMem hL, Set.indicator_of_notMem (fun h' => hL (e.1 h'))]

open PowerSeries in
open scoped ComplexConjugate in
variable {q : ℕ} [Fact q.Prime] in
open Filter Topology in

/- English proof (translation)
Establish `hG : ∀ k, 0 < k → _root_.GlobalTheory.MomOne.eis d k = L.G (2 * k)`. Introduce `k hk`. Unfold `_root_.GlobalTheory.MomOne.eis PeriodPair.G`. Establish `e1` using `tsum_subtype {w : ℂ | _root_.GlobalTheory.MomOne.InOK d w ∧ w ≠ 0} (fun w : ℂ => 1 / w ^ (2 * k))`. Establish `e2` using `tsum_subtype (L.lattice : Set ℂ) (fun w : ℂ => (w ^ (2 * k))⁻¹)`.

Use `e1.trans (Eq.trans ?_ e2.symm)` and prove the remaining obligations. Use `congr 1`. Use extensionality with `z`. Distinguish the cases in `hz : z = 0`. Substitute `hz` using the available equality.

Establish `: (2 * k) ≠ 0` using `by omega`. Simplify using `[Set.indicator, zero_pow this]`. Establish `hz' : z ∈ (L.lattice : Set ℂ) ↔ _root_.GlobalTheory.MomOne.InOK d z` using `h z`. Distinguish the cases in `hm : _root_.GlobalTheory.MomOne.InOK d z`. Simplify using `[Set.indicator, hz, hm, hz'.2 hm]`.

Simplify using `[Set.indicator, hm, mt hz'.1 hm]`. Establish `hdisc : _root_.GlobalTheory.MomOne.discr d = L.g₂ ^ 3 - 27 * L.g₃ ^ 2`. Unfold `_root_.GlobalTheory.MomOne.discr PeriodPair.g₂ PeriodPair.g₃`. Rewrite using `[hG 2 (by norm_num), hG 3 (by norm_num)]`. Use `⟨hdisc, ?_⟩` and prove the remaining obligations.

Rewrite using `[hdisc, ← _root_.GlobalTheory.latticeCurve_Δ]`. Conclude with `_root_.GlobalTheory.latticeCurve_Δ_ne_zero L`.
-/
theorem _root_.GlobalTheory.MomOne.Basic.discr_eq {d : ℕ} {L : PeriodPair}
    (h : _root_.GlobalTheory.MomOne.IsOK d L) :
    _root_.GlobalTheory.MomOne.discr d = L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ∧
      _root_.GlobalTheory.MomOne.discr d ≠ 0 := by
  have hG : ∀ k, 0 < k → _root_.GlobalTheory.MomOne.eis d k = L.G (2 * k) := by
    intro k hk
    unfold _root_.GlobalTheory.MomOne.eis PeriodPair.G
    have e1 := tsum_subtype {w : ℂ | _root_.GlobalTheory.MomOne.InOK d w ∧ w ≠ 0}
      (fun w : ℂ => 1 / w ^ (2 * k))
    have e2 := tsum_subtype (L.lattice : Set ℂ) (fun w : ℂ => (w ^ (2 * k))⁻¹)
    refine e1.trans (Eq.trans ?_ e2.symm)
    congr 1
    ext z
    by_cases hz : z = 0
    · subst hz
      have : (2 * k) ≠ 0 := by omega
      simp [Set.indicator, zero_pow this]
    · have hz' : z ∈ (L.lattice : Set ℂ) ↔ _root_.GlobalTheory.MomOne.InOK d z := h z
      by_cases hm : _root_.GlobalTheory.MomOne.InOK d z
      · simp [Set.indicator, hz, hm, hz'.2 hm]
      · simp [Set.indicator, hm, mt hz'.1 hm]
  have hdisc : _root_.GlobalTheory.MomOne.discr d = L.g₂ ^ 3 - 27 * L.g₃ ^ 2 := by
    unfold _root_.GlobalTheory.MomOne.discr PeriodPair.g₂ PeriodPair.g₃
    rw [hG 2 (by norm_num), hG 3 (by norm_num)]
  refine ⟨hdisc, ?_⟩
  rw [hdisc, ← _root_.GlobalTheory.latticeCurve_Δ]
  exact _root_.GlobalTheory.latticeCurve_Δ_ne_zero L

def okPair (d : ℕ) (hd : 0 < d) : PeriodPair := ⟨1, wK d, LinearIndependent.pair_iff.2 fun s t h => by
  have hs : Real.sqrt d ≠ 0 := by positivity
  have h2 := congrArg Complex.im h
  have h1 := congrArg Complex.re h
  simp [wK, hs] at h1 h2
  subst h2
  exact ⟨by simpa using h1, rfl⟩⟩

open PowerSeries in
open scoped ComplexConjugate in
variable {q : ℕ} [Fact q.Prime] in
open Filter Topology in

/- English proof (translation)
Introduce `z`. Rewrite using `[PeriodPair.mem_lattice]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, n, rfl⟩`. Conclude with `⟨m, n, by simp [_root_.GlobalTheory.MomOne.Basic.okPair]⟩`.

Introduce and unpack `⟨u, v, rfl⟩`. Conclude with `⟨u, v, by simp [_root_.GlobalTheory.MomOne.Basic.okPair]⟩`.
-/
theorem _root_.GlobalTheory.MomOne.Basic.isOK_okPair (d : ℕ) (hd : 0 < d) :
    _root_.GlobalTheory.MomOne.IsOK d (_root_.GlobalTheory.MomOne.Basic.okPair d hd) := by
  intro z
  rw [PeriodPair.mem_lattice]
  constructor
  · rintro ⟨m, n, rfl⟩
    exact ⟨m, n, by simp [_root_.GlobalTheory.MomOne.Basic.okPair]⟩
  · rintro ⟨u, v, rfl⟩
    exact ⟨u, v, by simp [_root_.GlobalTheory.MomOne.Basic.okPair]⟩

open Cardinal in

/- English proof (translation)
Establish `h : ∀ x : X, ∃ s : ℕ → A, Filter.Tendsto (fun n => f (s n)) Filter.atTop (nhds x)` using `fun x => by`. Take `⟨u, hu, hx⟩` from `mem_closure_iff_seq_limit.1 (hf x)`. Use `choose s hs using hu`. Conclude with `⟨s, by simpa only [hs] using hx⟩`. Use `choose s hs using h`.

Establish `hinj : Function.Injective s` using `fun x y hxy => tendsto_nhds_unique (hs x) (by rw [hxy]; exact hs y)`. Use `(Cardinal.mk_le_of_injective hinj).trans ?_` and prove the remaining obligations. Rewrite using `[← Cardinal.power_def, Cardinal.mk_nat]`. Conclude with `(Cardinal.power_le_power_right hA).trans_eq Cardinal.continuum_power_aleph0`.
-/
theorem mk_le_of_denseRange {A X : Type} [MetricSpace X] (f : A → X) (hf : DenseRange f) (hA : #A ≤ 𝔠) :
    #X ≤ 𝔠 := by
  have h : ∀ x : X, ∃ s : ℕ → A, Filter.Tendsto (fun n => f (s n)) Filter.atTop (nhds x) := fun x => by
    obtain ⟨u, hu, hx⟩ := mem_closure_iff_seq_limit.1 (hf x)
    choose s hs using hu
    exact ⟨s, by simpa only [hs] using hx⟩
  choose s hs using h
  have hinj : Function.Injective s := fun x y hxy =>
    tendsto_nhds_unique (hs x) (by rw [hxy]; exact hs y)
  refine (Cardinal.mk_le_of_injective hinj).trans ?_
  rw [← Cardinal.power_def, Cardinal.mk_nat]
  exact (Cardinal.power_le_power_right hA).trans_eq Cardinal.continuum_power_aleph0

open PowerSeries in
open scoped ComplexConjugate in
variable {q : ℕ} [Fact q.Prime] in
open Filter Topology in
open Cardinal in
/- English proof (translation)
Establish `h : ∀ x : X, ∃ u : ℕ → Y, Tendsto (i ∘ u) atTop (𝓝 x)`. Introduce `x`. Establish `hx : x ∈ closure (Set.range i)` using `by rw [hi.closure_range]; trivial`. Take `⟨v, hv, hlim⟩` from `mem_closure_iff_seq_limit.1 hx`. Use `choose u hu using hv`.

Use `⟨u, ?_⟩` and prove the remaining obligations. Establish `: i ∘ u = v` using `funext fun n => hu n`. Rewrite using `[this]`. Conclude with `hlim`. Use `choose u hu using h`.

Use `Cardinal.mk_le_of_injective (f := u) fun x y hxy => ?_` and prove the remaining obligations. Use `hu y` as an intermediate fact. Rewrite `this` using `[← hxy]`. Conclude with `tendsto_nhds_unique (hu x) this`.
-/
private theorem cardinal_le_seq_of_denseRange {X Y : Type} [TopologicalSpace X]
    [FrechetUrysohnSpace X] [T2Space X] (i : Y → X) (hi : DenseRange i) : #X ≤ #(ℕ → Y) := by
  have h : ∀ x : X, ∃ u : ℕ → Y, Tendsto (i ∘ u) atTop (𝓝 x) := by
    intro x
    have hx : x ∈ closure (Set.range i) := by rw [hi.closure_range]; trivial
    obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.1 hx
    choose u hu using hv
    refine ⟨u, ?_⟩
    have : i ∘ u = v := funext fun n => hu n
    rw [this]; exact hlim
  choose u hu using h
  refine Cardinal.mk_le_of_injective (f := u) fun x y hxy => ?_
  have := hu y
  rw [← hxy] at this
  exact tendsto_nhds_unique (hu x) this

open PowerSeries in
open scoped ComplexConjugate in
variable {q : ℕ} [Fact q.Prime] in
open Filter Topology in
open Cardinal in
/- English proof (translation)
Establish `hQ : #ℚ_[q] ≤ 𝔠`. Combine the equalities or inequalities in the displayed calculation. Establish `hA : #(PadicAlgCl q) ≤ 𝔠` using `(Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[q] (PadicAlgCl q)).trans (max_le hQ aleph0_le_continuum)`. Apply `le_antisymm` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.

Take `⟨f, -, -, hf⟩` from `Perfect.exists_nat_bool_injection (PerfectSpace.univ_perfect (α := ℚ_[q])) ⟨0, trivial⟩`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem cardinal_padicComplex_eq_continuum (q : ℕ) [Fact q.Prime] : #ℂ_[q] = 𝔠 := by
  have hQ : #ℚ_[q] ≤ 𝔠 := by
    calc #ℚ_[q] ≤ #(ℕ → ℚ) := cardinal_le_seq_of_denseRange _ (Padic.denseRange_ratCast q)
      _ = 𝔠 := by rw [← power_def, Cardinal.mk_eq_aleph0 ℚ, Cardinal.mk_nat, aleph0_power_aleph0]
  have hA : #(PadicAlgCl q) ≤ 𝔠 :=
    (Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[q] (PadicAlgCl q)).trans
      (max_le hQ aleph0_le_continuum)
  apply le_antisymm
  · calc #ℂ_[q] ≤ #(ℕ → PadicAlgCl q) :=
          cardinal_le_seq_of_denseRange _ UniformSpace.Completion.denseRange_coe
      _ = #(PadicAlgCl q) ^ ℵ₀ := by rw [← power_def, Cardinal.mk_nat]
      _ ≤ 𝔠 ^ ℵ₀ := power_le_power_right hA
      _ = 𝔠 := continuum_power_aleph0
  · obtain ⟨f, -, -, hf⟩ := Perfect.exists_nat_bool_injection
      (PerfectSpace.univ_perfect (α := ℚ_[q])) ⟨0, trivial⟩
    calc 𝔠 = #(ℕ → Bool) := by rw [← power_def, mk_bool, Cardinal.mk_nat, two_power_aleph0]
      _ ≤ #ℚ_[q] := mk_le_of_injective hf
      _ ≤ #ℂ_[q] := mk_le_of_injective (algebraMap ℚ_[q] ℂ_[q]).injective

open PowerSeries in
open scoped ComplexConjugate in
variable {q : ℕ} [Fact q.Prime] in
open Filter Topology in
open Cardinal in

/- English proof (translation)
Use `IsAlgClosed.ringEquiv_of_equiv_of_charZero ?_ ?_` and prove the remaining obligations. Rewrite using `[Cardinal.mk_complex]`. Conclude with `aleph0_lt_continuum`. Conclude with `Cardinal.eq.1 (by rw [Cardinal.mk_complex, cardinal_padicComplex_eq_continuum])`.
-/
theorem _root_.GlobalTheory.MomOne.Basic.nonempty_iso (q : ℕ) [Fact q.Prime] :
    Nonempty (ℂ ≃+* ℂ_[q]) := by
  refine IsAlgClosed.ringEquiv_of_equiv_of_charZero ?_ ?_
  · rw [Cardinal.mk_complex]; exact aleph0_lt_continuum
  · exact Cardinal.eq.1 (by rw [Cardinal.mk_complex, cardinal_padicComplex_eq_continuum])

/- English proof (translation)
Establish `hne : W.Δ ≠ 0` using `by intro h; simp [h] at hΔ`. Use `haveI : W.IsElliptic := ⟨hne.isUnit⟩`. Take `⟨L, C, hC⟩` from `exists_variableChange_eq_latticeCurve (W.map (ι.symm : ℂ_[q] →+* ℂ))`. Establish `e4` using `congrArg WeierstrassCurve.c₄ hC`. Establish `e6` using `congrArg WeierstrassCurve.c₆ hC`.

Rewrite `e4` using `[WeierstrassCurve.variableChange_c₄, WeierstrassCurve.map_c₄, latticeCurve_c₄]`. Establish `l6 : (latticeCurve L).c₆ = 216 * L.g₃`. Simplify using `only [latticeCurve, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `e6` using `[WeierstrassCurve.variableChange_c₆, WeierstrassCurve.map_c₆, l6]`.

Establish `hu : ((C.u⁻¹ : ℂˣ) : ℂ) ≠ 0` using `Units.ne_zero _`. Use `⟨L, ((C.u⁻¹ : ℂˣ) : ℂ), hu, h1, h2, h3, h4, h6, hΔ, ?_, ?_⟩` and prove the remaining obligations. Establish `: L.g₂ / ((C.u⁻¹ : ℂˣ) : ℂ) ^ 4 = ι.symm W.c₄ / 12`. Establish `e : (ι.symm : ℂ_[q] →+* ℂ) W.c₄ = ι.symm W.c₄` using `rfl`. Rewrite `e4` using `[e]`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `-e4`. Use `show W.c₄ / 12 = ι _`. Rewrite using `[this, map_div₀, RingEquiv.apply_symm_apply, map_ofNat]`. Establish `: L.g₃ / ((C.u⁻¹ : ℂˣ) : ℂ) ^ 6 = ι.symm W.c₆ / 216`.

Establish `e : (ι.symm : ℂ_[q] →+* ℂ) W.c₆ = ι.symm W.c₆` using `rfl`. Rewrite `e6` using `[e]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `-e6`. Use `show W.c₆ / 216 = ι _`.

Rewrite using `[this, map_div₀, RingEquiv.apply_symm_apply, map_ofNat]`.
-/
theorem exists_ok_of (ι : ℂ ≃+* ℂ_[q]) (W : WeierstrassCurve ℂ_[q]) (h1 : ‖W.a₁‖ ≤ 1) (h2 : ‖W.a₂‖ ≤ 1)
    (h3 : ‖W.a₃‖ ≤ 1) (h4 : ‖W.a₄‖ ≤ 1) (h6 : ‖W.a₆‖ ≤ 1) (hΔ : ‖W.Δ‖ = 1) :
    ∃ (L : PeriodPair) (c : ℂ), Mdl.Ok ⟨ι, L, c, W⟩ := by
  have hne : W.Δ ≠ 0 := by intro h; simp [h] at hΔ
  haveI : W.IsElliptic := ⟨hne.isUnit⟩
  obtain ⟨L, C, hC⟩ := exists_variableChange_eq_latticeCurve (W.map (ι.symm : ℂ_[q] →+* ℂ))
  have e4 := congrArg WeierstrassCurve.c₄ hC
  have e6 := congrArg WeierstrassCurve.c₆ hC
  rw [WeierstrassCurve.variableChange_c₄, WeierstrassCurve.map_c₄, latticeCurve_c₄] at e4
  have l6 : (latticeCurve L).c₆ = 216 * L.g₃ := by
    simp only [latticeCurve, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    ring
  rw [WeierstrassCurve.variableChange_c₆, WeierstrassCurve.map_c₆, l6] at e6
  have hu : ((C.u⁻¹ : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  refine ⟨L, ((C.u⁻¹ : ℂˣ) : ℂ), hu, h1, h2, h3, h4, h6, hΔ, ?_, ?_⟩
  · have : L.g₂ / ((C.u⁻¹ : ℂˣ) : ℂ) ^ 4 = ι.symm W.c₄ / 12 := by
      have e : (ι.symm : ℂ_[q] →+* ℂ) W.c₄ = ι.symm W.c₄ := rfl
      rw [e] at e4
      field_simp
      linear_combination -e4
    show W.c₄ / 12 = ι _
    rw [this, map_div₀, RingEquiv.apply_symm_apply, map_ofNat]
  · have : L.g₃ / ((C.u⁻¹ : ℂˣ) : ℂ) ^ 6 = ι.symm W.c₆ / 216 := by
      have e : (ι.symm : ℂ_[q] →+* ℂ) W.c₆ = ι.symm W.c₆ := rfl
      rw [e] at e6
      field_simp
      linear_combination -e6
    show W.c₆ / 216 = ι _
    rw [this, map_div₀, RingEquiv.apply_symm_apply, map_ofNat]

open PowerSeries in
open scoped ComplexConjugate in
variable {q : ℕ} [Fact q.Prime] in
open Filter Topology in

/- English proof (translation)
Establish `h1 : (m : ℂ_[q]) = (((m : ℚ_[q]) : PadicAlgCl q) : ℂ_[q])` using `by simp`. Rewrite using `[h1, PadicComplex.norm_extends, PadicAlgCl.norm_extends, Padic.norm_natCast_eq_one_iff]`. Conclude with `h`.
-/
theorem _root_.GlobalTheory.MomOne.Basic.norm_nat_eq_one {m : ℕ} (h : Nat.Coprime q m) :
    ‖(m : ℂ_[q])‖ = 1 := by
  have h1 : (m : ℂ_[q]) = (((m : ℚ_[q]) : PadicAlgCl q) : ℂ_[q]) := by simp
  rw [h1, PadicComplex.norm_extends, PadicAlgCl.norm_extends, Padic.norm_natCast_eq_one_iff]
  exact h

/- English proof (translation)
Take `⟨ι⟩` from `nonempty_iso q`. Establish `hq : q.Prime` using `Fact.out`. Distinguish the cases in `h : q = 37`. Take `⟨L, c, H⟩` from `exists_ok_of ι ⟨0, -1, 1, 0, 0⟩ (by simp) (by simp) (by simp) (by simp) (by simp) (by`. Establish `: (⟨0, -1, 1, 0, 0⟩ : WeierstrassCurve ℂ_[q]).Δ = -((11 : ℕ) : ℂ_[q])`.

Simplify using `only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]`. Evaluate the numerical expressions. Rewrite using `[this, norm_neg]; exact norm_nat_eq_one (by subst h; norm_num))`. Conclude with `⟨_, H⟩`. Take `⟨L, c, H⟩` from `exists_ok_of ι ⟨0, 0, 1, -1, 0⟩ (by simp) (by simp) (by simp) (by simp) (by simp) (by`.

Establish `: (⟨0, 0, 1, -1, 0⟩ : WeierstrassCurve ℂ_[q]).Δ = ((37 : ℕ) : ℂ_[q])`. Simplify using `only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]`. Evaluate the numerical expressions. Rewrite using `[this]; exact norm_nat_eq_one ((Nat.coprime_primes hq (by norm_num)).2 h))`. Conclude with `⟨_, H⟩`.
-/
theorem exists_ok (q : ℕ) [Fact q.Prime] : ∃ M : Mdl q, M.Ok := by
  obtain ⟨ι⟩ := nonempty_iso q
  have hq : q.Prime := Fact.out
  by_cases h : q = 37
  · obtain ⟨L, c, H⟩ := exists_ok_of ι ⟨0, -1, 1, 0, 0⟩ (by simp) (by simp) (by simp) (by simp) (by simp) (by
      have : (⟨0, -1, 1, 0, 0⟩ : WeierstrassCurve ℂ_[q]).Δ = -((11 : ℕ) : ℂ_[q]) := by
        simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
        norm_num
      rw [this, norm_neg]; exact norm_nat_eq_one (by subst h; norm_num))
    exact ⟨_, H⟩
  · obtain ⟨L, c, H⟩ := exists_ok_of ι ⟨0, 0, 1, -1, 0⟩ (by simp) (by simp) (by simp) (by simp) (by simp) (by
      have : (⟨0, 0, 1, -1, 0⟩ : WeierstrassCurve ℂ_[q]).Δ = ((37 : ℕ) : ℂ_[q]) := by
        simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
        norm_num
      rw [this]; exact norm_nat_eq_one ((Nat.coprime_primes hq (by norm_num)).2 h))
    exact ⟨_, H⟩

/- English proof (translation)
Establish `ha` using `M.L.analyticAt_weierstrassPExcept 0`. Establish `hb` using `M.L.analyticAt_derivWeierstrassPExcept 0`. Use `set β := M.ι.symm (M.W.b₂ / 12)`. Use `set a1 := M.ι.symm M.W.a₁`. Use `set a3 := M.ι.symm M.W.a₃`.

Take `⟨A, hAd⟩ : ∃ A : ℂ → ℂ, A = fun z => (1 + z ^ 2 * M.L.weierstrassPExcept 0 z) / M.c ^ 2 - β * z ^ 2` from `⟨_, rfl⟩`. Establish `hA : AnalyticAt ℂ A 0` using `by rw [hAd]; fun_prop`. Take `⟨B, hBd⟩ : ∃ B : ℂ → ℂ, B = fun z => ((z ^ 3 * M.L.derivWeierstrassPExcept 0 z - 2) / M.c ^ 3 - a1 * z * A z - a3 * z ^ 3) / 2` from `⟨_, rfl⟩`. Establish `hB : AnalyticAt ℂ B 0` using `by rw [hBd]; fun_prop`. Establish `hA0 : A 0 = 1 / M.c ^ 2` using `by simp [hAd]`.

Establish `hB0 : B 0 = -1 / M.c ^ 3` using `by simp [hBd]; ring`. Establish `hB0' : B 0 ≠ 0` using `by rw [hB0]; exact div_ne_zero (by norm_num) (pow_ne_zero _ hc)`. Establish `hx : ∀ z : ℂ, z ≠ 0 → M.x z = A z / z ^ 2`. Introduce `z hz`. Establish `h` using `M.L.weierstrassPExcept_add 0 z`.

Simplify using `only [ZeroMemClass.coe_zero, sub_zero] at h`. Rewrite using `[Mdl.x, ← h, hAd]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hy : ∀ z : ℂ, z ≠ 0 → M.y z = B z / z ^ 3`.

Introduce `z hz`. Establish `h` using `M.L.derivWeierstrassPExcept_sub 0 z`. Simplify using `only [ZeroMemClass.coe_zero, sub_zero] at h`. Rewrite using `[Mdl.y, ← h, hBd, hx z hz]`. Simplify using `only [a1, a3]`.

Clear the denominators using the available nonvanishing facts. Establish `hQ : AnalyticAt ℂ (fun z => -A z / B z) 0` using `hA.neg.div hB hB0'`. Establish `h` using `(hasDerivAt_id (0 : ℂ)).mul hQ.differentiableAt.hasDerivAt`. Establish `e : -A 0 / B 0 = M.c` using `by rw [hA0, hB0]; field_simp`. Simplify using `only [id, zero_mul, add_zero, one_mul, e] at h`.

Use `h.congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [hB.continuousAt.eventually_ne hB0', M.L.compl_lattice_sdiff_singleton_mem_nhds 0] with z h2 h3`. Distinguish the cases in `hz : z = 0`. Substitute `hz` using the available equality. Simplify using `[Mdl.u]`.

Establish `: z ∉ M.L.lattice` using `fun h => h3 ⟨h, hz⟩`. Simplify using `only [Mdl.u, if_neg this, hx z hz, hy z hz, Pi.mul_apply, id]`. Clear the denominators using the available nonvanishing facts.
-/
theorem hasDerivAt_u (M : Mdl q) (hc : M.c ≠ 0) : HasDerivAt M.u M.c 0 := by
  have ha := M.L.analyticAt_weierstrassPExcept 0
  have hb := M.L.analyticAt_derivWeierstrassPExcept 0
  set β := M.ι.symm (M.W.b₂ / 12)
  set a1 := M.ι.symm M.W.a₁
  set a3 := M.ι.symm M.W.a₃
  obtain ⟨A, hAd⟩ : ∃ A : ℂ → ℂ, A = fun z => (1 + z ^ 2 * M.L.weierstrassPExcept 0 z) / M.c ^ 2 - β * z ^ 2 := ⟨_, rfl⟩
  have hA : AnalyticAt ℂ A 0 := by rw [hAd]; fun_prop
  obtain ⟨B, hBd⟩ : ∃ B : ℂ → ℂ, B = fun z =>
      ((z ^ 3 * M.L.derivWeierstrassPExcept 0 z - 2) / M.c ^ 3 - a1 * z * A z - a3 * z ^ 3) / 2 := ⟨_, rfl⟩
  have hB : AnalyticAt ℂ B 0 := by rw [hBd]; fun_prop
  have hA0 : A 0 = 1 / M.c ^ 2 := by simp [hAd]
  have hB0 : B 0 = -1 / M.c ^ 3 := by simp [hBd]; ring
  have hB0' : B 0 ≠ 0 := by rw [hB0]; exact div_ne_zero (by norm_num) (pow_ne_zero _ hc)
  have hx : ∀ z : ℂ, z ≠ 0 → M.x z = A z / z ^ 2 := by
    intro z hz
    have h := M.L.weierstrassPExcept_add 0 z
    simp only [ZeroMemClass.coe_zero, sub_zero] at h
    rw [Mdl.x, ← h, hAd]
    field_simp
    ring
  have hy : ∀ z : ℂ, z ≠ 0 → M.y z = B z / z ^ 3 := by
    intro z hz
    have h := M.L.derivWeierstrassPExcept_sub 0 z
    simp only [ZeroMemClass.coe_zero, sub_zero] at h
    rw [Mdl.y, ← h, hBd, hx z hz]
    simp only [a1, a3]
    field_simp
  have hQ : AnalyticAt ℂ (fun z => -A z / B z) 0 := hA.neg.div hB hB0'
  have h := (hasDerivAt_id (0 : ℂ)).mul hQ.differentiableAt.hasDerivAt
  have e : -A 0 / B 0 = M.c := by rw [hA0, hB0]; field_simp
  simp only [id, zero_mul, add_zero, one_mul, e] at h
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [hB.continuousAt.eventually_ne hB0', M.L.compl_lattice_sdiff_singleton_mem_nhds 0] with z h2 h3
  by_cases hz : z = 0
  · subst hz; simp [Mdl.u]
  · have : z ∉ M.L.lattice := fun h => h3 ⟨h, hz⟩
    simp only [Mdl.u, if_neg this, hx z hz, hy z hz, Pi.mul_apply, id]
    field_simp

/- English proof (translation)
Use `set P := PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u) with hP`. Establish `h0 : constantCoeff P = 0`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, hP, coeff_map, tay, coeff_mk]`. Simplify using `[Mdl.u]`. Establish `h1 : IsUnit (coeff 1 P)`.

Rewrite using `[hP, coeff_map, tay, coeff_mk]`. Simplify using `[(hasDerivAt_u M h.1).deriv, h.1]`. Establish `e : hat M.ι (P.substInvOfIsUnit h1) M.u = X` using `subst_substInvOfIsUnit_right P h0 h1`. Use `⟨P.substInvOfIsUnit h1, ⟨h, constantCoeff_substInvOfIsUnit _ _, ?_, ?_⟩, e⟩` and prove the remaining obligations. Apply the tactic sequence `intro n; rw [e, coeff_X]; split_ifs <;> simp`.

Rewrite using `[e]`. Simplify using the standard rewrite rules.
-/
theorem exists_chart (M : Mdl q) (h : M.Ok) : ∃ ℓ, M.Chart ℓ ∧ hat M.ι ℓ M.u = X := by
  set P := PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u) with hP
  have h0 : constantCoeff P = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, hP, coeff_map, tay, coeff_mk]
    simp [Mdl.u]
  have h1 : IsUnit (coeff 1 P) := by
    rw [hP, coeff_map, tay, coeff_mk]
    simp [(hasDerivAt_u M h.1).deriv, h.1]
  have e : hat M.ι (P.substInvOfIsUnit h1) M.u = X := subst_substInvOfIsUnit_right P h0 h1
  refine ⟨P.substInvOfIsUnit h1, ⟨h, constantCoeff_substInvOfIsUnit _ _, ?_, ?_⟩, e⟩
  · intro n; rw [e, coeff_X]; split_ifs <;> simp
  · rw [e]; simp

/- English proof (translation)
Take `⟨M, hM⟩` from `exists_ok q`. Take `⟨ℓ, h, -⟩` from `exists_chart M hM`. Conclude with `⟨M, ℓ, h⟩`.
-/
theorem exists_model_chart (q : ℕ) [Fact q.Prime] : ∃ (M : Mdl q) (ℓ : ℂ_[q]⟦X⟧), M.Chart ℓ := by
  obtain ⟨M, hM⟩ := exists_ok q
  obtain ⟨ℓ, h, -⟩ := exists_chart M hM
  exact ⟨M, ℓ, h⟩

open PowerSeries in
open scoped ComplexConjugate in
variable {q : ℕ} [Fact q.Prime] in
open Filter Topology in

/- English proof (translation)
Take `⟨v, ⟨u, w, rfl⟩, -, rfl⟩` from `h`. Establish `hq : 0 < q` using `(Fact.out : q.Prime).pos`. Establish `hs : Real.sqrt d ≠ 0` using `by positivity`. Establish `hd2 : Real.sqrt d ^ 2 = d` using `Real.sq_sqrt (by positivity)`. Establish `him : ((q : ℂ) ^ n).im = 0`.

Rewrite using `[← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.ofReal_im]`. Establish `hre : ((q : ℂ) ^ n).re = (q : ℝ) ^ n`. Rewrite using `[← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.ofReal_re]`. Establish `hIm : (_root_.GlobalTheory.MomOne.h1 d 1 ((s : ℂ) * ((u : ℂ) + (w : ℂ) * _root_.GlobalTheory.MomOne.wK d) / (q : ℂ) ^ n)).im = -((s : ℝ) * w) / (q : ℝ) ^ n`. Simplify using `[_root_.GlobalTheory.MomOne.h1, _root_.GlobalTheory.MomOne.wK, Complex.div_im, Complex.div_re, Complex.mul_im, Complex.mul_re, him, hre]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[hd2]`. Expand and normalize the polynomial expressions, which then agree. Establish `key : _root_.GlobalTheory.MomOne.kap1 d 1 ((s : ℂ) * ((u : ℂ) + (w : ℂ) * _root_.GlobalTheory.MomOne.wK d) / (q : ℂ) ^ n) ^ (q ^ n) = 1`. Unfold `_root_.GlobalTheory.MomOne.kap1`.

Rewrite using `[← Complex.exp_nat_mul, hIm]`. Establish `hqn : ((q : ℂ) ^ n) ≠ 0` using `pow_ne_zero _ (by exact_mod_cast hq.ne')`. Establish `: ((q ^ n : ℕ) : ℂ) * (-(2 * (Real.pi : ℂ) * Complex.I) * ((-((s : ℝ) * w) / (q : ℝ) ^ n : ℝ) : ℂ)) = ((s * w : ℤ) : ℂ) * (2 * Real.pi * Complex.I)`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[this, Complex.exp_int_mul_two_pi_mul_I]`. Rewrite using `[← map_pow, key, map_one]`.
-/
theorem _root_.GlobalTheory.MomOne.Basic.cmLatticeCommutatorPairing_pow_eq_one_of_good_lift (ι : ℂ ≃+* ℂ_[q]) {d n s : ℕ}
    (hd : 0 < d) {y : ℂ} (h : _root_.GlobalTheory.MomOne.Good ι d n s y) :
    ι (_root_.GlobalTheory.MomOne.kap1 d 1 y) ^ (q ^ n) = 1 := by
  obtain ⟨v, ⟨u, w, rfl⟩, -, rfl⟩ := h
  have hq : 0 < q := (Fact.out : q.Prime).pos
  have hs : Real.sqrt d ≠ 0 := by positivity
  have hd2 : Real.sqrt d ^ 2 = d := Real.sq_sqrt (by positivity)
  have him : ((q : ℂ) ^ n).im = 0 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.ofReal_im]
  have hre : ((q : ℂ) ^ n).re = (q : ℝ) ^ n := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.ofReal_re]
  have hIm : (_root_.GlobalTheory.MomOne.h1 d 1 ((s : ℂ) * ((u : ℂ) + (w : ℂ) *
      _root_.GlobalTheory.MomOne.wK d) / (q : ℂ) ^ n)).im = -((s : ℝ) * w) / (q : ℝ) ^ n := by
    simp [_root_.GlobalTheory.MomOne.h1, _root_.GlobalTheory.MomOne.wK, Complex.div_im,
      Complex.div_re, Complex.mul_im, Complex.mul_re, him, hre]
    field_simp
    rw [hd2]
    ring
  have key : _root_.GlobalTheory.MomOne.kap1 d 1 ((s : ℂ) * ((u : ℂ) + (w : ℂ) *
      _root_.GlobalTheory.MomOne.wK d) / (q : ℂ) ^ n) ^ (q ^ n) = 1 := by
    unfold _root_.GlobalTheory.MomOne.kap1
    rw [← Complex.exp_nat_mul, hIm]
    have hqn : ((q : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hq.ne')
    have : ((q ^ n : ℕ) : ℂ) * (-(2 * (Real.pi : ℂ) * Complex.I) *
        ((-((s : ℝ) * w) / (q : ℝ) ^ n : ℝ) : ℂ)) = ((s * w : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast
      field_simp
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  rw [← map_pow, key, map_one]

/- English proof (translation)
Establish `hsq : ((Real.sqrt (7 : ℕ) : ℝ) : ℂ) ^ 2 = 7` using `by exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg 7)`. Establish `hs : Real.sqrt (7 : ℕ) ≠ 0` using `by positivity`. Establish `hw : wK 7 * (1 - wK 7) = 2`. Rewrite using `[wK]`. Take the linear combination `(-((Real.sqrt (7 : ℕ) : ℝ) : ℂ) ^ 2 / 4) * Complex.I_sq + 1 / 4 * hsq`.

Establish `hc : conj (wK 7) = 1 - wK 7`. Simplify using `only [wK, map_add, map_mul, map_div₀, map_one, map_ofNat, Complex.conj_I, Complex.conj_ofReal]`. Expand and normalize the polynomial expressions, which then agree. Use `set a := ι (wK 7)`. Establish `ha : a * (1 - a) = 2` using `by have := congrArg ι hw; simpa [map_ofNat] using this`.

Establish `h2 : ‖(2 : ℂ_[2])‖ = 1 / 2`. Establish `: (2 : ℂ_[2]) = algebraMap ℚ_[2] ℂ_[2] ((2 : ℕ) : ℚ_[2])` using `by simp [map_ofNat]`. Rewrite using `[this, norm_algebraMap', Padic.norm_p]`. Evaluate the numerical expressions. Establish `hp : ‖a‖ * ‖1 - a‖ = 1 / 2` using `by rw [← norm_mul, ha, h2]`.

Establish `hor : ‖a‖ ≤ 1 / 2 ∨ ‖1 - a‖ ≤ 1 / 2`. Use `IsUltrametricDist.norm_add_le_max a (1 - a)` as an intermediate fact. Rewrite `this` using `[add_sub_cancel, norm_one, le_max_iff]`. Break down `this with h | h` into its components or cases. Use `right`.

Use polynomial arithmetic with `[norm_nonneg (1 - a)]`. Use `left`. Use polynomial arithmetic with `[norm_nonneg a]`. Establish `hk : ∀ (u : ℤ) (e : ℤ), (e = 1 ∨ e = -1) → kap1 7 1 (((1 : ℕ) : ℂ) * (u + e * wK 7) / ((2 : ℕ) : ℂ) ^ 1) = -1`. Introduce `u e he`.

Establish `him : (h1 7 1 (((1 : ℕ) : ℂ) * (u + e * wK 7) / ((2 : ℕ) : ℂ) ^ 1)).im = -e / 2`. Rewrite using `[h1, Complex.im_ofReal_mul, one_mul, Complex.conj_im]`. Simplify using `[wK]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[kap1, him]`.

Break down `he with rfl | rfl` into its components or cases. Rewrite using `[← Complex.exp_pi_mul_I]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← Complex.exp_neg_pi_mul_I]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hb : ((2 : ℕ) : ℝ) ^ (-(2 * (1 : ℕ) : ℤ)) = 1 / 4` using `by norm_num`.

Break down `hor with h | h` into its components or cases. Use `⟨_, ⟨_, ⟨-1, -1, rfl⟩, ?_, rfl⟩, hk _ _ (.inr rfl)⟩` and prove the remaining obligations. Establish `: conj (((-1 : ℤ) : ℂ) + (-1 : ℤ) * wK 7) = wK 7 ^ 2`. Rewrite using `[map_add, map_mul, hc, map_intCast]`. Use `push_cast`.

Take the linear combination `hw`. Rewrite using `[this, map_pow, norm_pow, hb]`. Use polynomial arithmetic with `[norm_nonneg a]`. Use `⟨_, ⟨_, ⟨-2, 1, rfl⟩, ?_, rfl⟩, hk _ _ (.inl rfl)⟩` and prove the remaining obligations. Establish `: conj (((-2 : ℤ) : ℂ) + (1 : ℤ) * wK 7) = (1 - wK 7) ^ 2`.

Rewrite using `[map_add, map_mul, hc, map_intCast, map_intCast]`. Use `push_cast`. Take the linear combination `hw`. Rewrite using `[this, map_pow, norm_pow, hb, map_sub, map_one]`. Use polynomial arithmetic with `[norm_nonneg (1 - a)]`.
-/
theorem exists_good [Fact (Nat.Prime 2)] (ι : ℂ ≃+* ℂ_[2]) : ∃ y, Good ι 7 1 1 y ∧ kap1 7 1 y = -1 := by
  have hsq : ((Real.sqrt (7 : ℕ) : ℝ) : ℂ) ^ 2 = 7 := by exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg 7)
  have hs : Real.sqrt (7 : ℕ) ≠ 0 := by positivity
  have hw : wK 7 * (1 - wK 7) = 2 := by
    rw [wK]; linear_combination (-((Real.sqrt (7 : ℕ) : ℝ) : ℂ) ^ 2 / 4) * Complex.I_sq + 1 / 4 * hsq
  have hc : conj (wK 7) = 1 - wK 7 := by
    simp only [wK, map_add, map_mul, map_div₀, map_one, map_ofNat, Complex.conj_I, Complex.conj_ofReal]; ring
  set a := ι (wK 7)
  have ha : a * (1 - a) = 2 := by have := congrArg ι hw; simpa [map_ofNat] using this
  have h2 : ‖(2 : ℂ_[2])‖ = 1 / 2 := by
    have : (2 : ℂ_[2]) = algebraMap ℚ_[2] ℂ_[2] ((2 : ℕ) : ℚ_[2]) := by simp [map_ofNat]
    rw [this, norm_algebraMap', Padic.norm_p]; norm_num
  have hp : ‖a‖ * ‖1 - a‖ = 1 / 2 := by rw [← norm_mul, ha, h2]
  have hor : ‖a‖ ≤ 1 / 2 ∨ ‖1 - a‖ ≤ 1 / 2 := by
    have := IsUltrametricDist.norm_add_le_max a (1 - a)
    rw [add_sub_cancel, norm_one, le_max_iff] at this
    rcases this with h | h
    · right; nlinarith [norm_nonneg (1 - a)]
    · left; nlinarith [norm_nonneg a]
  have hk : ∀ (u : ℤ) (e : ℤ), (e = 1 ∨ e = -1) → kap1 7 1 (((1 : ℕ) : ℂ) * (u + e * wK 7) / ((2 : ℕ) : ℂ) ^ 1) = -1 := by
    intro u e he
    have him : (h1 7 1 (((1 : ℕ) : ℂ) * (u + e * wK 7) / ((2 : ℕ) : ℂ) ^ 1)).im = -e / 2 := by
      rw [h1, Complex.im_ofReal_mul, one_mul, Complex.conj_im]
      simp [wK]
      field_simp
    rw [kap1, him]
    rcases he with rfl | rfl
    · rw [← Complex.exp_pi_mul_I]; congr 1; push_cast; ring
    · rw [← Complex.exp_neg_pi_mul_I]; congr 1; push_cast; ring
  have hb : ((2 : ℕ) : ℝ) ^ (-(2 * (1 : ℕ) : ℤ)) = 1 / 4 := by norm_num
  rcases hor with h | h
  · refine ⟨_, ⟨_, ⟨-1, -1, rfl⟩, ?_, rfl⟩, hk _ _ (.inr rfl)⟩
    have : conj (((-1 : ℤ) : ℂ) + (-1 : ℤ) * wK 7) = wK 7 ^ 2 := by
      rw [map_add, map_mul, hc, map_intCast]; push_cast; linear_combination hw
    rw [this, map_pow, norm_pow, hb]; nlinarith [norm_nonneg a]
  · refine ⟨_, ⟨_, ⟨-2, 1, rfl⟩, ?_, rfl⟩, hk _ _ (.inl rfl)⟩
    have : conj (((-2 : ℤ) : ℂ) + (1 : ℤ) * wK 7) = (1 - wK 7) ^ 2 := by
      rw [map_add, map_mul, hc, map_intCast, map_intCast]; push_cast; linear_combination hw
    rw [this, map_pow, norm_pow, hb, map_sub, map_one]; nlinarith [norm_nonneg (1 - a)]

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[shiftS, coeff_mk, tsum_eq_single 1 (fun m hm => by simp [coeff_X, hm])]`. Apply the tactic sequence `rcases n with _ | _ | n <;> simp [coeff_X, coeff_one, mul_add, Nat.choose_eq_zero_of_lt]`.
-/
theorem shiftS_X (ζ : ℂ_[q]) : shiftS ζ X = C ζ * (1 + X) - 1 := by
  ext n
  rw [shiftS, coeff_mk, tsum_eq_single 1 (fun m hm => by simp [coeff_X, hm])]
  rcases n with _ | _ | n <;> simp [coeff_X, coeff_one, mul_add, Nat.choose_eq_zero_of_lt]

open PowerSeries in
open scoped ComplexConjugate in
variable {q : ℕ} [Fact q.Prime] in
open Filter Topology in

/- English proof (translation)
Unfold `_root_.GlobalTheory.MomOne.h1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem _root_.GlobalTheory.MomOne.Basic.cmLatticeHermitianForm_mul_left (d : ℕ) (a z w : ℂ) :
    _root_.GlobalTheory.MomOne.h1 d (a * z) w = a * _root_.GlobalTheory.MomOne.h1 d z w := by
  unfold _root_.GlobalTheory.MomOne.h1; ring

/- English proof (translation)
Establish `hs : Real.sqrt d ≠ 0` using `by positivity`. Rewrite using `[h1, Complex.im_ofReal_mul, one_mul, Complex.conj_im]`. Establish `: (wK d).im = Real.sqrt d / 2` using `by simp [wK]`. Rewrite using `[this]`. Clear the denominators using the available nonvanishing facts.
-/
theorem riemannForm_im_eq_neg_one {d : ℕ} (hd : 0 < d) : (h1 d 1 (wK d)).im = -1 := by
  have hs : Real.sqrt d ≠ 0 := by positivity
  rw [h1, Complex.im_ofReal_mul, one_mul, Complex.conj_im]
  have : (wK d).im = Real.sqrt d / 2 := by simp [wK]
  rw [this]
  field_simp

/- English proof (translation)
The claim follows from `Or.inl ⟨rfl, rfl⟩`.
-/
example : Split 7 2 := Or.inl ⟨rfl, rfl⟩

/- English proof (translation)
The claim follows from `Or.inr ⟨by norm_num, by norm_num⟩`.
-/
example : Split 7 11 := Or.inr ⟨by norm_num, by norm_num⟩

/- English proof (translation)
Evaluate the numerical expressions using `[Split]`.
-/
example : ¬ Split 7 3 := by norm_num [Split]

open PowerSeries in
open scoped ComplexConjugate in
variable {q : ℕ} [Fact q.Prime] in
open Filter Topology in

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[_root_.GlobalTheory.MomOne.shiftS, coeff_mk, tsum_eq_single n]`. Simplify using the standard rewrite rules. Introduce `m hm`. Break down `lt_or_gt_of_ne hm with hlt | hgt` into its components or cases.

Simplify using `[Nat.choose_eq_zero_of_lt hlt]`. Establish `: m - n ≠ 0` using `by omega`. Simplify using `[zero_pow this]`.
-/
theorem _root_.GlobalTheory.MomOne.Basic.shiftS_one (f : ℂ_[q]⟦X⟧) :
    _root_.GlobalTheory.MomOne.shiftS 1 f = f := by
  ext n
  rw [_root_.GlobalTheory.MomOne.shiftS, coeff_mk, tsum_eq_single n]
  · simp
  · intro m hm
    rcases lt_or_gt_of_ne hm with hlt | hgt
    · simp [Nat.choose_eq_zero_of_lt hlt]
    · have : m - n ≠ 0 := by omega
      simp [zero_pow this]

end Basic

end GlobalTheory.MomOne
