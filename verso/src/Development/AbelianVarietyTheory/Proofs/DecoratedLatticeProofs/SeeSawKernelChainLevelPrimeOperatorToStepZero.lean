import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.MoveZero

variable {D : D7}

section Lin

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
  {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

def sOpLin (β : Frame p S n) (P : Pair k n) (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (ε : 𝓀[k]ˣ) :
    (GA D S → ℂ) →ₗ[ℂ] (GA D S → ℂ) where
  toFun := sOp β P q χ ε
  map_add' a b := by
    have h : formAt β P (a + b) = formAt β P a + formAt β P b := by
      funext P₁; simp [formAt, map_add]
    simp only [sOp, h, map_add, Pi.add_apply]
  map_smul' c a := by
    have h : formAt β P (c • a) = c • formAt β P a := by
      funext P₁; simp [formAt, map_smul]
    simp only [sOp, h, map_smul, Pi.smul_apply, RingHom.id_apply]

end Lin

variable {c : Comm D} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}

/- English proof (translation)
Use `⟨o.I.foldr (fun i G => (sOpLin (o.β j i) (o.Q j i) o.q (resChar (o.χ i) (o.hχ i) o.q) (ε j i)).comp G) LinearMap.id, fun f => ?_⟩` and prove the remaining obligations. Unfold `TDat.S`. Proceed by induction on `o.I with`. Consider the case `nil => rfl`. Consider the case `cons i l ih => simp only [List.foldr_cons, LinearMap.comp_apply, ih]`.

Both sides reduce to the same expression.
-/
theorem S_lin (o : TDat c k ι) (ε : ℕ → ι → 𝓀[k]ˣ) (j : ℕ) :
    ∃ L : (GA D (c.X j) → ℂ) →ₗ[ℂ] (GA D (c.X j) → ℂ), ∀ f, o.S ε j f = L f := by
  refine ⟨o.I.foldr (fun i G => (sOpLin (o.β j i) (o.Q j i) o.q (resChar (o.χ i) (o.hχ i) o.q) (ε j i)).comp G)
    LinearMap.id, fun f => ?_⟩
  unfold TDat.S
  induction o.I with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons, LinearMap.comp_apply, ih]; rfl

/- English proof (translation)
Take `⟨L, hL⟩` from `S_lin o ε j`. Rewrite using `[hL, hL, map_smul]`.
-/
theorem S_smul (o : TDat c k ι) (ε : ℕ → ι → 𝓀[k]ˣ) (j : ℕ) (a : ℂ) (f : GA D (c.X j) → ℂ) :
    o.S ε j (a • f) = a • o.S ε j f := by
  obtain ⟨L, hL⟩ := S_lin o ε j
  rw [hL, hL, map_smul]

/- English proof (translation)
Take `⟨L, hL⟩` from `S_lin o ε j`. Rewrite using `[hL, map_sum]`. Simplify using `only [hL]`.
-/
theorem S_sum (o : TDat c k ι) (ε : ℕ → ι → 𝓀[k]ˣ) (j : ℕ) {α : Type} (s : Finset α) (f : α → GA D (c.X j) → ℂ) :
    o.S ε j (∑ a ∈ s, f a) = ∑ a ∈ s, o.S ε j (f a) := by
  obtain ⟨L, hL⟩ := S_lin o ε j
  rw [hL, map_sum]; simp only [hL]

/- English proof (translation)
Use function extensionality and compare the values at `h`. Simplify using `only [KerDat.lift, liftT_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `g`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem lift_smul {S T : HSp D} (kd : KerDat S T) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (x : DefSp S) (y : DefSp T)
    (P : PolF D T.rank S.rank) (a : ℂ) (φ : GA D S → ℂ) :
    kd.lift ψ θ x y P (a • φ) = a • kd.lift ψ θ x y P φ := by
  funext h
  simp only [KerDat.lift, liftT_apply, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext g; ring

end GlobalTheory.SeeSaw.MoveZero

noncomputable section

namespace GlobalTheory.SeeSaw.MoveZero

variable {D : D7} {c : Comm D} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem col_zero (t : Tup c) (ψ : t.Col 0) : t.col 0 ψ = ψ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem col_succ (t : Tup c) (j : ℕ) (ψ : t.Col 0) : t.col (j + 1) ψ = t.K j (t.col j ψ) := rfl

/- English proof (translation)
Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => intro _ ψ hψ`. Conclude with `hψ`. Consider the case `succ j ih`.

Introduce `hj ψ hψ`. Rewrite using `[col_succ]`. Conclude with `hI.stabK j (by omega) _ (ih (by omega) ψ hψ)`.
-/
theorem col_mem (t : Tup c) (hI : t.Is) : ∀ j, j ≤ D.R.m → ∀ ψ ∈ t.Ram 0, t.col j ψ ∈ t.Ram j := by
  intro j
  induction j with
  | zero => intro _ ψ hψ; exact hψ
  | succ j ih =>
    intro hj ψ hψ
    rw [col_succ]
    exact hI.stabK j (by omega) _ (ih (by omega) ψ hψ)

/- English proof (translation)
Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => intro ψ hψ`. Conclude with `hψ`. Consider the case `succ i ih => intro ψ hψ`.

Conclude with `(hR.S₀ _ _ (ih ψ hψ)).1`.
-/
theorem iterS_mem (o : TDat c k ι) (t : Tup c) (ε : ℕ → ι → 𝓀[k]ˣ) (S₀ : (ι → 𝓀[k]ˣ) → t.Col 0 → t.Col 0)
    (hR : ReadS o t ε S₀) : ∀ i, ∀ ψ ∈ t.Ram 0, iterS S₀ ε i ψ ∈ t.Ram 0 := by
  intro i
  induction i with
  | zero => intro ψ hψ; exact hψ
  | succ i ih => intro ψ hψ; exact (hR.S₀ _ _ (ih ψ hψ)).1

/- English proof (translation)
Introduce `γ y'`. Take `⟨hc, hB⟩` from `hK j hj`. Take `⟨n, y, P, hP⟩` from `hB y'`. Establish `e1` using `hP a ha γ`. Rewrite `e1` using `[h, lift_smul, ← Finset.smul_sum, ← hP b hb γ]`.

Rewrite `e1` using `[smul_comm]`. Conclude with `smul_right_injective _ hc e1`.
-/
theorem stepK (t : Tup c) (hK : t.KBack) {j : ℕ} (hj : j < D.R.m) {a b : t.Col j} (ha : a ∈ t.Ram j) (hb : b ∈ t.Ram j)
    (x : ℂ) (h : ∀ α y, t.rd j α a y = x • t.rd j α b y) :
    ∀ γ y', t.rd (j + 1) γ (t.K j a) y' = x • t.rd (j + 1) γ (t.K j b) y' := by
  intro γ y'
  obtain ⟨hc, hB⟩ := hK j hj
  obtain ⟨n, y, P, hP⟩ := hB y'
  have e1 := hP a ha γ
  simp_rw [h, lift_smul, ← Finset.smul_sum, ← hP b hb γ] at e1
  rw [smul_comm] at e1
  exact smul_right_injective _ hc e1

/- English proof (translation)
Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`. Introduce `_ ψ hψ α y`. Rewrite using `[Finset.range_zero, Finset.prod_empty, one_smul, col_zero, col_zero]`.

Conclude with `((hR.S₀ η ψ hψ).2 α y).symm`. Consider the case `succ j ih`. Introduce `hj ψ hψ γ y'`. Establish `hj' : j < D.R.m` using `by omega`. Take `⟨hc, hB⟩` from `hK j hj'`.

Take `⟨n, y, P, hP⟩` from `hB y'`. Establish `m1` using `col_mem t hI j hj'.le ψ hψ`. Establish `m2` using `col_mem t hI j hj'.le _ (hR.S₀ η ψ hψ).1`. Establish `e1` using `hP _ m1 γ`. Establish `e2` using `hP _ m2 γ`.

Apply `smul_right_injective _ hc` to reduce the goal to its premises. Use `show t.cK j • o.S (fun _ => η) (j + 1) (t.rd (j + 1) γ (t.K j (t.col j ψ)) y') = t.cK j • ((∏ l ∈ Finset.range (j + 1), o.cL l) • t.rd (j + 1) γ (t.K j (t.col j (S₀ η ψ))) y')`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e1, S_sum]`. Simplify using `only [S_sum]`.

Use `_ = ∑ a, ∑ α, (o.cL j * ∏ l ∈ Finset.range j, o.cL l) • (t.ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P a) (t.rd j α (t.col j (S₀ η ψ)) (y a)) := by`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations. Rewrite using `[(hL j hj' α γ (P a) _ (hR.ram j hj'.le _ m1 α (y a))).2 η, ih hj'.le ψ hψ α (y a), lift_smul, smul_smul]`. Use `_ = (o.cL j * ∏ l ∈ Finset.range j, o.cL l) • (t.cK j • t.rd (j + 1) γ (t.K j (t.col j (S₀ η ψ))) y') := by`. Rewrite using `[e2]`.

Simplify using `only [Finset.smul_sum]`. Use `_ = t.cK j • ((∏ l ∈ Finset.range (j + 1), o.cL l) • t.rd (j + 1) γ (t.K j (t.col j (S₀ η ψ))) y') := by`. Rewrite using `[Finset.prod_range_succ, smul_comm, mul_comm]`.
-/
theorem stepB (o : TDat c k ι) (t : Tup c) (ε : ℕ → ι → 𝓀[k]ˣ) (S₀ : (ι → 𝓀[k]ˣ) → t.Col 0 → t.Col 0)
    (hI : t.Is) (hK : t.KBack) (hL : LiftS o t) (hR : ReadS o t ε S₀) (η : ι → 𝓀[k]ˣ) :
    ∀ j, j ≤ D.R.m → ∀ ψ ∈ t.Ram 0, ∀ α y, o.S (fun _ => η) j (t.rd j α (t.col j ψ) y) =
      (∏ l ∈ Finset.range j, o.cL l) • t.rd j α (t.col j (S₀ η ψ)) y := by
  intro j
  induction j with
  | zero =>
    intro _ ψ hψ α y
    rw [Finset.range_zero, Finset.prod_empty, one_smul, col_zero, col_zero]
    exact ((hR.S₀ η ψ hψ).2 α y).symm
  | succ j ih =>
    intro hj ψ hψ γ y'
    have hj' : j < D.R.m := by omega
    obtain ⟨hc, hB⟩ := hK j hj'
    obtain ⟨n, y, P, hP⟩ := hB y'
    have m1 := col_mem t hI j hj'.le ψ hψ
    have m2 := col_mem t hI j hj'.le _ (hR.S₀ η ψ hψ).1
    have e1 := hP _ m1 γ
    have e2 := hP _ m2 γ
    apply smul_right_injective _ hc
    show t.cK j • o.S (fun _ => η) (j + 1) (t.rd (j + 1) γ (t.K j (t.col j ψ)) y') =
      t.cK j • ((∏ l ∈ Finset.range (j + 1), o.cL l) • t.rd (j + 1) γ (t.K j (t.col j (S₀ η ψ))) y')
    calc t.cK j • o.S (fun _ => η) (j + 1) (t.rd (j + 1) γ (t.K j (t.col j ψ)) y')
        = o.S (fun _ => η) (j + 1) (t.cK j • t.rd (j + 1) γ (t.K j (t.col j ψ)) y') := by rw [S_smul]
      _ = ∑ a, ∑ α, o.S (fun _ => η) (j + 1) ((t.ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P a)
            (t.rd j α (t.col j ψ) (y a))) := by
          rw [e1, S_sum]; simp only [S_sum]
      _ = ∑ a, ∑ α, (o.cL j * ∏ l ∈ Finset.range j, o.cL l) • (t.ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P a)
            (t.rd j α (t.col j (S₀ η ψ)) (y a)) := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun α _ => ?_
          rw [(hL j hj' α γ (P a) _ (hR.ram j hj'.le _ m1 α (y a))).2 η, ih hj'.le ψ hψ α (y a), lift_smul, smul_smul]
      _ = (o.cL j * ∏ l ∈ Finset.range j, o.cL l) • (t.cK j • t.rd (j + 1) γ (t.K j (t.col j (S₀ η ψ))) y') := by
          rw [e2]; simp only [Finset.smul_sum]
      _ = t.cK j • ((∏ l ∈ Finset.range (j + 1), o.cL l) • t.rd (j + 1) γ (t.K j (t.col j (S₀ η ψ))) y') := by
          rw [Finset.prod_range_succ, smul_comm, mul_comm]

/- English proof (translation)
Introduce `i`. Proceed by induction on `i with`. Consider the case `zero`. Introduce `_ ψ hψ`. Use `⟨hψ, fun α y => ?_⟩` and prove the remaining obligations.

Simplify using `only [TDat.cS, Finset.range_zero, Finset.prod_empty, one_smul]`. Both sides reduce to the same expression. Consider the case `succ i ih`. Introduce `hi ψ hψ`. Take `⟨hu, hr⟩` from `ih (by omega) ψ hψ`.

Establish `hφ` using `iterS_mem o t ε S₀ hR i ψ hψ`. Establish `hS` using `hI.stabS (2 * i) (by omega) _ hu`. Establish `hw` using `col_mem t hI (2 * i) (by omega) _ (hR.S₀ (ε (2 * i)) _ hφ).1`. Establish `hv` using `col_mem t hI (2 * i) (by omega) _ hφ`. Establish `h0 : ∀ α y, t.rd (2 * i) α (t.S (2 * i) (t.up i ψ)) y = (o.cS i * ∏ l ∈ Finset.range (2 * i), o.cL l) • t.rd (2 * i) α (t.col (2 * i) (S₀ (ε (2 * i)) (iterS S₀ ε i ψ))) y`.

Introduce `α y`. Rewrite using `[hR.S (2 * i) (by omega) _ hu α y, hr α y, S_smul, mul_smul]`. Use `congr 1`. Conclude with `stepB o t ε S₀ hI hK hL hR (ε (2 * i)) (2 * i) (by omega) _ hφ α y`. Establish `h1` using `stepK t hK (j := 2 * i) (by omega) hS hw _ h0`.

Establish `hlt1 : 2 * i < D.R.m` using `by omega`. Establish `hlt2 : 2 * i + 1 < D.R.m` using `by omega`. Establish `h2` using `stepK t hK (j := 2 * i + 1) hlt2 (hI.stabK (2 * i) hlt1 _ hS) (hI.stabK (2 * i) hlt1 _ hw) _ h1`. Use `⟨hI.stabK (2 * i + 1) hlt2 _ (hI.stabK (2 * i) hlt1 _ hS), fun α y => ?_⟩` and prove the remaining obligations. Establish `hc : o.cS (i + 1) = o.cS i * ∏ l ∈ Finset.range (2 * i), o.cL l`.

Simplify using `only [TDat.cS, Finset.prod_range_succ]`. Rewrite using `[hc]`. Conclude with `h2 α y`.
-/
theorem stepC (o : TDat c k ι) (t : Tup c) (ε : ℕ → ι → 𝓀[k]ˣ) (S₀ : (ι → 𝓀[k]ˣ) → t.Col 0 → t.Col 0)
    (hI : t.Is) (hK : t.KBack) (hL : LiftS o t) (hR : ReadS o t ε S₀) :
    ∀ i, 2 * i ≤ D.R.m → ∀ ψ ∈ t.Ram 0, t.up i ψ ∈ t.Ram (2 * i) ∧
      ∀ α y, t.rd (2 * i) α (t.up i ψ) y = o.cS i • t.rd (2 * i) α (t.col (2 * i) (iterS S₀ ε i ψ)) y := by
  intro i
  induction i with
  | zero =>
    intro _ ψ hψ
    refine ⟨hψ, fun α y => ?_⟩
    simp only [TDat.cS, Finset.range_zero, Finset.prod_empty, one_smul]
    rfl
  | succ i ih =>
    intro hi ψ hψ
    obtain ⟨hu, hr⟩ := ih (by omega) ψ hψ
    have hφ := iterS_mem o t ε S₀ hR i ψ hψ
    have hS := hI.stabS (2 * i) (by omega) _ hu
    have hw := col_mem t hI (2 * i) (by omega) _ (hR.S₀ (ε (2 * i)) _ hφ).1
    have hv := col_mem t hI (2 * i) (by omega) _ hφ
    have h0 : ∀ α y, t.rd (2 * i) α (t.S (2 * i) (t.up i ψ)) y =
        (o.cS i * ∏ l ∈ Finset.range (2 * i), o.cL l) •
          t.rd (2 * i) α (t.col (2 * i) (S₀ (ε (2 * i)) (iterS S₀ ε i ψ))) y := by
      intro α y
      rw [hR.S (2 * i) (by omega) _ hu α y, hr α y, S_smul, mul_smul]
      congr 1
      exact stepB o t ε S₀ hI hK hL hR (ε (2 * i)) (2 * i) (by omega) _ hφ α y
    have h1 := stepK t hK (j := 2 * i) (by omega) hS hw _ h0
    have hlt1 : 2 * i < D.R.m := by omega
    have hlt2 : 2 * i + 1 < D.R.m := by omega
    have h2 := stepK t hK (j := 2 * i + 1) hlt2 (hI.stabK (2 * i) hlt1 _ hS) (hI.stabK (2 * i) hlt1 _ hw) _ h1
    refine ⟨hI.stabK (2 * i + 1) hlt2 _ (hI.stabK (2 * i) hlt1 _ hS), fun α y => ?_⟩
    have hc : o.cS (i + 1) = o.cS i * ∏ l ∈ Finset.range (2 * i), o.cL l := by
      simp only [TDat.cS, Finset.prod_range_succ]
    rw [hc]
    exact h2 α y

end GlobalTheory.SeeSaw.MoveZero

namespace GlobalTheory.SeeSaw

/- English proof (translation)
Introduce `D c k _ _ _ _ ι o t ε S₀ hI hK hT hL hR n h ψ hψ F`. Take `⟨hu, hr⟩` from `MoveZero.stepC o t ε S₀ hI hK hL hR n h.le ψ hψ`. Conclude with `hT (2 * n) h _ hu _ (MoveZero.col_mem t hI (2 * n) h.le _ (MoveZero.iterS_mem o t ε S₀ hR n ψ hψ)) _ hr F`.
-/
theorem commX_of_laws : ∀ (D : D7) (c : Comm D) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι) (t : Tup c) (ε : ℕ → ι → 𝓀[k]ˣ)
    (S₀ : (ι → 𝓀[k]ˣ) → t.Col 0 → t.Col 0),
    t.Is → t.KBack → t.TailRd → LiftS o t → ReadS o t ε S₀ → CommX o t ε S₀ := by
  intro D c k _ _ _ _ ι o t ε S₀ hI hK hT hL hR n h ψ hψ F
  obtain ⟨hu, hr⟩ := MoveZero.stepC o t ε S₀ hI hK hL hR n h.le ψ hψ
  exact hT (2 * n) h _ hu _ (MoveZero.col_mem t hI (2 * n) h.le _ (MoveZero.iterS_mem o t ε S₀ hR n ψ hψ)) _ hr F

end GlobalTheory.SeeSaw
