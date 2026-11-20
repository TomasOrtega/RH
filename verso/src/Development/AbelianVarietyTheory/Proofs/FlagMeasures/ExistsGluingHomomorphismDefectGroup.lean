import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemPerpSpan
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ComplementLatticeOfTermFreeRank
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Gluing

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} {S : Frames L r k}

/- English proof (translation)
Rewrite using `[L.O_def]`. Conclude with `isIntegral_algebraMap (R := 𝒪[F]) (x := ⟨a, ha⟩)`.
-/
theorem alg_mem (L : LocE F E) {a : F} (ha : a ∈ 𝒪[F]) : algebraMap F E a ∈ L.O := by
  rw [L.O_def]
  exact isIntegral_algebraMap (R := 𝒪[F]) (x := ⟨a, ha⟩)

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
variable [IsNonarchimedeanLocalField F] [CharZero F] in
/- English proof (translation)
Take `⟨p, -, -, -, -, -, -, -, hgr⟩` from `hT`. Take `⟨-, -, -, -, -, hth, -⟩` from `_root_.GlobalTheory.FrameBasic.main L r k S`. Establish `hθ : (algebraMap F E) S.th⁻¹ * (algebraMap F E) S.th = 1`. Rewrite using `[← map_mul, inv_mul_cancel₀ hth, map_one]`. Introduce and unpack `w ⟨-, -, -, hw⟩`.

Rewrite `hw` using `[hgr]`. Take `⟨y', hy', y, hy, -, -, hx', hx, t, ht, e⟩` from `hw`. Establish `hX : S.X ≤ S.ME`. Unfold `_root_.GlobalTheory.HL.Frames.ME _root_.GlobalTheory.HL.Frames.X`. Conclude with `le_sup_of_le_left (_root_.GlobalTheory.HL.TermBasic.spanTo_mono S S.f (Nat.le_succ r))`.

Establish `hX' : S.X' ≤ S.ME`. Unfold `_root_.GlobalTheory.HL.Frames.ME _root_.GlobalTheory.HL.Frames.X'`. Conclude with `le_sup_of_le_right (_root_.GlobalTheory.HL.TermBasic.spanTo_mono S S.f' (Nat.le_succ r))`. Establish `htt : (algebraMap F E) S.th⁻¹ • (y' - y) = t`. Rewrite using `[e, smul_smul, hθ, one_smul]`.

Use `⟨t, ?_, y - w, hx, y' - w, hx', by simpa using hy, by simpa using hy', ⟨t, ht, ?_⟩, ?_⟩` and prove the remaining obligations. Unfold `_root_.GlobalTheory.HL.Frames.sat`. Use `Submodule.mem_inf.2 ⟨ht, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.restrictScalars_mem, ← htt]`. Use `S.ME.smul_mem _ ?_` and prove the remaining obligations.

Use `S.ME.sub_mem (hX' hx') (hX hx)` as an intermediate fact. Simplify using `using this`. Simplify using `using e`. Establish `: y' - w - (y - w) = y' - y` using `by abel`. Rewrite using `[this, htt, sub_self]`.

Conclude with `Submodule.zero_mem _`.
-/
private theorem exists_tauRel_of_mem_complementLattice (d : S.Datum)
    (Λ : Submodule L.O S.V) (hT : S.IsTerm d Λ) :
    ∀ w ∈ S.complementLatticeOfDatum d, ∃ y ∈ S.sat Λ,
      S.TauRel d Λ w y := by
  obtain ⟨p, -, -, -, -, -, -, -, hgr⟩ := hT
  obtain ⟨-, -, -, -, -, hth, -⟩ := _root_.GlobalTheory.FrameBasic.main L r k S
  have hθ : (algebraMap F E) S.th⁻¹ * (algebraMap F E) S.th = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hth, map_one]
  rintro w ⟨-, -, -, hw⟩
  rw [hgr] at hw
  obtain ⟨y', hy', y, hy, -, -, hx', hx, t, ht, e⟩ := hw
  have hX : S.X ≤ S.ME := by
    unfold _root_.GlobalTheory.HL.Frames.ME _root_.GlobalTheory.HL.Frames.X
    exact le_sup_of_le_left (_root_.GlobalTheory.HL.TermBasic.spanTo_mono S S.f (Nat.le_succ r))
  have hX' : S.X' ≤ S.ME := by
    unfold _root_.GlobalTheory.HL.Frames.ME _root_.GlobalTheory.HL.Frames.X'
    exact le_sup_of_le_right (_root_.GlobalTheory.HL.TermBasic.spanTo_mono S S.f' (Nat.le_succ r))
  have htt : (algebraMap F E) S.th⁻¹ • (y' - y) = t := by
    rw [e, smul_smul, hθ, one_smul]
  refine ⟨t, ?_, y - w, hx, y' - w, hx', by simpa using hy, by simpa using hy', ⟨t, ht, ?_⟩, ?_⟩
  · unfold _root_.GlobalTheory.HL.Frames.sat
    refine Submodule.mem_inf.2 ⟨ht, ?_⟩
    rw [Submodule.restrictScalars_mem, ← htt]
    refine S.ME.smul_mem _ ?_
    have := S.ME.sub_mem (hX' hx') (hX hx)
    simpa using this
  · simpa using e
  · have : y' - w - (y - w) = y' - y := by abel
    rw [this, htt, sub_self]
    exact Submodule.zero_mem _

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
variable [IsNonarchimedeanLocalField F] [CharZero F] in
/- English proof (translation)
Take `⟨-, -, hMsat, hf, hf', -⟩` from `_root_.GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT`. Take `⟨-, -, -, -, -, hth, -⟩` from `_root_.GlobalTheory.FrameBasic.main L r k S`. Use `set θ : E := (algebraMap F E) S.th⁻¹ with hθdef`. Establish `hθ : θ * (algebraMap F E) S.th = 1`. Rewrite using `[hθdef, ← map_mul, inv_mul_cancel₀ hth, map_one]`.

Establish `hMΛ : ∀ x, x ∈ S.M d Λ → x ∈ Λ` using `fun x hx => (Submodule.mem_inf.1 (hMsat hx)).1`. Establish `hMdef : S.M d Λ = Submodule.span L.O (Set.range (S.fr d Λ) ∪ Set.range fun b => θ • (S.fr' d Λ b - S.fr d Λ b))` using `rfl`. Establish `hfr : ∀ x ∈ Submodule.span L.O (S.fr d Λ '' {i | (i : ℕ) < r}), x ∈ S.M d Λ`. Rewrite using `[hMdef]`. Use `Submodule.span_mono ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨i, -, rfl⟩`. Conclude with `Or.inl ⟨i, rfl⟩`. Establish `hclaim : ∀ x ∈ Submodule.span L.O (S.fr' d Λ '' {i | (i : ℕ) < r}), ∃ z ∈ Submodule.span L.O (S.fr d Λ '' {i | (i : ℕ) < r}), θ • (x - z) ∈ S.M d Λ`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨i, hi, rfl⟩` from `hx`. Use `⟨S.fr d Λ i, Submodule.subset_span ⟨i, hi, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hMdef]`. Conclude with `Submodule.subset_span (Or.inr ⟨i, rfl⟩)`.

Consider the case `zero => exact ⟨0, Submodule.zero_mem _, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨z, hz, hxz⟩` from `hx`. Take `⟨z', hz', hyz⟩` from `hy`. Use `⟨z + z', Submodule.add_mem _ hz hz', ?_⟩` and prove the remaining obligations.

Rewrite using `[add_sub_add_comm, smul_add]`. Conclude with `Submodule.add_mem _ hxz hyz`. Consider the case `smul c x _ hx`. Take `⟨z, hz, hxz⟩` from `hx`. Use `⟨c • z, Submodule.smul_mem _ c hz, ?_⟩` and prove the remaining obligations.

Rewrite using `[← smul_sub, smul_comm]`. Conclude with `Submodule.smul_mem _ c hxz`. Introduce `w y y' ⟨a, ha, a', ha', m, m', ⟨t, ht, et⟩, hy⟩`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, hb, b', hb', n, n', ⟨u, hu, eu⟩, hy'⟩`.

Establish `hα : a - b ∈ Submodule.span L.O (S.fr d Λ '' {i | (i : ℕ) < r})`. Use `(hf r (Nat.le_succ r) _).1 ⟨?_, S.X.sub_mem ha hb⟩` and prove the remaining obligations. Use `Λ.sub_mem m n` as an intermediate fact. Simplify using `using this`. Establish `hα' : a' - b' ∈ Submodule.span L.O (S.fr' d Λ '' {i | (i : ℕ) < r})`.

Use `(hf' r (Nat.le_succ r) _).1 ⟨?_, S.X'.sub_mem ha' hb'⟩` and prove the remaining obligations. Use `Λ.sub_mem m' n'` as an intermediate fact. Simplify using `using this`. Take `⟨z, hz, hz'⟩` from `hclaim _ hα'`. Establish `hts : θ • ((a' - a) - (b' - b)) = t - u`.

Rewrite using `[et, eu, ← smul_sub, smul_smul, hθ, one_smul]`. Establish `hβ : θ • (z - (a - b)) ∈ S.M d Λ`. Apply `hfr` to reduce the goal to its premises. Use `(hf r (Nat.le_succ r) _).1 ⟨?_, ?_⟩` and prove the remaining obligations. Establish `h1 : θ • (z - (a - b)) = (t - u) - θ • (a' - b' - z)`.

Rewrite using `[← hts, ← smul_sub]`. Use `congr 1`. Normalize the expressions using the abelian group laws. Rewrite using `[h1]`. Conclude with `Λ.sub_mem (Λ.sub_mem ht hu) (hMΛ _ hz')`.

Use `S.X.smul_mem θ (S.X.sub_mem ?_ (S.X.sub_mem ha hb))` and prove the remaining obligations. Conclude with `((hf r (Nat.le_succ r) _).2 hz).2`. Establish `h2 : y - y' = (y - θ • (a' - a)) - (y' - θ • (b' - b)) + (θ • (a' - b' - z) + θ • (z - (a - b)))`. Establish `h3 : a' - b' - z + (z - (a - b)) = (a' - a) - (b' - b)` using `by abel`. Rewrite using `[← smul_add, h3]`.

Use `module`. Rewrite using `[h2]`. Conclude with `Submodule.add_mem _ (Submodule.sub_mem _ hy hy') (Submodule.add_mem _ hz' hβ)`. Introduce `hyy`. Use `⟨a, ha, a', ha', m, m', ⟨t, ht, et⟩, ?_⟩` and prove the remaining obligations.

Establish `: y' - θ • (a' - a) = (y - θ • (a' - a)) - (y - y')` using `by abel`. Rewrite using `[this]`. Conclude with `Submodule.sub_mem _ hy hyy`.
-/
private theorem tauRel_iff_sub_mem_M (d : S.Datum)
    (Λ : Submodule L.O S.V) (hT : S.IsTerm d Λ) :
    ∀ w y y', S.TauRel d Λ w y →
      (S.TauRel d Λ w y' ↔ y - y' ∈ S.M d Λ) := by
  obtain ⟨-, -, hMsat, hf, hf', -⟩ := _root_.GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  obtain ⟨-, -, -, -, -, hth, -⟩ := _root_.GlobalTheory.FrameBasic.main L r k S
  set θ : E := (algebraMap F E) S.th⁻¹ with hθdef
  have hθ : θ * (algebraMap F E) S.th = 1 := by
    rw [hθdef, ← map_mul, inv_mul_cancel₀ hth, map_one]
  have hMΛ : ∀ x, x ∈ S.M d Λ → x ∈ Λ :=
    fun x hx => (Submodule.mem_inf.1 (hMsat hx)).1
  have hMdef : S.M d Λ = Submodule.span L.O (Set.range (S.fr d Λ) ∪
      Set.range fun b => θ • (S.fr' d Λ b - S.fr d Λ b)) := rfl
  have hfr : ∀ x ∈ Submodule.span L.O (S.fr d Λ '' {i | (i : ℕ) < r}),
      x ∈ S.M d Λ := by
    rw [hMdef]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, -, rfl⟩
    exact Or.inl ⟨i, rfl⟩
  have hclaim : ∀ x ∈ Submodule.span L.O (S.fr' d Λ '' {i | (i : ℕ) < r}),
      ∃ z ∈ Submodule.span L.O (S.fr d Λ '' {i | (i : ℕ) < r}),
        θ • (x - z) ∈ S.M d Λ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      refine ⟨S.fr d Λ i, Submodule.subset_span ⟨i, hi, rfl⟩, ?_⟩
      rw [hMdef]
      exact Submodule.subset_span (Or.inr ⟨i, rfl⟩)
    | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨z, hz, hxz⟩ := hx
      obtain ⟨z', hz', hyz⟩ := hy
      refine ⟨z + z', Submodule.add_mem _ hz hz', ?_⟩
      rw [add_sub_add_comm, smul_add]
      exact Submodule.add_mem _ hxz hyz
    | smul c x _ hx =>
      obtain ⟨z, hz, hxz⟩ := hx
      refine ⟨c • z, Submodule.smul_mem _ c hz, ?_⟩
      rw [← smul_sub, smul_comm]
      exact Submodule.smul_mem _ c hxz
  intro w y y' ⟨a, ha, a', ha', m, m', ⟨t, ht, et⟩, hy⟩
  constructor
  · rintro ⟨b, hb, b', hb', n, n', ⟨u, hu, eu⟩, hy'⟩
    have hα : a - b ∈ Submodule.span L.O (S.fr d Λ '' {i | (i : ℕ) < r}) := by
      refine (hf r (Nat.le_succ r) _).1 ⟨?_, S.X.sub_mem ha hb⟩
      have := Λ.sub_mem m n
      simpa using this
    have hα' : a' - b' ∈ Submodule.span L.O (S.fr' d Λ '' {i | (i : ℕ) < r}) := by
      refine (hf' r (Nat.le_succ r) _).1 ⟨?_, S.X'.sub_mem ha' hb'⟩
      have := Λ.sub_mem m' n'
      simpa using this
    obtain ⟨z, hz, hz'⟩ := hclaim _ hα'
    have hts : θ • ((a' - a) - (b' - b)) = t - u := by
      rw [et, eu, ← smul_sub, smul_smul, hθ, one_smul]
    have hβ : θ • (z - (a - b)) ∈ S.M d Λ := by
      apply hfr
      refine (hf r (Nat.le_succ r) _).1 ⟨?_, ?_⟩
      · have h1 : θ • (z - (a - b)) = (t - u) - θ • (a' - b' - z) := by
          rw [← hts, ← smul_sub]; congr 1; abel
        rw [h1]
        exact Λ.sub_mem (Λ.sub_mem ht hu) (hMΛ _ hz')
      · refine S.X.smul_mem θ
          (S.X.sub_mem ?_ (S.X.sub_mem ha hb))
        exact ((hf r (Nat.le_succ r) _).2 hz).2
    have h2 : y - y' = (y - θ • (a' - a)) - (y' - θ • (b' - b)) +
        (θ • (a' - b' - z) + θ • (z - (a - b))) := by
      have h3 : a' - b' - z + (z - (a - b)) = (a' - a) - (b' - b) := by abel
      rw [← smul_add, h3]
      module
    rw [h2]
    exact Submodule.add_mem _ (Submodule.sub_mem _ hy hy') (Submodule.add_mem _ hz' hβ)
  · intro hyy
    refine ⟨a, ha, a', ha', m, m', ⟨t, ht, et⟩, ?_⟩
    have : y' - θ • (a' - a) = (y - θ • (a' - a)) - (y - y') := by abel
    rw [this]
    exact Submodule.sub_mem _ hy hyy

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
variable [IsNonarchimedeanLocalField F] [CharZero F] in
/- English proof (translation)
Establish `hs : ∀ v : S.V, (⟨c, hc⟩ : L.O) • v = c • v` using `fun _ => rfl`. Take `⟨a, ha, a', ha', m, m', ⟨t, ht, et⟩, hy⟩` from `h₁`. Take `⟨b, hb, b', hb', n, n', ⟨u, hu, eu⟩, hz⟩` from `h₂`. Use `⟨c • a + b, S.X.add_mem (S.X.smul_mem c ha) hb, c • a' + b', S.X'.add_mem (S.X'.smul_mem c ha') hb', ?_, ?_, ⟨(⟨c, hc⟩ : L.O) • t + u, Λ.add_mem (Λ.smul_mem _ ht) hu, ?_⟩, ?_⟩` and prove the remaining obligations. Use `Λ.add_mem (Λ.smul_mem (⟨c, hc⟩ : L.O) m) n` as an intermediate fact.

Rewrite `this` using `[hs]`. Use `this using 1` and compare the differences between its conclusion and the goal. Use `module`. Use `Λ.add_mem (Λ.smul_mem (⟨c, hc⟩ : L.O) m') n'` as an intermediate fact. Rewrite `this` using `[hs]`.

Use `this using 1` and compare the differences between its conclusion and the goal. Use `module`. Rewrite using `[hs, smul_add, smul_comm _ c t, ← et, ← eu] module`. Use `(S.M d Λ).add_mem ((S.M d Λ).smul_mem (⟨c, hc⟩ : L.O) hy) hz` as an intermediate fact. Rewrite `this` using `[hs]`.

Use `this using 1` and compare the differences between its conclusion and the goal. Use `module`.
-/
private theorem tauRel_smul_add (d : S.Datum)
    (Λ : Submodule L.O S.V) (c : E) (hc : c ∈ L.O) (w₁ w₂ y₁ y₂ : S.V)
    (h₁ : S.TauRel d Λ w₁ y₁) (h₂ : S.TauRel d Λ w₂ y₂) :
    S.TauRel d Λ (c • w₁ + w₂) (c • y₁ + y₂) := by
  have hs : ∀ v : S.V, (⟨c, hc⟩ : L.O) • v = c • v := fun _ => rfl
  obtain ⟨a, ha, a', ha', m, m', ⟨t, ht, et⟩, hy⟩ := h₁
  obtain ⟨b, hb, b', hb', n, n', ⟨u, hu, eu⟩, hz⟩ := h₂
  refine ⟨c • a + b, S.X.add_mem (S.X.smul_mem c ha) hb,
    c • a' + b', S.X'.add_mem (S.X'.smul_mem c ha') hb',
    ?_, ?_, ⟨(⟨c, hc⟩ : L.O) • t + u, Λ.add_mem (Λ.smul_mem _ ht) hu, ?_⟩, ?_⟩
  · have := Λ.add_mem (Λ.smul_mem (⟨c, hc⟩ : L.O) m) n
    rw [hs] at this
    convert this using 1
    module
  · have := Λ.add_mem (Λ.smul_mem (⟨c, hc⟩ : L.O) m') n'
    rw [hs] at this
    convert this using 1
    module
  · rw [hs, smul_add, smul_comm _ c t, ← et, ← eu]
    module
  · have := (S.M d Λ).add_mem ((S.M d Λ).smul_mem (⟨c, hc⟩ : L.O) hy) hz
    rw [hs] at this
    convert this using 1
    module

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
variable [IsNonarchimedeanLocalField F] [CharZero F] in
/- English proof (translation)
Take `⟨⟨n, n'⟩, hA, hA', hn, hn', hΛn, hΛn', -, hgr⟩` from `hT`. Establish `hME : ∀ x ∈ S.ME, S.h w x = 0` using `hw`. Establish `hXo : w ∈ _root_.GlobalTheory.HL.perp L S.Hm S.X` using `fun x hx => hME x (le_sup_of_le_left (_root_.GlobalTheory.HL.TermBasic.spanTo_mono S S.f (Nat.le_succ r)) hx)`. Establish `hXo' : w ∈ _root_.GlobalTheory.HL.perp L S.Hm S.X'` using `fun x hx => hME x (le_sup_of_le_right (_root_.GlobalTheory.HL.TermBasic.spanTo_mono S S.f' (Nat.le_succ r)) hx)`. Use `⟨⟨hw, ?_, ?_, ?_⟩, ⟨0, Submodule.zero_mem _, 0, Submodule.zero_mem _, by simpa using hΛ, by simpa using hΛ, ⟨0, Λ.zero_mem, by simp⟩, by simpa using Submodule.zero_mem _⟩⟩` and prove the remaining obligations.

Use `((_root_.GlobalTheory.HL.StdLat.stdLat_spec L r k S S.f S.es (Or.inl ⟨rfl, rfl⟩) _ hA).2.2 w).2 ?_` and prove the remaining obligations. Use `(_root_.GlobalTheory.HL.TermBasic.inner_smul S hn w).2 ⟨w, ?_, hXo, by simpa using Submodule.zero_mem _⟩` and prove the remaining obligations. Rewrite using `[← hΛn]`. Conclude with `hΛ`. Use `((_root_.GlobalTheory.HL.StdLat.stdLat_spec L r k S S.f' S.es' (Or.inr ⟨rfl, rfl⟩) _ hA').2.2 w).2 ?_` and prove the remaining obligations.

Use `(_root_.GlobalTheory.HL.TermBasic.inner_smul S hn' w).2 ⟨w, ?_, hXo', by simpa using Submodule.zero_mem _⟩` and prove the remaining obligations. Rewrite using `[← hΛn']`. Conclude with `hΛ`. Rewrite using `[hgr]`. Conclude with `⟨w, hΛ, w, hΛ, hXo', hXo, by simpa using Submodule.zero_mem _, by simpa using Submodule.zero_mem _, 0, Λ.zero_mem, by simp⟩`.
-/
private theorem mem_complementLattice_of_mem_term (d : S.Datum)
    (Λ : Submodule L.O S.V) (hT : S.IsTerm d Λ) (w : S.V)
    (hw : w ∈ S.W0) (hΛ : w ∈ Λ) :
    w ∈ S.complementLatticeOfDatum d ∧ S.TauRel d Λ w 0 := by
  obtain ⟨⟨n, n'⟩, hA, hA', hn, hn', hΛn, hΛn', -, hgr⟩ := hT
  have hME : ∀ x ∈ S.ME, S.h w x = 0 := hw
  have hXo : w ∈ _root_.GlobalTheory.HL.perp L S.Hm S.X := fun x hx =>
    hME x (le_sup_of_le_left (_root_.GlobalTheory.HL.TermBasic.spanTo_mono S S.f (Nat.le_succ r)) hx)
  have hXo' : w ∈ _root_.GlobalTheory.HL.perp L S.Hm S.X' := fun x hx =>
    hME x (le_sup_of_le_right (_root_.GlobalTheory.HL.TermBasic.spanTo_mono S S.f' (Nat.le_succ r)) hx)
  refine ⟨⟨hw, ?_, ?_, ?_⟩, ⟨0, Submodule.zero_mem _, 0, Submodule.zero_mem _, by simpa using hΛ,
    by simpa using hΛ, ⟨0, Λ.zero_mem, by simp⟩, by simpa using Submodule.zero_mem _⟩⟩
  · refine ((_root_.GlobalTheory.HL.StdLat.stdLat_spec L r k S S.f S.es (Or.inl ⟨rfl, rfl⟩) _ hA).2.2 w).2 ?_
    refine (_root_.GlobalTheory.HL.TermBasic.inner_smul S hn w).2 ⟨w, ?_, hXo, by simpa using Submodule.zero_mem _⟩
    rw [← hΛn]; exact hΛ
  · refine ((_root_.GlobalTheory.HL.StdLat.stdLat_spec L r k S S.f' S.es' (Or.inr ⟨rfl, rfl⟩) _ hA').2.2 w).2 ?_
    refine (_root_.GlobalTheory.HL.TermBasic.inner_smul S hn' w).2 ⟨w, ?_, hXo', by simpa using Submodule.zero_mem _⟩
    rw [← hΛn']; exact hΛ
  · rw [hgr]
    exact ⟨w, hΛ, w, hΛ, hXo', hXo, by simpa using Submodule.zero_mem _,
      by simpa using Submodule.zero_mem _, 0, Λ.zero_mem, by simp⟩

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
variable [IsNonarchimedeanLocalField F] [CharZero F] in
/- English proof (translation)
Take `⟨-, -, -, hf, hf', -⟩` from `_root_.GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT`. Take `⟨hli, -, -, -, -, hth, hthO, -⟩` from `_root_.GlobalTheory.FrameBasic.main L r k S`. Establish `hdis` using `(linearIndependent_sum.1 hli).2.2`. Use `set θ : E := (algebraMap F E) S.th⁻¹ with hθdef`. Use `set τ : E := (algebraMap F E) S.th with hτdef`.

Establish `hτθ : τ * θ = 1`. Rewrite using `[hθdef, hτdef, ← map_mul, mul_inv_cancel₀ hth, map_one]`. Establish `hτO : τ ∈ L.O` using `(_root_.GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 hthO`. Establish `hMdef : S.M d Λ = Submodule.span L.O (Set.range (S.fr d Λ) ∪ Set.range fun b => θ • (S.fr' d Λ b - S.fr d Λ b))` using `rfl`. Establish `hfrf : ∀ i, S.fr d Λ i ∈ Λ ∧ S.fr d Λ i ∈ Submodule.span E (Set.range S.f)`.

Introduce `i`. Use `(hf (r + 1) le_rfl (S.fr d Λ i)).2 (Submodule.subset_span ⟨i, i.isLt, rfl⟩)` as an intermediate fact. Rewrite `this` using `[_root_.GlobalTheory.HL.TermBasic.spanTo_top]`. Conclude with `this`. Establish `hfr' : ∀ i, S.fr' d Λ i ∈ Submodule.span E (Set.range S.f')`.

Introduce `i`. Use `(hf' (r + 1) le_rfl (S.fr' d Λ i)).2 (Submodule.subset_span ⟨i, i.isLt, rfl⟩)` as an intermediate fact. Rewrite `this` using `[_root_.GlobalTheory.HL.TermBasic.spanTo_top]`. Conclude with `this.2`. Establish `hclaim : ∀ δ ∈ S.M d Λ, ∃ p ∈ Λ, p ∈ Submodule.span E (Set.range S.f) ∧ ∃ q ∈ Submodule.span E (Set.range S.f'), τ • δ = q - p`.

Introduce `δ hδ`. Rewrite `hδ` using `[hMdef]`. Proceed by induction on `hδ using Submodule.span_induction with`. Consider the case `mem x hx`. Break down `hx with ⟨i, rfl⟩ | ⟨i, rfl⟩` into its components or cases.

Use `⟨-(τ • S.fr d Λ i), Λ.neg_mem (Λ.smul_mem (⟨τ, hτO⟩ : L.O) (hfrf i).1), Submodule.neg_mem _ (Submodule.smul_mem _ τ (hfrf i).2), 0, Submodule.zero_mem _, by simp⟩` and prove the remaining obligations. Use `⟨S.fr d Λ i, (hfrf i).1, (hfrf i).2, S.fr' d Λ i, hfr' i, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_smul, hτθ, one_smul]`. Consider the case `zero => exact ⟨0, Λ.zero_mem, Submodule.zero_mem _, 0, Submodule.zero_mem _, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨p, hp, hpf, q, hq, e⟩` from `hx`. Take `⟨p', hp', hpf', q', hq', e'⟩` from `hy`. Use `⟨p + p', Λ.add_mem hp hp', Submodule.add_mem _ hpf hpf', q + q', Submodule.add_mem _ hq hq', ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add, e, e']`. Normalize the expressions using the abelian group laws.

Consider the case `smul c x _ hx`. Take `⟨p, hp, hpf, q, hq, e⟩` from `hx`. Use `⟨c • p, Λ.smul_mem c hp, Submodule.smul_mem _ (c : E) hpf, (c : E) • q, Submodule.smul_mem _ (c : E) hq, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `τ • ((c : E) • x) = (c : E) • q - (c : E) • p`. Rewrite using `[smul_comm, e, smul_sub]`.

Take `⟨a, ha, a', ha', m, -, -, hy⟩` from `hτ`. Establish `hδ : θ • (a' - a) ∈ S.M d Λ`. Use `(S.M d Λ).neg_mem hy` as an intermediate fact. Rewrite `this` using `[zero_sub, neg_neg]`. Then use the resulting hypothesis. Take `⟨p, hp, hpf, q, hq, e⟩` from `hclaim _ hδ`.

Rewrite `e` using `[smul_smul, hτθ, one_smul]`. Establish `haf : a ∈ Submodule.span E (Set.range S.f)`. Rewrite using `[← _root_.GlobalTheory.HL.TermBasic.spanTo_top S S.f]`. Conclude with `_root_.GlobalTheory.HL.TermBasic.spanTo_mono S S.f (Nat.le_succ r) ha`. Establish `haf' : a' ∈ Submodule.span E (Set.range S.f')`.

Rewrite using `[← _root_.GlobalTheory.HL.TermBasic.spanTo_top S S.f']`. Conclude with `_root_.GlobalTheory.HL.TermBasic.spanTo_mono S S.f' (Nat.le_succ r) ha'`. Establish `h0 : a - p = a' - q`. Establish `h1 : a - p - (a' - q) = -((a' - a) - (q - p))` using `by abel`. Rewrite using `[← sub_eq_zero, h1, e, sub_self, neg_zero]`.

Establish `hz : a - p = 0`. Use `(Submodule.disjoint_def.1 hdis) _ (Submodule.sub_mem _ haf hpf) ?_` and prove the remaining obligations. Rewrite using `[h0]`. Conclude with `Submodule.sub_mem _ haf' hq`. Establish `hap : a = p` using `sub_eq_zero.1 hz`.

Use `Λ.sub_mem m (hap ▸ hp)` as an intermediate fact. Simplify using `using this`.
-/
private theorem mem_of_tauRel_zero (d : S.Datum)
    (Λ : Submodule L.O S.V) (hT : S.IsTerm d Λ) (w : S.V)
    (hτ : S.TauRel d Λ w 0) : w ∈ Λ := by
  obtain ⟨-, -, -, hf, hf', -⟩ := _root_.GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  obtain ⟨hli, -, -, -, -, hth, hthO, -⟩ := _root_.GlobalTheory.FrameBasic.main L r k S
  have hdis := (linearIndependent_sum.1 hli).2.2
  set θ : E := (algebraMap F E) S.th⁻¹ with hθdef
  set τ : E := (algebraMap F E) S.th with hτdef
  have hτθ : τ * θ = 1 := by
    rw [hθdef, hτdef, ← map_mul, mul_inv_cancel₀ hth, map_one]
  have hτO : τ ∈ L.O := (_root_.GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 hthO
  have hMdef : S.M d Λ = Submodule.span L.O (Set.range (S.fr d Λ) ∪
      Set.range fun b => θ • (S.fr' d Λ b - S.fr d Λ b)) := rfl
  have hfrf : ∀ i, S.fr d Λ i ∈ Λ ∧ S.fr d Λ i ∈ Submodule.span E (Set.range S.f) := by
    intro i
    have := (hf (r + 1) le_rfl (S.fr d Λ i)).2 (Submodule.subset_span ⟨i, i.isLt, rfl⟩)
    rw [_root_.GlobalTheory.HL.TermBasic.spanTo_top] at this
    exact this
  have hfr' : ∀ i, S.fr' d Λ i ∈ Submodule.span E (Set.range S.f') := by
    intro i
    have := (hf' (r + 1) le_rfl (S.fr' d Λ i)).2 (Submodule.subset_span ⟨i, i.isLt, rfl⟩)
    rw [_root_.GlobalTheory.HL.TermBasic.spanTo_top] at this
    exact this.2
  have hclaim : ∀ δ ∈ S.M d Λ, ∃ p ∈ Λ, p ∈ Submodule.span E (Set.range S.f) ∧
      ∃ q ∈ Submodule.span E (Set.range S.f'), τ • δ = q - p := by
    intro δ hδ
    rw [hMdef] at hδ
    induction hδ using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · refine ⟨-(τ • S.fr d Λ i), Λ.neg_mem (Λ.smul_mem (⟨τ, hτO⟩ : L.O) (hfrf i).1),
          Submodule.neg_mem _ (Submodule.smul_mem _ τ (hfrf i).2), 0, Submodule.zero_mem _, by simp⟩
      · refine ⟨S.fr d Λ i, (hfrf i).1, (hfrf i).2, S.fr' d Λ i, hfr' i, ?_⟩
        rw [smul_smul, hτθ, one_smul]
    | zero => exact ⟨0, Λ.zero_mem, Submodule.zero_mem _, 0, Submodule.zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨p, hp, hpf, q, hq, e⟩ := hx
      obtain ⟨p', hp', hpf', q', hq', e'⟩ := hy
      refine ⟨p + p', Λ.add_mem hp hp', Submodule.add_mem _ hpf hpf', q + q',
        Submodule.add_mem _ hq hq', ?_⟩
      rw [smul_add, e, e']; abel
    | smul c x _ hx =>
      obtain ⟨p, hp, hpf, q, hq, e⟩ := hx
      refine ⟨c • p, Λ.smul_mem c hp, Submodule.smul_mem _ (c : E) hpf, (c : E) • q,
        Submodule.smul_mem _ (c : E) hq, ?_⟩
      change τ • ((c : E) • x) = (c : E) • q - (c : E) • p
      rw [smul_comm, e, smul_sub]
  obtain ⟨a, ha, a', ha', m, -, -, hy⟩ := hτ
  have hδ : θ • (a' - a) ∈ S.M d Λ := by
    have := (S.M d Λ).neg_mem hy
    rwa [zero_sub, neg_neg] at this
  obtain ⟨p, hp, hpf, q, hq, e⟩ := hclaim _ hδ
  rw [smul_smul, hτθ, one_smul] at e
  have haf : a ∈ Submodule.span E (Set.range S.f) := by
    rw [← _root_.GlobalTheory.HL.TermBasic.spanTo_top S S.f]
    exact _root_.GlobalTheory.HL.TermBasic.spanTo_mono S S.f (Nat.le_succ r) ha
  have haf' : a' ∈ Submodule.span E (Set.range S.f') := by
    rw [← _root_.GlobalTheory.HL.TermBasic.spanTo_top S S.f']
    exact _root_.GlobalTheory.HL.TermBasic.spanTo_mono S S.f' (Nat.le_succ r) ha'
  have h0 : a - p = a' - q := by
    have h1 : a - p - (a' - q) = -((a' - a) - (q - p)) := by abel
    rw [← sub_eq_zero, h1, e, sub_self, neg_zero]
  have hz : a - p = 0 := by
    refine (Submodule.disjoint_def.1 hdis) _ (Submodule.sub_mem _ haf hpf) ?_
    rw [h0]; exact Submodule.sub_mem _ haf' hq
  have hap : a = p := sub_eq_zero.1 hz
  have := Λ.sub_mem m (hap ▸ hp)
  simpa using this

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} {S : _root_.GlobalTheory.HL.Frames L r k} in

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ L r k S d Λ hT`. Establish `h1` using `exists_tauRel_of_mem_complementLattice S d Λ hT`. Establish `h2` using `tauRel_iff_sub_mem_M S d Λ hT`. Establish `hMsat` using `(_root_.GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT).2.2.1`. Use `⟨h1, h2, fun c hc w₁ w₂ y₁ y₂ => tauRel_smul_add S d Λ c hc w₁ w₂ y₁ y₂, fun w hw => ⟨mem_complementLattice_of_mem_term S d Λ hT w hw, fun h => mem_of_tauRel_zero S d Λ hT w h.2⟩, ?_, _root_.GlobalTheory.HL.CompLat.main L r k S d Λ hT⟩` and prove the remaining obligations.

Unfold `_root_.GlobalTheory.HL.Frames.Ihat`. Use `sup_le hMsat (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `y ⟨w, hw, hwy⟩`. Take `⟨y₀, hy₀, hwy₀⟩` from `h1 w hw`. Establish `hd : y₀ - y ∈ S.M d Λ` using `(h2 w y₀ y hwy₀).1 hwy`.

Establish `: y = y₀ - (y₀ - y)` using `by abel`. Rewrite using `[this]`. Conclude with `(S.sat Λ).sub_mem hy₀ (hMsat hd)`.
-/
theorem _root_.GlobalTheory.HL.Gluing.main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ (r k : ℕ) (S : _root_.GlobalTheory.HL.Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → (∀ w ∈ S.complementLatticeOfDatum d, ∃ y ∈ S.sat Λ, S.TauRel d Λ w y) ∧ (∀ w y y', S.TauRel d Λ w y → (S.TauRel d Λ w y' ↔ y - y' ∈ S.M d Λ)) ∧ (∀ c ∈ L.O, ∀ w₁ w₂ y₁ y₂, S.TauRel d Λ w₁ y₁ → S.TauRel d Λ w₂ y₂ → S.TauRel d Λ (c • w₁ + w₂) (c • y₁ + y₂)) ∧ (∀ w ∈ S.W0, w ∈ Λ ↔ (w ∈ S.complementLatticeOfDatum d ∧ S.TauRel d Λ w 0)) ∧ S.Ihat d Λ ≤ S.sat Λ ∧ ∃ b : Fin (k - 1) → S.V, LinearIndependent E b ∧ S.complementLatticeOfDatum d = (Submodule.span L.O (Set.range b) : Set S.V) := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT
  have h1 := exists_tauRel_of_mem_complementLattice S d Λ hT
  have h2 := tauRel_iff_sub_mem_M S d Λ hT
  have hMsat := (_root_.GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT).2.2.1
  refine ⟨h1, h2, fun c hc w₁ w₂ y₁ y₂ => tauRel_smul_add S d Λ c hc w₁ w₂ y₁ y₂,
    fun w hw => ⟨mem_complementLattice_of_mem_term S d Λ hT w hw,
      fun h => mem_of_tauRel_zero S d Λ hT w h.2⟩, ?_,
    _root_.GlobalTheory.HL.CompLat.main L r k S d Λ hT⟩
  unfold _root_.GlobalTheory.HL.Frames.Ihat
  refine sup_le hMsat (Submodule.span_le.2 ?_)
  rintro y ⟨w, hw, hwy⟩
  obtain ⟨y₀, hy₀, hwy₀⟩ := h1 w hw
  have hd : y₀ - y ∈ S.M d Λ := (h2 w y₀ y hwy₀).1 hwy
  have : y = y₀ - (y₀ - y) := by abel
  rw [this]
  exact (S.sat Λ).sub_mem hy₀ (hMsat hd)

end GlobalTheory.HL.Gluing
