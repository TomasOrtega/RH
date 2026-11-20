import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.BadEx2
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.SymIdx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableTwistedOrbitalIntegralIntegralNormCongruen

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.Bc.ArchbcB.B
open PositivityTheory.Rg.BcB.F.Ex0
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Ex0.BadInertP

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Apply the tactic sequence `by_cases hp : P <;> by_cases hq : Q`. Conclude with `iff_of_true hp hq`. Rewrite `h` using `[if_pos hp, if_neg hq]`. Conclude with `absurd h one_ne_zero`. Rewrite `h` using `[if_neg hp, if_pos hq]`.

Conclude with `absurd h.symm one_ne_zero`. Conclude with `iff_of_false hp hq`.
-/
theorem iff_of_ite_eq {P Q : Prop} {hP : Decidable P} {hQ : Decidable Q}
    (h : @ite ℂ P hP 1 0 = @ite ℂ Q hQ 1 0) : P ↔ Q := by
  by_cases hp : P <;> by_cases hq : Q
  · exact iff_of_true hp hq
  · rw [if_pos hp, if_neg hq] at h; exact absurd h one_ne_zero
  · rw [if_neg hp, if_pos hq] at h; exact absurd h.symm one_ne_zero
  · exact iff_of_false hp hq

/- English proof (translation)
Distinguish the cases in `hp : P`. Rewrite using `[if_pos hp, if_pos (h.1 hp)]`. Rewrite using `[if_neg hp, if_neg (fun hq => hp (h.2 hq))]`.
-/
theorem ite_congr' {P Q : Prop} {hP : Decidable P} {hQ : Decidable Q} (h : P ↔ Q) :
    @ite ℂ P hP 1 0 = @ite ℂ Q hQ 1 0 := by
  by_cases hp : P
  · rw [if_pos hp, if_pos (h.1 hp)]
  · rw [if_neg hp, if_neg (fun hq => hp (h.2 hq))]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun ⟨a, b, c, d⟩ => ⟨(h1.1 ⟨a, b⟩).1, (h1.1 ⟨a, b⟩).2, (h2.1 ⟨c, d⟩).1, (h2.1 ⟨c, d⟩).2⟩, fun ⟨a, b, c, d⟩ => ⟨(h1.2 ⟨a, b⟩).1, (h1.2 ⟨a, b⟩).2, (h2.2 ⟨c, d⟩).1, (h2.2 ⟨c, d⟩).2⟩⟩`.
-/
theorem and4 {A B C D A' B' C' D' : Prop} (h1 : A ∧ B ↔ A' ∧ B') (h2 : C ∧ D ↔ C' ∧ D') :
    A ∧ B ∧ C ∧ D ↔ A' ∧ B' ∧ C' ∧ D' :=
  ⟨fun ⟨a, b, c, d⟩ => ⟨(h1.1 ⟨a, b⟩).1, (h1.1 ⟨a, b⟩).2, (h2.1 ⟨c, d⟩).1, (h2.1 ⟨c, d⟩).2⟩,
    fun ⟨a, b, c, d⟩ => ⟨(h1.2 ⟨a, b⟩).1, (h1.2 ⟨a, b⟩).2, (h2.2 ⟨c, d⟩).1, (h2.2 ⟨c, d⟩).2⟩⟩

abbrev Cnd (n m : ℕ) (w : Pl E) (y : GLw n w) : Prop :=
  y ∈ GlobalTheory.LFun.KGL w n ∧ nrmL n w y ∈ {g : GLw n w | g ∈ GlobalTheory.LFun.KGL w n ∧ ∀ i j,
    Valued.v (g.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(m : ℤ))}

/- English proof (translation)
Establish `hl` using `(GlobalTheory.BCT.StTwLevel.lev_hecke hw n m).2 k hk y`. Rewrite `hl` using `[← GlobalTheory.BCT.StTwLevel.lev_eq n m]`. Conclude with `⟨iff_of_ite_eq hl.1, iff_of_ite_eq hl.2⟩`.
-/
theorem cnd_iff {w : Pl E} (hw : ¬ IsSplitAt w) (n m : ℕ) {k : GLw n w} (hk : k ∈ GlobalTheory.PrincCong.congSub w n m)
    (y : GLw n w) : (Cnd n m w (k * y) ↔ Cnd n m w y) ∧ (Cnd n m w (y * k) ↔ Cnd n m w y) := by
  have hl := (GlobalTheory.BCT.StTwLevel.lev_hecke hw n m).2 k hk y
  rw [← GlobalTheory.BCT.StTwLevel.lev_eq n m] at hl
  exact ⟨iff_of_ite_eq hl.1, iff_of_ite_eq hl.2⟩

/- English proof (translation)
Use `⟨?_, fun k hk x => ?_⟩` and prove the remaining obligations. Establish `ha` using `GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a`. Establish `hb` using `GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b`. Use `HasCompactSupport.intro' (ha.2.prod hb.2) ((Subgroup.isClosed_of_isOpen _ ha.1).prod (Subgroup.isClosed_of_isOpen _ hb.1)) fun y hy => ?_` and prove the remaining obligations. Use `beta_reduce`.

Rewrite using `[if_neg fun h => hy ⟨h.1, h.2.2.1⟩, mul_zero, mul_zero]`. Take `⟨h1, h2⟩` from `Subgroup.mem_prod.1 hk`. Take `⟨e1, f1⟩` from `cnd_iff hw a m h1 x.1`. Take `⟨e2, f2⟩` from `cnd_iff hw b m h2 x.2`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Use `show r * (c * _) = r * (c * _)`. Use `congr 2`. Conclude with `ite_congr' (and4 e1 e2)`. Use `show r * (c * _) = r * (c * _)`. Use `congr 2`.

Conclude with `ite_congr' (and4 f1 f2)`.
-/
theorem hecke_phi {w : Pl E} (hw : ¬ IsSplitAt w) (a b m : ℕ) (r c : ℂ) :
    IsHecke ((GlobalTheory.PrincCong.congSub w a m).prod (GlobalTheory.PrincCong.congSub w b m))
      (fun y : GLw a w × GLw b w => r * (c * (if y.1 ∈ GlobalTheory.LFun.KGL w a ∧ nrmL a w y.1 ∈ {g : GLw a w | g ∈ GlobalTheory.LFun.KGL w a ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(m : ℤ))} ∧ y.2 ∈ GlobalTheory.LFun.KGL w b ∧ nrmL b w y.2 ∈ {g : GLw b w | g ∈ GlobalTheory.LFun.KGL w b ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(m : ℤ))} then 1 else 0))) := by
  refine ⟨?_, fun k hk x => ?_⟩
  · have ha := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a
    have hb := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b
    refine HasCompactSupport.intro' (ha.2.prod hb.2)
      ((Subgroup.isClosed_of_isOpen _ ha.1).prod (Subgroup.isClosed_of_isOpen _ hb.1)) fun y hy => ?_
    beta_reduce
    rw [if_neg fun h => hy ⟨h.1, h.2.2.1⟩, mul_zero, mul_zero]
  · obtain ⟨h1, h2⟩ := Subgroup.mem_prod.1 hk
    obtain ⟨e1, f1⟩ := cnd_iff hw a m h1 x.1
    obtain ⟨e2, f2⟩ := cnd_iff hw b m h2 x.2
    refine ⟨?_, ?_⟩
    · show r * (c * _) = r * (c * _)
      congr 2
      exact ite_congr' (and4 e1 e2)
    · show r * (c * _) = r * (c * _)
      congr 2
      exact ite_congr' (and4 f1 f2)

/- English proof (translation)
Use function extensionality and compare the values at `γ`. Unfold `U.lone`. Simplify using `only [Set.indicator_apply, Pi.one_apply]`. Use `split_ifs with h1 h2 h2`. Rewrite using `[mul_one]`.

Conclude with `absurd ((hKB γ).1 h1) h2`. Conclude with `absurd ((hKB γ).2 h2) h1`. Rewrite using `[mul_zero]`.
-/
theorem lone_eq {w : Pl E} {n m : ℕ} {KB : Subgroup (UL n w)} (hKB : IsCong m KB) :
    U.lone KB = fun γ => ((KB.relIndex (KL n w) : ℕ) : ℂ) * ((({γ : UL n w | γ.1 ∈ {g : GLw n w | g ∈ GlobalTheory.LFun.KGL w n ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(m : ℤ))}} : Set (UL n w))).indicator 1 γ) := by
  funext γ
  unfold U.lone
  simp only [Set.indicator_apply, Pi.one_apply]
  split_ifs with h1 h2 h2
  · rw [mul_one]
  · exact absurd ((hKB γ).1 h1) h2
  · exact absurd ((hKB γ).2 h2) h1
  · rw [mul_zero]

/- English proof (translation)
Simplify using `only [GlobalTheory.BCT.delta, if_neg hw]`.
-/
theorem delta_inert {w : Pl E} (hw : ¬ IsSplitAt w) (μ μ' : (w.adicCompletion E)ˣ →* ℂˣ)
    (Q₁ Q₂ : Polynomial (w.adicCompletion E)) : GlobalTheory.BCT.delta w μ Q₁ Q₂ = GlobalTheory.BCT.delta w μ' Q₁ Q₂ := by
  simp only [GlobalTheory.BCT.delta, if_neg hw]

/- English proof (translation)
Introduce `Q₁ Q₂ m₁ m₂ d₁ d₂ hs c₁ c₂`. Rewrite using `[GlobalTheory.BCT.StTwLevel.stTw2_const_mul, hM Q₁ Q₂ m₁ m₂ d₁ d₂ hs c₁ c₂, delta_inert hw μ 1, hf]`. Unfold `GlobalTheory.BCT.kapOrb`. Rewrite using `[GlobalTheory.BCT.StTwLevel.clSum_const_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem match_of {w : Pl E} (hw : ¬ IsSplitAt w) {n a b : ℕ} (μ : (w.adicCompletion E)ˣ →* ℂˣ) {f F0 : UL n w → ℂ}
    {Φ0 : GLw a w × GLw b w → ℂ} (r : ℂ) (hM : GlobalTheory.BCT.Match n a b w 1 F0 Φ0) (hf : f = fun x => r * F0 x) :
    GlobalTheory.BCT.Match n a b w μ f (fun y => r * Φ0 y) := by
  intro Q₁ Q₂ m₁ m₂ d₁ d₂ hs c₁ c₂
  rw [GlobalTheory.BCT.StTwLevel.stTw2_const_mul, hM Q₁ Q₂ m₁ m₂ d₁ d₂ hs c₁ c₂, delta_inert hw μ 1, hf]
  unfold GlobalTheory.BCT.kapOrb
  rw [GlobalTheory.BCT.StTwLevel.clSum_const_mul]
  ring

/- English proof (translation)
Use function extensionality and compare the values at `y`. Unfold `MB.pairIndicatorMatch MB.congK`. Use `congr 2`.
-/
theorem bad_inert_pair_indicator_eq (n a b k : ℕ) (w : Pl E) : MB.pairIndicatorMatch n a b w k = fun y : GLw a w × GLw b w => ((-((Real.sqrt (qV E w : ℝ) : ℝ) : ℂ)) ^ (k * a * b))⁻¹ * (if y.1 ∈ GlobalTheory.LFun.KGL w a ∧ nrmL a w y.1 ∈ {g : GLw a w | g ∈ GlobalTheory.LFun.KGL w a ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} ∧ y.2 ∈ GlobalTheory.LFun.KGL w b ∧ nrmL b w y.2 ∈ {g : GLw b w | g ∈ GlobalTheory.LFun.KGL w b ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then 1 else 0) := by
  funext y
  unfold MB.pairIndicatorMatch MB.congK
  congr 2

end PositivityTheory.Rg.BcB.F.Ex0.BadInertP

namespace PositivityTheory.Rg.BcB.F.Ex0

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Introduce `E _ _ _ hE n a ha w hw μ _ m hm KB hKB`. Establish `hM` using `h2 E hE w hw n a (n - a) m (Nat.add_sub_cancel' ha) hm`. Establish `e : fixFn n a w μ m KB = fun y => ((KB.relIndex (KL n w) : ℕ) : ℂ) * MB.pairIndicatorMatch n a (n - a) w m y`. Unfold `fixFn`. Rewrite using `[dif_pos ha, if_neg hw]`.

Rewrite using `[e, BadInertP.bad_inert_pair_indicator_eq]`. Conclude with `⟨_, ⟨_, _, rfl, GlobalTheory.BCT.StTwLevel.lev_level hw a m, GlobalTheory.BCT.StTwLevel.lev_level hw (n - a) m⟩, BadInertP.hecke_phi hw a (n - a) m ((KB.relIndex (KL n w) : ℕ) : ℂ) ((-((Real.sqrt (qV E w : ℝ) : ℝ) : ℂ)) ^ (m * a * (n - a)))⁻¹, BadInertP.match_of hw μ _ hM (BadIne …`.
-/
theorem badInert2 (h2 : M2) : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (n a : ℕ), a ≤ n →
    ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (μ : (w.adicCompletion E)ˣ →* ℂˣ), IsOpen (μ.ker : Set (w.adicCompletion E)ˣ) →
    ∀ m : ℕ, 1 ≤ m → ∀ KB : Subgroup (UL n w), IsCong m KB →
    ∃ L : Subgroup (GLw a w × GLw (n - a) w), IsPairLevel L ∧ IsHecke L (fixFn n a w μ m KB) ∧
      Match n a (n - a) w μ (U.lone KB) (fixFn n a w μ m KB) := by
  intro E _ _ _ hE n a ha w hw μ _ m hm KB hKB
  have hM := h2 E hE w hw n a (n - a) m (Nat.add_sub_cancel' ha) hm
  have e : fixFn n a w μ m KB = fun y => ((KB.relIndex (KL n w) : ℕ) : ℂ) * MB.pairIndicatorMatch n a (n - a) w m y := by
    unfold fixFn
    rw [dif_pos ha, if_neg hw]
  rw [e, BadInertP.bad_inert_pair_indicator_eq]
  exact ⟨_, ⟨_, _, rfl, GlobalTheory.BCT.StTwLevel.lev_level hw a m, GlobalTheory.BCT.StTwLevel.lev_level hw (n - a) m⟩,
    BadInertP.hecke_phi hw a (n - a) m ((KB.relIndex (KL n w) : ℕ) : ℂ)
      ((-((Real.sqrt (qV E w : ℝ) : ℝ) : ℂ)) ^ (m * a * (n - a)))⁻¹,
    BadInertP.match_of hw μ _ hM (BadInertP.lone_eq hKB)⟩

end PositivityTheory.Rg.BcB.F.Ex0

end
