import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TowerIsChain

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace GlobalTheory.ChainOnto.FlagModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {c : Com D} {s s' : PiLocalization₂ D}

/- English proof (translation)
Assemble the required witnesses or components as `⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _⟩`.
-/
theorem inFlag_one : s.InFlag 1 := ⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨Subgroup.mul_mem _ h.1 h'.1, by rw [map_mul]; exact Subgroup.mul_mem _ h.2 h'.2⟩`.
-/
theorem inFlag_mul {κ κ' : GA D s.V} (h : s.InFlag κ) (h' : s.InFlag κ') : s.InFlag (κ * κ') :=
  ⟨Subgroup.mul_mem _ h.1 h'.1, by rw [map_mul]; exact Subgroup.mul_mem _ h.2 h'.2⟩

/- English proof (translation)
The claim follows from `Lev.levChi_ne_zero _ _`.
-/
theorem ch_ne_zero (κ : GA D s.V) : s.ch κ ≠ 0 := Lev.levChi_ne_zero _ _

/- English proof (translation)
Unfold `PiLocalization₂.ch Lev.levChi`. Rewrite using `[map_mul, Lev.levFn_flag_mul h.2 h'.2, Units.val_mul]`.
-/
theorem ch_mul {κ κ' : GA D s.V} (h : s.InFlag κ) (h' : s.InFlag κ') : s.ch (κ * κ') = s.ch κ * s.ch κ' := by
  unfold PiLocalization₂.ch Lev.levChi
  rw [map_mul, Lev.levFn_flag_mul h.2 h'.2, Units.val_mul]

/- English proof (translation)
Establish `h` using `ch_mul (s := s) inFlag_one inFlag_one`. Rewrite `h` using `[mul_one]`. Conclude with `(mul_eq_left₀ (ch_ne_zero _)).1 h.symm`.
-/
theorem ch_one : s.ch 1 = 1 := by
  have h := ch_mul (s := s) inFlag_one inFlag_one
  rw [mul_one] at h
  exact (mul_eq_left₀ (ch_ne_zero _)).1 h.symm

/- English proof (translation)
Introduce `w g`. Rewrite using `[ch_one, mul_one, inv_one, one_mul]`.
-/
theorem moved_one (y : s.CC c) : Moved 1 y y := by
  intro w g; rw [ch_one, mul_one, inv_one, one_mul]

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use `LinearMap.ext fun w => funext fun g => ?_` and prove the remaining obligations. Conclude with `(ha w g).trans (hb w g).symm`.
-/
theorem moved_unique {κ : GA D s.V} {y a b : s.CC c} (ha : Moved κ y a) (hb : Moved κ y b) : a = b := by
  apply Subtype.ext
  refine LinearMap.ext fun w => funext fun g => ?_
  exact (ha w g).trans (hb w g).symm

/- English proof (translation)
Introduce `w g`. Rewrite using `[hb w g, ha w (g * κ), ch_mul h h', mul_assoc g, mul_inv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem moved_mul {κ κ' : GA D s.V} (h : s.InFlag κ) (h' : s.InFlag κ') {y a b : s.CC c}
    (ha : Moved κ' y a) (hb : Moved κ a b) : Moved (κ * κ') y b := by
  intro w g
  rw [hb w g, ha w (g * κ), ch_mul h h', mul_assoc g, mul_inv]; ring

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => ⟨h.1, h.2, rfl⟩, fun h => ⟨h.1, h.2.1⟩⟩`.
-/
theorem inFlag_iff (κ : GA D s.V) :
    s.InFlag κ ↔ Lev.IsLevelLift s.V s.β s.L (rTup s.β s.L (Lev.finE s.V κ)) κ :=
  ⟨fun h => ⟨h.1, h.2, rfl⟩, fun h => ⟨h.1, h.2.1⟩⟩

/- English proof (translation)
Take `⟨hr, ξ, hL⟩` from `hs.lev`. Establish `h1 : ext1 s.L.P.H s.L.P.chi (rTup s.β s.L (Lev.finE s.V κ)) = 1`. Establish `hb : s.L.P.H = ⊥` using `by rw [hL]; exact hP`. Unfold `ext1`. Use `split_ifs with hh`.

Establish `: (⟨_, hh⟩ : s.L.P.H) = 1`. Apply `Subtype.ext` to reduce the goal to its premises. Use `hh` as an intermediate fact. Rewrite `this` using `[hb]`. Conclude with `Subgroup.mem_bot.1 this`.

Rewrite using `[this, map_one]`. Both sides reduce to the same expression. Establish `h2 : ext1 (Lev.flagL s.L).P.H (Lev.flagL s.L).P.chi (rTup s.β (Lev.flagL s.L) (Lev.finE s.V κ)) = 1` using `Lev.subgroupCharExtension_one_apply _ _`. Unfold `PiLocalization₂.ch Lev.levChi levFn`. Rewrite using `[h1, h2]`.

Both sides reduce to the same expression.
-/
theorem ch_eq_levChi {j : ℕ} (hs : s.Is c j) (hP : c.P.H = ⊥) (κ : GA D s.V) :
    s.ch κ = Lev.levChi s.V s.β s.L κ := by
  obtain ⟨hr, ξ, hL⟩ := hs.lev
  have h1 : ext1 s.L.P.H s.L.P.chi (rTup s.β s.L (Lev.finE s.V κ)) = 1 := by
    have hb : s.L.P.H = ⊥ := by rw [hL]; exact hP
    unfold ext1
    split_ifs with hh
    · have : (⟨_, hh⟩ : s.L.P.H) = 1 := by
        apply Subtype.ext
        have := hh
        rw [hb] at this
        exact Subgroup.mem_bot.1 this
      rw [this, map_one]
    · rfl
  have h2 : ext1 (Lev.flagL s.L).P.H (Lev.flagL s.L).P.chi (rTup s.β (Lev.flagL s.L) (Lev.finE s.V κ)) = 1 :=
    Lev.subgroupCharExtension_one_apply _ _
  unfold PiLocalization₂.ch Lev.levChi levFn
  rw [h1, h2]
  rfl

/- English proof (translation)
Take `⟨hr, ξ, hL⟩` from `hs.lev`. Establish `hb : s.L.P.H = ⊥` using `by rw [hL]; exact hP`. Establish `h : rTup s.β s.L (Lev.finE s.V κ) ∈ s.L.P.H` using `hκ.2.2`. Rewrite `h` using `[hb]`. Conclude with `Subgroup.mem_bot.1 h`.
-/
theorem rTup_eq_one {j : ℕ} (hs : s.Is c j) (hP : c.P.H = ⊥) {κ : GA D s.V} (hκ : κ ∈ Lev.levG s.V s.β s.L) :
    rTup s.β s.L (Lev.finE s.V κ) = 1 := by
  obtain ⟨hr, ξ, hL⟩ := hs.lev
  have hb : s.L.P.H = ⊥ := by rw [hL]; exact hP
  have h : rTup s.β s.L (Lev.finE s.V κ) ∈ s.L.P.H := hκ.2.2
  rw [hb] at h
  exact Subgroup.mem_bot.1 h

/- English proof (translation)
Unfold `SameBlock`. Rewrite using `[h, h']`. Take `⟨hr, ξ, hL⟩` from `hs.lev`. Take `⟨hr', ξ', hL'⟩` from `hs'.lev`. Rewrite using `[hL, hL']`.

Conclude with `HEq.rfl`.
-/
theorem sameBlock_of_one {j j' : ℕ} (hs : s.Is c j) (hs' : s'.Is c j') {κ : GA D s.V} {κ' : GA D s'.V}
    (h : rTup s.β s.L (Lev.finE s.V κ) = 1) (h' : rTup s'.β s'.L (Lev.finE s'.V κ') = 1) : SameBlock s s' κ κ' := by
  unfold SameBlock
  rw [h, h']
  obtain ⟨hr, ξ, hL⟩ := hs.lev
  obtain ⟨hr', ξ', hL'⟩ := hs'.lev
  rw [hL, hL']
  exact HEq.rfl

/- English proof (translation)
Take `⟨hr, ξ, hL⟩` from `hs.lev`. Take `⟨hr', ξ', hL'⟩` from `hs'.lev`. Establish `e : G0 s.L.Pg s.L.r = G0 s'.L.Pg s'.L.r` using `by rw [hL, hL']; rfl`. Take `⟨κ', h1, h2, h3⟩` from `hl (cast e (rTup s.β s.L (Lev.finE s.V κ)))`. Use `⟨κ', ⟨h1, h2⟩, ?_⟩` and prove the remaining obligations.

Unfold `SameBlock`. Rewrite using `[h3]`. Conclude with `(cast_heq _ _).symm`.
-/
theorem exists_sameBlock {j j' : ℕ} (hs : s.Is c j) (hs' : s'.Is c j') (hl : Lev.LiftsExist s'.V s'.β s'.L)
    (κ : GA D s.V) : ∃ κ', s'.InFlag κ' ∧ SameBlock s s' κ κ' := by
  obtain ⟨hr, ξ, hL⟩ := hs.lev
  obtain ⟨hr', ξ', hL'⟩ := hs'.lev
  have e : G0 s.L.Pg s.L.r = G0 s'.L.Pg s'.L.r := by rw [hL, hL']; rfl
  obtain ⟨κ', h1, h2, h3⟩ := hl (cast e (rTup s.β s.L (Lev.finE s.V κ)))
  refine ⟨κ', ⟨h1, h2⟩, ?_⟩
  unfold SameBlock
  rw [h3]
  exact (cast_heq _ _).symm

/- English proof (translation)
Introduce `hg c hc k hk s s' hs hs' p hp hP φ`. Establish `H` using `h hg c hc k hk s s' hs hs' p hp hP`. Establish `o : rTup s.β s.L (Lev.finE s.V 1) = 1` using `by rw [map_one]; exact rTup_one`. Establish `o' : rTup s'.β s'.L (Lev.finE s'.V 1) = 1` using `by rw [map_one]; exact rTup_one`. Use `⟨fun κ hκ => ?_, fun κ hκ => ?_⟩` and prove the remaining obligations.

Use `H κ 1 ⟨hκ.1, hκ.2.1⟩ inFlag_one (sameBlock_of_one hs hs' (rTup_eq_one hs hP hκ) o') φ` as an intermediate fact. Rewrite using `[this, ch_one, ch_eq_levChi hs hP, inv_one, mul_one]`. Use `H 1 κ inFlag_one ⟨hκ.1, hκ.2.1⟩ (sameBlock_of_one hs hs' o (rTup_eq_one hs' hP hκ)) φ` as an intermediate fact. Rewrite using `[this, ch_one, ch_eq_levChi hs' hP, one_mul]`.
-/
theorem levelLaw_of_pairLaw (h : PairLaw D) : ForStep D fun c _ s s' p => c.P.H = ⊥ → ∀ φ,
    VecLaw p.ω (Lev.levG s.V s.β s.L) (Lev.levChi s.V s.β s.L) (Lev.levG s'.V s'.β s'.L)
      (fun κ => (Lev.levChi s'.V s'.β s'.L κ)⁻¹) (p.pt φ) := by
  intro hg c hc k hk s s' hs hs' p hp hP φ
  have H := h hg c hc k hk s s' hs hs' p hp hP
  have o : rTup s.β s.L (Lev.finE s.V 1) = 1 := by rw [map_one]; exact rTup_one
  have o' : rTup s'.β s'.L (Lev.finE s'.V 1) = 1 := by rw [map_one]; exact rTup_one
  refine ⟨fun κ hκ => ?_, fun κ hκ => ?_⟩
  · have := H κ 1 ⟨hκ.1, hκ.2.1⟩ inFlag_one (sameBlock_of_one hs hs' (rTup_eq_one hs hP hκ) o') φ
    rw [this, ch_one, ch_eq_levChi hs hP, inv_one, mul_one]
  · have := H 1 κ inFlag_one ⟨hκ.1, hκ.2.1⟩ (sameBlock_of_one hs hs' o (rTup_eq_one hs' hP hκ)) φ
    rw [this, ch_one, ch_eq_levChi hs' hP, one_mul]

/- English proof (translation)
Use `⟨fun k hk => ⟨hW.ωY k hk, ⟨W.xiR (), W.vac k, ?_⟩, hW.ptY k hk, hW.ItY k hk, hW.ioY k (by omega)⟩, ⟨hW.ωX, ⟨W.xiR (), W.vacX, ?_⟩, hW.ptX, hW.ItX, hW.ioX⟩⟩` and prove the remaining obligations. Use `hW.vY k hk` as an intermediate fact. Rewrite `this` using `[hQ]`. Conclude with `this`. Use `hW.vX` as an intermediate fact.

Rewrite `this` using `[hQ]`. Conclude with `this`.
-/
theorem steps_of_is (W : GlobalTheory.Core.Rk.Tower D) (hW : W.Is) (hQ : W.Q () = ∅) :
    (∀ k, k + 1 < D.R.m → (stepY W k).Is (k + 1)) ∧ (stepX W).Is D.R.m := by
  refine ⟨fun k hk => ⟨hW.ωY k hk, ⟨W.xiR (), W.vac k, ?_⟩, hW.ptY k hk, hW.ItY k hk, hW.ioY k (by omega)⟩,
    ⟨hW.ωX, ⟨W.xiR (), W.vacX, ?_⟩, hW.ptX, hW.ItX, hW.ioX⟩⟩
  · have := hW.vY k hk
    rw [hQ] at this
    exact this
  · have := hW.vX
    rw [hQ] at this
    exact this

/- English proof (translation)
Use `⟨fun j => ⟨r_le_Y j, W.xiR (), ?_⟩, ⟨r_le_X, W.xiR (), ?_⟩, rfl⟩` and prove the remaining obligations. Rewrite using `[← hQ]`. Both sides reduce to the same expression. Rewrite using `[← hQ]`. Both sides reduce to the same expression.
-/
theorem lev_of_Q (W : GlobalTheory.Core.Rk.Tower D) (hQ : W.Q () = ∅) :
    (∀ j, ∃ hr ξ, (stageY W j).L = Lev.datY (stageY W j).V.rank D.R.r D.R.t j hr (comOf W).Pg ∅ (comOf W).P (comOf W).chi ξ Lev.Frm.B) ∧
    (∃ hr ξ, (stageX W).L = Lev.datY (stageX W).V.rank D.R.r D.R.t D.R.m hr (comOf W).Pg ∅ (comOf W).P (comOf W).chi ξ Lev.Frm.B) ∧
    (comOf W).P.H = ⊥ := by
  refine ⟨fun j => ⟨r_le_Y j, W.xiR (), ?_⟩, ⟨r_le_X, W.xiR (), ?_⟩, rfl⟩
  · rw [← hQ]; rfl
  · rw [← hQ]; rfl

/- English proof (translation)
Use `Finset.eq_empty_of_forall_notMem fun PP hP => ?_` and prove the remaining obligations. Establish `h` using `(hW.chars.Q_ram () PP).2 (Or.inl hP)`. Rewrite `h` using `[hW.chars.xi_base]`. Conclude with `h fun x _ => rfl`.
-/
theorem q_empty (W : GlobalTheory.Core.Rk.Tower D) (hW : W.Is) : W.Q () = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun PP hP => ?_
  have h := (hW.chars.Q_ram () PP).2 (Or.inl hP)
  rw [hW.chars.xi_base] at h
  exact h fun x _ => rfl

/- English proof (translation)
The claim follows from `steps_of_is W hW (q_empty W hW)`.
-/
theorem steps_of_is' (W : GlobalTheory.Core.Rk.Tower D) (hW : W.Is) :
    (∀ k, k + 1 < D.R.m → (stepY W k).Is (k + 1)) ∧ (stepX W).Is D.R.m := steps_of_is W hW (q_empty W hW)

end GlobalTheory.ChainOnto.FlagModel

end
