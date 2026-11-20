import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SuppInd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

namespace GlobalTheory

/- English proof (translation)
Introduce `X Aψ G _ _ _ _ ψ B Λc red T hs SB Hd Th ip f₀ Gd hsurj hB hSB htr hmod hf₀ hwit hslin hThlin hThhs hiplin hipconj hiphs hThf₀ hip₀`. Take `⟨rep, hrep⟩ : ∃ rep : G → Λc, ∀ c, red (rep c) = c` from `⟨Function.surjInv hsurj, Function.surjInv_eq hsurj⟩`. Take `⟨ind, hind⟩ : ∃ ind : G → X → ℂ, ∀ c t, ind c t = if h : t ∈ Λc then (if red ⟨t, h⟩ = c then (1:ℂ) else 0) else 0` from `⟨_, fun _ _ => rfl⟩`. Take `⟨g, hg⟩ : ∃ g : G → X → ℂ, ∀ c, g c = T (ind c)` from `⟨_, fun _ => rfl⟩`. Take `⟨χ, hχd⟩ : ∃ χ : X → G → ℂ, ∀ y c, χ y c = ψ (B (rep c) y)` from `⟨_, fun _ _ => rfl⟩`.

Establish `hB0 : ∀ y, B 0 y = 0` using `fun y => by simpa using hB 0 0 y`. Establish `hBn : ∀ (m : ℕ) t y, B (m • t) y = m • B t y`. Introduce `m t y`. Proceed by induction on `m with`. Consider the case `zero => simp [hB0]`.

Consider the case `succ m ih => rw [succ_nsmul, hB, ih, succ_nsmul]`. Establish `hχ : ∀ y, (∀ k : Λc, red k = 0 → ψ (B k y) = 1) → ∀ t : Λc, ψ (B t y) = χ y (red t)`. Introduce `y hy t`. Establish `hk : red (t - rep (red t)) = 0` using `by rw [map_sub, hrep, sub_self]`. Establish `ht : (t : X) = ((t - rep (red t) : Λc) : X) + (rep (red t) : X)` using `by simp`.

Rewrite using `[ht, hB, AddChar.map_add_eq_mul, hy _ hk, one_mul, hχd]`. Establish `hχpow : ∀ y, (∀ k : Λc, red k = 0 → ψ (B k y) = 1) → ∀ c, χ y c ^ Fintype.card G = 1`. Introduce `y hy c`. Rewrite using `[hχd, ← AddChar.map_nsmul_eq_pow, ← hBn]`. Use `hy (Fintype.card G • rep c) (by rw [map_nsmul, card_nsmul_eq_zero])` as an intermediate fact.

Simplify using `using this`. Establish `hχnorm : ∀ y, (∀ k : Λc, red k = 0 → ψ (B k y) = 1) → ∀ c, ‖χ y c‖ = 1` using `fun y hy c => Complex.norm_eq_one_of_pow_eq_one (hχpow y hy c) Fintype.card_ne_zero`. Establish `hχconj : ∀ y, (∀ k : Λc, red k = 0 → ψ (B k y) = 1) → ∀ c, starRingEnd ℂ (χ y c) * χ y c = 1`. Introduce `y hy c`. Rewrite using `[Complex.conj_mul', hχnorm y hy c]`.

Simplify using the standard rewrite rules. Establish `hsep : ∀ c d, c ≠ d → ∃ y, Hd y ∧ (∀ k : Λc, red k = 0 → ψ (B k y) = 1) ∧ χ y c ≠ χ y d`. Introduce `c d hcd`. Take `⟨y, hHd, hy, hne⟩` from `hwit (rep (c - d)) (by rw [hrep]; exact sub_ne_zero.mpr hcd)`. Use `⟨y, hHd, hy, fun heq => hne ?_⟩` and prove the remaining obligations.

Establish `h1` using `hχ y hy (rep (c - d) + rep d)`. Establish `hr : red (rep (c - d) + rep d) = c` using `by rw [map_add, hrep, hrep, sub_add_cancel]`. Rewrite `h1` using `[hr, AddSubgroup.coe_add, hB, AddChar.map_add_eq_mul, ← hχd y d, heq]`. Establish `h0 : χ y d ≠ 0` using `fun h => by simpa [h] using hχnorm y hy d`. Conclude with `mul_right_cancel₀ h0 (h1.trans (one_mul _).symm)`.

Establish `hSBind : ∀ c, SB (ind c)`. Introduce `c`. Apply `hSB` to reduce the goal to its premises. Introduce `t ht`. Assume the negation of the conclusion as `hmem`.

Conclude with `ht (by rw [hind, dif_neg hmem])`. Introduce `t u hu`. Establish `hnu : Fintype.card G • u ∈ Λc` using `Λc.nsmul_mem hu _`. Distinguish the cases in `ht : t ∈ Λc`. Establish `ht' : t + Fintype.card G • u ∈ Λc` using `Λc.add_mem ht hnu`.

Establish `he : red ⟨t + Fintype.card G • u, ht'⟩ = red ⟨t, ht⟩`. Establish `: (⟨t + Fintype.card G • u, ht'⟩ : Λc) = ⟨t, ht⟩ + Fintype.card G • ⟨u, hu⟩` using `Subtype.ext (by simp)`. Rewrite using `[this, map_add, map_nsmul, card_nsmul_eq_zero, add_zero]`. Rewrite using `[hind, hind, dif_pos ht, dif_pos ht', he]`. Establish `ht' : t + Fintype.card G • u ∉ Λc` using `fun h => ht (by simpa using Λc.sub_mem h hnu)`.

Rewrite using `[hind, hind, dif_neg ht, dif_neg ht']`. Establish `hmodg : ∀ y, Hd y → (∀ k : Λc, red k = 0 → ψ (B k y) = 1) → ∀ c, hs y (g c) = χ y c • g c`. Introduce `y hHd hy c`. Rewrite using `[hg, ← hmod (ind c) (hSBind c) y hHd, ← map_smul]`. Use `congr 1`.

Use function extensionality and compare the values at `t`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Rewrite using `[hind]`. Distinguish the cases in `ht : t ∈ Λc`. Rewrite using `[dif_pos ht]`.

Distinguish the cases in `hr : red ⟨t, ht⟩ = c`. Rewrite using `[if_pos hr, mul_one, mul_one, ← hr]`. Conclude with `hχ y hy ⟨t, ht⟩`. Rewrite using `[if_neg hr]`. Simplify using the standard rewrite rules.

Rewrite using `[dif_neg ht]`. Simplify using the standard rewrite rules. Establish `htrg : ∀ c, hs (rep c) (g c) = g 0`. Introduce `c`. Rewrite using `[hg, hg, ← htr (ind c) (hSBind c) (rep c) (rep c).2]`.

Use `congr 1`. Use function extensionality and compare the values at `t`. Rewrite using `[hind, hind]`. Distinguish the cases in `ht : t ∈ Λc`. Establish `ht' : t + (rep c : X) ∈ Λc` using `Λc.add_mem ht (rep c).2`.

Establish `he : red ⟨t + rep c, ht'⟩ = red ⟨t, ht⟩ + c`. Establish `: (⟨t + rep c, ht'⟩ : Λc) = ⟨t, ht⟩ + rep c` using `Subtype.ext (by simp)`. Rewrite using `[this, map_add, hrep]`. Rewrite using `[dif_pos ht, dif_pos ht', he]`. Simplify using the standard rewrite rules.

Establish `ht' : t + (rep c : X) ∉ Λc` using `fun h => ht (by simpa using Λc.sub_mem h (rep c).2)`. Rewrite using `[dif_neg ht, dif_neg ht']`. Establish `hTh0 : Th 0` using `by simpa using hThlin (-1) f₀ f₀ hThf₀ hThf₀`. Establish `hThsmul : ∀ a f, Th f → Th (a • f)` using `fun a f hf => by simpa using hThlin a f 0 hf hTh0`. Establish `hhs0 : ∀ w, hs w 0 = 0` using `fun w => by simpa using hslin w 1 0 0`.

Establish `hThsum : ∀ (a : G → ℂ) (s : Finset G), (∀ c ∈ s, Th (g c)) → Th (∑ c ∈ s, a c • g c)`. Introduce `a s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro _`. Simplify using `using hTh0`.

Consider the case `@insert d s hds ih`. Introduce `h`. Rewrite using `[Finset.sum_insert hds]`. Conclude with `hThlin _ _ _ (h d (Finset.mem_insert_self _ _)) (ih fun c hc => h c (Finset.mem_insert_of_mem hc))`. Establish `hsSum : ∀ w (a : G → ℂ) (s : Finset G), hs w (∑ c ∈ s, a c • g c) = ∑ c ∈ s, a c • hs w (g c)`.

Introduce `w a s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using hhs0 w`. Consider the case `@insert d s hds ih => rw [Finset.sum_insert hds, Finset.sum_insert hds, hslin, ih]`. Establish `hf0sum : f₀ = ∑ c, g c`.

Rewrite using `[← hf₀]`. Simplify using `only [hg]`. Rewrite using `[← map_sum]`. Use `congr 1`. Use function extensionality and compare the values at `t`.

Rewrite using `[Finset.sum_apply]`. Simplify using `only [hind]`. Distinguish the cases in `ht : t ∈ Λc`. Simplify using `[ht]`. Simplify using `[ht]`.

Establish `hΦsum : (T fun t => if h : t ∈ Λc then Gd (red ⟨t, h⟩) else 0) = ∑ c, Gd c • g c`. Simplify using `only [hg, ← map_smul]`. Rewrite using `[← map_sum]`. Use `congr 1`. Use function extensionality and compare the values at `t`.

Rewrite using `[Finset.sum_apply]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, hind]`. Distinguish the cases in `ht : t ∈ Λc`. Simplify using `[ht]`. Simplify using `[ht]`.

Establish `hThg : ∀ c, Th (g c)`. Introduce `c`. Establish `key : ∀ S : Finset G, c ∉ S → ∃ a : G → ℂ, a c = 1 ∧ (∀ e ∈ S, a e = 0) ∧ Th (∑ e, a e • g e)`. Introduce `S`. Proceed by induction on `S using Finset.induction_on with`.

Consider the case `empty => intro _; exact ⟨fun _ => 1, rfl, by simp, by simpa [hf0sum] using hThf₀⟩`. Consider the case `@insert d S hdS ih`. Introduce `hc`. Establish `hcS : c ∉ S` using `fun h => hc (Finset.mem_insert_of_mem h)`. Establish `hcd : c ≠ d` using `fun h => hc (h ▸ Finset.mem_insert_self d S)`.

Take `⟨a, ha1, ha0, hTh⟩` from `ih hcS`. Take `⟨y, hHd, hy, hne⟩` from `hsep c d hcd`. Establish `hk : χ y c - χ y d ≠ 0` using `sub_ne_zero.mpr hne`. Use `⟨fun e => a e * ((χ y e - χ y d) / (χ y c - χ y d)), ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show a c * ((χ y c - χ y d) / (χ y c - χ y d)) = 1`.

Rewrite using `[ha1, one_mul, div_self hk]`. Introduce `e he`. Break down `Finset.mem_insert.mp he with rfl | he` into its components or cases. Simplify using the standard rewrite rules. Simplify using `[ha0 e he]`.

Establish `hrw : ∑ e, (a e * ((χ y e - χ y d) / (χ y c - χ y d))) • g e = (χ y c - χ y d)⁻¹ • hs y (∑ e, a e • g e) + (-(χ y d) / (χ y c - χ y d)) • ∑ e, a e • g e`. Rewrite using `[hsSum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations. Rewrite using `[hmodg y hHd hy e, smul_smul, smul_smul, smul_smul, ← add_smul]`. Use `congr 1`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hrw]`. Conclude with `hThlin _ _ _ (hThhs y _ hTh) (hThsmul _ _ hTh)`. Take `⟨a, ha1, ha0, hTh⟩` from `key (Finset.univ.erase c) (by simp)`.

Establish `: ∑ e, a e • g e = g c`. Rewrite using `[Finset.sum_eq_single c]`. Rewrite using `[ha1, one_smul]`. Introduce `e _ he; rw [ha0 e (by simp [he]), zero_smul]`. Simplify using the standard rewrite rules.

Rewrite `hTh` using `[this]`. Then use the resulting hypothesis. Establish `hip0 : ∀ h, Th h → ip 0 h = 0` using `fun h hh => by simpa using hiplin 1 0 0 h hTh0 hTh0 hh`. Establish `hipsL : ∀ a f h, Th f → Th h → ip (a • f) h = a * ip f h` using `fun a f h hf hh => by`. Simplify `hiplin a f 0 h hf hTh0 hh` using `[hip0 h hh]`. Establish `hipsR : ∀ a f h, Th f → Th h → ip f (a • h) = starRingEnd ℂ a * ip f h` using `fun a f h hf hh => by`.

Rewrite using `[hipconj (a • h) f (hThsmul a h hh) hf, hipsL a h f hh hf, map_mul, ← hipconj h f hh hf]`. Establish `hipsumL : ∀ h, Th h → ∀ (a : G → ℂ) (s : Finset G), ip (∑ c ∈ s, a c • g c) h = ∑ c ∈ s, a c * ip (g c) h`. Introduce `h hh a s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using hip0 h hh`.

Consider the case `@insert d s hds ih`. Rewrite using `[Finset.sum_insert hds, Finset.sum_insert hds, hiplin _ _ _ _ (hThg d) (hThsum a s fun c _ => hThg c) hh, ih]`. Establish `horth : ∀ c d, c ≠ d → ip (g c) (g d) = 0`. Introduce `c d hcd`. Take `⟨y, hHd, hy, hne⟩` from `hsep c d hcd`.

Establish `h1` using `hiphs y (g c) (g d) (hThg c) (hThg d)`. Rewrite `h1` using `[hmodg y hHd hy c, hmodg y hHd hy d, hipsL _ _ _ (hThg c) (hThsmul _ _ (hThg d)), hipsR _ _ _ (hThg c) (hThg d)]`. Establish `hk : χ y c * starRingEnd ℂ (χ y d) ≠ 1`. Introduce `h`. Apply `hne` to reduce the goal to its premises.

Use `congrArg (· * χ y d) h` as an intermediate fact. Simplify using `only [mul_assoc, hχconj y hy d, mul_one, one_mul] at this`. Conclude with `this`. Establish `: (1 - χ y c * starRingEnd ℂ (χ y d)) * ip (g c) (g d) = 0`. Take the linear combination `(-1 : ℂ) * h1`.

Break down `mul_eq_zero.mp this with h | h` into its components or cases. Conclude with `absurd (sub_eq_zero.mp h).symm hk`. Conclude with `h`. Establish `hdiag : ∀ c, ip (g c) (g c) = ip (g 0) (g 0)`. Introduce `c`.

Rewrite using `[← htrg c, hiphs _ _ _ (hThg c) (hThg c)]`. Establish `hgram : ∀ a b : G → ℂ, ip (∑ e, a e • g e) (∑ e, b e • g e) = (∑ e, a e * starRingEnd ℂ (b e)) * ip (g 0) (g 0)`. Introduce `a b`. Establish `hS : Th (∑ e, b e • g e)` using `hThsum b _ fun c _ => hThg c`. Rewrite using `[hipsumL _ hS a Finset.univ, Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations. Rewrite using `[hipconj _ _ hS (hThg e), hipsumL _ (hThg e) b Finset.univ, Finset.sum_eq_single e (fun d _ hde => by rw [horth d e hde, mul_zero]) (by simp), map_mul, hdiag e, ← hipconj _ _ (hThg 0) (hThg 0)]`. Expand and normalize the polynomial expressions, which then agree. Establish `hD : ip (g 0) (g 0) = 1 / (Fintype.card G : ℂ)`. Establish `h1` using `hgram (fun _ => 1) (fun _ => 1)`.

Simplify using `only [one_smul, map_one, mul_one, Finset.sum_const, Finset.card_univ] at h1`. Rewrite `h1` using `[← hf0sum, hip₀]`. Establish `hc : (Fintype.card G : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr Fintype.card_ne_zero`. Rewrite using `[eq_div_iff hc]`. Rewrite using `[h1]`.

Simplify using `[mul_comm]`. Rewrite using `[hΦsum, hgram, hD]`. Establish `hn : ∀ z : ℂ, z * starRingEnd ℂ z = ((‖z‖ ^ 2 : ℝ) : ℂ)` using `fun z => by`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Simplify using `only [hn, Complex.ofReal_sum]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem finite_plancherel_schrodinger_intertwiner :
∀ {X Aψ G : Type} [AddCommGroup X] [AddCommGroup Aψ] [AddCommGroup G] [Fintype G]
  (ψ : AddChar Aψ ℂ) (B : X → X → Aψ) (Λc : AddSubgroup X) (red : Λc →+ G)
  (T : (X → ℂ) →ₗ[ℂ] (X → ℂ)) (hs : X → (X → ℂ) → (X → ℂ)) (SB : (X → ℂ) → Prop) (Hd : X → Prop)
  (Th : (X → ℂ) → Prop) (ip : (X → ℂ) → (X → ℂ) → ℂ) (f₀ : X → ℂ) (Gd : G → ℂ),
  Function.Surjective red →
  (∀ t k y, B (t + k) y = B t y + B k y) →
  (∀ Ψ : X → ℂ, (∀ t, Ψ t ≠ 0 → t ∈ Λc) → (∀ t, ∀ u ∈ Λc, Ψ (t + Fintype.card G • u) = Ψ t) → SB Ψ) →
  (∀ Φ, SB Φ → ∀ x ∈ Λc, T (fun t => Φ (t + x)) = hs x (T Φ)) →
  (∀ Φ, SB Φ → ∀ y, Hd y → T (fun t => ψ (B t y) * Φ t) = hs y (T Φ)) →
  T (fun t => if t ∈ Λc then 1 else 0) = f₀ →
  (∀ x : Λc, red x ≠ 0 → ∃ y, Hd y ∧ (∀ k : Λc, red k = 0 → ψ (B k y) = 1) ∧ ψ (B x y) ≠ 1) →
  (∀ w (a : ℂ) (f₁ f₂ : X → ℂ), hs w (a • f₁ + f₂) = a • hs w f₁ + hs w f₂) →
  (∀ (a : ℂ) f₁ f₂, Th f₁ → Th f₂ → Th (a • f₁ + f₂)) →
  (∀ w f, Th f → Th (hs w f)) →
  (∀ (a : ℂ) f₁ f₂ g, Th f₁ → Th f₂ → Th g → ip (a • f₁ + f₂) g = a * ip f₁ g + ip f₂ g) →
  (∀ f g, Th f → Th g → ip g f = starRingEnd ℂ (ip f g)) →
  (∀ w f₁ f₂, Th f₁ → Th f₂ → ip (hs w f₁) (hs w f₂) = ip f₁ f₂) →
  Th f₀ → ip f₀ f₀ = 1 →
  ip (T fun t => if h : t ∈ Λc then Gd (red ⟨t, h⟩) else 0) (T fun t => if h : t ∈ Λc then Gd (red ⟨t, h⟩) else 0) =
    ((∑ g, ‖Gd g‖ ^ 2 : ℝ) : ℂ) / (Fintype.card G : ℂ) := by
  intro X Aψ G _ _ _ _ ψ B Λc red T hs SB Hd Th ip f₀ Gd hsurj hB hSB htr hmod hf₀ hwit hslin hThlin
    hThhs hiplin hipconj hiphs hThf₀ hip₀
  obtain ⟨rep, hrep⟩ : ∃ rep : G → Λc, ∀ c, red (rep c) = c :=
    ⟨Function.surjInv hsurj, Function.surjInv_eq hsurj⟩
  obtain ⟨ind, hind⟩ : ∃ ind : G → X → ℂ, ∀ c t, ind c t =
      if h : t ∈ Λc then (if red ⟨t, h⟩ = c then (1:ℂ) else 0) else 0 := ⟨_, fun _ _ => rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : G → X → ℂ, ∀ c, g c = T (ind c) := ⟨_, fun _ => rfl⟩
  obtain ⟨χ, hχd⟩ : ∃ χ : X → G → ℂ, ∀ y c, χ y c = ψ (B (rep c) y) := ⟨_, fun _ _ => rfl⟩
  have hB0 : ∀ y, B 0 y = 0 := fun y => by simpa using hB 0 0 y
  have hBn : ∀ (m : ℕ) t y, B (m • t) y = m • B t y := by
    intro m t y
    induction m with
    | zero => simp [hB0]
    | succ m ih => rw [succ_nsmul, hB, ih, succ_nsmul]
  have hχ : ∀ y, (∀ k : Λc, red k = 0 → ψ (B k y) = 1) → ∀ t : Λc, ψ (B t y) = χ y (red t) := by
    intro y hy t
    have hk : red (t - rep (red t)) = 0 := by rw [map_sub, hrep, sub_self]
    have ht : (t : X) = ((t - rep (red t) : Λc) : X) + (rep (red t) : X) := by simp
    rw [ht, hB, AddChar.map_add_eq_mul, hy _ hk, one_mul, hχd]
  have hχpow : ∀ y, (∀ k : Λc, red k = 0 → ψ (B k y) = 1) → ∀ c, χ y c ^ Fintype.card G = 1 := by
    intro y hy c
    rw [hχd, ← AddChar.map_nsmul_eq_pow, ← hBn]
    have := hy (Fintype.card G • rep c) (by rw [map_nsmul, card_nsmul_eq_zero])
    simpa using this
  have hχnorm : ∀ y, (∀ k : Λc, red k = 0 → ψ (B k y) = 1) → ∀ c, ‖χ y c‖ = 1 :=
    fun y hy c => Complex.norm_eq_one_of_pow_eq_one (hχpow y hy c) Fintype.card_ne_zero
  have hχconj : ∀ y, (∀ k : Λc, red k = 0 → ψ (B k y) = 1) → ∀ c,
      starRingEnd ℂ (χ y c) * χ y c = 1 := by
    intro y hy c
    rw [Complex.conj_mul', hχnorm y hy c]; simp
  have hsep : ∀ c d, c ≠ d → ∃ y, Hd y ∧ (∀ k : Λc, red k = 0 → ψ (B k y) = 1) ∧ χ y c ≠ χ y d := by
    intro c d hcd
    obtain ⟨y, hHd, hy, hne⟩ := hwit (rep (c - d)) (by rw [hrep]; exact sub_ne_zero.mpr hcd)
    refine ⟨y, hHd, hy, fun heq => hne ?_⟩
    have h1 := hχ y hy (rep (c - d) + rep d)
    have hr : red (rep (c - d) + rep d) = c := by rw [map_add, hrep, hrep, sub_add_cancel]
    rw [hr, AddSubgroup.coe_add, hB, AddChar.map_add_eq_mul, ← hχd y d, heq] at h1
    have h0 : χ y d ≠ 0 := fun h => by simpa [h] using hχnorm y hy d
    exact mul_right_cancel₀ h0 (h1.trans (one_mul _).symm)
  have hSBind : ∀ c, SB (ind c) := by
    intro c
    apply hSB
    · intro t ht
      by_contra hmem
      exact ht (by rw [hind, dif_neg hmem])
    · intro t u hu
      have hnu : Fintype.card G • u ∈ Λc := Λc.nsmul_mem hu _
      by_cases ht : t ∈ Λc
      · have ht' : t + Fintype.card G • u ∈ Λc := Λc.add_mem ht hnu
        have he : red ⟨t + Fintype.card G • u, ht'⟩ = red ⟨t, ht⟩ := by
          have : (⟨t + Fintype.card G • u, ht'⟩ : Λc) = ⟨t, ht⟩ + Fintype.card G • ⟨u, hu⟩ :=
            Subtype.ext (by simp)
          rw [this, map_add, map_nsmul, card_nsmul_eq_zero, add_zero]
        rw [hind, hind, dif_pos ht, dif_pos ht', he]
      · have ht' : t + Fintype.card G • u ∉ Λc := fun h => ht (by simpa using Λc.sub_mem h hnu)
        rw [hind, hind, dif_neg ht, dif_neg ht']
  have hmodg : ∀ y, Hd y → (∀ k : Λc, red k = 0 → ψ (B k y) = 1) → ∀ c,
      hs y (g c) = χ y c • g c := by
    intro y hHd hy c
    rw [hg, ← hmod (ind c) (hSBind c) y hHd, ← map_smul]
    congr 1
    funext t
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hind]
    by_cases ht : t ∈ Λc
    · rw [dif_pos ht]
      by_cases hr : red ⟨t, ht⟩ = c
      · rw [if_pos hr, mul_one, mul_one, ← hr]; exact hχ y hy ⟨t, ht⟩
      · rw [if_neg hr]; simp
    · rw [dif_neg ht]; simp
  have htrg : ∀ c, hs (rep c) (g c) = g 0 := by
    intro c
    rw [hg, hg, ← htr (ind c) (hSBind c) (rep c) (rep c).2]
    congr 1
    funext t
    rw [hind, hind]
    by_cases ht : t ∈ Λc
    · have ht' : t + (rep c : X) ∈ Λc := Λc.add_mem ht (rep c).2
      have he : red ⟨t + rep c, ht'⟩ = red ⟨t, ht⟩ + c := by
        have : (⟨t + rep c, ht'⟩ : Λc) = ⟨t, ht⟩ + rep c := Subtype.ext (by simp)
        rw [this, map_add, hrep]
      rw [dif_pos ht, dif_pos ht', he]
      simp
    · have ht' : t + (rep c : X) ∉ Λc := fun h => ht (by simpa using Λc.sub_mem h (rep c).2)
      rw [dif_neg ht, dif_neg ht']
  have hTh0 : Th 0 := by simpa using hThlin (-1) f₀ f₀ hThf₀ hThf₀
  have hThsmul : ∀ a f, Th f → Th (a • f) := fun a f hf => by simpa using hThlin a f 0 hf hTh0
  have hhs0 : ∀ w, hs w 0 = 0 := fun w => by simpa using hslin w 1 0 0
  have hThsum : ∀ (a : G → ℂ) (s : Finset G), (∀ c ∈ s, Th (g c)) → Th (∑ c ∈ s, a c • g c) := by
    intro a s
    induction s using Finset.induction_on with
    | empty => intro _; simpa using hTh0
    | @insert d s hds ih =>
      intro h
      rw [Finset.sum_insert hds]
      exact hThlin _ _ _ (h d (Finset.mem_insert_self _ _))
        (ih fun c hc => h c (Finset.mem_insert_of_mem hc))
  have hsSum : ∀ w (a : G → ℂ) (s : Finset G),
      hs w (∑ c ∈ s, a c • g c) = ∑ c ∈ s, a c • hs w (g c) := by
    intro w a s
    induction s using Finset.induction_on with
    | empty => simpa using hhs0 w
    | @insert d s hds ih => rw [Finset.sum_insert hds, Finset.sum_insert hds, hslin, ih]
  have hf0sum : f₀ = ∑ c, g c := by
    rw [← hf₀]
    simp only [hg]
    rw [← map_sum]
    congr 1
    funext t
    rw [Finset.sum_apply]
    simp only [hind]
    by_cases ht : t ∈ Λc
    · simp [ht]
    · simp [ht]
  have hΦsum : (T fun t => if h : t ∈ Λc then Gd (red ⟨t, h⟩) else 0) = ∑ c, Gd c • g c := by
    simp only [hg, ← map_smul]
    rw [← map_sum]
    congr 1
    funext t
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, hind]
    by_cases ht : t ∈ Λc
    · simp [ht]
    · simp [ht]
  have hThg : ∀ c, Th (g c) := by
    intro c
    have key : ∀ S : Finset G, c ∉ S →
        ∃ a : G → ℂ, a c = 1 ∧ (∀ e ∈ S, a e = 0) ∧ Th (∑ e, a e • g e) := by
      intro S
      induction S using Finset.induction_on with
      | empty => intro _; exact ⟨fun _ => 1, rfl, by simp, by simpa [hf0sum] using hThf₀⟩
      | @insert d S hdS ih =>
        intro hc
        have hcS : c ∉ S := fun h => hc (Finset.mem_insert_of_mem h)
        have hcd : c ≠ d := fun h => hc (h ▸ Finset.mem_insert_self d S)
        obtain ⟨a, ha1, ha0, hTh⟩ := ih hcS
        obtain ⟨y, hHd, hy, hne⟩ := hsep c d hcd
        have hk : χ y c - χ y d ≠ 0 := sub_ne_zero.mpr hne
        refine ⟨fun e => a e * ((χ y e - χ y d) / (χ y c - χ y d)), ?_, ?_, ?_⟩
        · show a c * ((χ y c - χ y d) / (χ y c - χ y d)) = 1
          rw [ha1, one_mul, div_self hk]
        · intro e he
          rcases Finset.mem_insert.mp he with rfl | he
          · simp
          · simp [ha0 e he]
        · have hrw : ∑ e, (a e * ((χ y e - χ y d) / (χ y c - χ y d))) • g e =
              (χ y c - χ y d)⁻¹ • hs y (∑ e, a e • g e) +
                (-(χ y d) / (χ y c - χ y d)) • ∑ e, a e • g e := by
            rw [hsSum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun e _ => ?_
            rw [hmodg y hHd hy e, smul_smul, smul_smul, smul_smul, ← add_smul]
            congr 1
            field_simp
            ring
          rw [hrw]
          exact hThlin _ _ _ (hThhs y _ hTh) (hThsmul _ _ hTh)
    obtain ⟨a, ha1, ha0, hTh⟩ := key (Finset.univ.erase c) (by simp)
    have : ∑ e, a e • g e = g c := by
      rw [Finset.sum_eq_single c]
      · rw [ha1, one_smul]
      · intro e _ he; rw [ha0 e (by simp [he]), zero_smul]
      · simp
    rwa [this] at hTh
  have hip0 : ∀ h, Th h → ip 0 h = 0 := fun h hh => by simpa using hiplin 1 0 0 h hTh0 hTh0 hh
  have hipsL : ∀ a f h, Th f → Th h → ip (a • f) h = a * ip f h := fun a f h hf hh => by
    simpa [hip0 h hh] using hiplin a f 0 h hf hTh0 hh
  have hipsR : ∀ a f h, Th f → Th h → ip f (a • h) = starRingEnd ℂ a * ip f h :=
    fun a f h hf hh => by
      rw [hipconj (a • h) f (hThsmul a h hh) hf, hipsL a h f hh hf, map_mul, ← hipconj h f hh hf]
  have hipsumL : ∀ h, Th h → ∀ (a : G → ℂ) (s : Finset G),
      ip (∑ c ∈ s, a c • g c) h = ∑ c ∈ s, a c * ip (g c) h := by
    intro h hh a s
    induction s using Finset.induction_on with
    | empty => simpa using hip0 h hh
    | @insert d s hds ih =>
      rw [Finset.sum_insert hds, Finset.sum_insert hds,
        hiplin _ _ _ _ (hThg d) (hThsum a s fun c _ => hThg c) hh, ih]
  have horth : ∀ c d, c ≠ d → ip (g c) (g d) = 0 := by
    intro c d hcd
    obtain ⟨y, hHd, hy, hne⟩ := hsep c d hcd
    have h1 := hiphs y (g c) (g d) (hThg c) (hThg d)
    rw [hmodg y hHd hy c, hmodg y hHd hy d, hipsL _ _ _ (hThg c) (hThsmul _ _ (hThg d)),
      hipsR _ _ _ (hThg c) (hThg d)] at h1
    have hk : χ y c * starRingEnd ℂ (χ y d) ≠ 1 := by
      intro h
      apply hne
      have := congrArg (· * χ y d) h
      simp only [mul_assoc, hχconj y hy d, mul_one, one_mul] at this
      exact this
    have : (1 - χ y c * starRingEnd ℂ (χ y d)) * ip (g c) (g d) = 0 := by
      linear_combination (-1 : ℂ) * h1
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h).symm hk
    · exact h
  have hdiag : ∀ c, ip (g c) (g c) = ip (g 0) (g 0) := by
    intro c
    rw [← htrg c, hiphs _ _ _ (hThg c) (hThg c)]
  have hgram : ∀ a b : G → ℂ, ip (∑ e, a e • g e) (∑ e, b e • g e) =
      (∑ e, a e * starRingEnd ℂ (b e)) * ip (g 0) (g 0) := by
    intro a b
    have hS : Th (∑ e, b e • g e) := hThsum b _ fun c _ => hThg c
    rw [hipsumL _ hS a Finset.univ, Finset.sum_mul]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hipconj _ _ hS (hThg e), hipsumL _ (hThg e) b Finset.univ,
      Finset.sum_eq_single e (fun d _ hde => by rw [horth d e hde, mul_zero]) (by simp),
      map_mul, hdiag e, ← hipconj _ _ (hThg 0) (hThg 0)]
    ring
  have hD : ip (g 0) (g 0) = 1 / (Fintype.card G : ℂ) := by
    have h1 := hgram (fun _ => 1) (fun _ => 1)
    simp only [one_smul, map_one, mul_one, Finset.sum_const, Finset.card_univ] at h1
    rw [← hf0sum, hip₀] at h1
    have hc : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    rw [eq_div_iff hc]
    rw [h1]; simp [mul_comm]
  rw [hΦsum, hgram, hD]
  have hn : ∀ z : ℂ, z * starRingEnd ℂ z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [hn, Complex.ofReal_sum]
  ring

end GlobalTheory
