import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Formalism.LocalRingCardinality.Lemmas
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRefill
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemLocSub
import Development.AutomorphicArithmetic.OrbitLabellings.EvenAddOrderOfHPOfPowLe

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField

namespace GlobalTheory.EX.Led

open Formalism.MainNotions.G IsDedekindDomain

/- English proof (translation)
Establish `hx` using `s.one_lt_alt`. Establish `hx0 : 0 < s.x` using `by linarith`. Establish `hn : (1 : ℝ) ≤ R.n`. Establish `: 1 ≤ R.n` using `by unfold Ranks.n; exact Nat.succ_le_of_lt (by positivity)`. Conclude with `this` after adjusting the coercions.

Establish `hX : 0 < s.X'` using `Real.exp_pos _`. Establish `ha : 0 < s.a` using `by unfold Scale.a Scale.b; positivity`. Establish `: s.X'' R.n = s.X' * (s.x * R.n)`. Unfold `Scale.X'' Scale.w'' Scale.b'`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[this]`. Conclude with `le_mul_of_one_le_right hX.le (by nlinarith)`.
-/
theorem X'_le_X'' (s : Scale) (R : Ranks) : s.X' ≤ s.X'' R.n := by
  have hx := s.one_lt_alt
  have hx0 : 0 < s.x := by linarith
  have hn : (1 : ℝ) ≤ R.n := by
    have : 1 ≤ R.n := by unfold Ranks.n; exact Nat.succ_le_of_lt (by positivity)
    exact_mod_cast this
  have hX : 0 < s.X' := Real.exp_pos _
  have ha : 0 < s.a := by unfold Scale.a Scale.b; positivity
  have : s.X'' R.n = s.X' * (s.x * R.n) := by
    unfold Scale.X'' Scale.w'' Scale.b'
    field_simp
  rw [this]
  exact le_mul_of_one_le_right hX.le (by nlinarith)

variable {D : D7}

/- English proof (translation)
Assume the negation of the conclusion as `h'`. Apply `h` to reduce the goal to its premises. Unfold `VV`. Rewrite using `[if_neg h']`.
-/
theorem cand_of_VV {L : SizeData₂ D} (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) (h : VV X K a b p ≠ ∅) :
    Cand D L K p ∧ Sig X K a b p ≤ L.sc.x ^ (-L.sc.eps) := by
  by_contra h'
  apply h
  unfold VV
  rw [if_neg h']

/- English proof (translation)
Take `⟨hc, hs⟩` from `cand_of_VV X K _ _ p h`. Establish `hX` using `X'_le_X'' L.sc D.R`. Introduce and unpack `(⟨-, -, h1 | ⟨h1, i, hi, h2⟩ | ⟨-, h1⟩⟩ | h1 | h1 | h1)`. Conclude with `absurd hc.2.2.2.1 (not_le.2 h1)`. Rewrite `h2` using `[abs_le]`.

Conclude with `hc.2.2.2.2 h1 ⟨h1, hc.2.1, i, hi, by linarith [h2.1], by linarith [h2.2]⟩`. Conclude with `absurd hs (not_le.2 h1)`. Combine the linear relations using `[hc.2.1]`. Conclude with `h1 (Or.inl hc.2.2.1)`. Conclude with `HEv.not_isCs (UpperTheory.even_addOrderOf_hP_of_pow_le.2 D L p hc.2.2.2.1) h1`.
-/
theorem not_noGain {L : SizeData₂ D} (X : Inst D L) (K : Consts) (Cr : ℝ) (p : ℕ) (h : VV X K (aL L) (bL L) p ≠ ∅) :
    ¬ NoGain X K Cr p := by
  obtain ⟨hc, hs⟩ := cand_of_VV X K _ _ p h
  have hX := X'_le_X'' L.sc D.R
  rintro (⟨-, -, h1 | ⟨h1, i, hi, h2⟩ | ⟨-, h1⟩⟩ | h1 | h1 | h1)
  · exact absurd hc.2.2.2.1 (not_le.2 h1)
  · rw [abs_le] at h2
    exact hc.2.2.2.2 h1 ⟨h1, hc.2.1, i, hi, by linarith [h2.1], by linarith [h2.2]⟩
  · exact absurd hs (not_le.2 h1)
  · linarith [hc.2.1]
  · exact h1 (Or.inl hc.2.2.1)
  · exact HEv.not_isCs (UpperTheory.even_addOrderOf_hP_of_pow_le.2 D L p hc.2.2.2.1) h1

/- English proof (translation)
Unfold `DV.LocLe InLoc`. Rewrite using `[pow_zero, Ideal.one_eq_top, Submodule.top_smul]`.
-/
theorem locLe_iff {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) : DV.LocLe w 0 A B ↔ ∀ x ∈ A, InLoc w B x := by
  unfold DV.LocLe InLoc
  rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by rwa [one_smul]⟩`.
-/
theorem inLoc_of_mem {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    (w : HeightOneSpectrum (𝓞 K)) (A : Submodule (𝓞 K) V) (x : V) (h : x ∈ A) : InLoc w A x :=
  ⟨1, fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by rwa [one_smul]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨(locLe_iff w A B).2 fun x hx => (h x).1 (inLoc_of_mem w A x hx), (locLe_iff w B A).2 fun x hx => (h x).2 (inLoc_of_mem w B x hx)⟩`.
-/
theorem locEq_of_iff {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) (h : ∀ x, InLoc w A x ↔ InLoc w B x) : DV.LocEq w A B :=
  ⟨(locLe_iff w A B).2 fun x hx => (h x).1 (inLoc_of_mem w A x hx),
    (locLe_iff w B A).2 fun x hx => (h x).2 (inLoc_of_mem w B x hx)⟩

/- English proof (translation)
Use `⟨⟨⟨⟨{x | P x}, fun {x y} => hadd x y⟩, h0⟩, fun c x hx => ?_⟩, fun _ => Iff.rfl, fun t x ht hx => ?_⟩` and prove the remaining obligations. Use `show P (c • x)`. Rewrite using `[← algebraMap_smul K c x]`. Conclude with `hs _ x (w.valuation_le_one c) hx`. Establish `hv : w.valuation K (algebraMap (𝓞 K) K t) = 1` using `(w.valuation_eq_one_iff_notMem).2 ht`.

Establish `ht0 : algebraMap (𝓞 K) K t ≠ 0`. Introduce `h0`. Rewrite `hv` using `[h0, map_zero]`. Conclude with `zero_ne_one hv`. Establish `h1` using `hs (algebraMap (𝓞 K) K t)⁻¹ (t • x) (by rw [map_inv₀, hv, inv_one]) hx`.

Rewrite `h1` using `[← algebraMap_smul K t x, smul_smul, inv_mul_cancel₀ ht0, one_smul]`. Conclude with `h1`.
-/
theorem exists_sub {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (w : HeightOneSpectrum (𝓞 K)) (P : V → Prop) (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y)) (hs : ∀ (a : K) x, w.valuation K a ≤ 1 → P x → P (a • x)) :
    ∃ A : Submodule (𝓞 K) V, (∀ x, x ∈ A ↔ P x) ∧ ∀ (t : 𝓞 K) (x : V), t ∉ w.asIdeal → t • x ∈ A → x ∈ A := by
  refine ⟨⟨⟨⟨{x | P x}, fun {x y} => hadd x y⟩, h0⟩, fun c x hx => ?_⟩, fun _ => Iff.rfl, fun t x ht hx => ?_⟩
  · show P (c • x)
    rw [← algebraMap_smul K c x]
    exact hs _ x (w.valuation_le_one c) hx
  · have hv : w.valuation K (algebraMap (𝓞 K) K t) = 1 := (w.valuation_eq_one_iff_notMem).2 ht
    have ht0 : algebraMap (𝓞 K) K t ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hv
      exact zero_ne_one hv
    have h1 := hs (algebraMap (𝓞 K) K t)⁻¹ (t • x) (by rw [map_inv₀, hv, inv_one]) hx
    rw [← algebraMap_smul K t x, smul_smul, inv_mul_cancel₀ ht0, one_smul] at h1
    exact h1

/- English proof (translation)
Use `exists_sub (D.plEq w) (fun x => c.cmp u w hg (D.nuIn u x) ∈ NP X Y K u w hg) ?_ ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `x y hx hy`. Simplify using `only [map_add]`. Conclude with `Submodule.add_mem _ hx hy`.

Introduce `a x ha hx`. Take `⟨o, ho⟩` from `(c.embW_val u w hg a).1 ha`. Use `show c.cmp u w hg (D.nuIn u (a • x)) ∈ _`. Rewrite using `[map_smul, c.cmp_smul, ← ho, algebraMap_smul]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem exists_served {L : SizeData₂ D} (X : Inst D L) (Y : LatInst D) (K : Consts) (c : LatCmp D) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    ∃ A : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V, (∀ x, x ∈ A ↔ c.cmp u w hg (D.nuIn u x) ∈ NP X Y K u w hg) ∧
      ∀ (t : 𝓞 D.what₂.LL) x, t ∉ (D.plEq w).asIdeal → t • x ∈ A → x ∈ A := by
  refine exists_sub (D.plEq w) (fun x => c.cmp u w hg (D.nuIn u x) ∈ NP X Y K u w hg) ?_ ?_ ?_
  · simp
  · intro x y hx hy
    simp only [map_add]
    exact Submodule.add_mem _ hx hy
  · intro a x ha hx
    obtain ⟨o, ho⟩ := (c.embW_val u w hg a).1 ha
    show c.cmp u w hg (D.nuIn u (a • x)) ∈ _
    rw [map_smul, c.cmp_smul, ← ho, algebraMap_smul]
    exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Use `exists_sub (D.plEq w) (fun x => D.nuIn u x ∈ LT.Nlam D u w) ?_ ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `x y hx hy`. Simplify using `only [map_add]`. Conclude with `Submodule.add_mem _ hx hy`.

Introduce `a x ha hx show D.nuIn u (a • x) ∈ _`. Rewrite using `[map_smul]`. Conclude with `(LT.Nlam D u w).smul_mem (⟨a, (D.val_nonneg_iff w a).2 ha⟩ : intW D.what₂.places w) hx`.
-/
theorem exists_atT (u : D.what₂.Word) (w : D.what₂.places.Pl) :
    ∃ A : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V, (∀ x, x ∈ A ↔ D.nuIn u x ∈ LT.Nlam D u w) ∧
      ∀ (t : 𝓞 D.what₂.LL) x, t ∉ (D.plEq w).asIdeal → t • x ∈ A → x ∈ A := by
  refine exists_sub (D.plEq w) (fun x => D.nuIn u x ∈ LT.Nlam D u w) ?_ ?_ ?_
  · simp
  · intro x y hx hy
    simp only [map_add]
    exact Submodule.add_mem _ hx hy
  · intro a x ha hx
    show D.nuIn u (a • x) ∈ _
    rw [map_smul]
    exact (LT.Nlam D u w).smul_mem (⟨a, (D.val_nonneg_iff w a).2 ha⟩ : intW D.what₂.places w) hx

/- English proof (translation)
Use `choose A1 hA1 hA1s using exists_served X Y K c u`. Use `choose A2 hA2 hA2s using exists_atT (D := D) u`. Set `A : D.what₂.places.Pl → Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V` to `fun w => if hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) then A1 w hg else A2 w`. Set `S : Set D.what₂.places.Pl` to `{w | (GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) ∧ VV X K (aL L) (bL L) (D.what₂.places.resChar w) ≠ ∅) ∨ D.what₂.places.resChar w = (D.mem u).A.T}`. Establish `hng : ∀ w, D.what₂.places.resChar w = (D.mem u).A.T → ¬ GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)` using `fun w h hg => hg.2.2.2.2.2 (h ▸ dvd_rfl)`.

Establish `hSf : S.Finite`. Use `((GlobalTheory.Refill.finite_le D ⌈L.sc.X'⌉₊).union (GlobalTheory.Refill.finite_over D (D.mem u).A.T)).subset ?_` and prove the remaining obligations. Introduce and unpack `w (⟨-, h⟩ | h)`. Use `left`. Establish `h1` using `(cand_of_VV X K _ _ _ h).1.2.1`.

Establish `h2` using `h1.le.trans (Nat.le_ceil _)`. Conclude with `h2` after adjusting the coercions. Conclude with `Or.inr h`. Take `⟨N, hN1, hN2⟩` from `GlobalTheory.EX.Glue.exists_glue D.what₂.LL (D.div.Nu u).V (DV.MramL D u) (D.plEq '' S) (fun v => A (D.plEq.symm v)) (hSf.image _) hfull (by`. Introduce and unpack `_ ⟨w, hw, rfl⟩`.

Simplify using `only [Equiv.symm_apply_apply]`. Break down `hw with ⟨hg, hV⟩ | hw` into its components or cases. Establish `hA : A w = A1 w hg` using `dif_pos hg`. Rewrite using `[hA]`. Take `⟨h1, n, hn, h2⟩` from `hS w hg hV`.

Use `⟨hA1s w hg, n, hn, fun x hx => (hA1 w hg _).2 (h2 x hx), fun x hx => h1 _ ?_⟩` and prove the remaining obligations. Conclude with `(hA1 w hg _).1 (Submodule.smul_of_tower_mem _ n hx)`. Establish `hA : A w = A2 w` using `dif_neg (hng w hw)`. Rewrite using `[hA]`. Take `⟨n, hn, h1, h2⟩` from `hT w hw`.

Conclude with `⟨hA2s w, n, hn, fun x hx => (hA2 w _).2 (h1 x hx), fun x hx => h2 _ ((hA2 w _).1 hx)⟩)`. Establish `e1 : ∀ (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), VV X K (aL L) (bL L) (D.what₂.places.resChar w) ≠ ∅ → ∀ x, InLoc (D.plEq w) N x ↔ c.cmp u w hg (D.nuIn u x) ∈ NP X Y K u w hg`. Introduce `w hg hV x`. Establish `hA : A w = A1 w hg` using `dif_pos hg`. Rewrite using `[hN1 _ ⟨w, Or.inl ⟨hg, hV⟩, rfl⟩, Equiv.symm_apply_apply, hA, hA1]`.

Establish `e2 : ∀ w, w ∉ S → DV.LocEq (D.plEq w) N (DV.MramL D u)` using `fun w hw => locEq_of_iff _ _ _ (hN2 _ (fun h => hw ((D.plEq.injective.mem_set_image).1 h)))`. Use `⟨N, e1, fun w hw x => ?_, fun w hw => ?_, fun w hw hV => e2 w ?_⟩` and prove the remaining obligations. Establish `hA : A w = A2 w` using `dif_neg (hng w hw)`. Rewrite using `[hN1 _ ⟨w, Or.inr hw, rfl⟩, Equiv.symm_apply_apply, hA, hA2]`. Distinguish the cases in `h : w ∈ S`.

Take `⟨hg, hV⟩` from `h.resolve_right hw`. Conclude with `(locLe_iff _ _ _).2 fun x hx => (hS w hg hV).1 x ((e1 w hg hV x).1 (inLoc_of_mem _ _ _ hx))`. Conclude with `(e2 w h).1`. Introduce and unpack `(h | h)`. Conclude with `h.2 hV`.

Conclude with `hw h`.
-/
theorem exists_lat {L : SizeData₂ D} (X : Inst D L) (Y : LatInst D) (K : Consts) (c : LatCmp D) (u : D.what₂.Word)
    (hfull : ∀ x : (D.div.Nu u).V, ∃ n : ℕ, n ≠ 0 ∧ n • x ∈ DV.MramL D u)
    (hT : ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w = (D.mem u).A.T → ∃ n : ℕ, n ≠ 0 ∧
      (∀ x ∈ DV.MramL D u, D.nuIn u (n • x) ∈ LT.Nlam D u w) ∧
      ∀ x, D.nuIn u x ∈ LT.Nlam D u w → InLoc (D.plEq w) (DV.MramL D u) (n • x))
    (hS : ∀ (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
        VV X K (aL L) (bL L) (D.what₂.places.resChar w) ≠ ∅ →
        (∀ x, c.cmp u w hg (D.nuIn u x) ∈ NP X Y K u w hg → InLoc (D.plEq w) (DV.MramL D u) x) ∧
        ∃ n : ℕ, n ≠ 0 ∧ ∀ x ∈ DV.MramL D u, c.cmp u w hg (D.nuIn u (n • x)) ∈ NP X Y K u w hg) :
    ∃ N : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V,
      (∀ (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
        VV X K (aL L) (bL L) (D.what₂.places.resChar w) ≠ ∅ →
        ∀ x, InLoc (D.plEq w) N x ↔ c.cmp u w hg (D.nuIn u x) ∈ NP X Y K u w hg) ∧
      (∀ w : D.what₂.places.Pl, D.what₂.places.resChar w = (D.mem u).A.T →
        ∀ x, InLoc (D.plEq w) N x ↔ D.nuIn u x ∈ LT.Nlam D u w) ∧
      (∀ w : D.what₂.places.Pl, D.what₂.places.resChar w ≠ (D.mem u).A.T → DV.LocLe (D.plEq w) 0 N (DV.MramL D u)) ∧
      ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w ≠ (D.mem u).A.T →
        VV X K (aL L) (bL L) (D.what₂.places.resChar w) = ∅ → DV.LocEq (D.plEq w) N (DV.MramL D u) := by
  classical
  choose A1 hA1 hA1s using exists_served X Y K c u
  choose A2 hA2 hA2s using exists_atT (D := D) u
  let A : D.what₂.places.Pl → Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V := fun w =>
    if hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) then A1 w hg else A2 w
  let S : Set D.what₂.places.Pl := {w | (GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) ∧
    VV X K (aL L) (bL L) (D.what₂.places.resChar w) ≠ ∅) ∨ D.what₂.places.resChar w = (D.mem u).A.T}
  have hng : ∀ w, D.what₂.places.resChar w = (D.mem u).A.T → ¬ GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) :=
    fun w h hg => hg.2.2.2.2.2 (h ▸ dvd_rfl)
  have hSf : S.Finite := by
    refine ((GlobalTheory.Refill.finite_le D ⌈L.sc.X'⌉₊).union (GlobalTheory.Refill.finite_over D (D.mem u).A.T)).subset ?_
    rintro w (⟨-, h⟩ | h)
    · left
      have h1 := (cand_of_VV X K _ _ _ h).1.2.1
      have h2 := h1.le.trans (Nat.le_ceil _)
      exact_mod_cast h2
    · exact Or.inr h
  obtain ⟨N, hN1, hN2⟩ := GlobalTheory.EX.Glue.exists_glue D.what₂.LL (D.div.Nu u).V (DV.MramL D u) (D.plEq '' S)
    (fun v => A (D.plEq.symm v)) (hSf.image _) hfull (by
      rintro _ ⟨w, hw, rfl⟩
      simp only [Equiv.symm_apply_apply]
      rcases hw with ⟨hg, hV⟩ | hw
      · have hA : A w = A1 w hg := dif_pos hg
        rw [hA]
        obtain ⟨h1, n, hn, h2⟩ := hS w hg hV
        refine ⟨hA1s w hg, n, hn, fun x hx => (hA1 w hg _).2 (h2 x hx), fun x hx => h1 _ ?_⟩
        exact (hA1 w hg _).1 (Submodule.smul_of_tower_mem _ n hx)
      · have hA : A w = A2 w := dif_neg (hng w hw)
        rw [hA]
        obtain ⟨n, hn, h1, h2⟩ := hT w hw
        exact ⟨hA2s w, n, hn, fun x hx => (hA2 w _).2 (h1 x hx), fun x hx => h2 _ ((hA2 w _).1 hx)⟩)
  have e1 : ∀ (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
        VV X K (aL L) (bL L) (D.what₂.places.resChar w) ≠ ∅ →
        ∀ x, InLoc (D.plEq w) N x ↔ c.cmp u w hg (D.nuIn u x) ∈ NP X Y K u w hg := by
    intro w hg hV x
    have hA : A w = A1 w hg := dif_pos hg
    rw [hN1 _ ⟨w, Or.inl ⟨hg, hV⟩, rfl⟩, Equiv.symm_apply_apply, hA, hA1]
  have e2 : ∀ w, w ∉ S → DV.LocEq (D.plEq w) N (DV.MramL D u) := fun w hw =>
    locEq_of_iff _ _ _ (hN2 _ (fun h => hw ((D.plEq.injective.mem_set_image).1 h)))
  refine ⟨N, e1, fun w hw x => ?_, fun w hw => ?_, fun w hw hV => e2 w ?_⟩
  · have hA : A w = A2 w := dif_neg (hng w hw)
    rw [hN1 _ ⟨w, Or.inr hw, rfl⟩, Equiv.symm_apply_apply, hA, hA2]
  · by_cases h : w ∈ S
    · obtain ⟨hg, hV⟩ := h.resolve_right hw
      exact (locLe_iff _ _ _).2 fun x hx => (hS w hg hV).1 x ((e1 w hg hV x).1 (inLoc_of_mem _ _ _ hx))
    · exact (e2 w h).1
  · rintro (h | h)
    · exact h.2 hV
    · exact hw h

def setLat (L : SizeData₂ D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) : SizeData₂ D :=
  { L with
    NuLat := N
    lenMN := fun u w => ((DV.lenLoc (D.plEq w) (N u) (DV.MramL D u)).toNat : ℚ) / (D.what₂.places.ramIdx w : ℚ) }

def setInst {L : SizeData₂ D} (X : Inst D L) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) : Inst D (setLat L N) :=
  { X with }

/- English proof (translation)
Introduce `C cD ch s D Y e a b L0 hC hg _ hs hW hV0 hA hw _ hR hL`. Take `⟨L, X, e1, e2, e3, hV, hcan, hep, hkap, hF, hE, hs1, hs2, hfill, hdrop⟩` from `GlobalTheory.Refill.exists_refill C cD ch D L0 Y.errX hC hV0 hA (hs ▸ hw) (X'_le_X'' _ _) hR.fin hR.dgam (hL L0 hs hW hV0).1`. Establish `hWL : WtEq L a b`. Introduce `t t' h`. Rewrite using `[e2, e3]`.

Conclude with `hW t t' h`. Take `⟨htied, heptie, hS⟩` from `(hL L (e1.trans hs) hWL hV).2 X hcan hep hkap hfill`. Use `choose N hN1 hN2 hN3 hN4 using fun u => exists_lat X Y.Gy C.GK Y.cmp u (hR.full u) (hR.atT u) (hS u)`. Establish `hlen : ∀ u w, ∀ l : ℕ, DV.lenLoc (D.plEq w) (N u) (DV.MramL D u) = l → (l : ℝ) = ((setLat L N).lenMN u w : ℝ) * (D.what₂.places.ramIdx w : ℝ)`. Introduce `u w l h`.

Establish `h0 : (D.what₂.places.ramIdx w : ℝ) ≠ 0` using `by exact_mod_cast (D.what₂.places.ramIdx_pos w).ne'`. Use `show _ = ((((DV.lenLoc (D.plEq w) (N u) (DV.MramL D u)).toNat : ℚ) / (D.what₂.places.ramIdx w : ℚ) : ℚ) : ℝ) * _`. Rewrite using `[h, ENat.toNat_natCast]`. Use `push_cast`. Rewrite using `[div_mul_cancel₀ _ h0]`.

Establish `hnu : DV.NuDef D (setLat L N)`. Use `⟨hN3, fun u w hT h => hN4 u w hT ?_, hlen⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hVV`. Break down `h with h | h` into its components or cases. Conclude with `not_noGain X C.GK C.Cr _ hVV ((hdrop _ (D.what₂.places.resChar_prime w)).1 h).1`.

Conclude with `h (Or.inr (cand_of_VV X C.GK _ _ _ hVV).1.2.2.1)`. Take `⟨-, -, -, -, f5, f6, -⟩` from `hC.1`. Use `⟨⟨setLat L N, ⟨setInst X N, Y.Gy, hs1, hs2, hfill, fun w u h1 h2 => LatCmp.lenMN_unserved hnu u w (hN4 u w h2 h1), htied, hdrop⟩, rfl, hnu, ⟨Y.vram, hN1, hN2⟩, hep, heptie, hkap, hN4, ⟨⟨f5.ge, f6.ge, hg⟩, Y.piG_lev, Y.piT_lev, Y.seen, Y.tauOf, Y.dgam, hE⟩, hF⟩, e1.trans hs, hWL, …` and prove the remaining obligations.
-/
theorem exists_ledPart : ∀ (C : FC) (cD ch : ℝ) (s : Scale) (D : D7) (Y : Lay D) (e : Formalism.HC.Frame) (a b : e.A → ℤ) (L0 : SizeData₂ D), Std C → 10 ≤ C.cX.err.g → e = D.R.toFrame → L0.sc = s → WtEq L0 a b → Val C cD ch L0 → HostArith D.host → 1 ≤ s.w'' D.R.n → (∀ u, s.X' ≤ ((D.mem u).A.T : ℝ)) → RecOK s C cD D → LedOK s C cD ch Y a b → ∃ p : LedPart C Y, p.L.sc = s ∧ WtEq p.L a b ∧ Val C cD ch p.L ∧ CanonInst p.ta.Gx := by
  intro C cD ch s D Y e a b L0 hC hg _ hs hW hV0 hA hw _ hR hL
  obtain ⟨L, X, e1, e2, e3, hV, hcan, hep, hkap, hF, hE, hs1, hs2, hfill, hdrop⟩ :=
    GlobalTheory.Refill.exists_refill C cD ch D L0 Y.errX hC hV0 hA (hs ▸ hw) (X'_le_X'' _ _) hR.fin hR.dgam (hL L0 hs hW hV0).1
  have hWL : WtEq L a b := by
    intro t t' h
    rw [e2, e3]
    exact hW t t' h
  obtain ⟨htied, heptie, hS⟩ := (hL L (e1.trans hs) hWL hV).2 X hcan hep hkap hfill
  choose N hN1 hN2 hN3 hN4 using fun u => exists_lat X Y.Gy C.GK Y.cmp u (hR.full u) (hR.atT u) (hS u)
  have hlen : ∀ u w, ∀ l : ℕ, DV.lenLoc (D.plEq w) (N u) (DV.MramL D u) = l →
      (l : ℝ) = ((setLat L N).lenMN u w : ℝ) * (D.what₂.places.ramIdx w : ℝ) := by
    intro u w l h
    have h0 : (D.what₂.places.ramIdx w : ℝ) ≠ 0 := by exact_mod_cast (D.what₂.places.ramIdx_pos w).ne'
    show _ = ((((DV.lenLoc (D.plEq w) (N u) (DV.MramL D u)).toNat : ℚ) / (D.what₂.places.ramIdx w : ℚ) : ℚ) : ℝ) * _
    rw [h, ENat.toNat_natCast]
    push_cast
    rw [div_mul_cancel₀ _ h0]
  have hnu : DV.NuDef D (setLat L N) := by
    refine ⟨hN3, fun u w hT h => hN4 u w hT ?_, hlen⟩
    by_contra hVV
    rcases h with h | h
    · exact not_noGain X C.GK C.Cr _ hVV ((hdrop _ (D.what₂.places.resChar_prime w)).1 h).1
    · exact h (Or.inr (cand_of_VV X C.GK _ _ _ hVV).1.2.2.1)
  obtain ⟨-, -, -, -, f5, f6, -⟩ := hC.1
  refine ⟨⟨setLat L N, ⟨setInst X N, Y.Gy, hs1, hs2, hfill,
      fun w u h1 h2 => LatCmp.lenMN_unserved hnu u w (hN4 u w h2 h1), htied, hdrop⟩, rfl, hnu,
      ⟨Y.vram, hN1, hN2⟩, hep, heptie, hkap, hN4,
      ⟨⟨f5.ge, f6.ge, hg⟩, Y.piG_lev, Y.piT_lev, Y.seen, Y.tauOf, Y.dgam, hE⟩, hF⟩, e1.trans hs, hWL,
    ⟨hV.ranks, hV.host, hV.hc, hV.dlog, hV.Del_eq, hV.eta_eq, hV.La_eq, hV.bT_le, hV.logFiveDepth_eq, hV.Ct_eq, hV.Cc_eq,
      hV.CGam_eq, hV.secondConstant_eq, hV.words, hV.etaF_eq⟩, hcan⟩

end GlobalTheory.EX.Led

end
