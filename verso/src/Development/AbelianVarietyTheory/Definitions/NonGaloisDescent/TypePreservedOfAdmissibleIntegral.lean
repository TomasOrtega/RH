import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleIndexBoundAllPowers
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ReadingAllLemmas

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms
open scoped TensorProduct

namespace GlobalTheory.TwAll.Model

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  {Y : NExp D.R D.host D.what₂ D.LL0 N X} {bkP : Formalism.MainNotions.BlochKatoReduction.Gen.BKPh X}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem zpow_apply' (i : X.Tw) (Q : Finset (PlE D.host)) (k : ℕ) (ψ : X.RCG i Q →* (X.Ok i k)ˣ) (a : ℤ)
    (g : X.RCG i Q) : (ψ ^ a) g = (ψ g) ^ a := rfl

/- English proof (translation)
Introduce `h`. Establish `h1 : IsUnit (X.l i : ℤ)` using `isCoprime_self.1 h.of_mul_left_right`. Establish `h2` using `(X.lPrime i).out.one_lt`. Rewrite `h1` using `[Int.isUnit_iff]`. Use linear arithmetic over natural numbers and integers.
-/
theorem not_coprime_mul (i : X.Tw) (n : ℤ) : ¬ IsCoprime (n * (X.l i : ℤ)) (X.l i : ℤ) := by
  intro h
  have h1 : IsUnit (X.l i : ℤ) := isCoprime_self.1 h.of_mul_left_right
  have h2 := (X.lPrime i).out.one_lt
  rw [Int.isUnit_iff] at h1
  omega

/- English proof (translation)
Introduce `i hi hs e he F hF A0`. Take `⟨Q, k', ψ', h1⟩` from `h i hi hs e he F hF A0`. Conclude with `⟨Q, k', ψ', by simpa using h1 1 isCoprime_one_left⟩`.
-/
theorem admissibleBounds_of_all {N0 : X.Tw → ℕ} (h : admissibleIndexBoundAllPowers Y bkP N0) : TwistingCharacterExistence Y bkP N0 := by
  intro i hi hs e he F hF A0
  obtain ⟨Q, k', ψ', h1⟩ := h i hi hs e he F hF A0
  exact ⟨Q, k', ψ', by simpa using h1 1 isCoprime_one_left⟩

/- English proof (translation)
Introduce `hs e he hF S hS A`. Take `⟨Q, k', ψ', h1⟩` from `h hs e he hF S hS A`. Conclude with `⟨Q, k', ψ', by simpa using h1 1 isCoprime_one_left⟩`.
-/
theorem provedGalois_of_all {E : ExpDat Y} {N0 : X.Tw → ℕ} {i : X.Tw} (h : goodTwistExistsAllCoprimePowers Y bkP E N0 i) : TwistTheoremAtIndex Y bkP E N0 i := by
  intro hs e he hF S hS A
  obtain ⟨Q, k', ψ', h1⟩ := h hs e he hF S hS A
  exact ⟨Q, k', ψ', by simpa using h1 1 isCoprime_one_left⟩

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem provedGaloisAll_iff {E : ExpDat Y} {N0 : X.Tw → ℕ} {i : X.Tw} :
    goodTwistExistsAllCoprimePowers Y bkP E N0 i ↔ GlobalTheory.IndefiniteRowSideFullHecke.LemmaAtAllGoodPlaces.LemmaAllAt Y bkP E N0 i := Iff.rfl

/- English proof (translation)
Introduce `w hw` and use `⟨(h w hw).1, by simpa using (h w hw).2 1 isCoprime_one_left⟩`.
-/
theorem twGoodAt_of_all {D : D7} {C : NChoice D} {I : TwIn D} (h : TwGoodAtAll D C I) : TwGoodAt D C I :=
  fun w hw => ⟨(h w hw).1, by simpa using (h w hw).2 1 isCoprime_one_left⟩

/- English proof (translation)
Apply the tactic sequence `cases b <;> simp [BlochKatoReduction.Gen.psiAt]`.
-/
theorem psiAt_zpow {Γ A : Type} [Group Γ] [CommGroup A] (b : Bool) (ψ : Γ →* A) (a : ℤ) :
    BlochKatoReduction.Gen.psiAt b (ψ ^ a) = BlochKatoReduction.Gen.psiAt b ψ ^ a := by
  cases b <;> simp [BlochKatoReduction.Gen.psiAt]

/- English proof (translation)
Establish `h1` using `(h w hw).2 a ha`. Establish `h2` using `(h w hw).2 (-a) ha.neg_left`. Unfold `TwGoodOne at *`. Use `revert h1 h2`. Apply the tactic sequence `cases b <;> cases C.sd w <;> simp [BlochKatoReduction.Gen.psiAt] <;> tauto`.
-/
theorem twGoodAll_side {D : D7} {C : NChoice D} {I : TwIn D} (h : TwGoodAtAll D C I) (w)
    (hw : D.what₂.muAt w ≠ D.what₂.mu0) (b : Bool) (a : ℤ) (ha : IsCoprime a (D.ntw.l (C.twI w) : ℤ)) :
    TwGoodOne D I (C.twI w) b (C.Q w) (C.k' w) (C.psi' w ^ a) := by
  have h1 := (h w hw).2 a ha
  have h2 := (h w hw).2 (-a) ha.neg_left
  unfold TwGoodOne at *
  revert h1 h2
  cases b <;> cases C.sd w <;> simp [BlochKatoReduction.Gen.psiAt] <;> tauto

variable (T : NTh D.R D.host D.what₂ D.LL0 N X Y)

/- English proof (translation)
Assemble the required witnesses or components as `⟨zero_mem _, fun y => by simpa using hB⟩`.
-/
theorem zero_mem_ball (i : X.Tw) (j : ℕ) (b : Bool) {B : ℝ} (hB : 0 ≤ B) : (0 : Y.Fm i j b) ∈ Ball T i j b B :=
  ⟨zero_mem _, fun y => by simpa using hB⟩

/- English proof (translation)
The claim follows from `T.Bsup_def i j b`.
-/
theorem bsup_eq (i : X.Tw) (j : ℕ) (b : Bool) : Y.Bsup i j b = Submodule.span (X.O i) (Ball T i j b 1) :=
  T.Bsup_def i j b

/- English proof (translation)
Rewrite using `[← map_natCast (algebraMap ℚ_[X.l i] (PadicComplex (X.l i))), norm_algebraMap', Padic.norm_p]`.
-/
theorem norm_l (i : X.Tw) : ‖((X.l i : ℕ) : ℂ_[X.l i])‖ = ((X.l i : ℝ))⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[X.l i] (PadicComplex (X.l i))), norm_algebraMap', Padic.norm_p]

/- English proof (translation)
Rewrite using `[← algebraMap_smul (FractionRing (X.O i))]`. Simplify using the standard rewrite rules.
-/
theorem smul_l_pow (i : X.Tw) (j : ℕ) (b : Bool) (c : ℕ) (f : Y.Fm i j b) :
    ((X.l i : X.O i) ^ c) • f = ((X.l i : FractionRing (X.O i)) ^ c) • f := by
  rw [← algebraMap_smul (FractionRing (X.O i))]
  simp

/- English proof (translation)
Establish `hl : (0 : ℝ) < X.l i` using `by exact_mod_cast (X.lPrime i).out.pos`. Rewrite using `[smul_l_pow]`. Use `⟨T.FmUr_smul i j b _ _ (pow_mem (natCast_mem _ _) _) hf.1, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[T.ev_smul, norm_mul, map_pow, map_natCast, norm_pow, norm_l, inv_pow]`. Rewrite using `[inv_mul_le_iff₀ (by positivity)]`.

Conclude with `hf.2 y`.
-/
theorem l_pow_smul_mem (i : X.Tw) (j : ℕ) (b : Bool) (c : ℕ) (B : ℝ) (f : Y.Fm i j b)
    (hf : f ∈ Ball T i j b ((X.l i : ℝ) ^ c * B)) : ((X.l i : X.O i) ^ c) • f ∈ Ball T i j b B := by
  have hl : (0 : ℝ) < X.l i := by exact_mod_cast (X.lPrime i).out.pos
  rw [smul_l_pow]
  refine ⟨T.FmUr_smul i j b _ _ (pow_mem (natCast_mem _ _) _) hf.1, fun y => ?_⟩
  rw [T.ev_smul, norm_mul, map_pow, map_natCast, norm_pow, norm_l, inv_pow]
  rw [inv_mul_le_iff₀ (by positivity)]
  exact hf.2 y

/- English proof (translation)
Rewrite using `[bsup_eq T]`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx => exact Submodule.subset_span (l_pow_smul_mem T i j b c 1 x (by simpa using hx))`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [smul_add]`.

Conclude with `add_mem hx hy`. Consider the case `smul a x _ hx => rw [smul_comm]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem l_pow_smul_span (i : X.Tw) (j : ℕ) (b : Bool) (c : ℕ) (f : Y.Fm i j b)
    (hf : f ∈ Submodule.span (X.O i) (Ball T i j b ((X.l i : ℝ) ^ c))) :
    ((X.l i : X.O i) ^ c) • f ∈ Y.Bsup i j b := by
  rw [bsup_eq T]
  induction hf using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (l_pow_smul_mem T i j b c 1 x (by simpa using hx))
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Rewrite using `[bsup_eq T, Submodule.map_span, Submodule.span_le]`. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Conclude with `Submodule.subset_span (h i hi j hj b g f hf)`.
-/
theorem bsup_stable_of_gKeeps (h : GKeeps T) (i : X.Tw) (hi : X.NonzeroIndexPlace i) (j : ℕ) (hj : j ∈ Finset.Icc 1 D.R.m)
    (b : Bool) (g) :
    (Y.Bsup i j b).map ((Y.actG i j b g).toLinearMap.restrictScalars (X.O i)) ≤ Y.Bsup i j b := by
  rw [bsup_eq T, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨f, hf, rfl⟩
  exact Submodule.subset_span (h i hi j hj b g f hf)

/- English proof (translation)
Rewrite using `[bsup_eq T, Submodule.map_span, Submodule.span_le]`. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Conclude with `Submodule.subset_span (h i hi j hj b k P hk f hf)`.
-/
theorem bsup_stable_of_hkKeeps (h : HkKeeps T) (i : X.Tw) (hi : X.NonzeroIndexPlace i) (j : ℕ) (hj : j ∈ Finset.Icc 1 D.R.m)
    (b : Bool) (k P) (hk : HkIdx i k P) :
    (Y.Bsup i j b).map (hkO Y i j b k P) ≤ Y.Bsup i j b := by
  rw [bsup_eq T, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨f, hf, rfl⟩
  exact Submodule.subset_span (h i hi j hj b k P hk f hf)

/- English proof (translation)
Introduce `a ha`. Take `⟨c, hc⟩` from `h i hi j hj b a ha`. Use `⟨c, fun Q M h1 h2 h3 h4 => ?_⟩` and prove the remaining obligations. Take `⟨Xi, hXi, hδ⟩` from `hc Q M h1 h2 h3 h4`. Rewrite using `[hXi, Finsupp.sum, Finset.smul_sum]`.

Use `Submodule.sum_mem _ fun δ _ => ?_` and prove the remaining obligations. Establish `hm : ((X.l i : X.O i) ^ c) • Xi δ ∈ Mall Y i j b` using `⟨l_pow_smul_span T i j b c _ (hδ δ).2, ((Fm0 Y i j b).restrictScalars (X.O i)).smul_mem _ (hδ δ).1⟩`. Conclude with `⟨(⟨_, hm⟩ : Mall Y i j b) ⊗ₜ AddMonoidAlgebra.single δ (1 : X.O i), by`. Simplify using `[TensorProduct.smul_tmul']⟩`.
-/
theorem integral_of_univBdd {E : ExpDat Y} (h : UnivBdd T E) (i : X.Tw) (hi : X.NonzeroIndexPlace i) (j : ℕ)
    (hj : j ∈ Finset.Icc 1 D.R.m) (b : Bool) :
    ∀ a ∈ E.Dat0 i j b, ∃ c : ℕ, ∀ Q M, (∀ P ∈ Q, Formalism.BasicNotions.IsSplitPl D.host P) → ClsQ (D := D) Q →
      Disjoint Q (X.S0 i) → Disjoint Q (Y.lev i j b a) →
      ((X.l i : X.O i) ^ c) • Y.thU i j b Q M a ∈ LinearMap.range ((Mall Y i j b).subtype.rTensor _) := by
  intro a ha
  obtain ⟨c, hc⟩ := h i hi j hj b a ha
  refine ⟨c, fun Q M h1 h2 h3 h4 => ?_⟩
  obtain ⟨Xi, hXi, hδ⟩ := hc Q M h1 h2 h3 h4
  rw [hXi, Finsupp.sum, Finset.smul_sum]
  refine Submodule.sum_mem _ fun δ _ => ?_
  have hm : ((X.l i : X.O i) ^ c) • Xi δ ∈ Mall Y i j b :=
    ⟨l_pow_smul_span T i j b c _ (hδ δ).2,
      ((Fm0 Y i j b).restrictScalars (X.O i)).smul_mem _ (hδ δ).1⟩
  exact ⟨(⟨_, hm⟩ : Mall Y i j b) ⊗ₜ AddMonoidAlgebra.single δ (1 : X.O i), by
    simp [TensorProduct.smul_tmul']⟩

/- English proof (translation)
Rewrite using `[eq_top_iff, ← T.FmUr_span i j b, Submodule.span_le]`. Introduce `f hf`. Take `⟨B, hB⟩` from `h i hi j hj b f hf`. Establish `hl : (1 : ℝ) < X.l i` using `by exact_mod_cast (X.lPrime i).out.one_lt`. Take `⟨c, hc⟩` from `pow_unbounded_of_one_lt B hl`.

Establish `h1 : f ∈ Ball T i j b ((X.l i : ℝ) ^ c)` using `⟨hB.1, fun y => (hB.2 y).trans hc.le⟩`. Establish `h2` using `l_pow_smul_span T i j b c f (Submodule.subset_span h1)`. Rewrite `h2` using `[smul_l_pow]`. Establish `hne : ((X.l i : FractionRing (X.O i))) ≠ 0`. Introduce `h0`.

Use `congrArg (T.iC i) h0` as an intermediate fact. Rewrite `this` using `[map_natCast, map_zero]`. Conclude with `(X.lPrime i).out.ne_zero (by exact_mod_cast this)`. Establish `h3` using `(Submodule.span (FractionRing (X.O i)) (Y.Bsup i j b : Set (Y.Fm i j b))).smul_mem (((X.l i : FractionRing (X.O i)) ^ c)⁻¹) (Submodule.subset_span h2)`. Rewrite `h3` using `[smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hne), one_smul]`. Then use the resulting hypothesis.
-/
theorem span_bsup_of_supBdd (h : SupBdd T) (i : X.Tw) (hi : X.NonzeroIndexPlace i) (j : ℕ) (hj : j ∈ Finset.Icc 1 D.R.m)
    (b : Bool) : Submodule.span (FractionRing (X.O i)) (Y.Bsup i j b : Set (Y.Fm i j b)) = ⊤ := by
  rw [eq_top_iff, ← T.FmUr_span i j b, Submodule.span_le]
  intro f hf
  obtain ⟨B, hB⟩ := h i hi j hj b f hf
  have hl : (1 : ℝ) < X.l i := by exact_mod_cast (X.lPrime i).out.one_lt
  obtain ⟨c, hc⟩ := pow_unbounded_of_one_lt B hl
  have h1 : f ∈ Ball T i j b ((X.l i : ℝ) ^ c) := ⟨hB.1, fun y => (hB.2 y).trans hc.le⟩
  have h2 := l_pow_smul_span T i j b c f (Submodule.subset_span h1)
  rw [smul_l_pow] at h2
  have hne : ((X.l i : FractionRing (X.O i))) ≠ 0 := by
    intro h0
    have := congrArg (T.iC i) h0
    rw [map_natCast, map_zero] at this
    exact (X.lPrime i).out.ne_zero (by exact_mod_cast this)
  have h3 := (Submodule.span (FractionRing (X.O i)) (Y.Bsup i j b : Set (Y.Fm i j b))).smul_mem
    (((X.l i : FractionRing (X.O i)) ^ c)⁻¹) (Submodule.subset_span h2)
  rwa [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hne), one_smul] at h3

/- English proof (translation)
Introduce `i hi j hj b` and use `(h i hi j hj b).2.2.2.2.2`.
-/
theorem typePreserved_of_admissibleIntegral {E : ExpDat Y} (h : IsotypicPartsInternalDirectSum Y E) : TypeKept E :=
  fun i hi j hj b => (h i hi j hj b).2.2.2.2.2

/- English proof (translation)
Establish `hadd : ∀ A B : Δ →₀ V, (A + B).sum (fun δ f => f ⊗ₜ[O] AddMonoidAlgebra.single δ (1 : O)) = A.sum (fun δ f => f ⊗ₜ[O] AddMonoidAlgebra.single δ (1 : O)) + B.sum (fun δ f => f ⊗ₜ[O] AddMonoidAlgebra.single δ (1 : O))` using `fun A B => Finsupp.sum_add_index' (fun _ => TensorProduct.zero_tmul _ _) (fun _ _ _ => TensorProduct.add_tmul _ _ _)`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, by simp, by simp⟩`. Consider the case `add x y hx hy`. Take `⟨A, hA, hA'⟩` from `hx`.

Take `⟨B, hB, hB'⟩` from `hy`. Conclude with `⟨A + B, by rw [map_add, hA, hB, hadd], fun δ => add_mem (hA' δ) (hB' δ)⟩`. Consider the case `tmul m p`. Proceed by induction on `p using AddMonoidAlgebra.induction_linear with`. Consider the case `zero => exact ⟨0, by simp, by simp⟩`.

Consider the case `add x y hx hy`. Take `⟨A, hA, hA'⟩` from `hx`. Take `⟨B, hB, hB'⟩` from `hy`. Conclude with `⟨A + B, by rw [TensorProduct.tmul_add, map_add, hA, hB, hadd], fun δ => add_mem (hA' δ) (hB' δ)⟩`. Consider the case `single δ r`.

Use `⟨Finsupp.single δ (r • (m : V)), ?_, fun δ' => ?_⟩` and prove the remaining obligations. Rewrite using `[Finsupp.sum_single_index (by simp), TensorProduct.smul_tmul]`. Simplify using the standard rewrite rules. Rewrite using `[Finsupp.single_apply] split_ifs`. Conclude with `S.smul_mem _ m.2`.

Conclude with `zero_mem _`.
-/
theorem coeffs_of_range {O V Δ : Type} [CommRing O] [AddCommGroup V] [Module O V] [AddCommMonoid Δ]
    (S : Submodule O V) (t : S ⊗[O] AddMonoidAlgebra O Δ) :
    ∃ Xi : Δ →₀ V, S.subtype.rTensor _ t = Xi.sum (fun δ f => f ⊗ₜ[O] AddMonoidAlgebra.single δ (1 : O)) ∧
      ∀ δ, Xi δ ∈ S := by
  classical
  have hadd : ∀ A B : Δ →₀ V, (A + B).sum (fun δ f => f ⊗ₜ[O] AddMonoidAlgebra.single δ (1 : O)) =
      A.sum (fun δ f => f ⊗ₜ[O] AddMonoidAlgebra.single δ (1 : O)) +
        B.sum (fun δ f => f ⊗ₜ[O] AddMonoidAlgebra.single δ (1 : O)) := fun A B =>
    Finsupp.sum_add_index' (fun _ => TensorProduct.zero_tmul _ _) (fun _ _ _ => TensorProduct.add_tmul _ _ _)
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp, by simp⟩
  | add x y hx hy =>
    obtain ⟨A, hA, hA'⟩ := hx
    obtain ⟨B, hB, hB'⟩ := hy
    exact ⟨A + B, by rw [map_add, hA, hB, hadd], fun δ => add_mem (hA' δ) (hB' δ)⟩
  | tmul m p =>
    induction p using AddMonoidAlgebra.induction_linear with
    | zero => exact ⟨0, by simp, by simp⟩
    | add x y hx hy =>
      obtain ⟨A, hA, hA'⟩ := hx
      obtain ⟨B, hB, hB'⟩ := hy
      exact ⟨A + B, by rw [TensorProduct.tmul_add, map_add, hA, hB, hadd], fun δ => add_mem (hA' δ) (hB' δ)⟩
    | single δ r =>
      refine ⟨Finsupp.single δ (r • (m : V)), ?_, fun δ' => ?_⟩
      · rw [Finsupp.sum_single_index (by simp), TensorProduct.smul_tmul]
        simp
      · rw [Finsupp.single_apply]
        split_ifs
        · exact S.smul_mem _ m.2
        · exact zero_mem _

/- English proof (translation)
Introduce `h0`. Use `congrArg (T.iC i) h0` as an intermediate fact. Rewrite `this` using `[map_natCast, map_zero]`. Conclude with `(X.lPrime i).out.ne_zero (by exact_mod_cast this)`.
-/
theorem l_ne_zero (T : NTh D.R D.host D.what₂ D.LL0 N X Y) (i : X.Tw) : ((X.l i : FractionRing (X.O i))) ≠ 0 := by
  intro h0
  have := congrArg (T.iC i) h0
  rw [map_natCast, map_zero] at this
  exact (X.lPrime i).out.ne_zero (by exact_mod_cast this)

/- English proof (translation)
Establish `hl : (0 : ℝ) < X.l i` using `by exact_mod_cast (X.lPrime i).out.pos`. Rewrite `hf` using `[bsup_eq T]`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`. Use `Submodule.subset_span ⟨T.FmUr_smul i j b _ _ (inv_mem (pow_mem (natCast_mem _ _) _)) hx.1, fun y => ?_⟩` and prove the remaining obligations.

Rewrite using `[T.ev_smul, norm_mul, map_inv₀, map_pow, map_natCast, norm_inv, norm_pow, norm_l, inv_pow, inv_inv]`. Conclude with `mul_le_of_le_one_right (by positivity) (hx.2 y)`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `add_mem hx hy`.

Consider the case `smul a x _ hx => rw [smul_comm]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem inv_smul_span (i : X.Tw) (j : ℕ) (b : Bool) (c : ℕ) (f : Y.Fm i j b) (hf : f ∈ Y.Bsup i j b) :
    ((X.l i : FractionRing (X.O i)) ^ c)⁻¹ • f ∈ Submodule.span (X.O i) (Ball T i j b ((X.l i : ℝ) ^ c)) := by
  have hl : (0 : ℝ) < X.l i := by exact_mod_cast (X.lPrime i).out.pos
  rw [bsup_eq T] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    refine Submodule.subset_span ⟨T.FmUr_smul i j b _ _ (inv_mem (pow_mem (natCast_mem _ _) _)) hx.1, fun y => ?_⟩
    rw [T.ev_smul, norm_mul, map_inv₀, map_pow, map_natCast, norm_inv, norm_pow, norm_l, inv_pow, inv_inv]
    exact mul_le_of_le_one_right (by positivity) (hx.2 y)
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Introduce `i hi j hj b a ha`. Take `⟨c, hc⟩` from `(h i hi j hj b).2.2.2.2.1 a ha`. Use `⟨c, fun Q M h1 h2 h3 h4 => ?_⟩` and prove the remaining obligations. Take `⟨t, ht⟩` from `hc Q M h1 h2 h3 h4`. Take `⟨Xi, hXi, hδ⟩` from `coeffs_of_range (Mall Y i j b) t`.

Establish `hne` using `pow_ne_zero c (l_ne_zero T i)`. Use `⟨((X.l i : FractionRing (X.O i)) ^ c)⁻¹ • Xi, ?_, fun δ => ⟨?_, inv_smul_span T i j b c _ (hδ δ).1⟩⟩` and prove the remaining obligations. Establish `e1 : ((X.l i : X.O i) ^ c) • Y.thU i j b Q M a = ((X.l i : FractionRing (X.O i)) ^ c) • Y.thU i j b Q M a`. Rewrite using `[← algebraMap_smul (FractionRing (X.O i))]`. Simplify using the standard rewrite rules.

Establish `e2 : Y.thU i j b Q M a = ((X.l i : FractionRing (X.O i)) ^ c)⁻¹ • Xi.sum (fun δ f => f ⊗ₜ[X.O i] AddMonoidAlgebra.single δ (1 : X.O i))`. Rewrite using `[← hXi, ht, e1, smul_smul, inv_mul_cancel₀ hne, one_smul]`. Rewrite using `[e2, Finsupp.sum_smul_index' (fun _ => by simp), Finsupp.smul_sum]`. Simplify using `[TensorProduct.smul_tmul']`. Conclude with `(Fm0 Y i j b).smul_mem _ (hδ δ).2`.
-/
theorem uniformBound_of_admissibleIntegral {E : ExpDat Y} (h : IsotypicPartsInternalDirectSum Y E) : UnivBdd T E := by
  intro i hi j hj b a ha
  obtain ⟨c, hc⟩ := (h i hi j hj b).2.2.2.2.1 a ha
  refine ⟨c, fun Q M h1 h2 h3 h4 => ?_⟩
  obtain ⟨t, ht⟩ := hc Q M h1 h2 h3 h4
  obtain ⟨Xi, hXi, hδ⟩ := coeffs_of_range (Mall Y i j b) t
  have hne := pow_ne_zero c (l_ne_zero T i)
  refine ⟨((X.l i : FractionRing (X.O i)) ^ c)⁻¹ • Xi, ?_, fun δ => ⟨?_, inv_smul_span T i j b c _ (hδ δ).1⟩⟩
  · have e1 : ((X.l i : X.O i) ^ c) • Y.thU i j b Q M a =
        ((X.l i : FractionRing (X.O i)) ^ c) • Y.thU i j b Q M a := by
      rw [← algebraMap_smul (FractionRing (X.O i))]
      simp
    have e2 : Y.thU i j b Q M a = ((X.l i : FractionRing (X.O i)) ^ c)⁻¹ •
        Xi.sum (fun δ f => f ⊗ₜ[X.O i] AddMonoidAlgebra.single δ (1 : X.O i)) := by
      rw [← hXi, ht, e1, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [e2, Finsupp.sum_smul_index' (fun _ => by simp), Finsupp.smul_sum]
    simp [TensorProduct.smul_tmul']
  · exact (Fm0 Y i j b).smul_mem _ (hδ δ).2

end GlobalTheory.TwAll.Model

end
