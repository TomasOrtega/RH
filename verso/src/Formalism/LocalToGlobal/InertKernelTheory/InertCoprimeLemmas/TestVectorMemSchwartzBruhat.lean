import Formalism.LocalToGlobal.InertKernelTheory.StatementJets
import Formalism.LocalToGlobal.GlobalTheory.GL3.NormNatCoprime
import Formalism.LocalToGlobal.GlobalTheory.GL3.ThirdClauseIntegralCombination
import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkThU
import Formalism.FormalGroupLog.FormalGroupLogProofs.ChainRule

noncomputable section

namespace Formalism.L2.KerInert

namespace JetIntegrality

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

section Good

variable {p : ℕ} [Fact p.Prime] {σ ι : Type*}

/- English proof (translation)
Unfold `IsIntP`. Simplify using the standard rewrite rules.
-/
theorem isPadicIntegral_zero : IsIntP (0 : ℂ_[p]) := by unfold IsIntP; simp

/- English proof (translation)
Unfold `IsIntP`. Simplify using the standard rewrite rules.
-/
theorem isPadicIntegral_one : IsIntP (1 : ℂ_[p]) := by unfold IsIntP; simp

/- English proof (translation)
Unfold `IsIntP at *`. Rewrite using `[norm_neg]` and apply the resulting hypothesis.
-/
theorem isPadicIntegral_neg {x : ℂ_[p]} (h : IsIntP x) : IsIntP (-x) := by unfold IsIntP at *; rwa [norm_neg]

variable (δ : ι → MvPowerSeries σ ℂ_[p] →+ MvPowerSeries σ ℂ_[p])

def Wd (l : List ι) (G : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  l.foldr (fun j H => δ j H) G

def Good (G : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ l : List ι, IsIntP (MvPowerSeries.constantCoeff (Wd δ l G))

/- English proof (translation)
Introduce `G hG l`. Apply `h0` to reduce the goal to its premises. Proceed by induction on `l with`. Consider the case `nil => exact hG`. Consider the case `cons j l ih => exact hd _ ih j`.
-/
theorem good_of_closed (S : Set (MvPowerSeries σ ℂ_[p]))
    (h0 : ∀ G ∈ S, IsIntP (MvPowerSeries.constantCoeff G)) (hd : ∀ G ∈ S, ∀ j, δ j G ∈ S) :
    ∀ G ∈ S, Good δ G := by
  intro G hG l
  apply h0
  induction l with
  | nil => exact hG
  | cons j l ih => exact hd _ ih j

/- English proof (translation)
Introduce `l`. Establish `e : Wd δ l (δ j G) = Wd δ (l ++ [j]) G`. Unfold `Wd`. Rewrite using `[List.foldr_append]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Conclude with `h _`.
-/
theorem good_der {G : MvPowerSeries σ ℂ_[p]} (h : Good δ G) (j : ι) : Good δ (δ j G) := by
  intro l
  have e : Wd δ l (δ j G) = Wd δ (l ++ [j]) G := by
    unfold Wd; rw [List.foldr_append]; rfl
  rw [e]; exact h _

variable {δ}

/- English proof (translation)
Set `S : AddSubgroup (MvPowerSeries σ ℂ_[p])` to `AddSubgroup.closure {H | ∃ F G, Good δ F ∧ Good δ G ∧ H = F * G}`. Use `good_of_closed δ (S : Set _) ?_ ?_ _ (AddSubgroup.subset_closure (show F * G ∈ {H | ∃ F G, Good δ F ∧ Good δ G ∧ H = F * G} from ⟨F, G, hF, hG, rfl⟩))` and prove the remaining obligations. Introduce `H hH`. Proceed by induction on `hH using AddSubgroup.closure_induction with`. Consider the case `mem x hx`.

Take `⟨F, G, hF, hG, rfl⟩` from `hx`. Rewrite using `[map_mul]`. Conclude with `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.isPadicIntegral_mul (hF []) (hG [])`. Consider the case `zero => rw [map_zero]`. Conclude with `isPadicIntegral_zero`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.isPadicIntegral_add hx hy`. Consider the case `neg x _ hx => rw [map_neg]`. Conclude with `isPadicIntegral_neg hx`. Introduce `H hH j`.

Proceed by induction on `hH using AddSubgroup.closure_induction with`. Consider the case `mem x hx`. Take `⟨F, G, hF, hG, rfl⟩` from `hx`. Rewrite using `[hmul]`. Conclude with `S.add_mem (AddSubgroup.subset_closure ⟨_, _, good_der δ hF j, hG, rfl⟩) (AddSubgroup.subset_closure ⟨_, _, hF, good_der δ hG j, rfl⟩)`.

Consider the case `zero => rw [map_zero]`. Conclude with `S.zero_mem`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `S.add_mem hx hy`. Consider the case `neg x _ hx => rw [map_neg]`.

Conclude with `S.neg_mem hx`.
-/
theorem good_mul (hmul : ∀ j F G, δ j (F * G) = δ j F * G + F * δ j G)
    {F G : MvPowerSeries σ ℂ_[p]} (hF : Good δ F) (hG : Good δ G) : Good δ (F * G) := by
  let S : AddSubgroup (MvPowerSeries σ ℂ_[p]) :=
    AddSubgroup.closure {H | ∃ F G, Good δ F ∧ Good δ G ∧ H = F * G}
  refine good_of_closed δ (S : Set _) ?_ ?_ _ (AddSubgroup.subset_closure
    (show F * G ∈ {H | ∃ F G, Good δ F ∧ Good δ G ∧ H = F * G} from ⟨F, G, hF, hG, rfl⟩))
  · intro H hH
    induction hH using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨F, G, hF, hG, rfl⟩ := hx
      rw [map_mul]
      exact Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.isPadicIntegral_mul (hF []) (hG [])
    | zero => rw [map_zero]; exact isPadicIntegral_zero
    | add x y _ _ hx hy => rw [map_add]; exact Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.isPadicIntegral_add hx hy
    | neg x _ hx => rw [map_neg]; exact isPadicIntegral_neg hx
  · intro H hH j
    induction hH using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨F, G, hF, hG, rfl⟩ := hx
      rw [hmul]
      exact S.add_mem (AddSubgroup.subset_closure ⟨_, _, good_der δ hF j, hG, rfl⟩)
        (AddSubgroup.subset_closure ⟨_, _, hF, good_der δ hG j, rfl⟩)
    | zero => rw [map_zero]; exact S.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact S.add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact S.neg_mem hx

/- English proof (translation)
Use `good_of_closed δ {G | G = 1 ∨ G = 0} ?_ ?_ 1 (Or.inl rfl)` and prove the remaining obligations. Introduce and unpack `G (rfl | rfl)`. Rewrite using `[map_one]`. Conclude with `isPadicIntegral_one`. Rewrite using `[map_zero]`.

Conclude with `isPadicIntegral_zero`. Introduce and unpack `G (rfl | rfl) j`. Conclude with `Or.inr (h1 j)`. Conclude with `Or.inr (map_zero _)`.
-/
theorem good_one (h1 : ∀ j, δ j 1 = 0) : Good δ (1 : MvPowerSeries σ ℂ_[p]) := by
  refine good_of_closed δ {G | G = 1 ∨ G = 0} ?_ ?_ 1 (Or.inl rfl)
  · rintro G (rfl | rfl)
    · rw [map_one]; exact isPadicIntegral_one
    · rw [map_zero]; exact isPadicIntegral_zero
  · rintro G (rfl | rfl) j
    · exact Or.inr (h1 j)
    · exact Or.inr (map_zero _)

/- English proof (translation)
The claim follows from `Finset.prod_induction f (Good δ) (fun _ _ ha hb => good_mul hmul ha hb) (good_one h1) h`.
-/
theorem good_prod {α : Type*} (hmul : ∀ j F G, δ j (F * G) = δ j F * G + F * δ j G) (h1 : ∀ j, δ j 1 = 0)
    (s : Finset α) (f : α → MvPowerSeries σ ℂ_[p]) (h : ∀ a ∈ s, Good δ (f a)) : Good δ (∏ a ∈ s, f a) :=
  Finset.prod_induction f (Good δ) (fun _ _ ha hb => good_mul hmul ha hb) (good_one h1) h

/- English proof (translation)
Use `good_of_closed δ {G | IntegralMv G} ?_ (fun G hG j => hint j G hG) G hG` and prove the remaining obligations. Introduce `G hG`. Use `hG 0` as an intermediate fact. Rewrite `this` using `[MvPowerSeries.coeff_zero_eq_constantCoeff_apply]`. Then use the resulting hypothesis.
-/
theorem good_of_integral (hint : ∀ j G, IntegralMv G → IntegralMv (δ j G)) {G : MvPowerSeries σ ℂ_[p]}
    (hG : IntegralMv G) : Good δ G := by
  refine good_of_closed δ {G | IntegralMv G} ?_ (fun G hG j => hint j G hG) G hG
  intro G hG
  have := hG 0
  rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at this

end Good

section Ring

variable {p : ℕ} [Fact p.Prime]

def intR (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    show ‖a * b‖ ≤ 1
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨fun e => ⟨MvPowerSeries.coeff e F, h e⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `e`. Both sides reduce to the same expression.

Introduce and unpack `⟨G, rfl⟩ e`. Rewrite using `[MvPowerSeries.coeff_map]`. Conclude with `(MvPowerSeries.coeff e G).2`.
-/
theorem integral_iff {σ : Type*} (F : MvPowerSeries σ ℂ_[p]) :
    IntegralMv F ↔ ∃ G : MvPowerSeries σ (intR p), MvPowerSeries.map (intR p).subtype G = F := by
  constructor
  · intro h
    refine ⟨fun e => ⟨MvPowerSeries.coeff e F, h e⟩, ?_⟩
    ext e
    rfl
  · rintro ⟨G, rfl⟩ e
    rw [MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff e G).2

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem constantCoeff_lift {σ : Type*} (G : MvPowerSeries σ (intR p)) :
    ((MvPowerSeries.constantCoeff G : intR p) : ℂ_[p]) =
      MvPowerSeries.constantCoeff (MvPowerSeries.map (intR p).subtype G) := by
  rfl

/- English proof (translation)
Use `choose a' ha' using fun i => (integral_iff (a i)).1 (haI i)`. Take `⟨f', rfl⟩` from `(integral_iff f).1 hf`. Establish `h0 : ∀ i, MvPowerSeries.constantCoeff (a' i) = 0`. Introduce `i`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[constantCoeff_lift, ha', ha0]`. Both sides reduce to the same expression. Establish `hs : MvPowerSeries.HasSubst a'` using `MvPowerSeries.hasSubst_of_constantCoeff_zero h0`. Use `(integral_iff _).2 ⟨MvPowerSeries.subst a' f', ?_⟩` and prove the remaining obligations. Rewrite using `[MvPowerSeries.map_subst hs]`.

Simplify using `only [ha']`.
-/
theorem integral_subst {σ τ : Type*} [Finite σ] (a : σ → MvPowerSeries τ ℂ_[p])
    (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (haI : ∀ i, IntegralMv (a i))
    {f : MvPowerSeries σ ℂ_[p]} (hf : IntegralMv f) : IntegralMv (MvPowerSeries.subst a f) := by
  choose a' ha' using fun i => (integral_iff (a i)).1 (haI i)
  obtain ⟨f', rfl⟩ := (integral_iff f).1 hf
  have h0 : ∀ i, MvPowerSeries.constantCoeff (a' i) = 0 := by
    intro i
    apply Subtype.ext
    rw [constantCoeff_lift, ha', ha0]
    rfl
  have hs : MvPowerSeries.HasSubst a' := MvPowerSeries.hasSubst_of_constantCoeff_zero h0
  refine (integral_iff _).2 ⟨MvPowerSeries.subst a' f', ?_⟩
  rw [MvPowerSeries.map_subst hs]
  simp only [ha']

/- English proof (translation)
The claim follows from `isUltrametricDist_iff_forall_norm_natCast_le_one.mp inferInstance n`.
-/
theorem isPadicIntegral_natCast (n : ℕ) : IsIntP (n : ℂ_[p]) :=
  isUltrametricDist_iff_forall_norm_natCast_le_one.mp inferInstance n

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Rewrite using `[PowerSeries.coeff_inv, h1, inv_one]`. Use `split_ifs`.

Conclude with `isPadicIntegral_one`. Use `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.isPadicIntegral_mul (isPadicIntegral_neg isPadicIntegral_one) (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.isPadicIntegral_sum _ _ fun x _ => ?_) split_ifs with hx` and prove the remaining obligations. Conclude with `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.isPadicIntegral_mul (hφ _) (ih _ hx)`. Conclude with `isPadicIntegral_zero`.
-/
theorem int_inv {φ : PowerSeries ℂ_[p]} (h1 : PowerSeries.constantCoeff φ = 1)
    (hφ : ∀ n, IsIntP (PowerSeries.coeff n φ)) : ∀ n, IsIntP (PowerSeries.coeff n φ⁻¹) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [PowerSeries.coeff_inv, h1, inv_one]
    split_ifs
    · exact isPadicIntegral_one
    · refine Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.isPadicIntegral_mul (isPadicIntegral_neg isPadicIntegral_one)
        (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.isPadicIntegral_sum _ _ fun x _ => ?_)
      split_ifs with hx
      · exact Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.isPadicIntegral_mul (hφ _) (ih _ hx)
      · exact isPadicIntegral_zero

/- English proof (translation)
Rewrite using `[PowerSeries.subst_def]`. Use `integral_subst _ (fun _ => MvPowerSeries.constantCoeff_X i) (fun _ n => ?_) (fun n => ?_)` and prove the remaining obligations. Rewrite using `[MvPowerSeries.coeff_X]`. Use `split_ifs`. Conclude with `isPadicIntegral_one`.

Conclude with `isPadicIntegral_zero`. Use `hw (n ())` as an intermediate fact. Establish `e : MvPowerSeries.coeff n (w : MvPowerSeries Unit ℂ_[p]) = PowerSeries.coeff (n ()) w`. Rewrite using `[PowerSeries.coeff_def rfl]`. Rewrite using `[e]`.

Conclude with `this`.
-/
theorem integral_psubstX {r : ℕ} (i : Fin r) {w : PowerSeries ℂ_[p]} (hw : ∀ n, IsIntP (PowerSeries.coeff n w)) :
    IntegralMv (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) w) := by
  rw [PowerSeries.subst_def]
  refine integral_subst _ (fun _ => MvPowerSeries.constantCoeff_X i) (fun _ n => ?_) (fun n => ?_)
  · classical
    rw [MvPowerSeries.coeff_X]
    split_ifs
    · exact isPadicIntegral_one
    · exact isPadicIntegral_zero
  · have := hw (n ())
    have e : MvPowerSeries.coeff n (w : MvPowerSeries Unit ℂ_[p]) = PowerSeries.coeff (n ()) w := by
      rw [PowerSeries.coeff_def rfl]
    rw [e]; exact this

/- English proof (translation)
Introduce `n` and use `by rw [MvPowerSeries.coeff_pderiv] refine Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.isPadicIntegral_mul (hG _) ?_ have := isPadicIntegral_natCast (p := p) (n j + 1) simpa using this`.
-/
theorem integral_pderiv {σ : Type*} (j : σ) {G : MvPowerSeries σ ℂ_[p]} (hG : IntegralMv G) :
    IntegralMv (MvPowerSeries.pderiv ℂ_[p] j G) := fun n => by
  rw [MvPowerSeries.coeff_pderiv]
  refine Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.isPadicIntegral_mul (hG _) ?_
  have := isPadicIntegral_natCast (p := p) (n j + 1)
  simpa using this

/- English proof (translation)
Establish `hs : MvPowerSeries.HasSubst a` using `MvPowerSeries.hasSubst_of_constantCoeff_zero ha`. Rewrite using `[MvPowerSeries.constantCoeff_subst hs, finsum_eq_single _ 0]`. Simplify using `[MvPowerSeries.coeff_zero_eq_constantCoeff_apply]`. Introduce `d hd`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs'⟩ : ∃ s, d s ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hd (Finsupp.ext h)`. Rewrite using `[map_finsuppProd, Finsupp.prod, Finset.prod_eq_zero (i := s) (Finsupp.mem_support_iff.mpr hs')]`. Simplify using the standard rewrite rules.

Rewrite using `[map_pow, ha, zero_pow hs']`.
-/
theorem cc_subst {σ τ : Type*} [Finite σ] {a : σ → MvPowerSeries τ ℂ_[p]}
    (ha : ∀ j, MvPowerSeries.constantCoeff (a j) = 0) (g : MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a g) = MvPowerSeries.constantCoeff g := by
  classical
  have hs : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  rw [MvPowerSeries.constantCoeff_subst hs, finsum_eq_single _ 0]
  · simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  · intro d hd
    obtain ⟨s, hs'⟩ : ∃ s, d s ≠ 0 := by
      by_contra h
      push Not at h
      exact hd (Finsupp.ext h)
    rw [map_finsuppProd, Finsupp.prod, Finset.prod_eq_zero (i := s) (Finsupp.mem_support_iff.mpr hs')]
    · simp
    · rw [map_pow, ha, zero_pow hs']

/- English proof (translation)
Rewrite using `[PowerSeries.subst_def, cc_subst (fun _ => MvPowerSeries.constantCoeff_X i)]`. Both sides reduce to the same expression.
-/
theorem cc_psubstX {r : ℕ} (i : Fin r) (f : PowerSeries ℂ_[p]) :
    MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) f) =
      PowerSeries.constantCoeff f := by
  rw [PowerSeries.subst_def, cc_subst (fun _ => MvPowerSeries.constantCoeff_X i)]
  rfl

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[PowerSeries.coeff_derivative, dX, PowerSeries.coeff_mk]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dX_eq (f : PowerSeries ℂ_[p]) : dX f = PowerSeries.derivative ℂ_[p] f := by
  ext n
  rw [PowerSeries.coeff_derivative, dX, PowerSeries.coeff_mk]
  ring

end Ring

section Deriv

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

variable {p : ℕ} [Fact p.Prime] {r : ℕ}

def dl (c : ℂ_[p]) (w : PowerSeries ℂ_[p]) (j : Fin r) :
    MvPowerSeries (Fin r) ℂ_[p] →+ MvPowerSeries (Fin r) ℂ_[p] where
  toFun G := algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p]) c *
    PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin r) ℂ_[p]) w * MvPowerSeries.pderiv ℂ_[p] j G
  map_zero' := by simp
  map_add' F G := by simp only [map_add]; ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem dl_apply (c : ℂ_[p]) (w : PowerSeries ℂ_[p]) (j : Fin r) (G : MvPowerSeries (Fin r) ℂ_[p]) :
    dl c w j G = algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p]) c *
      PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin r) ℂ_[p]) w * MvPowerSeries.pderiv ℂ_[p] j G := rfl

/- English proof (translation)
Simplify using `only [dl_apply, Derivation.leibniz, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dl_mul (c : ℂ_[p]) (w : PowerSeries ℂ_[p]) (j : Fin r) (F G : MvPowerSeries (Fin r) ℂ_[p]) :
    dl c w j (F * G) = dl c w j F * G + F * dl c w j G := by
  simp only [dl_apply, Derivation.leibniz, smul_eq_mul]; ring

/- English proof (translation)
Rewrite using `[dl_apply, Derivation.map_one_eq_zero, mul_zero]`.
-/
theorem dl_one (c : ℂ_[p]) (w : PowerSeries ℂ_[p]) (j : Fin r) : dl c w j 1 = 0 := by
  rw [dl_apply, Derivation.map_one_eq_zero, mul_zero]

/- English proof (translation)
The claim follows from `RestC.integralMv_mul (RestC.integralMv_mul (RestC.integralMv_C hc) (integral_psubstX j hw)) (integral_pderiv j hG)`.
-/
theorem dl_integral (c : ℂ_[p]) (w : PowerSeries ℂ_[p]) (j : Fin r) (hc : IsIntP c)
    (hw : ∀ n, IsIntP (PowerSeries.coeff n w)) {G : MvPowerSeries (Fin r) ℂ_[p]} (hG : IntegralMv G) :
    IntegralMv (dl c w j G) :=
  RestC.integralMv_mul (RestC.integralMv_mul (RestC.integralMv_C hc) (integral_psubstX j hw)) (integral_pderiv j hG)

/- English proof (translation)
The claim follows from `PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)`.
-/
theorem hsX (i : Fin r) : PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) :=
  PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)

/- English proof (translation)
The claim follows from `PowerSeries.subst_mul (hsX i) f g`.
-/
theorem psubstX_mul (i : Fin r) (f g : PowerSeries ℂ_[p]) :
    PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) (f * g) =
      PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) f *
        PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) g :=
  PowerSeries.subst_mul (hsX i) f g

/- English proof (translation)
Rewrite using `[← PowerSeries.coe_substAlgHom (hsX i), AlgHom.commutes]`.
-/
theorem psubstX_C (i : Fin r) (c : ℂ_[p]) :
    PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) c) =
      algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p]) c := by
  rw [← PowerSeries.coe_substAlgHom (hsX i), AlgHom.commutes]

/- English proof (translation)
Rewrite using `[← PowerSeries.coe_substAlgHom (hsX i), map_one]`.
-/
theorem psubstX_one (i : Fin r) :
    PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) (1 : PowerSeries ℂ_[p]) = 1 := by
  rw [← PowerSeries.coe_substAlgHom (hsX i), map_one]

/- English proof (translation)
Rewrite using `[← PowerSeries.coe_substAlgHom (hsX i), map_zero]`.
-/
theorem psubstX_zero (i : Fin r) :
    PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) (0 : PowerSeries ℂ_[p]) = 0 := by
  rw [← PowerSeries.coe_substAlgHom (hsX i), map_zero]

/- English proof (translation)
Rewrite using `[Formalism.G.LogCR.pderiv_psubst (MvPowerSeries.constantCoeff_X i)]`. Use `split_ifs with hij`. Substitute `hij` using the available equality. Rewrite using `[MvPowerSeries.pderiv_X_self, mul_one]`. Rewrite using `[MvPowerSeries.pderiv_X_of_ne hij, mul_zero]`.
-/
theorem pderiv_psubstX (i j : Fin r) (h : PowerSeries ℂ_[p]) :
    MvPowerSeries.pderiv ℂ_[p] j (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) h) =
      if i = j then PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p])
        (PowerSeries.derivative ℂ_[p] h) else 0 := by
  rw [Formalism.G.LogCR.pderiv_psubst (MvPowerSeries.constantCoeff_X i)]
  split_ifs with hij
  · subst hij; rw [MvPowerSeries.pderiv_X_self, mul_one]
  · rw [MvPowerSeries.pderiv_X_of_ne hij, mul_zero]

/- English proof (translation)
Rewrite using `[dl_apply, pderiv_psubstX]`. Use `split_ifs with hij`. Substitute `hij` using the available equality. Rewrite using `[psubstX_mul, psubstX_mul, psubstX_C, dX_eq]`. Rewrite using `[mul_zero]`.
-/
theorem dl_psubstX (c : ℂ_[p]) (w h : PowerSeries ℂ_[p]) (i j : Fin r) :
    dl c w j (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) h) =
      if i = j then PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p])
        (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) c * w * dX h) else 0 := by
  rw [dl_apply, pderiv_psubstX]
  split_ifs with hij
  · subst hij; rw [psubstX_mul, psubstX_mul, psubstX_C, dX_eq]
  · rw [mul_zero]

/- English proof (translation)
Rewrite using `[dX_eq, map_zero]`.
-/
theorem dX_zero : dX (0 : PowerSeries ℂ_[p]) = 0 := by rw [dX_eq, map_zero]

end Deriv

section Chain

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

variable {D : D7} {N N' r : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
  (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)

/- English proof (translation)
Simplify using `only [RestC.atLogA, map_sum, map_mul]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[RestC.cc_psubst' (MvPowerSeries.constantCoeff_X i) (RestC.cc_flog _ wq), mul_zero]`.
-/
theorem atLogA_cc (k : D.what₂.Tau × Fin N' × Fin N) :
    MvPowerSeries.constantCoeff (RestC.atLogA lam Λ C wq b k) = 0 := by
  simp only [RestC.atLogA, map_sum, map_mul]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [RestC.cc_psubst' (MvPowerSeries.constantCoeff_X i) (RestC.cc_flog _ wq), mul_zero]

/- English proof (translation)
Simplify using `only [RestC.atLogA, map_sum, RestC.pderiv_C_mul, pderiv_psubstX, mul_ite, mul_zero]`. Rewrite using `[Finset.sum_ite_eq' Finset.univ j, if_pos (Finset.mem_univ j)]`.
-/
theorem pderiv_atLogA (j : Fin r) (k : D.what₂.Tau × Fin N' × Fin N) :
    MvPowerSeries.pderiv ℂ_[p] j (RestC.atLogA lam Λ C wq b k) =
      algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p])
        (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * lamC lam (embT D k.1 (b j k.2.1 k.2.2))) *
      PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin r) ℂ_[p])
        (PowerSeries.derivative ℂ_[p] (flog (C • wModel lam Λ) wq)) := by
  simp only [RestC.atLogA, map_sum, RestC.pderiv_C_mul, pderiv_psubstX, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ j, if_pos (Finset.mem_univ j)]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem atLog_def (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    atLog D lam Λ C wq b G = MvPowerSeries.subst (RestC.atLogA lam Λ C wq b) G := rfl

/- English proof (translation)
Establish `ha0` using `atLogA_cc lam Λ C wq b`. Establish `hs` using `RestC.atLogA_hasSubst lam Λ C wq b`. Rewrite using `[atLog_def, atLog_def, dl_apply, Formalism.G.LogCR.pderiv_subst ha0, RestC.der_eq]`. Simplify using `only [pderiv_atLogA]`. Rewrite using `[← MvPowerSeries.coe_substAlgHom hs, map_sum]`.

Simplify using `only [map_mul, AlgHom.commutes]`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `set S := (MvPowerSeries.substAlgHom hs) (MvPowerSeries.pderiv ℂ_[p] k F)`. Use `set cj := lamC lam (embT D k.1 (b j k.2.1 k.2.2))`.

Establish `hprod : PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin r) ℂ_[p]) w * PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin r) ℂ_[p]) (PowerSeries.derivative ℂ_[p] (flog (C • wModel lam Λ) wq)) = 1`. Rewrite using `[← psubstX_mul, ← dX_eq, hw, psubstX_one]`. Establish `hc : algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p]) ((C.u : ℂ_[p]ˣ) : ℂ_[p]) * algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p]) ((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) = 1`. Rewrite using `[← map_mul, Units.mul_inv, map_one]`. Take the linear combination `(S * algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p]) cj * (algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p]) ((C.u : ℂ_[p]ˣ) : ℂ_[p]) * algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p]) ((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]))) * hprod + (S * algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p]) cj) * hc`.
-/
theorem atLog_der (w : PowerSeries ℂ_[p]) (hw : w * dX (flog (C • wModel lam Λ) wq) = 1) (j : Fin r)
    (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    dl ((C.u : ℂ_[p]ˣ) : ℂ_[p]) w j (atLog D lam Λ C wq b F) = atLog D lam Λ C wq b (der D lam (b j) F) := by
  have ha0 := atLogA_cc lam Λ C wq b
  have hs := RestC.atLogA_hasSubst lam Λ C wq b
  rw [atLog_def, atLog_def, dl_apply, Formalism.G.LogCR.pderiv_subst ha0, RestC.der_eq]
  simp only [pderiv_atLogA]
  rw [← MvPowerSeries.coe_substAlgHom hs, map_sum]
  simp only [map_mul, AlgHom.commutes]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  set S := (MvPowerSeries.substAlgHom hs) (MvPowerSeries.pderiv ℂ_[p] k F)
  set cj := lamC lam (embT D k.1 (b j k.2.1 k.2.2))
  have hprod : PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin r) ℂ_[p]) w *
      PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin r) ℂ_[p])
        (PowerSeries.derivative ℂ_[p] (flog (C • wModel lam Λ) wq)) = 1 := by
    rw [← psubstX_mul, ← dX_eq, hw, psubstX_one]
  have hc : algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p]) ((C.u : ℂ_[p]ˣ) : ℂ_[p]) *
      algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p]) ((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  linear_combination (S * algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p]) cj *
      (algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p]) ((C.u : ℂ_[p]ˣ) : ℂ_[p]) *
      algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p]) ((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]))) * hprod +
    (S * algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p]) cj) * hc

def DlB (l : List (Fin r)) (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p] :=
  l.foldr (fun j G => der D lam (b j) G) F

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons j l ih => show dl _ w j (Wd _ l _) = atLog D lam Λ C wq b (der D lam (b j) (DlB lam b l F))`. Rewrite using `[ih, atLog_der lam Λ C wq b w hw]`.
-/
theorem Wd_atLog (w : PowerSeries ℂ_[p]) (hw : w * dX (flog (C • wModel lam Λ) wq) = 1) (l : List (Fin r))
    (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    Wd (dl ((C.u : ℂ_[p]ˣ) : ℂ_[p]) w) l (atLog D lam Λ C wq b F) = atLog D lam Λ C wq b (DlB lam b l F) := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    show dl _ w j (Wd _ l _) = atLog D lam Λ C wq b (der D lam (b j) (DlB lam b l F))
    rw [ih, atLog_der lam Λ C wq b w hw]

/- English proof (translation)
Use `h l` as an intermediate fact. Rewrite `this` using `[Wd_atLog lam Λ C wq b w hw, atLog_def, cc_subst (atLogA_cc lam Λ C wq b)]`. Then use the resulting hypothesis.
-/
theorem goodB_of (w : PowerSeries ℂ_[p]) (hw : w * dX (flog (C • wModel lam Λ) wq) = 1)
    (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p])
    (h : Good (dl ((C.u : ℂ_[p]ˣ) : ℂ_[p]) w) (atLog D lam Λ C wq b F)) (l : List (Fin r)) :
    IsIntP (MvPowerSeries.constantCoeff (DlB lam b l F)) := by
  have := h l
  rwa [Wd_atLog lam Λ C wq b w hw, atLog_def, cc_subst (atLogA_cc lam Λ C wq b)] at this

end Chain

section Lin

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

variable {D : D7} {N N' r : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

/- English proof (translation)
Unfold `lamC`. Rewrite using `[dif_pos (RestC.emb_mem (D := D) τ x)]`. Both sides reduce to the same expression.
-/
theorem lamC_embT' (τ : D.what₂.Tau) (x : D.host.E) :
    lamC lam (embT D τ x) = lam (RestC.embQ (D := D) τ x) := by
  unfold lamC
  rw [dif_pos (RestC.emb_mem (D := D) τ x)]
  rfl

/- English proof (translation)
Rewrite using `[mem_algebraicClosure_iff']`. Conclude with `(Algebra.IsIntegral.isIntegral x).map D.host.φ₀.toRatAlgHom`.
-/
theorem test_vector_mem_schwartz_bruhat (x : D.host.E) : D.host.φ₀ x ∈ Qbar := by
  rw [mem_algebraicClosure_iff']
  exact (Algebra.IsIntegral.isIntegral x).map D.host.φ₀.toRatAlgHom

/- English proof (translation)
Establish `hI : IsIntegral ℤ ((c : D.host.K) : D.host.E)` using `map_isIntegral_int (algebraMap D.host.K D.host.E) (NumberField.RingOfIntegers.isIntegral_coe c)`. Unfold `lamC`. Rewrite using `[dif_pos (test_vector_mem_schwartz_bruhat _)]`. Conclude with `RestC.norm_le_one_of_int (map_isIntegral_int (lam.comp (D.host.φ₀.codRestrict Qbar test_vector_mem_schwartz_bruhat)) hI)`.
-/
theorem isPadicIntegral_lamC_K (c : 𝓞 D.host.K) : IsIntP (lamC lam (D.host.φ₀ ((c : D.host.K) : D.host.E))) := by
  have hI : IsIntegral ℤ ((c : D.host.K) : D.host.E) :=
    map_isIntegral_int (algebraMap D.host.K D.host.E) (NumberField.RingOfIntegers.isIntegral_coe c)
  unfold lamC
  rw [dif_pos (test_vector_mem_schwartz_bruhat _)]
  exact RestC.norm_le_one_of_int (map_isIntegral_int (lam.comp (D.host.φ₀.codRestrict Qbar test_vector_mem_schwartz_bruhat)) hI)

/- English proof (translation)
Take `⟨s, hs, c, hc⟩` from `hb.2.2 y hy`. Establish `hsn : ‖(s : ℂ_[p])‖ = 1` using `RestC.norm_nat_coprime p hs`. Establish `hs0 : (s : ℂ_[p]) ≠ 0`. Introduce `h`. Rewrite `hsn` using `[h, norm_zero]`.

Conclude with `zero_ne_one hsn`. Use `⟨fun i => (s : ℂ_[p])⁻¹ * lamC lam (D.host.φ₀ ((c i : D.host.K) : D.host.E)), fun i => ?_, fun k => ?_⟩` and prove the remaining obligations. Use `RestC.isPadicIntegral_mul ?_ (isPadicIntegral_lamC_K lam (c i))` and prove the remaining obligations. Unfold `IsIntP`. Rewrite using `[norm_inv, hsn, inv_one]`.

Take `⟨τ, a, b'⟩` from `k`. Establish `h1 : (s : D.host.E) * y a b' = ∑ i, ((c i : D.host.K) : D.host.E) * b i a b'`. Use `congrFun (congrFun hc a) b'` as an intermediate fact. Simplify `this` using `[Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]`. Establish `h2` using `congrArg (fun x => lam (RestC.embQ (D := D) τ x)) h1`.

Simplify using `only [map_mul, map_sum, map_natCast] at h2`. Establish `h3 : ∀ i, lamC lam (D.host.φ₀ ((c i : D.host.K) : D.host.E)) = lam (RestC.embQ (D` using `D) τ ((c i : D.host.K) : D.host.E)) := by`. Introduce `i`. Rewrite using `[← FL.embT_K D τ _ (c i : D.host.K).2, lamC_embT']`. Simplify using `only [lamC_embT', h3]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, inv_mul_cancel₀ hs0, one_mul]`. Use `_ = _ := by`. Rewrite using `[h2, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem coef_comb {Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)}
    {b : Fin r → Matrix (Fin N') (Fin N) D.host.E} (hb : LocBasis D p Y b) {y : Matrix (Fin N') (Fin N) D.host.E}
    (hy : y ∈ Y) :
    ∃ α : Fin r → ℂ_[p], (∀ i, IsIntP (α i)) ∧ ∀ k : D.what₂.Tau × Fin N' × Fin N,
      lamC lam (embT D k.1 (y k.2.1 k.2.2)) = ∑ i, α i * lamC lam (embT D k.1 (b i k.2.1 k.2.2)) := by
  obtain ⟨s, hs, c, hc⟩ := hb.2.2 y hy
  have hsn : ‖(s : ℂ_[p])‖ = 1 := RestC.norm_nat_coprime p hs
  have hs0 : (s : ℂ_[p]) ≠ 0 := by
    intro h; rw [h, norm_zero] at hsn; exact zero_ne_one hsn
  refine ⟨fun i => (s : ℂ_[p])⁻¹ * lamC lam (D.host.φ₀ ((c i : D.host.K) : D.host.E)), fun i => ?_, fun k => ?_⟩
  · refine RestC.isPadicIntegral_mul ?_ (isPadicIntegral_lamC_K lam (c i))
    unfold IsIntP; rw [norm_inv, hsn, inv_one]
  · obtain ⟨τ, a, b'⟩ := k
    have h1 : (s : D.host.E) * y a b' = ∑ i, ((c i : D.host.K) : D.host.E) * b i a b' := by
      have := congrFun (congrFun hc a) b'
      simpa [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using this
    have h2 := congrArg (fun x => lam (RestC.embQ (D := D) τ x)) h1
    simp only [map_mul, map_sum, map_natCast] at h2
    have h3 : ∀ i, lamC lam (D.host.φ₀ ((c i : D.host.K) : D.host.E)) =
        lam (RestC.embQ (D := D) τ ((c i : D.host.K) : D.host.E)) := by
      intro i
      rw [← FL.embT_K D τ _ (c i : D.host.K).2, lamC_embT']
    simp only [lamC_embT', h3]
    calc lam (RestC.embQ (D := D) τ (y a b'))
        = (s : ℂ_[p])⁻¹ * ((s : ℂ_[p]) * lam (RestC.embQ (D := D) τ (y a b'))) := by
          rw [← mul_assoc, inv_mul_cancel₀ hs0, one_mul]
      _ = _ := by
          rw [h2, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring

/- English proof (translation)
Simplify using `only [RestC.der_eq, hα, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem der_comb {y : Matrix (Fin N') (Fin N) D.host.E} {b : Fin r → Matrix (Fin N') (Fin N) D.host.E}
    (α : Fin r → ℂ_[p])
    (hα : ∀ k : D.what₂.Tau × Fin N' × Fin N,
      lamC lam (embT D k.1 (y k.2.1 k.2.2)) = ∑ i, α i * lamC lam (embT D k.1 (b i k.2.1 k.2.2)))
    (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    der D lam y G = ∑ i, algebraMap ℂ_[p] (MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) (α i) *
      der D lam (b i) G := by
  simp only [RestC.der_eq, hα, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/- English proof (translation)
Rewrite using `[RestC.der_mul, RestC.der_C, mul_zero, add_zero]`.
-/
theorem der_Cmul (y : Matrix (Fin N') (Fin N) D.host.E) (a : ℂ_[p])
    (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    der D lam y (algebraMap ℂ_[p] _ a * G) = algebraMap ℂ_[p] _ a * der D lam y G := by
  rw [RestC.der_mul, RestC.der_C, mul_zero, add_zero]

variable (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)

def GoodB (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) : Prop :=
  ∀ l : List (Fin r), IsIntP (MvPowerSeries.constantCoeff (DlB lam b l G))

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons j l ih => show der D lam (b j) (DlB lam b l (F + G)) = der D lam (b j) (DlB lam b l F) + der D lam (b j) (DlB lam b l G)`. Rewrite using `[ih, RestC.der_add]`.
-/
theorem DlB_add (l : List (Fin r)) (F G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    DlB lam b l (F + G) = DlB lam b l F + DlB lam b l G := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    show der D lam (b j) (DlB lam b l (F + G)) = der D lam (b j) (DlB lam b l F) + der D lam (b j) (DlB lam b l G)
    rw [ih, RestC.der_add]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons j l ih => show der D lam (b j) (DlB lam b l 0) = 0`. Rewrite using `[ih, RestC.der_zero]`.
-/
theorem DlB_zero (l : List (Fin r)) : DlB lam b l (0 : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) = 0 := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    show der D lam (b j) (DlB lam b l 0) = 0
    rw [ih, RestC.der_zero]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons j l ih => show der D lam (b j) (DlB lam b l _) = _ * der D lam (b j) (DlB lam b l G)`. Rewrite using `[ih, der_Cmul]`.
-/
theorem DlB_Cmul (l : List (Fin r)) (a : ℂ_[p]) (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    DlB lam b l (algebraMap ℂ_[p] _ a * G) = algebraMap ℂ_[p] _ a * DlB lam b l G := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    show der D lam (b j) (DlB lam b l _) = _ * der D lam (b j) (DlB lam b l G)
    rw [ih, der_Cmul]

/- English proof (translation)
Use `Finset.sum_induction _ (GoodB lam b) (fun F G hF hG l => ?_) (fun l => ?_) (fun i _ l => ?_)` and prove the remaining obligations. Rewrite using `[DlB_add, map_add]`. Conclude with `RestC.isPadicIntegral_add (hF l) (hG l)`. Rewrite using `[DlB_zero, map_zero]`. Conclude with `isPadicIntegral_zero`.

Rewrite using `[DlB_Cmul, map_mul]`. Establish `e : MvPowerSeries.constantCoeff (algebraMap ℂ_[p] (MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) (a i)) = a i`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `RestC.isPadicIntegral_mul (ha i) (hG i l)`.
-/
theorem goodB_sum {ι : Type*} (s : Finset ι) (a : ι → ℂ_[p]) (ha : ∀ i, IsIntP (a i))
    (G : ι → MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) (hG : ∀ i, GoodB lam b (G i)) :
    GoodB lam b (∑ i ∈ s, algebraMap ℂ_[p] _ (a i) * G i) := by
  refine Finset.sum_induction _ (GoodB lam b) (fun F G hF hG l => ?_) (fun l => ?_) (fun i _ l => ?_)
  · rw [DlB_add, map_add]; exact RestC.isPadicIntegral_add (hF l) (hG l)
  · rw [DlB_zero, map_zero]; exact isPadicIntegral_zero
  · rw [DlB_Cmul, map_mul]
    have e : MvPowerSeries.constantCoeff (algebraMap ℂ_[p] (MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) (a i))
        = a i := by
      rfl
    rw [e]
    exact RestC.isPadicIntegral_mul (ha i) (hG i l)

/- English proof (translation)
Introduce `l`. Establish `e : DlB lam b l (der D lam (b j) G) = DlB lam b (l ++ [j]) G`. Unfold `DlB`. Rewrite using `[List.foldr_append]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Conclude with `h _`.
-/
theorem goodB_der {G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]} (h : GoodB lam b G) (j : Fin r) :
    GoodB lam b (der D lam (b j) G) := by
  intro l
  have e : DlB lam b l (der D lam (b j) G) = DlB lam b (l ++ [j]) G := by
    unfold DlB; rw [List.foldr_append]; rfl
  rw [e]; exact h _

/- English proof (translation)
Rewrite using `[RestC.jetsInt_iff]`. Introduce `l hl`. Establish `key : GoodB lam b (RestC.Dl lam l F)`. Proceed by induction on `l with`. Consider the case `nil => exact hF`.

Consider the case `cons a t ih`. Rewrite using `[RestC.Dl_cons]`. Establish `ha : a ∈ Y` using `hl a (List.mem_cons_self ..)`. Establish `ht` using `ih fun y hy => hl y (List.mem_cons_of_mem a hy)`. Take `⟨α, hαI, hα⟩` from `coef_comb lam hb ha`.

Rewrite using `[der_comb lam α hα]`. Conclude with `goodB_sum lam b _ α hαI _ fun i => goodB_der lam b ht i`. Conclude with `key []`.
-/
theorem jetsInt_of_goodB {Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)} (hb : LocBasis D p Y b)
    {F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]} (hF : GoodB lam b F) : JetsInt D lam Y F := by
  rw [RestC.jetsInt_iff]
  intro l hl
  have key : GoodB lam b (RestC.Dl lam l F) := by
    induction l with
    | nil => exact hF
    | cons a t ih =>
      rw [RestC.Dl_cons]
      have ha : a ∈ Y := hl a (List.mem_cons_self ..)
      have ht := ih fun y hy => hl y (List.mem_cons_of_mem a hy)
      obtain ⟨α, hαI, hα⟩ := coef_comb lam hb ha
      rw [der_comb lam α hα]
      exact goodB_sum lam b _ α hαI _ fun i => goodB_der lam b ht i
  exact key []

end Lin

section Core

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

/- English proof (translation)
Establish `hwl : (dX (flog (C • wModel lam Λ) wq))⁻¹ * dX (flog (C • wModel lam Λ) wq) = 1` using `PowerSeries.inv_mul_cancel _ (by rw [hl1]; exact one_ne_zero)`. Establish `hwI : ∀ n, IsIntP (PowerSeries.coeff n (dX (flog (C • wModel lam Λ) wq))⁻¹)` using `int_inv hl1 hlI`. Establish `hmul : ∀ j F G, dl (r` using `r) ((C.u : ℂ_[p]ˣ) : ℂ_[p]) (dX (flog (C • wModel lam Λ) wq))⁻¹ j (F * G) = dl ((C.u : ℂ_[p]ˣ) : ℂ_[p]) (dX (flog (C • wModel lam Λ) wq))⁻¹ j F * G + F * dl ((C.u : ℂ_[p]ˣ) : ℂ_[p]) (dX (flog (C • wModel lam Λ) wq))⁻¹ j G := fun j F G => dl_mul _ _ j F G`. Establish `h1 : ∀ j, dl (r` using `r) ((C.u : ℂ_[p]ˣ) : ℂ_[p]) (dX (flog (C • wModel lam Λ) wq))⁻¹ j 1 = 0 := fun j => dl_one _ _ j`. Establish `hprod : atLog D lam Λ C wq b F = (atLog D lam Λ C wq b F * ePh lam Λ C wq r) * ∏ i, PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) (ePhi1 lam Λ C wq)`.

Rewrite using `[ePh, if_neg hp2, mul_assoc, ← Finset.prod_mul_distrib, Finset.prod_eq_one (fun i _ => MvPowerSeries.inv_mul_cancel _ (by rw [cc_psubstX, he1]; exact one_ne_zero)), mul_one]`. Establish `hgV : Good (dl ((C.u : ℂ_[p]ˣ) : ℂ_[p]) (dX (flog (C • wModel lam Λ) wq))⁻¹) (atLog D lam Λ C wq b F * ePh lam Λ C wq r)` using `good_of_integral (fun j G hG => dl_integral _ _ j hu hwI hG) hV`. Establish `hgE : ∀ i : Fin r, Good (dl ((C.u : ℂ_[p]ˣ) : ℂ_[p]) (dX (flog (C • wModel lam Λ) wq))⁻¹) (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) (ePhi1 lam Λ C wq))`. Introduce `i`. Use `set T := dYu C (C • wModel lam Λ) wq with hT`.

Establish `hT0 : T 0 = 0` using `by rw [hT, dYu, dX_zero, mul_zero]`. Use `good_of_closed _ {G | ∃ h : PowerSeries ℂ_[p], (∀ n, IsIntP (PowerSeries.constantCoeff (T^[n] h))) ∧ G = PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) h} ?_ ?_ _ ⟨_, heJ, rfl⟩` and prove the remaining obligations. Introduce and unpack `G ⟨h, hh, rfl⟩`. Rewrite using `[cc_psubstX]`. Conclude with `hh 0`.

Introduce and unpack `G ⟨h, hh, rfl⟩ j`. Rewrite using `[dl_psubstX]`. Use `split_ifs with hij`. Conclude with `⟨T h, fun n => by rw [← Function.iterate_succ_apply]; exact hh (n + 1), rfl⟩`. Use `⟨0, fun n => ?_, (psubstX_zero i).symm⟩` and prove the remaining obligations.

Rewrite using `[Function.iterate_fixed hT0, map_zero]`. Conclude with `isPadicIntegral_zero`. Establish `hgP` using `good_prod hmul h1 Finset.univ _ (fun i _ => hgE i)`. Establish `hgA : Good (dl ((C.u : ℂ_[p]ˣ) : ℂ_[p]) (dX (flog (C • wModel lam Λ) wq))⁻¹) (atLog D lam Λ C wq b F)`. Rewrite using `[hprod]`.

Conclude with `good_mul hmul hgV hgP`. Conclude with `jetsInt_of_goodB lam b hb (goodB_of lam Λ C wq b _ hwl F hgA)`.
-/
theorem jets_core {D : D7} {N N' : ℕ} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (lam : Qbar →+* ℂ_[p])
    (Λ : AddSubgroup ℂ) (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]) {r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E))
    (hb : LocBasis D p Y b) (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p])
    (hu : IsIntP ((C.u : ℂ_[p]ˣ) : ℂ_[p]))
    (hl1 : PowerSeries.constantCoeff (dX (flog (C • wModel lam Λ) wq)) = 1)
    (hlI : ∀ n, IsIntP (PowerSeries.coeff n (dX (flog (C • wModel lam Λ) wq))))
    (he1 : PowerSeries.constantCoeff (ePhi1 lam Λ C wq) = 1)
    (heJ : ∀ n, IsIntP (PowerSeries.constantCoeff ((dYu C (C • wModel lam Λ) wq)^[n] (ePhi1 lam Λ C wq))))
    (hV : IntegralMv (atLog D lam Λ C wq b F * ePh lam Λ C wq r)) : JetsInt D lam Y F := by
  have hwl : (dX (flog (C • wModel lam Λ) wq))⁻¹ * dX (flog (C • wModel lam Λ) wq) = 1 :=
    PowerSeries.inv_mul_cancel _ (by rw [hl1]; exact one_ne_zero)
  have hwI : ∀ n, IsIntP (PowerSeries.coeff n (dX (flog (C • wModel lam Λ) wq))⁻¹) := int_inv hl1 hlI
  have hmul : ∀ j F G, dl (r := r) ((C.u : ℂ_[p]ˣ) : ℂ_[p]) (dX (flog (C • wModel lam Λ) wq))⁻¹ j (F * G) =
      dl ((C.u : ℂ_[p]ˣ) : ℂ_[p]) (dX (flog (C • wModel lam Λ) wq))⁻¹ j F * G +
        F * dl ((C.u : ℂ_[p]ˣ) : ℂ_[p]) (dX (flog (C • wModel lam Λ) wq))⁻¹ j G :=
    fun j F G => dl_mul _ _ j F G
  have h1 : ∀ j, dl (r := r) ((C.u : ℂ_[p]ˣ) : ℂ_[p]) (dX (flog (C • wModel lam Λ) wq))⁻¹ j 1 = 0 :=
    fun j => dl_one _ _ j
  have hprod : atLog D lam Λ C wq b F = (atLog D lam Λ C wq b F * ePh lam Λ C wq r) *
      ∏ i, PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) (ePhi1 lam Λ C wq) := by
    rw [ePh, if_neg hp2, mul_assoc, ← Finset.prod_mul_distrib,
      Finset.prod_eq_one (fun i _ => MvPowerSeries.inv_mul_cancel _ (by rw [cc_psubstX, he1]; exact one_ne_zero)),
      mul_one]
  have hgV : Good (dl ((C.u : ℂ_[p]ˣ) : ℂ_[p]) (dX (flog (C • wModel lam Λ) wq))⁻¹)
      (atLog D lam Λ C wq b F * ePh lam Λ C wq r) :=
    good_of_integral (fun j G hG => dl_integral _ _ j hu hwI hG) hV
  have hgE : ∀ i : Fin r, Good (dl ((C.u : ℂ_[p]ˣ) : ℂ_[p]) (dX (flog (C • wModel lam Λ) wq))⁻¹)
      (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) (ePhi1 lam Λ C wq)) := by
    intro i
    set T := dYu C (C • wModel lam Λ) wq with hT
    have hT0 : T 0 = 0 := by rw [hT, dYu, dX_zero, mul_zero]
    refine good_of_closed _ {G | ∃ h : PowerSeries ℂ_[p], (∀ n, IsIntP (PowerSeries.constantCoeff (T^[n] h))) ∧
        G = PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) h} ?_ ?_ _ ⟨_, heJ, rfl⟩
    · rintro G ⟨h, hh, rfl⟩
      rw [cc_psubstX]
      exact hh 0
    · rintro G ⟨h, hh, rfl⟩ j
      rw [dl_psubstX]
      split_ifs with hij
      · exact ⟨T h, fun n => by rw [← Function.iterate_succ_apply]; exact hh (n + 1), rfl⟩
      · refine ⟨0, fun n => ?_, (psubstX_zero i).symm⟩
        rw [Function.iterate_fixed hT0, map_zero]
        exact isPadicIntegral_zero
  have hgP := good_prod hmul h1 Finset.univ _ (fun i _ => hgE i)
  have hgA : Good (dl ((C.u : ℂ_[p]ˣ) : ℂ_[p]) (dX (flog (C • wModel lam Λ) wq))⁻¹) (atLog D lam Λ C wq b F) := by
    rw [hprod]; exact good_mul hmul hgV hgP
  exact jetsInt_of_goodB lam b hb (goodB_of lam Λ C wq b _ hwl F hgA)

end Core

section Log

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Establish `hu : IsIntP (PowerSeries.constantCoeff φ)⁻¹` using `by unfold IsIntP; rw [norm_inv, h1, inv_one]`. Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Rewrite using `[PowerSeries.coeff_inv]`.

Use `split_ifs`. Conclude with `hu`. Use `RestC.isPadicIntegral_mul (isPadicIntegral_neg hu) (RestC.isPadicIntegral_sum _ _ fun x _ => ?_) split_ifs with hx` and prove the remaining obligations. Conclude with `RestC.isPadicIntegral_mul (hφ _) (ih _ hx)`. Conclude with `isPadicIntegral_zero`.
-/
theorem int_inv' {φ : PowerSeries ℂ_[p]} (h1 : ‖PowerSeries.constantCoeff φ‖ = 1)
    (hφ : ∀ n, IsIntP (PowerSeries.coeff n φ)) : ∀ n, IsIntP (PowerSeries.coeff n φ⁻¹) := by
  have hu : IsIntP (PowerSeries.constantCoeff φ)⁻¹ := by unfold IsIntP; rw [norm_inv, h1, inv_one]
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [PowerSeries.coeff_inv]
    split_ifs
    · exact hu
    · refine RestC.isPadicIntegral_mul (isPadicIntegral_neg hu) (RestC.isPadicIntegral_sum _ _ fun x _ => ?_)
      split_ifs with hx
      · exact RestC.isPadicIntegral_mul (hφ _) (ih _ hx)
      · exact isPadicIntegral_zero

/- English proof (translation)
Rewrite using `[PowerSeries.coeff_mul]`. Use `RestC.isPadicIntegral_sum _ _ fun x hx => ?_` and prove the remaining obligations. Establish `hx'` using `Finset.HasAntidiagonal.mem_antidiagonal.mp hx`. Conclude with `RestC.isPadicIntegral_mul (hf _ (by omega)) (hg _ (by omega))`.
-/
theorem coeff_mul_int {f g : PowerSeries ℂ_[p]} {m : ℕ} (hf : ∀ i ≤ m, IsIntP (PowerSeries.coeff i f))
    (hg : ∀ i ≤ m, IsIntP (PowerSeries.coeff i g)) : IsIntP (PowerSeries.coeff m (f * g)) := by
  rw [PowerSeries.coeff_mul]
  refine RestC.isPadicIntegral_sum _ _ fun x hx => ?_
  have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  exact RestC.isPadicIntegral_mul (hf _ (by omega)) (hg _ (by omega))

/- English proof (translation)
Rewrite using `[mul_assoc, ← Algebra.smul_def, map_smul, PowerSeries.coeff_X_pow_mul', smul_eq_mul]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem coeff_smul_Xpow (a : ℂ_[p]) (k n : ℕ) (P : PowerSeries ℂ_[p]) :
    PowerSeries.coeff n (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a * PowerSeries.X ^ k * P) =
      if k ≤ n then a * PowerSeries.coeff (n - k) P else 0 := by
  rw [mul_assoc, ← Algebra.smul_def, map_smul, PowerSeries.coeff_X_pow_mul', smul_eq_mul]
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[coeff_smul_Xpow]`. Use `split_ifs with h`. Conclude with `RestC.isPadicIntegral_mul ha (hP _ (by omega))`. Conclude with `isPadicIntegral_zero`.
-/
theorem term_int {a : ℂ_[p]} (ha : IsIntP a) {k n : ℕ} (hk : 1 ≤ k) {P : PowerSeries ℂ_[p]}
    (hP : ∀ i < n, IsIntP (PowerSeries.coeff i P)) :
    IsIntP (PowerSeries.coeff n (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a * PowerSeries.X ^ k * P)) := by
  rw [coeff_smul_Xpow]
  split_ifs with h
  · exact RestC.isPadicIntegral_mul ha (hP _ (by omega))
  · exact isPadicIntegral_zero

/- English proof (translation)
Rewrite using `[coeff_smul_Xpow, if_neg (by omega)]`.
-/
theorem term_zero (a : ℂ_[p]) {k : ℕ} (hk : 1 ≤ k) (P : PowerSeries ℂ_[p]) :
    PowerSeries.coeff 0 (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a * PowerSeries.X ^ k * P) = 0 := by
  rw [coeff_smul_Xpow, if_neg (by omega)]

/- English proof (translation)
Establish `e : wq = 1 + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * PowerSeries.X ^ 1 * wq + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₂ * PowerSeries.X ^ 2 * wq + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * PowerSeries.X ^ 3 * wq ^ 2 + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₄ * PowerSeries. …`. Rewrite using `[pow_one]`. Conclude with `hw`. Establish `hall : ∀ n, ∀ i < n, IsIntP (PowerSeries.coeff i wq)`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => intro i hi`. Use linear arithmetic over natural numbers and integers. Consider the case `succ n ih`. Introduce `i hi`.

Break down `Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl` into its components or cases. Conclude with `ih i hi`. Establish `h2' : ∀ j < i, IsIntP (PowerSeries.coeff j (wq ^ 2))` using `fun j hj => by`. Rewrite using `[pow_two]; exact coeff_mul_int (fun k hk => ih k (by omega)) (fun k hk => ih k (by omega))`. Establish `h3' : ∀ j < i, IsIntP (PowerSeries.coeff j (wq ^ 3))` using `fun j hj => by`.

Rewrite using `[pow_succ]`. Conclude with `coeff_mul_int (fun k hk => h2' k (by omega)) (fun k hk => ih k (by omega))`. Rewrite using `[e]`. Simplify using `only [map_add]`. Use `RestC.isPadicIntegral_add (RestC.isPadicIntegral_add (RestC.isPadicIntegral_add (RestC.isPadicIntegral_add (RestC.isPadicIntegral_add ?_ (term_int h1 le_rfl ih)) (term_int h2 (by norm_num) ih)) (term_int h3 (by norm_num) h2')) (term_int h4 (by norm_num) h2')) (term_int h6 (by nor …` and prove the remaining obligations.

Rewrite using `[PowerSeries.coeff_one]`. Use `split_ifs`. Conclude with `isPadicIntegral_one`. Conclude with `isPadicIntegral_zero`. Use `⟨fun n => hall (n + 1) n (by omega), ?_⟩` and prove the remaining obligations.

Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, e]`. Simplify using `only [map_add, term_zero _ le_rfl, term_zero _ (show 1 ≤ 2 by norm_num), term_zero _ (show 1 ≤ 3 by norm_num), term_zero _ (show 1 ≤ 4 by norm_num), term_zero _ (show 1 ≤ 6 by norm_num), add_zero]`. Simplify using the standard rewrite rules.
-/
theorem wq_int (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p])
    (h1 : IsIntP W.a₁) (h2 : IsIntP W.a₂) (h3 : IsIntP W.a₃) (h4 : IsIntP W.a₄) (h6 : IsIntP W.a₆)
    (hw : IsWq W wq) : (∀ n, IsIntP (PowerSeries.coeff n wq)) ∧ PowerSeries.constantCoeff wq = 1 := by
  have e : wq = 1 + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * PowerSeries.X ^ 1 * wq +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₂ * PowerSeries.X ^ 2 * wq +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * PowerSeries.X ^ 3 * wq ^ 2 +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₄ * PowerSeries.X ^ 4 * wq ^ 2 +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₆ * PowerSeries.X ^ 6 * wq ^ 3 := by
    rw [pow_one]; exact hw
  have hall : ∀ n, ∀ i < n, IsIntP (PowerSeries.coeff i wq) := by
    intro n
    induction n with
    | zero => intro i hi; omega
    | succ n ih =>
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact ih i hi
      · have h2' : ∀ j < i, IsIntP (PowerSeries.coeff j (wq ^ 2)) := fun j hj => by
          rw [pow_two]; exact coeff_mul_int (fun k hk => ih k (by omega)) (fun k hk => ih k (by omega))
        have h3' : ∀ j < i, IsIntP (PowerSeries.coeff j (wq ^ 3)) := fun j hj => by
          rw [pow_succ]
          exact coeff_mul_int (fun k hk => h2' k (by omega)) (fun k hk => ih k (by omega))
        rw [e]
        simp only [map_add]
        refine RestC.isPadicIntegral_add (RestC.isPadicIntegral_add (RestC.isPadicIntegral_add (RestC.isPadicIntegral_add (RestC.isPadicIntegral_add ?_
          (term_int h1 le_rfl ih)) (term_int h2 (by norm_num) ih)) (term_int h3 (by norm_num) h2'))
          (term_int h4 (by norm_num) h2')) (term_int h6 (by norm_num) h3')
        rw [PowerSeries.coeff_one]
        split_ifs
        · exact isPadicIntegral_one
        · exact isPadicIntegral_zero
  refine ⟨fun n => hall (n + 1) n (by omega), ?_⟩
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, e]
  simp only [map_add, term_zero _ le_rfl, term_zero _ (show 1 ≤ 2 by norm_num), term_zero _ (show 1 ≤ 3 by norm_num),
    term_zero _ (show 1 ≤ 4 by norm_num), term_zero _ (show 1 ≤ 6 by norm_num), add_zero]
  simp

/- English proof (translation)
Introduce `n` and use `by rw [dX, PowerSeries.coeff_mk] refine RestC.isPadicIntegral_mul ?_ (hf _) have := isPadicIntegral_natCast (p := p) (n + 1) simpa using this`.
-/
theorem dX_int {f : PowerSeries ℂ_[p]} (hf : ∀ n, IsIntP (PowerSeries.coeff n f)) :
    ∀ n, IsIntP (PowerSeries.coeff n (dX f)) := fun n => by
  rw [dX, PowerSeries.coeff_mk]
  refine RestC.isPadicIntegral_mul ?_ (hf _)
  have := isPadicIntegral_natCast (p := p) (n + 1)
  simpa using this

/- English proof (translation)
Introduce `n` and use `coeff_mul_int (fun i _ => hf i) (fun i _ => hg i)`.
-/
theorem int_of_mul {f g : PowerSeries ℂ_[p]} (hf : ∀ n, IsIntP (PowerSeries.coeff n f))
    (hg : ∀ n, IsIntP (PowerSeries.coeff n g)) : ∀ n, IsIntP (PowerSeries.coeff n (f * g)) := fun n =>
  coeff_mul_int (fun i _ => hf i) (fun i _ => hg i)

/- English proof (translation)
Introduce `n` and use `by rw [map_add]; exact RestC.isPadicIntegral_add (hf n) (hg n)`.
-/
theorem int_of_add {f g : PowerSeries ℂ_[p]} (hf : ∀ n, IsIntP (PowerSeries.coeff n f))
    (hg : ∀ n, IsIntP (PowerSeries.coeff n g)) : ∀ n, IsIntP (PowerSeries.coeff n (f + g)) := fun n => by
  rw [map_add]; exact RestC.isPadicIntegral_add (hf n) (hg n)

/- English proof (translation)
Introduce `n` and use `by rw [map_neg]; exact isPadicIntegral_neg (hf n)`.
-/
theorem int_of_neg {f : PowerSeries ℂ_[p]} (hf : ∀ n, IsIntP (PowerSeries.coeff n f)) :
    ∀ n, IsIntP (PowerSeries.coeff n (-f)) := fun n => by
  rw [map_neg]; exact isPadicIntegral_neg (hf n)

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `int_of_add hf (int_of_neg hg)`.
-/
theorem int_of_sub {f g : PowerSeries ℂ_[p]} (hf : ∀ n, IsIntP (PowerSeries.coeff n f))
    (hg : ∀ n, IsIntP (PowerSeries.coeff n g)) : ∀ n, IsIntP (PowerSeries.coeff n (f - g)) := by
  rw [sub_eq_add_neg]; exact int_of_add hf (int_of_neg hg)

/- English proof (translation)
Introduce `n` and use `by rw [← mul_one (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a), ← Algebra.smul_def, map_smul, PowerSeries.coeff_one, smul_eq_mul] split_ifs · rw [mul_one]; exact ha · rw [mul_zero]; exact isPadicIntegral_zero`.
-/
theorem int_C {a : ℂ_[p]} (ha : IsIntP a) : ∀ n, IsIntP (PowerSeries.coeff n (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a)) :=
  fun n => by
    rw [← mul_one (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a), ← Algebra.smul_def, map_smul, PowerSeries.coeff_one,
      smul_eq_mul]
    split_ifs
    · rw [mul_one]; exact ha
    · rw [mul_zero]; exact isPadicIntegral_zero

/- English proof (translation)
Introduce `n` and use `by rw [PowerSeries.coeff_X] split_ifs · exact isPadicIntegral_one · exact isPadicIntegral_zero`.
-/
theorem int_X : ∀ n, IsIntP (PowerSeries.coeff n (PowerSeries.X : PowerSeries ℂ_[p])) := fun n => by
  rw [PowerSeries.coeff_X]
  split_ifs
  · exact isPadicIntegral_one
  · exact isPadicIntegral_zero

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => intro n`. Rewrite using `[pow_zero, PowerSeries.coeff_one]`. Use `split_ifs`. Use `exacts [isPadicIntegral_one, isPadicIntegral_zero]`.

Consider the case `succ k ih => rw [pow_succ]`. Conclude with `int_of_mul ih hf`.
-/
theorem int_pow {f : PowerSeries ℂ_[p]} (hf : ∀ n, IsIntP (PowerSeries.coeff n f)) (k : ℕ) :
    ∀ n, IsIntP (PowerSeries.coeff n (f ^ k)) := by
  induction k with
  | zero => intro n; rw [pow_zero, PowerSeries.coeff_one]; split_ifs; exacts [isPadicIntegral_one, isPadicIntegral_zero]
  | succ k ih => rw [pow_succ]; exact int_of_mul ih hf

/- English proof (translation)
Establish `: (2 : PowerSeries ℂ_[p]) = algebraMap ℂ_[p] (PowerSeries ℂ_[p]) 2` using `by rw [map_ofNat]`. Rewrite using `[this]`. Conclude with `int_C (by have := isPadicIntegral_natCast (p := p) 2; simpa using this)`.
-/
theorem int_two : ∀ n, IsIntP (PowerSeries.coeff n (2 : PowerSeries ℂ_[p])) := by
  have : (2 : PowerSeries ℂ_[p]) = algebraMap ℂ_[p] (PowerSeries ℂ_[p]) 2 := by rw [map_ofNat]
  rw [this]
  exact int_C (by have := isPadicIntegral_natCast (p := p) 2; simpa using this)

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[dX, PowerSeries.coeff_mk, flog, PowerSeries.coeff_mk, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel]`. Establish `: ((n : ℂ_[p]) + 1) ≠ 0` using `by exact_mod_cast Nat.succ_ne_zero n`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem dX_flog (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : dX (flog W wq) = omegaW W wq := by
  ext n
  rw [dX, PowerSeries.coeff_mk, flog, PowerSeries.coeff_mk, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel]
  have : ((n : ℂ_[p]) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast
  field_simp

/- English proof (translation)
Introduce `p _ hp2 W wq h1 h2 h3 h4 h6 hw`. Take `⟨hwI, hw1⟩` from `wq_int W wq h1 h2 h3 h4 h6 hw`. Establish `h2n : ‖(2 : ℂ_[p])‖ = 1`. Use `RestC.norm_nat_coprime p ((Nat.coprime_primes Nat.prime_two Fact.out).mpr (Ne.symm hp2))` as an intermediate fact. Simplify using `using this`.

Rewrite using `[dX_flog]`. Use `set Q := wq * (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * PowerSeries.X + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * PowerSeries.X ^ 3 * wq - 2) with hQ`. Establish `hQ0 : PowerSeries.constantCoeff Q = -2`. Rewrite using `[hQ]`. Simplify using `[hw1, map_ofNat]`.

Establish `hQI : ∀ n, IsIntP (PowerSeries.coeff n Q)` using `int_of_mul hwI (int_of_sub (int_of_add (int_of_mul (int_C h1) int_X) (int_of_mul (int_of_mul (int_C h3) (int_pow int_X 3)) hwI)) int_two)`. Establish `hQinv` using `int_inv' (by rw [hQ0, norm_neg, h2n]) hQI`. Establish `hNI : ∀ n, IsIntP (PowerSeries.coeff n (-(2 : PowerSeries ℂ_[p]) * wq - PowerSeries.X * dX wq))` using `int_of_sub (int_of_mul (int_of_neg int_two) hwI) (int_of_mul int_X (dX_int hwI))`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[omegaW, map_mul, PowerSeries.constantCoeff_inv, ← hQ, hQ0]`.

Establish `h2ne : (2 : ℂ_[p]) ≠ 0`. Introduce `h`. Rewrite `h2n` using `[h, norm_zero]`. Conclude with `zero_ne_one h2n`. Simplify using `[hw1, map_ofNat]`.

Rewrite using `[omegaW, ← hQ]`. Conclude with `int_of_mul hNI hQinv`.
-/
theorem log_derivative_integral : LogDerInt := by
  intro p _ hp2 W wq h1 h2 h3 h4 h6 hw
  obtain ⟨hwI, hw1⟩ := wq_int W wq h1 h2 h3 h4 h6 hw
  have h2n : ‖(2 : ℂ_[p])‖ = 1 := by
    have := RestC.norm_nat_coprime p ((Nat.coprime_primes Nat.prime_two Fact.out).mpr (Ne.symm hp2))
    simpa using this
  rw [dX_flog]
  set Q := wq * (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * PowerSeries.X +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * PowerSeries.X ^ 3 * wq - 2) with hQ
  have hQ0 : PowerSeries.constantCoeff Q = -2 := by
    rw [hQ]; simp [hw1, map_ofNat]
  have hQI : ∀ n, IsIntP (PowerSeries.coeff n Q) :=
    int_of_mul hwI (int_of_sub (int_of_add (int_of_mul (int_C h1) int_X)
      (int_of_mul (int_of_mul (int_C h3) (int_pow int_X 3)) hwI)) int_two)
  have hQinv := int_inv' (by rw [hQ0, norm_neg, h2n]) hQI
  have hNI : ∀ n, IsIntP (PowerSeries.coeff n (-(2 : PowerSeries ℂ_[p]) * wq - PowerSeries.X * dX wq)) :=
    int_of_sub (int_of_mul (int_of_neg int_two) hwI) (int_of_mul int_X (dX_int hwI))
  refine ⟨?_, ?_⟩
  · rw [omegaW, map_mul, PowerSeries.constantCoeff_inv, ← hQ, hQ0]
    have h2ne : (2 : ℂ_[p]) ≠ 0 := by
      intro h; rw [h, norm_zero] at h2n; exact zero_ne_one h2n
    simp [hw1, map_ofNat]
  · rw [omegaW, ← hQ]
    exact int_of_mul hNI hQinv

end Log

end JetIntegrality

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

/- English proof (translation)
Introduce `hInt hOB hME hLD hEU hPJ D cc δ B hcc hδ χ hχ p _ hp5 hinert lam N N' L L' hAdm F hF`. Establish `hp2 : p ≠ 2` using `by omega`. Take `⟨r, b, hb, hbo⟩` from `hOB D p hp5 hinert N N' L L' hAdm`. Take `⟨C, wq, hC, hwq⟩` from `hME D cc δ hcc hδ p hp5 hinert lam`. Establish `hV` using `hInt D cc δ B hcc hδ χ hχ p hp5 hinert lam N N' L L' hAdm F hF C wq r b hC hwq hb hbo`.

Establish `hC'` using `hC`. Take `⟨h1, h2, h3, h4, h6, -⟩` from `hC'`. Take `⟨hl1, hlI⟩` from `hLD p hp2 _ wq h1 h2 h3 h4 h6 hwq`. Take `⟨he1, heJ⟩` from `hPJ D cc δ hcc hδ p hp5 hinert lam C wq hC hwq`. Conclude with `JetIntegrality.jets_core hp2 lam _ C wq b _ hb F (hEU D cc δ hcc hδ p hp5 hinert lam C hC) hl1 hlI he1 heJ hV`.
-/
theorem jetsInert_of : JetsOfInt := by
  intro hInt hOB hME hLD hEU hPJ D cc δ B hcc hδ χ hχ p _ hp5 hinert lam N N' L L' hAdm F hF
  have hp2 : p ≠ 2 := by omega
  obtain ⟨r, b, hb, hbo⟩ := hOB D p hp5 hinert N N' L L' hAdm
  obtain ⟨C, wq, hC, hwq⟩ := hME D cc δ hcc hδ p hp5 hinert lam
  have hV := hInt D cc δ B hcc hδ χ hχ p hp5 hinert lam N N' L L' hAdm F hF C wq r b hC hwq hb hbo
  have hC' := hC
  obtain ⟨h1, h2, h3, h4, h6, -⟩ := hC'
  obtain ⟨hl1, hlI⟩ := hLD p hp2 _ wq h1 h2 h3 h4 h6 hwq
  obtain ⟨he1, heJ⟩ := hPJ D cc δ hcc hδ p hp5 hinert lam C wq hC hwq
  exact JetIntegrality.jets_core hp2 lam _ C wq b _ hb F (hEU D cc δ hcc hδ p hp5 hinert lam C hC)
    hl1 hlI he1 heJ hV

end Formalism.L2.KerInert
