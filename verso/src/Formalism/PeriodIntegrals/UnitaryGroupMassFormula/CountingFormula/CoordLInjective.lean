import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.UnimodOneGenus
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralHeckeForms

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lat

variable (D : D7)

/- English proof (translation)
Unfold `ddS`. Rewrite using `[Ne, FractionalIdeal.coeIdeal_eq_zero]`. Conclude with `Ideal.map_ne_bot_of_ne_bot differentIdeal_ne_bot`.
-/
theorem ddS_ne_zero : ddS D ≠ 0 := by
  unfold ddS
  rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
  exact Ideal.map_ne_bot_of_ne_bot differentIdeal_ne_bot

/- English proof (translation)
Unfold `aaI`. Conclude with `zpow_ne_zero _ (ddS_ne_zero D)`.
-/
theorem aaI_ne_zero (a : Fin D.R.rS) : aaI D a ≠ 0 := by
  unfold aaI
  exact zpow_ne_zero _ (ddS_ne_zero D)

/- English proof (translation)
Use `⟨Ideal.absNorm (Ideal.span {b}), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]`. Conclude with `hb`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {b}))`. Conclude with `⟨c, by rw [← hc, mul_comm]⟩`.
-/
theorem int_mul_of_ne {b : 𝓞 D.host.E} (hb : b ≠ 0) : ∃ k : ℕ, k ≠ 0 ∧ ∃ c : 𝓞 D.host.E, (k : 𝓞 D.host.E) = b * c := by
  refine ⟨Ideal.absNorm (Ideal.span {b}), ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hb
  · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {b}))
    exact ⟨c, by rw [← hc, mul_comm]⟩

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem coe_nat_O (k : ℕ) : (((k : 𝓞 D.host.E)) : D.host.E) = (k : D.host.E) := by
  simp

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨y, hyI, hy0⟩ : ∃ y ∈ I, y ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Apply `hI` to reduce the goal to its premises. Use extensionality with `z`.

Rewrite using `[FractionalIdeal.mem_zero_iff]`. Conclude with `⟨h z, fun hz => hz ▸ fi_zero D I⟩`. Take `⟨a0, b0, hb0, rfl⟩` from `IsFractionRing.div_surjective (𝓞 D.host.E) y`. Establish `hb0' : algebraMap (𝓞 D.host.E) D.host.E b0 ≠ 0`. Rewrite using `[Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)]`.

Conclude with `nonZeroDivisors.ne_zero hb0`. Establish `ha0I : algebraMap (𝓞 D.host.E) D.host.E a0 ∈ I`. Use `fi_mul D b0 hyI` as an intermediate fact. Establish `e : (b0 : D.host.E) * (algebraMap (𝓞 D.host.E) D.host.E a0 / algebraMap (𝓞 D.host.E) D.host.E b0) = algebraMap (𝓞 D.host.E) D.host.E a0`. Rewrite using `[show (b0 : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E b0 from rfl, mul_div_cancel₀ _ hb0']`.

Rewrite `this` using `[e]`. Then use the resulting hypothesis. Establish `ha00 : a0 ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hy0`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (𝓞 D.host.E) x`.

Establish `hbne : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Establish `hb' : algebraMap (𝓞 D.host.E) D.host.E b ≠ 0`. Rewrite using `[Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)]`. Conclude with `hbne`. Take `⟨k, hk, c, hc⟩` from `int_mul_of_ne D hbne`.

Take `⟨k0, hk0, c0, hc0⟩` from `int_mul_of_ne D ha00`. Use `⟨k0 * k, mul_ne_zero hk0 hk, ?_⟩` and prove the remaining obligations. Establish `hcE : (k : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E b * algebraMap (𝓞 D.host.E) D.host.E c`. Rewrite using `[← map_mul, ← hc]`. Simplify using the standard rewrite rules.

Establish `hc0E : (k0 : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E a0 * algebraMap (𝓞 D.host.E) D.host.E c0`. Rewrite using `[← map_mul, ← hc0]`. Simplify using the standard rewrite rules. Establish `e : ((k0 * k : ℕ) : D.host.E) * (algebraMap (𝓞 D.host.E) D.host.E a / algebraMap (𝓞 D.host.E) D.host.E b) = ((c0 * c * a : 𝓞 D.host.E) : D.host.E) * algebraMap (𝓞 D.host.E) D.host.E a0`. Rewrite using `[Nat.cast_mul, hcE, hc0E]`.

Use `show _ = algebraMap (𝓞 D.host.E) D.host.E (c0 * c * a) * _`. Rewrite using `[map_mul, map_mul]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Conclude with `fi_mul D _ ha0I`.
-/
theorem fi_nat_mul {I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E} (hI : I ≠ 0) (x : D.host.E) :
    ∃ k : ℕ, k ≠ 0 ∧ (k : D.host.E) * x ∈ I := by
  obtain ⟨y, hyI, hy0⟩ : ∃ y ∈ I, y ≠ 0 := by
    by_contra h
    push Not at h
    apply hI
    ext z
    rw [FractionalIdeal.mem_zero_iff]
    exact ⟨h z, fun hz => hz ▸ fi_zero D I⟩
  obtain ⟨a0, b0, hb0, rfl⟩ := IsFractionRing.div_surjective (𝓞 D.host.E) y
  have hb0' : algebraMap (𝓞 D.host.E) D.host.E b0 ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)]
    exact nonZeroDivisors.ne_zero hb0
  have ha0I : algebraMap (𝓞 D.host.E) D.host.E a0 ∈ I := by
    have := fi_mul D b0 hyI
    have e : (b0 : D.host.E) * (algebraMap (𝓞 D.host.E) D.host.E a0 / algebraMap (𝓞 D.host.E) D.host.E b0) =
        algebraMap (𝓞 D.host.E) D.host.E a0 := by
      rw [show (b0 : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E b0 from rfl, mul_div_cancel₀ _ hb0']
    rwa [e] at this
  have ha00 : a0 ≠ 0 := by
    rintro rfl
    simp at hy0
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (𝓞 D.host.E) x
  have hbne : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb' : algebraMap (𝓞 D.host.E) D.host.E b ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)]
    exact hbne
  obtain ⟨k, hk, c, hc⟩ := int_mul_of_ne D hbne
  obtain ⟨k0, hk0, c0, hc0⟩ := int_mul_of_ne D ha00
  refine ⟨k0 * k, mul_ne_zero hk0 hk, ?_⟩
  have hcE : (k : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E b * algebraMap (𝓞 D.host.E) D.host.E c := by
    rw [← map_mul, ← hc]; simp
  have hc0E : (k0 : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E a0 * algebraMap (𝓞 D.host.E) D.host.E c0 := by
    rw [← map_mul, ← hc0]; simp
  have e : ((k0 * k : ℕ) : D.host.E) * (algebraMap (𝓞 D.host.E) D.host.E a / algebraMap (𝓞 D.host.E) D.host.E b) =
      ((c0 * c * a : 𝓞 D.host.E) : D.host.E) * algebraMap (𝓞 D.host.E) D.host.E a0 := by
    rw [Nat.cast_mul, hcE, hc0E]
    show _ = algebraMap (𝓞 D.host.E) D.host.E (c0 * c * a) * _
    rw [map_mul, map_mul]
    field_simp
  rw [e]
  exact fi_mul D _ ha0I

variable {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (f : Fin D.R.rS → (VS D).V)

/- English proof (translation)
Apply the tactic sequence `first | exact UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul .. | (apply UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul <;> assumption) | (intros; apply UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul <;> assumption) | (apply @UpperTheory.Reformulated …`.
-/
theorem M_nat_smul (M : Submodule (𝓞 D.host.E) (WbQ D F0)) (hsp : Submodule.span D.host.E (M : Set (WbQ D F0)) = ⊤)
    (m : WbQ D F0) : ∃ k : ℕ, k ≠ 0 ∧ (k : 𝓞 D.host.E) • m ∈ M := by
  first | exact UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul .. | (apply UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul <;> assumption) | (intros; apply UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul <;> assumption) | (apply @UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul <;> assumption) | (apply @UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul D T F0 M hsp m | exact @UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul D T F0 M hsp | exact @UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul D T F0 M | exact @UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul D T F0 | exact @UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul D T | exact @UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul D

/- English proof (translation)
Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨a, rfl⟩` from `hy`. Simplify using `[vPr, hf.1]`.

Consider the case `zero => simp`. Consider the case `add y w _ _ h1 h2 => simp [h1, h2]`. Consider the case `smul c y _ h => simp [h]`.
-/
theorem vPr_perp (hf : PartnerOK D F0 f) (v : (VS D).V) : vPr D F0 f v ∈ perpS (VS D) F0.X := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    simp [vPr, hf.1]
  | zero => simp
  | add y w _ _ h1 h2 => simp [h1, h2]
  | smul c y _ h => simp [h]

def vPrLin : (VS D).V →ₗ[D.host.E] (VS D).V where
  toFun := vPr D F0 f
  map_add' := vPr_add D F0 f
  map_smul' := vPr_smul D F0 f

def coordL (hf : PartnerOK D F0 f) :
    (VS D).V →ₗ[D.host.E] (Fin D.R.rS → D.host.E) × (WbQ D F0) × (Fin D.R.rS → D.host.E) :=
  LinearMap.prod (LinearMap.pi fun a => ((VS D).hT (f a)).comp (vPrLin D F0 f))
    (LinearMap.prod ((nX D F0).mkQ.comp (LinearMap.codRestrict _ (vPrLin D F0 f) (vPr_perp D F0 f hf)))
      (LinearMap.pi fun a => (VS D).hT (F0.e a)))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coordL_apply (hf : PartnerOK D F0 f) (v : (VS D).V) :
    coordL D F0 f hf v = ((fun a => (VS D).hT (f a) (vPr D F0 f v)),
      (Submodule.Quotient.mk (⟨vPr D F0 f v, vPr_perp D F0 f hf v⟩ : perpS (VS D) F0.X) : WbQ D F0),
      (fun a => (VS D).hT (F0.e a) v)) := rfl

/- English proof (translation)
Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `v hv`. Rewrite `hv` using `[coordL_apply]`. Simplify using `only [Prod.mk_eq_zero] at hv`. Take `⟨h1, h2, h3⟩` from `hv`.

Establish `hb : ∀ a, (VS D).hT (F0.e a) v = 0` using `fun a => congrFun h3 a`. Establish `hvv : vPr D F0 f v = v` using `by simp [vPr, hb]`. Establish `hX : v ∈ F0.X`. Rewrite `h2` using `[Submodule.Quotient.mk_eq_zero]`. Establish `: vPr D F0 f v ∈ F0.X` using `h2`.

Rewrite `this` using `[hvv]`. Then use the resulting hypothesis. Take `⟨c, hc⟩` from `Submodule.mem_span_range_iff_exists_fun D.host.E |>.1 hX`. Establish `ha : ∀ a, (VS D).hT (f a) v = 0` using `fun a => by`. Use `congrFun h1 a` as an intermediate fact. Rewrite `this` using `[hvv]`. Then use the resulting hypothesis.

Establish `hc0 : ∀ a, c a = 0`. Introduce `a`. Establish `h` using `ha a`. Rewrite `h` using `[← hc, map_sum]`. Establish `e : ∀ b, (VS D).hT (f a) (c b • F0.e b) = c b * (if b = a then 1 else 0)`.

Introduce `b`. Rewrite using `[map_smul, smul_eq_mul, ← (VS D).herm.eq (F0.e b) (f a), hf.1 b a]`. Apply the tactic sequence `split_ifs <;> simp`. Simplify using `only [e, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h`. Conclude with `h`.

Rewrite using `[← hc]`. Simplify using `[hc0]`.
-/
theorem coordL_injective (hf : PartnerOK D F0 f) : Function.Injective (coordL D F0 f hf) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  rw [coordL_apply] at hv
  simp only [Prod.mk_eq_zero] at hv
  obtain ⟨h1, h2, h3⟩ := hv
  have hb : ∀ a, (VS D).hT (F0.e a) v = 0 := fun a => congrFun h3 a
  have hvv : vPr D F0 f v = v := by simp [vPr, hb]
  have hX : v ∈ F0.X := by
    rw [Submodule.Quotient.mk_eq_zero] at h2
    have : vPr D F0 f v ∈ F0.X := h2
    rwa [hvv] at this
  obtain ⟨c, hc⟩ := Submodule.mem_span_range_iff_exists_fun D.host.E |>.1 hX
  have ha : ∀ a, (VS D).hT (f a) v = 0 := fun a => by
    have := congrFun h1 a
    rwa [hvv] at this
  have hc0 : ∀ a, c a = 0 := by
    intro a
    have h := ha a
    rw [← hc, map_sum] at h
    have e : ∀ b, (VS D).hT (f a) (c b • F0.e b) = c b * (if b = a then 1 else 0) := by
      intro b
      rw [map_smul, smul_eq_mul, ← (VS D).herm.eq (F0.e b) (f a), hf.1 b a]
      split_ifs <;> simp
    simp only [e, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    exact h
  rw [← hc]
  simp [hc0]

/- English proof (translation)
Take `⟨d, hdS, hd⟩` from `I.isFractional`. Use `⟨(algebraMap (𝓞 D.host.E) D.host.E d)⁻¹, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨o, ho⟩` from `hd x hx`. Establish `hd0 : algebraMap (𝓞 D.host.E) D.host.E d ≠ 0`. Rewrite using `[Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)]`.

Conclude with `nonZeroDivisors.ne_zero hdS`. Use `⟨o, ?_⟩` and prove the remaining obligations. Rewrite `ho` using `[Algebra.smul_def]`. Use `show x = algebraMap (𝓞 D.host.E) D.host.E o * _`. Rewrite using `[ho]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem fi_bound (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
    ∃ d : D.host.E, ∀ x ∈ I, ∃ o : 𝓞 D.host.E, x = (o : D.host.E) * d := by
  obtain ⟨d, hdS, hd⟩ := I.isFractional
  refine ⟨(algebraMap (𝓞 D.host.E) D.host.E d)⁻¹, fun x hx => ?_⟩
  obtain ⟨o, ho⟩ := hd x hx
  have hd0 : algebraMap (𝓞 D.host.E) D.host.E d ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)]
    exact nonZeroDivisors.ne_zero hdS
  refine ⟨o, ?_⟩
  rw [Algebra.smul_def] at ho
  show x = algebraMap (𝓞 D.host.E) D.host.E o * _
  rw [ho]
  field_simp

/- English proof (translation)
Use `choose o ho using h`. Establish `e : x = ∑ a, o a • (Pi.single a (d a) : Fin D.R.rS → D.host.E)`. Use extensionality with `b`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]`. Simplify using `[ho b]`.

Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)`.
-/
theorem pi_mem_span {x : Fin D.R.rS → D.host.E} {d : Fin D.R.rS → D.host.E}
    (h : ∀ a, ∃ o : 𝓞 D.host.E, x a = (o : D.host.E) * d a) :
    x ∈ Submodule.span (𝓞 D.host.E) (Set.range fun a => (Pi.single a (d a) : Fin D.R.rS → D.host.E)) := by
  choose o ho using h
  have e : x = ∑ a, o a • (Pi.single a (d a) : Fin D.R.rS → D.host.E) := by
    ext b
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
    simp [ho b]
    rfl
  rw [e]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

/- English proof (translation)
Use `choose dα hdα using fun a => fi_bound D (aaI D a)`. Use `choose dβ hdβ using fun a => fi_bound D (aaI D a)⁻¹`. Set `P : Submodule (𝓞 D.host.E) ((Fin D.R.rS → D.host.E) × (WbQ D F0) × (Fin D.R.rS → D.host.E))` to `(Submodule.span (𝓞 D.host.E) (Set.range fun a => (Pi.single a (dα a) : Fin D.R.rS → D.host.E))).prod (M.prod (Submodule.span (𝓞 D.host.E) (Set.range fun a => (Pi.single a (star (dβ a)) : Fin D.R.rS → D.host.E))))`. Establish `hPfg : P.FG` using `Submodule.FG.prod (Submodule.fg_span (Set.finite_range _)) (Submodule.FG.prod hM (Submodule.fg_span (Set.finite_range _)))`. Establish `hle : (lamC D F0 f M).map ((coordL D F0 f hf).restrictScalars (𝓞 D.host.E)) ≤ P`.

Introduce and unpack `_ ⟨v, ⟨h1, ⟨w, hw, hwM⟩, h3⟩, rfl⟩`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `pi_mem_span D (fun a => hdα a _ (h3 a))`. Establish `e : (⟨vPr D F0 f v, vPr_perp D F0 f hf v⟩ : perpS (VS D) F0.X) = w` using `Subtype.ext hw.symm show (Submodule.Quotient.mk (⟨vPr D F0 f v, vPr_perp D F0 f hf v⟩ : perpS (VS D) F0.X) : WbQ D F0) ∈ M`. Rewrite using `[e]`.

Conclude with `hwM`. Use `pi_mem_span D (fun a => ?_)` and prove the remaining obligations. Take `⟨o, ho⟩` from `hdβ a _ (h1 a)`. Take `⟨o', ho'⟩` from `star_int D o`. Use `⟨o', ?_⟩` and prove the remaining obligations.

Use `show (VS D).hT (F0.e a) v = _`. Rewrite using `[ho', ← star_mul, mul_comm, ← ho, star_star]`. Conclude with `Submodule.fg_of_fg_map_injective ((coordL D F0 f hf).restrictScalars (𝓞 D.host.E)) (coordL_injective D F0 f hf) (Submodule.FG.of_le (S := (lamC D F0 f M).map ((coordL D F0 f hf).restrictScalars (𝓞 D.host.E))) hPfg hle)`.
-/
theorem lamC_fg (hf : PartnerOK D F0 f) (M : Submodule (𝓞 D.host.E) (WbQ D F0)) (hM : M.FG) :
    (lamC D F0 f M).FG := by
  choose dα hdα using fun a => fi_bound D (aaI D a)
  choose dβ hdβ using fun a => fi_bound D (aaI D a)⁻¹
  let P : Submodule (𝓞 D.host.E) ((Fin D.R.rS → D.host.E) × (WbQ D F0) × (Fin D.R.rS → D.host.E)) :=
    (Submodule.span (𝓞 D.host.E) (Set.range fun a => (Pi.single a (dα a) : Fin D.R.rS → D.host.E))).prod
      (M.prod (Submodule.span (𝓞 D.host.E) (Set.range fun a =>
        (Pi.single a (star (dβ a)) : Fin D.R.rS → D.host.E))))
  have hPfg : P.FG := Submodule.FG.prod (Submodule.fg_span (Set.finite_range _))
    (Submodule.FG.prod hM (Submodule.fg_span (Set.finite_range _)))
  have hle : (lamC D F0 f M).map ((coordL D F0 f hf).restrictScalars (𝓞 D.host.E)) ≤ P := by
    rintro _ ⟨v, ⟨h1, ⟨w, hw, hwM⟩, h3⟩, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · exact pi_mem_span D (fun a => hdα a _ (h3 a))
    · have e : (⟨vPr D F0 f v, vPr_perp D F0 f hf v⟩ : perpS (VS D) F0.X) = w := Subtype.ext hw.symm
      show (Submodule.Quotient.mk (⟨vPr D F0 f v, vPr_perp D F0 f hf v⟩ : perpS (VS D) F0.X) : WbQ D F0) ∈ M
      rw [e]; exact hwM
    · refine pi_mem_span D (fun a => ?_)
      obtain ⟨o, ho⟩ := hdβ a _ (h1 a)
      obtain ⟨o', ho'⟩ := star_int D o
      refine ⟨o', ?_⟩
      show (VS D).hT (F0.e a) v = _
      rw [ho', ← star_mul, mul_comm, ← ho, star_star]
  exact Submodule.fg_of_fg_map_injective ((coordL D F0 f hf).restrictScalars (𝓞 D.host.E)) (coordL_injective D F0 f hf)
    (Submodule.FG.of_le (S := (lamC D F0 f M).map ((coordL D F0 f hf).restrictScalars (𝓞 D.host.E))) hPfg hle)

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce `v _`. Use `choose kα hkα hα using fun a => fi_nat_mul D (aaI_ne_zero D a) ((VS D).hT (f a) (vPr D F0 f v))`. Use `choose kβ hkβ hβ using fun a => fi_nat_mul D (inv_ne_zero (aaI_ne_zero D a)) (star ((VS D).hT (F0.e a) v))`. Take `⟨kM, hkM, hM⟩` from `M_nat_smul D F0 M hsp (Submodule.Quotient.mk (⟨vPr D F0 f v, vPr_perp D F0 f hf v⟩ : perpS (VS D) F0.X))`.

Use `set K : ℕ := (∏ a, kα a) * kM * ∏ a, kβ a with hK`. Establish `hK0 : K ≠ 0`. Rewrite using `[hK]`. Use `mul_ne_zero (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun a _ => hkα a) hkM) (Finset.prod_ne_zero_iff.2 fun a _ => hkβ a)` and prove the remaining obligations. Establish `hdvd : ∀ {k : ℕ} {I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E} {x : D.host.E}, k ∣ K → (k : D.host.E) * x ∈ I → (K : D.host.E) * x ∈ I`.

Introduce and unpack `k I x ⟨m, hm⟩ hx`. Rewrite using `[hm, Nat.cast_mul, mul_comm (k : D.host.E) (m : D.host.E), mul_assoc]`. Use `fi_mul D (m : 𝓞 D.host.E) hx` as an intermediate fact. Simplify using `using this`. Establish `hmem : (K : 𝓞 D.host.E) • v ∈ lamC D F0 f M`.

Establish `hs : (K : 𝓞 D.host.E) • v = (K : D.host.E) • v`. Rewrite using `[← algebraMap_smul D.host.E (K : 𝓞 D.host.E) v, map_natCast]`. Rewrite using `[hs]`. Use `⟨fun a => ?_, ⟨(K : 𝓞 D.host.E) • ⟨vPr D F0 f v, vPr_perp D F0 f hf v⟩, ?_, ?_⟩, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul, star_mul, star_natCast, mul_comm]`.

Conclude with `hdvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ a) |>.trans (dvd_mul_left _ _)) (hβ a)`. Rewrite using `[vPr_smul] show (K : 𝓞 D.host.E) • vPr D F0 f v = _`. Rewrite using `[← algebraMap_smul D.host.E (K : 𝓞 D.host.E), map_natCast]`. Rewrite using `[Submodule.Quotient.mk_smul]`. Choose the witnesses or unpack the hypotheses as in `⟨m, hm⟩ : kM ∣ K := by`.

Rewrite using `[hK]`. Conclude with `(dvd_mul_left _ _).mul_right _`. Rewrite using `[hm, Nat.cast_mul, mul_comm, mul_smul]`. Conclude with `M.smul_mem _ hM`. Rewrite using `[vPr_smul, map_smul, smul_eq_mul]`.

Conclude with `hdvd ((Finset.dvd_prod_of_mem _ (Finset.mem_univ a)).mul_right _ |>.mul_right _) (hα a)`. Establish `hK' : (K : D.host.E) ≠ 0` using `Nat.cast_ne_zero.2 hK0`. Establish `e : v = (K : D.host.E)⁻¹ • ((K : 𝓞 D.host.E) • v)`. Rewrite using `[← algebraMap_smul D.host.E (K : 𝓞 D.host.E) v, map_natCast, smul_smul, inv_mul_cancel₀ hK', one_smul]`. Rewrite using `[e]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hmem)`.
-/
theorem lamC_span (hf : PartnerOK D F0 f) (M : Submodule (𝓞 D.host.E) (WbQ D F0))
    (hsp : Submodule.span D.host.E (M : Set (WbQ D F0)) = ⊤) :
    Submodule.span D.host.E (lamC D F0 f M : Set (VS D).V) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  choose kα hkα hα using fun a => fi_nat_mul D (aaI_ne_zero D a) ((VS D).hT (f a) (vPr D F0 f v))
  choose kβ hkβ hβ using fun a => fi_nat_mul D (inv_ne_zero (aaI_ne_zero D a)) (star ((VS D).hT (F0.e a) v))
  obtain ⟨kM, hkM, hM⟩ := M_nat_smul D F0 M hsp
    (Submodule.Quotient.mk (⟨vPr D F0 f v, vPr_perp D F0 f hf v⟩ : perpS (VS D) F0.X))
  set K : ℕ := (∏ a, kα a) * kM * ∏ a, kβ a with hK
  have hK0 : K ≠ 0 := by
    rw [hK]
    refine mul_ne_zero (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun a _ => hkα a) hkM)
      (Finset.prod_ne_zero_iff.2 fun a _ => hkβ a)
  have hdvd : ∀ {k : ℕ} {I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E} {x : D.host.E},
      k ∣ K → (k : D.host.E) * x ∈ I → (K : D.host.E) * x ∈ I := by
    rintro k I x ⟨m, hm⟩ hx
    rw [hm, Nat.cast_mul, mul_comm (k : D.host.E) (m : D.host.E), mul_assoc]
    have := fi_mul D (m : 𝓞 D.host.E) hx
    simpa using this
  have hmem : (K : 𝓞 D.host.E) • v ∈ lamC D F0 f M := by
    have hs : (K : 𝓞 D.host.E) • v = (K : D.host.E) • v := by
      rw [← algebraMap_smul D.host.E (K : 𝓞 D.host.E) v, map_natCast]
    rw [hs]
    refine ⟨fun a => ?_, ⟨(K : 𝓞 D.host.E) • ⟨vPr D F0 f v, vPr_perp D F0 f hf v⟩, ?_, ?_⟩, fun a => ?_⟩
    · rw [map_smul, smul_eq_mul, star_mul, star_natCast, mul_comm]
      exact hdvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ a) |>.trans (dvd_mul_left _ _)) (hβ a)
    · rw [vPr_smul]
      show (K : 𝓞 D.host.E) • vPr D F0 f v = _
      rw [← algebraMap_smul D.host.E (K : 𝓞 D.host.E), map_natCast]
    · rw [Submodule.Quotient.mk_smul]
      obtain ⟨m, hm⟩ : kM ∣ K := by
        rw [hK]; exact (dvd_mul_left _ _).mul_right _
      rw [hm, Nat.cast_mul, mul_comm, mul_smul]
      exact M.smul_mem _ hM
    · rw [vPr_smul, map_smul, smul_eq_mul]
      exact hdvd ((Finset.dvd_prod_of_mem _ (Finset.mem_univ a)).mul_right _ |>.mul_right _) (hα a)
  have hK' : (K : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hK0
  have e : v = (K : D.host.E)⁻¹ • ((K : 𝓞 D.host.E) • v) := by
    rw [← algebraMap_smul D.host.E (K : 𝓞 D.host.E) v, map_natCast, smul_smul, inv_mul_cancel₀ hK', one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

/- English proof (translation)
Introduce `D u F0 f M hf hM`. Conclude with `⟨lamC_fg D F0 f hf M hM.1.fg, lamC_span D F0 f hf M hM.1.span_eq_top⟩`.
-/
theorem lattice_integral : LamLattice := by
  intro D u F0 f M hf hM
  exact ⟨lamC_fg D F0 f hf M hM.1.fg, lamC_span D F0 f hf M hM.1.span_eq_top⟩

end Lat

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
