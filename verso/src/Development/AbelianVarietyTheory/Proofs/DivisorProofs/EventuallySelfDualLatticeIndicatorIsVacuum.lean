import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntAddConjEqOneOfBaseGood

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.AdelicU GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Filter Topology

namespace GlobalTheory.VacIndic

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Establish `h` using `(algebraMap F (Af F) x).2`. Conclude with `h.mono fun v hv => by rw [← (evalV F v).commutes x]; exact hv`.
-/
theorem eventually_int (x : F) :
    ∀ᶠ v in cofinite, algebraMap F (Fv F v) x ∈ (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F := by
  have h := (algebraMap F (Af F) x).2
  exact h.mono fun v hv => by rw [← (evalV F v).commutes x]; exact hv

/- English proof (translation)
The claim follows from `(evFin F v).commutes x`.
-/
theorem evFin_algebraMap (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    evFin F v (algebraMap F (AF F) x) = algebraMap F (Fv F v) x := (evFin F v).commutes x

/- English proof (translation)
Use `set e : AF F := LinearMap.inr F (Ainf F) (Af F) (singleFin v 1) with he`. Establish `hev : evFin F v e = 1` using `by show evalV F v (singleFin v 1) = 1`. Conclude with `evalV_singleFin_self v 1`. Establish `h1 : (1 - e) • a = 0` using `ha _ (by rw [map_sub, map_one, hev, sub_self])`. Establish `h2 : a = e * a`.

Rewrite `h1` using `[smul_eq_mul, sub_mul, one_mul, sub_eq_zero]`. Conclude with `h1`. Rewrite using `[h2]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show (0 : Ainf F) * a.1 = 0`.

Rewrite using `[zero_mul]`. Apply `af_ext` to reduce the goal to its premises. Introduce `u`. Use `show evalV F u (singleFin v 1 * a.2) = evalV F u (singleFin v (evFin F v (e * a)))`. Distinguish the cases in `hu : u = v`.

Substitute `hu` using the available equality. Rewrite using `[map_mul, evalV_singleFin_self, evalV_singleFin_self, one_mul, map_mul, hev, one_mul]`. Both sides reduce to the same expression. Rewrite using `[map_mul, evalV_singleFin_ne hu, evalV_singleFin_ne hu, zero_mul]`.
-/
theorem eq_of_at {v : HeightOneSpectrum (𝓞 F)} {a : AF F} (ha : At (evFin F v) a) :
    a = LinearMap.inr F (Ainf F) (Af F) (singleFin v (evFin F v a)) := by
  set e : AF F := LinearMap.inr F (Ainf F) (Af F) (singleFin v 1) with he
  have hev : evFin F v e = 1 := by
    show evalV F v (singleFin v 1) = 1
    exact evalV_singleFin_self v 1
  have h1 : (1 - e) • a = 0 := ha _ (by rw [map_sub, map_one, hev, sub_self])
  have h2 : a = e * a := by
    rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h1; exact h1
  rw [h2]
  refine Prod.ext ?_ ?_
  · show (0 : Ainf F) * a.1 = 0; rw [zero_mul]
  · apply af_ext
    intro u
    show evalV F u (singleFin v 1 * a.2) = evalV F u (singleFin v (evFin F v (e * a)))
    by_cases hu : u = v
    · subst hu
      rw [map_mul, evalV_singleFin_self, evalV_singleFin_self, one_mul, map_mul, hev, one_mul]; rfl
    · rw [map_mul, evalV_singleFin_ne hu, evalV_singleFin_ne hu, zero_mul]

/- English proof (translation)
Use `conv_lhs => rw [eq_of_at ha]`. Both sides reduce to the same expression.
-/
theorem psi_of_at (ψ : AddChar (AF F) ℂ) {v : HeightOneSpectrum (𝓞 F)} {a : AF F} (ha : At (evFin F v) a) :
    ψ a = psiLoc ψ v (evFin F v a) := by
  conv_lhs => rw [eq_of_at ha]
  rfl

end GlobalTheory.VacIndic

namespace GlobalTheory.VacIndic

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Establish `key : ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => set w := z ^ (2 ^ k) - 1 with hw`.

Establish `e : z ^ (2 ^ (k + 1)) - 1 = w * (w + 2)` using `by rw [hw, pow_succ, pow_mul]; ring`. Establish `h1 : (3 / 2 : ℝ) ≤ ‖w + 2‖`. Establish `h2` using `norm_sub_le (w + 2) w`. Establish `h3 : (w + 2) - w = 2` using `by ring`. Rewrite `h2` using `[h3]`.

Establish `h4 : ‖(2 : ℂ)‖ = 2` using `by norm_num`. Establish `h5 : ‖w‖ < 1 / 2` using `h _`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[e, norm_mul, pow_succ]`. Combine the equalities or inequalities in the displayed calculation.

Assume the negation of the conclusion as `hne`. Establish `hpos : 0 < ‖z - 1‖` using `norm_pos_iff.mpr (sub_ne_zero.mpr hne)`. Take `⟨k, hk⟩` from `pow_unbounded_of_one_lt (1 / 2 / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)`. Establish `h7` using `key k`. Establish `h8` using `h (2 ^ k)`.

Rewrite `hk` using `[div_lt_iff₀ hpos]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem eq_one_of_pow (z : ℂ) (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  have key : ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      set w := z ^ (2 ^ k) - 1 with hw
      have e : z ^ (2 ^ (k + 1)) - 1 = w * (w + 2) := by rw [hw, pow_succ, pow_mul]; ring
      have h1 : (3 / 2 : ℝ) ≤ ‖w + 2‖ := by
        have h2 := norm_sub_le (w + 2) w
        have h3 : (w + 2) - w = 2 := by ring
        rw [h3] at h2
        have h4 : ‖(2 : ℂ)‖ = 2 := by norm_num
        have h5 : ‖w‖ < 1 / 2 := h _
        linarith
      rw [e, norm_mul, pow_succ]
      calc (3 / 2 : ℝ) ^ k * (3 / 2) * ‖z - 1‖ = ((3 / 2 : ℝ) ^ k * ‖z - 1‖) * (3 / 2) := by ring
        _ ≤ ‖w‖ * ‖w + 2‖ := mul_le_mul ih h1 (by norm_num) (norm_nonneg _)
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / 2 / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  have h7 := key k
  have h8 := h (2 ^ k)
  rw [div_lt_iff₀ hpos] at hk
  linarith

/- English proof (translation)
Unfold `psiLoc`. Rewrite using `[map_nsmul, map_nsmul]`. Conclude with `AddChar.map_nsmul_eq_pow ψ n _`.
-/
theorem psiLoc_nsmul (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (c : Fv F v) (n : ℕ) :
    psiLoc ψ v (n • c) = psiLoc ψ v c ^ n := by
  unfold psiLoc
  rw [map_nsmul, map_nsmul]
  exact AddChar.map_nsmul_eq_pow ψ n _

/- English proof (translation)
Set `s : (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) → Af F` to `fun x => (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (fun v => v.adicCompletionIntegers F) cofinite x : FiniteAdeleRing (𝓞 F) F)`. Establish `hs : Continuous s` using `RestrictedProduct.isEmbedding_structureMap.continuous`. Set `g` to `fun x => ψ (LinearMap.inr F (Ainf F) (Af F) (s x))`. Establish `hg : Continuous g` using `hψ.comp (continuous_const.prodMk hs)`. Establish `hg0 : g 0 = 1`.

Establish `: s 0 = 0` using `rfl`. Simplify using `only [g, this, map_zero]`. Conclude with `AddChar.map_zero_eq_one ψ`. Establish `hU : g ⁻¹' {z | ‖z - 1‖ < 1 / 2} ∈ 𝓝 (0 : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F)`. Use `hg.continuousAt.preimage_mem_nhds ?_` and prove the remaining obligations.

Rewrite using `[hg0]`. Conclude with `isOpen_lt (continuous_id.sub continuous_const).norm continuous_const |>.mem_nhds (by simp)`. Rewrite `hU` using `[nhds_pi, Filter.mem_pi]`. Take `⟨I, hI, t, ht, hsub⟩` from `hU`. Use `Filter.eventually_of_mem hI.compl_mem_cofinite fun v hv c hc => ?_` and prove the remaining obligations.

Establish `small : ∀ c' ∈ v.adicCompletionIntegers F, ‖psiLoc ψ v c' - 1‖ < 1 / 2`. Introduce `c' hc'`. Set `x : ∀ u : HeightOneSpectrum (𝓞 F), u.adicCompletionIntegers F` to `Pi.single v ⟨c', hc'⟩`. Establish `hx : x ∈ I.pi t`. Introduce `u hu`.

Establish `huv : u ≠ v` using `fun h => hv (h ▸ hu)`. Establish `: x u = 0` using `Pi.single_eq_of_ne huv _`. Rewrite using `[this]`. Conclude with `mem_of_mem_nhds (ht u)`. Establish `h1` using `hsub hx`.

Establish `e : s x = singleFin v c'`. Apply `af_ext` to reduce the goal to its premises. Introduce `u`. Distinguish the cases in `huv : u = v`. Substitute `huv` using the available equality.

Rewrite using `[evalV_singleFin_self]`. Use `show ((x u : u.adicCompletionIntegers F) : u.adicCompletion F) = _`. Simplify using `[x]`. Rewrite using `[evalV_singleFin_ne huv] show ((x u : u.adicCompletionIntegers F) : u.adicCompletion F) = _`. Simplify using `[x, Pi.single_eq_of_ne huv]`.

Simplify `h1` using `[g, e, psiLoc]`. Use `eq_one_of_pow _ fun n => ?_` and prove the remaining obligations. Rewrite using `[← psiLoc_nsmul]`. Conclude with `small _ (nsmul_mem hc n)`.
-/
theorem eventually_psiLoc_eq_one (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) :
    ∀ᶠ v in cofinite, ∀ c ∈ (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F, psiLoc ψ v c = 1 := by
  classical
  let s : (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) → Af F := fun x =>
    (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => v.adicCompletionIntegers F) cofinite x : FiniteAdeleRing (𝓞 F) F)
  have hs : Continuous s := RestrictedProduct.isEmbedding_structureMap.continuous
  let g := fun x => ψ (LinearMap.inr F (Ainf F) (Af F) (s x))
  have hg : Continuous g := hψ.comp (continuous_const.prodMk hs)
  have hg0 : g 0 = 1 := by
    have : s 0 = 0 := rfl
    simp only [g, this, map_zero]
    exact AddChar.map_zero_eq_one ψ
  have hU : g ⁻¹' {z | ‖z - 1‖ < 1 / 2} ∈ 𝓝 (0 : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) := by
    refine hg.continuousAt.preimage_mem_nhds ?_
    rw [hg0]
    exact isOpen_lt (continuous_id.sub continuous_const).norm continuous_const |>.mem_nhds (by simp)
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, hI, t, ht, hsub⟩ := hU
  refine Filter.eventually_of_mem hI.compl_mem_cofinite fun v hv c hc => ?_
  have small : ∀ c' ∈ v.adicCompletionIntegers F, ‖psiLoc ψ v c' - 1‖ < 1 / 2 := by
    intro c' hc'
    let x : ∀ u : HeightOneSpectrum (𝓞 F), u.adicCompletionIntegers F := Pi.single v ⟨c', hc'⟩
    have hx : x ∈ I.pi t := by
      intro u hu
      have huv : u ≠ v := fun h => hv (h ▸ hu)
      have : x u = 0 := Pi.single_eq_of_ne huv _
      rw [this]
      exact mem_of_mem_nhds (ht u)
    have h1 := hsub hx
    have e : s x = singleFin v c' := by
      apply af_ext
      intro u
      by_cases huv : u = v
      · subst huv
        rw [evalV_singleFin_self]
        show ((x u : u.adicCompletionIntegers F) : u.adicCompletion F) = _
        simp [x]
      · rw [evalV_singleFin_ne huv]
        show ((x u : u.adicCompletionIntegers F) : u.adicCompletion F) = _
        simp [x, Pi.single_eq_of_ne huv]
    simpa [g, e, psiLoc] using h1
  refine eq_one_of_pow _ fun n => ?_
  rw [← psiLoc_nsmul]
  exact small _ (nsmul_mem hc n)

end GlobalTheory.VacIndic

namespace GlobalTheory.VacIndic

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Use `set S : Set (κ → Fv F v) := {x | ∀ k, x k ∈ v.adicCompletionIntegers F} with hS`. Establish `hS' : S = Set.univ.pi fun _ => (v.adicCompletionIntegers F : Set (Fv F v))`. Use extensionality with `x`. Simplify using `[hS]`. Establish `hcl : IsClopen S`.

Rewrite using `[hS']`. Conclude with `⟨isClosed_set_pi fun _ _ => Valued.isClosed_valuationSubring (v.adicCompletion F), isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring (v.adicCompletion F)⟩`. Establish `hcp : IsCompact S`. Rewrite using `[hS']`. Use `haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v`.

Conclude with `isCompact_univ_pi fun _ => isCompact_iff_compactSpace.2 this`. Use `⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_, HasCompactSupport.intro hcp fun x hx => Set.indicator_of_notMem hx _⟩` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ S`. Conclude with `⟨S, hcl.isOpen, hx, fun y hy => by rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]; rfl⟩`. Conclude with `⟨Sᶜ, hcl.compl.isOpen, hx, fun y hy => by rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩`.
-/
theorem indicator_int_mem_SB {κ : Type} [Fintype κ] (v : HeightOneSpectrum (𝓞 F)) :
    Set.indicator {x : κ → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} 1 ∈ GlobalTheory.WeilM.SB (κ → Fv F v) := by
  set S : Set (κ → Fv F v) := {x | ∀ k, x k ∈ v.adicCompletionIntegers F} with hS
  have hS' : S = Set.univ.pi fun _ => (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext x; simp [hS]
  have hcl : IsClopen S := by
    rw [hS']
    exact ⟨isClosed_set_pi fun _ _ => Valued.isClosed_valuationSubring (v.adicCompletion F),
      isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring (v.adicCompletion F)⟩
  have hcp : IsCompact S := by
    rw [hS']
    haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
    exact isCompact_univ_pi fun _ => isCompact_iff_compactSpace.2 this
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_, HasCompactSupport.intro hcp fun x hx => Set.indicator_of_notMem hx _⟩
  by_cases hx : x ∈ S
  · exact ⟨S, hcl.isOpen, hx, fun y hy => by rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]; rfl⟩
  · exact ⟨Sᶜ, hcl.compl.isOpen, hx, fun y hy => by rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩

/- English proof (translation)
Introduce `h`. Use `congrFun h 0` as an intermediate fact. Rewrite `this` using `[Set.indicator_of_mem (show (0 : κ → Fv F v) ∈ {x : κ → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} from fun k => zero_mem _)]`. Conclude with `one_ne_zero this`.
-/
theorem indicator_int_ne_zero {κ : Type} (v : HeightOneSpectrum (𝓞 F)) :
    Set.indicator {x : κ → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} (1 : (κ → Fv F v) → ℂ) ≠ 0 := by
  intro h
  have := congrFun h 0
  rw [Set.indicator_of_mem (show (0 : κ → Fv F v) ∈ {x : κ → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} from
    fun k => zero_mem _)] at this
  exact one_ne_zero this

end GlobalTheory.VacIndic

namespace GlobalTheory.VacIndic

variable {F : Type} [Field F] [NumberField F]

section AtLemmas

variable {v : HeightOneSpectrum (𝓞 F)}

/- English proof (translation)
Introduce `u hu` and use `by rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u b, hb u hu, mul_zero]`.
-/
theorem at_mul_left {a b : AF F} (hb : At (evFin F v) b) : At (evFin F v) (a * b) := fun u hu => by
  rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u b, hb u hu, mul_zero]

/- English proof (translation)
Introduce `u hu` and use `by rw [smul_add, ha u hu, hb u hu, add_zero]`.
-/
theorem at_add {a b : AF F} (ha : At (evFin F v) a) (hb : At (evFin F v) b) : At (evFin F v) (a + b) :=
  fun u hu => by rw [smul_add, ha u hu, hb u hu, add_zero]

/- English proof (translation)
Introduce `u hu` and use `by rw [Finset.smul_sum]; exact Finset.sum_eq_zero fun i _ => h i u hu`.
-/
theorem at_sum {ι : Type} (s : Finset ι) (f : ι → AF F) (h : ∀ i, At (evFin F v) (f i)) :
    At (evFin F v) (∑ i ∈ s, f i) := fun u hu => by
  rw [Finset.smul_sum]; exact Finset.sum_eq_zero fun i _ => h i u hu

/- English proof (translation)
Introduce `u hu` and use `funext fun k => by simpa using h k u hu`.
-/
theorem at_pi {κ : Type} {z : κ → AF F} (h : ∀ k, At (evFin F v) (z k)) : At (evFin F v) z :=
  fun u hu => funext fun k => by simpa using h k u hu

end AtLemmas

/- English proof (translation)
Use `invOf_eq_left_inv ?_` and prove the remaining obligations. Rewrite using `[← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]`. Evaluate the numerical expressions.
-/
theorem invOf_two_eq : ⅟(2 : AF F) = algebraMap F (AF F) (1 / 2) := by
  refine invOf_eq_left_inv ?_
  rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]
  norm_num

/- English proof (translation)
Introduce `r hr`. Use function extensionality and compare the values at `x`. Use `set w := d.e γ with hw`. Establish `hshift : r (x + w.1) = r x` using `hr.1 x w.1 (at_pi ha1)`. Simplify using `only [Darboux.rho, schr, tens, hshift, ← hw]`.

Use `set O := v.adicCompletionIntegers F`. Distinguish the cases in `hx : ∀ k, evFin F v (x k) ∈ O`. Establish `hx' : ∀ k, evFin F v ((x + w.1) k) ∈ O` using `fun k => by`. Rewrite using `[Pi.add_apply, map_add]`. Conclude with `add_mem (hx k) (hi1 k)`.

Rewrite using `[Set.indicator_of_mem (show (fun i => evFin F v ((x + w.1) i)) ∈ {y : κ → Fv F v | ∀ k, y k ∈ O} from hx'), Set.indicator_of_mem (show (fun i => evFin F v (x i)) ∈ {y : κ → Fv F v | ∀ k, y k ∈ O} from hx)]`. Establish `hat : At (evFin F v) (x ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2))` using `at_add (at_sum _ _ fun k => at_mul_left (ha2 k)) (at_mul_left (at_sum _ _ fun k => at_mul_left (ha2 k)))`. Rewrite using `[psi_of_at ψ hat, hψ]`. Simplify using the standard rewrite rules. Rewrite using `[map_add, map_mul, invOf_two_eq, evFin_algebraMap]`.

Use `add_mem ?_ (mul_mem h2 ?_)` and prove the remaining obligations. Simplify using `only [dotProduct, map_sum, map_mul]`. Conclude with `sum_mem fun k _ => mul_mem (hx k) (hi2 k)`. Simplify using `only [dotProduct, map_sum, map_mul]`. Conclude with `sum_mem fun k _ => mul_mem (hi1 k) (hi2 k)`.

Establish `hx' : ¬ ∀ k, evFin F v ((x + w.1) k) ∈ O` using `fun h => hx fun k => by`. Use `sub_mem (h k) (hi1 k)` as an intermediate fact. Rewrite `this` using `[Pi.add_apply, map_add, add_sub_cancel_right]`. Then use the resulting hypothesis. Rewrite using `[Set.indicator_of_notMem (show (fun i => evFin F v ((x + w.1) i)) ∉ {y : κ → Fv F v | ∀ k, y k ∈ O} from hx'), Set.indicator_of_notMem (show (fun i => evFin F v (x i)) ∉ {y : κ → Fv F v | ∀ k, y k ∈ O} from hx)]`. Simplify using the standard rewrite rules.
-/
theorem acts_indicator {κ : Type} [Fintype κ] {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F}
    (d : Darboux B κ) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (γ : W)
    (hψ : ∀ c ∈ v.adicCompletionIntegers F, psiLoc ψ v c = 1)
    (h2 : algebraMap F (Fv F v) (1 / 2) ∈ v.adicCompletionIntegers F)
    (ha1 : ∀ k, At (evFin F v) ((d.e γ).1 k)) (ha2 : ∀ k, At (evFin F v) ((d.e γ).2 k))
    (hi1 : ∀ k, evFin F v ((d.e γ).1 k) ∈ v.adicCompletionIntegers F)
    (hi2 : ∀ k, evFin F v ((d.e γ).2 k) ∈ v.adicCompletionIntegers F) :
    Acts (evFin F v) (d.rho ψ γ) (Set.indicator {x : κ → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} 1)
      (Set.indicator {x : κ → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} 1) := by
  intro r hr
  funext x
  set w := d.e γ with hw
  have hshift : r (x + w.1) = r x := hr.1 x w.1 (at_pi ha1)
  simp only [Darboux.rho, schr, tens, hshift, ← hw]
  set O := v.adicCompletionIntegers F
  by_cases hx : ∀ k, evFin F v (x k) ∈ O
  · have hx' : ∀ k, evFin F v ((x + w.1) k) ∈ O := fun k => by
      rw [Pi.add_apply, map_add]; exact add_mem (hx k) (hi1 k)
    rw [Set.indicator_of_mem (show (fun i => evFin F v ((x + w.1) i)) ∈ {y : κ → Fv F v | ∀ k, y k ∈ O} from hx'),
      Set.indicator_of_mem (show (fun i => evFin F v (x i)) ∈ {y : κ → Fv F v | ∀ k, y k ∈ O} from hx)]
    have hat : At (evFin F v) (x ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) :=
      at_add (at_sum _ _ fun k => at_mul_left (ha2 k)) (at_mul_left (at_sum _ _ fun k => at_mul_left (ha2 k)))
    rw [psi_of_at ψ hat, hψ]
    · simp
    · rw [map_add, map_mul, invOf_two_eq, evFin_algebraMap]
      refine add_mem ?_ (mul_mem h2 ?_)
      · simp only [dotProduct, map_sum, map_mul]
        exact sum_mem fun k _ => mul_mem (hx k) (hi2 k)
      · simp only [dotProduct, map_sum, map_mul]
        exact sum_mem fun k _ => mul_mem (hi1 k) (hi2 k)
  · have hx' : ¬ ∀ k, evFin F v ((x + w.1) k) ∈ O := fun h => hx fun k => by
      have := sub_mem (h k) (hi1 k)
      rwa [Pi.add_apply, map_add, add_sub_cancel_right] at this
    rw [Set.indicator_of_notMem (show (fun i => evFin F v ((x + w.1) i)) ∉ {y : κ → Fv F v | ∀ k, y k ∈ O} from hx'),
      Set.indicator_of_notMem (show (fun i => evFin F v (x i)) ∉ {y : κ → Fv F v | ∀ k, y k ∈ O} from hx)]
    simp

end GlobalTheory.VacIndic

namespace GlobalTheory.VacIndic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
The claim follows from `map_smul (cA σ) c z`.
-/
theorem cA_smul (σ : E →ₐ[F] E) (c : AF F) (z : AE F E) : cA σ (c • z) = c • cA σ z := map_smul (cA σ) c z

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cA_inclR (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := rfl

/- English proof (translation)
Use `show c • ((1 : AF F) ⊗ₜ[F] e) = c ⊗ₜ[F] e`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`.
-/
theorem smul_inclR_eq (c : AF F) (e : E) : c • inclR (F := F) (AF F) e = c ⊗ₜ[F] e := by
  show c • ((1 : AF F) ⊗ₜ[F] e) = c ⊗ₜ[F] e
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/- English proof (translation)
Use `show Algebra.trace (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) = _`. Rewrite using `[Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]`.
-/
theorem trace_inclR [FiniteDimensional F E] (e : E) :
    Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) e) = algebraMap F (AF F) (Algebra.trace F E e) := by
  show Algebra.trace (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) = _
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

variable {n d : ℕ}

/- English proof (translation)
Simplify using `only [hTens, incM, Matrix.smul_apply, Matrix.map_apply, map_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[cA_smul, cA_inclR, map_mul, map_mul, map_mul, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul]`.
-/
theorem hTens_smul_incM (σ : E →ₐ[F] E) (A : Matrix (Fin n) (Fin n) E) (B : Matrix (Fin d) (Fin d) E)
    (a a' : AF F) (x y : Matrix (Fin n) (Fin d) E) :
    hTens (cA σ) (incM F A) (incM F B) (a • incM F x) (a' • incM F y) =
      (a * a') • inclR (F := F) (AF F) (hTens σ A B x y) := by
  simp only [hTens, incM, Matrix.smul_apply, Matrix.map_apply, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => ?_
  rw [cA_smul, cA_inclR, map_mul, map_mul, map_mul, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc,
    mul_smul_comm, smul_smul]

/- English proof (translation)
Rewrite using `[symp, hTens_smul_incM, mul_smul_comm, map_smul, ← map_mul, trace_inclR, smul_eq_mul]`. Both sides reduce to the same expression.
-/
theorem symp_smul_incM (σ : E →ₐ[F] E) (θ : E) (A : Matrix (Fin n) (Fin n) E) (B : Matrix (Fin d) (Fin d) E)
    (a a' : AF F) (x y : Matrix (Fin n) (Fin d) E) :
    symp (cA σ) (inclR (F := F) (AF F) θ) (incM F A) (incM F B) (a • incM F x) (a' • incM F y) =
      a * a' * algebraMap F (AF F) (symp σ θ A B x y) := by
  rw [symp, hTens_smul_incM, mul_smul_comm, map_smul, ← map_mul, trace_inclR, smul_eq_mul]
  rfl

end GlobalTheory.VacIndic

namespace GlobalTheory.VacIndic

section SympAdd

variable {R E' : Type} [CommRing R] [CommRing E'] [Algebra R E'] (c : E' →ₐ[R] E') (ξ : E')
  {α β : Type} [Fintype α] [Fintype β] (JA : Matrix α α E') (JB : Matrix β β E')

/- English proof (translation)
Simplify using `only [symp, hTens, Matrix.add_apply, add_mul, Finset.sum_add_distrib, mul_add, map_add]`.
-/
theorem symp_add_left (x x' y : Matrix α β E') :
    symp c ξ JA JB (x + x') y = symp c ξ JA JB x y + symp c ξ JA JB x' y := by
  simp only [symp, hTens, Matrix.add_apply, add_mul, Finset.sum_add_distrib, mul_add, map_add]

/- English proof (translation)
Simplify using `only [symp, hTens, Matrix.add_apply, map_add, mul_add, Finset.sum_add_distrib]`.
-/
theorem symp_add_right (x y y' : Matrix α β E') :
    symp c ξ JA JB x (y + y') = symp c ξ JA JB x y + symp c ξ JA JB x y' := by
  simp only [symp, hTens, Matrix.add_apply, map_add, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [symp, hTens, Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib, mul_neg, map_neg]`.
-/
theorem symp_neg_left (x y : Matrix α β E') : symp c ξ JA JB (-x) y = -symp c ξ JA JB x y := by
  simp only [symp, hTens, Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib, mul_neg, map_neg]

/- English proof (translation)
Simplify using `only [symp, hTens, Matrix.neg_apply, map_neg, mul_neg, Finset.sum_neg_distrib]`.
-/
theorem symp_neg_right (x y : Matrix α β E') : symp c ξ JA JB x (-y) = -symp c ξ JA JB x y := by
  simp only [symp, hTens, Matrix.neg_apply, map_neg, mul_neg, Finset.sum_neg_distrib]

/- English proof (translation)
Simplify using `only [symp, hTens, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero, map_zero]`.
-/
theorem symp_zero_left (y : Matrix α β E') : symp c ξ JA JB 0 y = 0 := by
  simp only [symp, hTens, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero, map_zero]

/- English proof (translation)
Simplify using `only [symp, hTens, Matrix.zero_apply, map_zero, mul_zero, Finset.sum_const_zero]`.
-/
theorem symp_zero_right (x : Matrix α β E') : symp c ξ JA JB x 0 = 0 := by
  simp only [symp, hTens, Matrix.zero_apply, map_zero, mul_zero, Finset.sum_const_zero]

end SympAdd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨sX, hsX⟩` from `hX.fg.restrictScalars (R := ℤ)`. Take `⟨sY, hsY⟩` from `hY.fg.restrictScalars (R := ℤ)`. Use `⟨(sX ×ˢ sY).image fun p => vecMulVec p.1 p.2, fun x hx y hy => ?_⟩` and prove the remaining obligations. Establish `hx' : x ∈ Submodule.span ℤ (sX : Set (Fin n → E))` using `by rw [hsX]; exact hx`. Establish `hy' : y ∈ Submodule.span ℤ (sY : Set (Fin d → E))` using `by rw [hsY]; exact hy`.

Use `set C := AddSubgroup.closure (((sX ×ˢ sY).image fun p => vecMulVec p.1 p.2 : Finset _) : Set (Matrix (Fin n) (Fin d) E))`. Establish `inner : ∀ x ∈ sX, ∀ y ∈ Submodule.span ℤ (sY : Set (Fin d → E)), vecMulVec x y ∈ C`. Introduce `x hx y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy => exact AddSubgroup.subset_closure (Finset.mem_coe.2 (Finset.mem_image.2 ⟨(x, y), Finset.mem_product.2 ⟨hx, hy⟩, rfl⟩))`.

Consider the case `zero => rw [show vecMulVec x (0 : Fin d → E) = 0 by ext; simp [vecMulVec_apply]]; exact zero_mem _`. Consider the case `add y y' _ _ h h' => rw [show vecMulVec x (y + y') = vecMulVec x y + vecMulVec x y' by ext; simp [vecMulVec_apply, mul_add]]; exact add_mem h h'`. Consider the case `smul m y _ h => rw [show vecMulVec x (m • y) = m • vecMulVec x y by ext; simp [vecMulVec_apply, mul_left_comm]]; exact zsmul_mem h m`. Use `clear hx`. Proceed by induction on `hx' using Submodule.span_induction with`.

Consider the case `mem x hxs => exact inner x hxs y hy'`. Consider the case `zero => rw [show vecMulVec (0 : Fin n → E) y = 0 by ext; simp [vecMulVec_apply]]; exact zero_mem _`. Consider the case `add x x' _ _ h h' => rw [show vecMulVec (x + x') y = vecMulVec x y + vecMulVec x' y by ext; simp [vecMulVec_apply, add_mul]]; exact add_mem h h'`. Consider the case `smul m x _ h => rw [show vecMulVec (m • x) y = m • vecMulVec x y by ext; simp [vecMulVec_apply, mul_assoc]]; exact zsmul_mem h m`.
-/
theorem exists_gen {n d : ℕ} (LX : Submodule (𝓞 E) (Fin n → E)) (LY : Submodule (𝓞 E) (Fin d → E))
    (hX : LX.IsLattice E) (hY : LY.IsLattice E) :
    ∃ G : Finset (Matrix (Fin n) (Fin d) E), ∀ x ∈ LX, ∀ y ∈ LY, vecMulVec x y ∈ AddSubgroup.closure (G : Set _) := by
  classical
  obtain ⟨sX, hsX⟩ := hX.fg.restrictScalars (R := ℤ)
  obtain ⟨sY, hsY⟩ := hY.fg.restrictScalars (R := ℤ)
  refine ⟨(sX ×ˢ sY).image fun p => vecMulVec p.1 p.2, fun x hx y hy => ?_⟩
  have hx' : x ∈ Submodule.span ℤ (sX : Set (Fin n → E)) := by rw [hsX]; exact hx
  have hy' : y ∈ Submodule.span ℤ (sY : Set (Fin d → E)) := by rw [hsY]; exact hy
  set C := AddSubgroup.closure (((sX ×ˢ sY).image fun p => vecMulVec p.1 p.2 : Finset _) : Set (Matrix (Fin n) (Fin d) E))
  have inner : ∀ x ∈ sX, ∀ y ∈ Submodule.span ℤ (sY : Set (Fin d → E)), vecMulVec x y ∈ C := by
    intro x hx y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact AddSubgroup.subset_closure (Finset.mem_coe.2 (Finset.mem_image.2 ⟨(x, y), Finset.mem_product.2 ⟨hx, hy⟩, rfl⟩))
    | zero => rw [show vecMulVec x (0 : Fin d → E) = 0 by ext; simp [vecMulVec_apply]]; exact zero_mem _
    | add y y' _ _ h h' => rw [show vecMulVec x (y + y') = vecMulVec x y + vecMulVec x y' by ext; simp [vecMulVec_apply, mul_add]]; exact add_mem h h'
    | smul m y _ h => rw [show vecMulVec x (m • y) = m • vecMulVec x y by ext; simp [vecMulVec_apply, mul_left_comm]]; exact zsmul_mem h m
  clear hx
  induction hx' using Submodule.span_induction with
  | mem x hxs => exact inner x hxs y hy'
  | zero => rw [show vecMulVec (0 : Fin n → E) y = 0 by ext; simp [vecMulVec_apply]]; exact zero_mem _
  | add x x' _ _ h h' => rw [show vecMulVec (x + x') y = vecMulVec x y + vecMulVec x' y by ext; simp [vecMulVec_apply, add_mul]]; exact add_mem h h'
  | smul m x _ h => rw [show vecMulVec (m • x) y = m • vecMulVec x y by ext; simp [vecMulVec_apply, mul_assoc]]; exact zsmul_mem h m

end GlobalTheory.VacIndic

namespace GlobalTheory.VacIndic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Introduce `u _` and use `smul_zero u`.
-/
theorem at_zero {v : HeightOneSpectrum (𝓞 F)} : At (evFin F v) (0 : AF F) := fun u _ => smul_zero u

/- English proof (translation)
Introduce `u hu` and use `by rw [smul_neg, ha u hu, neg_zero]`.
-/
theorem at_neg {v : HeightOneSpectrum (𝓞 F)} {a : AF F} (ha : At (evFin F v) a) : At (evFin F v) (-a) :=
  fun u hu => by rw [smul_neg, ha u hu, neg_zero]

/- English proof (translation)
Rewrite using `[mul_comm]`. Conclude with `at_mul_left ha`.
-/
theorem at_mul_right {v : HeightOneSpectrum (𝓞 F)} {a b : AF F} (ha : At (evFin F v) a) : At (evFin F v) (a * b) := by
  rw [mul_comm]; exact at_mul_left ha

/- English proof (translation)
Use `ext`. Simplify using `[incM]`.
-/
theorem incM_add {m n : Type} (x y : Matrix m n E) : incM F (x + y) = incM F x + incM F y := by
  ext; simp [incM]

/- English proof (translation)
Use `ext`. Simplify using `[incM]`.
-/
theorem incM_neg {m n : Type} (x : Matrix m n E) : incM F (-x) = -incM F x := by
  ext; simp [incM]

/- English proof (translation)
Use `ext`. Simplify using `[incM]`.
-/
theorem incM_zero {m n : Type} : incM F (0 : Matrix m n E) = 0 := by
  ext; simp [incM]

variable {n d : ℕ}

/- English proof (translation)
Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `z ⟨a, ha, hai, x, hx, y, hy, rfl⟩`. It suffices to establish `key : ∀ m ∈ AddSubgroup.closure (G : Set (Matrix (Fin n) (Fin d) E)), a • incM F m ∈ AddSubgroup.closure {z | ∃ a : AF F, At (evFin F v) a ∧ evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ g ∈ G, z = a • incM F g} from key _ (hG x hx y hy)`. Introduce `m hm`. Proceed by induction on `hm using AddSubgroup.closure_induction with`.

Consider the case `mem g hg => exact AddSubgroup.subset_closure ⟨a, ha, hai, g, hg, rfl⟩`. Consider the case `zero => rw [incM_zero, smul_zero]`. Conclude with `zero_mem _`. Consider the case `add g g' _ _ h h' => rw [incM_add, smul_add]`. Conclude with `add_mem h h'`.

Consider the case `neg g _ h => rw [incM_neg, smul_neg]`. Conclude with `neg_mem h`.
-/
theorem latAtV_le (X : Spc F E n) (Y : Spc F E d) (G : Finset (Matrix (Fin n) (Fin d) E))
    (hG : ∀ x ∈ X.L, ∀ y ∈ Y.L, vecMulVec x y ∈ AddSubgroup.closure (G : Set _)) (v : HeightOneSpectrum (𝓞 F)) :
    latAtV X Y v ≤ AddSubgroup.closure {z | ∃ a : AF F, At (evFin F v) a ∧ evFin F v a ∈ v.adicCompletionIntegers F ∧
      ∃ g ∈ G, z = a • incM F g} := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro z ⟨a, ha, hai, x, hx, y, hy, rfl⟩
  suffices key : ∀ m ∈ AddSubgroup.closure (G : Set (Matrix (Fin n) (Fin d) E)), a • incM F m ∈ AddSubgroup.closure
      {z | ∃ a : AF F, At (evFin F v) a ∧ evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ g ∈ G, z = a • incM F g} from
    key _ (hG x hx y hy)
  intro m hm
  induction hm using AddSubgroup.closure_induction with
  | mem g hg => exact AddSubgroup.subset_closure ⟨a, ha, hai, g, hg, rfl⟩
  | zero => rw [incM_zero, smul_zero]; exact zero_mem _
  | add g g' _ _ h h' => rw [incM_add, smul_add]; exact add_mem h h'
  | neg g _ h => rw [incM_neg, smul_neg]; exact neg_mem h

end GlobalTheory.VacIndic

namespace GlobalTheory.VacIndic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨θ, hθ⟩` from `hθ`. Take `⟨G, hG⟩` from `exists_gen X.L Y.L hX.lat hY.lat`. Use `choose yc zc hc using hrat`. Establish `e1` using `eventually_psiLoc_eq_one B.ψ hB.std.1`. Establish `e2` using `eventually_int (F := F) (1 / 2)`.

Establish `e3 : ∀ᶠ v in cofinite, ∀ g ∈ G, ∀ k, algebraMap F (Fv F v) (yc g k) ∈ v.adicCompletionIntegers F ∧ algebraMap F (Fv F v) (zc g k) ∈ v.adicCompletionIntegers F`. Use `(Filter.eventually_all_finset G).2 fun g _ => Filter.eventually_all.2 fun k => ?_` and prove the remaining obligations. Conclude with `(eventually_int (yc g k)).and (eventually_int (zc g k))`. Establish `e4 : ∀ᶠ v in cofinite, ∀ g ∈ G, ∀ g' ∈ G, algebraMap F (Fv F v) (symp σ (θ : E) X.J Y.J g g') ∈ v.adicCompletionIntegers F`. Use `(Filter.eventually_all_finset G).2 fun g _ => (Filter.eventually_all_finset G).2 fun g' _ => ?_` and prove the remaining obligations.

Conclude with `eventually_int _`. Use `filter_upwards [e1, e2, e3, e4] with v h1 h2 h3 h4`. Use `set O := v.adicCompletionIntegers F`. Use `set T : Set (Matrix (Fin n) (Fin d) (AE F E)) := {z | ∃ a : AF F, At (evFin F v) a ∧ evFin F v a ∈ O ∧ ∃ g ∈ G, z = a • incM F g} with hT`. Establish `hA : ∀ z ∈ AddSubgroup.closure T, ∀ k, At (evFin F v) ((co.e z).1 k) ∧ At (evFin F v) ((co.e z).2 k) ∧ evFin F v ((co.e z).1 k) ∈ O ∧ evFin F v ((co.e z).2 k) ∈ O`.

Introduce `z hz`. Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, hai, g, hg, rfl⟩` from `hz`. Introduce `k`.

Rewrite using `[map_smul, hc g]`. Simplify using `only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, map_mul, evFin_algebraMap]`. Conclude with `⟨at_mul_right ha, at_mul_right ha, mul_mem hai (h3 g hg k).1, mul_mem hai (h3 g hg k).2⟩`. Consider the case `zero`. Introduce `k`.

Simplify using `only [map_zero, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply]`. Conclude with `⟨at_zero, at_zero, zero_mem _, zero_mem _⟩`. Consider the case `add z z' _ _ h h'`. Introduce `k`. Simplify using `only [map_add, Prod.fst_add, Prod.snd_add, Pi.add_apply]`.

Conclude with `⟨at_add (h k).1 (h' k).1, at_add (h k).2.1 (h' k).2.1, add_mem (h k).2.2.1 (h' k).2.2.1, add_mem (h k).2.2.2 (h' k).2.2.2⟩`. Consider the case `neg z _ h`. Introduce `k`. Simplify using `only [map_neg, Prod.fst_neg, Prod.snd_neg, Pi.neg_apply]`. Conclude with `⟨at_neg (h k).1, at_neg (h k).2.1, neg_mem (h k).2.2.1, neg_mem (h k).2.2.2⟩`.

Use `set S := symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F Y.J) with hS`. Establish `hB1 : ∀ z ∈ T, ∀ z' ∈ AddSubgroup.closure T, At (evFin F v) (S z z') ∧ evFin F v (S z z') ∈ O`. Introduce `z hz z' hz'`. Take `⟨a, ha, hai, g, hg, rfl⟩` from `hz`. Proceed by induction on `hz' using AddSubgroup.closure_induction with`.

Consider the case `mem z' hz'`. Take `⟨a', ha', hai', g', hg', rfl⟩` from `hz'`. Rewrite using `[hS, symp_smul_incM, map_mul, map_mul, evFin_algebraMap]`. Conclude with `⟨at_mul_right (at_mul_right ha), mul_mem (mul_mem hai hai') (h4 g hg g' hg')⟩`. Consider the case `zero => rw [hS, symp_zero_right, map_zero]`.

Conclude with `⟨at_zero, zero_mem _⟩`. Consider the case `add z₁ z₂ _ _ h h' => rw [hS, symp_add_right, map_add]`. Conclude with `⟨at_add h.1 h'.1, add_mem h.2 h'.2⟩`. Consider the case `neg z₁ _ h => rw [hS, symp_neg_right, map_neg]`. Conclude with `⟨at_neg h.1, neg_mem h.2⟩`.

Establish `hB2 : ∀ z ∈ AddSubgroup.closure T, ∀ z' ∈ AddSubgroup.closure T, At (evFin F v) (S z z') ∧ evFin F v (S z z') ∈ O`. Introduce `z hz z' hz'`. Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz => exact hB1 z hz z' hz'`. Consider the case `zero => rw [hS, symp_zero_left, map_zero]`.

Conclude with `⟨at_zero, zero_mem _⟩`. Consider the case `add z₁ z₂ _ _ h h' => rw [hS, symp_add_left, map_add]`. Conclude with `⟨at_add h.1 h'.1, add_mem h.2 h'.2⟩`. Consider the case `neg z₁ _ h => rw [hS, symp_neg_left, map_neg]`. Conclude with `⟨at_neg h.1, neg_mem h.2⟩`.

Use `⟨indicator_int_mem_SB v, indicator_int_ne_zero v, θ, hθ, fun γ hγ => ?_⟩` and prove the remaining obligations. Establish `hγ'` using `latAtV_le X Y G hG v hγ`. Establish `hval : B.ψ (⅟(2 : AF F) * S γ γ) = 1`. Establish `hat` using `hB2 γ hγ' γ hγ'`. Rewrite using `[psi_of_at B.ψ (at_mul_left hat.1)]`.

Use `h1 _ ?_` and prove the remaining obligations. Rewrite using `[map_mul, invOf_two_eq, evFin_algebraMap]`. Conclude with `mul_mem h2 hat.2`. Rewrite using `[← hS, hval, one_smul]`. Conclude with `acts_indicator co B.ψ v γ h1 h2 (fun k => (hA γ hγ' k).1) (fun k => (hA γ hγ' k).2.1) (fun k => (hA γ hγ' k).2.2.1) (fun k => (hA γ hγ' k).2.2.2)`.
-/
theorem isVac_indicator_of_theta {σ : E →ₐ[F] E} (B : Base F E) (hB : B.IsGood σ) {n d : ℕ} (X : Spc F E n)
    (Y : Spc F E d) (r s r' s' : ℕ) (hX : X.IsHerm σ B r s) (hY : Y.IsSkew σ B r' s')
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J)) (Fin n × Fin d))
    (hrat : ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k)))
    (hθ : ∃ θ : 𝓞 E, (θ : E) + σ θ = 1) :
    ∀ᶠ v in Filter.cofinite, Model.IsVac (Model.mk (σ := σ) (X := X) (W := Y) co (fun _ => 0) 0 ∅) B.ψ v
      (Set.indicator {x | ∀ k, x k ∈ v.adicCompletionIntegers F} 1) := by
  classical
  obtain ⟨θ, hθ⟩ := hθ
  obtain ⟨G, hG⟩ := exists_gen X.L Y.L hX.lat hY.lat
  choose yc zc hc using hrat
  have e1 := eventually_psiLoc_eq_one B.ψ hB.std.1
  have e2 := eventually_int (F := F) (1 / 2)
  have e3 : ∀ᶠ v in cofinite, ∀ g ∈ G, ∀ k, algebraMap F (Fv F v) (yc g k) ∈ v.adicCompletionIntegers F ∧
      algebraMap F (Fv F v) (zc g k) ∈ v.adicCompletionIntegers F := by
    refine (Filter.eventually_all_finset G).2 fun g _ => Filter.eventually_all.2 fun k => ?_
    exact (eventually_int (yc g k)).and (eventually_int (zc g k))
  have e4 : ∀ᶠ v in cofinite, ∀ g ∈ G, ∀ g' ∈ G,
      algebraMap F (Fv F v) (symp σ (θ : E) X.J Y.J g g') ∈ v.adicCompletionIntegers F := by
    refine (Filter.eventually_all_finset G).2 fun g _ => (Filter.eventually_all_finset G).2 fun g' _ => ?_
    exact eventually_int _
  filter_upwards [e1, e2, e3, e4] with v h1 h2 h3 h4
  set O := v.adicCompletionIntegers F
  set T : Set (Matrix (Fin n) (Fin d) (AE F E)) :=
    {z | ∃ a : AF F, At (evFin F v) a ∧ evFin F v a ∈ O ∧ ∃ g ∈ G, z = a • incM F g} with hT

  have hA : ∀ z ∈ AddSubgroup.closure T, ∀ k, At (evFin F v) ((co.e z).1 k) ∧ At (evFin F v) ((co.e z).2 k) ∧
      evFin F v ((co.e z).1 k) ∈ O ∧ evFin F v ((co.e z).2 k) ∈ O := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, hai, g, hg, rfl⟩ := hz
      intro k
      rw [map_smul, hc g]
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, map_mul, evFin_algebraMap]
      exact ⟨at_mul_right ha, at_mul_right ha, mul_mem hai (h3 g hg k).1, mul_mem hai (h3 g hg k).2⟩
    | zero =>
      intro k
      simp only [map_zero, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply]
      exact ⟨at_zero, at_zero, zero_mem _, zero_mem _⟩
    | add z z' _ _ h h' =>
      intro k
      simp only [map_add, Prod.fst_add, Prod.snd_add, Pi.add_apply]
      exact ⟨at_add (h k).1 (h' k).1, at_add (h k).2.1 (h' k).2.1, add_mem (h k).2.2.1 (h' k).2.2.1,
        add_mem (h k).2.2.2 (h' k).2.2.2⟩
    | neg z _ h =>
      intro k
      simp only [map_neg, Prod.fst_neg, Prod.snd_neg, Pi.neg_apply]
      exact ⟨at_neg (h k).1, at_neg (h k).2.1, neg_mem (h k).2.2.1, neg_mem (h k).2.2.2⟩

  set S := symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F Y.J) with hS
  have hB1 : ∀ z ∈ T, ∀ z' ∈ AddSubgroup.closure T, At (evFin F v) (S z z') ∧ evFin F v (S z z') ∈ O := by
    intro z hz z' hz'
    obtain ⟨a, ha, hai, g, hg, rfl⟩ := hz
    induction hz' using AddSubgroup.closure_induction with
    | mem z' hz' =>
      obtain ⟨a', ha', hai', g', hg', rfl⟩ := hz'
      rw [hS, symp_smul_incM, map_mul, map_mul, evFin_algebraMap]
      exact ⟨at_mul_right (at_mul_right ha), mul_mem (mul_mem hai hai') (h4 g hg g' hg')⟩
    | zero => rw [hS, symp_zero_right, map_zero]; exact ⟨at_zero, zero_mem _⟩
    | add z₁ z₂ _ _ h h' => rw [hS, symp_add_right, map_add]; exact ⟨at_add h.1 h'.1, add_mem h.2 h'.2⟩
    | neg z₁ _ h => rw [hS, symp_neg_right, map_neg]; exact ⟨at_neg h.1, neg_mem h.2⟩
  have hB2 : ∀ z ∈ AddSubgroup.closure T, ∀ z' ∈ AddSubgroup.closure T,
      At (evFin F v) (S z z') ∧ evFin F v (S z z') ∈ O := by
    intro z hz z' hz'
    induction hz using AddSubgroup.closure_induction with
    | mem z hz => exact hB1 z hz z' hz'
    | zero => rw [hS, symp_zero_left, map_zero]; exact ⟨at_zero, zero_mem _⟩
    | add z₁ z₂ _ _ h h' => rw [hS, symp_add_left, map_add]; exact ⟨at_add h.1 h'.1, add_mem h.2 h'.2⟩
    | neg z₁ _ h => rw [hS, symp_neg_left, map_neg]; exact ⟨at_neg h.1, neg_mem h.2⟩
  refine ⟨indicator_int_mem_SB v, indicator_int_ne_zero v, θ, hθ, fun γ hγ => ?_⟩
  have hγ' := latAtV_le X Y G hG v hγ
  have hval : B.ψ (⅟(2 : AF F) * S γ γ) = 1 := by
    have hat := hB2 γ hγ' γ hγ'
    rw [psi_of_at B.ψ (at_mul_left hat.1)]
    refine h1 _ ?_
    rw [map_mul, invOf_two_eq, evFin_algebraMap]
    exact mul_mem h2 hat.2
  rw [← hS, hval, one_smul]
  exact acts_indicator co B.ψ v γ h1 h2 (fun k => (hA γ hγ' k).1) (fun k => (hA γ hγ' k).2.1)
    (fun k => (hA γ hγ' k).2.2.1) (fun k => (hA γ hγ' k).2.2.2)

end GlobalTheory.VacIndic

namespace GlobalTheory.VacIndic

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B hB n d X Y r s r' s' hX hY co hrat`. Conclude with `isVac_indicator_of_theta B hB X Y r s r' s' hX hY co hrat (GlobalTheory.exists_int_add_conj_eq_one_of_base_good B hB)`.
-/
theorem eventually_isVac_indicator : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E), B.IsGood σ → ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∀ (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J)) (Fin n × Fin d)), (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F, co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k))) →
    ∀ᶠ v in Filter.cofinite, Model.IsVac (Model.mk (σ := σ) (X := X) (W := Y) co (fun _ => 0) 0 ∅) B.ψ v
      (Set.indicator {x | ∀ k, x k ∈ v.adicCompletionIntegers F} 1) := by
  intro F E _ _ _ _ _ σ B hB n d X Y r s r' s' hX hY co hrat
  exact isVac_indicator_of_theta B hB X Y r s r' s' hX hY co hrat (GlobalTheory.exists_int_add_conj_eq_one_of_base_good B hB)

end GlobalTheory.VacIndic
