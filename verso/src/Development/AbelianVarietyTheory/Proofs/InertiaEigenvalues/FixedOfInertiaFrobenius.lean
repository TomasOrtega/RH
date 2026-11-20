import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AxSenTateComplexPadicFixedClosure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.RegularDense

/- English proof (translation)
Introduce `l hl F hF y hI hFy g`. Set `H : Subgroup (GQ l)` to `{ carrier := {h | Per.σC h y = y} mul_mem' := fun {a b} ha hb => by show Per.σC (a * b) y = y`. Establish `ha' : Per.σC a y = y` using `ha`. Establish `hb' : Per.σC b y = y` using `hb`. Rewrite using `[GlobalTheory.RingBasics.σC_mul, hb', ha']`.

Use the proof step `one_mem' := by show Per.σC 1 y = y`. Rewrite using `[GlobalTheory.RingBasics.σC_one]`. Use the proof step `inv_mem' := fun {a} ha => by show Per.σC a⁻¹ y = y`. Establish `ha' : Per.σC a y = y` using `ha`. Use `conv_lhs => rw [← ha']`.

Rewrite using `[← GlobalTheory.RingBasics.σC_mul, inv_mul_cancel, GlobalTheory.RingBasics.σC_one] }`. Establish `hy` using `ax_sen_tate l H y (fun h hh => hh)`. Establish `hcont : Continuous (fun z : ℂ_[l] => Per.σC g z)`. Use `Isometry.continuous (Isometry.of_dist_eq fun a b => ?_)` and prove the remaining obligations. Rewrite using `[dist_eq_norm, dist_eq_norm, ← map_sub, GlobalTheory.RingBasics.norm_σC]`.

Establish `hcl : IsClosed {z : ℂ_[l] | Per.σC g z = z}` using `isClosed_eq hcont continuous_id`. Use `closure_minimal ?_ hcl hy` and prove the remaining obligations. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Use `show Per.σC g (z : ℂ_[l]) = z`. Rewrite using `[GlobalTheory.RingBasics.σC_coe]`.

Use `congr 1`. Establish `hzK : z ∈ MaximalUnramifiedExtension l`. Rewrite using `[← InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension l), IntermediateField.mem_fixedField_iff]`. Introduce `h hh`. Conclude with `hz h (hI h hh)`.

Establish `hFz : F z = z` using `hz F hFy`. Establish `hpow : ∀ n : ℕ, (F ^ n) z = z` using `fun n => by`. Proceed by induction on `n with`. Consider the case `zero => rfl`. Consider the case `succ n ih => rw [pow_succ, AlgEquiv.mul_apply, hFz, ih]`.

Take `⟨m, hm, hlm, hH⟩` from `FrobLaws.exists_level hzK`. Establish `hr : ∀ (n : ℕ) (ζ : Om l), ζ ^ m = 1 → (F ^ n) ζ = ζ ^ (l ^ n)` using `fun n ζ hζ => by`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`.

Rewrite using `[pow_succ', AlgEquiv.mul_apply, ih, map_pow, hF ζ m hm hlm hζ, ← pow_mul, pow_succ']`. Take `⟨n, hn⟩` from `FrobLaws.gal_root g hm hlm`. Rewrite using `[hH g (F ^ n) fun ζ hζ => by rw [hn ζ hζ, hr n ζ hζ], hpow]`.
-/
theorem fixed_of_inertia_frobenius : ∀ (l : ℕ) [Fact l.Prime] (F : GQ l),
    (∀ (x : Om l) (m : ℕ), 0 < m → ¬ l ∣ m → x ^ m = 1 → F x = x ^ l) →
    ∀ y : ℂ_[l], (∀ g ∈ (MaximalUnramifiedExtension l).fixingSubgroup, Per.σC g y = y) → Per.σC F y = y →
      ∀ g : GQ l, Per.σC g y = y := by
  intro l hl F hF y hI hFy g
  let H : Subgroup (GQ l) :=
    { carrier := {h | Per.σC h y = y}
      mul_mem' := fun {a b} ha hb => by
        show Per.σC (a * b) y = y
        have ha' : Per.σC a y = y := ha
        have hb' : Per.σC b y = y := hb
        rw [GlobalTheory.RingBasics.σC_mul, hb', ha']
      one_mem' := by
        show Per.σC 1 y = y
        rw [GlobalTheory.RingBasics.σC_one]
      inv_mem' := fun {a} ha => by
        show Per.σC a⁻¹ y = y
        have ha' : Per.σC a y = y := ha
        conv_lhs => rw [← ha']
        rw [← GlobalTheory.RingBasics.σC_mul, inv_mul_cancel, GlobalTheory.RingBasics.σC_one] }
  have hy := ax_sen_tate l H y (fun h hh => hh)
  have hcont : Continuous (fun z : ℂ_[l] => Per.σC g z) := by
    refine Isometry.continuous (Isometry.of_dist_eq fun a b => ?_)
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, GlobalTheory.RingBasics.norm_σC]
  have hcl : IsClosed {z : ℂ_[l] | Per.σC g z = z} := isClosed_eq hcont continuous_id
  refine closure_minimal ?_ hcl hy
  rintro _ ⟨z, hz, rfl⟩
  show Per.σC g (z : ℂ_[l]) = z
  rw [GlobalTheory.RingBasics.σC_coe]
  congr 1
  have hzK : z ∈ MaximalUnramifiedExtension l := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension l), IntermediateField.mem_fixedField_iff]
    intro h hh
    exact hz h (hI h hh)
  have hFz : F z = z := hz F hFy
  have hpow : ∀ n : ℕ, (F ^ n) z = z := fun n => by
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, AlgEquiv.mul_apply, hFz, ih]
  obtain ⟨m, hm, hlm, hH⟩ := FrobLaws.exists_level hzK
  have hr : ∀ (n : ℕ) (ζ : Om l), ζ ^ m = 1 → (F ^ n) ζ = ζ ^ (l ^ n) := fun n ζ hζ => by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, hF ζ m hm hlm hζ, ← pow_mul, pow_succ']
  obtain ⟨n, hn⟩ := FrobLaws.gal_root g hm hlm
  rw [hH g (F ^ n) fun ζ hζ => by rw [hn ζ hζ, hr n ζ hζ], hpow]

end GlobalTheory.RegularDense
