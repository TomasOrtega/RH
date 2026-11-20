import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatMod
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.VacExApp
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.VacExA
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceDualB
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LatticeVariant

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

/- English proof (translation)
Take `⟨⟨b, hb⟩, h⟩` from `IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 D.host.E)) s`. Use `⟨b, nonZeroDivisors.ne_zero hb, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `h x hx`. Conclude with `⟨y, by rw [show ((y : 𝓞 D.host.E) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E y from rfl, hy, Algebra.smul_def]⟩`.
-/
theorem lsd_den (s : Finset D.host.E) :
    ∃ d : 𝓞 D.host.E, d ≠ 0 ∧ ∀ x ∈ s, ∃ y : 𝓞 D.host.E, (d : D.host.E) * x = y := by
  obtain ⟨⟨b, hb⟩, h⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 D.host.E)) s
  refine ⟨b, nonZeroDivisors.ne_zero hb, fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := h x hx
  exact ⟨y, by rw [show ((y : 𝓞 D.host.E) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E y from rfl, hy,
    Algebra.smul_def]⟩

/- English proof (translation)
Take `⟨d, hd, h⟩` from `lsd_den (D := D) s`. Establish `hm : ∀ a b : 𝓞 D.host.E, ((a * b : 𝓞 D.host.E) : D.host.E) = (a : D.host.E) * (b : D.host.E)` using `fun a b => map_mul (algebraMap (𝓞 D.host.E) D.host.E) a b`. Take `⟨r, hr⟩` from `fixed_int (d * starO d) (by`. Rewrite using `[hm, coe_starO, star_mul', star_star, mul_comm])`. Use `⟨r, ?_, fun x hx => ?_⟩` and prove the remaining obligations.

Introduce and unpack `rfl`. Establish `: ((d * starO d : 𝓞 D.host.E) : D.host.E) = 0` using `by rw [← hr]; simp`. Rewrite `this` using `[hm, coe_starO, mul_eq_zero, star_eq_zero]`. Establish `hd' : (d : D.host.E) ≠ 0` using `fun h0 => hd (FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E (by rw [map_zero]; exact h0))`. Apply the tactic sequence `rcases this with h0 | h0 <;> exact hd' h0`.

Take `⟨y, hy⟩` from `h x hx`. Use `⟨starO d * y, ?_⟩` and prove the remaining obligations. Rewrite using `[hr, hm, coe_starO, hm, coe_starO, ← hy]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lsd_denF (s : Finset D.host.E) :
    ∃ r : 𝓞 D.host.F, r ≠ 0 ∧ ∀ x ∈ s, ∃ y : 𝓞 D.host.E, algebraMap D.host.F D.host.E (r : D.host.F) * x = y := by
  obtain ⟨d, hd, h⟩ := lsd_den (D := D) s
  have hm : ∀ a b : 𝓞 D.host.E, ((a * b : 𝓞 D.host.E) : D.host.E) = (a : D.host.E) * (b : D.host.E) :=
    fun a b => map_mul (algebraMap (𝓞 D.host.E) D.host.E) a b
  obtain ⟨r, hr⟩ := fixed_int (d * starO d) (by
    rw [hm, coe_starO, star_mul', star_star, mul_comm])
  refine ⟨r, ?_, fun x hx => ?_⟩
  · rintro rfl
    have : ((d * starO d : 𝓞 D.host.E) : D.host.E) = 0 := by rw [← hr]; simp
    rw [hm, coe_starO, mul_eq_zero, star_eq_zero] at this
    have hd' : (d : D.host.E) ≠ 0 := fun h0 => hd (FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E
      (by rw [map_zero]; exact h0))
    rcases this with h0 | h0 <;> exact hd' h0
  · obtain ⟨y, hy⟩ := h x hx
    refine ⟨starO d * y, ?_⟩
    rw [hr, hm, coe_starO, hm, coe_starO, ← hy]
    ring

/- English proof (translation)
Set `ω` to `NumberField.RingOfIntegers.basis D.host.E`. Set `b` to `Module.finBasis D.host.F D.host.E`. Take `⟨⟨r, hr⟩, h⟩` from `IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.F)) (Finset.univ : Finset (Module.Free.ChooseBasisIndex ℤ (𝓞 D.host.E) × Fin (Module.finrank D.host.F D.host.E))) (fun p => b.repr ((ω p.1 : 𝓞 D.host.E) : D.host.E) p.2)`. Use `⟨r, nonZeroDivisors.ne_zero hr, fun x k => ?_⟩` and prove the remaining obligations. Establish `hx : (x : D.host.E) = ∑ l, (ω.repr x l : ℤ) • ((ω l : 𝓞 D.host.E) : D.host.E)` using `by conv_lhs => rw [← ω.sum_repr x]`.

Use `push_cast`. Both sides reduce to the same expression. Establish `hl : ∀ l, ∃ y : 𝓞 D.host.F, (r : D.host.F) * b.repr ((ω l : 𝓞 D.host.E) : D.host.E) k = y`. Introduce `l`. Take `⟨y, hy⟩` from `h (l, k) (Finset.mem_univ _)`.

Conclude with `⟨y, by rw [show ((y : 𝓞 D.host.F) : D.host.F) = algebraMap (𝓞 D.host.F) D.host.F y from rfl, hy, Algebra.smul_def]⟩`. Use `choose y hy using hl`. Use `⟨∑ l, (ω.repr x l : ℤ) • y l, ?_⟩` and prove the remaining obligations. Rewrite using `[hx, map_sum, Finsupp.finset_sum_apply, Finset.mul_sum]`. Establish `hc : ((∑ l, (ω.repr x l : ℤ) • y l : 𝓞 D.host.F) : D.host.F) = ∑ l, (ω.repr x l : ℤ) • ((y l : 𝓞 D.host.F) : D.host.F)`.

Rewrite using `[show ((∑ l, (ω.repr x l : ℤ) • y l : 𝓞 D.host.F) : D.host.F) = algebraMap (𝓞 D.host.F) D.host.F (∑ l, (ω.repr x l : ℤ) • y l) from rfl, map_sum]`. Conclude with `Finset.sum_congr rfl fun l _ => map_zsmul _ _ _`. Rewrite using `[hc]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, Finsupp.smul_apply, ← hy l, zsmul_eq_mul, zsmul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem lsd_coordO : ∃ r : 𝓞 D.host.F, r ≠ 0 ∧ ∀ (x : 𝓞 D.host.E) (k : Fin (Module.finrank D.host.F D.host.E)),
    ∃ y : 𝓞 D.host.F, (r : D.host.F) * (Module.finBasis D.host.F D.host.E).repr (x : D.host.E) k = y := by
  let ω := NumberField.RingOfIntegers.basis D.host.E
  let b := Module.finBasis D.host.F D.host.E
  obtain ⟨⟨r, hr⟩, h⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.F))
    (Finset.univ : Finset (Module.Free.ChooseBasisIndex ℤ (𝓞 D.host.E) × Fin (Module.finrank D.host.F D.host.E)))
    (fun p => b.repr ((ω p.1 : 𝓞 D.host.E) : D.host.E) p.2)
  refine ⟨r, nonZeroDivisors.ne_zero hr, fun x k => ?_⟩
  have hx : (x : D.host.E) = ∑ l, (ω.repr x l : ℤ) • ((ω l : 𝓞 D.host.E) : D.host.E) := by
    conv_lhs => rw [← ω.sum_repr x]
    push_cast
    rfl
  have hl : ∀ l, ∃ y : 𝓞 D.host.F, (r : D.host.F) * b.repr ((ω l : 𝓞 D.host.E) : D.host.E) k = y := by
    intro l
    obtain ⟨y, hy⟩ := h (l, k) (Finset.mem_univ _)
    exact ⟨y, by rw [show ((y : 𝓞 D.host.F) : D.host.F) = algebraMap (𝓞 D.host.F) D.host.F y from rfl, hy,
      Algebra.smul_def]⟩
  choose y hy using hl
  refine ⟨∑ l, (ω.repr x l : ℤ) • y l, ?_⟩
  rw [hx, map_sum, Finsupp.finset_sum_apply, Finset.mul_sum]
  have hc : ((∑ l, (ω.repr x l : ℤ) • y l : 𝓞 D.host.F) : D.host.F) =
      ∑ l, (ω.repr x l : ℤ) • ((y l : 𝓞 D.host.F) : D.host.F) := by
    rw [show ((∑ l, (ω.repr x l : ℤ) • y l : 𝓞 D.host.F) : D.host.F) =
      algebraMap (𝓞 D.host.F) D.host.F (∑ l, (ω.repr x l : ℤ) • y l) from rfl, map_sum]
    exact Finset.sum_congr rfl fun l _ => map_zsmul _ _ _
  rw [hc]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_zsmul, Finsupp.smul_apply, ← hy l, zsmul_eq_mul, zsmul_eq_mul]
  ring

/- English proof (translation)
Take `⟨g, hg⟩` from `hL`. Take `⟨d, hd, h⟩` from `lsd_den (D := D) (g.biUnion fun t => Finset.univ.image fun i => t i)`. Use `⟨d, hd, fun t ht => ?_⟩` and prove the remaining obligations. Rewrite `ht` using `[← hg]`. Proceed by induction on `ht using Submodule.span_induction with`.

Consider the case `mem x hx`. Introduce `i`. Conclude with `h _ (Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩)`. Consider the case `zero => intro i; exact ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Introduce `i`. Take `⟨a, ha⟩` from `hx i`. Take `⟨b, hb⟩` from `hy i`. Conclude with `⟨a + b, by rw [Pi.add_apply, mul_add, ha, hb]; exact (map_add (algebraMap (𝓞 D.host.E) D.host.E) a b).symm⟩`. Consider the case `smul c x _ hx`.

Introduce `i`. Take `⟨a, ha⟩` from `hx i`. Use `⟨c * a, ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, Algebra.smul_def, show ((c * a : 𝓞 D.host.E) : D.host.E) = (c : D.host.E) * (a : D.host.E) from map_mul (algebraMap (𝓞 D.host.E) D.host.E) c a, ← ha]`. Use `show (d : D.host.E) * ((c : D.host.E) * x i) = (c : D.host.E) * ((d : D.host.E) * x i)`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem lsd_denFG {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (hL : L.FG) :
    ∃ d : 𝓞 D.host.E, d ≠ 0 ∧ ∀ t ∈ L, ∀ i, ∃ y : 𝓞 D.host.E, (d : D.host.E) * t i = y := by
  classical
  obtain ⟨g, hg⟩ := hL
  obtain ⟨d, hd, h⟩ := lsd_den (D := D) (g.biUnion fun t => Finset.univ.image fun i => t i)
  refine ⟨d, hd, fun t ht => ?_⟩
  rw [← hg] at ht
  induction ht using Submodule.span_induction with
  | mem x hx =>
    intro i
    exact h _ (Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩)
  | zero => intro i; exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    intro i
    obtain ⟨a, ha⟩ := hx i
    obtain ⟨b, hb⟩ := hy i
    exact ⟨a + b, by rw [Pi.add_apply, mul_add, ha, hb]; exact (map_add (algebraMap (𝓞 D.host.E) D.host.E) a b).symm⟩
  | smul c x _ hx =>
    intro i
    obtain ⟨a, ha⟩ := hx i
    refine ⟨c * a, ?_⟩
    rw [Pi.smul_apply, Algebra.smul_def,
      show ((c * a : 𝓞 D.host.E) : D.host.E) = (c : D.host.E) * (a : D.host.E) from
        map_mul (algebraMap (𝓞 D.host.E) D.host.E) c a, ← ha]
    show (d : D.host.E) * ((c : D.host.E) * x i) = (c : D.host.E) * ((d : D.host.E) * x i)
    ring

/- English proof (translation)
Take `⟨a, ha, h⟩` from `I.isFractional`. Use `⟨a, nonZeroDivisors.ne_zero ha, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `h x hx`. Conclude with `⟨y, by rw [show ((y : 𝓞 D.host.E) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E y from rfl, hy, Algebra.smul_def]⟩`.
-/
theorem lsd_denFrac (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
    ∃ d : 𝓞 D.host.E, d ≠ 0 ∧ ∀ x ∈ I, ∃ y : 𝓞 D.host.E, (d : D.host.E) * x = y := by
  obtain ⟨a, ha, h⟩ := I.isFractional
  refine ⟨a, nonZeroDivisors.ne_zero ha, fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := h x hx
  exact ⟨y, by rw [show ((y : 𝓞 D.host.E) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E y from rfl, hy,
    Algebra.smul_def]⟩

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.LatticeVariant.lsd_spanDen L hL x`.
-/
theorem lsd_spanDen {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (hL : Submodule.span D.host.E (L : Set (Fin n → D.host.E)) = ⊤) (x : Fin n → D.host.E) :
    ∃ d : 𝓞 D.host.E, d ≠ 0 ∧ (d : D.host.E) • x ∈ L :=
  _root_.UpperTheory.Reformulated.B.LatticeVariant.lsd_spanDen L hL x

section Lat

variable (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
  (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))

def lsdE (i : Fin T.rank) (j : Fin S.rank) (β : Af D.host.F) (e : D.host.E) : WO S T :=
  Matrix.of fun i' j' => if i' = i ∧ j' = j then pairA D.host.F 0 β ⊗ₜ[D.host.F] e else 0

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `h0 : D.host.AA = 0`. Use extensionality with `x`. Rewrite using `[FractionalIdeal.mem_zero_iff]`.

Conclude with `⟨fun hx => h x hx, fun hx => by`. Substitute `hx` using the available equality. Conclude with `Submodule.zero_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)⟩`. Use `Formalism.IndefR.Fin.factPrincipalDatum D.R D.host` as an intermediate fact. Rewrite `this` using `[h0, mul_zero, zero_mul, zero_mul]`.

Conclude with `zero_ne_one this`.
-/
theorem lsd_AA_ne : ∃ c : D.host.E, c ∈ D.host.AA ∧ c ≠ 0 := by
  by_contra h
  push_neg at h
  have h0 : D.host.AA = 0 := by
    ext x
    rw [FractionalIdeal.mem_zero_iff]
    exact ⟨fun hx => h x hx, fun hx => by
      subst hx; exact Submodule.zero_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)⟩
  have := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
  rw [h0, mul_zero, zero_mul, zero_mul] at this
  exact zero_ne_one this

/- English proof (translation)
Use `Fock.DRho.AF_ext D ?_ ?_` and prove the remaining obligations. Rewrite using `[map_smul]`. Use `show r • (0 : Ainf D.host.F) = 0`. Conclude with `smul_zero r`. Rewrite using `[map_smul]`.

Use `show r • α = _`. Rewrite using `[Algebra.smul_def]`. Both sides reduce to the same expression.
-/
theorem lsd_smul_pairA (r : D.host.F) (α : Af D.host.F) :
    r • pairA D.host.F 0 α = pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) r * α) := by
  refine Fock.DRho.AF_ext D ?_ ?_
  · rw [map_smul]; show r • (0 : Ainf D.host.F) = 0; exact smul_zero r
  · rw [map_smul]; show r • α = _; rw [Algebra.smul_def]; rfl

/- English proof (translation)
Rewrite using `[← lsd_smul_pairA, TensorProduct.smul_tmul, Algebra.smul_def]`.
-/
theorem lsd_tmul_eq (r : D.host.F) (α : Af D.host.F) (e : D.host.E) :
    pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) r * α) ⊗ₜ[D.host.F] e =
      pairA D.host.F 0 α ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E r * e) := by
  rw [← lsd_smul_pairA, TensorProduct.smul_tmul, Algebra.smul_def]

set_option maxHeartbeats 1600000 in
/- English proof (translation)
Take `⟨c, hc, hc0⟩` from `lsd_AA_ne (D := D)`. Establish `hT` using `hΛT.1.span_eq_top`. Establish `hS` using `hΛS.1.span_eq_top`. Use `choose dT hdT htT using fun i : Fin T.rank => lsd_spanDen ΛT hT (Pi.single i 1)`. Use `choose dS hdS hsS using fun j : Fin S.rank => lsd_spanDen ΛS hS (fun k => star (S.gram⁻¹ j k))`.

Establish `hdT' : ∀ i, (dT i : D.host.E) ≠ 0` using `fun i h => hdT i (FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E (by rw [map_zero]; exact h))`. Establish `hdS' : ∀ j, (dS j : D.host.E) ≠ 0` using `fun j h => hdS j (FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E (by rw [map_zero]; exact h))`. Set `Dij : Fin T.rank → Fin S.rank → D.host.E` to `fun i j => c * (dT i : D.host.E) * star (dS j : D.host.E)`. Establish `hD0 : ∀ i j, Dij i j ≠ 0` using `fun i j => mul_ne_zero (mul_ne_zero hc0 (hdT' i)) (by rw [Ne, star_eq_zero]; exact hdS' j)`. Take `⟨R, hR, hRy⟩` from `lsd_denF (D := D) (Finset.univ.image fun p : Fin T.rank × Fin S.rank × Fin (Module.finrank D.host.F D.host.E) => Module.finBasis D.host.F D.host.E p.2.2 * (Dij p.1 p.2.1)⁻¹)`.

Use `⟨R, hR, fun i j k α hα => ?_⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `hRy _ (Finset.mem_image.2 ⟨(i, j, k), Finset.mem_univ _, rfl⟩)`. Establish `hz : α ⊗ₜ[D.host.F] (y : D.host.E) ∈ intAE D` using `AddSubgroup.subset_closure ⟨α, hα, y, rfl⟩`. Establish `hmem` using `jF_gen_mem S T ΛS ΛT hz hc (hsS j) (htT i)`. Establish `hsum : ∀ j', ∑ k', star (((dS j : D.host.E) • fun k => star (S.gram⁻¹ j k)) k') * S.gram k' j' = if j' = j then star (dS j : D.host.E) else 0`.

Introduce `j'`. Establish `hinv : (S.gram⁻¹ * S.gram) j j' = if j = j' then 1 else 0`. Rewrite using `[Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (Formalism.L2.Theta.gram_det_ne S)), Matrix.one_apply]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, star_mul', star_star]`. Rewrite using `[show ∑ k', star (dS j : D.host.E) * S.gram⁻¹ j k' * S.gram k' j' = star (dS j : D.host.E) * (S.gram⁻¹ * S.gram) j j' by rw [Matrix.mul_apply, Finset.mul_sum]; simp only [mul_assoc], hinv]`.

Distinguish the cases in `h : j' = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg (Ne.symm h), if_neg h, mul_zero]`. Use `hmem using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `i' j'`. Simplify using `only [lsdE, Matrix.of_apply]`. Rewrite using `[hsum j']`. Establish `ht : ((dT i : D.host.E) • (Pi.single i 1 : Fin T.rank → D.host.E)) i' = if i' = i then (dT i : D.host.E) else 0`. Rewrite using `[Pi.smul_apply, smul_eq_mul]`.

Distinguish the cases in `h : i' = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`. Rewrite using `[ht]`.

Distinguish the cases in `hi : i' = i`. Distinguish the cases in `hj : j' = j`. Substitute `hi` using the available equality. Substitute `hj` using the available equality. Rewrite using `[if_pos ⟨rfl, rfl⟩, if_pos rfl, if_pos rfl, jF_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]`.

Rewrite using `[show (y : D.host.E) * (c * (dT i' : D.host.E) * star (dS j' : D.host.E)) = algebraMap D.host.F D.host.E (R : D.host.F) * Module.finBasis D.host.F D.host.E k by`. Establish `hD` using `hD0 i' j'`. Establish `hy' : algebraMap D.host.F D.host.E (R : D.host.F) * (Module.finBasis D.host.F D.host.E k * (c * (dT i' : D.host.E) * star (dS j' : D.host.E))⁻¹) = y` using `hy`. Establish `h1` using `hdT' i'`. Establish `h2 : star (dS j' : D.host.E) ≠ 0` using `by rw [Ne, star_eq_zero]; exact hdS' j'`.

Rewrite using `[← hy']`. Use the proof step `field_simp]`. Conclude with `lsd_tmul_eq _ _ _`. Rewrite using `[if_neg (fun h => hj h.2), if_neg hj, mul_zero, TensorProduct.tmul_zero, mul_zero]`. Rewrite using `[if_neg (fun h => hi h.1), if_neg hi, mul_zero, zero_mul, TensorProduct.tmul_zero, mul_zero]`.
-/
theorem lsd_mem (hΛS : IsSelfDualC S ΛS) (hΛT : IsSelfDualC T ΛT) :
    ∃ R : 𝓞 D.host.F, R ≠ 0 ∧ ∀ (i : Fin T.rank) (j : Fin S.rank) (k : Fin (Module.finrank D.host.F D.host.E))
      (α : Af D.host.F), α ∈ intAf D.host.F →
      lsdE S T i j (algebraMap D.host.F (Af D.host.F) (R : D.host.F) * α) (Module.finBasis D.host.F D.host.E k) ∈
        latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  classical
  obtain ⟨c, hc, hc0⟩ := lsd_AA_ne (D := D)
  have hT := hΛT.1.span_eq_top
  have hS := hΛS.1.span_eq_top
  choose dT hdT htT using fun i : Fin T.rank => lsd_spanDen ΛT hT (Pi.single i 1)
  choose dS hdS hsS using fun j : Fin S.rank => lsd_spanDen ΛS hS (fun k => star (S.gram⁻¹ j k))
  have hdT' : ∀ i, (dT i : D.host.E) ≠ 0 := fun i h => hdT i (FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E
    (by rw [map_zero]; exact h))
  have hdS' : ∀ j, (dS j : D.host.E) ≠ 0 := fun j h => hdS j (FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E
    (by rw [map_zero]; exact h))
  let Dij : Fin T.rank → Fin S.rank → D.host.E := fun i j => c * (dT i : D.host.E) * star (dS j : D.host.E)
  have hD0 : ∀ i j, Dij i j ≠ 0 := fun i j =>
    mul_ne_zero (mul_ne_zero hc0 (hdT' i)) (by rw [Ne, star_eq_zero]; exact hdS' j)
  obtain ⟨R, hR, hRy⟩ := lsd_denF (D := D) (Finset.univ.image fun p : Fin T.rank × Fin S.rank ×
    Fin (Module.finrank D.host.F D.host.E) => Module.finBasis D.host.F D.host.E p.2.2 * (Dij p.1 p.2.1)⁻¹)
  refine ⟨R, hR, fun i j k α hα => ?_⟩
  obtain ⟨y, hy⟩ := hRy _ (Finset.mem_image.2 ⟨(i, j, k), Finset.mem_univ _, rfl⟩)
  have hz : α ⊗ₜ[D.host.F] (y : D.host.E) ∈ intAE D := AddSubgroup.subset_closure ⟨α, hα, y, rfl⟩
  have hmem := jF_gen_mem S T ΛS ΛT hz hc (hsS j) (htT i)

  have hsum : ∀ j', ∑ k', star (((dS j : D.host.E) • fun k => star (S.gram⁻¹ j k)) k') * S.gram k' j' =
      if j' = j then star (dS j : D.host.E) else 0 := by
    intro j'
    have hinv : (S.gram⁻¹ * S.gram) j j' = if j = j' then 1 else 0 := by
      rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (Formalism.L2.Theta.gram_det_ne S)), Matrix.one_apply]
    simp only [Pi.smul_apply, smul_eq_mul, star_mul', star_star]
    rw [show ∑ k', star (dS j : D.host.E) * S.gram⁻¹ j k' * S.gram k' j' =
      star (dS j : D.host.E) * (S.gram⁻¹ * S.gram) j j' by rw [Matrix.mul_apply, Finset.mul_sum]; simp only [mul_assoc],
      hinv]
    by_cases h : j' = j
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h, mul_zero]
  convert hmem using 1
  ext i' j'
  simp only [lsdE, Matrix.of_apply]
  rw [hsum j']
  have ht : ((dT i : D.host.E) • (Pi.single i 1 : Fin T.rank → D.host.E)) i' = if i' = i then (dT i : D.host.E) else 0 := by
    rw [Pi.smul_apply, smul_eq_mul]
    by_cases h : i' = i
    · subst h; simp
    · simp [h]
  rw [ht]
  by_cases hi : i' = i
  · by_cases hj : j' = j
    · subst hi; subst hj
      rw [if_pos ⟨rfl, rfl⟩, if_pos rfl, if_pos rfl, jF_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      rw [show (y : D.host.E) * (c * (dT i' : D.host.E) * star (dS j' : D.host.E)) =
        algebraMap D.host.F D.host.E (R : D.host.F) * Module.finBasis D.host.F D.host.E k by
          have hD := hD0 i' j'
          have hy' : algebraMap D.host.F D.host.E (R : D.host.F) * (Module.finBasis D.host.F D.host.E k *
              (c * (dT i' : D.host.E) * star (dS j' : D.host.E))⁻¹) = y := hy
          have h1 := hdT' i'
          have h2 : star (dS j' : D.host.E) ≠ 0 := by rw [Ne, star_eq_zero]; exact hdS' j'
          rw [← hy']; field_simp]
      exact lsd_tmul_eq _ _ _
    · rw [if_neg (fun h => hj h.2), if_neg hj, mul_zero, TensorProduct.tmul_zero, mul_zero]
  · rw [if_neg (fun h => hi h.1), if_neg hi, mul_zero, zero_mul, TensorProduct.tmul_zero, mul_zero]

open Formalism.IndefR.PHeisFC in

/- English proof (translation)
Use `conv_lhs => rw [VacEx.expand_cE z]`. Rewrite using `[map_sum]`. Both sides reduce to the same expression.
-/
theorem lsd_finPart_expand (z : AE D) :
    finPart D z = ∑ k, sndA D.host.F (cE D.host.F D.host.E z k) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E k := by
  conv_lhs => rw [VacEx.expand_cE z]
  rw [map_sum]
  rfl

open Formalism.IndefR.PHeisFC in
/- English proof (translation)
Use `conv_lhs => rw [VacEx.expand_cE z]`. Rewrite using `[map_sum]`. Both sides reduce to the same expression.
-/
theorem lsd_infPart_expand (z : AE D) :
    infPart D z = ∑ k, fstA D.host.F (cE D.host.F D.host.E z k) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E k := by
  conv_lhs => rw [VacEx.expand_cE z]
  rw [map_sum]
  rfl

/- English proof (translation)
Unfold `lsdE`. Rewrite using `[Matrix.of_apply]`. Use `split_ifs`. Both sides reduce to the same expression. Conclude with `map_zero _`.
-/
theorem lsdE_finPart (i : Fin T.rank) (j : Fin S.rank) (β : Af D.host.F) (e : D.host.E) (i' : Fin T.rank)
    (j' : Fin S.rank) :
    finPart D (lsdE S T i j β e i' j') = if i' = i ∧ j' = j then β ⊗ₜ[D.host.F] e else 0 := by
  unfold lsdE
  rw [Matrix.of_apply]
  split_ifs
  · rfl
  · exact map_zero _

set_option maxHeartbeats 1600000 in
open Formalism.IndefR.PHeisFC in

/- English proof (translation)
Rewrite using `[← VacEx.open_neighbourhood_set_eq]`. Take `⟨R, hR, hmem⟩` from `lsd_mem S T ΛS ΛT hΛS hΛT`. Establish `hRF : (R : D.host.F) ≠ 0` using `fun h => hR (FaithfulSMul.algebraMap_injective (𝓞 D.host.F) D.host.F (by rw [map_zero]; exact h))`. Set `g : Fin T.rank → Fin S.rank → Fin (Module.finrank D.host.F D.host.E) → WO S T → Af D.host.F` to `fun i j k w => algebraMap D.host.F (Af D.host.F) (R : D.host.F)⁻¹ * sndA D.host.F (cE D.host.F D.host.E (w i j) k)`. Establish `hgc : ∀ i j k, Continuous (g i j k)` using `fun i j k => continuous_const.mul (continuous_snd.comp (Eqv.cont_PhiM T.rank S.rank i j k))`.

Set `B : Set (WO S T)` to `{w | ∀ i j k, g i j k w ∈ Ohat D.host.F}`. Establish `hBo : IsOpen B`. Establish `: B = ⋂ i, ⋂ j, ⋂ k, (g i j k) ⁻¹' (Ohat D.host.F)` using `by ext w; simp [B]`. Rewrite using `[this]`. Conclude with `isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun k => (isOpen_Ohat D.host.F).preimage (hgc i j k)`.

Establish `hB0 : (0 : WO S T) ∈ B`. Introduce `i j k`. Use `show algebraMap D.host.F (Af D.host.F) (R : D.host.F)⁻¹ * sndA D.host.F (cE D.host.F D.host.E ((0 : WO S T) i j) k) ∈ _`. Rewrite using `[Matrix.zero_apply, map_zero, Pi.zero_apply, map_zero, mul_zero]`. Conclude with `zero_mem (Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.intAd D.host.F)`.

Use `AddSubgroup.isOpen_of_mem_nhds _ (g := 0) (Filter.mem_of_superset (hBo.mem_nhds hB0) fun w hw => ?_)` and prove the remaining obligations. Use `⟨∑ i, ∑ j, ∑ k, lsdE S T i j (algebraMap D.host.F (Af D.host.F) (R : D.host.F) * g i j k w) (Module.finBasis D.host.F D.host.E k), ?_, fun i j => ?_⟩` and prove the remaining obligations. Conclude with `AddSubgroup.sum_mem _ fun i _ => AddSubgroup.sum_mem _ fun j _ => AddSubgroup.sum_mem _ fun k _ => hmem i j k _ (hw i j k)`. Rewrite using `[Matrix.sub_apply, map_sub, lsd_finPart_expand, Matrix.sum_apply, map_sum]`. Simplify using `only [Matrix.sum_apply, map_sum, lsdE_finPart]`.

Rewrite using `[Finset.sum_eq_single i (fun b _ hb => by simp [Ne.symm hb]) (by simp), Finset.sum_eq_single j (fun b _ hb => by simp [Ne.symm hb]) (by simp)]`. Simplify using `only [and_self, if_true]`. Rewrite using `[sub_eq_zero]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `hgk : algebraMap D.host.F (Af D.host.F) (R : D.host.F) * g i j k w = sndA D.host.F (cE D.host.F D.host.E (w i j) k)`.

Establish `h1 : algebraMap D.host.F (Af D.host.F) (R : D.host.F) * algebraMap D.host.F (Af D.host.F) (R : D.host.F)⁻¹ = 1`. Rewrite using `[← (algebraMap D.host.F (Af D.host.F)).map_mul, mul_inv_cancel₀ hRF, (algebraMap D.host.F (Af D.host.F)).map_one]`. Use `show algebraMap D.host.F (Af D.host.F) (R : D.host.F) * (algebraMap D.host.F (Af D.host.F) (R : D.host.F)⁻¹ * sndA D.host.F (cE D.host.F D.host.E (w i j) k)) = _`. Rewrite using `[← mul_assoc, h1, one_mul]`. Conclude with `congrArg (fun β => β ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E k)) hgk.symm`.
-/
theorem latO_isOpen (hΛS : IsSelfDualC S ΛS) (hΛT : IsSelfDualC T ΛT) :
    IsOpen {w : WO S T | ∃ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      (fun _ => True), (w - u).map (finPart D) = 0} := by
  classical
  rw [← VacEx.open_neighbourhood_set_eq]
  obtain ⟨R, hR, hmem⟩ := lsd_mem S T ΛS ΛT hΛS hΛT
  have hRF : (R : D.host.F) ≠ 0 := fun h => hR (FaithfulSMul.algebraMap_injective (𝓞 D.host.F) D.host.F
    (by rw [map_zero]; exact h))
  let g : Fin T.rank → Fin S.rank → Fin (Module.finrank D.host.F D.host.E) → WO S T → Af D.host.F := fun i j k w =>
    algebraMap D.host.F (Af D.host.F) (R : D.host.F)⁻¹ * sndA D.host.F (cE D.host.F D.host.E (w i j) k)
  have hgc : ∀ i j k, Continuous (g i j k) := fun i j k =>
    continuous_const.mul (continuous_snd.comp (Eqv.cont_PhiM T.rank S.rank i j k))
  let B : Set (WO S T) := {w | ∀ i j k, g i j k w ∈ Ohat D.host.F}
  have hBo : IsOpen B := by
    have : B = ⋂ i, ⋂ j, ⋂ k, (g i j k) ⁻¹' (Ohat D.host.F) := by ext w; simp [B]
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun k =>
      (isOpen_Ohat D.host.F).preimage (hgc i j k)
  have hB0 : (0 : WO S T) ∈ B := by
    intro i j k
    show algebraMap D.host.F (Af D.host.F) (R : D.host.F)⁻¹ * sndA D.host.F (cE D.host.F D.host.E ((0 : WO S T) i j) k) ∈ _
    rw [Matrix.zero_apply, map_zero, Pi.zero_apply, map_zero, mul_zero]
    exact zero_mem (Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.intAd D.host.F)
  refine AddSubgroup.isOpen_of_mem_nhds _ (g := 0) (Filter.mem_of_superset (hBo.mem_nhds hB0) fun w hw => ?_)
  refine ⟨∑ i, ∑ j, ∑ k, lsdE S T i j (algebraMap D.host.F (Af D.host.F) (R : D.host.F) * g i j k w)
    (Module.finBasis D.host.F D.host.E k), ?_, fun i j => ?_⟩
  · exact AddSubgroup.sum_mem _ fun i _ => AddSubgroup.sum_mem _ fun j _ => AddSubgroup.sum_mem _ fun k _ =>
      hmem i j k _ (hw i j k)
  · rw [Matrix.sub_apply, map_sub, lsd_finPart_expand, Matrix.sum_apply, map_sum]
    simp only [Matrix.sum_apply, map_sum, lsdE_finPart]
    rw [Finset.sum_eq_single i (fun b _ hb => by simp [Ne.symm hb]) (by simp),
      Finset.sum_eq_single j (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp only [and_self, if_true]
    rw [sub_eq_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hgk : algebraMap D.host.F (Af D.host.F) (R : D.host.F) * g i j k w =
        sndA D.host.F (cE D.host.F D.host.E (w i j) k) := by
      have h1 : algebraMap D.host.F (Af D.host.F) (R : D.host.F) *
          algebraMap D.host.F (Af D.host.F) (R : D.host.F)⁻¹ = 1 := by
        rw [← (algebraMap D.host.F (Af D.host.F)).map_mul, mul_inv_cancel₀ hRF, (algebraMap D.host.F (Af D.host.F)).map_one]
      show algebraMap D.host.F (Af D.host.F) (R : D.host.F) * (algebraMap D.host.F (Af D.host.F) (R : D.host.F)⁻¹ *
        sndA D.host.F (cE D.host.F D.host.E (w i j) k)) = _
      rw [← mul_assoc, h1, one_mul]
    exact congrArg (fun β => β ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E k)) hgk.symm

open Formalism.IndefR.PHeisFC in
/- English proof (translation)
Establish `h : a ⊗ₜ[D.host.F] e = a • ((1 : AF D.host.F) ⊗ₜ[D.host.F] e)`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Rewrite using `[h, map_smul, Pi.smul_apply, cE_tmul, smul_eq_mul]`.
-/
theorem lsd_cE_tmul (a : AF D.host.F) (e : D.host.E) (k : Fin (Module.finrank D.host.F D.host.E)) :
    cE D.host.F D.host.E (a ⊗ₜ[D.host.F] e) k =
      a * algebraMap D.host.F (AF D.host.F) ((Module.finBasis D.host.F D.host.E).repr e k) := by
  have h : a ⊗ₜ[D.host.F] e = a • ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h, map_smul, Pi.smul_apply, cE_tmul, smul_eq_mul]

set_option maxHeartbeats 800000 in
open Formalism.IndefR.PHeisFC in
/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e`. Rewrite using `[lsd_cE_tmul, map_mul, Fock.DRho.infPart_tmul, Algebra.TensorProduct.basis_repr_tmul]`. Simplify using `[Finsupp.smul_apply, Algebra.smul_def]`.

Consider the case `add x y hx hy`. Establish `h1 : cE D.host.F D.host.E (x + y) k = cE D.host.F D.host.E x k + cE D.host.F D.host.E y k`. Rewrite using `[map_add]`. Both sides reduce to the same expression. Rewrite using `[h1, map_add, hx, hy, ← Finsupp.add_apply, ← LinearEquiv.map_add, ← RingHom.map_add]`.
-/
theorem lsd_fst (z : AE D) (k : Fin (Module.finrank D.host.F D.host.E)) :
    fstA D.host.F (cE D.host.F D.host.E z k) =
      (Algebra.TensorProduct.basis (Ainf D.host.F) (Module.finBasis D.host.F D.host.E)).repr (infPart D z) k := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    rw [lsd_cE_tmul, map_mul, Fock.DRho.infPart_tmul, Algebra.TensorProduct.basis_repr_tmul]
    simp [Finsupp.smul_apply, Algebra.smul_def]
  | add x y hx hy =>
    have h1 : cE D.host.F D.host.E (x + y) k = cE D.host.F D.host.E x k + cE D.host.F D.host.E y k := by
      rw [map_add]; rfl
    rw [h1, map_add, hx, hy, ← Finsupp.add_apply, ← LinearEquiv.map_add, ← RingHom.map_add]

set_option maxHeartbeats 800000 in
open Formalism.IndefR.PHeisFC in
/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e`. Rewrite using `[lsd_cE_tmul, map_mul, Fock.DRho.finPart_tmul, Algebra.TensorProduct.basis_repr_tmul]`. Simplify using `[Finsupp.smul_apply, Algebra.smul_def]`.

Consider the case `add x y hx hy`. Establish `h1 : cE D.host.F D.host.E (x + y) k = cE D.host.F D.host.E x k + cE D.host.F D.host.E y k`. Rewrite using `[map_add]`. Both sides reduce to the same expression. Rewrite using `[h1, map_add, hx, hy, ← Finsupp.add_apply, ← LinearEquiv.map_add, ← RingHom.map_add]`.
-/
theorem lsd_snd (z : AE D) (k : Fin (Module.finrank D.host.F D.host.E)) :
    sndA D.host.F (cE D.host.F D.host.E z k) =
      (Algebra.TensorProduct.basis (Af D.host.F) (Module.finBasis D.host.F D.host.E)).repr (finPart D z) k := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    rw [lsd_cE_tmul, map_mul, Fock.DRho.finPart_tmul, Algebra.TensorProduct.basis_repr_tmul]
    simp [Finsupp.smul_apply, Algebra.smul_def]
  | add x y hx hy =>
    have h1 : cE D.host.F D.host.E (x + y) k = cE D.host.F D.host.E x k + cE D.host.F D.host.E y k := by
      rw [map_add]; rfl
    rw [h1, map_add, hx, hy, ← Finsupp.add_apply, ← LinearEquiv.map_add, ← RingHom.map_add]

/- English proof (translation)
Introduce `v`. Rewrite using `[AlgHom.commutes, HeightOneSpectrum.mem_adicCompletionIntegers]`. Conclude with `Formalism.IndefR.Fin.val_coe_le_one v y`.
-/
theorem lsd_alg_int (y : 𝓞 D.host.F) : algebraMap D.host.F (Af D.host.F) (y : D.host.F) ∈ intAf D.host.F := by
  intro v
  rw [AlgHom.commutes, HeightOneSpectrum.mem_adicCompletionIntegers]
  exact Formalism.IndefR.Fin.val_coe_le_one v y

open Formalism.IndefR.PHeisFC in
/- English proof (translation)
Take `⟨r, hr, hcoord⟩` from `lsd_coordO (D := D)`. Use `⟨r, hr, fun w hw k => ?_⟩` and prove the remaining obligations. Proceed by induction on `hw using AddSubgroup.closure_induction with`. Consider the case `mem w hw`. Take `⟨a, ha, x, rfl⟩` from `hw`.

Rewrite using `[Algebra.TensorProduct.basis_repr_tmul]`. Simplify using `only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]`. Take `⟨y, hy⟩` from `hcoord x k`. Rewrite using `[mul_left_comm, ← map_mul, hy]`. Conclude with `intAf_mul ha (lsd_alg_int y)`.

Consider the case `zero => simp only [map_zero, Finsupp.zero_apply, mul_zero]`. Conclude with `fun v => zero_mem _`. Consider the case `add x y _ _ hx hy`. Rewrite using `[map_add, Finsupp.add_apply, mul_add]`. Conclude with `fun v => by rw [map_add]; exact add_mem (hx v) (hy v)`.

Consider the case `neg x _ hx`. Rewrite using `[map_neg, Finsupp.neg_apply, mul_neg]`. Conclude with `fun v => by rw [map_neg]; exact neg_mem (hx v)`.
-/
theorem lsd_int_coord : ∃ r : 𝓞 D.host.F, r ≠ 0 ∧ ∀ w ∈ intAE D, ∀ k,
    algebraMap D.host.F (Af D.host.F) (r : D.host.F) *
      (Algebra.TensorProduct.basis (Af D.host.F) (Module.finBasis D.host.F D.host.E)).repr w k ∈ intAf D.host.F := by
  obtain ⟨r, hr, hcoord⟩ := lsd_coordO (D := D)
  refine ⟨r, hr, fun w hw k => ?_⟩
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, x, rfl⟩ := hw
    rw [Algebra.TensorProduct.basis_repr_tmul]
    simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
    obtain ⟨y, hy⟩ := hcoord x k
    rw [mul_left_comm, ← map_mul, hy]
    exact intAf_mul ha (lsd_alg_int y)
  | zero => simp only [map_zero, Finsupp.zero_apply, mul_zero]; exact fun v => zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add, Finsupp.add_apply, mul_add]
    exact fun v => by rw [map_add]; exact add_mem (hx v) (hy v)
  | neg x _ hx =>
    rw [map_neg, Finsupp.neg_apply, mul_neg]
    exact fun v => by rw [map_neg]; exact neg_mem (hx v)

open Formalism.IndefR.PHeisFC in
/- English proof (translation)
Use `Fock.DRho.AF_ext D ?_ rfl` and prove the remaining obligations. Rewrite using `[lsd_fst, hz, map_zero, Finsupp.zero_apply]`. Both sides reduce to the same expression.
-/
theorem lsd_cE_of_inf (z : AE D) (hz : infPart D z = 0) (k : Fin (Module.finrank D.host.F D.host.E)) :
    cE D.host.F D.host.E z k = pairA D.host.F 0 (sndA D.host.F (cE D.host.F D.host.E z k)) := by
  refine Fock.DRho.AF_ext D ?_ rfl
  rw [lsd_fst, hz, map_zero, Finsupp.zero_apply]
  rfl

set_option maxHeartbeats 1600000 in
open Formalism.IndefR.PHeisFC in

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.sum_apply, lsdE, Matrix.of_apply]`. Rewrite using `[Finset.sum_eq_single i (fun b _ hb => by simp [Ne.symm hb]) (by simp), Finset.sum_eq_single j (fun b _ hb => by simp [Ne.symm hb]) (by simp)]`. Simplify using `only [and_self, if_true]`. Use `conv_lhs => rw [VacEx.expand_cE (Y i j)]`.

Conclude with `Finset.sum_congr rfl fun k _ => by rw [← lsd_cE_of_inf _ (hY i j) k]`.
-/
theorem lsd_decomp (Y : WO S T) (hY : ∀ i j, infPart D (Y i j) = 0) :
    Y = ∑ i, ∑ j, ∑ k, lsdE S T i j (sndA D.host.F (cE D.host.F D.host.E (Y i j) k))
      (Module.finBasis D.host.F D.host.E k) := by
  classical
  ext i j
  simp only [Matrix.sum_apply, lsdE, Matrix.of_apply]
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [Ne.symm hb]) (by simp),
    Finset.sum_eq_single j (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp only [and_self, if_true]
  conv_lhs => rw [VacEx.expand_cE (Y i j)]
  exact Finset.sum_congr rfl fun k _ => by rw [← lsd_cE_of_inf _ (hY i j) k]

/- English proof (translation)
Establish `key : ∀ x : AF D.host.F, N • (x ⊗ₜ[D.host.F] e) = (N • x) ⊗ₜ[D.host.F] e`. Introduce `x`. Proceed by induction on `N with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [succ_nsmul, ih, succ_nsmul, TensorProduct.add_tmul]`.

Use extensionality with `i' j'`. Simplify using `only [lsdE, Matrix.smul_apply, Matrix.of_apply]`. Use `split_ifs`. Rewrite using `[key, VacEx.nsmul_pairA, nsmul_eq_mul, ← map_natCast (algebraMap D.host.F (Af D.host.F))]`. Rewrite using `[smul_zero]`.
-/
theorem lsdE_nsmul (N : ℕ) (i : Fin T.rank) (j : Fin S.rank) (β : Af D.host.F) (e : D.host.E) :
    N • lsdE S T i j β e = lsdE S T i j (algebraMap D.host.F (Af D.host.F) (N : D.host.F) * β) e := by
  have key : ∀ x : AF D.host.F, N • (x ⊗ₜ[D.host.F] e) = (N • x) ⊗ₜ[D.host.F] e := by
    intro x
    induction N with
    | zero => simp
    | succ n ih => rw [succ_nsmul, ih, succ_nsmul, TensorProduct.add_tmul]
  ext i' j'
  simp only [lsdE, Matrix.smul_apply, Matrix.of_apply]
  split_ifs
  · rw [key, VacEx.nsmul_pairA, nsmul_eq_mul, ← map_natCast (algebraMap D.host.F (Af D.host.F))]
  · rw [smul_zero]

set_option maxHeartbeats 1600000 in
open Formalism.IndefR.PHeisFC in

/- English proof (translation)
Take `⟨R, hR, hmem⟩` from `lsd_mem S T ΛS ΛT hΛS hΛT`. Take `⟨r, hr, hint⟩` from `lsd_int_coord (D := D)`. Use `set x : 𝓞 D.host.F := R * r`. Establish `hx : x ≠ 0` using `mul_ne_zero hR hr`. Use `set N : ℕ := Ideal.absNorm (Ideal.span {x})`.

Establish `hN : 0 < N` using `Nat.pos_of_ne_zero fun h => hx (by`. Rewrite `h` using `[Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]`. Conclude with `h)`. Take `⟨q, hq⟩` from `Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {x}))`. Use `⟨N, hN, fun Y hfin hinf => ?_⟩` and prove the remaining obligations.

Rewrite using `[lsd_decomp S T Y hinf, Finset.smul_sum]`. Use `AddSubgroup.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.smul_sum]`. Use `AddSubgroup.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.smul_sum]`.

Use `AddSubgroup.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Rewrite using `[lsdE_nsmul]`. Establish `hNF : (N : D.host.F) = (R : D.host.F) * ((q : D.host.F) * (r : D.host.F))`. Use `congrArg (fun z : 𝓞 D.host.F => (z : D.host.F)) hq` as an intermediate fact. Simplify using `only [x] at this`.

Rewrite `this` using `[show ((N : 𝓞 D.host.F) : D.host.F) = (N : D.host.F) from by norm_cast]`. Rewrite using `[← this]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hNF, map_mul, map_mul, mul_assoc, mul_assoc]`.

Use `hmem i j k _ (intAf_mul (lsd_alg_int q) ?_)` and prove the remaining obligations. Rewrite using `[lsd_snd]`. Conclude with `hint _ (hfin i j) k`.
-/
theorem latO_nsmul_mem (hΛS : IsSelfDualC S ΛS) (hΛT : IsSelfDualC T ΛT) :
    ∃ N : ℕ, 0 < N ∧ ∀ Y : WO S T, (∀ i j, finPart D (Y i j) ∈ intAE D) → (∀ i j, infPart D (Y i j) = 0) →
      N • Y ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  obtain ⟨R, hR, hmem⟩ := lsd_mem S T ΛS ΛT hΛS hΛT
  obtain ⟨r, hr, hint⟩ := lsd_int_coord (D := D)
  set x : 𝓞 D.host.F := R * r
  have hx : x ≠ 0 := mul_ne_zero hR hr
  set N : ℕ := Ideal.absNorm (Ideal.span {x})
  have hN : 0 < N := Nat.pos_of_ne_zero fun h => hx (by
    rw [Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot] at h; exact h)
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {x}))
  refine ⟨N, hN, fun Y hfin hinf => ?_⟩
  rw [lsd_decomp S T Y hinf, Finset.smul_sum]
  refine AddSubgroup.sum_mem _ fun i _ => ?_
  rw [Finset.smul_sum]
  refine AddSubgroup.sum_mem _ fun j _ => ?_
  rw [Finset.smul_sum]
  refine AddSubgroup.sum_mem _ fun k _ => ?_
  rw [lsdE_nsmul]
  have hNF : (N : D.host.F) = (R : D.host.F) * ((q : D.host.F) * (r : D.host.F)) := by
    have := congrArg (fun z : 𝓞 D.host.F => (z : D.host.F)) hq
    simp only [x] at this
    rw [show ((N : 𝓞 D.host.F) : D.host.F) = (N : D.host.F) from by norm_cast] at this
    rw [← this]
    push_cast
    ring
  rw [hNF, map_mul, map_mul, mul_assoc, mul_assoc]
  refine hmem i j k _ (intAf_mul (lsd_alg_int q) ?_)
  rw [lsd_snd]
  exact hint _ (hfin i j) k

/- English proof (translation)
Introduce `x hx`. Proceed by induction on `hx using AddSubgroup.closure_induction with`. Consider the case `mem w hw`. Take `⟨α, -, -, a, -, s, -, t, -, rfl⟩` from `hw`. Introduce `i j`.

Rewrite using `[Matrix.of_apply, Fock.DRho.infPart_tmul, VacEx.fstA_pairA, TensorProduct.zero_tmul]`. Consider the case `zero => intro i j`. Simplify using the standard rewrite rules. Consider the case `add x y _ _ hx hy => intro i j`. Rewrite using `[Matrix.add_apply, map_add, hx, hy, add_zero]`.

Consider the case `neg x _ hx => intro i j`. Rewrite using `[Matrix.neg_apply, map_neg, hx, neg_zero]`.
-/
theorem lsd_fi : ∀ x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
    ∀ i j, infPart D (x i j) = 0 := by
  intro x hx
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, -, -, a, -, s, -, t, -, rfl⟩ := hw
    intro i j
    rw [Matrix.of_apply, Fock.DRho.infPart_tmul, VacEx.fstA_pairA, TensorProduct.zero_tmul]
  | zero => intro i j; simp
  | add x y _ _ hx hy => intro i j; rw [Matrix.add_apply, map_add, hx, hy, add_zero]
  | neg x _ hx => intro i j; rw [Matrix.neg_apply, map_neg, hx, neg_zero]

set_option maxHeartbeats 1600000 in
open Formalism.IndefR.PHeisFC in

/- English proof (translation)
Use `set Λ := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True with hΛ`. Establish `hU` using `latO_isOpen S T ΛS ΛT hΛS hΛT`. Rewrite `hU` using `[← VacEx.open_neighbourhood_set_eq]`. Establish `hUc : IsClosed (VacEx.U0 S T Λ : Set (WO S T))` using `AddSubgroup.isClosed_of_isOpen _ hU`. Use `set Z : Set (WO S T) := {w | ∀ i j k, fstA D.host.F (cE D.host.F D.host.E (w i j) k) = 0} with hZdef`.

Establish `hZ : IsClosed Z`. Establish `: Z = ⋂ i, ⋂ j, ⋂ k, (fun w : WO S T => fstA D.host.F (cE D.host.F D.host.E (w i j) k)) ⁻¹' {0}`. Use extensionality with `w`. Simplify using `[Z]`. Rewrite using `[this]`.

Conclude with `isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun k => isClosed_singleton.preimage (continuous_fst.comp (Eqv.cont_PhiM T.rank S.rank i j k))`. Establish `hfst : ∀ u ∈ Λ, ∀ i j k, fstA D.host.F (cE D.host.F D.host.E (u i j) k) = 0`. Introduce `u hu i j k`. Rewrite using `[lsd_fst, lsd_fi S T ΛS ΛT u hu i j, map_zero, Finsupp.zero_apply]`. Establish `hΛeq : (Λ : Set (WO S T)) = (VacEx.U0 S T Λ : Set (WO S T)) ∩ Z`.

Use extensionality with `w`. Prove the components needed by the constructor for the conclusion. Introduce `hw`. Conclude with `⟨VacEx.le_open_neighbourhood S T hw, hfst w hw⟩`. Introduce and unpack `⟨⟨u, hu, hwu⟩, hz⟩`.

Establish `hwu' : w = u`. Use extensionality with `i j`. Establish `hi : infPart D (w i j - u i j) = 0`. Rewrite using `[lsd_infPart_expand]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[map_sub, Pi.sub_apply, map_sub, hz i j k, hfst u hu i j k, sub_self, TensorProduct.zero_tmul]`. Conclude with `sub_eq_zero.1 (Fock.DRho.eq_zero_of_parts D _ hi (by simpa using hwu i j))`. Rewrite using `[hwu']`. Conclude with `hu`. Take `⟨c, hc, hup⟩` from `PDB.upper (S := S) (T := T) (ΛS := ΛS) (ΛT := ΛT) hΛS hΛT`.

Take `⟨r, hr, hint⟩` from `lsd_int_coord (D := D)`. Establish `hrF : (r : D.host.F) ≠ 0` using `fun h => hr (FaithfulSMul.algebraMap_injective (𝓞 D.host.F) D.host.F (by rw [map_zero]; exact h))`. Establish `hρ : ((c : D.host.F) * (r : D.host.F)) ≠ 0` using `mul_ne_zero (Nat.cast_ne_zero.2 hc.ne') hrF`. Use `IsCompact.of_isClosed_subset ((VacEx.isCompact_boxB (D := D) T.rank S.rank).image (continuous_const_smul ((c : D.host.F) * (r : D.host.F))⁻¹)) (hΛeq ▸ hUc.inter hZ) ?_` and prove the remaining obligations. Introduce `u hu`.

Establish `hcu : c • u ∈ Λ` using `AddSubgroup.nsmul_mem _ hu c`. Establish `hsmul : ((c : D.host.F) * (r : D.host.F)) • u = (r : D.host.F) • (c • u)`. Rewrite using `[mul_comm, mul_smul, Nat.cast_smul_eq_nsmul]`. Use `⟨((c : D.host.F) * (r : D.host.F)) • u, ?_, by show ((c : D.host.F) * (r : D.host.F))⁻¹ • (((c : D.host.F) * (r : D.host.F)) • u) = u` and prove the remaining obligations. Rewrite using `[smul_smul, inv_mul_cancel₀ hρ, one_smul]⟩`.

Use `⟨Eqv.PhiM T.rank S.rank (((c : D.host.F) * (r : D.host.F)) • u), fun i _ j _ k _ => ?_, ?_⟩` and prove the remaining obligations. Establish `hcoord : Eqv.PhiM T.rank S.rank (((c : D.host.F) * (r : D.host.F)) • u) i j k = (r : D.host.F) • cE D.host.F D.host.E ((c • u) i j) k`. Rewrite using `[hsmul]`. Use `show cE D.host.F D.host.E ((r : D.host.F) • (c • u) i j) k = _`. Rewrite using `[← algebraMap_smul (AF D.host.F) (r : D.host.F), map_smul, Pi.smul_apply, algebraMap_smul]`.

Use `⟨algebraMap D.host.F (Af D.host.F) (r : D.host.F) * sndA D.host.F (cE D.host.F D.host.E ((c • u) i j) k), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[lsd_snd]`. Conclude with `fun v => hint _ (hup u hu i j).2 k v`. Rewrite using `[hcoord, lsd_cE_of_inf _ (lsd_fi S T ΛS ΛT _ hcu i j) k]`. Use `Fock.DRho.AF_ext D ?_ ?_` and prove the remaining obligations.

Rewrite using `[VacEx.fstA_pairA, map_smul, VacEx.fstA_pairA, smul_zero]`. Rewrite using `[VacEx.sndA_pairA, map_smul, VacEx.sndA_pairA, Algebra.smul_def]`. Use extensionality with `i j show (cE D.host.F D.host.E).symm (cE D.host.F D.host.E ((((c : D.host.F) * (r : D.host.F)) • u) i j)) = _`. Rewrite using `[ContinuousLinearEquiv.symm_apply_apply]`.
-/
theorem latO_isCompact (hΛS : IsSelfDualC S ΛS) (hΛT : IsSelfDualC T ΛT) :
    IsCompact ((latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True :
      AddSubgroup (WO S T)) : Set (WO S T)) := by
  classical
  set Λ := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True with hΛ
  have hU := latO_isOpen S T ΛS ΛT hΛS hΛT
  rw [← VacEx.open_neighbourhood_set_eq] at hU
  have hUc : IsClosed (VacEx.U0 S T Λ : Set (WO S T)) := AddSubgroup.isClosed_of_isOpen _ hU
  set Z : Set (WO S T) := {w | ∀ i j k, fstA D.host.F (cE D.host.F D.host.E (w i j) k) = 0} with hZdef
  have hZ : IsClosed Z := by
    have : Z = ⋂ i, ⋂ j, ⋂ k, (fun w : WO S T => fstA D.host.F (cE D.host.F D.host.E (w i j) k)) ⁻¹' {0} := by
      ext w; simp [Z]
    rw [this]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun k =>
      isClosed_singleton.preimage (continuous_fst.comp (Eqv.cont_PhiM T.rank S.rank i j k))
  have hfst : ∀ u ∈ Λ, ∀ i j k, fstA D.host.F (cE D.host.F D.host.E (u i j) k) = 0 := by
    intro u hu i j k
    rw [lsd_fst, lsd_fi S T ΛS ΛT u hu i j, map_zero, Finsupp.zero_apply]
  have hΛeq : (Λ : Set (WO S T)) = (VacEx.U0 S T Λ : Set (WO S T)) ∩ Z := by
    ext w
    constructor
    · intro hw; exact ⟨VacEx.le_open_neighbourhood S T hw, hfst w hw⟩
    · rintro ⟨⟨u, hu, hwu⟩, hz⟩
      have hwu' : w = u := by
        ext i j
        have hi : infPart D (w i j - u i j) = 0 := by
          rw [lsd_infPart_expand]
          refine Finset.sum_eq_zero fun k _ => ?_
          rw [map_sub, Pi.sub_apply, map_sub, hz i j k, hfst u hu i j k, sub_self, TensorProduct.zero_tmul]
        exact sub_eq_zero.1 (Fock.DRho.eq_zero_of_parts D _ hi (by simpa using hwu i j))
      rw [hwu']; exact hu
  obtain ⟨c, hc, hup⟩ := PDB.upper (S := S) (T := T) (ΛS := ΛS) (ΛT := ΛT) hΛS hΛT
  obtain ⟨r, hr, hint⟩ := lsd_int_coord (D := D)
  have hrF : (r : D.host.F) ≠ 0 := fun h => hr (FaithfulSMul.algebraMap_injective (𝓞 D.host.F) D.host.F
    (by rw [map_zero]; exact h))
  have hρ : ((c : D.host.F) * (r : D.host.F)) ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.2 hc.ne') hrF
  refine IsCompact.of_isClosed_subset ((VacEx.isCompact_boxB (D := D) T.rank S.rank).image
    (continuous_const_smul ((c : D.host.F) * (r : D.host.F))⁻¹)) (hΛeq ▸ hUc.inter hZ) ?_
  intro u hu
  have hcu : c • u ∈ Λ := AddSubgroup.nsmul_mem _ hu c
  have hsmul : ((c : D.host.F) * (r : D.host.F)) • u = (r : D.host.F) • (c • u) := by
    rw [mul_comm, mul_smul, Nat.cast_smul_eq_nsmul]
  refine ⟨((c : D.host.F) * (r : D.host.F)) • u, ?_, by
    show ((c : D.host.F) * (r : D.host.F))⁻¹ • (((c : D.host.F) * (r : D.host.F)) • u) = u
    rw [smul_smul, inv_mul_cancel₀ hρ, one_smul]⟩
  refine ⟨Eqv.PhiM T.rank S.rank (((c : D.host.F) * (r : D.host.F)) • u), fun i _ j _ k _ => ?_, ?_⟩
  · have hcoord : Eqv.PhiM T.rank S.rank (((c : D.host.F) * (r : D.host.F)) • u) i j k =
        (r : D.host.F) • cE D.host.F D.host.E ((c • u) i j) k := by
      rw [hsmul]
      show cE D.host.F D.host.E ((r : D.host.F) • (c • u) i j) k = _
      rw [← algebraMap_smul (AF D.host.F) (r : D.host.F), map_smul, Pi.smul_apply, algebraMap_smul]
    refine ⟨algebraMap D.host.F (Af D.host.F) (r : D.host.F) * sndA D.host.F (cE D.host.F D.host.E ((c • u) i j) k),
      ?_, ?_⟩
    · rw [lsd_snd]
      exact fun v => hint _ (hup u hu i j).2 k v
    · rw [hcoord, lsd_cE_of_inf _ (lsd_fi S T ΛS ΛT _ hcu i j) k]
      refine Fock.DRho.AF_ext D ?_ ?_
      · rw [VacEx.fstA_pairA, map_smul, VacEx.fstA_pairA, smul_zero]
      · rw [VacEx.sndA_pairA, map_smul, VacEx.sndA_pairA, Algebra.smul_def]
  · ext i j
    show (cE D.host.F D.host.E).symm (cE D.host.F D.host.E ((((c : D.host.F) * (r : D.host.F)) • u) i j)) = _
    rw [ContinuousLinearEquiv.symm_apply_apply]

end Lat

end Formalism.IndefR.Fin
