import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitOff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.MovedSplitEq
open Matrix

section Algebra

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

/- English proof (translation)
Use `set N : Matrix n n R := (B⁻¹).1 * (g - 1) * B.1 with hN`. Establish `hεN : ε • N = N` using `by rw [hN, ← Matrix.smul_mul, ← Matrix.mul_smul, hg]`. Use `choose c hc using fun x : n × n => hS (N x.1 x.2)`. Use `⟨Finset.univ.sup c, fun z hz i => ?_⟩` and prove the remaining obligations. Establish `hNij : ∀ i j, (p : R) ^ (Finset.univ.sup c) * N i j ∈ S` using `fun i j => by`.

Take `⟨d, hd⟩` from `Nat.exists_eq_add_of_le' (Finset.le_sup (f := c) (Finset.mem_univ (i, j)))`. Establish `h1` using `hc (i, j)`. Establish `h2 : ε * N i j = N i j` using `congrFun (congrFun hεN i) j`. Simplify using `only [h2] at h1`. Rewrite using `[hd, pow_add, mul_assoc]`.

Conclude with `mul_mem (pow_mem (natCast_mem S p) _) h1`. Establish `e : (B⁻¹).1 *ᵥ (g *ᵥ z) = (B⁻¹).1 *ᵥ z + N *ᵥ ((B⁻¹).1 *ᵥ z)`. Rewrite using `[hN, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc _ B.1, Units.mul_inv, Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mulVec]`. Normalize the expressions using the abelian group laws. Rewrite using `[e, Pi.add_apply, mul_add]`.

Use `add_mem (mul_mem (pow_mem (natCast_mem S p) _) (hz i)) ?_` and prove the remaining obligations. Use `show (p : R) ^ (Finset.univ.sup c) * ∑ j, N i j * ((B⁻¹).1 *ᵥ z) j ∈ S`. Rewrite using `[Finset.mul_sum]`. Conclude with `sum_mem fun j _ => by rw [← mul_assoc]; exact mul_mem (hNij i j) (hz j)`.
-/
theorem conj_int (S : Subring R) (ε : R) (p : ℕ) (hS : ∀ z, ∃ c : ℕ, (p : R) ^ c * (ε * z) ∈ S) (B : GL n R) (g : Matrix n n R)
    (hg : ε • (g - 1) = g - 1) : ∃ c : ℕ, ∀ z : n → R, (∀ i, ((B⁻¹).1 *ᵥ z) i ∈ S) →
      ∀ i, (p : R) ^ c * ((B⁻¹).1 *ᵥ (g *ᵥ z)) i ∈ S := by
  set N : Matrix n n R := (B⁻¹).1 * (g - 1) * B.1 with hN
  have hεN : ε • N = N := by rw [hN, ← Matrix.smul_mul, ← Matrix.mul_smul, hg]
  choose c hc using fun x : n × n => hS (N x.1 x.2)
  refine ⟨Finset.univ.sup c, fun z hz i => ?_⟩
  have hNij : ∀ i j, (p : R) ^ (Finset.univ.sup c) * N i j ∈ S := fun i j => by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := c) (Finset.mem_univ (i, j)))
    have h1 := hc (i, j)
    have h2 : ε * N i j = N i j := congrFun (congrFun hεN i) j
    simp only [h2] at h1
    rw [hd, pow_add, mul_assoc]
    exact mul_mem (pow_mem (natCast_mem S p) _) h1
  have e : (B⁻¹).1 *ᵥ (g *ᵥ z) = (B⁻¹).1 *ᵥ z + N *ᵥ ((B⁻¹).1 *ᵥ z) := by
    rw [hN, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc _ B.1, Units.mul_inv, Matrix.mul_one,
      Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mulVec]
    abel
  rw [e, Pi.add_apply, mul_add]
  refine add_mem (mul_mem (pow_mem (natCast_mem S p) _) (hz i)) ?_
  show (p : R) ^ (Finset.univ.sup c) * ∑ j, N i j * ((B⁻¹).1 *ᵥ z) j ∈ S
  rw [Finset.mul_sum]
  exact sum_mem fun j _ => by rw [← mul_assoc]; exact mul_mem (hNij i j) (hz j)

/- English proof (translation)
Establish `e : (g⁻¹).1 - 1 = -((g⁻¹).1 * (g.1 - 1))`. Rewrite using `[Matrix.mul_sub, Units.inv_mul, Matrix.mul_one, neg_sub]`. Rewrite using `[e, smul_neg, ← Matrix.mul_smul, hg]`.
-/
theorem supp_inv (ε : R) (g : GL n R) (hg : ε • (g.1 - 1) = g.1 - 1) : ε • ((g⁻¹).1 - 1) = (g⁻¹).1 - 1 := by
  have e : (g⁻¹).1 - 1 = -((g⁻¹).1 * (g.1 - 1)) := by
    rw [Matrix.mul_sub, Units.inv_mul, Matrix.mul_one, neg_sub]
  rw [e, smul_neg, ← Matrix.mul_smul, hg]

end Algebra

section Adeles

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c : ℕ, Valued.v (evalV F v β) ≤ WithZero.exp (c : ℤ) := by`. Distinguish the cases in `hx : Valued.v (evalV F v β) = 0`. Conclude with `⟨0, hx ▸ zero_le'⟩`. Conclude with `⟨(WithZero.log (Valued.v (evalV F v β))).toNat, by`. Rewrite using `[← WithZero.exp_log hx]; exact WithZero.exp_le_exp.2 (by rw [WithZero.log_exp]; exact Int.self_le_toNat _)⟩`.

Use `⟨c, fun w => ?_⟩` and prove the remaining obligations. Use `show evalV F w ((p : FiniteAdeleRing (𝓞 F) F) ^ c * β) ∈ _`. Rewrite using `[map_mul]`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality.

Establish `he : evalV F w ((p : FiniteAdeleRing (𝓞 F) F) ^ c) = ((algebraMap (𝓞 F) F ((p : 𝓞 F) ^ c) : F) : w.adicCompletion F)`. Express the relevant statement in the definitionally equal form `_ = algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F ((p : 𝓞 F) ^ c))`. Simplify using `only [map_natCast, map_pow]`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, he, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hβ w hw, mul_zero]`. Conclude with `zero_mem _`.
-/
theorem pow_mul_mem_intAd (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) (hp : (p : 𝓞 F) ∈ v.asIdeal) (β : FiniteAdeleRing (𝓞 F) F)
    (hβ : ∀ w, w ≠ v → evalV F w β = 0) : ∃ c : ℕ, (p : FiniteAdeleRing (𝓞 F) F) ^ c * β ∈ Formalism.UG.intAd F := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ, Valued.v (evalV F v β) ≤ WithZero.exp (c : ℤ) := by
    by_cases hx : Valued.v (evalV F v β) = 0
    · exact ⟨0, hx ▸ zero_le'⟩
    · exact ⟨(WithZero.log (Valued.v (evalV F v β))).toNat, by
        rw [← WithZero.exp_log hx]; exact WithZero.exp_le_exp.2 (by rw [WithZero.log_exp]; exact Int.self_le_toNat _)⟩
  refine ⟨c, fun w => ?_⟩
  show evalV F w ((p : FiniteAdeleRing (𝓞 F) F) ^ c * β) ∈ _
  rw [map_mul]
  by_cases hw : w = v
  · subst hw
    have he : evalV F w ((p : FiniteAdeleRing (𝓞 F) F) ^ c) =
        ((algebraMap (𝓞 F) F ((p : 𝓞 F) ^ c) : F) : w.adicCompletion F) := by
      change _ = algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F ((p : 𝓞 F) ^ c))
      simp only [map_natCast, map_pow]
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, he, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      HeightOneSpectrum.valuation_of_algebraMap]
    calc _ ≤ WithZero.exp (-(c : ℤ)) * WithZero.exp (c : ℤ) :=
          mul_le_mul' ((HeightOneSpectrum.intValuation_le_pow_iff_mem _ _ _).2 (Ideal.pow_mem_pow hp c)) hc
      _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
  · rw [hβ w hw, mul_zero]; exact zero_mem _

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, by simpa using zero_mem _⟩`. Consider the case `add x y hx hy`. Take `⟨a, ha⟩` from `hx`. Take `⟨b, hb⟩` from `hy`.

Use `⟨a + b, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_add, mul_add]`. Use `add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[add_comm a b, pow_add, mul_assoc]`. Conclude with `mul_mem (pow_mem (natCast_mem _ p) _) ha`.

Rewrite using `[pow_add, mul_assoc]`. Conclude with `mul_mem (pow_mem (natCast_mem _ p) _) hb`. Consider the case `tmul x β`. Take `⟨⟨o, m⟩, hm⟩` from `IsLocalization.surj (Algebra.algebraMapSubmonoid (𝓞 E) (nonZeroDivisors ℤ)) x`. Take `⟨_, k, hk, rfl⟩` from `m`.

Establish `hk0 : (k : F) ≠ 0` using `Int.cast_ne_zero.2 (nonZeroDivisors.ne_zero hk)`. Establish `hx : x = (k : F)⁻¹ • algebraMap (𝓞 E) E o`. Rewrite using `[← hm]`. Simplify using `only [eq_intCast, map_intCast, Algebra.smul_def, map_inv₀]`. Establish `: (k : E) ≠ 0` using `Int.cast_ne_zero.2 (nonZeroDivisors.ne_zero hk)`.

Clear the denominators using the available nonvanishing facts. Take `⟨c, hc⟩` from `pow_mul_mem_intAd v p hp (α * ((k : F)⁻¹ • β)) fun w hw => by rw [map_mul, hα w hw, zero_mul]`. Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `e : (p : E ⊗[F] FiniteAdeleRing (𝓞 F) F) ^ c * (((1 : E) ⊗ₜ[F] α) * (x ⊗ₜ[F] β)) = ((algebraMap (𝓞 E) E o) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * ((1 : E) ⊗ₜ[F] ((p : FiniteAdeleRing (𝓞 F) F) ^ c * (α * ((k : F)⁻¹ • β))))`. Establish `hp1 : (p : E ⊗[F] FiniteAdeleRing (𝓞 F) F) = (1 : E) ⊗ₜ[F] (p : FiniteAdeleRing (𝓞 F) F)` using `(map_natCast (Algebra.TensorProduct.includeRight (R := F) (A := E) (B := FiniteAdeleRing (𝓞 F) F)) p).symm`.

Rewrite using `[hp1, Algebra.TensorProduct.tmul_pow, hx, TensorProduct.smul_tmul]`. Simplify using `only [Algebra.TensorProduct.tmul_mul_tmul, one_pow, one_mul, mul_one]`. Rewrite using `[e]`. Conclude with `mul_mem (Subring.subset_closure (Or.inl ⟨⟨_, o, rfl⟩, rfl⟩)) (Subring.subset_closure (Or.inr ⟨⟨_, hc⟩, rfl⟩))`.
-/
theorem pow_mul_mem_intAf (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) (hp : (p : 𝓞 F) ∈ v.asIdeal) (α : FiniteAdeleRing (𝓞 F) F)
    (hα : ∀ w, w ≠ v → evalV F w α = 0) (z : E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    ∃ c : ℕ, (p : E ⊗[F] FiniteAdeleRing (𝓞 F) F) ^ c * (((1 : E) ⊗ₜ[F] α) * z) ∈ Formalism.L2.Herm.intAf F E := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simpa using zero_mem _⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    rw [mul_add, mul_add]
    refine add_mem ?_ ?_
    · rw [add_comm a b, pow_add, mul_assoc]; exact mul_mem (pow_mem (natCast_mem _ p) _) ha
    · rw [pow_add, mul_assoc]; exact mul_mem (pow_mem (natCast_mem _ p) _) hb
  | tmul x β =>
    obtain ⟨⟨o, m⟩, hm⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid (𝓞 E) (nonZeroDivisors ℤ)) x
    obtain ⟨_, k, hk, rfl⟩ := m
    have hk0 : (k : F) ≠ 0 := Int.cast_ne_zero.2 (nonZeroDivisors.ne_zero hk)
    have hx : x = (k : F)⁻¹ • algebraMap (𝓞 E) E o := by
      rw [← hm]
      simp only [eq_intCast, map_intCast, Algebra.smul_def, map_inv₀]
      have : (k : E) ≠ 0 := Int.cast_ne_zero.2 (nonZeroDivisors.ne_zero hk)
      field_simp
    obtain ⟨c, hc⟩ := pow_mul_mem_intAd v p hp (α * ((k : F)⁻¹ • β)) fun w hw => by rw [map_mul, hα w hw, zero_mul]
    refine ⟨c, ?_⟩
    have e : (p : E ⊗[F] FiniteAdeleRing (𝓞 F) F) ^ c * (((1 : E) ⊗ₜ[F] α) * (x ⊗ₜ[F] β)) =
        ((algebraMap (𝓞 E) E o) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) *
          ((1 : E) ⊗ₜ[F] ((p : FiniteAdeleRing (𝓞 F) F) ^ c * (α * ((k : F)⁻¹ • β)))) := by
      have hp1 : (p : E ⊗[F] FiniteAdeleRing (𝓞 F) F) = (1 : E) ⊗ₜ[F] (p : FiniteAdeleRing (𝓞 F) F) :=
        (map_natCast (Algebra.TensorProduct.includeRight (R := F) (A := E) (B := FiniteAdeleRing (𝓞 F) F)) p).symm
      rw [hp1, Algebra.TensorProduct.tmul_pow, hx, TensorProduct.smul_tmul]
      simp only [Algebra.TensorProduct.tmul_mul_tmul, one_pow, one_mul, mul_one]
    rw [e]
    exact mul_mem (Subring.subset_closure (Or.inl ⟨⟨_, o, rfl⟩, rfl⟩)) (Subring.subset_closure (Or.inr ⟨⟨_, hc⟩, rfl⟩))

/- English proof (translation)
Use `set ι := Formalism.UG.inclE (F := F) (E := E) (Formalism.L2.Herm.Af F) with hι`. Use `set B' := Formalism.UG.bc ι B with hB'`. Establish `hcol : ∀ i j, B'.1 i j = ι (B.1 i j)` using `fun _ _ => rfl`. Introduce `x`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨y, hy, rfl⟩` from `hy`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem y hy`. Take `⟨j, rfl⟩` from `hy`. Introduce `i`. Establish `e : ((B'⁻¹).1 *ᵥ fun a => ι (B.1 a j)) i = ((B'⁻¹).1 * B'.1) i j` using `rfl`. Use `show ((B'⁻¹).1 *ᵥ fun a => ι (B.1 a j)) i ∈ _`.

Rewrite using `[e, Units.inv_mul, Matrix.one_apply]`. Use `split_ifs`. Use `exacts [one_mem _, zero_mem _]`. Consider the case `zero`. Introduce `i`.

Establish `e : (fun i => ι ((0 : Fin n → E) i)) = 0` using `by funext k; simp`. Use `show ((B'⁻¹).1 *ᵥ fun i => ι ((0 : Fin n → E) i)) i ∈ _`. Rewrite using `[e, Matrix.mulVec_zero]`. Conclude with `zero_mem _`. Consider the case `add a b _ _ ha hb`.

Introduce `i`. Establish `e : (fun i => ι ((a + b) i)) = (fun i => ι (a i)) + fun i => ι (b i)` using `by funext k; simp`. Use `show ((B'⁻¹).1 *ᵥ fun i => ι ((a + b) i)) i ∈ _`. Rewrite using `[e, Matrix.mulVec_add]`. Conclude with `add_mem (ha i) (hb i)`.

Consider the case `smul o a _ ha`. Introduce `i`. Establish `e : (fun i => ι ((o • a) i)) = ι (algebraMap (𝓞 E) E o) • fun i => ι (a i)`. Use function extensionality and compare the values at `k`. Rewrite using `[Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, map_mul, smul_eq_mul]`.

Use `show ((B'⁻¹).1 *ᵥ fun i => ι ((o • a) i)) i ∈ _`. Rewrite using `[e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]`. Conclude with `mul_mem (Subring.subset_closure (Or.inl ⟨⟨_, o, rfl⟩, rfl⟩)) (ha i)`. Consider the case `zero => intro i`. Rewrite using `[Matrix.mulVec_zero]`.

Conclude with `zero_mem _`. Consider the case `add a b _ _ ha hb => intro i`. Rewrite using `[Matrix.mulVec_add]`. Conclude with `add_mem (ha i) (hb i)`. Consider the case `smul s a _ ha`.

Introduce `i`. Establish `e : s • a = (s : E ⊗[F] Formalism.L2.Herm.Af F) • a` using `rfl`. Rewrite using `[e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]`. Conclude with `mul_mem s.2 (ha i)`. Introduce `hx`.

Establish `e : x = ∑ j, (⟨_, hx j⟩ : Formalism.L2.Herm.intAf F E) • fun a => ι (B.1 a j)`. Establish `h1 : B'.1 *ᵥ ((B'⁻¹).1 *ᵥ x) = x`. Rewrite using `[Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`. Use `conv_lhs => rw [← h1]`. Use function extensionality and compare the values at `a`.

Rewrite using `[Finset.sum_apply]`. Use `show ∑ j, B'.1 a j * ((B'⁻¹).1 *ᵥ x) j = ∑ j, ((B'⁻¹).1 *ᵥ x) j * ι (B.1 a j)`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [hcol, mul_comm]`. Rewrite using `[e]`. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun a => B.1 a j, Submodule.subset_span ⟨j, rfl⟩, rfl⟩)`.
-/
theorem isFrame_colLat {n : ℕ} (B : GL (Fin n) E) :
    IsFrame (F := F) (Formalism.UG.bc (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F)) B) (colLat B) := by
  set ι := Formalism.UG.inclE (F := F) (E := E) (Formalism.L2.Herm.Af F) with hι
  set B' := Formalism.UG.bc ι B with hB'
  have hcol : ∀ i j, B'.1 i j = ι (B.1 i j) := fun _ _ => rfl
  intro x
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨y, hy, rfl⟩ := hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        intro i
        have e : ((B'⁻¹).1 *ᵥ fun a => ι (B.1 a j)) i = ((B'⁻¹).1 * B'.1) i j := rfl
        show ((B'⁻¹).1 *ᵥ fun a => ι (B.1 a j)) i ∈ _
        rw [e, Units.inv_mul, Matrix.one_apply]
        split_ifs
        exacts [one_mem _, zero_mem _]
      | zero =>
        intro i
        have e : (fun i => ι ((0 : Fin n → E) i)) = 0 := by funext k; simp
        show ((B'⁻¹).1 *ᵥ fun i => ι ((0 : Fin n → E) i)) i ∈ _
        rw [e, Matrix.mulVec_zero]; exact zero_mem _
      | add a b _ _ ha hb =>
        intro i
        have e : (fun i => ι ((a + b) i)) = (fun i => ι (a i)) + fun i => ι (b i) := by funext k; simp
        show ((B'⁻¹).1 *ᵥ fun i => ι ((a + b) i)) i ∈ _
        rw [e, Matrix.mulVec_add]; exact add_mem (ha i) (hb i)
      | smul o a _ ha =>
        intro i
        have e : (fun i => ι ((o • a) i)) = ι (algebraMap (𝓞 E) E o) • fun i => ι (a i) := by
          funext k; rw [Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, map_mul, smul_eq_mul]
        show ((B'⁻¹).1 *ᵥ fun i => ι ((o • a) i)) i ∈ _
        rw [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
        exact mul_mem (Subring.subset_closure (Or.inl ⟨⟨_, o, rfl⟩, rfl⟩)) (ha i)
    | zero => intro i; rw [Matrix.mulVec_zero]; exact zero_mem _
    | add a b _ _ ha hb => intro i; rw [Matrix.mulVec_add]; exact add_mem (ha i) (hb i)
    | smul s a _ ha =>
      intro i
      have e : s • a = (s : E ⊗[F] Formalism.L2.Herm.Af F) • a := rfl
      rw [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      exact mul_mem s.2 (ha i)
  · intro hx
    have e : x = ∑ j, (⟨_, hx j⟩ : Formalism.L2.Herm.intAf F E) • fun a => ι (B.1 a j) := by
      have h1 : B'.1 *ᵥ ((B'⁻¹).1 *ᵥ x) = x := by
        rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      conv_lhs => rw [← h1]
      funext a
      rw [Finset.sum_apply]
      show ∑ j, B'.1 a j * ((B'⁻¹).1 *ᵥ x) j = ∑ j, ((B'⁻¹).1 *ᵥ x) j * ι (B.1 a j)
      exact Finset.sum_congr rfl fun j _ => by rw [hcol, mul_comm]
    rw [e]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨fun a => B.1 a j, Submodule.subset_span ⟨j, rfl⟩, rfl⟩)

/- English proof (translation)
Take `⟨c, hc⟩` from `conj_int (Formalism.L2.Herm.intAf F E) _ p (pow_mul_mem_intAf (E := E) v p hp α hα) (y * β) (g⁻¹).1 (supp_inv _ g hg)`. Use `⟨c, fun x hx => ?_⟩` and prove the remaining obligations. Use `set ι := Formalism.UG.inclE (F := F) (E := E) (Formalism.L2.Herm.Af F) with hι`. Establish `hx1` using `(hβ ((y⁻¹).1 *ᵥ fun i => ι (x i))).1 hx`. Establish `e1 : ∀ z, (β⁻¹).1 *ᵥ ((y⁻¹).1 *ᵥ z) = ((y * β)⁻¹).1 *ᵥ z` using `fun z => by`.

Rewrite using `[Matrix.mulVec_mulVec, _root_.mul_inv_rev, Units.val_mul]`. Rewrite `hx1` using `[e1]`. Establish `h2` using `hc _ hx1`. Use `(hβ (((g * y)⁻¹).1 *ᵥ fun i => ι ((((p ^ c : ℕ) : 𝓞 E) • x) i))).2 fun i => ?_` and prove the remaining obligations. Establish `e2 : (fun i => ι ((((p ^ c : ℕ) : 𝓞 E) • x) i)) = ((p : E ⊗[F] Formalism.L2.Herm.Af F) ^ c) • fun i => ι (x i)`.

Use function extensionality and compare the values at `k`. Rewrite using `[Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, map_mul, map_natCast, map_natCast, smul_eq_mul, Nat.cast_pow]`. Rewrite using `[e2, Matrix.mulVec_smul, Matrix.mulVec_smul, _root_.mul_inv_rev g y, Units.val_mul, ← Matrix.mulVec_mulVec, e1, Pi.smul_apply, smul_eq_mul]`. Conclude with `h2 i`.
-/
theorem globLat_le {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hβ : IsFrame β Λ)
    (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) (hp : (p : 𝓞 F) ∈ v.asIdeal) (α : FiniteAdeleRing (𝓞 F) F)
    (hα : ∀ w, w ≠ v → evalV F w α = 0) (g y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hg : ((1 : E) ⊗ₜ[F] α : E ⊗[F] Formalism.L2.Herm.Af F) • (g.1 - 1) = g.1 - 1) :
    ∃ c : ℕ, ∀ x ∈ Formalism.UG.CS.globLat y Λ, ((p ^ c : ℕ) : 𝓞 E) • x ∈ Formalism.UG.CS.globLat (g * y) Λ := by
  obtain ⟨c, hc⟩ := conj_int (Formalism.L2.Herm.intAf F E) _ p (pow_mul_mem_intAf (E := E) v p hp α hα) (y * β) (g⁻¹).1
    (supp_inv _ g hg)
  refine ⟨c, fun x hx => ?_⟩
  set ι := Formalism.UG.inclE (F := F) (E := E) (Formalism.L2.Herm.Af F) with hι
  have hx1 := (hβ ((y⁻¹).1 *ᵥ fun i => ι (x i))).1 hx
  have e1 : ∀ z, (β⁻¹).1 *ᵥ ((y⁻¹).1 *ᵥ z) = ((y * β)⁻¹).1 *ᵥ z := fun z => by
    rw [Matrix.mulVec_mulVec, _root_.mul_inv_rev, Units.val_mul]
  rw [e1] at hx1
  have h2 := hc _ hx1
  refine (hβ (((g * y)⁻¹).1 *ᵥ fun i => ι ((((p ^ c : ℕ) : 𝓞 E) • x) i))).2 fun i => ?_
  have e2 : (fun i => ι ((((p ^ c : ℕ) : 𝓞 E) • x) i)) = ((p : E ⊗[F] Formalism.L2.Herm.Af F) ^ c) • fun i => ι (x i) := by
    funext k
    rw [Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, map_mul, map_natCast, map_natCast, smul_eq_mul, Nat.cast_pow]
  rw [e2, Matrix.mulVec_smul, Matrix.mulVec_smul, _root_.mul_inv_rev g y, Units.val_mul, ← Matrix.mulVec_mulVec, e1,
    Pi.smul_apply, smul_eq_mul]
  exact h2 i

/- English proof (translation)
Take `⟨c, hc⟩` from `globLat_le Λ β hβ v p hp α hα g y hg`. Take `⟨d, hd⟩` from `globLat_le Λ β hβ v p hp α hα g⁻¹ (g * y) (supp_inv _ _ hg)`. Rewrite `hd` using `[inv_mul_cancel_left]`. Use `⟨c + d, fun x hx => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[pow_add, Nat.cast_mul, mul_smul]`.

Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Rewrite `hx`, the goal using `[Submodule.mem_comap]`. Rewrite using `[map_smul]`. Conclude with `hd _ hx`. Rewrite using `[add_comm, pow_add, Nat.cast_mul, mul_smul]`.

Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Rewrite `hx`, the goal using `[Submodule.mem_comap]`. Rewrite using `[map_smul]`. Conclude with `hc _ hx`.
-/
theorem globLat_both {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hβ : IsFrame β Λ)
    (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) (hp : (p : 𝓞 F) ∈ v.asIdeal) (α : FiniteAdeleRing (𝓞 F) F)
    (hα : ∀ w, w ≠ v → evalV F w α = 0) (g y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hg : ((1 : E) ⊗ₜ[F] α : E ⊗[F] Formalism.L2.Herm.Af F) • (g.1 - 1) = g.1 - 1) (f : (Fin n → E) →ₗ[𝓞 E] (Fin n → E)) :
    ∃ c : ℕ, (∀ x ∈ (Formalism.UG.CS.globLat (g * y) Λ).comap f, ((p ^ c : ℕ) : 𝓞 E) • x ∈ (Formalism.UG.CS.globLat y Λ).comap f) ∧
      ∀ x ∈ (Formalism.UG.CS.globLat y Λ).comap f, ((p ^ c : ℕ) : 𝓞 E) • x ∈ (Formalism.UG.CS.globLat (g * y) Λ).comap f := by
  obtain ⟨c, hc⟩ := globLat_le Λ β hβ v p hp α hα g y hg
  obtain ⟨d, hd⟩ := globLat_le Λ β hβ v p hp α hα g⁻¹ (g * y) (supp_inv _ _ hg)
  rw [inv_mul_cancel_left] at hd
  refine ⟨c + d, fun x hx => ?_, fun x hx => ?_⟩
  · rw [pow_add, Nat.cast_mul, mul_smul]
    refine Submodule.smul_mem _ _ ?_
    rw [Submodule.mem_comap] at hx ⊢
    rw [map_smul]
    exact hd _ hx
  · rw [add_comm, pow_add, Nat.cast_mul, mul_smul]
    refine Submodule.smul_mem _ _ ?_
    rw [Submodule.mem_comap] at hx ⊢
    rw [map_smul]
    exact hc _ hx

/- English proof (translation)
Establish `h0 : Ideal.absNorm v.asIdeal ≠ 0` using `fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)`. Take `⟨k, m, hm, e⟩` from `Nat.exists_eq_pow_mul_and_not_dvd h0 q hq.ne_one`. Use `⟨m, ?_, ((Nat.Prime.coprime_iff_not_dvd hq).2 hm).symm⟩` and prove the remaining obligations. Establish `h1` using `Ideal.absNorm_mem v.asIdeal`. Rewrite `h1` using `[e, Nat.cast_mul, Nat.cast_pow]`.

Conclude with `(v.isPrime.mem_or_mem h1).resolve_left fun h => hqv (v.isPrime.mem_of_pow_mem _ h)`.
-/
theorem exists_nat_coprime (v : HeightOneSpectrum (𝓞 F)) {q : ℕ} (hq : q.Prime) (hqv : (q : 𝓞 F) ∉ v.asIdeal) :
    ∃ p : ℕ, (p : 𝓞 F) ∈ v.asIdeal ∧ p.Coprime q := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  obtain ⟨k, m, hm, e⟩ := Nat.exists_eq_pow_mul_and_not_dvd h0 q hq.ne_one
  refine ⟨m, ?_, ((Nat.Prime.coprime_iff_not_dvd hq).2 hm).symm⟩
  have h1 := Ideal.absNorm_mem v.asIdeal
  rw [e, Nat.cast_mul, Nat.cast_pow] at h1
  exact (v.isPrime.mem_or_mem h1).resolve_left fun h => hqv (v.isPrime.mem_of_pow_mem _ h)

/- English proof (translation)
Introduce `x`. Establish `h1` using `hu ((u⁻¹).1 *ᵥ x)`. Rewrite `h1` using `[Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`. Rewrite using `[← h1, hβ _, Matrix.mulVec_mulVec, _root_.mul_inv_rev, Units.val_mul]`.
-/
theorem isFrame_mul {n : ℕ} (Λ C : Submodule (𝓞 E) (Fin n → E)) (u β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hβ : IsFrame β C)
    (hu : ∀ w, w ∈ Formalism.L2.Herm.hatL (F := F) C ↔ u.1 *ᵥ w ∈ Formalism.L2.Herm.hatL (F := F) Λ) : IsFrame (u * β) Λ := by
  intro x
  have h1 := hu ((u⁻¹).1 *ᵥ x)
  rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at h1
  rw [← h1, hβ _, Matrix.mulVec_mulVec, _root_.mul_inv_rev, Units.val_mul]

end Adeles

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `h0 : Formalism.IndefR.Datum.toEAf D (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (pairA D.host.F 0 α)) = (1 : D.host.E) ⊗ₜ[D.host.F] α` using `rfl`. Establish `h1 : (Formalism.IndefR.Lev.finE V g).1 - 1 = (Formalism.IndefR.Datum.toEAf D).mapMatrix (Formalism.L2.Theta.mt V g - 1)`. Rewrite using `[map_sub, map_one]`. Both sides reduce to the same expression. Rewrite using `[h1]`.

Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Use `show _ * Formalism.IndefR.Datum.toEAf D _ = Formalism.IndefR.Datum.toEAf D _`. Rewrite using `[← h0, ← map_mul, ← hsum, hs i j]`.
-/
theorem finE_supp {D : D7} (V : HSp D) (e : Formalism.L2.Theta.AE D) (α : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)
    (hsum : e + cA D e = algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (pairA D.host.F 0 α)) (g : Formalism.L2.Theta.GA D V)
    (hs : SuppAt e V g) :
    ((1 : D.host.E) ⊗ₜ[D.host.F] α : Formalism.IndefR.Lev.EAf D) • ((Formalism.IndefR.Lev.finE V g).1 - 1) = (Formalism.IndefR.Lev.finE V g).1 - 1 := by
  have h0 : Formalism.IndefR.Datum.toEAf D (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (pairA D.host.F 0 α)) =
    (1 : D.host.E) ⊗ₜ[D.host.F] α := rfl
  have h1 : (Formalism.IndefR.Lev.finE V g).1 - 1 = (Formalism.IndefR.Datum.toEAf D).mapMatrix (Formalism.L2.Theta.mt V g - 1) := by
    rw [map_sub, map_one]; rfl
  rw [h1]
  refine Matrix.ext fun i j => ?_
  show _ * Formalism.IndefR.Datum.toEAf D _ = Formalism.IndefR.Datum.toEAf D _
  rw [← h0, ← map_mul, ← hsum, hs i j]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D T L sc G W S X hX q hq e he hoff g y hs`. Take `⟨-, -, v, ε, hε, hsum⟩` from `he`. Establish `hqv` using `hoff v ε hε hsum`. Take `⟨α, rfl, -, hα⟩` from `hε`. Take `⟨p, hpv, hcop⟩` from `exists_nat_coprime v hq hqv`.

Establish `hβ` using `isFrame_mul (F := D.host.F) (G.Λ X) _ _ _ (isFrame_colLat (S.N.fr X)) (S.N.u_lat X hX)`. Take `⟨c, hc⟩` from `globLat_both (G.Λ X) _ hβ v p hpv α hα (finG (G.V X) g) (finG (G.V X) y) (finE_supp (G.V X) e α hsum g.1 hs) ((S.N.fr X).1.mulVecLin.restrictScalars (𝓞 D.host.E))`. Rewrite `hc` using `[← map_mul]`. Conclude with `⟨p ^ c, Nat.Coprime.pow_left _ hcop, hc⟩`.
-/
theorem eqAt_latAt_mul : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil}
    (S : GridChoice W Set.univ) (X : Node), DefNode D.R.m X → ∀ (q : ℕ), q.Prime → ∀ e : Formalism.L2.Theta.AE D, IsSplitIdem D e →
    GlobalTheory.MovedKappaEx.OffPrime e q → ∀ g y : FinPt G X, SuppAt e (G.V X) g.1 →
    EqAt D q (GlobalTheory.SumSize.latAt S X (g * y)) (GlobalTheory.SumSize.latAt S X y) := by
  intro D T L sc G W S X hX q hq e he hoff g y hs
  obtain ⟨-, -, v, ε, hε, hsum⟩ := he
  have hqv := hoff v ε hε hsum
  obtain ⟨α, rfl, -, hα⟩ := hε
  obtain ⟨p, hpv, hcop⟩ := exists_nat_coprime v hq hqv
  have hβ := isFrame_mul (F := D.host.F) (G.Λ X) _ _ _ (isFrame_colLat (S.N.fr X)) (S.N.u_lat X hX)
  obtain ⟨c, hc⟩ := globLat_both (G.Λ X) _ hβ v p hpv α hα (finG (G.V X) g) (finG (G.V X) y)
    (finE_supp (G.V X) e α hsum g.1 hs) ((S.N.fr X).1.mulVecLin.restrictScalars (𝓞 D.host.E))
  rw [← map_mul] at hc
  exact ⟨p ^ c, Nat.Coprime.pow_left _ hcop, hc⟩

end GlobalTheory.MovedSplitEq

end
