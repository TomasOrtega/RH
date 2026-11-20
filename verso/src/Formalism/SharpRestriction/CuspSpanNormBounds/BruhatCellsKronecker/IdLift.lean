import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.IdLiftDef
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.LadjFrame
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.LTheta
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.LretrCancel
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.LisoSmulMem
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.LFrame

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.LatticeGluingRadicals NumberField Module IsDedekindDomain

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

/- English proof (translation)
Establish `hn` using `S.nondeg`. Unfold `LinearMap.Nondegenerate LinearMap.SeparatingRight at hn`. Conclude with `sub_eq_zero.mp (hn.2 (a - b) (fun w => by rw [map_sub, h w, sub_self]))`.
-/
theorem lift_sep {a b : S.V} (h : ∀ w, S.hT w a = S.hT w b) : a = b := by
  have hn := S.nondeg
  unfold LinearMap.Nondegenerate LinearMap.SeparatingRight at hn
  exact sub_eq_zero.mp (hn.2 (a - b) (fun w => by rw [map_sub, h w, sub_self]))

/- English proof (translation)
Introduce `x y`. Rewrite using `[← S.herm.eq y (B' x), ← h y x]`. Conclude with `S.herm.eq (B y) x`.
-/
theorem lift_adj_symm {B B' : S.V →ₗ[E] S.V} (h : LAdj S B B') : LAdj S B' B := by
  intro x y
  rw [← S.herm.eq y (B' x), ← h y x]
  exact S.herm.eq (B y) x

/- English proof (translation)
Take `⟨g, hg⟩` from `LinearMap.exists_extend ((Finsupp.linearCombination E w).comp hli.repr)`. Use `⟨g, fun a => ?_⟩` and prove the remaining obligations. Establish `hmem : e a ∈ Submodule.span E (Set.range e)` using `Submodule.subset_span ⟨a, rfl⟩`. Establish `h1` using `LinearMap.congr_fun hg ⟨e a, hmem⟩`. Simplify using `only [LinearMap.comp_apply, Submodule.subtype_apply] at h1`.

Rewrite using `[h1, hli.repr_eq_single a ⟨e a, hmem⟩ rfl, Finsupp.linearCombination_single, one_smul]`.
-/
theorem lift_exists_map {ι : Type} (e w : ι → S.V) (hli : LinearIndependent E e) :
    ∃ U : S.V →ₗ[E] S.V, ∀ a, U (e a) = w a := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Finsupp.linearCombination E w).comp hli.repr)
  refine ⟨g, fun a => ?_⟩
  have hmem : e a ∈ Submodule.span E (Set.range e) := Submodule.subset_span ⟨a, rfl⟩
  have h1 := LinearMap.congr_fun hg ⟨e a, hmem⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h1
  rw [h1, hli.repr_eq_single a ⟨e a, hmem⟩ rfl, Finsupp.linearCombination_single, one_smul]

variable {r : ℕ} {T : E}

/- English proof (translation)
Establish `hXiso : ∀ x ∈ Xsp F, ∀ y ∈ Xsp F, S.hT x y = 0`. Establish `h1 : ∀ a, ∀ y ∈ Xsp F, S.hT (F.fl.e a) y = 0`. Introduce `a y hy`. Use `replace hy : y ∈ Submodule.span E (Set.range F.fl.e) := hy`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem z hz`. Take `⟨b, rfl⟩` from `hz`. Conclude with `F.fl.e_iso a b`. Consider the case `zero => simp`. Consider the case `add z z' _ _ hz hz' => rw [map_add, hz, hz', add_zero]`.

Consider the case `smul c z _ hz => rw [map_smul, hz, smul_zero]`. Introduce `x hx y hy`. Use `replace hx : x ∈ Submodule.span E (Set.range F.fl.e) := hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem z hz`.

Take `⟨a, rfl⟩` from `hz`. Conclude with `h1 a y hy`. Consider the case `zero => simp`. Consider the case `add z z' _ _ hz hz' => rw [map_add, LinearMap.add_apply, hz, hz', add_zero]`. Consider the case `smul c z _ hz => rw [map_smulₛₗ, LinearMap.smul_apply, hz, smul_zero]`.

Establish `hXa_le : ∀ j, Xflag F j ≤ Xsp F` using `fun j => Submodule.span_mono (Set.image_subset_range _ _)`. Establish `hX_le : Xsp F ≤ Xflag F r` using `Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨i, i.isLt, rfl⟩)`. Establish `hXa_mono : ∀ {i j : ℕ}, i ≤ j → Xflag F i ≤ Xflag F j` using `fun hij => Submodule.span_mono (Set.image_mono fun a (ha : a.1 < _) => lt_of_lt_of_le ha hij)`. Establish `hXa0 : Xflag F 0 = ⊥` using `by show Submodule.span E (F.fl.e '' {i | i.1 < 0}) = ⊥`. Simplify using the standard rewrite rules.

Take `⟨U0, hU0⟩` from `lift_exists_map F.fl.e F'.fl.e F.fl.e_indep`. Establish `hU0X : ∀ j, ∀ x ∈ Xflag F j, U0 x - x ∈ Xflag F (j - 1)`. Introduce `j x hx`. Use `replace hx : x ∈ Submodule.span E (F.fl.e '' {i | i.1 < j}) := hx`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem z hz`. Take `⟨i, hi, rfl⟩` from `hz`. Rewrite using `[hU0]`. Conclude with `hXa_mono (by have : i.1 < j := hi; omega) (he i)`. Consider the case `zero => simp`.

Consider the case `add z z' _ _ hz hz'`. Rewrite using `[map_add, add_sub_add_comm]`. Conclude with `Submodule.add_mem _ hz hz'`. Consider the case `smul c z _ hz`. Rewrite using `[map_smul, ← smul_sub]`.

Conclude with `Submodule.smul_mem _ c hz`. Establish `hFU : ∀ x ∈ Λ, x ∈ Xsp F → U0 x ∈ Λ` using `hF E S r T Λ g F F' hconv hconv' he U0 hU0`. Take `⟨P, P', hPP', hPX, hPr, hPi, hP'i, hP'iso⟩` from `hI E S Λ (Xsp F) hcm hlat huni hXiso`. Take `⟨N0, hN0⟩ : ∃ N0 : Module.End E S.V, N0 = (U0 - 1) * P` from `⟨_, rfl⟩`. Establish `hN0apply : ∀ x, N0 x = U0 (P x) - P x` using `fun x => by`.

Rewrite using `[hN0, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply]`. Establish `hN0X : ∀ x, N0 x ∈ Xsp F` using `fun x => by`. Rewrite using `[hN0apply]`. Conclude with `hXa_le _ (hU0X r (P x) (hX_le (hPr x)))`. Establish `hN0int : LInt Λ N0` using `fun l hl => by`.

Rewrite using `[hN0apply]`. Conclude with `Submodule.sub_mem _ (hFU _ (hPi l hl) (hPr l)) (hPi l hl)`. Establish `hN0onX : ∀ x ∈ Xsp F, N0 x = U0 x - x` using `fun x hx => by rw [hN0apply, hPX x hx]`. Take `⟨N1, hN01, hN1int⟩` from `hA E S Λ huni N0 hN0int`. Establish `hN10 : LAdj S N1 N0` using `lift_adj_symm hN01`.

Establish `hN1X : ∀ x ∈ Xsp F, N1 x = 0` using `fun x hx => lift_sep fun w => by`. Rewrite using `[← hN01 w x, hXiso _ (hN0X w) x hx, map_zero]`. Establish `hN1orth : ∀ x ∈ orth S (Xsp F), N1 x = 0` using `fun x hx => lift_sep fun w => by`. Rewrite using `[← hN01 w x, map_zero]`. Establish `h' : x ∈ LinearMap.ker (S.hT (N0 w))`.

Simplify using `only [orth, Submodule.mem_iInf] at hx`. Conclude with `hx _ (hN0X w)`. Conclude with `LinearMap.mem_ker.1 h'`. Establish `hP'P : LAdj S P' P` using `lift_adj_symm hPP'`. Establish `hPP'0 : ∀ w, P (P' w) = 0` using `fun w => lift_sep fun z => by`.

Rewrite using `[← hP'P z (P' w), hP'iso, map_zero]`. Establish `hPN1 : ∀ y, P (N1 y) = 0` using `fun y => lift_sep fun w => by`. Rewrite using `[← hP'P w (N1 y), ← hN01 (P' w) y, hN0apply, hPP'0]`. Simplify using the standard rewrite rules. Establish `hN0N1 : ∀ y, N0 (N1 y) = 0` using `fun y => by rw [hN0apply, hPN1, map_zero, sub_zero]`.

Establish `hN0iso : ∀ a b, S.hT (N0 a) (N0 b) = 0` using `fun a b => hXiso _ (hN0X a) _ (hN0X b)`. Establish `hN0pow : ∀ k x, (N0 ^ (k + 1)) x ∈ Xflag F (r - k)`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro x`.

Simplify using `using hX_le (hN0X x)`. Consider the case `succ k ih`. Introduce `x`. Rewrite using `[pow_succ', Module.End.mul_apply]`. Establish `hy` using `ih x`.

Rewrite using `[hN0onX _ (hXa_le _ hy)]`. Use `hU0X (r - k) _ hy` as an intermediate fact. Rewrite `this` using `[show r - k - 1 = r - (k + 1) by omega]`. Then use the resulting hypothesis. Establish `hN0nil : N0 ^ (r + 1) = 0`. Use extensionality with `x`.

Use `hN0pow r x` as an intermediate fact. Rewrite `this` using `[Nat.sub_self, hXa0, Submodule.mem_bot]`. Simplify using `using this`. Establish `hadjpow : ∀ k a b, S.hT ((N0 ^ k) a) b = S.hT a ((N1 ^ k) b)`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => intro a b`. Simplify using the standard rewrite rules. Consider the case `succ k ih`. Introduce `a b`.

Rewrite using `[pow_succ', Module.End.mul_apply, hN01, ih, pow_succ, Module.End.mul_apply]`. Establish `hN1nil : N1 ^ (r + 1) = 0`. Use extensionality with `y`. Use `lift_sep fun w => ?_` and prove the remaining obligations. Rewrite using `[← hadjpow, hN0nil]`.

Simplify using the standard rewrite rules. Take `⟨S1, hS1⟩ : ∃ S1 : Module.End E S.V, S1 = ∑ k ∈ Finset.range (r + 1), (-N1) ^ k` from `⟨_, rfl⟩`. Take `⟨S0, hS0⟩ : ∃ S0 : Module.End E S.V, S0 = ∑ k ∈ Finset.range (r + 1), (-N0) ^ k` from `⟨_, rfl⟩`. Establish `hS1l : (1 + N1) * S1 = 1`. Use `mul_neg_geom_sum (-N1) (r + 1)` as an intermediate fact.

Rewrite `this` using `[sub_neg_eq_add, neg_pow, hN1nil, mul_zero, sub_zero, ← hS1]`. Then use the resulting hypothesis. Establish `hS1r : S1 * (1 + N1) = 1`. Use `geom_sum_mul_neg (-N1) (r + 1)` as an intermediate fact. Rewrite `this` using `[sub_neg_eq_add, neg_pow, hN1nil, mul_zero, sub_zero, ← hS1]`. Then use the resulting hypothesis. Establish `hS0l : (1 + N0) * S0 = 1`.

Use `mul_neg_geom_sum (-N0) (r + 1)` as an intermediate fact. Rewrite `this` using `[sub_neg_eq_add, neg_pow, hN0nil, mul_zero, sub_zero, ← hS0]`. Then use the resulting hypothesis. Establish `hS0r : S0 * (1 + N0) = 1`. Use `geom_sum_mul_neg (-N0) (r + 1)` as an intermediate fact. Rewrite `this` using `[sub_neg_eq_add, neg_pow, hN0nil, mul_zero, sub_zero, ← hS0]`. Then use the resulting hypothesis.

Establish `hnn : ((1 + N0) * S1) * ((1 + N1) * S0) = 1`. Rewrite using `[mul_assoc, ← mul_assoc S1, hS1r, one_mul, hS0l]`. Establish `hnn' : ((1 + N1) * S0) * ((1 + N0) * S1) = 1`. Rewrite using `[mul_assoc, ← mul_assoc S0, hS0r, one_mul, hS1l]`. Set `n : S.V ≃ₗ[E] S.V` to `LinearEquiv.ofLinearMap ((1 + N0) * S1) ((1 + N1) * S0) hnn hnn'`.

Establish `hS1fix : ∀ x, N1 x = 0 → S1 x = x`. Introduce `x hx`. Rewrite using `[hS1, LinearMap.sum_apply, Finset.sum_range_succ', pow_zero, Module.End.one_apply, Finset.sum_eq_zero fun k _ => by`. Rewrite using `[pow_succ, Module.End.mul_apply, LinearMap.neg_apply, hx, neg_zero, map_zero], zero_add]`. Establish `hnfix : ∀ x, N1 x = 0 → n x = x + N0 x`.

Introduce `x hx`. Use `show ((1 + N0) * S1) x = x + N0 x`. Rewrite using `[Module.End.mul_apply, hS1fix x hx, LinearMap.add_apply, Module.End.one_apply]`. Establish `hiso : n ∈ Formalism.HermitianLatticesTheory.isom S.hT`. Introduce `x y`.

Establish `hx : x = (1 + N1) (S1 x)` using `by rw [← Module.End.mul_apply, hS1l, Module.End.one_apply]`. Establish `hy : y = (1 + N1) (S1 y)` using `by rw [← Module.End.mul_apply, hS1l, Module.End.one_apply]`. Use `show S.hT (((1 + N0) * S1) x) (((1 + N0) * S1) y) = S.hT x y`. Rewrite using `[Module.End.mul_apply, Module.End.mul_apply]`. Use `conv_rhs => rw [hx, hy]`.

Generalize the expression as in `S1 x = s`. Generalize the expression as in `S1 y = t`. Simplify using `only [LinearMap.add_apply, Module.End.one_apply, map_add]`. Rewrite using `[hN0iso s t, hN01 s t, hN10 s t, ← hN01 (N1 s) t, hN0N1]`. Simplify using `only [map_zero, LinearMap.zero_apply, add_zero]`.

Expand and normalize the polynomial expressions, which then agree. Establish `lint_pow : ∀ B : Module.End E S.V, LInt Λ B → ∀ k, LInt Λ (B ^ k)`. Introduce `B hB k`. Proceed by induction on `k with`. Consider the case `zero => intro l hl`.

Simplify using `using hl`. Consider the case `succ k ih`. Introduce `l hl`. Rewrite using `[pow_succ', Module.End.mul_apply]`. Conclude with `hB _ (ih l hl)`.

Establish `lint_neg : ∀ B : Module.End E S.V, LInt Λ B → LInt Λ (-B)` using `fun B hB l hl => by`. Rewrite using `[LinearMap.neg_apply]`. Conclude with `Submodule.neg_mem _ (hB l hl)`. Establish `lint_sum : ∀ (f : ℕ → Module.End E S.V) (s : Finset ℕ), (∀ k ∈ s, LInt Λ (f k)) → LInt Λ (∑ k ∈ s, f k)` using `fun f s hf l hl => by`. Rewrite using `[LinearMap.sum_apply]`.

Conclude with `Submodule.sum_mem _ fun k hk => hf k hk l hl`. Establish `lint_one_add : ∀ B : Module.End E S.V, LInt Λ B → LInt Λ (1 + B)` using `fun B hB l hl => by`. Rewrite using `[LinearMap.add_apply, Module.End.one_apply]`. Conclude with `Submodule.add_mem _ hl (hB l hl)`. Establish `lint_mul : ∀ B C : Module.End E S.V, LInt Λ B → LInt Λ C → LInt Λ (B * C)` using `fun B C hB hC l hl => by`.

Rewrite using `[Module.End.mul_apply]`. Conclude with `hB _ (hC l hl)`. Establish `hnint : LInt Λ ((1 + N0) * S1)` using `lint_mul _ _ (lint_one_add _ hN0int) (hS1 ▸ lint_sum _ _ fun k _ => lint_pow _ (lint_neg _ hN1int) k)`. Establish `hninvint : LInt Λ ((1 + N1) * S0)` using `lint_mul _ _ (lint_one_add _ hN1int) (hS0 ▸ lint_sum _ _ fun k _ => lint_pow _ (lint_neg _ hN0int) k)`. Establish `hgmap : Formalism.HermitianLatticesTheory.gmap n Λ = Λ`.

Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨l, hl, rfl⟩`. Conclude with `hnint l hl`. Introduce `l hl`. Use `⟨((1 + N1) * S0) l, hninvint l hl, ?_⟩` and prove the remaining obligations.

Use `show ((1 + N0) * S1) (((1 + N1) * S0) l) = l`. Rewrite using `[← Module.End.mul_apply, hnn, Module.End.one_apply]`. Use `⟨n, ⟨⟨hiso, hgmap⟩, ?_, ?_⟩, fun a => ?_⟩` and prove the remaining obligations. Introduce `j x hx`. Establish `hxX : x ∈ Xsp F` using `hXa_le _ hx`.

Rewrite using `[hnfix x (hN1X x hxX), add_sub_cancel_left, hN0onX x hxX]`. Simplify using `using hU0X (j + 1) x hx`. Introduce `x hx`. Rewrite using `[hnfix x (hN1orth x hx), add_sub_cancel_left]`. Conclude with `hN0X x`.

Establish `hx : F.fl.e a ∈ Xsp F` using `Submodule.subset_span ⟨a, rfl⟩`. Rewrite using `[hnfix _ (hN1X _ hx), hN0onX _ hx, hU0]`. Normalize the expressions using the abelian group laws.
-/
theorem lift_gen (hA : IntegralAdjointUnimodular) (hI : IsotropicIntegralRetraction) (hF : UnitriangularFrameIntegral) (hcm : Formalism.HermitianLatticesTheory.IsCMUnram E)
    (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F F' : LFlag S r T) (hlat : Submodule.IsLattice E Λ)
    (huni : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (hconv : IsFixedConv Λ g F) (hconv' : IsFixedConv Λ g F')
    (he : ∀ a, F'.fl.e a - F.fl.e a ∈ Xflag F a.val) :
    ∃ n ∈ NLam Λ F, ∀ a, n (F.fl.e a) = F'.fl.e a := by

  have hXiso : ∀ x ∈ Xsp F, ∀ y ∈ Xsp F, S.hT x y = 0 := by
    have h1 : ∀ a, ∀ y ∈ Xsp F, S.hT (F.fl.e a) y = 0 := by
      intro a y hy
      replace hy : y ∈ Submodule.span E (Set.range F.fl.e) := hy
      induction hy using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨b, rfl⟩ := hz
        exact F.fl.e_iso a b
      | zero => simp
      | add z z' _ _ hz hz' => rw [map_add, hz, hz', add_zero]
      | smul c z _ hz => rw [map_smul, hz, smul_zero]
    intro x hx y hy
    replace hx : x ∈ Submodule.span E (Set.range F.fl.e) := hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, rfl⟩ := hz
      exact h1 a y hy
    | zero => simp
    | add z z' _ _ hz hz' => rw [map_add, LinearMap.add_apply, hz, hz', add_zero]
    | smul c z _ hz => rw [map_smulₛₗ, LinearMap.smul_apply, hz, smul_zero]
  have hXa_le : ∀ j, Xflag F j ≤ Xsp F := fun j => Submodule.span_mono (Set.image_subset_range _ _)
  have hX_le : Xsp F ≤ Xflag F r :=
    Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨i, i.isLt, rfl⟩)
  have hXa_mono : ∀ {i j : ℕ}, i ≤ j → Xflag F i ≤ Xflag F j := fun hij =>
    Submodule.span_mono (Set.image_mono fun a (ha : a.1 < _) => lt_of_lt_of_le ha hij)
  have hXa0 : Xflag F 0 = ⊥ := by
    show Submodule.span E (F.fl.e '' {i | i.1 < 0}) = ⊥
    simp

  obtain ⟨U0, hU0⟩ := lift_exists_map F.fl.e F'.fl.e F.fl.e_indep
  have hU0X : ∀ j, ∀ x ∈ Xflag F j, U0 x - x ∈ Xflag F (j - 1) := by
    intro j x hx
    replace hx : x ∈ Submodule.span E (F.fl.e '' {i | i.1 < j}) := hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, hi, rfl⟩ := hz
      rw [hU0]
      exact hXa_mono (by have : i.1 < j := hi; omega) (he i)
    | zero => simp
    | add z z' _ _ hz hz' =>
      rw [map_add, add_sub_add_comm]
      exact Submodule.add_mem _ hz hz'
    | smul c z _ hz =>
      rw [map_smul, ← smul_sub]
      exact Submodule.smul_mem _ c hz
  have hFU : ∀ x ∈ Λ, x ∈ Xsp F → U0 x ∈ Λ := hF E S r T Λ g F F' hconv hconv' he U0 hU0
  obtain ⟨P, P', hPP', hPX, hPr, hPi, hP'i, hP'iso⟩ := hI E S Λ (Xsp F) hcm hlat huni hXiso

  obtain ⟨N0, hN0⟩ : ∃ N0 : Module.End E S.V, N0 = (U0 - 1) * P := ⟨_, rfl⟩
  have hN0apply : ∀ x, N0 x = U0 (P x) - P x := fun x => by
    rw [hN0, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply]
  have hN0X : ∀ x, N0 x ∈ Xsp F := fun x => by
    rw [hN0apply]
    exact hXa_le _ (hU0X r (P x) (hX_le (hPr x)))
  have hN0int : LInt Λ N0 := fun l hl => by
    rw [hN0apply]
    exact Submodule.sub_mem _ (hFU _ (hPi l hl) (hPr l)) (hPi l hl)
  have hN0onX : ∀ x ∈ Xsp F, N0 x = U0 x - x := fun x hx => by rw [hN0apply, hPX x hx]
  obtain ⟨N1, hN01, hN1int⟩ := hA E S Λ huni N0 hN0int
  have hN10 : LAdj S N1 N0 := lift_adj_symm hN01
  have hN1X : ∀ x ∈ Xsp F, N1 x = 0 := fun x hx => lift_sep fun w => by
    rw [← hN01 w x, hXiso _ (hN0X w) x hx, map_zero]
  have hN1orth : ∀ x ∈ orth S (Xsp F), N1 x = 0 := fun x hx => lift_sep fun w => by
    rw [← hN01 w x, map_zero]
    have h' : x ∈ LinearMap.ker (S.hT (N0 w)) := by
      simp only [orth, Submodule.mem_iInf] at hx
      exact hx _ (hN0X w)
    exact LinearMap.mem_ker.1 h'
  have hP'P : LAdj S P' P := lift_adj_symm hPP'
  have hPP'0 : ∀ w, P (P' w) = 0 := fun w => lift_sep fun z => by
    rw [← hP'P z (P' w), hP'iso, map_zero]
  have hPN1 : ∀ y, P (N1 y) = 0 := fun y => lift_sep fun w => by
    rw [← hP'P w (N1 y), ← hN01 (P' w) y, hN0apply, hPP'0]
    simp
  have hN0N1 : ∀ y, N0 (N1 y) = 0 := fun y => by rw [hN0apply, hPN1, map_zero, sub_zero]
  have hN0iso : ∀ a b, S.hT (N0 a) (N0 b) = 0 := fun a b => hXiso _ (hN0X a) _ (hN0X b)

  have hN0pow : ∀ k x, (N0 ^ (k + 1)) x ∈ Xflag F (r - k) := by
    intro k
    induction k with
    | zero => intro x; simpa using hX_le (hN0X x)
    | succ k ih =>
      intro x
      rw [pow_succ', Module.End.mul_apply]
      have hy := ih x
      rw [hN0onX _ (hXa_le _ hy)]
      have := hU0X (r - k) _ hy
      rwa [show r - k - 1 = r - (k + 1) by omega] at this
  have hN0nil : N0 ^ (r + 1) = 0 := by
    ext x
    have := hN0pow r x
    rw [Nat.sub_self, hXa0, Submodule.mem_bot] at this
    simpa using this
  have hadjpow : ∀ k a b, S.hT ((N0 ^ k) a) b = S.hT a ((N1 ^ k) b) := by
    intro k
    induction k with
    | zero => intro a b; simp
    | succ k ih =>
      intro a b
      rw [pow_succ', Module.End.mul_apply, hN01, ih, pow_succ, Module.End.mul_apply]
  have hN1nil : N1 ^ (r + 1) = 0 := by
    ext y
    refine lift_sep fun w => ?_
    rw [← hadjpow, hN0nil]
    simp

  obtain ⟨S1, hS1⟩ : ∃ S1 : Module.End E S.V, S1 = ∑ k ∈ Finset.range (r + 1), (-N1) ^ k := ⟨_, rfl⟩
  obtain ⟨S0, hS0⟩ : ∃ S0 : Module.End E S.V, S0 = ∑ k ∈ Finset.range (r + 1), (-N0) ^ k := ⟨_, rfl⟩
  have hS1l : (1 + N1) * S1 = 1 := by
    have := mul_neg_geom_sum (-N1) (r + 1)
    rwa [sub_neg_eq_add, neg_pow, hN1nil, mul_zero, sub_zero, ← hS1] at this
  have hS1r : S1 * (1 + N1) = 1 := by
    have := geom_sum_mul_neg (-N1) (r + 1)
    rwa [sub_neg_eq_add, neg_pow, hN1nil, mul_zero, sub_zero, ← hS1] at this
  have hS0l : (1 + N0) * S0 = 1 := by
    have := mul_neg_geom_sum (-N0) (r + 1)
    rwa [sub_neg_eq_add, neg_pow, hN0nil, mul_zero, sub_zero, ← hS0] at this
  have hS0r : S0 * (1 + N0) = 1 := by
    have := geom_sum_mul_neg (-N0) (r + 1)
    rwa [sub_neg_eq_add, neg_pow, hN0nil, mul_zero, sub_zero, ← hS0] at this
  have hnn : ((1 + N0) * S1) * ((1 + N1) * S0) = 1 := by
    rw [mul_assoc, ← mul_assoc S1, hS1r, one_mul, hS0l]
  have hnn' : ((1 + N1) * S0) * ((1 + N0) * S1) = 1 := by
    rw [mul_assoc, ← mul_assoc S0, hS0r, one_mul, hS1l]

  let n : S.V ≃ₗ[E] S.V := LinearEquiv.ofLinearMap ((1 + N0) * S1) ((1 + N1) * S0) hnn hnn'
  have hS1fix : ∀ x, N1 x = 0 → S1 x = x := by
    intro x hx
    rw [hS1, LinearMap.sum_apply, Finset.sum_range_succ', pow_zero, Module.End.one_apply,
      Finset.sum_eq_zero fun k _ => by
        rw [pow_succ, Module.End.mul_apply, LinearMap.neg_apply, hx, neg_zero, map_zero], zero_add]
  have hnfix : ∀ x, N1 x = 0 → n x = x + N0 x := by
    intro x hx
    show ((1 + N0) * S1) x = x + N0 x
    rw [Module.End.mul_apply, hS1fix x hx, LinearMap.add_apply, Module.End.one_apply]
  have hiso : n ∈ Formalism.HermitianLatticesTheory.isom S.hT := by
    intro x y
    have hx : x = (1 + N1) (S1 x) := by rw [← Module.End.mul_apply, hS1l, Module.End.one_apply]
    have hy : y = (1 + N1) (S1 y) := by rw [← Module.End.mul_apply, hS1l, Module.End.one_apply]
    show S.hT (((1 + N0) * S1) x) (((1 + N0) * S1) y) = S.hT x y
    rw [Module.End.mul_apply, Module.End.mul_apply]
    conv_rhs => rw [hx, hy]
    generalize S1 x = s
    generalize S1 y = t
    simp only [LinearMap.add_apply, Module.End.one_apply, map_add]
    rw [hN0iso s t, hN01 s t, hN10 s t, ← hN01 (N1 s) t, hN0N1]
    simp only [map_zero, LinearMap.zero_apply, add_zero]
    ring

  have lint_pow : ∀ B : Module.End E S.V, LInt Λ B → ∀ k, LInt Λ (B ^ k) := by
    intro B hB k
    induction k with
    | zero => intro l hl; simpa using hl
    | succ k ih =>
      intro l hl
      rw [pow_succ', Module.End.mul_apply]
      exact hB _ (ih l hl)
  have lint_neg : ∀ B : Module.End E S.V, LInt Λ B → LInt Λ (-B) := fun B hB l hl => by
    rw [LinearMap.neg_apply]
    exact Submodule.neg_mem _ (hB l hl)
  have lint_sum : ∀ (f : ℕ → Module.End E S.V) (s : Finset ℕ), (∀ k ∈ s, LInt Λ (f k)) →
      LInt Λ (∑ k ∈ s, f k) := fun f s hf l hl => by
    rw [LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun k hk => hf k hk l hl
  have lint_one_add : ∀ B : Module.End E S.V, LInt Λ B → LInt Λ (1 + B) := fun B hB l hl => by
    rw [LinearMap.add_apply, Module.End.one_apply]
    exact Submodule.add_mem _ hl (hB l hl)
  have lint_mul : ∀ B C : Module.End E S.V, LInt Λ B → LInt Λ C → LInt Λ (B * C) :=
    fun B C hB hC l hl => by
      rw [Module.End.mul_apply]
      exact hB _ (hC l hl)
  have hnint : LInt Λ ((1 + N0) * S1) := lint_mul _ _ (lint_one_add _ hN0int)
    (hS1 ▸ lint_sum _ _ fun k _ => lint_pow _ (lint_neg _ hN1int) k)
  have hninvint : LInt Λ ((1 + N1) * S0) := lint_mul _ _ (lint_one_add _ hN1int)
    (hS0 ▸ lint_sum _ _ fun k _ => lint_pow _ (lint_neg _ hN0int) k)
  have hgmap : Formalism.HermitianLatticesTheory.gmap n Λ = Λ := by
    apply le_antisymm
    · rintro _ ⟨l, hl, rfl⟩
      exact hnint l hl
    · intro l hl
      refine ⟨((1 + N1) * S0) l, hninvint l hl, ?_⟩
      show ((1 + N0) * S1) (((1 + N1) * S0) l) = l
      rw [← Module.End.mul_apply, hnn, Module.End.one_apply]
  refine ⟨n, ⟨⟨hiso, hgmap⟩, ?_, ?_⟩, fun a => ?_⟩
  · intro j x hx
    have hxX : x ∈ Xsp F := hXa_le _ hx
    rw [hnfix x (hN1X x hxX), add_sub_cancel_left, hN0onX x hxX]
    simpa using hU0X (j + 1) x hx
  · intro x hx
    rw [hnfix x (hN1orth x hx), add_sub_cancel_left]
    exact hN0X x
  · have hx : F.fl.e a ∈ Xsp F := Submodule.subset_span ⟨a, rfl⟩
    rw [hnfix _ (hN1X _ hx), hN0onX _ hx, hU0]
    abel

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `T Λ F F' hfix _ hconv' he _`. Take `⟨hlat, huni, -, hconv⟩` from `hfix`. Conclude with `lift_gen hA hI hF D.sp.cm.cmUnram Λ (gS D) F F' hlat huni hconv hconv' he`.
-/
theorem lift_of_steps (hA : IntegralAdjointUnimodular) (hI : IsotropicIntegralRetraction) (hF : UnitriangularFrameIntegral) (D : D7) : UnitriangularFrameLift D := by
  intro T Λ F F' hfix _ hconv' he _
  obtain ⟨hlat, huni, -, hconv⟩ := hfix
  exact lift_gen hA hI hF D.sp.cm.cmUnram Λ (gS D) F F' hlat huni hconv hconv' he

/- English proof (translation)
Conclude with `lift_of_steps l_adj (l_iso l_adj l_retr l_theta) l_frame D`.
-/
theorem id_lift (D : D7) : UnitriangularFrameLift D := by
  exact lift_of_steps l_adj (l_iso l_adj l_retr l_theta) l_frame D

end Formalism.MainNotions.BridgeLemma

end
