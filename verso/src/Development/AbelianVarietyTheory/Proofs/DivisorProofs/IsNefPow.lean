import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightDualAndLinearComb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionLowerHeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemipositiveNonnegCombination
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPowIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefPow

/- English proof (translation)
Establish `hex (L : HermLB p) : ∃ h, L.IsArithHeight h` using `(HE k X p D hX).1 L`. Set `ht (L : HermLB p) : ℝ` to `(hex L).choose x`. Establish `hht {L : HermLB p} {h : X → ℝ} (H : L.IsArithHeight h) : ht L = h x` using `congrFun ((hex L).choose_spec.unique hX H) x`. Establish `hiso {L M : HermLB p} (e : L.Isometric M) : ht L = ht M` using `(hht (e.isArithHeight hX (hex L).choose_spec)).symm`. Establish `hadd (L M : HermLB p) : ht (L.tens M) = ht L + ht M` using `PtHtComb.height_tens hX (hex L).choose_spec (hex M).choose_spec (hex _).choose_spec hx`.

Set `F₀ : HermLB.IsomClass p → ℝ` to `Quotient.lift (s := HermLB.isometrySetoid p) ht fun L M e => hiso e`. Set `F : HermLB.IsomClass p →+ ℝ` to `AddMonoidHom.mk' F₀ (by`. Introduce and unpack `⟨L⟩ ⟨M⟩`. Conclude with `hadd L M)`. Establish `hF (L : HermLB p) : F L.icls = ht L` using `rfl`.

Rewrite using `[← hht H', ← hht H, ← hF, ← hF, HermLB.icls_pow, map_nsmul, nsmul_eq_mul]`.
-/
theorem height_pow (HE : GlobalTheory.Published.ArExists) {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} {D : ℕ} (hX : IsArithVar p D) {x : X} (hx : IsAlgPt x) (L : HermLB p) (n : ℕ)
    {h h' : X → ℝ} (H : L.IsArithHeight h) (H' : (L.pow n).IsArithHeight h') : h' x = n * h x := by
  have hex (L : HermLB p) : ∃ h, L.IsArithHeight h := (HE k X p D hX).1 L
  let ht (L : HermLB p) : ℝ := (hex L).choose x
  have hht {L : HermLB p} {h : X → ℝ} (H : L.IsArithHeight h) : ht L = h x :=
    congrFun ((hex L).choose_spec.unique hX H) x
  have hiso {L M : HermLB p} (e : L.Isometric M) : ht L = ht M :=
    (hht (e.isArithHeight hX (hex L).choose_spec)).symm
  have hadd (L M : HermLB p) : ht (L.tens M) = ht L + ht M :=
    PtHtComb.height_tens hX (hex L).choose_spec (hex M).choose_spec (hex _).choose_spec hx
  let F₀ : HermLB.IsomClass p → ℝ := Quotient.lift (s := HermLB.isometrySetoid p) ht fun L M e => hiso e
  let F : HermLB.IsomClass p →+ ℝ := AddMonoidHom.mk' F₀ (by
    rintro ⟨L⟩ ⟨M⟩
    exact hadd L M)
  have hF (L : HermLB p) : F L.icls = ht L := rfl
  rw [← hht H', ← hht H, ← hF, ← hF, HermLB.icls_pow, map_nsmul, nsmul_eq_mul]

/- English proof (translation)
Introduce `HC k _ X _ p D hX M n N`. Establish `HE` using `HC.arExists`. Establish `hex (L : HermLB p) : ∃ h, L.IsArithHeight h` using `(HE k X p D hX).1 L`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Take `⟨h₀, H₀⟩` from `hex (HermLB.triv p)`.

Establish `H : (M.pow 0).IsArithHeight h₀` using `M.isometric_pow_zero.symm.isArithHeight hX H₀`. Establish `T` using `(H₀.isNef_iff hX).1 (HermLB.isNef_triv p D)`. Conclude with `(H.isNef_iff hX).2 ⟨N.semiPos.pow 0, T.2⟩`. Establish `: Module.Finite ℤ k` using `hX.finite`. Use `⟨N.semiPos.pow n, (nefFib_pow_iff k X p hX.isProjOver M n hn).2 N.vertical, fun Z i _ _ _ hc hd => ?_⟩` and prove the remaining obligations.

Take `⟨h, H⟩` from `hex M`. Take `⟨h', H'⟩` from `hex (M.pow n)`. Take `⟨r, hr⟩` from `exists_isRatSec ((M.pow n).restr i).isLB`. Take `⟨r₀, hr₀, h0⟩` from `N.horizontal Z i hc hd`. Use `⟨r, hr, ?_⟩` and prove the remaining obligations.

Rewrite using `[← H'.point Z i hc hd r hr, height_pow HE hX (HtSelfInter.isAlgPt_genericPoint i hc hd) M n H H', H.point Z i hc hd r₀ hr₀]`. Conclude with `mul_nonneg (Nat.cast_nonneg _) h0`.
-/
theorem isNef_pow : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (M : HermLB p) (n : ℕ), M.IsNef D → (M.pow n).IsNef D := by
  intro HC k _ X _ p D hX M n N
  have HE := HC.arExists
  have hex (L : HermLB p) : ∃ h, L.IsArithHeight h := (HE k X p D hX).1 L
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨h₀, H₀⟩ := hex (HermLB.triv p)
    have H : (M.pow 0).IsArithHeight h₀ := M.isometric_pow_zero.symm.isArithHeight hX H₀
    have T := (H₀.isNef_iff hX).1 (HermLB.isNef_triv p D)
    exact (H.isNef_iff hX).2 ⟨N.semiPos.pow 0, T.2⟩
  · have : Module.Finite ℤ k := hX.finite
    refine ⟨N.semiPos.pow n, (nefFib_pow_iff k X p hX.isProjOver M n hn).2 N.vertical,
      fun Z i _ _ _ hc hd => ?_⟩
    obtain ⟨h, H⟩ := hex M
    obtain ⟨h', H'⟩ := hex (M.pow n)
    obtain ⟨r, hr⟩ := exists_isRatSec ((M.pow n).restr i).isLB
    obtain ⟨r₀, hr₀, h0⟩ := N.horizontal Z i hc hd
    refine ⟨r, hr, ?_⟩
    rw [← H'.point Z i hc hd r hr, height_pow HE hX (HtSelfInter.isAlgPt_genericPoint i hc hd) M n H H',
      H.point Z i hc hd r₀ hr₀]
    exact mul_nonneg (Nat.cast_nonneg _) h0

/- English proof (translation)
The claim follows from `isNef_pow`.
-/
example : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (M : HermLB p) (n : ℕ), M.IsNef D → (M.pow n).IsNef D := isNef_pow

end GlobalTheory.NefPow
