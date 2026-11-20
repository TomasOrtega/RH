import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSemilocLengthSum
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSemilocResidueDeg
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreDivSupp
import GroundTheory.HeightsAndTheta.Heights.Intersections.StFibreOverFinite
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsLocRingDimOne
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFiniteAlgebraLengthSum
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

/- English proof (translation)
Introduce `K _ ι _ K' _ ι' _ κ v P' n s t α W E hv hP' y hPn hs ht hsP hW htW hy hE`. Use `hP'.2.1.1` as an intermediate fact. Use `imageZ_isPrime_of_prime v P'` as an intermediate fact. Set `_` to `(locToSemiloc hv P' W).toAlgebra`. Establish `hfin` using `h₆ K ι K' ι' κ v P' n s α W hv hP' hPn hs hsP hW`.

Take `⟨hmax, hinj, hcov⟩` from `h₂ K ι K' ι' κ v P' n s α W hv hP' hPn hs hsP hW`. Establish `: IsLocalRing (locRing (imageZ v P') W)` using `(h₅ K ι (imageZ v P') s α W hPn.2.1 hs hsP hW).2.1`. Establish `: Module.Finite (locRing (imageZ v P') W) (semiLocRing P' (fibreOver v P' W))` using `(h₁ K ι K' ι' κ v P' n s α W hv hP' hPn hs hsP hW).1`. Set `_ : Fintype (fibreOver v P' W)` to `hfin.fintype`. Establish `hloc : ∀ W' : fibreOver v P' W, IsLocalRing (locRing P' W'.1)` using `fun W' => haveI := W'.2.1.1`.

Use the proof step `regularityLocalFlat_holds.isLocalRing W'.2.2.1`. Set `_ : ∀ W' : fibreOver v P' W, Algebra (semiLocRing P' (fibreOver v P' W)) (locRing P' W'.1)` to `fun W' => (semiToLoc P' _ W'.1 W'.2).toAlgebra`. Establish `key` using `FieldNumbers.FiniteAlgebraLengthSum.proof.{0} (locRing (imageZ v P') W) (semiLocRing P' (fibreOver v P' W)) (fibreOver v P' W) (fun W' => semiMaxIdeal P' _ W'.1 W'.2) (fun W' => (hmax W'.1 W'.2).1) (fun W₁ W₂ h => Subtype.ext (hinj W₁.1 W₂.1 W₁.2 W₂.2 h)) (fun M hM => by obtain ⟨ …`. Use `⟨hfin, ?_⟩` and prove the remaining obligations. Establish `hyne : (y : FractionRing (MRing ι ⧸ imageZ v P')) ≠ 0`.

Introduce `h0`. Rewrite `hy` using `[h0, zero_mul, eq_comm, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hsP hy`. Establish `hs' : rename v s ∉ P'` using `hsP`. Establish `hterm : ∀ W' : fibreOver v P' W, Ring.ord (locRing P' W'.1) (algebraMap (semiLocRing P' (fibreOver v P' W)) (locRing P' W'.1) (algebraMap (locRing (imageZ v P') W) _ y)) * Module.length (locRing (imageZ v P') W) (semiLocRing P' (fibreOver v P' W) ⧸ semiMaxIdeal P' _ W'.1 W'.2) ≠ …`.

Introduce `W'`. Take `⟨hW'p, hPW', hW'i⟩` from `W'.2`. Use `hW'p.1` as an intermediate fact. Use `set x := algebraMap (semiLocRing P' (fibreOver v P' W)) (locRing P' W'.1) (algebraMap (locRing (imageZ v P') W) _ y) with hxdef`. Establish `hx : (x : FractionRing (MRing ι' ⧸ P')) = fracMapZ v P' y`.

Rewrite using `[hxdef, RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, semiToLoc_coe, locToSemiloc_coe]`. Establish `hord : Ring.ord (locRing P' W'.1) x = Module.length (locRing P' W'.1) (locRing P' W'.1 ⧸ locIdeal P' W'.1 (fracMapZ v P' y))`. Establish `hI : locIdeal P' W'.1 (fracMapZ v P' y) = Ideal.span {x}`. Rewrite using `[locIdeal, ← hx]`. Use `congr 1`.

Use extensionality with `z`. Simplify using `only [Set.mem_singleton_iff, Set.mem_ofPred_eq]`. Conclude with `Subtype.ext_iff.symm`. Rewrite using `[Ring.ord, hI]`. Use `split_ifs with hsW'`.

Take `⟨G', J', hJ', hEW'⟩` from `hE W'.1 W'.2 hsW'`. Take `⟨d, hd, hdE⟩` from `h₃ K ι K' ι' κ v P' n s α W hv hP' hPn hs hsP hW W'.1 W'.2 G' J' hJ'`. Establish `hdiv : W'.1 ∈ divSupp P' (rename v s)` using `((h₄ K ι K' ι' κ v P' n s α W hv hP' hPn hs hsP hW W'.1).1 ⟨W'.2, hsW'⟩).1`. Take `⟨hN, -, hdim⟩` from `h₅ K' ι' P' (rename v s) (Function.extend κ α 0) W'.1 hP'.2.1 (rename_isMultiHomog hv hs) hs' hdiv`. Establish `: Ring.KrullDimLE 1 (locRing P' W'.1)`.

Rewrite using `[Ring.krullDimLE_iff, hdim]`. Both sides reduce to the same expression. Establish `hx0 : x ≠ 0` using `fun h => (map_ne_zero (fracMapZ v P')).mpr hyne (by rw [← hx, h, ZeroMemClass.coe_zero])`. Establish `hfinord` using `Ring.ord_ne_top (R := locRing P' W'.1) (mem_nonZeroDivisors_of_ne_zero hx0)`. Rewrite using `[hd, ← hord]`.

Use `⟨WithTop.mul_ne_top hfinord (ENat.natCast_ne_top d), ?_⟩` and prove the remaining obligations. Rewrite using `[ENat.toNat_mul, ENat.toNat_natCast, Nat.cast_mul, hdE, hEW']`. Establish `ht' : rename v t ∉ W'.1` using `fun h => htW (hW'i ▸ h)`. Establish `hxe : (x : FractionRing (MRing ι' ⧸ P')) * regularityLocalFlat_holds.fracHom P' (rename v t) = regularityLocalFlat_holds.fracHom P' (rename v s)`. Rewrite using `[hx, regularityLocalFlat_holds.fracHom_apply, regularityLocalFlat_holds.fracHom_apply, ← fracMapZ_algebraMap, ← fracMapZ_algebraMap, ← map_mul, hy]`.

Establish `hu : IsUnit x` using `(regularityLocalFlat_holds.isUnit_iff hPW' x (rename_isMultiHomog hv hs) (rename_isMultiHomog hv ht) ht' hxe).mpr hsW'`. Rewrite using `[Ring.ord_of_isUnit hu, zero_mul]`. Simplify using the standard rewrite rules. Establish `hset : {W' | W' ∈ fibreOver v P' W ∧ rename v s ∈ W'} = ↑(hfin.toFinset.filter (fun W' => rename v s ∈ W'))`. Use `ext`.

Simplify using the standard rewrite rules. Establish `hsum` using `ENat.sum_ne_top.mpr fun W' (_ : W' ∈ Finset.univ) => (hterm W').1`. Rewrite using `[key]`. Use `⟨_, (ENat.natCast_toNat hsum).symm, ?_⟩` and prove the remaining obligations. Rewrite using `[ENat.toNat_sum fun W' _ => (hterm W').1, Nat.cast_sum, hset, finsum_mem_coe_finset, Finset.sum_filter, Finset.sum_subtype (F := hfin.fintype) hfin.toFinset (fun _ => Set.Finite.mem_toFinset hfin)]`.

Conclude with `Finset.sum_congr rfl fun W' _ => (hterm W').2`.
-/
theorem SemilocLengthSum.proof (h₁ : SemilocFinite.Statement) (h₂ : SemilocMaxIdeals.Statement)
    (h₃ : SemilocResidueDeg.Statement) (h₄ : FibreDivSupp.Statement) (h₅ : LocRingDimOne.Statement)
    (h₆ : FibreOverFinite.Statement) :
    SemilocLengthSum.Statement := by
  classical
  intro K _ ι _ K' _ ι' _ κ v P' n s t α W E hv hP' y hPn hs ht hsP hW htW hy hE
  have := hP'.2.1.1
  have := imageZ_isPrime_of_prime v P'
  let _ := (locToSemiloc hv P' W).toAlgebra
  have hfin := h₆ K ι K' ι' κ v P' n s α W hv hP' hPn hs hsP hW
  obtain ⟨hmax, hinj, hcov⟩ := h₂ K ι K' ι' κ v P' n s α W hv hP' hPn hs hsP hW
  have : IsLocalRing (locRing (imageZ v P') W) := (h₅ K ι (imageZ v P') s α W hPn.2.1 hs hsP hW).2.1
  have : Module.Finite (locRing (imageZ v P') W) (semiLocRing P' (fibreOver v P' W)) :=
    (h₁ K ι K' ι' κ v P' n s α W hv hP' hPn hs hsP hW).1
  let _ : Fintype (fibreOver v P' W) := hfin.fintype
  have hloc : ∀ W' : fibreOver v P' W, IsLocalRing (locRing P' W'.1) := fun W' =>
    haveI := W'.2.1.1; regularityLocalFlat_holds.isLocalRing W'.2.2.1
  let _ : ∀ W' : fibreOver v P' W, Algebra (semiLocRing P' (fibreOver v P' W)) (locRing P' W'.1) :=
    fun W' => (semiToLoc P' _ W'.1 W'.2).toAlgebra
  have key := FieldNumbers.FiniteAlgebraLengthSum.proof.{0} (locRing (imageZ v P') W) (semiLocRing P' (fibreOver v P' W))
    (fibreOver v P' W) (fun W' => semiMaxIdeal P' _ W'.1 W'.2) (fun W' => (hmax W'.1 W'.2).1)
    (fun W₁ W₂ h => Subtype.ext (hinj W₁.1 W₂.1 W₁.2 W₂.2 h))
    (fun M hM => by obtain ⟨W', hW', h⟩ := hcov M hM; exact ⟨⟨W', hW'⟩, @h (hloc ⟨W', hW'⟩)⟩)
    (fun W' => locRing P' W'.1) (fun W' => (hmax W'.1 W'.2).2) y

  refine ⟨hfin, ?_⟩
  have hyne : (y : FractionRing (MRing ι ⧸ imageZ v P')) ≠ 0 := by
    intro h0
    rw [h0, zero_mul, eq_comm, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at hy
    exact hsP hy
  have hs' : rename v s ∉ P' := hsP
  have hterm : ∀ W' : fibreOver v P' W,
      Ring.ord (locRing P' W'.1) (algebraMap (semiLocRing P' (fibreOver v P' W)) (locRing P' W'.1)
          (algebraMap (locRing (imageZ v P') W) _ y)) *
        Module.length (locRing (imageZ v P') W)
          (semiLocRing P' (fibreOver v P' W) ⧸ semiMaxIdeal P' _ W'.1 W'.2) ≠ ⊤ ∧
      (((Ring.ord (locRing P' W'.1) (algebraMap (semiLocRing P' (fibreOver v P' W)) (locRing P' W'.1)
          (algebraMap (locRing (imageZ v P') W) _ y)) *
        Module.length (locRing (imageZ v P') W)
          (semiLocRing P' (fibreOver v P' W) ⧸ semiMaxIdeal P' _ W'.1 W'.2)).toNat : ℕ) : ℤ) =
        if rename v s ∈ W'.1 then
          ((Module.length (locRing P' W'.1) (locRing P' W'.1 ⧸ locIdeal P' W'.1 (fracMapZ v P' y))).toNat : ℤ) *
            E W'.1 else 0 := by
    intro W'
    obtain ⟨hW'p, hPW', hW'i⟩ := W'.2
    have := hW'p.1
    set x := algebraMap (semiLocRing P' (fibreOver v P' W)) (locRing P' W'.1)
      (algebraMap (locRing (imageZ v P') W) _ y) with hxdef
    have hx : (x : FractionRing (MRing ι' ⧸ P')) = fracMapZ v P' y := by
      rw [hxdef, RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, semiToLoc_coe, locToSemiloc_coe]
    have hord : Ring.ord (locRing P' W'.1) x =
        Module.length (locRing P' W'.1) (locRing P' W'.1 ⧸ locIdeal P' W'.1 (fracMapZ v P' y)) := by
      have hI : locIdeal P' W'.1 (fracMapZ v P' y) = Ideal.span {x} := by
        rw [locIdeal, ← hx]
        congr 1
        ext z
        simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq]
        exact Subtype.ext_iff.symm
      rw [Ring.ord, hI]
    split_ifs with hsW'
    · obtain ⟨G', J', hJ', hEW'⟩ := hE W'.1 W'.2 hsW'
      obtain ⟨d, hd, hdE⟩ := h₃ K ι K' ι' κ v P' n s α W hv hP' hPn hs hsP hW W'.1 W'.2 G' J' hJ'
      have hdiv : W'.1 ∈ divSupp P' (rename v s) :=
        ((h₄ K ι K' ι' κ v P' n s α W hv hP' hPn hs hsP hW W'.1).1 ⟨W'.2, hsW'⟩).1
      obtain ⟨hN, -, hdim⟩ := h₅ K' ι' P' (rename v s) (Function.extend κ α 0) W'.1 hP'.2.1
        (rename_isMultiHomog hv hs) hs' hdiv
      have : Ring.KrullDimLE 1 (locRing P' W'.1) := by
        rw [Ring.krullDimLE_iff, hdim]
        rfl
      have hx0 : x ≠ 0 := fun h =>
        (map_ne_zero (fracMapZ v P')).mpr hyne (by rw [← hx, h, ZeroMemClass.coe_zero])
      have hfinord := Ring.ord_ne_top (R := locRing P' W'.1) (mem_nonZeroDivisors_of_ne_zero hx0)
      rw [hd, ← hord]
      refine ⟨WithTop.mul_ne_top hfinord (ENat.natCast_ne_top d), ?_⟩
      rw [ENat.toNat_mul, ENat.toNat_natCast, Nat.cast_mul, hdE, hEW']
    · have ht' : rename v t ∉ W'.1 := fun h => htW (hW'i ▸ h)
      have hxe : (x : FractionRing (MRing ι' ⧸ P')) * regularityLocalFlat_holds.fracHom P' (rename v t) =
          regularityLocalFlat_holds.fracHom P' (rename v s) := by
        rw [hx, regularityLocalFlat_holds.fracHom_apply, regularityLocalFlat_holds.fracHom_apply, ← fracMapZ_algebraMap, ← fracMapZ_algebraMap,
          ← map_mul, hy]
      have hu : IsUnit x := (regularityLocalFlat_holds.isUnit_iff hPW' x (rename_isMultiHomog hv hs) (rename_isMultiHomog hv ht) ht'
        hxe).mpr hsW'
      rw [Ring.ord_of_isUnit hu, zero_mul]
      simp
  have hset : {W' | W' ∈ fibreOver v P' W ∧ rename v s ∈ W'} =
      ↑(hfin.toFinset.filter (fun W' => rename v s ∈ W')) := by
    ext
    simp
  have hsum := ENat.sum_ne_top.mpr fun W' (_ : W' ∈ Finset.univ) => (hterm W').1
  rw [key]
  refine ⟨_, (ENat.natCast_toNat hsum).symm, ?_⟩
  rw [ENat.toNat_sum fun W' _ => (hterm W').1, Nat.cast_sum, hset, finsum_mem_coe_finset, Finset.sum_filter,
    Finset.sum_subtype (F := hfin.fintype) hfin.toFinset (fun _ => Set.Finite.mem_toFinset hfin)]
  exact Finset.sum_congr rfl fun W' _ => (hterm W').2

end GroundTheory.Heights₂.Heights.Inter
