import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyCompIffAndDegreeMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotDvdDegOfNoTorsionInKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteIffFiniteKerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveIffPtMapSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientOfGaloisStableFiniteSubgroupStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.AV.AbVar

variable {K : Type} [Field K]

def kerLPart (l : ℕ) {A B : AbVar K} (f : A ⟶ B) : Subgroup A.Pt where
  carrier := {x | x ≫ f.hom = 1 ∧ ∃ n : ℕ, x ^ l ^ n = 1}
  one_mem' := ⟨(ptMap f).map_one, 0, by simp⟩
  mul_mem' := by
    rintro x y ⟨hx, n, hn⟩ ⟨hy, m, hm⟩
    refine ⟨?_, n + m, ?_⟩
    · have := (ptMap f).map_mul x y
      simp only [ptMap_apply] at this
      rw [this, hx, hy, _root_.one_mul]
    · rw [mul_pow, pow_add, pow_mul, hn, one_pow, mul_comm (l ^ n), pow_mul, hm, one_pow, _root_.one_mul]
  inv_mem' := by
    rintro x ⟨hx, n, hn⟩
    refine ⟨?_, n, ?_⟩
    · have := (ptMap f).map_inv x
      simp only [ptMap_apply] at this
      rw [this, hx, inv_one]
    · rw [inv_pow, hn, inv_one]

/- English proof (translation)
Introduce `_ hx` and use `hx.1`.
-/
theorem kerLPart_le (l : ℕ) {A B : AbVar K} (f : A ⟶ B) : kerLPart l f ≤ (ptMap f).ker :=
  fun _ hx => hx.1

/- English proof (translation)
Use `set G := kerLPart l f with hG`. Express the relevant statement in the definitionally equal form `Nat.card G = _`. Establish `hker : Finite (ptMap f).ker` using `(GlobalTheory.T.isFinite_iff_finite_ker' K A B f).1 hf.1`. Use `haveI hGfin : Finite G := Finite.of_injective (Subgroup.inclusion (kerLPart_le l f)) (Subgroup.inclusion_injective _)`. Establish `hpG : IsPGroup l G` using `fun g => by`.

Take `⟨n, hn⟩` from `g.2.2`. Conclude with `⟨n, Subtype.ext (by simpa using hn)⟩`. Take `⟨k, hk⟩` from `(IsPGroup.iff_card.mp hpG)`. Establish `hcardK : ((Nat.card G : ℕ) : K) ≠ 0`. Rewrite using `[hk, Nat.cast_pow]`.

Conclude with `pow_ne_zero _ hl`. Establish `hgal : ∀ (σ : Gal K) (x : A.Pt), x ∈ G → galPts A.X σ x ∈ G`. Introduce and unpack `σ x ⟨hx, n, hn⟩`. Use `⟨?_, n, ?_⟩` and prove the remaining obligations. Establish `h1 : galPts A.X σ x ≫ f.hom = galPts B.X σ (x ≫ f.hom)` using `Category.assoc _ _ _`.

Rewrite using `[h1, hx, map_one]`. Rewrite using `[← map_pow, hn, map_one]`. Take `⟨B', q, hq, hdq, hkq, huniv⟩` from `GlobalTheory.T.exists_quotient_of_galoisStable_finite_subgroup K A G hGfin hcardK hgal`. Take `⟨h, hqh⟩` from `huniv B f (kerLPart_le l f)`. Establish `hdAB` using `(GlobalTheory.T.dim_eq_flat_finrank_eq_deg_of_isIsogeny K A B f hf).1`.

Establish `hdAB'` using `(GlobalTheory.T.dim_eq_flat_finrank_eq_deg_of_isIsogeny K A B' q hq).1`. Establish `hcomp` using `GlobalTheory.T.isIsogeny_comp_iff_and_degree_mul K A B' B q h hdAB' (hdAB'.symm.trans hdAB)`. Rewrite `hcomp` using `[hqh]`. Establish `hh : IsIsogeny h` using `(hcomp.1.mp hf).2`. Establish `hsurj` using `(GlobalTheory.T.abVar_surjective_iff_ptMap_surjective K A B' q).1 hq.2`.

Establish `hnot : ¬ l ∣ deg h`. Use `GlobalTheory.T.not_dvd_deg_of_no_torsion_in_kernel' K l hl B' B h hh ?_` and prove the remaining obligations. Introduce `y hyl hyh`. Take `⟨x, rfl⟩` from `hsurj y`. Establish `hxf : x ≫ f.hom = 1`.

Rewrite using `[← hqh, comp_hom, ← Category.assoc]`. Conclude with `hyh`. Establish `hxl : x ^ l ∈ G`. Rewrite using `[← hkq, MonoidHom.mem_ker, map_pow, hyl]`. Take `⟨n, hn⟩` from `hxl.2`.

Establish `hx : x ∈ G` using `⟨hxf, n + 1, by rw [pow_succ', pow_mul]; exact hn⟩`. Rewrite `hx` using `[← hkq]`. Conclude with `hx`. Establish `hdh : deg h ≠ 0` using `fun h0 => hnot (h0 ▸ dvd_zero l)`. Rewrite using `[hcomp.2, hdq, hk, padicValNat.mul (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) hdh, padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hnot, add_zero]`.
-/
theorem card_kerLPart_eq (K : Type) [Field K] (l : ℕ) [Fact l.Prime] (hl : (l : K) ≠ 0)
    (A B : AbVar K) (f : A ⟶ B) (hf : IsIsogeny f) :
    Nat.card {x : A.Pt // x ≫ f.hom = 1 ∧ ∃ n : ℕ, x ^ l ^ n = 1} = l ^ padicValNat l (deg f) := by
  set G := kerLPart l f with hG
  change Nat.card G = _
  have hker : Finite (ptMap f).ker := (GlobalTheory.T.isFinite_iff_finite_ker' K A B f).1 hf.1
  haveI hGfin : Finite G := Finite.of_injective (Subgroup.inclusion (kerLPart_le l f))
    (Subgroup.inclusion_injective _)
  have hpG : IsPGroup l G := fun g => by
    obtain ⟨n, hn⟩ := g.2.2
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp hpG)
  have hcardK : ((Nat.card G : ℕ) : K) ≠ 0 := by
    rw [hk, Nat.cast_pow]; exact pow_ne_zero _ hl
  have hgal : ∀ (σ : Gal K) (x : A.Pt), x ∈ G → galPts A.X σ x ∈ G := by
    rintro σ x ⟨hx, n, hn⟩
    refine ⟨?_, n, ?_⟩
    · have h1 : galPts A.X σ x ≫ f.hom = galPts B.X σ (x ≫ f.hom) := Category.assoc _ _ _
      rw [h1, hx, map_one]
    · rw [← map_pow, hn, map_one]
  obtain ⟨B', q, hq, hdq, hkq, huniv⟩ := GlobalTheory.T.exists_quotient_of_galoisStable_finite_subgroup K A G hGfin hcardK hgal
  obtain ⟨h, hqh⟩ := huniv B f (kerLPart_le l f)
  have hdAB := (GlobalTheory.T.dim_eq_flat_finrank_eq_deg_of_isIsogeny K A B f hf).1
  have hdAB' := (GlobalTheory.T.dim_eq_flat_finrank_eq_deg_of_isIsogeny K A B' q hq).1
  have hcomp := GlobalTheory.T.isIsogeny_comp_iff_and_degree_mul K A B' B q h hdAB' (hdAB'.symm.trans hdAB)
  rw [hqh] at hcomp
  have hh : IsIsogeny h := (hcomp.1.mp hf).2
  have hsurj := (GlobalTheory.T.abVar_surjective_iff_ptMap_surjective K A B' q).1 hq.2
  have hnot : ¬ l ∣ deg h := by
    refine GlobalTheory.T.not_dvd_deg_of_no_torsion_in_kernel' K l hl B' B h hh ?_
    intro y hyl hyh
    obtain ⟨x, rfl⟩ := hsurj y
    have hxf : x ≫ f.hom = 1 := by
      rw [← hqh, comp_hom, ← Category.assoc]; exact hyh
    have hxl : x ^ l ∈ G := by
      rw [← hkq, MonoidHom.mem_ker, map_pow, hyl]
    obtain ⟨n, hn⟩ := hxl.2
    have hx : x ∈ G := ⟨hxf, n + 1, by rw [pow_succ', pow_mul]; exact hn⟩
    rw [← hkq] at hx
    exact hx
  have hdh : deg h ≠ 0 := fun h0 => hnot (h0 ▸ dvd_zero l)
  rw [hcomp.2, hdq, hk, padicValNat.mul (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) hdh,
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hnot, add_zero]

end GlobalTheory.AV.AbVar
