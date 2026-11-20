import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgEqOfLeRightStabiliserStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.AvgProd

/- English proof (translation)
Take `⟨k, hk⟩` from `QuotientGroup.mk_out_eq_mul (rStab u) x`. Rewrite using `[hk]`. Establish `hk' : ∀ y, u (y * (k : H)) = u y` using `k.2`. Conclude with `hk' x`.
-/
lemma apply_out_rStab {H : Type} [Group H] (u : H → ℂ) (x : H) :
    u ((x : H ⧸ rStab u).out) = u x := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (rStab u) x
  rw [hk]
  have hk' : ∀ y, u (y * (k : H)) = u y := k.2
  exact hk' x

/- English proof (translation)
Introduce `H H' _ _ u v hu hv`. Use `set S : Subgroup (H × H') := (rStab u).prod (rStab v) with hS`. Establish `hle : S ≤ rStab (fun x : H × H' => u x.1 * v x.2)`. Introduce `p hp`. Rewrite `hp` using `[hS, Subgroup.mem_prod]`.

Establish `ha : ∀ y, u (y * p.1) = u y` using `hp.1`. Establish `hb : ∀ y, v (y * p.2) = v y` using `hp.2`. Introduce `x`. Simplify using `only [Prod.fst_mul, Prod.snd_mul]`. Rewrite using `[ha x.1, hb x.2]`.

Establish `hSi : S.index = (rStab u).index * (rStab v).index` using `Subgroup.index_prod _ _`. Establish `hS0 : S.index ≠ 0` using `by rw [hSi]; exact mul_ne_zero hu hv`. Rewrite using `[GlobalTheory.T.avg_eq_of_le_rightStabiliser _ _ S hle hS0]`. Use `haveI : (rStab u).FiniteIndex := ⟨hu⟩`. Use `haveI : (rStab v).FiniteIndex := ⟨hv⟩`.

Use `haveI : S.FiniteIndex := ⟨hS0⟩`. Use `letI : Fintype (H ⧸ rStab u) := Fintype.ofFinite _`. Use `letI : Fintype (H' ⧸ rStab v) := Fintype.ofFinite _`. Use `letI : Fintype ((H × H') ⧸ S) := Fintype.ofFinite _`. Set `f : (H × H') ⧸ S → (H ⧸ rStab u) × (H' ⧸ rStab v)` to `fun q => ((q.out.1 : H ⧸ rStab u), (q.out.2 : H' ⧸ rStab v))`.

Establish `hf : Function.Bijective f`. Prove the components needed by the constructor for the conclusion. Introduce `q q' h`. Simplify using `only [f, Prod.mk.injEq] at h`. Take `⟨h1, h2⟩` from `h`.

Rewrite `h1`, `h2` using `[QuotientGroup.eq]`. Rewrite using `[← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq]`. Conclude with `(Subgroup.mem_prod (H := rStab u) (K := rStab v)).2 ⟨by simpa using h1, by simpa using h2⟩`. Introduce and unpack `⟨a, b⟩`. Proceed by induction on `a using QuotientGroup.induction_on with | H x => ?_`.

Proceed by induction on `b using QuotientGroup.induction_on with | H y => ?_`. Use `⟨((x, y) : (H × H') ⧸ S), ?_⟩` and prove the remaining obligations. Establish `h` using `QuotientGroup.out_eq' ((x, y) : (H × H') ⧸ S)`. Rewrite `h` using `[QuotientGroup.eq]`. Use `replace h := (Subgroup.mem_prod (H := rStab u) (K := rStab v)).1 h`.

Simplify using `only [f, Prod.mk.injEq]`. Rewrite using `[QuotientGroup.eq, QuotientGroup.eq]`. Conclude with `⟨by simpa using h.1, by simpa using h.2⟩`. Establish `hsum : ∑ᶠ q : (H × H') ⧸ S, (fun x : H × H' => u x.1 * v x.2) q.out = (∑ᶠ a : H ⧸ rStab u, u a.out) * ∑ᶠ b : H' ⧸ rStab v, v b.out`. Rewrite using `[finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.sum_mul_sum, ← Fintype.sum_prod_type']`.

Use `Fintype.sum_bijective f hf _ _ ?_` and prove the remaining obligations. Introduce `q`. Simplify using `only [f, apply_out_rStab]`. Rewrite using `[hsum]`. Unfold `avg`.

Rewrite using `[hSi]`. Use `push_cast`. Rewrite using `[mul_inv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem avg_prod : ∀ (H H' : Type) [Group H] [Group H'] (u : H → ℂ) (v : H' → ℂ), (rStab u).index ≠ 0 →
    (rStab v).index ≠ 0 → avg (fun x : H × H' => u x.1 * v x.2) = avg u * avg v := by
  intro H H' _ _ u v hu hv
  set S : Subgroup (H × H') := (rStab u).prod (rStab v) with hS
  have hle : S ≤ rStab (fun x : H × H' => u x.1 * v x.2) := by
    intro p hp
    rw [hS, Subgroup.mem_prod] at hp
    have ha : ∀ y, u (y * p.1) = u y := hp.1
    have hb : ∀ y, v (y * p.2) = v y := hp.2
    intro x
    simp only [Prod.fst_mul, Prod.snd_mul]
    rw [ha x.1, hb x.2]
  have hSi : S.index = (rStab u).index * (rStab v).index := Subgroup.index_prod _ _
  have hS0 : S.index ≠ 0 := by rw [hSi]; exact mul_ne_zero hu hv
  rw [GlobalTheory.T.avg_eq_of_le_rightStabiliser _ _ S hle hS0]
  haveI : (rStab u).FiniteIndex := ⟨hu⟩
  haveI : (rStab v).FiniteIndex := ⟨hv⟩
  haveI : S.FiniteIndex := ⟨hS0⟩
  letI : Fintype (H ⧸ rStab u) := Fintype.ofFinite _
  letI : Fintype (H' ⧸ rStab v) := Fintype.ofFinite _
  letI : Fintype ((H × H') ⧸ S) := Fintype.ofFinite _
  let f : (H × H') ⧸ S → (H ⧸ rStab u) × (H' ⧸ rStab v) :=
    fun q => ((q.out.1 : H ⧸ rStab u), (q.out.2 : H' ⧸ rStab v))
  have hf : Function.Bijective f := by
    constructor
    · intro q q' h
      simp only [f, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [QuotientGroup.eq] at h1 h2
      rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq]
      exact (Subgroup.mem_prod (H := rStab u) (K := rStab v)).2 ⟨by simpa using h1, by simpa using h2⟩
    · rintro ⟨a, b⟩
      induction a using QuotientGroup.induction_on with | H x => ?_
      induction b using QuotientGroup.induction_on with | H y => ?_
      refine ⟨((x, y) : (H × H') ⧸ S), ?_⟩
      have h := QuotientGroup.out_eq' ((x, y) : (H × H') ⧸ S)
      rw [QuotientGroup.eq] at h
      replace h := (Subgroup.mem_prod (H := rStab u) (K := rStab v)).1 h
      simp only [f, Prod.mk.injEq]
      rw [QuotientGroup.eq, QuotientGroup.eq]
      exact ⟨by simpa using h.1, by simpa using h.2⟩
  have hsum : ∑ᶠ q : (H × H') ⧸ S, (fun x : H × H' => u x.1 * v x.2) q.out =
      (∑ᶠ a : H ⧸ rStab u, u a.out) * ∑ᶠ b : H' ⧸ rStab v, v b.out := by
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.sum_mul_sum,
      ← Fintype.sum_prod_type']
    refine Fintype.sum_bijective f hf _ _ ?_
    intro q
    simp only [f, apply_out_rStab]
  rw [hsum]
  unfold avg
  rw [hSi]
  push_cast
  rw [mul_inv]
  ring

end GlobalTheory.AvgProd
