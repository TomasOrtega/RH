import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.LcNatProof

/- English proof (translation)
Establish `key : (((ZMod.castHom (pow_dvd_pow l n.le_succ) (ZMod (l ^ n))) a).val : ZMod (l ^ n)) = (a.val : ZMod (l ^ n))`. Rewrite using `[ZMod.natCast_zmod_val, ← map_natCast (ZMod.castHom (pow_dvd_pow l n.le_succ) (ZMod (l ^ n))), ZMod.natCast_zmod_val]`. Take `⟨c, hc⟩` from `Nat.modEq_iff_dvd.1 ((ZMod.natCast_eq_natCast_iff _ _ _).1 key)`. Establish `e` using `congrArg (Int.cast : ℤ → R) hc`. Move the coercions through the operations in `at e`.

Rewrite `e` using `[h, zero_mul, sub_eq_zero]`. Conclude with `e.symm`.
-/
theorem natCast_val_castHom {R : Type} [CommRing R] (l n : ℕ) [NeZero (l ^ n)] [NeZero (l ^ (n + 1))]
    (h : (l : R) ^ n = 0) (a : ZMod (l ^ (n + 1))) :
    (((ZMod.castHom (pow_dvd_pow l n.le_succ) (ZMod (l ^ n))) a).val : R) = (a.val : R) := by
  have key : (((ZMod.castHom (pow_dvd_pow l n.le_succ) (ZMod (l ^ n))) a).val : ZMod (l ^ n)) =
      (a.val : ZMod (l ^ n)) := by
    rw [ZMod.natCast_zmod_val, ← map_natCast (ZMod.castHom (pow_dvd_pow l n.le_succ) (ZMod (l ^ n))),
      ZMod.natCast_zmod_val]
  obtain ⟨c, hc⟩ := Nat.modEq_iff_dvd.1 ((ZMod.natCast_eq_natCast_iff _ _ _).1 key)
  have e := congrArg (Int.cast : ℤ → R) hc
  push_cast at e
  rw [h, zero_mul, sub_eq_zero] at e
  exact e.symm

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `hO : OrthogonalIdempotents (fun a => (WittVector.teichmuller l (e a) : A.W))` using `{ idem := fun a => by`. Express the relevant statement in the definitionally equal form `WittVector.teichmuller l (e a) * WittVector.teichmuller l (e a) = WittVector.teichmuller l (e a)`. Rewrite using `[← map_mul, (he.idem a).eq]`. Use `ortho := fun i j hij => by`. Express the relevant statement in the definitionally equal form `WittVector.teichmuller l (e i) * WittVector.teichmuller l (e j) = 0`.

Rewrite using `[← map_mul, he.ortho hij, WittVector.teichmuller_zero] }`. Establish `hE : IsIdempotentElem (∑ a, (WittVector.teichmuller l (e a) : A.W))` using `hO.isIdempotentElem_sum`. Establish `hu : IsIdempotentElem (1 - ∑ a, (WittVector.teichmuller l (e a) : A.W))` using `hE.one_sub`. Establish `hc : (1 - ∑ a, (WittVector.teichmuller l (e a) : A.W)).coeff 0 = 0`. Rewrite using `[← WittVector.constantCoeff_apply, map_sub, map_one, map_sum]`.

Simplify using `only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]`. Rewrite using `[he.complete, sub_self]`. Take `⟨c, hc'⟩` from `Ideal.mem_span_singleton'.1 ((A.mem_span_l_iff _).2 hc)`. Establish `ht : IsIdempotentElem (A.toAcr n (1 - ∑ a, (WittVector.teichmuller l (e a) : A.W)))` using `hu.map (A.toAcr n)`. Establish `h0 : A.toAcr n (1 - ∑ a, (WittVector.teichmuller l (e a) : A.W)) = 0`.

Rewrite using `[← ht.pow_succ_eq n, ← hc', map_mul, map_natCast, mul_pow, pow_succ (l : A.Acr n) n, A.pow_l_acr n, zero_mul, mul_zero]`. Rewrite `h0` using `[map_sub, map_one, map_sum, sub_eq_zero]`. Conclude with `h0.symm`.
-/
theorem sum_toAcr_teichmuller (A : PAlg l) {ι : Type} [Fintype ι] {e : ι → A.A}
    (he : CompleteOrthogonalIdempotents e) (n : ℕ) :
    ∑ a, A.toAcr n (WittVector.teichmuller l (e a)) = 1 := by
  have hO : OrthogonalIdempotents (fun a => (WittVector.teichmuller l (e a) : A.W)) :=
    { idem := fun a => by
        change WittVector.teichmuller l (e a) * WittVector.teichmuller l (e a) = WittVector.teichmuller l (e a)
        rw [← map_mul, (he.idem a).eq]
      ortho := fun i j hij => by
        change WittVector.teichmuller l (e i) * WittVector.teichmuller l (e j) = 0
        rw [← map_mul, he.ortho hij, WittVector.teichmuller_zero] }
  have hE : IsIdempotentElem (∑ a, (WittVector.teichmuller l (e a) : A.W)) := hO.isIdempotentElem_sum
  have hu : IsIdempotentElem (1 - ∑ a, (WittVector.teichmuller l (e a) : A.W)) := hE.one_sub
  have hc : (1 - ∑ a, (WittVector.teichmuller l (e a) : A.W)).coeff 0 = 0 := by
    rw [← WittVector.constantCoeff_apply, map_sub, map_one, map_sum]
    simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
    rw [he.complete, sub_self]
  obtain ⟨c, hc'⟩ := Ideal.mem_span_singleton'.1 ((A.mem_span_l_iff _).2 hc)
  have ht : IsIdempotentElem (A.toAcr n (1 - ∑ a, (WittVector.teichmuller l (e a) : A.W))) := hu.map (A.toAcr n)
  have h0 : A.toAcr n (1 - ∑ a, (WittVector.teichmuller l (e a) : A.W)) = 0 := by
    rw [← ht.pow_succ_eq n, ← hc', map_mul, map_natCast, mul_pow, pow_succ (l : A.Acr n) n, A.pow_l_acr n,
      zero_mul, mul_zero]
  rw [map_sub, map_one, map_sum, sub_eq_zero] at h0
  exact h0.symm

/- English proof (translation)
Introduce `hId hSp l _ H A hA n`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `B hB φ h g hg f`. Take `⟨e, he, hcut, -⟩` from `hId l H A hA (ZMod (l ^ n)) f`. Establish `h1` using `(hSp l H A hA n).2.2.2 f e he (fun a p => (hcut a p).1)`.

Establish `hφ : CompleteOrthogonalIdempotents (φ ∘ e)` using `he.map φ`. Establish `h2` using `(hSp l H B hB n).2.2.2 (lcRes _ (Spec.map (CommRingCat.ofHom g)) f) (φ ∘ e) hφ (fun a p hp => by`. Use `(hcut a (PrimeSpectrum.comap g p)).1 fun hm => hp ?_` and prove the remaining obligations. Use `hg (e a) (he.idem a)` as an intermediate fact. Express the relevant statement in the definitionally equal form `algebraMap B.U B.Ug (B.sharp (φ (e a))) ∈ p.asIdeal`.

Rewrite using `[← this]`. Conclude with `hm)`. Rewrite using `[h1, h2, map_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, PAlg.PdOk.acr_toAcr, WittVector.map_teichmuller, map_natCast]`.

Both sides reduce to the same expression. Introduce `f`. Take `⟨e, he, hcut, -⟩` from `hId l H A hA (ZMod (l ^ (n + 1))) f`. Establish `h1` using `(hSp l H A hA (n + 1)).2.2.2 f e he (fun a p => (hcut a p).1)`. Use `set c := ZMod.castHom (pow_dvd_pow l n.le_succ) (ZMod (l ^ n)) with hcdef`.

Establish `hL` using `(hSp l H A hA n).1 (f.map c)`. Establish `hT : ∀ a, A.toAcr n (WittVector.teichmuller l (e a)) * lcA A n (f.map c) = A.toAcr n (WittVector.teichmuller l (e a)) * (a.val : A.Acr n)` using `fun a => by`. Rewrite using `[hL (e a) (c a) (he.idem a) (fun p hp => by`. Express the relevant statement in the definitionally equal form `c (f p) = c a`. Rewrite using `[(hcut a p).1 hp]), natCast_val_castHom l n (A.pow_l_acr n) a]`.

Rewrite using `[h1, map_sum, ← one_mul (lcA A n (f.map c)), ← sum_toAcr_teichmuller A he n, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[hT a, map_mul, map_natCast]`. Both sides reduce to the same expression.
-/
theorem lcNat : LcIdem → LcSpec → LcNat := by
  intro hId hSp l _ H A hA n
  refine ⟨?_, ?_⟩
  · intro B hB φ h g hg f
    obtain ⟨e, he, hcut, -⟩ := hId l H A hA (ZMod (l ^ n)) f
    have h1 := (hSp l H A hA n).2.2.2 f e he (fun a p => (hcut a p).1)
    have hφ : CompleteOrthogonalIdempotents (φ ∘ e) := he.map φ
    have h2 := (hSp l H B hB n).2.2.2 (lcRes _ (Spec.map (CommRingCat.ofHom g)) f) (φ ∘ e) hφ (fun a p hp => by
      refine (hcut a (PrimeSpectrum.comap g p)).1 fun hm => hp ?_
      have := hg (e a) (he.idem a)
      change algebraMap B.U B.Ug (B.sharp (φ (e a))) ∈ p.asIdeal
      rw [← this]
      exact hm)
    rw [h1, h2, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, PAlg.PdOk.acr_toAcr, WittVector.map_teichmuller, map_natCast]
    rfl
  · intro f
    obtain ⟨e, he, hcut, -⟩ := hId l H A hA (ZMod (l ^ (n + 1))) f
    have h1 := (hSp l H A hA (n + 1)).2.2.2 f e he (fun a p => (hcut a p).1)
    set c := ZMod.castHom (pow_dvd_pow l n.le_succ) (ZMod (l ^ n)) with hcdef
    have hL := (hSp l H A hA n).1 (f.map c)
    have hT : ∀ a, A.toAcr n (WittVector.teichmuller l (e a)) * lcA A n (f.map c) =
        A.toAcr n (WittVector.teichmuller l (e a)) * (a.val : A.Acr n) := fun a => by
      rw [hL (e a) (c a) (he.idem a) (fun p hp => by
        change c (f p) = c a
        rw [(hcut a p).1 hp]), natCast_val_castHom l n (A.pow_l_acr n) a]
    rw [h1, map_sum, ← one_mul (lcA A n (f.map c)), ← sum_toAcr_teichmuller A he n, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hT a, map_mul, map_natCast]
    rfl

end GlobalTheory.CompanionTheory.LcNatProof
