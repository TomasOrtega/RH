import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CrysCopy
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.FlatOfDvr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.BcCover
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.IntMap
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ValuationChainProofs.OkDvr
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.NormLtOneOfIrreducible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FKEqResDeg

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.Pst TensorProduct Module Matrix CrystallineSemistableComparison
open GlobalTheory.GalV (HTower)

namespace UpperTheory.Ru.crystallineComparison

open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.Int.Geo UpperTheory.Gal.Seam

/- English proof (translation)
Rewrite using `[OK_eq]`. Both sides reduce to the same expression.
-/
private theorem mem_OK_iff {l : ℕ} [Fact l.Prime] (K : FinExt l) (x : ↥K.1) : x ∈ OK l K.1 ↔ x ∈ OL K := by
  rw [OK_eq]; rfl

private def okEquiv {l : ℕ} [Fact l.Prime] (K : FinExt l) : ↥(OL K) ≃+* ↥(OK l K.1) where
  toFun b := ⟨b.1, (mem_OK_iff K b.1).2 b.2⟩
  invFun c := ⟨c.1, (mem_OK_iff K c.1).1 c.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/- English proof (translation)
Rewrite using `[← GlobalTheory.AinfK.card_res K]`. Conclude with `(Nat.card_congr (IsLocalRing.ResidueField.mapEquiv (okEquiv K)).toEquiv).symm`.
-/
private theorem card_res_OK {l : ℕ} [Fact l.Prime] (K : FinExt l) [IsLocalRing ↥(OK l K.1)] :
    Nat.card (IsLocalRing.ResidueField ↥(OK l K.1)) = l ^ GlobalTheory.AinfK.fK K := by
  rw [← GlobalTheory.AinfK.card_res K]
  exact (Nat.card_congr (IsLocalRing.ResidueField.mapEquiv (okEquiv K)).toEquiv).symm

/- English proof (translation)
Establish `: Finite (IsLocalRing.ResidueField R)` using `Nat.finite_of_card_ne_zero (by rwa [hc])`. Use `letI := Fintype.ofFinite (IsLocalRing.ResidueField R)`. Establish `h` using `FiniteField.pow_card (IsLocalRing.residue R x)`. Rewrite `h` using `[← Nat.card_eq_fintype_card, hc]`. Rewrite using `[← Ideal.mem_span_singleton, ← ht.maximalIdeal_eq, ← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, h, sub_self]`.
-/
private theorem dvd_pow_sub {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {q : ℕ} (hq : q ≠ 0)
    (hc : Nat.card (IsLocalRing.ResidueField R) = q) {t : R} (ht : Irreducible t) (x : R) : t ∣ x ^ q - x := by
  have : Finite (IsLocalRing.ResidueField R) := Nat.finite_of_card_ne_zero (by rwa [hc])
  letI := Fintype.ofFinite (IsLocalRing.ResidueField R)
  have h := FiniteField.pow_card (IsLocalRing.residue R x)
  rw [← Nat.card_eq_fintype_card, hc] at h
  rw [← Ideal.mem_span_singleton, ← ht.maximalIdeal_eq, ← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, h, sub_self]

end UpperTheory.Ru.crystallineComparison

open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.Int.Geo UpperTheory.Gal.Seam UpperTheory.Ru.crystallineComparison

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ l _ L _ H θ w hl n ϑ hC A hA O _ _ _ Bw hB`. Take `⟨C, p, f, hp, hpw, hN, hO, ϖ, T, γ, m, hϖ, hid, hT⟩` from `hC`. Establish `epl : p = l`. Assume the negation of the conclusion as `hne`. Take `⟨a, b, hab⟩` from `Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp Fact.out).2 hne)`.

Establish `h1 : (1 : 𝓞 E) ∈ w.asIdeal`. Establish `h` using `congrArg (Int.cast : ℤ → 𝓞 E) hab`. Move the coercions through the operations in `at h`. Rewrite using `[← h]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpw) (Ideal.mul_mem_left _ _ hl)`.

Conclude with `w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)`. Substitute `epl` using the available equality. Establish `hNv : normV w = p ^ f`. Rewrite using `[← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Both sides reduce to the same expression.

Establish `hf : resDeg p w = f`. Rewrite using `[resDeg, hNv, Nat.log_pow hp.one_lt]`. Substitute `hf` using the available equality. Establish `hpos : 0 < resDeg p w` using `Nat.pos_of_ne_zero fun h0 => w.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 (by rw [hN, h0, pow_zero]))`. Use `haveI := Bw.Kw.2`.

Take `⟨hD, hV, -⟩` from `CrystallineSemistableComparison.Pb.Kap.ok_dvr_pf (l := p) (K := Bw.Kw.1)`. Use `haveI := hD`. Use `haveI := hV`. Use `haveI : IsDiscreteValuationRing (Ow w) := (w.valuation E).valuationSubring_isDiscreteValuationRing`. Take `⟨φ, hφ, hφi⟩` from `UpperTheory.Gal.Seam.intMap E Ω p w A hA O Bw hB`.

Establish `hcard : Nat.card (IsLocalRing.ResidueField ↥(OK p Bw.Kw.1)) = p ^ resDeg p w`. Rewrite using `[card_res_OK, GlobalTheory.AinfK.fK_eq_resDeg Bw hA hB]`. Take `⟨C', u, hu, -, hOnto, -, hLies⟩` from `UpperTheory.Gal.Seam.bcCover E ↥Bw.Kw.1 (Ow w) ↥(OK p Bw.Kw.1) L (UpperTheory.Gal.Seam.kOf Bw) φ hφ H θ C`. Establish `hirr` using `hφi ϖ hϖ`. Take `⟨T', κ, hκ, hid'⟩` from `UpperTheory.Ru.crystallineComparison.ptIdBC p (p ^ resDeg p w) n (Ow w) ↥(OK p Bw.Kw.1) φ ϖ hϖ hirr (dvd_pow_sub (pow_ne_zero _ hp.ne_zero) hcard hirr) C.Y C'.Y C.p C'.p u hu T (fun j => (hT j).1) hid`.

Use `⟨hD, hV, hpos, hNv, hcard, C', hOnto hO, φ ϖ, T', γ, m, hirr, hid', fun j => ⟨(hκ j).2.2, ?_, (hT j).2.2⟩⟩` and prove the remaining obligations. Conclude with `hLies (γ j) (T j).Z (T j).p (T j).r (m j) (hT j).1 (hT j).2.1 (T' j).Z (κ j) (T' j).p (T' j).r (hκ j).1 (hκ j).2.1.symm (hκ j).2.2`.
-/
theorem UpperTheory.Ru.crystallineComparison.congBC :
    UpperTheory.Ru.crystallineComparison.CongBC := by
  intro E Ω _ _ _ _ _ l _ L _ H θ w hl n ϑ hC A hA O _ _ _ Bw hB
  obtain ⟨C, p, f, hp, hpw, hN, hO, ϖ, T, γ, m, hϖ, hid, hT⟩ := hC
  have epl : p = l := by
    by_contra hne
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp Fact.out).2 hne)
    have h1 : (1 : 𝓞 E) ∈ w.asIdeal := by
      have h := congrArg (Int.cast : ℤ → 𝓞 E) hab
      push_cast at h
      rw [← h]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpw) (Ideal.mul_mem_left _ _ hl)
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  subst epl
  have hNv : normV w = p ^ f := by
    rw [← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hf : resDeg p w = f := by
    rw [resDeg, hNv, Nat.log_pow hp.one_lt]
  subst hf
  have hpos : 0 < resDeg p w := Nat.pos_of_ne_zero fun h0 =>
    w.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 (by rw [hN, h0, pow_zero]))
  haveI := Bw.Kw.2
  obtain ⟨hD, hV, -⟩ := CrystallineSemistableComparison.Pb.Kap.ok_dvr_pf (l := p) (K := Bw.Kw.1)
  haveI := hD
  haveI := hV
  haveI : IsDiscreteValuationRing (Ow w) := (w.valuation E).valuationSubring_isDiscreteValuationRing
  obtain ⟨φ, hφ, hφi⟩ := UpperTheory.Gal.Seam.intMap E Ω p w A hA O Bw hB
  have hcard : Nat.card (IsLocalRing.ResidueField ↥(OK p Bw.Kw.1)) = p ^ resDeg p w := by
    rw [card_res_OK, GlobalTheory.AinfK.fK_eq_resDeg Bw hA hB]
  obtain ⟨C', u, hu, -, hOnto, -, hLies⟩ :=
    UpperTheory.Gal.Seam.bcCover E ↥Bw.Kw.1 (Ow w) ↥(OK p Bw.Kw.1) L (UpperTheory.Gal.Seam.kOf Bw) φ hφ H θ C
  have hirr := hφi ϖ hϖ
  obtain ⟨T', κ, hκ, hid'⟩ := UpperTheory.Ru.crystallineComparison.ptIdBC p (p ^ resDeg p w) n (Ow w) ↥(OK p Bw.Kw.1) φ ϖ hϖ hirr
    (dvd_pow_sub (pow_ne_zero _ hp.ne_zero) hcard hirr) C.Y C'.Y C.p C'.p u hu T (fun j => (hT j).1) hid
  refine ⟨hD, hV, hpos, hNv, hcard, C', hOnto hO, φ ϖ, T', γ, m, hirr, hid', fun j => ⟨(hκ j).2.2, ?_, (hT j).2.2⟩⟩
  exact hLies (γ j) (T j).Z (T j).p (T j).r (m j) (hT j).1 (hT j).2.1 (T' j).Z (κ j) (T' j).p (T' j).r (hκ j).1
    (hκ j).2.1.symm (hκ j).2.2
