import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelPlacesNotIsConjPlaceRealDat
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BunExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BSlotD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesNotPairwiseConjugate
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

open scoped Pointwise

namespace GlobalTheory.SeeConjZMod

/- English proof (translation)
Establish `hI : Ideal.span {x} ≠ ⊥` using `by simpa using hx`. Establish `hsq : Squarefree (Ideal.span {x})`. Rewrite using `[squarefree_iff_irreducible_sq_not_dvd_of_ne_zero hI]`. Introduce `p hp hd`. Establish `hpr : Prime p` using `hp.prime`.

Set `P : HeightOneSpectrum A` to `⟨p, Ideal.isPrime_of_prime hpr, hpr.ne_zero⟩`. Establish `h2 : x ∈ p ^ 2`. Rewrite using `[sq, ← Ideal.dvd_span_singleton]`. Conclude with `hd`. Conclude with `(h P (Ideal.pow_le_self two_ne_zero h2)).1 h2`.

Establish `hrad : (Ideal.span {x}).IsRadical`. Introduce `y ⟨n, hn⟩`. Rewrite `hn`, the goal using `[← Ideal.dvd_span_singleton]`. Rewrite `hn` using `[← Ideal.span_singleton_pow]`. Conclude with `hsq.isRadical n _ hn`.

Rewrite using `[← Ideal.mem_span_singleton]`. Apply `hrad` to reduce the goal to its premises. Rewrite using `[Ideal.radical_eq_sInf, Ideal.mem_sInf]`. Introduce and unpack `J ⟨hJ, hp⟩`. Conclude with `(h ⟨J, hp, fun h0 => hI (le_bot_iff.1 (h0 ▸ hJ))⟩ (hJ (Ideal.mem_span_singleton_self x))).2`.
-/
theorem dvd_of_mem_primes {A : Type} [CommRing A] [IsDedekindDomain A] {x b : A} (hx : x ≠ 0)
    (h : ∀ P : HeightOneSpectrum A, x ∈ P.asIdeal → x ∉ P.asIdeal ^ 2 ∧ b ∈ P.asIdeal) : x ∣ b := by
  have hI : Ideal.span {x} ≠ ⊥ := by simpa using hx
  have hsq : Squarefree (Ideal.span {x}) := by
    rw [squarefree_iff_irreducible_sq_not_dvd_of_ne_zero hI]
    intro p hp hd
    have hpr : Prime p := hp.prime
    let P : HeightOneSpectrum A := ⟨p, Ideal.isPrime_of_prime hpr, hpr.ne_zero⟩
    have h2 : x ∈ p ^ 2 := by
      rw [sq, ← Ideal.dvd_span_singleton]; exact hd
    exact (h P (Ideal.pow_le_self two_ne_zero h2)).1 h2
  have hrad : (Ideal.span {x}).IsRadical := by
    intro y ⟨n, hn⟩
    rw [← Ideal.dvd_span_singleton] at hn ⊢
    rw [← Ideal.span_singleton_pow] at hn
    exact hsq.isRadical n _ hn
  rw [← Ideal.mem_span_singleton]
  apply hrad
  rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
  rintro J ⟨hJ, hp⟩
  exact (h ⟨J, hp, fun h0 => hI (le_bot_iff.1 (h0 ▸ hJ))⟩ (hJ (Ideal.mem_span_singleton_self x))).2

/- English proof (translation)
Establish `hle : D.host.conj • P.asIdeal ≤ P'.asIdeal`. Introduce `y hy`. Rewrite `hy` using `[Ideal.mem_pointwise_smul_iff_inv_smul_mem]`. Conclude with `(hc _ y ((GlobalTheory.TypePlaces.star_eq_conj D _).trans (D.host.conj.apply_symm_apply (y : D.host.E))).symm).1 hy`. Establish `hmax : (D.host.conj • P.asIdeal).IsMaximal`.

Use `P.isPrime` as an intermediate fact. Use `Ideal.IsPrime.isMaximal inferInstance fun h0 => P.ne_bot ?_` and prove the remaining obligations. Use `congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0` as an intermediate fact. Simplify using `using this`. Conclude with `(GlobalTheory.Mem.Chr.conjPl_iff_smul D.host.conj P P').2 (hmax.eq_of_le P'.isPrime.ne_top hle)`.
-/
theorem conj_of_isConj {D : D7} {P P' : Pl D.host.E} (hc : Formalism.L2.DIV.IsConjPl P P') :
    GlobalTheory.Mem.Chr.ConjPl D.host.conj.toRingEquiv P P' := by
  have hle : D.host.conj • P.asIdeal ≤ P'.asIdeal := by
    intro y hy
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
    exact (hc _ y ((GlobalTheory.TypePlaces.star_eq_conj D _).trans (D.host.conj.apply_symm_apply (y : D.host.E))).symm).1 hy
  have hmax : (D.host.conj • P.asIdeal).IsMaximal := by
    have := P.isPrime
    refine Ideal.IsPrime.isMaximal inferInstance fun h0 => P.ne_bot ?_
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
    simpa using this
  exact (GlobalTheory.Mem.Chr.conjPl_iff_smul D.host.conj P P').2 (hmax.eq_of_le P'.isPrime.ne_top hle)

/- English proof (translation)
The claim follows from `Nat.Coprime.cast ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)`.
-/
theorem g_coprime (D : D7) :
    IsCoprime ((D.host.g 0 : ℕ) : 𝓞 D.host.E) ((D.host.g 1 : ℕ) : 𝓞 D.host.E) :=
  Nat.Coprime.cast ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)

/- English proof (translation)
Introduce `h`. Rewrite `h` using `[Nat.cast_mul]`. Establish `key : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ^ 2` using `fun k hk => (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) P hk).2.1`. Establish `hno : ¬ (((D.host.g 0 : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal ∧ ((D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal)`. Introduce and unpack `⟨h0, h1⟩`.

Take `⟨a, b, hab⟩` from `g_coprime D`. Apply `P.isPrime.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one, ← hab]`. Conclude with `add_mem (Ideal.mul_mem_left _ _ h0) (Ideal.mul_mem_left _ _ h1)`. Establish `hP` using `P.isPrime`.

Break down `P.isPrime.mem_or_mem (Ideal.pow_le_self two_ne_zero h) with h0 | h1` into its components or cases. Break down `Ideal.IsPrime.mul_mem_pow P.asIdeal (mul_comm (_ : 𝓞 D.host.E) _ ▸ h) with h' | h'` into its components or cases. Conclude with `hno ⟨h0, h'⟩`. Conclude with `key 0 h0 h'`. Break down `Ideal.IsPrime.mul_mem_pow P.asIdeal h with h' | h'` into its components or cases.

Conclude with `hno ⟨h', h1⟩`. Conclude with `key 1 h1 h'`.
-/
theorem g_not_mem_sq (D : D7) (P : Pl D.host.E) :
    ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ^ 2 := by
  intro h
  rw [Nat.cast_mul] at h
  have key : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ^ 2 :=
    fun k hk => (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) P hk).2.1
  have hno : ¬ (((D.host.g 0 : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal ∧ ((D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) := by
    rintro ⟨h0, h1⟩
    obtain ⟨a, b, hab⟩ := g_coprime D
    apply P.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hab]
    exact add_mem (Ideal.mul_mem_left _ _ h0) (Ideal.mul_mem_left _ _ h1)
  have hP := P.isPrime
  rcases P.isPrime.mem_or_mem (Ideal.pow_le_self two_ne_zero h) with h0 | h1
  · rcases Ideal.IsPrime.mul_mem_pow P.asIdeal (mul_comm (_ : 𝓞 D.host.E) _ ▸ h) with h' | h'
    · exact hno ⟨h0, h'⟩
    · exact key 0 h0 h'
  · rcases Ideal.IsPrime.mul_mem_pow P.asIdeal h with h' | h'
    · exact hno ⟨h', h1⟩
    · exact key 1 h1 h'

/- English proof (translation)
Establish `hm0 : ((m : ℕ) : 𝓞 E) ≠ 0` using `by exact_mod_cast hm`. Take `⟨q, hq⟩` from `cmpS_surj (F := F) (Ideal.span {((m : ℕ) : 𝓞 E)}) (by simpa using hm0) (Ideal.Quotient.mk _ s)`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective q`. Establish `hb : oToS F E b - s ∈ idS F (Ideal.span {((m : ℕ) : 𝓞 E)})` using `Ideal.Quotient.eq.1 hq`. Rewrite `hb` using `[idS, Ideal.map_span, Set.image_singleton, map_natCast, Ideal.mem_span_singleton]`.

Take `⟨u, hu⟩` from `hb`. Establish `hd : ((m : ℕ) : 𝓞 E) ∣ b`. Use `dvd_of_mem_primes hm0 fun P hP => ⟨hsq P, ?_⟩` and prove the remaining obligations. Establish `e` using `congrArg (resS F P) hu`. Rewrite `e` using `[map_sub, h P hP, sub_zero, resS_oToS, map_mul, map_natCast]`.

Establish `e0 : ((m : ℕ) : kP P) = 0`. Rewrite using `[← map_natCast (Ideal.Quotient.mk P.asIdeal), Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hP`. Rewrite `e` using `[e0, zero_mul]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 e`.

Take `⟨w, rfl⟩` from `hd`. Use `⟨oToS F E w - u, ?_⟩` and prove the remaining obligations. Rewrite `hu` using `[map_mul, map_natCast]`. Take the linear combination `-hu`.
-/
theorem exists_eq_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m : ℕ}
    (hm : m ≠ 0) (hsq : ∀ P : Pl E, ((m : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (s : Formalism.L2.Herm.intAf F E)
    (h : ∀ P : Pl E, ((m : ℕ) : 𝓞 E) ∈ P.asIdeal → resS F P s = 0) :
    ∃ t : Formalism.L2.Herm.intAf F E, s = (m : ℕ) * t := by
  have hm0 : ((m : ℕ) : 𝓞 E) ≠ 0 := by exact_mod_cast hm
  obtain ⟨q, hq⟩ := cmpS_surj (F := F) (Ideal.span {((m : ℕ) : 𝓞 E)}) (by simpa using hm0)
    (Ideal.Quotient.mk _ s)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hb : oToS F E b - s ∈ idS F (Ideal.span {((m : ℕ) : 𝓞 E)}) :=
    Ideal.Quotient.eq.1 hq
  rw [idS, Ideal.map_span, Set.image_singleton, map_natCast, Ideal.mem_span_singleton] at hb
  obtain ⟨u, hu⟩ := hb
  have hd : ((m : ℕ) : 𝓞 E) ∣ b := by
    refine dvd_of_mem_primes hm0 fun P hP => ⟨hsq P, ?_⟩
    have e := congrArg (resS F P) hu
    rw [map_sub, h P hP, sub_zero, resS_oToS, map_mul, map_natCast] at e
    have e0 : ((m : ℕ) : kP P) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk P.asIdeal), Ideal.Quotient.eq_zero_iff_mem]; exact hP
    rw [e0, zero_mul] at e
    exact Ideal.Quotient.eq_zero_iff_mem.1 e
  obtain ⟨w, rfl⟩ := hd
  refine ⟨oToS F E w - u, ?_⟩
  rw [map_mul, map_natCast] at hu
  linear_combination -hu

/- English proof (translation)
Establish `key : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → Pb.Div k P ∨ Pb.Div k (Formalism.L2.DIV.conjPl P)`. Introduce `k hk`. Establish `h` using `((GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) P hk).2.2.2 (Pb.pb k) (Pb.pb_over k) _ (conj_of_isConj (Formalism.L2.DIV.isConjPl_conjPl P))).2`. Assume the negation of the conclusion as `hn`. Rewrite `hn` using `[not_or]`.

Conclude with `hn.1 (h.2 hn.2)`. Rewrite `hP` using `[Nat.cast_mul]`. Conclude with `(P.isPrime.mem_or_mem hP).elim (fun h => ⟨0, key 0 h⟩) (fun h => ⟨1, key 1 h⟩)`.
-/
theorem div_or_conj {D : D7} (Pb : Formalism.L2.Host.PiBar D.host) (P : Pl D.host.E)
    (hP : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    ∃ k, Pb.Div k P ∨ Pb.Div k (Formalism.L2.DIV.conjPl P) := by
  have key : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → Pb.Div k P ∨ Pb.Div k (Formalism.L2.DIV.conjPl P) := by
    intro k hk
    have h := ((GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) P
      hk).2.2.2 (Pb.pb k) (Pb.pb_over k) _ (conj_of_isConj (Formalism.L2.DIV.isConjPl_conjPl P))).2
    by_contra hn
    rw [not_or] at hn
    exact hn.1 (h.2 hn.2)
  rw [Nat.cast_mul] at hP
  exact (P.isPrime.mem_or_mem hP).elim (fun h => ⟨0, key 0 h⟩) (fun h => ⟨1, key 1 h⟩)

/- English proof (translation)
Introduce `D G _ _ Pl0 T A Ks _ _ _ R F hIs _`. Establish `hPg : ∀ PP, PP ∈ R.Pg ↔ ∃ k, R.C.P.Div k PP` using `hIs.Pg`. Use `⟨fun PP hPP => ?_, fun c hc hc' h => ?_⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `(hPg PP).1 hPP`. Establish `ho : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal` using `R.C.P.overP hk`.

Rewrite using `[Nat.cast_mul]`. Use `fin_cases k`. Conclude with `Ideal.mul_mem_right _ _ ho`. Conclude with `Ideal.mul_mem_left _ _ ho`. Take `⟨t, ht⟩` from `exists_eq_mul (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero) (g_not_mem_sq D) ⟨c, hc⟩ fun P hP => by`.

Take `⟨k, hk | hk⟩` from `div_or_conj R.C.P P hP`. Conclude with `(h P ((hPg P).2 ⟨k, hk⟩)).1`. Conclude with `(resS_sigS_eq_zero_iff (II D).cm (Formalism.L2.DIV.isConjPl_conjPl P) ⟨c, hc⟩).1 (h _ ((hPg _).2 ⟨k, hk⟩)).2`. Use `⟨t.1, t.2, ?_⟩` and prove the remaining obligations. Establish `e` using `congrArg Subtype.val ht`.

Rewrite `e` using `[Subring.coe_mul, Subring.coe_natCast]`. Conclude with `e`.
-/
theorem main : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.IsGrp F → (∀ PP ∈ R.Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧ ∀ (c : EAf D) (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hc' : sigA (II D) c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), (∀ PP ∈ R.Pg, resS D.host.F PP ⟨c, hc⟩ = 0 ∧ resS D.host.F PP ⟨sigA (II D) c, hc'⟩ = 0) → ZMod' (II D) (D.host.g 0 * D.host.g 1) c := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hIs _
  have hPg : ∀ PP, PP ∈ R.Pg ↔ ∃ k, R.C.P.Div k PP := hIs.Pg
  refine ⟨fun PP hPP => ?_, fun c hc hc' h => ?_⟩
  · obtain ⟨k, hk⟩ := (hPg PP).1 hPP
    have ho : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := R.C.P.overP hk
    rw [Nat.cast_mul]
    fin_cases k
    · exact Ideal.mul_mem_right _ _ ho
    · exact Ideal.mul_mem_left _ _ ho
  · obtain ⟨t, ht⟩ := exists_eq_mul (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
      (g_not_mem_sq D) ⟨c, hc⟩ fun P hP => by
        obtain ⟨k, hk | hk⟩ := div_or_conj R.C.P P hP
        · exact (h P ((hPg P).2 ⟨k, hk⟩)).1
        · exact (resS_sigS_eq_zero_iff (II D).cm (Formalism.L2.DIV.isConjPl_conjPl P) ⟨c, hc⟩).1
            (h _ ((hPg _).2 ⟨k, hk⟩)).2
    refine ⟨t.1, t.2, ?_⟩
    have e := congrArg Subtype.val ht
    rw [Subring.coe_mul, Subring.coe_natCast] at e
    exact e

end GlobalTheory.SeeConjZMod
