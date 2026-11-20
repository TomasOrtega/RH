import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.CongruenceReduction.LevLocAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PInIdUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocEqOneOfMemGam

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKDef
open GlobalTheory.LFun (KGL)
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc GLw AfQ sim comp loc SameK IsCen cj)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Int.Geo.Pl.Tj
attribute [local instance] Ideal.Quotient.field

namespace UpperTheory.Gal.Int.Geo.Pl.Tj

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
private lemma nat_mem_cj (u : Plc E) (q : ℕ) : (q : 𝓞 E) ∈ (cj u).asIdeal ↔ (q : 𝓞 E) ∈ u.asIdeal := by
  have h : HeightOneSpectrum.under (𝓞 ℚ) (cj u) = HeightOneSpectrum.under (𝓞 ℚ) u :=
    GlobalTheory.DefU.ClassFin.under_conjSrc (F := ℚ) (E := E) _ (fun x => by simp) u
  have h2 : ((q : 𝓞 ℚ) ∈ (HeightOneSpectrum.under (𝓞 ℚ) (cj u)).asIdeal) ↔
      ((q : 𝓞 ℚ) ∈ (HeightOneSpectrum.under (𝓞 ℚ) u).asIdeal) := by rw [h]
  simpa [HeightOneSpectrum.under, Ideal.under_def, Ideal.mem_comap] using h2

/- English proof (translation)
A detailed English derivation is pending.
-/
private lemma q_mem_uId {p : ℕ} [Fact p.Prime] (D : Datum p) (q : ℕ) (r : ℤ) : (q : 𝓞 D.F) ∈ uId D q r :=
  Ideal.subset_span (by simp)

/- English proof (translation)
A detailed English derivation is pending.
-/
private lemma ω_mem_uId {p : ℕ} [Fact p.Prime] (D : Datum p) (q : ℕ) (r : ℤ) : D.ω - (r : 𝓞 D.F) ∈ uId D q r :=
  Ideal.subset_span (by simp)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Move the embeddings inside the algebraic operations. A detailed English derivation is pending.
-/
private lemma natCast_not_mem (u : Plc E) {q m : ℕ} (hm : m.Coprime q) (hq : (q : 𝓞 E) ∈ u.asIdeal) :
    (m : 𝓞 E) ∉ u.asIdeal := by
  intro h
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hm
  have h1 : ((a * (m : ℤ) + b * (q : ℤ) : ℤ) : 𝓞 E) = 1 := by rw [hab]; simp
  have h2 : (1 : 𝓞 E) ∈ u.asIdeal := by
    rw [← h1]; push_cast
    exact add_mem (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ hq)
  exact u.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h2)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Supply the required witnesses or components. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Supply the required witnesses or components. A detailed English derivation is pending.
-/
private lemma cong_of {A : Arith E} {n p : ℕ} [Fact p.Prime] (S : Setup A n p) (F : Frame S) (hD : Dict)
    {q : ℕ} (hq : q.Prime) (hG : A.Good q) (g : GUf E n) (hint : ∀ u, IntM u (comp u g).val)
    (𝔟 : Ideal (𝓞 E)) (hb : 𝔟 ≠ ⊥)
    (hu : ∀ u : Plc E, comp u g = 1 ∨ ((q : 𝓞 E) ∈ u.asIdeal ∧ ∃ s ∈ 𝔟, s ∉ u.asIdeal)) :
    CongId S.L 𝔟 (F.j g) := by
  refine ((hD E A n p S F g).2.2.1 𝔟 hb).2 ?_
  intro u _ i k
  rcases hu u with h1 | ⟨hqu, s, hs, hsu⟩
  · have h0 : F.cmp u g = 1 := by simp [Frame.cmp, h1]
    rw [h0]
    exact ⟨0, zero_mem _, by simp⟩
  · obtain ⟨ha, ha'⟩ := GlobalTheory.EulerTwRestr.mem_KGL_iff.1 (F.a_int u q hq hG hqu)
    have hc : ∀ i k, F.cmp u g i k ∈ u.adicCompletionIntegers E := by
      intro i k
      simp only [Frame.cmp, Units.val_mul, Matrix.mul_apply]
      refine sum_mem fun l _ => mul_mem (sum_mem fun l' _ => mul_mem (ha _ _) (hint u _ _)) (ha' _ _)
    have hy : (F.cmp u g - 1) i k ∈ u.adicCompletionIntegers E := by
      rw [Matrix.sub_apply, Matrix.one_apply]
      split_ifs
      · exact sub_mem (hc i k) (one_mem _)
      · simpa using hc i k
    rw [← Ideal.top_mul 𝔟]
    refine (inIdUnit_holds E u ⊤ 𝔟 ⟨s, hs, hsu⟩ _).2 ?_
    exact ⟨⟨_, hy⟩, by simp [Ideal.map_top], rfl⟩

end UpperTheory.Gal.Int.Geo.Pl.Tj

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Prove the second alternative.

Consider separately whether the proposition holds or fails. Establish an intermediate fact. Prove the second alternative. Prove the first alternative. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis. Prove the first alternative.

Prove the second alternative. Establish an intermediate fact. Establish an intermediate fact. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Separate the alternatives or extract the components of the hypothesis. Prove the first alternative. Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.Int.Geo.Pl.Tj.tCong :
    UpperTheory.Gal.Int.Geo.Pl.Tj.TCong := by
  intro hS hD hL E _ _ _ A n p _ S F x hx N w σ i hi g hg
  have hq : σ.q.Prime := σ.atp.prime
  have hG : A.Good σ.q := σ.good
  have hqw : (σ.q : 𝓞 E) ∈ w.asIdeal := σ.atp.le (q_mem_uId S.D _ _)
  have hrw : A.ω - (σ.r : 𝓞 E) ∈ w.asIdeal := σ.atp.le (ω_mem_uId S.D _ _)
  obtain ⟨s1, -, -, -, s5, -, s7⟩ := hS E A x hx σ.q hq hG.1 w hqw
  have tri : ∀ u : Plc E, comp u g = 1 ∨ ((σ.q : 𝓞 E) ∈ u.asIdeal ∧ (u = w ∨ SameK x (cj u) w)) := by
    intro u
    by_cases h1 : u = w
    · exact Or.inr ⟨h1 ▸ hqw, Or.inl h1⟩
    by_cases h2 : SameK x (cj u) w
    · have h3 : (σ.q : 𝓞 E) ∈ (cj u).asIdeal :=
        (h2 _ (by simpa using natCast_mem _ σ.q)).2 hqw
      exact Or.inr ⟨(nat_mem_cj u _).1 h3, Or.inr h2⟩
    · exact Or.inl (hg.off u h1 h2)
  have hω : ∀ u : Plc E, (σ.q : 𝓞 E) ∈ u.asIdeal → SameK x (cj u) w → A.ω - (σ.r : 𝓞 E) ∉ u.asIdeal := by
    intro u hqu h1 h2
    have h3 := s5 u w ((s7 σ.r hrw u).2 ⟨hqu, h2⟩)
    exact s1 fun y hy => (h3 y hy).symm.trans (h1 y hy)
  refine ⟨fun m hm => ?_, fun 𝔞 h𝔞 ⟨e, he⟩ => ?_⟩
  · refine ((hL p S.D S.G S.L).2.2.2.1 m (F.j g)).2 ?_
    have hm0 : (m : 𝓞 E) ≠ 0 := by
      refine Nat.cast_ne_zero.2 ?_
      rintro rfl
      exact hq.one_lt.ne' ((Nat.coprime_zero_left _).1 hm)
    refine cong_of S F hD hq hG g hg.int (Ideal.span {(m : 𝓞 E)}) (Ideal.span_singleton_eq_bot.not.2 hm0) fun u => ?_
    rcases tri u with h | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, _, Ideal.mem_span_singleton_self _, natCast_not_mem u hm h⟩
  · have hq0 : (σ.q : 𝓞 E) ^ e ∈ 𝔞 :=
      he (Ideal.pow_mem_pow (q_mem_uId S.D _ _) e)
    have hb : 𝔞 ≠ ⊥ := by
      rintro rfl
      exact pow_ne_zero e (Nat.cast_ne_zero.2 hq.ne_zero) ((Ideal.mem_bot).1 hq0)
    refine cong_of S F hD hq hG g hg.int 𝔞 hb fun u => ?_
    rcases tri u with h | ⟨h, rfl | h'⟩
    · exact Or.inl h
    · refine Or.inr ⟨h, ?_⟩
      by_contra hc
      push_neg at hc
      have h1 : 𝔞 ≤ u.asIdeal := hc
      rw [sup_eq_right.2 h1] at h𝔞
      exact u.isPrime.ne_top h𝔞
    · refine Or.inr ⟨h, (A.ω - (σ.r : 𝓞 E)) ^ e, he (Ideal.pow_mem_pow (ω_mem_uId S.D _ _) e), ?_⟩
      exact fun h2 => hω u h h' (u.isPrime.mem_of_pow_mem e h2)
