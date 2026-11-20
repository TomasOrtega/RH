import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Formalism.LocalToGlobal.Columns.TiedUpDnA
import Formalism.LocalToGlobal.Columns.TiedUpDnLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPtOfIffUnitaryDecoration
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT
import Formalism.LocalToGlobal.Columns.DecorationStabilizerTrivialUnipotent

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
noncomputable section

namespace GlobalTheory.Mem.PrimesAtLevel

/- English proof (translation)
Take `⟨a, b, hab⟩ : IsCoprime (p : ℤ) (q : ℤ)` from `Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hne)`. Establish `h1 : ((a * p + b * q : ℤ) : R) = 1` using `by rw [hab, Int.cast_one]`. Move the coercions through the operations in `at h1`. Apply `(inferInstance : P.IsPrime).ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one, ← h1]`.

Conclude with `P.add_mem (P.mul_mem_left _ hpP) (P.mul_mem_left _ hqP)`.
-/
theorem not_both_mem {R : Type} [CommRing R] (P : Ideal R) [P.IsPrime] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (hpP : (p : R) ∈ P) (hqP : (q : R) ∈ P) : False := by
  obtain ⟨a, b, hab⟩ : IsCoprime (p : ℤ) (q : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hne)
  have h1 : ((a * p + b * q : ℤ) : R) = 1 := by rw [hab, Int.cast_one]
  push_cast at h1
  apply (inferInstance : P.IsPrime).ne_top
  rw [Ideal.eq_top_iff_one, ← h1]
  exact P.add_mem (P.mul_mem_left _ hpP) (P.mul_mem_left _ hqP)

/- English proof (translation)
Introduce `B X I hI l u a v`. Take `⟨P, hP⟩` from `v`. Simplify using `only at hP ⊢`. Establish `hpr` using `l.pr`. Establish `hpiT : (B.primes X).piT u ∈ P.asIdeal`.

Unfold `Primes.vT divs at hP`. Use `split_ifs at hP with h`. Conclude with `h.mem_toFinset.mp hP`. Simplify using `at hP`. Establish `hT : (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∈ P.asIdeal`.

Rewrite using `[← hpr.piT_norm u]`. Conclude with `P.asIdeal.mul_mem_right _ hpiT`. Establish `hTF : (((B.primes X).T u : ℕ) : 𝓞 B.host.F) ∈ (P.under (𝓞 B.host.F)).asIdeal` using `by show _ ∈ Ideal.comap (algebraMap _ _) _`. Rewrite using `[Ideal.mem_comap, map_natCast]`. Conclude with `hT`.

Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `hc`. Establish `h2 : B.fields.conjO ((B.primes X).piT u) ∈ P.asIdeal`. Establish `h3 : (B.primes X).piT u ∈ (conjPrime₂ P).asIdeal` using `by rw [hc]; exact hpiT`. Conclude with `(mem_conjP P _).mp h3`.

Take `⟨x, y, hxy⟩` from `hpr.piT_cop u`. Apply `P.isPrime.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one, ← hxy]`. Conclude with `P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ hpiT) (P.asIdeal.mul_mem_left _ h2)`. Introduce `w hw hov`.

Establish `hTw : (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∈ w.asIdeal`. Rewrite `hov` using `[IsOver]`. Rewrite `hTF` using `[hov, Ideal.mem_comap, map_natCast]`. Conclude with `hTF`. Take `⟨i, hi⟩ : ∃ i, w ∈ (B.primes X).vG i` from `by classical`.

Break down `Finset.mem_union.mp hw with h | h` into its components or cases. Conclude with `⟨0, h⟩`. Conclude with `⟨1, h⟩`. Establish `hgw : (((B.primes X).g i : ℕ) : 𝓞 B.fields.E) ∈ w.asIdeal`. Establish `hc : B.fields.conjO ((B.primes X).piG i) ∈ w.asIdeal`.

Unfold `Primes.vG divs at hi`. Use `split_ifs at hi with h`. Conclude with `h.mem_toFinset.mp hi`. Simplify using `at hi`. Rewrite using `[← hpr.piG_norm i]`.

Conclude with `w.asIdeal.mul_mem_left _ hc`. Conclude with `not_both_mem w.asIdeal (hpr.T_prime u) (hpr.g_prime i) (hpr.T_ne_g u i) hTw hgw`. Introduce `Q hQ hov`. Take `⟨v, -, hsel, hgood⟩` from `I.exists_of_mem_Q hQ`. Establish `hv : v.asIdeal = (P.under (𝓞 B.host.F)).asIdeal`.

Rewrite using `[hov, ← hsel]`. Conclude with `(hI.sel_ok v).symm`. Establish `hTv : (((B.primes X).T u : ℕ) : 𝓞 B.fields.F ⧸ v.asIdeal) = 0`. Rewrite using `[← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem, hv]`. Conclude with `hTF`.

Establish `hd : ringChar (𝓞 B.fields.F ⧸ v.asIdeal) ∣ (B.primes X).T u` using `(ringChar.spec _ _).mp hTv`. Break down `(Nat.dvd_prime (hpr.T_prime u)).mp hd with h1 | h1` into its components or cases. Conclude with `CharP.ringChar_ne_one h1`. Apply `hgood.2.2` to reduce the goal to its premises. Use `hI.T_mem u using 1` and compare the differences between its conclusion and the goal.

Conclude with `h1`. Conclude with `Finset.disjoint_right.mpr (Q_notMem_of_ok hI a)`.
-/
theorem primes_atT : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (a : I.ι) (v : (I.atT l u a).vT), conjPrime₂ v.1 ≠ v.1 ∧ (∀ w ∈ (B.primes X).vGs, ¬ IsOver (v.1.under (𝓞 B.host.F)) w) ∧ (∀ P ∈ I.Q a, ¬ IsOver (v.1.under (𝓞 B.host.F)) P) ∧ Disjoint (B.primes X).vGs (I.Q a) := by
  intro B X I hI l u a v
  obtain ⟨P, hP⟩ := v
  dsimp only at hP ⊢
  have hpr := l.pr
  have hpiT : (B.primes X).piT u ∈ P.asIdeal := by
    unfold Primes.vT divs at hP
    split_ifs at hP with h
    · exact h.mem_toFinset.mp hP
    · simp at hP
  have hT : (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∈ P.asIdeal := by
    rw [← hpr.piT_norm u]
    exact P.asIdeal.mul_mem_right _ hpiT
  have hTF : (((B.primes X).T u : ℕ) : 𝓞 B.host.F) ∈ (P.under (𝓞 B.host.F)).asIdeal := by
    show _ ∈ Ideal.comap (algebraMap _ _) _
    rw [Ideal.mem_comap, map_natCast]
    exact hT
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hc
    have h2 : B.fields.conjO ((B.primes X).piT u) ∈ P.asIdeal := by
      have h3 : (B.primes X).piT u ∈ (conjPrime₂ P).asIdeal := by rw [hc]; exact hpiT
      exact (mem_conjP P _).mp h3
    obtain ⟨x, y, hxy⟩ := hpr.piT_cop u
    apply P.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hxy]
    exact P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ hpiT) (P.asIdeal.mul_mem_left _ h2)
  · intro w hw hov
    have hTw : (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∈ w.asIdeal := by
      rw [IsOver] at hov
      rw [hov, Ideal.mem_comap, map_natCast] at hTF
      exact hTF
    obtain ⟨i, hi⟩ : ∃ i, w ∈ (B.primes X).vG i := by
      classical
      rcases Finset.mem_union.mp hw with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    have hgw : (((B.primes X).g i : ℕ) : 𝓞 B.fields.E) ∈ w.asIdeal := by
      have hc : B.fields.conjO ((B.primes X).piG i) ∈ w.asIdeal := by
        unfold Primes.vG divs at hi
        split_ifs at hi with h
        · exact h.mem_toFinset.mp hi
        · simp at hi
      rw [← hpr.piG_norm i]
      exact w.asIdeal.mul_mem_left _ hc
    exact not_both_mem w.asIdeal (hpr.T_prime u) (hpr.g_prime i) (hpr.T_ne_g u i) hTw hgw
  · intro Q hQ hov
    obtain ⟨v, -, hsel, hgood⟩ := I.exists_of_mem_Q hQ
    have hv : v.asIdeal = (P.under (𝓞 B.host.F)).asIdeal := by
      rw [hov, ← hsel]
      exact (hI.sel_ok v).symm
    have hTv : (((B.primes X).T u : ℕ) : 𝓞 B.fields.F ⧸ v.asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem, hv]
      exact hTF
    have hd : ringChar (𝓞 B.fields.F ⧸ v.asIdeal) ∣ (B.primes X).T u := (ringChar.spec _ _).mp hTv
    rcases (Nat.dvd_prime (hpr.T_prime u)).mp hd with h1 | h1
    · exact CharP.ringChar_ne_one h1
    · apply hgood.2.2
      convert hI.T_mem u using 1
      exact h1
  · exact Finset.disjoint_right.mpr (Q_notMem_of_ok hI a)

end GlobalTheory.Mem.PrimesAtLevel
