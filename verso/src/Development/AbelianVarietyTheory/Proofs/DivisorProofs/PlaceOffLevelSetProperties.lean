import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfRegularForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankWeightComponentEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult Formalism.IndefR.Links GlobalTheory.SphPar
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

open SplitOffPlaces Formalism.L2.Col Formalism.HermitianLatticesTheory in

/- English proof (translation)
Introduce `D Pb Pg S P hPg hS hP`. Establish `key : ∀ PP ∈ Pg, PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P`. Introduce `PP h`. Take `⟨x, hx, hxP⟩` from `hP _ (hS PP h)`. Establish `hx' : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ PP.asIdeal` using `hx`.

Use `⟨fun e => hxP _ rfl (e ▸ hx'), fun hc => ?_⟩` and prove the remaining obligations. Take `⟨c', h1, h2⟩` from `hc _ hx'`. Use `hxP c' ?_ h1` and prove the remaining obligations. Rewrite using `[h2]`. Conclude with `(D.sp.cm.fixed _).2 ⟨(x : D.host.F), rfl⟩`.

Establish `hne : ∀ PP ∈ Pg, PP ≠ P` using `fun PP h => (key PP h).1`. Establish `hne' : ∀ PP ∈ Pg, PP ≠ conjSpec P`. Introduce `PP h e`. Apply `(key PP h).2` to reduce the goal to its premises. Introduce `c hc`.

Rewrite `hc` using `[e]`. Conclude with `⟨cO D.host.E c, hc, rfl⟩`. Establish `hg : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal`. Introduce `k hk`. Establish `h1 : Pb.pb k ≠ P.under (𝓞 D.host.K)` using `fun e => hne P ((hPg P).2 ⟨k, e.symm⟩) rfl`.

Establish `h2 : Pb.pb k ≠ (conjSpec P).under (𝓞 D.host.K)` using `fun e => hne' (conjSpec P) ((hPg _).2 ⟨k, e.symm⟩) rfl`. Take `⟨x, hx, hx1, hx2⟩` from `exists_mem_not_mem h1 h2`. Take `⟨x', n, hx', hn⟩` from `exists_norm D x`. Establish `hnP : (n : 𝓞 D.host.E) ∉ P.asIdeal`. Introduce `h`.

Establish `e : (n : 𝓞 D.host.E) = algebraMap (𝓞 D.host.K) (𝓞 D.host.E) x * cO D.host.E (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) x)`. Rewrite using `[← hx', ← map_mul, hn, map_intCast]`. Rewrite `h` using `[e]`. Break down `P.isPrime.mem_or_mem h with h | h` into its components or cases. Conclude with `hx1 h`.

Conclude with `hx2 h`. Establish `hnb : (n : 𝓞 D.host.K) ∈ (Pb.pb k).asIdeal` using `hn ▸ Ideal.mul_mem_right _ _ hx`. Establish `hp : Prime (D.host.g k : ℤ)` using `Nat.prime_iff_prime_int.1 (D.host.g_prime k)`. Distinguish the cases in `hd : (D.host.g k : ℤ) ∣ n`. Take `⟨m, rfl⟩` from `hd`.

Apply `hnP` to reduce the goal to its premises. Use `push_cast`. Conclude with `Ideal.mul_mem_right _ _ hk`. Take `⟨a, b, hab⟩` from `(hp.irreducible.coprime_iff_not_dvd).2 hd`. Apply `(Pb.pb k).isPrime.ne_top` to reduce the goal to its premises.

Rewrite using `[Ideal.eq_top_iff_one]`. Establish `e : (1 : 𝓞 D.host.K) = a * ((D.host.g k : ℕ) : 𝓞 D.host.K) + b * n`. Conclude with `congrArg (Int.cast : ℤ → 𝓞 D.host.K) hab.symm` after adjusting the coercions. Rewrite using `[e]`. Conclude with `add_mem (Ideal.mul_mem_left _ _ (Pb.pb_over k)) (Ideal.mul_mem_left _ _ hnb)`.

Use `⟨?_, key⟩` and prove the remaining obligations. Introduce `h`. Rewrite `h` using `[Nat.cast_mul]`. Break down `P.isPrime.mem_or_mem h with h | h` into its components or cases. Conclude with `hg 0 h`.

Conclude with `hg 1 h`.
-/
theorem offS_not_type_places : ∀ {D : D7} (Pb : Formalism.L2.Host.PiBar D.host) (Pg : Finset (HeightOneSpectrum (𝓞 D.host.E))) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (P : HeightOneSpectrum (𝓞 D.host.E)), (∀ PP, PP ∈ Pg ↔ ∃ k, Pb.Div k PP) → (∀ PP ∈ Pg, PP.under (𝓞 D.host.F) ∈ S) → OffS D S P → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ ∀ PP ∈ Pg, PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P := by
  intro D Pb Pg S P hPg hS hP
  have key : ∀ PP ∈ Pg, PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P := by
    intro PP h
    obtain ⟨x, hx, hxP⟩ := hP _ (hS PP h)
    have hx' : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ PP.asIdeal := hx
    refine ⟨fun e => hxP _ rfl (e ▸ hx'), fun hc => ?_⟩
    obtain ⟨c', h1, h2⟩ := hc _ hx'
    refine hxP c' ?_ h1
    rw [h2]
    exact (D.sp.cm.fixed _).2 ⟨(x : D.host.F), rfl⟩
  have hne : ∀ PP ∈ Pg, PP ≠ P := fun PP h => (key PP h).1
  have hne' : ∀ PP ∈ Pg, PP ≠ conjSpec P := by
    intro PP h e
    apply (key PP h).2
    intro c hc
    rw [e] at hc
    exact ⟨cO D.host.E c, hc, rfl⟩
  have hg : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro k hk
    have h1 : Pb.pb k ≠ P.under (𝓞 D.host.K) := fun e => hne P ((hPg P).2 ⟨k, e.symm⟩) rfl
    have h2 : Pb.pb k ≠ (conjSpec P).under (𝓞 D.host.K) := fun e =>
      hne' (conjSpec P) ((hPg _).2 ⟨k, e.symm⟩) rfl
    obtain ⟨x, hx, hx1, hx2⟩ := exists_mem_not_mem h1 h2
    obtain ⟨x', n, hx', hn⟩ := exists_norm D x
    have hnP : (n : 𝓞 D.host.E) ∉ P.asIdeal := by
      intro h
      have e : (n : 𝓞 D.host.E) = algebraMap (𝓞 D.host.K) (𝓞 D.host.E) x * cO D.host.E (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) x) := by
        rw [← hx', ← map_mul, hn, map_intCast]
      rw [e] at h
      rcases P.isPrime.mem_or_mem h with h | h
      · exact hx1 h
      · exact hx2 h
    have hnb : (n : 𝓞 D.host.K) ∈ (Pb.pb k).asIdeal := hn ▸ Ideal.mul_mem_right _ _ hx
    have hp : Prime (D.host.g k : ℤ) := Nat.prime_iff_prime_int.1 (D.host.g_prime k)
    by_cases hd : (D.host.g k : ℤ) ∣ n
    · obtain ⟨m, rfl⟩ := hd
      apply hnP
      push_cast
      exact Ideal.mul_mem_right _ _ hk
    · obtain ⟨a, b, hab⟩ := (hp.irreducible.coprime_iff_not_dvd).2 hd
      apply (Pb.pb k).isPrime.ne_top
      rw [Ideal.eq_top_iff_one]
      have e : (1 : 𝓞 D.host.K) = a * ((D.host.g k : ℕ) : 𝓞 D.host.K) + b * n := by
        exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 D.host.K) hab.symm
      rw [e]
      exact add_mem (Ideal.mul_mem_left _ _ (Pb.pb_over k)) (Ideal.mul_mem_left _ _ hnb)
  refine ⟨?_, key⟩
  intro h
  rw [Nat.cast_mul] at h
  rcases P.isPrime.mem_or_mem h with h | h
  · exact hg 0 h
  · exact hg 1 h

end GlobalTheory
