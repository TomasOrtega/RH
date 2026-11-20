import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRingHomPowPrimePow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PfFacts

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

/- English proof (translation)
Introduce `p _ A _ B _ _ K _ _ n ι hW hA hB`. Take `⟨⟨FA, hFA⟩, -⟩` from `pf_facts p A hA`. Take `⟨⟨FB, hFB⟩, -⟩` from `pf_facts p B hB`. Establish `hchar : (p : K) = 0`. Use `congrArg (algebraMap A K) hA.char` as an intermediate fact.

Simplify using `using this`. Take `⟨F, hF⟩` from `GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p K hchar 1`. Establish `hF' : ∀ x, F x = x ^ p` using `fun x => by rw [hF, pow_one]`. Establish `hcompat : ∀ i, (((ι i : B →+* K)).comp (FB.symm : B →+* B)).comp (algebraMap A B) = (algebraMap A K).comp (FA.symm : A →+* A)`. Introduce `i`.

Use extensionality with `a`. Take `⟨b, rfl⟩` from `FA.surjective a`. Establish `h1 : algebraMap A B (FA b) = FB (algebraMap A B b)`. Rewrite using `[hFA, hFB, map_pow]`. Simplify using `[h1]`.

Take `⟨z, hz1, hz2⟩` from `hW.ex K ((algebraMap A K).comp (FA.symm : A →+* A)) (fun i => ((ι i : B →+* K)).comp (FB.symm : B →+* B)) hcompat`. Establish `hz1' : ∀ a, z (algebraMap A K a) = algebraMap A K (FA.symm a)` using `fun a => by`. Simplify using `using congrArg (fun f : A →+* K => f a) hz1`. Establish `hz2' : ∀ i b, z (ι i b) = ι i (FB.symm b)` using `fun i b => by`. Simplify using `using congrArg (fun f : B →+* K => f b) (hz2 i)`.

Establish `hFa : ∀ a, F (algebraMap A K a) = algebraMap A K (FA a)` using `fun a => by`. Rewrite using `[hF', hFA, map_pow]`. Establish `hFb : ∀ i b, F (ι i b) = ι i (FB b)` using `fun i b => by`. Rewrite using `[hF', hFB, map_pow]`. Establish `hFz : F.comp z = RingHom.id K`.

Apply `hW.uniq K` to reduce the goal to its premises. Use extensionality with `a`. Simplify using `[hz1', hFa]`. Introduce `i`. Use extensionality with `b`.

Simplify using `[hz2', hFb]`. Establish `hzF : z.comp F = RingHom.id K`. Apply `hW.uniq K` to reduce the goal to its premises. Use extensionality with `a`. Simplify using `[hz1', hFa]`.

Introduce `i`. Use extensionality with `b`. Simplify using `[hz2', hFb]`. Use `⟨hchar, ?_, ?_⟩` and prove the remaining obligations. Introduce `x y hxy`.

Establish `h : F x = F y` using `by rw [hF', hF']; exact hxy`. Use `congrArg z h` as an intermediate fact. Establish `hx : ∀ w, z (F w) = w` using `fun w => by`. Simplify using `using congrArg (fun f : K →+* K => f w) hzF`. Rewrite `this` using `[hx, hx]`. Then use the resulting hypothesis.

Introduce `y`. Use `⟨z y, ?_⟩` and prove the remaining obligations. Establish `: F (z y) = y` using `by simpa using congrArg (fun f : K →+* K => f y) hFz`. Simplify `this` using `[hF']`.
-/
theorem wp_pf : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (B : Type) [CommRing B] [Algebra A B]
    (K : Type) [CommRing K] [Algebra A K] (n : ℕ) (ι : Fin n → (B →ₐ[A] K)),
    IsWP ι → Pf p A → Pf p B → Pf p K := by
  intro p _ A _ B _ _ K _ _ n ι hW hA hB
  obtain ⟨⟨FA, hFA⟩, -⟩ := pf_facts p A hA
  obtain ⟨⟨FB, hFB⟩, -⟩ := pf_facts p B hB
  have hchar : (p : K) = 0 := by
    have := congrArg (algebraMap A K) hA.char
    simpa using this
  obtain ⟨F, hF⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p K hchar 1
  have hF' : ∀ x, F x = x ^ p := fun x => by rw [hF, pow_one]
  have hcompat : ∀ i, (((ι i : B →+* K)).comp (FB.symm : B →+* B)).comp (algebraMap A B) =
      (algebraMap A K).comp (FA.symm : A →+* A) := by
    intro i
    ext a
    obtain ⟨b, rfl⟩ := FA.surjective a
    have h1 : algebraMap A B (FA b) = FB (algebraMap A B b) := by
      rw [hFA, hFB, map_pow]
    simp [h1]
  obtain ⟨z, hz1, hz2⟩ := hW.ex K ((algebraMap A K).comp (FA.symm : A →+* A))
    (fun i => ((ι i : B →+* K)).comp (FB.symm : B →+* B)) hcompat
  have hz1' : ∀ a, z (algebraMap A K a) = algebraMap A K (FA.symm a) := fun a => by
    simpa using congrArg (fun f : A →+* K => f a) hz1
  have hz2' : ∀ i b, z (ι i b) = ι i (FB.symm b) := fun i b => by
    simpa using congrArg (fun f : B →+* K => f b) (hz2 i)
  have hFa : ∀ a, F (algebraMap A K a) = algebraMap A K (FA a) := fun a => by
    rw [hF', hFA, map_pow]
  have hFb : ∀ i b, F (ι i b) = ι i (FB b) := fun i b => by
    rw [hF', hFB, map_pow]
  have hFz : F.comp z = RingHom.id K := by
    apply hW.uniq K
    · ext a
      simp [hz1', hFa]
    · intro i
      ext b
      simp [hz2', hFb]
  have hzF : z.comp F = RingHom.id K := by
    apply hW.uniq K
    · ext a
      simp [hz1', hFa]
    · intro i
      ext b
      simp [hz2', hFb]
  refine ⟨hchar, ?_, ?_⟩
  · intro x y hxy
    have h : F x = F y := by rw [hF', hF']; exact hxy
    have := congrArg z h
    have hx : ∀ w, z (F w) = w := fun w => by
      simpa using congrArg (fun f : K →+* K => f w) hzF
    rwa [hx, hx] at this
  · intro y
    refine ⟨z y, ?_⟩
    have : F (z y) = y := by simpa using congrArg (fun f : K →+* K => f y) hFz
    simpa [hF'] using this

end GlobalTheory.CompanionTheory.PerfectRing
