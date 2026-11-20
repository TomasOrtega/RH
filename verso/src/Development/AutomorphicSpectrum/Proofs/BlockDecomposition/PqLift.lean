import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRingHomPowPrimePow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PfFacts

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

/- English proof (translation)
Introduce `p _ S _ T _ T₁ _ i I φ hPQ hPf hI`. Take `⟨-, hred, hroot, hinj, -⟩` from `pf_facts p T₁ hPf`. Establish `hcharT : (p : T) = 0` using `hPQ.pf.char`. Establish `hcharT₁ : (p : T₁) = 0` using `hPf.char`. Establish `hA : ∀ a b : S, i a = i b → φ a = φ b`.

Introduce `a b hab`. Take `⟨j, hj⟩` from `(hPQ.ker (a - b)).mp (by rw [map_sub, hab, sub_self])`. Establish `h0` using `hI _ hj`. Rewrite `h0` using `[map_pow, map_sub]`. Conclude with `sub_eq_zero.mp (hred _ _ h0)`.

Establish `hfrobT : ∀ (k : ℕ) (u v : T), (u + v) ^ p ^ k = u ^ p ^ k + v ^ p ^ k`. Introduce `k u v`. Take `⟨F, hF⟩` from `GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p T hcharT k`. Rewrite using `[← hF, ← hF, ← hF, map_add]`. Establish `hfrobT₁ : ∀ (k : ℕ) (u v : T₁), (u + v) ^ p ^ k = u ^ p ^ k + v ^ p ^ k`.

Introduce `k u v`. Take `⟨F, hF⟩` from `GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p T₁ hcharT₁ k`. Rewrite using `[← hF, ← hF, ← hF, map_add]`. Set `Rel : T → T₁ → Prop` to `fun y z => ∃ (k : ℕ) (x : S), y ^ p ^ k = i x ∧ z ^ p ^ k = φ x`. Establish `hex : ∀ y, ∃ z, Rel y z`.

Introduce `y`. Take `⟨k, x, hx⟩` from `hPQ.pow y`. Take `⟨z, hz⟩` from `hroot k (φ x)`. Conclude with `⟨z, k, x, hx, hz⟩`. Establish `hfun : ∀ y z z', Rel y z → Rel y z' → z = z'`.

Introduce and unpack `y z z' ⟨k, x, hyx, hzx⟩ ⟨m, x', hyx', hzx'⟩`. Establish `hi : i (x ^ p ^ m) = i (x' ^ p ^ k)`. Rewrite using `[map_pow, map_pow, ← hyx, ← hyx', ← pow_mul, ← pow_mul, mul_comm]`. Establish `hφ` using `hA _ _ hi`. Rewrite `hφ` using `[map_pow, map_pow, ← hzx, ← hzx', ← pow_mul, ← pow_mul, mul_comm, ← pow_add]`.

Conclude with `hinj _ _ _ hφ`. Use `choose ψf hψf using hex`. Establish `hRelψ : ∀ y z, Rel y z → ψf y = z` using `fun y z h => hfun y _ _ (hψf y) h`. Establish `hadd : ∀ y₁ y₂, ψf (y₁ + y₂) = ψf y₁ + ψf y₂`. Introduce `y₁ y₂`.

Apply `hRelψ` to reduce the goal to its premises. Take `⟨k₁, x₁, hy₁, hz₁⟩` from `hψf y₁`. Take `⟨k₂, x₂, hy₂, hz₂⟩` from `hψf y₂`. Use `⟨k₁ + k₂, x₁ ^ p ^ k₂ + x₂ ^ p ^ k₁, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hfrobT, map_add, map_pow, map_pow, ← hy₁, ← hy₂, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add, add_comm k₂ k₁]`.

Rewrite using `[hfrobT₁, map_add, map_pow, map_pow, ← hz₁, ← hz₂, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add, add_comm k₂ k₁]`. Establish `hmul : ∀ y₁ y₂, ψf (y₁ * y₂) = ψf y₁ * ψf y₂`. Introduce `y₁ y₂`. Apply `hRelψ` to reduce the goal to its premises. Take `⟨k₁, x₁, hy₁, hz₁⟩` from `hψf y₁`.

Take `⟨k₂, x₂, hy₂, hz₂⟩` from `hψf y₂`. Use `⟨k₁ + k₂, x₁ ^ p ^ k₂ * x₂ ^ p ^ k₁, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_pow, map_mul, map_pow, map_pow, ← hy₁, ← hy₂, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add, add_comm k₂ k₁]`. Rewrite using `[mul_pow, map_mul, map_pow, map_pow, ← hz₁, ← hz₂, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add, add_comm k₂ k₁]`. Establish `h1 : ψf 1 = 1` using `hRelψ 1 1 ⟨0, 1, by simp, by simp⟩`.

Establish `h0 : ψf 0 = 0` using `hRelψ 0 0 ⟨0, 0, by simp, by simp⟩`. Set `ψ : T →+* T₁` to `{ toFun := ψf, map_one' := h1, map_mul' := hmul, map_zero' := h0, map_add' := hadd }`. Use `⟨ψ, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `s show ψf (i s) = φ s`. Conclude with `hRelψ (i s) (φ s) ⟨0, s, by simp, by simp⟩`.

Introduce `ψ' hψ'`. Use extensionality with `y`. Use `show ψ' y = ψf y`. Take `⟨k, x, hx⟩` from `hPQ.pow y`. Use `(hRelψ y (ψ' y) ⟨k, x, hx, ?_⟩).symm` and prove the remaining obligations.

Rewrite using `[← map_pow, hx, ← RingHom.comp_apply, hψ']`.
-/
theorem pq_lift : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] (T : Type) [CommRing T]
    (T₁ : Type) [CommRing T₁] (i : S →+* T) (I : Ideal S) (φ : S →+* T₁),
    PQ p i I → Pf p T₁ → (∀ x ∈ I, φ x = 0) → ∃! ψ : T →+* T₁, ψ.comp i = φ := by
  intro p _ S _ T _ T₁ _ i I φ hPQ hPf hI
  obtain ⟨-, hred, hroot, hinj, -⟩ := pf_facts p T₁ hPf
  have hcharT : (p : T) = 0 := hPQ.pf.char
  have hcharT₁ : (p : T₁) = 0 := hPf.char
  have hA : ∀ a b : S, i a = i b → φ a = φ b := by
    intro a b hab
    obtain ⟨j, hj⟩ := (hPQ.ker (a - b)).mp (by rw [map_sub, hab, sub_self])
    have h0 := hI _ hj
    rw [map_pow, map_sub] at h0
    exact sub_eq_zero.mp (hred _ _ h0)
  have hfrobT : ∀ (k : ℕ) (u v : T), (u + v) ^ p ^ k = u ^ p ^ k + v ^ p ^ k := by
    intro k u v
    obtain ⟨F, hF⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p T hcharT k
    rw [← hF, ← hF, ← hF, map_add]
  have hfrobT₁ : ∀ (k : ℕ) (u v : T₁), (u + v) ^ p ^ k = u ^ p ^ k + v ^ p ^ k := by
    intro k u v
    obtain ⟨F, hF⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p T₁ hcharT₁ k
    rw [← hF, ← hF, ← hF, map_add]
  let Rel : T → T₁ → Prop := fun y z => ∃ (k : ℕ) (x : S), y ^ p ^ k = i x ∧ z ^ p ^ k = φ x
  have hex : ∀ y, ∃ z, Rel y z := by
    intro y
    obtain ⟨k, x, hx⟩ := hPQ.pow y
    obtain ⟨z, hz⟩ := hroot k (φ x)
    exact ⟨z, k, x, hx, hz⟩
  have hfun : ∀ y z z', Rel y z → Rel y z' → z = z' := by
    rintro y z z' ⟨k, x, hyx, hzx⟩ ⟨m, x', hyx', hzx'⟩
    have hi : i (x ^ p ^ m) = i (x' ^ p ^ k) := by
      rw [map_pow, map_pow, ← hyx, ← hyx', ← pow_mul, ← pow_mul, mul_comm]
    have hφ := hA _ _ hi
    rw [map_pow, map_pow, ← hzx, ← hzx', ← pow_mul, ← pow_mul, mul_comm, ← pow_add] at hφ
    exact hinj _ _ _ hφ
  choose ψf hψf using hex
  have hRelψ : ∀ y z, Rel y z → ψf y = z := fun y z h => hfun y _ _ (hψf y) h
  have hadd : ∀ y₁ y₂, ψf (y₁ + y₂) = ψf y₁ + ψf y₂ := by
    intro y₁ y₂
    apply hRelψ
    obtain ⟨k₁, x₁, hy₁, hz₁⟩ := hψf y₁
    obtain ⟨k₂, x₂, hy₂, hz₂⟩ := hψf y₂
    refine ⟨k₁ + k₂, x₁ ^ p ^ k₂ + x₂ ^ p ^ k₁, ?_, ?_⟩
    · rw [hfrobT, map_add, map_pow, map_pow, ← hy₁, ← hy₂, ← pow_mul, ← pow_mul, ← pow_add,
        ← pow_add, add_comm k₂ k₁]
    · rw [hfrobT₁, map_add, map_pow, map_pow, ← hz₁, ← hz₂, ← pow_mul, ← pow_mul, ← pow_add,
        ← pow_add, add_comm k₂ k₁]
  have hmul : ∀ y₁ y₂, ψf (y₁ * y₂) = ψf y₁ * ψf y₂ := by
    intro y₁ y₂
    apply hRelψ
    obtain ⟨k₁, x₁, hy₁, hz₁⟩ := hψf y₁
    obtain ⟨k₂, x₂, hy₂, hz₂⟩ := hψf y₂
    refine ⟨k₁ + k₂, x₁ ^ p ^ k₂ * x₂ ^ p ^ k₁, ?_, ?_⟩
    · rw [mul_pow, map_mul, map_pow, map_pow, ← hy₁, ← hy₂, ← pow_mul, ← pow_mul, ← pow_add,
        ← pow_add, add_comm k₂ k₁]
    · rw [mul_pow, map_mul, map_pow, map_pow, ← hz₁, ← hz₂, ← pow_mul, ← pow_mul, ← pow_add,
        ← pow_add, add_comm k₂ k₁]
  have h1 : ψf 1 = 1 := hRelψ 1 1 ⟨0, 1, by simp, by simp⟩
  have h0 : ψf 0 = 0 := hRelψ 0 0 ⟨0, 0, by simp, by simp⟩
  let ψ : T →+* T₁ :=
    { toFun := ψf, map_one' := h1, map_mul' := hmul, map_zero' := h0, map_add' := hadd }
  refine ⟨ψ, ?_, ?_⟩
  · ext s
    show ψf (i s) = φ s
    exact hRelψ (i s) (φ s) ⟨0, s, by simp, by simp⟩
  · intro ψ' hψ'
    ext y
    show ψ' y = ψf y
    obtain ⟨k, x, hx⟩ := hPQ.pow y
    refine (hRelψ y (ψ' y) ⟨k, x, hx, ?_⟩).symm
    rw [← map_pow, hx, ← RingHom.comp_apply, hψ']

end GlobalTheory.CompanionTheory.PerfectRing
