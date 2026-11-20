import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.SinSupp
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.SepPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.SinFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.SinMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.SinLem

open UpperTheory.V.FW

/- English proof (translation)
Introduce `l _ ι _ _ η N hN hind`. Take `⟨S, hS⟩` from `sinSupp ℤ_[l] ι (fun i => (η i : ℤ_[l])) N`. Take `⟨n₀, hn₀⟩` from `sep l S`. Use `⟨n₀, fun n hn k _ P α h1 h2 => ?_⟩` and prove the remaining obligations. Establish `hl : l.Prime` using `Fact.out`.

Use `haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.ne_zero⟩`. Establish `h3` using `sinFin k ι (l ^ n) (fun i => redU l n (η i)) N P α h1 h2`. Establish `h4` using `sinMap k ℤ_[l] (ZMod (l ^ n)) ι (PadicInt.toZModPow n : ℤ_[l] →+* ZMod (l ^ n)).toAddMonoidHom (fun i => (η i : ℤ_[l])) N P`. Establish `h5 : AddMonoidAlgebra.mapDomainRingHom k (PadicInt.toZModPow n : ℤ_[l] →+* ZMod (l ^ n)).toAddMonoidHom (sinE (fun i => (η i : ℤ_[l])) N P) = 0` using `h4.trans h3`. Establish `h6 : Finsupp.mapDomain (PadicInt.toZModPow n : ℤ_[l] → ZMod (l ^ n)) (sinE (fun i => (η i : ℤ_[l])) N P).coeff = 0`.

Use `congrArg AddMonoidAlgebra.coeff h5` as an intermediate fact. Simplify using `using this`. Establish `h7 : (sinE (fun i => (η i : ℤ_[l])) N P).coeff = 0`. Apply `Finsupp.mapDomain_injOn (S : Set ℤ_[l]) (hn₀ n hn)` to reduce the goal to its premises. Introduce `a ha`.

Conclude with `hS k P a (Finsupp.mem_support_iff.mp ha)`. Simplify using the standard rewrite rules. Simplify using `using h6`. Use `sinLem k ℤ_[l] ι (fun i => (η i : ℤ_[l])) N P hN ?_ ?_ ?_` and prove the remaining obligations. Introduce `i m hm`.

Simplify using `only [zsmul_eq_mul] at hm`. Use `(Units.mul_left_eq_zero (η i)).mp hm` as an intermediate fact. Conclude with `this` after adjusting the coercions. Introduce `i j hij a b hab`. Simplify using `only [zsmul_eq_mul] at hab`.

Conclude with `hind i j hij a b hab`. Use extensionality with `a`. Simplify using `[h7]`.
-/
theorem UpperTheory.V.FW.sinnott :
    ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [Nonempty ι] (η : ι → ℤ_[l]ˣ) (N : ℕ), N ≠ 0 → (∀ i j, i ≠ j → ∀ a b : ℤ, (a : ℤ_[l]) * η i = (b : ℤ_[l]) * η j → a = 0) → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ (k : Type) [CommRing k] (P : ℕ → k) (α : ZMod (l ^ n) → k), (∀ y, α y - α (y - N) = ∑ s ∈ Finset.range N, if (s : ZMod (l ^ n)) = y then P s else 0) → (∀ y, ∑ i, α (((redU l n (η i))⁻¹ : (ZMod (l ^ n))ˣ) * y) = 0) → ∀ s < N, P s = 0 := by
  intro l _ ι _ _ η N hN hind
  classical
  obtain ⟨S, hS⟩ := sinSupp ℤ_[l] ι (fun i => (η i : ℤ_[l])) N
  obtain ⟨n₀, hn₀⟩ := sep l S
  refine ⟨n₀, fun n hn k _ P α h1 h2 => ?_⟩
  have hl : l.Prime := Fact.out
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have h3 := sinFin k ι (l ^ n) (fun i => redU l n (η i)) N P α h1 h2
  have h4 := sinMap k ℤ_[l] (ZMod (l ^ n)) ι
    (PadicInt.toZModPow n : ℤ_[l] →+* ZMod (l ^ n)).toAddMonoidHom (fun i => (η i : ℤ_[l])) N P
  have h5 : AddMonoidAlgebra.mapDomainRingHom k
      (PadicInt.toZModPow n : ℤ_[l] →+* ZMod (l ^ n)).toAddMonoidHom
      (sinE (fun i => (η i : ℤ_[l])) N P) = 0 := h4.trans h3
  have h6 : Finsupp.mapDomain (PadicInt.toZModPow n : ℤ_[l] → ZMod (l ^ n))
      (sinE (fun i => (η i : ℤ_[l])) N P).coeff = 0 := by
    have := congrArg AddMonoidAlgebra.coeff h5
    simpa using this
  have h7 : (sinE (fun i => (η i : ℤ_[l])) N P).coeff = 0 := by
    apply Finsupp.mapDomain_injOn (S : Set ℤ_[l]) (hn₀ n hn)
    · intro a ha
      exact hS k P a (Finsupp.mem_support_iff.mp ha)
    · simp
    · simpa using h6
  refine sinLem k ℤ_[l] ι (fun i => (η i : ℤ_[l])) N P hN ?_ ?_ ?_
  · intro i m hm
    simp only [zsmul_eq_mul] at hm
    have := (Units.mul_left_eq_zero (η i)).mp hm
    exact_mod_cast this
  · intro i j hij a b hab
    simp only [zsmul_eq_mul] at hab
    exact hind i j hij a b hab
  · ext a
    simp [h7]
