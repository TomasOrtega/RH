import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.PdMor

/- English proof (translation)
Introduce `S _ S' E E' _ _ _ π π' I I' J J' δ δ' F₀ F hπ hI hP hP' hF₀ hF`. Establish `hmem : ∀ a ∈ J, ∃ x ∈ I, π x = a` using `fun a ha => by`. Rewrite `ha` using `[hP.1]`. Conclude with `(Ideal.mem_map_iff_of_surjective π hπ).mp ha`. Establish `hdp : ∀ (k : ℕ) (x : S), x ∈ I → ∃ y : S, (k.factorial : S) * y = x ^ k`.

Introduce `k x hx`. Break down `Nat.eq_zero_or_pos k with rfl | hk` into its components or cases. Conclude with `⟨1, by simp⟩`. Take `⟨y, -, hy⟩` from `hI x hx k hk.ne'`. Conclude with `⟨y, hy⟩`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `a ha`. Take `⟨x, hx, rfl⟩` from `hmem a ha`. Rewrite using `[Ideal.mem_comap, hF, hP'.1]`.

Conclude with `Ideal.mem_map_of_mem π' (hF₀ x hx)`. Introduce `n a ha`. Take `⟨x, hx, rfl⟩` from `hmem a ha`. Take `⟨y, hy⟩` from `hdp n x hx`. Rewrite using `[hP.2 n x y hx hy, hF, hF, hP'.2 n (F₀ x) (F₀ y) (hF₀ x hx) (by rw [← map_pow, ← hy, map_mul, map_natCast])]`.
-/
theorem isDPMorphism_of_isPd : ∀ {S : Type} [CommRing S] {S' E E' : Type} [CommRing S'] [CommRing E] [CommRing E'] (π : S →+* E) (π' : S' →+* E') (I : Ideal S) (I' : Ideal S') {J : Ideal E} {J' : Ideal E'} (δ : DividedPowers J) (δ' : DividedPowers J') (F₀ : S →+* S') (F : E →+* E'), Function.Surjective π → PdI I → IsPd π I δ → IsPd π' I' δ' → (∀ x ∈ I, F₀ x ∈ I') → (∀ x, F (π x) = π' (F₀ x)) → DividedPowers.IsDPMorphism δ δ' F := by
  intro S _ S' E E' _ _ _ π π' I I' J J' δ δ' F₀ F hπ hI hP hP' hF₀ hF
  have hmem : ∀ a ∈ J, ∃ x ∈ I, π x = a := fun a ha => by
    rw [hP.1] at ha
    exact (Ideal.mem_map_iff_of_surjective π hπ).mp ha
  have hdp : ∀ (k : ℕ) (x : S), x ∈ I → ∃ y : S, (k.factorial : S) * y = x ^ k := by
    intro k x hx
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact ⟨1, by simp⟩
    · obtain ⟨y, -, hy⟩ := hI x hx k hk.ne'
      exact ⟨y, hy⟩
  refine ⟨?_, ?_⟩
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    obtain ⟨x, hx, rfl⟩ := hmem a ha
    rw [Ideal.mem_comap, hF, hP'.1]
    exact Ideal.mem_map_of_mem π' (hF₀ x hx)
  · intro n a ha
    obtain ⟨x, hx, rfl⟩ := hmem a ha
    obtain ⟨y, hy⟩ := hdp n x hx
    rw [hP.2 n x y hx hy, hF, hF,
      hP'.2 n (F₀ x) (F₀ y) (hF₀ x hx) (by rw [← map_pow, ← hy, map_mul, map_natCast])]

end GlobalTheory.CompanionTheory.PdMor
