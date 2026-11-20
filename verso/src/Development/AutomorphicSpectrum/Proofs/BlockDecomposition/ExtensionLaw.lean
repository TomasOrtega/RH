import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionLawHolds

noncomputable section

open PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEisExt

variable {G : Type} [Group G]

/- English proof (translation)
Establish `hex : ∃ c : K, p * k * (c : G)⁻¹ ∈ P` using `⟨⟨k, hk⟩, by simpa using hp⟩`. Rewrite using `[PositivityTheory.RgEis.ext, dif_pos hex]`. Establish `hcP : p * k * (hex.choose : G)⁻¹ ∈ P` using `hex.choose_spec`. Establish `hq : p⁻¹ * (p * k * (hex.choose : G)⁻¹) ∈ P` using `P.mul_mem (P.inv_mem hp) hcP`. Establish `hqK : p⁻¹ * (p * k * (hex.choose : G)⁻¹) ∈ K`.

Establish `he : p⁻¹ * (p * k * (hex.choose : G)⁻¹) = k * (hex.choose : G)⁻¹` using `by group`. Rewrite using `[he]`. Conclude with `K.mul_mem hk (K.inv_mem hex.choose.2)`. Establish `h0` using `hfK _ hq hqK`. Establish `hsplit` using `hadd p hp _ hq`.

Rewrite `hsplit` using `[mul_inv_cancel_left]`. Rewrite using `[hsplit, h0, add_zero]`.
-/
theorem ext_mul {K P : Subgroup G} {f : G → ℝ} (hadd : ∀ p ∈ P, ∀ q ∈ P, f (p * q) = f p + f q)
    (hfK : ∀ p ∈ P, p ∈ K → f p = 0) {p k : G} (hp : p ∈ P) (hk : k ∈ K) :
    PositivityTheory.RgEis.ext K P f (p * k) = f p := by
  have hex : ∃ c : K, p * k * (c : G)⁻¹ ∈ P := ⟨⟨k, hk⟩, by simpa using hp⟩
  rw [PositivityTheory.RgEis.ext, dif_pos hex]
  have hcP : p * k * (hex.choose : G)⁻¹ ∈ P := hex.choose_spec
  have hq : p⁻¹ * (p * k * (hex.choose : G)⁻¹) ∈ P := P.mul_mem (P.inv_mem hp) hcP
  have hqK : p⁻¹ * (p * k * (hex.choose : G)⁻¹) ∈ K := by
    have he : p⁻¹ * (p * k * (hex.choose : G)⁻¹) = k * (hex.choose : G)⁻¹ := by group
    rw [he]
    exact K.mul_mem hk (K.inv_mem hex.choose.2)
  have h0 := hfK _ hq hqK
  have hsplit := hadd p hp _ hq
  rw [mul_inv_cancel_left] at hsplit
  rw [hsplit, h0, add_zero]

/- English proof (translation)
Introduce `G _ _ _ _ Γ K P f hK hP hIwa hadd hfc hfK hfΓ`. Establish `hval : ∀ p ∈ P, ∀ k ∈ K, PositivityTheory.RgEis.ext K P f (p * k) = f p` using `fun p hp k hk => ext_mul hadd hfK hp hk`. Establish `hone : ∀ p ∈ P, PositivityTheory.RgEis.ext K P f p = f p`. Introduce `p hp`. Simplify using `using hval p hp 1 K.one_mem`.

Use `⟨⟨?_, ?_, ?_, ?_⟩, hval⟩` and prove the remaining obligations. Introduce `p hp g`. Take `⟨q, hq, k, hk, rfl⟩` from `hIwa g`. Rewrite using `[← mul_assoc, hval _ (P.mul_mem hp hq) k hk, hval q hq k hk, hone p hp, hadd p hp q hq]`. Introduce `g k hk`.

Take `⟨q, hq, k', hk', rfl⟩` from `hIwa g`. Rewrite using `[mul_assoc, hval q hq _ (K.mul_mem hk' hk), hval q hq k' hk']`. Introduce `γ hγ hγP`. Rewrite using `[hone γ hγP]`. Conclude with `hfΓ γ hγP hγ`.

Use `open Pointwise in`. Rewrite using `[continuous_iff_isClosed]`. Introduce `C hC`. Establish `hset : PositivityTheory.RgEis.ext K P f ⁻¹' C = ((P : Set G) ∩ f ⁻¹' C) * (K : Set G)`. Use extensionality with `g`.

Prove the components needed by the constructor for the conclusion. Introduce `hg`. Take `⟨q, hq, k, hk, rfl⟩` from `hIwa g`. Establish `hC' : PositivityTheory.RgEis.ext K P f (q * k) ∈ C` using `hg`. Rewrite `hC'` using `[hval q hq k hk]`.

Conclude with `Set.mem_mul.mpr ⟨q, ⟨hq, hC'⟩, k, hk, rfl⟩`. Introduce `hg`. Take `⟨q, ⟨hq, hqC⟩, k, hk, rfl⟩` from `Set.mem_mul.mp hg`. Use `show PositivityTheory.RgEis.ext K P f (q * k) ∈ C`. Rewrite using `[hval q hq k hk]`.

Conclude with `hqC`. Rewrite using `[hset]`. Conclude with `(hfc.preimage_isClosed_of_isClosed hP hC).mul_right_of_isCompact hK`.
-/
theorem extLaw : ExtLaw := by
  intro G _ _ _ _ Γ K P f hK hP hIwa hadd hfc hfK hfΓ
  have hval : ∀ p ∈ P, ∀ k ∈ K, PositivityTheory.RgEis.ext K P f (p * k) = f p :=
    fun p hp k hk => ext_mul hadd hfK hp hk
  have hone : ∀ p ∈ P, PositivityTheory.RgEis.ext K P f p = f p := by
    intro p hp
    simpa using hval p hp 1 K.one_mem
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hval⟩
  · intro p hp g
    obtain ⟨q, hq, k, hk, rfl⟩ := hIwa g
    rw [← mul_assoc, hval _ (P.mul_mem hp hq) k hk, hval q hq k hk, hone p hp, hadd p hp q hq]
  · intro g k hk
    obtain ⟨q, hq, k', hk', rfl⟩ := hIwa g
    rw [mul_assoc, hval q hq _ (K.mul_mem hk' hk), hval q hq k' hk']
  · intro γ hγ hγP
    rw [hone γ hγP]
    exact hfΓ γ hγP hγ
  · open Pointwise in
    · rw [continuous_iff_isClosed]
      intro C hC
      have hset : PositivityTheory.RgEis.ext K P f ⁻¹' C = ((P : Set G) ∩ f ⁻¹' C) * (K : Set G) := by
        ext g
        constructor
        · intro hg
          obtain ⟨q, hq, k, hk, rfl⟩ := hIwa g
          have hC' : PositivityTheory.RgEis.ext K P f (q * k) ∈ C := hg
          rw [hval q hq k hk] at hC'
          exact Set.mem_mul.mpr ⟨q, ⟨hq, hC'⟩, k, hk, rfl⟩
        · intro hg
          obtain ⟨q, ⟨hq, hqC⟩, k, hk, rfl⟩ := Set.mem_mul.mp hg
          show PositivityTheory.RgEis.ext K P f (q * k) ∈ C
          rw [hval q hq k hk]
          exact hqC
      rw [hset]
      exact (hfc.preimage_isClosed_of_isClosed hP hC).mul_right_of_isCompact hK

end GlobalTheory.CompanionTheory.RgEisExt
