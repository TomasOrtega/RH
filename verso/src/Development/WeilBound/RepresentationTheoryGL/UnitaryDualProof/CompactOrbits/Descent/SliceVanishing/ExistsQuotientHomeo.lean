import Mathlib

noncomputable section

namespace PositivityTheory.RgUd.T.Desc.SLF

open MulAction

variable {G T : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SigmaCompactSpace G]
  [TopologicalSpace T] [T2Space T] [BaireSpace T] [MulAction G T] [ContinuousSMul G T] [IsPretransitive G T]

/- English proof (translation)
Set `f : G ⧸ stabilizer G t → T` to `ofQuotientStabilizer G t`. Establish `hinj : Function.Injective f` using `injective_ofQuotientStabilizer G t`. Establish `hsurj : Function.Surjective f`. Introduce `y`. Take `⟨g, hg⟩` from `exists_smul_eq G t y`.

Conclude with `⟨(g : G ⧸ stabilizer G t), by simp [f, hg]⟩`. Establish `hmk : ∀ g : G, f (g : G ⧸ stabilizer G t) = g • t` using `fun g => ofQuotientStabilizer_mk G t g`. Establish `hcont : Continuous f`. Rewrite using `[(QuotientGroup.isQuotientMap_mk (stabilizer G t)).continuous_iff]`. Establish `: f ∘ (QuotientGroup.mk : G → G ⧸ stabilizer G t) = fun g => g • t` using `funext hmk`.

Rewrite using `[this]`. Conclude with `continuous_id.smul continuous_const`. Establish `hopen : IsOpenMap f`. Introduce `U hU`. Establish `: f '' U = (fun g : G => g • t) '' ((QuotientGroup.mk : G → G ⧸ stabilizer G t) ⁻¹' U)`.

Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc, rfl⟩`. Take `⟨g, rfl⟩` from `QuotientGroup.mk_surjective c`. Conclude with `⟨g, hc, (hmk g).symm⟩`.

Introduce and unpack `⟨g, hg, rfl⟩`. Conclude with `⟨_, hg, hmk g⟩`. Rewrite using `[this]`. Conclude with `isOpenMap_smul_of_sigmaCompact t _ (hU.preimage QuotientGroup.continuous_mk)`. Conclude with `⟨(Equiv.ofBijective f ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen hcont hopen, hmk⟩`.
-/
theorem exists_quotient_homeo (t : T) :
    ∃ e : G ⧸ stabilizer G t ≃ₜ T, ∀ g : G, e (g : G ⧸ stabilizer G t) = g • t := by
  let f : G ⧸ stabilizer G t → T := ofQuotientStabilizer G t
  have hinj : Function.Injective f := injective_ofQuotientStabilizer G t
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨g, hg⟩ := exists_smul_eq G t y
    exact ⟨(g : G ⧸ stabilizer G t), by simp [f, hg]⟩
  have hmk : ∀ g : G, f (g : G ⧸ stabilizer G t) = g • t := fun g => ofQuotientStabilizer_mk G t g
  have hcont : Continuous f := by
    rw [(QuotientGroup.isQuotientMap_mk (stabilizer G t)).continuous_iff]
    have : f ∘ (QuotientGroup.mk : G → G ⧸ stabilizer G t) = fun g => g • t := funext hmk
    rw [this]
    exact continuous_id.smul continuous_const
  have hopen : IsOpenMap f := by
    intro U hU
    have : f '' U = (fun g : G => g • t) '' ((QuotientGroup.mk : G → G ⧸ stabilizer G t) ⁻¹' U) := by
      ext y
      constructor
      · rintro ⟨c, hc, rfl⟩
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
        exact ⟨g, hc, (hmk g).symm⟩
      · rintro ⟨g, hg, rfl⟩
        exact ⟨_, hg, hmk g⟩
    rw [this]
    exact isOpenMap_smul_of_sigmaCompact t _ (hU.preimage QuotientGroup.continuous_mk)
  exact ⟨(Equiv.ofBijective f ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen hcont hopen, hmk⟩

end PositivityTheory.RgUd.T.Desc.SLF
