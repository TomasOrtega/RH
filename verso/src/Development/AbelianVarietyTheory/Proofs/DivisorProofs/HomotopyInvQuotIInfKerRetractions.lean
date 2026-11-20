import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLtTopOfEssFiniteType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfRingEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfSubsingletonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfClosedCoverStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `q _ D T E _ _ _ _ _ _ _ _ _ hq hT hlow ι X`. Proceed by induction on `X using Finset.induction_on with`. Consider the case `empty`. Introduce `_`. Apply `GlobalTheory.T.etaleHomotopyInvariantTwists_of_subsingleton` to reduce the goal to its premises.

Rewrite using `[Ideal.Quotient.subsingleton_iff]`. Simplify using the standard rewrite rules. Consider the case `@insert χ Y hχY ih`. Introduce `hX`. Establish `hχ : χ.comp ι = AlgHom.id D T` using `hX χ (Finset.mem_insert_self _ _)`.

Establish `ih'` using `ih (fun ψ hψ => hX ψ (Finset.mem_insert_of_mem hψ))`. Establish `hχι : ∀ t, χ (ι t) = t` using `fun t => by`. Simplify using `using DFunLike.congr_fun hχ t`. Establish `hins : (⨅ ψ ∈ insert χ Y, RingHom.ker ψ) = RingHom.ker χ ⊓ ⨅ ψ ∈ Y, RingHom.ker ψ`. Rewrite using `[Finset.iInf_insert]`.

Rewrite using `[hins]`. Use `set P : Ideal E := RingHom.ker χ with hPdef`. Use `set I : Ideal E := ⨅ ψ ∈ Y, RingHom.ker ψ with hIdef`. Distinguish the cases in `hIP : I ≤ P`. Rewrite using `[inf_eq_right.mpr hIP]`.

Conclude with `ih'`. Take `⟨y, hyI, hyP⟩` from `Set.not_subset.mp hIP`. Establish `hy0 : χ y ≠ 0` using `fun h => hyP (RingHom.mem_ker.mpr h)`. Establish `hint : IsIntegral D (χ y)` using `Algebra.IsIntegral.isIntegral _`. Establish `hne` using `Ideal.comap_ne_bot_of_integral_mem hy0 (Ideal.mem_span_singleton_self (χ y)) hint`.

Take `⟨s, hsmem, hs0⟩` from `Submodule.ne_bot_iff _ |>.mp hne`. Rewrite `hsmem` using `[Ideal.mem_comap, Ideal.mem_span_singleton']`. Take `⟨u, hu⟩` from `hsmem`. Establish `hsPI : algebraMap D E s ∈ P ⊔ I`. Establish `h1 : algebraMap D E s - ι u * y ∈ P`.

Rewrite using `[hPdef, RingHom.mem_ker, map_sub, map_mul, AlgHom.commutes, hχι, hu, sub_self]`. Establish `h2 : ι u * y ∈ I` using `Ideal.mul_mem_left _ _ hyI`. Establish `: algebraMap D E s = (algebraMap D E s - ι u * y) + ι u * y` using `by ring`. Rewrite using `[this]`. Conclude with `Ideal.add_mem _ (Ideal.mem_sup_left h1) (Ideal.mem_sup_right h2)`.

Use `set J : Ideal E := P ⊓ I with hJ`. Establish `hJP : J ≤ P` using `inf_le_left`. Establish `hJI : J ≤ I` using `inf_le_right`. Apply `GlobalTheory.T.etaleHomotopyInvariantTwists_of_closedCover q (E ⧸ J) (P.map (Ideal.Quotient.mk J)) (I.map (Ideal.Quotient.mk J))` to reduce the goal to its premises. Introduce `x hx`.

Take `⟨e, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Establish `h1` using `(Ideal.mem_quotient_iff_mem hJP).mp hx.1`. Establish `h2` using `(Ideal.mem_quotient_iff_mem hJI).mp hx.2`. Establish `: Ideal.Quotient.mk J e = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr ⟨h1, h2⟩`. Rewrite using `[this]`.

Conclude with `zero_mem _`. Use `hq.map (algebraMap D (E ⧸ J))` as an intermediate fact. Simplify using `using this`. Establish `hsurj : Function.Surjective χ` using `fun t => ⟨ι t, hχι t⟩`. Establish `e1` using `DoubleQuot.quotQuotEquivQuotOfLE hJP`.

Establish `e2` using `(Ideal.quotientKerAlgEquivOfSurjective hsurj).toRingEquiv`. Conclude with `GlobalTheory.T.etaleHomotopyInvariantTwists_of_ringEquiv q T _ (e1.trans e2).symm hT`. Conclude with `GlobalTheory.T.etaleHomotopyInvariantTwists_of_ringEquiv q _ _ (DoubleQuot.quotQuotEquivQuotOfLE hJI).symm ih'`. Apply `hlow _ s hs0` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk _ (Ideal.Quotient.mk J (algebraMap D E s)) = 0`.

Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, ← Ideal.map_sup]`. Conclude with `Ideal.mem_map_of_mem _ hsPI`.
-/
theorem homotopyInv_quot_iInf_ker_retractions : ∀ (q : ℕ) [NeZero q] (D T E : Type) [CommRing D] [IsDomain D] [CommRing T] [IsDomain T] [Algebra D T] [Algebra.IsIntegral D T] [CommRing E] [Algebra D E] [Algebra.IsIntegral D E], IsUnit (q : D) → HInv q T → (∀ (E' : Type) [CommRing E'] [Algebra D E'] [Algebra.IsIntegral D E'] (s : D), s ≠ 0 → algebraMap D E' s = 0 → HInv q E') → ∀ (ι : T →ₐ[D] E) (X : Finset (E →ₐ[D] T)), (∀ χ ∈ X, χ.comp ι = AlgHom.id D T) → HInv q (E ⧸ ⨅ χ ∈ X, RingHom.ker χ) := by
  intro q _ D T E _ _ _ _ _ _ _ _ _ hq hT hlow ι X
  classical
  induction X using Finset.induction_on with
  | empty =>
    intro _
    apply GlobalTheory.T.etaleHomotopyInvariantTwists_of_subsingleton
    rw [Ideal.Quotient.subsingleton_iff]
    simp
  | @insert χ Y hχY ih =>
    intro hX
    have hχ : χ.comp ι = AlgHom.id D T := hX χ (Finset.mem_insert_self _ _)
    have ih' := ih (fun ψ hψ => hX ψ (Finset.mem_insert_of_mem hψ))
    have hχι : ∀ t, χ (ι t) = t := fun t => by
      simpa using DFunLike.congr_fun hχ t
    have hins : (⨅ ψ ∈ insert χ Y, RingHom.ker ψ) = RingHom.ker χ ⊓ ⨅ ψ ∈ Y, RingHom.ker ψ := by
      rw [Finset.iInf_insert]
    rw [hins]
    set P : Ideal E := RingHom.ker χ with hPdef
    set I : Ideal E := ⨅ ψ ∈ Y, RingHom.ker ψ with hIdef
    by_cases hIP : I ≤ P
    · rw [inf_eq_right.mpr hIP]; exact ih'
    · obtain ⟨y, hyI, hyP⟩ := Set.not_subset.mp hIP
      have hy0 : χ y ≠ 0 := fun h => hyP (RingHom.mem_ker.mpr h)
      have hint : IsIntegral D (χ y) := Algebra.IsIntegral.isIntegral _
      have hne := Ideal.comap_ne_bot_of_integral_mem hy0 (Ideal.mem_span_singleton_self (χ y)) hint
      obtain ⟨s, hsmem, hs0⟩ := Submodule.ne_bot_iff _ |>.mp hne
      rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hsmem
      obtain ⟨u, hu⟩ := hsmem
      have hsPI : algebraMap D E s ∈ P ⊔ I := by
        have h1 : algebraMap D E s - ι u * y ∈ P := by
          rw [hPdef, RingHom.mem_ker, map_sub, map_mul, AlgHom.commutes, hχι, hu, sub_self]
        have h2 : ι u * y ∈ I := Ideal.mul_mem_left _ _ hyI
        have : algebraMap D E s = (algebraMap D E s - ι u * y) + ι u * y := by ring
        rw [this]
        exact Ideal.add_mem _ (Ideal.mem_sup_left h1) (Ideal.mem_sup_right h2)
      set J : Ideal E := P ⊓ I with hJ
      have hJP : J ≤ P := inf_le_left
      have hJI : J ≤ I := inf_le_right
      apply GlobalTheory.T.etaleHomotopyInvariantTwists_of_closedCover q (E ⧸ J) (P.map (Ideal.Quotient.mk J)) (I.map (Ideal.Quotient.mk J))
      · intro x hx
        obtain ⟨e, rfl⟩ := Ideal.Quotient.mk_surjective x
        have h1 := (Ideal.mem_quotient_iff_mem hJP).mp hx.1
        have h2 := (Ideal.mem_quotient_iff_mem hJI).mp hx.2
        have : Ideal.Quotient.mk J e = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ⟨h1, h2⟩
        rw [this]; exact zero_mem _
      · have := hq.map (algebraMap D (E ⧸ J))
        simpa using this
      · have hsurj : Function.Surjective χ := fun t => ⟨ι t, hχι t⟩
        have e1 := DoubleQuot.quotQuotEquivQuotOfLE hJP
        have e2 := (Ideal.quotientKerAlgEquivOfSurjective hsurj).toRingEquiv
        exact GlobalTheory.T.etaleHomotopyInvariantTwists_of_ringEquiv q T _ (e1.trans e2).symm hT
      · exact GlobalTheory.T.etaleHomotopyInvariantTwists_of_ringEquiv q _ _ (DoubleQuot.quotQuotEquivQuotOfLE hJI).symm ih'
      · apply hlow _ s hs0
        change Ideal.Quotient.mk _ (Ideal.Quotient.mk J (algebraMap D E s)) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem, ← Ideal.map_sup]
        exact Ideal.mem_map_of_mem _ hsPI

end GlobalTheory
