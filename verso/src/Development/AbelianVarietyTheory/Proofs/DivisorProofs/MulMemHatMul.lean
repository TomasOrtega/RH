import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApprox
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorFixesCosetVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction

namespace GlobalTheory.HatProductMembership

open NumberField Formalism.BasicNotions Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.FunObj.SqNum

/- English proof (translation)
Unfold `hatId at hx hy ⊢`. Proceed by induction on `hx using AddSubgroup.closure_induction with`. Consider the case `mem a ha`. Take `⟨u, hu, s, hs, rfl⟩` from `ha`. Proceed by induction on `hy using AddSubgroup.closure_induction with`.

Consider the case `mem b hb`. Take `⟨v, hv, t, ht, rfl⟩` from `hb`. Use `AddSubgroup.subset_closure ⟨u * v, Ideal.mul_mem_mul hu hv, s * t, (OhE D).mul_mem hs ht, ?_⟩` and prove the remaining obligations. Establish `h : ((u * v : 𝓞 D.host.E) : D.host.E) = (u : D.host.E) * (v : D.host.E)` using `rfl`. Rewrite using `[h, map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `zero => rw [mul_zero]`. Conclude with `zero_mem _`. Consider the case `add b c _ _ h1 h2 => rw [mul_add]`. Conclude with `add_mem h1 h2`.

Consider the case `neg b _ h => rw [mul_neg]`. Conclude with `neg_mem h`. Consider the case `zero => rw [zero_mul]`. Conclude with `zero_mem _`. Consider the case `add a b _ _ h1 h2 => rw [add_mul]`.

Conclude with `add_mem h1 h2`. Consider the case `neg a _ h => rw [neg_mul]`. Conclude with `neg_mem h`.
-/
theorem mul_mem_hat_mul {D : D7} {I J : Ideal (𝓞 D.host.E)} {x y : AE D}
    (hx : x ∈ hatId D I) (hy : y ∈ hatId D J) : x * y ∈ hatId D (I * J) := by
  unfold hatId at hx hy ⊢
  induction hx using AddSubgroup.closure_induction with
  | mem a ha =>
    obtain ⟨u, hu, s, hs, rfl⟩ := ha
    induction hy using AddSubgroup.closure_induction with
    | mem b hb =>
      obtain ⟨v, hv, t, ht, rfl⟩ := hb
      refine AddSubgroup.subset_closure
        ⟨u * v, Ideal.mul_mem_mul hu hv, s * t, (OhE D).mul_mem hs ht, ?_⟩
      have h : ((u * v : 𝓞 D.host.E) : D.host.E) = (u : D.host.E) * (v : D.host.E) := rfl
      rw [h, map_mul]
      ring
    | zero => rw [mul_zero]; exact zero_mem _
    | add b c _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
    | neg b _ h => rw [mul_neg]; exact neg_mem h
  | zero => rw [zero_mul]; exact zero_mem _
  | add a b _ _ h1 h2 => rw [add_mul]; exact add_mem h1 h2
  | neg a _ h => rw [neg_mul]; exact neg_mem h

end GlobalTheory.HatProductMembership
