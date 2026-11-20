import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit

open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatVal

variable {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem f_mem_IB : f ξ ∈ Lat.IB f ξ := Ideal.subset_span (Set.mem_singleton _)

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem η_mem_IB : Lat.η f ξ l M ∈ Lat.IB f ξ := by
  unfold Lat.η
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_left _ _ (f_mem_IB f ξ)

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem dpE_succ_mem_IB (i : ℕ) : Lat.dpE f ξ l M (i + 1) ∈ Lat.IB f ξ := by
  unfold Lat.dpE
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ (η_mem_IB f ξ l M) _ (Nat.succ_pos i))

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem dpE_zero_eq : Lat.dpE f ξ l M 0 = 1 := by simp [Lat.dpE]

/- English proof (translation)
Replace the relevant objects with their definitions. Proceed by induction. Treat this case separately. Separate the alternatives or extract the components of the hypothesis. Supply the required witnesses or components.

Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately.

Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Treat this case separately. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Treat this case separately. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem exists_rep_B (x : B) (hx : x ∈ Lat.sub f ξ l M) : ∃ a : W, x - f a ∈ Lat.IB f ξ := by
  unfold Lat.sub at hx
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨w, rfl⟩ | ⟨i, rfl⟩
    · exact ⟨w, by simp⟩
    · cases i with
      | zero => exact ⟨1, by simp [dpE_zero_eq]⟩
      | succ i => exact ⟨0, by simpa using dpE_succ_mem_IB f ξ l M i⟩
  | zero => exact ⟨0, by simp⟩
  | one => exact ⟨1, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    have h := Ideal.add_mem _ ha hb
    have e : x + y - f (a + b) = x - f a + (y - f b) := by rw [map_add]; ring
    rw [e]; exact h
  | neg x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨-a, ?_⟩
    have h := Ideal.neg_mem_iff _ |>.2 ha
    have e : -x - f (-a) = -(x - f a) := by rw [map_neg]; ring
    rw [e]; exact h
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a * b, ?_⟩
    have h := Ideal.add_mem _ (Ideal.mul_mem_right y _ ha) (Ideal.mul_mem_left _ (f a) hb)
    have e : x * y - f (a * b) = (x - f a) * y + f a * (y - f b) := by rw [map_mul]; ring
    rw [e]; exact h

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem exists_rep (x : Lat.A f ξ l M) : ∃ a : W, Lat.ι f ξ l M x - f a ∈ Lat.IB f ξ :=
  exists_rep_B f ξ l M _ x.2

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem mem_of_dvd {a b : W} {x y : Lat.A f ξ l M}
    (hx : Lat.ι f ξ l M x - f a ∈ Lat.IB f ξ) (hy : Lat.ι f ξ l M y - f b ∈ Lat.IB f ξ)
    (h : Ideal.Quotient.mk (Ideal.span {ξ}) a ∣ Ideal.Quotient.mk (Ideal.span {ξ}) b) :
    y ∈ Ideal.span {x} ⊔ Lat.I f ξ l M := by
  obtain ⟨c', hc⟩ := h
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c'
  rw [← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hc
  obtain ⟨d, hd⟩ := hc
  have hI : y - Lat.ofW f ξ l M c * x ∈ Lat.I f ξ l M := by
    show Lat.ι f ξ l M (y - Lat.ofW f ξ l M c * x) ∈ Lat.IB f ξ
    have h1 : f (b - a * c) ∈ Lat.IB f ξ := by
      rw [hd, map_mul]; exact Ideal.mul_mem_right _ _ (f_mem_IB f ξ)
    have h2 := Ideal.add_mem _ (Ideal.sub_mem _ hy (Ideal.mul_mem_left _ (f c) hx)) h1
    have e : Lat.ι f ξ l M (y - Lat.ofW f ξ l M c * x)
        = Lat.ι f ξ l M y - f b - f c * (Lat.ι f ξ l M x - f a) + f (b - a * c) := by
      rw [map_sub, map_mul, Lat.ι_ofW, map_sub, map_mul]; ring
    rw [e]; exact h2
  have hs : Lat.ofW f ξ l M c * x ∈ Ideal.span {x} :=
    Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))
  have e : y = Lat.ofW f ξ l M c * x + (y - Lat.ofW f ξ l M c * x) := by ring
  rw [e]
  exact Submodule.add_mem_sup hs hI

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Separate the alternatives or extract the components of the hypothesis. Prove the second alternative.

Prove the first alternative.
-/
theorem val : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ),
    Lat.Hyp f ξ l m → ∀ x y : Lat.A f ξ l M,
      x ∈ Ideal.span {y} ⊔ Lat.I f ξ l M ∨ y ∈ Ideal.span {x} ⊔ Lat.I f ξ l M := by
  intro W B _ _ _ f ξ l M m h x y
  obtain ⟨a, ha⟩ := exists_rep f ξ l M x
  obtain ⟨b, hb⟩ := exists_rep f ξ l M y
  rcases h.val (Ideal.Quotient.mk _ a) (Ideal.Quotient.mk _ b) with hd | hd
  · exact Or.inr (mem_of_dvd f ξ l M ha hb hd)
  · exact Or.inl (mem_of_dvd f ξ l M hb ha hd)

end GlobalTheory.CompanionTheory.LatVal
