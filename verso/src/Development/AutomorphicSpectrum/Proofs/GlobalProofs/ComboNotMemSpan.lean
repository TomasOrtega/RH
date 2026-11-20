import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CongSubgroup
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.StellarLI

/- English proof (translation)
Introduce `h`. Apply `hp` to reduce the goal to its premises. Establish `h1 : a • p ∈ Submodule.span ℚ s`. Use `Submodule.sub_mem _ h (Submodule.smul_mem _ b hq)` as an intermediate fact. Simplify using `using this`.

Establish `h2` using `Submodule.smul_mem _ a⁻¹ h1`. Rewrite `h2` using `[smul_smul, inv_mul_cancel₀ ha, one_smul]`. Then use the resulting hypothesis.
-/
theorem combo_notMem_span {V : Type} [AddCommGroup V] [Module ℚ V] {s : Set V} {p q : V} {a b : ℚ}
    (ha : a ≠ 0) (hp : p ∉ Submodule.span ℚ s) (hq : q ∈ Submodule.span ℚ s) :
    a • p + b • q ∉ Submodule.span ℚ s := by
  intro h
  apply hp
  have h1 : a • p ∈ Submodule.span ℚ s := by
    have := Submodule.sub_mem _ h (Submodule.smul_mem _ b hq)
    simpa using this
  have h2 := Submodule.smul_mem _ a⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at h2

/- English proof (translation)
Introduce `V _ _ _ p q r a b ha hb hpq hpr hqr hli`. Simplify using `only [Finset.coe_insert] at hli ⊢`. Establish `hp' : p ∉ insert q (r : Set V)` using `by simp [hpq, hpr]`. Establish `hq' : q ∉ (r : Set V)` using `by simpa using hqr`. Establish `hq'' : q ∉ insert p (r : Set V)` using `by simp [hpq.symm, hqr]`.

Take `⟨hli1, hpn⟩` from `(linearIndepOn_id_insert hp').mp hli`. Take `⟨hliR, -⟩` from `(linearIndepOn_id_insert hq').mp hli1`. Establish `hli' : LinearIndepOn ℚ id (insert q (insert p (r : Set V)))` using `by rwa [Set.insert_comm]`. Take `⟨hli2, hqn2⟩` from `(linearIndepOn_id_insert hq'').mp hli'`. Establish `hw1 : a • p + b • q ∉ Submodule.span ℚ (insert q (r : Set V))` using `combo_notMem_span ha.ne' hpn (Submodule.subset_span (Set.mem_insert q _))`.

Establish `hw2 : a • p + b • q ∉ Submodule.span ℚ (insert p (r : Set V))`. Rewrite using `[add_comm]`. Conclude with `combo_notMem_span hb.ne' hqn2 (Submodule.subset_span (Set.mem_insert p _))`. Establish `hw3 : a • p + b • q ∉ Submodule.span ℚ (r : Set V)` using `fun h => hw1 (Submodule.span_mono (Set.subset_insert q _) h)`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `h`. Conclude with `hw3 (Submodule.subset_span (Finset.mem_coe.mpr h))`. Introduce `h`. Conclude with `hw2 (by rw [h]; exact Submodule.subset_span (Set.mem_insert p _))`. Introduce `h`.

Conclude with `hw1 (by rw [h]; exact Submodule.subset_span (Set.mem_insert q _))`. Conclude with `(linearIndepOn_id_insert fun h => hw1 (Submodule.subset_span h)).mpr ⟨hli1, hw1⟩`. Rewrite using `[Set.insert_comm]`. Conclude with `(linearIndepOn_id_insert fun h => hw2 (Submodule.subset_span h)).mpr ⟨hli2, hw2⟩`. Conclude with `(linearIndepOn_id_insert fun h => hw3 (Submodule.subset_span h)).mpr ⟨hliR, hw3⟩`.
-/
theorem main : ∀ {V : Type} [AddCommGroup V] [Module ℚ V] [DecidableEq V] (p q : V) (r : Finset V) (a b : ℚ), 0 < a → 0 < b → p ≠ q → p ∉ r → q ∉ r →
  LinearIndepOn ℚ id ((insert p (insert q r) : Finset V) : Set V) →
  (a • p + b • q) ∉ r ∧ (a • p + b • q) ≠ p ∧ (a • p + b • q) ≠ q ∧
  LinearIndepOn ℚ id ((insert (a • p + b • q) (insert q r) : Finset V) : Set V) ∧
  LinearIndepOn ℚ id ((insert p (insert (a • p + b • q) r) : Finset V) : Set V) ∧
  LinearIndepOn ℚ id ((insert (a • p + b • q) r : Finset V) : Set V) := by
  intro V _ _ _ p q r a b ha hb hpq hpr hqr hli
  simp only [Finset.coe_insert] at hli ⊢
  have hp' : p ∉ insert q (r : Set V) := by simp [hpq, hpr]
  have hq' : q ∉ (r : Set V) := by simpa using hqr
  have hq'' : q ∉ insert p (r : Set V) := by simp [hpq.symm, hqr]
  obtain ⟨hli1, hpn⟩ := (linearIndepOn_id_insert hp').mp hli
  obtain ⟨hliR, -⟩ := (linearIndepOn_id_insert hq').mp hli1
  have hli' : LinearIndepOn ℚ id (insert q (insert p (r : Set V))) := by rwa [Set.insert_comm]
  obtain ⟨hli2, hqn2⟩ := (linearIndepOn_id_insert hq'').mp hli'
  have hw1 : a • p + b • q ∉ Submodule.span ℚ (insert q (r : Set V)) :=
    combo_notMem_span ha.ne' hpn (Submodule.subset_span (Set.mem_insert q _))
  have hw2 : a • p + b • q ∉ Submodule.span ℚ (insert p (r : Set V)) := by
    rw [add_comm]
    exact combo_notMem_span hb.ne' hqn2 (Submodule.subset_span (Set.mem_insert p _))
  have hw3 : a • p + b • q ∉ Submodule.span ℚ (r : Set V) := fun h =>
    hw1 (Submodule.span_mono (Set.subset_insert q _) h)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hw3 (Submodule.subset_span (Finset.mem_coe.mpr h))
  · intro h
    exact hw2 (by rw [h]; exact Submodule.subset_span (Set.mem_insert p _))
  · intro h
    exact hw1 (by rw [h]; exact Submodule.subset_span (Set.mem_insert q _))
  · exact (linearIndepOn_id_insert fun h => hw1 (Submodule.subset_span h)).mpr ⟨hli1, hw1⟩
  · rw [Set.insert_comm]
    exact (linearIndepOn_id_insert fun h => hw2 (Submodule.subset_span h)).mpr ⟨hli2, hw2⟩
  · exact (linearIndepOn_id_insert fun h => hw3 (Submodule.subset_span h)).mpr ⟨hliR, hw3⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.StellarLI
