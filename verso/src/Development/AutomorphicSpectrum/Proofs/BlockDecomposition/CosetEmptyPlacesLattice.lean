import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetOff
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

namespace GlobalTheory.CompanionTheory.Equi

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Set `J : Ideal (𝓞 F)` to `{ carrier := {s | ∃ y ∈ I, (s : F) * z = y} add_mem' := by`. Introduce and unpack `a b ⟨y₁, hy₁, h₁⟩ ⟨y₂, hy₂, h₂⟩`. Conclude with `⟨y₁ + y₂, I.add_mem hy₁ hy₂, by push_cast; rw [add_mul, h₁, h₂]⟩`.

Use the proof step `zero_mem' := ⟨0, I.zero_mem, by simp⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c a ⟨y, hy, h₁⟩`. Conclude with `⟨c * y, I.mul_mem_left c hy, by rw [smul_eq_mul]; push_cast; rw [mul_assoc, h₁]⟩ }`. Establish `hJ : J = ⊤`.

Assume the negation of the conclusion as `hne`. Take `⟨M, hM, hJM⟩` from `Ideal.exists_le_maximal J hne`. Establish `hM0 : M ≠ ⊥` using `Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField F)`. Establish `hv` using `h ⟨M, hM.isPrime, hM0⟩`. Unfold `GlobalTheory.CompanionTheory.Equi.LocMem at hv`.

Take `⟨s, hs, y, hy, hsy⟩` from `hv`. Conclude with `hs (hJM ⟨y, hy, hsy⟩)`. Establish `h1 : (1 : 𝓞 F) ∈ J` using `hJ ▸ Submodule.mem_top`. Take `⟨y, hy, hy1⟩` from `h1`. Conclude with `⟨y, hy, by simpa using hy1.symm⟩`.

Introduce and unpack `⟨y, hy, rfl⟩ v`. Unfold `GlobalTheory.CompanionTheory.Equi.LocMem`. Conclude with `⟨1, fun h1 => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1), y, hy, by simp⟩`.
-/
private theorem forall_locMem_iff_exists_mem_ideal {F : Type} [Field F] [NumberField F] (I : Ideal (𝓞 F))
    (z : F) :
    (∀ v : HeightOneSpectrum (𝓞 F), GlobalTheory.CompanionTheory.Equi.LocMem I v z) ↔ ∃ y ∈ I, (y : F) = z := by
  constructor
  · intro h
    let J : Ideal (𝓞 F) :=
      { carrier := {s | ∃ y ∈ I, (s : F) * z = y}
        add_mem' := by
          rintro a b ⟨y₁, hy₁, h₁⟩ ⟨y₂, hy₂, h₂⟩
          exact ⟨y₁ + y₂, I.add_mem hy₁ hy₂, by push_cast; rw [add_mul, h₁, h₂]⟩
        zero_mem' := ⟨0, I.zero_mem, by simp⟩
        smul_mem' := by
          rintro c a ⟨y, hy, h₁⟩
          exact ⟨c * y, I.mul_mem_left c hy, by rw [smul_eq_mul]; push_cast; rw [mul_assoc, h₁]⟩ }
    have hJ : J = ⊤ := by
      by_contra hne
      obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hne
      have hM0 : M ≠ ⊥ :=
        Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField F)
      have hv := h ⟨M, hM.isPrime, hM0⟩
      unfold GlobalTheory.CompanionTheory.Equi.LocMem at hv
      obtain ⟨s, hs, y, hy, hsy⟩ := hv
      exact hs (hJM ⟨y, hy, hsy⟩)
    have h1 : (1 : 𝓞 F) ∈ J := hJ ▸ Submodule.mem_top
    obtain ⟨y, hy, hy1⟩ := h1
    exact ⟨y, hy, by simpa using hy1.symm⟩
  · rintro ⟨y, hy, rfl⟩ v
    unfold GlobalTheory.CompanionTheory.Equi.LocMem
    exact ⟨1, fun h1 => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1), y, hy, by simp⟩

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [GlobalTheory.CompanionTheory.Equi.cosetOff, GlobalTheory.CompanionTheory.Equi.latCoset, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce `h i`. Conclude with `(forall_locMem_iff_exists_mem_ideal I (x i - x0 i)).mp fun v => h v (by simp) i`.

Introduce `h v _ i`. Conclude with `(forall_locMem_iff_exists_mem_ideal I (x i - x0 i)).mpr (h i) v`.
-/
theorem cosetOff_empty_eq_latCoset (F : Type) [Field F] [NumberField F] (ι : Type)
    (I : Ideal (𝓞 F)) (x0 : ι → F) :
    cosetOff (∅ : Finset (HeightOneSpectrum (𝓞 F))) I x0 = latCoset I x0 := by
  ext x
  simp only [GlobalTheory.CompanionTheory.Equi.cosetOff, GlobalTheory.CompanionTheory.Equi.latCoset, Set.mem_setOf_eq]
  constructor
  · intro h i
    exact (forall_locMem_iff_exists_mem_ideal I (x i - x0 i)).mp fun v => h v (by simp) i
  · intro h v _ i
    exact (forall_locMem_iff_exists_mem_ideal I (x i - x0 i)).mpr (h i) v

end GlobalTheory.CompanionTheory.Equi
