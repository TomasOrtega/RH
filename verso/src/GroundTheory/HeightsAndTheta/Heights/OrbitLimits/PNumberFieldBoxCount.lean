import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsNumberFieldBoxCount
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsLatticeImageZLattice
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCovolumeRelIndex
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsEmbeddingSumPlaces
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsMixedBoxCount
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory

namespace NumberFieldBoxCount

/- English proof (translation)
Introduce `x`. Take `⟨n, hn, hnx⟩` from `hL x`. Take `⟨m, hm, hmx⟩` from `hB x`. Use `⟨m * n, Nat.mul_pos hm hn, ?_, ?_⟩` and prove the remaining obligations. Establish `h` using `L.nsmul_mem hnx m`.

Rewrite `h` using `[nsmul_eq_mul, ← mul_assoc]`. Simplify using `using h`. Establish `h` using `B.nsmul_mem hmx n`. Rewrite `h` using `[nsmul_eq_mul, ← mul_assoc]`. Simplify `h` using `[mul_comm]`.
-/
theorem inf_full {F : Type*} [Field F] {L B : AddSubgroup F}
    (hL : ∀ x : F, ∃ n : ℕ, 0 < n ∧ (n : F) * x ∈ L) (hB : ∀ x : F, ∃ n : ℕ, 0 < n ∧ (n : F) * x ∈ B) :
    ∀ x : F, ∃ n : ℕ, 0 < n ∧ (n : F) * x ∈ L ⊓ B := by
  intro x
  obtain ⟨n, hn, hnx⟩ := hL x
  obtain ⟨m, hm, hmx⟩ := hB x
  refine ⟨m * n, Nat.mul_pos hm hn, ?_, ?_⟩
  · have h := L.nsmul_mem hnx m
    rw [nsmul_eq_mul, ← mul_assoc] at h
    simpa using h
  · have h := B.nsmul_mem hmx n
    rw [nsmul_eq_mul, ← mul_assoc] at h
    simpa [mul_comm] using h

/- English proof (translation)
Take `⟨S, hS⟩` from `hK`. Establish `hK' : (AddSubgroup.toIntSubmodule K).FG` using `⟨S, by rw [← AddSubgroup.toIntSubmodule_closure, hS]⟩`. Take `⟨T, hT⟩` from `hK'.of_le (S := AddSubgroup.toIntSubmodule H) hHK`. Conclude with `⟨T, AddSubgroup.toIntSubmodule.injective (by rw [AddSubgroup.toIntSubmodule_closure, hT])⟩`.
-/
theorem fg_of_le {G : Type*} [AddCommGroup G] {H K : AddSubgroup G} (hK : K.FG) (hHK : H ≤ K) : H.FG := by
  obtain ⟨S, hS⟩ := hK
  have hK' : (AddSubgroup.toIntSubmodule K).FG := ⟨S, by rw [← AddSubgroup.toIntSubmodule_closure, hS]⟩
  obtain ⟨T, hT⟩ := hK'.of_le (S := AddSubgroup.toIntSubmodule H) hHK
  exact ⟨T, AddSubgroup.toIntSubmodule.injective (by rw [AddSubgroup.toIntSubmodule_closure, hT])⟩

/- English proof (translation)
Use `⟨fun h w => ?_, fun h σ => ?_⟩` and prove the remaining obligations. Rewrite using `[normAtPlace_apply, ← norm_embedding_eq]`. Conclude with `h _`. Establish `h'` using `h (InfinitePlace.mk σ)`. Rewrite `h'` using `[normAtPlace_apply, InfinitePlace.apply]`.

Break down `embedding_mk_eq σ with e | e` into its components or cases. Rewrite `h'` using `[e]`. Then use the resulting hypothesis. Rewrite `h'` using `[e, hρc]`. Then use the resulting hypothesis.
-/
theorem forall_le_iff {F : Type*} [Field F] [NumberField F] (ρ : (F →+* ℂ) → ℝ)
    (hρc : ∀ σ, ρ (ComplexEmbedding.conjugate σ) = ρ σ) (x : F) :
    (∀ σ : F →+* ℂ, ‖σ x‖ ≤ ρ σ) ↔ ∀ w : InfinitePlace F, normAtPlace w (mixedEmbedding F x) ≤ ρ w.embedding := by
  refine ⟨fun h w => ?_, fun h σ => ?_⟩
  · rw [normAtPlace_apply, ← norm_embedding_eq]
    exact h _
  · have h' := h (InfinitePlace.mk σ)
    rw [normAtPlace_apply, InfinitePlace.apply] at h'
    rcases embedding_mk_eq σ with e | e
    · rwa [e] at h'
    · rwa [e, hρc] at h'

/- English proof (translation)
Rewrite using `[← Nat.card_coe_set_eq]`. Use `Nat.card_eq_of_bijective (fun x => ⟨mixedEmbedding F x.1, (mem_latticeImage _ _).2 ⟨x.1, x.1.2, rfl⟩, (forall_le_iff ρ hρc _).1 x.2⟩) ⟨?_, ?_⟩` and prove the remaining obligations. Introduce `a b h`. Establish `h'` using `congrArg Subtype.val h`. Conclude with `Subtype.ext (Subtype.ext (mixedEmbedding_injective F h'))`.

Introduce and unpack `⟨y, hy, hyb⟩`. Take `⟨x, hx, rfl⟩` from `(mem_latticeImage _ _).1 hy`. Conclude with `⟨⟨⟨x, hx⟩, (forall_le_iff ρ hρc x).2 hyb⟩, rfl⟩`.
-/
theorem card_eq {F : Type*} [Field F] [NumberField F] (ρ : (F →+* ℂ) → ℝ)
    (hρc : ∀ σ, ρ (ComplexEmbedding.conjugate σ) = ρ σ) (L : AddSubgroup F) :
    Nat.card {x : L // ∀ σ : F →+* ℂ, ‖σ (x : F)‖ ≤ ρ σ} =
      {y : mixedSpace F | y ∈ latticeImage F L ∧ ∀ w, normAtPlace w y ≤ ρ w.embedding}.ncard := by
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_eq_of_bijective (fun x => ⟨mixedEmbedding F x.1,
    (mem_latticeImage _ _).2 ⟨x.1, x.1.2, rfl⟩, (forall_le_iff ρ hρc _).1 x.2⟩) ⟨?_, ?_⟩
  · intro a b h
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext (mixedEmbedding_injective F h'))
  · rintro ⟨y, hy, hyb⟩
    obtain ⟨x, hx, rfl⟩ := (mem_latticeImage _ _).1 hy
    exact ⟨⟨⟨x, hx⟩, (forall_le_iff ρ hρc x).2 hyb⟩, rfl⟩

/- English proof (translation)
Simplify using `only [latticeImage, AddSubgroup.toIntSubmodule_toAddSubgroup]`. Conclude with `AddSubgroup.relIndex_map_map_of_injective _ _ (mixedEmbedding_injective F)`.
-/
theorem relIndex_latticeImage {F : Type*} [Field F] [NumberField F] (H K : AddSubgroup F) :
    (latticeImage F H).toAddSubgroup.relIndex (latticeImage F K).toAddSubgroup = H.relIndex K := by
  simp only [latticeImage, AddSubgroup.toIntSubmodule_toAddSubgroup]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ (mixedEmbedding_injective F)

open scoped Classical in

/- English proof (translation)
Introduce `F _ _ B hB hBf`. Take `⟨_, _⟩` from `h1 F B hB hBf`. Use `⟨Module.finrank ℚ F * Real.log 2 + Real.log (ZLattice.covolume (latticeImage F B)) - Real.log (convexBodyLTFactor F : ℝ), ?_⟩` and prove the remaining obligations. Introduce `L hL hLf ρ hρ hρc`. Take `⟨_, _⟩` from `h1 F L hL hLf`.

Take `⟨_, _⟩` from `h1 F (L ⊓ B) (fg_of_le hL inf_le_left) (inf_full hLf hBf)`. Establish `mono : ∀ {H K : AddSubgroup F}, H ≤ K → latticeImage F H ≤ latticeImage F K`. Introduce `H K hHK`. Use `(Submodule.toAddSubgroup_le _ _).1 ?_` and prove the remaining obligations. Simplify using `only [latticeImage, AddSubgroup.toIntSubmodule_toAddSubgroup]`.

Conclude with `AddSubgroup.map_mono hHK`. Establish `cL` using `h2 _ volume (latticeImage F (L ⊓ B)) (latticeImage F L) (mono inf_le_left)`. Establish `cB` using `h2 _ volume (latticeImage F (L ⊓ B)) (latticeImage F B) (mono inf_le_right)`. Rewrite `cL` using `[relIndex_latticeImage, AddSubgroup.inf_relIndex_left]`. Rewrite `cB` using `[relIndex_latticeImage, AddSubgroup.inf_relIndex_right]`.

Establish `p0` using `ZLattice.covolume_pos (latticeImage F (L ⊓ B)) volume`. Establish `pL` using `ZLattice.covolume_pos (latticeImage F L) volume`. Establish `pB` using `ZLattice.covolume_pos (latticeImage F B) volume`. Establish `r1 : (0 : ℝ) < B.relIndex L`. Assume the negation of the conclusion as `hc`.

Establish `hc'` using `not_lt.1 hc`. Use the polynomial consequences of the given equalities and inequalities. Establish `r2 : (0 : ℝ) < L.relIndex B`. Assume the negation of the conclusion as `hc`. Establish `hc'` using `not_lt.1 hc`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hgen : genIndex L B = ZLattice.covolume (latticeImage F B) / ZLattice.covolume (latticeImage F L)`. Rewrite using `[genIndex, div_eq_div_iff r2.ne' pL.ne']`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨-, hcount⟩` from `h5 F (latticeImage F L) (fun w => ρ w.embedding) (fun w => hρ _)`.

Establish `hsum` using `h4 F (fun σ => Real.log (ρ σ)) (fun σ => by simp only [hρc])`. Rewrite using `[card_eq ρ hρc L, hsum, hgen, Real.log_div pB.ne' pL.ne']`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem proof (h1 : LatticeImageZLattice.Statement) (h2 : CovolumeRelIndex.Statement)
    (h4 : EmbeddingSumPlaces.Statement) (h5 : MixedBoxCount.Statement) : NumberFieldBoxCount.Statement := by
  intro F _ _ B hB hBf
  obtain ⟨_, _⟩ := h1 F B hB hBf
  refine ⟨Module.finrank ℚ F * Real.log 2 + Real.log (ZLattice.covolume (latticeImage F B)) -
    Real.log (convexBodyLTFactor F : ℝ), ?_⟩
  intro L hL hLf ρ hρ hρc
  obtain ⟨_, _⟩ := h1 F L hL hLf
  obtain ⟨_, _⟩ := h1 F (L ⊓ B) (fg_of_le hL inf_le_left) (inf_full hLf hBf)
  have mono : ∀ {H K : AddSubgroup F}, H ≤ K → latticeImage F H ≤ latticeImage F K := by
    intro H K hHK
    refine (Submodule.toAddSubgroup_le _ _).1 ?_
    simp only [latticeImage, AddSubgroup.toIntSubmodule_toAddSubgroup]
    exact AddSubgroup.map_mono hHK
  have cL := h2 _ volume (latticeImage F (L ⊓ B)) (latticeImage F L) (mono inf_le_left)
  have cB := h2 _ volume (latticeImage F (L ⊓ B)) (latticeImage F B) (mono inf_le_right)
  rw [relIndex_latticeImage, AddSubgroup.inf_relIndex_left] at cL
  rw [relIndex_latticeImage, AddSubgroup.inf_relIndex_right] at cB
  have p0 := ZLattice.covolume_pos (latticeImage F (L ⊓ B)) volume
  have pL := ZLattice.covolume_pos (latticeImage F L) volume
  have pB := ZLattice.covolume_pos (latticeImage F B) volume
  have r1 : (0 : ℝ) < B.relIndex L := by
    by_contra hc; have hc' := not_lt.1 hc; nlinarith
  have r2 : (0 : ℝ) < L.relIndex B := by
    by_contra hc; have hc' := not_lt.1 hc; nlinarith
  have hgen : genIndex L B = ZLattice.covolume (latticeImage F B) / ZLattice.covolume (latticeImage F L) := by
    rw [genIndex, div_eq_div_iff r2.ne' pL.ne']
    linarith
  obtain ⟨-, hcount⟩ := h5 F (latticeImage F L) (fun w => ρ w.embedding) (fun w => hρ _)
  have hsum := h4 F (fun σ => Real.log (ρ σ)) (fun σ => by simp only [hρc])
  rw [card_eq ρ hρc L, hsum, hgen, Real.log_div pB.ne' pL.ne']
  linarith

end NumberFieldBoxCount

end GroundTheory.Heights₂.Heights.Targets
