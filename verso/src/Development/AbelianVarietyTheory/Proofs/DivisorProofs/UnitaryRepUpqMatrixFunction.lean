import Development.AbelianVarietyTheory.Definitions.Divisors.DatumEquiv
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower

section

noncomputable section

namespace GlobalTheory.PsCo.PcEF.MatrixRepresentation

variable {n : ℕ} (ε : Fin n → Bool) {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

abbrev mat (g : Formalism.REAL.UJ ε) : Matrix (Fin n) (Fin n) ℂ :=
  ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)

/- English proof (translation)
Introduce `_ _ h` and use `Subtype.ext (Units.ext h)`.
-/
theorem mat_injective : Function.Injective (mat ε) := fun _ _ h => Subtype.ext (Units.ext h)

def rep (π : Formalism.REAL.UJ ε →* (X →L[ℂ] X)) (x : Matrix (Fin n) (Fin n) ℂ) : X →L[ℂ] X := by
  classical exact if h : ∃ g, mat ε g = x then π h.choose else 1

/- English proof (translation)
Establish `h : ∃ g', mat ε g' = mat ε g` using `⟨g, rfl⟩`. Rewrite using `[rep, dif_pos h, mat_injective ε h.choose_spec]`.
-/
theorem rep_mat (π : Formalism.REAL.UJ ε →* (X →L[ℂ] X)) (g : Formalism.REAL.UJ ε) : rep ε π (mat ε g) = π g := by
  have h : ∃ g', mat ε g' = mat ε g := ⟨g, rfl⟩
  rw [rep, dif_pos h, mat_injective ε h.choose_spec]

/- English proof (translation)
The claim follows from `(Formalism.REAL.isClosedEmbeddingMatrix n ε).2`.
-/
theorem range_mat : Set.range (mat ε) = Formalism.MainNotions.S.UJset ε := (Formalism.REAL.isClosedEmbeddingMatrix n ε).2

/- English proof (translation)
The claim follows from `range_mat ε ▸ ⟨g, rfl⟩`.
-/
theorem mat_mem (g : Formalism.REAL.UJ ε) : mat ε g ∈ Formalism.MainNotions.S.UJset ε := range_mat ε ▸ ⟨g, rfl⟩

/- English proof (translation)
Rewrite `hx` using `[← range_mat ε]`. Conclude with `hx`.
-/
theorem exists_mat {x : Matrix (Fin n) (Fin n) ℂ} (hx : x ∈ Formalism.MainNotions.S.UJset ε) : ∃ g, mat ε g = x := by
  rw [← range_mat ε] at hx; exact hx

/- English proof (translation)
The claim follows from `(Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding`.
-/
theorem isEmbedding_mat : Topology.IsEmbedding (mat ε) := (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding

end GlobalTheory.PsCo.PcEF.MatrixRepresentation

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEF.MatrixRepresentation

/- English proof (translation)
Introduce `n ε U _ _ π hπ hi`. Use `⟨rep ε π, ⟨⟨?_, fun a ha b hb => ?_⟩, fun a ha v => ?_, fun v => ?_⟩, fun S hS hinv => ?_, fun g => rep_mat ε π g⟩` and prove the remaining obligations. Establish `h1 : mat ε 1 = 1` using `rfl`. Rewrite using `[← h1, rep_mat, map_one]`. Take `⟨g, rfl⟩` from `exists_mat ε ha`.

Take `⟨h, rfl⟩` from `exists_mat ε hb`. Establish `hm : mat ε g * mat ε h = mat ε (g * h)` using `rfl`. Rewrite using `[hm, rep_mat, rep_mat, rep_mat, map_mul]`. Both sides reduce to the same expression. Take `⟨g, rfl⟩` from `exists_mat ε ha`.

Rewrite using `[rep_mat]`. Conclude with `hπ.norm_apply g v`. Establish `hr : Formalism.MainNotions.S.UJset ε = Set.range (mat ε)` using `(range_mat ε).symm show ContinuousOn (fun g => rep ε π g v) (Formalism.MainNotions.S.UJset ε)`. Rewrite using `[hr, continuousOn_iff_continuous_domRestrict]`. Set `E` to `(isEmbedding_mat ε).toHomeomorph`.

Establish `hE : ∀ y, (fun g => π g v) (E.symm y) = rep ε π (y : Matrix (Fin n) (Fin n) ℂ) v`. Introduce `y`. Take `⟨g, rfl⟩` from `E.surjective y`. Use `show π (E.symm (E g)) v = rep ε π (mat ε g) v`. Rewrite using `[E.symm_apply_apply, rep_mat]`.

Conclude with `((hπ.continuous_apply v).comp E.symm.continuous).congr hE`. Conclude with `hi.2 S ⟨hS, fun g v hv => by simpa [rep_mat] using hinv _ (mat_mem ε g) v hv⟩`.
-/
theorem unitaryRep_upq_matrixFunction : MatRep := by
  intro n ε U _ _ π hπ hi
  refine ⟨rep ε π, ⟨⟨?_, fun a ha b hb => ?_⟩, fun a ha v => ?_, fun v => ?_⟩, fun S hS hinv => ?_, fun g => rep_mat ε π g⟩
  · have h1 : mat ε 1 = 1 := rfl
    rw [← h1, rep_mat, map_one]
  · obtain ⟨g, rfl⟩ := exists_mat ε ha
    obtain ⟨h, rfl⟩ := exists_mat ε hb
    have hm : mat ε g * mat ε h = mat ε (g * h) := rfl
    rw [hm, rep_mat, rep_mat, rep_mat, map_mul]
    rfl
  · obtain ⟨g, rfl⟩ := exists_mat ε ha
    rw [rep_mat]
    exact hπ.norm_apply g v
  · have hr : Formalism.MainNotions.S.UJset ε = Set.range (mat ε) := (range_mat ε).symm
    show ContinuousOn (fun g => rep ε π g v) (Formalism.MainNotions.S.UJset ε)
    rw [hr, continuousOn_iff_continuous_domRestrict]
    let E := (isEmbedding_mat ε).toHomeomorph
    have hE : ∀ y, (fun g => π g v) (E.symm y) = rep ε π (y : Matrix (Fin n) (Fin n) ℂ) v := by
      intro y
      obtain ⟨g, rfl⟩ := E.surjective y
      show π (E.symm (E g)) v = rep ε π (mat ε g) v
      rw [E.symm_apply_apply, rep_mat]
    exact ((hπ.continuous_apply v).comp E.symm.continuous).congr hE
  · exact hi.2 S ⟨hS, fun g v hv => by simpa [rep_mat] using hinv _ (mat_mem ε g) v hv⟩

end GlobalTheory.PsCo.PcEF

end
end
