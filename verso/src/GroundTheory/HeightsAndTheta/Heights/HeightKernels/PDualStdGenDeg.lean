import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ImportsFurther
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.ChartRestriction.G.AI.I1 NumberField MvPolynomial

namespace DualStdGenDeg

def fibreBlk₀ : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit) :=
  ⟨Sum.inl (), fun ⟨_, h⟩ => Sum.inr_ne_inl h⟩

/- English proof (translation)
Break down `k with ⟨⟨⟩ | ⟨⟩, h⟩` into its components or cases. Both sides reduce to the same expression. Conclude with `absurd ⟨(), rfl⟩ h`.
-/
theorem eq_fibreBlk₀ (k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit)) : k = fibreBlk₀ := by
  rcases k with ⟨⟨⟩ | ⟨⟩, h⟩
  · rfl
  · exact absurd ⟨(), rfl⟩ h

def fibreCoord {T : Type} {i : ℕ} (c : T) :
    ∀ k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit), fibreIdx (Sum.elim (dualBlocks T) (PBlk i)) Sum.inr k
  | ⟨Sum.inl (), _⟩ => c
  | ⟨Sum.inr (), h⟩ => absurd ⟨(), rfl⟩ h

/- English proof (translation)
Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨⟨⟨⟩ | ⟨⟩, h⟩, t⟩, rfl⟩`. Conclude with `⟨t, rfl⟩`. Conclude with `absurd ⟨(), rfl⟩ h`.

Introduce and unpack `⟨t, rfl⟩`. Conclude with `⟨⟨fibreBlk₀, t⟩, rfl⟩`.
-/
theorem range_eq {T Φ' : Type} [Field Φ'] {i : ℕ} (x' : (Σ k, Sum.elim (dualBlocks T) (PBlk i) k) → Φ') (d : Φ') :
    (Set.range fun p : (Σ k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit),
        fibreIdx (Sum.elim (dualBlocks T) (PBlk i)) Sum.inr k) => x' ⟨p.1.1, p.2⟩ / d) =
      Set.range fun t : T => x' (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) / d := by
  ext y
  constructor
  · rintro ⟨⟨⟨⟨⟩ | ⟨⟩, h⟩, t⟩, rfl⟩
    · exact ⟨t, rfl⟩
    · exact absurd ⟨(), rfl⟩ h
  · rintro ⟨t, rfl⟩
    exact ⟨⟨fibreBlk₀, t⟩, rfl⟩

end DualStdGenDeg

open DualStdGenDeg in

/- English proof (translation)
Introduce `K _ _ i T _ _ b G J hi hJ`. Take `⟨c, hc, hrank, htr⟩` from `hRat K i T b G hi`. Establish `hfin : Module.Finite G.Φ (Algebra.adjoin G.Φ (Set.range fun t : T => G.x' (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) / G.x' (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k)))` using `Module.finite_of_finrank_pos (hrank ▸ Module.finrank_pos)`. Establish `key` using `hPt G.Φ G.Φ' (FibreBlock (Sum.inr : Unit → Unit ⊕ Unit)) (fibreIdx (Sum.elim (dualBlocks T) (PBlk i)) Sum.inr) fibreBlk₀ eq_fibreBlk₀ (fun q => G.x' ⟨q.1.1, q.2⟩) (fibreCoord c) hc`. Use `beta_reduce at key`.

Rewrite `key` using `[range_eq G.x']`. Take `⟨hV, hch, hdeg⟩` from `key hfin htr`. Establish `hJ0` using `hJ.1 (fibreIdeal Sum.inr G) Fin.elim0 (fibreCoord c) hV hch`. Rewrite using `[hJ0]`. Conclude with `congrArg ((↑) : ℕ → ℤ) (hdeg.trans hrank)`.
-/
theorem DualStdGenDeg.proof (hPt : OneBlockPointDeg.Statement) (hRat : DualStdFibreRatios.Statement) :
    DualStdGenDeg.Statement := by
  intro K _ _ i T _ _ b G J hi hJ
  obtain ⟨c, hc, hrank, htr⟩ := hRat K i T b G hi
  have hfin : Module.Finite G.Φ (Algebra.adjoin G.Φ (Set.range fun t : T =>
      G.x' (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) /
        G.x' (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k))) :=
    Module.finite_of_finrank_pos (hrank ▸ Module.finrank_pos)
  have key := hPt G.Φ G.Φ' (FibreBlock (Sum.inr : Unit → Unit ⊕ Unit))
    (fibreIdx (Sum.elim (dualBlocks T) (PBlk i)) Sum.inr) fibreBlk₀ eq_fibreBlk₀
    (fun q => G.x' ⟨q.1.1, q.2⟩) (fibreCoord c) hc
  beta_reduce at key
  rw [range_eq G.x'] at key
  obtain ⟨hV, hch, hdeg⟩ := key hfin htr
  have hJ0 := hJ.1 (fibreIdeal Sum.inr G) Fin.elim0 (fibreCoord c) hV hch
  rw [hJ0]
  exact congrArg ((↑) : ℕ → ℤ) (hdeg.trans hrank)

end GroundTheory.Heights₂.Heights
