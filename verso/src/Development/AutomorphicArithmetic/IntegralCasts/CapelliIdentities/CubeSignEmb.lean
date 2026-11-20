import Mathlib

noncomputable def UpperTheory.Reformulated.B.Qh71.cubeSign :
    {ι : Type} → [LinearOrder ι] → Finset ι → ι → ℤ :=
    fun {ι : Type} [LinearOrder ι] (t : Finset ι) (i : ι) ↦ (-1 : ℤ) ^ {x ∈ t | x < i}.card

/- English proof (translation)
Introduce `κ _ t n h k`. Establish `key : {x ∈ t | x < t.orderEmbOfFin h k} = (Finset.Iio k).map (t.orderEmbOfFin h).toEmbedding`. Use extensionality with `x`. Simplify using `only [Finset.mem_filter, Finset.mem_map, Finset.mem_Iio]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hx, hlt⟩`. Establish `hr : x ∈ Set.range (t.orderEmbOfFin h)`. Rewrite using `[Finset.range_orderEmbOfFin]`. Conclude with `hx`. Take `⟨j, rfl⟩` from `hr`.

Conclude with `⟨j, (t.orderEmbOfFin h).lt_iff_lt.mp hlt, rfl⟩`. Introduce and unpack `⟨j, hj, rfl⟩`. Conclude with `⟨Finset.orderEmbOfFin_mem t h j, (t.orderEmbOfFin h).lt_iff_lt.mpr hj⟩`. Unfold `UpperTheory.Reformulated.B.Qh71.cubeSign`. Rewrite using `[key, Finset.card_map, Fin.card_Iio]`.
-/
theorem UpperTheory.Reformulated.B.Qh71.cubeSign_emb :
    ∀ {κ : Type} [inst : LinearOrder κ] (t : Finset κ) {n : ℕ} (h : t.card = n) (k : Fin n),
      UpperTheory.Reformulated.B.Qh71.cubeSign t ((t.orderEmbOfFin h : Fin n → κ) k) = (-1 : ℤ) ^ (↑k : ℕ) := by
  intro κ _ t n h k
  have key : {x ∈ t | x < t.orderEmbOfFin h k}
      = (Finset.Iio k).map (t.orderEmbOfFin h).toEmbedding := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_Iio]
    constructor
    · rintro ⟨hx, hlt⟩
      have hr : x ∈ Set.range (t.orderEmbOfFin h) := by
        rw [Finset.range_orderEmbOfFin]
        exact hx
      obtain ⟨j, rfl⟩ := hr
      exact ⟨j, (t.orderEmbOfFin h).lt_iff_lt.mp hlt, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem t h j, (t.orderEmbOfFin h).lt_iff_lt.mpr hj⟩
  unfold UpperTheory.Reformulated.B.Qh71.cubeSign
  rw [key, Finset.card_map, Fin.card_Iio]
