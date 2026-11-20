import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ChEltOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDetMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDetCH
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DPull

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

/- English proof (translation)
Rewrite using `[← d_toDet_CH, ← d_toDet_CH, d_toDet_map, ← SetLike.mem_coe (p := Submodule.span B _), ← (d_chS D.toDet B).2.1, SetLike.mem_coe]`. Take `⟨-, -, h1, h2⟩` from `d_pull (D.toDet.baseChange B) (toT A G B)`. Use `⟨h1 x, fun h => ?_⟩` and prove the remaining obligations. Take `⟨y, hy, e⟩` from `(h2 fun z => ⟨_, toT_ofT z⟩).2 _ h`. Establish `: y = x` using `by rw [← ofT_toT (A := A) y, e, ofT_toT]`.

Conclude with `this ▸ hy`.
-/
private theorem mem_iff {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] [Algebra A B] (D : GDet n A G)
    (x : MonoidAlgebra B G) :
    x ∈ TwoSidedIdeal.span (D.map (algebraMap A B)).CH ↔ toT A G B x ∈
      Submodule.span B ((fun z : MonoidAlgebra A G => (1 : B) ⊗ₜ[A] z) ''
        (TwoSidedIdeal.span D.CH : Set (MonoidAlgebra A G))) := by
  rw [← d_toDet_CH, ← d_toDet_CH, d_toDet_map, ← SetLike.mem_coe (p := Submodule.span B _),
    ← (d_chS D.toDet B).2.1, SetLike.mem_coe]
  obtain ⟨-, -, h1, h2⟩ := d_pull (D.toDet.baseChange B) (toT A G B)
  refine ⟨h1 x, fun h => ?_⟩
  obtain ⟨y, hy, e⟩ := (h2 fun z => ⟨_, toT_ofT z⟩).2 _ h
  have : y = x := by rw [← ofT_toT (A := A) y, e, ofT_toT]
  exact this ▸ hy

/- English proof (translation)
Proceed by induction on `hz using TwoSidedIdeal.span_induction with`. Consider the case `mem x hx => exact TwoSidedIdeal.subset_span ⟨x, hx, rfl⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`.

Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [map_neg]`. Conclude with `neg_mem hx`. Consider the case `left_absorb a x _ hx => rw [map_mul]`. Conclude with `TwoSidedIdeal.mul_mem_left _ _ _ hx`.

Consider the case `right_absorb b x _ hx => rw [map_mul]`. Conclude with `TwoSidedIdeal.mul_mem_right _ _ _ hx`.
-/
private theorem map_mem {A B : Type} [Ring A] [Ring B] (f : A →+* B) (S : Set A) (z : A)
    (hz : z ∈ TwoSidedIdeal.span S) : f z ∈ TwoSidedIdeal.span (f '' S) := by
  induction hz using TwoSidedIdeal.span_induction with
  | mem x hx => exact TwoSidedIdeal.subset_span ⟨x, hx, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | left_absorb a x _ hx => rw [map_mul]; exact TwoSidedIdeal.mul_mem_left _ _ _ hx
  | right_absorb b x _ hx => rw [map_mul]; exact TwoSidedIdeal.mul_mem_right _ _ _ hx

/- English proof (translation)
Introduce `n A B G _ _ _ D f`. Use `letI : Algebra A B := f.toAlgebra`. Express the relevant statement in the definitionally equal form `TwoSidedIdeal.span (D.map (algebraMap A B)).CH = TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G (algebraMap A B) '' D.CH)`. Establish `e : ∀ z : MonoidAlgebra A G, ofT A G B (1 ⊗ₜ z) = MonoidAlgebra.mapRingHom G (algebraMap A B) z` using `fun z => by rw [ofT_tmul, one_smul]`. Apply `le_antisymm` to reduce the goal to its premises.

Introduce `x hx`. Rewrite `hx` using `[mem_iff]`. Rewrite using `[← ofT_toT (A := A) x]`. Generalize the expression as in `toT A G B x = w at hx`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨z, hz, rfl⟩` from `hx`. Rewrite using `[e]`. Conclude with `map_mem _ _ z hz`. Consider the case `zero => rw [map_zero]`.

Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `smul a x _ hx => rw [map_smul, Algebra.smul_def]`. Conclude with `TwoSidedIdeal.mul_mem_left _ _ _ hx`.

Rewrite using `[TwoSidedIdeal.span_le]`. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Rewrite using `[SetLike.mem_coe, mem_iff, ← e, toT_ofT]`. Conclude with `Submodule.subset_span ⟨z, TwoSidedIdeal.subset_span hz, rfl⟩`.
-/
theorem UpperTheory.V.CA.g_chmap :
    ∀ {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (D : GDet n A G) (f : A →+* B), TwoSidedIdeal.span (D.map f).CH = TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G f '' D.CH) := by
  intro n A B G _ _ _ D f
  letI : Algebra A B := f.toAlgebra
  change TwoSidedIdeal.span (D.map (algebraMap A B)).CH =
    TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G (algebraMap A B) '' D.CH)
  have e : ∀ z : MonoidAlgebra A G, ofT A G B (1 ⊗ₜ z) = MonoidAlgebra.mapRingHom G (algebraMap A B) z :=
    fun z => by rw [ofT_tmul, one_smul]
  apply le_antisymm
  · intro x hx
    rw [mem_iff] at hx
    rw [← ofT_toT (A := A) x]
    generalize toT A G B x = w at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      rw [e]
      exact map_mem _ _ z hz
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul, Algebra.smul_def]; exact TwoSidedIdeal.mul_mem_left _ _ _ hx
  · rw [TwoSidedIdeal.span_le]
    rintro _ ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, mem_iff, ← e, toT_ofT]
    exact Submodule.subset_span ⟨z, TwoSidedIdeal.subset_span hz, rfl⟩
