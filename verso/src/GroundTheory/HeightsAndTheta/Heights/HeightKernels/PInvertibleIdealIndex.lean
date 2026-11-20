import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsInvertibleIdealIndex
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsOrderIdealIndexExtension
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLocallyPrincipalCoprime
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ExistsSmulMemOfSpanEqTop
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesLineDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

namespace InvertibleIdealIndexAlt

variable {L : Type} [Field L]

def mulBy (c : L) : L →+ L := AddMonoidHom.mulLeft c

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem mulBy_apply (c x : L) : mulBy c x = c * x := rfl

/- English proof (translation)
Introduce `_ _ h` and use `mul_left_cancel₀ hc h`.
-/
theorem mulBy_injective {c : L} (hc : c ≠ 0) : Function.Injective (mulBy c) :=
  fun _ _ h => mul_left_cancel₀ hc h

/- English proof (translation)
Establish `hMβ : M.map (mulBy β) = J.map (mulBy δ)`. Use extensionality with `z`. Simplify using `only [AddSubgroup.mem_map, mulBy_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`.

Take `⟨y, hy, h⟩` from `(hM x).1 hx`. Conclude with `⟨y, hy, h.symm⟩`. Introduce and unpack `⟨y, hy, rfl⟩`. Use `⟨δ * y / β, (hM _).2 ⟨y, hy, by field_simp⟩, by field_simp⟩` and prove the remaining obligations. Use `set C := (J.map (mulBy β)).map (mulBy δ) with hC`.

Establish `hC' : C = (J.map (mulBy δ)).map (mulBy β)`. Rewrite using `[hC, AddSubgroup.map_map, AddSubgroup.map_map]`. Use `congr 1`. Use extensionality with `x`. Simplify using `[mul_left_comm]`.

Establish `hCA : C ≤ J.map (mulBy δ)` using `AddSubgroup.map_mono hβJ`. Establish `hCB : C ≤ X.map (mulBy β)`. Rewrite using `[hC']`. Conclude with `AddSubgroup.map_mono (le_trans (AddSubgroup.map_mono hJX) hδX)`. Establish `e1 : C.relIndex (J.map (mulBy δ)) = (J.map (mulBy β)).relIndex J` using `AddSubgroup.relIndex_map_map_of_injective _ _ (mulBy_injective hδ)`.

Establish `e2 : C.relIndex (X.map (mulBy β)) = (J.map (mulBy δ)).relIndex X`. Rewrite using `[hC']`. Conclude with `AddSubgroup.relIndex_map_map_of_injective _ _ (mulBy_injective hβ)`. Establish `e3 : (J.map (mulBy β)).relIndex J * J.relIndex X = (X.map (mulBy β)).relIndex X * J.relIndex X`. Rewrite using `[AddSubgroup.relIndex_mul_relIndex _ _ _ hβJ hJX, ← AddSubgroup.relIndex_mul_relIndex _ _ _ (AddSubgroup.map_mono hJX) hβX, AddSubgroup.relIndex_map_map_of_injective (f := mulBy β) _ _ (mulBy_injective hβ)]`.

Conclude with `Nat.mul_comm _ _`. Establish `e4 : (J.map (mulBy δ)).relIndex X = J.relIndex X * (X.map (mulBy δ)).relIndex X`. Rewrite using `[← AddSubgroup.relIndex_mul_relIndex _ _ _ (AddSubgroup.map_mono hJX) hδX, AddSubgroup.relIndex_map_map_of_injective (f := mulBy δ) _ _ (mulBy_injective hδ)]`. Establish `e3' : (J.map (mulBy β)).relIndex J = (X.map (mulBy β)).relIndex X` using `Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hJ) e3`. Establish `hCne : C.relIndex (X.map (mulBy β)) ≠ 0`.

Rewrite using `[e2, e4]`. Conclude with `mul_ne_zero hJ hδ'`. Rewrite using `[← KLinesLineDegree.genIndex_map_of_injective (mulBy β) (mulBy_injective hβ), hMβ, IndefiniteRowSideFullHecke.Kernels.genIndex_eq_div_of_le hCA hCB hCne, e1, e2, e3', e4]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem genIndex_eq {X J M : AddSubgroup L} {β δ : L} (hβ : β ≠ 0) (hδ : δ ≠ 0) (hJX : J ≤ X)
    (hβX : X.map (mulBy β) ≤ X) (hδX : X.map (mulBy δ) ≤ X) (hβJ : J.map (mulBy β) ≤ J)
    (hM : ∀ x, x ∈ M ↔ ∃ y ∈ J, β * x = δ * y) (hJ : J.relIndex X ≠ 0)
    (hδ' : (X.map (mulBy δ)).relIndex X ≠ 0) :
    genIndex M X = ((X.map (mulBy β)).relIndex X : ℝ) /
      (((X.map (mulBy δ)).relIndex X : ℝ) * (J.relIndex X : ℝ)) := by
  have hMβ : M.map (mulBy β) = J.map (mulBy δ) := by
    ext z
    simp only [AddSubgroup.mem_map, mulBy_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨y, hy, h⟩ := (hM x).1 hx
      exact ⟨y, hy, h.symm⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨δ * y / β, (hM _).2 ⟨y, hy, by field_simp⟩, by field_simp⟩
  set C := (J.map (mulBy β)).map (mulBy δ) with hC
  have hC' : C = (J.map (mulBy δ)).map (mulBy β) := by
    rw [hC, AddSubgroup.map_map, AddSubgroup.map_map]
    congr 1
    ext x
    simp [mul_left_comm]
  have hCA : C ≤ J.map (mulBy δ) := AddSubgroup.map_mono hβJ
  have hCB : C ≤ X.map (mulBy β) := by
    rw [hC']
    exact AddSubgroup.map_mono (le_trans (AddSubgroup.map_mono hJX) hδX)
  have e1 : C.relIndex (J.map (mulBy δ)) = (J.map (mulBy β)).relIndex J :=
    AddSubgroup.relIndex_map_map_of_injective _ _ (mulBy_injective hδ)
  have e2 : C.relIndex (X.map (mulBy β)) = (J.map (mulBy δ)).relIndex X := by
    rw [hC']
    exact AddSubgroup.relIndex_map_map_of_injective _ _ (mulBy_injective hβ)
  have e3 : (J.map (mulBy β)).relIndex J * J.relIndex X =
      (X.map (mulBy β)).relIndex X * J.relIndex X := by
    rw [AddSubgroup.relIndex_mul_relIndex _ _ _ hβJ hJX,
      ← AddSubgroup.relIndex_mul_relIndex _ _ _ (AddSubgroup.map_mono hJX) hβX,
      AddSubgroup.relIndex_map_map_of_injective (f := mulBy β) _ _ (mulBy_injective hβ)]
    exact Nat.mul_comm _ _
  have e4 : (J.map (mulBy δ)).relIndex X = J.relIndex X * (X.map (mulBy δ)).relIndex X := by
    rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ (AddSubgroup.map_mono hJX) hδX,
      AddSubgroup.relIndex_map_map_of_injective (f := mulBy δ) _ _ (mulBy_injective hδ)]
  have e3' : (J.map (mulBy β)).relIndex J = (X.map (mulBy β)).relIndex X :=
    Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hJ) e3
  have hCne : C.relIndex (X.map (mulBy β)) ≠ 0 := by
    rw [e2, e4]
    exact mul_ne_zero hJ hδ'
  rw [← KLinesLineDegree.genIndex_map_of_injective (mulBy β) (mulBy_injective hβ), hMβ,
    IndefiniteRowSideFullHecke.Kernels.genIndex_eq_div_of_le hCA hCB hCne, e1, e2, e3', e4]
  push_cast
  ring

/- English proof (translation)
The claim follows from `(IsIntegral.of_finite ℤ (⟨b, hb⟩ : B)).map (B.subtype.toIntAlgHom)`.
-/
theorem isIntegral_of_mem {B : Subring L} [Module.Finite ℤ B] {b : L} (hb : b ∈ B) :
    IsIntegral ℤ b :=
  (IsIntegral.of_finite ℤ (⟨b, hb⟩ : B)).map (B.subtype.toIntAlgHom)

/- English proof (translation)
Conclude with `S.smul_mem (⟨b, isIntegral_of_mem hb⟩ : 𝓞 L) hz`.
-/
theorem mul_mem_of_mem [NumberField L] {B : Subring L} [Module.Finite ℤ B] {S : Submodule (𝓞 L) L} {b z : L}
    (hb : b ∈ B) (hz : z ∈ S) : b * z ∈ S := by
  exact S.smul_mem (⟨b, isIntegral_of_mem hb⟩ : 𝓞 L) hz

/- English proof (translation)
Establish `h` using `mul_mem_of_mem (S := 1) hb (Submodule.mem_one.mpr ⟨1, map_one _⟩)`. Rewrite `h` using `[mul_one]`. Then use the resulting hypothesis.
-/
theorem mem_one_of_mem [NumberField L] {B : Subring L} [Module.Finite ℤ B] {b : L} (hb : b ∈ B) :
    b ∈ (1 : Submodule (𝓞 L) L) := by
  have h := mul_mem_of_mem (S := 1) hb (Submodule.mem_one.mpr ⟨1, map_one _⟩)
  rwa [mul_one] at h

/- English proof (translation)
Use `set S := Submodule.span (𝓞 L) (Set.range a)`. Set `J : Ideal B` to `{ carrier := {b | (b : L) * z ∈ S} add_mem' := fun {x y} hx hy => by show ((x : L) + y) * z ∈ S`. Rewrite using `[add_mul]`. Conclude with `S.add_mem hx hy`. Use the proof step `zero_mem' := by show ((0 : B) : L) * z ∈ S`.

Simplify using the standard rewrite rules. Use the proof step `smul_mem' := fun c x hx => by show ((c : L) * x) * z ∈ S`. Rewrite using `[mul_assoc]`. Conclude with `mul_mem_of_mem c.2 hx }`. Assume the negation of the conclusion as `hzS`.

Establish `hJ : J ≠ ⊤`. Introduce `h`. Establish `h1 : (1 : B) ∈ J` using `h ▸ Submodule.mem_top`. Establish `h2 : ((1 : B) : L) * z ∈ S` using `h1`. Apply `hzS` to reduce the goal to its premises.

Simplify using `using h2`. Take `⟨m, hm, hJm⟩` from `Ideal.exists_le_maximal J hJ`. Take `⟨i, hi⟩` from `hloc m hm`. Take `⟨b, c, hbm, hbc⟩` from `hi z hz`. Apply `hbm` to reduce the goal to its premises.

Apply `hJm` to reduce the goal to its premises. Use `show (b : L) * z ∈ S`. Rewrite using `[hbc]`. Conclude with `mul_mem_of_mem c.2 (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem mem_span_of_local [NumberField L] {B : Subring L} [Module.Finite ℤ B] {M : AddSubgroup L} {ι : Type}
    {a : ι → L}
    (hloc : ∀ m : Ideal B, m.IsMaximal → ∃ i, ∀ z ∈ M, ∃ b c : B, b ∉ m ∧ (b : L) * z = c * a i)
    {z : L} (hz : z ∈ M) : z ∈ Submodule.span (𝓞 L) (Set.range a) := by
  set S := Submodule.span (𝓞 L) (Set.range a)
  let J : Ideal B :=
    { carrier := {b | (b : L) * z ∈ S}
      add_mem' := fun {x y} hx hy => by
        show ((x : L) + y) * z ∈ S
        rw [add_mul]
        exact S.add_mem hx hy
      zero_mem' := by
        show ((0 : B) : L) * z ∈ S
        simp
      smul_mem' := fun c x hx => by
        show ((c : L) * x) * z ∈ S
        rw [mul_assoc]
        exact mul_mem_of_mem c.2 hx }
  by_contra hzS
  have hJ : J ≠ ⊤ := by
    intro h
    have h1 : (1 : B) ∈ J := h ▸ Submodule.mem_top
    have h2 : ((1 : B) : L) * z ∈ S := h1
    apply hzS
    simpa using h2
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hJ
  obtain ⟨i, hi⟩ := hloc m hm
  obtain ⟨b, c, hbm, hbc⟩ := hi z hz
  apply hbm
  apply hJm
  show (b : L) * z ∈ S
  rw [hbc]
  exact mul_mem_of_mem c.2 (Submodule.subset_span ⟨i, rfl⟩)

/- English proof (translation)
Establish `hinj : Function.Injective B.subtype.toAddMonoidHom` using `Subtype.val_injective`. Establish `hr : (⊤ : AddSubgroup B).map B.subtype.toAddMonoidHom = B.toAddSubgroup`. Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite using `[← hr, ← AddSubgroup.relIndex_comap, AddSubgroup.comap_map_eq_self_of_injective hinj, AddSubgroup.relIndex_top_right]`.
-/
theorem relIndex_map_subtype (B : Subring L) (H : AddSubgroup B) :
    (H.map B.subtype.toAddMonoidHom).relIndex B.toAddSubgroup = H.index := by
  have hinj : Function.Injective B.subtype.toAddMonoidHom := Subtype.val_injective
  have hr : (⊤ : AddSubgroup B).map B.subtype.toAddMonoidHom = B.toAddSubgroup := by
    ext x
    simp
  rw [← hr, ← AddSubgroup.relIndex_comap, AddSubgroup.comap_map_eq_self_of_injective hinj,
    AddSubgroup.relIndex_top_right]

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [AddSubgroup.mem_map, mulBy_apply, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨⟨y, hy⟩ * β, ⟨⟨y, hy⟩, rfl⟩, by simp [mul_comm]⟩`.

Introduce and unpack `⟨_, ⟨c, rfl⟩, rfl⟩`. Conclude with `⟨c, c.2, by simp [mul_comm]⟩`.
-/
theorem map_mul_eq (B : Subring L) (β : B) :
    B.toAddSubgroup.map (mulBy (β : L)) =
      (Ideal.span {β}).toAddSubgroup.map B.subtype.toAddMonoidHom := by
  ext x
  simp only [AddSubgroup.mem_map, mulBy_apply, Submodule.mem_toAddSubgroup,
    Ideal.mem_span_singleton']
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩ * β, ⟨⟨y, hy⟩, rfl⟩, by simp [mul_comm]⟩
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, c.2, by simp [mul_comm]⟩

/- English proof (translation)
Establish `hspan : Submodule.span (𝓞 L) ((fun y : B => (y : L)) '' ((Ideal.span {β} : Ideal B) : Set B)) = Submodule.span (𝓞 L) {(β : L)}`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 hy`.

Use `show (c : L) * (β : L) ∈ _`. Conclude with `mul_mem_of_mem c.2 (Submodule.subset_span rfl)`. Rewrite using `[Submodule.span_le, Set.singleton_subset_iff]`. Conclude with `Submodule.subset_span ⟨β, Ideal.mem_span_singleton_self β, rfl⟩`. Rewrite using `[hspan]`.

Use extensionality with `x`. Simplify using `only [AddSubgroup.mem_map, mulBy_apply, Submodule.mem_toAddSubgroup, Submodule.mem_one, Submodule.mem_span_singleton, Algebra.smul_def]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨c, rfl⟩, rfl⟩`. Conclude with `⟨c, mul_comm _ _⟩`.

Introduce and unpack `⟨c, rfl⟩`. Conclude with `⟨_, ⟨c, rfl⟩, mul_comm _ _⟩`.
-/
theorem map_mul_eq_span [NumberField L] {B : Subring L} [Module.Finite ℤ B] (β : B) :
    (1 : Submodule (𝓞 L) L).toAddSubgroup.map (mulBy (β : L)) =
      (Submodule.span (𝓞 L) ((fun y : B => (y : L)) '' ((Ideal.span {β} : Ideal B) : Set B))).toAddSubgroup := by
  have hspan : Submodule.span (𝓞 L) ((fun y : B => (y : L)) '' ((Ideal.span {β} : Ideal B) : Set B)) =
      Submodule.span (𝓞 L) {(β : L)} := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
      show (c : L) * (β : L) ∈ _
      exact mul_mem_of_mem c.2 (Submodule.subset_span rfl)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact Submodule.subset_span ⟨β, Ideal.mem_span_singleton_self β, rfl⟩
  rw [hspan]
  ext x
  simp only [AddSubgroup.mem_map, mulBy_apply, Submodule.mem_toAddSubgroup, Submodule.mem_one,
    Submodule.mem_span_singleton, Algebra.smul_def]
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, mul_comm _ _⟩
  · rintro ⟨c, rfl⟩
    exact ⟨_, ⟨c, rfl⟩, mul_comm _ _⟩

/- English proof (translation)
Establish `: Infinite (1 : Submodule (𝓞 L) L).toAddSubgroup` using `Infinite.of_injective (fun n : ℕ => (⟨(n : L), Submodule.mem_one.mpr ⟨n, by simp⟩⟩ : (1 : Submodule (𝓞 L) L).toAddSubgroup)) (fun m n h => Nat.cast_injective (R := L) (congrArg Subtype.val h))`. Conclude with `Nat.card_eq_zero_of_infinite`.
-/
theorem card_one_eq_zero [NumberField L] : Nat.card (1 : Submodule (𝓞 L) L).toAddSubgroup = 0 := by
  have : Infinite (1 : Submodule (𝓞 L) L).toAddSubgroup :=
    Infinite.of_injective (fun n : ℕ => (⟨(n : L), Submodule.mem_one.mpr ⟨n, by simp⟩⟩ :
      (1 : Submodule (𝓞 L) L).toAddSubgroup))
      (fun m n h => Nat.cast_injective (R := L) (congrArg Subtype.val h))
  exact Nat.card_eq_zero_of_infinite

/- English proof (translation)
Establish `: Infinite B.toAddSubgroup` using `Infinite.of_injective (fun n : ℕ => (⟨(n : L), by simp⟩ : B.toAddSubgroup)) (fun m n h => Nat.cast_injective (R := L) (congrArg Subtype.val h))`. Conclude with `Nat.card_eq_zero_of_infinite`.
-/
theorem card_subring_eq_zero [NumberField L] (B : Subring L) : Nat.card B.toAddSubgroup = 0 := by
  have : Infinite B.toAddSubgroup :=
    Infinite.of_injective (fun n : ℕ => (⟨(n : L), by simp⟩ : B.toAddSubgroup))
      (fun m n h => Nat.cast_injective (R := L) (congrArg Subtype.val h))
  exact Nat.card_eq_zero_of_infinite

end InvertibleIdealIndexAlt

open InvertibleIdealIndexAlt in

/- English proof (translation)
Introduce `L _ _ B M ι _ a hB hBM haM hden hloc`. Use `hB` as an intermediate fact. Distinguish the cases in `hM0 : M = ⊥`. Establish `ha0 : ∀ i, a i = 0` using `fun i => by simpa [hM0] using haM i`. Establish `hT0 : Submodule.span (𝓞 L) (Set.range a) = ⊥`.

Rewrite using `[Submodule.span_eq_bot]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `ha0 i`. Simplify using `only [hM0, hT0, Submodule.bot_toAddSubgroup, genIndex, AddSubgroup.relIndex_bot_left, AddSubgroup.relIndex_bot_right, card_subring_eq_zero, card_one_eq_zero]`. Simplify using the standard rewrite rules.

Take `⟨r, s, hs, hrank, hfin, hidx⟩` from `h1 L B hB`. Take `⟨β, δ, I, hβ, hδ, hIs, hMI⟩` from `h2 L B M ι a hB hBM haM hden hloc hM0 s hs`. Establish `hβL : (β : L) ≠ 0` using `fun h => hβ (Subtype.ext h)`. Establish `hδL : (δ : L) ≠ 0` using `fun h => hδ (Subtype.ext h)`. Establish `hI0 : I ≠ ⊥`.

Introduce `hI`. Take `⟨⟨x, hxM⟩, hx0⟩` from `AddSubgroup.ne_bot_iff_exists_ne_zero.mp hM0`. Take `⟨y, hy, hxy⟩` from `(hMI x).1 hxM`. Rewrite `hy` using `[hI, Ideal.mem_bot]`. Substitute `hy` using the available equality.

Establish `hx : x ≠ 0` using `fun h => hx0 (Subtype.ext h)`. Simplify using `[hβL, hx] at hxy`. Establish `hspanβ : Ideal.span {β} ≠ ⊥` using `by rw [Ne, Ideal.span_singleton_eq_bot]; exact hβ`. Establish `hspanδ : Ideal.span {δ} ≠ ⊥` using `by rw [Ne, Ideal.span_singleton_eq_bot]; exact hδ`. Establish `g1` using `genIndex_eq (X := B.toAddSubgroup) (J := I.toAddSubgroup.map B.subtype.toAddMonoidHom) (M := M) hβL hδL (by rintro _ ⟨y, _, rfl⟩; exact y.2) (by rintro _ ⟨y, hy, rfl⟩; exact B.mul_mem β.2 hy) (by rintro _ ⟨y, hy, rfl⟩; exact B.mul_mem δ.2 hy) (by rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩; …`.

Introduce `x`. Rewrite using `[hMI x]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, h⟩`. Conclude with `⟨y, ⟨y, hy, rfl⟩, h⟩`.

Introduce and unpack `⟨_, ⟨y, hy, rfl⟩, h⟩`. Conclude with `⟨y, hy, h⟩)`. Use the proof step `(by rw [relIndex_map_subtype]; exact hfin I hI0)`. Use the proof step `(by rw [map_mul_eq, relIndex_map_subtype]; exact hfin _ hspanδ)`. Rewrite `g1` using `[map_mul_eq, map_mul_eq, relIndex_map_subtype, relIndex_map_subtype, relIndex_map_subtype]`.

Establish `hJ2 : Submodule.span (𝓞 L) ((fun y : B => (y : L)) '' (I : Set B)) ≤ 1` using `Submodule.span_le.mpr (by rintro _ ⟨y, _, rfl⟩; exact mem_one_of_mem y.2)`. Establish `hTJ : (Submodule.span (𝓞 L) (Set.range a)).map (LinearMap.mulLeft (𝓞 L) (β : L)) = (Submodule.span (𝓞 L) ((fun y : B => (y : L)) '' (I : Set B))).map (LinearMap.mulLeft (𝓞 L) (δ : L))`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.map_le_iff_le_comap, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`.

Take `⟨y, hy, h⟩` from `(hMI (a i)).1 (haM i)`. Use `show (LinearMap.mulLeft (𝓞 L) (β : L)) (a i) ∈ Submodule.map _ _`. Rewrite using `[LinearMap.mulLeft_apply, h]`. Conclude with `⟨y, Submodule.subset_span ⟨y, hy, rfl⟩, rfl⟩`. Rewrite using `[Submodule.map_le_iff_le_comap, Submodule.span_le]`.

Introduce and unpack `_ ⟨y, hy, rfl⟩`. Establish `hx : (δ : L) * y / β ∈ M` using `(hMI _).2 ⟨y, hy, by field_simp⟩`. Use `show (LinearMap.mulLeft (𝓞 L) (δ : L)) (y : L) ∈ Submodule.map _ _`. Conclude with `⟨_, mem_span_of_local hloc hx, by simp only [LinearMap.mulLeft_apply]; field_simp⟩`. Establish `g2` using `genIndex_eq (X := (1 : Submodule (𝓞 L) L).toAddSubgroup) (J := (Submodule.span (𝓞 L) ((fun y : B => (y : L)) '' (I : Set B))).toAddSubgroup) (M := (Submodule.span (𝓞 L) (Set.range a)).toAddSubgroup) hβL hδL (fun x hx => hJ2 hx) (by rintro _ ⟨y, hy, rfl⟩; exact mul_mem_of_mem β.2 …`.

Introduce `x`. Simplify using `only [Submodule.mem_toAddSubgroup]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `hm` using `Submodule.mem_map_of_mem (f := LinearMap.mulLeft (𝓞 L) (β : L)) hx`.

Rewrite `hm` using `[hTJ]`. Take `⟨y, hy, h⟩` from `hm`. Conclude with `⟨y, hy, by simpa using h.symm⟩`. Introduce and unpack `⟨y, hy, h⟩`. Establish `hm` using `Submodule.mem_map_of_mem (f := LinearMap.mulLeft (𝓞 L) (δ : L)) hy`.

Rewrite `hm` using `[← hTJ]`. Take `⟨x', hx', h'⟩` from `hm`. Simplify using `only [LinearMap.mulLeft_apply] at h'`. Establish `hxx : x' = x` using `mul_left_cancel₀ hβL (h'.trans h.symm)`. Conclude with `hxx ▸ hx')`.

Use the proof step `(by rw [hidx I hI0 (Or.inr hIs)]; exact pow_ne_zero _ (hfin I hI0))`. Use the proof step `(by`. Rewrite using `[map_mul_eq_span δ, hidx _ hspanδ (Or.inl ⟨⟨δ, rfl⟩⟩)]`. Conclude with `pow_ne_zero _ (hfin _ hspanδ))`. Rewrite `g2` using `[map_mul_eq_span β, map_mul_eq_span δ, hidx _ hspanβ (Or.inl ⟨⟨β, rfl⟩⟩), hidx _ hspanδ (Or.inl ⟨⟨δ, rfl⟩⟩), hidx I hI0 (Or.inr hIs)]`.

Rewrite using `[g1, g2, hrank]`. Use `push_cast`. Rewrite using `[← mul_pow, ← div_pow, Real.log_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem InvertibleIdealIndex.proof (h1 : OrderIdealIndexExtension.Statement)
    (h2 : LocallyPrincipalCoprime.Statement) : InvertibleIdealIndex.Statement := by
  intro L _ _ B M ι _ a hB hBM haM hden hloc
  have := hB
  by_cases hM0 : M = ⊥
  · have ha0 : ∀ i, a i = 0 := fun i => by simpa [hM0] using haM i
    have hT0 : Submodule.span (𝓞 L) (Set.range a) = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro _ ⟨i, rfl⟩
      exact ha0 i
    simp only [hM0, hT0, Submodule.bot_toAddSubgroup, genIndex, AddSubgroup.relIndex_bot_left,
      AddSubgroup.relIndex_bot_right, card_subring_eq_zero, card_one_eq_zero]
    simp
  obtain ⟨r, s, hs, hrank, hfin, hidx⟩ := h1 L B hB
  obtain ⟨β, δ, I, hβ, hδ, hIs, hMI⟩ := h2 L B M ι a hB hBM haM hden hloc hM0 s hs
  have hβL : (β : L) ≠ 0 := fun h => hβ (Subtype.ext h)
  have hδL : (δ : L) ≠ 0 := fun h => hδ (Subtype.ext h)
  have hI0 : I ≠ ⊥ := by
    intro hI
    obtain ⟨⟨x, hxM⟩, hx0⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.mp hM0
    obtain ⟨y, hy, hxy⟩ := (hMI x).1 hxM
    rw [hI, Ideal.mem_bot] at hy
    subst hy
    have hx : x ≠ 0 := fun h => hx0 (Subtype.ext h)
    simp [hβL, hx] at hxy
  have hspanβ : Ideal.span {β} ≠ ⊥ := by rw [Ne, Ideal.span_singleton_eq_bot]; exact hβ
  have hspanδ : Ideal.span {δ} ≠ ⊥ := by rw [Ne, Ideal.span_singleton_eq_bot]; exact hδ

  have g1 := genIndex_eq (X := B.toAddSubgroup) (J := I.toAddSubgroup.map B.subtype.toAddMonoidHom)
    (M := M) hβL hδL
    (by rintro _ ⟨y, _, rfl⟩; exact y.2)
    (by rintro _ ⟨y, hy, rfl⟩; exact B.mul_mem β.2 hy)
    (by rintro _ ⟨y, hy, rfl⟩; exact B.mul_mem δ.2 hy)
    (by rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩; exact ⟨β * y, I.mul_mem_left β hy, rfl⟩)
    (by
      intro x
      rw [hMI x]
      constructor
      · rintro ⟨y, hy, h⟩
        exact ⟨y, ⟨y, hy, rfl⟩, h⟩
      · rintro ⟨_, ⟨y, hy, rfl⟩, h⟩
        exact ⟨y, hy, h⟩)
    (by rw [relIndex_map_subtype]; exact hfin I hI0)
    (by rw [map_mul_eq, relIndex_map_subtype]; exact hfin _ hspanδ)
  rw [map_mul_eq, map_mul_eq, relIndex_map_subtype, relIndex_map_subtype, relIndex_map_subtype]
    at g1

  have hJ2 : Submodule.span (𝓞 L) ((fun y : B => (y : L)) '' (I : Set B)) ≤ 1 :=
    Submodule.span_le.mpr (by rintro _ ⟨y, _, rfl⟩; exact mem_one_of_mem y.2)
  have hTJ : (Submodule.span (𝓞 L) (Set.range a)).map (LinearMap.mulLeft (𝓞 L) (β : L)) =
      (Submodule.span (𝓞 L) ((fun y : B => (y : L)) '' (I : Set B))).map
        (LinearMap.mulLeft (𝓞 L) (δ : L)) := by
    apply le_antisymm
    · rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      obtain ⟨y, hy, h⟩ := (hMI (a i)).1 (haM i)
      show (LinearMap.mulLeft (𝓞 L) (β : L)) (a i) ∈ Submodule.map _ _
      rw [LinearMap.mulLeft_apply, h]
      exact ⟨y, Submodule.subset_span ⟨y, hy, rfl⟩, rfl⟩
    · rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      have hx : (δ : L) * y / β ∈ M := (hMI _).2 ⟨y, hy, by field_simp⟩
      show (LinearMap.mulLeft (𝓞 L) (δ : L)) (y : L) ∈ Submodule.map _ _
      exact ⟨_, mem_span_of_local hloc hx, by simp only [LinearMap.mulLeft_apply]; field_simp⟩
  have g2 := genIndex_eq (X := (1 : Submodule (𝓞 L) L).toAddSubgroup)
    (J := (Submodule.span (𝓞 L) ((fun y : B => (y : L)) '' (I : Set B))).toAddSubgroup)
    (M := (Submodule.span (𝓞 L) (Set.range a)).toAddSubgroup) hβL hδL
    (fun x hx => hJ2 hx)
    (by rintro _ ⟨y, hy, rfl⟩; exact mul_mem_of_mem β.2 hy)
    (by rintro _ ⟨y, hy, rfl⟩; exact mul_mem_of_mem δ.2 hy)
    (by rintro _ ⟨y, hy, rfl⟩; exact mul_mem_of_mem β.2 hy)
    (by
      intro x
      simp only [Submodule.mem_toAddSubgroup]
      constructor
      · intro hx
        have hm := Submodule.mem_map_of_mem (f := LinearMap.mulLeft (𝓞 L) (β : L)) hx
        rw [hTJ] at hm
        obtain ⟨y, hy, h⟩ := hm
        exact ⟨y, hy, by simpa using h.symm⟩
      · rintro ⟨y, hy, h⟩
        have hm := Submodule.mem_map_of_mem (f := LinearMap.mulLeft (𝓞 L) (δ : L)) hy
        rw [← hTJ] at hm
        obtain ⟨x', hx', h'⟩ := hm
        simp only [LinearMap.mulLeft_apply] at h'
        have hxx : x' = x := mul_left_cancel₀ hβL (h'.trans h.symm)
        exact hxx ▸ hx')
    (by rw [hidx I hI0 (Or.inr hIs)]; exact pow_ne_zero _ (hfin I hI0))
    (by
      rw [map_mul_eq_span δ, hidx _ hspanδ (Or.inl ⟨⟨δ, rfl⟩⟩)]
      exact pow_ne_zero _ (hfin _ hspanδ))
  rw [map_mul_eq_span β, map_mul_eq_span δ, hidx _ hspanβ (Or.inl ⟨⟨β, rfl⟩⟩),
    hidx _ hspanδ (Or.inl ⟨⟨δ, rfl⟩⟩), hidx I hI0 (Or.inr hIs)] at g2
  rw [g1, g2, hrank]
  push_cast
  rw [← mul_pow, ← div_pow, Real.log_pow]
  ring

end

end GroundTheory.Heights₂.Heights
