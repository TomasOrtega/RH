import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlaceEqOneOfNotMem
open NumberField Matrix IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

namespace GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.Comm

variable {L : Type} [Field L] [NumberField L] {n : ℕ}

noncomputable def mulBy (b : 𝓞 L) : (Fin n → L) →+ (Fin n → L) :=
  DistribSMul.toAddMonoidHom _ b

/- English proof (translation)
Simplify using `[mulBy, Algebra.smul_def]`.
-/
theorem mulBy_apply (b : 𝓞 L) (x : Fin n → L) (i : Fin n) : mulBy b x i = (b : L) * x i := by
  simp [mulBy, Algebra.smul_def]

/- English proof (translation)
Simplify using `using hb`.
-/
theorem coe_ne_zero {b : 𝓞 L} (hb : b ≠ 0) : (b : L) ≠ 0 := by
  simpa using hb

/- English proof (translation)
Introduce `x y h`. Use function extensionality and compare the values at `i`. Use `congrFun h i` as an intermediate fact. Rewrite `this` using `[mulBy_apply, mulBy_apply]`. Conclude with `mul_left_cancel₀ (coe_ne_zero hb) this`.
-/
theorem mulBy_injective {b : 𝓞 L} (hb : b ≠ 0) :
    Function.Injective (mulBy (L := L) (n := n) b) := by
  intro x y h
  funext i
  have := congrFun h i
  rw [mulBy_apply, mulBy_apply] at this
  exact mul_left_cancel₀ (coe_ne_zero hb) this

noncomputable def incl : (Fin n → 𝓞 L) →+ (Fin n → L) where
  toFun z i := (z i : L)
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp

/- English proof (translation)
Introduce `x y h`. Use function extensionality and compare the values at `i`. Use `congrFun h i` as an intermediate fact. Conclude with `RingOfIntegers.coe_injective this`.
-/
theorem incl_injective : Function.Injective (incl (L := L) (n := n)) := by
  intro x y h
  funext i
  have := congrFun h i
  exact RingOfIntegers.coe_injective this

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [Submodule.mem_toAddSubgroup, mem_frame_one, AddSubgroup.mem_map, AddSubgroup.mem_top, true_and]`. Prove the components needed by the constructor for the conclusion. Introduce `h choose z hz using h`. Conclude with `⟨z, funext fun i => (hz i).symm⟩`.

Introduce and unpack `⟨z, rfl⟩ i`. Conclude with `⟨z i, rfl⟩`.
-/
theorem frame_one_eq :
    (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup =
      (⊤ : AddSubgroup (Fin n → 𝓞 L)).map incl := by
  ext x
  simp only [Submodule.mem_toAddSubgroup, mem_frame_one, AddSubgroup.mem_map, AddSubgroup.mem_top,
    true_and]
  constructor
  · intro h
    choose z hz using h
    exact ⟨z, funext fun i => (hz i).symm⟩
  · rintro ⟨z, rfl⟩ i
    exact ⟨z i, rfl⟩

/- English proof (translation)
Set `I : Ideal (𝓞 L)` to `Ideal.span {b}`. Establish `hI : I ≠ ⊥` using `by simpa [I] using hb`. Use `haveI : Finite (𝓞 L ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI`. Set `f : (Fin n → 𝓞 L) →+ (Fin n → 𝓞 L ⧸ I)` to `(Ideal.Quotient.mk I).toAddMonoidHom.compLeft (Fin n)`. Set `m : (Fin n → 𝓞 L) →+ (Fin n → 𝓞 L)` to `DistribSMul.toAddMonoidHom _ b`.

Establish `hk : f.ker ≤ m.range`. Introduce `z hz`. Establish `h1 : ∀ i, ∃ c, z i = b * c` using `fun i => by`. Establish `: (Ideal.Quotient.mk I) (z i) = 0` using `congrFun (AddMonoidHom.mem_ker.1 hz) i`. Conclude with `Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 this) |>.imp fun c hc => by rw [← hc, mul_comm]`.

Use `choose c hc using h1`. Conclude with `⟨c, funext fun i => by simp [m, hc i]⟩`. Establish `hf : f.ker.index ≠ 0`. Rewrite using `[AddSubgroup.index_ker]`. Conclude with `Nat.card_pos.ne'`.

Establish `hm : m.range.index ≠ 0` using `fun h => hf (by`. Use `AddSubgroup.index_dvd_of_le hk` as an intermediate fact. Rewrite `this` using `[h]`. Conclude with `Nat.eq_zero_of_zero_dvd this)`. Establish `e : (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup.map (mulBy b) = m.range.map incl`.

Rewrite using `[frame_one_eq]`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨z, -, rfl⟩, rfl⟩`. Use `⟨m z, ⟨z, rfl⟩, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Simplify using `[m, incl, mulBy_apply]`. Introduce and unpack `⟨_, ⟨z, rfl⟩, rfl⟩`. Use `⟨incl z, ⟨z, trivial, rfl⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Simplify using `[m, incl, mulBy_apply]`. Rewrite using `[e, frame_one_eq, AddSubgroup.relIndex_map_map_of_injective _ _ incl_injective, AddSubgroup.relIndex_top_right]`. Conclude with `hm`.
-/
theorem relIndex_mulBy_ne_zero {b : 𝓞 L} (hb : b ≠ 0) :
    ((frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup.map (mulBy b)).relIndex
      (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup ≠ 0 := by
  classical
  let I : Ideal (𝓞 L) := Ideal.span {b}
  have hI : I ≠ ⊥ := by simpa [I] using hb
  haveI : Finite (𝓞 L ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  let f : (Fin n → 𝓞 L) →+ (Fin n → 𝓞 L ⧸ I) :=
    (Ideal.Quotient.mk I).toAddMonoidHom.compLeft (Fin n)
  let m : (Fin n → 𝓞 L) →+ (Fin n → 𝓞 L) := DistribSMul.toAddMonoidHom _ b
  have hk : f.ker ≤ m.range := by
    intro z hz
    have h1 : ∀ i, ∃ c, z i = b * c := fun i => by
      have : (Ideal.Quotient.mk I) (z i) = 0 := congrFun (AddMonoidHom.mem_ker.1 hz) i
      exact Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 this) |>.imp
        fun c hc => by rw [← hc, mul_comm]
    choose c hc using h1
    exact ⟨c, funext fun i => by simp [m, hc i]⟩
  have hf : f.ker.index ≠ 0 := by
    rw [AddSubgroup.index_ker]
    exact Nat.card_pos.ne'
  have hm : m.range.index ≠ 0 := fun h => hf (by
    have := AddSubgroup.index_dvd_of_le hk
    rw [h] at this
    exact Nat.eq_zero_of_zero_dvd this)
  have e : (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup.map (mulBy b) =
      m.range.map incl := by
    rw [frame_one_eq]
    ext x
    constructor
    · rintro ⟨_, ⟨z, -, rfl⟩, rfl⟩
      refine ⟨m z, ⟨z, rfl⟩, ?_⟩
      funext i
      simp [m, incl, mulBy_apply]
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      refine ⟨incl z, ⟨z, trivial, rfl⟩, ?_⟩
      funext i
      simp [m, incl, mulBy_apply]
  rw [e, frame_one_eq, AddSubgroup.relIndex_map_map_of_injective _ _ incl_injective,
    AddSubgroup.relIndex_top_right]
  exact hm

/- English proof (translation)
Set `s : Finset L` to `hS.toFinset.biUnion fun w => (Finset.univ : Finset (Fin n × Fin n)).biUnion fun p => {T w p.1 p.2, (T w)⁻¹ p.1 p.2}`. Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 L)) s`. Establish `hint : ∀ x ∈ s, ∀ w : FinitePlace L, w (((b : 𝓞 L) : L) * x) ≤ 1`. Introduce `x hx w`. Take `⟨r, hr⟩` from `hb x hx`.

Establish `: ((b : 𝓞 L) : L) * x = (r : L)`. Establish `h2 : (b : 𝓞 L) • x = ((b : 𝓞 L) : L) * x` using `Algebra.smul_def _ _`. Rewrite using `[← h2, ← hr]`. Rewrite using `[this]`. Conclude with `place_int_le_one w r`.

Use `⟨b, nonZeroDivisors.ne_zero b.2, fun w i j => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hw : UnitAt w (T w)`. Conclude with `⟨place_mul_le_one w (place_int_le_one w _) (hw.1 i j), place_mul_le_one w (place_int_le_one w _) (hw.inv_le_one i j)⟩`. Establish `hwS : w ∈ hS.toFinset` using `by simpa using hw`. Prove the components needed by the constructor for the conclusion.

Use `hint _ (Finset.mem_biUnion.2 ⟨w, hwS, Finset.mem_biUnion.2 ⟨(i, j), Finset.mem_univ _, ?_⟩⟩) w` and prove the remaining obligations. Simplify using the standard rewrite rules. Use `hint _ (Finset.mem_biUnion.2 ⟨w, hwS, Finset.mem_biUnion.2 ⟨(i, j), Finset.mem_univ _, ?_⟩⟩) w` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem exists_clearing (T : FinitePlace L → Matrix (Fin n) (Fin n) L)
    (hS : {v : FinitePlace L | ¬ UnitAt v (T v)}.Finite) :
    ∃ a : 𝓞 L, a ≠ 0 ∧ ∀ (w : FinitePlace L) (i j : Fin n), w ((a : L) * T w i j) ≤ 1 ∧ w ((a : L) * (T w)⁻¹ i j) ≤ 1 := by
  classical
  let s : Finset L := hS.toFinset.biUnion fun w =>
    (Finset.univ : Finset (Fin n × Fin n)).biUnion fun p => {T w p.1 p.2, (T w)⁻¹ p.1 p.2}
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 L)) s
  have hint : ∀ x ∈ s, ∀ w : FinitePlace L, w (((b : 𝓞 L) : L) * x) ≤ 1 := by
    intro x hx w
    obtain ⟨r, hr⟩ := hb x hx
    have : ((b : 𝓞 L) : L) * x = (r : L) := by
      have h2 : (b : 𝓞 L) • x = ((b : 𝓞 L) : L) * x := Algebra.smul_def _ _
      rw [← h2, ← hr]
    rw [this]
    exact place_int_le_one w r
  refine ⟨b, nonZeroDivisors.ne_zero b.2, fun w i j => ?_⟩
  by_cases hw : UnitAt w (T w)
  · exact ⟨place_mul_le_one w (place_int_le_one w _) (hw.1 i j),
      place_mul_le_one w (place_int_le_one w _) (hw.inv_le_one i j)⟩
  · have hwS : w ∈ hS.toFinset := by simpa using hw
    constructor
    · refine hint _ (Finset.mem_biUnion.2 ⟨w, hwS, Finset.mem_biUnion.2 ⟨(i, j), Finset.mem_univ _, ?_⟩⟩) w
      simp
    · refine hint _ (Finset.mem_biUnion.2 ⟨w, hwS, Finset.mem_biUnion.2 ⟨(i, j), Finset.mem_univ _, ?_⟩⟩) w
      simp

/- English proof (translation)
Introduce and unpack `_ ⟨x, hx, rfl⟩`. Establish `hx' : x ∈ frame (1 : Matrix (Fin n) (Fin n) L)` using `hx`. Take `hxi` from `mem_frame_one.1 hx'`. Use `show mulBy a x ∈ glued T`. Rewrite using `[glued, Submodule.mem_iInf]`.

Introduce `w`. Use `mem_locAt_frame.2 ⟨((a : L) • (T w)⁻¹) *ᵥ x, fun i => ?_, ?_⟩` and prove the remaining obligations. Use `place_sum_le_one w Finset.univ (fun j => ((a : L) • (T w)⁻¹) i j * x j) fun j _ => ?_` and prove the remaining obligations. Take `⟨r, hr⟩` from `hxi j`. Rewrite using `[hr]`.

Conclude with `place_mul_le_one w (ha w i j) (place_int_le_one w r)`. Establish `hu : IsUnit (T w).det` using `IsUnit.mk0 _ (hT w)`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_smul, Matrix.mul_nonsing_inv _ hu, Matrix.smul_mulVec, Matrix.one_mulVec]`. Use function extensionality and compare the values at `i`. Simplify using `[mulBy_apply]`.
-/
theorem mulBy_frame_le_glued (T : FinitePlace L → Matrix (Fin n) (Fin n) L)
    (hT : ∀ v, (T v).det ≠ 0) {a : 𝓞 L}
    (ha : ∀ (w : FinitePlace L) (i j : Fin n), w ((a : L) * (T w)⁻¹ i j) ≤ 1) :
    (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup.map (mulBy a) ≤ (glued T).toAddSubgroup := by
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ frame (1 : Matrix (Fin n) (Fin n) L) := hx
  obtain hxi := mem_frame_one.1 hx'
  show mulBy a x ∈ glued T
  rw [glued, Submodule.mem_iInf]
  intro w
  refine mem_locAt_frame.2 ⟨((a : L) • (T w)⁻¹) *ᵥ x, fun i => ?_, ?_⟩
  · refine place_sum_le_one w Finset.univ (fun j => ((a : L) • (T w)⁻¹) i j * x j) fun j _ => ?_
    obtain ⟨r, hr⟩ := hxi j
    rw [hr]
    exact place_mul_le_one w (ha w i j) (place_int_le_one w r)
  · have hu : IsUnit (T w).det := IsUnit.mk0 _ (hT w)
    rw [Matrix.mulVec_mulVec, Matrix.mul_smul, Matrix.mul_nonsing_inv _ hu, Matrix.smul_mulVec,
      Matrix.one_mulVec]
    funext i
    simp [mulBy_apply]

/- English proof (translation)
Introduce and unpack `_ ⟨x, hx, rfl⟩`. Establish `hx' : x ∈ glued T` using `hx`. Use `show mulBy a x ∈ frame (1 : Matrix (Fin n) (Fin n) L)`. Rewrite using `[← iInf_locAt_frame_one, Submodule.mem_iInf]`. Introduce `w`.

Take `⟨y, hy, hxy⟩` from `mem_locAt_frame.1 ((Submodule.mem_iInf _).1 hx' w)`. Use `mem_locAt_frame_one.2 fun i => ?_` and prove the remaining obligations. Rewrite using `[mulBy_apply, hxy, Matrix.mulVec, dotProduct, Finset.mul_sum]`. Use `place_sum_le_one w Finset.univ _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc]`.

Conclude with `place_mul_le_one w (ha w i j) (hy j)`.
-/
theorem mulBy_glued_le_frame (T : FinitePlace L → Matrix (Fin n) (Fin n) L) {a : 𝓞 L}
    (ha : ∀ (w : FinitePlace L) (i j : Fin n), w ((a : L) * T w i j) ≤ 1) :
    (glued T).toAddSubgroup.map (mulBy a) ≤ (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup := by
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ glued T := hx
  show mulBy a x ∈ frame (1 : Matrix (Fin n) (Fin n) L)
  rw [← iInf_locAt_frame_one, Submodule.mem_iInf]
  intro w
  obtain ⟨y, hy, hxy⟩ := mem_locAt_frame.1 ((Submodule.mem_iInf _).1 hx' w)
  refine mem_locAt_frame_one.2 fun i => ?_
  rw [mulBy_apply, hxy, Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine place_sum_le_one w Finset.univ _ fun j _ => ?_
  rw [← mul_assoc]
  exact place_mul_le_one w (ha w i j) (hy j)

/- English proof (translation)
Take `⟨a, ha0, ha⟩` from `exists_clearing T hS`. Use `set F := (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup with hF`. Use `set G := (glued T).toAddSubgroup with hG`. Establish `h1 : F.map (mulBy a) ≤ G` using `mulBy_frame_le_glued T hT fun w i j => (ha w i j).2`. Establish `h2 : G.map (mulBy a) ≤ F` using `mulBy_glued_le_frame T fun w i j => (ha w i j).1`.

Establish `i1 : (F.map (mulBy a)).relIndex F ≠ 0` using `relIndex_mulBy_ne_zero ha0`. Establish `hcomp : (F.map (mulBy a)).map (mulBy a) = F.map (mulBy (a * a))`. Rewrite using `[AddSubgroup.map_map]`. Use `congr 1`. Use extensionality with `x i`.

Simplify using `[mulBy_apply, mul_assoc]`. Establish `i2 : ((F.map (mulBy a)).map (mulBy a)).relIndex F ≠ 0`. Rewrite using `[hcomp]`. Conclude with `relIndex_mulBy_ne_zero (mul_ne_zero ha0 ha0)`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Use `AddSubgroup.relIndex_dvd_of_le_left F h1` as an intermediate fact. Rewrite `this` using `[h]`. Conclude with `i1 (Nat.eq_zero_of_zero_dvd this)`. Establish `i3 : ((F.map (mulBy a)).map (mulBy a)).relIndex (G.map (mulBy a)) ≠ 0` using `AddSubgroup.relIndex_ne_zero_trans i2 (by`.

Rewrite using `[AddSubgroup.relIndex_eq_one.2 h2]`. Conclude with `one_ne_zero)`. Rewrite `i3` using `[AddSubgroup.relIndex_map_map_of_injective _ _ (mulBy_injective ha0)]`. Introduce `h`. Use `AddSubgroup.relIndex_dvd_of_le_left G (show F.map (mulBy a) ≤ F from ?_)` as an intermediate fact.

Rewrite `this` using `[h]`. Conclude with `i3 (Nat.eq_zero_of_zero_dvd this)`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Establish `hx' : x ∈ frame (1 : Matrix (Fin n) (Fin n) L)` using `hx`. Conclude with `(frame (1 : Matrix (Fin n) (Fin n) L)).smul_mem a hx'`.
-/
theorem glued_commensurable (L : Type) [Field L] [NumberField L] (n : ℕ)
    (T : FinitePlace L → Matrix (Fin n) (Fin n) L) (hT : ∀ v, (T v).det ≠ 0)
    (hS : {v : FinitePlace L | ¬ UnitAt v (T v)}.Finite) :
    (glued T).toAddSubgroup.relIndex (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup ≠ 0 ∧
      (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup.relIndex (glued T).toAddSubgroup ≠ 0 := by
  obtain ⟨a, ha0, ha⟩ := exists_clearing T hS
  set F := (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup with hF
  set G := (glued T).toAddSubgroup with hG
  have h1 : F.map (mulBy a) ≤ G := mulBy_frame_le_glued T hT fun w i j => (ha w i j).2
  have h2 : G.map (mulBy a) ≤ F := mulBy_glued_le_frame T fun w i j => (ha w i j).1
  have i1 : (F.map (mulBy a)).relIndex F ≠ 0 := relIndex_mulBy_ne_zero ha0
  have hcomp : (F.map (mulBy a)).map (mulBy a) = F.map (mulBy (a * a)) := by
    rw [AddSubgroup.map_map]
    congr 1
    ext x i
    simp [mulBy_apply, mul_assoc]
  have i2 : ((F.map (mulBy a)).map (mulBy a)).relIndex F ≠ 0 := by
    rw [hcomp]
    exact relIndex_mulBy_ne_zero (mul_ne_zero ha0 ha0)
  constructor
  · intro h
    have := AddSubgroup.relIndex_dvd_of_le_left F h1
    rw [h] at this
    exact i1 (Nat.eq_zero_of_zero_dvd this)
  · have i3 : ((F.map (mulBy a)).map (mulBy a)).relIndex (G.map (mulBy a)) ≠ 0 :=
      AddSubgroup.relIndex_ne_zero_trans i2 (by
        rw [AddSubgroup.relIndex_eq_one.2 h2]; exact one_ne_zero)
    rw [AddSubgroup.relIndex_map_map_of_injective _ _ (mulBy_injective ha0)] at i3
    intro h
    have := AddSubgroup.relIndex_dvd_of_le_left G (show F.map (mulBy a) ≤ F from ?_)
    · rw [h] at this
      exact i3 (Nat.eq_zero_of_zero_dvd this)
    · rintro _ ⟨x, hx, rfl⟩
      have hx' : x ∈ frame (1 : Matrix (Fin n) (Fin n) L) := hx
      exact (frame (1 : Matrix (Fin n) (Fin n) L)).smul_mem a hx'

end GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.Comm
