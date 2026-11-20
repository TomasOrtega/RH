import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DualHalfLevelMarkingExistsAndMatchStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.AdmissibleSmulIffOfCoprime

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.CoverFourier

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r n : ℕ}

omit [IsCMField E] in

/- English proof (translation)
Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨v, hv, u, hu, rfl⟩` from `hy`. Establish `: s • vecMulVec v u b = (s * v b) • u`. Use function extensionality and compare the values at `j`.

Simplify using `[vecMulVec_apply, _root_.mul_assoc]`. Rewrite using `[this]`. Conclude with `TensLat.int_smul_mem (hs v hv b) hu`. Consider the case `zero => have : s • (0 : Matrix (Fin n) (Fin r) E) b = 0 := by funext j; simp`. Rewrite using `[this]`.

Conclude with `L.zero_mem`. Consider the case `add y y' _ _ h h'`. Establish `: s • (y + y') b = s • y b + s • y' b` using `by funext j; simp [mul_add]`. Rewrite using `[this]`. Conclude with `L.add_mem h h'`.

Consider the case `neg y _ h`. Establish `: s • (-y) b = -(s • y b)` using `by funext j; simp`. Rewrite using `[this]`. Conclude with `L.neg_mem h`.
-/
theorem row_mem {Λ : Lt E n} {L : Lt E r} {s : E} (hs : ∀ v ∈ Λ, ∀ b, IsIntegral ℤ (s * v b))
    {y : Matrix (Fin n) (Fin r) E} (hy : y ∈ tens Λ L) (b : Fin n) : s • y b ∈ L := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨v, hv, u, hu, rfl⟩ := hy
    have : s • vecMulVec v u b = (s * v b) • u := by
      funext j; simp [vecMulVec_apply, _root_.mul_assoc]
    rw [this]; exact TensLat.int_smul_mem (hs v hv b) hu
  | zero => have : s • (0 : Matrix (Fin n) (Fin r) E) b = 0 := by funext j; simp
            rw [this]; exact L.zero_mem
  | add y y' _ _ h h' =>
    have : s • (y + y') b = s • y b + s • y' b := by funext j; simp [mul_add]
    rw [this]; exact L.add_mem h h'
  | neg y _ h =>
    have : s • (-y) b = -(s • y b) := by funext j; simp
    rw [this]; exact L.neg_mem h

omit [IsCMField E] in

/- English proof (translation)
Establish `: s • z = ∑ b, vecMulVec (Pi.single b s : Fin n → E) (z b)`. Use extensionality with `i j`. Simplify using `[Matrix.sum_apply, vecMulVec_apply, Pi.single_apply]`. Rewrite using `[this]`. Conclude with `AddSubgroup.sum_mem _ fun b _ => AddSubgroup.subset_closure ⟨_, hs b, _, hz b, rfl⟩`.
-/
theorem smul_mem_tens {Λ : Lt E n} {L : Lt E r} {s : E} (hs : ∀ b, (Pi.single b s : Fin n → E) ∈ Λ)
    {z : Matrix (Fin n) (Fin r) E} (hz : ∀ b, z b ∈ L) : s • z ∈ tens Λ L := by
  have : s • z = ∑ b, vecMulVec (Pi.single b s : Fin n → E) (z b) := by
    ext i j
    simp [Matrix.sum_apply, vecMulVec_apply, Pi.single_apply]
  rw [this]
  exact AddSubgroup.sum_mem _ fun b _ => AddSubgroup.subset_closure ⟨_, hs b, _, hz b, rfl⟩

omit [IsCMField E] in
/- English proof (translation)
Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨v, hv, u, hu, rfl⟩` from `hy`. Use `AddSubgroup.subset_closure ⟨v, hv, _, h u hu, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`.

Simplify using `[vecMulVec_apply, mul_left_comm]`. Consider the case `zero => rw [smul_zero]`. Conclude with `zero_mem _`. Consider the case `add y y' _ _ h h' => rw [smul_add]`. Conclude with `add_mem h h'`.

Consider the case `neg y _ h => rw [smul_neg]`. Conclude with `neg_mem h`.
-/
theorem tens_smul {Λ : Lt E n} {L L' : Lt E r} {a : E} (h : ∀ u ∈ L, a • u ∈ L')
    {y : Matrix (Fin n) (Fin r) E} (hy : y ∈ tens Λ L) : a • y ∈ tens Λ L' := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨v, hv, u, hu, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨v, hv, _, h u hu, ?_⟩
    ext i j; simp [vecMulVec_apply, mul_left_comm]
  | zero => rw [smul_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | neg y _ h => rw [smul_neg]; exact neg_mem h

omit [IsCMField E] in
/- English proof (translation)
Take `⟨a, ha', b, hb', e⟩` from `Ideal.isCoprime_iff_exists.1 h`. Establish `: u = a • u + b • u` using `by rw [← add_smul, e, one_smul]`. Rewrite using `[this]`. Use `add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[Submodule.mul_smul]`.

Conclude with `Submodule.smul_mem_smul ha' hb`. Rewrite using `[mul_comm, Submodule.mul_smul]`. Conclude with `Submodule.smul_mem_smul hb' ha`.
-/
theorem mem_mul_smul {L : Lt E r} {𝔞 𝔟 : Ideal (𝓞 E)} (h : IsCoprime 𝔞 𝔟) {u : Fin r → E}
    (ha : u ∈ 𝔞 • L) (hb : u ∈ 𝔟 • L) : u ∈ (𝔞 * 𝔟) • L := by
  obtain ⟨a, ha', b, hb', e⟩ := Ideal.isCoprime_iff_exists.1 h
  have : u = a • u + b • u := by rw [← add_smul, e, one_smul]
  rw [this]
  refine add_mem ?_ ?_
  · rw [Submodule.mul_smul]; exact Submodule.smul_mem_smul ha' hb
  · rw [mul_comm, Submodule.mul_smul]; exact Submodule.smul_mem_smul hb' ha

omit [IsCMField E] in

/- English proof (translation)
Take `⟨e, he, e', he', ee⟩` from `Ideal.isCoprime_iff_exists.1 hcop`. Establish `hle : 𝔟 • L ≤ L` using `Submodule.smul_le_right`. Establish `hrel : ∀ y y' : tens Λ (𝔟 • L), (QuotientAddGroup.mk y : tens Λ (𝔟 • L) ⧸ (tens Λ ((𝔟 * 𝔪) • L)).addSubgroupOf _) = QuotientAddGroup.mk y' ↔ ∀ b, (s : E) • y.1 b - (s : E) • y'.1 b ∈ 𝔪 • L`. Introduce `y y'`. Rewrite using `[eq_comm, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]`.

Establish `hw : (-y' + y).1 ∈ tens Λ (𝔟 • L)` using `(-y' + y).2`. Establish `e1 : ∀ b, (s : E) • y.1 b - (s : E) • y'.1 b = (s : E) • (-y' + y).1 b` using `fun b => by`. Use function extensionality and compare the values at `j`. Simplify using `[Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [e1]`. Generalize the expression as in `(-y' + y).1 = w at hw`. Prove the components needed by the constructor for the conclusion. Introduce `h b`. Conclude with `Submodule.smul_mono_left Ideal.mul_le_right (row_mem hs1 h b)`.

Introduce `h`. Establish `h1 : (s : E) • ((s : E) • w) ∈ tens Λ ((𝔟 * 𝔪) • L)` using `smul_mem_tens hs2 fun b => mem_mul_smul hcop (row_mem hs1 hw b) (h b)`. Establish `h2 : (((s + 1) * (s - 1) : 𝓞 E) : E) • w ∈ tens Λ ((𝔟 * 𝔪) • L)` using `tens_smul (fun u hu => by`. Rewrite using `[mul_comm 𝔟, Submodule.mul_smul]`. Conclude with `Submodule.smul_mem_smul (𝔪.mul_mem_left _ hs) hu) hw`.

Establish `: w = (s : E) • ((s : E) • w) - (((s + 1) * (s - 1) : 𝓞 E) : E) • w`. Use extensionality with `i j`. Simplify using `[Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `sub_mem h1 h2`. Establish `hy : ∀ i, (s : E) • ((e : E) • z i) ∈ tens Λ (𝔟 • L)` using `fun i => smul_mem_tens hs2 fun b => Submodule.smul_mem_smul he (hz i b)`. Establish `hyz : ∀ i b, (s : E) • ((s : E) • ((e : E) • z i)) b - z i b ∈ 𝔪 • L` using `fun i b => by`. Establish `h1 : s * s * e - 1 ∈ 𝔪`. Establish `: s * s * e - 1 = (s + 1) * e * (s - 1) - e'` using `by linear_combination ee`.

Rewrite using `[this]`. Conclude with `sub_mem (𝔪.mul_mem_left _ hs) he'`. Establish `: (s : E) • ((s : E) • ((e : E) • z i)) b - z i b = (s * s * e - 1) • z i b`. Use function extensionality and compare the values at `j`. Simplify using `[Algebra.smul_def]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `Submodule.smul_mem_smul h1 (hz i b)`. Set `g : T → tens Λ (𝔟 • L) ⧸ (tens Λ ((𝔟 * 𝔪) • L)).addSubgroupOf _` to `fun i => QuotientAddGroup.mk ⟨_, hy i⟩`. Establish `hg : ∀ (cl : tens Λ (𝔟 • L) ⧸ (tens Λ ((𝔟 * 𝔪) • L)).addSubgroupOf _) i, cl = g i ↔ ∀ b, (s : E) • (cl.out : Matrix (Fin n) (Fin r) E) b - z i b ∈ 𝔪 • L` using `fun cl i => by conv_lhs => rw [← QuotientAddGroup.out_eq' cl]`.

Rewrite using `[hrel]`. Use `forall_congr' fun b => ⟨fun h => ?_, fun h => ?_⟩` and prove the remaining obligations. Simplify using `using add_mem h (hyz i b)`. Simplify using `using sub_mem h (hyz i b)`. Establish `hrow : ∀ (cl : tens Λ (𝔟 • L) ⧸ (tens Λ ((𝔟 * 𝔪) • L)).addSubgroupOf _) b, ((s : E) • (cl.out : Matrix (Fin n) (Fin r) E)) b ∈ L` using `fun cl b => hle (row_mem hs1 cl.out.2 b)`.

Establish `hginj : Function.Injective g` using `fun i j h => hinj i j fun b => by`. Simplify using `using sub_mem ((hg (g i) j).1 h b) ((hg (g i) i).1 rfl b)`. Establish `hval : ∀ i, G ((g i).out : Matrix (Fin n) (Fin r) E) = G (z i)` using `fun i => (hGs _ (g i).out.2).trans (hG _ _ (hrow _) ((hg _ i).1 rfl))`. Simplify using `only [← hval]`. Rewrite using `[← finsum_mem_range (f := fun cl => G (cl.out : Matrix (Fin n) (Fin r) E)) hginj, ← finsum_mem_univ]`.

Use `finsum_mem_inter_support_eq' _ _ _ fun cl hcl => ⟨fun _ => ?_, fun _ => trivial⟩` and prove the remaining obligations. Take `⟨i, hi⟩` from `hsupp _ (hrow cl) (by rw [← hGs _ cl.out.2]; exact hcl)`. Conclude with `⟨i, ((hg cl i).2 hi).symm⟩`.
-/
theorem finsum_tens {Λ : Lt E n} {L : Lt E r} {𝔟 𝔪 : Ideal (𝓞 E)} (hcop : IsCoprime 𝔟 𝔪) {s : 𝓞 E}
    (hs : s - 1 ∈ 𝔪) (hs1 : ∀ v ∈ Λ, ∀ b, IsIntegral ℤ ((s : E) * v b))
    (hs2 : ∀ b, (Pi.single b (s : E) : Fin n → E) ∈ Λ) (G : Matrix (Fin n) (Fin r) E → ℂ)
    (hGs : ∀ y ∈ tens Λ (𝔟 • L), G y = G ((s : E) • y))
    (hG : ∀ z z' : Matrix (Fin n) (Fin r) E, (∀ b, z b ∈ L) → (∀ b, z b - z' b ∈ 𝔪 • L) → G z = G z')
    {T : Type} (z : T → Matrix (Fin n) (Fin r) E) (hz : ∀ i b, z i b ∈ L)
    (hinj : ∀ i j, (∀ b, z i b - z j b ∈ 𝔪 • L) → i = j)
    (hsupp : ∀ w : Matrix (Fin n) (Fin r) E, (∀ b, w b ∈ L) → G w ≠ 0 → ∃ i, ∀ b, w b - z i b ∈ 𝔪 • L) :
    ∑ᶠ cl : tens Λ (𝔟 • L) ⧸ (tens Λ ((𝔟 * 𝔪) • L)).addSubgroupOf _,
      G (cl.out : Matrix (Fin n) (Fin r) E) = ∑ᶠ i, G (z i) := by
  obtain ⟨e, he, e', he', ee⟩ := Ideal.isCoprime_iff_exists.1 hcop
  have hle : 𝔟 • L ≤ L := Submodule.smul_le_right
  have hrel : ∀ y y' : tens Λ (𝔟 • L), (QuotientAddGroup.mk y :
      tens Λ (𝔟 • L) ⧸ (tens Λ ((𝔟 * 𝔪) • L)).addSubgroupOf _) = QuotientAddGroup.mk y' ↔
      ∀ b, (s : E) • y.1 b - (s : E) • y'.1 b ∈ 𝔪 • L := by
    intro y y'
    rw [eq_comm, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    have hw : (-y' + y).1 ∈ tens Λ (𝔟 • L) := (-y' + y).2
    have e1 : ∀ b, (s : E) • y.1 b - (s : E) • y'.1 b = (s : E) • (-y' + y).1 b := fun b => by
      funext j; simp [Algebra.smul_def]; ring
    simp only [e1]
    generalize (-y' + y).1 = w at hw
    constructor
    · intro h b
      exact Submodule.smul_mono_left Ideal.mul_le_right (row_mem hs1 h b)
    · intro h
      have h1 : (s : E) • ((s : E) • w) ∈ tens Λ ((𝔟 * 𝔪) • L) :=
        smul_mem_tens hs2 fun b => mem_mul_smul hcop (row_mem hs1 hw b) (h b)
      have h2 : (((s + 1) * (s - 1) : 𝓞 E) : E) • w ∈ tens Λ ((𝔟 * 𝔪) • L) :=
        tens_smul (fun u hu => by
          rw [mul_comm 𝔟, Submodule.mul_smul]
          exact Submodule.smul_mem_smul (𝔪.mul_mem_left _ hs) hu) hw
      have : w = (s : E) • ((s : E) • w) - (((s + 1) * (s - 1) : 𝓞 E) : E) • w := by
        ext i j; simp [Algebra.smul_def]; ring
      rw [this]; exact sub_mem h1 h2
  have hy : ∀ i, (s : E) • ((e : E) • z i) ∈ tens Λ (𝔟 • L) := fun i =>
    smul_mem_tens hs2 fun b => Submodule.smul_mem_smul he (hz i b)
  have hyz : ∀ i b, (s : E) • ((s : E) • ((e : E) • z i)) b - z i b ∈ 𝔪 • L := fun i b => by
    have h1 : s * s * e - 1 ∈ 𝔪 := by
      have : s * s * e - 1 = (s + 1) * e * (s - 1) - e' := by linear_combination ee
      rw [this]; exact sub_mem (𝔪.mul_mem_left _ hs) he'
    have : (s : E) • ((s : E) • ((e : E) • z i)) b - z i b = (s * s * e - 1) • z i b := by
      funext j; simp [Algebra.smul_def]; ring
    rw [this]; exact Submodule.smul_mem_smul h1 (hz i b)
  let g : T → tens Λ (𝔟 • L) ⧸ (tens Λ ((𝔟 * 𝔪) • L)).addSubgroupOf _ :=
    fun i => QuotientAddGroup.mk ⟨_, hy i⟩
  have hg : ∀ (cl : tens Λ (𝔟 • L) ⧸ (tens Λ ((𝔟 * 𝔪) • L)).addSubgroupOf _) i, cl = g i ↔
      ∀ b, (s : E) • (cl.out : Matrix (Fin n) (Fin r) E) b - z i b ∈ 𝔪 • L := fun cl i => by
    conv_lhs => rw [← QuotientAddGroup.out_eq' cl]
    rw [hrel]
    refine forall_congr' fun b => ⟨fun h => ?_, fun h => ?_⟩
    · simpa using add_mem h (hyz i b)
    · simpa using sub_mem h (hyz i b)
  have hrow : ∀ (cl : tens Λ (𝔟 • L) ⧸ (tens Λ ((𝔟 * 𝔪) • L)).addSubgroupOf _) b,
      ((s : E) • (cl.out : Matrix (Fin n) (Fin r) E)) b ∈ L := fun cl b => hle (row_mem hs1 cl.out.2 b)
  have hginj : Function.Injective g := fun i j h => hinj i j fun b => by
    simpa using sub_mem ((hg (g i) j).1 h b) ((hg (g i) i).1 rfl b)
  have hval : ∀ i, G ((g i).out : Matrix (Fin n) (Fin r) E) = G (z i) := fun i =>
    (hGs _ (g i).out.2).trans (hG _ _ (hrow _) ((hg _ i).1 rfl))
  simp only [← hval]
  rw [← finsum_mem_range (f := fun cl => G (cl.out : Matrix (Fin n) (Fin r) E)) hginj, ← finsum_mem_univ]
  refine finsum_mem_inter_support_eq' _ _ _ fun cl hcl => ⟨fun _ => ?_, fun _ => trivial⟩
  obtain ⟨i, hi⟩ := hsupp _ (hrow cl) (by rw [← hGs _ cl.out.2]; exact hcl)
  exact ⟨i, ((hg cl i).2 hi).symm⟩

variable {X : Data E r}

/- English proof (translation)
Take `⟨s, hs, h⟩` from `h`. Conclude with `⟨s, hs, by rw [← neg_sub, smul_neg]; exact neg_mem h⟩`.
-/
theorem cong_symm {𝔞 : Ideal (𝓞 E)} {u v : Fin r → E} (h : Cong X 𝔞 u v) : Cong X 𝔞 v u := by
  obtain ⟨s, hs, h⟩ := h
  exact ⟨s, hs, by rw [← neg_sub, smul_neg]; exact neg_mem h⟩

/- English proof (translation)
Take `⟨s, hs, h⟩` from `h`. Take `⟨t, ht, h'⟩` from `h'`. Use `⟨s * t, by rw [← Ideal.span_singleton_mul_span_singleton]; exact hs.mul_left ht, ?_⟩` and prove the remaining obligations. Establish `: (s * t) • (u - w) = t • s • (u - v) + s • t • (v - w)` using `by module`. Rewrite using `[this]`.

Conclude with `add_mem (Submodule.smul_mem _ _ h) (Submodule.smul_mem _ _ h')`.
-/
theorem cong_trans {𝔞 : Ideal (𝓞 E)} {u v w : Fin r → E} (h : Cong X 𝔞 u v) (h' : Cong X 𝔞 v w) :
    Cong X 𝔞 u w := by
  obtain ⟨s, hs, h⟩ := h
  obtain ⟨t, ht, h'⟩ := h'
  refine ⟨s * t, by rw [← Ideal.span_singleton_mul_span_singleton]; exact hs.mul_left ht, ?_⟩
  have : (s * t) • (u - w) = t • s • (u - v) + s • t • (v - w) := by module
  rw [this]
  exact add_mem (Submodule.smul_mem _ _ h) (Submodule.smul_mem _ _ h')

omit [IsCMField E] in
/- English proof (translation)
Rewrite `h`, the goal using `[Ideal.isCoprime_iff_sup_eq]`. Conclude with `top_le_iff.1 (h ▸ sup_le_sup_left hle I)`.
-/
theorem coprime_mono {I 𝔞 𝔟 : Ideal (𝓞 E)} (hle : 𝔞 ≤ 𝔟) (h : IsCoprime I 𝔞) : IsCoprime I 𝔟 := by
  rw [Ideal.isCoprime_iff_sup_eq] at h ⊢
  exact top_le_iff.1 (h ▸ sup_le_sup_left hle I)

omit [IsCMField E] in
/- English proof (translation)
Rewrite using `[Ideal.span_singleton_one, ← Ideal.one_eq_top]`. Conclude with `isCoprime_one_left`.
-/
theorem cop_one {𝔞 : Ideal (𝓞 E)} : IsCoprime (Ideal.span {1}) 𝔞 := by
  rw [Ideal.span_singleton_one, ← Ideal.one_eq_top]; exact isCoprime_one_left

/- English proof (translation)
Take `⟨s, hs, h⟩` from `h`. Conclude with `⟨s, coprime_mono hle hs, Submodule.smul_mono_left hle h⟩`.
-/
theorem cong_mono {𝔞 𝔟 : Ideal (𝓞 E)} (hle : 𝔞 ≤ 𝔟) {u v : Fin r → E} (h : Cong X 𝔞 u v) : Cong X 𝔟 u v := by
  obtain ⟨s, hs, h⟩ := h
  exact ⟨s, coprime_mono hle hs, Submodule.smul_mono_left hle h⟩

omit [IsCMField E] in
/- English proof (translation)
Use `Submodule.smul_induction_on hu (fun a ha v hv => ?_) (fun u v hu hv => ?_)` and prove the remaining obligations. Rewrite using `[smul_comm]`. Conclude with `Submodule.smul_mem_smul ha (h v hv)`. Rewrite using `[smul_add]`. Conclude with `add_mem hu hv`.
-/
theorem smul_mem_smul_of {L L' : Lt E r} {s : 𝓞 E} (h : ∀ v ∈ L, s • v ∈ L') {𝔞 : Ideal (𝓞 E)} {u : Fin r → E}
    (hu : u ∈ 𝔞 • L) : s • u ∈ 𝔞 • L' := by
  refine Submodule.smul_induction_on hu (fun a ha v hv => ?_) (fun u v hu hv => ?_)
  · rw [smul_comm]; exact Submodule.smul_mem_smul ha (h v hv)
  · rw [smul_add]; exact add_mem hu hv

/- English proof (translation)
Take `⟨-, s, hs, h1, -⟩` from `hL`. Use `⟨s * t, ?_, by rw [SemigroupAction.mul_smul]; exact smul_mem_smul_of (𝔞 := 𝔞) h1 h⟩` and prove the remaining obligations. Rewrite using `[← Ideal.span_singleton_mul_span_singleton]`. Conclude with `(coprime_mono (Ideal.mul_le_left.trans hle) hs).mul_left ht`.
-/
theorem cong_of {D : SW.Level X} {L : Lt E r} (hL : L ∈ D.lats) {𝔞 : Ideal (𝓞 E)} (hle : D.𝔪 ≤ 𝔞)
    {u v : Fin r → E} {t : 𝓞 E} (ht : IsCoprime (Ideal.span {t}) 𝔞) (h : t • (u - v) ∈ 𝔞 • L) : Cong X 𝔞 u v := by
  obtain ⟨-, s, hs, h1, -⟩ := hL
  refine ⟨s * t, ?_, by rw [SemigroupAction.mul_smul]; exact smul_mem_smul_of (𝔞 := 𝔞) h1 h⟩
  rw [← Ideal.span_singleton_mul_span_singleton]
  exact (coprime_mono (Ideal.mul_le_left.trans hle) hs).mul_left ht

/- English proof (translation)
Use `⟨fun ⟨t, ht, h⟩ => ?_, fun h => cong_of hL hle (t := 1) cop_one (by rwa [one_smul])⟩` and prove the remaining obligations. Take `⟨-, s, hs, -, h2⟩` from `hL`. Establish `h3 : IsCoprime (Ideal.span {s * t}) 𝔞`. Rewrite using `[← Ideal.span_singleton_mul_span_singleton]`. Conclude with `(coprime_mono (Ideal.mul_le_left.trans hle) hs).mul_left ht`.

Take `⟨a, ha, b, hb, e⟩` from `Ideal.isCoprime_iff_exists.1 h3`. Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.1 ha`. Establish `: u - v = a • s • t • (u - v) + b • (u - v)`. Rewrite using `[← mul_smul, ← mul_smul, ← add_smul, _root_.mul_assoc, e, one_smul]`. Rewrite using `[this]`.

Conclude with `add_mem (Submodule.smul_mem _ _ (smul_mem_smul_of h2 h)) (Submodule.smul_mem_smul hb huv)`.
-/
theorem cong_iff {D : SW.Level X} {L : Lt E r} (hL : L ∈ D.lats) {𝔞 : Ideal (𝓞 E)} (hle : D.𝔪 ≤ 𝔞)
    {u v : Fin r → E} (huv : u - v ∈ L) : Cong X 𝔞 u v ↔ u - v ∈ 𝔞 • L := by
  refine ⟨fun ⟨t, ht, h⟩ => ?_, fun h => cong_of hL hle (t := 1) cop_one (by rwa [one_smul])⟩
  obtain ⟨-, s, hs, -, h2⟩ := hL
  have h3 : IsCoprime (Ideal.span {s * t}) 𝔞 := by
    rw [← Ideal.span_singleton_mul_span_singleton]
    exact (coprime_mono (Ideal.mul_le_left.trans hle) hs).mul_left ht
  obtain ⟨a, ha, b, hb, e⟩ := Ideal.isCoprime_iff_exists.1 h3
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  have : u - v = a • s • t • (u - v) + b • (u - v) := by
    rw [← mul_smul, ← mul_smul, ← add_smul, _root_.mul_assoc, e, one_smul]
  rw [this]
  exact add_mem (Submodule.smul_mem _ _ (smul_mem_smul_of h2 h)) (Submodule.smul_mem_smul hb huv)

/- English proof (translation)
Establish `h1 : D.Red (fun i => y (Fin.castLE hn i)) = D.Red (fun i => y' (Fin.castLE hn i))`. Use function extensionality and compare the values at `k`. Conclude with `propext ⟨fun ⟨k', hk, hc⟩ => ⟨k', hk, fun i => cong_trans (cong_symm (h _)) (hc i)⟩, fun ⟨k', hk, hc⟩ => ⟨k', hk, fun i => cong_trans (h _) (hc i)⟩⟩`. Establish `h2 : ∀ k, Cong X 𝔐 (y k) 0 = Cong X 𝔐 (y' k) 0` using `fun k => propext ⟨cong_trans (cong_symm (cong_mono hle (h k))), cong_trans (cong_mono hle (h k))⟩`. Unfold `datF`.

Simplify using `only [h1, h2]`.
-/
theorem datF_congr (D : SW.Level X) {𝔐 : Ideal (𝓞 E)} (hle : D.𝔪 ≤ 𝔐) (hn : r ≤ n)
    {y y' : Matrix (Fin n) (Fin r) E} (h : ∀ b, Cong X D.𝔪 (y b) (y' b)) : datF D 𝔐 hn y = datF D 𝔐 hn y' := by
  have h1 : D.Red (fun i => y (Fin.castLE hn i)) = D.Red (fun i => y' (Fin.castLE hn i)) := by
    funext k
    exact propext ⟨fun ⟨k', hk, hc⟩ => ⟨k', hk, fun i => cong_trans (cong_symm (h _)) (hc i)⟩,
      fun ⟨k', hk, hc⟩ => ⟨k', hk, fun i => cong_trans (h _) (hc i)⟩⟩
  have h2 : ∀ k, Cong X 𝔐 (y k) 0 = Cong X 𝔐 (y' k) 0 := fun k =>
    propext ⟨cong_trans (cong_symm (cong_mono hle (h k))), cong_trans (cong_mono hle (h k))⟩
  unfold datF
  simp only [h1, h2]

/- English proof (translation)
Unfold `datF at h`. Use `split_ifs at h with h0`. Use `swap`. Conclude with `(h rfl).elim`. Take `⟨⟨k, k', hk, hc⟩, h2⟩` from `h0`.

Use `⟨fun i => cong_trans (cong_mono hle (hc i)) ⟨1, cop_one, ?_⟩, h2⟩` and prove the remaining obligations. Establish `: ∑ j, k' j i • D.β j - D.β i = ∑ j, (k' j i - (1 : Matrix (Fin r) (Fin r) (𝓞 E)) j i) • D.β j`. Simplify using `[sub_smul, Finset.sum_sub_distrib, Matrix.one_apply]`. Rewrite using `[one_smul, this]`. Use `Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul ?_ (D.β_mem j)` and prove the remaining obligations.

Take `⟨a, ha, e⟩` from `hJ k k.2 j i`. Rewrite `e` using `[← hk]`. Establish `: k' j i - (1 : Matrix (Fin r) (Fin r) (𝓞 E)) j i - a ∈ D.𝔪`. Rewrite using `[← Ideal.Quotient.eq, ← e]`. Apply the tactic sequence `by_cases hji : j = i <;> simp [Matrix.one_apply, hji]`.

Simplify using `using add_mem (hle this) ha`.
-/
theorem datF_ne_zero (D : SW.Level X) {𝔐 : Ideal (𝓞 E)} (hle : D.𝔪 ≤ 𝔐) (hn : r ≤ n)
    (hJ : ∀ k : GL (Fin r) (𝓞 E ⧸ D.𝔪), k ∈ D.J → ∀ i j, ∃ a ∈ 𝔐,
      (k : Matrix (Fin r) (Fin r) (𝓞 E ⧸ D.𝔪)) i j - (1 : Matrix (Fin r) (Fin r) (𝓞 E ⧸ D.𝔪)) i j =
        Ideal.Quotient.mk D.𝔪 a)
    {y : Matrix (Fin n) (Fin r) E} (h : datF D 𝔐 hn y ≠ 0) :
    (∀ i, Cong X 𝔐 (y (Fin.castLE hn i)) (D.β i)) ∧ ∀ k : Fin n, r ≤ (k : ℕ) → Cong X 𝔐 (y k) 0 := by
  unfold datF at h
  split_ifs at h with h0
  swap
  · exact (h rfl).elim
  obtain ⟨⟨k, k', hk, hc⟩, h2⟩ := h0
  refine ⟨fun i => cong_trans (cong_mono hle (hc i)) ⟨1, cop_one, ?_⟩, h2⟩
  have : ∑ j, k' j i • D.β j - D.β i = ∑ j, (k' j i - (1 : Matrix (Fin r) (Fin r) (𝓞 E)) j i) • D.β j := by
    simp [sub_smul, Finset.sum_sub_distrib, Matrix.one_apply]
  rw [one_smul, this]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul ?_ (D.β_mem j)
  obtain ⟨a, ha, e⟩ := hJ k k.2 j i
  rw [← hk] at e
  have : k' j i - (1 : Matrix (Fin r) (Fin r) (𝓞 E)) j i - a ∈ D.𝔪 := by
    rw [← Ideal.Quotient.eq, ← e]
    by_cases hji : j = i <;> simp [Matrix.one_apply, hji]
  simpa using add_mem (hle this) ha

noncomputable def ex (q : ℚ) : ℂ := cexp (-(2 * Real.pi * I * (q : ℂ)))

/- English proof (translation)
Rewrite using `[ex, ex, ex, ← Complex.exp_add]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ex_add (q q' : ℚ) : ex (q + q') = ex q * ex q' := by
  rw [ex, ex, ex, ← Complex.exp_add]; congr 1; push_cast; ring

/- English proof (translation)
Rewrite using `[ex, ← Complex.exp_int_mul_two_pi_mul_I (-k)]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ex_int (k : ℤ) : ex k = 1 := by
  rw [ex, ← Complex.exp_int_mul_two_pi_mul_I (-k)]; congr 1; push_cast; ring

/- English proof (translation)
Take `⟨k, hk⟩` from `h`. Rewrite using `[show q = q' + k by rw [← hk]; ring, ex_add, ex_int, _root_.mul_one]`.
-/
theorem ex_congr {q q' : ℚ} (h : ∃ k : ℤ, q - q' = k) : ex q = ex q' := by
  obtain ⟨k, hk⟩ := h
  rw [show q = q' + k by rw [← hk]; ring, ex_add, ex_int, _root_.mul_one]

/- English proof (translation)
Rewrite using `[ex, ex, ← Complex.exp_nat_mul]`. Use `congr 1`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ex_nsmul (m : ℕ) (q : ℚ) : ex (m • q) = ex q ^ m := by
  rw [ex, ex, ← Complex.exp_nat_mul]; congr 1; simp; ring

/- English proof (translation)
Simplify using `only [ex, ← Complex.exp_sum]`. Use `congr 1`. Simplify using `[Finset.mul_sum]`.
-/
theorem ex_sum (f : Fin n → ℚ) : ex (∑ b, f b) = ∏ b, ex (f b) := by
  simp only [ex, ← Complex.exp_sum]; congr 1; simp [Finset.mul_sum]

/- English proof (translation)
Proceed by induction on `(Finset.univ : Finset (Fin n)) using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ hz, ih]`.
-/
theorem zpow_sum' {z : ℂ} (hz : z ≠ 0) (f : Fin n → ℤ) : z ^ (∑ b, f b) = ∏ b, z ^ f b := by
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ hz, ih]

/- English proof (translation)
Take `⟨k, hk⟩` from `h`. Establish `h0 : z ≠ 0` using `by rintro rfl; simp [hm] at hz`. Rewrite using `[show a = b + m * k by rw [← hk]; ring, zpow_add₀ h0, _root_.zpow_mul, zpow_natCast, hz, _root_.one_zpow, _root_.mul_one]`.
-/
theorem zpow_congr' {z : ℂ} {m : ℕ} (hm : m ≠ 0) (hz : z ^ m = 1) {a b : ℤ} (h : (m : ℤ) ∣ a - b) :
    z ^ a = z ^ b := by
  obtain ⟨k, hk⟩ := h
  have h0 : z ≠ 0 := by rintro rfl; simp [hm] at hz
  rw [show a = b + m * k by rw [← hk]; ring, zpow_add₀ h0, _root_.zpow_mul, zpow_natCast, hz, _root_.one_zpow, _root_.mul_one]

/- English proof (translation)
Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨v, hv, u, hu, rfl⟩` from `hy`. Establish `: vecMulVec v u b = v b • u` using `by funext j; simp [vecMulVec_apply]`. Rewrite using `[this, TensLat.EF_smul]`.

Conclude with `(hL.2 u).1 (hle hu) _ (hY v hv)`. Consider the case `zero => exact ⟨0, by`. Establish `: (0 : Matrix (Fin n) (Fin r) E) b = 0` using `rfl`. Simplify using `[this, TensLat.EF_eq_bilin]⟩`. Consider the case `add y y' _ _ h h'`.

Take `⟨k, hk⟩` from `h`. Take `⟨k', hk'⟩` from `h'`. Establish `: (y + y') b = y b + y' b` using `rfl`. Use `⟨k + k', ?_⟩` and prove the remaining obligations. Rewrite using `[this, Int.cast_add, ← hk, ← hk']`.

Simplify using `[TensLat.EF_eq_bilin]`. Consider the case `neg y _ h`. Take `⟨k, hk⟩` from `h`. Establish `: (-y) b = -y b` using `rfl`. Use `⟨-k, ?_⟩` and prove the remaining obligations.

Rewrite using `[this, Int.cast_neg, ← hk]`. Simplify using `[TensLat.EF_eq_bilin]`.
-/
theorem EF_int_tens {Λ : Lt E n} {L L' : Lt E r} (hL : SelfD X L) (hle : L' ≤ L) {b : Fin n} {Y : Fin r → E}
    (hY : ∀ v ∈ Λ, cc (v b) • Y ∈ L) {y : Matrix (Fin n) (Fin r) E} (hy : y ∈ tens Λ L') :
    ∃ k : ℤ, EF X (y b) Y = k := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨v, hv, u, hu, rfl⟩ := hy
    have : vecMulVec v u b = v b • u := by funext j; simp [vecMulVec_apply]
    rw [this, TensLat.EF_smul]
    exact (hL.2 u).1 (hle hu) _ (hY v hv)
  | zero => exact ⟨0, by
      have : (0 : Matrix (Fin n) (Fin r) E) b = 0 := rfl
      simp [this, TensLat.EF_eq_bilin]⟩
  | add y y' _ _ h h' =>
    obtain ⟨k, hk⟩ := h
    obtain ⟨k', hk'⟩ := h'
    have : (y + y') b = y b + y' b := rfl
    refine ⟨k + k', ?_⟩
    rw [this, Int.cast_add, ← hk, ← hk']; simp [TensLat.EF_eq_bilin]
  | neg y _ h =>
    obtain ⟨k, hk⟩ := h
    have : (-y) b = -y b := rfl
    refine ⟨-k, ?_⟩
    rw [this, Int.cast_neg, ← hk]; simp [TensLat.EF_eq_bilin]

/- English proof (translation)
Use `Submodule.smul_induction_on hu (fun a ha v hv => ?_) (fun u v hu hv => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `∃ k : ℤ, EF X ((a : E) • v) Y = k`. Rewrite using `[TensLat.EF_smul]`. Conclude with `(hL.2 v).1 hv _ (hY a ha)`. Take `⟨k, hk⟩` from `hu`.

Take `⟨k', hk'⟩` from `hv`. Use `⟨k + k', ?_⟩` and prove the remaining obligations. Rewrite using `[Int.cast_add, ← hk, ← hk']`. Simplify using `[TensLat.EF_eq_bilin]`.
-/
theorem EF_int_smul {L : Lt E r} (hL : SelfD X L) {𝔞 : Ideal (𝓞 E)} {Y : Fin r → E}
    (hY : ∀ a ∈ 𝔞, cc (a : E) • Y ∈ L) {u : Fin r → E} (hu : u ∈ 𝔞 • L) : ∃ k : ℤ, EF X u Y = k := by
  refine Submodule.smul_induction_on hu (fun a ha v hv => ?_) (fun u v hu hv => ?_)
  · change ∃ k : ℤ, EF X ((a : E) • v) Y = k
    rw [TensLat.EF_smul]
    exact (hL.2 v).1 hv _ (hY a ha)
  · obtain ⟨k, hk⟩ := hu
    obtain ⟨k', hk'⟩ := hv
    refine ⟨k + k', ?_⟩
    rw [Int.cast_add, ← hk, ← hk']; simp [TensLat.EF_eq_bilin]

/- English proof (translation)
Take `⟨-, -, s, -, hs, h1, h2⟩` from `hΛ`. Take `⟨a, c, e⟩` from `Nat.isCoprime_iff_coprime.2 hs`. Use `⟨a * s, -c, by linear_combination e, fun v hv b => ?_, fun b => ?_⟩` and prove the remaining obligations. Establish `h3 : ∀ x ∈ stdL E n, IsIntegral ℤ (x b)` using `fun x hx => by`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨i, rfl⟩` from `hx`. Apply the tactic sequence `by_cases h : b = i <;> simp [Pi.single_apply, h, isIntegral_one, isIntegral_zero]`. Consider the case `zero => exact isIntegral_zero`. Consider the case `add x y _ _ hx hy => exact hx.add hy`.

Consider the case `smul t x _ hx => exact t.2.mul hx`. Use `(isIntegral_algebraMap (R := ℤ) (A := E) (x := a)).mul (h3 _ (h1 v hv))` as an intermediate fact. Simplify `this` using `[_root_.mul_assoc]`. Use `zsmul_mem (h2 (Pi.single b 1) (Submodule.subset_span ⟨b, rfl⟩)) a` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Apply the tactic sequence `funext j; by_cases h : j = b <;> simp [Pi.single_apply, h]`.
-/
theorem exists_mult {M : ℕ} {Λ : Lt E n} (hΛ : Λ ∈ Vset E n M) : ∃ s k : ℤ, s = 1 + k * M ∧
    (∀ v ∈ Λ, ∀ b, IsIntegral ℤ ((s : E) * v b)) ∧ ∀ b, (Pi.single b (s : E) : Fin n → E) ∈ Λ := by
  obtain ⟨-, -, s, -, hs, h1, h2⟩ := hΛ
  obtain ⟨a, c, e⟩ := Nat.isCoprime_iff_coprime.2 hs
  refine ⟨a * s, -c, by linear_combination e, fun v hv b => ?_, fun b => ?_⟩
  · have h3 : ∀ x ∈ stdL E n, IsIntegral ℤ (x b) := fun x hx => by
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        by_cases h : b = i <;> simp [Pi.single_apply, h, isIntegral_one, isIntegral_zero]
      | zero => exact isIntegral_zero
      | add x y _ _ hx hy => exact hx.add hy
      | smul t x _ hx => exact t.2.mul hx
    have := (isIntegral_algebraMap (R := ℤ) (A := E) (x := a)).mul (h3 _ (h1 v hv))
    simpa [_root_.mul_assoc] using this
  · have := zsmul_mem (h2 (Pi.single b 1) (Submodule.subset_span ⟨b, rfl⟩)) a
    convert this using 1
    funext j; by_cases h : j = b <;> simp [Pi.single_apply, h]

/- English proof (translation)
Establish `h1 : (N : 𝓞 E) • (Pi.single b 1 : Fin n → E) ∈ Λ`. Use `(hN.2.2 (Submodule.smul_mem_smul (Ideal.subset_span rfl) fun j _ => ?_)).1` and prove the remaining obligations. Distinguish the cases in `h : j = b`. Substitute `h` using the available equality. Simplify using `using Submodule.one_le.1 le_rfl`.

Simplify using `[Pi.single_apply, h]`. Use `(hΛ.2.1 v).1 hv _ h1` as an intermediate fact. Rewrite `this` using `[Base.herm_one, Finset.sum_eq_single b (fun j _ hj => by simp [Pi.single_apply, hj, cc]) (by simp)]`. Simplify `this` using `[cc, Algebra.smul_def, mul_comm]`.
-/
theorem int_of_nok {M N : ℕ} {Λ : Lt E n} (hΛ : Λ ∈ Vset E n M) (hN : NOK Λ N M) {v : Fin n → E} (hv : v ∈ Λ)
    (b : Fin n) : IsIntegral ℤ ((N : E) * v b) := by
  have h1 : (N : 𝓞 E) • (Pi.single b 1 : Fin n → E) ∈ Λ := by
    refine (hN.2.2 (Submodule.smul_mem_smul (Ideal.subset_span rfl) fun j _ => ?_)).1
    by_cases h : j = b
    · subst h; simpa using Submodule.one_le.1 le_rfl
    · simp [Pi.single_apply, h]
  have := (hΛ.2.1 v).1 hv _ h1
  rw [Base.herm_one, Finset.sum_eq_single b (fun j _ hj => by simp [Pi.single_apply, hj, cc]) (by simp)] at this
  simpa [cc, Algebra.smul_def, mul_comm] using this

variable {H : Host E} {Dw : Datum H}

/- English proof (translation)
Assemble the required witnesses or components as `⟨(l.prod ▸ Ideal.mul_le_left : Ideal.span {(l.M : 𝓞 E)} ≤ l.Mb) (Ideal.subset_span rfl), (l.prod ▸ Ideal.mul_le_right : Ideal.span {(l.M : 𝓞 E)} ≤ Mfr l) (Ideal.subset_span rfl)⟩`.
-/
theorem natCast_mem (l : Geo.Tor.Level H) : (l.M : 𝓞 E) ∈ l.Mb ∧ (l.M : 𝓞 E) ∈ Mfr l :=
  ⟨(l.prod ▸ Ideal.mul_le_left : Ideal.span {(l.M : 𝓞 E)} ≤ l.Mb) (Ideal.subset_span rfl),
    (l.prod ▸ Ideal.mul_le_right : Ideal.span {(l.M : 𝓞 E)} ≤ Mfr l) (Ideal.subset_span rfl)⟩

/- English proof (translation)
Establish `hM : (l.M : E) ≠ 0` using `by have := l.three_le; exact_mod_cast (by omega : l.M ≠ 0)`. Establish `h1 : t • a ∈ Ideal.span {(l.M : 𝓞 E)} • (⊤ : Submodule (𝓞 E) Dw.La)`. Rewrite using `[← l.prod, Submodule.mul_smul]`. Conclude with `Submodule.smul_mem_smul ht ha`. Rewrite `h1` using `[Submodule.ideal_span_singleton_smul]`.

Take `⟨a', -, e⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h1`. Establish `h2 : t • ((l.M : E)⁻¹) • mk a = mk a'`. Rewrite using `[smul_comm, ← map_smul, ← e, map_smul]`. Use function extensionality and compare the values at `j`. Simplify using `[Algebra.smul_def, hM]`.

Use `add_mem (L.smul_mem t hY) (hmk.mem a')` as an intermediate fact. Rewrite `this` using `[← h2, ← smul_add, sub_add_cancel]`. Then use the resulting hypothesis.
-/
theorem root_mem {l : Geo.Tor.Level H} {L : Lt E r} {mk : Dw.La →ₗ[𝓞 E] (Fin r → E)} (hmk : IsMark l L mk)
    {Y : Fin r → E} {a : Dw.La} (ha : a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La))
    (hY : Y - ((l.M : E)⁻¹) • mk a ∈ L) {t : 𝓞 E} (ht : t ∈ l.Mb) : t • Y ∈ L := by
  have hM : (l.M : E) ≠ 0 := by have := l.three_le; exact_mod_cast (by omega : l.M ≠ 0)
  have h1 : t • a ∈ Ideal.span {(l.M : 𝓞 E)} • (⊤ : Submodule (𝓞 E) Dw.La) := by
    rw [← l.prod, Submodule.mul_smul]; exact Submodule.smul_mem_smul ht ha
  rw [Submodule.ideal_span_singleton_smul] at h1
  obtain ⟨a', -, e⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h1
  have h2 : t • ((l.M : E)⁻¹) • mk a = mk a' := by
    rw [smul_comm, ← map_smul, ← e, map_smul]
    funext j; simp [Algebra.smul_def, hM]
  have := add_mem (L.smul_mem t hY) (hmk.mem a')
  rwa [← h2, ← smul_add, sub_add_cancel] at this

/- English proof (translation)
Take `⟨j, hj⟩` from `h2`. Take `⟨u, hu, e⟩` from `hj _ (Ideal.pow_mem_pow (natCast_mem l).1 j)`. Take `⟨p, q, hpq⟩ : IsCoprime s ((l.M : ℤ) ^ j)` from `IsCoprime.pow_right ⟨1, -k, by linear_combination hs⟩`. Establish `hpq' : (p : E) * s + q * (l.M : E) ^ j = 1` using `by exact_mod_cast congrArg (Int.cast : ℤ → E) hpq`. Establish `: a • (l.M : E) • Y = p • ((s : E) * a) • (l.M : 𝓞 E) • Y + (q * l.M * 2) • ((N : E) * a) • u`.

Use function extensionality and compare the values at `i`. Use `congrFun e i` as an intermediate fact. Simplify using `[Algebra.smul_def] at this ⊢`. Take the linear combination `(-a * l.M * Y i) * hpq' + (q * l.M * a) * this`. Rewrite using `[this]`.

Conclude with `add_mem (zsmul_mem (TensLat.int_smul_mem has h1) _) (zsmul_mem (TensLat.int_smul_mem haN hu) _)`.
-/
theorem root_mem' {l : Geo.Tor.Level H} {L : Lt E r} {N : ℕ} {Y : Fin r → E} (h1 : (l.M : 𝓞 E) • Y ∈ L)
    (h2 : ∃ j : ℕ, ∀ s ∈ l.Mb ^ j, ∃ u ∈ L, s • Y = (2 * N) • u) {s k : ℤ} (hs : s = 1 + k * l.M) {a : E}
    (has : IsIntegral ℤ ((s : E) * a)) (haN : IsIntegral ℤ ((N : E) * a)) : a • (l.M : E) • Y ∈ L := by
  obtain ⟨j, hj⟩ := h2
  obtain ⟨u, hu, e⟩ := hj _ (Ideal.pow_mem_pow (natCast_mem l).1 j)
  obtain ⟨p, q, hpq⟩ : IsCoprime s ((l.M : ℤ) ^ j) := IsCoprime.pow_right ⟨1, -k, by linear_combination hs⟩
  have hpq' : (p : E) * s + q * (l.M : E) ^ j = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → E) hpq
  have : a • (l.M : E) • Y = p • ((s : E) * a) • (l.M : 𝓞 E) • Y + (q * l.M * 2) • ((N : E) * a) • u := by
    funext i
    have := congrFun e i
    simp [Algebra.smul_def] at this ⊢
    linear_combination (-a * l.M * Y i) * hpq' + (q * l.M * a) * this
  rw [this]
  exact add_mem (zsmul_mem (TensLat.int_smul_mem has h1) _) (zsmul_mem (TensLat.int_smul_mem haN hu) _)

/- English proof (translation)
Establish `h : ∃ c, c ∈ I'.map (H.bar : 𝓞 E →+* 𝓞 E) ∧ c - 1 ∈ I'`. Take `⟨m, hm, mb, hmb, hsum⟩` from `Submodule.mem_sup.1 (h ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ I' ⊔ _)`. Use `⟨mb, hmb, ?_⟩` and prove the remaining obligations. Establish `: mb - 1 = -m` using `by rw [← hsum]; ring`. Rewrite using `[this]`.

Conclude with `neg_mem hm`. Unfold `cHalf`. Rewrite using `[dif_pos h]`. Conclude with `h.choose_spec`.
-/
theorem cHalf_spec {I' : Ideal (𝓞 E)} (h : I' ⊔ I'.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤) :
    cHalf H I' ∈ I'.map (H.bar : 𝓞 E →+* 𝓞 E) ∧ cHalf H I' - 1 ∈ I' := by
  have h : ∃ c, c ∈ I'.map (H.bar : 𝓞 E →+* 𝓞 E) ∧ c - 1 ∈ I' := by
    obtain ⟨m, hm, mb, hmb, hsum⟩ := Submodule.mem_sup.1 (h ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ I' ⊔ _)
    refine ⟨mb, hmb, ?_⟩
    have : mb - 1 = -m := by rw [← hsum]; ring
    rw [this]; exact neg_mem hm
  unfold cHalf
  rw [dif_pos h]
  exact h.choose_spec

/- English proof (translation)
Rewrite `hy` using `[Submodule.ideal_span_singleton_smul]`. Take `⟨a, -, rfl⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy`. Rewrite using `[Nat.cast_smul_eq_nsmul, map_nsmul]`. Conclude with `⟨Dw.EF x a, by simp⟩`.
-/
theorem dvd_EF {m : ℕ} (x : Dw.La) {y : Dw.La}
    (hy : y ∈ Ideal.span {(m : 𝓞 E)} • (⊤ : Submodule (𝓞 E) Dw.La)) : (m : ℤ) ∣ Dw.EF x y := by
  rw [Submodule.ideal_span_singleton_smul] at hy
  obtain ⟨a, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
  rw [Nat.cast_smul_eq_nsmul, map_nsmul]
  exact ⟨Dw.EF x a, by simp⟩

/- English proof (translation)
Use `Submodule.smul_induction_on ha (fun t ht v _ => ?_) (fun u v hu hv => ?_)` and prove the remaining obligations. Rewrite using `[map_smul]`. Conclude with `Submodule.smul_mem_smul ht (hf v)`. Rewrite using `[map_add]`. Conclude with `add_mem hu hv`.
-/
theorem map_mem_smul {L : Lt E r} {f : Dw.La →ₗ[𝓞 E] (Fin r → E)} (hf : ∀ a, f a ∈ L) {𝔞 : Ideal (𝓞 E)}
    {a : Dw.La} (ha : a ∈ 𝔞 • (⊤ : Submodule (𝓞 E) Dw.La)) : f a ∈ 𝔞 • L := by
  refine Submodule.smul_induction_on ha (fun t ht v _ => ?_) (fun u v hu hv => ?_)
  · rw [map_smul]; exact Submodule.smul_mem_smul ht (hf v)
  · rw [map_add]; exact add_mem hu hv

variable {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

/- English proof (translation)
Establish `hI : d.l₂.Mb ≤ d.I` using `h.2.2.2.1 ▸ Ideal.mul_le_right`. Take `⟨h1, h2⟩` from `LevelPairing.cSep_spec d.l₂`. Take `⟨h3, h4⟩` from `cHalf_spec h.2.2.2.2.1`. Establish `hp` using `LevelCoverDatum.half_mul_conj d h`. Rewrite using `[← map_sub]`.

Use `dvd_EF x ?_` and prove the remaining obligations. Establish `: cSep d.l₂ • a - cHalf H d.I • a' = (cSep d.l₂ - cHalf H d.I) • a + cHalf H d.I • (a - a')` using `by module`. Rewrite using `[this, ← hp]`. Use `add_mem (Submodule.smul_mem_smul ?_ trivial) ?_` and prove the remaining obligations. Rewrite using `[Ideal.mul_eq_inf_of_isCoprime (Ideal.isCoprime_iff_sup_eq.2 h.2.2.2.2.1)]`.

Conclude with `⟨by simpa using sub_mem (hI h2) h4, sub_mem (hJ h1) h3⟩`. Rewrite using `[mul_comm, Submodule.mul_smul]`. Conclude with `Submodule.smul_mem_smul h3 (Submodule.smul_mono_left hI ha)`.
-/
theorem pd_dvd (d : DeltaDat Xo c n) (h : d.IsLev) (hJ : Mfr d.l₂ ≤ Jd d) (x : Dw.La) {a a' : Dw.La}
    (ha : a - a' ∈ d.l₂.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) :
    (d.pd : ℤ) ∣ Dw.EF x (cSep d.l₂ • a) - Dw.EF x (cHalf H d.I • a') := by
  have hI : d.l₂.Mb ≤ d.I := h.2.2.2.1 ▸ Ideal.mul_le_right
  obtain ⟨h1, h2⟩ := LevelPairing.cSep_spec d.l₂
  obtain ⟨h3, h4⟩ := cHalf_spec h.2.2.2.2.1
  have hp := LevelCoverDatum.half_mul_conj d h
  rw [← map_sub]
  refine dvd_EF x ?_
  have : cSep d.l₂ • a - cHalf H d.I • a' = (cSep d.l₂ - cHalf H d.I) • a + cHalf H d.I • (a - a') := by module
  rw [this, ← hp]
  refine add_mem (Submodule.smul_mem_smul ?_ trivial) ?_
  · rw [Ideal.mul_eq_inf_of_isCoprime (Ideal.isCoprime_iff_sup_eq.2 h.2.2.2.2.1)]
    exact ⟨by simpa using sub_mem (hI h2) h4, sub_mem (hJ h1) h3⟩
  · rw [mul_comm, Submodule.mul_smul]
    exact Submodule.smul_mem_smul h3 (Submodule.smul_mono_left hI ha)

/- English proof (translation)
Establish `hp` using `LevelCoverDatum.pd_pos d h`. Establish `hM : 0 < d.l₂.M` using `by have := d.l₂.three_le; omega`. Take `⟨k, hk⟩ : d.l₂.M ∣ d.l₂.M'` from `Nat.dvd_lcm_left _ _`. Unfold `zetaM`. Rewrite using `[← pow_mul]`.

Use `congr 1`. Rewrite using `[hk, Nat.mul_div_cancel_left _ hM, h.2.1, mul_comm l.M, _root_.mul_assoc, Nat.mul_div_cancel_left _ hp, mul_comm]`.
-/
theorem zetaM_pow (d : DeltaDat Xo c n) (h : d.IsLev) : zetaM d.c₂ ^ l.M =
    (⟨zeta d.l₂.M', d.c₂.zeta_mem⟩ : d.c₂.F) ^ (d.l₂.M' / d.pd) := by
  have hp := LevelCoverDatum.pd_pos d h
  have hM : 0 < d.l₂.M := by have := d.l₂.three_le; omega
  obtain ⟨k, hk⟩ : d.l₂.M ∣ d.l₂.M' := Nat.dvd_lcm_left _ _
  unfold zetaM
  rw [← pow_mul]
  congr 1
  rw [hk, Nat.mul_div_cancel_left _ hM, h.2.1, mul_comm l.M, _root_.mul_assoc, Nat.mul_div_cancel_left _ hp, mul_comm]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c n d _ _ halg hlev ph ψ x₀ hpin r X D hn hr hT L hL mk mk₂ δ x0 hmk hmk₂ hov hδ hx0`. Establish `hM : l.M ≠ 0` using `by have := l.three_le; omega`. Establish `hpd` using `(LevelCoverDatum.pd_pos d hlev).ne'`. Establish `hζ` using `(LevelPairing.zetaM_prim c).map_of_injective (algebraMap c.F ℂ).injective`. Establish `hζ₂` using `(LevelPairing.zetaM_prim d.c₂).map_of_injective (algebraMap d.c₂.F ℂ).injective`.

Take `⟨⟨δ₂, hδ₂⟩, hall, -⟩` from `GlobalTheory.T.dual_half_level_marking_exists_and_match E H Dw d.l₂ r X L mk₂ _ hL.1 hmk₂ hζ₂`. Take `⟨hsur, hinj, -⟩` from `hall δ₂ hδ₂`. Use `clear hall`. Establish `h𝔐 : D.𝔪 ≤ Mfr l` using `hT.prod ▸ Ideal.mul_le_left`. Establish `h𝔍 : D.𝔪 ≤ Jd d` using `hT.prod ▸ Ideal.mul_le_right`.

Establish `hpJ : (d.pd : 𝓞 E) ∈ Jd d` using `(LevelCoverDatum.half_mul_conj d hlev ▸ Ideal.mul_le_right : Ideal.span {(d.pd : 𝓞 E)} ≤ Jd d) (Ideal.subset_span rfl)`. Establish `hMM` using `(natCast_mem l).2`. Take `⟨p, q', hpq⟩` from `Nat.isCoprime_iff_coprime.2 hlev.2.2.1`. Establish `hpq' : (p : 𝓞 E) * d.pd + q' * l.M = 1` using `by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hpq`. Use `set δJ : Dw.La →ₗ[𝓞 E] (Fin r → E) := (l.M : 𝓞 E) • δ₂ with hδJ`.

Establish `hJM : ∀ a, δJ a ∈ Mfr l • L` using `fun a => Submodule.smul_mem_smul hMM (hδ₂.mem a)`. Establish `hJL : ∀ a, δJ a ∈ L` using `fun a => Submodule.smul_le_right (hJM a)`. Establish `hJsur : L ≤ LinearMap.range δJ ⊔ Jd d • L` using `fun v hv => by`. Take `⟨_, ⟨a, rfl⟩, w, hw, rfl⟩` from `Submodule.mem_sup.1 (hsur hv)`. Use `Submodule.mem_sup.2 ⟨_, ⟨(q' : 𝓞 E) • a, rfl⟩, ((p : 𝓞 E) * d.pd) • δ₂ a + w, add_mem (Submodule.smul_mem_smul (Ideal.mul_mem_left _ _ hpJ) (hδ₂.mem a)) (Submodule.smul_mono_left (hT.m ▸ h𝔍) hw), ?_⟩` and prove the remaining obligations.

Rewrite using `[hδJ, LinearMap.smul_apply, map_smul, smul_smul, ← add_assoc, ← add_smul, show (l.M : 𝓞 E) * q' + p * d.pd = 1 by linear_combination hpq', one_smul]`. Establish `hJinj : ∀ a, δJ a ∈ Jd d • L → a ∈ Jd d • (⊤ : Submodule (𝓞 E) Dw.La)` using `fun a ha => by`. Establish `h1 : δ₂ ((l.M : 𝓞 E) • a) ∈ Mfr d.l₂ • L`. Rewrite using `[← hT.m, hT.prod, map_smul]`. Conclude with `mem_mul_smul hT.cop (hJM a) ha`.

Establish `h2` using `Submodule.smul_mono_left (hT.m ▸ h𝔍 : Mfr d.l₂ ≤ Jd d) ((hinj _).1 h1)`. Establish `: a = ((p : 𝓞 E) * d.pd) • a + (q' : 𝓞 E) • (l.M : 𝓞 E) • a`. Rewrite using `[smul_smul, ← add_smul, hpq', one_smul]`. Rewrite using `[this]`. Conclude with `add_mem (Submodule.smul_mem_smul (Ideal.mul_mem_left _ _ hpJ) trivial) (Submodule.smul_mem _ _ h2)`.

Establish `hrep : ∀ x : LaJ Xo c d, Submodule.Quotient.mk (qRep x) = x` using `fun x => Classical.choose_spec (Submodule.Quotient.mk_surjective _ x)`. Establish `hx0J : ∀ b, d.pd • δ (x0 b) ∈ Jd d • L` using `fun b => by`. Rewrite using `[← Nat.cast_smul_eq_nsmul (𝓞 E)]`. Conclude with `Submodule.smul_mem_smul hpJ (hδ.mem _)`. Establish `hx0L : ∀ b, d.pd • δ (x0 b) ∈ L` using `fun b => Submodule.smul_le_right (hx0J b)`.

Establish `hx0M : ∀ k : Fin n, r ≤ (k : ℕ) → Cong X (Mfr l) (d.pd • δ (x0 k)) 0` using `fun k hk => (cong_iff hL h𝔐 (by simpa using hx0L k)).2 (by`. Simplify using `using nsmul_mem (map_mem_smul hδ.mem (hx0.2 k hk)) d.pd)`. Take `⟨t, ht, htie⟩` from `hT.tie L hL δJ hJL hJsur`. Use `⟨t, ht, fun Λ hΛ N hN Y hY q => ?_⟩` and prove the remaining obligations. Use `choose a ha haq haY using fun b => (hY q b).1`.

Establish `hroot : ∀ b, ∀ s ∈ d.l₂.Mb, s • Y q b ∈ L` using `fun b s hs => root_mem hmk₂ (ha b) (haY b) hs`. Take `⟨s, k, hs, hs1, hs2⟩` from `exists_mult hΛ`. Establish `hM𝔪 : (d.l₂.M : 𝓞 E) ∈ D.𝔪` using `hT.m ▸ (natCast_mem d.l₂).2`. Establish `hs𝔪 : (s : 𝓞 E) - 1 ∈ D.𝔪`. Rewrite using `[hs]`.

Simplify using `using Ideal.mul_mem_left _ (k : 𝓞 E) hM𝔪`. Establish `hscop : IsCoprime (Ideal.span {(s : 𝓞 E)}) D.𝔪` using `Ideal.isCoprime_iff_exists.2 ⟨_, Ideal.subset_span rfl, _, neg_mem hs𝔪, by ring⟩`. Set `z : (Fin n → LaJ Xo c d) → Matrix (Fin n) (Fin r) E` to `fun x b => d.pd • δ (x0 b) + δJ (qRep (x b))`. Establish `hz : ∀ x b, z x b = d.pd • δ (x0 b) + δJ (qRep (x b))` using `fun _ _ => rfl`. Establish `hzL : ∀ x b, z x b ∈ L` using `fun x b => add_mem (hx0L b) (hJL _)`.

Establish `hzM : ∀ x b, Cong X (Mfr l) (z x b) (d.pd • δ (x0 b))` using `fun x b => (cong_iff hL h𝔐 (sub_mem (hzL x b) (hx0L b))).2 (by rw [hz, add_sub_cancel_left]; exact hJM _)`. Establish `key` using `finsum_tens (Λ := Λ) (L := L) (𝔟 := Ideal.span {2} * conjI D.𝔪) (𝔪 := D.𝔪) (D.odd.symm.mul_left D.cop.symm) hs𝔪 (by simpa using hs1) (by simpa using hs2) (fun y => datF D (Mfr l) hn y * ex (∑ b, EF X (y b) (Y q b))) (fun y hy => ?_) (fun w w' hw hww => ?_) z hzL (fun x x' h => fu …`. Use `Eq.trans ?_ (congrArg (t * ·) key.symm)` and prove the remaining obligations. Unfold `DeltaDat.w`. Rewrite using `[map_mul, map_mul, halg, hpin.2.2.2.2.2 q, (algebraMap d.c₂.F ℂ).toAddMonoidHom.map_finsum_of_injective (algebraMap d.c₂.F ℂ).injective _ |>.trans rfl |> (show (algebraMap d.c₂.F ℂ) _ = _ from ·), mul_finsum, mul_finsum]`.

Use `finsum_congr fun x => ?_` and prove the remaining obligations. Establish `h1` using `htie (fun b => qRep (x b)) (z x) (fun i => ⟨(cong_iff hL h𝔍 (sub_mem (hzL x _) (hJL _))).2 (by rw [hz, add_sub_cancel_right]; exact hx0J _), cong_trans (hzM x _) (hx0.1 i)⟩) (fun k hk => cong_trans (hzM x k) (hx0M k hk))`. Simplify using `only [hrep] at h1`. Express the relevant statement in the definitionally equal form `_ * algebraMap d.c₂.F ℂ _ = _`. Rewrite using `[map_mul, halg, h1, ← zetaM_pow d hlev, map_zpow₀, map_zpow₀, map_pow, pairL, zpow_sum' (hζ.ne_zero hM), zpow_sum' (pow_ne_zero _ (hζ₂.ne_zero (by rw [hlev.2.1]; positivity))), ex_sum, mul_left_comm, _root_.mul_assoc t, ← Finset.prod_mul_distrib]`.

Use `congr 2`. Use `Finset.prod_congr rfl fun b _ => ?_` and prove the remaining obligations. Establish `hab : a b - levRep (q b) ∈ d.l₂.Mb • (⊤ : Submodule (𝓞 E) Dw.La)` using `(Submodule.Quotient.eq _).1 ((haq b).trans (Classical.choose_spec (Submodule.Quotient.mk_surjective _ (q b))).symm)`. Establish `e1 : ex (EF X (z x b) (Y q b)) = ex (EF X (z x b) (((d.l₂.M : E)⁻¹) • mk₂ (a b)))`. Use `ex_congr ?_` and prove the remaining obligations.

Take `⟨j, hj⟩` from `(hL.1.2 _).1 (hzL x b) _ (haY b)`. Conclude with `⟨j, by rw [← hj]; simp only [TensLat.EF_eq_bilin, map_sub]⟩`. Establish `e2 : EF X (z x b) (((d.l₂.M : E)⁻¹) • mk₂ (a b)) = EF X (δ (x0 b)) (((l.M : E)⁻¹) • mk₂ (a b)) + l.M • EF X (δ₂ (qRep (x b))) (((d.l₂.M : E)⁻¹) • mk₂ (a b))`. Establish `: ((l.M : E)⁻¹) • mk₂ (a b) = d.pd • ((d.l₂.M : E)⁻¹) • mk₂ (a b)`. Establish `: (d.pd : E) ≠ 0` using `by exact_mod_cast hpd`.

Rewrite using `[hlev.2.1]`. Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Rewrite using `[this, hz, hδJ, LinearMap.smul_apply, Nat.cast_smul_eq_nsmul]`.

Simplify using `only [TensLat.EF_eq_bilin, map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply]`. Establish `e3 : ex (EF X (δ (x0 b)) (((l.M : E)⁻¹) • mk₂ (a b))) = ex (EF X (δ (x0 b)) (((l.M : E)⁻¹) • mk (a b)))`. Use `ex_congr ?_` and prove the remaining obligations. Take `⟨u, hu, e⟩` from `hov _ (ha b)`. Take `⟨j, hj⟩` from `(hL.1.2 _).1 (hδ.mem (x0 b)) _ hu`.

Establish `: ((l.M : E)⁻¹) • mk₂ (a b) = ((l.M : E)⁻¹) • mk (a b) + u`. Establish `: (l.M : E) ≠ 0` using `by exact_mod_cast hM`. Rewrite using `[e]`. Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules.

Clear the denominators using the available nonvanishing facts. Conclude with `⟨j, by rw [← hj, this]; simp only [TensLat.EF_eq_bilin, map_add, add_sub_cancel_left]⟩`. Rewrite using `[e1, e2, ex_add, e3, ex_nsmul, ex, ex, ← hδ.pair _ _ (Submodule.smul_mono_left (hT.m ▸ h𝔐) (ha b)), ← hδ₂.pair _ _ (ha b), ← zpow_natCast (_ ^ (_ : ℤ)), ← _root_.zpow_mul, mul_comm _ (l.M : ℤ), _root_.zpow_mul, zpow_natCast]`. Use `congr 1`. Use `zpow_congr' hM hζ.pow_eq_one ?_` and prove the remaining obligations.

Rewrite using `[← map_sub, ← smul_sub, ← dvd_neg, ← map_neg, ← smul_neg, neg_sub]`. Conclude with `LevelPairing.dvd_right _ (Submodule.smul_mono_left hlev.1.2.1 hab)`. Use `(zpow_congr' hpd ?_ (pd_dvd d hlev (hT.m ▸ h𝔍) _ hab)).symm` and prove the remaining obligations. Rewrite using `[← pow_mul, ← hlev.2.1, hζ₂.pow_eq_one]`. Establish `hrow` using `fun b => (Submodule.smul_le_right : _ ≤ L) (row_mem hs1 hy b)`.

Use `congr 1`. Use `datF_congr D h𝔐 hn fun b => cong_of hL le_rfl hscop ?_` and prove the remaining obligations. Establish `: (s : 𝓞 E) • (y b - (((s : 𝓞 E) : E) • y) b) = (-((s : 𝓞 E) - 1)) • (s : E) • y b`. Use function extensionality and compare the values at `j`. Simplify using `[Algebra.smul_def]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `Submodule.smul_mem_smul (neg_mem hs𝔪) (hrow b)`. Rewrite using `[ex_sum, ex_sum]`. Use `Finset.prod_congr rfl fun b _ => ex_congr ?_` and prove the remaining obligations.

Take `⟨j, hj⟩` from `EF_int_tens (b := b) (Y := (d.l₂.M : E) • Y q b) hL.1 Submodule.smul_le_right (fun v hv => root_mem' (hroot b _ (natCast_mem d.l₂).1) (hY q b).2 hs (by simpa [cc] using Base.isIntegral_cc (hs1 v hv b)) (by simpa [cc] using Base.isIntegral_cc (int_of_nok hΛ hN hv b))) hy`. Establish `: (((s : 𝓞 E) : E) • y) b = y b + k • d.l₂.M • y b`. Rewrite using `[hs]`. Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Use `⟨-(k * j), ?_⟩` and prove the remaining obligations. Rewrite `hj` using `[Nat.cast_smul_eq_nsmul]`. Rewrite using `[this, Int.cast_neg, Int.cast_mul, ← hj]`. Simplify using `only [TensLat.EF_eq_bilin, map_add, map_nsmul, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply]`.

Simplify using the standard rewrite rules. Use `congr 1`. Conclude with `datF_congr D h𝔐 hn fun b => (cong_iff hL le_rfl (Submodule.smul_le_right (hww b))).2 (hww b)`. Rewrite using `[ex_sum, ex_sum]`. Use `Finset.prod_congr rfl fun b _ => ex_congr ?_` and prove the remaining obligations.

Take `⟨j, hj⟩` from `EF_int_smul (Y := Y q b) hL.1 (fun s hs => by`. Use `hroot b _ (LevelPairing.bar_mem_Mb (hT.m ▸ hs : s ∈ Mfr d.l₂))` as an intermediate fact. Rewrite using `[cc, ← H.bar_eq]`. Conclude with `this) (hww b)`. Conclude with `⟨j, by rw [← hj]; simp [TensLat.EF_eq_bilin]⟩`.

Establish `h1 : δJ (qRep (x b) - qRep (x' b)) ∈ Jd d • L`. Use `Submodule.smul_mono_left h𝔍 (h b)` as an intermediate fact. Rewrite `this` using `[hz, hz, add_sub_add_left_eq_sub, ← map_sub]`. Then use the resulting hypothesis. Rewrite using `[← hrep (x b), ← hrep (x' b)]`. Conclude with `(Submodule.Quotient.eq _).2 (hJinj _ h1)`.

Take `⟨h1, h2⟩` from `datF_ne_zero D h𝔐 hn (fun k hk => (hT.grp k).1 hk) (left_ne_zero_of_mul hne) choose u hu v hv e using fun b => Submodule.mem_sup.1 (hJsur (hw b)) choose x hx using hu`. Use `⟨fun b => Submodule.Quotient.mk (x b), fun b => ?_⟩` and prove the remaining obligations. Rewrite using `[hT.prod]`. Use `mem_mul_smul hT.cop ((cong_iff hL h𝔐 (sub_mem (hw b) (hzL (fun b => Submodule.Quotient.mk (x b)) b))).1 (cong_trans ?_ (cong_symm (hzM (fun b => Submodule.Quotient.mk (x b)) b)))) ?_` and prove the remaining obligations. Distinguish the cases in `hb : r ≤ (b : ℕ)`.

Conclude with `cong_trans (h2 b hb) (cong_symm (hx0M b hb))`. Conclude with `cong_trans (h1 ⟨b, not_le.1 hb⟩) (cong_symm (hx0.1 ⟨b, not_le.1 hb⟩))`. Establish `h3 : δJ (qRep (Submodule.Quotient.mk (x b) : LaJ Xo c d) - x b) ∈ Jd d • L` using `map_mem_smul hJL ((Submodule.Quotient.eq _).1 (hrep _))`. Use `sub_mem (sub_mem (hv b) (hx0J b)) h3` as an intermediate fact. Express the relevant statement in the definitionally equal form `w b - (d.pd • δ (x0 b) + δJ (qRep (Submodule.Quotient.mk (x b) : LaJ Xo c d))) ∈ _`.

Rewrite using `[← e b, ← hx b]`. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_sub]`. Normalize the expressions using the abelian group laws.
-/
theorem w_eq_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) [Algebra c.F ℂ] [Algebra d.c₂.F ℂ], (∀ t : c.F, algebraMap d.c₂.F ℂ (d.eF t) = algebraMap c.F ℂ t) → d.IsLev → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (x₀ : Fin n → LaJ Xo c d), d.PhiPin ph ψ x₀ → ∀ (r : ℕ) (X : Data E r) (D : SW.Level X) (hn : r ≤ n), r = Dw.p + Dw.q → LevTie d (algebraMap c.F ℂ) ph D hn → ∀ L ∈ D.lats, ∀ (mk mk₂ δ : Dw.La →ₗ[𝓞 E] (Fin r → E)) (x0 : Fin n → Dw.La), IsMark l L mk → IsMark d.l₂ L mk₂ → MarkOver l d.l₂ L mk mk₂ → IsDual X l (algebraMap c.F ℂ (zetaM c)) L mk δ → IsBaseClassLevelAdapted d D hn x0 δ → ∃ t : ℂ, ‖t‖ = 1 ∧ ∀ Λ ∈ Vset E n d.l₂.M, ∀ N : ℕ, NOK Λ N d.l₂.M → ∀ Y : (Fin n → LevQ Dw d.l₂) → Matrix (Fin n) (Fin r) E, IsRoots d.l₂ L mk₂ N Y → ∀ q, algebraMap d.c₂.F ℂ (d.w x0 q) = t * ∑ᶠ cl : tens Λ ((Ideal.span {2} * conjI D.𝔪) • L) ⧸ (tens Λ ((Ideal.span {2} * conjI D.𝔪 * D.𝔪) • L)).addSubgroupOf _, datF D (Mfr l) hn (cl.out : Matrix (Fin n) (Fin r) E) * cexp (-(2 * Real.pi * I * ((∑ b, EF X ((cl.out : Matrix (Fin n) (Fin r) E) b) (Y q b) : ℚ) : ℂ))) := by
  intro E _ _ _ H Dw l Xo c n d _ _ halg hlev ph ψ x₀ hpin r X D hn hr hT L hL mk mk₂ δ x0 hmk hmk₂ hov hδ hx0
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have hpd := (LevelCoverDatum.pd_pos d hlev).ne'
  have hζ := (LevelPairing.zetaM_prim c).map_of_injective (algebraMap c.F ℂ).injective
  have hζ₂ := (LevelPairing.zetaM_prim d.c₂).map_of_injective (algebraMap d.c₂.F ℂ).injective
  obtain ⟨⟨δ₂, hδ₂⟩, hall, -⟩ := GlobalTheory.T.dual_half_level_marking_exists_and_match E H Dw d.l₂ r X L mk₂ _ hL.1 hmk₂ hζ₂
  obtain ⟨hsur, hinj, -⟩ := hall δ₂ hδ₂
  clear hall
  have h𝔐 : D.𝔪 ≤ Mfr l := hT.prod ▸ Ideal.mul_le_left
  have h𝔍 : D.𝔪 ≤ Jd d := hT.prod ▸ Ideal.mul_le_right
  have hpJ : (d.pd : 𝓞 E) ∈ Jd d := (LevelCoverDatum.half_mul_conj d hlev ▸ Ideal.mul_le_right :
    Ideal.span {(d.pd : 𝓞 E)} ≤ Jd d) (Ideal.subset_span rfl)
  have hMM := (natCast_mem l).2
  obtain ⟨p, q', hpq⟩ := Nat.isCoprime_iff_coprime.2 hlev.2.2.1
  have hpq' : (p : 𝓞 E) * d.pd + q' * l.M = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hpq
  set δJ : Dw.La →ₗ[𝓞 E] (Fin r → E) := (l.M : 𝓞 E) • δ₂ with hδJ
  have hJM : ∀ a, δJ a ∈ Mfr l • L := fun a => Submodule.smul_mem_smul hMM (hδ₂.mem a)
  have hJL : ∀ a, δJ a ∈ L := fun a => Submodule.smul_le_right (hJM a)
  have hJsur : L ≤ LinearMap.range δJ ⊔ Jd d • L := fun v hv => by
    obtain ⟨_, ⟨a, rfl⟩, w, hw, rfl⟩ := Submodule.mem_sup.1 (hsur hv)
    refine Submodule.mem_sup.2 ⟨_, ⟨(q' : 𝓞 E) • a, rfl⟩, ((p : 𝓞 E) * d.pd) • δ₂ a + w,
      add_mem (Submodule.smul_mem_smul (Ideal.mul_mem_left _ _ hpJ) (hδ₂.mem a))
        (Submodule.smul_mono_left (hT.m ▸ h𝔍) hw), ?_⟩
    rw [hδJ, LinearMap.smul_apply, map_smul, smul_smul, ← add_assoc, ← add_smul,
      show (l.M : 𝓞 E) * q' + p * d.pd = 1 by linear_combination hpq', one_smul]
  have hJinj : ∀ a, δJ a ∈ Jd d • L → a ∈ Jd d • (⊤ : Submodule (𝓞 E) Dw.La) := fun a ha => by
    have h1 : δ₂ ((l.M : 𝓞 E) • a) ∈ Mfr d.l₂ • L := by
      rw [← hT.m, hT.prod, map_smul]; exact mem_mul_smul hT.cop (hJM a) ha
    have h2 := Submodule.smul_mono_left (hT.m ▸ h𝔍 : Mfr d.l₂ ≤ Jd d) ((hinj _).1 h1)
    have : a = ((p : 𝓞 E) * d.pd) • a + (q' : 𝓞 E) • (l.M : 𝓞 E) • a := by
      rw [smul_smul, ← add_smul, hpq', one_smul]
    rw [this]
    exact add_mem (Submodule.smul_mem_smul (Ideal.mul_mem_left _ _ hpJ) trivial) (Submodule.smul_mem _ _ h2)
  have hrep : ∀ x : LaJ Xo c d, Submodule.Quotient.mk (qRep x) = x := fun x =>
    Classical.choose_spec (Submodule.Quotient.mk_surjective _ x)
  have hx0J : ∀ b, d.pd • δ (x0 b) ∈ Jd d • L := fun b => by
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]; exact Submodule.smul_mem_smul hpJ (hδ.mem _)
  have hx0L : ∀ b, d.pd • δ (x0 b) ∈ L := fun b => Submodule.smul_le_right (hx0J b)
  have hx0M : ∀ k : Fin n, r ≤ (k : ℕ) → Cong X (Mfr l) (d.pd • δ (x0 k)) 0 := fun k hk =>
    (cong_iff hL h𝔐 (by simpa using hx0L k)).2 (by
      simpa using nsmul_mem (map_mem_smul hδ.mem (hx0.2 k hk)) d.pd)
  obtain ⟨t, ht, htie⟩ := hT.tie L hL δJ hJL hJsur
  refine ⟨t, ht, fun Λ hΛ N hN Y hY q => ?_⟩
  choose a ha haq haY using fun b => (hY q b).1
  have hroot : ∀ b, ∀ s ∈ d.l₂.Mb, s • Y q b ∈ L := fun b s hs => root_mem hmk₂ (ha b) (haY b) hs
  obtain ⟨s, k, hs, hs1, hs2⟩ := exists_mult hΛ
  have hM𝔪 : (d.l₂.M : 𝓞 E) ∈ D.𝔪 := hT.m ▸ (natCast_mem d.l₂).2
  have hs𝔪 : (s : 𝓞 E) - 1 ∈ D.𝔪 := by
    rw [hs]; simpa using Ideal.mul_mem_left _ (k : 𝓞 E) hM𝔪
  have hscop : IsCoprime (Ideal.span {(s : 𝓞 E)}) D.𝔪 :=
    Ideal.isCoprime_iff_exists.2 ⟨_, Ideal.subset_span rfl, _, neg_mem hs𝔪, by ring⟩
  let z : (Fin n → LaJ Xo c d) → Matrix (Fin n) (Fin r) E := fun x b => d.pd • δ (x0 b) + δJ (qRep (x b))
  have hz : ∀ x b, z x b = d.pd • δ (x0 b) + δJ (qRep (x b)) := fun _ _ => rfl
  have hzL : ∀ x b, z x b ∈ L := fun x b => add_mem (hx0L b) (hJL _)
  have hzM : ∀ x b, Cong X (Mfr l) (z x b) (d.pd • δ (x0 b)) := fun x b =>
    (cong_iff hL h𝔐 (sub_mem (hzL x b) (hx0L b))).2 (by rw [hz, add_sub_cancel_left]; exact hJM _)
  have key := finsum_tens (Λ := Λ) (L := L) (𝔟 := Ideal.span {2} * conjI D.𝔪) (𝔪 := D.𝔪)
    (D.odd.symm.mul_left D.cop.symm) hs𝔪 (by simpa using hs1) (by simpa using hs2)
    (fun y => datF D (Mfr l) hn y * ex (∑ b, EF X (y b) (Y q b))) (fun y hy => ?_) (fun w w' hw hww => ?_) z hzL
    (fun x x' h => funext fun b => ?_) (fun w hw hne => ?_)
  · refine Eq.trans ?_ (congrArg (t * ·) key.symm)
    unfold DeltaDat.w
    rw [map_mul, map_mul, halg, hpin.2.2.2.2.2 q,
      (algebraMap d.c₂.F ℂ).toAddMonoidHom.map_finsum_of_injective (algebraMap d.c₂.F ℂ).injective _ |>.trans rfl
        |> (show (algebraMap d.c₂.F ℂ) _ = _ from ·), mul_finsum, mul_finsum]
    refine finsum_congr fun x => ?_
    have h1 := htie (fun b => qRep (x b)) (z x) (fun i => ⟨(cong_iff hL h𝔍 (sub_mem (hzL x _) (hJL _))).2
      (by rw [hz, add_sub_cancel_right]; exact hx0J _), cong_trans (hzM x _) (hx0.1 i)⟩)
      (fun k hk => cong_trans (hzM x k) (hx0M k hk))
    simp only [hrep] at h1
    change _ * algebraMap d.c₂.F ℂ _ = _
    rw [map_mul, halg, h1, ← zetaM_pow d hlev, map_zpow₀, map_zpow₀, map_pow, pairL,
      zpow_sum' (hζ.ne_zero hM), zpow_sum' (pow_ne_zero _ (hζ₂.ne_zero (by rw [hlev.2.1]; positivity))), ex_sum,
      mul_left_comm, _root_.mul_assoc t, ← Finset.prod_mul_distrib]
    congr 2
    refine Finset.prod_congr rfl fun b _ => ?_
    have hab : a b - levRep (q b) ∈ d.l₂.Mb • (⊤ : Submodule (𝓞 E) Dw.La) :=
      (Submodule.Quotient.eq _).1 ((haq b).trans
        (Classical.choose_spec (Submodule.Quotient.mk_surjective _ (q b))).symm)
    have e1 : ex (EF X (z x b) (Y q b)) = ex (EF X (z x b) (((d.l₂.M : E)⁻¹) • mk₂ (a b))) := by
      refine ex_congr ?_
      obtain ⟨j, hj⟩ := (hL.1.2 _).1 (hzL x b) _ (haY b)
      exact ⟨j, by rw [← hj]; simp only [TensLat.EF_eq_bilin, map_sub]⟩
    have e2 : EF X (z x b) (((d.l₂.M : E)⁻¹) • mk₂ (a b)) = EF X (δ (x0 b)) (((l.M : E)⁻¹) • mk₂ (a b)) +
        l.M • EF X (δ₂ (qRep (x b))) (((d.l₂.M : E)⁻¹) • mk₂ (a b)) := by
      have : ((l.M : E)⁻¹) • mk₂ (a b) = d.pd • ((d.l₂.M : E)⁻¹) • mk₂ (a b) := by
        have : (d.pd : E) ≠ 0 := by exact_mod_cast hpd
        rw [hlev.2.1]; funext j; simp; field_simp
      rw [this, hz, hδJ, LinearMap.smul_apply, Nat.cast_smul_eq_nsmul]
      simp only [TensLat.EF_eq_bilin, map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply]
    have e3 : ex (EF X (δ (x0 b)) (((l.M : E)⁻¹) • mk₂ (a b))) = ex (EF X (δ (x0 b)) (((l.M : E)⁻¹) • mk (a b))) := by
      refine ex_congr ?_
      obtain ⟨u, hu, e⟩ := hov _ (ha b)
      obtain ⟨j, hj⟩ := (hL.1.2 _).1 (hδ.mem (x0 b)) _ hu
      have : ((l.M : E)⁻¹) • mk₂ (a b) = ((l.M : E)⁻¹) • mk (a b) + u := by
        have : (l.M : E) ≠ 0 := by exact_mod_cast hM
        rw [e]; funext j; simp; field_simp
      exact ⟨j, by rw [← hj, this]; simp only [TensLat.EF_eq_bilin, map_add, add_sub_cancel_left]⟩
    rw [e1, e2, ex_add, e3, ex_nsmul, ex, ex, ← hδ.pair _ _ (Submodule.smul_mono_left (hT.m ▸ h𝔐) (ha b)),
      ← hδ₂.pair _ _ (ha b), ← zpow_natCast (_ ^ (_ : ℤ)), ← _root_.zpow_mul, mul_comm _ (l.M : ℤ), _root_.zpow_mul,
      zpow_natCast]
    congr 1
    · refine zpow_congr' hM hζ.pow_eq_one ?_
      rw [← map_sub, ← smul_sub, ← dvd_neg, ← map_neg, ← smul_neg, neg_sub]
      exact LevelPairing.dvd_right _ (Submodule.smul_mono_left hlev.1.2.1 hab)
    · refine (zpow_congr' hpd ?_ (pd_dvd d hlev (hT.m ▸ h𝔍) _ hab)).symm
      rw [← pow_mul, ← hlev.2.1, hζ₂.pow_eq_one]
  · have hrow := fun b => (Submodule.smul_le_right : _ ≤ L) (row_mem hs1 hy b)
    congr 1
    · refine datF_congr D h𝔐 hn fun b => cong_of hL le_rfl hscop ?_
      have : (s : 𝓞 E) • (y b - (((s : 𝓞 E) : E) • y) b) = (-((s : 𝓞 E) - 1)) • (s : E) • y b := by
        funext j; simp [Algebra.smul_def]; ring
      rw [this]
      exact Submodule.smul_mem_smul (neg_mem hs𝔪) (hrow b)
    · rw [ex_sum, ex_sum]
      refine Finset.prod_congr rfl fun b _ => ex_congr ?_
      obtain ⟨j, hj⟩ := EF_int_tens (b := b) (Y := (d.l₂.M : E) • Y q b) hL.1 Submodule.smul_le_right
        (fun v hv => root_mem' (hroot b _ (natCast_mem d.l₂).1) (hY q b).2 hs
          (by simpa [cc] using Base.isIntegral_cc (hs1 v hv b))
          (by simpa [cc] using Base.isIntegral_cc (int_of_nok hΛ hN hv b))) hy
      have : (((s : 𝓞 E) : E) • y) b = y b + k • d.l₂.M • y b := by
        rw [hs]; funext j; simp; ring
      refine ⟨-(k * j), ?_⟩
      rw [Nat.cast_smul_eq_nsmul] at hj
      rw [this, Int.cast_neg, Int.cast_mul, ← hj]
      simp only [TensLat.EF_eq_bilin, map_add, map_nsmul, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply]
      simp
  · congr 1
    · exact datF_congr D h𝔐 hn fun b => (cong_iff hL le_rfl (Submodule.smul_le_right (hww b))).2 (hww b)
    · rw [ex_sum, ex_sum]
      refine Finset.prod_congr rfl fun b _ => ex_congr ?_
      obtain ⟨j, hj⟩ := EF_int_smul (Y := Y q b) hL.1 (fun s hs => by
        have := hroot b _ (LevelPairing.bar_mem_Mb (hT.m ▸ hs : s ∈ Mfr d.l₂))
        rw [cc, ← H.bar_eq]; exact this) (hww b)
      exact ⟨j, by rw [← hj]; simp [TensLat.EF_eq_bilin]⟩
  · have h1 : δJ (qRep (x b) - qRep (x' b)) ∈ Jd d • L := by
      have := Submodule.smul_mono_left h𝔍 (h b)
      rwa [hz, hz, add_sub_add_left_eq_sub, ← map_sub] at this
    rw [← hrep (x b), ← hrep (x' b)]
    exact (Submodule.Quotient.eq _).2 (hJinj _ h1)
  · obtain ⟨h1, h2⟩ := datF_ne_zero D h𝔐 hn (fun k hk => (hT.grp k).1 hk) (left_ne_zero_of_mul hne)
    choose u hu v hv e using fun b => Submodule.mem_sup.1 (hJsur (hw b))
    choose x hx using hu
    refine ⟨fun b => Submodule.Quotient.mk (x b), fun b => ?_⟩
    rw [hT.prod]
    refine mem_mul_smul hT.cop ((cong_iff hL h𝔐 (sub_mem (hw b) (hzL (fun b => Submodule.Quotient.mk (x b)) b))).1
      (cong_trans ?_ (cong_symm (hzM (fun b => Submodule.Quotient.mk (x b)) b)))) ?_
    · by_cases hb : r ≤ (b : ℕ)
      · exact cong_trans (h2 b hb) (cong_symm (hx0M b hb))
      · exact cong_trans (h1 ⟨b, not_le.1 hb⟩) (cong_symm (hx0.1 ⟨b, not_le.1 hb⟩))
    · have h3 : δJ (qRep (Submodule.Quotient.mk (x b) : LaJ Xo c d) - x b) ∈ Jd d • L :=
        map_mem_smul hJL ((Submodule.Quotient.eq _).1 (hrep _))
      have := sub_mem (sub_mem (hv b) (hx0J b)) h3
      change w b - (d.pd • δ (x0 b) + δJ (qRep (Submodule.Quotient.mk (x b) : LaJ Xo c d))) ∈ _
      rw [← e b, ← hx b]
      convert this using 1
      rw [map_sub]; abel

end GlobalTheory.Dict.CoverFourier
