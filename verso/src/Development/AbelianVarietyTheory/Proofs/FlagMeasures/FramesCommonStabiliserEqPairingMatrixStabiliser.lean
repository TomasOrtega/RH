import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToLePerp
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FrameStab
open GlobalTheory.HL.Eichler GlobalTheory.HL.FrameOnto

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

/- English proof (translation)
Establish `h2 : ∀ v ∈ A, g v ∈ A` using `fun v hv => by simpa using A.add_mem (hBA (h1 _ hv)) hv`. Use `⟨fun v => ⟨fun hv => ?_, h2 v⟩, h1⟩` and prove the remaining obligations. Establish `hs` using `IsArtinian.surjective_of_injective_endomorphism (g.toLinearMap.restrict h2) (fun a b hab => Subtype.ext (g.injective (congrArg Subtype.val hab)))`. Take `⟨a, ha⟩` from `hs ⟨g v, hv⟩`. Establish `: (a : Fin n → E) = v` using `g.injective (congrArg Subtype.val ha)`.

Conclude with `this ▸ a.2`.
-/
theorem mem_unipOn' [IsArtinianRing E] {n : ℕ} {A B : Submodule E (Fin n → E)} (hBA : B ≤ A)
    (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) (h1 : ∀ v ∈ A, g v - v ∈ B) : g ∈ unipOn A B := by
  have h2 : ∀ v ∈ A, g v ∈ A := fun v hv => by simpa using A.add_mem (hBA (h1 _ hv)) hv
  refine ⟨fun v => ⟨fun hv => ?_, h2 v⟩, h1⟩
  have hs := IsArtinian.surjective_of_injective_endomorphism (g.toLinearMap.restrict h2)
    (fun a b hab => Subtype.ext (g.injective (congrArg Subtype.val hab)))
  obtain ⟨a, ha⟩ := hs ⟨g v, hv⟩
  have : (a : Fin n → E) = v := g.injective (congrArg Subtype.val ha)
  exact this ▸ a.2

/- English proof (translation)
Establish `h1 : ∀ (s : Finset ι) (z : Fin n → E), hf L Hm (∑ i ∈ s, a i • x i) z = ∑ i ∈ s, a i * hf L Hm (x i) z`. Introduce `s z`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [hf]`. Consider the case `insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hf_add_l, hf_smul_l, ih]`.

Establish `h2 : ∀ (s : Finset κ) (z : Fin n → E), hf L Hm z (∑ i ∈ s, b i • y i) = ∑ i ∈ s, L.cj (b i) * hf L Hm z (y i)`. Introduce `s z`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [hf]`. Consider the case `insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hf_add_r, hf_smul_r, ih]`.

Rewrite using `[h1]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[h2, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm`.
-/
theorem hf_sum (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) {ι κ : Type} [Fintype ι]
    [Fintype κ] (a : ι → E) (b : κ → E) (x : ι → Fin n → E) (y : κ → Fin n → E) :
    hf L Hm (∑ i, a i • x i) (∑ j, b j • y j) = ∑ i, ∑ j, a i * L.cj (b j) * hf L Hm (x i) (y j) := by
  have h1 : ∀ (s : Finset ι) (z : Fin n → E),
      hf L Hm (∑ i ∈ s, a i • x i) z = ∑ i ∈ s, a i * hf L Hm (x i) z := by
    intro s z
    induction s using Finset.induction_on with
    | empty => simp [hf]
    | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hf_add_l, hf_smul_l, ih]
  have h2 : ∀ (s : Finset κ) (z : Fin n → E),
      hf L Hm z (∑ i ∈ s, b i • y i) = ∑ i ∈ s, L.cj (b i) * hf L Hm z (y i) := by
    intro s z
    induction s using Finset.induction_on with
    | empty => simp [hf]
    | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hf_add_r, hf_smul_r, ih]
  rw [h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm

/- English proof (translation)
Use `hf_sum L Hm a (fun _ : Unit => (1 : E)) x (fun _ => z)` as an intermediate fact. Simplify using `using this`.
-/
theorem hf_sum_l (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) {ι : Type} [Fintype ι]
    (a : ι → E) (x : ι → Fin n → E) (z : Fin n → E) :
    hf L Hm (∑ i, a i • x i) z = ∑ i, a i * hf L Hm (x i) z := by
  have := hf_sum L Hm a (fun _ : Unit => (1 : E)) x (fun _ => z)
  simpa using this

/- English proof (translation)
Introduce `x hx y hy`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy => exact h x hx y hy`.

Consider the case `zero => simp [hf]`. Consider the case `add a b _ _ ha hb => rw [map_add, hf_add_r, hf_add_r, ha, hb]`. Consider the case `smul c a _ ha => rw [map_smul, hf_smul_r, hf_smul_r, ha]`. Consider the case `zero => simp [hf]`. Consider the case `add a b _ _ ha hb => rw [map_add, hf_add_l, hf_add_l, ha, hb]`.

Consider the case `smul c a _ ha => rw [map_smul, hf_smul_l, hf_smul_l, ha]`.
-/
theorem isom_span (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (φ : (Fin n → E) →ₗ[E] (Fin n → E)) (G : Set (Fin n → E))
    (h : ∀ x ∈ G, ∀ y ∈ G, hf L Hm (φ x) (φ y) = hf L Hm x y) :
    ∀ x ∈ Submodule.span E G, ∀ y ∈ Submodule.span E G, hf L Hm (φ x) (φ y) = hf L Hm x y := by
  intro x hx y hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy => exact h x hx y hy
    | zero => simp [hf]
    | add a b _ _ ha hb => rw [map_add, hf_add_r, hf_add_r, ha, hb]
    | smul c a _ ha => rw [map_smul, hf_smul_r, hf_smul_r, ha]
  | zero => simp [hf]
  | add a b _ _ ha hb => rw [map_add, hf_add_l, hf_add_l, ha, hb]
  | smul c a _ ha => rw [map_smul, hf_smul_l, hf_smul_l, ha]

variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

/- English proof (translation)
Establish `hs : {i : Fin (r + 1) | (i : ℕ) < r + 1} = Set.univ`. Use extensionality with `i`. Simplify using `using i.2`. Simplify using `only [Frames.spanTo, hs, Set.image_univ]`.
-/
theorem spanTo_top (g : Fin (r + 1) → S.V) : S.spanTo g (r + 1) = Submodule.span E (Set.range g) := by
  have hs : {i : Fin (r + 1) | (i : ℕ) < r + 1} = Set.univ := by
    ext i; simpa using i.2
  simp only [Frames.spanTo, hs, Set.image_univ]

/- English proof (translation)
Rewrite using `[hf_sum]`. Simplify using `only [Matrix.mul_apply, Finset.sum_mul, cT, Frames.Zh, Frames.h, Matrix.of_apply]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem pair_eq (s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (a b : Fin (r + 1)) :
    hf L S.Hm (∑ i, s' i b • S.f' i) (∑ i, s i a • S.f i) = (cT L s * S.Zh * s') a b := by
  rw [hf_sum]
  simp only [Matrix.mul_apply, Finset.sum_mul, cT, Frames.Zh, Frames.h, Matrix.of_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Establish `hl : ∀ a, s (Fin.last r) a = if a = Fin.last r then 1 else 0`. Introduce `a`. Use `split_ifs with h`. Rewrite using `[h, hs.2]`. Conclude with `hs.1 _ _ (lt_of_le_of_ne (Fin.le_last a) h)`.

Rewrite using `[hf_sum, Finset.sum_eq_single (Fin.last r), Finset.sum_eq_single (Fin.last r)]`. Rewrite using `[hl, hl, gram, gram]`. Apply the tactic sequence `by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r <;> simp [ha, hb]`. Introduce `j _ hj`. Simplify using `[gram, hj]`.

Simplify using the standard rewrite rules. Introduce `j _ hj`. Simplify using `[gram, hj]`. Simplify using the standard rewrite rules.
-/
theorem gram_eq (g : Fin (r + 1) → S.V) (T : Fˣ)
    (gram : ∀ a b, hf L S.Hm (g a) (g b) =
      if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E T else 0)
    (s : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hs : (∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1))
    (a b : Fin (r + 1)) :
    hf L S.Hm (∑ i, s i a • g i) (∑ i, s i b • g i) = hf L S.Hm (g a) (g b) := by
  have hl : ∀ a, s (Fin.last r) a = if a = Fin.last r then 1 else 0 := by
    intro a
    split_ifs with h
    · rw [h, hs.2]
    · exact hs.1 _ _ (lt_of_le_of_ne (Fin.le_last a) h)
  rw [hf_sum, Finset.sum_eq_single (Fin.last r), Finset.sum_eq_single (Fin.last r)]
  · rw [hl, hl, gram, gram]
    by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r <;> simp [ha, hb]
  · intro j _ hj; simp [gram, hj]
  · simp
  · intro j _ hj; simp [gram, hj]
  · simp

/- English proof (translation)
Introduce `v hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨j, hj, rfl⟩` from `hx`. Establish `hj' : (j : ℕ) < l + 1` using `hj`.

Rewrite using `[hg, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), hs.2, one_smul, add_sub_cancel_left]`. Use `Submodule.sum_mem _ fun i hi => ?_` and prove the remaining obligations. Break down `lt_or_gt_of_ne (Finset.ne_of_mem_erase hi) with h | h` into its components or cases. Establish `h' : (i : ℕ) < j` using `h`. Conclude with `Submodule.smul_mem _ _ (mem_spanTo S g (by omega))`.

Rewrite using `[hs.1 i j h]`. Simplify using the standard rewrite rules. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`. Establish `: h (x + y) - (x + y) = (h x - x) + (h y - y)` using `by rw [map_add]; abel`.

Rewrite using `[this]`. Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx`. Rewrite using `[map_smul, ← smul_sub]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem step_mem (g : Fin (r + 1) → S.V)
    (s : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hs : (∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1))
    (h : S.GLV) (hg : ∀ j, h (g j) = ∑ i, s i j • g i) (l : ℕ) :
    ∀ v ∈ S.spanTo g (l + 1), h v - v ∈ S.spanTo g l := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    have hj' : (j : ℕ) < l + 1 := hj
    rw [hg, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), hs.2, one_smul, add_sub_cancel_left]
    refine Submodule.sum_mem _ fun i hi => ?_
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hi) with h | h
    · have h' : (i : ℕ) < j := h
      exact Submodule.smul_mem _ _ (mem_spanTo S g (by omega))
    · rw [hs.1 i j h]; simp
  | zero => simp
  | add x y _ _ hx hy =>
    have : h (x + y) - (x + y) = (h x - x) + (h y - y) := by rw [map_add]; abel
    rw [this]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [map_smul, ← smul_sub]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Establish `hu : ∀ l, h ∈ unipOn (S.spanTo g (l + 1)) (S.spanTo g l)` using `fun l => mem_unipOn' (spanTo_mono S g (Nat.le_succ _)) h (step_mem S g s hs h hg l)`. Use `⟨⟨hi, Subgroup.mem_iInf.2 fun l => hu l⟩, mem_unipOn' (spanTo_le_perp S g T gram) h ?_⟩` and prove the remaining obligations. Introduce `v hv`. Establish `hv' : v ∈ (S.spanTo g (r + 1) ⊔ S.spanTo g' (r + 1)) ⊔ W` using `htop ▸ Submodule.mem_top`. Take `⟨m, hm, w, hw', rfl⟩` from `Submodule.mem_sup.1 hv'`.

Take `⟨x, hx, y, hy, rfl⟩` from `Submodule.mem_sup.1 hm`. Establish `hxp : x ∈ perp L S.Hm (S.spanTo g r)`. Establish `: S.spanTo g (r + 1) ≤ perp L S.Hm (S.spanTo g r)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, -, rfl⟩`.

Conclude with `mem_perp S g T gram i`. Conclude with `this hx`. Establish `hwp : w ∈ perp L S.Hm (S.spanTo g r)` using `fun z hz => hW w hw' z (spanTo_mono S g (Nat.le_succ _) hz)`. Establish `hyp : y ∈ perp L S.Hm (S.spanTo g r)`. Use `sub_mem (sub_mem hv hwp) hxp` as an intermediate fact.

Simplify using `using this`. Establish `hy0 : h y - y = 0`. Use `hnd _ (spanTo_mono S g' (Nat.le_succ _) (step_mem S g' s' hs' h hg' r y hy)) fun z hz => ?_` and prove the remaining obligations. Establish `hz1 : h.symm z ∈ S.spanTo g (r + 1)` using `((hu r).1 _).1 (by simpa using hz)`. Establish `hz2` using `hyp _ ((hu r).2 _ hz1)`.

Establish `hz3` using `hi y (h.symm z)`. Rewrite `hz2`, `hz3` using `[LinearEquiv.apply_symm_apply]`. Rewrite `hz2` using `[hf_sub_r]`. Rewrite using `[hf_sub_l, hz3]`. Take the linear combination `-hz2`.

Establish `: h (x + y + w) - (x + y + w) = h x - x`. Rewrite using `[map_add, map_add, hw w hw', sub_eq_zero.1 hy0]`. Normalize the expressions using the abelian group laws. Rewrite using `[this]`. Conclude with `(hu r).2 x hx`.
-/
theorem mem_Nof [IsArtinianRing E] (g g' : Fin (r + 1) → S.V) (T : Fˣ)
    (gram : ∀ a b, hf L S.Hm (g a) (g b) =
      if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E T else 0)
    (W : Submodule E S.V) (hW : ∀ w ∈ W, ∀ y ∈ S.spanTo g (r + 1), hf L S.Hm w y = 0)
    (htop : (S.spanTo g (r + 1) ⊔ S.spanTo g' (r + 1)) ⊔ W = ⊤)
    (hnd : ∀ u ∈ S.spanTo g' (r + 1), (∀ y ∈ S.spanTo g (r + 1), hf L S.Hm u y = 0) → u = 0)
    (s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hs : (∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1))
    (hs' : (∀ i j, j < i → s' i j = 0) ∧ (∀ i, s' i i = 1))
    (h : S.GLV) (hi : h ∈ isomG L S.Hm) (hg : ∀ j, h (g j) = ∑ i, s i j • g i)
    (hg' : ∀ j, h (g' j) = ∑ i, s' i j • g' i) (hw : ∀ w ∈ W, h w = w) : h ∈ S.Nof g := by
  have hu : ∀ l, h ∈ unipOn (S.spanTo g (l + 1)) (S.spanTo g l) := fun l =>
    mem_unipOn' (spanTo_mono S g (Nat.le_succ _)) h (step_mem S g s hs h hg l)
  refine ⟨⟨hi, Subgroup.mem_iInf.2 fun l => hu l⟩, mem_unipOn' (spanTo_le_perp S g T gram) h ?_⟩
  intro v hv
  have hv' : v ∈ (S.spanTo g (r + 1) ⊔ S.spanTo g' (r + 1)) ⊔ W := htop ▸ Submodule.mem_top
  obtain ⟨m, hm, w, hw', rfl⟩ := Submodule.mem_sup.1 hv'
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hm
  have hxp : x ∈ perp L S.Hm (S.spanTo g r) := by
    have : S.spanTo g (r + 1) ≤ perp L S.Hm (S.spanTo g r) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, -, rfl⟩
      exact mem_perp S g T gram i
    exact this hx
  have hwp : w ∈ perp L S.Hm (S.spanTo g r) := fun z hz => hW w hw' z (spanTo_mono S g (Nat.le_succ _) hz)
  have hyp : y ∈ perp L S.Hm (S.spanTo g r) := by
    have := sub_mem (sub_mem hv hwp) hxp
    simpa using this
  have hy0 : h y - y = 0 := by
    refine hnd _ (spanTo_mono S g' (Nat.le_succ _) (step_mem S g' s' hs' h hg' r y hy)) fun z hz => ?_
    have hz1 : h.symm z ∈ S.spanTo g (r + 1) := ((hu r).1 _).1 (by simpa using hz)
    have hz2 := hyp _ ((hu r).2 _ hz1)
    have hz3 := hi y (h.symm z)
    rw [LinearEquiv.apply_symm_apply] at hz2 hz3
    rw [hf_sub_r] at hz2
    rw [hf_sub_l, hz3]
    linear_combination -hz2
  have : h (x + y + w) - (x + y + w) = h x - x := by
    rw [map_add, map_add, hw w hw', sub_eq_zero.1 hy0]; abel
  rw [this]
  exact (hu r).2 x hx

end

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ L r k S`. Use `L.free` as an intermediate fact. Establish `: Module.Finite F E` using `Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)`. Establish `: IsArtinianRing E` using `IsArtinianRing.of_finite F E`. Take `⟨hli, hco, -, hU, -⟩` from `GlobalTheory.FrameBasic.main L r k S`.

Establish `hU' : IsUnit S.Zh.det` using `hU`. Establish `hME : S.ME = Submodule.span E (Set.range (Sum.elim S.f S.f'))`. Rewrite using `[Frames.ME, spanTo_top, spanTo_top, Set.Sum.elim_range, Submodule.span_union]`. Use `⟨fun h hh w hw => ?_, fun s s' hs hs' => ⟨fun hz => ?_, ?_⟩⟩` and prove the remaining obligations. Establish `hd` using `(linearIndependent_sum.1 hli).2.2`.

Establish `h1 : h w - w ∈ S.spanTo S.f r` using `hh.1.2.2 w fun y hy => hw y (Submodule.mem_sup_left (spanTo_mono S _ (Nat.le_succ _) hy))`. Establish `h2 : h w - w ∈ S.spanTo S.f' r` using `hh.2.2.2 w fun y hy => hw y (Submodule.mem_sup_right (spanTo_mono S _ (Nat.le_succ _) hy))`. Establish `h3` using `spanTo_mono S _ (Nat.le_succ _) h1`. Establish `h4` using `spanTo_mono S _ (Nat.le_succ _) h2`. Rewrite `h3`, `h4` using `[spanTo_top]`.

Conclude with `sub_eq_zero.1 (Submodule.disjoint_def.1 hd _ h3 h4)`. Establish `hco'` using `hco`. Rewrite `hco'` using `[hME]`. Set `t : Fin (r + 1) ⊕ Fin (r + 1) → S.V` to `Sum.elim (fun j => ∑ i, s i j • S.f i) (fun j => ∑ i, s' i j • S.f' i)`. Set `φ : S.V →ₗ[E] S.V` to `LinearMap.ofIsCompl hco' ((Module.Basis.span hli).constr E t) S.W0.subtype`.

Establish `hφ1 : ∀ i, φ (Sum.elim S.f S.f' i) = t i`. Introduce `i`. Establish `h1` using `LinearMap.ofIsCompl_apply_left hco' (φ := (Module.Basis.span hli).constr E t) (ψ := S.W0.subtype) (Module.Basis.span hli i)`. Rewrite `h1` using `[Module.Basis.constr_basis, Module.Basis.span_apply]`. Conclude with `h1`.

Establish `hφ2 : ∀ w ∈ S.W0, φ w = w` using `fun w hw => LinearMap.ofIsCompl_apply_right hco' (φ := (Module.Basis.span hli).constr E t) (ψ := S.W0.subtype) ⟨w, hw⟩`. Establish `hmem : ∀ i, Sum.elim S.f S.f' i ∈ S.ME` using `fun i => hME ▸ Submodule.subset_span ⟨i, rfl⟩`. Establish `htm : ∀ i, t i ∈ S.ME`. Introduce and unpack `(j | j)`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hmem (Sum.inl i))`.

Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hmem (Sum.inr i))`. Establish `hmix : ∀ a b, hf L S.Hm (t (Sum.inr b)) (t (Sum.inl a)) = hf L S.Hm (S.f' b) (S.f a)`. Introduce `a b`. Use `pair_eq S s s' a b` as an intermediate fact. Rewrite `this` using `[hz]`.

Conclude with `this`. Establish `hiso : ∀ x y, hf L S.Hm (φ x) (φ y) = hf L S.Hm x y`. Establish `h1` using `isom_span L S.Hm φ (Set.range (Sum.elim S.f S.f') ∪ S.W0) (by`. Introduce and unpack `_ (⟨i, rfl⟩ | hx) _ (⟨j, rfl⟩ | hy)`. Rewrite using `[hφ1, hφ1]`.

Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j`. Conclude with `gram_eq S S.f S.T S.gram s hs i j`. Rewrite using `[← hf_cj L S.herm.1, hmix, hf_cj L S.herm.1]`. Both sides reduce to the same expression. Conclude with `hmix j i`.

Conclude with `gram_eq S S.f' S.T' S.gram' s' hs' i j`. Rewrite using `[hφ1, hφ2 _ hy, ← hf_cj L S.herm.1, hy _ (htm i), ← hf_cj L S.herm.1 _ (Sum.elim _ _ _), hy _ (hmem i)]`. Rewrite using `[hφ1, hφ2 _ hx, hx _ (htm j), hx _ (hmem j)]`. Rewrite using `[hφ2 _ hx, hφ2 _ hy])`. Rewrite `h1` using `[Submodule.span_union, Submodule.span_eq, hco'.sup_eq_top]`.

Conclude with `fun x y => h1 x trivial y trivial`. Establish `hinj : Function.Injective φ`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `v hv`. Apply `Matrix.vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 S.herm.2)` to reduce the goal to its premises.

Use function extensionality and compare the values at `j`. Establish `h1` using `hiso v (Pi.single j 1)`. Rewrite `h1` using `[hv]`. Simplify `h1.symm` using `[hf, Pi.single_apply, Matrix.vecMul, dotProduct, apply_ite L.cj]`. Set `h : S.GLV` to `LinearEquiv.ofBijective φ (IsArtinian.bijective_of_injective_endomorphism φ hinj)`.

Establish `hg : ∀ j, h (S.f j) = ∑ i, s i j • S.f i` using `fun j => hφ1 (Sum.inl j)`. Establish `hg' : ∀ j, h (S.f' j) = ∑ i, s' i j • S.f' i` using `fun j => hφ1 (Sum.inr j)`. Use `⟨h, ⟨?_, ?_⟩, hg, hg'⟩` and prove the remaining obligations. Use `mem_Nof S S.f S.f' S.T S.gram S.W0 (fun w hw y hy => hw y (Submodule.mem_sup_left hy)) hco.sup_eq_top ?_ s s' hs hs' h hiso hg hg' hφ2` and prove the remaining obligations. Introduce `u hu h0`.

Take `⟨c, -, rfl⟩` from `coords S _ hu`. Establish `: c = 0`. Apply `Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 hU')` to reduce the goal to its premises. Use function extensionality and compare the values at `a`. Establish `h1` using `h0 _ (mem_spanTo S S.f a.2)`.

Rewrite `h1` using `[hf_sum_l]`. Rewrite using `[Matrix.mulVec_zero, Pi.zero_apply, ← h1]`. Unfold `Matrix.mulVec dotProduct`. Conclude with `Finset.sum_congr rfl fun b _ => mul_comm _ _`. Simplify using `[this]`.

Use `mem_Nof S S.f' S.f S.T' S.gram' S.W0 (fun w hw y hy => hw y (Submodule.mem_sup_right hy)) (by rw [sup_comm (S.spanTo S.f' _)]; exact hco.sup_eq_top) ?_ s' s hs' hs h hiso hg' hg hφ2` and prove the remaining obligations. Introduce `u hu h0`. Take `⟨c, -, rfl⟩` from `coords S _ hu`. Establish `: (fun i => L.cj (c i)) = 0`. Apply `Matrix.vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 hU')` to reduce the goal to its premises.

Use function extensionality and compare the values at `a`. Establish `h1` using `congrArg L.cj (h0 _ (mem_spanTo S S.f' a.2))`. Rewrite `h1` using `[hf_sum_l, map_zero, map_sum]`. Simplify using `only [map_mul, hf_cj L S.herm.1] at h1`. Simplify using `only [Matrix.zero_vecMul, Pi.zero_apply]`.

Conclude with `h1`. Establish `h2 : ∀ i, c i = 0` using `fun i => by simpa using congrFun this i`. Simplify using `[h2]`. Introduce and unpack `⟨h, hh, h1, h2⟩`. Use extensionality with `a b`.

Rewrite using `[← pair_eq, ← h1, ← h2]`. Conclude with `hh.1.1.1 _ _`.
-/
theorem stab_eq : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∀ h ∈ S.St, ∀ w ∈ S.W0, h w = w) ∧ ∀ s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) → ((∀ i j, j < i → s' i j = 0) ∧ (∀ i, s' i i = 1)) → (cT L s * S.Zh * s' = S.Zh ↔ ∃ h ∈ S.St, (∀ j, h (S.f j) = ∑ i, s i j • S.f i) ∧ ∀ j, h (S.f' j) = ∑ i, s' i j • S.f' i) := by
  intro F _ _ _ _ _ E _ _ _ L r k S
  have := L.free
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  have : IsArtinianRing E := IsArtinianRing.of_finite F E
  obtain ⟨hli, hco, -, hU, -⟩ := GlobalTheory.FrameBasic.main L r k S
  have hU' : IsUnit S.Zh.det := hU
  have hME : S.ME = Submodule.span E (Set.range (Sum.elim S.f S.f')) := by
    rw [Frames.ME, spanTo_top, spanTo_top, Set.Sum.elim_range, Submodule.span_union]
  refine ⟨fun h hh w hw => ?_, fun s s' hs hs' => ⟨fun hz => ?_, ?_⟩⟩
  · have hd := (linearIndependent_sum.1 hli).2.2
    have h1 : h w - w ∈ S.spanTo S.f r := hh.1.2.2 w fun y hy =>
      hw y (Submodule.mem_sup_left (spanTo_mono S _ (Nat.le_succ _) hy))
    have h2 : h w - w ∈ S.spanTo S.f' r := hh.2.2.2 w fun y hy =>
      hw y (Submodule.mem_sup_right (spanTo_mono S _ (Nat.le_succ _) hy))
    have h3 := spanTo_mono S _ (Nat.le_succ _) h1
    have h4 := spanTo_mono S _ (Nat.le_succ _) h2
    rw [spanTo_top] at h3 h4
    exact sub_eq_zero.1 (Submodule.disjoint_def.1 hd _ h3 h4)
  · have hco' := hco
    rw [hME] at hco'
    let t : Fin (r + 1) ⊕ Fin (r + 1) → S.V :=
      Sum.elim (fun j => ∑ i, s i j • S.f i) (fun j => ∑ i, s' i j • S.f' i)
    let φ : S.V →ₗ[E] S.V :=
      LinearMap.ofIsCompl hco' ((Module.Basis.span hli).constr E t) S.W0.subtype
    have hφ1 : ∀ i, φ (Sum.elim S.f S.f' i) = t i := by
      intro i
      have h1 := LinearMap.ofIsCompl_apply_left hco' (φ := (Module.Basis.span hli).constr E t)
        (ψ := S.W0.subtype) (Module.Basis.span hli i)
      rw [Module.Basis.constr_basis, Module.Basis.span_apply] at h1
      exact h1
    have hφ2 : ∀ w ∈ S.W0, φ w = w := fun w hw =>
      LinearMap.ofIsCompl_apply_right hco' (φ := (Module.Basis.span hli).constr E t)
        (ψ := S.W0.subtype) ⟨w, hw⟩
    have hmem : ∀ i, Sum.elim S.f S.f' i ∈ S.ME := fun i => hME ▸ Submodule.subset_span ⟨i, rfl⟩
    have htm : ∀ i, t i ∈ S.ME := by
      rintro (j | j)
      · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hmem (Sum.inl i))
      · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hmem (Sum.inr i))
    have hmix : ∀ a b, hf L S.Hm (t (Sum.inr b)) (t (Sum.inl a)) = hf L S.Hm (S.f' b) (S.f a) := by
      intro a b
      have := pair_eq S s s' a b
      rw [hz] at this
      exact this
    have hiso : ∀ x y, hf L S.Hm (φ x) (φ y) = hf L S.Hm x y := by
      have h1 := isom_span L S.Hm φ (Set.range (Sum.elim S.f S.f') ∪ S.W0) (by
        rintro _ (⟨i, rfl⟩ | hx) _ (⟨j, rfl⟩ | hy)
        · rw [hφ1, hφ1]
          rcases i with i | i <;> rcases j with j | j
          · exact gram_eq S S.f S.T S.gram s hs i j
          · rw [← hf_cj L S.herm.1, hmix, hf_cj L S.herm.1]; rfl
          · exact hmix j i
          · exact gram_eq S S.f' S.T' S.gram' s' hs' i j
        · rw [hφ1, hφ2 _ hy, ← hf_cj L S.herm.1, hy _ (htm i), ← hf_cj L S.herm.1 _ (Sum.elim _ _ _),
            hy _ (hmem i)]
        · rw [hφ1, hφ2 _ hx, hx _ (htm j), hx _ (hmem j)]
        · rw [hφ2 _ hx, hφ2 _ hy])
      rw [Submodule.span_union, Submodule.span_eq, hco'.sup_eq_top] at h1
      exact fun x y => h1 x trivial y trivial
    have hinj : Function.Injective φ := by
      rw [injective_iff_map_eq_zero]
      intro v hv
      apply Matrix.vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 S.herm.2)
      funext j
      have h1 := hiso v (Pi.single j 1)
      rw [hv] at h1
      simpa [hf, Pi.single_apply, Matrix.vecMul, dotProduct, apply_ite L.cj] using h1.symm
    let h : S.GLV := LinearEquiv.ofBijective φ (IsArtinian.bijective_of_injective_endomorphism φ hinj)
    have hg : ∀ j, h (S.f j) = ∑ i, s i j • S.f i := fun j => hφ1 (Sum.inl j)
    have hg' : ∀ j, h (S.f' j) = ∑ i, s' i j • S.f' i := fun j => hφ1 (Sum.inr j)
    refine ⟨h, ⟨?_, ?_⟩, hg, hg'⟩
    · refine mem_Nof S S.f S.f' S.T S.gram S.W0 (fun w hw y hy => hw y (Submodule.mem_sup_left hy))
        hco.sup_eq_top ?_ s s' hs hs' h hiso hg hg' hφ2
      intro u hu h0
      obtain ⟨c, -, rfl⟩ := coords S _ hu
      have : c = 0 := by
        apply Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 hU')
        funext a
        have h1 := h0 _ (mem_spanTo S S.f a.2)
        rw [hf_sum_l] at h1
        rw [Matrix.mulVec_zero, Pi.zero_apply, ← h1]
        unfold Matrix.mulVec dotProduct
        exact Finset.sum_congr rfl fun b _ => mul_comm _ _
      simp [this]
    · refine mem_Nof S S.f' S.f S.T' S.gram' S.W0 (fun w hw y hy => hw y (Submodule.mem_sup_right hy))
        (by rw [sup_comm (S.spanTo S.f' _)]; exact hco.sup_eq_top) ?_ s' s hs' hs h hiso hg' hg hφ2
      intro u hu h0
      obtain ⟨c, -, rfl⟩ := coords S _ hu
      have : (fun i => L.cj (c i)) = 0 := by
        apply Matrix.vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 hU')
        funext a
        have h1 := congrArg L.cj (h0 _ (mem_spanTo S S.f' a.2))
        rw [hf_sum_l, map_zero, map_sum] at h1
        simp only [map_mul, hf_cj L S.herm.1] at h1
        simp only [Matrix.zero_vecMul, Pi.zero_apply]
        exact h1
      have h2 : ∀ i, c i = 0 := fun i => by simpa using congrFun this i
      simp [h2]
  · rintro ⟨h, hh, h1, h2⟩
    ext a b
    rw [← pair_eq, ← h1, ← h2]
    exact hh.1.1.1 _ _

end GlobalTheory.HL.FrameStab
