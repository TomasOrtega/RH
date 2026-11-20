import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

noncomputable section

open Matrix ValuativeRel GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun GlobalTheory.SplitWeil

namespace GlobalTheory.CompanionTheory.BZMirExhaust

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def ballSub (s : kˣ) : AddSubgroup k where
  carrier := cball s
  zero_mem' := by simp [cball]
  add_mem' {a b} ha hb := by
    have ha' : valuation k a ≤ valuation k (s : k) := ha
    have hb' : valuation k b ≤ valuation k (s : k) := hb
    exact (Valuation.map_add _ a b).trans (max_le ha' hb')
  neg_mem' {a} ha := by
    have ha' : valuation k a ≤ valuation k (s : k) := ha
    show valuation k (-a) ≤ valuation k (s : k)
    rwa [Valuation.map_neg]

/- English proof (translation)
Use `Finset.induction_on T ?_ ?_` and prove the remaining obligations. Conclude with `⟨1, by simp⟩`. Introduce `a T _ ih`. Take `⟨s, hs⟩` from `ih`. Distinguish the cases in `h : valuation k a ≤ valuation k (s : k)`.

Use `⟨s, fun x hx => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hx with rfl | hx` into its components or cases. Conclude with `h`. Conclude with `hs x hx`. Establish `ha0 : a ≠ 0`.

Introduce and unpack `rfl`. Conclude with `h (by simp)`. Use `⟨Units.mk0 a ha0, fun x hx => ?_⟩` and prove the remaining obligations. Use `show valuation k x ≤ valuation k a`. Break down `Finset.mem_insert.1 hx with rfl | hx` into its components or cases.

Conclude with `le_rfl`. Establish `hx' : valuation k x ≤ valuation k (s : k)` using `hs x hx`. Conclude with `le_trans hx' (le_of_lt (not_le.1 h))`.
-/
theorem exists_ball_of_finset (T : Finset k) : ∃ s : kˣ, ∀ x ∈ T, x ∈ cball s := by
  classical
  refine Finset.induction_on T ?_ ?_
  · exact ⟨1, by simp⟩
  · intro a T _ ih
    obtain ⟨s, hs⟩ := ih
    by_cases h : valuation k a ≤ valuation k (s : k)
    · refine ⟨s, fun x hx => ?_⟩
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact h
      · exact hs x hx
    · have ha0 : a ≠ 0 := by
        rintro rfl
        exact h (by simp)
      refine ⟨Units.mk0 a ha0, fun x hx => ?_⟩
      show valuation k x ≤ valuation k a
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact le_rfl
      · have hx' : valuation k x ≤ valuation k (s : k) := hs x hx
        exact le_trans hx' (le_of_lt (not_le.1 h))

def unipMir (n : ℕ) : Multiplicative (Fin n → k) →* Mir k n :=
  (unip k n).codRestrict (Mir k n) (fun v => MirU_le_Mir k n ⟨v, rfl⟩)

/- English proof (translation)
Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Unfold `GlobalTheory.BZMir.colMat`. Distinguish the cases in `hj : j = Fin.last n`. Simplify using `only [if_pos hj]`. Break down `Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl` into its components or cases.

Simplify using `only [Fin.lastCases_castSucc]`. Conclude with `continuous_apply i`. Simplify using `only [Fin.lastCases_last]`. Conclude with `continuous_const`. Simplify using `only [if_neg hj]`.

Conclude with `continuous_const`.
-/
theorem continuous_colMat (n : ℕ) : Continuous (colMat k n) := by
  refine continuous_matrix fun i j => ?_
  unfold GlobalTheory.BZMir.colMat
  by_cases hj : j = Fin.last n
  · simp only [if_pos hj]
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
    · simp only [Fin.lastCases_castSucc]
      exact continuous_apply i
    · simp only [Fin.lastCases_last]
      exact continuous_const
  · simp only [if_neg hj]
    exact continuous_const

/- English proof (translation)
Establish `hval : Continuous fun v : Fin n → k => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) + GlobalTheory.BZMir.colMat k n v` using `continuous_const.add (GlobalTheory.CompanionTheory.BZMirExhaust.continuous_colMat n)`. Establish `hinv : Continuous fun v : Fin n → k => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) - GlobalTheory.BZMir.colMat k n v` using `continuous_const.sub (GlobalTheory.CompanionTheory.BZMirExhaust.continuous_colMat n)`. Establish `hGL : Continuous fun v : Fin n → k => GlobalTheory.BZMir.unip k n (Multiplicative.ofAdd v)` using `Units.continuous_iff.2 ⟨hval, hinv⟩`. Conclude with `hGL.subtype_mk _`.
-/
theorem continuous_unipMir (n : ℕ) :
    Continuous (fun v : Fin n → k => unipMir (k := k) n (Multiplicative.ofAdd v)) := by
  have hval : Continuous fun v : Fin n → k =>
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) + GlobalTheory.BZMir.colMat k n v :=
    continuous_const.add (GlobalTheory.CompanionTheory.BZMirExhaust.continuous_colMat n)
  have hinv : Continuous fun v : Fin n → k =>
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) - GlobalTheory.BZMir.colMat k n v :=
    continuous_const.sub (GlobalTheory.CompanionTheory.BZMirExhaust.continuous_colMat n)
  have hGL : Continuous fun v : Fin n → k =>
      GlobalTheory.BZMir.unip k n (Multiplicative.ofAdd v) :=
    Units.continuous_iff.2 ⟨hval, hinv⟩
  exact hGL.subtype_mk _

def ballGroup (n : ℕ) (s : kˣ) : Subgroup (Mir k n) :=
  (AddSubgroup.toSubgroup (AddSubgroup.pi Set.univ fun _ : Fin n => ballSub s)).map (unipMir n)

/- English proof (translation)
Introduce and unpack `_ ⟨v, -, rfl⟩`. Rewrite using `[GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU]`. Conclude with `⟨v, rfl⟩`.
-/
theorem ballGroup_le (n : ℕ) (s : kˣ) : ballGroup (k := k) n s ≤ MirUin k n := by
  rintro _ ⟨v, -, rfl⟩
  rw [GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU]
  exact ⟨v, rfl⟩

/- English proof (translation)
Rewrite using `[GlobalTheory.CompanionTheory.BZMirExhaust.ballGroup, Subgroup.coe_map]`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, rfl⟩`. Conclude with `⟨Multiplicative.toAdd v, hv, rfl⟩`.

Introduce and unpack `⟨v, hv, rfl⟩`. Conclude with `⟨Multiplicative.ofAdd v, hv, rfl⟩`.
-/
theorem coe_ballGroup (n : ℕ) (s : kˣ) : (ballGroup (k := k) n s : Set (Mir k n)) =
    (fun v : Fin n → k => unipMir (k := k) n (Multiplicative.ofAdd v)) '' Set.univ.pi fun _ => cball s := by
  rw [GlobalTheory.CompanionTheory.BZMirExhaust.ballGroup, Subgroup.coe_map]
  ext g
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨Multiplicative.toAdd v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨Multiplicative.ofAdd v, hv, rfl⟩

/- English proof (translation)
Rewrite using `[GlobalTheory.CompanionTheory.BZMirExhaust.coe_ballGroup]`. Conclude with `(isCompact_univ_pi fun _ => GlobalTheory.SplitWeil.isCompact_cball s).image (GlobalTheory.CompanionTheory.BZMirExhaust.continuous_unipMir n)`.
-/
theorem isCompact_ballGroup (n : ℕ) (s : kˣ) : IsCompact (ballGroup (k := k) n s : Set (Mir k n)) := by
  rw [GlobalTheory.CompanionTheory.BZMirExhaust.coe_ballGroup]
  exact (isCompact_univ_pi fun _ => GlobalTheory.SplitWeil.isCompact_cball s).image
    (GlobalTheory.CompanionTheory.BZMirExhaust.continuous_unipMir n)

/- English proof (translation)
Introduce `n S hS`. Take `⟨s, hs⟩` from `GlobalTheory.CompanionTheory.BZMirExhaust.exists_ball_of_finset ((S ×ˢ (Finset.univ : Finset (Fin n))).image fun p => ((p.1 : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc p.2) (Fin.last n))`. Use `⟨GlobalTheory.CompanionTheory.BZMirExhaust.ballGroup n s, GlobalTheory.CompanionTheory.BZMirExhaust.ballGroup_le n s, ?_, GlobalTheory.CompanionTheory.BZMirExhaust.isCompact_ballGroup n s⟩` and prove the remaining obligations. Introduce `g hg`. Establish `hgU` using `hS hg`.

Rewrite `hgU` using `[SetLike.mem_coe, GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU, MonoidHom.mem_range]`. Take `⟨v, hv⟩` from `hgU`. Rewrite `hg` using `[Finset.mem_coe]`. Rewrite using `[SetLike.mem_coe, GlobalTheory.CompanionTheory.BZMirExhaust.ballGroup, Subgroup.mem_map]`. Use `⟨v, ?_, Subtype.ext hv⟩` and prove the remaining obligations.

Use `show ∀ i ∈ Set.univ, Multiplicative.toAdd v i ∈ GlobalTheory.CompanionTheory.BZMirExhaust.ballSub s`. Introduce `i _`. Establish `hvi` using `GlobalTheory.BZMir.unip_apply_castSucc_last k n v i`. Rewrite `hvi` using `[hv]`. Use `show Multiplicative.toAdd v i ∈ GlobalTheory.SplitWeil.cball s`.

Rewrite using `[← hvi]`. Conclude with `hs _ (Finset.mem_image.2 ⟨(g, i), Finset.mem_product.2 ⟨hg, Finset.mem_univ i⟩, rfl⟩)`.
-/
theorem exhaust (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    GlobalTheory.BZMir.Fun.Exhaust k := by
  classical
  intro n S hS
  obtain ⟨s, hs⟩ := GlobalTheory.CompanionTheory.BZMirExhaust.exists_ball_of_finset
    ((S ×ˢ (Finset.univ : Finset (Fin n))).image fun p =>
      ((p.1 : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc p.2) (Fin.last n))
  refine ⟨GlobalTheory.CompanionTheory.BZMirExhaust.ballGroup n s, GlobalTheory.CompanionTheory.BZMirExhaust.ballGroup_le n s, ?_,
    GlobalTheory.CompanionTheory.BZMirExhaust.isCompact_ballGroup n s⟩
  intro g hg
  have hgU := hS hg
  rw [SetLike.mem_coe, GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU,
    MonoidHom.mem_range] at hgU
  obtain ⟨v, hv⟩ := hgU
  rw [Finset.mem_coe] at hg
  rw [SetLike.mem_coe, GlobalTheory.CompanionTheory.BZMirExhaust.ballGroup, Subgroup.mem_map]
  refine ⟨v, ?_, Subtype.ext hv⟩
  show ∀ i ∈ Set.univ, Multiplicative.toAdd v i ∈ GlobalTheory.CompanionTheory.BZMirExhaust.ballSub s
  intro i _
  have hvi := GlobalTheory.BZMir.unip_apply_castSucc_last k n v i
  rw [hv] at hvi
  show Multiplicative.toAdd v i ∈ GlobalTheory.SplitWeil.cball s
  rw [← hvi]
  exact hs _ (Finset.mem_image.2 ⟨(g, i), Finset.mem_product.2 ⟨hg, Finset.mem_univ i⟩, rfl⟩)

end GlobalTheory.CompanionTheory.BZMirExhaust

end
