import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.ProdList
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPos
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentTermInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorProductDeterminesFactorClassesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos

set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Groth

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace SegJ

open Classical in

/- English proof (translation)
Take `⟨Φ⟩` from `((hZ Δ Δ.start.rep Δ.start.cl_rep (stdBlocks (fun _ : Fin Δ.len => Δ.d) hd) (Z Δ).rep).2).1 (Z Δ).cl_rep`. Set `Ψ : (piTensor (segTerm Δ.start.rep.ρ Δ.len)).Equiv (piTensor fun a => (Δ.term a).rep)` to `piTensorEquiv fun _ => Δ.first.twEquiv _ (isSmoothChar_absPow _)`. Establish `hT : (piTensor fun a => (Δ.term a).rep).IsIrreducible` using `GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA Δ.term`. Rewrite using `[jhMult_congr_right _ (Φ.trans Ψ)]`. Use `split_ifs with h`.

Establish `hy : ∀ a, y a = (Δ.term a).2` using `fun a => eq_of_heq (Sigma.mk.inj_iff.1 (h a)).2`. Take `rfl : y = fun a => (Δ.term a).2` from `funext hy`. Conclude with `jhMult_self hT`. Assume the negation of the conclusion as `hne`. Establish `hy : (piTensor fun a => (y a).rep.ρ).IsIrreducible` using `GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA (fun a => (⟨Δ.d, y a⟩ : IrrGL k))`.

Take `⟨φ⟩` from `GlobalTheory.LocGL.SupportUnique.nonempty_equiv_of_isSubquotient hy hT (jhMult_ne_zero_iff.1 hne)`. Establish `hcl` using `GlobalTheory.T.tensor_product_determines_factor_classes (Fin Δ.len) (fun _ => GL (Fin Δ.d) k) (fun a => (Δ.term a).2.rep) (fun a => (y a).rep) ⟨φ⟩`. Use `h fun a => ?_` and prove the remaining obligations. Establish `h1 : (Δ.term a).2 = y a` using `(IrrCl.cl_rep _).symm.trans ((hcl a).trans (IrrCl.cl_rep _))`. Rewrite using `[← h1]`.

Both sides reduce to the same expression.
-/
theorem jhMult_seg_cl (hA : GlobalTheory.Published.IrreducibleAdmissibleGL)
    {Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)} (hZ : IsSegmentClass k Z) (Δ : Segment k)
    (y : Fin Δ.len → IrrCl (GL (Fin Δ.d) k)) (hd : ∑ _ : Fin Δ.len, Δ.d = Δ.len * Δ.d) :
    jhMult (piTensor fun a => (y a).rep.ρ) (jac (stdBlocks (fun _ : Fin Δ.len => Δ.d) hd) (Z Δ).rep.ρ) =
      if (∀ a, (⟨Δ.d, y a⟩ : IrrGL k) = Δ.term a) then 1 else 0 := by
  obtain ⟨Φ⟩ := ((hZ Δ Δ.start.rep Δ.start.cl_rep (stdBlocks (fun _ : Fin Δ.len => Δ.d) hd) (Z Δ).rep).2).1
    (Z Δ).cl_rep
  let Ψ : (piTensor (segTerm Δ.start.rep.ρ Δ.len)).Equiv (piTensor fun a => (Δ.term a).rep) :=
    piTensorEquiv fun _ => Δ.first.twEquiv _ (isSmoothChar_absPow _)
  have hT : (piTensor fun a => (Δ.term a).rep).IsIrreducible :=
    GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA Δ.term
  rw [jhMult_congr_right _ (Φ.trans Ψ)]
  split_ifs with h
  · have hy : ∀ a, y a = (Δ.term a).2 := fun a => eq_of_heq (Sigma.mk.inj_iff.1 (h a)).2
    obtain rfl : y = fun a => (Δ.term a).2 := funext hy
    exact jhMult_self hT
  · by_contra hne
    have hy : (piTensor fun a => (y a).rep.ρ).IsIrreducible :=
      GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA (fun a => (⟨Δ.d, y a⟩ : IrrGL k))
    obtain ⟨φ⟩ := GlobalTheory.LocGL.SupportUnique.nonempty_equiv_of_isSubquotient hy hT (jhMult_ne_zero_iff.1 hne)
    have hcl := GlobalTheory.T.tensor_product_determines_factor_classes (Fin Δ.len) (fun _ => GL (Fin Δ.d) k) (fun a => (Δ.term a).2.rep)
      (fun a => (y a).rep) ⟨φ⟩
    refine h fun a => ?_
    have h1 : (Δ.term a).2 = y a := (IrrCl.cl_rep _).symm.trans ((hcl a).trans (IrrCl.cl_rep _))
    rw [← h1]
    rfl

open Classical in

/- English proof (translation)
Establish `hm : m = Δ.len`. Establish `h1 : ∑ a, (y a).1 = m * Δ.d` using `by simp [hy]`. Conclude with `Nat.eq_of_mul_eq_mul_right Δ.d_pos (h1.symm.trans hd)`. Substitute `hm` using the available equality. Take `⟨y', rfl⟩ : ∃ y' : Fin Δ.len → IrrCl (GL (Fin Δ.d) k), y = fun a => ⟨Δ.d, y' a⟩` from `⟨fun a => cast (congrArg (fun n => IrrCl (GL (Fin n) k)) (hy a)) (y a).2,`.

Use function extensionality and compare the values at `fun a => Sigma.ext (hy a) (cast_heq _ _).symm⟩`. Use `show jhMult (piTensor fun a => (y' a).rep.ρ) (jac (stdBlocks (fun _ : Fin Δ.len => Δ.d) hd) (Z Δ).rep.ρ) = _`. Rewrite using `[jhMult_seg_cl hA hZ Δ y' hd]`. Use `congr 1`. Conclude with `propext ⟨fun h => ⟨rfl, fun a => by simpa using h a⟩, fun ⟨_, h⟩ a => by simpa using h a⟩`.
-/
theorem jm_seg (hA : GlobalTheory.Published.IrreducibleAdmissibleGL)
    {Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)} (hZ : IsSegmentClass k Z) (Δ : Segment k)
    {m : ℕ} (y : Fin m → IrrGL k) (hy : ∀ a, (y a).1 = Δ.d) (hd : ∑ a, (y a).1 = Δ.len * Δ.d) :
    jm y hd (IrrGL.rep (⟨Δ.len * Δ.d, Z Δ⟩ : IrrGL k)) =
      if ∃ h : m = Δ.len, ∀ a, y a = Δ.term (Fin.cast h a) then 1 else 0 := by
  have hm : m = Δ.len := by
    have h1 : ∑ a, (y a).1 = m * Δ.d := by simp [hy]
    exact Nat.eq_of_mul_eq_mul_right Δ.d_pos (h1.symm.trans hd)
  subst hm
  obtain ⟨y', rfl⟩ : ∃ y' : Fin Δ.len → IrrCl (GL (Fin Δ.d) k), y = fun a => ⟨Δ.d, y' a⟩ :=
    ⟨fun a => cast (congrArg (fun n => IrrCl (GL (Fin n) k)) (hy a)) (y a).2,
      funext fun a => Sigma.ext (hy a) (cast_heq _ _).symm⟩
  show jhMult (piTensor fun a => (y' a).rep.ρ) (jac (stdBlocks (fun _ : Fin Δ.len => Δ.d) hd) (Z Δ).rep.ρ) = _
  rw [jhMult_seg_cl hA hZ Δ y' hd]
  congr 1
  exact propext ⟨fun h => ⟨rfl, fun a => by simpa using h a⟩, fun ⟨_, h⟩ a => by simpa using h a⟩

open Classical in

/- English proof (translation)
Establish `hy : ∀ a, (W.get a).1 = Δ.d` using `fun a => hW _ (List.get_mem _ _)`. Establish `hd : ∑ a, (W.get a).1 = Δ.len * Δ.d`. Rewrite using `[Finset.sum_congr rfl fun a _ => hy a]`. Simplify using `[hl]`. Unfold `jmL`.

Rewrite using `[dif_pos hd, jm_seg hA hZ Δ W.get hy hd]`. Use `congr 1`. Use `propext ⟨fun ⟨h, h2⟩ => ?_, ?_⟩` and prove the remaining obligations. Use `List.ext_get (by simp [h]) fun n h1 h3 => ?_` and prove the remaining obligations. Simplify using `using h2 ⟨n, h1⟩`.

Introduce and unpack `rfl`. Conclude with `⟨List.length_ofFn, fun a => by simp; rfl⟩`.
-/
theorem jmL_seg (hA : GlobalTheory.Published.IrreducibleAdmissibleGL)
    {Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)} (hZ : IsSegmentClass k Z) (Δ : Segment k)
    (W : List (IrrGL k)) (hW : ∀ w ∈ W, w.1 = Δ.d) (hl : W.length = Δ.len) :
    jmL W (IrrGL.rep (⟨Δ.len * Δ.d, Z Δ⟩ : IrrGL k)) = if W = List.ofFn Δ.term then 1 else 0 := by
  have hy : ∀ a, (W.get a).1 = Δ.d := fun a => hW _ (List.get_mem _ _)
  have hd : ∑ a, (W.get a).1 = Δ.len * Δ.d := by
    rw [Finset.sum_congr rfl fun a _ => hy a]
    simp [hl]
  unfold jmL
  rw [dif_pos hd, jm_seg hA hZ Δ W.get hy hd]
  congr 1
  refine propext ⟨fun ⟨h, h2⟩ => ?_, ?_⟩
  · refine List.ext_get (by simp [h]) fun n h1 h3 => ?_
    simpa using h2 ⟨n, h1⟩
  · rintro rfl
    exact ⟨List.length_ofFn, fun a => by simp; rfl⟩

/- English proof (translation)
Introduce `H`. Rewrite `H` using `[vWord, List.ofFn_eq_map]`. Establish `H2` using `(List.map_injective_iff.2 (GlobalTheory.T.segment_term_injective hA Δ)) H`. Take `⟨s, hs⟩` from `Finset.nonempty_iff_ne_empty.2 hne`. Establish `hL1 : ((List.finRange Δ.len).filter fun a => a ∈ S) ≠ []` using `List.ne_nil_of_mem (List.mem_filter.2 ⟨List.mem_finRange s, by simpa using hs⟩)`.

Take `⟨x, t, hxt⟩` from `List.exists_cons_of_ne_nil (List.reverse_ne_nil_iff.2 hL1)`. Establish `hx : x ∈ S`. Establish `: x ∈ ((List.finRange Δ.len).filter fun a => a ∈ S).reverse` using `hxt ▸ List.mem_cons_self ..`. Simplify using `using this`. Rewrite `H2` using `[hxt]`.

Establish `h0` using `congrArg (fun L => L[0]?) H2`. Simplify using `at h0`. Establish `h3` using `(Finset.mem_filter.1 hS).2 x hx`. Rewrite `h0` using `[List.getElem?_eq_getElem (by simpa using Δ.len_pos)]`. Establish `h4` using `Option.some.inj h0`.

Apply `h3` to reduce the goal to its premises. Rewrite using `[h4]`. Simplify using the standard rewrite rules.
-/
theorem vWord_ne (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) (S : Finset (Fin Δ.len))
    (hS : S ∈ vSets Δ) (hne : S ≠ ∅) : vWord Δ S ≠ List.ofFn Δ.term := by
  intro H
  rw [vWord, List.ofFn_eq_map] at H
  have H2 := (List.map_injective_iff.2 (GlobalTheory.T.segment_term_injective hA Δ)) H
  obtain ⟨s, hs⟩ := Finset.nonempty_iff_ne_empty.2 hne
  have hL1 : ((List.finRange Δ.len).filter fun a => a ∈ S) ≠ [] :=
    List.ne_nil_of_mem (List.mem_filter.2 ⟨List.mem_finRange s, by simpa using hs⟩)
  obtain ⟨x, t, hxt⟩ := List.exists_cons_of_ne_nil (List.reverse_ne_nil_iff.2 hL1)
  have hx : x ∈ S := by
    have : x ∈ ((List.finRange Δ.len).filter fun a => a ∈ S).reverse := hxt ▸ List.mem_cons_self ..
    simpa using this
  rw [hxt] at H2
  have h0 := congrArg (fun L => L[0]?) H2
  simp at h0
  have h3 := (Finset.mem_filter.1 hS).2 x hx
  rw [List.getElem?_eq_getElem (by simpa using Δ.len_pos)] at h0
  have h4 := Option.some.inj h0
  apply h3
  rw [h4]
  simp

end SegJ

open SegJ in
variable (k) in

/- English proof (translation)
Introduce `Z hZ Δ`. Establish `hA` using `PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top`. Establish `hterm : ∀ a, (Δ.term a).1 = Δ.d` using `fun _ => rfl`. Use `⟨?_, fun S hS hne => ?_⟩` and prove the remaining obligations. Rewrite using `[jmL_seg hA hZ Δ _ (fun w hw => by rw [List.mem_ofFn] at hw; obtain ⟨a, rfl⟩ := hw; rfl) List.length_ofFn, if_pos rfl]`.

Rewrite using `[jmL_seg hA hZ Δ _ ?_ ?_, if_neg (vWord_ne hA Δ S hS hne)]`. Introduce `w hw`. Take `⟨a, -, rfl⟩` from `List.mem_map.1 hw`. Both sides reduce to the same expression. Simplify using `[vWord]`.

Rewrite using `[← List.length_eq_length_filter_add]`. Simplify using the standard rewrite rules.
-/
theorem jSeg : JSeg k := by
  intro Z hZ Δ
  have hA := PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have hterm : ∀ a, (Δ.term a).1 = Δ.d := fun _ => rfl
  refine ⟨?_, fun S hS hne => ?_⟩
  · rw [jmL_seg hA hZ Δ _ (fun w hw => by rw [List.mem_ofFn] at hw; obtain ⟨a, rfl⟩ := hw; rfl) List.length_ofFn, if_pos rfl]
  · rw [jmL_seg hA hZ Δ _ ?_ ?_, if_neg (vWord_ne hA Δ S hS hne)]
    · intro w hw
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hw
      rfl
    · simp [vWord]
      rw [← List.length_eq_length_filter_add]
      simp

end PositivityTheory.Groth

end
