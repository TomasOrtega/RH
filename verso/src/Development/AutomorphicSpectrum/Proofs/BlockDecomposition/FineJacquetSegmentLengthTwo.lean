import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentTermInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityCuspidalProductStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicitySubquotientLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientCuspidalPermutationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLength
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPos
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitarisableSegmentTwistPrecedesAddOneLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrrParIffCuspidalProduct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.SegFine2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Set `P` to `jacMap e f`. Set `K : Subrepresentation (jac e B)` to `⟨LinearMap.ker P.toLinearMap, fun g x hx => by show P (jac e B g x) = 0`. Rewrite using `[P.isIntertwining]`. Establish `hx' : P x = 0` using `hx`. Rewrite using `[hx', map_zero]⟩`.

Set `κ : K.toRepresentation.IntertwiningMap (jac e B)` to `⟨K.toSubmodule.subtype, fun _ => rfl⟩`. Establish `hadd` using `jhMult_exact κ P hτ Subtype.val_injective (GlobalTheory.JacquetExact.jacMap_surjective e f hf) (fun u => u.2) fun v hv => ⟨⟨v, hv⟩, rfl⟩`. Establish `hz : ∀ x, P (jacMap e ι x) = 0` using `fun x => by`. Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Use `show Submodule.Quotient.mk (f (ι v)) = 0`.

Rewrite using `[h0]`. Both sides reduce to the same expression. Set `ψ : (jac e Z).IntertwiningMap K.toRepresentation` to `⟨LinearMap.codRestrict K.toSubmodule (jacMap e ι).toLinearMap hz, fun g => LinearMap.ext fun x => Subtype.ext ((jacMap e ι).isIntertwining _ _ g x)⟩`. Establish `hψ : Function.Injective ψ` using `fun x y h => GlobalTheory.JacquetExact.jacMap_injective e hB ι hι (congrArg Subtype.val h)`. Establish `h3 : jhMult τ K.toRepresentation ≠ 0` using `jhMult_ne_zero_iff.2 (h1.trans (.of_injective ψ hψ))`.

Establish `h4 : jhMult τ (jac e π) ≠ 0` using `jhMult_ne_zero_iff.2 h2`. Rewrite using `[hadd]`. Establish `h5` using `ENat.one_le_iff_ne_zero.2 h3`. Establish `h6` using `ENat.one_le_iff_ne_zero.2 h4`. Conclude with `(by norm_num : (2 : ℕ∞) = 1 + 1).le.trans (add_le_add h5 h6)`.
-/
theorem two_le_jhMult_of_map {s N : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin N)
    {V W Y U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup U] [Module ℂ U]
    {B : Representation ℂ (GL (Fin N) k) V} (hB : IsSmooth B) {π : Representation ℂ (GL (Fin N) k) W}
    (f : B.IntertwiningMap π) (hf : Function.Surjective f) {Z : Representation ℂ (GL (Fin N) k) U}
    (ι : Z.IntertwiningMap B) (hι : Function.Injective ι) (h0 : ∀ z, f (ι z) = 0)
    {τ : Representation ℂ (Levi k fun a => Fin (d a)) Y} (hτ : τ.IsIrreducible)
    (h1 : IsSubquotient τ (jac e Z)) (h2 : IsSubquotient τ (jac e π)) :
    2 ≤ jhMult τ (jac e B) := by
  let P := jacMap e f
  let K : Subrepresentation (jac e B) := ⟨LinearMap.ker P.toLinearMap, fun g x hx => by
    show P (jac e B g x) = 0
    rw [P.isIntertwining]
    have hx' : P x = 0 := hx
    rw [hx', map_zero]⟩
  let κ : K.toRepresentation.IntertwiningMap (jac e B) := ⟨K.toSubmodule.subtype, fun _ => rfl⟩
  have hadd := jhMult_exact κ P hτ Subtype.val_injective (GlobalTheory.JacquetExact.jacMap_surjective e f hf)
    (fun u => u.2) fun v hv => ⟨⟨v, hv⟩, rfl⟩
  have hz : ∀ x, P (jacMap e ι x) = 0 := fun x => by
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    show Submodule.Quotient.mk (f (ι v)) = 0
    rw [h0]
    rfl
  let ψ : (jac e Z).IntertwiningMap K.toRepresentation :=
    ⟨LinearMap.codRestrict K.toSubmodule (jacMap e ι).toLinearMap hz, fun g => LinearMap.ext fun x =>
      Subtype.ext ((jacMap e ι).isIntertwining _ _ g x)⟩
  have hψ : Function.Injective ψ := fun x y h =>
    GlobalTheory.JacquetExact.jacMap_injective e hB ι hι (congrArg Subtype.val h)
  have h3 : jhMult τ K.toRepresentation ≠ 0 := jhMult_ne_zero_iff.2 (h1.trans (.of_injective ψ hψ))
  have h4 : jhMult τ (jac e π) ≠ 0 := jhMult_ne_zero_iff.2 h2
  rw [hadd]
  have h5 := ENat.one_le_iff_ne_zero.2 h3
  have h6 := ENat.one_le_iff_ne_zero.2 h4
  exact (by norm_num : (2 : ℕ∞) = 1 + 1).le.trans (add_le_add h5 h6)

/- English proof (translation)
Establish `: piTensor ρ g = (∏ a, c a) • LinearMap.id`. Use `PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)` and prove the remaining obligations. Simplify using `only [LinearMap.compMultilinearMap_apply, piTensor_tprod, h, LinearMap.smul_apply, LinearMap.id_apply]`. Conclude with `MultilinearMap.map_smul_univ _ _ _`. Rewrite using `[this]`.

Both sides reduce to the same expression.
-/
theorem piTensor_eq_smul {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (g : ∀ a, Γ a) (c : α → ℂ)
    (h : ∀ a v, ρ a (g a) v = c a • v) (t : ⨂[ℂ] a, X a) : piTensor ρ g t = (∏ a, c a) • t := by
  classical
  have : piTensor ρ g = (∏ a, c a) • LinearMap.id := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
    simp only [LinearMap.compMultilinearMap_apply, piTensor_tprod, h, LinearMap.smul_apply, LinearMap.id_apply]
    exact MultilinearMap.map_smul_univ _ _ _
  rw [this]
  rfl

/- English proof (translation)
Take `⟨S, f, hf⟩` from `h`. Take `⟨w, hw⟩` from `exists_ne (0 : W)`. Take `⟨v, rfl⟩` from `hf w`. Establish `h1` using `f.isIntertwining _ _ g v`. Establish `h2 : S.toRepresentation g v = b • v` using `Subtype.ext (hτ v.1)`.

Rewrite `h1` using `[h2, map_smul, hσ]`. Conclude with `smul_left_injective ℂ hw h1.symm`.
-/
theorem smul_eq_of_isSubquotient {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [Nontrivial W] {σ : Representation ℂ G W} {τ : Representation ℂ G V} (h : IsSubquotient σ τ) (g : G) (a b : ℂ)
    (hσ : ∀ v, σ g v = a • v) (hτ : ∀ v, τ g v = b • v) : a = b := by
  obtain ⟨S, f, hf⟩ := h
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨v, rfl⟩ := hf w
  have h1 := f.isIntertwining _ _ g v
  have h2 : S.toRepresentation g v = b • v := Subtype.ext (hτ v.1)
  rw [h2, map_smul, hσ] at h1
  exact smul_left_injective ℂ hw h1.symm

/- English proof (translation)
Proceed by induction on `d with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [Nat.cast_succ, absPow_add, pow_succ, ih]`.
-/
theorem absPow_natCast (d : ℕ) : absPow k (d : ℂ) = absPow k 1 ^ d := by
  induction d with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, absPow_add, pow_succ, ih]

abbrev seg2 (ρ : IrrGL k) (hρ : ρ.IsCusp) : Segment k := Segment.ofFirst ρ hρ 2 two_pos

/- English proof (translation)
Introduce `h`. Take `⟨ω, -, hω⟩` from `exists_smooth_hasCentralChar ρ.2.rep.smooth ρ.2.rep.irr`. Establish `hc : ∀ s : ℂ, HasCentralChar (ρ.nu s).rep (ω * absPow k s ^ ρ.1)` using `fun s => GlobalTheory.LocGL.UnitaryOrder.hasCentralChar_nu ρ hω s`. Use `haveI := Model.nontrivial_of_isIrreducible (GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA (dec (seg2 ρ hρ)))`. Establish `key : ∀ z : kˣ, (absPow k 1 z : ℂˣ) ^ ρ.1 = 1` using `fun z => by`.

Set `w : Fin 2 → kˣ` to `![z, 1]`. Set `g : ∀ _ : Fin 2, GL (Fin ρ.1) k` to `fun a => Matrix.GeneralLinearGroup.scalar _ (w a)`. Establish `h1` using `smul_eq_of_isSubquotient h g _ _ (piTensor_eq_smul _ g (fun a => (((ω * absPow k (((Fin.rev a : Fin 2) : ℕ) : ℂ) ^ ρ.1) (w a) : ℂˣ) : ℂ)) fun a v => hc _ (w a) v) (piTensor_eq_smul _ g (fun a => (((ω * absPow k ((a : ℕ) : ℂ) ^ ρ.1) (w a) : ℂˣ) : ℂ)) fun a v => hc _ (w a) v)`. Simplify using `[Fin.prod_univ_two, w] at h1`. Conclude with `Units.ext (by simpa using h1)`.

Establish `h2 : absPow k ((ρ.1 : ℝ) : ℂ) = 1`. Use extensionality with `z`. Rewrite using `[Complex.ofReal_natCast, absPow_natCast, MonoidHom.pow_apply, key]`. Both sides reduce to the same expression. Establish `h3` using `(absPow_ofReal_eq_one (k := k)).1 h2`.

Establish `h4` using `hρ.1`. Simplify using `at h3`. Use linear arithmetic over natural numbers and integers.
-/
theorem not_isSubquotient_dec (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (ρ : IrrGL k) (hρ : ρ.IsCusp) :
    ¬ IsSubquotient (piTensor fun a => (dec (seg2 ρ hρ) a).rep) (piTensor fun a => ((seg2 ρ hρ).term a).rep) := by
  intro h
  obtain ⟨ω, -, hω⟩ := exists_smooth_hasCentralChar ρ.2.rep.smooth ρ.2.rep.irr
  have hc : ∀ s : ℂ, HasCentralChar (ρ.nu s).rep (ω * absPow k s ^ ρ.1) := fun s =>
    GlobalTheory.LocGL.UnitaryOrder.hasCentralChar_nu ρ hω s
  haveI := Model.nontrivial_of_isIrreducible (GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA (dec (seg2 ρ hρ)))
  have key : ∀ z : kˣ, (absPow k 1 z : ℂˣ) ^ ρ.1 = 1 := fun z => by
    let w : Fin 2 → kˣ := ![z, 1]
    let g : ∀ _ : Fin 2, GL (Fin ρ.1) k := fun a => Matrix.GeneralLinearGroup.scalar _ (w a)
    have h1 := smul_eq_of_isSubquotient h g _ _
      (piTensor_eq_smul _ g (fun a => (((ω * absPow k (((Fin.rev a : Fin 2) : ℕ) : ℂ) ^ ρ.1) (w a) : ℂˣ) : ℂ))
        fun a v => hc _ (w a) v)
      (piTensor_eq_smul _ g (fun a => (((ω * absPow k ((a : ℕ) : ℂ) ^ ρ.1) (w a) : ℂˣ) : ℂ))
        fun a v => hc _ (w a) v)
    simp [Fin.prod_univ_two, w] at h1
    exact Units.ext (by simpa using h1)
  have h2 : absPow k ((ρ.1 : ℝ) : ℂ) = 1 := by
    ext z
    rw [Complex.ofReal_natCast, absPow_natCast, MonoidHom.pow_apply, key]
    rfl
  have h3 := (absPow_ofReal_eq_one (k := k)).1 h2
  have h4 := hρ.1
  simp at h3
  omega

def subEquiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (Φ : ρ.Equiv σ) (S : Subrepresentation ρ) :
    S.toRepresentation.Equiv (subrepIso Φ S).toRepresentation :=
  equivOfBijective
    { toLinearMap := Φ.toIntertwiningMap.toLinearMap.restrict (p := S.toSubmodule)
        (q := (subrepIso Φ S).toSubmodule) fun v hv =>
          (mem_subrepIso Φ S _).2 (by
            show Φ.symm (Φ v) ∈ S
            rw [Φ.symm_apply_apply]
            exact hv)
      isIntertwining' := fun g => LinearMap.ext fun v => Subtype.ext (Φ.toIntertwiningMap.isIntertwining _ _ g v) }
    ⟨fun v w h => Subtype.ext (Φ.toLinearEquiv.injective (congrArg Subtype.val h)), fun w =>
      ⟨⟨Φ.symm w.1, (mem_subrepIso Φ S _).1 w.2⟩, Subtype.ext (Φ.apply_symm_apply w.1)⟩⟩

def SegConcl {d l : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin d) k) V)
    (e : (Σ _ : Fin l, Fin d) ≃ Fin (l * d)) : Prop :=
  ∃ S : Subrepresentation (multiProd e (segTerm σ l)),
    S.toRepresentation.IsIrreducible ∧
    (∀ S' : Subrepresentation (multiProd e (segTerm σ l)), S'.toRepresentation.IsIrreducible → S' = S) ∧
    Nonempty ((jac e S.toRepresentation).Equiv (piTensor (segTerm σ l)))

/- English proof (translation)
Take `⟨S, hS, hu, ⟨φ⟩⟩` from `H`. Use `⟨subrepIso Φ S, GlobalTheory.Parabolic.isIrreducible_of_equiv (subEquiv Φ S) hS, fun S' hS' => ?_, ⟨((Exponents.jacEquiv _ (subEquiv Φ S).symm).trans φ).trans ψ⟩⟩` and prove the remaining obligations. Take `⟨T, rfl⟩` from `(subrepIso Φ).surjective S'`. Rewrite using `[hu T (GlobalTheory.Parabolic.isIrreducible_of_equiv (subEquiv Φ T).symm hS')]`.
-/
theorem exists_sub_of_equiv {s N : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin N) {V W Y U : Type} [AddCommGroup V]
    [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup Y] [Module ℂ Y] [AddCommGroup U] [Module ℂ U]
    {A : Representation ℂ (GL (Fin N) k) V} {B : Representation ℂ (GL (Fin N) k) W}
    {τ : Representation ℂ (Levi k fun a => Fin (d a)) Y} {τ' : Representation ℂ (Levi k fun a => Fin (d a)) U}
    (Φ : A.Equiv B) (ψ : τ.Equiv τ')
    (H : ∃ S : Subrepresentation A, S.toRepresentation.IsIrreducible ∧
      (∀ S' : Subrepresentation A, S'.toRepresentation.IsIrreducible → S' = S) ∧
      Nonempty ((jac e S.toRepresentation).Equiv τ)) :
    ∃ S : Subrepresentation B, S.toRepresentation.IsIrreducible ∧
      (∀ S' : Subrepresentation B, S'.toRepresentation.IsIrreducible → S' = S) ∧
      Nonempty ((jac e S.toRepresentation).Equiv τ') := by
  obtain ⟨S, hS, hu, ⟨φ⟩⟩ := H
  refine ⟨subrepIso Φ S, GlobalTheory.Parabolic.isIrreducible_of_equiv (subEquiv Φ S) hS, fun S' hS' => ?_,
    ⟨((Exponents.jacEquiv _ (subEquiv Φ S).symm).trans φ).trans ψ⟩⟩
  obtain ⟨T, rfl⟩ := (subrepIso Φ).surjective S'
  rw [hu T (GlobalTheory.Parabolic.isIrreducible_of_equiv (subEquiv Φ T).symm hS')]

/- English proof (translation)
Establish `hN : N = Δ.len * Δ.d`. Rewrite using `[← hd]`. Conclude with `Δ.sum_term_fst`. Substitute `hN` using the available equality. Establish `he : GlobalTheory.Published.consecBlocks Δ.len Δ.d = stdBlocks (fun _ : Fin Δ.len => Δ.d) hd`.

Use `Equiv.ext ?_` and prove the remaining obligations. Introduce and unpack `⟨a, j⟩`. Use `Fin.ext ?_` and prove the remaining obligations. Use `(GlobalTheory.Published.consecBlocks_val _ _ a j).trans (Eq.trans ?_ (stdBlocks_val (fun _ : Fin Δ.len => Δ.d) hd a j).symm)` and prove the remaining obligations. Simplify using `[mul_comm, add_comm]`.

Establish `H : SegConcl Δ.start.rep.ρ (GlobalTheory.Published.consecBlocks Δ.len Δ.d)` using `hZ k Δ.d Δ.len Δ.d_pos Δ.len_pos Δ.start.rep Δ.isCusp_first.2`. Establish `H' : SegConcl Δ.start.rep.ρ (stdBlocks (fun _ : Fin Δ.len => Δ.d) hd)` using `he ▸ H`. Conclude with `exists_sub_of_equiv (stdBlocks (fun a => (Δ.term a).1) hd) (segProdEquiv Δ hd) (piTensorEquiv fun _ => Δ.first.twEquiv _ (isSmoothChar_absPow _)) H'`.
-/
theorem exists_sub (hZ : GlobalTheory.Published.SegmentRepresentation) (Δ : Segment k) {N : ℕ} (hd : ∑ a, (Δ.term a).1 = N) :
    ∃ S : Subrepresentation (prodIrr Δ.term hd), S.toRepresentation.IsIrreducible ∧
      (∀ S' : Subrepresentation (prodIrr Δ.term hd), S'.toRepresentation.IsIrreducible → S' = S) ∧
      Nonempty ((jac (stdBlocks (fun a => (Δ.term a).1) hd) S.toRepresentation).Equiv
        (piTensor fun a => (Δ.term a).rep)) := by
  have hN : N = Δ.len * Δ.d := by
    rw [← hd]
    exact Δ.sum_term_fst
  subst hN
  have he : GlobalTheory.Published.consecBlocks Δ.len Δ.d = stdBlocks (fun _ : Fin Δ.len => Δ.d) hd := by
    refine Equiv.ext ?_
    rintro ⟨a, j⟩
    refine Fin.ext ?_
    refine (GlobalTheory.Published.consecBlocks_val _ _ a j).trans (Eq.trans ?_ (stdBlocks_val (fun _ : Fin Δ.len => Δ.d) hd a j).symm)
    simp [mul_comm, add_comm]
  have H : SegConcl Δ.start.rep.ρ (GlobalTheory.Published.consecBlocks Δ.len Δ.d) :=
    hZ k Δ.d Δ.len Δ.d_pos Δ.len_pos Δ.start.rep Δ.isCusp_first.2
  have H' : SegConcl Δ.start.rep.ρ (stdBlocks (fun _ : Fin Δ.len => Δ.d) hd) := he ▸ H
  exact exists_sub_of_equiv (stdBlocks (fun a => (Δ.term a).1) hd) (segProdEquiv Δ hd)
    (piTensorEquiv fun _ => Δ.first.twEquiv _ (isSmoothChar_absPow _)) H'

/- English proof (translation)
Rewrite using `[GlobalTheory.T.jacquet_multiplicity_cuspidal_product hA Δ.term _ hd hy Δ.isCusp_term fun a => Δ.isCusp_term _]`. Establish `hinj` using `GlobalTheory.CompanionTheory.SegTerm.term_injective hA Δ`. Establish `: {e : Fin Δ.len ≃ Fin Δ.len | ∀ a, Δ.term (σ a) = Δ.term (e a)} = {σ}`. Use extensionality with `e`. Simplify using `only [Set.mem_setOf_eq, Set.mem_singleton_iff]`.

Prove the components needed by the constructor for the conclusion. Conclude with `fun h => (Equiv.ext fun a => hinj (h a)).symm`. Introduce and unpack `rfl a`. Both sides reduce to the same expression. Rewrite using `[this, Set.ncard_singleton]`.

Simplify using the standard rewrite rules.
-/
theorem jm_perm_prod (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) (σ : Equiv.Perm (Fin Δ.len)) {N : ℕ}
    (hy : ∑ a, (Δ.term (σ a)).1 = N) (hd : ∑ a, (Δ.term a).1 = N) :
    jm (fun a => Δ.term (σ a)) hy (prodIrr Δ.term hd) = 1 := by
  rw [GlobalTheory.T.jacquet_multiplicity_cuspidal_product hA Δ.term _ hd hy Δ.isCusp_term fun a => Δ.isCusp_term _]
  have hinj := GlobalTheory.CompanionTheory.SegTerm.term_injective hA Δ
  have : {e : Fin Δ.len ≃ Fin Δ.len | ∀ a, Δ.term (σ a) = Δ.term (e a)} = {σ} := by
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · exact fun h => (Equiv.ext fun a => hinj (h a)).symm
    · rintro rfl a
      rfl
  rw [this, Set.ncard_singleton]
  simp

/- English proof (translation)
Assume the negation of the conclusion as `hn`. Distinguish the cases in `hb : f.ker = ⊥`. Establish `hco : IsCoatom (⊥ : Subrepresentation P)` using `hb ▸ isCoatom_ker hi f hf`. Conclude with `hS (hco.2 S (bot_lt_iff_ne_bot.2 fun e => hn (e ▸ bot_le)))`. Use `haveI : WellFoundedLT (Subrepresentation P) := ((hasFiniteLength_iff_wellFounded _).1 hfl).2 haveI : IsAtomic (Subrepresentation P) := isAtomic_of_orderBot_wellFounded_lt wellFounded_lt`.

Take `⟨A, hA', hAk⟩` from `(eq_bot_or_exists_atom_le f.ker).resolve_left hb`. Conclude with `hn (hu A (GlobalTheory.CuspFactor.irr_of_atom _ A hA') ▸ hAk)`.
-/
theorem sub_le_ker {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {P : Representation ℂ G V} {σ : Representation ℂ G W} (hfl : HasFiniteLength P) (hi : σ.IsIrreducible)
    (f : P.IntertwiningMap σ) (hf : Function.Surjective f) (S : Subrepresentation P)
    (hu : ∀ S' : Subrepresentation P, S'.toRepresentation.IsIrreducible → S' = S) (hS : S ≠ ⊤) : S ≤ f.ker := by
  by_contra hn
  by_cases hb : f.ker = ⊥
  · have hco : IsCoatom (⊥ : Subrepresentation P) := hb ▸ isCoatom_ker hi f hf
    exact hS (hco.2 S (bot_lt_iff_ne_bot.2 fun e => hn (e ▸ bot_le)))
  · haveI : WellFoundedLT (Subrepresentation P) := ((hasFiniteLength_iff_wellFounded _).1 hfl).2
    haveI : IsAtomic (Subrepresentation P) := isAtomic_of_orderBot_wellFounded_lt wellFounded_lt
    obtain ⟨A, hA', hAk⟩ := (eq_bot_or_exists_atom_le f.ker).resolve_left hb
    exact hn (hu A (GlobalTheory.CuspFactor.irr_of_atom _ A hA') ▸ hAk)

/- English proof (translation)
Take `⟨hi, f, hf, -⟩` from `hc`. Establish `hle` using `sub_le_ker (GlobalTheory.CompanionTheory.ProdFL.hasFiniteLength_prodIrr hA x hd) hi f hf S hu hS`. Set `ι : S.toRepresentation.IntertwiningMap (prodIrr x hd)` to `⟨S.toSubmodule.subtype, fun _ => rfl⟩`. Assume the negation of the conclusion as `hne`. Establish `h2` using `two_le_jhMult_of_map (stdBlocks (fun a => (x a).1) hd) (isSmooth_prodIrr x hd) f hf ι Subtype.val_injective (fun z => hle z.2) (GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA x) (.of_injective φ.symm.toIntertwiningMap φ.symm.toLinearEquiv.injective) (jhMult_ne_ …`.

Establish `h3 : (2 : ℕ∞) ≤ 1` using `h2.trans_eq hJ`. Evaluate the numerical expressions using `at h3`.
-/
theorem jm_eq_zero_of_sub (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL k)
    (hd : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (hc : IsCosocle π (prodIrr x hd)) (S : Subrepresentation (prodIrr x hd))
    (hu : ∀ S' : Subrepresentation (prodIrr x hd), S'.toRepresentation.IsIrreducible → S' = S) (hS : S ≠ ⊤)
    (φ : (jac (stdBlocks (fun a => (x a).1) hd) S.toRepresentation).Equiv (piTensor fun a => (x a).rep))
    (hJ : jm x hd (prodIrr x hd) = 1) : jm x hd π = 0 := by
  obtain ⟨hi, f, hf, -⟩ := hc
  have hle := sub_le_ker (GlobalTheory.CompanionTheory.ProdFL.hasFiniteLength_prodIrr hA x hd) hi f hf S hu hS
  let ι : S.toRepresentation.IntertwiningMap (prodIrr x hd) := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  by_contra hne
  have h2 := two_le_jhMult_of_map (stdBlocks (fun a => (x a).1) hd) (isSmooth_prodIrr x hd) f hf ι
    Subtype.val_injective (fun z => hle z.2) (GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA x)
    (.of_injective φ.symm.toIntertwiningMap φ.symm.toLinearEquiv.injective) (jhMult_ne_zero_iff.1 hne)
  have h3 : (2 : ℕ∞) ≤ 1 := h2.trans_eq hJ
  norm_num at h3

/- English proof (translation)
Introduce and unpack `rfl`. Set `ι : (⊤ : Subrepresentation P).toRepresentation.IntertwiningMap P` to `⟨(⊤ : Subrepresentation P).toSubmodule.subtype, fun _ => rfl⟩`. Establish `hιs : Function.Surjective ι` using `fun v => ⟨⟨v, trivial⟩, rfl⟩`. Conclude with `h2 ((h1.trans (.of_surjective _ (GlobalTheory.JacquetExact.jacMap_surjective e ι hιs))).trans (.of_surjective φ.symm.toIntertwiningMap φ.symm.toLinearEquiv.surjective))`.
-/
theorem sub_ne_top {s N : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin N) {V Y U : Type} [AddCommGroup V]
    [Module ℂ V] [AddCommGroup Y] [Module ℂ Y] [AddCommGroup U] [Module ℂ U]
    {P : Representation ℂ (GL (Fin N) k) V} (S : Subrepresentation P)
    {τ : Representation ℂ (Levi k fun a => Fin (d a)) Y} {τ' : Representation ℂ (Levi k fun a => Fin (d a)) U}
    (φ : (jac e S.toRepresentation).Equiv τ') (h1 : IsSubquotient τ (jac e P)) (h2 : ¬ IsSubquotient τ τ') :
    S ≠ ⊤ := by
  rintro rfl
  let ι : (⊤ : Subrepresentation P).toRepresentation.IntertwiningMap P :=
    ⟨(⊤ : Subrepresentation P).toSubmodule.subtype, fun _ => rfl⟩
  have hιs : Function.Surjective ι := fun v => ⟨⟨v, trivial⟩, rfl⟩
  exact h2 ((h1.trans (.of_surjective _ (GlobalTheory.JacquetExact.jacMap_surjective e ι hιs))).trans
    (.of_surjective φ.symm.toIntertwiningMap φ.symm.toLinearEquiv.surjective))

/- English proof (translation)
Take `⟨S, -, hu, ⟨φ⟩⟩` from `exists_sub hZ (seg2 ρ hρ) hd`. Establish `hy : ∑ a, (dec (seg2 ρ hρ) a).1 = N` using `hd`. Establish `h1 : jm (dec (seg2 ρ hρ)) hy (prodIrr (seg2 ρ hρ).term hd) = 1` using `jm_perm_prod hA (seg2 ρ hρ) Fin.revPerm hy hd`. Establish `h2 : jhMult (piTensor fun a => (dec (seg2 ρ hρ) a).rep) (jac (stdBlocks (fun a => ((seg2 ρ hρ).term a).1) hd) (prodIrr (seg2 ρ hρ).term hd)) ≠ 0`. Use `ne_of_eq_of_ne h1 one_ne_zero` and prove the remaining obligations.

Conclude with `jm_eq_zero_of_sub hA _ hd π hc S hu (sub_ne_top _ S φ (jhMult_ne_zero_iff.1 h2) (not_isSubquotient_dec hA ρ hρ)) φ (jm_perm_prod hA (seg2 ρ hρ) 1 hd hd)`.
-/
theorem jm_term_eq_zero (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation) (ρ : IrrGL k)
    (hρ : ρ.IsCusp) {N : ℕ} (hd : ∑ a, ((seg2 ρ hρ).term a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hc : IsCosocle π (prodIrr (seg2 ρ hρ).term hd)) :
    jm (seg2 ρ hρ).term hd π = 0 := by
  obtain ⟨S, -, hu, ⟨φ⟩⟩ := exists_sub hZ (seg2 ρ hρ) hd
  have hy : ∑ a, (dec (seg2 ρ hρ) a).1 = N := hd
  have h1 : jm (dec (seg2 ρ hρ)) hy (prodIrr (seg2 ρ hρ).term hd) = 1 :=
    jm_perm_prod hA (seg2 ρ hρ) Fin.revPerm hy hd
  have h2 : jhMult (piTensor fun a => (dec (seg2 ρ hρ) a).rep)
      (jac (stdBlocks (fun a => ((seg2 ρ hρ).term a).1) hd) (prodIrr (seg2 ρ hρ).term hd)) ≠ 0 := by
    refine ne_of_eq_of_ne h1 one_ne_zero
  exact jm_eq_zero_of_sub hA _ hd π hc S hu
    (sub_ne_top _ S φ (jhMult_ne_zero_iff.1 h2) (not_isSubquotient_dec hA ρ hρ)) φ
    (jm_perm_prod hA (seg2 ρ hρ) 1 hd hd)

/- English proof (translation)
Use `revert e`. Evaluate the decidable proposition.
-/
theorem perm_two (e : Equiv.Perm (Fin 2)) : e = 1 ∨ e = Fin.revPerm := by
  revert e
  decide

/- English proof (translation)
Introduce `N V _ _ π hL`. Take `⟨hd, hc⟩` from `hL`. Establish `hsm` using `isSmooth_prodIrr (seg2 ρ hρ).term hd`. Establish `hsq` using `hc.isSubquotient`. Establish `hπs : IsSmooth π` using `hsq.isSmooth hsm`.

Establish `hz` using `jm_term_eq_zero hA hZ ρ hρ hd π hc`. Establish `hmono : ∀ {c : ℕ} (y : Fin c → IrrGL k) (hy : ∑ a, (y a).1 = N), jm y hy π ≤ jm y hy (prodIrr (seg2 ρ hρ).term hd)` using `fun y hy => GlobalTheory.CompanionTheory.JmMono.jm_le_of_isSubquotient y hy π _ hsm hsq`. Establish `hdec : ∃ hy : ∑ a, (dec (seg2 ρ hρ) a).1 = N, 1 ≤ jm (dec (seg2 ρ hρ)) hy π`. Take `⟨e, he, h1⟩` from `GlobalTheory.T.irreducible_subquotient_cuspidal_permutation hA (seg2 ρ hρ).term hd (seg2 ρ hρ).isCusp_term π hπs hc.1 hsq`. Break down `perm_two e with rfl | rfl` into its components or cases.

Establish `h2 : 1 ≤ jm (seg2 ρ hρ).term hd π` using `h1`. Rewrite `h2` using `[hz]`. Evaluate the numerical expressions using `at h2`. Conclude with `⟨he, h1⟩`. Use `⟨fun hy => ?_, fun c y hy hyc h1 => ?_⟩` and prove the remaining obligations.

Take `⟨_, h1⟩` from `hdec`. Use `le_antisymm ((hmono _ hy).trans_eq (jm_perm_prod hA (seg2 ρ hρ) Fin.revPerm hy hd)) h1` and prove the remaining obligations. Establish `h2` using `h1.trans (hmono y hy)`. Rewrite `h2` using `[GlobalTheory.T.jacquet_multiplicity_cuspidal_product hA (seg2 ρ hρ).term y hd hy (seg2 ρ hρ).isCusp_term hyc]`. Establish `hne : {e : Fin c ≃ Fin (seg2 ρ hρ).len | ∀ a, y a = (seg2 ρ hρ).term (e a)}.Nonempty`.

Assume the negation of the conclusion as `hn`. Rewrite `hn` using `[Set.not_nonempty_iff_eq_empty]`. Rewrite `h2` using `[hn, Set.ncard_empty]`. Simplify using `at h2`. Take `⟨e, he⟩` from `hne`.

Establish `hc2 : c = 2`. Use `Fintype.card_congr e` as an intermediate fact. Rewrite `this` using `[Fintype.card_fin, Fintype.card_fin]`. Conclude with `this`. Substitute `hc2` using the available equality.

Break down `perm_two e with rfl | rfl` into its components or cases. Establish `hyx : y = (seg2 ρ hρ).term` using `funext he`. Substitute `hyx` using the available equality. Establish `h3 : 1 ≤ jm (seg2 ρ hρ).term hd π` using `h1`. Rewrite `h3` using `[hz]`.

Evaluate the numerical expressions using `at h3`. Conclude with `⟨rfl, he⟩`.
-/
theorem fine_jacquet_length_two_segment (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation) (ρ : IrrGL k)
    (hρ : ρ.IsCusp) : FineJac (seg2 ρ hρ) := by
  intro N V _ _ π hL
  obtain ⟨hd, hc⟩ := hL
  have hsm := isSmooth_prodIrr (seg2 ρ hρ).term hd
  have hsq := hc.isSubquotient
  have hπs : IsSmooth π := hsq.isSmooth hsm
  have hz := jm_term_eq_zero hA hZ ρ hρ hd π hc
  have hmono : ∀ {c : ℕ} (y : Fin c → IrrGL k) (hy : ∑ a, (y a).1 = N), jm y hy π ≤ jm y hy (prodIrr (seg2 ρ hρ).term hd) :=
    fun y hy => GlobalTheory.CompanionTheory.JmMono.jm_le_of_isSubquotient y hy π _ hsm hsq
  have hdec : ∃ hy : ∑ a, (dec (seg2 ρ hρ) a).1 = N, 1 ≤ jm (dec (seg2 ρ hρ)) hy π := by
    obtain ⟨e, he, h1⟩ := GlobalTheory.T.irreducible_subquotient_cuspidal_permutation hA (seg2 ρ hρ).term hd (seg2 ρ hρ).isCusp_term π hπs hc.1 hsq
    rcases perm_two e with rfl | rfl
    · have h2 : 1 ≤ jm (seg2 ρ hρ).term hd π := h1
      rw [hz] at h2
      norm_num at h2
    · exact ⟨he, h1⟩
  refine ⟨fun hy => ?_, fun c y hy hyc h1 => ?_⟩
  · obtain ⟨_, h1⟩ := hdec
    refine le_antisymm ((hmono _ hy).trans_eq (jm_perm_prod hA (seg2 ρ hρ) Fin.revPerm hy hd)) h1
  · have h2 := h1.trans (hmono y hy)
    rw [GlobalTheory.T.jacquet_multiplicity_cuspidal_product hA (seg2 ρ hρ).term y hd hy (seg2 ρ hρ).isCusp_term hyc] at h2
    have hne : {e : Fin c ≃ Fin (seg2 ρ hρ).len | ∀ a, y a = (seg2 ρ hρ).term (e a)}.Nonempty := by
      by_contra hn
      rw [Set.not_nonempty_iff_eq_empty] at hn
      rw [hn, Set.ncard_empty] at h2
      simp at h2
    obtain ⟨e, he⟩ := hne
    have hc2 : c = 2 := by
      have := Fintype.card_congr e
      rw [Fintype.card_fin, Fintype.card_fin] at this
      exact this
    subst hc2
    rcases perm_two e with rfl | rfl
    · have hyx : y = (seg2 ρ hρ).term := funext he
      subst hyx
      have h3 : 1 ≤ jm (seg2 ρ hρ).term hd π := h1
      rw [hz] at h3
      norm_num at h3
    · exact ⟨rfl, he⟩

/- English proof (translation)
Introduce `k _ _ _ _ hA hZ Δ h`. Establish `e : seg2 Δ.first Δ.isCusp_first = Δ` using `Segment.ext_first rfl h.symm`. Rewrite using `[← e]`. Conclude with `@fine_jacquet_length_two_segment k _ _ _ _ hA hZ _ _`.
-/
theorem fineJac_of_len_eq_two : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation)
    (Δ : Segment k) (h : Δ.len = 2), FineJac Δ := by
  intro k _ _ _ _ hA hZ Δ h
  have e : seg2 Δ.first Δ.isCusp_first = Δ := Segment.ext_first rfl h.symm
  rw [← e]
  exact @fine_jacquet_length_two_segment k _ _ _ _ hA hZ _ _

end GlobalTheory.CompanionTheory.SegFine2

end
