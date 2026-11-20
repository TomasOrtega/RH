import Mathlib
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.SingleEqSmulSingle
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.BernsteinZelevinsky.TopAdm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsClassificationOrderFreeEquivStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedFormsInterleaveSumStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ContragredientProductIrreducibleImports
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.GlobalTheory.BernsteinZelevinskyFiniteness
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.WordOccursOfSubquotientImports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsInjectiveOfSocleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLengthStatement

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos

set_option synthInstance.maxHeartbeats 400000

namespace CompanionTheory.Groth

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace PhiLAux

/- English proof (translation)
Use `choose π hπ using hs`. Conclude with `⟨fun Δ => ⟨Δ.deg, (π Δ).cl⟩, fun Δ => (hπ Δ).of_equiv (equivRep (π Δ))⟩`.
-/
theorem exists_lseg (hs : LSegExists k) : ∃ Lseg : Segment k → IrrGL k, ∀ Δ, IsLSeg Δ (Lseg Δ).rep := by
  choose π hπ using hs
  exact ⟨fun Δ => ⟨Δ.deg, (π Δ).cl⟩, fun Δ => (hπ Δ).of_equiv (equivRep (π Δ))⟩

/- English proof (translation)
Take `⟨Δ, ⟨hΔ, -⟩, hxΔ⟩` from `hx`. Rewrite using `[← hΔ, Multiset.map_map, ← Finset.sum_eq_multiset_sum]`. Conclude with `Finset.sum_congr rfl fun a _ => ((hxΔ a).deg_eq).symm`.
-/
theorem lfactors_sum {𝔪 : Multiset (Segment k)} {h : ℕ} {x : Fin h → IrrGL k} (hx : LFactors 𝔪 x) :
    ∑ a, (x a).1 = (𝔪.map Segment.deg).sum := by
  obtain ⟨Δ, ⟨hΔ, -⟩, hxΔ⟩ := hx
  rw [← hΔ, Multiset.map_map, ← Finset.sum_eq_multiset_sum]
  exact Finset.sum_congr rfl fun a _ => ((hxΔ a).deg_eq).symm

/- English proof (translation)
Take `⟨_, x, hd, hx, -⟩` from `h`. Rewrite using `[← hd, lfactors_sum hx]`.
-/
theorem isL_deg {𝔪 : Multiset (Segment k)} {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} (h : IsL 𝔪 π) : N = (𝔪.map Segment.deg).sum := by
  obtain ⟨_, x, hd, hx, -⟩ := h
  rw [← hd, lfactors_sum hx]

/- English proof (translation)
Take `⟨n, a⟩` from `x`. Take `⟨m, b⟩` from `y`. Establish `e : n = m` using `(isL_deg hx).trans (isL_deg hy).symm`. Substitute `e` using the available equality. Conclude with `congrArg (Sigma.mk n) (irrCl_eq_iff.2 (GlobalTheory.T.langlands_classification_order_free_equiv hf 𝔪 _ _ hx hy))`.
-/
theorem isL_cls_unique (hf : LOrderFree k) {𝔪 : Multiset (Segment k)} {x y : IrrGL k} (hx : IsL 𝔪 x.rep)
    (hy : IsL 𝔪 y.rep) : x = y := by
  obtain ⟨n, a⟩ := x
  obtain ⟨m, b⟩ := y
  have e : n = m := (isL_deg hx).trans (isL_deg hy).symm
  subst e
  exact congrArg (Sigma.mk n) (irrCl_eq_iff.2 (GlobalTheory.T.langlands_classification_order_free_equiv hf 𝔪 _ _ hx hy))

/- English proof (translation)
Take `⟨h₁, -, -, Δ₁, -, -, hΔ₁, -⟩` from `GlobalTheory.T.ordered_forms_interleave_sum CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top 𝔪 0`. Conclude with `⟨h₁, Δ₁, hΔ₁⟩`.
-/
theorem exists_orderedForm (𝔪 : Multiset (Segment k)) : ∃ (h : ℕ) (Δ : Fin h → Segment k), IsOrderedForm Δ 𝔪 := by
  obtain ⟨h₁, -, -, Δ₁, -, -, hΔ₁, -⟩ := GlobalTheory.T.ordered_forms_interleave_sum CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top 𝔪 0
  exact ⟨h₁, Δ₁, hΔ₁⟩

/- English proof (translation)
Unfold `cl0`. Rewrite using `[dif_pos hl]`. Conclude with `(clsGL_apply π hl c).trans (cls_apply π hl c)`.
-/
theorem class_apply_same_degree {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (hl : HasFiniteLength π) (c : IrrCl (GL (Fin N) k)) : cl0 π ⟨N, c⟩ = ((jhMult c.rep.ρ π).toNat : ℤ) := by
  unfold cl0
  rw [dif_pos hl]
  exact (clsGL_apply π hl c).trans (cls_apply π hl c)

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Unfold `cl0`. Use `split_ifs with hl`. Rewrite using `[clsGL]`. Conclude with `Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨c, rfl⟩; exact hy rfl)`. Both sides reduce to the same expression.
-/
theorem class_apply_other_degree {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (y : IrrGL k) (hy : y.1 ≠ N) : cl0 π y = 0 := by
  unfold cl0
  split_ifs with hl
  · rw [clsGL]
    exact Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨c, rfl⟩; exact hy rfl)
  · rfl

/- English proof (translation)
Take `⟨n, c⟩` from `y`. Simplify using `only at hd`. Substitute `hd` using the available equality. Conclude with `class_apply_same_degree _ (GlobalTheory.T.product_irreducible_finite_length CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top x _) c`.
-/
theorem class_product_irreducible_apply {h : ℕ} (x : Fin h → IrrGL k) (y : IrrGL k) (hd : ∑ a, (x a).1 = y.1) :
    cl0 (prodIrr x (N := ∑ a, (x a).1) rfl) y = ((jhMult y.rep (prodIrr x hd)).toNat : ℤ) := by
  obtain ⟨n, c⟩ := y
  dsimp only at hd
  subst hd
  exact class_apply_same_degree _ (GlobalTheory.T.product_irreducible_finite_length CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top x _) c

/- English proof (translation)
Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons a s ih`. Rewrite using `[Multiset.map_cons, Multiset.sum_cons, Multiset.sum_cons]`. Establish `h1 : (a + s.sum) ^ 2 = a ^ 2 + 2 * a * s.sum + s.sum ^ 2` using `by ring`.

Establish `h2` using `Nat.zero_le (2 * a * s.sum)`. Rewrite using `[h1]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sum_sq_le (s : Multiset ℕ) : (s.map fun l => l ^ 2).sum ≤ s.sum ^ 2 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.sum_cons]
    have h1 : (a + s.sum) ^ 2 = a ^ 2 + 2 * a * s.sum + s.sum ^ 2 := by ring
    have h2 := Nat.zero_le (2 * a * s.sum)
    rw [h1]
    linarith

/- English proof (translation)
Establish `hc : Multiset.card (msupp 𝔪) = (𝔪.map Segment.len).sum`. Rewrite using `[msupp, Multiset.card_bind]`. Simplify using `[Segment.card_ms]`. Establish `hs : CompanionTheory.Groth.sq 𝔪 = ((𝔪.map Segment.len).map fun l => l ^ 2).sum`. Rewrite using `[Multiset.map_map]`.

Both sides reduce to the same expression. Rewrite using `[hc, hs]`. Conclude with `sum_sq_le _`.
-/
theorem sq_le (𝔪 : Multiset (Segment k)) : CompanionTheory.Groth.sq 𝔪 ≤ (Multiset.card (msupp 𝔪)) ^ 2 := by
  have hc : Multiset.card (msupp 𝔪) = (𝔪.map Segment.len).sum := by
    rw [msupp, Multiset.card_bind]
    simp [Segment.card_ms]
  have hs : CompanionTheory.Groth.sq 𝔪 = ((𝔪.map Segment.len).map fun l => l ^ 2).sum := by
    rw [Multiset.map_map]
    rfl
  rw [hc, hs]
  exact sum_sq_le _

/- English proof (translation)
Use `Finsupp.induction s ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `a n f _ _ ih`. Rewrite using `[map_add, Multiset.map_add, Multiset.prod_add, ih, Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), Finsupp.toMultiset_single, Multiset.map_nsmul, Multiset.prod_nsmul, Multiset.map_singleton, Multiset.prod_singleton]`. Use `congr 1`.

Conclude with `(Finsupp.prod_single_index (h := fun x m => g x ^ m) (pow_zero (g a))).symm`.
-/
theorem prod_map_toMultiset {M : Type*} [CommMonoid M] {α : Type*} (g : α → M) (s : α →₀ ℕ) :
    ((Finsupp.toMultiset s).map g).prod = s.prod fun a n => g a ^ n := by
  refine Finsupp.induction s ?_ ?_
  · simp
  · intro a n f _ _ ih
    rw [map_add, Multiset.map_add, Multiset.prod_add, ih,
      Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
      Finsupp.toMultiset_single, Multiset.map_nsmul, Multiset.prod_nsmul, Multiset.map_singleton,
      Multiset.prod_singleton]
    congr 1
    exact (Finsupp.prod_single_index (h := fun x m => g x ^ m) (pow_zero (g a))).symm

variable [Fact (Assoc k)] [Fact (Comm k)] [Fact (One k)]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp [toR_unit]`. Consider the case `cons y l ih => rw [List.foldr_cons, toR_mulR, ih, List.map_cons, List.prod_cons]`.
-/
theorem toR_foldr (l : List (IrrGL k)) :
    toR (l.foldr (fun y a => mulR (sg y) a) (GrothGL.unit k)) = (l.map fun y => toR (sg y)).prod := by
  induction l with
  | nil => simp [toR_unit]
  | cons y l ih => rw [List.foldr_cons, toR_mulR, ih, List.map_cons, List.prod_cons]

/- English proof (translation)
Rewrite using `[hPL h N x hd, toR_foldr, List.map_ofFn, List.prod_ofFn]`. Both sides reduce to the same expression.
-/
theorem ring_class_product_irreducible (hPL : ProdList k) {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) :
    toR (cl0 (prodIrr x hd)) = ∏ a, toR (sg (x a)) := by
  rw [hPL h N x hd, toR_foldr, List.map_ofFn, List.prod_ofFn]
  rfl

end PhiLAux

variable [Fact (Assoc k)] [Fact (Comm k)] [Fact (One k)]

/- English proof (translation)
Take `⟨c, -, -, -, -, hPL, hTri, hMO, -⟩` from `hk`. Take `⟨Lseg, hLseg⟩` from `PhiLAux.exists_lseg c.seg`. Establish `hInj : LInjective k` using `GlobalTheory.T.langlands_injective_of_socle CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top c.soc c.jac`. Use `choose Lm hLm using c.ex`. Establish `hLbij : Function.Bijective Lm`.

Use `⟨fun 𝔪 𝔫 e => hInj 𝔪 𝔫 (Lm 𝔪) (hLm 𝔪) (by rw [e]; exact hLm 𝔫), fun x => ?_⟩` and prove the remaining obligations. Take `⟨𝔪, h𝔪⟩` from `c.exh x`. Conclude with `⟨𝔪, PhiLAux.isL_cls_unique c.free (hLm 𝔪) h𝔪⟩`. Set `L : Multiset (Segment k) ≃ IrrGL k` to `Equiv.ofBijective Lm hLbij`. Use `choose hO Δo hΔo using PhiLAux.exists_orderedForm (k := k)`.

Establish `hLF : ∀ 𝔪, LFactors 𝔪 (fun a => Lseg (Δo 𝔪 a))` using `fun 𝔪 => ⟨Δo 𝔪, hΔo 𝔪, fun _ => hLseg _⟩`. Set `f : Multiset (Segment k) → IrrGL k →₀ ℤ` to `fun 𝔪 => cl0 (prodIrr (fun a => Lseg (Δo 𝔪 a)) (N := ∑ a, (Lseg (Δo 𝔪 a)).1) rfl)`. Establish `hf1 : ∀ 𝔪, f 𝔪 (L 𝔪) = 1`. Introduce `𝔪`. Establish `hd : ∑ a, (Lseg (Δo 𝔪 a)).1 = (Lm 𝔪).1` using `(PhiLAux.lfactors_sum (hLF 𝔪)).trans (PhiLAux.isL_deg (hLm 𝔪)).symm`.

Use `show cl0 _ (Lm 𝔪) = 1`. Rewrite using `[PhiLAux.class_product_irreducible_apply _ _ hd, hMO 𝔪 _ _ _ hd (hLF 𝔪) (hLm 𝔪)]`. Both sides reduce to the same expression. Establish `hf2 : ∀ 𝔪 𝔫, f 𝔪 (L 𝔫) ≠ 0 → msupp 𝔪 = msupp 𝔫 ∧ (𝔪 = 𝔫 ∨ CompanionTheory.Groth.sq 𝔪 < CompanionTheory.Groth.sq 𝔫)`. Introduce `𝔪 𝔫 h0`.

Distinguish the cases in `hd : ∑ a, (Lseg (Δo 𝔪 a)).1 = (Lm 𝔫).1`. Use `hTri 𝔪 𝔫 _ _ (Lm 𝔫) hd (hLF 𝔪) (hLm 𝔫) fun e => h0 ?_ show cl0 _ (Lm 𝔫) = 0` and prove the remaining obligations. Rewrite using `[PhiLAux.class_product_irreducible_apply _ _ hd, e]`. Both sides reduce to the same expression. Conclude with `absurd (PhiLAux.class_apply_other_degree _ _ (Ne.symm hd)) h0`.

Take `⟨hbij, hinv⟩` from `h2 _ _ _ L msupp CompanionTheory.Groth.sq (fun C => Multiset.card C ^ 2) f PhiLAux.sq_le hf1 hf2`. Set `e : (Segment k →₀ ℕ) ≃ Multiset (Segment k)` to `(Multiset.toFinsupp (α := Segment k)).symm.toEquiv`. Establish `he : ∀ s, e s = Finsupp.toMultiset s` using `fun s => by show (Multiset.toFinsupp (α := Segment k)).symm s = _`. Rewrite using `[AddEquiv.symm_apply_eq]`. Simplify using the standard rewrite rules.

Set `G : MvPolynomial (Segment k) ℤ →+ R k` to `toR.toAddMonoidHom.comp ((Finsupp.linearCombination ℤ f).toAddMonoidHom.comp ((Finsupp.domCongr (M := ℤ) e).toAddMonoidHom.comp (AddMonoidAlgebra.coeffAddEquiv (R := ℤ) (M := Segment k →₀ ℕ)).toAddMonoidHom))`. Establish `hGbij : Function.Bijective G` using `toR.bijective.comp (hbij.comp ((Finsupp.domCongr e).bijective.comp (AddMonoidAlgebra.coeffAddEquiv (R := ℤ) (M := Segment k →₀ ℕ)).bijective))`. Establish `hprod : ∀ (h N : ℕ) (Γ : Fin h → Segment k) (hd : ∑ a, (Lseg (Γ a)).1 = N), phiOf Lseg (∏ a, MvPolynomial.X (Γ a)) = toR (cl0 (prodIrr (fun a => Lseg (Γ a)) hd))`. Introduce `h N Γ hd`. Rewrite using `[map_prod, PhiLAux.ring_class_product_irreducible hPL]`.

Conclude with `Finset.prod_congr rfl fun a _ => phiOf_X _ _`. Establish `hmono : ∀ s : Segment k →₀ ℕ, toR (f (e s)) = s.prod fun n m => toR (sg (Lseg n)) ^ m`. Introduce `s`. Use `show toR (cl0 _) = _`. Rewrite using `[PhiLAux.ring_class_product_irreducible hPL, Finset.prod_eq_multiset_prod, ← PhiLAux.prod_map_toMultiset (fun n => toR (sg (Lseg n)))]`.

Establish `h1 : Finsupp.toMultiset s = Finset.univ.val.map (Δo (e s))` using `(he s).symm.trans (hΔo (e s)).1.symm`. Rewrite using `[h1, Multiset.map_map]`. Both sides reduce to the same expression. Establish `hG : ∀ p, phiOf Lseg p = G p`. Introduce `p`.

Use `MvPolynomial.induction_on' p (fun s a => ?_) (fun p q hp hq => ?_)` and prove the remaining obligations. Establish `h1 : G (MvPolynomial.monomial s a) = a • toR (f (e s))` using `by show toR (Finsupp.linearCombination ℤ f (Finsupp.domCongr e (Finsupp.single s a))) = _`. Rewrite using `[Finsupp.domCongr_apply, Finsupp.equivMapDomain_single, Finsupp.linearCombination_single, map_zsmul]`. Rewrite using `[h1, hmono, phiOf, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial, eq_intCast, ← zsmul_eq_mul]`. Rewrite using `[map_add, map_add, hp, hq]`.

Establish `hphiG : ⇑(phiOf Lseg) = ⇑G` using `funext hG`. Use `⟨Lseg, hLseg, hphiG ▸ hGbij, fun 𝔫 x hx => ?_, hprod⟩` and prove the remaining obligations. Take `⟨a, ha, hLa⟩` from `hinv 𝔫`. Establish `hxL : x = Lm 𝔫` using `PhiLAux.isL_cls_unique c.free hx (hLm 𝔫)`. Set `cE` to `AddMonoidAlgebra.coeffAddEquiv (R := ℤ) (M := Segment k →₀ ℕ)`.

Use `⟨cE.symm ((Finsupp.domCongr e).symm a), ?_, fun s hs => ?_⟩` and prove the remaining obligations. Rewrite using `[hG] show toR (Finsupp.linearCombination ℤ f (Finsupp.domCongr e (cE (cE.symm ((Finsupp.domCongr e).symm a))))) = _`. Rewrite using `[AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, hLa, hxL]`. Both sides reduce to the same expression. Rewrite `hs` using `[MvPolynomial.mem_support_iff]`.

Establish `key : a (e s) = ((Finsupp.domCongr e).symm a : (Segment k →₀ ℕ) →₀ ℤ) s` using `by conv_lhs => rw [← AddEquiv.apply_symm_apply (Finsupp.domCongr e) a]`. Rewrite using `[Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply]`. Rewrite using `[← he s]`. Conclude with `ha _ (Finsupp.mem_support_iff.2 (by rw [key]; exact hs))`.
-/
theorem phiL_main (hk : Steps k) (h2 : UniTri) :
    ∃ Lseg : Segment k → IrrGL k, (∀ Δ, IsLSeg Δ (Lseg Δ).rep) ∧ Function.Bijective (phiOf Lseg) ∧
      (∀ (𝔫 : Multiset (Segment k)) (x : IrrGL k), IsL 𝔫 x.rep →
        ∃ p : MvPolynomial (Segment k) ℤ, phiOf Lseg p = toR (sg x) ∧
          ∀ s ∈ p.support, msupp (Finsupp.toMultiset s) = msupp 𝔫) ∧
      ∀ (h N : ℕ) (Γ : Fin h → Segment k) (hd : ∑ a, (Lseg (Γ a)).1 = N),
        phiOf Lseg (∏ a, MvPolynomial.X (Γ a)) = toR (cl0 (prodIrr (fun a => Lseg (Γ a)) hd)) := by
  classical
  obtain ⟨c, -, -, -, -, hPL, hTri, hMO, -⟩ := hk
  obtain ⟨Lseg, hLseg⟩ := PhiLAux.exists_lseg c.seg
  have hInj : LInjective k := GlobalTheory.T.langlands_injective_of_socle CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top c.soc c.jac
  choose Lm hLm using c.ex
  have hLbij : Function.Bijective Lm := by
    refine ⟨fun 𝔪 𝔫 e => hInj 𝔪 𝔫 (Lm 𝔪) (hLm 𝔪) (by rw [e]; exact hLm 𝔫), fun x => ?_⟩
    obtain ⟨𝔪, h𝔪⟩ := c.exh x
    exact ⟨𝔪, PhiLAux.isL_cls_unique c.free (hLm 𝔪) h𝔪⟩
  let L : Multiset (Segment k) ≃ IrrGL k := Equiv.ofBijective Lm hLbij
  choose hO Δo hΔo using PhiLAux.exists_orderedForm (k := k)
  have hLF : ∀ 𝔪, LFactors 𝔪 (fun a => Lseg (Δo 𝔪 a)) := fun 𝔪 => ⟨Δo 𝔪, hΔo 𝔪, fun _ => hLseg _⟩
  let f : Multiset (Segment k) → IrrGL k →₀ ℤ := fun 𝔪 =>
    cl0 (prodIrr (fun a => Lseg (Δo 𝔪 a)) (N := ∑ a, (Lseg (Δo 𝔪 a)).1) rfl)
  have hf1 : ∀ 𝔪, f 𝔪 (L 𝔪) = 1 := by
    intro 𝔪
    have hd : ∑ a, (Lseg (Δo 𝔪 a)).1 = (Lm 𝔪).1 :=
      (PhiLAux.lfactors_sum (hLF 𝔪)).trans (PhiLAux.isL_deg (hLm 𝔪)).symm
    show cl0 _ (Lm 𝔪) = 1
    rw [PhiLAux.class_product_irreducible_apply _ _ hd, hMO 𝔪 _ _ _ hd (hLF 𝔪) (hLm 𝔪)]
    rfl
  have hf2 : ∀ 𝔪 𝔫, f 𝔪 (L 𝔫) ≠ 0 →
      msupp 𝔪 = msupp 𝔫 ∧ (𝔪 = 𝔫 ∨ CompanionTheory.Groth.sq 𝔪 < CompanionTheory.Groth.sq 𝔫) := by
    intro 𝔪 𝔫 h0
    by_cases hd : ∑ a, (Lseg (Δo 𝔪 a)).1 = (Lm 𝔫).1
    · refine hTri 𝔪 𝔫 _ _ (Lm 𝔫) hd (hLF 𝔪) (hLm 𝔫) fun e => h0 ?_
      show cl0 _ (Lm 𝔫) = 0
      rw [PhiLAux.class_product_irreducible_apply _ _ hd, e]
      rfl
    · exact absurd (PhiLAux.class_apply_other_degree _ _ (Ne.symm hd)) h0
  obtain ⟨hbij, hinv⟩ := h2 _ _ _ L msupp CompanionTheory.Groth.sq (fun C => Multiset.card C ^ 2) f PhiLAux.sq_le hf1 hf2
  let e : (Segment k →₀ ℕ) ≃ Multiset (Segment k) := (Multiset.toFinsupp (α := Segment k)).symm.toEquiv
  have he : ∀ s, e s = Finsupp.toMultiset s := fun s => by
    show (Multiset.toFinsupp (α := Segment k)).symm s = _
    rw [AddEquiv.symm_apply_eq]
    simp
  let G : MvPolynomial (Segment k) ℤ →+ R k :=
    toR.toAddMonoidHom.comp ((Finsupp.linearCombination ℤ f).toAddMonoidHom.comp ((Finsupp.domCongr (M := ℤ) e).toAddMonoidHom.comp
      (AddMonoidAlgebra.coeffAddEquiv (R := ℤ) (M := Segment k →₀ ℕ)).toAddMonoidHom))
  have hGbij : Function.Bijective G := toR.bijective.comp (hbij.comp ((Finsupp.domCongr e).bijective.comp
    (AddMonoidAlgebra.coeffAddEquiv (R := ℤ) (M := Segment k →₀ ℕ)).bijective))
  have hprod : ∀ (h N : ℕ) (Γ : Fin h → Segment k) (hd : ∑ a, (Lseg (Γ a)).1 = N),
      phiOf Lseg (∏ a, MvPolynomial.X (Γ a)) = toR (cl0 (prodIrr (fun a => Lseg (Γ a)) hd)) := by
    intro h N Γ hd
    rw [map_prod, PhiLAux.ring_class_product_irreducible hPL]
    exact Finset.prod_congr rfl fun a _ => phiOf_X _ _
  have hmono : ∀ s : Segment k →₀ ℕ, toR (f (e s)) = s.prod fun n m => toR (sg (Lseg n)) ^ m := by
    intro s
    show toR (cl0 _) = _
    rw [PhiLAux.ring_class_product_irreducible hPL, Finset.prod_eq_multiset_prod,
      ← PhiLAux.prod_map_toMultiset (fun n => toR (sg (Lseg n)))]
    have h1 : Finsupp.toMultiset s = Finset.univ.val.map (Δo (e s)) := (he s).symm.trans (hΔo (e s)).1.symm
    rw [h1, Multiset.map_map]
    rfl
  have hG : ∀ p, phiOf Lseg p = G p := by
    intro p
    refine MvPolynomial.induction_on' p (fun s a => ?_) (fun p q hp hq => ?_)
    · have h1 : G (MvPolynomial.monomial s a) = a • toR (f (e s)) := by
        show toR (Finsupp.linearCombination ℤ f (Finsupp.domCongr e (Finsupp.single s a))) = _
        rw [Finsupp.domCongr_apply, Finsupp.equivMapDomain_single, Finsupp.linearCombination_single, map_zsmul]
      rw [h1, hmono, phiOf, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial, eq_intCast, ← zsmul_eq_mul]
    · rw [map_add, map_add, hp, hq]
  have hphiG : ⇑(phiOf Lseg) = ⇑G := funext hG
  refine ⟨Lseg, hLseg, hphiG ▸ hGbij, fun 𝔫 x hx => ?_, hprod⟩
  obtain ⟨a, ha, hLa⟩ := hinv 𝔫
  have hxL : x = Lm 𝔫 := PhiLAux.isL_cls_unique c.free hx (hLm 𝔫)
  let cE := AddMonoidAlgebra.coeffAddEquiv (R := ℤ) (M := Segment k →₀ ℕ)
  refine ⟨cE.symm ((Finsupp.domCongr e).symm a), ?_, fun s hs => ?_⟩
  · rw [hG]
    show toR (Finsupp.linearCombination ℤ f (Finsupp.domCongr e (cE (cE.symm ((Finsupp.domCongr e).symm a))))) = _
    rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, hLa, hxL]
    rfl
  · rw [MvPolynomial.mem_support_iff] at hs
    have key : a (e s) = ((Finsupp.domCongr e).symm a : (Segment k →₀ ℕ) →₀ ℤ) s := by
      conv_lhs => rw [← AddEquiv.apply_symm_apply (Finsupp.domCongr e) a]
      rw [Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply]
    rw [← he s]
    exact ha _ (Finsupp.mem_support_iff.2 (by rw [key]; exact hs))

end CompanionTheory.Groth

end
