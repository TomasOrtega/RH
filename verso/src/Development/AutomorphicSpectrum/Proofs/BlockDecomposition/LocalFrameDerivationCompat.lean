import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BasicOpenRsLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordNear
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal

section CoefIdeal
variable {X : Scheme.{0}} {V V' : X.Opens} (h : V ≤ V') {d m : ℕ}
  (D : Fin d → Γ(X, V) → Γ(X, V)) (κ : Fin m → Fin d)

/- English proof (translation)
Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨b', bs, rfl⟩` from `hy`. Use `AddSubgroup.subset_closure ⟨b * b', bs, ?_⟩` and prove the remaining obligations. Simplify using `only [RingHom.id_apply, map_mul, mul_assoc]`.

Consider the case `zero => rw [mul_zero]`. Conclude with `zero_mem _`. Consider the case `add _ _ _ _ h1 h2 => rw [mul_add]`. Conclude with `add_mem h1 h2`. Consider the case `neg _ _ h1 => rw [mul_neg]`.

Conclude with `neg_mem h1`.
-/
theorem rs_mul_mem_jacSpan (b : Γ(X, V')) {y : Γ(X, V)} (hy : y ∈ jacSpan h (RingHom.id _) D κ) :
    rs h b * y ∈ jacSpan h (RingHom.id _) D κ := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b', bs, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨b * b', bs, ?_⟩
    simp only [RingHom.id_apply, map_mul, mul_assoc]
  | zero => rw [mul_zero]; exact zero_mem _
  | add _ _ _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
  | neg _ _ h1 => rw [mul_neg]; exact neg_mem h1

def coefIdeal (y : Γ(X, V)) : Ideal Γ(X, V') where
  carrier := {a | rs h a * y ∈ jacSpan h (RingHom.id _) D κ}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_add, add_mul]
    exact add_mem ha hb
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    rw [map_zero, zero_mul]
    exact zero_mem _
  smul_mem' b a ha := by
    simp only [Set.mem_setOf_eq, smul_eq_mul] at ha ⊢
    rw [map_mul, mul_assoc]
    exact rs_mul_mem_jacSpan h D κ b ha

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_coefIdeal {y : Γ(X, V)} {a : Γ(X, V')} :
    a ∈ coefIdeal h D κ y ↔ rs h a * y ∈ jacSpan h (RingHom.id _) D κ := Iff.rfl

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨P, hP, hle⟩` from `Ideal.exists_le_maximal 𝔠 hne`. Establish `hPp : P.IsPrime` using `hP.isPrime`. Set `p : PrimeSpectrum Γ(X, U)` to `⟨P, hPp⟩`. Establish `hxU : hU.fromSpec p ∈ U`.

Establish `: hU.fromSpec p ∈ Set.range hU.fromSpec` using `⟨p, rfl⟩`. Rewrite `this` using `[hU.range_fromSpec]`. Then use the resulting hypothesis. Take `⟨f, M, hx, hf⟩` from `H _ hxU`. Establish `hfP : f ∈ P` using `hPp.mem_of_pow_mem M (hle hf)`. Establish `e : hU.fromSpec p ∈ X.basicOpen f` using `hx`.

Establish `e2 : p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f` using `e`. Rewrite `e2` using `[hU.fromSpec_preimage_basicOpen]`. Conclude with `e2 hfP`.
-/
theorem ideal_eq_top_of_local {U : X.Opens} (hU : IsAffineOpen U) (𝔠 : Ideal Γ(X, U))
    (H : ∀ x : X, x ∈ U → ∃ (f : Γ(X, U)) (M : ℕ), x ∈ X.basicOpen f ∧ f ^ M ∈ 𝔠) : 𝔠 = ⊤ := by
  by_contra hne
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal 𝔠 hne
  have hPp : P.IsPrime := hP.isPrime
  let p : PrimeSpectrum Γ(X, U) := ⟨P, hPp⟩
  have hxU : hU.fromSpec p ∈ U := by
    have : hU.fromSpec p ∈ Set.range hU.fromSpec := ⟨p, rfl⟩
    rwa [hU.range_fromSpec] at this
  obtain ⟨f, M, hx, hf⟩ := H _ hxU
  have hfP : f ∈ P := hPp.mem_of_pow_mem M (hle hf)
  have e : hU.fromSpec p ∈ X.basicOpen f := hx
  have e2 : p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f := e
  rw [hU.fromSpec_preimage_basicOpen] at e2
  exact e2 hfP

end CoefIdeal

/- English proof (translation)
Introduce `K _ _ X q _ s V V' hVV hV' d c`. Introduce `D hD E ε hL σ m r hr hs ξ y hRep I`. Establish `top : coefIdeal hVV (fun k => D k) I.1 (y I) = ⊤`. Use `ideal_eq_top_of_local hV' _ fun x hx => ?_` and prove the remaining obligations. Take `⟨f, e, cu, hxf⟩` from `GlobalTheory.CompanionTheory.ConeLocal.coord_near q hV' x hx`.

Take `⟨M, hM⟩` from `GlobalTheory.CompanionTheory.ConeLocal.CoefMemLoc.main q s hVV hV' c D hD E ε hL σ m r hr hs f e cu ξ y hRep I`. Conclude with `⟨f, M, hxf, hM⟩`. Establish `h1 : (1 : Γ(X, V')) ∈ coefIdeal hVV (fun k => D k) I.1 (y I)` using `top ▸ Submodule.mem_top`. Establish `h2` using `(mem_coefIdeal hVV _ _).1 h1`. Rewrite `h2` using `[map_one, one_mul]`. Then use the resulting hypothesis.
-/
theorem coef_mem_jacSpan : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] (s : ℕ) {V V' : X.Opens} (hVV : V ≤ V'), IsAffineOpen V' → ∀ {d : ℕ} (c : Coord q V d),
    letI := (strV q V).toAlgebra
    ∀ (D : Fin d → Derivation K Γ(X, V) Γ(X, V)), (∀ k j, D k (c.t j) = if k = j then 1 else 0) →
    ∀ (E : Frame (sP (KS q s {V})) d) (ε : Γ(X, V) ≃+* (sP (KS q s {V})).A.obj E.D), IsLoc q s c.t E ε →
    ∀ (σ : ∀ T, E.D ⟶ T) (m : ℕ) (r : ℤ), r = m → m + 1 ≤ s → ∀ (ξ : HQ (KS q s {V'}) r (r + 1) m) (y : Idx m d → Γ(X, V)),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {V}) r) (sFil (KS q s {V}) (r + 1)) (fun u => ∑ I : Idx m d, E.form σ I.1 (ε (y I)) u) (resKS q s hVV _ _ _ ξ) →
      ∀ I, y I ∈ jacSpan hVV (RingHom.id _) (fun k => D k) I.1 := by
  intro K _ _ X q _ s V V' hVV hV' d c
  intro D hD E ε hL σ m r hr hs ξ y hRep I
  have top : coefIdeal hVV (fun k => D k) I.1 (y I) = ⊤ := by
    refine ideal_eq_top_of_local hV' _ fun x hx => ?_
    obtain ⟨f, e, cu, hxf⟩ := GlobalTheory.CompanionTheory.ConeLocal.coord_near q hV' x hx
    obtain ⟨M, hM⟩ := GlobalTheory.CompanionTheory.ConeLocal.CoefMemLoc.main q s hVV hV' c D hD E ε hL σ m r hr hs f e cu ξ y hRep I
    exact ⟨f, M, hxf, hM⟩
  have h1 : (1 : Γ(X, V')) ∈ coefIdeal hVV (fun k => D k) I.1 (y I) := top ▸ Submodule.mem_top
  have h2 := (mem_coefIdeal hVV _ _).1 h1
  rwa [map_one, one_mul] at h2

end GlobalTheory.CompanionTheory.ConeLocal
