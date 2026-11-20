import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatioInvariantInK0
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvFilD
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.Per.PerMat

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. It suffices to establish `H : ∀ n : ℕ, ∀ c : ι → B, (Finset.univ.filter (fun i => c i ≠ 0)).card ≤ n → ∑ i, c i • v i = 0 → c = 0 by`. Introduce `c hc i`. Conclude with `congrFun (H _ c le_rfl hc) i`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero`. Introduce `c hcard _`. Use function extensionality and compare the values at `i`. Assume the negation of the conclusion as `h`.

Simplify using `only [Pi.zero_apply] at h`. Establish `hi : i ∈ Finset.univ.filter (fun i => c i ≠ 0)` using `by simp [h]`. Rewrite `hcard` using `[Nat.le_zero, Finset.card_eq_zero]`. Simplify using `[hcard] at hi`. Consider the case `succ n ih`.

Introduce `c hcard hc`. Assume the negation of the conclusion as `hne`. Choose the witnesses or unpack the hypotheses as in `⟨i0, hi0⟩ : ∃ i0, c i0 ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Conclude with `hne (funext h)`. Establish `hσ : ∀ g, ∑ i, σ g (c i) • v i = 0`. Introduce `g`. Establish `e1 : (fun r => σ g ((∑ i, c i • v i) r)) = ∑ i, σ g (c i) • (fun r => σ g (v i r))`. Use function extensionality and compare the values at `r`.

Simplify using `[Finset.sum_apply, map_sum, map_mul]`. Establish `h1 : (M g).mulVec (fun r => σ g ((∑ i, c i • v i) r)) = ∑ i, σ g (c i) • v i`. Rewrite using `[e1, Matrix.mulVec_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_smul, hv]`.

Rewrite using `[← h1, hc]`. Simplify using `only [Pi.zero_apply, map_zero]`. Conclude with `Matrix.mulVec_zero (M g)`. Establish `hrel : ∀ g i, σ g (c i) * c i0 = c i * σ g (c i0)`. Introduce `g`.

Establish `key` using `ih (fun i => c i0 * σ g (c i) - σ g (c i0) * c i) ?_ ?_`. Introduce `i`. Use `congrFun key i` as an intermediate fact. Simplify using `only [Pi.zero_apply] at this`. Take the linear combination `this`.

Establish `hsub : Finset.univ.filter (fun i => c i0 * σ g (c i) - σ g (c i0) * c i ≠ 0) ⊆ (Finset.univ.filter (fun i => c i ≠ 0)).erase i0`. Introduce `i hi`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hi ⊢`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`.

Apply `hi` to reduce the goal to its premises. Expand and normalize the polynomial expressions, which then agree. Introduce `h0`. Apply `hi` to reduce the goal to its premises. Rewrite using `[h0]`.

Simplify using the standard rewrite rules. Establish `h2` using `Finset.card_le_card hsub`. Rewrite `h2` using `[Finset.card_erase_of_mem (by simp [hi0])]`. Use linear arithmetic over natural numbers and integers. Establish `e : ∑ i, (c i0 * σ g (c i) - σ g (c i0) * c i) • v i = c i0 • ∑ i, σ g (c i) • v i - σ g (c i0) • ∑ i, c i • v i`.

Simplify using `only [sub_smul, Finset.sum_sub_distrib, Finset.smul_sum, mul_smul]`. Rewrite using `[e, hσ g, hc, smul_zero, smul_zero, sub_zero]`. Use `choose k hk using fun i => hfrac (c i) (c i0) hi0 (fun g => hrel g i)`. Establish `hk0 : ∑ i, κ (k i) • v i = 0`. Establish `h3 : c i0 • ∑ i, κ (k i) • v i = 0`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, hk i, mul_comm]`. Use `_ = 0 := hc`.

Conclude with `(smul_eq_zero.1 h3).resolve_left hi0`. Establish `h4` using `congrFun (hind k hk0) i0`. Establish `h1` using `hk i0`. Rewrite `h1` using `[h4, Pi.zero_apply, map_zero, zero_mul]`. Conclude with `hi0 h1`.
-/
theorem li_of_frac {B : Type} [CommRing B] [IsDomain B] {d : ℕ} {ι G F : Type} [Fintype ι] [Field F]
    (κ : F →+* B) (σ : G → B →+* B) (M : G → Matrix (Fin d) (Fin d) B) (v : ι → Fin d → B)
    (hv : ∀ i g, (M g).mulVec (fun r => σ g (v i r)) = v i)
    (hfrac : ∀ a b : B, b ≠ 0 → (∀ g, σ g a * b = a * σ g b) → ∃ k : F, a = κ k * b)
    (hind : ∀ k : ι → F, ∑ i, κ (k i) • v i = 0 → k = 0) :
    LinearIndependent B v := by
  classical
  rw [Fintype.linearIndependent_iff]
  suffices H : ∀ n : ℕ, ∀ c : ι → B, (Finset.univ.filter (fun i => c i ≠ 0)).card ≤ n →
      ∑ i, c i • v i = 0 → c = 0 by
    intro c hc i; exact congrFun (H _ c le_rfl hc) i
  intro n
  induction n with
  | zero =>
    intro c hcard _
    funext i
    by_contra h
    simp only [Pi.zero_apply] at h
    have hi : i ∈ Finset.univ.filter (fun i => c i ≠ 0) := by simp [h]
    rw [Nat.le_zero, Finset.card_eq_zero] at hcard
    simp [hcard] at hi
  | succ n ih =>
    intro c hcard hc
    by_contra hne
    obtain ⟨i0, hi0⟩ : ∃ i0, c i0 ≠ 0 := by
      by_contra h; push_neg at h; exact hne (funext h)
    have hσ : ∀ g, ∑ i, σ g (c i) • v i = 0 := by
      intro g
      have e1 : (fun r => σ g ((∑ i, c i • v i) r)) = ∑ i, σ g (c i) • (fun r => σ g (v i r)) := by
        funext r; simp [Finset.sum_apply, map_sum, map_mul]
      have h1 : (M g).mulVec (fun r => σ g ((∑ i, c i • v i) r)) = ∑ i, σ g (c i) • v i := by
        rw [e1, Matrix.mulVec_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.mulVec_smul, hv]
      rw [← h1, hc]
      simp only [Pi.zero_apply, map_zero]
      exact Matrix.mulVec_zero (M g)
    have hrel : ∀ g i, σ g (c i) * c i0 = c i * σ g (c i0) := by
      intro g
      have key := ih (fun i => c i0 * σ g (c i) - σ g (c i0) * c i) ?_ ?_
      · intro i
        have := congrFun key i
        simp only [Pi.zero_apply] at this
        linear_combination this
      · have hsub : Finset.univ.filter (fun i => c i0 * σ g (c i) - σ g (c i0) * c i ≠ 0) ⊆
            (Finset.univ.filter (fun i => c i ≠ 0)).erase i0 := by
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hi ⊢
          refine ⟨?_, ?_⟩
          · rintro rfl; apply hi; ring
          · intro h0; apply hi; rw [h0]; simp
        have h2 := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem (by simp [hi0])] at h2
        omega
      · have e : ∑ i, (c i0 * σ g (c i) - σ g (c i0) * c i) • v i =
            c i0 • ∑ i, σ g (c i) • v i - σ g (c i0) • ∑ i, c i • v i := by
          simp only [sub_smul, Finset.sum_sub_distrib, Finset.smul_sum, mul_smul]
        rw [e, hσ g, hc, smul_zero, smul_zero, sub_zero]
    choose k hk using fun i => hfrac (c i) (c i0) hi0 (fun g => hrel g i)
    have hk0 : ∑ i, κ (k i) • v i = 0 := by
      have h3 : c i0 • ∑ i, κ (k i) • v i = 0 := by
        calc c i0 • ∑ i, κ (k i) • v i = ∑ i, c i • v i := by
              rw [Finset.smul_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [smul_smul, hk i, mul_comm]
          _ = 0 := hc
      exact (smul_eq_zero.1 h3).resolve_left hi0
    have h4 := congrFun (hind k hk0) i0
    have h1 := hk i0
    rw [h4, Pi.zero_apply, map_zero, zero_mul] at h1
    exact hi0 h1

end GlobalTheory.Per.PerMat

namespace GlobalTheory.Per.PerMat

/- English proof (translation)
Introduce `l _ K P AI T d ρ hspan`. Take `⟨-, hdom, -⟩` from `GlobalTheory.Per.TiedField.tied_field l P AI T`. Use `haveI : IsDomain (Per.Bcris l) := Function.Injective.isDomain (T.eB.symm : Per.Bcris l →+* P.R.B) T.eB.symm.injective`. Use `choose m c v hv hsum using hspan`. Set `κ : ↥(K0 K) →+* Per.Bcris l` to `T.eB.toRingHom.comp (algebraMap ↥(K0 K) P.R.B)`.

Use `letI : Algebra ↥(K0 K) (Per.Bcris l) := κ.toAlgebra`. Set `S : Set (Fin d → Per.Bcris l)` to `Set.range (fun q : (Σ j, Fin (m j)) => v q.1 q.2)`. Take `⟨b, hbS, hspanb, hli⟩` from `exists_linearIndependent (↥(K0 K)) S`. Establish `hfin : b.Finite` using `(Set.finite_range _).subset hbS`. Use `haveI : Fintype b := hfin.fintype`.

Establish `hvb : ∀ (x : b) (g : ↥(GK K)), ((ρ g).map (Per.zB l)).mulVec (fun r => Per.σB (g : GQ l) ((x : Fin d → Per.Bcris l) r)) = x`. Introduce and unpack `⟨x, hx⟩ g`. Take `⟨⟨j, i⟩, rfl⟩` from `hbS hx`. Conclude with `hv j i g`. Establish `hliB : LinearIndependent (Per.Bcris l) (Subtype.val : b → Fin d → Per.Bcris l)`.

Use `li_of_frac κ (fun g : ↥(GK K) => Per.σB (g : GQ l)) (fun g => (ρ g).map (Per.zB l)) _ hvb ?_ ?_` and prove the remaining obligations. Introduce `a a' ha' h`. Take `⟨k, hk⟩` from `GlobalTheory.Per.FracInv.tied_frac_invariant l P AI T K (T.eB.symm a) (T.eB.symm a') (by simpa using ha') (fun g hg => by`. Apply `T.eB.injective` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, T.actB, T.actB]`.

Simplify using `using h ⟨g, hg⟩)`. Use `⟨k, ?_⟩` and prove the remaining obligations. Use `congrArg T.eB hk` as an intermediate fact. Simplify `this` using `[κ]`. Introduce `k hk`.

Rewrite `hli` using `[Fintype.linearIndependent_iff]`. Use function extensionality and compare the values at `x`. Use `hli k ?_ x` and prove the remaining obligations. Rewrite using `[← hk]`. Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations.

Rewrite using `[← algebraMap_smul (Per.Bcris l) (k y) (y : Fin d → Per.Bcris l)]`. Both sides reduce to the same expression. Establish `hsp : ⊤ ≤ Submodule.span (Per.Bcris l) (Set.range (Subtype.val : b → Fin d → Per.Bcris l))`. Rewrite using `[Subtype.range_coe, ← (Pi.basisFun (Per.Bcris l) (Fin d)).span_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`.

Rewrite using `[Pi.basisFun_apply, hsum j]`. Use `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Establish `h1 : v j i ∈ Submodule.span (↥(K0 K)) b`. Rewrite using `[hspanb]`. Conclude with `Submodule.subset_span ⟨⟨j, i⟩, rfl⟩`.

Conclude with `Submodule.span_le_restrictScalars (↥(K0 K)) (Per.Bcris l) b h1`. Set `bb` to `Module.Basis.mk hliB hsp`. Establish `hcard : Fintype.card b = d`. Rewrite using `[← Module.finrank_eq_card_basis bb, Module.finrank_fin_fun]`. Set `e : b ≃ Fin d` to `Fintype.equivFinOfCardEq hcard`.

Set `bd` to `bb.reindex e`. Use `⟨(Pi.basisFun (Per.Bcris l) (Fin d)).toMatrix bd, bd.toMatrix (Pi.basisFun (Per.Bcris l) (Fin d)), Module.Basis.toMatrix_mul_toMatrix_flip _ _, fun g => ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Establish `hx` using `congrFun (hvb (e.symm j) g) i`. Simplify `hx` using `[Matrix.mul_apply, Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply, bd, bb]`.
-/
theorem exists_invertible_invariant : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])), (∀ j : Fin d, ∃ (m : ℕ) (c : Fin m → Per.Bcris l) (v : Fin m → Fin d → Per.Bcris l), (∀ i (g : ↥(GK K)), ((ρ g).map (Per.zB l)).mulVec (fun r => Per.σB (g : GQ l) (v i r)) = v i) ∧ (Pi.single j 1 : Fin d → Per.Bcris l) = ∑ i, c i • v i) → ∃ U U' : Matrix (Fin d) (Fin d) (Per.Bcris l), U * U' = 1 ∧ (∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U) := by
  intro l _ K P AI T d ρ hspan
  classical
  obtain ⟨-, hdom, -⟩ := GlobalTheory.Per.TiedField.tied_field l P AI T
  haveI : IsDomain (Per.Bcris l) :=
    Function.Injective.isDomain (T.eB.symm : Per.Bcris l →+* P.R.B) T.eB.symm.injective
  choose m c v hv hsum using hspan
  let κ : ↥(K0 K) →+* Per.Bcris l := T.eB.toRingHom.comp (algebraMap ↥(K0 K) P.R.B)
  letI : Algebra ↥(K0 K) (Per.Bcris l) := κ.toAlgebra
  let S : Set (Fin d → Per.Bcris l) := Set.range (fun q : (Σ j, Fin (m j)) => v q.1 q.2)
  obtain ⟨b, hbS, hspanb, hli⟩ := exists_linearIndependent (↥(K0 K)) S
  have hfin : b.Finite := (Set.finite_range _).subset hbS
  haveI : Fintype b := hfin.fintype
  have hvb : ∀ (x : b) (g : ↥(GK K)), ((ρ g).map (Per.zB l)).mulVec (fun r => Per.σB (g : GQ l) ((x : Fin d → Per.Bcris l) r)) = x := by
    rintro ⟨x, hx⟩ g
    obtain ⟨⟨j, i⟩, rfl⟩ := hbS hx
    exact hv j i g
  have hliB : LinearIndependent (Per.Bcris l) (Subtype.val : b → Fin d → Per.Bcris l) := by
    refine li_of_frac κ (fun g : ↥(GK K) => Per.σB (g : GQ l)) (fun g => (ρ g).map (Per.zB l)) _ hvb ?_ ?_
    · intro a a' ha' h
      obtain ⟨k, hk⟩ := GlobalTheory.Per.FracInv.tied_frac_invariant l P AI T K (T.eB.symm a) (T.eB.symm a')
        (by simpa using ha') (fun g hg => by
          apply T.eB.injective
          rw [map_mul, map_mul, T.actB, T.actB]
          simpa using h ⟨g, hg⟩)
      refine ⟨k, ?_⟩
      have := congrArg T.eB hk
      simpa [κ] using this
    · intro k hk
      rw [Fintype.linearIndependent_iff] at hli
      funext x
      refine hli k ?_ x
      rw [← hk]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [← algebraMap_smul (Per.Bcris l) (k y) (y : Fin d → Per.Bcris l)]
      rfl
  have hsp : ⊤ ≤ Submodule.span (Per.Bcris l) (Set.range (Subtype.val : b → Fin d → Per.Bcris l)) := by
    rw [Subtype.range_coe, ← (Pi.basisFun (Per.Bcris l) (Fin d)).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [Pi.basisFun_apply, hsum j]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    have h1 : v j i ∈ Submodule.span (↥(K0 K)) b := by
      rw [hspanb]; exact Submodule.subset_span ⟨⟨j, i⟩, rfl⟩
    exact Submodule.span_le_restrictScalars (↥(K0 K)) (Per.Bcris l) b h1
  let bb := Module.Basis.mk hliB hsp
  have hcard : Fintype.card b = d := by
    rw [← Module.finrank_eq_card_basis bb, Module.finrank_fin_fun]
  let e : b ≃ Fin d := Fintype.equivFinOfCardEq hcard
  let bd := bb.reindex e
  refine ⟨(Pi.basisFun (Per.Bcris l) (Fin d)).toMatrix bd, bd.toMatrix (Pi.basisFun (Per.Bcris l) (Fin d)),
    Module.Basis.toMatrix_mul_toMatrix_flip _ _, fun g => ?_⟩
  ext i j
  have hx := congrFun (hvb (e.symm j) g) i
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply, bd, bb] using hx

end GlobalTheory.Per.PerMat
