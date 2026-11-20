import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal

/- English proof (translation)
Set `f : MvPolynomial (Fin d) K →+* A` to `MvPolynomial.eval₂Hom (algebraMap K A) t`. Set `π : B →+* B ⧸ P` to `Ideal.Quotient.mk P`. Set `e : Fin d → B` to `fun k => a (t k) - b (t k)`. Establish `he : ∀ k, e k ∈ N` using `fun k => hab _`. Set `S : A → B` to `fun x => ∑ k, e k * b (D k x)`.

Establish `hS : ∀ x, S x ∈ N` using `fun x => Ideal.sum_mem _ fun k _ => N.mul_mem_right _ (he k)`. Establish `hSadd : ∀ x y, S (x + y) = S x + S y` using `fun x y => by`. Simplify using `only [S, map_add, mul_add, Finset.sum_add_distrib]`. Establish `hSmul : ∀ x y, S (x * y) = b x * S y + b y * S x` using `fun x y => by`. Simplify using `only [S, Derivation.leibniz, smul_eq_mul, map_add, map_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]`.

Apply the tactic sequence `congr 1 <;> exact Finset.sum_congr rfl fun k _ => by ring`. Establish `hSone : S 1 = 0` using `by simp [S]`. Establish `hSzero : S 0 = 0` using `by simp [S]`. Set `c : A →+* B ⧸ P` to `{ toFun := fun x => π (b x + S x) map_one' := by simp [hSone] map_zero' := by simp [hSzero] map_add' := fun x y => by`. Rewrite using `[hSadd, map_add b, ← map_add π]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use the proof step `map_mul' := fun x y => by`. Rewrite using `[← map_mul π]`. Use `Ideal.Quotient.eq.2 ?_` and prove the remaining obligations.

Establish `h` using `hNP (Ideal.mul_mem_mul (hS x) (hS y))`. Establish `e2 : b (x * y) + S (x * y) - (b x + S x) * (b y + S y) = -(S x * S y)`. Rewrite using `[hSmul, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2]`.

Conclude with `P.neg_mem h }`. Establish `hc : ∀ x, c x = π (b x + S x)` using `fun _ => rfl`. Establish `hcf : c.comp f = π.comp ((a : A →+* B).comp f)`. Use `MvPolynomial.ringHom_ext (fun r => ?_) fun i => ?_` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply, f, MvPolynomial.eval₂Hom_C, hc]`.

Establish `: S (algebraMap K A r) = 0` using `by simp [S]`. Simplify using `[this]`. Simplify using `only [RingHom.comp_apply, f, MvPolynomial.eval₂Hom_X', hc]`. Establish `: S (t i) = e i` using `by simp [S, hD, e]`. Rewrite using `[this]`.

Simplify using `[e]`. Use `letI algA : Algebra (MvPolynomial (Fin d) K) A := f.toAlgebra`. Use `letI algC : Algebra (MvPolynomial (Fin d) K) (B ⧸ P) := (π.comp ((a : A →+* B).comp f)).toAlgebra`. Use `haveI : Algebra.FormallyUnramified (MvPolynomial (Fin d) K) A := hf`. Set `g₁ : A →ₐ[MvPolynomial (Fin d) K] B ⧸ P` to `{ toRingHom := π.comp (a : A →+* B), commutes' := fun _ => rfl }`.

Set `g₂ : A →ₐ[MvPolynomial (Fin d) K] B ⧸ P` to `{ toRingHom := c, commutes' := fun p => RingHom.congr_fun hcf p }`. Establish `hnil : IsNilpotent (N.map π)`. Use `⟨2, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_two, ← Ideal.map_mul, Ideal.zero_eq_bot]`. Use `le_bot_iff.1 ((Ideal.map_mono hNP).trans ?_)` and prove the remaining obligations.

Rewrite using `[Ideal.map_quotient_self]`. Establish `hg : g₁ = g₂`. Use `Algebra.FormallyUnramified.ext (N.map π) hnil fun y => ?_` and prove the remaining obligations. Use `Ideal.Quotient.eq.2 ?_` and prove the remaining obligations. Establish `: g₁ y - g₂ y = π (a y - (b y + S y))`.

Rewrite using `[map_sub]`. Both sides reduce to the same expression. Rewrite using `[this]`. Use `Ideal.mem_map_of_mem π ?_` and prove the remaining obligations. Establish `e3 : a y - (b y + S y) = (a y - b y) - S y` using `by ring`.

Rewrite using `[e3]`. Conclude with `N.sub_mem (hab y) (hS y)`. Establish `h1 : π (a x) = π (b x + S x)` using `DFunLike.congr_fun hg x`. Establish `h2` using `Ideal.Quotient.eq.1 h1`. Establish `e4 : a x - (b x + S x) = a x - b x - ∑ k, (a (t k) - b (t k)) * b (D k x)`.

Simplify using `only [S, e]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h2` using `[e4]`. Then use the resulting hypothesis.
-/
theorem taylor_alg {K A B : Type} [CommRing K] [CommRing A] [Algebra K A] [CommRing B] [Algebra K B] {d : ℕ}
    (t : Fin d → A)
    (hf : (MvPolynomial.eval₂Hom (algebraMap K A) t : MvPolynomial (Fin d) K →+* A).FormallyUnramified)
    (D : Fin d → Derivation K A A) (hD : ∀ k j, D k (t j) = if k = j then 1 else 0)
    (N P : Ideal B) (hNP : N * N ≤ P) (a b : A →ₐ[K] B) (hab : ∀ x, a x - b x ∈ N) (x : A) :
    a x - b x - ∑ k, (a (t k) - b (t k)) * b (D k x) ∈ P := by
  classical
  let f : MvPolynomial (Fin d) K →+* A := MvPolynomial.eval₂Hom (algebraMap K A) t
  let π : B →+* B ⧸ P := Ideal.Quotient.mk P
  let e : Fin d → B := fun k => a (t k) - b (t k)
  have he : ∀ k, e k ∈ N := fun k => hab _
  let S : A → B := fun x => ∑ k, e k * b (D k x)
  have hS : ∀ x, S x ∈ N := fun x => Ideal.sum_mem _ fun k _ => N.mul_mem_right _ (he k)
  have hSadd : ∀ x y, S (x + y) = S x + S y := fun x y => by
    simp only [S, map_add, mul_add, Finset.sum_add_distrib]
  have hSmul : ∀ x y, S (x * y) = b x * S y + b y * S x := fun x y => by
    simp only [S, Derivation.leibniz, smul_eq_mul, map_add, map_mul, mul_add, Finset.sum_add_distrib,
      Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun k _ => by ring
  have hSone : S 1 = 0 := by simp [S]
  have hSzero : S 0 = 0 := by simp [S]
  let c : A →+* B ⧸ P :=
    { toFun := fun x => π (b x + S x)
      map_one' := by simp [hSone]
      map_zero' := by simp [hSzero]
      map_add' := fun x y => by
        rw [hSadd, map_add b, ← map_add π]
        congr 1
        ring
      map_mul' := fun x y => by
        rw [← map_mul π]
        refine Ideal.Quotient.eq.2 ?_
        have h := hNP (Ideal.mul_mem_mul (hS x) (hS y))
        have e2 : b (x * y) + S (x * y) - (b x + S x) * (b y + S y) = -(S x * S y) := by
          rw [hSmul, map_mul]
          ring
        rw [e2]
        exact P.neg_mem h }
  have hc : ∀ x, c x = π (b x + S x) := fun _ => rfl
  have hcf : c.comp f = π.comp ((a : A →+* B).comp f) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) fun i => ?_
    · simp only [RingHom.comp_apply, f, MvPolynomial.eval₂Hom_C, hc]
      have : S (algebraMap K A r) = 0 := by simp [S]
      simp [this]
    · simp only [RingHom.comp_apply, f, MvPolynomial.eval₂Hom_X', hc]
      have : S (t i) = e i := by simp [S, hD, e]
      rw [this]
      simp [e]
  letI algA : Algebra (MvPolynomial (Fin d) K) A := f.toAlgebra
  letI algC : Algebra (MvPolynomial (Fin d) K) (B ⧸ P) := (π.comp ((a : A →+* B).comp f)).toAlgebra
  haveI : Algebra.FormallyUnramified (MvPolynomial (Fin d) K) A := hf
  let g₁ : A →ₐ[MvPolynomial (Fin d) K] B ⧸ P :=
    { toRingHom := π.comp (a : A →+* B), commutes' := fun _ => rfl }
  let g₂ : A →ₐ[MvPolynomial (Fin d) K] B ⧸ P :=
    { toRingHom := c, commutes' := fun p => RingHom.congr_fun hcf p }
  have hnil : IsNilpotent (N.map π) := by
    refine ⟨2, ?_⟩
    rw [pow_two, ← Ideal.map_mul, Ideal.zero_eq_bot]
    refine le_bot_iff.1 ((Ideal.map_mono hNP).trans ?_)
    rw [Ideal.map_quotient_self]
  have hg : g₁ = g₂ := by
    refine Algebra.FormallyUnramified.ext (N.map π) hnil fun y => ?_
    refine Ideal.Quotient.eq.2 ?_
    have : g₁ y - g₂ y = π (a y - (b y + S y)) := by
      rw [map_sub]
      rfl
    rw [this]
    refine Ideal.mem_map_of_mem π ?_
    have e3 : a y - (b y + S y) = (a y - b y) - S y := by ring
    rw [e3]
    exact N.sub_mem (hab y) (hS y)
  have h1 : π (a x) = π (b x + S x) := DFunLike.congr_fun hg x
  have h2 := Ideal.Quotient.eq.1 h1
  have e4 : a x - (b x + S x) = a x - b x - ∑ k, (a (t k) - b (t k)) * b (D k x) := by
    simp only [S, e]
    ring
  rwa [e4] at h2

/- English proof (translation)
Introduce `K _ _ X q W d c s E ε h`. Use `letI := (strV q W).toAlgebra`. Introduce `D hD`. Take `⟨-, -, h3, h4, h5⟩` from `h`. Introduce `T u v x`.

Take `⟨y, rfl⟩` from `ε.surjective x`. Establish `hF` using `GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {W})`. Establish `hcomm : ∀ (w : E.D ⟶ T) (r : K), ((sP (KS q s {W})).A.map w).hom (ε (algebraMap K Γ(X, W) r)) = algebraMap K ((sP (KS q s {W})).A.obj T) r` using `fun w r => by`. Establish `e : ε (algebraMap K Γ(X, W) r) = algebraMap K _ r` using `h3 r`. Rewrite using `[e]`.

Conclude with `AlgHom.commutes _ r`. Set `ev' : (E.D ⟶ T) → (Γ(X, W) →ₐ[K] (sP (KS q s {W})).A.obj T)` to `fun w => { toRingHom := RingHom.comp (AlgHom.toRingHom ((sP (KS q s {W})).A.map w).hom) ε.toRingHom commutes' := hcomm w }`. Establish `hNP : (sFil (KS q s {W}) 1).S T * (sFil (KS q s {W}) 1).S T ≤ (sFil (KS q s {W}) 2).S T` using `Ideal.mul_le.2 fun a ha b hb => hF.mul 1 1 T ha hb`. Establish `hab : ∀ g, ev' u g - ev' v g ∈ (sFil (KS q s {W}) 1).S T` using `fun g => by`. Rewrite using `[hF.one T]`.

Establish `e` using `(h4 T u g).symm.trans (h4 T v g)`. Conclude with `Ideal.Quotient.eq.1 e`. Establish `hf : (MvPolynomial.eval₂Hom (algebraMap K Γ(X, W)) c.t : MvPolynomial (Fin d) K →+* Γ(X, W)).FormallyUnramified`. Establish `he` using `c.etale`. Use `letI := (MvPolynomial.eval₂Hom (strV q W) c.t : MvPolynomial (Fin d) K →+* Γ(X, W)).toAlgebra`.

Use `haveI : Algebra.Etale (MvPolynomial (Fin d) K) Γ(X, W) := he`. Conclude with `(inferInstance : Algebra.FormallyUnramified (MvPolynomial (Fin d) K) Γ(X, W))`. Establish `key` using `taylor_alg c.t hf D hD _ _ hNP (ev' u) (ev' v) hab y`. Establish `e : ∀ k, E.τ k v u = ev' u (c.t k) - ev' v (c.t k)` using `fun k => h5 k v u`. Simplify using `only [ε.symm_apply_apply, e]`.

Conclude with `key`.
-/
theorem taylor_loc : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {W : X.Opens} {d : ℕ} (c : Coord q W d) (s : ℕ) (E : Frame (sP (KS q s {W})) d)
    (ε : Γ(X, W) ≃+* (sP (KS q s {W})).A.obj E.D), IsLoc q s c.t E ε →
    letI := (strV q W).toAlgebra
    ∀ (D : Fin d → Derivation K Γ(X, W) Γ(X, W)), (∀ k j, D k (c.t j) = if k = j then 1 else 0) →
    Taylor (sFil (KS q s {W})) E (fun k x => ε (D k (ε.symm x))) := by
  intro K _ _ X q W d c s E ε h
  letI := (strV q W).toAlgebra
  intro D hD
  obtain ⟨-, -, h3, h4, h5⟩ := h
  intro T u v x
  obtain ⟨y, rfl⟩ := ε.surjective x
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {W})
  have hcomm : ∀ (w : E.D ⟶ T) (r : K), ((sP (KS q s {W})).A.map w).hom (ε (algebraMap K Γ(X, W) r)) =
      algebraMap K ((sP (KS q s {W})).A.obj T) r := fun w r => by
    have e : ε (algebraMap K Γ(X, W) r) = algebraMap K _ r := h3 r
    rw [e]
    exact AlgHom.commutes _ r
  let ev' : (E.D ⟶ T) → (Γ(X, W) →ₐ[K] (sP (KS q s {W})).A.obj T) := fun w =>
    { toRingHom := RingHom.comp (AlgHom.toRingHom ((sP (KS q s {W})).A.map w).hom) ε.toRingHom
      commutes' := hcomm w }
  have hNP : (sFil (KS q s {W}) 1).S T * (sFil (KS q s {W}) 1).S T ≤ (sFil (KS q s {W}) 2).S T :=
    Ideal.mul_le.2 fun a ha b hb => hF.mul 1 1 T ha hb
  have hab : ∀ g, ev' u g - ev' v g ∈ (sFil (KS q s {W}) 1).S T := fun g => by
    rw [hF.one T]
    have e := (h4 T u g).symm.trans (h4 T v g)
    exact Ideal.Quotient.eq.1 e
  have hf : (MvPolynomial.eval₂Hom (algebraMap K Γ(X, W)) c.t : MvPolynomial (Fin d) K →+* Γ(X, W)).FormallyUnramified :=
    by
      have he := c.etale
      letI := (MvPolynomial.eval₂Hom (strV q W) c.t : MvPolynomial (Fin d) K →+* Γ(X, W)).toAlgebra
      haveI : Algebra.Etale (MvPolynomial (Fin d) K) Γ(X, W) := he
      exact (inferInstance : Algebra.FormallyUnramified (MvPolynomial (Fin d) K) Γ(X, W))
  have key := taylor_alg c.t hf D hD _ _ hNP (ev' u) (ev' v) hab y
  have e : ∀ k, E.τ k v u = ev' u (c.t k) - ev' v (c.t k) := fun k => h5 k v u
  simp only [ε.symm_apply_apply, e]
  exact key

end GlobalTheory.CompanionTheory.ConeLocal
