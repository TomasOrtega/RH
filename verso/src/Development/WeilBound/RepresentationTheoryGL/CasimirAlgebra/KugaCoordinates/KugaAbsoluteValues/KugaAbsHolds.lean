import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.KugaAbsoluteValues.KSumApply
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.KugaSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompInsertNthEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RemoveNthSuccVecCons
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KDKDelApply
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvarianceContraction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlternatingMapEqZeroOfSpan

noncomputable section

open Fin Function

namespace PositivityTheory.Rg.Cz

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.KAdjoint.kIp_kD`.
-/
theorem kIp_kD : ∀ {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] {β : Type} [Fintype β] (B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ) (b : β → P) (T T' : P →ₗ[ℝ] Module.End ℂ M), (∀ X x y, B (T X x) y = B x (T' X y)) → ∀ {m : ℕ} (η : P [⋀^Fin m]→ₗ[ℝ] M) (θ : P [⋀^Fin (m + 1)]→ₗ[ℝ] M), kIp B b (kD T η) θ = ((m : ℂ) + 1) * kIp B b η (kDel T' b θ) :=
  GlobalTheory.CompanionTheory.KAdjoint.kIp_kD

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.KDelFormula.kDel_kD`.
-/
theorem kDel_kD : ∀ {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] {β : Type} [Fintype β] (T T' : P →ₗ[ℝ] Module.End ℂ M) (b : β → P) {q : ℕ} (η : P [⋀^Fin q]→ₗ[ℝ] M) (Y : Fin q → P), kDel T' b (kD T η) Y = ∑ i, T' (b i) (T (b i) (η Y)) - ∑ t, ∑ i, T' (b i) (T (Y t) (η (Function.update Y t (b i)))) :=
  GlobalTheory.CompanionTheory.KDelFormula.kDel_kD

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.Kabs.kD_kDel_apply`.
-/
theorem kD_kDel : ∀ {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] {β : Type} [Fintype β] (T T' : P →ₗ[ℝ] Module.End ℂ M) (b : β → P) {n : ℕ} (θ : P [⋀^Fin (n + 1)]→ₗ[ℝ] M) (Y : Fin (n + 1) → P), kD T (kDel T' b θ) Y = ∑ s, ∑ i, T (Y s) (T' (b i) (θ (Function.update Y s (b i)))) :=
  GlobalTheory.CompanionTheory.Kabs.kD_kDel_apply

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.Invsum.invariance_contraction`.
-/
theorem kInv_sum : ∀ {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] {β γ : Type} [Fintype β] (b : β → P) (D : γ → P →ₗ[ℝ] P) (c : β → β → γ → ℝ) (E : γ → Module.End ℂ M), (∀ i j k, c j i k = -c i j k) → (∀ k j, D k (b j) = ∑ i, c i j k • b i) → ∀ {q : ℕ} (ω : P [⋀^Fin q]→ₗ[ℝ] M), (∀ k (Y : Fin q → P), E k (ω Y) = ∑ s, ω (Function.update Y s (D k (Y s)))) → ∀ (k : γ) (J : Fin q → β), ∑ s, ∑ i, (c (J s) i k : ℂ) • ω (Function.update (b ∘ J) s (b i)) = -E k (ω (b ∘ J)) :=
  GlobalTheory.CompanionTheory.Invsum.invariance_contraction

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.AltSpan.alternatingMap_eq_zero_of_span`.
-/
theorem kAlt_eq_zero : ∀ {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℝ M] {β : Type} (b : β → P), Submodule.span ℝ (Set.range b) = ⊤ → ∀ {m : ℕ} (f : P [⋀^Fin m]→ₗ[ℝ] M), (∀ I : Fin m → β, f (b ∘ I) = 0) → f = 0 :=
  GlobalTheory.CompanionTheory.AltSpan.alternatingMap_eq_zero_of_span

section
variable {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℂ M]
  [Module ℝ M] [IsScalarTower ℝ ℂ M]

/- English proof (translation)
Establish `hcomm : ∀ j i, (a + r) (b j) * (r - a) (b i) - (r - a) (b i) * (a + r) (b j) = ∑ k, (c j i k : ℂ) • (r' k - a' k)`. Introduce `j i`. Establish `e1` using `(har (b j) (b i)).eq`. Establish `e2` using `(har (b i) (b j)).eq`. Establish `h : (a + r) (b j) * (r - a) (b i) - (r - a) (b i) * (a + r) (b j) - ((r (b j) * r (b i) - r (b i) * r (b j)) - (a (b j) * a (b i) - a (b i) * a (b j))) = (a (b j) * r (b i) - r (b i) * a (b j)) - (r (b j) * a (b i) - a (b i) * r (b j))`.

Simplify using `only [LinearMap.add_apply, LinearMap.sub_apply]`. Use `noncomm_ring`. Rewrite `h` using `[e1, e2, sub_self, sub_self, sub_zero, sub_eq_zero]`. Rewrite using `[h, hcr, hca, ← Finset.sum_sub_distrib]`. Simplify using `only [smul_sub]`.

Establish `hsq : ∀ i, (r - a) (b i) * (a + r) (b i) = r (b i) * r (b i) - a (b i) * a (b i)`. Introduce `i`. Establish `e` using `(har (b i) (b i)).eq`. Simplify using `only [LinearMap.add_apply, LinearMap.sub_apply, mul_add, sub_mul, e]`. Normalize the expressions using the abelian group laws.

Establish `hsq' : ∀ k, (r' k - a' k) * (a' k + r' k) = r' k * r' k - a' k * a' k`. Introduce `k`. Establish `e` using `(ha'r' k).eq`. Simplify using `only [mul_add, sub_mul, e]`. Normalize the expressions using the abelian group laws.

Establish `hinv` using `kInv_sum b D c (fun k => a' k + r' k) hc hD ω hω`. Rewrite using `[kDel_kD]`. Generalize the expression as in `a + r = L at hcomm hsq ⊢`. Generalize the expression as in `r - a = L' at hcomm hsq ⊢`. Establish `step1 : ∑ i, L' (b i) (L (b i) (ω (b ∘ J))) - ∑ t, ∑ i, L' (b i) (L ((b ∘ J) t) (ω (Function.update (b ∘ J) t (b i)))) + ∑ s, ∑ i, L (b (J s)) (L' (b i) (ω (Function.update (b ∘ J) s (b i)))) = ∑ i, (L' (b i) * L (b i)) (ω (b ∘ J)) + ∑ s, ∑ i, (L (b (J s)) * L' (b i) - L' (b i) * …`.

Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, Finset.sum_sub_distrib, Function.comp_apply]`. Normalize the expressions using the abelian group laws. Rewrite using `[step1]`. Repeatedly rewrite using `[hsq, hcomm]`. Establish `step2 : ∀ s i, (∑ k, (c (J s) i k : ℂ) • (r' k - a' k)) (ω (Function.update (b ∘ J) s (b i))) = ∑ k, (r' k - a' k) ((c (J s) i k : ℂ) • ω (Function.update (b ∘ J) s (b i)))`.

Introduce `s i`. Rewrite using `[LinearMap.sum_apply]`. Simplify using `only [LinearMap.smul_apply, map_smul]`. Repeatedly rewrite using `[step2]`. Establish `step3 : ∑ s, ∑ i, ∑ k, (r' k - a' k) ((c (J s) i k : ℂ) • ω (Function.update (b ∘ J) s (b i))) = ∑ k, ∑ s, ∑ i, (r' k - a' k) ((c (J s) i k : ℂ) • ω (Function.update (b ∘ J) s (b i)))`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[step3]`. Repeatedly rewrite using `[← map_sum, hinv, map_neg, ← Module.End.mul_apply, hsq']`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply, Finset.sum_sub_distrib, Finset.sum_neg_distrib]`. Normalize the expressions using the abelian group laws.
-/
theorem kHom {β γ : Type} [Fintype β] [Fintype γ] (b : β → P) (a r : P →ₗ[ℝ] Module.End ℂ M)
    (a' r' : γ → Module.End ℂ M) (D : γ → P →ₗ[ℝ] P) (c : β → β → γ → ℝ)
    (har : ∀ X Y, Commute (a X) (r Y)) (ha'r' : ∀ k, Commute (a' k) (r' k))
    (hca : ∀ i j, a (b i) * a (b j) - a (b j) * a (b i) = ∑ k, (c i j k : ℂ) • a' k)
    (hcr : ∀ i j, r (b i) * r (b j) - r (b j) * r (b i) = ∑ k, (c i j k : ℂ) • r' k)
    (hc : ∀ i j k, c j i k = -c i j k) (hD : ∀ k j, D k (b j) = ∑ i, c i j k • b i)
    {q : ℕ} (ω : P [⋀^Fin q]→ₗ[ℝ] M)
    (hω : ∀ k (Y : Fin q → P), (a' k + r' k) (ω Y) = ∑ s, ω (Function.update Y s (D k (Y s))))
    (J : Fin q → β) :
    kDel (r - a) b (kD (a + r) ω) (b ∘ J) +
      ∑ s, ∑ i, (a + r) (b (J s)) ((r - a) (b i) (ω (Function.update (b ∘ J) s (b i)))) =
    ((∑ i, r (b i) * r (b i) - ∑ k, r' k * r' k) - (∑ i, a (b i) * a (b i) - ∑ k, a' k * a' k) :
      Module.End ℂ M) (ω (b ∘ J)) := by
  have hcomm : ∀ j i, (a + r) (b j) * (r - a) (b i) - (r - a) (b i) * (a + r) (b j) =
      ∑ k, (c j i k : ℂ) • (r' k - a' k) := by
    intro j i
    have e1 := (har (b j) (b i)).eq
    have e2 := (har (b i) (b j)).eq
    have h : (a + r) (b j) * (r - a) (b i) - (r - a) (b i) * (a + r) (b j) -
        ((r (b j) * r (b i) - r (b i) * r (b j)) - (a (b j) * a (b i) - a (b i) * a (b j))) =
        (a (b j) * r (b i) - r (b i) * a (b j)) - (r (b j) * a (b i) - a (b i) * r (b j)) := by
      simp only [LinearMap.add_apply, LinearMap.sub_apply]
      noncomm_ring
    rw [e1, e2, sub_self, sub_self, sub_zero, sub_eq_zero] at h
    rw [h, hcr, hca, ← Finset.sum_sub_distrib]
    simp only [smul_sub]
  have hsq : ∀ i, (r - a) (b i) * (a + r) (b i) = r (b i) * r (b i) - a (b i) * a (b i) := by
    intro i
    have e := (har (b i) (b i)).eq
    simp only [LinearMap.add_apply, LinearMap.sub_apply, mul_add, sub_mul, e]
    abel
  have hsq' : ∀ k, (r' k - a' k) * (a' k + r' k) = r' k * r' k - a' k * a' k := by
    intro k
    have e := (ha'r' k).eq
    simp only [mul_add, sub_mul, e]
    abel
  have hinv := kInv_sum b D c (fun k => a' k + r' k) hc hD ω hω
  rw [kDel_kD]
  generalize a + r = L at hcomm hsq ⊢
  generalize r - a = L' at hcomm hsq ⊢
  have step1 : ∑ i, L' (b i) (L (b i) (ω (b ∘ J))) -
      ∑ t, ∑ i, L' (b i) (L ((b ∘ J) t) (ω (Function.update (b ∘ J) t (b i)))) +
      ∑ s, ∑ i, L (b (J s)) (L' (b i) (ω (Function.update (b ∘ J) s (b i)))) =
      ∑ i, (L' (b i) * L (b i)) (ω (b ∘ J)) +
      ∑ s, ∑ i, (L (b (J s)) * L' (b i) - L' (b i) * L (b (J s)))
        (ω (Function.update (b ∘ J) s (b i))) := by
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Finset.sum_sub_distrib, Function.comp_apply]
    abel
  rw [step1]
  simp_rw [hsq, hcomm]
  have step2 : ∀ s i, (∑ k, (c (J s) i k : ℂ) • (r' k - a' k)) (ω (Function.update (b ∘ J) s (b i))) =
      ∑ k, (r' k - a' k) ((c (J s) i k : ℂ) • ω (Function.update (b ∘ J) s (b i))) := by
    intro s i
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, map_smul]
  simp_rw [step2]
  have step3 : ∑ s, ∑ i, ∑ k, (r' k - a' k) ((c (J s) i k : ℂ) • ω (Function.update (b ∘ J) s (b i))) =
      ∑ k, ∑ s, ∑ i, (r' k - a' k) ((c (J s) i k : ℂ) • ω (Function.update (b ∘ J) s (b i))) := by
    calc _ = ∑ s, ∑ k, ∑ i, (r' k - a' k) ((c (J s) i k : ℂ) • ω (Function.update (b ∘ J) s (b i))) :=
          Finset.sum_congr rfl fun s _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [step3]
  simp_rw [← map_sum, hinv, map_neg, ← Module.End.mul_apply, hsq']
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  abel

omit [Module ℝ M] [IsScalarTower ℝ ℂ M] in
/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Simplify using `[hx]`. Conclude with `(hpos x hx).le`.
-/
theorem kB_re_nonneg (B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ) (hpos : ∀ x, x ≠ 0 → 0 < (B x x).re) (x : M) :
    0 ≤ (B x x).re := by
  by_cases hx : x = 0
  · simp [hx]
  · exact (hpos x hx).le

/- English proof (translation)
Consider the cases of `q with`. Consider the case `zero => simp`. Consider the case `succ n`. Establish `h1 : ∀ J : Fin (n + 1) → β, (∑ s, ∑ i, T (b (J s)) (T' (b i) (ω (Function.update (b ∘ J) s (b i))))) = kD T (kDel T' b ω) (b ∘ J)` using `fun J => (kD_kDel T T' b ω (b ∘ J)).symm`. Repeatedly rewrite using `[h1]`.

Establish `h2 : (∑ J : Fin (n + 1) → β, B (ω (b ∘ J)) (kD T (kDel T' b ω) (b ∘ J))) = starRingEnd ℂ (kIp B b (kD T (kDel T' b ω)) ω)`. Unfold `kIp`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun J _ => hB _ _`. Rewrite using `[h2, kIp_kD B b T T' hTT (kDel T' b ω) ω, Complex.conj_re, Complex.mul_re]`.

Establish `: (((n : ℂ) + 1)).im = 0` using `by simp`. Rewrite using `[this, zero_mul, sub_zero]`. Establish `: (((n : ℂ) + 1)).re = (n : ℝ) + 1` using `by simp`. Rewrite using `[this]`. Apply `mul_nonneg (by positivity)` to reduce the goal to its premises.

Unfold `kIp`. Rewrite using `[Complex.re_sum]`. Conclude with `Finset.sum_nonneg fun J _ => kB_re_nonneg B hpos _`.
-/
theorem kT_nonneg {β : Type} [Fintype β] (B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ) (b : β → P)
    (T T' : P →ₗ[ℝ] Module.End ℂ M) (hB : ∀ x y, B y x = starRingEnd ℂ (B x y))
    (hpos : ∀ x, x ≠ 0 → 0 < (B x x).re) (hTT : ∀ X x y, B (T X x) y = B x (T' X y))
    {q : ℕ} (ω : P [⋀^Fin q]→ₗ[ℝ] M) :
    0 ≤ (∑ J : Fin q → β, B (ω (b ∘ J))
      (∑ s, ∑ i, T (b (J s)) (T' (b i) (ω (Function.update (b ∘ J) s (b i)))))).re := by
  cases q with
  | zero => simp
  | succ n =>
    have h1 : ∀ J : Fin (n + 1) → β, (∑ s, ∑ i, T (b (J s)) (T' (b i) (ω (Function.update (b ∘ J) s (b i))))) =
        kD T (kDel T' b ω) (b ∘ J) := fun J => (kD_kDel T T' b ω (b ∘ J)).symm
    simp_rw [h1]
    have h2 : (∑ J : Fin (n + 1) → β, B (ω (b ∘ J)) (kD T (kDel T' b ω) (b ∘ J))) =
        starRingEnd ℂ (kIp B b (kD T (kDel T' b ω)) ω) := by
      unfold kIp
      rw [map_sum]
      exact Finset.sum_congr rfl fun J _ => hB _ _
    rw [h2, kIp_kD B b T T' hTT (kDel T' b ω) ω, Complex.conj_re, Complex.mul_re]
    have : (((n : ℂ) + 1)).im = 0 := by simp
    rw [this, zero_mul, sub_zero]
    have : (((n : ℂ) + 1)).re = (n : ℝ) + 1 := by simp
    rw [this]
    apply mul_nonneg (by positivity)
    unfold kIp
    rw [Complex.re_sum]
    exact Finset.sum_nonneg fun J _ => kB_re_nonneg B hpos _

end

/- English proof (translation)
Introduce `P _ _ M _ _ _ _ β γ _ _ b B a r a' r' D c hb hB hpos ha hr har ha'r' hca hcr hc hD hcas q ω hω X`. Establish `hadj : ∀ X x y, B ((a + r) X x) y = B x ((r - a) X y)`. Introduce `X x y`. Simplify using `only [LinearMap.add_apply, LinearMap.sub_apply, map_add, map_sub, ha, hr]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hzero : kD (a + r) ω = 0`. Apply `kAlt_eq_zero b hb` to reduce the goal to its premises. Establish `hK : ∀ J : Fin q → β, kDel (r - a) b (kD (a + r) ω) (b ∘ J) = ((∑ i, r (b i) * r (b i) - ∑ k, r' k * r' k) - (∑ i, a (b i) * a (b i) - ∑ k, a' k * a' k) : Module.End ℂ M) (ω (b ∘ J)) - ∑ s, ∑ i, (a + r) (b (J s)) ((r - a) (b i) (ω (Function.update (b ∘ J) s (b i))))` using `fun J => eq_sub_of_add_eq (kHom b a r a' r' D c har ha'r' hca hcr hc hD ω hω J)`. Establish `hA` using `kIp_kD B b (a + r) (r - a) hadj ω (kD (a + r) ω)`. Establish `hT` using `kT_nonneg B b (a + r) (r - a) hB hpos hadj ω`.

Establish `h2 : ∀ J : Fin q → β, (B (ω (b ∘ J)) (((∑ i, r (b i) * r (b i) - ∑ k, r' k * r' k) - (∑ i, a (b i) * a (b i) - ∑ k, a' k * a' k) : Module.End ℂ M) (ω (b ∘ J)))).re ≤ 0`. Introduce `J`. Rewrite using `[hB]`. Simplify using `using hcas (ω (b ∘ J))`. Establish `h1 : (kIp B b ω (kDel (r - a) b (kD (a + r) ω))).re ≤ 0`.

Unfold `kIp`. Simplify using `only [hK, map_sub, Finset.sum_sub_distrib, Complex.sub_re]`. Establish `h3` using `Finset.sum_nonpos (fun J (_ : J ∈ Finset.univ) => h2 J)`. Rewrite `hT` using `[Complex.re_sum]`. Rewrite using `[Complex.re_sum, Complex.re_sum]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4 : (kIp B b (kD (a + r) ω) (kD (a + r) ω)).re ≤ 0`. Rewrite using `[hA, Complex.mul_re]`. Establish `: (((q : ℂ) + 1)).im = 0` using `by simp`. Rewrite using `[this, zero_mul, sub_zero]`.

Establish `: (((q : ℂ) + 1)).re = (q : ℝ) + 1` using `by simp`. Rewrite using `[this]`. Conclude with `mul_nonpos_of_nonneg_of_nonpos (by positivity) h1`. Unfold `kIp at h4`. Rewrite `h4` using `[Complex.re_sum]`.

Establish `h5` using `(Finset.sum_eq_zero_iff_of_nonneg (fun I (_ : I ∈ Finset.univ) => kB_re_nonneg B hpos (kD (a + r) ω (b ∘ I)))).1 (le_antisymm h4 (Finset.sum_nonneg (fun I _ => kB_re_nonneg B hpos _)))`. Introduce `I`. Assume the negation of the conclusion as `hI`. Conclude with `(hpos _ hI).ne' (h5 I (Finset.mem_univ _))`. Use `congrArg (fun f => f X) hzero` as an intermediate fact.

Simplify `this` using `[kD_apply]`.
-/
theorem kugaAbs_holds : KugaAbs := by
  intro P _ _ M _ _ _ _ β γ _ _ b B a r a' r' D c hb hB hpos ha hr har ha'r' hca hcr hc hD hcas q ω hω X
  have hadj : ∀ X x y, B ((a + r) X x) y = B x ((r - a) X y) := by
    intro X x y
    simp only [LinearMap.add_apply, LinearMap.sub_apply, map_add, map_sub, ha, hr]
    ring
  have hzero : kD (a + r) ω = 0 := by
    apply kAlt_eq_zero b hb
    have hK : ∀ J : Fin q → β, kDel (r - a) b (kD (a + r) ω) (b ∘ J) =
        ((∑ i, r (b i) * r (b i) - ∑ k, r' k * r' k) - (∑ i, a (b i) * a (b i) - ∑ k, a' k * a' k) :
          Module.End ℂ M) (ω (b ∘ J)) -
        ∑ s, ∑ i, (a + r) (b (J s)) ((r - a) (b i) (ω (Function.update (b ∘ J) s (b i)))) :=
      fun J => eq_sub_of_add_eq (kHom b a r a' r' D c har ha'r' hca hcr hc hD ω hω J)
    have hA := kIp_kD B b (a + r) (r - a) hadj ω (kD (a + r) ω)
    have hT := kT_nonneg B b (a + r) (r - a) hB hpos hadj ω
    have h2 : ∀ J : Fin q → β, (B (ω (b ∘ J))
        (((∑ i, r (b i) * r (b i) - ∑ k, r' k * r' k) - (∑ i, a (b i) * a (b i) - ∑ k, a' k * a' k) :
          Module.End ℂ M) (ω (b ∘ J)))).re ≤ 0 := by
      intro J
      rw [hB]
      simpa using hcas (ω (b ∘ J))
    have h1 : (kIp B b ω (kDel (r - a) b (kD (a + r) ω))).re ≤ 0 := by
      unfold kIp
      simp only [hK, map_sub, Finset.sum_sub_distrib, Complex.sub_re]
      have h3 := Finset.sum_nonpos (fun J (_ : J ∈ Finset.univ) => h2 J)
      rw [Complex.re_sum] at hT
      rw [Complex.re_sum, Complex.re_sum]
      linarith
    have h4 : (kIp B b (kD (a + r) ω) (kD (a + r) ω)).re ≤ 0 := by
      rw [hA, Complex.mul_re]
      have : (((q : ℂ) + 1)).im = 0 := by simp
      rw [this, zero_mul, sub_zero]
      have : (((q : ℂ) + 1)).re = (q : ℝ) + 1 := by simp
      rw [this]
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) h1
    unfold kIp at h4
    rw [Complex.re_sum] at h4
    have h5 := (Finset.sum_eq_zero_iff_of_nonneg (fun I (_ : I ∈ Finset.univ) =>
      kB_re_nonneg B hpos (kD (a + r) ω (b ∘ I)))).1
      (le_antisymm h4 (Finset.sum_nonneg (fun I _ => kB_re_nonneg B hpos _)))
    intro I
    by_contra hI
    exact (hpos _ hI).ne' (h5 I (Finset.mem_univ _))
  have := congrArg (fun f => f X) hzero
  simpa [kD_apply] using this

end PositivityTheory.Rg.Cz

end
