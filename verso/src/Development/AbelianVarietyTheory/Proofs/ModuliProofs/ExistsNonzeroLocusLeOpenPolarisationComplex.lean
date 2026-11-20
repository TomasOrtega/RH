import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsSectionRing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.AppLESurjective

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.AmpleBasis

open SectionRing

variable {K : Type} [Field K] {X : Scheme.{0}} (p : X ⟶ Sp K) (L : LB X)

def Extends (N : ℕ) (D : X.Opens) (t : Fam p L) (f : Γ(X, D)) (e : ℕ) : Prop :=
  ∃ σ ∈ secs p L (N * e), ∀ k,
    resG X (inf_le_right : D ⊓ chart L k ≤ _) (evalFam p L k σ) =
      resG X (inf_le_left : D ⊓ chart L k ≤ _) f *
        resG X (inf_le_right : D ⊓ chart L k ≤ _) (evalFam p L k t) ^ e

variable {p L} {N : ℕ} {D : X.Opens} {t : Fam p L}

/- English proof (translation)
Take `⟨σ, hσ, h⟩` from `hf`. Take `⟨τ, hτ, h'⟩` from `hg`. Use `⟨σ * τ, ?_, fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[mul_add]`. Conclude with `SetLike.GradedMul.mul_mem hσ hτ`.

Simplify using `only [map_mul]`. Rewrite using `[h k, h' k, pow_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Extends.mul {f g : Γ(X, D)} {e e' : ℕ} (hf : Extends p L N D t f e)
    (hg : Extends p L N D t g e') : Extends p L N D t (f * g) (e + e') := by
  obtain ⟨σ, hσ, h⟩ := hf
  obtain ⟨τ, hτ, h'⟩ := hg
  refine ⟨σ * τ, ?_, fun k => ?_⟩
  · rw [mul_add]
    exact SetLike.GradedMul.mul_mem hσ hτ
  · simp only [map_mul]
    rw [h k, h' k, pow_add]
    ring

/- English proof (translation)
Take `⟨σ, hσ, h⟩` from `hf`. Take `⟨τ, hτ, h'⟩` from `hg`. Use `⟨σ + τ, add_mem hσ hτ, fun k => ?_⟩` and prove the remaining obligations. Simplify using `only [map_add]`. Rewrite using `[h k, h' k, add_mul]`.
-/
theorem Extends.add {f g : Γ(X, D)} {e : ℕ} (hf : Extends p L N D t f e)
    (hg : Extends p L N D t g e) : Extends p L N D t (f + g) e := by
  obtain ⟨σ, hσ, h⟩ := hf
  obtain ⟨τ, hτ, h'⟩ := hg
  refine ⟨σ + τ, add_mem hσ hτ, fun k => ?_⟩
  simp only [map_add]
  rw [h k, h' k, add_mul]

/- English proof (translation)
Use `⟨t ^ e, ?_, fun k => ?_⟩` and prove the remaining obligations. Establish `hp` using `SetLike.pow_mem_graded e ht`. Rewrite `hp` using `[smul_eq_mul, mul_comm]`. Then use the resulting hypothesis. Rewrite using `[map_pow, map_pow, map_one]`. Conclude with `(_root_.one_mul _).symm`.
-/
theorem extends_one (ht : t ∈ secs p L N) (e : ℕ) : Extends p L N D t 1 e := by
  refine ⟨t ^ e, ?_, fun k => ?_⟩
  · have hp := SetLike.pow_mem_graded e ht
    rwa [smul_eq_mul, mul_comm] at hp
  · rw [map_pow, map_pow, map_one]
    exact (_root_.one_mul _).symm

/- English proof (translation)
Establish `hU : U ≤ p ⁻¹ᵁ ⊤` using `fun _ _ => trivial`. Establish `e : p.appLE ⊤ U hU ≫ X.presheaf.map (homOfLE h).op = p.appLE ⊤ V (h.trans hU)`. Rewrite using `[Scheme.Hom.appLE_map]`. Conclude with `congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) e`.
-/
private theorem resG_constHom' {U V : X.Opens} (h : V ≤ U) (a : K) :
    resG X h (constHom p U a) = constHom p V a := by
  have hU : U ≤ p ⁻¹ᵁ ⊤ := fun _ _ => trivial
  have e : p.appLE ⊤ U hU ≫ X.presheaf.map (homOfLE h).op = p.appLE ⊤ V (h.trans hU) := by
    rw [Scheme.Hom.appLE_map]
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) e

/- English proof (translation)
Use `⟨fun j => constHom p (chart L j) a, ?_, fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[mul_zero]`. Introduce `i j`. Rewrite using `[trans_zero, _root_.one_mul]`. Express the relevant statement in the definitionally equal form `resG X _ (constHom p _ a) = resG X _ (constHom p _ a)`.

Rewrite using `[resG_constHom', resG_constHom']`. Rewrite using `[pow_zero, _root_.mul_one]`. Express the relevant statement in the definitionally equal form `resG X _ (constHom p _ a) = resG X _ (constHom p _ a)`. Rewrite using `[resG_constHom', resG_constHom']`.
-/
theorem extends_const (a : K) : Extends p L N D t (constHom p D a) 0 := by
  refine ⟨fun j => constHom p (chart L j) a, ?_, fun k => ?_⟩
  · rw [mul_zero]
    intro i j
    rw [trans_zero, _root_.one_mul]
    change resG X _ (constHom p _ a) = resG X _ (constHom p _ a)
    rw [resG_constHom', resG_constHom']
  · rw [pow_zero, _root_.mul_one]
    change resG X _ (constHom p _ a) = resG X _ (constHom p _ a)
    rw [resG_constHom', resG_constHom']

/- English proof (translation)
Simplify `hf.mul (extends_one ht e')` using `only [_root_.mul_one]`.
-/
private theorem extends_add (ht : t ∈ secs p L N) {f : Γ(X, D)} {e : ℕ}
    (hf : Extends p L N D t f e) (e' : ℕ) : Extends p L N D t f (e + e') := by
  simpa only [_root_.mul_one] using hf.mul (extends_one ht e')

/- English proof (translation)
Proceed by induction on `F using MvPolynomial.induction_on`. Use `next a =>`. Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[MvPolynomial.eval₂_C]`. Conclude with `extends_const a`.

Use `next P Q hP hQ =>`. Take `⟨a, ha⟩` from `hP`. Take `⟨b, hb⟩` from `hQ`. Use `⟨a + b, ?_⟩` and prove the remaining obligations. Rewrite using `[MvPolynomial.eval₂_add]`.

Use `(extends_add ht ha b).add ?_` and prove the remaining obligations. Rewrite using `[add_comm a b]`. Conclude with `extends_add ht hb a`. Use `next P j hP =>`. Take `⟨a, ha⟩` from `hP`.

Use `⟨a + 1, ?_⟩` and prove the remaining obligations. Rewrite using `[MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]`. Conclude with `ha.mul (hr j)`.
-/
theorem extends_eval₂ {J : Type} (ht : t ∈ secs p L N) (r : J → Γ(X, D))
    (hr : ∀ j, Extends p L N D t (r j) 1) (F : MvPolynomial J K) :
    ∃ e, Extends p L N D t (MvPolynomial.eval₂ (constHom p D) r F) e := by
  induction F using MvPolynomial.induction_on
  next a =>
    refine ⟨0, ?_⟩
    rw [MvPolynomial.eval₂_C]
    exact extends_const a
  next P Q hP hQ =>
    obtain ⟨a, ha⟩ := hP
    obtain ⟨b, hb⟩ := hQ
    refine ⟨a + b, ?_⟩
    rw [MvPolynomial.eval₂_add]
    refine (extends_add ht ha b).add ?_
    rw [add_comm a b]
    exact extends_add ht hb a
  next P j hP =>
    obtain ⟨a, ha⟩ := hP
    refine ⟨a + 1, ?_⟩
    rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    exact ha.mul (hr j)

/- English proof (translation)
The claim follows from `Scheme.basicOpen_res X x (homOfLE h).op`.
-/
private theorem basicOpen_resG' {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)) :
    X.basicOpen (resG X h x) = V ⊓ X.basicOpen x :=
  Scheme.basicOpen_res X x (homOfLE h).op

/- English proof (translation)
Take `⟨σ, hσ, h⟩` from `hf`. Establish `hmem : σ * (secEquiv p L N s : Fam p L) ∈ secs p L (N * e + N)` using `SetLike.GradedMul.mul_mem hσ (secEquiv p L N s).2`. Establish `key : ∀ k, (Out.nonzeroLocus s ⊓ chart L k) ⊓ X.basicOpen (evalFam p L k (σ * (secEquiv p L N s : Fam p L))) = (Out.nonzeroLocus s ⊓ chart L k ⊓ X.basicOpen f) ⊓ (Out.nonzeroLocus s ⊓ chart L k ⊓ X.basicOpen (evalFam p L k (secEquiv p L N s : Fam p L)))`. Introduce `k`. Rewrite using `[← basicOpen_resG' (inf_le_right : Out.nonzeroLocus s ⊓ chart L k ≤ _), map_mul, map_mul, h k, _root_.mul_assoc, ← pow_succ, Scheme.basicOpen_mul, Scheme.basicOpen_pow _ _ e.succ_pos, basicOpen_resG', basicOpen_resG']`.

Use `⟨N * e + N, (secEquiv p L (N * e + N)).symm ⟨_, hmem⟩, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `y ∈ ⨆ k, X.basicOpen (evalFam p L k (σ * (secEquiv p L N s : Fam p L)))`. Establish `hyD : y ∈ Out.nonzeroLocus s` using `X.basicOpen_le f hy`. Take `⟨k, hk⟩` from `TopologicalSpace.Opens.mem_iSup.mp (show y ∈ ⨆ k, X.basicOpen (s.f k) from hyD)`. Establish `hkc : y ∈ chart L k` using `X.basicOpen_le _ hk`.

Establish `hmemk : y ∈ (Out.nonzeroLocus s ⊓ chart L k) ⊓ X.basicOpen (evalFam p L k (σ * (secEquiv p L N s : Fam p L)))`. Rewrite using `[key k]`. Conclude with `⟨⟨⟨hyD, hkc⟩, hy⟩, ⟨⟨hyD, hkc⟩, hk⟩⟩`. Conclude with `TopologicalSpace.Opens.mem_iSup.mpr ⟨k, hmemk.2⟩`. Express the relevant statement in the definitionally equal form `(⨆ k, X.basicOpen (evalFam p L k (σ * (secEquiv p L N s : Fam p L)))) ≤ X.basicOpen f`.

Use `iSup_le fun k z hz => ?_` and prove the remaining obligations. Establish `hz2` using `hz`. Rewrite `hz2` using `[map_mul, Scheme.basicOpen_mul]`. Establish `hz' : z ∈ X.basicOpen (s.f k)` using `hz2.2`. Establish `hzD : z ∈ Out.nonzeroLocus s` using `TopologicalSpace.Opens.mem_iSup.mpr ⟨k, hz'⟩`.

Establish `hkc : z ∈ chart L k` using `X.basicOpen_le _ hz'`. Establish `hzk : z ∈ (Out.nonzeroLocus s ⊓ chart L k) ⊓ X.basicOpen (evalFam p L k (σ * (secEquiv p L N s : Fam p L)))` using `⟨⟨hzD, hkc⟩, hz⟩`. Rewrite `hzk` using `[key k]`. Conclude with `hzk.1.2`.
-/
theorem exists_locus (s : (lbPow L N).Sec) (f : Γ(X, Out.nonzeroLocus s)) (e : ℕ)
    (hf : Extends p L N (Out.nonzeroLocus s) (secEquiv p L N s : Fam p L) f e)
    (y : X) (hy : y ∈ X.basicOpen f) :
    ∃ (n : ℕ) (σ : (lbPow L n).Sec), y ∈ Out.nonzeroLocus σ ∧ Out.nonzeroLocus σ ≤ X.basicOpen f := by
  obtain ⟨σ, hσ, h⟩ := hf
  have hmem : σ * (secEquiv p L N s : Fam p L) ∈ secs p L (N * e + N) :=
    SetLike.GradedMul.mul_mem hσ (secEquiv p L N s).2
  have key : ∀ k, (Out.nonzeroLocus s ⊓ chart L k) ⊓
      X.basicOpen (evalFam p L k (σ * (secEquiv p L N s : Fam p L))) =
      (Out.nonzeroLocus s ⊓ chart L k ⊓ X.basicOpen f) ⊓
        (Out.nonzeroLocus s ⊓ chart L k ⊓ X.basicOpen (evalFam p L k (secEquiv p L N s : Fam p L))) := by
    intro k
    rw [← basicOpen_resG' (inf_le_right : Out.nonzeroLocus s ⊓ chart L k ≤ _), map_mul, map_mul, h k,
      _root_.mul_assoc, ← pow_succ, Scheme.basicOpen_mul, Scheme.basicOpen_pow _ _ e.succ_pos,
      basicOpen_resG', basicOpen_resG']
  refine ⟨N * e + N, (secEquiv p L (N * e + N)).symm ⟨_, hmem⟩, ?_, ?_⟩
  · change y ∈ ⨆ k, X.basicOpen (evalFam p L k (σ * (secEquiv p L N s : Fam p L)))
    have hyD : y ∈ Out.nonzeroLocus s := X.basicOpen_le f hy
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp (show y ∈ ⨆ k, X.basicOpen (s.f k) from hyD)
    have hkc : y ∈ chart L k := X.basicOpen_le _ hk
    have hmemk : y ∈ (Out.nonzeroLocus s ⊓ chart L k) ⊓
        X.basicOpen (evalFam p L k (σ * (secEquiv p L N s : Fam p L))) := by
      rw [key k]
      exact ⟨⟨⟨hyD, hkc⟩, hy⟩, ⟨⟨hyD, hkc⟩, hk⟩⟩
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨k, hmemk.2⟩
  · change (⨆ k, X.basicOpen (evalFam p L k (σ * (secEquiv p L N s : Fam p L)))) ≤ X.basicOpen f
    refine iSup_le fun k z hz => ?_
    have hz2 := hz
    rw [map_mul, Scheme.basicOpen_mul] at hz2
    have hz' : z ∈ X.basicOpen (s.f k) := hz2.2
    have hzD : z ∈ Out.nonzeroLocus s := TopologicalSpace.Opens.mem_iSup.mpr ⟨k, hz'⟩
    have hkc : z ∈ chart L k := X.basicOpen_le _ hz'
    have hzk : z ∈ (Out.nonzeroLocus s ⊓ chart L k) ⊓
        X.basicOpen (evalFam p L k (σ * (secEquiv p L N s : Fam p L))) := ⟨⟨hzD, hkc⟩, hz⟩
    rw [key k] at hzk
    exact hzk.1.2

end GlobalTheory.AmpleBasis

namespace GlobalTheory

open SectionRing AmpleBasis

/- English proof (translation)
Introduce `hL P₀ O y hy`. Take `⟨m, s, hcov, hs⟩` from `veryAmple_lbPow hL.ample ℂ P₀ 4 le_rfl`. Establish `hyt : y ∈ (⨆ i, Out.nonzeroLocus (s i))`. Rewrite using `[hcov]`. Discharge the goal by the elementary cases of `trivial`.

Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.mp hyt`. Take `⟨haff, r, hr, hpoly⟩` from `hs i`. Take `⟨f, hfO, hyf⟩` from `haff.exists_basicOpen_le ⟨y, hy⟩ hi`. Take `⟨F, hF⟩` from `hpoly f`. Establish `hrj : ∀ j, Extends P₀.A.hom P₀.L 4 (Out.nonzeroLocus (s i)) (secEquiv P₀.A.hom P₀.L 4 (s i) : Fam P₀.A.hom P₀.L) (r j) 1`.

Introduce `j`. Use `⟨secEquiv P₀.A.hom P₀.L 4 (s j), ?_, fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.mul_one]`. Conclude with `(secEquiv P₀.A.hom P₀.L 4 (s j)).2`. Rewrite using `[pow_one]`.

Conclude with `hr j k`. Take `⟨e, he⟩` from `extends_eval₂ (secEquiv P₀.A.hom P₀.L 4 (s i)).2 r hrj F`. Establish `he' : Extends P₀.A.hom P₀.L 4 (Out.nonzeroLocus (s i)) (secEquiv P₀.A.hom P₀.L 4 (s i) : Fam P₀.A.hom P₀.L) f e`. Rewrite using `[hF]`. Conclude with `he`.

Take `⟨n, σ, hyσ, hσf⟩` from `exists_locus (s i) f e he' y hyf`. Conclude with `⟨n, σ, hyσ, hσf.trans hfO⟩`.
-/
theorem exists_nonzeroLocus_le : Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (O : P₀.A.left.Opens) (y : P₀.A.left), y ∈ O → ∃ (n : ℕ) (σ : (lbPow P₀.L n).Sec), y ∈ Out.nonzeroLocus σ ∧ Out.nonzeroLocus σ ≤ O := by
  intro hL P₀ O y hy
  obtain ⟨m, s, hcov, hs⟩ := veryAmple_lbPow hL.ample ℂ P₀ 4 le_rfl
  have hyt : y ∈ (⨆ i, Out.nonzeroLocus (s i)) := by
    rw [hcov]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hyt
  obtain ⟨haff, r, hr, hpoly⟩ := hs i
  obtain ⟨f, hfO, hyf⟩ := haff.exists_basicOpen_le ⟨y, hy⟩ hi
  obtain ⟨F, hF⟩ := hpoly f
  have hrj : ∀ j, Extends P₀.A.hom P₀.L 4 (Out.nonzeroLocus (s i)) (secEquiv P₀.A.hom P₀.L 4 (s i) : Fam P₀.A.hom P₀.L)
      (r j) 1 := by
    intro j
    refine ⟨secEquiv P₀.A.hom P₀.L 4 (s j), ?_, fun k => ?_⟩
    · rw [Nat.mul_one]
      exact (secEquiv P₀.A.hom P₀.L 4 (s j)).2
    · rw [pow_one]
      exact hr j k
  obtain ⟨e, he⟩ := extends_eval₂ (secEquiv P₀.A.hom P₀.L 4 (s i)).2 r hrj F
  have he' : Extends P₀.A.hom P₀.L 4 (Out.nonzeroLocus (s i))
      (secEquiv P₀.A.hom P₀.L 4 (s i) : Fam P₀.A.hom P₀.L) f e := by
    rw [hF]
    exact he
  obtain ⟨n, σ, hyσ, hσf⟩ := exists_locus (s i) f e he' y hyf
  exact ⟨n, σ, hyσ, hσf.trans hfO⟩

end GlobalTheory
