import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IwasawaCellDecomposition
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDEqSumOfAgree
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyDefiniteUnitaryLocalPointMemMaxCompact
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

noncomputable section

namespace GlobalTheory.CellDec

open Filter

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

/- English proof (translation)
The claim follows from `map_cornerGL_of_hom _ _ _ (fun _ => rfl) h`.
-/
theorem compV_finGL (v : HeightOneSpectrum (𝓞 E)) (h : GL (Fin n) (Af E)) :
    compV E n v (finGL E n h) = GeneralLinearGroup.map (pLoc E v) h :=
  map_cornerGL_of_hom _ _ _ (fun _ => rfl) h

/- English proof (translation)
Rewrite using `[compV_finGL, pLoc_locGL]`.
-/
theorem compV_finGL_locGL_same (v : HeightOneSpectrum (𝓞 E)) (y : GL (Fin n) (v.adicCompletion E)) :
    compV E n v (finGL E n (locGL E n v y)) = y := by
  rw [compV_finGL, pLoc_locGL]

/- English proof (translation)
Rewrite using `[compV_finGL, pLoc_locGL_of_ne h]`.
-/
theorem compV_finGL_locGL_ne {v w : HeightOneSpectrum (𝓞 E)} (h : w ≠ v) (y : GL (Fin n) (v.adicCompletion E)) :
    compV E n w (finGL E n (locGL E n v y)) = 1 := by
  rw [compV_finGL, pLoc_locGL_of_ne h]

/- English proof (translation)
Take `⟨h1, h2⟩` from `(GlobalTheory.SmGL.mem_unipB R).1 hg`. Use `(GlobalTheory.SmGL.mem_unipB S).2 ⟨fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) + s ((g : Matrix _ _ R) i j) = 0`. Rewrite using `[h1 i j hij, Matrix.one_apply_ne hij.ne', Matrix.one_apply_ne hij.ne', map_zero]`. Simplify using the standard rewrite rules.

Express the relevant statement in the definitionally equal form `(1 : Matrix (Fin a) (Fin a) S) i i - s ((1 : Matrix (Fin a) (Fin a) R) i i) + s ((g : Matrix _ _ R) i i) = 1`. Rewrite using `[h2 i, Matrix.one_apply_eq, Matrix.one_apply_eq]`. Simplify using the standard rewrite rules.
-/
theorem cornerGL_mem_unipB {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (s : R →ₙ+* S) {g : GL (Fin a) R}
    (hg : g ∈ GlobalTheory.SmGL.unipB R (Fin a)) : cornerGL a s g ∈ GlobalTheory.SmGL.unipB S (Fin a) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB R).1 hg
  refine (GlobalTheory.SmGL.mem_unipB S).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · change (1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) + s ((g : Matrix _ _ R) i j) = 0
    rw [h1 i j hij, Matrix.one_apply_ne hij.ne', Matrix.one_apply_ne hij.ne', map_zero]
    simp
  · change (1 : Matrix (Fin a) (Fin a) S) i i - s ((1 : Matrix (Fin a) (Fin a) R) i i) + s ((g : Matrix _ _ R) i i) = 1
    rw [h2 i, Matrix.one_apply_eq, Matrix.one_apply_eq]
    simp

/- English proof (translation)
The claim follows from `cornerGL_mem_unipB _ (cornerGL_mem_unipB _ hy)`.
-/
theorem finGL_locGL_mem_NA (v : HeightOneSpectrum (𝓞 E)) {y : GL (Fin n) (v.adicCompletion E)}
    (hy : y ∈ GlobalTheory.SmGL.unipB (v.adicCompletion E) (Fin n)) : finGL E n (locGL E n v y) ∈ NA E n :=
  cornerGL_mem_unipB _ (cornerGL_mem_unipB _ hy)

/- English proof (translation)
Simplify using `[US, Subgroup.mem_iInf]`.
-/
theorem mem_US {S : Finset (HeightOneSpectrum (𝓞 E))} {g : GA E n} :
    g ∈ US E n S ↔ ∀ v, v ∉ S → compV E n v g ∈ GlobalTheory.LFun.KGL v n := by
  simp [US, Subgroup.mem_iInf]

/- English proof (translation)
Establish `h : ∀ x : GA E n, ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∀ i j, (compV E n w x).val i j ∈ w.adicCompletionIntegers E` using `fun x => by`. Simplify using `only [Filter.eventually_all]`. Introduce `i j`. Conclude with `(pFin E ((x : Matrix (Fin n) (Fin n) (Ad E)) i j)).2`. Use `filter_upwards [h g, h g⁻¹] with w a b`.

Conclude with `GlobalTheory.BCT.GoodInt.mem_GLint _ _ a (by rw [← map_inv]; exact b)`.
-/
theorem eventually_compV_mem (g : GA E n) : ∀ᶠ w in cofinite, compV E n w g ∈ GlobalTheory.LFun.KGL w n := by
  have h : ∀ x : GA E n, ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∀ i j,
      (compV E n w x).val i j ∈ w.adicCompletionIntegers E := fun x => by
    simp only [Filter.eventually_all]
    intro i j
    exact (pFin E ((x : Matrix (Fin n) (Fin n) (Ad E)) i j)).2
  filter_upwards [h g, h g⁻¹] with w a b
  exact GlobalTheory.BCT.GoodInt.mem_GLint _ _ a (by rw [← map_inv]; exact b)

end GlobalTheory.CellDec

noncomputable section
namespace GlobalTheory.CellDec
open Filter
variable {E : Type} [Field E] [NumberField E] {n : ℕ}

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Apply `FiniteAdeleRing.ext` to reduce the goal to its premises. Introduce `v`. Express the relevant statement in the definitionally equal form `((ϖ v ^ (m₁ + m₂) v : (v.adicCompletion E)ˣ) : v.adicCompletion E) = ((ϖ v ^ m₁ v : (v.adicCompletion E)ˣ) : v.adicCompletion E) * ((ϖ v ^ m₂ v : (v.adicCompletion E)ˣ) : _)`. Rewrite using `[Finsupp.add_apply, _root_.zpow_add, Units.val_mul]`.
-/
theorem adl_add (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (m₁ m₂ : HeightOneSpectrum (𝓞 E) →₀ ℤ) :
    adl ϖ (m₁ + m₂) = adl ϖ m₁ * adl ϖ m₂ := by
  apply Units.ext
  apply FiniteAdeleRing.ext
  intro v
  change ((ϖ v ^ (m₁ + m₂) v : (v.adicCompletion E)ˣ) : v.adicCompletion E) =
    ((ϖ v ^ m₁ v : (v.adicCompletion E)ˣ) : v.adicCompletion E) * ((ϖ v ^ m₂ v : (v.adicCompletion E)ˣ) : _)
  rw [Finsupp.add_apply, _root_.zpow_add, Units.val_mul]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Apply `FiniteAdeleRing.ext` to reduce the goal to its premises. Introduce `v`. Express the relevant statement in the definitionally equal form `((ϖ v ^ (0 : HeightOneSpectrum (𝓞 E) →₀ ℤ) v : (v.adicCompletion E)ˣ) : v.adicCompletion E) = 1`. Simplify using the standard rewrite rules.
-/
theorem adl_zero (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) : adl ϖ 0 = 1 := by
  apply Units.ext
  apply FiniteAdeleRing.ext
  intro v
  change ((ϖ v ^ (0 : HeightOneSpectrum (𝓞 E) →₀ ℤ) v : (v.adicCompletion E)ˣ) : v.adicCompletion E) = 1
  simp

/- English proof (translation)
Unfold `tl`. Rewrite using `[← map_mul, ← map_mul]`. Use `congr 2`. Use function extensionality and compare the values at `i`. Rewrite using `[Pi.mul_apply, ← adl_add]`.

Use `congr 1`. Use extensionality with `v`. Simplify using the standard rewrite rules.
-/
theorem tl_add (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (l₁ l₂ : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) :
    tl n ϖ (l₁ + l₂) = tl n ϖ l₁ * tl n ϖ l₂ := by
  unfold tl
  rw [← map_mul, ← map_mul]
  congr 2
  funext i
  rw [Pi.mul_apply, ← adl_add]
  congr 1
  ext v
  simp

/- English proof (translation)
Unfold `tl`. Establish `: (fun i : Fin n => adl ϖ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl (0 : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)))) = 1`. Use function extensionality and compare the values at `i`. Rewrite using `[Finsupp.mapRange_zero, adl_zero]`. Both sides reduce to the same expression.

Rewrite using `[this, map_one, map_one]`.
-/
theorem tl_zero (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) : tl n ϖ 0 = 1 := by
  unfold tl
  have : (fun i : Fin n => adl ϖ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl (0 : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)))) = 1 := by
    funext i
    rw [Finsupp.mapRange_zero, adl_zero]
    rfl
  rw [this, map_one, map_one]

/- English proof (translation)
The claim follows from `Units.ext (Matrix.ext fun i k => IsDedekindDomain.FiniteAdeleRing.ext _ fun v => congrArg (fun x : GL (Fin n) (v.adicCompletion E) => x.val i k) (h v))`.
-/
theorem GL_ext_pLoc {x y : GL (Fin n) (Af E)}
    (h : ∀ w, GeneralLinearGroup.map (pLoc E w) x = GeneralLinearGroup.map (pLoc E w) y) : x = y :=
  Units.ext (Matrix.ext fun i k => IsDedekindDomain.FiniteAdeleRing.ext _ fun v =>
    congrArg (fun x : GL (Fin n) (v.adicCompletion E) => x.val i k) (h v))

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
/- English proof (translation)
Unfold `tl`. Use `congr 1`. Apply `GL_ext_pLoc` to reduce the goal to its premises. Introduce `w`. Distinguish the cases in `hw : w = v`.

Substitute `hw` using the available equality. Rewrite using `[pLoc_locGL]`. Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Rewrite using `[GlobalTheory.IwaCell.val_tD]`. Express the relevant statement in the definitionally equal form `pLoc E w (((GlobalTheory.SmGL.diagT (Af E) (Fin n) _ : GL (Fin n) (Af E)) : Matrix (Fin n) (Fin n) (Af E)) i j) = _`.

Rewrite using `[GlobalTheory.SmGL.val_diagT]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `only [Matrix.diagonal_apply_eq]`. Express the relevant statement in the definitionally equal form `((ϖ w ^ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl (Finsupp.single w a)) w : (w.adicCompletion E)ˣ) : w.adicCompletion E) = _`.

Simplify using the standard rewrite rules. Simplify using `[Matrix.diagonal_apply_ne _ hij]`. Rewrite using `[pLoc_locGL_of_ne hw]`. Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `pLoc E w (((GlobalTheory.SmGL.diagT (Af E) (Fin n) _ : GL (Fin n) (Af E)) : Matrix (Fin n) (Fin n) (Af E)) i j) = _`.

Rewrite using `[GlobalTheory.SmGL.val_diagT]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `only [Matrix.diagonal_apply_eq]`. Express the relevant statement in the definitionally equal form `((ϖ w ^ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl (Finsupp.single v a)) w : (w.adicCompletion E)ˣ) : w.adicCompletion E) = _`.

Simplify using `[Finsupp.single_apply, Ne.symm hw]`. Simplify using `[Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]`.
-/
theorem tl_single (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (v : HeightOneSpectrum (𝓞 E)) (a : Fin n → ℤ) :
    tl n ϖ (Finsupp.single v a) = finGL E n (locGL E n v (GlobalTheory.IwaCell.tD (ϖ v) a)) := by
  unfold tl
  congr 1
  apply GL_ext_pLoc
  intro w
  by_cases hw : w = v
  · subst hw
    rw [pLoc_locGL]
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [GlobalTheory.IwaCell.val_tD]
    change pLoc E w (((GlobalTheory.SmGL.diagT (Af E) (Fin n) _ : GL (Fin n) (Af E)) : Matrix (Fin n) (Fin n) (Af E)) i j) = _
    rw [GlobalTheory.SmGL.val_diagT]
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq]
      change ((ϖ w ^ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl (Finsupp.single w a)) w : (w.adicCompletion E)ˣ) : w.adicCompletion E) = _
      simp
    · simp [Matrix.diagonal_apply_ne _ hij]
  · rw [pLoc_locGL_of_ne hw]
    refine Units.ext (Matrix.ext fun i j => ?_)
    change pLoc E w (((GlobalTheory.SmGL.diagT (Af E) (Fin n) _ : GL (Fin n) (Af E)) : Matrix (Fin n) (Fin n) (Af E)) i j) = _
    rw [GlobalTheory.SmGL.val_diagT]
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq]
      change ((ϖ w ^ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl (Finsupp.single v a)) w : (w.adicCompletion E)ˣ) : w.adicCompletion E) = _
      simp [Finsupp.single_apply, Ne.symm hw]
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Rewrite using `[GlobalTheory.SmGL.SphCompletion.ord_completion, h]`. Express the relevant statement in the definitionally equal form `-WithZero.log (WithZero.exp (-1 : ℤ)) = 1`. Simplify using the standard rewrite rules.
-/
theorem ord_eq_one_of_isUnifV {v : HeightOneSpectrum (𝓞 E)} {π : (v.adicCompletion E)ˣ} (h : IsUnifV E v (π : v.adicCompletion E)) :
    GlobalTheory.SmGL.ord (v.adicCompletion E) π = 1 := by
  rw [GlobalTheory.SmGL.SphCompletion.ord_completion, h]
  change -WithZero.log (WithZero.exp (-1 : ℤ)) = 1
  simp

end
end GlobalTheory.CellDec

noncomputable section
namespace GlobalTheory.CellDec
open Filter
variable {E : Type} [Field E] [NumberField E] {n : ℕ}

/- English proof (translation)
Establish `h : tl n ϖ (-l) = (tl n ϖ l)⁻¹` using `eq_inv_of_mul_eq_one_left (by rw [← tl_add, neg_add_cancel, tl_zero])`. Use `tl_conj_mem ϖ (-l) hu` as an intermediate fact. Rewrite `this` using `[h, inv_inv]`. Then use the resulting hypothesis.
-/
theorem tl_inv_conj_mem (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ))
    {u : GA E n} (hu : u ∈ NA E n) : (tl n ϖ l)⁻¹ * u * tl n ϖ l ∈ NA E n := by
  have h : tl n ϖ (-l) = (tl n ϖ l)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← tl_add, neg_add_cancel, tl_zero])
  have := tl_conj_mem ϖ (-l) hu
  rwa [h, inv_inv] at this

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty`. Introduce `g hg`. Use `⟨0, fun _ _ => rfl, 1, one_mem _, g, mem_US.2 fun w hw => hg w hw (Finset.notMem_empty w), ?_⟩` and prove the remaining obligations. Rewrite using `[tl_zero, inv_one, one_mul]`.

Consider the case `insert v T hvT ih`. Introduce `g hg`. Distinguish the cases in `hvS : v ∈ S`. Use `ih g fun w hwS hwT => hg w hwS ?_` and prove the remaining obligations. Rewrite using `[Finset.mem_insert, not_or]`.

Conclude with `⟨fun h => hwS (h ▸ hvS), hwT⟩`. Take `⟨a, u, hu, κ, hκ, e⟩` from `GlobalTheory.IwaCell.exists_mem_cell (v.adicCompletion E) n (ϖ v) (ord_eq_one_of_isUnifV (hϖ v)) (compV E n v g)`. Rewrite `hκ` using `[GlobalTheory.HeckeEigConj.KO_eq_KGL]`. Use `set x := finGL E n (locGL E n v u) with hx`. Use `set t := tl n ϖ (Finsupp.single v a) with ht`.

Establish `hg' : ∀ w, w ∉ S → w ∉ T → compV E n w ((x * t)⁻¹ * g) ∈ GlobalTheory.LFun.KGL w n`. Introduce `w hwS hwT`. Rewrite using `[map_mul, map_inv, map_mul, hx, ht, tl_single]`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality.

Rewrite using `[compV_finGL_locGL_same, compV_finGL_locGL_same, e]`. Use `hκ using 1` and compare the differences between its conclusion and the goal. Use `group`. Rewrite using `[compV_finGL_locGL_ne hw, compV_finGL_locGL_ne hw, one_mul, inv_one, one_mul]`. Use `hg w hwS ?_` and prove the remaining obligations.

Rewrite using `[Finset.mem_insert, not_or]`. Conclude with `⟨hw, hwT⟩`. Take `⟨l', hl'S, u', hu', k, hk, e'⟩` from `ih _ hg'`. Use `⟨Finsupp.single v a + l', fun w hw => ?_, (tl n ϖ (Finsupp.single v a + l'))⁻¹ * x * tl n ϖ (Finsupp.single v a + l') * u', mul_mem (tl_inv_conj_mem ϖ _ (finGL_locGL_mem_NA v hu)) hu', k, hk, ?_⟩` and prove the remaining obligations. Rewrite using `[Finsupp.add_apply, hl'S w hw, Finsupp.single_apply, if_neg (fun (h : v = w) => hvS (h ▸ hw)), add_zero]`.

Establish `hg2 : g = x * t * (tl n ϖ l' * (u' * k))`. Rewrite using `[← e', mul_inv_cancel_left, mul_inv_cancel_left]`. Rewrite using `[hg2, tl_add, ← ht]`. Use `group`.
-/
theorem exists_of_finset (S : Finset (HeightOneSpectrum (𝓞 E))) (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ)
    (hϖ : ∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) (T : Finset (HeightOneSpectrum (𝓞 E))) :
    ∀ g : GA E n, (∀ w, w ∉ S → w ∉ T → compV E n w g ∈ GlobalTheory.LFun.KGL w n) →
      ∃ l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ), (∀ v ∈ S, l v = 0) ∧ (tl n ϖ l)⁻¹ * g ∈ C0 E n S := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro g hg
    refine ⟨0, fun _ _ => rfl, 1, one_mem _, g, mem_US.2 fun w hw => hg w hw (Finset.notMem_empty w), ?_⟩
    rw [tl_zero, inv_one, one_mul]
  | insert v T hvT ih =>
    intro g hg
    by_cases hvS : v ∈ S
    · refine ih g fun w hwS hwT => hg w hwS ?_
      rw [Finset.mem_insert, not_or]
      exact ⟨fun h => hwS (h ▸ hvS), hwT⟩
    · obtain ⟨a, u, hu, κ, hκ, e⟩ := GlobalTheory.IwaCell.exists_mem_cell (v.adicCompletion E) n (ϖ v) (ord_eq_one_of_isUnifV (hϖ v))
        (compV E n v g)
      rw [GlobalTheory.HeckeEigConj.KO_eq_KGL] at hκ
      set x := finGL E n (locGL E n v u) with hx
      set t := tl n ϖ (Finsupp.single v a) with ht
      have hg' : ∀ w, w ∉ S → w ∉ T → compV E n w ((x * t)⁻¹ * g) ∈ GlobalTheory.LFun.KGL w n := by
        intro w hwS hwT
        rw [map_mul, map_inv, map_mul, hx, ht, tl_single]
        by_cases hw : w = v
        · subst hw
          rw [compV_finGL_locGL_same, compV_finGL_locGL_same, e]
          convert hκ using 1
          group
        · rw [compV_finGL_locGL_ne hw, compV_finGL_locGL_ne hw, one_mul, inv_one, one_mul]
          refine hg w hwS ?_
          rw [Finset.mem_insert, not_or]
          exact ⟨hw, hwT⟩
      obtain ⟨l', hl'S, u', hu', k, hk, e'⟩ := ih _ hg'
      refine ⟨Finsupp.single v a + l', fun w hw => ?_, (tl n ϖ (Finsupp.single v a + l'))⁻¹ * x *
        tl n ϖ (Finsupp.single v a + l') * u', mul_mem (tl_inv_conj_mem ϖ _ (finGL_locGL_mem_NA v hu)) hu', k, hk, ?_⟩
      · rw [Finsupp.add_apply, hl'S w hw, Finsupp.single_apply, if_neg (fun (h : v = w) => hvS (h ▸ hw)), add_zero]
      · have hg2 : g = x * t * (tl n ϖ l' * (u' * k)) := by
          rw [← e', mul_inv_cancel_left, mul_inv_cancel_left]
        rw [hg2, tl_add, ← ht]
        group

/- English proof (translation)
Introduce `E _ _ n S ϖ hϖ g`. Establish `hfin : {w | compV E n w g ∉ GlobalTheory.LFun.KGL w n}.Finite` using `Filter.eventually_cofinite.1 (eventually_compV_mem g)`. Use `exists_of_finset S ϖ hϖ hfin.toFinset g fun w _ hw => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Conclude with `hw (hfin.mem_toFinset.2 h)`.
-/
theorem adelic_iwasawa_decomposition_off_finset : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ), (∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) →
    ∀ g : GA E n, ∃ l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ), (∀ v ∈ S, l v = 0) ∧
      (GlobalTheory.CellDec.tl n ϖ l)⁻¹ * g ∈ GlobalTheory.CellDec.C0 E n S := by
  intro E _ _ n S ϖ hϖ g
  have hfin : {w | compV E n w g ∉ GlobalTheory.LFun.KGL w n}.Finite :=
    Filter.eventually_cofinite.1 (eventually_compV_mem g)
  refine exists_of_finset S ϖ hϖ hfin.toFinset g fun w _ hw => ?_
  by_contra h
  exact hw (hfin.mem_toFinset.2 h)

end GlobalTheory.CellDec
