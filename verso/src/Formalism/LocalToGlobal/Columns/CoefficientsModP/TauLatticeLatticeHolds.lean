import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds

open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions

section TL

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {n : ℕ}

def du_f (φ : E →+* K) (x : Fin n → E) : Fin n → K := fun a => φ (x a)

def du_tl (φ : E →+* K) (L : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 K) (Fin n → K) :=
  Submodule.span (𝓞 K) (du_f φ '' (L : Set (Fin n → E)))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem du_tauLat_eq {ι : Type} (emb : ι → E →+* K) (τ : ι) (L : Submodule (𝓞 E) (Fin n → E)) :
    tauLat emb τ L = du_tl (emb τ) L := rfl

/- English proof (translation)
Use function extensionality and compare the values at `a`. Simplify using `[du_f]`.
-/
theorem du_f_add (φ : E →+* K) (x y : Fin n → E) : du_f φ (x + y) = du_f φ x + du_f φ y := by
  funext a; simp [du_f]

/- English proof (translation)
Use function extensionality and compare the values at `a`. Simplify using `[du_f]`.
-/
theorem du_f_zero (φ : E →+* K) : du_f φ (0 : Fin n → E) = 0 := by
  funext a; simp [du_f]

/- English proof (translation)
Use function extensionality and compare the values at `a`. Simplify using `[du_f]`.
-/
theorem du_f_smul (φ : E →+* K) (c : E) (x : Fin n → E) : du_f φ (c • x) = φ c • du_f φ x := by
  funext a; simp [du_f]

/- English proof (translation)
Use function extensionality and compare the values at `a`. Simplify using `only [du_f, Pi.smul_apply, Algebra.smul_def, map_mul]`. Both sides reduce to the same expression.
-/
theorem du_f_osmul (φ : E →+* K) (c : 𝓞 E) (x : Fin n → E) :
    du_f φ (c • x) = (RingOfIntegers.mapRingHom φ c) • du_f φ x := by
  funext a
  simp only [du_f, Pi.smul_apply, Algebra.smul_def, map_mul]
  rfl

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨x, hx, rfl⟩`.
-/
theorem du_f_mem (φ : E →+* K) {L : Submodule (𝓞 E) (Fin n → E)} {x : Fin n → E} (hx : x ∈ L) :
    du_f φ x ∈ du_tl φ L := Submodule.subset_span ⟨x, hx, rfl⟩

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩`.

Consider the case `zero => rw [du_f_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [du_f_add]`. Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx => rw [du_f_osmul]`.

Conclude with `Submodule.smul_mem _ _ hx`. Conclude with `Submodule.span_mono (Set.image_mono Submodule.subset_span)`.
-/
theorem du_tl_span (φ : E →+* K) (S : Set (Fin n → E)) :
    du_tl φ (Submodule.span (𝓞 E) S) = Submodule.span (𝓞 K) (du_f φ '' S) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [du_f_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [du_f_add]; exact add_mem hx hy
    | smul c x _ hx => rw [du_f_osmul]; exact Submodule.smul_mem _ _ hx
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Take `⟨S, hS⟩` from `hL.fg`. Rewrite using `[← hS, du_tl_span]`. Conclude with `⟨S.image (du_f φ), by rw [Finset.coe_image]⟩`. Establish `h1 : ∀ y ∈ Submodule.span E (L : Set (Fin n → E)), du_f φ y ∈ Submodule.span K (du_tl φ L : Set (Fin n → K))`.

Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx => exact Submodule.subset_span (du_f_mem φ hx)`. Consider the case `zero => rw [du_f_zero]`. Conclude with `zero_mem _`.

Consider the case `add x y _ _ hx hy => rw [du_f_add]`. Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx => rw [du_f_smul]`. Conclude with `Submodule.smul_mem _ _ hx`. Rewrite using `[eq_top_iff]`.

Introduce `z _`. Establish `hz : z = ∑ j, z j • du_f φ (Pi.single j (1 : E))`. Use function extensionality and compare the values at `a`. Simplify using `[du_f, Pi.single_apply, apply_ite φ]`. Rewrite using `[hz]`.

Use `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (h1 _ ?_)` and prove the remaining obligations. Rewrite using `[hL.span_eq_top]`. Discharge the goal by the elementary cases of `trivial`.
-/
theorem du_tl_lattice (φ : E →+* K) (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L) :
    Submodule.IsLattice K (du_tl φ L) := by
  classical
  constructor
  · obtain ⟨S, hS⟩ := hL.fg
    rw [← hS, du_tl_span]
    exact ⟨S.image (du_f φ), by rw [Finset.coe_image]⟩
  · have h1 : ∀ y ∈ Submodule.span E (L : Set (Fin n → E)),
        du_f φ y ∈ Submodule.span K (du_tl φ L : Set (Fin n → K)) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span (du_f_mem φ hx)
      | zero => rw [du_f_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [du_f_add]; exact add_mem hx hy
      | smul c x _ hx => rw [du_f_smul]; exact Submodule.smul_mem _ _ hx
    rw [eq_top_iff]
    intro z _
    have hz : z = ∑ j, z j • du_f φ (Pi.single j (1 : E)) := by
      funext a
      simp [du_f, Pi.single_apply, apply_ite φ]
    rw [hz]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (h1 _ ?_)
    rw [hL.span_eq_top]
    trivial

end TL

/- English proof (translation)
Introduce `E K _ _ _ _ ι n emb τ L hL`. Conclude with `du_tl_lattice (emb τ) L hL`.
-/
theorem tauLatticeLattice_holds : TauLatLattice := by
  intro E K _ _ _ _ ι n emb τ L hL
  exact du_tl_lattice (emb τ) L hL

section DB

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

def latticeTensorDualSpan (M : Submodule (𝓞 K) (Fin n → K)) : Submodule (𝓞 K) (Matrix (Fin n) (Fin n) K) :=
  Submodule.span (𝓞 K) {A | ∃ x ∈ M, ∃ φ ∈ dualFr M, A = Matrix.vecMulVec x φ}

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨j, rfl⟩`.
-/
theorem du_col_mem (B : GL (Fin n) K) (j : Fin n) :
    (fun a : Fin n => (B : Matrix (Fin n) (Fin n) K) a j) ∈ colLat B := Submodule.subset_span ⟨j, rfl⟩

/- English proof (translation)
Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨k, rfl⟩` from `hz`. Establish `: (fun b : Fin n => ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) j b) ⬝ᵥ (fun a : Fin n => (B : Matrix (Fin n) (Fin n) K) a k) = (((B⁻¹ * B : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) j k`. Rewrite using `[Units.val_mul, Matrix.mul_apply]`.

Both sides reduce to the same expression. Rewrite using `[this, inv_mul_cancel, Units.val_one, Matrix.one_apply]`. Use `split_ifs`. Conclude with `Submodule.mem_one.2 ⟨1, map_one _⟩`. Conclude with `zero_mem _`.

Consider the case `zero => rw [dotProduct_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [dotProduct_add]`. Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx => rw [dotProduct_smul]`.

Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem du_row_colLat (B : GL (Fin n) K) (j : Fin n) {z : Fin n → K} (hz : z ∈ colLat B) :
    (fun b : Fin n => ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) j b) ⬝ᵥ z ∈ (1 : Submodule (𝓞 K) K) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨k, rfl⟩ := hz
    have : (fun b : Fin n => ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) j b) ⬝ᵥ
        (fun a : Fin n => (B : Matrix (Fin n) (Fin n) K) a k) =
        (((B⁻¹ * B : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) j k := by
      rw [Units.val_mul, Matrix.mul_apply]; rfl
    rw [this, inv_mul_cancel, Units.val_one, Matrix.one_apply]
    split_ifs
    · exact Submodule.mem_one.2 ⟨1, map_one _⟩
    · exact zero_mem _
  | zero => rw [dotProduct_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [dotProduct_add]; exact add_mem hx hy
  | smul c x _ hx => rw [dotProduct_smul]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Establish `hle : ∀ (L : Submodule (𝓞 K) (Fin n → K)), L ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal L` using `fun L x hx => ⟨1, w.asIdeal.primeCompl.one_mem, by simpa using hx⟩`. Establish `h1 : ∀ j : Fin n, ∃ s ∈ w.asIdeal.primeCompl, s • (fun a : Fin n => (B : Matrix (Fin n) (Fin n) K) a j) ∈ M`. Introduce `j`. Establish `: (fun a : Fin n => (B : Matrix (Fin n) (Fin n) K) a j) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M`. Rewrite using `[hB]`.

Conclude with `hle _ (du_col_mem B j)`. Conclude with `this`. Use `choose s hs hsM using h1`. Take `⟨S, hS⟩` from `hfg`. Establish `h2 : ∀ g ∈ S, ∃ t ∈ w.asIdeal.primeCompl, t • g ∈ colLat B`.

Introduce `g hg`. Establish `: g ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (colLat B)`. Rewrite using `[← hB]`. Conclude with `hle _ (hS ▸ Submodule.subset_span hg)`. Conclude with `this`.

Use `choose! t ht htB using h2`. Establish `htt : (∏ g ∈ S, t g) ∈ w.asIdeal.primeCompl` using `Submonoid.prod_mem _ fun g hg => ht g hg`. Establish `h3 : ∀ x ∈ M, (∏ g ∈ S, t g) • x ∈ colLat B`. Introduce `x hx`. Rewrite `hx` using `[← hS]`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem g hg`. Rewrite using `[← Finset.mul_prod_erase S t hg, mul_comm, mul_smul]`. Conclude with `Submodule.smul_mem _ _ (htB g hg)`. Consider the case `zero => rw [smul_zero]`.

Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx => rw [smul_comm]`. Conclude with `Submodule.smul_mem _ _ hx`.

Establish `h4 : ∀ j : Fin n, (∏ g ∈ S, t g) • (fun b : Fin n => ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) j b) ∈ dualFr M`. Introduce `j x hx`. Rewrite using `[smul_dotProduct, ← dotProduct_smul]`. Conclude with `du_row_colLat B j (h3 x hx)`. Use `⟨(∏ j, s j) * ∏ g ∈ S, t g, w.asIdeal.primeCompl.mul_mem (Submonoid.prod_mem _ fun j _ => hs j) htt, ?_⟩` and prove the remaining obligations.

Establish `h5 : ((∏ j, s j) * ∏ g ∈ S, t g) • (1 : Matrix (Fin n) (Fin n) K) = ∑ j, Matrix.vecMulVec ((∏ j, s j) • (fun a : Fin n => (B : Matrix (Fin n) (Fin n) K) a j)) ((∏ g ∈ S, t g) • (fun b : Fin n => ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) j b))`. Use extensionality with `a b`. Establish `h6 : (1 : Matrix (Fin n) (Fin n) K) a b = ∑ j, (B : Matrix (Fin n) (Fin n) K) a j * ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) j b`. Rewrite using `[← Matrix.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one]`. Rewrite using `[Matrix.smul_apply, h6, Matrix.sum_apply, Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [Matrix.vecMulVec_apply, Pi.smul_apply, Algebra.smul_def, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h5]`. Use `Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨_, ?_, _, h4 j, rfl⟩` and prove the remaining obligations.

Rewrite using `[← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ j), mul_comm, mul_smul]`. Conclude with `Submodule.smul_mem _ _ (hsM j)`.
-/
theorem du_local (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K) (Fin n → K)) (hfg : M.FG)
    (B : GL (Fin n) K) (hB : IsBasisAt w M B) :
    ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • (1 : Matrix (Fin n) (Fin n) K) ∈ latticeTensorDualSpan M := by
  classical
  have hle : ∀ (L : Submodule (𝓞 K) (Fin n → K)), L ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal L := fun L x hx =>
    ⟨1, w.asIdeal.primeCompl.one_mem, by simpa using hx⟩

  have h1 : ∀ j : Fin n, ∃ s ∈ w.asIdeal.primeCompl,
      s • (fun a : Fin n => (B : Matrix (Fin n) (Fin n) K) a j) ∈ M := by
    intro j
    have : (fun a : Fin n => (B : Matrix (Fin n) (Fin n) K) a j) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M := by
      rw [hB]; exact hle _ (du_col_mem B j)
    exact this
  choose s hs hsM using h1

  obtain ⟨S, hS⟩ := hfg
  have h2 : ∀ g ∈ S, ∃ t ∈ w.asIdeal.primeCompl, t • g ∈ colLat B := by
    intro g hg
    have : g ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (colLat B) := by
      rw [← hB]; exact hle _ (hS ▸ Submodule.subset_span hg)
    exact this
  choose! t ht htB using h2
  have htt : (∏ g ∈ S, t g) ∈ w.asIdeal.primeCompl := Submonoid.prod_mem _ fun g hg => ht g hg
  have h3 : ∀ x ∈ M, (∏ g ∈ S, t g) • x ∈ colLat B := by
    intro x hx
    rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem g hg =>
      rw [← Finset.mul_prod_erase S t hg, mul_comm, mul_smul]
      exact Submodule.smul_mem _ _ (htB g hg)
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
  have h4 : ∀ j : Fin n, (∏ g ∈ S, t g) •
      (fun b : Fin n => ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) j b) ∈ dualFr M := by
    intro j x hx
    rw [smul_dotProduct, ← dotProduct_smul]
    exact du_row_colLat B j (h3 x hx)
  refine ⟨(∏ j, s j) * ∏ g ∈ S, t g, w.asIdeal.primeCompl.mul_mem (Submonoid.prod_mem _ fun j _ => hs j) htt, ?_⟩
  have h5 : ((∏ j, s j) * ∏ g ∈ S, t g) • (1 : Matrix (Fin n) (Fin n) K) =
      ∑ j, Matrix.vecMulVec ((∏ j, s j) • (fun a : Fin n => (B : Matrix (Fin n) (Fin n) K) a j))
        ((∏ g ∈ S, t g) • (fun b : Fin n => ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) j b)) := by
    ext a b
    have h6 : (1 : Matrix (Fin n) (Fin n) K) a b =
        ∑ j, (B : Matrix (Fin n) (Fin n) K) a j * ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) j b := by
      rw [← Matrix.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [Matrix.smul_apply, h6, Matrix.sum_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.vecMulVec_apply, Pi.smul_apply, Algebra.smul_def, map_mul]
    ring
  rw [h5]
  refine Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨_, ?_, _, h4 j, rfl⟩
  rw [← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ j), mul_comm, mul_smul]
  exact Submodule.smul_mem _ _ (hsM j)

/- English proof (translation)
Set `I : Ideal (𝓞 K)` to `(latticeTensorDualSpan M).comap (LinearMap.toSpanSingleton (𝓞 K) _ (1 : Matrix (Fin n) (Fin n) K))`. Establish `hI : I = ⊤`. Assume the negation of the conclusion as `h`. Take `⟨m, hm, hIm⟩` from `Ideal.exists_le_maximal I h`. Set `w : HeightOneSpectrum (𝓞 K)` to `⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)⟩`.

Take `⟨B, hB⟩` from `hBA K n M hM w`. Take `⟨s, hs, hs1⟩` from `du_local w M hM.fg B hB`. Conclude with `hs (hIm hs1)`. Establish `: (1 : 𝓞 K) ∈ I` using `hI ▸ Submodule.mem_top`. Simplify `this` using `[I]`.
-/
theorem du_one_mem (hBA : BasisAtEx) (M : Submodule (𝓞 K) (Fin n → K)) (hM : Submodule.IsLattice K M) :
    (1 : Matrix (Fin n) (Fin n) K) ∈ latticeTensorDualSpan M := by
  let I : Ideal (𝓞 K) := (latticeTensorDualSpan M).comap (LinearMap.toSpanSingleton (𝓞 K) _ (1 : Matrix (Fin n) (Fin n) K))
  have hI : I = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I h
    let w : HeightOneSpectrum (𝓞 K) :=
      ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)⟩
    obtain ⟨B, hB⟩ := hBA K n M hM w
    obtain ⟨s, hs, hs1⟩ := du_local w M hM.fg B hB
    exact hs (hIm hs1)
  have : (1 : 𝓞 K) ∈ I := hI ▸ Submodule.mem_top
  simpa [I] using this

/- English proof (translation)
Take `⟨m, f, g, hfg⟩` from `(Submodule.mem_span_set').1 (du_one_mem hBA M hM)`. Establish `hg : ∀ i, ∃ x ∈ M, ∃ φ ∈ dualFr M, (g i : Matrix (Fin n) (Fin n) K) = Matrix.vecMulVec x φ` using `fun i => (g i).2`. Use `choose x hx φ hφ hxφ using hg`. Use `⟨m, fun i => f i • x i, φ, fun i => Submodule.smul_mem _ _ (hx i), hφ, fun a b => ?_⟩` and prove the remaining obligations. Use `congrFun (congrFun hfg a) b` as an intermediate fact.

Rewrite `this` using `[Matrix.sum_apply, Matrix.one_apply]`. Rewrite using `[← this]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.smul_apply, hxφ, Matrix.vecMulVec_apply]`. Use `show (f i • x i) a * φ i b = _`.

Rewrite using `[Pi.smul_apply, smul_mul_assoc]`.
-/
theorem du_DB (hBA : BasisAtEx) (M : Submodule (𝓞 K) (Fin n → K)) (hM : Submodule.IsLattice K M) :
    ∃ (m : ℕ) (x φ : Fin m → Fin n → K), (∀ i, x i ∈ M) ∧ (∀ i, φ i ∈ dualFr M) ∧
      ∀ a b, ∑ i, x i a * φ i b = if a = b then 1 else 0 := by
  obtain ⟨m, f, g, hfg⟩ := (Submodule.mem_span_set').1 (du_one_mem hBA M hM)
  have hg : ∀ i, ∃ x ∈ M, ∃ φ ∈ dualFr M, (g i : Matrix (Fin n) (Fin n) K) = Matrix.vecMulVec x φ := fun i => (g i).2
  choose x hx φ hφ hxφ using hg
  refine ⟨m, fun i => f i • x i, φ, fun i => Submodule.smul_mem _ _ (hx i), hφ, fun a b => ?_⟩
  have := congrFun (congrFun hfg a) b
  rw [Matrix.sum_apply, Matrix.one_apply] at this
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.smul_apply, hxφ, Matrix.vecMulVec_apply]
  show (f i • x i) a * φ i b = _
  rw [Pi.smul_apply, smul_mul_assoc]

end DB

section Cons

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `b`. Rewrite using `[Finset.sum_apply]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, dotProduct, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [mul_assoc, ← Finset.mul_sum, h]`.

Simplify using the standard rewrite rules.
-/
theorem du_expand_left {m : ℕ} (x φ : Fin m → Fin n → K)
    (h : ∀ a b, ∑ i, x i a * φ i b = if a = b then 1 else 0) (ψ : Fin n → K) :
    ψ = ∑ i, (ψ ⬝ᵥ x i) • φ i := by
  funext b
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc, ← Finset.mul_sum, h]
  simp

/- English proof (translation)
Use function extensionality and compare the values at `a`. Rewrite using `[Finset.sum_apply]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, dotProduct, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Establish `: ∀ b i, φ i b * y b * x i a = y b * (x i a * φ i b)` using `fun b i => by ring`.

Simplify using `only [this, ← Finset.mul_sum, h]`. Simplify using the standard rewrite rules.
-/
theorem du_expand_right {m : ℕ} (x φ : Fin m → Fin n → K)
    (h : ∀ a b, ∑ i, x i a * φ i b = if a = b then 1 else 0) (y : Fin n → K) :
    y = ∑ i, (φ i ⬝ᵥ y) • x i := by
  funext a
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ b i, φ i b * y b * x i a = y b * (x i a * φ i b) := fun b i => by ring
  simp only [this, ← Finset.mul_sum, h]
  simp

/- English proof (translation)
Take `⟨r, rfl⟩` from `Submodule.mem_one.1 hc`. Rewrite using `[algebraMap_smul]`. Conclude with `N.smul_mem r hz`.
-/
theorem du_smul_of_mem_one {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (N : Submodule (𝓞 K) W) {c : K} (hc : c ∈ (1 : Submodule (𝓞 K) K)) {z : W} (hz : z ∈ N) : c • z ∈ N := by
  obtain ⟨r, rfl⟩ := Submodule.mem_one.1 hc
  rw [algebraMap_smul]
  exact N.smul_mem r hz

/- English proof (translation)
Take `⟨m, x, φ, hx, hφ, h⟩` from `du_DB hBA M hM`. Prove the components needed by the constructor for the conclusion. Use `⟨Finset.univ.image φ, le_antisymm (Submodule.span_le.2 ?_) ?_⟩` and prove the remaining obligations. Introduce `z hz`. Simplify using `only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hz`.

Take `⟨i, rfl⟩` from `hz`. Conclude with `hφ i`. Introduce `ψ hψ`. Rewrite using `[du_expand_left x φ h ψ]`. Use `Submodule.sum_mem _ fun i _ => du_smul_of_mem_one _ (hψ _ (hx i)) (Submodule.subset_span ?_)` and prove the remaining obligations.

Simplify using the standard rewrite rules. Rewrite using `[eq_top_iff]`. Introduce `ψ _`. Rewrite using `[du_expand_left x φ h ψ]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hφ i))`.
-/
theorem du_dualFr_lattice (hBA : BasisAtEx) (M : Submodule (𝓞 K) (Fin n → K)) (hM : Submodule.IsLattice K M) :
    Submodule.IsLattice K (dualFr M) := by
  classical
  obtain ⟨m, x, φ, hx, hφ, h⟩ := du_DB hBA M hM
  constructor
  · refine ⟨Finset.univ.image φ, le_antisymm (Submodule.span_le.2 ?_) ?_⟩
    · intro z hz
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hz
      obtain ⟨i, rfl⟩ := hz
      exact hφ i
    · intro ψ hψ
      rw [du_expand_left x φ h ψ]
      refine Submodule.sum_mem _ fun i _ => du_smul_of_mem_one _ (hψ _ (hx i)) (Submodule.subset_span ?_)
      simp
  · rw [eq_top_iff]
    intro ψ _
    rw [du_expand_left x φ h ψ]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hφ i))

/- English proof (translation)
Take `⟨m, x, φ, hx, hφ, h⟩` from `du_DB hBA M hM`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `y hy`. Rewrite using `[du_expand_right x φ h y]`. Use `Submodule.sum_mem _ fun i _ => du_smul_of_mem_one _ ?_ (hx i)` and prove the remaining obligations.

Rewrite using `[dotProduct_comm]`. Conclude with `hy _ (hφ i)`. Introduce `y hy φ' hφ'`. Rewrite using `[dotProduct_comm]`. Conclude with `hφ' y hy`.
-/
theorem du_dualFr_dualFr (hBA : BasisAtEx) (M : Submodule (𝓞 K) (Fin n → K)) (hM : Submodule.IsLattice K M) :
    dualFr (dualFr M) = M := by
  obtain ⟨m, x, φ, hx, hφ, h⟩ := du_DB hBA M hM
  apply le_antisymm
  · intro y hy
    rw [du_expand_right x φ h y]
    refine Submodule.sum_mem _ fun i _ => du_smul_of_mem_one _ ?_ (hx i)
    rw [dotProduct_comm]
    exact hy _ (hφ i)
  · intro y hy φ' hφ'
    rw [dotProduct_comm]
    exact hφ' y hy

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Simplify using `[du_f, dotProduct, map_sum]`.
-/
theorem du_f_dot (φ : E →+* K) (x y : Fin n → E) : du_f φ x ⬝ᵥ du_f φ y = φ (x ⬝ᵥ y) := by
  simp [du_f, dotProduct, map_sum]

/- English proof (translation)
Take `⟨r, rfl⟩` from `Submodule.mem_one.1 hc`. Conclude with `Submodule.mem_one.2 ⟨RingOfIntegers.mapRingHom φ r, rfl⟩`.
-/
theorem du_map_mem_one (φ : E →+* K) {c : E} (hc : c ∈ (1 : Submodule (𝓞 E) E)) :
    φ c ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨r, rfl⟩ := Submodule.mem_one.1 hc
  exact Submodule.mem_one.2 ⟨RingOfIntegers.mapRingHom φ r, rfl⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h x hx`. Conclude with `h _ (du_f_mem φ hx)`. Introduce `h z hz`. Proceed by induction on `hz using Submodule.span_induction with`.

Consider the case `mem z hz => obtain ⟨x, hx, rfl⟩ := hz`. Conclude with `h x hx`. Consider the case `zero => rw [dotProduct_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [dotProduct_add]`.

Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx => rw [dotProduct_smul]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem du_mem_dualFr_tl (φ : E →+* K) (L : Submodule (𝓞 E) (Fin n → E)) (ψ : Fin n → K) :
    ψ ∈ dualFr (du_tl φ L) ↔ ∀ x ∈ L, ψ ⬝ᵥ du_f φ x ∈ (1 : Submodule (𝓞 K) K) := by
  constructor
  · intro h x hx
    exact h _ (du_f_mem φ hx)
  · intro h z hz
    induction hz using Submodule.span_induction with
    | mem z hz => obtain ⟨x, hx, rfl⟩ := hz; exact h x hx
    | zero => rw [dotProduct_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [dotProduct_add]; exact add_mem hx hy
    | smul c x _ hx => rw [dotProduct_smul]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Take `⟨m, x, ξ, hx, hξ, h⟩` from `du_DB hBA L hL`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `ψ hψ`. Establish `h' : ∀ a b, ∑ i, du_f φ (x i) a * du_f φ (ξ i) b = if a = b then 1 else 0`. Introduce `a b`.

Use `congrArg φ (h a b)` as an intermediate fact. Rewrite `this` using `[map_sum, apply_ite φ, map_one, map_zero]`. Simplify `this` using `[du_f]`. Rewrite using `[du_expand_left _ _ h' ψ]`. Conclude with `Submodule.sum_mem _ fun i _ => du_smul_of_mem_one _ ((du_mem_dualFr_tl φ L ψ).1 hψ _ (hx i)) (du_f_mem φ (hξ i))`.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨ξ', hξ', rfl⟩`. Use `(du_mem_dualFr_tl φ L _).2 fun y hy => ?_` and prove the remaining obligations. Rewrite using `[du_f_dot]`. Conclude with `du_map_mem_one φ (hξ' y hy)`.
-/
theorem du_dualFr_tl (hBA : BasisAtEx) (φ : E →+* K) (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.IsLattice E L) : dualFr (du_tl φ L) = du_tl φ (dualFr L) := by
  obtain ⟨m, x, ξ, hx, hξ, h⟩ := du_DB hBA L hL
  apply le_antisymm
  · intro ψ hψ
    have h' : ∀ a b, ∑ i, du_f φ (x i) a * du_f φ (ξ i) b = if a = b then 1 else 0 := by
      intro a b
      have := congrArg φ (h a b)
      rw [map_sum, apply_ite φ, map_one, map_zero] at this
      simpa [du_f] using this
    rw [du_expand_left _ _ h' ψ]
    exact Submodule.sum_mem _ fun i _ =>
      du_smul_of_mem_one _ ((du_mem_dualFr_tl φ L ψ).1 hψ _ (hx i)) (du_f_mem φ (hξ i))
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨ξ', hξ', rfl⟩
    refine (du_mem_dualFr_tl φ L _).2 fun y hy => ?_
    rw [du_f_dot]
    exact du_map_mem_one φ (hξ' y hy)

end Cons

section H

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

/- English proof (translation)
Unfold `gLat`. Simplify using `only [Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`.

Conclude with `hy`. Introduce `h`. Conclude with `⟨_, h, by rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]⟩`.
-/
theorem du_mem_gLat (g : GL (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K)) (x : Fin n → K) :
    x ∈ gLat g M ↔ ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x ∈ M := by
  unfold gLat
  simp only [Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    exact hy
  · intro h
    exact ⟨_, h, by rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]⟩

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[du_mem_gLat, du_mem_gLat, du_mem_gLat, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_rev]`.
-/
theorem du_gLat_mul (g h : GL (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K)) :
    gLat g (gLat h M) = gLat (g * h) M := by
  ext x
  rw [du_mem_gLat, du_mem_gLat, du_mem_gLat, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_rev]

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[du_mem_gLat, inv_one, Units.val_one, Matrix.one_mulVec]`.
-/
theorem du_gLat_one (M : Submodule (𝓞 K) (Fin n → K)) : gLat 1 M = M := by
  ext x
  rw [du_mem_gLat, inv_one, Units.val_one, Matrix.one_mulVec]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Conclude with `hM.fg.map _`. Rewrite using `[eq_top_iff]`. Introduce `z _`. Establish `h1 : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ z ∈ Submodule.span K (M : Set (Fin n → K))`.

Rewrite using `[hM.span_eq_top]`. Discharge the goal by the elementary cases of `trivial`. Establish `h2 : (Submodule.span K (M : Set (Fin n → K))).map (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) K)) ≤ Submodule.span K (gLat g M : Set (Fin n → K))`. Rewrite using `[Submodule.map_span]`. Use `Submodule.span_mono ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `⟨y, hy, rfl⟩`. Establish `h3` using `h2 ⟨_, h1, rfl⟩`. Rewrite `h3` using `[Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`. Then use the resulting hypothesis.
-/
theorem du_gLat_lattice (g : GL (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K)) (hM : Submodule.IsLattice K M) :
    Submodule.IsLattice K (gLat g M) := by
  constructor
  · exact hM.fg.map _
  · rw [eq_top_iff]
    intro z _
    have h1 : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ z ∈ Submodule.span K (M : Set (Fin n → K)) := by
      rw [hM.span_eq_top]; trivial
    have h2 : (Submodule.span K (M : Set (Fin n → K))).map (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) K)) ≤
        Submodule.span K (gLat g M : Set (Fin n → K)) := by
      rw [Submodule.map_span]
      refine Submodule.span_mono ?_
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    have h3 := h2 ⟨_, h1, rfl⟩
    rwa [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec] at h3

/- English proof (translation)
Rewrite using `[Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]`.
-/
theorem du_transpose_dot (A : Matrix (Fin n) (Fin n) K) (x z : Fin n → K) :
    (Aᵀ *ᵥ x) ⬝ᵥ z = x ⬝ᵥ (A *ᵥ z) := by
  rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]

variable [StarRing K]

/- English proof (translation)
Rewrite using `[du_mem_dualFr_tl]`. Prove the components needed by the constructor for the conclusion. Introduce `h y hy`. Rewrite using `[dotProduct_comm]`. Conclude with `h y hy`.

Introduce `h y hy`. Use `h y hy` as an intermediate fact. Rewrite `this` using `[dotProduct_comm]`. Conclude with `this`.
-/
theorem du_mem_hdualFr (G : Matrix (Fin n) (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K)) (x : Fin n → K) :
    x ∈ hdualFr G M ↔ G *ᵥ x ∈ dualFr (du_tl (starRingEnd K) M) := by
  rw [du_mem_dualFr_tl]
  constructor
  · intro h y hy
    rw [dotProduct_comm]
    exact h y hy
  · intro h y hy
    have := h y hy
    rw [dotProduct_comm] at this
    exact this

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[du_mem_hdualFr, du_mem_gLat, inv_inv]`.
-/
theorem du_hdualFr_eq (G : GL (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K)) :
    hdualFr (G : Matrix (Fin n) (Fin n) K) M = gLat G⁻¹ (dualFr (du_tl (starRingEnd K) M)) := by
  ext x
  rw [du_mem_hdualFr, du_mem_gLat, inv_inv]

end H

/- English proof (translation)
Introduce `K _ _ _ n G M hG hM`. Use `⟨du_dualFr_lattice hBA M hM, ?_⟩` and prove the remaining obligations. Establish `hu : IsUnit G` using `(Matrix.isUnit_iff_isUnit_det G).2 hG`. Use `du_hdualFr_eq hu.unit M` as an intermediate fact. Rewrite `this` using `[IsUnit.unit_spec]`.

Rewrite using `[this]`. Conclude with `du_gLat_lattice _ _ (du_dualFr_lattice hBA _ (du_tl_lattice _ M hM))`.
-/
theorem dualFrLattice_of (hBA : BasisAtEx) : DualFrLattice := by
  intro K _ _ _ n G M hG hM
  refine ⟨du_dualFr_lattice hBA M hM, ?_⟩
  have hu : IsUnit G := (Matrix.isUnit_iff_isUnit_det G).2 hG
  have := du_hdualFr_eq hu.unit M
  rw [IsUnit.unit_spec] at this
  rw [this]
  exact du_gLat_lattice _ _ (du_dualFr_lattice hBA _ (du_tl_lattice _ M hM))

/- English proof (translation)
Introduce `K _ _ _ n G M _ hG hM`. Establish `hc : Submodule.IsLattice K (du_tl (starRingEnd K) M)` using `du_tl_lattice _ M hM`. Use extensionality with `x`. Rewrite using `[du_mem_hdualFr, ← du_dualFr_tl hBA _ M hM, du_dualFr_dualFr hBA _ hc]`. Rewrite using `[← du_dualFr_dualFr hBA _ hc]`.

Prove the components needed by the constructor for the conclusion. Introduce `h z hz`. Establish `h1` using `h _ ((du_mem_hdualFr G M z).1 hz)`. Rewrite `h1` using `[du_transpose_dot, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hG, Matrix.one_mulVec]`. Then use the resulting hypothesis. Introduce `h ζ hζ`.

Rewrite using `[du_transpose_dot]`. Use `h _ ((du_mem_hdualFr G M _).2 ?_)` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hG, Matrix.one_mulVec]` and apply the resulting hypothesis.
-/
theorem dualFrHdual_of (hBA : BasisAtEx) : DualFrHdual := by
  intro K _ _ _ n G M _ hG hM
  have hc : Submodule.IsLattice K (du_tl (starRingEnd K) M) := du_tl_lattice _ M hM
  ext x
  rw [du_mem_hdualFr, ← du_dualFr_tl hBA _ M hM, du_dualFr_dualFr hBA _ hc]
  rw [← du_dualFr_dualFr hBA _ hc]
  constructor
  · intro h z hz
    have h1 := h _ ((du_mem_hdualFr G M z).1 hz)
    rwa [du_transpose_dot, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hG, Matrix.one_mulVec] at h1
  · intro h ζ hζ
    rw [du_transpose_dot]
    refine h _ ((du_mem_hdualFr G M _).2 ?_)
    rwa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hG, Matrix.one_mulVec]

section ES

variable {E F K : Type} [Field E] [NumberField E] [Field F] [NumberField F] [Field K] [NumberField K] {n : ℕ}

/- English proof (translation)
Unfold `du_tl`. Rewrite using `[← du_tl, du_tl_span, Set.image_image]`. Both sides reduce to the same expression.
-/
theorem du_tl_comp (ψ : F →+* K) (φ : E →+* F) (L : Submodule (𝓞 E) (Fin n → E)) :
    du_tl ψ (du_tl φ L) = du_tl (ψ.comp φ) L := by
  unfold du_tl
  rw [← du_tl, du_tl_span, Set.image_image]
  rfl

/- English proof (translation)
Simplify using `only [Formalism.UG.hform, Matrix.mulVec, dotProduct, du_f, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem du_hform (cE : E →+* E) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    Formalism.UG.hform cE J x y = (J *ᵥ y) ⬝ᵥ du_f cE x := by
  simp only [Formalism.UG.hform, Matrix.mulVec, dotProduct, du_f, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Use extensionality with `y`. Rewrite using `[hL', du_mem_gLat, inv_inv, du_mem_dualFr_tl]`. Use `forall₂_congr fun x _ => ?_` and prove the remaining obligations. Rewrite using `[du_hform, Submodule.mem_one, RingHom.mem_range]`.
-/
theorem du_Lprime (cE : E →+* E) (Jg : GL (Fin n) E) (L L' : Submodule (𝓞 E) (Fin n → E))
    (hL' : ∀ y, y ∈ L' ↔ ∀ x ∈ L, Formalism.UG.hform cE (Jg : Matrix (Fin n) (Fin n) E) x y ∈ (algebraMap (𝓞 E) E).range) :
    L' = gLat Jg⁻¹ (dualFr (du_tl cE L)) := by
  ext y
  rw [hL', du_mem_gLat, inv_inv, du_mem_dualFr_tl]
  refine forall₂_congr fun x _ => ?_
  rw [du_hform, Submodule.mem_one, RingHom.mem_range]

/- English proof (translation)
The claim follows from `tauLatG E K ι n emb τ L γ`.
-/
theorem du_tl_gLat {ι : Type} (emb : ι → E →+* K) (τ : ι) (γ : GL (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) :
    du_tl (emb τ) (gLat γ L) = gLat (embGL emb γ τ) (du_tl (emb τ) L) :=
  tauLatG E K ι n emb τ L γ

end ES

/- English proof (translation)
Introduce `E K _ _ _ _ _ ι n emb cE τ hstar J L L' hJ hL hL'`. Establish `hu : IsUnit J` using `(Matrix.isUnit_iff_isUnit_det J).2 hJ`. Establish `hJg : (hu.unit : Matrix (Fin n) (Fin n) E) = J` using `IsUnit.unit_spec hu`. Rewrite `hL'` using `[← hJg]`. Establish `e1` using `du_Lprime cE hu.unit L L' hL'`.

Establish `e2 : (starRingEnd K).comp (emb τ) = (emb τ).comp cE` using `RingHom.ext fun x => hstar x`. Rewrite using `[e1, du_tauLat_eq, du_tauLat_eq, du_tl_gLat]`. Use extensionality with `x`. Rewrite using `[du_mem_hdualFr, du_mem_gLat, du_tl_comp, e2, ← du_tl_comp, du_dualFr_tl hBA _ _ (du_tl_lattice cE L hL), embGL_inv, inv_inv, embGL_coe, hJg]`. Both sides reduce to the same expression.
-/
theorem tauLatDual_of (hBA : BasisAtEx) : TauLatDual := by
  intro E K _ _ _ _ _ ι n emb cE τ hstar J L L' hJ hL hL'
  have hu : IsUnit J := (Matrix.isUnit_iff_isUnit_det J).2 hJ
  have hJg : (hu.unit : Matrix (Fin n) (Fin n) E) = J := IsUnit.unit_spec hu
  rw [← hJg] at hL'
  have e1 := du_Lprime cE hu.unit L L' hL'
  have e2 : (starRingEnd K).comp (emb τ) = (emb τ).comp cE := RingHom.ext fun x => hstar x
  rw [e1, du_tauLat_eq, du_tauLat_eq, du_tl_gLat]
  ext x
  rw [du_mem_hdualFr, du_mem_gLat, du_tl_comp, e2, ← du_tl_comp, du_dualFr_tl hBA _ _ (du_tl_lattice cE L hL),
    embGL_inv, inv_inv, embGL_coe, hJg]
  rfl

/- English proof (translation)
Introduce `E K _ _ _ _ ι n emb cE τ hcc Jg L L' hL hJ hL'`. Establish `e1` using `du_Lprime cE Jg L L' hL'`. Establish `e2 : (((emb τ).comp cE).comp cE) = emb τ` using `RingHom.ext fun x => by simp [hcc]`. Rewrite using `[e1, du_tauLat_eq, du_tauLat_eq, du_tl_gLat (fun τ => (emb τ).comp cE) τ, ← du_dualFr_tl hBA _ _ (du_tl_lattice cE L hL), du_tl_comp, e2, du_gLat_mul]`. Establish `e3 : invTrK (embGL emb Jg⁻¹) τ * embGL (fun τ => (emb τ).comp cE) Jg⁻¹ τ = 1`.

Apply `Units.ext` to reduce the goal to its premises. Establish `hJ' : Formalism.UG.cT cE (Jg : Matrix (Fin n) (Fin n) E) = (Jg : Matrix (Fin n) (Fin n) E)` using `hJ`. Establish `h1 : ((Jg : Matrix (Fin n) (Fin n) E).map (emb τ))ᵀ = (Jg : Matrix (Fin n) (Fin n) E).map ((emb τ).comp cE)` using `by conv_lhs => rw [← hJ']`. Use extensionality with `i j`. Simplify using `[Formalism.UG.cT]`.

Rewrite using `[Units.val_mul, invTrK_coe, embGL_inv, inv_inv, embGL_coe, embGL_coe, h1, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Units.val_one]`. Rewrite using `[e3, du_gLat_one]`.
-/
theorem roundLat_of (hBA : BasisAtEx) : RoundLat := by
  intro E K _ _ _ _ ι n emb cE τ hcc Jg L L' hL hJ hL'
  have e1 := du_Lprime cE Jg L L' hL'
  have e2 : (((emb τ).comp cE).comp cE) = emb τ := RingHom.ext fun x => by simp [hcc]
  rw [e1, du_tauLat_eq, du_tauLat_eq, du_tl_gLat (fun τ => (emb τ).comp cE) τ,
    ← du_dualFr_tl hBA _ _ (du_tl_lattice cE L hL), du_tl_comp, e2, du_gLat_mul]
  have e3 : invTrK (embGL emb Jg⁻¹) τ * embGL (fun τ => (emb τ).comp cE) Jg⁻¹ τ = 1 := by
    apply Units.ext
    have hJ' : Formalism.UG.cT cE (Jg : Matrix (Fin n) (Fin n) E) = (Jg : Matrix (Fin n) (Fin n) E) := hJ
    have h1 : ((Jg : Matrix (Fin n) (Fin n) E).map (emb τ))ᵀ =
        (Jg : Matrix (Fin n) (Fin n) E).map ((emb τ).comp cE) := by
      conv_lhs => rw [← hJ']
      ext i j
      simp [Formalism.UG.cT]
    rw [Units.val_mul, invTrK_coe, embGL_inv, inv_inv, embGL_coe, embGL_coe, h1, ← Matrix.map_mul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Units.val_one]
  rw [e3, du_gLat_one]

/- English proof (translation)
The claim follows from `dualFrLattice_of latticeBasisExists_holds`.
-/
theorem dualFrameLattice_holds : DualFrLattice := dualFrLattice_of latticeBasisExists_holds

/- English proof (translation)
The claim follows from `dualFrHdual_of latticeBasisExists_holds`.
-/
theorem dualFrameHdual_holds : DualFrHdual := dualFrHdual_of latticeBasisExists_holds

/- English proof (translation)
The claim follows from `tauLatDual_of latticeBasisExists_holds`.
-/
theorem tauLatticeDual_holds : TauLatDual := tauLatDual_of latticeBasisExists_holds

/- English proof (translation)
The claim follows from `roundLat_of latticeBasisExists_holds`.
-/
theorem roundLattice_holds : RoundLat := roundLat_of latticeBasisExists_holds

end Formalism.L2.DIV
