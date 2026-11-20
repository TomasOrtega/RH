import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralTensorAdelesEqAdelicCompletionOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHeckeOpFullDualLab
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSatVecUOfDiag

noncomputable section

namespace GlobalTheory.LFun

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU

/- English proof (translation)
Establish `hv : ∀ (A : Matrix (Fin n) (Fin n) R) z i, π (A.mulVec z i) = (A.map π *ᵥ fun j => π (z j)) i` using `fun A z i => RingHom.map_mulVec π A z i`. Establish `hB : (a.1.map s).map π = a.1` using `Matrix.ext fun i j => hs _`. Use `choose r hr er using hu`. Use `choose r' hr' er' using hu'`. Use `⟨a.1.map s, fun z hz => ?_, fun y hy => ?_, fun y hy => ?_, fun z hz => ?_⟩` and prove the remaining obligations.

Simplify using `only [hε, hv, hB]`. Conclude with `hΛ' _ fun i => hI _ (hz i)`. Use `⟨_, fun i => hI' _ (hΛ y hy i), ?_⟩` and prove the remaining obligations. Simplify using `only [hε, hv, hB, hs, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`. Use `⟨_, fun i => hI' _ (mul_mem (hr i) (hΛ y hy i)), ?_⟩` and prove the remaining obligations.

Simplify using `only [hε, hv, hB, hs, hM, map_mul, ← Matrix.mulVec_mulVec, ← mul_assoc, ← er]`. Use `congr! 3`. Conclude with `funext fun i => Matrix.mulVec_diagonal _ _ i`. Use `⟨_, hΛ' _ fun i => mul_mem (hr' i) (hI _ (hz i)), ?_⟩` and prove the remaining obligations. Simplify using `only [hε, hv, hB, hs, hM, map_mul, er']`.

Use `congr! 2`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, ← Matrix.mulVec_mulVec]`. Use `congr 2`. Conclude with `funext fun i => (Matrix.mulVec_diagonal _ _ i).trans (mul_assoc _ _ _).symm`.
-/
theorem div_of_component {R K : Type} [CommRing R] [Field K] {n : ℕ} (π : R →+* K) (s : K → R)
    (hs : ∀ x, π (s x) = x) {ε : R} (hε : ∀ y, ε * y = s (π y)) {I : R → Prop} {O : Subring K}
    (hI : ∀ y, I y → π y ∈ O) (hI' : ∀ x ∈ O, I (s x)) {Λ : (Fin n → R) → Prop} (a : GL (Fin n) K)
    (hΛ : ∀ y, Λ y → ∀ i, ((a⁻¹).1 *ᵥ fun j => π (y j)) i ∈ O)
    (hΛ' : ∀ x : Fin n → K, (∀ i, x i ∈ O) → Λ fun i => s ((a.1 *ᵥ x) i))
    {M : Matrix (Fin n) (Fin n) R} {t : Fin n → R} {u : Fin n → K}
    (hM : M.map π = a.1 * Matrix.diagonal u * (a⁻¹).1)
    (hu : ∀ i, ∃ r ∈ O, u i = π (t i) * r) (hu' : ∀ i, ∃ r ∈ O, π (t i) = u i * r) :
    ∃ B : Matrix (Fin n) (Fin n) R,
      (∀ z, (∀ i, I (z i)) → Λ fun i => ε * B.mulVec z i) ∧
      (∀ y, Λ y → ∃ z, (∀ i, I (z i)) ∧ (fun i => ε * y i) = fun i => ε * B.mulVec z i) ∧
      (∀ y, Λ y → ∃ z : Fin n → R, (∀ i, I (z i)) ∧
        (fun i => ε * M.mulVec y i) = fun i => ε * B.mulVec (fun j => t j * z j) i) ∧
      (∀ z : Fin n → R, (∀ i, I (z i)) → ∃ y, Λ y ∧
        (fun i => ε * M.mulVec y i) = fun i => ε * B.mulVec (fun j => t j * z j) i) := by
  have hv : ∀ (A : Matrix (Fin n) (Fin n) R) z i, π (A.mulVec z i) = (A.map π *ᵥ fun j => π (z j)) i :=
    fun A z i => RingHom.map_mulVec π A z i
  have hB : (a.1.map s).map π = a.1 := Matrix.ext fun i j => hs _
  choose r hr er using hu
  choose r' hr' er' using hu'
  refine ⟨a.1.map s, fun z hz => ?_, fun y hy => ?_, fun y hy => ?_, fun z hz => ?_⟩
  · simp only [hε, hv, hB]
    exact hΛ' _ fun i => hI _ (hz i)
  · refine ⟨_, fun i => hI' _ (hΛ y hy i), ?_⟩
    simp only [hε, hv, hB, hs, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  · refine ⟨_, fun i => hI' _ (mul_mem (hr i) (hΛ y hy i)), ?_⟩
    simp only [hε, hv, hB, hs, hM, map_mul, ← Matrix.mulVec_mulVec, ← mul_assoc, ← er]
    congr! 3
    exact funext fun i => Matrix.mulVec_diagonal _ _ i
  · refine ⟨_, hΛ' _ fun i => mul_mem (hr' i) (hI _ (hz i)), ?_⟩
    simp only [hε, hv, hB, hs, hM, map_mul, er']
    congr! 2
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, ← Matrix.mulVec_mulVec]
    congr 2
    exact funext fun i => (Matrix.mulVec_diagonal _ _ i).trans (mul_assoc _ _ _).symm

/- English proof (translation)
Establish `hK' : ∀ k, ι k ∈ KS ↔ k ∈ K` using `fun k => (hK _).trans ⟨fun ⟨k', h, e⟩ => hι e ▸ h, fun h => ⟨k, h, rfl⟩⟩`. Prove the components needed by the constructor for the conclusion. Introduce `γ hγ`. Take `⟨y, hy, rfl⟩` from `Finset.mem_image.1 hγ`. Take `⟨k₁, m₁, k₂, m₂, rfl⟩` from `h1 y hy`.

Conclude with `⟨_, (hK' _).2 m₁, _, (hK' _).2 m₂, by rw [map_mul, map_mul]⟩`. Introduce and unpack `_ ⟨k₁, m₁, k₂, m₂, rfl⟩`. Take `⟨l₁, g₁, rfl⟩` from `(hK _).1 m₁`. Take `⟨l₂, g₂, rfl⟩` from `(hK _).1 m₂`. Take `⟨γ, ⟨hγ, h⟩, hu⟩` from `h2 _ ⟨l₁, g₁, l₂, g₂, rfl⟩`.

Rewrite using `[← map_mul, ← map_mul]`. Use `⟨ι γ, ⟨Finset.mem_image_of_mem _ hγ, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_inv, ← map_mul]`. Conclude with `(hK' _).2 h`. Introduce and unpack `z ⟨hz, h'⟩`.

Take `⟨y, hy, rfl⟩` from `Finset.mem_image.1 hz`. Rewrite `h'` using `[← map_inv, ← map_mul]`. Rewrite using `[hu y ⟨hy, (hK' _).1 h'⟩]`.
-/
theorem rep_image {G H : Type} [Group G] [Group H] [DecidableEq G] (ι : H →* G) (hι : Function.Injective ι)
    {K : Subgroup H} {KS : Set G} (hK : ∀ g, g ∈ KS ↔ ∃ k ∈ K, ι k = g) {a : H} {R : Finset H}
    (h1 : ∀ γ ∈ R, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * a * k₂)
    (h2 : ∀ x, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * a * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ K) :
    (∀ γ ∈ R.image ι, ∃ k₁ ∈ KS, ∃ k₂ ∈ KS, γ = k₁ * ι a * k₂) ∧
      ∀ x, (∃ k₁ ∈ KS, ∃ k₂ ∈ KS, x = k₁ * ι a * k₂) → ∃! γ, γ ∈ R.image ι ∧ γ⁻¹ * x ∈ KS := by
  have hK' : ∀ k, ι k ∈ KS ↔ k ∈ K := fun k =>
    (hK _).trans ⟨fun ⟨k', h, e⟩ => hι e ▸ h, fun h => ⟨k, h, rfl⟩⟩
  constructor
  · intro γ hγ
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hγ
    obtain ⟨k₁, m₁, k₂, m₂, rfl⟩ := h1 y hy
    exact ⟨_, (hK' _).2 m₁, _, (hK' _).2 m₂, by rw [map_mul, map_mul]⟩
  · rintro _ ⟨k₁, m₁, k₂, m₂, rfl⟩
    obtain ⟨l₁, g₁, rfl⟩ := (hK _).1 m₁
    obtain ⟨l₂, g₂, rfl⟩ := (hK _).1 m₂
    obtain ⟨γ, ⟨hγ, h⟩, hu⟩ := h2 _ ⟨l₁, g₁, l₂, g₂, rfl⟩
    rw [← map_mul, ← map_mul]
    refine ⟨ι γ, ⟨Finset.mem_image_of_mem _ hγ, ?_⟩, ?_⟩
    · rw [← map_inv, ← map_mul]
      exact (hK' _).2 h
    · rintro z ⟨hz, h'⟩
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
      rw [← map_inv, ← map_mul] at h'
      rw [hu y ⟨hy, (hK' _).1 h'⟩]

section Component

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F) in

def compAt (w : HeightOneSpectrum (𝓞 E)) : Af F ⊗[F] E →+* w.adicCompletion E :=
  (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV E w).toRingHom.comp (finAdEquiv F E).toRingHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem compAt_apply (w : HeightOneSpectrum (𝓞 E)) (y : Af F ⊗[F] E) : compAt F w y = finAdEquiv F E y w := rfl

variable (F) in

def singleAt (w : HeightOneSpectrum (𝓞 E)) (x : w.adicCompletion E) : Af F ⊗[F] E :=
  (finAdEquiv F E).symm (singleFin w x)

/- English proof (translation)
The claim follows from `(finAdEquiv F E).injective (FiniteAdeleRing.ext _ h)`.
-/
theorem compAt_ext {y z : Af F ⊗[F] E} (h : ∀ w, compAt F w y = compAt F w z) : y = z :=
  (finAdEquiv F E).injective (FiniteAdeleRing.ext _ h)

/- English proof (translation)
Rewrite using `[compAt_apply, singleAt, RingEquiv.apply_symm_apply]`. Conclude with `evalV_singleFin_self w x`.
-/
theorem compAt_singleAt (w : HeightOneSpectrum (𝓞 E)) (x : w.adicCompletion E) :
    compAt F w (singleAt F w x) = x := by
  rw [compAt_apply, singleAt, RingEquiv.apply_symm_apply]
  exact evalV_singleFin_self w x

/- English proof (translation)
Rewrite using `[compAt_apply, singleAt, RingEquiv.apply_symm_apply]`. Conclude with `evalV_singleFin_ne h x`.
-/
theorem compAt_singleAt_ne {w u : HeightOneSpectrum (𝓞 E)} (h : u ≠ w) (x : w.adicCompletion E) :
    compAt F u (singleAt F w x) = 0 := by
  rw [compAt_apply, singleAt, RingEquiv.apply_symm_apply]
  exact evalV_singleFin_ne h x

/- English proof (translation)
The claim follows from `compAt_ext fun u => by by_cases e : u = w · subst e; simp only [map_mul, compAt_singleAt] · simp only [map_mul, compAt_singleAt_ne e, zero_mul]`.
-/
theorem singleAt_mul (w : HeightOneSpectrum (𝓞 E)) (x : w.adicCompletion E) (y : Af F ⊗[F] E) :
    singleAt F w x * y = singleAt F w (x * compAt F w y) := compAt_ext fun u => by
  by_cases e : u = w
  · subst e; simp only [map_mul, compAt_singleAt]
  · simp only [map_mul, compAt_singleAt_ne e, zero_mul]

/- English proof (translation)
Simplify using `only [singleAt, map_add]`.
-/
theorem singleAt_add (w : HeightOneSpectrum (𝓞 E)) (x y : w.adicCompletion E) :
    singleAt F w (x + y) = singleAt F w x + singleAt F w y := by simp only [singleAt, map_add]

/- English proof (translation)
Simplify using `only [singleAt, map_zero]`.
-/
theorem singleAt_zero (w : HeightOneSpectrum (𝓞 E)) : singleAt F w 0 = 0 := by simp only [singleAt, map_zero]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem compAt_tmul (w : HeightOneSpectrum (𝓞 E)) (a : Af F) (x : E) :
    compAt F w (a ⊗ₜ[F] x) = GlobalTheory.AdeleBaseChange.locMap F w (a (w.under (𝓞 F))) * algebraMap E _ x := rfl

/- English proof (translation)
Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨a, ha, x, hx, rfl⟩` from `hy`. Conclude with `(latAt w L).smul_mem ⟨_, GlobalTheory.AdeleBaseChange.locMap_int w _ (ha _)⟩ (Submodule.subset_span ⟨x, hx, rfl⟩)`. Consider the case `zero => simp only [Pi.zero_apply, map_zero]`.

Conclude with `zero_mem _`. Consider the case `add y z _ _ hy hz => simp only [Pi.add_apply, map_add]`. Conclude with `add_mem hy hz`. Consider the case `neg y _ hy => simp only [Pi.neg_apply, map_neg]`. Conclude with `neg_mem hy`.
-/
theorem compAt_mem_latAt {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)} (w : HeightOneSpectrum (𝓞 E))
    {y : Fin n → Af F ⊗[F] E} (hy : y ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E))) :
    (fun i => compAt F w (y i)) ∈ latAt w L := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    exact (latAt w L).smul_mem ⟨_, GlobalTheory.AdeleBaseChange.locMap_int w _ (ha _)⟩ (Submodule.subset_span ⟨x, hx, rfl⟩)
  | zero => simp only [Pi.zero_apply, map_zero]; exact zero_mem _
  | add y z _ _ hy hz => simp only [Pi.add_apply, map_add]; exact add_mem hy hz
  | neg y _ hy => simp only [Pi.neg_apply, map_neg]; exact neg_mem hy

/- English proof (translation)
Rewrite using `[← projFinLoc_projFin]`. Conclude with `Matrix.ext fun i j => finAdEquiv_apply h _`.
-/
theorem finMat_map_compAt (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {v : HeightOneSpectrum (𝓞 F)}
    {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = v) (g : GAd σ J) :
    (Formalism.MainNotions.StandardLattice.finMat σ J g).map (compAt F w) = (locMat σ J h (proj σ J v g)).1 := by
  rw [← projFinLoc_projFin]
  exact Matrix.ext fun i j => finAdEquiv_apply h _

end Component

section Record

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult Formalism.MainNotions.StandardLattice

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}

/- English proof (translation)
Set `c` to `(Algebra.TensorProduct.comm D.host.F D.host.E (Af D.host.F)).toRingEquiv`. Establish `hι : ∀ x a, ((toFinAd D.host.F D.host.E).comp c.toRingHom) (x ⊗ₜ[D.host.F] a) = algebraMap D.host.E _ x * GlobalTheory.AdeleBaseChange.adMap D.host.F D.host.E a` using `fun x a => (toFinAd_tmul a x).trans (mul_comm _ _)`. Establish `e : ((toFinAd D.host.F D.host.E).comp c.toRingHom) (Formalism.IndefR.Lev.swapAE D z) = toFinAd D.host.F D.host.E z` using `congrArg (toFinAd D.host.F D.host.E) (c.apply_symm_apply z)`. Rewrite using `[GlobalTheory.IdemSupport.mem_intAE_iff]`. Use `⟨fun h => ?_, fun h => GlobalTheory.AdeleBaseChange.mem_int_of_map hι ?_⟩` and prove the remaining obligations.

Use `GlobalTheory.AdeleBaseChange.map_mem_int hι h` as an intermediate fact. Rewrite `this` using `[e]`. Conclude with `this`. Rewrite using `[e]`. Conclude with `h`.
-/
theorem mem_intAE_iff_compAt (z : Af D.host.F ⊗[D.host.F] D.host.E) :
    z ∈ intAE D ↔ ∀ u, compAt D.host.F u z ∈ Ov D.host.E u := by
  let c := (Algebra.TensorProduct.comm D.host.F D.host.E (Af D.host.F)).toRingEquiv
  have hι : ∀ x a, ((toFinAd D.host.F D.host.E).comp c.toRingHom) (x ⊗ₜ[D.host.F] a) =
      algebraMap D.host.E _ x * GlobalTheory.AdeleBaseChange.adMap D.host.F D.host.E a :=
    fun x a => (toFinAd_tmul a x).trans (mul_comm _ _)
  have e : ((toFinAd D.host.F D.host.E).comp c.toRingHom) (Formalism.IndefR.Lev.swapAE D z) = toFinAd D.host.F D.host.E z :=
    congrArg (toFinAd D.host.F D.host.E) (c.apply_symm_apply z)
  rw [GlobalTheory.IdemSupport.mem_intAE_iff]
  refine ⟨fun h => ?_, fun h => GlobalTheory.AdeleBaseChange.mem_int_of_map hι ?_⟩
  · have := GlobalTheory.AdeleBaseChange.map_mem_int hι h
    rw [e] at this
    exact this
  · rw [e]
    exact h

/- English proof (translation)
Take `⟨e, he, -⟩` from `GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E`. Establish `he1 : ∀ z, (e z).1 = infPart D z` using `fun z => (he z).1`. Establish `he2 : ∀ z, (e z).2 = finPart D z` using `fun z => (he z).2`. Use `⟨fun z h1 h2 => ?_, fun s => ?_, fun x => ?_, fun z => mem_intAE_iff_compAt _, fun a Q => ?_⟩` and prove the remaining obligations. Establish `h3 : finPart D z = 0` using `toFinAd_bijective.1 (h2.trans (map_zero _).symm)`.

Apply `e.injective` to reduce the goal to its premises. Rewrite using `[map_zero]`. Conclude with `Prod.ext ((he1 z).trans h1) ((he2 z).trans h3)`. Take `⟨y, rfl⟩` from `(toFinAd_bijective (F := D.host.F)).2 s`. Take `⟨z, hz⟩` from `e.surjective (0, y)`.

Use `⟨z, by rw [← he1, hz], ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, ← he2, hz]`. Express the relevant statement in the definitionally equal form `toFinAd D.host.F D.host.E ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = _`. Rewrite using `[toFinAd_tmul, map_one, one_mul]`. Express the relevant statement in the definitionally equal form `toFinAd D.host.F D.host.E (a.2 ⊗ₜ[D.host.F] (1 : D.host.E)) Q = _`.

Rewrite using `[toFinAd_tmul, map_one, mul_one]`. Both sides reduce to the same expression.
-/
theorem comp_finAdEquiv (D : D7) :
    GlobalTheory.IdemSupport.Comp D ((toFinAd D.host.F D.host.E).comp (finPart D)) := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have he1 : ∀ z, (e z).1 = infPart D z := fun z => (he z).1
  have he2 : ∀ z, (e z).2 = finPart D z := fun z => (he z).2
  refine ⟨fun z h1 h2 => ?_, fun s => ?_, fun x => ?_, fun z => mem_intAE_iff_compAt _, fun a Q => ?_⟩
  · have h3 : finPart D z = 0 := toFinAd_bijective.1 (h2.trans (map_zero _).symm)
    apply e.injective
    rw [map_zero]
    exact Prod.ext ((he1 z).trans h1) ((he2 z).trans h3)
  · obtain ⟨y, rfl⟩ := (toFinAd_bijective (F := D.host.F)).2 s
    obtain ⟨z, hz⟩ := e.surjective (0, y)
    refine ⟨z, by rw [← he1, hz], ?_⟩
    rw [RingHom.comp_apply, ← he2, hz]
  · change toFinAd D.host.F D.host.E ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = _
    rw [toFinAd_tmul, map_one, one_mul]
  · change toFinAd D.host.F D.host.E (a.2 ⊗ₜ[D.host.F] (1 : D.host.E)) Q = _
    rw [toFinAd_tmul, map_one, mul_one]
    rfl

/- English proof (translation)
Take `⟨⟨-, h1, h2⟩, -⟩` from `GlobalTheory.IdemSupport.of_isPrimeIdem (comp_finAdEquiv D) h`. Use `compAt_ext fun u => ?_` and prove the remaining obligations. Distinguish the cases in `e : u = w`. Substitute `e` using the available equality. Rewrite using `[compAt_singleAt]`.

Conclude with `h1`. Rewrite using `[compAt_singleAt_ne e]`. Conclude with `h2 u e`.
-/
theorem finPart_of_isPrimeIdem {e f : AE D} (h : IsPrimeIdem w e f) : finPart D e = singleAt D.host.F w 1 := by
  obtain ⟨⟨-, h1, h2⟩, -⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem (comp_finAdEquiv D) h
  refine compAt_ext fun u => ?_
  by_cases e : u = w
  · subst e; rw [compAt_singleAt]; exact h1
  · rw [compAt_singleAt_ne e]; exact h2 u e

/- English proof (translation)
The claim follows from `(mem_intAE_iff_compAt _).2 fun u => by by_cases e : u = w · subst e; rwa [compAt_singleAt] · rw [compAt_singleAt_ne e]; exact zero_mem _`.
-/
theorem singleAt_mem_intAE {x : w.adicCompletion D.host.E} (hx : x ∈ Ov D.host.E w) :
    singleAt D.host.F w x ∈ intAE D := (mem_intAE_iff_compAt _).2 fun u => by
  by_cases e : u = w
  · subst e; rwa [compAt_singleAt]
  · rw [compAt_singleAt_ne e]; exact zero_mem _

/- English proof (translation)
The claim follows from `congrArg (fun y : FiniteAdeleRing (𝓞 D.host.E) D.host.E => y w) ((comp_finAdEquiv D).inc x)`.
-/
theorem compAt_incA (x : D.host.E) : compAt D.host.F w (finPart D (incA D x)) = algebraMap D.host.E _ x :=
  congrArg (fun y : FiniteAdeleRing (𝓞 D.host.E) D.host.E => y w) ((comp_finAdEquiv D).inc x)

/- English proof (translation)
Establish `hm` using `(GlobalTheory.LatDual.lamHat_selfDual_and_module V).2`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨z, hz, rfl⟩` from `hx`. Establish `h1 : (fun i => finPart D (incA D (z i))) ∈ LamHat V` using `AddSubgroup.subset_closure ⟨1, fun u => by rw [map_one]; exact one_mem _, z, (hermitianSpaceBaseLattice_eq_frameLattice V).ge hz, rfl⟩`.

Simplify `hm _ (singleAt_mem_intAE (w := w) (one_mem _)) _ h1` using `only [singleAt_mul, compAt_incA, one_mul]`. Consider the case `zero => simp only [Pi.zero_apply, singleAt_zero]`. Conclude with `zero_mem _`. Consider the case `add a b _ _ ha hb => simp only [Pi.add_apply, singleAt_add]`. Conclude with `add_mem ha hb`.

Consider the case `smul a b _ hb`. Use `hm _ (singleAt_mem_intAE a.2) _ hb` as an intermediate fact. Simplify using `only [singleAt_mul, compAt_singleAt] at this`. Conclude with `this`.
-/
theorem singleAt_mem_lamHat {x : Fin V.rank → w.adicCompletion D.host.E} (hx : x ∈ latAt w (frameLat V)) :
    (fun i => singleAt D.host.F w (x i)) ∈ LamHat V := by
  have hm := (GlobalTheory.LatDual.lamHat_selfDual_and_module V).2
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    have h1 : (fun i => finPart D (incA D (z i))) ∈ LamHat V :=
      AddSubgroup.subset_closure ⟨1, fun u => by rw [map_one]; exact one_mem _, z, (hermitianSpaceBaseLattice_eq_frameLattice V).ge hz, rfl⟩
    simpa only [singleAt_mul, compAt_incA, one_mul] using hm _ (singleAt_mem_intAE (w := w) (one_mem _)) _ h1
  | zero => simp only [Pi.zero_apply, singleAt_zero]; exact zero_mem _
  | add a b _ _ ha hb => simp only [Pi.add_apply, singleAt_add]; exact add_mem ha hb
  | smul a b _ hb =>
    have := hm _ (singleAt_mem_intAE a.2) _ hb
    simp only [singleAt_mul, compAt_singleAt] at this
    exact this

/- English proof (translation)
Establish `hϖ : Valued.v (algebraMap D.host.E (w.adicCompletion D.host.E) (ϖ : D.host.E)) = WithZero.exp (-1 : ℤ)`. Establish `a1` using `(w.intValuation_le_pow_iff_mem ϖ 1).2 (by simpa using h1)`. Establish `a2` using `mt (w.intValuation_le_pow_iff_mem ϖ 2).1 h2`. Establish `a3 : w.intValuation ϖ ≠ 0` using `w.intValuation_ne_zero ϖ fun h => h2 (h ▸ zero_mem _)`. Rewrite using `[Formalism.UG.P.levelaf_valued_algebraMap, show w.valuation D.host.E (ϖ : D.host.E) = w.intValuation ϖ from w.valuation_of_algebraMap ϖ]`.

Rewrite `a1`, `a2` using `[← WithZero.exp_log a3, WithZero.exp_le_exp]`. Rewrite using `[← WithZero.exp_log a3]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Establish `ht : ∀ i : Fin V.rank, Valued.v (compAt D.host.F w (finPart D (incA D ((ϖ : D.host.E) ^ (List.ofFn d).getD i.1 0)))) = Valued.v (u i)` using `fun i => by`.

Rewrite using `[compAt_incA, map_zpow₀, map_zpow₀, hϖ, hu, ← WithZero.exp_zsmul]`. Simplify using `[List.getD_eq_getElem?_getD]`. Establish `hq : ∀ x y : w.adicCompletion D.host.E, Valued.v x = Valued.v y → ∃ r ∈ Ov D.host.E w, x = y * r` using `fun x y e => by`. Distinguish the cases in `h0 : y = 0`. Rewrite `e` using `[h0, map_zero, map_eq_zero]`.

Conclude with `⟨0, zero_mem _, by rw [e, mul_zero]⟩`. Use `⟨x / y, ?_, (mul_div_cancel₀ x h0).symm⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Valued.v (x / y) ≤ 1`. Rewrite using `[map_div₀, e, div_self ((map_ne_zero _).2 h0)]`. Use `⟨List.length_ofFn, div_of_component (compAt D.host.F w) (singleAt D.host.F w) (compAt_singleAt w) (fun y => by rw [finPart_of_isPrimeIdem hef, singleAt_mul, one_mul]) (I := (· ∈ intAE D)) (O := Ov D.host.E w) (fun y hy => (mem_intAE_iff_compAt y).1 hy w) (fun x => singleAt_mem_in …` and prove the remaining obligations.

Rewrite using `[Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`. Conclude with `compAt_mem_latAt w (hermitianSpaceBaseLattice_eq_frameLattice V ▸ hy)`. Rewrite using `[finMat_map_compAt _ _ h, ← hg, ← Units.val_mul, ← Units.val_mul]`. Use `congr 1`. Use `group`.
-/
theorem divAt_of_diagonal (h : w.under (𝓞 D.host.F) = v) {e f : AE D} (hef : IsPrimeIdem w e f) {ϖ : 𝓞 D.host.E}
    (h1 : ϖ ∈ w.asIdeal) (h2 : ϖ ∉ w.asIdeal ^ 2) {a : GL (Fin V.rank) (w.adicCompletion D.host.E)}
    (ha : IsFrameAt w (frameLat V) a) {g : GA D V} {d : Fin V.rank → ℤ} {u : Fin V.rank → w.adicCompletion D.host.E}
    (hu : ∀ i, Valued.v (u i) = WithZero.exp (-d i))
    (hg : (a⁻¹ * locMat D.sp.cm.sig V.gram h (proj D.sp.cm.sig V.gram v g) * a).1 = Matrix.diagonal u) :
    DivAt V e (ϖ : D.host.E) (List.ofFn d) g := by
  have hϖ : Valued.v (algebraMap D.host.E (w.adicCompletion D.host.E) (ϖ : D.host.E)) = WithZero.exp (-1 : ℤ) := by
    have a1 := (w.intValuation_le_pow_iff_mem ϖ 1).2 (by simpa using h1)
    have a2 := mt (w.intValuation_le_pow_iff_mem ϖ 2).1 h2
    have a3 : w.intValuation ϖ ≠ 0 := w.intValuation_ne_zero ϖ fun h => h2 (h ▸ zero_mem _)
    rw [Formalism.UG.P.levelaf_valued_algebraMap, show w.valuation D.host.E (ϖ : D.host.E) = w.intValuation ϖ from
      w.valuation_of_algebraMap ϖ]
    rw [← WithZero.exp_log a3, WithZero.exp_le_exp] at a1 a2
    rw [← WithZero.exp_log a3]
    congr 1
    omega
  have ht : ∀ i : Fin V.rank, Valued.v (compAt D.host.F w (finPart D (incA D
      ((ϖ : D.host.E) ^ (List.ofFn d).getD i.1 0)))) = Valued.v (u i) := fun i => by
    rw [compAt_incA, map_zpow₀, map_zpow₀, hϖ, hu, ← WithZero.exp_zsmul]
    simp [List.getD_eq_getElem?_getD]
  have hq : ∀ x y : w.adicCompletion D.host.E, Valued.v x = Valued.v y → ∃ r ∈ Ov D.host.E w, x = y * r :=
    fun x y e => by
      by_cases h0 : y = 0
      · rw [h0, map_zero, map_eq_zero] at e
        exact ⟨0, zero_mem _, by rw [e, mul_zero]⟩
      · refine ⟨x / y, ?_, (mul_div_cancel₀ x h0).symm⟩
        change Valued.v (x / y) ≤ 1
        rw [map_div₀, e, div_self ((map_ne_zero _).2 h0)]
  refine ⟨List.length_ofFn, div_of_component (compAt D.host.F w) (singleAt D.host.F w) (compAt_singleAt w)
    (fun y => by rw [finPart_of_isPrimeIdem hef, singleAt_mul, one_mul]) (I := (· ∈ intAE D)) (O := Ov D.host.E w)
    (fun y hy => (mem_intAE_iff_compAt y).1 hy w) (fun x => singleAt_mem_intAE) (Λ := (· ∈ LamHat V)) a
    (fun y hy => (ha _).2 ?_) (fun x hx => singleAt_mem_lamHat ((ha x).1 hx)) (u := u) ?_
    (fun i => hq _ _ (ht i).symm) fun i => hq _ _ (ht i)⟩
  · rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    exact compAt_mem_latAt w (hermitianSpaceBaseLattice_eq_frameLattice V ▸ hy)
  · rw [finMat_map_compAt _ _ h, ← hg, ← Units.val_mul, ← Units.val_mul]
    congr 1
    group

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h hw`. Take `⟨x, hx, hy⟩` from `h _ hw`. Conclude with `hy (algebraMap _ _ x) rfl hx`. Introduce `h u hu`.

Establish `: ¬ u.asIdeal ≤ (w.under (𝓞 D.host.F)).asIdeal` using `fun hle => h (HeightOneSpectrum.ext (u.isMaximal.eq_of_le (w.under _).isPrime.ne_top hle) ▸ hu)`. Take `⟨x, hx, hx'⟩` from `SetLike.not_le_iff_exists.1 this`. Use `⟨x, hx, fun y hy hw => hx' ?_⟩` and prove the remaining obligations. Take `rfl : y = algebraMap _ _ x` from `RingOfIntegers.ext hy`. Conclude with `hw`.
-/
theorem offS_iff {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} : OffS D S w ↔ w.under (𝓞 D.host.F) ∉ S := by
  constructor
  · intro h hw
    obtain ⟨x, hx, hy⟩ := h _ hw
    exact hy (algebraMap _ _ x) rfl hx
  · intro h u hu
    have : ¬ u.asIdeal ≤ (w.under (𝓞 D.host.F)).asIdeal := fun hle =>
      h (HeightOneSpectrum.ext (u.isMaximal.eq_of_le (w.under _).isPrime.ne_top hle) ▸ hu)
    obtain ⟨x, hx, hx'⟩ := SetLike.not_le_iff_exists.1 this
    refine ⟨x, hx, fun y hy hw => hx' ?_⟩
    obtain rfl : y = algebraMap _ _ x := RingOfIntegers.ext hy
    exact hw

variable {J : Set (GA D V)} {χ : GA D V → ℂ} {S : Finset (HeightOneSpectrum (𝓞 D.host.F))}

/- English proof (translation)
Establish `hS : OffS D S w` using `offS_iff.2 (h ▸ hv)`. Take `⟨e, f, hef, h1, h2⟩` from `hJ w hS`. Take `⟨ϖ, p1, p2⟩ : ∃ ϖ ∈ w.asIdeal, ϖ ∉ w.asIdeal ^ 2` from `SetLike.exists_of_lt (Ideal.pow_lt_self w.asIdeal w.ne_bot w.isPrime.ne_top 2 le_rfl)`. Use `GlobalTheory.HeckeDual.isLattice_frameLat V` as an intermediate fact. Take `⟨R, r1, r2⟩` from `GlobalTheory.HeckeDual.exists_rep _ (isOpen_stabLoc D.sp.cm.sig V.gram (frameLat V) v) (isCompact_stabLoc D.sp.cm.sig V.gram (frameLat V) v) g`.

Establish `hs` using `Supp.suppF_iff_of_isPrimeIdem V hef h`. Establish `hK : ∀ x, x ∈ {k | k ∈ J ∧ SuppF V f k} ↔ ∃ k ∈ stabLoc D.sp.cm.sig V.gram (frameLat V) v, emb D.sp.cm.sig V.gram v k = x` using `fun x => by`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m1, m2⟩`. Take `⟨k, rfl⟩` from `(hs x).1 m2`.

Conclude with `⟨k, (Supp.emb_mem_KsphC V k).1 ((h1 _ m2).1 m1), rfl⟩`. Introduce and unpack `⟨k, hk, rfl⟩`. Use `(hs _).2 ⟨k, rfl⟩` as an intermediate fact. Conclude with `⟨(h1 _ this).2 ((Supp.emb_mem_KsphC V k).2 hk), this⟩`. Take `⟨s1, s2⟩` from `rep_image (emb D.sp.cm.sig V.gram v) (emb_injective _ _ v) hK r1 r2`.

Use `⟨R.image (emb D.sp.cm.sig V.gram v), ⟨e, f, ϖ, emb D.sp.cm.sig V.gram v g, hS, hef, p1, p2, List.pairwise_ofFn.2 fun i j hij => hd hij.le, h1, h2, (hs _).2 ⟨g, rfl⟩, divAt_of_diagonal h hef p1 p2 ha hu (by rw [proj_emb_self, hg]), fun γ hγ => ?_, fun γ hγ => ⟨?_, s1 γ hγ⟩, s2⟩, f …` and prove the remaining obligations. Take `⟨y, -, rfl⟩` from `Finset.mem_image.1 hγ`. Conclude with `(hs _).2 ⟨y, rfl⟩`. Take `⟨y, -, rfl⟩` from `Finset.mem_image.1 hγ`. Conclude with `mem_finPts.2 (projInf_emb _ _ v y)`.

Rewrite using `[heckeVec_dosetInd hφ (R := R) (fun γ hγ => DoubleCoset.mem_doubleCoset.2 (r1 γ hγ)) fun x hx => r2 x (DoubleCoset.mem_doubleCoset.1 hx)]`. Use function extensionality and compare the values at `x`. Rewrite using `[heckeLin_apply, Finset.sum_image (emb_injective _ _ v).injOn, Finset.sum_apply]`. Both sides reduce to the same expression.
-/
theorem exists_isHeckeOpFull (hJ : SphOff J χ S) (hv : v ∉ S) (h : w.under (𝓞 D.host.F) = v)
    {a : GL (Fin V.rank) (w.adicCompletion D.host.E)} (ha : IsFrameAt w (frameLat V) a)
    {g : GLoc D.sp.cm.sig V.gram v} {d : Fin V.rank → ℤ} (hd : Antitone d)
    {u : Fin V.rank → w.adicCompletion D.host.E} (hu : ∀ i, Valued.v (u i) = WithZero.exp (-d i))
    (hg : (a⁻¹ * locMat D.sp.cm.sig V.gram h g * a).1 = Matrix.diagonal u) :
    ∃ R, Hecke₂ V J χ S w (List.ofFn d) R ∧ ∀ φ : GA D V → ℂ,
      φ ∈ fixed ((rightReg ℂ _ ℂ).comp (emb D.sp.cm.sig V.gram v)) (stabLoc D.sp.cm.sig V.gram (frameLat V) v) →
      heckeLin V R φ = heckeVec ((rightReg ℂ _ ℂ).comp (emb D.sp.cm.sig V.gram v))
        (stabLoc D.sp.cm.sig V.gram (frameLat V) v) (dosetInd ℂ (stabLoc D.sp.cm.sig V.gram (frameLat V) v) g) φ := by
  classical
  have hS : OffS D S w := offS_iff.2 (h ▸ hv)
  obtain ⟨e, f, hef, h1, h2⟩ := hJ w hS
  obtain ⟨ϖ, p1, p2⟩ : ∃ ϖ ∈ w.asIdeal, ϖ ∉ w.asIdeal ^ 2 :=
    SetLike.exists_of_lt (Ideal.pow_lt_self w.asIdeal w.ne_bot w.isPrime.ne_top 2 le_rfl)
  have := GlobalTheory.HeckeDual.isLattice_frameLat V
  obtain ⟨R, r1, r2⟩ := GlobalTheory.HeckeDual.exists_rep _ (isOpen_stabLoc D.sp.cm.sig V.gram (frameLat V) v)
    (isCompact_stabLoc D.sp.cm.sig V.gram (frameLat V) v) g
  have hs := Supp.suppF_iff_of_isPrimeIdem V hef h
  have hK : ∀ x, x ∈ {k | k ∈ J ∧ SuppF V f k} ↔
      ∃ k ∈ stabLoc D.sp.cm.sig V.gram (frameLat V) v, emb D.sp.cm.sig V.gram v k = x := fun x => by
    constructor
    · rintro ⟨m1, m2⟩
      obtain ⟨k, rfl⟩ := (hs x).1 m2
      exact ⟨k, (Supp.emb_mem_KsphC V k).1 ((h1 _ m2).1 m1), rfl⟩
    · rintro ⟨k, hk, rfl⟩
      have := (hs _).2 ⟨k, rfl⟩
      exact ⟨(h1 _ this).2 ((Supp.emb_mem_KsphC V k).2 hk), this⟩
  obtain ⟨s1, s2⟩ := rep_image (emb D.sp.cm.sig V.gram v) (emb_injective _ _ v) hK r1 r2
  refine ⟨R.image (emb D.sp.cm.sig V.gram v), ⟨e, f, ϖ, emb D.sp.cm.sig V.gram v g, hS, hef, p1, p2,
    List.pairwise_ofFn.2 fun i j hij => hd hij.le, h1, h2, (hs _).2 ⟨g, rfl⟩,
    divAt_of_diagonal h hef p1 p2 ha hu (by rw [proj_emb_self, hg]), fun γ hγ => ?_, fun γ hγ => ⟨?_, s1 γ hγ⟩, s2⟩,
    fun φ hφ => ?_⟩
  · obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hγ
    exact (hs _).2 ⟨y, rfl⟩
  · obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hγ
    exact mem_finPts.2 (projInf_emb _ _ v y)
  · rw [heckeVec_dosetInd hφ (R := R) (fun γ hγ => DoubleCoset.mem_doubleCoset.2 (r1 γ hγ))
      fun x hx => r2 x (DoubleCoset.mem_doubleCoset.1 hx)]
    funext x
    rw [heckeLin_apply, Finset.sum_image (emb_injective _ _ v).injOn, Finset.sum_apply]
    rfl

/- English proof (translation)
Introduce `a g d u ha hd hu hg`. Take `⟨R, h1, h2⟩` from `exists_isHeckeOpFull hJ hv h ha hd hu hg`. Rewrite using `[← h2 φ hφ, hc _ R h1]`.
-/
theorem isEigenSys_of_heckeLin (hJ : SphOff J χ S) (hv : v ∉ S) (h : w.under (𝓞 D.host.F) = v) {φ : GA D V → ℂ}
    (hφ : φ ∈ fixed ((rightReg ℂ _ ℂ).comp (emb D.sp.cm.sig V.gram v)) (stabLoc D.sp.cm.sig V.gram (frameLat V) v))
    {c : List ℤ → ℂ} (hc : ∀ d R, Hecke₂ V J χ S w d R → heckeLin V R φ = c d • φ) :
    IsEigenSys D.sp.cm.sig V.gram (frameLat V) h ((rightReg ℂ _ ℂ).comp (emb D.sp.cm.sig V.gram v)) φ c := by
  intro a g d u ha hd hu hg
  obtain ⟨R, h1, h2⟩ := exists_isHeckeOpFull hJ hv h ha hd hu hg
  rw [← h2 φ hφ, hc _ R h1]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨w, h⟩ : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v := by`. Use `v.isMaximal` as an intermediate fact. Take `⟨Q, hQ, e⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal (by`. Rewrite using `[(RingHom.injective_iff_ker_eq_bot (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))).1 (FaithfulSMul.algebraMap_injective _ _)]`. Conclude with `bot_le)`.

Conclude with `⟨⟨Q, hQ.isPrime, fun h0 => v.ne_bot (by`. Rewrite using `[← e, h0, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)])⟩,`. Use the proof step `HeightOneSpectrum.ext e⟩`. Take `⟨e, f, hef, h1, h2⟩` from `hJ w (offS_iff.2 (h ▸ hv))`. Establish `hs` using `(Supp.suppF_iff_of_isPrimeIdem V hef h _).2 ⟨k, rfl⟩`.

Establish `hm` using `(h1 _ hs).2 ((Supp.emb_mem_KsphC V k).2 hk)`. Rewrite using `[hφ _ hm, h2 _ hm hs, one_mul]`.
-/
theorem fixed_of_level (hJ : SphOff J χ S) (hv : v ∉ S) {φ : GA D V → ℂ} (hφ : ∀ k ∈ J, ∀ g, φ (g * k) = χ k * φ g)
    {k : GLoc D.sp.cm.sig V.gram v} (hk : k ∈ stabLoc D.sp.cm.sig V.gram (frameLat V) v) (g : GA D V) :
    φ (g * emb D.sp.cm.sig V.gram v k) = φ g := by
  obtain ⟨w, h⟩ : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v := by
    have := v.isMaximal
    obtain ⟨Q, hQ, e⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal (by
      rw [(RingHom.injective_iff_ker_eq_bot (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))).1
        (FaithfulSMul.algebraMap_injective _ _)]; exact bot_le)
    exact ⟨⟨Q, hQ.isPrime, fun h0 => v.ne_bot (by
      rw [← e, h0, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)])⟩,
      HeightOneSpectrum.ext e⟩
  obtain ⟨e, f, hef, h1, h2⟩ := hJ w (offS_iff.2 (h ▸ hv))
  have hs := (Supp.suppF_iff_of_isPrimeIdem V hef h _).2 ⟨k, rfl⟩
  have hm := (h1 _ hs).2 ((Supp.emb_mem_KsphC V k).2 hk)
  rw [hφ _ hm, h2 _ hm hs, one_mul]

end Record

end GlobalTheory.LFun

end
