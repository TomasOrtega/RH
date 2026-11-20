import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Formalism.LocalToGlobal.Columns.XtPhiTopGCongr
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsApprox
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicLatticeCompletionLocalGlobal
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemStabGLAdeleIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MulVecMemLocLatIffOfFrame
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SplittingProjection
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitB
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImportsTer
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TwV.AwayLat

section Gen

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Introduce and unpack `x ⟨s, hs, hx⟩`. Conclude with `⟨s, hs, h hx⟩`.
-/
theorem localization_mono {W : Type} [AddCommGroup W] [Module (𝓞 E) W] (p : Ideal (𝓞 E)) [p.IsPrime]
    {L N : Submodule (𝓞 E) W} (h : L ≤ N) : Formalism.HermitianLatticesTheory.localization₂ p L ≤ Formalism.HermitianLatticesTheory.localization₂ p N := by
  rintro x ⟨s, hs, hx⟩
  exact ⟨s, hs, h hx⟩

/- English proof (translation)
Introduce `x hx` and use `⟨1, p.primeCompl.one_mem, by simpa using hx⟩`.
-/
theorem le_localized_self {W : Type} [AddCommGroup W] [Module (𝓞 E) W] (p : Ideal (𝓞 E)) [p.IsPrime]
    (L : Submodule (𝓞 E) W) : L ≤ Formalism.HermitianLatticesTheory.localization₂ p L := fun x hx =>
  ⟨1, p.primeCompl.one_mem, by simpa using hx⟩

/- English proof (translation)
Introduce and unpack `x ⟨s, hs, hx⟩`. Take `⟨t, ht, hx'⟩` from `h hx`. Conclude with `⟨t * s, p.primeCompl.mul_mem ht hs, by rw [mul_smul]; exact hx'⟩`.
-/
theorem localization_le_of_le_localization₂ {W : Type} [AddCommGroup W] [Module (𝓞 E) W] (p : Ideal (𝓞 E)) [p.IsPrime]
    {L N : Submodule (𝓞 E) W} (h : L ≤ Formalism.HermitianLatticesTheory.localization₂ p N) : Formalism.HermitianLatticesTheory.localization₂ p L ≤ Formalism.HermitianLatticesTheory.localization₂ p N := by
  rintro x ⟨s, hs, hx⟩
  obtain ⟨t, ht, hx'⟩ := h hx
  exact ⟨t * s, p.primeCompl.mul_mem ht hs, by rw [mul_smul]; exact hx'⟩

/- English proof (translation)
Use `sup_le (hA.trans (localization_mono p le_sup_left)) ?_` and prove the remaining obligations. Use `Submodule.smul_le.2 fun r hr m hm => ?_` and prove the remaining obligations. Take `⟨s, hs, hsm⟩` from `hB hm`. Use `⟨s, hs, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_comm]`.

Conclude with `Submodule.mem_sup_right (Submodule.smul_mem_smul hr hsm)`.
-/
theorem sup_smul_le_locP {W : Type} [AddCommGroup W] [Module (𝓞 E) W] (p : Ideal (𝓞 E)) [p.IsPrime]
    (I : Ideal (𝓞 E)) {A A' B B' : Submodule (𝓞 E) W} (hA : A ≤ Formalism.HermitianLatticesTheory.localization₂ p A') (hB : B ≤ Formalism.HermitianLatticesTheory.localization₂ p B') :
    A ⊔ I • B ≤ Formalism.HermitianLatticesTheory.localization₂ p (A' ⊔ I • B') := by
  refine sup_le (hA.trans (localization_mono p le_sup_left)) ?_
  refine Submodule.smul_le.2 fun r hr m hm => ?_
  obtain ⟨s, hs, hsm⟩ := hB hm
  refine ⟨s, hs, ?_⟩
  rw [smul_comm]
  exact Submodule.mem_sup_right (Submodule.smul_mem_smul hr hsm)

/- English proof (translation)
Introduce and unpack `_ ⟨m, hm, rfl⟩`. Take `⟨s, hs, hsm⟩` from `h hm`. Conclude with `⟨s, hs, ⟨s • m, hsm, by simp⟩⟩`.
-/
theorem map_le_locP {n : ℕ} (p : Ideal (𝓞 E)) [p.IsPrime] (f : (Fin n → E) ≃ₗ[E] (Fin n → E))
    {M M' : Submodule (𝓞 E) (Fin n → E)} (h : M ≤ Formalism.HermitianLatticesTheory.localization₂ p M') :
    M.map ((f : (Fin n → E) →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) ≤
      Formalism.HermitianLatticesTheory.localization₂ p (M'.map ((f : (Fin n → E) →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E))) := by
  rintro _ ⟨m, hm, rfl⟩
  obtain ⟨s, hs, hsm⟩ := h hm
  exact ⟨s, hs, ⟨s • m, hsm, by simp⟩⟩

/- English proof (translation)
Simplify using `only [hform, Finset.mul_sum, Pi.smul_apply, Algebra.smul_def]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hform_smul_right {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (c : 𝓞 E) (x y : Fin n → E) :
    hform σ J x (c • y) = algebraMap (𝓞 E) E c * hform σ J x y := by
  simp only [hform, Finset.mul_sum, Pi.smul_apply, Algebra.smul_def]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Simplify using `only [hform, Finset.mul_sum, Pi.smul_apply, Algebra.smul_def, map_mul]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hform_smul_left {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (c : 𝓞 E) (x y : Fin n → E) :
    hform σ J (c • x) y = σ (algebraMap (𝓞 E) E c) * hform σ J x y := by
  simp only [hform, Finset.mul_sum, Pi.smul_apply, Algebra.smul_def, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Simplify using `only [hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]`.
-/
theorem hform_add_left {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (x x' y : Fin n → E) :
    hform σ J (x + x') y = hform σ J x y + hform σ J x' y := by
  simp only [hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[hform]`.
-/
theorem hform_zero_left {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (y : Fin n → E) :
    hform σ J 0 y = 0 := by
  simp [hform]

/- English proof (translation)
Introduce `y hy`. Take `⟨G, hG⟩` from `Module.Finite.iff_fg.1 hf`. Establish `ht : ∀ g ∈ G, ∃ t : 𝓞 E, t ∉ I' ∧ t • g ∈ Λ` using `fun g hg => by`. Take `⟨t, ht, htg⟩` from `h (hG ▸ Submodule.subset_span hg)`. Conclude with `⟨t, ht, htg⟩`.

Use `choose! t ht1 ht2 using ht`. Use `⟨∏ g ∈ G, e (t g), fun hmem => ?_, Submodule.subset_span ?_⟩` and prove the remaining obligations. Take `⟨g, hg, hgI⟩` from `(Ideal.IsPrime.prod_mem_iff (p := I)).1 hmem`. Conclude with `hI _ (ht1 g hg) hgI`. Introduce `z hz`.

Rewrite `hz` using `[← hG]`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem g hg`. Rewrite using `[hform_smul_right, ← Finset.mul_prod_erase G _ hg, map_mul, mul_assoc, ← he, mul_left_comm, ← hform_smul_left]`. Take `⟨r, hr⟩` from `hy _ (ht2 g hg)`.

Rewrite using `[← hr, ← map_mul]`. Conclude with `⟨_, rfl⟩`. Consider the case `zero => rw [hform_zero_left]`. Conclude with `⟨0, map_zero _⟩`. Consider the case `add x x' _ _ hx hx'`.

Take `⟨r, hr⟩` from `hx`. Take `⟨r', hr'⟩` from `hx'`. Rewrite using `[hform_add_left, ← hr, ← hr', ← map_add]`. Conclude with `⟨_, rfl⟩`. Consider the case `smul c x _ hx`.

Take `⟨r, hr⟩` from `hx`. Rewrite using `[hform_smul_left, he, ← hr, ← map_mul]`. Conclude with `⟨_, rfl⟩`.
-/
theorem dualSet_le_locP {n : ℕ} (σ : E →+* E) (e : 𝓞 E ≃+* 𝓞 E)
    (he : ∀ t : 𝓞 E, σ (algebraMap (𝓞 E) E t) = algebraMap (𝓞 E) E (e t))
    (J : Matrix (Fin n) (Fin n) E) {Λ Λ' : Submodule (𝓞 E) (Fin n → E)} (hf : Module.Finite (𝓞 E) Λ')
    (I I' : Ideal (𝓞 E)) [I.IsPrime] [I'.IsPrime] (hI : ∀ t, t ∉ I' → e t ∉ I) (h : Λ' ≤ Formalism.HermitianLatticesTheory.localization₂ I' Λ) :
    Formalism.BasicNotions.dualSet σ J Λ ⊆ Formalism.HermitianLatticesTheory.localization₂ I (Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet σ J Λ')) := by
  classical
  intro y hy
  obtain ⟨G, hG⟩ := Module.Finite.iff_fg.1 hf
  have ht : ∀ g ∈ G, ∃ t : 𝓞 E, t ∉ I' ∧ t • g ∈ Λ := fun g hg => by
    obtain ⟨t, ht, htg⟩ := h (hG ▸ Submodule.subset_span hg)
    exact ⟨t, ht, htg⟩
  choose! t ht1 ht2 using ht
  refine ⟨∏ g ∈ G, e (t g), fun hmem => ?_, Submodule.subset_span ?_⟩
  · obtain ⟨g, hg, hgI⟩ := (Ideal.IsPrime.prod_mem_iff (p := I)).1 hmem
    exact hI _ (ht1 g hg) hgI
  · intro z hz
    rw [← hG] at hz
    induction hz using Submodule.span_induction with
    | mem g hg =>
      rw [hform_smul_right, ← Finset.mul_prod_erase G _ hg, map_mul, mul_assoc, ← he, mul_left_comm, ← hform_smul_left]
      obtain ⟨r, hr⟩ := hy _ (ht2 g hg)
      rw [← hr, ← map_mul]
      exact ⟨_, rfl⟩
    | zero => rw [hform_zero_left]; exact ⟨0, map_zero _⟩
    | add x x' _ _ hx hx' =>
      obtain ⟨r, hr⟩ := hx
      obtain ⟨r', hr'⟩ := hx'
      rw [hform_add_left, ← hr, ← hr', ← map_add]
      exact ⟨_, rfl⟩
    | smul c x _ hx =>
      obtain ⟨r, hr⟩ := hx
      rw [hform_smul_left, he, ← hr, ← map_mul]
      exact ⟨_, rfl⟩

end Gen

section SeamT

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] (iE : K ≃+* K') {m : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem algebraMap_mapRingEquiv (t : 𝓞 K) :
    algebraMap (𝓞 K') K' (RingOfIntegers.mapRingEquiv iE t) = iE (algebraMap (𝓞 K) K t) := rfl

/- English proof (translation)
Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz => obtain ⟨w, hw, rfl⟩ := hz`. Conclude with `⟨w, hw, rfl⟩`. Consider the case `zero => exact ⟨0, N.zero_mem, funext fun i => by simp⟩`. Consider the case `add z z' _ _ hz hz'`.

Take `⟨w, hw, rfl⟩` from `hz`. Take `⟨w', hw', rfl⟩` from `hz'`. Conclude with `⟨w + w', N.add_mem hw hw', funext fun i => by simp⟩`. Consider the case `smul c z _ hz`. Take `⟨w, hw, rfl⟩` from `hz`.

Use `⟨(RingOfIntegers.mapRingEquiv iE).symm c • w, N.smul_mem _ hw, funext fun i => ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, Algebra.smul_def, map_mul]`. Rewrite using `[← algebraMap_mapRingEquiv, RingEquiv.apply_symm_apply]`.
-/
theorem exists_of_mem_span_image (N : Submodule (𝓞 K) (Fin m → K)) (z : Fin m → K')
    (hz : z ∈ Submodule.span (𝓞 K') ((fun (x : Fin m → K) (i : Fin m) => iE (x i)) '' (N : Set (Fin m → K)))) :
    ∃ w ∈ N, (fun i => iE (w i)) = z := by
  induction hz using Submodule.span_induction with
  | mem z hz => obtain ⟨w, hw, rfl⟩ := hz; exact ⟨w, hw, rfl⟩
  | zero => exact ⟨0, N.zero_mem, funext fun i => by simp⟩
  | add z z' _ _ hz hz' =>
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨w', hw', rfl⟩ := hz'
    exact ⟨w + w', N.add_mem hw hw', funext fun i => by simp⟩
  | smul c z _ hz =>
    obtain ⟨w, hw, rfl⟩ := hz
    refine ⟨(RingOfIntegers.mapRingEquiv iE).symm c • w, N.smul_mem _ hw, funext fun i => ?_⟩
    simp only [Pi.smul_apply, Algebra.smul_def, map_mul]
    rw [← algebraMap_mapRingEquiv, RingEquiv.apply_symm_apply]

/- English proof (translation)
Simplify using `[HeightOneSpectrum.equivOfRingEquiv, HeightOneSpectrum.comap, Ideal.mem_comap]`.
-/
theorem mem_equivOfRingEquiv (P : HeightOneSpectrum (𝓞 K)) (t : 𝓞 K) :
    RingOfIntegers.mapRingEquiv iE t ∈ (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv iE) P).asIdeal ↔
      t ∈ P.asIdeal := by
  simp [HeightOneSpectrum.equivOfRingEquiv, HeightOneSpectrum.comap, Ideal.mem_comap]

/- English proof (translation)
Introduce `y hy`. Take `⟨c, hc, hcy⟩` from `h (Submodule.subset_span ⟨y, hy, rfl⟩)`. Take `⟨w, hw, hwz⟩` from `exists_of_mem_span_image iE N _ hcy`. Use `⟨(RingOfIntegers.mapRingEquiv iE).symm c, fun hP => hc ?_, ?_⟩` and prove the remaining obligations. Use `(mem_equivOfRingEquiv iE P _).2 hP` as an intermediate fact.

Rewrite `this` using `[RingEquiv.apply_symm_apply]`. Then use the resulting hypothesis. Use `hw using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Apply `iE.injective` to reduce the goal to its premises. Use `congrFun hwz i` as an intermediate fact.

Simplify using `only [Pi.smul_apply, Algebra.smul_def, map_mul] at this ⊢`. Rewrite using `[this, ← algebraMap_mapRingEquiv, RingEquiv.apply_symm_apply]`.
-/
theorem le_localized_of_transport (N N₁ : Submodule (𝓞 K) (Fin m → K)) (P : HeightOneSpectrum (𝓞 K))
    (h : Submodule.span (𝓞 K') ((fun (x : Fin m → K) (i : Fin m) => iE (x i)) '' (N₁ : Set (Fin m → K))) ≤
      Formalism.HermitianLatticesTheory.localization₂ (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv iE) P).asIdeal
        (Submodule.span (𝓞 K') ((fun (x : Fin m → K) (i : Fin m) => iE (x i)) '' (N : Set (Fin m → K))))) :
    N₁ ≤ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N := by
  intro y hy
  obtain ⟨c, hc, hcy⟩ := h (Submodule.subset_span ⟨y, hy, rfl⟩)
  obtain ⟨w, hw, hwz⟩ := exists_of_mem_span_image iE N _ hcy
  refine ⟨(RingOfIntegers.mapRingEquiv iE).symm c, fun hP => hc ?_, ?_⟩
  · have := (mem_equivOfRingEquiv iE P _).2 hP
    rwa [RingEquiv.apply_symm_apply] at this
  · convert hw using 1
    funext i
    apply iE.injective
    have := congrFun hwz i
    simp only [Pi.smul_apply, Algebra.smul_def, map_mul] at this ⊢
    rw [this, ← algebraMap_mapRingEquiv, RingEquiv.apply_symm_apply]

end SeamT

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.FiniteIndexSubgroup.target`. Consider the case `exact _root_.GlobalTheory.FiniteIndexSubgroup.target`. Consider the case `(apply _root_.GlobalTheory.FiniteIndexSubgroup.target <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.FiniteIndexSubgroup.target <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.FiniteIndexSubgroup.target <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.FiniteIndexSubgroup.target ..)`.
-/
theorem exists_smul_mem_of_span {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (y : Fin n → E) : ∃ ν : 𝓞 E, ν ≠ 0 ∧ ν • y ∈ L := by
  first
  | exact @_root_.GlobalTheory.FiniteIndexSubgroup.target
  | exact _root_.GlobalTheory.FiniteIndexSubgroup.target
  | (apply _root_.GlobalTheory.FiniteIndexSubgroup.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiniteIndexSubgroup.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiniteIndexSubgroup.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiniteIndexSubgroup.target ..)

section Loc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `i`. Rewrite using `[Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, map_mul, smul_eq_mul]`.
-/
theorem incl_smul (v : HeightOneSpectrum (𝓞 F)) (s : 𝓞 E) (x : Fin n → E) :
    (fun i => Formalism.UG.inclE (F := F) (v.adicCompletion F) ((s • x) i)) =
      Formalism.UG.inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E s) •
        fun i => Formalism.UG.inclE (F := F) (v.adicCompletion F) (x i) := by
  funext i
  rw [Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, map_mul, smul_eq_mul]

/- English proof (translation)
Introduce `F E _ _ _ _ _ n v B hB hs x hx q hq`. Take `⟨ν, hν, hνx⟩` from `exists_smul_mem_of_span B hs x`. Set `J : Ideal (𝓞 E)` to `B.comap (LinearMap.toSpanSingleton (𝓞 E) _ x)`. Establish `hJ : ∀ s, s ∈ J ↔ s • x ∈ B` using `fun s => Iff.rfl`. Establish `hJ0 : J.comap (algebraMap (𝓞 F) (𝓞 E)) ≠ ⊥`.

Introduce `h`. Use `Ideal.eq_bot_of_comap_eq_bot h` as an intermediate fact. Establish `h2 : ν ∈ J` using `hνx`. Rewrite `h2` using `[this]`. Conclude with `hν h2`.

Use `haveI := v.isMaximal`. Take `⟨Q, hQ, hI⟩` from `Ideal.eq_prime_pow_mul_coprime hJ0 v.asIdeal`. Choose the witnesses or unpack the hypotheses as in `⟨d, hdQ, hdv⟩ : ∃ d ∈ Q, d ∉ v.asIdeal := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Rewrite `hQ` using `[sup_eq_left.2 (show Q ≤ v.asIdeal from h)]`. Conclude with `v.isPrime.ne_top hQ`. Use `⟨algebraMap (𝓞 F) (𝓞 E) d, fun h => hdv (by rw [← hq]; exact h), ?_⟩` and prove the remaining obligations. Use `(GlobalTheory.LatLocGlob.latS_local_global F E n B hB).2.1 hs _ fun w => ?_` and prove the remaining obligations. Distinguish the cases in `hw : w = v`.

Substitute `hw` using the available equality. Rewrite using `[incl_smul]`. Conclude with `Submodule.smul_mem (GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat w B) (⟨_, Subring.subset_closure (Or.inl ⟨⟨_, ⟨algebraMap (𝓞 F) (𝓞 E) d, rfl⟩⟩, rfl⟩)⟩ : intV E w) hx`. Choose the witnesses or unpack the hypotheses as in `⟨π, hπ, hπw⟩ : ∃ π ∈ v.asIdeal ^ (UniqueFactorizationMonoid.normalizedFactors (J.comap (algebraMap (𝓞 F) (𝓞 E)))).count v.asIdeal, π ∉ w.asIdeal := by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Use `haveI := w.isPrime`. Establish `h1 : v.asIdeal ≤ w.asIdeal` using `Ideal.IsPrime.le_of_pow_le h`. Conclude with `hw (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top h1).symm)`. Establish `h1 : π * d ∈ J.comap (algebraMap (𝓞 F) (𝓞 E))`.

Rewrite using `[hI]`. Conclude with `Ideal.mul_mem_mul hπ hdQ`. Establish `h2 : algebraMap (𝓞 F) (𝓞 E) π • algebraMap (𝓞 F) (𝓞 E) d • x ∈ B`. Rewrite using `[← mul_smul, ← map_mul]`. Conclude with `h1`.

Take `⟨t, ht, e⟩` from `GlobalTheory.OverCompare.exists_intV_mul_inclE_eq_one (E := E) w π hπw`. Establish `h3 : (fun i => Formalism.UG.inclE (F` using `F) (w.adicCompletion F) ((algebraMap (𝓞 F) (𝓞 E) π • algebraMap (𝓞 F) (𝓞 E) d • x) i)) ∈ GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat w B := Submodule.subset_span ⟨_, h2, rfl⟩`. Establish `h4` using `Submodule.smul_mem (GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat w B) (⟨t, ht⟩ : intV E w) h3`. Rewrite `h4` using `[incl_smul]`. Establish `e2 : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) π) = algebraMap F E (π : F)`.

Rewrite using `[← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E]`. Rewrite `h4` using `[e2, Subring.smul_def, smul_smul]`. Rewrite `h4` using `[show ((⟨t, ht⟩ : intV E w) : E ⊗[F] w.adicCompletion F) * _ = 1 from e, one_smul]`. Then use the resulting hypothesis.
-/
theorem mem_localization_of_mem_localLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) (B : Submodule (𝓞 E) (Fin n → E)), Module.Finite (𝓞 E) B → Submodule.span E (B : Set (Fin n → E)) = ⊤ → ∀ (x : Fin n → E), (fun i => Formalism.UG.inclE (F := F) (v.adicCompletion F) (x i)) ∈ GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat v B → ∀ q : HeightOneSpectrum (𝓞 E), q.under (𝓞 F) = v → x ∈ Formalism.HermitianLatticesTheory.localization₂ q.asIdeal B := by
  intro F E _ _ _ _ _ n v B hB hs x hx q hq
  classical
  obtain ⟨ν, hν, hνx⟩ := exists_smul_mem_of_span B hs x
  let J : Ideal (𝓞 E) := B.comap (LinearMap.toSpanSingleton (𝓞 E) _ x)
  have hJ : ∀ s, s ∈ J ↔ s • x ∈ B := fun s => Iff.rfl
  have hJ0 : J.comap (algebraMap (𝓞 F) (𝓞 E)) ≠ ⊥ := by
    intro h
    have := Ideal.eq_bot_of_comap_eq_bot h
    have h2 : ν ∈ J := hνx
    rw [this] at h2
    exact hν h2
  haveI := v.isMaximal
  obtain ⟨Q, hQ, hI⟩ := Ideal.eq_prime_pow_mul_coprime hJ0 v.asIdeal
  obtain ⟨d, hdQ, hdv⟩ : ∃ d ∈ Q, d ∉ v.asIdeal := by
    by_contra h
    push_neg at h
    rw [sup_eq_left.2 (show Q ≤ v.asIdeal from h)] at hQ
    exact v.isPrime.ne_top hQ
  refine ⟨algebraMap (𝓞 F) (𝓞 E) d, fun h => hdv (by rw [← hq]; exact h), ?_⟩
  refine (GlobalTheory.LatLocGlob.latS_local_global F E n B hB).2.1 hs _ fun w => ?_
  by_cases hw : w = v
  · subst hw
    rw [incl_smul]
    exact Submodule.smul_mem (GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat w B)
      (⟨_, Subring.subset_closure (Or.inl ⟨⟨_, ⟨algebraMap (𝓞 F) (𝓞 E) d, rfl⟩⟩, rfl⟩)⟩ : intV E w) hx
  · obtain ⟨π, hπ, hπw⟩ : ∃ π ∈ v.asIdeal ^ (UniqueFactorizationMonoid.normalizedFactors (J.comap (algebraMap (𝓞 F) (𝓞 E)))).count v.asIdeal, π ∉ w.asIdeal := by
      by_contra h
      push_neg at h
      haveI := w.isPrime
      have h1 : v.asIdeal ≤ w.asIdeal := Ideal.IsPrime.le_of_pow_le h
      exact hw (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top h1).symm)
    have h1 : π * d ∈ J.comap (algebraMap (𝓞 F) (𝓞 E)) := by
      rw [hI]; exact Ideal.mul_mem_mul hπ hdQ
    have h2 : algebraMap (𝓞 F) (𝓞 E) π • algebraMap (𝓞 F) (𝓞 E) d • x ∈ B := by
      rw [← mul_smul, ← map_mul]; exact h1
    obtain ⟨t, ht, e⟩ := GlobalTheory.OverCompare.exists_intV_mul_inclE_eq_one (E := E) w π hπw
    have h3 : (fun i => Formalism.UG.inclE (F := F) (w.adicCompletion F) ((algebraMap (𝓞 F) (𝓞 E) π • algebraMap (𝓞 F) (𝓞 E) d • x) i)) ∈
        GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat w B := Submodule.subset_span ⟨_, h2, rfl⟩
    have h4 := Submodule.smul_mem (GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat w B) (⟨t, ht⟩ : intV E w) h3
    rw [incl_smul] at h4
    have e2 : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) π) = algebraMap F E (π : F) := by
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E]
    rw [e2, Subring.smul_def, smul_smul] at h4
    rwa [show ((⟨t, ht⟩ : intV E w) : E ⊗[F] w.adicCompletion F) * _ = 1 from e, one_smul] at h4

end Loc

section Adel
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

/- English proof (translation)
Rewrite using `[GlobalTheory.LatticeStabLocal.mem_latS_adele_iff]`. Establish `h1 : (fun i => prV (E` using `E) w (Formalism.UG.P.afsplitIE w (z i))) = z :=`. Use function extensionality and compare the values at `fun i => Formalism.UG.P.afsplit_prV_IE w _`. Prove the components needed by the constructor for the conclusion. Introduce `hz v`.

Distinguish the cases in `hv : v = w`. Substitute `hv` using the available equality. Rewrite using `[h1]`. Conclude with `hz`. Rewrite using `[show (fun i => prV (E := E) v (Formalism.UG.P.afsplitIE w (z i))) = 0 from`.

Use function extensionality and compare the values at `fun i => Formalism.UG.P.afsplit_prV_IE_ne w v hv _]`. Conclude with `zero_mem _`. Introduce `h`. Use `h w` as an intermediate fact. Rewrite `this` using `[h1]`. Then use the resulting hypothesis.
-/
theorem mem_locLat_iff_adelic (w : HeightOneSpectrum (𝓞 F)) (L : Submodule (𝓞 E) (Fin n → E)) (hL : Module.Finite (𝓞 E) L)
    (z : Fin n → E ⊗[F] w.adicCompletion F) :
    z ∈ GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat w L ↔ (fun i => Formalism.UG.P.afsplitIE w (z i)) ∈ Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) L := by
  rw [GlobalTheory.LatticeStabLocal.mem_latS_adele_iff]
  have h1 : (fun i => prV (E := E) w (Formalism.UG.P.afsplitIE w (z i))) = z :=
    funext fun i => Formalism.UG.P.afsplit_prV_IE w _
  constructor
  · intro hz v
    by_cases hv : v = w
    · subst hv; rw [h1]; exact hz
    · rw [show (fun i => prV (E := E) v (Formalism.UG.P.afsplitIE w (z i))) = 0 from
        funext fun i => Formalism.UG.P.afsplit_prV_IE_ne w v hv _]
      exact zero_mem _
  · intro h
    have := h w
    rwa [h1] at this

end Adel

section LocB

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

/- English proof (translation)
The claim follows from `Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds F E (Fin n) Lb hf hs g X`.
-/
theorem mem_latS_globLat_iff (Lb : Submodule (𝓞 E) (Fin n → E)) (hf : Module.Finite (𝓞 E) Lb)
    (hs : Submodule.span E (Lb : Set (Fin n → E)) = ⊤) (g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (X : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    X ∈ Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F))
        (Formalism.UG.CS.globLat g Lb) ↔
      ((g⁻¹ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) _) *ᵥ X ∈
        Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) Lb :=
  Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds F E (Fin n) Lb hf hs g X

/- English proof (translation)
Establish `hlat` using `fun g => Formalism.UG.P.global_lattice_isLattice_holds F E (Fin n) Lb hf hs g`. Establish `hfin : ∀ g, Module.Finite (𝓞 E) (Formalism.UG.CS.globLat g Lb)` using `fun g => Module.Finite.iff_fg.2 (hlat g).fg`. Establish `hq : Q.under (𝓞 F) = v` using `HeightOneSpectrum.ext hQ.symm`. Introduce `z hz`. Use `mem_localization_of_mem_localLattice F E n v _ (hfin x₁) (hlat x₁).span_eq_top z ?_ Q hq` and prove the remaining obligations.

Establish `hz' : (fun i => Formalism.UG.inclE (F` using `F) (v.adicCompletion F) (z i)) ∈ GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat v (Formalism.UG.CS.globLat x Lb) := Submodule.subset_span ⟨z, hz, rfl⟩`. Rewrite using `[mem_locLat_iff_adelic v _ (hfin x₁), mem_latS_globLat_iff Lb hf hs]`. Rewrite `hz'` using `[mem_locLat_iff_adelic v _ (hfin x), mem_latS_globLat_iff Lb hf hs]`. Use `set X : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F := fun i => Formalism.UG.P.afsplitIE v (Formalism.UG.inclE (F := F) (v.adicCompletion F) (z i))`. Establish `hp : ∀ p : HeightOneSpectrum (𝓞 F), (fun i => Formalism.UG.prV (E` using `E) p ((((x₁⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ X) i)) = (fun i => Formalism.UG.prV (E := E) p ((((x⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ X) i)) := by`.

Introduce `p`. Rewrite using `[GlobalTheory.LatticeStabLocal.prV_mulVec, GlobalTheory.LatticeStabLocal.prV_mulVec]`. Distinguish the cases in `hpv : p = v`. Substitute `hpv` using the available equality. Establish `h1 : ((x₁⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _).map (Formalism.UG.prV (E` using `E) p) = ((Formalism.UG.bc (Formalism.UG.prV (E := E) p) x₁⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) := rfl`.

Establish `h2 : ((x⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _).map (Formalism.UG.prV (E` using `E) p) = ((Formalism.UG.bc (Formalism.UG.prV (E := E) p) x⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) := rfl`. Rewrite using `[h1, h2, map_inv, map_inv, hx]`. Rewrite using `[show (fun i => Formalism.UG.prV (E := E) p (X i)) = 0 from funext fun i => Formalism.UG.P.afsplit_prV_IE_ne v p hpv _, Matrix.mulVec_zero, Matrix.mulVec_zero]`. Establish `e : (((x₁⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ X) = (((x⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ X)`. Use function extensionality and compare the values at `i`.

Rewrite using `[← sub_eq_zero]`. Use `Formalism.UG.P.afsplit_inj _ fun p => ?_` and prove the remaining obligations. Rewrite using `[map_sub, sub_eq_zero]`. Conclude with `congrFun (hp p) i`. Rewrite using `[e]`.

Conclude with `hz'`.
-/
theorem globLat_le_localization_globLat (Lb : Submodule (𝓞 E) (Fin n → E)) (hf : Module.Finite (𝓞 E) Lb)
    (hs : Submodule.span E (Lb : Set (Fin n → E)) = ⊤)
    (x x₁ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Q : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F))
    (hQ : v.asIdeal = Q.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)))
    (hx : Formalism.UG.bc (Formalism.UG.prV (E := E) v) x₁ = Formalism.UG.bc (Formalism.UG.prV (E := E) v) x) :
    Formalism.UG.CS.globLat x Lb ≤ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal (Formalism.UG.CS.globLat x₁ Lb) := by
  have hlat := fun g => Formalism.UG.P.global_lattice_isLattice_holds F E (Fin n) Lb hf hs g
  have hfin : ∀ g, Module.Finite (𝓞 E) (Formalism.UG.CS.globLat g Lb) := fun g => Module.Finite.iff_fg.2 (hlat g).fg
  have hq : Q.under (𝓞 F) = v := HeightOneSpectrum.ext hQ.symm
  intro z hz
  refine mem_localization_of_mem_localLattice F E n v _ (hfin x₁) (hlat x₁).span_eq_top z ?_ Q hq
  have hz' : (fun i => Formalism.UG.inclE (F := F) (v.adicCompletion F) (z i)) ∈ GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat v (Formalism.UG.CS.globLat x Lb) :=
    Submodule.subset_span ⟨z, hz, rfl⟩
  rw [mem_locLat_iff_adelic v _ (hfin x₁), mem_latS_globLat_iff Lb hf hs]
  rw [mem_locLat_iff_adelic v _ (hfin x), mem_latS_globLat_iff Lb hf hs] at hz'
  set X : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F := fun i => Formalism.UG.P.afsplitIE v (Formalism.UG.inclE (F := F) (v.adicCompletion F) (z i))
  have hp : ∀ p : HeightOneSpectrum (𝓞 F),
      (fun i => Formalism.UG.prV (E := E) p ((((x₁⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ X) i)) =
        (fun i => Formalism.UG.prV (E := E) p ((((x⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ X) i)) := by
    intro p
    rw [GlobalTheory.LatticeStabLocal.prV_mulVec, GlobalTheory.LatticeStabLocal.prV_mulVec]
    by_cases hpv : p = v
    · subst hpv
      have h1 : ((x₁⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _).map (Formalism.UG.prV (E := E) p) =
          ((Formalism.UG.bc (Formalism.UG.prV (E := E) p) x₁⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) := rfl
      have h2 : ((x⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _).map (Formalism.UG.prV (E := E) p) =
          ((Formalism.UG.bc (Formalism.UG.prV (E := E) p) x⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) := rfl
      rw [h1, h2, map_inv, map_inv, hx]
    · rw [show (fun i => Formalism.UG.prV (E := E) p (X i)) = 0 from funext fun i => Formalism.UG.P.afsplit_prV_IE_ne v p hpv _,
        Matrix.mulVec_zero, Matrix.mulVec_zero]
  have e : (((x₁⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ X) = (((x⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ X) := by
    funext i
    rw [← sub_eq_zero]
    refine Formalism.UG.P.afsplit_inj _ fun p => ?_
    rw [map_sub, sub_eq_zero]
    exact congrFun (hp p) i
  rw [e]
  exact hz'

end LocB

section Glue

/- English proof (translation)
The claim follows from `Submodule.span_eq (Formalism.UG.CS.globLat y Lb)`.
-/
theorem latAd_eq' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Lb : Submodule (𝓞 E) (Fin N → E)) :
    Formalism.L2.PairingIndexBounds.F.latAd y Lb = Formalism.UG.CS.globLat y Lb :=
  Submodule.span_eq (Formalism.UG.CS.globLat y Lb)

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {N : ℕ}

/- English proof (translation)
Establish `hfin : Module.Finite (𝓞 E) (Formalism.UG.CS.globLat y Lb)` using `Module.Finite.iff_fg.2 (Formalism.UG.P.global_lattice_isLattice_holds F E (Fin N) Lb hf hs y).fg`. Unfold `latCo mvL`. Use `map_le_locP Q.asIdeal (toLE co) ?_` and prove the remaining obligations. Unfold `compan`. Rewrite using `[latAd_eq', latAd_eq']`.

Use `sup_smul_le_locP Q.asIdeal _ (globLat_le_localization_globLat Lb hf hs y₁ y Q v hQ hy.symm) ?_` and prove the remaining obligations. Conclude with `Submodule.span_le.2 (dualSet_le_locP _ e he J hfin Q.asIdeal Qc.asIdeal hI (globLat_le_localization_globLat Lb hf hs y y₁ Qc v hQc hy))`.
-/
theorem latCo_le_locP (sp : Spaces R F E) (J : Matrix (Fin N) (Fin N) E) (co : GL (Fin N) E) (a : 𝓞 E)
    (Lb : Submodule (𝓞 E) (Fin N → E)) (hf : Module.Finite (𝓞 E) Lb) (hs : Submodule.span E (Lb : Set (Fin N → E)) = ⊤)
    (y y₁ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Q Qc : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F))
    (hQ : v.asIdeal = Q.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))) (hQc : v.asIdeal = Qc.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)))
    (e : 𝓞 E ≃+* 𝓞 E) (he : ∀ t : 𝓞 E, (sp.cm.sig : E →+* E) (algebraMap (𝓞 E) E t) = algebraMap (𝓞 E) E (e t))
    (hI : ∀ t, t ∉ Qc.asIdeal → e t ∉ Q.asIdeal)
    (hy : Formalism.UG.bc (Formalism.UG.prV (E := E) v) y₁ = Formalism.UG.bc (Formalism.UG.prV (E := E) v) y) :
    latCo sp J co a y₁ Lb ≤ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal (latCo sp J co a y Lb) := by
  have hfin : Module.Finite (𝓞 E) (Formalism.UG.CS.globLat y Lb) :=
    Module.Finite.iff_fg.2 (Formalism.UG.P.global_lattice_isLattice_holds F E (Fin N) Lb hf hs y).fg
  unfold latCo mvL
  refine map_le_locP Q.asIdeal (toLE co) ?_
  unfold compan
  rw [latAd_eq', latAd_eq']
  refine sup_smul_le_locP Q.asIdeal _ (globLat_le_localization_globLat Lb hf hs y₁ y Q v hQ hy.symm) ?_
  exact Submodule.span_le.2 (dualSet_le_locP _ e he J hfin Q.asIdeal Qc.asIdeal hI (globLat_le_localization_globLat Lb hf hs y y₁ Qc v hQc hy))

end Glue

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _hPins hTie j hj β x x₁ p p₁ hp hp₁ hx P`. Use `set Q : HeightOneSpectrum (𝓞 D.host.E) := seamP t.seam P.1 with hQdef`. Establish `hQS : Q ∈ ssRec t u μ`. Rewrite using `[hQdef, mem_ssRec, ((isChainTop_iff _ _ _ _ _ _ _ _ _).1 hTie.isChainTop).1]`. Conclude with `Finset.mem_union_left _ P.2`.

Use `set v : HeightOneSpectrum (𝓞 D.host.F) := Q.under (𝓞 D.host.F) with hvdef`. Establish `hQv : v.asIdeal = Q.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))` using `rfl`. Establish `hv : Formalism.UG.bc (Formalism.UG.prV (E` using `D.host.E) v) x₁.1 = Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) x.1 := hx v ⟨Q, hQS, hQv⟩`. Use `set e : 𝓞 D.host.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv (starRingAut : D.host.E ≃+* D.host.E) with hedef`. Establish `hee : ∀ t' : 𝓞 D.host.E, e (e t') = t'` using `fun t' => Subtype.ext (star_star (t' : D.host.E))`.

Use `set Qc : HeightOneSpectrum (𝓞 D.host.E) := HeightOneSpectrum.equivOfRingEquiv e Q with hQcdef`. Establish `hmemc : ∀ t' : 𝓞 D.host.E, e t' ∈ Qc.asIdeal ↔ t' ∈ Q.asIdeal` using `fun t' => mem_equivOfRingEquiv _ Q t'`. Establish `hI : ∀ t', t' ∉ Qc.asIdeal → e t' ∉ Q.asIdeal` using `fun t' ht hQ => ht (by rw [← hee t']; exact (hmemc _).2 hQ)`. Establish `hfixF : ∀ r : 𝓞 D.host.F, e (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r`. Introduce `r`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show star ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r : 𝓞 D.host.E) : D.host.E) = _`. Establish `h1 : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r : 𝓞 D.host.E) : D.host.E) = algebraMap D.host.F D.host.E (r : D.host.F)` using `by show algebraMap (𝓞 D.host.E) D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) = _`. Rewrite using `[← IsScalarTower.algebraMap_apply (𝓞 D.host.F) (𝓞 D.host.E) D.host.E, IsScalarTower.algebraMap_apply (𝓞 D.host.F) D.host.F D.host.E]`. Rewrite using `[h1]`.

Conclude with `(D.sp.cm.fixed _).2 ⟨_, rfl⟩`. Establish `hQcv : v.asIdeal = Qc.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))`. Rewrite using `[hQv]`. Use extensionality with `r`. Simplify using `only [Ideal.mem_comap]`.

Rewrite using `[← hmemc, hfixF]`. Establish `he : ∀ t' : 𝓞 D.host.E, (D.sp.cm.sig : D.host.E →+* D.host.E) (algebraMap (𝓞 D.host.E) D.host.E t') = algebraMap (𝓞 D.host.E) D.host.E (e t')` using `fun t' => rfl`. Establish `hf` using `((St j hj).K β).lev.Lb_fin`. Establish `hs` using `((St j hj).K β).lev.Lb_span`. Establish `h1` using `latCo_le_locP D.sp (gramN D j hj) (A.crd j hj) a _ hf hs x.1 x₁.1 Q Qc v hQv hQcv e he hI hv`.

Establish `h2` using `latCo_le_locP D.sp (gramN D j hj) (A.crd j hj) a _ hf hs x₁.1 x.1 Q Qc v hQv hQcv e he hI hv.symm`. Rewrite `h1` using `[← hp.lat, ← hp₁.lat]`. Rewrite `h2` using `[← hp.lat, ← hp₁.lat]`. Conclude with `le_antisymm (localization_le_of_le_localization₂ _ (le_localized_of_transport t.seam.iE _ _ P.1 h1)) (localization_le_of_le_localization₂ _ (le_localized_of_transport t.seam.iE _ _ P.1 h2))`.
-/
theorem lat_eq : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj)
  (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j), IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
  (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
  ∀ P : t.Pr.vT (t.word u), p₁.deco.1.at P.1 = p.deco.1.at P.1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _hPins hTie j hj β x x₁ p p₁ hp hp₁ hx P
  classical
  set Q : HeightOneSpectrum (𝓞 D.host.E) := seamP t.seam P.1 with hQdef
  have hQS : Q ∈ ssRec t u μ := by
    rw [hQdef, mem_ssRec, ((isChainTop_iff _ _ _ _ _ _ _ _ _).1 hTie.isChainTop).1]
    exact Finset.mem_union_left _ P.2
  set v : HeightOneSpectrum (𝓞 D.host.F) := Q.under (𝓞 D.host.F) with hvdef
  have hQv : v.asIdeal = Q.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := rfl
  have hv : Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) x₁.1 = Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) x.1 :=
    hx v ⟨Q, hQS, hQv⟩
  set e : 𝓞 D.host.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv (starRingAut : D.host.E ≃+* D.host.E) with hedef
  have hee : ∀ t' : 𝓞 D.host.E, e (e t') = t' := fun t' => Subtype.ext (star_star (t' : D.host.E))
  set Qc : HeightOneSpectrum (𝓞 D.host.E) := HeightOneSpectrum.equivOfRingEquiv e Q with hQcdef
  have hmemc : ∀ t' : 𝓞 D.host.E, e t' ∈ Qc.asIdeal ↔ t' ∈ Q.asIdeal := fun t' => mem_equivOfRingEquiv _ Q t'
  have hI : ∀ t', t' ∉ Qc.asIdeal → e t' ∉ Q.asIdeal := fun t' ht hQ => ht (by rw [← hee t']; exact (hmemc _).2 hQ)
  have hfixF : ∀ r : 𝓞 D.host.F, e (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r := by
    intro r
    apply Subtype.ext
    show star ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r : 𝓞 D.host.E) : D.host.E) = _
    have h1 : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r : 𝓞 D.host.E) : D.host.E) = algebraMap D.host.F D.host.E (r : D.host.F) := by
      show algebraMap (𝓞 D.host.E) D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) = _
      rw [← IsScalarTower.algebraMap_apply (𝓞 D.host.F) (𝓞 D.host.E) D.host.E, IsScalarTower.algebraMap_apply (𝓞 D.host.F) D.host.F D.host.E]
    rw [h1]
    exact (D.sp.cm.fixed _).2 ⟨_, rfl⟩
  have hQcv : v.asIdeal = Qc.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
    rw [hQv]
    ext r
    simp only [Ideal.mem_comap]
    rw [← hmemc, hfixF]
  have he : ∀ t' : 𝓞 D.host.E, (D.sp.cm.sig : D.host.E →+* D.host.E) (algebraMap (𝓞 D.host.E) D.host.E t') =
      algebraMap (𝓞 D.host.E) D.host.E (e t') := fun t' => rfl
  have hf := ((St j hj).K β).lev.Lb_fin
  have hs := ((St j hj).K β).lev.Lb_span
  have h1 := latCo_le_locP D.sp (gramN D j hj) (A.crd j hj) a _ hf hs x.1 x₁.1 Q Qc v hQv hQcv e he hI hv
  have h2 := latCo_le_locP D.sp (gramN D j hj) (A.crd j hj) a _ hf hs x₁.1 x.1 Q Qc v hQv hQcv e he hI hv.symm
  rw [← hp.lat, ← hp₁.lat] at h1
  rw [← hp.lat, ← hp₁.lat] at h2
  exact le_antisymm (localization_le_of_le_localization₂ _ (le_localized_of_transport t.seam.iE _ _ P.1 h1))
    (localization_le_of_le_localization₂ _ (le_localized_of_transport t.seam.iE _ _ P.1 h2))

end GlobalTheory.TwV.AwayLat
