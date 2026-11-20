import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InertDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianLatticeOpenCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger

noncomputable section

namespace PositivityTheory.ThKH.Evl

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

open scoped nonZeroDivisors in

/- English proof (translation)
Establish `inj : Function.Injective (algebraMap R K)` using `IsFractionRing.injective R K`. Establish `canc : ∀ a : R, a ≠ 0 → ∀ x y : V, a • x = a • y → x = y` using `fun a ha x y h => by`. Rewrite `h` using `[← algebraMap_smul K, ← algebraMap_smul K a y]`. Conclude with `smul_right_injective V ((map_ne_zero_iff _ inj).2 ha) h`. Establish `: Module.IsTorsionFree R L`.

Use `⟨fun a ha x y h => Subtype.ext (canc a ha.ne_zero _ _ (congrArg Subtype.val h))⟩` and prove the remaining obligations. Establish `: Module.FinitePresentation R L` using `Module.finitePresentation_of_finite R L`. Establish `: Module.Projective R L` using `Module.Flat.projective_of_finitePresentation`. Take `⟨N, f, g, -, -, hfg⟩` from `Module.Finite.exists_comp_eq_id_of_projective R L`. Establish `: IsLocalizedModule R⁰ L.subtype` using `{ map_units := fun a => by`.

Rewrite using `[← (Algebra.lsmul R (A := K) R V).commutes]`. Conclude with `(IsLocalization.map_units K a).map _`. Use `surj := fun y => by`. Take `⟨a, ha, h⟩` from `hden y`. Conclude with `⟨(⟨_, h⟩, ⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩), rfl⟩`.

Use `exists_of_eq := fun h => ⟨1, by rw [Subtype.ext h]⟩ }`. Establish `hb` using `IsLocalizedModule.isBaseChange R⁰ K L.subtype`. Set `G : Fin N → V →ₗ[K] K` to `fun i => hb.lift (Algebra.linearMap R K ∘ₗ LinearMap.proj i ∘ₗ g)`. Establish `hG : ∀ i (x : L), G i x = algebraMap R K (g x i)` using `fun i x => hb.lift_eq _ x`. Use `⟨N, fun i => f (Pi.single i 1), G, fun i => (f _).2, fun i x hx => ⟨_, hG i ⟨x, hx⟩⟩, fun x => ?_⟩` and prove the remaining obligations.

Take `⟨a, ha, h⟩` from `hden x`. Use `canc a ha _ _ ?_` and prove the remaining obligations. Establish `h1 : f (g ⟨_, h⟩) = ⟨_, h⟩` using `LinearMap.congr_fun hfg _`. Rewrite `h1` using `[← Finset.univ_sum_single (g ⟨_, h⟩), map_sum]`. Establish `h2` using `congrArg Subtype.val h1`.

Rewrite `h2` using `[Submodule.coe_sum]`. Rewrite using `[Finset.smul_sum]`. Use `Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h2` and prove the remaining obligations. Establish `e1 : (Pi.single i (g ⟨_, h⟩ i) : Fin N → R) = g ⟨_, h⟩ i • (Pi.single i 1 : Fin N → R)`. Rewrite using `[← Pi.single_smul, smul_eq_mul, mul_one]`.

Rewrite using `[e1, map_smul, Submodule.coe_smul, ← algebraMap_smul K (g ⟨_, h⟩ i), ← hG, ← smul_assoc, LinearMap.map_smul_of_tower]`.
-/
theorem exists_dual_frame {R K V : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] (L : Submodule R V) [Module.Finite R L]
    (hden : ∀ z : V, ∃ a : R, a ≠ 0 ∧ a • z ∈ L) :
    ∃ (N : ℕ) (e : Fin N → V) (g : Fin N → V →ₗ[K] K), (∀ i, e i ∈ L) ∧
      (∀ i, ∀ x ∈ L, ∃ a : R, g i x = algebraMap R K a) ∧ ∀ x, ∑ i, g i x • e i = x := by
  classical
  have inj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have canc : ∀ a : R, a ≠ 0 → ∀ x y : V, a • x = a • y → x = y := fun a ha x y h => by
    rw [← algebraMap_smul K, ← algebraMap_smul K a y] at h
    exact smul_right_injective V ((map_ne_zero_iff _ inj).2 ha) h
  have : Module.IsTorsionFree R L := by
    refine ⟨fun a ha x y h => Subtype.ext (canc a ha.ne_zero _ _ (congrArg Subtype.val h))⟩
  have : Module.FinitePresentation R L := Module.finitePresentation_of_finite R L
  have : Module.Projective R L := Module.Flat.projective_of_finitePresentation
  obtain ⟨N, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R L
  have : IsLocalizedModule R⁰ L.subtype :=
    { map_units := fun a => by
        rw [← (Algebra.lsmul R (A := K) R V).commutes]
        exact (IsLocalization.map_units K a).map _
      surj := fun y => by
        obtain ⟨a, ha, h⟩ := hden y
        exact ⟨(⟨_, h⟩, ⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩), rfl⟩
      exists_of_eq := fun h => ⟨1, by rw [Subtype.ext h]⟩ }
  have hb := IsLocalizedModule.isBaseChange R⁰ K L.subtype
  let G : Fin N → V →ₗ[K] K := fun i => hb.lift (Algebra.linearMap R K ∘ₗ LinearMap.proj i ∘ₗ g)
  have hG : ∀ i (x : L), G i x = algebraMap R K (g x i) := fun i x => hb.lift_eq _ x
  refine ⟨N, fun i => f (Pi.single i 1), G, fun i => (f _).2, fun i x hx => ⟨_, hG i ⟨x, hx⟩⟩, fun x => ?_⟩
  obtain ⟨a, ha, h⟩ := hden x
  refine canc a ha _ _ ?_
  have h1 : f (g ⟨_, h⟩) = ⟨_, h⟩ := LinearMap.congr_fun hfg _
  rw [← Finset.univ_sum_single (g ⟨_, h⟩), map_sum] at h1
  have h2 := congrArg Subtype.val h1
  rw [Submodule.coe_sum] at h2
  rw [Finset.smul_sum]
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h2
  have e1 : (Pi.single i (g ⟨_, h⟩ i) : Fin N → R) = g ⟨_, h⟩ i • (Pi.single i 1 : Fin N → R) := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [e1, map_smul, Submodule.coe_smul, ← algebraMap_smul K (g ⟨_, h⟩ i), ← hG, ← smul_assoc, LinearMap.map_smul_of_tower]

omit [NumberField F] [NumberField E] in
/- English proof (translation)
Use `⟨c ᵥ* J⁻¹, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[form, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hJ.isUnit, Matrix.vecMul_one]`. Both sides reduce to the same expression.
-/
theorem exists_form {J : Matrix (Fin n) (Fin n) E} (hJ : J.det ≠ 0) (c : Fin n → E) :
    ∃ x', ∀ x, form σ J x' x = ∑ i, c i * σ (x i) := by
  refine ⟨c ᵥ* J⁻¹, fun x => ?_⟩
  rw [form, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hJ.isUnit, Matrix.vecMul_one]
  rfl

omit [NumberField F] [NumberField E] in
/- English proof (translation)
Simplify using `[form, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_left_comm]`.
-/
theorem form_smul (J : Matrix (Fin n) (Fin n) E) (a : E) (x y : Fin n → E) : form σ J x (a • y) = σ a * form σ J x y := by
  simp [form, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_left_comm]

omit [NumberField F] [NumberField E] in
/- English proof (translation)
Take `⟨x', h⟩` from `exists_form (σ := σ) hJ fun i => σ (g fun j => if i = j then 1 else 0)`. Use `⟨x', fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[h, g.pi_apply_eq_sum_univ x, map_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, map_mul, mul_comm]`.
-/
theorem rep_E {J : Matrix (Fin n) (Fin n) E} (hJ : J.det ≠ 0) (g : (Fin n → E) →ₗ[E] E) :
    ∃ x', ∀ x, form σ J x' x = σ (g x) := by
  obtain ⟨x', h⟩ := exists_form (σ := σ) hJ fun i => σ (g fun j => if i = j then 1 else 0)
  refine ⟨x', fun x => ?_⟩
  rw [h, g.pi_apply_eq_sum_univ x, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, map_mul, mul_comm]

/- English proof (translation)
Establish `hn` using `traceForm_nondegenerate F E`. Take `⟨x', h⟩` from `exists_form (σ := σ) hJ fun i => ((Algebra.traceForm F E).toDual hn).symm (g ∘ₗ LinearMap.single F (fun _ => E) i ∘ₗ σ.toLinearMap)`. Use `⟨x', fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[h, map_sum]`. Use `conv_rhs => rw [← Finset.univ_sum_single x, map_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Algebra.traceForm_apply, LinearMap.BilinForm.apply_toDual_symm_apply]`. Simplify using `[hσ]`.
-/
theorem rep_F (hσ : ∀ z, σ (σ z) = z) {J : Matrix (Fin n) (Fin n) E} (hJ : J.det ≠ 0) (g : (Fin n → E) →ₗ[F] F) :
    ∃ x', ∀ x, Algebra.trace F E (form σ J x' x) = g x := by
  have hn := traceForm_nondegenerate F E
  obtain ⟨x', h⟩ := exists_form (σ := σ) hJ fun i =>
    ((Algebra.traceForm F E).toDual hn).symm (g ∘ₗ LinearMap.single F (fun _ => E) i ∘ₗ σ.toLinearMap)
  refine ⟨x', fun x => ?_⟩
  rw [h, map_sum]
  conv_rhs => rw [← Finset.univ_sum_single x, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Algebra.traceForm_apply, LinearMap.BilinForm.apply_toDual_symm_apply]
  simp [hσ]

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[h.2.2.2, h.2.2.2, star_star]`.
-/
theorem invol (h : IsCMExt F E σ) (z : E) : σ (σ z) = z := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

/- English proof (translation)
The claim follows from `h.map (σ.toRingHom.toIntAlgHom)`.
-/
theorem isIntegral_map {z : E} (h : IsIntegral ℤ z) : IsIntegral ℤ (σ z) := h.map (σ.toRingHom.toIntAlgHom)

/- English proof (translation)
Establish `hJ : X.J.det ≠ 0` using `fun h0 => by`. Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Use `GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hX.sig w) ?_` and prove the remaining obligations. Rewrite using `[show (X.J.map (B.emb w).1).det = (B.emb w).1 X.J.det from (RingHom.map_det _ _).symm, h0, map_zero]`. Establish `: Module.Finite (𝓞 E) X.L` using `Module.Finite.iff_fg.mpr hX.lat.fg`.

Take `⟨N, e, g, he, hg, hs⟩` from `exists_dual_frame (K := E) X.L fun z => by`. Take `⟨m, hm, h⟩` from `GlobalTheory.LatOpenCpt.exists_zsmul_mem X.L hX.lat z`. Conclude with `⟨m, Int.cast_ne_zero.2 hm, by rwa [Int.cast_smul_eq_zsmul]⟩`. Use `choose x' hx' using fun i => rep_E (σ := σ) hJ (g i)`. Use `⟨N, e, x', he, fun i => (hX.dual _).2 fun x hx => ?_, fun i z => g i z, hx', hs⟩` and prove the remaining obligations.

Take `⟨a, ha⟩` from `hg i x hx`. Rewrite using `[hx', ha]`. Conclude with `isIntegral_map a.isIntegral_coe`.
-/
theorem frame_X {B : Base F E} {X : Spc F E n} {r s : ℕ} (hX : X.IsHerm σ B r s) :
    ∃ (N : ℕ) (x x' : Fin N → Fin n → E), (∀ i, x i ∈ X.L) ∧ (∀ i, x' i ∈ X.L) ∧
      ∃ g : Fin N → (Fin n → E) → E, (∀ i z, form σ X.J (x' i) z = σ (g i z)) ∧ ∀ z, ∑ i, g i z • x i = z := by
  have hJ : X.J.det ≠ 0 := fun h0 => by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    refine GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hX.sig w) ?_
    rw [show (X.J.map (B.emb w).1).det = (B.emb w).1 X.J.det from (RingHom.map_det _ _).symm, h0, map_zero]
  have : Module.Finite (𝓞 E) X.L := Module.Finite.iff_fg.mpr hX.lat.fg
  obtain ⟨N, e, g, he, hg, hs⟩ := exists_dual_frame (K := E) X.L fun z => by
    obtain ⟨m, hm, h⟩ := GlobalTheory.LatOpenCpt.exists_zsmul_mem X.L hX.lat z
    exact ⟨m, Int.cast_ne_zero.2 hm, by rwa [Int.cast_smul_eq_zsmul]⟩
  choose x' hx' using fun i => rep_E (σ := σ) hJ (g i)
  refine ⟨N, e, x', he, fun i => (hX.dual _).2 fun x hx => ?_, fun i z => g i z, hx', hs⟩
  obtain ⟨a, ha⟩ := hg i x hx
  rw [hx', ha]
  exact isIntegral_map a.isIntegral_coe

/- English proof (translation)
Establish `hσ` using `invol hB.cm`. Establish `hJ : W.J.det ≠ 0` using `fun h0 => by`. Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Use `GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hW.sig w) ?_` and prove the remaining obligations. Rewrite using `[Matrix.det_smul, show (W.J.map (B.emb w).1).det = (B.emb w).1 W.J.det from (RingHom.map_det _ _).symm, h0, map_zero, mul_zero]`.

Establish `: Module.Finite (𝓞 E) W.L` using `Module.Finite.iff_fg.mpr hW.lat.fg`. Establish `: Module.Finite (𝓞 F) W.L` using `Module.Finite.trans (𝓞 E) W.L`. Establish `: Module.Finite (𝓞 F) (W.L.restrictScalars (𝓞 F))` using `this`. Take `⟨N, e, g, he, hg, hs⟩` from `exists_dual_frame (K := F) (W.L.restrictScalars (𝓞 F)) fun z => by`. Take `⟨m, hm, h⟩` from `GlobalTheory.LatOpenCpt.exists_zsmul_mem W.L hW.lat z`.

Conclude with `⟨m, Int.cast_ne_zero.2 hm, by rwa [Int.cast_smul_eq_zsmul]⟩`. Use `choose y' hy' using fun i => rep_F hσ hJ (g i)`. Use `⟨N, e, y', he, fun i => (hW.dual _).2 fun x hx o => ?_, fun z => by simpa only [hy'] using hs z⟩` and prove the remaining obligations. Set `o' : 𝓞 E` to `⟨σ o, isIntegral_map o.isIntegral_coe⟩`. Take `⟨a, ha⟩` from `hg i (o' • x) (W.L.smul_mem o' hx)`.

Establish `e1 : (o : E) * form σ W.J (y' i) x = form σ W.J (y' i) (o' • x)`. Rewrite using `[show o' • x = σ (o : E) • x from rfl, form_smul, hσ]`. Rewrite using `[e1, ← Algebra.trace_trace (S := F), hy', ha]`. Conclude with `Algebra.isIntegral_trace a.isIntegral_coe`.
-/
theorem frame_alt_alt {B : Base F E} {W : Spc F E d} {r s : ℕ} (hB : B.IsGood σ) (hW : W.IsSkew σ B r s) :
    ∃ (N : ℕ) (y y' : Fin N → Fin d → E), (∀ i, y i ∈ W.L) ∧ (∀ i, y' i ∈ W.L) ∧
      ∀ z, ∑ i, Algebra.trace F E (form σ W.J (y' i) z) • y i = z := by
  have hσ := invol hB.cm
  have hJ : W.J.det ≠ 0 := fun h0 => by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    refine GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hW.sig w) ?_
    rw [Matrix.det_smul, show (W.J.map (B.emb w).1).det = (B.emb w).1 W.J.det from (RingHom.map_det _ _).symm, h0,
      map_zero, mul_zero]
  have : Module.Finite (𝓞 E) W.L := Module.Finite.iff_fg.mpr hW.lat.fg
  have : Module.Finite (𝓞 F) W.L := Module.Finite.trans (𝓞 E) W.L
  have : Module.Finite (𝓞 F) (W.L.restrictScalars (𝓞 F)) := this
  obtain ⟨N, e, g, he, hg, hs⟩ := exists_dual_frame (K := F) (W.L.restrictScalars (𝓞 F)) fun z => by
    obtain ⟨m, hm, h⟩ := GlobalTheory.LatOpenCpt.exists_zsmul_mem W.L hW.lat z
    exact ⟨m, Int.cast_ne_zero.2 hm, by rwa [Int.cast_smul_eq_zsmul]⟩
  choose y' hy' using fun i => rep_F hσ hJ (g i)
  refine ⟨N, e, y', he, fun i => (hW.dual _).2 fun x hx o => ?_, fun z => by simpa only [hy'] using hs z⟩
  let o' : 𝓞 E := ⟨σ o, isIntegral_map o.isIntegral_coe⟩
  obtain ⟨a, ha⟩ := hg i (o' • x) (W.L.smul_mem o' hx)
  have e1 : (o : E) * form σ W.J (y' i) x = form σ W.J (y' i) (o' • x) := by
    rw [show o' • x = σ (o : E) • x from rfl, form_smul, hσ]
  rw [e1, ← Algebra.trace_trace (S := F), hy', ha]
  exact Algebra.isIntegral_trace a.isIntegral_coe

/- English proof (translation)
Take `⟨N, x, x', hx, hx', g, hg, hgs⟩` from `frame_X hX`. Take `⟨N', y, y', hy, hy', hs⟩` from `frame_alt_alt hB hW`. Use `⟨Fin N × Fin N', inferInstance, fun p => x p.1, fun p => -x' p.1, fun p => y p.2, fun p => y' p.2, fun p => ⟨hx _, neg_mem (hx' _), hy _, hy' _⟩, fun u => ?_⟩` and prove the remaining obligations. Establish `hu` using `GlobalTheory.LatOpenCpt.span_top (F := F) hX.lat hW.lat (fun p : X.L × W.L => Matrix.vecMulVec p.1.1 p.2.1) (fun x hx y hy => Submodule.subset_span ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩) u`. Proceed by induction on `hu using Submodule.span_induction with`.

Consider the case `mem z hz`. Take `⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, rfl⟩` from `hz`. Establish `key : Matrix.vecMulVec a b = ∑ p : Fin N × Fin N', Algebra.trace F E (form σ W.J (y' p.2) (g p.1 a • b)) • Matrix.vecMulVec (x p.1) (y p.2)`. Rewrite using `[Fintype.sum_prod_type]`. Use `conv_lhs => rw [← hgs a]`.

Use extensionality with `i j`. Simplify using `only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Finset.sum_apply, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `h` using `congrFun (hs (g k a • b)) j`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h ⊢`.

Rewrite using `[mul_comm (g k a), mul_assoc, ← h, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun l _ => by rw [mul_smul_comm]`. Establish `hs' : ∀ p : Fin N × Fin N', symp (R` using `AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) (incM F (Matrix.vecMulVec (-x' p.1) (y' p.2))) (incM F (Matrix.vecMulVec a b)) = algebraMap F (AF F) (Algebra.trace F E (form σ W.J (y' p.2) (g p.1 a • b))) := fun p => by`. Establish `h` using `GlobalTheory.LatVacArith.symp_incM σ X.J W.J (-1) (-x' p.1) a (y' p.2) b`. Rewrite `h` using `[map_neg, map_one]`.

Rewrite using `[h, form_smul, ← hg]`. Simplify using `[form]`. Simplify using `only [hs']`. Use `conv_lhs => rw [key]`. Use extensionality with `i j`.

Simplify using `only [incM, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, map_sum, algebraMap_smul]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Conclude with `map_smul (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E) _ _`. Consider the case `zero => simp [GlobalTheory.LatVacArith.symp_zero_right]`. Consider the case `add a b _ _ ha hb`.

Simplify using `only [GlobalTheory.LatVacArith.symp_add_right, add_smul, Finset.sum_add_distrib]`. Rewrite using `[← ha, ← hb]`. Consider the case `smul a z _ hz => conv_lhs => rw [hz, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Establish `h` using `GlobalTheory.LatVac.symp_smul_smul σ (incM F X.J) (incM F W.J) (-1) 1 a (incM F (Matrix.vecMulVec (-x' p.1) (y' p.2))) z`.

Rewrite `h` using `[one_smul, one_mul]`. Rewrite using `[h, smul_smul]`.
-/
theorem exists_frames {B : Base F E} {X : Spc F E n} {W : Spc F E d} {r s r' s' : ℕ} (hB : B.IsGood σ)
    (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') :
    ∃ (ι : Type) (_ : Fintype ι) (x x' : ι → Fin n → E) (y y' : ι → Fin d → E),
      (∀ i, x i ∈ X.L ∧ x' i ∈ X.L ∧ y i ∈ W.L ∧ y' i ∈ W.L) ∧ ∀ u : Matrix (Fin n) (Fin d) (AE F E),
        u = ∑ i, symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) (incM F (Matrix.vecMulVec (x' i) (y' i))) u •
          incM F (Matrix.vecMulVec (x i) (y i)) := by
  obtain ⟨N, x, x', hx, hx', g, hg, hgs⟩ := frame_X hX
  obtain ⟨N', y, y', hy, hy', hs⟩ := frame_alt_alt hB hW
  refine ⟨Fin N × Fin N', inferInstance, fun p => x p.1, fun p => -x' p.1, fun p => y p.2, fun p => y' p.2,
    fun p => ⟨hx _, neg_mem (hx' _), hy _, hy' _⟩, fun u => ?_⟩
  have hu := GlobalTheory.LatOpenCpt.span_top (F := F) hX.lat hW.lat (fun p : X.L × W.L => Matrix.vecMulVec p.1.1 p.2.1)
    (fun x hx y hy => Submodule.subset_span ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩) u
  induction hu using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, rfl⟩ := hz
    have key : Matrix.vecMulVec a b = ∑ p : Fin N × Fin N',
        Algebra.trace F E (form σ W.J (y' p.2) (g p.1 a • b)) • Matrix.vecMulVec (x p.1) (y p.2) := by
      rw [Fintype.sum_prod_type]
      conv_lhs => rw [← hgs a]
      ext i j
      simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Finset.sum_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      have h := congrFun (hs (g k a • b)) j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h ⊢
      rw [mul_comm (g k a), mul_assoc, ← h, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [mul_smul_comm]
    have hs' : ∀ p : Fin N × Fin N', symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)
        (incM F (Matrix.vecMulVec (-x' p.1) (y' p.2))) (incM F (Matrix.vecMulVec a b)) =
        algebraMap F (AF F) (Algebra.trace F E (form σ W.J (y' p.2) (g p.1 a • b))) := fun p => by
      have h := GlobalTheory.LatVacArith.symp_incM σ X.J W.J (-1) (-x' p.1) a (y' p.2) b
      rw [map_neg, map_one] at h
      rw [h, form_smul, ← hg]
      simp [form]
    simp only [hs']
    conv_lhs => rw [key]
    ext i j
    simp only [incM, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, map_sum, algebraMap_smul]
    refine Finset.sum_congr rfl fun p _ => ?_
    exact map_smul (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E) _ _
  | zero => simp [GlobalTheory.LatVacArith.symp_zero_right]
  | add a b _ _ ha hb =>
    simp only [GlobalTheory.LatVacArith.symp_add_right, add_smul, Finset.sum_add_distrib]
    rw [← ha, ← hb]
  | smul a z _ hz =>
    conv_lhs => rw [hz, Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    have h := GlobalTheory.LatVac.symp_smul_smul σ (incM F X.J) (incM F W.J) (-1) 1 a
      (incM F (Matrix.vecMulVec (-x' p.1) (y' p.2))) z
    rw [one_smul, one_mul] at h
    rw [h, smul_smul]

/- English proof (translation)
Take `⟨ι, _, x, x', y, y', hm, he⟩` from `exists_frames hB hX hW`. Rewrite using `[he u]`. Use `AddSubgroup.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Establish `hat : At (evFin F v) (symp (R` using `AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) (incM F (Matrix.vecMulVec (x' i) (y' i))) u) := fun t ht => by`. Establish `h` using `GlobalTheory.LatVac.symp_smul_smul σ (incM F X.J) (incM F W.J) (-1) 1 t (incM F (Matrix.vecMulVec (x' i) (y' i))) u`.

Rewrite `h` using `[hu t ht, GlobalTheory.LatVacArith.symp_zero_right, one_mul]`. Conclude with `h.symm`. Use `AddSubgroup.subset_closure ⟨_, hat, (hv _).1 fun a ha => ?_, _, (hm i).1, _, (hm i).2.2.1, rfl⟩` and prove the remaining obligations. Establish `h1` using `h _ (AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v a, GlobalTheory.LatVac.at_liftV v a, by rw [GlobalTheory.LatVac.evFin_liftV]; exact ha, _, (hm i).2.1, _, (hm i).2.2.2, rfl⟩)`. Establish `h2` using `GlobalTheory.LatVac.symp_smul_smul σ (incM F X.J) (incM F W.J) (-1) (GlobalTheory.LatVac.liftV v a) 1 (incM F (Matrix.vecMulVec (x' i) (y' i))) u`.

Rewrite `h2` using `[one_smul, mul_one]`. Rewrite `h1` using `[h2, GlobalTheory.StdVacuum.psi_eq_psiLoc _ v _ (GlobalTheory.VacAny.at_mul_left _ hat), map_mul, GlobalTheory.LatVac.evFin_liftV, mul_comm]`. Conclude with `h1`.
-/
theorem mem_latAtV_of_dual {B : Base F E} {X : Spc F E n} {W : Spc F E d} {r s r' s' : ℕ} (hB : B.IsGood σ)
    (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') {v : Pl F} (hv : PsiUnr B.ψ v)
    {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evFin F v) u)
    (h : ∀ γ ∈ latAtV X W v, B.ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) γ u) = 1) :
    u ∈ latAtV X W v := by
  obtain ⟨ι, _, x, x', y, y', hm, he⟩ := exists_frames hB hX hW
  rw [he u]
  refine AddSubgroup.sum_mem _ fun i _ => ?_
  have hat : At (evFin F v) (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)
      (incM F (Matrix.vecMulVec (x' i) (y' i))) u) := fun t ht => by
    have h := GlobalTheory.LatVac.symp_smul_smul σ (incM F X.J) (incM F W.J) (-1) 1 t (incM F (Matrix.vecMulVec (x' i) (y' i))) u
    rw [hu t ht, GlobalTheory.LatVacArith.symp_zero_right, one_mul] at h
    exact h.symm
  refine AddSubgroup.subset_closure ⟨_, hat, (hv _).1 fun a ha => ?_, _, (hm i).1, _, (hm i).2.2.1, rfl⟩
  have h1 := h _ (AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v a, GlobalTheory.LatVac.at_liftV v a,
    by rw [GlobalTheory.LatVac.evFin_liftV]; exact ha, _, (hm i).2.1, _, (hm i).2.2.2, rfl⟩)
  have h2 := GlobalTheory.LatVac.symp_smul_smul σ (incM F X.J) (incM F W.J) (-1) (GlobalTheory.LatVac.liftV v a) 1
    (incM F (Matrix.vecMulVec (x' i) (y' i))) u
  rw [one_smul, mul_one] at h2
  rw [h2, GlobalTheory.StdVacuum.psi_eq_psiLoc _ v _ (GlobalTheory.VacAny.at_mul_left _ hat), map_mul, GlobalTheory.LatVac.evFin_liftV, mul_comm] at h1
  exact h1

end PositivityTheory.ThKH.Evl
