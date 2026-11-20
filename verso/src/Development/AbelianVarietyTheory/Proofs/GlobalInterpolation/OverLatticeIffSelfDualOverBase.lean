import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SplittingProjection
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.OverPlaceIntegralForm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValuedAlgebraMapLtOneIff

noncomputable section

namespace GlobalTheory.OverCompare

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open scoped TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}

/- English proof (translation)
Take `⟨P, Pb, s, hs, hfac, hker, ⟨iso⟩, hP, hPb, ⟨hle, -, hU⟩, b, φ, e, hfr, hbij, hφ, hrow, -⟩` from `H`. Establish `hs' : SplittingProjection.IsSplitting sp.cm.sig v s` using `⟨hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1⟩`. Establish `hpart1 : SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v N) = SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v (SplittingProjection.dualLb L))` using `SetLike.coe_injective ((coe_partOf_prP hs' _).trans (hP.trans (coe_partOf_prP hs' _).symm))`. Establish `hpart2 : SplittingProjection.partOf (SplittingProjection.prPbar s) (SplittingProjection.locLat v N) = SplittingProjection.partOf (SplittingProjection.prPbar s) (SplittingProjection.locLat v L.Lb)` using `SetLike.coe_injective ((coe_partOf_prPbar hs' _).trans (hPb.trans (coe_partOf_prPbar hs' _).symm))`. Establish `hb : IsFrame (SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v N)) b` using `(isFrame_iff _ _).2 ((coe_partOf_prP hs' _).trans hfr)`.

Establish `huniq : ∀ g' : GL (Fin R.k) (v.adicCompletion F), ∃! g : UPts sp.cm.sig sp.gram0 (v.adicCompletion F), bc (SplittingProjection.prP s) g.1 = g'` using `existsUnique_upts sp.cm.sig sp.gram0 sp.baseGram_isHermitian (gram_matrix_det_unit sp) _ s hs'.2.1`. Establish `hlev : ∀ g ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F), g ∈ levelVL sp.cm.sig sp.gram0 v N ↔ b⁻¹ * bc (SplittingProjection.prP s) g * b ∈ (bc (n` using `Fin R.k) (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).range := by`. Introduce `g hg`. Use `⟨fun h => hbij.mapsTo h, fun h => ?_⟩` and prove the remaining obligations. Take `⟨g', hg', hgg⟩` from `hbij.surjOn h`.

Establish `h1 : bc (SplittingProjection.prP s) g' = bc (SplittingProjection.prP s) g` using `mul_left_cancel (mul_right_cancel (show b⁻¹ * bc (SplittingProjection.prP s) g' * b = b⁻¹ * bc (SplittingProjection.prP s) g * b from hgg))`. Establish `h2 : (⟨g', hg'.1⟩ : UPts sp.cm.sig sp.gram0 (v.adicCompletion F)) = ⟨g, hg⟩` using `(huniq (bc (SplittingProjection.prP s) g)).unique h1 rfl`. Establish `h3 : g' = g` using `congrArg Subtype.val h2`. Conclude with `h3 ▸ hg'`. Establish `hstab : ∀ g ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F), g ∈ levelVL sp.cm.sig sp.gram0 v N ↔ bc (SplittingProjection.prP s) g ∈ stabGL (SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v N))` using `fun g hg => (hlev g hg).trans (hb.mem_stabGL_iff _).symm`.

Take `⟨f, hf⟩` from `hb.exists_fun φ`. Set `ε : L.fM v hv ≃+ IsLocalRing.ResidueField (v.adicCompletionIntegers F)` to `e`. Establish `hfe : ∀ (x : SplittingProjection.locLat v (SplittingProjection.dualLb L)) (y : SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v N)), (∀ i, y.1 i = SplittingProjection.prP s (x.1 i)) → f y = ε (L.fT v hv x)`. Introduce `x y hxy`. Take `⟨z, hz⟩` from `hb.exists_coord y`.

Conclude with `(hf y z hz).trans (hrow x z ((funext hxy).symm.trans hz)).symm`. Establish `hlift : ∀ y : SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v N), ∃ x : SplittingProjection.locLat v (SplittingProjection.dualLb L), ∀ i, y.1 i = SplittingProjection.prP s (x.1 i)`. Introduce `y`. Take `⟨x, hx, hxy⟩` from `(mem_partOf _ (sur_prP hs') _ y.1).1 (hpart1.le y.2)`. Conclude with `⟨⟨x, hx⟩, fun i => (congrFun hxy i).symm⟩`.

Establish `hf0 : f ≠ 0` using `(hf.ne_zero_iff hb).2 hφ`. Establish `hsm : ∀ (a : intV E v) (a' : v.adicCompletionIntegers F), (a' : v.adicCompletion F) = SplittingProjection.prP s a → ∀ (x : SplittingProjection.locLat v (SplittingProjection.dualLb L)) (y : SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v N)), ( …`. Introduce `a a' ha x y hxy`. Use `hfe _ _ fun i => ?_` and prove the remaining obligations. Use `show (a' : v.adicCompletion F) * y.1 i = SplittingProjection.prP s ((a : E ⊗[F] v.adicCompletion F) * x.1 i)`.

Rewrite using `[map_mul, ha, hxy]`. Use `⟨s, hs', fun x hx => hfac x (funext hx), ?_, hpart1, hpart2, huniq, hstab, ⟨b, hb, hlev⟩, f, ε, ?_, hfe, hf0, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← (map_primes hs).1, ← (map_primes hs).2]`. Conclude with `⟨iso⟩`. Introduce `a a' ha m`.

Take `⟨y, hy⟩` from `surjective_of_ne_zero hf0 (ε m)`. Take `⟨x, hx⟩` from `hlift y`. Establish `hm : m = L.fT v hv x` using `ε.injective (hy.symm.trans (hfe x y hx))`. Rewrite using `[← hy, ← map_smul, hsm a a' ha x y hx, hm, (L.fT v hv).map_smul]`. Introduce `y`.

Take `⟨x, hx⟩` from `hlift y`. Rewrite using `[hsm (A.T : intV E v) (A.T : v.adicCompletionIntegers F) (by simp) x y hx, L.fT_T, map_zero]`. Introduce `y`. Take `⟨x, hx⟩` from `hlift y`. Rewrite using `[hfe x y hx, map_eq_zero_iff _ ε.injective, hker x, ← SetLike.mem_coe, coe_partOf_prP hs', show y.1 = OverPlaceIntegralForm.pr₁ s x.1 from funext hx]`.

Introduce `g`. Rewrite using `[hU, Subgroup.mem_inf]`. Use `and_congr_right fun hg => ?_` and prove the remaining obligations. Conclude with `mem_stabFun_iff_part (SplittingProjection.prP s) _ _ (mem_partOf _ (sur_prP hs') _) _ f ε (fun x y hxy => hfe (Submodule.inclusion hle x) y hxy) g hg.2 ((hstab g hg.1).1 hg)`.
-/
theorem localAtT_of_overAt (L : ColLevel R F E sp gp C A clsLat) (N : Submodule (𝓞 E) (Fin R.k → E))
    (v : HeightOneSpectrum (𝓞 F)) (hv : (A.T : 𝓞 F) ∈ v.asIdeal) (H : OverPlaceIntegralForm.OverAt L N v hv) :
    ∃ s, SplittingProjection.LocalAtT L N v hv s := by
  obtain ⟨P, Pb, s, hs, hfac, hker, ⟨iso⟩, hP, hPb, ⟨hle, -, hU⟩, b, φ, e, hfr, hbij, hφ, hrow, -⟩ := H
  have hs' : SplittingProjection.IsSplitting sp.cm.sig v s := ⟨hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1⟩
  have hpart1 : SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v N) =
      SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v (SplittingProjection.dualLb L)) :=
    SetLike.coe_injective ((coe_partOf_prP hs' _).trans (hP.trans (coe_partOf_prP hs' _).symm))
  have hpart2 : SplittingProjection.partOf (SplittingProjection.prPbar s) (SplittingProjection.locLat v N) =
      SplittingProjection.partOf (SplittingProjection.prPbar s) (SplittingProjection.locLat v L.Lb) :=
    SetLike.coe_injective ((coe_partOf_prPbar hs' _).trans (hPb.trans (coe_partOf_prPbar hs' _).symm))
  have hb : IsFrame (SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v N)) b :=
    (isFrame_iff _ _).2 ((coe_partOf_prP hs' _).trans hfr)
  have huniq : ∀ g' : GL (Fin R.k) (v.adicCompletion F),
      ∃! g : UPts sp.cm.sig sp.gram0 (v.adicCompletion F), bc (SplittingProjection.prP s) g.1 = g' :=
    existsUnique_upts sp.cm.sig sp.gram0 sp.baseGram_isHermitian (gram_matrix_det_unit sp) _ s hs'.2.1
  have hlev : ∀ g ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F),
      g ∈ levelVL sp.cm.sig sp.gram0 v N ↔ b⁻¹ * bc (SplittingProjection.prP s) g * b ∈
        (bc (n := Fin R.k) (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).range := by
    intro g hg
    refine ⟨fun h => hbij.mapsTo h, fun h => ?_⟩
    obtain ⟨g', hg', hgg⟩ := hbij.surjOn h
    have h1 : bc (SplittingProjection.prP s) g' = bc (SplittingProjection.prP s) g :=
      mul_left_cancel (mul_right_cancel (show b⁻¹ * bc (SplittingProjection.prP s) g' * b =
        b⁻¹ * bc (SplittingProjection.prP s) g * b from hgg))
    have h2 : (⟨g', hg'.1⟩ : UPts sp.cm.sig sp.gram0 (v.adicCompletion F)) = ⟨g, hg⟩ :=
      (huniq (bc (SplittingProjection.prP s) g)).unique h1 rfl
    have h3 : g' = g := congrArg Subtype.val h2
    exact h3 ▸ hg'
  have hstab : ∀ g ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F),
      g ∈ levelVL sp.cm.sig sp.gram0 v N ↔
        bc (SplittingProjection.prP s) g ∈ stabGL (SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v N)) :=
    fun g hg => (hlev g hg).trans (hb.mem_stabGL_iff _).symm
  obtain ⟨f, hf⟩ := hb.exists_fun φ
  let ε : L.fM v hv ≃+ IsLocalRing.ResidueField (v.adicCompletionIntegers F) := e
  have hfe : ∀ (x : SplittingProjection.locLat v (SplittingProjection.dualLb L))
      (y : SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v N)),
      (∀ i, y.1 i = SplittingProjection.prP s (x.1 i)) → f y = ε (L.fT v hv x) := by
    intro x y hxy
    obtain ⟨z, hz⟩ := hb.exists_coord y
    exact (hf y z hz).trans (hrow x z ((funext hxy).symm.trans hz)).symm
  have hlift : ∀ y : SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v N),
      ∃ x : SplittingProjection.locLat v (SplittingProjection.dualLb L), ∀ i, y.1 i = SplittingProjection.prP s (x.1 i) := by
    intro y
    obtain ⟨x, hx, hxy⟩ := (mem_partOf _ (sur_prP hs') _ y.1).1 (hpart1.le y.2)
    exact ⟨⟨x, hx⟩, fun i => (congrFun hxy i).symm⟩
  have hf0 : f ≠ 0 := (hf.ne_zero_iff hb).2 hφ
  have hsm : ∀ (a : intV E v) (a' : v.adicCompletionIntegers F),
      (a' : v.adicCompletion F) = SplittingProjection.prP s a →
      ∀ (x : SplittingProjection.locLat v (SplittingProjection.dualLb L))
      (y : SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v N)),
      (∀ i, y.1 i = SplittingProjection.prP s (x.1 i)) → f (a' • y) = ε (L.fT v hv (a • x)) := by
    intro a a' ha x y hxy
    refine hfe _ _ fun i => ?_
    show (a' : v.adicCompletion F) * y.1 i = SplittingProjection.prP s ((a : E ⊗[F] v.adicCompletion F) * x.1 i)
    rw [map_mul, ha, hxy]
  refine ⟨s, hs', fun x hx => hfac x (funext hx), ?_, hpart1, hpart2, huniq, hstab, ⟨b, hb, hlev⟩,
    f, ε, ?_, hfe, hf0, ?_, ?_, ?_⟩
  · rw [← (map_primes hs).1, ← (map_primes hs).2]
    exact ⟨iso⟩
  · intro a a' ha m
    obtain ⟨y, hy⟩ := surjective_of_ne_zero hf0 (ε m)
    obtain ⟨x, hx⟩ := hlift y
    have hm : m = L.fT v hv x := ε.injective (hy.symm.trans (hfe x y hx))
    rw [← hy, ← map_smul, hsm a a' ha x y hx, hm, (L.fT v hv).map_smul]
  · intro y
    obtain ⟨x, hx⟩ := hlift y
    rw [hsm (A.T : intV E v) (A.T : v.adicCompletionIntegers F) (by simp) x y hx, L.fT_T, map_zero]
  · intro y
    obtain ⟨x, hx⟩ := hlift y
    rw [hfe x y hx, map_eq_zero_iff _ ε.injective, hker x, ← SetLike.mem_coe, coe_partOf_prP hs',
      show y.1 = OverPlaceIntegralForm.pr₁ s x.1 from funext hx]
  · intro g
    rw [hU, Subgroup.mem_inf]
    refine and_congr_right fun hg => ?_
    exact mem_stabFun_iff_part (SplittingProjection.prP s) _ _ (mem_partOf _ (sur_prP hs') _) _ f ε
      (fun x y hxy => hfe (Submodule.inclusion hle x) y hxy) g hg.2 ((hstab g hg.1).1 hg)

/- English proof (translation)
Take `⟨hs', hfac, ⟨iso⟩, hpart1, hpart2, huniq, hstab, ⟨b, hb, hlev⟩, f, ε, -, hfe, hf0, -, hker, hU⟩` from `H`. Use `replace hb : IsFrame (SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v N)) b := hb`. Take `⟨P, Pb, hs⟩` from `exists_primes sp.cm.deg2 hs'`. Take `⟨φ, hf⟩` from `hb.exists_row f`. Establish `hle : OverPlaceIntegralForm.latV v N ≤ OverPlaceIntegralForm.latV v (OverPlaceIntegralForm.baseDual L)` using `Submodule.span_mono (Set.image_mono hN)`.

Establish `hmem : ∀ x : SplittingProjection.locLat v (SplittingProjection.dualLb L), OverPlaceIntegralForm.pr₁ s x.1 ∈ SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v N)` using `fun x => by`. Rewrite using `[hpart1]`. Conclude with `Submodule.subset_span ⟨x.1, x.2, rfl⟩`. Use `⟨P, Pb, s, hs, fun x hx => hfac x (congrFun hx), ?_, ?_, ?_, ?_, ⟨hle, ?_, ?_⟩, b, φ, ε, ?_, ⟨?_, ?_, ?_⟩, (hf.ne_zero_iff hb).1 hf0, ?_, ?_⟩` and prove the remaining obligations. Introduce `x`.

Rewrite using `[← coe_partOf_prP hs', SetLike.mem_coe, ← map_eq_zero_iff _ ε.injective, ← hfe x ⟨_, hmem x⟩ (fun _ => rfl)]`. Conclude with `hker _`. Rewrite using `[(map_primes hs).1, (map_primes hs).2]`. Conclude with `⟨iso⟩`. Rewrite using `[← coe_partOf_prP hs', ← coe_partOf_prP hs', hpart1]`.

Rewrite using `[← coe_partOf_prPbar hs', ← coe_partOf_prPbar hs', hpart2]`. Introduce `h0`. Apply `hf0` to reduce the goal to its premises. Use extensionality with `y`. Take `⟨x, hx, hxy⟩` from `(mem_partOf _ (sur_prP hs') _ y.1).1 y.2`.

Establish `h1` using `hfe (Submodule.inclusion hle ⟨x, hx⟩) y (fun i => (congrFun hxy i).symm)`. Establish `h2 : L.fT v hv (Submodule.inclusion hle ⟨x, hx⟩) = 0` using `LinearMap.congr_fun h0 ⟨x, hx⟩`. Rewrite using `[h1, h2, map_zero, LinearMap.zero_apply]`. Use extensionality with `g`. Rewrite using `[hU, Subgroup.mem_inf]`.

Use `and_congr_right fun hg => ?_` and prove the remaining obligations. Conclude with `(mem_stabFun_iff_part (SplittingProjection.prP s) _ _ (mem_partOf _ (sur_prP hs') _) _ f ε (fun x y hxy => hfe (Submodule.inclusion hle x) y hxy) g hg.2 ((hstab g hg.1).1 hg)).symm`. Conclude with `(coe_partOf_prP hs' _).symm.trans ((isFrame_iff _ _).1 hb)`. Conclude with `fun g hg => (hlev g hg.1).1 hg`. Introduce `g hg g' hg' hgg`.

Establish `h1 : bc (SplittingProjection.prP s) g = bc (SplittingProjection.prP s) g'` using `mul_left_cancel (mul_right_cancel (show b⁻¹ * bc (SplittingProjection.prP s) g * b = b⁻¹ * bc (SplittingProjection.prP s) g' * b from hgg))`. Establish `h2 : (⟨g, hg.1⟩ : UPts sp.cm.sig sp.gram0 (v.adicCompletion F)) = ⟨g', hg'.1⟩` using `(huniq (bc (SplittingProjection.prP s) g')).unique h1 rfl`. Conclude with `congrArg Subtype.val h2`. Introduce `u hu`. Take `⟨g, hg, -⟩` from `huniq (b * u * b⁻¹)`.

Establish `h1 : b⁻¹ * bc (SplittingProjection.prP s) g.1 * b = u` using `by rw [hg]; group`. Conclude with `⟨g.1, (hlev g.1 g.2).2 (h1 ▸ hu), h1⟩`. Introduce `x y hxy`. Conclude with `(hfe x ⟨_, hmem x⟩ (fun _ => rfl)).symm.trans (hf _ y hxy)`. Introduce `g hg`.

Use `(hU g).trans (Iff.trans ⟨fun h => h.2, fun h => ⟨(hstab g hg).2 h.1, h⟩⟩ ?_)` and prove the remaining obligations. Conclude with `hf.mem_stabFun_iff hb _`.
-/
theorem overAt_of_localAtT (L : ColLevel R F E sp gp C A clsLat) (N : Submodule (𝓞 E) (Fin R.k → E))
    (hN : N ≤ SplittingProjection.dualLb L)
    (v : HeightOneSpectrum (𝓞 F)) (hv : (A.T : 𝓞 F) ∈ v.asIdeal)
    (s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (H : SplittingProjection.LocalAtT L N v hv s) : OverPlaceIntegralForm.OverAt L N v hv := by
  obtain ⟨hs', hfac, ⟨iso⟩, hpart1, hpart2, huniq, hstab, ⟨b, hb, hlev⟩, f, ε, -, hfe, hf0, -, hker,
    hU⟩ := H
  replace hb : IsFrame (SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v N)) b := hb
  obtain ⟨P, Pb, hs⟩ := exists_primes sp.cm.deg2 hs'
  obtain ⟨φ, hf⟩ := hb.exists_row f
  have hle : OverPlaceIntegralForm.latV v N ≤ OverPlaceIntegralForm.latV v (OverPlaceIntegralForm.baseDual L) :=
    Submodule.span_mono (Set.image_mono hN)
  have hmem : ∀ x : SplittingProjection.locLat v (SplittingProjection.dualLb L),
      OverPlaceIntegralForm.pr₁ s x.1 ∈ SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v N) := fun x => by
    rw [hpart1]
    exact Submodule.subset_span ⟨x.1, x.2, rfl⟩
  refine ⟨P, Pb, s, hs, fun x hx => hfac x (congrFun hx), ?_, ?_, ?_, ?_, ⟨hle, ?_, ?_⟩, b, φ, ε,
    ?_, ⟨?_, ?_, ?_⟩, (hf.ne_zero_iff hb).1 hf0, ?_, ?_⟩
  · intro x
    rw [← coe_partOf_prP hs', SetLike.mem_coe, ← map_eq_zero_iff _ ε.injective,
      ← hfe x ⟨_, hmem x⟩ (fun _ => rfl)]
    exact hker _
  · rw [(map_primes hs).1, (map_primes hs).2]
    exact ⟨iso⟩
  · rw [← coe_partOf_prP hs', ← coe_partOf_prP hs', hpart1]
  · rw [← coe_partOf_prPbar hs', ← coe_partOf_prPbar hs', hpart2]
  · intro h0
    apply hf0
    ext y
    obtain ⟨x, hx, hxy⟩ := (mem_partOf _ (sur_prP hs') _ y.1).1 y.2
    have h1 := hfe (Submodule.inclusion hle ⟨x, hx⟩) y (fun i => (congrFun hxy i).symm)
    have h2 : L.fT v hv (Submodule.inclusion hle ⟨x, hx⟩) = 0 := LinearMap.congr_fun h0 ⟨x, hx⟩
    rw [h1, h2, map_zero, LinearMap.zero_apply]
  · ext g
    rw [hU, Subgroup.mem_inf]
    refine and_congr_right fun hg => ?_
    exact (mem_stabFun_iff_part (SplittingProjection.prP s) _ _ (mem_partOf _ (sur_prP hs') _) _ f ε
      (fun x y hxy => hfe (Submodule.inclusion hle x) y hxy) g hg.2 ((hstab g hg.1).1 hg)).symm
  · exact (coe_partOf_prP hs' _).symm.trans ((isFrame_iff _ _).1 hb)
  · exact fun g hg => (hlev g hg.1).1 hg
  · intro g hg g' hg' hgg
    have h1 : bc (SplittingProjection.prP s) g = bc (SplittingProjection.prP s) g' :=
      mul_left_cancel (mul_right_cancel (show b⁻¹ * bc (SplittingProjection.prP s) g * b =
        b⁻¹ * bc (SplittingProjection.prP s) g' * b from hgg))
    have h2 : (⟨g, hg.1⟩ : UPts sp.cm.sig sp.gram0 (v.adicCompletion F)) = ⟨g', hg'.1⟩ :=
      (huniq (bc (SplittingProjection.prP s) g')).unique h1 rfl
    exact congrArg Subtype.val h2
  · intro u hu
    obtain ⟨g, hg, -⟩ := huniq (b * u * b⁻¹)
    have h1 : b⁻¹ * bc (SplittingProjection.prP s) g.1 * b = u := by rw [hg]; group
    exact ⟨g.1, (hlev g.1 g.2).2 (h1 ▸ hu), h1⟩
  · intro x y hxy
    exact (hfe x ⟨_, hmem x⟩ (fun _ => rfl)).symm.trans (hf _ y hxy)
  · intro g hg
    refine (hU g).trans (Iff.trans ⟨fun h => h.2, fun h => ⟨(hstab g hg).2 h.1, h⟩⟩ ?_)
    exact hf.mem_stabFun_iff hb _

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2, h3, h4, h5, h6, h7, h8⟩`. Use `⟨⟨h1, h2, h3, h4, fun x hx => Submodule.subset_span (h5 hx), h6⟩, fun v hv => localAtT_of_overAt L N v hv (h7 v hv), fun v => ?_, h8⟩` and prove the remaining obligations. Distinguish the cases in `hv : (A.T : 𝓞 F) ∈ v.asIdeal`. Take `⟨P, Pb, s, -, -, -, -, -, -, ⟨hle, -, hU⟩, -⟩` from `h7 v hv`.

Rewrite using `[hU]`. Conclude with `inf_le_left`. Establish `: levelVL sp.cm.sig sp.gram0 v N = levelVL sp.cm.sig sp.gram0 v L.Lb` using `congrArg (level _ _) (h6 v hv)`. Rewrite using `[this]`. Conclude with `L.Uloc_lev v`.

Introduce and unpack `⟨⟨h1, h2, h3, h4, h5, h6⟩, h7, -, h8⟩`. Use `⟨h1, h2, h3, h4, fun y hy x hx => ?_, h6, fun v hv => ?_, h8⟩` and prove the remaining obligations. Rewrite `hy` using `[← h3]`. Conclude with `hy x (h4 hx)`. Take `⟨s, hs⟩` from `h7 v hv`.

Conclude with `overAt_of_localAtT L N h5 v hv s hs`.
-/
theorem isOverLattice_iff (L : ColLevel R F E sp gp C A clsLat) (N : Submodule (𝓞 E) (Fin R.k → E)) :
    OverPlaceIntegralForm.IsOverLattice L N ↔
      (SplittingProjection.IsOverLattice L N ∧
        (∀ (v : HeightOneSpectrum (𝓞 F)) (h : (A.T : 𝓞 F) ∈ v.asIdeal),
          ∃ φ, SplittingProjection.LocalAtT L N v h φ) ∧
        (∀ v, L.Uloc v ≤ levelVL sp.cm.sig sp.gram0 v N) ∧
        L.U ≤ levelAfL sp.cm.sig sp.gram0 N) := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    refine ⟨⟨h1, h2, h3, h4, fun x hx => Submodule.subset_span (h5 hx), h6⟩,
      fun v hv => localAtT_of_overAt L N v hv (h7 v hv), fun v => ?_, h8⟩
    by_cases hv : (A.T : 𝓞 F) ∈ v.asIdeal
    · obtain ⟨P, Pb, s, -, -, -, -, -, -, ⟨hle, -, hU⟩, -⟩ := h7 v hv
      rw [hU]; exact inf_le_left
    · have : levelVL sp.cm.sig sp.gram0 v N = levelVL sp.cm.sig sp.gram0 v L.Lb :=
        congrArg (level _ _) (h6 v hv)
      rw [this]; exact L.Uloc_lev v
  · rintro ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7, -, h8⟩
    refine ⟨h1, h2, h3, h4, fun y hy x hx => ?_, h6, fun v hv => ?_, h8⟩
    · rw [← h3] at hy
      exact hy x (h4 hx)
    · obtain ⟨s, hs⟩ := h7 v hv
      exact overAt_of_localAtT L N h5 v hv s hs

/- English proof (translation)
Use `letI := D.host.cmStar`. Conclude with `imp_congr_right fun _ => and_congr_right fun _ => exists_congr fun N => isOverLattice_iff (Lv u) N`.
-/
theorem overLatticeAt_iff (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    OverPlaceIntegralForm.OverLatticeAt D Lv u ↔
      (letI := D.host.cmStar
       Formalism.MainNotions.StandardLattice.SplitsF D (D.mem u).A.T → SplittingProjection.HasOverLattice (Lv u)) := by
  letI := D.host.cmStar
  exact imp_congr_right fun _ => and_congr_right fun _ =>
    exists_congr fun N => isOverLattice_iff (Lv u) N

/- English proof (translation)
The claim follows from `forall_congr' fun D => forall_congr' fun Lv => forall_congr' fun u => overLatticeAt_iff D Lv u`.
-/
theorem overLattice_iff_selfDualOverBase : OverPlaceIntegralForm.OverLattice ↔ SplittingProjection.SelfDualOverBase :=
  forall_congr' fun D => forall_congr' fun Lv => forall_congr' fun u => overLatticeAt_iff D Lv u

end GlobalTheory.OverCompare

end
