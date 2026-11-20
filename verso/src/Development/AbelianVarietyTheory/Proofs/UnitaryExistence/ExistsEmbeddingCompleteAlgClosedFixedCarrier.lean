import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
import Formalism.LocalToGlobal.ProjectiveLattices.LatPAddRight
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.DepLaws
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsCompleteIsAlgClosedAddValuation
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.MainNotions.DIV.Cons
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmallClosedField

open Cardinal

/- English proof (translation)
Establish `h : ∀ x : C, ∃ s : ℕ → A, Filter.Tendsto (fun n => f (s n)) Filter.atTop (nhds x)`. Introduce `x`. Take `⟨u, hu, hx⟩` from `mem_closure_iff_seq_limit.1 (hf x)`. Use `choose s hs using hu`. Conclude with `⟨s, by simpa [hs] using hx⟩`.

Use `choose s hs using h`. Establish `hinj : Function.Injective s` using `fun x y hxy => tendsto_nhds_unique (hs x) (hxy ▸ hs y)`. Simplify using `using mk_le_of_injective hinj`.
-/
theorem mk_le_of_denseRange {A C : Type} [MetricSpace C] (f : A → C) (hf : DenseRange f) :
    #C ≤ #A ^ ℵ₀ := by
  have h : ∀ x : C, ∃ s : ℕ → A, Filter.Tendsto (fun n => f (s n)) Filter.atTop (nhds x) := by
    intro x
    obtain ⟨u, hu, hx⟩ := mem_closure_iff_seq_limit.1 (hf x)
    choose s hs using hu
    exact ⟨s, by simpa [hs] using hx⟩
  choose s hs using h
  have hinj : Function.Injective s := fun x y hxy =>
    tendsto_nhds_unique (hs x) (hxy ▸ hs y)
  simpa using mk_le_of_injective hinj

/- English proof (translation)
Establish `hfin : ∀ n : ℕ, Finite (V ⧸ maximalIdeal V ^ n)` using `fun n => haveI : Finite (V ⧸ maximalIdeal V) := inferInstanceAs (Finite (ResidueField V)) Ideal.finite_quotient_pow (maximalIdeal V).fg_of_isNoetherianRing n`. Set `f : V → ∀ n : ℕ, V ⧸ maximalIdeal V ^ n` to `fun x n => Ideal.Quotient.mk _ x`. Establish `hinj : Function.Injective f`. Introduce `x y hxy`. Establish `: x - y ∈ ⨅ n : ℕ, maximalIdeal V ^ n` using `Ideal.mem_iInf.2 fun n => Ideal.Quotient.eq.1 (congrFun hxy n)`.

Rewrite `this` using `[Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal V).ne_top]`. Conclude with `sub_eq_zero.1 this`. Use `(mk_le_of_injective hinj).trans ?_` and prove the remaining obligations. Rewrite using `[mk_pi]`. Use `(prod_le_prod _ (fun _ => ℵ₀) fun n => mk_le_aleph0).trans ?_` and prove the remaining obligations.

Simplify using the standard rewrite rules.
-/
theorem mk_le_continuum_of_finite_residueField (V : Type) [CommRing V] [IsLocalRing V]
    [IsNoetherianRing V] [Finite (ResidueField V)] : #V ≤ 𝔠 := by
  have hfin : ∀ n : ℕ, Finite (V ⧸ maximalIdeal V ^ n) := fun n =>
    haveI : Finite (V ⧸ maximalIdeal V) := inferInstanceAs (Finite (ResidueField V))
    Ideal.finite_quotient_pow (maximalIdeal V).fg_of_isNoetherianRing n
  let f : V → ∀ n : ℕ, V ⧸ maximalIdeal V ^ n := fun x n => Ideal.Quotient.mk _ x
  have hinj : Function.Injective f := by
    intro x y hxy
    have : x - y ∈ ⨅ n : ℕ, maximalIdeal V ^ n :=
      Ideal.mem_iInf.2 fun n => Ideal.Quotient.eq.1 (congrFun hxy n)
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal V).ne_top] at this
    exact sub_eq_zero.1 this
  refine (mk_le_of_injective hinj).trans ?_
  rw [mk_pi]
  refine (prod_le_prod _ (fun _ => ℵ₀) fun n => mk_le_aleph0).trans ?_
  simp

/- English proof (translation)
Set `A` to `algebraicClosure K C`. Set `L : Subfield C` to `A.toSubfield.topologicalClosure`. Establish `hAL : A.toSubfield ≤ L` using `A.toSubfield.le_topologicalClosure`. Establish `hKL : ∀ y : K, algebraMap K C y ∈ L` using `fun y => hAL (A.algebraMap_mem y)`. Establish `hcl : IsClosed (L : Set C)` using `A.toSubfield.isClosed_topologicalClosure`.

Use `letI : NontriviallyNormedField L := { (inferInstance : NormedField L) with non_trivial := ⟨⟨_, hKL x⟩, hx⟩ }`. Use `haveI : CompleteSpace L := hcl.completeSpace_coe`. Use `letI : Algebra A L := (Subfield.inclusion hAL : A.toSubfield →+* L).toAlgebra`. Establish `hd : DenseRange (algebraMap A L)` using `(denseRange_inclusion_iff (s := (A.toSubfield : Set C)) (t := (L : Set C)) hAL).2 subset_rfl`. Use `haveI : IsAlgClosed A := IsAlgClosure.isAlgClosed K`.

Use `⟨L, hKL, hcl, isAlgClosed_of_denseRange hd, (mk_le_of_denseRange _ hd).trans ?_⟩` and prove the remaining obligations. Establish `hA : #A ≤ 𝔠` using `(Algebra.IsAlgebraic.cardinalMk_le_max K A).trans (max_le hK aleph0_le_continuum)`. Conclude with `(power_le_power_right hA).trans continuum_power_aleph0.le`.
-/
theorem exists_small_closed_subfield {K C : Type} [Field K] [NontriviallyNormedField C]
    [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [Algebra K C] (hK : #K ≤ 𝔠)
    {x : K} (hx : 1 < ‖algebraMap K C x‖) :
    ∃ L : Subfield C, (∀ y : K, algebraMap K C y ∈ L) ∧ IsClosed (L : Set C) ∧ IsAlgClosed L ∧
      #L ≤ 𝔠 := by
  let A := algebraicClosure K C
  let L : Subfield C := A.toSubfield.topologicalClosure
  have hAL : A.toSubfield ≤ L := A.toSubfield.le_topologicalClosure
  have hKL : ∀ y : K, algebraMap K C y ∈ L := fun y => hAL (A.algebraMap_mem y)
  have hcl : IsClosed (L : Set C) := A.toSubfield.isClosed_topologicalClosure
  letI : NontriviallyNormedField L :=
    { (inferInstance : NormedField L) with non_trivial := ⟨⟨_, hKL x⟩, hx⟩ }
  haveI : CompleteSpace L := hcl.completeSpace_coe
  letI : Algebra A L := (Subfield.inclusion hAL : A.toSubfield →+* L).toAlgebra
  have hd : DenseRange (algebraMap A L) :=
    (denseRange_inclusion_iff (s := (A.toSubfield : Set C)) (t := (L : Set C)) hAL).2 subset_rfl
  haveI : IsAlgClosed A := IsAlgClosure.isAlgClosed K
  refine ⟨L, hKL, hcl, isAlgClosed_of_denseRange hd, (mk_le_of_denseRange _ hd).trans ?_⟩
  have hA : #A ≤ 𝔠 :=
    (Algebra.IsAlgebraic.cardinalMk_le_max K A).trans (max_le hK aleph0_le_continuum)
  exact (power_le_power_right hA).trans continuum_power_aleph0.le

/- English proof (translation)
Establish `hle : #C ≤ #BigT`. Use `hC.trans ?_` and prove the remaining obligations. Rewrite using `[mk_set, mk_set, mk_real]`. Conclude with `(cantor _).le.trans (cantor _).le`. Take `⟨j⟩` from `(Cardinal.le_def _ _).1 hle`.

Set `S : Set BigT` to `Set.range j`. Set `e : S ≃ C` to `(Equiv.ofInjective j j.injective).symm`. Use `letI : Field S := e.field`. Set `r : S ≃+* C` to `e.ringEquiv`. Use `letI : NormedField S := NormedField.induced S C r r.injective`.

Establish `hn : ∀ x : S, ‖x‖ = ‖r x‖` using `fun _ => rfl`. Establish `hn' : ∀ x : C, ‖r.symm x‖ = ‖x‖` using `fun x => by rw [hn, r.apply_symm_apply]`. Use `letI : NontriviallyNormedField S := { (inferInstance : NormedField S) with non_trivial := by`. Take `⟨x, hx⟩` from `NontriviallyNormedField.non_trivial (α := C)`. Conclude with `⟨r.symm x, (hn' x).symm ▸ hx⟩ }`.

Use `haveI : IsUltrametricDist S := IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => by`. Rewrite using `[hn, hn, hn, map_add]`. Conclude with `IsUltrametricDist.norm_add_le_max _ _`. Use `haveI : IsAlgClosed S := IsAlgClosed.of_ringEquiv C S r.symm`. Apply the tactic sequence `have hiso : Isometry r := AddMonoidHomClass.isometry_of_norm r fun x => (hn x).symm`.

Use `haveI : CompleteSpace S := (hiso.isUniformInducing.completeSpace_congr r.surjective).2 inferInstance`. Use `haveI : CharZero S := charZero_of_injective_ringHom (f := r.symm.toRingHom) r.symm.injective`. Conclude with `⟨{ S := S, norm_p := by rw [hn, map_natCast, hp] }, r.symm.toRingHom, hn'⟩`.
-/
theorem exists_scf_isometry {p : ℕ} {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
    [CompleteSpace C] [IsAlgClosed C] [CharZero C] (hp : ‖(p : C)‖ = (p : ℝ)⁻¹) (hC : #C ≤ 𝔠) :
    ∃ (D : SCF p) (e : C →+* ↥D.S), ∀ x, ‖e x‖ = ‖x‖ := by
  have hle : #C ≤ #BigT := by
    refine hC.trans ?_
    rw [mk_set, mk_set, mk_real]
    exact (cantor _).le.trans (cantor _).le
  obtain ⟨j⟩ := (Cardinal.le_def _ _).1 hle
  let S : Set BigT := Set.range j
  let e : S ≃ C := (Equiv.ofInjective j j.injective).symm
  letI : Field S := e.field
  let r : S ≃+* C := e.ringEquiv
  letI : NormedField S := NormedField.induced S C r r.injective
  have hn : ∀ x : S, ‖x‖ = ‖r x‖ := fun _ => rfl
  have hn' : ∀ x : C, ‖r.symm x‖ = ‖x‖ := fun x => by rw [hn, r.apply_symm_apply]
  letI : NontriviallyNormedField S :=
    { (inferInstance : NormedField S) with
      non_trivial := by
        obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := C)
        exact ⟨r.symm x, (hn' x).symm ▸ hx⟩ }
  haveI : IsUltrametricDist S :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => by
      rw [hn, hn, hn, map_add]; exact IsUltrametricDist.norm_add_le_max _ _
  haveI : IsAlgClosed S := IsAlgClosed.of_ringEquiv C S r.symm
  have hiso : Isometry r := AddMonoidHomClass.isometry_of_norm r fun x => (hn x).symm
  haveI : CompleteSpace S :=
    (hiso.isUniformInducing.completeSpace_congr r.surjective).2 inferInstance
  haveI : CharZero S := charZero_of_injective_ringHom (f := r.symm.toRingHom) r.symm.injective
  exact ⟨{ S := S, norm_p := by rw [hn, map_natCast, hp] }, r.symm.toRingHom, hn'⟩

/- English proof (translation)
Use `letI : Algebra V W := φ.toAlgebra`. Use `letI : Algebra V C := ((intO C).subtype.comp g).toAlgebra`. Use `haveI : Module.Finite V W := hf`. Establish `hgC : Function.Injective (algebraMap V C)` using `Subtype.val_injective.comp hg`. Use `haveI : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective V W).2 hφ`.

Use `haveI : FaithfulSMul V C := (faithfulSMul_iff_algebraMap_injective V C).2 hgC`. Set `l : W →ₐ[V] C` to `IsAlgClosed.lift`. Establish `hl : Function.Injective l`. Rewrite using `[RingHom.injective_iff_ker_eq_bot]`. Use `Ideal.eq_bot_of_comap_eq_bot (R := V) ?_` and prove the remaining obligations.

Rewrite using `[eq_bot_iff]`. Introduce `a ha`. Rewrite `ha` using `[Ideal.mem_comap, RingHom.mem_ker, l.commutes]`. Conclude with `(map_eq_zero_iff _ hgC).1 ha`. Establish `hmem : ∀ a : W, l a ∈ intO C`.

Introduce `a`. Establish `hO` using `normIntegers_integers C`. Take `⟨q, hq, hqa⟩` from `(Algebra.IsIntegral.isIntegral (R := V) a).map l`. Set `g₀ : V →+* normIntegers C` to `(algebraMap V C).codRestrict (normIntegers C) fun v => mem_normIntegers_iff.2 (g v).2`. Establish `hint : IsIntegral (normIntegers C) (l a)` using `⟨q.map g₀, hq.map g₀, by rw [Polynomial.eval₂_map]; exact hqa⟩`.

Conclude with `mem_normIntegers_iff.1 (hO.mem_of_integral hint)`. Use `⟨l.toRingHom.codRestrict (intO C) hmem, ?_, fun a b h => hl (congrArg Subtype.val h)⟩` and prove the remaining obligations. Use extensionality with `a`. Conclude with `l.commutes a`.
-/
theorem exists_extension_intO {V W C : Type} [CommRing V] [IsDomain V] [CommRing W] [IsDomain W]
    [NormedField C] [IsUltrametricDist C] [IsAlgClosed C] (g : V →+* intO C) (φ : V →+* W)
    (hg : Function.Injective g) (hφ : Function.Injective φ) (hf : φ.Finite) :
    ∃ g' : W →+* intO C, g'.comp φ = g ∧ Function.Injective g' := by
  letI : Algebra V W := φ.toAlgebra
  letI : Algebra V C := ((intO C).subtype.comp g).toAlgebra
  haveI : Module.Finite V W := hf
  have hgC : Function.Injective (algebraMap V C) := Subtype.val_injective.comp hg
  haveI : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective V W).2 hφ
  haveI : FaithfulSMul V C := (faithfulSMul_iff_algebraMap_injective V C).2 hgC
  let l : W →ₐ[V] C := IsAlgClosed.lift
  have hl : Function.Injective l := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := V) ?_
    rw [eq_bot_iff]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, l.commutes] at ha
    exact (map_eq_zero_iff _ hgC).1 ha
  have hmem : ∀ a : W, l a ∈ intO C := by
    intro a
    have hO := normIntegers_integers C
    obtain ⟨q, hq, hqa⟩ := (Algebra.IsIntegral.isIntegral (R := V) a).map l
    let g₀ : V →+* normIntegers C := (algebraMap V C).codRestrict (normIntegers C) fun v =>
      mem_normIntegers_iff.2 (g v).2
    have hint : IsIntegral (normIntegers C) (l a) :=
      ⟨q.map g₀, hq.map g₀, by rw [Polynomial.eval₂_map]; exact hqa⟩
    exact mem_normIntegers_iff.1 (hO.mem_of_integral hint)
  refine ⟨l.toRingHom.codRestrict (intO C) hmem, ?_, fun a b h => hl (congrArg Subtype.val h)⟩
  ext a
  exact l.commutes a

/- English proof (translation)
Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible W`. Take `⟨n, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hπ`. Rewrite `ha` using `[hπ.maximalIdeal_eq, Ideal.mem_span_singleton]`. Take `⟨c, hc⟩ : (u : W) * π ^ n ∣ a ^ n` from `Units.mul_left_dvd.2 (pow_dvd_pow_of_dvd ha n)`. Establish `h : ‖g a‖ ^ n < 1`.

Rewrite using `[← norm_pow, ← map_pow, hc, map_mul, norm_mul]`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hb (hg c)`. Conclude with `lt_of_not_ge fun h1 => absurd (one_le_pow₀ h1) (not_le.2 h)`.
-/
theorem norm_lt_one_of_mem_maximalIdeal {W C : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [NormedField C] (g : W →+* C) (hg : ∀ a, ‖g a‖ ≤ 1) {b : W}
    (hb0 : b ≠ 0) (hb : ‖g b‖ < 1) {a : W} (ha : a ∈ maximalIdeal W) : ‖g a‖ < 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hπ
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at ha
  obtain ⟨c, hc⟩ : (u : W) * π ^ n ∣ a ^ n := Units.mul_left_dvd.2 (pow_dvd_pow_of_dvd ha n)
  have h : ‖g a‖ ^ n < 1 := by
    rw [← norm_pow, ← map_pow, hc, map_mul, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hb (hg c)
  exact lt_of_not_ge fun h1 => absurd (one_le_pow₀ h1) (not_le.2 h)

/- English proof (translation)
Introduce `T p hp hfin hpm`. Establish `hp0 : (p : T.V) ≠ 0` using `Nat.cast_ne_zero.2 hp.ne_zero`. Establish `h1 : (1 : ℝ) < p` using `by exact_mod_cast hp.one_lt`. Use `⟨?_, fun C g T' φ hg hgm hφ hf => ?_⟩` and prove the remaining obligations. Take `⟨C, _, _, _, _, _, hC, hCp⟩` from `exists_complete_isAlgClosed_of_isDiscreteValuationRing T.V T.Fr hp0 hpm (inv_pos.2 (zero_lt_one.trans h1)) (inv_lt_one_of_one_lt₀ h1) haveI : Finite (ResidueField T.V) := hfin`.

Establish `hK : #T.Fr ≤ 𝔠` using `(IsLocalization.cardinalMk_le (nonZeroDivisors T.V)).trans (mk_le_continuum_of_finite_residueField T.V)`. Establish `hx : 1 < ‖algebraMap T.Fr C (algebraMap T.V T.Fr p)⁻¹‖`. Rewrite using `[map_inv₀, norm_inv, hCp, inv_inv]`. Conclude with `h1`. Take `⟨L, hKL, hcl, hac, hL⟩` from `exists_small_closed_subfield hK hx`.

Use `letI : NontriviallyNormedField L := { (inferInstance : NormedField L) with non_trivial := ⟨⟨_, hKL _⟩, hx⟩ }`. Use `haveI : CompleteSpace L := hcl.completeSpace_coe`. Use `haveI : CharZero T.Fr := charZero_of_injective_ringHom (IsFractionRing.injective T.V T.Fr)`. Set `i : T.Fr →+* L` to `(algebraMap T.Fr C).codRestrict L hKL`. Establish `hi : ∀ y, ‖i y‖ = ‖algebraMap T.Fr C y‖` using `fun _ => rfl`.

Use `haveI : CharZero L := charZero_of_injective_ringHom i.injective`. Establish `hLp : ‖(p : L)‖ = (p : ℝ)⁻¹`. Rewrite using `[← map_natCast i, hi, ← map_natCast (algebraMap T.V T.Fr), hCp]`. Apply the tactic sequence `obtain ⟨D, e, he⟩ := exists_scf_isometry hLp hL`. Establish `hle : ∀ a : T.V, ‖(e.comp i) (algebraMap T.V T.Fr a)‖ ≤ 1` using `fun a => by`.

Rewrite using `[RingHom.comp_apply, he, hi]`. Conclude with `(hC _).2 ⟨a, rfl⟩`. Use `⟨D, e.comp i, hle, fun a ha => ?_⟩` and prove the remaining obligations. Use `norm_lt_one_of_mem_maximalIdeal ((e.comp i).comp (algebraMap T.V T.Fr)) hle hp0 ?_ ha` and prove the remaining obligations. Rewrite using `[map_natCast, D.norm_p]`.

Conclude with `inv_lt_one_of_one_lt₀ h1`. Take `⟨g', hc, hinj⟩` from `exists_extension_intO g φ hg hφ hf`. Use `⟨g', hc, hinj, fun a ha => ?_⟩` and prove the remaining obligations. Use `norm_lt_one_of_mem_maximalIdeal ((intO ↥C.S).subtype.comp g') (fun b => (g' b).2) ((map_ne_zero_iff φ hφ).2 hp0) ?_ ha` and prove the remaining obligations. Use `hgm p hpm` as an intermediate fact.

Rewrite `this` using `[← hc]`. Conclude with `this`.
-/
theorem exists_embedding_and_extension :
    ∀ (T : CDVR) (p : ℕ), p.Prime → T.FinRes → (p : T.V) ∈ maximalIdeal T.V → (∃ (C : SCF p) (eF : T.Fr →+* ↥C.S), (∀ a : T.V, ‖eF (algebraMap T.V T.Fr a)‖ ≤ 1) ∧ ∀ a ∈ maximalIdeal T.V, ‖eF (algebraMap T.V T.Fr a)‖ < 1) ∧ ∀ (C : SCF p) (g : T.V →+* intO ↥C.S) (T' : CDVR) (φ : T.V →+* T'.V), Function.Injective g → (∀ a ∈ maximalIdeal T.V, ‖((g a : intO ↥C.S) : ↥C.S)‖ < 1) → Function.Injective φ → φ.Finite → ∃ g' : T'.V →+* intO ↥C.S, g'.comp φ = g ∧ Function.Injective g' ∧ ∀ a ∈ maximalIdeal T'.V, ‖((g' a : intO ↥C.S) : ↥C.S)‖ < 1 := by
  intro T p hp hfin hpm
  have hp0 : (p : T.V) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  refine ⟨?_, fun C g T' φ hg hgm hφ hf => ?_⟩
  · obtain ⟨C, _, _, _, _, _, hC, hCp⟩ :=
      exists_complete_isAlgClosed_of_isDiscreteValuationRing T.V T.Fr hp0 hpm
        (inv_pos.2 (zero_lt_one.trans h1)) (inv_lt_one_of_one_lt₀ h1)
    haveI : Finite (ResidueField T.V) := hfin
    have hK : #T.Fr ≤ 𝔠 :=
      (IsLocalization.cardinalMk_le (nonZeroDivisors T.V)).trans
        (mk_le_continuum_of_finite_residueField T.V)
    have hx : 1 < ‖algebraMap T.Fr C (algebraMap T.V T.Fr p)⁻¹‖ := by
      rw [map_inv₀, norm_inv, hCp, inv_inv]; exact h1
    obtain ⟨L, hKL, hcl, hac, hL⟩ := exists_small_closed_subfield hK hx
    letI : NontriviallyNormedField L :=
      { (inferInstance : NormedField L) with non_trivial := ⟨⟨_, hKL _⟩, hx⟩ }
    haveI : CompleteSpace L := hcl.completeSpace_coe
    haveI : CharZero T.Fr := charZero_of_injective_ringHom (IsFractionRing.injective T.V T.Fr)
    let i : T.Fr →+* L := (algebraMap T.Fr C).codRestrict L hKL
    have hi : ∀ y, ‖i y‖ = ‖algebraMap T.Fr C y‖ := fun _ => rfl
    haveI : CharZero L := charZero_of_injective_ringHom i.injective
    have hLp : ‖(p : L)‖ = (p : ℝ)⁻¹ := by
      rw [← map_natCast i, hi, ← map_natCast (algebraMap T.V T.Fr), hCp]
    obtain ⟨D, e, he⟩ := exists_scf_isometry hLp hL
    have hle : ∀ a : T.V, ‖(e.comp i) (algebraMap T.V T.Fr a)‖ ≤ 1 := fun a => by
      rw [RingHom.comp_apply, he, hi]; exact (hC _).2 ⟨a, rfl⟩
    refine ⟨D, e.comp i, hle, fun a ha => ?_⟩
    refine norm_lt_one_of_mem_maximalIdeal ((e.comp i).comp (algebraMap T.V T.Fr)) hle hp0 ?_ ha
    rw [map_natCast, D.norm_p]
    exact inv_lt_one_of_one_lt₀ h1
  · obtain ⟨g', hc, hinj⟩ := exists_extension_intO g φ hg hφ hf
    refine ⟨g', hc, hinj, fun a ha => ?_⟩
    refine norm_lt_one_of_mem_maximalIdeal ((intO ↥C.S).subtype.comp g') (fun b => (g' b).2)
      ((map_ne_zero_iff φ hφ).2 hp0) ?_ ha
    have := hgm p hpm
    rw [← hc] at this
    exact this

end GlobalTheory.SmallClosedField
