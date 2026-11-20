import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntValuationNormEqSumResidueDegreeMulStatement

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

namespace GlobalTheory.NormCompat

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add]`.
-/
theorem prod_zpow_const {ι B : Type} [CommGroup B] (c : B) (s : Finset ι) (e : ι → ℤ) :
    ∏ i ∈ s, c ^ e i = c ^ (∑ i ∈ s, e i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add]

/- English proof (translation)
Use `((HeightOneSpectrum.Support.finite (𝓞 F) (x : F)).union (HeightOneSpectrum.Support.finite (𝓞 F) ((x : F)⁻¹))).subset ?_` and prove the remaining obligations. Introduce `v hv`. Establish `h0 : v.valuation F (x : F) ≠ 0` using `by simp`. Break down `lt_or_gt_of_ne hv with h | h` into its components or cases. Use `right show 1 < v.valuation F ((x : F)⁻¹)`.

Rewrite using `[map_inv₀]`. Conclude with `(one_lt_inv₀ (zero_lt_iff.2 h0)).2 h`. Use `left`. Conclude with `h`.
-/
theorem finite_setOf_valuation_ne_one (F : Type) [Field F] [NumberField F] (x : Fˣ) :
    {v : HeightOneSpectrum (𝓞 F) | v.valuation F (x : F) ≠ 1}.Finite := by
  refine ((HeightOneSpectrum.Support.finite (𝓞 F) (x : F)).union
    (HeightOneSpectrum.Support.finite (𝓞 F) ((x : F)⁻¹))).subset ?_
  intro v hv
  have h0 : v.valuation F (x : F) ≠ 0 := by simp
  rcases lt_or_gt_of_ne hv with h | h
  · right
    show 1 < v.valuation F ((x : F)⁻¹)
    rw [map_inv₀]
    exact (one_lt_inv₀ (zero_lt_iff.2 h0)).2 h
  · left
    exact h

/- English proof (translation)
Use `show Valued.v ((b : F) : v.adicCompletion F) = _`. Conclude with `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _`.
-/
theorem valued_locUnit (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (b : Fˣ) :
    Valued.v ((Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom b : (v.adicCompletion F)ˣ) :
      v.adicCompletion F) = v.valuation F (b : F) := by
  show Valued.v ((b : F) : v.adicCompletion F) = _
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _

/- English proof (translation)
Use `set x : (v.adicCompletion F)ˣ := Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom b with hx`. Establish `hb0 : v.valuation F (b : F) ≠ 0` using `by simp`. Establish `hu' : IsUnitAt v (x * ϖ ^ (-ordF v b))`. Unfold `IsUnitAt`. Rewrite using `[Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hx, valued_locUnit, hϖ, ordF, neg_neg, ← WithZero.exp_zsmul, ← WithZero.exp_log hb0, ← WithZero.exp_add, WithZero.log_exp]`.

Simplify using the standard rewrite rules. Establish `h` using `hu _ hu'`. Rewrite `h` using `[map_mul, map_mul, map_zpow, map_zpow, zpow_neg, mul_inv_eq_one]`. Rewrite using `[locUnit_apply, ← hx]`. Conclude with `h`.
-/
theorem map_locUnit_eq_zpow {F B : Type} [Field F] [NumberField F] [CommGroup B] (ψ : Ideles F →* B)
    (v : HeightOneSpectrum (𝓞 F)) (hu : ∀ x, IsUnitAt v x → ψ (localIdele F v x) = 1)
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : IsUnifAt v ϖ) (b : Fˣ) :
    ψ (locUnit F v b) = ψ (localIdele F v ϖ) ^ ordF v b := by
  set x : (v.adicCompletion F)ˣ := Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom b with hx
  have hb0 : v.valuation F (b : F) ≠ 0 := by simp
  have hu' : IsUnitAt v (x * ϖ ^ (-ordF v b)) := by
    unfold IsUnitAt
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hx, valued_locUnit, hϖ, ordF, neg_neg,
      ← WithZero.exp_zsmul, ← WithZero.exp_log hb0, ← WithZero.exp_add, WithZero.log_exp]
    simp
  have h := hu _ hu'
  rw [map_mul, map_mul, map_zpow, map_zpow, zpow_neg, mul_inv_eq_one] at h
  rw [locUnit_apply, ← hx]
  exact h

end GlobalTheory.NormCompat

namespace GlobalTheory.NormCompat

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Both sides reduce to the same expression. Introduce `h`. Conclude with `HeightOneSpectrum.ext h`.
-/
theorem under_eq_iff {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (w : HeightOneSpectrum (𝓞 K)) (v : HeightOneSpectrum (𝓞 E)) :
    w.under (𝓞 E) = v ↔ w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal := by
  constructor
  · rintro rfl; rfl
  · intro h; exact HeightOneSpectrum.ext h

/- English proof (translation)
Establish `h0 : Ideal.map (algebraMap (𝓞 E) (𝓞 K)) v.asIdeal ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]`. Conclude with `v.ne_bot`. Use `(Ideal.finite_factors h0).subset fun w hw => ?_` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq] at hw ⊢`.

Rewrite using `[Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← (under_eq_iff w v).mp hw]`.
-/
theorem finite_setOf_under_eq {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (v : HeightOneSpectrum (𝓞 E)) : {w : HeightOneSpectrum (𝓞 K) | w.under (𝓞 E) = v}.Finite := by
  have h0 : Ideal.map (algebraMap (𝓞 E) (𝓞 K)) v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]
    exact v.ne_bot
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  simp only [Set.mem_setOf_eq] at hw ⊢
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← (under_eq_iff w v).mp hw]

end GlobalTheory.NormCompat

namespace GlobalTheory.NormCompat

/- English proof (translation)
Introduce `E K _ _ _ _ _ B _ ψ1 ψ2 S h2u h1u h1f a`. Use `set Na : Eˣ := Units.map (Algebra.norm E (S := K)) a with hNa`. Establish `hfinE : ((fun w : HeightOneSpectrum (𝓞 K) => w.under (𝓞 E)) '' {w | w.valuation K (a : K) ≠ 1} ∪ {v : HeightOneSpectrum (𝓞 E) | v.valuation E (Na : E) ≠ 1}).Finite` using `((finite_setOf_valuation_ne_one K a).image _).union (finite_setOf_valuation_ne_one E Na)`. Use `set TE : Finset (HeightOneSpectrum (𝓞 E)) := hfinE.toFinset.filter (· ∉ S) with hTE`. Use `set TK : Finset (HeightOneSpectrum (𝓞 K)) := TE.biUnion (fun v => (finite_setOf_under_eq (K := K) v).toFinset) with hTK`.

Establish `memTK : ∀ w, w ∈ TK ↔ w.under (𝓞 E) ∈ TE`. Introduce `w`. Simplify using `only [hTK, Finset.mem_biUnion, Set.Finite.mem_toFinset, Set.mem_setOf_eq]`. Conclude with `⟨fun ⟨v, hv, h⟩ => h ▸ hv, fun h => ⟨_, h, rfl⟩⟩`. Establish `memTE : ∀ v, v ∈ TE ↔ v ∉ S ∧ ((∃ w : HeightOneSpectrum (𝓞 K), w.valuation K (a : K) ≠ 1 ∧ w.under (𝓞 E) = v) ∨ v.valuation E (Na : E) ≠ 1)`.

Introduce `v`. Simplify using `only [hTE, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_image, Set.mem_setOf_eq]`. Conclude with `and_comm`. Establish `hcomap : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = (w.under (𝓞 E)).asIdeal` using `fun w => rfl`. Use `⟨TK, TE, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `w hw v hv h`. Use `((memTE _).mp ((memTK w).mp hw)).1` as an intermediate fact. Rewrite `this` using `[(under_eq_iff w v).mpr h]`. Conclude with `this hv`. Introduce `w hw hS`.

Establish `hS' : w.under (𝓞 E) ∉ S` using `fun h => hS _ h (hcomap w)`. Establish `hval : w.valuation K (a : K) = 1`. Assume the negation of the conclusion as `h`. Conclude with `hw ((memTK w).mpr ((memTE _).mpr ⟨hS', Or.inl ⟨w, h, rfl⟩⟩))`. Rewrite using `[locUnit_apply]`.

Use `h1u _ hS' w (hcomap w) _ ?_` and prove the remaining obligations. Unfold `IsUnitAt`. Rewrite using `[valued_locUnit, hval]`. Introduce `v hv`. Conclude with `((memTE v).mp hv).1`.

Introduce `v hv hS`. Establish `hval : v.valuation E (Na : E) = 1`. Assume the negation of the conclusion as `h`. Conclude with `hv ((memTE v).mpr ⟨hS, Or.inr h⟩)`. Rewrite using `[locUnit_apply]`.

Use `h2u v hS _ ?_` and prove the remaining obligations. Unfold `IsUnitAt`. Rewrite using `[valued_locUnit, hval]`. Use `set c : HeightOneSpectrum (𝓞 E) → B := fun v => ψ2 (localIdele E v (atFin v (unif v))) with hc`. Establish `hK : ∀ w ∈ TK, ψ1 (locUnit K w a) = c (w.under (𝓞 E)) ^ ((w.asIdeal.inertiaDeg (𝓞 E) : ℤ) * ordF w a)`.

Introduce `w hw`. Establish `hS : w.under (𝓞 E) ∉ S` using `((memTE _).mp ((memTK w).mp hw)).1`. Rewrite using `[map_locUnit_eq_zpow ψ1 w (h1u _ hS w (hcomap w)) _ (unif_spec w), h1f _ hS w (hcomap w) _ _ (unif_spec w) (unif_spec _), zpow_mul, zpow_natCast]`. Establish `hE : ∀ v ∈ TE, ψ2 (locUnit E v Na) = c v ^ ordF v Na`. Introduce `v hv`.

Conclude with `map_locUnit_eq_zpow ψ2 v (h2u v ((memTE v).mp hv).1) _ (unif_spec v) Na`. Rewrite using `[Finset.prod_congr rfl hK, Finset.prod_congr rfl hE, ← Finset.prod_fiberwise_of_maps_to (g := fun w : HeightOneSpectrum (𝓞 K) => w.under (𝓞 E)) (t := TE) (fun w hw => (memTK w).mp hw)]`. Use `Finset.prod_congr rfl fun v hv => ?_` and prove the remaining obligations. Establish `hfib : ∀ w ∈ TK.filter (fun w => w.under (𝓞 E) = v), c (w.under (𝓞 E)) = c v`. Introduce `w hw`.

Rewrite using `[(Finset.mem_filter.mp hw).2]`. Rewrite using `[Finset.prod_congr rfl fun w hw => by rw [hfib w hw], prod_zpow_const]`. Use `congr 1`. Establish `hs : ∀ w, w ∈ TK.filter (fun w => w.under (𝓞 E) = v) ↔ w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal`. Introduce `w`.

Rewrite using `[Finset.mem_filter, ← under_eq_iff]`. Prove the components needed by the constructor for the conclusion. Conclude with `fun h => h.2`. Introduce `h`. Conclude with `⟨(memTK w).mpr (h ▸ hv), h⟩`.

Establish `key` using `GlobalTheory.T.intValuation_norm_eq_sum_residueDegree_mul E K v a _ hs`. Simplify using `only [ordF, hNa, Units.coe_map, MonoidHom.coe_coe] at key ⊢`. Rewrite using `[key, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem prod_locUnit_eq_prod_locUnit_norm : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (B : Type) [CommGroup B] (ψ1 : Ideles K →* B) (ψ2 : Ideles E →* B) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ v ∉ S, ∀ x, IsUnitAt v x → ψ2 (localIdele E v x) = 1) → (∀ v ∉ S, ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → ∀ x, IsUnitAt w x → ψ1 (localIdele K w x) = 1) → (∀ v ∉ S, ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → ∀ x ϖ, IsUnifAt w x → IsUnifAt v ϖ → ψ1 (localIdele K w x) = ψ2 (localIdele E v ϖ) ^ w.asIdeal.inertiaDeg (𝓞 E)) → ∀ a : Kˣ, ∃ (TK : Finset (HeightOneSpectrum (𝓞 K))) (TE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w ∈ TK, ∀ v ∈ S, w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) ≠ v.asIdeal) ∧ (∀ w ∉ TK, (∀ v ∈ S, w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) ≠ v.asIdeal) → ψ1 (locUnit K w a) = 1) ∧ (∀ v ∈ TE, v ∉ S) ∧ (∀ v ∉ TE, v ∉ S → ψ2 (locUnit E v (Units.map (Algebra.norm E (S := K)) a)) = 1) ∧ ∏ w ∈ TK, ψ1 (locUnit K w a) = ∏ v ∈ TE, ψ2 (locUnit E v (Units.map (Algebra.norm E (S := K)) a)) := by
  classical
  intro E K _ _ _ _ _ B _ ψ1 ψ2 S h2u h1u h1f a
  set Na : Eˣ := Units.map (Algebra.norm E (S := K)) a with hNa
  have hfinE : ((fun w : HeightOneSpectrum (𝓞 K) => w.under (𝓞 E)) ''
      {w | w.valuation K (a : K) ≠ 1} ∪ {v : HeightOneSpectrum (𝓞 E) | v.valuation E (Na : E) ≠ 1}).Finite :=
    ((finite_setOf_valuation_ne_one K a).image _).union (finite_setOf_valuation_ne_one E Na)
  set TE : Finset (HeightOneSpectrum (𝓞 E)) := hfinE.toFinset.filter (· ∉ S) with hTE
  set TK : Finset (HeightOneSpectrum (𝓞 K)) :=
    TE.biUnion (fun v => (finite_setOf_under_eq (K := K) v).toFinset) with hTK
  have memTK : ∀ w, w ∈ TK ↔ w.under (𝓞 E) ∈ TE := by
    intro w
    simp only [hTK, Finset.mem_biUnion, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact ⟨fun ⟨v, hv, h⟩ => h ▸ hv, fun h => ⟨_, h, rfl⟩⟩
  have memTE : ∀ v, v ∈ TE ↔ v ∉ S ∧ ((∃ w : HeightOneSpectrum (𝓞 K), w.valuation K (a : K) ≠ 1 ∧
      w.under (𝓞 E) = v) ∨ v.valuation E (Na : E) ≠ 1) := by
    intro v
    simp only [hTE, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_image, Set.mem_setOf_eq]
    exact and_comm
  have hcomap : ∀ w : HeightOneSpectrum (𝓞 K),
      w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = (w.under (𝓞 E)).asIdeal := fun w => rfl
  refine ⟨TK, TE, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw v hv h
    have := ((memTE _).mp ((memTK w).mp hw)).1
    rw [(under_eq_iff w v).mpr h] at this
    exact this hv
  · intro w hw hS
    have hS' : w.under (𝓞 E) ∉ S := fun h => hS _ h (hcomap w)
    have hval : w.valuation K (a : K) = 1 := by
      by_contra h
      exact hw ((memTK w).mpr ((memTE _).mpr ⟨hS', Or.inl ⟨w, h, rfl⟩⟩))
    rw [locUnit_apply]
    refine h1u _ hS' w (hcomap w) _ ?_
    unfold IsUnitAt
    rw [valued_locUnit, hval]
  · intro v hv
    exact ((memTE v).mp hv).1
  · intro v hv hS
    have hval : v.valuation E (Na : E) = 1 := by
      by_contra h
      exact hv ((memTE v).mpr ⟨hS, Or.inr h⟩)
    rw [locUnit_apply]
    refine h2u v hS _ ?_
    unfold IsUnitAt
    rw [valued_locUnit, hval]
  ·
    set c : HeightOneSpectrum (𝓞 E) → B := fun v => ψ2 (localIdele E v (atFin v (unif v))) with hc
    have hK : ∀ w ∈ TK, ψ1 (locUnit K w a) =
        c (w.under (𝓞 E)) ^ ((w.asIdeal.inertiaDeg (𝓞 E) : ℤ) * ordF w a) := by
      intro w hw
      have hS : w.under (𝓞 E) ∉ S := ((memTE _).mp ((memTK w).mp hw)).1
      rw [map_locUnit_eq_zpow ψ1 w (h1u _ hS w (hcomap w)) _ (unif_spec w),
        h1f _ hS w (hcomap w) _ _ (unif_spec w) (unif_spec _), zpow_mul, zpow_natCast]
    have hE : ∀ v ∈ TE, ψ2 (locUnit E v Na) = c v ^ ordF v Na := by
      intro v hv
      exact map_locUnit_eq_zpow ψ2 v (h2u v ((memTE v).mp hv).1) _ (unif_spec v) Na
    rw [Finset.prod_congr rfl hK, Finset.prod_congr rfl hE,
      ← Finset.prod_fiberwise_of_maps_to (g := fun w : HeightOneSpectrum (𝓞 K) => w.under (𝓞 E))
        (t := TE) (fun w hw => (memTK w).mp hw)]
    refine Finset.prod_congr rfl fun v hv => ?_
    have hfib : ∀ w ∈ TK.filter (fun w => w.under (𝓞 E) = v), c (w.under (𝓞 E)) = c v := by
      intro w hw
      rw [(Finset.mem_filter.mp hw).2]
    rw [Finset.prod_congr rfl fun w hw => by rw [hfib w hw], prod_zpow_const]
    congr 1
    have hs : ∀ w, w ∈ TK.filter (fun w => w.under (𝓞 E) = v) ↔
        w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal := by
      intro w
      rw [Finset.mem_filter, ← under_eq_iff]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨(memTK w).mpr (h ▸ hv), h⟩
    have key := GlobalTheory.T.intValuation_norm_eq_sum_residueDegree_mul E K v a _ hs
    simp only [ordF, hNa, Units.coe_map, MonoidHom.coe_coe] at key ⊢
    rw [key, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    ring

end GlobalTheory.NormCompat

end
