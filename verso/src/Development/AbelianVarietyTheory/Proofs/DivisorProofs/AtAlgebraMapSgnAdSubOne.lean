import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.RealLift

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU Classical

section SignAdele

variable {F : Type} [Field F] [NumberField F]

def sgnAd (w : InfinitePlace F) : AF F :=
  (((fun v : InfinitePlace F => (if v = w then -1 else 1 : v.Completion)) : Ainf F), (1 : Af F))

/- English proof (translation)
Use `Prod.ext (funext fun v => ?_) (mul_one _)` and prove the remaining obligations. Use `show (if v = w then -1 else 1 : v.Completion) * (if v = w then -1 else 1) = 1`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem sgnAd_mul_self (w : InfinitePlace F) : sgnAd w * sgnAd w = 1 := by
  refine Prod.ext (funext fun v => ?_) (mul_one _)
  show (if v = w then -1 else 1 : v.Completion) * (if v = w then -1 else 1) = 1
  split_ifs <;> simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evInf_sgnAd (w v : InfinitePlace F) : evInf F v (sgnAd w) = if v = w then -1 else 1 := rfl

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Unfold `piInf`. Rewrite using `[RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply]`. Simplify using `[compInf]`.
-/
theorem piInf_algebraMap {v : InfinitePlace F} (τ : EmbOver E v) (y : AF F) :
    piInf τ (algebraMap (AF F) (AE F E) y) = InfinitePlace.Completion.extensionEmbedding v (evInf F v y) := by
  unfold piInf
  rw [RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply]
  simp [compInf]

/- English proof (translation)
Introduce `u hu`. Establish `h1 : u.1 = 0` using `(InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)`. Establish `h2 : u * (sgnAd w - 1) = 0`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show u.1 * _ = 0`.

Rewrite using `[h1, zero_mul]`. Use `show u.2 * ((1 : Af F) - 1) = 0`. Rewrite using `[sub_self, mul_zero]`. Rewrite using `[← map_one (algebraMap (AF F) (AE F E)), ← map_sub, Algebra.smul_def, ← map_mul, h2, map_zero]`.
-/
theorem at_algebraMap_sgnAd_sub_one (w : InfinitePlace F) :
    At (evI F) (algebraMap (AF F) (AE F E) (sgnAd w) - 1) := by
  intro u hu
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  have h2 : u * (sgnAd w - 1) = 0 := by
    refine Prod.ext ?_ ?_
    · show u.1 * _ = 0
      rw [h1, zero_mul]
    · show u.2 * ((1 : Af F) - 1) = 0
      rw [sub_self, mul_zero]
  rw [← map_one (algebraMap (AF F) (AE F E)), ← map_sub, Algebra.smul_def, ← map_mul, h2, map_zero]

end SignAdele

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a a' G X om om' hT w`. Set `u : (AF F)ˣ` to `⟨sgnAd w, sgnAd w, sgnAd_mul_self w, sgnAd_mul_self w⟩`. Set `z : (AE F E)ˣ` to `Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) u`. Establish `hz : At (evI F) ((z : AE F E) - 1)` using `at_algebraMap_sgnAd_sub_one w`. Establish `hpi : ∀ v, piInf (B.emb v) (z : AE F E) = if v = w then -1 else 1`.

Introduce `v`. Use `show piInf (B.emb v) (algebraMap (AF F) (AE F E) (sgnAd w)) = _`. Rewrite using `[piInf_algebraMap, evInf_sgnAd]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hexp : ∀ m : InfinitePlace F → ℤ, ∏ v, (piInf (B.emb v) (z : AE F E) / ‖piInf (B.emb v) (z : AE F E)‖) ^ m v = (-1 : ℂ) ^ m w`.

Introduce `m`. Rewrite using `[Finset.prod_eq_single w (fun v _ hv => by rw [hpi, if_neg hv]; simp) (fun h => absurd (Finset.mem_univ w) h), hpi, if_pos rfl]`. Simplify using the standard rewrite rules. Establish `eα` using `hT.chars.expα z hz`. Establish `eβ` using `hT.chars.expβ z hz`.

Rewrite `eα`, `eβ` using `[hexp]`. Establish `rα : (X.α z : ℂ) = _` using `hT.chars.resα u`. Establish `rβ : (X.β z : ℂ) = _` using `hT.chars.resβ u`. Establish `hpar : ((-1 : ℂ)) ^ a' = (-1) ^ a`. Establish `he` using `hT.geo.even`.

Break down `Nat.even_or_odd a with ha | ha` into its components or cases. Rewrite using `[ha.neg_one_pow, ((Nat.even_add.1 he).1 ha).neg_one_pow]`. Establish `ha' : Odd a'` using `Nat.not_even_iff_odd.1 fun h => Nat.not_even_iff_odd.2 ha ((Nat.even_add.1 he).2 h)`. Rewrite using `[ha.neg_one_pow, ha'.neg_one_pow]`. Establish `hab : (-1 : ℂ) ^ B.mα w = (-1) ^ B.mβ w`.

Rewrite using `[← eα, ← eβ, rα, rβ, hpar]`. Break down `Int.even_or_odd (B.mα w - B.mβ w) with h | h` into its components or cases. Conclude with `h`. It suffices to derive a contradiction. Establish `h1` using `h.neg_one_zpow (α := ℂ)`.

Rewrite `h1` using `[zpow_sub₀ (by norm_num), hab, div_self (zpow_ne_zero _ (by norm_num))]`. Evaluate the numerical expressions using `at h1`.
-/
theorem even_im_hermitian_sub : Parity := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT w
  let u : (AF F)ˣ := ⟨sgnAd w, sgnAd w, sgnAd_mul_self w, sgnAd_mul_self w⟩
  let z : (AE F E)ˣ := Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) u
  have hz : At (evI F) ((z : AE F E) - 1) := at_algebraMap_sgnAd_sub_one w
  have hpi : ∀ v, piInf (B.emb v) (z : AE F E) = if v = w then -1 else 1 := by
    intro v
    show piInf (B.emb v) (algebraMap (AF F) (AE F E) (sgnAd w)) = _
    rw [piInf_algebraMap, evInf_sgnAd]
    split_ifs <;> simp
  have hexp : ∀ m : InfinitePlace F → ℤ,
      ∏ v, (piInf (B.emb v) (z : AE F E) / ‖piInf (B.emb v) (z : AE F E)‖) ^ m v = (-1 : ℂ) ^ m w := by
    intro m
    rw [Finset.prod_eq_single w (fun v _ hv => by rw [hpi, if_neg hv]; simp) (fun h => absurd (Finset.mem_univ w) h),
      hpi, if_pos rfl]
    simp
  have eα := hT.chars.expα z hz
  have eβ := hT.chars.expβ z hz
  rw [hexp] at eα eβ
  have rα : (X.α z : ℂ) = _ := hT.chars.resα u
  have rβ : (X.β z : ℂ) = _ := hT.chars.resβ u
  have hpar : ((-1 : ℂ)) ^ a' = (-1) ^ a := by
    have he := hT.geo.even
    rcases Nat.even_or_odd a with ha | ha
    · rw [ha.neg_one_pow, ((Nat.even_add.1 he).1 ha).neg_one_pow]
    · have ha' : Odd a' := Nat.not_even_iff_odd.1 fun h => Nat.not_even_iff_odd.2 ha ((Nat.even_add.1 he).2 h)
      rw [ha.neg_one_pow, ha'.neg_one_pow]
  have hab : (-1 : ℂ) ^ B.mα w = (-1) ^ B.mβ w := by
    rw [← eα, ← eβ, rα, rβ, hpar]
  rcases Int.even_or_odd (B.mα w - B.mβ w) with h | h
  · exact h
  · exfalso
    have h1 := h.neg_one_zpow (α := ℂ)
    rw [zpow_sub₀ (by norm_num), hab, div_self (zpow_ne_zero _ (by norm_num))] at h1
    norm_num at h1
end GlobalTheory.RealLift
