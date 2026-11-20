import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
import ReciprocityTheory.ClassFieldTheory.LocalClassField.InflationH2InjectiveOfSameRamification
import ReciprocityTheory.ClassFieldTheory.LocalClassField.BrBound
import ReciprocityTheory.ClassFieldTheory.LocalClassField.InvRes
import ReciprocityTheory.ClassFieldTheory.LocalClassField.EqZeroOfMemBrKerOfCoprime
import ReciprocityTheory.ClassFieldTheory.LocalClassField.FinCoh

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

/- English proof (translation)
Rewrite using `[← mem_range_layerInfl_Kn_iff hK hn]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy⟩`. Conclude with `⟨y, layer_inflation_h2_injective ((layerInf_layerInfl (Kn_le_Kur hn) 2 y).trans hy)⟩`. Introduce and unpack `⟨y, rfl⟩`.

Conclude with `⟨y, (layerInf_layerInfl (Kn_le_Kur hn) 2 y).symm⟩`.
-/
theorem layerInf_Kur_mem_BrLK_Kn_iff (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) (z : (urT p K).H 2) :
    (layerInf p K (MaximalUnramifiedExtension p K)).hom.H 2 z ∈ BrLK p K (Kn p K n) ↔ n • z = 0 := by
  rw [← mem_range_layerInfl_Kn_iff hK hn]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, layer_inflation_h2_injective ((layerInf_layerInfl (Kn_le_Kur hn) 2 y).trans hy)⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, (layerInf_layerInfl (Kn_le_Kur hn) 2 y).symm⟩

/- English proof (translation)
Establish `hn : 0 < degLK p K L` using `degLK_pos hL`. Introduce `x hx`. Take `⟨z, rfl⟩` from `BrLK_mono (Kn_le_Kur hn) hx`. Establish `hz : degLK p K L • z = 0` using `(layerInf_Kur_mem_BrLK_Kn_iff hK hn z).1 hx`. Take `⟨y, hy, hinv⟩` from `exists_res_ur hK hL h z`.

Rewrite `hinv` using `[← map_nsmul, hz, map_zero]`. Establish `hy0 : y = 0` using `(invUr_bijective hL).1 (hinv.trans (map_zero _).symm)`. Conclude with `hy.trans (by rw [hy0, map_zero])`.
-/
theorem BrLK_Kn_le_BrKer (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) :
    BrLK p K (Kn p K (degLK p K L)) ≤ BrKer h := by
  have hn : 0 < degLK p K L := degLK_pos hL
  intro x hx
  obtain ⟨z, rfl⟩ := BrLK_mono (Kn_le_Kur hn) hx
  have hz : degLK p K L • z = 0 := (layerInf_Kur_mem_BrLK_Kn_iff hK hn z).1 hx
  obtain ⟨y, hy, hinv⟩ := exists_res_ur hK hL h z
  rw [← map_nsmul, hz, map_zero] at hinv
  have hy0 : y = 0 := (invUr_bijective hL).1 (hinv.trans (map_zero _).symm)
  exact hy.trans (by rw [hy0, map_zero])

/- English proof (translation)
Establish `hn : 0 < degLK p K L` using `degLK_pos hL`. Take `⟨hfin, hcard⟩` from `card_BrKer_le hK hL h`. Establish `hle` using `BrLK_Kn_le_BrKer hK hL h`. Establish `hc : Nat.card (BrLK p K (Kn p K (degLK p K L))) = degLK p K L`. Rewrite using `[card_BrLK, card_h2_unramified_layer hK hn]`.

Establish `hset : (BrLK p K (Kn p K (degLK p K L)) : Set (Br p K)) = (BrKer h : Set (Br p K))`. Use `Set.eq_of_subset_of_ncard_le hle ?_ hfin` and prove the remaining obligations. Use `show Nat.card (BrKer h) ≤ Nat.card (BrLK p K (Kn p K (degLK p K L)))`. Rewrite using `[hc]`. Conclude with `hcard`.

Conclude with `(SetLike.coe_injective hset).symm`.
-/
theorem BrKer_eq_BrLK_Kn (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    [(subG p K L).Normal] : BrKer h = BrLK p K (Kn p K (degLK p K L)) := by
  have hn : 0 < degLK p K L := degLK_pos hL
  obtain ⟨hfin, hcard⟩ := card_BrKer_le hK hL h
  have hle := BrLK_Kn_le_BrKer hK hL h
  have hc : Nat.card (BrLK p K (Kn p K (degLK p K L))) = degLK p K L := by
    rw [card_BrLK, card_h2_unramified_layer hK hn]
  have hset : (BrLK p K (Kn p K (degLK p K L)) : Set (Br p K)) = (BrKer h : Set (Br p K)) := by
    refine Set.eq_of_subset_of_ncard_le hle ?_ hfin
    show Nat.card (BrKer h) ≤ Nat.card (BrLK p K (Kn p K (degLK p K L)))
    rw [hc]; exact hcard
  exact (SetLike.coe_injective hset).symm

/- English proof (translation)
Use `⟨layer_inflation_h2_injective, fun x => ?_⟩` and prove the remaining obligations. Take `⟨L, h, hL, hN, hx⟩` from `exists_mem_BrKer hK x`. Rewrite `hx` using `[BrKer_eq_BrLK_Kn hK hL h]`. Conclude with `BrLK_mono (Kn_le_Kur (degLK_pos hL)) hx`.
-/
theorem inflation_unramified_closure_h2_bijective (hK : FiniteDimensional ℚ_[p] K) :
    Bijective ((layerInf p K (MaximalUnramifiedExtension p K)).hom.H 2) := by
  refine ⟨layer_inflation_h2_injective, fun x => ?_⟩
  obtain ⟨L, h, hL, hN, hx⟩ := exists_mem_BrKer hK x
  rw [BrKer_eq_BrLK_Kn hK hL h] at hx
  exact BrLK_mono (Kn_le_Kur (degLK_pos hL)) hx

open Classical in
variable (p K) in

noncomputable def invBr : Br p K →+ QZ :=
  if h : ∃ f : Br p K →+ QZ, ∀ x, f ((layerInf p K (MaximalUnramifiedExtension p K)).hom.H 2 x) = invUr p K x then h.choose else 0

/- English proof (translation)
Establish `h : ∃ f : Br p K →+ QZ, ∀ x, f ((layerInf p K (MaximalUnramifiedExtension p K)).hom.H 2 x) = invUr p K x`. Set `e` to `LinearEquiv.ofBijective ((layerInf p K (MaximalUnramifiedExtension p K)).hom.H 2) (inflation_unramified_closure_h2_bijective hK)`. Use `⟨(invUr p K).comp e.symm.toAddEquiv.toAddMonoidHom, fun x => ?_⟩` and prove the remaining obligations. Use `show invUr p K (e.symm (e x)) = _`. Rewrite using `[LinearEquiv.symm_apply_apply]`.

Unfold `invBr`. Rewrite using `[dif_pos h]`. Conclude with `h.choose_spec x`.
-/
theorem invBr_layerInf (hK : FiniteDimensional ℚ_[p] K) (x : (urT p K).H 2) :
    invBr p K ((layerInf p K (MaximalUnramifiedExtension p K)).hom.H 2 x) = invUr p K x := by
  have h : ∃ f : Br p K →+ QZ, ∀ x, f ((layerInf p K (MaximalUnramifiedExtension p K)).hom.H 2 x) = invUr p K x := by
    let e := LinearEquiv.ofBijective ((layerInf p K (MaximalUnramifiedExtension p K)).hom.H 2) (inflation_unramified_closure_h2_bijective hK)
    refine ⟨(invUr p K).comp e.symm.toAddEquiv.toAddMonoidHom, fun x => ?_⟩
    show invUr p K (e.symm (e x)) = _
    rw [LinearEquiv.symm_apply_apply]
  unfold invBr
  rw [dif_pos h]
  exact h.choose_spec x

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `x y hxy`. Take `⟨a, rfl⟩` from `(inflation_unramified_closure_h2_bijective hK).2 x`. Take `⟨b, rfl⟩` from `(inflation_unramified_closure_h2_bijective hK).2 y`. Rewrite `hxy` using `[invBr_layerInf hK, invBr_layerInf hK]`.

Rewrite using `[(invUr_bijective hK).1 hxy]`. Introduce `q`. Take `⟨a, rfl⟩` from `(invUr_bijective hK).2 q`. Conclude with `⟨_, invBr_layerInf hK a⟩`.
-/
theorem invBr_bijective (hK : FiniteDimensional ℚ_[p] K) : Bijective (invBr p K) := by
  constructor
  · intro x y hxy
    obtain ⟨a, rfl⟩ := (inflation_unramified_closure_h2_bijective hK).2 x
    obtain ⟨b, rfl⟩ := (inflation_unramified_closure_h2_bijective hK).2 y
    rw [invBr_layerInf hK, invBr_layerInf hK] at hxy
    rw [(invUr_bijective hK).1 hxy]
  · intro q
    obtain ⟨a, rfl⟩ := (invUr_bijective hK).2 q
    exact ⟨_, invBr_layerInf hK a⟩

/- English proof (translation)
Take `⟨z, rfl⟩` from `(inflation_unramified_closure_h2_bijective hK).2 x`. Take `⟨y, hy, hinv⟩` from `exists_res_ur hK hL h z`. Rewrite using `[hy, invBr_layerInf hL, invBr_layerInf hK, hinv]`.
-/
theorem invBr_res (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (x : Br p K) :
    invBr p L ((resPair h).hom.H 2 x) = degLK p K L • invBr p K x := by
  obtain ⟨z, rfl⟩ := (inflation_unramified_closure_h2_bijective hK).2 x
  obtain ⟨y, hy, hinv⟩ := exists_res_ur hK hL h z
  rw [hy, invBr_layerInf hL, invBr_layerInf hK, hinv]

variable (p K) in

noncomputable def h2EquivBrauer : H2 (kbarRep p K) ≃+ Br p K := (lowEquiv2 (kbarT p K)).symm.toAddEquiv

end ReciprocityTheory.DiscreteGroups.LocalClassField
