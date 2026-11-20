import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceAtIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExOneEqSelf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestExistsCombinationsOfExpansion
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ProdDatum

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum

section Gen

variable {D : D7} {S T : HSp D}

def tens (a b : AE D) (Φ Ψ : WO S T → ℂ) : WO S T → ℂ :=
  fun y => if IsHalf (a + b) y then Φ (a • y) * Ψ (b • y) else 0

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => Matrix.ext fun i j => h i j, fun h i j => congrFun (congrFun h i) j⟩`.
-/
theorem half_iff {a : AE D} {y : WO S T} : IsHalf a y ↔ a • y = y :=
  ⟨fun h => Matrix.ext fun i j => h i j, fun h i j => congrFun (congrFun h i) j⟩

/- English proof (translation)
Use function extensionality and compare the values at `y`. Unfold `tens`. Rewrite using `[add_comm b a, mul_comm]`.
-/
theorem tens_comm (a b : AE D) (Φ Ψ : WO S T → ℂ) : tens a b Φ Ψ = tens b a Ψ Φ := by
  funext y
  unfold tens
  rw [add_comm b a, mul_comm]

def tensL (a b : AE D) (Φ : WO S T → ℂ) : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun := tens a b Φ
  map_add' Ψ Ψ' := by
    funext y
    simp only [tens, Pi.add_apply]
    split_ifs <;> ring
  map_smul' c Ψ := by
    funext y
    simp only [tens, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

/- English proof (translation)
Rewrite `hu` using `[half_iff]`. Rewrite using `[half_iff, half_iff, smul_add, hu, add_left_inj]`.
-/
theorem half_add_iff {e : AE D} {u : WO S T} (hu : IsHalf e u) (t : WO S T) : IsHalf e (t + u) ↔ IsHalf e t := by
  rw [half_iff] at hu
  rw [half_iff, half_iff, smul_add, hu, add_left_inj]

/- English proof (translation)
Rewrite using `[smul_comm a, mul_smul]`.
-/
theorem aux1 {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (a : R) (k l : ℕ) (u : M) :
    a • ((k * l) • u) = k • (l • (a • u)) := by rw [smul_comm a, mul_smul]

/- English proof (translation)
Rewrite using `[smul_comm a l, smul_smul a, ha]`.
-/
theorem aux2 {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {a : R} (ha : a * a = a) (l : ℕ) (u : M) :
    a • (l • (a • u)) = l • (a • u) := by rw [smul_comm a l, smul_smul a, ha]

/- English proof (translation)
Rewrite using `[← mul_smul l k, ← mul_smul k l, mul_comm l k, ← smul_add, ← add_smul, h]`.
-/
theorem aux3 {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {a b : R} (k l : ℕ) {t : M} (h : (a + b) • t = t) :
    (k * l) • t = l • (k • (a • t)) + k • (l • (b • t)) := by
  rw [← mul_smul l k, ← mul_smul k l, mul_comm l k, ← smul_add, ← add_smul, h]

/- English proof (translation)
Rewrite using `[smul_comm, h]`.
-/
theorem aux4 {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {a : R} (k : ℕ) {t : M} (h : a • t = t) :
    a • (k • t) = k • t := by rw [smul_comm, h]

variable {a b : AE D} {Λ : AddSubgroup (WO S T)}

/- English proof (translation)
Take `⟨-, k, hk, h2, h3⟩` from `hΦ`. Take `⟨-, l, hl, g2, g3⟩` from `hΨ`. Use `⟨fun t ht => ?_, k * l, Nat.mul_pos hk hl, fun u hu hh t => ?_, fun t ht => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Conclude with `ht (if_neg h)`.

Establish `hh' : IsHalf (a + b) ((k * l) • u)` using `half_iff.2 (aux4 _ (half_iff.1 hh))`. Unfold `tens`. Distinguish the cases in `h : IsHalf (a + b) t`. Rewrite using `[if_pos h, if_pos ((half_add_iff hh' t).2 h), smul_add, smul_add]`. Establish `e1 : a • ((k * l) • u) = k • (l • (a • u))` using `aux1 a k l u`.

Establish `e2 : b • ((k * l) • u) = l • (k • (b • u))` using `by rw [mul_comm k l]; exact aux1 b l k u`. Rewrite using `[e1, e2, h2 _ (nsmul_mem (hΛa u hu) l) (half_iff.2 (aux2 ha l u)), g2 _ (nsmul_mem (hΛb u hu) k) (half_iff.2 (aux2 hb k u))]`. Rewrite using `[if_neg h, if_neg fun h' => h ((half_add_iff hh' t).1 h')]`. Unfold `tens at ht`. Distinguish the cases in `h : IsHalf (a + b) t`.

Rewrite `ht` using `[if_pos h]`. Establish `e : (k * l) • t = l • (k • (a • t)) + k • (l • (b • t))` using `aux3 k l (half_iff.1 h)`. Rewrite using `[e]`. Conclude with `add_mem (nsmul_mem (h3 _ (left_ne_zero_of_mul ht)) l) (nsmul_mem (g3 _ (right_ne_zero_of_mul ht)) k)`. Conclude with `absurd (if_neg h) ht`.
-/
theorem tens_sb (ha : a * a = a) (hb : b * b = b) (hΛa : ∀ u ∈ Λ, a • u ∈ Λ) (hΛb : ∀ u ∈ Λ, b • u ∈ Λ)
    {Φ Ψ : WO S T → ℂ} (hΦ : IsSBHalf a Λ Φ) (hΨ : IsSBHalf b Λ Ψ) : IsSBHalf (a + b) Λ (tens a b Φ Ψ) := by
  obtain ⟨-, k, hk, h2, h3⟩ := hΦ
  obtain ⟨-, l, hl, g2, g3⟩ := hΨ
  refine ⟨fun t ht => ?_, k * l, Nat.mul_pos hk hl, fun u hu hh t => ?_, fun t ht => ?_⟩
  · by_contra h
    exact ht (if_neg h)
  · have hh' : IsHalf (a + b) ((k * l) • u) := half_iff.2 (aux4 _ (half_iff.1 hh))
    unfold tens
    by_cases h : IsHalf (a + b) t
    · rw [if_pos h, if_pos ((half_add_iff hh' t).2 h), smul_add, smul_add]
      have e1 : a • ((k * l) • u) = k • (l • (a • u)) := aux1 a k l u
      have e2 : b • ((k * l) • u) = l • (k • (b • u)) := by rw [mul_comm k l]; exact aux1 b l k u
      rw [e1, e2, h2 _ (nsmul_mem (hΛa u hu) l) (half_iff.2 (aux2 ha l u)),
        g2 _ (nsmul_mem (hΛb u hu) k) (half_iff.2 (aux2 hb k u))]
    · rw [if_neg h, if_neg fun h' => h ((half_add_iff hh' t).1 h')]
  · unfold tens at ht
    by_cases h : IsHalf (a + b) t
    · rw [if_pos h] at ht
      have e : (k * l) • t = l • (k • (a • t)) + k • (l • (b • t)) := aux3 k l (half_iff.1 h)
      rw [e]
      exact add_mem (nsmul_mem (h3 _ (left_ne_zero_of_mul ht)) l) (nsmul_mem (g3 _ (right_ne_zero_of_mul ht)) k)
    · exact absurd (if_neg h) ht

/- English proof (translation)
Use function extensionality and compare the values at `y`. Establish `h1 : IsHalf a (a • y)` using `half_iff.2 (by rw [smul_smul, ha])`. Establish `h2 : IsHalf b (b • y)` using `half_iff.2 (by rw [smul_smul, hb])`. Unfold `tens halfInd`. Distinguish the cases in `h : IsHalf (a + b) y`.

Rewrite using `[if_pos h]`. Distinguish the cases in `hy : y ∈ Λ`. Rewrite using `[if_pos ⟨hΛa y hy, h1⟩, if_pos ⟨hΛb y hy, h2⟩, if_pos ⟨hy, h⟩, one_mul]`. Rewrite using `[if_neg (fun h' : y ∈ Λ ∧ _ => hy h'.1)]`. Distinguish the cases in `hay : a • y ∈ Λ`.

Establish `: b • y ∉ Λ` using `fun hby => hy (by`. Use `add_mem hay hby` as an intermediate fact. Rewrite using `[← add_smul, half_iff.1 h] at this)` and apply the resulting hypothesis. Rewrite using `[if_neg (fun h' : b • y ∈ Λ ∧ _ => this h'.1), mul_zero]`. Rewrite using `[if_neg (fun h' : a • y ∈ Λ ∧ _ => hay h'.1), zero_mul]`.

Rewrite using `[if_neg h, if_neg (fun h' : y ∈ Λ ∧ _ => h h'.2)]`.
-/
theorem tens_ind (ha : a * a = a) (hb : b * b = b) (hΛa : ∀ u ∈ Λ, a • u ∈ Λ) (hΛb : ∀ u ∈ Λ, b • u ∈ Λ) :
    tens a b (halfInd a Λ) (halfInd b Λ) = halfInd (a + b) Λ := by
  funext y
  have h1 : IsHalf a (a • y) := half_iff.2 (by rw [smul_smul, ha])
  have h2 : IsHalf b (b • y) := half_iff.2 (by rw [smul_smul, hb])
  unfold tens halfInd
  by_cases h : IsHalf (a + b) y
  · rw [if_pos h]
    by_cases hy : y ∈ Λ
    · rw [if_pos ⟨hΛa y hy, h1⟩, if_pos ⟨hΛb y hy, h2⟩, if_pos ⟨hy, h⟩, one_mul]
    · rw [if_neg (fun h' : y ∈ Λ ∧ _ => hy h'.1)]
      by_cases hay : a • y ∈ Λ
      · have : b • y ∉ Λ := fun hby => hy (by
          have := add_mem hay hby
          rwa [← add_smul, half_iff.1 h] at this)
        rw [if_neg (fun h' : b • y ∈ Λ ∧ _ => this h'.1), mul_zero]
      · rw [if_neg (fun h' : a • y ∈ Λ ∧ _ => hay h'.1), zero_mul]
  · rw [if_neg h, if_neg (fun h' : y ∈ Λ ∧ _ => h h'.2)]

/- English proof (translation)
Use `⟨fun Ψ hΨ x hx => ?_, fun Ψ hΨ y hy => ?_, by rw [one_smul]; rfl⟩` and prove the remaining obligations. Establish `hx1 : b • x = x` using `half_iff.1 hx`. Establish `hx0 : a • x = 0` using `by rw [← hx1, smul_smul, hab, zero_smul]`. Establish `hx2 : IsHalf (a + b) x` using `half_iff.2 (by rw [add_smul, hx0, hx1, zero_add])`. Establish `e : tens a b Φ (fun t => Ψ (t + x)) = fun t => tens a b Φ Ψ (t + x)`.

Use function extensionality and compare the values at `t`. Simplify using `only [tens, half_add_iff hx2 t, smul_add, hx0, hx1, add_zero]`. Express the relevant statement in the definitionally equal form `Tm (tens a b Φ (fun t => Ψ (t + x))) = heisO ψ S T x (Tm (tens a b Φ Ψ))`. Rewrite using `[e]`. Conclude with `hT.trans _ (tens_sb ha hb hΛa hΛb hΦ hΨ) x hx2`.

Establish `hy1 : cA D b • y = y` using `half_iff.1 hy`. Establish `hy2 : IsHalf (cA D (a + b)) y` using `half_iff.2 (by`. Rewrite using `[RingHom.map_add, add_smul, hy1, ← hy1, smul_smul, ← RingHom.map_mul, hab, RingHom.map_zero, zero_smul, zero_add])`. Establish `e : tens a b Φ (fun t => ψ (symplO S T t y) * Ψ t) = fun t => ψ (symplO S T t y) * tens a b Φ Ψ t`. Use function extensionality and compare the values at `t`.

Simplify using `only [tens]`. Rewrite using `[symplO_smul, hy1]`. Apply the tactic sequence `split_ifs <;> ring`. Express the relevant statement in the definitionally equal form `Tm (tens a b Φ (fun t => ψ (symplO S T t y) * Ψ t)) = heisO ψ S T y (Tm (tens a b Φ Ψ))`. Rewrite using `[e]`.

Conclude with `hT.modul _ (tens_sb ha hb hΛa hΛb hΦ hΨ) y hy2`.
-/
theorem tens_model (ψ : AddChar (AF D.host.F) ℂ) (ha : a * a = a) (hb : b * b = b) (hab : a * b = 0)
    (hΛa : ∀ u ∈ Λ, a • u ∈ Λ) (hΛb : ∀ u ∈ Λ, b • u ∈ Λ) {f₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hT : IsPlaceModel ψ (symplO S T) (heisO ψ S T) (a + b) Λ 1 f₀ Tm) {Φ : WO S T → ℂ} (hΦ : IsSBHalf a Λ Φ) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) b Λ 1 (Tm (tens a b Φ (halfInd b Λ))) (Tm ∘ₗ tensL a b Φ) := by
  refine ⟨fun Ψ hΨ x hx => ?_, fun Ψ hΨ y hy => ?_, by rw [one_smul]; rfl⟩
  · have hx1 : b • x = x := half_iff.1 hx
    have hx0 : a • x = 0 := by rw [← hx1, smul_smul, hab, zero_smul]
    have hx2 : IsHalf (a + b) x := half_iff.2 (by rw [add_smul, hx0, hx1, zero_add])
    have e : tens a b Φ (fun t => Ψ (t + x)) = fun t => tens a b Φ Ψ (t + x) := by
      funext t
      simp only [tens, half_add_iff hx2 t, smul_add, hx0, hx1, add_zero]
    change Tm (tens a b Φ (fun t => Ψ (t + x))) = heisO ψ S T x (Tm (tens a b Φ Ψ))
    rw [e]
    exact hT.trans _ (tens_sb ha hb hΛa hΛb hΦ hΨ) x hx2
  · have hy1 : cA D b • y = y := half_iff.1 hy
    have hy2 : IsHalf (cA D (a + b)) y := half_iff.2 (by
      rw [RingHom.map_add, add_smul, hy1, ← hy1, smul_smul, ← RingHom.map_mul, hab, RingHom.map_zero, zero_smul, zero_add])
    have e : tens a b Φ (fun t => ψ (symplO S T t y) * Ψ t) = fun t => ψ (symplO S T t y) * tens a b Φ Ψ t := by
      funext t
      simp only [tens]
      rw [symplO_smul, hy1]
      split_ifs <;> ring
    change Tm (tens a b Φ (fun t => ψ (symplO S T t y) * Ψ t)) = heisO ψ S T y (Tm (tens a b Φ Ψ))
    rw [e]
    exact hT.modul _ (tens_sb ha hb hΛa hΛb hΦ hΨ) y hy2

end Gen

/- English proof (translation)
Establish `a2` using `idemSum_mul_self ha`. Establish `b2` using `idemSum_mul_self hb`. Establish `s2` using `idemSum_mul_self h`. Establish `hab : a * b = 0`. Establish `h2 : incA D 2⁻¹ * (1 + 1) = 1`.

Rewrite using `[← (incA D).map_one, ← RingHom.map_add, ← RingHom.map_mul]`. Use `congr 1`. Evaluate the numerical expressions. Take the linear combination `incA D 2⁻¹ * (s2 - a2 - b2) - a * b * h2`. Establish `h1` using `h.2`.

Rewrite `h1` using `[RingHom.map_add]`. Establish `ha'` using `ha.2`. Establish `hb'` using `hb.2`. Establish `k1 : a * cA D b = 0`. Take the linear combination `a * h1 - (cA D a + cA D b) * a2 - ha' - (cA D a + cA D b) * hab`.

Establish `k2 : b * cA D a = 0`. Take the linear combination `h1 - ha' - hb' - k1`. Establish `k3 : cA D a * cA D b = 0` using `by rw [← RingHom.map_mul, hab, RingHom.map_zero]`. Conclude with `⟨hab, by linear_combination hab + k1 + k2 + k3⟩`.
-/
theorem orth_of_idemSum {D : D7} {a b : AE D} {P Q R : Finset (Pl D.host.E)} (ha : IsIdemSum a P) (hb : IsIdemSum b Q)
    (h : IsIdemSum (a + b) R) : a * b = 0 ∧ (a + cA D a) * (b + cA D b) = 0 := by
  have a2 := idemSum_mul_self ha
  have b2 := idemSum_mul_self hb
  have s2 := idemSum_mul_self h
  have hab : a * b = 0 := by
    have h2 : incA D 2⁻¹ * (1 + 1) = 1 := by
      rw [← (incA D).map_one, ← RingHom.map_add, ← RingHom.map_mul]
      congr 1
      norm_num
    linear_combination incA D 2⁻¹ * (s2 - a2 - b2) - a * b * h2
  have h1 := h.2
  rw [RingHom.map_add] at h1
  have ha' := ha.2
  have hb' := hb.2
  have k1 : a * cA D b = 0 := by
    linear_combination a * h1 - (cA D a + cA D b) * a2 - ha' - (cA D a + cA D b) * hab
  have k2 : b * cA D a = 0 := by
    linear_combination h1 - ha' - hb' - k1
  have k3 : cA D a * cA D b = 0 := by rw [← RingHom.map_mul, hab, RingHom.map_zero]
  exact ⟨hab, by linear_combination hab + k1 + k2 + k3⟩

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {t : T}

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `a2` using `idemSum_mul_self d₁.e_is`. Establish `b2` using `idemSum_mul_self d₂.e_is`. Take `⟨hab, horth⟩` from `orth_of_idemSum d₁.e_is d₂.e_is he`. Establish `hsm : ∀ a : AE D, a * a = a → ∀ u ∈ latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) fun _ => True, a • u ∈ latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) fun _ => True` using `fun a ha u hu => GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ a (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu`. Establish `HC` using `GlobalTheory.HeisComb.main D W.ψ (G.pS p) (G.pT p)`.

Take `⟨c, hsupp, hc⟩` from `HC.1 c₁ c₂`. Set `d : FinDatum G t p` to `{ P := d₁.P ∪ d₂.P P_over := fun w hw => (Finset.mem_union.1 hw).elim (d₁.P_over w) (d₂.P_over w) e := d₁.e + d₂.e e_is := he fn := tens d₁.e d₂.e d₁.fn d₂.fn sb := tens_sb a2 b2 (hsm _ a2) (hsm _ b2) d₁.sb d₂.sb z := 1 z_cen := (FinDatum.vacuum G t p).z_cen z_supp := (FinDatum.v …`. Use `⟨d, c, rfl, rfl, ⟨fun u hu => ?_, fun u hu => ?_, fun f₀ hth hvac => ⟨?_, fun Tm hTm => ?_⟩⟩, fun y hy => if_pos hy, hc⟩` and prove the remaining obligations. Take `⟨x, hx, y, hy, rfl⟩` from `hsupp u hu`. Rewrite using `[Matrix.map_add _ (fun a b => RingHom.map_add _ a b), h₁.1 x hx, h₂.1 y hy, add_zero]`.

Take `⟨x, hx, y, hy, rfl⟩` from `hsupp u hu`. Introduce `i j`. Establish `k1` using `h₁.2.1 x hx i j`. Establish `k2` using `h₂.2.1 y hy i j`. Express the relevant statement in the definitionally equal form `(d₁.e + d₂.e + cA D (d₁.e + d₂.e)) * (x i j + y i j) = x i j + y i j`.

Rewrite using `[RingHom.map_add]`. Take the linear combination `(1 - d₂.e - cA D d₂.e) * k1 + (1 - d₁.e - cA D d₁.e) * k2 + (x i j + y i j) * horth`. Conclude with `(GlobalTheory.PlaceModelSum.placeModelExistsSum D W.ψ W.ψ_std _ _ _ _ hS hT d.P d.e d.e_is f₀ hth hvac).1`. Take `⟨c', k1, k2⟩` from `GlobalTheory.CombsExist.exists_comb_model W.ψ _ _ _ _ d₂.e d₂.fn W.ψ_std hS hT b2 d₂.e_is.2 (infPart_idemSum d₂.e_is) d₂.sb`. Establish `hT1 : IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) (d₁.e + d₂.e) (latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) fun _ => True) 1 f₀ Tm` using `hTm`.

Establish `hT2` using `hT1`. Rewrite `hT2` using `[add_comm]`. Establish `v` using `hT1.vac`. Rewrite `v` using `[one_smul]`. Establish `m2` using `tens_model W.ψ a2 b2 hab (hsm _ a2) (hsm _ b2) hT1 (GlobalTheory.isSBHalf_halfInd d₁.e _)`.

Rewrite `m2` using `[tens_ind a2 b2 (hsm _ a2) (hsm _ b2), v]`. Establish `m1` using `tens_model W.ψ b2 a2 (by rw [mul_comm, hab]) (hsm _ b2) (hsm _ a2) hT2 (GlobalTheory.isSBHalf_halfInd d₂.e _)`. Rewrite `m1` using `[tens_ind b2 a2 (hsm _ b2) (hsm _ a2), add_comm, v]`. Establish `m3` using `tens_model W.ψ a2 b2 hab (hsm _ a2) (hsm _ b2) hT1 d₁.sb`. Establish `e2 : comb W.ψ _ _ c₂ f₀ = comb W.ψ _ _ c' f₀` using `((h₂.2.2 f₀ hth hvac).2 _ m2).trans (k2 f₀ _ m2).symm`.

Establish `e1` using `(h₁.2.2 f₀ hth hvac).2 _ m1`. Establish `e3` using `k2 _ _ m3`. Establish `hcomm` using `HC.2.1 c₁ c' (fun x hx y hy => HC.2.2.2 _ _ x y (by rw [RingHom.map_add, Formalism.L2.Theta.cA_cA, add_comm]) horth (h₁.2.1 x hx) (k1 y hy).2) f₀`. Rewrite using `[hc, e2, hcomm, e1]`. Use `Eq.trans ?_ e3` and prove the remaining obligations.

Use `congr 1`. Conclude with `congrArg Tm (tens_comm _ _ _ _)`.
-/
theorem exists_prod {p : Pair T} (hS : IsSelfDualC (G.pS p) (G.latS p)) (hT : IsSelfDualC (G.pT p) (G.latT p))
    (d₁ d₂ : FinDatum G t p) (c₁ c₂ : WO (G.pS p) (G.pT p) →₀ ℂ) (he : IsIdemSum (d₁.e + d₂.e) (d₁.P ∪ d₂.P))
    (h₁ : IsCombOf W d₁ c₁) (h₂ : IsCombOf W d₂ c₂) :
    ∃ (d : FinDatum G t p) (c : WO (G.pS p) (G.pT p) →₀ ℂ), d.P = d₁.P ∪ d₂.P ∧ d.e = d₁.e + d₂.e ∧ IsCombOf W d c ∧
      (∀ y, IsHalf d.e y → d.fn y = d₁.fn (d₁.e • y) * d₂.fn (d₂.e • y)) ∧
      ∀ f, comb W.ψ _ _ c f = comb W.ψ _ _ c₁ (comb W.ψ _ _ c₂ f) := by
  have a2 := idemSum_mul_self d₁.e_is
  have b2 := idemSum_mul_self d₂.e_is
  obtain ⟨hab, horth⟩ := orth_of_idemSum d₁.e_is d₂.e_is he
  have hsm : ∀ a : AE D, a * a = a → ∀ u ∈ latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) fun _ => True,
      a • u ∈ latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) fun _ => True := fun a ha u hu =>
    GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu
  have HC := GlobalTheory.HeisComb.main D W.ψ (G.pS p) (G.pT p)
  obtain ⟨c, hsupp, hc⟩ := HC.1 c₁ c₂
  let d : FinDatum G t p :=
    { P := d₁.P ∪ d₂.P
      P_over := fun w hw => (Finset.mem_union.1 hw).elim (d₁.P_over w) (d₂.P_over w)
      e := d₁.e + d₂.e
      e_is := he
      fn := tens d₁.e d₂.e d₁.fn d₂.fn
      sb := tens_sb a2 b2 (hsm _ a2) (hsm _ b2) d₁.sb d₂.sb
      z := 1
      z_cen := (FinDatum.vacuum G t p).z_cen
      z_supp := (FinDatum.vacuum G t p).z_supp }
  refine ⟨d, c, rfl, rfl, ⟨fun u hu => ?_, fun u hu => ?_, fun f₀ hth hvac => ⟨?_, fun Tm hTm => ?_⟩⟩,
    fun y hy => if_pos hy, hc⟩
  · obtain ⟨x, hx, y, hy, rfl⟩ := hsupp u hu
    rw [Matrix.map_add _ (fun a b => RingHom.map_add _ a b), h₁.1 x hx, h₂.1 y hy, add_zero]
  · obtain ⟨x, hx, y, hy, rfl⟩ := hsupp u hu
    intro i j
    have k1 := h₁.2.1 x hx i j
    have k2 := h₂.2.1 y hy i j
    change (d₁.e + d₂.e + cA D (d₁.e + d₂.e)) * (x i j + y i j) = x i j + y i j
    rw [RingHom.map_add]
    linear_combination (1 - d₂.e - cA D d₂.e) * k1 + (1 - d₁.e - cA D d₁.e) * k2 + (x i j + y i j) * horth
  · exact (GlobalTheory.PlaceModelSum.placeModelExistsSum D W.ψ W.ψ_std _ _ _ _ hS hT d.P d.e d.e_is f₀ hth hvac).1
  · obtain ⟨c', k1, k2⟩ := GlobalTheory.CombsExist.exists_comb_model W.ψ _ _ _ _ d₂.e d₂.fn W.ψ_std hS hT b2 d₂.e_is.2
      (infPart_idemSum d₂.e_is) d₂.sb
    have hT1 : IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) (d₁.e + d₂.e)
      (latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) fun _ => True) 1 f₀ Tm := hTm
    have hT2 := hT1
    rw [add_comm] at hT2
    have v := hT1.vac
    rw [one_smul] at v
    have m2 := tens_model W.ψ a2 b2 hab (hsm _ a2) (hsm _ b2) hT1 (GlobalTheory.isSBHalf_halfInd d₁.e _)
    rw [tens_ind a2 b2 (hsm _ a2) (hsm _ b2), v] at m2
    have m1 := tens_model W.ψ b2 a2 (by rw [mul_comm, hab]) (hsm _ b2) (hsm _ a2) hT2 (GlobalTheory.isSBHalf_halfInd d₂.e _)
    rw [tens_ind b2 a2 (hsm _ b2) (hsm _ a2), add_comm, v] at m1
    have m3 := tens_model W.ψ a2 b2 hab (hsm _ a2) (hsm _ b2) hT1 d₁.sb
    have e2 : comb W.ψ _ _ c₂ f₀ = comb W.ψ _ _ c' f₀ := ((h₂.2.2 f₀ hth hvac).2 _ m2).trans (k2 f₀ _ m2).symm
    have e1 := (h₁.2.2 f₀ hth hvac).2 _ m1
    have e3 := k2 _ _ m3
    have hcomm := HC.2.1 c₁ c' (fun x hx y hy => HC.2.2.2 _ _ x y
      (by rw [RingHom.map_add, Formalism.L2.Theta.cA_cA, add_comm]) horth (h₁.2.1 x hx) (k1 y hy).2) f₀
    rw [hc, e2, hcomm, e1]
    refine Eq.trans ?_ e3
    congr 1
    exact congrArg Tm (tens_comm _ _ _ _)

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ t j d₁ d₂ c₁ c₂ => exists_prod ch.W (p := .top t j) (ch.G.isV (X := .top j) j.2.le fun _ h => by cases h).sd (ch.G.isV (X := .top (j + 1)) j.2 fun _ h => by cases h).sd d₁ d₂ c₁ c₂⟩⟩`.
-/
theorem prod_datum : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (j : Fin D.R.m) (d₁ d₂ : FinDatum ch.G t (.top t j)) (c₁ c₂ : WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) →₀ ℂ), IsIdemSum (d₁.e + d₂.e) (d₁.P ∪ d₂.P) → IsCombOf ch.W d₁ c₁ → IsCombOf ch.W d₂ c₂ → ∃ (d : FinDatum ch.G t (.top t j)) (c : WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) →₀ ℂ), d.P = d₁.P ∪ d₂.P ∧ d.e = d₁.e + d₂.e ∧ IsCombOf ch.W d c ∧ (∀ y, IsHalf d.e y → d.fn y = d₁.fn (d₁.e • y) * d₂.fn (d₂.e • y)) ∧ ∀ f, comb ch.W.ψ _ _ c f = comb ch.W.ψ _ _ c₁ (comb ch.W.ψ _ _ c₂ f) :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ t j d₁ d₂ c₁ c₂ =>
    exists_prod ch.W (p := .top t j) (ch.G.isV (X := .top j) j.2.le fun _ h => by cases h).sd
      (ch.G.isV (X := .top (j + 1)) j.2 fun _ h => by cases h).sd d₁ d₂ c₁ c₂⟩⟩

end GlobalTheory.ProdDatum

end
