import Formalism.HermitianCurvature.ThetaExistenceInductiveFromPieces

noncomputable section

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite

section PSD

variable {X : Type}

/- English proof (translation)
Introduce `a`. Establish `: ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k' x y = ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k x y` using `Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => by rw [h x hx y hy]`. Rewrite using `[this]`. Conclude with `hk a`.
-/
theorem psd_congr {F : Finset X} {k k' : X → X → ℂ} (h : ∀ x ∈ F, ∀ y ∈ F, k x y = k' x y)
    (hk : IsPSD F k) : IsPSD F k' := by
  intro a
  have : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k' x y =
      ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k x y :=
    Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => by rw [h x hx y hy]
  rw [this]; exact hk a

/- English proof (translation)
Introduce `a`. Simplify using the standard rewrite rules.
-/
theorem psd_zero (F : Finset X) : IsPSD F (fun _ _ => (0 : ℂ)) := by
  intro a; simp

/- English proof (translation)
Introduce `a`. Establish `: ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * (k x y + k' x y) = (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k x y) + ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k' x y`. Simplify using `only [mul_add, Finset.sum_add_distrib]`. Rewrite using `[this, Complex.add_im, Complex.add_re, (hk a).1, (hk' a).1]`. Conclude with `⟨by simp, add_nonneg (hk a).2 (hk' a).2⟩`.
-/
theorem psd_add {F : Finset X} {k k' : X → X → ℂ} (hk : IsPSD F k) (hk' : IsPSD F k') :
    IsPSD F (fun x y => k x y + k' x y) := by
  intro a
  have : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * (k x y + k' x y) =
      (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k x y) +
        ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k' x y := by
    simp only [mul_add, Finset.sum_add_distrib]
  rw [this, Complex.add_im, Complex.add_re, (hk a).1, (hk' a).1]
  exact ⟨by simp, add_nonneg (hk a).2 (hk' a).2⟩

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simpa using psd_zero F`. Consider the case `insert i S hi ih`. Use `psd_add (hk i (Finset.mem_insert_self _ _)) (ih fun j hj => hk j (Finset.mem_insert_of_mem hj))` as an intermediate fact. Use `psd_congr ?_ this` and prove the remaining obligations.

Introduce `x _ y _`. Rewrite using `[Finset.sum_insert hi]`.
-/
theorem psd_sum {ι : Type} (S : Finset ι) {F : Finset X} {k : ι → X → X → ℂ}
    (hk : ∀ i ∈ S, IsPSD F (k i)) : IsPSD F (fun x y => ∑ i ∈ S, k i x y) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using psd_zero F
  | insert i S hi ih =>
    have := psd_add (hk i (Finset.mem_insert_self _ _))
      (ih fun j hj => hk j (Finset.mem_insert_of_mem hj))
    refine psd_congr ?_ this
    intro x _ y _; rw [Finset.sum_insert hi]

/- English proof (translation)
Introduce `a`. Establish `: ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * ((c : ℂ) * k x y) = (c : ℂ) * ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k x y`. Simplify using `only [Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring`. Rewrite using `[this, Complex.re_ofReal_mul, Complex.im_ofReal_mul, (hk a).1]`.

Conclude with `⟨by simp, mul_nonneg hc (hk a).2⟩`.
-/
theorem psd_smul {F : Finset X} {k : X → X → ℂ} (c : ℝ) (hc : 0 ≤ c) (hk : IsPSD F k) :
    IsPSD F (fun x y => (c : ℂ) * k x y) := by
  intro a
  have : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * ((c : ℂ) * k x y) =
      (c : ℂ) * ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k x y := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  rw [this, Complex.re_ofReal_mul, Complex.im_ofReal_mul, (hk a).1]
  exact ⟨by simp, mul_nonneg hc (hk a).2⟩

end PSD

/- English proof (translation)
Establish `hfi : (R.addSubgroupOf P).FiniteIndex` using `⟨h⟩`. Establish `: Finite (P ⧸ R.addSubgroupOf P)` using `inferInstance`. Use `(Set.finite_range (fun q : P ⧸ R.addSubgroupOf P => (((Quotient.out q : P) : K) : K ⧸ R))).subset ?_` and prove the remaining obligations. Introduce `x hx`. Use `⟨((⟨Quotient.out x, hx⟩ : P) : P ⧸ R.addSubgroupOf P), ?_⟩` and prove the remaining obligations.

Establish `h1 : ((Quotient.out ((⟨Quotient.out x, hx⟩ : P) : P ⧸ R.addSubgroupOf P) : P) : P ⧸ R.addSubgroupOf P) = ((⟨Quotient.out x, hx⟩ : P) : P ⧸ R.addSubgroupOf P)` using `QuotientAddGroup.out_eq' _`. Rewrite `h1` using `[QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]`. Establish `h2 : (((Quotient.out ((⟨Quotient.out x, hx⟩ : P) : P ⧸ R.addSubgroupOf P) : P) : K) : K ⧸ R) = ((Quotient.out x : K) : K ⧸ R)`. Rewrite using `[QuotientAddGroup.eq]`. Simplify using `using h1`.

Conclude with `h2.trans (QuotientAddGroup.out_eq' x)`.
-/
theorem finite_classes {K : Type} [AddCommGroup K] (R P : AddSubgroup K) (h : R.relIndex P ≠ 0) :
    {x : K ⧸ R | (Quotient.out x : K) ∈ P}.Finite := by
  have hfi : (R.addSubgroupOf P).FiniteIndex := ⟨h⟩
  have : Finite (P ⧸ R.addSubgroupOf P) := inferInstance
  refine (Set.finite_range
    (fun q : P ⧸ R.addSubgroupOf P => (((Quotient.out q : P) : K) : K ⧸ R))).subset ?_
  intro x hx
  refine ⟨((⟨Quotient.out x, hx⟩ : P) : P ⧸ R.addSubgroupOf P), ?_⟩
  have h1 : ((Quotient.out ((⟨Quotient.out x, hx⟩ : P) : P ⧸ R.addSubgroupOf P) : P) :
      P ⧸ R.addSubgroupOf P) = ((⟨Quotient.out x, hx⟩ : P) : P ⧸ R.addSubgroupOf P) :=
    QuotientAddGroup.out_eq' _
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h1
  have h2 : (((Quotient.out ((⟨Quotient.out x, hx⟩ : P) : P ⧸ R.addSubgroupOf P) : P) : K) :
      K ⧸ R) = ((Quotient.out x : K) : K ⧸ R) := by
    rw [QuotientAddGroup.eq]; simpa using h1
  exact h2.trans (QuotientAddGroup.out_eq' x)

/- English proof (translation)
Use `finsum_eq_sum_of_support_subset _ ?_` and prove the remaining obligations. Introduce `x hx`. Distinguish the cases in `hp : p x`. Conclude with `hS x hp`. Simplify using `[hp] at hx`.
-/
theorem finsum_ite_eq {α : Type} (S : Finset α) (p : α → Prop) [DecidablePred p] (f : α → ℂ)
    (hS : ∀ x, p x → x ∈ S) :
    ∑ᶠ x, (if p x then f x else 0) = ∑ x ∈ S, if p x then f x else 0 := by
  refine finsum_eq_sum_of_support_subset _ ?_
  intro x hx
  by_cases hp : p x
  · exact hS x hp
  · simp [hp] at hx

/- English proof (translation)
Establish `hA' : (A.card : ℂ) ≠ 0` using `by exact_mod_cast hA`. Establish `hB' : (B.card : ℂ) ≠ 0` using `by exact_mod_cast hB`. Simplify using `only [mul_sub, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem mean_sub {K : Type} (A B : Finset K) (hA : A.card ≠ 0) (hB : B.card ≠ 0) (Y : ℂ)
    (u : K → K → ℂ) :
    Y - ((A.card : ℂ) * (B.card : ℂ))⁻¹ * ∑ ρ ∈ A, ∑ b ∈ B, u ρ b =
      ∑ ρ ∈ A, ∑ b ∈ B, ((((A.card : ℝ) * (B.card : ℝ))⁻¹ : ℝ) : ℂ) * (Y - u ρ b) := by
  have hA' : (A.card : ℂ) ≠ 0 := by exact_mod_cast hA
  have hB' : (B.card : ℂ) ≠ 0 := by exact_mod_cast hB
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  push_cast
  field_simp

/- English proof (translation)
Take `⟨a, ha, _⟩` from `h.2 0 L.zero_mem`. Conclude with `Finset.card_ne_zero_of_mem ha.1`.
-/
theorem reps_card_ne_zero {K : Type} [CommRing K] {S : Finset K} {L M : AddSubgroup K}
    (h : IsReps S L M) : S.card ≠ 0 := by
  obtain ⟨a, ha, _⟩ := h.2 0 L.zero_mem
  exact Finset.card_ne_zero_of_mem ha.1

end Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite

open Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite in
/- English proof (translation)
Introduce `hGI hADE hLC hKH hMLC hLCh hLF hSU hSmU hUG hUNB hCP hUB hCSA hMM hKG hKBD hGRC hAB hPG hPD hPL hCM hCNE hTL hTB hTS hA2 hN1 K _ _ _ R ψ hD hch m hm hA13 n₀ F Lc Om hF hCut hOm`. Take `⟨hLo, hLcpt, hRL, hNs0⟩` from `hCut`. Take `⟨D⟩` from `hADE hLC hKH hMLC hLCh hLF K R ψ hD hch (m + 1) F Om (Lc : Set K) (by omega) hOm hLcpt`. Take `⟨V₁, hV₁, hLow⟩` from `hTL hGI hA2.2 hUG hN1 hCSA hMM hCP hKG hGRC hAB hCNE hCM hPL K R ψ hD hch m hm n₀ F Om (Lc : Set K) hF hOm D`. Take `⟨V₂, hV₂, hSh⟩` from `hSU K R ψ hD hch ((D.A ×ˢ D.B).image (fun p => p.1 + p.2))`.

Take `⟨t, ht⟩` from `hSmU K R ψ hD hch (V₁ ∩ V₂) (Filter.inter_mem hV₁ hV₂)`. Set `τ : K → Kˣ` to `fun σ => if h : IsUnit (((t⁻¹ : Kˣ) : K) + σ) then h.unit⁻¹ else 1`. Establish `hmem : ∀ ρ ∈ D.A, ∀ b ∈ D.B, ρ + b ∈ (D.A ×ˢ D.B).image (fun p => p.1 + p.2)`. Introduce `ρ hρ b hb`. Conclude with `Finset.mem_image.2 ⟨(ρ, b), Finset.mem_product.2 ⟨hρ, hb⟩, rfl⟩`.

Establish `hτ : ∀ ρ ∈ D.A, ∀ b ∈ D.B, IsShift t (τ (ρ + b)) (ρ + b)`. Introduce `ρ hρ b hb`. Establish `hu` using `(hSh t ht.2 _ (hmem ρ hρ b hb)).1`. Simplify using `only [IsShift, τ, dif_pos hu, inv_inv, IsUnit.unit_spec]`. Establish `hτmod : ∀ ρ ∈ D.A, ∀ b ∈ D.B, modK R (τ (ρ + b) : K) * modK R ((t⁻¹ : Kˣ) : K) = modK R 1`.

Introduce `ρ hρ b hb`. Establish `h1` using `(hSh t ht.2 _ (hmem ρ hρ b hb)).2`. Establish `h2` using `(hMM K R ψ hD (τ (ρ + b)) (τ (ρ + b))⁻¹).2`. Rewrite `h2` using `[hτ ρ hρ b hb]`. Rewrite using `[← h1, ← h2, ← hτ ρ hρ b hb, Units.mul_inv]`.

Establish `htpos : 0 < modK R ((t⁻¹ : Kˣ) : K)` using `(hMM K R ψ hD t⁻¹ 1).1`. Establish `hcrex : ∀ x : K ⧸ R.toAddSubgroup, ∃ u : Kˣ, ((u : K) : K ⧸ R.toAddSubgroup) = x`. Introduce `x`. Take `⟨r, hr, hu⟩` from `hD.unitRep (Quotient.out x)`. Use `⟨hu.unit, ?_⟩` and prove the remaining obligations.

Rewrite using `[IsUnit.unit_spec, QuotientAddGroup.mk_add, QuotientAddGroup.out_eq', (QuotientAddGroup.eq_zero_iff r).2 hr, add_zero]`. Use `choose cr hcr using hcrex`. Establish `hcr' : IsCr R cr` using `hcr`. Establish `hBR : ∀ b ∈ D.B, b ∈ R` using `fun b hb => D.repsB.1 b hb`. Take `⟨hper, hpsd⟩` from `hTB hCP hKG hN1 hMM K R ψ hD m n₀ F D.A D.B τ cr hF hcr' hBR`.

Take `⟨Θm, hΘm⟩` from `hA13 n₀ F hF`. Use `⟨fun z h h' => if z ∈ Lc then thx R ψ m cr D.A D.B τ z h h' else 0, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x r hr`. Establish `hiff : x + r ∈ Lc ↔ x ∈ Lc`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Use `Lc.sub_mem h (hRL r hr)` as an intermediate fact. Simplify using `using this`. Introduce `h`. Conclude with `Lc.add_mem h (hRL r hr)`.

Use function extensionality and compare the values at `h h'`. Simplify using `only [hiff, hper x r hr]`. Introduce `x`. Distinguish the cases in `hx : x ∈ Lc`. Simplify `hpsd x` using `only [hx, if_true]`.

Simplify `psd_zero F` using `only [hx, if_false]`. Introduce `x hx h _ h' _`. Simplify using `only [hx, if_false]`. Introduce `t' ht'`. Distinguish the cases in `hx : (t' : K) ∈ Lc`.

Use `hLow t τ cr ht.1 hcr' hτ (t' : K) ht'` as an intermediate fact. Use `psd_congr ?_ this` and prove the remaining obligations. Introduce `h _ h' _`. Establish `hu : IsUnit (t' : K)` using `t'.isUnit`. Establish `hu' : hu.unit = t'` using `Units.ext rfl`.

Simplify using `only [hx, if_true, NsK, dif_pos hu, hu']`. Use `psd_congr ?_ (psd_zero F)` and prove the remaining obligations. Introduce `h hh h' hh'`. Simplify using `only [hx, if_false, hNs0 t' hx h hh h' hh', sub_zero]`. Establish `hPlat` using `(hPL K R ψ hD hch D.L₁ D.lat₁).1`.

Establish `hRlat : IsLat R.toAddSubgroup` using `⟨hD.isOpen, hD.isCompact⟩`. Establish `hfin` using `finite_classes R.toAddSubgroup (perp ψ D.L₁) (hLF K (perp ψ D.L₁) R.toAddSubgroup hPlat hRlat)`. Establish `hS : ∀ x : K ⧸ R.toAddSubgroup, (Quotient.out x : K) ∈ perp ψ D.L₁ → x ∈ hfin.toFinset` using `fun x hx => hfin.mem_toFinset.2 hx`. Establish `hAc` using `reps_card_ne_zero D.repsA`. Establish `hBc` using `reps_card_ne_zero D.repsB`.

Establish `hp1 : IsPSD F (fun h h' => ∑ ρ ∈ D.A, ∑ b ∈ D.B, ((((D.A.card : ℝ) * (D.B.card : ℝ))⁻¹ : ℝ) : ℂ) * (((cSize R h ^ (m + 1) * cSize R h' ^ (m + 1) : ℝ) : ℂ) * N0 R ψ h h' - uGram R ψ m cr Set.univ h h' (τ (ρ + b)) (τ (ρ + b))))`. Use `psd_sum D.A fun ρ _ => psd_sum D.B fun b _ => psd_smul _ (by positivity) ?_` and prove the remaining obligations. Conclude with `hUNB hUG hN1 hCSA hMM hLF K R ψ hD m n₀ F Θm hF hΘm (τ (ρ + b)) cr hcr'`. Establish `hp2 : IsPSD F (fun h h' => ∑ x ∈ hfin.toFinset, if (Quotient.out x : K) ∈ Lc then 0 else thx R ψ m cr D.A D.B τ (Quotient.out x) h h')`. Use `psd_sum _ fun x _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hx : (Quotient.out x : K) ∈ Lc`. Simplify `psd_zero F` using `only [hx, if_true]`. Simplify `hpsd _` using `only [hx, if_false]`. Use `psd_congr ?_ (psd_add hp1 hp2)` and prove the remaining obligations. Introduce `h hh h' hh'`.

Establish `hsum` using `hTS hPG hPD hPL hLF hGRC hCP hKG hN1 hMM K R ψ hD hch m (m + 1) n₀ F Om (Lc : Set K) D τ cr hF hcr' h hh h' hh'`. Rewrite using `[← mean_sub D.A D.B hAc hBc, ← hsum]`. Rewrite using `[finsum_ite_eq hfin.toFinset (fun x : K ⧸ R.toAddSubgroup => (Quotient.out x : K) ∈ perp ψ D.L₁) (fun x => thx R ψ m cr D.A D.B τ (Quotient.out x) h h') hS]`. Rewrite using `[finsum_ite_eq hfin.toFinset (fun x : K ⧸ R.toAddSubgroup => (Quotient.out x : K) ∈ Lc) (fun x => thx R ψ m cr D.A D.B τ (Quotient.out x) h h') (fun x hx => hS x (D.cutPerp _ hx))]`. Rewrite using `[sub_add, ← Finset.sum_sub_distrib]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun x hx => ?_` and prove the remaining obligations. Establish `hxP : (Quotient.out x : K) ∈ perp ψ D.L₁` using `hfin.mem_toFinset.1 hx`. Distinguish the cases in `hxL : (Quotient.out x : K) ∈ Lc`. Simplify using `only [hxP, hxL, if_true, sub_zero]`.

Simplify using `only [hxP, hxL, if_true, if_false, sub_self]`. Introduce `x h _ h' _ hne`. Distinguish the cases in `hx : x ∈ Lc`. Simplify using `only [hx, if_true, thx]`. Establish `hz : ∀ ρ ∈ D.A, ∀ b ∈ D.B, ∀ b' ∈ D.B, uGram R ψ m cr Set.univ h h' (τ (ρ + b)) (τ (ρ + b')) = 0`.

Introduce `ρ hρ b hb b' hb'`. Use `hUB hKBD hCSA hMM K R ψ hD m cr Set.univ h h' _ _ ?_ hne` and prove the remaining obligations. Conclude with `mul_right_cancel₀ htpos.ne' ((hτmod ρ hρ b hb).trans (hτmod ρ hρ b' hb').symm)`. Establish `: ∑ ρ ∈ D.A, ((D.B.card : ℂ)⁻¹) ^ 2 * ∑ b ∈ D.B, ∑ b' ∈ D.B, ψ (-(x * b)) * conj (ψ (-(x * b'))) * uGram R ψ m cr Set.univ h h' (τ (ρ + b)) (τ (ρ + b')) = 0`. Use `Finset.sum_eq_zero fun ρ hρ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_eq_zero fun b hb => Finset.sum_eq_zero fun b' hb' => by`. Rewrite using `[hz ρ hρ b hb b' hb', mul_zero], mul_zero]`. Rewrite using `[this, mul_zero]`. Simplify using `only [hx, if_false]`.
-/
theorem Formalism.FourierDecayAlt.P.thetaOnDomainOfSteps : Formalism.FourierDecayAlt.A6.ThOmAssemble := by
  intro hGI hADE hLC hKH hMLC hLCh hLF hSU hSmU hUG hUNB hCP hUB hCSA hMM hKG hKBD hGRC hAB hPG hPD
    hPL hCM hCNE hTL hTB hTS hA2 hN1 K _ _ _ R ψ hD hch m hm hA13 n₀ F Lc Om hF hCut hOm
  classical
  obtain ⟨hLo, hLcpt, hRL, hNs0⟩ := hCut
  obtain ⟨D⟩ := hADE hLC hKH hMLC hLCh hLF K R ψ hD hch (m + 1) F Om (Lc : Set K) (by omega) hOm
    hLcpt
  obtain ⟨V₁, hV₁, hLow⟩ := hTL hGI hA2.2 hUG hN1 hCSA hMM hCP hKG hGRC hAB hCNE hCM hPL K R ψ hD hch
    m hm n₀ F Om (Lc : Set K) hF hOm D
  obtain ⟨V₂, hV₂, hSh⟩ := hSU K R ψ hD hch ((D.A ×ˢ D.B).image (fun p => p.1 + p.2))
  obtain ⟨t, ht⟩ := hSmU K R ψ hD hch (V₁ ∩ V₂) (Filter.inter_mem hV₁ hV₂)

  let τ : K → Kˣ := fun σ =>
    if h : IsUnit (((t⁻¹ : Kˣ) : K) + σ) then h.unit⁻¹ else 1
  have hmem : ∀ ρ ∈ D.A, ∀ b ∈ D.B, ρ + b ∈ (D.A ×ˢ D.B).image (fun p => p.1 + p.2) := by
    intro ρ hρ b hb
    exact Finset.mem_image.2 ⟨(ρ, b), Finset.mem_product.2 ⟨hρ, hb⟩, rfl⟩
  have hτ : ∀ ρ ∈ D.A, ∀ b ∈ D.B, IsShift t (τ (ρ + b)) (ρ + b) := by
    intro ρ hρ b hb
    have hu := (hSh t ht.2 _ (hmem ρ hρ b hb)).1
    simp only [IsShift, τ, dif_pos hu, inv_inv, IsUnit.unit_spec]
  have hτmod : ∀ ρ ∈ D.A, ∀ b ∈ D.B,
      modK R (τ (ρ + b) : K) * modK R ((t⁻¹ : Kˣ) : K) = modK R 1 := by
    intro ρ hρ b hb
    have h1 := (hSh t ht.2 _ (hmem ρ hρ b hb)).2
    have h2 := (hMM K R ψ hD (τ (ρ + b)) (τ (ρ + b))⁻¹).2
    rw [hτ ρ hρ b hb] at h2
    rw [← h1, ← h2, ← hτ ρ hρ b hb, Units.mul_inv]
  have htpos : 0 < modK R ((t⁻¹ : Kˣ) : K) := (hMM K R ψ hD t⁻¹ 1).1

  have hcrex : ∀ x : K ⧸ R.toAddSubgroup, ∃ u : Kˣ, ((u : K) : K ⧸ R.toAddSubgroup) = x := by
    intro x
    obtain ⟨r, hr, hu⟩ := hD.unitRep (Quotient.out x)
    refine ⟨hu.unit, ?_⟩
    rw [IsUnit.unit_spec, QuotientAddGroup.mk_add, QuotientAddGroup.out_eq',
      (QuotientAddGroup.eq_zero_iff r).2 hr, add_zero]
  choose cr hcr using hcrex
  have hcr' : IsCr R cr := hcr
  have hBR : ∀ b ∈ D.B, b ∈ R := fun b hb => D.repsB.1 b hb
  obtain ⟨hper, hpsd⟩ := hTB hCP hKG hN1 hMM K R ψ hD m n₀ F D.A D.B τ cr hF hcr' hBR
  obtain ⟨Θm, hΘm⟩ := hA13 n₀ F hF
  refine ⟨fun z h h' => if z ∈ Lc then thx R ψ m cr D.A D.B τ z h h' else 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x r hr
    have hiff : x + r ∈ Lc ↔ x ∈ Lc := by
      constructor
      · intro h
        have := Lc.sub_mem h (hRL r hr)
        simpa using this
      · intro h; exact Lc.add_mem h (hRL r hr)
    funext h h'
    simp only [hiff, hper x r hr]
  ·
    intro x
    by_cases hx : x ∈ Lc
    · simpa only [hx, if_true] using hpsd x
    · simpa only [hx, if_false] using psd_zero F
  ·
    intro x hx h _ h' _
    simp only [hx, if_false]
  ·
    intro t' ht'
    by_cases hx : (t' : K) ∈ Lc
    · have := hLow t τ cr ht.1 hcr' hτ (t' : K) ht'
      refine psd_congr ?_ this
      intro h _ h' _
      have hu : IsUnit (t' : K) := t'.isUnit
      have hu' : hu.unit = t' := Units.ext rfl
      simp only [hx, if_true, NsK, dif_pos hu, hu']
    · refine psd_congr ?_ (psd_zero F)
      intro h hh h' hh'
      simp only [hx, if_false, hNs0 t' hx h hh h' hh', sub_zero]
  ·
    have hPlat := (hPL K R ψ hD hch D.L₁ D.lat₁).1
    have hRlat : IsLat R.toAddSubgroup := ⟨hD.isOpen, hD.isCompact⟩
    have hfin := finite_classes R.toAddSubgroup (perp ψ D.L₁)
      (hLF K (perp ψ D.L₁) R.toAddSubgroup hPlat hRlat)
    have hS : ∀ x : K ⧸ R.toAddSubgroup, (Quotient.out x : K) ∈ perp ψ D.L₁ → x ∈ hfin.toFinset :=
      fun x hx => hfin.mem_toFinset.2 hx
    have hAc := reps_card_ne_zero D.repsA
    have hBc := reps_card_ne_zero D.repsB
    have hp1 : IsPSD F (fun h h' => ∑ ρ ∈ D.A, ∑ b ∈ D.B,
        ((((D.A.card : ℝ) * (D.B.card : ℝ))⁻¹ : ℝ) : ℂ) *
          (((cSize R h ^ (m + 1) * cSize R h' ^ (m + 1) : ℝ) : ℂ) * N0 R ψ h h' -
            uGram R ψ m cr Set.univ h h' (τ (ρ + b)) (τ (ρ + b)))) := by
      refine psd_sum D.A fun ρ _ => psd_sum D.B fun b _ => psd_smul _ (by positivity) ?_
      exact hUNB hUG hN1 hCSA hMM hLF K R ψ hD m n₀ F Θm hF hΘm (τ (ρ + b)) cr hcr'
    have hp2 : IsPSD F (fun h h' => ∑ x ∈ hfin.toFinset,
        if (Quotient.out x : K) ∈ Lc then 0 else thx R ψ m cr D.A D.B τ (Quotient.out x) h h') := by
      refine psd_sum _ fun x _ => ?_
      by_cases hx : (Quotient.out x : K) ∈ Lc
      · simpa only [hx, if_true] using psd_zero F
      · simpa only [hx, if_false] using hpsd _
    refine psd_congr ?_ (psd_add hp1 hp2)
    intro h hh h' hh'
    have hsum := hTS hPG hPD hPL hLF hGRC hCP hKG hN1 hMM K R ψ hD hch m (m + 1) n₀ F Om (Lc : Set K) D
      τ cr hF hcr' h hh h' hh'
    rw [← mean_sub D.A D.B hAc hBc, ← hsum]
    rw [finsum_ite_eq hfin.toFinset (fun x : K ⧸ R.toAddSubgroup => (Quotient.out x : K) ∈ perp ψ D.L₁)
      (fun x => thx R ψ m cr D.A D.B τ (Quotient.out x) h h') hS]
    rw [finsum_ite_eq hfin.toFinset (fun x : K ⧸ R.toAddSubgroup => (Quotient.out x : K) ∈ Lc)
      (fun x => thx R ψ m cr D.A D.B τ (Quotient.out x) h h')
      (fun x hx => hS x (D.cutPerp _ hx))]
    rw [sub_add, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun x hx => ?_
    have hxP : (Quotient.out x : K) ∈ perp ψ D.L₁ := hfin.mem_toFinset.1 hx
    by_cases hxL : (Quotient.out x : K) ∈ Lc
    · simp only [hxP, hxL, if_true, sub_zero]
    · simp only [hxP, hxL, if_true, if_false, sub_self]
  ·
    intro x h _ h' _ hne
    by_cases hx : x ∈ Lc
    · simp only [hx, if_true, thx]
      have hz : ∀ ρ ∈ D.A, ∀ b ∈ D.B, ∀ b' ∈ D.B,
          uGram R ψ m cr Set.univ h h' (τ (ρ + b)) (τ (ρ + b')) = 0 := by
        intro ρ hρ b hb b' hb'
        refine hUB hKBD hCSA hMM K R ψ hD m cr Set.univ h h' _ _ ?_ hne
        exact mul_right_cancel₀ htpos.ne' ((hτmod ρ hρ b hb).trans (hτmod ρ hρ b' hb').symm)
      have : ∑ ρ ∈ D.A, ((D.B.card : ℂ)⁻¹) ^ 2 * ∑ b ∈ D.B, ∑ b' ∈ D.B,
          ψ (-(x * b)) * conj (ψ (-(x * b'))) *
            uGram R ψ m cr Set.univ h h' (τ (ρ + b)) (τ (ρ + b')) = 0 := by
        refine Finset.sum_eq_zero fun ρ hρ => ?_
        rw [Finset.sum_eq_zero fun b hb => Finset.sum_eq_zero fun b' hb' => by
          rw [hz ρ hρ b hb b' hb', mul_zero], mul_zero]
      rw [this, mul_zero]
    · simp only [hx, if_false]
