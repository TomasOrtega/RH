import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLocIdealKer
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace LocIdealKer

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
  {𝓜 : (K → ℤ) → Submodule S M}

def degProducts (𝓜 : (K → ℤ) → Submodule S M) (P : Ideal (MRingOver S ι)) (D : K → ℤ) : Set M :=
  {x | ∃ (p : MRingOver S ι) (b : K → ℕ) (n : M), p ∈ P ∧ IsMultiHomog p b ∧
    n ∈ 𝓜 (D - fun k => (b k : ℤ)) ∧ x = p • n}

/- English proof (translation)
Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨p, b, n, -, hp, hn, rfl⟩`. Use `h𝓜.2 b _ p n hp hn` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis.
-/
theorem span_degProducts_le (h𝓜 : KH.IsMGraded S ι 𝓜) (P : Ideal (MRingOver S ι)) (D : K → ℤ) :
    Submodule.span S (degProducts 𝓜 P D) ≤ 𝓜 D := by
  rw [Submodule.span_le]
  rintro _ ⟨p, b, n, -, hp, hn, rfl⟩
  have := h𝓜.2 b _ p n hp hn
  rwa [sub_add_cancel] at this

/- English proof (translation)
Take `⟨G, hG, hPG⟩` from `hP`. Establish `hadd : ∀ x₁ x₂ : M, (∃ y ∈ Submodule.span S (degProducts 𝓜 P D), x₁ - y ∈ ⨆ (j) (_ : j ≠ D), 𝓜 j) → (∃ y ∈ Submodule.span S (degProducts 𝓜 P D), x₂ - y ∈ ⨆ (j) (_ : j ≠ D), 𝓜 j) → ∃ y ∈ Submodule.span S (degProducts 𝓜 P D), x₁ + x₂ - y ∈ ⨆ (j) (_ : j ≠ D), 𝓜 j`. Introduce and unpack `x₁ x₂ ⟨y₁, hy₁, e₁⟩ ⟨y₂, hy₂, e₂⟩`. Use `⟨y₁ + y₂, add_mem hy₁ hy₂, ?_⟩` and prove the remaining obligations. Rewrite using `[add_sub_add_comm]`.

Conclude with `add_mem e₁ e₂`. Establish `hzero : ∃ y ∈ Submodule.span S (degProducts 𝓜 P D), (0 : M) - y ∈ ⨆ (j) (_ : j ≠ D), 𝓜 j` using `⟨0, zero_mem _, by rw [sub_zero]; exact zero_mem _⟩`. Establish `hgen : ∀ g ∈ G, ∀ n : M, ∃ y ∈ Submodule.span S (degProducts 𝓜 P D), g • n - y ∈ ⨆ (j) (_ : j ≠ D), 𝓜 j`. Introduce `g hg n`. Take `⟨b, hb⟩` from `hG g hg`.

Establish `hgP : g ∈ P` using `by rw [hPG]; exact Ideal.subset_span hg`. Establish `hn : n ∈ ⨆ j, 𝓜 j`. Rewrite using `[h𝓜.1.submodule_iSup_eq_top]`. Conclude with `Submodule.mem_top`. Use `Submodule.iSup_induction (motive := fun n => ∃ y ∈ Submodule.span S (degProducts 𝓜 P D), g • n - y ∈ ⨆ (j) (_ : j ≠ D), 𝓜 j) 𝓜 hn ?_ ?_ ?_` and prove the remaining obligations.

Introduce `j n hn`. Establish `hgn` using `h𝓜.2 b j g n hb hn`. Distinguish the cases in `hj : (j + fun k => (b k : ℤ)) = D`. Use `⟨g • n, Submodule.subset_span ⟨g, b, n, hgP, hb, ?_, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← hj, add_sub_cancel_right]`.

Conclude with `hn`. Rewrite using `[sub_self]`. Conclude with `zero_mem _`. Use `⟨0, zero_mem _, ?_⟩` and prove the remaining obligations. Rewrite using `[sub_zero]`.

Conclude with `Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem hj hgn)`. Rewrite using `[smul_zero]`. Conclude with `hzero`. Introduce `n₁ n₂ h₁ h₂`. Rewrite using `[smul_add]`.

Conclude with `hadd _ _ h₁ h₂`. Establish `hP' : ∀ p ∈ P, ∀ n : M, ∃ y ∈ Submodule.span S (degProducts 𝓜 P D), p • n - y ∈ ⨆ (j) (_ : j ≠ D), 𝓜 j`. Introduce `p hp`. Rewrite `hp` using `[hPG]`. Proceed by induction on `hp using Submodule.span_induction with`.

Consider the case `mem g hg => exact hgen g hg`. Consider the case `zero`. Introduce `n`. Rewrite using `[zero_smul]`. Conclude with `hzero`.

Consider the case `add p q _ _ hp hq`. Introduce `n`. Rewrite using `[add_smul]`. Conclude with `hadd _ _ (hp n) (hq n)`. Consider the case `smul r p _ hp`.

Introduce `n`. Rewrite using `[smul_eq_mul, mul_comm, mul_smul]`. Conclude with `hp (r • n)`. Conclude with `Submodule.smul_induction_on hx (fun p hp n _ => hP' p hp n) (fun x₁ x₂ h₁ h₂ => hadd _ _ h₁ h₂)`.
-/
theorem exists_near (h𝓜 : KH.IsMGraded S ι 𝓜) {P : Ideal (MRingOver S ι)} (hP : IsMultiHomogIdeal P)
    (D : K → ℤ) {x : M} (hx : x ∈ (P • ⊤ : Submodule (MRingOver S ι) M)) :
    ∃ y ∈ Submodule.span S (degProducts 𝓜 P D), x - y ∈ ⨆ (j) (_ : j ≠ D), 𝓜 j := by
  classical
  obtain ⟨G, hG, hPG⟩ := hP
  have hadd : ∀ x₁ x₂ : M,
      (∃ y ∈ Submodule.span S (degProducts 𝓜 P D), x₁ - y ∈ ⨆ (j) (_ : j ≠ D), 𝓜 j) →
      (∃ y ∈ Submodule.span S (degProducts 𝓜 P D), x₂ - y ∈ ⨆ (j) (_ : j ≠ D), 𝓜 j) →
      ∃ y ∈ Submodule.span S (degProducts 𝓜 P D), x₁ + x₂ - y ∈ ⨆ (j) (_ : j ≠ D), 𝓜 j := by
    rintro x₁ x₂ ⟨y₁, hy₁, e₁⟩ ⟨y₂, hy₂, e₂⟩
    refine ⟨y₁ + y₂, add_mem hy₁ hy₂, ?_⟩
    rw [add_sub_add_comm]
    exact add_mem e₁ e₂
  have hzero : ∃ y ∈ Submodule.span S (degProducts 𝓜 P D), (0 : M) - y ∈ ⨆ (j) (_ : j ≠ D), 𝓜 j :=
    ⟨0, zero_mem _, by rw [sub_zero]; exact zero_mem _⟩

  have hgen : ∀ g ∈ G, ∀ n : M,
      ∃ y ∈ Submodule.span S (degProducts 𝓜 P D), g • n - y ∈ ⨆ (j) (_ : j ≠ D), 𝓜 j := by
    intro g hg n
    obtain ⟨b, hb⟩ := hG g hg
    have hgP : g ∈ P := by rw [hPG]; exact Ideal.subset_span hg
    have hn : n ∈ ⨆ j, 𝓜 j := by
      rw [h𝓜.1.submodule_iSup_eq_top]
      exact Submodule.mem_top
    refine Submodule.iSup_induction (motive := fun n => ∃ y ∈ Submodule.span S (degProducts 𝓜 P D),
      g • n - y ∈ ⨆ (j) (_ : j ≠ D), 𝓜 j) 𝓜 hn ?_ ?_ ?_
    · intro j n hn
      have hgn := h𝓜.2 b j g n hb hn
      by_cases hj : (j + fun k => (b k : ℤ)) = D
      · refine ⟨g • n, Submodule.subset_span ⟨g, b, n, hgP, hb, ?_, rfl⟩, ?_⟩
        · rw [← hj, add_sub_cancel_right]
          exact hn
        · rw [sub_self]
          exact zero_mem _
      · refine ⟨0, zero_mem _, ?_⟩
        rw [sub_zero]
        exact Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem hj hgn)
    · rw [smul_zero]
      exact hzero
    · intro n₁ n₂ h₁ h₂
      rw [smul_add]
      exact hadd _ _ h₁ h₂

  have hP' : ∀ p ∈ P, ∀ n : M,
      ∃ y ∈ Submodule.span S (degProducts 𝓜 P D), p • n - y ∈ ⨆ (j) (_ : j ≠ D), 𝓜 j := by
    intro p hp
    rw [hPG] at hp
    induction hp using Submodule.span_induction with
    | mem g hg => exact hgen g hg
    | zero =>
      intro n
      rw [zero_smul]
      exact hzero
    | add p q _ _ hp hq =>
      intro n
      rw [add_smul]
      exact hadd _ _ (hp n) (hq n)
    | smul r p _ hp =>
      intro n
      rw [smul_eq_mul, mul_comm, mul_smul]
      exact hp (r • n)
  exact Submodule.smul_induction_on hx (fun p hp n _ => hP' p hp n) (fun x₁ x₂ h₁ h₂ => hadd _ _ h₁ h₂)

/- English proof (translation)
Take `⟨y, hy, hd⟩` from `exists_near h𝓜 hP D hx`. Establish `hc : x - y ∈ 𝓜 D` using `sub_mem hxD (span_degProducts_le h𝓜 P D hy)`. Establish `h0 : x - y = 0` using `Submodule.disjoint_def.mp (h𝓜.1.submodule_iSupIndep D) _ hc hd`. Rewrite `h0` using `[sub_eq_zero]`. Rewrite using `[h0]`.

Conclude with `hy`.
-/
theorem mem_span_degProducts (h𝓜 : KH.IsMGraded S ι 𝓜) {P : Ideal (MRingOver S ι)} (hP : IsMultiHomogIdeal P)
    {D : K → ℤ} {x : M} (hx : x ∈ (P • ⊤ : Submodule (MRingOver S ι) M)) (hxD : x ∈ 𝓜 D) :
    x ∈ Submodule.span S (degProducts 𝓜 P D) := by
  obtain ⟨y, hy, hd⟩ := exists_near h𝓜 hP D hx
  have hc : x - y ∈ 𝓜 D := sub_mem hxD (span_degProducts_le h𝓜 P D hy)
  have h0 : x - y = 0 := Submodule.disjoint_def.mp (h𝓜.1.submodule_iSupIndep D) _ hc hd
  rw [sub_eq_zero] at h0
  rw [h0]
  exact hy

/- English proof (translation)
Introduce `S _ K _ ι _ M _ _ _ _ 𝓜 P T d h𝓜 hP hT w hw`. Set `_ : LinearOrder K` to `LinearOrder.lift' (Fintype.equivFin K) (Fintype.equivFin K).injective`. Set `_ : ∀ k, LinearOrder (ι k)` to `fun k => LinearOrder.lift' (Fintype.equivFin (ι k)) (Fintype.equivFin (ι k)).injective`. Use `set N := (P • ⊤ : Submodule (MRingOver S ι) M) with hN`. Use `set L := IsLocalizedModule.map T (LocalizedModule.mkLinearMap T M) (LocalizedModule.mkLinearMap T (M ⧸ N)) N.mkQ with hL`.

Establish `hLmk : ∀ (m : M) (t : T), L (LocalizedModule.mk m t) = LocalizedModule.mk (N.mkQ m) t`. Introduce `m t`. Rewrite using `[hL, IsLocalizedModule.mk_eq_mk', IsLocalizedModule.map_mk', ← IsLocalizedModule.mk_eq_mk']`. Prove the components needed by the constructor for the conclusion. Establish `hkill : ∀ p ∈ P, ∀ z : LocalizedModule T (M ⧸ N), p • z = 0`.

Introduce `p hp z`. Proceed by induction on `z using LocalizedModule.induction_on with`. Consider the case `h q t`. Take `⟨n, rfl⟩` from `Submodule.mkQ_surjective N q`. Rewrite using `[LocalizedModule.smul'_mk, ← map_smul, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).2 (Submodule.smul_mem_smul hp Submodule.mem_top), LocalizedModule.zero_mk]`.

Introduce `hwP`. Use `clear hw`. Proceed by induction on `hwP using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨p, a, y, hp, -, -, rfl⟩` from `hx`.

Rewrite using `[map_smul]`. Conclude with `hkill p hp _`. Consider the case `zero => exact map_zero L`. Consider the case `add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]`. Consider the case `smul s x _ hx`.

Rewrite using `[← algebraMap_smul (MRingOver S ι) s x, map_smul, hx, smul_zero]`. Introduce `h0`. Take `⟨m, t, a, ht, hm, rfl⟩` from `GenSESStep.locPart_normal h𝓜 hw`. Rewrite `h0` using `[hLmk, ← LocalizedModule.zero_mk (1 : T), LocalizedModule.mk_eq]`. Take `⟨u, hu⟩` from `h0`.

Rewrite `hu` using `[one_smul, smul_zero, smul_zero, Submonoid.smul_def, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Take `⟨e, he⟩` from `hT u u.2`. Use `set D : K → ℤ := (d + fun k => (a k : ℤ)) + fun k => (e k : ℤ) with hD`. Establish `humD : (u : MRingOver S ι) • m ∈ 𝓜 D` using `h𝓜.2 e _ _ m he hm`. Establish `hspan` using `mem_span_degProducts h𝓜 hP hu humD`.

Establish `hut : IsMultiHomog ((u * t : T) : MRingOver S ι) (e + a)` using `GenSESStep.isMultiHomog_mul he ht`. Rewrite using `[← LocalizedModule.mk_cancel_common_left u t m, Submonoid.smul_def]`. Generalize the expression as in `(u : MRingOver S ι) • m = x at hspan ⊢`. Proceed by induction on `hspan using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨p, b, n, hp, hpb, hn, rfl⟩` from `hx`. Rewrite using `[← LocalizedModule.smul'_mk]`. Use `Submodule.subset_span ⟨p, b, _, hp, hpb, GenSESStep.mk_mem_locPart n (u * t) (e + a) hut ?_, rfl⟩` and prove the remaining obligations. Establish `edeg : ((d - fun k => (b k : ℤ)) + fun k => ((e + a) k : ℤ)) = D - fun k => (b k : ℤ)`. Use function extensionality and compare the values at `k`.

Simplify using `only [hD, Pi.add_apply, Pi.sub_apply, Nat.cast_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[edeg]`. Conclude with `hn`. Consider the case `zero`.

Rewrite using `[LocalizedModule.zero_mk]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy`. Rewrite using `[IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk'_add, ← IsLocalizedModule.mk_eq_mk', ← IsLocalizedModule.mk_eq_mk']`. Conclude with `add_mem hx hy`.

Consider the case `smul s x _ hx`. Rewrite using `[← LocalizedModule.smul'_mk]`. Conclude with `Submodule.smul_mem _ s hx`.
-/
theorem proof : LocIdealKer.Statement := by
  intro S _ K _ ι _ M _ _ _ _ 𝓜 P T d h𝓜 hP hT w hw
  classical
  let _ : LinearOrder K := LinearOrder.lift' (Fintype.equivFin K) (Fintype.equivFin K).injective
  let _ : ∀ k, LinearOrder (ι k) := fun k =>
    LinearOrder.lift' (Fintype.equivFin (ι k)) (Fintype.equivFin (ι k)).injective
  set N := (P • ⊤ : Submodule (MRingOver S ι) M) with hN
  set L := IsLocalizedModule.map T (LocalizedModule.mkLinearMap T M)
    (LocalizedModule.mkLinearMap T (M ⧸ N)) N.mkQ with hL
  have hLmk : ∀ (m : M) (t : T), L (LocalizedModule.mk m t) = LocalizedModule.mk (N.mkQ m) t := by
    intro m t
    rw [hL, IsLocalizedModule.mk_eq_mk', IsLocalizedModule.map_mk', ← IsLocalizedModule.mk_eq_mk']
  constructor
  ·
    have hkill : ∀ p ∈ P, ∀ z : LocalizedModule T (M ⧸ N), p • z = 0 := by
      intro p hp z
      induction z using LocalizedModule.induction_on with
      | h q t =>
        obtain ⟨n, rfl⟩ := Submodule.mkQ_surjective N q
        rw [LocalizedModule.smul'_mk, ← map_smul, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).2
          (Submodule.smul_mem_smul hp Submodule.mem_top), LocalizedModule.zero_mk]
    intro hwP
    clear hw
    induction hwP using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨p, a, y, hp, -, -, rfl⟩ := hx
      rw [map_smul]
      exact hkill p hp _
    | zero => exact map_zero L
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul s x _ hx =>
      rw [← algebraMap_smul (MRingOver S ι) s x, map_smul, hx, smul_zero]
  · intro h0
    obtain ⟨m, t, a, ht, hm, rfl⟩ := GenSESStep.locPart_normal h𝓜 hw
    rw [hLmk, ← LocalizedModule.zero_mk (1 : T), LocalizedModule.mk_eq] at h0
    obtain ⟨u, hu⟩ := h0
    rw [one_smul, smul_zero, smul_zero, Submonoid.smul_def, ← map_smul, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at hu
    obtain ⟨e, he⟩ := hT u u.2
    set D : K → ℤ := (d + fun k => (a k : ℤ)) + fun k => (e k : ℤ) with hD
    have humD : (u : MRingOver S ι) • m ∈ 𝓜 D := h𝓜.2 e _ _ m he hm
    have hspan := mem_span_degProducts h𝓜 hP hu humD
    have hut : IsMultiHomog ((u * t : T) : MRingOver S ι) (e + a) := GenSESStep.isMultiHomog_mul he ht
    rw [← LocalizedModule.mk_cancel_common_left u t m, Submonoid.smul_def]
    generalize (u : MRingOver S ι) • m = x at hspan ⊢
    induction hspan using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨p, b, n, hp, hpb, hn, rfl⟩ := hx
      rw [← LocalizedModule.smul'_mk]
      refine Submodule.subset_span ⟨p, b, _, hp, hpb, GenSESStep.mk_mem_locPart n (u * t) (e + a) hut ?_, rfl⟩
      have edeg : ((d - fun k => (b k : ℤ)) + fun k => ((e + a) k : ℤ)) = D - fun k => (b k : ℤ) := by
        funext k
        simp only [hD, Pi.add_apply, Pi.sub_apply, Nat.cast_add]
        ring
      rw [edeg]
      exact hn
    | zero =>
      rw [LocalizedModule.zero_mk]
      exact zero_mem _
    | add x y _ _ hx hy =>
      rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk'_add, ← IsLocalizedModule.mk_eq_mk',
        ← IsLocalizedModule.mk_eq_mk']
      exact add_mem hx hy
    | smul s x _ hx =>
      rw [← LocalizedModule.smul'_mk]
      exact Submodule.smul_mem _ s hx

end LocIdealKer

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
