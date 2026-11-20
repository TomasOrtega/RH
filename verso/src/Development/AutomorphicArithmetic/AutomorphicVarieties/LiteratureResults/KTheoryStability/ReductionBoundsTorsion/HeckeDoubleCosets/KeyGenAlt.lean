import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeckeDoubleCosets.Formal
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeckeDoubleCosets.Assemble

noncomputable section

open UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.AffineStabilizerVanishing

open PositivityTheory.KB

section
variable {Γn ΓN Kn KN : Type} [Group Γn] [Group ΓN] [Group Kn] [Group KN]
  {ρn : Γn →* Kn} {ρN : ΓN →* KN} {sO : Γn →* ΓN} {sL : Kn →* KN} {qn : Kn} {q : KN}

/- English proof (translation)
Unfold `ev`. Simplify using `only [smul_eq_mul, mul_one]`.
-/
private theorem ev_one_eq_finsupp_sum {G K : Type} [Group G] [Group K] (ρ : G →* K) {m : ℕ}
    (Ψ : (Fin (m + 2) → K) → ℝ) (z : Chn G (m + 1)) :
    ev ρ Ψ 1 z = Finsupp.sum (α := Fin (m + 1) → G) z
      (fun g r => r * Ψ (fun j => ρ (Fin.partialProd g j))) := by
  unfold ev
  simp only [smul_eq_mul, mul_one]

/- English proof (translation)
Unfold `Fin.partialProd`. Rewrite using `[map_list_prod, List.map_take, List.map_ofFn]`. Both sides reduce to the same expression.
-/
private theorem partialProd_map_monoidHom {G G' : Type} [Group G] [Group G'] (s : G' →* G) {n : ℕ} (g : Fin n → G')
    (j : Fin (n + 1)) : Fin.partialProd (fun i => s (g i)) j = s (Fin.partialProd g j) := by
  unfold Fin.partialProd
  rw [map_list_prod, List.map_take, List.map_ofFn]
  rfl

/- English proof (translation)
Rewrite using `[ev_one_eq_finsupp_sum]`. Unfold `cmap`. Rewrite using `[Finsupp.lmapDomain_apply, Finsupp.sum_mapDomain_index]`. Use `congr 1`. Use function extensionality and compare the values at `g r`.

Use `congr 2`. Use function extensionality and compare the values at `j`. Use `congr 1`. Conclude with `partialProd_map_monoidHom s g j`. Introduce `_`.

Simplify using the standard rewrite rules. Introduce `_ _ _`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem ev_one_cmap_eq_finsupp_sum {G K G' : Type} [Group G] [Group K] [Group G'] (ρ : G →* K)
    (s : G' →* G) {m : ℕ} (Ψ : (Fin (m + 2) → K) → ℝ) (z : Chn G' (m + 1)) :
    ev ρ Ψ 1 (cmap s (m + 1) z) = Finsupp.sum (α := Fin (m + 1) → G') z
      (fun g r => r * Ψ (fun j => ρ (s (Fin.partialProd g j)))) := by
  rw [ev_one_eq_finsupp_sum]
  unfold cmap
  rw [Finsupp.lmapDomain_apply, Finsupp.sum_mapDomain_index]
  · congr 1
    funext g r
    congr 2
    funext j
    congr 1
    exact partialProd_map_monoidHom s g j
  · intro _
    simp
  · intro _ _ _
    ring

/- English proof (translation)
Unfold `ev`. Simplify using `only [mul_sub]`. Conclude with `Finsupp.sum_sub`.
-/
private theorem ev_sub_hecke_double_cosets {G H Y : Type} [Group G] [Group H] [MulAction H Y] (ρ : G →* H) {m : ℕ}
    (f g : (Fin (m + 1) → Y) → ℝ) (y : Y) (w : Chn G m) :
    ev ρ (fun t => f t - g t) y w = ev ρ f y w - ev ρ g y w := by
  unfold ev
  simp only [mul_sub]
  exact Finsupp.sum_sub

/- English proof (translation)
Unfold `Gq at h`. Rewrite `h` using `[Subgroup.mem_comap, Subgroup.mem_map]`. Take `⟨a, ha1, ha⟩` from `h`. Take `⟨g', rfl⟩` from `MonoidHom.mem_range.mp ha1`. Simplify using `at ha`.

Establish `hc' : ρ c' = q⁻¹ * ρ g' * q * ρ c`. Rewrite using `[ha]`. Use `group`. Establish `e : (fun j => q * ρ c' * w j) = fun j => ρ g' • (q * ρ c * w j)`. Use function extensionality and compare the values at `j`.

Rewrite using `[hc', smul_eq_mul]`. Use `group`. Rewrite using `[e]`. Conclude with `hF g' _`.
-/
private theorem coset_lemma_4 {G K : Type} [Group G] [Group K] (ρ : G →* K) (q : K) {m : ℕ}
    (F : (Fin (m + 2) → K) → ℝ) (hF : Inv ρ F) {c c' : G} (h : c' * c⁻¹ ∈ Gq ρ q)
    (w : Fin (m + 2) → K) :
    F (fun j => q * ρ c' * w j) = F (fun j => q * ρ c * w j) := by
  unfold Gq at h
  rw [Subgroup.mem_comap, Subgroup.mem_map] at h
  obtain ⟨a, ha1, ha⟩ := h
  obtain ⟨g', rfl⟩ := MonoidHom.mem_range.mp ha1
  simp at ha
  have hc' : ρ c' = q⁻¹ * ρ g' * q * ρ c := by
    rw [ha]
    group
  have e : (fun j => q * ρ c' * w j) = fun j => ρ g' • (q * ρ c * w j) := by
    funext j
    rw [hc', smul_eq_mul]
    group
  rw [e]
  exact hF g' _

/- English proof (translation)
Unfold `hecke`. Both sides reduce to the same expression.
-/
private theorem hecke_apply_eq_index_inv_mul_finsum_rightRel {G K : Type} [Group G] [Group K] (ρ : G →* K) (q : K) {m : ℕ}
    (Ψ : (Fin (m + 2) → K) → ℝ) (y : Fin (m + 2) → K) :
    hecke ρ (MonoidHom.id K) q Ψ y = ((Gq ρ q).index : ℝ)⁻¹ *
      ∑ᶠ c : Quotient (QuotientGroup.rightRel (Gq ρ q)), Ψ (fun j => q * ρ c.out * y j) := by
  unfold hecke
  rfl

/- English proof (translation)
Rewrite using `[Quotient.eq]`. Conclude with `QuotientGroup.rightRel_apply`.
-/
private theorem quotient_mk_rightRel_eq_iff_mul_inv_mem {G : Type} [Group G] (S : Subgroup G) (a b : G) :
    Quotient.mk (QuotientGroup.rightRel S) a = Quotient.mk (QuotientGroup.rightRel S) b ↔
      b * a⁻¹ ∈ S := by
  rw [Quotient.eq]
  exact QuotientGroup.rightRel_apply

/- English proof (translation)
Rewrite using `[Subgroup.index_eq_card, ← Nat.card_eq_fintype_card, Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel S)]`.
-/
private theorem index_eq_card_quotient_rightRel {G : Type} [Group G] (S : Subgroup G)
    [Fintype (Quotient (QuotientGroup.rightRel S))] :
    (S.index : ℝ) = Fintype.card (Quotient (QuotientGroup.rightRel S)) := by
  rw [Subgroup.index_eq_card, ← Nat.card_eq_fintype_card,
    Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel S)]

/- English proof (translation)
Rewrite using `[ev_one_cmap_eq_finsupp_sum, ev_one_cmap_eq_finsupp_sum, ev_one_eq_finsupp_sum]`. Simplify using `only [hecke_apply_eq_index_inv_mul_finsum_rightRel]`. Establish `hT'` using `hT`. Unfold `PTransfer at hT'`. Set `X` to `{x : Quotient (QuotientGroup.rightRel (Gq ρN q)) // ∀ a : Γn, Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (sO a) ≠ x}`.

Establish `hmem : ∀ (x : X) (g : Γn) (a : Γn), Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (sO a) ≠ Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (x.1.out * sO g)`. Introduce `x g a ha`. Rewrite `ha` using `[quotient_mk_rightRel_eq_iff_mul_inv_mem]`. Apply `x.2 (a * g⁻¹)` to reduce the goal to its premises. Rewrite using `[← Quotient.out_eq x.1, quotient_mk_rightRel_eq_iff_mul_inv_mem]`.

Use `ha using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_mul, map_inv]`. Use `group`. Take `⟨act, hact⟩ : ∃ act : X → Γn → X, ∀ x g, (act x g).1 = Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (x.1.out * sO g)` from `⟨fun x g => ⟨_, hmem x g⟩, fun _ _ => rfl⟩`. Establish `hrep : ∀ (x : X) (g : Γn), (act x g).1.out * (x.1.out * sO g)⁻¹ ∈ Gq ρN q`.

Introduce `x g`. Rewrite using `[← quotient_mk_rightRel_eq_iff_mul_inv_mem, Quotient.out_eq, hact]`. Establish `h1 : ∀ x, act x 1 = x`. Introduce `x`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[hact, map_one, mul_one, Quotient.out_eq]`. Establish `hm : ∀ x g h, act x (g * h) = act (act x g) h`. Introduce `x g h`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hact, hact, quotient_mk_rightRel_eq_iff_mul_inv_mem]`.

Use `hrep x g using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_mul]`. Use `group`. Set `Φ : X → (Fin (m + 2) → Γn) → ℝ` to `fun x y => F (fun j => q * ρN x.1.out * ρN (sO (y j))) - F (fun j => ρN (sO (y j)))`. Establish `hΦ1 : ∀ x g y, Φ (act x g) y = Φ x (fun j => g * y j)`.

Introduce `x g y`. Simplify using `only [Φ]`. Rewrite using `[coset_lemma_4 ρN q F hFinv (hrep x g) (fun j => ρN (sO (y j)))]`. Use `congr 1`. Use `congr 1`.

Use function extensionality and compare the values at `j`. Simplify using `[map_mul, mul_assoc]`. Rewrite using `[show (fun j => ρN (sO (g * y j))) = fun j => ρN (sO g) • ρN (sO (y j)) from`. Use function extensionality and compare the values at `fun j => by simp]`. Conclude with `(hFinv _ _).symm`.

Establish `hΦ2 : ∀ x, dC (Φ x) = 0`. Introduce `x`. Use function extensionality and compare the values at `y`. Establish `e1` using `congrFun hFcoc (fun j => q * ρN x.1.out * ρN (sO (y j)))`. Establish `e2` using `congrFun hFcoc (fun j => ρN (sO (y j)))`.

Simplify using `only [dC, Pi.zero_apply, Φ] at e1 e2 ⊢`. Simplify using `only [mul_sub, Finset.sum_sub_distrib, e1, e2, sub_zero]`. Establish `hΦ3 : ∀ x (w : Chn (stabR act h1 hm x) (m + 1)), IsCyc w → ev (stabR act h1 hm x).subtype (Φ x) 1 w = 0`. Introduce `x w hw`. Establish `hx : ∀ c' : Γn, x.1.out * (sO c')⁻¹ ∉ Gq ρN q`.

Introduce `c' hc`. Apply `x.2 c'` to reduce the goal to its premises. Rewrite using `[← Quotient.out_eq x.1, quotient_mk_rightRel_eq_iff_mul_inv_mem]`. Conclude with `hc`. Establish `hst : ∀ h ∈ stabR act h1 hm x, x.1.out * sO h * x.1.out⁻¹ ∈ Gq ρN q`.

Introduce `h hh`. Establish `hh' : act x h = x` using `hh`. Establish `e` using `congrArg Subtype.val hh'`. Rewrite `e` using `[hact]`. Use `conv at e => rhs`.

Rewrite using `[← Quotient.out_eq x.1]`. Conclude with `(quotient_mk_rightRel_eq_iff_mul_inv_mem _ _ _).mp e.symm`. Establish `e` using `hvan x.1.out hx _ hst w hw`. Use `show ev _ (fun t => F (fun j => q * ρN x.1.out * ρN (sO (t j))) - F (fun j => ρN (sO (t j)))) 1 w = 0`. Rewrite using `[ev_sub_hecke_double_cosets, e, sub_self]`.

Use `haveI : Finite X := Subtype.finite`. Establish `hz0` using `hT' Γn X act h1 hm m Φ hΦ1 hΦ2 hΦ3 z hz`. Rewrite `hz0` using `[ev_one_eq_finsupp_sum]`. Simplify using `only [MonoidHom.id_apply] at hz0`. Use `haveI : Fintype (Quotient (QuotientGroup.rightRel (Gq ρN q))) := Fintype.ofFinite _`.

Use `haveI : Fintype (Quotient (QuotientGroup.rightRel (Gq ρn qn))) := Fintype.ofFinite _`. Use `haveI : Fintype X := Fintype.ofFinite _`. Establish `himg : Finset.univ.filter (fun c : Quotient (QuotientGroup.rightRel (Gq ρN q)) => ¬ ∀ a : Γn, Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (sO a) ≠ c) = Finset.univ.image (fun d : Quotient (QuotientGroup.rightRel (Gq ρn qn)) => Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (sO …`. Use extensionality with `c`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, not_forall, not_not]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha⟩`. Use `⟨Quotient.mk (QuotientGroup.rightRel (Gq ρn qn)) a, ?_⟩` and prove the remaining obligations. Rewrite using `[← ha, quotient_mk_rightRel_eq_iff_mul_inv_mem, ← map_inv, ← map_mul, hGS, ← quotient_mk_rightRel_eq_iff_mul_inv_mem, Quotient.out_eq]`. Introduce and unpack `⟨d, hd⟩`.

Conclude with `⟨d.out, hd⟩`. Establish `hinj : Function.Injective (fun d : Quotient (QuotientGroup.rightRel (Gq ρn qn)) => Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (sO d.out))`. Introduce `d d' h`. Simplify using `only at h`. Rewrite `h` using `[quotient_mk_rightRel_eq_iff_mul_inv_mem, ← map_inv, ← map_mul, hGS, ← quotient_mk_rightRel_eq_iff_mul_inv_mem, Quotient.out_eq, Quotient.out_eq]`.

Conclude with `h`. Establish `hgen : ∀ f : Quotient (QuotientGroup.rightRel (Gq ρN q)) → ℝ, ∑ c, f c = ∑ x : X, f x.1 + ∑ d : Quotient (QuotientGroup.rightRel (Gq ρn qn)), f (Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (sO d.out))`. Introduce `f`. Rewrite using `[← Finset.sum_filter_add_sum_filter_not Finset.univ (fun c => ∀ a : Γn, Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (sO a) ≠ c) f, himg, Finset.sum_image (fun x _ y _ h => hinj h), Finset.sum_subtype _ (fun x => Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _)))]`. Establish `hNpos : 0 < Fintype.card (Quotient (QuotientGroup.rightRel (Gq ρN q)))` using `Fintype.card_pos_iff.mpr ⟨Quotient.mk _ 1⟩`.

Establish `hnpos : 0 < Fintype.card (Quotient (QuotientGroup.rightRel (Gq ρn qn)))` using `Fintype.card_pos_iff.mpr ⟨Quotient.mk _ 1⟩`. Establish `hcard` using `hgen (fun _ => 1)`. Simplify using `only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hcard`. Establish `hpt : ∀ y : Fin (m + 2) → Γn, ((Gq ρN q).index : ℝ)⁻¹ * ∑ᶠ c : Quotient (QuotientGroup.rightRel (Gq ρN q)), F (fun j => q * ρN c.out * ρN (sO (y j))) = (1 - ((Gq ρn qn).index : ℝ) / (Gq ρN q).index) * F (fun j => ρN (sO (y j))) + ((Gq ρn qn).index : ℝ) / (Gq ρN q).index * (((Gq ρ …`. Introduce `y`.

Rewrite using `[finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, index_eq_card_quotient_rightRel, index_eq_card_quotient_rightRel, hgen]`. Establish `hd : ∀ d : Quotient (QuotientGroup.rightRel (Gq ρn qn)), F (fun j => q * ρN (Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (sO d.out)).out * ρN (sO (y j))) = F (fun j => sL (qn * ρn d.out * ρn (y j)))`. Introduce `d`. Rewrite using `[coset_lemma_4 ρN q F hFinv (c := sO d.out) (c' := (Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (sO d.out)).out) (by rw [← quotient_mk_rightRel_eq_iff_mul_inv_mem, Quotient.out_eq]) (fun j => ρN (sO (y j)))]`. Use `congr 1`.

Use function extensionality and compare the values at `j`. Simplify using `only [hq, hcomm, map_mul]`. Simplify using `only [hd, Φ, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Rewrite using `[hcard]`. Establish `h1' : (Fintype.card (Quotient (QuotientGroup.rightRel (Gq ρn qn))) : ℝ) ≠ 0` using `Nat.cast_ne_zero.mpr hnpos.ne'`.

Establish `h2' : (Fintype.card X : ℝ) + Fintype.card (Quotient (QuotientGroup.rightRel (Gq ρn qn))) ≠ 0`. Check the signs of the components of the expression. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hpt]`.

Rewrite using `[← sub_eq_zero]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Finsupp.sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `g _`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = 0 := by rw [hz0, mul_zero]`.
-/
theorem keyGen (hT : PTransfer) (hcomm : ∀ c, ρN (sO c) = sL (ρn c)) (hq : q = sL qn)
    (hGS : ∀ c, sO c ∈ Gq ρN q ↔ c ∈ Gq ρn qn)
    [Finite (Quotient (QuotientGroup.rightRel (Gq ρN q)))] [Finite (Quotient (QuotientGroup.rightRel (Gq ρn qn)))]
    (m : ℕ) (F : (Fin (m + 2) → KN) → ℝ) (hFinv : Inv ρN F) (hFcoc : dC F = 0)
    (hvan : ∀ c : ΓN, (∀ c' : Γn, c * (sO c')⁻¹ ∉ Gq ρN q) → ∀ H : Subgroup Γn,
      (∀ h ∈ H, c * sO h * c⁻¹ ∈ Gq ρN q) → ∀ w : Chn H (m + 1), IsCyc w →
        ev H.subtype (fun y => F fun j => q * ρN c * ρN (sO (y j))) 1 w =
          ev H.subtype (fun y => F fun j => ρN (sO (y j))) 1 w)
    (z : Chn Γn (m + 1)) (hz : IsCyc z) :
    ev ρN (hecke ρN (MonoidHom.id KN) q F) 1 (cmap sO (m + 1) z) =
      (1 - ((Gq ρn qn).index : ℝ) / (Gq ρN q).index) * ev ρN F 1 (cmap sO (m + 1) z) +
        ((Gq ρn qn).index : ℝ) / (Gq ρN q).index *
          ev ρn (hecke ρn (MonoidHom.id Kn) qn (fun y => F fun j => sL (y j))) 1 z := by
  classical
  rw [ev_one_cmap_eq_finsupp_sum, ev_one_cmap_eq_finsupp_sum, ev_one_eq_finsupp_sum]
  simp only [hecke_apply_eq_index_inv_mul_finsum_rightRel]
  have hT' := hT
  unfold PTransfer at hT'
  let X := {x : Quotient (QuotientGroup.rightRel (Gq ρN q)) //
    ∀ a : Γn, Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (sO a) ≠ x}
  have hmem : ∀ (x : X) (g : Γn) (a : Γn), Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (sO a) ≠
      Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (x.1.out * sO g) := by
    intro x g a ha
    rw [quotient_mk_rightRel_eq_iff_mul_inv_mem] at ha
    apply x.2 (a * g⁻¹)
    rw [← Quotient.out_eq x.1, quotient_mk_rightRel_eq_iff_mul_inv_mem]
    convert ha using 1
    rw [map_mul, map_inv]
    group
  obtain ⟨act, hact⟩ : ∃ act : X → Γn → X, ∀ x g,
      (act x g).1 = Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (x.1.out * sO g) :=
    ⟨fun x g => ⟨_, hmem x g⟩, fun _ _ => rfl⟩
  have hrep : ∀ (x : X) (g : Γn), (act x g).1.out * (x.1.out * sO g)⁻¹ ∈ Gq ρN q := by
    intro x g
    rw [← quotient_mk_rightRel_eq_iff_mul_inv_mem, Quotient.out_eq, hact]
  have h1 : ∀ x, act x 1 = x := by
    intro x
    apply Subtype.ext
    rw [hact, map_one, mul_one, Quotient.out_eq]
  have hm : ∀ x g h, act x (g * h) = act (act x g) h := by
    intro x g h
    apply Subtype.ext
    rw [hact, hact, quotient_mk_rightRel_eq_iff_mul_inv_mem]
    convert hrep x g using 1
    rw [map_mul]
    group
  let Φ : X → (Fin (m + 2) → Γn) → ℝ := fun x y =>
    F (fun j => q * ρN x.1.out * ρN (sO (y j))) - F (fun j => ρN (sO (y j)))
  have hΦ1 : ∀ x g y, Φ (act x g) y = Φ x (fun j => g * y j) := by
    intro x g y
    simp only [Φ]
    rw [coset_lemma_4 ρN q F hFinv (hrep x g) (fun j => ρN (sO (y j)))]
    congr 1
    · congr 1
      funext j
      simp [map_mul, mul_assoc]
    · rw [show (fun j => ρN (sO (g * y j))) = fun j => ρN (sO g) • ρN (sO (y j)) from
        funext fun j => by simp]
      exact (hFinv _ _).symm
  have hΦ2 : ∀ x, dC (Φ x) = 0 := by
    intro x
    funext y
    have e1 := congrFun hFcoc (fun j => q * ρN x.1.out * ρN (sO (y j)))
    have e2 := congrFun hFcoc (fun j => ρN (sO (y j)))
    simp only [dC, Pi.zero_apply, Φ] at e1 e2 ⊢
    simp only [mul_sub, Finset.sum_sub_distrib, e1, e2, sub_zero]
  have hΦ3 : ∀ x (w : Chn (stabR act h1 hm x) (m + 1)), IsCyc w →
      ev (stabR act h1 hm x).subtype (Φ x) 1 w = 0 := by
    intro x w hw
    have hx : ∀ c' : Γn, x.1.out * (sO c')⁻¹ ∉ Gq ρN q := by
      intro c' hc
      apply x.2 c'
      rw [← Quotient.out_eq x.1, quotient_mk_rightRel_eq_iff_mul_inv_mem]
      exact hc
    have hst : ∀ h ∈ stabR act h1 hm x, x.1.out * sO h * x.1.out⁻¹ ∈ Gq ρN q := by
      intro h hh
      have hh' : act x h = x := hh
      have e := congrArg Subtype.val hh'
      rw [hact] at e
      conv at e => rhs; rw [← Quotient.out_eq x.1]
      exact (quotient_mk_rightRel_eq_iff_mul_inv_mem _ _ _).mp e.symm
    have e := hvan x.1.out hx _ hst w hw
    show ev _ (fun t => F (fun j => q * ρN x.1.out * ρN (sO (t j))) - F (fun j => ρN (sO (t j)))) 1 w = 0
    rw [ev_sub_hecke_double_cosets, e, sub_self]
  haveI : Finite X := Subtype.finite
  have hz0 := hT' Γn X act h1 hm m Φ hΦ1 hΦ2 hΦ3 z hz
  rw [ev_one_eq_finsupp_sum] at hz0
  simp only [MonoidHom.id_apply] at hz0
  haveI : Fintype (Quotient (QuotientGroup.rightRel (Gq ρN q))) := Fintype.ofFinite _
  haveI : Fintype (Quotient (QuotientGroup.rightRel (Gq ρn qn))) := Fintype.ofFinite _
  haveI : Fintype X := Fintype.ofFinite _
  have himg : Finset.univ.filter (fun c : Quotient (QuotientGroup.rightRel (Gq ρN q)) =>
      ¬ ∀ a : Γn, Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (sO a) ≠ c) =
      Finset.univ.image (fun d : Quotient (QuotientGroup.rightRel (Gq ρn qn)) =>
        Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (sO d.out)) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, not_forall, not_not]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨Quotient.mk (QuotientGroup.rightRel (Gq ρn qn)) a, ?_⟩
      rw [← ha, quotient_mk_rightRel_eq_iff_mul_inv_mem, ← map_inv, ← map_mul, hGS, ← quotient_mk_rightRel_eq_iff_mul_inv_mem, Quotient.out_eq]
    · rintro ⟨d, hd⟩
      exact ⟨d.out, hd⟩
  have hinj : Function.Injective (fun d : Quotient (QuotientGroup.rightRel (Gq ρn qn)) =>
      Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (sO d.out)) := by
    intro d d' h
    simp only at h
    rw [quotient_mk_rightRel_eq_iff_mul_inv_mem, ← map_inv, ← map_mul, hGS, ← quotient_mk_rightRel_eq_iff_mul_inv_mem, Quotient.out_eq, Quotient.out_eq] at h
    exact h
  have hgen : ∀ f : Quotient (QuotientGroup.rightRel (Gq ρN q)) → ℝ,
      ∑ c, f c = ∑ x : X, f x.1 +
        ∑ d : Quotient (QuotientGroup.rightRel (Gq ρn qn)),
          f (Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (sO d.out)) := by
    intro f
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun c => ∀ a : Γn, Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (sO a) ≠ c) f,
      himg, Finset.sum_image (fun x _ y _ h => hinj h), Finset.sum_subtype _ (fun x => Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _)))]
  have hNpos : 0 < Fintype.card (Quotient (QuotientGroup.rightRel (Gq ρN q))) :=
    Fintype.card_pos_iff.mpr ⟨Quotient.mk _ 1⟩
  have hnpos : 0 < Fintype.card (Quotient (QuotientGroup.rightRel (Gq ρn qn))) :=
    Fintype.card_pos_iff.mpr ⟨Quotient.mk _ 1⟩
  have hcard := hgen (fun _ => 1)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hcard
  have hpt : ∀ y : Fin (m + 2) → Γn,
      ((Gq ρN q).index : ℝ)⁻¹ * ∑ᶠ c : Quotient (QuotientGroup.rightRel (Gq ρN q)),
          F (fun j => q * ρN c.out * ρN (sO (y j))) =
        (1 - ((Gq ρn qn).index : ℝ) / (Gq ρN q).index) * F (fun j => ρN (sO (y j))) +
          ((Gq ρn qn).index : ℝ) / (Gq ρN q).index * (((Gq ρn qn).index : ℝ)⁻¹ *
            ∑ᶠ c : Quotient (QuotientGroup.rightRel (Gq ρn qn)),
              F (fun j => sL (qn * ρn c.out * ρn (y j)))) +
          ((Gq ρN q).index : ℝ)⁻¹ * ∑ᶠ x : X, Φ x y := by
    intro y
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, index_eq_card_quotient_rightRel,
      index_eq_card_quotient_rightRel, hgen]
    have hd : ∀ d : Quotient (QuotientGroup.rightRel (Gq ρn qn)),
        F (fun j => q * ρN (Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (sO d.out)).out *
          ρN (sO (y j))) = F (fun j => sL (qn * ρn d.out * ρn (y j))) := by
      intro d
      rw [coset_lemma_4 ρN q F hFinv (c := sO d.out)
        (c' := (Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (sO d.out)).out)
        (by rw [← quotient_mk_rightRel_eq_iff_mul_inv_mem, Quotient.out_eq]) (fun j => ρN (sO (y j)))]
      congr 1
      funext j
      simp only [hq, hcomm, map_mul]
    simp only [hd, Φ, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hcard]
    have h1' : (Fintype.card (Quotient (QuotientGroup.rightRel (Gq ρn qn))) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr hnpos.ne'
    have h2' : (Fintype.card X : ℝ) + Fintype.card (Quotient (QuotientGroup.rightRel (Gq ρn qn))) ≠ 0 := by
      positivity
    field_simp
    ring
  simp only [hpt]
  rw [← sub_eq_zero]
  calc _ = ((Gq ρN q).index : ℝ)⁻¹ *
        Finsupp.sum z (fun g r => r * ∑ᶠ x : X, Φ x (fun j => Fin.partialProd g j)) := by
        simp only [Finsupp.sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro g _
        ring
    _ = 0 := by rw [hz0, mul_zero]

end

end PositivityTheory.KB.AffineStabilizerVanishing

end
