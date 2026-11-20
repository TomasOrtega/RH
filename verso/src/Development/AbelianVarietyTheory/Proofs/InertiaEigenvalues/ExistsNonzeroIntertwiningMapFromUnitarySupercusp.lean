import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryAdmissibleMatrixCoefficient

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

namespace GlobalTheory.CuspBack

variable {G W V : Type} [Group G] [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V]

def lineStab (π : Representation ℂ G W) (x : W) (hx : x ≠ 0) : Subgroup G where
  carrier := {h | ∃ c : ℂ, π h x = c • x}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro a b ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨d * c, by rw [map_mul, Module.End.mul_apply, hd, map_smul, hc, smul_smul]⟩
  inv_mem' := by
    rintro a ⟨c, hc⟩
    have h1 : x = c • π a⁻¹ x := by
      rw [← map_smul, ← hc, ← Module.End.mul_apply, ← map_mul]; simp
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hx (by simpa using h1)
    refine ⟨c⁻¹, ?_⟩
    conv_rhs => rw [h1]
    rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]

/- English proof (translation)
Establish `h : ρ g (ρ g⁻¹ v) = v`. Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`. Rewrite using `[← hi g, h]`.
-/
theorem form_inv (ρ : Representation ℂ G V) (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hi : ∀ g v w, B (ρ g v) (ρ g w) = B v w) (g : G) (v w : V) : B (ρ g⁻¹ v) w = B v (ρ g w) := by
  have h : ρ g (ρ g⁻¹ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [← hi g, h]

/- English proof (translation)
Establish `hwd : ∀ v (a b : G), a⁻¹ * b ∈ H → F v a = F v b`. Introduce `v a b hab`. Use `hH v a (a⁻¹ * b) hab` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel_left]`. Conclude with `this.symm`.

Set `Fq : V → G ⧸ H → W` to `fun v q => Quotient.liftOn' q (F v) (fun a b hab => hwd v a b (QuotientGroup.leftRel_apply.mp hab))`. Establish `hsupp : ∀ v, (Function.support (Fq v)).Finite`. Introduce `v`. Take `⟨t, ht⟩` from `hfin v`. Use `(t.finite_toSet.image (fun c : G => (c : G ⧸ H))).subset ?_` and prove the remaining obligations.

Introduce `q hq`. Take `⟨g, rfl⟩` from `QuotientGroup.mk_surjective q`. Take `⟨c, hc, hcg⟩` from `ht g hq`. Conclude with `⟨c, hc, QuotientGroup.eq.2 hcg⟩`. Establish `hadd' : ∀ v v' q, Fq (v + v') q = Fq v q + Fq v' q`.

Introduce `v v' q`. Take `⟨g, rfl⟩` from `QuotientGroup.mk_surjective q`. Conclude with `hadd v v' g`. Establish `hsmul' : ∀ (a : ℂ) v q, Fq (a • v) q = a • Fq v q`. Introduce `a v q`.

Take `⟨g, rfl⟩` from `QuotientGroup.mk_surjective q`. Conclude with `hsmul a v g`. Establish `heq' : ∀ h v q, Fq (ρ h v) q = π h (Fq v (h⁻¹ • q))`. Introduce `h v q`. Take `⟨g, rfl⟩` from `QuotientGroup.mk_surjective q`.

Conclude with `heq h v g`. Set `L : V →ₗ[ℂ] W` to `{ toFun := fun v => ∑ᶠ q, Fq v q map_add' := fun v v' => by`. Simplify using `only [hadd']`. Conclude with `finsum_add_distrib (hsupp v) (hsupp v')`. Use the proof step `map_smul' := fun a v => by`.

Simplify using `only [hsmul', RingHom.id_apply]`. Conclude with `(smul_finsum' a (hsupp v)).symm }`. Use `⟨L.intertwiningMap_of_isIntertwiningMap ρ π (fun h v => ?_), fun Ψ v hΨ => ?_⟩` and prove the remaining obligations. Use `show ∑ᶠ q, Fq (ρ h v) q = π h (∑ᶠ q, Fq v q)`. Simplify using `only [heq']`.

Establish `e : ∑ᶠ q, π h (Fq v (h⁻¹ • q)) = ∑ᶠ q, π h (Fq v q)` using `finsum_comp (g := fun q => π h (Fq v q)) (fun q : G ⧸ H => h⁻¹ • q) (MulAction.bijective h⁻¹)`. Rewrite using `[e]`. Conclude with `(AddMonoidHom.map_finsum (π h).toAddMonoidHom (hsupp v)).symm`. Use `show Ψ (F v 1) ≤ Ψ (∑ᶠ q, Fq v q)`. Rewrite using `[AddMonoidHom.map_finsum Ψ (hsupp v)]`.

Conclude with `single_le_finsum ((1 : G) : G ⧸ H) ((hsupp v).subset (Function.support_comp_subset (map_zero Ψ) (Fq v))) (fun q => by`. Take `⟨g, rfl⟩` from `QuotientGroup.mk_surjective q`. Conclude with `hΨ g)`.
-/
private theorem exists_intertwiningMap_bound (π : Representation ℂ G W) (ρ : Representation ℂ G V) (H : Subgroup G)
    (F : V → G → W) (hH : ∀ v g h, h ∈ H → F v (g * h) = F v g)
    (hfin : ∀ v, ∃ t : Finset G, ∀ g, F v g ≠ 0 → ∃ c ∈ t, c⁻¹ * g ∈ H)
    (hadd : ∀ v v' g, F (v + v') g = F v g + F v' g)
    (hsmul : ∀ (a : ℂ) v g, F (a • v) g = a • F v g)
    (heq : ∀ h v g, F (ρ h v) g = π h (F v (h⁻¹ * g))) :
    ∃ ι : ρ.IntertwiningMap π, ∀ (Ψ : W →+ ℝ) (v : V), (∀ g, 0 ≤ Ψ (F v g)) → Ψ (F v 1) ≤ Ψ (ι v) := by

  have hwd : ∀ v (a b : G), a⁻¹ * b ∈ H → F v a = F v b := by
    intro v a b hab
    have := hH v a (a⁻¹ * b) hab
    rw [mul_inv_cancel_left] at this
    exact this.symm
  let Fq : V → G ⧸ H → W := fun v q =>
    Quotient.liftOn' q (F v) (fun a b hab => hwd v a b (QuotientGroup.leftRel_apply.mp hab))

  have hsupp : ∀ v, (Function.support (Fq v)).Finite := by
    intro v
    obtain ⟨t, ht⟩ := hfin v
    refine (t.finite_toSet.image (fun c : G => (c : G ⧸ H))).subset ?_
    intro q hq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨c, hc, hcg⟩ := ht g hq
    exact ⟨c, hc, QuotientGroup.eq.2 hcg⟩
  have hadd' : ∀ v v' q, Fq (v + v') q = Fq v q + Fq v' q := by
    intro v v' q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    exact hadd v v' g
  have hsmul' : ∀ (a : ℂ) v q, Fq (a • v) q = a • Fq v q := by
    intro a v q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    exact hsmul a v g
  have heq' : ∀ h v q, Fq (ρ h v) q = π h (Fq v (h⁻¹ • q)) := by
    intro h v q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    exact heq h v g

  let L : V →ₗ[ℂ] W :=
    { toFun := fun v => ∑ᶠ q, Fq v q
      map_add' := fun v v' => by
        simp only [hadd']
        exact finsum_add_distrib (hsupp v) (hsupp v')
      map_smul' := fun a v => by
        simp only [hsmul', RingHom.id_apply]
        exact (smul_finsum' a (hsupp v)).symm }
  refine ⟨L.intertwiningMap_of_isIntertwiningMap ρ π (fun h v => ?_), fun Ψ v hΨ => ?_⟩
  · show ∑ᶠ q, Fq (ρ h v) q = π h (∑ᶠ q, Fq v q)
    simp only [heq']
    have e : ∑ᶠ q, π h (Fq v (h⁻¹ • q)) = ∑ᶠ q, π h (Fq v q) :=
      finsum_comp (g := fun q => π h (Fq v q)) (fun q : G ⧸ H => h⁻¹ • q) (MulAction.bijective h⁻¹)
    rw [e]
    exact (AddMonoidHom.map_finsum (π h).toAddMonoidHom (hsupp v)).symm
  · show Ψ (F v 1) ≤ Ψ (∑ᶠ q, Fq v q)
    rw [AddMonoidHom.map_finsum Ψ (hsupp v)]
    exact single_le_finsum ((1 : G) : G ⧸ H)
      ((hsupp v).subset (Function.support_comp_subset (map_zero Ψ) (Fq v)))
      (fun q => by
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
        exact hΨ g)

/- English proof (translation)
Introduce `G W V _ _ _ _ _ _ _ π ρ p hπ hρ hu hc hp`. Take `⟨B, hB1, hB2, hB3⟩` from `hu`. Take `⟨hρs, hρc⟩` from `hρ`. Choose the witnesses or unpack the hypotheses as in `⟨w, hw⟩ : ∃ w, p w ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `hp (Representation.IntertwiningMap.ext (LinearMap.ext fun x => h x))`. Set `K : Subgroup G` to `{ carrier := {g | π g w = w} mul_mem' := fun {a b} ha hb => by`. Establish `ha' : π a w = w` using `ha`. Establish `hb' : π b w = w` using `hb`.

Use `show π (a * b) w = w`. Rewrite using `[map_mul, Module.End.mul_apply, hb', ha']`. Use the proof step `one_mem' := by show π 1 w = w`. Rewrite using `[map_one, Module.End.one_apply]`. Use the proof step `inv_mem' := fun {a} ha => by`.

Establish `ha' : π a w = w` using `ha`. Use `show π a⁻¹ w = w`. Use `nth_rewrite 1 [← ha']`. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }`. Establish `hKopen : IsOpen (K : Set G)` using `hπ w`.

Establish `hKu : ∀ k ∈ K, ρ k (p w) = p w`. Introduce `k hk`. Establish `hk' : π k w = w` using `hk`. Rewrite using `[← p.isIntertwining, hk']`. Set `l : Module.Dual ℂ V` to `{ toFun := fun x => B x (p w) map_add' := fun x y => by simp map_smul' := fun a x => by simp }`.

Establish `hKl : ∀ k ∈ K, ρ.dual k l = l`. Introduce `k hk`. Use extensionality with `y`. Use `show B (ρ k⁻¹ y) (p w) = B y (p w)`. Rewrite using `[form_inv ρ B hB3 k y (p w), hKu k hk]`.

Establish `hl : l ∈ smoothPart ρ.dual` using `by show IsOpen {g : G | ρ.dual g l = l}`. Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `g hg`. Establish `hg' : ρ.dual g l = l` using `hg`. Establish `ho : IsOpen ((fun x => g⁻¹ * x) ⁻¹' (K : Set G))` using `hKopen.preimage (continuous_mul_left g⁻¹)`.

Use `Filter.mem_of_superset (ho.mem_nhds ?_) ?_` and prove the remaining obligations. Use `show g⁻¹ * g ∈ K`. Rewrite using `[inv_mul_cancel]`. Conclude with `K.one_mem`. Introduce `x hx`.

Establish `hx' : g⁻¹ * x ∈ K` using `hx`. Use `show ρ.dual x l = l`. Establish `hxg : x = g * (g⁻¹ * x)` using `by group`. Rewrite using `[hxg, map_mul, Module.End.mul_apply, hKl _ hx', hg']`. Set `F : V → G → W` to `fun v g => B (ρ g⁻¹ v) (p w) • π g w`.

Establish `hK : ∀ v g k, k ∈ K → F v (g * k) = F v g`. Introduce `v g k hk`. Establish `hk' : π k w = w` using `hk`. Use `show B (ρ (g * k)⁻¹ v) (p w) • π (g * k) w = B (ρ g⁻¹ v) (p w) • π g w`. Simplify using `only [mul_inv_rev, map_mul, Module.End.mul_apply]`.

Rewrite using `[form_inv ρ B hB3 k (ρ g⁻¹ v) (p w), hKu k hk, hk']`. Establish `hZ : ∀ v g z, z ∈ Subgroup.center G → F v (g * z) = F v g`. Introduce `v g z hz`. Take `⟨c, hcw⟩` from `hc z hz`. Establish `hρz : ρ z (p w) = c • p w` using `by rw [← p.isIntertwining, hcw, map_smul]`.

Establish `hcc : starRingEnd ℂ c * c = 1`. Establish `h1` using `hB3 z (p w) (p w)`. Simplify using `only [hρz, map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul] at h1`. Establish `hne : B (p w) (p w) ≠ 0` using `fun h0 => by`. Use `hB2 (p w) hw` as an intermediate fact.

Rewrite `this` using `[h0, Complex.zero_re]`. Conclude with `lt_irrefl 0 this`. Establish `h2 : (starRingEnd ℂ c * c) * B (p w) (p w) = 1 * B (p w) (p w)`. Take the linear combination `h1`. Conclude with `mul_right_cancel₀ hne h2`.

Use `show B (ρ (g * z)⁻¹ v) (p w) • π (g * z) w = B (ρ g⁻¹ v) (p w) • π g w`. Simplify using `only [mul_inv_rev, map_mul, Module.End.mul_apply]`. Rewrite using `[form_inv ρ B hB3 z (ρ g⁻¹ v) (p w), hρz, hcw w, map_smulₛₗ (B (ρ g⁻¹ v)) c (p w), map_smul (π g) c w, smul_smul, smul_eq_mul, mul_right_comm, hcc, one_mul]`. Set `S : Subgroup G` to `{ carrier := {h | ∀ v g, F v (g * h) = F v g} mul_mem' := fun {a b} ha hb => by`. Establish `ha' : ∀ v g, F v (g * a) = F v g` using `ha`.

Establish `hb' : ∀ v g, F v (g * b) = F v g` using `hb`. Use `show ∀ v g, F v (g * (a * b)) = F v g`. Introduce `v g`. Rewrite using `[← mul_assoc, hb', ha']`. Use the proof step `one_mem' := by show ∀ v g, F v (g * 1) = F v g`.

Introduce `v g`. Rewrite using `[mul_one]`. Use the proof step `inv_mem' := fun {a} ha => by`. Establish `ha' : ∀ v g, F v (g * a) = F v g` using `ha`. Use `show ∀ v g, F v (g * a⁻¹) = F v g`.

Introduce `v g`. Rewrite using `[← ha' v (g * a⁻¹), inv_mul_cancel_right] }`. Establish `hHS : Subgroup.center G ⊔ K ≤ S`. Use `sup_le ?_ ?_` and prove the remaining obligations. Introduce `z hz show ∀ v g, F v (g * z) = F v g`.

Introduce `v g`. Conclude with `hZ v g z hz`. Introduce `k hk show ∀ v g, F v (g * k) = F v g`. Introduce `v g`. Conclude with `hK v g k hk`.

Establish `hH : ∀ v g h, h ∈ Subgroup.center G ⊔ K → F v (g * h) = F v g`. Introduce `v g h hh`. Use `hHS hh` as an intermediate fact. Conclude with `this v g`. Establish `hfin : ∀ v, ∃ t : Finset G, ∀ g, F v g ≠ 0 → ∃ c ∈ t, c⁻¹ * g ∈ Subgroup.center G ⊔ K`.

Introduce `v`. Take `⟨C, hC, hCs⟩` from `hρc v l hl`. Take `⟨t, ht⟩` from `hC.elim_finite_subcover (fun c : G => (fun x => x * c⁻¹) ⁻¹' (K : Set G)) (fun c => hKopen.preimage (continuous_mul_right c⁻¹)) (fun c _ => Set.mem_iUnion.2 ⟨c, by simp⟩)`. Use `⟨t.image (fun c => c⁻¹), fun g hg => ?_⟩` and prove the remaining obligations. Establish `hne : l (ρ g⁻¹ v) ≠ 0`.

Introduce `h0`. Apply `hg` to reduce the goal to its premises. Establish `h0' : B (ρ g⁻¹ v) (p w) = 0` using `h0`. Use `show B (ρ g⁻¹ v) (p w) • π g w = 0`. Rewrite using `[h0', zero_smul]`.

Take `⟨z, hz, c, hc', hgc⟩` from `hCs g⁻¹ hne`. Establish `hcU` using `ht hc'`. Rewrite `hcU` using `[Set.mem_iUnion₂]`. Take `⟨i, hi, hci⟩` from `hcU`. Establish `hci' : c * i⁻¹ ∈ K` using `hci`.

Use `⟨i⁻¹, Finset.mem_image_of_mem _ hi, ?_⟩` and prove the remaining obligations. Establish `hgi : (i⁻¹)⁻¹ * g = (c * i⁻¹)⁻¹ * z⁻¹`. Rewrite using `[← inv_inv g, hgc]`. Use `group`. Rewrite using `[hgi]`.

Conclude with `Subgroup.mul_mem _ (Subgroup.inv_mem _ (le_sup_right (a := Subgroup.center G) hci')) (Subgroup.inv_mem _ (le_sup_left (b := K) hz))`. Establish `hadd : ∀ v v' g, F (v + v') g = F v g + F v' g`. Introduce `v v' g`. Use `show B (ρ g⁻¹ (v + v')) (p w) • π g w = B (ρ g⁻¹ v) (p w) • π g w + B (ρ g⁻¹ v') (p w) • π g w`. Rewrite using `[map_add, map_add, LinearMap.add_apply, add_smul]`.

Establish `hsmul : ∀ (a : ℂ) v g, F (a • v) g = a • F v g`. Introduce `a v g`. Use `show B (ρ g⁻¹ (a • v)) (p w) • π g w = a • (B (ρ g⁻¹ v) (p w) • π g w)`. Rewrite using `[map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, mul_smul]`. Establish `heqv : ∀ h v g, F (ρ h v) g = π h (F v (h⁻¹ * g))`.

Introduce `h v g`. Use `show B (ρ g⁻¹ (ρ h v)) (p w) • π g w = π h (B (ρ (h⁻¹ * g)⁻¹ v) (p w) • π (h⁻¹ * g) w)`. Rewrite using `[map_smul, ← Module.End.mul_apply (π h), ← map_mul, mul_inv_cancel_left, mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply]`. Take `⟨ι, hι⟩` from `exists_intertwiningMap_bound π ρ (Subgroup.center G ⊔ K) F hH hfin hadd hsmul heqv`. Use `⟨ι, fun h0 => ?_⟩` and prove the remaining obligations.

Set `Ψ : W →+ ℝ` to `{ toFun := fun x => (B (p x) (p w)).re map_zero' := by simp map_add' := fun x y => by simp }`. Establish `key : ∀ g, Ψ (F (p w) g) = (starRingEnd ℂ (B (ρ g (p w)) (p w)) * B (ρ g (p w)) (p w)).re`. Introduce `g`. Use `show (B (p (B (ρ g⁻¹ (p w)) (p w) • π g w)) (p w)).re = _`. Rewrite using `[map_smul, p.isIntertwining, map_smul, LinearMap.smul_apply, smul_eq_mul, form_inv ρ B hB3 g (p w) (p w), hB1 (ρ g (p w)) (p w)]`.

Establish `hnn : ∀ g, 0 ≤ Ψ (F (p w) g)`. Introduce `g`. Rewrite using `[key]`. Simplify using `only [Complex.mul_re, Complex.conj_re, Complex.conj_im]`. Use polynomial arithmetic with `[sq_nonneg (B (ρ g (p w)) (p w)).re, sq_nonneg (B (ρ g (p w)) (p w)).im]`.

Establish `h1` using `hι Ψ (p w) hnn`. Establish `hι0 : ι (p w) = 0` using `by rw [h0]; rfl`. Rewrite `h1` using `[hι0, map_zero, key, map_one, Module.End.one_apply]`. Establish `hpos` using `hB2 (p w) hw`. Simplify using `only [Complex.mul_re, Complex.conj_re, Complex.conj_im] at h1`.

Use polynomial arithmetic with `[sq_nonneg (B (p w) (p w)).im, mul_pos hpos hpos]`.
-/
theorem exists_back : ∀ (G W V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G W) (ρ : Representation ℂ G V) (p : π.IntertwiningMap ρ), IsSmooth π → IsSupercuspidal ρ → IsUnitarisable ρ → (∀ z ∈ Subgroup.center G, ∃ c : ℂ, ∀ w, π z w = c • w) → p ≠ 0 → ∃ ι : ρ.IntertwiningMap π, ι ≠ 0 := by
  classical
  intro G W V _ _ _ _ _ _ _ π ρ p hπ hρ hu hc hp
  obtain ⟨B, hB1, hB2, hB3⟩ := hu
  obtain ⟨hρs, hρc⟩ := hρ
  obtain ⟨w, hw⟩ : ∃ w, p w ≠ 0 := by
    by_contra h
    push_neg at h
    exact hp (Representation.IntertwiningMap.ext (LinearMap.ext fun x => h x))

  let K : Subgroup G :=
    { carrier := {g | π g w = w}
      mul_mem' := fun {a b} ha hb => by
        have ha' : π a w = w := ha
        have hb' : π b w = w := hb
        show π (a * b) w = w
        rw [map_mul, Module.End.mul_apply, hb', ha']
      one_mem' := by
        show π 1 w = w
        rw [map_one, Module.End.one_apply]
      inv_mem' := fun {a} ha => by
        have ha' : π a w = w := ha
        show π a⁻¹ w = w
        nth_rewrite 1 [← ha']
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hKopen : IsOpen (K : Set G) := hπ w
  have hKu : ∀ k ∈ K, ρ k (p w) = p w := by
    intro k hk
    have hk' : π k w = w := hk
    rw [← p.isIntertwining, hk']

  let l : Module.Dual ℂ V :=
    { toFun := fun x => B x (p w)
      map_add' := fun x y => by simp
      map_smul' := fun a x => by simp }
  have hKl : ∀ k ∈ K, ρ.dual k l = l := by
    intro k hk
    ext y
    show B (ρ k⁻¹ y) (p w) = B y (p w)
    rw [form_inv ρ B hB3 k y (p w), hKu k hk]
  have hl : l ∈ smoothPart ρ.dual := by
    show IsOpen {g : G | ρ.dual g l = l}
    rw [isOpen_iff_mem_nhds]
    intro g hg
    have hg' : ρ.dual g l = l := hg
    have ho : IsOpen ((fun x => g⁻¹ * x) ⁻¹' (K : Set G)) := hKopen.preimage (continuous_mul_left g⁻¹)
    refine Filter.mem_of_superset (ho.mem_nhds ?_) ?_
    · show g⁻¹ * g ∈ K
      rw [inv_mul_cancel]
      exact K.one_mem
    · intro x hx
      have hx' : g⁻¹ * x ∈ K := hx
      show ρ.dual x l = l
      have hxg : x = g * (g⁻¹ * x) := by group
      rw [hxg, map_mul, Module.End.mul_apply, hKl _ hx', hg']

  let F : V → G → W := fun v g => B (ρ g⁻¹ v) (p w) • π g w
  have hK : ∀ v g k, k ∈ K → F v (g * k) = F v g := by
    intro v g k hk
    have hk' : π k w = w := hk
    show B (ρ (g * k)⁻¹ v) (p w) • π (g * k) w = B (ρ g⁻¹ v) (p w) • π g w
    simp only [mul_inv_rev, map_mul, Module.End.mul_apply]
    rw [form_inv ρ B hB3 k (ρ g⁻¹ v) (p w), hKu k hk, hk']
  have hZ : ∀ v g z, z ∈ Subgroup.center G → F v (g * z) = F v g := by
    intro v g z hz
    obtain ⟨c, hcw⟩ := hc z hz
    have hρz : ρ z (p w) = c • p w := by rw [← p.isIntertwining, hcw, map_smul]
    have hcc : starRingEnd ℂ c * c = 1 := by
      have h1 := hB3 z (p w) (p w)
      simp only [hρz, map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul] at h1
      have hne : B (p w) (p w) ≠ 0 := fun h0 => by
        have := hB2 (p w) hw
        rw [h0, Complex.zero_re] at this
        exact lt_irrefl 0 this
      have h2 : (starRingEnd ℂ c * c) * B (p w) (p w) = 1 * B (p w) (p w) := by
        linear_combination h1
      exact mul_right_cancel₀ hne h2
    show B (ρ (g * z)⁻¹ v) (p w) • π (g * z) w = B (ρ g⁻¹ v) (p w) • π g w
    simp only [mul_inv_rev, map_mul, Module.End.mul_apply]
    rw [form_inv ρ B hB3 z (ρ g⁻¹ v) (p w), hρz, hcw w, map_smulₛₗ (B (ρ g⁻¹ v)) c (p w),
      map_smul (π g) c w, smul_smul, smul_eq_mul, mul_right_comm, hcc, one_mul]
  let S : Subgroup G :=
    { carrier := {h | ∀ v g, F v (g * h) = F v g}
      mul_mem' := fun {a b} ha hb => by
        have ha' : ∀ v g, F v (g * a) = F v g := ha
        have hb' : ∀ v g, F v (g * b) = F v g := hb
        show ∀ v g, F v (g * (a * b)) = F v g
        intro v g
        rw [← mul_assoc, hb', ha']
      one_mem' := by
        show ∀ v g, F v (g * 1) = F v g
        intro v g
        rw [mul_one]
      inv_mem' := fun {a} ha => by
        have ha' : ∀ v g, F v (g * a) = F v g := ha
        show ∀ v g, F v (g * a⁻¹) = F v g
        intro v g
        rw [← ha' v (g * a⁻¹), inv_mul_cancel_right] }
  have hHS : Subgroup.center G ⊔ K ≤ S := by
    refine sup_le ?_ ?_
    · intro z hz
      show ∀ v g, F v (g * z) = F v g
      intro v g
      exact hZ v g z hz
    · intro k hk
      show ∀ v g, F v (g * k) = F v g
      intro v g
      exact hK v g k hk
  have hH : ∀ v g h, h ∈ Subgroup.center G ⊔ K → F v (g * h) = F v g := by
    intro v g h hh
    have := hHS hh
    exact this v g
  have hfin : ∀ v, ∃ t : Finset G, ∀ g, F v g ≠ 0 → ∃ c ∈ t, c⁻¹ * g ∈ Subgroup.center G ⊔ K := by
    intro v
    obtain ⟨C, hC, hCs⟩ := hρc v l hl
    obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun c : G => (fun x => x * c⁻¹) ⁻¹' (K : Set G))
      (fun c => hKopen.preimage (continuous_mul_right c⁻¹))
      (fun c _ => Set.mem_iUnion.2 ⟨c, by simp⟩)
    refine ⟨t.image (fun c => c⁻¹), fun g hg => ?_⟩
    have hne : l (ρ g⁻¹ v) ≠ 0 := by
      intro h0
      apply hg
      have h0' : B (ρ g⁻¹ v) (p w) = 0 := h0
      show B (ρ g⁻¹ v) (p w) • π g w = 0
      rw [h0', zero_smul]
    obtain ⟨z, hz, c, hc', hgc⟩ := hCs g⁻¹ hne
    have hcU := ht hc'
    rw [Set.mem_iUnion₂] at hcU
    obtain ⟨i, hi, hci⟩ := hcU
    have hci' : c * i⁻¹ ∈ K := hci
    refine ⟨i⁻¹, Finset.mem_image_of_mem _ hi, ?_⟩
    have hgi : (i⁻¹)⁻¹ * g = (c * i⁻¹)⁻¹ * z⁻¹ := by
      rw [← inv_inv g, hgc]
      group
    rw [hgi]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (le_sup_right (a := Subgroup.center G) hci'))
      (Subgroup.inv_mem _ (le_sup_left (b := K) hz))
  have hadd : ∀ v v' g, F (v + v') g = F v g + F v' g := by
    intro v v' g
    show B (ρ g⁻¹ (v + v')) (p w) • π g w = B (ρ g⁻¹ v) (p w) • π g w + B (ρ g⁻¹ v') (p w) • π g w
    rw [map_add, map_add, LinearMap.add_apply, add_smul]
  have hsmul : ∀ (a : ℂ) v g, F (a • v) g = a • F v g := by
    intro a v g
    show B (ρ g⁻¹ (a • v)) (p w) • π g w = a • (B (ρ g⁻¹ v) (p w) • π g w)
    rw [map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, mul_smul]
  have heqv : ∀ h v g, F (ρ h v) g = π h (F v (h⁻¹ * g)) := by
    intro h v g
    show B (ρ g⁻¹ (ρ h v)) (p w) • π g w = π h (B (ρ (h⁻¹ * g)⁻¹ v) (p w) • π (h⁻¹ * g) w)
    rw [map_smul, ← Module.End.mul_apply (π h), ← map_mul, mul_inv_cancel_left, mul_inv_rev, inv_inv,
      map_mul, Module.End.mul_apply]
  obtain ⟨ι, hι⟩ := exists_intertwiningMap_bound π ρ (Subgroup.center G ⊔ K) F hH hfin hadd hsmul heqv
  refine ⟨ι, fun h0 => ?_⟩

  let Ψ : W →+ ℝ :=
    { toFun := fun x => (B (p x) (p w)).re
      map_zero' := by simp
      map_add' := fun x y => by simp }
  have key : ∀ g, Ψ (F (p w) g) = (starRingEnd ℂ (B (ρ g (p w)) (p w)) * B (ρ g (p w)) (p w)).re := by
    intro g
    show (B (p (B (ρ g⁻¹ (p w)) (p w) • π g w)) (p w)).re = _
    rw [map_smul, p.isIntertwining, map_smul, LinearMap.smul_apply, smul_eq_mul,
      form_inv ρ B hB3 g (p w) (p w), hB1 (ρ g (p w)) (p w)]
  have hnn : ∀ g, 0 ≤ Ψ (F (p w) g) := by
    intro g
    rw [key]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    nlinarith [sq_nonneg (B (ρ g (p w)) (p w)).re, sq_nonneg (B (ρ g (p w)) (p w)).im]
  have h1 := hι Ψ (p w) hnn
  have hι0 : ι (p w) = 0 := by rw [h0]; rfl
  rw [hι0, map_zero, key, map_one, Module.End.one_apply] at h1
  have hpos := hB2 (p w) hw
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im] at h1
  nlinarith [sq_nonneg (B (p w) (p w)).im, mul_pos hpos hpos]

end GlobalTheory.CuspBack
